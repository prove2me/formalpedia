-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5130
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:50:35.481983+00:00
-- url     : https://prove2.me/submissions/25c92f2d-5c55-4ac0-bbc6-e050b3a4e9f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 922482014 ≤ n < 922661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 922483264 1250 922482014 922482023
    0x9060c030114010306051809012406110a0209040f05060a02070f030807090e070c0b010f050303160305120a05150103051911120f01080f03040b16030516061a0109080d0c 74
    0x5041c0812690349103100c2c0194052041000b120508d080300155094980f070034600400f05040000d40607141061034000700603208a4a4200600024007078400e10b41054070360f019410521000501041c0403d01c492a00341d02d00038021a9010381360500741004a20683c10302400c1e844140d5010400a8031443c0c40e030742c100000c3d107000d5080503118016010f483c5000d48204e00412203000e004002c020070034040e0360042000d45428440c1600d0070011917200d1041d8031140c010b41520f450130800301801401900d40b00400180c540440b803030242c41c000c00601d0150b0740004c50820b00741c160322556200340503041c4500790240040c43d40304800500103019042030fa01d01038840505005140e207205055260900c5410515941d10003545010086420b001000039600020f400400c01441816001800c46000c0d260560080030617568904044446010f06118580c0d0702900c070340b11000780803240e00306d0600150300c0031166041800310001542c1e816494451f0a0807900241d4000c484035015409010b6918000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 922484514 1250 922483264 922483271
    0xf0c030e01081e0108030c1e0c01050f131805130201091e050303030f040b010e0403090b0f09030d030b0102010c0302040807090c03180b01140105030f0a05100b070c0e09060c0301140103 81
    0x255030612269109802240e0186d0002c60f00800e1020104800b445e4029a110809200482c0300c00041c0c44018604a00341400000100c0050340c14820045500e008482c03104a600305850b030801542c0c0d14210941107480c6400d15001c03a810507491024000340c1681615940b48544c5400071458000c0500e0081c501c000d11100c2c000034071b03610705000551041b2620480110146010714000d8082a01a004001450045410040040d42100c04101603c075610340711500c51a1002118a1511078486880d416000d040403040c1c255130150072022101100360028414484040e00c2202207000d40d214080b0b4a41c4a00d80400c4a04007503032004032104024600403540b10340e4900710081140c601e02d02129901d0340c600040100442c02d4240300400c41003460b1540c5541450490003541c903002416248160b55150086001e045010140c14001c02c00400d0316074488060b070418007100c05083c41811143d40c0600c00040024002085041c89260749500050450342003511800030b140000c2c040d135060542e0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 922485764 1250 922484514 922484551
    0x712030b031005101205100506030c1201140c09010512060f0a0e04150510090e0c100e0108060a03081c0b0612061306081c09030606060306060f0c030e0108 68
    0x1010310180044039002400410f60342032151000a038800140d100000c00c600301c0101500003a00031480540c00012030601085070303103c0000007404c203202302050a5010b000d10b08007007410782e410340065001c500124003282003561603c10840041c8101d041e0680050010803605102401c4441d142d500182d0250580c4038810743c0b03802042e03103203c1e182c1000b40810300c068100700400248110019040c0302040080c82a8140100703400b003c1c918030b0141c0d2741c100d600e40c06c100483c01d2040080744851074006080700c07840c041c100000340100008409042c0012884400181035080c1a40c6d1b480807a44e00a0388289801c150480805a090810030034043c070340d4841d5014641542d40201801d102c2201000c4910309041000801000d0b2a05681d164250350a090041150b10008512040116400020110314414261080b2100300d01500002c140740e20300b200100e0321580c1540b0050a0310003a480c0c801104403080020341c0c0312513040c41f0050000d80030540d42c013219485102070a40200240410048014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 922487014 1250 922485764 922485769
    0x2070c0e010914010914221b2606070e120307030207060905010804020d06051302060c0c090c1c020d182618090403110d080609010b0f0712030b 63
    0x403802e9211181803078555800c4403091040905080c01041c22500c1080600c09207580010b0081c8000c0c030902098030104100035200341070a0740d0031103295000401fa071010201c900a803903020074501881280c1038a14100d03030800b20a001e0110b90b4a52508000e20881e680e07200215103004c0b4202e0182d070403141e0001c03d103000c000c04102801d62240301e40c028102e02c50600b6001071201d00c030742d440141040600c000340030240c0c071038001d05d100880e007003a80428142d071031030540c41d044028860000e4000200203024a00010040303a0041806411074100b144c50f00c4a030340b9480c403405003c85100d4562500d01d64000000c0300c503402003a6500c03a01c1070104044269040c6030010304845481039030165080a50b2110040c0348094105c4843c52070360140741003107a02148481750f5080407618500031a56880828180360290a218603100103007800ca5109920304c143c000c00160040da00036000e040c0b0b00700003280d10f6101005848800729510321860801415490f10b0882003041c800403010705a8031150810580c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 922488264 1250 922487014 922487039
    0x1e090311040e0f03030a06180b1309050102040f03140c09040302030a030b030a080316120c0c030804061d032203321603021c1a0c0d1b1101051902070c 66
    0x1b800e1000c000a2042d01e00305185583c0c0a610084a4041d4a01601c24130103a5a481042084480e4050000748101152901600910550b000701c2c074140711500b400004c1003180080240b2058031001507070000c626135814000000000e40b03008016800910071080400d20a900800b00340c403005048401d44403030742d10b80400b20b6000350780d4500444100b01e0107200769600442da0f50b1030541c1050041148025401e0014107103142c1c994010200106540820107001a40e000302d040d4822880800f00144080c1030030641c1c952009042612003030016100103241200081044201c07a00182900004158131500c0b42007104180102c1304c0303511040f0341034103011070100300c6403907a0300d04111204043c0e400c41c010030180000c5212402c58420003146a42d001400501d00c0300c03030760095201640000c1d00ca41c2c030301440f64000c8203112040e0f1440c0c900300c2249454040f40300341100e544c03600c500316503440c0090a03600740d803411220850070325100d901c1641c1e0880d84d81e0050040500a90000322000e840d100c202020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 922489514 1250 922488264 922488271
    0xc0337111918091a0603210d180215030f010608181006061103030c0412050a060c050912240702030403020a08030a030c0206092a060a1e090311040e0f0303 68
    0x266543c4030700741010045445801c40307080c0c0301400160850710f011400a940d80c01086181c108241120300c0c41110076003250180d50b594111100f040c0441201400c00c03400e41168100f007a07104101c141d159480380d00d04941124004c0110400e008401e03801d003001074501c6107000e8403000c00004515131000701201c06002038030000d4648940400d9007440c3c282c0080502c10008544162500100148001072040c54115811144501c00c540804241410314a04156254801030138040c2071815003103241e54084002c04d00e9103400c40d0b00c0b8940c0c1602000c0950340380c04041208050302c80e608069110407540c149103581c880000d20480c0e10701900d941c0030600e41e40346e43c1d204c1c6207141c2c0003182a00c02c01d5010302501d042081c007840203200c98a08402c0c00e40d0340303000010b043c25040352220741c0811252094641e41e450104007500c940d030307513032030300308008098a0301c1142011042410400000d50b0301c1c850000e08086a400042c2e03081c40e090110308001c010468901e40012902c80c2051540d43d64400341301a510 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 922490764 1250 922489514 922489559
    0xe041106180a050f01051801140c0d09060c0312090809100903060c050c0a0b070c0b090d110c13020d06030c0305030c0d2d020c03371119 60
    0x1005403500042c082406841d0f006184205600b196402c40c590b803007000d85604102640c15180b50a26010050b5041c200d8440b4481040740d000804030348200000581c0c40c030b0041955a0302c0c0090340c1d1503078116a80b4041443c001d00040d6031540030070518160760400ba00450254010501e411403660020304c9210080500001050303c203002002401124803030240f91030038906005141991409820b81c41d003660002c02042040c02070089091644101c104a81c1e80358822080301003070822014681d502c02d048400600028040060581031410108481d07520a10140008c0f0000302140340300c50103500013a240d56152a0745100c000042003148144100550140010b5581c5049240400713041540c40e0f07200009104411400103600e00b105131030921910043e500d00380e001ca00c00c01089081c07258400d0100d5142c49481c5280c0c001c01c90498090b40c0680301a00d5554004000030300d0310300c04a00c48100948070621181004186041400c450000c1038080c0d042102160744880c42030b049401c0c5181da055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 922492014 1250 922490764 922490797
    0xf0c0201052b0e2109060306151c050402270c070203010e1b090c03010f050607020418050c1009080a1101020a0602070317061806040c2609010b0a0305070e041106 71
    0x1040162080c080401410300400c0080c5172039403600100b00c0d13511002d4083c0340a43c046c00200742e4070310048402e50303117a008503000c02d007022844140c2420103404141d070140d124001d00346110301c1440500341c1440c40044409411500c954800d80da01507240c012441c166095500d40e40c080501ea80c0030311401c1004000e070380919208518040511584100040034441d000c1002c200504c04c646004800c8001c491003280c2d0566584803920100380940010b1b0b01c540807192113141d4403170405c00c02090b249a200b10599611140f0b60440c14225000f03c821f01c5400c84503000b00b50108089984000e0313404092606004850f1010280e42d40c00781203a00c100e0b02500041c8141c044184082402d50050350000001c54405845510703050000200c024003900c000d20643c1c2c1c0d104540300e4103000312140400d94044c0040c0c1c4480156a04155060002c11100c0e41c1c1154030f0109071110340d1030141c0e05041582d41000003003004030f050010044000c480503000740d0b11010201084440d950f5000014241054054641c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 922493264 1250 922492014 922492033
    0x2150c0d0f1106010320013603051b0306091603020f0105040e090a210f1101110a0203071a0714251b090c051e041d070f0c0201052b0e 59
    0x304120b00c0c41091141c10071523030980506a101161520344940b907058500c40038030280030000114040a5030703100178501d00840005480f0031045400b0001c0070b450607002d503078265840c2a000c0703485044404010240722070f2042d041c03025061551020131180c1040c10311924094079a59690044c00c0d007203481000903031080c41c8a40400861000c2c201c024484401e0006900905410141503109050008010808c1c3d140054a01c500c0035042003013541030b0550b60701e03650300702d45200948950142c00291100340040ea000751074901d01c2e1265500c035641d40c0d41d6000c006061039501405a5111101e88107890010103a903800d000c941d500024000c5116131300c030112032050420344401d80309082c0d1080c4501c0340740c40e1444164940043c1155800300b805281c0200714444c01c00c80181c1c07405030383c02042d514009120001c00d5484c42c04080c5001c0c000356111005140d1080d0422148100202402800110180719404481b03048481c60400d1942c1041a03031f0700c0d2840c0004281c02ca48032110200320584c080c00c1c00c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 922494514 1250 922493264 922493303
    0x81009112d0303120a05040c0b030c2a0303040201050a12060b0a0f030b0307050103090f331b0c031110020a09050405010b09010c020a0308070f02150c0d0f11060103 72
    0x14a101c1981500a076080006503e180104c0280c0108141040d5488800003801c1108040c180e5002d0070340000c103641c5900b8a200c00d94416004200c1c4c40c3d4143d685104c06c02c9134031515004050032150603200542c82c540e10741d401126107030828120310062094800040303410090a018400c090210400c580e600d4920400c4010407120314490800141480c0c07a00c01c0004d628040798280684034282000310b0b02c07087c82e260504040007100c4c0c018181d03041048168050b5054071900c07507284800008054064200d41c100b510840c0d1003820720749002c10000105a601d280510010000e80d030090420405d803c8209074072030b06040021030f81021442e0700055040c1d16503007061b0b481c4040c01054400b0401c56042c015003d05510070060050f050148000140d021503903641e0b410703000307036500c0014940c0b02d003160b2605400384450402d049110316000d602e028145500d450555000b0002c0200a145180c04100103485011040382c0100c100303c81034a00c0701c0e0b101c004020540c001c0d4810450701806803c251103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 922495764 1250 922494514 922494589
    0x706050f061314010e09101b020705060a020d12060905090a05060702150a0e160b0405040b0f010c0210020f120c12070206030403320a08010e0108100911 67
    0x3900b03003070720340a40186840002d001c4981035604981510b1003503112032915514088032960001c40d200e003070681488401c00c2d644c60116203210260225141d2036140c604000c802d0046919500040e84101c600008162198520b4003004013800300026004d40c0302c10215098540c2240ca907c02c5500a041c0141041020014260700c50303003d2000d40761080e0a07000322442d44d20040c0c100580755480704203a012809040c0480a445035401124440389952122000e800390810320a0170b1255280c03161103501c0e0308002803118a0301c0300513500d00c4612200c1d6802c00001003903406071001148111107011201400800c241150030010064154403000401c2c0c40518066420100140140c414428000141c5510040e43d421581c1810702e5420040045205c090301c1c1d520304000d00107101d100702c0015022030700300010503902080382c1d201142030381c80d420143c00a49080c403681ca03540d031040840000001d0a54045007403507100c3c552140b0040c03d941c0000e189081c9600a844d900141c10b0758002ea04110444c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 922497014 1250 922495764 922495789
    0xf070c05041806020f0903070f0905070e060702240a0302070c1205030f221212020a05070b0d090602040e010503060f0f1b07060c0302131703030a0207080706050f06 72
    0x1a01031080c0c21000006001c10315016000800e00ca4010503c4000b44c41050140c03490340c1d06c050111804580d550443d4203100d103443c4280700c070541c0b0301808160110300c1107109091070240508040d06d488050303401d2007012034080d1170000b018882001e0b101c0c45002000c00900725521199000341e1a00a1814904004030942e4440c10803004402480c1000840101c152084200502d44160301c4000417955001d5040703585074101c4400c008201c003c5200d80340c2c24245904140a106000d4001c92820341c1641d071040d0611004d0660340c4926000c10400000300028002e1481c03419000c81e01c540f550350f41c5000da030800d81001e080100c603100140103505003000003552040d1040556155801c10f440680f00111010706007030700d01d11a010520541e80600d0080b500b0355507001c44204140b2174400802402500649000120400a6180085d0600a600b8043e1010141c030020b54519150b01007201c00940c0540011941e401007070200c0c10124501d48519442040d94490000b0783d880e040080006458542 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 922498264 1250 922497014 922497019
    0x90b0114190513090c0306050c25030819020d1b0305131a0c160b01030228170f030a020d02010c110c010c050c13090b0702030f0a03020304080403080f070c05 69
    0x7034504111030340e12520301d40000302c0440300c0001e40c9042414544c1c2d121100b0f40015000504090902c1449000c2d98028050013100580f00d01144420344003101024203501c0b0090700080041002c11105044005440903400111000502c0e001e400351403903003a0340061620f4090f020091903101c80240e09030150b030b640001149903414070414030355990140f0b58147c288082691841c10001900c40c503403c012200c01101d081c100b00072041c00c41c60450090b080074002240100c490210014140350255580042d4415400d50f0389403942c2804424070000c43d8100c00c1c080903220301c0d6a00d242c1c203003003071006100d4110b55034081c18846501c00d5000e42900e89102c00581004403996002d40d0440010481d40d8868500b403070000c1d07481c1c4542c1812450302c0100e80d5103681c040010800094128081d51020554901c2018810181c2c3c5e24558266141e000d0f05002c20800c403030801007100759a22079401160f205100385203075070420f501d98440c050340d904450a8160441c400094001c240020504843c1c001c00d403c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 922499514 1250 922498264 922498309
    0x3060d0308151c0b0a1b0c080706060b09040c14071b260c0a0501270e010f030b0109140f1306020a0503010806061f030f0b1806151204080904090b0114 66
    0x29130841c4c2481106e04840441041202d8004600b08440c02003203c06194002605014058035021003c0e01d643c4141c1c103081c8103d03c0c080d10b52003910300400444500c450140002400c1030110f842c1d01c10050b007500400c1c20384c1090041c003ca07510706688495400d40030a080c4a2207030380903140b105480d00d42c0041c01c45100381e01e084010011a81d215144078240d0b0003940e4042614465000f02292220803034001149083c115400880c3c901e50514070b02040303034054000b85610382d82c0c0e5210f040c05c0740c000203880c607000302001000454088242240c4c6070090b5682d2400c80785070010341c941d03030200c0c0c12490b8800002200040100230000f400c001590304040c04a449985003034480f00091801c050b00171116080c91f031203810b4a581c0816aa1006c084024040c200e035203142c07010b0079190344568040352024414852209115480803480d030943d40140306410100041e0f0301d95842e00300194000d0040258007a441381c618000041480d00300314020300c485da01183c108081d200030050001300800c101600c0152 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 922500764 1250 922499514 922499531
    0x2010b09060d031205010b0d0b01230a050417010603020a3206040513052a04060804140313030507170c060a030b0d2603060d0308151c0b0a 61
    0xa400e010280c000c1c800322060b44050216141c2521444100b80151000b1403500000081d4120b081c4024450507180c002d0420140140d00010b46120300455007900c07000c06420595001c0b412400000e100786100390400300d0400d40c0e5601120701c001340c515051401a5155241001142850710f90070028010102e8050301a80900314240050400200045840900064803a4440e00d6a508980151030060718600112070060344503400380400381c54208803010590814071842024030490510500c0341865540742078508282200c003040c001d04184da608500300a00d00c0c44039070810041140e038807040d102c07805003071940c14550b00705029a40011228146c0148680481e40046103642d018142121001e44884c0b00b00030031401000588001a00700381c00c48103134414400c000220600d001000003100da08a50a100040718074001540d0762608408551007010000e03000b40245540485601410011030540d000000c1300c1180090803010700e0050700112005201e00003804651103500c0364000e0200c60b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 922502014 1250 922500764 922500769
    0x1103071d01090c021504110312070c0e0402060f1c06090903020d030516110c06040f080c03010b13051302061c0e06090a140109081c0b040b060324060f030609010602010b 74
    0x10750a095074905c0002c100015003007181c41c1060b0078034800068100d5032481c032448448400c6a018030401e41c3c01c50090702c00000d000e0a42c40300c140c8a1607018010a0902d1410b030800d0045800601009000c00d10b800c0034424580791a1040c0c40040c0815500411001481c0c100030b400c0c114010360880c02c060410041003803d80d86694154030020b981d2600002002c04c0800460410f0202c01034260320550010b0f001070012400b080c03000644100f0400c2d110f032140c1000400d803c8810009040307400200d0004190003400c050741c0f04039808030300040c0b1041d541c0b80c0795000400541c42040481c0d520000c0340301c481310030401885150800703201000108024100720091654580d000d46c40105000e02c0080e0b00c0068820a40021210f43d0b0b0001126450311508200500068580c49904030401c0c907101150b6620700d068041c2c0c1c0000d84001d00141d140d52501d150700c401d1011010500c80c43e6030134503c0c0d550381c01d40b58030300100b9222084081160303e80c04c01204004083c0340603400481168100710b001107455 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 922503264 1250 922502014 922502023
    0x30305160e060702040e01020d0e06010803070c17030c0d27030209010e061516171c0b0102010e100212060d0312050a0e01090b090106090c020a0f1103071d01090c02 72
    0xc0794200c031072980380c3c2c0080c4001030140080902c0440e96500104a01103c0e00890308482e403c0500c4005031902e503030300d0701c2ca1386589010300c20001d040b000f68044100590304600744110382070000c20040d40e21b003503080140585050361015010300041c4004504942135680003c450740841482d0401d031500ba49541c000405980741030042c02c7c0500c00e458041400d0750740b41c0081d0405100107440198441c0c1006646000a0b050319100359214849400d003410090142e10444203e100d9104a413484c024813011008000c040000d1042d05565036000001e148050402501442c481c2080d4003507550903c00495002d804400703010f1502801c004c81125000980001c0b5519090b255446d0000e1580c1d44c5290440c0948040c2e02c1c1e80344203528103460001409003806840d403246ea0482c000340180c2d07684d5941481140c6e080d07640d030001604000e100c0d10000300035a82d100380072809641207103400080400000e081c140740351f00500341e81d11601c092408001816886600400e003010040000c40010107000c2c0d142c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 922504514 1250 922503264 922503287
    0x60b0a0b030727080a0b0a1d06150103020705100506010905031615030b0108130c030b0a0f110c0705060d0e01060b19090605090910080d033e0703030f050c0703030516 73
    0x17107903401b00000f04484000d600003001098180311525006210004e107648072901550131050f441644444031140303502138000c403804103501c00014102e0b0034078158440b000f000e010741110f0400c010713070b0400a01654108101c5010340d59151501d46c2503071030901803481100c2d00b481100141410102e44220580e000000719611203802d201a49945050b8a480500c2c0c1142e0380000300b6040701d8409100c0d40e141c10381d01641015840e00d50412039500740e0b000d0130310b0710b00904602c0700c299401040705000c070341001006002400c0500c0c101055031300c03045140509460081d0807420030100041152213000302400d01d1501005c8141c240a90110300300342c4001d20387c0c450700404601540c2c8401c0480c5d030000d00002c001006290100c1500c1c011018500000c015100aa401843c43c0f10034040d0310f01c120030b200d045802000034035207149401c044400c1c1c0e00030316900643c01c2034003403540c2c9009460394034005015480c0704052039080b01c1c2d62101c2d05c0c54050201c1c0c4c0c1c06090340c54102686040c41081c144c120440a84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 922505764 1250 922504514 922504523
    0x1202030f0f1005011202010512250323090c0d14060114010206130c091a09090105060f120705040507020a050a030c02040614090a0f150f0e071b060b0a0b030727080a 72
    0x102b50740e07a145824810301c203241006240c80c60882000a010781c9a84590100c80d1184c50820303807080000c0390f203086d44806540341c03e8036410008080000b4509066098942d5208012070758812001d403980c2400c20000764480050107a9140e00c1041c50340e4180070203907004c0e03d0044020300701c50454981402614141c001d001c1041e54031100d50344e4007e00b044c0e420356203580081c5281030601d4000247c0d40a0002074442d60302681f04040c40791403501e4130900800854039044001d00d10945000d042102504000e0541019802601404000f044051000d000001c0c029110314003c480107105000c22100030303a0001a516000b2081c00c90580d8402072415040506000c0100700300606198074001016568241410010900c50000d9104070021000c006c03581d80940b070114030f5468400c180d59500031012154580ea1003042c01900041440e40003030020303100602410769598030366040b481280d109a60701000b0a200c218480080082440400f10000c03210358581007003031a10601c1a03480840940041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 922507014 1250 922505764 922505797
    0x20c1c0c110409170a030c030e240619150e060309190203100e0604060b01050c0a03120906051302120c01050703140f0708131401091202030f0f10050112020105 70
    0xf41441071110203060480321303d50406690300d10440f0003074000c0030403000d1a030119080903c2008c2002020400c0c81c41809044440800000396090001940900812031a070010b60381074481c050680280b07080c070141c12120018807102600e264080c1121160034072103441084100200f1111201c0814600142c017042c03480301154000c03d1000a0074040000c40102580f0310300100311511040000303080d4020f40c040c4a080083d4500d800044582d44248a0008203540c0404d02d0390740002d105590703448010403080000501849140d076580180d580654200e840166034220520962900a05e22107510110b80c000b030803007a00c0480042c100f07004800007d8240903240d034461040f4641d0004403164038103264291582d4a241d464000441d41008041070560784002da0046407907003508200d2110312005071110380d41c0318607180f25800d418a8400d012a090f02074403a100060400810891400200000140c02170301095209101100c034143d00426090524401100141c1d8000c4203c4801d01045170f81c90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 922508264 1250 922507014 922507031
    0x18080708180306101d0f010e09120f0703170f06040b060409052d06030319030902130e0c090606090103090314031f090b0a0e19020c1c0c1104 62
    0x8407410030350508a00c0d0980a000100001801d01d19509403d40b000710940b0341a00c21448100b02c2c1c0007804031442c0149106050050240200f8004055880078180c0125144080303944c0c6401346076000800c0310101d01c1c2c0080b175942c04058201146801c1004005009902440d000e0900c8420b00c0005d07080d94000ca645030008001c81e140c503000c5401600079008140580d040807981041d030401502550501d454103003a1702c001e5442c040c0f044c1030107210020020750601440310710300607d0b000b000700f13201d0603d991400404016290340304405030848446100062008215a070f85040082c0100788500c00c00c50901000706a603142c1e010349404070800e18000481c0c646a00d400c1c0c40c50103022080c580400c0000c0304208070100000310004141c040130141c05007295440d50302c10203603070503810042d602815504007401340400200019070700c0030001c400c10013050f038290320b194104e038071a0444c0b0007580c00c81402d4002000e440000c0390102e60192401500501440d160706a8100407038410520035900d54455 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 922509514 1250 922508264 922508287
    0xc032b090b01062105091029010f121410080a0b0c0304060902130506030106060c08070209190216050d0206011a0a050909090c0108070f0f08100902070f0618080708 72
    0x2400c4140703030b941c0800c00350a103050010356400c58001c207896500d00740720b420040c403005080381c83c03e00c00108c03052005104810005444e1071941104d0303d020045402411192441c803401020344c00380d04101d072200d80e0f0a01d00c00c040e02035410380c0c20030703100e6502c600310b0600080c0c40001d60703a60110130955000d861340c40340e02d41503001e8032801303c0c0030794060311000700c03400101e1640d841240a26000c90007000100d5840c1c209948201c0c82d40030103020312806105a80160901c822030580c40381c58189242d030500108540c00e0101c0e00300b2070030b06510102141030314040040400c440b03a51900c245c001080190300d40741c100d802c0011030894075070310504007042d4a20504e00840c10366194203001402428245030294181d42c2d00d544001070031f0700182100000c561014050001e080b074405d2959203030200000d01c450141c0d01440c0240c4078501c0300e4030b10b110010324075034280301410a25103e900d800c005010340d400d140085e41d072500404ca440035041042d0070f00041c000c0c804c45800f5640512019241e4124801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 922510764 1250 922509514 922509557
    0x219030804031815031a0d0812151c21020d0339030b0a0902070210090e1602070e0f0f100f0909150516030e01180201140c032b090b0106 60
    0x500c02e030000d200d10921000c00c07239200c020701071038150f0030380804040d503e0900d40a04802000b02442e0000e5200c0109202030300c00d1060066817500480b201e0010a1000603a0500c0c41000020300c00143c1200210901c1b09034507000301c078940400a070000c00901c0c1d030120030303002e9101100c03c914181044504103010300c0b80a9001204864001440c4107042c1d503442150f030005c2c3d845548120300c0b558511079800b032000c3c018040d40c030940c0c8c0443d41007401607132a04407122106a110740020154480c820000405206020b0024810b880b0074406405900f03021111030100b102c040c0440c2c480701c08111043c000c2c0310088130084100d8640220124040c0c520381800e00000945d1104074150318280010803c140780c41030591001c440843e5420002c0401c80e050b000c1c22203505800d6000d410940e090240d01541c4030340720b020880303140000310070303e4010590012032542c1d200181d00850701c8910040000800814205e030404108a00011300040d8180e507070f0383d0025401409010b05102d83c0c40115001d5070042c14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 922512014 1250 922510764 922510811
    0x150102011b0c0320030304060b01050c0703140304030b0a0e0114091c030e16080c0402070b0103080c010222050a060f27050612010e011d0403050307021903080403181503 74
    0x103c0007800d01391500000c6481754011a0142d41ca40d007070580e10569944134000301c03015076000170091f001c01c50850703440800542040c8074041481c0b00074071012003c9102e0300603c6d402889441000201d00060718145403d45404214407411120340504205a405010800c000c1d22420101c0b2404040915030050f001000c070805010f54910a00141ea40c0f60862a24004240e90540c070489000451800c02c02007688a0090001c01c0344541d613004000240705140a407202e110315100150403c0c1049807030117016000080c000c1c402d100480c034100a2030030880d03c0080506442d00d0500001c16180002400c84007090100007035455800704619860300d0800002005007200030302040d6a0405a07101c50011842070140f07038230801049000180300541e80112408030f02ca40d0000118a0741c1d5a10141e0744d41e00002d101409600420300c200e003980b18504500c1c0140c038460b88510050b0705150400401482403d071b480449003154940502c1140c00805a848502d1100c4c0f8000c100d80682d090704241600200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 922513264 1250 922512014 922512047
    0x3090b010b431b0801061a0d0b030607080f100302060702010c1b0b0a0917120309100216060e120919050301060602031b0c0f28030b150102011b0c03 65
    0x8010080803c48222002d142c412411000d010040c0e445510103400c8070028810102101c204045249048203860050121101f540d44c1c00a0f0b1010b000e004241414021514000010801e008000d5585403d03600e040e046640d01007c90292411a0f010484c10304c6070f100040d040c08005144842000240210300120400b00080c0d1081d09641c0c0603446e03910f0f005811880d020803004000402c1c5045049007103034003161b81c3d00045c030309101d00a00f40055544051300e020b51138081c0080401a80c87c05000412100080c194083c2000c0d03441d0030035030110f404d1240941500e800c1b020001c1e0b01c00c1014029501008411078064280a66101080600e1040c90717004c1b6406508080d40041e1311900400500700048a80b03401d00c2c101460000000d03140d1890138641984540003824040081c00d000c9014946411902400044803402d040240c40400c101e610444015000a040103804600c60360701c104a040d003130000784584440e80c01c540062402d03100c501c40070041d41b100e600d424140310365030500d0f025035103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 922514514 1250 922513264 922513387
    0x603070e121c110109020d0308101a0a110606090a0b040902030105090706090b0703120b010507021c05210301210b01080a022706011809020a03090b010b 67
    0x24403100b00c007208a03461194011500002120b03421a4040c0110640300303600810a90000d0010380c0c082d00c0381071000c0c00074441c580401c20049100817801a100c40030040c0080802c0d25030340c03000802007088120300c02180841c3c1288042c045251602000f4130b80082e6000c2004c929070309110007181c010700d035004000e9415800c0c501440581d01000c01d03c41c003503401582c0d502c120252140d4074205280300b00c1400500107040c403110007056000c1c4d50300401b00131105141c03540c60003c2d0b5400146862042c182b2444c10804049141804c105081019520342c0d020449030384400c038030710100b500c009d0005214440d404422200001100300030801014003559000d01182c05558460b40200d41c0c60615681c22400384819900708103001c94046c0300035a5040c41e00726006d01d030781e48210044451403160781d0509407540303044001094581e03860015100c1000320380e4000500e00902e082c0350703142c0070040e400303844806d2003003007a0210400c0c81070344aa1122800c02c90000b5822070000850805420030021807070300180d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 922515764 1250 922514514 922514533
    0x20f03040204230403050726030a05070f0c03031e021b060f040b01090b0a0b2d07020a0e0c090a060c03030506031c0e010c05070f0303021b0603070e12 66
    0x141501450140e40240d9080210a020104203088202c071011400a907038962000a40000e124000034003c05205410f10000b8844c451807212403d05803002c128819107000c003c101c0066054400c440c0d01c0300c0740d480c00402180d83c100000e400c800690401608141d111205105a410740d41c000c48012441c1c0c4500b103581e903250751911007000c18107205403071407801103001042a40d507003100a5805148c10818040459180c82a4200200b0b1503a40441e08a4140500000c1e0400000301400c55804210354030060780c0d0921180303070311400c1e100c10140f02d061030500208026889030201a02078a072078108081040c0c039400710603011800764100c4c0300d9100702144008a00d041d40000d8506101f4441d40b802c1c86035031102e00401d41c86290b80d0342205800b0030845010045184180403803000c030081030400a42904003515680d08002464000102140c1410f904000b015410459400c84011400c14154034051880000d220b500c0301518220400079881d0b00814280d80e440700b0001d0408044048411081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 922517014 1250 922515764 922515787
    0x60406030606081b0d02160b0a05060f03121210030804030309050a061b03081e0a061a070c1811070b0403030f0903020312220506010f1a16080d02 64
    0x3100b40500e00005444801040805100c60075400d203e4440b40d011600380b140000046009412010300401005c1102c095080899201d501d01c9010320b081c01800300da545401803d200b690110f030304516000741c0c000d404550050000d8030a60b032810301400828851505c8000c440e100d2002107420151000c88001000010540c2080c10141220000d030b6103184c4556891206131b070303841640740440c901c80341042811400a0b204070300040d0302c140c481051041c24071028002d8800a202110b113040c52642e103010511010300c0444031051074120ba01421882e080543da940d20410680d44103109040c500d081400007440b0b00d5410110400625041041c0c0f10403240c00c003c07110080c2a0b41c02e401080c40c004a4214240442c0070b2990180d0300b680040d441d04007a28802d0110900040410003d07501e904201400d14046950b1400e03164029001050254181525180f208406a100c0f840030025421850300d0280084c06641d48140d0641d010300301c0e0011400c14482070b01c074000c0110380451000500b0b15040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 922518264 1250 922517014 922517021
    0x210201050403080f04021e060f040e010f090209060409150e0c0d0e03040f0b030a0b030312010e1f050f0307150207140303030106020601052b1514042a0506040603 71
    0x50b80039a85820850302c68090261481d80d041e41c2c040d400146490a00000022400440a8410018115a15002494503900c80d982c100e5000b05c80000ca03200010400058040c1521001d0100349004500d0320810400294841c0314a2084410050326070555024110254903180000c005070282c445403440d0590611076580e10044c104544c50340307085000c01d40040000256816501c2051030302c4001400e00d902c10210390001809041c54903210005405240c0301030024111084400d080090903504103441e020007140000d041845442c50898a0b420341d1407080d0f81c050840304141e4250f83c50340070a5011904200458104890044d682ea0700d42031a107074001074000032100c10340f001180c1c2070811002c00d500c80c4000e1284900583c446001402545450044180303881200b00b00f043e010f103c104072b21150a50070540a0301c222400140600c2188001e0060201d00170b0b0442760083c05181983e40c600c41a19255200e000c00700103180b032600400c441c03080003c050800208404d449955405005018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 922519514 1250 922518264 922518271
    0x9221119090c0809030a050f0c010e0a03021002072f0a14010908011505040b011806030f050f0603060f070215040f0507080f0303070e0f10090302030111160b0421020105 74
    0x1c00d14251449624610845880d8012141c0718017451a2007074104080b5510b070030401c55000000000c1040224061091040840c24020a8041c0a40340c5103410702a0400c07007107025001106d0b00421007100040d0040c421a42010220f0a8203034040d00c201c0082c1401600c21160340d50000d0120030042070a050400c2c00700000e1509985e0307448800d846144041c01e8890046500002d9030350010280030b6490182c004500901c0d042c58500d480640340b4000b0b24620f901544610040f0350f0710a205440084240142035015007040c8100f2407a0404401080d81d91030024011008940070601081415200380300750034800451001c0e0354860308290a100a80101d0361004542c14494900c0004940c1c40c041075190b0780e45030b10302c051819907941d204142d030b2965650125a50011446064140360b030740d03d00c2d4806141e40b440d514840c09a04510516003110079440c00a1002d40003444104400110250030010300c640c0b21480c100c8940b528a0186126100d1698001000040f4184111060707030540c8050b10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 922520764 1250 922519514 922519529
    0xa0f03050f1b0f0c1005070b060613030c0806010909080715020d02040f0e0f0103050a260a031b18050d020a0b030f0a05010f030209070804031e020c03070509221119 72
    0x2140b404c450402c194054002000800f04005201c94004519001c10080e400080689198a4500b900c9411030400700550012107803034440200034030401c20304002c61405001c8460003000041083d0301c40c0d82290240c45e000524124250050303448085464041d0b80304600c4000e4159204d03911105a00900940ea00400c903c0c0f5181d9400125203603801c0528504a0fa0400d000d802206115140d01e81441d6444c040944040d00c151100854100300341c00610344074030701c1d80d0001422804100402030305e1490070010810000495001c0d0420b140010000c0b04a8804955401140b900b51001c20303400705041d4400a0147c1c400310811011012120b82e0612848261780d0805c01d981e21036103450305004180c04065040100d490000711010b004180e071b80d81040c020305080440c0c001c00d0ba502d180724100b07400d41e200141c000c0300921089040402c260f0700645411642c0d4a0640303070042c14803074850450461441c0114818688906002000d02407041c6403102501980c038918000301401c0414000e449403c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 922522014 1250 922520764 922520773
    0xc12060902040602061e010e0403030b0d0317070309030905010c0314180a0e0c07062c0c030d02151b120f01030b060d020108540a0f03050f1b0f 63
    0x80b004148130445050052806c040c0014903400c1c03800d0000f102c40010b00032001d040e070b21400401036030354540b00c1c403c01d0b03482580c4110040070003030f404041480d0040e0500c001d140c03e2103103030000207400c14914030680f5820b00c1d2a4803522002e080031205010310882c6820581c4000485809141c02d04103c0104280240c0d034050546503104001c1000420858a021204009015000000e1f1054100b01104500268038002100d00e0454403070300a5075031a03880800754030188e002c0b5103500301030140b984001e50382c0c0060180c0060006001c20b903900000c1800e150b940b030108115000009440940703451351310188424003940351408152062500030f01043d1031000804000804519100641402e1a07506940d41521502c07411140000e50843c24860790410111000c0b030001c0030224200c60310080381386a00c2e0040104d08184888a4000c225074524040c1c10841e07020380400c07106405022116414984240d640c80407240c0340c0011f0140e04a401190380000c50780c00a09440002c115546034140b40544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 922523264 1250 922522014 922522021
    0x80f130501090303081b040b0d05070f0905030c06030702030415090609092f0c2d07030203030417030d05011502062d0402040e120703180302130c1206090204060206 72
    0x10b440802561000030300180e00200001c29507846a064840c80e546202c00f410b09158039180d28541a400501c40416407a079900c0402100c81da016008101492060918010300d0f401d0101107505d58105040d440d004400000204094031310070070850b4014031b1003120084946840100c0107018150f14450078000a02e59980400d200400d48145596041c02e2a0342c180c208010407250110780e040c0d1440301856120030710030030349009018040f480b51140c80510030200c104814100094603c08150310103c01d03409001c052006842c0001100c0646045060b018404524070b040d1510318401d00400f14040390170240000b640400030a81d040c14101c440d000d48000f50394a00f042d049410b0340c4030030b441070b14885180e010400350110717000c0c9070040c0c00030300080b90340381045051603d8011020740906035a140000c00c0402c2c1540101c500c00c0d0703841e941c405800030516580006000c074201c3d421101c0400c1e07403400b009490350f02406145c00d130320015500921140ba900c0040c98000d4201e403081c8009802420000f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 922524514 1250 922523264 922523267
    0xf0d020303010f1509150c0b100b07080d0221040b16020607030b18011d070801030305091c050a061a120703060b03070e040516090504020a03140a080f130501 69
    0x10340381030b1403504141c11119490804101c140c1d144c0300400703405002c4e6540d8045903501c944211144d44a4480d00c900003480050700d0108a00440100240d8070072403001e4043c03021031031620494440c1a0054980358940c0601d1428100a00c01c10141003034017085440403041c0e94200d528070f24800c5001f10100001c95496003a420b4034010100010700c011b800890000c0c0009010340d0240012000152540328100015120700e00c00250170381146a4240c0c01075a15200d02c803040000310340c412054030f0503040c2e5514559000d003140c010104403078410807800040b411400c8008860303c10701600f0400315590488107003000002495200070081d001641e209007402c09043c1009032000440540c001004079030303e981c0300c420080c1040380e10356a0500901e80c0c0052195000d042e8140107a0061002e081c8820b010030004803490095840404c040d400c110402002d661f40c410500203d94021024080e00048003000506050300424001c00c1100040b50201c8102034200280c13596054500c8040601c5d41c80301300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 922525764 1250 922524514 922524517
    0x11b150f02161202010e030c21160303050402040b0d030e03011b0801030f05150c040f06030b0d0224130503010c0903020306150402071e060b2209050316050f0d0203 72
    0x280c04041140c0d1070b0302d000580c074020315070058002d840001040c01d2044480350656000001040c039583c4118820298805504284402101c019903590710b002510502c0034003441300001c000c2c0c207150351200020203541b169006003d61107030003440b88211a1091401400070001000042c0c02980307401c014110140e0020050001d14285032990072941e8030b0359440040e40420101d08460030f00501c04668918100300f0301c15801450355401580d116801c05958021255585e4000702c10075003040c100030190345401039820409034041e81d410300d00c11003a215440d00052500041910780c10009a500b017100802c03d84081030350ba044000b801884541d0760211020310a50002940c182c1147c008603034401662071500010600107000941042c0d03550301c949044500b0844188580c0ea002c0a21004100661041d01d183c2c90701180c2079540038401d0210100740c801e02d0001c1000541e6100002414410100b06031100c01000da0b00c46040e80701ca03464820b40314203a0707800c292a0762107003001c0c20411030700100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 922527014 1250 922525764 922525777
    0x3021e01060812070213050f0403020d0201050705040902180319020f040c02060c071e08030f090f100c210915020a121e05090d021e0606010e011b150f02 67
    0x100a0681c0343c4810050b82e01d036800107004990100d81458220340510081c0a5284240883c920840c4285071505010b824600444034038404c59162004100c0f0f5030303400c08107880c02d8a4540c0c9005859059000d00c0c11481100a400680d042c850901c1c0484841e4002d500500303e94820b40b10880301c0c4544d5000e01c030681d0014044940980c200300c00044400c8400400707030029030701808030310f5820780c2c1144440101881d946c0007900c52120000070018003180740314203d500701c40001d004042445504d0354154035982d9070715080313140c1c0b41c070358a0040c81c02d03103d07941410302d142115954483c4280039002d108001c0592800072540c9416082c5801080401803003a1000d4698640b502050700005c031079107000500341c40b5140340e07405903141e81c40184c1c0314451154900c5100b22a00620b989012040042c1c0b801800e001c0c44d10740b0b040190f840c15010040410740940100003800c064198000403801640c03d020300d0342400003000718426126040c40214601c001d2010090039041281003600d02d00c0c10164800c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 922528264 1250 922527014 922527029
    0xd14090f06040c06180b0c0a06050601020a0b07050310050307260601060c111f0f1e09090b0103060312180515070212010e010c0206010e060111190312060303021e0106 73
    0x100f4003000058012080c00c5402c042e812551042151120100525900200c000a89540c0030515030310401666120b1290040c109000501c0300c29040d540780084900003c101d04104080480802c014a0b503010200b006000c0040c19142c6094a0381002422031148040515401c614104070100f11030001c120300f8143c61165036000c10940c4c1030349420202c80d04041d0748682085040c3c8449401da40710f40d1011503415102d079509030460007085801420181d19200020a0031442265503c01c16081000075040300c00703199000c100044e40c41c0c01070b1300426180d40040c02c54000d1030441491283c4c04103090742c2c40e990008a00780d02944070f0050108001c01424007441000b01005010b015182220110402143c0600081740188501501600b03440302002d91501690101300140700c4040c51404003a07100d0800e180207080000071280c0d21303075113440052542c412204c5100032401814420110702c3c00500b072041e0140202c1f075a03458000e58801102c144030391503406500f0541400c16044c01800c00f04d0750742 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 922529514 1250 922528264 922528283
    0x150b19080601230d020a0c050c040605030a02010804050a08031e010e01180e0a140d080606090306130302101d0c0a06020c0f0a091112090706080114060d14090f0604 72
    0x40300000d840400f4610340700d5807049800d0010130f0700141180001d003c0c14506942e07008043c2c0d124070700b403490076052014140c4560304008080c80700b030318006031404d80365409103001e0840741c86605096003040b4051f4800b030140381c0000104140c40c100c1e040148012006500390511981c1d0714020604030720b0080c013984246c0c0b40e40d54001110a082a00121380860003142a5041d209144c2d545508081032102c04040a400100c3e4800000d07400030001c0d9804001070391442d00d00800040000e0702d0b403000a0120003030700d04a007802400e1601c208001d8805c1d04c800e2400308051104443c01203245122031709a883c0398403988403c1109810000746a504413680c54009000c81c00100b0308200921484020054002c500c0000c0060500c03014001c41031036405001086503640d507a800741e95001c0d500108400c98540c001c020070098154000015030464241c1504d514034180c50f200011b00c1c41c4908420080518140340c002c4400d4080c201c0c105004070a00300850302c5405c1000c8002d9120340301218068491400c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 922530764 1250 922529514 922529537
    0x50607030501060504170f0f071d0c041214060f060906030d090e0604020705120717250611190905013905120d05011a09010f03150b19080601 62
    0x2206c0c45240c0c8035611160a660070000d90300b109034074000b00b1041204141d48402e108000e40d00c043d14064040c1c107000c44c02c21200746000383c0f4883c8a07100c0e0344a01954448a010343c40d0501c0306040d00d04c21407a1b403032402d81c0da09080080481040c41c0d000d0b00d00070b110307144241c042801c51038001000c0c40c03507520a4560302c0d44107151558041402d03000800b420f070065000c0060a0005409020310403103c201d0b51751842d102d224038100138034050307454040042103c0c0c0410184142071128510a01040105201031000740c60500d8401e028100c848160b690741d1002190108404500b0b101180c03030400f941c0da03060820b44e43c6400456814031140d980ba1040516a003403c0d50300801c0c545502920010700000702521107007507a84038905030f0451403001b4035200c0400c8281d001c0480e8011180141400c4625940c04884d00e4500c01d0719109001c01c040c144070600c074006240a0294000c840480106ca505d0460680c0e03503400b460041d03000800301d000701c5002e045a00040b034041e08a01d401203030182d460001490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 922532014 1250 922530764 922530779
    0x4110307020c0907210603141204030f030309060216060e1f1d0f0609010b1819060e010609092708030c07051c0e030106180f0905010f0504050607030501060504 70
    0x450103045402080300c400c060b4444a5981c01d001400080d00485c00070f1072902d0b500341040341e01404040421190424641039181d07601903001e0f501540d4005e100303540280c10700d1809400602810100411140c004514a0400e007400c0300c1200720b00b80516130601c69102c110b41079907200d200d114a0100c2c4043d500049814002d041d0b444880c4e0400b0030240c617001803402c041d4241c42c1c41e1040c000850554000c01c02c10100b8042801603854603802036840d000c0030a01041041c41400000300f88090041c80c0000c650400392564010900400d00c0020b01c91a550316414018014002c074054204414207044410710740035403140c0790724044050842244c070407c465580c3d20782c132a0300151501c0c80a640a200220200700c0900900380c000758070f44200d104600314501c001c2c210440b0010350500ca80d15021007040500c504410034003018100b00c800140403442060418000e159031200a003180d803a104000303201300100d40c8600e0142d80160b0894449944802e01102030b24824020580052010700c030400221 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 922533264 1250 922532014 922532029
    0x1008010e0a0c0e13020406110307080d0e03270114090f040903181203080603241308070b06091609120f02030d2003090d1101050f030a0b04110307020c 66
    0x40030146000c00f0880a0140050018000030514188003580050204a816000460702d070004103c0341c00ba506003159a00c480f00540161003403450003e80b11811410941c00900482c0e48110b60101c21032410091440704003070441254201501146002c01020100c03ca003006490043c08024002d40304440300380705110190505c0354045080c410f103c40915502090f032031000e000340030b8843d9101c0101d42c0c14200140640f5010f4400ca01a4000340f180c0201307c000035106c840e06400100030000e0580b1030300e500c8011003000c228054200e0344045201020000c404a040c1d000d268120303401c203410348a10544141800c4044030303240c08a06005010041303102c480210421031409103030800b90310b04098000c40d0510412020070000502440e1044a802d07016503221007880400c00025400e00005c180403503030b42c07041464060221402c0300f0b542d03220f03a0703c110b040343d10003000004925100c0c1400808007011b040b03202c4049100d542070000d030b560192070b6072054070b104414941c01030038107260300000d00808 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 922534514 1250 922533264 922533281
    0x60301111801030b0a09020319020a0c0201030b01050405151b0c090f0402010c0f050105090d020309030c19031202061506120613061a130509010303020a170d0501141008010e0a 77
    0x615072035010413045a6140312284005101c8800003580c2c2e80b5018056008442004902e100094411b11004008a620844103d0810340c282400a0003400700c4005903114011a0300c1164480e00883c002d29080d01c20002502070f440002030754401003280e086c00369480e801e0480075180c03c4010500020010b60040040d00d8029006040242000201d5151203007461011003040e501ea039190f500b80440700c0703001c000c4104280035520165042c14010710000e62111002e40d0702c01d00c01e201050440013100001314050008661011010480c0001c0c1ca401039112102102c40300d03020500e41c0310951582c20904111448103507000307400ba0b003d0fa1040100300c809036a10940d00c084e581c1d0303640041806828042d2040c02d034903896400680741c0c10492500c41d95100a500014081c4005c50300400009400162070072016900045a000c12150301301c1c01800390080b001d849004605000001400c45864981f88120880a0780c0004000440c41026100c4d40d4085c412506000380720000150603283d980d02070880d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 922535764 1250 922534514 922534517
    0x15081e0d14040803070c06180f0603020703021513031b080313050a0606030c260a02211605010f0503070e12070b07060e0706020a0f1b030b0901090b060301111801 71
    0x41a4483c444140b664000d954200d0340c107010341c801880800e81040c1c554490001d141c2d000d025050815014401c1b80704c0030700c034610502d0b40124921040600034800700f040d50f12000300d0381ca50362405001141c004544068207501282c0d6080c0030764501f8100c204501c0c41350303800680052654680500f502450300366900155007038050b0038a20b00029000d030060070025030181492081143c10219002d0b0351a15800ca0720a040303205a02000406202050f41c50b04d030ba8040781c40d502880082d100c1c14980100c0c2981c0d106a41c0502c00003c01c09100302400c150550b103003a0303a6001a590411030507034a078441901c60b80086659040801c0d0f0a04c2c0442d1104c1da400140c0081d10300d43c0c0d07070b40c000c04d045603008044100d90f0756407103480140f07e0820803c00c0304000d08040c1300030205a8195104d07200b0108210700054060005020084000d1001340004130095901ca606610b0624003103440600030250000201c441c2a41d40300410b6441c40c05001d040013070304848080c1c030b2030819100250f600525011244d1030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 922537014 1250 922535764 922535767
    0x20613020d031407061406010e030a08090a0803040603020d150311150423030c03060408070f05010b0a081014010b0a0305152106130308010b09030106050415081e0d14 73
    0x1465903c808080c0442900c1680c001c2814121000d18180d00000180701c203040000c6120500c103a40e40000e42c0583c00384e0031030203099880b071009000c2401c0003101d400521030b901c00000d002800e00d52541c010a13034041200d50801070b0410242120700c80c01c0c00b074840075202070848604140700380341070300b60081c41400a01c1313a603181075980c62040285242c0401c4003c40351260000300070081c101480407008544c030807006052246056610780106009a00010704580900494182000300c254840c01031128003c1c09054415030310b6002c40e546000030f505884901d03043c01c0512080b5100c0301c2516041ea86c03040c1d0310034185034550804070010715000f00304c031074000d120006024181c3c0740c81e2840114288031038161a00703e4640d0112030300e4014007034001c0421401e00c4203484003196000310003d0646860422082ea5480348a0019001d010141c0010340c1c0a454010b000300040c0751207450b00304460110007590020b901034080c109007000140088995600300c500c400046520920703103035480b42c1c81460001d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 922538264 1250 922537014 922537037
    0x103091518060606020f1501030c060c08040506031005040b040e0709090f060e1c02121c09020a0e1501110a020f120a0f03090b131a0d09110f01020613020d03 69
    0x10b0054a6456001e0005600540c510380d085040c14003401c43c1c0d00b8441d040307901c1d4551660381d1300352036104184903100030000341050040c02c0103020b83c100c4005000c000d01e0162a410980303000d5030003c40c1840b901c3e201e20703d0322001300c04609050140d0001102114080e015107032a082c046406000c04c07813411100b04001190140004000d0b20415007003e495034014014400065648400c0c0006c10302602d05551004004c81c1c5040e800c0400c0703c2004012601d041c10080070790822901406001c00000d50052400f1000b00e140c404136200c06205001205400c03060301c0c1d40800540c1d11061040c00b404094008014500240c00d000ea18003940000c0500350402e10510882100e00340602000203d504409080c1880c00b81940050500082c1c003040880d54a0701c600704034042c209206034400c1001e20b59009200c81c154404540a882c241c0b0100201807092111602d070013000001404070451003620050082c04d06940f0004071030384207141007039075071486020b41e400b085510340607000114100119141203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 922539514 1250 922538264 922538273
    0x4060b041e020304030f09080a080a1403070e01030c09030519111809070e060d020d080d0f0608060901090804030b0c071401020c01111e09030c0d030804110103091518 73
    0xc0703080c801401030702d9040900d8001e2004910074242010802c1c155800d015404010440f440d000b031744603000603900c800c809416126450a1031034081d03818008420008025040103441d503004000742e07401c05c40011142d40a89540e00c190101800507032100f20703080e0086050a6000442e54003a5000e050034814200c0021800101da0001c1e00d0101c9406045c80160002003041e01e0103070a03458861512441e004011039071a00350300d04007910604613400000300f886402c00813210040f02180c0207202c5030441070b06190240c00c0a11a108042c071070b000c00100c555206120380d00c440340d07100520703170b15240ca5600c0e01d80c0704002c054001e40310a02d0030810000010300d89500080c2a40d89200007688511500e4816800c6030340b0b01c9802014804c0800c850032900e0518000c2e41c1c0078034520700440d41c551600304042460002e804c101c1a0f001045800b034071090541003d02ca500c61441050919443d007544401101514621000144000c003070300d140d00d01c1e451540c1c10848050b04a200c1d180006070b0b03179458 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 922540764 1250 922539514 922539551
    0x102030c04060912081909170d1101020a0e150910030f05090708100c0c02032e0902030a02280f081e2d03040905062704060b04 56
    0x159040300e100d0004042180603007258803500141640c20a083e014000d68446401a00c910818100700c4211900340288080c0200500700103800030381118000e940301e9201c003a980b003228860840208520301080003180805008a030028402641c8075101924048140040515881c801841050f028000066542c40301c190f0003040c03140d82da402090300c0c0810384617203040340c0c00640005601d030003054081c851081c000038040c80f8110078110010b0b20000100d421540040b44040082d450300407000510103070311083e4401c0e01402d000c0c14081c900002c1002e03206c0e00b11041c84000a406400003d11080503180015260800204070140c032284002000d008080708a0540c0040c5804516488180b04000e03040013115401c0c0b20710414150802d00c036503417103643e880d12184d80300c1e030388402d002c558225000d400400340c000000c00d034200c0380c58648030301000000d8201150014020100c0c1c08048441c5174109245c0d03280c81c89210074202043c0c43d86e445520240c10841021a00103407521a0705011045259 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 922542014 1250 922540764 922540771
    0x1112070b0d0c0f0507051b031f050405060906010608010504020304030e040905070806010f06051b0304081e12040501170a110a120c05120c2203030f09080102130504050414010203 78
    0x1c10020307500102c00c00c041d1a400c0000b60700700800c1024041600003900004074901804022100c0c10b64000074807000902d000c0c20509018610a4021600d581101058100d030380100c1c403c5007034659581d141a00b84c0d5480b1024403c9200040b50300004020034106640110342140c081d14007a80c0d011600e01c0402c0642e03044043c212482da2100400300451803090140b540507102400b000351901d454003100801c0b50051560b0071400101f02200f6000404041040340c00816101c0e00b03441042180384080d00e0740c20340051600d4014020841d100301400c185808413400d0300c20503140c4040310380c1e075000d10080104000300000c10b66541c07454601e48944040000d040d00103c69504c44030034031441c01c00801603901e0101c03140280001031105480384a6030144103a40001402401c68079081c0c1814040d043e100b51207004101001c44185c04030925601114100380c140301ca0310345141303842e40d8015081c00c0f48203010340013000c1c0b4040d000601861605400441d08640203030380040c607802840c2c00c041c3c2240c2c82034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 922543264 1250 922542014 922542037
    0x6090c03200301050a0509030405040b0a030c0e010e01060813140c09010f14092208091c02010201051302010815030f070e070f021c03090206160b010501110304031112070b 75
    0x907000d081c1c007442c0034094541d0003c1e0702c031802d000c80c0c00c1150295940e4016130140310300c90394032000c81c144143c54402100c5c00031600104a81c0c07000756106022030900b03c081c00382030640580c1d0400810150f010383d213007900491851044024604203502c4c2d0800e4401c5406030310010f0b0060b401144160b07a101da024a02070407082c5041000c441c64140e000b405040c280e030400e03004541003420000c5035400c1f00c11950307031450f205941581c8014985030000c0103116143c3c0e19030703004003402c401401016500080c40000351003a0001c018544540180040c00501507900074002840f000001d01c1994603c015180442c001404450b40c4841c0c0c0d069072030404a103a0400400c01d1403410400446551140c449541a0050b00203494040c0030b0707200c1c0c0001d0302c21201c4c0e41c0042c5034035403030303207200315200c02084034201103844c1e03d180d0000410b8036011260040a101d5240046d40500401d18106000710407242220391140941d2a1500410140100510088411002d0340183c9200180928000d4000e05010505 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 922544514 1250 922543264 922543313
    0x9080d110309010b0904050d0810090c1206050d20011205040b040b07050304080403061109060a0f020d2a0201020a02101e090803090f15130306051f0306090c03 70
    0x14880c164216010081344a2140c2003050a000c082180840c1e87d20380d85c042c1d407a0a1255649a25160b412003000358043c800d00e901e011000e11200d0b0b0f00550001d2446410b0006110f201da8640070082c87c0c000050002e08407104001081002072707103c00e0321a450250604040a04d84009003450b011500216029500030039040d0410080150000e89117900c02618203111341581442d031202400d030300650000401c8555100d100d030700001211f0302038400401004002542d44d0040c040c00030304804504925101500c00c3c0313020101618000c882410205110304000030403c40e041403a94600715007030200b039042d401683c000e01c002d41c03a40940b04403903144907100e441000540484d503201007080740c0d004c0420011644418404110084120b2303500c54012a86000f010008200150b8007200c80c0050a0400f100024105804c010060b0500210303400303100100b00139641c01c80da094031268144010081c0b130442c00428800124640e02509215001e60740c00400300751a035035190305822201041e00d101009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 922545764 1250 922544514 922544521
    0x307030b1503030f0a05030603070f1e061407030806190f0807140a060f18140906060f0a0c030c020a03080c0610050306181203010b210c070609080d1103 67
    0x15240900c8030841c4190011898542800d0071003030180141c000c0e68080000001c0410f155580400c01c00d40076101400c03501c4d00203903480030400401ca42207035680f516042c202200080359405404140c01014114403805e140c076055980850702060014240da034803051404140c1461030007402200041e00340c060b2403103046030030030396214034040556101c41204860940964410782b1800700c10700c2100c000342803695415000800c10b4a1081180300300023a90001280000f03200c000000c030100c03001a056810110303030780350841805030b03e1203035a9510300b64480401c142d202403803240501080c8079010b403a2140900d20382c0c0c2d00141e800d501540c0180e5a24001282d007825400e0700303021581e006001a00844081881c280201c0d495032030042c0581019500004001034030035080c800080a01c00305154282e50b582c54561500d00c41c3c02101103201c94800c044121180c81c03541d03004040c0503808070f21043d030038070072680c0d0380102910f44c0407001c413464070052140a590907840d00403552944040780c0702644914 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 922547014 1250 922545764 922545781
    0xa0201020d2408032803090b1015020309090103080307120906020a120b03100c03020904020403140d0c030e0907120e01060326040b071e0507050118180b0f0307030b 72
    0x2000f0380190708140c00401c0382507680b0b040e40300741682e003400203140003203403c420140640040280c05400307440e281001c410815550b00040080080e1851a001d0f80c4043e45a40c004903aa40070b15400a5004a8028014030100d548140135641c800c413245051030098900c000000c0581d51881c03000c8580c50b4000c1120382c003040d0821010f000341203a4600801982d5050300010f540c440b00c1c0440c55031030300d40d58000ba0000754400c0e01121100c2501070406c0d55119603d10340b140c524042203014034140c0c0615480c3d1007225100d140c168030b02a4060350b40c154031405840800283d914081c5c0068140080b01007031100c92105800740100301506d402c00001d401d443c41c1001c0549900c0255003001982804403440d803060aa00140c900352080c841240c0d03143d122514201c010840d42c808464030b40070014507510100000020302105440c0300781c2e1a04052140f40c10340000002d400e02a03460030080411010580307415903071010391340303d4004044080401c0035101003410f080c070541003691002401000c001244 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 922548264 1250 922547014 922547081
    0x903011e0504060513020f040f0612050703150b3d02150108030a0c0f0602040f1211060406140904140c040915030c0509090a05010203130b0a060302030309060a0201020d 74
    0x7803031085141190141503030000d082d81204035107582c23003280d8800711200c3c1c06c00e240d0300030320181010000a814600311800c0990b5100024882100d12a10b440030303580c540c00640c002c01980d00d10181c8070000447c0031000031001000300d4100c200d00307800c0300540c1004841030001140c03800981070300649817501500c0400c5000203016005004258800c0140314001079005034030000340ba820014540c4506803520b4550003a1240303601900424036940804640c892500c01042e5009200f416215080a0b500d03051200e180224460000414046030140141902c89002800311900043c8005051403000d000c1070440340054904000d0204080b03818800090a13208254019048241c1900c0451640e40c0f009100e50b624005c05020317401e1500403c0c04498104240c980840d03102c0000e540306e10300700500d20740c01d070300010341903501c400040041a00d41c0c84502c00c0d1b409880c0c0150195140100120520130140d103d00055411503500f080800350047c010b105d9000342440514000b4003d000080492611 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 922549514 1250 922548264 922548271
    0x6080c18102609100e1f0b010f030b1c0602270a08011b03020a020a050708010b011209122123160206060f1c061407110a080903011e05040605 62
    0x10300540042c04003e94001483c11a01040c4403004903a0310180b005c21810030fa10703001c0c2100c40082c010820904540725800c012070702e50081c3e0300e80450596811003101542c43c409016a005201081d48143e0f0400400303c483d00107029440152070005141b9144070707640c840380c025450480759400352031700520301050b8010013403001200a020491040c540d0391410074204400d481410383c0000c200c44954000d01c40d0b49243c5401c1800d039034001f60b86201ca18060050040c10500103202003c0034078140c82c0ea8413030125001e8000b2900d4031404c8065400b40e42049801c202000090306402003006100405e029001d58803c941926216403400c0f088100c1c40c0c41c4001c0d000701c04603000c0c140c03000400741d40018003070307404041140d208221250020205510498000c0e09215000302001030030188500c0d41c00030302030800794400381c6029541d207800c12240b071004414020229001120032602061001c07000d04202c81c8001e000164030300400000d4502e0383c90000303c10000544440820085c000f691140560 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 922550764 1250 922549514 922549577
    0xf0d1a0f0303041202010c050f0d1815140408390102191a0c2a031e0903010501031a06011d01083111030706080c1810 52
    0x86009104006502e0f40034501403c0022a29282c04134290380c0305039590300310305421078180c640006141c1c0d032035034407098240c80c0e44000c124104c06a0110b05560744010046850301c2d80707400003074800304400319002c003224002c905031298140008280d081c030600c5943c80c0a80c440b0b0440c01556a4220707141c9180d00c8074190f40c044035410300040351b20b50b40c0200785020405030b0443c281d0a6001c031490f1003206141900400c0308190021410003a54141c0300000700108500e44135071400e140071401d1500c0d00b62501d03507070100b141d400c00e118281082440d0b0b80f00d04100c0c5100c0b66001c1c00d1402000209003114070991095070440c500400060810780c0b10081950090401c1c640414580c004140904484650000080c10803401d100007450300c01c46036001454004581450098200c1c0511845444c1805000c05581d4007401042102c0d142c0740010727051b4115130403902c500c1441d660318a070420541d00b2030820400c006c4a90f0302c0c8034485035104a95207164200c6600e4900011455404091400b09090303400b68 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 922552014 1250 922550764 922550779
    0x81c1b0210080a0e07060c050f0a051f0e030307090f2310030902090705040501030606170402010e031006030c090f020702030c10091e06030b03032704020f0d1a 70
    0x10240c1c890341c0e600c0c296405036081c41c5485071904008040202074002aa01039402030403000702e201ca0744000036543d0180174104659440301c00005064031881e02030801881d40d48000d20060500100a101c0121400244000507413480b25035504c1b03056078000c880a2000800e6141c0501c805081110618050441c3c1c2c200b84200303012407020003034045866607401c0e21400691981c400310b05c1c4290400c01915034064010b4000d81082c910242454026014185c0481c0c10a400801e080384901002880442280d1000015481f260015900c0d0511400c0e4541c15004113104080c0148041c054140114495916841c64600e000c40344401c484070302c9606044140104180701c00b503503000500e4410a10103c1e568000e01008490654503041598426a00d190361103070320302030001c6072802000444030f80b910706001019200041644a00ca0500059001c1e10418420000c00483c400780703e10510020308010b00d032450083e818000d036080400c05000c0d00d034036800345900361402c0036075010f12031000751400b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 922553264 1250 922552014 922552067
    0x6020414040542040e0109030816021c0203120f060f040203041101031e0e06040212010e0d050d0f0524040c0507260a050d0b090417030907081c 63
    0x1d00180c02c880d00302c1c1030b40c1400d400341c1c60749050f0000409000004014000c000c1900241d0742140030340807046058001c1048840020420b00441000c2c4400c070f42c559014103203d01026003190b551940d07041c801e034110f10003804500c10b0030186201050240f00d0920080c1460b18000c020000c064510f414194001c900610920002504425081c1040301e82401c2c0132400c0e00b00107009548203112126010b04c0d8600301114a4802000801d019005600039034098100c24000d0a14500380d502d0000e0240382d580c400303411295078070f203d03001911048501d080c000c54a13107494645481030705c5041d164010b01c9a040003100840c00c4410030319102881c1c080c1c0d810700078140400b4026005024a40025200d084009425a045081580036900200e000000741d40c0700c03204220014140e0300100c0d0030721501032070701011400600e46002c1c003d2040d40d2094408400c43d14030385c200b0b4440d40002e404101d051040440108807880e0900004074481418210f1905104401304000c25006110444d6401303041d00310241c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 922554514 1250 922553264 922553311
    0x100b1801030b12010216060e0a05030406051605010c0e01110f0d051305180609070c12050912060115020d0c020d021005041d070f050a020615030a060204140405 70
    0x111409a002401e0009022040c03501007045481e000309851055440000c1549503c0c1c107041440911074050307101003181c80d203440f1440e951401c1c05000030340a41c1c400e1004000d0140b01d40014610b903510091800e05460040d42c403075003952a28500030011611044440006580c80f2003c83d03030b00001c140040003400904042c0d161103554401011080041c00208401181540040c5100508020344444401424102d08034101401650710310305c03c3c5031074000703c2d036014801d000060000ba00440e4a0036410401c4405548544c0440401e03900410907200b964a684020b01a10340200071070f01c018034241032030b844001d06180c11a240d507403d2101c110300c04009a11880c13102040303168150303209104045022805e0f41d8900031503000c544035458049178044280340209000d400b0364407584425644034210b0800742c0c0c060003011000401640614001150910006031070745805801038256000c48000351603c0e416030f40650030113034008080411103003079400c051242d664030884082c030500d90000003502 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 922555764 1250 922554514 922554547
    0x23120c0712050903010608060901020904060602060906060d0c0b120901061d13030504120507050f0a0b090d03051e1e07050a030e040b06180a050909030412140f06100b 73
    0x1c90104110300400c074844075840035448040580b001c074003251218544100001e010b0b51001220ba8081e90420f040010500d00015185001d140030f04003605456440307030180540854100c506031087c0103a40800148400c2110007072030180d0314851124460315000388810700f9a0f04549c00001001002c2c043e4017043c081040c01c1c140c100d01c8040c0c4058400c205401d0032100c5003c0c5400c4200c03184601c030310490401c40300041180803554261085846550b0b0790080299203610b40c8907400704070104002c0e580c07681c600704402c61401c2d44030341403240c240309015003036000c012060054036250a80000d901d070a01e01c6400050341b545050110341c0c5242c184607594481c0c440b6007551000b010301c80131088016440e0380b960014029014054201500e404034040e200256030344140301c090050301403207008501c40c2840c0740100d114161030380007180780c20b00d0310201901c800d1440d0002d0360402418200141030001c2409402d00610020005047d50f061095103607030303500559800501008401c01825098600c07580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 922557014 1250 922555764 922555793
    0x304060909020f0c06100603050a05060d0f061e09060b0405010803090607050a240b01080103030906050702030a02060f0910030b030d0f0c140105070f1103030406050723120c07 77
    0x507840398442c01580601d4010420451300768000c01003000400705a0b01100000c98181d603600b48090f481d6090340504036a02500c155070040d505000602c01b003000b00b000000324901c01c1d6000100c40d00d000c400000d810514000c100d40c000e0f242c03064101881602d000b001c605620031a01000709514008000307649119070300226014120200321941440b006101c0c41e021941c104115403000400400307101680400e21000d900f101c0d03d0705981340400c0d44250103a6060b81d034952540c03600030381000e02c151400c0d08403800882e450310969012000503124040904200d40c940d13518240c452481038100800003070101d10810405143c12000d20342c036500060314907588001030800b01548101c0c21021109003171500c0e405045c416003c0c2e0110b44180d01540490b00c12035040e51100b4101c424403030111880803035041c0000d40da500600200d408500c4030340c4816000a003504140c0c25504024003121000c246180c8240d840210203d0310401c0d40c150040020f602c426102c5201e450001556144d049100421 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 922558264 1250 922557014 922557029
    0x510051804031b050607031b02150103200303160b1e010b0d1b0e0f3f071e090e06040308061216030c060804030207090507052b0e03040609 61
    0x18081501d00180070203400e1981da4012058038442e150001c000b4000e40b00b05914148c40e40c400382c0f20f08541e503102040035640048070340002501a440c3d620381d01c100c04a140e484600100300e03400780a2945d90708000504050520007010200c030b40703242c00d0040310b601004204005001e806070520660b504481103072415150010303561504c030f4443e151207100902c11085e62911864a88240d180030b103802500e540b441c01e80849140240c445c600c814403002ca8002d050080f007003804080e50101c030808020351541c0d10004500c403e0303690300e1004481d601c0c20b406a800451031114141d4036290900e441602c0c68094000e034601032040d840e1200d03486a4840b4000c0001d070820184d00c1c04252141d0307a840c0f103e032070101000101d0780300c04542e901da041211041e210031a8028a0307060001801c0b8011003186200d0768154014061b42440e00302140098000180040d08110081004442842040c04850307422205148150742c3c003415840c1000484910241e000c48603031060204001140c3d00840c12400d44249 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 922559514 1250 922558264 922558277
    0xa03050c070506430602030a1b050a030e01021303020f03070306020d141e06150909040b010618151809051815060d080a051b01051005180403 62
    0x6036031150400ca40c03a00440d030321400c009903020268880b152a0301c4a541e803454801c8405541e81104640d075030700011241050038103d40c1c0714001c29006d6010f10341c458131104e4003050528103040d0706400503200171090000b151012070601c13021030b89441503c04500760b03040210710301208201c400190342d0062100911400440d42c44601d26101403040c10000d5031301541c159198010342200402400038900c030070409141000000d80c0f1070b0550410800e500c40344496403166030300c4003070520444546428a0380c6081000b0444441c0030344a800f1800c2c850303400f54401c60074550500c3d2005125840d40c2c1c0650040c00d80420f01403115030100c00c0410f89030410350801c401c0212114103d80108415540072a6046d45000201300c403807881c1d040c0a845800300c00c4152100d000c0d8010141f100402e090f40c40b50b412003152049000055080002440c03408440d00f04141464109191410581c041c407601e02440e94450082c00f40820404001c0341c00703054100d65800c050500c0c1c5004481e0b030140140b000c2c1c2000310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 922560764 1250 922559514 922559527
    0x30e0a56010f080c131b09050f01020705150f070b0403051b0d0f05161407030501061a070204110d0905010e161a03060a0e090a20010c0201030b0303041e1e080a0305 72
    0x5c166005440000310000d444201c564880300103040c142c0180b041c140078010700d89030158a98030108907002540c0b07000b40450101c2c0c0c140c03c8405582c0d00301000b002c8030f0850401808001c035050701101c07031040b032080d6101560741108000c401c40700d0030031226200b00341d4001c0d020450b03400c0c0c2100c031482d000c0c0107a00d41152194000c146d0601d000420b040060641c01036543c0303081e8052404140d140541f80a000217000383c0eaa107240c42406c41d46082c01c0400c00e943c0a009090052034207401800c030151205ca2814209403100c2d00c510b003240c07035112040710280c1d0750f6080744044a00c14003091104000300280710058174030342801d0f84030201c070a5109403000030317000001036850380d5a00707940b802030310000500303210a152882060317a80b1050140c09482c409440007040c00c42c0c00c0401c211180c0c1c1d800680d501030280c0303100e40c010740c054000e00e207810b607250000b4000400d0100c154822441e0442c0254280041c02e840c01031801501d08100c1440c1c0c1d074001000d0001d011080d0700050450001c1da1601d0700542c1e450303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 922562014 1250 922560764 922560799
    0x90201021e01060f080a060e0f0d051305150a1409362707030c0b1612030b011d0d1401021201090606030e0a56010f080c 53
    0x41c50f0071540031320000d5040822000e80001e213102c202d030b20039036041140040c0c0c4030780c0c150b607102c11125100349039000d080c420030350500c03920160288400d032680c200d44503522080040d4010300304042c00d10b80385c0008500c8003e450351040001c0700f2034491110003480c201e4408003103421078220314588442c8280c500341c1c0408020010741c2e004425003002000c030a80342001548011000300d1080130000c40a448520b008a500012820a003201e501a4015005a2512000d048a9009401d101040320001120710010038184640700d86154216600001e2440750f401c00034202117081c214034250703001e400b0070340c041d40d440c0c1000c0d10355040c0d0801d48001130100b6050499000e0700c144107030108840410000014001e4140d0044010344580d9141444811a1000e44650310300c01088003401131103845000d85000381c5140e0302e1031240c0c0f017038034540c1c0141500400324164040450185980e2845000c80ea80c05d807691182655003d4000c00c41c04460191400f241c043e07132000c01c0d02055200d8a092404c426115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 922563264 1250 922562014 922562021
    0x108161101092f06040e07020309040e0c0a0f1406070807050a0c05010f020109122a12200715120509060406060b0c060a091406010f0315090201021e01 66
    0x240c9500d0001c0c440d08402d46040f400b10080c200c0d080015240e00340240c2d200b400d441d103a40c09115005010345043c03034034241d81125030041c040d08000660000300301952064980c0c0c003032035040410b41c40082003580c5c01001031280b000110b6012540c07001406205000500317600402008000c0c080710030030b482d04c00c5410528801c0c411030100810a11034a90300404000350703ca08e4004480c0e098803024826101840d041c0c4c281d4100c01002070042920307040038800e00b1f01031240003600d07549002405c0501140d841c0400e0042040c54010364a43c00b0008141c00c04903440a004101ca0002042c8800841061741d9150b03a11036142c0140f0b1083c06820a2000c107507449180d03040206044220240300604118008540745d103c00d4906940f0b1070300741403000c5040d0041d08110703401e203070b49540200384682d1101403840041440c210110703810a08000c845810940800c03600303003e040d05000300440c0a02d1890041c3c4c50b4900d54046c3c83c2d116060815110160b0380229a2a207071000242000c0503c0c0904000700707004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 922564514 1250 922563264 922563287
    0x33080c1507050102040b16060b0d1a19140906091f1107060204030311060906070e090405011b120e06010b04031103100c110f0f0618281b05010816 64
    0x110f100104002c7c0710f02d221200d4018400380510800c00034000c6040034010f4000714014060003001c0b010802d0400304032000d160795448144131041c1001624007141050a50389070810780d035604040300050200465051002913006198440200a54440a08032504482e10030100c280c0580d80c1e124929a000008da0449070003d51080c0119500d030340301d01e0060220206000d400d007142c0b02c0c090005140180c0040c0c407030302411450300c03a02c10f0030350060300300000840002c204a4065486404e48a0481100760480701d080c20b040e11050460599100828226110f0104003030007684280d00402410395030b14110f4081e2074000c0e5120810000000c00b00380741225028240e10281d181111030b040c01603104074480e00010348041511321080e039103809280e031003080e8840c09500f07400020118060300c11a420201c0004002010781c2c2d6040c8401c6244110559511003414070511620710140400c07040c41ca8004505031b00c09280c14405003400002002604001c0c420100b00d00c202040c04d8074540a1510781c0d21 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 922565764 1250 922564514 922564529
    0x18030c0b0c0c2e031a04020d0b030307060506150304030e060912060702010c110601030b0106080423070e0a020315190e040c0806010f150309030333080c150705010204 73
    0x150f0825001900d030048407601242d45810160741a424840c0b0f00c0707405051030a040709907045075001c40c860100720003580801c02d0000c1880d954984420191010300c0606400c900071880059030f841d000c0c051201c08800702c0d02800900104104100009410100c03c000a420681e815901c680c10390700800c004040100c4021040d201e03030f05c1000401c2e42c1c15009400b04a82c0c50365605010045ca400c41030b0740306070a01000788900d00c010014001203201e20491036000b800342d51914842e00003040c49808224841c0000c88441d041180300740b2070000d10f010f40c0358110180741811461480d00e080e032060940340010180303100b00701c040c09004001c1004448bc5000d043c0c59080d4500b41d00745480c000722031841500c2105464000c1000002c3c01c4d45401c500d80003252041c0400300c1e001c01c4141e038210020301901c6130407824180e036a4200d988425a4030140c4500340d482416034880f040740c10510650a00407039200001d240c2c00300f000c0c20840e03103814104072018508000802d031146591304e04140640034a8012a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 922567014 1250 922565764 922565779
    0xe10050c1908130f1e111201060f150513030804062a0f020a0b0d020d14010b0a0c05030f0a0216093305030f03120a020a0c020609280618030c0b0c0c 65
    0x2400d2050101d0a8110a94101c9a03a10351f038100040c114242c0301c0900c5070101c4883c189a08000d81d074003000003000802e1302491b1261401840591200c032203d4990030a0b107600d032003c0340600ca103a0300083c40e41e0850304402c40c40004c4950300c142d014a0b20080d190000c102c50340d0109008110344442010780090b064900b40c842c0ca400300c400115009402c00e480c00f030030840c01d0942466480c25140324a9041e2001c458055140c0345250700c00b42e540d520400c000f2100d5100401801041c2c0400101405401d0501d9024110030001c54141c0104002250085120107141000004000740d9500340303441040b00790080c500f9040c0a601004881010680c08a609801110076040d00907034044000c2041d207200076603140960301c070881180100e000e0b055443c00030506882c404005840c0210281002003c003d19a42221080c0341e801c0286540b02183c2542000d16032006228654100140140076814411031410301899074503601803c00c110712980f2140c03400042e214082260070f00c42c203950404040d1100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 922568264 1250 922567014 922567073
    0x120b06150f0a08311b081f0c300507201f0c0302160c1502030a020604080702030309030a20030615060306010c120215071d040e10050c1908130f 63
    0x588a299856280c4002280402202d1f00c14009200b1003107400140e1361030314420380b09099448134014040e01061543d074209495050080c25900450703100d10303459940c01c02d103110361410481500005802908240c0c100101c00101150780e8402031070031088a80c3c0c04039201203103031000e80092203040310080300115207001c007400b03001200440c1d50031218500f0100f40c29902140c0c0c126180c2c0114004880160400404a40840ca41801601b81d99000030103603894800128000fa14104402d50100d0782d00c802c100b4849444a9203032400800745a00354041d0180e441e2400203a40e104030b0450080e403148501001041090f4414040185001c4e840440b21021f05826040650780e0702c08400c0b1070402400c05000074070000d1040c40441066058119038039404030110b42080003801ca4410520207522416040c51800795071406100c1c06481503810595540c0301d0f0f030001901070036800c40d01c2002c0c440103406004885502660341c00c0c40640100c4100b204004501c0c0c00301030100701c3d8000702c00d00701450720174 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 922569514 1250 922568264 922568279
    0x901120b0d1a06030d0c0b011a19020a03031503021804060b090405150105040b031c021213080f0c0607120504030209090d020105010807120b06150f0a08311b 69
    0x30707a003d03007001c6007100c070740103100705040b60503070000039005041c001050010440291034586801e01010045030310360811018403142c1d2030f010600e035680310040e808004117a017415010b200e1a42079403810100c8921031810750b00411001c84c6070310480444040f4001c005814406140d020703602440000302a80086c2c1001c1c10004c0e40c9250303403594088081a41e90000070249014841e00c80803401c00360140109040c811098044203070362040800943c0242c601d545001d0315420001c004106005040890182c100001d862800301e0f00064080c2641c01320740c18800355980c55003070f201101c6d401401001c00c4015898115540d01031607100035000882403040c081041c0b400701d07203140e25590700c8c0d00030005c0d1384e6200d4507075a0b600c0407446440ca03004503404040f4013003500c820b2740a0340b01c2c0f009003040c2c21a0f0510000403146500c0303141e2034000c03c1804112102c8495001c68142e401500b0007800016080b45c0103607400c240c000f400b0b06082c0e807a90a00380342040040d9601803016582a030100c00d0070460751400f2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 922570764 1250 922569514 922569563
    0x607051005190b06031605091f170a020a020303041b08060c040302030c1e0f010311030405060f0a0e120913060b0c10090b280c0e0a050103020901120b0d 67
    0x400b0728106003000306039282e0703062a900f564824100718250030f680390b0042c401911903034004610749401289002c0e000300d00518041103044131011a688240100390100e8503450001d074040c002c00044e5004225a083c1c069002081d01c0e0020340103150b020700315280904510301d501c015800940a40224002c116044584001600c01c4a0080d01960788158003a010485808100340f80345c40640701c203101446030390074180c003c60554401030600240b003e40c0b480080e10140c104460441d02c641c860b00c00c1090611103501c0d02d50700440380c8001445410000e5490076262440309032107184406d07000c140e05280d50b4130344440c0e56603410012400c201164484500c0c0703509500603502c07050350744112184000403084a104c0c0c0e12105410000e901c040d9107880c003035203007a030000c1c004110640c14502c8807807040002c2c9119400d0401c01076158000d03a0007d6031f0601000005603030005061501c14040f5a2090342c001819a8506c6008000052142418400140c030034240305c80203480341c12070810080d80c0c4100c104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 922572014 1250 922570764 922570801
    0x17070e01030c0807120f060803030a09030e01180b25060603020312090d02060c0c100309030207050603090a03080c16050a260d0b010c02040e0d08010806070e0607051005 74
    0x907414019415400010345807010151032034400200c69580c090100302d095031210ba8902801c0780081029655131034400c0c07441e0010389520325600e40d100200000c040e0803034402022580b003030810055420000381c81e0301c00304c00d1a203d24a0f500c91700240c00f20810030140c5158400d0716403018180ca8210140c1002002400140403c901030712899001ca01140038000036600009802094049948160b0742480302c507070400e4940700498851185001c00c543e40c5d880c5050a10245594001501155030074000d14265041d071042d4084c203020018000b80708004203610001a40504045006885441d00d041843c4030361011450940388600041080040126090041600442e5950b480f81c90725030444489030f4002c600000988030030410f040c01420300f0b800020310084e05040000300c0c41e1060700428140c0310b04009681c0c0c01d412004030034441980141d4410b01400b644d100900081c640002e0240c801c600d0981070600ca41400714810b006c00c10108500300185982942c18401800e001403004170701c42040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 922573264 1250 922572014 922572017
    0x4030b1f03123f0e19060c0c0201050910170705181f12020706050f0a1a090604090f14010c08160206160c020d03080603010e03070c0302060a17070e01 66
    0x108005039509440301542c000c0f092941d081ea40503d14800070011400042d4030307800342d206440d8079503440c250506114000140070041125041d1a0580c54458100e81c0c10a0f04074083c40410003118026036070040c113031603108038141d4020718621300b04601036a0110b15451404a0224518101301c24203901c0009040004030400703009042c080304030100804280c103500c0c000e049403080003041803018446c400c40c50550310400401450700900f52615803e80d5030446100c020b1160401c2030001e122101d02c50481002250120314a0a03041c900020701c1046011f45811310464468000c4024040042c0c01500c00c00c2d408410101d65500000c1c02a0207007590b4494040812200d000048003840440408084020103502070007441d44e0b141040c2c070241c24000c0e03c400c02c10039201e0641e801a11164021041903009454621b05403034020109400e482d0001c644070140e401c148485000030740c0750f4005a0075a81d040b6161912078183c00401c4803010103c0c03011201c22710060050190181c0c0110720316401480a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 922574514 1250 922573264 922573277
    0x301330f02070e0f04061d0703030e09070c0c180b0d0605060102010e070305060106050319020c01050f0109060f0504020702180703150603060e13080c01020d24060504030b1f0312 78
    0x303d4128001d004000c40d820310351203040400050003c1c800d64042c0a15448030000c0404090350a1203984c41c20030247c00440c045078114030140c0741c0f4a002d40041d9444401c0c0d00d003004a01b01280c1e1092510340962041848003601050390381c2c41400d25070001509400c001d030081000c2c0c00c0c40e05000e80500415500903015510f8207104008240e80450007009980e0040001d00032a4644041240c00341c0c03006000c0ca90100420940c100303259000d000a140c0140c240b0004125030806102c81000d54006a11517003540303103000700c200700145040d500b110444608460050f25682540040f5580c8441000c2d00b0701903041e4042004139058059100384034080d003013110150700341c0c2c44004c140d00b254828000c0c0c07050b40c80240002058100034500704103800348100c5196041640ba006543e007682c00444005402545425604106040360f000702c81c6c01085030420171a1a51424402a225200c0c41c0405002c0c80061000900a800e200f030820091084002c0001a000c2d81e0b81055070440550b8039014000600303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 922575764 1250 922574514 922574519
    0x60306011a0a0306030b04050d020c030d02192306190203040c121a01060e01030b06070f17040b0a12180b15030a0c120c09020f0301330f0207 62
    0x100060028140c44100d00402032490304055031803019084256890201921804040001910488850700862140005242c620303050b440281c03d1448044440b40240d0000901c0711300d5580c005041c1700c011400035115910024130307040c072454104411a4410051042c101040507414000030513501c5207070001c00c201c50780c054403541d50050740b209850140014050302d406000b07848680101c00003c0e0302c01c5282e0f038140304249294580b00d00d402d9000e800811005c0010303500b0f81d60140500003014604503400c80c68072403203580d1400c21680a0002030000307280e0f581a98142000042210090300c145651151100000500241007220451500300600d0400d164850b6882c01c1c481000c0000364041041c1c11160b40b1140348444e6401c405007501d034507208180344000400e2a16041002078401c1d10884410901075050408413904030341d219180c02841042031100c02e1041c03e084d0381c1982d030a00c0c0c7c0300d481c540041c01c0502c401c552560044c0501d2100c07501103035401c0d4000aa44400c04d55a8080d25002c40e0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 922577014 1250 922575764 922575769
    0x40f021315110304050a0509250509040b01261320040c0e030c09071710060f02070b1608070206120121080d110403140a050111091c02063006 62
    0x61482110b40001440340103114600d40000d0190b800b03000162141270314480154042c1c20102c5c2c080c00d040100d24002a00b862a0500f0b0040c5130010001317013880d80400c04101845d041c0fa5103007081061279403c0740f070041890381d051303a00c0e6401d1035a040740d404101c410030010020001f6840c003092a11451a0140b024001401000807405142c0020b02800d100c00300041030004e0820010103440400603103c0c0c01150030780180002500400d04d0480c400c0105041440141860a031050309805551020a08100121110701100d0141c00c0e001d0365403500007041d141000f841c0c020000000e42c401404a03061140d106c45003181c504070303200348401000020b9403070403807000900f21000203040c40c1c404006055035800641c2141c200e0000281030103107020350300d8030f030101c5102040c094051150400c01e0441d041c407009005c1d954a001c03a19400d5480d1101040c0001c2c044600b0003c000c14030410410010b00355a11501510707801d03010000380c1c1d84407000d541340130f0b5003902031480e110420700d44c05400b060300c60 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 922578264 1250 922577014 922577017
    0x3050a09030c020f240304020a0e040b160528032a030203061306180b030c011d0a080d030207050f010b06030402010c080d0606030e060f0c09040f0213151103 69
    0x3501526081c02051464007400320084d0b4486440e9081150042850707032900320504030f00f0400d04c514540d80e440303050510400a000646a0100803440381e11810b100210345d0000255420050700156640d2090055506496600900119607000d0a0030741d964042083c0640000f0300380b01d0160b608105081101d0b5003420030741e1034042030030130342588002440a410b011754000c43c0c21500090020b0700c1000c60900d030400781d40ba0350b0084038000e00c45a031030391001e50050198031454041240942083d01e900340c0001c0c4000e03010000f00b54540403d011500007030311006c00d4407001c1c0100f401504c1e02e498410744040d02a500c2528221003500c40d0740c01203424070781d042c4515800f07400000c0c4403510b1911107400444408450020581c1d0034441045523560044440c0308a8000708081d45000c1200f90000e03100340d040003130082a0582d0a030614003040b442c0080f040840702c7c42c0c641141e0000c3c034102881503c500a006071141d02c1c038003120b0210046054070a0039101182d00070385c3e64840380411704210400c2c0e100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 922579514 1250 922578264 922578281
    0x110d1b021203070f031d010902090c1c0b0d060606110705121905070b070302011e020c12220e0907060212040b09010e21070b0a0e060c01200a03050a 65
    0x484028000f24a070309103d10060082c5040034035005c50a040c038550410007800300c1165100441e9500d121160460030866911540008011002820a4030400b5104a1031400502c00c1c007001d0382d0b6007140305480c0d50b0b500041c503506400c1141000300545800d00500145c8061482410750305c90101d00185900d86102c54000380d00c101406891516220075048503144940642150503025109001c00c0341c4036000081c00340c01d40070781e0000c00c1150007010340c03d00018401880403022170040011519540002500c100001c081001c1c03540da51801050750b441d04010300c031031910307c8411200300040b82118803458034024001c00d4241c5412030784e41d1100b41d03035454441500d0121000140b00030001c03802030070007a104016040c1885c980c0850201e0024014072000c400020040c00844842e5601460403c000001b030b0460384419446d16030010b10140444610307007a050701c04e07240083d4104000c44290000d543c4588132100754221200c15444404954110542c1c004c000391412000404002c1c9500900e0798 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 922580764 1250 922579514 922579543
    0x20a12020a031202030702090a060504050a0902030607120f0e06090c01020a0c15090306021b100b011202130b0318061501050f0318060a0f1802011b06110d1b02 70
    0x744919580c2c8000041010480d01c5040d400240070305805a1104010706100f03610380200050a0387c2010100f0048400c0502000981c522307012080d001603c00160310b580010060425a0060328180f0090002d020399646420251781403c0003040020310000b00640030308800d00544241c8840070004980c1c1d007100c08806421a80e0b060b0040114400d4040b4000e0703071828514003100b80d161a070325144240c3c0d101e4802110300d10074150a040b2622800c0c0200e004c0261004400d02040c200c04000806034170039044828075041e8005224010100084800002132001e91486522480e1410040c1d050404420702c03c1264042c07000000c00703441203803a54034800c0a050311500d041001e018013030071442e000208803d100c2c482a4403280107401d42003040398030590341008045040011010100285c4a00a134201400c0c000e2586100040c0e0300564001c04500c10141c59509504280c00d001c0090400c0f510010420030740003819840c03d500c1500208200d140401010050105611040b603803107041c2c070050203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 922582014 1250 922580764 922580779
    0xf140f060f0108090309030a140f0d050f0f040807060203070b0c13030602070f0204050c030118060b0301090b0d060501090609050c1812010e03030c031807080703060504030516060504020a1202 84
    0x20966000390f000316048500602240d00302606080030074078000c100d0b04c080e40c1901c0c140e2948800701d1810020043d5001c0e0301006031840c0fa50740580034081c2d005524a0605155004c00c2070312036881981d081c0d600805010046501140d900c1c07c2c003a49984c44400c00340c0d00720700c1e03035000501a050588100c9208c00139804440d807003680b6544402c0300a4201040885024042070341410141e5540d004150003845ca868195959503d0990032800e1110340003814800b040c1820300410170708004034156411100d0a50020035000d541c400000e03041c0101d04401003106180000100e6070407102d91000c2c0c00c5e907800b840e082110741c40320a03080e0f14a004a21140020150001440025080c40481c510b1204000000850030420500030700e82075800072102d0f03d520b0302002c401c01c410700280000d030080a5010038058100a414001c62603140d0080d800302078511234441c0c002c502010301c910100e608041850803903040300381c8a031508402502080d00c060b440307141c94640c042480002020b41c80ca403980e00030140b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 922583264 1250 922582014 922582039
    0x605040501031107050105090d023306121005010503070e09102a030f0609050702060a02030907050a0314070b03060604090b030127210f08190f140f06 66
    0x11000f0b01004591161106800c3c0811000200309004803401aa110006008080c10741c0c1c00081c640080c0d820907080480ba8841c100507a03223058000283c0c2c03c4041e4035092843e035610303008038549201812082071180308030820b079540603459a0056040e80c3c0300710f040d100420780c1c8040080d4010400e540002c03042c0c0201003007140c1ba810640c40a000713501046880c000c207034106900d0036517001c14a140100425200d0324080281c485900c0b07600041c0c405554101314a0400e000d009503180801804d8103d19036002020560600f0200124401000004c1040303103843c3d02c038540040c0c911086260740301c69210f100c0000c20000125415a4413500016003414103161030200e00c14060b22030000d10542556a03000440da1140000e0f081a443e0354500c600d8207880861407800e0400c6408100d080c003a1002d150b02110383c010b80c40051600034440500d046421510fa100c0c010041c4046202c449030414901091418000b919402c036164643d003c5000c441540d961141146110400310303101b65001c102408e40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 922584514 1250 922583264 922583267
    0x7050d12050715020c01150902030106090303080c070501052d160f09120311060901050603030f0d1506180806010302060a0f050f040305071521320609060a0605040501 73
    0x241c050b89000d1201c1c0419200c40c00c01c10002c90b405184d08000da40d446945400d4449080400e80c00100040030085255615290009040150500005040081040104410074443c07010b44c2c000940000c020007403820561a511400300032516081900f0004452000d0041301c04485240300b4207941d080e4411051103000e044035480d02c0402108203200280d0004509030619039a038401d8180700781c491170050800140c58910700b2000904101d00d41c1c1c14041084603a80b030200a03510020305215400f5111942c2c1101d001c0601078403030410802c910701110025a2541c060803403030202d8005075032002c8441c0c6035039100d61900400d000c040c0d08480200300c82940c640c410b0b1a40c4107182158500581001e909441c101d02c0c42c0e1247e8000d95103580064000e00807031101d0484e202c0401d10508100300d20390420191404081180d6614035002541c90b4010880c181c030032003c80c0c000c0e040440d440080001034509171481c000c0b040d00c02a000b100801c00149aa0400c2c40c0710304140c4011b0f07100c09080620700b900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 922585764 1250 922584514 922584517
    0xe040c0e150c0f03090411041401083408061c080d0b1207140418020d02120f0102040e07020a0209010905090c1002030d0f1a13020712020a0507050d1205 67
    0xc1071500160400500940c52802e014103524000740c08051a55645c0d11000c10040d21000c0303480c1c59000c001044200121030780440a08140042802c2030f4485a032000820002840c80000842e1040455204000000740050820030800c000740c6907059251220340074040b2000031300b80860b01000d254031503c400f01c0d03e582c01400810500d044081004d00006000c180c00407040e5800e190395074401c143c2803001d0060000d6640603045e0554003000398084811034940e01124510029008079500f4481c0402d5440e00503800071641307d4102128000845080f00034000c3d0311a2082000c0300c17288a01040c0360b28808103c0c81044d0740c005181880c282d0a20710b1303590050034080c00f58080c52081b40c078007030720310349410484405401240c1c01440c1c07180380c0a9289030540f205854240c0100c0e1a0030328140600c803002c02000001002582c100b51031845030242036000740f04003200078016442910499030400d50024107031581510501c240c615007580c95007404162124250014450412900c070404600d20400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 922587014 1250 922585764 922585789
    0x204060210021803011410150e01050903070306020a050c07090501080d20100f0f060b0f0c0304091b0f170a0b010c1b06091703120402120303160e040c0e 67
    0xe40050800c0e000c03d00003800c4072280d82000010300001001c1000ca4840005158000c02091240801c44152140003c007000f400700d0440d03040c050082011206928204442d0001d9607004404660f103010600b80604550400b00717a201403486041c102080211490040398121a4101c0050542c01a0140241e90f0f0840a008812101611032201d0500c0f0608000b1003980740b40070b074000100d28a920850704247c42c1c440380030144113402c1400810105408400b1203240495020100c0d48400d80000d0080c118403407036101c4d002e660304128512040110280103084041b2860300c80c2c08140798864002c2d190310b030b00b00781a20140f18031540081c56184a90300141e00204051502c845003d181342c0d81c240801503502c10041e2030000d6030101b4898240c1004007000688003a203041030f41540640f880c4ca41d03038810055034910000703c03000407801310b481d048034103010203a1090640341c480c074207487c3c401c0844040b00340301c4001a0800c0b914900d2801e0034411907030301c1591507482071030350f9030300c4d005000c030b411140c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 922588264 1250 922587014 922587037
    0x10060518090c1c09020f0913150e0601230109060804080307170a0c0f0203120c090a030507030818090f0f04031b14370501020403141e01020406021002 66
    0x803c042408481c00c641d0407041600300c0c450014a00c20070f8014018401c0902c100c00d4002d10402c01440100c0b40b4040c00380380c189500c031180c0d00c48044c00c403101d50040c0041106506640c0300d0200003049404004003000b4050030f8014404440c41c0000b40111082002d0344584000304403860301140104448000441d0300680d03d00f1311610b041d0007600301d050031003c00c40d003000c50266140d1621003e141e010130000d1007075401d440218242113500d42c0320702038031001501c01000010002030f0815036496901500d4001c1d0f0b000002c0c1d402d000c1d901d007007074401e607403080c071859101307020340c1c08403001e5498017903c0c160040c5040c0405480c00e54504203040000103003d00280c0074070008105072044404000401c251052003509071004103480e032001d191601c04410786a640341c010f00c040d2101d031036000e2040c00b042d01c0d0038060002540d281a040013402842190005030000c1019000015070880018403410310003c02c0c0f4607403154451901c1c040e400c0b40100e00a0500507041641d04081c200380c150050500103400e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 922589514 1250 922588264 922588267
    0x4030e010207030f060e100b011202070615150f1803020906031e01060302010e0303071208040f020a1d0721021809180f0d171e0a020310060518090c 65
    0x1691940c0844c40f400081c21141e15450780902c2c20b4401c0d05202030719414050003014814a015000003030946130b070016210075040c7d030114640040c015140c00001e48220740d45041c0c1c2c003540c0c40c0c013503010301021a1540d907230100e1101102606024412016030f40004000300c0c200310000e00359401c0103802032020300001d0b40740c810046c80010303a501000d6040041041c1c03200024a0070300e580b00141007c4051740145109030000d01009012441c42e01d0b04c80070b0301c00b1a140c1944955210314118070205041d101c06500a444004d0214012001c508441c0301c40070071b60400d080c03a03601c0b0801102c244600c00c001d0601c5c4140c4100000d81c802103a0042c2c1680020704ca0000a4810704601140c16000101c600c4440e10500c0c4c0c09850312000d040c004640c3d5400307100040c003103c0900041c090100307100e056681980c0c0b600e440000d81c280344403203403296107101d11182031322090030075280c000043d42041c0c89404082c884120001040b5004804459454800140360b0710701046a13020410100c00082999008180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 922590764 1250 922589514 922589519
    0x40302010212010b040f1d0c0705030c12030a05010b07051f020c01020c0a06180b0106080c0f070b18032805040e010f0303080c28030e07080c0310110304030e010207 72
    0x19600b0074064090504c007141c40c0d40c0741100310000b1030502d600c180e450303169185080b514000440036059000c6824450507949d92540d1510b9480c1d4840c182412259003c0d103045da950360300c2010011405a500e0700424481e80e40c8590724500f480c480c000340107040740c0c80280300c1351245d402d00d0100c00596001003070050600301403a001030b09990041c00c411341d850708200300d41c10400c5028403e850000004040302d107034000040c0e0318180e030714070b06000d0a000e00c5180360016000c008060704071030950644420803900d8001a142c10054400183c80203054002040c400011480c8008166170341010020220348400faa000b45a5008054005049080090403c00420042e040561041c02801d1000e0103441007071550500810808001d0b00e00d415a81d420004140d03440d050300d000c50900d410040e903c1842a85010302a40244542c02c1ca984050091100c0019515004200c00c1180700b81075040c4c80001c0000c20550049400800050705040c00c14008140440d125618804000e203041c01141d988a4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 922592014 1250 922590764 922590787
    0xb0c09011205151305010e07030c02030d020313230d1d0d1e03050c120a0e0103050604061e0504150609120c0e0c0703030f0506010203030105060f041205011b0f170403020102 76
    0x840d0002084e070780c80e400104100794a100103140d01482a1504000350502940002c0d2207204496640c609c4903004404652607110100c0b036090401d0713010b80c01c40304218103442d031351034411000c511401c694001d070303c243c9040c1e03400f860311807012561050011014007071100420003090720119060311149030340c20003049c21a601083d203ea1441c001e031101030721103400c05555850b0144400c0f08104d800c400744901e04009400c074008400010742424041013540c1d500021034010f10706640255420f80d03081c5440c0e12124407103100c4100360340381514103000a908900884442c040c0510501d4001844203004119604500c01040e07001841000c401c08215544d030405c07103808405640e4803240c0b00c0c1c0000c800c010107805d442442450180820300380414500440043e440c1d000500c50b682c025070000690180f009030900c1158003400806030b141540004904005000780f85011801080340d000d51051480140140e01003402070b203e40d07503003861090500c199181c6140303024004400703564080c4042005038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 922593264 1250 922592014 922592029
    0xf0210050606031929100c02100f0c060f050a0b010302090d020607080f04090b09090a0c27061203090f120303020d092307060906081524070b0c0901120515 68
    0xa00c0224014124030305c10341e003005108168580c1c12024840880a09401038403080e1555840300014204040d100001040903680c034030715810001c0c8050b18203d0300b0b09000702150300550203201404420000d085a000c015003c0b8850406540c1d030110b0040d003440c005141030300082c90301030f110700d071428145406083d040d00c8903002500315a0405880300400ca2860030305c040100e60080041000b020030500c56103848840e55894000c0c0c2c423407002c844585108403190400f583c1504c0030700e6481041040d03550204150112000300781100040e4002c507001480041d0341c1c1400c000e40b0442d480c4241c2e50251a80c06400079402407000e4000c0e01e4540c50602c01041600c2664405013003d060080c6940030301c12086810300c501da400441c1401380911061241990140e074140d4400040911002c40c60000c80c001402c4041c1c803014000701d4020100352028002200c000750082a10580c001d8203903455148266010b800303804401c0b400079040210f80b80b1400a80e80289070094201014420b0b200590000316110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 922594514 1250 922593264 922593311
    0x31c020a0e0d0b04062d0e16080705040b01030212070804020d0c0924080d05211603060602030702060909060406170d021b090412020316030f02100506060319 69
    0x403402003400f0007017400710900034400300c181c04d1098407040440d0b20b150250038980c41e81c0c1c80480c2c21b60f900d0524003101000c10210401e0240c01c580308001903034075120142d1700d40c440d00503180507600300303850300c540c55000e0300a40b05a4406003810035219070740da40b01200d0865000344140c1c0e01000700e2146401250300d6900c01006032910010100303100102031601129000360078210604e02e448030104002295003c6034081015102d8600350355a0402070410000701d0711511401055800d0340c42c140048441441d070b24000c020501d84040c0010b943d150b20698032170064180181d0046070412403840c503441c149080c3d0340d0129004100056907a12910344612280c90031555804540c0490550841103804000a802120b403910180380c0030200c2c0300201c1c980440140000300801400c080000e01203000f881a2045034164414002441002c1d0a000f070545048111090150145440c1c03101c2e101d003e8043d00744070310b4014200b24516101c3c0800f08034403100301c800d9050714541d070768070700440c08104640c0c000340b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 922595764 1250 922594514 922594523
    0x372016030b0403031d030d1a040e06100902120703050921040513050903041502031603180e060a0b0d060915051005030f07050a030603050316050609031c020a0e0d 71
    0x1442d02d4900541100ea000d00700c910031070341d420500010303500004112075120342010b0010440c3d01895007903031a440e054643d40350b031240c10920071005840000641c544545c1c481c452802c03100b039a50040c00102e20401c060703015216028400160864007a82040d5000f00c2c202c011940f0701c600300c401e034071050240005510000e8200060400c03480c81e00e074600c5180005050010009400c200104a640740326505c510640c080e00f4889116a030350007401500c0048111801425190b0128139000308034100c21070140465100a43c80800c0d0000a5051644220700c0a0f2548001505294007419150030590030990219200c0070041240e04060140c0c902007800680c02c41d020078100700400100000040c201c0c810072905004110002c0d403aa48469000201070408035960a4502801ca01801143c0c00143c032600c070004003407499202c5800b0605130640034400b034844030f40307038040e1040d102d1298160050f0801480c0111404103000da43c02014050241e0520103195203225010030440c80700b10f401030742e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 922597014 1250 922595764 922595783
    0x160606050a0501090602070909080412050106051305041e02040f0c0e0a0801050415050a06051e09010e010f0e09031308150903090d2637201603 63
    0x100504101004001402d82401c3c40d50708a030400c4002551800c0e98400c030000c00c1d4652500300144010344c0101e0f000b41c50b20b04804240c454450a103140600018031a1030701030200c040d10f00818801070301c00c1d90300583d40720700408103010400700d640d0404030b0307258001e0340d0250fa00d140c0c44011513160b200f6074140c44403a4440300d03001c16600702000b401c414194003000280c0d06000404c000502d410380100604030305460001404e84507003c001c1d00500c0b0070340000b0381280c05041480807450100781e0340d004101c1e040b00c0705081c90380c0711240103084410a1003080c0300003942c00d9050103c50350f03000c403265103c5241c0d82201d041011403120191030303001540c081d0003a5000300d10f070011242a0580303035a5102035200b000310302d004400008140400d5461030094078840802003510760201c220154400d1116816007929155a0300c000308028064407145510003001f07400080010305824004225920102500d8400e103460048408124243c0c100200c8603503400381e0310390002404028601c0300301842c0030301c0d0032a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 922598264 1250 922597014 922597019
    0x50a11031801230f0a09091806150f0b1c1b0807020102040e1506090306040602180904170702211506010206061e06070206220614041406160606 63
    0x500050002c00d4800e42000703e0002101c5110300c1c4400311403030580441c40d4140e991406031030480382d901c42500244200740c2404d43c0041a03244110480d020540200400c015018116034001c5100707a087c0f10b4004081c0c2c2c01c040c1001a042c0030009401c03000d900d0404801056411140306003211744a2415411221840450b65081a4040312450740007031940000c619050801182c0c3e041844001d146a80c4840c0325900090b0b95101c040560f000c0800203412207205080510700310020b90413518807103549a01d80c5075400700c54a04446040e004a4011040e024404410f03a000403d40d03001c2141a030f0814080003010f21183c10a02c100d10403a84148041d0100301c0580110f034a1480340a0016811580880180000b5603692100b80240100b0502c08002039202000890454015004060b5000340082855400700c90040b140456407070580b4645100e00392240d5081e1600080c002c0040e0480c1400c1c40f051110940d100003120010200400660030700740e2003003995205a203560350440f0000d8942d02d08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 922599514 1250 922598264 922598267
    0x1103040e151008010506030709030b131101030605010804020405270606030115240212040b040e010503161701060510171513051b040e0919080703050a11031801 70
    0x9030220310340102d400304034989210400420070798060080c0c501c01d41c400004950042d020b07100e90002154040e0504015242034070000320301700c01c425026501420644008a4158800e10a1070186d620584483c01aa1100c0d002d0000400e0010409d420850301d000340c020000c07086452520310360031610b00400c0c0b1840c0ca80d06040c207603207000000c0003030100b01d507030240142100d420454504000c504010b8902c2d0400b14022460b19851132020a50540d00060106140e02403000400a846c2110b404403020f0360389d002416900d04010071a407042504c0c45505100c26201d2114030042d0076400000816042c0e01c960008400c4440706945c5000f040b46802c0c0b861090070599035556001011914602a00d054900443c2c00d200140000d0784a403603440c00095894141482c2c0013070398a045141840c0c660741c48000380320103940160b0f150825403041184151440041d16401b01700e80354030102d001e0403e0340595054800d0303005400e40070103000d81022120383c01d02c020405000015020b1310b040b200c04105a00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 922600764 1250 922599514 922599541
    0x90304030c080312070806310e063309181911060904140403030e060906061011100e011a06090a050d020619200c0907030b011103040e 59
    0xb91007030341090000b00c0340f0b030f40016a4164440001e04041c0003907640c81e80040c44403000c0c4040160f650000c5c607000c41070f0f20442c403030f001c0102010b59400c0001380c0c800204242d0b11403045917214006680c0413507048807603515055180341a081e0110034400199100c0014411410403a464000940400107079100504100400381201401c0d500c100071044890700c5520706010602d86013030180c3d80000700081162035a5000c0e80e12004480652540f900317181c90010041c2c800d10100b00d0313480c40f4000110701007900110b861030080702c0c001c00001101c100110103503940c180d0040194940c0c0110b5204200c40351446c061440b02000314400081c80c10341e2000000d07029080c458400303015100c140540d49d025118884404281ca20451303c1d180390411a01c0003c00c28030516210510b00c514001510300c5032500a00310f45030580c03c80440c000c1885c141c0c1c6100d035503030b0904500250712424000c04211007074003d52001070b45d0b10301171500d01031144080c15918074540c447d40c031007425a0200030421400400421 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 922602014 1250 922600764 922600769
    0xe06071205091e1603050d1e0e090403110a050d0912110d0f3804021e0301020f0c1c080f010311190905040b0619170c09090304030c 58
    0x940c100800d007041000d00380e40d1503020040a03a100200c07075461148030010046010550761024540103065140e2425540726891082c1d44004100f40031311800701081d807002c1d0408a4202c90f5220350710815021704111039120007500075810711050030000e0240840a06c80d044d4042d00800080c1004001da800c0180f41c204268808200b41241001d1040002c18030001400c0740c04080740c3e1030046401504064400720200325009214801c2c406d400c0030580704600000b9070211141014942c280000e140c00c1c18244400c0340c00941c400c0d44007203000a4a07580b410203040e0319002400040c10108280f01601c81740c2d10049503546168010142c043d54030580d40e443d505000140d1a00c100941058411003d8044060100518440c55070600005a0300c07207105020304202ca4504407582c2039903039807910000700000e440540b002900c0c24001101810000500c0301c8810101c582d0104d41c1e4645100c004010361111484003013406a050400101d5a800540380d00450481c4003841c4d1721440d624001c074801d0303d1507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 922603264 1250 922602014 922602047
    0x80d030906231b0301051c0c090204030c080706030603030e092517131e060906060b0306030606030c010f1b0f030f0216080a060b041407020616170705130305010e0607 73
    0x8000502440d03c0308071f941301d10039200b589041605080d503d40001d6487c03164001c0581d051000c00d0010a1201e0164510212071508007541c1a260b20b0b40da0441c20f0750110f002c00b0300882c100071026402c81c105240415409a155074628550082d400e1040314410207c109520002c1c1e244030706401c2100402d0041034103c00000b5078064444515519141c4500340074040407000741d14201c00c0d0b400d100458000c4006168412004c000e03c64469031a80d865810644241d8024412100041c41d6403e0000320071251200c1610386102c1e48404010455501c0300940080c0e41a141d50101400002c0d00f03084508003041c441d4032145101041140000e1400401283c904911581a0f904102d05000420011a5580c2011001c40c6020300b003c045805020528000c2841c02410002c200b6500c0d0f012840f980610781c0074003610102404c04d0000c96000341074401a003049090500441e40c80780c080d6009000c007802015100240640c1c903100e580c00c4400500d5030104980021080045d0958022005040e0143c1e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 922604514 1250 922603264 922603267
    0x3031c3b070311090408040e0405010609180b18030d0213090b0118140114070b0405010507030e0303010b07030e1903030e0111100b030309120a020a0e01080d030906231b 74
    0x441c0c40f00c40c0c1020721035003010f00a495031804241846007180407100036200405040240781000d1803c01c0c024012803040301103d81c54010300100d000081c0e01ca4090090304446408030765103550003180c4200c1c5126902000c1440704000b185040725081c00070300151b9a90943e403201813468000c2e40002e860503c003643e8100000340764041180c44440e070045007941c692404200324100345ca0016101c105c0072820206d900302d0040349000400c00c0d00350b0894880c500c10002403101e500d5401050303050b101c1e641c0c003455168100b0b01c0180242d200002c060508540a0301d04005202c0742407011840a540a5038000c280400f105018000d05412080d1003017081c0c8286801c2c0388110f03d400e01c82e80c8810044410000581c2c451541200075031f8100b0036684507080007001c64400240b015000380da24100e41c1012409090324010002c1c840745881c0c00039048950601c0a0304045900c90803c40052001e20750441c0d10315620903d041d207890702e01c180d00c0c21054020040182d01e0034a250302c55030108410440204e4030340f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 922605764 1250 922604514 922604519
    0x50a0503100c170a0e0d0203030c18040f0e0604054c0e0d03060807030809091b070c0612090221071703090a0b0903031c3b07 55
    0x300080c0350700c41c00644490006003010050300454440e41280d214600703410a110a000180d0215400740c4c000007050811103550500c0c04d1400d03030322804210b900805c98042880700c00c0e1026403400041c08900c02c010800130322501da10710528111a001c40d01d000080e409402008100b01c41009104401c00c4010340c240702c4080300700e035030300e2200e240d40005003040e1140c8031800101d200b4600b8449100503520100340300d11001104059660001d00009400103820041c0010b079800380441c2c0501560780012003649800040002c0c000c401c4030150103402001441c0800d50f40e07102c00c400c0a8030a00b0310075400c15800c07915000c001814146000300e010345071460300c3c96040c01a650404034002030000000881c44882c03507052203e050042c180c0c800002000d05607074050103020044010314003904115108058603440701d15100290180d0240380750940d0042140d05c0103840b192140d02035221016034007142001086219002584011708091000c0102d0108032001820201c00d052001078a2002050040e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 922607014 1250 922605764 922605769
    0x20307020a031202011803080a1404150b06161a07110d20010f090209160905150f0a0c0c05030309180c070507030c061e121a0a031b050a05 61
    0x15010700c0002d11074203040d083d41c48868001e401c005640040d807000401144085d0a0240902c50203d410100075442c1100280048040c90045030045811440003640a21402d9240c002401103d1039150f011900380102400301c1c80031418402c01074442c802c08001c20301074001c0c001c0341c800b02600c10414003404143c0c1c1750b84241c00103502403501050349801d04030307102c1151407034100c98400b16900c0d0095080842c0791903000429088280002c0c400d03100c0c01709a03940c08120620b0366898102c641c0001304410401c01080c9400103800503caa43d0700140f13440c010720740d010800e035540128102c40105441c00481014447c200030500001c08058000e1440d1801e80000650f911003500c48290071044401d01040c604c81c55041500d00840c0d001084503440c9889080210f00a105485000c000a030b400c1840c240c01c401070315900d01c1d19030705901d94441c07500341594031307101520302d074002c41d038810f6001d0301101415030710203200c100107502400103400820608c0e0300b0380140790715176003220f07000b440e000b00200003e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 922608264 1250 922607014 922607029
    0xb0c0a0507030f050f270607150e0309091602010c0201020405032a0303160b0718030b09010e03040906180c080f0a140705030f13020102100f0f0903050a0f02030702 72
    0x200e40c90f1516403c01c83c07480b0401d446a025081d1251a80c03803010881ca00a003003901da1481030310003d14560501d0104990400182d449200c03c000d000ca1940140d43c40c4442180d04140320308600502601c1c00d0807031610100b449140c0480b03025008504a489003804190288031b41c1108002030320096107442e003000003003a43d403642c852a00001d5560340180300290700007001d88020441008080e248c2d10070700140100a003901140c020303107038034482c1004035060901a8500f58020102428000c0104e86107454400c00410001c14042855480306d030224403008041c00100060200c480780019a0790a00b90811400c5d89021030011490b4602001c1e440004d4003c945103070301c42840d010844c01951040c054401503c141c028104040200c61705000049400a01541c40765200c0205144980e44021a4600b10b1200880180c05600320001401503443c0c990895074407408034580c081041c4040480d01011600c11507000e400060003c04c24840c0540d002400c0d6034030030014402141070000b5a0000b0303051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 922609514 1250 922608264 922608277
    0x306012301050c0d03020306090c07020d030302090301090203060403091d0c0405090712050f0604291c02031606030e34030b07120501090e0318150d06030b0c0a05 71
    0x1194920035000390a07071142c021101034860401c140d50301918183c001402030340013944e90a10626140d000180107031a40c8044c0c540d810303001448000380001c02d403801e1300294043c001058040d52540c0419001d41c85c20860203010740e1180d6202ca410b80d20f080c40010404800f00518a075480108040c000383c0aa01800d817001e841003220410929107545500f0303030301113512a14140607182003008100031680c0c80306206103c2c0e04240d43c10310089043c0c0076610b0401c0d070b40020703218207090702080d10000d500780120004021050290545924080341d00040e00d012820030405c40d0300100e1040922519505006154102200000802c181d2440d200100a04032075201c3c034030340c010040341c002504c4542c0b00125070300540e00100c0c601401c0c28260b20080c00b2055004075565a10305250000803602071910818140c45042e90280d03042452001d181c0c2d6502010303960081d80110203417030000c1014484001800500c00da1003002901e0b614510b803806034080c0c010800b10072104c09016014031103401000301d420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 922610764 1250 922609514 922609559
    0x6090a110f060408071d070f020d0e0f0d0506010816030c1502100c030b030705030f0c0d021917061e0a09061e1e0b180a0e150411030601 60
    0x810800e20004a0100d0095501840d42445800c00004e141d00041c00c6d4284100d4140d01c45c40780c656210142a01c00c141180d0303020740103030300201145001d9441546140c0940d0801400d11071010078060000701e10000c5003500343c2c0c031078101e0f40040081c0380781080030402100b010b150007038005185813203003c1500c090b8454520030301e05040907541c0700b070300c00c0c002114408079240301081043d00e102002802001c01a4089000344540400480c540ca00002c1d884440c101321001440041c5d489414064100c40c0094201c0c0c0104882040120020f100180c80000e800f040b03141440d04020381071800e25120010b44140740599000e0224040d00115200003540f00c880c102c00854494503600d008001441d42240e001d840c3d0340403024483c41810300c0c1c1c001d9180e0000c1c40010200005c00071000000311022201c4c0c4561100621b14011000c60b0300b0703442142e0012001d80005a02d60901c81118240f60b41095036a0310b020648082000700a02a0000d230503410007900100004e60429042206c10210b002160b80e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 922612014 1250 922610764 922610779
    0x1403090c220f0b3015010e0901060f15020c100503220b0103030305073e0615010f110313090c050909073905010506012102130b13050306090a11 63
    0x1426044c0042d501d403980c9040403208214846020207054290a00818502c0d020450201c0c0d00074805019003016510920310a118aa15042100c0c042001c5440c0381c10030f6020301c0142d40f40036078481101080c4ac003915158039660f49040030191280050000d048900a5081c009200c01b084c514032049040d264182400503450300d0360b400646092460340000c0007840540c3c4000387c160b03c980840c94217034440d00d860041c42c1801d8071188503242d14040307911513003281002d8a0319881c0c2d88a145c024096400c141020100c1d44c405401c1c80307055900c0052407030304080030603500b0001c0900d81c1c0b180000b0320085180c0b16040100700000108500c50107031100c41088188070362080c0303903d01044100d40d101ca100300d0018a659920015080780880d007542900c1d0395190000003040d80d4002d1403100c80048000020080c2a8a01d41d1418025005600030349407803070441c5008580031040100401000c038000070f01214003844c040403d4509603000300004016042521001c00184c5005440c2c0c1a0400032200b44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 922613264 1250 922612014 922612069
    0x10915080a0f09030e01081e131a0a2004060509010c060e071403100e0604030507031709011e0b0f0418060c09060318031403090c220f0b 60
    0x180080e1986020491100340fa1030341150803d500018940301400080e2503001c030035590030601d46600e007424010582d0941c8041d00242010203072200c00488e0503c03e542c00c110f005c030281039541074008221458854a076841132443d02c07040c868078104e40c1000580d1241440d00342002001441401200c00a5044c0b10803401924100103084e0000300310a002403003203650b041d5441810b07030340c070385042c8110900a00480e456030341500d581d8003407190285801c00080280703403120b80c4c04845640c4002c0c02901008914510600c0a00c0744400b028051000800045940c02c66244d400c2e200c030103000c01428409281612400081d2a046110440c80358101d0340001c8035144800135900503800440000c01680c0385c102e0030a0800e0308984046c040c0ea0180d07504109220354114001c1c03400341e0003500075010035810748486d682801404011175010301d490342035800c10700485010441e0848082d404054403031440341451060a014840c603603400d001e0788802d210004580d80400d0020b4011030003801010008100d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 922614514 1250 922613264 922613281
    0x1a0f0a1b17070c05030105010f1e0806040809040e060702100f0902041d2404060507020a02031203160507081902071703070b0a02070c1e09150f0501091508 68
    0x15840140c01c00452201052030348550310150b4003084048807904002d90001c1858181485000e0507504000005a82c803400c000b01c0d4034140540d06140560143c44401c00b10306180b062010902a80c842c1c00c005441e46801c0c01000162507941450015540c015820000d20301e0740003c504a151007108400194040800e200d5405442c0444004e03400c41d0030003d01e0400302c00d004560942c00f00c05a41500c428412070140c0d040024004807071501031108160129000c1101680b0403904103803a0b004403601240b06502203801e015810300c8990000714040b04210480ca41681c403021403140c5460040e10700f201d150307900350407805650040c01c074a403042c694050b140390080201c500a4042c849003141002c004000ca10350380c0c0d016070000c4410900c501e0108030840c0341402500c1100d50b2048000807248d003400703400109080481258502071550020016800302c00388140c41c2d21091140030000024142403603031200c03074900e502203410404813000800400078242200f14100384a0314003102d00d038a940d5039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 922615764 1250 922614514 922614557
    0xc1507050d1e1401060f1805120109030306140616050c060309030a0311030105090609040203030f0c0a02040b030625120f0209150c071217040f1a0f0a 66
    0x2000c0782801d00d0304100300c1d803080d404801500108952002030150304000004128426000c1c030440003c035001e050500a01e5000b00600440c03000c81d5003010880d6540d600000c0d80440d200b041426090355510315080a1540c14080c1c03201402062840703115000860010071580d2140a8903103000d08260300394001000720a2100b0040448014482c680341c1c14600c020a44a5020300c1201011902c0e00f000c4550098418003528100e13007001784009010b81c1c40c1000c6c00405d0034010700c00c0740c2c1400200004142d000040010344403d040500042201c00c850344103200480c3c1d035541d502c0d0b21a41c46081002000b600e8a410504c0b9030605000c2a0022458002c0c19a4000307181900e02d4402800d2911140c041165a03000c0c0110b0042180d10300e0000761420059040d501c1009003601e100e030000e010030b000101408420040c0284110a40e07020f000103c040c50809030819044641c0414420740100f001a007048039820303102280026480c90040344214681080c0b080c95101c2007480092490f40051615011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 922617014 1250 922615764 922615777
    0x20114160813150801150306080304061709010e03220803030f150406060203190507080301090518030c07052107141002070b0915070507060c15020c150705 68
    0x503038848030000395141901840d0040e50254048040658000405428040c2141d510103001c0d100d8070f8441c1d007030884c0d0b0032019106081c1c00c41030580340c1c1c3c0001194082003000300020012641d030851142145100c0b0b0b88298400742010035903030304081c1e59010380c04d404001c0301d1080d08400e44000786103040004c4a50b2481c0c560780a511240004000c000420642120443c413b03203202c085003031141282d208010407134a4501074840180e100b8424850f030209004800040841141021811b114465965580550090b001000359a4a038401d0182c6407101c040321189540c010000745060248104078260781e03410714458070384200b00140c1d110710801c2d401c20b14068038900110940784c1031a200c0605c08002802d27500c0540c05002c8151192420300d00c0400c413002039401c01210f05d03250801c4c2004001c1c0324021514500c059403400c01800f00014000c110171b0009104903191007a070382000f03051041e0f071407101c05151218540104101010380c000401c0b000c1a48004d240002130303503221000215054001d14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 922618264 1250 922617014 922617037
    0x604060e1f02010f0b04052a09062101080607140d1404121103070302063715091406120309131b030c02190f0c030f0209060906030a020114 61
    0x1188001c0d203190341904011141001c04a082c4031002c2000140811035008035021400a00400103c0f483c55111a91503418100341c4600c0c80c1c14841c804001a90b2940f10503140d00140c4111820620348448900c400c07401400c520b0050107071460b1544010300f100a501c40c81035201e800025050a410400340c4c40001c0e00040010070400c14a001d01e48840411450707020880030540281c00e1010003a000421070b80c81c25819405030040e601c13a01c2c2807000020310540455220780d00142081203810780703510449000c0d6a40e20700030421541d082c0030140e44a0f5039411100807075041c5030f464488007030f1401c2d0050f0412002d03212003007600188a201c0e8114001c0300346259000c0c100d0780310301079145d905e42c110840c1c0301070a1140480206041105030100c5100703006500258005589440c80354040b14640f8507910f000e200d50482c1407030250740340d590001d6903130801c851645901c2c61820a40c2080c140090b4400e1041d1203035500c034106a00000d82d030b600c3e10000241086407085030f0401142e07c500c00c1e502288441c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 922619514 1250 922618264 922618309
    0x9070b09330f0d0e01020406050d05040c05060f0a03050f01030f0f020103150b040303090b07030e22110d0506120709230703060626181510050111010501050604060e 72
    0xb044008a42e030107007022003a07440c00d200d2054036104040c803c4900321015910380c54039082203800c004024010080081c1d2325003640035400215510780a0050401e164105c1c1d0080c2d07202002c0c40064219000503100380203a009000c0103000158081d030040e000c582c2c01c0001c0901d444090310049002d130102840c180d10f952206c010014071003030b8000240058921907103a40d0b101540340c201a90307041c0249800540022418003000303c00f82409801000022010b000c1c0600c8171007020f801781e0a403076142c03841c03c0d8440c80c0081c1070400c00c1c0c2ca074401c581e007040007180c982c80c4e420040709400f6543c07107660240014803a604c1c880d000c24540da10306c0c0c280c000e41400f4085a190f1405483c054014801840340b88003184000c0c01c450040b07203444221803d0100015440307181c80c0ca40c00035050b800364503000c1c9001c0c2031280400008003044056440b92080c0c40c00340c05c800074542000300041620b10b10001014581e814400180426518101134800361146490400d80c0f1000c1c94000800001c1c0413200e0700400051b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 922620764 1250 922619514 922619527
    0xb0a09060e0142030c0e0a05060f07080c0a030305070c0b04110102010906060e04020906010c08030708040807050307050a0510020708040e060409020604090c170105010e12071d09070b0933 82
    0xb400f4042038800c5016450400948403107420580304502c01e00e102e981e1002c07581c8014000761400401034403052035070364000c90034114599240b440030b0b40260307000e5045034000391596040550500a42e41d10503810b03e021481c070b0a040e62288812500500020300a03860b24542c43c0e0141d1007544001c07a10768108009000d11a583c591480c050321050310260301515810000600650290980c154038681c40b0941c80d165507a5524101c44900d0050000c55192000300848404641c080015180d1180564081c010032071030b038600306282265440c41820018014059540891202c0054800712440445e00501654a650000d801016031030300095100c00301142c041042c410320340c00b40c034182500303840301020301c4e21107010206001002d105040c00a00c0e52428a411814490300e40c48004003648101c410058445044508441c1c44800d905051641c110400c801780303100b0400032000b0221580c01c03905d0200c50002080c4000442c0ca003e08000d9210f4000308a414914000300e0070742c02c1c0414980d900c591 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 922622014 1250 922620764 922620869
    0x501030e1528140f01120f0201090b0301030b06040e1605010c0807050a0308070305060301020f07081305211932030406030204241209080c010f0b0a09060e01 69
    0x11140d0b01d00030743c0c11210310000315001169845141600c6074a1480e28201010381d40d04480a03400a104a04200401e200041d41e40c03040340240d8041e500c105801c002514210003840200c441056901c11281d0000b844000b0308140640b2040c00d490003841c0c00311200210342070400d044e02c80c143c2e0051051181008500a00d940840e0050069803d65002d00494a03820109402e034011102003e428443c03c000c1000050224801031250f0b01214084941240e5a840020030a83d0341c02d10141300c9009810030f00c5280c16083c00040c4440c1d824040428a12005498045810070101e160807c1140c07520340117031800d9032080c02d01c010780341020100c960716615903000402940062013110b024410140000818400400d40c4a03070010160765885502c9130144881d10103403800100660700c4810810981d00f800c407082c0200b08640054000c0441d84803040011f1064000c0c0c1940000c071017600c0c040043c85040113982c0d4403030445509a004084034030714820400440b0b00d0a142a5030403003500007a400b40d28 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 922623264 1250 922622014 922622021
    0x1807180c0f170a050a15080f15011a030711010c2a12030c090308120708061002061609080d09080609011515020f0307030c06060501030e1528 62
    0x8690315038945141c0c5104410035558450040c0e4041000007100e0006128a07601c2d902040d44444492008101c1010583d002a091030080c0c0010001d034008041c1049910003c0088900c100c150383c81e561030350361400e0000081141030309089141c0400c0000814100d51040c0d805490404c0c068000700030103078000130080c14101450710001000d14a0900070f202e411300c50154100c0d01500407618a21415208904800403c0058003400502c0410007010010541c11000380c449902041d20740402c5050403000a8403400b001090301e07104901d01c2005890b050380c00300d20541c11a05210309a1044100514261540c1040b500410700758440c10740e40580207540700c60440704640204094134071a0f10780c0f80143c4d0a07101d05400642c0160010503007003140301e11650041c000b6030359602c19139115085024225040d40d201100503030018154030841424403105100b1180109005d007403c0051808410001e034036844074626080d20005400c0000702c200c0c0a42c611512061624070481c0c2100c901d11102c00c008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 922624514 1250 922623264 922623281
    0x20f0a14090f090a240603050705040b0a080d2d05031803040833070818150408160209090a051b0a0e07090b030709180c08180718 57
    0x1c0c1e4044010030030b81c00d2071555043c080d05809014040020140d142d140401480c0d07807034080e81485900305504200b01e00e01c5908003640c0300b00054480c0514000c02c110960b2544007003503100d04031a4000b0015400c0c0040c0348801e410aa007000b4001006800802d03d451009628030038030080c00130400c51542c0d522000131803042101004500710f01e107008011642d03c0c080d901072001349070320121014010aaa1004071011070000140b6001c00852541200240030815038000c40400c3da00d1017403040c40c801c43d8075000c40c075182d010020500409907880c0040110009000a01050400522100a51304400d04d4114240d000f4004403202e06007000000c5d075814000c5010f6415001c3d11001800300d81f40c5922200d0803680c0101241c0800742005076000319204042d0802c03003800f0b001800040d526140c01d014603c11045030b220141482e2815131000000460340c032001240c5881c2c07160140c0c0c0c141d040080c8035004500e4056121000e031109540900c0c0a046820006001c001e001074100d02d0105904203065 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 922625764 1250 922624514 922624519
    0x1112010608150604090e100f20030c04090207021c030f09090e030f0c0a06060618270b0301020f03010b07140f060601121b020106090b030c060706020304020f0a14 71
    0x20b0707072400e0001c02d0700c907500710300340c0e5012004000400108030303550840f42d00c0002d0613003554005404a910802107801407120134090545810480001141c440c07801254004445215803039450159032a1040388680d01034440030540c0400c1c19015512000040740300d0301c48591884404d001e50742000b905180c40e004070031000410590000c00c2d060b10f540150b860041e000360095042140c400300164140d0071400c5040c1551142c04410b1011821b0b6010701d074000d01e8641c44503410703e000110040e0100c4084d0704002c0c0490b0b80740d40f201c5c251031120301404010f4881654005210151540003030701910510307406205020b404030000c9003c0c0c40034002000c06034483c80b40c0d1681203c410200380d44500614802c002a608080e00042455001e9595006101c206150009105a030400c125028280e4640e460005030365521b814407a10040d0b118510503008114000c01c041a800000503645100e042d50003401c1507000302c0032600f19180c11005110000c0024400901145c0798094440518100f801151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 922627014 1250 922625764 922625777
    0x7060c1e02010212150d020315070e100206060d03050c100e0d020606062d04030809040e070515070521070b0601030902011d0a092c0303010f1811120106 67
    0x80d400d005200b10760080300e12008001c043d94a403e10384020b14502808641c0042e5020032900c010303034042c40144200f128440102d1003030b0502c40340040191820340c07010341c0514030460410405540001c0c903c0d0f441030b0111a00d080311306251034215001e004841c801e100c03038800e0385010380f0028400d03002948418030034422102c0800d040c82040382d5400381581d440e60020010000c01510021000b1200034901079031075000680c4c44503240004466005a0003541e2030000420303112030f01e01d414000e565144040074010106541000d00051005410803010020390500060314420408248040010004081308421440c1e11003a8075034165804008115200550341c4006502507010344105020b964041e1740e0b2800c09080ca00009a201c000580b1007a44290042c0c1c0000720a045801303a03492502914400b40903106a81d080c9911515a040000e45290001d0006210800707880105104480c80791480d90718840001e140b41c4001e1040301c801203041003000546000100d21010480c0c125a07141d980c41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 922628264 1250 922627014 922627067
    0x20f04050c0301051003060510081807030c06050c100603050a0506070318200a0635060603100b04080d09140f040c2021070506040201031107060c 64
    0x1204482084034404900390090005100c00d04051a00d52048555402c000581a407240d00007400404540969030018080f070041007038020f0000d03551041d403000b1100409a190440e6039031000b990343c03030042400300080170540c075080030020040c15090346220742d001c03c2110380300e0400300d403144050070054916102e003c0c003281005210703104400d00754100110205d004c400940d140085c01402d0072140300301e00703041c090b80c0c001c0360789507040701e801042d09840d00580040c2203008450b01680041c0c002c1c819080c5a50b034001e2012814520642c045000c5901e60796035550710000540200403a001494030210201d40490040d4000032007013074844503911801c00700c0341c3d100e070900603010a00e60299004400740582b180c4c02d0909811118881d0603d0a001d010400301c00d002503158015001c020089900081c900c000c10106490745003d100369082546142602c2c9460f2103a59032030180c00241019542c2940380481482d207400e860001c2d6010700f0a2290300183ea900901841e44014034210242c0c071010708 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 922629514 1250 922628264 922628269
    0x912150603070e070c0602072003100e06042d0f0201020610120b0421021506030a0c0e0403020102090612090c09090d030e0f0d0801081b091602100509010603020f 71
    0x2e0708545140204004503074446800302c0c3c003407217102d10850710326409001c4100052200d042c1e0000120640205140300050b900801d0300d44210f10110380e10042c54955041c841c1d14020419030760040d08000d0b48580007401c207a20030400e0000c2032800d141018110744e03103403c004c111f2440200c414000d0f07003154075603190254001c004202c648101405103046000b16000500022150303940301b0f00500c5c00c441c11000100010821403029658080141c00101d000710784c0d007209001303058100405500901e0420034581d508418142079018000e038001c90200041d0030103100350103c1c0c0c620000038002c1c5454000ea101b01300a0400c0c180e400011a0040d500c00312113600301491800d2040c10440d000b8403e051903d0b0301580141010000c400c2c540c06410052081610204080400e40d000c640d00d01003550324102160f400c02100d0000d04c0c10801820b041d06d040c0b6a02c1260f0740d5002032600841030b00300c404215050785010401c2d00d1000c2d4841c01c01d010817054030170662100041b24000c1e05e089840ba41a6000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 922630764 1250 922629514 922629523
    0x1005190f0b09011d01032a020111030903040b18042c01091104020d0e070303050c2506081e1f0b27032b0e030c0108011a0912150603 58
    0x7680d400121504e11350075100e0010310000340c1e4200d040c1400503140502d10764050b0050f0714011010590800310100041d09503091191060005c1031100860540c10a203091f5522881688940020340c440803600100010031005041d294440040042210a011242400e142c181103000c1051280d1107030078801c0034100602502c280c5a511003c680c003400c1401081200075004500040011aa24503686500000820004000d1070003174803400e03166020040304600d8541da12143c41510150412144501c8011203403100641d07032242810443c45d07076841c6800001040701c1c2d6855090b09064800d0040141c04402550004503440f41400707040c58032400c0d001c2c014031800a02c0c42c1050240785241e44002e5800c03404668031600142594030301e0044103500d10482060800c403042e554480c110701c2d0040e6401c5402032040c0b00040c1c0203045500c07a00d00001e41103031014494106ea403500c1040b0394100724010821240c3c0018010010340c019110a044240d5447d8290900711100842d0404649640f0300001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 922632014 1250 922630764 922630777
    0x5010608160c0c0306020c0f01060306050901051b0a050f09030d0306060905031f2a05040816050303070308060a0515180a08030f0f070c080604050c09011404051005190f0b 75
    0x43d9000702c141c0784d5a5980b00950081503a543d050151800c030403141030f400e000c3d482c0158000d10700455a424104c0040c0d0031190064011031501044206a010119480050703410b0880d007810095290484c0003a002d4003445910b46059150007070003002d005030f0b90180e10171070540c3d2450340c604e80c1c115111410f055441c00c0568614181e9080703008800ca007164580c020004248914280151840e17000610441c0201e00c941720001198010400b07100c004001c00c600a103154141054030070261078080804c0d1070303114951000e0200813a00000420a03118000c03150000d0801030001c7c03031024410280c0000e66000150b6000c0003d0020402145515002d8003034000e075424000658074241000c14000207036848050075842a180511121000c203901d20081d000500c00c000241000c1d20741860028104900b11415500c0b5640110050054124820700703181024010340d030005844c3c40b00c001e40a03903e210b582c0202e5010000c0b0000d10501070407034201000f2280078081d03031008aa02c5030040c0c4114002d56 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 922633264 1250 922632014 922632023
    0x40c08030a14070c08030a0908010c0215150315100e2a0c010b1903031205090d030e07030b090d090801180818090106030501080f0303090a11060c0105010608160c 71
    0x580c0c9490801520b0300082408911130300040001c165a09242ca082d50400d00088000c902007130404c0041140038091403142440340e01c050002d05d9007010013984126005010081d104165100f020ba1a44080224810115003522881004e203028004480d28146501910008440100200f40c00d0003924110aa003543c0c2090242040d9a4081d0650368907003052031803003100e640340d40303038200d10b5294103450681d054102d920a012650860030702501c4a1008840354800c03600e04400c002c459a00450100381452692501142150145d210240b40c810680c00244c0746400311400d02400e144001291424005c00303403070b42c4221b180c3d1045401c0c201c55090300c036401410060a08500054404c000801041c1d16895681d8551700040000c5440040244c100c900401d40d180014032040b10304001200207070341003000451a44c43c201810710740b00e00b00d5820003030a200508160452694400041d40d44070b100d200020040c0350f950350802491850103803441c07928110407080030b9034110310624059400d207801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 922634514 1250 922633264 922633277
    0x207050a0302060706020c03041203051e090d150605040f02030a0c11030f0318190b0a060302150a0c0206070c1a43050309090108031207110c0a0e040c08030a 69
    0x517110880a9800445040d00e9400104400700d2440810380c0302001c802c1c040d6440a48454032040300030390381030109104141c400f00500c9241442c2e036481283c2c0101d190700c207000c1d010070540944680c02820300c9405c016131050800505400c1c50086901444c4603081d0641c1c10b120004103014140e411f50980c01d101e0045030400c000d80c1d9040348100b4002d6810500202c49004510000650b480c1803c0000c10041281c020f01c22807603007480345800c0541d4004c0302180c81004200d185078000352030007070240945c2c51010008a18840e02e18003030031003000b00d160080d04141e603410b22803500822a50342c5010795400c040707016089480c134070388910039035070103285000c20b000741025014030003d02a50300751003c03441402601d40c241c0c2c0029004e2007540c1a030744500c00540c1c840f2860400c205c902d42050f0031540300b690041c40030880d080101d5120940091781170405200f5002c5800901c0e0910441e02145a01715806030000504106220099031280d809001c1080209440701002e03900d81c82a00d440d0000543c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 922635764 1250 922634514 922634527
    0x10e0d120b0a051c021c0b07020c09150904050a0605010f0314011802010c150f0b0a050d03171003050a0f02010f02010b090105130207150204170d080109110d050f070207050a030206 79
    0x8030681ea138030b0124001443e0040c020440f8042c10000c912895080700d000c10450300384641103404001e444032520003180c011846180102c1040d07540c02e1640d45d2144210b080202150500c20288124000160071130002d011f1581c54580030b2295440c00d00c01243c10b041000792010060006104074480c1c0c000407800481000455001190000c48211054404e1200742c800b407085c41da4548201c03990044940c00c0031468031140020450740308103942c809805003038490a10310001e54084138000b20280741e007011001540b04c0c4c80c2101038210071600018041d1284058072424086191072020405100341d95900a04c021075100328280d0f41c40c54640c0d500a0044401880301d407901d103c1c4207405260360b100060810240b601c401c00580c0c5a003ca110066a00240c18030406120700200541220014000c04100544120080440303505108002a6039500c8080e40c2d95882d080c8200c03090010481000d01c1981400040740002030000d8074404050f204d1030300e00040750b052000c46441202e030010400fa08041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 922637014 1250 922635764 922635799
    0x607080f04050c04051504060806010e04080f0705070f090605040209030703030e01120f0c170c0a030504020d0b1e011d04080309030921010606050315040b03010e0d120b0a05 76
    0x5002510071100b50040400200c01925036214891003052072094460b94100304ca01400110350450b000090a5040400180040040446c4e0180c20560003000c20365610181841c24039036000d020360090460092303d100081c44c1102484070820b90710300c04030401c0280d41e1442000100d2082c6003440c0e4054000050400219000e03e0f6014003401060408414502d5446130351402c5418140482902603a0b078011100859485540f480342c6e90b0218424111303070f01302550071580354012406032108045c1c64200140840d110b00c0c0c80c04007803541c07000c107071902c83c2849801d80d2403c10306a640e4484103010f00000050b1203107a0441000caa2102299401e1309803038507115840541d10050080c84140710802c440385090b1110729440200129005040100082025059007582c100f540f1a0003041414414849082001c1045003442c003000c403000100d03c60b140d03000ca4050b10a28240320300034010040d2169182e600103000001c0304003140010806038504004005051445000300307508010860310900040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 922638264 1250 922637014 922637041
    0x100801061b021332090c150304061505040509012009010c0602070c120503121e012d0b0703120c05032a0304110117060105031906050301020f0c070602060708 69
    0x41c842e40000c0c0a4405105a40903d0300003e221358092000c8003030f04110b84418144400c040e07083e02221024000a00c04840d407002d40030280010b40143e40c0c6203070443c0080c610080390402000054000d22051500c80302480c002c1a01941003603540c0c16041703141c41d0308280001202d1070b800b4144c4504608203015140c07500250000310040b60815103034071010030fa03601030791842008030b071003030005540d2210500400800c007403000d80942d0b000401d001c420581040c1c00c9a44074159602a001c03006018031485020707007819043d880080c0c0500c403488010030071001000081c2240c40c060384807103590840000c100012190004085800100c041c4045280c101d14040129072103400e5000b0304c02d0719000040007083da80e00540d01150f18055032030311900c0c1941c000042015166840040010b40d2412100207080c0780310080508151402d9405c000341400304540c07103100a060090021900c0e0010250a180300350300c0542c828079030388070b940c1000030050701c0003440a108420b540e40d01201c0da1200100c0b4082d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 922639514 1250 922638264 922638281
    0x3080103060c0804080d200d020a170c04090b131a01090e04051b060c030307050322030c060203060a030c0f080609030412060c0c060f061a071e050a02100801061b0213 73
    0x10401111f0b6029907811200000c1c0889038490b44c00140d0b501c0fa004c4d005420344118080288000c603540d0b08009001103448213580031101a860007217240c0e0155030005450000071a034001d000c0d031401e00801d002042c50002c03e81c0c0d2000a80b40d0f0111141c54610181c0d14090442d801000f40d4024002c0e10b034009000822420301e40d1b4045c0045091448040c4010b055401c1180e02d5000601c000c410041001611081101c0e01400382d0305240c0a4104c0361802000480b00145c003038503064000005c81c01030340300c03014144021500110316040c540d4840344603150041c0f0078400d484143c41102c0120354480b40100451b81124006124507032100030940c0d41c1030241860300e1600c420f20141d08040b8000c076855000d503034401c5a0701c01d0002407ca0801e1540e45440b01250940d80380f00710280700c036200140600d05c0311102900c0c0b005482e1310405052624528000320360700025007102e0070820420207180c03c80c0e42503060350340d07035101d110444004801c1c0001850500f40065030081030080320607121200c1d548800032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 922640764 1250 922639514 922639541
    0xc0303180708030f0307140412020405040c2312150411060418020a12060821070212060a0f0b06040e0a1104080a02090906281803080103060c0804080d 66
    0x401e03541e1004440d0843c0c00c0300c041e011004000000304030049078003060160352003e00781640c07414203090a91b03d03000c00e0601000280a940c0d00d50109003070102c27842841c402400e5144080010030104c42d145040c40c6040283c00d030140350201c0342d407110311b24081a601801a800c0742c420720680d445444891003c0c0c4c043c43c0868112000b0000400c0d0384215030050000b402c180080035079a0030b0303010402801c00c2c003980c80160b051480c00da401d01409101092060088581c0c402e003012440c0c0001d29014207105400700258092025032002a0900c00421410710445150740204000420035140400b601c00c8041c1c060f610880c1000140300c003281c01030180c1c1e0040401c41c00000c3d660324a40c1d010841340d006800240196004100e25002c41c50004246548448068058040c504142c2c01c0c0c2c601002c804209642d07890b406c01c0c10716109100c160700c1004101c034000795044a5031854240032700702010a001c240e070039504240303084110300e0140795550f01035039001201d43c0c0b4107804e600d0310000801c0c00201015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 922642014 1250 922640764 922640773
    0x1140f0708151305160c033e06180106030305030115030b090c031b0f0d020a050f0a0e0a0b070b0f06030109020a150206070c030507020d0f080c06061003020c030318 72
    0xb10710384400b480f041c07250185001c001982d0600500c455030450306107a5040c00c00c2441c2c240c080c002988010081c0c0001101c4100754031030308064070702c0d401c18010b0100008541c0c00549070b0b6402e81c00c00282840c02a0300c0328000380702207507500004500382d584900000e8082901040100003000714011800c84481052070005501c06541d40010024030055602041404003c0148803c00c19800d10301d40d803520503801121b1501420841100c5140140044020900e5000c14100c20050050007121074190000010580d901ca0102d40a81055002408140942100b01000c104030b54084d0494641c2030b08403040500e10f0307682e0320451001d01300c01000290075540b100c0a600c0142c4498080f0009403000050000071904402002850070340e0042c42c0c042000801d400b4800800e070004111100c0c9501074881c05480240c42c00c004681511010000303090840014902003204004202c0e0750150800721286d80070310140c1c62084041c0c1c040c102d12041a83c00800205142080944052000300d61440544 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 922643264 1250 922642014 922642051
    0x150c1106070e0a0b070614060105160b0414072d030312050402040209060403232b17070c030801091e0b0a0824090703080304031d0a080705010201140f0708 68
    0x122101c0d00401006c0b2219500c2d80c1d040c0222940e03102070103600c4002864003d040c4940546010700c4d2400b0168090140c1e0102800300c3c0c01d020f9600c1c9a040f6245101d0f085800c10750741c0d4444102014540302d180010160f140c052100c3c2408142e821208883d090b9403600c000b242d007400004024500508100d80c0315a003000811229100c3e41c025200450262541e448804036429080854580842d0b10050310742001c851020451004204151501c10321004d040c560f42c014403050300c060303410038610410542e110040212455008041c400702e144240d551000a9a881560b6410b807001d0000140c440008042e0040f43d280e41c03075201800c4500001d200c517452642da50112800c218120750301001c44079450b21034085441c00780350050780094242e401800b0403451503c42e0011400060002010444040188603120600c070f8043c5410000c02403040d41c501d80c0c2c03083c21503a00e40c820b214070b9006d5403c00e0305440d00701c100d44c0810f5116a680000d400c0f469a19080210b40e982e00c0100300b02c20f8882280d04c034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 922644514 1250 922643264 922643279
    0x90601030902040606020106090f0e06071b0f0b07170c0a050a020a0c030602120919030e1807021b0108010b0403020d02060706150f051f11070b07150c1106070e0a 71
    0x215801003601b078000103012428030612800f45c0c0c0b20b4400301e042160a207000051320000000b1481e40c001d0301c0c1c4c542030200d0b42c2c200b00a410075a68064000e48188609030081080c8021418490b0140107180c0b42d8002c001b4140200b84101c42d4100c8ad806400401403208030340c1b0500503401420441c4481c8107403002009144d0b10680176a1322038105807451a404034142010072000600c43d504007400100514807909070242c1e800b4000800f8100604024895007941926240d0145ca04148074071801070040501d00050b0081d070b280400900d03038000c0104074034881c080354001c00e0f20f44c0c169040040c405280c00d042d9000d011140150750360807a0040010408540401c0c0c15100d4030581341c0c100301456945502e881f00c44400f1000c5030b04071521880002607000a6403841c0800780341c00c5d40309420503064840140010300e0400600f0361020203100380c006500d8040215a030031000f9054002401044509004041166070300071003090090b0a40c8070a002c035401d68001d040c0c0d0300320504010010320030340e030301d6000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 922645764 1250 922644514 922644521
    0x618030b090a1412040605090402070f06050402010f14090411041502010606180e040f080c0a08070b07090b0301030605061c0303150e091509120a23120609060103090204 74
    0x300c90070305402404414081051001c110015481c0610080120100c0402101a00c0c800c0d4031030030301808400142c02840351525019100c906800008100301c0003114203100d00685030881e4120b0001e0880d40b140c03500310307000c2c81851141c24a4080083e007003541e8001444020300032850000004c6600340400980c1c1e00381c0701003400c28500d43c0c0d8004500c2501d4050013078000102101c456030300c00f404000030300060b0035424034203a01c15007090b410152140c0f035040150940c41184000e8010707002c2c111740c9506103d511001000d40d49d2107281007075065560359104581845150141056002c4200300420205503079401442d0000e1004182030811024101c84040400640c8801c40102792124200070448000340c2940f001060b01d1404103909241460f07410781c80c2c03c030b89100382c9a20107581010130000c0008205402100d13080c9401507a550319a90070103408040e89031480748007080346405041c10a06407200307035800540360318000c040c540ca0b1103042200e642030050000d41015516100280940e13650300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 922647014 1250 922645764 922645771
    0x405040225050d11010525092d14180a0e0a0c06030506010f0203220e0a0603140d1d0f030a0b10050d080a0503040311030403150509160618030b 63
    0x100600b02420500000340580c1c5030032140503130a906d80b004200c820100c110fa140407558242015500751852064180e4140000350021003041c62034209200e1414403006201d0743e4501c07199030b0720383c0d80c540d00d000d140c02c6026901c10b13458000120200c130500c0310030b8011104d50441091100414410441c031141c91030892046020f492400d11550208075058045c4071b820b03000107082ca80310319010441d481c003035920700c6001818140015019080105483c14141c200003520410384c2002c0f40d82000c01318079000e41003500083d1004091118848000ea00c0001c035083c90350481d84440880101d001a8400100d102d00c41c1d240c0c02141005e109034465506000100f6010320519020340641400c819183c490241c50300840c0c0507000300e03c4c0e6000070406038401d442d521052460306540d26500c40c54220750060b04103c2e416440d200105010040000c00d0400701c1c0c2c02c40f180d501c20091950364401c01c40c0d40303007500c050380510500b9007001070240070320403902c280550010060342c024281d56030341c41014024044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 922648264 1250 922647014 922647023
    0x9010908070312113901020604050a0b10080a08091906170c07020603040320030a02060f0a09020a032001080412031a030304060815010305010b0406080402030a1403090a05060f0405040225 82
    0x5540043c48005ca2509046401e07400388020451890940c0e5a035581d8406a1006005802e8500c0010b802111b100802c0d805080f2070f2056480c448813a103845012034110400c158031074000c0c042d0351a1600d03c41c02c4600c0442e0b0341e80d03070382e24902c60040401c199040c0001c0e00c807070044401040050003586884000390f0040e407095840041c40840301d44000c0791001e01c41d0042040c1e40023044803000b030070390010340190040565101c680c400d88407599560028005114029084100c008000090181749822110840d0300590094a0b01c510712004480c03d0400f1100285082403801030f8200b141c0c4690300c81030003289601c5804030300c0f50401000919540040d401000095520301c204500018281d5903a41d42030401e00741131101d54108840c04002e8020703401906e0400008100140a56a080200d025200d0f0000260815107036004010b60f100d5103e05052030080102d1040080c060405004840503141047c41c0036003401c4c105000c00020f540510604110343e8500000c0102c1d181105481d0341c3c105124 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 922649514 1250 922648264 922648333
    0x909161b1119140f1c0305250f030302030a0f110d18020607030f0c08040303030b100903020306160504030b01080a022d0d03030f110901090807031211 66
    0x10041007040c440451501210706541d034030820094481c3c0154100c1d004041100c40301c201d10030400200d000c0d500102d0801c01c000600071106410300d500301006140b140f404024481818407001006913003480c2000c1300400716000a401800400c2c882d9000c0d64014018000c0480c44807030203000c0700150b40d101c03203560030700c4440000c1400d19900c0c03902c41c1c0002c42c005070145128442c1260002035040c09040d40c0039050252170740340841210711807400d01c005580c0c040101900c60782c8904000300103000391b9110601074103c0a55220000b4045c2551000b200d500070001e1905644074840d07603001c010030b00070700801d106007840040000f4204a0300240030746044001440048800c0c01081008035a14030791690500d014400741c0880d00320380b041c3e0300c03c4110945406005070014a4220004c0820003070414a041ca00708021200882c514000d1001c02e10036079801200c180c807949040e4444481d403000605683e20940f0303001145018060103007505a648041c0c41c00300b030514085507410888a00c0e0700744444074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 922650764 1250 922649514 922649543
    0x91d010c050a030f1806050403020a080a030911033f0d050609011d0601050a050d02160b1b12150603070806090c03040f030c2303130b0909161b 63
    0x145449400f6113200d1440e401e024038900141c02801c000b60301d01000d015145c0700c000160030b042c002c2090b031350441c0d400600b255484c4141c040c02001444c0103542101c1c035080708892903520b440d0001d001d99015407090241072040116400c145071060500a111043c0c00c815100f000d900b096900c06090340c401810400302d8240b41680800c44028416042502486280c8600804072043c0040080e40b040e82070800700d03a100980c1609807190702800082c09002400007607920f041c030141880501c1a02d2150840201ca901d0315540489041401ca6803202c447c0e4092040a000000d04031920760404c410100b11120248140e000c2101c940c411103040010540c207030b05000321030800d804040d0b4002201e0712080e04605103555100e1481e02031080150400650550f10002c1c0038500c040b203ca80020811003c00050700000741586980118a100c0c400d0b44581c00000350341078441c3e00b1100c4407900144a041c0035540c220840c8143c20342020002c0801841c2e40d50f40c8203240c1960302c1c1c9081e08cc060840c02c5090070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 922652014 1250 922650764 922650767
    0x5010e100510060212040605090a050a140301050c0307021b0a030204050903040f120c120c1e0501110c03280614010323060a111201120b0108070f091d010c050a 70
    0x21040c3c2c2c0007004541c407502408914010800c1500d040c0d40061506950342c40d41580080d80000785d980109038046103100340041d410700183d0504c0d0140300264024440d0390b58030b0840310541d00040703c40c9000b50700800c26890746041800000300306028004c1c49084402e440780c01081c212071781114000301c0c80e8400142440310b04200000e01004021034405000214100c0e512100a5100c511812607460f0440d08800c00308501e0485c0080500550b0002641d04074010521052118541c407035140440c00c0d001c4090a4100042040403244070040d0052510800b44c0c000819160014038004c0407041069107008006591406107040e00c10444501d40e09950540c1021500c44420030680044000400007400b1404004a00b0301d5001a42c0040001c140b203001d40d10b0b40413403062011240c1d1f950054030010a1990038003060101c00c6000340f20b80052a13898403089680d4032800d01400e0145003614208024400c104c0e008404800480440001c81e00355482140e0301352440b15515001041000c1452065103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 922653264 1250 922652014 922652041
    0x30c06090a140304150e0301090f151104140114070f03030605010e013014010f030b011e03110d120c021912060c030902132c0d080405010e1005 63
    0x1480d102d00034614062030480072050340302000016405020f807141c0e4002c029a401c1d0b01c00c2c81016004248141080c1c5186030006506955200c16000c0a02c4c0c02020f5480415100a40d0305844d17902d10610300c42010140151451400e003803050743c040c1d004001c424001340c041c1c050030300400c0c42a01c01088140c100302c000b41203c1c01c002007a0f410000480200050600c1c0c00c05130340d0562501303c828120310b06144007240054074511150700c5d44540407a00000341140315120207011203014000c8260982d0b01c448020503441240c1840e030080100500307062002c20803912900290030303802010440f940103a43d990220780c1075840010000300d0451102c400079802d003011800c40c0125021040e4984500740785412040c40c0d540200a84280d40c2c41d00d80076440b6001c4d038826400d054005144800c0c02c00590300160240040d001c0c004001e44058012405c468408103800c0001c0000ca0050300c6115800c1d0811243d07100000e00554040d900e07440118510300d42403249001188100c40c0c041040e2500c1c440c0c00440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 922654514 1250 922653264 922653293
    0x33f031103061309080c160f050609061e0d050a0e0c030309011403040825292202090c12010807031109070e0405010b0d0b010e010905040e030c06090a 66
    0x48100030030070030030b859444000d202c2d4601c0440c3d03030000340130302103080c103885600546054000c50700c03451005c48030f80d0640069080c1103c1840b101141019190000d10100e80550000240c011f81d050040c0c000340c0d9552500185042d068121090511745c84c2140c0b4015182c080e9540d4180c00d6440441c0b9100c0081880000c0d102d110a80003585018101c0c0d000802d02c526071051580403000100110741088044001c50312000401010f0f10145c10f200780402114102d40d40085078010b44c01545ca52040031111102421320f0071030440d90103207540c0c28440c4ca10b01401840400d000145e108405c070016500c1d60700c881d0098014500b005d8072091000b40d02070480d030b0180c01402907035024107004c00008503030000340501000242c46011007511011000e90301103180c40103a07640309013800004141050140080c1151030000c101c18004003404030015581948504912030020709c00c14424881070030950050345030004103500300da00d012503410000b41000416070358240385410a0714450244501994412030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 922655764 1250 922654514 922654541
    0xc03110103110906180d0605070f1707050a120c0e0f03210921160608162a0f060e0304060c060504020d1b0603150f033f03 54
    0x11014500b401c03003501e40990a1000d22030640025444214502c1e04042d02c03101d0700c060300c902107200e01490018082e000482d0100001384d2030260310505540b080100c80319500d030301c2c202030b20303d510303015002c5441c0d0307010380911028032250351011380c0186190310440303010085680e1540410007054040026103815030f461544607a120900d948107426040ba1740d4a2030307600c80b480300c81d61142c1210201d1400c6a002e9110f07614a040d07851090750b410404039010b611000e1040f10b900c1a140c0700c00cad0581d11410242d0f90035084030340b49111a041c0900030740f01e160284407441024091a540e1400702d4410707100e58131048601c0851030702c9881c1080700c94000c56035805603007805541441e0070584020058442d040010b2300107525400400c00f5510f54500714056035030004085580c9001743c21240b40b4500903841103c0c000b07458443d44c0c0301c03040126048070040e5504080490ba840b880d54440c40450055502000b10080380300030a41c1c03000701c0e0000d15800c0b02d4202c844411075184d1000001d4200c038403a114420 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 922657014 1250 922655764 922655771
    0x17030702010e040b0d0c060909142502030c031b0c0103060815060604090516020d030c0f03050916151803032f0613021c0f080c01180c03110103 63
    0x50380c00c61007542c20a42e00b0790780060078659007400205184030020010308000f40000020820390740c40f0040030107480d0000d13028401d004030844148016072088518040c07080100c80350760007001c0500700f0522101d41d588112410b2280141c00b90341564044d040c06100c0c42c04020f8020b200c1041409984150102401c0802505250000386030700c442c141503140ea0f0314017010340000c03a160b0b908010b0300d018100b4858108a580b81c08452004100407080103c0c002d4465240c0f42c00c0300701c1c07087c080c0548203245070f9a5085901c8030507105401902d4044c104042902610240c44079081c2a500618010501d04105203a48a12503801600d818061115030310041402502400841d4018601080c8003009000e040c510102c82600400003c52035400d8440e40c1c02900b0a00c42030740d5003c2c3d82d002c50a4022a04e4800302508903031294000fa0280704014042d40301c504031000441c6000011f01803140c4d050f4004980c10032051080e007082c000c944411500c011045800380180080e4041c0b80483d40400c0c01c081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 922658264 1250 922657014 922657027
    0x20a080423091b0a03060810050f130809011805040510062006220b01140a090b1309050703290903090a03080306010e0607110102061311040510120c1703 67
    0x14a0f001c1c80ca542540c1a000019001c50001c1c03081e44040000c0c01e8103400c3d41c0c09070f1a00050000070384001c0e2803151a20707020074041861b04111000d0403000c5a80036900790301e407046c520019542c404007000b901102d181d085400280a07161401828410642c10019105180c200f10b0042c00d43d04126000003426000c440410040c0d8500240c00d0b500140c0081c4a00305044008001840140e00120000d011020b034400005102502c48505050264110ba180003c6c0d40c07201003510490f06d05000e45684040c43ea202d1200e00e40c7c803507000d80795142c02841600c5c0007503100d0311a060304030504540403800100c000354040200040e03a50441d00180b012015500d40300d8501e00060300d217656400007509001b000404070352a40e01880c0f0010807c0700160030603442d180142802012000c1003502c1e2805805158002001d02210403a40e40056522064030700400c107201c0240402050010300d00c0c900880038500104880314400c070b4a040603842003044200c06814003580c1e44c00c01e90300b0041d003042c0e98004c1c03140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 922659514 1250 922658264 922658281
    0x2d060e130b040209131505061e03101503050d02030c010501060e06120910090f0b0f010b030f06220507020c030c0a0608150607030f0807081b030403020a08042309 71
    0x841c1c0d00250111140c0712240c8542c0011042e03c40001002050031517859000b010248154000314030070b0b4030486010346264001101581422000b46207a40d05030002e54000351358120383d92150340410b5101203000f2255889580756840c05003c440640c015034800310740180040000d000740c80c0540128503100d10b03e4031003400420400d0107507050351652422034100050f2030300c10030001c40c0f0044017a400300340000915130611a09140c113514080d602490041c0006000780442c010140c100d0300320540252444e0303241e0090b1186001c02030b22003039010381c04460700303500000d801c05138080100d4000070004480c14441d4000e40b034001d50300300143c0250000340304c40c0390039503400c1004070848d0340380c3c10301d502547d641c100005a2170101c01c0c602603002101065030700500d40e01c2005610403d007180c0358140c030f035107900346c1c261440d400494180c980b11002820035050ae07948000510b800038403d0040f03c1c000c0f151a542c005c1a41c00641100940442c1280f80361003085a91034038801002050b00e60500d01d0900d02003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 922660764 1250 922659514 922659533
    0xb090c0609060d2d051f0b1b030f0c1903140702030705060a0921120c03051201030b090d030e03041e0e0403090e09010e102d060e13 58
    0x542889035a0105410400c01581d80000030081424540f0b900380b010440210460205130800410000340740c0070000b00100b08040305080340c03091000345c4074402032070220301c040c40345e00203240941070f48440300040551303078020000341c06440000a0a180c4610704004c1d014541030011808023015030401718ad01e40420340014440303081e25100c841441d518256800407d18000c0c1c240d0003181c01620004910240960284059080e10b059400340900b2040030900c400e009440c01201810104d0315002450ba45805924a66000751003828081d081c0401c01540084018003603005807541c6901604000e24681d00b8070030b600010845040402c40048a003042c1a5a4010740c000c90125440c1502c00c029803800e00c03012071001340350410889040d8902403500802c1c1d01014480c404003200e00b1008641c001030180a040b0303036106d214008042c400701209401c000383c40041d0807001d07540612a080703520040c11100348108602c44c0072021580e280740c0b6196501d80f001c010107280b08407821302c41b0140054844503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 922661870 1106 922660764 922660777
    0x708030909070809060a0f24060305070906050d0f021b010213060813120e0628050408031c0213030f02030f030a090911090901030803040b090c06 64
    0x1d00c140d0b01c442060b44c10f00b0b1180c00941c00100f06614961000300e60000c0d4480200d80d60b1849810314003900061003003986d45920014043c07001d19014042ea40e0407444526010101910b8618010401d014110305109801d45582e0114400d5915405a901400151054813204249000e160b8001e6020301281e0950300061741e000503400d4000d80349988118111080540e80c7c61f0203541c4c2d10448a5502c0c0c40c0424003003415201d821584480028041080c08007407c88980341d0110300050741d030855001b0907800c20a0801c006d028002010090780c00c00c2604a410501c4000c030800d210380039014407131034a060518030fa50000203005d0840851b50f02c1d203000781c0c00c0d15459403103041d02035281e10a00c80d191010401d40c0b1400c0100c035601c0d078014060360003501c0c1c00504000d00080000c054400a900a4401030030200c2404144006010700c00e40080000c2d0080a00500d02d6012840c280102c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 922482014 922661870 := by
  have h0 := BRFrame.cov_init 922482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 922482014 ≤ n) (h2 : n < 922661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
