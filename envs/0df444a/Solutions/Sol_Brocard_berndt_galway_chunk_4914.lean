-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4914
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:08:39.011342+00:00
-- url     : https://prove2.me/submissions/40d5133e-9624-4d4c-b150-f5d28578ce9a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 883633093 ≤ n < 883812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 883634343 1250 883633093 883633141
    0x120b0411060708031305060901090b1506040b0309010e010b1c1103010b030304090f050a0506030307080c0c09070309050d0305010f0b1809040c0312020613110d1401060914 75
    0x429001d46540048a80c000c0e40034001c01d40c4d9207091041400a0022241c0944d52842920002590340c10f0512075002c4903600219016440c0d0307140518000d41c0100b41c486160054814400080d02c800d104000c0c5000d8103500780046015040084034a08541900581c20700c03035007000103094811072400c1855450b054015031041218003805010034050010000b240fa014480000c001810240540c0001c584201c1d0207414862074449080150a60b001034600a0781a00208098000101c0c00002402c040424a00341c48002c4517100006114a604580703850200c0e80741d54050003000000d00c514081c042c007034103007001154148003c00380c11006034043c0380203e460001d0350382c6002a001c0507c6680c43c4008180d03910a00d0f0a02d400e40340700c00c4a21003140d0109041303101032041400803a00b5403050400c284890020b20030b944820764182d585400c501e4205184001e20000b1503548481c3c58103e00c484000070030442d103020059404c50b060100b488000e14644001c1c4509a0403031298844001406 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 883635593 1250 883634343 883634363
    0x7030b03120c0d140406020717070e132f27130c0e0c03060603040f12020304140d3305190c171b0c1f06120b04 49
    0x1003441d000360050a20300054010503400310507180011030001c407000503034800703007503200d59030405446010300d00a02d000361304120014404d8482116090000c100b0345000c85000c50b40d1148007810300d81007916071071440c600300d041d04400e002c0000c011040c945072028070b501030b0f105504104191194101301007446903201d0300a01000000400e0109510f81c541c2800780e8503820902c0811401071b032042c00c00c903010104484e00054038075110704102e00c50130344030041610310707500c50f01040440d500045c0129400311a25805202150580e40700450804281c0c0043d039171031342050109038252001c41d02003885601e072900b000000a418074060792002d000021440c2e42e0441c58090400010310390449091400d00d000200a03080e0403080c003803000c03012034503001c10802c142c14004884102000441d8003a40c807401e4089000e40c0c5100341c1c01c90702850f03d0420203090001c8001200d0524505140001c0c0b902d2002201d00c10801e12441b6080051019180c0c21810002684d52070a0001000708041c00d001c0705 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 883636843 1250 883635593 883635611
    0x10807050a050705030f040503071203080f06150d0c0810060e09041e06021810080f15040f0b030c0f0d1b170133090b040207060c09210b0703 62
    0x381040d28440c0c4c1d0304c0b60541c2d454100d690540d0860f03030814890288607118401001600c2141922070442058250342d645c1542e541e60050003140d01005040c0700e030800c2c080c01403d00d03e02c401c10082c00d500c0c03503070364004035040711a0540240101d80103013040301503500f0403d0400c5100d0b003108241200f8902610100c07040e540c0e60919081120704440c07a10b005403009889442004940d500074405401d100310790f0b89401188400340402c101ca03c8541030b0101c3c0c1000e01194107101c1041d4072551288035490040308210a15012a040d03449002c0601a03158843c00301c1103907441c061003080e070001007da0b084840a500c0000203401225001c001030202d5100324101c21900007414400340240260700c0a22101d0800ca00600e402400c030150a07040c41881244d81d130b170f8512020440b125000500d0717000300012605044000008005940340983d000d982003002000150480c0202d26070040151182e06030320b031034462814002030320710311340448000300c010300e103400501c0003006a504a1628500040c440030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 883638093 1250 883636843 883636847
    0x2030718210f02190609080303010e13060f1d151605030a0e070312020d02010b0109091109090108160b09030a0308040302030c0a081c0605060409091703040f021806010807050a 77
    0x8020b1201a40040b0442c5082030707007400401e0344ca02101e0007661241c91880da07034418070ba01c9008c2801348202d01601280415488000f10058424031030007810300283d440d8402c2594000c40d0404005444102d04410205101e164184403141040120b03610050440c03a10a00140e40100c01c031120710140500400890184940b941c0001100c0c0fa5030b00c200d411450b200d040100c071400c0481c1c1c140c0018444d551038a043d20f80b060140d21801401a142d181000741040c2c0b000c806854034040c42140a813051069012a92314144c40b42d000b801c4ca500500080003000070510301d104540d400c900c42c540c0e01040b9400c80307910002441200f030361301880d0160305912545002c074154030417840c103203000d48280b541410030f2044000040010ba86e0030700c0704140450029650b881a0359041c814640e000c00180400c221440701e40e04210300741c0d80302d40d42c4181032a081868016503500247c40640306189035070468401c604000da00b520b03440009071000135032845c01d10002000e80600038020020044041009680a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 883639343 1250 883638093 883638113
    0xf01051b0703060b040c170109051806040804150f0516060b09090c030c0d0b150d050d0801031b14010f03020f0403030c1e051203060604050901090203071821 69
    0x140c04600707980c0d1155590600348080c086064049101d1482e04d0340c0045140d000701a080c48901c01940c4400250386001500703401054024811800111440c860419821045c040c41e4820b501c80c515080e1a9400c01c802c00c4a28042144201c0c280040c800d008002c2d150003605540c520080150496101000c5260840242800c00c51458106d01d000062209520010540d00d00d002c2c401c0e81103039843e000c00030810034007042210300a4040d62007500440c0c840d0882110341051000c001d00001194170090340e44e98500303455000c40da40042d1100005104120051003040c824110100c5040038031401c0000c40451545010003040c1400084014001ca0300c2c004c2d01070795200d81941d090641c40301d40c1d908028280114200c0c007220716030040704600c1c40d202080040028001d400c00010240b0221114001690742d001402c056404102448001090b03031300e8840c40380c00381c43c860301d0141e142d003460b000c040e0501c000b803041c16801d03020850b41400312500b03151f1000004100e58109040c04800b85c1800c085007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 883640593 1250 883639343 883639387
    0xd0f0c0f060f1103090c01020601050d0f0215210108010b011e0c14010f230621060a0f0506040905280803010906030201022503020f03030c070905180c0f0105 69
    0x1590500b00c040490f482200b015500c280030b940c0c25949420105401244c42d00c10902986900c03c003d031036441c1c0403800000040850030700c041e1000c100107100100201d866004101c81c800404c400e1050110901154101180100340040003481a51000d00004e4010f00500d910222040c4e41c000000407071510400260714075640244080161840e0480128040c0a030481072080c0642489036070441190300aa907220307040003a07174100c000350712203008000f106802a8904003400c0761600d5419000e210a001c0d960044c01d61903400205442048003080903604c00a2042d0b120ba49001d07022008600c01003608051246204085200b604040259900144003007401801b408400700000c150300d071540e442581524002d03001c6a445c0a003031400758032b2207507401d880101e207000150b20070401402e00f64400507241000030280e80c104050781042c60710300b1440354000c010f100d803150144a10f0280c690b900030482c20210014100014103040444c00040d11000114100400040c8828180302c44c01003803855 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 883641843 1250 883640593 883640621
    0xf0a05030f0723160f05151c0c030c171003060b0111010f090308061c0305070201050909090a020f0316150309080310140609090f1f030f050d0f0c0f06 66
    0x103016203e000355071054144481d1041915284002c01d03201241a14581241d80050540494040328400144150452208034200503000b05080054820b40e000340c00403a90142e900142d6411021300c000d00a8217000b4180018011000501092100e028950026260042c03004a28444550012242d204420f81403030350710b5107403042e00100908981c005030401d500a90720000a83c58800030442088211382c008070256108080c0d5100190050303014040c0c981c01410202e08081250001c59a1454103c41006840d00528503100440c50011044403803a0001d80c010b0100780b548507117072420745060703000d455840711511b1a900d44840c0720390441000c01e40d0100b84292281010414038440a030f950203246241d0031030030308503442030070001c0540b01820303801804a0b055480d120855003c44034043d10905407825903106070351000c001410b007a402103100b00300356074460203242802400c01c0c003640031030401c2000c181e41a0305895031091000c150700390400a1424901e45504d040c1c4000d1980d4050005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 883643093 1250 883641843 883641893
    0x10020f030a08011e180509010603060e0a0c0902030c070303110d151703090612130b07020a03020f06010807051314070804050c09010e0c130e0c030601020f0a05030f07 73
    0x98901e0b8040c0c4081d040303460f240f0450001c2c01c1c0010b4070024602d0b01d40500e0314103a00340c2c1180c1c40359540c1d41e00142d8111010b0f10001031807e03104c9d00c030441940d00420000072140e0000c0d00e51400c010144003400014120803001318150300b001c00c0d240005200b266006820551240214004500746904668842400100422003440401002c24425100348a20030100100b0030b0035441401c400300444000da48004d00c3c00745414003014985240741c0c8060300403400d80182d2a022400140441d102c0ca014803610f40040002046518000746000c00481d0102e00390340100c8010064040002104020b43e03c048511001740136601c0c41100090159501000c225110b40c2c080c01581900004945d00880c000c2c1c050b1542548058180089000c0038400c07964a002c0401c0003504621042c00134040030400c0c1c56902c46081d81d920b00051080b91305a40c001002000041030040e15a010071002c10048a0b007c05094001c0d401e81700c00c0c0d1a405002491002100001814820016403c856440803480d1400c01c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 883644343 1250 883643093 883643107
    0x20c03010c091d011220030106171615230d06140414010605160c0f090e06010b0901030c09050d110102010515060412081c0516090605030610020f03 65
    0x1c00c50103881c4162009400c030181800200243d0f040118141c5481d40344607078549400790303641c40001e0848602003130094055019543c29a4003030140030014944003000043c00981241c0b1982440045094110a0210090b04000c844004406003c0b0f00a1a0a01c100302e072861903217840e0100701413011050314010000d12002c4843c2070740d20076025205c01c002013880340800c2100388030032140c0101c082c15410100c0001001554410310081c806540035030a0000d200041da40c6821002c03034940c0106020070f10038141442703911061f100e04802c0e4056400100082d514010b034980c41441800c0d00c0c2d6040588880c0c0707008205009000010003043c2c0900f2040b8040c110303040461105403000900e5006500b4075012400022200307980c0400c03118018443ea2416240c001e084080c1442240b04440c1c1190500c13240030401d4a545103c40d00d0341d4040030100702450036070302404c4a00c1800075010184082950140049544901942d5001d00c040e658003104a140410036032518061448151461100181070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 883645593 1250 883644343 883644347
    0xc080d11100509190b01031505040b0f04051e061b1c020a05040e010e040302100218010e040e120403120507121211160b0a180818030a12080708060a0b0a020c03010c 72
    0x781c100c0b802421040d406c010030404500c150380c9d0a4401030020781300c41d800700c0d0b04071060059040d0810b03c1101203030141c0c41c0034549103020303410009886109800080401000060100c4102d4600d5480d440691400c100070f41098400f44c20540c800c40c403503501007030074007c050041007110060714200e0b19000341da6030b55480014200c00100c60032801801101c01300ca00c0d00280d0300030344100c4041121683c41c80d02c1d085004442103250021600e502c103496a81c1005001e40038040c01e210440d2034a441a0348a05500340050041c0303c0304442d004100d400c02c020340c00b0459a28280703429606c140b9081c80c0d0104a10030000103006003000500409000080c10040074500c0440014030301c1c45400340348125941e81d030f070700c034201c172141e9215011f04100c4540c00d400080003c001000c184900c070701c2c001500d0034002c02180c648680a1012103c100703414118019071900000025484a418503010825140140208010f60b44030300c202c8142c5078001c980c0c22080c6000380036081c0380d00005402000540580900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 883646843 1250 883645593 883645613
    0x50d080901020d4107110319020a02122107030e31110909060112060f180e0c0f040612080702040b060403030c0f020406030f0c080d1110050919 63
    0x302c1c07031202c034502c0712000b000c00304410302103114084d264490100d03a40d1010305585060148040610600041000c078080d80302003900001003001513401050601c5c424418401c540e944501d54005903448000c05420041d07441d01c03d240001600c0d02896280c214a01d0299140d040c29000180e001034049591250410801e843d141d65111068050f900c442051844604843c54070303020b0200d0040800090002d0f00307050340303033541049041c54a40b000c2043c45494400b1a00c2940024600c652890070400600221101d4004141e26010003040a000c07107040c03075a5103165100e00d0a000c1d00200345869101d55880c0c0c0400010000000c410140c804103150039200c075400703030200f20f01c01c610b040e01a500f030341070100a80c2e041d00e905031645c400c450000e80380c03000e10503902601264060789891000c0300042c82194281032082c415404200380da41420229405e00344036a203402c0400c00c41c00e030405481100002c00c1c13040401e070000d000031142c550217101c90620381c03210300703905900d003442d5002c808100701400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 883648093 1250 883646843 883646891
    0x50d0206060f060c070b0a1403010603020406020d030509190309090c030b030f0c0a0603020304020418060504060b2b0627050c1804120c0512210103050d080901020d 72
    0x20b51010010041d40030841203009840c0015882c3d0700c694801c3c4020309915004000d69145424000814045c1c07410b00601940300360081c60000b500410204800c6804002024100c071003802c06122628001003040d95503c2174440070091180d0484156091601a8201d5406007980103018060b001500001501504070518002d00904c42d071501e2040b0394402003445110000020200e0b801603103030a1045019401c05041640d100d03554014a0b4080400540441e140c1803241c0c0c4007207024606800d00004540400007628040c007101001c01341607858400d043c0140405460300b030a00358400d418501c0013044110b985192a2003e008000581d00064005011a900c0fa1044840b00c0c100f000521401d41c035403100281c07079880248041030001d0301035a844c2c13440400c1850050080344041d12628504590204031950500000072690403090413039551040c940054100b030100c03540755550b00360340c071584004144104020b0f00c0208510760401e4040303403418981590b003031102282c4050f00132440d1369070070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 883649343 1250 883648093 883648099
    0x1602010c06020a030c020c12070608190203070f2d110a060504050a0b010b120115030e0114101406071112030a120f150e060402130909050705120703120c050d020606 72
    0x1007c540f010b10742400700c2204a015a0050080d50385480401d4828010203850484e000090300c04866056120f803014502c2003000f96102c08844002c880041c0024424400110b460003aa110035005082280c02080100000c0d01d003400030f100111034498103002c50582e0050680d410402400b09000c00007440380d42c964091080e40d10644da0358249006a48105501500c65211410040040e44050707160410050303518140440c0380740c403546200382110f5620076207580070303c201410300c4840c40500323141d500079207a0808050003021076040002c07028040d00000402d0a5491a4008106e40b190030048041c00b80d0300d012642c5400f90340d075024000c0c0d0440400d0b80c400600e44000450140f01034011065005070051b244034160781040e140d035180100090000b90415020480144039004003104100141401e00d40003400301c28a103006420200c01e82d001d00d100342014450703408600c2c0e01080010444c1d81c0a4200c5101d600381003029502c0c051102c0c000385c0f480c020b1074120640b20340c020a1b0203214036011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 883650593 1250 883649343 883649353
    0xb060603040308072d090603060929030a0c060509010221070f1e060b03070e040308190f0908191b1407091b0210111602010c06020a030c02 61
    0x51414014140021100600040c1c01500031900207401540c0f40c4a5a14103404245041d401c00e40c1c06a2000340120512400141c040008115852307142c450714015200f08081070021101d0030309074404403e00c01200d44074924140d4400082035600300f0140c0034481c2c0c080240c00ea1281d41d01c2c00901076400c028a0a4050300441340c403040c240201c40c03032905600c034000c4c45250a10400380ca507002686001081207030071054150f40c502502070214a030f001a680b1590003c5180c040303120508d42003011941c040420005050180f00010b0b030007590751a445003070301c0f08000584d414562004050180d0321488140c030b51500503010180b00400d8020300e24090688491400659800030031510b481300d80904401c40c08001801c0e400107051100030171420705116044511007903e84010b5801c54400600070410f03074038108440c1c1e484507018404140c40340140c1c0c20421802c668190428043d120300d6a8400d002544680e0003011680038400034085103410110440d100c0741c0181018004008919480015100e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 883651843 1250 883650593 883650601
    0x50f0315100617100e070c240e0d090b07240203010306051b0d0207020f0a0b070512070f0201030c12050a051503031602010c23070f050111060f070e0307030b040b 71
    0x20791090042004007483e5000c10b20700041712400c1400a04842d00304003c500074400420002c0760780c0d0040c5d010010031303903100c1d00f1031210800c101c0307216800c1034010360080c6050110884d00802d01d8000c4913100b154403a903139a110b150a0500e40d021010349188030444038500a0ba02003554055810b0f00d1062404000645440000c0742c1006244010540c0c40e04040000780c03000e0b5402d4003d03180b594409054501616220000034004500e15041107403c101c0104001d0140041040b420742c5561a424400b49001b801c0e494404003241da0010281c1031640b202c0034100d1036071040b00441818134818600b0000741c140f03140000003501050b074a000d076214a1040244051a012040740d500d00e0f0b0483c0c011600440300e038010340c3ea188500e00180d903240406803040c45800c146800003840c2801d080d01034000309082411290306440c01c0e400183c10415420041104844000b0b1283c4d08100c4000340e0303028603512828212070f210410001d498250051100000400440c40c003042e005a10500c61080c865507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 883653093 1250 883651843 883651877
    0x607121103060a0b1812030a03060617010501050a0516140106050a0605072003100c080c030601201f140a05060603180a1a06010e060c07050f03151006 66
    0x41610116484400b00c0403c100e8614500f00510b070742000a8000f01c4031030050170006003540504424144143c00004401c4002c2d5490310690020700810706050300402d0016028000042c0c05024090521400159600c14240141c0179036000c5d819451520024103e103142030964800340d41c16030529523007004c3e00418189042c484600c00e451b02640d070b290034918180c4860a103d602d0b1402907210400740f01c0d041c11151000e210140e00241450004215182103e00c000c0401c0c80c014076072059a1400c0c1b0074080c00d680d2201c010f00c0302200d00b0720602d5950140000d82802c2c0718102d0710440c180a142959001807101d540c00200c20440c07141000d0b8499540d12255805441c42150340c654092000c000007065000211003244c196003580c02200d2901c90ba270750310665a555400520b550034942c4000f080079070740e80010f00000c0c955095a509003002c4e40e12120075521034607405010701c2490441004030366500d00f04046c0c030004035010350386500750429602201c543c4105004140011760545a80c00d204a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 883654343 1250 883653093 883653097
    0x20102010c0311090d020a03050601060c20060f0705070b03010f0f0b0403030903080a030204030803041110030b0105181309061b0f02070e1e0108100c080603070608071106071211 78
    0x10004401451a04a00d103081040f140c9030140301b240e0003500f581011020850812041c0d000e010151030f04200180ca9040030069064411030b01d419410781c1d00d441f82d4007a1a000103440948609001c0305031a40140c0c030b4040e060500707039008022160f90120001582035903454440d0110381d1030844001c1a1611140400118422400060040342000a00304000341c00b0314010074140c407013460010b04040e10703076440e10f109a00c241c0d02a511002c030103141207030703d03c2c10041c40c0000c02a1410104002e0025000182050052004080201c54410003121081d11440c1801d00e032110f090108001c0d82c4851705d4900003c00301c49856403101d00b210041c81e2080c2e405690484d0210485070010040e29240c0079a1101c1000e000b04110b8100c00e0602400040740881d0321090301a001113005003c046c1440741641e0200c41580200c00308005060b4144041910046804400e5a800e0301d02001c1d0381c0e5682809a800000c1e504150b400d070320522041041303180e4404020000c428110700148009401444102c13024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 883655593 1250 883654343 883654361
    0x90504080304080c100f0920090a020c15090f06010e04030c110604090f060305060a091e020303090907030603050c2d031e0313090606050a0305040c0f080a020102010c03 74
    0x19020420104001c103c803800500b40d80a20201190116203000c0711000c156486901903510554540700712504200e07501602020f0181c40070364140300d25995400160743c0c06400790400e941e06030f00013180744840100f0b1284404203809005043c0f614284102a83d90351860381407221941e0103114004201f130100110349a005581659501422181503100c480b0340c40603074140386078483e900300300004002c4505c0c00b13030224102605400144a61442c142503081c03003001007a0380d540d9450f02120341c000488000032500d0000c0d4003032684c0071f440d02034400700b451481004929584134581000b0003200c1c0394590001d03025a44108103030303000e02c041e000500801e607000000102d51100146d5208000f07500d104441541003600404454031950101c1d044d10a1100040e01d14403280c100150250780785440840c61401020444001c04c60203262403802052800f801100d40100340d160408502400440901800038000749110203884a680e01c0080341d81d000104000c902550818060301c00781d07800f074400d41080f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 883656843 1250 883655593 883655603
    0x20f040f0b0c1e0703140d090f0b071106070602040816051008060904150203011401021204050319110616110a061e02031b030c1216030c02061b0105060a090504 70
    0x602c0c2c3c640701841c0200c6140c2e64000700c040c0720328040000411070000d500c001000e0460040c1191540c2c1c070600401c2c1e545a40c010303410100b6251020440c7c3c00440048404241d0491034180400200200003032031031265400141819001280c0030400040214203156800c3c060501c0d0007207596500240881c00008261003c0450310000004141d42004030540ea840f6114400e801081010800a04126042170f04012910441907207000c0c0e5551b010801c2444c20760704001e00500b03162030040040da0b00c01d40c3e00da442010b01c02080306041004101103590f050064001d1885880305844c81d4607000340013501c0d20a94014111710050302d0b003030500c24010301c00c0d1603180c1c1d5810f07500c3c10450780120060440541031811440f0412001d0800c2005101610285030440c3c084c2d6640c00c0c1100d1400d1502400000f00c14030900100080c0101c0c500303000b0204d5900d03070b040c00e203c02c0101250001450170b001d0060b0303a42040850842c083c0742c091044d41300c1485000c0859075030000544410380001120404c6030000c1c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 883658093 1250 883656843 883656853
    0x501181a0706090f050705010201231605070510020d0506040b0a060e150d09030e12100b0d0b091e0a150f0213080303190506031c030f020f040f0b0c 65
    0x4404031960052220a0141001003080007880c0d840c10003040000b20305413125002204148034960313080c0070310a172562713a900e02c4040380c0c01b1359122202583c1000d007003082045480504941d080d80100c00b52880513030040103580105800e1000308010b9844651080401450580041c901d03140511540700701c5000a03102d0a07a86040000c1a40c01010443e5034580c0503441d4240009010300c1c076801003403c3c111113400030500f40c90fa45400307026020702380c05480c8207116183d50610405000a520301400f0580140864051040c0020510b120b0703034003002600203d030700410000d00b500002402604c444811803221100e42c0941001d68481c1d803e008000c2c035100c2c151100c0102c50885401c614101c09100000610b0310800004076a120f10241d4010403064001008110307100300c06206144c04002550014004c9140900010351550800450300c01c45400c03444200d10001c1c400e038032072104800040ca0840d0f03190341901e10080d00c0d4000b81310380c02021001804c04140d107503221058482545200000349 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 883659343 1250 883658093 883658129
    0x4080d081308160305090d1a06030102090603042409062f0d050c040b0304122c0108090f0712150603020d171204060b0f03060f0a020f0d020310050118 66
    0x80543d50840d8815020414207001010059480b02e0000b41100e01ca031125a48040c802d4403c0d5564420040805201f40d205024400e2a501e0b0202201e0740654801e420040d010404c211040070440c04201d80d45d0880d10300781105080040581c040c02a41c00011134550b01e1548142c1c82d10503000441c0c80500f1100400e0020070b0f441d130110341110350065030000c1242d080c43d03151003a0603640c1c1c00c216400d0b9005189203503034413451504803496454102d4911130300d07441c003d10036020741495040ca80c0311604102c4806d000880d454010300041e00b0007081441642e00072075a41203198144140300409981412900c085107a41881500c140001c8990191507241041003540b1842c2913515032038420803404508201880303100101d83c1c04240300340c1c4215400030300d502038907082c005000c0080a03901d00a6001d0803d100c022044d085c84664002d2580c0409a030310b80744540703041d84074040e69207400c40b041e0022061040c0b420000c4010801e485080c0da5a00071500100c04402503080940300301040b0301440b801030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 883660593 1250 883659343 883659367
    0x302091810020d0609230c0c06011214060f0912040f090c0507050102191106190c02010e010504050601080d0807050913090f0c03020a0623090a050604080d081308 71
    0x41c0500c100c0005000444a503503c600c2c009441203000441540c071b8075004000170442c520061160041100302c101800d259440090540e1504103000d03181c00020424100420044c181c3c492200c48000c0c1c0f010364102d420445540c0c843e16000342d6030078042d406040d60074550f40a000c1c0541b4101c40324101e00001d61845d0052070f00080a106d9403440400500300462400301c0c0702400201040c5c180c0c8070800e002411200001081d14000c252610030680100003400105940d5101d46c902d14022035400003080d014408040c1d00424251140e000c05500700020030092044c00f0821904031760040040d240011000344044035240811249200070600c24005c0f00c00300e0800d640c03020384031101500e00060b02c03040c03034a6000e40051611004c840321008102d060085003070206400f0b0044c031003401c1204241640e1030454480000314038105102400104140a65543ea552500001c1c18050162035940c0d03254284592540394413030682e00403804000c04a80702841c1100785100d201c3d0020310184c00c008254000e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 883661843 1250 883660593 883660597
    0x1505210a0f050f03120f0c041503051005040905060f1003050604080903100f0912090602030405010c0501020d020301080a0c05180604200c01060303020715090b0a03091209030209181002 81
    0x1c01d9403a88216000907444002c02c00c000c210000039001c4c0d021551422102c0c5d0300318902d006048030161601400100247c4082070503405038228141400309007940c501c180d500002d4025442603504c941000040720901101042d09405035060368800c0c2c80503aa0410707403e441114078400104107503c55000100860b400030007509003404002d0980d5580302d003091100050303841d44502191131a903603014210810450501071136403520b050070308203425894000040d40302d009612445040c4801914072508011081d812a00240a4800115120350b104c1c00450344d01d5440040445502c410ba080107d40b41c40c11400d44220191200c02d10798565843d1400d0001402d072941c809540e100301400c1100650300301d007020300a18400e200002a0852940c10020300d00301081d03024000c10344007800d1028403945d1240030001503440c080d04050341c40030b4101e0100c0081c445d803c0c026021001a40c40700082c25404114071045134003c940d40034039a150240e08095440a608001b44070394451041284540500c3d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 883663093 1250 883661843 883661873
    0xe040603020f100210062418061407060504060914010207050a060b040e01060311180906070c0c0e0403080406050f091b010320040608090d120b131505210a 68
    0x7055a06480001441340c0075200c1d150081d07e02000146e00c049079603041049007941110706443c2007607482040420900b032183c45030050804001f46000c130710342c0d8949074400300c994041e0300000c100f01505d0281419001490b4003503044543d25411541c00441c03e01c14001e803a22103800802900002c001952400b000300009500c06030050780300c03c0d4400440e482840394100941c001e5280b440980184410042c103036005942c200c0f1802400c105101508100003040765001107207090004201030241480084d100e12603100e4030a5542202c01c000402d5803205e00c0cae0740520701c103c078140443c0c0c9130f0070300381030b12070104480540c81a0f1000724030242c8a48000821602e0729418100052280d859002044100c680c4003041d944080c4001000c101d9140d00c5840b9a0780800140042c00b0320a40124004100140d840c0ca004020790310341c2001c03900b40d52807070840c2c006110380c01d004015a51104641551807003592050b144100c19180744c01000c4582114812007005041020700b070b1141055a4260030a40008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 883664343 1250 883663093 883663097
    0xd02070e0a05060406050405070306090c091a090a08030a0f02070f060516060b15070b0105030604020102030301270216020a0f05010e0d0c0902130306060b0a120e0c1f0e040603020f10 80
    0x90700001b4036071110b1107414050f01145d50f01281060030702c0e0100042c0c40c1c8174004a01001004030701000300c040b40c046548004120703d142e503590b5501c4d070380000f81258042d0704181c1d518040000d4041c00d05401c4a810f401c0d406054098030070080d56040d612606005030706c1aa40481c00411805440c40215450710003080c0c841c0c640003c0c0d40e4425800700d80d501c0e24000001b02d00040001382c0e00e00780041e4020407401044110010000b1340340c9640000d4031ba0006129042006010601000340302003101840350000b2142d130411510365107001151203054410754010780c000d1034007400100e0000e0b540c1c00c80c0ca05a1320180c40340721141d4a0f40e0203100325130071a00c0d025520184604000f18041180c1e000501e02c20701503c02c1c10140034114202031044404952100400500c01c01020a0840d0800340e1660b03000d62107400020a80c0d02e1180c800d00703140354035013071640c000080007404021405502150040d04a40e9a031903c0c04810b50052004840c0c0c1400042d61100104d484010185032068414150003418 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 883665593 1250 883664343 883664351
    0x6030207080901081f1202010e1c0b0a0b1f1d090112080705070b09032b0309020d1a0702150405100b06070602130504050c120a15170f0d02070e0a050604 67
    0xf030038a070300240e4141c10a0320211b95505050040d982c0c841c03160811503c0858140390f10000400e510010003801d120004c4c0088500d000040c1041095840350312080030262500d01c0d082d009504240d000829003a60358080b4441d002040320f6588004060100c64402902c80f4815900300b410380509000c0303842044444507020810704000410500440c001401c3d080103c90700c8510302c0003050704112040c40c581d030411165034032400d8042070f0300c2c1c0030810504540c1800162404c0e140013003030b04400700e5180544440c1e0140c50441100008039502881201c0f41e5003604e07111264000c100b80150819031b8054100c0d440451a4819400a90b10808541d50000c101d02e10305081c0350741e103030140e0b040002080514401e1541c20403203070a080c0030b21075005000d02480c0b032412640140111110740050300d070b40381075507541903400500c010100c0180c0281403014054a0381c4030702da0f5034641d550000e081651520340100714019840b140005542d1094072000e900e86406a0348030025500101401824554440c0e15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 883666843 1250 883665593 883665631
    0x21912090c2301020a0503040501031d0f060406060f06020705090c270102010605090f150f0613051206070512090106050d033914030d061e0603020708090108 69
    0x80c0d01414010110503108004401e201981c030b149031601800c03140d066410926041000900c040704403815a00c0c00d0900003491003041c82c2e440461900584041c0c018032510f001e406411400141f000e128074441d45d400c0c080e907074580840742044002d610642025a10901c424041440e08042081d402071004092034103010103600d4110840a882a030340d02d1900d401c452000140d68280202e50241c00241c419030b106045c41e028006160200130100c0800c100041940c0c00b042d5901b1900640483c4020510b07a1a903003012045003048000b840391034030072000090031074640140807407624411491904d4481c1041c141030345054411000a013074031965540c410011801e0342e00c07110b600950300c2c003c0d503070320aa80c008900c0403801151004034500c1140469800d002c10a03034464041f6584c0781d40103419812940c181c00b1218a90300030110b90407030881c100440803074281e1800d00e92210030012146081c0c0e40f6540c0300b00c02c0d0120702c01c51001401c1c40d54100200c4034554004c1a011350030071500c55040e601040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 883668093 1250 883666843 883666853
    0x5040b15061e0d091410050c030a0905150703150504050606030408460809070b07020f060412020306071110090221030928090504170f1c02191209 64
    0x302c0d0031a00e007410407403005080c0400301b10a0219114a06041165080c9142900d4150100412800006407501032000401c03109000e0030311001e280c050b4590084c01c1a602c0900036040305841210745070130701200050140742900900740600c1f0050200c6145482e00d03129181ca9030b000341d0010300040c01c0140100741600d20810321511052450703640400001955220b84509a0500c030700d6001c0001c9a424008126408642e100071912004d01f0640d0314000d81c4041280c2d40d0b40300036220340c80400410009407480100515400380d81c402ca0a81c1c034550380c3c00d00300b0340f80180402c9c402c1800b41e0068903907502812090f80444003032070004003103590305c02d504200070741302040b04680301c80303207070000304081e10242841a0480e20b841011141106001000003440050551038440e650b01c2a4440c000724041c0300744a00035040c4551b59584044c1d4440c1d004800000503132110a09010103800c40d0168200080c0314401d40d040c07140003000700c0c480328228920071103c054103c4107280001c0d9565003c000011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 883669343 1250 883668093 883668101
    0x109090215040308070c120201021e010f020310032112050a0908070c0603050c120f07050f0c0304060806061204060504111e030c010f02060109150b0d05040b15061e0d 73
    0x140c81190440e984890503e00b40305240c41c04e6010385400740302c85480300c0c0103032b80106800c3c0d242c184076455100c00c1381603640e1103401b41c0034600031243c03040e1000051100075205c15000030f06403405680301d100f80011a1a019013120f005c0700c15140000c404200000c00049550401e6400000d210000315080710151100c1d40c07158021a811280200100402c02802e5054007a203644044103801d89410482910701c05000000300400d105441c0c2401d60014520300d009005490000341603450071500c40025440442e07907a80a40070302e90119035503000244003480c1540842c1c081e11420004040b080e12281e41e250003610002d0421200300611030302c00750043d01d40800148192801210200d80000f0600a0604104020020314100029107407450341c9960000b03034045c1110590000054070001000719107091030029000301020031700000322040c00c2c1c101604001c0c011805000c690502da2180020ba031075090124866030f40010051000406548200c003002c41c040013580102480c0c1120280084111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 883670593 1250 883669343 883669349
    0xc090e16020a0b19050912090415120f0605090705060712020a020418030905090f13080910080a1805061506120117060c1e21010e2d010909021504 64
    0x100403100390480e010740310345c09540c0c1c20140600103081d5204940300418607510620700202d0190391103010349510a5880c52158000b48030486500589110340d02d4502c084900c1840240c440500303040204036500000304900044a0004043c0b618105099540606842910505500b94050a01c142000d80c945002c0c2d131001d00c0d02000b107540100224503000d03100480c250811030144540c0410020601500e07076645c2c0e00000104114400000759240511072481202a2241c01007247c60301401220781010303070f141c000c0185203400d2050b840520140d0701c0440a1301806031403030b0f03c00d5012070b40e103400d88200300041030300c040c05c50391500000e801c514412880a038480008401101012038070500c0900c074103600301e80c0c000c80c403518100344000d502c03408099404a44180d030000146030496610101003035050300c40c0c6009035450540e958100424140700456465140c0102d17030b05640399100000501c0b03100601180c407030010a90801106000410a018040780c2180444c03a00582c0c807104040a0001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 883671843 1250 883670593 883670611
    0x507050d0e030909190c03020708071707080706050f0f09060103032007080303270601090b01030905010c08070807050a05120402190803090f040204050112050c0d06060507060c090e16020a0b 83
    0x148814401024100ca03280c0300c551b420944103020800002d00c051003107c0c0e1058000300d0290f421131420312803070755030300c289000202441d03000643c030401c006054002c1c510480c0303410408036140e0744041c0708101c40442281e0b8440706d60826001440000d00441c100c2501d030b0030344c2e0a1000040c001444031454000c071a007180020740d20110400c81c010054142144800451903d00000d1b03000042050703590780310600460700c0f8070340ca4001400c20b0340d102c0d1340321981464018000348006034500034040c110750400da5080000070500c00010309590302590444000030410764070a4a0440107882406101b5000b0300304903800030b80c0d602c8001d107801404089030040c0241c2c0e0040c6a0301e500e20401c2092007030308000e2080c0241d0050100f0081680c200c40070491005d00d00d04040b03020390340e03a0000000ca00c01c074410721001d81c2c501580800d4056006018048952190300108420300300c0601c15603e8040610501c400700348440005007070f940c1014441e0b01d0001480c0101c654509140d9070300716000c0c80855150302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 883673093 1250 883671843 883671871
    0x122701060f0902131202010c020402210a0c0507032609070f080c010c0602030403030905070f06030e16150527030d080f07300b12010507050d0e030909 66
    0x1420140c011244018078100c0000c52408041602c100300002c8113100307564402d1030b50103c5d031065902401c0481d400c107500030301c115914071710701d03c40614001c00140c00b0038101c801034000034161041407080c41e03100c0382907883e41410060b080d80e045035500d0400391080305181030041c2c060301030800d040041c0e01520a25000c0e04005080c030703404a8003841d10b0b03070225900743d00005460446907082040d20051a81013580942d0f26500d9040642c040c0280500c02800c6200b00b07040001c991000070070b2202a03a59540c1e05000290406644a40e01c580b00c2821403500c0d805008104420000342d8141e000a55181c200b4070700f0440407801c03072200d9080800c42e110341061003440f0b9109914007442440200e01c02da0070500a2801e001294002c202001014402885010a003201d003c0200c1076081c0700c00005602c46241000e031005aa40142c09000da4190203060310030581c4501c01c00c1809540d105400950303d250903e869048020702506c01e0480e130448500003041200c481d512149050303071040200d503200c11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 883674343 1250 883673093 883673099
    0x1080f1308090303070606060f08010522020c3306030303280e1c0201020703080c0904020408030d02071106032e21020907020705090105040c050c03070c0f051512270106 74
    0x242c590010604e82508010070000180721036036650400880e5411400000304040c007070550003374024400c03241031034100e00c1170003103d5441c3c1d4541400000741d42c0c84070345ca441e140007039109501c20b921001d0300c0072a80342c1c0007031000030800c0e20740c080c0400d0783c05550759441c08140b002220b44001c0b21030301001410150000100ba00341002c0c8031b111001258600d100840c500041514000c0c01500c000c1c054001c0e1620000364403410340d940f0b40603600a440c40c101503d03500c182690b0850001e500100c0102e8400e0143c4041c14240e29000055030b1003002d214441c007000c1001c4c584150b006402d0124140b44500b00e280d404182e0411401c40d12580700740c0208420080f1305140100102400014042c00031988402c10500c019191807a07400d04543c0c00f03440c0800c40c01036420055400d4003808645812030300c00480c400c03061114186141e01180d01c01c050860900391500c2c1404100c0c0583c0741c14281c0490200241480c64100c0c1441544c400041c0500b400c0300303c0000742100c41035114480140c1241c1d1213400078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 883675593 1250 883674343 883674347
    0x12092304090c0e1e0f070807180504020f1b030c060c030c071e200a0b0705070b121506030708040219030212010c1701030b1602010b030105042001080f130809030307060606 75
    0xa1031300510176070780902d16481c01c1c040041010030000d25001c00c00c140810a0308000b40c0c450b01050203018010003d546a0b0907091030045c0c1d6170826842c15a415200500350602c100010003110801f8070b960026018076518456440c4459102078240340110404115581c08141604031070303418201030a8050f19484500c8c2800e80310041c072101d00307204400f4a2028a50242e4910510720201d8042007a86600e43c80305060881c2405803a5000700c010003000035001000070100c044041c071441015060416016800051260a000403644600454401e101160151038080e00c409501c1c6080152021490b8032030380420314076031444c10410741681d11528680708458100070202003421400e49000f0b0690316540f5040e40c1c140001d0b2100c1c80740c0040403c0707518524400c0d08030b880d1264015000348100d04251420807000110344650b03a202e01c1112242d099158070400820f8059944005050710586440c603441c0508200788078101c1d0300d041e0800043e10f6030f85080c00600b80c81d42c007400380025168500500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 883676843 1250 883675593 883675651
    0x3a090f0308280c0302120f04050f1b06070819030614030a020a060809160e100e07140a0215101e03080a18080a12092304090c0e 56
    0x2142e415000b07041e451810340a04404505454115080403954404211042e0000e114100c6035001c000b0340c81c1c0c00c0141c1d02c0e00132015280100d2140048a00d0b0b4010511803503120b842c00512000400200c400801844c074042c400307000118081c03050b05207401d10020840131522851503100d0042038a070b030810040c82030b988400c000d08040035405000303407024903030015482082a0003850180804080411b048100400071103e08105580203080c43c9602d0300c000c45000002107030007400340d900307141c4003060814a8403402c500401c0350b503c0b10000c1a6507907030347c2085078200c00754500441c480c481c0407441a01a03100701d50b00404040c80c0c4040d500c0d050100d0b0000501c2d00c0c1a401001452225081002400c81000c5801299070307441c055150182c0401282940702480c1d01c50f5003c0d01c18688510103115509613000300d0040c0d01d8030703004015031350382c2010310700c62501c250703e030214001180c0c0403290b03070500380c0000c01c40034861425511156245d244105540c1400d59130501c0840740c07001c010010000304d140d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 883678093 1250 883676843 883676851
    0x91612020f06030a02071407091d19080d1406130207080a0503100b0309010b040e060709060c05010e070b130609050a03021207030b0c07173a090f0308 66
    0x1404550401960042041c05034880a9140625030000010f00c080e825981507401c42c95011b0a400e40c200c029407807542d620740b41409035008003803603d00142d8031282440c00040e40d01c00c499010704405101e000042c5108200b0080540c0d01301410010b1001c2d0303100341d100f46451017080e0014000c182c142070b0f0038010745055100008202510420001010030511011b5030090856803811655980e140840d626040509922035854084040180921404103420501c10000305640030440441c1941c1d80325030f01d240a461400c08038100c240b05020580c410345403512218041c0300040340070780a80701082d03e042c003182d0042e0307282c00707020940c40f0000c00070210f0400102064a0035028480c148000104044800c0c40700910a41010115185120044c41020300464115821001c2c81c0303051004501142c0c070140048480100003c5441d02c260b180000fa9000012950b0300c2e1010041c02507100345500d0f120f103504180c4007000303021403c1200d145000d02c8010b00d00c184440e034202e00c41490041c2c5000380c090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 883679343 1250 883678093 883678109
    0x60301020a080c13030606062106230d0b10051002150117010f06030c051c050c0d0f150906050f06031c0302040b0708030f07140429030916 61
    0x965099968004841c0380c0100ba080b000c243d4800340c90022241078038543e48006c0480713043c5a0000b40710b035040090203e4003c01c5008412a111154900100f19a9203000307400a03d403040d590740c01001c9240c8200358209202400030710001201da254144005411a00c01100740e08100061110341055075014512400c035000074a0071311004482c0000340941400f0720310500c0d0452607445a45402500140d82828203001c0400405499091882580c8100d000d001e0003000011001a1281507040d10034402503000409483c1181001080001d102c04266090380c0d03144213106000e0200d80c01551068404a80880c0000c0004003490714400751140200542d4218043c10200400f0fa14042034170498840281a048490090b250040d402400350360442410700c1c0e404035a6000304020280214010200d0085848a03a07403445012100078607601c2e44200b140005200410004c04140c0d804058001c0042406444241e55031404490350803c541c41c506070351050702101028803212000d507002d803141c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 883680593 1250 883679343 883679347
    0x50609161409040204022a071e090b030307150509060f190c021006060c1506030f0f030e10020c01080c0a300e030a080c16060b040914011406030102 65
    0x726020860005105116000301a00b1001504569855049910820464040c2e414400711009122040c00440d0a503105620031414080b8101d44021100c1030003a24a121000707285007880310240203449000320041e05032100b0b110500018880c00100e000314084c80c080000d01c0c1c9400c0804c9407030a00c000c1c0141c200e07a2080801e00000021030405e0341500c0890501c086080040f51404901d071000c0f40c8600c80c90103140607404600c00e6030209a00480c180980c0641c15112211203030001100c8082c480107004c000e00104040014250001c1803130554000d00b0403454036142d0002040460501c84103d20040e003044d01d64041941c2c0245040e9004110055520f0912071000c1d406010300c02149254030701804401c40c1402c42c1c202c8880c0e98002648103500901810b02c03081c41c2c1030394175000344500101142d040300c0095207418543e01070f5048040303a00006d101c12009501c42a0040444255803604961a419070b1004200c05114903074100d2205130000401e40f032480324900b110301000d03180f18071076401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 883681843 1250 883680593 883680599
    0x1e031e0a11030105010c050c120a0212030c0a021c060501030c030203010c0e01080612010e160305070605031302090a02090d050303010f050102061302040e210406030b0402070b161b05060916 83
    0x20103041c2d078150b400030f0a1080080c2114203180d8980020700110642c00350b001c064a0b80709440201d0030240712403003030b21601d82050900d02c00315140d0146401d4007a0684c000442000545030824010120140d600c4858070203012985603d415075030241c1040c0d1b51440701500410850800344070310a8041c45034500b40110102000008044100103852544526111000220000000c2d441051841e2240c802c0f203211002d091082e0000e03660364481a01c20303000708280014814095801c4a100d440348060280c0c2e141e00d207078200846c9800103804081c40680c00e100c94001e0740c50b0420107070203240c0610010f5480303614000401a001c0502c0d008541150001401d020500302c80d45e0b2030b050340950440f0041f070589115402c7c00d1505c21001064030301035003a4080601c001b20940020f005681c603680e0140207090000b011300c020713407007403500080c000b007420400924021207040d00494400080c0c50b00b034142a185c1110a80d0760803101d030050b1503907086401881058a0100503025070355001801c8070800502d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 883683093 1250 883681843 883681871
    0x28060f1d0a020a17160e06010206070807050f03190507020703061505010504050915060a090e06120307143909010308030c030402040902100c0c090e030904021e031e0a 73
    0x6440c0c80350b40c10070130350282d01c000507070401d0007412200088000e007502c034181e807011140c21581d02550a58054021400403545c3d640c41446881c3c40b5501c50388036980b400d480302c503400781a548002d10410ac01e41030342c440c00300c1c00803080c01018003c03c6903a00412805056003003400072600000e40340301c624000d4440400503a60040c0a82d0b0488508641c04065950360752425440c1900d005102c0d07520080c00140f106c0b1154101049000f48c81c4049402c0c1059907440c0280b1045ca603008091198075031003404044000b90b24201c2c060102140c0e04251008006440c0d00342001d5440d00000e1031000350664481c4a2201600510625500741101c10700c086505d1900d030714010b880301810400208100100080c20b540b2590095081541d015009170801c011070725004203142d0105c2d2086403240c016440c0020480c02c18002c6000202c041c0d00a035241c920100100f10080d03000340c6114890034404034a20100401c500b02031889840094042d410014100807010b0006500a0503485400e14102c01001601c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 883684343 1250 883683093 883683109
    0x61302010c0503040b0313050c040605060304060905070b030108010f0e06010f061103090d0f05011a0604230409060209010807090b091509041a01030b03030c28060f1d0a02 75
    0x1a020308100a50310901d09020b41103129540100c080c0c00400021703c045040100a1406900d01501c15504240c11000c10041554218828183d00c28802d0010402040e819406200d00c184550704503081150303100d41c228041d0f00241d001164130f0355101c0960f038054000303028203c10800504050042503040207075011030340781e0030700417070040003185c240101c1a114100122083e403c0000c0510b22150710a00d07016890f95894039045402d0f50910000e400b2000000502e01800c0e9002040b10303043c03508201040070000c040c400d10400c00e0414003041161a01c0d5481040b034181d00880c00541c3da0101080090f10200000d000141045200b0508104500f2071a0a4503c001d0302201c5d400c2c2d80c00c40c503140302642c501921039a2503009240c00d40301003030180c80006085c00c181013070702c0c180142501d8804041d1280504001d42884d908440700c076940d600d940280c0440300c1684800380b80700da0507807134175550100d40c5002036450100d035488001000c1d240808025050030a802c800500e00c01001c1da000c0b800303603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 883685593 1250 883684343 883684381
    0xc16030203070312090f08100e0327041e090501050105030a0506010e0604020c0d1d01051c180b040b10050a14040f06080f06040209060d051e0109020a1d070206 70
    0xf6030266000544024801c021740c0006000e00a061064162280070b00d41d100d050500200740170f24234040d0030050080e4048240e481d50401c45500300d844071881403c0d112901c7c16120000d502035038501594003a224182d280b103100a07202c0700002004544d030b00d003403070840e00e043e0001440382e840300340e0700740000700001221419201d034080d03c510540c0300c010105001c1e020340c162102c1c2c68000c408600250325442400d14070303828102c2402011030314405e4019542c43c401c4561900c2c0c60800703a01181680541c0e034100d1000c0b91181101715010b00100d480b403601ca01810f403001c54100032008213020386684849140000361078112850b441d89442c0041038025003200c00d0341280102e840d0010400200d445a003d40010585142691250707041d80010b00e4403041c044408903c1030080c8030100e0b24900780300a40001560b0b000e0000c08c61044400f041e910f00702c43d010000c07020b642d00c0320007900068640490940007000801407000c810544c4140c403001115000b03005d00215071020080120a6100e07070120204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 883686843 1250 883685593 883685603
    0x40e0a11030d110d230703030c14041532030f09060705030105211b010206130506010315150b03041e051b210304050a0603050c0307081504060b0c160302030703 70
    0x1e28103484042d100c40d4070340c80c031780c4404038001041000602d6015000250042030680d1103800c000d450fa41c51065074041d500441d500c00d0b0a2005842a4034081c1081042c0104074808042c02060280c40c4140301400028a0305a210400b00511880c070900c0b1a1b429000f03144007029190a00c0d007000c1c01892400148105c910601c440302034000c1701526584c40c2410200e4140580e942d202c0d03968900901203101c82046030041c891040040e1010b0322115000ba1030030b034400003078034071a4030b141c0310010404005246642c003180c1e41d83c0c81d030160814106102c001410005100742d02c0349498245584000010344600ca019107102000d640000c101180c0194544040e41c444180c0704045004219003c1c840c08101c80103400701c03504404068030000c00340045440459146d100e00391110030480540740f003a10015480c0d2400e00c017180d03095003d14038965000c1c00d03007906481c90100140004003500c3d000c2d071244220080000d0012039580060108144184008031541307209455071b80880e503030310359038030010386 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 883688093 1250 883686843 883686857
    0x30f05031b071103010f1d060405100c02031603030b09010605090f041a2e02030a08010b16020d1a0109150b0a05090d08031e160e040e0a11030d110d 65
    0x402c110001946000c040f00140003000480c4104408034004c156818021460070314606048006040c0003800921407a0b10402174208800f41c14101405442e90a21400a502050003c001c80710108000340c00700900030358001c40c181d100c1c001807128540c0c0681004081000030030440c40d154a90b030804101140054500258802e4542c180c4030a8461005146900c018407140c0100c20680320315070316050b10901c039207008500c2c86c10700d8241d90302d20400103020003041240740100a02c0841c030380039110911444040400d0040716a00003455940300000494490398100d20f040100900000e02c64050450503c0410854807811800020302c0343e030f4843c4003845400081d088243c0e0340f05106549001c40058421381c40c1c1c5400744bc110880d5002283c4003008040e0100300405000c80c02c5a06c40d0107001c40b0300803111b40400d1043e00b143d144188682d0290400e80301d40d21846094010014142814000c000758540019100c08050030404100c14481c00c001d0696a404801d05011900c1d04032021513044c10a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 883689343 1250 883688093 883688107
    0x30206070b091e010f06140a09230403050a090f05032503060504080319061a0919080309010e030309212d01050610141e0313030f05031b 60
    0x43c540550541d4012107100d1007440c0070040041508018145411a01c041c0005510790600f07134050020340800300c3d80714014000400100764541d100c042584035009540a51151001c065560144256011000941c000490091840d4001c461070040c10000750a020440d140c200002d0341c0300b08031071200b02100220f903a07803000040c4144810005580c420b10610882c81c2600303160300340d60030032036001d4611341301c04c1e58081b01d2502511a0100707607203850418102005000042c961581c20000390360350042d10040b624400318840c200c02100608181c0e006680c0d503002072000411904003880103034000d41c170038001c40603195a501c4154a2041c580074200c071643c3e0103000300e185060112080c900d0940b090840c1e00c41180c910305041c034400c10004009200703540b07900b003c2c800c2c003620707020603100082d50124001d2940f1038104020042d9102101e4108442d00310301c50340203d40d500540d01021310040c0391000d003041503004504503055080c80e00340036007075182920790544609007060351b0800c1000001000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 883690593 1250 883689343 883689361
    0x313020906101e1b0c0509180607030e01020c150907051e01050c10140a0509150606030903090405090d11030313030c0602070b13110402090f0906010c1a070e0a030206070b 75
    0x250703240b04500d0140004c040c00c44e0810855213407240c01620b010300d0512001070301003804030002460f8404040000c0005a0721002c04800800000340e15060b255002c102c2c541c00803400700220cd2000b103a580312030002e0304203d00351a241411690201b4000c02c1c0146c1d81044800301c400b200b0000c0402800c1140e610103040b41c110382001c1e458022108000d03e02841500900700c0301080600c80c440300ca108211075201c420320700f66242c044c0704e0956504c10305040042c00d18144880907641002c41002103d01301404040014140c40c012240c02c160380c1d00108080340c442d9444284100c00c95540400345155081c0681c1c00404101c9420000d4144101e0a03030321801c010069044401c11500442d48041b2410004018464481c41d020241e91001c402c2460303225614007442103409090004100414105801c03052207400030008003a14140210b000085001c43e88951590342040020f4040c041e4505d410781c0058a98078892088038001d01102c5018001a25500c0032155070603001640d13015550f8841c800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 883691843 1250 883690593 883690607
    0x9090e0a0f0c08030d0b0939092e112815020901231b1504080c0601090c08010e2806180207030c0f0f080313020906101e 53
    0x4011040e220009175050003030113613800030200790012191407101c5d40324040000700340e294021074031070000301038607500f2020f01c03a070301c201440c0110740d200d014101140b140000720300d00124040c034209180900480c0103090b090300300c100e02a096a0816028448800036200d644003003458034142c05c451001046122421200e25000c07040c0d03400400310f009005000d41c5203010b9001028880d003c200c5001e80403010006188014404c141e0b01d4440c241020101d18009000e50b02c0740101c8019406543c00402020340c4e48440144124024070410744d0340c04c11a00014078000d41640882c200510705010801c0490f0f01000040c1100c1840141a4480c0c81d4864040868440e15a1840004818203401404a80c25030410030403108080380032184011280c0c48807080c2d220784280180002d4040c030f25000055040205103921303a004080c68a400c11990340c5004043e4025128203540049a0420404614210250903030000c1c0541c0c100740484002c1101614000824028040c0c14081c0521001060300c60b034a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 883693093 1250 883691843 883691849
    0x100b0915070b180f0d141312050606090a05060d020d15090506010f0f3609080d06090c0806060a0e13050103050106080307051005070509040e06010609090e0a0f0c 71
    0x1002d05501e0901d042400a1804003807030342405402611824080e10b0008240000070b04015103640d083c80d207110416054940c403218601c4000b50386440049000e800c034032005a4441e10550003040c2c00c0c100700e820010803950092001c40d20301c0c140702c10015203444000c2041800c1398181c07400c00c0e0220003803034000102c0000390401c1d106107141c03800d688140716000131018100c2d4080d00314804500d8a0b605c02884140890184480c00c01280c00403058100140420f43e0a440c0e28529020f6141c0613007a0b0082030f110224010740f9550004903c04040758464803681c0001c1c0700480e01048034400c15403000d400c0e850010000c610170390300031550362000c50003040507440310000103020001000211000034002c000a010640b140d40c41c120700411042c0c400407c807801c003a0400300420340180303a0b80c3ca0202038200104020204a0300740702d0750801e40c440d4090f104250640d0005000c05604281005040710845e1f80420740760307402d2604882d1807080100f000b0140c26000b80d46c0360590569810501d16206040d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 883694343 1250 883693093 883693103
    0xa050711031b011103180904020a1a0304110a0e0a0b040219051815030c1c02040902120601031817120709030314090a0b0c0c1002010204060206100b091507 68
    0x50140a01071940901d814605030007600d40728a00004e1a0181d0703078900500005440c803402c5d0f07a506620618040180c6644a0b03c0200b5010b0015190211403003002050717038050427862008418002000a003401640d0f0580090b650000c02c07a1400f440341d105d6000c040c1080203001c4e69400310b0006502c0d41e070100e640c40005526004058200c0900c0182581e03c940042040240e000303201800350701d41546291480340c10348400d030b4110b072140210f0f41e442d503224080004000d14048014480000720f8005000144102d840c0140c40b071408680d5800602c0700182194101443c207000c0a10fa242400c10f03421066800c4035030480001c03840c1048807407d01c2014070048012541b241041646540004083c056a110741e03140e2a071030701409014a00d5001d842021503000c16586418490840c00c500507211104044044540401da180c0108601c1c21441489800617500040c00344606501082140c0c2c000c076100907814441d0f840d15000b000c090107101c003658810050000d130030940d17010040036100340c25049 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 883695593 1250 883694343 883694353
    0x504031701080a0b0a3602031914070501051615240f05010804111c12090f18050402031203010f1502010b0a06110a050f010614030a080a05071103 64
    0x592040e0341d0307900030180c2201c0c0e43c0c03141c4000682c1c000031030250b001e480c140b507110f95000e40c008070744040c40070025102d013000c1c44400d003a440015039002c0181449c0c9448002c0e21451180c2c0c0303400d00d40e90180a50645400359800444100b04507648881120b8216036003035003110301d40c07100c0d01d004075040506800010959040814078043c03d5a00c119680d0f1010b00003060010b0f40350b031000c020755810464800c05002c036021800081c04582c10088440d50200020400e201d42c00500007905071024060105503850303844002c0d81c142030707500100c05c000a40b10700c000c550a0a46040400c000040030f41001d29072031529000442c0454408002090b0001410041c0540365a183c8000d0b1607005420b00c141000e070b050400044c4483c0380103220b100c0340804090704000a0a0800ca026188243c0c200a103284500c10070081102044050010600c1d0400d258000b05170145081c071300e949a0246c08681c24130a0700a01c4082c80058845011079001100c14201030361100700f642001c005808007160381581502071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 883696843 1250 883695593 883695599
    0x613110301060327030305130605180c0d02030a0204151502010213060305070c060b1f030f110a0503072d0206040b1b2718070f03020a0f030504031701 66
    0x420245041e210300740e80030050300041100707614401081c5003030240700c4d0000202c10b001107842600141e0f031103c1d111400011050725555000201d91080f01c4840038018040742040c0010402d00410321545411a580a412101c640003c1d4850019450080c4260341e00c80300c0b40200035812034800d0040500400e00c0c44c0300745019034068080c0d40100c800c1c028850b42101c000c0740b514068841d090044002c2d0b03881484400a03a41c6420051442c5c1071516844505805c23010500c480f52003813640c011016986c08243c54841d2003081094401103860410429014084401e6070765110082d40d51018040c9443c030003003640c00035510422601200c4211805c0f000515910b40c460300002c500b4012445900008a00e548181c0e40c9a508103186401c0003078050100401e18500c1072900c0d038030b28070000013816100c04040d8030740014806040a034078034500c040d104003045006501320600300000011030509600e80b440f40480109000380350352020061592b01c070b01180c141807050a11b404e203046082480f00c010b5031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 883698093 1250 883696843 883696871
    0x10080a06051c140d050307050703020106150e0301050c0424030b130504050d09080c12120c0d1403130b0c090406030318050102070305030a0302030c070b1005150c12030613 75
    0x700050250342010142c40e9003c800040000d0740c1d500d01c12181d079207a0840e01c07000e004503002d500486054007151b485440200e4a0710388071040c100f581cac031580c440141d040240010b050170740e80700030080f0702d003520280401c01440554900015041c0441010318001e1000b5040a900520303000c10b025802c105031303100305601800c180e405540582d000700e04890589803104401c48030b00c4114000d955803900800c072480710764104a06481014940d10040d101032419402c2c54100382c0c0c020b000ca03407540c1d600810f050a80150001c42c200008800a0551855841c14a200101040d0807510007005642640c0010300f920110b0426604d0a0740c00400501c82c896807810005c1500b417a82e809080a144444e60004480d03000140700400c40360305c02c01035400e00003e850306400030340000748210110380b000c100d004005860151803e1141201c44e602c1e64030349003860188680790040796166444403400700181c0c0c03450f41001802241403000c64031080d65955500340418241d004071000261281e052007a0206001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 883699343 1250 883698093 883698139
    0x40b0708070c1403071a250b060102060c070b04170d090c0b09030a15060305071e091404020405090f010e060f07081608040302120301060f030506030102040510080a0605 74
    0x203000300c09200c2c00701e0703e61010301e10003521810219850760003a042080807020035907441620300400918281000703907103400038500d55944445a1900c6000d000d41d1010800c1c3c0e020b42e56003060003880148010700d4940100800b601c03600902405540f01c101c0003400b003201a002a421205a10030b1181d104c80013009000082c00c00c064044030890a0488085100e141d41015511460b10040041c6181155600c900500d50701844280301080d071a01000700200d8820420100140207142644041e1200d142000c0824685d0740c00121003681085000349035000320141079034001e0340440d000503658035000b811a1406890030000714007542802840010540041030346071243d00e00303502503902540d8080049a007460b00701d603c2c2031840d041550070f822041c441c0046552252280c0115111710900030000318050300b099000700f0020740050120707440b0390b505006d41e54100e0400d900035810316003000c000814001c008012402044003030f20008510a04a402075401064081d11011010f401020512004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 883700593 1250 883699343 883699357
    0x80304140303130b18100507020409020a2706050109030c050105030a090611040501020c030607230705030304060608010b0d050c0f0a150801080f0a030212030402010c0506090606040f0209030c0f06040b0708 90
    0x1000210030f2441d1400c02d401e1b41018041166500c52402c085c5508101c000d020280050341c004d2940745010404c503071083c1344030440700041e855285112819080d0781c07050340e50750b4010504010119404000044040c2d0000064170024201a51207540e05940c460013000c0b481c001614a50404240d00d41028800d030080013030f11800e03800d8078010005c9909156407480250741400006a811601d800e100381c040c6c0700d280c40d56180b41c901c5854080240c64045c80c540065a044e03510543c1d0380801c0200c00000d1040504064041c4e901c0225010191281e948641070b400344503000d1003c03440711080310303503030400d8a1018040004c075803000c41b00310400c001c2003448240030381100c0e403040c41c91400201e88001641c540c0564154020030280350341860003a0190005401241030248280c800da00182041c003490b4402d40141c0000c2842c1e00e0980c0c10042501e00d0002d40e5124a481041140010b84000c070701010f00b09415a550100400944003151542c411507215181c0f0150219800c030400107104002c0c418 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 883701843 1250 883700593 883700617
    0xb0c18130c0906080f040b180d170612151801061203030b060f07020d08091f08011d0105040c0216060207060909020a081303021c020f060c04080304140303130b 70
    0x40c243d103690080d03c0c1c2c0c11040d10241c3c6550034003000500011420601c09900c2160140b0303403000040445e44440c9400071f0048441c0c0480c1c0c3c0c801d050310002c4122514150306c108111401f030090354424014a481d405d00202c04c83d100c2401c1030001d08501c8200c0140040e54400c07000810900c0c1d9203210f00c4100070030140003140002d0510449420914102081d58880e443c120348943c0f42c0a0b20707a08021080b0800417044802c00b6007440351071070580e6030f0400713034076484408400c400e6001d000220040910005070005103481c0b44c1d2507036248421000007802d42c1511350590700002ca4510889042e8a0060345203280100101a9000802c40c2503011907600105d1780f458484850f02c98651050b5030681c001d9404240005d150300000500b1a1080020350400a00a00690741c06c0c03002c49056054003440700700720502503401143c0501800384200b01c0c5d95402514014094281800c03c3e0aa60b200d1060b0321844140c01182c4040000f035550a1003140c4084104408032182540c2d00c031120b2036150002010000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 883703093 1250 883701843 883701857
    0xc0f16020415180501080703020604271b11060910050414010905030a0807030c0c02010e12010e0c0f060301271103070f1206050603060111150f180a0b0c18130c 70
    0x446d41400039555080e00d40c011300b00b0f400c2c5400e2641d40d00c00d40301030814084e06c44007100d005009140c010320030046041e142e4502c5c0c0103442002040908a07a50206100a09500070f008100c40c00d900480d80260200100b000480c8580b103504001d0b0601c074255004507410b501c0c1500343d00c10898000002c095401e45c9480b0580c1960310f016040d800c0300c040800c46000305540030003400c0190702c92000c1c1600c1a0000f0f00100321020401c50340307030071215816080d015583c0298428411340c6004107000c00d40c56006c90b466071031036042002c0580654000c400d445c69000e0700c4c000200f10900795401c04900d25505624054891401c00c100424450307200d0791203008911440344008070350040b4050300003681c0000e03000ea8034540b116401112405400b421070183d9005110f11180384400d54400c20340286000c11703550407103062500420700c00c0ca079a8022480c00c1d074404607038200051014880e0310f51000309400f8890b02d5860010314100755090002440ba48410243c181c6d07001400141d0200c204481c40340c1d80d0780 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 883704343 1250 883703093 883703099
    0xb01141206091f06030203071b0b0901180203070608091507090f05030a23010f02070605062b060221090a05010c05120c09030f060a0f050c0f16020415180501 69
    0x2070715004001560700310f0502c0c90703541030165074003a400560b0000510b1901c110b10f115912404044003208280844007000701c03405001d100c81d003d00840c2c085003214445c1c40d600c00102d45c0080e617200c0362482600140124070000400c0e0325000d001c441d122040030311128a891903c0f40000f03080d070303071140034000c0720341c4404402007941e080005000c41d116620000c0c04103640342c00d0200000b07106140b580f03501c8641d00d51020703d0440e940750018100045c80b480e000301d1141449020006861201c440700442c04144100603100200e134413030218422900000300607035520300140a00202e06201d40910001c1c48020300b404050b210000f400d0381280c1c00360000300302807446031004503164401d81c00b41c510640c204e076000c262094001030090602000003012941030000e90106141000001c03a52405020360b2aa003a403100c4081e4020300c2c1c0e004a00e030300007508c0c01c81003111400b41402420740c1410711300d61245005046407a2544102c004602d01c0b843c9208466881d1a60300641d80700d14000000c00b41080000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 883705593 1250 883704343 883704361
    0x31808030420240c0a03091502030a05030703050a090b041202060c09010212030624040618060c030e0a09020d0b01170106140304080d15050415030804090b0114120609 73
    0x3038040030000510b2601055400d109000703d9072030703814681d850480d040110010440041020303000881c4291a4a03a5072440c1901985404070f0100c502c03000d54004001140c28140d00604480d40b012241c100000c0c962102605c1e6002040c4980004085401201c144028480d001180854045a507800c0f01d442c1d41c5c40f84941c4e82d0340c1c01556500ca0159102a0540c2e0740d5901d003001440e0b00481c060151282c2403000c0701410b4800f00a43e14032a1903610000702071113a40e41c00300a0031201034040208004852510a0040204070043c1f009000c20013440c51000141d510102c400000f05601101591162507100c40c080c000c014803135465000c0344980d02041d0368452001d009034121341e025120440a0624140c0005241e8001803003112002c004100d4800301400070b11030b60841c80c0d00c2ca00b803040220705040902049500061080d441c0142c0c100c01000060306810480303003521440d080206c0c03040d803d0801030b0340c0c80000d180e90b2652000e010407040e42612500280501c21071b421a409800c44e1606651 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 883706843 1250 883705593 883705643
    0x90803011e0f050607052a100201050106080621071512090b07030230010f06030203151003020f03250807020c10090302190303020705040606020a0b070318080304 71
    0x42d01140c01c402d010b0030811803424070040c0100c180604150780303215110a000e1032030420f41200c07903d04000108844115030034800c2c0246845155030000300460b506007a0090148880108103520402030b1102c000345042012a0f04905000d0f60421610b41365210500d00051550b110144400079881010784210414240903403109076400c14200c05154440f08003c5001c0c2d070041c100c1640300c8034030f0203092911640e103122130340441d140500100060f505140c0100c16110103548107100305401071051180030303240d254401c00c1d4000e0131103180011510428054019002c0c0c0b803480d07540c1d501d0100030400452148001d02000c1d4a042c075a104041c202100207840180041d20700a0043c1d2058025400c0c030b041c00da803454840411030401044250351380c0d00082c1d84403408421003802100c001410810181c04000310b03806800111404d00103203041100c025901c40ea000c2010304003090560200304203d010f64085600b911001120080115080c10940550345c001e442c100c501040020300c03a1503406080714 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 883708093 1250 883706843 883706849
    0x5071412010308160203191a0708060d1b06020c0f010c050d0c1a010803070b090d020a17040b070f11040603020a090207031e11010b10050a120b0301090803011e 70
    0x10006a060b420342c0c58400c15500129454202c0d1075401c90400c000d81d604020321000010f101c0488100602139181c201255181401c1543c1501d4014051110307203600200c42c0c0d5405030064400110f0f90207507040845d0419501c4507100040c0000d070101040e5680e002c03413049a80041640c64400b000c100a0045030389100340903000d02903810501d1003d440500c9024100c6405000d1003a8880408030309080340000c03182131b4040f59240e440040c4030010006030010442e484400c2901405c000100c215000c0d4441501680003807000c156000c060b0071811503041505c002d0501c2184c0f184d220b104c24907154000060001c000d5070300d4504450805d10b00e00c1c05c0e00440040c1d80d40900301504803403500f0110000b035000384104030b062007100220413000c1100d45201b118442295692004034001c0d404103507007104e00c600b032894090003081b01e001e85c8032a0042c0843d42010010f01c0e00d4010809890420360082c00010002507041d401c000c044000d20101c41c02443c140e0788800c9001d1a00289010214000c11180c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 883709343 1250 883708093 883708117
    0x901020a1b082a010c0f0b161b0510090804171f05070903150e0604290411060c0703241407170a060b120709061b0b0424050714 56
    0x2500684107505c1040518030640c8074400710042580b0a50f6200c202000c1112009140d40104e081c18503072941c004482220401031080d500d4608030141c881070f071100050042e402943c0e4a5086500c02c000401e02103034000d00ca24610050b0002080d0481d40d104c2010400f44030903141855850440300030135110f2070303024104a865215400349541d64159120440c440e42022007641c0b210b0130380e8401c9040c07120754401c1d0f10a05880213060051513414075900000720f02a0b0044411500f0000041c07100400310141c1041141e000703450b01c032011851450400c2c03a400040503036034104410100d4102d1030b481c1c8100004100b0342403110401410043d89044401c692401c0042c61851500540081c5000e01c250460010203010541d1919100c2400907988111165007100c5248401c1000165110483c100640460301e45980300c3c0c260300040400500c0342c2d82001e804941823002050400001d000c042c20a541551820f44903031154461881c002c0500b200c41c2800724840c1101002d04145020031910045800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 883710593 1250 883709343 883709413
    0x1091505070f080f0403200d1d0108010b0c160b070203010612050c04200a1805090403080a1e110706060503060112080d020904060b0403170316050901020a1b08 70
    0x250324030341554440074005a061003c1103481c11502c0350016400004125844000c18808c00039102c01002000c210300e1344409410b40fa1100c0c0016a800442581110340c401861602c400360341880303608102c0ca014125a50900f0303000000b42844100e0b01904010340210300801207542d03181d024040005240c00010310a410210004e5a140f501d0b500c68211429160032034600703081e07400b02000d41648040015004520b01449100c00411781c915000c024040984002c800b60070940e401902010002d00170070b40c01d5440c0d0640c0100041603407107144000034600f01c14025810710110301e2059034000c0f103041c2e5090307080640204050070001100e5040b16034040f1486200381c3c00381c4031180325401004000800359000c01c0038849555a5000f0300740504101802199142e00c0c5161410b140003030040301034281c1c4400d10030000d41012065108807001c00904190b81da40c001200100d0810701034a20052180c2106c4411042e081c81c0e5001389000d49085000701c40900441001c0041510f0402c904254901d1203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 883711843 1250 883710593 883710601
    0x30405090a1a030111120a11030105060d02070204090c03141b010e0d051516020706120515040e01020306012a02190b040902030f011d010303080c0c01091505070f08 72
    0x1c0da01841c445114000b000d640c1c9009803000900f52001981c8040c160350011500041c41242d00c49142c2d0045525070341000400781440f4035105034001485020b1041c50301040705801082c1580442c1e06040e1300420400400c143c5141c60300342d80d515400261502e02c4000300342c1845105c006640d0710b010340781e1650b01c00c03a009074000441d8002280c0440c1500086441500e4000074000c219000a4288007a80010945044220b402c4c10180940158045501004c02040703016000314004102d10340040c004a9595110b40580d5855900c251825130054945040c000340c40e181940507500404090341c901a01c0d06800d1440803036030010b00110717800212003003da00014541200011648221600b1407891a13541c0c5180d481103402540c0f140043c5a000001c10102075035449056001d455030758404403101c01c10240c5040704000500006007800000004603203c6081c01c02a00c46a84040000f40082e500ca480c0000c0c1960780002810007550500002c01c14403401804030398020381d51560703161a0390703035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 883713093 1250 883711843 883711861
    0x1021e151939080103110a03080f1b0d0c0210111b090105240703140a09030c050a08060f1807080c0301050a05040b0a090807020402031305070602120d11090603010608040c0803040509 80
    0x11b820510796800001ca004c0000041c2505021b05045081071540d1a2156504840c491b610340340a60140c0700340c2c21044032041419007020b099900150182c42800741d50000070307020740341c46613040448001c2e0312440e410b105c03003245265090262070310300f9111204541d070382d40c0a2000707041815040c103842d400c0f20030076000302250260113001014042c1c98401c040041c5039480340c260fa0b200e0b07480400019050309050091007040782042c0300030701e8156000c180c02c9261024164440e0809418400c8691141c400704901c4c080c0407842883c102f0360300302500c049640e41d894241ea20444c13006800c0c000e500700000610309607106d1141c01e10460700590f00780c07010303940d5a01800082880301821900d0140034461703000540c440e8405584079028004005008000c60b091991600c00710744c1c42041154071032081c800c890503042040d2140d140e841c650110b41070095104001040c007502070507642111001c000002c01036804800c80340107034040c100c038580032074036808030300c2d00e07882240242c40d04401e0880110b66000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 883714343 1250 883713093 883713113
    0x50d0305070507030206030408120f061305100b030903040e09010513020105070501061206020c06093f0a05540301090b0601021e151939080103 63
    0x40c0c4107038262a419034503030317001501540060790162042800415050302000e1104511600140803443d0000d00d451b0980002b020034080390071000080b6164004030381d400c1142042c40c40030304404401c0c19100c1c6018800c2c69900c0d001880b501c410401c409012a91020b018031a03036010384402840030110305d60700e4005480c1d030350010004a45070b40d48e44000248200b80303031400c0a000791203104056907681c0c420342c1d02c61601d00050702c4c0744125005101e00e001580740c03e950a1910300701c004110b1b400b24507105c40082d0020034034881d0000c1c990000aa0b5050750707038094010080d0032003446190610698800c0c100c0b0391244d5805402c0100308441d01d0841c68504107d10a5050008282d1401d283c482c140000c24256480f940c000c80d00f41c40c0b044248000d07982c06010009035400031140090302c00384d0380c000c0543d8624050500318681d20034000814154100311102d05058241c603031040c03204665041040d5030b40001440491818202e844072268480301c0e4a010a04808275999810f00503400c0d40c0702c4580d61 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 883715593 1250 883714343 883714357
    0xd0512070317010801090201030e030a0c06050c1b06010e0108150106031503120806131112060f0d03021c0f020d031a040e10061a030a0507050d2c07050d0305 69
    0x2220828032616100c8400041c2d00c0c1c0681070060020924010a00c00074003078445401c0071000c19002800110605980190b10041007504511301003101e403200c00e803008240c459202c2e07c1d6000003280751540c00c44e40001541c3e504884042102880076a0b88840913a21150385841000f82140c40308010415107120b90401180da01c4802d2030003074096a250748100692007200e0a113400305813240c0c1000840e2609101402511800d55420b0040c06000203104186d84120401c40811600070b40c0810400d46500300142c031034000103404865807154905000c0d55488049003040d0318a4801d0500c551a03610403e41c0c03a040711010340040038800ea5066055014080c50b403100c280142501c10100711940d924000d01c145006924003030304005403034855030400e590b19038110603040c0211700c441801c00e146200440f0f512403071510740040c080c2c6440f00b040302d50f4491400042501420304004803d486003e84000d41515403403d0141e507a00342104026171074103014446e00354070600700b840100c04a8001c20040c10781c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 883716843 1250 883715593 883715597
    0x90c03040317090a0312020a02190c0f0e0a060501050901092304020d0609050a02070209060603070c080a09050306070f08010b0c070312020604020a1e0303050f090a0905070306050d05120703 83
    0x150741c1401540b910103420031201c1e500729501501c01902491b400c102c040304402c000c07070402d51600ca1061800f9641d007680d00d0040311496100301411050026070301c0d003107000c1d00780c404100044542c1d803200717003800540139940c15000c1443c0020010345907025a04545906006841d107500603841c100050754002001801030602e40480c0300c0d81025a500e0b48011b00c0b02001032040040c0c03003030901400c0c8003243c100604100000b0310402801c00966204404640d00240031200c0340d03a00c1c0d5982c01304592006000c50001c000c1c91020030403207020358219004400340c601c03e0f82207800c2965106800c40e171484d00c11001c1400b042000c00188071084030030b0002c4c0141c13030030a8101c0d101aa920741d100c01d4585404410341006800003401d010840c45c218140c0401000301440d40c100440b84440c0d0180580c8031b07403000030288000040c5114018147d6401c0e104040300c018040510290746094204c00b90a044800f0000285000f60204441c83c200c00d24204081d0880e0080040c16440b02e0080085d600c54841601 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 883718093 1250 883716843 883716857
    0xb0a060c1709120d021b01090806181e06040b06010518060c0f161707080c090604060b0c0105152202160c0f24051e09060708090f0105030105090c030403 67
    0x40e41d02040802d10484c51075008000b4284808445440d2056540c0920704000c2164000c0212520010745181c0020311001030313072601421aa0032070300e071a25a81e0f40100425800e09050a9684081441c51141c0e002e180904419603440e801105d0511070b2801240038040b00140c002c810307080c0039001e85081040300d030896184183c003c000a1174010a4000c0000101c0148000d1001d043c450304da05030722005000046c12514100510b8584400b00300f10120301600300c40780000c4036683c032a0482c800915141c00d1203541c0b0044150014041c1c0401c4030304040c2051801500c141504052900c0c0c0038002e2503251100841c11104080c8003e50b00461010000b10100c007040e038007040b030801802c1d0040c000f010b50032541d945821445180c62202e14110304404000048004841e03800400700d400424610203110601a182d6002c604240901001c582c0c01940c0416080108100308000f4129094110f540e070b41040e210000460b4184824041c0350380014400c00840d462881c010b005d103800c1446420202 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 883719343 1250 883718093 883718119
    0x7170601052104060b03030c0d0c03021504080c0628021b2d01050103020a0302010e040e1b0a090e0d2001090807030e010905030601050114040f090b0a060c1709 70
    0x41c0e800b01040b550b41c0c00703598012090000304007003441911051001074002d5801c01c80841e241c42d8039071003150200002d00c100c440202c001c05100b4461b00c100c40203107410410141c01d050600a1060304400e5440000703100d40804100030304000c4a80300c42ca0070440b0f01400c45000c814003030002035000301c01161060f48001c0c0c510070b1104000e0040007860712007620300041403c600d40000048075a0b201680f841c1e40d01d0500144056124100e0300703c190394082c00c1024044010901150003841034604902060207000324400c1d1136003009440c2441400120364820030651a00d0307001049446100b12107030503034000c50310a0092405030120440d0f2000740c20720648039100e10100c280c2507a1426208031990180040c40c0000c0581000440d64065802c0ca170000100d418007012a540340410300038281030000e1080403101e801c119004440180030410030340501b0954446145000d00000b800b0144141c41d140c0c80071030703254402d10b0302c40072054024030b4080758201c0303520b041102070b801161a60740150101040b8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 883720593 1250 883719343 883719367
    0xc011e050c1c080708011202150f091201051b1c1104080102030c120903030702061b040302030a1401051f051905030313090f0e0a231e010f02030717060105 68
    0x107600c0c020303141c3e03d0700711242c030b08040000c000000c160045d00b0b042100c0002e100c05a1a507110441c0038144109280e0303520791030001004014007a62840950094070a0f6048002c041d0640000d4003940903200800c031340e0a80742c00500c8450040806090b800d03001d81041320f040608a420000250b20344144842c1f51a0300c4899443c00d991007103d4554603603000041c600b078990590720845034001d0503103000d0750950030000402501d604002c0c090f41c22411a440c00010500703c0c49041ba8000c550040c00c4405400841c80c18851411941544220365483e000c0046c1d4900d036800307400d5810f800c844840c080b045041c03900300228046042d000d007107610200d04000c6000d45040004221070036000c101c1c440981c0c0392020540a80f030300c0340700300c010290800a450490040010f1841041e541c0100c1c0400751440c00000c04091000e41c41c2d001d10680b017040208039100345030050410f2200c3c0240004e01022458032400d40580c48144d41020000d85454004141d0a5a94807a943c1007041450298540f88a500b04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 883721843 1250 883720593 883720633
    0x11e1503120509010206222a03060614010c0309150201020d2f0903150612030f03070201140f070c1b260c0604120609020607080702030c011e050c 64
    0x70040030501c0001c88409940e0100041d552000d04d0003101c0081c000c0507042050201900c8600900364500141c1c0e41c00c4101480c10b25441c0211001c00b03040655a4900303018001d0402403190440740181d21442d001107500c0344800405035505511074a0f0b0032854061420030207810964510b045543c00e111400415106000702c14000420303c003041500f02c0c1c10035128072112400c01220300420020400e0341c48645012800601e40548400618400d41d1010085140880a00e00c00711007400006645008103000c076001d140140440e5000b00440300d9140c21405001c90141e51032500d44480e030000503c111710400c0c42c0b070340e40c80c45852045010708610000b5130356640e040d005044c0103221410402402c95070241c0d01d154070800f200c000d0251070180c40100d052403180f40180c8442004448450040c417200b9040740d80110381c0584066603801792810501066003042d034003203201340201c03240c8000641c4111007040021015601d49001e40c440008103a4995000a04070300301402540c020700e0b80382246549d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 883723093 1250 883721843 883721873
    0x6160e090f040b061f050705031303060207140307080414040f1b02010c0503060906100c05100204090b0d030e1009030c0825080d0302071a190e011e1503 67
    0x104407010781410b1910500500004100c2d6003e0f0451007901c0c44900301124a4500c0c00080c2d013801617480b0200e080c41c1d4114401e151143e224420041400410889550b0007080710600401040055464060b07449850380725603140039000720070500051180400c0c141240001820003040003500c3e0700c99084400a591840803009540d210058910b85069028000c0b40240321046c40e180b840c504c0e22200040c0f0050000e00700a0060720320803644e080a81c000d10b04482c080c0d80000c02c4079404520413883c40040e612a001321403000c1d0814200d241c660400c0ca5540001a50607110b80c3d8000c45800c081c400607c41c02000341c42040b210440c0000403e0429000001801c840400b4080f0314680320040400c1103201d410040c0d4003048100104061440814031940c07007a0a45000740e502e811904142c541d030a030780e910000704c0002d0b80003400600707400e802c0e4036200040068401e000c404200580203088482032286803100015849211100000340c1e801716050b48007407440448403c1d1030b6111701e01d0009402d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 883724343 1250 883723093 883723111
    0x20f04090905010f0b181b0f0f0304021e18150a03081809060d0609060b130c0e041e0510150504211703060f042f0c06160e09 55
    0x4800860325101409007110ba10025540550344400c00000c82c03106d1400184200b500e00ba25800300c0c80d80070066011190100f801c0798080d40c81d541d0101c104c42c1c0c0c690050710128803c071221184211907100c0c100d010254842c0c0140011a2014a15190202110000c041000d000020b4000700700b00e41d039240400c00030718060b4042d20340301c42000181c1145c0c401940001403040c0000d04c10070100c0c1e604da4948400c102d6000c840820500711510301100549100d0b540c680c1d004500306207482c69076034140d000c00d031010400d039203150040c40010184401c42c0c01c01c0702c2d121800c40d03004444d644e010a5903000550030600036503443e00420b5591015005d40b03082ca1f5070083c00160001802c10054020820341d01d0440b010400290301c00005985d07050369500c0d40344601c1c20810010001410715600c609910143c9a00a402031144200028001c8000c1c0ba071117440e41b901e8080076252451900500040d80c1d12001d00b14014445074032100d1100700f5000f0380801100070001150003115880c0c84159000c2e000701c080c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 883725593 1250 883724343 883724351
    0x9010303171915032307180f06030f150e0304050f01111603050f0d050d0f09020d141e0d0513030819091403070521060108101b080a020f0409090501 65
    0xd454511404480c81d2000610300c10f068031091405c0a003c284103085460001600780c601014101d442c0c0a00203030300a28020324a04070000091000b0629000182440346c0c801c044070f005520040030880b0403c1c4180c0c00694024031050101f414078240107047c504c0141050740524059001c0300b4a8561f0341c4102901c080700c503c1e010002c01004002c044005209000980700160000400905a00170103c1c89801c4581b207010741486002907601001307486401804505015400f03052262a40d40722413030051292194510390240d03554030524000e507888401d07001d01411a004402281c0d290400541300b04000f8400340000005201b1000a10501544882400c9680c185e288041c003207032080d52002d0b1203540c0d40d01811310613a83c08188101694000c071504404460200100000103001d0f0315420054440c207400810030080001c2d03408081030724941c2c20300c00c40310880c011003042d440b10b00901000c60101004250100c8c40354016005812207201c5003410240d403086040b0640f8045401079444da552 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 883726843 1250 883725593 883725599
    0x2102010f11092704080912030a0c050c150403020d210906090e010311090403140705030301050a050a050d0305090609040c050d050114060901030203130f0308090c09010303171915 78
    0x4502030320701e405040700c00342403e4003106044456a981e801400104002800549980196a030f1707404c00c4171000000c0c08590f2900c2c5540d101400c80c1062442c1541e0f60b11551010841d06d01c4c00d01805044c0c1d00c4030020241c00d152031a070030b110000c2004041107458910068050b00c40590000031200d00d443c480d900d01a4081c81c1c01d1000d806424140c2101d644810020011310114403402e2141e040c0d4501603a0300c4110303688a080c1191003d54141c07400d92800c800260032000d1041c0000518143d800c00c842000798142e41e0803c2241c0076845104454100c1150040c000210303020301c025214480018044500d070030407100c0040d04442d006c6d9441c1020440208580514900e44c1c031034030b400341000c420b000300000f0030310000803418082c0b0713041141055000000500354000009c1d110340000e0388000800c01c4100d152074080c1401034221059181b5201c0c1c6038605000340b07003200d261812242c141d1505403a601085040d00a08640100301c40090280080b0108040380e1034801c02d110a14030f00e08640034242 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 883728093 1250 883726843 883726849
    0xd0501110304060c03060f15090b0301301211010b0604121208060f04180611210f011208070c0e07110c0a060c03200105070e01020a2102010f1109 64
    0x20031800c91304040c82c0c402c050140c821700c05402d10681e903100343d071200d186030044012548a074181d003200b810f1120210000900ca29508070b11b0380c03c0690035010002c16613483d065415010f04008014201e00307140c0e40c2c0013403da402041c100c00c080c07000c140003143c032100b02d00110740154031541c03040000c8804500242d00788090502d1000e252115450030780b005044c40000550808420f10980340b15543c0c443c09040000007a82d101400c241d8000018000340b012943c082c000c540100030310f66100720b0505486c8032840e0381d01001510032200050211220b90030100c60801001c041c0e80c04903001c1004000010110ba5640900c000801070801c1040d803e14044200400c18040d4069903500d0b54400d090319141e6a442500c0581500c07080c0ca40258628031600b41190f00d11801601d84c480031001c40c0070b0b00031100301034203c94800c006079200c9164100405004980d21449100017800c1c61092440040c901414100c85003608031700c07480080f030600c1c50a44090110752003c2c60004001400181e030710b986003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 883729343 1250 883728093 883728101
    0x13111323030613060c023c2a0f1c0309081603110301061814061203030402040903052214010f02072106020403060c03060819020d020d050111030406 65
    0x40c8140d01814250410781c40940c6605080000140056181c68500694038800c000c186491000c0c108100b008a07510058119242c0c001c501600c1c0e03a10aa0000f03500503000010700324010950107080d208805444003c6600c0426050301403030384140780750f041e8081c1d96244604100040c8207500e0145181105180c0603003a40785c0d651107030f03410350085105905070b40c0051032030400b01e0780c1007003112039201c0c201c0b40003a00501881c0c0001111003541d601c64a6a0002503000000500880003002143d4841100b00200228900350520055004100190050030180c11003c500d6109060407402c10f012111140706c010725005400418001d1402c2c200b1043c03101021860008100f800c0c04800010700c132400944903240d900445880140340c2403001d41b6580407c5594540c0d03604070100b103440c0d91710f92400802030440c03050550300003402c18002044a000110310701121416451403841940d1360f80d400e1200b10302c000e000a07a0301c010f1102007000410028002c541c611089410469a28a09481c0440c115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 883730593 1250 883729343 883729409
    0xa120b030106050315090a02120304090c021207030f09051c1104050f010e0414030a0503191a0d0218091510030b180102070507080f07090b131113 64
    0x1070382c10103a080120382c0b00407502c3d1620304030300803500816580b01e040c030030b243c0400014000d40001c40400700f804400d0f4080003070f01c2903415220050105810080080740d56001c40844090b840900b04a00e00c0005e005242d0925031400c18145621019519000211581035036142c040028801c20800b03001c00c00c0c442c1c2e5560301c18030125010003807410040a000035a0b54140a03200c5088010030109060080d45c08040c9115940d51040786e0b0b0703800c04010b00421640064401700d09a0001802e0840c1c4c1246c14007031003d004074486201140c03080079008010745440c0c640300603030b0800c007070034082003003110f028445034803410922009183c554424a480c0000150003082034140f0384103840c0620000350604401e94104c0308114109107280105141c0d680207101d000c00080151194550009890002207480d056900f071000070358010340d6a50100a064841914200344d01451140a006010100d0350100c910403010002150070140301e040191000c00701500a81c401d882801c074040c454203c544041100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 883731843 1250 883730593 883730599
    0x243080f03071112120f09091321110f0a030906051801081909141c02100207030504080f0a02040b04060303080610030b36010510030905070b0a120b 65
    0xe00745490312003607105800348000604c0365042218448508004001404200119051199440a01449415483d808800054000c0c0c411000003a501401d50410344800d9030042c0e55501200c1c0049a103240703200704020f83c0700c00c0c0801c050500c04e1135100bc000380358528040d40014101c141d00c504010b01014001e070f00c82c90400c40b0411465141030302c0350502c41c04036142800c0c59030382d5407161030b40c10f1020600403081000441c90722000105001280441070700e000408411345080001550341c0e4250585074007400005a4000e8881c55242c03103443d030042a5242c0a4075144d81010b03220042030703043c0000c0040303d1003070340c0c07110850409502e800d100c0d50129003022241040348a1542d54060610034000f003603648211746020f019500d141c080d0304122081030b00100384031400001030300d25071407103003103951440f502101400090145552590803141038070b20081c14a0a0381c0d8003801c0231006407070312000407552030241b80d00004030612541d0142145c154180c407041c2130209284040c000719180b0f0034807284 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 883733093 1250 883731843 883731847
    0x602010509060108031615090f080a09050907050901082212021009030e1903060203100305010b0f030c1021052d06010e0a0b07061e060302010243080f03 67
    0x2d4042d04c4a541b03030810381c0140344002940c030820604000304400000546850b140070606001c0109000040c05d6250080d260840802d03212028450b2030b00d02192540042002042a0366440d030141e0f0406500c822070903414020030600301102070510344600011200100c0c441001d0111f039405014480c0c11500d091010081281261130042ca00701c21410f050f8010b4060714145111214025010009181c1285082d5940c0c2040041d45401c2c0c01e00e0300c0152200c1d40303881d42480a83c0780c68507601150f032800034001c114140c442d6081024070200541400140601050110b81d03200d00322070506c104540c10540000c2c1440d0986207006440c60118a0002e03070501b604a0700010409070141d550425020302c3c1c4090043c94800c04128011000c2e000900454404203a0008010458000304e148403000303181409410050240704080d1032580c040280907810008101141c0052a074800320400d0700d9a103100500b01c03145801d071503950343c200d4041203c40c031400710612500c5010081d41465804002c0118 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 883734343 1250 883733093 883733107
    0xf010c05030417212a04080d03110f0c1c020c01082d0604090807200910061b0b0403080402120705030a1104060b0d06031e0209040303051f060201050906010803 70
    0x1860b49981014102c90800c3c2c400100f108070fa45c42c81544280c03014800030085104601018030210f41041c402c808180c85494041c1400911030300804d03040c100c80b120403d0400c8440311070a142d0383c002100380c17a4140724004403031058207200041e034214032b03800b6005404801c2d40791000500e04000188244440445107802c081c0090610017121403001074028018442d465400c00207002e0910f504003c0c00c01403010a0840c01c0c00000441881c03c40100820051110200130610850410882d13154202d415205010000c4c075001d03505101c9211008950b210380c05906c0e41d0b400244104c01d5505a00056082040000b1800c0080c5121507000002d0001c1408503d44400641d803104c00b0b10f0010b084400c0d0240e40f120070b48940d002500504201c4007010b0303e5210030b1203403900600b41440f040d560304650340852203031611012003040070707550090161801595651815000b81c1805842d01c2046a1481c40d403040c4582c03c0404c0300080c028650000c43c003400e08414040c5406010f8100c3d03002900200a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 883735593 1250 883734343 883734367
    0x21021905250c05031002090a12050307120311070506040b150a1406070c080303100b03010f1710050705090109080106061b111504051c021c02030f010c05030417 70
    0x200410070562244840a200900d45210456002c1e0301c0150907205409240e1448001500501030000c0251402c10740555a40d4900c03501c5804105c001c0d0484d0000c02840010905421440072491800d08010130001040c3c0104103040e80070303c00550b1250040c1c4240000c015007003d40640080d04012000e0070301c0c40000005901444030710512644d106403281021f42a107414083e5a0201d800030503014a059803107110302c1d100c1d8001c42d5061080182408089003446071907040d0380c1650070340d1880e48040340c109400d644080c0d080c03002d005500e01c5418616800c0040358000c15202d41e009503146174594601030300140401c202600f200160380d06005050101a520062850303078003000f00301d040c07240721071410080780c20b04194114039081030000b010341e101c0312074500051045a034250345010440da0741040d04000019001d90096002c00340c000684450000341003075000759030009040d0b07040503502004580c2106c0001d20200b001c540040100810701203030244044900c2c0300c020002e031401e0260400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 883736843 1250 883735593 883735627
    0x3030518120c270a0606090f0608070c0206070f0507180e060a091407060503010e07030b030c010e04180f0605010506041503020307140d06080705040b030c1021021905 73
    0x3003a4003410a800b0b96200b10300300c00c58490f041ca0105000d070000d84c01d0844030000940014050302e8081400c0a5001446810351420001190255902c000d5151a1903208072140c008491043ea8440018800400070a040340c000640c854414030091225516140011646800495410300c040e483e001a40c610084041030003544a542400000f132215854507100c2da070b041030348100e215144609640445c14907005030040d41a1000f8100200040e624810110140c03004d007000950190001c1d00394104a50060301c2c04c2c500800024408a0300c160f20004142403100030f45401d90369a82c09107140c90a1003070314070480d07000d03207010f0301d25600d002c0c14801c6401a40001d01c4088003010ba00200041079944920454081d54000e1003101c0da40300708240c01d86000d89044d00895103c0c0c026000005610f141c83d00c10391142c1c10020700907144203260201044000c84507a008902801b40e21400000082d090459090b4111140c050060300c510340c0041d0f084041411421071010b01804104140d0b0030440641 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 883738093 1250 883736843 883736863
    0x506090609120316150e0c01111c050d0f0203010812070c0306020c011b020712031103090306010305071403030315040c0903080a0f031401060c03080c0c03040303051812 74
    0x48540c1d84095000120b564118411000c04160201156101d0040c505a40d1288079600610068801c80b201c40241011103400541410960713010596199407540250030034400080304400f170701e4040c4680a00c0350500100611440001000040c041084d00c0040c8502c08031920b6084085040d981031845d12a900c11000c86080720040000c1401d00030000100003134005140d02c02415511210310190640c0600080140003c0c1350700420072211560b8030000d0100c013210500e4100e205545025142581d155088068042080c042017105000d141c404000c20703802144a00c00821900d882d191240c0035000200c00340d1482a0410414400000c511f00a500d178450000c80c0c1c000f440694031784040ea00c06100c3d6100034502c49000c2081806c09e900038170050700c0103507291014404007055064800c140342c001d004100201e45440c03600804a072140380442d611480c17030716113103141101c03442c81145503400642c02100042d8000682500d4190103040b00400ba180c01d441c5074040181150105840d041602 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 883739343 1250 883738093 883738099
    0x16030c0611010e010213210c050618030a0311210f160204240f030209040807022202071505040507150c0c0e01060305090609030d0518030c0606041104050609 69
    0x107800c00a900d2000e43c0126180611040215038a6100011082020312140b140d2940403040500c05e5102814141901100540c403604015145003002c003002030b6504191000b01300d018203412205800d84080104031001070094491070480a25411054035103250001c1c60300380040c03034440000a40e6070600a903000b100d440e803202502d17540200f00c541902c3e0514100654400e05001c1c0b194020824610725182c1011045640b00c4510b8450388502848240340c40020341142e030f4200014007040302d0300007a1201d140300030810000c0d204404d805901880032603280345e402e81c0d400228141044000b0030b00070740c4540e05102c07e00c0145416110551214007605c101006004410940c940c03840c45058010445a88401246d1907142c40c0d07460710003044002d009000201c1d24200201d0704094001843e20b11860716000110300d0041c1c11000c400240c030f4054001e0802d84000029610020350507c013074146e0303c550000404c0645008010002035824041e5250041a0104400c0c0251b858500c21250004020303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 883740593 1250 883739343 883739357
    0xf1a0616020d031101021215030c030a1e0f110a0f030b0f0a0b03100212070206190902010c0212030a081501140f0415020601030309051504030b06150409060816030c06 73
    0x24102501c0d5075644e880400b02c2d551001502018400707480141c117014861081072305603200b6522050554480b0400d83d92581035006d4100440001c10208004104402d5000000c0080466954401d0419059003080b95403109001000c2221700702403110000a1081000ea50201071441d151020740140262986000050100016100811503089154500c0c8040c040b100e400b440c4080503130080d00f040403689088070040001c035081c2c1d440000c0c203901581140c840c43c0d40f100e1001024100030040e00000f2070500170406400005681c4081190b0700800c107010240d55034600da80300c003c002010040c0f1100f89150010088015079a1050300e0084915104001a03521007415540d82c0942c0100e44c0074082403003080d40110245d0742d000c03c0e254100e074840d880d044403e0351651708121044510030104c3d03010347c20500c0b0030400b18581503080303508428044d00101e00d000307290040f000960702a410445c81d9549070784003041722107000c1003214000d03190120401040360843e51818182403c911a0078100300c25 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 883741843 1250 883740593 883740619
    0x702060a03090b130b0f070212160629122a0303030403030615030515060708120117370203070e0106020c0a080f0c091005040f1a061602 60
    0x2941c00b420340c00e90018800c40c0d00745080c08400000e40e0520f00b040343e450f104a00854090000000910b0083c2c0d0182c02900040302042d40501003a001480002c94841010039420080341c0c951140d0312102c0390354000c4000e001c01c0250603401a04015042070302401005243d00d160801c04180c40c0c8030b95910042404020110903101414440305081c680c1d450f0000100b440f04040d01584610212400c0c6581301701800800c82d000e0f03084a00845102c0c540a845001c1d040c49482d252008088032440398030f241d803c3c10788030304420300007041c01d81240c0040c0b0a040039000b945041040200c800d481140f94a003a9060307403610052130b03201115044882d0044d60010725017195000d1001c280600791400100e2440d41c2d4500000f0740e1801c2e81d07030101c4e000d29040a40421540008a4002002c1c0000f500804d5880f680005219075800300074554500b08201c0303a40894165500d0140d9018180180400320b60300f050900404c6c05482c815101511038201001015042c010b030521614429804540c02000118 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 883743093 1250 883741843 883741847
    0xc0e01140d0921080108070e0a2310080c04060f050f030114091c0c32071805060a0305060103060203041a010e07090e010b1b010e060118050901110702060a 68
    0x48141001000c90b00c0c507048446100f04620f04000c0765035107a40c2d50b10011307643c40b502c040d100e0585d40203d44007040200e0005401e20100e800905944100c6640080881e80f000151180701e40103542c261260b81f402ca1040142480411612181e400100e50821242d460301c048041040303018442d0900400d41c01c1e000401d07903502903011880e070103224017a024061401070645d40d10744014510004400170611480e00009108a004843e02c9900040e55140100a000d42c0100052180010400100703030351180002450144880c034014905020904030311640d0401500644000130109070203800802c2040000c1140052505c0c1105d8004800594903111420702110039681d10804500480021000040000200d03080c0c82c8601000e50710f0103c03643d01c030f02e400c2d58685021321420800c0c14080c040520740881c9440c02008800c840d40000071185002e4084504240742607100c00480c419007044980c0b251004e0103407d600c004a00001c00c402c107000075034861280070b64a4040c3c00303007501198100c1118 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 883744343 1250 883743093 883743101
    0xb0603102c01020903032d041a0c070510030204030c120215070812011203081e270a0507062003040308090f030f06090f0f0c0105030408121005040c0e01140d 69
    0x64000303026603503901e1040d022040003440c0c5401070b5a0b0f0b600c0c7c1007880c2c030b2045448401e482c2522a0501418007a0041e143c2880d21508403041c004101c1c0901e000000e499130362600008410704040c0c034050380380c51546c1480034480501d40d2103040381c0445000c40d000181e4403402c00219981d6158081501d441003800d00103414001c2582d1030300e900580c0740001c11312b070071140c8500c10120f01c030303a40e00c2d078160340ea003111800303007104585041402c8030b403e10100c0c0c00f0030050031011950802808500b00050041c0c041c00380b0b000c00103002585c280c0c01c654001d011840e80804806c80d00d5103030460780b81d101d601e4550295601d1203188005488203d0125201446a84581200300400030050445442d803000e4410345444003800c4c1d6400340c1c80d2084100410342070304003080c2d803001c070b041c6500903290385c00c8400b00650b500d5000500480b0150380030040000c0d810600d0b407165028000c034448005000d8240003d002c00c540100d17000b02c1c10b11088280780d030041daa101c030501d003010b040c0540d200e4480b101c1c810384238090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 883745593 1250 883744343 883744357
    0x29090c090c04080607050d0f0216060f090203031305011107030b0106141b1627182018150d05010f0c03090b0604051603050405031201030b0603102c0102 67
    0x40c080c4d503061000c03d5601c140a401d1540d0b82d40020032542c0c07203094182c402c82c842e4551103c401c100780c00d034010201e265a4850702558480743e401088401c02d40d40080c1c11030313204004452561201c050240603550b8040380340e00342d0422034002003000908680712104c0420051140100300000080c1010500e100740c403c3e14088040d0100040a09006018aa85503e840d0300e04000000a1110024102ea01803b40200700c0c100c90820b1004880b410300020081c16480e0b1142440c1d00111500c50005a00e40010f200600d40300c68180100740042400c00440c0e0904003440100082c008040c80801c40140d1800c58030194219118074032803e20b850094054200c0091000125180881d0076005035050b0700100ca016204502030445030755200d040008540c42500ca00c0300c07201706a400643c0e00d80c00b070340c0940d0300940a41f08072420030030304003400d03a88007209070030440780d4001034410310800b810100b21000c00c05285107024003010101101d024007042c0b9500c003c0c16a040111200d40711000294126046 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 883746843 1250 883745593 883745609
    0x606140c01110a020d0e0105040f03060509070e010305030406020705100801061d12030904060f0f0e0a021201061101151a1606020a0c02030d030507020307020f13050429090c090c04 79
    0xf00c42d41d402c4042e49804a030060240032840684222820750312400480707040ea1408046011854150780740c090051000401106031741c80740324804240510308100c0d00d4000c0d44100c00a41d030311070500e58001d00740071540e4011401046100020521650008049130640b5240c0c680000d01c0118034103401040810140c1c1a03400001404441104c0c83c800300080026040c103550611140d945c4601ca0180549144105075021070015810302071620079289080e00209030074005400d058802000800700320b420784c000c40106900e4508190b40c00d1081c081c01c107060940380040c083c51442c005010101c5199145110b0302007800044e42c2000030b9600c50340c0c441643d00090115100c80c80d140b0701402c680e040030300a9101e84204415401201e1090103618820b26180d40590708001241d403c0c089644090400360794044014100040700c0702403481030f10b2245008403070070689511a084042d04044000203401c9400602c07008100f0500000120b1042048090750b0070303001e5983c6c1c0300910005005039040004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 883748093 1250 883746843 883746847
    0x15120e0a020907180e0603030a08070203041a03010303080c0711060a20070302010207051002102a0810090606140c0307170a080a021206040902011e11010e010606140c0111 75
    0x6968010081a281c040705404010344c551a03040041010b48120f640e40c0d41944100808100c0e10301c20103200350011842d0040f03d0a0548614404010204141a8110080d4084010402e040d03201b0462a00b0001480b6058035104240e200d8810059980c7c001c58000c000004d182d240d5143f05804070719117064000c850b072a00349100380c101915001d15200a90040c45002800305040c6803450307080000c140c05030010803004034030190000161820200c0001075142c0030140190448072154504440301b91540c41380d11910300541b603140214229040407003440d1414200740300b480c1e04810904c14101e864080151907034648200c01c0d103503101d60040101110300000000c012000400090103248005803140b1940b5600c0c0020300c000c03805042510240071103004d000c0781c03613400c041e40800d60050040c54901c161b40e81114142801601c1846260006140304d0b4050740c2d40c5600b8490814513140f0f4000078403902d882c04900a007003a11a05030000002400034501c1321aa40940c0100c0c10342e0160000d0760303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 883749343 1250 883748093 883748101
    0x120c050f0408101d1905191b170c0105070f060204030b070f0e090c280504080111030c03041e06050708070e240a0e04060b090a15120e0a0209 62
    0x16448100764a0f40000480c10302c1c040e5184503150300e10402c5041640341c0207100d00f0401d680003400f000c2949030161803030302550b017201c1c1030301c68a0300c9042001c90003020300c0580302c2c2c052541d4542d64585544072403c14807151000803d045004541500341c0030b824a0704980701d16250805a080f0420410020181403001900008000c00c81c0340540c46061281c40f800c10f0840248010b540c01d0418882e02544010440d00180642141401401400020342d41c1012610f0300740080300510096500b808020a0002c40c0c20007041e0303800d004141c0c051416000711790450500001c4241c0038040904002c081c02502c500810b1440750034001d408049800044c180300c80d08000300040c00c1c1d0501070341c6032000100400b131210300350300740b5900c100c90140c42e1400c02d0031401d0710280c03c000d0325001140b4540c01c1011022959156948501440000c1d2a28203038095585c1c48203400c020f0f8104840e801038011507060303c800215140c0021114a0400d10020302251000704dc4010609045103920020b500404c40421b03c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 883750593 1250 883749343 883749359
    0x5061f090609061505180112090b07082e05060309030c03040905041406040b1b070c0e01050a1a0702102601081e0a120e0a030311011803120c050f04 65
    0x5400c44c0c581840c2c502ca0b4251000d001ca9542c81140d14288202c20043d13120405544126151030000407081d600142c110074aa032040c200c00021744000d0001840708090000584050214030707840d45089400705414040c0b401e85106440340c92051502c81e0f034000c80080c130540400d1044440d9242c2c0c0300c0075a079442d9201c0142e00010714045d00d05441a882c000424000004005105c901a40c0c20552000095952105881c0414a04444969005401d0015400291500840802038220407404050a60505050050b5084154000c2d01040714540381454802e40b1602101d00454055442146031030960b5000da40144150b4030722040354a06240c0411078a02103500141600e4400003541e4144113880824164031000041101c00c5420161040c800181030302d44c1c0f80b06220580c14100795002400d000200040165030065001c10071078601010080c10038803500400101c0c0624200400c9200d4a00402100041030110312071079986031070200e8540100142c030006a0200f01c0c1030380c0d0750b032600c0070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 883751843 1250 883750593 883750601
    0xf060405010c180503100f0612030e120a02010c0305070804030c3302100506130e101811060309011b0c020112111233120a05061f090609 60
    0x400e100040c4075454940304091142d42c90f904803080207004006000a003940f000090100c80712a50405135590b500040c1141d100301c00c582c520f806500e400101d004524107020842a0303d02c40f02c0c403070790003825101d8010b0b0303008001505220b406180140d2540311605e0302e004541b10b039800c0034129032007148000590b003d05424007400402c0984121011100c000c0490710315010f8582030b42e000d6004002001c03d40c007210740c00720351701200050038110304040e0840c070f200450340001540002604982030b0a21503402c4c60142000d0200c840380b090350a0a12500d44161004403401c540384688070001c040f4080c0382003504402c001114a601e4101404402e4101401c000c11a480480c042685e0000f92901c40b4403512072410300440750141a4905a102c040c0030607982401030881044000100100f01e039000c0c80e028407078000c41141c4441d84250040d20170030515020f040e01c2e2101590040c411480050400b2030020340000314215030302c0044601c40d000382c8181040380c00c488519403621400003214852508 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 883753093 1250 883751843 883751861
    0x415020c0108150f01030b04020c1e06060a0b0d29040c0503010e0606160602391b04060503030d0f06120c29070606090f14040b07020f06040501 63
    0xc956400d090a00151004035003101d0f01c41d1a440da065091801c0d080c0300c003c001510505140c0001d25044150006080b170300044d960483e954811100a00c417007850b81001440343e20060028401c0f490408009610141d803402500c9846174041400c01e20144150401e40c44850f01d450040c078600381214400e5040c41c034a1664601c1241429003010840d4011811a8143d074201c6d502d19030366941d04c201348045503111104581101d203000e0340d05000f00c0d1461001e803180c1500445020795000841441c0c3e070800c0f00c68002e81248401c5404200285080094100da4441041c00802200c00c00080000c0040c88154009034240c000020f58002e189865402103800360007860041000301c5d199903031072191103a40713007005080c1c110310b80d42440401c404030404c0590030a04a03c80070890140c80701c0e108150046c61040b140981c03180700900c082d007041c0c021150912400701c810060268032440d440030070782014001808000c280c00101d14114400d10070392061003011000c56841d42041e240c601e00030103d242c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 883754343 1250 883753093 883753097
    0x31d0d03080f0709140907170903210609040605060406170303090d0c050d1416140d0315170304030602030c0403051605010512070216090c02240f090c060415 69
    0x403000030b280030300813583d420070384045180791501c00404034284070070070744045c00b007106020744444052992030604414074401c561845c040d54607151180442802e110b0784031840f40d0408100d808014058498060f03155100b038020030b020966440d40000700b07004018582104084044040043c0d622400000045018550503401c4030014100010101c1e4841c0800b01d0080880c0c0100020849041c440c01c070b00c0d10404140303184030345040c450321080c0d1030f00c104019080304d95a944510600e1540000e00c507513040d014850905120804405903074000d00706003802141044108100880c911038010000d4a0255501440855480c2002c1e0344403001c0e50428802200e0500c140503804800b00388809a4204450041c1c5a29040850341c412010301f01100504420442c4210182c0c3c0d18040c0c00d40e031059000300083e14001030100000c0c0f0000382042c0040c0e0480c00e5070b1805421020402e91010f10b4150f2040d507443c2d210005443e1000700b581003259a044056020801180118014014880c0000311440c69 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 883755593 1250 883754343 883754371
    0x304030b06040203100506181c05011401050306010603091b0e011715060d050f060406150e01031a100f0801020909060f0a031106091306080c1c031d0d0308 68
    0x14070204000da202c116402c0d1000d00d00000204902d050080107411182c000e09074100b0121030460226081e0b149400050003903011a810700014403c0070b02c02d840007442c4c680b00c00c0c001d660401003c2aa2040d0601c50107040694408501e010300c07911000c48400804aa402080841d60307520003040042070a0146060040034a01c1e80214141e001800c515900c540200d21803103035036171100308050711b28072400556085c05203110713035035821030144041486244103a0b00060042d17010078451040400c1c5030440306034860540c006001050101c1c1d03042e030032440154a001200e980f1003540024425140e0b004900002c00b110001c00d5850043d00a085241400e071500c0295564071820017105040c00c1d6421a000300a4000a0001c41c1915050764001c410190242d49425407200204e07000b00b10b0001c1c1d5111240e83d400041c404c03880d00384000c061014040300d614a0401c21100038400b0800c100760002d082c0300d42d03c8503d2100350180c01c031004690300014481d0010710401d04000d0980101200d078003002c0564 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 883756843 1250 883755593 883755601
    0xb0901050115090f0315180609060b0d0b0c07030306170f010f23071b050c0901050603010320010207180c08063a050106080a0b060303121302040b10020304030b 70
    0xc10340e2010101c070070344c028514015156481742c0414440581d44071b001580c403a1407280442031000c10700015a03101c0d5100240607442401e04004840405100074840c14500d04144c0c0480c0c5c0f2050255000b14250b00001d544190525050740140701542c48038201c20420f6894940080c40030894584a806d094020f10400c8940600b0b4001c64600c0d550000c60340c0c0031448000b1003814060030041d4080d41e142001902078400d10300882d021980203400316915403090401c84042e0404801c0b41e0700415098981500310350455541c1d01c070300c054840c230000c0c0c94040c51540028581c03003041014000c3c0341c40d400a410308204503140d90080d003815419900802c072201d010846c0c0e405d10882503595941c0050304424140098200e40112a21403a507020401c4d040554030310103d44213104540080200385d005003500300c00703840c1008140d100180498841d405c1400a0501e80201d6424607500120555504204425601c0060300401204020783d402c0283c0c0034a0001194000008005690041070303180110341e2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 883758093 1250 883756843 883756847
    0x10806060d0809013617250e0a02040306180309060e03030d050a050610020102070c03060b0315090c13060f1505040902031e071b120306030b0901050115 67
    0x4810303a001908406000d801401149540003d00050403052422a03206181c607034514a142184c509030083e0f0140301140c00c0745103904a058240100302c035040750013600d05c00c110200d4035410030200d00a2595082c2070344a0b451990002c0b07003070240c82c1d10403020b100c81c1001000c120094001d804102c0d0443d1a2140c00820380041961404c080c60b415a01d080702c850400e981102d400b604182c01a8051005201030303000000103000e45845854144000076041c900101000010046100208256441000090040341201d540001500d40218005c45e145280c3c6000c645000c060b551500d00030381030b580901c07aa03190007264a01c1000d038216a20190080212020000c8076402c1c81019110311500c1c2080040c10a02c0210400101050408134100796035400461700303a80c000c035410102181d06542d1000707010704d50311001d40c005c030280c50480f1440100c0040d50820300251030001d0b00c480c0c1c1c0207800940040c46500098065640308a40c181c440c1044c080d40c0c6c0c0a45400c1c05010342c2049120756040d4268 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 883759343 1250 883758093 883758103
    0x231020a0f17040201030f1e020a03111312020607140f120406090e070e12010507020d0804020306042604140f031f0e0309060a0806010e0303040f050108090a12170108 73
    0x4002c52080c5040d5110342d40150b00a0542852414800740c81e240d0780d400441202d004510716850120300942c0d00c04041b0070080803a071111000c030807801c406004451688500c0c50020040c2d888220401c40481c1c0507000080c1d09000d0044000c10301c098030401e00751420b002092061035501103604540428454402c89070030303402035001390b4001600808040180d05030800c4510f8010074517041108044070084041006802031001c0c040250b910703101440038850b41008012003140ea1807521641c5030030706500194441f07402400181400e01c083c8548202080c1808e071507802001c21107034142d0b1319075846a40c4032160101d81e8045205000f803c040440e02c3c00c0102e40040381e0303840c440c044410110b203101000000c00e1a00c000d080b4a1005120380c60640d21103000030702024080da2944041c520300f843c00103110107051a07100380650014001001096500350320401034510908200000b9621003814628111f001d02c3c0180c2054200c40c1001030b010f8118212415149060b01140e001c1d83c2c035035201690318 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 883760593 1250 883759343 883759367
    0x6030c0c080d0e10050118090c030b01030b01080d0f05070b04020102070f15080c360402030711010f0b01020d1b060612020111010516121e0204051201050606070231020a0f 75
    0x14900e1070070810030780355108a002d144100007410b50b152b20303921070007009a4240c004507101d8000030014400e1038020424020003541c58a81148200015000105a8041c42c00018808069040810b08581c000d10008004c0e140569001c451030b0b40d6407180083c0c038109031501c0d801080e02440417170520302c006030440e024640209040340880c0721060300d25001140441c0f026201e540740480c0c61005981d01d00055010308010f41e2845d1801052080d06803c5a0320000c81006991414007602156600402c01685080c20303802d001c1d1141040c2d412640d041001510002c09541c078210000c2102250782da03506c90791900030f984913004440480400c500b02c40c0180c1c0c50b64404030034a640001028410b0303003650201c018041c00400d411000b4201035015841418504182540210703040c082814400c0110400342c4006009000500b000c0000c14250312903901d0280c06504000504400302000761850440f21004284440c0c005004c0340f5010001d402411f6020300013100c001c508400d09110f01c01c08104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 883761843 1250 883760593 883760609
    0x2a0f191d0a0e040b0c281403071d0406080111030108010c0932030f06040b0a090809060f04030c0806071407020306070305060406080a0507290406030c0c080d0e100501 73
    0x11601c99803254018a0402401d0403000c000412450042400b049100300e803900c1b0304080721404605052020f8020003148802c1d005c182c20074010014416803180075054411100e0a105000600d5080410041c00da5604014555030030310701c1040803824800c00a50407240640000c02802c125104c1c1201c10391454802d060030402d20818034002c80c903120040c881c408604092005210117818082070510340a0b0008081982040081000784004a02101d07031100303101d42c01300100b42261740c81c5035007030082c20360881c000c0c000031420255881e0301d5001c4070f02450700900005101c2c1d40e269250b82e80c1e42004c0302c142c40010151041400b003010480c09031040aa4004c0240251f40c0c1c40c00301c1100105801445950f1150b00d8210009020005010180c8914024400b8001d407d01340f841142e040d00400c0030328110010002d58038a11000031a05540540d10381c0d20300407518111150040f00c03080412231003e803a02c03d000070b4010400c1c80e01da0040704d0310383d2101c00340d54a186485281800f19082449000c0c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 883763093 1250 883761843 883761869
    0xb03030c07260717010f050f09060603011b08041103030304080301141c0609020f0a170c03070f062d0903060c0311040504090503042103082a0f191d0a 66
    0x1050104404d01c0144d1003c0401c000542c48460144100c140e0b201620080381d1950b007035003806111081848581d5011a083d80240480701c82e044600c000807000800d02c80400107210301140c01c100a55a0b00d1040500040403a910781c10941003c1b0220b600038498011f040110b07010201701c5041400f26425126071902000103080d9031a01d03544040c0c618000700701d03403010f5400a82030066440c00040c0010f818481a900d041c030113683c00741480d166880c0c0c1080c0c03003a0320030380e402c000072041080c41406685251800405492000a549581961304141d9869450305640740d0040564050100e10849000c2c0c441400918a01e06c015400c44505c40b01482115204100a101504158200510051051041b61720b42a5100807100072001402d02082008541c0742d6824289903103c00c5c0160400c11000701302c002c410110204081001c0c900c8107800c0040d6001c20b020391411011010fa840410309484c031023000c000d03c01c800402c15251090800c130701c0d401034022a9480c4c144004140140c17501e07040301403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 883764343 1250 883763093 883763099
    0x21803060f07051206040e0a08091003051501210c030507140307020d180b031504060e070915050c0d121a03060c0f07120801150e060a08060102010b03030c072607 71
    0x6a5840c3c001005c480c0c2258440a03036640d20441081603107603003801200381c5526440205c0c00c005000d2140c0c0840340030903003400180311060b503181341340c00145034003403d000494840d8a0351041c00000d40c242840029031038048440c8010360181c01aa108030a1596440c403c04a5a900e0110340d01040d91100c0c0140e0101451940103030080d401b035080ea4407031078521038045e59603032415800d5a00c200e405483d030300620b00031400349081034042d0101910b00f05102070075500c0c00a4006041d007085102e841e01c3c505c0c0d101c0d111080e1034007c0c0f0464034045121815247c48074114a80030f0842004034400340550751400b81c030408511404030000007a5400200580b1040d100d01b000300fa09500140c2a001086404004d00c10000b00b090b0b6a041000703e094484c0c1085615160781c2c2c94500c0c50140045007803062817050350507155211011611908940d060042041c1c980200403070041070017920b03054051200107802c043c44400090000100e0b1905120b2022070001f1314424500c0c24010520107a0503800000e0034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 883765593 1250 883764343 883764367
    0x30b013510211208040c0f09021909032112020426010209150c031b07030302010c050a08010e10080607020c190b03010b0c010f0906140a0c120c050c01021803060f0705 73
    0x7640c0082c0100340c1c4c084487e0315a80001c00138001d507440b1f4084140e001030502c013084000828050110b82d5030505588551454860b824505441c40c07010a00b01c44081c10b0fa541c0c01e005180d80001e0208048045441c0ca45600003151190f50820784003080f00e15100120030403110500032682001000341408040703004000840c0c81c160402c04100c1d034580820301407220015110300d002140b615800004144240c03075410b003e82100c5403504002d04000e8100205050960406812811195001510800e594034102e4545480d49250041e216500450b000d001038a6400503820400c4002202c068060486a5400080741c1c0d400e441421003240c400d01c01000400400d0014244919603500080751004110a1803001c88801c49002c41c1d040b55540d0302d040751540d1541c1c16aa000c80003550402012100010180604804542e44071a09071203108000384540300701309888080d40d103c4000d649450369000d1081c1401080f14080340641310303080000f1074058604d00320501654071919154545452404070b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 883766843 1250 883765593 883765607
    0x1603200c100b0f1c0204020c0a0c080706020601060c05010e07230a03120e01170f0f0a02031003120c0c0902070b07020303190b121c020d030b0135102112 67
    0x101c46404c03051104c8840c0940c0b9a40000d100b010080710240840e540c04d4503200c01c9a010540040c91107600541c0184000d07900040e4003030544845041000d0801c905140c254090300d04c03044102018080c6a80010b40841342440c6071003002d08a01c0c258001240c19024014021002d10000d0301084810100f03210782401a92080b14241040c500b048c814000b0340c4883d04688001e841c41580320b810f00003001a61500c0300c40b0b20341c01c414035002c03d61071030600c1808180724040b240400760502038103081e61600c060103202031000956002040d01c1c11540da8004203002500b00e0350302a51855041e07800551101d01c00f0084134400c00c6c1d19039000180c680415422030041c042007504a8000d000720803840c581e03910070450b891115a240c0c2c40e60789205008000203003020701d1510704c00d0525040c00404003139a0f0f04503001144100d409000c11800c0a4440340d070104800c040c0307000102103c2c0c0138041c407011401810514064a45c824171865210000081c081003503840c0d980702400d4061141d0541121300d2062107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 883768093 1250 883766843 883766869
    0x32318060307030905160e060a080d081f140f1c060f0f02031503070e06060f031b0a0c1403030f0c1305060c01020d0b0f091603200c100b0f 61
    0x30340001c011481da03551030715012120106d40ca41c101502810050341c02070b0410580d21100a885440b0340743d2400c04081d03039503000180c050003880001c000050040e00030340c000800010740741450564003a13031404200410302a9500e902c0c012004400c5120f00350420400030b9850003008081d00350000c0440e240e401c0208020364420307601039141e0b00d20300820003003400030394003807640803e803030207000045400c00d490b001c005c2d071151644035269410401c50b95100c40a8480d50003402c49000c0d940d030355108410700c4034440d15003507814944011070321004127680300d81b03800d0106225199180e80060441e88080e0b4074002284d243c002c038401d880c00152880d04103c0a000000500004551407607100c0c4001105508081400413890f94085991849140340340262505c0d0708095411800214042000ca02d03c400d00070a1a070755154250410b400b1544682e01281c1c5402400c032030911440d186001180c41c55100800c40f07885480341c0031801c2030184a034442d0750403143d0010980601e2032140030500070505116030f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 883769343 1250 883768093 883768097
    0xa090903050a080c070f0c091415060f09090c12010602031801050c0c0301061404060b090906012d032c0d030e0312040804170a080301091503020409032318060307 71
    0x100030745002590701c01c41038446c1482180402080c0d41041107205c02c8909151003a0451409601440300d8000d82c0d160000603240c0c15200c40713640b4007150949140b80c0c4a40502d040e0003410f03e40400c400842e100001d444a2502c215110720a070743ea800f012a40c3e07020f850041120511900b1030030040350300030790040c0154508101582c21400c4807600080c02c452280c1d0111401504605281034145440d104020207042162305903400d00d041c220210703001e03003802402d0a0502907003030181000880032050821a00c41100100c0e1108200c03400000c01034013201508891070b1188001c281012503100e5100f05040c40c102e0024540007034107201c1140074084419801c5441d020812140b8542c0c0c82808a6034403e6009803190b581e5a850460020840c10342c866806440da000002d581c0c001401110880781101d8810301c0210f0000c10b01124940d018045500007503100f40f411400380101500301c3c2580b088003440700da42c039400c00d078070450183c21807250305012131903500080300c40c1626107030107805560004064 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 883770593 1250 883769343 883769347
    0x905011209060c1107090207051e0a0507091b0e0310091103160e090303040f0605040201050405040f0e0c0927120418050703110f0a0e060a0e0a090903050a080c 70
    0xd03442e54000c40c0c0c22080740c4400228000b00350341542004205d50f6000784540d0104502e0034190fa00c1d020f48a500c070030171003103904110b59000400600104500307201642c2200550f000c603662048180700400e4103200a80b81207460200c0302907083d002e000d07004070707200c4003030060440d100c040c071003440080c9000f1004131245c2c00c0300b820030009910200890032440b183d40c6281e0000504265000c0020400180554103584c030030801c010004000d949c5003a00154000310200d04c613191840103885a0156421554015150100e91224460290009600441407a05540d00c0e21a10070074480c50200803101035a550800c46181d5048000403001c607010320102c8426980f42010400078001031394460b42c04620052603032440d01c421040a4828560041d5103801e080010140003018042c3c4c0d07001d4200109882d6801007403240380f05010b0b03094000840307001812140d440345a8407020b04070000030502d45015900080020504000511030f05803c6905505c926080c0041c0300b0b030031108510010a004000801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 883771843 1250 883770593 883770611
    0x2010f0c0f0b010602030c1606050403120228021314150a05030609031306181202030109060923240423030a03051315150509010306090516030309050112 67
    0x6420b90050107407501d0f5014599460a15240301e180a0f00041039901c1c1c100d08450802070750380c0003000c580440760700c01c0e008440854070400690504002014091455031000c3d56045680b0240c240010320500c211109003c101d40e0071060b004644252120396940e40320100072900117444078044201c1444005e246500d074644500109013442c009840704051580081102107036200c0c03440341800900520303d171207840408443c6c070000d400442c52103000325a04040034404c1c10354800b03411000701242c100b1003d12074aa1a80340411904480c090009027100301598081003072100441c203520007405000d22845210a00302600c1c804900140003110100740d051100c05a511901c400c003034550312180003a40c1c130b90311001c00140507508020040e0010200f0a20131100180c040341d24040340003a070980000d030000324000e2424901e4040e070070281c0d00c62215000042041466004211100c1c40744098032030040c1d0600e00d00318207428a00008010032611441401654031030360f60009406443c3e1404161000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 883773093 1250 883771843 883771853
    0x11030c06011707080304080a050c0904030e01360303110129010905030a05030304030306060507020904060e2811040207020a17011d0115081f02071b06050319050402010f0c0f 76
    0x100940c480741c0741390004122313401449401d0002a11010741035509010901e825a002080e8200185c42d40f4148061445044000f40d4030392103d00074580d034071840803840030380c22546c03500f59640c1d1312040707000410440c00800006018003601e5500445442503078500c0c0600091a0281c4d014420428100414104006055601000294600c5000b4400380d41d403402e050030014141c801e150405030078443c003001301d0780058590000440e40560031010005a40d00c1c201c0900b81040200544464481842c003004100d0071510000c85034051305c905000094030802105000590060b8800a5800403031110100042c06084508001d09110712000042c80a08208401013802181c1c0124221ba03543d4108503154085924900002e42950070042c696000c0b42c1d035030350349c000b00d0000040c1011030b00845e0001c10440d0085190811a00569003011019240c0308000c20680040303030400d1180ca42c800c0303081041e000310702c40c8034041c2d90103940320b6800b0214070106403807200705818100e803408012080750001c14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 883774343 1250 883773093 883773097
    0x319080c030307120f09020f0402032e1409270709050a061409060616020105090405010e0709120507150e0904031d04231008010e0d11030c060117070803 67
    0x103207140c90b010019290b0b00040d80484645d4030700d01000d64642903841c80580d0351144031400d1420704440140c1c0c1caa07901d01d02d0a50104000110019916204000341601c41901e94003a00796006c07010b03c0c82000c4000f10812020420686e030210800a540c8406139030841445c003103c20803210701048030384d0959100701d4002201c2003160155181980c4100612030301f066894060440103085420308800e041900c0000d005c3e105119520301d9030b5110002c12000c590050b01961701070b020080c400c0080b0744c0e40750464410301600702c0300c1c1c600040741c052001c501c6180420342803400640200050440350300303040c2c407205003032000c81c00107003481501100708540756250b0800c0351051703100c1ea9801c92004001c050107480b0304591822980b080f030a00320b13413000c00806005a0303d4041e001c000e02c00c20720307111584214003401c45a00204007650816112a000700400120544948046d5460b4400400d101485a0712400b600c0640d641c250444401005020003580d124990150381c207094a000daa5a00301d4240342d9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 883775593 1250 883774343 883774351
    0x6020703051c020405040e0a0201080105091e1f06050a05040b0a050d090f12090b19050705070e100515030f090c1305060a0803090904080c0a020d110307060e0319080c0303 75
    0x2c0d400207000d000d035042c1400740100300c80502d401481084481d41c00a42061814002d960150491000142c00c1e0002e07500200031040340d0f04104c840d6420315040c5c4d140c0c00074900d0048040156901000607005204030100d554640190703940d1030803d418000c0c2d8060a81c4402d5003007041150074051500c1c40d004a10503410003521492512a800e00e2074917090920352081005c42c818800805820450950b00c00b081b0742c810300c9802904002c4d8494a40251010301070751002800910030040081410f9000018880c001d192182c0300c040420395840421690312210045034502c2c400a00204640075240000160041045015280c1f54100346000c55682c0300503145240c422622201401014180410303520060220540514078000030000841c101c0000504000c064010011f40c0359a1460140102c7c09800d500811080ea8060941041a82502c001e4034042c464040e8020000d280e60045850140d1200050301801e5001c00c0d9242003070903100056000c1d07811400c10020001c1e2118140000d501c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 883776843 1250 883775593 883775647
    0x31c030e010618150e13083103060614101b06021911010c0203040308280302031608090d0c06091203050711071d1302030708030306030c0a0b0301030602070305 70
    0x20301800c0040748100003825602680405c801070003848008044134116000c0160070080e00750761190251b000075590880c620840c1c01f00244502c0c58030301050415400c00403240544d42c02e11540381c551044420001c42005101e0b80401201c01c3c0d610340c3c5004a48603c50b4242d03080c60b0040c03565503178455074140d9000a070f404443d044d1016042501315001184407e850540000030403502c10001c40c00b070344c1c0b0721a500020785001000708191406800e942030246c03036002510103003822403010700006400b9400940300310a2120755600880c5286100d202c0f12441944400d004080034800024196416942c242081e54070303d840e9440003020a4100c001010300b070090b56000220303840c10f40310041c07540700b0821030194250008a800c01c031000d41c4004e485801c40b00c200070440e481d12002e1000f4910b52044400940501a03404001880c5c0f01c0803019600c80c841c150166501800a03404100c62560b217030051907a2007600307100500100c0c0c0e541e805004418800c0c1003151a00d030800307030b80f0f10441003540c031310141c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 883778093 1250 883776843 883776851
    0xb180a140405011d0f0a06110f0c06061815040c0302070606080c151e03062d040f0e0a110604030218240d020f27040c05031c030e010618 60
    0x1d500f000f2041000140d501c01001d030a440d07056607034151b00c45422003009089207407108840d520030f100300070407200d90400e6070f02825900c5031107480e4a501c6520482d5090322406084040807810140c1c4a09184908001300c0800044003d9808100040901c541c03203030100360b800d1103100001050b511515000d040d494004041ea214007104200e40300c0c01003542010280002d10180501c11b1894031000d403400c146010654882e40c452002c81c0e441541d0300106003016914407403450300306d00000090910140107490038401d80f4003011072181035411148a54182e648002032040c00b04609500d0454118030007000d80303140541e65000034070941c24940070003015540c00780134003503078504c821a041648201c90480c1c0081134030a5001400e40c03007004e035020f8010315010010543c9a92690302d800182d03048400c1c503400103001c80c020750414040440342218500b610701008601442c000a51144041c081d0341031001c08030316980224094003950100c010950340794500404e1044003810714200907295040002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 883779343 1250 883778093 883778111
    0x60d0608120f0307030b19090e01050a0b0a051903170c0c031501060e04060e07020703031b1101050708090319050c010e030304062d020c10030b180a14040501 69
    0x1605141105801d000c1401003042100c01c10144081900d50160050900151050300000801c9007602100c0425144100142c0003203022220356008080100e6541d008010558940341114100c6040c000b030795902c90704142003040103181650600c030420f03030b5540c6000c00c502d550f595003144150046810074210038000c200041d01794420002c080c01220304500400002c05020722900e105a010b000e10003c00c5070800003c1855140d5400001c000c0c0f110300c0c001100b501c0c1c6000000e49440e000c0c0001c8000904e51215040d01041019800510366013080340190b031303084500e006640c594000c00d07080710030308028411200d03265000d12180f044a0310b076005800b241c058500e0400e0070f01110402c40d81c14025007010711507054900100341c42c156126406d1102c41c1c5000f81d88100c0e01c440c50200c080601c290001c2d140303c8420790200e5800c2c207808054586040d40d0000c85d40542c141c4914010a90f0801d010900309450842c45480319030f00310000c1c031000240e5000303114036094600000c0301c0607100da139100c207190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 883780593 1250 883779343 883779359
    0x1090b03070b190f171518012306030c1204030c08040306050a06080f1b030a1e0201030e1222150905121b0f2101140c03040206090d060605060d06 64
    0x281d0b41a05250201780c030305a080340701e251144013403e20061030b24484c1c2003881c2d03a104c1003114901e0709601210b00600d581e5078106d54a0410b161000141c0604070411104180d05001055900554401c480c150070071080054500d0005030080042e01001540400030317011409005c0180041c50140d54040b9681c035003030804c01c0596940b6841014540d010340404180344801180c1e1900311440901a201d001c082c080009191180449000e01420b100e90801310010300308a09400c180c43c400e0b241400310710903118042e52034156401c00320500352000c2140074080858200070038183e000c508150100b84d510341045103000310354184c10001040200c2404c2c0107924110300a4040d02c8116001000343c1d07001245d0180310910082c0d900b500481a002c0009180d070b4641e0504405e4681200420104ca07080a580d103010f019002d80c110b1514440c800401c902c0180303002201d209507005012a072818000d8810b0000c4c40c503900e40d0954023540c0d40c1300042601c2d0b940c1c0d1300405580c2c0600310b010403114106801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 883781843 1250 883780593 883780607
    0xe0c04081606020a020d030e040e0a050d030213120f0602030a051e0c0f031b12040618080a0c05100f06060e0d0308040f03030b03060a0207060c020d02030301090b03070b19 75
    0x1900d141c400d22031000704103081d40056007580c056415120946100e00b90300d0300351802d0031101d07500e0f54084d00b40980307101a071f0382c002000600b050041040300c4070300e401f4010907070803071180da640740a4171703080c0035400d102c03000340c1601500400340b080009507a100102c0e1108012a00306a0784400419100c074180801c040b02c4074140e4034910a4a0318940b014104034035010018482d4400c5071141c244040f00081d41e4419105908502e00285103980e40c0d0303109610b4500201182c102c404684651a2083c0c1381240026480c2c08108146e000048a20b07010b0312500c143d40c0c841c000402110a44038001060707151102a0055488454072001c001c221182412400f400e401407050000d40030b0342d8105600000319500c440160380290300120a084004400d041c11005071019501c0d19801d44290340c203220050704507034024046c0a02a58080203a50785c480c02c100c0c0ca8030401e610b1080103178010300061180c46502e5000c05520040201211840da5440802a000c2d0300b011003a2044c0443c640c03d0050700981142d2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 883783093 1250 883781843 883781863
    0xb01060806031501050103180f06050609100605090d0206071a06150309060a0e0a08070305040510020c0d0209180a0b070908060108030406050d06030f1113141503070e0c0408 76
    0x241c800742010760207440c0240340c1403103517504140d1200e04400314100405031103a038450308030030340d044500d070103003882009400f090300c601c0d0281c208400094202c040c842e40e4401a105155140c4d481d10215030208841400101c2d0140c0e80194208040c03000110310035031507103001e031606807050511f02c3e2000401142003040e0310703c0241c1326810070810144013000300340d0302c1d80000c0c01040003034030a4540240030f1506086881c0100b0243c4002803650034141c01501900803520110b65110003441071510803a10340340ca0b0515a034000108509c541300502d0100942d039403040c40022892001e01031302c3c000034a00050f0b42801c4e40d040e20b45906124141d80c0c051800c00160030204014080c551504444d203607244600c0c4940000c0110208000c180f42c81240c00400003160004880c0d0900440381c24444050090038030442c2c40f82c0060744e503070040304200c0e000c1c2121100b1240d604411036610000d02c0799805c0c7d60421500d0740340c050140081048580383c281d13540641400e00f035803a00d03641040300d00d0380b078a41e1902d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 883784343 1250 883783093 883783099
    0x408030a080f0606041d07140f040503010605010504141509030703140706090b04090e03090607110102100c0c0609060b030a2f10050d1b0f1403090712031103070b01060806 75
    0xf00c00c0c0442d81000d1b14406071200f00d00f01c1e0100b036540f00744045034180b01004617820403041c0015090b00101c55040504103960f001c6008016055072107005455501c1640f05640003000403180c80d006901d401a4000c031400b48080ca481d1a22003448006814600a03400444402c013030041828111030003008030b200540003d00b4076140480c24400709109074081c41c410240c8031130300c1c0e03140e42d026818140f0680780e24400150405441301068a8007106120b45c201c0c205005100781c000c0c03600521a1401401403282c0103445175100780000d0780311007000c2c01c649202500d4254503440d1040d031a48003000b1a88006004100c031020071085240b40450200c0071107032120362242c01e01d0420001e9a1141810180c1107071a0910035075604442c00711001034580c09010f4040483d40100101c460758015525840d4094140c4da41d4140000c485a0200d03a8001583c2210300ca9000c044207200001c85c109602d4038550290070004800380105204610f141c0c0942000c0740d00c13150080c01004a00d030080c1030302e90032110403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 883785593 1250 883784343 883784347
    0x41d03040e0a0e1f02070f080409050a0b0a06120b0306070305040506090102030c1c0e0f03041e03260d020c10060e0906070e01120e0d091d0c0f0408030a080f0606 71
    0xf4030315284c0c1d07100032203500d108140005090002c3d0008942c111000958404201c4000c0c1d07040d0308104500e84c000c0d204511246007010002242c07146c0354130130381010b50b1000389038154942c10034100303d4052126038000c1440c55034450541690340c1c1d0410045210b80c1c10b50b540820320380b500d840c055040c4103002d407500030560700620900c0300d000b0440050b0307100403490101c21811440d8000408015004400380084a0300403550141e0740d155012001f48156058a5800406580781e41c4d01c40340d01c41094030000e00760f800c01d44211101e00c468034042a0f607107020341d0015030030583c2d019500c2c01268488217680c0d48a510900041400c1d443c0ca008000007014895004481d52500e42c8515450788070003480f81080140304101940b00b42e000d01401f5502c6100004c00b04014144c4140450307840c03a00707260b02030210f006a500040c00f503c40c20900e81564110030f1500605407074180122402e13070002118921301807001e200c0400c1003441080038060b200350903580e143c100e0400007220340b001c20300070303200c14007628007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 883786843 1250 883785593 883785611
    0x30f06090b0a120b04030305190207061401050a0b0d091110050712171302060c300a140c011e1a041b050d11120403020f0a20041d03040e0a 61
    0x4d080c2e0b041303521030381609004c61540d441c10800c0710349a01c1034007400d10007031020507090f050103841d03441103140e20181c1c08840340e580d8842c41002954002441031075050101040991141122a00001102c81c495405108508800300016554a17106c14400c0d0000da00400d0440074080391450014001e07500d0300303000e41040300d01c005010100300010303c004454004a00c5100440d11007408440386c614000b800d0b904401240c0501a540c0e104501c9a130003403128068010314000c3d140d0040b210f4812094407240d15501010702c802402c0d40146211105555070b0f001340e0210301242c4050020074009400d0b0018404544451000b03840000120150045180000c41d244501140d1005141240d050a00c0c503180d1610030f2140010340003d80030482340a0000c509030244000c86011980103034820303000d841d80014040d42d42680e59408540150500600f0b18000c04a500e2101c880c010003c8050f00110b00d00e07006680b042d031800f80b95280880550320020703040156200d07841c009034114041341d0052140c600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 883788093 1250 883786843 883786853
    0x816090203071b1b090f060f08030a0f0c08070b04351c0905070e0a0b011b030c120809010c050c10150815070305070f0f0807030f06090b0a12 62
    0x1044400542000100032004080c0003e11400d003440c401d1130f0320101d00050722880500003800090500001103030078090080b42c0d595641c00001c0685849800850920301150006c944518030004400203004503098041d010901c0341e8000c20306a802501216980d040c2842e00304400c15003080d81070f1704948402c2c0442c1e814801c9140341c802c0740440c0300a840e154204540d4800c00c0c2022840c0c1a81d0051800303208000300300012422600f02c900188001c0030300c3d40e5214000042c0d4000c0c03c480c90000b8030003c00c1414164102000c0082d03d8024904200621707985e039a03804015070815040d8012030160030030030507202c03000d00034074940d681c40b850514201012140990b547d0f00745402b405021549a40d81c40b401503111024440040c103442085403071a04070000040108842a00d45a00090a042c009980c1d00e01514004051044907500c003001131650040846682d07002410703000401d074132081c281d20700305198054079003d45031496000904041704010800300c40e0243d0b010340b5515900900c0c1101041c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 883789343 1250 883788093 883788107
    0xa12030c0e1002190501091205030c0702041a060c0609010c090602061618230603092d030c160e0108060112030201020d05010b0702010e1e04090c0f081609020307 71
    0x4241e42c9000e85000c503410582c2040d0215121440c0e03001c0480c848800d10005401521109014841c82c12000922680884440c4801c54044020b55000c000240040c1855408000c075680511070704480380c0944d40026885034020480c40740d40b540300d034050040d604000e100c0c04485425604003003d036945040c4001e900c881c0d00501c2c0d03c0381c016000c5c1c00104442c0c00f4000800306a400d00c0d00d44404c0720b49540003e81c050080c40810f80da4100000c04c8030300641016402c0300d008a00f0100140041c40c80f480c04050100030325590f40c01030f2004490903e0384a00100058130040b00e40380e01038240044c0d00d8415203524041c2c3ea01c0400f078a80700c103004000485020071030605541845070139158403600750809034064820380c040502c04d1481c0c5000002c174026248040d0910500c01d988200d00c1034440c100304460402010841e13280022000a100365a10b080d90007428090712408100510540d031302c0003001d040703080d54001c02c00b540100e05844840620780741c03000c004d0803510b44114150304200c400100b603a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 883790593 1250 883789343 883789367
    0x3010b070615060c150c0e0f0f060406020d17061c1a0a020a031410120f05030f03070807090b04090c090306060b1909080604020f1f020c01030605120a110604170a12030c 74
    0x85d003000423580c08585552a2000c2000006403090340c0c4c80f565107000a50b107083d1040081d0014142c0041204540800c102d0507008900003050081c00c0c4200760080f421007034180c18200c1c3c13040c50800b1000b1103695400f200500ca40d41c140d00c0107864900d8101c015040c0c40d50411219118011601042130b1800e1038000c05003942e241b0404449240320919080815001c40000074200b40302c0411411030804c0d09200452107080c5c2552142c0c03441e2a23801050341c503014107001c0d50782e200405010a20400b2150390048203141101d151400d1200d0741c0c0c0e01d8401c121821900710b0a0302500001d640325209854080110910070107140600c03090b8900220a900d4500203080244600c40c84400d201491b07642c1540881c0d504420040020703004150b0030003960302d103518203015000c0b0b03041800001d000e01c0d081c03844282c00105180500090082c80d0354452400c03582e880c0040c0d2041040c000030425603103c9283c0078008005100408903072016050243c181143d200d11402054200a000000c039130b800300182c202 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 883791843 1250 883790593 883790599
    0xf04060b07081b030304050303041106030415020d0f0f020a0f080f15040f180b011e1a0f070f0204061710090203010204150e09010e0c03010b070615060c150c0e 70
    0x40c3c1c0000105403000c50407040f180740c103910000c01844184040031005500580c07044003000641c0d03032070000b07100035800f04840180076074404590b4102d0202250f00101103102105400007409407800100804840f0400e442108003503000c240301081c1a004100d00702d40c031509050403a040d141481088504540062034044030501e0f40c40302e8083c5440b50341227602c15002e201024022182c8070704003006d202c000703c1401e40d840b02003440005408508460a4003108000003000380400b401d16650a0f540e00440c444514031400400040e101e1040007400350200724030892526800f000c0d1070040205489298000e401401c1c2c51000c0c070340401c8400104004411406540819015018000280240281c1c0d0100340301d500c05e0b0f10031040c0c207a803002010240000480b00e0b2500307662038a10004000e0401c07600681c8504d010001400b400301c1d04130140440b1340c820080480c0d01000101c0929a840307240c0d126401141c8401003030420802c0b035012032a80350080c4d03503003080300000840700105110401c141445c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 883793093 1250 883791843 883791847
    0x51003020a05040e040803040c170c0f0d0b0916050a0e040201080402010e1905090c04030c17160b032508010b0d0605030a120f0c0c0b0a12050c090f04060b0708 70
    0x842140034809483c0108200410036030285014200004607034002c40c2c040380c0d074055041340401d100b2141c18601c2001100c1900030050040c0c65001d0220202c0700c06400ea500000c80210000001d5003c903142e40726080c4000907226014094650725407500d000e402c118400d0f1800c980c14020000c0700f94040b54420780910f08a051601c5a0006035800c40c030180440360403c10300c05c600010000c1760320301c00b8121a002e1b6002c45441e95900c4490b03170140101e0200804448654000b04504e42e9400040500d002d5000b00303480c01038021041301003035100c03a58091800040f0200402c0703a5407600c0038607100032810541c6852410605144000c2007000140250294804040741503c0c0074511948a4809401e01404451042043d400c7c50304448940002c002d00140c4610300103403071036224000f00051954041101d084003400c20f045020301d604941004005c0000c000c441c8403402d20075004072405007041d03901d9030f951160703074400348402d0106036900d8078007950074000b0400c10040410700b2180c11a8014034015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 883794343 1250 883793093 883793107
    0x6160309060c0e0f09041203052d0609070c050607111216020a12120302070f1b0305060a060605030103082b0e010b1c0311070f090501090c0905100302 66
    0x90000e016030003001d481c8a00e441c210822441c0c02c50740d40c10003d40e00700d42000010345050100701d1454400c131401400400810311040109000360401c6400403150384800314104880449404407140707200e500011b1003c5003081c04403070700b0241c040a410249a243c4026031607003a0711060b0b030f1804040c0054081244036410000455000d220008078000079400c0d00703598140d03a4684e0b082402000300e00741c1c866400080002441581e040b00c0608a40c0d00032512907841040b0391084d0002e40081d901a6242e800fa044088002254450020440091007602014032800c605099140c040000c11403000c0074503081c024000680c000058a045a0740301241503600e40094620302c0300300d0b0208040c10150420351320f81c0a14400290004210307078103510001c01410601104203d02200c440c0c200e0300b900c41c032076403031640440d1085000d4504960a0000c4a4146a5a03510209136244640c00f00c40a00d89d01c0b401800224074901031146a001180740c400c00341424800040d620600c54581c00b810315030300260301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 883795593 1250 883794343 883794347
    0x3021512060d0c08010627020712081e04060207060c090602120c010e12030a0c02150f04060b10051201080c0609100e0a0902070506100b030c0903010b1002070f080f0616 74
    0x50080c0c26204004d01983e50348218204000008281041110001c41c13030a10084c9154401c0d521450303000184ac004204940c10140d5003c6005401042c1c48503021b8942c4404070718138000c950180c1c0c499540140d4034142d0703007880030850300c2c6148420b003041603442041109580c006082842c0c068038560b1150703112040c5c084180100701c8bd00380f150941c05105440c10b030749a0403002440c403c0510040a100e0880c85603400c0b600e480400000703042249007440800c8961507115291503000b0300c0f807407002070070b01c9600001499000c9400e031034800094002030201d03d1500f1410f0340b0360040240200071b164801810001800502411a280707000e02c0e6441e01a640503031249014548001019051080715034a441044000c3c0d4400c000980386442000040f80d810b05202510000f16414002c029055440d0b407018061142c6c043d04150341c0c03540d250030a1502c5036580b411081c1b59250640c00405e4020719041b0b41039505001c80c0c4c081c4083e40c201d00c0b444002c00b04081a416800000c1d10340700c10100700d8541003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 883796843 1250 883795593 883795613
    0x3030d0b031c030507120219030c03090f0b10050d0803040605060102100e03070c150915020309151b030a0c02100306080a061e1e020a1b0c03021512060d 67
    0x1c02d00d002c81000e0000d50882e0158007070ba0282440381d0340c441c1790000d103c001d5020f910454158083d560640030144c1d17140d92003503114280c060700e03a00d4042801d114540350b550100b00c181000380c5010b9400750601c00c07008402a5050000e003001c0d50041c00c0ba03121341d1603c41c518000104003501c079545860004503641e2083c080708040907015074041140c81000000281d581e003020340102d03400f120406011071405400e40c98000d0303002d065500c0d0700c0c0143c04c0c201c0d6282c183c0384001c2518258441480403030b00994405004800f03801060040c55241c040070b600032403d10510006e6046103801c10810b000c40320358010381e001d840740d405403013900c4401050442100100200e600c203500c203001d0b81052000b0003040380c001201200a00011600809a00b0524000c640b0881c0b941c40301c40c0440f001d2052540038680242c11601e0701c0b403c00382d03500c042d0b20144040400c03204000b151324411000d820720452a0035001504080c0c04801d5141c1403c10340c0001d400480000741c441882030390107102100810a0b0005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 883798093 1250 883796843 883796863
    0x2030a0209030f0c0414062101330e01050d060e030d1d0105060316060809011104181b0e121c03140606030f040b130c03080705011a03030d0b03 63
    0x1007154220703c000303c0d0a60b02c07440340c00c030018800c42c141b01000700c0030b85001e800e40b401001c1c018038810000b030a22040d180000352003451040b0a54941c084041500c071423001054481031500303641ca2003443c4404051148101c950011a100007015006000c961a82d41d25a0071142c2d0045001030940d0302e5141d12481d6000b46046030050724103100d4682200d0012181040c1010403000003880680c032504101030b00c4815142d21841c0c404400b510411840b4420313207605400440401c000940280d00d10f0646070306500640120405800700044120a2a00c9214410090050003241c42107114000001032041c108210f0341442007426005101c1040710901c41c00398008690b452280300c10b03803040000740c050448075169084138010980040d07850b003015001c4a2140510100e85090303036803507503140e100c600b601034440b524000c600c0001c0800100c040c0b01c1d400195004460941e00d959080c9045400c1d5951408200403540030a00060781c0340e100082a0342d040318580f00007081c18030782c91001c80d29100e550300e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 883799343 1250 883798093 883798099
    0xf0d02030c04170111090d1b030f03120605010503070c060f14160203031302060c1501121232070602130501020d08152101020a0306060f110a0602030a0209 68
    0x18492040704000080040f6880742102445600181805508940315003519040740e20082242d90160710b0841210700071944144003840000616800280da00074081d041203409034000ca440074180750b0000010f12044000c040180305080c14007000800c280005440c038400d2020400240e410002d0a0b08903203450001507200304480710b100685211403000c1510400b00915030a00310300c01862000c412a4445c42140c0d4101c074281d42641e080c04401da00101c04400c2c2400307060080203000e2031a0603454000c0007054000d500020040c24101c0740101d80c0c166036000e0005071510805507080e8002002801e1802c3c0f03080b0440130094418401441c4922030005100510001c0c0c1052951a1480ca40080d030b8403e07422103038070082005084c0d0308100c0503240c4e5000308660007002c150a2400b400400840d01100c282801052940e0500c00d0a80c3c100681c42e1002c60f4a46e407060000d40d5021901354001c114600d0a41e00601251661545031200110080c04064000001560442094040300d00710b84002e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 883800593 1250 883799343 883799347
    0x30611031012140f01061410050414040219110105060a03350c0f0c04051b0304030314070c0203010b060a27030c0f08010501120804060507020f060c010903020f010e0c060f0d02 77
    0xd2800c0e00d00900301d078002d0b47c6000c000f5010704120b60910380c60b00034098950380c131500d00c0c05040400704031800d511001183d5220707800b00030009904281c0034290814140c00d884d54007040000c500c04609454004028030300a1540c4441040840c0c65080440c0c00f0b031200c0c0000815541201c80e201380c0d05442c000444620a030006a030312552800004c1c3e48592141440039200800700c00c0c01000304cd1602690000342c1900464500501b0321450b40055403c14401d05001400360400749047e22030480464148001c1151f4030f0640055050038000c40e11862401c54189251200f04003002d0444003010b1060b08441180d100d403c2c0d0002011400720020b5038000400d0042c0c560340d0240545a11060300400c1815402e1200005a2240d03c10400e11401d9205911608007810032200301ca0079042010160f900c4111618203c9154036554020410640c01200218990306a802d000e407900c1107040c05401d05a04d491417514003108041080450110111070280d80e034a00c61314581c8141c0100b844d10034a003840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 883801843 1250 883800593 883800613
    0x90108031201080c093c0402040c0f0807050c0c0a03060e190807030e190e090d020a120f11030307081b070c0b03060114040b0403061103101214 63
    0x800000341810030a0040148a1a030326020300c0c0d40c5030803a02008940000302000030413410317a00c168030b80109100420600ea00d8061b10801400c1001d10904610088103903a01031000b1341c14940121110a8542d00b8280805a150700e002011050010480b10400c0004507882d14446414000000704100040c1900302c065100e08080c00117092600f048010f0788100b001004000102e04500102d05401c91940c0381401002d032000d90f00300d003108980f180e000c002e042d080180a030040030502c1c060030541404e011146000090949801c000400b2081558849160040001c040e00c00700410010340f4907008012590b002c2d41a510405a104400c0c01400040100105141d1141074903125a88c0d0514030aa0162110400d80780c03885022030180002d1803000c030070320680300254011604008103240141c03440442d80000480c036040741c1c105040300080010100140f0420b03000e400000d803a00c00b10203188d0306040200307001c100030078031603910010000140b032130501c000e00c0000e40041e40c1100988286200c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 883803093 1250 883801843 883801859
    0x2060913050f0a0606180e07120e010c020f03040302090c0a0302070b0705210403171b04090f1a0d110402090a09050711011a120a0215040f0b03040804060315050901 72
    0x400c0321000d4019103004e00c002040d40c0301d0b07031045012407101d5070507204503030400d0400b02181078028000c0090101d80c01194041410034401d030f150b00c001c2e800c00000c043c1000c02c00241003038030910724801180e006110602c0540d0b44c00c0749058118840d4812507503070744544001600a0700803650054003000d6000c00b004909904000240782d03030154028070f0740a02400a095a9240d0300c190b60203400503502500c07020041c500c3c6490303a80c000f03020803441001a00c40c005801d01759400ba4202ca07040c5030f00c590051101800354099000110940c82480d9070000c03000010032000c402501010782881499001c40403181c0380d641c108d5000310300240043e42c19544402c2908040c02042d1200f800288042c28501810141840b0300100003003094900e0341400401700800000071006428070000740506c50b00000142c1c1ca02800690781901000751680300c0d8500740d2102140322940c2e01000c0034102c00c00400000030f01d940700f2103055404600b00080c3c450007846101641000e540c2006410040000020030070075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 883804343 1250 883803093 883803121
    0x20a0809010c0c030c02100903141506040c0c020d080405091312020a03020303070e061204050c03071502030a053108010b1207051c0503040b040504060803160206091305 74
    0x9500c90000d100b45140c645049980c0085100080c000400800040b80103242803510220110340a18011b14155100e40b601350b0303a6030f800801590240c0c0001c56100e20011700b440c4055102001316002c10060000d010050064103070680024495034180d03111b90708000705002560054000035160b0303401c918010f81540803207503500009842000101e81036614481c4009403191100d40e26074050341c2181c550110a8070000d40042c940b943c800360074001490440d20b4250554401c0d4080d80c0202400c40300720301403604100550304500d11070801500d030591020703000022100326008c246000c5c1da17281749400e04440c47e40850b0812029800481e80c010302e000303007508600c009070f81d4071800801003502d148080002c2d881c0450b415030500c0d000420108000d282c044164541c1c0007c014800c10421000d1340d80e10f055611079044080219000b08090006003824400d9601a00800005524148101e03800d8414004c1c50344009105440008002c0c0440c1c803000c0300320b07840c0740700c0801c24041400d00c100601559 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 883805593 1250 883804343 883804351
    0xf03040f02011407260403060f1b090b07030509040b0d03030c020d051e0c0a020303071b0e011d0612030706020304020f060a20011b02030c060c1905070c0801020a08 72
    0x14500c0f16080038900c414812520129801581c21001400090500401240c3d0204a13a55490180800404141c6a00600f00002e682400001d42c0c0c40c1c40c1c842052a1941c58410501002030710f000a005145c000011142d065815082c02d684031501d001c005000f070021488a641c0046014141408164040d002214002a1a000e5034000e004151046032603014200d5500b0b842c02102e05900011100e46004005000081c8141c400d4500141c02103451907001e560120703a1241310312408c80255203040e90b060301500c0d120594440b2035152801c105420a48881c12000c140301c0500410010f0766488000b080ca0301c0c8007025240c848506041090013034004071026405440c0d4407041005502e01002141c281034020386a10030a00b80e1080b90f00a000004503081c000d565072069085d80c0c1c0b19880d0140c0c044d112040d40156a681590f08c889410414080c0291101800030312410700f10307010207100c2c0c41d4102584e2814a4680c0c0300d0341408290386160354041c003629480043c0c24014141e00507065486 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 883806843 1250 883805593 883805597
    0x1b0c060201021b0c0a060804020f09011e0e1905151f030b0f0a210804030c06030e0105040b630309040f0905010501080d1112120405030f03040f0201 65
    0x3c00c18451052644910407040901d621000e03007030b070600c14a0b00509a20b0b030094005011030410441e01d42c00724202c980281c0010064150f072000c008901c00b06d068900019000c400390b9581d490402181302c503010042071405454481d1900001980d40c515103c201c440e4520041800070803c505200c1e203020580194411800a42482440e0209060880c120071800c20060240c1c18810303d46648001080f000840c40400042a170307c403500411030600180c8080c502a200e9100c03d1031900c3c0000d4101c032400c071340c1c2c900c059050104110100703021000f065800000f190586000f01c0101299a00c4081c03202001000e5190000b03486070400c1d1815411f21407400a80d0900040f2006a41c0f0340c2e44031003420400c0c0b03001e60b204205202e409d040070303007040c400c4106200021420b541a59209400d44609030000c404c2c0f0303400601c1a4000b10b51080c1c07101e0200042c0c4001d480814000007940105225444551840c401c4001c08035003004070820441d1052102242410b0b02c0c1d09251420241402c1e0b040c0703060780 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 883808093 1250 883806843 883806877
    0xd080d0b0315071b020a090b030f030708040f17060a1a0301090501060302012303011202040b120105071d06090402091207030809100914040e160902030402030d030c050a1b0c06020102 80
    0x2150f007913200b03958010941c0003018040200d140c01140005824071084081d01030141030005214240100054094540304022080c0c54600300303126490040c2c0795910a0000c208500010b6003100c80100360607420500e903810103c2c4481c41d0001c25680181b4004482d03403d50b00e040c0c10340091080660022090764403d036501b640325007460740409056940200c04916804007080100580c1903580f0310402e00c81c1c4040d002080845045001910b0400c902400c0e11b2141d4440f000c005415a20030b00803500c400180b0180941c155008011404a000e10054617003c0c65002411020303036900c008a02111054403021141810f0312442c000c61a44c0028074654000c1000c0c80c1d4003d40c0c1d82c042d05200c401e075000340c04080c903244902410400501002650446507000340001d200724000600c40050140603000805030b030340d00f40380c4141494130b886088140c04061414a07060000c170f50000441c1c503512040c0c5000403580081040001d81010300440c005c0030324880d4080080c40f1601900900092540540703070f44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 883809343 1250 883808093 883808117
    0x5180324090613031706030709141603060b0a050d020c01021908062d04110c01060302030c040209030c190e0a0e0610030309090c02032502090112020d080d0b031507 72
    0x81848080d07072001000305840005d003699a00c240307440c00354042c000034119095240d481c4000340844000500c0c485210791640b0402c20002c203003e4642801408a14042000d00d1500700034908501451207484204800001c400c00c030810150143c60142407204004c65a41d2000350b100004100f2202402000c14440c01c00034038103141c90f03102460444259a50120441c0960310700d240400304c6c854403140c0c01a911a00030641c40031103001b030580b0b41180c100004207141140100b600d08001030000a11607401001549031944000c0340705610403205030790140c0700901c0b260031044248800c1c0c1007600c2c040300f00790421440d80003581080d54180170300c2c2d0a03100c1c19241c25610303565501d01400f0103008140301c440c003040314904030740c02402034040920541c3d04021207002c898034180b440e101d9505407003111042203c01c1d07280c02d1b40342c2e07801482c80782d8070013070b20010326404180c3d114400f03103002c3e22504010a444170304080b60740122100d080010265094042011024641c030142501e403a03000602101c413030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 883810593 1250 883809343 883809361
    0x30c08150c0909010614070507290705031209100c0c06140f0613061d010611031305130603050d090905060f1c02031603060515060703051803240906 65
    0x3504141e001600f0034107260300f880b07829586404040c214802c800d200300500b0000c0748050007094044c00c2c102103803100c1c003005908880c1b5000442c4082485000d0204034840015100204981d207610400b0f052200e550b6410015504210901d0414030945042407a641c8426622000840100344a82c0c4200142003211031412205034086500a0b029000c8102145040c5042c1d02c18034089040c80c10042801600c07558401c15058040c003040114410420041c00099040f90003c10381074509001141040404001030070543c1c02880740b00c0c0140e072285040340710321180344c0140010b181c0110413241c100b80c0610f0300400e40d0f00c0910581c0300c007500d404041200c40c034100d4803002c000340c3d00a00e2510290354218007040d56040d10315040340d0501c5180042807000000001c010011030240d1000503540c07410140411013000310402d110f108800410084001a80140555a001d1717100c941c5a0b44015034000817030310740244044085a20b0708140201515000c07017224030740c0305901a40a0381c070180c50384561 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 883811843 1250 883810593 883810597
    0x1b0d0335010b04060c350318010b09340203030a0c0203030903040303051b06040807050f120a051c0612060609150509100e070302070b09070303121104030c08150c 71
    0x60100000c042c00306580210300031806106d10b208100e1800c071141441c07001883c181040080041840ca18048108103228030b1151801b880c14403900000c0c80380c00700c268002502c9580040000790010705203400d04a6480b092000140d115003048644500a5070881e00a5542d4000f2981d0a405a0520810050076031010007a24040e0041000a5091608680d001d1717950780c02116540078482d8800c159083c01c800200032450245024003103983c0d49400701d003443c80c200f03107030100b490100754451001104e645c900d400403940342d13480502d401d80c3c942c1d003905101151384001c01001c58056041c003201080e105440900c06e5201c5108140c10014580d0360a509020766030305255010a144409500300130364103002d405598000e09040001c1e01e0280c0b43c2826940d0400c007510400f0000b03078045440d00c00c200c1d0320700b005038210701010020950b403851942c0062070328645407041780f005a107501c0b1140b840e41d801000d5030055640401c148658070b0703c03540036503591509440d1050712894194040303100300c00300a003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 883812949 1106 883811843 883811849
    0x30b07030f0e0712210503011203021009030806100305010b04030206070f0f03051c18150929070f23070602190e031b0d0335010b04 58
    0x1400c0c00d40582c004a0082120491003610500c0c9406c1400e40e030445102c04004000000305107012070516240c1300343c4e40c880c0c504162081c420590004030681c0710388002c0c1d40080117030b640024114151202885002042d0300200818070260402c00c004011040c0612042c00b0152283d035a0300044400148003075000030070103c2c64108120035680c404c0348800c42e074401802182501109882c05810019004082280c03d06c2001c0401202d0b40010071a683c0101441c1c01e20400a184200890b20b502088484407a04c18000360003140244210b0401e050319665802d860207000310791207400e00d0012600d41052105002c0200000c019000030b00241518a01e4041000c0201c0405041001e08801151180e0454641001d840b1703800d5002e203414100460380c61103505007a00303040d9003c3d0a2400d80360300d04280540740c2c44071600b281030758450208514007564016039940ca450b4080c0d00441c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 883633093 883812949 := by
  have h0 := BRFrame.cov_init 883633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 883633093 ≤ n) (h2 : n < 883812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
