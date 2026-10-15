-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4697
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:26:51.779986+00:00
-- url     : https://prove2.me/submissions/1b0a6c0e-b599-46db-8983-e34987d5fe83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 844604316 ≤ n < 844784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 844605566 1250 844604316 844604329
    0xb0a0806041208180115080f0106050a0515120a0203061507031416150c09050a150e061201030c150804030906030f0e01050903040f080d020616030b030123090d050306060d020702 78
    0x1130f89102400c010440c10030240d0010000c0500c0780988d03030000c104050500c0f0104001e20a2801410300070040d8010310341981c100c01c41118044201c070a1020b120703007032801d1824065030055030181d10407880f035403102059800c0d4408075071040303515407a40c2c03999103540803003900b00b90803c0d02d101d40c41508821a01000c14020b003030110301b940700d01c50002120a0b001001a1070880e4a403c968010f002d180410310552032001103180545900d41010b030801d490000018416114050001c0f0700243d1400c00002001019501d280c2507506c02e0501907000c00c01e07001d007107555400403600580003892641c0104076040c003035130210700d00c0246004041074004503510403a09480098a8020883d40700040800881c0c0354003026101800500020b804005d851030802075480e1005800b0440302080c031141d40440501a512003410502d000d402031008030b8494882410752441019034180304620980002c2e0087d0300070503035a84480c02911024256220f550912815821559a020070307182d003013001c0c0c8050f07a64032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 844606816 1250 844605566 844605581
    0x212070b092116061805031b03011104080a05060f130605070e04140a0c02010207031d1306060809010e0610030816060509100615050a0c05010605060a02010b0a08060412081801 77
    0x200f40c45409245010700050410341324410704030380024414402e000e15940030912904280c5c0c41a0f07040003240da1480007a00410440c00c1d480035001002900090203035000c1502005140210103460181d0740d5400002c205400c02c0b104181048498414030001172066805076410030410b2070700d280117003003007000b140072284031010004884015404210b9664224000d58161060710310080d030501c03080d80d034050405d01c050500a110480300c040c0c4100c50fa101e144d031918903411110424081e50303980d0000644544400d03907030040c0c15400c0c00b20003120460005000c40c001d02400042014603407458591610315042540c9880000c00d075039441c5800702d0780320f0250501a001078405072062461240381401143c102c2d501c0782a825000c003099450701508142075074060056414103008009080c40c00b00d006103102e41015600c00ca02043c0b07104142d60540c1700000b03814040d0303207240c1015100c040080e5210000c64000340400015244d03108503a104250340e40c0c02c5900040c11712040c5000c08101070075241034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 844608066 1250 844606816 844606843
    0x60d02121509010f1508280812160306150f030b03010905070e090601030512030a020d060f2105030316050712020d2601090b060418090212070b0921 65
    0x403140000b05001c04d0b48100c0d04c00c1c4900c05900c0c0c00f00c0c0c0c601100c05031a000f03100c04c052082006141040603c00c04c80010112980c0d00140a031356881c80e20080100c202d00075191000c0c694024000e2102003030103441058140d40e075401c1d0b1180700c915103e10807030301045210800d004240d2944001c540303079207090007002610751107407001c3d0a01c9410550111440d40000704000c10541c0860b0042002c5100850043c10b40b0100c80704560b6a50342d60700904020f4400d18448602c030034541400080c1035194881000b080e1140d200801104010910a60403140140c0c5001341040d0020008100d1031124440c03540e8034002c0c58213045080c10299101d00c01640041110040980c020009248940740d00c00450841c45403411b840c6d5524100c02c00c2d40c544075070014011181490f030380e841c0e142c5295031010107880c0200a0003500b141082c455802540207000401000c901480c0000f03510766405402080d19000d0360080158a400c00d4400c03810010501d1080e00c034001c1004070484660f201c000c0500009000101e1f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 844609316 1250 844608066 844608071
    0xf060b0a1d0a0b0312030f0414060711060619091505090705041e030b0402090a06150507110a060c0b0a0b0d05010504020a0e010f1211280e060d0212150901 68
    0x2c0c103040b058282d42042040a2281d08040600400134580905a030b400609070a80c0651a40e9280350403802007403449180700051180b08108005180d10455105100101409440440e103685044c40701342103102b03e9003003100c4002001444400c0c55544039143c1840d40c10442100380d075807031020555071070042c4c80550001740700280c00d1182d00b0369019190080314607401d00c07407089865622222018203015000a1141004502103680303060b0641100000d441d116a000c40f00c007080040c060b005500a007000c4a0b40b43e01101484080c0c60034101441c00c41e24107072109180181c0300d03030b209841c2280040c003500e0519950400c3d0764081d00c524103640712540c400c0000260a080034010001942e0050348210350a109150051006200c610041d904841d464104504601146d280440151518071030554000941401c04090b4000c41411400d501010760750101a107a00c40007c0745801c0412034410340c1000280e200b82d001410420328400c030f4a00d80b002581c0b480304a40040c80340c2c800d41603400c00c0b0941e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 844610566 1250 844609316 844609321
    0x14040204121a0c031003020603150a0f0602070503151303180e06011106090d0c0218070e120c03120903010b03070b180d02130203040f0b0a0c08130f060b0a1d 69
    0x1402c603180c0030303080300925041c241189002810005500001e000003800f840d00032001c28002c00240d81c0c483e000d03501c010030055125490360304002070003c40d845044014401d104000900307040c01706401c19401c009441d9842e1540d00c48030208440c01e00450101c0c2086012003440c8003480840c0108030203010160388415190809030001800c00ca101c9220304c0050304144140a00c8400020b00c688054102d0305000219180c540000351042c00c1170802260216810005c00c03120990280c281400c1301004c41c3c18020039080c404020f40d441e81c03031802080e059070101c100c075410305480030003505200b02c0050004c92803140900c003113410056150b0141162000103d05004100100c0e150708030154000d90315003000040b1034000078402c0818140e880c4a80d640000860203100841c1c0c080c050680c0c115580900354284541c1003401413900c0307001c0d000000c0110000c00c00054241400861280c0c2069805142c080355803070340c000608059540c140d100e0170301c1000240d18041c88005000b504103035151807082d0b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 844611816 1250 844610566 844610603
    0x26090103061d19091401020910020604051203061f0c200a050d0602090a080312061c0b070e0d0c290427020f0d110309071404020412 58
    0x64046402608260070389120b08901103801e404800d80c004540e000d8400b10b00429000c000051110b100c015200381d10b0241504003100054004112144058076801820b040085003281c64860a581c01065074002d05030104270404048040c6401841c001c02880c020801056045030507a0012904000310701a12014414010200c0d6003400184405000314064032404c1e000644000e101e0041c580704200c1d0140c1d20f024051300f40e05642c0310a070090489402503449240c1300341e803a080503412400800b2444005190313420404100c50003000280009074030658551f480002d01c00d00248110200116402d009119540c1e03040d96045160040e0071210000d4200100c001d107405164411000020400c0c2c0c5010815000401310740803108007054a011205e5110400700c119520091021882400800d440700800324480080101c158542001c2000100d0b0080054050108a400500e16007114204100e281840a9031088141000b00010300c1c0944a0480710010703225003c0a172080002400148c055 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 844613066 1250 844611816 844611821
    0x30b040309051e040f0207020604121401060b0f1804060f090e01020c0303011a0f1809160f120905030c0d02070e0603071202011818140903030a0926090103 68
    0x5030030b040d5411010001214280da640741425800c040c01140c0d14510750802c1400d55054501d1998000d0010703580c4c658a100806a00d44d2022003502d8051403860707008a603000c1441070504683c2c0050f680b5040c01c5800d4200d0300140c01c4600e0b031900403a031808404403555100d10400d8041c0000300c0b1068980707400d0207203030000c03100400e641309040d130310402c0042090300001007581d0450b09842900c1403410071034450061140103020210b8042c260214026169030124404401c00004c2500d500005544011202d0201a407194204c4040340d400b400e04000d00348503029000c41d0410744d68010594100640d115482c650002181c003281da04410800b06145074180000001080c10000700d4900d030600c1c5001a803031380c0700340c8242c045229681c521001164021001c00400c0740f940030061448560b19809018510860f003400d800c1d452a11828103004458074407101c1c0900b103054000d6045695480300c850040c000d00d40700361034071480303440e0318003800c03a44071100000000b54048054954001d0b038000b41c107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 844614316 1250 844613066 844613069
    0xc020d02190506011202030a05060f0105040e01181112030705030702041d25080303100801050702011808090111030a09091b0203220b040b040302151312050c0a030b040309 75
    0x400110740080000480c03000246039040d1501c0340400080101c07603200007803034131020f000c00070001d0207a003041015182d4207040c0c080c100e4074161014040303001201c090a00f01c45440c030303040400c40e0300700c000c200114030701c2c4800115504002c1c12000c4d51000030260399145800044007201e80d54000a185001c41c00e003801044803143d40c030300e1050980101e03400b901d505d03184040c110900c810f115480c010b407100c0c0c40d04034001c0180102000d9950300e06101c0d8a180090400740107a0b0751640c00c0c4808540d0320362051042c40c0c6402d134501088490303d64580e5648803290b019500e100c3c1000b904009200f15950300744001c114030394543c1c855031007a51810b151803080d1503582d520780c02c0c0b20058503c00b5500715008412600780b40d4055001e030418400c880180c0c882c3e6083d58000091207600458007003010780c0c0d0700300100241c82c0200da000140c421400d030b480102d481501d1940c241c074007a00204001c001c61b05031607100054481c60665035042c0c00781010030b03001c0d5059441618840310350b100788000c1c9608040f0000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 844615566 1250 844614316 844614343
    0x708150402071121030f09060d06081e0309060403020d020301090b07050304140307030e0405060d0c0f0305010614010f050c070b1204110d020102031602120a1a180c0d02040f0c020d02 80
    0x1092013450144151603015042003041806000a0720019560782d110803992038040318201040302645640c041c03551200710310510a1400c11003260004c000c040041501c0741184014003840c50039080d07a091240d204024082260150b4039103078080c00141340c204825100c1c610300d0f40d68540364030342030600d4103996144480200303017504100244404241d12001084c034480c42070754003058940341c800205038218003c410142038104502004128042c03007003109021280910700900c261503c0d41e02c507240035030100d15494046030b01c004075564502d01131406450381c00c3c00d44058420556488481c9480395000d000386e10140040c11003044200711240717003d5840948251840042c100a0f0740c0040e550303100b041ca444075401c407141010f01c00c56841d07400807440e42e100f203402c0c0c9410b100c030780c42c000314003407541c1002400c07400c001400629000c25400741c00e03030301441d80401000d090b2803840500400001c0040c00ba60402c0d21902c3d98a0f00660b00e0056404100341540100707000500104020b061030340c42485072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 844616816 1250 844615566 844615609
    0xc1801030b06010518030601170f120307080c1c091502032a07020310090605070c0c060e0a0518040b0105010905130c02160f0602160e07081504020711 66
    0x1031000c00d580c40d1a01ea44003a00782032155503403680c2c0350202e4490700c88811055151150a00208038144040040828070050ba002c885003080b49a20302600c540c0c03520f201030a15041800048d040500c20810740f0380003c8584009842e145982e202c0380c3c0414201d07c1c0c000600b6440311801c90030401c5000c0400c2071a0b1080c80214114148121f086550980c14a50740d0902c0c000301c00030740810b135a480101c0360581e034024222840301103184601005401d000034140ea130300d440d200014070b010307005052200c00d0b103521072007000c07496080c601c007501c2d00c0720700078112500181c01c180301144035201ea91240203403000035880004a85418a40b1564412058028504001114104010540b10060b4000d00f80d9100000030429000a10049180519111740342e0304000ca01040060100c10390700341035060350116400c8e2403174024030301243c040486040c816503681c29400d90004000074481d40c0d099801c103294003103001022407500000340580e004182c040e00c101e00c0440651010b0300c0c00414001020a804045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 844618066 1250 844616816 844616819
    0xb07090b031501020c061b06090705132003071d030c030a1707020901120524130c03080339030f040f0f03080901051f1707090c020c1801 60
    0xd2405001c0540040d14006448901c501160300900c00c1007070548002d4441915011a070040021101050038071401c54043d51002c16100607001c1000c2003514000f030115034001305012590f000400e440c0720f4448400d907600d01380d80c0f00c282c0c00030300840c082c0c6184e6a07030703892003800c0380660305c580561140b81600ca80e0121040741d540d07440110300101312640001844420f51041c1e0304000d0340f48039000c4001c1d40400340100200d01c046070242c038414a20b01038011601001c8941c0c00c0d2507d5110000c10a480861866000480c0c01d080c43c0403a49034540310740f4024950f1903407561024101c0c7c0040c3c43d1000003d42c200c075481c0180c0b65406c40c0c04800c5801d1303606007442c0310510001c900f0701e02c006003c2040640c10307000010b0610101241d036005160b403100c01800318420505005110240079034142c040b550030900416465007904003807520462162040c0ea4855180c101b1140c10160100c214961350f000e0090b00140f103c1940c820407994100c186c0240950150a00c201300100d40d1707088000f1180c0c50720000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 844619316 1250 844618066 844618079
    0xe090d08010302030d20010203072303010302011e0302120406021918150918140f04171b010212090c060a05030121050d020c0103060b2b020c06130b0709 67
    0x805c03011440c81800c040d9111103640250f0200c0032840080050190b00010a0107080c540c07207002540781030b034100da03020880101107000000c0361000303102c0640099500c120071046140c40703010014140c40203050040c6410000c1d0300e501d03e464001c441c15100c075940030600051441e04480001c100d01c0e104d00d080114203c141c0e0f40c1e44110446409240c0e1400b44001040030454041c0d00a9070190444100c2000100c0c03280700c22001405540e00109403012881002c10407545020b8190350099502c0141c6040c5034910010403251030b0000a0b403001881c2000d4005607401400f0700c0148000785071a12041c105262010006240050320000240038200c1001480d80c4250300005403815606408403c003582c1c1540381c2e50106c0f850990f440034041f07000308e10341101502d030005030401584000b070b01d060081641d00d43c08140c4a0103040b2000c0c18049814481015032007250340c00d86d4500f40b12950050134108011020303031810004483d400205006915100144007010721415402001460080e003201c1c02c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 844620566 1250 844619316 844619323
    0xd030905090a020432030319030c05090d03120b0d0b0114030307020901030b04052a0f2d190305030307080a090c141f021006050409020d020105030901150e090d0801030203 75
    0x448144517103c044a05401c15640400c42600c44400901701e03621010003008414041000641c15804070f0316151b146000140120192101c1c481c0041003030301f0b00b40280d24180c880c07004d0ba13000f0352a0240c0e16400e49030f190fa02c6045103c0c2e000d0040008081942c1440e0241c0d02840840c803030b107803103580180003940040e50f4008030310703040da0740c440d0090b00162030300e01d05580340c07503d41d4003161031002a00d40210605500340c02e00c002e41c20300844242d01d400050a0900881241200d010a40c4220500610146a8280701c0c0400300311006400f22580515075082e1010a908030380040b1025040042441180e41d48400c0250708804580c2080204010700d41d075118410340244034204007034006001d60b51242c0d40e02c5404001c0b0301c3d0040c00c0c1c1031402e00900e00007074991415044010070b8a01d0034001241e13900346485514400390f40945218180180351300151102d0b0401002c104140d921540200b48202d610300e8404002c0c0804a0b101025051608095040a05030300d80c40c0c04204402004202582c0c002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 844621816 1250 844620566 844620599
    0x70e040f05070e0a0506010f11100b130c0903150b0906010f0507150e0f0a080a030203061306030312050f1611190f0b010b0310230d030905090a0204 65
    0x402420321000c561829034141030483d40110400c001c850200001d448140e000700e88034070f03026a03c6035507000640e20706940140001d000e040d100d6205d03401d800d0351400c0a40c488141050010260643c407040401c143d0300b507a0704668000000b400000701041040845161101086184502403081e5200071001c52041d0340d00900090404c0200115207603118002c030b0031510340e01d40100080c010018851303201001380850103500d0b0010302c0fa55404061620010036408003455000c88464585200341004801030b40002d0005544240303511050030a641d07640c496070000790710984502c440e07241300c01607082c101c0d0300050011408004020810000d103011440d101d10955031818101056248020381500c0c14494800c861424554210485c00340f02d401d229245003a80300d040220916a01c48a0580d0940010f4a64070100e2500c68803e22000d1001c0041160000d1680545000344103103100107140c8108110b401e4020070f9030301e003062005040140b41e03682c0c00034400000f549890f28020740e001451076407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 844623066 1250 844621816 844621823
    0x1906020a09051e0931050c03150a0e0c0d1a010906051f1e080f0a1517010f021801020708010b0d060203060a08070e07180b220b03010807050103050603070e04 69
    0xf120020b60340c105079100209800c506180105c004540c50038685d61514260320040d58030b4450030000c800300e80380000e040b0124245420901c59191160344189014141c00c103da00c40d0b5001d44801108591034040440d11081d000e10000d010340740c0c80d1040380e0030f102c8040c0c006603505424100305000c02d4591501c002e00e408003580c907014150100b0903044641d44051000b82490501070040e03076030101d92000c003250099107055154121a00e400140b00c0803075130345409008018001000c20041c82e0301c109405400d0182460002c01c0d40c01040c3c02020490340820550607000841c1410044956070411042014001400c0200805903807200082d4648889620051045400000040c510b450703c03403566000b440345070112084242c503158551150b01701181d9200000c0c0d40041c490300884240f0904e2411a5443e0706001c0ca00380d811820940352005a14114204036107810700040c05414500045000300710303410181c0301c1203050400060641d00040e1805101c0c5e40900070a0091104101805c0d420a0380b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 844624316 1250 844623066 844623079
    0x60e010c03110703050d030b0307090e0a02130b04050f0f0609012603120405150a021608072a0512031801030b010c050607170a18060b031906020a09051e 67
    0xe802e600d03549004801e4100030440d01480110814558264200c14101c41040b4156000d0b030342ca40c0712610440d107400d0040081640441160005400c00300d0280380c0b042e14040010030f5880600c00880c0540303205940c0b502090320044100801c80500c0305486401480854490046503d042d440990305404800c9441d20f034050b216032600380c100104101e901410038040760110070303c0c150502a03100c82c220720a000805402c174000540f2080d803882160030a031524090400c000340c160315240401c1e0440720003184c0c2d40702042e00c0784001c141403001640c5140700f800103c0c07010506010500440d031404d41d03400e14859000303201c8004419a501400d92a01e0340a2034000703825050040102e403591402040a48580181801e0040c020b50000d01d03134981101c0000058283d8541041345000c8504aa001d500d510300c80c610780900040c0c1c00e0704820700111000b0126103880480f400301044a030000b1500325612507002900b501469042072085d0001c042c1241d40002580d1b82c0c0c40080c42c40c15020302428404c1a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 844625566 1250 844624316 844624337
    0x2120a03081b090a0f06031b0f08040204060506190f0302070209011202010302071401020304120e060703030b120312090601080a05030406032c010e010b060a200118050a0606060e010c03 81
    0x4807510281c0d20300f6000107082c12413066440c00403441c0d10080780240d03800030741800301d900d00e00e07826071100143c01c00b0140d84c0c480d401f002c542c42c100c0b41524050000c82e4000e49441300040d40740d0b40c0d040035008036501c4202621403001c0320030002d42141c0703002e0301c20424503005009800140c0d0f54896403034111692103082c2c104890580c80103e00902c94003100901603c40040e03402d45040c01540610700c03c6101e0091404a0390304580e0645020308064a6264041000c20914002130b03c00d4110700d14540001c1c0400d020385414401c61400e503000324800b07900036240718040003500d60081000500410688026120698260702d501da00d0b88180e0140c0780502d6150522000501021010702900880401d189501e101001042901805000b07880451942c20000001e17402e02c2d15000301d94104032640c580385400403051142c10510401011601d8843d503071822045c0c01700c24282040030b079491181c400f402000300c5d54030b80340d005c81740e058101104124060020740d00690300052500320107901418100e4001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 844626816 1250 844625566 844625611
    0xf0e011812020d1e170f040b0a0c05030c0a1e02010503010302060a0504051e1e0f010f14040b12010608090d08060316150311090607080913060e0402120a0308 69
    0x1c10801d001301084030050b401c3ea5400020740702c181900b44a0b440380380240200c0e0440d41c01901440c001010404001c101c20041c110f841002080c071110141003030302c10403200d81c8034142507070001c101c421a5900711903000000c010074202d010320400102119200d4000c501d4000a00d580014000240901f00010312428481e00510070f40b8000c0000910b0910300c40003207403074070000550227a000c500074000c4500c0e0704040310344190a843d00300b1002d0480c1880d214800011902c505c1c80d24110f0003409010b4040681200f00d4030020405800142802a41d40500c003084410342c41c4161310940400410f2420310980d550003154603403641b078503480c00c4001d988400380028104012000c11503448030bc450070000c0c42400e100907070341100b00103031020041040c42042068540c130900c1441070340620f007004841c1c0040e038200040d044440001e84a41603a01c0305071649011100d440e00028004814141040218600840c10500e851030b0702c4080c214502003035030040c041c3c2c0800350410010082142003402807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 844628066 1250 844626816 844626829
    0x70e0c0304020a0e0709090b01030902010e011412131e050a0803100e15040c0f020726030a11011a010c020f0301020f070b09010506180a0b031c0f0e01181202 69
    0x141c440429113803014200002c002d05405a10f21034012214180380f2041d011707600911441a102d901031312809510a038020044481090107850b00601103818846540643d00301940705102d0124444540c500340c40c281000d045010a03131800018941001e201c0800240c00480c0800c1500d03480382109440e600c0e001004080385d01107420001e01d16840b0010010360304c42030248513803000400d030340401608000c09422250100c80c541c617000540d101107402c008001540a0058440c407050f48600711204d2403540d91400e541c4000c0f150310009074000e80791040c1c40b000b8400e9103c240e1407880f542003010140400640f040000b450003a20502c1000380c2060580c80079011298444109035404c0d565148501e003100c41c408003603071090510340c0382c90000f4882e8180000411200e845020101195940d0030b966880608400c00c01160903000d0b04507071501041c03401c140c0c480341541d41e858011000e041403400a012080d100c41c0c1904015200e802d601d02d240d03c1000100a45400603008060340050b0b00100d20b2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 844629316 1250 844628066 844628069
    0x7030906050405010b041b05040b18030a0b071d13020c010603060203010f0f090c05091c0b010b070b240d03020c0603040602120906160305070c0212030a11070e0c0304020a 75
    0x800c9060900308070402806500400250030200c80401c0303155054643c1c40c04d484a000f50030b8001c02d00402052148003181005000c0069141503441c240c0016a00800d0038140050300858a40980c6001d102e4030581080710001c042c0070201103000210722080004000d240e9140c0302d44030742a0f0001d00c1c070301c86200a400c06405580c020f0340640d83c2c1c2d43e44254008400d0118411142c05841003180841c94410500580c8074180c0d541e40c80a00380b0100e20100701240240454004108640030540c00028222850b09402400407180e0181c43d00c4e920f062140107039030010260900310903850403842201000968034882003078180c0c4e010060341043e00d402d0741341012200b40380c0d6124202104005c104400e40c0c00070051054040c403101119110480d030140c3e50001916511075107a0f0f100f8016044501c0399000c254003002d01d1900600d8a0380701e40205030081e5105580004507040000c42c02038a0b600049440c0f0405081002400507500e82514941c031540050504140c4200001c0480e0940d51070030381c1d400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 844630566 1250 844629316 844629323
    0x7060818010e0c040e0303010b030109020f0409060608101d040b090708160602070617240405040317010f08100e0102040807090203060a060c020904020112273305070309 74
    0xa0142001c4103580c0c800c2800f00d2403250341040003080c6132120120680303040300d04130034040341076134201000c040c060b400c00c410810300c2400511001403000e02c1c0780a0b010007040035485220141c2011214005440406d4000301120020345099880c01e0103e0030241e640240c101040d4041600d890724414180015a48001c0841c4108228000030035083c100c008200c800c0c0f9022a6501340d43d0b120203403165404018510302140901000415050400d8440030805030140d800815004500c000641100d00a4400f42e0028500040c400070007111031607028091700303019030854130507450b11440e141e60b504083c030b800030348a4660b00c41e903801c10025019100541034090995070201d41343d4007184025081114114803420724158001416801400d03080d00f09074014291b00001c0e41c3c3e0f900155000c0404441d50303038015683c1c0c0707079410307644001d200d0110400c83c140c4a888907100090a100c2c0c28504005500d40000c2640e0105040605221003088501c401c840c1c00464690ba6403201a8000c010040015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 844631816 1250 844630566 844630571
    0x6050d030905030d02010e0303070f0306050a120203010c030506030a140c0a1710060b0d0c021e16080d020a0b18070311030f1c0507020a180618020a020706081801 71
    0x408058000341d100e800d80c1c0301541164015034521000f24240c031303503803210140c0c242c000700b021a00c800e01c51000c0c4186907075242404119940d40b180071610ba400d86034812112110b207000d0300307070031883c0a00440910b00030b546418451400e2030b000094640300d03000c400501981c0c1076041e000a0540a00c030304440383c0801003400040300c2ea12411005c1c6081c08070101d40e149e02440302a400d44116521580e01624a82c00342d55080030503454141c801440646040002d505c120544070303c1000c0040c0302d1708441444d040260070340080347d411405518604d0f400c44549500500f1040000c65400152101c60b00d80050000c04541c031504001c50880344103c034180e40c40d02034442d022060260007400c000003480c0c19421140e06c0b000c01c0e4a55621552800e2064210042216a210320b16124034060a26640010021003040c0e40d10017060700030b406000d00805da02c944078007040000c030a0601d00550140880042075280800d00b40000f51070f008580034400900554402094040a131210180f04c0843d201c0c008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 844633066 1250 844631816 844631839
    0x6021e011401060e2d061809042004020906160f0506090a0b060616120201020906040e0126060406020d1b09030512070b060907020109080d020d060e090606040b0102010605 75
    0x14148596000040e0003461441401c00101a517907514805405c8406001d44c181001c50040040962240300d50f100311041503900030046035640100075014511800d0007400700340c80c4800d802d450302c0c2d0070f2141910035407050000c0e01081d15800d0817a083c01c0104075200b0094003203440c060000d081001c901521710b1150b5401c002180c1d000040c0c048049000d504440020345c0e4031010403025202d44941892074039240100100010030804d0942c0d03c2030500e000150400642c1c07004198144c000c1d500012605418000402a4665041210f102c0c5101c1c41443e1001d00c00c20004640da8480250000b80682d50005880341042074550200781c19030442c0007180000c1308468001015030b40c0f60b003c00e4849000380026214030150401c21981034951040884089035106010404001e030014285803d554031007419100040202004168036480784500503155444101c05104517503089d00040d0320100000c05004041c0c9001401941c81942102c01090002c1c201c0d004074007418980d8403603600000105034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 844634316 1250 844633066 844633079
    0x105060f16140c0a23011b0309090b06031308180402070609020a05191a040906151e08040b150306070c020405130c0b0d110315040e0706021e011401 65
    0x3141c4006550750084451004002c0e00700404444c0c42d2051000c1e85c04100824005112240d4002c1d0f200307481414015031044044d51100c0c603004405100f28005280710006100e4040b80d80300310600a0f5083e5682801c501d400491030180d0342c0e2b4040c010745030590102d070498862045807800000c0100187c415500d07003c0500d0944082d280c40502203114801300507003c28079050010f01c4d01d09588140d182030a080d85450380c3d0400842c0d48000b10529a4020400441c07040c1283c000c03400201151861807115014509001340300070640b8480b40d041d40010001e682000364808105508070350000f0110803192191881b01c50b2062514440c1c9815006501c2000f0034640c00030881ca44041c000d4030248490354820921981c00721480700020403606240d00184110f02c809405880c8103a486c0b0300014801420b06840d5a45800450750404218003148a41c1480e0504d4090f00198a034407000401105062407006929420403c90040e07554030908085404400c003500680012200c6140c0c0b030010f540c4a05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 844635566 1250 844634316 844634333
    0x30609041502270d020a150903080a09150f080a020a0e130e010c1b06110d14041a090d182c010b1201090507260403080c040506030105060f16 62
    0x140e00914080e83c002060b00141001200e106186900401e41070300c03242000d50b1700d810310400031805002c00004010210020748050020318a145d032640342e41400038500308078282491000040c0b0700400c03640c03452058134540c01c604e00740d40214660001685404041401300c443d840005106c65000e000326285a2100b0a00d42c030818480c0c0581009000b514031850042d69280045c0503004284030b89501c04002051182c0e2007400465143c21140745004136540c0350324281c4140001507829000032006010801040100403001034035108400340f0640380c6442c01c25215400240c03071a0501000440c102c60780744080c48000d01600c14480440d0040449441003010400d107214500c10321400d400001c1010400c3ca170a54403407840c0d880700b00107141c2c01c006084026201c0a803800040c840aa081e8403000110400103008002c84c0350011845407606040043c0356500c05010b084d848141084144015100c11040b40c2c15114262806940c8a03801c04a62445105801c0c1d440002c000ca090f420080101c080b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 844636816 1250 844635566 844635607
    0x20030a1d0a03091701060320180406020903011802060d0b0619030f060b04150516122319050c120301080a0c0503120a2d03090308011a030609041502 65
    0x240c0c0f6148240000081040c200c400310301003c1c0100b03035099046099918100f803403003228a00581000c00ea1214011102c0d4270000036181240e0342c0341c0110b0b1401c210708003481200c40a0028403071003940e0500c0b80c0c011446030300c100082034043c15151882006252038800840d80e40000c0c900003206503d408850080051014801890806d81000342c0068110100c1d0280c03810b1b01c500d41c986010703450f80d01a064504e90300c105942d444a121002180300418074445454143c412182c0f9800c010180345050608a0103040600c1075410f10141f2000340180d8418110b41c50003011030030b2403562500011032035854003101c0c04840107180c4002002090560001c524143d540b8031950a11402d9600c40c0201074a0f00c00101138800d0191040c44512400c40c810a840341520b4500d84100140303107807609403054079032110950b0a000c00e031508100010940d01c0a0344a0062600211280c0c0c001440d010f1501c41c3e22024045a100e9080c810100382884080780503130703005020803942150345002c443c19450140040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 844638066 1250 844636816 844636829
    0x2100c0b090307020901150c060c12140132030604050f0f031903111e040512031603210932070b0c031204060f20030a1d0a0309 56
    0x156800728001100010540b85900e07401081485143c0c00e040c0940d061034000801d04003080500d500c1e00300030452130f1103507a44c1c980d01030382e40804040d5944c0411081d98503c2c005c000321104404010400c590700c101101c01c000b0046c0c0c40038501c0b501c0036034410202d41074444416a05009240a00c070030480001400b103462201c0c00141c448901480d01c4050f2240030f511144031800c4441805c08090074840d078014442020710140c814186600d8050b00301c1c0340e4a903a1a00d01c030040c2c0c005014051403625544c0381c20380388c1e080e1000b1450a20150040e07910051448001014042500108260101d000d520700200c107000c00400c2056031010b04041e4035211800c4103c5030381542d440c000f030004909905811100a102030001d182c45480c0c400e070440c0d640e00290f2802e0b4180002d00014103151500f14009026130f000e1f50001c9003142d000d10344641211b98090744a1071a24800c2204580d16600906603584201c2204000800d10600340c0d4032003024086121300e903120701441407032008141e04400020162041e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 844639316 1250 844638066 844638083
    0x31e0d09061b020c0d030909090f0503120a0b0609060409200a0201020d0f06050108152818090f060207080f0a05071407080a060f0b0402040f061805010c020904030c02100c 75
    0xd513028041c044045100107030004010880c00e0040e003001e42c000b500143e201c3c0c0403507007445003961603842c00c40c0c220b80d003901c103003e03800c17414848045124001c0492484044031020b14000b11a800035900d8880c0f40310311070f4019104d401240c89003d000e1b582c0c00415a012400d203076207011800c0028002c1d40f0105443d00002d00e407003804814140f01c4d200b030702d080c0e55060b110180740381c03612100809510111281c1d1a804001041d10708000d1201e51121010310280041311400c07941030003444d005900e00010070305e03421860f00301d41c84040f564210b10000c5254001c0001a07580500d418800d955100b0b580b02e01c0c18004000402c80040c036804001006000d02404918a00c110701d40803540e1601c0c460304c950445d87e80240070314000302d80306038041c1d9100302b0300307050000f44a25184040303401c1c0c0c0c00550007007400006101c0100300c0a5040b04160b03201a0704e0b0181045001e091100290210080120107405928544005002c060144200030052500284000011056000c00400e445508078007200c1c55131 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 844640566 1250 844639316 844639333
    0x40308040e070512060405090c130b090c07030519020f03040311310b0a050405150111120316051608041e0b07140717030301030b060102031e0d09061b02 67
    0x140325109907115180404c600201e0750321290100070103003078040c01c403040c9402a59000c2039940d550440a035500050b020011440400300003c0002d80000240a0b400c1c1520401c1a00c00080c0c0c000111184010a002005050200514100e00e045120340d80e45845200000d0080148140300100d004204401c0b01d19403003244461110ba90310001d25200c419080c4000800d1440406952b04181c107084400f070054222160340304000b07030648200355918002c0b4074060384803007003659018610f40d0503100301100801810050080b00c2c040d621005162461110041011038040e6104104403000101c103803d03e00c80a0b052410046401e0b406407007241e29a01440051540d500103155031881160b495a420714240399050311003201c4080f0480c0340d120b007030003081008125503032a15041840940104011034403981140b038440c0080c0c501506c5541598010311640c6500034502108030f40489204101d90b071900f000c202888081e141c0600d00500140c10301c10024902c3c0038014013454048040d5080701c0880 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 844641816 1250 844640566 844640581
    0x60f05030c1f0509030a0c0801140f070806010309060c030c020f0a050303042904060e1006030206090d060b10020a060b10091401021005040807022b0303150902040308040e 75
    0x18264540c286401844029216000c088440ca280b4482c08442c184a840c0c00303440b2001a041c00705007401150320a01c41d0100b409044000d1007078541b588090312900b002800c00d0110301c0340c0c0c20402803115041048010010314140d1080d0481c14005a11100500410385c4424020380545910042c8800501c070702c10014002c000300051842e40e05030070501031461512076071a000b8208524851205a4800700c00c00510001c1746d440589200d03600682d40000c20400001180e810400c16022041d8921b041ca40f083c00580d4a000490700503400c02c461103108817140f4602500505202c0c5911640721001d9840d1816a50b00440c04041c05446000d040105591071010040c150412401d0000002c140c031009007d000e400310a0903240403c140102c41c0d4031414401c04e4019150300701c070211800301c40807a501e01141031a00f030003203450000c0b9200e84600e42030788000b40007542030b03030101604054543d01c1c603941000300c094098010b8038811405554564072030800204d1075005100d10000094000d0000d07410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 844643066 1250 844641816 844641823
    0x8090f040203042114041404022107090b04061e0e04110c120309030301031707080412020f0301050702061303031d0f06070507231f0e0106061107091d01090303060f0503 74
    0x24134005c8410300d091906010a107600e00021a000b190040da0030401014502c4010b0b000c4002c00355843c0011005261034a4000c1812145a10038403591406020900c203035a0403122000340704400280310b035200100c803d001c6030300e4178a011416800c6880c190084448200100c010081000e04004941084052580000709403004444041443e0000d10050002400ba04d011a00018400c1d14007400c000725500c1d0844540e010b58840841e09034401000411810511056542034104900802c450314140300040d46802c0010819016546000b1134582054000da0207400103c103200c201c2d00200c81c4180807244d0340c00c5003134185081441041d0005010078482e2049620107a4040600c81519051500003c003071591507041e50103500410100910111206194413141c4603402d101103021910307090709030708660140d0003070000c000d03404400014802c0e0015240e402c130740607808005542030fa03824403840b4060803000c0050065080028520503d649508041c00380e4a045400469041d43c4e10105a41d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 844644316 1250 844643066 844643087
    0x10e040f11182b1704080601030c0605090a0b090303070c15030e2404030e040504260a17061c0b010f050a26010605220c030209060708090f0402030421 66
    0x38000c08030f480803c14070308507002075512244a040b01c805956124518410103030010382041e041d9034881c1c001001401442c01d010340c01000141085440d0180500100b2250038203805664203518000031030360142d48040040704c0706030707401c9000d01c0e4925880f0050001c0000080400304002401c1c08540150704101145000200d518012407014182c140ca2594a0300c03a0010000d0382400700d0103828065540300c901800f0300c558801c20302c0100b1040c10441c8405240500380002c2041d035403d01220680c070344c01803402c100000310b1508082c2c86581d110002488000040c000190301c00781e100c29441000b010f8003819041c0c07801c0811020015442e9024441c1d1a42e01e40b0610910a54122901c3c3c00341109500c4000000c00100c00450415140d40114011007111805041c0000a404250320526628810222a00c5851600758500402040000e080d40907441010b40015400211800d00c0c0d035a0700301a0a011201a000355181e103018100021414144100d00e00d6480342c00102e104024411040001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 844645566 1250 844644316 844644349
    0xc08011d060d06052d0703060608011203110123010e011514030402030a02280e0c040506210f18010b01080703090c09111b010614010e040f1118 63
    0x4020740c5a0300e0fa6000782602405452a400340755142e1949001d0703405030b0b1a00600305210210450500c01801070440b43e8a078024400c000012005100c280088500100000c0d098034140c40c01740106040300340100707103003202c0c098007060059104100300101507400d41207c11843c000c0310280e03600d0b0050503036030070000300800c006080340512000e1500c3c581e014540080c00a411280e510b441580819080c5141c400e50707079170409030b40512485644241c4425405024041400442c6007090040c0c52080d00a50050a00c0392201007081a05c0301030440050b81d0440b40c010b00740c04113040c0000e07507001a100503114520101c0000e1072801950a050082e04180314040c0d403074a0740c40c0e0300c0380f42c01c03001002505012120078102100006041d40d4038010800c240d40b2194150356100c52603507115080005101100096904092040009051240c8000e108490038204454101d04450005008100400c2441d40152500080c4001c0d0003004000e001a07124010000f00413070100c00400000902240c00702 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 844646816 1250 844645566 844645579
    0x1b080606100509031504150e030d0f060305120f0f04060f0806040c09090b0105071b140a0f0b032e0f0f0803041202120d0e010e15031f08010c08011d06 66
    0x1700441e81c550b1940300d60180c0221040c201c88075000c0300200035246000807801d029400410300301c4d906810741c800d501040c500c031402040044d2540d621203072299948010440c45110201d071301346000451034202c13031414407134481d03a1341c0d6503454420241820111511040014491000044c0103043c0351240340d910503c6901c85640551600800d0f402902c0078a88107410460309209140000ba0442130b101901c0554100252506040011110300066110002403040002c003004014100740c03203401500780c0316070840060f030701d555120007080368130318404400c4c1d00680e822408a032802c80100401c0f059a0407809021031481c0e0b1540c10381c0b10550306001c0c1c18201d4004210030005010040741c4203085030f202620503442c0c1605008014144000e03800810003090549d603000e0419a401a62036818960403560000e029216050030b070314501004241c41c101c1042c104940104481c0e4003000b40040000c500240005221081c3c000c00f000020310800210000d049840110b01c005035040c0344c40340f01c1c05404c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 844648066 1250 844646816 844646833
    0xb0a2307060b0118090501080c030705091302040b060417062a160b01170d0507030e19030602180f04060803072301060906060e100206060d1b08060610050903 69
    0x50100070001003990b5410302403e1380d0034419a05038075009600030181844006001e605d4940080d04040c0550400c1c3d109400000e000c0c4101d40d41e800b00d49402054040f2010702070569440407900409502c60001e0303020b600030070b00041000c00b00350380043c00e800716429140213031107441c1c0c485c00ca40403400351010804009000e9040042900e0040d03d0a501c505141c0c0c07019031620344071604500001c0e084041e030170103410000391070110700b0070480c48402c8035072410310b15220f00354600500348a81c42e403d05104002c14582e00b19600701014001001c2c64001c5000c40d5125144400d4164a56020031000d0094406480b81242d610b06441214210703004113014606c1c010841d980c6170a88228030218854080b22035021840005091103904054070301200001000d0b030034507038043c02c010a13403154107100383c40e0380402841c840e07808221550040b1342030b10701c1d1200403540d00e0200e203c1c2e060217182e89410851000005490040021041d000d060252030440c400032403d40c2c11206881071103d44c680590006a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 844649316 1250 844648066 844648073
    0xa0603020705011107060212161d03010e0d02030307110c09070f110a1101091e170a061802090709030b011203200d18030f02040203040503070b010b0a2307 68
    0x420841d03108000001d9142019903150b2071340c0c0c002d56010f4445503400703d07800340c036203480c491250382140450740144902840820002e00c14100c015801c0c107107450800c1c081c4890345003508a036105107a000c054582203150307039600030b40d00c1d01704440d140009403422044c414036003004520b100d000040503003005841da07241038051342d01030919201e01c0100416507032000c0395013009028940c030340342c07103441c0a26115428400041800f01320360801006944810103031300250b100d09030f450b07046a4800304c400c8054580d000b03a550821410142c003509075070500340444c4030b40c1c51414030344120a108407001c07005603d40d52001c40b002000c9020043c101c0c441600180540182c0b00c00481c102031092419042101402001910030903050041c1c0302c4507807005402d0307448107410901880b4500c05907521103070034900e0b688a074010007079401e41c0a405680d0000120f024410140304450400e0380005a00a41e56076624050704294410482d2000084010160303458003403010602c0a110803003d0359582c204041d584 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 844650566 1250 844649316 844649321
    0x40b01030b130c09080a051b090712090606361401063e0f1c030b15070c14030705100e131a180c0f0f040f170f0109020a0603 55
    0x20900042c0140b2180000300c805c000c104160180c2d100b007010304500b00400140b0320203d815842c803d0300c1001c00104000728203074401d030a5218007079000000714223070009041800040c000340c1c010600320150848061070240704c48450705100c4c1e1100501e0000300040c40590000c40f503035101c45111400b074010042151500c1030400440348840c0303144801c0200b84800b041c28000060300e01991101100f04051010313201b00340640c00101e60f0040c00791488000880302003081c00228211001403659420100b90a030701c42c1c0411030345040240d40c8490b541c1042e03080800c1c04118138400ca141001c24146040340300e09001c00d20104a40000c2e01c40011103105500c165842840c040080350000450f5214001c1803030540514401030b40341000702d14805111000348100440c104803100d01050001050000c1082008210740d600035060700300300c0d114004e004c070000304d610a40c1d00180f261f5510b0280864880c1d15821040e146898a40450340602140e200032400d8a124034130103913000d006000100b1600780a078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 844651816 1250 844650566 844650581
    0x218150714120304141917160c03030201053c06030c09101d0c1e0d0f270c050f03010b0312031815130c030203030315040b01030b13 58
    0x30142d901510b540c0d00310107819001114180d030400300640707170a20f00312000e02c1019200c4140c10209090902a51a250090408195072204551001400120280c1030080e07038a881c6500c00200c00449950f414000d004e00401e48412181c0032000c010540c8046840640e03400d0400b05140c0da0146070070440c0d880842800003403090b50103000700368041c48d040e82c2c2c02e10420700c80d031408401400c100c2d04006100303500000b04103800c0d80441d050024480312011000c150f626240c00c1c1c810304221500c0e25200c03840c03540100f40303820074114208030501c8480c0da4290043c41b92045840903182c54000f0811041d44103000140014180000d020310510503414540804901710201400203c1c41c0c1c0f8515021034030b04600042400f00004021092040c1d03034030b00d8030601050340c0b00c8100500c0100c04035070016003c03080c05030101d114a10075411400c1000364980a40000b142c00030b007070302d49a207080c01d4607041544800c045184560302c0d0004410305907000e88207034240d540003c0c180075802160b0382440e80042c03100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 844653066 1250 844651816 844651853
    0x405010c090807150c0305043503092422051009060e0f062a0d02070815070311030906100807470a03060821220902181507 54
    0x20400840c00c5106428046c8800c0050406980750001950802920f1940c0272400c5943d80c20070841241e40da0b6429424001c0c00030880d07411a0802e144448004040c8984115114032400500e0034546070203100000404850050b1030a8407080740081c0112403040c0d007405800b01054500c1d00380442800d10300c0200035503441c0940383d03900d00312140303a41d110304c6084840f100414115400c04c0003000c020a0040c0c0d40315840c280010032140313090600540d26407042c2c07088469074100c07060025228a00c41c0d0070022a0640d00014a0740d0707030030a007003d00d8075104111910071502c16031900000b51501c000070340400300d4500801c050700d011400d11a442c00941401d00c00c1c05004a00d104103810341422503004d00c00400c6003c00f8a035112020000901903400130743c0500d070b858020301c1410941071405915000302e51100020070750380d10380801c5911441e411105042040072603880011a400150380d00420441e032421a603a54888508000c010641181500080c0341035418001e0400149041355288641303142e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 844654316 1250 844653066 844653077
    0xf030f0114090c0a03150b0f063f01050d1a040c0501111507050a050705160518101502031905040906080303090c1903060903030605151e0d0608060405010c090807150c03 74
    0x41d2303440003d041e03810842c0a1440d10300d400f4030740c507000c1c011551906052590860100000150440083e41c59030051007001d0081208201400811101c0d1412058001c00031a030b5801900f400d0800041c8844117000703080c00325010000c000740c10031001400f0f5550b180c92002d1003919030350700c108c1101d0a0300040c1000c418004248222000140188441c00b0840490046043d88500e1b00007000103082e815255a05c3c0340e0300040034440d02ca02c80c220713040c0a540c0b50b1581c040d02c03480a510202c7c0385110b06040071506c00c000345803051015a10200a00807110a0481804030989954420343c4902c0282c405092540c8021035030056410301c5564208011002d40750380f05059603e4a41000b84d401c49402100040e03076030700041c00315191080c01103000000c041c45040c1441c1c130380000442d100c4c424101264041401140b58102d0101030b030409000780050009541c2e03541040d203041c60280c00d4521041022907030340b01020960810004d000005c4900c98a01c8500b0400d07034610503103198441c4038051b806c016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 844655566 1250 844654316 844654339
    0x3090c1a120109020d05070908250b03070c0203100204060801030b07052a160b0714070902070f0203070e1303121107080c060f0112020f030f0114090c0a03150b 70
    0x4001c5050a8020406003030090382d50f1032070700b8101c021940001c02c80024840c800e0f0091018034800194900880003410b49210f208495915450460b1070640c0008540900042081041540a1034442185100307408440c4030340e40c0820441c060707002e5405100c0004400d103004002180071000c0041e080b0105081071440c001d0f40b0f0555604030441503c00200840e15a0004503540c3c5041005d0082402c0d0203003c0b000e00340c14000b0042c06407040a2000d805049520740b013010340e0b801072007400c00402107008215074442c0c6919007281c401408881c164480d0140c001c0000da03d02d00090421720071413252413a019003081507a010703152007402240007123419940d04080b406411821008086071030048a00d83d850b40360424105280400081801508800880042000e03031065042112420360455200aa0038880e0000c24a0443c50f0200114950b0170075419801140c0f800da5424080c664610607651102c2aa00c14001e000e6181e110040c2704a140000041621016a00580600500410045510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 844656816 1250 844655566 844655587
    0x9060501060c030801060302130605030a0b0627040b030c0108070507021819150911090324090a051002210702030406090509040807110d140d080703090c1a 68
    0x124426000440031614a1040009164101c3c4001d4010051840c045d450207044484190106225200309810b00402002090440800341c00420035010080d00c01034480309501d032081c0e600203922191a10b201c0c0408a0500e460409000e200b1103500060014140040d40400443c3c00b03040080840041002c00e00c800b84c0141c1c2d60540c148810081a0700141c400e081c0a05644900030304140880700c0c1c1072902d0030f58480044040240b800300d51101e00b00095502e4021103101552003100c44a40c1c0c5405501da4407107205884d158a4400606000b58142d801c1c1d4600641d00d90301d2084030006407142c2c5c44112107101c00100c1d9002003001b20b2000d54809407040101d485c20140e250240e406c02c000da0004601441602c0e40581034000804040b18030310040e05080e00d51002c2d510802c100030b02003002054140040f502ca083c9a80c27581380d4000780300c420703101c1500c0020f626001d01070880400140c91070042007150340309006140020713030050000b4034010b1422985200c0035664131a52143d01c5c2c010301022240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 844658066 1250 844656816 844656821
    0xf0e2508010507081603140c130914011d070210090623040605090a0206030606030703060b0409020d0606050906031305013305063112060c12022502040906 68
    0xa0412034030b0707080c49805c00d410031030210001082c440017050b140444c4041e0f00d00d001c080d01b80c1c1001c035000c081a5943e460380700640e0f41c0121074101d005258140070014000941720a6800d048640c06204041070712001c6a41d035051203001d881d10303001a40118040b030b41c0e507510366121007405482220000742e00030b48403540842400c00c4100c2c0c1603400101c0001c00c0203000140c05555070160815005d0841300c0c2c8280d0000354240006000507001e620040009102c0d0350103548850041c000442401d0348036076403408484080d51204131510902ca003003280000307002d40a10241d03603400e00020001c0f070543d9906003a450f5540781440c0107030307070360340d00c80c51881d41201210781200e45005050040886c11540101d0170b404222241c0d10540c010b120400201450016010010302400506103001080b20304002e8040020001c0340c2081c903040d00e08a400c00200511036011b10400803850b19260b4400c0d050701d00500403070044100b01000e40d4915544041c818810001120115200410001c0c10b034100e034941804 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 844659316 1250 844658066 844658071
    0x1d102007090e060f06060307140f07140703060c1b02130b0406060e0a1706161e0c051911040209010513030b04020a1707030b090c1e040f0e25080105 65
    0x40d0f8100905220825043c90942c0382d00840c151030440c55801c001100825030911441030988407030300421081c0264400b40129603015811202c001c2041c0125078025480d44900c0c0700403203074586001d0f4403180c854011820f1122110400400f00700300b4101e502071002c520302c54500c00800943c0c03503081e5105544c3c3c602ca1907001d04055075901c2d003c11062380a000320001d05070081c1100400e00209840b90220000740c01d50710144071000c00240459090702a5901038005041d141c0c072640ea8295941c003e0750003410b0804050040003228144080c5000c00b20302c2025904015100108151561000b8280b45c1c00500c142c031010300d4864509000380440da064010642c0044031a40035600500055141c0704a0940180510025500c03140c044114103c0d556541c5220080100c0c1500e00081c2e13800d0300502484020910241003103840002005140d1905980440c0030740c40303549002c80101218819204d844403101030080100300c0c0c1004103c081c0441d45101e00d0340c810742201a003003c03480702020f004860 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 844660566 1250 844659316 844659341
    0xb13060e060a0f060509010308160f060f0b0405070819020c16030f0201020105090615040f0e060a05060a1715060f06040e091513200d031d10200709 65
    0x40150301c0c0c0f50340c00305a0b0800d901c0140310fa034175100140041040181203c40701d44241c6180c4541040c1c031300c2c0042000782c815202070f000074a021180020070784640c1001c80c0c00f4900319010899507032040350588a05206035401694903404400d14841c000c015401840e0000550088030090180303100014803441c49600200c842045803c420011075809020383c070740043c204001381c51946840991202908102540c940c896031711040c4060f5800072603808108241310540a4aa4610f40003000201034101581e14034024008103400180e05106045080c40900c28040a40a00004000c0c400da2004000e0030031640006070306111a1280d4900c1c1c004d00007001c0c08920701941c1c0c5460ce01d55030400c0c1a003004000000007000411501c045004100c4400e1070b40040e01e003050221006a03440d0318000c0420182d00840c071000c0410070b0640002031210910403042043e01c5000914040c40060314103000084003048695004c03070300c1ca070307807041d840d600358600c042c11560303142d64500c0d118054400ca414000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 844661816 1250 844660566 844660571
    0x7090f080309120d050f2b0207150b03030906091f0f03110403150c020703020415050f12151e010b180a061407031e0302190206040b13060e060a 63
    0x140240c1c2000c100401c2034410712405440c0400904202400d6840303900c58001c01d0a9000410805940389a031260780132061540d1144c120041f01200c8900035800700005030350314004d0180d04802140c0500401d07031480e4016000d14100100c0d0301c04d122180d044404d440d98008684820601c0c03900750101007030010314043c1d0360058540a066006011103641c261360036146c04e020841480031981c100c401000d014800c070000994002181c4040f400e2200b0364200070361050410f09800c0c0c07408500200c243c15a002200e007264019000c03401c100442c100800d80c1c2e503558020341960002003d007140016800a01400b18610040140086219254098004400300400410442c190703400905a00150a0050f10302c1140c460034010054050045041004850140065202c0806128a48003a6038002d44040319049012040018010b0b400a440d000d08020030090f60039a10343c0b0028405000b9030308003c079070125032505080072170030810380b140a590389a02d401d51001110000c0003110710507800d44400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 844663066 1250 844661816 844661827
    0x50f1210021b0a120c050319050d060e011206020c07091503060b010f0801031b090e071419030b071407030206070207090c080f0702010e15040b0a020c0a03030507090f0803 75
    0x10040c06035450b0212885948a048200b0000b142040305141ea080c0074182a031000f10140b0301070b883c1d80314021400e4641d034008104c40a41c19000400307400c1154440f04184841e6071225600030503a13409105445201150034401408aa6581e0041c0042d12903182920b000c40d8a9182e440b0070340d500e05920a80070300000c58104240425440780401d46107003440c0a404c0c501d0203c1c1c0081c40c08006001c080c0401001d8001c95403460003500e040d0001303161200c0140b00b180c4140300145d803925114840e0903551344a14241b102c49141c05207200441b4070404117504602030039903c843c9201c0c000280a4000d01c50202c1c150503845074a44044c00c201031083c1e00900c01454501c0d03009080654661112041c40d042c00c0c00b1907140c13030300510031681c041c50000481d5581e640d8044c04a01401c80d4100c0289503000d8036100515028049012910840c007443e4014115194002203c00301d00c501d1080c0c1c4190b80202c1c1c1d541c800a07101c0c0d000390b5002186494124451526032200b80300703684407a44228203d034070006e0b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 844664316 1250 844663066 844663087
    0x60f0f0a0603030503180712060212070305130f0f06020c030a0e030c030a03140412050706030b0d030503071b0503030705070605090c030a020105031e0f0a18020a050f121002 76
    0x401a9022500c10010711081d4607559000e440e501000c0d02c440c0c0801c400503980080513100300300000040c10b038122282e00705222800c002009500c040c040601c1c080c2c501c00029030f0240280a2680a800c40c5503a551410f560340d1a150490313107800404a95020350381c40413001041460018103e0340c81c083e40038560b658601c820140003960001c05903030190700941410320041c0d0b404500a400d294050808140c2008004420b005ca480b4680041014881c0f904d001400c1c0310001a0282c19a011620200300c0c80c030b04502048003854401c0300080c0000e20400004108911418043c0d400303082c3d208a4680054580d65158210f8004541483c006080800ca400a00c4894081c581d0841541c00207464489001c8000c29100c02a040c0f0290512400101140c08850303000c001d0343c1d103145481c2141e24241802d20070300c0800b00040d5803101d500c50900207046a40007a6408560010b64000e0480c6a42072901082c00040820340f042154007002d1044a01044541031159940380e075a200d100503580d20340c1e0b02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 844665566 1250 844664316 844664341
    0x4030c05030c06190c0c031b08220e250e010e130c02010f09052112131203051e0702010b04020c1e03040e13020f030f0a0201080106140904110705060f 66
    0xd000e40c02c020300d106000000c02e810801c1041c2e08c0c0c0c0c002d1a096080c500d581001c1056204005d8500d4501414950385104c0262a807644002e5a140d64640d101c0d9032100d200300503404070001d01c1c0200e08410008841000c034044d0340314180610b018180701e900005000000303441e203030a070440300080c0746d180c1c0d0180060a5080c0b1450301120490760080044469a4171140d0b43c9610911001c2d0001c24003244105441e0143c0c8141c9100c16074110740c401071803070300300d210315040c80381204116011040041030001c0180203009441c401d010301d008192202e05940c001d5049540054000420755603100342c40103403a102c1d4001405440c41020041c132480b08802500c8114416030010440160001d00007801300d02c07a0039001c45d4010304c030700404508054003800060641a0500c90081d89403145e9001031140e20350100b2101d4466000343c07a400c00350303aa68401920f102030000c081092032642001b1103103091825600a182c409001c02c4204d00300300e9103613940e5103025000d4540380843c5076402d0407c14100c5248 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 844666816 1250 844665566 844665581
    0x9170c060a06050613030f0512130503010b0d080d110c0d18051203270a0e0f06060310050919021611030d050304080c0f07090b13050105030604030c05030c0619 70
    0x250f13646803030110004560040c10074030b408001d04800200000350203100381080400c45c030005601030b6a540d414007620b0140a24410b2161034080c0d403e10b0030078600c901c1c06003003941030f158221903404d1400611584440c01000c100350344900804041c400d01d02c507040d0070400d050640a12381c641c00b0b00040842e01c0c000407243c41d54081403082d00a0091011150b8010064410760041c48002d4140c0d581c2004043c014092030840c0c16403c03202403900081c00c1414a03888500031260710b81c655901e910756009000ea00d11003201e00d0240c24100034410801c50501088050380281c04007854500d1100c20380c1d820301130341d00403240030481154540030481409a0030700c901500032001c90003070685c4614480068a1400000c0020b41580004a9801d4010b07409200c40550300f03001c0380680d0240380e00c88207103800808a0340312007800b4403074203142181020018071926060f54401030081250f40d03030325a002c603105001e50204450501040c064000e1000b420808a070040100d0140803141c0119071440f0750449000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 844668066 1250 844666816 844666819
    0x1902090f10180b060a081501090e060112090f0b0105010207080f060c070203030d0c03020d11030c040b030919030f0f0f2c06030103060203040b01050306091009170c060a0605 76
    0x10500344840a01d18000c41c1040750038004100c84105100b03880e40008200c840790940d000b81d00001c80100d02640081c555100300b000350401e5000c041c01c500111141d0070140641023904a000000c01c0c8258000d809039401a0302150000c1440c91140c0d0301d261600113685001c0720101c12000040c00513680520020015104500082c29071041529445582d0b50001c1c10042c1c11b0303980080c0180540d281403044481c900f5189800303111218145c00c004000794803040805440a1400068440e9084030a003100d01400340305410606140c142120740300d25501c00b91070520a88a01888403421451182140900d0741c020307281d900000041c03010260003d0055641c20041091030b4035500c1d849500690403a00386600308001407440ba40d54601030382d0340c40c04080c00c25803005001c00000200a19500218461885661240c0da81e90b40d480602d560b80c0c9098910b562107800c50261410002000d900580266000b03400040c51400c6940e1015500c1e4824685601e03141c121404014042999000d500001d100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 844669316 1250 844668066 844668091
    0x4030f050105040b24040c0e19050307050607080d0f0b090405060915070c03080a11040e06030d05030f0a150911071101020d052b05090a0c0609060804080714190209 72
    0x190160072008000c81740100c0d4401d0760b40720301c0b002100c2d124201003021070001411030061081740e00c41c000841c10182c480c0c14420b21800c1c0c80801c00c1e04180c002d4a9441d6813103a181070400101c800c501c405071042c01010011599101c00da500360f50b9030b1301c00d854026405540a8101400c1241c00726083c00c1c142031121450b20841018885107590119501100c0703609481d00c81d2198035144080700c0901129071000c00f1900000c03070041100d000d800365081c00b41c07000700c0031581109820441510b45000c201c548078000038800c0000741c941c44403500143e020050040b0100da11351b80303070300f044407c540d2a0350b040c0840c04001301e507c0041000e80126005015001d0000b4289148501c0c0018810721400c0c003080d40300c440c40c0305001c2440002104c40148909101000c2c0154642015400d80d2514144010740d0460982c82c07001498034042c81e40041030b00c11136680c110250f541d9450302d070b00d41c1d1b01101c3c0464049220100444920f03000f0700c0700341020303080d41c04e0b0100b07005e07001d00401510740e102078101e501018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 844670566 1250 844669316 844669351
    0x10e0a05010b04090903020f03040f050f10020705060304031107090506010314010509011211150a020d030612031d090c09120c0d2603040303091e030f03050c04030f050105040b 77
    0x10000069404442c41340703070081040c4103546003c90400c0b45c0c030391248000f40f00200d404504400e03075660354010355100b600c1c4241d00103a24070401100307107200503180c8050303088004103000c141441c5c07005561043c02030601d08000d54000964500d03042d903070703801010b82c0e6a4500a210032580d040c02030041500750348102000c1541840005050b5141c184030790b200480f1a8500c4030200880a0345500882c400100307041801541c4a00031180d030780c040c450400044c090b042e05680414020b10036907003131355040c090b00f43c8602523550b0195a00c1803031200c1340c02100c41d88240180641c0c4c5400110b44160340402c10a40c5541003802403158005021780aa011600700c0710f001034079901ca9426010b0090b820001c0b00c840c2c51822401814150031000c2d4042001b0f200204000c02d00d84c254116080c494401d100b000205210b140c5032940600307908000900003030b034800c60740340c070b061003030f04481c1e0401d08081c08940b800355a0341e80d040d515000400200ca09945a508000170300c000c100c881503000310a4544400d1b0304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 844671816 1250 844670566 844670579
    0xb030708010f092904060308030a050105120a030f120e01020d1b03092d20030d0c1a0c0408030723030a0512040602070f06200f0403150b03030a08010e0a0501 69
    0xe1080412500380d088030703086000349a611504004021504143c80035270303c1c1404488500588170902440e8041e4012100341e440000000940c00c80d4650590307039008216090810882e14102c110064400141d280c188000301443e081c0b00a114020508000140d00c102d030b000c4000d030200c81349031008185440c0c0302c00c07400810000d4894400000f00281c550b404160560300381540992903000c0503045c1002031500044005021600c904211401c0301140c0d81103d854030210740c1c1c100e0021f0002c150207685048000c51450b085851604402010391450800317803503040442c510741201509681d0084007050080036049404c840f09481c00c02240907600e45220981d000d0418828a1441811000c2580000d000c2c002c081e4181d405a5901c0321402e01c0034800b505003203010b06407a100000311190000a558040c065040032100000c810602d00350400f0300e580c48800740c10310f08241c0c1401c00f50712082080c0490740e040c0014406500070303440b9030079070754105882000da200004201d0107030030303248c00d00610a2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 844673066 1250 844671816 844671851
    0x2070f05040506030a06060605071509080405010f0e0301050c1c0203060306010620011e180209070e011709010914010603110d1e0605060f090412180b030708010f09 72
    0x103482040d640450303140c85030804646403030740020010b0680307481d000300440c2c215809002440003a0003142003c1024250482241c01c03203140b550010f05400e4104000c210075401120354a00301a1a030420144241c0c0400100c0e0a40e0001c6981e81d84c40c0c0c20000c0d6131134400014209600440e8000d680441c1145006c00c0400e5940c1030600410050160301c280c3c018903801e0011503403c0724500394000f4807103620f001c2201e4044110702d0074080e05a0303080c100e080c00d84200d2100701c82102c5030024149921501d8000080c2c50202401030494101300e180803a03100c040c0c4005038124010900d0b03400020382c1b146d49060805549846510303021143e410aa420000306440d42c1072070210311400c40300e003103035002e81380360a01580050040a0300c501010240c0c2c1000c4c00101d50106100c0e010030350f0301d820b40000307400402c458500308541c020159032507a8244d0b40c0c1c42d07104045160040800d65100f00149840d1100d0131026001200d048000883e100010300c025641180e0f110014070a0f0402484001d50007144c8025 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 844674316 1250 844673066 844673069
    0x10f0614030f1f0803040b090406090b03071a090307031b050307062309040e0a0b1608041203180f0201090e090318011e05030f070801030b0c09220902010f02070f 71
    0xc20b00f40116003070743c0210444039001c018015001125a1140d039091140a203421a40c00c841c03007903203000e50000f1200b200c0d001c1c140040b20300601600b016414558800000714801541c03e05589050194400380c0c1c50400824010b10f001e41c001042c411304031048a0300c00c020701d42285009401003001008080c2c1c0140b6001a544038519800782c2d605400d03001f094480c000c03201d001d5401803c0050544910402140c1c881c4098015010300b21965100c17007540350064a00f41d132403000030b03074404001004540d18165403640d001071841c01059480410804084c980054802a41c030a142200004110740c0c0140c51f5100420400005820078034041090644900680c1e481200d07610541d01145c9060707104c1c24a4588101460a40300c8003408070200007801a0404c890900340e1103d4880440c03945c0e0b01031320400c0c3c1243e520028155040c0d80b0869143c80c070380c000c0f075842da4218021000040025003400800d00501c241500d0010b00450030f80001000d0200104030402590005030301403100d0000201c02c1e40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 844675566 1250 844674316 844674331
    0x1060516021c15020a050a140405040204030b150117060d051501080f0c03190f050a020d08212e0302030307050102130f05060307081e010f0614030f 65
    0x1038440030568080010100c00c000000e52100c44104601c00e52900001c003402003078068611182030b61208107501081748a000340d0000429403d0115120344d51041c00a00f6031103d42920301400c1568581c00319080c0d81060b0422500b000040040100321700012040f0000642d09180480d000d2001d00000f6a6038500944500c4c0500050141c0000f4403004001c01400445d80c0b160084856948008450700e40804c41c010f0107840c0500c01c0c3c50000c80c070380043d44000030500c00c600094142c040f583ca03410f0700c0d50300c4001101c50b80954801c80d000361350b48440f501e0880f8002c0792915076a020110000b030f201011317071042c034420b51904002c0c4405004800c1115107950105c1001e9812504d82d041c91006100981c2d000a40c54440020307075004019064002c4c0641a019103d60482607031651a4a4600c40203801131580040c018000038207101e126001c203a0f004004c0c1810020410000314410b2a00d102c04d800001c0f82052f0301c50f041008a03071091025581c078084801441c00c5061065694085810203010700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 844676816 1250 844675566 844675577
    0xd02030a0503130602160b060102161a21010303030603030915080f0613230c040602030d0510030f0506071803320d0c05060a110d0c140d060306060f030305030106 71
    0x3c03810003245504440c46000c41c954a000e074032801e480c140480700411a21607006000702c98210889980c02c0c252030080d00c2507151003075a1442c0c1d82e0182c21594010901c2c80703c603034400ac1c404c1005104e086507164060350080d5004250302d410340c20b0240101080750f014a088902c04052000c41c0c0f40d2201c42550854280c00707001006458120010b64408041d100c141407092500c00103113443c0480c8600381540c3d84840003003111075903c1c220f4a1129000714810500541c10412020b400b00c41644e008507406105201d044a805451351980b484120020344129543d510446c1449402c030f80120304d98590302c0344a240100308038190380c1c074103001c1e2042c0c105010a08034400c0c6000c860303024001c40c1d03c1014001d1011a0941c0240c800010001c1c860880c0580d40707070144c030001c92010120b41c02000c4c0c0f610307803000e03000749020141c8098500909080722008200811850303112411007680f0010b108500c90800082201402c0d82003140c11114150b004030300150381c0312400c00c0040e8010054a04486460600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 844678066 1250 844676816 844676851
    0xc030613090302120a090e0115080703230c0d0f0c0507150b0909070f0e040309150c020919112b1509091415130203070e01090b030d02030a0503 63
    0x6034604106038011340d5444c400881d8460304507034001403400c02c65080d1504804070743d0340c4909654003007803409540400100c59000140c1848d000f5008003039120b10a190983e005034020305122026541510741210030500055800a044c40e140910a1415540001000045a00c03e4090480d2140c4440184181201c41c410715038440b01da40300d4407008401070080c0440c0c2ca00302c20b0b5070f910303200c40d401001e1010045a4001c1200c413001903e0340c0c41241e03d47c542c1d40d1550705040103940c0300750700c4403c0d035410031940f1700d90740c401a03c070240190301505040c4140d00104400110403015a01000c0420384416014040d4000001c08040c143e451050302d80c083d0003040315141200005000d0728020305c1c204014000000460484075405014254041c10500e24032075022041c0301d40745c58420460031400481d540c00328280303c00c00040b0720b0317000f48014101c0c0c3c00c00b541c034940d040b00720400341c0c44144c8079a5150400143e9040521004a41724482d1000d10b103420070208000e07140b8080a0305030100c1d46403d508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 844679316 1250 844678066 844678073
    0x15040513061e0303021204180f0207050f03040906050315040311030f0f1e030910020d0e100e0c061c0903050423270613150f0503060c03061309 63
    0x20702408100350690703107620b0710007803021a0841034481140184a10f8800081c2c14405009580a841d5680a0000da18401e40402c001601e180861a01015802c12105000a004102000844810001454580b172910f43e24504503240c641c4041d000344c00c404211200310384040e01c4141d0041e41410100c40c144518401a481c5008000301143c00860002c1c2020a480701040940b10300880d081e0965804010341506141e540020349441c13600707034410741c800041001d070b43d0060b012121440f0f6000800d2220000d0b040d1602d4040c0070180101a41d9580d079400080040c42208d51030041a9411031508215101051899102045140055680700350802c10107101e60226130040c8141140a4910000c0060103209003c19640b0300e8811078441c1c001e58030301c00d103000f1108058000c3e0700c6160a640d13200c100780000410003a82c4410303016910030001c0e00030201050308001611760600c0e8034808905200a0501d442c80c05001103210300c2017402002202c0c0e450304003903035103241d0600d80814a90b68618 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 844680566 1250 844679316 844679321
    0x122001050f0d05091e07032006120901021e03100902090306073209010906090f05010e0420030103051b090606070512030901021c0615050c0f0a06090b0615040513 71
    0x70500184082064103840d61054009061000d5030300984200b600550030940da100300d0207400c8c0500f40c224006001884c40d0104500000f584086850b002503c0d04d5180742c01543d60321030b001d4620280c00c00c04014000c540c0942c101040191807545011443c0800c03041c0001e0365154001d15010400171803084da1341049409180c02c16031154540d03510303c400c0c206031810300c003035802c5402c1e442c3c002101c1d801c001900501c1031601c20122400e2100102030507050500450700c03c40110001e03600315485034124440c1e1000c0304541e50b060100540603946950440c5011800c00780001003006030240c880c01000391654170804800d4000c0011a209540c1d400d032494540e09008902074164032066000c800c000541034190000c020500010740422094000341070110100c2d10356010f59000940b00c50340c0450451300500040101810610848a621084041c420f2030820380070400c40300240c4400044041010700001560490401c6440803440074041400080a0090303216aa00c0340b07400455405458400d03070b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 844681816 1250 844680566 844680583
    0x103170c03030c0a0e0901180e16060804050607050720010c050a030f0219151e1113080a170901110106030b091c0e01030207020109122001050f0d0509 66
    0x9109494407440c20002a1105800409074480480c1592800011615001d100d26048e11070220329075040d5000d041000d0010f0800d07081e52500c0f44200306a00940023030410141c00203020030382c4c07280000c1ca803d2625505000000d000c03c4140041804483d000942c482e2000d241c031441c005004148501001c0101d0f00001000000360280c050032440f1000c1c503900c004800540041c903003c9400510702c00c07800400d4000701180141c0700500f84940403841041680184d104540516a10900112660710140440d840145160300c200000a50008980c00c43c080420040030740c400a4110f9000300e44800341c0481012000e01c540c7e000c00038003981c2c140e003c0d54070860a0700ca603034001c00816843c1d14001040c00029128041c440c4103481e006964036101c66030002e24a5602c0c0d9070322501020500064011350020344040b41813040d018000309034040c07220300c0b804060340200b01c5005050f0010821180c060741280c40181002010400018908007420446104034100a000190b581d50304508a0415009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 844683066 1250 844681816 844681837
    0x2030a0530190e0a0f020918030409050702120c2d030a0c0204050a02091c0302070308030c03040311011104170708011b03050916090e0f0d0512130b010317 68
    0x1d20034000c100646081800722501c0d11001000007040c4090b8050b40c91034030460051044c2c944861501c014109030640d650041d01c101620704003c54012007140c1541c1143e04070051080c3c0e03600810800c280c2c1000f8044050380c20445080c600401103110503190103400c0202d5101d802c91402040c8403109010719502640294000d8075180d00b59007100610414141100b030341324508100101d440241300d44200e03007004800800ca100060724012418007014100175003501540120500000440c5804000714400d8102c4001560b5901c0c2c80d16001e440c00b516055000f6160f8500300811003818060804c9a042d60741c01e0105098480030145014604240b0340c0201c0c615500b0446181c51880d40d10740e0602d041c40d02d030b8505010360341c0d40d42d0190703336034030003083d49501003240d101c00402002e04190f22219101c443c240994122000b08a0400d01d450002d282c004001000010b44c95510113208279002d8000b81d1038040d0551007070454079140c03032079141800060901c2d41c40001c02211103e2040c100c500300f102c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 844684316 1250 844683066 844683157
    0x61e090c0e0310060f210b07050c15011811030a15090f050414011e050c160b011508091c1b060b040c080417030a060308121602030a05 59
    0xf01100e9000d419503200300c644200c070b02900820b46000d48885c020443e1101c01c1c80500c1d0324159101c000840f58054080000e000c0200001b180400040c010a40b80c4e41c5404c84500c0c2035407401c2620b2100c40850b00e5000841c0703150150b560f007050743c80d50440350081c0240002244840e003684010030800c94980c00011200c4ca04003401e03440d800940c000380d1007580031713102107041561446d105500343d03000503007900840920401c0300281d5500c954001600b20202c1c2486500348807440488801c010300200c1c055560038a04401001400700e00001010700300c42c0b914002c409070900c040d2180e0742e40c03405051740300f00215000908400304d1058200c41040034003524081c00e0701055040503030050100702000d82c09141010703884a04c0e640039488940c0519485a82181c100081010130021904040c0c01170031080d031212000400301e10104040e148048881044022504200b0382c120f5115044510402c10740d00140703c101d07400f542000139a0742c031407201c00040795010349030420130035484510300d00c9104c9040e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 844685566 1250 844684316 844684333
    0x801230d050f0708030c06070815040c0903050d020d08160309080d0509010c0c200f0a06080604051003120c030509091e070e0d061d0a15061e090c0e03 66
    0x5400510540014a902d0654a1054032101d26a85900c11203030000c00c507600030008a15083d1240c2d100c10341c4003a840310341c41030003013000300001d003030f6040c28002d10002407041e4020b01c1071000034054221200302c640010080c0c0e0603444006400c0740001072503180f003a1202081034289134041d0f04000b069030343c00f08a441d036030038154401d40d000b020151010b07941980b0381b0783c0d000b0180340120081034107560040300054841001071502880f0f1201041c07856003055484850320520f071501030b17500024116a41382c8001e40c3c81d122060000303c510003000c10b000c1c0030750040b08001044a001c1242c0d4220748a29002403d4200c505003505d2030b00c0b450320313101e400c2400e180c1000a00030690081f868603a1b07000034152007a032510001102c41e1800c1020569121130302003803003000038030954072030301606a0b4200b500000e640075210907810118210016a40c0c03242103c41038190302070600c51000900003103800450410165140c906c010f40e441d000e0400256501d083d00c580c001c0c010031a40500700c0004044680c400b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 844686816 1250 844685566 844685573
    0x2060f1306020717031e0309100f0c080c0906031902220602010c0201060e06120106050d03090510030911040e0c0310060f0e0c070f0c09060f1a09010801230d 69
    0xa01092140c1d604802401d143c400203408040110350604100d40d02d181c506ca600e0360702c000f241d0f0f0300250030142c603480346070444858010940200784040340920400140038500c09000381c0307131034402044100d122404000340712107030f0307903000903640c21600a405400494000c0084d000003403003a0303a00032400700000080c1c0a60010110000c009a520342d5000740302049440c642642651018091141d5441030315000500e04c2c18082c8180b80d54076401c2001040995890010079100f554a240540002c1d8401105110320304007041c02e9400c068040c03908000c24407013a02da88022403441c806c102e1049464080b074020841041007000070290f001425214896803400d00c4800420b081e101c0c800c2200c0034424000f03201c515a01825204080350400c081c5803d1042d96500103454014004481510000401040310380b40d51040501030444000310008a6041241100039100f07168a18505040100450031659a0100071141140c884000161030358800d0101500b401c0c1d24038a020b504112021500780c1030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 844688066 1250 844686816 844686823
    0x30301090606030b1c0803060a1a03070e01020d08070305190c02011d07060206060603040c0f0303030906060902070201120b0325050907020c1809070b1b010501170a02060f130602 78
    0x121207140c1c50070408040b80209008048000c0e0645d07003041ca0000d05a0700c0800d00b024000c1d07030b01070001400f250b0059200c002040514132003030802c105c8994084100100260014001e6100840900041c0502508048001d00c103d000415102c1091781701c3c00407500b10070159460a0300d1446044040c0000350720110700900030145602d17a1820118100c0110700078180219004d004e90b440d0b5070142c58665680303c280403440e80054002c031401c480d0b44000081d0f000b054220300e40558804c0e503010808002c1c9080903026207810b608180001e5104200380302c0181e0b04141e41c0d108144001c0320200318500d40c200002c0c00d0a0074401407030814036510a04484e08110500100d0a41da006c03620082c5d5926003003422640c03180011a116003210320812000a5910089211343e0b00c440400c04588100c0d890b070303203404190340000c81e66030303001c2c4c02010010741c580c503081c090300d8054001907684502d8185000c907203594035810040080d0040d0400106108503080480864042002c040c03410b285040d40e40200955 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 844689316 1250 844688066 844688069
    0x1303081617040b0703080402031e0a05010f022809050a170610150503090c0a030606030308060f0616020a1e05280501030e1507020309120c2407050303010906 69
    0x49900001e14407006508100081e241035504003004581001d81c00e40d01a582c5903800780c030a90f0f040c41025800c26030300304441003280a0f640d03c8000380203802090b107000e81c00d4804070010003003000d00500108000c440d5000130040028808203003181c1000344d240c030588000342190080c0381c202c2700c2104041888407100d1514610301c1503250454507140c4e0f40040d41c420610043c0102c8903540001601a07142620501c003558022400388242d61040c810107000910185076035100710b4cc0c584d00c40e01c08000b0316800042a07680101e096900b580c595080100095840c400c52030b1805902060820000c1552121040d00e0040c0084440c4020149081585550305400d0b51090a110b0b84003d4004200320341c45540000c08850018882d12009003001c0054018142c048800c0350148036480e110501c403126101901d005a1007a00915900c09000080c04041c2030100c5a405243c1d0091009803001d88400b100050700d240c2490f24941d80080c1000c0000b01445043c50103860761101000109210802da4090f00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 844690566 1250 844689316 844689323
    0xe0f13060f1509060f0b0f0f0304050c04060e040302120309101d0c0d11040b0d0516050118060504091a060711030709050114012f150f1006030213030816 67
    0x511203982c4203400c00c1515290300030300c51032085c942c0c5d041092004000c05407844096600b100d60408030000c00c4000690812202502c0590200300c803154141803d108140190554046103006031406480c040d42e1816030343c0b4480c0101c00000006041610244142c2c900d120242100b4800c0094a40940003100030000000041d40222141c24103a4500306420040351030340005840300407a035910800c0010001902d805401104112840c80001d1042c03010400386081d803003800c11401c1c00d00c800100f541540c0e59a003041c03206c1d0320600f1302c889a040000e0b107044900454000c680307440d0300c00700c4002c021200803846400c03a0001c82c0f2a020000092880d0701c0200003074048a403050b548221400c01d83d0000e01c034002e5040c02c0d240c0c5161076548200d503020181c042075203a0380e000308034404812006880380401072006070000d441da480188111b02a05410044a1000306000d050451646a4a6010b4824502450340c00140150007031008150b1600542c0c01c80e9019803141c82c0e29041a001c10300c0c0d8032045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 844691816 1250 844690566 844690601
    0x206040210020706080c070609120302030907050303160b0a0605180a05090a0f060e151302040f050408090108151306090b0d0c151b0305040305160e0f13060f 69
    0x18400a0310000760507040b01c010f03039034400c846d4448032039200c15a8483c41c41681c005031a0302424010801d00502c85000c00c64940d001030740c81c94201116404c015960b00300030702c25041003040f00d003049281882d1344230480c1c00c444000c41e82d0711064880401041158015504800d541c402c0c49000640d4240c894031441407400140001e59400c4280358587da5080001000c1d413040c90b441c00701240c6c40360f0002040d905204100c4440c03200d420300080340b10100300e60380007840c00f60b035011504509140c01294000c8081c001d0500440c00c2030380d80d41015006800d03159042200c0b2000161045850f00500d0407151300140405c7e1901072040380b078001804184c01808034071820400b000c00c840c14500070360742c19540c016075001911410000710003890540c1704940402c01c2201000600c0e101066550a4034480c800d0f00c40c80d43e0b580c42c625080c0d0525200801d801214500503604001280c05400d03004d5100110003030820259442500d001030b10720200741c002e441146046552000f0125561252a422030042c0c0c04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 844693066 1250 844691816 844691839
    0x601111e0a0b100b04060c05150c0a1205060a17031908010e090f10051504060b09041424120d030c12110f0304030e03030712080c0306060909040606080d02060402 71
    0x9911140b0041c1304100c51404200700401032203106081e00850315119030165030b1044080d418085551314241c91030841f010f4009828140d49402c048107091001c190070707050000b841e0880000d00e150074540700d40c00b41c41e00c11004d202c00703101c018400c035600703c004801885030030f4042520003404440709008030650342030145c0c0480e29051000840c0300004030281c00900a10360b0002c07080016020103000305100300e540504200385552240110001703020829401074881306014200301c2622109940c2c00c24107003404c0140010f5401d000c041181d070120406201e02d842c01d078980840c0303086035240420091400703091403041a841d89a0445a2048541c1c3c0d0340c1e00d82c042a41c83c03000c0403070715242c520702c0d104c040401062025600d02c0d009075a0003802414028405000800460705550088004640c000c0d00030004014031900f19494641003a45610203d0031440e1a4003ca8818494003440070f04c5007035200c3c006810440d864006030054448042511030044044038007968804003a10228800c1075001c42c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 844694316 1250 844693066 844693081
    0x12050c16080c040902061b070b120a0606030504020d08070f02130c09080309060a111608150a140123120c040e010504120c1b060f11010509060601111e0a0b 68
    0x400b484c4e40d8006101d50304d4650b0703104549450f00e200340c001e000b9500800500141003a00840035101d500b05034000d8070041d02d01b4500700003c8a010f60018410b141c548001e21000d078640c0d52100c050183c3c4a0540f550781d50701820050701184098000a5000e89100d010380b03e0845250044144003181d600c40c1300c2987c2d100d10031603480e800b0759a0089d400c400c0a01c81103040c0792040034110b81c01030400054800d454100841d40140c103000d078010b103220b03034400307208441c00701056032409a0001d8048810850001990320800c142c4c08103200d0104481042c2061031410700740300800d00d2102500400030520140301c5210140c0b951580640740e80f049160035580611814107001d864420340d0310019009408041450039503000304c403141709840107004040301c0b9003000c2c20558404050134440d110185414407a1030005c1255000d142c0b41c180590410050203001c140000318141c101c142401d10081003841182d1203031800c1d040c00629020120701c6945007812480104001150034021880e69816644e03045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 844695566 1250 844694316 844694321
    0x1401020d0c1728020106170307020a030b0a02090315061903080a0c1407081b060705060a0209190b030403110d05070803040213050f0a052212050c16080c04 68
    0x880a400c03a42801808102c00c070003070b00245038014904184030b2141490721001180080119902800f50b90340d10414015221840c1281160840c2c040085290884940c0407444000640c48003c01e25100c10010401c0c1080d00d8044c2c9080b02d0010303040701c540d03031410601c1c0344081c041510780c14001e800f21503003c26090b03103200b48031080d680c0042c0c80c03510b0040e15480448000c400100e0a58058054652061185000b40f003041c005081030f400030b025410010fa03200603031200c4403103d244162020003d05000071000301d04180e004505010050f15036403000b011841c083c2d0485a4113440668181012400e10300781006580920300a603070b041824206629000c1d078404584180c1001310b54144128000905040011a40144050026981010402004415160203130b60b00b81840102008000c1d40410343d1054591250102c000e50140c1e01e4400302c2c816142c1020b00d0060070503856034160505260150782114060000b1004686c1607011410402d808909207001c0c40c00c0300d00418154484602c1d150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 844696816 1250 844695566 844695587
    0x150c020a0f0b040201020a020d0605011d0402010e0d0c26060c04050603041203020708030a0b011413060c06021219060f0e0a020306120706030e0f010e19060609061401020d 75
    0x80d038944001d441c59140c10202501c000c000b01c0c11031060040c9200140c8809800d104458400c04020800b0b5052074030aa007039062000d2403590a40503a01000050b07a070000740d030006042d094034071509650250911100344079064011490710324000b0350311844102e1035042884010541010b0b03800c161128a6101002c4c41a481215400b090034000b0801044c1140c3c1d10356080345907810300520785031103030780c64140c540c01c12a482c035030b43c5030f5500c540442c0b0350700402c1c0c0d000402e142e1030380940345c40307a010b0610302e075080c242c000c1c2c0e410015803085070001c1141e030750704546021008070480d1a86140c550004801200001c001e0003c4a04000002556071003607a0680b081d19110311802c2c3d0140d0b00c622900c0001e4100070803d55000c1852183d40c90484018004000588402da0300841c200c06e0f0003523864a4100c0003100600315030324220680301031082c003180d0010004501d402000004450b414000c020303080c144c014103070040c605980041c03080d21007401882540c9003a000d075904240e07000303816524078810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 844698066 1250 844696816 844696823
    0x170c0111040e0c0a09080111190801180905030c070e190507020c0607051e070501031d060403080619080a0b07050a020a080901050c030d050a0e0a030e09070318150c020a 74
    0x181c00461030100084000d000c5032192071408505060307503101b43c0e03800d43d00c1c1c800300403011100028034034240c08201e110090100403d400c0180701c652511001038600741400013001038039903681d00250304200090003124600300c5480111902c8545030b0581c0c60340201c0a94031030b01e8846008403020b8110700c440c01a148214101c0d009070210703280003400d00910b175210400c00c41d014041c0602046140d00c0105030f20001041c00c1c80100349031400c2400242c102c8a004100e0030020800100310301d0080000192254025490301d4214180d48422020600141c012049440c49030b11000c40030402e000b00183c4100060f000b90516402900d03035420942c1d49101d83c00d81d030030042e00700c03004007000305031280000d1884000c18903186240c0402210300d00c0c15a0030260860080e1903ca10a10000001030302843d141d002040018201000559802a00501d08103407003038001e0410380c00013450b0340d002e68420701c2840d0f60051035103011006880c1c0f050000003000e81c81003100d460700d4031803020f0a20008580d107240d41d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 844699316 1250 844698066 844698089
    0x10506100f0c0204051b12011e120213060e0103050f0d08070206040311030c0106060224070f0e030712030309020103060905070c02151303120e030607090b0c0a170c011104 75
    0x1100e800b8080541170080614441204100079400302480704c1d00102046011449555010750400700c030082c003506104885000700034510024440f4000384480d0b0300f1034036412198124081611507811001c1e022a90041c08079413000c070000401e10002148041c07059404105441c515403102c01d0075078010500760ba0fa040145d0102000500007801441e00903060680581100c0c144602513140b0350a40700c03e50018001a003213290b40c19012401d0181c8007408013822422000d031481c0000c0e0040065042680c4207041029003102c180054805200403c0605900450031186101504014000d481801d0003280040d182c4840000c81c0d841511032507010711400c0d80d5a08101c0f0054003049403481012180c1c0e005148100001c0d07141481110f214001075101d20085000d41d601c0c100701030b10030006044598041d0300500100100154060150000e440d0382c940402c1d1104c03200c0c4420307445d000c00403034002c0800040d8660701080d161401c014000c007800420082c8081030340c514a10b41c040c0283c0c410041201c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 844700566 1250 844699316 844699337
    0x602250e15030115170d050a0c06020c01060e0612010c020c120106080d020a0b1b070303090807060f050115030b0f0d1704091a09160f03020f0c010506100f 68
    0xc010303000040e0414140600040e98200d100c000900f1102a1241240d400444ca1010040756804403564041a1407180c003614040d20180400303016807182080302d000f04034800c42c040301007182d142d040c4e805020b40790008001e0b103138584204240c0842d040c0c1e91a40f00d49c0140e41403405041c0140200710030f1590365030142a136030704942c00340219040440200c200035501c1f0540403603072140c204900500e0081907801800c042c0b629040c9000c2c0b007040602510a403100020700da4040c2c1001d2400c0b10142c03545850300050320b110070700b86006180185e55005101038108142e030300c5007290503007015041e01d1080721204400841c81c0c03003d80446595004890b04490481180c0e800c5190505260000070300420260080f804072050b01283c660158000044407650b80400d1a2040d800749010081d071041681c084aa504050581c0701c011050350b0322650410840964850105100c1d13015110b4074640301181c251140c81140225020705003c0300c2c214010808012003440540c4500d84d200302c090410b0311007003040e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 844701816 1250 844700566 844700579
    0x60c0a031409092707030f0201141b0d120905070b0711060c0303100f0803090d0c050a270603020108010e100e0705120108030f04330504060225 63
    0x512071042112000081484504080c0c2c80e0210070511903000c10407400302040c40740072078a190800c1242c000000d640719040c00d200003010903820721000f03502400d04148000105141031240d104880c20303079582c99101519001d034400006101e292240311a15440440c4a050b0b0f0340343c0403145a07010160860f031000c0001c0103405c07004801001c040340200c1c040c0304520b406c100404e031a076001122880466000008008400c0c02c440104d00c090081a01040d440c03a1034910041e5690050006d0300307109403082600a0100030820070346100802c0003800e40e1030341039a15220000b07408109414070030210301c2a01c1d501664032240c0300e00c2c1c084d41c2d0f050316010a540d0a013000f1b5000c0b80300041c80c022009480500201b440800d990070035105503181c0e581c40c1d566489859204c41c1c660303010ba1020710650310a02c00040414000019075050301c14405920b610802c01c582c1c001b50011142e94000c90b002d0081100b46c080b680e10000070010340d4069003c80704400f501002d284103100c0c1e40410956004664003050005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 844703066 1250 844701816 844701827
    0x601080907060818030c0d09051903031107050301050112020406210f06230103110904051c0201090b010308121f0506030403210204090b0405360706090e06060c0a03 72
    0x10420100340c0c9682004444c42e600d15680c80600c0c031504a138846101c4e03c8609a0081d405005000d0544a4812074040104107001c10441030000034113003c0034011180c0c5c12601004880b0043c60700400078030072560344000030803c6814980041e40150308285002c074942c5041c40000b07151032040041e00305011140e44400380541d10680c012a08103488540006000c211001c01180e81c03114100e0034101945036150818940320f01d0102e0900440c030710002c200200e40c002c90a0340c40c10a40010080302805080340c100d0040c00e83d00001044103000030004414820000081e010310b120351300c0020255151800c000140710040c004001200412030018041420000051600140b090400031442442015002440c00100581042c066030219042004000754041e07540d082101b80c508000d00d00b40800d049410100c5510910300c03040d0305000a002a2800b81510380c2c0048107042030b901c1d00c1d9111000104000d940d03108140d4404254000f00f035441ca046012034829480840080452400300d80d0181c41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 844704316 1250 844703066 844703071
    0x3031003170706060b030a0e1b0103021e030c071e05030706020d0f0e010c0810261f02030a0b06031e090c04090c0302040c0305011503051b0a1706010809070608 70
    0x803a241c1400014000b403003a009500243c98101c03003141d260320f0000f18084c125281c580034059542d205032540640c006a90400840f403240a10700542d40308007000a850030344540641c0480040c000108010170800f414002e009120300c11040000880b80405003031443d100c024001404540080250034001130341035001f003070141b40b8207001180d4030b940003141c80104e41c000b480419490f5155a80c1e260400d90181805038052681140001ea071402c01e425048501c607940c0f00b02d440d101c040c003002c41c203110040020746054800900c02c0800b01500110740c201940050f00c0702d02800e800d04020300d0803403604005a038402d450b09512248054001d41107841d46000141036195a805402a4010a5100c0d4001d243e0501d010b618040318407465071050004444660460400701441c2800500c14005551400f10000b00300e80745c04109911031075001c80844800f01001e145030310300007900341c81c00340d04042d44564080f000c580ca01c2c0181e603200010b5407000b0b41111008216000303202c00b44619400b42c8016074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 844705566 1250 844704316 844704353
    0x509090a0b15190b090907030203070c021c1b0806160509060a0306080609010e191a0a062102090f040803072001020d1506030b01020706080415052703031003 69
    0x820f4640c5500401d5404815400030710b6161070001c1d0021441c02e011443d40e0f080340c82c5203030442c558a03001800910300f00107030100034800d0b8a880f0320a0000d005040700701810340c0e0401c018000d151203141001c0001e003e140724401950150000103140950740d100c0000702000c1d5504c802c0e00c0e0405000400480c1d40c00740c0e0107441455900c01c4045250070003080021704c0b8040308400080c1409802180d545011040c0b104240040d28405141c00095030014481b0b04a2468206902d226201c059654020b414150031603841000c00ca24074685403410441c920400c94000d45081c1c403a030f1500c4107441e0304400226405005c241040001c943c020f481050880075440b101801c08206004682c0e103142668041c15072410f0f11038903206100149400605aa0010407076414200040c11034280041c0d1a00014803070407007441030400000e0306001c035104d0b5400303032002080c10800861900011401d160442d018820a01444100c191805002c0000c2104e004184031081e0511061859480c4200380b200140c00301d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 844706816 1250 844705566 844705579
    0x3140705060f0604020705010e010f0b030705030304060f020f0a060b280e071718070609030c0b03180a0b1605041206020d0e19030e15180109120c0509090a0b15 70
    0x140d010447c284122003044040d1000030845003980300900c42922512107d4902c20340064200b000b10391360000032103003110907500b440301d002041c92200b030f42010700035170006070940030b642d449030100880342c1d11214980c0402c403000401588101825103000346031150002e040720170b1602c00c1c40180880c0d80440e92040030752800c0c02c0308100e4016500c49542c003e4a88402d100010f441030529944140500b4001e010070b49000c500f07003440c40d2140c0b0170740d000500c00d8004da51800408144400d051310510900c0340120001c95188004c0c0e4500410003000c125440b6a0140110b510030b44203a1140040790b00312408a10010500c0d003c54036283c1c002e52201c0784440195540da4050031f101d40040c410541103000c0203d061255100d80d0501604004003401107511500c503455004402c50890b4041d280c5410054448902e00c0d8801e900503102480180c00860400925148400800020f0305003c1c00b40c0c0c0003a5201a46030301c0c0d0005031a038489140100810b0710031403000048180d15000c0c03450b01c0c641c03001000c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 844708066 1250 844706816 844706827
    0x60111070510081b0309030f090409080408100b0406080c04051e0117010605030114131b08030d0b0a03030e011b0b07030c0315050108060d02030a060f050403140705060f060402 77
    0x440400b82c2050300e8000c11100010000035200900e440c080c003018109981d131071481c060700265103900c54100da20b540940c02145074406a01c13242d21124510780e200e451180e031036446800641c3ea5140c42c20006268505140c010007044c24140283c5c1d04032100e26000b4800021010300700700207413000900102c51290b00708110502d400e501101d0130300805c0034607201ca909514980945007074442540184e40a82c3c1846d0700002b0100c1d41110f1964040050440f0100e0711815107001c914608404800c00304100d940100132030301c0c0e1404001880d5050380d002081001007048010700007000e80b280301c00307004509040c50388507455001d4000400741d800c40b5803503400c00c0003581c0c0d02c202482200342d9070540003c1e900c2c01d4034051781e600341c81042404070480441104007440c01c030000304011001090240039400c200900d20442d10204064407041da030201c0240030200034002c03400d0041804075020f4000034032800d5108844030400007203802c1645c0080c00b618107507403006d050b140b140c1e41c00340101d80c202d0b81c20041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 844709316 1250 844708066 844708069
    0xd0903030f060906050a0911040b0a020a020d2102340306060b0307081509040204110f030a0507090e010305070b03060a0302042904180b060123030621060601110705 72
    0x10b040c1c0a09019600000c105051105100300909260810920603241c01054068200c0c000151000c84100200c2031365103004030001281008032256000f5044040c0c81e0f030b81c0d0108800b1846c9040c61200942c22802c249203012000c0341d549a803034113440354301125485825001002103c05903401c004966a107140244c0d20354440c0115111342d803101250704008020300c050302d944100003940014040208400798141940001e0b00554084c0000384a0703075540d01c05443c000d030004161190310301a0440c0544914040b078031880038100c02c0f1388250024808460110351784130b15042940c1a05c0e040002482c50303508000c140019039001409540d48030f00324144c000010b0f9a90f0151341d001c003506c1e100300440c008445404040d0f00c8629045940700742d0800c0d210000c20304d44070841c909810f42040b000401c685481d00180e0758442c00e405003c070b100c1030001d40700d20390210310720003103000b488291048030100d180b000348040a0300a0508011194002c5404907540d588522150120290b01d10240c8070701c20b50340c0c070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 844710566 1250 844709316 844709321
    0x1802030d030203070f090b09090628050a060809031204110a06021005070e0319020f0307060816020105010609120302160602010c11031201031403301b0d0903030f 71
    0x2000340001039000401c210751254841000041c6028900380440701d2807e025042540307001d03010072079014000d0900040e5040d07407000711800349004200000301c0c40c0c0049200003020710310180140c2d4080d1911340302c0010800e200310b144a1003007503003030040c60400000744007025201d00041d0056171511b00464800f00a960b61450a90040c6002e80060a85541040620302919001400d00b01400300702c40411a054030049501c5208a001d00e071010a020401c0c800925001041c0d02465058440d41d5008640d8641000455010302010b204000d41c2d14245e1900303d003a54003d000301000281000c03c10000c1080e01d20010381803d100380160b54072181d0354100c010503603501e680b2400060391038155460840340c001c01c4c4069140e17060005107181c25151410f440c0413031410310006058807014218540344d03a200b4019030b900b03c03001c0d0a075205511911151602c0c0c5082000081c46030100d1800410f0941303824000e03058211000260385d0382850620048080181880c00307056040c10b0725060307100312032405072 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 844711816 1250 844710566 844710583
    0x203070206031006110c060a2304080109020a0e090a0f0809032509020315091b301e06011808030703090609120f0201090806190f0c0c06180203 63
    0x10102403c141ca042c100a0030020f11078071801c1540c110038000180d5480c0c0808913840b00c540d80c1800781400c0075a0030034940e00c1d00789a445400d504404200480c0130207042d08140c400a00840764101c8903920b030942e80b81512001d503a03034082c5a1202222800103500a00046809805802c410b03087c421b0b01004a420f21601d00544903c03a001301111841daa1000b814075409008288011425032618218544511968800d96403050050100003034501e518030110800c51414113800300d84602c0010401100310604015410254125842c00d40f82d000c4011800c51090b203892000b410070b0404100b8214120300080c26950401c10080c1e65894980d01d40d80075a0018280344000316a945040d08000300040796541000c000c11901000422680c1c41c03010300c0c0d81605400110003490070100e8401070b03032290955484940c8901540c8200440184405690701841c0b140c000309010119003202e0402c1101c10040300000454003c03220b16001c601c455201c1c000f02c03c880711902100000340c0d00003c0c070700401c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 844713066 1250 844711816 844711831
    0x51204120206010803090f151308010b09071403070c150606020a1109161214070201020c01060f080d0311160803250c0b040c0b0c01020c1b06120403020307020603 71
    0x9026811402641c1000124010a0413501071410a4030103400240030903580d1049501c80c03110380d0100d0481e6840c41044803107140e44a2030068403030ba90340b0800c5000e0b0080303425661041480900094216000700303410500c80140141d00b41c03039540c400006903120783c0c0002081d02d0714010072a015900e0741c1d49206102c050419900144400800c43c170f1304c410b44181b000002401010234505220034003a0700251110707003503070390308103029021410103488009180400b40e9021490310101401601c68041d0300400000b00c207a40240450b54a0340f00c4007115281c1880b40c450140e0080c1540c400c840c1c03196006407800840d005d0410f20f041c00341c001c25003807003815907410b550741c1c18000203200f400c90310444107a200c02c611071200e0180143c4c108019060035240c1e0405400c006031400014100310311203940c800600003610442d42c0310580110540d00035040070101ca40c041c031072203210700132020811010740740819004007480d260591002d919510303034070041e0007201903220034054840169510700140d48103004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 844714316 1250 844713066 844713083
    0x80d02030c1e070e132310200702010c0204091a09070f170312010e07021b0604031218030305030a0c050a0c02091e10080721020d0201051204 62
    0x215181450030708902c80c1003200381812001d1002e80312400400c0b280100c8000201e0000c007a41e682e180c02c42c0950a442000b0404501051503020b990100745003080c10001441c2103690304071201224208507003d8860080d040903019003440c1040c41036400900c1034500c180f406e03845c2211154041402d0302e0340018211a50002c558050501c803401c0311405030b1050b642801001c0b407030326204c000088121a402200308101a40305a40b080f03480c10400c5500391514510303015880d680d917034080a0868802c0e504940140201c01c100e1454102500102840c0540200698036051550741d90f20b9403070300d4128050040c0000e14010064154440030507400560013a10b545581c3d140002d22101260000e0788035405209042c0681710f1296800300808180d1507040d01c080c0301646500341501040e081c620102100c4881050411103071503003c42c202c4007280c1c1da00d0219402c00ea1142141d1a0143c081c003144000c0101840e0702101615003002c4058403503006040c554174044008145006000040b601a1407041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 844715566 1250 844714316 844714327
    0x51606050a110a090308070609140c282607081b0406080309090a020d0c0201020c0d140f030c0409020a110f0712060f060e041a1005090a020d06080d0203 67
    0x3800d0780140d0002c00c0b00d0451503403400b042030034068220303016404045e1820038041018003c200e4254800d05441d0340240c1d50880c800c81c50303520306a40e054000c4103507000b8074104515010712101400c10080c80403c4581c5144000d0034404603808010341281043c03510100d8440400035903005201d0388000d842401d001e040002c4107400003d03401c1c0c0030801c0b524011450204200b08014012054440c81c05d0304607055481070700e0764501c20000c0c1c0120440d500f055451322031000c5034560154018003a501d00304082c0d03100850954420b55802c0c0c00c9000ca04004103080104c00006a480001943d01c02c00405085007003640302c426500480c1c00c8010380b003001c50016042c0c6801403808000c0411408045002802282e003040c040303401c81c1c0100c480040103291506900c02c0e04000b01d40045019065000c501311007031829040801c03041817115115641e4416000215000e21810840d000035940e003e0100421601d68400c403200a501c0848900d481c00d40c0c0343c0380030601407401c1c014094490302c02c0d4000c50303c42c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 844716816 1250 844715566 844715581
    0x30f020d02060114040c1107150801080c060a140d090f05060901062105030d0908070212010c08041e12020105070912020f0405101d01030c0e09060a0c05160605 70
    0x5408103040415540158010052002030b180660260b50003550041070013020f40f0301c15100480d81034100360450080d00400703d000a0701e01040b0640c0541a0744803849666241d100c0d584440780340b02d9042c1c00180070071411a003d8003a243d66404800320a91f0980741c4008188414200d85510900301d079214202810038040c40810090780d50401340000081050fa40750032030704409042d0082051007514018080b0b0000e01806009403104180e2500c03052010040d949001c40300c5034405001280326000500351902e071804140304802c0c0840d41740d1514400360311951241c580c2d842074280048641e9107041c4408c40040c1d00d20450451031a410380001c5854142000050180440c5404c601d40c1e50342c1c0c241b04240585da5100300d88201600030380340058170f61550702000301a2460364106c2d510300640d45449040300c80045061034122030050340f002200d2926240906803c5905955012481e4010804641c00308510307404070b083d504d0f4034109245001d400b44551080440990f50944e00700389e94030b0420010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 844718066 1250 844716816 844716823
    0x5040503060402040207140a0c060e04141810050109090c0605070b010911040801020c0a020307140f0d060b10120c0305072c1008041e0f110402090a030b0412051c020d0f050103030f02 80
    0x40482c200e41c280440111340c04c2902840358024283e180b003b001c054a159000e4082c08101c3c5001900320f4240019a110142e000151031090000c90781d01d40e400c0000950540301d2030071740e6255544441000741607407074030440b400a4201c071078000411000800002a8841c0248001c05622240700080c148040107401011b0070103419901c84150802d62070440c2807541c1e201841202c0070001207861292002290408a0040c0b61181d58260444c00120002550070780220a4180000000806121105000340228281c650549070400460110a445c80310b040c0f541001c0303860041801340a08404007140002926030b1803081d007220100c1c40050500c410f009481001d400820b2000d0081c1103c000e06564540d60440404800750864601810360a01591035804807031282e40000c2101d0401d58803400c0060040d039080c0ca048038522444207007144003501070f0702074401000040e504007915851409169011f50b02880b07031441d040e582c03403030007a80700b01d2240b107540d001c1c602030356640d0b40f1414201d101900e17 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 844719316 1250 844718066 844718087
    0x230c1501080c0315090c100801031b060804060b03010908131d160c060b03030a030f0c0329040612080c0706080c16080c060705180105040503060402040207140a0c06 72
    0x140d900800e0546074140c0f000201c040112902c42203000042e60f0b15000710b4101312110ba1030640c450032040340c00b560b19500a10383c0f41a68058010542082c90000540d000c0031540d21501020501c00c6001402054290344036000c40c1001500202e500340c141c0e44c03400402d03402035407a400d04400d090030030301a000f08654078074144012400c0410701c0b41480071a5103141e4504210402c03c00500c00c8941c01000707c0354010707200d03110b4060100c03038841d0490319010300904104174041803500d2a000141050718428040c03541900466426031950302184400002d4a036400d00e0541c1d0032a0302c03002c00103041d8044180d408019802402d9035512281118069414603800d6442102040300031070500c80b0010066045400340700d0b04490340d0003106400e25000010b80aa070321000c0a43c0101d00c1003001054025004002c060b0031605036801403244480191014080c500400d50181d0040b40000d0040c1040d070700900c2600e0080b41116401c851084100e03182c4000b01004440d400c60900c002c2141e0341e0001141c44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 844720566 1250 844719316 844719329
    0x1060f0216030503120c0d0207031d01020604020906040e15100504150b0301050d1e140106060c17031807090b091e0415020f04091d0d050406230c1501 66
    0x72200e6165455850303982c05954001d0940d040f560001c10b4076040143c0880390000c500f00300640d03c5500c2401d0181c04419000700039401000d440d00c950300c081d07201040c0d81c0d100f20780c0148025880d465110511004040d0100810b915100d01ca80502d03150855a100522528488550991081c2030a0511050317884209184040b81400202800b41001da6800c0d00d040d610241da218a03a41e91a00f4100028820908020f20310310700800310740d0178450011030350344207084e040009008150342c03400300316511140b4034005052800004040d003401d84261f002035400c08411a8400394140ca48056241007411035800702d40c0da00e50300c0d10321104900304107000540c019224081031240c06040e4040c117001c0c4400805c010017100021480e8542d444c183d07415034100b44040700b04107450380e8546000c44d00900745000030803484401143c246540a600140701c01402d102955064107041c036003034003a91307445020318000f08089100008107250001a80141504011103001410080c01c540031241c0400700680104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 844721816 1250 844720566 844720603
    0x13140a0809190b0a0c03120612060e060115030902030c09010617060114120604091e020307080604111905270709050a15030638130e04021801060f02 65
    0x204001030b50541130f20440c10103400d022403014440d2070102e42c4074002d02d400055051900c0d40110b40c1004103048000c199105a800b0084080c68014560780c0b0f000c24440d00c06d010f080e00842c1c4050900c69005881d4091003c2c04540380240d96900184000034240c100c03000086820991503406040743c00c2140d00000c081c03c08107261405100c240c2c0403840303480d0305c00e002442c60001107a000d4840d940302d0840950070241481c0ea003040d403c00b02000540c0d03801c050b880303841003038404038941402080700c1c1e002d03640c09461005070990a106004010005801c44070715203502e62000202a00c0390a030185031001803680721198170708000c0021001441c0642000c08000c04420300740865151402d40f40300751896209644640000000e086000d84551f0b04207407000201949000314010508590784290070030484411180100350300100150700468800002e1400ca0500401c17000c0c0d107000c005600180050502c1d4015074061083c0b0602e00e03c280d009400249280c2c11a1aa40d54188400381394001e0f18201d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 844723066 1250 844721816 844721819
    0x40219060c081b010c0216052b050a0812241809010605180a060e09070b0322050c0f010c030509060307050c07060201050703060906050913140a080919 66
    0x1000c0200c4020000c04401c40081c1d10850040043c1d0241d020301c03075080080c40480245140203440340c181442d130005c1c0440483c030101d09032421a14014040d400441140948503441d058100d940c40c0c50711042e9000c0c002c083c4180d02003081100240b0400741c0000880c44c1c2c07810411000d01075030a100c2c1c10003460400fa402031800a83d1001c41032100405075a001e603820303898003102e4600401c2e0361703800300b07a10031800402c00c106260b102100501c0354070750b907800300301c1c41d0750f18801122244d20456a11203240c00884040c014200304401450b00401c400c0306000c054140e0100394903042900030015a010b034011440d10310300c0d1410407030302980582c0078a0010424140d070b5402800d140900d030031041c401c40c400320000b01050f10500070307507600c5060303d01142c090640c0c1d900701a0080c0415201c070b000007030034048040380c000e00501540c0d08035036020b049422203580b6200729003da104005011507007105071000e404258401000b150b20414028082142d40f84012010808100480000c500110002020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 844724316 1250 844723066 844723079
    0x7050a030c0203011e090b090c03100507030b210c010237060606081503011808090103110c03091c0507030803181608100627090b0f040219 61
    0x44112549505080010140d9000d10019001d40080309100304205000c081524180115400c48004c030390244c0e030308000c15161908030540750203174100200e030181d00c415042444266180d000941c01403107031500240d4a5420400241000c100d121103a54840c0c8072402104a0042030141000f00802400100b00d4248a0849608864141204d000442480b02c0305a5981c4180d813589288842e40810100705482c0c03a01d81c003902042c0180c41d0080d814609d9900f0b840d09060511403100002c0c0341a043c00b00c402000d40d02c10f00300b0b60042182504040c0c458030908415458403000e802d208188402135512a0441014090402025500f54803800b4102c61406c021a50124400c0300307a9800c41c2c005035883d074540341e818107180e980703840c420441d205010300780790414002510034095071f80303e60a980c401d10070900c2c04819102140109080384142000400750b03900c40c1c0301e03104050201000003041404043d10b45d8509204102c3c0e03d2007911070102c04020840c82d01c601c0580801909550747c220b01c50070080d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 844725566 1250 844724316 844724323
    0x30509031605150a090902071a09062a0c100507030c05031302040b031509010603030f050c1c020f062706040804061d090907170f0a0f020d05160f06050705 68
    0xc0c0d0f07041da2114009074181ca5148500369500207816640005d555611080c81e080da041006c2198684100391040301158000d100814010700883d01c210b5084900300d03200140c00015128860391140c181c03400c2040d140300c4d18081c4505402ea645580b80001e17180b902c81c0000d410f98600c040f805081020410810024000d00f54011000c55015100000c052441002207440c2200341c02c0100e6041002d1070800c070000d481500044241ca01c01ea98010845401510584541c001e0090a43d200d401003001d6030514070340c0c3e000d07140c00300240748115420451086c101c0c0e803c00070150703400b15420510032144440038008603c2c803205440c3c040b004080c1e0b440c040d214110350303004602400c0c0802400c0044a5142800300b03080b607d1a0000a06214250030800350300c541e5185140f0400310600f4400e14141800007010404414042000002d864070807601d40d607a4544419191041342d11020081c0d0210200788104001c444804018081d1402541001030b0b21511603007a43c0309000300b29041102600203000031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 844726816 1250 844725566 844725589
    0x130201050403110d080f0405040b0f03100b01021903030204081603170a180e0f0c0901171b0c0f070b1306120b3a080304200d030509031605 61
    0x4080507004200c10f00043c52004605000381800c040452040303980002640140203c41e41103a041004502040900001d801000321362649500310510400e040c2d541908001c1e90071105206603054000704071340310008010f09807010360000f0b502107420300400104004081c5480e00080c0c2c02214685942e41c2c0c00d00400b000303034449403a0342001c43c191400900584250000e10071084200b200e194491010140340b400490380c86182d10100c80c081195401e905049804004042c1d40d0b4540c03d2002c1c2804035081c000140c40c4180310660303086a01031403101c1001400c900b070007034809003030b18080d44842e8a01c0c000340c640010101d4042040071070b220784013045000d821680b05051030103181e08090f0b1a0f80003030005103d00c0703820aa011410410308000c03000000e201405865200d9903010710310460a00724440b0410003400c04104101280124210305002d11141500d10802d140e8403603584085035100741411000c6002c04c01c08140b5244610303003030010a0790704021480343d2100c14601000100c080889 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 844728066 1250 844726816 844726823
    0xa05090c19140703080901200d0c050904140f09390901152703031b05070b1c0506010c080d0b03190506071b031d0d0c030b130201050403 60
    0x9016581800a01900d00100c03460002400140c5442490130080e102d880212074101d955460480342010150341c0d9070660401e00090441c40e400c280e0b10013184001006010622028481c00380080d111568a501a03001080c90303080134110f150400c09548103409101400c0c01699400c128100384010700407455520b080d800740540700070465030310358504907003240c0d030220725411240c02400400e641070300a1420009800654644c9a590800d280c05030800d400c00d01076400825040d0f40400100e44201424150074a24006840d4510045d6403014a40207031303680251a10180820f258520007160540c8041807202d80710103002d28a46107000130400450031000a000c0500820000408030705d40d40007003803406000d8100c1f00c003249800311411a078202003004417414071404001540b9544a4201071401c41800fa1440b0000d11a030ba0381a02c0c1c0080304004601c040808510125030783d6588500002c01d64005c448192660b81103040001015100034002901d8018400300a401070b6484000c54049075003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 844729316 1250 844728066 844728097
    0xf15090601050714060702190510050c09220c050a1e02070f080102070c0602030403020a0303030e030702090f070801060201050105030a03030908090d03110f0a080304201009050a05090c 81
    0x880000580d418015000301401030440ca401380300c2003600008085000f00420340072602d02d000301d00300000c4199000200200641c00824031680d84080f01c0d000250003ca050515505080c1c2c05804540c06001c80105518a003030044149900c1060b50f104400c46624107103000c6d80340041c144400b902090180060038001014107021100c1c061080c004038028000e2038804803865039464110318003039000044195000030000100040e441c3c000000c403401c4030350150081100c03614540f0140c000300480070b0740c0e070070300e0204110180040c6e44500c00b2a100b0108194003c0c07090600e124001d00d500c005130441025603152a005003c19500096618032859041c0f8000c59074480303600e40703a0a14000c80c04010f402480da5101036042542041102120400501c115504c142441c4942580c6801c2c03900c1c05040c04d601007000c42e01142080002d0a00d400d507980501031586235910100d08503503240104a000954591011301451a049250300000e1030100e400e8078036414038020130492482022030f020040c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 844730566 1250 844729316 844729321
    0x20a1d04051626070e1504030b0f0405150103030804261b030c43150c0c06090f06032013030503040602150c031312140715050f1509 58
    0x350000341c003241020300c1100307010450410403001751500c134200000e58480c0303e5420000c0c3c0303401148030694048030b401c041000136503165480500141d410240003903e0500075440100101c45603074030b141c8c0c02944640c0c3d50000b240390604007183c003503c04440c080210400000c5010180310004240c880c1800022402038203442d088644500e14400e020b000308981c024021070340c800c1444e0861100d04841d580c0e00101c5054003081d134a009480c040c5111814240b0003850900c800b05a0f02d007404041e41c03890520409400040d2215031030380c0310603804007000807042141400580b0030908e0001c0100f610f41024032100c4010345800800f001668090080300d500480c80140407900801c082c80250f8004040d01d80d01c0c1d03140d4600070340b41d0014800c0e00c0c000f0030a10300440c82500f2142e0440344a141192003c0140081ca60f03103102d1080ca01d101c841c1e04001602c130f000362503c200c0900030180c2c5886030240301200c424406c02c9009542c0300030700800320382c8450800c02c10f400302c40007078000e5050070484000c0d00c1503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 844731816 1250 844730566 844730597
    0x5180609010525021f020a030503060d080d060602010f0c020a1103070308070303020c01050601141c02040b0a02010f1103100306020d14040b180c0a030b0c0409020a1d040516 76
    0x41c083c0700c101c001e5452500020701d0181100036080403801e030084c0c802080d6101285031058111520a0303403100140e01c010070001c0441d125002443d04003000606c41c244049043c0c03154951500f184502507403607070391600200402a0244190131702c3d9103080350144101a8240000f946900c0102e10142000307000d00c5821007265003d10483c009554040c180c0703511030250317090040094010380c0254455600c0c0601182c203a41c010303010000400c0c44040d25030300c4c0440f1400300100108040b03101000c029000e010210f1895002c074047c3c031380e000c01a400018441c41201c0e448040e5480d50401c14040300b170801c148a80f10380007a0f001b4050300d4020102585e90b207110401e00004000c200403802402089505100401000303120080c021507050100390142c6019100458907005031441c038550005030520100001440c5121b0b09034130880c8044201d080c2540c0e0201d41d03003640c0c851240c01000408400c1c0d00c180c2e0742083c040e40f00710030384291420070080c030703066800c45441e00860401d0000e110800c081c042c01c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 844733066 1250 844731816 844731827
    0x3060b040605130b120a1107152c0c04060b0306150f0c01110c21030a1a09040507030c0803030112030c060f06081608012f0705030a08060a060518060901 67
    0x20400d02d0460b603510012045c071a0001c0400350340288a45060400c540107500d541415103180c55000810900808019403501c0b0050400180c4800c0c2001420246180314807072854043c2242e041a0182c00d514906100304400c851040c3c10082d0104000c0c4140040d0740c035120400300b038010a042c1095a21044014080402d010740d4030012510340c2000d28522442400b24041c008226425003101c08099451641556503412034000000b40c1c401400054142c0c107075604501040034890001359020030012001c81c0c011001124162203d42c0001010010000a114040018100100914155410a41c044003c0c040c0000d01030100442d9401076000d0040d1031340401507604601038100001a581d80c1e000b615400031404139201d0652400000034051018010440c105684d69640010001c544070241003035100200f038403962000c01d0201c9800079004100a10b161342c0700d0703200c81c0554a000010042d4403d03075500510f0420109101003202900083d901c40d511610031540e0310f441c3c005000c0101c55 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 844734316 1250 844733066 844733069
    0x180d050a06020a0e0406122d0614060316030f020904060f0f151d0c031008060708010e13031e030209040603030e13140c180d050f070603060b04060513 66
    0xc1e248005850007040f40c1201030b100d030040003540d083c0300b125a0360140707a0480608241c0a0071000026203240c03551045140c80303240b0050b02e80d072240411402500d8081c100c07851015003021000c0d0200600c002c510b820043c040400b0144c0442260305421551b4903071740e529002000034042c2c83d854010a04100d05034200360341c10000c4410800c4460740f03002c1d006000e404158000585d0107001e0f100454803d1402d50401c44000d0701183d03004040e1980800380405900082c80416038040184010500010501146001d0708071703a503070200f003541815100d110206014001c031034410030203c1c1c002c0000350000c46042d05807101c000600070445030414281c0203403040c880040d5125151060100400d500100c1540d400781c0c00341c6580301d003040f0794a5010204d44803440c2c41000c0d18490400a00d06008440040c00d2800202103642e88140800002c142001d1004000301c8140e08480010701c015003080040100400d803514060080d42c1c0b4060605505204a0040408001000554030751285500340d0100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 844735566 1250 844734316 844734323
    0x603030717130801020309071e050a031407151202030711060a0c020c190509040c0f030606080f0a080a0e0a08100e070b1309021b0f030a0311180d050a 66
    0x1d0018421031984829a80042070302c0d0001000303201c0c0070614520510969110f00301c00002131501030b082c000d58803040300501d5480c4186000c0840007107a152a40c03000e52006600c1800380c3c0100d81100301c2014109220f90b0003802c37042101c072041013000390b0301c03250300005005403010060b0340b034488179001c941d908a20702d0b14030181c0c4145010301c0510300760f0754040689103000e50b007039480d0ac0d4030326070800120746128071000000c21503241c4280a949004a2101d4000d44903503031011079155914481f0313903545229030060341d607039a82c0da400f00b0203400d0501039600d00e010900e01401481d041991030b5061402181c03034410030007103a400070451b1a1a0150018064030340001150904009002900060f0080c0802f0484501503a0b400045940d99401680c428140c0d00150710105030501600400a421960248084040c0590300c50030380c003410712074001b444445030061659200e500202506440c0c3d18041015103100c108440184081c2041d642c2d504840c08503610070911550b1300700303146040085000034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 844736816 1250 844735566 844735583
    0x90d030b01050a080606120f060a060201060f2c0c070c080a1a0a020403061e0e0d0221070f11010e010507051f020c0708010515041b0c050321010311040e030d0506030307 74
    0x81d10208d52410301e446000102c45120520382c0300c100403401c1e2405032246408a03043d00c0400e11101e078854041628041e5040003012007010b46d981807020860042e103251806000003e03007403050001c0c907462100130309050741c001d109400f500d980e440102c0c030ba0382100b4440322800f440462003030003158040303400541c0c0152060004a4400100c0d2a4211451031748d00c2e21300e1f282426640000700003081c1b0b58440641c68000c2e0413904084411040052006200c000c0f046c0c0f410000b210000d41780c2241001c5003400342e00300440e2601e0b0300002400700c0034110002418088148900c0d030004100040c0c1060810b00039a00640c2000c1820105003e03025002890410740152400400c006505500c803034401d41c100d0802318065580b0350f080c4421103440e00c645000300a03030f040e0316400a0b409540050a0944180200d03490001c0110003c0041d610f10442606203805000041003440000412203190341c2e0129000c000d108070217900ca507500e02c98612156005c41d121030003c0c08a56090040d01c028039000340a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 844738066 1250 844736816 844736821
    0x30f04200a140405151c02031207030302181c0602130f150806040b130911150c1002090108040b0a0227100906020c0d0804091103090d030b01050a08060612 68
    0x540007950b00c406031240990b1404001034078400b001144c00300307034281c00340034108003070340781020410716900014090741c0610a00c940c403000c208000009120044c040c0c1d90041c2c90b003000d50404460a100b0580452003944074148000141c404840880c841d1688075000690b10320b010a01c1410505c40e96004040c40103c0c4200000d141c0c070310f2020013001c018141e5555100d0398846080204403404a9001e40e000186c0ea600342c04201001d6010752903103030040d200700b60390809020014800071a924048030105802145071036800c0c40411185d43c0c0000d078414198208a0860b000a060340c400400c05010b408042c00422540700d450b42c1280c0800c41d00c079240d420390071b40781448801d03562040003030300d40522a55040142c41d6071107040c0400a1341c01d1540582615140102084254008118280c1d030b107100405c400103005001d0310070801c0340110025401c0c1c0303030314001004509242115205009240c180180c1c545241ea01c4004c032450b00c01541040b402a448000c0810824018401c18900f001c1d0500c00b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 844739316 1250 844738066 844738079
    0x80331080a050f1204152705040b0a030b0403050f0f0c070614090d03030c020c060c0606010e10020303010513060b0310030c0504020405060711041404030c0c0605030f04200a 76
    0x1c1c1074601e18041d0003101c40b504032940c0c0540d5942002c850388a1402c00500c4140007200d110309070f07561241d4440c6012020038400c006041d1480c01d1070900440d0705050000708010604144c05401c89010742100d17401903503880d5454616280300020f200504000b80000c0d0200c140c40d000081ea150112125805512808000c800d43d07a50482400703807001140c0344000900f0200c0c100800c0301c00030000584010300c43c40b2a0f55064029024444d60201540942080c0c0407903600c1e404047c0c610320070700c5002406141040380025103051803409201e40a40d15604040008940000449045640940b4403401c1c12a103851040300a254580003900792543c00400e1068000900102c00f00b03603801408a90365543c0e0361002c11040b032050707105068100109009072804141c52140010746000301400103d40021602000e440da0201110110086035400c8076250030b014140e40f400d0041c00e01c2d42000307469424894403e426540d4001d00c001c1c402c10004924200d4500ba411030322865800240206809644504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 844740566 1250 844739316 844739323
    0x20d0e060309012414040501050f0f0a05060d0212010602030a05070b2502100506010207050a0915051504090c09242f0c03070b07080705010207020a09021804050108033108 75
    0x480d4076040382e850b0b031707a404040c0f40511036941240d0009000c80c1d960342a1109202001d08808400742c1d010b5002c20f00001d90780c8501005086c0c166012100603543c0c600e01d16003040b00101038015400310b40c028400c0307406054000d0304950071a504842081000d99441d02400f076520101c40418072810344440c1c01620140c6c001443d0402c83d0290f100c14402d650b1044d004a954100038031030b80e5401100000c0c100901c0c182d03540203401210142891a200755120004200500741c14424100c038180b00040400119069101d503844119840c0340c0181c40320303d440000003080c4070108000c0f05144952080c500f12070b004140092500e42ca0100c416000380b400b400e0300440704551490000b0b54028401e59507010320b8049203a07070540303190762a2542480c3c050b40b40ea00c0607403c04c40044030903640c01c00c04000076071b55450b002401002104c5016a86004041800e01c1c0d50070b44400d120300031402c00005002c608808030698013200501c1b0141c1c6202c400000328000300b09034400c50120a0190744402290400020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 844741816 1250 844740566 844740569
    0x302061c091202010b09060109060f0507050706170a140103030e13090516060309120302212a09030c04111608030429150d30020d0e0603090124 63
    0x6400800c56031741d08905001007100c1c200c07403890005c1c41609003482518019400440c2142c05403a005041c4031044ea595850402181c02540c086021408503940715007103840342070b80c88a4484806d101c00c3c044038100c480003d02c180402401d021410b10020100c3c0c481034060300c0c190610100c1407100c8101410301e20746403510501409200d004988012032054007a014054007a036022905001905191504130000d40120f8076403421000001401e240d02d01400d50350303a0090381a5891501901c1d4080748221242c00f0360314078030300c609031706100000140d540070503d00130440301030310003052400304640c109106204109100440d0031820004100344801c1d200914480c1d4030451408500f020b81060a00d9440f02c1540c00040350211840042c0070307200c0364400340b410004041e046010601455485000840d1241c866903a02261950030341400d0078501c00452000103c2c1c00540809694000018036403207400100f58000c05000010072200d450950000c001e402c1c40032400e2085a201e2400e945002985 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 844743066 1250 844741816 844741853
    0x108030406020c06034f210207050303040608091c081506091917010b0904150603140a05010b0f010f030207052b08070e0a17070f09020409240302061c09 67
    0x41d081c20014066218002841b141e0030241c0009403400540414900030821011941140918040004d1948040010717202812245d141c401da03616108041c1d51a185800d4980e13041442071140d00d0311102d030051286034224034411b0003240800d0181000c50203034412042e1594111219441c0103143c00d064210280a40d00e030700024510451010301000c2c2614814000ba03030b4468017850100f40040c80c2540e40590f10b014020010038001d603a503d8120305500d40420b40d0f001e03034114003401d900304102880303004081001106c07528402505403000905030300007644550107040e40050107038140902003128240d21015080d001401c0c9003003600501e0340e8000003030400089610140840e0243d4000c0f500c14400c1c010140070899440c2c9401c0d00e01c54958400442c0c600180201d41011074140c942c014094050b119070b0802503980e600d041c0142c0c080f203403050303440c200400311141c440080d00c204030b14400c11260122402616034501402041002940728640700c0054a8003d86004002401d0810490f0541 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 844744316 1250 844743066 844743181
    0x3011d0a0201090e0c030115020c0405040f0213050705041806050622080309091923060a090b060d0207080d020a0801090c020303041a1806010b03040b0108030406020c0603 75
    0x2d0f1240401d0b004141135410003220b041c06d200500650310f10031000050088684110340b281c0c61501d01041c1140c80a0b281a1606980c1601030015810248603030036402e50850001c009a05d01100010400d01840c050010040ca90700c4020200700e00d160410000f038200100170b156a00c07103003030103440c48410a90060740354940352000094926004410b850868001030720000d5146e0300e6849880288070700c9420020b055583c0c00031040340300c1d900880034510742e40000d8640307840e0801e0400c111703a04d001640488036160400001c140280c0f02e4a0039036046048122003d40ca84040c3d00d4114514016011440d0005102040d46800580e00940c054100c88806c00200400c2c083d003c0120707102d100c125406000000c0f101600c1d00b070b00700340c480d9107175100c0d43c045480c0140c16894a07415051450030780c400c48440201200f0302040c0001e00880a00406054005618251034100301940341c155800c03031117101c0d1f01c0c00300000d00702101c04100201c100e07904d240d02001840001184480d20700c6a032000401054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 844745566 1250 844744316 844744319
    0x6082406030c0a0f060e100203070611041203020604050c060a0e060a140a0f0314060603040f140a050f3f042105120a0903060b0f04020c0a050c010c0c1403011d0a020109 74
    0x40c14034a500881070b11323502a501c1d1019035142d960152802d49a0720034408805c01002902200d132984001c181846640a040c150a26041c030381e1078041000c10707080c41240304100c500100c40d000300920084400944a01d52540010302c0245c699800c1c2c101002c1030000005a00104280d01c0541d41c4010000c58030304201401c0c0118034070003207540865031260845070070004207000c640314239a221403a44c4201c601d0110070002810710b03410160000350881d120b90046c5940010703e0024400c11141d0f51015a03100264000400d02c10a41d16103d01c0542c401e540000344055564030200071a00504240d07207a10510380300e508240b24802c24003520585107801110000c00180c20ba5204451007049180d448040941c25901c0c0c81000340040300d140c0b039000b681c42546c115503071914000f80103902041c0019202800581c2099402c145000080d1070402501c98070b0b58000680040c011816210800c5003c1400030320880481c0c01810809030800d51007491342c6a610540e40005001101d0038401e0741d800c950107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 844746816 1250 844745566 844745569
    0x7110307030806010c06110408010b010e040b060f070c03061104081516030e07030609030c0c06090305061602010b0a081b06031e07210902010306082406030c0a0f060e 73
    0xa0150344002030000341400c0c041410781d8811880c82100307a008600024600f002c81501c21142e910581c8241c40d681d4480311060b00541c1c1000c1c804132440011b68061201100e440001010307840b80075140722200c2e00c0450341100780300b1036500440185900100400004070180b2548515802074402d4071118071035000d01440100072010168021248108485021001c509099002e049030015a4a140c8241100000840c1c418000c2d07040a50090701c0c1c0c1d11440e101d9003018030000615800178002e101030100f041000401c00900c0d907a00210300d818440180100013000c90162200d07102c82680080c40142c0414901d901080394a82c1c0c91181c0c3c2e00803c0c0101600c14000c850104403840110040340c103091060043c50051900d41c008154540344400002017501d0036000100d0803420340100d60f8507103500b811541c05100d40c0000c0c02e0030500512648181704131200841c0890819000c034410b00c00d0106019850030024040e0140c001008102c40b0f50300c0304518094149076109d0000010348844418681c1e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 844748066 1250 844746816 844746823
    0x20f01020c01024803070512070306020304020a0b0307030e0601050d02090a0f02120705040602070e150f130c030509061f03110f0a0303210b1804050102070c0e0711 72
    0x201401030b000382c011481061011440e029984400401c4c2c0790511500d66072102c41325070600210182954030102d043d2100051500d1315029820041c0144400c0542d4502c41d00001418002c581d4000d00141c0e4a903914404540c4010f01640a014000e40100501103056096040749401010f07c004980325030ba80c560400c031302c5140994002c0c0d040003189003c0386145265030404140380c0d0400c4030141c60080040700301318400c102102c100e00011800704007400821307814442900140f1842508400c282418943c40c5001c05854510718452004c50150201907140d41d40e40001d1881e0800003001101c05001780a030180c28200c6144c0c2190248074002800031001846140d00e00c086040030006150a5a80d00000980c0e2080c025900c605650021145540d44801503400781d842a80c500e98201e11000d0020710320301000300a0b0103403909014440b14551102d5082c2c030440084c9400070596500e843c1040c2c0c1c02849808070240c0f04030500c46000c02c600c2500101940103142660780d4009201550420b1601c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 844749316 1250 844748066 844748083
    0x1d06420715200f090a0f030b04060c03110412030207211e050607050a0e130c170403050a0302071712091c050d051503010f0606030b031b0d1b0b07020f0102 68
    0x120b110040c428038411a0000014220b040c2c00038010524080d120040c8160001311940111200d184181c1004104240380c0541d0022007101d0401744602c0c0c0040800d141d490040d40110307816071b20b100d038400c000d2500c200f00c60001030960103090b24400070100a04c8000f1512618251b072031841c10181126843d508050003904140c10038081c060544031804201c0d0680d01c40c07003404c1d0420403070404425141d5204044c81c14000380b00480052203a8804201406400301225456401c07541c420811011a030400200c640101d250301d00180d0b554054905480c1208202106580c0110b022402490031400c0400c0180112055400c543d000d9407403c14000e1146401c4112000242092080421800d0281c00c4660000c1032081c218858848c0e0f080401e0840b1045040250034a895850401c50703d81c05d44142a10010250082c05000e03d941d42205161030948454501542d00544105c2c1131060440010884c13000c4151400e080c9641d4888503111034005070020783c81036507650800002036000103080c41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 844750566 1250 844749316 844749371
    0x106091706161b0b070c03120902030a0303050a02161a10061418040c1d06090a15020f100504030210020c1b191d06420715 54
    0x1d55000103208a914140d02540f02c220a07000328243c800280b24041a188035502d40d541e0340401d00e5903410014040100f17002c480340d81518021130398000d61400b003440c521582e0103003004201921040d102070000d00c0303845403103c481c02e00003a1040070091048403440103582d01e0201d4100c55181c03640b2042c005106032165901080398a484681ca01c500c00d4003514540048445014445010030041010f440c08000c040c0005490f1900214a40c4012080c04104080554009007001d00e001e011803006c03101e600031071010b00520950303840194800c201020f100c80709482070300c404030400c00c03011000d002d0941c0c00310b0140c020301030804200e291500c02e44030500441c00080c0101c15070b01c0c1e41c40044801c0c24410f640c010001400720341d080d0038211601c1009060400002480f042c1c5890000d44030440640907034812102010051182c90540e9040d20980307105000c0360703000d124140410071003840103d0340d91b100460003094403004e00011032200a40d62580000c24061b100c840012826070b2407400e034a11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 844751816 1250 844750566 844750591
    0x50d030204150318080a0e0a090b030a030302093606010305040804380903060f070f14070c060305061e031b0406030803090604140601080c06030406140106091706 71
    0x45891880f83c3c0008810f0120b041c5029602c00c019122625142c6c083c00d91a0080340211040b600d003400c0c9042c0b00001842004c4040001650382da0020f5100e191791280501059004181001d003691030440c1d03000900d8105030561103244601000740420f035464500b568441200c54005041035020b809400c2c4296031095902d890705091800a440ca007103503920101100d030400b00100d4003464880d007402c50006c445184540c450b414034003094039025005000903014940b190038010400c0d0090010503034404d003820030030700201c0c0c1c0c82103035201405050000b50980b00300c002c000032500d1305503000038018072007510101c0c0007807175880071008806c0d5501e4840d501580009010141c1c01b030b0303589080c901d1660090000c592207940c0e854203030300e680040c0c0e8002c142e908a02e00380320402c05030710f0f03444a40e0724241000e4450f0b9890701403450b845500c0f24400700c5c010003000002030104003413940880c10b450700840da02c11207075071201e078010700314100c90040c0030000181c00300c1d0403400903001403601d10861418694 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 844753066 1250 844751816 844751849
    0x308071e050307050c2508010218060913050c13050102061003030f03110d0c09211118070c0b0912030a090503070203070e040c15020d0c050c10020a050d030204 70
    0x450701680000c0c0b080d404c22a0500c107030503550f0b10034402c810400c0c001900c015500e81038103404614444542d0301c007001681c81044030140a15a0a5925400d010101e401030b4859002c0c40c00724200c08451440100340da40b5200400c02e840301c0800141c0210740d000440d40c0400c0f52100016a0748440c02d46003202c02034000c4c4420400030307100b103031ba014a0040a01d0007181e2020741d9511030406400245044100949900320340c100d16500900c40002401d40c4070f5940c640c502c134103806080711440d60781c010b40001c0300c64180901d15107600740400c0011104036403100c61490031100c02452011581422140300d4a40c1c00030820f822800210740030649240c5283c00c5c80d5071203d0380000010444c01da4100d074580024440f140c0981c2c0e09201c08030080071202001c00f2145028a041c540e4000150071102c616040c400c0341204079540001c170a4854455800d0080f00e00d801410107030319000101c0d480b290300c12140110012880d0303002c2340c114125440ba104a40c6908c005034025000c3e401a80690005843c40303054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 844754316 1250 844753066 844753127
    0x606050c1c1b051b010203030712050403180b030a050c0306030d0e0d0515100b040303120c0903150c030e0114191407031a040504050c0f130612030807 66
    0x7454902805003803a10307010024148041c80001828001e03221a040f6100d161500c60800f84851200c44003440a103140d4a06a000070f00340284c0c002590a9981e036440004040600407c009042042c10100a80405540d044d04602e80d40c82224080001410b09012464610049040d60701a0000401610840750182c2044a285602c0721541d9408900c2e0030b080d101154041c0305070f11151901000c14101c0c1d14080f000104501c2d01076000c40745004003000204003090f4406039210030041031a001103143c880c0c3c40f1040741d4403480c03500302500c01d48124010004108107230f0b12001c83d2880350b8a041c401070200d401214205e8400002004405c04100300240d5554203041e041340d400b1490f43e00c0020756502c3d4059624400d04111081408030382d90710741402c0c1c500d5440b82081301c2c03090215810701c084d24282d595180c0352130447d10311f18003984c000d00c03000c0d0f0300c2d80d60090300080546460400b005015540c4c4099031785014404019404030780b1441c0429005489042c58504104014440d580807044511 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 844755566 1250 844754316 844754353
    0x30908030606161a060102160b3a0615090803040e0606070b0405070608060306190c050c0a15060b0301080318040b12070810020406020c0d0507031e060606050c 70
    0x4582d100c3d103031586078985001452070f0207152084040c07800340074120320386040068607041c8040d071000b01c40c640720041000440c031a9000c894190f00b040ca4030075041850410310203040c9810544d02403c030a1148408000300080d0341c446030172070743c2c1c4001500e080c2e04010010745000702940101021504200024410714264501350b0340c00440152250f071801c0c01a07151200b15840555044035a070700800000c000c1c03d9800301d40700ba0800c400300c02912312420106006005d421040c503203800260b84030354000d440345000d00c064603040c0726070006036151000d46140c03103240b001413803580c0c01d142c604e050340c041086487e01301900d05032490100250f180445108002a94014070001c82e40c0c065151017900000e9295101a07001003403000c0c0c000d041841c103151905080002041140c1c81c1d00d0710520081004c20350014441d4645071003901c10100384d803010b081c4281010000e80000c1e00c8120956000c03c08044070a0314030a801e4065501000b0843c0c4a80003200d8900c07d2148802c041c1e4881c00d200440d422040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 844756816 1250 844755566 844755577
    0x19030605190e041b03051005070305070c0f083a0b0604030b2203030e0c040203060a0e041401020a02100c0203070c180b0307080a0606211202070504060902040510030908030606 77
    0x8910b56410070130280c510005140c0c141d08111000e40000790462210b10380c0d4007406400103140e007010311551800c81c6000b09694985000600501e07a80c40043d420300544804950740703100340400341c4000401d0050511412031461100130342c00c84c165a030f0803141988900c2102c01c40000141041d00e0185980c4610b1138241000e00580300900780b58004502c2661800311904145120361000b25521000180844c00c060741448043c1c00f03140100100141c59680741022410781e100f40d0b100e01c03825151401c0024078804200c11201c00781d840015190350560300096260906903101c0b4041c42900314034401284c42e4010f100c001051800fa001061040410204050340c603400c105030005030561a090009150080799480300d41c854106440f1842031140c107014010180003032000c0c4036104803240030b041c02c00c614024400380c0391004504001d0381c5c061081c0318081c01020010028070038503480e082345030002e600c0791250b40d105580f0302d44140d078968068086c0c0c1c0e0921341c1003421182940d407210180711130307580003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 844758066 1250 844756816 844756823
    0x12120316090510030c020c0a03170f1204060915020a0f0c050a0501050f010515180609011205040c0501120e120a11120d110c0a11040605030319030605190e04 69
    0x3000c802107a141c8501d0003d211452065034003143d80003254002a00300b19401d01d02d10b0140b01101c5080c004950f10100141020321440b2103607a41d540ca0791201c00050003500030700180390701441d0500040c402e041d00030315242801200f140c1d450300c2406010340100d10a001140000c50b190f00d400d581c03c1809910004c056038041c0c81591140303111540d40a08495041f030300004900a00c80045c4041d041c409105d1003080350401c00b1074640f02d00040080c02074800000400c2c401c050005424481c0e900c2801501070448104cac409210608140c68400580040c038002c1500040035118101c40c4845140142c2002500398805400d40800c04203190a184d40424040014032018114001c6441000c000c91f0a4010035004419150b180520303901051310460562060700c0f070414803201000b141c0100b03108000580c050443e142e8151181c000c0b802900c4680d001540c0341c000801d00e081e00b454002c01c10310100c4203540d0100000703504c030001c204035588203c09490301503070320f4101482002c480d0305030b0300e030414003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 844759316 1250 844758066 844758077
    0x30b0601120c0201060e060109140622090e0d0c0b0402090903040f060801090b010f080705130b0c0109030908061003020d1a0408070b01050114071113020307020c12120316 75
    0x1401c12070038191041c401c00740d00181c0d0354020400c02040309140b4190000c0c002d10303082080380c1c941003814140300350349031901b4803542c00040d44160145070f540100401c20408020918219a2212094000e103a5141c64003102c0c0152a01d42c0343c0700340315509841065031700030351034802a22640c00340003004c3c80042c80c1c0c0300c03e44020000850a012000c520310000c20031540c070031030b00707605005400007a110303090b4582d030500103510091358030a43c110320358a5001c14a4502a6101d80c54421084140c25465010ba00e42c803100089042001d4410740018007491302a0f100d10080507561858a0380d58030b8200d1340e980c03098203034520170300051805110b0300c110389001d0340201202100a030002d40003034106a03000c90707006000160780403c00107035030601e500621003402c200803580c0522940d0282c912880e10006c1100600c0b4008411541c0e5000c041508212085411500c81c5030449001e5690607500a0280c49200b08044046080c040040c443c20681d50006c065411a1149580d02c80b607240d030804104207119 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 844760566 1250 844759316 844759337
    0x60f0603013c0f050613050d05070b0708042d140d0b07020607170c030412020a0b190b0913020f45091b1305040803060a0b0a09030b0601 60
    0x40031600e85200e1050b00c498645005464840e109141c810701e64005801444c0c1441601080940120014122002070381d142056224511f041030601c15a5000541540c2d00400c1d542d05108819002d00300b6282c003503070b182501d1603180311255100145e15010801d100801c58041c04082919008520300900180c807110101a99a603002c0301180200c504100503803100c0c0030045440d50110758120f500e03403000350902d21801c20701001d0209120040c000340c0a2000c00708e2a00d0800d00c02c01c151302c2c25541121610317020781841d10002c15007020b128110007000e4202a03400c0002c1c50403098031802011020140c50350810180c0c00e000c001c080c04240035902c9070000c0070303c1c1010b500b2020031181d14950010360f03a00e0908203040740104a03440c403903030740c10705503c10741084064540081e00a50844d000e42400080080d1000081c4418102e189020200782c180303800d01041120910246024020442c1c0b2882c046403265020310060040c908004005440d0300c0d010400b042c0600f40e4907400440601d41000c029 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 844761816 1250 844760566 844760639
    0x51009030c0306021207090614090d051b040f020c0a06090602040b030f091c0221090d030203070506151807090b03160306150207061404050a06050a0206060f060301 72
    0x1580194800e0f540e4640024071a045c10f0400c3c0b6085920911300c0c1000300466080c0361000f007500710036039440013492000040580700c596410002c040000e0b805402c84640515018030407031800f410418050142e4107121795041d621187d0f00035a5000b8040310002c001c40d00303690b2104806802140000d0341e0f610f908100c0031445016510041d4030400034a10700344002d0401481151a00050071442c40c1102103124042c0c40303480d40403995400d01814882000141c3c80140b10360825407094855280d80b089503188500105034000c000342500d40e0080058901980e6200d182c6140b840c15a40150f40c08090b54002c01d03441d54102c40d04507080b4101d0f1811061058030781c0c0658115500c1a19183c428050300c505c0304012580c580582c40c00382200182e9a40014030419000c0c0d0b507601907008100501407918082e0300341c4190042500c005040080085085070359641002e0f046500009007000140075450001d000d41c1003052803040c03041030180c40c4900c4c40c0c0c83e0640214041d42c08486000300c440308000340c40d00b41c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 844763066 1250 844761816 844761833
    0x30b0d02030f0a26030703240f0303140f04060f020a06150314010b030d26040803010807091802090a021303050d0e030c0d11060d0e16050609090105100903 68
    0x20199030030061000c4815410203504415150504c00f07038140d16210494080b066103820707650060380034200424284049402040360392552000000511002d1100040e05131002c005201147c2c001e48600c8640c800030100ba107481d1103104411104800c0401c81040694440e18003010109414416074859224a81e1001e040c1c2e00030101c01010020801420700c18000484a0078100540b920002c001d00a00000401d403035004500281c4240064148841801d59129500305005003424034450145d203040d147c4140035820030b02031490303588505a80811802100d01c5001803129030704034440c1c2c00940c65400c02c071296800600d4034402d507800303002d000f03007142445854001561090020740745511000000400001c0d40007a864482c1d440000c1c04100381c0c9a00c00e002c8001c0d030f00705400450310351154010800700e00c43d00c106569412325015080c0d01c25070001c10100c121704420902c40318080d07590f408008403801140750711540507040c00700401c881c0c50900c2121100c4062828449101aa20b03119002c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 844764316 1250 844763066 844763083
    0xa080706031506080403020703021e03060c2d030f0a1b030b01020c042a05040302120a0330051906030f05151311011403040318150f030b0d0203 63
    0x400e0716110076110407450841c0b07401c05400a4a0122040d10b01510000d42c0e5203030760312002c4d01840141d0f91070519214400c5d50708008417006811215079080c0094200c6856202d400d60f00240010101048a112101259000c1406001d10b8590950b194015544040c2c1805400f1b941880d03a03071006268280c0a02c20180303188806501c00050000e05240064249843c80c825544207910307145841c02040c80f40c5100c000c0c0303180b007000d4158262105c00c0c01980c4604c0341c0d07000654070072580002080341071000071700b039007101d4401e81d24180003004c4610000c1c4a1119071f46c00b40098100417503600c3e4080707650750047ea440720454003000d103c00700001c4050109c55480d041503804580500d050320030b00c0006c02c078004646600403501d04184c50680507205407151072010040243c2c9103d00e45031240d80c0b043d0320800d0140440050b6607a80d0800b49005041e00f11410f820388200320b00070300d0001c0c55110b640e001038048459a15001611052684200e001f00745101140d41e0014a00b203a280158600300444030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 844765566 1250 844764316 844764329
    0x2b020a06080901061a0a1d04020325030c0c0b0604110f0c1e070317040b180f0409030206131506060203130906060c080a0c141b0a050306150a0807 64
    0x1801ea040040120b402d441031900b0980d080c1d80d032010410b200710100b20494010000d240ba02c00340e1070000c0029100c0c00e42000f00d61729442400031003072100100d00b4130440e81d00402556500218510710a800360290344403c0083e8002c20031040e82031011440b01410740d580594020301c0080c846000e4518421070f900840380209800d0408600c520604030100080040c0c4030104c0d1080d17400648203090301785d840c102400000c101c0315032042901d481c00c103050250b8020700280c03002d0310345442038100d400720301940c01e206041c03040864203050115800c0a2140040c070755017687c0501259a161090a11513184d00d10b01110401210071380600d624100e8410b50020b80f046a0196a8074403652061001c5c034801a0000021a07150402c10819107030010342410901e50702040b00c80e20b40218400907503c6040c4580080d0441d65a00307944144200e010414240500102640004001ca044280100002c0c0340c020103406502400104864074072080380345241d000014a040d603140e464542c920b08050703242e40f010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 844766816 1250 844765566 844765577
    0x70603091a0c03072d030e100920100e0f012001020d050f0112120c0501180204051302090a09050102071209210b1501021006030803010e0a0504022b020a06 68
    0x20003642d5011103505600b0340301c00413060314039060707400c80403030900126004006c1c103551f410a5083c00101303000b0b405595120910400003002e041c1401c21002d45081c50070814800e41c2500c0780443e1801070f55001d03800714196911010117285200f4081800f149855090501400d07e24001c01c3c3c1480b184100d90300c1c80d5400c009a125110890084140c1d80098904812054032900500c9070781009141581d07802c0c0c21040390303001e02c4c0702c082c0305a5041542d894090100c3d4200740154030700ca82007580a0b5025482520200300694448036500504603c1d180001c0d4030560300e030b01140161825412046605000e074000500d0322900da40c0e444000c2c80f0084008001c54402c2404200800b21449171601d40d80810944111301c20b03c42c0e49442c10034a0090961340b100391000054445a40b00300701e00c000016000c0000c02080f83c6900b07000f030a980091049000c0305000800244100c200350007524003032a400f60461b00085002c034010707413080c5c0020803280080d850451280300545e0710000003100030440c0d500e03030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 844768066 1250 844766816 844766821
    0x204090b10020303010e0a090c051804031205090c0d05071d010305010c1d09040c0906081005180a03120e0d080a05060108040c060e0303120709180509070603091a0c03 73
    0x1800050010000c4100c19074105100406c82220703215442a4440031003440012116110b05e010b403680e40050700420381020440003e005003410560246004600a440f000819142081843d0540f0000c403840e00b03142c0c100d1540c3c000c45060040e800300e0702074450b20a840c2d80030f4562022600381c108101d505203400907888010401d200d801c1c800c0303850076102803801c0814860001d81850b0310206450341c281c0610701180015080c80480305200c409407403800400d100035a03071b03102c0c52650f940c16014007281d81480d1201040305a4036900520102c4921034021b07046400d5640c80550f42d00347c0314881446030f651540700308443c1602c00c2c4000c4000c0c1b0420b0b200c220203820705d90701205c201c5400409003418403070103e0a11010903200c60014040301c03414640355110a041601290450003600e012038034039201d6038140305c035883e008810b01082d2503401d242945a0400045800c0c21348a040e240417040340c0001c002440b040b80300e600b0155031603009180c20701d0340320355030400d031000500b08480304600d12001006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 844769316 1250 844768066 844768069
    0x1e050610050a2a12121a0f0418050c0301180c03031404030503130603050a0b0906060901030b0406120218101e08100518030702010e090928031206060c060b0103020903010204090b 78
    0x8444100c4c6017262000c00546541c1044040039580c6000c02c1c42c0b081050a034510216611501301c4919140a405800c10f110502d1903c155074503042c5800c1c921030b50920081e4541200e410b000010081e411428100030381d840c6450a8442850b02c07015882c496004020200100d0300410040514410328000c0604140c0f03040002821520301030b00030380615041080884a955076001200e8100f0f10486072942c0d100f41a60060b0300400002809580043c18a0000207034100c000841000640c025148402e06940400e00b03860801c0040311007008000c0036101c24010f00c156003000d00d01d05010710403451001c07074454101600d054001810100d00548400802c007006c0d5006456108840c3d04000075401c1c035a042e03001030241c54001060a00900c1e081001500070b400800941e220f156108c5140043d88400300c10000c0800420901903010030080302a481003486244542021a4000c0e40c80c50f181c200c19580c0d5002400101810321304150b0240555011aa0207200030001054216000500103a2000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 844770566 1250 844769316 844769327
    0xa0f060c051501080c310203090c060c0d03091a0114030705030d0e090606070602190305070206010f1e180f0f020c190f061e050610050a2a12 62
    0x266520000e42d00c07800401401e200050080e4280b0070460f141e1140d0111400080d207000d50482ca6080090701c9011814000c201c1640190300551281d01a558800075001c00d020300d0344180904445141d0203031441485251282d4000602d980c4100420328640210b840d4140f0b5145080e0009104440114002080c62408108090003414180e01030400c2d1030f00c0d8803024200d0b110240c0b85601402c80b020004640755a6801218002c0da40071808540f81c96020364543c440c0e0301404448404203240c640030444190000500b01c0c102c6a130003008200705800c003094030051110219051021984050002c2840700541e200d65241b110070803c0050500607904c016020760380d130010f003544080e1042140401190001c2421226010701c0c00d01003100c0440c91a0074800e0111380f50000d820b880c500030402c83d5043d280034400c4624014080c040c001a01c6203010000040c541c40f10711004540204190403403503010380c140940004180350035420741c00c80284001e2414451034021251141d2107141402e4058000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 844771816 1250 844770566 844770583
    0x81219020f060a020d0e190b0f0412030e0c0a080f070605040f0e18010f021201140f041a0925020607080a0902041803032a0507060b0a0f060c05 63
    0x1480141401102240e010ba19407034050198a1155000904071418451030341000c00e42c460f180302210740c0135800c08075214820704000c101b01c5031081e0617004034100102841c0d04a0103035400030341c00007061181060030782c020100300c5a4070001e4041e81110344655038803401280001c06814010306a0101840c420b01c0c2407011a8101405110082c0300502c2103d485504600555165940710002d03501c80c0507102208010350350b0a40e2070f560070000d0310b49040700c580d006010b5850301c03d4800100c9036210041c0070848080a08426001400664105540c6c54590043c4100c1e044440c04c02222050032804140c540c2e03400c984404012080d00c02c81440360000a00249c074a07612407020300150300342b1802c020000400540095070181d22050f03900150b603210362000c2e4070074595040100c510f410030311380600a48504e5001d1520080381c3c80e43d1040c0d03c622012007502414065079032610300741c4580e0359407004000c880c01550700440d5401c00440e000d03000c0909140503201e0340d200d00d003806c40185886854200c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 844773066 1250 844771816 844771867
    0x6030e0a0503030121050601080c10031109130f060b030405120901091a0d050f070f050a0c020d0f02060403080d0522020405070e10031e05010614130812 67
    0x40039100811404000d90b81510860121010400c0812601c0141c1c82d41852000d071072405440e00014071120001090890300c901541d840741c0c2032150040c151b041f548501c012107418401000100403e10380380c441c04504802d4034000280040a0700b008001f200e130f40d6045421034100c00001c1c0410b000040040410001a0310314441c40c007240f00300002c10320082446030a010417400030070425400580701c181e03100140d500030100114075061000c2d400c03500c4182c0702c000c04516040392030000148503504840641640c3e490381840c85207250b007802038041c0781213001d0301c17124902503d200c010f1b44e4581c002d00c01540128046522800242c159600b00c5502818070394941380139034407550f07100f4242e10260b24002d4049038002001e0799075a01c19141207940400c210b078010810814562825050750059020360079440c2a18405900e40807403804554080c0100c90104088215130b00d5100e0076407008084115480e03068400150380c44180c45d1416200400f1440000c3d40400e58180c058665202207019055 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 844774316 1250 844773066 844773073
    0x92009061504030f03020321010e101a0c070b070c051e0a0306050a09050717070801140c09030304091104140603152b120f0c1505060d0212010606030e 66
    0x208803491980c24456444014000411307035a0301e80c1418000d000f82e03045d00c690a411008540d03103550f00c00302c60700402d00440c1c40310f0030316a010903081c071417824500742510b5856021007907078594650b101225411a01a034000c83c40380e544045910f0b1000b00160401c180f10300d0b00c03040d2160806040292510703210030541400402d4160710811513803484505011a40c10503000a92038a5182920000d00720401d00901940b040c060001070040d01500002001c2640c0c0d03098800c0c03a5283c00500d0709882c0040e0500c20303a03280c4240410014840c0304003c0000000c024100e81c9842c1c1e89495020548001c1495040381742d802240c204058a000780b0072011035282142c031540307180307070840588102c41c0d11074614a001c0c0c64100c18484903c0403800b400c0120550745101c0c040e48071103c2c90610740030f1b0400d803c410005a002c0c8002000315005802502c0502d0788030540202105144121400a0100034580381c3d014030750320300b40c02c0503131100c0031145081c4004070b0010460500b420005015038500407011080340d070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 844775566 1250 844774316 844774339
    0x1d0106050d080d0c090504020c0616020f1507171003061401050d1b091e150302011b05010204092309060c0d1107061b1701050604030303020d09200906 66
    0x42c004000c4600301c042d003007000038082c0e6116504076961891508426000f03440003075052041b0000141081c42001c0c1c20002e1000140c40407002c0362180c00c2c604031501d0036132002c0c400c603160300320740d910059100e0540d18081403d0750300b59003080000c07103054595070fa40014224060041c00b0041c0618080381001000600c10740d407400b8003041814200c0c61001d8128180301d4100c0c8200c8070b00b04840f00080410f400244504400034601d9080c518500a46a0300caa2804075849150104503a0000c00c990b0141c6800b0070f1440070503a80c3c641c0881030380e001c4510307550800001c2918241481001182501c201c030848090320074000341c901d4060301a1407114103034092410000c2000d540c50455840186203203010901c40b400003a000e6103805003010040845051000015140c03034030340c02c030780382c0700740240e41e03484000c1c02d0f41c2406d0984c03c4081c081c1e1508501d080005001280c002c5c2c00400381400341c400c0000b4129a15210204018004c4203801e8800341e41d100380842a203441c000041c0c015008a40a50184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 844776816 1250 844775566 844775573
    0x5190b09030f031504061502012f03010e0705040801090309080d111b030708010501060302071e020d060911090103030504060f14040e07170108030a110c0d0618061d0106050d 76
    0x2804018150541d03541c0d40c007250412503c40c3e42045004040101280347c070317614868000b901030211501702d42c034a8605241c0c800d1260110314000c9088602c01000030f40366900300010064100380040c01c0106222040000250f80b0b8408d00c40d580c01c0074025603d45043c10f05202c0c0031810602c0c0f0201103000c00c140815810003ca42c0850f1b00c0c0101e00c04074414501180003100032a0030028180d028000c4d135403070140002031054064004121031480341d1141c028004040c180d80d0502108074101940154002500000050456001d401e07814003942840084055000002d0602c403001d82040f00041c6011408110316034000c00c4262007019141030035130380138095110411080c0202d100d4140141d040d040400d111a00456410138281c2921190b145e0540e110714a6980d250700907840c12000620317200c484003100302c002c2a40c810403980205006aa55550703201d90014200e80c80380c075201459102d8900002841c18424010b88080c0c010344030341d205040b507501d28210f514560055004009559691002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 844778066 1250 844776816 844776847
    0x40303080901150e0703110c160e160804060f09060c030e010e030d11040e090a1e02220e19060501120f15020904090807050d110c09060d05190b0903 65
    0x40d10781c2d00c0d040c0e204c1c0e507444180441c01741442c1d07041c0131000800042e0303c0d0b0484401080d0307201d0100b20744084941403039803180c0d00480042c085520243c49020085400110743c400c00280b40c125000da100494810600211407007110040c032000c0740c003d030b603890811300200d415000c1e00c0d441e81c000400800142140c00d040c162603100b06a04003481035981c0c448000400b1010342664040c2034030003840d0a051038a080d0850b0348650204e03050f6100c464030104003200c140d41c0c1810310800c42e4050700768021a00c8034481c002010b1941c09104004d50389403201c0c8a10380100300440e00d8084401c1c12101d00441545c02c127001110b4061700003105045400f085031011412180300b101080703a0221000188801d81882c01000f0300a00000550290402c2c01135801d00c854031014040b468000c3e0140c0d101d01c0c80c07041c2c045d43e9041e81d5020582c019008458541020b142c60343c54658400c1c4040e01561800080b41d840c41d0a090f1000745d52200041c42180c102c06110036445001d80c840d00c10300046203801c00c1d19504031300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 844779316 1250 844778066 844778069
    0x6010803040515070c0f031b051003150306150314011a10020a080f0d0c020d090b070204060b0408010219050903101a180610031109010305270304030308090115 70
    0x30307054560380e0401c148034210844030703250342150164100ca1b45a00b15070030060418441a2003210291403901402c00c080c01c003007000c071040108007900640780c100c002d4020785022040746100d0000c0d51000004600b23036000781690380c5440d074810500e0604514084001c400880b454500c103030302d00082410041c07601c04050120700e030201c400d980b2071801e103002245044441840281070700030200d0402c50f00400e42e000392000452000003800324010f440b1007280d4422031415903000055100d181000038095410040860710f00191000ca0240d444454040f0150302c242e0116085a43c00140f2050009000070522281241c40c0351140c03400c007455001942d10004000751103800b0b66102000546050714a4101050304406829034080d030002e2503400b00c034000d0403070301103000e46068004440118440d120f0724900c40030303800c0101e00304159000114001c0074024046040d099105029140c00310005140d089144002d000441c0d0b01d03030071032500400a41d00070300000211380c100441e9444c030142d15042c000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 844780566 1250 844779316 844779319
    0x9140103020306130c020102250c0905091623010207140405130f0c031407030b010312021f05060a0509160c020103022a0609060c0f030702010906050703020306090108060108030405 79
    0x16280e48800000a0985040a441380540c3d45850807548107aa0190003a1800c003851909041002c0030346514202500c5a1110080c82168940000c1c0001d03c2d240e40100d80000000d4111110551861000003102005400c0078003140c81d00b15003010320704262003143c1c640c05420304c085d000c19460803261060303d60071003032003500c9642c403480001c1145220402c0c00346003c0e045105030f07501c01c18508000342444060b0001f07807a0f0701c000c0d99200b0610f0130006085c4c411254801c1c3c010841da86103417280e6804002c4020041d0850050640036400c01003a0014100035070100603000405013041c004103c0f510000707900480c0110701000800c040000304140d40080042c04e41800c680340c0001e480102d009200d034129080c1156070b000d456100b412074424296600c0e1000c0801c560140d10b0b2401c480d9134139241214605101c500400142e05070f02c0d1305402030343c0c01c58040e000200300010385c1ea880f2029208100d0b03c0e140000d5001c41045410700c0c101303200074018080107010304025410070361015101c2c0701ea401941e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 844781816 1250 844780566 844780571
    0x70e0901090f020712051803030a1202070f080703170604091106070204060b1611030c0303041a0f040e06010206150906012102030408070506090102090901050d231c09140103 76
    0x102180b610680440d2400d9a100300c1c226560b504d030300b1000c0c00f960040380304140c102244000b00700f41070a0000842d0a50b28940d01e5441a50361003980480181d0701c030f11401c4071001c128000780320004400102400d9040d01c2520381c035100748030403140181100e00040605108038280205a004164000341903100d180c401c2e42d4007070391130105002240c05800c082c1c0c01071954010010700d5018001440800c0aa004d22441ca69030803061140200b6070b03507907074503541581d05800c100004c001c20714441e04000b001d00b561098103400d0140035086501180c01c560300921480c1c10030010000150707410b00080b41e1101d14401c840040040b0040421040403005140c0390500c0940f0000c0c0e21001c5031500070003842082890250b6482c907003440c0240403a08400003c50b00c40c0b0500000c101c0039401802602c070403e0700500207241c968a0542007010458110a044c2c410f1012154030805158210fa6444401c41a000007801106c080f0035000207580d001e0242d049c20450103090500c100c0004664001d801842480c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 844783066 1250 844781816 844781831
    0xa020a060f0e03070303020d0e010c08090d0311030c0615091b1b011508070605030c03070c020111031809060402040303120f0e0d120f02070f061d0d05040806070e090109 74
    0x2d5a2582008a48a502d8404c01d2000410103500003a450f1400c01265610668001c0c441c0042d107461002e0080206210b105000c20200da0a01e4051034500f0b40c0249465081a900000310f1401e40d884000c900c0915000401000995a8200300c1010400010344860181e1b242804032103c640344000c0c0d507c0c2c504e01000901d285403800d45c404c80d40d0088100402000900c280c100c035545603800d98070a01c2000d014800001032554014804e030391040b0700300300d000340c40e43d0348216044a00f00c3c1c840c501281070002c1410340d90000b080c1040548101e52800109502d0300d05a0b4041055000300184154441c0d40100f006100003640f010100103001c030110004219413a9521455000c0e0612040d42d02d691f104920086071980e0303001c004040400390626041155080d1030382e1050680c89000c0000d080b81001c62824400551550b101c222400c49411414003041d106001050400c0224201c000000d0301c0890244840382d4140301003500700d40241000c007030031a890f802241e4544014840c0000444e0758154 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 844784172 1106 844783066 844783097
    0xf0801140c040f1a1b0307030305091f0504050c060310170a0f02191a0a0206060916180e010f030614010e060f031f0e0607020a020a06 59
    0x114003c4d06118802c40100b00380d05081046802c01c104041140c40da800d1183e84d04030380c1402071507036410345080050a035400a84044160342000f803032340b511030500d485052070700c900c100404102d50751030f414a00e0915210300d403401c0e0055400010040801848041d80d42075920300391510032200007100e20b40f83c0c0c540035040014407003500001d08030017500c5c16503c1000d0508a40c0f0300c40e50040e49942c00c8480040d8a004440000d40010440032592070301840a41d42c080c000b40c4000b8890700c0d000c01001000054081d040044c0702d0f0140300f03400c13100340400520014150042501e012544d5032a458440c4a007144400c1c2d42c071920300000f01c104070308006030090484151001c2c0d031400d42c895400f00491485881070303d9905102e0911508030700001d15019010707607264250005404c0d402c11105a090080040480c403c5412080303031407005a0711545807100740c075035518042881090142 = true := by decide +kernel

theorem cover : BRFrame.Cov 844604316 844784172 := by
  have h0 := BRFrame.cov_init 844604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 844604316 ≤ n) (h2 : n < 844784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
