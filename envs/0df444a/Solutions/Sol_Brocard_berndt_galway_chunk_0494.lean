-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0494
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:05:37.012768+00:00
-- url     : https://prove2.me/submissions/634897c6-f38c-4a83-95a4-c7d5828dc176

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 88669065 ≤ n < 88848921 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 88670315 1250 88669065 88669069
    0x180403270512100e0d1d030307020d03020307121d010e0d0b041a060102030f12060a0f0609030308060609010906140f07080309010f0b032d010f05010627030f0f0f080a1209020a05 78
    0x6d100d040c500201242d060902540005404010540c012009640001031481c10018007050100400a4900b840034000e001e0b08000c003419203080c060641084030b84a11981c00f95100340c203641040d504a8003070441881c185c0362641c2c0d41c0c101003140c400b20801c8240003510a600c00402c4800300040c4c4900c207420045c1042104919a60160a0685c01204090701040b01d80235102441c0051031103503140345d816032450030701805001d0050302c241d00a184c100090b508998110441000b00d03030007403522080c9140c450803d5101c078000c0e00f0241c00c1041002490740d051201c070303401071801580341c14020041c00e400007003540c003203c6074040e00c0c0c1d400d500301440c00d2030000360303050001110040c462809400d04004a0119017118100c401400685940c0c50040c030016500ca1021000148180e050302920050503d4149003146503220042001c000c903c0080200454501800d52050340420540d20400d42450101c21a800c41038040340082e42c5003146080d40c2e4104d00401c41c1ca1034018215404075800c000c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 88671565 1250 88670315 88670357
    0xf1c0203040c12030f080a0b040905031903061a07050708010c0c060b03060609150105071401060f0806040b010b030c09120709180807150b0909010506180403270512100e0d 75
    0x500f051f41d0b0f070340c000c0034100d600c0d80d00030381c0e252070b1044000c0d40d0750b22203074108205540d0f1041200e4003007603c2c004050110441c101c142035000da1000394031035112a500d1070031502d88810b5030001e00d080e50030309610300301c5541c0000307003411043d22468090003d19144d6061542d94030080b5200365120003041c002c900c442c4440146540143c8040c58070510340352083c1c03640c4180c02e10346030010007207030340d50380d030400048c00c03520100c20141c403507440074016500780354681c0346143c001809000c141081c0000811300c402c050000b110002e0201030900c03a501840b0500e040d44900310303072150036411030400c0c0034040030688019000f02c415a10014690401e05503845000c2d0554414202e491050764907190a1103da80e540e010364840c4580c140046183d190072024441c182c030003901000011500312080c800000c0c2c000c0d03000c000da10303029484150700603040400030440034159409240c1164807061022405003005c10b41c02c5910b80380302c40601902c1c03a1410541d41d51952000e0080c00110103078024258105014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 88672815 1250 88671565 88671571
    0x7080106050a1d15040f03051b0d2d0b0a140c040902070203070e0108071401050702010504050d02150408070501021207020a0e100e0a02040315091101050f1c0203040c12030f08 77
    0x2d404d01d0031a03c0b90192079002a8060780003c07404140c0c0d45002c1080100802c84524201206004a03130f1003140710010036154000400300410a1039818100c0003d580e800d42c00505003140f0b01c0248a91802e03070f05020b080b49900303072442e0b240f0609150150394180303403024809014203000e81420303160031b1400c04010002d4101c040100c1c0d00d80180c0d94005400d00c1d28050403400b81c15000d003c0c1c0300d8549082c040722070051503035081505200050003200c1c0035030b8001003a1000c80c3c1c0103940c8408941403500c00141080c0c0300511682e0640c05c0418041441200091510291802a001c544024505d0315000030540609107009620190a0740c040c00741501c0f030f8501641004010b20341c030040355100d004618841204aa030386403656400b0a0400c10f02044003e11403070075081550030016440c80d6243e000500c01003280e024140030000074103880d0080a101221812480e41c21504804480400004040d620950b42540ca0401c04031000c900781c1460076031403030442c0d0305895200703c1007020501074504507002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 88674065 1250 88672815 88672819
    0x203120c070b0408010e060a0903080f09010f1b1106010b1e07060c030209010921030e0f0303070c0303090b030c040504050a060b031e0a0608190809031507080106050a1d 74
    0x80042d4601c0d6200107040605103401c000316030209990740b254036007100100100602d50824240901003070700115030903000140c682c0ca0a140da510000350502502d0440e02c00e000092402c4226a01c640c0c00c3c42040c10002c0c525500c05001030a82030007075075a01d10a00424510721000c00c82c10004100d00e40743c1030030007014500c030b4900f80046610f4071030071500c54a1210006c82d40001d10b51a81e90b03071064850002e004c031550031100202000c0030314414000d00e00801428861441001045a80d1740321043c038031482e00808881d9200c0d6685007038503001e901c40c8000c80c0400c04c40440825500e011809603446081c181d0320582c1802d10300740c00c00c4003418016004110640d40d810012840c2100304005604c0b49108040249245106000000066900906c9035044902c2c2020502c0040703004180582c020b000c1d0305880e41d034080c00782405080303413003003c03084c90741403182170f07084000e401d580030b061803140d009503c5450392a0b036290004e0740c091089140d583d0000b41d940b24145095460112054020310340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 88675315 1250 88674065 88674073
    0x40c030203030a0504090b04090503120a0b12030405090702340b0d020c0d2109020a05031c02010b030a0215030a1517010b060408030304020603090c181f030203120c 72
    0x150340c000c82e007164442ca280c200000c0d80002c0038004000d00d806a112904825507003000314200a40b5043c5c0c481c00f489181d80801d081c2c9a010030365296064000101c2018000e1545003002c9210200603075a5100e441349a00843d05800060541800441d0500c001140d81c2e43c002d01701705880307440fa0f500ea1140c8005c0751403141407030b0340441d019104001601c0c06c602c04080c0142d565041507050341c601613070640d8030000c01c039100090700450b90107451541d2840b4044000410147e02c14030000300c0c0c0c5003a980055402d4820003000c840700c508006d410708038211154000304441c072a100f00381078460002d850045c0d00071504482c0e010301d40040c1c100950740002080780c00903c44100b5010b51611307083d1540850040f900e0305603000d00e00d460a10558042110495400340b4061a015805072240402000a40706410110018182c0142480040b44510300101071411032110300341912003104055804101c100206c511721072160034581c01d03c0d41520340040050084801700c040d0614103500a454485080c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 88676565 1250 88675315 88675319
    0x50d08070302120307080708060a060906050f0f0a0305060108010b03040b06010f1b03031d07030b0a020c03040e0103080301090b030d021203060a09090506040212030f0a0509010306031a040c0609030201050f03040c 93
    0xb0110f0702843c02020540e99441c01420003200c0240002c00241070395200b044c10303440401016800c0844941162164103015071103520002c1a02400e003d000034000d6511030000f112040c140e0705a1103a44908002d0f05d601041e641c030303410608110700003224014645a40000403d40f50f42c068294040101d00c00d00c1d0848a0310003071140c6910914804000318046521081124901040403212482685003c4000c3c500c0502e191103400ca540c4001c1e018071007c81c0d0000d02c400381c500050007114081d09007600305030520f59492074510310990017440789500d4a4030f0001407200918000c41c006d200034071258010104002440c0304626290320207000d0f030358402c9043c180014609042d020b071000c03030f03401000a82101c0c50240180011850900c10116440c3c10800034080024076101c1951240003252422545482c444c600680c02010260030140000710f410b003c61905901d02e000451007288100c110550300c90391a01c00b5110f48015004c02408904140102d8121030000030282d130b070040c00b0f200c1c2e40c0101c82d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 88677815 1250 88676565 88676593
    0xb0d0204090606091109012f06011e091b08180d020109021302040f0e0403030f0e0f0706050c1207050a2108010e040b04020103050405120315130501050d08070302 71
    0x1d503600c501202d81d00c1c2c55403810000d9032602c1c8202d00d07030000745110461030302d40100d00090200e241028940c2c0010004442000b410510480c0414204c2841e82107902558480c00b012012a25030040710130946d141207804070302d10f0413a001e000c001c101a42ca00844526001000f6640700c24000c00001c0c010007039604407014a07100300302c2080105044d800009010000d40184000031840c4664a060a4010001044101710880b002d03800c441d420300f540f003041c1e111850201e0150210415526a040c00c010b004c010318840418010900300e8020304030b9420030365880301a20140a003852080b00d07034000ca00c50070070002d10794004000c1c4c0c0d440344050f1021240d040d92640304045c901406110000400219013124a802c21340d03190160021600c040c40c0e51070b181d40d460f850703003100030b200a04140d250340208003003003c100a49412080010302a5480303140c941041c0560807030148549110f101003d22002c0c01046901c10281698405040100c0e8084141c46004040d0721004c0e044046100740c4002d91050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 88679065 1250 88677815 88677821
    0x110102160906061701050303040501080405010905060a0e0c0a080606010c0804050306070504050909060919050a0b1504060e010b070210050706110712050306030c10110717010e07030809040b0d0204 86
    0x181035007180019101c1d0801100a181380a0704140c081506820390043c8010b64001094a00b201c000340b83c00c208a9885282c4180542810480201303284200000e100303910146412203081c110120302103401d00300596040001490302449015415001040810501d501c11318940c61554002c3e0000e502e456542d60200386054021a044000a8000308090010f0300d484135140d60028905001040d203401d1031a070302c685407040c9040d50200f0702c0b41614000c04204007031101e42c1d24180c01800c0d6144500c1d100381e01d054074540d0780541c43c1c40780745005c4005c20985484040f00b4166441d0001e180d040004680c280b214030b410710714401c000d0002c1402220300142480c0180b004002418214075120003c91600070144001511a9014400d0a0003000166200010444240c1004454401c052110303d00306440400c8150440740190042c8903011403804103645006c490102100001c129104051045946859031760100910301102003114881070f141c26042858141c074000d05104000c02194001030071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 88680315 1250 88679065 88679069
    0x1c050a11060304380f01090606050f0a0e040608010e0c040e0714060a021510050a0b1903110405040c03050f060411041a04090f0e100b010903140715020708010b0105090d11010216 78
    0x190b4117204010300060560703015070b48c020440d60600f242401c10f999602005801420014420055260480d02c40c96999070003501c001c01c00c3d28020845261680b81442d240d81c048201b480c0900e080100e07145840c540090020125040b544428060504107010416140c1c1300407038810441c03080310302d1941c60004041c0400d01919042c0c1d4206002442c01040c440c1090f10ba03482801003d0701070216607000d081d040c1c0d075a40651181c0c03500040c031800e0525036016900132034000a4029191a480ba6101505036210a0103000410301c4203816a81d030508210a0719208560310a955406020801c803801c140030f4189228401042840d0910b0b446030810f10403118184034040c955070301c424a0021512051160410f4800c8a944c00d0040001c2031001174207078200361000503e0411001c40d41e41c20a08140f040f0405440e80442e031528250300070000942c1c030300c01402040c5041d403038840d410129600400c2100d0000c6400741c00441c0032151a1a80ca40c4415280085070560041040020307180c40e03460034105c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 88681565 1250 88680315 88680331
    0x70b0304150203070903030e0103050c0307030203070212031603050a06030309060c080d050c0301090f0e0c0f031c0e030708010b030a0204020a03090b07120b0603010f0909021c050a1106030438 84
    0x6017044c07940c20006d01c0e0305c0105541d94140352a081c24060032625100843e40d204119060240c0d4a40355007000b04e20f0201d03c0c800d0320740320000100c00e10043d080040c090f01e030b03281c9050790180a076850310500202155003600c4010045103042e603080043c140519283c4071281d010300030581c2010107440e060b000f5207908540580e230842c000801031210300c07000c5c410f09202c40b68600080224200080c205035403062000b001520882441a44604940d010000039940071020000d10903c21100c041c058100c4400023241c911901450304040303085c15051140d8105c00b500100202102c0c40e89400b400000e5100480900405413114090b4010401c6085450300804140d42e402d108000c02d849141d08807128250f24501c075450400040204030510200803003070715220700002800090701e1001603004041c3c3c030b1032042c07800d0000e040c4006104000c40e4401305035002d121100e000c103028004100d1940b0080b038008145043c0341ca10000c0750b24400841070342e080644d4101c0c600644030039880303411014048490075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 88682815 1250 88681565 88681577
    0x30b0109020406260105011101060801060b03070e0d0515040c0308072d03020c0925030e01060b09010518040f0e01091704050109091505060f0c011d070b030415020307 73
    0x24035a0229001c401d103c1092820520000c01d5130440c1443c0c101881118104084140c500450344800e6020600600580f0002c0090315941e601c1c00c211508200c5494020552024801d101d5060650f041c0304c4059125000e001c60344520131903080d031108040c000380c503102c130001400700000741031a005004a038090aa40710300d40e160000c0180b615008002111051488a0466800650006000d400c0307140211620403865803101c0500902580710300800c4c251800c941e220f0039040d50036600203401c04c41550020710095403030f00d885805a11070003c007140064010090344212107092221400140c000600c049100d00c1d01d444404180d40c54000c2000b41e9075074810700340c0c04101900c1a100c11052410000302c0c102464240042d1048805105031086a42c48001d4042c01010108900024010042c42992200c00080c403e00c1a03401581300b9040030343c40c0c40182282a000764496203013140c42280140700d06424004e00c0a001d4202400031940b0011001c41c3e1204e0500c0d0340061445101c20340c1c0c5034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 88684065 1250 88682815 88682819
    0x50a1701060e09180703020f040b030123100620010e010f0b040605030604020d02011d1302180904020604050415120f1a04032307020a0b0406030b120a0b040804030b01090204 76
    0x4012a03901401c01c4d0011030505000002d00c000100380c1c6412030740c04407103108021030a100898003038040e0508060f415441c020200c2d040c104003c03108a404031a401c00d60485541e005040d6003500c603140a5500400e944140c0f07040501c9448401584d90301a00001241d02010074541030709582d14011411151038880b121904c071418103100d17a2000380700440061042e82010b80104100341c581700c00190410242d40c26604c01541100400d81e85a04040c2c880c0c0700c402c1e800b0941e40000d42001004100000d811200c60400e0318102c0d004501880d002000389241600d0581040020300752800d8450100c924510001403428844098100c594020140400400e440746494070050390801c040c0e401d0240c040d010b100101c0d074082c41144c260581810b0161481000d0340b52501c440c081d00200030b500103990703400481c607260321801500440390709840c1070151280b6902080014141e0b568201c800f43d10075074007000420f210100c49074000e400f45081c1854a9220303190a010200c0917000154031640010b41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 88685315 1250 88684065 88684069
    0x10605030c09040213200a1706010f17070306091e060e010f0b07032106170a0503120601051b0d12060506030402040b060c07060207050a0602060702030406050a1701060e 74
    0xc0c2407490030112203444851510381e0025101240041d8141c2203542c1d40d00404c2803403c0603520030140941c5a5107025150f541c41580100b00d4051146202d1042d20341601081d041d502505c05502100c0c904e0301c910018141c107900c989400300004100f6001c03d40c030760078001180016072203403034900084003000c014100d4040d04072a09030749995000b060b8000d203c000410500f290502c041c001e80304101c42c801e948a440381011618400c117484c4000206079400c00f051541c8995501a40c12659502036002c001c440b03882000d51114203c4101405a4100300802c0001c3d03a8507080103a44500141007450800561002d885501d061000040700c6a17130021320443d03901030304584800480030b000802071200e581040d0201d503144c00080c10090040351a1111515140d850a050300e104604420841d404aa510b240003545e820203845124002c1d803800c40f01040c00d6101003101ca01c1b9030002e400031071a0901d8000d048405a000c845400e04010200007030424034030700e03484900e0080443c0e42d10240d40c25582c1e41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 88686565 1250 88685315 88685323
    0x6010302180702030f0702041b0302031501021c050d09050303010303050c15070e0906040f0e0109060516080103031d0a0f0e0915010b130819031128140d0201060503 72
    0x4004007011100c40d00300720712280e0001c1210305400d44d003d0320342e407141003070710208001e0908045824a80416003c03801911303a8035601551091801c08000141c12104500582e04c0304416000741e0b4001400040c00c01d1118001c5006096001003c1c0c000901a0101d0b00e9440c1150000c0e04210000390b80041d0500d00c020b42040110741c140c4294680c098030f4105000042d02d0741e100d91001e00d000f0909140011005e42d1107901a8449114065092080d003884444c41402054982003c942c2c45180602255200048802c0c038141064152514803845e400c41d18140d45408811a50344080c0d10042c6030400e858030380004202c010f190b0903520341c1d0014144092201b0108008020011692050f60700c68001c1440500c014111240402542e0766080c1d00034818040d1041508032510612030710f1300c3c0c103010314841104486058060307610418101c2c104484a92a030b02e0603582d01d9800780055130140030115411480822841c404c1d882581c0c118840002e5a0414104408900250f552040100310f1401d040c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 88687815 1250 88686565 88686589
    0x50f0102071208090705010f030e190303150909080904020f0f1204030f0806030d18261218040b0f09070c031b033f0b1504080a12020304090e06010302 66
    0x40c05442046e08000008200b00c40d046804c0c410540ca840401151249c203012520b40c0c02102c41103082c0350040781c10080c1c090607200d4048403200030f00351000944000c1034854005015400080315281080010800000c0d4020031106801d1007402c2240107508a4800001d11845206092200e40d61400381800307044020201100024000750341c0400c64965000701d041c0803040030900f000041c034140141d644420805035000007120400020040003612542034620080b07402c614222040d501c0802c0c40602039002c0c41038210b00c1c070300000c50300306882d01e029001100048800313400d84604440800016034840001e0700c00340c0114601d844480f0905601c015490005440d0758003a501429070707542d009044c04c050100400348003100320001408540e094040703910700100000f0070420088840c2000d4000c01c1c020032014440c1d02c0c040d00c0101c03911034074800d030b800301c1c0e2803800600305050341d68a62110503405400b95401310700003003001040d42103091141000c4110980c000304099815841440302c2001a2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 88689065 1250 88687815 88687831
    0x1051926010f18020904030e0607080408012d05040302160b0307030c03180b100909080a08100506030103060911041d01050f040209221211011422050f0102071208 71
    0x400d40c84012007103c2455020f03429810303680313000b1603075503070404450160340101c070a80e0000e03000403511306010001000d402a525048020060948611008032840208580010181245292403004030b161a07201c80da125000740165041106020301c0c07840001000d0300284a10103001c014083c5960745845141d020726854101004503244506460901d1002d00200901c80c2603100d0001e80300034080b01c0030030014880c086050007100881c1c58144456002500001d0000301c200780014011401500e500d070490b03001421651469007186c41e0b50019045c035001c10b0b54825030500e158011074440b403164100c07844034006034030a44c01058170080e080d114080c1190307101e5251340c01440050b80c7c070024016008040070051089032444484001f8010130341c1c4c18058802000d03655090001750301f0040950b194a060002009004202e64180740b1418003038588035080c10004504120640700c5001c020000c41c040e5084a01070240e40807102c3c03d903030040c5002c0b110040c80c400301c2150250049801504a026 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 88690315 1250 88689065 88689071
    0xd0c02010c0503150a0305010e030903060c09101202090a03050d12020c03032a0d1b0810090203090c06071b0b21061807020c1306060801051926010f 65
    0x101e10000b00240006008403116a44185105030940c0d10190400c00865210f4000d00c030580303003400c1c21a129048159500d0281c000d071130004040c80f210b42c040310000c0000074440c0729686101c09003110318441300c140703168525a0800400e851a41e4044c058001540300304000c007043c200c2d80070014444208000d050280d5401801400e514002c0403040e40e621050b4481e044180b03443c0395600d00f0441c144a10002c0c0070001c000703003031800146181c04c019801d054000c521030710f050240c0404c541c0000d04a6000411400408080c011041550011741c1c1050500041b1907604031a07800081d02580084001c0b100f218810349500e03e0307411129800e900500c00c1e8401e05092241a080a110183d24400b170422210001000600c9a603a01c218608108090501403c80c5207040b900113951800c40800c000e11170213011f030b82c0d001c158020380901016120300e5640c814650346441c0a00580e5500310110a410b604040e501081001070540c40820200128480034018801390b80349a085076520b0b18541c0c1d40c141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 88691565 1250 88690315 88690331
    0x210d050f0904050402030102120108010c080105010e01051206030f0706020f010b010c020109140d080708120906012601021918050d1205030a0906050702010902090124050c010b0d06020d0c0201 84
    0x41140180c505030700c0c040c1c8010580742d4a070310000c5e009120340a8180c20310388101c800411800c1055202c568510015100c8005030b03601c6400541c0c1c189101d100b101d001600801c04003860351428011290010405803c1b2000011602d140e541001e00507000040180d2054488039a0300e442401961099502804c0a1201204030340008000f04040c0c0142c0700d0510020607024015202c1041c010032942d003165a2589032482c504d04125a80e0210b02c00700858001400440e82c28140071408038100c88442850b044408801d483d5004040b9500e0300d040981d540c20f03c14492100c5100346403d4441010781d849289000000b1013420010035250800c0703014107440088000003650020146007180f4803810016120f50b241d0100780040d04484000915060403c1c040c006444c3c0c054000c2d00da01c601c21100b120660b030300d40d041079030210100722074004090440705001c45041e00940040230100711160000c1038100c0d866010a840d40c5d0460004c95000b40d00007290880c4a203144543e00e44941e03644000d0044103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 88692815 1250 88691565 88691587
    0x30b0325150c140f030a0e01120e07150507020904030f02070b0304080901112b090b0702090f060607050601120b01080606030c130905060c0c06070f050a03050a0605210d05 75
    0x2e01100005182c600600701c480766840d41040031440000c0307000d04417035640c2c0503240006c00c68104c0d0040540401c6000d00d504028103a81d00440030220301840c002d1404074600400d401d6023050044e4600c044c042c0030800c11003d6114404e07858440d90003034403028050110f107d0001c0c07808401341d00a4070352540510501000420341c0080b500500024070380010854940da00c0541420041c10712980c0281150700c01800c8203881214101280d8445d4882240c000d03954140301245118107070009501400b4400020301c5800e80d050300c030b500800c02070104d904180c019506c0b545800c20a8024584800c3c81000d05001c00c00e0f050b508074007416254025100508205010035594842c501096105001204403140050704960108040541040c211038050810807503421956010442042d10741c080c40b00080c5045015040700e6940254507907505143c070840d200d08800030200030f81407902442c0c0b03c1d00700168917a909081070242c00c3c10b0400c054040340542c0700306450140c0701d078010350601c0360500c0000c1c1c00c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 88694065 1250 88692815 88692827
    0xd0914062a1905160303050114190509040812010305070806130b0f0901022511040b06030a23070e01090515041a0408031606060605030417070201030b032515 69
    0x1c000160300050b4010210b10984043c000c00960040300b400140c507440c04e045d819000070b412240400d5050a03420084020700c4007625040d4111500c241d0040c008114a09000d01002c1e4058080e01c0c9280c02d010442c83c1c1a10a400c080e130050ba035650049030103000400040c801d113a00010600c129001e80b4101c1d560725090818000d2505141c2074041c000180710144c02c1d01100e140d007011141d0103a00d05030b80c0c503101c0304080806e1802c1d1849200250b80c0c0c411400d040c4a8512180c20040c0441c0c1160344904040c8080d18030007190703c05e99500781506400c440400380c2ca05024107140c3d100c4126101ea41000146043c0b040c0c0d03c1036100721560101d1020050301c1030f0444060300c1c12070345641c00048a103158494580319076401100d05100000d009502c0002003445d03103010034070645041c85019641c1e0401c035141d00007138070081c0065001030040340d01942c2c40c80061156500c181000306601241d00300081c1085040e1550b4010f040d002c44d1299841d0100c03e02d280081d2855004401c000ca04d401402020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 88695315 1250 88694065 88694077
    0x19090e1303080421030e060912041206020c01110a0305090c090a090503090907020609120f042102040507030608010b1f11190c0e060d050c060d0914062a 67
    0x24041c0d20780126043c400d0140d10300d02904d4040018044021130a64020018032900c0e148a0950080c1d1000c51074812012560007030752210182c0b0345052a003400c12014103201c03401012a00e044d420081d20b0801c3c0020300421810130b10340c40d51282c555001d02405402d448005040b28042d170420100301c0c802c1c0e40c5262501c0c1d08190780160000310f4035003d03d070484c030303602c210980c041d404080f074001c0241142d40003845920401100c001d0382c01d4034070003104081c40c03400b0301410030000300b6092105103c01a036521900d54014504414180d8042d80d90300071504440041d2030f600002912851705005280c000d0040003100c2c94141c45509650b24401c118030100510782c58440100403400070175002041040014462403584554040d103000c0184c07611540c011040c2c07143ca00000d910000041071441d0400603400b8550b040f07009040c0041c2d8200403c07103146e00c421280d07102280d80342840340229818603801c000e4103034041d00401890402c0700f8840302d0301c03038a60401850b0600014619500e04006019601 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 88696565 1250 88695315 88695317
    0x40c080f070c02130c02011b020d050d06180c0f020f07030206070809060d0f0f060302060a030903020f0106140a090606121505040504060203100e06060a050c100219090e1303 76
    0x6078035495070444000300c50b03000295110349052043c0f500c00b141e0364014904415180c0003041966000e800302800205202030322005a0403c00004030400d00032001010100300314000010055168205208078644103880082c19955415507025040c0d004400c2d43d403444504c0c0002c2071800311f9050b10aa9460140c00000e020703100c003064100c100002001074a403e054001c10268403214248082d000810311107884aa0450400400c000c01c04164401c0e075060f42e130041c0c02d4502d00198103000f603000c1c2148000480c00c40c0301d1001603c1107100c00384141c0d4050301000c0c2c50b10000b400c00c01c041000869894000782c0a1515250041000b00c0d0400d1412450302e1503000b0104524200819a03d20484141e020b90b400905003410801048566802544541c0d844134200540c039890307014010700104201c90441e0410820052006040d014101071700042c1c1c4001e00300c9500034070030070000c0140d0b00040c0c20302e002c0c0340181d5030503030700141c00001c00005090b040040f1713402864200305081c290422094090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 88697815 1250 88696565 88696591
    0x6010206060a150c1a09030703090e010302010507080a0207080106060203070203010f02040608060d030c0203010c031415090a09170c15160207051302130806061318060c11150f06040c08 81
    0x110800100c1414401702c0441c0e81c0301001c40345044201d180d1130703038402481100017907505800465110280100c5c81d0681c1d8040c1c1d00e1904007209565040081c0d03001c0621078003980304401c000a003a010074007800d400303000260b0103992540ca1712310605007034a05450078034181c1c500611050019640c07200007950b12950456003158160564241901d40744100d080107501135081c11014428a50950000200c0c0c80c50300070800000e0707607541802034490b9060000203a20040740000302c6c90917159a0482c01d0b8450240034010744891042484d500d07158000311180c20740b40c00001120b001d110704124005c0d40041d094600c058114240302c0002e46403002c601031684603035001801a640c441aa9040e9101d101014458070103650f05c0741c07041a0703266011228180700b01800600840300c0c500e10300504890000b10b8041085000e2155180700140c20801e40600410844d800c0d50840b4004c00c006507603030480e05181d0070340203003440050b685030010700900c3d2900542c2000e00a403104c551003035200b40e01210700d014107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 88699065 1250 88697815 88697837
    0x114032208070506010b03041202030712030509010b06070f0203070509040b040210090b0d3c0c020307150b151912020c0d05180406030203030403060506030115080606010206060a15 79
    0x34204038041c1c0c2c60090484e20913400081399052420340114043c2e030091000402e04120614104d940c5e101e03180e8000c044144030a03040040c0c0d13000390002c580090700342c03001046e41d08000c408034102d508003100070307501042c0780590441903040901403400900000c0c2e84101651619845e124150500030f80028080e000c09880714581500c034810a5014180c90300138580d60f49084224a0003800f42501c040d02e00307048021510300d000750020030502c94016045018000411030b00954070003490025140000d40c0400c001e420b0000f018409950f1000c2c00b40342c8001800c400080034081400340c03000d003640000804202ca05d003521000748146400c0241c618000c180101402084406805a141c40c0485032003503408540d0403640000140a03035100c400008150b0b20b091030200710982d0494800039425030410841030001c29015000301c3c1e0b1006000c1c2c00420000c5c020500c2c21145c0c81168025035003500107105010441d0303810b0046a401050071a80c582941d0b090100f00e1000c3d51104590505200d409945 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 88700315 1250 88699065 88699073
    0x5090304030f1a090a0b01151b08091017090304030f02100306030b090a03081b040b0a09180506010e010206040206041710060609050a150e040207060f061401140322 72
    0x580710f80c40c481104200c1504001c144c95544108226080302c060095a00100b0135546120b280d201c680c4003680d44810300010300140e89142c081854003502e08d81c8007080f0003040e503116140000981c0d440307035071920003684982c1300b4a1a40394001d040c807803064000f0081040441d101a108680c8190101c43e110800ca01c1414103a00401803507100a24200284080005101001c11079610090003a114020140c2c1d513080c000802e0304443c2c032541d1070840305102c144804c05020020f4400b009042c20700c40101512038110f141100340400303131a140141c07140208a441c1d40c0c046400d0740c15401c2030000f07080500f03103907000403007034050b03801840c44909074005000350034603041061403207420740e6081c200034180e22000001c00c1645107000b65806400341c80c00c006400411081964410402a990340c10656001d03020040a903010b400e069034025100d42c000d8080410030b1203154000c10005003000c0b038820114002400501c40f032014041c0b14a0180200004041002c2c0b005001400d5491400203019061074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 88701565 1250 88700315 88700333
    0x6020a0c030809060d0c0201050907060206060901030305030702100f020403030914090a0c03091403030405010c080c03220203010c0e040c17010302280f291218030f03060f030105090304030f 83
    0xf100711000c030b007040e4421401c6c075010740c4294080e040c40703416102610740703410050b665580261403603034004942c840100042881000555009202441901c8a00c170444c2011000d54107508143c00c10150300103810401c0540141c0c1c0f0000402c8049d841ca51003a0700e03030000a4200b4001048002031589903451002d0251181d44a207414562001b40900100075500010380d1704d4004513401c513055868085034803000c50161074281c0c40740400200740c03403856075401c640c2c403400303801c00035800c0e40218507030031000c01607500380a00c100040c0e6607501ca0080c03143e44410082514070201c0c03110309100c100440715170781c042c2020007541501e0b01510205c07940401e01050541c4008440c90202e01d5a26150021408924100781c0c68201d8094980d4100c06803100c1001540f01700185402c003007000001c1226008000850400d150b0001c55121412980140001c000e42141e00068447c0d2445600000700006458441d4010400a400364000c01491400c202c501d0781c0c030b202d1030002a1030070080041903000c1101d1030f1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 88702815 1250 88701565 88701577
    0x40510080d03110c120904150321030b060a0c1b080d1d12060f06010206160c150e010e060a0e03040b030a0e031206010f0c0308070e240a0906020a0c03080906 69
    0x9400c40e103605440c0003845c401c035003000003070380c0c42039091101d9200c000075140c1001c000e0701d400c03020b0b801030a011074940000300a0001c40c21814161100c0043c20a030b0b5405d0003908403984292070b07054a0084510301101b141c41c0d107420500c09001500000e21404000040300110846079090101001e49030039040d50034169002c42c0755500c0b548088844c2c1d10a0b40214801e4000c0c035818031a050542c039554016603c9080803a5540c031200b01901003010785500c04e00e2040072160145a041e007240e071a580d03c03101a10304042c584a00c2d6919a1450350501c1c2041002c1684040044003c00200308141341032a124400c0e8072400b1b00082002c0301007090384529900555000d61008200e960340c1c00c000601c0384c480c0004440702400b00350011096035440b0b0285039000d0b80e40b81c1c182c0d90002c50390742da03040a4943c104410341d1581c00c1010007803251000740303240d012000400c4504a2840d242e6400c40401004624550084007c640041d940d0300700041c480c3c440c101c1965444201261903001c0c10f40410f816000d80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 88704065 1250 88702815 88702837
    0x110c01020c010b0102060a0b0d02060714010f020405100c050d0809071203030b0108010603140103021002010f0905010b0306060105040b03010b090f0405102d0e04030c020a030b06040510080d0311 85
    0x140365464041c15809400d151900307800faa0303c80d81d0744a0161040b13540c185c0071650040c840b2000030006113070000041503544d104851031100c1503100c481f801e0840e0001960901c00039070020f802c0c01700385405210b442035041d00b85002d205c1c1e01495a1156100c44c26401c680d024840e10002040075540309101c01c102800e001c0341e080c0c1183c2200d040c01000382030b03e20307601c6002c2060300e0004200e10b442409801e0003001021704801c0039900e1582800180d210b8145036100315562800b0109001c2c032075010300032000c0c0c000c40001c90340d441d800c4101820481701900c0203041c13180400c001c02104103204103690441d0b0100d4090354070303129010081403d40074040086940140ba090401c0b840410050310310040e100a900c013058002d00500d0034441d05c02008514000042c43d000e810070094816a03102c0754070a00c00d180102006406a010130103403803082d002102c41c2c24188c400c00009007090701c0b41c1503018628041401071030b0310380000c55442e1003080030903008054882c14441c00055a050032102c610041c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 88705315 1250 88704065 88704067
    0x4060905030a030606031a010c021315030b0103050606010c02010207030b091608031e180603060d060207080c010b03070303270806180c0303040305030f180d03050306031c0909110c0102 81
    0x20782c00e0090082460b4018000424500042d03d030350843c0010b047c1c0791460043e101c600d400103007602040032007815203031800e1234076450b00e0001904110b2841104011841040c85d4122941940303000e5080220003003000e070411101420000141c0c1c1e002900c0e00031680c01ca0441c01003070b00c815004904080c4240f0001a4030905079000251001c4008001d0403014282c0300c000c448040c903900c1d1203220348902c01610741c4840c010100203465140400c0119001140244560444c0c03205a0b26102039820406098680c0701c400b08521604280070b0003800d000000440103040f00505558011300001c201030400061030300000381c2c203214035008034188000b030442d0008482c10792a0540700280003150000545000e80136011100c070060800001361415661701c03101447c1468420940d42206401005c40c1c24202655102d10758919180c1c440100603046c06039a400380d80c4e14140c014549055862040d50f4445003c04042900a40e8881602e00594030054804141c440714503285011354020007180e81c41da944 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 88706565 1250 88705315 88705327
    0xa0b012304140403020609060402031c091a040e0f090607050703030e0f010e0c22050606040909051b1206010509090c0a330206011404090503070f0c051203120406090503 74
    0x2c0a00001885940303c0d5013114420394400c1a000e0b1105410744000f03406501102a9005072820300303915180a0005143c4042d6055039240d6000c40c0c03001c601038149005900180502000c401712036801c5d4040c06540c00391540e402d000d040f103541c8550082c200005c004000c684002054402c0d08800d100d1400403049031042c50b003181c196402000384050381c0249101c1c2408031a4603041c441440b0003d188803400d2945900c02c80008103001d0500100b0650703000310b0821021404242c00e20400c2e0246010350b00800d0301840c041c14000d041c5007481a02c5114080207171002002c107500040d0310341959000d80e00001a03446004810340b41c84503000c60302c0e5104420f540040b03207821440303494141076a2070818941da00e45102048081c0207c01e85c4c500c00050300700c500180850600c44041d42502c0318080c02c0010b851110751125811a000080211780a6402d102e8010a11249554402c0074000860780b1102e50103400381c0266aa00c13400038414001001100004c09009944c4c0c4008401c0e03400c08107983c2d81c0d407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 88707815 1250 88706565 88706591
    0xc02060d140108010b01020d1e170424060509130c05040c030b2b0b1b0a2001050c0702010e24070327050613150203040602010e0a0b012304 61
    0x26024080c0b0f801d5980b03020b125040e19071000600c2d0320041080e40752000a20141132480111a060885000c24090000840d0381c0306510080b03050b22a03805050300b990121001c20f03000c4404407100e01004c2c0f4440c144103050105a5414404940110610013561040449403502224186003503118a610620f061247d424180d05170700058500d40044480301000308402d00c1c080481c1d800090320811520010b401d000004440e18021500002c044035400c50307032100350700f807081c103a4040ea003a08000b8001200580f1806003042890f041c1041980c020300003031a100c0700c1c124860042110113410000f070300120850342d849444542420b800c1e01d005a8880444440034000d45610510046000628513aa400b61701a41c011f14000003d10000c0c04400d44c6181c5010030940c0d4011550741e001d071a8200000142c0c0c0c040c9014001d0503510603030007860300c0303602e810300180c2180c0d802da400100300d4101c03c0c0e6110002e8550021941074841a00e2843c5484400b07181c3d441d5400700d0442001d810500d0412026060 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 88709065 1250 88707815 88707851
    0x6140a2f0105011a04050909010f06170f01091203020f0f03010303030c080c070b040b060102190c06031a0f010f090f060302090f06070b0708150a030b0a0c0f0207060c02060d 76
    0x90340310800a205030b903a11503502c048a403055a88400c540400d00041c44903240ca01403864014040100108a85100c40248000c4445a070310090034401204002c40070a41c040c070441c466000800c0003006192003a40754104c001000e2001582050b5000030300c100e0400d0483c1c1552600410080c40a80f82d68607890082d0081040710f080002140c1100009059405580e0490303c2d11035200d0080b1a0503280c0c1d988150105102804a0341035008890502c40c500508041c4100c0282c00340c840100362030301c0d04038003030300f11105100c2c0b22440707982d4115128050348403005042107581003032030608150890f000045076903001581180c801c01d030035030f2000201e040d815009059585400c8072464605030014082204030b11568000601030902c900c00074241c1d90251403d150b002072240301002e090101b120000d5200e0480d034000b202c0154100081c020302c12424410f0969068081c10100c82034001040065034908580c454241004642c0c0010f4045480713690694210701590102800415402c0c0181001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 88710315 1250 88709065 88709147
    0x140304050105060f0d0c050112060b0703020c1318140a080c0607030f0501030201020a030c111005130f0e04060c0909090503070201110601050a05120712050304080105010e0106140a 79
    0x4900010313a46440d55207052080c1c0e0025590110103201000d2500c00199441c1c1c1441c00040c40e20350f0780d8800000c40d00c2c81c0c0401031440d20700c42e50103406100c0e4502c04001e0810300c074100c0c0e070348070f1454480500e101c968521380c2c256001e60401245031320445a08805880d02071800c070700401c07240f000f08074440341d0200081d40601529080e1824050483e050b0b00308012584d0034440a40141e000101260100b4018481c0300f070481e000b5840034815040c0d03003022582d00c80310158035000003940007402c0c441c200614001c480c058000b1441d0351344a035150281d0107a643c10050302c0500000d989038039400000d030040758907900520307000d40240080562400c00e1034590b00305900a0b4045199400c144025120104003141038402c0101000b8000381042c050000c01480c0464a09036031192020114070881060800601248540000c2d0f0352141845050303402c0d00d006a002045143c1c000005011098003da00c51540360f402c00001c60712041020000c44441c44943e507014100304000140174a1132001d0019041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 88711565 1250 88710315 88710319
    0x4061205060703091101180906140901050303090108012606180d03060f14030109020402030408040f09020901020a060e01090c0f1a07050706050a0909060b0306040608010504030206061014030405010506 88
    0xc1e5582d041c4107809032040300c54000c0500c01c038220b1070481903000d141c0d012407001c0007a6003400b0041d01c98110200f198a00d40002d04600080b9042000501c1c10300e41d1540504403c1d0055400c2025403000a046803a06000c3c030351100d002104007640c10100440c2d0110761070706441c06c072140341c01c00c1ca4201c4500d00d1500e01c3c01c00580102100d2554060080c090402224014030b083c01d2918a0000c3d00f0f00300f040071000403a415500e618800000d6a61400030314000e40c01091099990780c40c10b060490050110f50103032584600601400e00c3c1d030703038002c00c42804e102c1d088803003c00c1100c44050581c5c010002c040f0001d003c000c6800b4089a4124680d0112066900200052a009819508101d803901071040300800340d0b40204014400a40310780c0c094151003802d400c194440c0f5031102035410035510150000c0500d0240801045814036081c015070340180714400c02040203081c1600c0017520768400504142c00f0304034410000d080b8900c0b801020120f00a440d00154682c01c241c94541c2c064042070b00d4181c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 88712815 1250 88711565 88711573
    0x1b060c0e030f0601171203160e010c08040b031905130203010501050406080a080d02040f030602070203060708130f110d0f060e070e010e06060f0c0a02210d0507080904061205 76
    0x80a41800103440700c10000e90300040c01c091707203000d0413841030354680c0d01100c0d060700030a08031038030f100c1d2140b000d14020001c060114500740e0080314000e02c00c034a15006141007240300c0940c500420750003000c44003900d0b0300464580c0c0c0d9035510000a030304400d240b079060804500d4201040204c180d44080004000e20071002448141d81c0d540421040e54014001d0100c0d40c1c202c0f65403c00022103000c014a510f2202c13000c0541080e41d61641d185106600b03600541d9803580005541085180501040d035108035641800300399400c0910038a07046038440d110092400103910710603000e02060710503a0004101c01001089030f03e03460328082280f138003c100301f1115281040c034485003101c030219031481038480345c42ca800e42d00e81c07800d42811030440700942050341080c2e04102801c1814000802450440044d030000c01402d60248140241510044c9120b44203440f9840c00032404200403403002c9980042c0e24007a1707103590480c10100c03071901ca850002075016280c910000369004120b114101503a00a034203803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 88714065 1250 88712815 88712837
    0xe0103060b0a090b06090f0d050a030903050d08011410020c03010c09090615171302090f0114090c0d0207060f020c060108100b09060d0503070b04030203180d020303040302060a1b060c 80
    0x19064a54514130180d0242c424050b42d8a1803c0580980b180b6503401886400c20003500c2d00d4090604070107400c241d0001d08810814003d00004001500c80ba0402d45080c0090390324029000c96100f200340b0600d4440c0b007200080e203600074400c01902c2c012000003002081a0205071001070108940361003041d29030782c1807000010b05049160201200305c0135030340703c5900203906490f000b500604001c0c8007103400106400d0b00e03000358503404007040c0b080640c0c0321401c1655060100c03409640720030700c414500c00d000e52000c2000303c1c0d00c460155105500f48400140c2c854500303142078800303030500ca4400c04115102107003210307496000140b2141216040c405981a510f0300d62401420b40c1c81d48601d9980004500000c144103042000c00e0b550914010001c1d28146580703035035030703081e102410341c1d09030016400424991103801c168a951842d548003200c00c020074418a030b0100b038480c001d62102038469800424043c0351300d0b0061140100c1013034808051030300031030315141043c014440c43c8891300c005a05401d070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 88715315 1250 88714065 88714079
    0x31506020303070917101503050105070309060b0316170c090c040915030b010302060a0527030d171503031c140604050105090f0a0f06090501080f060c180a0e0103060b0a 74
    0x2117100140403e801410260b00e03403c4040001e8a000f1400702549014110000007142d020310806020380440d94010903004c09500380101901e02c0c284080c2c0c070a81010f4100381c4c40d150705110742000c6981c1300a24100070340300c1c00c04040c20310b4480360640760004540d408100703150599200034800e070380084100300400e8070840030b0101820011300000b014407503400c00500140ca440d00191100c919646091451701a258000520017281044883e8403409540d01d0752085141c18810650f81c480c003440c01511080800c2403241004501070051500f1040001ca04859510305008807620b0028000c1104c0c500c00c40d10b40450000d10114851990060f400d202190b2a85024003400e0b048a000624800580c0c0f00c81e411041d461501800549a82e9600c8bc6086448103240c00740340b00404d030403000003841350301d041882814000700c148501d005070440f404001403a86c1110503241d02c45d0304000406020003007000450a500a40c1c0c04c02c0341001d405200000400c5060b40003209607c00c2682c1d0a00143c1e03036485 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 88716565 1250 88715315 88715339
    0xc030b0901061203030e030403150b0f03010507050a030f0b0607030915020303060d0b100306050114010206091207380a1a0108070311070c0e0402010206160c02010c030315060203030709 81
    0x10840c0b0850360140f42e10100b4803942099010208110589203401d0341caa450024928844004403091510303003883d84040e00d410024992100003d60003440759160100700181288035416040c01850743d25045144441c0c260341c40742e03000c001d01501040e07480466080103000105203204204030304409041181b4810b201209032400b030301c800341900001e0b83c1c05a98491040400600e68030041e007400e00000041901801894002c180d290a2001e0343c02d402400207040230b10040c0045146e90207140901c1c1e030400c00c0d600711810140c20030340003600c8448400b4110003854000c040080c00040c26443c0b28094001c07030700d00704d0190103440010040c1404003910684611100c114040c0070401050020f02c925001e6085001162400040303d880c0007996551000e03c124140c00561840c142e080401045580400c28140c002511003031a00b0390b0b074500c600041403820001d5000341000300c4180c10360304040c004c0e000310b019a5000be00c0c0394a040c0d00e46074005d541c2d40044844800051040c40c0014119403522 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 88717815 1250 88716565 88716569
    0x21c020106050604030803190c0f020f030f041401050c0109030e040b010f021c020c03010e0c030705010801141302071a071b0b0109090c030510140f060108151c0c030b090106 76
    0x20b031100342411724640740c0c5185030b00000c18144141301039041551258a00f440b80b80000030140d140c40031000620600285030240d0074010f8107407a0300c100301308c100048000041e2012240e40740c4040814261110040f541406a2202c0e140c0300c1d800e19100c24101070300201c00720780032401034500704241d040c10001110110300b00e0100d8009a002242c00b00c2c448084170828001c900c1290044070a6000048003103403c60b01c07010708800141d0840301c0722012500e418000580100800d28046200394182002c0e074403a42100b0804a204003551114032102013040c1d01641e6505406c10003024448404460b078140094080712000d0000d00944200c0b25141c010f815003c1015801032800e2990380e00b4804220300600080c20169641ca459920000001c0c1c400c118142d0709400c0d98002007400f0640e403628000b51034000d0040540503406400308550360760f0242e500cda02901140c1400c00ca0302c01a0089900220980c5603488440304405e0034006002040e07100a044911034032880320b481d61400f50440c01c941c2c0714 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 88719065 1250 88717815 88717819
    0x60b13020a12050a0e0304030516060f0203160521070201080703020f04030b040206070605010b0a12060b090402030a060306020a050703021e0d11010e1605130501080d1101090503030403021c02010605 87
    0x300b00c0982e840e4030b1903409240d011004003000202c403e425142030f0f1558106502c1114968007150b15009001c107280b2414006142604240f404040862006500c4e070082c54212610907107421548002d110381000f0114600c0483d07000483c00e0a42e100444075964440c500a0b4041486030010030640c921a100b2120580b03030846086d410b1a0030f5544802480d480504166803044c014001e0001003051445003034000e002c4180035a5440034003001c00360108130000c51021009180c12410844002460110303003292008440042e030302c1e900d0708501b000500c0c4607003010b440701c0d102042003504030790000e009144e5203010340c08640f0000390740103a280d40746001210b1403240fa00403181000c5101c5c05080740408100010f80013003861408869007903d4110071a030300034503141321541c0c2003110b410412800d4419240c2803100340310b10340c14054410341c0e80c40458451010000030000214000b0b20039404070440f960700a00343d9681c0c0c101818025600e120064071401852400c611719a017450052042030121100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 88720315 1250 88719065 88719077
    0x605130b0a090c05131d03030405100209040f0e010209150301081903050708030a1401170705090a0204092c19030309062a0801080309030a08070809060304060b13020a 73
    0x74806021000e0b006400d012100e442030b00401103815034842032481600c05040f01c0014050480c2d840c03140180500c000c070090190000c1084c040420008250480e54150008016907910082d9020a000b00f40c07038100c00640500d0410710a401d11419002404d070340c03100b110110141c2c404114444481c5c4000e114900075544000709806241035403a03508080340d03010303041060a0021986903a107490b4001c4500c03544080c2e031a2403440b03072121000c0c03159000d800802c003402c0040b0891602c0c160313218141d0180c58801e0402800062194131181c0489000d4450075034240728650307452000f03460078441220f0400190505002c600c62210001501c401c0c90f01801490301001c1485271016001842c44041c15100940c4480c440412404461300c684a031445020308982001e00b940c0000b4510700040e08040b40d01e4004003e01c85c91603a001544111032a08101c01c0703540c48190345400001c03849001202900038102200308800c3c0000c43c1c1c09074000701000d681013030868aa66005008038402c4014000126030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 88721565 1250 88720315 88720321
    0xa02040506150409060f0e0c03040201110f010f0b03010f0903050f070f0602030c0703030b0402030603120c03190906030606080403140306040917180301060303081f050604060302070605130b 83
    0x90190000c98020201034481582203a002c070007500b09611642200d0200c2c3d0304c0d41001c018003061581607000401503061001442e0400e01000741032803002801c06410808005000031100301c0c20b005074919402c0100081040e01c044407212000350240d14030043c42940f8100e4600800d030428007400c40301c00d6055580f6072a0a2a004144015400c0703014103540740f50103d160340c000501e85100440c09920540d9281c2c1c0c96000e00e2030020190b94004030180d018074014024000c4c03503100000c14604824130390741c020b80c84481030500c81d440d501a80100c07400304c2c1e80c1c0607040030f25542c00c01121400e9500640c1c09002840d15000d0030b5030402c605503401000516450784040404002d100955044800100041454951900e80714070ba000b4112410345580350009415070f9024101c0480d44a00205400a00c00a8510b843c090b186001c010440080107800340c456032000002100404090700000703100d140c840e5140c407001002900709080c115592880c00010480b55440c0102c401c1c01540d009003054020b0b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 88722815 1250 88721565 88721569
    0x30f080a03090210090503061506090409080705031303020a0603140726070206151903080306030709060e0a06080c0f010e1302030406090b0f07020d0807110f01060e010609080a02 78
    0x1a0018161004041e40c4881d208010799416400104e40d480f50f94406001e142800b080506250001d001d2010b03401070f000b010340145d1134200c00c2d941c10b5034040b83d000802c02040d007020401d0b0300c95800000e156001c00a8011b070200300102c10175082d24000e4078000c02542d00c5150a46c00c07900c01c030320362007107030000c260001c1d0f0344034070801042c80c10411484140742c4040c41c0494003903442030213030fa0380070242c0c10001c02c100110314100310309051940201c544c03901c400306a28581c00c510b002c900000d00540710000010700b45403002c001c0c007001003103503500810241e030b80d500814000000a031680000181401c60014003000d000401506c0010010032000c04c20031140d005503000e403e6019265007000040f44000009801072000e984141d0083d035010a01060b94900b20808800040c105406021600d060003007081c1e0000b00001400c4040c14030104680b03a000c01500d03c0000d00d00707103181c2c5205019102004000641010b0126000300d001488141d80f1448103603400100c0c4e0113040281d40c0a00080800340c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 88724065 1250 88722815 88722817
    0xf0105040b0d02060c0106170d0504030b060d051204050405060103090209180f07091d030307091701060308030702240610050d180f2f0915040c0c03110601030f08 71
    0xa40d1000340b410802c103650750702282c1190400c10800e03a40f655a9042001440200c0c00300705038100e1768902030080ba44180b0000751581c001c038080035110100d0140004c86548403000d0501700c480d000421245090031412140d801c41d031280c010640a02d050a02069040d40070f40140c004c0f0300c1d40103000d1400340d5215203240c0c55044000790043c26912503a105280d1440040c0f01c0342010f030070340800218264400c41c100d2400074074080c4daa0341140d40100104500d05920610841c2904c030003115000c00c10400180c02400340c42103800140c070106002050142d0f481c1c00080030000010124100c5425a030824400d400000003107420a0700002045a442211031040c001041d22142c130340c00c00180110000e01c40d6001003400340b42241c021a4200702842403104050003030401404501010780d22003250a98017200c80f20700459240229030074404990445c1c02e0241d041c802c0070000d4010400c016102c0d100a00440b51983c0550118085000400200001080290503250464011034804030640d80710041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 88725315 1250 88724065 88724081
    0x3060e010909150227060c0c0d0501020705030301060807030e0604020105030c07051903050a020601080105060307050d080d050703020306040b0102120f0c07031403121302130c0e040504080d050105090f010504 91
    0x506001c2881c6030040f0440740c4050321211124240c19061018500a0b6401e0303040484c4456101e4034051180b104071403c0011201c6d0500016030316210800900e150150182c05840e200404600000c000851110307480b6603860f03c5540d29079400e0002c4465200199100c000c10703034000e8005042000000ca820820b0801050000e2040742104c4600c1c3c51040404500200800110700180002800c3c500343d580c10800c0038054411440208034078100a0000f81d40ca404520895000d031a101c82c80308240040141076610350000038030203102c2ca1402c4c1c4070042c020f5204a0b500e0307100c3d52600003100d25951000841c0c00550590012052a024140303e003d4460742082c00318803001c0c4251040400081c0c9003103058030410303124034020340c3c0343d8a00e0f0340c0940b078000000702104079420b11a4138500c0541d951812000110318440c1c000030702c11007480e4040b00c41c851040e0304140c1260400d0f05004c2000641c400a1250001440d802c0103140d07260010010088808c3e2074003d5401d0390540140f100345481c1d441190 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 88726565 1250 88725315 88725323
    0x21503070e06030109020703020f15070e04141008120a05090f0f06180a12030c120905030d0c0203060702030306060f0d14042001050c0703081b0f07080c0103060e010909 74
    0x4941d150200c002031503a4000d0304101c42190b00400d0000030190100002786140802c07601411a0300d5800032814283d070700042202c0108510b2101c00c82484e15281d01c8040c0700742d0341c090031072054944501c0d4100144418420121035114591504c43d2011045059a10681e0030355a80c3e450300307255a0030848914400b096096000c0708540c0f40000e1587d500c0010325255032b1942400136082282c10070440e004049900046111448681030800641e0048800b4000e83c1e20a8403508082018501120014920b0b00b0190701403185481040c500f03500050490b4005100701c0031a032007641c3c0c03500101d842e800140d6080380c010741b003844003c1c035031000303240a41401d0540400c0001c1c202c56050044030103c4090320255000710312040105645030481ca016034a00000303003000341c941410303d22013964920240c032000c0e00300400030580800b44d50400701104c0d1398801401c1200d070079003000d8034119240c4540c0e2244101602ca51990500036500a008003000c955042e204c5003010703880c01580c00003411509400700d07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 88727815 1250 88726565 88726577
    0x150702120304080d06080703170a050405040e010905120d1b20010e010203070507050c0307180216050f1c03050105011b030512100609140f0d0c080a110a06050702150307 74
    0x81d08800030717103d140700400b070681c014a406451810000d445880310703600c1c0c060010013004944e4443e84c118045030111881a200010b600107411525801032600c0c8000412500034104e18264041011014143c00725a12004100c440050144002400e40c103070350322000b08812a80008100b422007404108000004002154000740700f181c3c14220390049442d800822004512041400010403c80c01c80101c107900510381c0500700303046042482034500318030b0a40b9030001a41002551541c1c070400105070300208445050001d80c0540340c445a0080080082008003880c48001c1842409807504030351040e11918400c0c861003540400c0019600d80640078040100040c1781360400001c94a4856040080d203030410340d003040d2006210424560000600c4292409801003a545181d010683c1010449801c244403400c0d00e060000211154400c00d03036409102c9811051052660900510610458070700d00f100340c07a40001d0b100c80c040c40501a410008020796030100101a10055400c19060305100c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 88729065 1250 88727815 88727827
    0x3090a05031603110d200102070c091406270a060806041103010507050403081204030207030206030702010c020c062b0605190305010606050c1f0209090106080915070212030408 77
    0xd440d42e48011404544030401e007002030245a40b000380c900c902680031003d0103004c0b080c1000105021025000e480c12904050001c14504009504650754540d00c0141c0e00d0105a54058860040030b0300d6101c1102c1d80c26800001d0701c9440c01c00b440f00b03c0d1601144400c0000c4503030b01c1c1420195540101090800c540d03902001c145290104202480b95201d5942d04080420031018103094030405805007050040900003440024000c07400e82d6001030303620281841e43d0f45c56050492404607564006034001ca00003044c84a460b5040d0800d00340c4a03229021a44105101002e0118a12561000c0d441500c40c13442d0690030603101c001d0381400c2c0071400f40081102ca80341c0380026810358060442c40344200c0c05002c10400c01a081c099a4005d042c03d0a02c141420340d141c8441751035030110b683c8045000c0f01c13413403102100409070707040c4c626509001d040c021696850306001b4004a40a59a9011b244903136580c00d82d840070008182441800303160b015018110200400b01002d0308090400c0343d02c89014824 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 88730315 1250 88729065 88729073
    0x1e060921130308030601020114090304140402091513080303060f041d1603060b0d030e0111010204180f0506030a030509040b1f0f1103130303121d07060f03020403050c0603090a 77
    0x1101c02540c0107419255803400c0c01d8001a003102d107a07030158402c0308050300401c50fa40b0008011f0341c0840300f0209040c0c24040141c00010000d00c140f147d03c0e9800070140c0b901380c4842c60742c000a00750403186401209101511042603655a000803220150b0004044c030b2080a00e0915801100d02c0c411085840462103540100380c0c0e061425207d403000d880690b00300f0030000c1c80000e01801d00400400c5c0c070080785d089007a0300c008100d08107000c3c1d4281405000340315018101001d42c100c500800e45c180040c10078020b10201c2a005d80700ca900c24880c02424500810818900030604030383e0380c8d5040e20340515040c002e409000113400301c0070045d5401248802882543c840702e1302080000030007503031851925440403034090034048009442e03000740c0d4404e2121400300282c01440c40c0543e5014140301c81e50b4181d0007140b0024002e442c6201000700382c2d10404001c0b02c03e00040000c05d6941c5074560503840901c0160441c100d004031710003e0303c680d01c00c400300300540c1045002141c01c0303984102544d50141e85034a07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 88731565 1250 88730315 88730347
    0x20f0111030c01110310050901030b270f030909070203090a05120102040306020f0703230a23070c050f04140606031305061e012c0901021b1e060921 65
    0x4026031243c4000010001c41b0304205a039500600021184211154150340f6a20b450003001421604001030164800300c14298211002000b406a80201c80019080781c00740c2c5d40302d41100300c2c8180180d070b043e804142507074001b0040e2901194050701d140e41c100c0c03422040010900440e01e201856550030071001c0003280b00b0b0300003401000e00012500341d0341d0f4403500e001802000604441406074100080c4050070f05100000c0705c02076506803a10407840d08200300d03519201049440e0f801c00514000074210100802000a502101c0d400c8441d400341d040d0400610080d02c1020707036116001030b035100000b0080c1c50f060000d5070700720b5140c0c020006000701b582e8405240c1402500d04c88104180740c05081441d83c0c51068550260080c00b40007085001c1214a280c00f10014155030708004841c0c0340020310030030f070942c107559802001c4ca404a03d0700c0c517540c1c0c41a459407660001001c03d03694565a880b0155000a83c40e40585e90032001081071000080405110408400700346140c3c89040040401c850070801c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 88732815 1250 88731565 88731581
    0xf1e0303020c070f051f0315090c02070f080703060203090a020a03080409180309090b180a0e010615051204110901030303050601030c17012d0b07020102100603020f0111030c01 77
    0x600d00581c0e59103400022864140c2561185529004500e000d11050b2110546010007000710050381104500c0381d007094003d0080c001e20030141c0c031801c11002074490142c0d00800c2584840d90203880c40705846803008034010540c3d0184e25201e600019013040081c0344c6a0003582d000842c401642e4070360b05581d000030f051200590095501c403101041c1480300c4141c07441070340c08030811126076030190100341e0f80c050310340740a900c60b1240c0c031581ca102005003611207080110344203115840a002c985809900d580091418610030346041d03180141c040341403000c202d10402c0c1c500860325001d00b00282c8a10901107010f00400442d800c06119070508801d840b04807805020b144281c4010a485c500f0900040031a12442e03210001c00c42080c51074100610f8500a17107054501c4100c4200300d2081c0d080d81d502d848880e01f0200c580c180195440014000d0200d4080c18900e8400d9090f1469103144c4c0740e010081da015404007952009442d10b2950b504d6015a516107004034920041d68100000490310600b102c040e0b0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 88734065 1250 88732815 88732817
    0x1e21111f110711100806011e050c1507030e030c070b2802030304121b02040c050c1006030203070e0f060609011e02010501030303060902041a07050a050f030415050405030a0f1e03 78
    0x480003c001403030001113211214904d0700e0202d445160a00000b490902d1002c1805126102d401e50402c600b44180219050b640f07a1104a4100741c0d81203804181c0694103c0d0a4400280380c01143c024807000401103400310445000280607440c20100380f19100c1d84407801c143e4000a110200d07016039409080010a20b00058025544910303150424030240480c0c60048010825020f54050415640c0000c1e018283c0d01503c001500d0205c00609a40d588a2400340c1401031080044200703002400b0340014060324402d07000d40f00303034a9603102e103a038444809680002c01e034a480720001d8180e04145002d0310b4000310526101c0428900d4602511144116a4060300141d44480051040c03640600905c00204a104421407400d46024810541c20a6008802d052144002002c000741300d810042501081e410109640d04040701f200b07150341c1da500c54032440d01180c4e030407c0e2440101e401074003903c084031009400b61004030001d590f04801c2d00c270409003c9504001070b1800d44c3c07a03c0072040a1178201882 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 88735315 1250 88734065 88734083
    0x3050706050a0905040603150e01020904020f0715020702031b01050d020c010506040509070602030a0302130302191e0e15010909020a030b010e090112020d1e21111f1107 74
    0xd001e42c000c210b46004d4000b01e00071400c1450030800140a0400d40c0f003100b41148002540396923071890640a84948883c40d544240085440b40c0784020643c0201031680c490722401d47c11906142c0b281050b4002c4600181d410b400200c111500c0c02c1c4255240d120407101403418a20f00301301502818100d800c050041e6200c0e83d9148100549810030b441500e8200c03030148000c017503031840e109000359240300310071a50f01095000b15a43d50781d0104440100d020350360061502403a15104151007442040030b104480b81e400703c0140009000340500384500644000009111682d80c4402e10720040c0e801c405e404030704002000100041b541c0851001d0704900e1041c0c0d03808a0014229800103000c841070b0f03120307180303e41c81610040000c4052a4910203100b1ba040d1054403250381e550030a001009171541c903009551440c88145010442c501c82d8071b105c02003010404803040d01259030100e0b8040c588500442051b440a503403060781e0100d481600140d0f0321888004540300341d40c0c0c0300c4c25007180c004683c100c807200f00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 88736565 1250 88735315 88735327
    0xa060c0314010f0b0913110919050609010f0215040605180f070618030503070302070315230a060906031505010b120c0a2c03100b01080613060305070605 67
    0x9410302503000e8140d606040c810840d4101100d00300c0c040350b107100382e00c1680300005d207083c400e484900980401103280c1004100003a01040300044960000d40b026201d50b41040c96080815030000002c81920005051a414009103a0056800303e051401440c158031074001003110b440c0c1001c409510540c401c000103d00c0b42000a565181802e0134640304207070350049165449100707400140310b41100d020386003000300710031489445a4920410b410191444c0170004690007815000540c41b0201c91282c0c10034007541d81c540c2d0001c0100c800d140d145c1c4644603002861101110450301040d904900c0440c800609103640e440e5210032202d1a51040340c010b0790b603c000c51480c182c18454a4014290750310941d0cd40071040003140d003034020003401e0400341100880c00b002e415200d16181c92041c1c00d00020ba9904022442d02c107070b10001c030f00c11158481d104840344210700d48005c0c040e0710860744042e12011640d45510080100f1001e2000703600c07510030360f19007001000c6030b010401d01001700001c1d244c2c2030382c9003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 88737815 1250 88736565 88736567
    0x12060402122502010b0625020603010608010608010611100c09080d0809010b0303090a0e04230a02030c01180e0408120403081009050105010504090905100e07090b0a0e010b0a020309030a060c 83
    0x45420b40081d0540e490141011600c0d16040115007000a0000e008444440824000003200c1200b44010750000804800410b0164105c8040c50680e0040d849202c3c0c1c2da03a940c10100d8146016450100851300301010881c014940360300200d50526075818900714180d00d82c07064034640400c1c0c3e08030ba400981c1e001c06000011100780314000b20200164003551414442d000403403d0300249118a82e80303204007070300040510180c1d05419114a9001c50401c0d1011403422a10b655003440510036446030040c0b10300b11810f58018021985041c00c0701080da17203032a14046035080446002441a61412820846001c000c0804040d0b580308074843d854082d442d08104a002803441038640001040754034000042c085aa042000e070750071144190800b1440310400c0c40c00605001e50300720124809420840d182070907050204990741540c100700020030035800c07240100014030301240302c2c2c1d40e041d00800e0014809004030304001c280002e4a801100c0c644442d141c0442d00c0c0500421050754010f40d9116078000007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 88739065 1250 88737815 88737871
    0x912020102091905030a0b04030e131d0105010311040906020403080f071a06030316031214060111011107030c05070317040306060e1611120d0e0f0f031206040212 71
    0x104034103501c1400360504140105c0d035283c445410103020a8940000541098401c0b540040e10110240078a0034035030507030940c1c0307025103280400d4848811103034890f4500c104e414490141200e81208524036845050400d00005101003a010b4600540812000c070205583d000180001401c10900c1583c9581d2400c1003440099003400301c0000071800c609102180d40d00000303469001c07070a0115000c04002c1c3c0e103401e403031051000401b51029410400f21102850000300d010b84101801c2e2200200745c01184a8203080341d21180c0044150b850a01c0520042071040d5100040c075403040701111182922521540104082d41d0b595200c0401c0c0042e041c41048510300071107004048022045c00320303041980c8100300e85801c000c041d00410030610981d0004c0304081101e40c954414020655540f45c018070490710140000911109551040030380b131828232030001401d051900c3d5500090f41c20108a6210403540407400b030084c0390b000b5000e00404402000c0303550410f000d10414641407c40d0802240309403d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 88740315 1250 88739065 88739089
    0xc040501080f06040611090907020606090604201e0f03010501030c030605030312101701052d1602160605070605010f061d04020408030a0906080c04060c03080a091202010209 76
    0x300d0304036042e09400010002403060b00301d40d0065000c54a1007408202c05903900407412850340c00515a07042c13000c01c54002c6a0140103140c02d0340e0600142c2d40c0c501c14001901d80621594440c25000b203002207104009201402c040c0f0b20386840003030000c40d41020300a803900300292500c40a48008010016580c046c4a0010b00301e015050600501c1c1c0380100080e1280a0740ca1107102c000314690000c0c0c85003044002000c080c0c079600e040b00341c01c08404020103009003c11182c4915807400620040c2104181c44d00100040494500d0a6951394995041040c21118101d00a0130f5200f003580403d904000010176002400b403e071b41d85078660000742403c0c41990381c1070b8082c5d2a0306a00801c18402d444d808518108200c20001050081020100c0801c00a1055602c0045640000700e03040c3c4095601501003411141d59a40b19841922a0918885240b0941c0304041c00709402d002c844c00040e002d050031a9000d00c0c24880001d605a05443e100c602d0840c08a0800050f5030004046a04d45090000000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 88741565 1250 88740315 88740329
    0x20f06130e09150a0b040605030601080c130203010e0123090f0702010c0819020a05040305060705031006080105030a020405090c12060709080304080d0e15040e040c09180b06010509030f0c040501 85
    0x141c01d031082030580604441c0035220400854031041040c05c1500c072070f0000001450040d007155442c1d030f522411180c131078071072114071403254500c000c44a03803004d454000d0364161080340c00105880e9103020b1074404803c40401d8021180108000040d46580d0345183d418807961943c0d0440c145480d00b40070003802c464484052400380030144040c40300d4120340b24180c10042c1180d020050b6144003c20042d1100d0160741c1c4000c0c0207214890801130b4481e405400b950082e424044209012038480d941944c06080134001d07990164403520031007002d1702c0c16402a540218280e401e442d00000d003140464481c95003071144000c0717607000c0810300c4034959004507081c0c001e12a44000d1030606040c09a202c1d112807406000e103040284400c20303003469507106410b6a0101c40100c910781d41d6903a40301001d03000c0b0700c0b0881d01580c0a0b0303100b40b40011a90a507026241701c0700101401001500072903641c040d07a0403800b40c01e0a04108003446900740503101000705c140040d00c22401808000d0b0184104416500140c101c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 88742815 1250 88741565 88741573
    0xd0e01140c060103020118262a0904060902041b0e0f0112020c011401030317010605031509040503090315041202030a0f11010207020a120b0c090a030f020f06130e09 72
    0x2020503074001c216a4150f903424030f400340e03a00302d045e0086691001c1d250040d0000038000303468415104204e40e010508014510251050b0710121220001070341a60752a43d4103c41c0e102107002c80ca86001800396902c0b510a190004080c041600481d00f01c0ba0409200d5a00003040143c0100080c0c0205146141100c215900c40c642c590603000240903c00e001e6400c03100640102d00ba9061440c01e4200314000c600e80c0c1e414012541e542d090050a089170b034900800d098026100105200c1d00c503504581c840c6001b04046800801200244842d418000740161400e0000f8090000d2075030f01172205d9045404280e07030080f958181402c1402e403843c0390f1a1003005640c0200200b8941c1ea42140c548441c802d0036040036110202401d001c14068840c40100a510015102020500c1c0c102d580c1085491400b40d01d641900f80da6400c010001d500c1a8082103a000300100300407c0000e00409406030078a02c0501f19040c405801e401040d080d030010881180c0d0f0015580080c09909078a201081d400701c202c070014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 88744065 1250 88742815 88742827
    0x1b150306090c0507241103040b100f0522060f051903050606120a0b07030507030b010e0120100207050a1a0408031b070b01290708090418050d0e0114 65
    0xd8150321509030024903046130005581c00d100f81c426100035020340c045c2e400344200e011107030b9107190340e500031101121412154004284a00200e68407171064070184010f04d014541071404100710840d652a40034101c1c081c0721070000309510b4070300801e001400303420381060a041c148030401c005004603580030342090028600070030201e10001150354200c0d40a4a2500107400020800c0d424146d20450203000b04280c0f10a0100d10380e030503840144205105e0340c0400c01d081d482d0f401120307940702000800d80061103202140742903284c101072840c0e107c100e02003103854071400030381c2003c107903081000159400c3e00301d45940002c0c03240925070f8600c4030010465600b480c0c9801d43c1e46480718000a03118041d6041480c1c408400011a501251000341e00a50300d0a5950ba43d04a410141d41704004111031740281b42c88152010038020b0b0030703a9401548627508a061000c140240802401d04150004280710301441280101d039091048d00300200c865940e481c1070f03403c14000902000340507207040b00c4c06a4200b142c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 88745315 1250 88744065 88744067
    0x605030108070b09030601091d0d2105060f040e0304080a0c031214030a0902040603150e01110705120c3306010905030d030e0309030313031e03090b071b150306090c 72
    0x340b241954043c600c009840d0008101a52a94100741030027000c42c410710204a6403543c014040440e9807107071003c00380441c41c03212209410b44a00b41e62894210303c0034070762452246080c1d0000d99101c2c60305000c0f01e00341559052803606c0c00c100c0410030340f050180100c0510034010121140b030003490031424070070040b850701c5040900f144030081c4021030f0341d0340e03031404001156038a070001c81c02140c02c030801040c585201c5803201c009080c0d4030800a10303907107880480d05142e07212000395001e498024001d80743c1441c0700e411407500d6510000c03244400340245031490420140102410340150801e4218084040e03000090304614900a00400d0501843d03c2027008030360380004030041c0c40e124034500440c3c000e5441c41d42c645107001e0300400c1030b454040442d5902c1c0c0265011560300c1160b0040e11554030003400001050009070030740344080c0c0051103582d400c0c40b00b280100c008002e014443c40115020424061318010400000d401c2280e10790300c2d0350a00e0340000da06025000140c03c15500401008400b150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 88746565 1250 88745315 88745323
    0x617010f0f0b09010203131e081902010c0606050a0b030403090902040b07080703140f13090b100f02070b07030f020610080d120b09010305010501031a0405120c01150605030108070b0903 81
    0xc2403640040c00083e050583ea4402e0095440d07031030000c94070640e11600c030352981035014664032100603010180e080000745414001154074840400c4c2c1c54034000080c441c3c00442d080a40180240c80b41d5840d42030025044d01c40702d0640e03008000d048001512402c091070000c1a00031150b2241045600500082c02150250000c0b580300c5503000325281e582c1d070381e9807406807000681c10720711804c1c000020031b0061049501034010510404400e01404025444809071421200130405003038102e0007485802400500501c09912406242d00441d40c502c0e40c2c031054038a1070742c001d03941240007034100e5148009c03407a0100582074201170852142d602550a0042607903859034080e03c50070400c0385501081000712040c0c0d0040b000c0c200050690b07920781d80c580c2002d901810b000c0c401102c0f00070001c04c40041c1c01c2d540020031401268000c01900d0a10110031040f8542e81100d5540003541d5030300c00342c01c84455044c4171140000d00180e00c4603600d80d03161140d440d05005a651107070112071801c0111541070380d0041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 88747815 1250 88746565 88746569
    0x7140a02010f051c0e010204061b0b0f04020607060911040b011b110d02031204030506130807020103020306060f1603080a022a160f030b0a0b06070f03030b03070617010f0f 75
    0x71420f80e0300c4002e280540c08492403510001402d903458282800c0d1400b506400500a0325000c0e140d20050f50750451041d04501d1a1071005442c400f44040441d2504518144080c0c009000500c0303503062080380c2d00c0710001c603000e09004a0780320303841c0c00c0e080c04641801d016041d50704400342031010038002410030306403900030307281d500030b2150002c0c000ca540b0070780e5803850500c030054024084901603e40303000315514691050105881034419000080c2c903ca4442e88a10110790344020b4182c20101140c1c012342c06500050f094560128050000b4074924640d00080e0030400704010250444510a040c01b8108810203044ca1010310300401a000340c04550215518400308071032100f00584c10366507a0b40b41031500f203a524000395521031200040d500902c10034141520300983c80e84030640c03104d0300c902003282e0940c008250400400e10401c0007191111226400b050301174100403d000d00ca01e00001e0402a40d90042c0d0702050044082c2040e2280c0a1103450140003902c421b420851b0520b580c8440c992024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 88749065 1250 88747815 88747817
    0xf0105060a0203090d031103120a0b060301050102071e0b0706020a1419140408070b0a0f1b080901170106020718050402090103080c010f02030c030402041b09060507060e030a02010207140a02010f 85
    0x24220101010b2241f14556088070002050f02d4485624140c801034403142580c0c20901e507820101290054030b000e03411241221070503001000c4851520450064031100c1c1c1c1100c075180031190200141d40221030006008c2c2c1031040c100160348031881c00f005404d00d420b40d04140070b0f043d018099181310b1861115006440b2100d4185a08108c188441840c0e00c2c1c0b05640005040340a5040b00003554803c3d500503203104035403521a200000d902c8601141c2c010001166611001141404800400c0e00d55009022440e4107240800f021900048c81401d402420307803000740164040c6004000c840d013503171100c0061981c41c80c01441142850f40004040b51418000906181d2000404565622095000e40c81d01d8005007019034803480c01070048882c0c1d4008580070f0780a1410700f00360001c601501b2401700f140b14001d465400d0600c1c00d140301100d1981182200703c40a90795241d001c404404100050f0919540c10381c00560f48910520f0007200500c10080403841076440312069100507030f00900c40300301c50815 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 88750315 1250 88749065 88749079
    0x4150311090402302706040308090a14030408010c1d01050a17011409070c030210020306040216060507031107080d050c1b070306060b041404090201020f060f0f0105060a020309 77
    0x2050314404e40303860302c802d00c58081c03112003900b0500720004640598032484500013600684450744003022000b151401c81c412254109400060003e40501c0c3d9280e003203038050701160140d06a80c0d81ea4806200209803043c80c81e88041030400c1285002d0180030385000d40c5262482e50526442641d00b9188400c4502d5810302c000818070010f1144500030907407803d21a07600c4403c0c9565102c5015500c0c5c0e004071031480c007820f100b60000d852a8003404000c48810740c558010f10010000f000f005000750005498240e0298080110008483d004103104034018003403e4001518142032501074202e982c505002c0b1740040d01482100c001c0342c040420b03a800445040808500d0340d1703400360808458170031540403041210ba44120003c2c6040001450426684102e200300011030f00d1b10300f440d101c2c0c09107100d00e54410360410704480407400d05400191030288103004030b0f140a18042c615a0034500c04036169203510070190100f11503010200099401810141c40b01c1c0c1c540f02c000b1070700a44034450700d060360f400b40017 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 88751565 1250 88750315 88750327
    0x41a06032406030c0a1d070f0c0f050c060f120a0605150d0b04060312080c1303030c02240d0b0405040c03060203091f020a080a1406101101020f04150311090402 70
    0x900b44464029400001c01441c5180d464114402061700c40c098007160441b2104002150ba0340031710541c0007031101584850302025420b60341c0c04000c0614000450707144c000c000f54058161601d0340035204500d10b09800744e071580c214000c602401071008128501c1d603030030202d04021a441e80304100c148803d4810741c0d25629520305045001400d00340200c01e4100c0e2800d0780020501207203102d00604501e03181d48401503901c03849442805405841810203415109010810009000b20042d4481510140a0041904022029010303040782c00d50303001d14840000520b00004d01c0d040c03040c8201c46000f181d081100c1e05103611403d00640351400003c1c42e1550001c04512981010002000007500c1284001070f051100b14103240a0741000c000200403601e00c001184030014180510545405181c0755030341b9a0b5140d5041200290f4080f90420500c103000004500800082c0024005410341c2588aa80c6919044c208080d60f05282c0318482007519041000201ca200d844c11240c540ca400c94000d6181d82c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 88752815 1250 88751565 88751569
    0x9060c07120918020406120b1e010309020310060608011a0d1e05240301050603120702010915090510020105060108012603040f030605010b0307050307031d0303041a06032406 76
    0x319541c100c0380d0001e912620f803201e030f600b5540040042e030b8260f9440321948403581940a00303980a00030303001d5200180d407000d1120302c1e00c3e9074410001060145400310300d00c071554001c03c1c1005c5101800e04441602e074001801500d8104200e40d0060000100120340701c10401c1c150034680c001c0c50721702110207031601110884805245001e000c40d40a0440810a608000e4982e046440c65503400c190019100c3c00c09440078a8180706483c491040540901440d0460103101d00c09680296812030500c0161500810045c2c41140310300300d03252080d16085103940c01d1504120300419031090003011681000100401c80c1d9100310102d04503800618100300c100b5000303803907011001c251701038542e003032001140001e44202c041025030100c0703000d500204696602ca06170044a0700c81100c03d000420001c101240c602e9100e580071141c1111114101e4604900e405281400d551050354140d41e208007206561404c01e0303c4e00301003600010118010800c40e01c03804103030000c01c0080c5088848070344c540d03030014041c0d07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 88754065 1250 88752815 88752827
    0x110108100e15030601050f0a0504020d021309060504050a0902010e010c03050c0d120c05040b040608060406031e111207090f0e0102070f0c05010e010519090306050709030201020609060c0712 83
    0x142090368110345492a224400014440c1c16803100d0f0311a1080b640006001d0074012615401107101614100000d824001031002030351000c0580e00c00303507908201c8041e1a282e8407501c04040c104006001c240340c1c0c0f40c4400c01041d16005000351101500e0000d130200140c0e0802030302180342c1e1080c280790b130700001d89003800c0e2128094080907590a000705200342d40043d90002030504800c00022007004102c0c0000001c50b03450046000e19061010108814400300740100e40455000710024004100d8076166903800703405095044e00080c480c04880300c01c40401042c61a1a841c4040555490500c0e16150000d01c0e940e0015101d0305805a030b4502c1c905850b50502e4100e42c503000741040c020366a82c11b052a08642803a8027000c1552980e0703500e0408111036218101207115194143e640358100403081030404141081030b500a001c1c40b1000740d000000034414065244156800e1300c848502c01d203540006400e00900030003e040e0354201038108888051080300303403000607810542a03000202c8106055443c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 88755315 1250 88754065 88754069
    0x140402090615030a0606120c050405131509020901111615031b020604210909020c0102090d1b090e030304060c170108010f0c0e01140c0a060203010305060109110711010810 75
    0x14205000013001034101d41038004030104c03140b560b03840b245200400600822199407404200001d1010402007090380f0301203040c0d030881e0141d20000244a01e904d0503000250400d58000d4110540205070500d0035030708949025482c54194000d40102d1f422030781c0465090700c8900074060840b00f110041190203200303030700072864220900b07242115803900350360207551750a04030b0781147c1d286410706003240c004511008004ad032240759103402c4c06040c2072a807100003030341002c80d000b400b56500b0301600186a50b54070b00c001c461401241e480c4110310203d0352454030380c10590000d4142c142009800d0072034240010481c1e6000e030704900d00084859000070115403814958031001c02e0382602e000003140541040d8481c21500a0b840d108000200c8441b000b9203041c05603031a003601141950680c084a214004010318000f490003041c0c071895040c0c3e40c1d5450480e0402c2e00191440d03849031005005441681c0702d40c640b0600c0c8141041d082500c2c590b207290f20041030f00d200c68104180400816084207000f925080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 88756565 1250 88755315 88755349
    0x21b091003061401141c110d08160204060807030506041b0e07080a180f020d03030605030102070303230f1302030c1309030801050a08120c2d010b01031404020906 71
    0xf000c0c0d03060076007214010740c1c2070250004802e000800f0507464a8000003800245840044440c032003a001c0d162880407075180e0400c00c1d0000c00380c030180400203003440c1c02081104031030441081203c40c41c1c0113000403511240c00845099001070401c1c4040362001130b415074440d50204c0702011000d001045a0300108440c0e1008449490450a2040746a080b09029200d00c04568041000384107100840e0705c00a9942c401605510980c0b40c10405401c003002007900050080c140401c5207a036400c00310342268018181980000da40d80c66403a02071401c81c450341201000804004868203066030034400c52100508058090300c110103020045450500150941100003025450034010f0490600081c011100c8100d000414400003c0362928224880e07130180c1d1000001000300055000c40800254003182904182d8419000505110400302d107a411f920035040004240d0315040b01d0201e825141c200c2c00841c10315040480039040003900b03079115a4855011140364400b0744640c004110018002e107105a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 88757815 1250 88756565 88756571
    0xf0702031803251406040608040b06210d080f07080c0d0f020406050903100e03160201020a0f03090815010515031306060e1503010209090417040801020c060105040b01021b09100306 79
    0x280f1048502484012190380815401225140104111491099004410201d0400000715002c0781e980010139921100c0607000f41c03100403941114444055012404146503840009582c1015a002c80903940054044200c080541828a0013401c1c480300148071581c51140443d202c859603506030445a620180010110b650740d44a1000502550001c20428042e11410341c000001c4c1d1820301c0b60446641c0910041c60034a030180307212250313940342d00c031042c2c0c1103218661000d004aa0b80d404a00140352003a03c07030301455843e02d0005402c1050320b102c1e03121079040c401c004001c80e486005036150b801002c030011035601e5440313040f031030082203038407002034090b81c5021004150a8915018035020384910304135010205124000c150903485041c0c180d5401030254004680000c010780160300020058000050405450703e04080c00c9030040c0701041c0d6903502002c01044613080920803880c04032800c0c800b80504140f00c0454414001a54a040c4e0044501000040400d54160100b001850b0701030700034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 88759065 1250 88757815 88757863
    0x100f06020c04060806060d030809030d1a010e0a03030507020103150e0a0c180513050a0b0310020304020405060a061d03070b12010305060a02070b0c030702100c02010905060f0702031803 81
    0x3540c03900c010003900e008038a03007a00456685000965030340706c0d4200400b0410b505644d65000c542e51f010192200305144010b20150f0b00d10780c1c4a019104446401034540402c400001c000148000c182e076905c1d50054951140c2440840d80c82800c8942142e0282030200ba40718110b05201c0c45181c60341e2080701c84024610030302003a100103400c52044007480d581c03410124000350744550035000f2144141580040d00b240138054410b81c5410003640141e410200003040441000428103250404001c007101e01d60000810045190074482d054200c00140d88000c0840c2c10440b015044046044819940010000c100801d554041104070041c1044642040d113400f90810140241d120230f0100329624080c03a40080c0d200c42452081d80c3da00c540028040040340c80d22200008541c3c800b503c94401c501503540052032070101c42c06000c22800e43c540c000501044036080c41801e0501c058a0043d1070702ca5017003404101039001098803012204000403403000452900042d1a2019078a240f40300d1000090503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 88760315 1250 88759065 88759067
    0x605060a09060e0703060801050603070519050315090d020a02010f030209040603050f010f0501090e07060f0c060213030b070c0c090b060d05040302010c08070c0213020f0c060103050d020d020105130b100f06 90
    0x120f80c012081500d05100003a11180440d0a072101100c1c0c0d00e0b05548158801c2015142c113040482c0001000b140d00c10034140c43c0c0c0003090501d48202c04406210700a0780a100e00708008105100c40c82443d031000e0160607040b81d0000f8101001c00b0142010140c0100e000140390b501c0f41c0c0b00800a561001c2250000156200c42d607000c3d0070041002c80107141341800008140c8a0390191202d54075a103800b9040460610800b43c4c1c4504403465030030104000c00040c0000034186100403c55005540d010080071480c614100c48100f000170b000c0c8040040c101c0c0712000090269401c0c0080d00d0107450080380008580011078100c1c0070f0385c1481100705d814001844103150f0103500240031108140d50b09942c581d2092410764648401080017508a480c40d40306803100e02596024040d440904810180303044880816240fa05e1000e0304152500e42210390200089901000728525511407070000784040e107080a002250640d1844e0040c001c80d004000282c10411450b1102002e005040501174007030f07031161702c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 88761565 1250 88760315 88760339
    0x160f1e0b09010e060f0402061e0406030207021005160b060117041a01150906050306060403060207050f1b130c020109080a030c02060132030c03070308070c1706040605060a0906 77
    0x8560032994a801d000fa1140f6a010030510b10446003444200d015440b07a50900c0700e241d1200998490301c5000e42c0301d1044891640c4020001841a6a000342c2c60749128010803000c4000c014070981801000c029822001101260340e1400c0c4c4c0d00020030303608541d207100050301c1000d1519210350302c8051541c10401003101001c440b0060000031113130703181140c3e01d0343c400e410b42000c20060342c0045444444104007440c0b0440095a004101500356420f050b40c1e0341d15201660090b107002c42c1c06800440a0031300e400ca0030480da454030280030003145100c0e2900300108000b00d00015030341c0c1081c1d4840c2e1103411428002d40050700301d254003814840c3e0307030104010010020709079001008014025440001410904411126050482c1070905031008603614080c030a909070102e50070350140075080341030240d603805115105c000c500406446a07034001d1440c0c804a1f40c601e40d0004101c405001d000310070120f000080060740154031541c002500d88807000003424020f05540003500c9242000c1021501e224849 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 88762815 1250 88761565 88761571
    0x302030d020d060905010f0810020c07170109140c0a09020705030708190e0d020f270108010b03011d0d0c0f020618030c0a05012f030a030506100203160f1e0b 69
    0x10007001147d0301c2d90f404001c0044507100e1114540e2141902c18100940c66000b00310880d81e0508a0344565503803101105170411848002069940d00c845034402d006130005504900222000074250751f10b010000500b8901c8039014014043c2d602040820801c6420001c49840b41e4021603c182c44440c07041c980c41c1429001c40311200040c000e000c0d03490060805248180360701e6401028a030103154070300148211011000901c00c0c0100c008100002c0082214291501902c510f07000403400c0c450302c8050500b0348154950411000d0b04016010624040101e910410310802e4a0302c1d402c0c1315124103020800e400d940740082d40c030641c0044d1000b0341c1040e000c108950141d00740d040d84c9000480e041000000400c51013580e01040c4286d00700384036110000403054034140d800031946000450b0001003459600000c4440c0c0c040f03540c4000b449464586290552210103d0344011450000e12040901c2e409501c1c24004008000703500841c0c003005007101c00170305200c41042c3d03000d00220150400542410302a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 88764065 1250 88762815 88762829
    0xf1e080d08190b0a06051e040824040f0803040201050706090809030106060809030d020309030c1b0109140f060306010c05071e08071a16020306090a15020a02030301030b0c0403050f070305070f210302030d020d06 92
    0x7005107040c0aa05501032441233401102581c0c55000d952100320b065803005000301d040010801c0190002040f078170a21100b5030003040c11039164403000b41458216040790f005041800104800c00a440400104680440c1c0224002603229121550f9080c030f50300a10911034010302075900030700e030312680c039100b52415043c090380d030742e076145a030340d84480004c0d840668459044031410048549908040c8029600024185055030b04850251140d40c20101e10707411a80c1c900c409440285180e0000c3c0480c90050311111000e403100318640910309003080f41a07011000c41c0300307022440c4104181030080d900f0816401806448041ca06a1845500c681d09404122010402c1a8940402240078400e44031020401e400540c51a402c68541c400c18401c020b081200d4801c08100100001d1070030b0107d8804070301c4e240002d2090600318605a41001c041307800c2041d00d141c1d41c090401c80c56840380408400c088420070603d840c3c5200742001c85c158450036043c50707641800082d64148901700b07030380064101d40013 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 88765315 1250 88764065 88764103
    0x80f030907150203090103050702210711100507030c0c150e01090f140f0402040815070206070305060f010c020102011401060905031005010f1e080d08190b0a06051e0408 74
    0x100c25080c1e0b08503200c1010440140c1c4148a103017690350082e441640c001065004230b0b0f00c6100f105104240c11440c8400d40300e10100046080d0082000450b400792611004940c402e0010240c030320002e113180034034100070f01048903403030402050141c80440134015109a40800c200f0a91041c0017614482c0d8901c0e0450000e5003c140008040030300241c0c0b0703025503210360703c0305c05c68100d01c1c0b08001901c1400c075000e9500c0b9600704000241040300708a41502e9038005c1d1041d044500d80004060305255004003104245410181000615642e2610383ea05010007403c01d8a1052000d000403401004c82c400007140341c2e2200c50012607100c1c1c10040743c0080b1388044003119201c0304581c03145c0c01901c02c20700c11000e245203100c80c103010b040e80e18492140304200100354031440703d549495280ca0403408001d05c0740031520110520010084840b180240b00c80e11540620940100c60040b030f102c29220300c968001c01001251441c0301003683d503101a0161544045903841740d4550341416100c65898940a500c600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 88766565 1250 88765315 88765319
    0x5030a030c0b1005060406030f15080106030c0e0108030d0509011d1e01090b0106050a0210020409022a0c01030c05040801090506070f0815040c0e03030d0e0106290c0a080f030907 78
    0xc9143c0380384180ca001525450920b842c050003600501110403c1640440d1203100d14040c10540384000340c01010380307a001140240c0f942c100703030a0071001c90b0000c111000f00000180100d50002084625400741100f0000b06035488041590050080d28401540c07103542c00d9100090510018140003c8100d45501e070710346408460600e800c0765000c5000034051010344004101250299010340003c060f0350040d036540c0124a000c01c0101d03401038000d540c440d03a002c2a04150642c070703101c8258400615010701a809088411010b5950b01c208c4400c1d810140c444540d020034510890030350b402091100028400000d440c60a261030742012540040010954080024050b119214140c0240c0009282c0300c1d04141e00c10601002c0e0412424482c14041041e1814945850410007000802810f0100281c60307604036940c0340c2520869030040c0070845014038100380c50056100c0c1c030342c00344030210000c59980139541511810403240c00009003007603401050480f428011100154407800000b410340e0b501c1c1d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 88767815 1250 88766565 88766581
    0x4030f060e1213120302070503060a02031006030b0603060d081303080309010c0f0921080301060c11120d03020904090b040f0b13030504231003090605010909031b0c05030a030c0b 78
    0x101844803070b9214105003203c1000b003ca000303807441e902580a441503844481e16003010900c8c04100765403810040b43d0000c10401108807081c0c07480042c00e001e1406001350031109000030018040540114865688038030340c141000a4082101c0310b100002d02a4028107613641007100d4142c108070354894455091203420340100d803003030410903258606034952225040c2010a060325620841032100303201c0850034440f002203030910340610b00038042a521681921100e16054030540140081c071030140b2070004607507550700070106403040e10588d507140042e03c40043e040020f016004420016050001701401e100601103001032038003010340940407110850711a6100070b40301142031180900007801c14001030211a03981f180f80a0000c05200e460340b5010700c203030f001681d548504000c0030301090351042c0b890200b00080c0685401019107080030030503c8000e84018128880d82d4100100d03100c9030000080030001c0c00c12100020f841d0107401c48140c0074044c40c025010446955060f14107201c920300180c011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 88769065 1250 88767815 88767817
    0x516030204050c160f0807210f080f0c0a0c0f05010605011b0308062206150f020f1b030a2009180c0111150405060a14040804051504030f060e12 63
    0x7140b0201d011101401300e80d1034180c0d410880d04011103003100f0030010203010402d1168400d0b085004a0301c01c40100421500150042412108104c18080e01e43c0c2000340c0d110306002e50660051480e66015942d00c8449411100150003480c01000c4401c002c80740014050154025001d940003138030f454070780000008101105004101c00100042c07060000a42ea0382072228007018030a0603040c000c0c8004806507030180940f51190800c2040050032240c6410041d031001c42c1002d041c416002516194000c003001c0c9885082a0a003050000070150241a058404000070502c061300442030540d041412804074070344000b07d9030b032588a5407840021501641100d52103035903c0079804001c04a100d2004015500c0c090b28100b42d81e100d004508074181680303c000c585034852445140a4000b518107a003000c3c2c216007002c402c50a200e90140b041000003403061b4200c070f065840464000c1c461044c4840911668855070304014460181054018100301d50b80e0040202940240c00ba00d0015031070808180f51 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 88770315 1250 88769065 88769077
    0x4110405040e011a01140703260a09050d17150105040305030f09030c040608100b120f0f011b020607030f0f0c050a080105100e0607080d1103010306060f0e07030203060103090516030204050c 83
    0x41c0f1030400080d800a4040c0c9c03110b000440d070700202c21000101142c2c81c0340a01c1c03030880c0c1e10030515032210501810400d046c059500c2c40a906d003080035009010f000d290001d40030007030401d503d441c49400600f038980e01034401e8900440d48001101e50314800030107109030707640007044558002d1060115010355440e2501541040d503801030014415140140d0456001e040058246074100001007404550345000744a150b01040e2020024101d404800038541d003114020581d0681d242010b007400c3c0c02d10b61303001c1203254111840c0e240c04110a024a50141c00500035040801c041c0c0c0e00c0c080034068002d4210740034107001e40d12625806916a82c0e50140b19482900d5501180040e9604c1c5008840f07240800c050483c0d540644501401c2001052001c01190800451054641004801081008168003c4d203002e01400c1450800b014646200c030001d44d40d0107030460b018103802200003451130b4880d40c0800042c9800c0300450f500003690102c083ca14003040e000584c040c40c01c03e000030764207014032022203003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 88771565 1250 88770315 88770347
    0x9020603011e0605280306030b010605090114040608061207050d0308090d022e1b030912090312030914070f15050906070b09030f0f040f08010506030c04110405040e011a01 75
    0x5c10350a00204a2803049003000134040c10766031900840450f1f00c04c0d551a000c2c104544545560b80c0c0784c0300014089a4030441c00501e02c500030442882040e42c1301080c141c01500a4600144980132010440c0c20212a5041250440f800140382024142c0c8611050701810100c42541c82800c400d8404076151882e011500d8074602003081c0c44100084001445e00035110f600718006401c422015416003001c5071103060b00000307511000b039101406400003006c1c0102100f400c280103050701c2c55994a82580c8414520400e15035205902c1c8140801c403480394040344429401c0c2c1d0a03481e2992401000c502a5005150055a07640c003a04402d5010f002207412403000284030a00380203e80c0e03034140e20444000c107422218082400804c4183c0407440c05080c181d02c6910882e40c8481c2003074541610402542e10a0075268144401d00003152004141460701400035a0003107a102d00081c65407005108950100703810925002c0000440c5406620824502c6c8420208548200da00c41c0110360021030084142 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 88772815 1250 88771565 88771597
    0x1201150c03021209010c0c090b040b030d090b07020a05030307060504030306050a180203150909010b1f0c020409260d050c09090703052a070b0a06180f09020603011e0605 74
    0x143c148280310000d0080c08605140400b032444e41580d400840c070440380d01c22041e2a880d1150101d040ca024040c42e00604001c0d001415a2107100c48002e0a200880c031600d1485d100c0012032409649030310082e14040c02003c4e00b01c0e07503a014039140c105c00501c41110103800181c6400f4001c2403a140030b091210440d0081d444d914049200000c4450007540041c108000004c0b115050051540f01e00f81b0052050f20b5803000054183c003003500b030280c01111b00340c401c0c3c6a0140b10f0005e44105030002f0421200d2501610001411121494001e4980c0d000e0905900103c403500a800703840d4400c440213090500c2e00c207000b485035484140d68201d580c0541101d90790b00880080000e00e00c10300c2a405103a1020303070104000c100880d40940c000300c4140080c1040b038108800207000042c021014180e64000c4040c000411610345015070307806025840c140031100310b0303440700c0e01d42080895940000d141c0d0380c1c00421050b521350b50f4184020070740840e41600200601c1e502e40001d20b82d401a0b041e54402a80c038042e003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 88774065 1250 88772815 88772833
    0x40f0c0f05090f0907110d05190e01030b1306090b03030403020607020d03020715050408010509060106140a020703150b100e0102030d0513150c0210060302030705010807050409021201150c0302 84
    0x2510150082c508841d00103e464042c940d06560321881140264100e440e5101c41d10381c0120314506140e030031a40c1d601485010440e040d007200e0071044440c5000d000b4a41411030600d0240100c014003a070050785a131006001022a503021903650107032007290701d0840200f00c1a46120280f540703034040c40c80040c0d8049000c5c8901d40241c100302200d154a140b00b032050303c40e4261250011401a02c40c02020300005101050600c501e020034031403240c01c0405000101a10340c07514a00805c10140c0c00d0b138100000e80017003055041a4000c12522005e11b81c03107401c82402c802c2c0081d9401c02001a804031900c00d101c5502d804808a024a088581000046c1d020314a044100b014040150801908061410510080e039802007441d101c03441102110a81c00441c03001c1d0400c0000385000c002c502c81101141c074000082005070740001e40b1108581c1c0a080441c8180e0300c60780b042d0b440713018503480300404a00000e82010b504000d1f40105041e1000d1403280c031000d80f06080f0403100c42d0502103005000d42d00460756 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 88775315 1250 88774065 88774067
    0x3050304080f0406020619090203070b18040204090219050403030e1e090f101508270a05010b0411040e070c0503091815040516050a020712050a02040f0c0f 68
    0x565110307000d010708034600168015050390b00d920070350000006812032410701180046140854181100442d010702070030b00ba540000b522101d0510880c1000d40001a40711010403001c1800c0010032002403085454550351408000a035024144401500401c82c1c1c400c0784c4035001e101034a06490309a51074080d080c811000340122840c0041c00007003500005030200300580d0316643c0700c910880c108074403d0f101c1d040c84461f01c1b04000712504201c00f00340c031111915100e55404079086901011003100310b5a00c802e80f1f1103031206003c2c070068040c180d0061410a60a01c20150820703261140c5c1a541000481e03000842425280118015841c00c03440740780124050310302c2000580c0329039028101f9203243c00c11b0f080000f03012500306550382110800b81300070012010000c0c0c010310408142614140406d10301031880b411801c42028200c1d0600c1008520243c080d8420403510001e4003140c81e206988508505003075a4912070f05104903c620700b441e880c414003a2840c010040441c50641720324854508400c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 88776565 1250 88775315 88775317
    0x3030c030504151808030405030a06020915070308010609050d030c0f060b040e07080c040515090403050903060a023601030b040f0207080a02160501091412070602010b011107050d0305 80
    0x1080c0e04000c414000440c40c07042c201440500300750261605007000350b915403055100100d0380c1c401461500284070800c00e5440215600c0a4a80c0c4180c005980f400c1c04c00c0017a18030380b5126235a001c8460042040003c02d60000050b5059038050345030380044030340c4c030020494201881d040003030000761040e001c240040d035100d030440f0045100784c00104402024a01080440d03000e0401d440d03059104441c2045008402c1c0a90020924203840c10f00091800c62030180c02c50715061100b500801025000074189031086040d9a048400101515140e081c00d032181006500442281b030000000d45078800141c0c81c84185502a0001000048214211240041d07004044180c0001e8000c0e4441d03141c1000240144010185e1912071983d0a44425450710000c0c5002113141c10f50100c80303030001d024801c13aa04403410f0001c450281c10b01c0401d00056002003551021859240c3c0c00b18414040c002c03c2d2541c064000c404800000c0e42c0e04103068483d52a030039a81d0a1500c1040e030407246554000e00800c3c4903070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 88777815 1250 88776565 88776587
    0x12180309100203091f0f0215060f031005090601090e060403080a0b0a080109060509150c03010e0a0b030303040c08120a12180f050a0b010905090c131803050405030d03020408070303 79
    0xc01520f080c401c04001280414001141070b9412104810713644000755048801140e605901f4801172500300d00100b54082c0c0b803400940003a00c070305141900440d407070740e0400003000e840060b02e07424001420402140c0e95100400e0003042d050a062682142c1029000261b25100f1a0103a860403180d4941d4001c00000303000350b0098030740241306000040341d01e001c02d02902100602c946000225898040c56490a10b00003841180071046140144000404444180c138152206e114150306940c40300c80440c0000c081400c000c3da010301011041206101500040008894101064450025080040003d180716034070700b001c081385110f94a07015040182e8400c280030041011004081149911000a40c0e100010300b15280d6126003c0d0745d04001c0c1b040c990703d0040c00c0c420b10038400b03424174030300143d191640540402c1c0920020140c07018004080d80011029100b20046c0c1a41310390709007401415603115001d168024811103202c002c2e824072034800c6a04594109010b080c2550a55400f100e02e0b01d150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 88779065 1250 88777815 88777817
    0x201050a0e12070f0e07080705070b070c02090c0706110901020a0b041a010e0a060602030f160318060f031406280312030207051606020607050c07030b010303051218030910 75
    0x40390310007a110802c200e1a00070340030111142c507000780f520a1703800e03030340000600e5581000034080a1001580c0c0020a031204075610404084d090350320745604845580700c90300c000e50710076800d00901c960010040028051036004210502c041300d194031080609215000986005078800001075001c10070b045a0641c10610496504d440302c5103419203682d0a1000303070400c3c0d90206c10541840f80480326449a84001d00c0d460014600349071401040c105035010341c244c1d905a0703811001a50081603c00e40d50030500c0283c03072418458464550300d0060903914504080300101e860b18028805107901c840d11148940801419181c66072640e90044942001140c004030760600728200100010b801c0c400240e64607240b40d90700607191440d9050032031070040005040c800144002506006456000c03948681c4107000b801d000ba55044813034806440e103a007552001e0115440d28002108041d804801004510f10162108a0340d486003c41010200c0c2c08100c0d030303003407030784204401c4900741042844d4180e01001c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 88780315 1250 88779065 88779079
    0x611010f0b06040b071e080309070f050d0303110c0d031a010e09010902160f0f02090a0507170907051e0f100e0409020111061305010c21020d06050a0e010317070201050a0e 75
    0x42642d1103051411700081c1241d006502004110949c001080b00c0002000c0b001501c84da050701d000045281c95814140c00381c100354075410607039442100c0071300b280c240380c5142080703d4001001c0d074002070041c0b00c2e0561200a03800c0101c88880258400c1004051400000306502502e0b443e015003c8029032090014483c900c0001ca6020086010303160300d210310394020141400091030520400c818900020070307600609103000103018089030b008a18002420003003a4417046031b2180c18140c1c0c6085070755405190301504183d50b81c0c04840048885500d009810346801c0010100d50040214100480b02c0312400566540b0542043e403405804c0b0400d024010b040042580200c9202141080400c40e5003500f182044200041001000d10801449a50510745130058060045081f00b611106403e004c90541d0003203907402081620350320000080c4001004c2d507000b1a9034101c0d9280511003440107030381030018241c030111404054000c907100d07282d0580d98a45054006001510035445100f840b58004407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 88781565 1250 88780315 88780343
    0x120309060f020903031605010617030304050d050a050901030903050c0703060204050a050604080d0c0303090602031806071e0e042301060e030312010e0a0b130b090907150507030e06040611010f0b06040b07 89
    0x2b5205201c0c40c2c442c00c254081e5a981c642401c01c00c0c0b40600300e50065042010802442c48001da01006131440c505007442c0105408a80e82030445281c0a01010b09240780075070b200004c01c00009030300900840e10140c5110851139941c0d41048814081e1f84900d11894121002800301944a546014151480ba041c001000c50150700e803030040340c00031612800c440c00c41c500421781802d02003000650141300d41c5005c000302c021240d1716194099416000c003060089840016606946036048080e80c245a46d5140501c015514409080d4000a10402c0302041810f905041c007800c1c040102c4440f480e01d0341c2c0030328051f46001e030f120312054002031808103400c1d40d40c2008130007941ca40440310182034040c3c002040c042180c0040101248001c1d102c0d0b501d035444500108600e213004600c40483d072509042c240c0d01e0301c0080c20180c81301441c14442c01d51140000801140301a005030b0301d070940c1040ca00080058000000c043c004840c150089503a1060090204010400d40c8900030701c1035500c03c1e41c1c8160704030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 88782815 1250 88781565 88781579
    0x90607081902070b04020f0a0506040513090f0302070509090f07060c061409010b0f0d051507120c08011d0f0c090409080409021801080c090418120309060f0209030316050106 76
    0x103001854111424100c18042c04294134203d011840c503c07d0407683c00c102c1c14a450001a518825841510b014500c4242a0001c2c50804d0348080d40c81034020410203070605091400035220921401000c2c80b8026040c04107103a00740000d007038051300c08084010107015061000c161903060b46550b00f1540d0903125601e00c40c1c807011540300c0d01d0158103010004034040e00800c080020941e0228041c80c051000100c121000c55000035050b5031900d031040411300070380c0344d07598210303040c11101014643c81414001c0300e02029038080c1c4894101c0da100e0008220071110a401020104400d503403510a5440b110701040007000d55100915555200810000350082943d07101500c64025601104a0640c00b18181c2c0c00c180d514000c2c0b840074202460944868036004050340b410340550f030026805a60b980d81e11013103460400002084d02504440054028000510003c014109105088445030300709420341409280a0007950001c02009024504061042c000e8204103110b80006441c0d81d034035468005151 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 88784065 1250 88782815 88782817
    0x100908040b0a08060306220b060d05060112050d0801150f02070f171e0615030c04110901031406010f03050408090604060f02070f0303051803071e05090c03090607081902 74
    0xc045107031100ea0f1103103004020182403010041203500c0001c0a220a40c1413943e1100111216a602582940c0180c960038045036030603000040090007031042c4000407903240741a10f046000d0754402c80c05c5030f00c103035003c64003120000828840c1801890614003100300c030b00d000d11403800350204144111181141c0d01d000ca070440321907aa03c051000c010780e904024400c2c0c0144031000700d416031107a42d9031469a84101550307403090000d00c103103001500544500d031913a506000364610103a008000f031040c01d158000f0088a51b0180307407030501007883d0181c1c04005201c0b100455100b00e41c1611005507450402005a001d0540100110740c001d40802c45004113648880260001d890103940701c900c00f4401d20b41c0a880c085898000e103c10307500c40001000002c0d88032045405508203100f4224070700040501003031600c0c0c01c5412007420070036014140841024040711701d4045640407140e558072605d030f481007046a440142c0d24010f0030780100001482050190780201e401003044025542c24401c035032682c0040b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 88785315 1250 88784065 88784077
    0x190504050a0f02040f0311060309030a081b0a050306091e06010c05030408070e0103021305010f03060e1014190501140d020d05060a0f0501080102030603100c020c0909010c021e100908040b 82
    0xc9017800200510038032600801c03d03054510b00307864103440c40c182003005541ea03020b10700280c02041a6080040e000c951100d883c8060700c901004940c5e200c09880d0740191240c3c10440c1d91078020280000050300e14480c15444034800705000721403000e00d459040044030640c00300802036a480c4020040020041d9042001d42c3c0102004003600b546941944108011078030300d80d81c0f1082c5981014014440e2204032003d00040342e40c4600f00180c09868201d645041207110803c0c00c0b40b440c5004404100c04441d5014548076200038506000110f0b150003584040b150280503410102c03510004003440c5003010401161014002400321880407140d17a1114a03040044540070901c0e5282c0741940c505400600800e4090140b00d0020342c254030f4020046a81c84039100192600c0c19103d0441303000b114000d001c40300b400440940304c02481e191980080f4041c10254020300e00610401200103015400700c0d042e030007c94000d034064040d41c0e208501c0c031000b81c1f0200b0815552008104400203071401e1160051070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 88786565 1250 88785315 88785329
    0xc030b0727060807172d0702061009110304020405091905010e07060903030c2a0f0302090a0207020109140a0504020304120314010609260d021605190504050a0f0204 72
    0x21046040241c003d08450340a41300b4000d000c1c000c260b000f000c40440c502c566000320843d4403a04102a0b2810002d06c8007042c0020304d01c2201c980091103000da90100d40b40d07104c0d01c41c0200c0c00c0c207da80e403122070804580f140e9180d00452041400883d0041c074154100a81180c1c280c0d0031242010f0f0004079241c00d1408451041b51260b65440291400340014040c050042246080001c0880c0c07440d24040c000c65071041000f00341e200300310040c506825410360710710602c154103500244860707219011501c0400a60105038451403c490000d4003c4000f402110784855069584604183c900868000e41107068400c4550010341c158000c1013540b07580c4040c52049015000c012044140d4080240886000103040c0c0d078008100342c0144512900b04d040c020887c0d0702c17039044e455002c0d0041e44804891191140c003440b54040d01c075071a210643d0008840d4200c0340e000c860f0740341299031340c1c04121980040321900001d01c204400e04100510b0b16610541e40b00e81d02e403c000c15004d807c0012041243d00c150803481f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 88787815 1250 88786565 88786637
    0x80402040209120d090b030c0a0c050115080c01110c0a12081c020d0b030a17070c0f0602070f08070302010c060203062e020708060c030115110a05070905090a0c030b07 73
    0x105113958060310781001013001c0a0f04901d10f08151141034914451000086c0c02e01c0440c40318401000000d5002e80102c0408040581440e07448014664403007441d0780d18940000e2150220070145080030940c00c424801c0117216400c05481c18030540781c880c01102c420b40364070009000c8410240340c030b1080c40480c0c0141000c01a0707140c01c203241da10102c80006603c82d0080d400306451000040d940d0061007a030985c80200307981c4440325460a15080d5045130031100001c40c01c9140081c00c540c0010309901a664542a014040358480c5480c0342d0310590743c030000c2d002400100c03510000c40e000364021900810040c1010301c010281d80544ca0482c8090f204084100c4816a10040e2540c1d041c030520700a8808940900240d00301840c8203219400706025001015105800e025401c902803042003650b06c8103841500c0341c0d00c6440c1455900c6501078801c52040604040c0010504000440c850398680d81c00b0300c16011250850310b078080502002040c03001402624415504125001c0c0700010681d26500c0d034203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 88789065 1250 88787815 88787833
    0x140307021005070c030602030a1d0d090501230310090207050c010206010b0406080406050603010612060603120c030804060c02031b01091703040807060c0e060a0806120f070608040204020912 83
    0x405141c1c54041c08071030820400703000d020b00007200c2d40002e00480307402c0b030030142c1c80b034030380c002e40354001e1000f414840c00c1842a1b840405e0701100109124200604c95103455181a42d10001599035000c0100c00301c4010140e40c88101000110601440d000b140e4002200d0f045512881d8000032640321000039149548100c4a0309025a810888140501690486503051038a004170107004a240a4001008070362a03000003002a1000d60200300244040241080b10309068181fa07801000c3d28041a203548a219421410f05405071198000c1036506580d0f1103825540d640324070b00201404180c0300e0846c0002c200c0c40070100b5500600a400e51040b00000441c043c5900e002a2080066201c4d102c0b084810f00c00c2101190095055136116a0001d41c0424800240c40b4221544815a213582c2c0d403102d4049049010154440f0b241e0340b298400b40c4010140103148a50070307036940b15089007071040d0b81c006802880400c6c410354549030000c1c4090409820300c886080000e003008400741d4007541542c0f040c192 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 88790315 1250 88789065 88789069
    0x50f0d0e100501091a011b0218040b0705040e1812040803040906080a0317090106030c12030f0206090c0f010c120302030f150102030412151d0d09050a050d05070314030702 75
    0xb00c07801800b2440042185503050850142c1032080f00601c18140031082c214001d40d6a9056015100e031a4000c060703da00001040b50744034005030555050310100074000018440c0da02501c00c031010341c0e2182d044031059580d25401001845d00b5038042d0f5003180a44000400d00c1c00c0914050300180dca42c00c05962541d0803c00c03100b0845003142d001c1e83e8681d00c01001000800d400815243c1c1200c42491094420b0380c1c0c4410300c80c090001e5500050148004100028040d00c42c036032905c0081c0e00c00d55030340220348002e2404994803079013640d100c02d56401140c0e5800880c43c02400a8070380c140b0605106d01440c0003512036581c420307060092100031a800000704804101c0480c1015403040304940c1c05000090360300b0000795640200e00030f1014001441041b60b05001800b0406407140c4401d1000f405010103800440014100016241080e4403441d0380602d407050003031070100107842e0058000030849191200b006803020300641d040c0c0300d03402203a101001180440e14031034008001e2400a556400080c41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 88791565 1250 88790315 88790321
    0x1202010b01031406120717030d0f020a09150c021e030d021507050d060b130302040c050f161103060403020706080609073603111212040303050f0d0e10 66
    0x28010704040c03401012012159150301c90329088402918080341940014850b549003941640041c150140103410512030b900d0000001e0a60070300000c0c0c10b201e110214280402640641074500011444486007032000f9100d00ca411511002146844a01c40300b007500480c41c645085040080d0a00340a10655590304042141c24865000c0317100038850000d40585510340c1c86402f0b02031030208a80019280548078094101a000c1c2c0310079801703075640d10090000c0010301d0407140300803401582010404c50259005a040d200f55010b421450b61400900e1100004030040920048540b54854100c5101070785040003110300c514442e4000300b2016043c104090114400104101c2c8501500420400d84039400791441ca040308040c1c640304c1c84415164085415219002180d10f05442016000802d21045002e201a103542c10354055003240e20a45503039444915141c0030b001000e13010042040064403440c010f0103d506525030950034002a829040191240d005001100f48d005080900350614288 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 88792815 1250 88791565 88791581
    0x9031b031106161e0212040602010e01060b0301080a0b1308030f01090b0d020105160c080d02030a0806040606050a050f04050402070b0a0b0d0507050d03050409050f040c0b09010206062704120201 85
    0x40395241c03d141e80070004141c01c1c01c0f190305210350212404082d10f90b074020046440480000c820094503192500002802020110b44401040d801e010000a5250514084034165030075040948001c2c8040d07116900d9150b000741c40800c03081240c440b100007142848000d1760194181200011255140040d00c0094600c80782c0604d110300d0b1229050340050303801c00115020301c1d44102800d460036501d400d005800000c2e41e842002940103907240103841c1a804001032101c104140c4601400343c40d00010f20003112414003940c008074604001c1001c0560003071024040380b0902d440702500c0c0c2910b03000400c061f600203160440d24a6072190070300c6038640050003241424030701900d0007043c681c0c080d100c80c0d907125400e104081c0203041e4154214149803190701150b014051500c801d0042d424454a440643c030300403641503a020307101c1680415a124440308840b00000140c4c024100c0d92210020410041500c0000000040684664032a0784075481d00d07441c40740f40500700c1103a46031360000e006800e481c081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 88794065 1250 88792815 88792831
    0x20f0106060c0f0809100905040e0601080703060b0604080a03030c1202270f06030438280c09170c09040b040203010b0306130204110a020c0409031b031106 68
    0xd2000d018040c2c0c061000500903400008110564400381400c0480d4882d005800e84c11882c170003880c1044640004481080301ea0a40d4200700400115481548a00c402c2c09411001d4000e11400c0010907885d42140000450003004c003444c082e81c948500d450030458045c00c4010030748071031a007411070b80c00c10002c2000d100c0a02040d440c00b03201900d010902105291245074100c0ca441d040340c1d03681c5503080078030302c40400500b1081c4d50381081c0c1420000d01c0103182900c4004101c6065041241111071007803040780211281264144c0c41c0c200700c480c0708100302010801500d81140b901e1111044a000d025001440c54131128a0ba07070030540003c414011611f5540d01d59842807030740c504d40e82c4078650080e82c400d4001389680c842e901d55200190152441d00141941482000f00784a0b101c3e41251010300014803c0354104010802070f00201e89900072443c80c0c00160700b00041c1d010450500783c1250a03680d00c24070b007200105090b43c952031705040c580f400950002c0c036641c0149181003000c021381a048401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 88795315 1250 88794065 88794071
    0x6040603030e040e01020f0d05010f080102121513050103080910050c0709050a020705030a08070f08040b0402060703030e03040b040305150c040302060c1005010e0a051305120a0e04060b0406020f01 86
    0x45460103030030381503121991401140d40700c0c3c520444c0042981510340204003120140d5540701245560806000d0130b000d502d08020711440005184a4140308a424007071600901308501d81d2000207a01c0c1801c0e00800b065004201940400c43d04100c0b4410180658458410700c1c1d1900210014080552058150f10061000400000d511803800251580c200c2d088207030003252035903505480c64042d02840c0c40c010070910022a4074050541c001c61a24032a14213980e62038140381e06410304540300c0f40251005040c032171400e00828054201030000705400c50103030030041f40c0104205001c42c556401036111903000a0b0104050041040c00e100200d0202d0364103950140030f04203820f8401c080d03c80c80c400284160b10000c1d440c020101c00340320a132000d14482c80c1c200400e40e9208917281011104130f4100213928a42000108841c1904403101881c43c0c00200510001c50141c407050150340c030241443c018055040c54949990381c840c01440058504400c2c055112841d0a1010746003406d250a101a5a41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 88796565 1250 88795315 88795319
    0x2100c030f0c080603120c03070c0324150e04110d050f1204030507091e06031b05040e0718060302030a1a07080f06010309021305041a07020c0f040e010e06090d08060406 74
    0x2030009500742d01e0042c0317007038101d0b03030b808411f0b01c290300d5849500c034010f010b258001000014095502c10300700d889860164078414001556086504a80c0200c0442d002102a41c2050054500c154180c2e548103100e46443e61041024400103050541c40c0310707080703c42d40d010000005065405200d0200705a00c0c64444030708050031035440b25284d02840c0600c02005684d100040300c818000201e40c1c1a81d454018100442610b908101811501034514400b00c4c502980c3e0014282c01c1a00c5901a020707107480140c0025814142c87c00c0c3c00794000014480715548a070000b0000d40c1d014819400c0d80e611604000c07601c0c000710042900800f60041c44d088c20300c00f80700d0400400e40c0c4501147e56104400f440d00140f51070b091710000383c41c0e4120406071032420303142c20100401c1125182c5401c94400c2a1762801c6c04507076940c18100da130364040c0d200441d008500c001e908515070138644c00084400030041c001040303c13014080460310b4100d045806480550000d02d040384c1079500b00b601d090300004113440500c807481c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 88797815 1250 88796565 88796569
    0x30a020109030b060102160e01050906150a0e040605120f010b01110d050f0417030306030c030106060f05070204060506030420010c08070308180102030106020d02070510080c03040302100c030f0c0806 87
    0xc21030740310103003c0303914000001c0c4290b031090000c1d03003050b80380100c02030095449100e0609000300c00d008103400703000c43e84c010a1003447c1002c225860f072540122035904e08103c9010440707072000c2c040d0059800c25111200410b2999803141e4540b54041800c0081141450b0300c11080e081d9035200581c241031007102064440c200101040d104500961424a6a540c554207010010709100340d5021500f102007428100600c010b0110003107000b01c0044085498040341002058200d0300c00c1e01c212808166820700ca00603070b0f80140702908400d80001e01c0001d26603943d4006c40e03195481141c0450307143c5025000f01900004004421000c1102880c10031074120042d555094184a04203028041c00011400a40032100c152501d03c5010b209200a544a50351000080c5d03940444001900c050b000343c0c1408a00c5084c00c200c1e1a5007182c803a42c8a01c22038a0300c0b003071b0201c66031002d4001c0d0214040d804002c40904558040c0c41030b441c81c195400194014200c40c3c0300102d03075510904030100300d4503c0a110607a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 88799065 1250 88797815 88797827
    0x4020f18190b070f1232031501020a1202011d0303010311060c030c07080321060303040303030905070f12020406060309120302030928030305090d020a0f15020d0504020f030a0201 78
    0x55600c2d00040d03696590103091900002034040401001c496110300a00d6a040d0300c00d501c0310264002c0c01c41200303098801112461902400040341d180b024003807000403000783e10030001c13003e0140d060050700e642001d80d86991340780b03520050054015030f4685c1989583d040641d80100035202c8500040c5040d941586d80f440140c002840709544901e00208400a050506008503040f0326101001c0342c012035503400225481c0e0304a800e0394603221031406440c0c0919005807004070b01c27824000300a103182508540d82179000b0151101c0a982c1c0c0d01c122100802c1c52000c440c1a2400307410510041c1030640424410007040d54a90381141c0704042c100194030000900c8038613400400003481c200941c4a5980300c5005107481540b9405200320f0405403c2e4400700520f0a4404a0380350003070f6801c1c441031391000b0b03015a903041c0303039500140184d1007000303ca00410848494200d60903c50302c1c0b000c00048404000506070382000c4010780e15247d560f0203020031031030426900007046500740c01030640707e102500083c00c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 88800315 1250 88799065 88799069
    0x1090303140f0408100f0b0604030c030f060e1209040f0207050c0906040e0a1b080613080a03060b03150a140112020304060209030a03110609060609041b0504020f1819 73
    0x440100b4103441d5200d0030030a0318007510040e41140d1110340700581c44400350a0301590310301c030036107044021040340c141482214256a003080383e0030905403840d91500c800c010107010a894241d9507103514103441170700f409003142021500316031030340340c01c00ca41c104000c540048001c1c842c103034230402082c000644045942814010201d45400c0c81e40c0d00d1001040c0604aa50040b071914024102c0103010018503030312443d455000c9050780c040003505c1d10b5580d66901d0f0103a41c00518a07042e40d103403900082c00c500050542002600d00866819600c0b00740d000a03400556004081840e048000c1e01c140c00c020b1041c2e4000c01c414407640c02c6107406240041c000e1070100c4205001d65400200080900c207864040700c5c0310f410040d00322141d0240c01d082c02010b623070346146946034a00941e80410720700c5a0025030365001d503000812800381c0e03841d65581c0030110f071081703070b104401c0006803180014156114170107004103801c111402ca82d24040c580441880c2d005041c030b00382c46a101084c5903003202000e000000b003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 88801565 1250 88800315 88800347
    0x3070b090d050a0909151509060e0613030b0c120112051005010608060d031103161a010305060609091c050c010b090c040905040f080c010b01030c020f060a0c090305060114090601090303 81
    0x34406c145c244104030520b0094000b00490341071501e11003042c9511002503401c0320041e5882441d0348440d00200403071031154200b251003c0c1c1a018090003ca0401403030325400c01e440a900618012a400100d00301d194240c1c0900703400003101d200c1800f44242404040c1600c0f01c40001002158144070001c1d01c040780107465513014000500c2000105401001f09250802c0a041201e031903041507106004104100c0f40700300c84e80c88070002800d100140c0341d40440e05990703200001e82101e5907100140701f80702c00000c040c1e0a40e845403002034655086502c6080c3c1080000b59605943c9003e141d07406800c0d5103c4480580c0a8640038003041446090780054405448400001180b50340b2542081c183d4025060303005401c00c0d00008900b100e0010540c030850001c2c20a0701c080c800390050902c184d0b10b841084840140c2d80d045400002c4480d00d4640c0411048199030078000201c41e100c0d110179180801c01d8200392041c00c20005410003a140420905d94040310902e8050b080d1415654000c0c021040d17983c07064 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 88802815 1250 88801565 88801571
    0x7020d020616050c070e0403030605030313030f08070b0a0f0c020a020901030213060e1315050f06040b010909020a0203040e0c0307051b0a02180f2409150303070b090d050a0909 77
    0x288114403403c02c130307410800494111a1080e8403160207808403903003513a040f008245031501c00195400d02005603664500201c0f03600d1030b014a5601d80e00003400d82070310110785a00040110030002400342c00000c0c0a00c51111000944075000c90a050407560001c21a50955204081003401030f80c0b03031200c0506580c0c1c1a295000c1350b0244005e800040c0039642c104900038050360040107244070210f4101082240107a16545000c3d1204115808035181030303981c454041d42c1c10000134101c3c00c2ca504032860040040c5480171405d50355540310001c980008855000603000018200010488030030020b4110103028a180c0c994200400c0240051048401c03001c4101c1d0303d207008101c146014007201000540141200b81c0c02d4044002643c2c00c28802c0350585a640500000300703015030140c1d0514010070302850221400f5118950400c81c20482c010300302c0308040580d084070007080c0c03030500190940a1051007070b0f000c01d0608050280c00e0040320380c036500c02c000e8240038219813594070403840f200f140e070201c02c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 88804065 1250 88802815 88802851
    0xe130b0307050f0a0e010303050c060f0c04140d05030a0c05010515090f040c120b220c0512010b04090b0906010e061804080705060403050a0906031a19080703080d0507020d0206 77
    0x21a1380400a82d0041c0000c05081c40004103068108006040703c0da600d0003a00e86958500440d03804020058030103101d8100184014000b0708032a265000405100070120942e07441541d0b07030103285511600c281c0c000140301017a0242001002d001300c40d001071745481c20b01d8807078035540301040a0140003010042c800d00e00f07001080c18803203221250005003840419a954070340c03260800c104001301c107844e00e201c55900030000c4c2c501003240c40400091743e5030041f0003042591902e0104101c502074007209250ba950f9805011409946a01c12660143d11945040740c01e448c0c500c1c1043d061260590000402007440007c0245a64034010060004849080c0c03284c80ba450b40d00385604d0368082c48900a0480c8118000e11080c980c20034080c00322500c041d501d00410355129401201903440c201c40c01d1a0712800d15006401903e41400082700450300e41c8043d0700d5044d41c0f642c1103454840707182e0042d21881300000b00068600c81c1402640d900c560b0500082c10081000200259249001808941d04c1111050b80c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 88805315 1250 88804065 88804069
    0x3060c09150a0f0e100f030e070e090a0201030c080103350310050a0b0723010b060406030608010506041404030c0312090b092b030207110a060e130b0307050f 69
    0x1001030040c1c0c02603191030b2100ba031240c01400e108050300000d404036058564090301840d003000d10501920b00b507610854a444110340c00e402038108004200101d0281800c04540d030780d00040100d10900c900c00043c841c400f5140000350480b40d4000303904040025400052000c582681144070025001d1101e040c004505200600c90042e000c01513010038620000910003040300b08080d04090342c0081360380e48034003592034101542c0e51140c2e10000f4440f40141c501d00c43c8030000710721a40e1900300004008514001c1c5140040d82560240c2c01c00b0000c65078070301c03040c00000e4003441341e581d0200040d50200540c45076100d240010302d40c010001000c010f4030040880806101c0da2111584428440050250011914001040000403107007480c40348906000304490f10340c40006941240d00380c29540a0900c00a00b003140079600c0600c054404040c00c1410b04096100c0c600d80344010100e55680e9007100441404114041000f40c926030b071380600f0003e00180b1a600447e1510480360210b038404078400728400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 88806565 1250 88805315 88805329
    0x90210050304020a060201020c0d110a05070f090f05040f02060a020c040f020409050903130302010c1127070201060f150c060914121603080604020c060108070f06050903060c09 77
    0x942190225000166464001000e03500a602c2215018801501d81c00200c0c01c03401613030000303001580445031790341046028070704c0348a84152103000d842c1090a903840342d0340341c00c0503a4842d0490001c80d64040099000c14490300c101c0503000b45041c4110304241d168203007808807a4002911030000000c05182d01402000394006115002c2d2082c40303aa42e059641e04025001480384900c12810800003a081d410084200d5502c800d02c18034403041c03541507400460707182240001c1283d0b0420060076181c03171640c816400c4184507a2289510880302c80744c01d00c3d542c4070040074080900350ba05088080c46041d10180c4000180c980100c084046c0400c000000c0711480c4006101420309450099214140140302090509106128040b20880440008250a64401c0c5507040c5100b440780640080068410105140c201030010805410011141041e03410300d0400e0344001c03115880041e01b00400b40010580d00010001801c01c0c42c28400325601103905c401000701070004c04c0d140020400c0c11542c48e50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 88807815 1250 88806565 88806581
    0x8060112020d06030302160915031202030c1603290c090a0f0b03161803020402070311010e01270b010e10080307080a1407031d011b03050301051e061b01 67
    0x41000d0000698070306019491f803e01030740c1c2104000405001086446080c003c140240601c0c4605112107440c1da240c0107031940741c5500400071800100003191b9500300c200000015400d2404003d04018614580b00120300030714251030451503014024414a01c026080030760340900760752062a55041c60000264006005070490031000350202008900710b034070400511b1181d5400c00788480880490081901d824100200c00140c80c240b0300000d100608060b005400e10b070344281003001230103e4031552903080d2915504200c495030754030b07080307a40102400511407018000d06240d001480b104c5444070680501c05004545040c051030740807a040110140302e440040006100f0b90340ca4018525200046600c075001c0c580004804c22285606141c902044488899060b181e0030505403002d00100700740b500450420b418403401840550740c00164940722644580319681c2c60796298148010000b1041520506000da41c1d50100400c1c2d00391a0f03082140e4000501541c0445140d06e82c1c00d205015045403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 88809065 1250 88807815 88807837
    0x21507030201090501060b0702100c020a03080f030a05010902130911040504020403051006080d0905010c02010c241103060a0303080907030c06051b0a03090512100c0c0209070e010806011202 83
    0x812405155041d8005110b2130700c030300024013609030394003580d041034042c00402070350000c1a882a00c41c0c040c0180700302e0f48100c1c030161080c00c15607501c0d119882c0c2504215a5406040400420880c100c2d0442c80703141d02401884030304504004000300310809452060283e103054a030f0340e400807221820386e181600c004010080c41903513640d031170740307880358407000c060300c070040740d142090342c04900040003040d6000c074038603940e0b51a4291460000111400c125601d01641800350841910340031856015490900d105042422a247c42c44006890210b64030009411a124070910074001e0070740e030f50b124607800c03a901031401c1035581d00e0791001076003407504551004010401003000050016042000351109201206c408031800c0c0a00f00b90948503040000010002003a21030148000c0c50281203010101c16842e040302c0c415900c5c1200041202c802d03c080c0030101d54801c1d04c0d40118a01110000e134005414504036100f40740010020781a0940942910306021107200300050000c0643c0c15604d1002c20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 88810315 1250 88809065 88809067
    0x30603050f0703050f06070512070509100906020d03050408030c09060c010501080a020907051e0c0a150501030b06061801080c0c24070e0a03020d03030b06030103031206090e0d08040215 81
    0x1e44211954440c0544070407580d50085002d4a40b1a4002013007907031040e166611001c0c50082c1c200b503001070815008001d4014400d00340203050b0107803207410302400902d980780c545100043c20200f0281c0b81244d82000f0704d0400d0b05002c05c001c0003844d04400d40350040b1541c91102e0719500c00c0070010b18140074213007200f066503281c07000000300ca400020b207040da404c0c001d1343c40c10055110020100c038244200720380715a02402100741c52080104401c0105600388181e03081d9200b4924030b0350b40c89610b840f00c29010850f61b4944005005010708141800c3e005181200d03407610700520280c1c4003200d00c031552421340c1444107440004441d0700d0307043c0c00c880008491800b6a0044130544010114003420841c00540300f0240400007802e80340144031854003a140240071039000b610f90750800156038139801c02141056110240100320303480e6030001c2c50195110b52901c040300f12130014403c041364000d6108400c02030800442c0c02e9000310104480d6140c1c0003d1500c1c42c0f070b654031030000c281042c0e40710144006101c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 88811565 1250 88810315 88810333
    0x9050901110d0b280501030b10021b03071205010b0406080102040509040b0a0207080a0c030f0306120b0925091401050906010c050c09010902120f07050f0711060301090902040b15041503060305 84
    0x144c188490803c1e10001d89040006a2521060203d154011604200583c1c803000003c3d04081d0a54060125007600a0480d00c030b194a0305940d182d41085800c007102c55030745a141e041407030718190260301e0182144000850416282c94005003042a001d80094086507503400400c6012038a901101c0e04076801685255444e0340c07800c4010820717908c074942076002a40c0c0c61002059a442070040c0003c607401c1c84c21003406d286c840d46844000f1040a03010702d03005e10500d1902e6500d6058a4001c5a40351115020145c3c0396182030808001d83e5000c000c070740b4404100b1001071003142d440c201d020360130410a213170454424100d80390180c503205089014907031140e442400000d03ea035040c1c00034042681c1c020030740c000d01d482c5c04441650301502905e4a0001c82c1d002c0c080d0500e00d008120242c801f4602a5110f100010308030408110941c0c8282c001c2c1100e203444a414400794200b60240740e0340f090b800c0d06c1203801520903007003604850095028501d95003410b0400310104900c40d07048600919082410f41d0b41c050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 88812815 1250 88811565 88811629
    0xa0309061107052104090b04021c06050307060203031b1803120409060905090a0b091501150915080105010e030f1207050c031c050a140a02010609050901110d0b 70
    0x20700a00c0307040300c051180d040a0801030380e09118080c8080f0008603085c0c102410002000301030025201d010303070080d07802c0c0840c07003010b4091690070800305890400014500d0801007410708222150700038a017590710400502408855507004071840c2c442c0004920380307824003032908200103d90b40031510707030611820f0340250721015500028022142a110204440d9654860304001e0f20400c40724403c1a030425000680460040c0c40c1b180d83c040700c4d48041c0d860740c0c100035200070a030100a030885880041c2100c1c10010850300505980c01800075090070304942130380e03850b00410304501400381c20f04108160b506030806881c20400d0070f075198100030907a0031001d14002c20f0f200c25002103c06903118401c05490704400e00700444d1424041e0140840e200105039924800c0c2c400e0307441210b40d0410071069466100610442101510b074080c6107500100c4c00034505040d644c140c450140c085603541e40b40101c80081000b10208072031030b06907040d401050024681e800075103451860403030410101001c9000c0140c40c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 88814065 1250 88812815 88812817
    0x90906050a0b0d03021507030e030301080708010c03020405220204081b13050403052508030405010c0f08190e100c020a15060501051206150f0a080c030402060f0a03090611 75
    0x14800c007101000041030301d00400c2206007203030101401507040b802d203201c41d4080f0400a5031740400142004240001c2145102c3d140d6403003640650700d0b035000200c05014060007030082800c1841c071480c06608090030705c80014208002e014140b468041d448980510707802064060b030340145401030940c0e1504000f100d130501032044480410344035080ca10007580700850140f041c90f0042c2e81580d1854102101e8210404040710322055a41800f20f14030960800642c207080194401e80c424000442e07000c540c1340c8003604802c0142004014007800008000001001c0d82e81184130000d05500414003201040750181041c02c04415141194102120b0002071600040c43e04041d91160207003060030303980d20110f00200e8840d8018140001c0d410040502407040d400c00d1540c0021008004407014018050348141c5a408000710562000d00030038480502ea4000ca0320690200c50540c400381346150a0f40081c5c8603101d10301c50050405004150307504014030130790140440907405003081103004280c490b21411 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 88815315 1250 88814065 88814071
    0x3150a060c1b030305030f04050f121206030c100e1813050d020c1e03030d060f2102030604020d0507030b04050703060623040203060103090c0f0821030411010909090605 74
    0x40d5928055403500711201c1d4418032003c598050b911a0b04544a00301000307812400076005540030311440b212010103510078010b01840d050a5042190360b188140c41400701d2080003030600d031083d0404d442059a94072004000c0861042504c3e1003503080d0b0004001590f54130b130400c0554805804036040080c400701105a02c1c00050141e011110101308410040782d4400010b80d0a80c0c02005801241c803010100032104000018002e0a480c204200031102c10308407006503000090708030202604008811403101c014000700e04540c0ae400c883d110ba40c0100741d85c2c8001900081c0151307a030350b00c4130003400070a004510107503500090345aa1030400c1e0070319903903940103404165550383ca031410000c1c1500508c0c5004103045101c01003c104c583c810000c1000a410003071900b418075840d083d03540c00084201613030038050440d2280c0d42081d9820702055910f07044000004000c0406680c60004030600c10341d050302d6020758401240365000d1081001240c48101e190b00c850072035414103500c078042040c1034205c284 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 88816565 1250 88815315 88815323
    0x10e030a180312120204080d09050a090b0d080306120604030806040f0c08040f060e01090f050607030c050409020706060905090a1403090a0306020912120d0b0a0f060503150a060c 78
    0x4015001e9204400744500a4400240842c10a000e6014414000d1071030140302c0f18021001810969102c0150342003900d840b1415000885500d030510991801d8071103400030301a14030080002c800403030041076040010400c08ec4c03001c400423002030781036503490284c2d02400c0c1501042c2c4015003454500648014020340c0c525200c3ea040c0400000042da05228407415079034166500405626a9101d900060340180001c1d40c1e860384642d590080704c102401a040e400340314151000602d01541049414118041c042108040c00c1ca400309610b60740c0082940e0955908103001a43e45030b080c54a6002800f940e4080c0842071300340801c03c070300c40002080805880b40615808503580c13000f680b12030b4072489690900c030b0340b02c1c100e1002030001c643d0382c0e03018004204019004200301d014201d0002d01d0301c0c07941c01c1036040034400011300008035041e40c01000c40041041d01c814010506000700c58111068a0082400f005008000a03e4903064881000f02c4188090802c0543e980c03514030042490740400001e403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 88817815 1250 88816565 88816577
    0xc0c0a0308190504020114030a06030209090d080c03010e040210050d14150a030b07030c0311190908120702010f03090b0a02030703060608040203061b0705061006030608010207020a0e07050408010e030a 88
    0xc4650310305020f070781c1c481c0d607050359540d045403c1e11141540c29040581a403018507a286004001170700d84008075030098503000b00816070340300701520013014610001c14468030300400380b004111204003840c84030340080d0f046681201c44140d10204a0306809001d00020300d943c04c10004120149074090300500850500c444940c041c1c800400b4001040d01511006080f1806900000e000600c02c1e0b0003080c03c50b440303250102d0010010000744e0000e40002d200c03080344a0001c1c945100858000036048001c0039000c000d003a0040400c0e0030000d55000d00e100103810310224842000b2a1031182d400094420340c0803032407201d0b600f04031600c00003e400c12140c40300441c3c640400803648c107005800700303440340e50300070300618456035940003201070342903140e0754485420018040d41002503003c2c0f1049101d81c100c200ca403001d8502e04400181941c0a5511a480300d034410042840581c4440c640c00d01a180c940d41c5c0ba1050352540041145c8034403e590000c10954603040300e11510b41d402000500c23401050355160 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 88819065 1250 88817815 88817851
    0x61503020f090f060108060d14010b0108010509010803030106080c09030a05100f150909050703120206061005040305030a03050712060f080c01030618090203030d0c02012406170c0c0a0308 82
    0x12000b141420703a204081e009a180000d202984145506507121034080d200c1c26020b1040d55418108041c00c0d00c2604850b512900c515050f560b10080d900d0050000302ca5032403455240501d0740d0340f04c2c401805018200400c1d00c00040c00308103450204d40c006a0003034216142d0a5043c20855181e021001511034124140003d0840031041802240100f0b120003200c0a6050302e00b601c07040c010001662b04840c2030250800003c0803808800701c22005d500d2940151041d07250000030003e514414001d01c0c0c050010034081440400c0c1c001041d6082e041c43e60900141c20344890000ba60800030001c0104000c0d401c000b80861460309034a400400c891350705084418140050380150281c3d65940200e039054484940c1c0b403c01411340c4e030450310710540041d054a1800007000703d0384003030b540d1011008000d41e444110303140d400c42900d804088a142200d12481d50386080100040858807601510700c940c843d00ca0203c0c0c96041910200c40c414840001150110155880c001d01441c40803115202c07000c40089030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 88820315 1250 88819065 88819069
    0x60e150c0d0f020c07091e1401030507090614040e010605030f01060807170d142a0f0a02101805090a050106110c060412080c0703030203220f0b0c0a061503020f 70
    0xb5102d03c0084c0c00003038454079041030340e0701d00100780c4207010b07400010105407a9558801c040c13081500711002d14003902d00b19811410300602d00500c56024801e620701d030030406c01c440f20360032542402c8141d00320f502050600881745114003401c42c54200c142c0c180aa41c0302881100c02c1584040100d0314144140c2e00710554421444c600002403130307000715039504040c9160804a2150b4200441018400040f82c00c2451f9004421445c0e18000102201c0442d01c83c3d41103c0c1070320802018541c401d16174000c020031121940410b88080d090071891080c0b10b00103070703000d1030243c114542c00c0c00380c6000f500c030b901c481c5000040c02c00600000e21902c804240c1c60740c03880400c1030b004224041c81c03000160041d442c103072400101541d4440742c0c03001505d41c03032804e02000101d810180054402940680e00540c1c840d00601103000e01c03141d01c02c1c400210384030700000c00c110701034074004254101c07510350102e40d0b03e40d51926007603401c004030042e0052107245000c5150740c05844a04480090364001e80f01503201c1105002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 88821565 1250 88820315 88820317
    0xe06040f0911091e04030906090b03040f0b1302030307050115060824011e03050601090501050c1c11030304051b01050a0e0f0102010612080301090510060c060e150c0d0f02 75
    0x21001c0d01151401103090914103014040940000c0071620701150343d000710048189881e070a0b1740440000700c49503402c00480da48020b0130805881000e07401c51460500303a0350380e0140c0f4070300b4a0080c4680352601c00201c0050360003200040e200e4001e402c0d6a0b4450481c6801030007000d030865900d05015107014089100b40c811603180748608444a500c854002892030781641c0c50300e0b0311400c1030420030780c5040040005807041089590100985000c200e0381040400501809403540045c0c5c104101449803a841a0780082e6941e407000c0d010b42c0d000801520800c0c02c544042c9401a02170b22444004180010004000388a02d854141c0040d0449803255009c01151144600440b080000301d44035144c1d9034518020b408890310b40c00500002640359030b1000c20403030001064205841c0c64070040300402c442c070700ca405a02e038000500079041c081d160900d4409071245414400c040c0c40184c0d1010164810541040941454900030004c0205131030301c2100300c1e9660b030010140840c007604205d804440389540740 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 88822815 1250 88821565 88821581
    0x21308060c0a020a030c02041506030c03051b070b1b0c0a0c060201020f040905070903020a09060503010515010203032a070c03050d022a0604031a01081c02030406120f05010e06040f 79
    0x540a4138281d4071903241217034480c16030f14040e0b0380907940b40382105085480840b82401400d05841c045640c5140340006070440c0e20083c11a008500040b2000c4a07a403200c000315440150300450650984e00d4240c1480b8a07141007800030808010001121640001c000940e5814280300b84408501d00791915030890a0380a841108401c480c018031043c0302c0381c0c0054202a030300071494a0561141d375541c3d000144501100d6204011550741c0d80424811801c081c0a00e0303134008100f01e0029180250f08000030b5903031000400c207150780c0c11500c2c0d0303030446500001141004c10044a20594945d0744609001500d2030303003031204680c584074400613002514000303e5496106a00d201c000802ca10040c0003060418000c1040203038801401c20010001a8042512101c0001c041044402560402c1d40080c43c14011004003000003070f00c10950489903900104990903541246004032640c032140354400003a01c00400c0c882681401c0400100d90a2070704640580b041200f110180701001c410b0115004440e614 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 88824065 1250 88822815 88822817
    0xf0c08120405041d010524030604080a0e010903060f0506100c020a09020306041424010215012c0406090204051501051e1306050405180c090d05030409021308060c0a 72
    0x6101c20031007403a0607030140d0b005240000f070f03055018140501441c2124004c40343c0003075969200c81c00001e20b6810080b2244140c00990062a0500341510348003c0c5004102d591000c000e00f074139902c44180d100302035040041d81d005205001600310b4541c0744c0003800e021549540a0b1451580d020760b0710740709049500096401615101c0000d040c030341c00f1000703907000900c0f083d000781d22a0b11100d11500041300d030920a820049502840c4070b040a85076a1050014103850304542c00641908010f002c41580309046484520311a0700c4da5940c0240340700c0200d416800d80c0a1000c4000802081c03180039000502c19070b100b00c40800c0207940700c42809c031144408110701c900240040c40400b03011b1041409041c0d0701520007074039a0030700c032440d0221054003005411080008030301140c10403460802e00c045141b0f02420320404031042c90005c03c0b1100a0007090301d268883c40c40c0006403010b100c8140202c80143ca0510010755968200c130103101007945940c8102540d5206510006020100b54015202c0104107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 88825315 1250 88824065 88824067
    0x6080a05060f0708061806010e0d05060406061505180f10050c06100f06080604060801020a050d0e0304060c0f0f0501060b0a020c0301050103020108060108040516060c03030f05010303050307030c0e0a030f0c0812 92
    0x45100c6e021031030000201854113110740c255040c003869559400441000384150002c00280c90903207004420307034140340d008801105145c4114842c2c50703044401d4a4140781d4420b0000b80300f00c6200c0004840a9102c200d1607000251820485c81c060b9014009109070106001112680d81b500410059503921a00c141c0c0448800c44000380310300b51042051a0701300500500c041011a00c0340082130880c4d11410380c000c0810341c00103071049030440c14011030405940d060302031803e043c50706602500e00e9400841c002c1948810300b5002c010040c0b905040e16030550000d008000d445e44518041031940c4c00f80b14003c01510071032400b000980b0301402860b043e02d41c10f0303407030301c01c0764842400544402c030001e4011141405580a4548021049501c203401030040741e071810314030000c80c01c0190407140c0144070700d1945030401c40148086604202101e400c10328030f00c0c0000e1040c400081c101e81c2e4040003440c0c15030042c540c03240003081c00000d1041640041c044d2000d070460380e99400e6540e0340d61003c1c00c0c0c04045044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 88826565 1250 88825315 88825339
    0xd1110080705040b0a02030c030a030e070b0301080a020919051f0f1404020a050f22050306092a03010e0703170316050d0609020313050115030302060a0203090106080a05060f070806 79
    0x1d0350117000140c585d40122800e010000c441d41d8110b80011608800080c1d50300c00d118a1a03504110307100c01404002549883d40d410482e0766500c4030300f0090041c6c050f41c261800310f090804142014060f004603110100028140700c4940c10f403414103c1604031114111481c04240303c800b901c0280200c0c0c4128200303040d0100c003401400007a420241c0c030a428403500307208250010314600020003200700d0110001301d11400c6010f4100c0c060b203980d04402d000b0ba01038002c120620400007508140b4107211030140071582809002c0c0300d51000d00c030845a4155003480070003000c41500260301d000f900d01c03c907050941c99a420700c1c58140c034001254a034100501230701010300468001c3c40106840c04c122240862026203802d41c4200fa80d00544542898050310000903023032000c02e200b0b80c40c0c0c1115400c480314083c4d15540b0025960b0700007501c41e10542ea4000003144041100b540000028901e5100707540082c80e0b1410b103141c0303504084a00080340c441800024422500c0703111481d00c1000c1c02885148503030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 88827815 1250 88826565 88826579
    0x50c01020615131a09040605011509080c0d020a0812070b090c01020613050a060c020f0d05030c181f0f0e090606030112050c0303190e03010b0f0904030c020d111008070504 75
    0x1032441c0c542031003482c1031004c1c25010348601080f46d1082d80608404609545000a401014440c2c402a1803c0100700c84081c06201d0011426121000040790503103039000b2140001803204c403d680c0500d40303511916119109410062000d0002580101003010a031b0365080c52280c0c851a0b8500b01900580210002440300030410210580751809202100c0f0303c4002682d07030400b00c0c1e903110070907009a0312000ca4040c03140b200f04030b00c900c0718072070b4a800303815410708a180d00080d02400d004d10098661480c485007851321814442149400508410f42c4032528000c030240a801ca18081c4100045044548020070b041c02d1368241d005070b00c0030700410b02e542c0c68448204ca001c00f02c8841210396002c0c80030261069038041000d40440c40749401ca2060344458800c010b442895401c8020740030382d0520300c48225a13954020326101102007614544200c0e0b139030f0300d07040340c900c0941d0100030741c0881241000030030f00c96405050100038405035050808040f50401c02c1ea84107208580e20000100200018043c107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 88829065 1250 88827815 88827821
    0xc03030605041802090a11070303090519050c0609010210140613020a080a0209030109050714041416180305011a0f030c0d110a0f03060f1410050d150504050c0102061513 74
    0xa0306c001000400405040c0c00c0d6445034020071050740041c0c3c9520b400d00c01e014007407228541c0c1d00442c05280645080f5a41c071552500140c3c00c0d460310804004c0f4074a07007264024040e40d80d5680c0d14050030001d0030300a9040e1404c109040c0d407030303d002d101c5130203042003400320a01c01c49100303038819112200507589280c50407000c0e601646070150555241e03440780002500400880019119183c049514803541c00144401c41d140d401801468800740000d00803c84a09403204420190718a09420b02c6081281c0c520806083c0b81d1000300158640f03c000c0001245c04040ca00844a00b11810140341880340700701655414410300c1141d1040c02a8012000202e801c000100d010901800031102c0a035141c5d00210040041d5005a40c415101d142003030342d0751203600c201d5010511072907100b211030912010012074014180296030041400d03c0300710080c069625103c5000811803407050201e0b00e05442c2c00380e16035401071140381c007510600d408a411079440801c40311040002a00300190307401c03020b8018001d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 88830315 1250 88829065 88829071
    0x13030809060d05070807080601022103061801090203010801060509070f110f0307050c040605030601030f030f0201020409021813020f070b2d09060c1201030b090705060a0c0303060504180209 83
    0x1c0800308118411040300c0342d0050358401c1c1074a490740002c0d4a04407070068400c8400411490464210480310800d5090003c0b003030b101908145412622a660320300480c00c2101c0300800902d01b00c180e43d0002134009201d0b0010350584c2c040000a000790395a900522043c1642a01c07000045260a191181d10500c11501e00620b800390318215030020701b64401190959004010a0701c030b41c0c0104035103111904040c0a46002041c3c1035006261640c07460725074424400300607500a0411002c402e004441c2c81c804d405440141801010465445494201800c0030040d15031501d4002c415000701c0c001d620701c6510a80307503260029a10146450040e580e00305001400520b11051880c954298503042c40003124100b03c2e58546261180883c241254981d02d09000141081100c4d00b0030000c44101c6200102454110381d44801000826210190315a003054115001203401040200e50218240d0380582010826402078504102c8261a4028401500c0d110b200d42075400c0100c10480c80133050041030749034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 88831565 1250 88830315 88830319
    0x901050c07090e0705190501050f0a05040305190605070e060a0302130e07200706020d0305040204090209090319050c0307030e012717030c060708070e060d060807080313030809 77
    0x5889511510420200c2d4004003610f451540040014803681c2003900480000200c2e0b0000b2009091030240001e0540c41072904092603610080741c003090060084080d80c001d180d2000503101844c1e88000e1101107000d01c0030007900c1c0141000c000c68103a42c0200090180d00300b02507c0c40c0d00c1c0c600709600a41c00f81d440110b43d031040040c0c2c0080040d2513110b415005015a065603901e1100c0c8071107401301c40b42c07038885118000e038580006004000c415000280c001c174010140c00c0c0030607140d907540001001480ca1103c0a900703c1c01c00d04c100011210044002c0c80303042d8403215914170800002d201200c150140c81c0b000e801644c020041500428002c510180c0a0300e030500d05010454140980d1034242218891401c0b001622800c2c01c0c0052065070711001208201174000b182045c0e668685d051783c4e403802511400030f00c0044000f255000c2e21880902440c2b20340900216500c9900e000d40350000d025502c41d54503a8022000081010b00000c0112175001c2c001520302000030b400d40d200d5070441d9200801483d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 88832815 1250 88831565 88831573
    0x21303110d0c0b03010303140c1f020723070603060305060a021803030406090312141b030904140108060108070b0a0f09050d050a03080114060f0f0c0102030412020d0f050901050c 78
    0x800000c2140c1201c4010f8501c40924945952440c40c0c0500900400070152505910a1107080882c0d50b000803000c062640030100c00c04943e004200000091049030030107096a0942d40007040c80f82d051081e80302d03190001c14202c540041e03603008102c084070180c1c0070081070781d040341020031000c213643d03000740c556142c071480c0c01a141e54400000900d564003641c02031022440302c6808106100408040104428490401e01d1032110f40310706200030f900c200c40c01c07102c90f4680047d0280c1c84110820913a501d0110142041059082c0c46084560494091044000d240704102c000310b030f44500810040110b4001004060400d810408107981501c000000e1004102200100013215619a00d5201840780140054180400142002050703040160048510100c40c0c02e024142c60729242c0032030b14600074584450f501c8242e40e8601010500c42c41740c0c0d0600640c0048240300502010074690a0007200940848003075145540c02030f101d0703034900c00041010801c14050180694002c0e0010640b080d4000251 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 88834065 1250 88832815 88832839
    0x2132702030106050904030816030219050a1119050c0406050117252f1e0a0b010b0406111501050907020a02040f02030a0b010201020f0702010c02011709030304020405070302130311 79
    0x11070185c14044400f50300048000c0f0500850300800c05c200441d506141c5800d5142400d1110300b0440024000140000c00000080110300d0510a40748961a82404425541e0900802242c20101e05081030196130034020400091138920f8684074040854006031901203482d10040ea1a644002c4010034140e002c80c0c0d00d2018004400604a0f0700104425a88900caa170300814280c05200d5500038201d48104e1101d0400000942800602ca09002c0d400303120305d0f04040d64107200c460a05415040060681685000209090104070058010307114940d484030701e1303420382c4118540c2c4c3c6c68045115a1188074841c1c014005814108901d41e0b120384c180c0103c442c0090103902103000c50703900310030000402c1d90110620401e21aa8002c0c5414000300340b00070350030070400c100b08035140e118180c0000e0601804400d000d0441e401204c49004684900715a08000e180540d061601c80c1c0c0b003110301301d05c039604e0100040e100c24000d02c20390344076045262503200411f0641d0343c0d64104280320300800364041041406 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 88835315 1250 88834065 88834069
    0x10050124030b182205060403090522020f0f0f19020604170906070503191407150b0f0a0603091104090807060911060703110c03032d0706050a090213270203010605 71
    0x70080c0b0344c03446540100154900b50400420594140d0480c0e0300c51403010046200034000150300f19100342005000680c0d56503d01c00c815074a11a034244010044000b181e207140644c1c02501904100030900341d0280440283c0c44205e841c6c40e002c0758001c105144200502503010103903005001c41042c05008640740c44041e03180d0f50700d035800200040344c5c0d0414bc0f54059901d140c1c4503c401c00c0595070481060300380f4010f95140a07040d0750703054440c809555140c911210503583d100142c0302078440903042c0b0194640300d82005015001040c001e07a40e0124460200100f03044c2072050704143ea4020344064200000c6694040161100c0324050b12a42c50105043c402070352440001c1c56034900c29141c15000400c40c4d03403024184040040711912a410034030240b08011100c0c003108401c0a850b00b5620081703aa0701c82c02075441e015654000e082146170000704a106001039000c2030203d170084418031540345880c00c0c02010756144000d1b6070000407000021201810300e18103112100c62008002003030b4640c403500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 88836565 1250 88835315 88835371
    0x906180207110d11040b041b03090c050904030f08062e20010903020609010c02070303111006090203010504050a091e0c080a0302071d010302030a02010f0210050124030b18 75
    0x10303060b0340d0541c3c002d6841102d45464400c802c0804400e44091224120407a08401104002c103480018152680e03a400104446e2f41c4902020300f40c0200361310420300300b40c14000d1140407a88000ea021402c0700c0085203851909420380d0041c0842824000c0101c154900d20081e641001e151100521402030246201043d02400d0010700080da01d00000d4008117900780203143c008041e10011440e450902600081d644c0800c6840940760035040c00c100e0242071b01095860080c501002101d500d00c1c114020488580e20380041d0b0403640202c9042c0010b40387c54a4501c215810703000000d1100d2900b200c0103c0c0070100c89101821580034072000000d641c2d80f10341d400d04041c0046001c0b40140c00c205414020a04003900740344840c18028011800c80d812750b4082951102076001c081c0c1480824000040c2c25071080128411a0445220610055a603034400e18200400040ca030300b40c0030b4400041180080c481d00c00c110540d42e00402c0c06800b0a60610342d40c0c03000390090104403109803140000070003144c15070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 88837815 1250 88836565 88836589
    0x1260601090b0a1e090c1e080a14130b0901090206040b070302010c050711040203041502070b070e12190f020612010e10030305180103021902030403020a090618020711 73
    0x70740803441d120140200207030b42000d600841d14821960402c0038001240c2c4d80920306030b80000e40002070740001c185003500d000d006000600c1400d8486420104e41540c80400ca900031415450b0134400c01c40c50415201d003203207013221140c1d15915524250741c003040d18062425007000200380005124403490700429410750050b004003003000ca0000b0b0034420194244142c3c5501010341c83c041e4102440c982d01d04c165103044950262085402001040034002c1c46910450305d0f4058503000c541d03840540c41d19100c0d401c021a80b24011415540500750030b410442d0740260410301c1071001c1d1030081191100043e005100d00c01c15a00c1c0c3d0000c4280c000141c0381c5400924010780101880c134015031424240192824000301105450000e0000400001e500803040c1c5500c9801c20300324500e80c0350041c004a009000d03d452240c840e4080314955a8603a4010005100341c0740241e95282441e03882d1f29010003500c0c000d01c21300c5c1300c0d07407440040035040c02415400780034610b103c0c011080544440900040908880f1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 88839065 1250 88837815 88837829
    0xa1b030908070f02190308120f070210050c040906030f06060b030c16080d050c12060d0f0602031f0b04060e0303090d0201050a03060b030117010b0406050f0f060403020405090a050d1701260601 84
    0x2140081c148901e51006d501c018009d02600e56440d04000007501c0e003985407504821682c8600100c0c001416640940d0003030021700d44104001c41d542c3c00d100388101c1d8154029240c2516024000c12828881c0003160301ca0001d88011600c3e0a50406042d6a4a0401e0303034103981094090201070006003180c0180b0b4003620040800a8031000c00c0c54200f00c2480c00641143c1c0308841110740c1e040003443c2c4056060700e0b66006180180c513552045245514080c80170707400f622042c000b81000c01e00814000152043c0d82195942c1000510301c070040c0741d82d038030404051981c42a2082c02480066100d08010310ba407901074503000ca8081d031741e0203100169410a130013003080303440f0b20000703208038207400d20034800a0a0b04480510000d480c1401140c101e0700d511410901403122200c0c21109502c40808503001558003401c01c21091900030102c41c2ca42000318400c03641e5010721210a410340b4892440c0e28040000ca50446000f40d1a1001c8054150f20158100e56040b8402071544908802880a1b038020510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 88840315 1250 88839065 88839067
    0x60f0905070b0a0804060b010c1a0702010f180f1502190f1d04020d02040e010b0301030c1203080109020304060e060906040501050717060609010905090a1b030908070f02190308 77
    0x151400904040c0c03907030001c2641040501c1410f8206070301000307964101e5040f810010b006d0401070012030300824080409003010307212840f41f20061a42d9004c251180800354001c011424803801d10400307840c0304a52241c100412031030304c10041004c0c001d07070b40000382c40383c54444c0c1107524251000080c0d030421140c1c0b03920060410030a44006401803480c4400210502d05420308802d01e00c5940248100c000c03125015a0740403030b80711001c2000b42c0c11180501966880700300d0b9507a6600c4a062158424003084900c4140000006071103c00c821031074000075132584030740d5203c3c2e080104504c006d400c000c00958400751207900c144210842804028001c10f00710020707126521341424034600350f41010384918208026492181c1803a5140042d4035089002290410341d11500c00004880c0c00602d5004543d111019030140181c10b10b6a42c071003401250041c165400d65007525000360225241c5042c0608048003c0007400001a8188030007500241f00520b0700000716503800840d210ba10b181c3c0c20403628404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 88841565 1250 88840315 88840331
    0x2151b010608010b01050306280504021b16051c081603030903021b01020c1309051c0201060902040308070201080907080601080a020414040f020909030910030605090906010f05060d09060f 82
    0x1c401e0013007000d401c1c001c5c00c6c250f2441c103105001c115401e400f901026140314401850112a002c0c1c1000000180340c000e00c15501c98070340f01d003031031a1a1181a080c2c4800d102e000540c1d035820a030762030b015048400003450944003140c080402c40c041d0180c104102c40310841044124002441c0701c8a01c0007032800b0380c1d07000541600504d00039180c90403246880f0f0482d80b10b02d0490311aa07900241d001c180300c1044d101950080f6241c04e8034809402100e80041040c0160100501400f03550802c1c00f00b00820340e4020f1003101da441062100f244902e00020b00040c108010800165014801da541c0050380a800c0301c2c012995a2000380c10544283c01455458208008000951500d40594003040444003004100b90400340d90f000c60110f9080d1000340281c1c0c00341e00040d0242c02c14030543d0718014000c1d140840c030801c4828010028511030058520881d24600800da00401c001b40c5181601c5400110915507410401048917540103c417513418950384940350103000402601031045d4100041c900860303045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 88842815 1250 88841565 88841579
    0x20a0306061709060112060e01060603091b0305060c1b0604050106061d09012d080606011e020a030516020402040914010b0307080408070204060509070804060b0303040501020a02151b0106 82
    0x301c1d607500e090074503100205001c07426101003401411144113038540c20070710005183c1507019108c020040e03030081d4a0050005846901070f040041c802d803140c1861452921845c200c40384c01c00303042c0005055903004200242c0e03031040c034200418030b01640b00d110007900a50b0705055854620103e03422900c0d81d4485c07408002064100003401c0054a00d014407100e003981410105240701e40500c03c0513048495003030201140c001250781d0b040401c2103c8804007000c1e407074000740e031b0762014140c0d20503000800c43e0080c1d0180301c0d024503284507000081c2e4007414010003a5242156590045101e003400c2648480803000165a503200820060035101008154180d83d00e08a840108059000c2a00c5071020820071804607484071203590300c07e0340145158bca80e4018000f117402400280c10039600030040c1d00520002d1504000400d100e14425a001d22507400781400341074882c080c5225031409a481225410010710700b00100c003c1410010b5102e40c100f90440c1d80d501c03940000f050b40785107145d56880c0c06005131 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 88844065 1250 88842815 88842827
    0xa080109051b0304380406090303181118070206070c03120f0e0114010509010b0c0307020d0803040b06040b01140c3901081005040203060102011b1d09010e18010f020a030606 76
    0x604400003400178a002581078603c0c001c001400144426034500d5a0001c141c003983c4000038a80c20300d6015005c1e0002441c012070300041d60402c062250b0058219001114084400700d441024140e011f04890b46441d881a01d0101c0300017421003d0240c0310f0a0064028400e114004400308008800301c2d5001004185c9400c41360328815400c0748100000050041d40c0b540c4841d90b0450762441c4544d569440c03503225a40c118000c104000794403003000f60190303051107034200286000381c1c000d540800d001d880e128100411500800056400300700c00910404444000c0c10207010703041000c500340c5081241c100c40040320075030008071080004103d2098181400401411060070200c20b00703003d040d81c10300000c000503864051152501c103d40003c005401070340f00b900300c2ca40b05141d9450b0481220081c1d10080c0011307195600048541d00000b5110b40a40780107017820741203401071410b003c455124552004001d00e0001004c200940d00d44908181c031000178801000440740d01c1d03500260560400c0300080c41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 88845315 1250 88844065 88844123
    0x20907031d0a0803240402070b0619050906060703030608011104150f0203030a0b030a050a2001080c0306040c11030f0406120b01122f09010809030a080109051b0304 72
    0xc1c40c0d002d0748210000070610000c8a0308044420f0340406210010120100c050000b122203580160011886904001102d80d2240c05845c0031510503911840c000e0314810030070245e11031260b001c034400300414240d040101c0100400d43c040c0c940810002d0711a5002c07402e40301c20000540b010080041e0404c40c1d0100c1d0301c19031444c16107034078049c0131551010380001d40d2804040c0c400c90699940c0e80b0000d5050b03804201c0c0d40c520340c1d80502900c140b034515042400b400300c0109856071002c441582e04403001e6200e44121413213200400792860468440405100003040d03004444e10a00015072400600e41030100301900440041c080300a80e664208180200440d061010141401e07040a54100780e81ea008414084104d0754440002104c1c0b5600c1d10304105090358612411195803452a464051136075074004000d440000e80310401e690321008143da42e40e100e409c001100040305000148090070142d0001e03608080000c0f40c04054001010000c10301f0342c0140c030100d40c502141c2e10006018100c80c414111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 88846565 1250 88845315 88845371
    0x40504110a0206040b1003050618070f05030601031b0302030303010e06180c0d05070e0a03110f09101502031b0303100b04080a14070314150a060b0901110a02090703 72
    0x108040740501d0195a030703c00070304014140d44080001690b0300c01080c280100441e0040c045404d01c0c2000c090300613041e8841c4000300060b02504502107503500520f40440c00f1190068003c10b400da2031a199202c841840e2124410f801010180000243c0e400b00080c60107400a100000e0301424440e00b0403001c0d070b011140a40c072000701030703082281c0540e07a9001c0c0c400f4000580404503c550b00c6440440c3c1c814a00880142e22002e4142c0100a120a166016900d81d2050300c1d4034502048210070052010401c580e131251210f6680b9041c003103c2c40d034441010b0304200600440381801c002d501106c0404100d81600c215941c0003008108169000b40c035207000402d045101c07a40f40506212281741c940030182e80180a054407410461800c2c4e05c10060301004540041400d0f4441010301e14058076041094449034000f4400408900c1d078900740c2c4101c6049820030041c080c42c0003581401580c503007603280c60140d41c0e03000d0307042e060001d61224058540b1414440c1d40c0007a0307a0031000c6101312240f94100340b82c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 88847815 1250 88846565 88846567
    0x40f0509071e0c0606080f060c0301290904060b030405191713030f0602071506060509090a09020406030827030307060b0a030807030f080105040b030d08070e1504050411 74
    0x500da07000080d800741012040b0300c80c550050100c03000e44a090710303c00000d01e042d14000000030170300804100381d00964100ca088e200a611099840d6000380401c1c007078100340400c00c1000801e80344400c01800702c4150211141414003911000040840360641d00103944440008208410803009100d00348115819900742c28810419495218118211080020103400d0020b607101a4114a550003c011036100b00801c507496a203280104c080d4000b25000ca03591011004402e08451144c01030600b5143c02d5603402c0c0c100000078040240d800e1000c3c1c140c0511a42e14034075500540c40d10300603800618002c0c00c10b5541d980b60303600b060b03016078182d09a000d41181000d10b0503209a4000c0102e42569403c280701148410703803880000c220096a5200804550001540c0010503400101c10441c1f8061340d1a0103100780e0740c8c0c60501c0b0a446045100340d0781600400031841c415030060108503000206481c140c52540440700125011607451500b448150b50003050030419842c3c117010f0012060784418140f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 88848921 1106 88847815 88847821
    0x150314030a030c09060f0f1b0f0203070603020708040b0703021912030605060a080a0f0b06070308060411070c06050304020105070b04060e0c09160509040605060f040f0509 75
    0x1110120b070418060f40c410f036009103462422289140c41e50404c1800c401000c0f1004c46000320041d0038020808a00f040b0710440001800100d4418080c03002188260300425141c200b20303a01520416004002400024a504095404996440c40026280c0e02a86003c2e420b0101d0410241c00352010211020140700d0030b04d4030004146410b0328104803607038445040c0003a0f4030540c0c00180c08213419002054038404164061400414403c3c0001070401c07100d0000f5405038401365050f00000c80360f909010407854548038414602c850002d8851400501c1e17641c0300c4810041344180814000b01000080035640034004590f039007940190700c81081d1070140b43c00d2008000160b00c0000522850b404c10f44030382400c91842c0e0007507010350160380c4a010801001c4079a0340c0401a80c0d60031603242d00700000d490722000041d014010454510540355814002c0c00c41c80003503a80d02c0325105003c0003040c = true := by decide +kernel

theorem cover : BRFrame.Cov 88669065 88848921 := by
  have h0 := BRFrame.cov_init 88669065
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88669065 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 88669065 ≤ n) (h2 : n < 88848921) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
