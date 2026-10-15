-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3876
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:13.593631+00:00
-- url     : https://prove2.me/submissions/df25f54c-9f10-4989-a0ec-1274f1c9d764

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 696942446 ≤ n < 697122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 696943696 1250 696942446 696942457
    0x180213020a030f060b2730100f050709030c090b0105130e0414060112020d0f0606080c0307080703020d0b0606070803091c030c080a0c050c01180605011a04030206 71
    0xb80380c00116119048600d804442440e08a0700c0c80c51000300e800e45402012980e8a400a01e284409882440c042070202c3c01c0c031a05000034040064080c01314070074400141105140b2480d5420449002600303c15903003004069100400b4144d82c18100040c08040c040d4000c0011654004080e41c4001d29100c05200103106201c0c81e1410002c042244010801403254500c024191084441009080500e00100c21103014501d1031820381242004100c200390301c416010500da01602c4005040c0703c0c1e4900f4600e081c2c6c1d001002400d02e850301c08042408800000c0c0c00f0302c0344000b90121404180c407120700f95900d0741144802940074138101d180500083c596803003643c100d9405030a0ba420032101ea925120b650704200c503160500e83c0321194000080340800501c9071040c5060504110200402d10000d00141000340140040c1c0d4036401d4400f4858420340c1140d400807854402004410030903405050001022a419541e0034146000414460580c08000c100c02c1022200246028550350a015403078200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 696944946 1250 696943696 696943717
    0x5120c0a0924020115080d0f0309050a050d0e010309050309100201150b0d0501050603160c05070f180507021f0e03161b080303280e070305060a18021302 67
    0x140c1000a90b900b48003082007406112000d8011a140c4a264000e003194000000c4607501241507404000214011514802d540c1c0c151500c07200000c0a44410740c090030035624020714912405281c81b00b4000d001ca07081000020942e070741d005080800d0011016100026006041038004100313080b0140b40c105540c0212900c9800045442c4281f051000310901c02c542c0040d0700b0881c001000d45040c000c0d40708240c09840220f0b01e207815810000e180c803180c0345081a03480180040000310134180079081000200404c1c030f00032003d031001d27211007c2003445040d810000107018180400308214600100704040c2826944c00603201d4881c004004c1d001a26050403104440e010030448501101e40510380b190161340540b581d800c05041d8000441b2013601c550b402505140c00620511004046072020782c42c0c2d58036900c18000035400110f100200074144611004000c4c8601e2038000108007000c244940b1400f1682e004201000c1400c00342c00b606440703000001e600401341608222a0b44660b0301405019030b0703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 696946196 1250 696944946 696944957
    0x8150a11160c050a3f02040c030906050a0f110a0e06030709031a06190b0d02090f0901080d02101e0c050d05100f05011403041106070f110f0105120c0a 66
    0x35900c0104500c80801e8211140d2402884085c200f04000400086004280c6482e0a030b201a04410040c0030a504904001d1103584c0f25100e51042d603202c0d402001005e500980c040015007885000100203120341040414054101541445401442016a035024140e42c940814040c0b200c02003050540c4000e0465043c0400d10402101040030616003803060361010017580d2007400c080e07081050701d525003158000c2061b8802d00a12145d4011803d07200744c91030061015807203e082030006940d07803000c240f4071074210f03048000000321500001031409112415409030b66800300c0020f826001d07101ca01c03850150f800d40c4a07503040e820310310701e5105c1c1d41d0110041c0307001810180c8142404c2c083d0b440c10b50748450700038422081404036400138007a0b42d008020900303000403046031504120115020040c07003d0440d10120200362119207c84088079000c0740d04c5007002221110610740071203500000186603000d0304010031104200c2d4003400840300050b02ca0b12000790290f64140038401c4650000d000a010401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 696947446 1250 696946196 696946199
    0xc110a12021009260a02120a0201142e140616050a1109010f080703061a0a0603200306030a0209040521180105040501091502120408150a11160c 63
    0x100c0740b20304094507100320702c5454102c42c0c094400e44607000681600140c41310411a440204da00061b43d105403c421280c00c40c1c80d0b00241d40240c0c01041e01c8111800c1d2080100701304407490805c0c0d03007818002007254100451807884009899000ba4041c000c40b046410040c90100d410700d88100074203807038000c880d080303207a80545640e543d05008010304100c8480d40c1005051085107485100c0e5400351140309410031605140003519941c403805c91002410155844060144450210214406494000e88010503c9079240801001804a503002c80103194480c9600403802c0b0081c41100c0c06080e00030001c10140e42d032a0200804601d004e0b00407100c51040000898420165004128072460b048100c0b80d1642c0140e041c81c0d0f1658881040c050400c0f0040000b0f110683c1c10001c1030040e1480091840200010000e0a034644200e2070b04488800350046000070340040d00240e141c0c01c0d016008034a4009482d04c10348202524080c210400401106000540162035031808001082e401500143c1905 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 696948696 1250 696947446 696947473
    0x31b0609080f0307120e1e01020f0a08090115060801090e01200c010b030f0a140c060d0204060201241802040e09060603120a02150703091b090c110a1202 67
    0x10307800b201c0c03000c0702d5407004801c1003d00c1ea0494030500c01780328500301c18400c01d0458605a41c0319040c01100030305072200e88980c0d0412400960550300511030080c0415541c91180b4006007041c4001c0f00c00300455070910040c0c60481034801b0384101110041d40b10707112943d0a0145000c0034141102b840d44540d0b42c1d5007012040c1c1c501820f0042e1007100d658030351a076510004156a42900d03210111180243c0c00b1802c01844100001044898690806081e44000c0002601c40d4200461b20260682c40a40803c1c40c41000c1c03c0c85d8000c10840306940c0081090050803054001079001ca2030600010910300718042200803c2201e40429003410303d000103207495241c40149941241c00e440d000d1055100c0c0041105130b0070100310303090003888050043d82c1849c1c01080020b503aa090000c1410001103000c6c04901310500941001c61001e91013030281c0c60030b1580c9600809a64414440d03181d003581094202440540501c03e12a800313906100585100c40654071042d81b44090244090118880c03000010440c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 696949946 1250 696948696 696948713
    0x7110109060c0306171603030810030b07050409050a0506010e01030b010c02193015060803030f09010b060f0d11120408070302011103150405040c0b07051f0207031b0609 74
    0x2c5040320740340051010b0800075032030040e8030740c1c484001440d44400f5091007842d03104d50480003142d50500e4040b403147d50340b41948141000c2c90744002c040101c102c050207a01c0c0d03006400341080d550a810304000c940d407100d802c035083e980242c44541c04203842100b119040c0d48a60007600030814103040105c251521540450240352105081008031511000c0c244625030050019010002d004845114550100054000614411070000f040031103012200c204180040d08128001c0c00140b0a5130745030700c2d044103000e10000e02210009200d52903c41000c19500e4064241c03055514101e030054100150005004000d00322400c03007050024003802101d0305110841a01c610481c0300740d1003192900024a00030b82907620403941a14000d1050042007603852401c100c10071207240071603021503241c456050460b4414503940103080304500000d0380c04140310703001440c0019138080300c0c0604417042000b000d103803c0740140b180040002d21041070221141580064546609010302000201c150707096031030001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 696951196 1250 696949946 696949961
    0x15030f0706050706060605041802030411090c0a080f160302030a0f0c17091912200a0b0903040b0403032709140a110a030e0a1a0603100c05030711010906 67
    0x42e800040c00b41c100042806040010324141c140f460500d8180091081d200340041c1c170140302030f980440041c3c148000ca4502040e030507400340410543d42041c846400e005d902c200802004641d902c03004c41c0c001c20301180d5243c0700701050a144203812400c06030440280d4400343c130000700c95858000b00461440c81e4480c0001c12400ca03202d1555280c500704000003d0f08000341141c049410488000154180040f00342e900180c0c4082400c02000340c00d001a90b100004489030b1511000b121705000951500088401509014030740035000355442144c0259248128040c1e5468400d0911040000a0160705018a04000c2000800b0030030700c0342d0340000c0143c0a5038040911152255290f00700c0c1c4200c4c0b10040c0d040741c400c0d40180400e4452803844c2d04d591041001d0481015551004161940018008010301644c0818544200a1101e410309203212060307803100c0c401e000f56183c40344444d20313521070448000c0c1c0c90740380e150540e95001c4084e100800c402c0d0900b10195203d0f5891000030350036103c0c810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 696952446 1250 696951196 696951209
    0x903020a230706031a13020d09060f0f020301211a09030a0806030c10120209060c2d0c040c140304030f11030a1704030c0c0f0312050702010815030f07 66
    0x1e078500409100314503140080e4044028075142a44080466a04c901034400040e01680c1a400703400c00d606c040c0000340300f013080c20301d1064502005a4108040d41e004201092000001445200084141c08040340300030700c2403001c004811003550240d81000e0b01e107070483c80c1c01540d120060300d03255a40c0410201040324602d82c680c000103042600750b0b4000031501c0e0040340650007029180e0711040840c640c0d02071074003c7c00c180610b14414070f407080e0180d01110b40d90b0b40c0c0980425102d1720b42c13000d1039586907440100008001e209061444440810fa200d2020b0024080010450300d1303040000c5c00014020b0080d24401c02481100740c521040c1e02000441c0558800d964080310140c88540040c6401c01c25802652507030420820b01e2502c40d4010141280e0004e242c1303045805486030300d400c0d41d00b040613510081641348400000261181c41104071001c603801019034408109030b1400031190f0344101e0800a002c66204c04c003280c2540c0d01005541c1c0d10035400b4040724018a2581040761030021140e1103c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 696953696 1250 696952446 696952493
    0x813060507150e0c01081b040303110c0103141501021c020f07060e0a09050a15030305030106170f160c2003070b0a14030a2a1803020303030a0903020a 66
    0x1000108288481c203003440b65420060065010820f43e280c4481c5100e4504010b4281c001c1800d0300c0198180f0b01103001c03050f80e0b0f00da5580d41c0380380113001e100c041030030b1007442d0180c07005085940d40039004001e810080a6400c041c10f50b541071007220703c2014411524114410701c040429601c0f080040e900c8194001d0f001800c0010202c000c0a14042054000004010844035128810346419080750140c1d4480c00000c14140d13602a00b0f90010400e0b11403410001c2c2c050507000040c0364002c00158181c440303940d1041e00141c010000c07041c00e0f090540350300c0d12544040001903580007880c05980b00c045441c2c80e01c40c89001068a0b5004202c0d801c880c1c01100012001a26815140070490308006040444c1c03c942080758969000e4115504440d1004e030421001000482040056101804003188a03200300b2200c0015400e05140ca4038034801c95012900f83d5142c040b050740600704010842e80d0041c0114a5640c0d14001c14019081d0200120154814070f9250030020b500018522080f00c20920034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 696954946 1250 696953696 696953707
    0x50d1109060102120a03020d240608010e0103080405010e0f0409050d09060e0d17130f210f020f130f020702030d0c05060c0304020a090f05251b08130605 67
    0x421050320009803019042d0751011a20f28114000c9409560107401c1504006844038088000240580f42c1c0450950010200c00c480700300c01d11082400b04246d9043d55501c00c540d070380300c9840000d003510a000281a41b08140000c02180d0303c27038803030171080e208054980080b00d610900031030152584941c0441d480c0c0c01004561362196400f03600800100503625061503a80d40304804506c0e40307140c07107401401100d0024003c030384840c2100d040f1034202c500d460b0404503083d82d49807414040d100b40c2c0200b0141d80c4080e4000003001e03051901c10442150840b2342038000642a42c00c000351076000070021038000030000c1901800d060703a031080440010040c503001d0380c1c1c0c440902c109414038003400e1082c400c1c42102410080400e03c00549184d0085000c0101d81e40c0307445034000039404400942c4010440b5080112400ca1150503030482405910088904da1181c0d40001c00349540c2001c182e41400061582001b00000ca042c4036500c1e030f0300030b000d112000d00c0c1c43c4d4240d81c05107103016260080c10114800040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 696956196 1250 696954946 696954949
    0x604030306031e02091b040b0a0909060506120a0b030115030c03020405060111060106030b060904180c090e150a020f2a0102040b0a08040c080f16092a09050d11 70
    0x202c844038143c024011100101240d000861040010740300c0d00400d100003818000c50a802801c40307016100461520343c031740403092001400c40d0b1081c05507803041e07070800c0340007c0c076420680241d171414203401030345080950740d084003500144090701c8455072641d01c484a1113004201a254107002e1400f4a102640c040e0442c0180002d40d240904500d0402c1000d0b100403410541c0460424190398052074045280780007a000a01c2501900212580c4507240c6065006050000d00b8888003251042c40320070b003400c0d950f070949421034000c900891a140c2005000c1ca5110a0303092485900c100c00e2140103041404402610409400407005410204a12a2101c1c0e0701841d800403840d03c4100b40009510341810288070040700c1c003400c0d4280d000d101510000c0f500300501481036101038160740703007124100e03445544036540c0c03851000007810482849800c04580c040d194010085180c61412072000300b514102c4a00904140d034085040400100010202d503d81c3c49018840241c0d000c2c0e9800316101e0075110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 696957446 1250 696956196 696956213
    0x90a0b0a1d0f07180204030602030c07030323011418010306023408070201030f090b16111c090803030f0703110a0212130305011113060836060403030603 67
    0x1409081c16038040910311a080704001105815030352030108510310030303d14800310400b81c05107400040980740040100702c4441070342406001503070300959082c494030001d1390740a412440d400c0f4141070b00c0c00c4401c0041c00181005042e0032410700b0090410300c0166101d640c0c9030780300350003a0800c5460980001d169140c40b4190b0618440e8841d11a80ca820342d81408901c6903c40c990044005110348404a4081c1c1568041e601178001c0c0c40b042d00040c4036110031840e00d02405181200c0c524081165143c0d80d051041c4202403002e40240d20300000d08020a2134001d40d40500001c000010400c484140042044c58003071000c1c501038002d28060346140d0030441809401d44022880140c0000c1003804100201035001030f0403030810410b9407000390f50f440701d4105283e6001e0306401c060a60b43c280b0861745084000070b0b009249100030000c4a440e80341d10b44808542288046e2000420035541007032440c1800e0704896188040010002c4128241800c2c0101c81c0c10701c00212403d50100b030703072031a08005101400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 696958696 1250 696957446 696957491
    0x60506120a120f14070b15060a0314011a040b031513140a0203090d0c052103041103061311180103080a020f0d090b0c0a081204050708071a03090a0b0a 66
    0xb42001455014001d42a00490080201c050002500080800d80c0f559900241041860028203110f0351142703505400f40c0601007e0340c0710030034406070800000780c109201c03410101d10607040810526081c5068541d18607a0005041002040c0d0011090310302641c40b400c0d144901e800c40140461002c5425010141d60320005020f81d82603801081001034950010856080802d454100800003007010304140d454540315101ea4412200100c9290100320100d00103184960b1283c00c05080c1b61010006142e12809c00b80c40c1d4090118856050000243d41140c00401d9121701030130001c048041e1110100c1c0442082e84291940c040c00030314504580e50500041c100314440c44000c06281c1c02e56007000740769402e00d201e0396610003008208510303c98800c1c000f07031842e141c04c0f17880c880d122140c0d01034418081d10242c0b000c4881d8412940f000032407850101d45902140c00b0b442060400c040385001e021480e80c4010124107140c0500c1c0e50b20800618011a40c5000301c514200010309442d5940300486000c508 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 696959946 1250 696958696 696958727
    0x120b150a081b06072f060a090f050d0305120a0f090c0e07030501051e0103061a130f05010815040e010e01050709050427050304151809021303060506120a12 68
    0x4004c00000720380062404002411001080074005541c0c00c21849044901c2080d1a0702980004a08032116400b45440e01903902884100034001c1e6a03c0401094900303810005000c2501440b00c8110000d0400845178400c065080108608960280000c100d80c10041c04a40c82420b003070091103200d024007140c40e4080d0b218102044194100800034240364200c00e1342814802803c2008011644660040e00050040741a5400100c82c00a903041003501f108040440f18158010000390700c8585081070310444030180c45a42041e04d460441212001d41d4995481c3c00c50741b9881001c00d05c00c003d00c100c01c4582000c20000419003003900000700760681c90f5120a100b1800c148400c0d015201d004994059041e41c0798101d51091490b241181c11802543d220605104041c20100043c40e08101c840c5080f2403020480c0b601941c80b41060740403802205511400703105144c1003840000c00c2d9600040d00b16800a00c1c40140d550078158042c07034083c080004540d420170746102030942503040084c0e02581c940c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 696961196 1250 696959946 696959959
    0x1812050a060b090f041403090915010f1403010b031512060103030912020609040b01090f0807051314060d060f0c030e0105010e01081015030807061b020601120b150a081b 74
    0x1303080d141500f10140181018005190304d102500404004204440e1000390251840005140c0f107035200c007511114148041c0442c03001400c0110340c61194400d03031103c0d13946002031070440c1d0038018403105d59000140000350b5000c14140f16100303981c455440300000010607004050560651500501500c12a40101c0c03000000d03002c9440140d45a40994800340c60564001915088250049454282c40c1d84581800000341e140810b0071031012980790161102501c80b41c010303268044090040702c0c400110960a40b584502103101c078541032405a0405020b80270215213040070a0616044500c100c4c2980040303036030b51980705007104003806254010660f82115044640c03418a24a4840c50360034081c41500e9681c44102105c80c16000c004000785400c806207585408142c03030f154000342034100c0700d40030355805d484468845502c006440340c140e0700c000c4010aa000301a41c1c1700780d0400c07800b0b00301000240010300014055118044148010482c040c01803907024045649581505600f0011038000c20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 696962446 1250 696961196 696961201
    0x2030615090609240a1205072d0c0506010602010605010e09040b04021311120f16140c1002070c0e10140618040c0e01030e0601151812050a060b09 64
    0x40d0381c8001d0300c5400d4015180c020045080000c6400a41d400605200c00814017203902401c543e40900c14040024100c8401c0099071030f001700c19551700b6400308031a03c4d060010382913200c00c5110041d14900700080747c01c0c140c110445030381d201d40c1028026005040140c2d5111070801040d80d00c11003544440f2810746580c00c05040a8503820f400030310041000c1e010b02844e802c00418581e081e0f12949001c0050004075484084031044021034070801d90700c011005c444100810407591170301c10b04d1540cbc10010744441704403c45452008803560008a41120b05000b00307140c0300750400d0580010700900d849130395103a0b07569082c190741014591000d800084c42d00c400a60a100b6404045a0740e9000c44044400399100d440d0441c0d445c10050301600da01d0f401c1404d006200d401c040d0001c0000030071180c00d0320280715003608500702540d640b1003403061086040c3c02940c0c8070781640c0600c4e40004461000d0080e44d050315210140340c42080d454840031113040d8000384043d000c0c40000c0c49652600c1c20101c13034030045030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 696963696 1250 696962446 696962449
    0x603240105090601180e0f15090f0a060f03151506080718031a0411010e010507080306010e031204031101030911120c150d0b040902010203030406090503070b0a0203061509 75
    0x10505015050041541d80c010030066030041442e0005c120214a1951006442d041c4200810b042960b03180c0041102c1c00104070801801350503040c80c1c01000e00003020503550405107c0001e200541080b181560b2401d01080c1d00d402c0400c6900598050a10500802d10050f503210803223aa0784c0440c0c5029500442c14402a64030024185c1c100056190016208288540d0f1a52040803035000801ca005010403c10408641713186280c0304038001c40311740c60b84d07560b003100542c0d0750142d0314074060004804001503c001402d1030081c3d50401d0040c909820340300320b00004a440c1c540074070700109108030003050800400180250f00c1c0255142031906001518103075941c17501303603064141e5580c82400800050044030100b00000e04000d1f90042c49400d0141100283c28a20b6011040d5a810780e030401ea0240c0507410700d400360320b10180d4103900448ca180e80f541c03181401040340600c100e803540010002e100104207401e0540e0300400c00b40d040140e81c0e007450020401e00300e04008960354501c0c1c040c000030405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 696964946 1250 696963696 696963763
    0xe12070f120606090e06150913061d060403170601031a0d050c060f090102060c1e0a02010e01051806060a0501020607030e0715020307050709060b0301090b040209090109050603 77
    0x11200d03003900301c518503415440d104018114a0700001000c03450030080c404020000982507000314680610b100c0070030880e03814040c0207c3c0441c0e90b001c0d50411000e241d00042d0b02c5a20041c00c182144a01200712001c0b8000c2d281056810ba806500080c0d1031000652000c6c2100c0019420081c02d003010405e01941d100c8202d40f9440e11840548a850310308902000e000c41402000c0d8072490080c8407541c0c5901e080070007604e035048203600754014401e034800596900c007480704a4400144440304d40000c03802c612014006940803010401c00c5548070500820120b030240101c1f8003401400581e8601005a802d0b507a00d01400105042c1c0326501c0f040c4204201d0341c02150042e040b4a0610300414082c0800c0b081d24038081c041d03801002c82d052085031055241e1760201c040e003007651066098035401507485900c801500e03554090303071560070010001003218070b040e54803a000b046030103080941000c040307030001913040209a000b2244c50b6122000c100041c43c0c1809448411094440c183c2003084024824012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 696966196 1250 696964946 696964949
    0x6080708030a090806091902060d0507050319060e0402061303080a0c14150c0c0a0c03061506021c1b150c031b050403110109051302040e130201020a0b06040209040c0e12070f 76
    0x3610f41d400d920f15001c1d07443c9da00403106802c1d13540009001604107240000d256078400c0312150b4010200c2d043d0794001005a000c2d4000b102c2002000c0a4a5100e80d001c0042560064a0a0455034100c0340300000103201000031300001003094560680c2c502250602c1c0c0c0070a06081b8040400360400c524000c505514900382981201d8112042615883d0381040c541c6414012040030b045c070058810700108015980e040940e103840030030098814180e4403107041e6905c900b5807052600619515220030103c031702c107903a40a2409203605c107042180c40c0f1500d400482003510400112510f80301c641c0d0312365043c0c242c007810f800b512a20b015000c002441d41e000628501807804000c04074041c11042c3d90740b0b030b880380351450301400e00144070507005d120780324000f40203602034424004002e01c00000102c0c8802d00a4030707010b000380c040c4c001d080780300038980c0e401142c200002c1155a0069081c41149401d446900c076084130790140741c4801141032166420884000302c0003019100c6030340601820b103c0c0540089c503c80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 696967446 1250 696966196 696966223
    0x141b0c34050d03110309210f07030218070306150c030f020c010c11061210031703070f1101060b0c0304050901050a15120e0a0b161409011206080708030a09080609 71
    0x65443c0d0307103500d68604510039030300c2240d8041007041f190810101c980554003501d948003411690304101e6104680d4a4248174840650700950954100e600d0300000d101c81907200d4020300c0c00261560315a640c42e041b404201d02903c3c00078030f401000804040d0404401c840c140410300042c0f4628140800090800b4007080000700665804800321600b0340b50f00d030503980e8130a02d2002d035907640e18094071a0904c915207440255400c04001c0089400c0000c488100ea007d41c0455a4119050303241d44d0060b107010305525000d00b4950350302c4000184400c40701014110161a0714051556a0720f07040402c07041aa06130482803041350009000c1050640c1554805074103006070801c1c1d0300342c1558240394001401c414a12030168052540e51000700403280d01001d218801c5d64100b0007145600c44007ca4004020703008821011400300b20b00e10f2158040c005d004072341d0a503030001081440d20340007141d00380801a440342070168404a09103c0c406c0d04030610501a041102c0201880c1c6000c00c000380d035403005044441c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 696968696 1250 696967446 696967457
    0x3020415140f0d05010908120a11030a0b011b0302010203090f0105190b030a06050a0606080c0306030a14030f1b0106290f04080303070903030206060103141b0c34050d03 74
    0x24043d11118900240c00360808000c0000c0e20581c00d28911980c0b09510b1000c4100e805000101449442d204030543d0090b40c05000c1c0c1503070307115125030004080d000c804606014405a24071a00c100214503076000d2403190b400941c80c1c2c20003441c07551600b0308264800001d41d0408040200618580c4c0785002c003000748040100d5001440d4012038146032007040060310310380c10542002100c02080d041042103490f01e42d5000516a121004810b05e8001130b180158950810003141004c90b0700404c620343c035010b01a007030305d1501d0312074418840d041d4048414000d1030740c1c24032400a03c41c5401c3c82118020091840b5803d90b545401c9595900c032100400741f494461008248915040450300550300a00206002c4903964144260301030301c0c402d0701c1c3c801280144201d40002e02254424003d140069824404920f07007500c404d42e44100380a1081c211803641002406003890048080000b9a0381e00c4c0d00c6120360400384815000400c2e0b0242c1010340109a0007100000c009580390002d08104150705440d04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 696969946 1250 696968696 696968719
    0x501210807080909090109030e0402040605160201020309061201170303040c09240303020f1002041a0306120303130b090615010c02010309050601152d0c050c090c040302041514 77
    0x1880c0d85010fa004401c0c1c11138201e00410103030643c154040b0917454000c0d20f0700da5500d500c400400c8140c1c0708a0040e080000e00510090108414050035440101d00c140143d90030040c2d00000703d002070700002020040001c40c003004200e00c2e0300808040c000091840046d501c1c1d07142c03603101d4981c132507114469410015580c1e6030304003562f004c0c0f00600001c900101c0b0240c4980d0341e6400d009680310b6003000b03a030005004400c41c2442d803d480780b0803a412114245901c660410b10302802c0078150300003c1041c0e403c00800c1d0b000c0d00440354140b004520403400c0c43c608a411031780c541007410000f04010207143e800c0c0c0c0850f040c8420078804000451f001300b42441c0404001c0b500780300407000340a1400c1c0013480f0344030307030400460640c52140c101d070400e100d1660f5882da0700c5652a80d40c9000f090301c26086800d0f00c0042c00c580f0082d40314042500b51a4007807030880305004107241c0420200b1404039203402210700041428402c514050007005408849032000b07000807800d014007600302c2140c03940d409204001603482c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 696971196 1250 696969946 696969953
    0x160c0f0e1306140a020d0c031a040c050405150a020f010c020c1e030109060f0b031501121b0305031b010203040203061611060f010501030b15090603060f040f0b040501210807 76
    0x309a094443c200301d10005804c04440349030203500400800402141442c1c200e001d1540709100c1d20070008041d00041c010311104201740402040403c446604101041001007800e44500c0c0c03000c80c8129151514070303510340f100c1c14000e0401d410301483c14056410800b1020241e0380c00101200750720341c2114012007141800050400e0540d620102e180c05508124950003404403582c0300521500460307074184030650310748080545408101d903081002200d0b8200600054400040d90036078140b18070400f441c0380c030603100c242030922a180d008441560000820311100032100600500300c240c50002581141043c0d030009450750002800d0340c1001318000041d482e00303032088040096041413041645c0c91411710920911082c0c10900440e8007080c14416026010b040984004118039a014205414198120100000c0385c3c80074003c4c0b0751050395646100101d40e41c0748503041c0014501c9000103441d400f110240029100b05134803000030381d56110000045060500084c040e402e901100041e900c20040c41c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 696972446 1250 696971196 696971201
    0x18081305100c020927100c0c0c1a0702130209190e070c080d0e0a020901120b070302280203090103050604021602010302090d060618061a092202160c0f0e1306 69
    0x481c000c54407000800c0c041e8103c011810480f6546c925200340160b082050342550764000c58580140b919010486c20000da1005c0031008c1c0307211031503148451503d0300540000d1003c28251817000c81c4580d00052000c2c09203040a03c680046030780b00864000145081c648050b26a0018049420300107130130342c96801c00587e074080320826201040c0800500010306991561003141e0300b4100c3c0251011400460080290300350011104e6124001d000160344041e4110040e42000720400ca0590701c6083c451034100034a41c0d0700e50840c80c2540290b80340c1d103010303000406480e400b82180340118810001e60180f44040940044401c0d020300300542d0b103181d500080b44070300100b100080d040901d4182d000c58103126050000e0f0748524901e07803c0c0401900c62036003801c400640040d958003510300700300040c294209020340394203c011000c4140101c40c0d00340055800e80e03216000c1003003c0000506110200702000010002500300c481c0031441c1a0308107a0b10041001d00640748142a040141401c0c041040300e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 696973696 1250 696972446 696972481
    0xa05030717010f03020901050409121124091c02030a2f0a1403090a060c020117011e0603050c030a050615180103060e0402030a12020118081305100c0209 67
    0x4040d80c110a69483c010480d5640403804200c1c03103181445e00014161500e03018113101d160f08540140c1540c800524140d071190310303003c1e10840600800c2d111124140d52090001d511580c05111401d041c5801000c03d410003001c81036103407011075020710048aa40e400015a2031f01016400d2805101c250360780d502c01d05542c21000028a4600303503101c01a080c2020804050440c85403a1009500750580d03000380d200d000b0714508907000540d8100070408144590480140e060042c18085500024440d80300c107000d4090f045112412103d84a40d818a0414448100107004a1404120a00340000201c59622010b0300011160351108081b811035034807200380040e81c00c4212205a1784030424252a070810140c00c00c0140428038002000400240c0c140c112403095600901904110402c1da95501d107800b61904810f0466503075a52222072034008481112507180101101901e800381c020713070b0384445401034000c0d81c01202c0300b102040c05582c0001480286650440c1c0349511a03650740d40060110100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 696974946 1250 696973696 696973727
    0x50c03040f0906050108060904080a0c14030706060317071121030307030b090f090d0c030e0a030305030906011712090d2301200f18090705040f12080a050307 69
    0xe030400150304209070380f04008a540a1321454104e0790740404020301d00c6130032100904074040410a150009220f0b425aa08880c800e100c0400050b000c19141461500140350846440f542d541c000e00c10300c980c81c110301c004c54980c0301d212460031070155503403c0c010803c405a94040c1c0c0080da00e24188020105520714034024290440382c41c1d182c0340c40010090424200c10314000e0010381c000c1004c01c5d65151a05104000c1c100c02010782a82e4013000301c501c1c7c10103500c1a800c000050980c091241c1ea2001c908000b54040ea640a80700e041030210b0340d040042c1030707010940a084103100c9004004012541d803001066122405071500c09000100b0180001c150000300740b4023a002c0040c0311004511008405d10503000d00801c0000d410b118001040c0400c41d02001c2e00c0c15060007040100d0300810001c003c40714204c1d02c01000c82107481d000c00d44459069442d078011541c080303420300c0810f00c0c14a501001f0501c4401d11051105507894102c0e0714480d2650240c00c01c0780001c0014130704c500412403c04980305 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 696976196 1250 696974946 696974969
    0x130f02030f062e1d1b1c051302090105060a020f0d1d0f01050d18050a03020607180e0423100c0e150405060c100c1218030f050c0304 58
    0x901050b0900e255021800100110380e1181c140d1040000384210038041da1080b001c0002d11240e03c00385100c030180014104940c485000175641c045422070b801405103000c0c041c240c00e8510480f1540718043d2100201203c118030038948208002d0f9407004010380c11507002340c0e4840d584104e9940201d080131000580000f40d8480c100d000b8820316488141c1c3c09011004e030f1803142c502459501040722040214808a0018006104144101041c0d07403042c0e0040709060824020ba81c66546c8150400c0d417501c0040c0c01603041081040202c0c0d0300510344100400c610441601224189000610000005000600502508a00840c8802d1840000e25510940800b1100b0012608020314060b100300b04c00e10700000d00d0407003030300c2e00303800d22080c40c86010020f0350703419042c5030404040c00286e07080b005c201d101610441410800005140c4a219509800c640d5800103030084400f045007030301c54860040703e4a01c00005030780c0109505c4085299554a140b40032544c91510302220f07803031401036404c054103005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 696977446 1250 696976196 696976201
    0x50618221b0e04020c10020c0109020a0b041a03010b030109110405210f070503030405040902010905060d0608010605011b02010e030106170f01060e091203091e010b0f09130f02030f06 80
    0x1189101c5008001c149507540d182498a12003400280c1c00f078040780c1007140c2d006c0008070807015541e0700640101420000001590b88298000456008a50f4020036103800001410300141000701903d403089000500010301c1d44d45421107240341440140f0440414664035503075102c09449401c11078000740300c02000da43c2021911803101c0d0010a2000342000780f4884c00b001e060625030049034140440700001d02442c2014035141c14000544200780c2c040f41000400e0300c000c15566250703000b41050025602c0b0004001c1c0c101900f443c2114460340110f81440440c0705007031901010346100340b036000d1313083ca41050025441d102090150490380c20030482112508500e00840c1e41c0001d03c185445060741c02809019500d01d1401c80d50841660642d8058100560172690004180e0086070048085801c9512203007207a00488002c00342960280c0700381c1d44550b0b07400324620303056046990402048500800780c4c01c1c008070308440844010002064095010018001d66806221400c201da003600d081c0d42562 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 696978696 1250 696977446 696977471
    0xf040204090c032307060e2403090601060906020c131802150d150b040312090b030c040821161509060219080103260c0a03110705061822 60
    0x400c44c8a4440120341c0194000703600c15480084c9920440f84240c0300e1906489000040c030010b640308801030901c0c4042094400b080142c2d150046229414602c050550307541031040041030300a143d44650110340c480c25203450f46640301d442e03815400034a08400251701016040614002d001818065885041403421080200020000745004c40503003e0400c1080d14000c100e11016a580c000c039a0b03994024001440007800c0034000a900d0003450509514940d51440421480c1d80100d403102c0d200500810100500da05c00c21002001d41080400040441c7e40300020705070a02070004140342c2071108a0062007440201d10ba40f050f9000708410034800140c03103080600c007a50280780c50800d50303450142200c2545101d40744150507a0380c040814101800300d1040c0c07a00c2e075214403100c1c1d21404410024003c00c18020850980c0e40d9119403280c044102c40c46040b1030400b010f5130b00840c05800100140a80111950580050b00104981300b11009088100e03015612060310b404801151810f009881d60 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 696979946 1250 696978696 696978713
    0x20c0a03051006050d0b070f020f0d0e2e0f030204120b01080609030a0804061a060c0a0c05270a0221040507060c0f030e030c0a06080105091303080f040204090c03 71
    0x21100b14103014020683c0c1c03041131000c0903050ba90068141444000800c00031842040c400721000e02d00e204136010b0000b50041070303040c100d01d20350000c0803031180841c0d8031007410544800085004920241d0590305034040c411641060b810300c00b00c080102420714210118041d03410741c4c028000041081c40d4981c85071800e41c0708803200f03008000d41442020b0008640001c004100c90041e400c0d55241c00761500c495a80001510400103420303030318050700d1040115038a0b901c015184480603030340189801c00080c1000d0342e21b1107043e00010b02a4110f0a000e207030726a11014001030102c0b102040c0e641a1b40d03600c000100901452805850041d025038803c00466070344080f081c002d600400a0720b0405984d583d007a2003013440748400800326003829030a00c0100e80140313502041d005016040d510a0004180051000d8649410000120300070360010b03c100d04000748000d60081701a10011110031032610b01809800d40100203507030182c10301000500f152250341291b8540c0358000f00e0400801c2d183d1404159 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 696981196 1250 696979946 696979963
    0x1107080f010b0a030302191106031906060905010c0b04111f080109140c1b030a051e03060904120e060f0a03050f010e0703020703030b19030213050f0115020c0a0305 72
    0x1400d6007004000c0a180c6081c0c44000f0131280d240d00142198070814046000c850014101074078000351180c08000c2c00c1d21214000c51040e03a0207020481140405103500c42100c080d030300808100181a0018032090b41c100c503e4140080c0c02000145450b0751b03501c0c060140344104e0345210380001002c0000d406c04440c20841d00c81d628a030780c1350107945130380307400c0414215a4845c440140c08014200030400300711420000f001d40000c1c0b1705103c141003d845881030b00c0c41d84141c42a40c00a130700041c2d19000b42482d0001a001030111000051860400c81c00080c80c40c90050070280c0780140140a20303041601844c0b22291000001e4010b030345680c1992102c091030341222182c140400e09040028121030802d0103402c5c16581c24a080d161380d901e42c944224001d40100304120141035480d9802c42840d620910761206c07610300016500e48450440c03040c0702c0301103a01c00c04481c00c24184010b2060300c0d18001d501e01e0654080348040da1000805240c221b00c0c0c00e000d5100340350060361078080403003403080c041502c50 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 696982446 1250 696981196 696981223
    0x3150402150f04030201030e160b03090f0f0c060c07030516030c050d02030d18030c090504060b090c0412030507060c0e04051501021b1906030c02151e040201110708 72
    0x7040d890000c0111914400c00314240c001900410007880150300030341c4010f092203804402c4400e0f210b030724018413000c1406900320344120748010040010600302084040d0a2441e500050030340c0e000c005419966403000e40e41400d10440d0007198003e0a0001017050100451b0072104880c141c012561030707035245080c0f600068610540010010855007040401250100c2e8064018412100244011203d05c42d81c00e0f441012080b41c4400000416524089074000c1d220200d400105410980b40010449101d140405d005200d840c1c10801d00742c0010058400f150415140141c100c4440e03c0c3c1240c2c00d11907544000d110620740b9101075000c650003140f450007503130103940c108480d0700e0f8280c240032a901444071980c0180e0058241144003c071110601040783c07406007070003000f07508800200c048001160030000009645840203840c2590422002c04a13003080581d010385030804104440c000384e2039401c1c00350390030303185404903045902c034030380c0044c1001502d01507400054942c05829202c030710071900792 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 696983696 1250 696982446 696982459
    0x30f141b0109150f0f050c030c070e09010b130b031207080306040e070b0d110d0c0c050d08150108090a0519110603101a0f1305011803080301060c1103150402 69
    0x1c5055410012a50b0510b08207071200c1030089901d02046031170354513252000007001400d0050083c400341c00c1024020082d030041c09040c6a504091880001120040c040303041a81171440d550003a40b00c1c510085803400c03900c2030200e080714886010030714001c000040003403100d4001440b40300f48180724000c0c5004a07000c84091110100d00e1141c19543c06050080001600080080501044a40d030020900c04a01320556040000340c12001048510006450000c03851603400c0d0400c010043c0211040901542494a000c0c00d00489034aa1180d08812441c14865408041203280c0410440000125030040440b180480328400d8640440d402140444064610075100c100d940f402d802681c4c81050b00a09200109143c2890005150040000300c099200c0400244407503040d010014000705055900d42c420503072602c8001031076440a4500c000041d0800750051001820580450341160003501e0661303000301890820000e01441c041c42c0395854801c1254014507068403510043c40b03a8000c60b040e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 696984946 1250 696983696 696983699
    0xe0d030c05011401140f01030e0307030906120e0c010c150603110a1d06151c0203011802120103081b100501091107030c0f03050d1a04060801060b04030f141b0109 71
    0x628551103001e000f600d0042044131707602c02c0e00d801c006810420708041490081484111410010b0031039120090580c001003002c10280328541d0440641c1140c11b2803820100302c660040c071312054440340441000d90400804007000400d0201c0d4844202c0e00b241c2000040100954a180540280103020120b600854a1346d4001507240e07142161418a8801d58050b59603640d500301c01c11586542c0c06001206d10b802c1406900c41c080200c940d55148511413080050782e9505210800080b582c03e40c2c20300b400280104191200012164030103030460b45e000912a49a1621413030304a401021600e031b254052144600b880082000f640110303040303988e4580c0c1005a4041c0500c074016510401c1d10140105101d0b6011000103840c4290904103c0d01074680325091400302c0d004502a42ca840c49416510038081c0300c0c03010b1500d824841c1000426209008010507490030052108070301952101800030003040006105002182d00b5101d0003403d25000d9416140c0182c15440103860f1500c059400103400000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 696986196 1250 696984946 696984971
    0x721062304150f0902090105120f070e122109040f060509071b0b06010c06051e01050108010f0501110a1a040b0c0f040308070c17102304020d030e0d030c0501 69
    0x40300b80c01d5844485071020851300300040071010b5489a40014108581001440c00c000300020034140201c81e5041c03409000d080001004181e514a4030701a849002010050608400000b400390002ca684500d529011200c0d103c1d8001c10380038024810b5041414640c0864600020303501c07201c1a10002ca4040c030142d2240841102c00c810032401c00038540c00b22100740d101096034250050b91081c01407410300d81004481e43c804d829a801070381c2800400b1520022a4541060340341400e01500c0300f031929400079803400c0402c0c00a6200d0f84030701814000c031400500d0700c900007070084000154005446051070100341e43c52400e45a41200c040d0307440c503e50008100b013080c1c80c800321040300c42c3d02415030f81010b082d038803600810391003007000321a424848500001c9060b00b0201d910110304064001d00301243c1034860400558114516420313207554454100d0f02048004c010240e003207174058a40115402842c50b083c1e0b08419081c2440e81d005481d074000d001010760000340c10309080d00c100300038013036001c6028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 696987446 1250 696986196 696986231
    0x1308060c040f1a09060f0703121401060c1406090c1c0807151e02091003061a0319181703040c06030b041508150f0721062304 55
    0x200c0740040d08100007000781c0c0300c070000401c0e42c1448181e0f5152401e0300d42da001070040c0e4010360800c840c0c01400701c3d400c01071541080d030303004028151603414040c041d842c40708007501003814081d04061004207091401442101c0300481c1d042141c0d041110030605103016072076507484140d00e10345d106511b02103401d254100449040100b49038400c0c0114103101c1c1542d52480701d1200d40035240300c0306070303079841051800c0c0081c50089070103000840016902c8078050b041c048800c80600700b070020700d810090100300d5010503008504001c491041d845840e61030300024079501002c6101c5445a01b0f04007034611a401072144000039045206461642d541988044912001c1c00111400b900001e0007030401c1200c46d000340c02500c10018010400503551004240322400709125800c501400d030301210b0000da48110541d03440d42c001036183c6005409180c8014002d2100009070b4040c0780d04004111540306080050300941c0c040c0c0082142c1c90f07482039200300013015481201924a104508114034a0448050381 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 696988696 1250 696987446 696987449
    0x60b0907180e18011a0a2c0a0b030a050c0f0111060a0f02130f03060509060115030e03130b071a240a0e190b0429151308060c04 56
    0x10150525803401c80800c041000007000381001c0506400c94a800f0502031080ea580556000f080e08400307060a41807205030811600418074509512951640540500800d5000d109032441c14116903600d514110010b000c5442c901c9130503200740410b600030080c011404481e541d2090341e051410601d40001100d0f1b24040001141103a04964082110081c4c50f13005880311099102f000740c0f03811003007980c3c88010b204540c8280307444a546a02130042212500400d41c010f42e18070024105941400c801403412002844500103050352000e20646a20050080c0c544801d0b1640d00c01007015910341000a880d4009102203070030190b504207601095042001817401160031072100415210b02c048e058160698000c200d941c808000e0200241d4005072243c0c55114000c0104a0004010050304000c19942d0070b80803e48240e041c0303c401540f044403a0782d5403200c2c0300543d85985402584401054882c01840031817414440d002a4150910170052003150032071b421002110516030300c200c004201402503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 696989946 1250 696988696 696988727
    0xf010f140402040b012d03110f090d030e0405011d060a0807180615110f01020c030a12020d050c0c0c031504030c0c080a0309031a0f06090709050d060b0907 68
    0x1480c0105016061692207801082d8042c144024010920310042031040121a200c0c0c4440c45103001800b20789a15019041c5489100000b150a20000d101076190900801c441c80d0702034501202c1d80c00a1500c9281c900302070041c00b400410503540c542416a00503c0f520480d1140c201c00e200104031241040b1809070100d030248009000494148807002e284c47c1d1030f180c2001c0d0500c1c0c554401080340c00981007070801403189529a90442414100301c01d0038907003e5802c0007a240d105022040c8102404400c80388040c1c0036141c0300294100c002511402801814406280740b440c20040100b00d2800f040103000c000c00600454020300001802c05075035410070503e40241000c510f006c9400a4015072a960750340d80b01e00c1000e201140c81d03900e41c52034190b010f201500090704541c001c109110b401c02440340303084441020400b0b03a20b025550505403500182c4410302840d80c1d800000d000d648244680e27030240c84000d040c14040c54a41c20804042c120b84034401b07200740400004240700500a8200c0101600d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 696991196 1250 696989946 696989981
    0x1b0a0303230720010f0b0108010b18010c0309092409020a090905090a140a0317070c02100201020d020d060f050111190512040902070605070e030712020409140f010f 72
    0x7200c410031905105000d5840025620354004074543c02c400b801150004070b0314a20000f00000c040e00010011b40d8180d0180c03001d00b41c104602d1807807415001403001d61120a00b4113070482138280c5421038843e8040d5001442e52440c2c200e1003a140380040d1003283d100c0713407200e01c4c0c060300b1038803071000c2c100728400e1003641d030041740d0981d82c208100303000c1c0e07081b0380da002102000f0340b06403150a4580f001000e1240d01c59061541105803c41304064110076000042c0e0007081d00c020b518031303704501408100c60300b00d0291040100b2a0a400051b100350115404030343c03c88000d40d01d650b0118501c0d030281c0018010300c854a5421400400c580d40301e0415112070403c00c070020000b1030082d110b40c0c0ca051400c40020387d0280640308030700561b551004006c200410049400507521001420840200c0d82d0191072401000402008040b007a80c0001e2503105030382e5079041244030003c143c070014004200b032010090002403480340005900c03102050540f40c1c007c400f0b00a00001e0892041c4504680041149405020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 696992446 1250 696991196 696991201
    0x60908180109060e040f0605040e06011509060c08030a0905010c0c170307050f130305010c08040213050c03061002010615390f0201050903151e040c0603111b0a030323 73
    0x1505c0c0d080600042c01002c400903010b921100468244d9496414002456001070010040b00740300d4011a282d001c0c55103042c0c210203003014001000326100110203000810f0210100780450900d0b0300c8407112030f82c270400070004480d608002608001c5940c4003610008102c90910700910715100450384034550350341d41d191a00f41060302c409120f81107400150040424100c3c084000b85c8244100c407000521529030200511300b901c104915008107c200e18000341c1040107120b001c100130002e4a420103403ca61030084084d10000c01c80c01042c55901070480c0b08100007260711000e420100300424110000c0300e0012640300703110040d03403600d1500b0030342e40000940b009500c08203070003103203030b52080f44145000c078034100ca0f400000703140026050b429008861200c061154141704902079080c500381a100c805030354a031a03198400358040c030344284401c0c543c4038801c2c40c04c22000300044400130301d03401d900d44e4581460440789607603c1060030000c601091400c402e010940300440c4404010380341c0c118905400780d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 696993696 1250 696992446 696992449
    0x10807090b031c0201021b1606021b12030c010504060917090f060903161d1b0a03021303151d0a0302060606030a1103040f03030f02190e031e031c0b03030d0b0a03060908180109060e 79
    0x5410080040ccc1c02c9010511084088000038040d0b00d0050303000d048040b490030000d0030071040401c5640f040080c5d21800300103043e080d4580344e040310442c61088460715111440e4030007003401c288181d100d0194000c00e90714003189500a02200349010350346400455900e41c2c40d04600c0030801e504e4901c0403100a402e01004001500c207400904c5e00c801d151030440205a46c03075540c4546210380b11501c83c1758648910940e04c42403007113101c900c0c04403c4040242803440264a01070b40314000070700020b02442000000800b0312030983c014800340e00304005000d0b40ca10301f40c20004001c0c0e507480c2c011000079040409400001c0b5003402907480784080c508031a0004100a042030306c140c814800425090b0284540002440707040302c441f40d40c40c8a1304400355a072020480c114604c02051010700c808002e2610000070342c00d49001085c1c92200321907103000209001301c0300000d0003403040c5a02c010011402e280581e402c01031010b02401010071604181c5503100303102c2005541034410b41c0900e50006584280b0031416 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 696994946 1250 696993696 696993709
    0x1605250c091404030f02010612150b030f1b0a050901120302120a030b090903040e180f0604150506010804052508010c08010807090b031c0201021b1606021b 68
    0x111441510300e42005075841d403034401610100030501540c50000410002410f4102e8141d000c01d03000ca1000b000100d0602d1150321080b201c0c0b103c0034045c88110608001c003c1c1c06c0f54410404903500800316020f002900c1081969689441d0500344000b5100e05030704940d0504407110710a1b00c1000b06018102d81c00c22010300d401600701c1c00b0980441c41004404810200000010403a480e004e40c1d01140c14880101404403080c4042c141441d5603000700000c0220800c010080c58000340f070101c01c800040a031855180ca0142250701414407405007030700b0300080002e0590800504080e0076030510840c0c1c0d40e07400642d5245421140540a900500074522a011001e072042201c11a050328500d6079540b01c0c0350507400c40740f02079941030202d0302440040c082600100000c0d0014002500c05100c660851004642c48446a0084c07036600358440c030030110007078004c2d010b844d4040740c064a40c100e6904140c541981d55003030051001407042c180c00380460400c1c8040b0310118043c1c450f0207000c2145c01c1082c00d0007203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 696996196 1250 696994946 696995017
    0x3020901031418011a060a050f210f01140f061b1507230415031404051c03090305040e0c0f0c030c070609060e0d06020c0a06051605 58
    0x40555988603442210b980c04500d0b40159444000c0038030407a5182c002c9821501c00c0c0c20700491000118080c5500d0b950383c00100e9400100da0314181d07440e0305c1e552903005607a0055140f41003040e541d10800e00c040b01801c609035441105852025801c0340d0742c808003848030912115190380c02c094a4104070740c0a0070100014107281710340f220071041d0501d025840a04000c0300e02c248030303801100b102c01c2c0b20585a0100780a043d0700d04005075007554482913844043d0a118030712031000300b80342d686030680065002c0da00503e105094404500140d00e000d150550f00c1c0d10700034200311810010300450b107070960f1080c4242e00c0c40c41e5264454502d002c1c10328885039080750004140c1101040c0c2005a840311407480c03805000e502d42d943c401180c80f050641912070818100d80c00c09010000300c072404008580d4001024914080c0c02d481c1109407540c03508044000e40300d070781168044c600c00e9044a5041111580c0854807400300b044115510a140c4001210360f84103203a40f2501f207050400f00844140d044078076030403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 696997446 1250 696996196 696996199
    0x6070b10050a030b06040c020601061e03020f03041a0f0105010c0f080d0c11070b0f03010608071e050703080f01030503040b03090313061d0a030b0115021015170c01080106030209 78
    0x90304103540781c0008011a41035001207070030044900c00d000c4182041d008100b211061400540480d6051410061041403900629603682421942004141340298101c0f0003852954801d50f41d6441d1500f0403403422504503070940e0b194203403600000c0040344181103082c16600e0507907840c1c0ea014881c1e00c035103410348007036407090350041000c015400911f061813184041e0049140c55240d0410000d00b0300c0c1e4185200360b13120245020b020811301440c010050202c81c151049801e00310065200e0460403a48150144001116003181c220008010340d089030103821158441d54841d8540c0da220114090005028400107045a106100c14080c035021500559440400d020441e81003c00325001a031542c246c5a10810210341104c0080030546050030b00404021401c0d02c80703d258078915500e60710035201c1440354038407000c40c0b6228294001c0c400e004560426051100030f00c05201c52030440507a0550300d00c50b000481b19050005988102c0100b4004480c1d03d0507140c2c403540d0303032070030341d040c0c01951280307900c02d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 696998696 1250 696997446 696997471
    0x30615100309050c13090b0a0b0d2a0806100b07020a17031606050a060803030609040308090f0f0c010908070b07031d060a08010810020c07031104020717030603070509040206070b 78
    0x440c01a102c58005c1c00c01c0040100d000300e10002c01d400d1070f40c046803019040d01c003140d05042140c00503489114020a40703a903c0102c0c003004161035286019401803183e00074088601a20000400020015005028080c0703001080c0c000d03980c0320f07400b21142c13080c2c0c90005c0d040405c001c01003107111b4041925101d004000d0060302d00d0701c0b01e8682132501401806004960b500c2c0d440080c00041c80300c41c40b42001410113000103603e182450310005184d540c00400040c02c000000000619065050101200070313003d03801103030031903030b8520b135450748520b101d09500b800200e0701200018800d0b4002658000c40708141000b40c505403094808035080071140076007903400c90441c0445000c4d1748800c4000c0000041d6607503103004650412440d141041c0b0010310780c3c7c0711640141b0860800c81c10102c2e01404990b846040408501c03c0a404507010380903562016100c04007004c6070409649603e40114886d071811802d441c559512441000650f55056402a402c54820300000300010025060140c0045115021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 696999946 1250 696998696 696998713
    0xc0903081e07080c0606220b130f0b040c0c030f0f030b0d14010c0806062508121609060909020319050106020a11030105250509090408030603061510030905 68
    0x101900d0b9030102c10120343c88440007031000e0346280c042c003840c0e8229500b00c901e0390b500c071749a4040c00a026081c0011444440d600c8246029550342c00003101c09183c40b0700b04c20b00920b81d42c50f50340801480041d48140c000c900303202c1c0a00c84244101c1580305c2c10355060b1280e040c062020202100c040e0422503402052550300d00c451100c0d0b0340d0704860004194402d0020100d0000d402840ba400c0d04d0401100c8824000d20206010300c542d60b0384280c80410381d14202c0f68110f0b1055201941100140207030152100d100010006c0c1490a042805c0b40b1402e130790f0482907030b03980981a0840d08250603116401c00074000034414412407601c2e80003507030401010b05a101e184014450520201d800c281d00c040b000d03038008140e000802035074010f01165000114001c001501e4400305410780071002a9020035440d03250116541090b0080040e1082044050700c5001d9510781842c050b450f0350700990304907129200e224002607414118440030180c0c0700303020341010034801d1401d038240c3c081c000340d080072100ca000300c000d0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 697001196 1250 696999946 696999997
    0xe0d0c030c0b0a0608011d0309010f05040b030109050612060603070302040519050901020901140f030103020d0807080f0a08090102070c050f12120d0e03030f01140a090203040b16030c090308 83
    0x12181c3c002d000c68500064240d1916460500b103500041804918401071003861003003001c0441134504024007802c12071146900310b00201c1e854425174110102c00480400082103070015a40014460301054640320140e0110001507a524482144c4255059002440910050030950031690f0091018005114018031240078101503400480300141669070100740010b85d0340e40805010400d01100220a02d007150142da032441500c41400083c2c050302105200004211402c000c40e040160082982a2984200c81200b03500350f0050b182030002070243c0003c101074203c18402c94900310303401442000c1da5481c0000344208002c074a110320f903000c0d00b000342c21040d00c9401d2140c59903800741500d003250307550051401e1408a4140c0105144650720900030000840845040305041d0360710700100d098000c01c44c00019103442d14580250400f50f00100500c41040203201007580542d11250f82c1c900c0118040b1012802c072a0326450400004d80c6504007000407a021400030a08208101d9496011003041d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 697002446 1250 697001196 697001213
    0x14040b0a14101218060b06120c0309210913020412030c0203031b011e05041e17070302010c08091c1103040915150f0c0813030219050f03010e0d0c030c 66
    0xd03402a0001c4985503403010404180700e0006c10100c21a0010308010100452080e59030000703241d2102400000b01041164108000444803480b000d10304440c40380f00201824416041004800e000790b0b1020f100443d66034503402920180d0700800510080500980c404540c030320260ba0051340c15000c1009010900500000d00d414082d03804000801c00e800c241040c41982440c80292004d11440e000510000440020907511900c5462042200202c1581040c1c54960070081c22020003c60001d2140c00b00768041d00724403d0900b2940f82e0308280d0791400a441d0703c0b00d03840840070850310360412190075a203002d003005040c00c9451108403401c0503200d40c414400c031f0720b464581401c14082d00404000284841d5a115000c1c0080e14008908048680700982011100940240341402c042010340060200e03032031880083d60003c000c0218001d201901143d404041d0052034090b505003900705042e03040500070b400103903209a00520403040f210b0340c121141d11090030110f04000000c4c08003400700c0c0424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 697003696 1250 697002446 697002461
    0x30c1113140c12070f05130e090d0306050102120a030b091510090609171c1115040206031f030501111b16030b0c04080714040b0a141012 60
    0xd10004000c0040e06850002480042031000c40d00700800078521800720050006130410320314242884081c038583c409a03054007808500c101080480000010741d002d01006607405941c100080d91909512800100c0580d1420300609026070301c101c4602c035581c503c80c8010090500185800a90459440300040704100151181d8004110102a1400c10328100b03030740200d550006e050040900c0d03d854406886101c1c1c0740304031114903000c1e0b92509101c07442484400c400a82182c5100111041c4000c0904662070340c0c0c0c45c4c0d905900c9050385800301d004c0740701c8205000c0d03500100b10b9804c41e500c60000d242544c03134602032803940350148a0b0001c000b80d0309000e0803101000703080207a900d0309140c003420414001403130b144c4081e0b40e205c41c0c11881094403022145080c3c1c3e0300705210303240b2542da610b00404548070f11760007500d05101da14ec0000b50b51480124540040a0454003400354401c00b07000c020100205010300c04010721007030b070b82007076616203242c0c0e1032501c09590420709450711403048488111080c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 697004946 1250 697003696 697003729
    0xf18061803050a1401060b031302040207020111060f0103120309110405101d04020118060e090604020903070b04091104180209010201090c0e0a060b0a020a060504110a081b06090d030c11 81
    0x40d82c1030313482a000a0090b0700182031420303d4642580b40c8080204007007410040301030b02950340010702d0000d5902c80d42b82c2110150002c000c0307481c90704103036a5120120740244400c1c0c6a0a0a403c04040c8161080c0140d9220359044250030b1b48242d65401003000408018107440d50b0047c6c006800101c1003241848442080301c100305d607030550b107410f000160111001142007009810b2103d814000c1355002007039143c51480a0354028036503560360003c0b030001c0c42085511a4148140c1c4000604210310728020b009955a084061040e800074140721801402030303005108139500014000b0a00da041680644a0340005100102c0d55034171688a10300c110009404c84c1042c1c007103210422581e44d120b80505070041803a5491b86141895140000351506d80e2810b000303003c0fa03103640118042c0b00d040080da51005900074880301c02550384d0b42ca020343e030710f50140c950816500c10408451241c03902e4411b070742c1018070140090b00301c5001c0755001c482003094000100d4030200700101005090f182c126029081c4d40300b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 697006196 1250 697004946 697004963
    0x1a09030610090c0203091c0f061d1006060c030f0201061a19020d09120204020c01180b160e101e09140910030602070f05060703020a0f18061803050a 65
    0x5104090b01981c080c0000c600c20355004000e518059180c01680000c0210501c5010303085c0324141c90004083c815aa402a00f040d0809410250404a040a080c440001401100c01e000780b1001840c0503070340244140c2c404628000c002202090081152007501a018400010499100c2084110002e420041101ea41502044440025000e254001c00501150000b0140c401c8400700041600c85540545800c0c00383c190380010864540340c060b200992689402030201120003401c24261980800041d00e941e050500804c01c1e000316105000d10a616655452a1140e412014000c0c212240750b41704040002c4407542608245180000c0b0308e85200607691201040d1400a42a001e002443d440a106140c10000e0001d00c0d21482100401c40307a1003000561164940e0802140700d84000001030040d00402c4200004a5417541c000c0c000a50300d030b1030340c529440c0c820344100d408c1180c103c48299148441c0c0424400c060003003d103800d0024080e021b015689481c1d80d68203090130800c0604807181c80703 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 697007446 1250 697006196 697006199
    0x27030b060d150c141c022a160b040305070b09010504170a0c060e1f0207051509030709060806040201080a15060302190c0c030311160308030a0605060f041a09030610 72
    0x590041581c080e10130b07485842c504000b44140340440200030450b1880c0e82c5c0e54001000051000b00c0d46203600100d4000f11680b401c1d40d14107041c5501d5800c083c0b4002c0c0903640031100481da81401c1d200341d80c16281c001c0e0023001c419041028400840d071150122078140300050000040710901e406d4440c45150b4040e010340f018001510344480d40c4140b075003001c01406001c0b4018030782e60711406410300075222040c035400c04115100c04141d0800c1103640000360003036070014002d03180d540750340001d0012110940494031000e5450722000122240360103140c0d2250046004640558420000b1a0304440030390000141009006a100700c041041c1e48001e0100360045a2000d5070030900400081812309800d10a01c1c50120b1303590b24400b8039080c080103040c02080031080403415010003400f890050082088036546e5282d04140f040d0341c00859010100c2c1e4103002001c69076007008003d0305d140f1911481307a103081500301409101059178410807000b00c2c0005021400e0b0aa404224140c000c410072404c08680343d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 697008696 1250 697007446 697007471
    0x90204230f0106020a1e0b010e090f06060904081e04060f0201180302150408040509151918020702010c08030406050405070b0901091502010b0301060303030501050127030b060d15 78
    0x100c00800700c4410050907401049525001724420081c69884076004960024100f40e5003401c484428028100e03180da4000400d4508403800100c0c00f68400b03030b0489418060391210903584140480305690403804001c04200080e0814014100c3d142d103c500d006002c40b1500c0400020303400075480103000607608582c440700c04d60288a881c2126007501a001c2c1c00002d944c83c01780d0303103000c8a8400d07001040c1000000c0c05000c00001918041c150080401440d4185800e0030061804080304d598841c1880080c241e00d800281c1c60943d003214061203d0407031f0b006010f110b100003500540d400760b05002d0b403407110100140c07031f0000a502c81d038442c0000181c6070a190034007510702007494000062029003004619210317030700800114101c0d0041481c00c01094000c44041b4090845581e070700d40c040d802e0039000310806070107070440c80c160340c0b0030781e500390380c03130300e00c80d50080161614a4002030040d40b803a0341400494512500e942d409800604015000103965591080035080e202e13904000d00d40c0c5140b40c1c0f0381d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 697009946 1250 697008696 697008761
    0xa031e0203071115060d0c170a0309060f0f1206030f080c0f060103080f090109080303240a120807032001050702120304150c1e0201020c0c120d050304020103090204 72
    0x240101407001302045840868101e1007003070f0103003400c3c2c450550020514200002c0b200801d0107800ba0106589609042c450950b40d1078403414011401304081c0c80000c02c20340e104400d0489000c035259110008092088402e0f200121900310100c0480e4982e840400881c0000801c02d40c618414500960703907051003041d0600300440001092181d4001100400c042035000302559a403440300400c070340e03a0703100d403074016544100d0b1903109942c6800088100205420700c190041d51807160003006041c124809820440079a51a000b0444072802d00c002110104145c64040d01c0c40c3da04c2818070721000341400d0004d04485a00c0152441d243e0b450740c04001c0ca0039414440a91182942d039403250460500750350b17082d00b103220011a0207410b540e481d5900003092060700d11102d82e411843c110111060b110000a02035807100c0750341b0015118441c2c1030601e0381000142c049581e2a00c2014200409543e801100d440d40050020307810503844000000150f5031381d01c15400d54224054406d0225828106010030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 697011196 1250 697009946 697009967
    0x200301050f1210050c070f140c040506220b042a0509011d031203070527030a3909051b030105010f0c05070303020708070e09120a031e020307 62
    0x741010603085038802d070000900c095400c603008000724a56903400e15a00180c010060007920802c008040d24043c03015000413549192000030540d0083e40c6102d0621042e104140c41d582d400c030003410901942c028a040c080401d2001c80040403940c00d500e907000806031a823030940c44007010303400095658443e0b5911000440440903007011400c01c60b4500010703298040d002c8114080740400046003400760303800e0000b00c20a0646012142d01e80c00c0841c4010541d81051050786d448101050070b511300d91702d04a50030000c10000400500150301da90ba44c40c2139040b6003100390701103c0003402c0e400d0703150208000312003541c88800002111040c03421441001790b89003c0d14216000c0000d2640881c1e4840e000d040341c0c10f4036000c1c28280400013410104035a6000c40200180903805a0707103001c401c141c0d0100fa500c04465400e4129400c0c1c0d0b4681042c201010800d4819a209500108085581d00c01303080c013500d910b40070750400040c0c854107a400c4002d65040d9060480b8101e500001b041140c030f8002e80d8048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 697012446 1250 697011196 697011199
    0x150109050606030c09010c0c090e16121112150720070911160804030311030a02101e020a0306090c0c1a1b0d061a090d0213200301050f 59
    0x214a0501e107000c03905a1001400c002c9001c0070015010213035034002c461000d5070300d074020305c1042041da88001c0b0100038110303490007140e503009146400c40340701941595041510561030140d280e41c1e40300d9407401c0d028440c029841b6000070b8290f40c0b681400c58144040411461b180703480d0f6910b0314010030700515068015a19928041c080460024540350000d00c10046d03402c1580300180d10300b84d00ca694941806002004400700700c00940000801032540c000d80201ca2103511007088a04d41c050f1142c1e2a070103550100c8004be48842918029500c80e900198002203031002804052643c0882c00c0c01643d0020f8a26400b003a00d4100402052140d4400c0c01041b036070528000142d0602c07071366030141d814030b045052040c0704400d801085020105c4166900c58640c504145940d40b2441c0d444040500150b10850355904040c099003040081104116a0342c0140140030781d2180c8602d508100002030302d401400e00d415038985030610140d0b150444442240d1aa0802588a42c0740100704004000d1400c1c90300d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 697013696 1250 697012446 697012451
    0x14060a0c051c0605030316020a0503060628090e06150306010f06052512020c0a030807020904060e07273b0607031e110426060405150109 60
    0x4a5110341c014151499003222014040c1141c406000302c0002c3c20032600965454000025440d0300b5110941c04400300700d10903a120381c12980d56404268448001329a051b801a001c0104e1412080707480d4079841120850142c2000d400c0d40b035902150840d05860140e03005580114140f100c072040074002000d44903c01c81c024280c940c1440c424250681803407041409001c130105134900c89650000350103012605e000403411042000d41842c1c10900039480501c4054040c0c183d080348a030030400000700030740b50820101c40c5002c4141c2d00b449442e01d070040007514555603448404400d0102440018010800b07132504400503140d400030780c03072404850b61002d02c07020f2400c2d5104003000d100c05c180c4c1c2d200024510b40000100081d515407052003c4402c02e022071809140c0820081c26019800b83c80d0010032000302c2d10300c802d000504c402c1141e9a04047c0ca0700300800784410070100d501000742003c81d42d02d00d120050021100d480f168038200c01508d00b21603540141e00c040304000015103180703005050a181c103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 697014946 1250 697013696 697013711
    0x5071b0b0306120d0e040b010c020d08031f0b0a0804050313150f08040b04031103070605091b01030b011e230301141c0b06041b0c0507090e1209030705090414060a 71
    0x2034002206217260f580155180e01d051501070380242001c455850700a00030700603445082c5002c04003075104541031544134000b102c0441c190042078030120180d8141882040c64074282d0102a9550740008208441c0e42c84200b06009a01510348a88801850329032442d07148040c0e00f48002e440103000c1c0020341c0421851000b0000840c10001c480e0f500140c0505001414240b404100c3d0700b9441002009400e207800c03c0180f0080180000b06618214607140f40d0400440c08000110309a5100341d9140d40000d020385501400f0b22031000b40c101c007400c51810905403070700c0811000b84001002d080f592091450101c010002c139865030303000903500c41040354181b000c81040036652001d610720701c0000d427445014000140f1f50351070315400902d8820031481da912000a03c1d0700001e080b50034a0108032441c1c05581030000700e44095011304003102d0840005811607a500300350f1005107800c0640d0442c1e040c80358020000f05a11002c01d0039010301d02807003072710030b0000104614a2400501400d46640580341208 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 697016196 1250 697014946 697014973
    0xe010c020a150504020307050d0b0106080f0405030d1508010903170f10181d0d020f030a020309040f023c0306010e0d02280f0b0c060705071b0b030612 66
    0x640711100b031000281c54a5a00100e80b4200c44c60300f20303d40100d43c540d911028810292500da0480707e00c1d560780204d540e9051803120341c3c0d901c1a10028050350040c08044000c00d00390b0460b82c0030035203001d10010003554404415095a4500c542980400c87c44010ac03001000180d0710140e210401507041004c03410310403c89000543c9500c25007480b00b0310b080030f403014480307642c0052642c4203001c2d42545000503c182816203403030080d0134490151007411203c002c84507010040da9100d45454001d9402c014a4100344400b801c0420743d0403503815070130801c0b0b01200380082e040c0360441464141c9440e02c402070b01441000d00314401015019540d0910401c02d0aa038080a1840c1c4001c050790308001b100210301c04203285925a038060824174105071010854140040381500403101d28020305a4172a58030750900f81d41d0b10946039501c4e059004040082c2e8020300540c01400301911500791103100c010750030701d40400300701d04e130300302c0301c60035500205004140c504508a0420441c00101030400d40c072000c007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 697017446 1250 697016196 697016213
    0xf0c170d091a1519090f0b040c08090303070c050f010e01020307091d06060706020c061501030f2703020f0607090f091a010311040902041e170606061812010e010c020a 73
    0x114062091040c413a02443c1c40c500e1900110040600510a20207920402c00050141042c3e9415500881c5446240100c00c3d10820f2500e00a41c0c810000d1032650701c1d1102e0031500c1076074005043e01c6038814030a00c5441c1d135009215140411507000300068072800e08000c010004400b5038400c40b46014100130580c402c0f4010020b00b5049442102d1341540d461031031400344041c2c09860400328881c000e4004210388980b2140210b050228240d81c2046104551f400300021240c85031f44500070601341b04030190240e9803040901c0c04c4540170340100e0b4545180c49400525201c400c40f00f80c800654011010052860a200380e48041c0041c0382e0188842040a00000c1000301c000191504241d1255403010740c1501440450300038010000c015580c854540340c030140d00703c203070104050306440c0706c020001d88070341d4507140004a207220402038101521030b001004040d030000194000c14141c020880540303950b6071040c403003c28022100108201654401841c2190400c5035000c0542d00504a107000181741750 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 697018696 1250 697017446 697017481
    0x8070303080c1e0a020706030501050d0f020906060f070f0308010501032f1902071806080703030509130501080a0311010608100e011503080316030c0f0c170d091a 71
    0x40d1401c41d11034904070642c81940c822108070050030f03800000c00ea144560301280210513990302d520300b4081a41e8407428010441160440a080c8050300d0003030a0052400304e05560b08800018041424152400850f1240750300c0303c2001c40d00002044800810160890442c5005010900301044456540f140142410800e03200000c0c40851503c4200e4101c1e5504042c0c4012516808140651404403800a90744403950f015401304680e0480c40310010200d14058001a618001c000d0400285903a40644c0e0542240c204c456020440c403104507208641403082d64020029070000307107903544017400d001c0d182c550508141c5404d80d040520078000808001403107a084080700c480040e90340e138a00340031030042180d19240310150000041c008144940c0030041c0d0700895501c01c009211030524801a403c07140d183c020f840c08500ca218040740e85600901045610398019031100c5013101c050403009425034050010350480c00e40d20755188041c07251003140d1500740c030301000d07055243d400e081c1c5462040c0ea00c107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 697019946 1250 697018696 697018711
    0x30b01240c03171801060b0a020a02011202040506030a020702130e120904020d05090c010210050f01120f0209040510180b060d1505040807061103042612041b0807030308 74
    0x4050711201018802c22012100041043c112400350400301a0071209200f450030a01466007814000b14428680703030102c1c1d2101820382c00605050b1030303550065842d411090000307400c00d03600340f100041d0781d101c810085218141d49040140e03603002030300c10004140c944580708505640b801c189664003039000030b003000c490031800030000e4450981000180c060b100e02c1d020700c40c03401d00309000e05c01c00d8800000e015600e0f1500760203480c00009840e81d0340084450454502d0a4500024010803080004500c3d6119440c01a00407418580075a0042a10301c01e003542d00722482d41c0032540425507a80c052003000c1c1c1c11f0a0508604048581130b0b00c1d4400b4070790f0042d1089114007030702c044502c01c001001c50056803c0d41820000d04c0580f03800d061000c0160401c090a07200d41d41000050f810321106042100e124540c0b003080d20300d000c0b048503800842840d07002c00b420100041040000140100132880310321884c4540c0302501083c50018000f280300310303141c0c40080c1940c000101400001d4000603030704d600c40344 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 697021196 1250 697019946 697019957
    0x8040c060e0d0204020c011a01080c030f07030b060c060a0e03040b180d12080604150b03041106160c0305070b03040302060c0a090f0825060e221401030b0124 69
    0x1824030025614000002c0029030040c80018812404074064104a402c003840d18004404024400e0046d02d0a0720112088a0101d0080000461000300f00080603080303001c0f0300d40043c00302c1c101170219400307278040403001c40f07940c0c012402c1141d0440180250300002441101a60130280f03418640c510230f02640440f141401c4406420308025114a00208205a04914020000680448040c000c0c1c0000e441c95800703942001c01d41c900040d0252115011141d0361300b055407a580c4c4a89030413607003405000031654092007c2024a911910443e5020305103030107090400800340ca1442e02900d4810960b03c00d03040207500748100008203030007080740c0b503210a85492045c0e8030101004125800012a001000030405494021503003140016001c415400810300c41c030b1300090211120b013050b00240c840c01c0300003074220142041c20300304a94070440d800d080c01e03a03880c0101c2c44085000c0590b0400801101c50340100e0340100300344200750300c001d8010f007025608481900d0450043c1c09200d44032400750030078081e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 697022446 1250 697021196 697021217
    0x10e040b04060b0d0b240a020a21020f0a020f0919060e0603371104110c10050103031719050708090d0207051e03030403150504021008040c06 62
    0x119203401840500c40014010002180c40300510802c0d90000700309443d0382480c16441c0251070038584d6a0b0903440003002840413201052801155072607102c2110311086000340003169000031500450f0071a64110305000c0c000c0d0506080009113821140f040b100d001790b10a05200f800342e02d130a6842c0e08500e4080d150144290341d034101481401d1501c1c54800e0106243c9103002a80600304070200d4000c000480a1701c02c41510b8000c3c903000c030701040b44a02411000c055440d401010000c410080d420301c204c0e52044c5440f41d1100280c21102104a007244415000482c0000c4600a0184a40305005080c040040f54190348005243c0080c80e0705040c0f0b501200c501180f420115800c50b0b5000402103002880b00346801e0314010081e00c410789800100b40b00748cc2c000081d4038004101001075610150801c1000140c0380307081c40129401c06d0540c0d030540000c10000c00400d5005c07617803c04c07120541d2004591414148103200092014048010401c030b141001d1000081613034a0403011102185864001c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 697023696 1250 697022446 697022449
    0x308090c2d0a0e09060f0606030f010501031505120706090e090616091806090501090b1e04060e04050d08010b0a0c110411270103150e1003060c050c0d031802010e 71
    0x503282d03504103040605406040040000c00000c0041c4207104100819803a42c40e0310091100900054072083d0304240310700014802c40d44a81e021903000810656908401a92a0041480464040261401d84c1c208060070b0200c20b403c80d01d090020b140d0381080c1c0f003140c03178073700c8610b43c0f00c000150891040d41600040340c12100d01c0340040760090004c00250307502501e03400c01d100d0001d003402c1c4500b45102e81023100004d048666403040301441c04000d000000310200b120048400c010114400ca940b03e075440002040040c0c00b01d860343d11441c4a6401003244141c1c4036000303004000d0580c414a20320804108036250300d0381c8580c3c1c0c00c60095201c0446402e041e54030700018042c28184041011981c40881c2c13031202e004c10740441a0402117120407445c1d20303c0395500110305071020310148144034107070303031400300510b41481c1d41291340710402070f81344408692240e6403038059550860b8000300040d00882e00c1c00c03042c4800d05c50040340d0034980c10108070050344c3c0c1c0b59601c0306014a05001c0e041c00214035140700c10303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 697024946 1250 697023696 697023709
    0xd021f0311030c03090c040b010e130f090503070c05040b06120907091505040509010203070c08070309090f02031e0108100f11070b04030f050304051c0c0c030308090c2d 74
    0x480419100c0d240d240e243c42d0302c4110003034000300e511a00700e2081c5c004070b1102e13080034411044c0071350040c1c0d00c0342c101b51006000c0c4508a519020034040c0d0b99551102c4802500311441549089403084001d181e6680481c10048a107005a400a43c82640340600d41c2c04a80d80c4c01d011102d8031080310308902025511280407500345040d5620440d03103035040a4448220070410004e1005446040358100020f4542005041c02c034002104d40e00c3c04035010526101c0440c07045030240400b0b034840e1918541084d110552201610805110b0250b2070342c01000344682c2080076402c882c000c0390700f514800751540c5000c00ca55982ca4404009081503544c0d0032a1540c200f0a9401980107186100d42c00c0350349007403e150003a9004001c96081d0006a02c811010070081d100d10201ca0050381c00800400446030900c1e6000910440000d1020910400c803014500007941d40d480c074030065019494200c01480c014202d24280b41b01c54104600c074038138000e01002ca0380401c011800304130096040e030101300c00030350010611 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 697026196 1250 697024946 697024961
    0x8010e07021011120711011a060f09031618060509090d030e0c060304200910060e0406090e0c0901051002070e130c030b0105040b010509090a09060204120804140d021f03 74
    0x300c2003052020030485c00d8101910881d02a0303408000c010f015408800c10042c50a00e02c0241d510103401c220307100c0e00940600207429800e00003400c0d00e01070340103038002101d0702d03c40354026400c0d159526a800c3c0302503120310982c03008042c10349004030113152801072251140008040744007816561040034048040c00c1050601c1000c0282500d607407800e29041c074860004070400108111910707801c800c0c080742840b00c1c00e40c2c0140901e045c00eaa416050043c140c454005501007240c110740c0c0d8040014005140340280e0f4041c03a20b1340054991906544207004060300141c0080d40500522040c149103250300150020498178101071400b00c0342c840c258088100c1440003000b030301c0c801a400012080c001da01030383c14100c4031704440c02c00c50742c0c144200542d0320380101c01130207601190034000030310064a1f0b0340101c00c0c61407080400602c3c09849501304032806440b04401d45000802060a128151021048100c03962045400808190240d40000c07003a03440030040c51f0000e00c50640e1041d005000313400645 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 697027446 1250 697026196 697026217
    0x31606060911030603010e0c0907030e15270c0a0b070206040312080906010815041212021b0c0a03082d070303090b0604110a110c10030501050108010e07021011 70
    0x401d10b030414809403181c1050b56440d02c02d528080c0e100901c5e1000146800541402900380e03640395894000503402002d100900403c80c0c0600e40c1c080e0a10400c011044d8070562000707210108000b480d004444285406070f40d007251f0790703002c4a00300340c03550750300856a011910a03c48096440c0c0491001c0390150003290300003006c46401307110b6802801d408c464400c0c03040c1e400400321907282c1c2c1c0e5920180d6907001401c1840340d4090600000c600800d0040541ca14030b5207403401c01c0170380b06039649c01070001c03030344030b03a680d80607212800c100d880c145581884002d070116422102070031034904688600b4068030901d403030034050030810142c03004664210508501107526a12003ea02e80100341400b4018008841c0f084481d03503601c078002020703440c00f8414031b4004a4010034242c2494a50700044d00c550003940007000f041c0c40380080b1440183d403084a00c0c071860041d1742d00443d00d94500300024103140c80680100c911104041e007003000840d800550380d008444e405801154800700941001814410043e005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 697028696 1250 697027446 697027451
    0x606160b04080408060703061401032307050a0906032306190b03100509072a0501050406020a08091c050711090f0f090703020f0607020a0b0a030c020d110316060609 72
    0x8818441e2040203441182c02e0113040c3e40483d45c3d0382e00200e0403100140109000001c800c1d000440d81c3d48a50b104044280712580e202d0000307491462161b00401e8211030010010380001440c1002c0c9a00032100001440301c0e040500095030711900b54840c5880150702100302d14500c00000311a40c0c1d90710564000007501041c4a0348660300c9803020b9500740e10454251814114580b0001100d080c0503510f5441032540e03542310341c4d440c0441071010032200f0701940c031f11003030204001500c80818002e2140c0e42c042c0d40304850042c0d0311200050003811681e001050801a6001000384140c0d104036110010120640c61070101d40d980c0031403622811448508000541020b084001c00c5080d030364040300d0601070300d24100700e02503642c0c0d00104c06a4616081c00020342041c901c018000040c1018409071801d14801000210300e0f64680c401c0f403c50b07420400c80800003d441d80c01c4219155014844d00401003068a000301900c041d4903c080e42c1e0340b050710440080304800105400920005510400240000c520309 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 697029946 1250 697028696 697028701
    0x1151505040b0301090b040516170601021f0b0f01020319050913020711150c071a0f071211030f040605070c0510030606090509011229070804030215010602060606160b 73
    0x85c42d0080480803c4240568507082c0480e200340a075544450451506a549880b09841c0702c00c01c002003003002d00b025040d4460031800c458005114100701c0d015144039400000d00c08821010855940500050b240c155002082000e0355891845c00741d9503800d03518101959618440d03000b00d0f1102c826041074001040c408502d0204026040d610001032442c110f9140c4010841c05115038498440c092001407640e1250308208000c4e4400480304016622020b04a0b003019040f814200a5500c40501142c0c078010062003000310541090f07910070f50041c1c18008500b0042c01d10590009c81c840d80c050304091000c0892100100440041610b01515015004084039030000394040e01811041c020040070941e038501c00b040c0ca0070a001614100c920010f00310040064984640c0b0400344440c00710b68040c20703891900301c05e4444820744540110f1003550740f04000e10381801c00900780341c0e040003402400b4228900400016a00140075608040c00711147d42e51201c00700c10071504400e0940004207410400d204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 697031196 1250 697029946 697029959
    0x2508070c0303030b100504170307020d0812151c081b0106050a0902070807110a0906060c11042307050705160501030e030309030406030f0e030d0c020d0201151505040b0301 75
    0x1000390440c1d2080c1c030180000b034466420003002c400c400b40c0b408001a8140400c000b144c035810300c2d4228058100c401d0f2403401e030281e0045110042800001d90391528005181044150ba1003115948180d01a02d0840d52805080018002c1d000c415000e84c1015641c5821006001c456021034022808d100022080c28260350b880364082c00c200d01c22240720303c80e810700002c1c5150403802229400c560114100c1e00c0d1640300c2e5161500000c80d40d40ba47d400004d540e10200d41000c82d40f042c1006061251500b50070102d051070003484240d80030310958000c90600b824030304100019880e40d00c80400142c4401d2095840b40d0040f660381c01800c002500714441d916a000c086821110400d00380d6400782d9040c8040c80d00880c007a0b036248000d41d40444680e004100070880e452007035208052502c0f1400300132509480d10004245540c121070040d032105c03940c0704201580c0d0b50301004009036030750a500003403020303140c54212682030203074074800c034811041c8050703401e10700030700c07031000c0700c001d40702e010003540d140d586406 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 697032446 1250 697031196 697031213
    0xa05040e04051b01020c01050d02030a090c0f0e0a0e060f1801090b0108100e0613030c060504030302091e0604050118080a03090e0a020310032009131a0c250807 70
    0x340243c42441c034541076003010754804a142d01d410070040c1c64652411031007000d000002d43c030061280401b260b0300e5200c000080d4156100000070003003824004141800c00700c40c1005141d0241c00d05c40c0c114034001420002c02c01c00301e060359110781464884100f0b945c2d90010249450451180079009500e084200310801101c441c2c001d040e146032100f01c820584810081800722001c44402c1c440940c000c400007503003004008034001c0303014828541203c41c08180d646d000256501910124042134010807016050b051140e41046400d40b500b14042520642c0804900644200d00605041202c050b11201780202810944030003020102d04a40e160070190400a01c1d204803402800400c1050001044d6220f46a00030b41e0300507103070b10340e02234a92865691000f00d8201e0018580544005110074400f00b5178504000d42c0c4900e1084118562007401c516140d909203851801d5101c60580c0c0809004042400c101038500f20007401c00c04480111040b003440d405c00c86030040040c55403100040110410220381e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 697033696 1250 697032446 697032463
    0x8100f0801021b0f031e0f0403110913020f0402130f03030309021f0f0c14060f01090b06070519051e0a02010e041b051e07060902010e0108010605030c0a05040e0405 72
    0x81020550f200e101e04071641c1c03140c2c20902c000301e06500600c2040380c076161080f680c0d8124900044501d05d4042c2c0710b626001c06811940c0295407008450002030f03500d0034500b0300254440491405007a40074441d60010310f002e040b0101c050b020365408240301c156662003081c148040c10461308a154495942c0c41d0003409407183c504224001c20321381501c0000101d0350640101d4918540d1245000001140340498404050050035166506088140380c003c0900b80441030190444158010440d0b0400f400342041d61030303c0403c14001c860400c4102c0c0402c1011415002425183c00001c0d40042c01c1e003000c0d840c00d00740e03000c4d240040790a8000036588260000c1c085840c0f510030707210880d900000200300000ca0f0340401c21011818040055111824441d10080059442003806480041031058600d1455084814115000d5a9400000041d5a00090b03201c1c4800000d107010101c40d0704204004025000c003a1203d0416a400306641076170500030f900f17450141c100c04040031190b00d0182006a0344c0c40b01e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 697034946 1250 697033696 697033717
    0x603080c0c01170c070201141b07050d0c09020c0708070b0405090109020702100f180b070204140928083c09132408010c021c08100f080102 61
    0x3400308100c0c20354083c2c545400110f4a08866800c0ca581c2d0034540c41181d444141c0880c100b041d884126509605030300064200d402501d801c421010b0318982c541442c0070000c0e008184119004540700e4000382e408040c0320151849014050303200c1c00032040b014a04090754120030420b000e8268081090301200c00a0000c85070100c450002036640c4d0031030103003244210b12002c0c1d00400350049902c4100d00400101c00b0160440c42c090340c40ba0501801d02c0003e0704c041c0c0000003400000201041580303490f0151f550594070380a10f4500c1424040e081d266075000c2500c00c465002c088040d0180c0301c4000030640000c040c0c00001c01c5640e078080b44600d0198011814488150700b10307120f00007042c0e481c10044074541c9040000b40314640b003440c00c01c00800b9180c850315007085544485034000142549017100341d100502c614805021814518130f242135518004a540466000c800c106440c40d140c05105840c15006091803541d64490640c08102a40180c01620045c8a400400100c00a05500030460b0003031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 697036196 1250 697034946 697034953
    0x70f0f080a020d0807050a0903020603060d02040c03020702031b0102061b04030c090b1905150d181406090105160311091e0307060c0f12022b1d0a150c0203010603080c 73
    0x480e140300f1b8900740140040e640004075088030600050804500551b0405401048040454050750016054410341c00c004e800003a0040340090850030f0800c613800a8203400c10110201c12034040000f035031940f004280401000c0010058075164003230b002190080d54005014141403a10343d41d01c00090050012920702900803080c1e00c1c217098044148084c165080103040c40e80341c180a284040311900a03c14005d4403e580c0d03400e000120b250002c41ca002e0912801c00c0301191a1400700d61030814200402c550300c01d074140f604000303070001a400e00c4907040081c0e040c0018000141120004a40a10702c11150407050070f0b07654988165404000c859441c004600301c5a0042e12090102e1301040a900c000b4818002d0303600301c0380001c000d40714000c540041c030b2045594620100500245403c01c003035800702c038642c44041c03030041c2580c40412211a2608a0038410760704000e00c000c00c0301000c4610032121110b40c1002400c01c6030f80704414100742141c0080c000e022403078607802c001400340d00403400d2424510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 697037446 1250 697036196 697036201
    0x80927100515031b031504060f0e1b0708031017100c111b01050903100b100801060e100905030d0512010509040c1a0d0204030b0405010b030102030606070f0f080a020d08 74
    0xd00300011a803040ba0660103084c80c00d522100305101541005c1c00d440d110301983c0f180e203121380e00c0e00d1080074000c0034000403c00c40c1905d8050200401e031b801604100c25643c0712101021070040b214201c03521140d015101d2943c84d9602d4003402d95219454200d402100c0740d2442c5465080e40c001011041e80003c43d030b0802c540c800e00c200c240e80080030108103071655041889800c10020150310703080034070001030503c1440c001e0104002410700c02010800071a140d80d69980d9901410221108100003c0d107003800f403d15410700c403002e8140920528400c1c410b08214080e015818131642009000380700c068100c3c1c94030184c0e0200500316801ca039020b4010507148000004180c41c01081e02070103950003c190015041c00c5c914036000c0100d40154402c01400c0c200414007407081d0302d2004000660044034a030715941402d10b882c90170b5030495845184207a0050080c0195691030034201d40ca0750360300440040880115180003c1301c00d02d80c0b200503080382800301d0441149134010131414030305041a07079050f40e90b6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 697038696 1250 697037446 697037479
    0x60b031005071d1206130312020711040f1401062c220e0d0e1002062401020106030203010203090106031406070507300f031104030809271005 62
    0x89900b221080300243c006100c440200c00d848481070b0810b40003a004007405080142038a140000542d00a542602522444418580e00c00100010a01c4042003980341005540b0b4000d103511100c55043d1040750b0b80d010171100c1e800c0941c8080e22100d0502403d010640e0b440d07001824a506115940e904240c5400d618818101c15181101c008080180b01c00d02e50021a510400d400064408032040c0340d607507180148601c8070420242040d10369075666201c2c1040013200f8040c4a0801c1c049440035503203c10240140f2101034a0390b00e0f07018002c0d044900e0034400c142e004070301601140d403029401d03502c00030512401c81ca0640043e01603d004072901000c038401081c80302d90f5810100c0d0401c00003035041c4038010000d130707950301a100100000010311104080b101d580c0d6224405100e0094080b810a091401500c2e4150058032582d85411814030b042600e5515160968421694114861000c0c4000c1400c1034400104214540d42000f2102840b0314280f200483c1904031409514071594918034420240c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 697039946 1250 697038696 697038701
    0xa05060a0b04030b010605070c090944090f0d0b06030f03030f0411371703070b0604110d020408060a1112040311011406090a02040b0a21050103060b0310 67
    0x8070fa620100138100e5070303e00501240e01707810214049681c3c000003500013800140d01c1c011442141d021740e40455039202010022640c2c11403101d0740c10610f8070054089640503500140e00818210655421a07643c440b01000a08800e080903c0c5030340803900c1e4416800340685080050b02c01d0700250b0440c1e150034502e1407890b0b5240001c640c000c80c80a45400050006560700c82151121500607080f1012074a0040c3d43d074983d10201c404940c1c910212034203020024202c9404d8000400d810391804406d5a0050012502c0340704131f56018010000c1d4030b008c0303000354845a01c1300d642c0c0c0d8541c142d42d40c2c6070522008500044c1d0310911441c00213104001c04134003102902e12550090103000d4150500e013181c44030003916064802042a014814144001a40000d00307002d8682d00d4542d0381c0b0349011034601001000044280075150350401c1c1c4c4107020030b0100540020440b1904180c5041c0700c5029803010130f905840c0201c2000d107041d007a0414000004108994004c50341c031020850903120401c4803220704004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 697041196 1250 697039946 697039949
    0x90503060103150605040e0f0d1e030515030303040c0603061a07060f110a090302011416081303170403020103140606044b08070f0501030e01140a05060a0b04 69
    0x51581080c801040041c08038103004124602041c0c1c0490a603940f03d0000b403c40e4030850a0540c250006045403035101020301501c20751443e141410100f0f08480e0f01d00800d5012000310301000c4c50340d500081240240001081d103540d080081c210382da68a090b01d40600203800c1880740402086c1010070100702c84960455503803070000602c03141424049252201c9000d0150500c85e00040750341e8125012140c00410001c109540142d04e03141400c0380b961000500110110030701c002c0d145000e0101140c4040a0b80412044d243c215002c1e82c7c035549200800c0e504074503076500c001e1018048408030018060b00e42c0140048a000740c80c100f1441c440484480c01300d02046840b95440319082009000c3c5070070880c1c5c40e036002001c0e50701007900741e02c2c003080d48000e004c542042e1042d0600f800e0b4810104207481482c0e040600b28000c0508181443c00d65908042041340c090f450615032960684a2404025844030100b100f6038000c01c00a0304054150f48001c102c00d460380c50082e0b00150012a248010701c3c01c840 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 697042446 1250 697041196 697041199
    0x10b040e011505030412030b040f051f05150a1106010303080a0605011b1502092e1110050c0d0504030801080607030e030306130e100b0f040e0c12030c0f100c0905 71
    0x9207195140c1e43d4a030107080c0390080d003a05244c2c8d2a5800c6102e51114801c01c206583d1641c800902030600307158561070207000e0406030700d80781134055003884507480342c01401c0070003400603103034684901c800740e810796040031100d80001c0144200300002051690003558240a003481090800520752100d0044405962110001c0c41148086030180300044420007114007507c00541d006050850710760000c0c020030a07005030000901601c8145400f0141d0111200704d04900d2800c0040c3c50f07130f980e104490780381d00c03c0c0c0003030115003580c0d0030008505d028071800b01d0781484440e07481080755143c03500d405440c2030304c20701030701c0d003603105841c00503a0003402171240401c02e0705040011419503580404003ea41d6201901c0c1600176920f41c080314040100800a08411200158007c030b0500c2e00c0c002407140310003010384114402c03414000701d81c0741018080313080300c88041c0c10ba50f5021901ca0b000b80c128a180302c3c103d9640740398480c201c080500c1c0000800c134004d001000f60402e02c1603484030b41c803c50300c00d0407034020f09 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 697043696 1250 697042446 697042457
    0x50904030f1202040303090302030106120b1303091701050703050f07020a2003071503050c090f01110a2126070528030b2107140402040806010b040e0115 67
    0x280828000c00340311008903070500c0c1c189960122402540180e03041940100c003c0707606c1c01c0c014011841d0070300a1001400c00c105070f070309101c0c809032906540c0c4480039108400308401e01c1c2e81981403501c02c0030329070040c0580c860400e03605901c1b080301302c0c000e08040341c0000010780f5103030118061354960780840d801381702c240c0e00a04841c560758a603241011074100b1611800c8101b0021013a00741c40c1071224100803e41d0703041900c02c80d100c109014042d00d400420f08000c00804201d00801541c0d1701948151500702840d000081804180d02685005d443c03500203004441c0c814141045014a40141411820b10ba90b54003007002c280a541d1006061388403002040310142400150078500c240040c0501c420354900c0812246183d4440b80704490003662a040001d80380c00803e100342c1402c0c0c0d262600032420345448030750520550075590b1140070318012509070405410449000d07559580583e8003600340d5405680665135194144081070b40148170b200b5030f44c59840d00006041c106c54003807a030310743e00c5919031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 697044946 1250 697043696 697043701
    0x602130306050603121b0f1905160501020d0e0f04090b0919080a03050c0d0213050103050108190602030a0b18090f150118020d14090f0d021b060906160204150509 71
    0x503c0080d0441d040d081102c0c1f141e50f40b1381850050070001c401c2c3c0e0820f09461711400c0179640c20200d0414a0074481c041d49200000c00070001641d0001e42d00c010f590311850482a0b03040d0340300000e5219000744507110307401424600700105000080d070440c2d000f00307589002ca82900190881c80c070070603550904041d001d80c4040c8101402280a40c101c194412500540070340740c80308412440d012600110350103500c0c0c1140d0b03003003400f4558042c8605d81c09055500018050b81011040050514020f0701c1d00404290300070010901c0b240075a0400500800010400f0f4107885503000542102c1354115140c482c18030402c40070402c0c2c6400030525882d507051080011205a00b000322418000103050a6001c1003a400c00242d030840465210320004010302049142280c10300c0321609242001c10343d081c07045038000070800000c1a400281b041c00228a0514070340040006d8000200240590400c1c107030402400100c3c00c000c0d03040003da0200c0c030b51007181d003041940c075604045007415019004140e0000081000b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 697046196 1250 697044946 697044967
    0x50c0f04060e0402061305060705030304060c210c0e0303040801020c07240507050a0804270c32030702061b0403032a020a0f050310021602120a060213030605060312 72
    0x1400703211b80c0c444000852507900d80c08110968000f24058800c1d0700040180420080346028294040c030396442c0108040c814580f00f580c031a00591566610203560b610501c0840780202241c0083e1030000b002e41e610740d655031a5041c041c0d401040f110010f806091404541c0d40c3d05070428950140621104845c42000b02c0c0041c0e4090f4441c0000f07a40c540f098808000024500000410281c03a000c944003440340340e4454640e108800e0035111221090401440c403501030350010355040c9001c42ca0701c001030101a550010241d03403030050042d181090000003082909500051a80d002d03554180030040c82c24070803607003d030541c00745010080008070950017032045441d420401a02c0d9030850000001c14030b480380d00040f0001307400d52152054403482c4004000310715040c89807d4211404030410b614140e40d00c41007200320410100000e10901d0309456007080c040003040740d18089035021000310344d00c425040f103030b0056002a02c4110340c10b6081900144040c1004140520841b60411090b400d0079007245 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 697047446 1250 697046196 697046209
    0x1b01020708160c0b04030602070201020d021b1507050a1407090b010e061b010c020d030c0203040f1502030d060e040212010c1d0f040207080c06160504290304050c0f04060e0402 77
    0x2e0503281003090101c08200790484900400045114050069803a0307090710029080460710b24034103041d07400026540d0100345a4860030442d02d91308072030407803107c012468890400e00074a4006040c910a180d415000c000c40d42c0744004e50114400c0489661940d580c202c2c0d815240c036514640e0015895070044803080c10800c01501110305074041d040c0410041b14405400c507a60130500e803006902410a90302c6494041c4642d0500e0040751000e10f10706420320756820b51320000f40c4110030350400d2148400032407501c241705494440940150500c8a6a0b0354600c3c0c9805500330b1f034060748a11450504403155410512501061000c0341c0c5580d030708001d4031005641c04008441586410042c004070781c1095540c1c51005044051169203070341d07152004441c08a1030000d0007013980c200e06404000c0811241d0b0054260380440c0c042e640305096004140083c0c00e1520f0010810703598029001c400d0000300800803e040400040c03d4400644403050701c020001621141e02c506540f01d001200864051305156 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 697048696 1250 697047446 697047487
    0x10b03030c1b01210f0507050408030414060c0d08010e070908100b1c08030f0f01081002130e040f021003020f0d1508060f0109180b070e04150b1b01020708 68
    0x504010003c204492001904c118004c400381a1a80d0b0b10214078410704050f11406401c44800d181250426040400140e9030b84181d0080b540240816200c2201c996110401c560740021243c0580f07410590844e80580056020f0041c640540d02035000151440e1280e48260100c810040c01050490154007040c030040c1020400340d600700b0311a6118030502e0003205854244144502409a500c0c9022052800034180c05444080f410f0b8084004101c202e40018040c8902c0d170140d00c0040e1f0700e0b4507074885444101c41c2580040100d5610340100700c20300801c65000c0c44424000d5440c4406c80000e81e504a04034451611411000f54091184a40c0350307180303a220001680c00c0748510007110740c0341c00543c4c0c54008226002403440c50080010300c00750368140103048003c00c54000d208004181a6030b4000c10b500014180810042e010b4141c6025a88036040210300da4907045403082c3c0d0350744400c0d043d020360b4402d078050740222940142c03031040c2140501c02c44004c10b80000b60141007043c006136025103000c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 697049946 1250 697048696 697048699
    0x712092c06010c1415060406080309271e0f090715170f100602030405030d05030a09020d05060901180b0f0408040819210e06031b071202010b03030c1b 66
    0x5058a100180d40c07062201d5070702e402c0390001c01105171000315100b4402e034000c0c4200d01880c200a01040201c80000585911110880b10b0514260301101e40b015600e400c10b00a03892003019001b84071801401454001140047c100d1543c002d0b5110001c10f071400d079050702c00f1401644103010400c1007400803003011102021910f404480c0c0b0314403c6685042c2c0301c00307031250f580000a00c018801c2c0f0400480b601c10040c4104d002075401c103443d0000091b00e90546450703140c103020000001405030b0718640c2c840c4814030b6005000000c84075403820a5990f0b6402110054101d41c83d01100c280c62b00300d48a00d520000743d2200042c50640d03201c1c02240d110a0000d030003102d01000601c40821120b500b404600d0040010403005011181c840c20002014030080004120386e43c24504a01c5046034402075180c80e5070000c0d241180d480d122064480141c503405c200006501c2e8000c03c182c01006114000803068114a0303000303010864103101059124400c410082c0c20561140b10034000c244204652004030000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 697051196 1250 697049946 697049957
    0x7051206010f0e0a170705100f0c030e0d11040b0618040c0507050a140709050c072a030c03050709020309060a3c0c030203070e0909070b0712092c0601 66
    0xc0c0da0104130040c0c0c4d9500240001c410140c0302000840341044100000c02044134040040c108004003e00610600d18484041203040391082313003450300880464240070405814078140102504007500c00f040c000a04921560070054040001c1c640352095580c15400010074074004e6003401c041000a01d0240084420320170240120004284140814071401d405044021400c0b90360f000020b0404120b0341160f4112850306040c030460705125402d030380c00c040d4007420075200390701c00308010152081c051b1f602d1000702c0c542080202c00c2004200c0301d1401c0b20b202c1e20403242c0781600ca00241d0141e010445864140f6030042d8002003140da55500a00810101c80d50b024040d0400e00500146c0c42c2c0124502c4450b90359200d6014144050030720501c2641405e61504600318140b03100000d100d00900000030b8440c8601002045500c0d00a21001000b490b4120100c0d82e01c030010314002821a4074000000c01050174404000f03295458901070b005030100362814404070345901e0888142d2034101600f240d04100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 697052446 1250 697051196 697051217
    0xa1502030d091a070f020c0d0f020f041509061806080604080f04081c0f020606280b19080901020702150724200f120c2203020907051206010f 62
    0x4901d0450036005018650f5642900317644043d002c0e00c2d20280d01a440e014107400300b51b00001c03a00c40c0440b150400e038101d40c0c1001d2100f000000501920b181030a00310b07402400031000490300301c20303400442200d030584803003401024900311000885070584a0610302da049072001400194004006000400250352040d003032a482e2100249400c0d1181c0a111b024040c0c64000307003545800040c01030034004544000d01c1903140650210742c040311501c82069114501c103011038034500307841c0138102c0070304031500c1c0311030300e0b910601c4080350a0501c3d503d40c0c01c040741060b80400d800800600071184001d0300581480181c50f01100000b8056110540c03e40b2004084682581200c0460304180b0014002190200f0700c0440d14036072a00002c1040e4031364141c00030804c400603c100d800c000392040d20646903520107180e9a90303550001c05110b6000c81d04500c085a03000c003010b011846e146034064a00071b4804000d03603030b07030100b05403000d1040d4002541035a0369100086c640350b2190000000d040b03424a0403210381d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 697053696 1250 697052446 697052483
    0x90c3304090507093003140c120301260a03050f070204020307080108120a0c060504020d08070303050f01060e010c11010e04020f0c010c020105061f0e0d03030b0a1502030d09 76
    0x5410a031000d10000b60300b91000c00903003440083da0003080395445c0041084001c1100401c0e00c80780035840080a2106c0744c074080b1540d400350800e4510402205080d20001c501c094644100383d0300c01d004101c210110040011020040ca014000c2c4d0003403144002d08210000f0f441c240e68940051240c0c40341003d0070801e281c016280e500155008140e02d484000f903650602100c0390804c0c3e0305901d0405108814444c501c5201d600c51300c080c050304d0f0070100020300b64540740082000c2c3d444c060b0015100da03400062034420558950f02261058080d229051180c2e625101c3c2222580700c80403145000034202d990500102e450801c601c4500d40050403d4130041d000140030900383c1e001011402c0d20614045080e0f00190740c28012840840141d200800c44c038507007840041e0b0043c50400b1101c031a16160300c03000e80400d000c2d04883c803462100500303c0700c40100900e00100a403451036003160007103284090000b41c101c0b4038443c0f140e0301721994010710305200c1245481ea004041060003501d144410446182c01c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 697054946 1250 697053696 697053701
    0x7081309090507080c0d0f0206130611070509070e041a030717010b03030301121401090812010302010e090c040b18060a020607170f0a0902030a120206090c330409 71
    0x800c648a0041281d9100341072280c1010181c1e0300403802c41c0c018541c880b885541d095034141203c1e1740862400008a0341340040780c071902942c030b9160b10700030b04004003107a082c0d04094042c03c03820740401141d86454550060024042e4290343c501d011a40b20750f4038600c2d6180c5078000c000e4503006040012070301030460b000680350007520f5100c0d1607100c0d2229079a000e4020203020300048103000350000c625651502404c034580355165000909400080111118100d400f034008117a03e940241d04281c9442007810140c119071401e210480c00302e1481520100b440c03c141d003074544604045144c1c2403d10f440c002c40038030340354001074010000c03221905000704030f956188042d050043c2c0a1707000301410b292015026050005040c032050b00ca0030b1100400c002c1d1600400465800f0405c4000401c40746aa48003003071402c844004010610f081c42c2e42018400d03940018003600c2001c0b003104071a4408000401e00c400000c85031140400c40100e0740348101210308448020500c3d40080c1800c0c0d14255030790401c4000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 697056196 1250 697054946 697054949
    0x3030a18020415051203041802160b1e0106020d0f050c0c090c0a090b040f060c06060527060103110313020f0306090c1302040e06090a0b0409050109140c15070813 71
    0x50f00341c0418010301050030305e903040b11110240440110325260614900701c24403002c1e10f2140b40900e400181e104141151003411764034640d480805000c050500070403d1041c4d042d2403400700078039100e28000181d4540f0010700781c142c00e103041e00c0394201c1828015040700c0940c82540e40181900c140455407100d52100e000181c403d21103c2d99280e164060b0341001007811100d6404120360f100d09000600501d0030441003d4200c680b10b08100c2c060401c2c6141100c05001698031090b403118208004480c040200038428118050028140c041d0b81e80e02c170019000c544900c9100c110810007800007421060b01081c81c54070b410f0000300302d0321250388034000092404104070368010703c2e5040701381c80b01858100b0501c84070b0103494414080d418581406440d1824010042c111849803505401046040105500281d030100026106020900740707414214080c110080080780c024540094600000c0008038545600d0f04004180300440382c0b5080d40003445400c95842030765402d00400c81d85078100c804104100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 697057446 1250 697056196 697056221
    0x617250e10080c040b0c10020a02011d0714041d0a050f210706020a1218020f1905010503041a0a060501081305061602011805280503030a180204 63
    0x10110080c814800464201011002804000e405000301e4044030000c1c0c40c00e480c82010210b8980510740d840d1860316103100c144420040c80040c01c0302c2003a5041d00280240001000c81081da0b0aa08403079968810103841104140e44009019403003501d071640200c422003011440d080d0001090368000b03403e01030001d0044481e86d1104180711802d503424014480c0c0d444000c3c0a0603417201512238a00004d01c00c40c01c0040c0760301d03400205812160b002d03214a420f0320072020410000d6503c00091803c2c21120380340141d120b01c003a05101e0805141100620f4490801440300d182c9280c6032000566098001a1044614503811b98440075604070b0940403602c13507030241c8004100039241c40005000800007408803800f1204104606020410018034680c000c0350351401d941c204504070314100d00400441c8200880134070844284000d0000001c2c0201d110903443d0480d445640100b40303925030320000c0d400018203e41040c40003070f0410310a0fa0200c5110300e0850704600721020164001000c4030812003941 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 697058696 1250 697057446 697057457
    0xb04020d060515030121062a1202190e03191b060c02210c030303010e0901150e0118090813030b060d0b0f0703090c080606041104061725 60
    0x700410702d819042c03a0704600b0200003ca00e5941014500c141c2d070102141a4455012850070031020014284e011203602441e0840044280f1822941350380340c03100900792440000e03050100711106c042540308480c0d842d0390131241c0010000f0b6154052324102c050544890349409224240e01d0740040d100b1540040d148541d10040c4001c0306d195980c06140d5040e0019010402c048031042c0042c0c9072201d404a01c0b11407001c102c4a1002a03a03890b526001484924036018000071000080107280d5080d12409100658000e202195551108074440710b00b070711400750030070002c50041106a104e034842d01004540c814000c100401039031a14640783d800f001100c18030011580c4104180500b4084054001d0000c8804800301d603e1901d5213255404040d06005052410340d000c925001e0195101030301c81a44850034408041c0d881c08996103604044400c0c5005034140844c480c90883c865040b201561500e072902549002c6d044420f100c012030050018942c04400040b8503001483c85d4020b184428199444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 697059946 1250 697058696 697058699
    0x21515030d170703020f1615110c150702030d0218060f0a0206070519450f0303050301090e0109060f09111915050d090b0402010f140a050d0b04020d06 66
    0x101d402c4000300401440402d441844080018414982210011000110305050300300450401d8030817545403520b031000c45494825084007214540f0083c10130300400c0f9041e140f10140a10040d00411811650140140c104000d54007030ba041035805840d01c541d022000030309024203400410120f601000c2c42c0440c40c0404241f00b4081d96040040a81c0007400c0d142007818290341c0d83c401c030041d4000b85030302c1c1b080c001c03990005003a60403030344a09400c074000b1010040a900d8180422888003c0000e4031820503204503102103803a410b40c4000c181140d90603600d00745140e01e05030b84007005060740380070f440340e554803070019002040d0a4001c200660214820005407803145241001219281d40309c4680151008020300e00d0160342e400c28030044600a40c54005183c0ca25182214030380b0403403903545000340c60b0103510343c14484007410061040b0303c00e0b2203268180c595000700b55017040d41c0040c0d0311040c01d02001008205441036000e00680d02d4120004540f4207a0500090103a803c00307600100245d944040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 697061196 1250 697059946 697059977
    0xa06030f0b090d140406031a0a0306021e03060a030209091c030c112406011407080901120504200d170c010b0a080303010b0304241b090501021515030d 66
    0x1800c00ba81500341050003002001d413884401502652080b43c00307241d50b0301c44148240090824007544654010201c08a2a07124035000c0003c0d00410903080b1803c98072241d845940704804204c3c2d0040d071009002003c114a03690800480c00b00c003c00c0c0c51042d02800c0c180e40000462010400d02601c023907180402c201c1084040102000e1070400d43d200d81d81e112501d000c2c080c0a20003070040080b0182040d064031641c07410016101c5640000c80b90045110008103c014803070440003810700d019090341e0301041c07000a1140b94065903406e58014000a40a19100602d80160100d5203a10b250280650a00e4031082e1034414841c01c1c246c0d01401c082c0d0002a003c030504800307218400c0c00d03070000c4458440d181c0c10075035041d50303034081402a031040050000203d0213216000c0c0d031130703065100302420340e0120b0048090342401070441c0c850300c4a010b40304040b0103460359014801203020b031081a4001c1680d150b502044142080018000b036025031400b04604015460602c100d455000d103540f9034010f02841d440c4c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 697062446 1250 697061196 697061203
    0x40812040c090c0e0d060b010c0212010903030b040635070e160c170304020312031e010806090c06070804090603030503040314120c1e211312080a06030f0b09 69
    0x24558410000100502e210365905c00c9003441c0c807590080e500041440003513005031903c07404044007030350140350b071003034100d81890540060001c1d034442e40d42405040c09003003d000c00d8901c40d004003200c0c240b121802034201300000d101d049581082c0d8441e10942c07010703134000900300744e0f0542080c100c0007040030400c030603181c0410f40b00d09003492500c1c00c42004c0c40a41c4950a01185040b0117545022002010030255501000358010f00382044151555a040c182d10b103654843d038451820000964510000980303070030120700c076445405400050002144004100704030707079114034000c0302d03080000d200200715611281b0482001d140309440300d542e213042c182000340000f2000d10001081481c10410702069050491031281c2000c0951a1030b0b4540700c10241c058028907407684040c1e00a800810a0004910750f011082c129051078210a02d160304d61150b00140307205104800350004400128601d5154072860005900c98a000c9001561944a5440090310800034009551060091050025134041171 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 697063696 1250 697062446 697062461
    0x62c04150806011a03010510020708071d070c03020c060d0608010e010b19061b1505160905040e0d1b06060308030f28020a090b0408010e0f070617040812040c09 70
    0x44c0103250041e860b00c0da034010612050283c0c80c00350300e00e00000b00800b8000c12010000d40440302c180c0781c0c6151108200102c5041c1110005510000e11011450f518066151880340d290158041c0c03040848c030300c00340440782d4080382000d07402a5448400107080202071044000c581030442c00030981401c22001c0000c130150f103603c1c1000e14216003400f000101d4007e0f50f05095441c1158840c0c0c10100c0d01e050140744488034840c500304984c1000b04000301c1c02510580c1034070710005612280032a0f0f8485041c00112443c40c00d80c40d18036445813000440b110301407204503009101012030340d09200340310350f200c2c0e00b603901c2c6a100701c3c0c604402000740f080740989641c070316502021200c6c885128481c10301100d85090001d07100702c40354580c0051000d85441c400c0c004000a0840848080d0351107584003c480e000f0080d0501a8005000c1e20201c044650700228030001100c5182d900c8403468201510900c02e040e80143c0221610702c0204062140301c078203d03400ba44a030303010b4004241010710307060785241030320a103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 697064946 1250 697063696 697063709
    0xb09070b040b0315040f0903020a170c100e0a140102040311090f1b041e0302040608030423010912030815041e09050c030a080301150306062c0415080601 67
    0x140030a000c5400740b038054a60090310059002c02c035800f0b00c00454000d0840391b651418980c03c04041c4014117070001680e881083c4510220140c520341070300090a2801000d007c55020b0f040520004180745041e0800134000c501041a211550282c0d03898140f03c0300d82180c264541e0750049410800e11107445c80320b08d0840340696900c412407806000c0c1c0c25440000506980d4160746e591404446a524081690084c0c8603403140007030010090100480703d480c442c03000300c0c441c0e0306203440401c189001209440460341054200114249806a210140e000c00c049150400610b00d0001500303c10030500082018002c0c1c4804800d410406031b00c1e0108008003420a00541c1030000d0b0900d454480c09203d40245160003001a0b03440e118900941003008a00c00d40d6454850581e164040c40102c40003036040300c65101d103c0b2901094208243c050b11000d2007041c000c00c0080d0800100301071a20805182e03c0c0c44007642d860140c46c100300040c00c8840b1316507080513a2a800c3c03801d20601c0c80810582d405001b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 697066196 1250 697064946 697064969
    0x1f08071209020603010618030209100e09030c0c01050319020301060903060b030d022503080325021b0d060e0d0905130216110319030c03140304050d0807020a06090b0907 74
    0x900b6004601c50b44410301c620401c01c0300d1024407e040b02140014080517640c010b0001180381047c440c02c200310125402241d4400e02c50001144049000000302c1e03202d0051500a081c44004110044d074690f04001c00c1d0f00407d8540e4445511904582d10081d0302030810342d121214039900711708207030046400c0000c0e014020350050303580090303541d0006251416613051040c00011200c006450300411a80d45c1d100030b00000011040c05441c580d41a10103414100000c8003804030002c41004a0341c1d45210b034104035010402d41c400c1c0100c3c2c1454500100c0c0c00d03016201c0800c40119413558940b4202404180030000b0b0346107602031009203003a2290025142c241c00701036082034140c0ca03150131141f501c0d1000400240043c08070b008113403814400443e400c0d0040b446d0b250a12400c0c203024014103076585040740092040c2581d4000910340c07809036030050740c005005100031418000152075075803014201205600c1425004070004200d800b42000442c41006042a1414070003c024900f04003900500440c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 697067446 1250 697066196 697066211
    0x610051017060604090609200304030504140a0e150909030a050f070c030506070305040510051e04140d0c1208040807200a03060207230d0309021f080712 67
    0x26801074160060040e805100c1500380c81d948009000e40c42030382d10618000c0e090002c00100301c18558070215800200d81e07400f1401c1310a150351640a8071013198010b01048c4107000601c130801700008082c0b0b2291001e000151a1a254150101203c1d0304480346850300400410341312080c01c0248040341c00aa040340210f041a109400260480c01a49903500480402003014828422411340c124001c40d004800e4038490f00341210000e0181001300ea080ea66403142d88100000d004040c400e40d8856181402015003903003001d4180600b00d0030281061348c0442d9901e05034440c00c40d082c00301c7e0041c0e041e00d4a400e144c00c0c40a1601003030001c00c00c1c5150090203080c0082201045031801101c010700e5101c81c1c620400d4a41c5005550006480b40b42203030040c4400c100882048017541c002d18076180aa00c00c828060014140009001c3d81b44802e414150407802210b240d00340603810200040d4070060295001490703402040000001d0003200000003403a000602c903146402c4581c40e00c03003456800c0240080b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 697068696 1250 697067446 697067479
    0x102010b031612050a0b24190e06031e2409070e0907121406060a0f0b070f1b05010f02030405033415091202030a0303091a040302061005 60
    0x810a51040c07180f040144260716080220900c988070f50550322061946450400c10101480e14178040c0d904107400c04514940c101901e8506180b55240f80484c00102140d4244144903164002c01782400350148200e892005040500c0b40c1e220129201e04c50003001070f00040b210354101120421491a5170400050a0003828000401d144080d29040d4070303440c0a40d25aa0000c51130440345610a80090420f03622000c1001140708142c03200041d0b00041740c0d000e0b11141c04020300f1039503500c40d0fa040121008020001050a10041c0848900555510307480303080239144c0f072001e012801c0c55062040000907084c0450341c1c00120380401c1c15581e00c01941828140b0001c0380e51035940702c0300041a078264a0503000011003403c0c081e52103044c0c91030702c0ea80319a500d12808960b6101422200041401c040300030450548a4a0096107150010000c0900100e2600c06500403c1030b0b400c00d4a4071500c1c01001c20010040700b0720b00d07008038420f500601da80e141001141801265030303000140701d8556113070031041d032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 697069946 1250 697068696 697068733
    0xa050d030f0e030d020c07030c0602150106022a012a0b10140603060d02060c0a05010e120712140c0f150f060114090a0308040905060a05060d0c1403150102010b03 71
    0x4a12404d10050b40ca00d8120306491030310391030f50701c0200300c0c040c400008240d155000c50300c0c0e20380a00c8005541c1c00f60b600ca01080e82c0b941010701d10b402c1070400c880e084803c5400380c5100724045e1034060520b001005950419807018946001c0f160403800e241c800726004204200d1881640000e030420001341441c18071150076030004444070320305d1003005c020010a40d1956500603180f03650381d00410440da120030799900103460710904801610302c1d51034290741204980020901801c2a4040c070880381c0b8002c41c65969000728814001c04400708101d600c1d248017443c500300f00030616003605400815038071101420003031501040e52400c8810b10203560600030000e1001c05c2c166000b41c1c00f42001c14040f102201040180d0140a1710954090112003000080c814800d0003401a0b81e0300900a10149c2c4d900d038280001801d03d44680c0790001c2c2c040004660b17200c0c10303500920304581c0070700e001130321000a12441d00c0d59420680340c2d02c280750003003554081c0560b02486441c8078a0800d0380170301050014046590310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 697071196 1250 697069946 697069957
    0x20f19030e1506030c091503060105010306080c0d06020408010504080c070801230402152a0303060d150b040f02040519140d0302010e030301060801030b090703111e030a050d030f0e03 80
    0x202c1d106000c0c0880c1041e0b4007406010400c40740039101c90318514000c4e21801d101c0d40c10b0940140603000f03c0700086100c3d403280c095402075440113402421541810f50500c0031a0170003403010740b03405509100c04940c44030b0038003d640c0100c4c00340c00c600d074848446145540c1070840b81ea01410847c3e142441490042c098001e050140c0c0d0400512802c8a50b92030002c42c01c01c01111380c1000d0602d000007006518441c124180a01c4c20003480300c60b40410740b400b44059501e00c01a00c5040e44215680400c800240090031528400515540003090100540c000b150a5607060300c0703188840c64011600f408a418641e404c00102d0020040d01500346c0d04e00007200382d80071495004140100c3c051310030754007898000d4200c04291703103038a01202d65a40e911100185481420701040b18000014004141c0448001883c02c0580360000c411070304641c4084100488144001c030004100741038202c80d488903907014802032240f1801400640256a030019000301261042402c0111142c60441595040d400000c2683e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 697072446 1250 697071196 697071223
    0xc15010f05010f03140c1305090105031002091c030206071706012102040f140111031c23040b0901051825050603160311090904170d020f19030e 63
    0x30f00707012500c0c003c60140100080d84000211500c0c20302c040174001000500031600b15451205080e40ca80703080052490080c031a45900d03901c00780c05c14056400c2c0e640207049981c001044499051802000132000b080150010350268108004215207940c01c2058200b04100c8000380d01102d01d01a00040c020303103031490111004021241c080d203034040d02c560440707014240a44802084907514106408071422103d0f0703060019911050080c1a0503002040c0e9002030090343c0031411024240315110010040f680808a5004a180c41e1154407070007819083d000d58010906c0d030405140245280c0e00303644010300344501413508540c01c4dc40c2f900b0301060031405101c00360f20360090001200b501407240e00f000d400c03c5a00c00c800009000b1044201c010f61078203c0703c1914244422511149008800d003d009006034100701181d0000300064201248505510850f400710341c2401008040c840072030f00400d0084520320800116204400402845c06038205214542400498120020141ca0310500401c80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 697073696 1250 697072446 697072457
    0xb03100507030b0607050307170406080112030e040f0207060501050306011d090309060a0f030b011d0904060908160302160f0b30010302040b030d09060c0501060e04080c15010f0501 79
    0x615600c0c80ba41007110400340c000c10b580d485208a0402070b0312907000280c11903511030300e070001c14100c000e00c0003603c003100c51527240c0d0a42d0303038a8048202c2d081e40201d0001c41c104580c1c020114070b2503407a4032031400e0b9102400d200507181c600f285812412580182c001ca8420380c081c10041140300040d0311003440304000d00320b6810b1581c035480300311031450080c2034280d64450004104002010742c0420030300b01040d41b99800b4003070700307003180c00550300149403d1610080030395038074506005050481c2c00381d1304a849200c0015612140d0740f5108031a030000c041e899040b0380f01424040a241d03040043c5026411707415044039440b0b141c2640e007280070420340324400140002142e21210042c442c400440c0c2c1c0040d04004000170f04070700205400c566401d0100301d128500d48075402040781400254a0b00d4504191109500b090034114243c1d400c12a00c0741c00c440c1503490340f6010940b44e11004d55140114821404503440746602101c0600345024080012211a002d40040000c01da408011303408991007800e00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 697074946 1250 697073696 697073701
    0x1180809010e0a030507030303050f01090b06040b031905040c080c12030301050906030f0a06020d0c020a0b0105010e0415080606090924043002010e01022b021905070210030b031005 79
    0x443d00700d0140c1d6002800c1c40c05039030400418580c040c0c0099100e480080002c0030503a80303c040040442c0e01045039036801c01014003040c400761403c80000c43d0407115400524041001d03800c3c0c0d0340103131030084404030b80c0706416060400c128a005c10a070003400d4012900e00e0f050505111115942e40014818140f060240001080903510b052017011062140d0b24203a03104044503003002d0b0040c0d4040c211850034203107007118800260303102051913000b180e0320060900d0240d10303100045400b91041c26210740c0c0030ba80c440141c45802c4100303103c40018001c2001900803131401504000c2c1420300100f0042c1141c010076488020840742d070340a1030404400700304011194039070b410200ca10100c2d00c0d0000c000c241482020307481900401140c2d04800005600034820484204030181c02d0b8040c071502130070b500001c00c10312501c40c9015200030002401141d001400c100901710786503410044040301d000418000500081941802e00180c080c4103500e003001c1c4941103007000803940e03034020820080f4250303a0780d101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 697076196 1250 697074946 697074949
    0x180911030f070e030a030f080105061611040b060a0806040b010503060901030f1502030a140a060b1e1312140a0b04120e030d110616021f1401030f020301180809010e 72
    0x10030700e8a910f0040c04440741c14046180103014124010703071810128401d03e0000030b080c5049821500200c40c038450007101a0070642d15400c4136a411420030741e110b40ca0b1a5640c159489401c040c1c52054983c2d69000c805003010400e000071110000e50362410417100308100452a01c40e1407600c3c0c1181e901c5034040015014901f00001c142d02c6403911980082c0c00003051001e0781c02181c0201d01480020300c402060350315540c103c042140c100784548121600280802d8406000c0700e10000d4840b1690913a00317141118029109100c804560014544902509400310a1060089e000801201810000d000c4c1400c56198600d00d2800188002c15060300a580001000c2c81401035110402001e01140c5080f155520041c04490540440d140948036131000500c0080900b140080c500800741c0141c2407404c00b0030300b401401440500803026882c2c950213100c2460820721800f41c02235002c0c1048001d01e0925204041c2910103584003246080c48101d03e41000c41e65a004480d1464000d08084001c02413000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 697077446 1250 697076196 697076207
    0x90209160e060304231002030408180f0f0f0d0c080d0f02010b010509040b0111010c09170a020a0302010c17030c04030c0e10050909010609051914100308130b0a180911030f07 76
    0x2811ba500c1e0f002000b4401080403010152a010924000300210b8021032000d2244500b01c160791107a0000710009001d1507810804048080c41c28040c203134811090a98581c0660111b0702d500084080e4000d0b405043e0b09079102c00c40740030300001807000f40242035842000801900821403241c0c400e554855500c416680100c86448070f14840750024003a0340b001c2e84c0040e1401c0541d10882038180c030200d600c030258000106810802e0342c0d0003403031800c01c142103800440355000142c0c021200402c6400d5400c64116404d0069480384403840e206c00d0b0781d40e04600e0074880384402030b4088251071260314140021142c900c0c0c0395200341c410907982c0c12010f969241d42c4a01401d210303030100d40c0603803410042c005240384421043e592001e04440c24012075000c842d0248140c0c604607001000001b20010034400030b520076000f00700924204481c0d0b01e8a64440c1099011a03000c401114082185191100460300114106030020005800e003004400c0010602241c90320005241d410750354524400198090f0041c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 697078696 1250 697077446 697077463
    0x405060130020403060f060e01050409081c1118010e01082404020d0207050c0915010f11011b08100602030c1905010f0203241c060f090209160e06030423 67
    0x45e03070910004070100c2c0481c0090100740a4130350f407070306080004119424680603140791242e200079514904444109410041da8054103a000f6032515403103982414106440544101a4109039900341c02c80110000b51411094007445410300c640d1030100003100c048021204034040000400054415034000024000d1142e0700c40c5070301c42d41c4045000d44c2841000101c1007242413094880601c60740725403045040039080317001031600181700c1d09008c154807440340380b1038003c1815101c0042810103c4110480300e0b000e05840520003d00c86008110320005203810400c000c2105002071844d001e0400f1586407034136000c507000702426500c1c484034401c01609502c0341c5403206000c00d08641300c1c10b141a1214080d14402050f501524480c00d0400d581d14048140c0760456996000e840ca00303664a036601805043d0001c9004d008a0792442d008001d038070380c00b01c124072035045c410802043c0140d8813005005040b800b006a070007000c00703200f00400208914614a01150b603800d5004610008150051070071804 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 697079946 1250 697078696 697078703
    0xf04030f0e0303030a1d0f071505070803010303050c1c021e1c02030c120c0a200d08030a0608060c07022803242c0a1403090405060130020403 62
    0x20030004030315000c0c6e02c82e0356102c0c40540500c3c04c00401e03098203a41d484100c107281c1c5040c3c01c546c008101e0701d020755074650014609030a155041481d180c862000c00d4000740e0040d004541c0000700300b00201f1040c4403914102c81c4a00f0000600c60b00d22000030341e11160340314811016110b850381d18248403c10841c05400d10014041010101800c0b400203441e0303045050450000e11030980c00301844140b40007500d1408510f4801442e494240d515580c044046c00c001d1070000703a0409104502d19100d01c1518500309024a288941d00d0410034001c00407145158818181034000704c05110340c040c202001c5039541e54049840032800804518a20840702c181c01d8500f5203105181c6001081000192100c1c1400c94544007400314103070020403180c12b40319010004d44036074040080790610403481c814480062501c1c0c07011a0b502001d035a40b240000c0c115030608400f40c2c2c1c0003052162039480c0601920341d0010007072900119060034200c04081c0c4e5005021845000b03d03408103c41d46150a80e410764005541 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 697081196 1250 697079946 697079953
    0x4052103310927200d0f0c031403071e0305090612012402030304080d1d0c0a14030604020d030e0315041e02010815032416030203010f0311040b041b03050105090f04030f0e03 76
    0x38a005441c0740c14234402122101d8170040804005480030065416003900951842c64903003259008280c0c02d2403e201c12014880300b480baa0410ba1904400b03031a420600c110b9241c807070350500026640341030a450001c1891521121601d40e100d6021050300d8003e0350020690389c036040840c0340d41c4042c003695082a41a081c0401820140b1031000440d6a601d140c01c2d905400070702d480d0b0906c450b40310b60b24124650103074003810205005003880459445001e00915008051440d44000282082d50302081c04019041074024002030112115080304e403240c440600c2c1c5441d0449600280c00d41c2c1c002004001c80201d03141800324a5241408000c40521303e801612a1108600764a00401c40301a1462070b020031503c040e4040d224000e2086906031350b01e52560740a500e01c0c55540303640340c590b0b12003690303007240d103490a1682c951240d00512042162800d0b1524024046030001811200c0503445148165003440a211680074405400703278205d501407605014a841341c810a55010800302d400c25014071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 697082446 1250 697081196 697081223
    0xb16060207081e19020604030f0c050109060e0106090b03010e15090f0a0b0f0702060405030f07140d05040510080415020309031b0304052103310927200d 67
    0x88401020092401440c00c04c40310148881241c1c1c0d807808440003001700e4121103400c1002d50240c0f42c090070240c810710012034004050ba07500c074250b40340040400011703034460a0078801f40c202401450140340c400c0d002000b00d40044600c25945000f0310303120300c2050071a1000b0506015003070000c00300f0820420100c80044090b460082c50300390003200d80c12542845080492002d505c0440d00707900440c2c01000850918010b4007110080d58030121040b10745414440b02c49410000c00c1c8029411000c0517240c0d42c0e1640e01c0c003400d11030380720b210801d09000c0203030140400000495120b00c003213600501c00c074016201d0b9113604031b03145544141061514090003542c0280113100f0b000004106490054910b80100302c140c4401d00742d08280e05109062039041440740d2200008208501510340c0c107945803400c000400c0441182c2c2c0c049554120079078580d02c2d030101c0c3c0c412144210501c680304070504a610940c4c2d03181d40325046090160221281020841050080580c1c0c9890105003980d800408490031032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 697083696 1250 697082446 697082497
    0x20703050d110901091d04060b06091801030b0702030f0414010c02031f0f09020117060301060b040803190c4b0c0509040f060b060d09060e070b1606020708 68
    0x143c100c50003181c0042c0301080d000c1030007503160000c200c102c0030120345100162140e035200000740944031400c9070044000c0c81148807590760400b0606071416920b19503e601d50460405403d0344500400d100199803003001440740c0c0e13956400803a0111380054003031340007802c98080101d5400c0201040a0f5052062400c1c1002e48011036402c05052040320700104100c94070290140c080e0340c81c0800c042e0201e40320f601d000d0001c041900c103141e4000b4004000246503a1680615003681c3c010703800c01d00440d40041102c405100c10320060608460310760400c10a21a40c6a84034203e00074080e62010a000d41c200150031082c1c1e40504140d0021160102c4059800818891804850245106a4854505c5540019103041400850b03000c3d90f04003d01c9038820511380c031074001030701504000c1c1350440b408000c0d1092060040c810500b055200307100114031000308542e850b01d0694507412500c0c00c2a0104044990580704010405085502280168490786141400615400340000b0000395880d000d4958404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 697084946 1250 697083696 697083731
    0x50705011e0c020f07060207140a030f0506040303150f050d0303270303140f06091801090f120206091b01020c0a0f0f06050909011206020c01090308010f0603020319020703050d 77
    0x12150f401c03036000d41c01010b102540c880c3e19100ea0801b68210000078400f440003000c1c07480c87d01030b01602d4540d00e244c0e641da0f4605036014902041e201900482d0a100415a00d4040c4001504001540072011410040e007108010010f1240c076202d50140d0f401441014000d8002940c2520000d140c03d84e407110211900703040c140c2204080340082e14099003a140900e80603182d41c021200203040341c031141e650000f80440000081c002001000044101c24038016090242004052207000040400300003483d02401042d411802103041d50080020810400030004998102e804110720b0b01c0603042c9583e0041c1e04200d5480c01d01a0071000714030010609004ca10340150446202c035007001c0c40a5902d07002244d2902450f107403994403090030030040003241c003501e4859410602801e4014a0711030984180760171610301100445c08a070303200004000d00c2118501010003403c250800b50b10750704d001c450f468030b0464040f24405907a940422008141846141610b00013800c0101c00c020200315460380074072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 697086196 1250 697084946 697084961
    0x110d030504061101060b0a0c0f05120d0e0f0a030e041104090203040309051203073305010302240909091606030f06050f01052b090b0105040f0501050d03050705011e 72
    0xb10300c3c40c15003205011014461320044400e00303c0d03003504002c4c100008031258404941c0170340c1d0501048451801055052040d0061034071810103060780c030040c03440c14005503081900d46559640181e049146126808a180c9000329818600b043d0590f0002c80080d001300442001880f010300081800b28540d1900c1e401580142c1c001c3d15802212651441003000a000000d0049440c3e0828880000003680b8408952080e454401807040007800380a03002c03a4401440405d43c0600ba2540010400d40c10a2802d00781d041d812140c5110f5036008030142c8402c588240c1d00341c01d0192480d00000f23540c068041c001c50a010811300385e09010281d0740e90000340603220032010104894075040001885182241007072202040c107071541c608081c409012034400b805e0b420141800170880c0d00e0448441021480f41c13480141c420210802d031541040c060000710340d0681000250036145c00c005110565a407031403d001d0701c0e07251030060781c3d07440c02d8a452805000e03002c01c1944584600b015940000c1c6031a0030440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 697087446 1250 697086196 697086209
    0x221190209131505070e10020109031707051812030c1b0d0201090e181e1b0d0b0703181110080f070309050a050303130209010e060105090904110d030504 67
    0x41558031920b400c8408a550090014240140350a40c0011a00c00c1d8204a9100b01c860422106180c00c81000c10f2000710380c0300c40480140d540343c01c40300130141c212541c00ea40d2026010300841d23a00e004000076015100b18400c0080354124400c3c00c240395910400501541d03c0c420060300e4a421029001f0b5507035010320040c0525005224100301007504007002062440d83d0140e58600d002858060680100c22000e00028501220714440c2c0400b040104107628581007140d5035211807622007c003c070304020040e088102031240320150b0003076640d03071001114081c43d000342400384180c903030b2a002d81c0104484c0f0f9000d41410100c1900006200041d854408454002d03039601c00c04c02c00d030307000c11100800d048911401100e00f81010420283c4039600c020202440b8400712110b105003500c525195400c1190122a0074416144031021070030f08403840c40c01044400075007051807c0000001e80240030f90017001c0d004881010001c0c0c180325001c44244804d480151032000074007903a040082140d80035001c0c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 697088696 1250 697087446 697087459
    0x2030610050909070809010e0604081806040f15090f08061602010e07170f070b090406330e06070606170307050717150f070e0d050a02211902 62
    0x9190180224120b070b02e0158000c1c400c0101e80d03910311064940040203400f44850307650b01c04180b010004200943c501aa0003858910345031040340090010501c01e40304041e000b00404c1c041040010300d201185425070307044c003898a81402c841e10307080396107240b0b0350f01c42600740c0d01c00140020550004996031340200d54410140c1d00c11000b40100b0307400c0c0c800080002006900c1403008214202c01c0c1d503214507078140703280c1c280d400360f00302011070b40d01e000c219400c0320800c4400003508601e18503052180c68000c0401020f100c0781d10000b6840142d508800421016414440945400900f4440c2075400c0c075007a00200425210702580c1810300090515008801001000b9030380d11a0501001090b104e140c4d5000005000241c180040743e003506180809900c0359102c3c050420142d56000407010744520901e0b04020365600d0040c4000b4003592001001c00e01400390200600d02041d000b240161600342c06545c0f203490304882110007094689000010707042c40c081c50b031071601e01201c100346548200e4002c844d107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 697089946 1250 697088696 697088719
    0xd05010e01030f0b0406020903030a020303060f01080103080307030b222c0703170f160b0703060308090402030720011a03060f180a020409030504080610050a0902070203031309020306 80
    0x80c10100e80070301002e441e00c250080070000145090044e990701c80d1054001605101010001c24a190885080c190241c0c00c04001c00c007082c100303030042c00e1003400c0900c0c20311040d51468507494024440607000b04c08164507011140f100d6141c02100f000c40344038079a014500c4150411f010300003000360a280f10030301c0400018580e00c03203044ca0151190030f0b00f0400640741c6a0300d542d4600c1380f254112100c1c40207440307080c0900400d444108000d0243c124a05628a548854915040c041c0040040a14051600c2c000060002c540386500703444200c0d10a840042e40c9441703569061303e040107540c040e869044030703800c42c2c10244d90041d0030090b800301110500c5015203070214100740c0c0b121803c03511449084a0840095a81951340c0d0160125071101c500b41d609003010b90300450195a2108010b41c042035001030200100e40c2c04204413036110b003801f442c00004c1c0d81070100003002c1100c24071400c06031700d401003985010f5550a00441e0511140e03241c0b64244a9540d080500c065082110300318402e0203800311 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 697091196 1250 697089946 697089959
    0xf030f0703050c04050d02030106030b09010527030405010c030e030f030a030606260408040807060804120c050706113c0a030f12181a090c030703060908120403050d0501 74
    0x2142c1c09140c43c00e1150f42030900303100a100c058445d203d0160781c95926442c001001c103001c0c040c550702034695400080b50518011050f21448500c40c4480101c125900c400803050160210685041d50424a0059103035040c0303040488580021446156150055520403070581000200901486500e606c091215a645002c281e41600d0010012a04601d600c0984102c000c480030059512600c00c070380c0d10341043c1e2030f116414982003140d000800828940810712003030000442140701041114502000c03400341c5940c605850341d01e24400c5806001c00242742424006007404015880c1c1d06501070441c222218405102c08610108840b42c2c1c1c0300e640c10300d0041c01420100d601c54105070183c40d07034100c1c1c0c01a040100c400488034447c45001c69030341d1000000c00350680d03466010450140e00456042150315000d00000c01c4094842c0320b07103900600e0240100d0b180807a00e04200d1780c002030000303040851420483c40302c0c410616460660031804041104040d0044090401e249a00500300166a29402c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 697092446 1250 697091196 697091201
    0x10513060c090807150c12090914010503150702011d0114010803070c0b090a0b0f072015070807021005030403020f030301052d0312040302040e03030f130c08030f030f0703 75
    0x151900d41c0d008410184445124006110a145603520380011724010b00c0d00c0703d09081e04074030014000036100c07010405c82c27110280901c180440070034100e152594500f1000036a201c45040540103000007503c005503182d4001e6112400034100d541c00443d0065120210314001c2c09942080c802107460a0004107c0c24030000580340f50700c3d40701c400b06208908150f0703a204140c10480c07400d07a2000301d10304041000380302d01e40504480c5038110300d4252114014505002141048000c400d80c031060086141010394980c0020250300c0a04101e056a4490030305003c040c5220b4101c000c4e400c6149081581d02d844d510100441c803d9000c2d80c20303120290a4180166201e220078404c3c29070101100410320240c54a00c04109840418000c43d640d030001c1c02401300707081810074141202c140001140030000d605160280410100000c0091444e41c0783c84041118030986c047c00c402031001c143c4595000308427044500724040c00740e4000b02d80e1107507a000c00c0807000c0c1e401241c0080300c6502c1c1c0c0010809503030090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 697093696 1250 697092446 697092449
    0x12060b0c011409210d060b0a081303091202060403120903170a0f0f170106120b0f0d03050c03040f081e1b060a02070b190e01080f160c05010513060c09 66
    0x3e102800a68508100f5800480c4440c40c4501c24604100a2031a0910940c40355100909002141c203469503086032015000400080c9500500e10300c100c010000680e000d0354041c02c1d1000b4641301e01c03040709103002181003800780350801008600e61542031000700e038200c4508021644503d0710420280c035041c0161040e4007801d001500400e40000340c42d00054002d01683c0b2496a09280480c0d1080c03c0ca03480040d440d07000c0e40280049103520180304401030080c003a40c030040d08203854021139000b04501182e50b151414002408024000c11082440007080c821240184803455031199059146e02d4041e488134800d8010038625200c0111a820850020400800c586034941109084001000130310540d580120000e004500840402280c0e202d0420050b00b5544461500410401101c0002919602628031428148640e032010009c04905207444507900071400c2c1200011034401550030b6405040410000b000d035420141000003c1c4000958000950f010311000e109115000f03100b6600700311103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 697094946 1250 697093696 697093711
    0xa0606050f06270409051c0219110405090f16060905040b090414012415050408030301140103090c06033608160209070503090c0102030315040c12060b0c0114 69
    0xb20401c3e003d441011404031400d2120181000c100391403140d032480d0404e806800d101a030850440d14032285544d04101d6900c0c4d885140f051075440081940710410f44401074803996102e40e84902c00248458010701184d250108c0344401c64040c51446c0890b280203d0f82030145200003411000001b89518240c0075801c0088000b0701701400a0b1620345451041c00040301c14881250b48031205184410000000f109400019100b101142802d1019294600342c6a0b64403204001c41403006000c01c6402204483c11100e10001e400300c007038160001a4060900514080d105a270051400544143c0540004100030300d00702844200b03008030600c56600712072500508807a082801e060b000001c032408011f003004404880100142000e40d030001d211040c0803a8104001070b404000c1c410740311410842c05018010034005541185400402450002185074140f80b24035119005101d40c5405082000050221502c0c00e01c031860b1034a94809956100014107a100d40c6007104650181c11580145401083c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 697096196 1250 697094946 697094977
    0xd0903021b040c08150a030c062102070302060c071401050705030604200406110a060603030f171504110d0c230f031b04080d0917030c0a0b0c0c0a0606050f06 69
    0x11a145803000c1c2c5c86009183d00c0c4c00c04c40d00c1c00044041088003000b94002c0c070103540c45001d0442c1130b03060054216031954002d40350f00d0041c031201c00020703004991a0f0380015619645a103550303440c100505070201c1c00301043e00715440c2c41c051180207a8484000d510035a0142c3d4140240035950800800313218035901e84824518080c0700503c41d582c8189010181c100141d01240e40d03815180d115941290460f52080380402ca49042092481e5001541d2030200703401e4a51024443c5040124815074413240d200c060f10039681c030720740312048414040c02e50703d111003030b820200f0451100c040083d2400c115064042864842d00d0030609040b0f00e904101c80d2040740c1000898116180c1d4042e00f00e94584601402c80d0b100010311004c5400075040250b2403459004d5500c40c4007a514210210544603444422451142c10803c2140120725001800c00e00c8147c0c0460007007103d0760394654032040d030700484295070070034061902d00d9014065247c002c001a502c003151444410403943e820001c261040e07a40088541c003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 697097446 1250 697096196 697096201
    0x20d02120306150d092a05060d0e010c12050903090d0f051f0603060501050d120f09151d060903100b0307090f050403090b0901020717030d0903021b040c08 68
    0x14103000c05103800c15405031099440030203001031840150001d44a103030301166100600c0d02445080036003105103141442c00540c007484120000c544070710302801014081c200000e1035101d00000c51740321144461050000704014074003900c0081143c507034448400385203401c04020070880c5001008036010702d50000c140400140007641d40410001c0303800415102c078001c5d840c4003062034400c001072501c0d1490700440000c1160441c5000c0003140c0060300554080c10f00c8002e4040051032080301c1c880d0104403400c003030310f40d001c140380201d40b4103001c0d8019601c04481072094002450b080001d00035a0190916030988800402c8240692402007507007007680f42d40500108802000b244d8480c510280002e000d45401a484100482c151032030b51000240c2a5943e50821061540c410801006017a050300613502d4041d040300003d66400e224064000181d4050b081044800010002c40c3c011803841103081c080440e00c2d0030042e41324001160041082c5a009100160518080c0f103803c810b50110b468141964 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 697098696 1250 697097446 697097473
    0x303070c2906011805010f110a0b1f150f1d0406080a1a150111010b04051519050901090f021c0b190b04092c0601061709060c07050a0614070e01020d02 66
    0x108c0888200c1e000d01a0003608000b05101c1c6011620400000302c10b101100c801101c4480c40400e10743c0302110034118060000815503002c00300c01c001159910700700c00e1520046440c017100b04060500c075035000c2d10301507001820820110300c2e207410a000d1114541080018864154900d904641600c0744200c13000c8021000d6016030007840c00702c08204c0001542c03d0001c40070a084030030580707101500a41d4a00050300d60f281540c84149007812441820503681d103464003085560b081802070f02d11058407000d071410801c1440d819992940c02020340c40418032940252000102120b80c5540d000301c03500201d815200e1600a5070404940c0c255094501d400c0c58000040b00624001c1002510300d140707041245840040521620565403030440944010351610704060402d81d0342001c056060f130a4941000180e503008900d0641c81b011680d41c003a92500d442c603007581403141710000180004d24191110883c08100400301e44158030680710742d0800d004000069964038030b02405400141e0005074042100c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 697099946 1250 697098696 697098707
    0x909050a030513150c0c17060c1b0307060204050405060616020105091816031a2b020604091e0203040506130c09110d0c0905030303070c2906011805010f 67
    0x1440741e00d03c0c0c11250103031540c00c0081e01c0d541c00d011280005000042200c288003580950800808981d00c4036902e0090005181d9210300380203041101c818804290b640e007541c8004505801ca01c403003400e4941d90304451408000030340140c043c40380145d02c3d04001504a04080c030498299000100960340520003541c0111442d42c0010075243c0c0080c0024500c040c400d600501c0f2074000c50240401c000740000d942c0000f411210607150718500c065184034480455200c00200060002e400c0ca0800800000e050740c0903907441000c8002500f02d600041c00281c0c0b4802c0790b01c480301c01d505100b55450704d0a915682c1006032701003614058404c1c1c10800100e1688014400d900004502c60300140c105143d541c12158100d401c52011440714810014544170304240c14410200580c44505103910300344d0400002c01c1d0380f400300400000512008510800902c401c1d000941000d40541e00d160303902400d4550709208011041c0c400502090b0158441c0f01c060707991314080c1040d030318180c1d1007890501040004684 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 697101196 1250 697099946 697099957
    0xc06050603030f0d1b030b0a05041d07080a120903110402071103060916050303120712060b070c050f09150609011701030c05031c05030a020f09040c180909050a0305 72
    0x1030501c4104200b034901445400686101106a01c00051300501c1502c0349000341c80011740701d02010720305201156255a080b140d001a0341098400140320003103103001c2c0042ea180107401e800da52207100c600090403240003a40402e400d200340c080300510308050000703613111202d40c0801031180d881d01c4c0705110181400c1d40503144650040d501e1050085240c40400d0a00c0c00503034009000740c00003403806110880c0c41d00d00e04001c01d03041d8011340c90f180c007164030008503990280c4030404000022120000a907540d40103031002d05550034a15030380d070246151109605c1c16600c1604d0051203907554140f800d10300138180a1094441022146071445041d04010085d4410f84400303042c0000000d450191140120700c80c2d0113180300d00f044664041c104000c00d480c0501070103034680034a1100f4503482c02c01d9404810b0707a0708555152000f50f200e42d00040001618042c00e908260014076241c0c1d00d40e000c6921040c0307201c000c2207003a100340000341c0b1000d9007415600e000601502d01c0d8000400e010019104100400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 697102446 1250 697101196 697101199
    0x503090102070f0501051b100501060518090f2a04090f0b01020102090307062316230709050c09060325091a0f04030c03050c041d0a03142511040203070c060506 70
    0x802c640b0080c8c00c50011200c003170308078500040000c01c88030384180f41030365a96008042214230b800c1031303d0700b00e43c0d090b1440307002081d8400f1402605503803800c039600022a6648206620300242d211600c400742200140551006044068106000e0580c3c035401031003110070320714002d4040c0206608000040c0d400010b030040250514041000e407031401d80c0310601030902404c0412029500c04031030f003800d2105074048034025140c908030102400d031000000400c482142c03034020000c11130350f44140e1000307030900502d05004c0c1c011100204120f044400c840d4007800581400700c0101e05403920321006c079601c0f080d9000b0084403e14603820010340040100292841c2a800c403071b2186003a4032070340d81510010440e80102c50b00d51251041c00b100d458640980741e00507420070040a003018030100a90380c0c62015041c054140650019800802d1714103400305c0c5d56420060040545151056020b12600c40d81008155003180d40700040031580d1415000f02d9006010603680d517110030711540c440500415002e0b0dc81c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 697103696 1250 697102446 697102453
    0x7030e120a03140615032d0f09070602190b0a0f060303050c3a0212180112060b0f1602031f1505090c13030f0503090102070f0501051b 59
    0x44205915a00200344140842d074000c95070071224280a1001e0f600901018820750304c1c035807440c4150034420141c80d40100e251150300d0411030039254201d1442c0114180050b02d4464400f0000036003640040e050081d03102c441210007403650b030a001c0340c480c12003e124940b03400300e00d940c10002c43c9000030100d410503922000050702016004802d4116842c50303000300c010400c0850001c0030020284540d51244c07401e041581c4210049895114000c54010910307048414025200e14110f0310801031482c41d40305084c81c0030381c2d8080c026001c10046500b10600f5002500642c0c0342080316500e80120011200174428030360511000c11810301c402d030090000c000721703031440c03000720405a6010000c084c0700c0102c1d6006020107810680310720341030310f0025401101c01004d0084c10402502c500d90219446a400381040d621000c802c100c05010b125030b940054003220001c0556024404040003c00c00400d09800301c070b801c03503590504039181c2d240c83e02c00e0714003184040c0844000c50720141085c2128240c403200380c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 697104946 1250 697103696 697103713
    0xc010503070509040e0303270307020a17030702041e0e1b1002190606050405060d05062703040b0309060f0103030c0b06131a040f06031112070302100c030e0f01050307030e 75
    0x10306c0c3d0717041103034540f0000c0500c144080584421003a148a4182c00d44051807030b041e00c1c1c0d00810400d4803507100b00010010101c4169100e800f050090310020f0303034000e10074405a1003400340803080504405003110418902500107c0b80140080c00d15030041b2055a80b0b1806600070742040314407901808060b0640c000c082000490400846405a000784130308070020780e5508100a020450b24000d0403540507114008824001c1040002c141ea40a44000f8036040c3c4184c9408025103248480c130071004c040e00c004980411414003800107548184808070442e09255110303c5403070490f110a10014001c940107544082c080b4659204050740400080c00d410105040c10100b0702c100c030704501455130072000412410003149098005c1c500e5003d0800014001c030b9080d6150040d40310081d0030124441d0040700d419040800c0306001c0d440c007c5130010500580403c401a01500c40b4200880440000b0b40e01500e114051822a0300e2005451040c0c0d00d06085555412040e0002d00e00403170751701560303c600e118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 697106196 1250 697104946 697104971
    0x2040c020312130f0503070501021e1c3201090f050408030705030a1116120815040905010f110a03050603060c0a1b120c0c380403060501260c01050307050904 69
    0x11f100c0c05214400060384c804911003541c68551341c0351120343c0c4201e0100003207a41c001c500c5070104001012001c000611703514041200380e200d400b542c445d01e000708241c4c519a0b401c9228030703d1103040310391014003030100d2140340204a003125002c48000b05500020b00201c0c004a01ca00003a6a01101c54075000412020106909003d6003143c0c002c004414650302007241000b10845901d44210001e00f00b58403581029030754810003211840704540103640d540780541c280b00003500440b5000c21407050412820640d580c14001d00c0c2d001c00404008a0304100210703c050800040c0b00d403140d81043c00700ca0078451402c20407030f0702c4280343c11007404800f00c00c0c0f04040030030700c0c170f5030758440d803540c1d980706e400148190707140c0304130352444983c0720721f10b0850f4001d0780e00e001800440a0604450030100046a00340032102c41340500d000e01d400250040d0704d40400480c1e035041c242103003000f01038406a103c1142e20b182c0740f51a600c60484200600040051001c0349d89940290080d18841e6002040821103008030324 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 697107446 1250 697106196 697106203
    0x90f120c0c0a0e092e23040305040f1a0f030c0c07260f1504020307080d030207170a0c020103050c040302060c061f0f330c02040c020312130f05 63
    0x820044043c0f4105043c808031010402c4841210103840080190b83c020740001e40c0a030002d484009070030903455a40e0241c103030380c558401130a0840a44402d03084c60905040043c1550000c1c05402e81103007644602054000401d489107030302e080b07010162490030b40050980300a40d0406440800400304c140300d0042c03c5101400340700050400c40c50b007000803140d1050303102142e003400c1600450310703042071455402c40040441d4080905802c24803030b042c40d031201c0c07000c01d2500b6070307590050106024005551030000e1741038009001050140809454001160004085611901d007410001c42d454030906001540241c0026030320003400c50078141029520703004150a81e000208441d0b09802c80010050b4181c1d0001880d1408001940c800c0c110340d00b41a1060b0045115015000d0710070140c2c540300f408040c01e0059892400100280c6600b2820341e1000502900c0d1030000403440345003000c20b084003052001040c0c41c880f00304400403d140751104500c00345401da00000075032301c0b41900ba074010042481003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 697108696 1250 697107446 697107449
    0x14010803030a0b040b040207050a03030f020c060a0c11030a02150a0507050307030e030f180a0e13060e01290103050c0315060c0102070503040e090106080a030815030c0a08070905090f120c0c0a 84
    0x49e030190482014519006040360a0441103210039031041c03000794480400010b00300d41c4220261070000c0c100c2c074840c4040c2c41d40c030f40c1e00000c03082a1000041d00c0e01d03941d501080c4550150200104040940c0b2100c00c0c00381620300865040d0000f030710a00c00284054400d410603001544d80c4019a403820718501d010002030b030b21684601d40010300141c02c51006040c0b401400c80100341610440e580307402c1421500c20140407084003e00100e4480c0145100e1010030f500040308014000b036070300184080085010ba0301c0050602c082d0109145c100005c4440149500310b038400c0120042000c408031240701044030715000345403030f201559405e00880c00002c004000800150292140407003507490302503501401d651294211421a8004114181c0020380010320b041d0425420a024034240140d4000720346010006041c20758440040800011803071008282d0b03009450b842d40c0148072a2360342c4962140d841d9940c2c66946283e500144180c400303840c2010140104454000685030285401800940603e159 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 697109946 1250 697108696 697108703
    0x2190b0c0312090a02030304030b07051306201b2205090a150e0307030c02030307051f0e0a0f1212020d06090c08150907020102070209040c0914010803030a0b040b040207 74
    0x90b00940e4070110100681d0006284000300b4109080345d001c60380b00d005600c001071007014600301085c0d201d07029005035100d82412940c03014001d40d0b1894010000042d00d00300103850503290a60b8021040c010440c86440b0304140900c902d00d8181030f003800300c04001052001e09044005030080e01f07000d40740c0180c5008180020040c65990401e0404064116010b12000302452400391070003503034000071081e204030b20740501b0032541880d40d80c00861700314442c905000f0b0441c001c3c82602e0324240d404003088103021504500410280c020204510b58904000b40013410000b49101c2c04c46c0080d0102030821407000c11450301c0400d01d241e0021000c1079030807118031030380c0c03083c1c0b183d400784141c6503140300305288101180381801c00d6080c2a001003801074a2090b2071801041001c0c006003216000350112100e696014144203054501414881502d4002d4001c080e03015051115044403220401d00c168141d580600245146d921146044402440640340c0ca541040e1280c2c100140c960b42c1384081e012042c007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 697111196 1250 697109946 697109953
    0x350a0c020414060909160b18030105160e031209040207060902090f070305070e01050315041b090314060103152003130c05010f1b080702220e01090f02190b0c 69
    0xa11a040118900700242070550701c0e0300804602d468620a00d4028084480d1080c0342c7d95a08400100d42c0300e8590344a880541641c240f40031301c0003102520319035050300402c03a5071304450341c0400350070940c41345e01c80720842600d00418060f6040d01d00c1d090340200012403003980002203861282e8007141c60410115a10307107000002c08100103456030540110fa51000c16031030715815020006002a00500010300400c441d03c0002c2e03141411070b00c2e260b200c040c914950a2000030810720380ca01c01024156140012580400032042480344103900040c104e060381c3c0d018038000b4400000e0101e200090000b07410b503841050007004041a0594181c1c010340c09a101000066042e80f01402e004c0c050a14980c0003a0400c080803003051106644100c8014209000e0280d40150f0000b40c01d01032030ba40904880654030040c4050428499811801c208900c0d4407160740600c51203410a004900301d9610305400f4105120030341500c001494003040c40d401c01c02030406810f218a8850420300640d4002c0701c00aa410350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 697112446 1250 697111196 697111201
    0x405040309090b0906181009110d060806010e13240507020607020c0a0521060a09020108010902160b07021c08102403021b0a030c350a0c020414 63
    0x101d0b4003c11081d0356042e1511000da04001001c9800c1c018411a141860030b02100400c54040c000ca007460014030900070184032040e41c8036106091a0322541000540758900b003c00500106d0111705d16040324040392040c15540d5030000c03404000d00303540000316400d00c030b607141401401d8219405444000d805120001d12494407400103480c2c03110290487e0255407010b551092903950b0f2540c480d0503240190b8200c0142c07a21600c0c003041411040503aa07040340168010401c515445600054040d4000d0341c400301c00d40d036030308100d074100c1c401c028840c0501000d4007416004207451030052a080342161044a986000a4507021626014400300d40005103455007405000a0003403107800180941d4000d030300b50450b0303a0300c0100c040c2c4200e07070480091680120f4961200803419104603a007038680010796112440c80d1900410016641d03004446010700f03110200007545a0410749800c1e9541c40740080400f03c4144180480340e00300340001c00420003501e2070b0100584480c011984003a40c881c00608150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 697113696 1250 697112446 697112459
    0x90506030330010905090c0609010315290a020c0d11032b05090f190509160f090503030a0e19090212070206130303090302030403060608030c0106050301021602010e0f0405040309 78
    0x2100103070301c0f1905031810103062040c02080840c1f4604000802c80d08166508980c40069000e0900c5a200c48800d03d04180c4c00100900050702d0400412020b1441c41c00707065016041003064083c0301c5400b00182d000340c85401003414542c010000b424022000060a40351b80000070b490b0a800e5000c00b0701f201c0f07004a56000307000840031032032071141036420a6030515181c040400d0b08024403c012522601140405140300941d4644040142070003a200b00d0107440c2c04541468540d1000742c0c2d080004a0711051f6803401e5128810190558000070003a61400040c0d01044407000c03103113a982035200680541068290140b08500c40007000002e201686800c44a00c21018151000b8034102c1590000070400940001482800032030ba13a250a0014035100b007410b0492a600998000034681c1c0d191030802701c0e40420020151682280720b60003403044039110800d00d4241d00592031199810200b0705d1102e40107600480c10340d507402030058210b4410024082c002420346030152010b03404030380c0d4590103010301d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 697114946 1250 697113696 697113787
    0x15140f03010605010f0503040816051c14030c070c090608010903080a02090901330309021f09090c12060b070b011a07030507030c0506010602011b0801030803010905060303 75
    0x2150220002c11009241000180c0341100b42e40d1100304002000000508209000b01039800000211810141d045410b10300300303544000010900c41400d40d2140080d51503481450080308401c010860341d070858466014060280d00821421219240e13040c2d00414bd5481c0c502c40c2200800c1031400102c1c01c10b4a509000c1c04040000c2d048044040c010407071108280c03034200000e070444000c021512100c03003000001d9500b2040074644402c0d1070810452400b0050742c517801c5040c481c1d00854a0b2002c0d40f460f03510822003c600c1100410104155007810825444203030b001d4201c0c902c041c00c088030030385841400ca82c1140c0c0c0c0d607007044668050214841d024407010082c1140905900c81d032002240d260b6094844281c00345600040c200100000c41c201014441c0500140e00c5921504880440d610740102034040c0000010750401a05a0b84003400001e105030203042c101c0f50082c18181c0f4503428507191794003511005004c141c143c441044040f0000c0c2500d4007210f91400c2c40ba000c80c180701c07113b6500022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 697116196 1250 697114946 697114969
    0x20d2a030c03060803220305030a08010f210209130506010909060e032701050f03041208090c01080a0c050918070f03381206090d0207030c17011514 65
    0x4040c90703c1418040b20100200303c4401c5008041008000301520340d4401c3c021045400041a03400302140200305650480c00f814141d40180c1d40d5044450707180d400c90f000440c0031030801c4009030304501e600d8000d0708080c8140c941060340380c401d402049516842d83d901d0041d0a0340b00b40714603640c1d0703516801400300790311039901a84580800b0b5032801c00d400c5401d00304804482400c1c0b00700c0c10328042040311a8080d20803a1701c000c2c0540074054403840c180c1001d030340d01c46074242208045003201000455030030020131031810342401615408500d4a8085561004054080048082c03200801c481d1f1000d83e103003000c002e80b0b00140c0811611300d1034044c80091801c80c80500c00002d0600b040b90031402903810f680300c0c184007545d003c0c3c0440c4008070044180c078185010f0403029088800d80000341903401c0c011560350700c2005068100d642038414010100d0350750701d2520000d0b1909103958000c0c00125210305030340302c081e10100c0000c541c3d80c403440b00c8200816003551003240e10500c501c003204500d00784030f8414007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 697117446 1250 697116196 697116221
    0x1120f1409151314031902100f0204061d042c0f0c010c15060b0a030c0207051207050d050a0c060e012010020a231c0504030c06020d2a03 60
    0x30018240440314003c0c030518030390001d1003032040c0045040035010800c152860940c50a6599500101c0300b0307030203912101d00d502d40442c0c1c4e0b4206181c000c4041224000c4600300ca10f80c2d50350b10b0143c03c0901c5084003502c0224801580140c40c0da0301c4502a0580c682c0c031511103044d450110742c0919401490311302d4032070303000050003103a00606401c3c0703403e81c0c100d030840c4240e507000340480e0300068120711514010041074100c0c4140e8000850b1b070448055050380540c00b0700c1e441d5001c40e41c01340d444900300807443d0b422403096036465000e8a001d0040c1d090000c2044520b0b032242c800c0b1030a00d0040ea58080e84d501a40d0045400600640d50b106d8056901511b6902e03040c00c018002080d07c400c0f00000394407064909074140d41d66400103810b014180c0b044040704a052584a25420038010617814207241d0f030310015144590510070282110036052074850180640d5141d110f400c0b2490481d550344003e5000380100108186d41c803643c00c2480064018841c20300c5074401040c440b518086000038040f22410420300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 697118696 1250 697117446 697117483
    0x803180d08060103090f0c030305130e06060409020c030f0d0f0b040903082806081e071202091510030b03010507030e0a11030f0f0706170403020c01120f1409 69
    0x100303003103500300384520341000c82880e001c01c0200340c074188116902c0e08200010070240c1068000010301d0380c860f0103801d00802a400005045648900d000c10b48c00056603007950250040004100e1a40d01768002d2010302000020740c1d09100d02240d8201003900f155446c0b02d18130b0f4803210f00107140174a5100d04a1014000c9a0800c41903d250302c0c000c0a0260041c41c05254030f4480314100582c40039040e00c99030748007448005002d104c1d103030719699440e051440d05c9800101c42042c001c1c92004004265002901c601c4044008103940765000c10010020191124440040d02103c0c9003032601c0d45069614002e404e42c80204841e00c000d020705007142c0c2e000345945c04040c64042d40d0591858081404068160071948206606803804000fa003401600c40b0041818411500003441040021032140b088401030345aa5a4495458860fa00010030440b00100103811000c00554190701610f00315021013026040002d0a0107600025811100c0d61a0303a1807000c030420b0200000c20b102080300144603141720200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 697119946 1250 697118696 697118713
    0x130e010b0414040c02010b03120408060705040b0a1d120303040b100b0d200c0f0709020a052208030c0703021c03050906030c090301050f010303020d020f0c0d02031009080318 76
    0x1144000611100554803803500e076031513200e84910035040701d804a40004e01341c45112084040070301c3e160f8403910030b5001c14000c071310001d5000b074040c0e010f41c2c0884400b43d5008d450001c94ce9011035040300c004181840300d60762183c02d07014a4070b031071400ca07aa0003510340056507282450b007824141500010301b942030305120010180a440b6060b4141c851084d030045000c5580f064030728440c1404000e10f40800c44818000c6000d240c4440002260b041000081064440321501c0b4104070301a0b01c10301c1d0780703900440c00801c42c0e1010b0204600b005540a4113000427000c0d039544940d500d40c1103503c0710303100342d01c2d80c3d015a40078004d5141c00b03a0178a40300111030f0b1400490748110b55002d4140d018580c1924414800400014038182201c011203690707160080c02000540313081403007078985240170302003680103100321000c01850600014a0541950002d4000d01c001c080d1441084be0f07042c5803040c1242c0600440a01d030385100c07841e01600301114800c07601240c481c43c10034641203000f4140480500e03546d005101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 697121196 1250 697119946 697119959
    0xc1005010b04150201090b0406051e06180606130303050d110c060609040c030507232e0314160f0804110103091722050a030209160e0303130e010b04 65
    0x4403012180f90f8035003040100490700341a13005140010300644044084e1040204000455005a10588141382c041d000e04803ca410310642060445007a46c0000614491081003482d8400c5640d0155005168034a01000100d120780e0007c2203030310031004030b100031030080800c02042c01482d44281e4942d03055400e00640b015540d80c6d40e10058400340c001c00042001c5014046400c64450145400c5001c03604000e0340c0e15090f110b1140c981d9290340040c3c41504814502d49407000100c2c55100600512001051000481c0c2c200815003171006400e05944075500110341030a090640e104405083e54017881c403003200c5000e00021a90600002041359280c00c1000103517032040030b082052420320f00080c111216281c03841403900c4024045650500c0440d0610018100481c007206603601c101814100941c0d44051141400e081d0200a40c0000500c1c0013950400f010020344600c9946480d0484145141e50b0209046a2244c100c5441034281d1040c01c1c04954140300103140100900282586058038151 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 697122302 1106 697121196 697121219
    0xb030a050a05010b0a0e180c031501050a0902030403080c160807260f090d210804030807080c0313050a08040f140a151209080703050c100501 62
    0x41241c4203050580389041242c003c0c5a064030f9a48079007100020b1041d101c7e0354a94184a002c0e08401c1c50342d410001b1103202c0c1d01c80c1c85548019418035061048115068112040250041091000081e4405a4141d0205800384c02648032001c1c40d0030148642e003000c04c00780040d100030035010140100480f102544451158184651070708602c207000c803602425010038100304042c049000541450300054426511986090304c5c00762815011404050402c590342000442440030002010740110f50700c0d40043c454104803504c0d18041404000c0340c0300c001c20b040d0074090303450709990030040c0412062455590100b109910345442d13103580d000380d410354801e101d0360f0f465501101c10380342001e4025a0a0300d00381200400340c5c4403084001e40f50030a0700b402c00001c0399a20010341000c80c0224010b0b08060b0300c030b5580ca5654844445581d071600340364103d225030561400c8010083e00f241c81 = true := by decide +kernel

theorem cover : BRFrame.Cov 696942446 697122302 := by
  have h0 := BRFrame.cov_init 696942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 696942446 ≤ n) (h2 : n < 697122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
