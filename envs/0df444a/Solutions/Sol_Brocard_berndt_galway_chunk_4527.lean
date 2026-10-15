-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4527
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:54:21.110427+00:00
-- url     : https://prove2.me/submissions/b6eb3e06-60af-49fe-8b2c-b41d5cffab8b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 814028776 ≤ n < 814208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 814030026 1250 814028776 814028827
    0x9190f020d020d062f120703020f0d110a090e060d0b18191406070e1c060507090512120d0c050f0406030b011b12110f0a05071706010b 59
    0x4202c4078001302d03445118a2108444000741d0f607881d03c02d8481c1003410f81041c2d10800e55842000d010701c8004d603c81c01c15040d4009450301d801030f80e82c8000c2c0702c5149180900141c40202c103240403c1c031841d0007000c20052201c4035035500c40a0000d65150782220800704212961600006d500160000142c620051030750000b0b034100c0802c0f605040000814540143d40720340d04c0500701c1c050310700800c2c4406440a4401250204043d00b55403810a4016008903101408640544505509011035480d01030580300415400030003845541010308000740070150078010140b1581c09205443d070884800500b40841000382d1031424248070f0440d04002c010100c40c0009420b00008000a000c41d00c4540003c0c00901010f0304e000448522200c0014401c00143e5507801c0f45071480d10310040402e0151303810100382e014074900491400c0c040d0562600303000880d013601e2030a200c0c440c007007010808041061420303542c00c01080c89001c55525440c1c2d5841c0302c20710038500b0381c1360100f0290b040703842c1270800f04e505e0404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 814031276 1250 814030026 814030039
    0x10f0c0201051e030105100905030703120c0807060219022e1103040b0118151e0b030c0d050a14071404180c030c0e01050415030f020c010509190f020d02 67
    0xa15140881501141c101068400f00000014085460300380080345d0b5004042ca411000d60b030804011070350710304d440d000c040e08040800070400d00051003080d0801c4242e90245c00e81e52a00f20501d0080041c3d0800222040f0305058101c0c1d00c1c0e01ca501c0054003c0d001e540341052081d411052000840c801b60b41268080c0486840e02030b03000c0103001440065004d0340c41100f90f850150b15221003d961044800720348a800c030300700540d00022a1490801c4403c1d200c000032034100d04101c5842000c8000c01a901160501401200300300c0c1742d40303250000e003081a075009810700c03180c1d903456125000c0380c122620120b48035001c20042000584941c3c503100c9503803918946d851a051301c038000302c111544007070915a44191600080c4060312342c035004100340809c041c02c02c0030202c3c6502d400601507001d940520407000c007400801140191080c4c002814461440c102156501a00200700b40070b0181250850380f58404d01c03803291140941160b05101c011303044003115400c03060700d6081000c0c0030707201407050740e110b007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 814032526 1250 814031276 814031287
    0x150d090204140910060b030f0702010b310908040b0a0c0f050a02040c020f0d11010b06070b10230603060d1209030309050109140603060307030f03080a0b0609010f0c020105 75
    0x844520402d002c50345000802002481c0400c021440c20307804080c0f04c004e490508404000310085081500d40002502103c070829075200402240189a0a03000035801002c9021052003a09035481160a41503941c0c401000306c03a105030804141c4103450002480c4a90400081041890a901410340c19900740740c40415400a61615a881846a00b00381e420750040d960020440c81c061144542455590020740782c002d50700e01c2600e442d0040407044005000b0740315440c84100d0740a512018a800006000702d44407840760911401c100b508403502c010f880781030f100108601c11404200d003e01d41e22401440d043c2c058801c241f0981d508060502c681240a21010f000002e1311090408a031030b0590b502c84018616505000f0318085050f802541400140f160501401500c110720b014043c5050311056076075100c100c00320746403103042d0b0b00c06040100c14502c10f0342016841080c15008808110051040c1a140703020040c2901c1103603049800324a0308500341c481540500b00f080b0f11103005040440c02d25 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 814033776 1250 814032526 814032529
    0x151107140f10110606011407330608060603030c030f1309020309030c060a0513030311132303030f0702010815030d05040911070203120c01020d020d050405150402150d0902 75
    0x41c1610b0010001042541c0c8071181405420488107900103424a03260301090480114842d05118240010f0540c0c1e8000400740c0b0442c50a01541e048000c07a140000d840350b80040e41d82c0000e001c42e000704e8820340030350008204946000800d96a48a151300080c5d8601960180342c814141d001d1200d902e1150b5001e00d0004895541d40f000d503200b41c1c01031001d1a500d03104400111308002c0300401c8141c16a29040c00d01c03200341014840841c40301e03803604000610b0300403030a109106020b801102071001720320b0000807a40c110400011494141400340700690312110f5020180c0764042c83c01c1b00601400d0510a45c005980b02e01c428079000541e0b00360a0a02004050210f4100000d40b02054049400050100000f03142c03441000c58061180d56201e00f040881c4c1c0c0000d803204020b030b80d42c1082c14000300e400800c900007941100c0310440700480441d0380f000e0001c402800f802e001c5900f0390729405500625100d03040c0c803682207482603500070400c0c802c6d483c1840c00040550850300044654550341c00804006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 814035026 1250 814033776 814033789
    0x30405010b041a0414070917011b0f09170a110d0c061d060403020303030103020402370e01080403022a040612140a120302030a021210151107140f 64
    0x29500f41c07107240c1c60800041c007808107580081084044031840b201c2080031081e07005070326906480c40c02400078003070340e08070141c40d0140c01d503203c82a15500d1611034582105d900300c1c0c00000c1501440d181c0241241c0c4e40c1459030100100000f1013845900881a0200020201000030f000e5600040c0104012509a01d684007410126089240842d100d088078040d402d82545000d8181141140c1840c82c3c542540d006c243c0ba8001131200034041e0350080303034540c940502e0540101801c1003a0000080742001440515041d406801034100031034440300309009194824590540304580540042a11410240c521603420366040c03400ca800b0702e0852903000307070741d070b9140100401440d411558035201e002600780042010040c40d800e1840d40e001c2e80803040040c034940403000042c02d29080050b10b0342d5581c0f0210006c7e2003001d0960030b07500c070b00408200208800100c00760075603040800d003519040303000506441c80c050030211900540c0c0000c404100c43c1c04980350a07081480c020303010902c80daa502c00816036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 814036276 1250 814035026 814035041
    0x90d02011b050709050610020a02090903160c03060b0d03080615091009080c010c050703120c12020f010b0105031e0402030a12021f091101030b0a0b03010602150f0106090b030405010b04 81
    0x6480c3c1110300304004814007800307500d0b000b21007198464079000f88144065510b82d440c0a0003070091a0480004526200500503100039040120a40b098032207140b0705220f4048090000326002840c05d880c21559050000c3c10301036895140d25050015202c0c3e8007088032540d00b2590b10081c4082c10050700740e0f95200c1e140c0740c250100c8039858104e01a42041e486a0500c004c200c24903041103040b800e2807001c03843c0042d4440c2141e400c403814184000c86101704660841c0c40f640c02900b0a03100703189090200340d000603900a4010960000c000e60301c10040116401c0c40705a680048070400041c455188550100740c041c0c002d44000c00300d826041d0721741d0322440f40104181581001d40c124505d00b42d440b5a00088152400c00003a03070070000307200c1e160f44546107100d41804031810160348020030030054a82c5285980584030b01c4200e07035225a036440009548030b80c82ea40e00c002c1d07105420045103180d01e5000d1550306a03000c0e91544280d10381031100c00e1100c1e42000300191160341d02d4411041d595100d80c4100c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 814037526 1250 814036276 814036283
    0x903011d0a1103030307020618072c06010c021f021e0d0f0c05060708041a2409101e0312121a01020c010e01051309020409050c0f090d02011b 62
    0x80d0103101d5042800140d002e00009a000760404c0080084155000c00c0d460343c489540f0f690041500c9410030782c03502d00002604959502444c0280b40c0c00c121118924000b054a150741c01d01c030350b1396a00d2004665004100400075003224849a42c8d10101c4c2042c506407008041c2481120325050100a42a2041100448205094010620802c0c06503400640c910074207a441c207042520941c06d584450380c48030010884030400411030040350422046030000944201d10a00d9a40e2604251003180241e00c5400c0900e044144401c000009605001105a104000c45044418040d01d080c0030499075026910f00d00d2501c015142000c40011450b100e8006101820b40d079011110104005580449240380581d584215613218281408e80c0e00080079a01004203280c202801a204801030703605006103406d4520f201001750000c1160707080c50703020b40200c40c10010144060707114440e0101a504c2001c0d64031100c05010030400c005800c015007604060b61062500c03035240c0140e54030007070043c568a00c044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 814038776 1250 814037526 814037533
    0xc09050907210f020a03060915060504092a0b0c100f020304050a120909110309071e0b09130608060a0e070609050d110405070f02060a050c07080903011d 67
    0x20245120400c2140064400340b4001042000c0005405240d002e910310010031040c2c0080e452030854441c00031980c01540c2c4800d00b030050b2202031415180003e43c9286801703080740340001c00201c615050141050540d0410352181d4019215000203004100114040d83c001145043c0002c180c2c030008010314101c6071003000780400000003040c50003620344d0b01c13842d201100c1c0184107203c08a140032585810070307a48110840982d021442d01601e0760146584640c0e0050b203041c200c1c248100c7c644000b1441070190109585225850306101d0050101403858105000c030803941c180312035074240000700200b0b40d00918640d080407800c1c0d09a41917480780e400c803011507080102849141e0000c0d020b011140348040d0050880781c4c0c14000000d007404200d1003440d102d80c50036000c0c40140b28001000c0c100031117001d44107000d01c3c5001e41018016040c0b400c078040041c422100051003403103042c440c0b1405160300030003140c0703810342540380c3c3e5442d90072550000354035542e0355a0f0061107001e803100d00340c012200c11000c1c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 814040026 1250 814038776 814038781
    0x1d040302010f06050f042d0917030103050d0804080d05040606051f080604020901091203080402090c160f03121e0c0e09060409170a0518041503060b0d0c0905 69
    0xe09552460a0b800c040900f03000081c402641d840c040780304844400c0d1000100d40140403001c2603d15100c00021240020158224200c158107070001c2c200f10f1300800c060126444600740508051000740f00c0645590801c0d00405490381c861141e190304a40900c812a08108410344180c040340c005850403150507075200d004005034146141c42001d010716041c0081c01e8020071800140014400810380d0307101d6940000c5451040e801080c1c6440500309124201d85200c41c4c9240c06040c92105503000d0f4800d100440000b4005c840744811141098042105d400c01c0070035954800070303500441c00c000c405202c0e4002803148016858402c400000d08204c05400d00440410032600481d40700301054403c201045969028030f8880707401094000c0001d0f1000990f500d03840c2403e0003283e640501282c940300c0300245451940f640b003c050700180259481c103100110030001007000f203840c1d41c404945a002001420030104202354081160f21300b02030945c00705c2c80050b40c1d4440050400f078009268481c3e4074006d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 814041276 1250 814040026 814040033
    0x90e090733020d110102120403031805071202090c04060e0d060e0d030c0f030b061c060302120c0307050d12080a0b0d0515010602240408091201090506071b031103041d04 74
    0x14005502d10b086130007145070540a0b005d0f01d0318048000c001070181074a0750b42800100d0060181103030150741000c00c0d114010f40f2a5140f48011410700401c0e441092800007061441d444c040c00c550072900b440d105c0403411954507090100114001c4015201d090369080e000400072022700c0956442101554005509400104082c04000421a07844101841c100085a0b0794844000700c0300000031201d13402d0040c280303011215000c0c08190300300a41050b1000078180c1800c10006100444031400c03016a08425103c40601c203c4880c00342002d05124203864068800074000e101d0030790446450f54011844628400100362069032010f0120340c83d60000c0400c3c800401d490780f41c240500820700c0a0502001c080007103c6281020901c1c0c50508500d45000c0340400451804460303034500c0180400450180040c1c001e4000c00d1045e009a8290251000041c3d4040c4603102c1d20060a41140001082e0306c281d880813120340070740ba2103d2006100c10000402c5085023010201000284581555000c3c0303403516 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 814042526 1250 814041276 814041287
    0xf050402130c02100f0e0102040f0e0a0903080106080402121b130204060e010f3e0106230a080a05010203040312050105010c06050a020702190501090e090733020d 71
    0x5800c404054905802d01555590200d13030208801c84060021038003040140c1114006c00440c1e020700b01a601c0094000340241c0780b45100804c80b01d5183c040d85141d130790000f500d01aa6134003440140012000c0005010031401009055042030010340791705a500c40c2c022107186011042d4500c1d51000800500540c420301c0c10003503544d02c404a400e400e604240c9802d00261a1100b20015a814400c01c1210358214038890102c02c1c000000310500207652aa4804803581c500708401c1c41c510200351400a8240210f105010b001c2c00c071340f500c0d40008c500003082d0070340300382d4880d603130b070305a50302078000140012641c400f040283c1207140038134001a03490030940703406014000000700409440342443e0041140740e8000c2c080f50006030700591702080d9070b603410300c49000a01c00c8940081d8404a0100c403c0c031130010720014501a00d80a072101d11a458031500c0c01261800704543c80a999400000180700d49018080c02035040910001c500b00d10b050200f0341400b41032100181e0340016400302404a03581ca9015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 814043776 1250 814042526 814042549
    0x80115020c090f07120203010605031017070620011e050711211909090501081b060a0e1e0108070804032f0706080a0c0509030d0806130f050402 63
    0x140014205a00518003144040c000240103c034414500c1d0000f6410724003a9000c01d4501c0c6615000319030300d603140c180c003901e190810b6035100240c0554071004581c0e900007140c03d0704d031003a00030010407002d480e040f0102c5800c0744015607a450a003400300754020403002401a44451315030740c0c121b00544043e0380d49000403600c005241d9001c0149a401d9141e0700c000c0840c0c509034103110b4007001e100522000c95814600d01c585e10002000058641e00841140e600c0900402078401c02c000601c200d0341c1c0c0c0c3c0ca41c0e40d80c4004130390b03600107680f02d11101c41c401460018001c068600c0a402c00d00b0100c0120b40020703441e8001c03034a203c0b064a0740741840d84019a446030710103a02908908201c2034030b040c1a10300900c6100010020a41c3c000e41b2030f17020410b000c1c00e041d07040091040314212002d054582500510f80c1200340d85034594103080500c5038010501880c16074003510009801000c000784100000c40d1882009441d598011940e0b050520506229010b010201221a0004100c506140c414407903245040d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 814045026 1250 814043776 814043819
    0x2d0a0e0f040603020a061206050a03050c1806060f160b0c1207020613030f031104091a060703050715020d090b0402090603010908090f130e07060f0e0a0918120801 71
    0x103160b014801682c0b0b107000d11042e5130340b81c600844800c80da401901e00034111781e0041030303010421b18400010014005941030812006440c004488400300081400c0e20600340d4100340d000409103e4003880503a00f03070242401201e035103031880c000c0450340c131030b041101402e8510450300c010000f4a000c010040c01e2255401588604c000c007007030328042d094101e0722300d003681005040094004004407c0d81c42030b0499918030f003980309041c0d40e65646210344001016030143c000404940185043d545107031420179200100e4054440c145001c019590341c2d070488d0b562800e0001550303030a21040000390740d00e12030f041d04244980c414440c142404c1c0104100c2c20070082125210b40c0c10407642d00d0001e41d44400b40d40c0280700c1514011100d0020344002984c1a0700c41c000c01d03150b107241507003219501c1c000080c15421103600d601c079401e90340700b11201141d28084002605812188000040041c000d150b8491001501c003100790285c2000b442d583c51418015424071071001801c0c082c01440550040809020420341 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 814046276 1250 814045026 814045031
    0x60608090f160923070806040e1617160803090a080a0c0504050c0706050c2d040e13060219021009021c0f0f05010c140304082d0a0e0f04 60
    0x2c1211201000d440c81d00448241a40b01d00d101c01c0340b9400d818507403010148407041446070307250010700100541001c44581e031141d410505100c00b2808049085410b0713480c69000740807240d060440e0351880b41880c0484201600c1160090641c2e0b590100501c1d000c0d00b1f503c03000c1c55031280d40308204100781c48540c105d140c0c1034110945160010369a29072403002c9072030584020510f9903920b0800301c00340c01601070107400c081c2000308100d840000d4074000c0c5003440726260894140300541c42d603603030382001001d085450742400b04006d01000c0000c16201e94030042120032041000d4090f901d10050760081c610014080ca840140d603590180c06001d070102238201114100071065613600007910f540301007140351980c10f2400014009101601ca42c0d0800070b0f400c0651200003203007070300e03020b4020155511428006046840c620750070754404800c8a0240d5044400a403c10141144e5200e1251380d201c80c1507541024443c3c02c2c2008010500902149901500d0b8010910b00c9013003030040443c0c0c0c112045102c2d03803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 814047526 1250 814046276 814046293
    0x305060105181f110d03020f0706150b040308030a0c05030907120507050a080312060d110f01020a020a150e0d1e240f1401150f12060608090f 62
    0x740d01409403420300b451610600c01c921a694040303400500703a500d410603000c1c18040c20000164202c9804060010200b089400d8900b071800c049049001d03440d41c0c800f13078010070401180414420381184030552458600b1050072661011801e0b01d943c09030b40111801c007008410051064294030400b1036403815403c0461079490300d109055269400c0f40121111184403030340d0310080c801c0c20000c01c005011b0140082c000652118000c5660341c0254000300041c40040001503081d060145903800f541d6401001c0ba410082000c00300100c0c2c0c0c2c1c50641181c1144624003015001d0ba90b007050000040080e400e10307800a035401440100f084840301c140c0c42c00769140c02c5015001134000e5081440c0e0980814034100c40c0c60091400c0407008109598025900400c420104942c1d03e045c1e02a41d04458110000c20811545000c2d0010148091184541d02c04030200c0305d82c8100c2c0200c4103403001450500c0d14550210902901a0441d8081d402c84130000341c5050070406443c408012040c1182d0856000704801c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 814048776 1250 814047526 814047529
    0x108040803270102040602072405190318080d0c0804321203060a09090c05060f0714070e06010c0c18060503010c020a060b0f0d02060705071a0a0f030506 67
    0x1d2201408940d1807020303040e900b0807000542038062160084003402555680c2d035600c0c000355191224043e12030300003455601102411000040492070711660f031203d90a0400224415114132034400d0329800f8142c940141c1015480901c4401c54070b648254803580d20398540c40c40c01c100710f41e880c64460f02030020210902010981c101c00b28910512050154684044406174000000a00501c060103074494507406056482c0100f01841c401d81c03003510030f085010b5640e00e00c54180c40440c1d902808811590400340010305250b00100882942414540e01d08002a41c070030040140110340059940c01114041c44a81070742100c1542000e803d01c0c05040a5566441d2880342004074032640400c80e40658001d009002175400000007088010001c1012443c00000651200080c1c1c8046640714078010710031405d0b2902044680e08000c020f003ca81c00c15410f07500f400101d5004030300a442d580b0a10f40d00142d1250b602c0b20740111900b5040d42c5540740c05512602800605c0b0030015103042c03604200402009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 814050026 1250 814048776 814048793
    0x20703030509120f1e06240f03010204170c0a05010302122e03061e110f070c030b100918120e150c010605120102030912360f010804 58
    0x40004a82c40000c1d03020580c4034510300b50b04a6900d06881c02043d41e0040e4400c0514980013403d052002600d50b55071f200144000007030030000e03511141c00c1224940e099917051038000c9000d100700c0070b4001440d16488030355900c950102d8801500e02030b800405200d0342d6003000c1000320000c0c05c0a00f015414101041d10f030b4598094010701d50302d5450229a070448107240d000f00c2100d20185e0315024a00d0043e2030341440e40141c0036402c0b040c0150304c00e21811070240040b0384911050080e207101e070319080240c0701d54051082c0d40250310a8903801139245010000c03945582c030181c05940340d040f28101c424581031401054440491911125400c017072281d4006c00c518807520780d55102d0510f09160910088030020b0f410820710f0883e0000c000c0b021030300100502055021206944048840d131342c2d540d0020490601343d20003200c0c015000d070490f9250280302c48007c0042d02202141000302d028003281036450170062400c0d4000d0036080900a0b41101040c2004141200414800c0c0b80c048180d19240e200c42c1c06 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 814051276 1250 814050026 814050037
    0x3150f16030204030615030302011508070b0a0302131e0909020d170d05010f0807050303070c1e1a0301030209180a030e13050405060a06150903030f110a061b0207030305 74
    0x10910380000300100e00c65811200a581d011100f0044601d81d103100300c07600081800110059843c1146100d0b0141b0001903100440c0d07600c900414149051050101440d049170000c2010f040d028050b0b030600240c0d4000b800080c4c11119203541101c00c410b4801d4000c03d44561180e18070034500140d54025884000c080d82105804c16400c0103010075243c0848854401c000482c9070035443d10001245141614103075900b112503210854110030786aa0405442784660b0030001d210407442d035000c01c83c0415555820580480000c40e4988455696101541c46000c00c015400020310000c014011854052403183d00002c082990380201384030021040d688a0590401a00b07000b0107001442c2156145107130401903007814442030025041900c0e003195520803d9070480305140c20120003103000c82c440251180c00d01900d44e50002c0c0d2901d140c4040c3c50851095400100700007045146600d401000c03c030805449220b410001030120145080c1e05211809604080c1150808541000441c0d800b10507501c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 814052526 1250 814051276 814051291
    0x1003050c010807200f060c160b0402060408030a030e01060b090102100f0e071413020c210724060503070b04051c020405091b1507120e130b03150f 64
    0x805038550704800d843c400141d04420041411580c07503045003c00100c0c011184c03c0426040f10b0494464880031410348c000d80e603064041501e41030703c060101c0c000280f11504580050085440c00e0386803101141141c0c09541e6000c00700340c130356035000040d441c240f2a40009044450301a418403c8610000b510380c2c02d49910345400c90744449880071585080c0c3c0c84007800342c0200040300d0780700b5070740c09948600f24900b540b03183c0300d01c05164011240c030580f8000c5541c403004c0c8902615060315008001584024444075000e040101800b406002550711043c600080d29200c03002281d8121a00210301540c1040d00894001e4000da04204200003038075055400782c41c3c04803100c454110100010341c1d40c3d40310700e510281d8000d0611043c4100d2000c08509614a8007070f800e000183d402481041c8613806030b42104030360302c0007c2004034002003880c0c0c100000303402c0000d16058958010780d20003c3c0f013246003009440c01190740c8418100c01464100844800810300343c0d0181414603000411110750b0308010481c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 814053776 1250 814052526 814052537
    0x1b03040813150539010e010b0405130f1b0608090f010c0e0d0807080d02070b09010b0916110601060905010909060807090c1809060e0a0207020d1101091a0309061003050c01 75
    0x150300c00d06184020061060540b041c04c01000e10b0340c81c003805180780e94281c03651030202c60451a003464007403980315400b41c0024071120521640da00c222640e182600b952282d1011840d54070030342c40020180300814440c0c1e10b021322800d100413180c1c2840b040182e01d00b000e03851300550a003a84d400c103140e40407008007268901031130042418911090321507124003c0007802c00040c6954441c02546c003404600340070f01c004410310f55401c0302c90b908980f0a01c400315440b400c1000080c140280c1419183c080030518a0525030400e41c69200a04d010000e0300a04042000e02e0824042c40d40d00a18a00003045281024030006141070000d030740780d651501070f50182c02d0f12105a03a00c44c40c0149403442204449900e0042d14950b00e044500c0206060b00620f02c0b1410072902140300a000c40c02561003464004000340031014081c0c0d100551180031002c0181440300c89480000c40541a00000c00c0b0034044008080c1e0f81e20745140158180382c4001d25100c5140010801130020601c0029120304202c030a0822 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 814055026 1250 814053776 814053817
    0x80a0b0c36060f04060f020304030c140a0801051315021216050c1006180b031f0b0d0b0613150e040809040c050a030c0e15031b030408131505 62
    0x4580c61100360340710258000c9030003d000a07500016900420441d4510303600c801c1c02c81d1100908913164440c520002e000709010083c240000c040c2c84030312074089100140604819503a40703c4039800e584041794041c124114022425040c49410300014008100d140307021403424072054150700b920317840a4030b1040d1120072640740c003500c14090000c032070140900500315180703000c0000042024000c1402850192500c10003102c14541c046d0084c1150b622006000d00310314560700301010440c0003a1010041c1c601d40300c41c488000b43e1a4041000401401840380e5600c3c1e29125060140c80707000710603150003043ca0b02010030710409040c505e0105032030200668a6550300d9504000405011315000301d68840c4c54007030115100707070b000b400810003150944c03028481500f4150094462030a83c424031508200d40700030706d0004448100045511002000a070b090110241a004650707400c200d070100c2c3d150000003541c00d41c01540400c4a402469441500071500c5112a002011400759040b0141801460202c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 814056276 1250 814055026 814055107
    0x21e0c0316050f03030108071d01060504290d09021203090a051c0615170607050307031d0d050304020310050c07030e01170c0d0b010c020f0f060f04080a0b0c 69
    0x8000400383c500450391296118480d0039200c0e0003038810312003906014440c021304000b4859900c0e0403a112616118182440c100380300503c030032084000c1c012140101c841e010b0402581d0050035001e03816400c005003541d011b00c14009203c0403402c050303a0320750060041d006682e0f03c0341000e0090f500151112003040c484462103174401116403200500c40382c00e0180101c0d5208440c10f10780f081328580c944000c2c0768002c0203e4181c03680426111300300095400c10009068500a0b000307100980c0c0d0407008052000308800d1828202480c0c42000380002d4400420300c0250310342007041411030700c032000003003286040c001202e003241c0c440d46000400b84040043c062829a0246c20301c80c0c4500b18150f40b420061a000d1030350b8510758031105031703410402d00e0000c00083c1035228080000841c2d41c0a84441d0300c80c0280e07410059054446100b843d44210100038806440e001c5001800040201c3ea0045c03400f03020500d031440c0d02080007040a54010402c2c000c0403d10402c2c01401c042105100c80d6250858a803003a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 814057526 1250 814056276 814056283
    0xa050d02160e151f23090a030311210414010207120f021804050c09070e0109180204051302090405070302120612100e0303150a0b03190207020d06021e0c031605 70
    0x2c241001340c80c0d140d14008a60b0080c5083c40c482d5110034040e81901d9829450703011a000c0d641d101034014985900c2400028000c0c107401c02d601d42d03a04101c034802c2100410800c6020030031140d00001580200d81084040e440c80e4840d035074460240094200142010405034500703002000c06060010f00c6d070850021f5465510020003020b94445401c01c00d880c0c941003044d500c141c21001c05000701440000219401d01c9a4078140d20010140e48240d405441c110708001c100305e404490300f001545c02c1000284950751492001c6680c11400b00158650102404000031148020142c0d010700d401007080b2141d00703d454070a164003080c111420b031325180010440307a2070100e1442056294a00e40400c0981c00b40002019600c100b0140d1503103d400e420031000d008518061b803144001480061000c0740f01803c82441007004c0340410800142818110b40000700b8444c5082c1d016200185e0000304c14803660740d0040703481e0035408030012842c581501300140698904c0360034984420540c000141004200061 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 814058776 1250 814057526 814057549
    0x607050d12091707140d050426010c0c050106081c03150f0f05030708150c0a0c02030313081005061e04020904090b2211010815030a050d02160e15 64
    0x140300c040300079503803c5401e1116441010141d038041100e992807041000009240c401401c07082d99000d040510b411101156401d0040884016000c0c01401c03141100c1d00b4464001c4c4041c5903680d5400c0c41985040580c00c4a03404d0300402060b420000c00181d42e4800d074080d00c051455030b8980002c2d5100310200c0c2c0c101d0b65006412400d500b4102d0040080c12020102000040d04c40803019981c6590391080d615640700c240c980b600014054541c002000742001c000a8003446241342040d4502d07030764035400241154003c0724072000d407032204142401480030801c2180c1c902d100e030b8801000281071a4000900b038400b42d481451048a000f58064135540300c50f015294903600190060042c000141b8040600520845003050440c64905801d0064441200381140d1a9004004103820910308401125280703030003401110441d80200c683c20079614100865002c60303000d80040c0c004200905002424111f203d91010324000c0403200c00e120000307018001d9500003052078600410407174400c000c102c910800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 814060026 1250 814058776 814058783
    0x41a01050a0611012c101b050304170301031506061704020907031d0d18180f0902061606152403180803070305060111031204020631050607050d1209 65
    0xd25010440c03a03042c00051500c1c0304128001d41d090b2054046d8030b03204036a0501d40c8911400014030b810441340340200000c42e0000e0080c816043d41030700038980c0402c154020b0707100f2144120f034a440710780c603c083c501c0b030507001e407815280210031050070043c100120000544041d1146024001060085009503c00c20741e980045650f480303c0c92601e4512600c07441c03880d0b541d4003c24072240841c444412140800c40544400c10179500f1000c6441c190100202002d04026400658421000000d80c0c0c50300060b250300e40c6c1c80108600c115070f46180680030355500410002c1004182d0109004082d0250741f11500308003c009030250414500c030044014000d802d030002391090480c0c40d00360038001201d0003144642c00ea03403014403580c0c48030380045941d141d0010b81c5041a030024054a40480ca40200307980e04180020030b9181011410300d5007100d076440d00320003040e0300011100c601c003040c961112070780c000f001d049450508011460310b800e07803508501c161038030400904600101200350300d0360204104581 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 814061276 1250 814060026 814060061
    0x12020903070b040504060621110d020304061e270606030c03030903060b061c0c0207031707020f0306070f08040c0306050f09060a0603120f050408010e06041a01050a061101 75
    0x90742c00d036000786079201e4010903010b02d04010002c206240604032545001c0380d00d0700040e0a81c00c245510b030004150141420130b48238001c004002c040c00b07050009c0e40c000c42c010680041c104594034544691402e0490760250014245032445084c080d14005683c500780409001910f18801d526004009104c103400c02030010035020408400d2550017000201980c0c800c2c0c00030854103a0a6081000b940544007102c0c400852104d1940051211504800354a0340700b80116051729803a81e4070035941d19090120036013010700c081030a00551a00030aa2001d0407419006042c10b030404450042903440c440310030000f0720114101003410000b0082c240c1d801150405010030a505107480144030004040d110160107214040215181c2e00b0144039007001c84c0c0e440100000b40f03a0018105071000b400503141003042c03200500c800600b000b001e000b8629041d014801410040c605860036440c008100c2080543c0328110308018405500d41e01440070544d0018241420602608040c103800b404400c5400c203407519 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 814062526 1250 814061276 814061279
    0xf0102041e080a050a0303020a03020903010c0315050d020904020409030c05010f0b150c15060103091403070303050117101d1902120a03050d0207031404030b040201081003030e011202090307 83
    0x65411101aa100385900303800503140d07074500e4480e64511001c50084c1c003e4000d829641c00080c0a0390080214407180d090160500d0642800207084074112115880802d480e140000240600204240003078a0200e488048001c007036000726402c0c11009000034000d42e502ca180c041494020f80c0007000142d445002071003c188692840005021032880725809011100240e610740140354040d40c0b90841d1110040402c01381c803401c00d94019a01400190505135500a168046034541d042030b10110300c8540216540d503d1444c00508443d01688012107401c5481c1011031800300105100d41c0c01c000201010170209219109085c01810b00c81201016100b10f4031542240354a010440c010700d8005c40324800c900f1020600191125040400200019001c002c080d0324030368664051700c0c1d81802403410b56804180f41402c00250f41c002c0e00181d13000940c007400c0200b103680c03002d0001e0303120080b011840095031031079a0260804500b00c0489060141c0764010780b000141c50750545d01701c414000d08590605 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 814063776 1250 814062526 814062539
    0xa02040f181406010f0e191b030203011d0c0406050a0201061716090b0604050925081501180b0d15062f070501110f0d080114010c0203031b0f010204 65
    0x201800202c011090203440f0000944a0105460004a034607244001c081c0750741c0d45206082d60300780300c41c01c20f100d0b940d03a0b2450300c10008402c8200031005015200180c0d40c5d41808038039072460501c0700201c25814241e60401051407c90029902120300900340a6200d41c500c9000344d015203019080340b5000c2401d60300d0a191204005414400803c100d42d100740580d0b11034402c0c4080e00c06041c15150032030810002044a8148900400d40c00149051000b2281254051811a5000d03030b10601001904840a000c119642411140a5601c00f407c04d0740407680c00f0000681c1c8600e00340716440710040c0100703284095040301d41010b668103900480820b0f56507210380703010b442c1503407840c60484038540844820f10700c0c107a00552a02d05040300001481124941001141d05050034158205103008486001c58042300c100160070102e07119031500c680c50340c10f01528500803d8451021410804418500e0016803800300c00c40350760040c41940458490520030740340b40707090115420502658070015000450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 814065026 1250 814063776 814063793
    0xa030c05101503030f030b1f03060b0c0304050909030304150515030d0302210c03060d081b06070f0f0f05030c0c07030606030204050f0705120604290108180a02040f18 73
    0x5803446515007802d4142c914a01b28106c50980320500d400240702e1242400806480b42c035404a5809450041131064449048003200d4100c41d01081d02e0f40e0010905216031304d0070040545d800b040c028007c501754038140d00d030100f84003d54038000c05110350307541c0880d800c0c540c03083d195215a240541111002e0b001ca44005000b5840340b5016002ca1407050b1400410b550003d00785800b60014110301c81c156241c8008216081a0f0440c003100d00e22800c201c00e041038403464030002d10140759400a0105403a103420007500e0f81d072016402e10100a00d410801d6180c1e42c010748042c0304450710b450099100d80e255034180c01c840c070805140c81c01c5032007000000002c125150b0001400c1e03900c0ac1e102030003151140c01002c840404140c4400011031000d109104200c8846051554002c40003040400c0200b03030300304ad00c50000c440c400c2074070301c040d01801d5039241560040f02064210b00600800c400003404914410b44401220100905c81c0d038840d802884250301d0f640200740003040040a03072904000511300481ea = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 814066276 1250 814065026 814065029
    0xd030f110f10050703060f09050f07030e1905030c390a0e0604021606021e130e060d060615020d080106080f040c080d030b010806120a030c051015 64
    0x40c9000c44010045100454010000380360300c0e00034034810b00a2180d200250200500e11810144d03034801c001460f107017900d64000241005040018942031145801118481c004c00c03190506080c00c480812030500020744070f4140a900d10030009800503454018154885c0c0c8076040d05038410400000d00c0b03c01d01c1461004003c4500d19082101c64800035104440088614119130140c01070f40100b1061010180641d4050801800146029841c20020150030340b025000e030344482c0d0215483ea002c0c0d12600c2585000400e80701d8a60403d101c0311a00483c07005039003e20840010010040703107460322400c3e8800c840315031200c010701400c1e80300c1201c40901410000402c0040c4a1290340030001c600034565581a02d105590b0005542d4503600c4003e008d83c80030f031045841c5541c0700c600145491041c801090803c2c0f290b0b4022135001c5020b0001084c0ea17001a00251040780d00c0b00305d00c042c41800040c2d50324441d6150602c080da00c0d81c1e60070f206040c241402000c03c04141031100c84644403208044040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 814067526 1250 814066276 814066307
    0x224040609080c030715030e101b0c020609040b0301110a171305071203050d060608010f0e100510121e06060203030921040f0b210925050d03 62
    0xa81c282e510034515964084000e01e01c1d4040d044100140015244940c00003070901040c2004105003c610161a1a10088210940c1c0032030344c030680c40c50030070801d902004006105180c480400300e225000a00c051160161480c49686d440041081d103403401c0d00701c4940be03003900e070f02c840d100c180c104400b90083e4191540300d02400100000100302c002986400f2500d9a0004002c1c1480341c1021900500600c00101c02d90074000d05002c01480c040203400740030003522440e0b030707100c00c1c651400c00320000c4644c140c0c00030074801c100c2d0750421240403c041000012140e00720380010202c262664151010041d0418500c4c6507800e044042c040507030846242c088018512004119065440342c0891f1203020070b503500c00c0c858000d412034460400c101070603250401880d5281c00e1420f0740e01c2d4000020f0034102d501010f800100420902000c2000b00c4224400307428410040c1e00f545402d060301a103407440c1c502100c8188007003201200c0060f00ca80e074180e0142c0400742c10102c5100d010706024001008014060 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 814068776 1250 814067526 814067537
    0x30302070e0408040e040206190e0307060903080d0507050405061206101d09181b0f0904020139030c1202010c05090105180d08191409090402240406 65
    0x5144010740ca0030521507504000d02130300346420134040402113980070b0816688144240405a218082001084c441c042c86446440003180107509140c20059143e1002d400d2251805081010542d032008407207000c0460f20001034955a144000e0344d02d401590406a007000700455400d0480890301c0c071507030003080c04880580303000d01541c0040b0b507421a0f114001a0b0f5040d981c02e020300324108880810b0300811a44a40c0da47c80c015992407616001407204c510000c0010183c0c0c0c544542001c80000404810075101007442d0314064002a0680c0044080a00c280c400c885645040f0020714102681d4808a146081900c085508004102035010f44042e1400c0d082e40d8450184140140f05000c2250500d4031001d00b0006050015582d941003c42e402401c10b50b000000c0540f66912016651003510945a49413594034044a01125420b0743ca5040705200601e5001144851000152442c1c0d190440d00203d0594403480030401e00c21002c1e0700b20b0411080b107500d4800c8510520054400d64840c0d80c0d50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 814070026 1250 814068776 814068779
    0x302070305160b040504090f051903080a27060e01090b0f06091b180916140301050105030414100504151514010c031b0507140f1813080309010603030207 67
    0x2e46070498240c441d600001c1c3c3d08000811035410240c10058600b40030303000b11004452151951418815082020f001e0030140024200406812205580c0c010700200010003680110241c40c0c2c41c0c5d4140c22074282a42043c9900d1141045a241c00480b21405440000d220f440300c64504106205c82c00c0c1e5240008100460001e06c040c00c104042c070703106106101d41071008150030f041c82d441550240e08404109a1704e0b241c038840b940c9440e10f445004980080f00d00c88200320054004280a003000000d03c100e5100b08010000c0342c0e440429070350007030740041010280c11a03c0e0151843c284480820019650a04003000244400c030041c904400d82801c10600860f5800e18840052844c54061462001c0481e1466034043d442070340320031800c0e88282420216075203215804d9041000314202120039a010704c1d42441441406007100104503805c1c1c40203036842d0315400c001407030805807420040941303a8040004800f551203005c0d000c1b4181c3c1044003ea501e0500c0555079029040c1404150050703c0344100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 814071276 1250 814070026 814070053
    0x181c020d0e011d06090a03140f06060d0c03080d09060f05070e030a0209041506050a0e09100c05030f091002041403010e07030b13050c091e010501020c0315060d0501090302070305 78
    0x20303c21241e044020610003180d15090400c0041e401146900b50445044100800003400404004a00d002c40500511508a1203920300f031034482c009100314020540070300f4010001d50b01b0f2450340c042e65807015100307440341400450702d0b00801d0516005023400b0708000b0304085150a43e0b01c094061192350b80c8065180c0e64074402d1660300e191460f802500308101000090202d0b0710260385411490a8002c003084240d82d607400114410341d5900180c00c4c0400c0d45050145614003041000d01c86100c21000f031120050030701000d0003902008000d01c9845c4e03e07501c00507030f01320703002d002c022205040d4090454841e0b407200603000a2072500e44c41d85001e03600c1c1654440220400260510031207074130020106940c2c1d00c103c102004181e8001c1c0451f25031040c111400b09580c0e80c010410311400107600e15917600300310410b22100d4907a0680c007041c15904244071100b25900e003c03900c4004d81da004178010b030041d2103075004a00801c520060260040d46004901070070950701003010720450b0b011300116011540301d101c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 814072526 1250 814071276 814071287
    0xf0a110d030522080f130905060409230a0209130b0f060d02060c010e06150906010e01021c020a1401020307081b04050f0303090a0b19080c03181c020d0e01 68
    0xd03a403100d000d0000c8a030741c080c00303035110840c03c2551107901144d040c41c0c44280380e0700d0581c104091140050b0300c1c8100600880303039584192035201d00d0885d0288a90101d940380c0d07440e906070b40404003940100f1507810112111082113007a840d0341d03000e80500814a09000307540040000c06104840f00036405021032040000a071484e80a404020000341170010030740d08108903070303000180350030040d500c3e0340c3d001135103c00a020755072041901c8041101d131520340740200031001900a20007410b20044041d060803a9a00040000c149c1503403955400511112200503458142c1d00c5030024581c40701062951808030041d006580944031a0b01d8561041d200c064014000d0b01440b2100c041c441d10a100810540c80c20702300c50402c080d4040c00b0780b031401d1034000204800601a80040d0300d0100000b42c91030384514144020600300b009031600302c5650800b81002d41e220f00c000380c03441042000e51104004402c0303007400003445500c03060b400180f0303482d240107001e5151610000e250001c00d41c0d030150900154081c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 814073776 1250 814072526 814072531
    0x50a0e13051f030203072d06020d0e011d060f0403020303030c1206011b06110408031306090801090c09090201110d1805010e01210b0d05010e01180b0109020c030f0a110d0305 76
    0x103014000c0c0da4200440c090000d87c14035004040d004504007034021214054500c0005000150f0140046440c5c111000d03144211580f0421304010241d07402e242c0d4541582d1644458407000c40320b49540302c0380c0d8901c04100d40510380020b0351600000091001d04d424602c014003a295642019805540c0e0310001500c0030108050081082402080d02000140c90340d0301108400200c44a11400c040d180c90f0b03010b286410030180c0c0c425803201000b051206640005040008059820090090b0203150380e807c1140302d00f901c00c0d0740580751a080c010b81107a000303291407451041984226202d0300500540205094085072090740c81015502c070120b51944107408440310706e081038580707030041c807810180d04221000c032107030f98516590798900500c059500c10000340d88443c002d80010510b01c540384201c0c0d0031a44104000036060300340408610024120000140c1141c40350780300140c640311050b148506501c1170030391407407003000b00041c40c00d085504503081d0750b014000081203a4074000440b81c02e07004c50300b05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 814075026 1250 814073776 814073779
    0x90f060a0213091b0215190b03240a0e010c050703050c0f030d1a03190201140f030103060e010c0c0c26060a021209070501090501050a0e13051f0302 65
    0x19000520603091500100031032002c280c10610308a03038403014041201d80440d070a50480d84140740c120ba42d10350410200c030486400c014200c107035080107003881311282c10303000c41e610f4199120f48012039140d4041c040503410010b2000c1c903034200b00c00a1054039149908580b445259407522008070075545052040d03044101003074640a25144d02a00c05650703a4004003500c9546200780351101c4034240042c8090002d07a24101000b14a105012000010401c10042c2c90b60080c0d110a050045400045054010450302800c0440d044011118090340360301c14014001130b0342b10000000020400381d0b5210035801d032144402001044451401110920078014000e00301940c8030b41c080c042c1c140410850042d09016082e00111180b042c84140c6c2032403821141403040660100c0c81f8140b444000301d503654440c0302500071300134140c14500040d0002081d401114100440450b0300c04e551801607503044c0e00804010000f1382981c0d544400b203400740c282225490340803001d4000316118041030011010030b80b40d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 814076276 1250 814075026 814075033
    0x130801051501110c03121b010539030103050714040c090308030a090f081b06011203030b010909020c0a0c0b160b130f060509070b0307080712060f081005090f 69
    0x410700046844442903112168280a1050550060703501003190300e0a140c40008040e4a42180d0900500340096159114072a64188010040145583c8007035080102e00703502c0d54400004050300c4400070003802024001c00041c0000007005200e0002101c40890321400c51850001e800e604c18030003594180c03803008000c28a0f441c8240001032828001c4c40c0c2c841c2040c03000107002c10325a1542c070711038142380c0000d03500c01c41c0004591002481d155003030107446490348010049035141c007042d1154000080c0002c0c0c02c1580d00c484940480e031242025000038010203406646621480034007985801c08041d040310104407203140090851541c0056615480625201e549215041c0c0c0b00c691001d140180040d001c40c440072002c5000a151203d503030f00d0301740070300070000d5a840c146804510b00119600320a0304254103004102006900016003584600135290100750680201e03401809411107400c4440070152402c00400ca00d5000a00c00001c1c5c1e00072017050082d42c075420319083e01c42c80c0c0812600725940 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 814077526 1250 814076276 814076311
    0x501090b0d0f031806030516020d140322080c070f05030c0103051302040615030b09041101030e0a0209011409010f032d0501060905400f14010213080105 67
    0x40c04981c1c0080c00074000e080c4040040110024401c0c04d114035044000800c1e90342c02030001080682098104407041c41c0010f1002c60600d2202034040641b0400907048100000005051130141e011010f4078081c01c1c42480c2c44200151a0043d11600922041a02449604400100030b4548040c02c8121070004d005080300544040c011006040000c0016449240245040c00103803600e00c00c40c801880e094181c140140000000101960704421405128003168424003021917816682c00c2d0b800b0340709003000548008429451414054800c0019600c800d03410000207840680c00034203030001c8411a80b6031a81d0ba00d84840b400d8000103400050845401e100c0c2001c118100220002e050300d02d0f0310682090382041e5941c041c00e40d2aa0703080300800949030f45c2070101190403c0c1c0d0010015a00d28554070030504124001450983c10340340c4600981c0c040c0c803400061140c6600c01d80011604040c070040f8100ca00340f98a4082e5102d240a9040150381030000145244184501c6000710b208002c92840c89 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 814078776 1250 814077526 814077533
    0x1502040b180904021012240302011701030309090209130c08070e150d240602100501051206060103050a1d0601030c0e0408031303030b130504020a091424150d0501090b0d 74
    0x20843d0809034201554030387d01d800401a121826001c0440440c6002040c64203510004014410001a09010302a0380005000080e000400c141c1a503c5028005803119001000102110100302c040b51280b49002c8040ca1070503448a00c0c24403501041c0c850722402c08100c800d1013459088140da189660302c05000404030202550006d018040d03030003400f0402d989042c44400400c86042d0301c08805a80300704041203484005008003401028212a41c450117004c20724400e0b103800300140441c1c1010780d42d20001d042ca0b9003982c41600c034800c8022b001c0300c0b5020b880d0352156681c0000e000507103245840c0130001841c1c406154025118a5009800c1800d50729503240c4600b10f003000c0f9004400b4961100550705840c0c8039004140c1d081d014400001c1400d0421340103200e021070f001e41001d581c403410004002c8011009640064208245104415400650048035080c1c4c00071080c1103580314115110000b1400424030240501c0c1070b10403010081641d841e683e88040301c00c001030035904043d1213401540031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 814080026 1250 814078776 814078787
    0x82a0705060d0c14130801140103080a080408041a04080f06130b1003080705010f0b0f010c020603060406030206030c0403050606010302040302011706010924170601090b071502040b1809040210 84
    0x441035400d040100185420342d140d815080002079101c945c002c0b00302000048024040c8012030301d41071516a5186d41561148101481241028418843e55001041c200320048084600801e140c00258002409045400846034030901c11030f40705101e074158058801b14080382050040b400c00c290141c0c20500340c0d544041c54503004120202c814041c2c0b1000020500140080000c5c502c100700000d0302594094018040740c00300320b103c80c0a51400000790241d640c1000c4010480c54045605503103d680c0d1100007005420b00c1c1d00000c0d0030200203c00d000e0f0054100d03000e0026a8890819505180d852900441c100d004600c00a0300150082c0c1802c511034180803c9d840e007204043c036204c200c603900c800c3c07441c03454160742600801e058070490a4000300369002c0611110212018a00e01190401310300003486180c1c03d0080030991900011440104607819100003060500000250748a50390b90211403225081951a604521030080318680c41d86000d00403144120350041560140c090300b005d0440e075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 814081276 1250 814080026 814080041
    0x608011701060b030408090306070905031f1d0a022803150212011712040e06060310090c05040609090b010c1202191520030402130603082a0705060d 65
    0x40c15580e5600110f090040780c0000c2d445a4000c41e001980c91101506052401800134041002c10a0b402d4083c0304079600401c0c0600074030007015030019541c904000d1040240451081151800c401000c1208a02c6000ca40310400c14004c40c5e1408846403050072040381e0702c000f41c1000035110b1000c042030000564100c11506480d40e41c400c0182010b0448007401d400d01800c0c0c00c910340b82c104003c80c0701107101c000c03c09483d12941c400c3d0041d06040c03074150320440411011340050f1217418080300052580203020a220b0080440b540148054900500040d003107500c103014060020b18202c001166089442c003d002401d04180c5d03071584249641c0d15401d210b0f1610f00000011401032041040e00203840502d0843c80c0d80c0110a030b62443e8031700d9002d0b90216542c0036045d20112200d900c08104900c048020b80c0d5100360142c82001120301964075100081841e6000203100c0200424826551650220b4404280340c14010340b040f0040d1105409644180310711400703512401c108010300070b00926421014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 814082526 1250 814081276 814081319
    0x1062d0302071e06090b1e0412050c0d05130603110706050c09030717190f15060b0d0e100b130b030319050315010314060105280e030606040204060801 66
    0x10404115861001010043d0800a072482a110540c2400380040081029004011a484501c80d8185402d84444540b0300420140540c280d0361640e6003800d00501c1240e141117501c50a40320460b00907000505190040700311542400d003a80400320b0307070a029124004644449440f0b190900c2525510039010b040e0060131070008840c10b000040e40d070340b0708000300d0018042101501c0342098a0b550f0051a0158422306100c1d503400d03284044000c50418400074101a42242c050301205154a00e044040d1a8591001c00203020010365155039460030380c403002500846d5015500700c000404003950a0300c082c25400755002200e01042441d0703814030350100800d103401409603820a83c050307150808454594080c0d9011038000420060100c4413040002c0c03040400342020481c8c2b1480b055002c0d11600010003140c14072800003600003e821030b000300c0c0c14a000e00c2291401e420081807800501d10048144154006d01caa4004102e0501d403a00a890554801d591001400d070300c1c085e519500c4805959116 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 814083776 1250 814082526 814082543
    0x31c020a030b04150e0c0f1215060d09050f120a05090a0513090b2203030b04180516060518060a0912080913051603050912030f01062d030207 62
    0x46034a65000d0404522501341c07400c1c10071131401182d0201d142c40185010003500080003400032100c0c1c03200a580105503096060011652103460303070655403401454007548542e01160800000c5119001600507034810415511103403d04010746903900520b8000160810003400507801003481078000e0b00b4456030003002e050403195110b004c00c07181c00380f0440c40c0400503150300f554403e001009011540241300e1900410904454003d0181441c1042000a003010f4543c1c2c41c0d10340303d40c0d039500310420183c100118505695114944159191160240815418102c100015200703000b901500c21121060410600341440300080000550000400000340502c1d0301000c107510300b160721031120751803140f40510750700d91926003008410b04003003194402d01d034144000c10640c0e40c40c14100c1a021045400c010480f9124041040e0900500101d45200c056010040103030a603a8409050f0480f03d0a0315851204040c2030000c414020030123100450040e41001c3d82d6405038402e5000b0b00b01d060091000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 814085026 1250 814083776 814083791
    0x813120c140c150403170304210e1e090105101707050a120b030a1704090905010b0a0608040b240411130f2304020403080309061503031c020a03 63
    0x8034440032405031070000099215144060b40c9040a5841d58910882100e1075400c05145070b403114840c50003803102010050010010a00f040103140702411240320510005205820310a4003c1001441d15200752003016030000e0b0108030394034099807120500700689494001d03800c5c0320a110045035180c10705010010319040c400208010140c0c818040c440710340d202030b55158501c0000382498082c55004c0352041c540103400605e03030b50009541442c980d000d410240c400d55600303280d801e2805103600031030b100303400c156015081100640c403c009440d0119542c841c8552501d0f8106c400450899005100c8201180415802803014a0030b244042050101400c03500301d2030042400d5034500203180c0446a40400c0348806100c4c0300300351102500420701508070781890520307101040c54100c060256034030b00d13002003103081f40c40e150101c030051504205004d40e03a06000f41c4245d0340d250b08a0710304c10003a034000b0b0310030410719001c03048528030040640001506100c3c51585e400940c4000720141c203060380e6058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 814086276 1250 814085026 814085033
    0x60603060609060705151e010605031501030f0b0907090e0f01030218040c05040603080d0f111b0304051c2105030a050604090b0a0e070b040b0a030e100906060302010f0813120c 77
    0x11b130b81c400c42d014941c01400b00c1030b135420003004040603005402405030900410217000b9031121800304645003460b000c40d210300e901ca0b800004003007145003e90000c0c0890104019550840d4040e0221480107c2003d01540c54905a0800740000c0c00001e43c000000c3e000350744801182a07046030401d026151021800b96a400010109c42c0c250340b04a0b08040d011481103030503e0300740b203401c4844a030f14005110000358907040480038404d2180002c400743c003076107442c120340304100b05072005060051300d899200103081261040071024a20b045407000b404030317414400c2d100d0100310701c5013548040d140c3e1401e503102e8011810103400010080c5030020340d541c11f05e10219800625190150100c24800900b1260540c0c0303890414a198000b0b103001c1004100800140a44504031120f180c81d40c9800070b0a0050154081d0038907142503020000c041c01d02c00520b06000641e8010812a4803d0325103c5000c1c0c07600c002542c0003e8100c95480b6201d003420905c4d00880c3c0d181103412072011851404a0540b140355a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 814087526 1250 814086276 814086313
    0x30a0f0303091a10150e090103082b061a040e0105042003151903050304180612140606100c060b0109080d120e06061311040504020403031205060603060609060705 71
    0x888008180c144d1103020000411030540000f420002441d1a1b018040c0d20008141031041c11f21000303080e6000010700811480d02044da10f0708c038640d59540b07102010b001420000150401c0e000b10b081a540301781f40e402824404200b110101c408203035000200380c4c42c1004000c014070b00c0711140c5050800c0154035aa900064000561003072103c407501d80041c1102409004100041c4c44820481480d010300510110b0400001d071002c84039818218048c14001401490240000782d106130060b0803c40c01c41c1c4200a80307400010a5880c5803012120f2a41e9500b0410030b90801d68460f142c0807a2180711100b001c2001600046c6204006060800409654404040c5420211f8005400240b2a400d005071150b82500454032410500740062100c1d06140d0000f031401220f00902a109590350700c00c00d00311501900a94004010041086490f1b550301d06002e48095a0071030008070b000d2502000030300928141c026a03002d228094039086c100581c41c0240b0000d0b44c015007003600c5600c200f00400003000d034a030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 814088776 1250 814087526 814087531
    0x10513060627030b1f0e09030f0306040e0d020a060c0305060d0204021315050c07090501060e0607170d2301080714041431030221120f070e030a0f0303091a 68
    0xb104210590301e21005c0c04828640360b50483d030141061241484a019030000c103482076140c0080540c2e82c0c030303120301c00054020a01018008454010b0441051400e07401080c0c1d42d1580d40a00c2042c0040d0210341021001caa1f0215485940000354856071400b6040039070191940c6c83c12041e00c55405901d50a804842401205040b8000340000404400f4490140310541c020a9200001d015650418201074030200c000d41c907513401454041551400d03c0304030944d800c0301c045400d09403541c50b103006880101520000100080c1d960249006201071540b1441c1e441c12240301c13101a00c0d24030308200c901d200c107000d000003895001d511001820007018500061034003400407456003d20f60703410114141110b41c41c00d203070341907040e4147e42e015010036008a190312810366568200e5154402d01c6241c0200341c0210a00407542c0b1074281c0030081820582441d140c055029a11030000e40040c1d07908040d61490480401007104580031b2607007002a010b9005131484510642178a0b86240410341c511095040c02c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 814090026 1250 814088776 814088791
    0x6010b090102120702101110060815130b06042c0309011106010609120c0810060e01120812060307051002070306110301030b15030c0402040e010513060627030b 70
    0xc0c0028056804105450070321140200950504020790000b83c00629098000420300a1102c9072a50050060000d02d40c80d54640404101070740c0c0315040d9503031302c0c0c2000c114003942c005030801003990442d4448070000406d0b0320401c074282c01c4d1f0f10303d82884003800400e102c070404c0503000c220b41503a03002c0d01440004001a080010740c2c882e07103008001042e203000f010386606590440801401556803140d684001c2e07401080b41502071144a10f80419007a0540e44101d03041d000f01c0301d4504110303a032500541b0071110780004605441e629041e0183c0464100c0700c00034187c40c4100035a2040810300258594054401800e4a0003d650340000c190b0442c01d0001490050f0000d000a00c1049414800e203040203200c401c0c00c9086604595030366942d001e02400000712100d0840b104142c2d40c2d4100044101441c019100359200c581e6490518510802800ba0900c2400003403040403041d017061180c2d404440c4c1c6a920800300d03413582248158820713110b149202c540300417050040045001c8102c514040d200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 814091276 1250 814090026 814090049
    0x140a0b06150f0d0c02030720130b0d0f0c170d021b0a030f331d15090304090c0e03011b0203031f05090a05040311030a090e04020d050601 60
    0x102101003026000300306908205492050041c030100900b80c805a480014400400241c2501d5003182a0720398040c87c1c0d0000c00c1081c02082c011200500040c0042c0c002c0c8003070b2600c00c0684014911201620201e2031516000b002e41100f10000c40d0a2001642039203029503180b5600329112940ca64407500305454a1190340c0c4960142c1c1041135042100ca510569040320351505001d403c00080d0b1480601e01c0091700103050b2042800500200c94080e190481c2c0138400151403d107211128850602e0b030000741c4a0a43c0b405142ea405100040c022003107910707148014101f0090310488403044424080c002500c1444140300104000519200712482150b40742c6402c0e035808011010542582c1594401180300036000c030719044171540000549070009889000711440c110b4610741e07800d40003200c0e444a540940e0102c144528400581e20240c0264003d68070b2903560303268860319581d00e0ac00c2c0c548e5403000a00c4000b01300456a8009845504688020401420702c029611050301c8c0c5502078020b03d10400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 814092526 1250 814091276 814091281
    0x609251a0909090a030806271f081b0d050a0506090309090c0918070509060403060f180503070b060d02090a05160f080c070602160803060a170309010c140a0b 69
    0x350010b4480d0340080742d04000c0c0510035260b54001e010340006400346000704202c1c1440d10021000018601040d40450654405444c0400b00115018811101039900a42c420008580d446000c20281c00c2c007201c00c918a0015140c2d181406800740e8800b0080d20036010300c50b14500080c1c1306000d458005c2e542e080055854203545404c00c00c3c1c62801412158140f00200300b52580c03600c86500113140003105078164803a80d600d5030810760f00c0707111300c3e08141d5202e5000100031040004da85d10407180302007201c40c100140054101072854200035414083d05039030061081e08001807050301241d43c80240508400c0d00002290301007110110284d48400c03101f81c840f0100110044642400c11180016107080d490181281c84090450341000c2c0c40e0302020b100010341101441030540440d607850301030320030301e030052007490409020541041d520039101d10b081c035600140300541d40b280e441c0e045141e40c0107035180c103644000540e000701120000b169520b25080103800b80100610030080900d00841d0300b940f00d031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 814093776 1250 814092526 814092529
    0x1e0503180301110702090a05060a050d15050109050103020114070201030212040b06010f021603061802060a0918060501050d09031101360b01060f0504031707030f020609251a09 77
    0x165040341404040007410b101350b00160f0fa0b49a142c81d0044008403000405413201000f19802c040340e600b1164000b00c000070103008000581d081220816a0400104103d07625005d003e0300340c1d882840701a0006400c03040301c0466080c0324001b450400d10505005240c00c041911030035090b84100e030300707039018140ca1080000558006040e0410300029102600d040c40749003451156684481c04042d00742079840c6400d180d032080700360300e0701003003900141501e484075001c2e8002002103400b40108042e00801c2d45141a020949028480994070140c507654109a80083c0030702c010810b4000a5003044000103920419a0f004c0c4100e208803c2020340c0503c1440c0001207084100b400b2102c00403040c654116480c0101c0d00403000503040d29414a000181c078042540202c42a0203941c101521580710340c07100b8501c03001300e5001817640a00c00e4880d0000c4000400e8140c0e2100c04c01c440b030200b150001d090b244014861034031001c00542001c190074400c140c4840020301481a0120a0350300c03024001680c0d80903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 814095026 1250 814093776 814093781
    0x8010e0c01082d100f06120e0a030503010b0a0504090e06060a060905100f0302070f0c050f01090308030103032f1b12060105130f0509071406030c070305030402010c050105100501090b0f03041e0503180301 89
    0x8e07140c0d80d00003410340d030764940d500429910051140000361000451241859072048040310002c000f104000e01c880400180710b41d40f0340340192000c52088410500000c0e51070f0207250203d0449030010103801c2c41400d00c420035035411200340305200806a08100460006180c0709102070701c42d0082c100d0103000c600b01001d000592940b07640240c14030544850420002d1200c0703040b03d06499040c580100c50504801c4900c00318803610340101811040c3c5035000b071592000144000e40e90728001580070703c04e4020000d108113400076107110725040d0440c10041c0880d09081c400d00c20307425a0361000007034494803280300ba000c43c0d03415181d016140d00001010405044c016101c00740e42c4000b1a0000d1031410401d40c0ea6144d440f81c0007000b0184500131000405682c0075094035852690440d0080c011460000d0040b95507084502445008c40c80c100b0300440d0754203142c03054540074012a90307490718607101e40e11032080c030380410304081c443d01c4021500140024020f0010b40341c06485030400b41e071885041c2c401c050a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 814096276 1250 814095026 814095041
    0x3030c260f060102390d0b06030705041b030e1e0c091e070c11101106180a021309081209070617010b1308010e0c01082d100f0612 57
    0x1150700c401c0c08104001c44255a4072015442d104840d5086510151000b03800c1554455442e030000786c40e00d0a4040c840140812481180c0407410f80305815222002c00048074070800821620407000202c1c1c0c55954040c1d8011000006031400b26801d500c0c0d0207060300c081d10352400040510b0781081c3c40583c80b504000c000150411003002241c070440400345113011303140800922401c20400500803090030310281980104c5810005000345d03030254007000019211004050201c18244100e40c00944107100450340307503901ea015070b409040301800795000c0258004001d210046581d40c0d0365108070020300303031200030407900308146e800c120145410383d0202d04104090b4000001d100c103c0203080415806d0b051340d541503c00144c07829480d1a5000b5608640c020135400c01c88807036103405600c0c3d100450018aa4031121400d82c2c4071495a030b01d80e03444d0303000c1c144044607215001c0c6410070503030302c00c41010f095550b011000c11403010f6a1542d503a0900c200c808168881c42c003050a0300b8481c150744500b0b005052 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 814097526 1250 814096276 814096279
    0x30b0c121b0f0a03180f03121e0e0f010c0c0b180d140d1e06120f1e0506040804030b010b09090403051c0212100e070c03030c260f06 58
    0x4144080c444404a05200384070344080d00500c0083c021000d10301070790006604c0ca2424243d100841514034007030326404410075081d00030480b001413802c4001218041c0804034100751100360b00c051134495911010301302c1c00e030102a10b030180d21661109072000f449510035511255455001c9070704181008080303008054803d442180c101301450500c0000001c174106a102949402aa8041d4840000c003d5015614000040e5800c0164051411f48508080c441c0c418211004100c5240c1c3c660020460800c030745001024102c0703490155021446018141d800d5565501d9132140380903155440707500b4450304a40c1211000d0010806000744a010070750030380544103102c50b6510b03190070b500005540040081004040100010301020b0851101510076144002c9500542d19103584030382034002110226001d01040c0ca414600007519420805558001c00050710359032650401c0751400c40c040c00704041c1d00818882c2c11030742c16840444001c1400b0340c88001070703031078030312800d1810240b0300410b006821385 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 814098776 1250 814097526 814097551
    0x100e060a0e0d08161b0b010f050604050321070b09030d0b040204050d021026010510050703050d23010b0c010e060c0a031a031c08060a0e060f030106030b0c12 69
    0x751841034105118540041500c02000d0f080440244203c82d440600b042d2802040c00c034a08800401440306c00c8141614402e00500c3c490513112000d1003a28020751081d03543c103500035690f091160201c82540703a14070750b11129251800144e03443d020b12500c81070fa00c50025600006601c24084041c0c483c402001500f1a02546004d1030000014030811403190003078440c003012000301ca0070714024401c0200050084a0303819002d054151101d03200ca00900c14203000d440010031204140b4071076070031550b40d241e040d2281814000790f0b2000344001c08404884008420000b00f80f5802c072507006103158003c007000301d800380e50307451211101c900b0340b1400c45100403647d01030001d109080030840240e8100e62621b2400040107a960003e40402a42001d066600350190030b1401a0800b803101e486000f0900325162480c098a5150a11101606034400d040003484002c0c0440c07514940200d000000423002000800d0342030310f80d00d5055401000b6206118840c4c8000398030900310071641541a802209480c24 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 814100026 1250 814098776 814098793
    0x3120f070302040b04090b1206070309020f0a06050f0f071a010303180506220f08070807080708120c0a05060f0115051206300d0908010e070b0a02100e060a0e 69
    0x7859418082c5000d0446c1a50301c80c00c6c5018913448102016200e1800c4200b00d95203820051000750007054000d009900441881ea00d22060341003a0884008449a0355a000d103005040c5400b8083c03504000328140070031404000340d101191440c0d07401c06900b0004980405554075616025103103542d541c00d403e40c003060352041040a9902c000c151016480c1c140c224010101c42244070030741b900296008050440805030300828452400140c0805841c100c034110782c0519215808a6565400c9118850403a44040f001c130110613a81405040445031b480700329a00d0500b6030b524141130640480700c55442210440040255261140000d0304219160030b2441c90303c01812504518203400500e95402090149407100300c640486511200c440303020000440345403851000c2c20784808118a00c0c030000f501088020949020600c01c4c4206207012a0007407902500c1e1501ea003030503806c0780c0302c4941540140c001541e46001d85005940d94170300100e02600c2c1b146004d98502c411210210004403155104c0c404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 814101276 1250 814100026 814100039
    0x114070503033102040213080304030602090f0628200a0c15050403060e0c1003020c06060a1409090c030106060504031a07170c0912151b072303120f07030204 69
    0x803004086805450247e550500e0b480740e900d401c110303544207214038400001c0001c02d0185550107001c501500711903c28586010380200400d41c000c4003802c0110b40c40c60112082001403c00659082002c1c07800c1414200010b1401d0311000d91440900e1300c040d400800c105020080380f051800c001e03140b03549200b1a01002c04200900d03901450000900d410703691100c104c03001c00c04200c2580d040c00d000300364566061002e00b00070044c0d0000305a0340035a100306008500b5503d0209401015074100c21403007104014100200000240041c3c01000c00c1d000b0b591052400f5107080c05040c0c0940015107441c1e03662851840c01d480c0200340e18501000c0c10007030601b40b06080b540a43c1d1402002000c8080c00110303282c0c065618040d200c1ca000710781e8445200c119490501901280da02d024040d4900b070039907a1b039100003441200035101c3d00e0b1070007082c600b004827000003074154902030088030030405290b5058800c135075a6031450b032003000302c500440005810405810140103441e58013030140e240a5061602e07044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 814102526 1250 814101276 814101361
    0x6030f0715051c02030702030a033c150807080f0114190204050d15053403060e01120b0709050312070213110c0d0302130303030b011407050303 63
    0x250104200b210000c0ca241c08007000030070b240d0403ca1980d804565a003401603000e503a03a4403245060011908203000c107a062621441510240981c5046207180c840c1e14171064130210362102d4a0701c06d040da59111003100b50361b5103003105014108501c01005130ba800d001084d4a0904032250b05103143e0f04000c0d49800103408610840c0d001401c3d081c03207440d22001c0c0712205000e030003a5004290841d00a1004105102d1a81001404e003101c1d6030040100f500c8000e503080c1c0e94032440c10064100b603d40d032031158001580403112014083c0a2500103191a110f44481d4900e580a034020450030800a40070014040e0b5540b596401c0682d40c100080124035003404030381c44407000b900c5480007403000714202c4155201d0303c0300403005030142601000211200200480305800100c1302070003a00c031307007614990803d02034800ca9088031000b00c00aa0341c3c6140d550224060f00080b500d440c100000d030900113459188800c0542660740c801c2001e103851b80307080454100c0b4514449800700081200503130075498001c855 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 814103776 1250 814102526 814102559
    0x11090a0e040c08101505030a03020d081306050a0506040b100e040207060f18120f0903060e0f030a020c031c0503191104090608060106080f0a020c1002040e06030f07 72
    0x104501440c40e030700c60030299541d660b42c0d400b40d41a402074584000c40400340f07070303c04801e404d038011a0020554942c01459500d90740508010701590151103420505070007404900d44c00a07803401f08400b03c0f40503689020980d107090301d1510100d5100d800380203403454680a4144240010394044080c003c0c0510003c0418040c110314901a0307a00245a0040c0a0141c00c40180515040000d22504514030020004440081025268204003a1084084034030070201181c03207420581d03482c0801c50860316400002c00801024200320b03c46c011900840309800d00c041e12040c011038020b4000000c10105140c1400c445c0c903410218044d200081d44100768100043d00d4100000158203682146c21064400051100042c1c400c100c3c00e01140000701e600740f9030000c0d800c2d1283c1c00c003540c1d460399036120146c50f1000e042d600d8082403215000010300343c01c0d950307018000701b0218404581051400314040c90403a0b100f83c0016041c11a91800c00c0302a040402c061000c5c07805410082072520300d07081d00361518a208 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 814105026 1250 814103776 814103789
    0x6190b1c0f1104090e1903050a080a063210050c0d080f040b0a1d010c030b03011a060310050405010b070203010b031605010c02010908010c1107060e15030a140703050a11090a 76
    0x2c450f401c00ca441c0c810040400354503066405400c0d1b001c3d0604014155800001c5611300040c2c1190000b400565a40107100c01c4950755005280301d01112040702648482030051203482e01495441c84000e0b60791616502d03500307007950311207594902c011701e207190905010007043e1040c0114403041c403000704400345400c0e40c0300d604400101355036100c0c0c82c01040549240c4001000c4030800c81c00c00540030304198031511010442c0c3c1c07010800104400140f600341d0354400360b55841c0d9200d82c00513007824240000199400070355554000c00030382d200c1d00050125903003030b08488010000440d11004500b42441202c400c44011401019090141030810000e44e10074000d490400c0709805404085900901c140350252001800910650407407500080290b03640e2417414946120f2200001030041c01400c81d1a8489000f030451109080c130b00c894200d0551010302050215696011007800b8904028540c2d4002e04580c1d034041410b04000c0b0b2580255800d038500f40e9600e8100308000d4106075a88807850302103c0d213 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 814106276 1250 814105026 814105031
    0x9020a0b0903010e07060e041a0306010b13092c030304020a18060b07060c03061d01153501050a1212030b03060109050403080a020a02030306190b1c0f110409 69
    0x40040403d0141000d81181402403207201004036900e134100390041003008044e20300b0406e02d804c42100d90030b26056207075401e400d41c1104005001e5291000c0c007e102600461546001441d5651010340807591051002c4240151180050700594000d40421080d07007a00c100171421410301d0b80004500c4011403003007022000824003da1102c50302c07904110b006020004646444040a090190207841c40411400009203021008220082910002ca416181c903140c0b0683c96820041038065001401d180c08003404003036651440d501c20024125000c90604010689540380414a80d425111042c0c000912444644038140302d2039600341000c48829411031600450714005e04403d8005020b59a240c6e42c00d4084e0000204042c4029000b06000c1c0380300b0f07510702810f507503a0300b0801c040703014481200006030800c00c0400d09071f03d4031349103007104000c074071000b10500c175a540702c03a60090784102046000a1440d030f80400c80d18400348241ca83c640c08002c0d0a2100140e0252550994445c60080c54003055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 814107526 1250 814106276 814106287
    0x608010602100b01260103170a120b0102122803061202060304150501080f060604051320040c020c0a080703170d020d060303090e06030f06150105070602040f0f0909020a0b 75
    0xe2140c03901400c3c4440c1c20800c0005185e91000822903100240000d40d441c2048001180d8002046ea0480b000c004050f074407450945c041124000c06001c02a081c18118820082e1241301c0031220801403440500b40000b80107176200c41455000306e0300744895508240f41c07409400300000041c41c1b414114296045480030364a0343ca070700d8090001041820101c03009460040013184000c0001003031006035500d0012078a543e62048200019100200d41f41b081c010300c411450b8000071042220b66158813282c11070425800205000b0070100c50341071035040300690240d00c0c00301540c10055000400340240d03034054040c580c11911106690320203e2001200c60b5000940080c0301406c6a05503001043e1503501031040c0c0340e4a0030001c0ca01d09403401000d8200c0088004554a8680000c3e2602c2c1c21401c00d000e0300c0c0340d50b00c0170000c10f5490541003143d81488410000300000a116200501c082c00b00000700c558000d003454503104c282d4410780c01002085d440c0c445103c0140c1d68111288048400c0f1483d80b81d581c030f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 814108776 1250 814107526 814107529
    0x40c030e06010b0717070812060f0907020c0a0501081e070909060602012003101502151f0b1804020f09030d0e0f0303040f0b09010216030317010608010602100b 70
    0x90403105440d0003a409410000700c1c400c40080700404c1d2080c010045824821050303105a52070388100f100050003484204448e0350702100046c4000e921040040410702c1c01c0a02901090319007034219011001038000c1401d4401914007600c9120150a0070b1918080d5403800c903403003c01c01c80b52141d1812001106800103201548103c442a000d00521442413045543c0c40f080a406080108088204101c1590a14105a1406042c0c0c0c0c8500e4818050004151810400300781419004507003100310701070251040d886819480c0d180c0d000d20101d148428500f0780409894100b8a4070703810004a68108100300c0f810741000030b03190001a20225801a51600303010030040452141d9407401c0c0e01402901c0070140b0721a0030406142d028141a2085143c1c4912101095100c0c407480c055040c000e030f0b80400920628002e0030103894071200600481d8180003414801d03c4813444c080e442180020650100c400c680244640b00500428046c209412a54140000030b525a1032081d20140320569074400d01a09 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 814110026 1250 814108776 814108781
    0x302120306040603020a030803041509030203090910121a0a020a020d0e0a0f15020c03122b0608061605030402010906050d06170a030905090601020c150f0f0a1205060f040c03 76
    0x1103030300a06d542500780d07a9203001d41040d0804c807010ba5440c1e604910441451555004505c0043e51542c040c602e800304403020404109070107010116010740600c004110406841d10084034140101c03002c1c0b0291401c07003200136244c0340c020800ea000c03d005000380107615400140818081c08203040c4110701850f07201c0481c01080e02c0d98400c1e0511105801c000030041c0002c980170109440b80da0903901211788000a141da6405401d4213008a9001040b006c8110b40f0307020148000c004901007103180e580da41d00030b402d040d40c05641000d82141c11400500c108040305640b4400c1c100368134104130f0305518058002034583c01003446284241314000861070402c0b540750f48140090301da544c07141c1401511114415944030245d0104a02242140d44041524584200003d104c0c000581c010511402e03003005200c6541c610400c0c01c941c0c400103008010700841204054402041c500c0d121941360f0105040c01060b00c2014081c6907241c3d4030f000d080c80055140c200032894089415035000c02c0c0c0c105450800ca00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 814111276 1250 814110026 814110029
    0x807150203070309021017071101180c0602150c12180a0605062d0d1a071d040509060424060f060810060903020415180509061303021203060406 63
    0x14040c400000c005900b034269002080550003520b031030003030140d0300c842074a4003902c4041c41c902030328021000070401c5204180090760441b00c03100206030035404920401c00051500300c122175140100d07400340182503041001e003501a81c400307040280e5050042190300c06214034100b1000300c42e0344a0004822540c140c0c2e030106000120000c64150019604002c002800140d4600c0d2190101060b00144094808140c000e060b601105644a20302c1d944100200c00c01035400884614130410307400c0010ba030320240907038411101178440300500c0002000620000c1120648644128902021702100e03900c000b4103d580179600c510000211030856a41c10310312141800004180760810b1004604051845c0d190011520961110340c19a12100c4211200d1245800750500147d07203198200003600e410342204000411861242d201e81d51220110214a01d143c00c4040750561900140100603404201c015404004e5400c51b08400074180e4000351503991075803a40d07000c4070012010850f03c2d6501d510400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 814112526 1250 814111276 814111313
    0xc0f0303460507031d06130c0b0f0c0d030e03030601141b010b03120412030f03291306052d0604080610050d1e140601090e1204120807 59
    0x601d101203240d80384000d44003c8070310100081c20b203288203c0070f0740d100460b101c548032a080500034941d1070205142042412110517501d24980c1040080c40c45070314802040c0354110340300c00e01e564402d00a522483c02a200240b802094a08841c1614006022040d25082070302446c24000490011181c88175030b024200c40919618005039026103036a005520607500008243d060310304454450316100c141740103070301c10744003021380341500080024803458035203820380e01a044c002550540f600c92115103a11940da2040f521451035802c07800c070326041c1c21141919252040502070907087c8408610804202c1c2e00c2207011900f030013905040b004401c4154140540040c104985950f550545581c1d030780001e03240303418601d400340300101e46400c00700f5445078050307000360b1203806900340740784624444131030108280c441c0c0321045c400c0380c40b00000740308190007004211070110f22204d000c6611410030280b51000c000d0a0820002040181d8a0b54060700b0a150410400c075100e290741d00f0204441c40c1d0300b64070032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 814113776 1250 814112526 814112641
    0x8070201110c030a02061b1902100c0804020906100509040e0106030501091b0803070506011404200a0306060207050a1406130915060e0102060a0c0917030c0f0303 71
    0xc441d070b00001512501945900f15141502c0d8003080c1014140410f55840d400075080204964181074242c05140740c10645c4100d489100e051880d084c215400321102d0400140e410080c001035103050000250000c1c0101d811055004000030043c04a1268403c03403406943c44d60440c00c0490b4081d03202d800110b42243c002c0c07100358058a81552600c44005402c00e21342a500d802060004000064400300c2e03501c2002081d4903420003880c1d502c00030526044d264803586035400000740c0280d4401800d20184030704400e54890060440183c00e5445039007000c400c55100030010055662000111800c80b41c0c42e03208080141d00d004080744a500c00c44020b0070251022060000320900c2c507a00c80701c00545001e40d0b80c101c4d2500d840742210011203158100b801a405007002c0399250350251301c41544000141009504c80c0d07560812080054060100c00900ba00007060740c082401c400c0c04144403031010840034602d90320304404030082040c0d00344811420195180e1001c0e040e522000380810264400e00c080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 814115026 1250 814113776 814113787
    0x3080f03010f0f030302070e0c040b1216020c010c0b07230702130902060703031d0a051b03070b07080a17010305010b1003022d1603080901060803070803070807020111 73
    0x411819802032080c0050344404010001e07420922114410550b5890350240880758508100414003000191202074020000c100008a84d44a00010070050070161601e410925005444a19401c80080e640040d034011040450440e07920501001c0e589074800420307400c41d1110305040300c900f07440d1006060607003460102001141851009004468421100c6000000440e500c0d030042e10b03056000250050401e00211000a00070303080340c0301c1d4043d0819604200410b0f4403c191070701c5040c4005603156001210001d0101e195401000094281680281000383c41c001b0381c074026201e0700c080a014403801152042d0010b12070b500700324036440400f20040a9584a0900c00e0081c600308075006d109014071048000b615000f40280e0f214140303a014100a0300d0809038208400414510403414450401c0003041203241e905030400c4400c40c02a920070300680380003654682101c1c080d41200f0034a9000348220b00000300160100c076442012490f0031680d580701ca07c01039000d801010314011081401090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 814116276 1250 814115026 814115047
    0x2241504050a02120906010f1d06060c0a02190e0c03040c0519030c0e010816050901090e10020f2104150c020f1c030c0806151e031005010f080f0f100308 67
    0x80c1b00d4141c0300701e81782d180701c540c1d500c030a040000e21110342c03880344010001001801c2882c2c49405044140c0200041d580b4100715903000582c1203401e038640d0580e0f079150340418411902d481503200d030300800c540c110f24a5802d1a840e54605a500c3d0f2085d18030582582042d0701c00410550507100056500c8010100f0541d20742c15856800c500134050320f03845104034010030880004134611070701214000342c503c8500740d0910306883e01404005200c0c030020301c0340720350340d00c1d2614040c401001c5040300d01829544940840218007691030b401036008034480703083c50038000410b403003400b025009014807500141d00d4080d00e2080c0e080610042081c083c500500c00b50001d0282d200040045510a40d60300300500e080b1100305642d80341d0f055441c16080511004074403100c015440c010210301d0180205407a0501c190f000b001c686a008554580014203081c40030042944c200311101850303001c60414622511b0403201802c0202e130010650b6201400b80000324544070315004d42034018607008001e050b82c80c540700d035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 814117526 1250 814116276 814116283
    0x13090504060b01030b01050a0c080f04030b011203020d021506040209180a090506010914040f03020c03060109020910090303080f0711030a030912090503070311040b1002241504050a021209 82
    0x602c6680400d0601384032086662007182218001c10240d10b4440070101e20751035842d80c03030f0404481c03034044020401020010880c40719000d4028070b06003051528848403850000e05040c44030061000395842144400d002c8000c4554244d80058299401a240c0b011000011410021172010329030503d03600c82441280606074010494090048048a0080c0d13652400d11044825140c400346d041020800030400151003100000c040501070b20441c1c4140e076440000030b00b8002d080e0f0000600340c0d80042c0c13800b041d0030700c14038103071540c4d09074207004141500c3d544000d45640c0b00181100007988000000032501800383e5038003c40d041c2000200d0f0b0b2036081c265400340003848103039405e480540f401e40d5225003041c4924200d07070035203402502402c140f52645c0e46049215844451956000307407075008079201611904003d96650f21245d00130120301d80701c00b03281000024100b0319003001030003000411150031a001019280c107101610001040d5484100e081c000340111201180320040c40001e0254419000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 814118776 1250 814117526 814117541
    0x209120d091521020c15040c0f060c0303150f0f09060b07031b03031b200c01090510120e0706020f010218010c0305070609150b03120f1309050406 64
    0x1616450011500d541c0c81d04081e001e1042e2000000b1a08111250100b008040e211540386080700b0240c1001003a61440741401b54403c10480c8032640e4600304414080b0812802008100e14260b4206c3d0b603041c440f004010310a0f40178054241600e1300f50710021503482c0407040000348840b1200c01d600580721a03400d040710300d1724410452620b04088010604480681c02c658072141c1c1525409410303002540c0d400440d2450007000c0c0d0030b0594840c503e410b014140000340d0300c1c01006569001883d032064001c2d04059490813449003403503110300400350450760090400820b68008403950700d000c014084003225007002c0c20b05081089424410766103050b0000203008815036a10703800b907595851000707226600b03e000301525130081c1000b08200310b030554090448501c1c0a8024070304a861300c035032900d904050300c0e281081129100314405108070340c61511b1061107030004046000d0040380c0b0354001c000d10140140004400e81040000781a5400403e00f2420402070500c40030510040c030349810500d00529a5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 814120026 1250 814118776 814118803
    0x20312070c0e062701090f2f040f060c020907030903020a0b1f08100b01050a09030204020901031113031202030f1b0c10030609050604050c03040b0603120c0c0316060210020d020912 79
    0x90a0344400c0300d1115004117030408023401c0a24262800c0c0e65003101c00007512003c6105041000c100100c1e1000e40c0039070201c00b0704996190a072241100d403040c46070810700203100e9001c0620b088070300710000c1d0380450307581c0069800441000068072525880321341100072007440e1900c81d40c490000101d80e08049400d03c40c0c0d000004080240e407038881d006440910512920320005114140309100524055010307081c10503040c500012007c0310124041525440a4071344116260203160801c00c00a802102a4209415101039402e00200800c4074404d805500000307810104c501c45032907080a41001800c42981004103800c0242c040040060300504050003044405030510002903554101801054000c01e00d400c2000c0c51603699403581603511001a00e81030f030500400e829070300c000300700310b01400d00005010b0181c803181403927800301441c1890302d0010001540911404205040d000b181d1000d51612007000565100d0074002100c0091260041642c1c0c4924421024400a100000d01c050700408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 814121276 1250 814120026 814120031
    0x3080601410903030703030f0906050415060602030c033001030305040f27020c01060e0a020d0f05090715090510080906090a02060316120f0207020312070c0e06270109 73
    0x1861002001d148285038156805510421088000a00c2903101c0c17624840031140000d0714010542d44d020654006030303401c2c1c07011010282500404016840b03403070000e04850000798900035000d050680c0700e01a0180c8058544125072581c05030711450f200410300e083c400c03161241150785030700e030151468100b806442d200e0805440c0c081082c4252800840d4a4a1481c1c4d90b40c031910364022449c1c01a40c0940c00400f195501ca95000510150301c41c0c0c101c1c05500d02c0000561160b40e001003075000c80742c0000206540c0341c20034050003603050002c500741050381da054403680a410b02c0101c054480b0802e560146410410002c11043c6c541d0b44420814025031411040d1000307501d070340158136078495869001a40c006800c00205190107200382c200b03015000f090810065100c41c600d0b6500890741d5803001240169000075100701149418050481d0604a2400d05410987d02c0d4a8420304545503010f103480c50200100890307402d9a40c00c0112105515001b1400c0155080072400603402c0d0f0b081c0301700d042d41d60 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 814122526 1250 814121276 814121387
    0x4030f0206090708070b0a1b03032f090f0312030c0d0501080a0203070b0d060803071b06180504050601050d090501060612090b06040902060912010504030806180403080601 75
    0x11403100103c0380e42c40c0050162a0400c03003000159402605a0300070b0241c4107000c208c071140c00c4501c100b40640a5140082c00094002c089000c014610108220b2840c640491101805c2060240c403100c00e02690388001ca0461080841e2030040c80c20200d074141c2101000b00180c41242d03100074416001d240c0340030701059a0310383c95140e41e0708000000130b41c503401c440b4003407204003190000b92203a50808403001c10000c1d90b4609460461303000107020755290100c00c0360706c004c41207550450300c02030415203008060103009800900600c841070003601c1c030a6440f2004150160710a0065503501c1070394640c02c00c1011064a02030740201554850880811542c0d090445440d9191050100683e080800100143d42c0c18080000500b1000d004070b80c02031050007255040d4540510103503100304190700016050504e0300740900034500007030003140301d40b15001c1140a820035041140b034200b54103003400b4050384c0307420b001a10580301d0051031203ca0703d820350502000f4010030b82d5030901c60b032680710b802e40c400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 814123776 1250 814122526 814122541
    0x40f02040f060506030f040c15050c0d08041a07021501080604050106050619080405071a030106320a0c06020f0417060609060904030903061104092405011206030b04030f0206 76
    0x1502c182c810168010004d00004003080e078903034521640305124201d0b1519164980c9252801c0310401e00562001941c04950340315085401c10902c9c100784100e08000304186815541c0c000701c411688018180250840045041e050007006a0740800580005800c42580c6132040b40b0f03a00c80046400b640c640d828801c0029050804004035601c1c0400001c1000400540d68400e5a0a601c0500121348a100c0e585002601c0c20070310041000482b240140603540c1d5160110083c00341c20b42c0b4010b101841200c0140a040e4445100902c0000d50700c1d40301c0700d0b04c4815444050728400103015000e8a4070f400010200c0441103840010403d94640c10b00b89003004121821007503645608580e401d410800040c041581032500d119a5540588249860480c464072641d0b458203859440d01c034640620004502030101000501800d004107a0341007203c841e00700243d501d602c001181c0d00c030351418003104081d80078060b0f0300c50308940003654104046605034149480c009001c010030803800c0c80140903010116140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 814125026 1250 814123776 814123781
    0x3050f0c100c02010c030c1b0f0b040305030403080c0c0303070318140102370516060c0323090c041e02161a1b090a030615081b031b0307050603040f02040f 68
    0x4555641c1c0d88d1422880318220402222907145809480c5a00f0010118000640c40030059102e940720307960340c0d03441e4202850090b140000140064002500501500c000141d001080d00d030300084501e408954540d600070002c241000d0107401801d842c0b000000b5540e40300054000f4060300c0c0c0e220705141d1181304c10f01d00c4e945c1d4000c1800d0090601c3e1556880d2050202d04c580301074a24030b0000307010b0004210031941c0c2e07607048413024040a40401d0711600c1410700d00340c501340460030b0f46054000a01444c81c1040c1e11548454001800d50321450303403a01c05401c0000500100c440d414005182190382d00c980555141c0c400030910411a4000f81003001c521303130008035445050040c460504070041c0e20400c0b4240780e40c690040307100d5030f030800b944d07420000c00702c0c00078001ca240740271721034061a01c0c060800c801507091602d0b0001a40d140c1d00e0003407041190703480019074000007001c44d0035003080c0305250100103810701007140d2000e58854800710900051110842358107c41500c203e40400000c41188640000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 814126276 1250 814125026 814125041
    0xb040302030a110325050f010f080708100506040914011205030a03020a120204140405060a14010e03100e2413060504050a05010e0a0b011a0703050f0c100c02010c03 72
    0x1016001884003a0000d111400c00d0010b0700c20080175665584000c51740070400c0c194403400c4660640b48007030108101e040565002190f481d00386001c0030148241c0c00d0103031074100d01030320a000700584540000c8507250441c14000c050400100010382c2c65650381603200c00750411510382458400014000200f040080090810b0703503510601079402c00e503c1300415002500f10700300000610100c21005800f0490910003400a00802c207000e24410a001041c0403c8a10041c20035000f10105003090000d0704904095201c00b480034645400d080d65054086810a9100c0c00426002c6041441c040030864004c2207229000d04075603a2801007402d0080030000d400400d5031000107941c021100e11001c54610f030405a8001e0241c0100d604c0402030380c4e900303421607402460302201c2c3c3d005404688100010360306118010804c060310440c507244104100a0f03540319140d030080c240403002404180c22800d00090b94151304001c003ea0320150180d4030008003800007054940019489c0480550200d4000e11901c003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 814127526 1250 814126276 814126279
    0x60e0c0c07080613081608040303050307030b0406182c0f0d050304240213030b0a0b03060606030a1805011419021624060909050c09070f1b1b0e010b040302 68
    0x800b26103182c0b0350380440c4c0d2206040c24424403403910800d0216441c07200a20045110356160cc1c2c0d80d2400140003011204558000b9104034106030041052651a9442c0482c20441d058000b840c0004100001c40141d10b803e0501c0029008030790f14510042c0114a5045040399281952603c0c501d14100b120340e4401100c0040c000c0c0460f50201d07002014041145607000051a801860040c4c0f14401d00c4e6018980d601c01c40e90801c8100c10400c0300310031401001a0303460160000d12080c10143c00203031907800000c041d40b081c07581d01e0080307164105a41805084035a0014020031a0060300903102c80c8010b4111410700c50700f020329030a004c10300349074422501c103401d403481b202d1359820469a816403102e91f00c45002000e82c16000b010424500548034440013802a400d0000e1688490f14045080c08000c49006204910400402031469040054002816954030f05164414210a21501000c5c000d0b41e02601d032031114609490303400e40d41000c1009480d150110103841d40e03a44e00c1100005e200d40d02009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 814128776 1250 814127526 814127551
    0x3031201121106190807140c060115020111071205121006200d180f0608060f100503010608060d0b01090207020316060509060c0c040e0a06050615070213060e0c0c070806 74
    0x42d92188248080c580001e41c034900300e106013440102d1f03c0d400360410407052103590441d100410180b00c20001c001c1caa90540e000130300c5440000304001c01d0901400304094002806514240c581c144200c045409482040c60380c800b4508065001c2d60040c0c403280510380119216204800400300700145600b0410807400081c0444001114115000c044c0b90844401076019101c1c04910f030382c0700c0c201700303c085c144994440085103818030400103c403000318603450007400c040920000c103550110460b41595030500b4040381989074a000308030700204403a80900b0200c581d00010801d1403403074005022040c003c408642c4103c10020403503201c64414824040811000c2101e80d1140c14010060070408000c030003a0303180e0851820101301a1b0703602c404c1d5600c1c0e54200040c04404c0020030712829800001c20f0b201034034008003034902c00c0b200b8851070b00086c0c4502c1c884000c14541441076001400582486eaa040d00340e801c08003e000d0668102d211598018000d00c0c40124036008001901c40c4221036048a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 814130026 1250 814128776 814128817
    0x7021b0901060e150c0c15040b0316020a0501020333060d0908041508180c010f0c080d060902030105030c010813060510080304030f03033803031201121106 68
    0x50f01c001d8040210160003005010341c0360007121285000d4504c00c050000500b810500582c2080800040c0144001d0400c00500c820301c594003165060380e601041446000d00c031900b018401b070b45440b07100c50f4018007540c000810440c6070042c10081c07010740307958031000c4584180400e204009000850071500d800030000c6c0720b1202901f495801c20201c0500031001d041c9000d0b00c9450780000d8104a02078100400d62500c148204007243e0046074528101c294080c0009500c02c50008000304e54001e110820040c2e851009010300010508440701200601c00400c00c80e6512030214019410034403e6034800c1c001c0341030b100c20035409511040e10036001a994040b1000780c80c1da600c07006110107030085c4856041c0540204004008200400103140a4440c2507140e400c03615000b400e40780385041a039541012000140e014038081750b190480a1520100380740c0c484259004a499405440e06110212544000004028900c078100781940340c0582d02c0031844035a50f905215080c8241c902503105450301c03991 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 814131276 1250 814130026 814130039
    0xd062102061605060a0c0215011401051c051306060605161e05070603020904150617040311011d0615181b07051b121b0f03070e07021b0901 61
    0x2030500e60303145255840c4144407030f00c4440c507080c01100d020041c1035542104240003030f0100b29100804503d501042d59542c140701d01c904500d070030b18403020705000300880c0d0703000d546c80e07501844801880030f100d0802413882c2c030a1545189009850064036441c0c0740a6010641c01d1107a02200d44074005203110030141585551041c0a1348880000958881c0c1b04074801800240280030550081ca95a940540c42c0c00d00042040222585514a100081903100b4108019600117801e40b1018051841c0c1c0711144d80c4906054803407504000c040f19440d441c000d03c281a81d156445c1c541488131001d022100c0c281e6801e051500180070040c10035070320481c4540c420481844481815501000b80c4218251074501544c0980068000c030b5021a9550010001d40d0302460080c0202e6444040c2110191008640a0030007034888101004917510003000d60740080c030300c0d2100d560b01c000b81ea1000c0c00311404142c1d40d500c066211b040955400c4d0042c05016500b00c003140d80c1080d00740342d120000303201106603460480d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 814132526 1250 814131276 814131289
    0x316060509040905010e0a0606090b0f01030c020c041107060e061003120e0a091e0b010e06180a2d030804090f1d0f151e0c1b030d062102 60
    0x1c5140d50040d01c6040b0300740084d00a0096044d45038104004000380c8000d8074003401540c000d074100040f41031400b22a01c00030f40e200c0c3c5031204401302c01e080000315058040012420140402100c5810504020000e490710307005070700509615004607010071613031100c81c3d410381d2101d606441e24005825050002d10100d95490721107030904c0c0d100e041034911180702c6c0300428515076040d802252501e984040c1c040ea000320203420f0321030914180900300002d5024400191285004a40382c50003840007244020b00828080039000460f03000410320440143d50313080b0038080d406000c640184844108414808110361651030b00c0aa0b40c3c003080d200c1c28981499007440003000340c20384901c81141c8641481d0000c83c221040705801d4480d03a8050043c1581041c1110f1070824114080c901b902d00c01c104100c000c01102030003103079400b801c940c0d00341e041d00ca039503541c0c12600841c01560015081104102500ea100000800c444c10700f07260140145559002c601c1c041300b485840050b0050350354214180145000c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 814133776 1250 814132526 814132537
    0xf0f0f0f060703091a040809040e19020f06040e1311031f0b0f12032d070f0c17070305070f0b0414030114070c0c05061c05060114070b040b1f0e0a110a080f0603160605 73
    0x3400d200c3c140782daa0849091150d00c01e640306081100d40d100284140440148070140d03521084c1d0081c20f94800b00740c0c101b400321490b0824400a240d66050440c1c4a03550707140002c001160007840e80142c0c0b40302c000723a180c8a0f4002c000c0b154420030001e00310060301c008007005000740301d0588452070601d80e00e601d41440380345050008462101513100c0c080307200c00301240074070110b02100b8011300740c0b2411460410b26156550300502c801500e040030404c0f030f002d00002110261501c19007030240d00e1600c900428007402086101c10180e81500041160302c1b81c1c17040d5500040c5000c1c50300c09010941d81c509010040c45024064510140d004098041422468100e16040041890120b81d4140c610703c0781c0c3c050b508058400c40e0581440c07403d01083c008500001a04400c1c1d2440c0e800000c176010400d458998820700c81e042c0403240740f00000d07501c0700d2258010300030f00c4d0100350340c10b6072404034450003464039000b220340c00c44110304140462030b0b80c1800101c4111020b9080050040b01c0e080c0142610390390090b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 814135026 1250 814133776 814133779
    0x1d04022206150e040f02030127060f030305031603061208031b0316090e01080712111309060e060c0301050d140f0f0f0f060703091a040809040e19020f 66
    0x803800000341c00c070702c401c8680d01c2c40c48182d6900c04580326801d04120a0f242c06035015500c10b4010f10042c8007100c4161120041e0241d030f450030f510b1004150744003101a1251b87c0c465402403d0100300001410307001001548648030290048401c80c008103c207500315000b038003d030340079a8100040040010001070041d80c1100606101d5002e1b4120503000301e0f92603104948140a92403480104424280c100f6512806420300d0010980a58142162603075079180a1088000080042ea5503c0078851a02042402c40704041c180c0300c070150200915001424050b08111a00c9207406448001d81e04040340031400341c200658000e01d583d181030700f00003003030207180802c0c0c1c0c0c3d82d24505140001b5500c100300340c0d00036944080c0508400e210581100f8102030303000c8030201843e08400c041c1c0c00e100038080350b2954840524140010801605d0816003842a042549601160740344402d20050080c00409001c6110040707800b4085200d4440d03401c1c6d00c4a00380400c07550040c17001c030300d860018900300d058403114820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 814136276 1250 814135026 814135031
    0x61e0e060d06090e1912050a140304031d06071106300115050310091d0a030c05010513021813020d0309030c05060a3212011d040222 58
    0x1400c41d1440102c0c0d88940c8100c480c1c503940c11312401483d100303221012101081444421024105456402080ca03003400700004124000035070400940c000c20102034181040ca0541d42c0303034075042c5806401d5139144d40c1e56219100c0250500e5980303203010022948207943c41040008110500f000703000c0c00e508079502e00403000c2e0810707d0b1140c10050a1401303c10f460014420b889165141c500c1500e29a00c040e000c01e0100700b02041004a08003210408004481030a00000b034907510700d40d89403000c00304c0300b43c0d404c696014190b402401e1503172081100030220f01036002000745488a600c2a45400304501000f50040303d0101a0140710409420280c2d11489541c852040c40c03c540e40042e0001042d444200c01103400204103006001c3e15120100181c007041e14417614080080e88007074018200c50380d900009280b01c9903002c107913841c421000100c8003040d40a280d00d42d030b40034009024108090040c00c601c80b070700e0080c500385034090b80328a03406903802078030507440a0800080001d2400990740009000c0c3d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 814137526 1250 814136276 814136287
    0x81e0c0f04062d0e011a0a210911010203030709030209040203010b0904051e0604020603540c01050f03040602091e040c030b15070212120c07061e0e06 66
    0x4900a065507428075849190f2010281c003040c5042154405400200c83c1c0e14001c001030109551405000700c10b9a0740c41c000540b079090100c03084803288002800d11004019014a041001220b90000029140708880010048100c3d01c01281da0b40422a0028001101c0c4181080942041e0901a03040f500203030010500203280400300300c2031601940c0840e082c1c1d100584040000c03510040880c0394511400190400b4205900002c503207004c040c0c0b1414607140740c41c60185ca402064940a6003509d40c200b84101c9000516803003a4200d000140c0144803403202c859054143d00e4041a00c070045107058440382c1c1846030b0513001c202e154200034011962190300300b0a900103691200101070043c0140105242d0b03e0607030005000988804180c4402450b08180107020143da9940780a60364250b080d035242d469003030900015101c0002000500d0b12800390100c020744144101004120601d40e900440300c1c01c980d51003085800612902c0704140600c003550201009604c101d80280e400a4001e04150601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 814138776 1250 814137526 814137539
    0xe03091513170f0a031706030a0b0406020d061e0306050c130806060414090a080a0e0a030b06010f02030c0709090218070320040324020c0610081e0c0f0406 68
    0xc400c81e000600b616070b140c8200b12004104200c01c50b4142c1d00c2d403000d00380c0284141e03409454071500390f510b050f06d01101c03000540544c9080107640003403500400201001e007440e0030054002e60200300c0d88003415041c250017103010702207000d1000c203140400400e0503100c1e2030343d1980300c000c1078003406414011070b040202100c00340d00c0c420a00090002c03070000d000b40c1c0c03e100c0200812145002e0307015940d2510f600400c40c8110007c0342c2c1044031130b00441415030b00e21428502b02c1c0e50525094040780d2040c1003030300c080244800385c22210f100307020070b072600355000c5c800c5d500a0b640c0c0d00588200524076800300f60300b032102800300c0d0400c484840c8050420302c224108043c00303040d050707421604da00019035a40703c00700440110501c12107588002004643ca49815500c5400304418000481d491800d888410a08466526411070700c801050000b0f48215040c0380d01080e1043c00c9510481c100391040e00d800c2184601c0c81c000c5031100e203080c04020034030011540c050001190060140c260310990307403030002420 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 814140026 1250 814138776 814138807
    0x130204060b0a08011412032b021201170c1e01120236010e15070f030531141815040f0203040b060d0602160f02130e030915 54
    0x38844644926042e5810146450614001c00d1282481030240303d03103200c6c0001d4040b0441d6804c5201c0d00d891f10300c6030340c0c3c0c1e80900101d180c229059004184009030b51140950512222030503103406a51040480401520341603960315428051948010708082c2001a4940078161030040c01e81810b00d80070a1010034080f0040303802c4400d4418140400300035034004001e00c40c085001c07030f0a49100380c0d14108003030300009100303801c03281c4d280f130140440c0a941d019103110b02007940c06144d440580a17610b000d10b0316000b4140e4000d0780000200c844034180040c517052014148070329601e18585150f440c0352810000000070f02081080da60821038105521484221401e4118811014861000c0b1030004031010b1100f00c603581082c45148500c1070040c80002039060b51025080301d003c849140150b012420900028454500c0e03000d411790484149100b0001107103803120940303008480e041042d0200c916400152204a1100b244507001004254242d250501c0c4902d10201c602983c1d03401d00703001030509a074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 814141276 1250 814140026 814140037
    0xc1204050f0d031202120411010809120c1f06030b0c040e1b070606081b01020a05190302030f0307020a061d061b12010b1306020d1d04091a0f06010314130204060b 71
    0x40091b0308070304100500c968841568149207081c600003290749811500c142c0c1b40c0b602441041e8001000103296841c3c0f8808100c010301f0580b6094041c01800d01c950380c418000d1880b484100d401500070070000d03403c0c0758294150340448217007403104040b9a036803000342c00042c0000700898840d80c909000d583c01140c900d01c25a8060400580184a1002c220414009865007001c1840c1158441007140001039004501050b881c00e000440b11443c408071b2900b40d00310301032091040d06521000c010082107c0d80050032a96060003031208000f0101590810501401040e905171855481800800c200030200e40a42441c0c10700180e00606005c03d074125641156000e901002070b00c000415628001041c0714058002001240014100c0c0f0f0562000a08001e142584071048098030184686080c5c80d05c1c4c001c2402958441c185007a280900c814415110200b5583e0346020b42c4640700050301940244a0000090710141c000f0310030b41e8032030814002d50b0b04e00c0b00c2c04a8010752605000259490150064032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 814142526 1250 814141276 814141297
    0x109080d0c1e110a090e0a11030f0d020d080a0c08190f021303171e030712020f03090721080903010603020909030a020d03060b16061e020c1204050f0d031202 69
    0x141c091410383c04010900c00c058000c00000c40c60b0500003180810b00103540f8243c554440110741b030800400b40000d05080074918048640c2c010f0b00c080303040d4254086841c10343c8a24684401c405611000a10800c540842031803102040800c0c4c041346010314501d922001e00070307101101040107a03090040074140d03080740007038007200601d142d070503c10000c8004218029480e000e505c6402c1c0f111104a407511400007111182d0354003c0080402e50052007440d60782104444075a0556541c48165091891a0700844000d03106014408002c0350f00640d000110000c100c03070030f040340d80e0780081d134072420079030b80c420000f40743d0544d43d850700000140c0303400f41e14620840300c12018607140c0c00320200c064104903042c54101c0405240001c01d100082890040c1d407081440e12b404090b0fa1042490301783c00034030310b440c66851882642c0303010150844190b001010400d05600c1a5030340b132a00070000c2840760089001e401c1d030100d5064030324521b500782095401250703030007072911401e2103c03070034204d0b030072603104c0426070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 814143776 1250 814142526 814142543
    0x60a05280905090c0304050c0603252601060905061b0106151404080a030309111206060102100213060c0836091902031f0e0f060109080d0c1e 62
    0x4000078905102c07040d5100304028013080c03862420b90b4849072501c0e03281200c144201c2001c07000c0360003256410500782e0003103c0045c400d00124030781040602070108640c500d103202d83d0820300080d1109002c12905040300c1d45502c800700d615080000700445034100800c980e100480c01003c0301c2da02502405840000c00300c640c0304942d6045009401461a1104208102000410041000b07060400110403a0941c0c151030009502001c0d460290550207001400d6544200c40f62440000c1c03a40c08946903029490903021180e40e01a00960305c800d9003e8040c0c01c07901c0354040c00b020030155001d452120006441641030b686402c169074240894010b0b0240f125103032011600308411144600c5400003240c0000301c0d225103161070214040c2c140588a080803554803900072011509440b0b0582c00000c561444121070001036407904910740c40000304590002c420031028001c200903501419004040c0c403160307000b80843c00409001074030003003102c3c00300300d444404000035640c071041130310390380c0340f50600c42d0051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 814145026 1250 814143776 814143779
    0x1021215130f0b01020f0a03020d26040c17070e040b1315060504140f07140903011d10061203030c21020a120203010b04050922210509060a052809 64
    0x9141c4218400f140b40b182c2c7c410b04138003010a03000590510148024545802c0386107200310344c007804103040001c1480302d801280a10007001002030295050f05c4000d01c0300044002c4912156907a00c980c4c4c400c00950341e806101003400300720506180c1d41c1c000e01d50103190048051075a00c0324451040074160f80940d641d190018440e9140c9400743d070b2074041c0b07a2030205545060581d01d030200c25a020f41007100307000081d41c1c251000c3c00202c0c2550030041e0000c00070400300303c407500c00709410f01c030b01203a101d120300a4a104100c5914240b03e18425541c980d10342c0d1092980d6940c01b034004040c80101e040030b10400821540405844c244074491030b09a014000d610f41590b03c0024003c200b500070081001c034010310061040da030b5201c09507012950b0864522681d500d845a840001410460300e055056007400750107810701030103010903107000340300c154182000d50b4840001c0b1554010000d085900000410031a11041d01c20300181080c694510000088800071402802d80b1198452026000c6034040c80e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 814146276 1250 814145026 814145029
    0x307080604050c0d033203010807180905030301211e050d0f021009030903020604120b0a1119110a05061009090c031b0b04081e01021215130f0b 63
    0xc80f0114042c01d8030050700035441d0b075030046c1400c41c4503400f03454200e40241021030070703011031110101c0500d80300614580d03c1d6100e10240d42c448116015120510540c13007512025170350948179503804c0d1a000005103081d40d00700746200750300c02224206803000c11100c860f01804541c800250402008540211024201c80741c03a2250405440300c0f610010b01003c028141d4036990003082c40c041c9082c080c0d100080315072081c5420388120800d0b03000690800000710b0080b54820008088080144c010781403007207207540f880c0499081e42c62611030400c01c10b00510694008003a1849075018002103424034441c0a407030b1602092402000e0745042d225036005805224440c4e40030407140c8042c25810760148400c910f1515002d000100900c0010305109140c0b145c080411030000755100640304141519984950320031046503140d0614411921001d910828050040014800c4a5000d40e03400ca84c50560b55401810007004a11405c0c0250400c454820401d411b030740c18030805d0304074980c200c400214800c0a00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 814147526 1250 814146276 814146283
    0x304150501240503090d050f0f040906090b03120f1b0303070c060501060e0f0d0302030f0f04050906010f0e12030f070b011d0403360303050901080604060b0a030e0a02030708060405 79
    0x880b141401020424071204002c00f245c6c0e20303e803402504100e540e81010950a6142d84a121080c12a500c4042400326a005694105904132120610203202404020003016110503a08207143c0c400802004040304500c110b00140050142540402d4418030000404d0350031070b882140c1041c00a9840545c2c081085064031480c1d01500c060b24008034102d24070300102d00280303581910313984152070740b0500300101071081040b21800d0080035016510b60039001d5480c28580c21500840348143d8007075000490652082c2d83c22072203686a039403580690a81e006c1445204010b00303d40785003a010401012005010100080607910b1203607545160b80d62505140d1010411b001c1c0345542031500310000e20000c00d0b400b03258a582c000d1880365100c603200c104071450501042c50450141d00342c104070f80020074035400501070b00100000b80c03510401e03a41c441d0108030887c1d4007401040400d110034000344080e98403a40c40050605d407103030100c030001005500080d252450030750205115073b001e0803c1000700308091 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 814148776 1250 814147526 814147589
    0x306010801080c1810171006080c10050a020705091008060a060501080402010503090106030219030b0f01080d050a050708032703090d03030c1209060b151c020304150501 74
    0x4020709140300c0e600b0300050f01809800720380001182c50402140c030511030f9031780c0c400c0201610304401441d11038240b5441e44411001c007022014526120700000c990344c01050784045581c0040c1a036855104410065402c1c1e000b0400031811445400c20110301500c80c0d40e51680501e01c102c05200071245022222460448010540c96060342466010441c41e40c00c03030f492941090742402c00da5204d17070342d81ca561401006c89900c041d6002e100b1801442e0f9030311501a400c820740b4094014501c49a6070f80340543c400540a210341c42e1181c0c00f10680704a041d10640141000e0002d0b46092881e0504c191904049600195a0090302403491303000581c00b542d16288400c64004124051414241c4c0400060018400c440340131b000c0c142c8132099100034920dc1c1c03071110300701401c039072040054111604105000f48002e145403801400201141581480b6410945092000038141f00460024600215002c0c0d04041c02c210344540d0b0410120900960b41e000c1d00c0e02074120754400c110251406024a80241500d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 814150026 1250 814148776 814148789
    0x302090a0519030221010f0906140f010303050c0c0a15030513080d0203071e2a0c032003100e1048020c19240c060c050306010801 57
    0x100c0502a10690382c40c64004200c0e501290145080c03d0707400305001e00d00c414555404115417911880d503001c1c100702c3e809900601d020b41401c124080c1251001404180d080c0c07845501c22141500400000703100d003000f403040008113800d03101c1540ca10000f15542c0d88076a086007010801a103000e144242d850302c1125444078880e046102d0342481a100d100e00c03846254003001480c1d030000006822240640c401c082c0d4403650302a11f025424107084020500b5880480303400e810341300560301e000d0301c0e284410840c03ca280c110009010840c0396a44161a4100c078030360007c40d4401c2541882c0080d902072002107034040000f400440c43c810700c40d05c1030741000d0001d240482e101e031400000d1f05190450055055440341d06001c941160403031030300407031003401d801031602098507184141010103070745c0400d255140d40000d98022003480c0400740139a489941a0295054524100701c880f000310003000c0c4840c1c0c1c030740c1c0503041054101d00c0301d4880d1416140003542c21400b1410002c00c1c41035a52740500040d005020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 814151276 1250 814150026 814150039
    0x403050304200d050a12140d0b180c09100f020d0309020307080a0c0326040b07030306030c170f030c0c0d03091a121e0c0906090a06030506011b0b01060f1e0302090a05 73
    0xb1000c2038481a800754080c0f0400040d070b1440301c20700070f495114102d1030038080710ad440400e910b0680b050190951028900700d01a030300406030100304038007410051202c05c40c1500074081c4460485004c40c003c01c40a03009030b0341803181090004043c0001d001320541d45000d2203420004a082d0b003021490300c60806038588000c3d155080440780802075000365401e940c0b011170180d964008604046010f01007580001c1c00c1c1d404154800514100c1d4200d120541c80103450540302c05a000d070708011780360300411400c0c84071900702001c0404149007840000640a12074109440301503214503444510100704040c80030500070004141c3c021980768000c01e94050002c1494082144504151941348500070f007080600b01c2003c40d02481a50b01c00f4140c550401014084a501c2c1e0358820000b405090240e5959022800d15040c0703140142c0640d02c155281a00031812a103a81d05e400c0b011200d00c01540341a0040245c802401c16840350f181c0b00000200350517a501584581c1071404000401990b0340c8024030684 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 814152526 1250 814151276 814151297
    0x2070206031f0e1e0a0b040f020c010e120306040513081303060b060310061b020607050a0605240108220b01031707030915030e03030c0a080105090403050304200d050a12 74
    0x79140d22540c44c686086201044c0c1c0b600055070000d03000c4240d80a5210f400d04115512103842940030b4490034403081c00a001410420003041e8850800c0030304940a40d20800c000f89c000e0a280d045250842655041c101001d02d10b5180c529094110321035402900050050400c140110740c0074102660000301d813034500d1820100c0080c081e0518501c070304800c1c06048465a22095000c5242c840160b070003511441c0c1d190440d140094030b941c24414115121440c003070200d0500400311004550300411100c210415040240043d5002800241402c0c000310f111301c8894500006c141d440c10303050707114501105003541149090381c41c24003062541341c2504814410300c40840d5000741d0020403242442d141d8400ca2030f10306000c6020f0014003d00c659548400401d028119814400404040442d0b07511090326076280c0c030030040c0b580380a0343c1c058001801400030501182a427001218503401b0300c101c80071002d0b030020114008882922098402d0f4000c503603128140071100304030004500c0d540c5801c800c0407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 814153776 1250 814152526 814152541
    0x120d120f060e0703050402040b0a0b07050106091b051305040926130509100308040305071715010902031305010e0c01080f01080703140102130f0510030b0f060c0102070206031f0e 78
    0x540d4000c000d80f00b019158030100c0c05544440e4000b1f0000d00c005041520043d8440701000280e92104104607040e610b094000a501c545a214056030100c01c40c0c0c007203500c14407030403040b14240c01c10141c640b440301520070001050355452182004c1030344180541c0c622050704468101040700ea00240d025131100c1040282c400241c0154544240c074001c4551882c1c40c0c44840c50841814440c2d00000e02c6003200042c007005010b00080c2d40e0045480008120352031000091055417034561400f501000700c1100c10061140f003000e0f80195602100681c0410244002a1101d6003507c04082070020242c00550303400c43c0079607101c2d01059002460b060030010035407410b12500c1d41c4006920001e0081c0c003900d60000c4280b0420340485e100002002031000f8029114120070041c0416481418800c02d014007050386064024014416003000c020480d4010403003d005100c0c140d480003040182c995820003026006a591307402840c094000b440400003100140d80d2001d1801f510fa8000c2031200c4070703a4003007142e807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 814155026 1250 814153776 814153799
    0xb06090f011503020f31030f060507120908310303030b0105070503070c1502060405070b03070207090213030c050d1235060114090904020f120d120f06 66
    0x1180c07200c2a10740b4101090500c11030007801040e0180c44180e000003641d49020180d0b580f00b9206c603196000c3e00d0303031100034a03c0ea40c0c01182d041c0702c01442c0071080c9a40c0008190a54040c580c01812400c100d03501d0102000300c541140c14528080703e0401000c500f03a10301c0c0c065060241907203189880303048190800c5843c1c00042c10b12a00c001020580c0392001c100e4103034400da0542c1c0e0b07620ba0080859031200d8032464080308009040c01400c41c000601c10748056400d1000403014003442d0482c002e000c0941c202a01018180d1004102c2020b40c070500f07100040f01c105034402400180303001c3d5140e80041d0700394900380c074000700f0a0748403500c80d880c580d4858020803a4000118032041e582c0c00c01c103215102c180742e40d162440030303002c00c0304c40305401d41405465100c0b00038405110f010241c0c3d4201c0519110008000c1a0107030304c3e03000381c11a400100250050802110050306414010701d4141c818981308cc0203443d05180703002500c00074442c0b00054051610301e01400b10100000c4006114850800600b682d9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 814156276 1250 814155026 814155029
    0x1005090714010c020f030115090501050306070503072f0d0215070216231002100c03270510021309110901080a020d062d090501050f3a0b06090f01 64
    0x10030160b8544802486e074095104881081501074a5410b02d5a00c0e000034009107000d105660007802114002810203101d00c0840740309030503c0e1207004611400c0012070256481c621007014800590010402160108002e5864070161130380c020825510030040c41d01c0549005070005055500084030010810034544403603054072418440031103000510000b0040d0465000210745d003241c92a85091310140e4045480d130150251044103100525080340b040f0200c80d191301680c20040751403c4403001500361100e02c4500ca600035000c13101002034490b11003080380e021480c0c2c060481d043c10b40801446405d0f000c0d42c010129030301c3c0f01c5c6040c64a144006000484014400f600003580050310384000c3d040c3c3d40c40740c00034084aa10400c0d0100c089264031803038482c280303110710f001103034110f00103508540360280d6410b943d00030b04002c042482001c14003022003070000780c10503000c0c0400131203052500485e2203030b018141e0396001d4010f04201402c00c910100e60190900c1d018000d46c10810031070400040e5000d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 814157526 1250 814156276 814156279
    0xc0e030a1208071e110c0d0b13020d060c0215070c030228050f01020a1205010b040614070611040e1f03030f030e150103020f0306010e190605031005090714010c02 71
    0x90240e035009022030301e202c05090f030400200c0b1444002040d0680c441041014017800358100c0d00860311034003c00030445551034000b00002d5480c0300252445030a03540b001380c143d1010700801d54048084d0303155411f440160315813000680c480400a42c00c252407a1600381c2120550419002ea4282c03510002c2d12a410071001d04030340440007524401d51204c2c01076001d0b4058102c41500c00e80700740960041e004c0d40c0040d040c400060100042c45010404e41e101e11812a142c0200c1e1707d01c0c00340341030800c0e14500314070881d8940e0030300140318040119500b402107582403441022190341c1c8030308119641c84107080207440c80a00d00d0f10700c00a91003a41917600088107498140c208010070341c004080c110090104030003413240c24018643c040d0202e420900700c140c1030720720841d021041445e5560034182d0360740d000d205950100c003055000c1032000591250784144035504001c04600d1a07214400b10389040c5040000050980ea00c1c8200711082406002200152030b00362401286605044002460ba000015029 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 814158776 1250 814157526 814157537
    0x812070c080d181a0f070f0e0d0f2103050f01151110020c0f0f0303060303030112020609120d0207080c0a0b031008011b0207090207080d0f110c010c0e030a12 69
    0x30300d10003d410110414250b4031007880341201c1814544034083e1042540c15440c0c042e08200401c1c20103020346070740c03155403590350f0310381c8048600c0404201c48601c00741015a2920342e00c5d101c01010a43e42004266000000420070741c80c403400040c0101143e03c0141041000e1814400602c00703400d014102d14216503851030b0010440810710145410003c050040f00302d03072807000508070b40788080800e146103901001d1056501c1c0d03482c07180207070382c407131008640d01c42e496001000140680181c031090780d04500e001400741418000400003003611240f850f0742e8180340c0c1c0d0042c0c4a0034550759040055101401c26440601480c030200800f240c143c440e036004038112444044009608841603065400c000d01914009210071303030706180144811916805554010301803000c0106083c521402242c02c0c1030340c032032801440c0c516045070580040c5601c00c2e600500c1034507031400f41c07007645121b0b000e42055245040005034000d81d460003e005000044480742c0a40c0041792010042051922212001c0202d410f00c07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 814160026 1250 814158776 814158791
    0xc14011d120f030a02010e061803090907090902070614180327040606050a0f0f0801090906090b0703020904141501050703020a080a02060a0f02070f030f030204030606030812070c080d 80
    0x2068142292180d2840083c400400c030070056940c150801c4041c1e050003c03d0f04c80035200c20031411500860f00c5044a1540d10410000c040d41c205656507130fa010209181010b41c00781c4544054069912000003540d00076280c0c020a5080c07410b00010f03a0b00200005110440010602c900f40c1d00d0340140c840d04500199407000c40da16502e42c118034022401c1004104010240e10b5400141841d04554103c4e000103800703c0b034655446004502031041c0c5403958484410aa10b032482100150103840780c03c549058541301114000b50441d0b80c014002d00d556200540c803680d4000c148804c40c3e0040a600d00003001500074004e840d4102400f9014400003840d103940d40b2521814180e291090803403000f40750f400000784140d510366000ca5514001c4803d10701c10701003885010f0301402a0300803d200075010000410114001034020314003220840060700303002d41482da17245c5440046812035401500e05460000791859012048800194410103600303050844065a441e665090f009000c03410a0050741c0e02c08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 814161276 1250 814160026 814160059
    0x8010902130608180a05061503030a080411130c0e03010b0f061605030c1002030402010905010305010e070315050a030f050d03020327120f09011d10050d0204120c14011d 74
    0xb50f284a403004c84d0200d0b03120308404d2030021f40e640002c0303411011401024801700001d260200c12079044500076a1100b550b901c0f07584421072942d5a025010ba0301c6488040c07450410327034440c05010b500900d580c4076181e0007868101807509403032176141d246200700c51ba549805c00d944d96a0080d2148505500003288001c03c5a00d02a451881001c8000340c4520850000f5103440095400440c8203034800c1c1c2c2e44803469661400150300f40d071028050900c18424000c009840316100b580314001031303100308251407840f9580f40c011590440c1180c1055880038040c442c40414800b040203118a902000d2400314910300c0c00d0b40040c01c440810304a0355203502d035414042101c41104120a10b404007011409a0b5144240c103031720303045d590000705134602143e0f15448a01c41800404844482c0c4000a482040b201c2d030b0604089038180c1c030080e1584040f40d42444003207095600300142d44880c610a040040e0712a00703148080c40705901481c07078641081407820f440313002001d1101505400c1c060999001924110501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 814162526 1250 814161276 814161301
    0x80d030b06071a0403030f05040201080a0e1c0207080f07060504031403040e070e0f032b0c080c1501080309030a0b090309091f09090803010e090312070f08010902130608 74
    0x8402802000320a003c1c0070701c0c0030b5030304400d600071482500c041020084045041042d00c0c0704880c047c1c04140d508000a20b0300c8070316080b417414a6980410748a0200b98521071002149100a0340b00040e4031511090000c01d0040003426200e005400c01061502e2424000801c00d2046010041030209141c40c80c080e000c00c00c00070f89020740801d80c103d13182850300110041c100c8410010082c0300b0303c108142c00c07980f410045103c3c803010071540e04211140302001c2c40300f80241c1e642880e010400c5199406080840c0c100b1340070f001001070f10f401905c0306500c107401801060006820051035600b04000c20001513900143e4042d4241c1c1c01040040340f40d9480c18103500714010080b1480d0490440303010841f65401c2c3c03070954448640c40044060310385407914019411100c4400008140c40b1040006014004201c14640c0d4400d201e403003101e10302555180b15280c01e000544804011400400111018030b0b00044001e002d010003400450030301180c50300d2116446002e07c40e2100b480000c001048401d00400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 814163776 1250 814162526 814162537
    0x6161d100c0b010602061512060106030203090c0402160b01061b0312240812090a03110d140105060901060804032106080111071203050402131a041b0e0901080d030b06 73
    0x181c02e6030000c1da501d44010f525400c040700d0880c0700079030206002400e8036054642e02c0103002c000c030041c003250b802c0c46015402540060090040307403003861034103419641c2d50700003005082103000032a01c80300369601e441c0b2100e040682040c0c0c00d00011140d2482c56920300c041060203d5010f00c0d04800844040703400b030000300003565566484501605041e41c010b80b40d0010312080b6803000e01101c0720035810021038820703070040c100c60541c840307190078003080450440282c042c07a00e0030003003c9102c10318665454030034024100b03501e00c406e039448004000e140c0c030706036035103500600d47d40c00c1581c072501c0d195400a002c08008c45c011001140d0118921940f412641c2c441e1002d001404000c0048100c1006402c05e1a044560101c03901c2254003450383c880d5101e4050030b1b00866028020700300c080031368102d42000c1c10070a00586120115002c0d11003050b1344d14080d03070f010034141480e00c2150791511500100301e04a40031500b0300485400e0010001a2400144848098078520340000e00d140c01c2c000040081c4a0f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 814165026 1250 814163776 814163783
    0x60209041401060e12070609050d0215070b011a0322050c12030d0b0a0f0b0a0c1509020306060d1e050a020a0b040e1807030b0c0d0c0206161d100c 64
    0x69000200b681504444c0c1640d04c0c01c3c003200d10701c3d05024007071011580d4510a0081d81d00042a050b41004507007170180000c00854402428410680c04a00c101c54154201c100250b80021821004000c0d00d50f610810781401d010349251a80b442c0780410840681c2c13012003000b036407540d420000c00800c2c860306024440c0c4104000b071070059000307a010401c907929000294282240342c0340050078040e91a000c00b541c000c4503030740c49030482540d10300800414540c01c0628802c007070240c2c038115030340050401101c401c0c01d072025240000c4c0d5980e25006061070b0040041919000e11040d0b00150003144408017400c80f28404480441c1c4980e804e0b10b44030b814154044402508981c04081c08941c6c1600e00000d48256844042480c5a1350f44a00c2100d0000c205040301e200c4135080800180302161300c0207083c0f5440641800701d285004010304102003101c0c041115000180c020b070040c8807180403800c40d01c0095550601c0c11000030100840c1b9400054a1890800e100d0041c0e2001d0410041c040c120442c9510340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 814166276 1250 814165026 814165061
    0x913050c1b1c0206060f0406030b07030c09080109050a030906020109020d1104090819030e06040c140f1c060b06090306012607090b0a1a0d050c16110f1c06020904 71
    0x40c2c154040d50b1110b090321304902c1048802c45540e1541064840c450889801c40c58190054a481c50180e0040c8038a52440082060030840412f421909000f00c1031014800c50003004000c026040041c403003403c80e0041c00441e41841e40904c05039540082002c045a08000c00410004920b000030f002031451140050030505d02107442d00c0946042c04214404c1e580c02c2d01c0a104001c40300340101e480710011500240340c0100c1300030034031480103900000c00b0103d50241c05501c1080d020000204405000d80c104920310401e20041010040c041c001e00c0521030058074014105040352001a4442105005400b03800030898200380c2141c86d100340004a0140040550300f1a07034484120320040c20301c80075000e020b2500305500003048815200301802d904003401303a0908201c0c41c0411840a884040e00e0400d451600f800046e042d1103205005007000c0344070303048450b048000c3d0810310018568110f4800d03ca07504403c07401d180e010340e00c403000d65085e41c8a6801a5280000000100280034040aa44e0b0390700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 814167526 1250 814166276 814166323
    0x5071407111c03090f050a23190e180f1005090a0b090f010c0507230f060702070f09060503030f07030909020d0b010e0301091106070c09110913050c1b 66
    0x5800404c642c0985880f001031003040c07a140c1082c008921918451020007a45a0301c4040b0b22070f4010310340d103030300120090502030034410441840e0b9a160003a00b0648150302c1403414030882c480f040800320940b11a21000e041340445825040740c0310610000401505521803000540c841000c4c812140c11a034012000034450910102c142d603038440ca140ca5200b2503203456517551b9024010b03010b540c0040e0307214010b000c1100d500070b0140c082c0101800e110129104005400640442c00d1020b240b16041907030041c203440e803805590440101056100680d01481e143d0184070075200070040302c030340607040c1c0042542da04030340c45d044594101580c001c400f094030125485c1d6410b0344542104074819800d07079406100c09900300805003250103140d0018005040c00e0790040d0b0300e003445009480d034140540c40301414180e9442c0c0b00000e4a0b154129030501140000ba059054505090b0411100c90b405e8010005850708152148940c13080102090b0b4090310010240031f0180200000c02000200180003640324 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 814168776 1250 814167526 814167533
    0x1c140604050c090702010908030a0c110a150b010924020f07080c010f0e0310050601020a0f05010506031c0e090a0f0f0917180906010e030a140105071407111c 69
    0x5003281c410b19441940d14402091155105000c2d088101e0340000c0d06501d107494580d0000d008040075480d0406101d21044042001c0c81c0502c030b0350b10148e001e0803020490007410309000f0125407112003054148150100140f10403240840b5045c1304403041d4036504e45410044509a00e81400c03045100843d11030001c01140c00c0801040851131100207807207005800e9000300c0b01faa51074604511550f01503106910303150107002181c00040d00004180107aa50003c0c20ba1180c8480c42c3e80d0301800c1c2d4417a91100f0600082c0c4c01c0800003280362081014804414440e81c090003085040c1001d503031881035030304401003202c03040190701640a0040c41d4408000c01d4110003d4680a4980000250340c19070014180070702c0707584254120b580c0100002c41250b0b0f6880302030204280b0001c003400c0641044004041210170383c500b00040c118040c0100c502c2605c181c0455011030039204014401010025850b00c1811029481d5060b03c4030349601c080035120403e000c1340451401420341c04520810b540c000e40c440d051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 814170026 1250 814168776 814168783
    0x405070303020d03020906090d0602130b031008060402100e01120f0b04050a0209010e0d1103070623070209040b060d0605131e12080a02040308030a0b03100b1c14060405 74
    0xc480c401c1e000c3c0d514015007041d054049005440c3d03d0741d0000c07010003d9022500d00030380c8070021980301e2500142008852034440c0404810798008514122002040c4490034000c080010010503260b801407459203455404180c3d08408240307c3c40c02c3c0140c40d0300d1843c80740c0c020411810a201003203020030001856100c11400b9000b50301045014600c0e10700410815000c5000322611150180c403001c000b01000400e104a85c0f041220981d010f121140e43c0442c01d80d41805118014160f580d103001c0456009400c503101011001f808400400d0100b05a400580703617007150541c0f00d03400000c100250760300c04010940c03494040074000c1215181208225200346c514000e01c007010702a648040d001c000b445680c03030034640d140c0b40250001c440c006205842500c9101401d0340031448501c05420310b5034aa8502841d90000e4450042e0552074240c0a01c2078102041180c6e0b1125603902c0600502e0b080710007140010300030004c200800704071483d20b84140700e080d0141494140150040310358518203070800544 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 814171276 1250 814170026 814170029
    0x31005040201170c0a1b0f0b0709060c050c060f070c0321020f0303011a070c08010b0405130b190204030b01030b0604050c0f03010b0a1101050411090903180d1109040507 74
    0x1182285100c420b80032100310007107103d414010440c41c608007001c001511024121844008001070300311846c0e0018142d0790403070a08030300c03580103c0701500f4004c3e80a0841c9490f070b001078041110650305240818000180c4c0500e00f4819900b141d620255004426120b11031480e0203845080c0381d1800008104008020720b0400505200e07a8201740180081281c840c0c0701c04004030000d6109000510404c0e060400548181134004a03080c608003156560904103d05580000042c3e5911a4111007500749400381e0360707000c044202e0100c241d03100c556421040001c003601e840000c50701400b2100c0c0303074070317480e030491f0040c0d5005014140c540d0303542e00d46401c00c0d00084400307e00a60a1a0104580243c10010345541c03403480c0900c9400d507800c04c90400c0c0c1641010154604110004411540701c4100b032289500980c05440c003daa140c2182090040e4841e000c1e21041290f40304004c5d45009074000848074030290003c0703070313805044c181c0c0d4201101014283e94a040c5d00081c004140420440002401c50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 814172526 1250 814171276 814171279
    0x31e2001020c0337141507030b03031204080d1d120a020a03081906090f14011d15061204060b15040902030403021e0a0302070b25110310050402 63
    0x80d40d07642028141520742c000c001400b00d081c0c0e00c50716040242c3d0b0313804400b0011032880b6007209010721103544401d80d02090404c07030040c00fa001840e02c15002d0b8240b040081e0720500500341400200152030100b541c5c3e10030400381084210405000c0ba0400c10036008440c2100d1281d00240501c2f028070451244142c060300500c40e8500c100d40c2200c084c020048296549140b01e80c01130085141192029140e1890091421070000b00c1d011b1441c10500c040e100380000313060b401000092407080c1154034001c5416610700320303070040e25500041005000026680c070f185a00c1030440b00703242d01c4004100c000801d08040a40c0c0c00036020800c80784055162000b644a180509010b01c03618402906122046034124800a4400000c11044c09101c0c256002180c01500c24411500080380c0d40c4150400c00250226081140d003042c0c3c810f2040c141c0c1001408064000c0e44841e03403512605480041605145844544280704500900c80a200322100ea44141c0d640240690381107400b012160b500030b010844049 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 814173776 1250 814172526 814172533
    0x7120204080c03190506060d08130321030603050607050a0318050a0c0905070804030f0e0a080c01091a07060e1f061502010506030607121e06140118031e200102 70
    0x4c0d001038443c2e01008004581090140000381c0b240000d0100c0500700381c03002d0340e69840070000e0f881c86c403da04010340011406022100d4038501012924500048140c600d40109820040c042c40424004200c040c1c004200d130030807580c2ca0134800c4003903016000d0800c0700c468162080e82d07000103201c00801e40959952140501c46803a54071030604100710741082d02c9040008442100040019004421a02c080c5000382443c52004042200141c00440c00e504803030215088808081c03aa560080604006000c601028400d24000050152104c0c0580c8802601442d1900100f0307402d40c0c424404450f2011416240d4803003c00002090009405188581682140500140c100403481881001e01a52006001d804661030b101c1003110b80c5107000d4500c51800741d80d6a0015401807041c40c80d444141c02c52480451118500307200144802018030003207060001901b005441c0720080601801600da005015281e8039405c1e01d4000c2800ca502c013001046048440c1c402c3c031350030740d01c031540c82d40070202642203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 814175026 1250 814173776 814173793
    0x5041103010918111504090e100f0b01170421050408100605030c01081b0d0510050f010c0b040c2324070204020705030d1e05010605090d0b07120204080c03 68
    0x403820300d03a4800000d00030100103e11300a10346044580d008210b030b11200101e040a807541131800c1100e00300d904829180e4000181408810440e00807c100318071210300401000305d0100000c2c2180a140319000c00803603a0031b00080400c503034101b800c004100401003064a42d1081c0d04064039582c0140100382c0d03107118140d40f0150401d000e00842c82901d90240241040e000364400540d03007440f028002c4072050004800413441c00303000d0f00140582c0c422090307001c5080d0905001c494401445c44d00300e10302a01944c41c89844a90700030b040f4000c0c10345d0260420546540f80d04021072405840c2d042501d540c0c4a020382c002d50104844660b008400044455002e824400302e2480c034040d01303609142000e41024489000545050342c0500314190045c4162450810700030201c90440d200c0c5800300303c1c001190706468040c1e800a10509002d0b010a003091480c001074000010715003001441c0040107104044c001a105a01c54264441c0303078000614195103e03506d444119440d0617010003014003d204140c0c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 814176276 1250 814175026 814175051
    0x714030d030e100213320402070f120f120c02031e1207080412180b161e05060a0b010518010e030d021b010801030c060309050a0b010e190b01090618050411030109 71
    0x5940f04055441306c400c402c13100e116414400a500003103019607450003044104004a800e03400d0010202c217a9683e01260022000f801824008540442e130080501d4800310800f0140c0000031a90300701320296000b124200e20940100051103a50807250303100d20f20400b0321081540001103540114452084d420f202c20401d98211404d102d071700621001c115132990704000e030740c2c1c0110040c510a42145d01c420400c0410307483d0746040001c010070440100711982814001e0240c14010780c0c0e0080811030090101000c8800001c219005104004511240805d80c030301c0581e0044101e0780070742030054152540c0f821010006034a034114220f6440e007501a00502402a40c82421107506890380594010011810a10210000c0074070301000c841520800503010080b90311601001c1c02402c10302c0e03d42c42c0d5031405103014058002c030220710098080c00c040800300306a8000c000441a18502d140001480209000301c080d0303443c1d10f0380040d030094034110380e805031070045400079030603501d610000340400210f07001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 814177526 1250 814176276 814176329
    0x50703050303070f181701060306110c0d081302130902031c020d02070f1e08071503060b0f0313110d050102090901050f090a020c16060309050714030d030e100213 71
    0x844802460301c8a440030b1000c01106c8003d400e1040f020f0000140164907950ba140403625031003c0c4414168001c98404040350042041ca0915441d80c0f0b8081c12505000a07040200400090004c1c0b081202002c072400002207980620000350300141254510250040b4004118155804180045c0500030400c80d42034000501c9604549400c411701400c58a49140401600b1200403001d000200b08240016070607400c000e60300c0540a91003100050300441c1c500a0200e900c6c0340e00182c1948c00034402404040041c0301683e92052078090041744081a42c60002103070917100c4100d987c4207405170900c905002056000d03004001b000d0f075a84506980362020480c1c0010300f6403540e03901c44007000000b40f00c080e560b00900fa1740c075400c200f1a4041c02c020019024103d006800c4800002c0d51240c2103810710808111040080201c0c0c10b19440703880310303400420f8031404a005c01c841419101c250002c0e03400790801c400c030142d020b207080440d02c4d0407041441030128501803040b00c07004a000d0303441c2404000e405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 814178776 1250 814177526 814177547
    0x30d0207030f0e19051c02150a090e1312120f0207022b260412031803020303090f03240412030c05161121100b0303040e0c0403050703050303070f 64
    0xb14800da1503d0328005c20803880402d480d000490350361900000c40010384400c1100240300c000d1080040e220300d81c180c00240003010b541d000c804541c41c005d007808014291800c2e00848103030040000511020b518201340d03403e42c1c043c81003034115883e140d1110300c1c400c07003940030b05401071003101c4490401001040d45107840d042c041c043d854601c80c5c4500ca40c00240340c0010340610b43c0d4a541e18005102207401c500e2903c0c1c125501c038000c2c0c9807520b100781040650008260a2105003401a604a030342580c0109903031740203000401d03010310044655000c0b565420000300718040848148408111005a202c1c50381c090250350460313846500a650ba07480c14024003a507000c004407640c940f400d0011081d0001354a19141c0425280750ba50304601c2e000b00c0c1c5901000840d10360000b603a9181107410759040d20b2400c1c2d0034801030050a440c102000030f075a50301204540440d1003810090010707441d807814024552040b5032000344544248a0000304103e00031010758403d110540b60100c1c4000f00c1442a12810407a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 814180026 1250 814178776 814178809
    0xe0108090607080402031009060914210d02090901030609020111120711010504051c05120a080f1b1c0614060904050403120c09051504060206150102030d0207030f0e 72
    0x2040001d03001c030321405080d5401390005040b02c0507442e031020100101c6002c61800d07141c282e190300408081c00700c0ca64401800e07003014802410480c0001c090402c903244030840c5800032410015040c1d0169045805075000300d14010000e02e03203035950346005001080e1000c401ca000c54250041c0700850000491142440c070384180030305203000c026a41d905518502424440d0511205110104e0561120140c0d616203c502c852400001e0349107060581c80c0c811440c0641d100810200300c200b5683e5400541c441d080420926042c5040d240c219008640319050404c441c7e100c807011803403648507811041c000901d195054070403c0402d031902428400c41103001d205942001c4204540d14260419a200d143e1203070281c03030000d0717071503400c0c001c7da1098412900c4c90340c0008600720307070520181c0703010458001000207410400e0314040c54000003a40300d80b8001c107a00c0304108080c0000c44540d0081c0121400e00c50242e0b000c569494183c074028000583c0d0304c03000c0d03002035031103c40700041d8113100c010107428099 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 814181276 1250 814180026 814180033
    0x80307021e090a0e030409021209060f06010c0f020a12080a090801061d070e060d0c0e0306060901121a07050c011503050c040908040b0c0601030219210f0c080d0e010809 74
    0x354241d40902804d5482040c985601c0104800030f1040304e03500c081c280d501c2085018940c1802c0041000d440c0c14000f4001c9680302d440e240601c4510f0303030800440c0440903440220760a16540600000f06c2035000d81d0301030741380541e80da241d031403c0012040040c4241e4490341c59010481c0c2c1c891000a00702d42c114000c49034603180d980202046040801403045d8881c002c0e00d441c0c0c81201e03601002c80e1094100c5040345041d25112010042190b8201d6058032445d034065004003010315003800084d0300d80c0c1c010312500224840ba00102803d00000d000307040c0030546100d0301c0d080c50b4188500c008200ba808540104c2c515440c1400100c0c2c030344104c0c0c203490200c07504000282806180f070381c2000004c2a858104480014007040000342c054a160064009545640c1c0582070661540c01401461020741c0c60400a0461004080c49102e52002d40c0074180035a2089401c1508507500c4c01c1222084a0302028220706480000064405c0000556114170045940c9051540000780c0054641d0442560818400d41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 814182526 1250 814181276 814181281
    0x3140f060307030f1e03050a020c09100b0307020a0611030105090c12070302090319060204030b060d200609060c160909030e040209010513120c050d03080a0c03020c07080307021e09 79
    0x40340004c20700d003158000ca14201d010700c02002c40d034038100d18801c801c902080f0040b44001e840c42d011722602001c000140d5450240d49416200d0b00d81c001302034040e01d040c026020011800c414800c0200d00310032684442c00b0080c42c1c0e07043c2291203150300309225041c410490800060450004c040c1a500d80b103001c00061303001a194803209a0103034200b044d1040e0103200d004454130801c0d40e04045451001d002e07100050b0307100d04500300705221020041442c0c0c0281922010440094045424642411052000420525007040000382d0724824541c0701c2d5888a03010030340d04031b04100450502c40a016030021403610315030360300c401c0003a17441414018011404004c60f16096081a03001040800c034149002e91600d000c8000a000841884e0442032020b0039110307009041180340d81500c409003e007140c8541132a00a41c1c1c0042a509005211014031911f0760100e03000700d400794040d20b898000300c102350ba0415071610411a681c0c3c1014000b84d01c90300400e0b1100240ca455105100c0c08400041d041400a5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 814183776 1250 814182526 814182533
    0x80c070e0f0115030e1c180e0a0e03090a060309020105040504020f0d05060f06071704050405070f03061d0a09111f0311030912130305070e0106031d0304260a0303140f06030703 77
    0x20031552016000f4403212005054002c05d80a1f504000b0381b407054aa6180f90400c010500c0c1110381c4004000103581c0100300118043d554410b20008454043c42c0115208040c0e200485160080f03901564100c0d0011a801898010304000b0700b102c0c04c0c510030100903686c0d880e01080b44205041c0209a0808810400340000c6180d020250000101c100515450180e40d030011404a46088481000107007034100070400041c2d050203400000c220303202d088941418010b140c00c88680000d45100711690b507644200081205400c80800640b41c0105041c90414070646a0014800c0802c80c00c00028601074005000301c0c1c00e0021f80340200161002050055000362140086a012980310380d5840034208000001070010400d85001c0e042c0c5003070600701540b42860250503500074400c1d00801c4d2500d80b5180155110000c166000c542c150202e8051004082c40085c00145469440181c10300810046805240d050342000c01c040c18000d00307900843e13542c2c01d0070108401041d07070030b01c2e8182c100c581c1c1000407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 814185026 1250 814183776 814183813
    0x51c1406120c09130b1506031909020409050607030606090308040e0714180f030303091002090105070203010212042603060112181208091207080c070e0f0115030e 71
    0xc014620071074000c0e04000700043c81000301100c11004040c4840c50b08020002c40900240d00250700d4080d807a51840140c001411a0000400c45201c401c0c0e074080316500f483c40c41d00204030054015200f00003031205414510784440301140c40320040307410b02100203a15403080f1486000c42e60800c0c402401c21b800c004c280e07244030300090041010080b07000424440c244620004010600010b0300341d01001105c0014410f031941c0664529110760001c0c001c000c2c0c0c1c0e007000304403141441c0303c81100583e0749881c80d0040e1218000d070800650158400304400072068699200c13680074034012960b41110180200807100c40003030b6501c14126101c400e00100d0120350203000301c95103180000f040410340644103003201c00d807400140010b40c0c00c0c0c20700d8054907101d10340002d4010303046040b40000c2c02070014070302820403061003250b00003021110300250281d9140c0c0d05100076806020f0501814615040400c01e41416100a0141d0301184c0c0b101408004410300a21510400f00c204001510442d15030310080082c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 814186276 1250 814185026 814185049
    0xc0c030f0512040f0806150d030f1101020a1701050f150f07060908070209090106060c2901080f011b091701090204050106020d021626010e0a03051c1406 67
    0x4141c400e441c201802c079820030340070f070000d01a0354200d0036000d46407040c141e14001001c0c04040f903c0080742c00c03040b55500c82d0801e010b4002c0c0c0606060080a1034a4011150080964000d00c1c1e90b51020403040e844543c8160307a91045012b5030107450499882d10208004c0041c24600c0e1603200034000d5504000416203400b8001e20b0340b00c0354116003040c0d02c94a48206448400204442603840044d00c00218034222100c15001282ca000070800142085805081c0e0300740482c010382110803155000319181d610140100c54150184505046940d44949442c3c0e03690f4003036110b403419400c2c140d0640b00b182200340f040d80b14040580d40c030b80c00a440c00400141c0480c00e0140925955241e882c444007603215400b440f40200305680c010000000030240090412140541000c0c1d04089580e04009049403a400d5000f40d6290f65503c000d03940a15510318010329108072005441c0c01503030300031410325400601905d202c0c55101103880e0121444403c280c205c454002c0d0300b00c0f20b1001100411550300340401c0170034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 814187526 1250 814186276 814186283
    0x111032b020706021204031b0b010506090f120a03020f2806140c04090f020c0c0f011206030305070201112d0f030d05061f021f090b070306150c0c030f 66
    0x600d071507900d0700c0f008140c0c0d0102d1180490841940140300406a001e80c42920b41c04489001c00c0c4081440e550f0030310a04030601c03401e40300d09004665156950388500410001103c0203000804c80342890400a403180400d8400344c026000343c0c803030040c601902040d000c20750144031111056070388005402c10380c079403410075041c5da500c1e940c1c40030740c0070110101c0485030142c1e03d551000d0351036900c0e003a1301c90242c1d02e641c0f40d0542c0c05401807180c0c090b00000000c02c1004100d080f214002652050340c0121031200401903c09a10341c1000f8002060503005070080c6500c500030390380c0d610009460303030030543c0d240702d00d881101c05030f01400960104c030715000024802c0e0703c4502c01542e0040915440b181d2460b003210060000195490301400030510f0a150a08640c2d525541d0000e0008440e07803010303499101c85401d0600715000d080e0400e8820100358018448103502ca10f1485850426140c001d0040c80a4043c1c224115007141c518080c1e50300a4150760a01c9511202007075095080d0f680322180c000d136650085 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 814188776 1250 814187526 814187531
    0x30a080a2114010e06030a0b0a0f02070b010b1908152e0503100f080607080a060906030b100501110a0222290108060627100e0111032b 59
    0x30520580745000d1003a080e11081200307605941011300307900c40780e0b00107000c040c0300c1c1d4083d201e0000001e0440313903910b600c8241c0400020b4a060207000040192095040080094500c08004900840c41801806034680f1245242010300d0390030100b9115082c003641e00e4034034207100055030f0360303a031403e11412010740180b000480c1000001030600084260000325040c0031980100421940c21208103940c0001d00c4011a14414a4600350343c168480c08050003c9007000208400510700c1201c58000380c008160070724041000c5562800c14000828041d1580481c05a40d14400603141d0310a250301202000780001520005940d40d00704007246002c2c1c9884031000641b401e2003c500b100d00c0c420322840701220b6107108034a8450181400c0342c85070700828581403128a905108144c0c42e004150390000e00e0140100040d0b491031208403011480c16918541c4c0001e4800b00309103990741c0854984013401c82078031118244d0200800300c580f40e001d0310400c00c540030052106004020011020b0000780f04560100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 814190026 1250 814188776 814188827
    0x405101515210b12030f161403030a020d05160801090b010c0212030a0210060f090e1617010c08010b0f03070917011b050a02070b090310180203010506030a080a 70
    0x31050568503070290000c8507941e90401520f81c0c14050f401000e0540b03a00055403402084580c500709500850781c05007501000c1103485002c01900c0b41101400384040c00843e41c81c0e252511003031010b0b41c0045110303441141046c000c100140803d060525015001d130315030092507828038192000802c1c010703581c14108100090010302589445110904810040014642d11501020060b141005451001d40302e6441c15004000c1041e400103010180c800583e404036604140300b41107032510010241d00000a8a41500016003d292010392070601036001c0003880260b20861081e11104002d1242c103030001c03000c0005044003990342e07004540c85801801d0800c81203440740e0340301c40d00310007a00a804860303540e44800ca46206420320700075000c0596240c030a1400d18000750094644200f8402d241c96158049102804e594082c08408031041d60b1200401459406803110100d0310380a000c2a40694130300404510315040114090002c1504903400c5494804400f2084505070201e0f00c405203021030200341c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 814191276 1250 814190026 814190057
    0x2a031c050d05190e061e100b0309010b0a0b0f18060f160519020d200316050906030105040b0c03040302120d0c0305010501050915031008030408060405101515 69
    0x20940521000f4540c0401e82601d0380d0310404481c40d00b0364011861788500308003c002c1d40c06401400d0000006140c070685a181d01154968a03140c0e50480c10414001104002240c03005501184d03010350200c0711a80c1316640ca0317400340360074031400500b5030500c20100610320300508255408120500e0103043c81d450300c0d03030070b00e8000d10a4004070300e101c000303105103901101032180801c00c1000c81089600c2c01d5060018641c0043d0000c028000000d100340c0421124400e4041400503007040c0c0c00c000b90540d46402c0d2140e00e12010b030381160207098403c0f9111804a0b0742c500741441400d119903030003185418541c1350301b04c1400d045c5d04001c004400b18403c03c000b2402c00c03082400a8000b100c0e03540c10110398000c001700060113443c0c05800c404c0c1045420300c40800184da491440d1a43c003d14842c0b22540ca07198400200070288842d0801c0020348800a03001078003045c002a524812070084094884012150014805643c0c9040c4d80e000c9100c0d4040b4148141442c910150110580c2410500d150740c26910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 814192526 1250 814191276 814191281
    0x90c0e06190815090f040c0b040f052205011707080c03210d0c17061f0f030e15011d01060504060e040b040501080c01020f0105190b0616052a031c050d 66
    0x407540786445c9a210144010003041c21105405801c1011003e4100383c02c0050366034141d04140705944c4900480d205001c40405081c07446a000c181d0010203006960f141c07001d2181e8013a0003004610284075030080042c40c02d0300170441c403450050040142003031407903002500810543c0000c510004003030400044c0701c2000c4511035130440c201291903004900810790244035040c1c2c0020318071400b988401c0d221105100f400d00140c170618505091654145589020880040200b100030310164401c001000828a00713484040d41241c4115005414000029442000c8850b084c401c00000c03900510040c420280690710345198107201800024140801c2c5000606551080c1d11420f42ca420401e810011942c0c10f000c0045100703070b0500280181c1c10300040c0141e034455001d2440d13a101d59a5030010b662980e0f400120385148080c41e10043d40c0106508000751a1441d543d46943c040c070301e4a424a41843c0000003080232041c00030050448101040a82d90110b1034400841e410004204266100b06c0541d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 814193776 1250 814192526 814192531
    0xd0e0d120908030c01050412211a0d0614060307061e03020c100c0f1b080d140a14100509181c0c061116060b0d020901090c0e0619081509 60
    0x100c000310310781c202402c01c0d81c009200c11748c260040041c0c01d0b0218911861042e4003103403845906030700040e901d8440f00c410743c4403850705c2c00131031f4040094591031040c0141c0c1e41110280b50708c40700e0440160f451b00010159070300c80610a86000c03a1540d030300d48090246030702d69400851107600b4050318040054584504250407010382a1404e0703514004007400c10782c0041d0a90b001d800900b0001c102e40c480350211800605100300081141d40d00003030b10580c21442e42c015414002100104501e5424140b000ca0003404660107100641e0030002c0c00070703984914050401e822100c015011a295403a034000740031080ca8a102c4081c0c2c148507a4015040c907400e02d050301f40031607006076030790400c00125140440030366607041000441d045090040c1d4010700054106130080e240c0c0040c000410140c03101c04079803001d8607031401a500008032400010521500e40000b200c20341c0541e500c10030b11401c002041907034000c450404a6081d80d0301c40d03a5103034900428407107030003015000100040c50805c1c4001891042d08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 814195026 1250 814193776 814193797
    0xc0b10050d0b16080705090625030c0b070206040f080c01060807080322062007051c1101030c1e020a0510020a02070f1203030c050d1109030d0e0d12090803 68
    0x54410841801d143c5003960080d281c283c5003408950030310000082450003940b8003e4498070002075000009010a61060030501c1136010407a40412a414040c00340c03030381d18809031401003084000641c00c0d8808103101d803223103070b2120320300075007043e10b4030303441144c2e0001c03da40001b41d0340e40c00d80895900400c12000c1d000f044640021a6240310a9034026000c007800f030822160186280006d00265400403034441d43d01451065245000d0720810030300e443c02c00940d02540e0054a410700d1044120301ea1000a10480e0048440038a0305601c0b03401181100c000b035441d1000140072044051031007418220b61030f4124258812140d100d001905c0c0c41c1c0c2402c1580744030440d9141d0010314441c42c0c0d42c0510020008000c41d503035003500c45103019909044843d42040c024201540e608009001e1030141061380c000120005042281007100414001282d100303001d814485c3c45110f21941041c1e03c94841a00ca142000e801014805003030341d03400220101021000d82444110b001c0843c1600c020809000110038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 814196276 1250 814195026 814195043
    0x9120c010e0102010504020303120907331b1103070305010f050f0106080c0f0a0903060c030e010f020c0c040b01020a050a050d18060203030f060a05060f090406080d0c0b10050d 77
    0x4009001400c00d000c4414414196410981000003580d80070082e945101c0f54005080e0b115903400801c0c0307040c08142d030401c1d419100c1d1803003c2e00c01103060b81840c810200d070100444828a5582030240d6a0000b00c222440090300f0908507100015403200c18480943d80180445260035143e07994942500c1801980c0c0c84000c2d0754004101304d03280d6070405207004100a0420041ea401c161052600c0c80c41a810448140200013481000c0d01c1d2040c0f810740000c58206004001240c1100801006850101544032581d801c00c28990786200c198030899001c8190040281440161801440041c05000400c035040d07024200309030740490700a0004100030349c4100090306940d5400c04000d401d140500751042005c00b048003050140703070380000c1280d401c000004c19040d169600d4400160381c40b01580c011a402c074001082d82e000303403015800a401020421142440b0b030540303548405903a204006044c1001891031010200400c8210890395040300c080d04620040c1900c1c0c1c00819071424401801302d44016 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 814197526 1250 814196276 814196293
    0x250501110414090a02120f070e121c05160b04050c0406030c0e0a050403050702190f08010e060c190f0509030a1217010302090601052b090c0f0b1e0912 66
    0x1d428050680c0c0044d2500b011400c0200c01055560710780d10040075810441054000304031164010443c5001104009001007946100c1400a585504a404d40340800511310140b07507103058056010341d049840e4040d4010300000c1d060703ca41c0e00f25040540b00b17440c035009030300c014006500c42d4011200550b000d42d207520f6807185016543c01211400a010455061a26040c0000281e00c0400c5a0300e90b6012107800441c040c41109103024000300b540720b46d901c1a805c803000203401c071040d00050514944103040c1c1e205a42d400389150168443d10b80020307402c079a0f0b079549018060190125240d12400c5203840f80c05d00718000003081c03421a40040a40380000031006440445502107003000d017003140c041100c200d5514513804642c1c9104050702e03850502c0404160b40c00c3d8269000c65003040d02070200003400050050340516001840b8203030068620244100340400c5141055004104450500c035502e490000b540d80c1c0040444019500300005c81c00410640d013440c0e903481010121000c0d9080a03207001c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 814198776 1250 814197526 814197529
    0xa090e040f0b010605030103110618181005010c05063c0402040f02191407021f0e030607020601140609130507080112030c02040b012601030204060b250501110414 71
    0x1801c05134828030130090100014000101c4038024400587d4080d03807040d8980490140704083e8640f40c65485400120100c41c00e506003054031102c8d40641c1960b0720880d05d442d2208011281981c10240182480d070112021035222000d51030f880280041d86000c8001c07501103602c6050310450300501c01d14100346048140300940c6000d100e04905124102c10441c0382203a1000c04a40e0340501011020901070603500118500b400d540c1102d80056005040d220b1455110724582c40c9184880000700c0001c250200031040c9090010759940224007640040103aa80381c22040c5000740410001030f90440e40501c0922015207074000c05903e0003400c3c81000c1010302d04210000c00b40a0b059002c450018002d45d40c4001194121408002154066030701103030300c0409c50b0040c0e60f1400c02c1d841c4988640d001c0b01e000000740c113010381064180c900c00c94091150603526044c8404602a01d4080b4001c01c4503400c0400c01c5500d40840c259201d1311550001c00d1009560315010445d811540c8041841440c00690720210b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 814200026 1250 814198776 814198793
    0x1403030403030b0d1e02010207091503060506091e060a0f03060515190b090604030c0e040311160b0a12050109060305120c0601030f0f08182706060a090e040f 69
    0x142d403019112820b03803040949542075011038070003429000014441d422410b40e4230030322070f101c082c040c190000c0c0116200c2c00308000c042c0509100642c0c009161001040311807800041c00c0b070041d200701004820f0310408088108481e90040e00566104003030100008501c51281c4143d0011400b94200150a00d00103041c541e0188001545511980c204406002d8100c6488200c40135500c4094699860b42e00e4100421010310964201034403040c0b1400c800550b903140140240d1041d4403d0352100034075180144507543e107414015180d01080e4480f1000d01412010354050044020340789480502907594002c204102c9800b078102c1c0c1220f41d110a41401406020070000f4410000c0155442c5060078110400e611000180401000c10034480244002d000c1010400503103190401143e59454070072090601c040c000419806001c1c95500100301c1801c5500d61601010031003901d418000c96403a5000c228040d4030144264017800400000403440d171a05442c2e0500c0b85205510120300c0a40504010a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 814201276 1250 814200026 814200041
    0x70510090209070c0b01060e130603140d05041a0c0102120702010614090907090b1306060503010609090b030a060e03040e0906010303090e01080a03030911090712150605070206090d140303040303 85
    0x51010004e01440001d04103a00241190b81c149405900181c607031000810072050f2102c03ea03056410100c0100034003e60b02c1500840c240388508966451101c0c040c2a5910b0140e0b1141c01d00001c1d0701c019022481840710010078007010a40001403030301365030701c05140e032040c015190200182c2d55050184408442050180c0c002c40e4121a400d14615260f08000d03a12032103030051900302601d92070221031503220802500e000c0401c04c20107004840d1a8107005003180c0091145d0b00010340d9404000079050103d120340600484060b000e45100c0781503456400c060000e0041035211b900c420880000d0382144448418050000c08015280c107505d1424020008051500b203080710794120340041000c0600007400c403c50a506003804100e0300d1a90610705d2510038271884060b0040840030800111310341c40b8219101d503504c160410410320444c0d01c4c6070500300040c1d015130b80108600700f011001500c2c000c8050200d010004040c9071070001d4542e903603040340f240c5c0100045141d1010062000b09a014000c040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 814202526 1250 814201276 814201291
    0xe01050a05090a020a260307060b09060105070f060b010e0411030405160501211506210209010e0f0604031e060f0c090326030903180414160203070510090209 69
    0x8140100344d000204041e18031b01c50b80e528019080d901c84805500c1c0d03d040b17041041e40c2403d46e61500600e003800809405100e8480d0b00c20b0030944c001038610740c0603c0503a481641c209051003450f00d00c50390f90100410004c00b1050500006540c0402c1b076030380361b020789000000314081c15502c1c1d0501d8070342240b40c6901d410021290846240c3d00b40110b0f680f240c4140350504002c0140d010642901b030303002c002096020300103000304106000104001e600a944603400903085503c8903646004900454128092181101c0c002030b82c1c2c48003803045281030055407602140092616203416601c0da2500d00f03032640000741e0300701031000585480a00c456403040c0c0b510000045401d00482c2080500185065110700000700f000d05158005404490249211010400428a51580c900381178411030b503a81c000055a00ea5030302c104020031000c1c10b05004140c8016100300d0300045d2601c8180c601d029906c8403100013411484248800801b08204000c83c41d41c40c0c0c050300002400c040c040c01480003042000b0b003540c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 814203776 1250 814202526 814202533
    0xc01020c060f0606270d060b18010e1803041206051b0f0d090503160b190204380f190318020108070207030c0f1419050907030f0e01050a0509 62
    0x203555182ca200312815032070103c000c40c0b0501ea0728102450030a07401003c4035003180c000d0446c0410013140354040791684008070b8408000c003900b03200074203c0d02024003648000b6501d403000b241c104413402c0e50710186081d904c001c1d0380c18180c95905015040459000542d80b01d51568144180d040c507151a103d0503101680c502882e101c011800180b051048103070000380c0507a24000381c0248035080c01a13803007109100d0192004103601e0300700741c5218201917401440281800310303180280c2000e03100321402c40f101e1070004040300f03101c020107070000540c04d0b8007002103802111100419003001c10007884100d50704402180c41e042a580c150314204561141d140505140c51071034110040c00c0c80d030303c010313441e42403800140340c0da0382201c07c901f0074525078402060300f03101860100300740d504c0e089844103407180e203000d000c91025103400700b148403400000c401c40001040d65061143d814038040e42540500700d0704020412101c0c008044040312042d0f0035440140c0d540b2014000308204074007a060b0003c441038000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 814205026 1250 814203776 814203781
    0x12030c2312010501111f0b03010e0a02091305150a11220e072715030504060f110304060906200703030e060c160c1706010f0f060801060f03090501020c01020c060f 71
    0x20391b5200400740d50003818091540d8801c0d11480e45400c1449034290190007881140d041c0d01c0715030380c0d540e4105800c0340b04004c04000542c1101185824041054004008104516091075100201c900180411207180d0b198411100009a00001040f400d29042415040441c9907015504071031195005050245012002e0082c0c9607480481400c90b02940103010240c20760105e04040b109045030b002caa80664a042e02400d0355800d80d10891043d40108410301c4450301403484d61b000c440f600c0445040391a02400410081401d56001ca84070381d2040e00f0000b020b680070400d03c0792010800300701901d0074600148020406605000c2d40e52071003207040c020704050400030300040381c90091000c4404900d00026041041c0005611150000d1698403a072206616044403d0394071380c4004d001e00034101c202030780000b902c91366003801d010841e00c2913a11040b6a0b401c05104481c40108041c02c8400c142d103400c86503000c21780070b2006040d1a01d00c90001039581c1000d408003030070914000c14581c0e0079416a000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 814206276 1250 814205026 814205057
    0x10819080d0b0f040e0c0a0f0b300103080912010b010914040204030605010f0f1a1c0b0306010b04081009080901030506032e0605040912030c2312010501 67
    0x550303941c05006030000c00c2d818540004203c000000c24103c41e881030800d03200200701200404c048000003c20b03101d030503c15440321041c0911246610415280304410400310024004c1d5200318050114a26800191940c1100f20310b04501400c0c3c0040d100607c0015034500756180c288c2170b055808090400900084400d900003030280d809031301c80c401003090b51030a014850340e1150304981c051503105d1010011542c459101091805850181501826250304040313107114040300500001031442c07400070b04d400d00043e00c0d8518524000038070440b845d00d0301410a00ca990a000d164043c0998500d0941c54515110020389012640c108000483e480d00d000540802c01c514100c50580c00300b824042415160080821f20b045888070240c03040b09602d920b81c40c038850b0400665008444401018400784e1384900c20082101c405850041ca4400c0c85038004041e24080d400603850041d09083c05454984402110342e08003e01c0b94030b5241c3c550f40050442c000d0030603503005501518007868556142d806050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 814207526 1250 814206276 814206293
    0x305182a100206060f01050c030c010501030c051e01030f0216030305070915050904050919050a02180f39030604110c07140301020d02180f0f30070e010819 68
    0x804c828000e550b410401c0a160b40100221102d90196004aa5590b074513644031034004d1000f800b003200c1c5c140d6080f00c00541c0d031400c1d8010f0f4002d500404034024030114000700541c02084091010440580c0a11410000154880717024201c0e80c003e440105032450580f80060604c3c68503080000c501318041041c11260b54003d00f40c44907240d06660000c2c032a251109158503150004005c8518100d550100c0f00402c04e02244400100703100303a0f05680b1155076009102c4d506841200d1034207444030f558000440c1c2c83e001e040340040c226038140c100c5854090421015010a050350501240703100b00005000650078540b0806812100d1014140c0c00c003480803242e141c44160318822010000000c50401480b95002c0d4100c0745107032801c000455517907a000e11090070038111030304500c0c410b00100c0c407d20094280030084041d03900d030050104803241641200004000c04048501c480740c0c0d4200c50160b825681044400003134060550410390541c5481e076090720709070f0001c2c40101204600280680002e602c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 814208633 1107 814207526 814207531
    0x221060c0a03050a0c050d0926070203060c0c0d0807021510060206060a08100c03090b0f06030d0212070b150904060506040b0406050a060305182a100206 67
    0x10b507082d0b404440c00c42c000745c800702d10204464400b0312055400840d05911400d0940c40900c00c3c8183c0058521310314013040031019000038140d0039403404103c602c0d4480321001c0901e1070800700c00c40d02c039140c80540203000144400d41000c07034805030080c815200600e05002c2001d40030300d004881c07121900010310900001d8052800401c00ca406c0001700507080d502d0241c02043c05040c0e4055034001016100000700405541340242c40004888481060040c0030f80c0e076003064903040850425041c110b116007070106542c800802000d020b00100d0613a100940c1000b9048070955400558080c07030000410400e034000708580401003009095884980202c0d4260713800c2044a4542080c4000c4501c140105903201803600f20412000f4400d07040107510141d5100e03440c50301203520f41c007245054148031002d602d200c240601240f0340d180070b903488902d0000c2140d03040c441c0c40c500000030f912441d01 = true := by decide +kernel

theorem cover : BRFrame.Cov 814028776 814208633 := by
  have h0 := BRFrame.cov_init 814028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 814028776 ≤ n) (h2 : n < 814208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
