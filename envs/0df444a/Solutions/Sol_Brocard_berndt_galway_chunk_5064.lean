-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:37:27.101038+00:00
-- url     : https://prove2.me/submissions/78bdf4d8-fa7d-4444-bd11-acdd00d925b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 910611510 ≤ n < 910791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 910612760 1250 910611510 910611529
    0xb0a0e061801060504020412121b080702181312020c030718060602010e1207020d0c090c14040503070b07080c03030f01030606081507050306190b09010809010c0e011d 73
    0x1028003051a607022100c64024410314004000a0300c2c01d40c24507281036081c0c0301c18403541c03601074442c0740c0040d0924100361003101038400c10801c0c00490743d8003500c0b9080052071904001030072802060060b90000e59008203081c80c40c4038010344190030a09040139a60520002038003100c19003580304000151171196000d00880c00508407104a100314900030342841c0081d00c2d0642d20400541e45000109203400c0c00110769080ca0240c1480003a50b0350142d0700c0410014021742030041c26500201c7c1011590440300e0304601052905503403a110303041c01c0c0b00103421642c4582d108039603045c0d101c1c0000700800706d0124068202d0034080d288560506d0780b4a5130060565100300c41c06190005403200603c2040703013038405d076005888550000c1c0020b10802e001150195005003c04050000c00300c002441940c501c071010348200041010401c913599a2071621246402658507140420416400105239010503c98044480c000c1c1e41c500341800f4101005549002000449040c4030000c7c1e020005203803070300d0300030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 910614010 1250 910612760 910612771
    0x20903010e100c200a030f02100606030e3706020d0614030f01020f0d0f18420c05041a0301030209010e060f280e100b03010e040b0a0e06 60
    0xb19050220b000f00428800e910440305007041c415500b2840b48440004806081903850300300801c0b000c000c4981a894641c42c3c0003104031081c03c1150226035991306030007441d1300201e5402120b02da4840800003410080190304410440240c8540080007008682c8051a05501981005250080051200e4280d5030190040d0b411409403000c07115032400c0800c0104008141e0134021420700000161108170340c49242c07130001d903591300c2d0100c00b000d000b41d13607020a0b481c0c00120301c0303e04030726407619044040b40c048111031501034420062041d00e504201400302030014035040d81200e103803840380c00e0400510050450200304501804007190300c000fa01051800c00310030131460368880d031441c4100215400305030485004c6002d040e09100c03813a119040c0e080280482165000340e0007101641400002c030300c40c1400559000000030018171840700c19032090103110043d104005464507092414070b07038402880742a40d888030344000900803e81c0040c01e590001b0860a000c100a141c4d107810b10700d0720701706658 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 910615260 1250 910614010 910614043
    0x30a0b04180302060609100e060105090d150b0102030a09030206030403091503141320041e0f0b0f09150d0f05241308031504020714120319020903010e 66
    0x40701024160104456540440105c07042122843c0c2105c0048101c0350b14401c821040c0e8507080803990342c1e0702800c141c0c4e207610390241c0b194000e401e19041051402c4407416102c2d10030b92800b0721034555544044100c46070540244c840700c101d10700e15030a010b41a4401401601081802e010128940000740d0b03204d140000d5542e40854840d96a5452008541024280548103e10710044200003002c254511046a940d811029240c10024011034080d1010013005520210040607111480c01554840488a074040030200840910141881051066111690b80c401c1030303200014040c2c00120151866210302400c1c0384449555550740d5624828406070490721900140300000a40e030500c5400d0700081c1c800807446450741007003200b680410f08010400f03072080800000083d50912408102200d580e00034004566850580c02c04802d0f4080000c3c094166000d4a0040d03484a400c0601340e82c0182003200c2c0390800100c140e45400007d61085c1c1859400d0f5480d51000708201d02d040c400820485030200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 910616510 1250 910615260 910615301
    0x304080a031823010e06030a0c020709020705071203050409060306020a110c0a060518030a1202060c0909010605090d02030604060e07210602131a0712050307020a0206030a0b04 77
    0x500904001c1e9040ca401c0340c10b99825100b000681c8151410704011020701c4640600c0f49050720048402440c100c00703064000d80000180591030419034480b41e0030b24071b56421b58001a8882007605c050b84100c0c0000782c140c0c0c0c001c00041c0440d0302c8900042c00580d119003000c505e00303a642d40c0f03c9001d6a603d944142c848650121b01c5201c115004a080b03e03100c42c1c0c14010303003c40360741c030400546801e0a41c002d4008204000c16949208400b01412a01c501002402c136004103040d440c10051002030740e50740d43c0041c0200000305100b10020001d851402c1c400400c1c40f18641c4c01d00b80c04a8242c7c020500c55030b8824041005e080c00343c4c030b060140c03034001e41c015000440c4810043c81c00603d82290f545c00516198138165034103404001d0340760300d01046a40088096900c603018000e846021010740c00220700404421100185400d4850090540302d12841000b801c010640301c00f66502d0104445060140c4c0281d1004001450802c1c01546d010301091000500508400013090454841325880c020086060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 910617760 1250 910616510 910616513
    0x16060218010c030801060f050408030c010c03110310050904020d141c09030b060d0f140f070e191d1f0509030319020901030f1e0501050108270f0304080a 67
    0xc520030800d840c02800c00381142d0405075001001c450741441201c00b08040002009502482282240e004281c00700c21261604800089103000b810503080c4074000c0391902405240000300c020039284100e4081c0c3d5403080141c0b07080b00b4404802c030001d004a074445002459a40042c041c0b4203810b0082b41070100600e0ba1142d011040404481403814640038080d804d0010400a04400315040d8131407822340d08101c404055181c0101c041c01c0a6400070311401c084c0011a000020006039400130300e0001085590700c030b548114000d00c01c2c01c140d074040144e6095601c1181c2040c400e030000b03152584445200001d00c0311000400782007061040c451032155605c003010424038540382c02031540084400c0051803440c10140004581c102140c1c1084800c0e64021508107016070007a80003001c0c210b5418010b2081120442c00034014686a0b080001024548800805d041d4441e0441ca881021051056041104090003100c1c00250141e4401d50900c02c0207403c40f104001880904010038801006084071040e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 910619010 1250 910617760 910617787
    0x60307030b090c0c101d0307030f0e040506060412020307081b04150b090114190905030d08070f0c0f080703080414011104030b22050c0f0103230903160602 68
    0xd800a100500d05116200744c910010410b070024510b028800a00164150f8400a8092451030390408601002c40c902041c10340042000c290b09505a550311040700c07111007048102d80e81640c4264011100744800d008140c2c442443e026264001012118200d50703800440c0c0ca444501106220b10902c054444c80460030103009440342880e207400070f11243c0e410107001c00018021a59114108000340c804200400032080854000300104c15240540b04280980540108482d01c00c140c024450b4032108c0e500c0900c2601c00d54090f0325240d40d030034010140c1410031225031250781c030300382c0311207a411840c4000030b5207000c024101c152003611030724090314060070900c454000c41035000141e64184031a881d03e5040150441d01541ea11a60741ca61684601241302e0801d941c95039101880070104500d2024401d0000d80d880911800f160214402c201982c0110143c90501c005003400407040042003481020303034140f090b840352158044030304052400d007031860300c8030541070196070043d13000030b00103144200e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 910620260 1250 910619010 910619029
    0x9040e0705011704020f0d08370314010527130302010617060c1c05041a091207060e0111070f0507060f0503180304090c1e0e0a140f060307030b 63
    0x18541000b0f00d4949034020401e100c283e29041445100f150b42c5200402c020329050b2064400b5246e90703100201c00401500c980903824080a20110202e01d002c0c8554a10070301812440192401d07044c0c1700d83c0d28110500c150140aaa40400c44440300c10f04803809010f4118802e100c0c140b090313900304007103555040c0030b400c50308107070094885120f590448000c8071100007002ea400c28500c04401eaa0303110692020b201d500f038141c101d641d1207070900080c041801200f00c0043c48001a07852005440c5e140d80c1203056807001440408030b503600c400d0080b580810015484102c40b551404004202d201c2003d07401807480c0c0c00345600b1211402d01c11916024402c08203e0343c009403003a402d00c19246044014094000c0c0001820410328410748002c10301454002e00944004020700001030200824920005d8074101c110300992903408030070900d01801c42d1003480562905603000e0103143c400390510f802141014050120726401210060310038100c0d48400c0001d40c0300c0c2881d60390004151f0310001c1003109101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 910621510 1250 910620260 910620287
    0x150604081b060f0c370807031e0e040f020301050307090b150f21040201141602030f15061c02090406020f1603120e1c09050604080d0206090d1d01030209040e070501 72
    0x1060480c5d8601500c4040c0403100160800822904c4200500d0210b81104030485d40410700c44140400c0500c860b0020500454020708550a2143d850f00c0c45c401e00c1240803d200f00e40d0300d42d00050007044681e1440c1e00403400840c01400e10082120341c1c108200865201585c1c401560f60005031700390352160750486401d5100900400003215003800e800080c07122050b00a407800000d40002d60044500703030300d01a1411142d020b01521444200304c030807180c40d682035030a120350015084001030744a18100380c0782c80d454007807040000b29002c1d680d001e0140c4010000c10450f12680d0800039140703942480000382c501c0400d100710a0302010380500d4000c01c200b01e040700405555040012001c1c286401181c522054241b40c0641c06001c4440138044401c1c1380207a0040350050320001d40031038007103070200749684100000c1c2c00311140c54454081055803120400074000000d0030642d1407400440064042c0c3e690058149005420000140c0000d81140c0c4404000c51003a071141d4001c00c020f5070066624454503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 910622760 1250 910621510 910621573
    0x10f050d060812031e150f061b010b03190213050702120c010209120d1409030c040f0905010e0f07030605250909050c040e0118150e150604081b060f0c 66
    0x203003030011540300c17240310801203030b4481c0c1f40841d0b155045171915004d403240c0310001c041c1ea803c0031010303405140c0200310341304182c0d029006036404600420103080e10340d2a000c1e07018001820900b0010200703001407401801c52001c601803120b0000340040188090215481c241000580ea03403803000c2040b00da01c181a03a101d002c0d4005903100b5011640195103031800700c0c50701c1c82d01072761140f034032000a051411031640385034050b241144548010051350700000303400b48242d00070030203140004c0f04280e5400e43c204007080c0c241e00c000c20900c0003800741d403c115004010b104541e5003841c1c14203405000c000e2200d000200084000e10208070344009402000d0b08030800406e25131600d42420300700960548140075000c0250001c2042c2c3c2d00380110748e80311642004094000c880525201c88414a08080503102c00007451340103013164401e03141c4442140c04960501d80241080e0203218107801814845c520210b0744000700b400b8082e0407441010081c9045032401001c2c3c0b03820740c10100b0b0b2040a60743c403c00107124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 910624010 1250 910622760 910622821
    0x7030318060f080a0902060f21060d1e0309050a09052e030b061c050307031d090103021e06030711060c0c06010e1f030f03030507020c010f050d06081203 67
    0x1480c0e0861410f0743c111101c1200410752000b6800030600314451040d00c0e40c500440001d44842240031011030b1400c0c1d007201404921140c0f00c9200b08000d4046442d405061002c1c44a500300308040d4800c2e1001c0c082e0b110f81411240365959000066003010780da4044043c0d1600c54040021001019107000d00c403100110150050300c2280d038902c04d00660078080100780180080c00300b09039985800a1b0041100b00b00b0b03c14100c00090700d8650307204d4010b40011800f00704076200c0320304c41c4880107500c117000101c00351245446030720715000c005e032805116508100c50700518000c503000352189001035214a40070340390110b40640101d6010700d00f501c01080c0080320b40c814001c00d002000082640c0341141c040c0e400e503000c907450725800c481e011103204419540340781c401280081000300214181c1c004131300945041013159243c03101030ba1200030704600240040ca448840300502800b40d070240020101079a4006045500c50251503d8409c0d0014086440c941c04010043e0300b00a48001c810b11200609581c003c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 910625260 1250 910624010 910624037
    0x2b0f020703030f0c0f050c072606010807030f0209060418060203090c01080f0c0f1303111c020a061b020a030648050c1603060f090206120a06080703031806 68
    0x3501800d80038820400c400011f014044c1c050030050007000d030510b100c1101c4c04200f1601c10340f24100310140c4480140c040d28000155240010805900316504a8401400c0401380d43c01c1040039440200b107070307a10651351106042c1c000304114100c0b00040c8111801607170b030f0400750300c0c0e82d06e4500d520600342d0402042108100d18850340700407058000c0f5041054a4a52050303500d13441e498040d0031420381000c040398500000740400c0c00f1741e02c2d458910950b074007858804100d010400c10014020082d4002c108400c040050600c00e03d400c40b81024424032040303020100d40d00088080c0060342c8107440e0740d030700c580455124410600f0b8203998541d01e0a00340702402c1184401c0d03200484049038482c070180c0c0a2500d0b401043c011422120070603e03000a4819040390141030301003000003801b094500c249070120700456005103210f030006a40e0001c0199003000c1220070070a0695100404803050703661141000181d400040060001948c82602c600801c0d0b450501070012010300ea500080c104882c0c0300102c0e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 910626510 1250 910625260 910625267
    0x105030c1302030703110d090317090c1201020906120f0106110a03111e0d27091503050706020312060a140108070c052d0c01052b0f020703030f0c 64
    0x204071407500e03040962603560700705007070b4020402d0f480603080e500c40008498217480e805030700c048807a503c2a181c1c200c07030140c802c0941c0c0000e102240c25400c540d0103003000140519090300725001108110002628208406012078000e4201001d49242c8820344001d02403d0062103419070b0141001f4640303240003201006100740d440d40b0400d4081d0501141d0700a0340d40110b0f0901c0b200000045a10114507005448001d03039903a01c00e00841c4030b000901c0820b0401030000d261000344400002008030400850426046100400380c50090280e2480100400000103a00f03210305d900130850303030b005162180d200b41c4030f5298409000b04100d110b140800300c20b201412100340290700080c800c0c03814044966410500340c60700820210082c0142c45802d0b849800d1203110410700130800faa05500c2048401820402030340e96121209160200310280000c004503140d00714240c2c083c0c0045841c040700c141701800c01c0400c603041c001140304880e40003e80c1106246d090f003d00286003a05d1941041014168030005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 910627760 1250 910626510 910626529
    0x60c01091106071e080c1902030628020901020f0111040e152209150e070602070311010309020d060507020d03060e13060c030b03060108070503070806090d0c080f0d0608060105030c 79
    0x1074030324458000c1c01001d104101d0159028003100008070348004681c00c86c50f1f01d404178082000ca1181c401c80c070004a00300220100c40e0000b014000030344140d0366601c01c41c003010f5041000542c2c1180b20b0300d40b9902081c40d09002c1c20ba00e881d20010300da580c960900e280d00107926001007038008a00091803081519490311039a01c0d814041280c12400902c0c20700c6e42c3c0002900c0c000303102600542c501211406403a00c964401d11f41800010200c4144980da1007003aa102c1142d0311029104048080c810082d80d4003940111442c148000d00d8030140c1c400c1ca07030324803003110401d8a00c000180d211200a110b00c6030944100c801501040655407001d240002c0c85085d8060b507048010316107500e401304800411b00035005070f41100e400505464103983c44211480e518007c42c440c06103e881048800a106000440e4850007901c02c80c0140c2070209840c0000d0324445003031102166405001c103c2e81d0094180040070b0001c0d0800c0d44000b04142c1d1074510320500c1c0a2040c1c006904c2900444040c1d038132075980c100035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 910629010 1250 910627760 910627793
    0x7060e04052211040b040b0f15130b0415030b09240303160b1005030a030528020c01030c141215040c1701060c1718060c0109110607 58
    0x41400e42d1240c0d003072411000122001c2c00d1444040311600100072655a1a848542c81504d0402c1020300510411041c1ca1212210b1703500200c1c0ca00c080c2055062491681d54602d158076200f519100b9044505d21841308240e200d089100808a018040703c0e10058259401016600d028080390800000180300d11802421109040070b8002c1402589140442036000c00000242078940700e80943d1507a502481040398112070442d01c42c0e0004e008ac00f074041058050f608058000d00303032041155800e0f550780c3d20141d0b00180c0001c08220040c40c40707104150800b1020000c3d0f0140401d05003141c009001c1c0c40c2003000c1101403262003401e800200c1c0040b42030301c0b800100b0250718500ba80713440b1019511242c1c0701c13005503081818142100365a580003510200c1c2450201100500d980c0d992000b1038416110700300c010480010399006250a03440310029000200040e000108246010000949283d00c014410075459440c0c2200c502480104080180b400c1c0c01070381e1052600e05650340d80180c0040d010170 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 910630260 1250 910629010 910629019
    0xf060b090c1225020c0406091109060c19120807211104050a0303091707060806040507020c040614031204140d031b08030f160212031f0b04061107060e 66
    0x3e030400c09112881c00c2c2c01c001d101c640c07080622141000a4803440c088500c103000301d081c01000601020140b02d072a11030207486400303500b420500000c01c034480e8001e105c0c0c0103840c440d501307000103900782141484052a100341c0300c2200365441e84001401044008160f6414801c0c1c0d2a111060204c2c416000340ca00d22082034006403c0084140e0f5031154010f035044290014580707100401010340040540e41074583c104059000041119103503030781c450907401000009481c00d800b01e0054145508240e411034558015145e010b540b00c0c002c14100d5145074041c42c11455a00320010050506003d00c0e0441410301c0700c2c00b480d007810311703441c03046c5044107000b45401490b01141183c00e16104040c5882d90300e10080d5080d03005131141c10180d0064106440105520040c0d50216060701c1d4001d20b000400980e5070080d004000420031070a505400040c00c0e55503452544040c81c0e07070140c807038540d0310103041c001030903540300c41c10504002c155407029454000c0a5110072000d00c00b980c1c00c00085024040c007103c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 910631510 1250 910630260 910630297
    0x108041101050403050102042d1a0f0d0213060f09030b0f0603150f04121e030e0c03030409140601030501180e0102094207020402070503040b03040f060b090c 69
    0x10300403a01c2d0300c42d951001c0d065500c041004079001190120110354503145440504501221240481c042690742c881c020a130340415800c8003494600101812a8401e10309803141442020340603403043e6805012202e8180ba05004284202034100c4400714400700c0702d103801b007100d9086948940f030004000d0042880c41c80000002042030b9800c008000b01e0005003880d0b18090b04004803013040e00e010541d011161507404107aa209000d115084055054402d0b210802c00b01c8110082a0300602602c451480d40d4020301d0325002150314104020030003010103140010f024440040b803244201d030050041c038101418407004010590780d800305140c190708400000616190441c80c070130b00a100702c10406070440741d00c4c0c16803003104c3c08480100400a0b420481880b5010050542d01c90030003501c8419076801d0300c28084070380981426406803a00c0b82c410300489181a450b0384120500b030b04100c600302c1d04185d402a1103410001d090203134180ea160113840d040d405040100c1c413640b882c02801c40740141707100760740c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 910632760 1250 910631510 910631543
    0x21250606140a0e09190f0218011401020303071704051002030c131703030117030c010912020618070b07020f0405131e020d030c0609020a080f0d05091503040c03060e0109060b040902010804 82
    0xb8081058203c1e1700030f04040804240120520b80d03c402482900000491441c422040cbe50010048038401c082c607a5508031404030840d044284003101400546080c0300e00300a400b44501c55200460060403806540b81d1566a5030a890f00007403c29002425001022003202404502c0041600d042d5052003813864090341c13241400d185035000d0702c8220b00340f03582044c50719010312401030204603401c1001e50070f44800342d4030300c0700380c000e5000c040e940c2e90401d604c6614201310340d10300f03640a480e00510042617034001c1a41d00c400a016250242e9904501100006401040240c0b04800c0032120480041001085000d41c001a51212500d600039090002803201d410030032a00b94004d2882c1070b4014001c5105c1ca0b107856407a50380302d407500c3c48e1000034460040300152160103207099400744d1070001d280c00565001040c2032103658201070011680752122607030200015109001d9420900d003120000551a41c607424803006441c201003030903004503d04405100541d9000140b0340c5e01c150054292120350404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 910634010 1250 910632760 910632773
    0x110405060702010e0d05010501351506010311120907050d050c1509040c030b0406080c031e0c030607030b03070e060d11270921250606140a0e0919 64
    0x5e488010034a519000011440001140d91280c031030b0781e081c602140c000f42c82c40001400040c80e1000c0c0340c40d9030203881060b40c060f006280c603e6118806140201e120b4110a102c1001e036000350310b0f4900110f10708410060600c0c41089030701c00421081b03a40b0b404062007615210740742c14400d6207050040d18608802c00025107204110303000040c1c050002c00c140540004024010041c80400c1d80c807803421710100046a03d00012000000362004014007024124101c0f1980c00c0001c00b0782006060003840c07010b0006980610003548a401e03a500d0108040c03401c0300806003840300607000782161034600024400151075a60b8642c1046030300c01030340c5101c1c2a600e030005405a0301050300380e070b24078407500c1d000d05002034608103540601042d40484501d40e030804c00b0140340d00ca00405441a00006001d40b04410142a01c01000101e1129103005100c1032901c03020181d5080350841e0490904e403101e04456810011040c0000307010140075071486080542200740c403011085001c1d40072450250380c90f802d1045 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 910635260 1250 910634010 910634029
    0xb0c01060f0303030f0b0a0513052509060f050a0905041508190b0915070c1106030115081003031d03120d0912030903021c0c0203010e03030109110405060702010e 71
    0x70602601214140d407860020003501002680324012800c00440707202d142000000441514002460421821003c101f0744005140c0100402d6241c06100304a05000254070221a0138103000d944100303406003066405040101d0005920081000c108403422070254446610002ea440072140401d40c14814002401e0010040d0407844160041c100210300380040c1c2d04500200314441c00030710b05141d4514034490f40761f04070104e032584403141e640b0000d440c0c2442388400c1c9015a00c50001c45003c0110500804d8454100341c001212034114290842c40c0703e0303041292035500610440d0340c4400c0b2801c40c0c0c0c00522045165a200340b540d00300410720030303465605000e00b40710b185805072601d0316605001d175900701502e000740d019035100c2051411a1001c520900070455041d030150000d1501e554080403c0c1d4610b40b1008070300007000070303240150740140d030b003801860701001a03600219242c0d4140300700d0204032900101c180e9114030013000204569151801036402c400e40900340103c050b50104080b40b061f12 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 910636510 1250 910635260 910635269
    0x1703070c150204140603090604030c141c08180d230c030405010f020d050306060f0403051507091203200715020a050c0a0b03041104020f0a021f060e010b0c0106 70
    0x3500a00d49280d0550b4064412150403050703194084070182c0c04d2090912041c0c4082c9801d0f002440090040790107251000c81c014454104108640e80d81d1440d00d040c903040303030301a56200721102d01104003194050407e90300300c0d014540b914401c199454400d80d483c003c1450090500c8002207611000000800c480d151743d100b10804240e80e15620703211680c5a0748035000c0c5a010170603030b03642003c1c1e42d8800079020402c4106500d50394a181c4551007080243d4011061601c4d03050010031000c40010420700840d40e00813234104135601d20313041c42c1b00e010b0124010341c0c210700601443e000241012941c0f00e154541032035140e0300f0180070030510b0030109043c50308540111100128040c08040b5055001802101c00f50088080c0c0300b04200300820016028510721070040e000030280041004034008201e540011140240010703d004440c20701015190400c0741182c025800802c0105003800c0020b205149802e4500d00810101d0f04064580010b00010f01941c0d0324002e000c2085482c25009510080281 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 910637760 1250 910636510 910636523
    0x1c0c1a0603210912150106050906030703090c1a09040f0b0607060e1c090602070e04150b0a0f0b040e0109052e090204090204061d0307050f1302041205191703070c 71
    0x81c001401c15603880581e4865020300205c0c40c0c0c00000e00f14410030548100e50301c020800c51668860f058114040c00c8607070030a40f400d0f00310b035000181c640003039120b100340c940c0e00182d001c0d20341c500b04003004116248401d6100b415070425080910642d03440c030071101ca555101000140c42c400c5550040e20303152001906005030a01990071041540e04407981030f08071001d030303800c40c1e01d01e49d11040740e1310140342c1c20340b0024914041034240d0810721010b40c01040c03140c4000350440148607501c450100d1840501c0c0d0050403200d4000605101040d48071071094003600c0b0302801030006041103640c252a1102d40c003002d0400c110422107071403200282c01494002811741840a40d00c458031030051200950080c429000407a0381034004e041c068405035000044000000c000d00542071900061055034030703c5400c800da11001c1c1d070800203d6460184003070000b8001004007488450840e190941c80d0030780354060985409030000c0031b40e0008403e00204044044d114001c0c6450b80c03101001542c21002214009002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 910639010 1250 910637760 910637779
    0x190b0603040b0f090a0f03050d1404030509030d080c091908060a05070e09090619060b04120c170615040209090421091410021c0c1a06032109 62
    0x18024142d12550081ca103483d82400306440d4050810358442c10780000411021000155802280c05072002e4a803d040300f00003c18602108120703014080b008690480201d100450b00f0300c490f050400c00841000d050303040880142c1460700d60300849000340c1191a204148110300000040070781c0701458010030b0040200d6a0394104510079001804084070510000707500c00014007038a140c0407c0340c500031080940a04140d49803a5449c140104c48150b0b142d0511752544400203910748000020401070000d1190345d440e050301440e140d220398481e83d004403486040c50034401030060020030400e8021148a1554104019002c0450064044ca40b00c05a001c0c100004010a0080b01d244000311000094100c0c0340f1201110015240040f150081010b544101489051581130164510142d412980103d880300e2250310b01551088030500100c1002600145442d0104204045841808005260a0402d0340b03015030100e039072414020844180311190f801100c0d00703400c403081103507a81240030340000c05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 910640260 1250 910639010 910639013
    0x2030c0a03080a1b0e190b04030309090c0503010b0d020304030e0a0801050f161d0d060c051206030703030f03050714030a1a0d050c010c06022505011401060206190b060304 75
    0x49158103c40d00754403941001d80c001e03100022581c0301c1d03400b01c0858407003103100d01d01c01003400380c80c1e201111814110818000040740c43e00720200548020f40c42552001c50b0541031009800940d0040010101405002c1c00144009a80b22043e15044829414016240d07525400c04440030740401c0703119600f020030090046003000c019080144140710b16404030101d40c07280319001e10781c07400301900c0b040000e0815260342e090a4604000e0782c200000200600c00300d0015845480490310f06600d10004200009a1080030103110394a2581c8001c0403006014100e00c0c5840103410314924500000400d1b55074000078a1043c0504140c1c441e030004206003645078034140c0825030044c90311105810a02c1d140c000340172a58600103c040444982c4180501403411007a00155010300c88410119051502405040c81c40c0c11044840c0300b119824866030440411281445800c4844012108502407491001440b0315600010200d8206444181d4000c103038526078411001042c8000016502031800805d000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 910641510 1250 910640260 910640267
    0x200304020d0c0504060f090c08060a1509031502030f0c03040f03050901050c0d1d150d0905120c060f01062d050403020406090b12061003030e010509090f01031b0e041202030c0a03 78
    0x1050710811482040800e41c1a641620120f00c200e03069503001e822002cbc02c0c800c44403032502840c103144140c1000d00c2916183c1c1d84040e02c51012454008009c0d501004005103203000c2d03181d5a400c80300c2c038409140f8504240d00c40c808801d0460038040c00740280010022100d91007541258001c5203044251a12404a48030041032174030b02c070029418405000c03c0504140ca8464075111072000c0b4075000e03e00d030011109440001e003001c0082030715503001c1c4000e5070341e06c00e65910041c0881c000040161213907145c42d02106898000682054080202c4525020f0315140c0920b045044410740c5c00c00113650040120701111f0710300c02c5070002904141807903400122020190070013040c550003150710b80381c40f001d03030340b03065603070f03600447d0040c103000028041040860b000c4e4001e40c1d85103c0624100e80382080b18404903c5040080d610008501c074400010424001190040313201c00400c12007500c407040c6040a0040520340162001e440f1923030740c116a09289008004845120080350305603482c0341d0785e034140038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 910642760 1250 910641510 910641539
    0x12060f2e0936110405091003021806040c0806010503070e1c03020c03010e01091a07090f06080405010c1125031b090e01140a0b04141306200304020d0c050406 69
    0x2107041c5003510420b000608507001d0b503a1100b141900b414285482d200c10054840750140070585000350301c0d4808409a12614152041e41401d008040e040c4d003040010701c07046400100024080080701400d100c410303a40308c0101c98000c4664940004610502000500b941400c450b4054145280d12043c100b0144c011540c0d6011801c224000c210040f8803400035803d07188a18001001400804503116203d01a90980b41d040601450001c00d035645440d070088a50742540c021070085003149042200f000303405d0103011100701451900180702c50084144030b9075003a19402c1c0d00f051000b0a00e2000c042c0d007500f50000c0040d50040e545500201c0125580a070480044c000c20340c07a542043c40101112405000b04066154010845111a650b02e000c4100511500750020741c400d0f100c103c0c182000103081c1e44240103885144071580014a149802421580030540c0a685078126400e030200e40d15007203098031742c000d4040e201134500f030301c462402010401e4541c10003a0700501c0c0203400701c2c00d00900a40d2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 910644010 1250 910642760 910642829
    0xc1e02070303080906070f080c0c010609140a11030610050c010f090308131a060316031118150d0c030c15031d0a111512060f2e09 57
    0xd14010b92151300031345803150001c45203840829000c0a4950f03005206991080d40302604200203414880340e82040e0382503959991025a03e661942039101c1c0c0d0701844550f0b96004984840100b20304c61a44506600d09d000050510f031050004880c0c0310301c40c2c0d01071750482c0d42a03000300c0d000300011090845060002d1400034070070b5000845900000300d41c41c49462001c0e17441900040c4001c080541e81a220401d100c00800b0160140906000c9944a0110b01c4100025512541103894400700c600180505c410b8030b90a40600c81e410903080c88010b44e00f400d110807200d0815141402d600e8417071304103800c1d01981948020080c0301d0446000170032850303075444c80400240c2683d080c04074081078603c2d90b01c0900024101c04887d00320104490010340c1d40f00780b2020500000e04070300c10b00c1040e0a2000c10075040300060148008010742080b150345000d280d8464940011960ba004a4085042620130030b1607015086420740500c107150140f9134095020a001010805150780740c50b4020400e040c401441103a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 910645260 1250 910644010 910644017
    0x90a170a09060c0b0103110a03050105070f030f060f09050406110f0405010e0d02100c15020a09050f040c080a020c190318090b030d1214040807110301110403060c1e02070303 76
    0x5000c9002c40c480c41100c1d081d9504503072070312083d07400c546901e55250412071030310f80c2c03125016800000191003801400d202d400ea0303403030700c1405c031000e03100181c191591130403103624652030f00c081848402415030300304090300c0c0d4200300010369645601d0b01c81e008280e04c07001c0c2441c1030008500b00c824500ca10300107206603042a2b951981d407000a09c24810300b80300509009500004a103880701c048d51142241e21081405202111031611441c10728600304d0340542691800264040c1041c00103050000c0c00000d00b03003082ea02040751030032b82440200240d0b0007030302e10549260005218820075800300014500d501015603003d2000c0d080f0b14015040c6c0c54a4094a291110000c1000074170064902c288002000041c01400440c81001c404441a03c031003a403c009041d6144964030481e481d20111520a6120b07200e02d036540d84c81f9041500100c54044035240c800c0e03040c02e0030316070500c8221090381d049170b074010b10109110b00c54185c1a2440c00203031105072032030181c42030050700b256400180c990460303000e0b49 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 910646510 1250 910645260 910645277
    0x1217040f0f18061a030403020a1b03021f020607121103340f0e030f060708060306100f381305030606062d0f0703090504020c0c0603090a170a 62
    0x4409040ea0f00921803607078040c6aa260b40003628500b031005550140c800e00c140c50304c5d5141540d4a11030341003914080d02907411201310600460401c40c181e220a8445280034481410b6000c40080d91014000e08a000300100f507081380d1110031060300040012412078200c16140c0c5064054088621079800745410120361003542900f40740941404041c0382c02c5140d54014440b034081c10103031001c001009030680c040c480c880d010103005c54140700003401218259940c0095040030381c1054a4507102820f424069102d99104006054000d00e641080710841c10f0005403c18042c002c1c0140032804400450010002e1140d25010307094880082500002d540351000446889905041c2c6d1004201c6000e50842d100f0441500310003166070490000000030603071801c0052444000040c0c50300080040618a50042220780415811a0540c8064142a2401c506055030401b0705c6036150100700e20540180703400004940c0c000801d20012450356000281068500010b0701021709652000320300c4c20010710f018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 910647760 1250 910646510 910646549
    0x605161403041a13050f0f010815040f1a030613022e020c03160b030a05040809060c0a031e0806090415090305041409010609180207150906060605041217040f0f 70
    0x44640100c0454060700387c0d10032030012801074410000c00340c040f020031034940c08911011381d15405900b01c206035028001c50040c1d5004586031075071300d200181502ca50000c0081003040d054900d2840b642a4040301c80381c5134003501d403a00d0701d80c1030a581c1d6203200c48801b40e040001560f80006400703084c0e050540c2100d10b03003900b86107000251881806410440441040462800c2c800d40d0000c980013801000ca0034a4407084000080c1c04e40c2c080b1065101d107410841c5e5001c2403640012807038642030481c50b544040640c03641401007465100030120343c0301d1808000400e09201c2d106540e04000307406050100412003040c02d0141c09900284202c0310620307010070b511240c13410032a8105040b102d07252152001581083c6c0720380a0601c001c554107421075400e01c8540045601e20103402480482c40100262508030b600b0b000742681c1540d088002841001c002c100520f183c07150581c164560044400d00a07941c504a000500c2d11640d8800348110780900350105103070603044107081c02c8480e00212440b180b20036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 910649010 1250 910647760 910647769
    0x16050f070b0108061f1805040c082410060c030507051c090e0109060623070204050a02090909070302030c0d06060f080715021c05090103140103060b0a0605161403041a1305 75
    0x2540220406e865444481551104c0e454010503086403058489100c0c45450341d031054a00700b040c07a00110030340008144c400c01c0000210280da0080c40e5564100c0d2041e007172120140c0f400c180380744024200000042c0074400d00000740000300c1c04042101370680c0880880c4402001f8450501a1b40c0410201c20000514070300b0910400b42150304a403107601d5054000058000b1000100350010501201001740c40c00580d00d034810a440382c1c1040d0710060315100010709000304044018115003c81e8801003060001d69000a00d2021000e400c81e4002010325207444e014029004944c030200d80340c40a400c3c0031841e19400b0510609903200380c07002c40700c01551480107ea803180d203d40102640c00383c0e800440300c0280300f18000c20f000745060502241680600300c80004910099100fa518696510002c4000b0318005940380002e0580346880b504100c101200c08500c2900c4420040c0b041c0c44124110208000901c01c2e0780c0140340914403d00c00005c0c000d5106001c1d8406028450000c59004020074035180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 910650260 1250 910649010 910649071
    0x2070e0402010f23190e03120d0603050102030a0506042409150506031006110c010e0d170a08090c01141206040e011d07050916050f070b010806 63
    0x1401204124251620740065540381c56165089040080c5404510349003108401d48140c1318559204041c3c0e02c284a000c1e800101840c0c110142c01c00050070403240c0c141d40c00003a80f01d00004480021680c510180f0700450003804c19030300081095002008201508090b40d001d28400c01c020741e014003845044485106101c01d0a910703000c1c0100c4030150510111001c1c3d44070000155098401040b810b840301d000580a4104480b0712006062006040c05a43e03404044440d07288440402004c0382c544880010b4a002152410103006907502602d00d0706210703c0d42c1094040058000280d5516444554000c040e036404175000d092500c9052206110355106401c108245c203140c81401e4185540d500e860f404840018291691007911880d4503074080000780b1411380440700f134282c500521401d28401ca42011502e40c80680300c0c80b981d20401c40803074040100b0300b0400301e4070b00d41550788141a051300c03039160081000151031810325030000320703d002d40000e06034040e440a880c00d01d8480541046a01c0450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 910651510 1250 910650260 910650269
    0x60609020f0409020a0507020a0b07140f0a15020910050706150302130b010c050d03140a09020a0501051321050118200a0503150115110309010c11120102040602010c0207 74
    0x3078100010442d00070b40358098103540e503581c40e003e482c24030f070383e000925041e1480d0411550400000307540410400003040504458243c44060b20542c10404192502d0358803402014203040846880105c400d030b0340f40d04685400c14020185038800c89615001000703034001d640121042441c145440b408450904445000c80b43c0c010408000400d040c4100340241002c01d9505050103006040390000480600003100e2884180e07600040d50030070103403808013101d0050719118840e4540116503015864070161801943c000b801c0c1280c1e0b80804061034100080d9941c4141c0c1c101c0711034042d4100c4000350591402440b40104028003403410246103c0c40140c80d114801400c8091009103820354502020307403d05502002024144c81365a03400102c0e08040c011144950611250401800815101810300841d94400c2ca45299240031517128a030b82da200b400c00c05e90512040503034403800c003c842c940c0b185061501800034802d03d018100070714081d4020340592000355084c02800c1022034400205001207a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 910652760 1250 910651510 910651537
    0x2106100807030b07050f09180709060e13021c0204090b011103090a090f0605030f0102030702060c0c0607080a020d09030801080111120f1e0108070503070b2703031605010906060902 79
    0x54907040416102d40e4000794041d0740f41b00d800d00118580d03654070baa4030b450400c1d0342d01004140e4640607100800a44298101c07c0c01d21006441c0401d10792506e01445810485d0208010b9445d400034034910314240b2120498828280001008070340103030b4680180b40c0c0d103d000e88800e0941840701142e51340301d001d00b6441641003041d01504000032078082d0045a8652401200050141d4858021a0405941b0703000c1c0c4569a40003c2400a559410801140e03c240d00160080c1840b40c10705005488240141c820fa04100005e800b080c1203008560440c0e2403e03000c84070802443c42203290150410360240f054041c103500e046400f11250300031804071011008034400d03249091781c40c00d1400c0034115000e8002d005400c2107070b000c680b4403041610345601a0034001e0080051510f0202094a01107440e0072041141c0d000b8490300d0303420f181c0c038415a072080400d49a42750140c441c07000441e00d0350040100306c80700700b0b1388000d40100b0b004041d40038801381170084005200c16920351032120b0a030300c40c00856507480f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 910654010 1250 910652760 910652783
    0x702040f0e101505060406090302150a021c17040501140702060709030314040e04080c100b09060f1816140405011e0309050d080f061801050609210610080703 69
    0xb00d02c0d156000341c184401c4421103200058485005ca0403541043d00004045058800180158584070380030320482d072820003100d071504903001002900d41101c018031180703007189030990036521800f80030a1003c0c1405008404480d29082c10650301030480828904c41000760400800d03041c900c0400c0c114800c0780e03640c40d9001c980349155012140c98140001201c04140f0034003021410341d20102e11103020b980215070981d11076560035801418541d02502c100e40c00c1c0e15201800100d6140e10360240c1d840601201c101702c1c040c0010010840c00e03040f5040190034105000c0811156030202820b6901c3c10155642d0b05082c0c820380d040c940110712450045a02182d42010002c01c1c148140001c01c901c2441c500c0e005c903403000306139645844e100d101001c450105a5801c100301c543d05c0611083c1d40e2003041140c803040c0c0b2800c5001080c50441040c007446005200c0002d01e0380090301c440d07407008509a514040c45510b08461107260342c4600064403496403440410b640040d40500004400060b20b801c0000b0083c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 910655260 1250 910654010 910654033
    0x81809011a0d020c030301080c030d18090c0c050610093e160c060e012c03010e150103020102072306030a090213091509051e0705030a0302030702040f0e 67
    0x4880e0481102c90628980810074100707034907014805076000f040600c0c01411086c600c0d80426080140a0071080100203288680f00c0066240a03840c4c0120f403854800081c13540080700d0121000c600040c406481c070302c0360005200c408004403510204440c8511000c00400e40403004040920718040d00720b02105160220107440150740a00c03c88000ca00d001100e0310342380f0700c0b40908142042d4140103640f06400614100641a00300c0f191000200003460602c0940407116154020001081c242d0305c21508030310b070640e140f510700f5880b807580c003c1c247c421203030780002c0b2051f2882c3e13403c0240001ca0060080d0440012405d411008514048030781901029010304107105001c1b03070f80c00061802e41102c0c0c448034008056140c181d5010351040ba0407001080011140c10400d00c1440c002900020803450850f00c003001c00c0340420010f007004e81e000642a00c95074455410751420b81c0c6600721540c5801801c4000e410942c0000042c45030b64420394003481040c0701060203400721094100b540d00300d604158596030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 910656510 1250 910655260 910655309
    0x40c20070515090a2403060f0312030903020118050c18040b160c060204180e0706020705061b070f0602060a0b09070f1106160201270213021608180901 66
    0x1e10f003e005002910307999910b62001550000100f64840030031540300c0312001555141c003494000c1c1c841300e0714040c02e141c50f50380c0b2000121070b0b89d11100105903803403070500c0070140b00703400c805000249101420f444101030f040040d1a51525044d461103007210020900c5a440c800540034031542d0811300110300c4e0741d62640f03944402030070f4010003030030000e400c81d842001501d140f001c3c0001d858201039401c1c42104860003041255038410a000d4141d001c0e00d801c0200580c0003440005481064401a4680800001d14110340c08070a401d84e68a00611a0100305581204400c8003180c90650032910641c444200810440341c0444038150083c034400000780403540140d0740111a20624601050790707040203e00c090401000703945407000c034030048514000c456424002c0c0982d05140d4499503d9003550ba401c030382201d03414542e00038000c1c3c1c0142400c68074a50340d641917418030b0b11420603d108844007840c00740103d600595080714130100c8074616040a082850311030b03041e640035035800106044206a4034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 910657760 1250 910656510 910656517
    0xc090308070f1211011a210129031002040b090f010c0506070f12140a09020612010305061009020a021b0d02150d1b020624040c20070515 60
    0x94800baa4041001c2c0001541c0f03100c442801c002954481c00c1e00a92052032500750f071051440301030b604a20004062850380ea48048041c0108801280820b203034402e02a90301500842511580401e05440c1600c542d042c0841c15403410349044080e501c0407502c0244d820700302e004501540352008070500c03101415080c0360f04002524041410202021b041c5561003624106003111040c00041c004414090ba40360011812003035042c00d04000e00c1140e400684003880528000c01082d40151624407810641d290002103410f52540e51184490350b6031130f0304040c0e80e02c00c1c05451340e003030030071007210001481c6055209075000c0254542c040c014046002001400201080c3c604640c000003680b1100d005036a00400b0a21003c102c003074941d100d0703a800b44000c0403503000c101800d0548072900201c500c007650109031680c0c0002e000c0c610044130303030b03046200b00b1005464524864001e841c181c103000449403c0080c6039140f181220340981c0b00815102c525403900098450150824000b0131011140340032003018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 910659010 1250 910657760 910657763
    0x106050f070f031b050a2619170f091911090601090b040f0311010206130b0a0609020a08090705120d0507020d0203070b281709160906090e010c09030807 67
    0xe010b0b259404e002130000695140c0100e40d00c0d0701111030101041005003204801c01c800c6058600e080800da08600306c18424144145490021001c0501c1020302510002650303c10001d007068507450a84103175050402c094a65030709606c510040072044004108511034031591001c0d609201c00150b009000c101d49020f4003050503c80001808100c091410700580003c04d40e1519840e84945141005040d0200c00081107046412030000c00000c14448400d812089a000c215031031540c1d5035400000040030940c015041483c00021100250340e80f0281d00ca002e410450160b40e100382d039603420801095403049001165401401c00354040070300500140c800e09002910f01c00110007203030300003800d011440d0040c8519440c0452510540ac00c108640b81c00e094540b5200c500c080000074000d80440b4104d00040d201c54950400581451428803c16812000405074016000d40701d04164002d0803c0f802507144a902c0c2200d075101c00c4105000e404200c02040c1c6618076007509603110728580303902030f05c0f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 910660260 1250 910659010 910659017
    0x21507202a090609040b221a011e0e0106140d05010330050d110c0106031211011b0f02031e07141c12140c070b0106050f070f03 56
    0x10031080c0c50303620000c640e008007816404080500646001c110040002a00b401d008030805020400000e4104000541000c100e035a0340c10341007460b50051449884990000b0003000f50103051081c0368003910170703803810b0740c0030002c98048041501e1700c0c4400f92265440780c0f101741e0b28032000410500d030003200941248803006110f02d04c0d1154803003601c000c0c1e46080c0d10445220340000700003a4443d66071411300050a4081035004103806010318011300900031008682d07242c50742c5481c80041104154200c8210010250080c0302495890500b01d013501c900b0300500000c51600700c81c24514070f0042c031481b000c00c1d9003400c5050402c2029281101c0c2086040d6407203007544410403c040c519640c2e82030300040c003101e070841c540c2e4980080c5440e40076028010014001c41e0320fc000480e1403045141201a4010040d1030311194041e211202c1c080902101c040f03030b60340c030001c2c0024490080c0c801c80082400c180100b501f2038440c0d80c4c0e41c5045444c0d03c02c4610b400d0010303009211080000b010000a44041c034080d19 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 910661510 1250 910660260 910660273
    0x60b030d0c1416080f0f12041520071a040302032523101407060e160608220302101505040518010c051c021c05070f02150720 55
    0x3510030355548541d044044541d11240c486840e18008208030458044010f005d81f144030441d07014008140550301480d501464900c441000040c0300c2c880010f032103004503503884d4005460b511810b886e060705011720750a440c07034550305500800001013110100c07980078005064370030400c40c0d03440415a510200c1c0300000a210000107118080c1c0c40c0501038006845015248100450104501c1038038a603c61010b01c0440940d011104100b5401d4512803904400c0100316040c0340d8a0207410b0450f940b0b188141170fa110007010440c10790041d4074500c01d0303140c4080d031400b0107070b4038035208004210440f00130016409115a42c0c030100f981c2c3c21400b0301c030a072200c25140098031040003905403101120488800e21000414038500c0109010f1044000300b103041c07041c6884402d28003201c056130310078021712907580c000a03c0c03039400840441d5440344c0c001400342004182030401b4000d110054800141c0014459898802c8450700e1a0035500c1c003c0a070b41e00d60007a200c0c51251b40c042c01d03e204c0c080d901c070300c0d01880 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 910662760 1250 910661510 910661533
    0x50606090927060108060109090c0608090715090620060408070f0f0311210301060c050703050109140607021f0f180302061f14040b060d090b04060b030d0c14 69
    0x3141d41c0a03041d80550b01900c0c1641c1400c2045140c54016030140307103481d0400030000c0c042070b004680e07001171b00c0c0d140c5055100d41d40da058469113800c041754844c9190b44695620211240e1348414460140c0c0d44681c0c030040c409011005203000340100d070190038103d4104402240000740300000070100240b0035091031135444c1450703c1c2c8014001c0e04c15402d07804034501528a1402d80c60501c0151406c0b4002c502c4c0d0345c2586146001034526020500031103051001c0707a581c8000b400004c204140003141d00500070300c42c00c0b60318582035045184049400000f4420100428880750000c035036903141c10648020034820703401c0d0300c2e0070501410f0920484170303207a66a0340711030442c0039071201c100d07683c24000d800500381d41c1840d0081c4005203940d4a800f181c1c983e9011018402010294030b92501c48004540104607040c540300001c1441c415000400041ea2600c46c524040003103c0c100c42e403240c0d0090b1420001000e001051544501a6010b4540028014410000081c1d0707002407170840c03000e982003191184040f5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 910664010 1250 910662760 910662811
    0x1308010608060f0c07050a0321050c180a03081e04120f0c05040b0105040e04061b0207030b0c030c0d0e070503011e06060e0603151516060f0506060909 66
    0xe07009010307690000420400e054a5400015401007520514245001c0f041e803150340c0c480f09030100040800c0b82e1255448800754220410b155a0540110300300120708010001000c554003003050342c690f8a91480e50085286810058102101d41210a20749405c04512107402111424890300322400c0f001e01011075480035000c20b40b0b06980c441d82069410714045c1c181102540711350361040d4891350400410380700d666808000d86088036904828001c80da02c6034540300f8041d11068180d5207441c07042c04000811150300144030003c880c0036803201c2c0078030381781d040300d50f2480e01c000c482d50511510104000260b040303165201c0e54803003552209030786405d13441e40006420f581008400d42101007000c40f040e041c1003040d102d01002020281800501d402d40ea00101b10140401070404920f0510f0a58440740f0780c50342c0c0c80501d8111009030305203030b0300c144001c6484c1c010240301c00160350140c40d0030000000b5407000c3c0300c1e050145000a00040c2031115090820403900e4000345140e90b407420256a44d150f2016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 910665260 1250 910664010 910664021
    0xf0e01140703030209090a0b0a090509010617060406150b0f1819140402180108041e14010c020a02130b0312040807031a2a1201170c0103021201050105130801 69
    0x1095801507a05d01048080081488002e018141250701d0000b400141e0355030071a0441c21030b10541c001113816601c1800646c01040c2c0c86d88882c0010810b500480c0c80c1721b001086141c4240d1040c0404c20003d42041d4800304c0c03a20090155400d400e0003004242402c1341c440d005446815000c01d0014076120002004c41c400c00c002005070720841c0070350401402110042d800d9251208001d030703401c50800050300d107000101c001a10f01039060002c0c80010030f007030080c407514403980507070000301444c2c66142c1813800016902411000002d039528004600b80c09a01c04503c0d15210381d0020308020100780a5801c05000301007402c41d0070340c940306641070500883c0c0c002c0f001d4401000d0303000c05004000e2550038160302d41c035481068504404054010000c42664520200404030480540d011032a41002580790f050f00c2081150f0b5aa0031048000040080081c007640d102c2203800e205462a0340d1049005500f48c1c042d40700c800241d545400014403055201c0d04c080d02551844c039800c0d0039a01da40311005401c665 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 910666510 1250 910665260 910665263
    0xf0607020d170d1416030921020c0f12120f270a0501050a1e0c1506080f03070b1909080703030c0f08130221010e0a02030c030d0f0e011407 61
    0xc92440c403c4011807060510081c50380304c01c40400d140c40400c081220402c003078001d0525030754a140e14280f2010200d0b0054400b0b540c02804c2ca504456030300a9a18100300860a11410004500800c1401c05442003100002900020500c2c50031008010090b504100d800700312506003071001507140d211604108094800c01d038420388001c04c2c1d204c1030001c4d0b1040350304a107050040030420301458640c48601c95a15120788107942c9041c9203c1101110384030809003004e01442e00e9020204501e18283e480501114240001c071030f54a01d103010700a4981c01201e40c05032200101c00700090100482c090b0300010b0540c030180000e00302c05144d5486003542c1200320140e0019a443c41c600c50310642144950110948a003442e594520340800c85101e000301c1c0f02002806820404d200e1400c0021180031985030b01c0b50310000340b12854117540c80f2503540f4103007041a8403a2140c0307004046142008a844201045580d5078412402c00400040c1c03a4504d07401400d40c10000b0001380c000d44203202401400c0e605 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 910667760 1250 910666510 910666553
    0x20906040903021011040806010f18020d0912050d05090c0609010809010b030a03170609060f0d1104050a1e050402010f0804210806040b0a050102031c14151008060f0607020d 76
    0x19800c146c00c9502e0080160000c54203054ae00303000340241c82d061a9840031100c00071501580d5024403c024030094901800001c003d01090b050581d4482d400a000d4044a56a5001044161b076540511980d5200740e80e59240c000304104217005040d48210340565019602038008501c01c0c04941c042403404060a400783c00082c0c0000c40032154050100311241c00080c22641c0e044d45007022000180140c034190540e038451800700400c8402c02460144250350714074010010016480e00c0d103441030141c04950b01c0c44060415443c0c0a0601c4507040c07148601454060391890010085030600783d036034100140043d1000c070911500b05030300344107000901d140041140d0b65603401e41080018842543c8444002a200c0c5002d00300c24415664004256900742c00b101041201ca040d2110290005140c0c858202ca00f4041e031000308841184584620100303600c095484045044403404e003101c85001c00d443d2117500034402d02c0e44804900d0b05001805403540010403250b15682107680710302403903002d40d400c841c0301d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 910669010 1250 910667760 910667767
    0x105092b0210090602060118240815041a070203040315020a08070804121d030f030306031515130b130b010207120510020d02040b0304030504050913020906040903021011 74
    0x214105100001d502c4920740c24000ba00508141000c4c1d20f81405008052844204000d1800841d0054104015100e01088004000341d0755000b0240c0b100c4035402140010700c03403020200790701959144e209100d203400000c8210201c0b415030b0f4003170711940060035100c21031001f03000200105e050112400041c032a00d0b140103a46a92400c4040e0603141c008014009000141042001056258010f40c5101c00c1c035190102c9110f841d52410881c066030b0980c5039805108098020305107440000c0114061482242242d40315035810b0044d00610304100c034602c8075242e50300480111410704a1000d280c4000e9404e001c20301d260400041117100380070001d98448552994041e0103d542c05000840142c620000c04c1032894075240c9030b0780d9a510040000003100ba5002458041e01051641a174001e0312201e080140d403401c0c2401d000380b1139081402030903c5800340c88081440500c0304e152854210342d02a00c020b140c0c0ea221302c01c21000300310820003503040d405074401034801406148140d04913941d049011070b44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 910670260 1250 910669010 910669013
    0x60901030207080f2505061305010e0f0a050f0c1806030a211223060609030708030406090b040f03060b0a050306010906090b03010209010c1e05150610030c09050105092b 74
    0x4140185d650410218101984150007003071001c2042170740800160042040c005103458000d004000009098400d4000c0d0403500c0398074040072441d02c105c640601c0480d024803104d43e01071a00c1e08004075107150310a051081c40307025010080c40d25544075100038240c9040600640303c035030507000c1c2c40107140c00e200d00780003a04d11240c1e001690301041d900b40070410441465031181c01860342c81100e410103046c403034a1b40028402d5944004441c00340c1e1014090300e201565422400380e50b500140140c0740403840000020468151040c107440c101e88208840d41400c910715140c40340103080503a0b010744c02c803141940124040d1020840343d030007080f0807040003c10134508084002143c059000091281e401004142010382e881503050728820b8100300d0034031503c000c641108110b409801c00061040c0540c501d019040c09410f10101c1c0301e444280e41381c5c40c0f50840054100d08854040c021000810a00f8609210551042001d420405005025030302d980361100310b500d0034840c0c40c0c202d0b0402c4404006c01d000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 910671510 1250 910670260 910670287
    0xf0f120c0509100f05090f03030c0102070f020907170c0d1808041e03050604230703030c11010206070206160903080c0102040f08150703020d1b1205070906020309060901030207080f 79
    0x4140f00c000d01e40000c0c20f1600420041c2035200381c0d00150b201c0c01c80b0b04000e1925541c02e0048503020810b04000715070710f4406140a01c950804400240d00c0f1344040400518030314010901c03191040340307031800c0305010768903442004010303048042c4d01c1214030781d603004523900105c120032030202850080e110b064641d881d00e80c50040e1074800305030140480708154002c0001a20008415802c00e500c1808084401d80c45101001032440000001d4182e2044450000c245500010001d4060340140340040305c3c085c0d90307401613943c3c1009940c032400681c070480000c1c014003681c0110050800403403034003a544680c1e075110480c40d501b00d0188072015950019042004142d072664072002000342b0005400c4413081c1140082c40300800805400505800052a4603565160303442a5a03000200340c950035445081c66005140c50f00d00c8280f1181a880e10002c0b07400b050007070302c01c2000c60b540e0703600861410f0031880500029812403034801d03050680074040c1030002042040038007001c180000e9940c2e00c44030900041c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 910672760 1250 910671510 910671529
    0x1d09010c090602150402030309062701080f07031a0604060305060a0f050d0f0201090b070b190e07120c1a03190204030201051b0705041b120b010f0f120c0509 69
    0xa805101c0401010042c4603004112a8400250118400019900d0340046400c5210700c0c0801507000400140b0aa404420f0440c1044034405260007048042414401074800c83c2d8243d4034158a020f50b0000120541d121b50040e0b035811420000401041000308081030980e0003a40000d004130b501c510400c401400d002074040024142812000c0c0700510b090003040790b4070880d00300a08200c0000ca940b1003564010303400b1400a20203c04620381da42c00904124012030804e464940341c2d00700213603c1346460340f55805180c40f01e21054000d001c0032454168007005203040e4070f42c01c0300e000c4031150000843c06d81e8210104804103e50144035a2454040020300108460522400250344184014005071340c1c0300e0140c1d8a80111400e07004a9090402c40032454901035030b2010b603006040500e07044940707920080100b411001529150304030300c400390060301541d00410020340060480403174200018465503140c0d8250701542458a07241d05c050781c01e0002d64a0f00c04004d40440c40c00140d400a80c20810002d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 910674010 1250 910672760 910672781
    0x925030228032c060610053a14101404091b0806070206070504150804140115060e0f030a0305070f0b07090e0a0b09150a0b040e040b01120f0b101d0901 66
    0x6c1914030008400140c04c1740180301407802c0c0c0a0a5002055211030800d1a06400c2c2d425150050464544004078001400398641c4548078882218041401d5085116069042d241c031070107006245c003900400d00004211504090741c025211000040020b014040d200c80902482c41c00790046140c98000a86000c0004e00490704001e401c0104100c00f042d4100e10a120b07241c0713441c1004940c0c1702c034205090800792441621030749510301f01030040342404100300001107034820340b00c506042035440e04001444600900325501908000c0314400000d04c42c0e402007038428482d0b001d141d46c102147e00c4000d5060700444110010a807820000c0c080c0700700b032110003940480618001d00c4101c4800d0041250314070040c242c884005207854051070030303a139076140c03d038050076502c400b1a440b40d0b501d522200101109a4040d1081003001e400400e803600c500180600c1e640d00003460141482a5036140c45200a0080000041c070f01c5100c1c000c03e0680c0400c07085504078540c0d00030068135090071844542141c288000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 910675260 1250 910674010 910674019
    0x1020307080c0a090e18030d0b2d040902010c15141003112e030f0606050403020607031d04020f030709060306060e041a0925030228032c0606 62
    0x144025507500110070400d40380030305a174103190b1b294902e1036500d03841e207101178600b00d01001c00c15203400d800640c44402c0c2e151048500c1d02c0a1900c543c07285404000300c1c88500481d402900c44030307995041980141800600c1850035540d4a4500d803203205500c5201190410305035101c4901016801d45101d007a9000600c01156a00311840c645e138007003079288610314640c094203600c0c16007500b0b044103004840b4641d442c41c100000006807804010020264920903294252070094085070305485403041c1d9003aa54007800c55850415182c0f01510002810782c2e4910b81400d003210078107819113460026080c2410000c0e000d40e22400c3c1142c0181a220151300030b0307010145012010400d40e0341c01072010900040641d030010301781303103074a00000e80460a1a0140e411481160a20a8100c003980c0451520040801c4402240100c040100e051703109400e00c0313942491500403482100c00070448241d000c6416804c001520751400c2c00306a280e03255010805000c10704801c84070114480900c420723640440b007140d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 910676510 1250 910675260 910675267
    0x201140613090f0203031602030708060405030a2007060e01110a1709040b0411070c23060a0c0c14040b01020f1009140a0807140c13020904020409060801020307080c 72
    0x801c019030751041e80e52081644480b4814240a41400c500b003036983c02030107403a903440040d2290740c11700794881000c03030192049030710000e120340011a499003d03d5100010714607003556604115911140c010240c0903000300e082000ca400c1c00d0806c40c0900800f000e44810344080c40480001d090035240c680b03032540701d40040d0030b610001a0a103040425450700c110303800f0380315120000424010108034100b644c101d40351400441c0c02c45030040291110502c902c42d82150641c0311b043d04807003c1080d01f540e0004c140e881c042070b181898080d000c0d000607859440e11403511001c0d61503581102d092648032025844680340d003000c542c1010b00692000d11800e00040c20800b8000210540d120085942e050001e81d5409007581000681840400030484d02c1041398502101c90a2808003540040130032664041d040d02501018030021465001241008100300141001208001d001c0e5000c5502c02c2d601507800c01005c241801e2912a840107408880c00043e104d18120101414100300500894403004091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 910677760 1250 910676510 910676521
    0xc14040b01080c030c0403050303091e0a1109130501020d09120315120c050306190606080606031602030c030c03070203010b01030501030803011206020702120d090f050a030615050d12020114 83
    0x1428240c02801d003041e0284d80e640c54200c954801c4c0225000142503000000070701071034880000b0303031558442511486070300b02640c03041d40070f0f500d0040b61801402050420501100c9241100e0709035402665490040384884581c0d513000d0891303004034210301303d00765034084090034805400c1c3c031105550582d08003041280d040a06607840b85440e40b04170074441000c0c0c00010704003c013401000e0000c05000d4101c501d503007001481c0750086081158180103491170b112001901c00e00c14543c1d02e000f2040500b031286192101c659034080c15102410504c1544410030502e40007a900b000103180400904c40611384540c82481054290382286600b1030405080c90018004514814201c0307045843c0e80c1401d00540003546441c0b0043d020310240658800c03646220202c03081c0000c074594041c961999102d81c1600d45551500d101d80d041d6000d1190045010039050000450a0340400c489206807070600030461b03134800c00616101814002120401c4504580d695040c0e02401661400030034213030044241d2500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 910679010 1250 910677760 910677767
    0x90203160623030c090d170a021005060301140a05090114010b04180506031c02070b04090509060a1b032304050f0607050423130609020c0c09092e090c14040b01 70
    0x203000d86903205401c2c030000d40e407c10104191000c2ca00300144049a210041100080e4803011540c0e644070303241d03081c0343c006041480c040c850540d142901005541c038039110140050010031000304401d000d596201c1b078119000c0f0002c01024001e10f0b880c040d96a440c4d05104503062429001c910009a281c00e21040c4405603401040d984c4100340d400075030080c00460741c1401c0346800c800e80d01403044058001008104502d0580146104548080844101d603c45160355011901128000d91a60348031184138107010f44250484403102c107440f42105240159100f9452020780251000c0701d5590001d6000040400280a520350001440c101241024900b044c1502401c000d40780140d00400042000440e59407100c00c20141c040500b4800c02405031105e00c0c00009602980c031a01c0e19101c0c000395002036290a419143c4203001b244090070041000e00e40002d00c45504060080c14038030804410104103459229109125015181d40f003c014604500c00c2003030a90084e1040c040c03802c1104030205642c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 910680260 1250 910679010 910679017
    0x80c040e010b0312221e05060304030905150702041d010509120d0504230d020f0d0e04092609041a061902030c030c0a05070501080910090203160623030c 67
    0xd40c4403c0da468802d01174400c0e40106810146a5100000c140414a0f109040c0c1120b08001010107003030009480d442007260790302040320014009500d680082c006401d04444038642284d64204690402c01c03a1f80c001401d81c2d015010403a240350020902c0d075400c0d1024064030740c00601500240564040c2180840ca40d407050707003030b02105682c0310303c0400d081141030400c903210301324000c44469001088041036a01c410981004030010320400800d14416030021581146440007a11005000d607210b40c107100c06003000340700588624480c44640000d44602d040d45003814405030b01c01650b20a03180e02044101c07440d2880a00c12080d00e8201d01c0081c2c2c6070300c022514650503942e1540a5030400c090304910f0f502c20f583c4484103502002c502070602140005102407624451400c0c1c0f203801d500c4500454041c40c040750215041d52145208a80068a99000040103400901034484280b0381d0014446072100d154400b100145e9800c094003d11080b103c00030440d04e010741e811030f19600344905540ca0901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 910681510 1250 910680260 910680283
    0x1020c15160c1b050a0b030711011a01030e0c060f030405011a06090409064503051606061d010806060f0a05041d16080d0e0306070305040206090307080c040e010b03 72
    0x40421556003e0b4005600521008140c0201845601794650f101c0511ba6001a181c01e8081551900c0c140005078060090b01084801484c248012503031850044010701030801c1d40f40c0260041d40b07400a101e440c0c0100400440288984c00c17940c1e030420389085070844403500f4048400030526606520300c0e5840c3e000300c42006000b00c50109000c181d6051580082070f001c04080c1c060f0307201286080d0059115001d101d0a00e240a10740904843c0e8508018070700d8510420003000908104190705511442da1498002079000d030310001901034440c2c2c0f035058100d207080ba000b01540769040c0100400c120800000b54080002d07151000a0040d1001095080d840d03401950710664903500380810441002190200d07010040017241e104101c03410002c00b001c001c034002c0b400240214041200346901500e11010044000b60042907036a0700c0d120118001c040141089038052020484030381c0d5603034104805006041c80401801d1000d104404000448500c1e01d40950b031a418401c0d450100d9801049615841 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 910682760 1250 910681510 910681523
    0x10608010501031a0a24090803040306050c27040c020a0b04080d09200a08060405070312050c030c070918020604030212160306060509070309051f0e01020c15160c 71
    0x80044ea0503000a03050704051054000707240600000780150802c0048110340351180240c003c0100b6940304580c803031403900581c8070b1540300f00300410000717660346d104030380c0100080c10307042c2800010803902c06051559180440303114020403046c181c9141504c00e07002100c5807400141040c815503601c03802d920b9030003013001d4503c200c00f0030080511041500401c0880b40e2207903003008a00d8501d10f164800083c005006030080c502039001140703000b0001031484c0078a4110000744400b0b0b1450740c43e07440c0100b5103030b8a1810001c0a201014142c1d40c10006480b0004111020b0010542003140c0c5801f25036104003440c100f96400080302c000350700c80d074003180c00ba1b0740c041d074210050304070718110507290440c10307012104550207010b0300005014443c3c2c4a4002d03134504868903001030b100c8403012010344080d580050250b4105c1c0e6944000b5200c2a1181d0345100700340398010800e207140340845802c9820403a4044c400ea00802d8a44510080c81e01a880c2d01c02c0b48100c80210488280000514468200c0c5c0d00070b049 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 910684010 1250 910682760 910682771
    0xa05031321020103271401112b0b06040323010c050a0c02033c0c0105040501080402280608011502060112060f0c03060602100501060f0e060c030c010501170601060801050103 76
    0x25191505c17600d181001c0007490201c60004625084400440f0350f8010042d0754030b004400e0303c800c02400112a503000440c1d02209401c14442001040c000c91f80e040d01400b1562001c0600c8240c075400b010300010b5024910680c00c07104003c240c8071049001c00105003907649001d14650019070044150b0b034052080c4e00c6c0010a4030300034804240703090030b14075180b10754580e03c16202c0c0c0701d5440081c1c40244506a80c1796080510081c010403903071030030542211404a40e0a01051005500c101d100e02d6001d8002800404891210040f164404115180c90810914170b160140030032600400514010720f0300301d00d88640303035110b00402500c555040c003442400c40e0080c846d0209120480d0071100405640c0e450401c84610b21800280c010300c030900c40c03c4003600541600d50040c800511405040711956140d00c00c1c000c82c4804100c4450307071015146503011205002c460802c0b2001c0016081041400c800024154140840d144c2c55035105001c030380480e40400c005010082d4031809681c11100c00b820080754 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 910685260 1250 910684010 910684031
    0x40326090d0f090e090102130e01060813021f050c010b030703022b080f0405131a0609030118060614030715031509020c0604031d01020a170c0a05031321020103 70
    0x1d45014071340c04151180314000602c00da604c03040d8000d020100320010f284055035a9603200143c0803009102e40b1012404a10000c1c141c880042c0c01c021003c2d1000f04050480e0310085d41c802c83ca955800340c20400580003082e1012002001d12032500c1c2e488045004011042c551780c0001d030110030301441c2d9080c0300e9420100c079445000c050905940203500941e130689031120b0444000d101e40091080703d206107070b4401c041e29003562500c581c5d8418001050b0740d40c910103c200034004c065106210064240d9030f81ca2407055a070380880f810b00001e80c410340d404101e181c54610640503120500c44118803a0304403000402c006011001e03050320540050901060743c0840e650001c142d02c0041d44490b00f6140001200300000d100480c00c18402c0b44241c8420300c1000b94a032002c1540e41d00f04a8070390159010340412004640c400310050611003040704203c1c54001801013090415003a00c01c11261680049000c406130b45020241e85d0142c0502030441c80f00350307000940400c262225840203810f040d076400e02c1a5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 910686510 1250 910685260 910685267
    0x210030608030a05030406060504110a1d1207080c011403150f13020d0615050922020c0703200d0212160609030512040501020a0213060509040326090d0f 67
    0x140144140c01c2501e4440c90078540160481e8000c0700e0481d1041e01d048404141c0d03107810b03c18034903201c00c01c100650500b10300c0c0e02c0648440810080c03038042a480081640407554039095021a101c500038040c3c510b040ca00903501d49841401c4001e50705000308510b58150301041c81d13042d40d5008112000803030702803003204041407075103e010b00180e420264a002701741e994110f035002044c580703448030410401d13140da5001510f0507516082201c40055020452104d092034000403052007601c0070300c14079294141c0030030341e503040780c0c08610260440d40000d80308105020300314080c100e000c8003144410511440d1040015090181c0550080c4550b4540e10200885c000070030240711400c1d45440c0107410151274440280c00d281491200300c1d41403107114001c0314100140b00c11359003181c0040e0020701c0b90380c1081e8200590502061411540140c0d58100000c566a80c0310f50a4003c038029107680d00c1565441905c4c103000d1814482d10920681c01005000010000282c450741040c10f034a4440349045502c00103d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 910687760 1250 910686510 910686521
    0xf040f06060e0a0204051c0203060106030c110106140901060302040b0d0216020907020120070c05010c1a0703060f0b07020a03030f02010209150d050702150103021527030f19021003 79
    0x150000e80700b62040086018490703004000740ca008580f1080d49841d18001c0080d51440c0d400300035096003203100100007003400b94001410b045a14104440c2200d041d5a081c0d0031100d00c4c0e40000b0001a500b2001c0d4254240f81c5021405451359190951901d401e041c000003191190301008110700364000b88489a04589800c0d91080c1360380100324440904183c81c009028200c42004055040c9038291058004140c0400b07c0e98115170003e0b00240d01c0e481c0000648a421851001355002d840d0a1303212018001d003242050310401250b200019118209002e03000c3c045ea880e04403001d410401c02c40580560385200d005012030780e01d0300d89501c03d10441c26049001e03002d908400b9400406400ca038079209907045001e04148150f040d01008250307a14081284d03100c8191381d10350b040300310b118018030160904400984002411410342490091030748801c1c501300008040c0c0500160300e9a524404514050280c2d000401c1c0040042c121348541803041220200c511000a02c40ca0003400115542070003030700013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 910689010 1250 910687760 910687769
    0x203220b0f012111062b1a0307052b050d031b021b0604050303161b1d1308030f0702150106020c060c0c060f0a0f080c070807030908100f05010803030f040f0606 70
    0x215844544400c201b42e13032501d004245e00c000c050810a45d080446508501000715442c014001c020309071902c0c0a02020710b006a2000b040c0250b91311807510003480e0300e50710720001c2d031151000b400e1000324030400808a55900380420a0381c41e44c01d422540c05a030009003560380c02c1d90407014008a051040004031070f0711907984555010b0001265400844100c0120700303461a00401c2c0c00c1342da5040310a110380c10a00c030f5008080200c81c2045111541020400f02540d0111150034640c0080c0301c0d41e2160002c80e00304640300c2d01c0030b0720b021041100c4039505003c124141c2503100c02280d5154100040a5212004102c0d414090303030020a400304415803c00c54014521030140040d9599041042004030301d5002d03020f20008202c0403940e0081c1d4030f100700d0b202c51013500c004102905281c01c0d60303a04000c0d54481c0e0010740403c0b450010205944100b1b1124019404c5d03440400242c00c203a80101e2801e40342e059100502070f4106100f0010807808151103564082d85c081e8504403540c0040c9003030f10040c4159000f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 910690260 1250 910689010 910689037
    0x30c03051810030c09091107031110140612010e1b0d06140609090601030201050901080a02120f09070f29070c030b040c0e060f040203220b0f01211106 66
    0x102c50b04040d0140d00507500b812180d5511039041d902d6484000903191103900c0ca0303204000821110011a00c179091443e4000024401d4800d9000c40050311700503110840070034600c0710940c109002051034008178040700500703820000d00051015081e050748480e541c070b100c601c00315100408000c3c6550365082003252070b90701c03103010044248400d1128100c40421030f1503d01680051000c20840400091043d04a950596519103440c0844004403420170000d0043e480c0b8540910040c0c1c05c50321228140d42c452000000901c00d02d00c3c1101d0040c1c5842c899600805820070800800c1c800321000d9000d1045940c1d04c400060541d01c2c0c0c2401c038a85500c40c20a0141c248001b204000c400c0050302150903000c0c42c002e01c2c5401011f51201d40b601c036800d2043c4c5200398041d04c0c550a20b509405d064010b541e100d101c48401c000c04044107408440e480700d0b054030032690300b5520810483e000640f40c4140b070142070200c2c60040301c001c02d0074980e50810700081d00070b00142040500c0703100c596070714002c4a907040305000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 910691510 1250 910690260 910690279
    0x3a0b0d0510020a09051903110406030212010c0e01231b0304090218121f021b0109020a060c0201080414030906160b28021e0f040819030c030518 63
    0x55076a03009400c625030880004200b200005014501809002c1041c40c02000c2d40401515607503c144000b055400e500d601300e5152540000560741c4c44880c404c00d90401d0740003155a100001000704140400e00c0c056051260205944000081000c001c0e2120081d020001e03591f0000081c20300c4c00c880c0c516081400c46d11000501056041941e0007500602405d01c101c0c03410f82034003000f045820511841181066401401c51000c80400c1e40e004522054065000500e001c0310101b594035a040300030341072100d42e916003000c80214140440c140008007850f04e0008545581580004d240d06800342018201002c3c1050103160340c07800b44110b40d03113040014101c5030b4560000800c064400c1d10020155192101c00d40001c100084401412a20400c2d00240b00c107074200c0c0341041d00c0203402880402c60401e884441c08071414105100601c0102c102d0811552950b02d001841c510702040040030241180d0401821000650070080041d415681400e105403aa1948103451607c01210505541d00000d0706 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 910692760 1250 910691510 910691533
    0x32d0507080706170a02130b1908010f0f060c03020c0306040b0a0e0c15071a0103141b0105030c1b0d080108070b0f07030806031603083a0b0d05 63
    0x40d04000c03207280d0019910002c1d41d400d020398042e020031038413141280d42c610004841c0220740d8000e09200c0245c0041c1100162196507200c96504248042440c44100105661000e50000704250040941c004200a0107080c450a8401c0f40b120744945401d000402c11036508140c001d00092040543c06801c903202480c0c1810044d41e9800d0680c0c0007503030245482c68403500f6890124a030f000c0b0a502524480c241d000425041c6107541c810101030b500c3d103040c4101c0e0504110344018490085000326110801014800d1000b414250304140000451507002d04541640e600a070030b0320717402106802c88a4440700860340785a5007150315040303071446001e543c416200355138214400c14144c81c84c01045940c0a6100c80700640d4034890f640003001c2242c4240301d0f140010b4811486298401c1c07024069910a04c080031030310340c000080360801c481d410b80102c3d070b4000802d990721042e1400c4000c101c0e00c1152801c454a4001000c0c0ca141141c1e040d983c60b800d0920541d21001d0b039176074900c0d0f4424226202e2a142 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 910694010 1250 910692760 910692763
    0x40c090f020d0e0303040215091504080d17010e01060507060603060f14011a0306060a051603050a0221160203070b0c0a0b16020d050a020a120f1215032d05 68
    0x1d44807110031902d41514843c41d064000280c03031041d9030180007800500008060540c1c0c0d60089080650701c0007038041c5190b644004040644010320000b401000d075001c2091028100c140d85e64842041001428010030440e41000c4030325046a8190504966542060400030042c0849da00040d16040c180031061b107005c13545a0050b100354005e10008003460b42c842111030071130b619900008042502c1400403500d1454107500810460006040207403408246502030801d4410004054000c5580032480000c40340e010b101d208080680700c03940900e41c80c1983e66441c2940552480001c110072030001100844d1020803000700030300441b100080c3c0f50031041030220b0b42c402c2e070310310110b503004254004280003401c40c00c000540581160054402c51804038012111034110030421411442450b4141d4045040348410b05e41525040d658440070380d4500201401c020314405100d803c0514080c0420500e84800c815039003569803044c02c180000e03a4040482d503e00380c003400d040c3c98000e80c400115040240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 910695260 1250 910694010 910694017
    0x152d0a06121a090c01120b0303071b170606010c0609052e060b040803030f04061e020705010b0108161404051f09060305040b040204050c0d05010f06030609020403050d0503040c090f02 80
    0x10420000e200c3d500c03000540d0300c03a0000c503415404146200d00d4115114910740103040714032809001c503400c0018588809201500000040c8802201104180500c138034905a601c08064010010304117030800c0b80000f48142404c03100540203a80c6e4072401d20401006011101c1800304100c1140801d101c481d01c040302100200508020252411900083c4100c03400152422a9451000b4500b580e41c0c000d80000b00308801030040700d5a65035181d408051502d81c140e22841c60140800c010384032081440c0860071200440d52050600c0b20690401285c3c0d85d080994410405081c03501c14484070200344101580d0103590465513000d508040d01c0c40c0c65000c1c18014814101481d918024000d60741c07202a0101c0740e00392809005100118001005410245c201607004920b0b081c5c0103180c0000c1c90602011148207070052401e03c05201400c0008640c1801510050440d51404601e041e10f5681c500e517880c8020f503484008e120000c0001005c1c0034a0710044d800801408a00f48110103041140400950 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 910696510 1250 910695260 910695293
    0x70b03010f140d03030b12030309150f040b01061215082b0e06070f080a110105010b0a08040b0c0c07030807031409181503010e152d0a0612 61
    0x1100018005002c0c10034000c0e032298088003801501d01c181071610200e000d80148554280c018480665164100c4010002544151840405081e0300d4080c400070480b030402c05441413003412024000e0101141c0c2000c64181102c2440c20400c0980c14651a000b014001246c25840b8203840d0107800203100d01c01003184414101525801e0000d0144e00b42c5004240114143d02c00c006105400d100620b8140a001002800d0140380348603100100b665031440c0c1c50b40f0a18500d800144c1042c0d0744107182509001d014054030f9202c00180c201518130f000103004003c000d1018026940e644c001c6000e20040004a9171211460303016aa01242c803070908001c07030362140004070700003510403024030000c41da140140d81252070014065085a81006800c0c80f2050000d00381a0911110300c5c42ea1940d50740c00d1003480700c40b95104014142c00c407400e400794040d24200a248042c50038081070800c441803003841500b80c0c00c800320120800c0d980c40380e90b1001c1c0100125008141d40e18001500d4005003d441041d002094 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 910697760 1250 910696510 910696529
    0x121f0e0a030e12032802030d05071707091208090d0206040f030c09060f23120a060f050702032b060f090e0a171804020a030b0102060c040f030206030603010e070b0301 73
    0x41ca00311140b903036139100da6504003502c0030807410015500410350b4104c818a070081d20440307060590f4040140e040b200d0543c0c4110100d1030051030061a142e0030f22030940d200c811802c14603c103510b4410503c42a0322103d000420803c0d000500451964503201c1e52103109402816403078886455081c07071900c503803050100b81c515440c4c2c9000001c00072024010202a6003a55005031081031810b0100c50135600c400400e516042c51940303614969840d040188440c0410711001401007075081d0822780101c848210b00d51000b10709110401524640000454466414003001011042c0c401410341c034144058400850015003000000283e8034800007015055502441c820000304280e4200c042c0d4580c2d4a00d00100601c200d007585800b103091404c0600700030794581d504003000141e400000b50488c2d00400300c0c0d0f0003290340c071880b60f03005503410050710b9401034040c100079140a044c00b2903001c2100080c0310003403040200000042a036202034118860340580c04080b5002607803259141c5299410900810004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 910699010 1250 910697760 910697779
    0x131505010b0912070305101d010906151d13050312090303070f0e03060103120c0819031413020f06120a0c020d0f050412060914011a121f0e0a030e 64
    0x21440810444c00300c0386d00000411003018880e0f000e4001d000b010384004826107600c1c100c6110103d00780203032814030348520400900c03e520100d8500071948281c003c00c081c00c1c01c0c0303685052883c0e1311030703019034201d501801c00510500c45454540e195228070a400e010b0555020b09021440c0400005180266255107866032442d9000d8021a0a80c10b601c0203964190302840041010030701407000026001010301c1c2500940c160340c1c80c2c900e8242c3c80b500070b42d1587d07000c49584034405540340c4070b000308410f91100d81c00003178201156085c07076522a4003000f030310510050301922031b155510411941007281d4191402c50074640540164010116500004050301075000b40d500d02500c141d130060880000d60321104c3c00d150420307403640000a07950800301c0b1055611103400c000302d00e03040c101510008890300045903582403641000442550102c01c1c03401040c0940b400c400b08100454005003c050814410940d441c80e0700c84003014001c802c08180d401d000702d011314802e241e4003840000c007003002611360300390 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 910700260 1250 910699010 910699039
    0x60306060b12040201031d1e1507021f02041703090a090e071e030614090d030204140f0f12010b030c030a2402040902030f01051306060503131505010b09 67
    0x4040c0b14901180d5802d150001c005801580a5401501d204d000240c142100403404036206140c00c0c009180d000c60502c05407841250314000f0000752042c0001c030303110000035091002c8045d40d60694045080504c156444070151885066410b8030000e00d0340e4003068058480703452040d0740300d0340000140d901a6031412408070b20a00d09010391004044d03060001d08400307203401c0000c03c0b501e10748401c0c4401040840400000304009001305424990343c10b18803c22414441c8034949050301c4030318110181401480100401d0044044100d100b010645801504040c00340000d0102140b00b41410341c031585000203460300200c1588071040c0150150f00300c8140300c1c00c0004040d03540b0301005004040c1c07240c045806091000344c0f41007a618800001000d4202a02e902c2c4140c143e8004070344120004501da0010852441c19a141181500c0b50304401c0100034180035000380148001402c40c9a014000c450120400103061401e0035600703080e202c10011541c4800840745254481c0d01d15605c1420000c1c41d030b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 910701510 1250 910700260 910700279
    0xc050c060418051f1413020d050106090f0b0f0c1f0507030c0504050d0305070f0804080d08010e040b06120c0303040311090612060105040c05041d010602010e010c021207050309100306030606 83
    0x100c414420394a131841e1030328101040700c04116a0000c903412103640041e49103001014005803029a107500d13004030b00ca40c1806002064800c25921041404a1400080000806410480740c0c880c4030140040d96407905d48100c6494412040c0142c0d072300d0350305c105001e00c21481c203030b01c15401622159030910a50400d15000c0700d25019901842e9800f04103c1001e000090241000341a8284104030098030310701261a00010b54205d6404564141c006460303640c18107900c141c41c61301410b41400e40d050141031940b1110b0500000505150241c04442d00030021040b0401803405a0800201125519501c078580700e0b1420756220205405044041c001c100c00c0c2c90a44030303001c1603002d0380005000a0b860901048081d017102d003a0f11003800410000810ba104d94103e24000024804180c4030144d450a0002070031581134070f000c2c0c24564036010314020195030104140e004105840981c0303855011908103241140b260f0804542d11031a084400b9101c00c0e0540c201100310b90007000304110140d500c00d50030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 910702760 1250 910701510 910701541
    0xf03081005040608100c020c090c07060501060503130b1906260d0206040809040605060c0a03080a02180d06061d0a0b0f0a17010b030105070e030c04060b0a0c050c06041805 75
    0x13030071035003000c0003803241d8014a500c14400e1011910440743d80300980c60201c0c0e8000000e5455107030388080011404240040f0740942401403190340781403440e40c1f501c160b000229441c1102d00031703e20080c0b0b101061103614441168200d40603e10010082d00381d5400c8495442d043c0c21351403a031311110103640d6000200c000f04080016200c142c01501590396141ea50384001c0e4000344400b0751081e034900001c6125156031010300031140010006044a0b4990304001d410039000401000425004102800420100b072880c0403110300305482044161070b1507d4044041d110380e0304400079003d501403440241420b040703011342c010b0494110402c080d880200512410940300081c154100310707440420001c445d142a03580c051701c0c1c0d044000050070780305600000d0a444090f42c03103000254925070030070f40390710f02030001716101c607000c8a0030400f0900d0411507a90354081e0031504800d21008150b8007060110500128500600c0104055503403034a501190307400035440440507401500d082e0016801054000c0003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 910704010 1250 910702760 910702769
    0x705040518070c2406090204030308150a050f030f030705060415293c18010905090a0c0b1c0c141b100e060f0f0a180f030810050406 58
    0xc49200405130380b00c020340618081d1800101c1e610800710030313201509030b100c2e15000e042c002d82c000d80e65620314100100030722405070085d925607582030350002240d40c0c1d18400008841c4140d40780460001c0e544006402c103100c61030088180d0000184102c104500130030502e205500c600826400c5600000c000e40c01c44224407000300c202d100d88021444141c2118050700c2940d88000c2c0b5840c02801d080800b032450400300d04030a07003020000407080200c14200001e892407004140d03001c00360701e5100c5440c00c411401c188260407000d640e40c804510b041c3c200380014816550050380030341034036aa45106240c1684960092a1310004c0344405101c07003526030060340c0c0404491b98613126000350500c400ea410350701000740202002007002940f00c2d00c260070b212b1501540644900065002c0074408000d061400080c00c2e40c0303020781c0301c0d8100f1164203a03c840041e00508500700016100400c1001c0744400c2c40910b002608502c000355940c010564400402c0303204900c1e4000501126030380d60b0900040d83c950303014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 910705260 1250 910704010 910704017
    0x30e0d020303040b100b0a021501050f031005071b0b0703050604020721120e03090a0b040617091002030a02030405070e070c03050f19050406090f030b0103121205070504051807 77
    0x2143c0452600c9035200e80000141a222206035a0380f0385040055018403102c1d80980c1295043c0c004541040503503a005000a545449008444000207925000f0800c079082c0801d580e0804a40c506204454500e88800e0b0718003408200441030401c44040720044601200003410140001c0d000c0c201402900c00081e4802c0191411717039460381c00544018640c070b0070001041409074408a0729080707401070b2900c0e000c0510141d07694580400c01d0022100c01d075001141030702001c02c0300300807140c4d014010090203409103111200549400b0250341c207011440ca0118000d5001205202c005203981d401907001d94400d100b1540e41c15681e2500240c481d0085464001049500c003040e00440d0094009001c0915554105842e00e810b00303594410003606800c1840001c1c0c0007050911a81c1d070040d100b0f2015001e00400b1040030792455039004881c000500008041c031441101004d400340c0200035080000c140140140410701d031400b0b006000d900503104851181102103c280910440030403800c0c00344444d030f0f4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 910706510 1250 910705260 910705267
    0x60d02130902040e07140307080a05060601081504050411090a140601120204031b030213020c0a0303020a030f060e220f021212030c030a061707050f03010603020d050d030e0d0203 78
    0x2001200505180900742c0e04035460304807210401e401440217002403e00142030044500284041c14a0403149400c0b410380c581c81841c0540c040b4400203641a400314007441d1039905a07561081407200e0803808918586c01c00c0c28030703040c00200100c0003142070003150b00369551440c90380c07030b5080c1d0760650794918001080c040070300010030f0941d449403040c0c400a180c2c0c07803005031900d0340e2581c41011a1009094940c10b550549009008502d8a40c50410750544500c00c2582082c44141c0015102c1c09904401401c1c076900040c040120f0307000e90407502c0607402061003000307803656070509090641d030110b644003c055a20040509808000c2d18407480c03003600045d61468a082303035130038070145020784202c0100d14864401e00551586c0e0401c0110710600804403c0c0751a03051210311941941c4941e000740c1c0c060b02011100003000c3c0c000091400448008403045a800d501000200f801010b043d04041c0d00040c60b07515050030b000b00025658401c50036640d04004494045600300d445c1c0d1042c1d081600141c1041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 910707760 1250 910706510 910706539
    0x100b1201210308220b0c0304030315030302062d09010507020f010c0801030809120f0f0c0d030c03082806081501030c0e04020f060309210f0703080901200c06060d02 72
    0x35461110303000214000c414104111791105503240d10100c0b015110701900100700001c00d80e05005214202c0d800102410403241036541c060b450741401441c41040c1ca1366109902c249001c00c05903800740d41101e4605140300d0400c244a240680011100c4802621450700c00b240c400c0b03030520546135900070a590700c1100780d0071541d61041560145030003d42c801c4c58007021850000090010091410401e4020000400c01c0d407a42e509001c40c01040a04c03a4100101180c0403c1d0044074007150301e40c0c18a048100d960f034030b1841690a100c200003440305020404ca0514001c001c0d030b404138050303032031510856802103141010781d2540042400010110704e1003072410402c441804118035046440200b01c020400a0640460001e41088416603201e910028884548841c0c200580a86200c103000d8549042400c1c20200024030440b00000d00b00701000002070003200d0298042020b04a517128000d0101c4100081c05140d074000e80c0040c220784c00b4000105000f0b18000107400e502036400303000c544100425 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 910709010 1250 910707760 910707781
    0x509070608150d060e01180b0a140109023a0f020a141b060a0504120f020d1d03030301060215251215030803010611060c03010e100b1201210308 63
    0x1560f0381100c4260312803210100224007070003152140d81d00302004500091181c2406510703c00040c2c015020b0b2403610035402000c2c42100485419101c400f03c02581e20715250340d944580c0040c401384203020403a044517044043d6800500b13550071a0400006011603400552408100e10809110fa004a2400c240100441c8000c0c1c014088049000340c0700002108080702950502d08120b40418606546904110402c00309403c0841c0c0d400c4e80d843c0003a41d020b0000d05c044d551b682031410201c28000950007804100743d1045818801030809001d076500c03540d454030040e40d201d035045015688005508002220000b102200c44403082c1c517461008541c1420020641c2c90f40f2400d0144c0c1c20b915241c5400403a010090180540150b200307005095480d1b2402c04d00518041004440300603a42104042c4405a40e40d20700b0380c1d05523122882d03003140c10303200c403c410740440740a41d201043c500d00200b500340c261220070030b406040f5420403540c3c0840c0101c1080c600303201c00c0700700e82c0100030907441800306902c07040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 910710260 1250 910709010 910709029
    0x31312030527061f09060b07210e06032802090315101e150f0806012c040608060a14010e0c0307120b06040b0c0d030e1b1302030406050907060815 64
    0x1031221403006803686a0031642e05a0312550844000c16000040c1c4004224039022718025520710000103104048052500500704000150700b41d120710340100100700000d9404560181c1d5020351000143c0a0381180940e00180d080b01031014400d0056140806c0c0900e41c1d003a07114810111001501c26090a08030424031400020302540007602036504003107030441c0604840c9032149001d40308d00910404089000344590b000800380d83c100680d00030002c42440307504071403506416a4040c2c0c405201c000202050040055070f00c005454460b01d002d00c0001d1403a90310000c050300d41d981007001580c0c0c0b02e0103240344401e030544507140c401104000182e450b80c03141d40c03d40d207404d00844000c55082100703000195240c010340c00c010b07021000001c80a02c144010440104103901c00c2c1820f100e0341c00d071443c0041d01c48002525101c1d0602580c1443c00036980c410b501c2c2e13025450010411901e900305400c0800060000701c03900700b054441c0300c0c0c021500600611403140702e40c203000700b8010040e01202c00d0119401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 910711510 1250 910710260 910710301
    0x9060b040b0d09050102161a0c0f0a050906070c060816080f0c2d04091a0a180929090a0203030a0f020309100806030712120503131203052706 62
    0x546c2408098038500f00180c82d80343c0f076030003651072846468140c80350380e81c840c00140c50082c0c0d0f648108007258030a500c40d0107030750b10b805283c18000c0c0c84480c460045441841200e000400303ea810f810046030498018041e14011f000d0008001d0b5110708444080c0e6840405030765000c03c0d03c00a00016000a00b171000603c540000303170881c8801400c07211050080302140d89041c00e00d01c0c0c1e0109040c00440b0340392050076004039611030111000d401c0c18022680f80e0741c0a018901848406c00c60f030107807441c1a90088682135521810301140481020020005d08142d548122822045440850383c9000001900030840d60020091480d00f04200e006443c00116640210f09500003405890400e50351424a41044122901c6040680c0760240400d402e20020350841d4100088421104003c920b5008404401e0708150403c20340e2502c540d035011000c1034034032000410b03030481000800d00146d4950400c2d800390010700d90410004600c1401a10080300d4001c0b4200c46600c20000541380c0e8080858840909 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 910712760 1250 910711510 910711513
    0x506030f12030702100902100305090312010b04030b0702060609160c02030619050603210906090616020108061c0602070321061d0118050402062209060b040b0d0905 72
    0x1403149a050516900c4002822014000300401014075014050004106046441001404800c0e40010b040c000544100340030565100c0029681c0c42c0108122503960040b4100b40300d0560f075031009104954840d01003168261201c10106808500004031540103d90080a1b400c10fa03852010880c400c600381c071441e004001d01c00d5002400340c0c5042c4042c0b4051900042010000d010300505c46080d10805012036000740e11948400c02401010803100c041070031040d0340300d540c515200c00000c215000d4801003c0d401100050344481400404108500c064401e888508aa585280412507201d901d0148160b100f001003207201d00241c456401002c0300380c400c0c02c10705012903e45070a59403d00c25070103001c0c07801c0c0da00d0f00c0902c85102010120303584040b0802042c0d80941c10188a1440750071183e25011481d51a540403900310b540b00401d07268140343c0c60603014111030103680000d507e14070720710840c101503290007000b1078034414481c100e4007952140d200031461b100210fa5401d00614804d041529507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 910714010 1250 910712760 910712773
    0x30c030905060703110706020c011d0103060f0e07023007061d030310050d080d1e0213090f06081f0b190302011d010207050105070201021c0801080f0d0c06050603 71
    0x1d58440010f401d50f00e00a80e500c80450000c52400c0d4034140d92904030364259401140303255483da0f03000c1a24a995088019058414192500147c0242a5a4000e884104d520103404107100c0b2070ba6401c02d1044541ea0300315001d000741c03000e40c800d07104190900007114000b461105401c80924100400103244a88000a01c040ca0703004070240c0c04102c1060040940c00000a110040145640081c060201110b40e100c01c0b04107a030310341000c0d10888030740d410003070b480d00751403104d14518044100c103030004a0380c00d40d41c418450f802203040c3d45460040b0000f840c070f4a8038444044a0710b1042c0c0040e501c052000f00b0300702c0c02000d02450101d000c4070b14110303065242d003800803c42d19020340c540324484415000580700750462001400d54505410380d401d0714a25600c60b40001d82c0d00189100032140c0a00f009070351058075000403403e0444800381201c42c0c10940080250302580060010304035071103001a60302e400380c142d01030781d200e030141a1050005480c0840080100b10142d00085c0c2155006046403507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 910715260 1250 910714010 910714019
    0x9090e0c04020703020304031401020f0702041805010f0605040e060f070305180f0604021c0f02062a0a030f020a0c0b0901051c050105130902030a080d02071e0501140c0304030c0309 79
    0x143c0c0c0c003101049006030000300d020070800100701640001c0d2811200250305181100d80110414052103401070320881d21082849890101000c4c0315500b20b80281c024030403003000f8800d00f00504010b103d8903000b01d1410018407000c00d004504140191000f000d1404a81c550707040450142501800348030303040c00381006c1d40368018400c0010101c40002c140182080f460540100000049800391480801c03039604e00000000b0301007400845d80b241e0480e002d688484284944800401124144558222188069081106002589004a51007680e44180c8007a0b849800c0b40c0f01c0419800050030150b42040034000303004460090044110107240c030508001c04017050f8408088000d21104030780d50380d1801407010307040c004240e0207050780346802886034100641c003107642c903468200043c014940220715082008c07a035030119440d19400c80c41c5800044802544010503900440c01142c0b9980703030049694000c0f000e0759100b446404005081425aa590386003910400b8500d8011000c01107003800100b07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 910716510 1250 910715260 910715269
    0xa0e061806030a1416021c091a090a0b09091302060f07061a010f022a030307121b02010e011b08030c0706111806070501020904050103061b0c0309090e0c 67
    0x107215041c0403001044282260804001c0000090300017680810a8500761500c03d4000681d00910780c0070b907449640040942d0400c030f41044858100301c000c3c0c3d801804810882d02280302070f00c107400f001c956001d0780340c1d650300801c3d0707041c860f50b800c0a42019102002500882040300345503013860010702a1032038200c00403000400c80d40611001c4904580d100f0752511303401c80c0702042c14845442800e00300f50791094041e01a6440f1003441400105005800280c80f104020350340c000d200c0c140c0030341126283c0c000c52500c1010458000064400645030304480302702c0c14419891400c00c190107841e111195031000c401150720000126054a01004072400c060015458000540c4528500480e25443d1a014600b40c01903d072428003c00da030500502c0071141e0b001c401c401d04100d80404030b504555036940d0346061070280c010131001c1640646054000018408160031510b4a00d200042c0701a58070f1410030309840b02003d80002500196403000c0070f01c400b50b5164020100d0f0400340e07003240c0300040200000b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 910717760 1250 910716510 910716517
    0x10051603030e1b0310020d0b18011a1305010c0317040b07090602070f0504090c09020c210703020c27130b010f0b0304020f0111010f1d030a0e061806 65
    0x46000a070ba8100d03040e6030b60700900028102ca403203500c15841080250001076a500004051201405c0c2d0000328070303441840c03a07881030401510141a403039140c03044003c0c80e00502401d2003002040c031036000380c15156482d00011112200c544600c0d0002040c10040119150040c09200300d0602161105500e9520205000d0074800c0388221030540b003031300d00680c00800071800c50748203106551141c1e40621081601f04811026200c003030320002003a00803400d041068100560042c20003034400034083c90b0b0b280011a06030036002a143d10802100c80d540c06400c0980304800340540140c1040075410042c2c50201120884000d841c0c0d0700c00c40c84001b10090580c000c0742594401c0d00720603407101c10010080764502c4c00740108005408500b0481c900042942d00744001400207208a03034907940048160b02036415540c3c0160007200803c50321403080c03500e40050020424500c0c4214404007010800c40c000421150700c0d81c46580c52101d004540014015160080329030310400040007240c254040d2180c4018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 910719010 1250 910717760 910717763
    0x30c0904020d09021f200c0a0602060a060b04030f0210210b1206100608060105070b09030a1709030702010c0f0807030804111c1407090614130506010e100516 69
    0x60945060710410401c440d05c480e01c40003e6402c903803110314150300b0001d602c1040303800703643c0302c40f1020100b00c015007030107201e007159540300b8100800464140d50009034030384140c02c410001c00c425074540300b00c41103038002c1c4d100080c01440300003007000041c10005641c0000c0b195500b04070f904281ea0300102e84d071000c2e00b4944044040c0c0d48482084d0a45021603c15107504940f01c041c000351b0400304031358455042180652014007072028041134280e44100c086030030740d40c1c03c0b10402132142031032101caa449600040013180042c02d0401e5030100080101c6400d4094803644009520306505a0b0046d03486007200c14003955110045001000444d81c540c0040c5003040c0310350f451140310f00e0f2929046c3c0c401030032411182c3c01a100c901c00300320411510480014604e0b00141480340c882c1c0c8500d181031810390f80e900180340036802c003800010706200c03208800307207070360f0085400d00401445c0010740f00440300200d884030300084011507500e80b41e0070100840602d000c0c6e00d1405a140c2141d1080014414014040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 910720260 1250 910719010 910719037
    0x30b0f0307150e0409020901050d032105010311010f0e100e041418030c06180c030106030c08070b0c0303011202120706080a05010806042406030506010b03100b04030c0605030c090402 80
    0x10310b500307100c0d0700840b80407203034604990402c076426032500480c054090501a0714080c4010704400702c249401413040030824640c0600e004615090866010040d000070f220845a0012201c2481c08a60049100010341d4205545990080342d1107401c00c541400310700c85240502002c2042d11801c0d841c4c41c0181c096050748001282400d00303000c0c2403443c00c401800c3c4945400d400078005908040804214150040841c08a082550940b0400302e42040350303034080306034107619050001003089071030a451012207581200b034814a03540c41281c50801d1003180c10951a80d001040107101e111800001d50104900260001c000074000c070031001d15101d4150030400104607510700300004504240590707800341c0000005040300e800c0c240c0e02e00080c07014603d103400c1205003120445090703000c2c1d81d0081d0011508001228203c0d42c1d554504178555005448070721703038090511000301d1403501c0c000c02c9800300e96008003503500301841c1c103408079402d4102800303002c0d03141010001d0381950703034841c000b9003006c202044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 910721510 1250 910720260 910720289
    0x40b18010306150f0303050406030911040507020c1005161203110a0905030d0f0c110316060e090703060b03010324110c30031803070c0f140907030b0f0307 68
    0x295643c01007060380030015807040d030390042c40000d07404000c0d20103c400c90f086c0401d40c2c0c54135203400040c1c0c03549400c0e80741e00945020100401d191340011034818640064840c1060514191400c84062182920401e0305002c0ea004a40016000c110740458400480c42c000584400c41c202c075989a034010300b0340400048054070207018900d01131100310103030b45d8035007440014601c600300041c200340840f81002d401100d50080c10601038034240b0407001900545003080308003d448020180007036040700c1c1e070b090041490100048081d0301a1180b84283c44c0c00c05619800c607071071541c030f0000003002500b9a50040d50350071001d000c00e0b005409404806d084201d12240c0b550f1103c3d210718a40181885a140d0f50000145440185080d0440010059410400d034903503e5440f00e246540801c550744000656100c002101400c2c01290580c040540f07070302042c2c0ca83d4517542c1d110389a081025500303410383c0c400924404168294080d03800300004290140200081d00f030751500190501c001c5902c13881c3c0452049 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 910722760 1250 910721510 910721531
    0xe0d06060e07090f1d0711030406091d150d03260a0e150a0b010c020a0308070203100203070e0f0d1a18060405030405040b030304030803040f150b030c040b18010306 72
    0x1200180210034084d0042600d02910048540641c14a01c03502403032140115a980b4461505000032880046c2180e81d110341d902e0000b400000c55114681140c42d100e5907803000c207000c80b60900d002d400500074504800308258100301e08049900d0341241271050b85981c0074280c4848800040c0c00c496441d02c0380590f031400410503402c0d12850525000280c0081e6424a1400042c102580c2c21950408c4001000c0340b1201c0182c071b21304400c2802035400840d04c1c02c008100003001c0001d200c140d20940940702c02041031040c1c102070307000a58410001c2103503c40c8007802e508180401d141c0000c4c00034040c245110711034403440300c0c51020100c50f68190b8842401c001400301c0550341042d941c540807008220034075094036526101d004034081c2d14410303921400402c81b2540c0410644024642000d1080d54900f07042c80c01a4000c8031011f0300329035102a21504502d2480c940c80340714403050005d0054040581c01c40c042000402881860769408680300d5014410b8209882e81c85020318400c140000f03104407039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 910724010 1250 910722760 910722767
    0x1b03120d2c150601020114190609020c1c090608060411120f0709080a08161110020115050136090e07030b0105100f080c07120c02040c110304060e0d06060e07 69
    0x2c003e40d065a04040f00c136107002c00810704295002c0f03405850808500300b65001c070009085540d00c40c1110b60700124814100d15130128100504d00c0704483711460700103054030143da2814451089401080c803ea001518500303060700301112055908a01d10f1a200c06a400c04540004c2510b18a02c803032112020080762907046141280a00345401c01440100115a956000e034800c2c04a081107044540c403429042200050794811040e500501c038a00600000d01d00034002d0458036080a4a001c0d08440065079500960215600e03941d0b1780300c145140c8940010b0711080011440c05400084d2811100141500d21485260005802e9001902840340303142060102e600c0c040e00420705c43d001e160f111012b1590803041d840b24004640c100403026070380c0d124940d841c03405402030181540d082c00d0005100d00d94061019001184200c6040100c106c00a000f1121100c2e01d00c0840541d6000700024001076005036183d030b0340c80e034009160701d46001d41030b078444d402e031042c0d6440507040e515807605004510b40c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 910725260 1250 910724010 910724053
    0xf0406060816260109030503040b0a061505070302100501060c020f04061409040f0c15120510050d050c0a12051e0601030b060d0c081b03120d2c 63
    0x1036000a2030418901455020260528411803928280d51940b1900c000d42c0a5040c05066071184005c020301c610508025005501c00c0394211481d0440c0380000d5403c10141c803030f50301580c0d094903000d080d8000782482580c2c19401441d0560651040500708080494070703000b400e0180010759a003200e140c05510511a026107184403561003a41010f2003444020200d910841c800001190090150345507400d0804090001c808003400c0340c40110404112607007044580003503140309a9640fa2a110501810b4040300c0c000d6402c40550b100445041001c1e251000f0150341c924058002c1da000045000000348035542c00d684890356407503007010000107015003440007000200040320102d1015141e62032a175100d80f41400001c1c90f4070b100001050b204c4d01d0340f144c02e0003c40e6008030004045516103016079580e00c240007007401026100b0300d112845007070114400000480c070103102c41c1014640c02c020030140c441080110325000b280000742061900010541540c0600e44001d0403c920211528000150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 910726510 1250 910725260 910725269
    0x50f030a050c091b0a05030423100c0504090510061b0b190f0504060603061b0903080306030c1c060b01031802090705090a082d0d03020c0c090f040606 66
    0x40009030100080750021500080100045400101e10b40c2e400300d00300201c0103005041c2030701c0300c2d011803183d200c01d4004000b90f026900880707545800c3ea41036402680400828181c000250b0001c04070b640c40700482d80c2128459003441c6c1802418252208440002c0782c0040310340307501c00c034003a10082000c250050405003040c00303022000c030320340404d54503041c401c1e903000b5005400b503d4000068060110345980181403880c2c2b114030900c030504040c2044000b902c01e500065420b20b03c2d14000c28080c800d24407451001c40200e8a4002d240b80c5180c8600959420003020b05406001d1b01400b0340280d5074a08180491070072001c20b04030070302000d013014003ca480c050040d505040c42c00200745100807400e0200d502140d0b04980c10495030340c6290781268180640440340303421204c1e0780700c0032136a0380000c600080b00b04480c0019400d10305c028042e030300603801000c1c050340840c0c0066404082c1c01d88260010002c2140102c11200c001c440407001c1014042d08503040c0c6083d5030520180420042c1da80a00030050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 910727760 1250 910726510 910726513
    0x120201020307051605072c06040209130207020d0506010b0d0509010b0d12020109060e030c06060d0b040b10150923100f110604030c0b1f0303270609050f03 68
    0x185001800074007244a5000c00134082042018001d04101e0104125001390180e11041012100d0074041781940074040b408913030903149682c00080150400d4420f4920400300101102d2200c0c0713071114650025440717070a09903004800144071202080040112600800c1030921150340d40103840740303603000c586010340101126410101e00c1442542c1da0710310703038074202c0d00a611282d511100c01c809900402040200400c000d040c401880006c003004006414410f119009651b0540e5500e82004904501082c0081c070051003000030801240060754501c0e0300c00d1001c0f11490050307490f62100e9203c06500c000030000039401d01014001406217000300320250903c45112010300780c154002544a00511154100308882d0950031013555229445140e0f10149540c1075981c241410700f802000b0b00c0f50003000b0388100d42e5a4000c01e003a0350480780c660140c0411544400d49807400c40c0d0702124415062001140d014640c96409211401e00800d00d5005240f280c0350f48890314684414840728038000c000d8136219 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 910729010 1250 910727760 910727767
    0x5030613090807240c02030c19020607120c170a0906081b0901050d02040b0315010801180519020d0501050102161a2101080a0b0f04020d060b1c0f12020102 68
    0x1030b49902600d0007079512044050000b40101d0b200e100c18803542424184a605052416600329000301c018000f00356000269038540c540c814980f1003900b85100c00a4002e00c1c100031b07d03c08550ba260306984034000600c2c0c040c5105c0015260002c5a202008a2226454000030b14508090304403140c0c4000f0401d50500500f50b2500380d0400d00740c0d40ad501894000301e240061103201c168030039021110a140c0c0c80c50110b49854a4420640d200c1e0421180c1c482d12600700e00400f032196000e101c9c845d040300c01c0105580100c608120303021001d401f026150a02000f081441616401224000341c4004450080f00141640c90240028a010f40f102c440408811811005100c00d000890607000a145491200d543d00c0709003001440b0b200300068450300b10b40800300000300d1a46008900c030418180203501d804041e0b02e8412080403480010340700258881400315a01000502e40d410003680010000c2403c003100300c503400c14502103030b14800c040b01c10303100d44c0340c00108202101c9603601c51a0001e1008604 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 910730260 1250 910729010 910729013
    0xe1e0105030708040615080609061b04120f0f08031005041109190503030403120201050709051f0e040c26060a120c0b0f2a0613020a150503061309 64
    0x40c400502082c2c00c0082c10b000203418840d181c1c0006403242c031024101c0200b2591005125100c001c1681c1d145c11030f004400c0400c01a1410400211f908d01a400d095807070545000b003003140c08059850308651308486100c06034040343c000c4e0812140b031401984c0141d541c0c40d110302180c4180d505a04501d20075032601c07a41c0380034141d000040e00c035100d40c151907031031400300c800441000e00030702031f4005a0705210018010041050300490980d4004440e002408aa25800340544401041d40a102d030800440010b245601c0e50851141d4450031082c1402c448201240c40844c040d00c03032042d1010040341610700c3c605102c2c20002061803c1e0720040070052007030301746407000500c2d002e114482e243c9103240b001c810005210303000700b00707000500c0032003207050791148002282c0d0400d400ca1925014100344030055103100e021003075010240f42280c0300242065039184800347c6600d02c044103050741c10084ca501c000caa0651805031104040880c0d0715272580303a25024003048107500c00070b10000342860815081c42c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 910731510 1250 910730260 910730267
    0x1030e0a0804120606050306070f021207081c090203010908030603100203011211130608071403030a020c121006080313050303071e030309020d0b0702060a0e060a09140d0e1e01 77
    0x2003c1d9070b042000c100204407213007820710151a007034000781c4e4503014950034806c429402520702c5041101d1038080c2c40045000b1425012240160100134080c18420441281c09038041100c1e4210080d403203000040030566500400c2c21180006812990100004140b01c003a01d07003001058404003592009510b1507042a1420440940e1040010012143c035142000d250351444801040700d40501800c02c04169200b420382d9480120748140340c84000390ad6641501c0f424044120780c2c0c03101c266001011247c10050500a903658003141955482c040c02c1a1607000c2c0c40e10b806240003c281a500560701c0c0d01103d0080340100c01103612844c0b01c0c1e4003c124050024543d0258609000ea0003180c00c8a6031581d4242a0041d122480d802980300e18248000420450011301e414029a0302c0d600311045079030359150413421200c50389018081a031040300000c90380c1100d90000050244280e2900c00031480e405a000e182c1902c200e241d2010940c0b00711040c010782802046980190b92880001c0c2d91000c0e2400044d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 910732760 1250 910731510 910731517
    0xc0718061833060e010f0c0b0603070f06050405030d0c0c03060c0917011d011a06070204020d11030a1808040b0310080d030b01020106080105040c060809100204030f0201030e0a08 78
    0x3520761036100a1120b07102d18048900304080c07407a1540015a0280c10380319032500780e800f540c40031413400b40380c0c6151944a080302241c100d0070b5464021850703189880311480c2542c0141000c2e4184284500401c0740c0042c404c42c00024050380d25020b4969050000300342c1414a03c1e0780d141d0820003401034510114900c40c840c0001c59820800c0002d40014a04d421111282c01d030b00203141054030b00d408407030704000541c0007201d034030a1203884403118008152803a080e20120020b40c0d10042c120034410403a4600b44005250551005000510b0000b52203403000a40ba003a002441c400480070041105000e09130150100612003120003c4c8140d09640e03801c134240c000c50050800c1c10201100051880711b40aa00c87c0240c40e80e80c08480c202c0c00241c60081c054200d00c3e40b040d0042d420010001450241402410b01a40d07000140014842c24181e0444801d0300090140141c0d108000548404640c20710062014500071421107074400c2043c000502601e01c0c581804180b43d00468109002c164090241e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 910734010 1250 910732760 910732799
    0x3060408190309020d08180f030706030e03090901080c10051e03061831020a120206160c030210110703030e0414130c050607081206010309080c071806 66
    0x103141d0100d1054003100204250071000b03400c031140b21a0b00c1c05000ca10005030000801c51141040d07010108000e11198400c0781d441150540d0140105200b03481c041c0d00a040c02c50700c0a001c403400c286490300000c90108003a071100090750004500d001c403906148514011610041c1086450700e4407c80100d01c8400c00c100303c64000010100c040303101544c510418060b64a1018411001c42c104602c0d2100c580b5000e2400c510140040729003113005400311986480c1051700102a176200324540603120f00e0010561400b00d91002d020007091040b00244198030300e1007801018003c0c527a9066205111590010410707000612180b540a11510344000420b0700940380d0524050038601e101c68040383c043c1070344036002181c0001d120100a0b00300200d03100b000c64103015480c685a203035502c00c00d20a444c42021405841000c0800000d02c0c10f03c04048840d812010600d00003030304900980b2188240d4101a17078000198100c100c0c1005407405556405104130201c5a08000309443c00646c034a00d05403e001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 910735260 1250 910734010 910734037
    0x230906010803161e05010203090105070e0d031706150d0b010f0804020f011110060e0a0c03060303081b070c0e0a05070810061d040617010c0c02010c060509120f0c010b03060408 77
    0x9292100c0300b0104407203113465a00000039500e90420141c0c03c0d010b090300704c400100240340f45903025038603c2c4c0030344942c110716015251080c06038130800c80c4201c0d50000816494021118050900c0450a0070006024000d81f00c400062442d80050004021805072042001005540c43c144000741ea100b6000c00c032002024201a0300d2004000a01d9082c101c41111202030549082c1c80040c0ca5041c40082c9403145c0c84010b810070440c0c5007280c066080719420f01000c0e001480240004074205e10b00b4235241d0b100503400414078107110740c5503500320380001c2581000059000b07420510200d40010300406070809800c4c240b0403d90302e41009071000b8203000c0e06c26002000001c1c85100e4040da1110f11200c03074808050002e208040d241c46c01d0901c507140d480d2003103000d9841e100c5aa02003e10078400b1001441d8165a8000c5044e80394940002921000d803c12119000b1005080ca0076944800241000035002102d25113035604800218211021051898000d80100003003000058110084840708030f04100b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 910736510 1250 910735260 910735283
    0x807021204030c0e06040e0304060c0c0905010f0b07141212060f0108190b100513091a22050a0501051201090f0803131403041a070c1823090601080316 66
    0x10001b60240c403219001c84040e000010300030079500da024141c41c0d103143c01850400c081c0c0c3e039a60055030450b1800d03c1400b00c4002d00c01020300004140400409650b8090040d4000f801e40000640d0f080a8154102551008000568619101240c46c02c0c541c081c1c1c007140c0040e0b0b41e0300d4400018007903074401011445500100c10101c158464554440e00650401034150000030940f54405047d603480200d041c080d2180400e40020ba05c065070007103070004c2000000007818408010b041c00741045140a8007004050b40300c0000c40c0d1250b03107100e1544070300303500c00b0042000e51600c0b05100056000d0240081183d0404000c0e9000c1400c3c00c020921142d03014091b81e903640e8819055000d5200c000c28002c100c07815900440c001854008050000e40d030a901c5c4040b9180324030b1504890910540400501444d4100020001205010840804070290034400701d90030140700c1c18001c504018600035022540f04c0d5051010000341002614090300801c1c00661070100c1d0315071810f4401010582c010020f01c2d451 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 910737760 1250 910736510 910736521
    0x3070923010e040b040609021911060907030209072a0c0b0903070b030402150d091a070f030f0e011112100323030f0703050a08150114280807021204030c0e 68
    0x1b540900000e0548040071074407515a6440e06880c2528a040d0300000b13900c40c00b00402548008c10500d0103a41002e00610381c00f89550b00b8050f0055000f000042402203102581916400010740b030345600740f10f1620010705005074608003241822682240c10010000c0c400c0100a071800111041514070020703200c2d840743d48900c000358540c40c0d200380701e810030b2001040c4c21b9410900c40c2c1101e030391144200c60510700014202c00c154450142242c1000c0020300c2c101e10060042c0c02640080c4200c1e060b00404a01c000380041e0603401d60744401401c0c10b9044002404a0400d501606040c3c0c1100741d02028441032031a580f42e000b0000e11200802d108034501003285640307448100102c4103c9241c0a1141da202e200b207050140c141c2e046281000086000c401c0003070311a4200031708010940300142c645030040d00b0405150f20040e000f8000201484042a4501031049684645601260b81540c5c0303500461600160090a01c000da0820205510307080c001800020319903e11513040da009100c4015090b55030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 910739010 1250 910737760 910737769
    0x62d040b030f0f0304170105070e010f02010b15070303150e2d0a0207020f01030506090a0c020c03070b03370504030203070c08010516110a12090b03070923010e040b 72
    0x2000400c050b03c074001c051441400e010000d0000c0b0364070900c8078114541c0000d88142640c9049071408000f540813030144030190701034145409030980c9440005001c6d80c204012801e0701c03281ca1081e2100d004c001c1408020075916005011180d60301c031104082c11032601280f102c7c440d10242038151943e14031102542c0c035801c41b48a200030307a5160600d072520350400c14501d0000b503000e42c0301640681d084080282d02c03540a4003c0c03501400e405400000c80e80da584681c0741c0100000451001103008024804520b940d0400141000c0c01001c0102035490a1000b404050320202000c95035a03042e440c102c040c02c04c1130380d45503900040c000800c04102ca50326844d041b030961080410040000e50351a00104031010158829441030015a0000c8007001010001756100c026188008866911000500000440000712118034541e0743c01c02c035405030348401d4110303041c1c0c00403a4003000040b0403010400504031712507910312044500008c105034000164000030440850076032a140103a071607a141d08800d845 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 910740260 1250 910739010 910739023
    0x270311011a331c14070c02040b0613232205040c05030109050106031403121f050d0501021213051c023a08010510030504020102011b08062d040b03 64
    0x1000c242056682901d0f400d10241c80c102c0045080c40d5924080d20340305040c621910060040c0c003152244402401d290b07003084050046200c100350010814021020140040316542c00a01a0301d0890044007065180070203c558200d140984200c03007034400c00e50710402c00c4d41c52640141215001003030076903c030300b00141110700c0e0b540040e0f0158a042c0e9030900340403040d4021810307644158502c3c20b0244e4100c0d50b2961f40d0040348424104440c41c2c0e00070507502048614804507940400d240e0b4902c0940d03400000300d50100003102a21181d400041c50311580c04c00d480020741c02264000459003103204c0e5164143e4500c00d41c80703c100c61040c0c81c00e080b2891802080406040568401840f005421403100301c070789180c0d48001c0365420910340e101499490f000d403180c00c0c181c07030303010707240b202c0707500d0259811005090042e106a055558030a00d02010300d0a01d64100d02040e855103800b001070600038284040c840380f14016282c11030304281241c52100100030404039013241100e0111b080440000000e0402a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 910741510 1250 910740260 910740349
    0x15040b07120302130e0a0c050a02030405190e040311120f0316020703080c010c030b040e0312070903290f060f0d020316090c02060903040f0603270311011a 68
    0x8281150024010512000340ca208150b203103000d04c251f94241d40300b50b4082c045c00c070036240540c005220612040c1010b0b031800e5103090030f615220206c55640c0f00d03110075190050740c0560009620034088050041c0810401c0403024200b20303c0c0740751a4200c0c2c8409068040640881c0c0c0d81c0b64002c000c6841c07140b0030403151024540140c009980d41e01c00d15140e5000b802c903d1a1000800c0c1450812030040c41c01d0310400402e0b03c0c0c81300245213040c4220581c1100c000c4010100c0b800d22003800008070100700e42c0e103940c400e406003000c00d441c00c02102189081d64400001c01c00c045100c825010890961984a240300e18203c00f954220480d5166200013030800395050140d104110f6800c40000e11843e458012090341340464080c2d0306c054032146081c2d030b22440b0f0b9020348441604269010414188294000e0009903d03a12000400640110420040c0c0306021425000560202003a6218443c28414040001900ca124101070300b071420218001c0386440c2450000542c0e0b8003001c1100704041c0709000c1210313 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 910742760 1250 910741510 910741537
    0x90d06091416090614060310080304080c090f2e0e150103150605180105040902070303050405010b01170c030c071a09070b04030302031b010b041a15040b07120302 71
    0x3980800900c42d501c00a40755024244050340c1000204009140300e0f01060741e040e0220582c0c1c2502010a02c44164006480090100ca0300d0301c00091500e424809403001d80703840c1003d041940c02e07460400018040280404088031030540a110444501b0b4003003030030001500e80302c8150000c2208082035841010f0788052004e8070544100308940c0e18500e809040f159098804001a00000c3c0075041484024042c1d100415401c03c2880103007400c1d803501c480c4041d4145800b42c581034540c507468007a40c01c000c42c110046601e520038001040310070b0090003464102071031b0079100b0600c250160351a01001404486202b0783c00001300e041c044005040f504003039040720703403241c04111804024441c0700c81191400d1240c0146000410440111000c903011250164000c60901c4607da415019a01c80744852040c15981e07003400d8a915101d50041210006119010a0aca1000745061250700c0d80c5081003140703a0343c001c01c8207000c041407041c15a1013041d000410b40402c221440002d500a101da90106000c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 910744010 1250 910742760 910742783
    0x7050d0b01030203010e0d0804030503060f0d050303041406060d0f020d06021b010e1b040b0d02030607030b091b040315020f0409020c1e071a13090b0a060e06090d0609 73
    0x180050000ca8904a074030a600030011244003280c9a9215121010305800180d0048003050201e44554003941e00000700030b04032088212030100040129492010803292030300301204000c00c5c441c203100c5010000035008082c2c01740345041800500802d551900040442c5012556182951580030814155660101c030865032460b41c0c01307115003113404040300c2c4850b540c200800d8484081002c01d580e55290f61643c0c4171040304054900f003001a202080d012500f11901904000160b94200001400740c405a100000e40d000f10b43d0502000b018003c16181c41c5050502c242c00e6800c101104981c1226085402c4000e46151817001c040039100d5510229040c0402080c04204e080881d801030400c500300702e0850740c1942010707246404d900031100090075990403070b0404200042d5560801c0c2c010700f18a540c00da240c0101c003602007030303c60f9072608642910ba544024440c0c0c0c50501d441018017511440c00c2071145000740e0390004c0d400d807246840d810301460015103c501041220b410a450b13042e400a2400c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 910745260 1250 910744010 910744013
    0xf01020c03070c0b0f0d0902030c040f060807170d0e0a03061104090f0911040c020f1b1008190b040908121015050f09060405150913020405060a0c02010207050d 70
    0x2542d40014030140e07007811040000103000f1410f441120000500141c43d1401c0c0707640010505c000384642001a6014000c0c00d81c1040103a44e00d11604d1245203030000c00146031410001902e00d0005207800c8804020304410111411540015015015907107a151898400c0c2110700814441030160b480107012a081c880a04400560b4034094020303184100d2040100201d59211042500d00d4900040d11503440c015136086c0908054201e04588103850045810000780504518a8a081036590b403010614908e0040c003949003d241c0324a810764245401c0c50b45003450b120742038082645810880179a60b5070480000552201e40002d4072a43c0c201c8240394407801c40300c0e446a0040710440d204100110320346000f04003c040c0101d99181746500341e5420f810003044008008040c0c2c8991000342d0f0103102800300044aa076902c0c079809442462012450b116200c2800303020003485030603a41c1c3c14503401030009006545441080d6941400586800ca58075482c500050381011420380040e50006000c000b54070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 910746510 1250 910745260 910745263
    0x1e0f030708181c122007030c12031b050c0d0303020a0915021b0d0b1e06090103170d1e0b0f030309010801060507060f0612050105100501080a020703020f01020c 70
    0x8950700a60b40400e03080c103041c1042503044401d601804010104210383d004100040d0442d031402c00700f4106900701d91940340c00c04070340184800c880510b60b4001384c0184100b04441a05900a140c0b1000140c1400110740d0003030030304406110500c02c811010030301c0009000341040a02a0500090840e0160a80c01e0800901a6101c1000d8a020070b40080c0001010460507003000d6001140b80e028001840020005002034602507103100d90003151070800d0004120445601c9001c0c0c444c5d1a40b00f1044110040d5802c00750304001c5c15148500f0b445001003000c80e6108180d161051100c2c00d01c0c564410901805200500002c140220440c40c20030903004442c06540c403038030384100308641003064002484101503607441244849400100c08800400c01e0501501c00b402c0340c103108080c0030a5a40c8000501411142194803181c42104204100014864280b01d0b2640000484524404003401d04d00080d290f80c1c0040c044060403030f40080e850090602c00d0001148041c9103000955a40b18001d1400c0e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 910747760 1250 910746510 910746517
    0x6070b070809072603041805070f0908150a1508010c02070920070201020f0a06200711060c1510050907050c10090602070f0629031e0f030708 62
    0x100c0c0031518035804907850040016030300040322281c0b40102901042c0030310ba08a1108500c0f5180e04030711003800045241d0082c2c1d400c424454490b400000b4141c134050800070004400280000c2c1408003240044c800c1110102d220b901da4050b942801d8032a444817806a00148080c2101c607007a5200e580f00814017074019004024650705590032901d10a07140e807440d01c09c4480c2d22442e1a10f500000514160650300c0001401c1580d00500664044a10301850707175052043c8070204a07000c035031703810b00a00321402440e141e10707640c15000002410503040340d0300c04c540c41c01d0406e10588500d0000c541014203400820000f5400d0796121184c040d142000d00c03440600031414028284a40c80c0000000c0d15244a01c0a4800b101e0411008001c0410081c401000400303507000e0541e0702607000c0024202284c038506136400d4030ba100704800104004038010903080d400c5880102c515101e489085c0f030040f641c00140c2c900c1d1160000b0034034580304c1020142d880c07824450101c3c8041c1400b006c61440d05018422018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 910749010 1250 910747760 910747771
    0x91506071b090209062a0604050c100306120f0602041d0901050a05160f1202030c030702010b010503100620010507050c07050301111918140307140105030c1806070b 72
    0x100750510b0329002c9020503801511103140e042001402100101b00e009112085c41110780c41c99041c80740340d81d000c4203052001c2150182c449901c404000b80007030504500703284282500780340400c0241c0c10490300407402c0d401c24901400e03000340b13000928240032140e81114000c00e2301c0348200ca061103c4080b4520000002c075081c2e2000d5190500054040002d8020320f446503144020500c0c08001c5030307209903622201d56500108101010700400c50b00c0c0086c1c8000c40c090b03002040c8164992074881002030035235110900750307410030070240203010f0a0910a00404103492823800e094004011040c0c0c10107100340da08040902c29802c0c50103009699070000020494244c80d031042da40b0081e03c071400e15098030b0550008607140301d8100415496060038000490310f0069034a050b0380388034403200c2502005003c60700b0010520900130310001f1207140c1040200000c000c3c4654880c0c1e2144100001380c41804000d181c147c41110018401e179112951900c2c400526400400c2d0301d0300ea85550a00407044081180e9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 910750260 1250 910749010 910749053
    0x6020d0b0a121e0210082206091e240209030d03091b051005090118140102011401080a030e120a0602130605070b061009080609030a17010f0509150607 66
    0x4083c0c00003606031928004041c3c02a01e50300c12002d40050031200010300030150500300e00342076455820b140811090380a8540104004200c1180d9400d015440c2d8854800070030010044140340d600052002c3d0071400034540546400c1c500d51420a4180c01920800c55145e0f89070059400380b41d000c42e0560f10102a00380543e04d5007101c510088400030030700c009030241503071101105840c82001c51040300200203040041c54103500e8005041110101a100d030f41000c0c114100f28541e407119035909205e0300366125100d074000420b0b9490030f08410f031a0299910f0140030001441e0154401741c8450f1100320110b01460116030301d034042c0b401e10200030f41203c10002147c2c01c00c0c1c0c1d000126584900291512550014610403443d00c50008000070403801d0714201040c42360141000418010138040c10713100d401008046c66884040210042c20b0b0110314001c0c540704909280140428440080c3c2102a00c1c01541d600005d91140c00030a0044681d0898041d4880c000086100400c0442500b44440e02c07410f42 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 910751510 1250 910750260 910750283
    0x607080105030a05280f14010b0a030c0b0a050c0706110c09011d15060c010e0f012f09130903080601021929070c0b090a02060706020d0b0a12 62
    0x10101903c60030401d41c05026030303110680340380544800d258040058103002481c0c1d82c4c44805507a0b07410469041541c16101c000b150f50914007405828028505030308412584034606a00310342c2c0311030206490b8068a10050004192245000c0c0130354215000b1002031012507075183e07039800004000401c1048600d017036000d4040902c1c070398142104101e05a03079002030801c105507007404229118181c020204440811400035001c102d0319402c004080400d07500d000462030220f2102000d10340000c43d5000d04441e0f240542c8030700d0600080020401040190580c00505071030220850000e019000310785900c545030500b450b6034200710303074007001c80b00b031003512a4407450752001c00590312403001d10850b081000420510314000b0346030591104820310100b107031448080c00b648151010420817904180807171842600c0343e091010900180394001d03807201c000c000c600b2041d070100b039481c061075400600d010380101e0107803102c98580c0c02002c400c5401034400c86045070b4400d40107154070352800c0207843c00540d10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 910752760 1250 910751510 910751519
    0xa0b0106090503030f040902070507170309010e030307050c06030c091801061128030c0507060825050d1a090712060803130b07080708030a0f0e010b0307090c050c060906070801 77
    0x4400e8505d84107000603880d040514041d4480e0282d40328490841e014000c00381c0105403114150310030805584960020b64440c0d4080001518669120340c00a120f58414800f003000500009030300c2e00c40d95825240d10b5129207500109010f00d0107012302490b4400f9811070100305140d402d081c030328101c2e8040d50b82d80d1420420035116940720040001128082840307241c0444054083daa400c0c2e92062007882c2c0f2040c040c10070707118941403000c035030000000a1444400d01c038401d00d140e074007420901d041502121200d0700c50703d8050030301d10604030400d5500741c03034000d0103030149030b8108060315544d4007510403840fa2500c03810040164210044410700301d4074105001c1500d060010030307607003284280116003607414104000382e01030b500068411511030004124900019040340080c50080c600c102000c1b6a42020054607002e0b2800100445078503807425030031021a40c1c00240380310895000c01d000040802418030211031921071055106403d1050f00305003c007131400044d101d031042c1e0003952502039990303d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 910754010 1250 910752760 910752763
    0x3050114060d0c14130f0e0c0a08030a21020703080711010606170c19021b0f011205090c040212270604030503131a0f060103051b07140a0b0106090503 66
    0x42d2800380c8078004100301400601440b462a07420702a00401203c600015801180250340c800c0305525511038444d1890144001d040140c407900c40340c11a9080c0b4a00e0501c400540d581c018050085e040051051818507140081d2410710b03880e01b004001595203000b20f083c00b41c0aa0002c1c1e41c0100000c1c0707058042c0004200c1072081174281c560725907642c1c0c20b100014640b085007640140c19902d003d20108a0100c00c00c00ca021050306420803a0042d204119900c266000124401303961180112000b100b44d4444d41e901a5410401201c4224000b4075a11107040e0107162010f00c050780358000d4400510400c015404c2d5110b144140c4044c400c500400b01d4a000189080028140700c0307440f94008001f00d000207000300c01a542c0007042c060351012014030f944420071182180d03610620703c03200f0381082c400c0000e11a106954000d50a084c2440b05080480c40c2414020001d480c40c01112008034405041001c9658503290502d046000c88a0441d898100180d0018081c07054002103216000002202d080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 910755260 1250 910754010 910754029
    0xf2104051002150604051026190b1e01030609060f06060c0501050105120d0c1a13140604020109180b06180109091103010501030b0102030c010e1c231309060305011406 73
    0x60f03511500118502d00303074401c4854441e88c0210929010500c8004240360801c1040000c004001202d4040070021070078100300007030002d40304140301841d200c41e850140d80e0101810341144d9001d00d000036282c4a50510000030140c01e0f805281c014180703180010101d501451542d4040c0c02a0000c10144c5d81c2c8108005400d440c0c1d008035480c40e04102d01c00c03420240180b003c00080c900410100c400030041000b0b40846000c202d60141c1d595071407070131400a02c0250703910410024042c0c0024050303400d2540010f810200d032440307046044403440e14922420113060700f110100400290009071954200200c40c201110202485400074140440c00209403030b0600895115082010040f072075039091400440280c100e01076a41d040d440200b0102400503424030981003002440d01c003401c03440c564911410305080e0541da02c0c40400c000c1c07101c0c040c10002c545800e0b507440d00c0b03c10001e0f41e8981e501c02182c80c24246179400030307504500d000000403d205064004214580211011100d1950380300208290b06c1c0303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 910756510 1250 910755260 910755271
    0x80d021504020a120f050109291b0f040806011403061027020f07060609110f0f0a031119031512170c01180b06030f210405100215060405 60
    0x8001450801880400e04540c90038a03009080150700d2525a4a810b03080d10b8034860110350440b0090000c4000c04541600c1492765140c21b0864541420050b019522600b20f00e008080f080c040055180c24036902c4504440080c2441429107a01d9a0742d40307030300541c10300701004260290140100117100300545980344e406442c1d100c00301c0204045010361264500e04401c113020f100e240e08000005610701040b002d0034000c0d11841c00440d5050034203a2031019103c01d0a10792149900034030010889810407407d032118000400030003911100314500440103400114289121644001000e20b8182c2800448031604c803226141402950703141078040e0007003403092181c0a100008000c00c140003a5034141e440c0081c07224045034030f0a200b0301034a0503003110507000c03050028403420040c110402650050321684140304501070514653100ca00d00d075850302003246510031807106044010085404d10010b0ba0f010306405040c48041a50104019603552804002007a103900c1490000701c80f4a060b00401d8401c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 910757760 1250 910756510 910756519
    0x30d05010819032703210801061d18091011091305100905100609080607050909100b030f01081b06090d0303061e15110a02090916080d02150402 63
    0x900e0ba41c0701203a03e01442c41e552000c80d5a120703121411841a000c61101450148410740310016800d040748800b481600b21100070720400e040100081031300400d0318968404000f01140480d07038501c00140da080c0d0ba01d4928903e501d03051050010810000a100989010a0740200081c0b085020b038049540690124558003c0340c07805410000001c6410060704042111004040162500c102106880c01150208400796280e6010410164000b012400410404010f00002d0a1603400140144036001e4120301807070100002c5505559620500c80060002810282d22420008600800c0142c20700c40d1400030300c12070050000180c2c01c047c00c0b1401400090042c2c0c80c211030301c4c00f80041c5600301d0f0804d41c281991284005400c807600302d40300c00c02d04402203c0c1c00945041c4031030089240a01360000041001200d040300b00800001807244119404482543c6203565101415142030f0032107003802000b20009500144903100000c164120f0701c1e9903001c5da918030b80d00030b002035480d070b40480e4080d612 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 910759010 1250 910757760 910757803
    0x40b060a090515151c0f0f0621080c061302090c0a020a0303150f2418090902040b10020a02100215060607022409040609090308071404090e030d050108 66
    0x1490000e010004d1141c5140a0501301035030000310a0344281e40c117600c000e9540d161a100d4a0a0f20301d41704003440c5d03658800c2c2c2000494280001c00c0036a140c440342260b2068401512601030146550030341c1c0c881c0780c182040b90545c0c540300030a0000080031040485c09a1004000b243c440402e081c01e440c561034555000b0b01078180a518110054a4058880030301030a1104001c10042492200200548592074143d0b5a40790665060801c0f0200407804004001d95030f0b80020a419a81c04446c0850b0044107005c50289a180001401007110350a0254003403445000311880c1500412498401c6008440c6552088000078003aa01c54050301c50310141d07580c400340058602c0c40d02d6800380c05000d0028114000340101001e4580c2101440710542c3c06030840131a020340c051616004940162009090034400c0c2c16503a030b80030b08489005030103401440b181007100d403c1851190103850081c2a517000500c80c0302452040542c4075844500700340291810000007144004000404900c1e00c50740d003c41040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 910760260 1250 910759010 910759051
    0x30803160e060d05041403090102120a03020409061e0806191e0203040c2412020726071103150c0a1701180f11040909140105040b060a0905 61
    0x31544020444105020000300c03001e0068444070041c14000300f20f0300d00080c6504060800c134161303250800308181309a00c1042302d0038007a42d000c10003c2410340348444041c0c9680d101c1c2001e401034000c1da00049001440e11000041039201700303401902c002d03002e0005031030060f2500d08264840d5021121034105a24540d400720031540c095210007010740c140c0c01d541285440d501c042000b6030340150b605813014221a40c1c18800128070032092030007040d803401c1803d001c98404401901c502d0600d40c4401800c1d5001c11540180051103699081c009440410202c14084081c900c010301d0300180340a0300c0c525002c0001c0c1505040c005100848038110700001616543c44402140c0c0076445000d5103410412080445000700824801c0240600880070b0b203218403801c84101d4008840c060101d041030b142c1441d420740d0700045107000321000c0ea0780e040c00c003003607041e900d003081000c8201e81c0c8880340066180a04200030320200000c5c480c01498111008043c2c0c03540d44d01740300150f40042d80d034607102c99102d495800307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 910761510 1250 910760260 910760281
    0x60504050d0303090203010c090e07050c100b0d060e0d02010f06050f0609031905010b010e04020711010509011b0812101d040201031811091e1305190c0915030803 71
    0x50700352081c9070209022034a0350109003541e1400120b1000b103540450b0610a440c1080b010580c0006140380550034a10300308012503a500c900b802a220b1281d440d0580d400c0741e02c85042980403aa0059401c4c44407440b082e1000703586640c5108090015442c0210762403440d9014000e280880b03034010082c0c40035044200401c03140c5c0e8401105598988650622101c822502e4442c200c9a140076000009184d601400050075009022281d14412881042034000141e80c602081d6014034083c44c0154803002c0c00d40c01602c80c0361100c002410881204000d240801959a000b400484120f15a0203003d49038141072802640590044065030303280b800c4010342000007003103202da1040c014900440d102031101006c00d80c030b824040048d640e0481c512a080402e080001d03c05400000d00301600d0001409040e03001c0401d00082c200740c07055001c1d6103d54040c05010095000d0300107442d0b407204e0048540e0710305580304034528404d644032a401c045060829000410000c0304032038008003143d00d90340d81c0b2248031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 910762760 1250 910761510 910761529
    0x1c03030b0613231e010807030212040303150b040f0504060b0f0403030c080f0a02010b030d020c220204030618030306090504081204050f060c070209060f150a11010507170f0106050405 80
    0x82610b5010f10301d98826640d100c071820700300d941e1000c078032459055000000510301c2e6001880b55045c940108216030900004030b41d03003540301e905841c0001c4c0e4064091000700284520383e2100241120102d0082650225040e20a0031118211000c020041d9551244111801040090355802009106c100b02090048041d0718140e8440c1036080c0c5040185003884c4426040b0a00010040c1c1d0369a2807141c80f810100101c410454a070b0000341104c40846c0001085a4045504811544412010325030300c00d03010b4055030003031584002e00b4800100e44000c18801045e03500402c0d0000b07801c1c2080000c1030151481064012500106520b00d041c1084400c0b0800d800041c004548c503100c3c070012195003110a0080074000e1804005031561412107004000701c418029008030700c02e1000641060031666083d0600200140b240030007519092882403d540102400d10000301c15428001000130b4264001c10110150740c062030143d885071202c503007805180e9024019003010501c208801d202034581100c1a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 910764010 1250 910762760 910762799
    0x60904022107050d080429090d021203030115140301061d0d1b1e05100c0302030421030815010e01110703021905090c0705060a0b040b1c03030b0613 65
    0x101c5400b2580e4002082c0030351120341c025502c00401080500056202d01074110031500c6c004860600c120707100c1b80300021803280003013035445001d003225680115214079414000c04544441030726125a5a08040d004600c010b5462000107056502100501c51080003500e040e07803815520007940840b10595155950489514182d000c82c04401c40c20000360700040c451001159205a4030225291060151103409020320225100300800c10505c01600c0c2d612103030031040803d02e0b04143d10501414103905506c104d820143e03000d003e00b2201d5070300400c503556105603207100f075803100c1c1c9654440c00d1107100703001c1d103581c82c1d8001402081c6c0602c3c43e61141e44403d100410100a446a4650f02d0740020048000c0d00709a4400101d9044108050300c1e048503250b510405104210349000341e2503071160b8490707000800c250183d07541c6c2e00f5542d070183c8072607011b07940c01d920103803000741005400c1070205043c40d0321000440000e800c2c401134074014100301080d11400341c0c0308005980000d082c122031071300c2e40d6207903010b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 910765260 1250 910764010 910764013
    0x80402011b030306170c01081f1703040518150f120106170d020d020304120f0c14040501060f0c0b0c0c060c07030f030513060905120c01060e0609040221 67
    0xd4400e15034103a415030508544a43c400003801494018941d0110710144082c443c2a0850703024628140d0b089182503900c60b01000181081c8034802c425104100f4458000d0340765811006a4904e06100000003003096800445a0188401548110300315000007100c200d42d0b01c0b02c040c1e008808500b01203000c6d03c000748000788007510911006404a003143c9946d804a00d0b1b103000c2c4039118051100a202c071220011191005d0049400b070113402030b40e24880d520454014a42103840382d0b045c009441d05200400340e000004241035a566079400c0d0007100900076552199280500000b0154054214400e02d04040c3e2142240804d0a41301c1d2a6001401444412841d1003001400d0f40d002046c002c0c3c61080e040e16003082d45030003517420f0003489036981f04500001e06117000103022031080300d6880c05940c90750202c0041020601498203134103100d0000b0819440483c0031801145441d0190485026601060404411a0760b80000c103c581d22060f00c02a405c4110400480c2000e202e402080c15058020380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 910766510 1250 910765260 910765277
    0x702060c0a0b0a200c0303010e19020d0911040b28030b0702070807060207080618010b0d11030d0c0f060c140d140c07020109060302180a03060203040b060d050a020108040201 76
    0x121000044541265250100d84d074800460700c505207282141e0300c0200c650702406003003100c50941a0785c1d9220601600340604d0207000083c002d203078006c1d540b041c05607a45509548521450103110b0103451441e100301d40450706003809062600345485008a000070003802c3c5080b4000d094000c000705204141a2110350b240000088045240e43c0c00d128060081980108812880c05e0015070170101b40d60071610464000e120200b108050000d80390f504909004490340c1002c40403160140104104000b068100700b280d8000c4041c4424200d1a0201c200140c09480a40603544030843d410148410001d1044c200300e0020004680d403944109502043c504100c60b00c210304511300e010300e0b0001000030070840c1c0c1b104044210780da11130440a030000011302c6110304003925540040d100c0e00f468045c2200705540442c40c54501c410f4541c1071800c03d8030181211031561385a08154021354000c60301031b140310361060017040403411314807406604181c0180107084880e003160700450301030310040c2c03050781089041b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 910767760 1250 910766510 910766513
    0x30204020301032108045d020106050918010e06090309100c2105192003040605030a090c150e03010515100e0415030b010e100302060702060c0a 63
    0x500c0114003840c09003650080d4034059040b10408548a494240f080081c00303400c0c4000561100004d4900359416418141c3d50301d00c086045007912a004020b40c444038500e21040c200565105810611550003400740301042c1302e10350140d00340c4086104c0c55401c07142d41400140182100c40c6000907400216001051031840b80b02e4031840d214040e503180d071507a000012580120315141c102d03520540b4160030071aa808220b40c881c0003003c20508030f807618036240301005901551141c0100c0d04825880000540000112000105441d100030440074070203960240d60801800c000054134101e030455031f01c06203540d40c4c1d852801d015000c035600c105c5100c0d207021408500c0f140026804240810180d440b16041d2017140105429900054240d842d24002c0180c021816140c0164442e908441d03410011000000070303010400030148240c42407018a0b0f64403010041004440343e07103040b04c102030101c1ca0151186900c40205030700720b1100a510100c20002c6000600300030015201d021951410f491a61119 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 910769010 1250 910767760 910767769
    0x10225021c0302061e130b07031d0703030810240909020f0903011419271a0c03060604030b2211031e0a02040b1f0e0f0f0906010e0103060302 62
    0x101d10440142c1c0141d0204000f1098035104190140700305100c4107610b0508444200d22901d0049024007441414000154030034002d411149982042582c104135100000250f2a1106110300013240001c84580c0401c2c01034268a9802055078070380d410f0002448544010880103001002e111014070019440002c1d0518407407014001c5000080c840d540c5d9038907540105802c46030702074507101145e02d1035001c0c0300d02c84d481403a4240003903a215070300081c000756500140b410400b40102d117450913191f40f80d041d8100003216290512000c0580c050540707030345039918032103180d000c2200d00d03603080030007448100081410400899003000c044000b4a4400c1d10484410200d96a6030005a07540c035201100c04a560808001c00002c0200344001f030000c02c180c106045490321003500c00a48101e4079621004401d664030008002e0000c0350190025140c0d609640250040042c0c5490601c40c18110200040c41e04004100707529051005086000c81da40702d43c0159409205220940e04155560300f0100041c0c07075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 910770260 1250 910769010 910769059
    0x606090405150a0617010e0d141b0d0201180503190302041806030512040f170f0303040c050102060709050102060403030c1b03082202100f030b04020301060e010f0201022502 76
    0x2003c002c041003480c1400400070140c46070000c0040305a00d04088002ca140c001b02d8503482c3c03031015140c038040d0b80803d019050311074059441c480464004d0201d281c0c0d14008000745d02407803001c0a030000d02401c0300020400100d90400040500341e50401c00400039421b18201581e244030400307080040c180340d19a1481c0c000040c1c240310305036916550350030600500104216566061050002e55490719040559401051f00c1e40d1280000d031402c05005e8001c09442480014166500007003100d8503441d09080c4105107244034810540035000706408524614401c50628084d6041a0001c117082c0c3c4513603a0031001803072001621400c010a602c01d000414101c0306505c1c1075a8020380d182e103828100310310550028403036418104080c894101c1a0340050b20f4020a400805e4064103000c41d822090346801e0700030340300100c43c0c103900600c00000400c05541000440482d08001e90301c1ca2204e08002d10240c0c00c07403051303203071202c0074001104230740c0382443c4200351a109581c40545104402403081891044018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 910771510 1250 910770260 910770271
    0x1005030a02041739010507020307120f1e0206090f0414090f06100528050a0314010f050411220603030806010f0f090b0d02160c050f03070503060609040515 68
    0x411252610440940d020400c0215150f401001401c001c0c008070407161039135442c0251418030001041d50010b550301400310000401000d14114000e00d510b00d400602c40034809801c0303e82809281c61404161450500f1024030b50f806410b00340341511442c10001c9002140300d21316446505c0d02030308070003c19403400d030b54004c14031040184045070b45500034508003800100051001080759604000565a0b840ca16000d410091a0003104541806894407010503640100c0c1d08070030030071000401c00825090058006228000170080c0c103140c1000c12080d1030040d6405171003a140d614401109141091103a0301180d0000300d492404029003424506460050b441680400d0a0714100041ca507045889040c480c40d142ca002081d0050004010301000928021044500c1001c5680304d84d01010781e0454140e5011389a0304140d4052030315004031420510b0003000d0103200b031891441d03d9814001481d20a56000402030f0881d6921001844003c040090043d9824480c40440c82c00c403a040b10070b400e0084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 910772760 1250 910771510 910771513
    0x131205010e1209120105040503041e23040c21020307030f0516080c131e050409060e01060504150909230601030b1e07031a1008241005030a020417 64
    0x5002000400c00400044008409146d0400d81040300060002c002c030360517075990601d01c110424a2141d803400300241030304102981106207422001054030003280d0f40440310211410321006074685021910b581003040200b0f90301c1803111700049046216000303990300410780d00e00020007006246038942922420743e60341d2403070158004d41207061030740040340c00c0e80040d1150703c2d18600880303803415020f811700c0752080304451502030301703040003051070328100710001c15000f081400490303081d0030031400610700404000d041d5842e0500020f82803c00307000e0780c2d981d0101000c44101e180d1134000110041c1003060b80c116001d1402d440c0000031171044540c487c0f0749001c0c503c0200300c10b605602d40182c3e05080070b00800d002600b940200030302011390340b1400b81d0051b581e207004a401c440c207c10518600407100d05596100000b4803040c0c4405a000315201d00c2006040b22011400103204044c0d10300d066041d880b941c01480c2c2c100442c090314043c030025900103217044401490140c3d0b46001c015290100f02d0049080d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 910774010 1250 910772760 910772767
    0x31c0224010801060506120403080a150803030f010611031b0c060408070312021501140d0501022706070c030f08090d03050403120206060a14010c1a010f0902131205010e12 75
    0x11401c01d04c01c00028040c180d43c01858007500000d0402180c1e0700900040400200b00c00140345400c103500030450340e031042c200304c0329900c1d00c55607556100e400c21604069100380400001482e58824030703415254001e41400707580740c81000d4400009814084c0d1000485105100c0704074141c5e140c0f400180004c0a04034003502c09141186403083c1d00034100b0202100719405240c215040b82d20340f1900e03034115410b8071801c0340400310a00118440364000c880c09882e07544049515003940b4142c00c0c14403280c2e104100c50700d034158242f1040003410b010302c41014061106404041c000160305001d2000194058290a420403100c00006401240031403011000aa4082000c004125209425082000050024055903c1d04a01003075030003880780b0942c0041c418201c1103480c143d0107081400348450b08154078449a0400b000c40070184074081c1704000c55001c84500000b040400c40c0300b5120a542d202d82100e503c3e034901081c1e2000d500c0f5041c01542c00b5561510b01d60013640301000040c0100309881441c030384 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 910775260 1250 910774010 910774019
    0x2190b240a141009030803270a03051815040603110d060914060405040f020f012115060203070803010510031b020a02040509010e0a020913020a0608010801060f05031c022401 76
    0xf20204169450360070f008140b8000c4c8006404101681e520000c005082c1d405e0304000161b200303045140c001d07002050f002d007044000a15910400405070720042014181003178801909108004404100707110140c0d80c103000501c0060701c641c1245d1030b82d05c803c4d44c07843d0400c1510051b8000f1200c459104690550b40c920003240342c0c3c5a030844899100310103c0f000c00c4185859160b0000d03018111030024800c15650034424200e0303004104d245800d64124800c6075131805813400d168001c0c4060f8110b000c980c0e2b120b6000003500c51000049602c010b5108940c20b08603480c11040c020b008002c02e100300185500d44c5400c555480c4c02030f90360780001200350f00034020f100e42801072104440015000545a90400007685418280080c0210784c0c194190b810b11900d595100b40d040c614212640000d600c005180b1000940383d42c003401841c10385c0d0780440200802c50f601d08440c1751454040c4070721034140c3c1240400c14039030404044501c40f900700c60b005451406481d4041c0c544450203c03280758100034401d000501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 910776510 1250 910775260 910775269
    0x70306050609010e0409060f14010e16090e1506030a15080309030a0213020c01021914071e020a0b0c030715092a050301090f0302190b240a14 62
    0xa000c19684549000000c100003491100c03800754843c00349444403d80e204100203130380515802d10440204000c101200804a20a03040c20705c00c0c07100124005c408152003100c03601c030076030290126807251a4510314104000c00f07250300003001c0d0140405c031841902d090b41c6500d801144541d0410300001505062030041d01420403480c1c0107064503034824098520261000a4510030f42034044614400401421440388040d00c190b021540076540049854041011314800c891000e08041c1c452040c8603c6401c0c0c020007501500f0805091854a80191041901c1010031b1111035070000d08021107813038898a8000d042e1f40f1101121184d5480045c1540501503071482040c0c00c0c00701c00d4000d201c4c20031075071500060a0340710303150000501c00c660700b0001a564191140713070090070041e00030b004019086c24030308210b004d500000c4d40580950000c4c00800d00e141c02980c1001d681c801d00c1c580d8981c035600c0d00985008030725140000c00381203004100b08169611400500101150030486913030507840b10901 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 910777760 1250 910776510 910776521
    0x30c02030d0c03020d030e0a0203070e01030312050f0705030711252718151e05060102060f070207050405042a0812071e03120516020a080d060513050703 67
    0x1101004401d035103290010340c0c08103c8170182c81d00c910b40420000260200c0350300b0280768680082d85403140d6800000c0d0310f40e07110a0315048030701903110f03080880c01042100d010340341c00715858610002c4140001724982c1c000c101071074000d2850314088007011150b4115620b041529901480c5005040c0030071810941e140c10b511001d004034035902100f1124284c0140b092401c4c00132201d0f01a900c401c4000d503168544918001c8050300200c1030800141810000700003404140c090a0328021241d10300c07804040140120b901881045c0e00a04d00f13503840005074440b03a04007070405021402074002c0040c0c203a0369405110b0245010303580d400c4691100c0c6080200064000b04101210700c081d002c01c00000c00081652035090050b0800c441d0344950038506001c001c5a407420b43c00c000e07440d40003603000781a0320400c1240704a0b0302c40d800f0050f54923445003243c041000c4903140401031340b00700040000581100b024000010301e00720081451a00c42c00000e2041498100c0c1c040c000da5554108501c96a060040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 910779010 1250 910777760 910777783
    0x12030705220518220c09110702060a051306090302010503040221030705010204180c1e03020403080313050c0402091012020f0a17010f0b0f130e01060e04061a03010513060503030304030c0203 83
    0x206000c03c116030743c3c44844c5e85983c400d143d01c40e030751080d0689000019404039011154000c00c680d5449140701005040e40d04990071140802d0301840380418400e000729807000540341c0517152907086503a66800c01600029010750001c07140106076000401d61b80030006007151a11800000d43c80d42d04150b01030350b1480d010242410081e003400d0400c003105400c00c5a209003c201c1c241018280d450814058000c0e102d551b200901d4100b0000400c40304454442072800441e1040c82036802c690600401c000a900403088003e0340040016551403070f42e4025a042c14070035030310704005410900500311140c2d10b5042800d030300e000710b000c1a0341c500d00c111940c5445405090021004010302d8204007180140c1d01418500d45182000080c00405014140720aa0700600d400c1841644960b1504e50040040600c8003445004500f4501c01013603a1801c0c40140c0b5216100300602c43c110fa00e4003080000707612010b0240100160b0380c0201055684091008512540c06034551404034002c0c2c2c41130501d400090382b507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 910780260 1250 910779010 910779061
    0x305160b04030b07020a05100c1b1106180303130314061302060a11010c050c1623010531050d0b0619080709090512030705220518 57
    0x90900c41100d0980589066a810034582140c60761080c0040e483c010703803100003420031301c0b8030a50b40f503050419400080e421400380d0368070400190302c42d101c41074081101400500c1130205002c290361f00e05280b0080c0c111380c2d0b82c02d0955040040d0320008681983d0000c000e03042c012088403414001e110301d1000f026201001c10009001c68680b1010404c2c4064401070001c0c411040001c0e142e004920031840ea54490454100800c0078003000c540180c03044d030020790407806070b004102910a180010120706001c64403d0108040d4202410702d1007aa03035a0200411410b120060080c0c5a15a001c160f055004046584032560003440040e4441d1022540b41d00180c840c0d11005020000100803600c0103401178810740d400c4202c075412a8000328024100d0300801c2301c620070701e100081e940005070400d800170f0780140150b4101d40a02d0403940340b203200c116a200040b80081004880c1c4c140f000c0e22807130010014040803000140c032100010042d0407001450b01041520b80140300d821000040307203030303c01102ca42 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 910781510 1250 910780260 910780303
    0x91b051201030206090f03061306184b020307050603090309040b24030609060d1e0c0f080307050d0e0a0e06030c03010e03031014090a0203060f03010606090305 70
    0x111440e00d800050000034020140400e03c5085a1070710040640011002000d549081c58410700d070714104041c850090390803d0801d500080c079442080c0d05640810340082040403440e0b003042103a50032003a8201035241f004660110320060305441400d02c02a882c0c2d10b0b5144164555500402d8507007000d07a001644a0041082488001100041104e1640c0020740380803d8181c110340020f0411000c0062824401c1c084a00f61100c0701141801544120400c4501c55a181c503000709011511a08100c010a5140100b0b00c0c1200a001e9064003414244070b0400320072102e803165545061110181d20070038050740702050300390411209100c1c034482d0311305618040444460040001da1040b0192060302041d101003c0401c800f500c003440170030030740440035000f800020b000402107030380c070b9100719154a0081e4a00b5000b003a8644404490610424020080a1301e40c85610a0400a40c0701030051039000d403050300c0b24006034900b8003c040040002d0344600071034600d542021070030030010100644c144248407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 910782760 1250 910781510 910781527
    0x6130807060f080c0909070c0b07050406030e0303310f0b010510140301090b0102160b09030d0c030c1e0218011503181e0b010308090a0605031003030810090501091b05 73
    0x2001517549078041111804034036103940005503050141c0c48800340040110108104405030030100900c11154259810130645c2071603003145490740000c3da04400301d049490044c0030490040091041d859030500350030046032100c0c1d615144030480c11902158982110001001503103081102640e04c110303a8100511040c109803c001c0092105000e07a8000c1940c075100040f007079202b0040b007416080e00054132600e85841e030307a1245042c1c00c600441403080c170400c0e151031512441800c403015080e0340f50302c40c10340c840c202c1d0f52005460011140c9803140c103040125687c01607510400000c402d4050120f9859003035040060617900f4640020300c082c14181401a0010108200090110042d8009007444d03001013694a0591142a030400080c2000440170008400c1c4003e0600501078041e00301d4244004994503c01960940401c070307203859100c4141841000824000c031107940c0d112802400302442d040d251690482100d5080c0c000c020001e03551030310b940c5014594548040c003040d440c02d202d030901004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 910784010 1250 910782760 910782781
    0x10b0f12060c0f040b030a09050705061c0203060d051903120e0601051e090a0b01030c0c03120b03010e0f010213080304050904080a030209042f0315010e06130807060f08 74
    0x2402c1c000703401e030002443d180c20700c5040c0c0540b00500b42803003072941e581c00c0c10803508001d000321803010784450182c100002102d107004003c86544242a0b54104c451100c9903420300700075003004215681000002c03c1a00000301e090084c0841d804982d0071812400300c4500300204540034100c0d203d0f401034502078140d100d56000085c8141141c0040f5103201001d01c00e110100d4080d1480703241c3d41d41056468041c0702c59400c041c0c02540014030280e8081040c6031031424115250350f05681c002d0086144ca640400039a02242c204e140400006000400c00c1543c807210146000084400c10205035800300e400300c48101003141c00c82c010b00842c0b0045040600302400a101800c019000404070309000a070032100340d029170161403202100400410001c8018492418010400d01c541c0c09540d90b02c0d6215600103641c00e055a00074400000c1c0c030813043c1c24a030019901c01c00c01600f180d50003101404140c4403100d241018001800a44010b8001286040c0000e8042128808110280100c0c0344c200248c5030724 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 910785260 1250 910784010 910784023
    0xd0f2a05091306090e0607031a13020a0c081308010b060301080312092401080d0906021902011209060605150a1b020d0c0e090c0411120c040801020c010b0f12 69
    0x1c00c07100d01c5110382421801a004007030980c4030244490a200c0140300000e80840c020740705600d2078405201d1108181911002c0c0040c400345942c0c000600d40051001c0b20b490340c05000e1410641c2880208244140c41e0043d082c1c204051200826101d10800e0140300e6003801103840002064480314219410a440d040e10303400f45600012901c0c0390880026081f805c204449642c041d060041e1b070414400c6900102e05449090243c1b921610507003411074902c61154840100700c441680c040c2040307841d10700c0b80130b044003866141603041000c10514404001858814026128483d070400a0620300e07004c20b001f00d48260149403107804000380080600c030f5070040400802d480344020040d104074814800501420013810002d0407080c00e8480101e889844000c0c003501038105ca0702100c100a141c3c20411054030000388601c1d4814000b8817100e0711040607100083e80010626404904040e12014181d007240c000c014101450ba4440a8110321414200c440c803603803540c283c4225065004001a040c0c2c1c2d0803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 910786510 1250 910785260 910785277
    0x30807030302160c030b04021c0506010306020c1e030403030806010215060d08120f060a0510140a05040b0c1c09082a030307030e030c010f020706140d0f2a05 69
    0x54001901002c0c044142c08100e0500b03610013003852a60340c8034108089081c404840407030052081d007851390814440d00f01003034007040c0d100b001040281c0c00c660710f00010303400c03480c1c9c51003652241e0000048a2003611202001c05001207009507107480c0340d41801040380780301030001810744d0000b0103a0750550400c103410680c85603050302da00d031481d14940b070020800d118840d50900100c61200c10701412041c500c1d00d05000f003c0880d000c3d00c080b501c0f00c04004175a4104081d41b00400d1404001a010311810005031000301c0c000e06205091990b20f4a0041c00c4d544056200e01568004000300b017580440030103030020854581c6071020510b810010307003599030002014990342c20040d9a40c4240402c20f5080cbe134202e0b00300c0140c01c2d07a84071500c40ca0042c003484066620340d44030b4041d400d01d140c01135110b24040c00750700449500503e41d051910138140e0b04410311240301400c0d1042006005104201c602800008052007400000c0d0071414000c43c40054424045000078210054990a5055401300c190340e81d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 910787760 1250 910786510 910786517
    0x209010c06090c09020f1902071503051003020d05030c160b1210180b01020616090509070e03070b0a0815060a12150305030a14090307030f05030c1606030b040603080703 74
    0x42490b0078244a01000c3d540811091400082d0030002c80a04074003610805286950240081c109200241d80b55074003030103001c01076100d5602c0e511a030b91090300b000350440c807440388290340036803280c0104008070210f00081d101c40e032000031162240b041c200b03c5540d03484441a003415115003000807000c5103111341c1328010300c00d4900c540890041038005070420300401a1f000f4042c10a4aa1140103000e4214020400d0240c0104030008140c01204808800303540010b5030343c003800e00c1c144001c1003c00d4402a140008012400c1c040d2401502d00b0040300b4090700c2c242c610552100d8120340c0c0145081781c010804582c490601411018984920341a51080740c11420300d004141c03082900c000c024800300750940d051407004c450000034001c0c08401000c03e0410f03a80c2e1310050460142101d4000d11540d101150036500c02c004c104003003401c4d8041d00240e0f61181098900c3e000700e181d00d4501d0070034180f100315103081c54180200b0107580c151183c10041c400554081c8a00c0d0b1440e00d5047c0c55010701c03130028003030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 910789010 1250 910787760 910787771
    0x61e0305010b0a030f0b100f0219020d0212070b03070c12020307050709180f0b01091d060606071401140f07022a01090302090c040509061e0d0302101e0f0209010c06 72
    0x304030741e0405081c041d000b030314900581090f0b42d0000c000040c1ca49000c400350081c100d058000c170140d612b0741036803142c02414007031481c1e019609000007262a5162020640140340010950203513030740045001e42050b548002e0b400d41c480c2001d010080280c0d04200640d03100304490000988041981802c5a0302d40b000050b00032000902070761490a8510010207114260b12050100f0807603c0c1094140c4003a41b008008041a03c0108200212030f0b01c80440a40c0c00700c4002040e61038910020140b482c1310384078100c4002c0300c3c00c0c48070703003035958110a05101d450a8000c104014400168041d03000b032661008001d001403103030703518030600200003104691000740034008110764001c404100041d0340c0584800c0880c500155540c03841e03080b50080a104003003000108959140180001004a01c1c40400e9210404001d0400c2401d40241c00114258020501408104a000d1046c10b1114140600c01c03074000e0300c000075040403a03926489a0030000c0c418081d040c41d590384a20010801607000800080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 910790260 1250 910789010 910789031
    0x30121052401090f0b1c050a15051b19111e2104050109210606120b0a02181002120a030c110c030d05090d060204061e0305010b0a03 58
    0x1c245000000700700040600484000c0e400120004504841c4410010402241403c040b01c0680e0a1003003215800841c040f00106103102842c03060744682d1040d012691004a40e0361041ca24000c1560003024503961002040040c03840044050451001500c0c3d1520b01080d8107004102c1740845d01c8400b003000389180d81c0030340545040040e58403400090b00d2003403446e01c0e5031581c2035a5000d00d40c00c1c1e0301c0c012500c3c006069008a42c0041e00d0969805840f014a01400c0441c0c1d40070b0108400140c031000c00c45032842601203911403081e040a46000c00003842c401099081841e25241e010380706202c00707071040000200c106200e042044841e282198182c1e507003003900c04101c0c5009287d54511548a0002031041c4c841e9405500022100b0107a4452030994110f01e400192035003102200e00784c05401c083c42604100c1d100d000149408080100200c80d0502c2544901040780c0083c3c004e1008600185120441c5120500c2001004141031505000319030500820142500030750303918000789610713581d1201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 910791366 1106 910790260 910790263
    0x31506031205190f030f091203060e0f2707081b030102030f0c0d021b100e1b040504141609060906060903080a0201060506120105030d0503012105 64
    0xe0f01c0c6000c0181615503401d0b152001d002c066130b9403110380b00c0e00355500c01c81c181e40d8020f0083c91100101d011001e01140c056401c0320218908010802507500c40c460b41c0c40f41e01010b1400041044501070325000300301c0e14542045000c0380640385010845003c001124460000d40c031131034501042c24042810300300d22003540e202090b44414400503813004240c40c000c245412080360014038061443c40e0984101e014074000341c1c11500701c0d10070743c5500f41e02400b442080060384000f0344800c420210740345003149000010140070b103880d400014240718080700012043d15440782502c200304081f80c528004403409000b500740c000c0c0781075408944000d03584508016034032580c880441140c11510303050400d8100c4540304085640340c503808522600d800001e002448510101040554104000c16050000915400d4200002030004121444242d01c451410a004071501c05c1850010304165 = true := by decide +kernel

theorem cover : BRFrame.Cov 910611510 910791366 := by
  have h0 := BRFrame.cov_init 910611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 910611510 ≤ n) (h2 : n < 910791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
