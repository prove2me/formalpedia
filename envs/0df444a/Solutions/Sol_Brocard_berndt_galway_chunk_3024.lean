-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:26:49.444582+00:00
-- url     : https://prove2.me/submissions/5fc2bb6d-2812-4b33-aabe-8f95fec1cfdb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 543705035 ≤ n < 543884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 543706285 1250 543705035 543705049
    0x240904060f1508030706180210020a0309050d110423162a0f03050904021c050a0c0518010507120f021002090a0b1c05010f060905010207031e0213050711010b09010e0402 74
    0x5040411200740303404580140d071038803480c0041e41096401400b0750580cbc0d040c010841d0078103610a84c041d19101c0030707a00100b1140408640b505000780c0e0041142d04164a401110415401038422509040024400941141c2c0e4501a0003002c0f03545046030900d441c41e0480d0440c0c82c1203003884050720880700c5a0b0004401ca1000300006009040aa041204100c08942070342d004024052812075480042075200780d01c0d115290f00685050703000c100504501c48060f00600c1002e14404404502030701203c2c19038803940842e41c0003607001c1e0301d9134900c2c1d12041d000740100480c0d811040250188100409141503d071090740c02e001c070014170002c0503d181405c500861b500c41089044c910921442e0741c41000443e00413140240f0f5080d840d5103a49141010080184556800c0141190000308040000c0f031001041065100b241400c1801c01c400d0b00c3c4000b41460b94050441c007501801e0204104046401c42d41d8842400f0621000b488070300306000c10820540c80074001d60300703188141004034000d0f080c284 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 543707535 1250 543706285 543706301
    0xe01080619230a1517060c0c010b03100b01081f05010c0516030b04050607030504030918090204060801020a0e030708100e10050906061201050f240904060f1508030706 73
    0x541c0502e41d0040c40710b010160080032035040350520388649041100c4a90440d4070340007840c04001c54120340b00309081803900c6e280b024000c411501c01c0411510b450135000c0d84000d503440030050031034815558441d201805030120025642c0801d0203200081c4c038500c480c8102c0b0a0544294145810407820580151174020500d030b4269618820404403400d0880c0f15640040a14018000c1c031501e80b8140c1340c00b51410034014a40410503007844c00317020002e904049510700303544040002c0110340d40c000e00b0307034070003000402800f80d40141840c00000d000c01041d0b00501d03513051076580780c034162045681403540c0c0300c3c118800d00b402c0f540459240035010300715900400355603640c1c000392002080d1500074502a24415101d048058102000b840350724500702d825940e03600c076600006d00480c900504440c40780c1500030100090b0100e13882407030440403000d002d000d100d00d100501c0c0041c02d0400b418000028007000d5a900f590030318014800c011440381c41d403000e048075403000065242170465581c5102800480e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 543708785 1250 543707535 543707561
    0x302060a0207090203100e011e0e0403050f120a06142b050a03170a18030e240705100612030e2b12110c150c0a0c0e01080619 55
    0x10b10303010441d81c4181c001540182c14000800745d100e401c106142d003458a0603070160400c44403260340c0945018189100e0000c895100241e45041d42d100e08003901e03035101b415a500c0c1000320010b004003e11140c500c1e05405804029010400b140d282d0070304001c274550000c013590344404801103083c01c03078915496101440c00c46c254010440c0c0b4030341d80d4145c548904018105c000c140303511141d050b51101182c0c00e5030321038600c040034058500708030091a00070340100705c05401c001c1e031071020b00d030140c03241050402c40d0310100b4040c000e038038004103005006403c4201c04075218000c0741803580750a11a40505800c2c0c0384040c21a80d0203044c995400e03944005003640081c0c00c0080f822212444e480414081c42403085c02400c805ca940c469464116130f1400c1c010008400e02080600000103444000b80642c0c507110140d503000c071211009031982c000e601a60120107070b207101c0e8001da94101b001d0540d6040480d41c000e9106001a41c80700c102907203c61003140c4100700c40c6000c1815101e10f00050304000743d15140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 543710035 1250 543708785 543708793
    0x909030d020d020706090506150108010f03020d030c0c0914060306160f0e04023f010504020a030f110c06070207080a33051006110309090603120d060e18070302060a02 73
    0x50342d1703845003540c200140903103540c0c024508103e40c0e440c03091a14080303504240b80c04c5da0f10b581040b41c580c0c181c210501019000c0d01100392000105400380452101c40c0b5044007821001070740e10881c14002e1300051950b082d0701e00300c3d48041075042c140001c2d4280140320306103a007010004080c0301101e0213601402000304102d03600c07805c0061038841380f000f81032100000c4480c007085600400e001840d1120001016001c0302d400d0f95440501c00300a000c0d6040d10720465016035a8850102c0032030150010409003031009190607010716032440039200501e040e8100070241d5034a07682d5940c050340c65210500c2074901c1600419408400100c00d04501844104034560401100c0b0310a40c200317030800418520a0302c1103030307564284903213041c400c00700c100181000d281501814500c03800b190340301d001d072641079801020040003050050f64140704500450740c24002481c1c54403006000704010388000e10440907400340348004581070107008070b81c2d0b4140c0b100340401000c01c42d1440d0300340702050340407994000441c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 543711285 1250 543710035 543710047
    0x90108060102160914130f1b090221060109150c140d030b031603050327180a0b01140306100908030705070f05030c0a0b0f04030204050f150909030d020d02 68
    0x242d10103481000e020410710024401c00040c0070260780e8100030b006c1003882c030103038500784001492041d4620140c990203032a08410412003000c100c200b41540c1c05c43c042c4940045081c500c0c10031110385e00508402d2500c19048242c9030740005603070f00782d001c0c062032700c0b041b141c180b402c0c0c0301034002c8400003c2070b031142c51750701c481060882c1204d00b0f2101c1141202c00298483d00c61f642d0900e0200245550a06103240980a8628655440381d4a10649010b9104005418241ca6104803010100540414090a0350074508400d400040c00c20307008545090303901d4504101c000343c651159000e10410402c2c0d000d0b00b86181c031054100800040040f06410400001706d10210b021a414400703080c082c0d200340024040c4c181072040203108500150032160181c5e100e07440e5030328955509400701044501420443c2e82d00c210744520161288225000030b50072500306814000202c200c41101d5108103040254402405070b070100b007003074680094510501b10390003885000c0c0442d80d01c3d40105400c14400800600e824 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 543712535 1250 543711285 543711313
    0x18030906040e060a060f0207060809120708040f080a0209182b120b091915030f0209060d08220518180a0c090203040618121b0206090108060102 63
    0x40e10581240da00d103040715050211505140c200980034012600f007a81c4000403024000355523400902c42c010030004981c003c100f081605210801b1a681540107072661124039082c482000d5005225101c80d50302010382c00140d514010604050784ca50041040030f254540b4200301206850900340405c4c10300035511b403e6440c10f28910b0600350580b07078101d6030694050f09000039000b0700e8000c140b0300c43c0f182860b2542600d0354030150080c0e4080c0c040c8800344030101078240c03c03400500303090302400200316180c0302c08028020b4140044034180d20845030b011603503482c101031081e50b003540034008240b0f0b0000d208002c041e4090500a40b54512009034040ac1c040e5240b000035144e00422294010002c81d403400e003c85110064862242000b4000041c4500203076596070005035896445003640540d8040081800c100c840e8103c45202c601c1d90120313650120050030070113000c0b91042541c10104044c041c00707449a068048808000c99001842d0074208515117006440c542d00c014081c0c1e0449c010407031101600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 543713785 1250 543712535 543712537
    0x9090c1b061811040c020601031205130e01090b1e0d02130902040216030e01090e07080411090709051e061611030604050304030c05064621050f18030906 67
    0x16801411903e0f090014201400700315001c144040c4110342100d401800440c3c2d180d00c1c13240c038a010342c1c9001d0355244048071028140010b2600440c6200c0026800000d6490181d00304101c1039900f00c0c0d14040c075603d420f0345006402005101c0c0c640003840f042010025207016480001c00a001c03e0010071544010745c002012a44900c61210b89040f1250808081c19405060032500100a0030402009400c0c100714980c501c40007003000c0c0c10882c2d0240000c0c104402c030700d2150812400039000350081c0c10400c0307018050300c50a018940c06800c40030b0560150040e83c150009403d60701070480751501216129041d40d28030702c01c4054501e12007040717940d90f00361000c01c6128070440c0245c000e103480b00d083d4a0085070303468543e0b00c031522410341401b0344405806104140715508007008561001010701c0410001103591014103250f252880041c03020b4103507040022010450f0f080c90324442059031201114013294401c1d904080c18400240010343c044682c01e1204c1d1052001d0302c12a800e100d034010001c0e6003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 543715035 1250 543713785 543713831
    0xd022b080a2c1f060503030f130905130218010b0904090212030301270203011d0414061e0a05100b07050a08031512010b130b0a03021203030709090c1b06 67
    0x558440040428203641c01001010583c0041100b0b00000d072500f40042d550b401020903940d940c40000408804001c01005030400030034580406026030b1402c00108001901080720690140f0b504500b0b9854003040a043d0505850545015500700381105d0b040c08010102c42001b01e070031140d846507800903450104040c5008054070142149580807442001c02c40d07548000c1401d84841c010300061000e09650f500c0d00121041c003040012203566141409031220891038500511030041a00340320150401500a0f82c0d5030181403140b140d503480e0316220a046410849200c1424043c151050158070002f50013001918010822a4942011a2220401948156010071a080001c090000303181450ba0000c0042448070f402040445070082c007080d56202042d861006507540c1d02d940c850706a480b5000703070024540103803014014003e0354103800d54944c421fa54101c041110504009006e50303490041d022000b6241d95480149840742030652158100f02404890a80d102c400c41e44d00d840c501e505003a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 543716285 1250 543715035 543715121
    0x90c1324020d050705030703050c1c120e0f0c0103150b03100e092a0414040605040c0f0b040b0d0e1005060a0501090b090d0f050d022b080a 61
    0x4001189000d010b07150411114000c1c003445824440800810b10100580700c000d50141015074ad200c01c40306899050142e26803056042000254070102225440000a0303611000180c042010128200c00d10781d84161400c60380445a203c4020312800354800c0d0031818a58030300b40840204140c07141c19215940e0400c031820080d170f190b088010000c00e810b809103079030080c4148018115481004c0135a22020016803400720218013100201c000e0f0351a598481000401142c000c181d4034109894070b10007402096400344e510012481012400c074042c40820b5048500e000c00d400d203401c0c640300034184245c021000030030189507254440172034443c0038041c1c40300703038100508001101d140c20810080c10022a801150410001c000240a81c00c4140200c440010040340c1c44140c00c10245041d0809440704034006195000b030a55a45001e5000031301407a43c0342003003124002ea1007504038440d00c8079030303c2c0c502c000000301a032000c640300c11410782c0400410194800002900c1d80c0c4e000c2203042100456100381 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 543717535 1250 543716285 543716339
    0x503030c10020a0c0b040308070f0e061b071a07060605090c0a1b020604090f0f0e0a02010302340501050c090f0108040201170c09040506060c0705060a030603061a010806040b090c13 79
    0x200c0d4a42c000141482b1940364208a450102c1000c0400c1079130044080b10014040741002c00305d9814020480300700240550003030b110365041e10003803804081c0c11092048803da0305001c4e0200d440d141043c00c5910500101945c01d041c620355900c110790303c0440c604400d000c588008e07542005600c400c1c3c0204041c0c00d800c04040381c9071805250000880e10141542022185080000c41d50404041845020603809290150b114000505400d500d10203001c1d505609200c2031090780c44045041c02441691801603008200d5681e031203a02c000144962740d041d13680881e009080065a6001c1c0d03100c0c81c0c001d03006141ca20000101c10744c04a01d006000c0d581402480000702e01007580c1c0c9810301455030700040a9480508103000000307110b80d540344030702031a0b11070007010411440c2180b00341c1c003540c01580c001070203001400349240c040c401c01228030320050006130046c00080700d80c1428086c01504141c05800e4441680d00c500d981c0fa03030b580180314020210b90382d61030001102d1010754101101060004011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 543718785 1250 543717535 543717541
    0x60f090901061e110c01120213080d110102070c03060507050c1629041a071505042904080c0c0409050d0f02070605030f060d0203150a060503030c10020a0c0b040308 72
    0x72100301888003c15808101290030301210001010440c25803001013801c001e00780502c6000100c01074010080d02e403500e9804824005230081d000640304070381131141d4540921181803a003906090384070721303000600062103907502000001e034964081903000041c0d02d42a41880d02600549040180300c03c40300254409001003807100ca11241c5004000c0d8001d03501040d03c4454010300c41c03d90b40654401c0400b401d4a21440c00c101e42c0003e000ca5690960161103500c088800d6076266005140c00c5e102074520102e4900304584110791b624020380e41e10809803502c0419038840d59a0f181d82e900032500c0d60b6240c010041c0c02c641544444c05010640c0788a44040c02004421031720050209004070700310300865114003000c20041d81c12008a035000b00c0e448071540da86a880f030010030072841000d01c00940600c141c465418a04182ca4041c0c0c1c01803a07600001d10005035504109a81c034042d49030f035400b00d600009280c0c0349100c90f07940200040b10950610111803c101d440c0e03010801811a01940403403008410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 543720035 1250 543718785 543718817
    0xf0703031401050402121302190303110c040c120b01030f06170d050307050d110912030909090d0909051e0103031101051609050d051c050c0c0312030402060f09090106 73
    0x6282c05442c065a0442c204141840c8580440b07802920b00d1002898030101d00d0159192030030844000b0820f400c034011810341d40e181c01000c0200e075680d40c0083e80200b440720070b8646024000c41822100c00e50310388480703d003c002c5040051403401c01685c1415a5002d58007040121405035100030001d060450600300c0c0b18901090030403104846030344c200082003042040440d00f00c410740300042500100020380001c0c04409201c944500c8402540c00400c1031501c4a05100000052180810964400318283c480d8046266185190400e030b502261042005000f4030500c0d9015a030701244000220806070540e250649071040203810503000240108801e90000c0300074000d135504201d20400854958030b00c07050051202c4414025140311398030140340c14051140c20402c52142c000c000ba43c0003030111081002800550010710b010599000e40d000e502c10030b180c04902ca00c0709440360504546181d80d0380d420824181d000009131a4020307428001d54280740c403003d0080707000e80025100d0007080c22003415 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 543721285 1250 543720035 543720071
    0x102f060108030406051219051005010f020c0303030106030c090504150501090e04171b0106081c02030c1b0604030501022109010203070c0b150d0b1021030f050f070303 73
    0x1ca0003040c0d00800c8100401e550040890701500035226601c803094450042c005911201e0001030800036007032005020724450450041011078001741ca070f001c811b0310782c00c00c180c0c1c13603104422030241d26810500040005a000360402488582d061500400c011b48540008080315250010384407420f10843c018805540c02c0840f00018000348140c0075154600b0ba80c81d41040781c01007071070055140000c030300e0b036009965003200c800b40c40004200a010076031b100c0c00d01580d00c005145244280c4008000300700c59003400842190101d160741000740251a803c011000d80d0b4074903403110150802c1c0100000808a1028806402c3c84d0b00300307403018841e0740888100c590361014060210340c00d59204005000119070402094240307640d00c6108802e9641d520002407250403500c0c14a960011002c0142c0410040b180c0d076168410107041800c403e90903102d9041600071840c00c81c0310749180041000c000d01003409119400c4007481d40313150651038030307100b818070b05181e401081045002c2a102ca01c1550000d600f0701c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 543722535 1250 543721285 543721289
    0x70602041a0f041e12060b0f0d081e09090a0b0a17031c1b090302100207030b0c030a021312061410030611040801020a02100e0d0e102f0601 61
    0x2600c400c1c200705030070122102d00e108a12900c541c2d00035142c0a000c40c0809900d5010050a00d9001010428250709050000e00310800419214241c4941212481c0c5400d544848a40f03800500c090306002c00400114002e1450007440c00c4001d1007400140c480b9a510324803d88034003114000031030002000014003c0d10250754100e9500112000c003424070000e0004180e4040110b203804548031241240c02440040c403001540280b0325411103010451945c210b0056402c036031003030307580c1c8007241c0030002d003240c80b42a603010080c94a400c90011a103500c400b800555000080c080b8014902001c45059181c8100b1981c0500040c156a0803d842840694481d0360300910114078181e8081c07812a07841c00b41e0014900009106a40c1d40c0381c15001c021412080d68003900381c4d20000c40d13440d0001e44e0043d5403544560f08080f503503400c01c0c80c2c4034a24100410007034030705c0c0d880c1e45900c0c2c104191401009030580c100c5051004210000302e0054000281180704041100c0581a015049001802683c1850300503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 543723785 1250 543722535 543722579
    0x2109090506090412030515040c020f070e090a140c03060a05040506060414061003020909010e180703020618010e15040609080c0a3846030e0307060204 66
    0x540420010a01040108030007842d14540000d41d980e47c4c40800030519102c800d001c1e001864049502140d0340c0000d0001c18200148046421290344c5241002244030103c45911458200c550504001184c0c412100c5003180300f00c0c241e400340200500408e10300981150000215600d50007440140102841060703084001503d040c026003540d40c0c98801622005001980180203003ca928441442641600c03e1030400030a0011156554459440302000c05d84855013117040750094601203050000303030401140c0e070180850b400c00708043d006001034915a825241440401420018580c1e54901c141c0c0d11000d0b03c07042e10740c995003005c00003010780541e80c02c02d440940c0080000c1c101c581d5044500e60880d003203444107021044172a00a05400710801110820a20340d16040304007403600000504200a0145030343c1001a503403500d99038540118000c103c103004160a460b40e6910900c1d075424600d004141070100d42ea44621210510750b6001c0181034805039404202440f200408800c402110868 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 543725035 1250 543723785 543723799
    0x4061202030f04110310020708130f060c02060a05070f0311011107020f0904061b050c0d030204060815060c10050402090709030213020c070b0d090c0f0b162109090506 73
    0x20350302c800e0010107840a0705407110b11101c601d0942c1c040003900b400484010041d07403a51824600400305400401c2e0070703046181c40302c2c4082000500000d1700d80c11204203030b40b0301301040d0036a020f11241380d20030070b0010304011080050f000841e4102040c01801c0381310b0303500c1b006032401c03140c007560071504800d00c1c0145100b07003040040050b0351407140070351080300300303c61707010a6454030310300308004140c450048100c00d41e80004100025400c8009011a0085142a10b0321419040d904070304a01c2a80605402f00300c2200c003007828107005030b82c40021200060040c500e011104403c2c90b150113100744044200f2611401088210305000f030b45250014001e05105031000e0856000030050074151007841c001c56804a0b59803010801004400b0050410503031303050352800040b040340c000d440d02030f00c151034907030080310001150f501040006044401081000b400c0040d003555a00c0c100c02200c00c25901c24010a100440240b40111011b8402d0242d850f0f00140516012001c0700384e40c002440d292051032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 543726285 1250 543725035 543725041
    0x81608070c0804031104050f13020f0303090a08060f0906010b0a210f09140d020c0d0501180c170c100e0301060f060306050910030f02010c0f0b0c030109110c0d030507020709020f0406120203 83
    0x880c527070705154550440b441c036103021303002000c81d1643c041e1881080d13200d581198005980c0c000410443c1c007680e1007000310710055442c114203551b156002c2c8207a42641d0000c016407280d050ac144210520381c1d40c3c0e01e00d1481c5031012540503605a50240d400d0820381da650b50000030800c000da000600121440300042c0a06a000031030194803040e90501b094020749580400c0d030104039081d840300d0300c80302050426a0301031095042290001030749002d940b104c90044644440e400c9000a141c0310035803c0181207950008600703e0888000e4850f100542d0199203d40b40851610440001c07000500003a94001131002c0c80d00b02044403009002c0c04001020321b15013000d0000c1840c403c4480c4480d502820280310086091503c50300c0c8100030b200140141c542241408007000038000114125014001e041c4200610294a40042c0c807440c0b02960301030b402030301c050040314040e420880d400819401038841c00c40e40c50103144182da00412b1900360700040001c00b4814250850a51001c1c3c6546020460442c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 543727535 1250 543726285 543726301
    0x3131407320d0303230c0703030b011d0112090c090b100519030515031902121209040e031201060c0213110d0504020f120703060c081608070c0804031104050f 69
    0x1042c420240c00c258403103082c05031241c00d1010002c0d00b203120915641040c50a140d06560f280c1004c41d0840005c3d09000c038128141d807081d180321140c4501c8020681c680b089500041d1001e40450a04100309500c401c04240030421040c0350030010b09841c1c1002c651021040100003410007010b80000901c4030621a441c114501040c0c10308041400303090001d802d80740c072803400140079030400c00c07264940324a43d0b0000c1d4900700c0003658080e891081c1c0d2504601403070300e80e09035100c41c00102c03002640305051010080500d0581c015855458000081d60f00d00703a0120903104484009070843c40101d0b1001c125842141080c555002c1da207100400c081061001d0490002041e20401006140341070b04c075008503056603035071207440310000ca004103540304494a20980a40b121a540705c281c92152505450f051300c1170042d075100740f01d45100041045000003e01007618000c030060014004c000c4c50501c01400a01e9402c0108083c41c020303614500c2000a540c20001640d6005101000030700d810703405e10100d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 543728785 1250 543727535 543727549
    0x2402040e070305100906060e1503010b0f090a03052b0504060c12030b03100902031005070215130b13050f0703051209150403060207120309080313140732 67
    0x40303007482c0208198481c50140546403203035420680c0e42500d0511b000900c0d40d04208000e0b007844058513405210101158080002d000074030400740101020010302052034280e41c010103100100502440c1d002c0e4480d201c1e9450448201e15188108500c04103103501c90444c11040d018000043c5401440c00f030a000c0d006002000d00c080040400045030909012507000750490b040c802c1001e000c40390034004040304100038000300d140582c0640503444082c500c609132801801e01c1a0702540040418000b240d1210003806401401c040c2280059140c903000a44060701c0c0340d0241c02000c44c842c08099107401d00c1c505140e0094030703400f001d500000c000c00c0042c03030201d05020000301c440061605c5003a0b40012500e4069000d0345c11110310350000f00802005103542c007800041d40a248042089103005c07130240c08031120400040c04c2240240001a181c4500ca02c07080b0b48503201d02604420b400501c101c5520b400b04980000c00c40d40140d51031803140008481241c020608074020b08040000190089486 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 543730035 1250 543728785 543728791
    0x10311010c05100e01021e040e0103032a0503070605161403150409140c030303010e0a09020d0204020a0201050403110d080103141e070518060319140a2402040e 70
    0x6100c501c01d07654060060034414902d6544201d88244410a040b0080034000d40c00a0031181170f0380c8400340c00301d5940380c1390426103003507403240d4014140b56400e60b1400d966031003034070a4404100c0041d290689a8078013170bd40350329466200e000115104d0500c1d181401c2695001000e10420510300c0d04001502a031000e2401c07681c15540d00c60568a84407410306180601c1c3d886d20003a0000d00f0034030381c0c10800031010820380381a8011016902002280800c041c0c80c0e00c002e10070b4814107002d4070f0109441d46199842100d00314401008032503541c8650f4081010f98003c4128940540d544d10204018141c00400440410014401a128115500001520101040c0400b4001d0241201160305481041040030f0300c0c160502090710007501448105507a030f143c0d0f4020280140c00148184401400301c100d110f000e510000e0142900480a81a900040171188000e66103011030303182c0f0013200481800b2410345140a14a041c1c0d05000d030b010301110898207030000ca200144100420005141015042070b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 543731285 1250 543730035 543730037
    0x14010e2b050c040c18090b0a181e1e061a09040e0f030d0e0c10121d0c0a0830070c09050702060a0605030309040c034101031101 56
    0x401661035003005480c0c0000040015042842e103000060480d80202105a0f0408009003148142e51164038800542e440100915000701412805102c140407085207a4814507a20720002200002a612002440c0300c03081c400000b150380300421910f80148103c1007804058901082c0f003007074900222682900400044121140300110340e00d08156125000184182c100800721501d413070030900d005449a2080750760554403490441c185051410102e0380c940400001064585020300443c019a001c0181803c5500080e995644c59010219405201c43c1e08402c03100040509c10032140501a00d1f640a0700441f035260301c17002c0c00004280400c41e00d0424441d0030240204d000d07480b221258070300e003d02c2100070111400403102044a02180e800307284624134036400c4500391b0326400b61000c21121240505078141d0420055601241403a80000da009601c0e890001074402001c42e0100340328600c0000050b072840c096001c3d1805101440b541000e254500364100341d1035142d030340e40100300c00900c12128 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 543732535 1250 543731285 543731359
    0x1c021e190c080102072f030c06070602090d03180603090c140a030f0302340b0a11070f0602070611030405040f02160c08120403150f0209060414010e 65
    0x1420440001d820000514142d00295180c507124074103117211018140b9107502045402400c072482c1012918103040b03040e00903001e0701d210400101880050780c00f000c01910000d0f000c00c0616019224104a032a9041c0240c3da50040114444070180c50001e103980001d08260812009002041408800400300d034441d5081c0040c90b0303004004211140155840034140b4482c0111106c14103070041400400d00c409040029016000340f6100801862001000b9a064000da41c050000c085488020500a080c80c10a020036009a040c104c0c680451500805004030280204101d42601005a00044c10450401444609a0821117642c0c1e00130351080500c1641c0380c002102e0000c0ca194100c130201a9180c0d200f0340c000016051650b000c054520540c10039124092110141d001088251419254800c014001e007000a0640038090050a400070440d140c3c00c0040000c4c5c5c0d0f41701c90060008000c0e1000d0310130314200940000d0546080024218091080d40e101c100e900c450600840040c074410107030b00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 543733785 1250 543732535 543732583
    0x10f08070f151e05090a0b04120b06040e100914120d09060b151b1c0809030d060e01060e060a0819060b0f0d051e07110a051c021e 57
    0x225100c001d00c00041c2c0d0f110220394034020300e80e03038050001d0403280402d4403405181c41e80d4002c2007100340b1492050805c0c5030200c0e95903c3c00103c42d103400641008000b400451204455018076050240e030241520042c1da403030081e5020407200103100e4220501c454050a0f00c54071180b0a000107200300d01d05850398542d40d80344603081101a50010f05071b0303140a04a00d0031014800c0912040f035010f00d4410b94680d00700701d00d003821201d00081820b2251401003040030321240000381a907003000080c01c00c1300c142c0404e207c006a54a0075100e0f09008dc8a0b10300309550f25490721102400241810703c01600030703c8200304203c00716410141558001d01e40c880d050800c0c0403d80c40960040182e50040f080f418400101307411a0032800c4080c082c2c802c29080c1c2004541c803000c070b5040e1110588101d041034200b01c000040c4660303025032107036070000440d0401d5440030b03126030f076a86051a0310089005001c5c080808a030341c107180d041140c40a050881c448075540c18400c0d1a0547d0b840d40b1803884420808005040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 543735035 1250 543733785 543733787
    0x4060b090121050103061406030a021e040b060a05070c080d020312060d0215132108031312090f0503010509070e061206090c040509060705030411180f010f08070f15 72
    0x15590b84040d281608101c40e503101e06d0494003901e51340710f02c0780007030b200030010580d03c0c035003c40c0242c2001c0e07004000305036190b44c00e8001d840c510070080c07045611694601611201e501e80030f0007841000a00d45c5c6090303a85c046843c0803030003040c554212101ea03a002820b0030403000e40010444180320070320040050780355104000940007054440000390021a40c8040604880b00100a403c06450308032100c0002511040314003050b110108003c00341d851141ca001000c203002400030340d00071500c000c1508001a507070300c1d00c11a80401c1e081c0440010380c8403000b04001c492102c00e0b10054501180244400d080840300302d03035260041d0141100040c41180412081e42e034a0b80c1036803c01c0480300c1a02c0302d900d081d0b80c14544490040e028603000b0390408000564403800402e0951181060744c07100e6013903848a49a51b4102d03088400c8a5801200c1200c09246508456407607a11500080202a903158180114042380007000c2e0b021461341c0d8080b078001c2c0000c000d080c1c10581561110000a82c40e15030240c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 543736285 1250 543735035 543735077
    0x60c0303021b0307060e07050d03050d0504020102070b07050a0203060a020a05071b0f06080906070f020601150c0b0a0e1e071a040e0f0103060c090311011d1002030703030b04060b0901 80
    0x1490700700c1480002101801c000482c1c100c0390700c2018206c29222569640c1c0c0c00d11103030f03142401004001aa040261400021603684a11380040c010720446407540d85130240c0d002258014001074075141d001e804180704601c0d00b04040c40d40900200b10950500240003030142040c0140302d0001c298082d44c40800200e45034440e111001031100b08075844c591560340704090a0004142d6201406018190009840764010f544001d5170480c00d60003801541e19011000f401c01000f80081c104001300d400198020422000c285405100500e400050034050444103504d0701c4401240e0b50300180808000840044000c0352040440f5078000c15400e02025160030342016118580109801d42507210502001422001109042c2c80c4075034000c0000d5410b09030195003c1007584001064a6040500020503501c11800309002031070b0943c51564010341100054035420441950ba40140d2004c5481010f04d43e16000c2ca080001c0c096508000d803e041c10f82008040c403540c030061341482901c0f008516008071080c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 543737535 1250 543736285 543736327
    0x90c150e061617030124020106150f02150f1602010b181e22023106051e010809030421120e0f190902120a05070504060c030302 56
    0x10000d41e6038040c0d01c000004000d402c0c01080e00c0b44140522801d80c08040b2100704da043e074480503050790098000450045c1440014804102155201c050004102e0103036000f440c2c0400e019220b040312401d55400003483c1902c4501c0000c440030307003d0301b401f02e0341901c6500c03260060b4101c04100403103101440d00b603025280720010a5003104a18000d0142c130200c10750854060851120924082009079000002c1c6200a883c4500c000c0f03121442400c860b00d00380c01c0c3d100440e01c0609605000c81c08070122256140c8007140807145034045c210442c010702c8040c817480d400342400b1203094100f07403905641e011103550041202d0f03040c0b02c0c0d00c5000c5a220700c02041580c3c001d040c076100c8640d26421034400805030317201e0481e00b252407552071804080c0c030074014050031700000c1019100039a60505842081012440b20002100c1402c48030700114082205000030b01c0507103440740e1901d195050240f8010100d80000307020504100d01480188000c591056120901c290107140150300d0720758000e29460780704c94031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 543738785 1250 543737535 543737539
    0x807063002130f03050f0f0a03020c2b1203050105030106081903030e0f070608131a04170a05031008010506100302070c05060d0b03011d0307140102091021090c150e 72
    0xc0000001c0250004980c284070b60346c40c044d125940ba00d0482d07140e407810901801070241c0c001a42d8160542031800d146201c030b19052002d400345034540d8080c60418082c91201395400030307081d01c5600000c2c0d090700813140102001e4000f080600d2404103440d03154584500003040052110800c801818070a8100c03030103c04070f2034251072190840200480d038403881445120b0200e00080001401c0c11000340c1e0512140350000c00e6100002501150a841c0140080c011249031001078494503820386074002a12082c481519050350b24100142003804162140c2c0c40b1341e00396810700d01048010340700c2c041000b010207824180541c03610303004d141c2150030000740e0700004c1d0444008944007003503503140d820560303400e2410b0b0020820100703010407015901d000001100e0003035004118000010791246098210702c0c1c00c5400040c10719401c0f00c001122071105206400000e00320320602001e10350081d04042504014680402500009589800381040944103a0030320441581030200b0080c040ca54052442c400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 543740035 1250 543738785 543738809
    0x60607060c020312010902040b0415140c0c24120c0f0a0c1e11060c0a0f05070e0a060602060105010521071d040513020405071404080706300213 63
    0x307020025603a4002c1d80445102e02200300000942100500c2100c007a210402c030302600e402d0901215a0814082501c070204000708045280820086100600342810062002d0400418590100541c0b9400d08103903680c2041712191035018124044121104040c110000c603103030b642d900781c41e0706582c00381c8a050000c416002602110896000c5204600c142c45220f221000103a80d548680c081c0d1071000006040c0040c0604206180c42c08002a00c0b1500816085a600903207039650010300b124540710803925517020810900499001c50034041c0d000c107226400b046074502c1d0100c020740c1d5a5040c8281414002c00081d401c03110b118004040c0140842824503510038240600010281041060030011401d0700d030f13003100ca143c0784c240101406480c01c010f1684034040d498003004010a40a0281c4040c000703c00f03010038005290703d01400003014800c000c0c05074545010000f1b0032011034a1442a4810b8480c04411407002101c01408003000c0018801a140c0c03010002940c0030010035004041e40b400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 543741285 1250 543740035 543740051
    0x10909030216032d0507051306180603031716050d1b1d18010b0f16051b0a0513090503090310020c19031715040911040b060a140306060706 61
    0x49446401c0e04c070741052035040894450036031032080c8800d50544002c240341c202d07040800203890b104140d13080103807032090f000403242da4440500c000304500000b111038060729180304005140d00000060710b00701074503071503044602e081d002051110f0101c034070060902001007030700d481540e01940020032404000f1000d520f69040044090590280f40411803803000f0301102c10b1450341081452000120343c3c80c410012035900304548125940c200e60300c1130044070303400c0c0500d0801c911500c200d07082050048010300360009495454001e41d4030750741584d90064103420030411950321001c040b1030f02160800e50001c0c8c51a040d19159040d032250101450341807180c840700c0001380d40c1590041c002e0403850821a0036844400001a1703042c0d980a2000d03022801884803c2070304c00030b5540c1c1550010908191000c0720400c440001c044409405054070f404c030b5154400440c50901d0f10600720642801c0703d0060600b841d807480100a0340000c1905440b68070003002088441d16102d040d565043ea00c04001e01c0070038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 543742535 1250 543741285 543741293
    0x11090a09021915030914060f042607020f12011a01090f0522140c030f070c0506180109050303090102070b01091a010503130b01181d0601090903021603 66
    0x80c6050003603118458180010740c05412002c4680121100445440c0310906020000d800401e03040304141d980c2041484241c08001d01400154421058141c5c2507000e41418206003e92185031750200300013003070038042c0c45840d81f11101a45c02e002d50496140c3c10300300c0e510011039880e12150381c140107650f00b0246202800c04182d4150201c010007030340c5404d54181d442000c2443c00c0b41502c14581c12102c840c032641c64004603060348920390007510902040310f001c2040c9914001d02d084a02842c103000100a021003100341110044c1c21011601d0b0041800c4a5030700c802c6d8444d1002f500401c911a401d20342d10215001c00e410152210b0303040010b4139224a40707403120034040e50151030102cdd560000400046210240c43c0300d545204401407001d00503041180005450036031014101d03805090303c8801f40000034010450140c06012110781c54190300d1030649403403084d40c80d24401800440740c0c1d800712000345400003580c1411913503e190049205000c0307090076030418152004002000040e010080300b84 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 543743785 1250 543742535 543742541
    0x209061b07060f020604120516080a020a06063c0f030f120216060f090e0403110d030b090a0c032003010503120313110a05100c110901030206031311090a 67
    0x42d829503c420f4260b000204040341c407038104803002007040c0c00b0340d00301d000e00b2442500901b008844102910110b0b0401e0f07250000d07960000700e084401640404058020030800d401007030b00920f4020302c00c20342400c3c94a100c180e02258402008270004d1409003a5101800b903a0108008040c0080484c5071140c81c4e0401c060b5200d030784901030303648051081d07100c2001f6100050880001120314229904507040402c120340950200c103000080012b00f003808959400054207084c01940b09450f151500c4241c20911400e00884040c4641803618080c14240c058903032114265004c60400d03000103480b00c3c00c80054000306826803a003186581c2114440044071114402541030380d07001c80880da0501000540e04140d8401250441d050708154140da80005070207040762408084020005840c4a4035440816000b24648a03642d0002d20301500000a00c00c1f802411842d000d41503400300c0a075811900030500030b00c80500b801c0e0180002050081c14031120400f60004104000c1c6034401c5410b01800110203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 543745035 1250 543743785 543743789
    0xb0303040b040f090b060901020706030b2709061503030a050d09050a1406010e150609042d06080307020f011b06060306090605060301090201081506070501020409052a09040209061b07 80
    0x103102c0c60942c150040d40b03441ba0a0b83c015a2050380200103035800c029044015116020003a900800c603040d4101c8505040744107040100300c0c07001006c1044c58480360b440d2510101500e010391103541040706007040d0318048101c861080b49428042d07501d070aa40c0c520002425140d40c040c2c918041c41d01007808122181c1902d00c403c80c180f5084800b6640c80350303100005090180d4200c0a401840d1040980e5410b00038050601d02800420014400030043d8030508100e03041111258a80c1c0842d015900307030815480391501405d130201c002d50034400300790b0204019010105819060004070f4100c40404058803035221140780d80982d05000150b070b2441e0607005084604003c999083c2044002407440c10148134410421340c059566401a071240225a0510550300c035499030400c2e41003007800c0202c0d500340000d0000342015240000e091030041214403010750051045590f4581150307411100d1025081926042142120010b07991540d0f500001c801c1e10a49800d40303003415400c00c241101c12070104017501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 543746285 1250 543745035 543745049
    0x3030f040201090b0c03030103021315080105060103180b0606030c0d090f1202061b0307020f0f0616020a1212061d01080d030204081e0c09101a1206040b0303040b040f 73
    0x140c840e120003070b104d11402000784d0004554000d00c0100090301c0e00c1808040c80344860080007804800c850840100d41c0ca141d08a103600740c0d141d406008040d680b612856580e101d04044100165030f159441740b00401d000340030326114090100c04650400b007103108450910644100800a03c542032828041451070040c00307488042e440d02c9a0b98170035002040961058880c201c4210000b41d58600c0c2840d5070b0805000401103109a403900348030307076404106044000e40b00c24014403c0d0300c0c0a105480c0400c101c40034078400c40d082110365200240c5c1003086460204014100711151203c3c1031280b20040a00b580a2008141c006105440e0300c842940618141d8000e001658102c03102104142c09901c55031040d140603a01c216500d0740740d03161b5290000d0116442c00b01340c032100b00d103040c0040d00c009001c2e10020b82c080e1580104101785a111000f004407603031004456420502e908920307014480004003400d0240742c50340d0801030310b9502801110084c0c50071a40054a4036102c8040c04900881405849 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 543747535 1250 543746285 543746297
    0xb280207030b0a0c0e0d1b17060604020a0f0305040f0c030308090601080d09030b0c04030b040b011d04020109030308150433050a05010f0302090d11010f0903020114071403030f040201 80
    0x34030f41804034014403540440c1c3d80c655104140003070051004804c40502c003a9414000c42010b020350034100b00d031003001000c80c00070a070300a01e140000642019000380c07181d44a584108900e0180d99000306c080c51a61180c3e00b00001c4c8c6139201d0a189248840c82d6a00504003903000310084201a04011024010742101c07080314150703a00d03000040d5440c0824046d107404100d0281c0100001240500c0c1c01e50300085039600306041035920343e126000d1520075a0100c42c1c84240200601c5800072002ca55142d10110030581000c0703082640000e030039150a800054100001c5030006500309805100507a10b654015104000c3c030b5442012007040b0309521300017062441142c0c8959001030010043c81c030280c607001410a030190789014010743e00158a4540c0f04140b42d003c3c0145440da0b80e8440c0d10510b40b5009904003400020007400041c0031030396010b104410322200d0003091003d44d91000810b0600c1c4050755800e60b940055007014202d8141401400d03445110000401c01d04602c2e0890303007070141d0b2003a01c03a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 543748785 1250 543747535 543747541
    0x5010b061b0d080c030a0c030e031815160b0a1e0b0103060608040507141302070c03031205040f11030c0d050106050f0a030b07141204030207030212010c05040b280207030b 75
    0x4982030001544c081d500402c05002080640c0742c01e0307004601e414013030f0400060254103c1c50150441d081040300052004906181e421107007001394203d845443c01d400d0710f51404428200075100011006009044681090000b41c0c10010765404011030000c1004450000f00c60810104050400030715841d0000741481c60000b80240200e803d42c5c0541c0d07203c80980103441c02e1001164800304036412071903100c034150107003214610701840103018640c0100049a589800c509000d018002c200d420044d003a0310700707010040407400400d080c00000d98446081880c1c941a07100281c034219001d0b84150344414140700d85400c01205500070f5040315400e86101c03041c041410204803030780a040c80054100e90141c00000c490501c00d143d06900c1444026030181008180d41e074070340f0305040881d400c07005680650400d0042d450492904103440045200038404044a0ba5006080707010f14070840d00014404100940112403081c440565000300030000d444000e010395000b90346400754882900c00042100c08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 543750035 1250 543748785 543748787
    0x120718270c0c032c10050a022a0d0606052206050f03250906030302100509010b030a022106040c060e030304210c15020a0c09020a0c0f05010b061b0d 65
    0x56020994154446032480345908401c4072060b0b00700304013450154030610f1841e00703680d515103212280c2c94580e941c507a105d40400101901c1e0000f807011b040042c03229a0701910403100012880303002020700351400c08000001e031908101402e400e4200c5d5900018000f404807080034044018260840f1000050141e070390344a00340201452020441d50705500000e044040009522540c0c09407002070118a04460f65511103500884440f84c00840c0181c03c01040c258000b04a4000c2c00d800140c41c0f002007004180313000000703a55100035000280100041d801c090003a018080c906c130007001e0104156242890300c0c0c42c005104e8171490084401007203d02c8800b040d00d0400100355002d503450038080960741401c2083c980f007014035034501114609001c81002c079215905001248041d6019001000c6d40080e624000400c92015003220040ca441070017001d4807240c1c0500058404e0f60845c407500d0400c0601d00f085409804009541e039000b441c00660040d4260f80041107003007001c0c006003030702c502240e0900c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 543751285 1250 543750035 543750047
    0xc021c0f0e031c182409033801180c02100606030902030d05030c0a082e15140405040e15280b0907080a0b0306010b03010503060c120718270c 62
    0x1203504a00c000369856207080310402170b02c0503007041410002091a601c1c0c0d203244203203896071041d0566003108c1a03803048407100003040c20740603c01c02541444540c1451101c60340703034607101034400c10349884a004e0003095000380f01c00303840c130100000d050200c1078590b0700150107403030790b240100e000c1d01c507010409201c240b1a80c1981d000707094002d05246080312078401119041406095803d60000d21909039409882080c3c101d445480c001c01981043e900e0624000700c10200220110240314402030b00b102c203481c211040702c0079164100e4000030400c940920880c9031104141c11341c03051880c4501031109102d8100111100c01300090120148090700c180a070050741c0018000607045070700c41c008901c90710f0141490315407110b40010f0004020310010002707464034000ba8070180f45203000000601080c2014401c15a000c505280b545150500301410124841c1c4014000f104104405000346c80b2810220291401088c1c0c203600b4694007110b404106c3c8061544003281035400b45415142195240214 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 543752535 1250 543751285 543751289
    0x1209070e040c1406090409060506090a0e0a0210020c0a0b09040501050105040819081c090b0f04051e03041d090708010c12050a0b030d0f02010c021c0f0e031c18 70
    0x1a590a1002c2c54100010401201c0c4105603521420900040081e511140325405c81d16002d0322001c9030600702582400f229070003303800c0300040d9083c03c043d105010400a01d07820f030550f0503162842112901ca00c100d0070705081803401c0340d000f00044000181222100050300e8071900c02c46040055990f224010340d181d128074400c803801e640226160070320241405204900c502d00500442d403400f4200d03581d000319610303003000c0f40c0e00042d0f0320714146052100c8050b070994440c0c042c000c000b8160400d03032030340365aa0440416580418a244800b400d90040074004d0383d0081895100910044601c002c1034011400211544d0201c0d11034481d0005082d60b0501a03094000100c0d00e40341a07540304441e0b41c00c042c0c0b00080c01406660f4540d001c0b010170303480801a00e5040452030352605166030340400002d0949444c64240005c5501440c103128081b5001250782c3c8004410b4208400182448541902c907140d821486507450300404142c002e03580c903078450f1101940025602d1800440040701204d05012082c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 543753785 1250 543752535 543752543
    0x20010f090f0c0f0f0e07090b0406180b090a360c020c0901210201181203141206040515040903051e0412120c0f0602090a0e0402011d01090b1209070e04 66
    0x921017081040d1214401c250403c81c540b07041c800c581d440b41040a00c960040e807009000403034445a5000810b03000c4000f0f40508040d400c0d4a14002c82840000c9404480d805100a18894441c1400b00b9003000b4542d5a800300c00a81000d5046505800d01d800601381c00b00164098000c1a10303404151524544ca18141c542085048420600c45140080d8800e00000100c3c1440450750f1081c540441c0d0f00c400c000101542d101e1060040281d150007443c0001468142c8016081846641007400e41c15400c96070140084d1000902e50b0307521032011400d20900301c00d8542181c54211040c1c1416408401072141c0e0f00c940701c0f201c01841c0e040381590340e944954070030b04003002c007034190b48400205c80c03980310710060545107484018680c060316070100c0c0e0585000f045070f2039640005d07070b00000e003040900c07400144a85000401c1c140740a40010301103021010501040000100d4032000581c0a6045000a0080080800e03222452100b418206150a540c071006900c03030b40c00c00284110341d004c3d50798071480d40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 543755035 1250 543753785 543753809
    0x9090813080a03080117100e06180a08030714040b07050c150a1b02060c100507030b04020301030b06040e03040f030f050f0f07060f02100e0307030f0207050120010f090f0c0f 76
    0xa0400c03146c681e0320001030b42e18403601a204201101030102d0050368410f94002000e8a258200035018070302078002c04c21694140c4d0042003034280440c2011003a25400031060074212256442c0070710052003842250801c0b20714070b9010a02600384900000e5074085100250b0b80f850645000d81d0080105008049002002a40c1c3c40c48000080c2111191101c0b0039101512107410300c2c9209a55a0500c000804c403040e00d00c0d80da4081254080d0b0500070300c120210107460446c030b594107588921001030320042c0418002c0da00c2c5e80003190f1420042044074000c0030083c00d1000c0d0b5503240c0c03510f400c120400005c1520345109104840361031100c08550b00034520402401001144e1034002c080c2c03041d28481c140801507024040c612803a00c88180a140d00c0003001c600515078810303691401401c4000ba45900c00c0440d0b008890038003859800c920304919078051104541c490b4a12030100c10301511054481c030342501c1c2030400301020403d1500051002601c2115079555503a00e0340108210b00605105449060701 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 543756285 1250 543755035 543755039
    0x12010618090e0c030106060f0f21091502031003030e0909060105121005010308070209160503011811040e040b090a02030d0e03011503081305040204030809010f0909090813080a030801 80
    0x3189500150b800160203083d24422146600081d0860300780f6403001000c01e0002d11000d040c10b60042c042800c80440342480d00d01c070220903078216140d21340340c450415840c0c1d4072681001401007011409100c0b5200003429944c920303028440a95030f0b0300c3c40c4011004034200318012882c40c41d10f448400d1140b02260000d00345a80b800307080001e6490b14550035180b41c0a2804081400c2e0028050b181c080c3d40500341040d0b45800500c1400052080140468071045d0031380990358005511600703ea0440c1c90240c40000b941c804d0807890001880040001c0c01200f400140005036a200f20590f01d22890250200d040ea071342d1800b1059803603010481009506400c0304969018240c01510352096010700a400041c060000d2106004002c400c0d8000f504e0400011612151424118007900041c01080d01d043d4102461540e031406640180700f400c6060024581c41080d000d480340c0c0c030840c01096182c00511943c041c5003002e0701070354071503182802000007400340131406c20400510014056819a200c0455078 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 543757535 1250 543756285 543756299
    0x70302030c04020901050c011404170304030c0b1905180f070e04151806050405011a010203040b030a141005030d080c030f0c04080f060105100c08271512010618 70
    0x341c0114015030500c030007449000d00a0303409210303070a0110032450401c0080c2c0ad21b42803220141080e03201700d0700c2c000740030010040000e61107031001032031075440f485040158460240d40824403074580c0c42103030745a00c0d1600300030b881c4c40d0184119061041070000c1d107420320116810961910128000d00b40c8000500c000705000403c510468011207511010020350486441c460302800d030019442940c1c5036440700280000c1c001c0c00c0c0300c1d00141582a559070b4000ca81300d840081d48a005a00c1089036a000100019030a400b80781c10201401450060a8120749030041e40d800c0d42038128085c8900034882c06503a500e4030750140003414010a00701c812541581da0f244501081004000d060030f180090a00000403940d0302000111350070b252841c080c0000d50b040c07600303000d03c42e04840e103a0020070040141204c0411000401c9400303660500f2207a65040e642039244910b0540c01103403040e085814080d01e4420300c068400944840703880d82c21050034a0342d03542e008581400801c403100c2c1030003003480e100700085 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 543758785 1250 543757535 543757537
    0x702120f0304050304050d060b04060807050d140109021906080130030306050618040e0142090e010b0a03020609010e1801350c371403070302030c0402 66
    0x4144507000b04c91925440d4004142c6124880101321062900c4603da524a80b4083c010040500000001406103c0c03500c0000b40c4230f030b50f0890700940081080d9003e800a40001c0d005072483c0c94000d4482000400ca2400e800740f042c0360340c4140c00c006180400085820503032140048120140c00c001039080c44030240c1c10002180303c60a0480906985d1040000c03e602c80002800c01042081509003201e0309403000e010544162403940e5155034582411002140309902d5140095040600c2001b400c402010b150300510720340000c03000810f40c080c80300140f0540b16402015920395080b00901099150f0024400e2550040c00001e60103442403100c882c15500c21450300c0104840241040690700f40a0344bd02d501d41d4007a00440c00c00c04001440c2000019140240140e941c1001c100c81225034042c11029203800c1d58544051051211041120074060f03181030405113000c10300c94400c2d8895040d0030908418a585c0304128465150150b100e02c140340120707480d42203d070080c010300340c400701c501d08000003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 543760035 1250 543758785 543758791
    0x30d11030c0f07050a0509010807090e030d051603060608040209040b0712050c04050315010e0406050406020903160509010602160905061f0c030905040b10080601210506090702120f03 80
    0x9184014040e4618156082000d400c40d0400800074242040c00c207400c0c000e003550305802c0385000710b070b003c40100883c0a0000d4140700b110082040000d07440140f180d4641144110f1070f080306020b05000500064010000444031290520784080040c80d03526070003a120444101d402940c04a41e00c000079000c030b9031020041d58002000e1400d0354520380078824510841c0d006891103981018081000d2006040800010040c021540114200343d0b14280da86e40708142c0040c801041151582c0c041010846150183c41180b14018165401c0060808215840903098450f86101d401c494000040c41800440e24160328642446401910b5007000d2180c070290401030003880e0080c01052030342e46d01c038904650850f004c2e4103558909081c80003d050041480071540c01c02d40c840c528000d580c0300e450340e4400c01480c041d0550b04280c0702a83c0c81c2d500680b031031030b100d09201d21103122440c0e00c0f40b9580c1460703103c20b02c100310440f4034003182d8607950070482c1d5547c50b41401001d20b600c2040340c4a2410402000395038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 543761285 1250 543760035 543760067
    0x50607030b030f01090b0906150913030504050a121506060c020d050a020904080d1b050702090405010f06080a17160f15020706060918050601060c0309080303010f0611060105030d 78
    0xc04603020b07000d03d421214200350035104c401c4600e0a001110800303000c3c15801001503000811007110038400250045c2000c1c09002000a81c1c100c42c50806002d2410b540052030002d22140311540ea072802c00e030220800001c121545004842c83ca071794800c0030320600c025540e20340e840c2242d800c4180d00344181c0c0040e248007940e882c820580d29000503135803414440c0c442c520410750251030701840e20350781d429140111281d165800086844c148060747c00410b5950154040b1800425500c840c2030540c0140030704681080e41c107040c1040411400701c002000500644503c404945d0407081a540481500880c0524940c0b940c4c25400d54010880142038085d200b801890082240d42003a0b0883c022640003400441e0015200c010401c8459224803441d254002881070320b0019a90302d81d06d0903141e06050141d041444820840382040c1407080b004840a04540c4003143c6d030325611020440d8480c940c070310981c0e0014060000340107c0200100e2107031b040360809001044100350058080e6a50b09003104101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 543762535 1250 543761285 543761293
    0x6190f0e21270a0905190c1e02030414060304020d12140a02150f040308041412122a0313020d05010513050c0a030512030a020405090103030f0e0a03050607030b03 71
    0x1200e034520b4491072880001e000d54181c24004110140300040e1041d610401409241c1402c10460505503194590084181c8030001a110f03210841542c40000c6005486805000e80600c2120582c0000c020300503150070083c00317803030620f0072010490785100c2101e00035040807000501000003a44581c91400319945401c11100d00808452030200540140500c040180d0241c00e4000d1203150340b03204150880e07541c004900640c41c060310b01805811015100400c80109800c070600418000c0c05080591030098149a40d030b030000039111400e02009490b4240680c84448064003004c8091603070000c404030300858581940e940405512412488179401d90f045248000400000f6100b03100e00e034864440c40d1a00c04104002c0c0c00c2661501ca00201d050340554101030080c004210001a50091a611004940c0e940d079950aa03444c043d005650055800282040c000b0003016040b11280840c0521070b62000b806480f079208002d00c5951502c030103042c075048007000c1038100380710750411210341c5d0006d0100d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 543763785 1250 543762535 543762547
    0x803090a0b0a1b1a13050604030e0f0310050f010f0602120708071509060f020c032a010c080a050703090809010503040f020907090503160806010e130506190f0e21 71
    0x500003802820200c0d030034207400203480020245002c40c01c5e00610400c2507200d5211456640c2555514090005424410788007100c800940d14503542100403200074055a24076490902c50b1030150000b031342c0b8568071100803030020403182c7d241c0a80004444041e4000c020000c041c0350034038030720752100c0002e984103a400c2000300e000c100e141b021200c00d41441c5100040450300da04001c7c088844025903080c015004200d00310012a00100385c411300c080864460040c0720f80304228440300900d00044160030f500f44901c102c92030350060a100d00c900c11001040c8801e5a07039002c101c0441d900180700400c0b201051006407003a502c10000395070b00038803c0e800400e01100607000124504401c94141d00003c0c0c3c07103482401281024003500c14800d856550303104c402c6041c200016203480050090480346910140020a10560350180c80850768000c030039100142800e1554107080305041003040f401c5400c01040c006103440034419228203110202c09000800c07140046050851107a01ca03d2054003024420707 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 543765035 1250 543763785 543763817
    0xd1d1f06050603010b0d0b1509100c050d030905070f030f03050307030f06030b011e0b040b07030c060c020c01080106020615061602150a0801080a050303040b2203180803090a0b0a 78
    0xd6005c2d2001a5140d41c5030085182a082901c0c10380c40c1c03c3d405030107510b6804501141102c01e9500381c00048a00c0d80712140300340c2c021200c480f14284041d103188205080015001e81681c881423002d0f020b8005c1d541d00c02c0d16080401032540c5d5a01c8001d106505800818000c6441031000d541c000050b490041010250700c1c1d02c0105640554106a8400c04448010045040d190700c4040c1d80c9045440070200c040d103002c0d1780c0c0c08a805503106020380c2e00c600240308010944039004160b45203500c00350030041e580110300b0003581d0340203522680303000c0b48c45003001007031142c000510345201e05024018650041180411300021b90020501020701c10007128504005940b18544079954008a100458803801c0c08080100b0590044c5d00041c130320741004440d0b80209401004032507000d504068045025101d490074812240e0701c000c60008500c51a40c554001c05600100041c0601c02035502480040d486030142c640741c1c41440511a031001c030f00c000400841d4098406814588454140545107400041c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 543766285 1250 543765035 543765037
    0x50703030e0607030606030b0102120d0b01180e0a060905091902060415020610050105130e070509040203130b09030406270305151905040b0c03060d020301060603020d1d1f060506 78
    0x501c60f000c81d0311520280f00007680340c8220603000b002440100300700d02c0035201c1c05205210b141da8210805844800c1c0d024164014080d0b100e4003a4002401c844095803103a403010707d0a000e0b2592220b03907082c05400500b80d0054040c030780c0581c03ea0405050480609650390044031400036041760030a81c148000940c01d1404248406401e0441c1c001e48158030b848118043c511410b508201e040c4402030020041641242c0700c50b20584100b1100c1d0f0310f0607166035505407103a00914585170f903c90300000400010420800c425040d480c402e13000d00c400343d01d0346140d1b5504e900079800f5280c0040c01030454108180d910401c005554003040103110703106a142d40b90142003074281104143c16030003210074004007901c090103045040480b54030401c61420140c0c1d510b501034101070300b692000c01c0c000c0045422a520a60000207083e801402004160b1350707180090080e41084203801d8406141001c00010407120541d80303e6003444c99000760a080c0e00445254051600380c2c00005081c1d541d0700c030007140320303250f181c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 543767535 1250 543766285 543766291
    0x4020c030702041b020d08071413150e09160e0307031109070203030f070521270a020d320a02040e010b0a140303072f0102030a050a050703030e06 64
    0x145558a03100c2c0144400c3c0d80d10401c21614140c05111928201980460241007450b40e07450300c0d030103945802400311510304101c4010079005a000600150406d400b18400003122040a0000501d641c84502a1000305c0d05180480d004120030000070121040034540e00b2490300c090600000f40c06190001ca0711b010f82a400031141200d41055001a40c5808035402e13610030850710046103546810304451602c0e0802402140034400007086480705a90b00082c403840000705113041320303103c1c507081007880102c04030381a258140c02d0342030282c0b401c0d01001050501c81280c0182440f22040c03100d50300c2403604840d5003211a0782039a2403204040011a4545c2c5250307001c6441c0040c241290305004100494483c502e1900e49681f41518000e901d848440c080011202c0b0300301c0c1c0e50700381080e100200307040d4821104018030240c05240d41205a60405c1c0340c0ca4420641100e03d0543c1c2000800107981ea4402d42d0ac201003c45c01c01d100071007442d0b01c180021311505200345004a1a0000c007810107141500076 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 543768785 1250 543767535 543767557
    0x608090c0f0120280503040303030b13050708070e0307030503091c080d05090c09090d0c0203030c031216090608150a050603043903080706150b0a020c060331020402 72
    0x103040006082490701c0c006100d00c8680c0352805444d40c95a03a2100e85c3d0744101e100007014107403606101d49040d43d411a07a612181c03401d501c14012440d09040050000404495500c08220f0030079070301480e801e0008101041e01c2e402401507240240304400c11000c00c10360310f00c3c0c23413404400202074030004984070042e000180010b98041203c0c2080c0340442d00f480391a00000d4050803a80c020410034640010314145002d089040055040d046800400e0a5100302510b844181c48001920a400003004100700e1103580101c500649030305c60000304641c46240b9105980004010b034004c205400e811000108204c0380041c114069156108003280345900125400d030b5288602c0f00403000c3d00070840003401115004400d9103010310411104851404480d8080a0b01100c0089800d108014072644503402c42c41c103104801d1351342c1b550f030114180e0550152819030014000d0195103652420200f007078074003422100e801500f0311032001c3c0340344042651480303c004d40e42c5035030351400b40540c0300c1d0300c0104480111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 543770035 1250 543768785 543768793
    0x80f0a0302010c030b060316020a020901060e010818030301060807090909062702151324180510050a0e09040305041a0403021003200a02160608090c0f0120 68
    0x1260501900311072107540807209050a140d4125003e988010071217500451031000050301c50b0540208a00e00344019900a40262030007002040890b00000303403070003a1500340d1700ea0307055a68008102211500c0c103074254119500c00d20041c049a0301500420f82e10808910306442c0c510381c0c502c1c0d060150340c3c034024259511030342c1c3e143e02070388905400c160120520307400c060000c41c500300758040f880c200301c00511408004008540c0d07280c200c8066603140010310301408031013030102c3d6207821040b450078034090090109490968500c4441080101d51040303400040c9004205658000b041d40c042e400803121034200441c6c0c008104980d51744c600098050760095442e00d8841d400e0030703140543c1e92148600c00007501d00520080006035540b42c141500b6648500d000300e1031002d90740c183c031000a0300003114003160724080b52008102d580011041c21440f0312048519501d80c0d540c00540d17442c0b60640725030b81a504801820407003030030400c04005640314180f5202c1901040c01c04c816183d082541c0d0541501d403c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 543771285 1250 543770035 543770053
    0x706020a080603010b0306010b0f13030b0a0b18011e0305010203130309050609210304081c09120b0402220204091a1504170712120305010605042706080f 67
    0x503002070390720b6200c0401e4000b040304203071510000350b94001c148170f40950200b00050308890340104600790384001c00240d20243c0140d469180c8624107031000c44d000e41c0103d241c11000009441e18070010010410501881c40b01c80c0d003094a402440282e0361041a41b0300d102200000006009100030341c403d0a00c8142c1c4103040040d450028480103456116910400050040305031a6499800860142d50a90340311441018889803240c00c0d4000c40d808542203000709401510f29030f09894010407a000c82d0340d550004503454081c408140d08071a0700151002c522800000c0040c1440031610008004034262482c4920340303c00e5100c01c0ea0b0258000d00040c948a880da40f100d801307084010f03440c40808580109064440d208010064003c500c40d001600d07100d070241c000745a4043c001d240c040d015205240f40d00002c10305002081e008151402000a81360100000b2054883c400750343c203542020451120300300c0103200400d00100c9500f030501c1499599100000c071000c040005803204101803001c2d0090385 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 543772535 1250 543771285 543771287
    0x3040303180f0f021005030712090203070503011506110a031403060307031b03061128180906030203061302010e01110f0307060e060c0702060904020a0c06090b0928020d030c05030706020a 82
    0x5c0c500401c1c04d00b402014014080703e0b9401c0600040b4016901c0b400280c05011400000d00d054001e43c801c50b0954078283c85080d0010390aa900c0b805e6030443e4403091100c982005101c0c0e96035440c0103011300011568500012180440001960030200003000c8a6945460352548940c2c60020403c822450500c0c000800404c0101d0040740303461001201d000b410301c1707003025103002e800c055001141c41c07008100c65050a460f0180d62091314000c0f00480c200741c100d0b22407031013100a05042c0000e900c28400c89e00000c250303501601804100d5503041c1e40d010804600e4000556030601c00151030404c034000e54219070945207080010304a214000e171004504112400c0245041c10005403031404215001c01003500941c03507800403114070100c15200113a6461100754201d500003105000286154244248841800500c0b50316030301520203c0165505844418a03810200c0029580c0a41d004240514030b07000d85000d451003260980682091002804a80d441c18116880514100c440550100f101e100c11 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 543773785 1250 543772535 543772549
    0x6060712091a120103111201020406020102090a0b0a0c030806030a1a040218070e1009120c03170703170c0906070b0a0c090501200c040207030503061c020603040303180f0f02 76
    0x50010002d5891426429204000510005000c040c00d200d41c0103928038444d840301c610240703402c13212800071515180c075044002d01070340c4000c8085108020798400800d030102400116410161140c5074041c12441656044e2404035005220740c4c8e06000b14980100810700c054071510920310300340408a5185002c2c030411152000c3c03a15915180049903081080c0c8681284807614203010403160002500303541a000c8448141581144208402814011041140041000e001d4238860803460708065295410241a4010202d000c0d0000d1114141c181080048850080e001011220414506881c0d807020a80d03a40c003100e000c80301d41458404010041096100c0c200c8620703090301c0c24640980c940b9000134108441060140e0213004444191002c62804111400c0b800310090070640d1107036980e003001381c8039410488046000700110440f0364000c488000c041d01c045a4010000e505544031900c08030028183c0c100302108000c0310484a00205501c1e00d5070700c0610348280745400380705590344184800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 543775035 1250 543773785 543773819
    0x3040f1e09050c070b0a18031e0509010c06090809061303050c0406030b0a0c031b09060809030a020a030c0f020901030b0105101706150d0509030a02072c0606071209 72
    0x800e407408043c4034495509804507490944c000e0510000c98503500c204a00906000a0b401c0740180c0541d80c4408042d000480a4540c00c1d1204d040c1ca62130100d15801d669610840c14503a000135690180b05001030303841c0e0b00000c900790041404905104150011803403a81c0010010314041d03c20304402c108210007004140442c031400d0f81c0505c80b880c61a65080017021300544a000226203071150240d0140c800d03840102d010b20004116040d40301080c0d0050825a114060440000c15090010322261400070841d80001c43d654001c2c507401e022601c04850440c00701404580c2c0c6800708440e2405a91054461406540603d0792200ba552601041001340000004c0e0f64007800a2602c02c55121003810710080e50104080c0c071264050070142c00e0110303091003201842143c2c64540410300ca00c00c8000006480d00700b29940131204080d4a401c81c4050085040480d03110b0000154989801288802400c90b0400c43c041d048500301586c6503540c2c0410000300440100181c2420700400040d85901d100e100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 543776285 1250 543775035 543775049
    0x140f0f070b0715020d05011a04051c02030a06060b09040f0624020f060405010b04140709090e2404050c061e0a05040305030a030b0306010603150b07050c060c0c15040b090409020303040f1e 82
    0x9c80e051805003c24880c1849445100c4501c484400e00d1055440c107202c0a00d1107079202c0020030040c0d03100e0300e04507010313004920300070b0049140680007100c3e00d00e40d10440d02074454a05c0794103442680004c40d2009843c08680380411809410401a009402007100314001c40c070070b000100d47d450601040c00210780c150114614826500b00500107003071f810244840a640640d000440c400e05c4000d1000d02c0c0c0080500d00340c2c1c00d400801c0000058280c4840028020b81c80380095551201c3e40c001044014056940580c62544010304c60080800d51440104401001c80c10400d0600d83d40c1e44540f82140c01040c1c003900441d845105420340b0749801e01000d400340c40d5178142001905400d900b140c01c03a424a00511003d140c2c009003800c144030b4204102a40048001c00480e51a41803c481984a0001c01212805102c8040904400c2003900c800e40e0150b544241200b41071600785001c120103400740e88000c0ea094002007102041c0d0050452006c405041c040444401c2100160045080ca04960340f00c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 543777535 1250 543776285 543776287
    0x71a0a150b0702151903060503010b090412030c0e0d080d051f090f020412121e08160c060c030b03060a0b01020d05030c0d0603140f0f070b0715020d05011a 68
    0x22014114441c00e0764076064054550031205441100a2805882454000000d8040011642100302d030316812810660304150024000051114248a05071105482c01802c11081e02100e1078840e10030b5200c0780d2580344d240303014500b03020030301c0c0452810000300f40107560100740040c1401c00c0c180c4034021103402c1511b00404040041c49074044a01c403400600842007940d803a9000240101030300d8051364060465441450400091032401c6880c60711101507a40228180c0913007925151050b04803400503007115291400e031a82c42e91a403800500b8003c215809002c401d140c2c560209105116185607680c0b640c800042404c000700c01c0604d0004020f08403c401421b00300b8204081c0d90224500c0f582a41505280342c03280c458081c080124020031482c001c06a140400000c02c0c0180011001c0e01b05d608032040d14511551800d0481c3c440114900310300d8941e00c5800100039664004001300f00340c0380109100c00b40941c401150a007664803e006209510351558018000061480c489101280c0c004080d2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 543778785 1250 543777535 543777539
    0xb0309120a0521040b0106050d0e010f140c040608063001020a0e0d020a0b13030f0c1508090706080a0f02030f0403020d08040b060103050402040b060304051605030712080c03071a0a15 80
    0x170b0040341414060101003101c0400c072184001b44235004140203000c170074028441d076000041e82e10000c181c20301c40902c0e40500b5038082158001003e0465041d1a07981c3d45801c1c40f9520441401411120040f0740c006a00c6404150b50b032540d581004441c8010300c01e000540c0da0a0705400042411360321a00030ba00c02c0e040380c843c9000599034800b000e000c41c1c0c0e25020090716864001e45070010130340f039a0300c0a81040000030510b810402c4480321401651a0136842080d02400030104441c6450210382c002d02981c00300d407044c08100d000b4040e056200030340040c041088a8419910b03030036a0001e0b92101850002a002c0c00205038060280c0452207d5514004100d464103440d81004000b0207420203040c1a070f500042000d54840c2d1f003040001c104054000d40c2e81303040c58505142d40c0c200c42c41d0010b941c5a01c081000c101d6150209090045601140003003425040c0c40d04e4048040d8891700807854980700410007840081c0c4450701a01c02d401c2528481c20b05407500600c09002e803100c008840313140038180501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 543780035 1250 543778785 543778793
    0x5130611162d0303020706050c031501120f092402270a0e09030a0f02070b122703030f060303040509270f010b130501050a0b0309120a052104 62
    0xc0ca4a9941c200c004100c0842102c600755a450400429403510354442000520034550550002c0820a00c6400e04021542e903605860005002c1900d46070307102801000030b0300c1a1361103119240a01d503d458000030307803070345150b0300c02080320304040044403102101607851880d403030300c49004407040c0c130604819032600c2e000c2a051134168000841d9000e042001101c1c5007150b0700e40100f0f55001d0045004059014107003e81040c1c2e0303941040d89050300007821042c0e420880342c4003048450840d003200345010308001c000c2d02c02480c3d11900805c11701820b81c0d5403980e051444d403040400301e03554600b04003440d80c81c2803280c0035211380d0300002c040d14043c3d801004104015118560349542c011403522108044500c40e0055041c4070710707920700130101d034491211703420023114043d480004c22080c209c5040440c00b1510090000313a0301e00344909540940d5482d001c100c0661010003d5a2000101d0142e82080b403103000000c0044c1c128034000400500e0103c1d51030406401c000a082f07080b410a00d001e02c0914156031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 543781285 1250 543780035 543780067
    0x10612022409100212031e061203030a0f0b030a11010f0504080a02040b0f0d03032c070b090328140a0f080f070f120305070f09030f1505130611 63
    0x100c2c0303000d8201003803201c4140c3c0c070070b1103014541a00100c50940e2400d1000e82c28174040807010202c2d104080500200e520303450003448218821a0030400b5505540e65a5049402416484031040b44140c90709640802541d040c08610440c6108003d464040c085100c001010204640310303140c1405070821050040110018042008940c1164081102080b100c0411820020944440d400c100ea0484502c10150550001c41401034440b80c680f180c501b03000792110b0500f880ca001e102180c2c02c0307080240880401ca00040c09548006011549031940607041203002145d0741107034811000f040c43d541d104120f6290b2142d08040e10b0400104076105442c0c4806080101040c001400d11000240e690320302504030013601c4105402050715020f50f1220304101003282c801000a1000134640400205680c3c0640c0307288941052595500081905680d41d0980d044040d10094071007c4207183c0710f01c00e0482038040c2c05e105a01515800e90099064509001075801000595070600001d208503440440894 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 543782535 1250 543781285 543781297
    0x1f0b031e09190b1329060103110d05071107080c030d2a03090504020c010207050c09010e13080706050c0a0201060812090d0c090203090f06060906100503070e030106120224 75
    0x8003d8032280c50351040d118200b0290306004141c000256000b410f800800303004800d110000c00c0c49030b031903551030780011012100c034103c5242c241c0b001844030380700700c0a803980710650041d09810b01d110540c62070001113190043c10b610014565101e40d40000700342c1014050703084d0301c07030301400c0510302107101070307414048a40c0a07044d1a00580c051152001810f10030241b43c0002c000143c811946c48041440c0c03a400707580807140c142c4070780c807840c0700c00640c1c1d00b494040d0904032522204030b1101901e0700181da40c96600b44000598001c802848070b9800300d0b2440c8100d50145d0411012641d880240c80006401d42d425603100c030305076411401f84807403c0031522040b50a01c10044601c000c080071301d842c02080c3c0d4a440e40044111070320110030040e074041300140040c0c041c2c640300c040b2001c5503244030410070051400c954164100c5441d1039525202d03130065018580042e07090034403e6030102c0e010042402c684481d401180da030500c8280c0603003907041004006903010884102d0001400c040590705010344641c1d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 543783785 1250 543782535 543782543
    0x807050f030403240f0e070603050c13270501090501051216060302090102030d0e010c090807080706030e0a021818010b09040f0503130f051f081f0b031e0919 69
    0x70742821380d0414942c0800302c00540c3c00c6003040a80d42603030450380d8401c2c0703500499001c00e16220100d8a4421030034103a0b5198011401032039000c60520501c403622a18850300380408542e002c0b83c0c118414994040d0030701900d1004d800040c2c82d0b00d4001041000ea040c8091958150405910a601121045200b0b41900c045c0c0c2400b60b43d81100c500101c0c075501c1401c41461665181481e110410360040d0000340c1010074591300e89030f6047e00c0e2400640c03101d03041d114a8102da40040c200b085030500a41000c2460030801060364010511030b0042058066030b0b1501048010400040010818107207600c8500c01d501080200003c4000e40086a02c1c40c00291014240f8030410718287c081142c1001150119613540405850780b50303940400d000c07510401c1c0034040c070480c01045802e40c000070507244461038001591350072100d46c07038208040c1c0d076101c40d24100c0d07401c00c00161408030780070b003441c4019805540c00800e041c0710145695000044010090103c08070303074201000c0d014500c607410a80723406071504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 543785035 1250 543783785 543783833
    0x60e010c03200a050618030c07060320130e071805090a0905151b1206090c0f0a0e3f01020405091305011a061608160807050f030403 58
    0xb004001c203000c4080901280d0080c41049151410001c004c1480341c00740340c1041d251845414840800d80d01ca000d006049030180c0d0005100f0000144241c00ca10801c4080c8600001ba09c14407889241240c1d00c000c0f0000b8035200041070070085444210b42c03459004095103810a800c50200b5445508024240b09884c400c1c92450041204003440d50700c1407001c7caa00008984170641c8081d40e4441d90340044074880030900551300410882c5042c40100c0e4080b07000c2c0074000341e03140c0d0382c881044181000500881c12101c4144101d60340d08103041e0003000301810307584400d050700451030108015441d5500a00320402c0ca020320390300850200c40801c0c2800401c0d90081d4841090104c1c941c2c0c0280111b5100541c00b004001c180000025160100940280100004e101c46c0319841c0c0140c0325030865075200ba80201007040f451a01415900b8107200e4103105080052a02280d80c0340b105502111080680f41c0d028001500f1041000402c40c034540c0d6000c03100910b08052940e242d00302038601104030340000d40300c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 543786285 1250 543785035 543785057
    0x60f1a1e091b03090d081f170c12010609061703091005070209010303080613062411030a050c0601080c01020c100c0c0e011805040c0b0708040b071a01060e010c03 71
    0x110020b0950a100d407041c89612403134000100d940d41c03d02d2203002400708101401264804c49004416a034509110103207156142c0741c211036428150504488031010b01440312104070075901c901810050a140030004540e590400c40a2011581c81d0307442400145c2c0c1b010a0101400d402000380c42c48403204803000c0001d503040b10019030740b61061500080d0f2000b00c08001004043e00042114002d0b0001da98110407424102032200c11a01103001d4201c000d00c1b40c6600b882010694000b8540c004c5c65464404a0016243e0800345140c1121700001c010510102d14054140420803600740100600380003001d0541100001075112150b1181c6030780210340c95004001280d00449950048640c001c24a189003581c511908420391004c1c020032441c035803603201044000b1014060140142d800107144050380d131422000000980c400e05e0105c43c004010700000600742c100c040904200e038041c040e41d07801d0700c690f51a140c0c424201600500103008001d403007d00c40382d07442900185030a605003000683ca81c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 543787535 1250 543786285 543786301
    0x3040206160b04060c021b06030c040e010f050f18190212270a0b010b0309010e07030f020a09050708060d080409090602090f03030c06041509060f1a1e09 67
    0x807190109a4228454160700a020440e20595483c4118080c440030043d41014050803600c400c9503900e0200d5400e02c1c40c04020081c500540103580001c00c5203071191506030b607041480c420f48002d9025411420802908200b00d0030441c005841c120303170480d00401944200a03000800010142142c1c01544070344000c090100d81c290304445e440003d841000c0003a240c8103400c218083c0716503d840040300000c1804c03514841001031101c2040c0d0f407101c03407694547c0c01c0c4408001c0ca508000d2400003a5034891043e000003075000d01030480514000e0000c814071540c1401401011213559010400e42490941084546584655044c0c6c002d51b00301c0d0480c40070300319801c0c400f9884c01903811541c0c00d07614200c0e1503c1008540d90041c1504c040540b450201c20b0142405c150f103900440070054500d400410001c0e00049083c040c41c01010400c040005030000f4544030042140c0c03101100c0084541c0d20074043d00c00e91840e5503402d0111a044507400542c0d2441d07031030301031918814248030703000747c48070404501c0f90 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 543788785 1250 543787535 543787537
    0x190f080d18180902040219140f0703120f0513030801150507060e100204180e03070f12020a080f0705060603061b0702010909051e0906060108151c110f01170c03040206 73
    0x100e074000308155103d003c0c7c43c000750400500400074101041030046542100703842d801c169103a85207100da955040030500c0d2001d45174201c410b11810b120968440351801c48031124800e0602401d400d5000e80e540742514900605071103010f07000001d601c01c03030804001e1850760000454504950190b00030919040040300c0901d081c0d11381d148903641c607002042c080780d200a035015200c94640c0c1e0060074402e149800c00f4840e100e105245000d8107518070700c0010400700b0103003010311060200301d1040352800c544580340d00f0758641000c0c28121040c4000a191020301104024aa410860440240201d4140642000c02c0400a072a0100e02400c6c085880c10039603005080303138801003640f10018412494080c41100508144890700c1c4109001c41e00854041413001402034030443c01a11040701d55203504a9030340741d61458000d0198040900c000d410801c5040c01c078078400e00e80c4244010502c3e40c42100421900c8260b150b00181002503061004403140c4ea01d4540a8212000800c0d01c1c0d620344031800800c03d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 543790035 1250 543788785 543788801
    0x20f010e220b040b010e13052212080f070f080c1c0f14010f032301020c060601080903070b01151103070807050111040302060711190f080d1818 63
    0x7122440e005001c06541c640d0002c1a030000100c0e010851012500700641d1100c050640d1030760405d64079409001c450300ca680c0101e80210049240700d0552000c0003c03035240c0e45003100119198a225012066a503810120703881d0070540c804000040f41c0342010004104550510001003000320721404104034802140c1210000004030000c25100004610131401425800307095943c4c551400e5a412912090648920305031244006000e5101e4a1600e83c11a00001e900581c010300b14142510030140e035003440100f203020405c41c050109890110000f42c00220011304801541e00f00b081040e001581101e007040c15034030455a801744600709010b0465101c1031804c9022010b1100185442c203000c3c03004080d1600d60b00c520004c1c0841c030a541103108050041c2e12000303402000c144503800c001215840b60038454000a07141c40724002025501070b1039030829602050b50312070141c2003407001c2c01050042c40310304041e60510480c1605844c1010038400703c1849880990328400402103c205900e0300b042078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 543791285 1250 543790035 543790069
    0x105090a05040204180b060a0b0901050f0d02160b0411010305070e040509010b060f0403170a0e06092806030608190f0302030d0228031a06070f02100801170a020f010e 73
    0x805179030385161801c044002036030302d0351080400f40000110030103450100d50982d14180c0d9950300b0010414504185500401d804020080c0c0a1101681c1d4800059210014030701602c020006402c050400d9202100c50441e00e604050170081040300003a040205203903840c0003510006015a02c83c1552401400c000448552104001842c282010201809482500d001d1048080084450411701038a8840c440941d008506203041034100381c50701c4d4028080810014013460540300d0040d014204145c01c1d521070f08810412100f02f03100341c5500d03200d0070001d44000402400102a80ca5402102c0e06c0a000d0042001c440d40500600f014404c0c001d07600240b143c00d0080d5103075041e6502d0001042142c200008004076021209070040c2d109005440325040c0c0342220000611055040c4400ba601100702690704040790690107006807250401140303101003958460340d0300e504040303410720108401207141c203140c1d1210800e007015076644105045900c01c24200500c070090f840010605030001400321803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 543792535 1250 543791285 543791321
    0x20403050a03170709090518070303120b04050105130b030304080109121416060c050405060d2018221802010207090228030b030f010903080f0105090a05040204 70
    0x10400030006562003586100e619480000f150554060100d10802c0359128001904d1007003c0004808580c015500584202410075162141d2a001454644c65070302c128000340c00180b108042171030f1441180407602d000c46061040b035161100080000182c41c60314022aa40c2d0403414403e03a80810880307005000060090001d034060782403840c0c010210741080b0011a04070150000400e15a80c12503541c0fa50341c42a407603000d80b8503110b0000900894184408ac8401084003048035039070100079044102d0a02d801184a000d08400c58210324054901c01072074500c2400702c074a10040c3c4402c0e8203402081660140700030382048030184440c07020394841548a0385040074401c511120240c014406034002c0c0c0171039100641e10940c2e00c080f4800c1c1c041c0070420304034040201074540030301e0304102021481032402180c080b0f01200040e080569004810545c3e0391340e04074207400c05800c0102d880c5d00030120307913008401c0c0d0f1410380443c844690081042c291180d4480001d8110350380d41c1c0c400b1400c00c48800440c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 543793785 1250 543792535 543792539
    0x19030c06050301260607081b0c0601090c0201150605030910021b0606010f050403060e070f0617100f090203280b120304361109040f09050c220204 64
    0x1800c658004c1c0102a1807011120603000c00480c41c00000c9110884030000f00700aa0ba0540101c0701d41c04007070840c1c0d41c107040310391083c00e07290032003006020506c00820107481c29502d8030411034101d60346070300e2510559040a08403807030b4001002140007107540500706603989594107003189082c5640341c1301c2d02e161144040b4ad8a00689090045d0081c4881c141301240c4d90303030700c030080152401c6152140040014200708024000640503400031201013501000315003140303880d104000b6101010350004c000042040318500e02454103402c6d000d403c42051a00300c1541401c00910652111850046204258000000c560702000180b03001481a004800715600070400700c640c00003818a0070324691080b041140309a101c0b0f0004801c54049034405282d4840c0607400f5524584100d110080303040c0d600f1008500784032001454012007100c040d004400d1a07032061003508020484e0140d0b2403248403e403401035034100142c00080d03030109069080311030708501d0041d00b4035206004000e40d06024414004500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 543795035 1250 543793785 543793787
    0x120804061b030f0e070b042102060307030509071205030403300e011202030c040909020315070f2705120f0f060609010b0304080301030f0311010c0801090501080708060619030c06 78
    0x30002080e150600103212880754a061307143d803200c0c1c2e0300909050f000c01700b00801401000d11040a810405070300841a2000ca0743c00160084e0000c0f200c1c400466128000c0010541b000d00c41ca601800f6803540d40442a560394849503528003a5000040c4003c2d981d0b0620080030544883e6924030740c1d00101c520b850441b6200f4010710000824400c0c40c007042411403078421560f4603000740d0b4031441244202d94140703460f041030240500341c626001c1ea0580a40b0105100005c41e11a036244104066140c00c1319004100e403004000c0101c88108400240f060010042090080301c03021040300d1085480d01220015201e80c2c60500020702100f00340c81c440c0b0000d20203840404207400780f003031408903907012043e030380c1e03031810030f4a40320442c2e0003000c5400408c0180b000071600040280024040d1400942c803014070300129084400f51058040451044001005000094081c4601515a40000c1d1007075614140d82140d40b0759001d400d440c8180c0000c00310243c122000c08400740259002508400300a569641c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 543796285 1250 543795035 543795041
    0x609070e10030c121808090d02060d0207120503071205101e08010b03010b01020a120512040f060b030c0a031e080f0c0d1701030219091a010e030109120804061b03 71
    0x183c40302c0802c031015078402260b9058440c120041d415492100d42600c2d0a545074109a031007a141203034840e480c09080b90160301c0303071b02c080c1c1880c0726a110016a2412142000403000a0584401c1d0800c4400c004000360107600c040d0034110084501400f08841d1030740c9002081e001c907503800c5410481d0742601401d20b842d00d125130b6801103481d100700030000f4204410034942a01c0e03042a005015a10251001c0005142c40c00c8800350307901c10303150080c00d2450315404044501826941074032020390810f601c40070b00280b44164403240d0303000c80c02031405000c500c001c20400c034458400075108034010009800d00c0140785020f200d40c69400303030480f070741c40381548107450594103c00d070700380c4040c030803044001112801125900500000c0f01d81108132a8a10350030081c80707071204c1007601920030717510340e00003100d40d00e03400340c00700c902000608509616002400103003076440c0340700b40e5442a1b04090058001c00c000d0300c142441d0345c6d030601d00b142c007070f40e207d051a00151400c0c0d4030f8003c8071b54031103025451117a0700d64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 543797535 1250 543796285 543796301
    0xc030909010f030804030b09032802010f0614010c05010b040c030606091505041a071b180b090109151a03011a033904180606170609070e1003 62
    0x4858440c16600c0e690b82218104070ba0000400d5240d003000700307101265410b2151075201440c00c2c212407a007003980000c541b081c650741d20b940c000b81e14181d146d030280b10b4080c02061030345201d20030108501131400600c0c41030607815a105905021030b00350540103000c02900b0411400c1c0b4041d20074481c00039400b500034000c0c01c45100b01400070b4110100456140c11a504070307400303050160341d8a0700703044c2000c4c11104400c8441803503120002c420072041d80041da1400003603030030035013014059001078a4030b00407a503205d15056800e56003c0c41c1042828060b500c080f55641985d542c1d203000038200080d02c88120100305140c005640c03010700d6600c40081021510021410780d290f07054500105c450355030581c40ad600050307400b480d04403080e11402c00700e5010b90004034039030b0a411040c2445481e038207030030720b1040d4003a80080900d440200404000400140600b40045c540d6282c26104034003401a10a43c52001800c079901c1024408045910b841c4600104075a5000c0203045840341001c0000250040c0068 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 543798785 1250 543797535 543797539
    0x90b090c01020f1c0311040806091501090209011b0615080a150e1f0621120507020d03030203060f040c020604020306162001150305150109021312050c060c0309 70
    0xb0340100e41040b0100b2480030340c1c4640313008420003488029098014010340c116104d500d91041c840052908401c00c205805040d050002e4140f90307032103001400c050041604181b102c1030040104000340d0340e000c80c0070204a040c41443c00c80c030300002d26060024014820301000803c4515201003950176001c605407d04a21402445416080c0803080005684000501002c960480c1d40c01950654900c0007040c0004000680011000e4940244128000d10380d0b90f040346690349940c01008002d26030441903c81c80c480d0500e1810302802c0da001681d40d045c10800102003540210100700b00751070308051420f2b034260003441804542c0e1a280000c0d5100e1044900368441d21410000c00c0103c1620040105251180e9451501080c1c00801e14100864a20ba04541c250341e14500e00030110b58440410018500c518040c106482444414a8842e5010f81007901c0c214810802c45402c032001e403504c1c0c0111991f10901c050307100e042e800d01c503040255100130290007800010b0411204403010005110784501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 543800035 1250 543798785 543798793
    0x708030906010909080427051303091d061e040c1214310c141207050616030318080d0e011a011b050d0807141804050604090b090c0102 59
    0x2c1d0704440004c1d030307081903c0500b11050412040c001241c0205019803001c2d181080304000c0e0206402e107004882c01114061100e1815440040030190700c102080c0040040b10080218003200b07105003103d10700042d0030648207224002c01640c0b030044420100b504e400000300f08003c501d21810016001c203030615440d010480c50500c0d00c0404070940003038a0b000d8062a0003504d40200101114104c090b81e8100302084070b117070b1b00c10340c100107601c0459110140400d40290310000c0d20107028080100c182d44504d074050b400014040c841a2511001d40305030110f00c0e0210b8000c154113040603002050510f20b051501c00c0000c40040c140661803004254030111000c0c200128164107403a5800c842406034083c40007030b07041c0034035091136200e000e403051071040306010040c44540941c3e9071480c00512390010000b0030100d00411060700e411180c86802a580144507034581003e00c0d064000c40d50060441c42c1c401c1e503451001c03601580710b550002c1c240c103902040191071414080091982c40d40005219401445 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 543801285 1250 543800035 543800039
    0xf0d0206010929060d02041707031704060c020607020a0e09010c111203010504090507050603091f060303021c0932030a0308130602090409030314010e060a0b03090703020303070803090601 82
    0x49070160380f4000f5921440c20030744202080400c00700e5400b8214a85505d82c0900003c50328180c01d070f030100e4000303071140010301c41c0500c2d5207015242c0c0d00d00044036001240b0140020032005030415100a11903a04443c03803542c50741c507440020002c0c03000741c07c4010820708240801c41c140205600c900303070808440c0c0360310010307030590104142d43c0c1c074400c0c03031840b01a44107000420440c10650401450300c0d101e803043e103089a031200f001c1007090300111890b801030340c0a01407a1400c885924500d450100c2401c100b17001031810b5407400707590342056040381c808440d44210a407003018407610405000e00032900e2541c1e800c01841c0780707914031050108071150b110710030300100301000c0ca400140c005500760306840b00c0c809651806010000c44031804000e80d1025006c1094019940d21440341581c0c05100307440014002e026000c0704020710005800421076803c00c1401d10409030b03a01040102100c0d003c200346981c035510082424242105580001d403d880041800e000b000042805184034403103441c101d9400d43e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 543802535 1250 543801285 543801311
    0x20708121f09060602030a1202090306160e091e04050109170c01111222051006080c0117130c030b0403091e120b04020f0a0806100b130501110f0d02060109 68
    0x40d07aa201c1c1301d0245e441040410b1a4902400e006440385110007001030802c9400700200f424220308441001600d64481c3c0c040201039040580e0440300507080c0c5150341a450710540e0001e011101018003080d11102100040810600350407030440c20b58400c030b0258848200c00d4104249030480010680c0650800b5a0f10f00910100400e4550403600c020340803c1584440c011800007130785200180d120010340200365000300741c0411400448200d00a80092898540030302d0609140040f901141003240c00c2d05100781d204603290065812904074200c1e08ca041f00350303160108150410fa0700040551a5090400061607002500c0380c08880300b82205c4031015540c3c0154101c15601801504002c114008401011424400055900910141c03280e03a1840c02e48000883e240160b07030041c40c49038009801c0054005031461102e00410000200038141141403c01902d02e04c424028141000101c1c00c10712200c810802440c00c6440c001d02c2070301c00d40c1641c010000d4488070240502c0c0b03a62424048105403003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 543803785 1250 543802535 543802541
    0x2a0305040918020d02210d0e10030c080f0a090f052506141b0f010609060f050f04020f16140601210605090709060803270a09020708121f09 61
    0x219070044c04040c4204440d03003000080f00b03801d03d40f08003060f4001c0e02c180c9611780c1003011140c14a81526008a036410140c1001102c00203039003108100342c145100344000a401c1100c2c15001416000000b071280e0b103014024000b4900600b0150150201d060081d00380600446c040c031800d224216842c2416250a04118044a0074818100003605c540703440007001c0160030180212003a82042c404095203405125850304141d00488141c60755500401c00c0900014402c2070002d04501c1640304119107020001f6407900c603855540c5004580000368110141018030440d81ca030090051120a00300842c1003001141c0000d0408640e94403034207002203110381c0280c00b0075240c0d9628191441a465856503502c000d06406054820548a021800b0410107170600600e405803051900441c0c88010301010303817013410300c1ca13610780c94841645422a032007600d81d00414000e40e80c08403009643c595007480c1c8262188250703022103107404030540c01e00000f01f1010304030340c1020708010007540303803140c50f030b01c81c9011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 543805035 1250 543803785 543803831
    0xc0806070914010302190f030f0c05040b0702040e010c1806031e0b1912110f06070f0516260c030c240301090b0a0602010902010804032a03050409 64
    0x124400150400c0b403a051059145640a0103240160030604032a0301001065640c3c030601002c01c00e5034043d00306450b8188521101c2d04441141032204030078440c030140c0148500d00840d089080001003c6081d502c841e0045800c0960300002004529100d6500900311a0000340355110b10350404400501d080c0b19000b1107d1900621900720000302062580c400140005050320b50000d02c50038151511031200800c0c10014081410103880d480070a203806c0c616091030110030f51040d0365461440f0b187d51a803509a805250f030154520f480c16810f81455850401c510f1660024420703804d801281035030b10451034041907492495580c012511300b00760191104060140660980d03c588100e03000d61800310403040c222410403103d244050700d0540d1500055200341c1141c21001c1c3c90f52030f00c8801e0300f0300801900003003074244020804a01e00f580024a03414015002400b003020441042c0122400030146e010800c400600e070b91184025807034060016003007446040d07a61450302c08a401021a1541421a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 543806285 1250 543805035 543805037
    0x90109060806090703090f0b2d13170f1809090c090f071215050f0a08150a02040503100603020907031a0603130804030303060509070f0f030506060c10090c080607 71
    0x200c2a41e42000880003015915007c5d20403981207858540860b102c50403147c040d119007107803110820400070184001c4440b9004990302c041e5208104101000c3d80101a02c426a0140441002014a41c048000c40c000c50b09d50310314200e400a001081e502c6540c00c0d00351854030a540880566454442054840a824902c6ca4014103294001740840d1004114140d10500300d05041100c0341084000004881e0012486581d01c20b0810041c01039250561030803200d00c1d0110b602d000f0440c1480055070300c818000c200240300d0b0307141501240001c0324980503100680700203800c480444980342200305c00381c201c3d0302c4283d01030100400829080d034031a004565a00ce104c1e6126408003a029050145544c402080c0c03498903410610b4140020b110307400140300540c000e40d0045200d504010410443c16800740c03811040c000040383d4080c1190b0071800d031260038046400d0001d52980d0300c4011030354510940e10069030900031011941c000d41d600303510002c081401801e0741c02c5100c0d101c1c02440c0da1507600b912100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 543807535 1250 543806285 543806299
    0x90509030d15091503051204031509020f0d06050f010b0a020d261905010504090b06041e0204091a180112060207020306150301050a060e06010e030102120a02090109060806 75
    0x6503829a107030403030110202024000b4404a0f9290048400c4400d00e000018107901c4284040084c06410003103540342d15400d038640340c41c00b45541e4606132131441e01e060103561355440740c0e060000c2d9034803e0b0140c1071200020303200507040540d52410000404c01100c400c14100380c1100045626440b44098030501c0710283c004044002c1c0c2030034140c41e803501001c031206c0e002c003070745105080f401c070301005403030041c11100a2291901500b00303d1a040da401604901d015503c0c100709240810201c140309074100b0420744000405a030302a0705007020320402019080002d000050018004402d64071080410300300002c0040700d03241c1c0302c0401103003503542503c0c0850078aa00d4014401c85800c6100c03107100c5403260f08014501150b40d40880d040c050700315881101d5040400620f40141028000c00780d00031000b4104110044c20803030380030508100940b0300d6040000316100c02000d0f407004d6041703686511604c2008039051034a20310300c101a6002a030b049000401030403000035224007030500ea5006000c01400c2d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 543808785 1250 543807535 543807547
    0x11518080316111005041a0a08010302040902060d1a0406290f0d06080318060c0a0602160c09060302030c01050a09121a0709050901081207111906090e0109050903 71
    0x494280c0010140940f804030490121420340c0d9144445001126460303213550307480d01e1500c908800382c81e618060043c081c541c2003100350f4285520a041d42d064030350441c0c000500078540d0000c00d415000d400c2078010a6072074001d04c1c486031481c40c180103502580864040c460b00351921130118101c242103a11300e00d03000c10351598200540c08100644000e00454024600380904880580160340e8181e2201d01d00303820014a2901c5070400c5d800c4070342d01e00320075a60b50349082982c4010980c0c401ca42280036025075404580078000441d0011b0700b0880903040102441100d403149101001403c162004a00c203200e01001440c25500503c01c0d141800710580b24149103d140c900481c3d004010202304540f03040303800711039072800559807074110f00590076940c800c54901c2c20101030080841c5d068000410581c041010b5440c0084000101c8600030b6104031009540b1203e0f201081a008441350100405400c030400130a40940c03011240040311210354a600840c3d0361540c2010407200192001d1015400801c13007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 543810035 1250 543808785 543808807
    0xd0503030609040314030c0a0f0e01051e0405060c010608070905131b050d061b02070f1e0806130302010b010f0c030f11030c0d03060806070e0d05070503060115180803 73
    0x2081e44035000c1c0c28100e0300c40b190032480e041a54800c42d9030f6450b180c0b0100e481020b00303501c2700240011000d00d0901d01030100c20007001030413500405c104043c03035242640c4000350742454001500c00a08000d000d403901d07071a42c540340d01e010b41620f008400c00e83c890170000052000d034a00459002e045101d44a0007039107415203d4118201d0342c080c046c0640c01c040040012207880c1d842c0100101409030030000752038072103400705001c5001403a9004045600000c2d0034091014046821000c80c1d40c01100c2c0c1c950301100000000d100901c542c0082540e000390070400c1800200d410001c200c0a1180d402000b002040c00f00644050a0000610b00011040301c102d4001a014506002c01000b05007804d414860720715120a00e1684070b1032030180d045d0085900c035414140c142c0101c401038101c1d031026116a25200c0002070544080080442c455601c0b80300c40c00a1040602960b0040c0c4400f9054441c10344c0c5910b1b240074003548180b21100007400c0074002440e124070006401003514440310213580b4105840703039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 543811285 1250 543810035 543810049
    0xa0503041b031e0318030302030f090d02030a030309021816030207030c021905030f0105150910080601230402090d06050703150f09110a27050616110d05030306 70
    0x1c514503040214100c04000f02e1030f11500300040810355a0500244200d600c0c0040909043c00e0300c11940c1d000c00340050001039000f1003900d014034242c1c079000392108001000940c12001010b0302035014000da282d014140340d856081014214000e03201a035141c0000d004541507202c00303c0d04c01c550351282e680e18819003813207034000f00082d60080c908961034003103e4000440c00c450740b130083d07180305140c010100043c0c1001c0c001c05408107451002040549850100c3d00034001446e2002841501404001081c500c0c50fa192032010384400001c5811541e15180e01c081049509003004500e812401c1440e101881e06000303c1e2802f043c0035295504c28000c0396038000240030b02074404030626841d92138905074581291015401800f0055284000300e00d0038100004a03000c519400d03401d04010022508519003189000c40d015103111510b07480010b084024903880d0340b0a81005038072400c00a50300c40d51501907242c0084c0035020b81d9103a0700030090780c0c1c2084165014044000d246400030f10000c0d8081c80d00741 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 543812535 1250 543811285 543811313
    0x1520040308070602120f0105040c0302160611130e01050a050d0f0b0601030f0c09031b120f080d0e100f0e101119020609240f04170f0702010809030a050304 68
    0x1c0f4058240045518034010312001191006029074030b90004104528040c010810561610b040462800001c0c45610351020003480c0090110340d21841091080510342041b507040c075860360070801c80b00e9102d044070002c0d1002031090314880d59020002240c0e600c0c1206160601e01ea1014000b4211241c607038440f06400c200900d0035050541c0c880d90a2309480f454090350140c0b00155450044003819031400c000c1001c40502003490141100405000c0b0441d1007500035040d40d0041e80a652010389850214090300c2030714400381440d410240d400504010024484801c070164407024882c15031440f0000c01118071340e440400f5640d2021080e66030055003a802641c203c2d2203290768a26144045e100c03810410030b03810b81900182e120604001104409010711601c66840e02029800e02001c07494000d14164080c1000152050b0080410700b00f0403200907010510040d4402546c58090f109074481c019002a2000c2c4d0100f020400050310100c030101c2101c6503a0a02c0d11010308544464480c01e0a41240d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 543813785 1250 543812535 543812543
    0x915150a09080643050a0201060906030b0f09010f0f05160f0909021804062c0106090312051e0c070e010b070f0516180f021e0307031107152004030807 66
    0xb0090b0701200d0780e0384d0114055200c5550302c44940d80d11064a00a086560b603a00c0b00c89028580300080c00010860010300707400c07205070b03411200152900c8134542d004104055000120034604080128151441c0e08002d10424030703901803801107842c190b401d4030010b407581c8110001465020041c400c1d4030071980540390b0050f000000342450050180400c04507150f41d04001a030b142034080d0b002d120625004075601c6490401c0440c0c400323514121001d80303206400e000c003c1200c020f440d00215040d00c15003d41d0500c480d084404450001144640308150307014484d046224065120046500401c00e40c2083c1201d40c1152118030706119a1a030540300ca0005004982c680070702c00c091003240e0380000c5a900540741010b8100411100148050110707010300500d03031103050050082c85010000c400da80c0c284510958090782d81ca503242c01d030407002030402103044001d4250100d000b0707061103100c446a007184981d4500800500701400c40c0100b00030070705072040780100707010003041c80010900b001509100e449 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 543815035 1250 543813785 543813871
    0x1030c2c0d05010e0f0a0809060a03020f070b04050d0201090f0206070f08180f04110306010e0f0a03030512150901030305222916020915150a090806 65
    0x30000180381145000300540d900d0b911550210311a01c800c4c840d42c2d0409000c00001c101180050307170303080b640b4004d00030070500c0381a02082ea47c00443c003c1e0121140e88003419150347e0b032100c00e0320304180c0345d100582d0191590b1082d44030440d40e10780144250403120703811041510440400394208110382d40314443c2100e01c07521501303900b00000c4550340a40a950018441300c0e181c41d4091060004a41617008014032450074020014217000030001180e4000340c00780b8213000358a81900200d030390090b6814280d500145011400001c1c960301c0005000c0b150245146014140c440c0b0351800d10800c0100700f010380c806200001040040c1c06400201000b04440c0005429409021422070340c03400c117070f44001f128101c400d4600345d51410420300c1403140c803680b541d13581c2040084514500400700c0260024000d034030782e0010640c007540080d042c000c0d6100040120510b072148415040c2aa000031603480c0110f401090701060607100880c940b0300c10481c0d625024107801031182c407032140c0e0410180c0b204810003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 543816285 1250 543815035 543815117
    0x230609060703020f0d0305041101050a0201060810090606050d03051b0f0115030b16080c0703030e0a1103070b0a0509010e1f0503180708070303030902030313081b01030c 74
    0x455030090064640a90007034500c0e06124082035003400c40040001e0308051800c000c1000107071411032604402807081c41c0c07080e21410200001d038010300310764004c140c42d4072901c0650100d50103140c210091441c40748d030060210a65841c1445200c00044a0080224200307005601c2003044040e81d0a980c00c2c404406c440c4e4100c038407060907086414045450701c0b840705040047c000c2c0a05c070b000c2c45070840c5124200c446140041c04000704000b030050030030482c00c0c000003507907018036101e0b41210780c1480c1080c098840303103043c074500f0401e41549203408900a006607800011070480010583d41000925194103281c1400e078001140c4000910701e0884d400a018490210b1891940840340401c451544a00f81c1c0c0703082401d4070b00f0100300500281c0c4103907808050148103401c400700d400c0e412664507040209000d9041e01c0007a082d070003188248001d08684160000324040c00003400c141d0414a1071404041c0e001c075100460aa494001071100800c0c510030f14058507250340300c5c3e500d104444100d1005940340c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 543817535 1250 543816285 543816289
    0x192604030c09230702120f070b010e06030d171306060e04050a330c09150306150801051806030705060c07150905030d080a061a0a0f0306230609 63
    0x1006603042500d01c0d6030b0b81d402906884015075107581058040480c00f145600d00b450b0000c0d51440d10340d442820503540401d1002c0024010301c15501010b50000400586686070032004115000885000388207106002d0800011401040c3c0d400c04d1034555071700044117955016081d403064009510485e88280d0f1100c1c00500010781d10301c6a8040c40c8694040c106940707031410703e04030501c400168082e00610900e0000741c60300344c401c51034081d000c0856011423020710210017940c20703504941c0b1200920200d030011101e07a03580360744110169001d10003041c00784112203200b100d01c05424000c89412688061800b940007107101d2041d94012002012281e1082d11072010075941d4114540c02c6440c0e91001406000c0c2e10300c00341101500307140310328280c81c00070702d44400260b607039108030030a0f0144038030031004c10b45044645c1c0210010f4042a07040800201070002c01c46079580c415810f400010b81860244440b2030f1080c003864017103981d080c00d07207001101094680a84008000789899200030300b002981495 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 543818785 1250 543817535 543817553
    0x50705040504050405060f060f060a12090c1d07020c0a031428020a1a07080a0c080a081603051b090102010b09091c020a050d110c09010e070219260403 66
    0x5617214101902c99800c054501030381c00d802c0541810321824804030001647d0300d0301c40a44048040e185404c4d6004882550b207000100740e414006003c01c1c3c66a2004903078000700b050002ca00b07104a04119416945800c0101e861b0a40c12445940c001c0e030362030702000410070120310aa07a501301c6205940305c3d041c80850050100241001091030410201003400c1540f82c0348c51058020862260005915404a82102542e2050103c01001080c011a40481d06480f13006000c2d8260b50000811b0303a07600a100c4c0241000340e0445620303006001c0c0985c4200c4680c442d01405000c4c444200400029031031a14551200e130300110329460442d9650b040485070b80d1351303d002d890300850108000d003e1132030a10615803540d81f1451550001e540c800717440e00002810000c0d2410316045289041c0d04210155590300f41003d04a0714440e07840306c000800820081c1316020740d1809640983c0840702074070300007560007550b561104070140c1038403014407040702e0010b100c035206000b050100b01d50524040d1a55221414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 543820035 1250 543818785 543818791
    0x9010302150d15050406050405090304030303111b1605040c0c20090a02091005030403050d0903050d0c18060e03070e070201110c1006050a2619051b09010b030a05070504050405 77
    0x10704015510400c8135090a102d0240680300549040c0a03a00d0a4268940d0300d00c03039880020304040d901c0000241010b0103900740c3c4c1a07410301441001038041d2106502d030ba0b0300ca040700c000310740e0018070f40000f0307403450a441020700c0e020b02d50f2520625003000303884000d1188490a042c0c1c074000c400d0b95401180b0b41c1c5110309076110304410040142c0b03683e00c1d8000e000305958000c0400e0b050010401c2440302083c1c000c01542ca0090291302d011800c42c0041c03034119002d0207682400c4d00701030300300142014210341040d141000944442064034665581c0d01d0101c13496007059040d2a01500b200390240508882c1c6200f26902100381d000104806808038070001d05540b0080e08070810303401c54017000310b1884080c0100e000401084510300300c414240340c0c940c3d12003d80750000541c181420440c00c0e0300740000f480f1000c64282e081f111602240898203000d134070383e03401d121501400c0c40c1f5007440c1705075494482682d40c180c40600b041c02e415991080c205400030940a044001802400d0000003072580c5d8900031644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 543821285 1250 543820035 543820061
    0x3010b0a061115010503060411010c0803010605031e0601050d0914070e0103060b10050d020309280b01050405040302030415021507050d0e070303021f090609030305010e130209010302150d 82
    0xda0b005164400a052880b82106084545282401084195070001d40385810276007240340e6407110f8451500590382101c221030010400440030000040c080d4009002c0c0d80302c1c011170f0401c41d918107003440360b010000a0454070f40f40865028003034200049002e90040060340e125030031078000380c0c2d6101d1500b407803c0600d0380300321401050580140b0170401240206520200c5c141d1305210580280c0c940070341503014960361140c949030b01100160040100f08001405408140c24070f200c5441041920340c90038002c59401e4840c9144040000740b0b60800e07224440c41241c05038049c5040905040540003004c0b1090f80410441c030800c4948510f614a00f20042e001302c4894070b40583d2403a400d90040241c0d103c9a403680d219420452080012980106042100c2510b45000b1481e1180320018403004040428002d0061494101201c0406415510050684511481d000025034580001c10541c03000108002d4001d03a5045c0100014209080c10383c807000b80ca9843c1500705041c01004000b1214440c018031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 543822535 1250 543821285 543821297
    0x19110d09050d0f020307060507021006081c052104052b0801120b0a0e0a08190813120507031b111003110910180b03010f09050402030c0f03010b0a06 65
    0x30100a820016801c040003103040c9000e0381c0864490103500c07130040032000f404d01521a000640418403d0000628800402c0c00170080113407503840d81580d1780c040c03090351202d298540d03401042d401d02481c00d07140e03403203d1644940310041e8814442c411509014204480030320400070181050090302c0c902c80100504d5035007142d0030340c04d02140100b100e50b040e80589400c02d1284d6000010aa8011407254811212000400d12401c00d07001c01d0300e40207000c00090b00300384002c11000c0c1841c10003141030009800320b959110305504c03001c100304124000884000e00303207421104072410a0380544080c4c04464000d041220503184518500017210329666400ca5043c143c504442000389011402c20b403454280c0c0c9030802500103649201b51941c850115030b544030303001e545001ca1240780b0074080d0204094042c004a01842ea031840c42c15029003007809014054112001d0128002c01640b241900c103d80042c0223001811020b410301800810f4401d8070f64042d5210815560952036a2034100c00400203a5642 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 543823785 1250 543822535 543822551
    0x30702030a0b06090a0504080304030f0e1224070903030309020d0b01030b07030e0105070f081308041d06060a0914210c042f0f07051218040b060319110d 67
    0x18010000900b0025002d03e06407c1c030007c2020788003030b070741d206615040c201410741e01044165103201c04030500a60020b2400c00c242e0381c600002c02c11403c0c100b422010030700740015504000751250001c170360075000502d02c0c3c40704201081c07081d00034464035400644908030b2480329883d107041c6010709070006d03104054424184209154148a6800c000e2036110007000682800c11000704030890483c0704104001c20100800c0b24104003031248060b00d40d002401c20342d503580e5101110980c0e500d170401c2480c61031950000401030306120b000c032290780000da40c0b0020a40d05003a40449412101c1110341d0300f100c3c00c500c102d0781d031004003144054265035000091448140840c100030a407564403088000c0a91424016210211841e81802582071000c09054a03100d40d000480301900550070003400c203100f910b000002142400d002801401000c03840200c00c11140e0b001d12003079030802d240c440d4014030300f007001800c600e40d0240d103408103c002c1c680200b600b90420790034605a42024107800b40c0d01d5590300780 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 543825035 1250 543823785 543823789
    0x5130b04080f371409123012160c17090a1d06040e160e040b130b0c130f0305070905010806010602060a0f06150801090e0304180e030702030a0b06 64
    0x1c2e120103500d901505805400104001c00303012003000e01038849100410145040d0b41e4410055055200c003604503894001843d810380c7e0552060f00d0b107003403214401c24600c1c0b00c4d11140d0003184d0340030845500d150314584a00d05440041a1140e803450300f013080d11668072000895a80c641100140c40c1c20a40d0744030070646c0e081116001880d80b080a401070a156050100d50760310361038a9005601300c9000415000b9580d07040d013480403980d40741e100c0d0b00f41c80c003000c00d002020414081c0582e01407000385003a6615400e44d80c00451030314402401e0341e5081d4001541f017007008130041001487c0c6180465500d6070b103030600441c66050b03400484540d04804070620408119121f070300c0c014521000140429450504041c0d00c920002d464000c1c601d0310351b031350710407004015080340c4000c01c060425102014409840145001c50070f02070403901c90b08104410700315410000603501a940100d081500a41c03402100c3e000800d59000285903d010500800740560750500103450b8050045005541600e80303001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 543826285 1250 543825035 543825097
    0x150a0b0306040b0f13170d0b06040801140a1107110102070f0b0c0f010b0d0803060a1a09011806020c0f040e070608090c01021911040f05090a02040f05130b04080f 71
    0x12405650405c40e01c2210045220359504c4c80f131007501c0c221002c0d6600690106a4042c5c07000c071078000d400401c0020005070f03520f0154486417031130170039681181060711030b1031b8000103031800814040c104403800d10922021a0040c581c40030103500500440703803c0c40c1c1e240346603c07840c01c2c603a010000e10400440d0610321540240b00c46410420114002c000c0c0c40703020030000d94412480303080940304620100019210380c480c00c4041000d005994142c00f811004c41c1038083c0c2035400100624000740341c50120744500e09100070310105840954002e808042000c20601c0300d030820004910ba401030f11040f01039a1001c06210f1070001e03050340d5441c45403038a4048941840c2510f02c011a50441d849a2034100110501039020050b05502485c408052003180000a000c0c00101c0d900c846014980800e00010480004070b10345030078030980e41441200a07040c0d000c41182d100311106240c07020000342140004d0b0f082c11400785c0c0b01d80305226040c05e103150908052441c0d00051451103000380c40d222147c080c080c080d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 543827535 1250 543826285 543826291
    0x1050105030c0901030b070e031c170108070b16080433090b03040201021f0515030102070809010509010c0b13150e0a02040b060d0504150617150a0b0306040b0f 70
    0x1d4010840084803402082e8141c40520028100c2c881e032402080446120fa20394a001400c02800c0303c4558810388006d0845d040d100c400080820300791440851070200c0d000120b03049407064000b50201c82e2401c0d080c149181c0c0850450343c45000080c50308000154400c003d44003030301001c0b08a283c4100b0b41841c1c0149000d20744002d04202c41c515143c030354a541d10400c0c003c155160320322078a03225102c44c40140c0c503010b85403410f5400d084480c0024007403503016901c8584035107a04402510017005060506080b440f45c280d01516182c2e08210200c3e40c2c0d40980700074080900103141403c2c4105440e1a1242080c009032440f800219212110105000d081036020010503c3e11008024000421024682d108401c1800078055500c504101c2000e591754000e4814200d61600d0611451516140202c03000c5840c038040c2146a1602c0e20109407074000742140146051308d08001c1441d481411882e00410b80001d10103c59152100358848064909014160155218040d01c007224141241d401c050f1075401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 543828785 1250 543827535 543827539
    0x1021605100617060601030b0d0b072a02010e090615031503061815040204020d1a100801030213050903270307150c061d19030318150e0c150c01050105 66
    0x20507140f00601e2010a40f145c00c030034242000a24000d42801140210010520103400011210b0400a02940229120a01c0364200b0380b45448c0c81120180e20700302402d08000640007030007151071400c50b070800d29005504840c0007400c2d10302101d1000e00c80c1d03800358801c80b800080003800e207034a0640b0f0304040195030b40040d01042c441c000d1142003030503d585c484180400c03c401e4013007000440d084d500d4690403901003100c00702080c06035060b0961100004100350082c00d008031001402001054481c64502e41038941c000c0c6441c100c5161000100080c007006402283c2500003000500407810328100307186410710441d00c0072444891013208140c104142944440790444610ba03504919030740c400c080001480c0d11007400145103034504800c9010684920307546003e8403603140c061012041d626000c43c03c0c1442658240032002c005910303640f6a80328040010040d0f1030301b58048030100081e8025803055141038080b02e08030212000015618101400298003003180050490b030b03443c10038005d541c050401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 543830035 1250 543828785 543828809
    0x30c070303020d0813111203041e050301060617040303060b070b041b03170f090312091f141c050f0a180506060f030f0303251b080c010216051006 64
    0x2d0380d18030380d012121190041045002c91444601581c031031202c1c03070040847d1401c40344c0701d540b903114541a2801d00ca0b8004a0180b1640000a6500c1c05000f25810780c0d2031a915031701e481420b41c14500195002620443c203164607a200030030031568207405010082c1c080c00c01e000380c0e400d2500300440300400740d40c1d02c7c10344601c10301010310104440c284041c4000c640780f0b40140d81e50268041c00c0c0d0705401000c003219030502400c01c80100b1501954007410b403005007103c1c4a21444c042940100e5103500c03482243d00071a00051a0001c8140c000c0d001e07001c01d40440e104000c003000711144000844404540b401c80c1c00048109005840607107104821110150ba882d0503610001c54998a03a1403c0c014043c500c10741e0464404541c41d1014452501180e040c80200ca03101c0c203009001c4050a89032100700005090035884288546114444200d0310230f03070176908100d40340102d444401c00c41c0c0c4010007450b4159000c00c12986443e904540c02c09d0781d180254090101010b0041c0200141c0b10347e40e01c03111035280 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 543831285 1250 543830035 543830041
    0x11030109060909020d02061602060c0708010c09080c1005041503051005010c021309020607140a41070503030703210b221107030e0405060105040b070311030903030c070303020d08 78
    0x99505000c805c1c140c046030810b4039040b02011514140d00181070082d000b240105200d0b03143c00d0300007402c006030345204000f4000500b95070700c202c07804001807089214680c0007660055041c2070129100414070300d9454400e14142c0c480b000e211026221441c2080003d907980208100743d0700c51486200580720918000d0340e64015500040c1681d1030040906890075640d070480411503135018100c56885600010981c1502e41c480c100e1a12010501c0003504c058031808511805034178009200d05039000340c0261031044941c403031184040d442c0c0c143c111020038841d4090204480d5000c0002e49480c034801c1c1e40f2100b52218000071000c0c0c41480518030614a8108010031580da0740b010410741103d20008003120301e030400d05119002900ca8007142052a05001410b01709155009001a130007004c1558103001684807080111080c2c4107510840280c0f000500507000020b00c0780707003841210300440d0100e0381401c02c40d00000341540c2c04410342c8505580408420800c06406000341c2c00390444608010800e45 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 543832535 1250 543831285 543831289
    0x6032a161101030e0c1504090903020703110f13020307091a0d0f0c0912030c0f0b0906070c150b18100815151017090d03110c0307020d151103010906090902 68
    0x17503800c4110341c4110130f03040110100020b91410b4500802d001c1c9000c1c0304a41d400c0c2400307074a601c5240410342d6854000240d0000c00e003810306101c540c00c1c001030b108442e2162004040c1d002500301400503c06c0003450940010078899441030064a204007030030346596000c945009004440150404110a0341418003c0104a401030002c404840044009210600161800311040c244005e40108001070508103c8140301c4240100c1e0312409940c4110781d80c1c0d849243e0103841080e81d10034018450002d184111200c5400303074211203100c4c10003403e6800030414034452240300d124111031025045507421000c02040004110b40c040d150200c007070100c101e081c078050048000641107500350003030303109a1031030005910a00b0b06c00303200c0d240241c0b0504182007503808640c8070300300c03111410006401c29150781107182e511404c46480441040c02145007041c03503400d10091003a200d0054908000815503644102b400d4081d65041e0310001901076940d41c101036440045039541e820020f41c980c40c2090031801a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 543833785 1250 543832535 543832543
    0x5040e010513020904020303190305180312010b090f060408030d140c0901180909050d0305060612040b0c160c0306142404062105010606050906032a161101030e 70
    0x82d6405592407031071075845001281c0741d0f100704130203815645140054640322a5241e448180681c20030b22a1030032a0140d9110b00c0e80e00c2c003907005003255807080c50004005010100008000844014002c02034240f004400200d03e604107621000030b43e000003980c1c04d80d1480502c03980c0f00120056002d02481d0820b1280c000303013809040322045c14000001810820110000300010081c45080d9003807080341d06500e003a680701d1a1145211000c01d0400c0045051460158196043c20442c5030801090745d855880e041c400a101400107065505c00300103401d405610120b035203902034028102a203602d840c0d0f160a408880c284c25181c0074900091007480215901172600c40c03908150b138081100c2995111002a004044903445108140c3c0310708031603202c0c13a5403280a401c401e070041c0001c000482d55180180d50038810f20218940c4136204100240c80041c1c1e07100d030b1031480208140e03110340d110a503819803442c6901c498800040395032504210710803c1100307507109041d002c00386010b011003a1452032640da2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 543835035 1250 543833785 543833821
    0xa1d0a0504020406030606180c050423060712051201050901060c20030d02010c0e04060b0901080a0915020d0b0102121b1c0e090c1201140d02041505040e0105 69
    0x44a4540010400b9980c541d00060051500040100000c65a80c81515400e100301d40750717080c041e800c29288682082c040c0c401d607421a2400c0400044400310035080503030406813000e0443d8013500510426000c5840f0302000b50181034251540341d0f4031091040d0250703000b40140e0002c0e100d242c4d00401130000c0b0b903002c43c0e178901c4103900c40c1d100c0da03030f17111181017810689109280340d03900351040c2040d40201660542080c1c0440201d9180c004141d5501e10521040d66214051100402003c110a0031694071401d5050341c0305444400c001a01d04190380c40110b031582c0140704e064032503000300301440440784a1090403940c0740240000e1103081e08200903000c0900404502030400c80340b0310841c02d0034120a01294403e22050a00d50102000500003e8065108010b400d40280c4103140004c8203d0545001c860548007142d4034011140c0c41c25103102681000c14804680000503000204010384403409042c00140325503000c903101030705041c2440202d0b40e40c1a00e18802d68102010700c14050800308400c98 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 543836285 1250 543835035 543835051
    0x90515120c3c09030109172a0c0607080c03030106050d060623030907050607060f2027041e05060105090a050904060e0d090321050a0309110604030b060a1d 68
    0xb48820100000030f00406d0150005442580e01581441c28100c62000400c003180c0144000d120505042444a10181c0b84003801141a030044030381000780e1400701c01400e01c1512600c0d2540c500540c030700c81075081d90420303072061001c41c0c80411010b501c1d025034021500588090300d000c8504860064854030018503400c0c95495210000010540e031788000c1c0300d440050640a061f89a9442051a1900081a035106180300140c9401c15114000c080212520390070300f2400c0005042c0b04c600200344815480c0001c0c04070000c1c10480310003000d81c6950003002d420224108105a80643d00507044c01030712070080100781008010401d50f45507075160201d180c10b952095035101015a581d14000b0001c058032180b42c4118440d00c02c00020041d8021000004d884c880d21000e00b84080c003003044014416001c0340c01020900c140a0108014401c0e03010f1030f0f002e4013030500383c2141c0700500701181c095403103034000355010524a41044042d003004001c00001b00515491180001003100c0d08000c9a100548111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 543837535 1250 543836285 543836287
    0x7060f020a0213152c0112060c0e09010603091208010807090e1615031803050301091503080a030204090e0d020309011d0418020103150303090515120c3c 67
    0x1031001c0d005580136010900007107000741c038602c0d11007440c1c0711004107108841800d020340d8040341c0780303061a00041354100e4200d0080402e080c161130381e8500152407500502c0041180f0b2402c481429600c4031034080c001d0a05da1000216040c0b1303810000d05224060018800b0b00003c07000401501c4400079480d0200d0b2a000320005040718480343c003904225180c0d413500710b00701c4c1c1204041038072010280110703031410054504101c0c2c4512826690600c40001c2c00c0130b004030300b041c00108030b4140f5542000700c001c416490b0001c41c4070344035518040241c00c50004000029030110b410b100b03056562249440c0004282700a000782e08650740025035910034030060750b04004c405c2e6032040c13142003002200850510001c0c402d020b034400d030b920356040e20048500b080e4002030400c10303880b580c8282c040c207150682e50581d44241e80641000244060041a414030310305505041124a2220340001c2a040c05100301081096039202c2c041300c481c2109120304070b03014007a40c4603183d41d0040ca80b81d2503004c0f07820035038410f45 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 543838785 1250 543837535 543837559
    0x120b0409170705010e030309070f0807050d0803191509110304080711010c0519030305011707060341011e060c08070b070309020109090c1409040605101107060f020a02 73
    0xf1400342140c10b0040300107110100a1040981e07000c60440305445200340c224006030b5498841e560358119510415030007100030081d09011400b0380d00196804920b0b0140c5e007200c1003441c584401101c20040c1d05002d140c640c008240000039550050340c41c4c0c034000300c40b07480c11400c15407580d06140c0f166100c028080480c070407203034146134007452020380001e4024043d5803d10b580000405038442565404400092811740041110441c0d104401451b1703048500401455003008030603801850030201942031a04520001c0324051441c2d0b10700e01140141ca1161180000311030744002200c241038009035503044ca006107440c7d098150114000c1166043d150015006450341045a900c0c480ea10000d08881200c6c0c0c02c21103242d405400944500d8400e80e25510026641c45541003202c080602d0000003ca02d800e400440c501090060701418500910024031165200005140c122040c440c05002c1150800a41d010f1036040c017016000308090b041003078650340c05400003074a40081c1103000388205450701032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 543840035 1250 543838785 543838793
    0xf07020c090c07170f04260a0627060209031c02030304030f05041d1515041202120106330f050c10050c0c010605030a032f0607120b04091707 62
    0x40d1810710340420b006141d40d095607140302005c80e801070180075500e80400300391850a80b0300544400320805146c01a0812a00c01d0361504094015844035031078505901080510000d0390202d288400c0388610070045c1d03503450b02014582820b40c40d203e0380310301b180701010006030113801004481d0700076414074040009603281c81c03065445000316003140d8001010342076495648565100028024140a41c40380b0180080000700004100021702400c00722070b041c4020400c400300c0d03800104009200401810361895500301d8242180c00683c04941041400070a500d446030900c01e40c00d401c04c0345040c110341c83c0c201140e07000c0d102d18450407002c0c003048000101240d0f03e680074000849030030305081040c80607003000c0601040c642c10012403036100d5440c03d8400141ca2800060010505a01d91990181c1a0684ca1400000d8440b00248546821144100445400140b00d4a4070508241e12800091301c8281001802c984555006501640ca0301001d42c01007010b0b4040301c008189400500350b0360700e0b01c41c50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 543841285 1250 543840035 543840053
    0x9060a180207150605010215070906030b030c100f1803020f0105090103020903070923151219080a082406030a020705120406170f0103061104120b0f07020c090c07 71
    0x100203488040c0f9044903184401650b000304e000c807030090b821680c0308511050102100101a5120b5001c9031480e0020094940070790041c3c03120310350060590344610100c00c01300ba490445841d842d0b00041c07803008202d02a603080600c4008001e4003608122903a41181e000c14039903010884c1c43c42c1444000709102400d42e04c41d40403103d009078064140c0d450a5520000d80c005416040182628004243c200701c50792034080520720f100c0c203c07241d071811401c4006c000340300303401d81d14181009650040d001c0f0700c0890003000e10160703852441141116500d0000f8400148454400761015250456018400c0503407050400c41a040c1c920449145640e9225109410024410040001c09501580981e0440c039a0020054000c5034007540b214032820b0403440382c0d101d1180b42140c000811700a0b00c00140045129544005140e180101150b480d0580b982c6015014040e0683c045420005070420000e1400085201c25080501d50008002201c0564005520a100244104c4074894081811420f0141d124 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 543842535 1250 543841285 543841297
    0x30f050f241b0d0603050705010201020c19030c0f05101a060d0c030b0a140414040f1401200304030e01030c02030909040203010f020307020a0605010602061b1b030307050706050609060a1802 83
    0x50055503911854501d07801504d00c80c07205032520702032100001825401802282c0c0000740310300c040c01d00640c025140b04080e0211401c290100841081c0c03000004856148862146002c0c0008141c070f4180318903030300c0c26500c42c0c0409403002085000c9004840d150704003130355407070720032044042580018000110300802c058010303258085410800011448200b40036002203c0064906004080c9140500c442c2d50b07106076802003058031420300580114000c440664042e040d4a070000c10344e00d040f41c1e007400003c01880b82c010f506a2001081c00205500604442c094100a080034002d0440c120b001030345034014a020603009142e0040010119942981304448000c83c2c400d0864032424072410003503482021010413190a4980030005c60054000164284910031136403030000000302009046d4041d070049016683d0307112940f4400c10510700c1c280f010314031451459448030b484040f607040160986801410143c040c051203020701c80907440c0c0c4e207444002d0b00c400d044c80071103070391014511100070310440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 543843785 1250 543842535 543842581
    0x40212100f1208030601020f07152021090a0e0105010e01020f060a0c110105010806010e0a06050604060f050d051906060e030705062101031104050f07171f030f050f24 73
    0xa410003103138048001c040800544501d07580c52061740749c41c00640412449030042c801d060752048007054043e8030000c80201060940330406030030212181d0101d1205541d6401680b82d4114060050003256403155501c08900d400340300421460000e4010141c50304406498034500e2900d495001c5001405002c54040e0301190100810482d80c1d90801183c8414081c020840b507014224003080001206000d02030036210014850341c40c1519061040c6c5031031642e04240d005000081c004104031000740d22500384074100342615523203402d08400d0b11104850050708580180628501d800c03030355840000381c0d4402d03201c0a56003195903404d0944407501418411103203c0f0300380c5154001008100c0300c200f1004d44503400342c9042c8a00e0f01c402980c001905000c42d114000551030b4101c1000804e50300b031196801c100c000f070f100103208042d070254003400222030b0016140c210034460080100304040002c40314402011014284000011700c3d45181c1c080c00f000000c00c01c500420100301180880c1f6600540c410745 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 543845035 1250 543843785 543843793
    0xb0c280513080708071502070e181902100201020c06130507030512070302010b01080408090420040602060411030601030b0c1c020a030f060f0f090218040212100f1208030601020f 78
    0x159211056a84002e80110803941c000e8010003da886c0d142800c0f6035801982d41c0150150606004a090349500010070300341c1201c21510b0042c0d110741c3d080c4820700e001010003601108680c01170062108010300d003000001107a1040280c41c00d6500c0104000750480d03101c0c4095050302c140b0b400c00d81e00d412020740000d080ca01034045041e0715018250000c190080c406e800034401101328a00569110a04840c0a030848000300100c01d03040c03406900000300da4401c000c117440c0603101c000341e403005a00690090005030307020070f0a000c140b10381c20058039011803088004103160b6040d5500d2000d4400d018102c101c40502c00301d110402e41014994016019501c040215100e80c44200000d0213030080e02d401c580030520741803020511101d001418030070307a0510030074855503d140c801070100030340c00300c070340e40400810345070080c0341d65a00c1d4001407000b03451085204017241800c90595401c0030f00b0b03034001844c3c0c8084940801025141c1d0710011a565004886541c0b80da075000e005034200020b4105107103007405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 543846285 1250 543845035 543845039
    0xc010e06010e0c2d032401141914040f1a070c06052808041a06100c0c0f0e1602070e041e0203120d060605030c1902030706050f01030b0c280513 63
    0x1b81d03007801d48240361001050f01e404024010015508007181c01e0f044859400108140045541e81001c0318088080741c0c90412614010340000000a4000d901311340c035400c41b030213001c001d0028040c184c48180215244041e18190156031a00c0c2c0f0054188a504180700010803030418503440c0f16075503843c07000c10032006424901601d50040805a04403412120549c1c0301c801c1103607800c940d01c0c0c09841910f01420645007685420350a40c0c0b0801c03400411140100030800120b020f292071140c0800034031800e1005159401e0001e80c00a00c20805609d481c21540190702c1000400484521a500550061749050403c8810440c850602040c000069014413a92803024040d11400c4000c1c4080110380c1000c00c842c2c0d44074642120303a44010b45400002e1709042c041207526030240d000341c00d054156070045030714140c40f130794441054030000c0b20701100315200c1c0350040084c011000001c541c00a41c030100d0302d2800c134001c18003804900c8044100c210715801c0c4442401d0322030040781252250040008068000e075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 543847535 1250 543846285 543846301
    0xd030207030305070c0b01050f210601090c1b020103020706090209040b1005010e03070b0307050c0f0f07090b06030a0c02010609110325020a14070302060c010e06010e0c2d03 76
    0x50300c0480d0880010386018001418140b0542c2c0b071681c002c2e41b0064101301a40380c002004080307640300d0002a4064124071444584035201c04207403600b616840f010384025894041c00b40c040794508212030044c424403800c40720030710310441c0000c1350b580c2d82400c0060301d400e0b0905200c0020064950003c0d0080001c0e0240010f010419480c40c1c40703202402818500355031140b004640301c0d004e00d418907030103511424003800a40345002c099607102803140b0382182480505072002e0703e0100b1502120f1490741108900d207002400a008070740c040d03c0900001d100701110400418140d200080000c2c803000d5441d80d108074468402c0d008903005081d040301c24400000d83c001001c000c0e500980341e0900c50240403000d0b072444445113840d05030380c50094029041645998441114903607449003100d650340074401d00840140d40d20740c0903060644085000052071070103103000624090060300500b048025a504200124011798112456a07042030f040203107815004029080d4408440e00944980038040204a014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 543848785 1250 543847535 543847537
    0x50c0402070b150a080304271803170c18280e241c0f08030f0901050114240f070b0c0309150603030c0709320a1d0d0302 53
    0x5801003010b500314000320703d420451520b07103e11030340030a500103120801c01440c0102600390641c11110075010481c10350601c2104441ca41d0741e0411511700b11000d4082031541c4100700c640c600c0f101030000c0a0908004608092078046c0c1000701d68202c940c1c004902140d2900380c2080300b410803071000d02e803131020644642c0d00d00030b000b4040d449074403600c2d00000e422082c28403030300104030a000d0641d0000c10042c0080c084484100c0011400003040501c5030b04c00100c04600e084c000600402007191a07080c41900100c4100c000f41402c80b1a03030610006200b40d030315480d10304820842c02c8401d000c5e1101240f169141101b80c8070340d15803640700c0200b4503120030721401c4000e000b490300c16804070301d056440100700700040c0400e45050550740d001c50a80b08000220b0000343c0e410480090450b41450494085c843c0303000e555800580c05245c48624a00c032450a6034644580c165148811703125802501c0c03148020a4030051022050680381c0c1103c690078024074419aaa986a82040e40d0f8000400030020f40a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 543850035 1250 543848785 543848791
    0xb0a0c0510021902010b090112050f03040612050601260a06051f0201062c0a0603081b01051003020d170708070506040b0c0405060d091110021b0a0b040e04050c0402070b 74
    0x40340b01002880b03c2561040c0314402510300014a210110790a094a500780b01c06200011900c91144842a0412440400241001302020b50f902c4142007c1280c080b4142d034070140c9140d040c005a900203a000811507001601000c001d888509443d81d10206540302400351540810703004964000c11503a0f03e00001c884880c0c06009030000c0c000c0130754403100c1c00c03c010602114091800750000810003182400304030715400c00d40340b4002080311502c90311107800d00c2d8081c6241044a0344207101503030b030303d84003801034a03032200c20200350b41c2540c1e1a58000c5420000c0051004080d403098200c3d4240c85c4070f0b09400c2d592007980000c04107440340c28500d40280e54480544d010348441400741c2c0041c10300101e06003128252200500800d041c038160100f514068200c01c5800c407021450084d0000d00c9850700805200410300580c010020f00c24100c060140309103140040d40d010303400392030741841b00203c482c0851301107aa000c400444141d40714100141081200d03130b0040c1d440740c0005070340400d1007054021a40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 543851285 1250 543850035 543850057
    0x10020703060e030316140403020406090906060b040b162105070302010e030301050d02040b0406032916230705060c1b010b100e0d080406170a0c08010b0a0c051002 71
    0x20070340e14038403081982d078003088450040400c2d4503502a501c640c442d40d500e2041b00c841103003190406031668002400da69245e01f112104595402c02c1c030040c4801400742c000208a029100c910f840d0a25000c40603038884c1c0403c1d108034803880c4141c0810880102107003030101c01c9945481504092607000144140d018040c20341c019800c2c02401c80d075040f0084101c82c1202d03001030048003814100c3e400d21014140108205610942d520800000f00d6420004072400e99501600011a81d00908141680d0754003e002529005d104801c0380e041c0c1d98000b912004518103124031000000c1c800d41001c60580b091810040c158001d250500c184154400050000308001d42007503411600c1c0b1100f03940c2245d80d4620020741c0321000c40b250307460440c014114142e4401e005000f2840c41c01051302c4414043d4000d50201001680e03c4485409159440700f100c0e0308503080500038056180c40e07400c01400b241043c00307030800c40d2000080e404000c42c002d403450112660300109860200c091201440f000b13401c0a44680 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 543852535 1250 543851285 543851291
    0x10e0604151109043b0d03090c05060c0703050a06020912030c0a060509030438070b0705090f0d06090b1008030d0c091a04091802030a0f111002070306 66
    0x809140c9a00540b100c0740c1c94105010300349011401044003421882c400c40c9400c11414442c0381000345120301c044440b9141100790340d00207140d00c0402e40b0384100081007004240c6070245500c00510b074841e059044034002c550090321254460b102030700304211a44010040c0c072607500d00f2000c00555402611207120101d440580103401802c4a030340b03e00c5841c09541141e0091112040015000d038440ca41268070801100d0401e030b190348020421400030915511010204001408203502032103d03c8440c030520f100890412410b90f882038011031000d1700600a21a001c901c000460720780780346860555400074a82c4001e901e041c103200000300100001034404034160000101c0080c607000304042202c00500055141900072481d00c0c000b4101d0b40100400c2055103d0000b03007034080c100d1614070b00d82920784015540d51034000d4440450342c9840c1c590007060030320703c002c0d00503030b8012a9a1044070b03001207142e0076a603042e14011000d6810000304a41c8a10640c2d00d5402c2290b000401c6820f50388aa4020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 543853785 1250 543852535 543852563
    0x30304080c0c0a141809030306010305070201060b0409020301080f01020f07030f021005010e0612060717190203070f0e18060112090203070b0a08180a03050a030908030a0c1706060904020c0f010e0604 87
    0xd6481c0805c00c403100b104a84c030030004207125510a900440d40002d40d880001966130700c0d42030108955200d9808244560780100060017008020301c40102c900c1c4250000310325018030307030b04808a94001e00c08060148462101440d00e050b00900201030b0300050603004000720368482094200415054403894000d003041c646c47d4042c0780c80055043d000c2c1d11030343c5501e0104510102402e025020042001c04031860f41000440d9172031241c00954081c03400d50f141c05512443c114401030001041c10040c40c81a21510002501980b051b00c07840d410450a10300400e2802d03188910001810504e20300039018854504001210329846000e04503000140d6071b4605641c544034080c1c681e80f0380c04500b20310341ea04008111710002c2e000742d00411866089090118600c161902c400206d078004641c0c03001c3c019102c00401010b00c0d8824040f000c00a1600c1d1b1102460030280080f403024028101003078000ea41c0040ca030802c0000800c84410310389240e400074444620f9201c00765484a2302034808a60b00c01c07841e840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 543855035 1250 543853785 543853819
    0x40c080609070302010e120c030a1101080c09060415110703030305100b121302120f1b0118090e0a06061e0f1a0a090341030304080c0c0a14 61
    0x441d904484c0c050351283e459841d01c1040000215110010348018440e40702e10150360b032800e00c401610030340654a078010302c00c000c01c0054840c08008060080f0b0050820013040207070303582001d0f1001d8802d6011015204074410f001a10070800c1001d82508500c6415000410168543c01070751044590a07091481966103a1410b24140907441c15100207110290015040b42000c0e07001c17071031240c00104903400182082c600c803400d044690b05a03140703d41000c4902c0c00d03040c1d0103080c1006c41c130400b0719110741d120721b0481c08000304000030b004a60046840d68401c0490510421510a516410035010072042d60340b910303030129681d43d04081d060300e01407840300003a08a60386100f0700202c1d0001802160800511004016a5848500080c060200c103080c04804155407501d02e080d9500341407400a00620f8584000d0b085006c008011003a580b1751302d6a80b10000e102100b52600706600c82041601c41c001d0021a85c2000414402c542c2c02400000001500e41001846010082000e4034080e0034200c8000d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 543856285 1250 543855035 543855043
    0xd0e010912020418080d02043002041508240c040e040f030c0b04060e0f03090a06050c01020f0c0601030c06050a080c0d090803070302070309080106050a15030605030105040c080609 79
    0x8038070160511152111805403c0130b40102c82d0000300c41001070340401d00d82d078440585401528000721000d81c041030602100003102543c5114950140801040381042e000d5084550240e4a000340216115000480303c004071625880c003504094050701d901132040c05035001d04134140210126541201008102107240b448100e409031403240081300002e80c1d441c0c940e40b4000e0010801101042030b50300640380404c040c884100d0188c0d21480380031403c8000901c1c1d20f80703000041000140c0603042045403405c6c47d641c440c915401ca4510741081515040341440c101d00900075940441910100003e900c01079110104006046c1ca01c2024a045032030b0b1592012205405151080c401051254011820161003000940714035000880080703500c00c2c039540c3d80e0310113410540c0c031712010a4000c41c1c2c000806402451080180c1070010003000b01600d40000184201002d01c6000300c00c10b440c10380b400c181ca10035007113840a0300000c1c0c02840241024a01004484141d1249003141d0103400e000c03502d5210080307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 543857535 1250 543856285 543856289
    0x121008031219060e04050c09090d1b2102100e0303150d1202032113020409080d050405060106030606020114010b160204111210030f0f020a0806090d0e0109 68
    0x280218280306180c92440039039200580448103501d0303802c00806895034180100780c00341906001d002c0760760034280760891a040031204401d104a0418081091070800000c00003100c06585c0b4000000d40d50030780d4141c110303041c0312a019104444e4404a40047c8240c900b080020403850b908489002102d0500b1500321201000c00b8216030b0010000b01c0d452181d0542101c1005000500c4060325010581e1901c04051108c0c4000b0096000881d007201846202030004094070700111110305145403201d000355160300c54100003071189650304407207405c0c401c1c80b0003a90010b0458802c20030050a250420030782d40d45007407041700002401c01d4800301d05c10740f042c01050300704410404802101e9003800c0105000350020442e25403a28643c031042400340e602e03401000758420021b030900707940d109205022030008000428102c03a0201c1d24208000150000c1060728002c3c0e0854003011000e09540b00203020400d01c0c1c2d010940522440040c04529540030800b104000b46039181d00d08000c04140c01514111124 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 543858785 1250 543857535 543857549
    0x70e0114070219090507090609080c010206061309021201020903120711010e03120d1e060806010927050606040507080108030406080c04050a060f03050604090b16020a06050a021210 79
    0x3400150014104602507200b0303c150004040810b60f22400060200e681c12105100040c0e401c20302005400e400c2028880540380b10380103070806001510006c0d60341c55000e0440c9005410300358200c4942c04613a0b20400e021b590003000c0b00055440c0340300c618084c2d08900c080304d11030300900d0308107880c80e40301e0303800c48807942d500c014076012500c801c0005417024008911816014000e040800c8010301d5104010058007504150004049400740150901400d15032084034500b41340070300500005000052090450301210f0b0003007240085008030060351481e9200d542c1040e50b0b204000b41c10410042801803281a0580e8100300b150788182040310310503800e2169034255041000107002e024815810994071000b1090094507207a6135002140c6c40d041d181e8000000a40c0c02100c9a00160b0315008241c2c00c039408823030600c483c0004c0e4844041450b800381181000c2c9040d002414843d038000e203c40b13240a44c10880421140c64100b6091000c5d52005250405005400000902c01c0351940b003154103444203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 543860035 1250 543858785 543858787
    0x150e0402040b040e010501290c060c160804061d0d0c1401020c030a0305040e07020127030c0512041e080607050702120609010f0b0d050d1407021503070e0114 69
    0x25502840010700c0e4034107629400030340f192800c0a02c00000d0145a008007611009a01043c40d0155242c100d01e0340b402da0400c83c11410000d44d920310303130009030b4240c20040c540741700e42d03030b4545054501e08219505e1500800210b00800d0003e034030703070700801030040841d00900c510240070f039010204201c040c03c1610040a282400505121070b074031001c2000c6040704180121241549881c0c0003914104001d1002c03400294002400c0c84200c1510842130b401a201c0d0000303201280c048928081041038000445410594180304002414892030f403800550340c014054030380116004150125a034014060300e60f0b8011122000c03007060800c0021403048501b104054041ea4940313a100310745a903c07aa8082c0e0788140c1401240e150342e138046c40001d000780400d900000da0504907508500941f11000600c03031041c0035075881c00000c0380c40418280f405050928042100d9504406102042c0c011100080d42200c001007800340e51640c0702e00118022035041e10345a1050502500443c1c0d0014480c01d8640380e014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 543861285 1250 543860035 543860041
    0x903020a03030b0a0906090c020c1206010b03041a07030504060b10020316020303120108010f0f05010e13151802180118020702150304050303040303063f080705030409150e 75
    0x21080d40b001e075420800403c005202d6179543c1d0820203a03002a0001240d0315a282d48200c0d8158042000362041e0000303440715022812544c800701e40340c5005100300c4a9100c000800142041105041500d290910065031050360502060040c010001120201e42203460500314400b146018070b10200d00603603941c02586000609490381d11090503c8100700d82601c000c0c0604254807450f089800d02900241b0000100c0120428444094500c11001903100078584001841958030400b0200c0d8001c0740315052094090b4181f406203580400c041907003074554034048200c42409880002821054021114106900e0189a80f50035601d402e1103454502c0c8142d441d40800128113401410196000030000c401c0840c402c20310340b1296008a030300b26042c0d000001040304054051144102501c5141c480c0f8200070110300c110044820700c0050381070346006081e03030751101c0c010003407056054940c05066151208514a8003d66a41090240d00d80d16824050a600114080e02c00d40c02158a18800307400591 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 543862535 1250 543861285 543861287
    0x806060c030d0e031219051003150e0c0405070923090106110f03070f1e0215092202070b0f0c09060f070f140c090f01030b0c0d090302060f0702010903020a03 69
    0x102503c2c42c41c0c1c0c5940024441503c00d04070004a6511846400c00e05203100340d055200b01c01191002040413002c0089104188040340305105814800c0325182000a550100c4000440c94000746551170f5900038200400c00000942c80f0031510308440440d1000000100711200e4584009043e40c1c030550407212050040148500c980b50007201c11a0403001c0d20024035500850b00d0955001240543c1c903400748034400000c100c90000d00c414078804038030f6161301503050f0750300141d4403803940680f8000340a0040f40c96102a92901c42800364440d88a6147c1e82802851070034401030b40202c001958030345c8034000000c2d204900c0124151181090030380d1035141c0a041c008004451300540358040300314109205840024a0280314185024050000d01c2c404c200a411254030b051a0316a58070701506400c011300464082844026040d60390103d5124116501e036000c0317161902440d90414102130419070f9420a158000c10360a00603081d03800304903069620b00f8001da007602c0940780000c005900400001c0046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 543863785 1250 543862535 543862541
    0x308041e0528090c020a0c0e07120e01020408061f0e22080405120115090b0105030f1302030a0809101e03050c0d090302030909010504060506030703020a0e0607060b010806060c030d 79
    0xd10b58040c8180001600d8140d08000c90310000301c60070159001400640920010000c040000e181c80324203a1100e14103280f004164440000700501311079140c02c0c1496258000f90180c4002e014180110b079014600b01510442204105500584030040d0502c04612500a07000045c891346143c1440402c0e50040300303021030340010581040e43c02000c24800845c1c10381c1d030b960f0200d982c20b0300c03c8004280540620700540403511183d1065810786d25141c07030080c40e66046401d882e40990868819212a900c50440421541507060f00035818000c40c034440080000ea070003d450016825600c1940c1202c4400096a00048840740c0401d8401e2041969480a1082d086607500003081540c0e5800c094003609c4a0058504940003140507030004607184035035043c4607219500506013200c0078407046250001051440c4000303800c0d54201074001074410301c91401041d84101c0d000f0090b2107540d40c1c54403030400f03100030036203207900c41d00040002000c0f03480c9150540a80e11001c0e001d81c050751a10304204514001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 543865035 1250 543863785 543863839
    0xa1a16020a1b030b0c07050d021b1903060606090f0603050112020d060608030a11060a0203010f0b0f070c150318030504260106030b09060c04030c0504050a0e01060308041e05 76
    0x420b000d100c07000300c0041c040f00f0286014051403080b81d82c4415280c5003103402e001c104006001154811030320b47c0100400d4186a4920301c1041d101d0b0500140030140ca09100f40c00c540016100c6810070800140307050744841e003c02100c90b40045d52190540700c403401c40546800b8441e494480030307491100405454980c0441032400d02c136920002c0d4141d980c484280c1141c004000002c0401c10744c0710920540d01003031003072503840001c00000b1455907060940300c082140c0d840c000d413004201e0101e05401424000000c517070307056412081d0500074a9507440c560780e594180d12401000642000c0380e41100c3c1c4c0e01e4070802303100d441d4142c0314141050308022041d0030340c07031720f402c1c0345c09400c11011303081c509880080c45144081d60144211800c0b85c641260102c0c40d0800142c51025825401c00c400c0011540384a410026604203c03404502a114284500d01802880610084551803c0c400004202c0102c0041c41101c1d807864042d101da036507010031103d4601c1c1901c0303030740d40028103400e50b0002c4036003c1c95142c031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 543866285 1250 543865035 543865073
    0x405031c0906032c0d1205100303031d070b040f06030515040e070e16030b240901210b0114070b01030b06031606080f06090903090f030f0a1a16020a 65
    0xb4400c0c03403c1c0e20305030008135402010640d8001d40e4490256513840742d84003084001448080c055414002501607925060b80b20103010199590043c1700500098100d018101e00d0700001c41d503005407194a9001564082c0c480c0300075000305c07200005202d0b4028051035100d11380020401c16481b401e4402d03c00a840780c01410740140c050314034040392a151014006020320b41000720344180541140000e4226480b42c2e0b52184200a90b0ba001000c40d01c00d010b028041003000e080044d02c4105450050360101180349060400c2e4181000c040c4114009500500c0400c401f60303900c02c1000c0c2e0118403030049124040000d01066004001071010604001006400844c0642121884034060030003900781d4002e41c100b000058020000d100d00701c0115102c3c503800501c11282c021050610700090343d5a48140c0315542d0081203c101c60002954050104841d10030041e000d603614100c1914080101072000110300d0300c210b540d0000308145011611000c0c80700c0325036400504004100b5200c0500b40c6d018055002c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 543867535 1250 543866285 543866321
    0x3050130081309090c051813110604080609210a0503150409150506040b011209050a15020c01060b0f091c02310b1c0c0b040b0405031c090603 62
    0x10350342c0d1541c1d4401c0d80043c0320700704001601e02c14900d4030460240e0180c1c419032051264280e0980b0075040d18a038160400000030121a072510741c0c0c68407000d821000e0003843c0e070100d07010030300082529010612a200d0b04200c000c0e20610840641a669040c02100040011410078071404000038080c000139500003902c84170b441c0085400384001002e0303c1c46283c00b1a960303c0341c801c0c0c8004800c51401825005107048038240103ea40c05000203090710b01420829203402d0b110f441134001c0c003078144403450003207070000700001c4421103456510005e907107c2d42118030b01c1d620b45413000400f032242c5410f451700e1000b09090646020b0b50641042401540440100740c5130a41100000045c0e40780912821190741d00343d1103131035800c09038202d03490110b040700901c040b00d41444805080d950b00da00c414104040180c0c6903202003a41818021030807001500040220400001c0200d80300b40407a01070402c850046044070b0317694a5110181c45006c0d154810100401c84510051100310300a40080b92407901c003417445 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 543868785 1250 543867535 543867547
    0x60806060708040e010602010c021018110f09040501060501091205030d110417071508060310050703090602120105031c09060806040b1905130e06010314070f03050d0305013008 77
    0x30421309902a404640548e65450000078002e8043c4040c03c2c605101040c20040d5440010483c2080203686030014007168861a00c0ca2066075400c40c6ca0040b10700180c1162140e1400d0314101d80204828081c0501281c2000740c001042940030160b46800c65100000d0340c00e114a4000c2680078103810f00b00001c41d440c061101045061070809884400c4034044010455145040000c60010040d1040c40003000886001c220450302d0004040404a402030340000f030a5580c840304030300400c00301c640107100d680000307407080c0c202c0c00c0c841026060310011000d4880b00065255101007140c8021200d01c00301d20021000c01c02540210803261340408003400114118100c1800901110b00d02101c2114034880490103010301d04201400340d4051381508802c001b220114a15196946014840208850811805043c00360401c7c081314005151a20309442c400d0b4903860031984842000845c03000082c602000004d120551041c3c500040c81915010300740000d40c0503181d004414826419a2201010090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 543870035 1250 543868785 543868799
    0x207030903140a05120d06032a050a12030804051e01061502190b0709090207031d100e0d0204060503070e1f030f0b0a14090a110a05060f0714070303030509150106080606070804 77
    0x802c0c050002000e007034800b0615410b90099646c0903400143c020742c01d141c000e002002e03033058a6044141c060508007299a10361030078501d485611074a200d8060f8850080c03c4413040b05400c1032042d52400c02d80204519008007081742d503086110402031688021107280350108001060044e00084540b43c0300746000d488103020b2050f6401100b0840c0090040c0e03556194141c0051041103c654089502033000074421000034247c0c060000480c0c459a0340200c01300031941c41e5071081380184009826030780c072560b48080403d554841102c1364410500c51040d80607500c0072100950342543e078486031002040c007513501d4440040e00000e009040099032030311460780740b10700c0c800328a1160f2452070040007504906c2c54032005d000301400c100c6000b01c24210090280d59261016962601d14141070b6131f85610540c101040c0c0d111400151032641e0050440100c00d0503895040f2301d00c59010901158050480c20000c00c1844800744111000180f0304400302d01c15280410041540310301400c01c003403c05444004c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 543871285 1250 543870035 543870053
    0x1203070e131815150602100b04020d09060506030706090b1207030e061501090f0311040b03100509010212060d020a0302040b13320708070f11010207030903140a05120d0603 75
    0x206030703188076400307a0001195050b801280440016032015907640340c80c008011f9902c00191362114046a2640a13038405601c0d15411340b5101001e500b03003030080c1080c0e820a00300608081d03031700c1e034002c2c001c0d1500810010700600300c440885410148003450308a01403203000241c04090808401c1580302e1070308122800007004045d00908040a081c14940a408000340880000d80d21030749901b142a0b0301040450041c5012900784a4140d6001c10740d42c2e4030b4800031303041402d10102d04244034909014403032400ca055002d000400c941706000000f07034407090f041040c140b8014034000d6101788100001e00040c201900301000b1402c0150044c141c03c0702c1e40c00d201d02130ba89444001d03108040c881c2814022420181803442190020030151106410030090040000600030105000d20810303000c4a15014410f03040c1601c0344004000031501e0756154070380141000228813007a00c2c4060164840e41c0c0504001c650007400c0e0358004c00030900c88030821507444044e00900305841a10f95195000004604014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 543872535 1250 543871285 543871331
    0x20105030727062303040f03090e0f0a23060f0a05060f0c010b101709100c030506130e070311030f070b0d0510050108040204090c15111203070e13 64
    0x400c10b005414240500103003c81030040702e01e0207442442d84480e80c0c00001000310382d0415000060001c6040c1181405d80f60201a684242126101c2008210240014880c4140907080c2100140302c9684005000025108540a80451082443c1c0880c0d41c2e032800c2000060403a0000d0070b80d100440e41c900000b0382e103800929000d03503022400070305022104420320a1040901e01190300340310754041590b006000000038070b41620407140e980049442141d04020300c030b02444080506200e580c0a9002c0103015010a81d48140141111050009480080d008110180f48810010501c0e21701e90740703c00d0141085030880329014020408440900b00007400f001d409072071020703502d540e00d01c45080400c045420060400c0307c0009010700510031a82e000002c1038000e41c0480300420707512028204010b038903c0590002c450307281440a0035480301d0b00000140c50440481c2305070b9080c10b211660840e050302c403c5070300b1000280700041604140c6044e0a0030341407401180700000d00a10b10a001c055031100e0303a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 543873785 1250 543872535 543872597
    0x108010f091814150604061401081e1608070f14071a090610090203091209120a030f030c050310090e07150507060b060a020a0209072f0f06130201050307 67
    0x9206401300510300d030807000350005400e40d02001003500d01691604a0030000c0c1c1414100614480441d0032240c0988000000981134110103900b810041da03100590701001440e0404a00c3c0b02e8002000300380205030806080b4032070b4070391640c1e034040104040749507440700008035098004c07031031072084c1c01444000c1e071480b83d46c075440200300070305040850300d4812031241e0021000e6401041002006513002c03600d1030021902d0358000d502c807002d0800240034048028581d00162181442c0807080c164008042000320f01c0c41e40f0200304000c0c0d40311080301e01344012258026201816881045401c4060b880a14032040c1c441c00c0c3c8840310344a081828914686110201c0002c6011902d601070120a04c100d042a0108031000d500d0104901801fa4036440c854030040e04c92a2168005a501e0380190489040c20a070041c41c02d85120440c84032281c0414590402581c1344552007030105442400541203010b003620b0203c0c40000801c0b6401102c166000401e07000803c040710401941003901400700941c18151 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 543875035 1250 543873785 543873793
    0x8130c08060711030708090f010908060f18010b0a031e05070f060215010602060f0907080d02100605090403082e0311011e0c200907021b0108010f091814 67
    0x2c1500c0c02010402c021508a42c2504104000000903400c0012030740c12403019110707400140d8584005032052580c0750311000840c0982410813888006d00161301e4071070801c900d0f40308011540c40c04680c0c02c03280165450341d000080e129040c0f005c20400455080d080b01c112400100f640b015589050804445900407450701001280038410300d5018021210030711609407118005600d8400c00960322400a01901011041040810203000c014051840a40400f81c202c0d90701554018000350340b0034803007542c00e8016203800f00100f010b00d400c00c0064081c6415070346042c11074542c585200b96822002d407200310784600403142c140c2140d02002e100700046001d5000d00a1100315140003620b060b2035440c1d0a4950b83d08503495040c1c641d00400c440000c5030f00700c409860030900103585c400c0d16402c1040444d900032107400801030ba4547c0011142c0781c2400e803001d0701c206020048019a0300000038040c0c0c0c02c10700100582030002c03441d1030f40001d95411140006403d45201d603107038055400b01503148044a80c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 543876285 1250 543875035 543875041
    0x213030320010207080d090f06020a0f1202070b0c0a020f0d0908010c080c27042d0603150b0414010801020408280f0f15060504110a0f08130c0806 64
    0x450807880d075180c614554000c0d0f1410400b03549108080c032411017829031450703868480900f4409151446a80d440d0300400c00c40d55410303065000f901d0020281c120900041c1041c40c0b520301c1c01c15600071780d1525035102c8071503400b03600c0700085850650040800034085102c0c4007541d61458108102180102c2c607562a4041d126041c40340e0701d42501c010306003800500c240d5006002045c540356089925031400c0203030f101d1036803001c1c120310041880200b200c03550140c201405000406440030150309180c0602090105c5000344003000da0503601548005040413099030146000504113810208500200500001d0342c1c0c400400d10400388403080e08851031580d801700d414884420104030742141916410299000074203c0d00c2d03820503140142100070301c0c001881035003004000050142019255000a0f460707080c54030311050304d0060026100742c900c10342c00d000d01036045100c01800c54a01d007000355a43c00019120f1a4151443c0e00098000d010400325aa02003011880503e2000041d00ca940c001c0c2c0030a007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 543877535 1250 543876285 543876317
    0x18060203070c0b1305061501230d140103050d1b150b01030b0307052d0616030201050c030408030a05060a08030a09030c0605090604030b0a0609090f0c230904020402130303 75
    0x400240301c6148141c0030000900030403000102d080e445142190125004181f03180125050008064804001130460a03840004550034001e00901540f8110400014114906080c4c40e6442840080d25a41000030071030011031255807403c64040101043d8004030209a03140c492a40350740104504003540d50500340100d680c5801480290f0358100c0040c05010309207400100004955407680718001c08214044000455a2030040004003000f00541d4850245c046590003807411100708800651074480010540c059240a89000da60071200280c119507d9511002c0280307800785c651503100d42102c000060000342000140081d50a0350fa03400b40507803440c0307411614145580c02c8207060120901405000da11000181d8041760b8110345140545d131580700310030009000c84e402030751846051403004000d105070480201c00701c9100d4082d13009025174890181c04140d484001c1070755100701c0c19030000b00324a0300070043d54101d070000300014589800c843c00415030312041e510482c040b07602c01400740c07200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 543878785 1250 543877535 543877553
    0x40512060406140106090504050406060e070504080d08010608060111010b220518031606140a0222060e0112020f03090706120b030a020d030e0a08010219020a1518060203070c 76
    0x2103d2451110001d50500e80302400e40609405102d0203581e0394000581800b00c81d4004074010114654000708500b02040700401d03692190150b07003054821001042c001601c61024941215915518040c3c1500c600004441640c41409949025034070380f580100207a856068072900a9a104003014907083d417888035200f6242c00401c8807004420343d03040c02468001c04800c503040340c414041c1c0c0d989400348078500900141032542901400480003010403c0c403010990040c040d00d890408001d50402c1d07207100d020b010400c2802030b080002d46801300080d043d4000d40c1c0c132401000c52424054100300c2a03660007803150304101c0c0e09900301c3d44882403c2042c1d940020358003440c001401014062120b0a001003039441d4100c2400902030764120401030705151185110220f40030006200d14851941c40e80124042d40040940080300300072800c80a8103a4000210244210b50220005e0f8401d00c0080e0384e0381c014000c0007096841c0030050b000160001e6030501c000c520401680d21000e000031442e01b41714000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 543880035 1250 543878785 543878801
    0x6080604020901060320030103030c02130c0c0b0702030903010e1506060f0301030818030d2d081b04030807080c0706031806050603010f02070c0806071806050d02040512060406 77
    0x1150098000e0201588415003407074156520f900b00480d5842500514441215822801d406851008000071040660000e014a001e074000c41e186540c0071501c400440894140c582d00c103020640f103105510003c1c1c500703544ea0740e21849c6d5005903410800d09101090030369403c8025241944c022100c1c80c42142140840650420002c1d102c10741404070b0581d24092511060001070861407000c510281043d41d101c00c22603840700301406550400080503409068282c808600c59144040400c980032414080008400c01e00090360710f80d807058444c08900341d4010708405402201920400010011551200c01804180d10420340c4540d5544000c50041c20600c0075000501003600346082d54261048600380c50600d240c00a80004540e12401c0001e80108201000070304941e0001c80c0110038410b5400c1c141040754181c0081d20010b07a2080001c50b100a1100c400300c0c101804070070288049807261001c1d048100303c0560040c5000c0d05c03900040c0340340c0d616503000c0b031050340098204401c014850040c062 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 543881285 1250 543880035 543880049
    0x10221041a13060e0f0a0e0406110c0d1d0d030206011d0606040603020a03060302041109030c0907051603110303151c0b01090c03090803040b0103200a0b07050313170106 74
    0xc10301e042200340c400b0301400341c03080000300301100200302c8003595103121910600138000c2400c1003140d5140c0020444032800c80b01510314030714080c01e55a41d40c030340301c013144c1c0e800d002200984070f8030040304800c2c0c840c0340d06540c031031402a803200c0d0410080d03207036545a01082c41c0646c00820a541c94180c40980134603a0b40542102d0202020501c401a2074900541e0141c82c45801c025858640c10b00040307004051700d50001c2c2d40300b4205002c548509044074014038a03d1010340603221503505e410141f1106940036903d10000640400990540c2c10089824401d064401d14000d001010710303a0445196130010341c2d86a00c208007901c5900c81c6803805880c4a00300ca00044520041c620076920343c1c010401c4c052240e550742c2501c8a0f65054103c0c4641d20184941e9485208961039081070b003040d43e411002400300310b5010400185042d00900c10703500003552008020a400080e41c01c26151036083d400c00309045425100500c40320102c1c1040c003000101074540307008440780310f032803944030035080d50010340c0012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 543882535 1250 543881285 543881287
    0x609010b0a0905091005070306050a09060b030f070c08180a06020a02010906080a06120809040c090305070308070305091002060412030e03030610050919050406170607080402010221041a 81
    0x55250300d60840d08401c0b110388850001d00c41da20050810304200b6044880301e0030302c0c0f03003004002d00385425600120030307100152050b8081640314074081c4e040f03450a028242c5210028000221103103404400a5404026464480700010f565a00ca01da07907013169003800300d00041c03070031211003504203105000000e00d413901c001e1140340d01c141c0020b440c000e00380c016041005162800601c559155422420041801008450100c031450400da2165003100708140d1149052035803086207184115908810340c1e41003000752240600d150f841045aa0100700200d003801001d1140003882d60320700400103c1b4402d607801919640c030f01854010300d81000c0c0c802c01014585070280c61a16030400100390784e80104107481e4010950400c1c1e0041c0d59501031885c0083e0b0160403000390088160140715171404450b13041d82d05001c900c1e01d8007185101240c0341c03200f2108581c8818006130000344248611604a401801911150010058031102401e00e00042a0060344001400c00000741118a5000050755903007081d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 543883785 1250 543882535 543882551
    0x30c030402040c0c022d0a0b0d050c03041205091305040501020c0606041a0f131d0d090e0406050709180209011101060621150e060102160f1e0807090e060901 69
    0x303444010407a0300c0c00400201b04400d0380c40c030280c0c0681ea001c00310001d0080d6400e69450350204c5840d44009143c04241d818072000c11902030150f42501e01540e4041c510640291402c0011503807500b048000313660000720b0020f0200340c2d010754031406010318061000503a5621030381c1d85003442d082000d0040e0740100e00c0c0030101a401d1082910915000a00b1100b03003481c41041c00c00200184181880076002a1070640d09088101b09507013842d01c0e0094074800d031040c00c0361059054a105104c5c2c03240c06440c2300782000280020703205520440e84044e00741000010341d901c95440da001d1240c2494001ba5465000418074055a00300341d107503130140107000081c0102414000002c0880090b840c041b800c5003001014400e04107819007040a00c007070590100b9824540d941e44d103904c0031005803007030b5000d4040c40704014030100700810750030190b4800c943c64061207840d018254102c006410f244c0703800382c1c455090101e414035080c4403004c000d11404034040389102c607201109080200182030800c90740e160484d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 543884892 1107 543883785 543883789
    0x402210403080c0301030804031205070c0806190e07150c0b040606030309092003180a0f06060b0c100b1c051e01180620030c030402040c0c02 62
    0x55101d40d81d110381c150f201652000703010181c1842c01c100001e00201d981980c15115500840c50140c0c584000d41d140d1003450203558000c804190015018031a284410000d0100f0651640900700051030000902d5541d4964501c161400090100c54035041030340151b12403100260410035003485031900e403818200a183c140012004118590004107a0b503000d4864400110743d40c07080b0f9441c1741800420b081031174000820301d001510102950110f40d003018020341240501c07800032411028520f251110546103a90231441d10510f060201c646100320016602c40d40c00e020003400205140480041a02c06480140c0700840c41aa00b03008001c208001407441c1d0030038944c1130020030741c0c5205040c0720700742c4800d041459504585642104042181036103e80d9481940c1820343d103122030881552401034104607811101079202104100c01c1d400d041c0a007404e07403c464a08802180c541d580 = true := by decide +kernel

theorem cover : BRFrame.Cov 543705035 543884892 := by
  have h0 := BRFrame.cov_init 543705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 543705035 ≤ n) (h2 : n < 543884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
