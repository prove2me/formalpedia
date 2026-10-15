-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4504
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:50:20.988007+00:00
-- url     : https://prove2.me/submissions/93cb7297-e43c-4128-b1c7-eb5939832016

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 809892086 ≤ n < 810071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 809893336 1250 809892086 809892107
    0x10091b02010b0f03060415061509080c0a0b030c160b070215010e04120c020f0310020301090e0c09040f03180f030c0611060612030c0615100507050d030506010314090a03 74
    0x50392120f0b12a040300c00000d0700c811004200402018448507410345042c0d4940c4107502500c240c401007980815100000b5100041d6486480621b2044c450303240ea1500b4001910022500540d600b0340c01d50319812102c50301c54008a00009602e007866140031b0118508000040c05060b941e009060341e610106c000350701e10348050f0000b044002c1c01d041400700141295122581d950200c0c40c2116042c5001d20001e00c4801c07480c0010340e0300d80315034035603082c01030320703641c0114102e03040700404108810280700b106445045003030000d0b60042d070300b00c001401303e04180c0b1a105224403d14190302c6402d11404400742a03c500d4004131007209000701d00703208000c481d03c040700c0a07211500b00f00d03840c2e010b64070950380c0d038000040c10b80d0300075641078003064807d10042040e10428024a01584d1152070003801d140401c4030480c164600c181c11030840c070004980108115580c142d0000043c2240410301041503015145c00380c141810140d80305480680301203003a5049028402800103890300452904005101030f222 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 809894586 1250 809893336 809893339
    0x10503040302031801050c0105071106070c08030c03041b18110c34080f0c01140307081513090c06080105030304060c23030a03051e040b10091b02010b 66
    0x42040c0300c0426000410344076040d42c01d07002d110114400c3ca004890038060752040240c3c960800c424000141e81104001590104060480301217540d40700c0200c0342e01c6442d817800340c8444c0c81000454042d1680500a59000340a43d0190551000d030302500511195651b0050705400351036a64015000c1842c00761407005903403001d109080040707540005464030b00100c0402c40341d074407504101d90110b072035030400c26107040740009207180c01d0340e1680e03001d441d00c03041c00010010703010701003058040e0f6019501c0b403000c1c0385121400741e0542d5940442a42c210101606400d8000303c1202d0898465540a407205808040210049554016417919001c004c072240c0003101030060003001032020b5240001910101d07542840d040c0300841c00303410300448031204208440e00c08001c001e02000082c0001006201e4a91240c0d020449595498146c049500d40c00141d00f80361108a400328002c1200c15402940083d0880c803242c0c440340c1c1e60540c00b4101d03007840501c22003a1044913a0a01c59503028031560b00302040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 809895836 1250 809894586 809894597
    0x8130221101407030509011b09050901090c050301230603130209090604030f0f030b0a0e010e07020f030904020702010201020d1a030714030c010323040312050109090f0b0c0d060f1401 80
    0x50b980c101900720a4001d11510400d90390b0700025040d030000b50400312034118203e806202c1d0f00c40101c0c004006441e140030702c034000e6000d44d0001400c20460710230061305c0c6d03005070313030b1982180d00f004940c603e02d24100d0001c03c40c00c462908240b10540d240e000441c01401104145161000140f05200074560014131200c2107070400c10405c404a6005220308000c3c07a8031b80b4180420401d0754030b054009000b22002c80d03070004c41070440450040da0790141d03a4140d40e05803100301c89584d01c1f8101281c0d0380c0705000b100030054005000e882c03a5418030750064001c1606c1400098107150041548804440901c40521038000c9006601c40c803d041c248004c0000d0070301c030100d6030881d20915000c030750398a4403802c03143c0c10141d40e02180415404031460740103410300400c01300c2c00d140c146401c00501c207007046000e2401e035034a00000010122003e218203421180e1002040d4107402282d00c81c90391940c4020007041840c1820009202c1c070868030710500002e0814428405600c81c14050361610b008441c01241c0c3c103202 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 809897086 1250 809895836 809895851
    0x2121306120c0921050102030c0304171303081b0d02010504060f0207111e0907050a02070e040302190303150305030d0b0f132c010e06060f060a0813022110 68
    0x83d4044000c00954000e1480400c00004002c0c074660702d9120f1a00240480d4400700c103002007041d88000540c0102e018500401c6110240b802c004203a214114080b0810800b41004000140e80750000c0c0c181820092101c0d04682c9002094500b440c070035402140c0140d5481081001f04180d03441811020010030038110f0808465aa0b00c2d1808600085a588505403c114101d00d8a10b0620017140f07440307001c0e1200034a4240070350041e016421002c003220141c0968031000c6452402010202e10442d0140d00410142078035603d00c1c0b038209025442502056218592100508800c4000c5002148500015a030711036200b80c540040750350802c4c58501c6003240c411901415a101000d920402c1c0d84c10000160441ca002089984142540340052002c000706000c04c04040042d4004801c44c0c01c00e405403440c03030307403244100251031400f802000e03400078060205c5080d051203040d000c2d0303104000411184100b00903400080d604107039604610105c40c0d12954001d03e4030414807620f040303c10085001e01019 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 809898336 1250 809897086 809897111
    0x203160507110a080d03140c0703050714010c0f02120301062106180504060c0e090c1b0a050604031803021e040906111306080f06010c030212130612 65
    0x141100400030090041081030034041100e90191400354010100414184e681d82002d40300d0400a035000f01081c40c1040038034012001502481c810303440d40f940145058810f0741e0039141508070004c00c1c1c9900c071005038040e501c003000340308100008035076850300d6448240c1c44100900d4420441041d070007190003840100441c4d50009131500a80094007040b01601d1240030b041c000500c080d0740803110540002d180f11541c0c2445a0005008a004200134803103590000001c0d2000c640c140c80031a0031031500030010364440c1c0803401070003c1c4403242c0003115034610503980c407600d00700c031800e000ea8145c1c0010082c40101074114800703d805100c44500740d0a00c80c60b5800162124000c0c52112900d03a00c0402c0c4016941d0359130707000140c007940c4040d00300b100348036980011400381c002e010080d2081090440108a0900581c4c015101d4903648040c0d489550f00c40004403414203c903002101580b25040e01c982c00d41c030203040a00035400448004005413864440020700380c3e604480031035102032410111031800c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 809899586 1250 809898336 809898361
    0x2b0b0a0e18100c030204060905031b13060e010b0c0c150409020307110f07150c080306190302100c030314160806060c0f070515040503070e1e04051f0203 67
    0x1905165945070040c034211503a04000c146408190301e2458000c1c0e5040b8960507074060f100781c3d00303266903001394a0b444109150343d4400c0e80302d0841c410340020303030a00100d180440c405451810510800324038260b40d05c03c50440c180d8281c2101a61220101d040c80031070008000039408602c080f100f01c6080c60310310080f106c4520850007225855900000003d0180707000703c00c2c29141048040440d21020903e061740341c2c0320301e0365000301c00c50310141501e0580142d124007a050039698004900e10b2640d280c0300c0c10810203551034400c4d4010001c1c95200080940c0d2441211030b515083d54440006105413803800408459213841c91040484580b004e011155000e421901452903041c20403041584070100003c031280100d01c180001c51248a020030716440c0040342c0d20007128004e4407805250524503581180d40c0c003850258540560014404100f00d0000e8050f554016002205d4914070484448081d07408010450302901c082e40011460007200034062049030100703507401401c508509000c0c804252 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 809900836 1250 809899586 809899591
    0x821010e0c130b07080405210f030f2a01050f0f0c03010e040f031106010801090c050d030f0807090302151206010f0807030c02030c0a0c0f06091413022b0b0a0e 70
    0xc100310201310034041120038412540501801070080080c0100c0012000442e8000d030b2510b00e990260300d40c00516000004181d035540103103420030504050503480348a41c06950071145403041c0030501c520030b944030000e1003014005c407129903800c1d405180c400642c522400c0091710103041386004000410103032190f001c5442d0041d13808002d400c0d03510308a050494103c4e800c405243d45a0003601c0000819120540c072054078a44034019007001543d43d007040000f0003800140c003038003080f603092112000358400c2c0b155507803000d00ca003801c0c03543e65280c1c2c01080140361001c50707141d440710300000e00756400320f14951015800722091070499440030780d4502c000e01d401c8003d410001419110001862080c8c024010b0b1290081440100d8152010340d0803c42031201440c400c1e07039858509464086251031082680b117080e01c640340040441d50711044207207e40ca80b694500580b400740d00780505068000ba404603d585a000c8200180f044d0720085020030885030800300041c400c8041c0f002c03c00c00085019056039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 809902086 1250 809900836 809900849
    0x30421090504020d090b0106020f21030402012a0302030403060b0405070c0b0910090506040201030b0d0b150a050d1b0b0922090c091b0305011d040821010e0c13 70
    0x42e100d4a40004c0c03000509040c41d40180950300550003c0781c900e80c0000c028241010510444413491280021651a446c40701e600c46184602080054003650140ca40090b080460480013180013035a110040710f007007225a01100140c000040070818403296000d6402549806c860402c00303814000005002c1c101a858010450000710001820680c801d201320960040da101081c030000215240086d22190704442c00c0340440e1038403e112000c1e08001c902d044080ea40706a5441603526400030131000e407607141e2403503a840307040c0120105068031944181d1621034440c00b021a680041c406000c003100d071168010011084007840013078450307902e03994038041155890b9186040c60f0306401c0000c4c0a803c0c03200c00500b641400c1c42c03000172007a40311b13803025601030360a9080d40890115840201c064031800c3c418001100000c408030500c0020305803030142c005224400c002d02d080e40c00c0030243c1064030015110001880d44400401c00122079920003580010044850340ca0a092414a024000c0f064082d41c5c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 809903336 1250 809902086 809902091
    0x3071527061e05180f030d0e0a1a1504110906030903071b0303020105011a12090c0a18061e0317040b04090509150709150212040605030421090504 64
    0x3401400010352100441c0b10204804050b03010310722491201505040d2815448078003000e1103201422008200a480410707410041c6182540d00120345000d002d400700440c48500a0741c1107000003c044040a0002071850140303c1042d19140d00900800c1d0181144240201c0c1040b0810100c4010740c012102040000c4402d60384075102c1e001103505d50b0144040c01844070040d00300410100080d01c40010171640719900900403aa03c510b120028413210148180c41800107101d078847e00040710091660210300302e0111039445943c1c82c001500142c4070350180c4110b113000d40300485000018040d04d070203000b489441f8514441085001c9044a915110190020200c0f0b2446038203140000308890090140446494440c0e4aa500403c01001c041d515000c0600c502d074801924130b21076241d0a84507065a40301d02c40181d1401c3d00054078041c6803c042c504600a45a04806c8001d1540103800034001036030345d1644a140611301186d1015400740c907904100d181c282c0d00c01c86907a000c040c54040d52011b4401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 809904586 1250 809903336 809903411
    0x105041509090504050f0d09030305030a02090d0501090b0a11040f14012615221e0203151008311e0c050a05061623030715 54
    0xc4825040c15000b08801c542081c0c140f1051003800900007410000e141c050b144115801d820980e981c8403180300c02400300b142800012042c442d9507005e40440940034019100030000741c1c1c0c0b00340c2182c41c08601154104034400510400c0000c51103422840c4200c3c0b001c05203040c1c10a0f03400909561940300d01041c17030030740e10484010713079204680d0189228001001d07031180d01c0d0150003503903103200200e0b85e14402112202024095244c240d088040300544a070820ba041d21001e40281c000e0400c070700d640c2004100300c0c2c9000e255607407988021403250070403108486100001c0c400f001501c59100314000c0411201405120b860006042c00403103090021003076208454001c02400c1103401d408502400743c0902d0702d40944103520400e1410600740c8200b40d040381e101d443d14100611045940201500316009002c818119102c03900305485060141c28504804030502804048500d0500c00440040d0400f017401c200700a518010036600064800b000c0c040d09000c1e894a8115014001301c4590700e03c802c210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 809905836 1250 809904586 809904629
    0xb0607060c020c06161e150b0102280c09020306091303090f03030305090705030d09030b04020d0203070b0409050a02040e070e0d080c03181906051e03150306060102010506010504 78
    0x2104010000c0d00703041d04d48940311808401c0c403102c8001a102d86040c4c0300120352072010042486c000c40d900400307810700c545040f00740c60004e200c81015103055100e041c0707091109503140c0383c02c03c001d05000310801503d4070451408079001d88035507000c00c17400c50040c03051050a660b45904190301a070f86d010b0fa00c07500c98203414104c0d040e0f005a400407401c140310150200a15600d03801152089008008444400d81c3d40d209043d900e0580d004150005a0711107000d0001445580721550481d000601001080c40544c001904045c0c040c2d00c0744c100b03c1d00005040251612a005543c2d1014160700e046040500c4c5c0031010040d42c0000b02007030100f007041c8451807207690341c1c9503034110401d070480c10098071144490103c59881d4405040201100000411a09186071207280b0241c0c0508803183e4004251070305c42d0070713103107900001b02940100c0c00d441e001e90900d2429401840c807a84c0030085100741c0c202c0c110107060070035030090091811a410501000850390f046800c440840e404655800c603190503180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 809907086 1250 809905836 809905843
    0x501030f02060315090c0a0f0903210320130b040e0402090603190506151e011b0807030905040b040b0109140103060503060f160513090c0e030627010b0607060c02 71
    0x1660b542c8140c5e4101403080030491400903000c4c01c0140e4803402c02d4200c030188199408051440020400c41d15400084224940065405500b84003414003040000d040c65134440c50480151000c5c031420707408510207030812a482204070091030039004040c40c4c213062503900b10880c880104007900a04a420106400d03407410845119149a00380d540340d444a80e6142840e150740050703c0103c4101d40090340c0103814600030f5240500414280e840c540b610122800540d40800c813004207003c041b03a00c540d14800724039850020a50745110b44d40d5560203d041c2002c11040329203411000c4c0c0a18a007070014011030b40c221400b10300390f03203000d00b0049901f020140102c014050395040182c15004030002d00c01081c00107804d46000301d210188404804500080c01c813018000c3d44111070f44040c3e101e40402c5000c00541c0300300342d9140030f40b6055031562031035408a0f1500d84190741603e090401140200020b2400003d21907405c0c12460081c00660341030f0000550324064401e024049641d5515074060050080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 809908336 1250 809907086 809907121
    0x181f0b131a0d0216020f01030c02100c020f0615090703060b070b2502070e0a020304170319110904060806060604092c1b01031e0f06081c030f0501030f020603 69
    0x61805566501c690500b0482120a1300c6040f8040c13141c941d004100b540c002c4c02880000941980100b00307440035582060080d03c1d100c80c5180550141342e50481141100f400945d10921804800350006184002480310420f4010001304c10945044010b005211244040340c82c40d03070300306c1c014903031544540304084001000791400344040070148074140300d25070300814603004882d1014090615988c0311000715043c2d100803070300108407184200c4d000c1441c3d484000610381000100e441856401c03900800f4030110b07801030021000b603e00c04600a00d41c1e103050300460f0040c0c028100941254140317040031549038011402104501510b0ba1a00b944041460203003101c0080e0140b01c5691464070b40e030342651112640c031070454000e1051829440b81c1d5005c1e00804141881d440022481c03005039209060081ca20752151484c510b071115000941c0c0342c3e0070440b074107002c282c048802b925420031105c083c040300d0308400115803150500e001040441c401d04202100c5503010384481c1d50380d07a200f50301e900004a44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 809909586 1250 809908336 809908357
    0xa2606130b04030509033405120a08030c0d0f0506210601050d0816030509120d08040f03020a1a0703060e010b030402280315050a09020d02040b181f0b131a 68
    0x4444901706000031240c06040300c100c1080b5010525148d00901c0300b03040c1401803071002a4030500c454800180c0d0f1a00441c1d1243d400007c2d1410180c0c550015020340b4a41401400141c0c3c9a005024071890034660b500c5030074480039000a145000207c403951120414801c861048182012617001d11407900c5c00c07615030703d078240b031030749000800c40c90b01902513040750f440680070720072540e907403050303003c0000b60308501104903100c1215a640b10b5840240c04156004100d0850180849110014900b0041d400000d600b04001d0a250b2402000040448503194488020961900010481600224122508a60180ea0b20b00308142c22420200d4140d2a148140321020070054001040c80a4602a201e45504500b03040c0090f0b00c803d58540300352001054080d5126000140c0e160041c07a1a40c090420f05c0c40140c61a01c0c1c0182e4488220011750040ba00d06a440400204540070802e036926504090050f41c0d004505003003280c100e09108840030b010705041e2411000710741e100340d1200002c1e45c0d0504031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 809910836 1250 809909586 809909623
    0xc0e0904050f01060b0a1b030c1509020f2d010c150509120a08130212100e060f1303050a030605130f0b030303070c110a2606130b0403050903 62
    0x5151401590300c1c2d141d050701c01c2c4a546030200218800c0c400740c0031100c4528141d9100d00741c0c540e2142c841c260581c0110811802d0012140c401c00004580742e20f45016040b0f04100040e400040e801401000410780d041c06110b10309001000019915074810700d90030b2420300f403c4541c0c040300384005a600c01100c46010307041003000715104115640d20b400140c030505285040c1c5a125580c14074010250062440c850042100f01c0001401e0301030a13442e101c0c46e1400200380070680d01c103044415040042c00f5001011440d01da82141080201c10850310f50460480c00d20400e00c0d1610400301b400f0340a82407001000c10000054054450348039030442006080001c180c10802c0c90701041010003000c0000714004242d0030010000380d1440d010042e0f80c410900754450424030005035460726040d61110040315807004400c803001c80c060012441515005002c44131800c0c5440c2420350300c80ca043e600400c110030118010f04101c000414181100350000d0341803c00729183c04010000904142c24524034180140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 809912086 1250 809910836 809910841
    0x204020d0518070801020f040b0a1202040b071b05090f1f17060f0907090e0f0615090112030f05160203121c060b1206060d02040b1305030c0f040c0e09 66
    0x440d1194122582c200c594225000c860340c50b1800c40c01e0740a90204041e0b0004144010000a001000180700800040c40c0c82c1c0c2d203121b002c0e01c0407401c03a00b02d504503011005001c2201e40c100701c141d10110060451400020307110614110006034200c03001803941d41075050017000719894425100000103100040b61403c214180c4900c5841503c07034282c0106025841014007044151641802003401034100e9001380c000941000c2c0900046c0900c84004a028410485003040c4c0b80802e005581c0240303403201a41900c00c0d8458104080340006800000d80401d0a22100780000c1c0c21044854402200e8141719455002242c00748400110085010b50103016030b204807900b1440c140003c0c81c100d11700084600c0c2c1c101070041c1d50f000702c50107806404100c050070040100201d00c60701c40c15030300100c0100542d140c104040030344026600140e022100403c800304000200c24040f58482020300790541c000c105100c0c8920005030755008030044c0358040c90f43c1d40250300c9810700c242c61502a41b00060540c1501d070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 809913336 1250 809912086 809912101
    0x30c010c080f040b0412050f030f090c0a0f1214060708040c0819021e060d06030b0f06060d0506010e06070c0f1e060e0a0302041a030610150c0204020d05 67
    0x9014000c00280011070800000d0200c00c900d80500740165045140702c0260b90703441c0d5440806a4080100c0b000303104d400d00600e90044001d500440c401c03940d400300c2e40c03941d05209000510b844402e201a0707100310740500e802d01c181c070300920100c81150605c0402c441662401c0c01e20000705a11010055a0307405503004011030301d0b0b0002c0344280030301d109807600e440703069860030000d1b114441030060b00b07003101e038411803e000b51408145200f18000000c10004030001031000181c0580d101c2804000202d456000030001c1c484039202c00c6a100c1302028181c2b200385419000a03041d44240940c2c00d100994032401b10711135901c503050000700c00c0d030007a210307581e03412882c240486100f0f29407050503000c80c0c5e458400301d8180380440004000540e0b40c42d040c007900c0d09040d41500c40c1031211a5060700010100e0000000d656030307004224000c203146142803805007903801810705001d00102a51002040c0745d40070455081c0240c1490084440da10700507010f81c10910000c0c01a1042201c9150218180000e000c440c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 809914586 1250 809913336 809913341
    0x60305040212010e0717101803030e2d0a2f0a03020f0d050c090106031d0d0207061209020d050c030d0e0307050f0303070b0103080904060812070f08040305030c01 71
    0x61402200c160b1041d01c10050001d081e90940d84400800c0c3d000b6001c1045804803100070140c1481d0140c064071100c030b0101f040c0e0130440b6010345a001c006040640002e007030542600c0b9483c400c004040107082030091103500600d4406014030b249560301a0f40c4d41d0988a0b10040c45543e04040c0d0108030504c03402c07500c40801584580108102091041710b43c0745207010710381259a05d04403036001d0601507280f0120400c0002d01d400e0150244c42a0041e05e440101559880703902c01c5c06008540c0b40014450b2052072480384000e6182254800382e44071040c1c1064403500010000e04030340c0b0300d140c60703810784204c400c00308042e001510300207410065001800007003000100303081c1c0c2d2000c0c1c26800c54520101007181103e003400b0115005405800a05c020311050501b920309100c80540036080f00e2402c0807942c1c0da00705410b800d038815264010085400300f100e260034000c0701d0041c0118801080402d040c11009885840b481c01d008010112002810080003c03010641d80110742103030a032038072200500c180e00d02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 809915836 1250 809914586 809914591
    0xf08040c12081b0c0f0307050907081f060201021b0a020a0312140c0d0f02071802070807080d0905160503060a0c09242303070c15060303180509091c0309060204060305 73
    0x704d0540c1141141d40e900380016501f0446000509062003521441000d0b507000700042c1540d403940200c22124142034000340d0600c40101015400182d45900c048420b50628100c3c0c4508280c2d500001341c071001594600c04107405036a040580d580030203020341c034143c80e0340b040c00b0400480c0d2500442e03001d00035403000c9004207c0c4030040d201c2c0310510365200822600ca080d5402038070705c0e034503da48000c00181c5455014040c12807040c00301525150b4079843e580400e4010482c19003003d83c56071190000c10009218000e001c44143c0c0301500f51350b040c540000c1d22200002c000401d02aa280c03c1c3e516180e00c80c281c031800400002030401f000c01d2081001e8a80c034208078114001090389100405000e20f07040c01c1c90301c07a0001c0140414290b4891a0b411104450f501c00280c1e4a030322006404031504840d849900c00035440394964580c101200384a0b210811113a90080f8890f400c41310400550050214503140160b500c00c115807014130010f042a00108045400601a50300c04500403c502da0590305c41030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 809917086 1250 809915836 809915839
    0x14131b0e0a0e01080607030908131202030705060a05071419080c120304020105070807021302030c130b070c1205100603111c0c050d02130c020606010f08040c12081b0c 73
    0x150755984801c0c480003800c20a03c28000c50340c3c40301c000194558400d0340500d0701288100702c81c500d0407502546003aa6203880f82c1000703200074504103071402145030402c00390008140544810342171199000d4045c0443c0079003c4040c00e460f0240e442c4a400039801e22808440c000d0403030210b46c241c81c03941401022030300000e002e20158401c0c52200c2e00da0308030b140162840350b54140d64091801c80030781d0301c10360b142e00100d004030780203154203190911070440c074005144640000c42200c5d45851180d44039224081c2c966020040d142010450600072406495240d4142d80710150091071000e15890040d03d010003841401d02103c0c40d00c14040200090141482c140160171100c04804804100c00d00581f0580c020300203064041900d0f0030402810201c1d200440640010040d05010220300350032020b41e1000c1c1040c40040e0031100411125603004030000c25055850b1814015030714065449140d0f07800f40d4041c551440f2040303d011000c00503503804507042d40ca2408546016290700000b000c3c2c5d20f1008086030b9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 809918336 1250 809917086 809917099
    0x81929030f0303040f02102124090e070e0c0d11040e040b01050406060206070c110a05030a0803070906080c09040b040e0118030f050c030910050f07031706040614131b0e 74
    0x1f05c0b84900c600c1480da05030240000c48078081800502d048000c00d851540d00b80c4100030350b12040e8000f42c00888843c02000240804940c0009501e41030f41050b207546c02031031855000c01c0a0201c520710080958205201001c000182d1403800101c9803050702071035008403107007800302040000b04403100302c445040315070944041c13141c651645410390305c8200450b1540c0019580c1918500450154610400c0b54a4098003040d60030381c49001090401d8044041a02d14403000010310842d9a0320038005001004146018401401c05000e011900d01c246400d440c031950703c60703c501c031f2290394560280d000c28140c0c0e0001c02400c00700c0721f6036a01494056030213401080c0001d10080d401401130f01215a4900f130316014518203044501000924100c140c15802004024008102d100711003600402919010b42c460700d4031200071403103452010a005201034011b9080c100e080150620b00440c407148010210350a100441d070104960b0011b0601c0d010081d080c224034440e075509103400c0810501c240605075401d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 809919586 1250 809918336 809918359
    0x110405070309122a06020717070c030f0c1d060f040e0705120a06020a11060105030a0b0a0506040902061b06060a0e0601052206081929030f0303040f02 66
    0x150121980c910740600084920161003001070f1003003000195004d1a045982c603160124528503501c43e0b0311a1049400d168002103403001e22101c003079010b02e850100b42156113400200d6640c1c0c220a286840000c1030708500d612080100400c00d0320303000c054548050380c08240c418416100745104800d40d240f500500055440030141c0c2401d0040c00508a1140000c1a0091509040c4119852210780e862028003642d810140000c03120f000402500e0441e5071030555001c640c8000d03c0c2000c8041c2d121500ca6486100c02c2c000041e944803003541d020410f042c0000303060351500045400b03400c4400340250320500014901080000c00e411100d03401c036491044038241da482d076062101c032221074000e200400c04128000b40380341d8866001480b24a9110003124419120481c10343c1c150040c540218000c40d0301312082100c190708427500308440352490703581484061030000450f280c1c0103200b010030030340113610b100b1410300341c0f0b04105060581c510141100d549241508000110b00340a40040f481903568410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 809920836 1250 809919586 809919601
    0xa08070213050105090c0903150a02070201200a15020c0703030f0f031802060c190b040b0901150510050928050901031101083c091f0b0f030a110405 65
    0x81c150507907101900005c1d2603142c80103031410030340094105680c1846000398000c07100c4c1c01004107e0103280945005a142e12082c40094507001003461840100e1950210300d0903800400a0300c02d20080c0c01440d50714040801800140c064810214000c0292041950000c1050b92040c2217113800c020550b00d100114100302c6089040d1002c80002460800c00c2003280c901503d0b202004003d420031741e0080390941c2c900e403984c00030041c1c0d450001791303404070707103c070411003070012100701550310012207402001002109806c007140042d090083c0c90050300004c00301e407856030290085505019004007441d110240318400300d6020192081d01aa4a8030b51803800180ca043c0100c000303048c1c83e030001c00d48130f2000481004594582000b0035401903412076108166203d1515280741880b43c1c808100c00c420103c0d540d4013844905d50280184c10558800e601e8591034003446990610162841d90b004261a0382081c000350080142402d90b9515000710303802001040090702c81c000c08000c00b03407802e10440d070b82d811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 809922086 1250 809920836 809920841
    0x6060b0a0f020d11030417010b12060709090b0d0b07090b0c011a12030d050403050d050403120509071d0a02310819021c060606030c1205061810080a08070213 69
    0x44c040c21310741c018071041c00701810443d4440c89200c0420f0000400c8840e0038000703140360142c070341c076201d0765040340c0c007030018a0f0383c0300207850f000d4211941c060003124031010220f221400100380203001c2d20300103004034078043e1107070070100c0040070342e1130203180c90b004180440e03802482da402c000c0305000000c0c2c140212034202441070305506e441d41e102540c04c064802d0b5201c2c002c0c100082c012000c00504001c840c491040134446ea9000354000d50700c900d10b1910350407845040310310140c40381701140d2086008101480071003440c3c40201421401134800740d01d6001c4918060300844030300342c440403c2410424100300c4407969040d0b000d10701c50071001c0c01c590381ea800540c64450a86007042d800203c00c0203c00981464110001032009070520000241c00350780b205012103001e0f401010010303071120010b40c0503550040001540100300342d0304001d1030812100050842c581e05803250340070300d000400071341c0030840840e5040041669200b07071103140185207807034541544500d00880c030914070b200d240448881c135031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 809923336 1250 809922086 809922107
    0x912051b0732100507050105130b01050103021b2b09030b13050c040c03020901030b3a0605040813141011030720030d0c030806040906060b0a0f020d 65
    0x40c06a80d0300303402000c1c0b035581080070703040080da000ea0014211800c5850f00d0401d10030070a0750ba61000d464036a00d1800b40d081d2030018240c006000c0f60050b0701c0001c9960200d6a9045400c00d080042e0303910000c84042101a00d00c03044807006009111304160100f9494551110000d4145d0840d124034000e44010343d0280c43d6400003402c00305032903000031008900b02407103561240c061811191404511000101171710210382e0745e0f0300029004290070316156014010101c01241c221021070801040c01c807079400c460359840c0802c00340014541e20340c500403030549900c2c1585420075800e006a184c01d00b0550400e600c44040d40c141c076901600001140141011140c000740741c0180b030001102c0b25494200c800c040d05890b00c0a1a02040002400080d1182085162000381e120032450b02000e0804040c100b203410f10411080c00280c100c040c001a90107074005502c141d00301d50025080b0600c3c10302d00300810143d00a41891400091a240d041307801034a9003110000c035070708544c6828800a002c6500f251780 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 809924586 1250 809923336 809923349
    0x40c0506030705031b090316080d050f0f0f12010f0305100615080c04150804020a05030a0f0f080f0703030209030c0307080a020d110301051e10050a03060c030912051b07 74
    0x144080340900440080b804082458078210506240c006c00029051003066507600880030220501040311141c10b101c0d000907001b07141411410242643d01c03a0f450303846203003d40100300d040080d4a400d0544002d080d00e03203604040c03004103055a180e103d16495480319000030760380c3d40f00c4c42040d11030380d01c040d018a005590070078101c1c2d0039014002300c045e621543c000e40000ca090606020200345a55503100046007051960707107480326420b060043c426085c1458004600941180724600049078144261683c0d45a0005003403000145500340a40c240c0545c06020740a064009020001e2690503005000d20b243c08405076025a000c9008041c2d0343c0306240b04644003a000801840b01619140c00f110518174042c081d004c02d4015044000b90031254210340100b98241c0801113404070008501e4510b500500841e40381741c07a281080c00003a103d490390312000700003544036620743c1c101500c0794012074030403503010700c84254180382901c0142c0b10707420031000d1011f090680c1000c49d042d0400003a412040300c41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 809925836 1250 809924586 809924597
    0xc14040213060503060d14070e0f0919060e06040807061d070902180d08041a030603060105220606051809060907030513170a1e120209131103040c05060307 68
    0x15103941920710f82c10042ca186c2d4032940c6d00b2150300101e168034601119240c0c050b00034202503420a49000740e50a0b010301040d80c03882d090000c0000c4158001940c02440d09030700c61004c024442032601c40080e10222041c41d8281c00751405010030080302c035000d015131b548140b206014520344803501034202c1c1150600c0580d9548180400c100c034048582c018a00e0310f0131030105200c8403901c100494068001c000b021907c0d00380001c3c041040c180300a400036001004d240c036951550500d0710020782d03110410300600c1d1180f20042c2c131030b20f10182c18440a280303d8158000c1401510741c0c6580190068100003420030000801030070100440ca802c1ca0581e214103030003060000d01d43c036440021002803100a140103400d040300d21586000c030384010b82c42440c0c0d00c02a212340c0d65070640d01c40000c11000d010f4a204001d4144a03031701010090300001454201802c4410050329140c05800140624541c03000c040c007010f1600d103240c0e910810170001540f0840c003540b81201503039a00e00c20b0144910080310543c2c0001c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 809927086 1250 809925836 809925839
    0x15090b070c090c1115090c0d0f0b070507060e060115030c14030606090d150b010c02061c020f040f0302030105100605030414010207140d090e0105031f15030c14040213 73
    0x80b00c90340110b000402503d00f410824052008813454611000d100c2000305440d402040080d035000c0002c43d40b0f0060035204204013060035911096075408180004100c0764601c40016007117442803055a80300d940040f800e001b980000781109032942001e0041c200b211180000081c02d503800707406011080c145a42c0d07901910120990114a0368101400d4180e001000f00515141d50380c40405064600340034580c8400404804001841150400f8500360f06000d207038103080015903504003c0d510400c0b090040500c802280c00c41e050000c0c49a84ac4441c1074440201d00851050803601c1c180080c0ca2007076000308403c1d2101220302085102d188a40c2001410400020b00001e0013001d003c0c0b001c66605c0005824403200341e4585956041d9039128a026520858003048119442a800d200074100c00611483e1941008080798035032402070302220030081c01301c00c010a0140d040e4007000f00c151a0000401400c0d072285440c2030301400502c1180c58280d46540310302e502d86020b00c2110710250117003040c1103085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 809928336 1250 809927086 809927099
    0x902090a0c180e060120120c0f151f0308180409020913020405010f0b030412021501060c0203060a05160309170409150e07170702010209090f06040c0c1e0c0b0415090b070c 75
    0x350f01181c2d500001d27000b840e00000042600b00241c4400001c0341301f1500c00c40c9410482030754004c40c0f07064a5482c030440d0240810124840030b04442c120721010514800244983c80420040c00c00c600009411080b61010003402d0100d450b00e00460354401c4a09100591741d501d16401580480e0040c9080d8801c2040450001003000c103031421081181e0040c1c9010b4500580c800304071040036800040440e074940500030440c501071061641c0028080d8040183d42810852100380104064015043c560380c0ea0303205c420301c0080829941195500300c1d16a0356141c0b81e0034018064036011006488a0b1007680000c03912240042c0c11a2141c8007550310b08031007501440d2044820725000c0c3c08030741555401c02411203951206070181d03101d451045442070903418070200340422078522040070410401045001ea00143e14181e4a5070710b02c4403050f41448500444c1400e1000301510f9000d03202d103000004001804801b0300c400307080980d0050300c4003400302e9568500e0700624230415038028001c0718081c10602c141d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 809929586 1250 809928336 809928373
    0xf12021e0c0d0512130f23060c03040b180a0602070614030a0f0515031603020108010b0306010908061504140105060a1409030d02030705100902090a0c180e060120 71
    0x1250240b800c41d80814450703801c03038004e50700c0440d0f80d00c000b00c11400c081c44080c1030f512407040180b014181c0c080103407500683d0403040c0c80c0050840d43c441c8100242c1c0d900c2c22101007007541c0245c04003420281c0e5880c80a40b07411039600e00d40380e01d20300500c15031400143d5030380049034507811a40d8a403281c00c4042050804500d503584020001510b242d541c4103100c8000301144101e030b202d860b40d0081c003102c05590780105440d02000001d0100b486600510600c0140d134441c012038111801016155101d032104401600c0c200e070680c01123070481c070a60042041d12040c01c0d800b402c000c81e056800308902a81c80c4407202c00c0800900802e5000441040803410315031154061184690824807a28241080100080c0c100500003840d40c006074008500741c0b0902c00140000110059000e40400c50200c59502007951404002c009100306540c4861079080c00d40030b40070100c680d83d01800c03d60447c40d01c504240701c04080685501d40040c07404041000c4541c0030400f20303440c1c560404003c0c03100510305035010360b8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 809930836 1250 809929586 809929609
    0x6070c080c031215090121030c050a0501050c071a060d0b10050a08070914010807030f24140633160c053c0d0f12021e0c 53
    0x21903120801455030783c1c1810449480c0039120514458503200750801c1040010301041c0c02000e007580c0780010903074480034001d034000c04903681800e144103004042d083c12410481180d9016185500340020001c290010b040100f00151080c8000440410809881c141e1100101e420b15080940800d400001ca03414400c0315505c40000205020f10941754030205002038203030303031200030130368000401400007007007502428035900550740a486480d0314100b1100e0780e4440d644005001d03890198402c50501c11040b40903403080890a80721031a00310750b54556002081045541c0c1402e80d1800c001c22514600202891815a040f108020210035143c1400c44403425440048640c40d03410070103180b100c4428501001c095000f40c00c1280001c1c5800700340944180d036441e200d0380e100d015400e0003079005924911100c0480c21200c00198248010001c940141c0304554040c140e44401c10b14141088503050740c00c1c1000201e07030309a0360000d050054800d418507582c82c101d24075411035440c070181030030301e07840200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 809932086 1250 809930836 809930857
    0x4031b15080a02070507260114011a040f0b1206300a0209040503070b090f060106140c032b15090e16081b092401051908010e0906070c08 60
    0x40c5000c00543ea92450484247e000300d000040d600400e003000701d1501c0c651321060314500e0003031180e0002c01040b031803483c6050040303420103a04901c05245000b43c4000303807400307000b80703049080403503840d00c2c114030490f003200c441e410b04030541800040c158148102d203d140c040004000341d03410344000780e00e800416115440d80314030b40314600781580580d46040c1c0c41400ac2d406500995a1150b145c200340c0b08140e00200380c84210f9108044d50000a40f0024255045403600e1a1045455240307401804651165404c600003d100219000c907168411105000500c0340e02c0d40c48110550306824004107075511001005050701c0700c4001040040601e8104141002464040d01c40004961840c0c2492082c690000724032988007946000ea086c19611214540c090100e60003503440c50081c071222140341030181100c0c0b062551802102c141d034050703401d0782e40411001d064565518040c030030003000542d09200341c5150f840968042111080e010030420701400c081c1e51072221600c490b85414071180d00c48410070b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 809933336 1250 809932086 809932091
    0x8060306360f0a081c05070206150a1a0c060708010b04090509150906090f15060d02150301140f0607020f061b0106240f09050d0501020f0c0304031b15080a 68
    0x501c88114103000c261030613882005443d4456808011504440c115501001901440d010501114a400250b0b040e44650384c3c01030006c2c0148110045650991145d12281c03d070044008940043d0819002812581c03805d0f00440e41c02ea0380d00401180c10300000c3c491448045002c120500c0a4a00c6420655000200c04115258003d1000c5003084051048070500c000e50001c105020041406000c50840b51350030500510740c1a41e55074440ca00114042c03e4079100d0780384401c1d0300301151070b0440c201e071000c0646010291203680d00c001c8440d00304490002c251184801c100e498003241b8049003a80c00e2180c001c2c0c450248105a4000d024440d446120b001462003400d07880e150040809009801c0904224540c041a01c03030200d00c82d14808404140010034440e0036000741002642c4981b00303504482d0704685180d48903000d42840c3c2c2c024802c4e107040b80ea9001340010032190189000006004032032150082c0280c0d0b00d01d80d801c603800321055008120312064024041d00304c4034810300c1c0d031540114581000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 809934586 1250 809933336 809933353
    0x516081902300f0103080d0f0f09030e01030b0d0c0303080903070813030606120f0305030a09080c0a0201020d051206101e021b0d02030a060906090b04030806030636 72
    0x100010006452000540c2861008400e076000000c65030283c106414030403502144d411503a0740b5136503000303e500420700c556550100c0a07203d0303502c2c1c02070039030383d8000d11041115407110b0500600f007000600655011904014900c1043d080131048540c6850700000018901401c2d40d60072640e1030301c00740082443e03120a22225011034440d400410340c4806801700c9240040c03441c41c025040c3d071095840003140783d41c0000c02d0804200c090b44001c400c50b1f4145400f541d01d47c0d40c000118020310b18040050507500c000300b45107030f00b842c0020b144100c46000b6000c403504001d01401c00c95480c803c01c5504880b0f0401140440c444d401d00c0302d0f030003130710740101e044c0740c030a902075950441854030305c0d100b840740103a20541d24081c2e040140d0a0282c02200150349541e0302d0800c5801280d030321414440010840c40c0d90380401d000303110f8281e010746885c036403007260b01040b81000d040041200c0c00560303103607200b8021000440e01c1124181d00183c508803010410940c051114010f00d80320f680b100c0344222090144004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 809935836 1250 809934586 809934607
    0x61d0c09060405091e03070302210a300b1807090320060c011a100912080705120403061802091501121107050f070b03040b101511010516081902 63
    0x500031144d5040100442c1c441f07000381402450101491b120007a8481085600c003080c0342c10750100c0701802110309104a00f503815505c0301001080940503e0283d002036030203801e5050603500107001468040b1040721a601d040301710500406070940300980841e0030600108009002c082c16480c442071440b0203000e000c00001c01041c2c2a41c44100032aa05954880320b51080c0030b0300c0e242013484c400d4141d6081c4014a024a03020f450b448540c0114201300d06154030710320800440300225020180d015060707450319425080a96510b801c1400304880d940e00b030209258030501c01c1d01c3c603031500079002041c00c40c00b03032111001a034414a0b55401789042003480b01c03880e42a85464041e1154021050f002c40740e85038400c0c06c140d81070a04d042e50301d0002d9004000d0402a003000941a0303500181c008a900902d0f031911420047c0c0c8060941c8a840301c8200c0c4444040002d0b00401080000202c00000344a2503640c2100003044c1b042e60b900d40d034017090840003c203204054240301241c1d60361440c000103203482e240c0c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 809937086 1250 809935836 809935873
    0x1e070f18020f310b0d0b22050103150e06060103110c160f0b0316052a010b0109120b150103141317041404090609020d061d0c0906040509 60
    0x19829981c001c00f0b20b41c1848082154a0044240383c000c0c1040d209503041203150a0144107503919050f100f40c80d214014030580c2e800b4802c01203820354030003400d990708841400c98060b113803d02c4241c40c02c00300c001780725113981400e0052040500822024000907640d08005400400041380203640c40d9209002c152083c400c1009210348172394000c44001001d525010025130013448980007000d56101c01e100b0300030313100001004104011385034200180c9a840301c034843c0c1506000401c83c80301c006481c5001c4a4408419409942e85440c03c1c0d035184001c6440310203041088110650080001c034007040000e14110035004941c6e4203520501d804640411070b424128900201502e075281045d200e04012410072a5000403940700380c4555540d1414185089107103008840c0c241c007200d0150742c0b1094550104580c9500008100b54010302c0c1103910300c002d0514030003d00001c2280105c0d030414610100103103100003240b0107800001841078120381e807041f080c8005004041c001403528070400480c2c0030f410303840d031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 809938336 1250 809937086 809937097
    0x50d020913050a0e0d050d0b220c0320121510020c030d0e01020a0305070215030708150406051003020c0f01020406080a0b0d030909020a0e121e070f18020f 68
    0x10070702141c5410084162400c4903160603840d1403541c4014520144071350810140c0319590702540700000d01362207500100e407407008824006610602d044491010b0a0030a0f809145024a1036030100322420070025540001554031031030640c0b6034024080d00702042d0080e083c00340d010b1100080d1132800d0424202003140348403032a0f940b10140c0c104255071600d60804000d40c04040c031513440c08940184040002039126044000003504101e4000382d0300c0c0654aa00120b825000382c1114241d9513464400340041c081c40701900c5d00b5407107088110725500685490b01401040d920700038131014456400300019030083d03204014642550048102802c440482880504000d10503a203030100d1a00d81620b8a00440e01c1071044240310f12a4080084007090344420001e003625951100180e4a943c030440640e1468040300010303038400c807140c603008103040003c94002c40c402c803403044041c0360080340380c2d40640f50b004900030644000d0441004001c00340c83c8182080c2c2201ca0300100514020305a103106206a100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 809939586 1250 809938336 809938369
    0x22a0c0102010b0402040b04180209090f060906030a15020a17040602040611011a0d03020a17040602071a071707060221060301050412050c0c06070c0e09060c0a050d0209 74
    0x2010200a540c0a0207182c031000d408540031450035080ca03051101c076004a00440326102c603000d1015007a608594102c03802650002c0c0f1b10001c520b0700c00341c0c034a5415011564240130343c0c04400400c40341c1c10f0003d14010b00c290302c00c0e1901d8180c00c0020000c0300940000681d2820000403881000548041c0904079010b9400390780090307600c03400c01002a05104402030781d40910383c9880c20000d984100890880c0d070004040394401601001400d0032481d09090311030107010708032690b10090341c501c10480240110f641907025901e00310b58481c08100c0c0e41e00c0f1084c244100ea032080041400003268014084400141e0801003414019180c80714000c0360440005c05141c01403200301d03131813a00402c0f00ea059011104800a002601d4260764080c480c841c0c081e50071041c08000300d03611000d65824010005c004c00081d00c01501d405850500c0d501942291242915502105022480d142e8000c1000c41c030640055031814902031044000b103519500200b4403080195082c000d01842e41d81b2010016600940c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 809940836 1250 809939586 809939593
    0x40b06131e0b03030c0307080f0906190e01020307050703150204030b07030204030201021504030e150d0f15150f0f09090e16060306050a0512070312020f0c0f0a09022a 73
    0x11007640314100c0d851407006030301c2540306000406071100000116515694415152a2030351240318484000d4050300745019402080030445078210140e50454038200062542c410404015490044ea01d034131411070701910725007202c030381400854882403154649001202005292030350b02c2d00c42d0240303441c0640c0c40c40b0003e900060200159030f41000b084940140149211215041c42e40e009004c0e11004400c07140241c00728040600d01a0034070f41035919188138080c0a0240c401d4072440d041c01130440311b101d070744202c2003100017203074a10701d55001d29801700b4143c031419402e0048000a44010481d1041802040354049022a4036001070081286041d42c4200800b8007821030300c0c020b03c6504042d04158101482c00404011a5a40051400480e601910314140c0c00d0100d6600301d003445240e81010b8440040c0480c13140380958002111240000c1c1c04054450082140040100421210042d41d80c40081e15205102250240d070041c01c00090080181019a00c60984c51503201c0c3d00300009100ca40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 809942086 1250 809940836 809940881
    0x61b020c0603010e010e06032802040e120a08040c08011107061b050a0509010201020c12120907080604060c02010e070b0d0627240b040303030b0103020c06040b0613 72
    0x250100315009a200c000c403265421503041c80306080141005102c1c801d00803440300c01050b4151000e100a400400c0380100c135070100092030207402411001808124042d5203409070b50a0200408030748501020380c0030090130b1429083e03807003c4812000150080d0346030744890000183c10103091152020107071500300410303201c00300390508034101c0d02c154100c81134520380c0145080d001a4064100c40100e605030800540340c0c000c00c0c004038024003c0304824501d52041c40b1a44800c84551405051640d030b00c2201c00c007496480d4140c0548804162040da6401d038080e00125000480766046035880e461030384000144214500300c4140380c00304a500c210081c01000400a2003020340d1f000300c002420a58a420014540062027943c0f902000d0790480340c56607a5a82644500d038449190400b00542c0c409100400d0f03889a00c2040c050b4042e100c110007103840c244002c8001d5009000740d5404100e01c0000d0201c3d581d5545031000004070040903240d002c94144511200704c0c1d414481d0542e40d205140030040b01d103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 809943336 1250 809942086 809942141
    0x1101200a11040507081b07050708071a07111509062205030f0307120912112403060d14190b0108071203030c050f0a0e13180b1306 57
    0x181180c4842c0c01141008100300c5990340010320a0b03040000d03036a10110b5a02c01d81c0c0b421120340503070140148207001c1c000d00011020000034000c8107903446194183d40c2589000e8880c0400d00c140107004000140808001c6c006141c005040742c0121030b10b900da41e103000382580014009138070411002c8614164072188105c1d8070182c1c08540040c0205900a1002055000038039543e4082c0c07001c0286031841c114078441c03040340300b00b004400910340307075004007007091240c41c4c400108400d00070319500915400e1003010340354510001411500071040b681d1850b684503081403191815a180741524071075070102000502c1c01041011041c0720050100d48541c480062030000c12480c4103070700580380c0358440e0f80140300820110b03d040d40d50070b601d41400200310860034015601c5015006404001d4080844d1280010f07030410b00804112800f02d4000005d1042d1406490444074056800105266898000c00008141c4250950041c144ea000c00a000c07880f03694050076980e04540c070100c007004205413107080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 809944586 1250 809943336 809943353
    0x90d03020a030e0411040306051005100c120207120204020c2104050a0506040602150703090b07080403020f120a030b03070e040c05092202210105090723030a1101200a 73
    0x103102c004ca0b020300000d0105468000c8900a600002d0711041d07a460124024400080b1004001c000c05400200010300001010740800c00d115800d6030b64039509600314030054408a000419542046201c041e044015000c1c40001c3d0001d00030104241306490540c104c2001c2c0912696182c001018026640c074141001c1c4840c1c0400b82e840a80190403d02042c1301c501e40104514000400118038030036a981c03446000c034003030302d00f004c0081c1c07a21003800103101c1c080f5803100703000c2c0c440c41c080e03001c41c0c1c98a5045259143e803040722040a00c6250801e100c1402031600c40c0d04200b074203103801811920516200d01082c04002001e8408854180c05510108482e0405000459000d24010303000301002e184070b10811903e4203190b0000b0300c00c0d13500305130300803004071a100c40c0d1652100e9a0003c0003140b80c40842c0c560395a100e03000d49110521500701c0420040c051060190032864003401405e401141c03031780c032603281184139141d45050240c131407810450540703c1210402d91411947c0103040100c09401c2c428003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 809945836 1250 809944586 809944607
    0x52b1a07090602011103181f09020901060e01090902030a1d070302030606030a03080c0a0c08070303060e0c0913020307110a0b0f07080609040b0c0904020d140c0418020c0102090d03020a03 82
    0x43d0790400503480030030101901904c0d4004900300001160403048022075040552104811a0303050740c1d5007041181c501140d10603d4028801e548140341a600c0391000c0e544601c40700c0302c003400100514001d01c07038078031650051038100117060320125000107081c100a0b12a16441c00d030042c40d51145c48200103500d420000f090704080103401801c084c50040e10010300c5132500410b00020501c0004440c02a14031034107103884000c6e00500c20715103a21280c038004000c0c1c21076116112015603800041100e00701c560044640d6010001d014a09803901c1c1d80720180039401c010800e900303010342280d000090640c244880d056092240d40140c507249410500c002030200043c0c0104100031003070040003555120264005e07041a001100500c880c2c0e80c409a004080c030802d2000d94001d4004141115020220b4001c2c0100301405d091102c66542c4c0c00d0308801086c002c600c106480e0700804895140410f4243e0b00510007410071600141c41c0002c1c0c00081100d140600e0400c9005900003074440e000d142d480b514055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 809947086 1250 809945836 809945849
    0xb0a110319020309090a060e0420041a1807120906090f080a030e0105040305121314071703070f170c010212160e0f010f0c060c081609052b1a0709 64
    0x140da410001c444403002c2002740024111190140c1406501311500741103a00c0c07031002130007803084901c40070f00c0664215424500740e0040d07075004c5041009043d2505441d10410745942c0300014504c00800c0e61000c0c0101c6e80301134032000d5482c18804c0200d4081c0211201e0940038040d600d685404104000b8101c0e8002200112141d140005101c00243d003c0101e0300234070700e04010100d080d100c0d00c0f17401c400700829800c010312010403404000018100402d2003002c07144444c804920b04483e04940ba0340324401c0080003003513840502d6040000071011040d002103030419400280c10504080b207a1401ca0307010b40500c0384041409410000005e9804042d01c440c100285003200c3d03442d03c08804140092444412541840389100311441098450340d45d80d0341550f00074174107000b0064140409081c24000784c41c1011140008070026451500441c07044c0202c41000d00854401c5400010fa90030000c0050742e03190f04400c521350b030540854108404016500c241605101940c1424000908540219400003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 809948336 1250 809947086 809947091
    0x6030e160e061003020c100c0f0c080405061b060405011d0312010e06060f04170610030b0103030e040e010510050112110405040e030903070f091103010b0a110319020309090a 76
    0x620002103400849504114283d95250305120a0350058019018025881800c3e101d03845403a9100c01d0030b500300440d085101d4540c0c1480e15181c0070211020f1442c00320103030030000100010001410104010f10203115a002801d005458100c005410420700b502c003601d45079111108280090883c03500102980030b02c4c8003c40c50040c9540d0a034941550500c1a40c0c0c000752104006800b580300d1408030b603e100a003a110aa6a9880da981c50b0355401d45c0806040d0139200740d4000411040c1c01d4208041600c2d0040803004a5070720716641120311a0000000e103400640303a0b9212402071000740140d071300480000f0452109141450300040c5000b070030581400c1d00600300100c80d102741c04039604440a4400569020034800d0805541e945184a1a01819014030940c00c0c00220340c9400c0c03485c40e040c4d400508041c000c075400201181068082070140d112a031500b0000e10020500410864440000d00c50aa80c00c1086414000d480145803030f448002580001030004840c0ca49940078552150380d80c5001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 809949586 1250 809948336 809948339
    0x10b07053909010602060601180b0a0503090d080615030603010f2f2a191202071a030a0b1810031502030403270b0301091b0804021e120706030e16 64
    0x21b55440e0064540c90520410828101c54054143d00c0391000d443e03420081036031420328460040c8164401c98000f20103020b035600c00341e42e451041d26880d014150051002c2e668680d110780070301d1180d0018051540c0740d03603100c03028265511280250300729003400710314400e00070b4481c1f0890720079144201020101140d003080b000d818100d4031040000f404118011009210b40110550380c5000c0b80c025640000b413455809000c1004074060110103807800359401d407040c0955548103620100c81400500800044c2840014055401d541c480b0581d000b004083c0441840d0912000c0e91140068403001c0400104200c14820300c0300e220556000c49440c1c40c011841d516240e18000d100c00360391002c412080d4403010002102c103e10b140d144001d003503e42d0750a9070b6540e60b480a9001029181c074001080c82000091070415405203c01c5441280c02405454400340035402e00402002c00f20126540094032b010030250005040003214064440e0362400034400f090000300d2442c00c071082c8034100089912900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 809950836 1250 809949586 809949599
    0x3090210030c050f07050c041a0316230d0c090b0a1a0d11070c060f0e0d2409080f07060e1b010309030309060e0a02010f09050108010b0705390901 64
    0x31500c2c1d61050f1036544d84c9500e002d181450415026403001c6074040d003070407854034130203103400010200c400c0100c040741d00d0811003084104e11040c81d80b01c2c01103002c84034108042d50f500004441d280c1c0c042e000340002e005c0380b0a82c0c0c03800c0e8040d210303410040029594447c51081420041b030604007800c11040380400d40618180719403a41e100f142e480c2d49070705440780d17142021800000151080c3c180c0c0043c401d0050341c4c5541c001003540d0900e5140f080010750541501c400c504103000a08107007a0048108203905003400030040c0d85410480d4095046641e404001011031000c401501c549801d4040c130b940c1e43d01c41410524159000c12003201c90170b40040b103c00801e04041c41c80f02c00125800c0c00c0200c0e021041b0700b01a0f00a000e8074102904943c1042c50810442c0c03408540005001d100740c0f500c0407500c820b5070f400c48441c0c8040c002c150126000d1801440840da4403000392540910070740c100c4901701e00940b541003008541d2948061504014165000d50144140400d0040c94040c1c51860b1990324081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 809952086 1250 809950836 809950847
    0x210f10080f1f090b090303070207050d020108040209100f03050f060c040f060e06040306050a2414010806032401031106070b0103020415170313050301050105090708091005010603090210030c 83
    0x104082840246507a0b200103040d1150000300c5100d03000050a0f0391071800c0310065882e0f50003195140010f0046130000305061901c0302d8291000c0341c060391103102c40d035216420300c5489180540140c4001c8600c5c0e10010f0343d5288020035102440c801d44c09030120b0491020200c2c50b103940540000b04600c010f1109210590300b950071107003164181d1038400082046040030508a108a40001e46118201008c00a4580d00d0340c0100310880b0240441c1071412440344c0500308107100174000c114001d055501c08020390340c462542c0a4200d00c0040c141c85900d4088002c5804010440c05042001c070304410041061080800e61150844415106540b41001d255504076100c03a050100074881d96a40c0e4004982900c0d03244044041c0c90400b80b01c4600c0340c0c0c8810030300e50301d820030b01280209031100c1c880844c8606041c00b480303040720030181010f911511500c0e4142d034404030060000d10b15115000d40084d207041240141c5009012540340061005240c1c0180214079a034880e405003418140800883d101780d001c0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 809953336 1250 809952086 809952103
    0x803031b0a03021c0515010c0209070f03020c0a0f0c0803030f010909030c140304052103070f0201050c0d0f14090306070f030b060409050f130314210f10080f 69
    0x150000c81d6900d01606040e8001c0c0507080501e1040700001205070038200d034503030210340207606803c11940410080801160031f0000850700a40113145070001c80c400600411007400e031130030035080c09410903405501107840c000c85004251001449442d01006002000b84080007600b40540034508d03501d071420262808401c1840b40489441e03455010105052061140f250101da00590650010f100502c0c0346659400501136213104145540084510325030071041d21240c0c4400e40003a44c1088003a80700c1c07005a95104030240d0510004200f00003200d0000d200d002d181c0d43c1e02c0e44500c1d50324804148010314420190108007110b11342005800210b6030000740d2180e100c802841c01030a000c0c69410228045c00c540c48070300342c020002040102d456410780d00302a2141e10013801c540450b607204802d6183e00415414080c0c0440c0b211040391100c002d04200500f5540381110403401e41c901c0c80c02140581c00d00403146110741c20800000d0200c00c2c441058a0700082c000e880052251101c4c10742040d40310242c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 809954586 1250 809953336 809953381
    0x81302010e010e0603090c030105010504020705070308090402040305031b1902090613060b040803031e07080f0a0621020f031b222d11120a1122080303 66
    0x824119000e5603202d5240c024101c04040c000b99106d041c000c55080e130700c10071040980d1081d42020000704442c1054420360f45007680020041c04000d01e15100c034035507680b2040307400390001d030208408004a0010401080200b0302d5a2021000e40131301c1510500b00b80c0d082110041400107201004c0140c0e0301c50012230b410200c1250f100c110180500050002080302e41d0000e0001c00307010800280c40368011001d10312500c4413002c5c0200700003054840c00c2412004981a8001c0746066000c99030102c0000c00c45035001039103040002e00e0703503107500841501a4450040c410700c0c8114610071000c608100c2000350f5060010f600503e6044284d21480c0c0d80c0038000e441c01c07030081c11448002c1e8814495076002d4805131608a4040100c880fa40180000000f0072a007008450034401c2d00041c003001c0a84245c150301c800b100c036102c2c1000000c0d441c0c140c68203030203062035040d2515004035010381e094040003043c0411101d011180f165044010f40c4c6145000c40e400031420342c00c18001c1108801840480c034080442 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 809955836 1250 809954586 809954597
    0x6010b1309020d09290f01032f030105070e090f04031b0809090a020406030f09020a090b03160f0608090f1221180d050c060609130b0c0a0e040b1f03140c120708130201 73
    0x1049e41030080060744202e030081d450341c03c1c0800d01c490141c0008418452510a680d0b0b25801d40c0d13241441102258159402400143e28200c01c008000000c81e04450481c132444c4001d28150002002580d080c5003910450700c0340e60700150802c0401e40511801c11548d41075601032206005540001d080303500203200302448551651b25480050781c00707124a400d01c034481c0c0d04070b030b24aa07155041d0150070082070180c24007040100b4049418084002051912503040a0003007400f1450070500c00782a802844551004000070043d0300c2c20000441c1d455440381a018172051b455203000c4600701d203001d00768000c2000380b040401004005c2d000100e2801c1c2d0181c41526034a4854980200c0b100e800061543e0150040080c4405d1110002e541801403040e070201e592545121010b500401c02240c01041240b54001451858802c0010b4078401020030a15203040018a0055448030a0703200102210381c880e0400307001814000720044440480d030005010302e07041e002403604a1804141100f8600c000e0b045c0507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 809957086 1250 809955836 809955893
    0x60a2c0601110109060b090c040f030f0c0b0c010504030219030504090e0705030d0804030e0906060d09060605030a0303020d050903030606040b1e0c0a030206010b1309020d09290f0103 80
    0x240203210b20212541c0c2000200030404441c24182c000300a1000158464511000441c401058100603102541d040c6001090003a05d140e6a03a450b04039107580486e86064092800504003015030040c004506005e0004102440c2600e0b00078208a054608400000c0d039030709108011039881401c1d6415a449403a000a03521045241a0300d02000c50f440b0a606105401c0101411580041c03040d000d240300b91941c030521980306d010000810801c86400e07030403000500000800c0342454100313040c56409548002609601c23000070038202590041c0039404240c000860010724402c17072003400d900c003128901450031030600000298030b030300c110300c01c400c00380c0070114907400d0030003028118048592075084000d58031514091915150a4104001d03805402081c0000070000b1007081103403040180449140f0070f483c10910b6110003500014602e40c403099032103070420006900c8100d2030440c0c001204a1400c2808840c08001108400402e000110750b101e8004000081003240c03030b103618500e020424440c12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 809958336 1250 809957086 809957089
    0x3160b040b1c06080a0b090c06220801052d010b03011a0f0414040c0e01050f0d23040b15010c02040506180408130603050c030f0403050d0c0206060a2c06 67
    0x400030840702d0400107203414400a2101000100d4a0f45c0501c1800704450699030500ba0a07200c034031480745035401c51002c200c5400e0020000524009100705000c40d80d0702e058882a061703084a100b12441c0703401e03372220703440c540d145945480d40b81180300500c07030817110560404100d884140010301c0344003010345544850002c070320100c900b40c17030482c00b4000b511034449546490400c810386910031494003c0d840e111303a200030f46200b8100320110fa00107840e580d141c039a203400e54400039802981c064001c2555604403074903404022500d55440044105041c0c56403e160034608a5030b640503015402d07101124140703265076604070901d0300d09160111000525a034070f04010900e004201268075025100540c104401c100007403026006002d0050301b1120700540741d000c00d07001c0301e07811399000c10680c0c020f10000345440c08a11900750300521074039156040c030210ba00300205640a418100c000342c3c104200304007450819a074403d0080080d020890710b841d540d42001d03031640511034000300103800c0c0c003c00071304207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 809959586 1250 809958336 809958367
    0x7021507020622030303060806040201021b130905010207141605010f11030a1106010803040302180c0913020d0c0c0818011b051f020309070605070203100603030e03160b040b 76
    0x1240b00c40101009142c00b100304501640340f0700d0100f1000700e403030180c2c04a110080000c04511442e13040e0014070355001442c1c546a02c1c00c0421090710360016056070260f10030580d500030603450a110b01c001685070355403844c00081d180a542d9901c1d00319030140038601010f81d628100102162000c3c01c0c500b030301001e2030768111040d0703002c81e040d102244000112504582c0d0f0041101c8044092501a2021644c0300d5840d2600ca01c0340f48006540131f00a1202e08200700102c00b0b0344c03a0030144070700349145030058210118103542041074080399415070200d010010040310b4050600b03e000c2c5450545c6158046130340744c15250262825407a0303195800e0906124071f034003480750303000c80f00c104101030001d0015a28142d03030703107030200c4580f01101a943c2e451140406801d00a40380100506805010900d0034a24110f50a400c41d40d001d80c4c0c14800c246030120310101030300c02c03180510f009580c0d800d1807903180c0050514160300c42c4000c00c1c512442101c1005050409000c0e20140c80c0f076041d12030341d00c0c0312881107100e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 809960836 1250 809959586 809959597
    0x30f0c070c12050a05060114011d04021e0315030c0904060b04090507260c0f010c0302120d060e130c0611071a12012c04030c0510051902070215070206 66
    0xc0c10400344103141c0502c0000952130980c0c612690444a45a881c2c80140c07804040c40c00c0c2d490301083d000c81c074014040380281c0007207008540c05400103050610804d101501d10158000590340b009000051125082420b0b076462001e8034254001c1458a0100d03000c100c421200801c040d101c25600c0180140c6552650002407005411070f0840e040c030340d200d500c6984448090000e101074840304100c134051020380801c07420340b0307000001e24800c4104800700040d52615003105088046006d2540342c9007181c1250009040700010340407000541c1414202c100c8010710b409011103080c141d0300c030b01110005888a4035035007a900305140c40b55a545c08003040714941420342e00501c4040150490a00d1040d00010151912605401c508805179907604072040448140400d84100607003d8040000038050504865400c50320902e04038ad4401c0054031010700707210003503000c41602900c07a01131082c1400c41e4524200713000b0f0350070030840c0341c076049a0001b03036496800e440c45500c0f0180840c01d007041d540c54500303551 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 809962086 1250 809960836 809960849
    0x30715020702090f16020708060a0c020f0115050a06210f0f0914120304080f03070c050a140105070504081f0e0717120a02060a09060209040903051b03030f0c070c 71
    0x2c15a05040722071400008044840d00110300426495170744940c4002225011900342001a008030b440703449010010f001d0460650302584100118042041401d120b40200e015519880c0c509040c1440104900c109581e0301c498100b00800b42d804040c4011201070030340001c5800c0002440501c40040742c00031b0500b00000041781440d082c140818080301c820300d1041e0700c01389019a2080380c10070300e510f80c807030000f130701c001c0c203d03000c18004003910350606001150824654240345501d2503003a034469140c100c10110071214030800c4062259040400d0007400e81060003418011f04040c2400c0103d950381524128517150710100d59500788508034a075024030000c00400382952465911000c2810003820854038420244c440c80c1280301502080801340d461000309503010300aa038458180100290414500648a143c0c1c00c1200c0b214954071445100503652194603103a13262071030302140071030180c440610203125400804c01c0204800c0e01c080300070340c4103200c1d030f0402d5119045420500500174440d0040f6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 809963336 1250 809962086 809962099
    0x81302121506090a0c051204031707050a030f181113060b0a08220204050403211a0406060c2a03060605122b111603030f080603030715020702 62
    0x901c102503050035031003004292541805610f80310496400c0f100010401703000242c050009491419801c2c1003142c1241c01b915000200040c00c3c4103900303a1280035506040030600019a003c04035425015403200d00c8244881044107407070203500d00d442a588194014000154284041220341c0c1c1c01c2001c483c1c080b1080e404004040c0c4442e00c3d4412603010341c0e00c0303401050505002601c00303c0c100465140410000c43c00802042c241d1742804003500b00170b0412020310910352402070700702440d030440c0620200a4a000300d41c10200c00a1003808204481025000e541400b41c14002e2035002920500da40b6031008034001010440380080000120803200c0c040d601d184c6100c0042480300c250000410380350100c0300441e855848608480c1d54003440340f045911a00e00500d13100c500041146442c003c0e0009042401001d104c0044042c140703421303190104000c2020840c20302c18141d006128040240c134900f40707402c144c2040c60001e036482c002c1c4000185007000740001442c0242c12070f01924403007540030740207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 809964586 1250 809963336 809963353
    0xf0d020301030c03030908030f0f1c111b1507050307110a12030605010e0a0603020a181e05060f190e0907080105131514030304081b0a0e0708130212 65
    0x10f00c0c41450039200603000650950004030350328001000b01c659202e031306c2c41402d2410f80c9000c01c0c181c0c0c5803c032021122140c08a01144100717003610b4098460361000742110a0381d101d5820404102c2d08001000e1461264050911031004001080d01030fa040704c3ca40c2441a1681c0c3d40c40001c46800020164030403441c01008009420440804140c0c1d0080e103a50b1418045503031030740011940004070596950307121000749820881b071406039000b8130a8800302d1800c240c82c868070750301c2c1004080c40ca44c400b030400c1300703103526038180306886480000140c40b0440b40d1078948694030002e81c03500c0c05003041c11900b040b24600f00c20856405180f803012454405481c15400e868400c5002d460040240724581c00381e4520030b44410045110310072800c088201e001f14a00e4079091980c6c074110303400d04000c440d801d44000c11010980c1d8030300300042e00f2283e20320468444002155400d01c4065000344d0300c110005c1018100740400260071142c2d156220700e46061b0030000640f103000040700c4a00218900409006881d034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 809965836 1250 809964586 809964593
    0xf1210020403030e0103021801110118080c0c010509101b0c0b031006030606020703060b270a0f0501120b041a070302040602240c1308010f1e0c0503010b0f0d02030103 73
    0x1901c101c0f40641c54852580034a00d005600340e02c00c00c03d019042c900040100e060b15030141c0800841c01c511100006100c480c10300820480707588074081520060004248116030703141c1001001c15001c030030300e040c07030404c0d010001042c2441c2c0c20317050179824810072081e41002c04641c81404c0e0425500a00c084c104a59185034600440d402a60315101c44802c032031000c03c003280a801210308840c030960040c00c46d2841c503101d0000811420415551040503603490130815101c0400801b103101101440c504541004100f600880e2030030010201c03980d08000040040700400b07000d909030ba0341c000e11441615515803501d190380f9240340383d0042440c000b10050000a036032542c081d10545106400704e400c846061041883c7c50403040303003103a6200010070001005e8038070f03036005000c80070001c0390181d0304030313440345281825112250403441c2e80d5551904090710941c441c200300c1e405114040010800542860340c000c5c03c41c80140244c202c4030342c0002d03a00011001c2c8404a501c000c07100e4a045489586070b29 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 809967086 1250 809965836 809965841
    0x302090c0924091e030609070e07030c05040503030c011b08160e0105090901060810051905150d020a020102030618190209010c05011a01110d09090b0a0b1b060c04030b04020f1210 78
    0x1244e80284201400120b14403800215802a907180038070038120b0b0764170300d1800c8014080300030035001001024080003400d9202080648030b5911107000100c1c80c03038102c510b0700311b010311026228030030400c0c19410710a107039500d41c00303000d00d83c075103490b080101001a00c0140d5491041c1e5000640000c069000022910351000c842c0c0d002d82c0081030000b820950740e000300310304d200703d009144070603400c0c12208004614160391010684445005090300300302d030004880d0201c2e04a2031350320002d42d4002040000d185458602c3c0719404072040c23210312581c141100401820040c2c2e4030028035203540017400c00e00c141e020b91200c450b0187d2080003844444c10800108148030049640d15020408c2c3e20000110b0384404680400300c01d10340c1e5100700a841ca8a510040540040401550030a031044c8000c40c1d14500f610041140031103c00c1c0c04800d042e050000307d4581480201505034804050206000050a1811458100d501122001940b070400c40000c0c694481e07042045002d4800c16603464508040764 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 809968336 1250 809967086 809967139
    0x7061d0d0306060c2d02030a120f0512060d1b0605090301050726060112060b0a110d0e12120a120e0d211d01060302090c092409 56
    0x65405020701a6640c3c0300f41c2d0080c2449074000c0c4604284e07001100c08000a2401031100d56135090030744540c81e91070700803a003003500f0004107a50400e9408882c401c22600038400039440829131030628038149080b0b80f00000340b0800341c0070b28803030994080d0038014070404480342c80340706801d0345910b0900b5a561002400c207506c80b03500320317009500f0203001513900303405510106070ba580d444d0030b9040c000080c40b005480c80c1400800c1607042c40381c05c07100340041807103d00c914409440441034882e503404030541c3c00740c0564045540e03c40e6981c005600e200c1950f40c4070072047c8a02900b603803120f46208201c1c0710305050038500050076003000004200e10307824a234804403816901404401c2040f40c0030214450076250f65000e140400441c04201c8821510074588211030071511000d5030000f441c0d0520242c1a209880041c2030107001d80d11980280706601c0d00462480d0404045607095280002c84008101000e200c03260a21181c40300007002c030645042c50045400724040100308401009050244403d141d130b29 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 809969586 1250 809968336 809968363
    0x3050c0708030d06030c1719081207080403170108031606180b060112020405010905010516170901120e0601030305160b07050315120a02040225150e160b07061d 70
    0xc48400080002c8000702a56038520014082d01c00c2902042310116400c171310070811102c0366010440c80c1003480701221400d000303400c2d135551903143c0d084c14100100381c0190900c032510788060710001000500000821a04000300f00f408114203c000d90500600038500c0c88410b005010065048400f0410100340b03091003000c00740c803100071300a280030785d12080b4061402481d0100702040418050396024002502c0d41d070032113030300580300b1468503a122251243c41d030710380414120001c200c0c04c40715a00407548205610720300d4410022600e9160005588810602c4060144800001c950000810a500ea000160f412040c4210f080c00c00000c0200301d0340c41180c504d198202104040d4015290800b20201070031000401412002d14980810000b0b40c0034000c1d20100000a0001c5810311780041c00207421140110303410910741c16103290700c005840b10105090300b56008450100d0b120740f103541c610341c1501c1d131b080801516121a85402d100612440c0c0c060f4030b200c171560700c01c0708401d84002080040c0800c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 809970836 1250 809969586 809969603
    0xf0903010c1e18090f0e06071b0807060204030804080a061413060f02091e0f010206090a030525150b40050412091d010303050c0708030d0603 62
    0x240c500d000c4980810100b4021101c1549580000110b0303c01e800b1080d0482550340d108a02d1955040e040c0219944184000c1c41c1d00e0f00c03580000c031380110502102d0341c0721001d07081003d60031440403001505a141080f000b030400e0340208100c401d009445d81500d019540c000b01003941e81d40c0303458045a41702581c0c01d0403034406090290a01d060804261510f0003101804284910740605075a02c4001c3c04070306501184844c2c0c01d2043c01c1055540141043c1c0014110900070320300240c5201740b18449407207514030740c155030015017485145200054414007550b010310300551942202400325072480c4105c0c1ca2050401e0561955006014460700710030b00c0d01c10002c00c1082041006024000c00144007940e03021041c913403400c5580044040b44179600300034190220418820002c030b0303106080340c00c01d6a0942d941e946400417119590742009040d00a02000720420540810b81d000e02013510605010041c10443e0100d4250700301c9904000440140c42110f041c4d070348030200b07002e0000c0100390510003a03d8502c0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 809972086 1250 809970836 809970851
    0x604052701032402070b0610030f0f02070606050402070c1203031821082a0909071701090209031009030e0a030506150a2405360609130c02120f090301 66
    0x100f41d403003280d500951012003040140d6902e0f04100d00301852200f079606040d10f802e54185410014841c0110f0b500046c10010f8079024103082c11011140c07180c00141c086d510422185010030194036504045074001450320444c4901b502d8120b000d0815682182c001422058131281041051002c001c0d000200c10102450384280031000c5030606000d907244100c40402040a0200080010545c2c010910031304038a450014640f0110b54003040449040000808820b003109804039001c070000d004042c408030a40c10055a14000703a00c481d10380480314126540c1e0242c010806005031014241080700812219501d0350f81e003806501d42c582110700210304281280054800c2c40c00b8500c00090b13662070804010300c80c0c480f243da0000c819042010000340802131045894060100340380d00710304c0134140c0c00720f0781030000c181004504000031104503100742401c0c021a912601ea0582c07032a00086548800325000c0c140070000d80c240505540c1d141c01d007400002c1c6114140316094002c0241000507002040001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 809973336 1250 809972086 809972153
    0x7060203090a11060313020f190b090f0d110f0f04140603010c02010905060406330608011202013e010b0a0509040309030809010306050a080c100905060405270103 71
    0x51104454400d07070303811b03100080c80160030a080c08034603e62000d8280c0546d00b000020507401041c455100c5100f1050010790703540c69091081c120045048152800c000d030486660702c40c2200140441040d008000d49034002c1c41c0b1b9501d900000344410000b41c4100800170320b0ba1030f5415185422154940a5030030f040c80720004074070500c034030708005402202500380703500c4569452002d005280000c601d032203107a0f2019510f80c584501802d00380c14200c1030b440321040c60200050102a4168070060200004048140150b40c0100c3c50b501070610700c03061009680606d40208019001d1580c1443c2d0141a100d00311500c10303c154480d003400c030710860b4a580626603c400300311140344100e900a00084002e101040002c81d80c00241044000505010542ca62940045034003021254030600003680f080e601c00702d00f800e180e038000c81c60a4091400c0e00310142840080f030958803c5104183c0154020b0080410591071400012a40400340070564465690b0742005a02c891007a0580480d01800780e0012045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 809974586 1250 809973336 809973349
    0x2030a090f08190212060c07050d0813020103020c011401090f0e1c0807030b090f04061404020105190210051320102610060f0903021e0607060203090a11 67
    0x407100c0b060020000c02c820031056081c0110400800c90700640303800140b071a2000f00b4051a4800d035424401c16881e44250300b0f025140c262151901001e1180d000c040c49a20240f481421001d941c0a013800b41e51072102d106c0035801000e681a440c3c1980703884200100f1188841d411082c00c0007458942440000b0009004a844110302c144100c0c5002d11039003245111401205240e5200c6000d0400140610402e000314000312011a44418002d4202017080102308843c07040c030302803030301e4013000c0704452410741d0000c0c4c05807007003d05001d000200c491106440301d20030017807010485068031051200e400c0c804401d1041d03c1444000321144214640341c80603014081900c20b1040b600100303035881d1450500d42c103a6116021000b1404008150140c864103184100802800b1399040c00e60325500c40d01c0c0080040080d00815030300001c01c0300110b400c00c003580e00e00b10142d89440300080140384400c070030700c00144644507100008050310b0000c420002e031000c0c040f554020352402a54246007505011040180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 809975836 1250 809974586 809974589
    0x509010c440403020d021201051611060f28020d0b12060c0306090618090a02102325030f03051b070f020102033a0504030f03020f12010602030a090f 65
    0x340c07005000c2000940343c84100b0752003282c000351802d12a5040084280c0c01c1d10011903142030110494400010050351000081c600c030b0712f10001418842c201900d052052680140104181b205c0440041008201c0b6106144980031580c001b150383d69111f50900b0080c107a0901c5c028840c811400c11189aa0000b20340d061003941d144003100d01e19540d03170003000612a00644882d4001170b17070821030302030081c0c510091802040f5100081c1001c600b20710400044000390724002c2c040080c0d203207027a14240f41020a101030200301850054807000d2440044580b59204442c0781c460040e00354545042c076800400c0c0b03082c905100d035414001941c4640154000030310f03404551030310002c10084180400c00ca9190340c80c0b454814415645400007910900c0c4c8491188030151032000d46d8511380b082c452a03888559109120f002005110320319060700c0c00341801d10842110820b040d0002913a10400100c50100c0b40450795185a6081c5545c41e0310000355650842d00700c1e0008688140350202c0e065004201440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 809977086 1250 809975836 809975963
    0x15080106061806050d0b18090f03090d0303090512041512050c161a010b2d0a08040c03020a03060c02010e0c13020d020d0501030b0402010f0c03020d0509010c 69
    0x52070b14903240c070845032039000f04980c0600c16652610032480d66580464101c6094440c0e074084050300b4403442042c140440244019910f900030004c0010a8880e080c880c808a501405d000079542c01c903003011401d22640410a03103810030006404a000f003a90100e010604c02207a81d407400350100300c0d0380c042c01c032041510141d0740c40400703005410262020341810204103108601e1002501540380c81707a03000360f030203030412050070502250540011407078841c400301806040e079995405198060410895200300007590080000107000203060011601440c00155809050554015540c1c280a401001c8400c0c160006508029160043c214001042032300c01c88002c0c10501103803505144200290b01952800c5006502800301c24076802c2c00d032240c14000d502469071594580390501c00108039001c3c0c81030304001d00008402240c0882c0e800209844a486182441541c501e81c100040c0c07a000d4106c0d1000380321a504180c414140705041c411180c0880d558101c0d0034004020380b2018004110074080603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 809978336 1250 809977086 809977127
    0xf050f041b0807090e010e0601081b180f060120030d050601020a170904150305010903090f0b0d02160506040c1412030306100c0503121e0105011e02010204091508010606 74
    0x3413146070701c0e5034885045000703c01d00001d0a220301c0c01c10075041c04c0090f401640b00790461540f00d969040d45071102c42003a40c045480c0e8440803400000c1c0c00e0160405000c01c02184048000a14540d004800d40b0b01c0d034056460001c103400c071201c0d606660f00d51100000c1c1c0c449030708210100d6825400001c104221550080b5495107261402c0d00040701e41d040406460b50090700e8444c2042a1600c00717440c140070314082c6e00045951070702c6040150400031654020000c00b640044200071010100094560700b14a0003405641c83c10528416014608030742c0b4054018011481400208106030322444115041c1250101440d0800c00400600d459007542412140d0401c20001e080da01d0660115a140301d80750600905182046d200e8500e550031100408510188131024000c50740b0004650303002c0c600c5c04400049256040c100028000c004020780318a80846071150342c0c4001c1c1c000e40645003c0d1a10038010401c008006481900749000c0d4424241994a003020200743c4500c1800c56001404c82c5003600c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 809979586 1250 809978336 809978339
    0x1050f01180f08070914040503070b060d021f0f02061e04140a050607120213050609040b19050117010e060607080d1a01020d110c060c010f050f041b0807 67
    0x56803072a00d00540001940d140e0300000c20303110a1001d0b140054807a0300c0c000d18000d81804e000303008840010100001700003064042100003100001110036982e4013030817251440e25a04041103107042c2141c0000d5100800441c0514014200480c0d4294810381d66210b0600490b95142070303803900c6003900d94140010203030404000c1d40c03880c0318919030001e20407400d400d07032442c609600c1420415812011a00e54102c0c83c24018141da1281069003c000030b400e0462030901402e410400c40c0300b44d841658000d20010031161540c0e41c0b02c0d44401080c900240020442d44ca4030392015800c68010f002700350114000b55584603800c049412418160307175483c1003600007030b2956010403c0b5500021003c65011504208089040f84903010340070151045d140801c1e40c3c011507000185c10541d0080685c1c04000c42003148115040f000564444a8081541c4180e03503159134a09450140c0300005500d0009420035080c031907001c219400c003501ca140114244848607003034509c94104070304103205440043d807201a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 809980836 1250 809979586 809979589
    0x60513022104152007084602031303060b03150c04140d050703030903020a0b19140403140303010608060d12030b0604090903110f031314011103040f1d01050f 69
    0xd0081c440070b1401003130120403690f4440358070303a100a100712200d00003c1401c60141a040201d064040781040310040c5c4504400030b400d111000903266062090200d04621001c5402803040b6000450100300c00701c5156140d04004000d080407280c00390091107035040020f4107200401c09140903800c401040384c60a480c102c05100c60b80d4112404603400142040110300060007003007110021807280c2c44107100b0318038600410001c405c043d4071900c240c01080020402c54a00d0407210b20400b109130a0910117002c01050417180381c0101d07000240340c034100c40303e41800f542001002c0c6040350390541e0f0b010119036400c42403143d01d002e41c1c00010086004081e42401c2580250803c0005800c081d065034141076686031180244c070ba40a8041e004565203c1840c0c2c880710051150f40002c110800040d45048004442d4050000003441003584641443d90504553780c410000415850701110499403615180c1c15040400e25170f031f224000b142c42c007d01040181c44640032401d8103d4000070310355041c2202c541e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 809982086 1250 809980836 809980841
    0x10e06030702120d050103120c11100e0301060609090f0c12090609060203040605060f09060d0f020a0f08030a02100606090306050406060b041805010e060a0b0d06051302210415 77
    0x521950a60240807503800805140f40041c00c8002d4820302c2c04507141d45581020400102da0035440f0003004075094800002c280000d44030107031500c06507445132807034210400c01c41d0020784102c00c0396410350810b00c0024405500110b000b055a8448a003088001990040081140c00748018040031600150801c080c02060394800390066000d0240454810030b5030b43c1d60800c81c0d104480484d80e8680d15001d2240d02d09203034030110100d000c00d94001056082000006520403100c58004000c40c1200c0108411526000c000200804000c111a45855210322800340c0f0303600841050001407080703021101c0c06c600344e800380501300c5034651641c0645a00311740700c090241130000d1080e22040d895000004001000c1e5008000a2640404100c0e0f5110748403420425241c06034041c44e41054240c1c1072040e07507a1140503420884141030043c0f03030340d0242d00080c6c0018101c564416540106034000303000344000c40790003c110306000d8100c2103105810800c003414078024250f0f4042d1507560464907100001201e070707 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 809983336 1250 809982086 809982091
    0x801030b0c0f0a0f0e090108060c0d140703060317031b0901051b0c1e1011100501030302030d1d061906050901090f141b0a0903050d0f110c010e0603 65
    0x100802d2900c107540b076164803164400025840019444d401540d0340719405030740520140317011114040c0c917502d400c5000f070703403020050000415020300290070240360040d54001c03000305400c89620481460503620140080050744410b03038004a41c488e105006030509002c0307c0c810bc0002241035002e011400343c0e11415044404401c2c180302040001d5102c1a400568801480050100915100380c10701300b4090011040c2c80c1c40e110071482a07407545201e5484203e0011008040c0c0b5200c0741c82d04500c0d08051078175507112210562103280100210915038040000c0000b101107010034000c1d00058040841e040346480c08400041d0000008a040003d100e5241074045145003000f182e402d0315000082c07041007007039102d5402140c1d5800c06482404550041803c1054540240042c030b10301000c4901c40040e210810300c8452100060b8515440d000c0c6800c1000340d03411a00b10f07200056049409800501c2c4031280070003103101001d40324041c0800184400d900e90301a9282c44030304044805001039a00f01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 809984586 1250 809983336 809983351
    0xc03111206042a1d160c0c031506050d08070203060c18010f0201230415060e190f09030c0204050912041a0c0105070c0b09060c04031b031509020307080a030801030b 72
    0x8040001c264000c11070301c0c1d0110030300b440800c80d5400d00001d01c03041052210319445c140482c41451101050344502c281c4d085a41060031035541710301414000008050640100d40c1c803582c0005c844040c400c030200542902c620960499100d5241ea012780e42c403502035114280070b05801d9043e03200507944100108101141240000b0074943c142e1041c04035540c11000095000d030700c1d1002080144401c0704030340c852811110804200150070b0980c1041c0f0941d0043c804048030307a00340310b1403110201d00d501c100d0701025100710401c009110f501d4000d283c40d9502000380e10840c00c0c075000c5100488080b90301c030002454100a00d103094a4001c6c00040c00380c4034079004202d03150034070902207295028001d070b510410055075950b40f51b94070b5240c02c8030a1072010b08408a1a840701d01007050700342038401202c0c143e0360071000e0b6008240700c0e08450b898114598000401c80b01c2c983c200840007000b02c0d0003200d100c0788210296491a520780a803150756400500c00900015810001000890b030481d00039500441e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 809985836 1250 809984586 809984663
    0x503011410020c09130c050a08060f040f020910030308100b04170a12020a050609060606030a0f0f0f0209030f060402130203090f12041503360c0311120604 68
    0x703d4000142001d200300c800301d850203aa0701900c0100520242602c0290000b1641e440016041842855503003000400018591b0252400304c0c0c107000910308040340c0301c0e40c02481c0c0421403500d80151140001d0030312049000c37815280110700040ca400c0b607840141d40f807240b580f5090603d0030410b281010640c2d40c540405028094546020602c04001c09180358050b070003e00c04050f5518115142260040405812390061404d00880741c0e104030490340c011244180225410320703840c810308020412459441c0829140c40184056000b141c0c000d0101280c080302503810384442c110107da2520000c94000794005141907400c451090745034042c6170408110011203021546c0425020316100900402595030140420200441c0030091f4220f0031007403031031800b84440300c6004940c01c040382d5101659042c442042e40c00401d00242d04190b004902d0f04003403801c010315903074200420000c0a10703417120700035400d410007651900c000046050103a030340404000025540041d6640f0200b0700c10201c3c100706407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 809987086 1250 809985836 809985853
    0x21509090f04110a0806010b091f0201050907060e1804110a06050d0516021e100c18090c170a110703020d020c0a1223010606020307060c050301141002 66
    0x12906005107100c1e0854003007205003030420703040c416031040510340168481c806950050000c00da000c640c643c1103500c086085a02c07441002c0000f80504010b10048010401d00d0210302401641500000e000b000e101d02a6000766403110f4048a0380354291480d55008003601082d400006800301c0003d901900509250303c02c4070521000441c0c00f1095031142c030000f4000f050341208610740b0b02c07a0981050224034801040c59480d600a5101c00e0030300c4c000e4808004100106600c0f0384240240c2210002e0507004001041d00c400010b0904034100ca687c50320910800004a00000c0a105c1d9000350f0000341c840241441e031740030046002d001d009006002090f11440000a614103040c0030f06a898825005402c11101c18900285000500100d080c403500d1411000c200c0c4080703230385000184541124020b01b040819003405002c9820300350700100c1c1c0c1d40c80d00c140090030382d50202c007904406110302018002456000e0044a0350b010a000d0b110310520407584026051800308c1c4c3c2c04e60b407152980156030641 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 809988336 1250 809987086 809987089
    0x6050c1b0406030c180608030702090106030f06030204110a0908010e03191707030203090d0f080a02210106170114011b23030a020c03061014032e0e01090f021509 71
    0x1526030f511610b040a81c4071030104400c80a80181b0001d451007200441c00c041c00e540024050040601c01e02c0203056994072050710a00494201030050764020344240f0403c0070240024009520112240e40014541100481d4850060140803103221504c8000c500704040040684072031554030200c034007030007541508103e6041d0360301d803c0c510074212510010303200e151240440303003003407010103a2004124000440c070300440d41081590780c010024190068481180b1002103540c1181c03009160800f04014000040b1581c1c0440300600c021580c48003200301c2c1c2d0380d0354018095040070062041c0032925820030200030644800e91182031030b02034107000d0041c0d1080c80090410441c5070240d04101c0d00006205201160104481c0104020580081010745403d0005c0c2c94520002c0c022020300c41c80040100d0203583c1e04101e200361042990700b0740841c2114040700710ba11135000c8140c2c00c910701d0918028058584061280c554601e42260308400c156900e0350070001c030103074041e81c11000d146050007502405d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 809989586 1250 809988336 809988353
    0x180d08060f0a05031b18070306060909140106110f010203010e06030705030703110d2f100f0e04020901050f030f040506060901080a03210c2c0d06020a020114040f0b0106050c1b040603 80
    0x58401c23503d0004407641031401c010100c03080c0b40c0003881902d003002a061b010340c094092040c111083d51801701c2c106650450b035981005014016070a40350b0001c0000700303103461113000c0113005910807400c6414099481c01450740f220800d01c8050040320800710f5101c0103050504c92060781c14403d10720b440d0000b5a20415805485104140c00140c4114030b038590464208035002c883d4040305070070404404c8801400c000c1c00d5000e8440514051500440c4006299000300203507561080402601d507160f182011400c00100e134121026030710341c4169000308040341012010181600c0c0d140000d0561070000da141036030f80d2840310400045a822440751000c3d00c90440c85a0704131051503988401490303c0302c403040d0440800b203804054481c0300308040c50210380c3d40c00e088075000f47c1e03003c0e40242c0c480700d5212041e40102041c1d05100d01f03038a120000c204c2001400340c0c0b035030003040c49002240e500b641c82d604215070071b0180903c006600e501c9515401c2c0302490030710105003422001040880d0154981da601140c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 809990836 1250 809989586 809989591
    0x4090209130e1b131407031d19060b0405071215031a10030c0609031a091509150f190b010e0d0807080d141617180d08060f0a05031b18 59
    0x5030340085e5010710512660500071201c802e83c5c0111908400d51030410741d15122900018450030543c544481901042116040900d1038500204100403d10b03009070b000d0000b82c41d01e10046480307480c2024400241c7c0c4800700035400e890308007034001c01c0c3c6c0d000031605419526000c0d0400390346020302d500000000d038070304541401a00b0701d81d071800f11080c9946041c1c80c04103009022080c50200c1801000f95907a00001c6202c0103460031090300416455070207505040901089613200c0d03000760308041085000b03403035080b42d010791b00c0c6510801070720750402001c2c02102c40348540c0c0c40c00070342e030108504100d00d007001c4040c001c0c2c2d018028080c9003100c3c9a072100241d43c02034244035400fa403111480e410b5440c8010400da800910348682d8810010400c8005010529211121040c5442c131808a52510002d0b03030031011503040d10044828a600f884c002415031402200c00a200b2181410803004e6800d044022034104d9002070020025000c000c4c6829204810780c49072250010071242003200e12005030f10a030350 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 809992086 1250 809990836 809990861
    0x31e150e1b0303030c0a0908070303031a09060f060307090b070c150f05040e0a0608030d1a060909180a0f06050402132d02040b04090209130e1b13 64
    0x245010036034503440c2094120150340400d0700400060030074584000c012281c0c0203c50701712207540c0d040c0a000545042642e1b802081c40c500c074212001c4105505684003420495141d1110760301c04400404100400c0d50456a10b42c01100c400700c0b900241c14000c02854015130780b82001c1036131607110068003185801070403098035032a004034000c00400d4184074440862018600e0004000350500380702803c244038078441d1046180c00c80c0d0028002007c207034070043c09000210242c994586582c1d101300007a024400d590017200c0c545884003601c51034400700f15103079082e02030601702c01d48c0d82e10a01c941c00c85660b81c0e80810103019402d50b440000b10a412901d113102c0c0f00e800d0004190826005000b407440641412004803498058590344002c488441101005668a40d009405400b800e04101900882d40491000d42c0c01082c08a4001400e4000e00740e001e0007035851100569203440802c040e600840f417400420380003014025040e8611845500200e8800f6041a400d035000e6400c010441f4150500799 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 809993336 1250 809992086 809992091
    0x21203070318120503031303030b150319020315010c0c0e130302010b03030a0516030e03010608030d0b030102090d031206050303030c0a020d0206060f27090a03090f0b0301031e15 78
    0x2e100c0410340e0b40240500f14400c890358900401d56680c80c2d0b280300c0504015a1002140f180b02c0805110b9040302d41e03140c0300607104c3c2c1111400103150250541050381c5000c2407640f038a54881d403842103031083e02c1c804e0b01484818910840b055005440c002468001a251004541c0004c20000c0030150f003180244542840d00e562104a030070001e0845000c039041074440d8000704024051507070711a040e55042140001880720207626032500b0350b960806103044980550030b14000054100c1c2c04400b800403844a00424802d0f850b041081600302d2041210141e8840e240580342c3c00882e114940d510702654003a58002500364a03140000d1668000700c0c2ca10440e081c001a000744415410702240f43c1d24280c40c0000d0100d0300b042c6002500c065040d0034014003030464044006d082c3c01e4840d0003000c102c1c4503507903e0141c5081406c0f205840d4035168100383e0101c7c940410000740d040d400180740041380d40c0c40c400c2c0c9080d6421591100020840200d013a003960001c840342d0004100d28086c2d040c503002d07149500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 809994586 1250 809993336 809993357
    0x20106120302071a030705180102032106041d100509121801031d070515070c09050103120c0302150709090510050a14010e4f0b06070f0212030703 64
    0x200340c1003410000c003c80413080601c02d12941030340100a5654016030b04200c0c540c90049407004034514042c1e0b01080d10010f1405044a2001400c24080c1d402030409660510503c9014103101508402050b0018000d0b80041201841600036510541c0c01001c010181c030003008040000c44e4180d0094040829111640100070000d580c140c407a410001c000c81036100700c0600341c030071400e880c0e000f0780c49203500aa4444118061045003c41124105030b0b210914412403519800440024502400101c07586140c8100008000d07003d07540000003294140d0003800c8100383c1005105804a001e08a407080c07040703040f408a85850b00d40036a510070b03121080c1c100021890300040104007142540610140ca002980a00159901c400700c0b82c030328101541c00702506100d200c0d140c6862503031400600b00c4008807010006074090f010b030703d44580d41c80c030440c5910200145006a01102d50301c070b034910390100c0d00704a10000698900c0422800310b00040500410000001565041d640800c800310001902c1901 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 809995836 1250 809994586 809994599
    0x20904080c06070c02100309020406051507170c0613050c0a150909020903030a0e0f0603040c03030311250320010905070803070c0b0c0a080f09010e030604021c0302010612030207 78
    0x641c4640c83d46406642c111954003c0f071801d05401356803908060b210342d5411705540719038000304000d2201034640030301c14140b0684032030640c0001101b26010301d601100711640c0403880095810785000360000d8410f944030800740e10304070303000100c0843d07590080789084001981c07607000304402000596204800b01c1c00c4008000d0072608260044c402031403041c400501182c0780001a14105070041c20003005105094002410340790480941e554030000010810082200c601c0b19401240d220303440502041c9003440207020140070310341d240109410152034400c00c0022805040d80410b010b814107108840400480d80000c01d5031a080d885569110540b110030428208203c000900b100c401441c244249699414070700d074000e2040b459070500106210403140c400f84149071100b0f6010300d0f00e559070080520100036507000442040d0200d07400100c1040181000f1603035a118640c001c08003580604614025024010502001e6046640e501d80101d03030190042c20b480c0e000c0e40aa00105541d514001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 809997086 1250 809995836 809995843
    0x2a1103130e181b010c02030102041706100e0c03150d0c0512030c03030703111204051608030304150203070314090a120203130306090204110d0f0606021b120a020904080c 74
    0x10201d4030340d81a0b40b101032500000c046940078a400da0a81c950482000d0300b40100c401c90041e41c4081e6240d403000800190020300c40300d0302e42c004103556058800d50703640c08803004c0228049200e60130480300e901d030028505d242182d00960740440f00e41900b080d44c4c13080c08042681c91040101c11500700700c14002c00c0c0007a1a10503040402c00359040c001310300c2e0907511604207480c0d000141c041414142c6807284840304141400c20f42c0c030400700e00250589185030904103203580b081c1d0400c01e0300302c0c002c0c40500072802440110031079100d15000b841880c4216400e10310003009520003001d2030100355a0b82c0c1c411410380b440100140c01034618070000c180d502c0150604815152268110703005640c020000d0b0f6515528590840088075009100014900c2050002c1009044007a8045014210000c1c0c0701005042d954403549000340d15120400a0544807041640c1d249a00b00d010101148012100340803461718001d0f2020b0000a4801d807002a50303d0b0780802c43d6480c0076501240d6260b00030605140381e41040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 809998336 1250 809997086 809997091
    0x1b0a0204180309090c050c0a030f030b010903030206040210050c16080606090402030a11060f0d0207110418021c0b0403020303070216050d0807060e0f030c060a2a1103130e 75
    0x2a41075400d0801954060165200c43c0702e030144894540e40d0f180403450180e4250307018180b0780c000782c804004951a000b0040001d42c144003012034507046400100b544641c0744a0243c3e54982c0042219491b44e808020b417101d035900c951030800130104440325101034180100342c0d030103940c92410807802d420201c0c042c4c100003000740498018104602000050b0340c0006800071556003014040e2602001640415003a11801a81c3c0940700b20028140710b2501041d03000b400c0303c1d8082d01201f00c01404403c104401c3c0c0b1007103c64260402c3c20210410054685940075802442078408212022541541c0710040c3c1c80b022a000d80261304080204a01540c041c0108692806010280d01c0c080b03081000003410462816000340ca190300100b5000d0400005903c4003c0c00b0006200321010804a403200942e282d02030802446030380142c202041c01c0c03941900070070603000d480011000459000655082c0d80c15880d841da84108410b085032042d1450701400100f00380c003003001d0310303449a03814082108a2490b02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 809999586 1250 809998336 809998361
    0x60605070302120c1504050a1b15110d110a0b0403020c011101050c0301030b090a0c031115091c0c0312080a0c020f30040f08010c05040807030b0a021b0a0204 69
    0x30020040b1094020030040178044c00c034041c2100546440c20b0a524000d1480001809600700000b401c04070203a602010b01106c452024000c05c80900b102e007181c1d808542c000e60021688461900d61041d401010071202c85087ea80480303101d00e070117031034283c4460000d031820340240c0c01c044941c0580313581c00011044620311180080c042130521540c2ca1242d48414480642036081304000b0030b4021005010131810181c003c00201e159503100e0409441010f081460944540440510300e41008032040584505c0700d801404682c44140d21001c092140903c0c1c0070440f40e40c0381444000c00015850507031140f00c4200ca136204180e52070310035620070407200640e46040544d80102d6410340d040200007000d0b041c485294000e0340040c003400100449000c01e100000b512501c1c04940030072509144d56880e412125010000c1c13202c4a131a1100740c07118071681c05101c104d07801483d0144041186a60504c0d00300d1500c01c4014502080a412a1101041e04030301130100e800001d2400e00754506406035001e0900c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 810000836 1250 809999586 809999623
    0xc09050106090305031e09060c010608061003031b05210c0706052b060f03210e1c0c050607110f0406050f09060d060e031b07050d0312090501060605070302 68
    0x441e1074845d9a405282514120710020b922240000b05004050310144a005011507441b182c2c22040300340a000580622036042c0310340c03070004941f600000390300400c407901621241d0320250f004008801503010420251030382d104c0d012039481c100c44c003140030a000d6481141c00c10f46880e4000d0b019420010b65a10000c20030a0920544014072903090154003c2c16008c000302c0410240e0034085400b0300b02c0360380804206940c80b40300006001c07000303208a030940c1d505e842c0b41050204240003900d0030b00001080b20381100840b01082003004844803003940442c0034160150b00c040e655000114940d0050504a50045154401208a00301846220040b91013240c0510200d81450049807004888140c200d04c151002004295030761074900400c4d2181d070f002a0140081c58609205c50368903440000c078460081d07800410071001c1640400c040055170703402020540c04041c1600d007120500b88800401c1034030b680d108050b200081092040400410f910746605445560504010b0305000307190149a40c101c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 810002086 1250 810000836 810000839
    0xe061b0d020c0105040e1305160906140319150608120913050106080c21070504051c02150c1504050618030412021203041d0f0105040c020d0f021005040c0905010609 72
    0x1110009407a4847d028920808410340513080251505010300000e003054500d101011400e41019003200058a0302280911241200350062503a103a661601c20344180c0f02140d840d000007074101c031005501c1d051608011483d1501c03100c0b02810402801207240100c040040c1c1e004c40c5050203440080d002603240e07010001980f400401411607440100122446c100029422a10340580e604182070480c02d101480b085180214007d08981e00a0040c988101c0c104262414500510b0094010b03844d03000c2e00c000042612005020b901e9003094426840d5030103907103800d119600b0030158252081d8054801010b2609004c044240c1d00300324036446c59a96081000140200e0b040c14003010700f51a41550b0992000140200207030443c0981c0d00064100041f00c40c0c1060b0f110120900e240c00740d101c40701c0401c1d540e640c41080000f150100a40440940c00c07411171481d49a00944016114500c41e00683d500c910780c41e0000401c846e01200e00300c6465481c107009002441182c45400c0c0036000c54200841c3c0b85 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 810003336 1250 810002086 810002099
    0xf1507051308190201200c0f13050f1803070c180e1902010e0301090f0b100803030108030406033806041707030c1208040e0907030647010e061b0d020c010504 69
    0x2551800e68082c008d01420040c1c125980321070302500e16a0f01c04010030084c0d41407401c070340d901d54203080e00d0b00702c0f06060203500424a0103011089498199100c10320f022014500068400c000c9110810802c03007540c1e810080c10752203800e21200002004444420340540d040d4400500248102c0c4c1889001380c1c545040080010703003109090070001c0c2c01028401099036184004039000207642c1000e5650700001c0f000050b0321000201400a562403a02e050100c41a108051814110020240208a005191419405d10304645155203c10b40940720740c0c6015140d21004621105210200c1c00985c84102c00300180231003100504050a02c204580020700201c3d201d02003d4000c500030708a84d0300011003c00c89500d8100a00d00044d0b9200009109525464510021540c21007030f4000c65000c03100340c01c0f8405144c0e10a40000400c400c154405001400c00044036035400a1060cd900007100b0402c01d40c0b128114801d25401c82d00c240010070441901e041c00904015000302268103000003440180b052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 810004586 1250 810003336 810003343
    0x60717100614090d08030132010c1403040b0c190b0415090203070308070b06151c060306050c071e0b0a0507020c090103030206090f150705130819020120 67
    0x100c1e01d407860502900c0b00c4001d6030310554482c0704078260b8803c0c3c0d0345250800304841c0c82d0207075040312100007040b150b411203510281c1c0c0d94441d41c03010126154840c90942d41c690b000382c90040c5054003d612958400c011074020510b0340c0d10940103888a003001182a1601c5070041020301c2c0c000000700304042c05001d031580c07801d4000201a0005000c43c5000c0c1446c0700380e107813950101a8458000342201c040b6a500d0801c9115640215402c1d101000b602c3c00141d00341c200600042034464030710901c03601d8048803450520804440d8400446500e44400c0004003007072050046e103000e0f21100c0d01c0d50350340300054600302c2d00b01c0351180343c041c40320700c4501c4c5020041120800c074190301000040e0042900c0d950451301b21309252000c80401d0f803101241c000401490350005030b4a20aa4000d002c54241030806010b45039503e21b0704454005940301000010310051160340a0103000396000090520307030341ca60031003d0400341c0b25107010001c200d90071210001e541c0c1c0700303080280301c0c0c1d4060b101e138990790000e504c5642c0303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 810005836 1250 810004586 810004589
    0x8100f08031e0c03030a0b040e0c0a171905010c02070e070503040b0a021b0a03090623180a060206150d0209070c02030c0607061d010c021b01091706071710 68
    0x1c00b5555081ca4041c4800120704481c200400101640d50341d14066010340d000b03020014100340218600131054415450014114100075001007a8a8285103480b00c0c20440000c0c140d030240580c001e2285011440b050060300307040d407610480020525040e2148001d2410510742e00a40084e602407040c000c4894020048170303000303a0860300c0d1030640d0307841a60700c001a11900d1500003084800e1844101900c60100761004140e220380e8a01780103075583d020840303000030702d0001c1d0301030782d451580503612164012004024408100400c085142d090b4000076596403180c0c2c1c032000c0507030403040c2004000d45070070400001520040750082150041034000c900c1405c0003c2c180b0b414021400f0000c410765600f004030300e00c2c21400800c56565100c030307460010090603045c60200c00301100b0b05c00000b12a501030051180795200c035401825644a03081c5e0302c05184c080054200d05020800201291040c02e0918000c18401d0b1040100050b00300048000e10743e5441c18501070040011000b803002c8848075146920 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 810007086 1250 810005836 810005857
    0x8010e10050d080f040b030f0f09010209060a03090c0305070b07061407051206041e0903080a02251401020301033005340c0e0703020702010903140f0d08100f0803 71
    0x1d40b1404e003140c2854140c4280e03003142051034400710421030300420705140359101c0c140c607004491081e12052640381c03d034080e03a0442503102c02c050200709001840780d0b1114400074004c10a0361000c50390f9864103403d00d102508800300611001440900f840038030b0003903508800311124141418a85001c00604a001d02001140524030402c04200255030300d4001c1000d122032162140c030340032002550600201202e4500b1030114108c6000580070000ba44240d400703c0303281d2620446000c000100e202c001d560101c0088401010480320203602000900c00b55001e18400c080c4c1e001080a00314080c0b040c03038152601c80181650f40e071101c084c02d90744001a100071420502a107194150760104a80c1103400040743d0f0600c002c410b15511050166255001c0d0407581003110300700b400d440b040000c505912070380601a001c00d0740d09500b000052481c418403103280b041d82094800c5520407a400d40d0030128901d042c5000904008144600303e41000c1d40c6100800d8421505024079240c042c200c0d449024000c80c0c40e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 810008336 1250 810007086 810007103
    0x7050d0e03072705071110060b0306100918150b210a09020409110118030804030f030e1e090901150e041119140405091e010b030d08010e10050d 63
    0x82d80c1088142210841100c0f41500c1408149891440108100101c20780340c1010700c64512001000d00c6140709103026642e8204001d0314583e10700040c8007400e81142c02800412540e610000f40c03c02421803a500130a00361703400840c0140011111084940460f0007000001800304540c0300c403084c1990300090310219429801c0269603072484070b40002c19009402075002410b12007a54100400741d03070040004030090301c62100d017032802840c1c5080e030a07980c00010b107030b60801c0005201280c0b146502101c40c61080c645001822441070100c0c6003401c24401211081d207025550380e0252801c006102d5000c003504008100461341100508040941d511643c101c0d20007002c04182480020502d1071080c1d04041d0174070f421100c0406600c0070341451403082e20403805158404140c2c520701401424091104000100309000805400950300b030042034100540359600c0601c07a15645050052a80d99035054a43c2113103503150004502c0002001000e003500703c0485103080c01075584035041c00c0c8660341c03c80c410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 810009586 1250 810008336 810008369
    0x12050405071d040605070504030515040606170a0606380f070b010609120c030b060f0307060302120f0f0c0c03040305060a0506130519020d0b0a0b07050d0e0307 70
    0x1150510410790008141014010500e18900012103010b83c0100d03c5044204919a40d042c0c0850b01400345001c0241240c1000d284408400c00c0d000085400c50f015620000c1c150b591044028002e0051980741e41c40742d0001c550403c02c0c40740340e205c0d9000500844c1c100b203103842c0904c180011501c901d0310303070103e010010107000c0301c50408410a0b15086400850116615006410040790401c42413140c20300041844030041011520700d00c4101080e603215807103d40280c02d41c0d071070480151004040780d80002000342c1c01c5015640420144004015981380142e9602c4803102024a59400034040004c80e03100d50306011049150594581c0e101c034072074198540315039007500b10b203045211303035407028205204e440c0900407041015400349001e00c030201c42c2d200c145069558600140c0f80c0440c2d00300d200a844080d00c0700080340350380007054201c000003000a14140341c04001404000b041e00844003140d404a021800c00608011080d20344800b8100b807540c002920002940d105400d018544180d2a44e00a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 810010836 1250 810009586 810009593
    0x3110d090218192a02070e1008100b03010b0a0308041404020c030a050702031c090e2410050405060c06012c0705280c050d0f091208041e0f090b01120504 67
    0x1c20080c00c0400350801c42e41003c020002036030f030754041c00b60500c01f244100c0030071202010884160100c40c4a800601000c85410400000602400e81440e805540780c0e407a000080c5d4a010010010707520820312580c03214241754441c1c012350001c81e0f825014910410810f20540800030640d11942c40503e040c42d81c0720068404a81032400381444000300840c1403543d6102550049007081c00c2c0e400d0621000101c0da6411401d0041d01e06540074038404051803406001d40d41003803c25550701030f8a03410300a2916940b40081403655121070301e0000b0740d0304804014400351507158001b00c80c41d80c0b100c00441c02c42c650124401c842c0f100c05032440080c0940000c4e600c0c140c0c0307640b04050485a0380e00b8141c0d108043c7e0350700042c1145551640485080c002c10811003940760180702c06003101c81d4141c5d50031300b0140c01c0140f49c0d10740904254044c0c4130b6090a002c000703003000d502035150340050070b20441708100620308100070f4040300042d0446400345040c0300e5109010703640304000c9003082c1615100418152200c1c01d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 810012086 1250 810010836 810010871
    0x30305070204200d0b0108280c051306021b0a03120e040609090b040b0709060e090402030a0c24020102090603040201080637052403040303110d09021819 67
    0x407102c1203085000b08014205a00135441800c0801003030701c0c0e85005503181c1010340201c1000407035240c2004008424236a070b11243c0d80c445c03018100303d418100c0c42d081075156569031000d4198000d000503449407000382010010100319644001c0151801c1e25694110b644103500a1418104c1b14100000d14810b00c000d6a12500503200420111008010201003403c0000c0c00280458090792419040c0e400325041c1c40c46060751504a0b28955100100d1044540420200f98000351050340d01d40304010300c0c0d00c08240100c4080004010001d03902d807000ca035500000b0200c880031541c81e0190391040c0110340c455180c0e00c007180e17489642440c002040356500400900c81026100340c210581d100c144c0088002c0e0054840c0d6034400d40c0303075807080c0605641e65040080c42042c91000310825a0000107000031031a000c809507400c2803013810081030354101307050001010f4110410398180c20f5207441c1d00c1004c0d401e0548526280d100809640e000e1468a4802220300908042d40a0032242d545e0700003070b42e071a810b00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 810013336 1250 810012086 810012131
    0xf0111040e013c05040c1403060d0201020a0c09060602060c1e0f0c15011a0702031221070806040f021303020f011103040e1b07051009020f0d121107030305070204 71
    0x20340b042c0b000b079000f503414420710003c40c081c05000d0f80c54494561403080c00341f060301d6060105001910300e075959131f005205260342e914a01301d0641c454003584800007034416090300050300c201d0788001089854050003c2c0340c002c016200c40d500c0441005003505403054000d18074038441700011420340e150002001c000c883e02c0b442144507141d00840e07000100220350840818100c4c0d2001405101d00071500307a54407028440e4540c02507140e880900c885291040040260030030440e02d000c48131400d4508120030469a904a61b4200054070810402c4000c0c94544a10b201084c007403d0110b00f03140b003040306c4000404050101070307c640914208135007a070b841100d02d058844a801d0a403a16290784840d02c0d216018150350448002c03151036001c0400c3d006450030382d00c1141d00100100904000c2c889500000c281c00707081640c00040a0240350740d6512011844101e0501c2a80340c04000e0715a00c6009240d032141d034403140181d400030003041010030351040130740b01000d40480300000c0c0d06000c89621035441000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 810014586 1250 810013336 810013409
    0x7080309060106020d030e1c03110414041109010e0f0604080f0a021005070302070308130b1902072c10051207141c230f0f0111040e01 59
    0x1048241040401c4090403501c00c0c0d02112800d00e1902d03802d4050741c1c0300940d40461176010308407101d40420781150308290b5044030300300000d00b1100000160000e90058100140680100340c0403090341c00d0501c00c000280c800c00b040c403410b040c14280020540001d08001502c144082c0c038054a642d5101d03402ca800515841d4101c424100c034038280c0c1c41e11420940d074141e11400410245040290180d01101c0445615034064078400d401d6503111300084c1c0124078014286400e465000c2010402e80d0300030418400070f0402c540c0343e400101e20003440c2c4080364004c10360403890410030b441d604442000d8126109a80c1100b4030b0169a0941c001a4803002988459484400521503ca060b0000724041d8103880015a10008024511041c003c00f01402c40400000c0e2040c07041040215001242c0c0380c2d2070103070010725210a01c6001c01001e1501c0c002c1c60484000b500840ea071480c54840034410040c14012003980e075820300f071034030500b04113800d8144a11260041c22002084d100c0040040c82c0300444c02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 810015836 1250 810014586 810014603
    0x12200706030b120102041a03090102130f031b030b07052101060c21090510030207150b040605040b0d14070305030a0f0824010509010c080c060f0f070804061107 70
    0x10358010040282001480d014010440c1e901d0800c4510018000c43d015519001e0840300000070407100603c05900062809465550a2003034141035056a00500c009100c0f90203207609550640c104803c4041c40c2551244101c905000b0401c0040c40d20407005a011100303040081e00c45050001a070403490007112201c80354640d0300700226005030080c1203251058040e40000640064600412410f40700d40c00d2650003003450385a0411a41c5045402401e101031146005030030000b09603164141c04c00d04c2c0319555952511801b8279001818544511801000304607400d1201c21000f0f00410444e500c02000a809004c52108500b040c41c002c2002030011030740035049943c1e800d0b200c10300500004005614070000f0305101c000c42e0151011104151301008021076134818107190000541e00ca5011004c024140a2860582c0011442d0b441c007418050740004c01a00e010701d00900303201e074210710081408404010001c1801249548100e0140e030050b489900000d0704503c84283d11501e000f0404000c20120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 810017086 1250 810015836 810015839
    0x10216260a061d030c0613060e03030709140105210408070b190b0a0305030910030e0a1b082b030f050c09010305161202030a060812130909122007 64
    0x49a510603882400854103105160903031109090304c920858021808075807159021403034180c0d44100ca841114421480050403c005510391401c41d00102d40e41404120601c1c000c000901069400d140d80714400d02e001c03483c1c0582c10130100591080e0a000c515000c3c0c0c1c442c0014104601c1c04111803032142c01c440305c2c00c814600b40c9102220704181c88000025a41098005080d60406240c18000e4950100145003072254010a00c001302c0c00b03203181f04c4201a258034032448040c00a008041c44103000303441c142d03642c00b030109076044072044545c01000240c2c4000726801c0016454840d90003c804c40c041c034200348600043c0110060b100044811001515000c00c0c415a4070702c120050103041780a0720f00b072103550383d120922541805001e00c40d40209440c405403032100800e40d1f00841e800401c07101c0010702c10340c40752802840d000c03128045100e00d11000403141c403500750942c1944010401000f041c010b0000ea50b642e60a03020303c050441d8140403c000b0300104145011010b030302032001a40442c0d0445 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 810018336 1250 810017086 810017093
    0x70311070605070e1e031e2a03070b2d0702040b0a0905100515030f18102a1d060702030a15020a09090c022a280519060c08041703090a05010216260a 65
    0x340d102600e81c981c52a00000e08075440c41c80d045003052400a241c0c034cc1420b0140e00c0e000d001c050441946801c0d0300164113480440d24240c1481446d01a0002e051102200307800d22003072022501c0b6441d4110907200c2c00340704002480b0300c1e001d00c2603400083c4c0400c94000205c003402036441c04952001c00003c41e800c3c0842417140d07a041028949541059089401c0031040740030382a00c1c0120341d43e42e0450040540300706074100c2e003000c400074030240744050220380165086482e1244e05403040d04030b942c0071940001c0c0e039003242d0b40d01c042c00501401410500700641c41014201954135a10b203c2c02040d200c45901d0455007030b07280c0100c01118814043c00c0750031030000540000c084201321001140f500101410080740d18100420303464010b02d19401d840d08c0c100c1c05c20500303454801404d00101c602820400000c18840c15040104902c014890002c64640c0542400c01482070483e8000e03604540c00618541f801070100c800c243c1c100c03000b00d2882107003143c240d200c3e02881025144500c81c1446200a5803040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 810019586 1250 810018336 810018359
    0x71709030a05120702130203100b09060d0e101410060c060209100c0c21022e020705180412030e1002041d070311070605070e1e031e2a0307 61
    0x30a10844002850003038181c4010101d0102707503222013400e20301080601c03011401d00010803564000505c0c6505000300c02110005840f034040da2442c46400040070f620480d0001e002d10341c082e0290015446043c540380d0000131040e85144500e45c200001c0c44190010302035203604584000384040c1000b1901c220001018016a60740f1800716105407140c203000620401da0004122803c0a0b040c1003001888990208031004040c5a02c10907a64038055510425520b00e48000c03a20440b2500540343c0c5524240810009600c881180048002010304010010f901d6507a9600e04040300e00340007a0f801842581e040c80d0406102c48852410701c006800724420840318116649041090110807496480c80380c00c40590382200b1b40d22142d8a0148664000220580c00540d44540705113802e00e18485404000703110030406041081e01981c503205482810f04090041111f00c00105a401c50941c100071180c0d90341da02ca40750000300002000050038080c443d00701c0e0385100224002c0845070f85030740710310b26240e2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 810020836 1250 810019586 810019597
    0x6030402101d21120301181a030115030501060504050606030c0c0115090e070506070305091e090c09010219051b011209050c0306091c08060103020904050403030b1302071709030a0512 80
    0x31074490180321501d00043e039030460b81a0385025408442002c0100c41140140c10524100400c150207030f01582c0d85a1000d1007200003201c1c1c0300300bc881800b450750030301508403000c9404c5180107504190421480d41c884808503600f00058083c5c1981d83d0102c049200d0041040b40c06c21024104001400034003400640c111142c5c01a03004103507032516a80b21f040014078410070030000c002c907005000c03081c410f1919100c882c0001d909003000d00c1114001400066407080c0860b005490000041804041542e0402c440d02680b0b14081c00b030407441c0032540782c00795140201c501503180d5510850781440281d2094500194211500d00280040ca619190481e01c2d0844000360a0080c446c05002a401d0203001400c80307100b2080101c504001c1c030704613904582540c001045541855004c0003000740b652254030a0920a5010350b40008412003d402000b50202800da058200c42d401404450045580c000111224507046501d16982d0001007003c6030500d031a5000141460243c0b9544114000c100402040d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 810022086 1250 810020836 810020899
    0x714010f09030b040201081e0901150510090902030604020408010203040828050a0503070306050d03020a03090911030a0e0a0c0806040b0109020414242706030402101d 73
    0xc5503000e46004840c000c1c203522018101c0b070910400301d40554000c101d60740d0042c00a8501c402c403c3c4184c00e03060300c851826201400c250703569004040301c0d0050300060802a00044500c080803000d2803000030401c10081c05000c1165a000020030300d03e9840354125802029031500a41d00ca180030708003000c0307607046a06542c09503840042c010355501d8070f1a014040400240e101d9a01b0304d511648102d0700c0e600000d00942c1403603910080400c2540e540700c495075025100b039006152805051500130507a41c802c0d440041e8060a2401c40030401750308105490780103c0d420000031314020f02400407850b050aa807800b4001c4902c04c0c01c003280c000e00100384240700f80e005c3c03120101d045c0d0fa41c080d210300301c0c4518400c500719101d0543c56a886858016403928500c1107400415219000c404014482030384280c030300701150b81001c9407204902002203043c081d241812241d4a09600d80b80d000300c0c1c440301c030440c1c0e9802001091a00001c0070100d030303500e0b9802105c026101030000b10b003080b000c025640c0c1540c00c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 810023336 1250 810022086 810022097
    0xf0c0306080c0f0105030f07031104090c030c02030c0d0507050c27150904061a27100806041203020d02030106030515241e0a05031006030c050a1b05071401 68
    0x980c40c904140103503101503d07060b500c543c51035032000c803030990481014210f0010540c941d40c640c440400c50a000d00041c01030000006400c130440703400501160125213441c1c056420a1100300380058001c00c0c004289289801d0881d80c03a002450f21a0901000b1000594401d0300c400002071540c1e58040444540e440341c4419044a0703d80110849038070306d0300031505504c0009580006c0c000b0b009030704007003094044400d0144900640c0300005003d0b0359040780f00b4030440068180d000c180d0042c0101d954002c007130011068192401c046540c1d0300c40e000180050000461a03408800340751190381160100242c00e40110340f256119600100604415198100da08034140800907203460840a2016010003140002d904406012503c40031604410149030140240b43d00341a07004e05000d00034104103040341d50340d41e560303d0092401252045150401c84c10140350601c0281d400d50081e0845540c117406040000305541825009000c840c21444001c04900600c00001010b5820301e039000d10002c1e090300e49 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 810024586 1250 810023336 810023353
    0x1f090302190206040504091110030b040b0d0c03060513051b01080f06090403031805060907030506090d0516141902120115090203150d21050412150f0c030608 69
    0x40400703054a95019522042c00c200c2000a460300c0e07405500c01031b12a800705181e5848040010300fa040071804448040b035107904d9102d1061500c0d02c15003800000456441c00c0299698403001c01d011031501000307201c207966a02281030030419120207800382e540130b0210b1343c03c0d454082e85140e0000c00082c035140890700b03c00c04140014801d0840340d209003401303007080c5074540d15510228043c101c0d240070030345e117880640c6c951004100c0034402d99114001c06401400340a1851070200d02c0c0c1480104074271540d41006460000241d8024125070219400c1c0e80485603540745401c100c940c10b525a030050b4414401c1c2c2c103102c241010000240d102030350080781c10f8030040101d9070b216403c0e515140c0e1107145003604904184a03450709035000c7c40e00280b50410b43d0f1003811140020803150401003100340d802e0482e0200c1c90b81004c04485001a45640a1424904192a0103d0014041c5400380d000b4000b000407046079218800396800545080c17030714401406802c41c8050094000c0603240980c14035030280c03501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 810025836 1250 810024586 810024613
    0x10030510020706060807091b0e031f020d0207210203030708071d060309010b03010b0a0807030b0a02130605031b090a05061e0a09181404080d090507090f15150c051f090302 75
    0xd40d250598000d8090900b20005400b480a1500e00704990f060fa2f0303600b4045030035441454030181103010702c1034010700c1409000340440c0f582200c01e41500c20441d80b003081002511030f400405650080000d0401d00448600310b0b4113480680c94624565403c81c40c00b1040203240c101c1508544102d10b4203400820181c030310101480b29001050140c80340b00d5102c11801c00c00035207400019980b100422000500380800c40316000d00e542507035408240015004030601c4a40f80e075588012403030000c02014a40390810355004101c410805200da5840f030b40010511100b42070008040100d4214030140d80ba550310003484002c0c102a850340101c50380c0c1e11200c06406280c6205118400d100810601060f1540e42c1c0c660f03a498482c5e000310302940ea2943c42d10f500900244007000104041c04c0980c102151380e1101300c800d00c040392001407402c0c2003040e43c000f04000c00c05415568000352019403408101070025410603600e058032444004180022220190880805950001c13824174802c0e0709403100d9a94114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 810027086 1250 810025836 810025847
    0x405040b12070611010219080103050709150303031e0f150e010e181504080711031c110c0d1b06140a12180b0f10030510020706060807091b 61
    0x20030300c00c50b41d00c000c50a00c20580682c07805071080d0b001e0800507207450b0618190034100402c0b9150301c800324400400620400c130090003981c02408070382c0800c22511015a8102c0c511045602c005400e240d0b50304600c54841d0040e850b907016642c2184403d029542498002d4402447c0020190401c01d01040000c02c1c0300c03400c040d2280c102c4480c010240803d4617040b0185403a0840640080f8607445025401d0042e5400c601c0c805106074001c4108035210809800e0042e000d0318a075206034400d0700110341082c011680480a9145003040381340001ba0300a442c1c4106240080c3e078141c050340000503002220402070f04040e02980f254400700c85015023070b501c4074196900781036401c002e000300f442803015031030b050300c02c1c0d000e40400c000340d60010480414480c0c808500d80c460721000d80d000300b514010011880e01010002e85c1002105076000d464a241da104c494890002d001e082421a40003d0a02c0c2402195007108001d401603200307680146075580044c400900c41402403035110007000c801010183c1c06503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 810028336 1250 810027086 810027109
    0x50108010b131d0d051905040803031f09020c0f240f0408040e01120317010f0303050904110c0f061b2d0a050d15030206070210020f0109080405040b 65
    0x2e080b180c1c2c1d507805902c0200240c01c458500c204812040e8040c22001c0701c0030840315400480302c0d02d85555401d804080c0354106014810440280541040b04201c00c20002048a60040c49040031400c0d126410943c02c3c045442580054611400821054100c500209100648078041800c49502c8a9003400342c20408e604026003a91045a4100090300c0c0d0204a65040d88070f4401d001d41403502d501d0344040070001c04280c100c0f203040c002a1031050101908250440c40512a00414009546c5020701f4826041e00d580001070030050b010502440c41d4866420100381803040c1c01c4c030315840d6417840354010f50340e100c119003404040c482c1901080030701c0410700c060031801ca999411f052030011184080d800c955048a010903908190900503007000c0034200182c183c9800560360f00303565125940000f404c0d1900582c283c0e446142000f0100016542d5500f152401da5040e503a8040d141d1070310100340c0c10201d200030350300c6155091850038400c124503440180705942040b601000303501504002d000c840144c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 810029586 1250 810028336 810028339
    0x213171b04182003010c031b140306010e0d05070605090901090b0105041511070303020f0f06150f1212040906091e020c0a02191a181012050f0a050108010b 68
    0x25507400030081002c4807503900c8043d030104800420416850b011900b192440480a00000d030b660320100d45c01c181015510b00e081c082032401008110b06100f00721306610015042a05000440306901c0c4182c1b50b20281030045034004c7c081e02c901c1c5a6030301c03002d0440c0d48505050751003106454001300300c41c1d031140b242d86030a01060307443d00d00702402e28059480078103003c08071400b40003043c100001104d400300510f80165200354090440c1803403503070999180c0400001346451681021003000801015002509800b0f08101c1e1424148482e080124000254160f0000c0540c00740c44032619510082d400104103c5205103400c0048695a0140c0c0d81110034051000d0a294800c074040c01810496070040c1100315080c5040c1d40344400c032580010412603034101804019003211104001205021004024145001c51290320f020121a086900c520380f100c038061041c01140845102a44130310540100101e11902c1001282001c41c28003444000131292030a100c0e0070300d8008140f401041c0201c01035a01d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 810030836 1250 810029586 810029621
    0xa030c03061d0f0c270412050f04140135060a27050a0606020d0f0905042c0c0117040809060f040f050d0201120213171b04 54
    0x8541d14480078044000010b03a0364228550b00100c80d48050084a440002ca071008014901c1c1d82410b000161003440075054655080c1510160f450080c02400c581c4035a0001c0800002c003174003c41910f01e401000d1000503166408140841c022164a5070b1111002c030036202c28500300ca12101080e01c5d001803072101c1c542001d21070b0080c2c88a81c0201065604000000d0850208940760f142001019541030200481e101001413004003060107480b035079070456412041845080d04241000e552006000350310001c00c040c081c1d04503503440c451123740015100003481440002100d1039852070070168005074081d0100c3d000442c10311440001824500b00506864a81111903811101558441c0003002903605120030045602a552a44000c100c000c28019001d40c495050150449065010750406801180400c96a1026030f81102051458480a003809171f92034914064804010010750b00c45100007144000101e41510007054100a1000020a4140160760201040203851302c0d43c0c0c440d0310015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 810032086 1250 810030836 810030839
    0x601030317150916090807050f01050c10051305010c0f120c020f01141803071109090114042001090b0d0c051303060c080105040b0a0e070c210e0a030c 66
    0x44000000781e400240900105030141444010403c6200c00300c920304010061104100039540c0c00c1200203003d07100705c5004142950401c80408c4201d2038080aa40c14020f000c01c0c6221001810007098403102c018030000c0c81b641c20040d12950710031000710340488455080c05446c158051050003920003080d801d41c0d458100900001c2e43d4002000160b07051004c40c010b0f074040a4a00f0005d00510100c1030070222801540d00d040d00f5041076080c428003100480390010002c42001c0b4510350078050303a030401284c401506440e00f42c5c400d40105807200c0e4825190f01001d0400081c030101d044002108030104684c82100001200115043c4180e409442480136040c0801e1207140d2050740101c130a44028101907141104070181c2005010650340122034031526002014205640594210f0060078161005c6c414002810300040480300c00740145415244c03420005180588142507200005030001003030704d04030300040e07c0d0300d404c00152240d8002040c0ca03845c2c0c03076030309040a103105d0040703c0c0c001c15402840c2c2e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 810033336 1250 810032086 810032117
    0x9031706100c0809030109080c031809090a022e02010b0310090f080f0913060801112a0c1002010209032806020f2b1109060a031107050304030f03020f06010303 70
    0x44c4c0000034203035010341d40c454540d400a541e4600601e41c920140c8002c2d034031042c0c41c4c010440c20005a010b018020700c100000c1c00880e5070b0001d151891175038100c03284010110200d00d151140d5180d03210154540400441414420790190712880301c609003a800c0e6401540c1c10a07480080e9940600010301e040c0c41182070801041940c8080c2c1070b07441560b0206450100b86100142c030718408a81600d03074007503480f10108242c1c0e000b440b801c00345412180740642401d00340c190020ba400703c041748520345800300046c00703221181e0502c04080055001403500f165044201c500038001c1d0040b20351a40284100300e51101100c40b41c83c40d030000c00326548001c01d60712250b40e440390060341140c02000c600e00b00500c0f80c0c40004500d9290120503000b0340b0403011070f00c1410400b00042e02c880d2000711210190070001801240c032808100e660780f9440e81400b06882d5000c00c2070100d58031400c400507201c1d0001040200411030480074040d017550195080718801d03841d4003c23660306c07400c080c400140032809001d42034000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 810034586 1250 810033336 810033353
    0x603120c031608130806070f0c020301060b04140301060e091c020118030c0510060b0d020901020c040e0a0b010e0c03040f030e1e10180e1909031706100c 67
    0x3030440301059a04048808800107015038100b6412140010042201c41407128a034420400030f01d0241c000307000c5414811000780070000c1c4000d8404c10400040c1c0340340c00b99102504044002d0140d41840f9070b4135035984400c01e41c120f6049107818841d50800130005080a001c0c0c4003070f8020420840600104c864514034008980c441e100e03008199502d03074045054510700c0d55032080c60240030b601e13004c40c0d03101a0b140942c145600d017a41034454600e008014414007100e4010303908014030f0080016500c00c803020060340307802d81d50461564002e00b03065446144034000308054036490712070141031007140d8030746583c170b014000c046030700712140042400040c01040c40000040800d80c00f90404481da00458070200e0304100c047d95019100e071064042801c803504040d81903a40380011132902903c03500c0419401480007245118242d0000c0d212808030760907500025a009528480751410051121180360140007040309080905860018a001440c82d0605452540a100c0740380d503802d100d002503903500c028 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 810035836 1250 810034586 810034597
    0x330807050f21060702030a0f08070f141608090111120306150c011b0905010f050d0b01030e0307051606031802011116120c0501230c1501061214060312 66
    0x1450181d02c082140103410500041d4001c203102d40c0655a1880382000141c9140c501609000c2084003c004002c009a400383c6466412082845c09100f1200d01c00d41602817401100c131030f10b07182c9064169003400c00203e40000c014032182030305e82200003019990010b40703500a0400d402d4a51100704002140b500e48210f00840043c1c2501d81d01342080c1052908a08552295042ca1060518010540c0320f407900702c2c864070002c3c01d0901c1c0c5440c51420042c0001c1c07c50141c940314080705512610000280d0703009030401c000030a4020101c0ea180d1002d410032030340d02d82d100c00303100d0701c040d0708030394046542c51080c09842c800a40511042e900900c0b1340c1c3c0115092958070b02e0100031800f45206000c820742c0e800b18981c00810308908a00080c1a00c0d0400d4160740c0d420b03501140c18081d550255a600d4412036451454100318001003a0729804415505070900c4444201c081c95a62040700100d01d5540080450302e09409140e0708100114003044000b0100e201940d10551660201a0314080c00800d08010324 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 810037086 1250 810035836 810035869
    0x619020d090b090624042013030b06030109020109060e0d061a03060a0c08040f1506030303050a0c030c020c100905100c120306120b0406330807050f 65
    0x14039040000020200311a0381000803181103100d01c0911203628400c015254002c4d4030300c0e04885968406240074140c489402d483c1078001c1d522110306403211002d480c114244541390f40300041e070780d0001c12020f0b4207181242c04120340d20345a55005c07881600b0140714030184142e040e180c502403142400c00559021440c0078a11798800000c4000707000080c42401240301c82c41084900101d00c001040c00c041c20413800030b00300c140c25443c18a50b100301c00d9000e0300300380c3c002d5001010305842d45030741c0c01c01c40d100c0076010440204260034440000105685940f0480c0b05614414040098101d40142142071b940608584070060f8010720b10b0300501d103401c0c90394803c0c08030181040c01c502c541c0c80c1c0100f80e20031510003a1802041810042006101d04c0d030710004103d82041c541003184a04186100381241e01c92000a8041e281450000302000301c550302002e905200041d00281e1030750b045420102c04084050300d004030804101c40002c4002c40054220161b9074000c00310404440310fa01480595800b0406c41c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 810038336 1250 810037086 810037091
    0x90b03060f0c040608180f0f070503060c19020304090c0801092d0b04020913022a070b070206070f05071707061b030306031704050f060c030d0c231b0f0619 68
    0x501b82520030401920441d01807000f81c1038200480e0310f411301303101056000303a0107070300048200001101c4c40301c02c40d500c00015440f814034034000c44e1000c034554001c40d080014454500020240c00a811581c0d103812100031200600079004d1422450080c0c41c90f18401d0400c00124664070102d2800507003040c403010138064001810212a000011045035003401200c8200364009484062410412000c40c0b2540401c00c5088850111250721540d8904520034042221001700d00c0408640d20042260750b1503812190103610903a440c00c22686640d07031807144203445010501c0381441d11f90042030f51130895140c2e44628a000300d2a44605035500744400b0110201a5621404800601c00031040d004020b91550b0f840c1c2c585080009200181502e80d422a115402c20300404100c0c080000444018503440350340030030702e00c140040c02d640c0850a100e07848a02030302005596059000782020700390b24400c4200c0010900780710405292030f445228081701c159000b620009801d4007200801c00c960302c4a07040c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 810039586 1250 810038336 810038371
    0x50304200d0c081005010303090b0c0a08041e060806131a03010213090e030f0403020105070c181a0f030601030b0c0d020313120e06270a090b03060f0c040608 69
    0x2040a581c201088a22092030841840044000c024064001c24460030800c0a541182c40150800205104540611000140800c000c20060040421580d40181c2450700c5903210140c00e4840582c0c0c0c0300700300c12403030040c06c0003541d103100d04102d5004100191082080c00510321541000d0300400e0071050102417206062103050710f091000300740d00394940320907241300d80c2045079a5066806054404525a0086c80403482c1204004100e6040305c1c0d090800c031342e0714105c61130050807826080d0f00c00491014140e81a0104003042d03000380e60080d5407814030400c400806010040c0c030500030ba441e143c155004100510020708416010780e0400e40c0d40100038202501040c0c1101645d1007100c0800034450010004010002d00d031203c01203001d058200a03080880001c00304945010321094000152144891001c400050201041d90f662002e270201803a161105c0e1b04030040c00b00c29038407038020b2160a000480c0c5900122a48d409080d04102d15480c0c2444c4c60422036201002400c0c0e800c04c0441c2114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 810040836 1250 810039586 810039589
    0x60e1002031c02030f09070b0d0e0c10032415050a11190b0901090b0703150801050f1f031208060402040815070f020d0206010b07061b1e0c0305030420 66
    0x50340d00071102d040380096600c2c9820080300a45940180c40c0311b6940c0e00c40603060007072075218400d035142e0001c2240d000aa0440b11070341d162400080d04001500509802149030207035034582c0101c98a1440350349980d0042c00c0483e1074400300c014502c6030500a14aa4103c00f00c40d038402c000818840120345450f010003100d0f11465410f00862003611100d06540d0000481040202c08400d46d110030020020820400300c2e403a48040c0c550000c0c120401c241d074030040c80c3c5140300301001c0a00604101070081105181094800410002c15181c203209902d081140080c2001c8e801000429240c0c8000301c042100300180007520104d6015200c9a070141c0c02b0700011888030010014550b5030300c0c40701c50190b500d0074481409810081900c0b036000854202148090150760000717051411182c659840d0307940c91000d4140240100140907036024040c244c200070600c465405443c0c1c5001c1382c03100032071452202d10100d099680721003840740107000c82c0060001501003409450481c4562004078284105400c41c1c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 810042086 1250 810040836 810040867
    0x210f0e0c030319210c0816050703030e07150201151e12020604030206030c1902030307090b032707060912030e061b011107030219031e051e0a020c010306060e100203 72
    0x85844d00746907958140700041c582d0251140c0e411000214280c040c100b0248402415803041043c0607041c151103c181744071144e0100105002004d5000c0b90024410060350001d0103420103924030601054800004544504c110444840300d48407501d070200c4484c03401c461000880000803050341e0120003032200002684070000154400c06a103200540d4860350080d410010360208006030045500074004c214641d034010030040c00345e0788c110352881d880c0d64860203920b030503481d00c03101d9400c00c0802411410b0944270002e040c3d07080c0d03155515894001601c448002c5000c002c0240017600180280b101403486040c00070003810040509039980008400001c40c107030a461810461007802c500c00030b401002d256040c002e9011206410b024041c00b10300549005082d420013140e091800c0b91001d00040c0c01502070000c483c5c401c071480c05400c03940300488507207a0b07007500000c50760005400b49000040d2a0361291048006030b0381c803919148403994084041c0003540290b16010001d510040141212010340fa1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 810043336 1250 810042086 810042137
    0x106230412030305070c050718020706020c161d0628140f0a0e0c0f040f0e010e1e04060b03010f0f1a03070b19210f0e0c030319 56
    0x25041060081074070b2500500321030703000b0301c000204181c8040d5040055000b01d5440d0881e40020107504030000b140d46220001c2c0704501009128510016409800d840d001c120070340040e1031407950f05107040d6500c44e010071041c04201d070074060880480005003640381440001c2d41d00c880c03002010b142d5048001c07080c07070402244d410141c07003442542c11411407860001c1d507174800c0c030341c00b03407402e510a0349010210440248003030040900350301d001c2115134002c9540701c150360040c0041064030102030780d20070303150301c1d204021f00440d844684840c0002d140741010b00c031008a244274100b0a0b4031556a651a4007004004000354107a05540f9442c65001044240c001c000b4545a4100c00058440031300309900d040d81c2203020328be4003a40000d0000c001008001041d91103840031450413409600c0320240c2116629441031501188012007640d0700700147e100d6002c1d5400a003840e40070400304011aa2103952148942c080301c1d40342c0d000b0441201800204100005800a40e00704a00340005019031180d069204 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 810044586 1250 810043336 810043349
    0x1f050d05070503190308012606190b040b010f080604110d060521070603150b0f03040210210906021228150e04111f090e0c0301062304 59
    0x2062100d85001d004003440d55140c0300e58035a800c141a64060b20703803a014420400848078065890b01c0300300b03520010310402d0005406551803441c0030440d044076440ae1003003980c44e461801c1c070f400c0c8544c1003511400d103410304141c4403040c07105544c000886001c100140003940081d110408003400b1a000d401030400740c01d9550021940c81d0404050218100021540c04403054090300817442a4101292641c00c0e1210381c58081203880381011b00909890701588a200f180000090503400c0026090203075001324401c90742c600410340c642e0800c403004400d08960030180301002c00031000c81c10003075000c201124840d25016042ca200d07850704000c2078070f00302c2c1d117140403509904c41d20b4201c02c485500d90b00341424504041045486090008141d0081800b0340d03285420b0fa100400e040c421400c403100f011910040c19851504540704050032040c0356800c014000c503494a07004100b041039038000610030081c0c9194103055a1824001300d40c3c0034001150b040b10544400445003190400e00024070103000e8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 810045836 1250 810044586 810044593
    0xf030d09050f120f0d1b09030311010b060d1d060702071a031b0706181401140c12060a0f0803190f09050603070201140a0e07080a0b1f050d05 62
    0x20107060031420001280b5091010f9000058518080300c080e4041d101c0800300326004907103508075120503000520245882280d0581c04045c1190416405514502500d00c07a5075007001c1095801c45090036138034200355180e0b020000f40f02d41825200b40c1c3d4880c154010131071a45040c002200283da07428405d091391402c005800a803424840030035568070144c41c4280e031101c0c01d842d500e8007030861140140300c2e85642000240c00180d4409000c602c0c0c201f4036080041a01c0b02e03102400a203004c0900c3c030380e104010038071542050040c0c10f0080e00c8040487c8103054a0058070724142d02c00c01d00c8001c0c1710009081a80c80096540c002c5807461846005030301a02000303004580e2403400c17980000303c4d0a14002414200542542d40090281d401040d603812505c0541d640c0340ca030740b216141607001d03003100b2014003050340203001003000b40c0f803140e0000c802446080b419078091035160103a40d0384039102ca45004d001d02d40b06c5d03408282c00b0b902038100169121114910080e8a82d1650005084002c030558245c940e5030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 810047086 1250 810045836 810045851
    0x24090103051c08040c121a190c02030909060f0607120c050705040501060e120304120507090e03071a0c0d0e010b150405100e151612090f0302090402030f030d 69
    0x2c1600540d074039622908080c103240c42c01c0d0751120744a4010380074a07006035504006042c20001c406010b403144000e0001210310f0342c5050841da09201c10f06c445203404941c2014a540d41240c008421106810b50103031000c1c13580e58901007030040003101505026041482082000041802c08003403041481059075201d43c848005d08103145400010f80026100e64a40001040740d250010307004007440d4000e603282d006c0308032003251050440c05241d002c2c105004001001204000b00071a0400c2610b113a42030401002103888291941c900400100800549910155650802d1340000c103070713400cd065005041c50040c1e09424034095a00301c940c0d50701c650303440300e01080d401d10f0080805510015159485818103140c1400142402c840080300c0b42030151b10f28104c250364031206901a100d8442400007559002c00120503514100346800646000c080607442c01113182c0300b030741070004a4401c1400d0702011401c6808001c10208080d01c02ca0b491321510304110b4a1010a1000d48001d503044400003400c00b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 810048336 1250 810047086 810047113
    0x1b010204120b090111040e191a0102060108070f062709060311030f03030a150f0816080a0305120628050a05041b181205010b0a090b03062409010305 65
    0x20409000369190b6410440d041520314200ea0507103003240c17100c0c1e4000707440d900c07544030123641e40f00000b01d1038020707509001c0340040ca0704804e000d0225040c0c0a901311500740c3c4ea51580d4507114055409140212480e48070704010007403055080c00c910794020b06080310b011503104200c050719a031035480541540e4985900300240508011800c01080017034029040703000713600f100c2e6074a030b2000825036141c10340d664045200c0304c0001e601ca000a0321421262510040c1c80305085560f89910300400301c2c4011408801043c0403d01043c0c3c031140700d5040d240c550420300f121088000c0041c0050929070400103903030346200210664504c0c6076801098521036240f260401d81800b17428502d1f03400450107107082001a03410424022000e6400c5019440c1800d1900c0610025000103004c036070016400b1030310003d0030410f0200651001d15000b00464036118910b646480759020745a920032110b81c941c00030800103528040700c603203001e4580d2079220344021030808000002d000300003c0c0c0041d1801ea202c84103d9030030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 810049586 1250 810048336 810048353
    0x20d0908030909011e1206021201060c05070909140d0f03060b04050a090c05070515010603180201021b0a090c050d050f090a0f080f030406050403141801051b01020412 73
    0x1818903040a545000d010300040f5481c02010b200346580070b5510422000da45010101c6080034005c429000b07840c14000c0d0600401130340002c5000c1d60217005034000016010701030040915071542c45000b07004480d24150a85005040d090400d5031010362102d40300140c0703003040c0b14800e00e0f80019118000c030149a2030000341203070300c113030410401958100710034051556a884120112125014040784001080b5412100e901609000409906c1803914000700c030308c0401100c2e816540142d5041114408400e40140c03c4c10110740043c2c0903030450a42021100241100b01400321000307001031952a0b641c107a1704049442e208115800190f0114020082040f280125500405020014400b5080840525894180a041c000c100800000b0001d08000a00c0300f60394502e194006655200e00e014200500078010440b000c5000408940000f02c080441106564101c0c5c1d82c0d400589001b00d03510019500d41e4007840101035000d290502c2c2d005008002d000030009826032a1401d40c601141e840c154aa = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 810050836 1250 810049586 810049589
    0x16030b0a0612110906180f03150a0e070510180314031810050f03131b05032e1d010207140f0c010f08040311070e071403060f0d03090b0406020d09 64
    0x2240d42040280c1c4c1c0041d41e0758000e481400044030500c403268420709000030010014000d54030b426000b801c0c03000151290403031546e0312641241c00140300d0989440d03985034942c000c900581d0340c440000d036096885248070b985c1d0000a4040004986006e45e02c82e01c0e140410508190520314a40c00001e0030211040030310801b0383c0f8040c3c242c8071403c4015105001504500560045101d01000071000840790352481d0900c01804cc4c00c02407003c4001100c0c5c2c6580440d074564003450b400b0348540c4e1000f040800691107440204c48040540701c0e01080c0d44040c20004d80424400c05440059102262100c0b1400384024000244a440c1030a040110300c0070700d03410301c4615028050b041e001901c0344042a40c2102000460300d0003890100e40d40d40c1d407454250350b500380e110344003400c91041e11008110b010f0380742d800b2809811079482c0c4600300d082c26110010644011a00390340c210700103180050440c2016480c000059100e4246a030750795450303038542d0041c2c2d0420380c4aa8010b03804482a40380061304422140d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 810052086 1250 810050836 810050861
    0x5030a03060e06090c0a140309100605061309020f07140a1703041a1018060302010212040b0403020d02041103090a170c0d080601020f010608061008010603050616030b0a0612 76
    0x910a15104000035600e113402000d008000b8030018540c942c842c0700c1d8011801f41510880c0c00da071227040503803105540351400d400d502c000600c1c2100c0440d03203140c12420380d05040248542c1d84d481c9404c1848840194205c10641d070700c520b4050181d540011884120b0500d40140c51005160350852418116010750302000409400c0404009101c0440c8000c009010760403902c080c10782907503e44150308030503a85145d0109901c41100e40410b40c0c50717401c0707800480071a0b000b60f0071244000c841e24442e05075845a482841c06070141000200010305110b40c004480c03038001400001e840303240280c41e40107036104a600740c1113500090700c0d481c2000f00300c0740480c440d1114500407600300000315a455544200003140e00c014402d8180006026a01c00c012849910800f80001e02140d80c0e2000000e907104010b48040000a081c0c00b40460300c5a014410181180d400000801b0340380c84180c1c0c000c07941041040c1d290201030b00d40540b200580c40d01c1c20002c0041000384d031150540d030304009807002162031810804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 810053336 1250 810052086 810052109
    0x106080307060b130c020616140c1b060f070215090402070c06110102070b010302041802130c02060c0f0f030408071b0501020c121c11011a010f0507170304080d0905030a0306 76
    0x1c01540e60000f02070f98408820031000380310480400e23050b01d4210195280d456000d4000030380500170a000716400c100642146001c03030048c092141042900c6c02050340300c1e5003d07070007801068098030380150b0f121001d0004484040c40c3c4100f400c00704059074080741042c1d4136400003d0080041c681d1003000c410211401000850800566949402d608070041c44003074403981c0c8500c2e043c4041950300c14480c40282d4000c0c01e0100d810a00590031700544001c0b01758001500031180020076075020340003180c00d00d00c0b40c2c00589241a80b20b541010281c1c1020f00306607501d40d005d1020000040f0103180c0c03581c0d00c1040160548003503140c20002480d1007048800715000e071480c80032003c0380404c0040c6200c0c001e011a003164410f9680c1000c102c0b011002c10b100e0f1621907003071540360340307840071a04800041075500781d0310411058115401515148103d8030014240000c841101104420322400345810500c114101c40c5081c07813140706c1100351072440d1003c2d902c079000013803030303e4155030988036040040812000a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 810054586 1250 810053336 810053351
    0x70e010f2318070809151b0c0a060c0305330108071119020108370f140106031503050c04150f08060402130203090a060903020106080307060b13 63
    0x1454402540c0304009803110a64401240e019038411440d12100b03041c0c1e20000c4003501e80244010034007131003a640207203540203010040d009031007200da9091181201303961051428115041800b46c0341c1c0001c400d50000d02400f8031200018070030b8007031004c01524599020400e03007071455100040321512103462240c60040c1c00d400c62001c01e100124140c0010134201b0f00450758440400355000300704181c14140c1d901407003060301150103001000a081e42d000303985900c0159034068a450741880150311008a0709060505a08901c2c0d144240d0b1b008502d56500204500c00000403180a0b03900303074418014070b040c8400050080302c1d49446100d00e5009220b41c200c16080c03a54440540f41c0b2900742d8214080c0340c0f2040002c60b0704e5506811070004140040d05001f8059540506940b5407070181d5080b8881d411540c542e15041006000b92400b400e1028054042e04071240d072544003d026449003217095548035980010f2151091000d401c03403500601c03011604043e01001c00003603d01e298640079085185c20700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 810055836 1250 810054586 810054599
    0x110609030d0e0f0d053301030f030507080d0203070806061c0b0402070f081b01060303080610020f01051612110703110c06030c0c0c010e06030c0d0f02040602070e010f 73
    0x580444500550610050707950361200403072402407821121035042407006201100b000b0001030b0b542c6e45661325005201b5000f0103100500030740e0700390618080c0c04140c060014000b0458240503112294801d040c01c82c502149965110656080159034080c071903804020814250b402020150f80250111225840c02c483c5280e0090500c1c0580351011001e5070f102006902900d0769812078000d160400455003858200c0d28244c100780e400300000181c080301000500e4403a0310f050150a0603030b0f41c19115541a540c07a0000d00c03d07032031036000c1c1c07101c11030ac1000540250040f00713228090056030100e8040c140038006000140000d1201d008c0c0000a5141c8207c41c85002c1304103040c0c50550703615140105d044805450a10b10f495400e020859000c9400424058540d46050044c02c1c40c030840c10980c1e408101c2c074401524038516403804660841402c20008051610903c020710f00d1004100740080c100942c1d0b43c001d030232a0825003000025a2001005007e0100c410b1085401007507551a10b6080c81d003800c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 810057086 1250 810055836 810055843
    0x31150c080d110c010204090606120203010503070b160209010603051b190f050d0f090c0506070c0b0f2704060b0a020d0c021215060a1730070b010311060903 68
    0x1008580c802d544403000d02022540c01c0c111003120490318025900c69441c0c0c20034100510541c4038440206000049220003580c060007520b04a96005010b0100d09182210782c0360994000200302201910621744940141c3d01e590030705029119a540c00103180c40d00c0301038615500500f610140240100748041c800c414079004c10004540e20350300c3d0403014030f401040156094020070400040f0141040d0400c40650b01c1684510201800b60541c69040d90b5588103110030303403007480c070054070f050078400e82407003411540c8008140810903114104c0c03030300c040803101c010300055031520624140c020f22130201c12882e0074040d103c0500ad01041c0d1030310b09000e2010107503882c031103c0701c550306110001a42e1410741d501c8150b52030541c04004103650800010300460000103a0854840e407042c0610f00700801e80a51072541d40b440340222000400d5012485e095151710b034180d40c5000f10f81908466075020030b0705410302c040e110302d42c42501e01640d80d50461424034070100100ca8202d009040c03d0100704890754001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 810058336 1250 810057086 810057097
    0x30510020f091c051e07121a0711010f0b040c030b0109180f0c030509010e0705060a05031302060a0c141513060b060a0c0c0e010b03060631150c08 64
    0x40762603e20480d034100240407800d007001c101030074500a0b44501c0c09010b00314041980c20100d44015074204644941c820b42101c4006131010b01481001c10310000850241101e154105109060110b50407165000c5142510b0740541d024400d251907003000461410075004a200011050400380890135000000a240c0d500c5446031070703d08007011040d9074400715076a04c4001112070000090050445000c0058007030038040d00c4501856203001030366003078020b012a00006403600248018a0008014412201604040e204002100012000700d0050381d030140203099865007622100d0041a842c02d01c1c4010403400d400542c81a0000d455a05e8070300c400c0c80105910881b100481d10402a03541001801041208020f94000c0e0001130450400ea40000e00203503882c0c810312030400380c9500c0f50861a00200e00303114004500505001043c018540307071000d000788105d2200c02410b0301c0c1c0c1e40f0f40506121540100c056052450449061160740c80c2c5080c0705c008074005060082440105540d8520b440c03050303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 810059586 1250 810058336 810058339
    0xf0c0f09060f061c0c09050906040903120b0303040e041b0f050a12050a02030114101a0d021b12041401020a050c09070903021f0201052512090803040c030510020f09 72
    0x1310b00c2055681030b000b40b4010301c032600040184031800c1802411240003405994480c1352040c0005205203800d001e9010025410b644210014140035060030107003510400240e8103000034080803802000040c9018070a5000b142c260f0881648176081800b40207803608018032558440009004503160894407000700c603603000c001010500203040c43ca040050f900c2c002580341d400c10242041048015201d14091005102075281159440708800340840500c41c1560310600d05020000000e0003c1d405800c07140d1004481c2104110a41c0d580360400350150f00106e58607802003414882d8903034260416460313200a00080500c01e20540b5007a0380d03061750044007031240c40c0010000705813600c50118800110390141580885090f0640c4950134143e0401300000158a840c0c0051030240c60301c003c43c029402d034429040c5008200315400c46100709505081149a5200c00c20840040c00b150001c500c0b50340030340680c0e9035003030641c0707042424038441c401e0455201c3d00600148400f24680000c51302441340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 810060836 1250 810059586 810059599
    0x109050102300c03120a1104080a080f12010801021c05060618060f0a17090c0a06030c1b0f030801060201021c020c0717150c040e0a020a030e0f0c0f09060f 68
    0x60142e034180c0ba0b02c2031801c1c0d212540004a1262051400260618010700f4040014091030a80540f101c6450265116203c1c2a0380080c0a000214003102c00070002d440d103940089103015508076861141c40004e03030058600360341c0011030000c0f0f05041c80704505180c05200342844541040c10004810f80503603003c110110401d80044400f5035190170458200000c1c2901c0991a06860040a81541c121410345099032241d00c0015215180100f032244440c00c0c010f00c0c141085044c440214001e00c1c0c0b00c02014288040f0103182c0203d159000700d825041441800b2868017190344d482c4c028078148042e07200f281503a00511800312400c0c1118180390b401d03403099000684950f0403028080c82c102c100e40c041c00002801c0c0c00c100151410104104580d5000d1140780b605503100e080c400350a910030361090380d46040c0b2200105410421640040500c0200b920380422200340050b4001c2c20040307840d51560159004401002e603c1c184005c0401e00440220b89a000526043d4082502c55462403000c0d0f100340e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 810062086 1250 810060836 810060913
    0x50c12130b100e090a0209010b0a091a0a1d06031603090803010303111204120b04020d0b091006091b05030702070f0b0a1707090504051003080d02090109050102 70
    0x100c26089a00c05a0300058024100e040140920140501500625440304600b0340003a0505a00249024200c0d60180c40320300a82c0c41d18101d68040e8028940100c01c20200100020b10080301c4403060012071003807001c0aa035007011600240c10003406225580402d0a82008031840360740c1c000580344c0c06520003441614004e070000b4214000d040d4280e0081c04410040b0011050540c845c00500c00715007914115010714450710f00c1c15a00d40103a200394644c00301000380b1100007949440c4900e400620151904140d0041c0e030b40c074120b514104840240e029403201010b40b00502c1c0f240284d10003002c0180302000201d0701151040034040078040c002050080000110300345e613100f001103800800041044484682d180c509104d602d030b000385420000101094000140003100c3d82900780104815185c1800c051b14240038040a04801010768616010b5540004041500c1030000c2005805850006a0341d0795448005080310641c4c0d0032035811980320110080400101000303802070200041001c88458 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 810063336 1250 810062086 810062101
    0xe060c09120303100f17030d090f06050a0b0112060302060706090c050d0507030210081302090a1b0818070302090c16060e101d0309090421020f0c0103050c12 69
    0x384591200d624480c4000010000354400c42c0b14200169000b031507811100da1ba0702c0a8004140e2500d072219015500100845c44420040791b01c5500c81d0f0b40304102c1090800541d440300b00072107404640e035181c0d0076200c29444075990f85c4062000c2c0c145000850402c00b40d421900400d82c14010400c00505481c0e403460070b0424000c080040c04c00a01000304005100e800b145401610381200c0d1200301d026071740345100040342d68002c401c103503c180798080c40781d20480c500c0d4007004200c00c009003141a40381e80c0c1f40140d041c21492444032401d00c00c05a129201141040303003c036400021884459030003500300c40424401640d6003009540c014100038070658031003007070301481d800c0c80d02207041c01004140380c8254880030410103d54086581d0041200700301d42c0c4210042d030130000b00c460100c0d00254104006c2030103035140ca010040d40142c0135061503802c00c120344103540540440b02c00902c003d644941c806c40540d01c81000000350254082c0380610050070190f01c42946c80c096a51403001e800a03680020341e24 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 810064586 1250 810063336 810063349
    0x6040e190807060e0304061101050115050715150f0e0f060112140406050f10060e04090503090a0b040312030905030406110c041a12160302040b12030f0415030e060c09 73
    0x100e580003c01007001030f0800064596a0b4003a20440c0045084c0c1e8080401c500300620a2034102d0b28640c640840c6984900000c0f01d099021100458036414640d1138100850211311070154030401500311803c2060400c9044801c0311590340c44014141d45d90401c10003e043d100704941d4010800307092680b103600d00d0b0820031014241e10003840840c0c942020411041c801d590300aa07000b402da8104590346a00c0303ca501502500d002e0050341c0114010090a100c2810681e000041d0300e4001c0096030b04010006000540c00c100640c444400e101d000b00d814001d12901c030400c80081c59160800304104886542c810740c0b2801184603003414010300392502d948070342040c0704882c40490010420019540035241c52028094905007a601801400300380d01e003c4500001d80000d82303c485148d004140f032656007000090302c000d20360f044d000300103949215044c1d0f20400c09006540118400c080d115424078440344c102c1c3c41c90f49854810942004c0e010040541301007400c0d5007085070003461035901c3c044071000c84c20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 810065836 1250 810064586 810064597
    0xd030b0d14030304060b010e01020d050c01140a06050406230402030604090f0f03020c100206010e06060c1f0f0212060f06130608010f0b030103031e0e04140f06040e1908 74
    0x10074580c0d01140090000400154840c920404003000084025001180d000d0310b4411401e02680c00403e010810703900410180000100c001c00100d111034208180c00c40401c07064a0f91019070741c4809080c043c40c6440d00a600c081e002d0315032070030340d10451003a44540b410602c880c1d0302d0213154008007043c2d968a882d0030900c9040d0700441d0180141c4c0071490412102c0140740814bd005020b440405641d905c0d00c4055041250540c1d0300800d03a99003002c0380c103012004094440340d400241000310346858202800400b200c00810a420003408207560078010545e203104503403c1085104101624910306014411500610f09030741d403034445010074000c901d03607109a41400ca802410124000345141c1d0021000b030581ea164000c060350035550700940f013043e01086c00010003044240641038200481d07103094541aa060385032400610b5041c0c2c008c1811541408007102c00d00c0b4008082100003583c8102d165046002510100a1090b90200da691618047c43ca4241500780722100c4a082c48100030580da07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 810067086 1250 810065836 810065843
    0x3030f070318240e0f0a0b102c0619090506010903020a0f06021c0c290109020a08090a0c0b0a0509130501054f0c0206010503011404050d030b0d 63
    0x1200c0821483c2030500307050b880c0d000b0702e07411810100d401083c050040b5000310680089001000c0782e003695568001c40c00c100818050048a40000c00a403034128840f4020803840b02d1646074001c00e201c03ca0804485000070a040d000f0140e00f4141d814500702008041d0403034a50000000749138a03011b004951070f036a25400a9800081040c0103c0d0780c1c18205c080304101ca0503902103807907002041000ca641c1c0710000c140300340801c404601a1010a0802e00d07085800042e803c0c25074010041c0344000c120204082e00481050740d0b020408807085504549a544c010110000038003005126642e0941100e806000303101c1c002c074001c554008410f0007141501d50f420343c01814201c1441c0c0c51000f860040509100340d038411384c1980c801c800c40042da01291402100001f04003020089100c0c0120555070109040130288502c1800d2000300c2c000d01d1284814518150f409401903515040425096031244d802403100c0b0b0b003802d402d10002400000d42100a89003506010804541e40000201c03960150301018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 810068336 1250 810067086 810067103
    0x140d0302100c050c07060305100b03060a031e0201031a090106050a051b0a03030630110d0506040c0617061005070210051213120806040209030a030504030203070803030f070318 77
    0x32044581c1000182194820004c00c84455540c0d076071048003522426509401010045001440301c101d001c00150b40c00380e400760034400065601e94401d80016003007600042e40701c15119440c0d0466905000d01d0250420506401031a100800000391080e01e0602c2008140f00c000518500c10b10300400583d00130a1400d031503030303401c21b40d4150300e59111070051381c045000034500500450140b28500300825400a06000030783e02c480c00318260b013240000400141c40c0ca81025081d400c503999403120426034948204003501e51800c141c03901c032040015603003200e81406440002d5071a5810003a1003298012011a10107201c6d0b000b40e4800c0c1c44510070850b001c0d4110b071140c4005082caa8010008190742c3d0055500b246050795850720310218100b107800700414280000c500e07014114400d04016800000081c0018503103070f01c4c000001c0c50103290745001c601085010904100307516050120800400f88040514a58600044910018480142040103140d0303206902c200300d4140c041003140742c60741f00441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 810069586 1250 810068336 810068351
    0x121204080604060b090106021002090a36020c1023040309080c060a050723011a0f090f13140709050103060f06081b0d050703120216140d030210 63
    0x60780c5401d001c0700c09441560a20b40e1002d104d05003680c41c5e070704948143e0b0141060301888628040039510228840350700004004010511001044850082d4151982943c00104441c11910402500098004940781c13040c8041074401e41c0101c0d00640740014034800107800b240e10407600350788844200311001040c108800300001c040c0c100070741d40260751b4840b003194903c2034550100400341c4541d8a40400144050260000144a06070040d144411080107000c1d203040e29500310342107410349184000070119400701041c680c1442c52060107105815078460b4441e14105154110001c009040c8039440302c2640261018008a5284012054400010f0f540887e40d0740c54100c02401083c0819603041d882d183c0324010703d445a1040b40202c8030048042c12214200442c0c4c81e1514070707016810b039005410b112080300080d4040c0002c8002c1e500c91003890f100046d81e4003000389003010101c1c610800c20140c071411b2021101206079651804022030703a88000f00d040340f5040381400040e903c900611400d0041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 810070836 1250 810069586 810069599
    0x51f020307090b0903030406030f091401061509301a0709060309030818010f090c09051006170601030b031e0d0221090324011a090609121204 62
    0x31070140032035680b0601d28070b4035406011403a2044182d000e905a008200c200042e40c040c1e00305a003401100d050000d0f403400d0603180d02003080f001010b9541980d6480b0002d100000800030540200d0101e858440541e0741000016011595a011804014a00c145418080c41c0c805607a48840300c2e8012140e44000039889103010251409880760008a01c3d100307004100790b48070348280701000d901565250050f132a100300140c09440614815180342d52200002c180e100b04602641ca0001e00c43c03810f0b4100a40791150400c21a90007900c0d600383c43e80c005508104a43c0d2201004201c095418108240c949400006800a001a182c0d69806018803900c1c202c45447c5526000072038a54881503480d0065503000803600c034501030385012072804241e10903c606401c4040034003405103000e0200c0c0c020742000d5083c51146100300c80d04450b50724413400103001c480101030641000e210f804000358203050a00c000030f891400b50351446070003801140e40825107010104001c01501800140740ba1795581c5940 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 810071942 1106 810070836 810070841
    0x60f03070801020403050f01050a0e060130080d0b04150e04050307083006010819060512030a0e030d05030105120c03030a031b0801061209051f 63
    0x18800310307403400c00740700404c0618000e00080c0f2940003600d1915081d248020065a46a41003c15a20b089a80002c0860550f00180700c140000d807918220045007030b40300f4502d06804622002c080c000e00030350b03c008184a001c804021312840156806010640390f01d01008001c100c0d1902c010081d41004004084e0080d10070f0050300d16008040d2034003c1c00e900900c2001e1640301e8190303420008103e201c923a42c402080c07850a2810a450030000180074000000d00301400390800c00c82801c0c42c002c60354810406024001d00300c079007044800541c40d5598001d4800320003c285081607440d01d6103800a0101010f4020759162461a806e020a210207e05507624010243c42000e8000b4083e41e8180094400501c2d207940004076180360704132440c240003130b005a4405000b4000014801c0c980d00c08007100410809130004221030460f45092454110504403c140e05101180f04090100d100e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 809892086 810071942 := by
  have h0 := BRFrame.cov_init 809892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 809892086 ≤ n) (h2 : n < 810071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
