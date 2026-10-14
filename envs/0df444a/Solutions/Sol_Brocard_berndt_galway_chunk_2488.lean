-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2488
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:51:49.107207+00:00
-- url     : https://prove2.me/submissions/d19bff42-2d64-466d-9baf-7e0797728a0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 447302158 ≤ n < 447482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 447303408 1250 447302158 447302173
    0x306090501090b072d090b03010315110703050f090d15051602120f03060f0a0b07060606050c0a11041b030b1c0b2805010605090a05040605061206060c 66
    0x1103015070200419034003841d00262a501c9040c01101d11031001c000c5034203069108543c5a40700724080c8028904d2181504141200940d14080d511082d0001da2065440c00314502004c000c0060900480c840501354681c0c192401d900d556010b080c50181c0040340c8044140031581c4a800c2d02c400f1075142145400c054048050300303041c0c1042001e0202151004420310f56201104946400085e001003501c1010f49414240004440e035020f40c0c4d0002010141d100603840d1269046480d2030806001500c05104134654170289403c004040c1c0d2000e500100030070004001a09840d0f0001c078201401940c40064552405144400038000e8082d842000351000d60042501c0a0542c241d4004800c0d06019101c2015080e240c10300d48a100126120150048852100141c50b85c0c1078074030001c0f4070401c54540c2c105410f9030b184949044890980000307001c2600043c5110380c0303140c60800030000b400215400d028807800c140104406000d42524807403113145070000314070700381e0b00c43c01501da00c901d01c0011211351 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 447304658 1250 447303408 447303413
    0xf250210050a05090f010506030a200a080d0306080304030c0e271e0a0309031403040308040e010501020120090607020121140f0105010f0509131508010e0307050703031107030609 78
    0x1043c05039030390841480b0300c03581e0120748a410301400d841094003d001c2c04030300c8450b803225008070030456000001c0007003040440c243c42d5580885940a0306035403005042608210601504890041c0c0003200c1d03030340c000e102c108002802c031490401500d811080101d11501c0703e80d2090030700c03d05910b01c8c5d6050034210403841d0007500b000600e0010000c0079624241d44220000720030b03846e02131541c00034000620001c001d0004c56107540c0d041c900b0604040c00c903494140d80391100b4005402a03040510f0400c280d0004200325a824010350300071650a24254403400300c40340340000036114480c40903002d245e0200b024800d581c0500031942000c0d000604c0000c100d141180c004c401400786c02400d5102c40c01010205406081303600440c0c0c103071407041e140c60502030307c060826102500700c44841a802455002841c03400d0741d085c040c100c003600000340c060300030f2420f1488080c03d40d01c0a8051070007541c4140102000b154001940c0405c49030141070540782801840b6109081202e01d07000900101d0608905508 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 447305908 1250 447304658 447304661
    0x31104110c0703150609021c050c041d1b09031b0301060513060602060c0712030b040b0315070207081506040b0a030b04050c150c030a0e030c0d0f0203060f250210050a 73
    0x20107000f8003020032801d906d078000d510407400344103540140300300001d0204507007011581c4119084042881c0440c00e2655903904500d81400491003448400740f07020a1028075018501c400180901d03c03000350b03040c401001c0100c0ea9900c003c000c00c4c81001c5800425901030703202035100030301800002e00340d0b010034920b24a106010701030a01c54440107118200004a94504042c20307941c00d140c0c0601074030050041c00304220003034030f110f225050380a980c0e6448405281c0d0100f010340000701d5140c1c10035410349001030029041866692000d060b43d0006240800c0002d11881c0440c1c1c0100100c0b4000748034415000440c4100982c1d0308000d00c0407103420140001c0c031000242450243e07008407108851440003d2016a183c0100c0d8000095a4828000d0040b82402001c000003d14006400c4a54140c40d041c0000c802e0b21000e48182c6103090005a64020b500b014041e00c1da104905030300300c1d4007505008001082920b00c1840c10000040c461f002e886d5510310901c600c0542e00b00c0c20710706018ae41854104c050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 447307158 1250 447305908 447305933
    0x70501140c09060711131b0809060603030406030504050c03030a05180a06050a0305130203031b1005090c2817010b0103140a0911030709020c070609031104110c0703 72
    0x162040c0400e400240320301008070807034080d680040c0000d400c2c01c1c03c0d82d0f541c0c041600050b4003241d104103065803450048540f80700356610342c0401c50580c0c000e803a03041805088a2000b9052410b01e4100204114468a00004640c1260340398900082c2590712414040d0130180a8001242d05000c001b03000b00c0151f5001001d00319aa9995580903042680801001400a00c501c940800304005000b5007200d18040c0d8092684410f600390035500f0741d0f045a000030304540c01070509002d51080d030a10420712001c200030000002e4281c800c100401c1c1045030300300c3d550311400304132036208200e0500d51449099444880305c8120081100039842c45441d00c8400c400c034285c001080005600c0e10100307118a6100380101800c00e0010881c6402a80301c50b110000500001d01c001e445680100b103c1700e2540c0c60801100004107011600161100b41c807031080e038201003ca0380604d04202c440041480450703a5010130f81059081140c00040c0c0c104805a1a03a041c016500d07104800d019080c000400e110351405045c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 447308408 1250 447307158 447307181
    0x50d0207060c0f060b030f01060b030a0c030b03030403080f0f1317060f1b120a09060516120b0f0d0b0402090c0a0c020f060c071710110d0b0411070501 66
    0xd031000358a032041150141c91070b103805826000001d06160201c0d00c03581c001c100001020303007500c002000c040c0400d42500d44507407144c8215a000001c005109002e440707011001c26040c078080c0144242039001035501d0245000180c52001c0014034041550a044201c0e81c241d01c458003103a40320040d80e000c102100c0e52510510f4508281d004035809146000304105100c0c603103000041282e92140d25040744500d0700400030a1035008c080000100c1382a410789250b1003900006400718581d094ae140501c2a90b1001d402d0390322100b84024201042c2d83c02003119144c7d03941514000906c0a40c40c000108a00c8903035134060381144440d1066018010354045591041d40280c2e40c07142e00d81c565000c080c1a6120340c0e0a0381000806600b240001864a83c001d80e004441c0103002c81c0c2000182c9083c94100826548554003208070b0f000500b03000701301401a0040300c40c0700a0100446a0000e0710f0300160b11032a05400001d0350380d12190a0135643d25402a00d005100340011612481711b80707000e0b40240300d03080c1039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 447309658 1250 447308408 447308413
    0xa0e0c03091207150c0509190f060c0f0b0a1104090f0c0503070c0311031b030705010b0f1804061b020109020a080a020a120302030d150e070e090c180904050d02 70
    0x74030020610240c1100e04141c2d119810b1581107244d084c044004101d0450402c040080070461800e85542e03101804134070118400580c50001d18001c60b80a07441207660044d0240144034070700d880810401c60400c40c141c9d401c8805005160b071342842c0312009203140408540840008140441c005020368000d0502c0405440c04209220300c401d425036040c081100c180002402c10640e500020f407141818100c00e000c0002140c2c00c101d581500c4040042c2050541e4680d170303101152030001e1241c24042d0180e070a00680c0c400030391144035804203c140e0440518015100712a07000b040c1004190b41c0440200e8480d00302407800b04460580003070103013810242c160320030038858001040810001c07584840f1b080d401005058260b1610780d0740440c1d05a041001c1c3c080d80418031404003403e045010340701070100101280b05149007000605211b9980180c505d400300020000841001c3d00ca4020064000905004040c1c9401807400c03801e00035134010100c141c004281c1410b01c4100070000680c010b10280f81d809 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 447310908 1250 447309658 447309673
    0x5180114010e06040504090f060203040f021f141615053c0603100c0804020a06080f04171c06050406080f06160c0b070f020c041e0203060a0e0c0309 65
    0x460341c82c0d0076481d10ba5030003142040100490310307040e80306003030a91141c08001a402c2d40b50b100e0000b2a00202c50642d05071040145210841c80c1c10440360800c412481c03004801c01034140c0c0020400c10134110407000c04d12000a0070482c00742c0d441c084142c40b9501401d07e0800402c50010400a044262000c5102040c03610007843c000c210f101d0a80d6440300c0e044230310958030380c50400c01703801607101400e81278041c0116460482011700341c0c0200361070b9203400d84500d8282d050510511800c5091581300c181004807503030038000b112a51102c866007040d044103610541c03070f05400401525204501c254070005014444c16921610f06070018021100200d1b81006016a034103140381e281d1204c04031541d41600460005100c140e52001e40c3c0c60800c07a5890007a00700700d01591461180a01614260041282c1c01c15200e00c6941c100510070070440251810b04c8000d602044903000101d4a1a901e0001038001c000900b20b43c862140450081407030a04035102801c200b60f10b1106507000307841a0250303008118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 447312158 1250 447310908 447310949
    0x10b0906060f1c0603020901030f0b0c0c0a26040f0302240a0c080426060907060e12014d1206030f030d0f14011d10051801 54
    0x1042d680c030071600e04161481c080c21980b0203030440245030351160b81030342c2c0c0e02c00220151b00c46a03c02c601840c0704101c84001c100d201c0c103140c252080300400c503480e040e1040009800c1c900b000301d500c0039000d51010200140214000040c08819061b440d08800810003050025800078a1011031044074000c2d1249010b10003207031441c1c402c101001a080c0c0401e0010001c10000c0c901c0743c40300702e516500907821641030a48071500e1030000b480b420307440802110050211a5104024032406800940600c010000c2514150020b880200d15500503442843d1019808968680c290082c4003212444800082d0780e14543c0001502001801c9200c140c203085e03d4914005101074900c038030a8807810070165400c180070303950a004140d5004000980500405804200440003040548407940707041c000070170141401c4041d401141da00c41c0380c0407410500c440040000d12103c8080c1220900820a940195980d440081d91040d041d0350040303401100c0d01403c08801115403120034142c6662000c2d03d0441074001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 447313408 1250 447312158 447312169
    0x120f050f1c08010b030f01051504050402041418040b0105040c0c0f0b09070b0f091e030a080d0e06060d2901080313050d0c05090a060315020712110c100c14010b0906 72
    0x45034010f1b0788001c0d010061040e807a00b11140c0307501d40b0103001900c0c41c15407200046801c0c0d030000c0d8000124502264120f520518024500074049643c03260035462601d03058980c2400f841041c40b0f2913025a0f62804401e481074800c450b02000315420000003940a4040e29003449100b1013295200c216006850020903a2044075085641d10030f050b0000307d045c80041e408000e0302215882d0030800010058080641a860600150b01c01e1801024516102c203001c441840907183c0904d40182140c014500300700803a41d800c04051031054100f80035261a0707a00584004c040c510f2551405c44550fa0180006968a000801042e905140e0100310001c1a40d50080c448004c00c000c0c4018461041c0032800d010600705000500c1d031240c40c041002c00d0f8541d89807541d0304c014500308180211644c000913000180680700d226200450200e207444038403801103103c02501c07141d9154845205000084401130081d11442c1403401c0141c00c81081c1c8151000402ca03a4000d1070814840d50085038074030700003812072406 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 447314658 1250 447313408 447313411
    0x90305010e03191128050d02070303030b12031b01150803131203020c131805010212100302011d01050d0f0f0c05041d09030f0f040618120f050f1c08010b03 68
    0x81c04001d007160808000c1c911700003402d80701500e461440007000c02c004207404106001403180070350040c09285040d805c0003000d580c8000c0b083c1d4003583c2c400d03004101d261400011142e280c102c208400250603021803075640036240070201d000703800081101c0031513070800120040c040580503103602c412035503031070812541c41140380c0e6000d0056007085441e20796a041041401c141002c41c614000303404096400340341445034803502c00741c0c2c0030b03075012401010100c00da00c0515000500348509080d480e186600080c105118000031640044100b820511107900400940e6080c0416200900c4004408140c9034000d04440d2800c1c82c4c10360400008080c440d001780c0840b0144c4110a440d03040500e84d150b400c0000700000b40180c0300c90700c002c00c5100b440e43d040d94050451502c02d00c0c401682d0380d1400c4401072046900365000c12885a841c0c03010401d04940b0504000000d902c01301841384801035091182c10403140000c08010383c010a41c0200300d482543d0301644941ea103544558400ea602c135001d27002035010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 447315908 1250 447314658 447314687
    0x4050114040b01020106090e0a0317130305070602091c0204140405030a0f090e130c06050a05091203090a0f051c020306130f050709020d231501090305010e0319 70
    0x105200d0400d01401c0c9500001540c0314180000b00e51155a100380404a505100c0109641d0300016190790406134884a081c003041003030305c0c07030840d1760402001031403d503440c000c0001e05218000403c4d0003002131680550700684401001a00190302040f00c10308500200ca000320b120303d14140700c0d00326012059110a026030340100003141480c2030543c0a455100711134460f0f02c18010b10040004290642d4070fa060303c140004c070484800d65581e07181050394411039401600902005101c16420242d1100a42d56000e40c01c03501d404158a00103115821445200600781d042807120a004c9000402c4a450340201c4d4003e44101d10701da07403540102551069260002035050300504081481a40d010305003800c00c0340100c4407000c0d2108256525441e028003940031210710307600401d068940f20340d07a205417001c160040443e130407541d00d404210ba0000b04018140395844070301d801400c0c503e03441b0746030810107035500c50001c211160741c40201e00e55030340094411801c9205151032545010384260301d0540d4000b03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 447317158 1250 447315908 447315929
    0xc090303051c0e0a020a0501020a0803190209090a090c05040606051207050f0307020c09060d0f0308090c0607051510050a0603090f120315050406210c030506071d040501 74
    0x1425030340c003100c541d0702070b850341c2103000301c0341014001d4a280b40c0324550305203003000d0062054880510601c00c2c2c0800d80d1b4481e9056401502d103040200e1110000c0300d900224034a180ea10142c800f0807110000d000d448007164104410343c04016042d076850b4400c101050241e000680b2507a600c2080100ba01d442b801090000340082c8103100703510340f0b050074640e001461400e14904060300c4500e034110036003003101c240e00180e015a201c1e82c0c1d142000503c1c10382081f0b06542c402d0001080c2c4d1106841800000c00040c1000070001c0018410a4180130310031100100400a0381e03250000c2c10705079515075070b42e41c0d003031200244400410102c8d600703001c3c65002c603000038045030700c05807412800350024280000242e402c843d0740b1803540d0024240c03440d1800d5031120381e100001e2030032445000b2440460140c001c0340c01185040414840161030b1450b0400000550520030b079144030310721300380000c2c02c0715500060003407041d0b5080c007000c00d40080d80c21103c007011340103e07904003074030500700010789600703114050f403c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 447318408 1250 447317158 447317177
    0x61b050a090f180e0f0313090e15040b04020102070302030d050c060903070f081e03010312110a03120e0a0b0106050a02060a141302181810050f060108041a070206010609090c 76
    0x880503800040020303164100307840403017411041320340c00c40e44001d10491b00260f0445082c0301d142050703c202e244007407880c0e00401c076000c100051440803001c00341003c1c0904101e8800501168401c02c2a1405540d000d4282c0789400d145000c054080d03000014a4515406040300142e40030a000094500da590050041007206169448620a45d03008141c607220021110908040103c0c1c4a070080d8000c621903a010011021100002010380c150504c02042e0f681201c09100e0200c1da21507d01d1050400f001d5000440d40d58440701646410300480c00188484100000013a983d9040006049020195003e40d180c5a403140009011144444480301403a035102340070400304040c0c400c205007403920280180741060102140340c412103000300c1d0480c40f01200064884074504e01400300886001010105010a081680d510014088010072150400440b80d0004041c01019400e40c8092540c00c00031112a01f406c100082d11420240500300100782c1e410300000e03400030755109201c81c452160303a400601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 447319658 1250 447318408 447318449
    0x5040b040620030907061205041a22050102040806010f06090e0c090310091502160b0405122101051f1d03010c18050a080613061b050a090f 61
    0x2001449911680740a880c542d501e42c80145100640c0603030304030f50041c008146018001407403580c1c00f8050310041c07824241884005440c40e0340781801000c203228044041c3e80c0c1c0f007038000b0400030042c6002c01c0740c000208203207062000c194001c2054035400e500b0b8072910380c0c9a500c00c0e45d541115106660008142410810410880400150b0030160b241d0887d49481190400a450403012442e003004259491580c401002141d00c0b90b11500c2c152a01c00f50b040c0b003060040c00c60500752000000d0550241000082c0401ca41032040c09014125440341c40d84400e09400c903210300c92403440070b40c92014030640001c40e0920f00280c5230301104250100c500c0900e0400c40302140c1c40d14501c0000c0c0d0001185080030483c45e43c0a0007900c030062210380d0b85d411500c4001080e6091034419611040c00307002c500601f8400d04c080882c080da4403da50140046401007a0302c0c1000051040d0200c40301c0034510100c00c080d02a5124008021091460b40d07080150b545801108840f0b0b055032059209a400e0040c01e50342 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 447320908 1250 447319658 447319661
    0x100f0f0e0102191505070315030201050c12160302101e1839141005070203010510090e0f0c131d0c1c0803151f0203180405040b0406 58
    0x42040c0600c180d0b410f21801212035404650394240490b424500c0c250104c1e00110a4421164031400519040c040b240c902038501225141601000c3e042081c00528042c40e900104081000549100795240d0341d0906034160b1a18075294a80407001405824009040c8036010300903d007003005840b15660980580c0e010182c018580403401c1404003814513045008518261800f10001c1400103011201249211070f1060081000c00700c145a88580c044c14010504070000494040c0c2041e6249048114001c1081e601809032600003940766085c50200071250900c6e580d03c1d001ca40884100344100041e8030103650315801c012244400b154008020884913141a2001400500d800440000c08183e03108035140d0211001080f12610740c8250b000e20740d5802d00c4075003250701420300c07a40e4028030798450303584a00c140300180240c10204c2ea07010783c01c0c103c0e503141c110a0180c052244464850304041d130101035102e400c003001c1c5190b01c01503008440118242401460f2059510500944a80d03507240d443d0700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 447322158 1250 447320908 447320927
    0x90615040f18030315050a2d0902130302011202070f08030c070c0306090b130c0909110612010612020f03010506160507030308040b16020c130b030a11100f0f 69
    0x41805441c2c160302c50210b44940381c241516400313550003040911419482c16014042c5030302041c041d82e04042c04122100c280082505039131455400000010752403000b494140300d954000c95401c0744001410702011015801420403603100303072280103081d8540c4180a089000b428070103040001500c245400143c4020300565112443c68912070a04682e0744841178810f441e0740040343c2c0b8030b0362200300340c086c00b01c42e80c00154450b91052104103100c81981ea00030000c0003520495542c03940b10f403001c00810042c1001c15214a4002d40155212740c0d9441040c299103100384180c1020442c8242e06503881e902d00e000b11500030b051aa0060318607441e160900615a0040c0200a446080f05a00d0350000c1c4060194100941c0255070700b030080e08041c100703600d1201001d4400721032480030801c604003032074001c2148000d5210842c0c0e20001c4c0b0074511080d1001c2c05460400580c50300036010b461007000050121212616020ba51103200100c07010000d4862140f1084600d003c01e610080140106205401d0358 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 447323408 1250 447322158 447322181
    0x50d120f0201060923092a0607020d0303051b040b04031506030602030c1801050a0c0f02010201060f271a1306030203030304150c090510032007030504030b09061504 72
    0x151255074521402c211a101c548042c008107500d005601a03410400d12290406d04020240c8656031403d104144041081010ba210018110000e109130b0b5440d00240d410381034000d80800030b4004030303241c010014901143ca0400e03102c4448056058003510b08140c5054403032a00700f03603241a04503103c800d4240308980000d400e158503040d0100000c1e079103001443c000d000135141076482d44040300748098142440c0c41a00d04000b0107003d403800c03103135110005480c0303560001c0300305c0d01500032400100d01620103500300c0c1c1d2060003010380005000c500c03260910a20f91400e010130705102202d445140940e00120010614034180302c0d01c0314070714940320804620420b5405400034a00c1d60b0303980880d095400c01c50302924180400c0d9510390b4010100d010b00b00304200035260400c0300b94240380020301e0640c2000c1d034a50402d9a80c002021000407441c1c091500900380800c2d05403511030504d002802a402030004654411602000c41e0803090f00089850180d003015034418210f00303841091200401c1c040152 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 447324658 1250 447323408 447323411
    0xd090b031f030501140405070b03090a02010e03031b1606090e010e190e0d0e09040b04171303050303041a010e130c1d0901052d0a1e060906050d120f0201 67
    0x100040f0244292840245000342c14095031505d4100303141055500ea0007000c1e8920104100039203201d02182c00c159103030742400d00001500e0400082407450080030044845c01410082c00c6081c550f0000b40c42201404540040000c03e8071208203c03024501441032848402c11b22005100f09030b01c0d581c0319940165502d02d0060003983c0700c81140181c80d01c82040200380e03006640030341d44c49a802000d100c1155001d83d80302d240f80c01e0550f21823112980050016040050310054499400503c0c404c07a03080c510002181a2403946070f0070119181d80c42a50100d51002c10740d9280c0710a08800148a41280c10500355008550380700c0c2c02058143c20105000c5441e1a024800801c500c1c44807005060060403184201610745041c03960036003113903805410855050709001010448803a403203c60b03142950404070341d141548580d003d039005000c01012000d0000b030401c00c180208482d59110900311042c00c40b061000303907650f100303100140c100c0d90030281400b07180d21842ca001902800b001d01408146200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 447325908 1250 447324658 447324721
    0x92a03022817010f0f060c0b04060c05210916050a061202130902030a0608030c07030602180414040b0703060501050d240f0303022a100516030305090d090b03 69
    0x1d0031516050b00b43c10030003840daa5044180011030801041101400c0c6500304071008507101c0d00c134035200050003040100030380d03100d1003044991403280080e1804048850b00c03003040000c15480c6000c421004840e4500c4512920f1300d080710700900c415640c401c444000c2c20804000e410100125440030014041503081502005615041842849450006c5c01d43c45801606ca0501000090564038543e01081c031035803040c480b50816101c0031840d0b108403a8050360050b641c1d010302919800248015aa0541c054508010b482d502d05407030740c009204510035003c80e41250f9400d0070541c00c07541d05000f0640000c805105072030204945c0e0340000e20944c19084170880344412420080341118003a0400510005580310420416404000c0072441c407812513028040c40d0740d1561422000704246001503c01e03130130080012651030007401106c0000480b40c40505045019040c00f501401e421b503a404124842d48003039007202c0d8818611075054600c10806240b960300e8031442c00b01c4803070035011500c0d9414080760 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 447327158 1250 447325908 447325937
    0x30a09020d060605010e04050c03062202030a091e0506010302090a0b031b0a0905060f060703140a09140906130f060b07051506060f07080a09092a030228 67
    0x34200070400344142800b041240c1810f000400c0d400d90045c3c0c060249042c002402a0440d45e0020340394454029107080f040c0031221609a150b5540030550a00341910000c1480305040705500a40940c1c6d001e0305941d050500700d814070074405041c0c00b0002e405500f040c001070005140c210043c940001c045030300481c1600d11000041c3c18508501c0007010705071803000304071441d0b041c40c0542400034500c5071344c100f000e0b1501c400441ca400060800b0184141e50025010007014022001498489481c04107142c49088928000d01783c0f41c514020002001d9140c000284a46014050300d03105400c007901102d10b000c81400001c015140c46019805102c0d114940414007400200140c0a02400b6800400340101c0c0442c440c5030050300a041a402040c0811044010b191104210761032180c0c17004105607502200c0804450a150507081401c002d403c0030200c4181c0c050a904442d0307500030b0051039084c000400702c0c050341248100300030200b420140c020040013010b0000c02d05088000c01c1c1c05c0134100e110515 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 447328408 1250 447327158 447327169
    0x5070b1c0f0605030d03091e0f0506010f0f0504021c0f0b060d052703040612110a05091009050f060d091a04030f0206010e01230406060e0312030103110105030a0902 72
    0x1014401c81165451008000c689410000e1100d100000c0c18100801e20550319249544401151114412a241c0080d02c0401c40d00100018405070464140c414550312115542c030303c40c805100d084a103242c9103070085030500d0702d48200d80342d800f00300b018a81c44085c08000080540f42c0c600012484564030010041652927184c02803980751300501c00090140343c1815040508282c02c150b44404511803840200404000002c50f03042d900d20742400c4032000c0c201c10b001d8028101e00e6803881038101021036500031413a00000580340300c01080702c81d01805120502e04481e0016144038055001c20301d1440c425550034100001d0903118030307041004c150007001d0740325178038880c00306180010004c40840400c41410b41c000201f4056402c1c61000e0701455140152a0880807010700484900c000100644030307103400c1c820000103817a1400b070800e011040d0364030806841c0c0010b41c0006802402600308513003c0c24690401c4905a81e404400701c04801000c5004444680008200b41501640c410014015079a107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 447329658 1250 447328408 447328421
    0xf01150f0c03022806180c03080d0b18010e15010905130f111308070b0f0c0f1c030b030109050d0c050304170102190513030b06031e010c1b05070b1c 65
    0x8460344580d80e07184c6481e1500403200000003150150814115110000300c1c2d0f4503802e4201c2c1d0f08290100e886a24500750f4030700a228028109a00c819018001c099241c030641161307040b2918030500c54096650081c0d520303403100075030b020a1b000130a0140c0502242c6065444555064030900000a41a080411040032920300c5610042070110120b561010442c08294403406000248045c0030181c1c41c00e41640528000d959940d5110300c00814241c0122004010810811189604135819140980320b80303900c031020001007100181c203120098000f402c0c14014440d03140e41c0701e00203150301402c005045590200100c01200c00d40000c0200140201c0c842c2c15032400103170750100040e5942d0411080c4101e9004000191082c00810700c1000c0d41c0c1601041c8500469401c2082e10003507030385000000e1300704800aa41c0d008190b0023640441410041580042c00203e40b039140d0500014244e042c50110201c0040000c11507401040280b00741000880942188118105800c0301901100662001e80701d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 447330908 1250 447329658 447329713
    0x2001200733020304060203030708060f03010513060b010f0c060c030b09070201060e07081905040c12050304090606080903041401051605251a07021807080f01150f0c0302 74
    0xd0441007800e00c4144003080034003201c680000d52405180000103512400014401418040c001c0c00140c680d4075802d03481082200018001c01003441c1010040160300300700e280c161042032400c210802c455004100e026500c42c0c140c0c03111708108009075601005007001000c83c0c41055140c940d55440743c0c0301c180c02c07140955030640000c588542040304216540400620410400489602384416100b1401010b00e400c80420000700c0c0d0340c0d450b030402210061051340486001c0406000b62000e10001002801c25036403858003d009081d40c94504035940c040503a5281c0f1550003c0100700170400385101000c40038101810300900b0001d000c060840003662018007500c2c140c211980ca02038080680a8070017110400358540d900b200d0400d01140d0941103050403840c0000340004440d000e56942000c0300e65520545000321495141002000741501c07402d49905012101c1e0400100300c01e5264442140d26022640d15070702d00d1020640226070304840c071141038080d03000c3c0a0803903641075100781c1400102c0b407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 447332158 1250 447330908 447330959
    0x6040b0a06050304060c051206043602270708070e03070b1c0504120c021c050136111f0816050c07030206030711060702060420012007 59
    0x50142400f100741c4004407203003c07c00038100500315140d0142c0c0d90168101c1c82c1510b00103100c44100c070b0008090007010301c202aa200c0f465440011782910103850010301c42c401d564605500790042c0c0340403400b01039600140204e600b01000520918407840d03141d0780c82101c5250081d8141d40382e00129082c88429080380625500000d51650f0410820040058250b580c01c0108a245000c2d258100804920702419040002c81440f400c159503174000650090f20b80f5a00d40d00100c8200d25101c0e000300100c1006c86251490203880360909210b14070038641d40a614426007045e09580c1e40d030a91045000090607034403608034400d0903a00342003a01d10302a95022500c50072424104000e03111002e11030701e1070543c1044820824050700e030340040342c01003c0f00d6040c0c440c0d0751039448401c020346505000031f12100c824810181004211035001a08501031801040803074600b080d118107408190440b102201e01180e0014124010f00c0810241700009590140640b2070342515030062900742e0300c072240c0644000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 447333408 1250 447332158 447332161
    0x602010504031b030e0915090c1201150905041104080a051501050d0c21050d05221202010c030302090303070c1703040602060a020309071a070303050c0a1706040b0a060503 75
    0x1500b00e0a0f603014540351051410041c00182da008040b40710b903941040c01501d000300813464400c050b4034200d001032001402244c151424088018440d001480038081c9450304c3d000010301d038881224407024440242d96004412401c3c8070900019211007030f051100550100310000e80d1784414400c507000e06100c2c50140c980601d004425048118068100030711900d41c0c0d80c120f1700003403c460006e208940100c4041c120782150a032010004100d966006800340c000d5840d0780c1d0072a0b42c402c005042500d01c07544c1140251070b43c00c4d1510000c0f0498018124625107030201030025601905c8140c1415100703240141c94141d404001c242036070040b40044809001d0700500b80f1034404519101c20b03010480c000103500b89894900000c0d81c0e020050700e4001d196a000022825242043c8401000751040e040b20020b00c40e4180d008681c01d44c0811800c2e4002880c080201d0342000452003203030201c940c107a5492040c070b1021541100075080c0980100e80c0503964064545007600c910784100000d141070346625440c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 447334658 1250 447333408 447333413
    0x501090b0f09071704050a0f151109010c02040b040f0e0309040b030105060a051011121c060302100e0406080a03030b030d0e0d0b090a050609010209130203010e070e06040f0602010504 80
    0x8002821041d10700c5481041e04000740380380e00200510280c003025401d20300d02d40340d40c20214185a0100c10181c0049084501842030101e580d65803034990307100400801c06004c55081d111904d000d4401c08900180710f600c24640985410f40008015030300c01080090301c18000030804044030a02082d068603038001041c91070240c9444d2103206000702c800e5000340480c0c0b404000051100d101030040c0703481906003040303c95a180c81401014500c201c114100c4008000b2607010000d550040881405d6104540000c1d0780004624052030044a50260000340704482043c01901e00c29618228107030040c0c0c1d03400000452060070403070450396074041d0310001b400d4071035a8245414a5505001042488446220b403032042d00d032410324981964000d4408070560310b6502c3c5003802c204100002a04070b01c00c0c0c10500910382419402400300640c00c81e024800c42c5041c54000d000da01003449003c04080c8444005800940201d089244821009141c2494030b5180e024601c8580d9443d000040143e640300e040204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 447335908 1250 447334658 447334669
    0xa0f022506181208210c030103060b100c060c0c2f010c0506060904080f13050a060306180f150303030605190302031903090911072001090909020d060501090b 69
    0x582e10500d9002c00c0c03541c00c2c1602104862070b00140107102c43d00024050303402c3ca40c0d03480e182ca00b0301101c2ca81c4c0940f0703042040c0040b04940080c002540d4041c80c000d481861031800c004060f03888116a02d900412000c291982801098188602800d0107001c628520018000e0640258040c2101e0071045191903035244000311002010702035410301880220b400003040000850a40c0103c0480b0110026a00e40c034004950b8001c8541c0c00703d940001103810318141415982200c280c0d5402e581c8202d0300f070b0741d6120417410741d40e042c0303d151140004400005c00507509508083d445a62101d400b281001d451042a00b209103103600c00e4001980d201c80912a510300351044002d400c4c5852517403202542144c00003512020003803030301110748200c2440755041501a0440e42c00405500000b005044561a00139851780d100100407a071805240059403081c0081c6944c460064506039100120f01e820143c034080109030210040e60b0242024801000182442c040d40d8082c0515202c045030380e503005810310a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 447337158 1250 447335908 447335927
    0x110c130b03030f070b070e1509040b09090109060506100912050312160905010c020f04050a0b0a08280512030901020c1204081501140d020607080c0a0b0a110a0f022506 73
    0x1c007000401d01d940c000d80e5803403000380b08c007040f034000300166900a100c00140040000408031504040b0300d0701001450714040d444600542e02941c02401b259503203000b0000e0045241d51184d011030004c81061090501e0030035803481542c8100100c0c2e2802500b01e0078a0003405007180c48003000c00100e0b426500e620b40c0090410000c000a007030451190440780e001558201070020240e01455440d00061407510a40d003104150342c1e000b030b000c0b80f0201c4e15085da0035101c0e101c1742126082c0321000c6212503061035848000b040c0c11900b02c00130f00741011040345000c2c074542c0003030100c11056400780001c1e00707108000c1c0100039a6139001ea1000e03075901d2800301d08038182041c214030329030502804001041480755041c414454810101c500e6010205c0c1c910004009000c1c44101030091100400d02007003110b00015000005805071100d80c0503079450001090540d071640e444000d00c0c2d00d040c81804419030052010b40102141801681d2890068400841c40071f07501c04110f20140b82200800c00c4825005402035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 447338408 1250 447337158 447337171
    0x9040602030603071d0c0a03021e09010e010504030b0a0c050c03120f01060201051512030408030f040905010e09030406030c0519020706110102280509030307030816110c130b03030f070b 81
    0x3c003030500c5d080070408403940300400b5600102800a000c0b0342c4a031090381220300030740d5161960f9002c00940910204283c108514041c0466103250700c1070055801081500d04699000081c50313102d9448504010140105841240a22400380400140d403081803010b0600b5007500700000d5503502c1c1506007107000c2407041c1e01181c196490041448108460b0a4400300c80f400306458140100081e0002d56165100746c0d8810811404082040300840c00341724003e000300c5111801c1800140d0325800302803440b070000c0d07405c042241d00c10001088014003030f400c003041d840d00c0340c208a8148580003040e02e0700740070030191f514016000b101c410b114030380d0802c101000064a5038002c5041801c80c02c14400700303070b014000e44203c012030304010307066003031041d001c54044040140a40e80c9500781894082c10349039042c0d404010341c045016441840c03621699200c200b01420703800038a540b0002c3d5080c0148860041d40100c451134943c4080c2025440400081c580b01c807840c44003503900c030702500300440a4003019049 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 447339658 1250 447338408 447338429
    0x120100b010f0e0f060d0903030e01050a0e071806030f05010504061a031e120406021b03061e0901060807081510121202030c0604150e07061d01020703020904060203060307 75
    0x40b24211a8004049260796000f601d0500c14556003d00184060141010041e10030381064040340415626801c001403842d100f81c02840326840b198401400d49074580b00102c0d5591003604100550705040c0c42400000703904260020303e40ba02c980f2548240c007280c0c0e00680da6a1345030011300007000103600c61800c0d075100d80040345541c0a1284000f03600c9484a50081c001d035055000211405002408000c00c13014520300c903941d0300d50399220080e450748111800c004030100d011581d180c1d0380c24041403481c031400800208146601c41c960841d04c1141c0c0141c00016a5903a48202003401d103010001140684503400c0184042c545480b00202c20250042141c4501148a4001c010302041003040395015a8000420030704484400c400301d24500460420512910401040c00309020406001e401e8141103090180100c209041180c0d5850400d0310400c400a0691910f400c0c607084114602e03500008140306a500ca40d4ae640c0004110400c140c5040c0c602d02e80c000140100342c40c04104000003022103498 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 447340908 1250 447339658 447339677
    0x7060509060709140d0312050103030e031002190807110d18052211220905090633090406020301090e07081f1e050a0e0c0d0807020120100b01 62
    0x145103540358130001c07045001c1d006000380c2208160186074088195503400000300055a541c0c01e0003000751030744400e494002c1c080d20841801c103040500895541c907802025000318500c01d84000c41d07407464002e2043c010442c00c3e0ba12220146002d02c00c4111040e00d55503025090140343c61030400065060b40801d00c2220b950705c0310b0005980c1500b4402004c0a01c620010b00c400041080384580d10031540c00d803910080b0f01260f40305401e086034010f010344200c00401c1216558501400d039807220280c80346e001d03101e0b9060400b02c2c0c03101040040c01c415074a0b032000303861140080012407284c40042ea8215880c9401000600c5410440e114030240340c01743e40024000c452034868060b488640d40024a6907008076101490780880c401c1c1c00c110345494030100b00b1a6404418051b40008050680340c0f07001450824403042002617001030b0441e1075000c010003142d50603181380d40e0280320394409102241403120003a4034070b100d420749100c000d019a1440000c0c001e641c0d810250310048603001111103050000c65403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 447342158 1250 447340908 447340919
    0xb010e0c040e011202010c080706020a0f08010302010c020d03030f1406120d122703210c020c1201060509010b0d0612080403080d0e0f070303020609060903071b05040207060509060709 80
    0x110ba0441d0651200c00d2600910340c0012220310030141c00142c005c4c02c0c002080302c100301c80c03540240010482a5603003604140c0fa0035084072801002e01c0040e0004840c00e0300072016140c0110011080c92007400d00148080303180041c0030035200700c83c2307402c01600c4c2c400003000842d04010651143c80d4003964050041a0311805001d045024810b007800c44003903a40e090081040402070201014414002044040c01140d1500500440c1568074200c041e51514241c403004421600502e5603d40c41e0340c01074045002078800f0701c107901d004420120480d41d00c4490003d000c2c0c40c2d0030700c124040c1c001c004140b0f50714035207859800269105588004511a1450401404119440c09641c01d80e944a0f00c441e41d42d0300c149481ea0b001e030090412480a13030298040601076603500048100c2185d201e6000d8650a43d01d4010f41500c440003210b811884d90410000c07100004d529000c00004400c1040540e007413682c844002ca0708a0b04441c2c02103a243d5511003d102c01c44408210040e030250031854482000c60600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 447343408 1250 447342158 447342179
    0x3060f08030708190207090f0f0e0d0207090b031e06091614040207050309100915020304050904060506120708031314010e1306030215090906010c0c030f1703040b010e0c04 75
    0x2802c038081d66603040c0c0d200c41c1e1aa2007440086c00034984000c05000034a0181e00b004018400701e035648524130315044500d46100c0005c500011a6030080d00504001880c1154010291400e1880a80d00d03000c0c0240c191031920194590303402d145070010041c0f44070b01e0500c4034240350000d0007103035100011407000e04101600200d14100301003c410f03140580c50b1422460500c0c518050b0800d00c643c03144020415180301a880030701d24040364444103c4034100071250205903201c5c487e6026668000005100050214140f0341002c0d40201016141a58500c1005055401c01055070418115600b001034001c00ea0910366200c00094920301e0201072003d024203001a103100c0701c40019a010308102d504d12811504a0ba000000540e00601800c40710780078419070100c141e028202d1503100b41d0400000c1403840d4459075103000400c0d03002002201075030654841800598a840084480202c441211500c0d103000c00b0286000d00c0c03040c0b135001e6081d4141090501e240c10020141444e6a03001d000403c211080c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 447344658 1250 447343408 447343417
    0xf0203030f01140d150515010507261201030f02030d08010803070311011d0a0b01060201090c03170702220501060203030c04091508011d0d090e0703021804060603060f08030708 77
    0x20300c3d0780300342607420b000401c1d020002000054405880700301c40212034200d5400091080d14182100d5201c5c5220328015151070055050113020003a0741c241e103124032102c0c481c00341e4400594401060810611450f881c102038002d80048a15400030501c0e002182400c21503404100707424206819190304054600703580340180e0320040d08000503240c2c140d906001c00c0d07010700040001540e01d002800c0032030300305da070381c50b0f24010085819040360400020880d01c103110700c440da035074081c510340419491900c40508501d101801212400020410000140d40d91a0342000c000f010b0b0714075199200740c0e00034010407208143c0c0b03d030055400402c104000d584191084030180d80da503010025241d50441c0751051600c03c16008aa1290700e456110000d080449040361210700280044407401c0c176100000b2525003900d0b11685200780d42035008928058041d8014100c0c010b44215140307403c1600400240a66095a010340042035448005120300ea01c07110000300a400c50000561420510b543d07400d03100e10a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 447345908 1250 447344658 447344669
    0xe0c03040f05120a080a0c09171c0806040e060106050d0f110403050f0d03110405012714270411030304030c030b06091608010515120c07030f0203030f01 67
    0x6080045007408544015003000448404003e0720402c070280340d000d02d60742004a100c0c08000b070f84094460103103413041e80c0030761799a241300c1c0c0c54040e0002d942e00301c03e0003c584074080c508940745420f850865210106046540b680e809091140600c0111040e00c0f000c1a02a0064401446803d030080100d4203030101d448000505000c400c0030280040280b2080c102c20500c000070b0000500100203481800500907030241c0c3c0407080e400005a0440c2d90002ca1070005072001e00003000150701900450000918164a0b095000011882c00000d14466000042015451156203189081c215060004844000f90f0301d017803100c044403070a00d1003800800c02007002c40c0c88018401c03552000d10994004550040031104207548030b01d4212501c080c200c45260003076042c01d0010340d50100d980030a000c54401c076140c8441c243d0900c002e110b801030381f121482c03850720360422000801c140103005051156164110040e12041d44e0300d00203182079006180381e41194001e2060011440f61007030702e50b04542c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 447347158 1250 447345908 447345931
    0x10c0305030c070206120a0506100905150c0a1b0b131a0702030d08090c0f060d0b0312070309050907170a0e01090c140f01030e0316080f070302070e0609010e 69
    0x182c80c91039040052180740b0000b900120045008010034122909450042604040a02240c0c3d1140280498040c20b44481030008800c0c0c0c030200b080d41015000700071104001f410340d078540804c01007002c0c0b0300505014102d174003251750309580050b00d1315860355101528114645510b00041101d29200d0030160340201c5c5503e40000b1103c070b070411400c4040300c41c502e5015065603c8201240f0020f44840303400c5826103071600079008110b0322882d000c0b0741242020b000600c41800c1c130481801c042d0041140c281c0303084d054816802c20054219403203000e4910740e440f0f0f42c1e40404103420942403141800c3d01502c880280002960100d40030307001e0b070166541c452a04000094062401b101c4c00e03024140c640400340442c1c10340320380030a800c1600c0c04800503814056030100d450300b802c400110203c80c40080240540e810a00420038840a48124061083c1c05114828141811842c40b640e0517800020b0480c050b034401c2d8002c0181c101c0d00d4803010741c004002c56401003650314040d040f400c4400001c0040c40c285 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 447348408 1250 447347158 447347161
    0x604090b0f030105010f140402030112030806030c03060c041e120f17030a02090111121902030403020a090e1c0206040209040305160b01060315120b0c0408010e010f0c0e010c030503 79
    0x3601e520941c1690004020001d00441d40e554041500c0c0f084075000703032082100c0c0c402001420b070620340202e178100d9140c80c44c03080c0091050b4504864001028107003a50500031146e00b0540c90794104850740c003c4c48507140c0d00f540c40703260038501100908070075406a0304c0301614008101c46442e000d0302c449483e4004d000b1038075460381d52400060580b000500720042c00008000d00c403800750582c0c003074142c100c02a00d550b082c1c070905007022642e80d45408122030340c0540800003400c8070184440c43e44110541e500490342010748a9000402440850b08079841e0380341d507801e00e5004440c0812036000c00c1703610780b84024042c00c40b80c04000d45500f4000c001a000c3c40c0100082010584a401203c60340f0060312001c0c51210f22038074202c0644503080c8150342c00a400d2911848059992030381c1f82c2c045421038900c02484101940d65404040380061070304e2102c01042c80000390281081c09000340000c0e0f120000103d00c1c40e502e141c44115201a410003041011075100c2000e241d0b003180619011704d8250070306584a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 447349658 1250 447348408 447348431
    0x30e03040909050a022704080a02011805010f110f2203021809061b090f04090804121b0b09010818010c05070b0105060f07060902030a140303060109060509060409 71
    0x451003541d2101411914011030a41405804650020b10354800c442c0c0c0495006016180010511413030600d0800c1d03144500441c0c00074010700d0091001c0740e2a40000b280280c2c4031514820140c200380c2054510340d460300c2005005084a10502c0f0a9140c8848a603003013445c410a104054066410b6024401d804000d2802119004a16002c01140c2c01007080344e130308022403206c103403000050780c5c003500705d00c14031005c80c5603104800003501e8564401441d450400c42d1903400c00c01080ca15180540d00250b95149034404107210000910180102c0311720848100994a80206400c03c8200540f103903d0100d13005110080c1c07940120b9585000910b4410400c2e1a000032400c24610524a1a40c2d03540c030309900400d04a030003070050030b2410b0181d184050142e98131400d000461081c2e5200d10f0304c00e181000042c000504d15402940d0341800502203910030b48581e034a00208840c04c0d90341080c654408010000c1c103680c0110068041c2c5400c0c81e086003481e036810003042843c0690301800c410b42e616000307404603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 447350908 1250 447349658 447349663
    0x60606030115030c230a0e010806130b1804120e0612060f010e040e0f010612050604031b0c0b0c061003390f081204050a0e091006230109080706030e 65
    0x1708600e2000c0c07802d0020a0704580c03202c01d90041c1c0424010407100d0706160450341c0100f00d080d101d004040d2041c09042a58801da034020000003003159803040184150560711807501c03d009100f20b11500400c080441031030300292000404005c86486a6001c001451070204d000c1d5085070402d4080d22202003c0740204c005a98034150442070940042c50104070f03008582002502d4419415580000c00c4400e0b1200402c03080b1300c5100f6009095070b0311203004940024450402c1040394401d03580084424112a51117040300c007070503131118004400101c2c4440311001c0c14000b50b074219454400412000b8a0740d503d00003940b00200c0800f0f03540313800c0d54814111030212200c000310840d4451403520003649402c00110f901060b8060000707544102c22905140380050811641607600040503050181d1a0500800480c00c0041c01c520080c001c150340c8080320030960040c10b02500c4051818400d02e079813038400c090f009106941c1d19040050301c0004006403000402c02c60161046842c011583c802144241072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 447352158 1250 447350908 447350927
    0x2061003032c0405040501060f06080c0406051e0d090605060603100918140a030905031f0f0204170d03110a0c080f09090907030203070e0601200f01060e09060606030115030c 76
    0x80c0c100703090138100405c10406600140550740701180180c0a60b458042c2151130200c105c0340107180841c20030041c07003424003803800b4140380b5540c40c48a0445a55016201c260b540106181d124100d031202c030032004200003400303107507130100041e142241585440311034004401101d1282c43c41c80d0342c1e075200e000e64255450160650840d00700f10300c10200841c40c0340855031420480402d84c0020f000c0071000c42d0750311b80400c0d28003812006440c2164164044a40080103161140d80070030140d9003000000742c000c426070b070581c0d9590710000190005072084200917098414682d0107284041c400c1010459190f0072041000174541c01502c550380f14400100883d0309445482a21941b02d0340c44010003460003000101c64003505c1c0701340c069501d80c2e0b54442c890307016502c0c00d4603e14003003500e6130701c00307198100300c2c944123540c2645646c1200c1101c0751091120f402c403481e94100304a04d803040000c0050443d010440030350048002d485182c515858007210502418180700c01d0b404142c0ca800803490030b01d200d00c0c410b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 447353408 1250 447352158 447352247
    0x901141b0601080f0d390b0613021306051b01020f0c010f02040e010e0415051302010e0a030305070213110414030f1c0302071502070c05010206100303 66
    0x111010034003121140c0d90341000b403003444a244160108400d45520114403215815110307110390082a92100c15120307981d030384903d020408041c020300825403c00b43c107140454180200c01890803414041c06102c9121840e01d1010b514038010049050102e041e14041c0003100d206242054480c01c1500080e415840404140c0310203600200f02000c4030100072000b0103100c002c04000304440109040c081c01a0f008030320655003c6085800100120002411420740c06445022040801040d0303070782e030208480c000d5505d040c9003e18800000704550300700c0300f444040c000031541003c005113103031350080c03c47c850020024014a00c41c1000c2000c914560403d02e0303000000196181c0300c0351901d210049010310400900e100e841504401d035900c04001c1740050054038000e0304107035031108442054020354030100088400400541c8a81c095404500c05410303000c3c4682200442c0700c0c41c01e03000a1420401030300d007070f1030f020a00341c0800002e5008514031001c400e08400c88900d00004200304000040801e101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 447354658 1250 447353408 447353437
    0x4050d180f030b07021501050619030b030a05010b011404030b010b1b0109030f0314040c0b0a050d09120f0807021908070b040606081b0312090d020a0803030f0a0b0303090114 76
    0x100411001400f450302c122041e1782110081c010340c4680441d443c00030702c9001c2d00a0f804029402005180b220301300c410341704a05020450380002004030345005202c1d141900d942e591460300722415a80008407801c074520b00c1c2285800c00f81140c80d990362001d010300c2035250500f40060084202c07040b60321f0340c644070740c0c2d83c100070090404141030240c0f448440c144d1040002c0e18010001001c2242d040c80c6500a6800c141c455401e2414407420f855154000c1007564240030040c0a810f40d0100c1501410310b405204520194000c0c1848501a10341d0a55040700020302c01c4101c204460180d0020f84131b83c140a003100d0160040a96080c06600d0f4400d800d00030f000610700b0010041072100b41e4010303104958501d0200c0c0c0e525203200303803071540c0d4003101c0b80403e0303064000c0c2d5102182c001e481c5d009400340410043c0320b4601c2c0728a60340082c1109400b644408203a41022040010a403146040039900500008081c40043c80341d5000a4a030b20408200c2d9060000010f02d00c5040520780d801d907808036010307088 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 447355908 1250 447354658 447354689
    0x303030c03010911040e070c0c08010609060306050a0506102709021305010801060e0d0c0905190606020105042103380301180f031b0c080c0904050d18 66
    0x210000300c0d407090184442090a0481104003440400204e13004c07550b114070b69210139140c10300304407500702c0080305c142d03200880b600011619410a11448000b0042d01e100019202d28501d410307004d5400080c0380442561400080150329150b0300c0505846062600e0041c100603450407100003d15244464107907a66403802001c80c600307206500419040d1582c06400200980d41ca0045401c00d009010307120000c0da03c160081210306048844d500707510300c40d05503d4015619448003c044541c02c0b180050120f030007100c0145a04d038a40304e150040c150520080c172251070a611001d43c132040c401c0b401070130000d02d0b003800c141c11403107680040c030704c12649406907580e208010804231082a0542000840b40d4601c034003624945014440c4117190100b451007101031345070317030f4444224a604041058051001d0702010050314109203404610741031150341c11b1082281440c18840c23130500100c245d180100d007420b0600010817000140003006c0e200901c0e22084100100c504080304211542c00000d20030115503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 447357158 1250 447355908 447355921
    0x80a02070b0403090303021009200a0812070c080705010906050a0302090a080606040f0b0904110316030c0f3c03050303010306020a0806010813060c0e09160f020d0203091e030303 78
    0x28404c803c41e4000e80c00c8400100c0c2246000003207498440e0300400620105da45000500c8103c0d01d241c0441200801e000b040640d1171400c5824551115140c45040314005000020002c0e03d03c3d921000e026124001c00c0035a0820b00068111107107801000280a00403850740e0000d84650101c400c501006020901410b640d45845640c901c82a40c0c0d09101c4c038280000b003100c82a49d84aa05008540241180d84941326921512000c0c105001801c0c1c160140242500e0410741c203400f444010742c41414010130641c41d20401c5185109980c201000d14420342403031b441e0507082d00b026541440b010300b20060440048090a8a07030003483d43c8010300500020000109105495001d41103016060f11002c446035190001101c210004481c040c82404000300d124005c030340d07030b640401035000650910545418000f00014030984e000c45a040007154075040e60b050300f5600c00002c0260350b0307460000302403090280310082d4803406401112405610f803200603030b05401c488224081070079405002d0329034a0038a80e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 447358408 1250 447357158 447357167
    0x30706020315122107030c1509050d11100603050a060506031920010e010207060c06110301121407050109090203060307090213060801080a0b010b0c070f0603020d0b0f030d080a02070b0403 82
    0x9070f155034291003030350310400c2c151681d0702c2c01c541c0c50035410350b980511f4040c0b6584459000c0318600071000b20a9562641100041d410002c0503100345c5c240c2c4401c032112600a1a1510b405003003051504010b09003503040002410016617203202c590f2003a0701040590f18803011a01c1c4c1460500c1e0107460b20084034052043c825182070070f003841c1c654915110103281109005540f45448078840e03d0040e801541d04009480c407417013180001034880e0b0800302d02d00b4a82002002d481e0000e8100100e2401ca1418810410082070030b41b01e0849105400352003064507120010300070381c000e40310b41c2d850142c0001c00038000b42c2d8107000d02005010150740c215184d500e00310881c290300159010f0800442c95000011034143c1002490411180d404020410f40d46c1c203141c805403040e080140c204200c0d109006010512005518030203015200303540d001604e0302d90009426090b1900821504c3c003900900c05d0403440c1c6e490105842c024040d4034201000107071103801c8948000c2c426000c000e05030075130105c140010168030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 447359658 1250 447358408 447358423
    0x14130902131508060105180903040302040c080612070605090d020109090203010e10210201051803070e0915060d02040507020709110a080c12060918030301080106081e03070602031512 80
    0x4440007809801e4a0303461084d5225003e000e41c41d40068400074041c0682c50034803160341e020440e642074030308299a0380c0c0071400340e4007440e0600307012450306810020750f404c3c01c00140a540125500030031034a45481c41c05002031003100340c09030081e0903020108040d0f9002d15a010010400c040382155a9a50f8034610a070441d4280d90000048040c073703030001181d10041c0e6508520502e030079601c0e100d0204c140d0064a59070310881481c12104040501c60b155035406000320700c02801c441c220302034240fa142959170b0404d40050001f417041200842804000e413031b030840c1850070310b82c10303107000645449130403042e0300d00f0031543c0c0503640e007074100440c42c204801c106003d404070014540342c04045454420044403203016612020700c2141c0c8480008416107014100290010b10420305503406900e50744d0802d085600907041910700c0e039190b4030f0400c00548100035a030741c0030f50100c05000c002d01c440e03030341030f5180d01c240e1202130080b50300803000c0390381c440010040c8140302d94014541c50030410003041045e1118003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 447360908 1250 447359658 447359681
    0x80106110a0507090f0e070e010e0406060e1302030c0d0b01030b07090f03060c08130807060f060b1308070b04083c1f06051809010b030a050a110102071413090213 71
    0x700401101c2d000400507c80d015610340142d17101403682480c0c41c040c2c9655009105644580d141c41e00050240b000c00312503401004550f4002c041419540181803800141076052401401052038881c040341e00d03130303003064103495204036404129110240c0031a101c00c816001280c1c1146080000010421158000d44240c4000d444902240d500d2850400704190030740070150640a0800c4040d001503250780c41103162070940100010b0a54981840f010f0131b400c42c0651040c603210b0038009214412042015000805141105920785800c00c51990740b6084815a6140305407480204140310084410810350403040c850000d20528404601d5581c1e260350004081900106003281c190705403c080c01510300b5240064920801011441e4400e101080c005005d1001c41d56035140400345a40c080c072440b41600d0144000301442082420300d4040c0040c0c049804d41507500c03480c410071000c200000013440c00745d4120b8150900c0680d4050000162688450080d882010503c0d26400d8240c0c5a006500142 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 447362158 1250 447360908 447360911
    0x31e0e070e01080c010503010306330e060607030e060a091503091509051207021302070c03020909031206010c030509040e03040906050612040b101802030103150903080106110a0507090f 81
    0x90780e9000b00c41d01c4d03000780e032041400110100014800300300f09411040c1c0840c005524501c032040a00d0720a02a00791078403a2000041908404200c1d0a8204000b00d4022a040b41e03d249000d406980140c01401e00d6111103020303401c041030b090001e60058070f0450092402e10f103a182e0701c0c03101c084000c00134800044111400c82070348088160400251203061507640e4450001e14503030072428008110381e000031a00f01c1c0d0080c41801000c2d10300c04c8a002601c406442045d140b0600d605510410540500040000405500a015503a4820f81003503d95400413000e09100d00840e0301418100c500f4403c4a0304240c105040102140e43c1d408000000d000f00c403038820b02000250b45610030041c0394401d8200c0700399266100c81c0880d002c81c212942d8070f90001a5000441511552000d43c00d5a01c03012180800b1210750100040050243c14428042500b404180c1000600829980500222018000c9038100003140106a00400b010003108180a401504a501c60741c0d6502d00200038140a440e0a141c10707 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 447363408 1250 447362158 447362161
    0x312080609010e0906061e1216060503072c2205060a03080d0203150d06092d060b010e0303040f0f0501030e0d0305070219050303070801050901050f01031e0e070e 71
    0x880070f4490742800b0b42041c402070940c5888120412040da0b140800c1500740b210070380c071078808564410300800c05040030301e0042c00f69004451040d6a0906c0c80b940640c00f4003c0c10070403c0080c40c0c1c403802009200401940c652010414510741100c40c0395410319480e002080d00d41070b40000084110000c8581644900501c050380c2d42e4028041d0101c050300c401401160305200d60400e20034a0703006958010701c1c08460701c02401002c00080c0d0380b10003828096030820b584007015401c0c00744007420b0f118a10798441d1144074590329801d040940c1d084606002d003540d5514450350141e03038481c89000e824082d0080461352541e84500344031380017102511a00b0000c21014500040305d5000c3e001d80040200e030742d0060200590301000035000340000500d101c0444c010300c2440c80280b0b080304c0c0f184800e1401400110740b01d1401d440d000d8414103041c1c000f9031242d0607a070010401c540d0b48180c11841082e081c43e020818102903844800715001420108018a0911110a00d2a4400540d400464080c03140c1541607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 447364658 1250 447363408 447363419
    0x3061a07050f011e052203050301031103190803060a030c0f06091409010611030f07080a0f0e0a21020307030305070b0f0103020a1403030705100203010f060305060306041407031208060901 82
    0x3c032107405030035004049052050384d03a0310307400c3e0340055801000000e07140f101c170300e44002c05060013094110490100701c2c040014400c0c07182030300140340140001d900802c0105032010354140500703038144000300082000000241c0546031610710100640d030105024514540701e60962100000c0d60240100060f03113801c1c0010952004140311300011006402d4580c01d03401c20408490000960040642e00d1000300002c5141544050040500320b004050303c0c0c4d2500413144004060f6903914524108020401e070f0880c03a0359aa24400d541141d00721180340d82400a2000a29161030307103208041e5040c0100d40d000410325800100a0500b50b2103071540c010139545205103049450b0081c00082e40015800e013040c005c0160350811b1280c00311004081742d0030b00c200340c1d0303545161043c20300d0b000d039140f5004001003141c2d03600103034107002a244078102804136103418400302c0d940b1030b0006c1026000c080c103a071442c0d002007424042007000c0c640000c0885030980344101c001d04030440640d000340c00340c195800002003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 447365908 1250 447364658 447364661
    0xf060103020f060903070e040f060e1c050a140c0a0c1a040302040902220b03060a020a0203120c040503070b0a080114030c04110904060e06131e020a03061a07050f01 72
    0x40c0c0e54010041e801c150202000c0c00307041c2e0071001203107030144924400032a8030f140800300c0a111f244103000111501c070541ca80740c000c0e100c1070708008a180d0b00c4200340740c14400401c1003c141e183d00030b1a14070f450b800094012503d110f0511030114428100103280c1c003d092000c5804401c0074040c05d9140340783c0380c2c5c96820400303e01040c280e2115110061005000520780f54001f40c01e0381c1d0008204241000000c3c419141080710f00c0c08a01c042c1d951840b6030002824240070031607224804000440c20510b00443c080d427a482000c1c0d500454220040009081034484410f031805048003500310383c5072903103452028480d940020b0a59001c208e220000165588070700c4000c01d90110003501414800e2000d40501020b04006011618031000c01e200340202c6443e107200700402401800c80401842c2031010501800c013041c84221550306003007034a03002c0301005c44070102c00b2402c0c0000c0e00582c0c6038207410301240142200e410401c0029080003503030b2800b08880d0040d101075130144066589030b001c880f40700d90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 447367158 1250 447365908 447365911
    0xc0206060303041404090206031306050708090c15120c0d060510120c030f0c0e040b0301050f1602071802180a0303020705060913020f03181203040605191506020f06 72
    0x95050740100024400220543e0400b040c4d10390160011441c0c250300e50024030b13660001c94444120842402001040c00100d010362500b00c18281010007480c00d2518410741c84142000d40745025500c00112101e003070210b1002ca50300c000c0c900528401710f0610276a00c10460f0300c6004070303840347c0d8141013000c5024034004c6000310300000f640c0c40c2c4189224241c0d041e20042c3c100426043c0a142d542c5401d8555140d90780205010009550360f80f03440c0f46814410041102e420000050190b0324002c100f00302c0d42c12805280e500580342c29180e8040e8415403004134504040c87e0003141d018108a80b541e81e41000c0e40c0c028018404440080b22030252040c03040c06100c1486200141c0160700c00f5400700041d0074090010091174401401250f54552540d49860980e030001c65900140301d00001000004002c0702c640d44030340184000076101880800b0080f40032800003420140099684002250141c0001210009441070342c1009100050160401041414851081402500a0307002d1006104400700310503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 447368408 1250 447367158 447367171
    0x40b03040b0603010e010f06051005040e04140f19110405100e0a2304020f0a0e152d010207061407110103060b070c0503010f020307050a0e0a270c0206 66
    0x4508696464441c0c0d505160301800b55909550386160f00f0300112001c1c0030740f0100c052180400f090842c40c080c01e02021201c11003d843c1008000e10007884106140340e809904542c20040070130300401404c00242c10011110102ca80a00c10a2000300c4150898646601c2450040ca101180c2a60800600060302c1d81144c000e07010703200c010720902841c5104284550401000500022405003400b01c4c01e00c055800201e010f2103400348010802103241a40c21b0148038001565014643c5144c50035094944202a07c10490303004071051400858980794114103980b5a00306030050061003500c03042c04221061540103006004061000c50814002d49980c4035517100031207101d103440c0054483e09409001208445c0c10941c803070900003080f6002c4000f626481e400790110360300043c80c0c9800c1600b1a4803405140501c0c1d4010f00c100300b01c10b9000800c0c0d0f07101041d1070404807171240905000444640e8a40c00900101c0a020750030100321100721104a903407050340000b00401410000b003070782c0c1d80d00100c500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 447369658 1250 447368408 447368429
    0x40f0f2301320706050114060702090703090305091f0f0e1005090d1a0709120809040203061201180605060f061903020405030604030f03140105090610020a080f07021504 74
    0x1ca441030228a009410000a204a440e403842d10484002e0603404100d044c0e40d180d8403000140070f65200701c0b48051591030201d41103032408880e0780c00301703140c1d043c02010b00042c140d0321009031701032500032070803680e11501c010014004d0301000b00e61b1040800f0348001c400009642c1d0500204e40354002e00045541860041c01c1a000d6040810304803155800700c0c0b595078001d001c8482c080c00089080d40703000d550301c04985680103645003646006144c210f095001c4410000e90140003404104914102e0b43e00343c1003034401503525070b00e441c00300f2051482d079144040558a801e86240500c1e40d615400000c0ca0b20070542030025890702005c0041701d103041030f400c3c0d030303c03c00070058822a028081e10040701000941005414980e845000070f06069080340c00394081b40c111070400352407503072610070000c06820540b40c500c519418540802c4c1c0d101c0c00180304502655441282c0300106008000d49201340f0f0f4000760465a848a25001c1c00c425001020100d00946034007902c170000050b11800e407019140d50020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 447370908 1250 447369658 447369677
    0x406051c030507060501030b090d090609060503060d0b0c0d0f0605031005060a0305060c030103021807080a0c020a2a051206060f041d150109020c100e0102040f0f2301 73
    0x111500d00c5091003411802d1100c10002c00c4009030650107841d000790700405050559141c1070301d4030750805030915002020401c10304c0c41404115000300403070b070079900e82c0d10748180c07030355038032800302e001150210009000c140680c0c0c10014148164001000d002080590a1000700c40d4207070860141d8602e801055415003150b1045d20421025a000740d174400320040245256640d81e48940b410044151801c00d00100e0010040c81035040040c28a440214424050030b020318200c24010107100c800343c6480403c6488108844110307200700410060309030480000180c288241d1007041c42c0150001180003001800d4900207031900d4a2542c0d48510702682c40a041d1076690042046140d102400007698401c2d590260121083c10000765000e00300799040092101c1e44005a4012001c50b059011050690040200000f5400702185442800c9804003000ca01e01c0200c3c2c00d094068010b68101c4c0a01c8070300c44400040d0005820501b0b42141c1c3e8550107840c0100ca08034801c400c5041301411240850303102607 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 447372158 1250 447370908 447370939
    0x6020f1b0103090b070206061504051c210908190807060203090a0b0c09010810060c060f06092d0908040b030702120a0e0306150325080d031a040605 65
    0x4000c0100d61105140c0043c03541e0b21031303640054050054584400591005007045024144460b21601a2104c210b0700b508180c94480021490306087d040952000150030001c1e0402c203400882a2080f80c8800d9840100a40b00300c0081c02010984580000d502c282400c1c070040144041401c0041d46d00181c4040c0b90a01ea5182e00c006580083d180071500c2c4120200100070520365002280074611a070b0b501550ba600f2100010300c2c180c80038200c0b0011082081080001d250402d9511072134580c00030010031003a00108034580140419408080c103103042510b00040c40c450018030080071881000706540d8072107201e40c01000c41e651800c00a01090702040140401c24804000e59842910341c0304541840706012126003094100c00d44490200b59141c01d8100140360510255622058100411040046c0640080e68414440701000c0c2c1c1c0101c43e000d204003000041005001401c4210100c034515050342c00001c000300034008407008245010301802a01d407900c1d0056008a0300028404c1c144a603446 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 447373408 1250 447372158 447372193
    0xe010305120a140406090e06090906060409140a0f0b0901050105060d0e030c010603150b060c120304021c1211011806020a020a0204150f06020316061a030313060906020f 74
    0x2c156007804039908040090103424401070000d404156614a110742c504005802030710409452240300d5640c10003041140036000601c0c0e903000718200c0b80440e08800c2c5e42031110010700241045202406044001c2080c00950242c00300e010b40300c0c0c882c0044d07560303078100d4850072100c007805169070020341000340c14500d0181c1e4200c0800e004c00c3c80d0640c0e25041005541d60f0840701194000c940c0940e9001030f5242188252141d030405a0068581d203180080c0d000802e51290040c040e8125900408004a0b0540d01c5040b032aa240140005d186030442d03e6608087c01c1605614161200150a01d0030001802c0d006000e841002c0490a0045070780702d281c1d86e02c46001e504442c4a0000b188500c031101000341e03031540180741c050801007100d4464942005e541e803450b1301c11500301d00159402041540700c0002070700559000e02c3c3d0410400907018800c04686485420701d1100241c0c1403001190002001c000c44580304101e1f001034071040c1245507103500903a100c180145200007607801c028109070102402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 447374658 1250 447373408 447373417
    0xc0611070e04030c170c0c24030a1508060a1b0309030804022e210606080c090105040b0a02010507020d11070e34030b0603060603281a09010e01030512 66
    0x90b044520003075036071888030145e80d080005002c11a510480b4050f105091444035110056001500302440701e40c4142c09000500c40a018140c0041d91862000c4000115a64080c06842528140c9509041c50030314070018100d05040c91130580503800c00603034014000d03c50403075071503499200d00c0d2480c0d440303800b000310242c01c003154500c1020300c01d202c46d040749500340820501e001c8a40c55444d400100c1d0080d01c03411454194072580d0f03180c0b07841020321240b508041c0241d400f02ca456115a503450002e07004988501440e4010403c02001040c268941c64040d0021449030203260700b25090109800400c481d04210412203526039080300b04103014031031140b900c15034406c44082d05d2061804000c0f92452491850099002c070720f00301c0e80e940e0b101c1c0c00d034140155070ba41c19085401c0303400c60610301c0004a107880b0150200103441008944013401442c51034280341030311302624041003503901001d00c070055180e22102d241c1c46081143c00104500c0c121141c040d050300c2d0003100414030043e120000d081103501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 447375908 1250 447374658 447374663
    0xb07030e011d100504030501050916150e032a0907080601030c090b0408030301030b0a11040506031314030c010b030105100303030533010e0f0312090a03050304030c0611070e04030c 79
    0xc84403000c80ca56150f214400c0c034840d00341e13503480f60b4a9186003099400c5a1014000152513002100d8008003200e407907602000341d40380c42d407001e2850035500030242c81c0100c40c1f41074030707825014050507540c440052500340d825140c8000040b00b68030314400c3c03c225154404944a001080101000c40d5072944260301c90414070b12641048100340340c031010031070300035080360703008800c1c0386e100200520412621502180d081041c81c0414030005114100700c51a6024034040c540c005c0c0404400182c0b9100b144422004003038204401640c6944841c2d50380381c999201002040e070710340c24a1034803000d44c05c0c14400c152140d00002c0c0c01d02115802c540d8210090040036103841e50f80c082550301d2242d954220000c1092403485d010440d220031002000161400b420b1806040c4200300d44600c60300140ca01180c915403100003200d60039641c5468200066070468581c102806501c0007041c08403c224440d20712406807151500c500c0c01d02c00400c4002559541ca50003840d180740300703100c045000a8041c9050010345403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 447377158 1250 447375908 447375947
    0x210050313060207230604080304080a0536190e07020a12020f010c092304020409090f05060a0b03120c0a150b0907050307351306060b07030e01 63
    0x11642c1c503600240e8100031415075580011452000d02500c4041c0e6500450f828400503107a02d1030076442d08141d5000040010780400000205074444610403000c0f1080d50441c413024003040d041c11203c0415000110103d018200140a6290810f2411034200c3c0c0303100c0d41c82555000210f0600304004c0c850394001d4800c1d002e500c1881200c40010b1000003000e00c4c7c039549030380181000240820340c1c41c01d590040e45000c05000d10300ba010312110304c44c4d0342c400d2840b1418420741c6a40303034405800709000384625404500384070300d0468044104880c0c0e40c080c801c0640a2021101651174507100401140e5606800341e074554818182c01e00b10b02d41400c040c0507001c00d0001542d1004519481e8007c0c60f1030011a220f5102ea074a1141c458585080903096030440102d00d0a942903140c0900c0141c41d59003040700c041e05101002c90300d202030204010b400100c8500b8150120741c18140140e04441e0081180c000b12181420b28501080e0790303144d40103030341d0055003565031080e004925100659040220700162803104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 447378408 1250 447377158 447377191
    0xd02010c02070f05191d150a06080708090f0f150c04051f0903061d190b06012703080c0607020a020a090c2609010b06090a05060c100501060509010e0402030402100503 73
    0x15120800310425040e1b002c1c1c0b0085498421000c2e01c22584c4054a60301c50345080a0078008941d000c81801e501030514140400241c4801c205945444041c48520b043e03849a60102ca00c82003000c10018a08644840b141d8aa901c541d1742100c440d01a600076590040d04a408291440f0540014241c0f003605a06041c1c04050701c0e500c603002a590801c070440f414403420000b10f0040c0c2820403040c8640b034404d88448103405846d80c0d4030011660040d00300d1341040407441500640c0703184507640f104169400041c02118503a645000e032010341040c01003c41901039207002a100714000b184411b01d00368010f041d51140f5042101c0c400081c5030450301882082030240021902c98101c207014400d8110310b65507002540f51985d6501d081d11900030034980150814080c440749500c45500c0c01c01914000c0b104551141d1700102030500e842002211500030b5410580009982e81e04a0300400c980f083c00e036030b4480745051a00500c0144c0c8400c0c1d03002504802e0030741444c04180d2080c8042c40d046524902101340c00e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 447379658 1250 447378408 447378419
    0xf04080613020a09050420030111030a0903020606101e03091b050307050609150a05090a03030f02120c0c0f0105091003051e040308040809030703060507020d02010c02070f0519 77
    0x80030000c075801041503005865100035880c02c1c04842c0300800200c0c400b030080c0d142981d07810f840306540322611088141c100d0400003a6503420b4002d141e04982c1c0e40300203621b07480c00400503009008031903000e40160203031601241c1c03181000c0789522401d6400e40c8885400c1704d220383c410795208a0b02e2102e44105941d031000c100c000741030405081e04040d4070448554801e818402014102481c42c0d10840c41210108040240b54494810011803440d09082ca280c540e4106102610b0034401c2500c025805511a50080308041c0c020840030320341b01a41c0e0854154070010810311000344210610040c981e8040c061030080c500d040c10300500034150614103d4101400e603c08120001314000c1e109001ca502c813800c10280750703001c8801c00c400e8101e490620700c05052a450250200501130009049400d0000365180a0f440c2000100011a8020303420056441c00c090029100c01320511b80c03400650804481000003440040c0a0054800a01400100a10303007130401021801032050204040c070b00c134400184 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 447380908 1250 447379658 447379663
    0xc01060b0712030f1a0f030a0606030b041106090f0d030903020406260106050609090a2703030f0b0f0f03011b050702010f02010c020d1b12031a010c020310020f0408 72
    0x3401e030300c10451148414001c04000d0b05a90b02009a820410301c0c0c00c0c158400d0409155503c03840e03800a0307070401428a00440400d00b400042480501141c4c1000340000c2040460148240b042c1e026a01004044c0c03a40b0341084039611402d070a45038000484069000d02e40303404100761200742d110341070280601e90f4036404981542c08030350000d050f00000c054110101005c5000d10703610340880d00000c00c078460030100018030354040d040c100c6024943d8a400600558016480b124041a1120380f40300c844203003a200e200007400603030702140041d083c0ba81d401800e0440c0e005440d0000380041c1600c0200000f401886800307110300f01c0c0568950b4880300c1c1e1400c0580035640c2100c8005c016a0740c81c0c0d81b00f0f03003800050f004250807080141168034114001807c1c0350b02060103055805203140943d9010952208100103840385500a4009017000d000f136071003250558056800c421940090690200c8504d0043d520802e0a44010b505a0001c1d80c02c4088803e455005080c4036080c0c400381401d00d40c035543c0003031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 447382158 1250 447380908 447380917
    0x40308060a0501140d0506030304080a06021c0509100209030c270606070c06030207030903080c0d08010b070506130c0f080a060501090507022e0c030b150309120c01060b 74
    0x100422209418810982080740c1c400d07000c2d00c02804d2040c4800d4410300c3c1d21055204101048410b00c0d035582c082a04ca980034002c031001000c0300c0301240c6241c2c4280c10200021b5000554a100c5154000c541400f00c58690107080d00c0755038200c01800c410680324025402075408103d12907810700500801d6640303503440c00840410204001a90b00b81c41c00441c0080c04180005400544594803d00c00c640002d00f60780c1f900c905980c100e150168841c0c81a1500343d5034007000382c00050113140040b5900c40029400035103200c00303c2c2d550b43d0342c10060340d80c3d502d400b5843c0304400d0702401a8100b4000502c1505044a4a5010034424074034030440035541d4840703003080311a9420000e0690088a8030b081801910f0080e1805481030720380401c258144144060750341e0690040030800a04020f1844084001e0b50444284250080c0400d0004203c200d1000303000f0413407411441d10800c24008662080d09000d001d491107000c220006101308480b03485485555080703041403c004c0e64841101141d0000080003a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 447383408 1250 447382158 447382163
    0xa091a120721050406060501020f1905070906031a060a0501090306020f04170604050d05030f0112020120070812040620030c0a0605040212011a0d0c1e051e06030a05060301090b04 78
    0x60b0a003405d290a0080d150207034007450440d070240e0041450f00340081b81034010301031082c1b0441d025901d145001030402c1895030041914a280110002c00d0210001c030180c00941d1410000031581c0c1c0b0030082100c0d40006000760b5001801d01c800500018030541c0c002c0c03144404555a8a0401b0f0756a406c14031801c2403800035540d01c2e080382007400200301e4108481c070b48051541c1801e60441c80e065413072841105051040c040034200d13443c0b4260969001d40c41d440c5000c0510200350b907842c264503220940c3c81ca20b521444c20765200c0c00b0006402580d04c0703001e66095520aa035500b040190100c0c0c1007106410a41c458003281c0030030001c400515408000d0140721038403490000c5600c0c0703003900420903d40200d546181850f410b0103a106100c0742001303100304611804a98100141e07403141002d404465490700844001803001218200c8130510344681822240215841312440015894107403500c0480a03201b82c20441c28004200016042d420070303584082c01500006004003507840303521880e88103582c03e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 447384658 1250 447383408 447383411
    0x1802090112090302280209060105160209091b03070b030609100f2c0702060402130212101511031c0e10060302030c04020903060604050a0b1003020a091a120721 70
    0x9686604806204214401c007111034803060002c01a00407602407a40206910b040142c0010504030654481c1c0f06442c0d5950043e00c37903200e52510700c0c1210741e6040701c2c900c10080d001d515810ba030300503e40011071209650343c40c103901b41107032200828843c060001400704c0075078a80091010607044400c8407651300038950201403040c4c0450103808a07143c610180d808001d0000c20300100210160000b859a400950549142c0c00b5440d505c880c0c1d00007070050340c083c02d501864980500668042c09114003090301e003040c0c00c10310380304140c200c117903103c0c001d400c5148050f80080c41080480d42d810403810102501004c4041040360f034101d006810840c02c1040c158060b943c400d030610950804110120014a043c2e81c21442c0c01c041c200003a5039804020040ca22507510707440007940303d03101a08240b548007005052001010820361000e801707508410481c07000181d040a000a8001601402d124548946074400e850012122184c2c4146d00f0000c080d18207000141400c8103003200c082582c103a2a60000300e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 447385908 1250 447384658 447384673
    0xe180f061f061704060f061202040516020d050306010c06050702030a0914060414030312070224040201050a030c090807060306230603280f0b09101802090112090302 72
    0x4a469050074401e8580e2440880303101802542d802c00440c030341801c0300fa201c15010ba07542e4a8244060081c140c5813110240c10a0030014140c01280c02045a09200302c0e401d100070b98440c01d651204c0440c0801d14001a445155080d06a501643c011600aa811714010010803072540700d481c00e95205807250704c011b80c8002121952144d000c00354030090040202281c4450304814002100c074000d500400d0b0074450a03a0359031516581c10401c4501403201c2d0700350380d41c7e140307000e12004e900c5903032480c41c0c0218080410b030602d00705921080741c3c1e40318603816180c9604088861300110b0043c100900140140302c5404008151024108404c800824050742c002c22903d043c4051261600500404044110348141190364155111003d40394040700a00c0c00005510344540500c00100240d02480142c034608491001a4103c1e0b40015240e49400d40d050f4009440341c0d6040c0151a009200d4200d5074011040600c1c004211074008002d1940c051418545446906000d181115010748007100541d20241 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 447387158 1250 447385908 447385921
    0x20c10200301170a0b01170d09061409010309120309170c0601090b0d0b0c0a1403060a050d05030f1c0e030c06060105030601270e0c030c090402160818010207050d0302070e180f06 78
    0x403100d030b1070030580381c100401440d000000d054861120bd803c0b0344d10002003007000d40d9034800c2d4004125990800d403007000a0464907400b40040c00d02c800161981c2c03000500c0c05814548202c11139032452500e07401454568601040b2000401000c0d0446501c00b020b800c1d99000306031301c10329140c00ba440080580743da0b405048000341c81101c012000c584800d40c00e10421006a0340d49900201b200d60a40386100c99404900d8414298440d035001a41d9003200400c10b01e4030440046086040c0e0445503504201c58112141d00030f550303020b6204014140c2d80a400025038652040001d1500035006042c02c0740b020304801d501d01e820f484802220246035082d140304003c000e4142d455990041602119203185040c201c1600069110305600c0381c1c09250000b40090004140010f03000e1056002101c464030313030310407a91348071103003407142e51441c014810400086a0751500c02d040349121541600204491850110303030408014008000f000c0f8441e032051900040035050018400d0390700f0315405080c080c87c006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 447388408 1250 447387158 447387163
    0xf0b090f1c061a03010e0c13060803030a06031104060b0d0e03090406030503120708060d03180e0103110f0405010f230306070f02070e04030804031d04020c10200301170a0b0117 77
    0x180307a5846a8145006060040d80c0070039517002200e0142c1d21022315840c4518048064406640320b80b1040c0310000c10407020070055800807003528818a0328a081008290030013054607014011540c0c811410008035418409035440080c1010140080e41d080c0320124000030704981d00381c0d0040e00d250304000380b41c1e0740c1810842c01d115446166820184000c1c144080801c088403048a0020288009181480340c0b0040681e0314900038007044081d8601580c40b450041c0e10b000a0b10000780c09565080e011845074501802114180d600492000490601d000c0d21400c0740318020940e440320080012a815541e101813280034030908413074071620303140034800c40000e240c07203011352091103098640340500c00081c3d0700c05800c0d50000d40620b4140c00440c40c0141c11240c0c00ea0840d89164858030006070f5803030000020440e507000d5499100c0800400c042214104110b610120300301d9940c107420001130200c2404610314044403140a000c442134000b4503662000c80c1030080e08040a1480c1071500302c0141d1808 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 447389658 1250 447388408 447388451
    0x302071401020a020723091603150e15060d0f06080709020922140a06060210060f050105070c0306020c071410091a07020d060f060f0b090f1c06 63
    0x412008500d80031010f40001d4030790003a0300401402001c002c601d10000c01010000c40340307035140185103012600b00610350f08142484400c0242c013203401c2c80652402320320381100700000c03248540502d81c09659045040c5007008040340a144e8892821320801c2940b90300c51041c240c1d16030301030310001000e6081c400035503d001495401700650b0b0340100320740e2200384c07a404241001c20700d680e00240b0380360301d0810488014140304405514101428001c00002c02459040002141c01d0380d0252400e000600e80184181d5209000794640b0076000c1200f00855403043d0010600349014052032034059490703030341e030800b82c2c1d100c5403d42140e0340c41410184520184c10301242c0405404841c5c0d540d4210f40100054119510341c49406150704a150003011910400811515603950080001d1162070091400c440101600813031101c0683c07504102098140318002e142c801e07900710800c0c241c03c1044400400580f061a41031541c3c001484480d22000601000c0941c1c0020380310308000f040b03240320034000b049203051 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 447390908 1250 447389658 447389693
    0x5040203012703080c16060c09050f03120705010605060316031a210c03030d06030507140102070b0d110a0507030810050a0b1b032d070b0106050903100c030207 70
    0x161001420751165402000000d00c0e941818194026561103842c1d200b1402006c100612a00e1000c2d004404c02c0100d03030062055604a4480d0903481d5103400902c501d4030700401c0700d16056804082411046842d0201510015200d5070001c0340d0141c440000c139031142c200340d90f28582203015105128001e900b40c022020f01001c0140094582c0928000082021051124403000e40f0183c15807032500e560b0600c8440c020405c01740c105e07959214128a1100140001d01c400d50f01401140320110300d841660369401c100e8030059004021f071a042c000301c3c00155200420101e803035903032a841030000e1a00300000e842d001a83d511241e88480041c103018002d003400400040400702900003e02c11036684041c0304094503000c01c6050340b5050320780001c00342c604010f45103018a01c0041121009410501c000b20120011566400810000700c60b041e072030f6005809000f45120264001400144e101da8090000d4070401800c0701c00802040054004440c4d0811f52040041c0c1c001820728184000f800c040d031542c96 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 447392158 1250 447390908 447390941
    0x3090e090c0109051e0402040b0d060803090d230d09031209030510180206040e01050307091406010c050a020409080a0f0504030f17040905070306090b030105100e07050c060a0504020301 81
    0x1011070000a02058442c01018801c1c0004580c04203640f094202803d51001c010708119640c03074130b07020003030000d8100e5480c0c0b000c150309210010841d03000100584682401c0645501081804c0380c0d10140b41d505407035200d04403031084460410b0b581c0b40402191811007000c1d190a44020300f10f04000c05182d85070b0340d2200038411111001c200003400043c900d0709a80c1c07611000200c05e0f04140350b14003038642c0e01e00060342c007030400300d808519420b030040300b14100c0d0f10480844096a984030103000130f0701d002c20040480c6810840015566501440d1081e210b50b05c00d106884042040354005030407111a202e0a50f9010800703e4040d0006030003001e40d43c4516075604106041c1491543d546401d4a00400300524244010051100856880c029074007e0001b04174140151b2810f540c00500800c10b6118040e001c6090201980d80b41c1018440c3d1409a40c60b80c2c81e0b000c0e2a4280b00000c1c1c0a07501c0504000d0811000700015406884144196409113180101c00304440c1850700415094441e01e0010b5030004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 447393408 1250 447392158 447392173
    0x403080603160501050a02101d0c011b0f021c030201050a0513080d151a030609011d071413120b0108060115030c0212040602010207170a0507020409050a050a03090e09 73
    0x180070300710b5079a0840e4000d1905070303a40d40010350103e08181c41d00c024800601e0a08210f1940c4035000d9610301d0041c4d040f0000c40d103003401c000780111501d44102289919400c0a034140ca070100e00c0b165107620080e4000307002111040d8540d9442410180300c0841680140d6450040c0001404140030303260700b0a4041c0003c4c03404000c503841d071030194415452400c100651b142c000c1128031444181d03400060868a502c1c0100c03190880516002da0300450b5818400d20171980003188a28401c40001584d1000408250305940c8000c2c0a0381c1d612a0804540000078003400103c0095010341300340e4010300400002d5200e03444191900d0300d0900ca042e00946880d804c1040180050300006024014030344031454040f07461120b18100f81d0401900300c9510701009000100400d45c560150001c2c09014400d81c0c02d801c440d14080d82884d41e43c0207079010038001820801001d00503145c16040901c410380600b05441c580b0131203a039620b02d000607418086021408000f02003280711550000c180d403012040c0003811a6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 447394658 1250 447393408 447393433
    0x14060603030a030b03011107050303010303121e0b0411030901020c150606160f0b04030816020a02030303010902090604090207060e1615140c070e09190f0807140d03050403080603 78
    0x4a0242c440c0381010141d95602c82042a90309400070010b00401030100b69035a10f06050481d100d5000b40419000309150340360380505d4102030303c900807041c44c99060030070440307a6900c0d02c0700c0038024030700d006a4000d0301c41c1c04041c0c0c52004a0002e6008221900c001a911100714075140d0034021100c4000494507030680400907107848500496200c0168501c0101c080c010303c1ca801201100d041e40050700c0d950b40340302004101500150800c0c0140c4050801040e0005c4001d8100eaa0b40244040250907410074001000032030095000307095414001099540ec1c16155004c4004076008000300b9190705856010113051450140300f01c00a05441c03509a048442c10400c408507910351891490040020700d6188070040c007101e000703032860f00d883d2400317a844d8640d8902e042e8a0900302a940c02c4c0c568050070140f00703190340c3d0407115101c0f41039101022208501030741e10344143e2a007102c2c805444941803000c43d518400d1061001340c0d08bc800c2510000741c1070905080003404220002c1445000f07920035103c0105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 447395908 1250 447394658 447394663
    0x10504030213020c0304081f1d0d050d0b060d09060b0a1a03220b0114030708070e040f0c0e15040605010c2d0506011d060d0303110403020a1214060603 66
    0x602e031020309000b5075501c562862103803030351150f41d1080c0e45500406581c045140036650711910b98034029030040c803d18181c25030807240d00420580f40341c140d601420300d0700007190041c0e02410803209a803200003440c245980110703008c2d50080e000e02d5041955000d050003007100f035100345003c000d803d56028489a05003c5031201c01c24038407001040c0c0320300100000e40d00d03481c02d082c80c42c42030b07683d4030030a0301c2c180303040c0740c442c1880e6000c2c000d00305da550240c0d0600c801814001200340442c5c141100a2405924080c05102c400384007030815200004446800c2d00820000d10f207400081c20b0049512215241501d50420b451008400442c41241400c604000340d80c0d0124030069929044801c92401c1401b20700102c0000519409410000696134940c1c41803190208080e412600c0800201e039500301c90700b4440082c440e0407500b656001c0f081c022540003192003030b8807402a00541800c45da262940380d4002450390b058560044956603400b031501d208000d10501c0c4c4080407042c0b60001d0250741412030000e41c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 447397158 1250 447395908 447395929
    0xa03090603090206070206040e180d0c031803020a0f1403120306010e0d120309060e0313210602040e06010219022101060e0a0b0a0e06030a02090702010212010902090f0105040302 78
    0x508050302c0302041c030259580d2204a41c13060fa0b0080c54940c0c1d96a8550741100f0800b021144040004e0000c0a001007a16000c10307401d03414102ca6641c03001200c3c6655084c1c0311340320781002041c69110210b00100058980d066408090118400500a84c515000290b20006115400c0340e0190b00480c10003035800c00103100fa83d810500909140a0b02d111b00404554601d09596000e042e04040000c2d03812032540681c0030062060142d0b00511140030701a0045079213125009e0420050305014004000f4140c043c00154000c0e0a40c00c03a03290105c0c0951614030030f070307000303908071a0320f203201c50b0140071156030100302e64266440910701c9a56600b07030b507400103a11a40460b918103030702000303402d0b14044c10b10207500400c00380c0300107100d40c44c5505200a01d04010415840d915000d280351400104840c003408032000c1c0305030401001041c10105a0742800303900d503000b819400a541d0240102008a0784e81301030b050207020b079990f00503103e0307100000b00030302c43c001114582c0c14000104002d20142e1610603802 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 447398408 1250 447397158 447397169
    0x70806011403011e02041815120203101505010807080f01090c03020405030703060b090f0130120e1e030303130512030c04180209060702040b01020c0d0803040b090a0309 74
    0x41c5418020008207000d801c05a1800856052007020058041d466901400503100c80200040388551204101e03003c1319042c3d42104a0301109031002c1000c40550310703105140c1c1e4406415a000b5820703001040b41a542c0c0344040c490741c0070030b0000610841d42c0c0038101943c043c150b80751803080c03030402120403544090180602d41500e501c544d420048603000e034046400412014003100c130403030303601d0030a60001c0c050741200c0e505c621014004500c9500542e8440c50503100d040e080031111040c2e280c02c201c0007107003a21500d40402c1c203081444010804c141008802000d480d102c43e40020201e404008104d020380101e84036030303060002150104d0300d000003501c0e40081c550407401583e0400341003951034004040c001c09000d480c0001000440b480800290048038058100300341ca940c2200342e0300c000e81c003901e0083c0d0341240741030022401619058000c1d9844a5040c0141c40e5800d000c203020500594510b0001e0f9046e800010074001000107808403954000f107010047c1101d100e89540061410300c03a4803d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 447399658 1250 447398408 447398429
    0xb0903100b0d0b09030f0a020303010905010f06050307050313171e0a0c0803060a030b071e02030423130f1a040c0915020f011805060f07081f050607050a1407080601 72
    0x390742420b00b01704507030a0345400314105444034141c138802540c0364000d00131100300e6030424000041c9880f6822000e016906540c41f41401c640d40c91800b00c0d0560401001c0120041185450401080c0c40da071100e0f03003414a089009a44880041e60031031140c5500200c00a0030104002000035036034051805106550711152656a030740310b178ce00049240304250409441213418000317000a440d000314241c801210208504c907804206880145d841e03010b94850101c02c00040b50102c90503043e020320890a4103801443c1c503600c00d1005007d8400c581000901c1e040c1c00791340380d41081c4210b40705103030300c40048411603040c0202c10f10204020020301c2288103e0b04241c40300f040c103404035070091019045c091002d0b002000303204030080034001800380841c0300b510180152008503883e1060550042e21901042c3ca13016035a4890310002140300600c0181c1050341d218680000c691650350340300901006010b10002c200c00030650a01c1700c2480e804441c142615400404200300142000c1000c9044540003201d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 447400908 1250 447399658 447399661
    0x1213050714010e040f09030801150e010c0201031e1505030c100c0c09110403030f03050f070e06040f030609121b0f061404030314060102070f090c17010b0903100b0d0b 73
    0x60b0f81103001480819030160805c5849101c40303000c0e6000107080d90080d5140146a60703502d41402189240c00680400038182e51003151455000f8140040141c4c030600d4001604008071400464411061f008141265101c00c050180c10010f00710034000f0706004c8003d0055844003a00107440b101c4c17040d50800900030503030190028004804050030040c01815030900c00951000c030a82d02691050000700d002c241c4a81c214078015100b48a003074410034254503016240d8441e0102543c9191403141c030b25500000c1040701180c15680d4840030402148100760114031003103985403900041d801010000f08004441044082210701e01d62080e80c00350b08950a00c5036000b090405201811600c3c0075118540403200500081540c954000407064161049940c40c80e20741c8001281c60344000d1040c1000a030350140284950b20856010390810461818204440c3c101c000b00d8902c400402d80c0584022440800d4403042d605007405508000d861070207040207a49170031320000d01075851140340609030180c80c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 447402158 1250 447400908 447400949
    0x5280302041707030b151e0307090618060512100b0d02041103091501080307140f0106170105010b03010605072306090a0530130909030512130507 64
    0x3030444014280d000810702c0000d00140c005035607101c1e240301c100c66280001c2d00003210a403001c100242c0e4070034000d1515032400901c80d003d52011150382c5400b64540511103002980c6c6481d485004002c100203007218a411207681d07171880c121040d0380d00c540c5c0500c01d05602c2034012000818401c9a00034581030002d020407481c00030500c651804040203402503d041602201c031401540a1031061454a0031603888444c1003d240c41e441b1800c0c03055100f20f0303000340b1007100094560844800b41510f11000c65040c0211658200e0035600c880d8400e00349001c018941d80c030040c10a0241c2400b41c4240e1034501e280d03501d0204010710300c2c41410809032a03141500b004070042005c054070141009606811510107003019070041d40c54800c2c0400450b0144550f82031014101341d80801806540e0801e0300142c9104001000c501d1140e00c02490b40741d9802c12103070f000c29544450311515104602036580d240e120a4001d620022010f40a40140441c1401907021000a0000144001a5020000c86182081d00103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 447403408 1250 447402158 447402161
    0x1a0705070f061406030706090501050a030b0301060b03040c0b0301080703120c0209040605011d0103080909070c1a0709050d05120a050405040204030b09070501050309060f04171b0706052803 83
    0x5001011140e0301d942401019040301035400e06028401c200354840d60209550340308039224100c0840c2007004104403d60140d4060000015076080100f01845010f00284c00c40390140c000c020007150110500090007040f003c44805495146c40103840c550400034015580e102c148001854007494005200e90203101d400710105984d0702800545003400c180c640203010f0802401101c6010043d510700c29098250350a015040701e13048851645440d403050240035800700c0040294044c055050104030002d2819214403084c0c96041944a00f117040100c0001c0c0b0001d000c2e0b00c0284a500180001c901260010810341041401000010f6a50f82907800a46680c00303240d0015512070f1003c1800030502c01140241482103410314150f0728800d480300010f5036a808183e400280a40c40f0100041078101d86110030382d0410b0040c02524541e12607042c084056074002c200c00d410008074880c006d1041e500800074480904143d041c030a00313040d00c2030a041240010400b1440995030501b030b0318118607019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 447404658 1250 447403408 447403417
    0x60c030612011803030b010903030e040207020303040b0a0f1d1804050c120102090301050610120c050f0c0334060515031c020c040501030209010909061b020a0312091a0705 75
    0x7010092003000d000c0c21110a0300f12016105601190400c0300c1001c40351f200761180400c0c2c0307034107407501120a501f000c144130081d08142e100300d81602c0200000b1800b0f00304d010181118010700d42d2803207511161a10b00134107025410007212011007000d880800d160fa030301820a00a0280c0400345881c1303680e03900f00079180c040391081c81c1e50000221084015901c0042d001814150b070260300030b00c510307210318050013002000038404000242c6130000d41540007503150040ca940800518196042000001c20108194000b1055807200c0e0f0000a0001d01c200d042c181c51410200c95410b80541010202c060354014208171000405031a41d91000903000c40c0709000324441c90304040c04481c01c0100034201c3c4d008a46d14000240058890382202c9102e80c42e142c0241416250b016100091f6039103000031503805015507460403140f03181c507030920500c4143c149283c02d0881c0b986a000741001c0700c0600f800341c03003409486400144a4204021880450700c04242c011894030140520ba82c151740f6400100c445000703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 447405908 1250 447404658 447404689
    0x10507080115020a24060f05010e130902031f0507090303120e0a14240c0702010f020c1216140d12090905090c1002160311120a06050103170c060c0306 66
    0xc0d0070014901071a02c180d2446940001410100039268451f001e1034141c082a01c95180055102c01791591682046074482050f030170441e40c0403c7c0015540c2c0080d0401707804030400d07103814001030543d060800045c0121a0402d0b003509211848038103540700100394580d0034005441060300e500c42c0c1440c6540410400c070b14260000010000707040004002c41d103e00c00c0d80a0482c05051655a00e050700c1c262042c1c460080e120000b00500d07002c032503801500c03000ca12041318401e50007014900401030322200702e0806051100341c054410801c4a800c1414007504940105d540b50003840490704954469484940c81c00b42c10540c0d00030a828018811a5a464107411481b404dd041c4003d118400b00c001a45201c1840d040750380702840303045200c00300da45040c0b4081c00f50304507a640808101180401c10501601c4002804400900c080c10710319900d4820101d004503030144d515801081030118401d40180d8010002412500c0c1c40300341b581e595983ca138080d150040d4010000b0210304503564400c1c0ca00a4003c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 447407158 1250 447405908 447405923
    0x12170c13090218100207150315080d0c26070f0f020d0c09060b07021806031002120a0606050301081e15040f020906121015170a03090503010507080115020a 68
    0x1200d50340d200f440807019186a034068802d04000600c030b20300100313250090b02c1e0000ca04a0040b00540402c801511a56554401c100184030002c601c506003840f40d814814840d440c0c10300540c0080ca01a89854800a010107040c10700601800c0c00d00180c5045071107954002207501c0b1030400b5400c200004046000009603c817581c012810f0812a101d2040421503210000822101d0740d5203840c04a40d02c01d040d4000d500030b0710005803040e05071054035400e41204006e4221240d008800c0c01d810300b280d10460803100046141410001d915215018010181c5014940181154034040000b80c1e55003107002241e40c092801810382480041c10085070804003a01d1744120030750305007414448100125484103038000c2402e00001100e906010703003001200103100000b04111144001448000d00c01e0460342c180503620100c00003440c0c50369444100318890104040c0040b0f034014036001d0510340c015071205003e64102010031250941110185044603905003008242e2034500500301e00300080c03410010400d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 447408408 1250 447407158 447407167
    0x30e0f180103050c01030504080a081308030109060f0f05031504060f02040e07030e0d0e120c0a03050c030f1f09031206150e090f060f0d0c1212170c130902 68
    0x460060342281203a002d441591130003c50000118180ea000712005800c01c041040400031007072085554550111103206545c44c244e030191307030b0400164001c0c3c1c0908c0c221500c1311010300445000b101e86000500203030846144607031509000c6511568000185500402444009402d01c01e00c2d410200c003514000804550b904d072204a42e030b160350f00c00c0d10100001703403030443c00f07003200100050403e0b1601455216034030100c2004003000a10700d2082030f0148580900017040740207407100350300d6001451145018040e041e0000085c9032a02c1c112402000c080e5100084168000211803405a40302601341c0000c04c410320203083c240c800c5c814950201d0030311480e000c40015201030b0004c2503040b009035542d6594151501c1030170408040070583d440c131b038107581441c04a070301c034908005160442c00c806400e044050f55607440b00000240c40d40e0120100c1404066918100500b00c00400403401d41d41c01c1040701000c441c0240c070068100148941d01c0c00c00006a02d015200c103500c0484020084039005544d507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 447409658 1250 447408408 447408439
    0xe0408120c0706060501021501091a031b0102010e03041a0a0504051206040b0c091c02040912020607020601090c08060108070504080f01061e03211e0e0306010806070507030e0f 77
    0x1c0c2d40003000a503519842c0101c04a059071020603080c104003885010b03206164201282400100410460403855903030030201c8602a0b201406802c400c1c2c1180500703490b600b9410070000e42960140c0c00985282d801c200014003620114044c911074507141014081d8480d80400c909486612540d0809a8045903001c4212034006001a542d4400d5205030b00307105c05915440602005c600900500507800034503218030f051081c900f85c1441544900007440483c101480e078907a641c06060b0080c11100603000f0700108030781c0540410039607005020852081002d00044e020003440e000e0090702190401156a001c9101584100300303640c00b901800d4117a40b6203880301d400150081103144542e01200c00c0b0310000480c03040c0303907400c5e090442c0e401c140156110410a400100340c0d419a010400621000203030840080c503181490500130545034a51200c08002c000416160007016408111035500080410102503404403d90310a580d050400035000c18400c40043c07001c1c10381180544d003002c0c0e0885c1a444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 447410908 1250 447409658 447409681
    0x30f0c0c12031206050f060c030405190920040501030513051204140f030312040c03050307031d0904030f0f050c010e1e01060e1512100c0e03010501050a0e040812 71
    0x1451181c3ca0f00d290750b0140307401c50801e60301c142c802c2c03550040300b00600081c9070600c00c008000f003168080649251540ba03600099401b0200c60000517580d0340c0150038049903910b40b00d912520500407500006408801601d02164450b5002b150704040c0c489010503140c80c1c5001c40710766500e03400800d440e42c0154103181c0c56602d1700300b0f10520030700003000000510142088480024003c40c080c1c040d61502c80d14a401075003802001d4012074104000400c000041642480035241892081e0344419610001d1f001410014012a0213648684466010320000907040040c09803041000d0a0408110011a00039a854003600c0e0311035450703500303000822406240106403540300801d200c1006070ba900303a00203004d0803540310340540000c5103000d10120b0080c000d41c9143e00c145020080203041c1d08004032400ca4100030039007910309500c58850650000e2541c015070207251400b0290001c104d20344c075081c009200105070784a903d0700d0088034404201440030302e100310f8180f61500a640925411318034115407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 447412158 1250 447410908 447410939
    0x50403020d09140a0e06010c1e12050918070e131d0318090c0405061602010318021503040516030b040c091103070e0a080a0c050a050103090f030f0c0c 66
    0x280001c03600503010a111029040c10543c80d4006400344c0d00b46401c140d00c100c8020170207000c031418451078441c44000954880001c9202c0e080310f18400c02c0c80c440f40e00d07010350f081844034800c9040c08001e114006554450344c3d880c0c0120007915540841e507440b658420303a02c0194000c050f036040f80c401030100000c90110b81040304c1c400b901c1c0c06002e0301002a080410744902885500c1040c901a1400c41400352404e00b05407904074110805407841e0961390000100d590340030a2401c15001c0c0b01e041c3c0c5000395a00f5209000f048010b95901490230055580094050380c040300810203031442c0031012030f003400002c0000080c601c00c2c40d031001003003507103a040c550240c1504690840d4108240000890340400d20300607240d0741c40c2d54107025400d43e140c0c0c83d0280d90303481c5041c1a10b50040e54142c0006001c28080241d0b000b12405094000d0b10f0504003014080c0320280b9422013030600d801c10700c4801c0000c200c40c886024064145c41c142014400242c1b0803900c030b44203d4406001501d90031004a4546408840b03003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 447413408 1250 447412158 447412183
    0x110708122a120105090c18190e061e030304230603010b04081605010c4d060f090d050c10030e01140c0405012001020f12070221071505040302 62
    0x3080c850b13994004200000b5012218010310321800c2c406884490300058900c1c009001c010503449440401d5142c440d0342071160741c40b0070034403105141440300f541401e111000080504103c090b607500500307008603135a481503114a130307450070340c0c5801e082e6500d0b050058100300d810001c0106640f56075034080010290021b001e00c196a0092520100040350703100b10b40300403030f80185c640c2c800e1010541c8640380608031040c186000100a86845001600d900e4400034007200200c01404c02c1d29003290040700680c5c1074144450207000e081254042c507960803c10b031524008200c4d61984906400d20700141050813003100c0b15003054015558205068040d005184040082c0008000320003260074a80c4c5200c0c0d060b101040101c3c000c100920031544114800b803207400b0220707005c1d001da0480342541404c9902c0591242203041c000318969140c10b203601c0b0280c1e08885117100801d420b0050b0444030a102d089843d004000e032031b0020303120301080301c03d10180782c1010dc1e0782402c001528290401944a88901005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 447414658 1250 447413408 447413437
    0x705030705010516091a09030a0605091e0106080606190e04050d0311070c0611011404080304140706020303060f0409350403110d05070b070c0603110708122a 69
    0x10410f49201c1c07400c1001b1100002c0c1c00c40740e0b001c80200240403550051002c41e8140c0a54030580000c03a1441c09041c0c010305001d801040d000601d4007442e2000300600c08840016410003000304128400003810907000760007160444542c0886a42001409016a10110040c4240c0041005000000c22101a09480354909201d0601c040da0380184c2480f03a840c000f0501e40c8445001d01c4060f1080d0b4102c80b01801660001400d51500e0115001e4540102d404642000001003000704101000070700010f101040030082c079405081c0000a5264080101014001d581e09210440c1d00d0b6950b4000c9002a80c000d03941412060b485c4c28150510403500078444c24040c9202c0740200d0002c805021039007100d801011303038151507071380004200094441c2e01d81586e21f48224135000c507050004c0d0006100c1540b0a64a003440e036883d00d2006802e40b0030102210710200c0c0d05001c94004101c58078203c03038100711104c82808031a80d92080100c181c0c2d032019641c03150700c80840450394824002400402003203071100c1c80c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 447415908 1250 447414658 447414691
    0xf0b070e03160e01051203030f04081303060f0e061b28021b01020c2b02042903010501030c15030f020c010209091005010c0803090a05150402040e0d1409030307050307050105 76
    0x600021b002c0d074041d5449070f5401000000c43c42c8034841e02041d04103201e0000c1510304120303881950940030040c1c005032011a51013001c0c0303c062005100b05900e034407039440a882c4900e4502c1c400e680a1901d094904880b450004100303215030820010303900b41c080c50400303d0001c1c2d0784c20180203680300055101503009030380c240740c081090760000551b85504040200b0000a01802816404415440c0c0c5c249000400410f884100165611300801c1c2000c55858501d81c54402000010440901c45204160003a4942401400031505119000c2d00351841000481e0301d01511000c00c80c000d14801c4030484106201044402c0e408006400405288004803002071807910b54001791140c1031b0251050078003050b45403003200001003480000e5a88000c41a041e24400c0175181c4869040155440301c00d00b503600000100800c6103058400c0c010f0080c40780000f0542c601003000080d244c10040441c4071404c05001c0b030200748940d8100100d88415074060290380c3c403101e00b441e1040c0a040207661010b00384c0c04482 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 447417158 1250 447415908 447415919
    0x130b060d0602091e091e06130b040501141305010b0702040b0123040609080f0c100c0c0605070c0b09150c0106030c1203110303041106070c1e210f0b070e03160e01 71
    0x41c0d20707801146e50392030388a890344400040044600c40141c103880d000b521041c0070800365980d031080d24000d20b0701c02c9071101800080410000b01d911070300d40303001c040351405005201c42d2040340b01b510125076040d00d0005806050b2401600d030000d000e04018076840711242e491a112012038050701c1125003544030090000e0f111803160352103030121561004c0701c0e4880c242800a5152100c026100c10080d0b0510b80c420500c03a445100000300300e0b03004000441d200080d450308102070340703d03030340d0080c5064985e00342880408000a00320300702d420b40c11070058102064850980d81c007075001c00c004590103200c040103030b9a42c0d12181d6404800d07020079004540c0c040101e01090740b010080303c0c0300b643d100c48015030107008242001500c3d04240419900e50185483c0413034901541207191303a204c14000040c0300d51524240b2086400f213114402511b040e00040803100024081040002d8210b42c800003821060741c915a00b1540e172913141282035810302c40c9621607447d201d0040300c84003e984050b07541502aa0301d82 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 447418408 1250 447417158 447417181
    0xa0f210f0e28021c05030c010b011704151e0c0c0605100f09020705011d013606050c120f010f08070b030a150807060905030105130b060d0602091e09 65
    0x10700c012820000482d0710840140740009003c02200300c02c0d42c401d44810700070703243d15185030058441003005a5440c10b00c10280c0d0380142e0100904014590035044518050351001c0300201034900c0c4100741c03a00d0740712038142c4c1c0b01c12246031820b0400150040100442d48000140300700803551083d14540c1c46c00003c10720211052662909070f036040c0c01a0840b031464031440c2030080d44460340544040d540c40b40141120b2441014600030380d10410000314821056400c00c8003005103194000340010180d4082242d85940b081c490f541c500d41120001800e50f5907120701481c148941003108400b03205440800c8211100350040700e05803100002c40c002015250382c003690760340216014a1240c040248005404c2c401d103074000c0f0582c88035002c0d0240350566074981031494401150080004181d9001c404e0040e17007000d00c185603201ca2851401105208142c40c5c0700079030b00c805090103005540d010104024040e02d41c0440c0c030528000b42031a072480400d40443c2d18807401219100c0c0c81600b83c0740114403c081807 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 447419658 1250 447418408 447418453
    0x40317090603010e0a06030512040608070e090601030b03070e0c07051005070507140a050604052808040e0714030a0504020f030d02101a0916020c01050a0f210f0e 71
    0x1c0c140510b141d003880440926003500508103286161070b01d01c0400024002d102810f81c0c0e00c404103246844a081c64805408a03100602c0c420400c4814a116440c0b0b030380b0210020b80040d828280002ea01030480003080c20304902d5045128090760341810710180c0c20201e40140039090260041d9058081503001c0d8009440c070a448120024105010040200e50441f0a080c0905441411078215080c5560344500b000c01c00c40d0142d4194006600422950604000540241c86219460000020705907140d00b0140200c0c01038203420322964000441c042e000e01c103108024266040d42e1600e03442d01c25680c0002d03020444041740910b0070080100c03c1c0d41400541c4825001158000c3d01409224400d081d00038138180301103110250206445a216480c0c10881c1d07405220241e001c41c1031b0b010310034230203444e0507000c60029040040800c44580215445401c0c4400400e4525004280e4814041038060318140c02e101070089030300c0e050420010040560004400c190104155080496078a1001d58000751 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 447420908 1250 447419658 447419677
    0x1080d1407060f0b090f06010206150a121a090a05190b062b05072c010902131a0703030b040608030a0c15090b010e09070f09090c03080f040317 63
    0x42403000c800002d02c6a00142c42034035911000050b00100d01000411a0350140d0710142808950000c0c05550759051003ca0ba11580c1400403a841800d180f0104070303865114450482d00320545d0040030304121401156908000401a0510b0300c2d050400f5a0b54485400000844031482010310084130184038415a808a0b41c1103003001d516030351010140030011840d007803280002071190300c002d810b854010404500705030007500209039003420060a6100e900c134081d140150030107200c0c85840d010b0556442c10741502c0c0100c00261700e41c203000e001e4039026a025004601644a0304c0009012165088050260f0f01d010756014801c04d40c1190500c000ca400354065444a07400c01c21080007182e015080e00ca8625104491000e44c4541986144040f144a50021035044280b20700411240032a060782c140c00c00740c080301800070300d40f500500138408e038128843c8009880d19540030405200c0750740440c100840e0004203056a4110b008240350490f0b10600003240e1f401c0303142d03c3c1803100480e0303031055464828 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 447422158 1250 447420908 447420947
    0x11814012706020c010e010614090901050103111309120f080703050907061103070204050a020301030b09030a0507030e0f0904060209030f0718110d02040605341b0803030c0301080d 79
    0x2407090b110b8502039032041c100e500043d0740b00d1072400401e45c8244910001400c1ca0103200451000e100100261808094601c01c42681048010b202044912004c4602c0740001c40d071900c0104c5126803464080c0905d03a601501400c80358111500c020b42023041c110402d14240d58003685942c0e4544181e0444806440040255100449c24403415015800810100c205141201d040c1226130f03002030283c803c202c0306586c0003a004801042042203440f200342e013000003c4061401d1482700c1c8070091180c02190006001c00400404503103c50310b922040c8294948042d0422101c0d2400d81051f00c0071f5884007140d28060b01c95111583c2c02c3d84004580d0308151449401c012914032602810f0074054640c028a250001c641005998000ca415100030300c0202425151103440314100c0030042e020804455225508650030503072030001c1040340700251a06940070071042d03503444640200049082c613680001070310744800000e100b03600341c045000e0b6048455940896034100c054520880e850380d034800300c1072402c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 447423408 1250 447422158 447422231
    0x50d030f060f090212070503010e0609040305040503063d1404020906041502100204051804081c141305060a021c020a030914070807061101181401 64
    0x148240c20154521004030008511075445540408900245034000100d0a50015294404803a00c208841e403014907401c1c15419580b4000e4050100075008203d03503c0751003c1e900040c1090301800030f450152001404903521481c1c1074000e442c070500e0b080c0400c540050038241d822022050801d854402840b59004d038850645001e91503488500d46600c0b95034816001d10910100d900d40f040608020400c050301c0c003152071b24410019042102215103000303010700401c818810382d240d80c0c1c42008200d080e0082958180d50303c1c00e0028107402800100703c4002c030b16401c105401e0015030001c20907052100e114222544445036100e262100714580209990003203400100010030950103080907044810807060f5000d2030400c500f0072030740300d5010702010943e62024803050110001d49020f030410440c00810348141005c5505655010503c103040c100300498030b400c1c3e14542d0130f401c1051640d0780900c42c45160280382c5881446030605100c00d884c03a45c604140340021003000700c1c140000310a0b41544800340d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 447424658 1250 447423408 447423433
    0x150605031203090703050604032102070201091512060915150f0c14071502010b01110714040b060d020a1101051e0a020c06010f050f0301090b1f0801021210080a05 71
    0x72034200806110f49070080c1d09002010a030140b210030321540c8256200001200304c1d11400e030a900c5940307406440d952060180c880140d0300520910b0a07a0703110f4030306042d400e480860031580d09405800e0485203a05020b4001140701d0260030500c6031030f2070310170451000f5846940503038101118404520000702060f04144045005e481c0813612140184401210150400d4441e840c2c00440d0f441000302103509013503819900d5082c030034490418400d191080304004581103159854402d4050300c400c040031032160082566655101440d2058094000c0307403940383c0c915070a0001d4100c03540c00e401060680100079041441807040f24442c03e107071002c00841080000807400454401058442910307800c0050600480382009164000c000d07120020345454241406d1040012494000074001e070304001c0310074005450051041d9101d81d40825031a01c50800303141c8444140c0c001c0e4000140c6500c0000e1072401c140740c40303010074405e098030440816102da54902c02696410101c0c80501141c002c003404250 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 447425908 1250 447424658 447424693
    0x1021e090a090921051603200d0c0b0c07060912030b180106030504020d060e010b0f03030c030405040207030e0a121e03020309090c19052703100e030708031315060503 73
    0x5071040c0340c03250500c20340d05450035046d4103070181940803400013640c0241032081c04114441c0e2111035005480e900d22981000307445690032200090800c1070300d40004820505010a8601140d00900144456400c600702040100341d03100c1d03508002800c0c158000c9940c01c00a41e40b5403541c0d0440c0c00c609650703103010003c03401000084c0c8102c0c0e02c6860140080701282c41d13030042c200d9158402000080b0310310440200b03e40c1d000301d40c0140d4040d1300140003264036200040162800c0b1079003602c0c0503985180c1842c1c1140c01c00150407640794021520756000c150000419048008544a50f0b10041c61410901020700702c22a10032004005910405c80c1d010b8508001c0308241d0450041400e0500f0140440b684202191289000f400045c0001c51028108441500c101c03880c0741207038003025803020001010944034450308240c609025114003450014460030800c4503043c580041c0147c2c1c80c4c0c20b10819000c422602c0640649100c1c004419074091170070148100411240000d00034240141000395060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 447427158 1250 447425908 447425963
    0x70807030309020607060b0f011805120a02061c110f09011209080c010f1406100513080106060f021e0706030b030f0f06160e06091201021e090a0909 65
    0x1030425894488180060322240c000e40035051040314081901c510000134000f40141c41d04e041410170107019640e448a59101e1035640580700d00303a03000da05812003800c21601e48000000000c2d08000000b0b4001c0b042841c01040800885507c40248942c50300701800381d241d80560440040010400c110301f00056000d12401100d12104050124005415885400035074000414840231039442d00c40300780355403201d4414520b507603805100f4a021802d00038003040c00850320304c0c035074003d100c0c00190001c019003492418400810000c002400015241d4200501d81d044c0502254094400e07800b4200280c850b0468a05100e000000207012851500308110080c002d02603600d6054000c010b0030a650f0301d818001c0c000043e00b00001401c0ca07050001230310034128400c3d40440308011050f114411566074a00486944442c212544a0b54003a21940640288504990407034054080006640169900c9002c0d00403c0c40898616150750794502c00b04060f1098201c0080004403000c039694410012001c3c42d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 447428408 1250 447427158 447427163
    0xf07030317060415060503150405090709020702130c0e09130b1b0c060a060518090d1206081905010e031e0a05040e0a050103020a050f061204051c08010e01150203070807 74
    0x7158841c01040c0503130201c04260083c3c000504000200003c8280100024000e15801d490400546c58504030050300d6140f9802441080c0e0740002e850425969540d1980e400d0141c001020803010040c0c15020701200300e0035258038041c003111800115885036842070600e0300354002c10342440a0395141003c800c8140004242440d01000788213045024204100c0d02c1c1c812614a0000200780303090908010203918040c00c1d0f401020b524900300000c002c0081071951048409040480b095a82990128090841508451824441c1400d24100c04020b10f02c00070029008000800c001120032806503103910402020701025658070324400e402c100c10b0401464202501d02e001030a0913181c4c0701011454030300741c485980c1d03517403580014020761600d185204018042191440c802c00754010100e00300d40946170001c3c840040c00310004040c040c0070b010020460305010124124007880200103400d02d80c082c003030170044005e40000030640d8000000214000d9409400550503d9035070743d07595002d46d1104004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 447429658 1250 447428408 447428411
    0x160f050708030708180f01020d08040317070203070b0610090611030f04080a0519020a0504021c060603090303140c04050603041b171915021303020d05030306030f070303170604 77
    0x1260794061020340001c9100321070031640ca1400c0c41581d0309203035944103428803880c1c0043d8082c0c016a00090741c000c0154190030503035400e544504040d074044203e111070a00d90582d420812450301d50200003801a54401d501102d2152128801d003d480c0100209150209500729014440355000d00c01b80a0f03603291010840785440c0400c02c102e801904180d000748400d5000f4226002000814404404400c030f4681075491500055000120601041c0c807a5a0040707600150b20000040386a0840c031481d42501750500c2031607520000103004010301d03841940000c0c540011070311000000040c0c240203c01008449080900f45000c01505600c05401110b240031800b40b01790702d50031514010002410070144d244050900c100226040031520048000030708290300e25100020001c40c1516081d0488030801a02c51201c0700c20f080c2800c45507000a540503019609603020040000011440780d00c081e4251284455404021950380d10300d40401804140b40306041d03111058101e1155500c035000030300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 447430908 1250 447429658 447429673
    0xb1e0d0204030b0f070309051209120115061d06030115120606050403120302130303030b0406030206030f01050f0a0e06010f171e06032407021e060603070506160f05 72
    0x500500326441540304a0b080d03e0301404220203603000c8162103a01402905040c031a201d01d5a5815803540800320b03130308800400110340f003482600e5040e20501070f00f000100801000c08600340030124565580708072000941400e11301c4040f820304080c0c2c280803120243c02d050450f420460190603442c03400102c4020099500c0c48800024030a0040303034001d0080e0b0f194140e4507400c6052403c40c03104041c3c070703620508d8010017050008da25219000030450b6014030300004c80175007200004004e82001d07800030350702090100c00e20005592109099040790310031951042e00707440a00074418840d041d88515400300c40701d000090306030f50052206206e201c40b10320344451034605c0040705d0034050300d095610002180d044030311074201032400024113030003010882c0100b0011840d002c6040004003107440003078000030888003241c0074500800105507801c0b519001c132280381c1000360010740c0d620070441e000f0b0720a1181513000645410444101c1d1400ea886a811850b4000c040c0c03a41c110620446d01c0c1115544610316 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 447432158 1250 447430908 447430927
    0xb03060607170405010807050a08061203130603022205010203160606120b060f0f06090103110405030d050a030c140f0304020d0b1906050a0e01150c050d030204050414010b1e 76
    0x742e4145101140d0614951180d04007000100302d400010141002c0c1710b01000030b00c4810784c00c05c01660340800e049600040d0448100b203618210700034000741c10340f4070444e0200450b0241d05500a0020112003080c0c620320200c07505286d0b290441036209950150300200a980640030305181600312a034062040842d9251382c030404a4590903801c5415545d0b19202c0c02400001d1421600994083c4c1c0304850494400c003c9000084452050302e140c60305040e5103442e001d4a03003450328141c60080c04010f041c4d0f10004417001001c0c1080d8000212a00001d01d4030b1899002c2d54020856400c05800c80c1c55254144400800c00080a80c405001a40c1c010040c2446000240c4c0700909580b14050000801c030180300c940c09500181d400d1500401e2060345108400e2202c0000b043c01c4078111a110741da114581d5000d11400da402c40301c1c591024100707000740c0701d0b8100752070b4154000300100d40c0166020081000c0303803210441c44007028040e14000040421541011140381d124601620f690070381c00e50316044501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 447433408 1250 447432158 447432173
    0x2040f060c0512030708012309180708011d070e16030207030509040c120c0504030b040816141b040b0a171603050a020907050f040303030c050c0a03020f0606190b03060607 75
    0x1c51700031000444160040c4004110a200e10602c1b082c1004580144078040000642e110801011209040703403042900307010500c01c0144100600410f0001c1060b00385d121496281089080280c051600c034003000080d000c0e942d2921179204800742c0c00740017041900400102c0180d44070503419405c00509005400c1c1555071485148a1785640d0340350403074819000d948000548040c41d80070350a10001b40010000700b1004004280e019034080c90342969211020070070b20132401164009840e54504503502c004c41e903800541015444e1031040c41150201d056010030041c5c40540c500c160704041100002c0100100d0354401d0151601403000b9102840c1d09400c1904905560b41d000391020f5100c1424031041d8204a221150000080d2030700925200c04001051100c0c415488000d08060380c03800702e07400852180d82034039030110881c81030700c2c448080d42c10000d556920401d040119405200302140c80f902d8010342a040c10640c69200854103450004500d03c1070b0402004250461020001e5600003450b2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 447434658 1250 447433408 447433411
    0x60308030f0901060b040b03010b03090304080f03130504051e18030c03180105090d120c080316090509100306050903160305040609120c03020f130f0c110102040f060c051203 76
    0x418615081c10310346808010b00b52013840e408804615410070003070004121b5401142d040d940801c110666944401c01074a180d4400c03907220326813038001e01d00140c4288201100804400700c1516108001c80d4544040100b00d03103080d600410400959281d010044240380801ea600c00e1503c580c00c81c425088855550071944560f01200c03040e0400162104440141041c2d9202040c0a29105003001d84245c0800d05110a21001402c0440e41c4003c4200700741c4101c0c004a40c0580c8041402c6d01c0f410000c80d146006400f000904012502e40580800e8501f007050a80740b2845515078582601881c1d42c9946004080c050940540d5010030419005100c5040f030511344224401c0d901c081d035a5151100060914005400480f12150a0300201c4080b070b19500c504d0701130b07a030100e820300f221511803400116404c1c40840e1a40c105410041100300245c035a40c071460303400c101a01c03a00300010a50030614201c1c0b1035405400d4580c210315400b0301000344030f0a25203030203d1140b021116201942904150103810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 447435908 1250 447434658 447434671
    0xf0a0602070501140a0f180b0a09150201090506061309120804050f06070e0121090501060f09020322050316050309040c1d09060d020a1403010c090f1202010306030803 73
    0x7500401055030f220078074600402c14030030300d10b0412400550041901c2412a000350030840217901d40340009540c001500d004094640c01c481e626110f4880282043d8818401c4c48104101c0d180c0c034031103090060003140411980400a0304142e922901081041c03070042c544520480e9442d000200042c0c00c18441c2c401c014050b45402c80d1500c1d013480d025182c80d010040300c21141c0c004000344007500703400000b0000c4040c1c003400d02c60030b207110000301e08018501800d504014a400d0075040000e0000c103602034401c3e00c180c0e10b0110030042e1500040c0080e84810b958038541951a008540c100105036005414074078842e40590781703426000d5800703d0754a11801025074843d040003540c9425032500744a2801161940d06100d0240a018400b80e41d00740000303812a03004150580018540395184810702c24400d03801040b0b114070a40350004841c4100c074001e4054001c0d1700e00001281c0c124000c10448080303551440e07000750340300d00f0300c00711400301441044e00324141510b42c00f0100000f8200c201640c400c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 447437158 1250 447435908 447435913
    0x141203131202150406201305010f030b09010b0706020f07060507080105010c0320010b03010f0e0105010b07170c03090604060216090204060f0302130f061d0406140108060f0a0602 78
    0x85410035801d11080404101c055500c03243c6030000c03c400444000b640b040c0c00190014032032021450354803801c2440d00c5600da40100010b40d95460710a00001c80c0140e40c000c1e600d04d5003003004444280c3c1240c03480c001c40381d44524180c1c0100000d40c908002056054421030010d8105401021004030079044003004580c80e40e01c0310100a03255034801000c5004007024038040c490030a107500c2c064201c803016502d9030758800d400007640780801b03425080002e228a01070000c111700809030095100422146401110035428407000080700e080340c2d0203031402c094001280b8009440740781207050003640100c001c3c07070315808140285825959100040c20003003001c0d402a01c3c4411020360752400c00c0200d0b4100d21452803050000348040c80c2d100c0f5000ea180101401c0050340c6d0079040300800e42c0031440360f1004403483c40281000c5085c0d80c0c4920354a400d99403042c21400e80c5500c2c07004000985916000d002c0c07a2094070903826195611401300c0c1508a4006090300950352068808105500713840d81090025a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 447438408 1250 447437158 447437191
    0x50304061b08040f06110a0c0302070b04050a1229090105070f1b0203030708130509010f060c02280b04083a050f030a0903031d060103141203 62
    0x400c031070003404880030749650505910203084402030321044014001504121030501c0080c01c01400e5404450200d142c17030b103141e807205a07205004002445018085005010345240054004603003820399041d034800410b003500041c104084901d00b00c500310010313201d604840288071204691881c0110003521a040085500d03d000101113003542d4028180c2c808008910032550013030741d804107551810040c86900d01c0740409090000901d10700170000c0103406400d00049070b0094021f5040000704440090310203810607070340c03124609264a20782c0b2031130f008103c1c150401001860025200c1041a40d00c50901107442142c6a60004034130850f0021085503c0000742407041c0700e03080103900100190700006500c031401034199545291b0000c10210314880000b6182c1300318038010781c15642000744448c3c002c0e0702d0b8a000c03a0210041c0410b20800d4000c2441c09008900c255400c03030681d00c074010031000074000ca0b442d41d51182d07102e81c2d03110b100d20a81c0c054004c8524001c0586402035010340501c104103600c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 447439658 1250 447438408 447438413
    0xc17010f060b130308030601020f061005010e0d080f030c0f07150b04110702090601050c0f07030b06040903051c0f060f2c070f02100608060a1b020a0f05120307050304 73
    0x498207280c0000d40b2103102446540c50603c0910925410380e54084101030b00c980303c20780140d25181d401c1c441d00d800b9000341010803900c503090468001c1104c0c2d00340d80707440740204c0c84018072050401500000e09001810000e00c442c00c2ca201c40116009401c081041d8600f50501c4e210111070f41208104440944070108100c0030000240100c1070032840440301007041640001c511070851041e004001d020301400c0303000540340da000300c00342c540000400098400605070b442c60292214400d0000321340840d0164086101420544110035680d0351548545152078400400c407040401c880e00d4088026480d0800d0f0034500c0b5030b50192100428032a600c0740c01c03250038011002c03240d0f91907140224015078800d06c035025021881610300c3e0005c8d2641091001c130f00d0b12030822400c10000c1c17010101418240707200040c0c2000e000600a208100b0007400300305048200550b015440001006440141d225a0026003c9408021031941142c440c10450760b8442c083c4042143c80d800444511000c541c011080009 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 447440908 1250 447439658 447439661
    0xc1115070507060908032709011502010c050909070e0f1012050105040c0f080c0d18020f09040201020c0609062205211504060905060f19090f020402070c17010f 70
    0x14198a08040e00f03440d0800c1145076490081408041d14501c0046504055401070111f403500b0a0001e89800c1c40740d1703115038101c00140d50001541005620300780217003603014030030b106480b000c103802061154a5110418100c07201880da55070f180e400110b07889000c2c001e0781c80849144c48140b2980b204183c0302d1081d42c2c1c450403244164001c50286040002241c1c409601454051030000c1034203101e0400e0300c440d5101780e160b00400300044ad6280c80c01d42c454051031200d0381f41c143e103540f003102c17450140c90442e070a11400d03007000d80f0000c1c09a0f002080d0f00506107002c002401c0040c8014200c9810504203034040e08000c640200500c000102c40b5805120318140b8501c030015088140082200400541185640e1000b003640481d10180813980032504002040e00402c01e426085800c03159141003518900e15854016601c0c0b6152a004200340b5655070300902400d050642c001d40b050040b00c1154003400040d43c000482150402e0700714002180c50b00140010083d08415840000f88698000890f0300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 447442158 1250 447440908 447440923
    0x1314100f0c110303010303110f121801050c060f0712060f05150301030b010603051b0a08071d0d06050403020c090114040609060e071d210607050f0304030c11150705 72
    0x41c02c020a01860582d440d0700041141c1c1181c0e410700c2c200040195091190b41440b0300140c2e500034501034840d5102c910b4405901501c80c40c590b2003904620040618015907040c031030003500d08100c0d04a400011403150002c0241c42d4420700038100110443c95220420044808641140ba62940207140c144118188500e007000030314144822179141d03505640300c1104807481489400300f050b44400019113403803a02c0107010b07540c2d68040819504c42100385c0029088200031100c480025495424101101e45202c202210b090b90141001500c0ba02070b8031004081c001c000c100350154400c00b0200006a00c8110800d0300034500c9101c00d9000e02281003c020680c7d91381d074000d440391030038900284aa08007414045410444a00b0500c022040700354448045291a1f04425400210050b00b542480d040c4c0e041190b5a401e001e007920016a2891410b9a6038043c4c1220181454428400100001d000f20a1816601d00440700d40d80c05200c0303000000e2560441c06190f1050070300204900041203410052403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 447443408 1250 447442158 447442181
    0x210f040b0714010b0913030207030c14130c0504030b0c090909071509050f190315060504110a020a03110a05030703050c0f0f060619080303041103070911031314100f 72
    0x74020001000002041721034041c20091003a9078806446c002c1500030042d0600850f84504071070714082da01c81007907200d00d104008050007a80d15500505c182c1c0910710030500321000301d40b2824289070454507201c0121100070500301c05c8031b508115510140d07a460604500c01d5070040003c1020074203040b007100c046c4100901b4601071021011080c0403075030311400c2000051074241e45c0d10103440d030401e9045400b01c41951000c4d1031000e58001c00040060650004c3c0141d90003034406100c070001440d422889031140252000040e04000c1c11040000c0c400c22a00c0c0d12180060120b40c0109000c0e04e440d41103a1001500706d01061700010340e13420340e44c07041c00242c0100c40c0080140145e0442c080e407190303c400004101c0c0d4410030030a6580400840c0d00003806000e003e40c04112912440e01e4134100e5003040440304454881e10441c0f03000a50b00d00c0038000c9007001d0084400e424110b40b00c1001e000c1d1208150141101d800c05407082200c40c001c001c21414095030030441001c5041d9644800810449445069a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 447444658 1250 447443408 447443411
    0x290c01020c1c14040905091009201504060309020d06020c0304060809010e1203181b1f050d0c031404030309021509030c0d1b230a0305210f040b071401 66
    0x80f0a807980304034190b0f8100e603036951010031035995100180b4103000300e842c042c1100300e02e81215081804456030403903e4011072003642c1074039803c0007820050145c07200d0580d038082e90000c00041c01207510036004601083e1020b0890080101c0c4d40e901c142c00d0b6040407000010035400440d042021907403003840300da04020840e008100201c8080b0110f5140c10100100031281400000403070f0384011200100780004007050700b92030010314000581c402000b2220710483c444c0e4012800c13900205251604019848040d45400e850700c5d80038113050024006940000003419130b10943c0c200c00c0446040c0841c42540720340ea000804000c80d20410602d4807240c10341110200040c4288400c54400145594441008441041050302d01381b5101e00c04400420719003803030449800d400103113114401a02240d001148000303244c030040c100d00380210440c09220180655010300d20000d00503641c1e407403d00c411000e90003c4ae280c0000f201c0500165070144c0c0c00700e40e080100244081c20300030210310320500020740100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 447445908 1250 447444658 447444677
    0x101107030503040f0809040204062105101526060109210b04080405100c051005060105030a02071a01080c011101020a080f07051606060e0709290c01020c1c 68
    0x5004006010081c4000c000c0507591310010280300d04401520764000000344159a00c41d240c203402440e1010780449012031031070301c00700c1080d511407078003580d8030501450300209041d0713140c0038606008062140c9040c080c00321003008603541c2e25000042110742c802c0000c55181600b000030006040c2a8203511080c101c107020b003644a10300c04600100405240c108003100706079111414135848502c07031076000503406450340d40600b00c01c0383c03ca4a0103849a0041c401c0d503a00e80941c1c60310138107440701114090300103882080001d00c01780e00b41d4050300099004080a00c0c010f070244160140d10502030700140d15590260074071070b190350b91041c1100891002c0000079800c00b07500c038502401c56200034000e00d0b20224110001800700c0d00c0b50080d26003400c01c00c5907940300807025041401c000c0003d03018060720b14800c0000a50824016824a811559818042d60034012042100071410060410340450001e0411034000402d00c240060308160705031001410901801c03d580d11701003007047c0b4408090241e0a0f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 447447158 1250 447445908 447445913
    0x60405060c0903010b0604030507050901081c050c2509150e0606090303070b040b040b0c190503100e0108100605010f0929030a09030210090503030a15080708101107 72
    0x25425820000c040300c526102d41007180024003400d000c142d0300303800000105001040c003000280080449400341c407401d0342c50741c80c0d010240d1120150810300d8a59108060b60280b068411402444880c0d0312034150351401104200032100945011124140545c0300002804480f001d442042a240b490076992841303d4a040340e0b003581030900906a0f8490180232400b131000f0b0702c084c011101c20707a5102815a0280c82c042c03a03d11220201981c00b1307110b8801c40c800090400414100722100b0040c01c112481c3c003090310140c102c41c180d20061041d01c03102032170b55001910b130b07030715402a90284c030440307004c0c10107000d40d000000d01312115980201d0401154040c4207680c65000400b40c016200341d0102c10500c0001014103248100035520b070300000300000020032600c2081c60f40100d000d40e110b6401d86240300d40c0b020814094a500b2040a40941c104002040c5446030650000c400020403440d1321038070030340d181d0089083c1030403903009080d40e400046118520a8203882050640c66118a44c2420b01c003164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 447448408 1250 447447158 447447163
    0x20f0d021509120609030304110409151e110702041802060a0305070314011401030c02120d23040c030308010503030333130609052413021303060b12060405 68
    0x81c00400d4005070005842846480d40301d61060b0241c1640211185170504002140d42c039030003124213580c0c0c40c004039044021803515000300943c194006d07011402891011301504020035202000c050700d560101c0700411024050700505100b20b01e00300b0b07101d03140d00040c0144419610000b0110341290030700c4141d540160b0ba440256410f0764200d182c002501c2e030760204180c2c014080701c0125244101d089000103078826110884440742402030340c080c0201c40c4500e03400c1e69107180750142444c8500e4180524a0790602545c4402c1c200120fa058503160259008014010380c04156003d0b11000d00c10102401850740007401c843c010541030780114a185400343c000d041c85156000090328000c01860000340c001c031030a50301604c44000501622901c02d581b4000c2d4010314207881070140c85800c1030000707402100300c5c4078554090140c036072a118444000f4820084042c3c82a8600d401c00c076400d011480c1c81c1025440310101545c0300b62400101a0b070484108003220003200c809400304c0d40b1100030000000c030302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 447449658 1250 447448408 447448429
    0x209010c20010e0f030a03050304030207050405040b0105130c05040b0c15040639051803070b0d0c0e0307090b010c0807060621020f01110705040e0d110a120f0302091c020f0d02 77
    0x51f140c8103480740c44912f422410308000380d20a42e4000c1c2840148410711481c0e40000d4100c0c0d0048171a0b00803511040105d0b402d07038819001d500b01050003448204059141000107011660442c0c040d034200c0d082d08519a91030010682c0c0644003541e0791240701600149113041c0046500041e8500700302540400c148032980415512040d0401c100480c010a4200c100341850b410001d005040e01c050036102ca014030056000741003070081d80c5041210415026014000d1a4142d01d030240140c5001420050020060300080c03001c0d40c108100740100303502042601015003202c83c481c910210704a89004400c00c0003209110000d0a40c182c000d024400507950000c0d81103082d482820060141c02d44030044508012a40d030006401c203040c210344041108021488031076900990300c81102d00d09600d207055640d41c40b00d070801001080080d01e100d1806006840d400c40804035880e02511700384220000c10171701c02d2640303020304070441c4c0c07079054504500d000104042d4003041510b043c1d1050303d1940004540b10318 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 447450908 1250 447449658 447449663
    0x10606021204180b040219030b100801051513030302010f050c0901050313020418030302070204060608100e09071805040b070e0f12120703020604030f140d0209010c20010e0f030a 78
    0x4000703c2d81460301185401280300403c0003001191070315140811034803442419240c240c002450074024124518000d2080e156201069452000710707030800091119590102c2100095840d00703006104041c50b0702001074001e90f100b54008213250440c01049800c0d103401420910000320103101d207074040d0340d1020940754061212019008070200d203001250041c0002c04900c0c42c5400b20200b80701c14940c0540041080904c00e6808118040e80c46008491031041030f5040c0380c260304012410080070750000f46030358220340d032041501c0341c1d140c0c0c40f4013220b103426041420100c80707074442003000184107904803620f03800660303030034a004c01c0b401038000103190040240c84103108851a0a09030800541003007080a412020038200390f5900d00d90a02035661030080301c040b000660206407106500d032056810b40413a0144142d018205070912100d40301030740050f09645d0400c030440d84000d0100f80c24507040840d1002d550801c2c400946880001048242c1c84160320b402340e0686003040e1526200010350311400c0c1d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 447452158 1250 447450908 447450929
    0x20307080a150506100516060f06050f040603111315380a03090501060b030906090609030f04030222110919081011040b070c0509091b01110a0b010e0405010606021204 73
    0x209503143ca00c150520104000d468203142c80112427407251590b02c6003054590031208045035215010400c01034a5460100800782c0640210202040c00d01111420803202450404140040a400020206811548a10180d00c012028482a88401c1d50300c1c100405509260250742000603140f01000d2160503100c100309507540700c00e80c003801801e6000304060440f918000c0d88c0da0505102c0321343d03202402e942c07841c450b01480010415049000046400312940554028201459a002c00400080b03240704200940c01ca0845c205802d142849103800f4070015624881e1641d01c00e405200b0003010000e600d15020300420018441e4010004140c0e4810b001d070079010030700c07154114515403540a01e5100001c02c2c4800703e180f804108801003010156401074a080c6c40c0ca507a140350080c1d590f440c092410400d10100900180954400d08204030504550303002c4400e130b8440c81c0c2e2040e40e00e43d400d84c4018001c0f00048144800c100742030140000030803007440140400205490224282e105520030015400b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 447453408 1250 447452158 447452167
    0x70314010303230705071706040b06040b06040504020c0601080705150409020d150e0f0c04050f101b1110031103010b09130e0604020406050907050d05090109020307080a1505061005 79
    0x54414100881000c0d90b010361511113180789042e50791603146018101420101008411000c1e50009a507480303660030001c01141c1d0f46030003040c48024003101c00e0554208508100c0441d8a03181c40c002410300d00d00000040205600d0501c0941c1000781e90f400840c030407620700503003038110014003058606031a000000165a1134070b4110b41e078014880ca220201103420249000980c0c0d4140e08840c0d4400d0019a4444002c2d58078800c1c58a140d00c52800340d507511808084d9000043e09280091280b02107141c1880d01460368145142682100080070445180050102000503414034465010002000c0c1c03c050000b1413903120403004a003c1402005038620f4081851401c0da69082580300454180100401401d0949141142c23158401c58042e40580e05180c0c00040904010032802e20800b003555840d400d10041d84034400c080c0a028041d04090f6403103650a50140c0d8040c480b510091000d84020441600c15190050b0066803200035242c06500d071004104564443c84d1004e0300203c550b2904550302c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 447454658 1250 447453408 447453437
    0xc02010209130b18040b0405060106090b1603030609020c0106060e060909070f021f0b03010b0d02150906040f06050c1c020c1c1401020405120307021005031b1c05070314010303 77
    0x50f45003130140860404c2d00d0358184000e0240b0035054500550142080d585103a80b02ea0064594484500c584c6822840800c0f06803460500c5030384402c1801e120745000700c4c410340c1d5488090700ba40c002841410040c3d55960040020542203101c030482c86009440240c100200c140005a011400510200602c900817101d4000d9500c2481402031482c0b1440100c1191010074507200001c060b07600743c1301c0c003030361070b00203c40001c1c500303185000c41c010f50051142c4a0084080822401600290441074100c0700900c8003081d80243c00340014007420b515901c00380c560919045640ca400e42c01d00e030a4400070799a034001d01035a980802c03c0101c02c10185c94082c4940d801c4008039035480030300b0078040c00100d10400003001401042d0004d2048640494030035104100784001b003903c1e4072500c0c9000b54004c1180f0060030009006401643e4000032070301d058280000e4242814807154004201c40840d0751307030803c0c4102041c0c154414250030540502d0100103010304141d420204000601002e0240940da8414112 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 447455908 1250 447454658 447454669
    0xc061503070501212309030409050c0903120a0207030f05030304121b020105160b091e0f030d05040807080f0304031701080d080402060d150510020d02030a030f0b0d030c060c02010209130b 82
    0x1214280d08850001718a02211001d40300c2d0024000d58510368101000304111515140694000060081c054000d40389030085648071940300c10f14140c25401428000808501e1011a000c640350041c8003540c0d42c0d203001d181003488403000003400340500c510b01c0204505d10780c03510b08034030200e6420700386159a5845c5d001e084c0b010600002c5d00401000e818810410b01c884c003c10b04021034011a120480250f8071150400c0e280c1102d00c0c40d01040d0350084c00806540b0185800064115008114140c60070240d503c4104c02540702c614481d814010010500040582c01070a0b4944c12841000010141d414100d5246e16400180d40b80410004080081415942c484c03040301d030505102c20040180c03160740d003021041e1034520300c110381c8121101c1c021012454004503100c51080500e5014500e00300c00c50b60300390010f040c8445454034480d6180b80c50314094961556240d00c85000303440d045080580ca00e04441034501c134608540c11640144444d40282d100c0403030425000c0c034040801308228002c5000b10300d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 447457158 1250 447455908 447455951
    0xa03051c0f0204030f0b01080c28080304082b080103060b040e010501090f050a02070b070f03020409060b0c160608010501050c1c0509030f01060302030307020d080c06150307050121 79
    0x4075184001000403c214280300b400c600c840c03080b808607040781c0e81d9a038015204c080079600c0c0340e005004000004605c07400411542d400501e4140d00c401d980c1d490307940051840d0402e03002256103600c030700c89510b0071601d030116843d11980700c038000790f0800b190950000c24445d41840010070054840107587c07550f0b5a181c01202c0502660002003200f5a035402e140000307000360081600d0420300e0300e8003180a454943c001c031503489820041c800000d80301c44608480082c034040658081590074440450320030b606008443c0140f01400c20075441d003007e82401410a44070798003980142e6421001082002d42001d40c2c10304541090074500e40b500c9000300c0407818245443c03076040114002c064100d00c65600b10010708000c0c0011340440d2a03071080841d04508030303203290001a5040d4401e006180041c03034105000c50100c0d00c101d00080c10a5141d600c0980703066020342d00b542400e00580c400b240541410402c0c14000d000910b0443c40e16001036041d02c03240c02c010103044a080da00c62810011007660b102581 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 447458408 1250 447457158 447457181
    0x30106140d0905160501030606080606030408070203100c0f17101509090501031a010e01180f09020d030e0103150f0302120703080f07020a050904031b031806080a0506030a03051c 78
    0x6541c429030301d91352070100c4182c81c001d03940802d15141011407032922640344284900d002900c42851511b480c6c54540d610f17000000200d81c144210110020045164020034070810040c0d11a64014102118080d1410002c03100a000d149808003c020a05008100d0300080341c8401d035455007040095030b0115500d05158000d001c0b41c03420701e0000400c0100c0350840b0510308595144408aa90f251400c802c1813940c284204003454151b008070007205401d1b5402140d2507001c090000070704454070303804504a444089400d5011070510720308161b141d60940904507809503c100d08030003070303410049259064003003400f02a0248243c0c0b1400400082c0401242d000782d9048a441c40c0c60700b9500c240c0102546c03044000303c0c0038003802c0fa4002510700340068180c0c040d56164481510030b804415448590036861101902003141542980c1264404402614007402150365446030a02c4e0011400e0140c40c405001c1034080d03400503c050011a50010640384800c41c680207002d10b030a00000220003500c1d00b01c245 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 447459658 1250 447458408 447458413
    0xc070605100b0c0309100306030b010b032a0306010201140601230421031704110d150204080a0506060a030c0e0a060504181101031a0d080c0f07031403030106140d0905 73
    0x115070307020010190117444000c8035080303004034a0b20021401c1d24103d10004014800300310040c4034114a86001c0c603801884e4050851034004c3c007588032000b0300c1c900303140001547e40010500129507420700400001c006816000101c0d41850320000780050100d11401c024003503c1c5074015070f11017a0204440042910380e0300300c0000001c02051001125043d402180410303c20000545800e2840003800e01c1340741c02220360441c000b8010f05105200700120812242d400c005418582d01c840b01d1700c094006069080010210b00c10545041307450700501901203885100c10b55010000035400888880076200c402c01d03208100d0300c5e0b00c52b11202400c090380100c0c1c3e1060404d01418281411170781c8146c0b926014a9504190001400054040710f020b41c0c1d603821041403440603c00d050500290524100d44501d42d001d00d4108505441c5003000e141c22842c600c15002240100180078200c868848895000b2001d540703194034110003e4041085038880b04400c1b900443d408080c01255031140e00d5050f0030401307 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 447460908 1250 447459658 447459667
    0x1030915061d09010606170402030c09040503040501090b0403080d0b0109030b04080304030924030b03070b0f1806030c030609150909010c030e010c1b2603100504050c070605100b 78
    0x4007220020380b5a0203044058509400030720480c4050050508a4680351164000224031815410320300500410990b0584245aa01c0402d40c803140b001c40c0c0301d039014601450f00e56040c20001415805203500a4680100c01d00c02440810300d40021202800d505480000e004d01030f420059030454120b84c8090002a164001c000c240b0003218011842207100c1d6981a051a480d4142d00410302d00c0568425a01080182c003440c00d01d0103503110300c500c03220040484040b00e030b0314503032541070b5440800c40303d00140740030a4a80f83c5c0622040c1103011810106e811a0441c641044614900d01004011a00c921060720200380340041a0540e02038100000d0183d419510b04a00001d01800400c410400028504080e4000c05078040c41110540950f0303956240e0030124070301e00c00584000202007a80c07080071086d003c1c00d0002a08510701074201c69410510b8076490320062210190341a64401800340e418141005045e524000440e951154001400145030315002c54041c00050340e0f400c000c042140002c2d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 447462158 1250 447460908 447460919
    0x1e15020708010b0621090111131401020d211503080a0807081003021912031211091c0f0210020115150801060f030e0a06020702010206071d0103091506 66
    0x2a440c0203860303220000340203544101042c01641d100e581201901c0c0c0111060f107520400448440e26002540e07040003003500c6805d5401c20b5002d038001005040d0801c611b040400ca0342000a0b50096200000d00250600100740040a49504160b0704400f56190a0001c1000100713515417102200b918a9403a0800303880e200d01e025a0b02e0b0740b100d8400001b14100b070000a008503c2800c205100d401d0890610180c94915424010500d04489092802c80181c50021500d41d11410300310745007e01a580301c0f1741a400b5800c401040300d5000c030a0280e28401002102201c0e2541d411000340d40f201141290a40318841c140300200d41115407000354032400752555050810741c150042505211460000c05101c1c1d52100c40c18941a05092798501103951680100310240c05104a03480d44946400c01090300001d80161a040c15050a022196283d01050050941d6410803907281e0014640c00c280b59003491251a10744992401c1e032801d4100342c0c039080702004200c0c14149682038040c2d0610305214268541 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 447463408 1250 447462158 447462163
    0x512100501140f03010501060509060a030b18070f08090c01120e070b0301141c03030e0a0c090f050601020d120f0f0f06031202121e120f010f0501030b09011e1502 71
    0x75252507101d007050356460f499030304d01849a607040f00c503035440e5640361907820400d101442c0c00449280e0705069540301c20701c07042c2d117852006254525003091050202d103003000d07016150703103000002c80d07040205940c2044201b400000f481c1846110908092808042c0c071304540d8090280d1002c3d10300c1c5401803e50001d03140202c8000742d4142c5c1c900e00796407110450f441c403c1c818041c0300c810003040402c0b103e0150901003400b035030000c00846004c10503034450302040d0300c41b600e100c06150300122015648020300c0741859113620846400ca0406d1001d010082c000200003044c0340d4860b01c0700e5000660300d4400040d07110450b480400e55154845050001d41525840e000041c51170b440242d6241c00d1421002d08090b02c086818000315442c6c071009824406007000e10340d4003c030320140d0002401d0041022403a8000c5401e0014800c0400c19642d07140c0d90304006162098007100d0344044c1c141418080c1c0080e003981e5407045030f8103403610404130040350651152483e102c00e03c076501c103e00901c81c0c01e00000c00c880c1e01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 447464658 1250 447463408 447463439
    0xe060403020c040c14030408070c032907230d1805060606090a0915030b0c09120c0105040e0a020d020c240402090106050c2d07090509070512100501 65
    0x1e40a0b10315004102040c4425034160303e081310000b4000007080d000c180c0000d800b541d0014025100f00381061110b503a407a130107900b2038009960300300d43c1000c81c0740c0c00360342c0c41c0c1041a0020b03000b950b00d91f24106680d0182c86101250b444070480100c002c22011440340d032100b55602054445020700c032889415940c14846000100c0a031541d014101c0003620360b05242d000c0b9460140040c10f0b1101c503d203060300050060608070209007a10181030400400b041c0c482030980e0103842401c40702030f9176040c51800c002e241036a140d01000d040d0440c60440605a8025041c0c404489407880c0750925a03452520640080c85000701c0c0c031006500c04210100010400582c01d00c001d2807818141c0d8130030050008500440c1d40071107000f5400b01000c001800038900c640094002036002e402101c40b01d58440790018900200c62034800b292608507224800f442a04010400080245407000c002609080192640b50b00f001c0c00754030b0280d2154070441141c0c07041006465900071028004100d82d50311072554680c001c80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 447465908 1250 447464658 447464663
    0x4050102070e1510050702191701050106080c0901090e0f041203090507061124190504110f0a0b0d020a110d090302011d040f271707150e0604 62
    0x1d60002249200b00010414000c22001c15820058015801000141c022942018040180501c002c100586601340c6560f00a40b06410581c804c5040c074095000c0440d4030380b040d82550781450010004184c100000c00e4014038403940c40b6a4620030040181c54a041e15070248015940510800031100d0704d0502d02c60080748942145491404c4000c0d04409682d8512806803240c2c1215204010759070049101e4074201007035209480408210710851400e407600502059901c00315030301002448030340b07402c15904140300c0f82030400181c04d20342c03503200c07103c04002003081c058000411039980c0355407800202c900401c3e0102380da5a456001c012480042e40150b404440480e80d90b1902100c50302c0d01007100140b45001d541c0782c0043c1c03880c540045034a01c954501119200445050101c01520f660091404400d90800c01092004da210b0a802082e080c03907520540c6491020007450008007503140902041d01c1e90080591a05807a050155035920015200c0030a01c0c6480060741d550b03400411b9070b034412030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 447467158 1250 447465908 447465913
    0x3f2703030702150c0f13080a030c0606120c05041505120c031b0102060721060314060f0c0d0c0e0901030f110a060f051303060e0312010f030f020f01020f060c04050102 73
    0x116540e0a10030f104107659803080d00b803042c8041408912030801038500706950814a204450b55154050f00744011514160009850801a40f00f884820302800c0300a12014500c0d824442c06a1035840c075101032401640d20464a4958480b680d250200302080a013400400c4207184070310400000d6036880880c40300a01902a444d01d03808a40202d2944100d0f640e4182c0281c9401d070780b2458212001d503203026000d0340c101101808400602002d01c94980030314070801c480e046501401c8a11468088014498440200c40c0d6080080c0c4c12520016152000c0342e8507070125078a400300300241c5d00f685103480b13001d800c045104000003c0c440c0b00c1c003641013902c0c0900c0c40713108002c4105050140b1034106000d51000b0503001600400780c10721510082100c08005070613260017075120b982d40c40c19a444a4040c0c03500c0d40c004240c0500c11804504418014150b404614840c0c52460ba140d4030b040c055103002074480c1003010388078100742c0d000b4003c0138074500001c001e403141d5241c801caa0032a50341041c001d150052 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 447468408 1250 447467158 447467173
    0x40b01050402030105150705010e10090302120c0705060c102a0c050d1d090f0708100302010206010605030a090b0124031406190f0b3f2703030702 64
    0x1d003054401c49040c1e80001d0480718001407000c1158089500403201192030303669034030101c0c1c280781003400912509801244041040829410003e24040c81d0409500d0441c0040080e01c00c40480000c0c1c042c100c95040c0c80c065140d440c07059025040c802c1741c0785940d500d18100301c025440740056407814200c840360f580740c2020307072003858504803003105510340000c006910000d603d1003401d01403404c203a1981000c40c0c1c401e000c0b41c03040e8007068221400b95020860145140140038040da000551540d010b500d0000c8005a02d25540000f541d404042c0700d4401070141c0040441c040041d9030300850342858006a561001d035a50700c40d4684030524569040400341707043d43c840d4021030303c640126100ca0030950307495801500d40c0000c1042e0106410b0381c02d9180e1001c0c410001f21180c52001c1400101502c0640e0358503011000405d030303001009110810340441207611840600829840b010403020010900d11707031a0740e0b42a11590307446030780400f8442101818960032035002700000007948604510390a03035661 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 447469658 1250 447468408 447468419
    0x105151207080d030c0314240406030204090f0b1b03040b0613021b010b0f0604090e030c07030f021003090308131103030403060b040f02090a03121206080309010f0504051003090f1a040b01 82
    0x1008107440c0f490070700c4028614000382c084c0d01c0048c582c103c0ea00800c0011070590b660f0024003140d640080c229945a8400c030740b1024001d10030a11a80140c0c0d601d2854800980c4210940403880000c00042ca14014034001c5221307922080d10041000c25010300456032102007644001c0800d1711000c03071024541c06c0c0316101d046810201c5840303800c00c1e0003801d203a04190500a00b13102070300f08003440c148a44002c0c4044585618204001c80085000b205600030461241c01804100121506070906150802d00c546001980c086100c55000d208100003203c0703d00745203030100340f104c040198640e1622020902100340005a8090600c2c5241280c0801c60200c01003405030681c01010b000c5a4061001401000410300d11484000284420705e004110740251500d41d100300c0d15680c001070095070001c6680f20045d41c10456060480c1003c1c01c22500701860b000001d1404200b0b000100205030f12407101c001004160f0108580c407a9000d241c104904c5824201e5a01000303040764142c0741e0020f50301c0000340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 447470908 1250 447469658 447469691
    0x306051b0c030702091e100801050c030c03040b1902030a0e2802060a030b03010c09031401050907061b060c02030a021605010215130b16090501020105151207080d030c03 74
    0x405603801960034090300703400304010240000c00303031416031450302a582c9440300e21100047c41140301c410541c511a00b02100c440c2141c07801001c60710500001c20900c03010400c04010340e0b03400340e48840104456510500030480c01c01890054a80c03107800401401400380c00f5410124410000000315456a108a5201e06000b130345060b010108401c19031034413025060480041c010281d4508002c14500300c0100841d08540380708000100258a280c01441040403a15180050f0078480000348035505105081541b075489900c240c80500070078907001e201c0b14a00100402c02d1640210040001700407034203000e5100da01c00c002840042c094901d42030034640310080e4090546206a0082040e4a0000002c40d61a840070305441400014441403000007042d1f450507902c41d1007000c0c40c000218440140c040c2c61011180c000b02d040d64107260810001f00e400c1c00300013440130411240f2801d070740c00700ca600070f003080d00c5500801258011108000780302c2d6016004903800030195075041100465800c01e080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 447472158 1250 447470908 447470917
    0x20c0a0f0603050619090b27010501080a09020303070c05090129030c0405120d0e040e100504210207180b030303060f01031b090f080a0807030c0303150306051b 70
    0x1003115800d42040c0400c502c640d000c1c42e84654054039000d00d8000031480c0002c00d0f040390780312441c105d440b80e420701058100592000f008908000e00c12130f00c1810b07115003a0428405010701d60411024000040c0b00020942102070004e80280550755942244d08141030f401c1182c0c060a8050010440001703828600c00f8680000441c960300c100740e807030382c4081c0000855030000d416288100301c14000480c550b9508034220703082d11802401007041002400000d0f2040350001c0380c4a203d1031900468006a03100403565581c800c1c0031100000f8103903200d2a000c80c424481003c04001c4c0c4403400c1d0381480503900054002c1c1501c0c2d5031b104600b4901040c0408006944040c060250560001e001089150030018902c0e0781c031840504001c02c00814a030f0410003804001ca52601c00515003410400800c140303a520800680314090181407010510b1711080b44901c2070901c010100040b010300e1030145840f9500c8100820348610030400c00a58a003004009000d060717880318000801ca51890554222780350484 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 447473408 1250 447472158 447472169
    0xc0604141806031009020310020c0f0c0f030a060b0a170307050c030102090d08090a03080f0901170708040308041a0109050f07020a12050a090515070302070608040305180f10020d020c0a 81
    0x4007031309040300c01c81001811604104070f03054030800b5409426020580040c00040c1c1d18000100400380d40c00701050f16004005c3c00c260b0246600e0b500c01c0e0311944010810000282d0010000f1a2440a86020824400c4507030301100c6c50000b80740700303041001004001494190f0060003190400410201014200d00c03e844445a0042d104100400010210030103416402001060701c0b0b016680da07280c40c58107510460309141c1c0010300040885941d80c20404210001c0c4034a20f01b03071842c1c41c150001038814070000d000501480030394400142007043c0c054010280307290300d0088111a507035940e0344401500c000c7e20708001e420300301e1000131a494070000303440d580c4a03004281000100d6801e5801d5840fa842807035444204140f00704045402d07202c07800070b03c1000c070710150307001e656400d10706000781040c2c42a0041400c00200005000200303a20200790b45c10001c141c8449224004080b000900340103203480c1013a00400c1e8142c08182d16a00400e580c5055245034003607c144556890802c00e20003402d020340c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 447474658 1250 447473408 447473413
    0x206190b06070f05030c060103060e0730080c0106031104110901091404180506061005030106020304031113050f04110d0206310e0a0b040606120506030c060414180603 73
    0x19140464000812500524000d84c2903a11744030750300d503c150402000343c1082e15041d0702c940340c24204bc4810095000104104049000c003c0249103d0002d1441900400190b01d54041c07480e05c103100fa124112808200344400810009640c1c1c6008038006100141c45481345150000100401664004580030b03070301d050352141d01e40f03800d21460a03025918036940c29003081d5106c0c41420640c2180d0200c4516034000d00042141e480c02c4002c106088101410036000c0040510041006980000039035044c1d0b603222140c002400756880c00b107925003403001035504409051030144140f68a4041145004034019214865914180c50600c80b000f55204d9000b50401c004000034403042409075008440c0080d816180c07a039649078402e0040c0d60341d072260030907070404100100b4000519401d20611003000030603901400410701d0309034054079410021040300348403500e8200140c0c00350360500440d0307142440200541d40302c03902c412810f920324a200d99203500032400480341c090841060f90704a882928001c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 447475908 1250 447474658 447474667
    0x216030201020d0f1b060b15040501020703030f050f1903060905061c06060b0a05030a051012020607030e042c0307080306130b0d06091e0510150b07030206190b06 71
    0x408132201d0100d40303c0101042010300840750f14941d01080003058900480c001310b40c0d8118a42001038800c0101d190350b0034000200000c100c10790b00480d1000c102c0350141000f18548144d200141c40622500c46020310720100094a11503215490382c6000418845980800015443d0301c9014212841a40c0c0e481d4055448016018010a015070011a980c49a640419119500d01402c0c02c2a0018504000452404000c00a580ca050702c986a8021000403016a020707144c4901e10203040002c00d8003a000f0080024640c0604d402055400101c03180071703000304080f0601c10503400844040080300fa00c1401101144c0361114000015240f003903410000807491521130404011112038403440041130f003500c500902c80c8595440216002d694090007000c00c21070964074041880c060241c00b0285400003040f03c5601044001a1803581100c542c0d0000030204540c0d41100000b510380e510104540c0c40018064040503404918207015052209140840303040c00a924801d030360112480c0c0303812220600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 447477158 1250 447475908 447475933
    0x6180302060609070203090d0203070905090303010e0912040b0d0902030d0203030106111b120a050102030c070606060c050c09090c0d050d0816050a0e0414090105071d011b02030c0619021603020102 86
    0x151841c0281c80141200cbc80e5554820548007a942e0403a00c010701c5401c00300c0104044004411000d9006060764040e040245040106c071a950007140141e100021011034034032000d910f00d034880303010030b03800400321340c0c01800c9080002e549a00c24051030002401241c030001c104100019101d03030075805010020070080310b0005001c0081521141c10400c3d01c1160100380200e00c1c08e00c0103602490012281e660350b001d1608000041c0c0d030569100104218508400e00082032002c26428031407401105c000c4150346a0a5840b440e11503c0d020140e88210406010030030050300056231040c5289a072118a25996210811031f031400c0e400902c103020071400c1180b1604541b10f940588501da0000f4000580d00c0078640409075090703011181c1400681d5a842441059a002101085040f0035801d03a204003080c0c0c000000d12240f000c01040307241c40c401629130001c650b0248031a1b0022080540016200d0310040c001c0044604d2018200303000d03000e0300c1102226189030f01d0342c07102640c1e01071300106800c58400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 447478408 1250 447477158 447477169
    0x613020c1c0203400e01030203070515090906030c121b0405370207240203070e060c071502030a08010803030f0c1303060c120b060301030b070c030c0618030206060907020309 76
    0x9200000f1003460b0070b90401c86001491510380d01424810150005c0d82d0b05510500d40303414a6900900c0c8219a01010380c3d14554449040b00c188000583d441d00702c64944d00086440d00b0348468065078010b540c4c8803c500c18080008050310304806405d541543c1c2c180900c180001c4400c141e4660004210020100441003000795007124454411801c40c110792a125450307500300e800815085600d90b03100a81484510003036044202c10030320102c01103140d4100303050301400341039002804600804003c10f00c20302405050201800030800c60444403002d4900000080d01d1364846148480400c1407000041201c074000801c0e01e10449031020710711595150a90301c05840e8000c111088120078040d1000310001d80d45002e0014a407401d030700d0343c10003801e1035654a0141c92020b03401c180a03c00c00c1c401040400d041d541e03002e42055140c14640b81d5124039050883d000d514002c0050100c40c280788440020303016620589074518000d50a452280e15040100321070715034103a60f204c006070702c03c1c00101e52a1801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 447479658 1250 447478408 447478477
    0x408160e070c031103040305070605070203101104140103020c01020a051213020114160f03050c0c0409110d050a0f0f020906040c021c17090607080903040602030304030302030613020c1c0203 83
    0xc1394100c1e41401e68070f951301440c084580d002840012004954281141000c1001881d003c0e00b00c03c06200c10340c45400120128000ca100b4803400e894a03151282a40e4041d0341280c02105914000750740d00d06072050050301c40c3e4840c0105aa0001c900c00000b055000d24260640c5070f198141d481d040401e0950402480540100b0401081c920030310b442000018200d5800d840740c0c03407207612001c0c2c0710105c1c0d180e0030b030070130109010482c01541032080340c03070008581100703003070b91050102c500303410703e8a96040162524864a000a000da40206a1074044c41544081039211510840c0d0505550f0781d16018801a11028031205000d030388806866419040392400f0140c041c0028039103801e0840209503c100c0314803050307035003110b9504680240030155a002c080150b0043c185801180740502d0540002c0d81c901c001000901090b9000c008600c1980da06240112244440345055464441e828503030354403011a4144a00307188000b500b120744c014004003e43d10700140f400f4405002045040b95407070006070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 447480908 1250 447479658 447479687
    0xf0304090f02040905090607030c020703030503130314040306020706110a05090f0301022110050a0609140102011e050610030b0a1a090402030103030c0b0a050c030109091103030408160e070c03 84
    0x2003c1c40081083e50851003410312a040c0c41000300322030305100c1c00107401c45880c031000c5021504180c000740302007074109007143d412803803100144022009a0a048580c2c2600400d181c00340070002034000144801b540150140302d008900402c2011030210a111517840340000300c0d408140144000496031800600c0e481c45000050005442d04484000c00e105902c074104528005620090a00820019030f15030350000d072500307035070b028011800c00401034142005445003100c3c10750145026003803642700790031400750545240c0e02d408003c10b509040e07101822085840302d010745a00f0740c2c18620544a4011540110406454004094101825501440c40600340e41c2082e450802c00d025850311390348011030085000b6541c6d1119a14a4a014508148058519100d0740d050000748140000d00340102d83c112866003000003083e4100e0701d0710a100740d040040709a85800003240008007200d003c40d000c102e106040c200307000e400e030b2a16200030a00a00761800c1c07000070102d440e8003000074001c9044840406 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 447482014 1106 447480908 447480911
    0x180616020a0b0a0608031611010f09120c0f09050610030b03060708040f020a030308090106061728060303051b0c0d02190e1f080f0304090f 61
    0x5190301005480941d1a1001c500480f0766503004070010200c074000d0301c0d00d8012000c10300c80c1040350f04100781d5002810029003902503105050004804100c0d07107a201c0c0d000d040c0500001c0294865008544030821100c01050a5040304c508000900030003901149038500303181445801c599080a40c01854103021203041d0580c0d010980550003142c0b464001000d0f5124180382050001e0510042d4218120717500c00f200b4194450402ca2003158000300a100040d81e50300c00f103039100d00000e05100c40899000c00316007004121000401802e600c01510242e94001e0309080781103944c241c0c8100c0100da0001b0310b16114510341242c2c1e6024030f500c44017030428854031002140d0700306000c0c5030080c400d501d0000241010400151400042c0888034900340c3c0ba454103e00300c0b80004195800808001c483d4200007525000c00180e03115000800009503041a00d454840d40c00380c007010a4501c0520f = true := by decide +kernel

theorem cover : BRFrame.Cov 447302158 447482014 := by
  have h0 := BRFrame.cov_init 447302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 447302158 ≤ n) (h2 : n < 447482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
