-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:28:43.086113+00:00
-- url     : https://prove2.me/submissions/ac06d037-134b-4d61-80c8-e3fae0785c29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 364208633 ≤ n < 364388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 364209883 1250 364208633 364208653
    0x302060612100c050f0c0a050d08060303030703050612070f05090c070b0c070302010b0607060f110906040b03150405070507050f0d08010311040e07090213050409080a391103 76
    0x1c0840c1ea11500c003400c06000482c5003180788101c1e080d0088005104128800081001c0011000192095403e115a040303c035680c60b6202c00300e417803540c161016a050361040c40480d450074002d410940e4040400340401f58900c810300c070041c0c501b8095034000c0050140c6224184401c1c10000000e40d07020300002e1245240c01e034280d40e224504000101032054032100460340b0401c142c402c0d002030303034212001002161100700c50708101c8001e06408071039140d450f1070242612a00c000c0c2d4000e0718070b0001c1c001d184a0401d0300e4030a814245600003042c02004d0b255950880e10187e4992041d50b005031075554803540c0f01c1c0d42c545001840c0c449551200c0c007080c1e220518205401d64060021415a940005c800406d100100081405401141c004050900655101007a4048079502829000650540c403d6416a441090108691140c0e1001e40402001c2041c14091030003030b50310a148968802400da00180c01182e1100d1050854421210b030f080c50b1140802800814031071100380c410114068200c00c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 364211133 1250 364209883 364209919
    0x2030a0804092910110703021305190c02120a030e030705010204060f0305100512030c0111031501170606030c130806070306060f080a0c030609050a020a0908070e0f1b130303020606 79
    0x6090344c4030310402c22010040d0ba004801484100015640585110107030340c10741a029000c0c1500300c0d0300c00742d10000969040480001c0c0c0c0100700f040711440e000341100c1e1700c00d0404910b05a0100440e1001c3c10744401c0c0c501807018040000b024218000c1d03000517200c500308640103040d019034001c103008050500d414094900c03a0010444203d807007c9803400030007078180030124118001e928030038016510707203a101d82998404000451040694000110304203800030300541e2010300a003900e16051070041c0000d005410300300002c2d83c002030b05151007400c016004030041c480480d507400c4241c042e0048424080c00c3c54040c050503000c2e20807410035848800107030a0080401030010240b03c1c580d034075400c040d8000c9010794441c0002d409071102c01d00143c68001d00140103940000d00c0031001814411001400002c007103000c1c01511080460702d12961a00d4006900894004c0d04051400440000c0303090007041510041002d00d4009103513400f09455800e0107400c2801c010200341c066204541c7d1011408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 364212383 1250 364211133 364211149
    0xf03030b06040e060112180335060609120d0905011b03081504021e120703020c0718060e0f18060c1b16082503020a0e0402030a08040929 60
    0x44020f2038504a039255019030b442c0580007554020fa140c20187c170310700c421705500801e18082e02420521401808118000b5001a01d1113903000d410003100d030b1800309030300d40b62410040c002200d0060134401c840300c034001c0702401d000500329a500440c038a82c0b010004d550700890340c0103200b841007a19010512640d18040c0072030000402c51604840040030107929a0740b6541501d240000303651601d01d601c083c0c40074907400c65005807050901c00580c040085d54052290085a04024800018000540c54901c03141420b100e000b452900242d21a54040390078440070382840d104190601f000360709820440d00d10b180e900214160114203801c01e80402805005581c00c0303130281d040710f40380d03907241d02d2212503582c2c00c1108007246001c540e141b5442c0060340800015410524000030000e1007206459004405001162440b009400c8040c413030703040000c2201c0c254115481400034003034520b004070780e542e10740c0070f40d1190b082004000d03520030011aa07828004c1000e40042c07a0403c074980f100a014001640c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 364213633 1250 364212383 364212391
    0x20708030a0b1203031e100807030201121e0606030f0c090b070c05120105070206090105040b010b03150a03080a09060302090d0f050709110403020111030310180e07030f03030b06040e 80
    0xa00c0d1140e0072000e96032103040f0440d00c41030140055030b80b0703410021180000049480529840384050302c010500708001144548111007ca60007031a07000c1c595030040d500145002c0031301140b19035072a00900c2040c075540c0c90822084080c40f00103001402c0003005011600e07140040d924280c03803c205001c80d183c0107641d91080d240f103400480e464030428034007030031809101c0d04826040812134014214480054020034060401502502c085236903075042582280c4040300d004c0c00041002c40108542c110910041d40c11102e0200c04020031b0881c0000304581f80069401102c00640019074501599480700403c0b015140e00d10b010351529249a00042070600070205c0504100080041981002001c102250003000c999805002c12080012003810075081884241d02061480515422195022048a01c14150b0788200e074280f90402c02000000070003d034000041030780d11051520031035401c000314402940318100305040d42400d031170010160f54400c0002802004103000c00c2c0010070358020b0860340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 364214883 1250 364213633 364213651
    0x61e0b0a2a080c161e0302060a0908010c0c0605100602120f0c070f090f0b100c14070f140904050d0807020a062f0313061a0910080f0102070803 63
    0x1c01c54881d5201100703a0108005020318400208a03070700c0c40d40442c5441041c5411a1460b896580d41d451481c02c98285045030040480001d43c1070005140c15400346c9079056052811001007030703c4011003421203030b4100c400350100d0841403451040140c1805000d610060101506031154a040006941d525a9220100760310030b001c142442c0284041042d1841c040b08017040b0f5140075640da103484070b2041203000e200c0c00c0d00e042002802d1071082900444690341e4002d00511400540000308440324849000304407160402d041c5003607101c1d982008400003802000780c201c0000b1345801c80a1120090842440e400f03644076004000c0032440106005001100c141000c0c10644d642c41412803c0c02d1419100401061405601d4604044102c0302110542c2c4945126070601000c00444040d40c0421901e01c00000401c1c00c0d14000074174103802484416a000c41010507102c0030f04005000424111544a6505506941003000300010800303400f03071540800c003c500c1e0000c141c903092200d00c0f005040c980 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 364216133 1250 364214883 364214927
    0x303040b0624090d05060c0c0c03070b03060d05070314010e01140c0702101704030302090306130c050f040204120501050403020d0e3a0302011a0910090c0210061e0b0a 73
    0x50fa2622000862000e070b211003951411721f48200401141c4e0400d50700c4000a108070000c001c41401c0000301d071016102c040c40107a0460f03070f4070b00803c94290003d680403a43c9010340c40c0000005031071480390240c4a0200c400102d58000c0c0d00203841e08403000c2e81a1164491031300402d0004140300c1d0320448a4041d01070781c1052241c1c5e11a0010b84190285001407428402040c040009040d030560107044042d000b24145c44840e1101c02d1040b0407141c100e50045e059106451041200d86014080c55020160141c00941025900d40c035407450015040015940d40e515541000304043d414010b0001503e03590408900c04108040071606a40b0103800d400346652440248048145400b000361454884602389440d02d04484e2030000e028084c0810020a04031f04c0081c411058031707001c52000e104011651500314441d00d404e55000c007925203500c80303000358006c00c01c0512001c141400b40f04040d281c0c1c4444c001c042c0341403aa4864050015510180e05200280306032000e03079503c80c1d08260071070316486a0340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 364217383 1250 364216133 364216147
    0x60706090218010b0304150227131107060c081501030207211e2307020a0b03010906030c09050f070804030519120506060903030706050c0405120303040b0624 69
    0x188030422a5038006401d42d49000001440d140e010009500c554030078010f909038000c81c190a00f041c0d00410211015503c002e880c0700c080d00340c1810b0011008000280f40350300000d5000c011004075041c02e0030680c81610001140c07010701000d409004104010707498102c00350300d441c038860350213110320b10a81030400d03800042c854240210451802c60b20760700c1e01150003c0c1c001f1030740080c210850f0000c03041c201d030341040c0748000e149004141e1076085900a40400e0710502c480c10015603254080d000407640b001c11580086404d9003080e000d54082c10035039600240c2d00d800c40c10300010003c0711b94843c0c00c0341c1d82400d007042130851582003803076080038240c24103a0081c0c50b40d00c0d0a490350702444114803846800050410741043d0300c48820079200740749060411060b103442c01030000610448100c00c0e0035074005c00890000940e13940c000c2d9807204254490a00385506c0d080001c0c1740700049244550194404003e004c1400981c98006402800417101d1903240710320503010302d10544191000407103c080100e200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 364218633 1250 364217383 364217389
    0xd050a020d0c020c0f101709070b1c05090102091c0201210209010905030a020108040813090606090501120621030e0405180d020d0e0f0f120102030601120504020607060902 75
    0x7a03400c0080c0641d0511150442d60002561035980c582c940b403088101c09206120760616280b890400d00d0a50707500c1a0346007103052001c40846010305010414850080700240701c1000078050320f42c0c04206104c54400303064440540040e5240a0612030259204001e2018150b03903490400343d844651150700003c0c205180010382d000054188074100114010340c1d444500c1d160390b80144842d07142600c0781d40d052a01d8074280740c0c0d80c00a4840084c0480d54040104d400302c0d0240c0080c1145984030f24000580c42e8444203840c0c15035041d0781c071480101c2c00b100c0c010300a541c1c011440400f58010440104030310740c03070447d500c0107640b01c03c2c0e400030b1107950441d489418140b00c0d05071003002140181081c005800c103090481d011b8038000b10000058018040c0c615a0b4a10110303010594000a51314010b4031003c1000700b02842e40d91010711940803034196200040790f1036130410641c2c1da2200310001078503442d00200261442c0a001002e42c801403400c0b08000040e80c0e007105448109410100004081e1428804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 364219883 1250 364218633 364218637
    0x2010e18010e0a110c060f060d17031509100501050a0201020403021f030c140a08180a0b09161239091104080a03082701150f05060d050a02 61
    0x9003554001094100341c0d0002c860040003011010002220310701c44d401000e0050921501c02904880049503a005410003e02d0f0000c5000b0120720035805507581e0380c02e000d000d40d0003600d1140f0001c070030840c26040034042d030901240d064408400c10329125036200144240390180605012000c101e00c0203840c0301b58180d602a607809000203103440340710b0401030f801c00369140080340000d0508202c01035540c410b00041d2604440003c0b858100b1124035000d0301c0408000b80f0751007116060b10326211488004003d10301d00d03035004001818007810405101410814402030109810031008403c01c03400e0301e240400d0385885e0300000d500f4010b0318540c111040342e940c0039464100341903181540c2605094007900c0d40040303504507402000110307802d860400302402544100042c076000b040710000400d003c1d401c40c03940180303030300c407030840d40d90708100d1600c1d000071005801e82c200e0791354800000c200505011341501801421610490303c41c81d040c0051a50711446d00034103600741c3c640b070129040b2001501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 364221133 1250 364219883 364219909
    0xe07240c030e040f0204081b0a0f1a0901030f180b060316030b09030c1f050106090312030504030c0b090714032d0a1e0b0a09230a0507060503040309080c03030702010e 73
    0xc00e550a03070840960402003486011810781c41078944541c001101c1400101e0f200c100c0d448114be900c610b46a441c4044059041a44424141900d0300d5240d00ea000710b912980c0b0602889445101a980c8541854481071100904050007039102c40702303103022226184003070b00c21a5407016440c10f840ea83e001441d8210f024480d801041d5102e000241b40f640c0b1800e040080d9080c4158404000c1030f80c1e81d03103040b503c7e040a4803014104090204c000102c0d180700c1c0d01704991203070083c20205002c0885958440300104100c80ca9000c0d03820405007400780320303101c503000411100d00b1402412160342081a01001c842c00003091424075034001c0011403c060300307018502c6d00315004a4441300c02c4802c180180c0000415900841d4203861910005902c2c190501c640700c0881e801081c540d210358145444484140000031201289119010603180010740420006001e0180c40d504e440c1c990929140140084409401510302508000702c80542924004242c0f070105809280c00c2180340c0c8045c0105402581c0c41d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 364222383 1250 364221133 364221149
    0x13050619060b0f040e09070302100807021f0e0d210b030f010203010608220506150f090108370206090105040b13050109080c01020709020309010e07240c030e040f0204 73
    0x20800f02d0700c00c15001c001e40115a0f80021701941680c0d0b4402c01501e994440c0002984600d8402d0054901c1c1d1041540a1307000d6000d0040310310310b0488119010b0868040c814000785c954036085060059103042c410842400c00e181803030303030400c0000011080c0d001d2041c020b4205240c1e03521502441503504005820801100300b008550343d50710b03500014082801182c050020200402c81010008508806200c0581e00200608017a842d044403001d0b128281e512a140c1c00780603110460981d80d41c110009000b091090010104006000c0170890300500440c101c04400d240301e02e810202405094100c115550704a81071a0b50f0045680142d1ba075002c0c82c5c011461001010500703c94044c11581c17800203640c02601c800d15040d5445940607030700c050352840780d4010f811a020400285100d42c001c0c5401622030301c00032540d0780380040c11520780140350748511801d50b0402c4113281590107140c1c401000b1131440c81e1402da55122138070084e148c40e036214052401159610031112110781990f0548000d40504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 364223633 1250 364222383 364222387
    0xb040809091e070918050604020c0f0105041101080618131406040b0603071a07050102160503040906150c02100e270c03101e0b040b0d0513050619060b 66
    0x1590540b40501c01d4a10300c03031403041070000030446142c003d292690485000382050001650b501c2201c1015140152001d508540c0a001002c4405020704c010396801c8041030000070a4545030070700c00001d00403e003000d414801b00000b40540b42e01c5002210f10383c603e01c002800d50b00e84491820791400d00074800081c10240c504070308441c42000105409004034003400d00e040d0f007516204101602e4805a102e81030746548103070581c07412182540c001c1c06070540160001800c00117141c0394090280c611240c111900e801c0000d040c00350010174421503000d041c1c070014981042c00c041d08050301c5900065800ba00c68a45510030526142c850b50720361101c600c010b0071014826176000341e41d040a179002116410348103503d0000030301c034010040c02e89101c0e07900d03440800e031014540024000032189940740348040b45485003010421641040061000b040383c01d100540c0d4078401650841180c1c03000e0f04c91440c1c0c0c1c10b005820070100d240050000d0f0880c000c400e0307204040d001030044034000c0c140d81d40181c0742c41d500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 364224883 1250 364223633 364223641
    0x3031103010f12032d0818210d1a010f09030b01033009090c05070c05010804080c030a0503100b03040b0604110d0624020d080a02031b0c0120070f0b04080909 69
    0x40d83d103d0b5010f086a91b00e1b50385250301ca103415000f000e004207526a085070b0003c1e0600304c0d445a0321485c0710038002249201450480801071090070344400b0407400d2181c003da640100400e50784940503c60362040d41c54802411170455607004469041807101074035001401510004421070440110720641959400861500712080040e00c924614030038440e03544d00d400354440190b8060800c48070f48640c081800150103080400540e00c1200c0a0010740700c1560a01810054800810003002402d00341e884171a100d25000b008158200810f0b0400d0480d20401c1c001e11000850306010b40750049000c4801103544040600940c0c810301402701940040c42c10103a0024403030285490080162040305d00041da030b601c07204010b903610700c010052a0000340d0601c0000d4090121039001d1038010342112421050070401020b9040c403034012901c0d521490755113145018445284e07035804800394082d4a080d5040851940706c2c50790300c18203040d020b0134200c851300c005420400204100c41040b40300400b03034002410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 364226133 1250 364224883 364224947
    0xe1b0412060515011403042d060e16081e0c040204030b0a05010e04030206150a15120f0b030a140a0c230103060b0f0a09050a06050703031103010f1203 66
    0x10301501c1c80070b072101c500142c3c854654458080c0c4041c903518011941d1070341d1a41c2e90f07010101401904100380c00c1501d00445082240203a02100b000c1c1e0142c400807481000310035402d0f080541a84030303403004a06070b0408112000d13010607180c00d81e09291941400b202840c0b2000c41c02c4c4041c1c6010b481e405440001d000c8200502c40510f1802404e907040f04105580c1c88400205080c90150340190160b441807000544111008005040d040e03005000b40d00140c1c2c0d501d982c51000d000418001c80415a900e91441c1948050301c00c0f1540700f201c0d02d000707001000052000c00d0b140e031460040684540305000c2400c4800a0401021481e150300c010f01d000c1a0740c0e500100741110440c800390101604040c25010180d40c800c1c001c01050701c042110076450070088204003c031651141700d400c02132180c41400000c0710345d81c0760f10910042c55540c0703d60f90384640b903107802404c0f0b4107010104d0710600018001072101050091a04c0b081d1030102c20160041d043d5824142c0352034511602d100c80d8601d01c80c0000644403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 364227383 1250 364226133 364226141
    0x8060a0503071d061503040b0415110304112e110d0c0c0b04140108150409030e190e0a0e0f07080703060f02030f06100507020d050708160e1b041206 65
    0x3480e04051810390711200300f04062050003410800717503404240003080104054503d901e0b0001d109500840a0900101582c01580c403140003502c1e00d01008410002440501104d2030000403088030840d00005242c0b500b0502c500028908484d10303041403030581a120b000f407280c94042c3c40408125501101d45003801880288070300380c100c0e040c080c0080d0000d82608010705860940e096a0305c588a0800c0e002c00449469800810041d001c944401c04507105454503c1104645402955a00008142c2005014000c086d00544840020302d020003044031604c00366296402c200c000c2d4020440e60000d000c000d00d084001c7c0650451400b60803400261200000303001001c80c0d100704028451450003ca0200480c04222944825020200c0004a03546080b1800300f40e8100b8a00307040781400c00b2a0082204d00492507403c84280d400101c0502c8541000c12881c1c000c242c0d00c4544c0c900c6a07013850340c004402a4040d11008841883d400901c150065090985010702283d042c0004d420701507007003240c090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 364228633 1250 364227383 364227419
    0x1306020d1103132a091a10090f0b07050307080d141003060524040b03071a0d05060d02220b060c030703080903041512090f052406010c0308060a050307 66
    0x545900000019680040d040b224104c5800106211301c91415000c40003510360301c001d1004213034290480292564841103106000482c603076070100c1c8a81090341501c0009200d800184031031409101c5500059400000c80c7c0c00643d0110034141c07034241c180001800307001c00d1188000c45010180811180100070901e80f004c403401150184420f031280b4244031103d0003010400601c014400c0c81a17860f0f820140c01c080e085000141c1110326040c1ea40c0103090b080001e0a0288001c00da00048100c401d10250240c41e4000701c0840710441001400d90000380903100c1c800e00d8030007802c0142c02590038144c8590004009e14001b07005d85654000000c95241c407a8041d1004501041441c00814503699001098900307584203040c01d020541005581501e214154406087c949034503960100c002a12051000010030302c1580149404944500591101e44003000030100c0702200d0710810180b40e0380061108002c03a050b0030900f03005e0302c2d400f01041010001e904003d4043c8101200051081c0c10704041c2900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 364229883 1250 364228633 364228643
    0x807080d200d0c060f050438010611010605031222030b0708071803020108010504110f0c032502090117010b0301090308160c0b0103080a0903050a0503120604051306020d110313 77
    0x140c4500300d05c80100d41080d036010344880d01e108412010340d002021051035000f801d2a02007110f208603813548444120903048140002c1e00d40c148145405406d0042c503001e4941140680348103c4140c1c16600300d8015a90380c1140d44100c0100b0040c0785015403040741c00740d500800c0e11030051804140107000030401784d603003170000342c50b420410003141c0c410102d010990340d050303460600307d9190504200150640c01100c8102c00d10030402001385074101c1c0d000701a030000c0c10000d9500c981d440d546442c081d040116041104055210712400144d49445a59042da000312200103480202404814010000d1080b001d80561070202c5060525412154041c424001c00401c1440e041c3e04041c112160410031100a0070800b01d40d006000195280b030160043c80c226142982c201c558030340700ca43c90300300140b10543da0f0b90000609200915040d000099200b01c050301e040c4001c0c00c040207006911804007401070845a808180200d10f10b1064224120307184c0795040b45070316410842c9451810342151902240c1e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 364231133 1250 364229883 364229891
    0x12210a0c090803121617130c06050c0d050d0f0f0504060515010516020117010b0c0c0904030c0605040203340909021c02010210140f010807080d200d0c06 67
    0x907140e000007040b60008503000003410480e403541e2000b2142c00c1ca480442c0418030119418812142840a15107071190320148a098146072050821130f1002c80707145c0202701042020040c0e40c0c4600c000003907500c141e102a1500076950203650b10a5001803c005201e588007034101b90726a030098035550060340c0154000c65082180e0b494501c2c106041c10755400d4810b012410512103140140c0c2510080e01a540c010b061260701c01c0118407112503403081c00d030040e222504000c200740202c800100710040064005542e0700f911400d09482c080d140101c1d40c4c800410365522000040c08540f0306000760b0b0140c1c0030030013051000091b0309407143c0303594000c01024400304090701d000180ea0780c01402120866034016140840355141c01d5a10040042020f0341641507102d03000c00e104112035103205400015983e250540c11500709060b0058900b801a8460015030340003503000e100300c010100d82c0904409641c104051a00d10900d600381078041c0c80c640c40303038a60141c1c0d13000548803078011301d018410b180b03d030800300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 364232383 1250 364231133 364231139
    0x409150e090a1514010b070515280e030406020a110301200d11030c12090a0b0106050a0309080a0503190218040e030706090302071403030c12210a0c09 66
    0x58400e04040361212926031021080c00007284070384000703148182211201290f60360150850036000002a400105121070014140092200611002d443d4010701c6000000354107103608102c0c2008038070400180490f103000300f03810014400d0b43c020004001c0381d00c2507a446560300c00700070307445096010b03041d14048804011200300c1e03d010321803c40d60200e69400c1a0454850410341f1100750803d160416441e95601e0007412220500c6c0061885083c051040c0b42d0b07260703059649203050716405050302c400c9500511540d800a050400c010b03040d00e1041c54669101e0001001c2100500200315010f0110500002c3c1d0869440d40b11780114460b00b11a82c41240e2401600084401ca00c11b55404c03d142010005154041e0300e0142c104085080f5100e003100c0c186400b948a0b04210307121000f040700075a0048500700318101b1009044030403204118095801c010603084229250b0480000e0407070036000c0018540d20452410508001000c01782c2041212440e00c1107102c801000020142c40c04101034031000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 364233633 1250 364232383 364232399
    0x603020f211c02250911120c09040e060714030a1d1e0a0302100506132316090909050304031208010f0b04060c06090809060c070e0703020403030906080402040f02040915 74
    0xc101d0b0101e1044e2284003541c9012103100042118030000205404100310004000c4c2d51441494018502280c0240c2d66200090400003111501042c0007a40e4001e0300420407000e40080c01511a0000010b00725a29618100c40d1001000d48542020074200c1d500340910301c40c080010318a1081a038440391181c10141d80030703220360320084560006d00503030242d600c5141d2061a500500d030403c9010304050f080401e0164444181c1c3d0704030120007002d411901d401c1c2c16400c40c500c10b468000703002580c0c17801d410140b0740000303100084600032880d070192031b02c03003040400c841041250001e64005a00a424120f8240020508070080c0310b11900421003420104480983c0e81c1100c003250390303a842e40b140c01035050340c4580140c1000401a1a60300b800e204c403400715121480140300c0603c0c0c82c40500843c1c1d04044e000703010f013000a40070000b0544103000500020b5000f80d510010f80e5154207000605540e0351000901801250144004036400441d0005100031f483e04a61102001c20310340c1d510b0140c070382c100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 364234883 1250 364233633 364233673
    0x17010e0c0415030f0309170a1505061804020a0b1b0606010215040b1008010c0f1403011401050c0f0307060614031c0309020d02090c04030b0a0603020f211c02 69
    0xa05031002e024450200005580c4044010748a4442e00f4002c400c03640e9030240e03580782444100b5103551504540800020011203000880182c520f0100410007401c261022840b00c50101c080fa10403000350782c0200c1e09650f14440403800800d07170005031903500d2060481803104048082c4100085109410101c2c02c10340c008950f00181400081141405a4464540e6200b01c000500350b036407800e02c001c0000c920320030280520b0a000d40307291104600d012492100902400001040130b104c0e00d4280014090300d4030040c500c01008609181594550b510031001c14102002480c1b04000c44c0300004940c0c0c10403403250405811148a6030301f5141038010001810b0b01e60910512255014440c0180c070b80c501030103648903145a90018045180000840c5c1c041550200282c4086092000c081010000c1107d080091075202d184020700384019480c641c04965030300000181a441100546450707a182d803400e51040400400e6001254400081c03a028410300c5507030001e02d40014000c0d85417900c480000121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 364236133 1250 364234883 364234901
    0x10203090a0209060f03101a0a0b0d0c050d0203090d0e01020d0206160c0f08030a06050102030a020a15090b04150e030403020f060a021c02010203101d06010e03030417010e0c04 77
    0x40070308250039080e0b0812800c01001448550700245001a4010680b01000061280005400006100c0e5940c05007d15410505c2c5406031082e90004000d002a411800680f5072900c80d442c808a500340b0190800e840038080c0c640c411a0303c51007c002c005142900040c00041c020310f40c2c442a001e803164000480e110780440e8803520240c0e001c1c1002c40e03c03102e903004007019a85e13820301e041100c109280e5506d41d49502c0307a10781a1030b6400d0100c1400100344a5200d0107000b02001d000039480c088100030065243c888440c005072000d8081e05603140c903c8011307081180c0c0d05501024034107441c605460450820820900c050301070504d401483e5a23000800812102134907001800701e05c613000a103040000c25800825014114003d001e1a980361802a064804501426800140c0c49242c00920120500c6165101e0700c43c946244031040140415809020341190081c44d0842c2500d00301000300380303144540e50043e6224000313400c240c480c5c2001903000511a0a9003004c4e50b204001113420482625100c40d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 364237383 1250 364236133 364236151
    0xf0d21180f0213060e0414030d0212060301110c25032312130306020d140f0f06060f0301050402280201150806040b061e180103021311031b040b030403030617010203 72
    0x1001140115038005001052a80810108c919140310417845506070b80080307060044102504080c071280b4034080c000e9140c0d0b1511070320161301f030400010f00e0315561001401221000704204001c1521b40e0a1950408003441d041110300e900c08a141c0c40f0218446881400079a00d030041c01c441e00c400e032000c0d004481c4040c00c54184241c0321811511800020f41c03103585000012a603070300c0f2007140d4202c1194518407411407a4a07115052030801e810701059100104401d100f0841003040100400c0540c0959041d50000c1d100140c072030300c0d10303052241e0000f9041002110001100c80405005071305410a02c0b034151034080070110709a40786d9401ba500c00e019200200b200700010005a128104000c0a13842c06280311000c00d1481202c00c08511916403c031414804880c83c44014015402c043e40108000403240e902088401c03d40900f003200b03808042c0c4034481d149000003c4a00f1481540191400740c80c81c99407080d42ca00700382c17170090300500303262190010400005649001311365061003528421840b507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 364238633 1250 364237383 364237409
    0x1060206100f210b09160611150c0d0f0204080d030e06040f08120115110303062b061b14041202060f0d0219020f0d21180f021306 57
    0x1280107400180343c0c84500e200e5880900e09030201080d5100f640074003621951000e00510044070b0517649450200f504200203100c4c041802c6401020001404a0111140c0b403061105407500510f42d50075104079168031014605204523200d080340300758010001c8800200488000300040c0030145c0a031400d884105000c0c0d044040028013050314200c603a580d0a1041040910780f10741301d2092107440000707070000d104c04d10741002d00d00200380c0c00c00001301001461400450071841c0040005481c5a802030004038200d42135000d52001d440d606421000c02a032204084c440e882c03040070b1500200b03240d821882c0c0040d0340c610b015003421119808580603590000c070110b02400140c1c003440034503841004c403190304080030884000a41254030240054402c80384804c02902c10a10000f440c0800041006140e03810400f02c102c292904191b4034407940206401402c8880352007a2018000c0c01810303848440208a9040762040100820f014402c02e0b10072984c044405002200c12021219103002e5410b0000b20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 364239883 1250 364238633 364238639
    0x603190b04120203040b04090b01020d030509031603030b0a061806030c0518010504090204230f060a030905010b0d0c090e03040509070e130f0213081c0507050c090f01060206100f 78
    0x2c140d40150070050b500441c0c1c80c29544216081c0140c0c05540440b0050f44d80d0084ca0303515607818012541104a035160a002d40e007010003006072284290301c1c12440300c0c050307a048181018001e4003c40e010b207a0043c4400d03115035075014003411002581048440614134031801007411030082c40f03843c075121520780d034450509686500042c1486608940320b418031805100000b07900d1420300041018145144c061101403070610030030070010000300a064420b0b603801c4410007442d01c4c0d44098a804410070700e03001c615031000e4182140101407421141e900000404251824084840364180071200d000204110101c43c0c240341640380d0045024440d80842d45001045120348920321b602c000d180000c052600c1c2405280c1400c0032031300c4115440b60318580206d128030100441e5540c01d401090701c02c0140c00791404d0841c100207880d41d0518840d050010200c0c001e0180300b03040041507641c100240c860210b42c20000c040764079150017442440014494540050078171443c1c415031031b0072201030520000113581 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 364241133 1250 364239883 364239893
    0x501080307330c0e12010b010f050a0302070804060903020108070c05071a0c0d0323130b13060204080307020a090b36040c082503150902090f0603190b04 67
    0x461086902e4a24010380900c00c0c40c42c0c948185000c5a680c0d844c1c050751018484103221104003407050504c002c0e4904024000b490b60400c1c0d60100b80b010603d0301e15666004040300360b00134064124050298480442d021402035042a080802d4170f000b6200c141295030788180c201c2d6004a201e000400d2070304000300402680c02140d8800852403d5209402d06040d0260307405494081c054006000007030b02e40e102c108205240ca81000c03088504090700140e5403070400c406640c03203522100c1c018442456100022020250703010700c4c0c0640ba501c14019541e503640c900980399aa0007000b000c2c2c0c030422181400052031500740c401d4401c80035010340b00321044c03a00c18001d004e610100b08078460200c1c80e0100303042d245240d00c400c4107101340d1042c00c000d0401c5052045051a024000202da0418010389500380c1c080d1000c4250b407000c0380e521000c95507610007003038034040161105090094005103900240704402135a022184d200700e109400312031046200084031391240c0c03210400038203034010402c017180c0420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 364242383 1250 364241133 364241183
    0x1b032505241c0207210906050a080613110a0305061e031e03040510020709060801060e0103170405060406080f0901050712180203060412021510050907120e030a02010501080307 77
    0x142c4450341c0141803240c25220ba25081d6a00d01940d0380340004842804081504415407202516141c038240d410009000c03005441081c0c040c00091240c40c000c08968048002a00003050051501041070b0701c4600071900980079090942c0c1c2d00c1e1007030104c1c04061500c25141506540c50900003002002040d100d01036220115080500c140003500007000080340a854550306010070b0075483c0d00030320b070f070301e28001319001103448940051040b0703410080100458841e802c040c0d4192608148102400760344021140101c1c425a84181c1c1c01850109000800540220510388203144486024086503038054109003258000c803100d0001c5000d14101000c01d01d400d60054450340d2050031005090303401d40e00028502007048400320745070320040381440103603941030100d81051035480c6002e40c52800e00c80b4a40300c0070241c42c00f594bc0240c0c004c10005080904c682601c401015407803004122640c0800815520303940f104551401542c02c0400002c1c40c0b646c000f00b01c9060300c0e000046040e031080541d507010410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 364243633 1250 364242383 364242427
    0x50406050a0e040204080f1c09060807120501090c02010c2316150203100e041110030f05010803090a1a0f07031e05070605060609031b03250524 63
    0x100070b002416019403a036100400c0074007141d0006001d03110002402c6403500085840c648801c285102031440e065400c00300034416a02030703040550030342c0d449002c01c45407410503000c0e80c4406d44c100000041e90054943c40404412003507030091101c092006c50a42c1d80201225038202010070068000c0f23080140103016203194540d00c0380c00441c044103900d8905c0156568401c844800b940001407144490604000800500e4001104c80c0c20740380540300c807a80100030300480b42c014141040e046801c0c034404d030f010010356070308024100019611407a05568035001042d42e28080c14040b08003044512450007007041d0a115002d505240c400d00390100f5009400030b010450a026481d4548104520380740340d20782c0021071036a510303629511281004410365501030240c900501080100d003030a601e01082080310b0b06101002002c0403010000841d2a0418034101c94801003c6504010280c040440d425070032110100c0d41c1800382c1204966080412030034500103400c041042100300c0d0f2801c03144441d40c0303071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 364244883 1250 364243633 364243637
    0x11010e04020c030c030307081012020114070605040302070501020f070f15031e050a0f050103050a0b180a0b010801050606031e040f020a180501151d060f0f0c07080d050406050a 77
    0x41c101441d100b1031650300f01800254041d04040104082c2c0c541c0314040541c442820282240c407503203050016600d4491445020b8100040b80d14801c0280e1071100842d00031f43c0d4040300c20415450075003802501c580c001d00800340103000303081a0741c0140d800021503005648018003a445001c0c80c1c200300d400c40e55031212581d814192a1000c040074050340da014080c6c1015414404500e0749001c4800070111140c01c1c00c06080d6528082c011300210350006025103c950f401402c0c8519511841040c243d0110f6040c1050301d688a0300202004100c908801c003412654124002d0202c0c0c0c880d081084424001120800100c28190b040340c00a81c030340d10380c41a089030088240c0e030f10043d8242c020503032145080e0061210441030310051000ca604134800d00c2d004214591a02c0745c81d080c0444018041010070b46810140c450049101d5902d03505c01c411a82480110a8041d503181e00707000b0964465041414200442c0c091303280e000030005000f141d40f628003200d0f5034809151078181801910b175504540b141d201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 364246133 1250 364244883 364244887
    0x1051e0301140c071205071707050a050303011503050f0903090d0816030309050d08040804051917011508061b0313051e0c060903030f030612060103030e0a060c11010e0402 75
    0x19401403409080e4041c80940c2c034020b6403404d031401c04ca00650380e176076540e5080100801c10000401c260b80210b00048240d003801c2c40d550306050a08916000c520710002c1c1103408004000107503901127003800810320502d40c4007802256034000300070407a40c2d01210701031040e8104003d06866450030f03d03050b0f600c0d01d1146607050301704020324a940070090030381c0001f01d02003980e50b000c50040c040108420b00d23102240f031400038164901507980d044140202d100e1240921000d08200220641d044a15405012034031245500900d0410800f40030380301d800c50b03a1960030f480180101e1100300c0445c5561190460710442254248506044240395200401c1a8941d600204031000090401d0001582c4c0305010003204071105094240241003500c0f0000309841040c1c1040300ca000350b140403050303510580da90074403e5120390712500465880000f00d10580c6071401603000100405400c000b80c0c00c0000c008bc0c074140400c82e00d0b03100c1903c0100340c000003e05083c81e010300000750345d0300c02d17104449681c4010340054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 364247383 1250 364246133 364246151
    0x1120b330c070e13060e060106110f10110408100510060804051903030905031309060b0c0c0f04061701140c0a0e09073e010b01080c0a0c02100809060f01051e0301 71
    0x790440d0031400e1b0840c03040d001040100000780c1e1221074014401e05041c082c0415004d4401c0b6581d0b141030b202424510141c65800e2140e0031702c4a0804d03600203280c100182e9800c980343c1c0d045100101400c4071613050760780c454040400c2c524843d000c0c1902c516880740041c050b201c030060043c00c0c640d240400c100c003056141c0500b440018010300c060320213400e58645500034241000720350400d070307106a0018207074550241702400d00c008001407204509001528080480702414000c1006031100b900300d4031011003d0050001403000560180100320822840450f07151a0002c1c03401c80303849004100c0000131090310705c2e420381e0304e07144445580040342030a00300c2c0c2c45440401040d007000f02c0f0309400643d0081d075002d20130185e000341012590500c0082c008001c00c20503035002820f602d00146c241c110b0303804c1c0820480011800745100c0301c21942c00034854848001300302d20040180c1d0049400410b40e0150781c000c1030b020b4901d000014140c0f003004080c05078525807043d40c2c00c00b00c80c035808440d90540d01c0700350300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 364248633 1250 364247383 364247393
    0x10b0325090c0f030c08091020030910050702030310091a1002010e12030c0a080c07060f0f14011a07051c02010615090e010501120b330c070e13 63
    0x40200990b103803602c12189101d50800b9040303502d4206800140480755040141c240e8010483c43d07242113a41c0c40001e544e00300c140c00c20341015241d807102c4049080001c140701c0c48101c002060f01d1041402d940900c007594407200101d8072400203079030004103540d8040b000e01c0100035942048000842070141b50190030000c00000e507040714a0f074170102c0540d6480616200200f410f011010414805040a902c1c50400a840344401d208524901d4100141c030030119078039104c0384080b1404a0f802400501011210782d0740c0500801100b0b00307800d2a14a4100f400b20340041184c42541200c401c9010082c3c0480106008805507006120444042c0900c2000d03203800306c40d04840503400085035000007402400d2030a001e090705589200c141c240481c14400304030700760303c210752603065800178a010801c0035405014840680501c0c260107600580c04944c40c00154408485454141c15480c0c201d034443c00d4920413a986031180c03011241d01c0d42c1020034248a441c1d009042150458040000301611143c140c807a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 364249883 1250 364248633 364248641
    0x6010b1810180503010b060d020c120403051b09161b060f02070c08030304050303040204180206030412021006050303030136020901080a0c080f04021914030f010b032509 74
    0x8001d020a142408241c505408142c8940140400350001c114100048001801900610700d660b4030481d000280c10340100307014408003c0301001401c81e10b44480c2c1340c0c03414603184c003000400700c924450111107000032880c2107030140b40110141c003c000c0c0407500155040324020f080514149040a522000340300081d0b980c07280341c0301e01510300d20041e20f4103c40d00d4110001500e5601008242d0710600c2400b020138404000c4941080d411a80020300c841c084847c0b21421440e5a03000e9407011002c0200814460b942070f02c849000c206500b540c04a0303240203000d074116411800748131342541c424001401381c1d1204444110400302c1c054001d005844560144050515403081100d103200e80100e22070400e03507048041143c120400501c28407844031100d200400741c581c010b08503180d00385058049001c1d52070380382c00f8240380388034041c28041d16501e8401c0035101502441029000e44154001c1404485061040c05502d003c024003800d03207000842200e982c107004003a20020702c4040c00c41d0001c0c8844503481 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 364251133 1250 364249883 364249909
    0x51603030306080613080f16150203150910030809030a08070f1b030f0807020d290a0c020319121b110c13020a1107061107150206010b18 60
    0x6408a595410040351a04014001c0d004482c1200102c0800000408840545400c504c0342c1c0030540e110311080b848a170f82314030000c40140841265001100b00c00c0e000307800440c42303044030000c0030000002e004280032061100700c40f10b400030880a141031001039040030007005461401411601d0607003482c0c0301d0480360340c45642c04643c5200d101140d007080003e1844078201100d10384c110103002078a1a12821810208224010688040011317034404558400343c0c10440142c001c1034001c1c03001c28400c081090f0b0f5003919210f0708008005400908001481d028956100303c581d8003035410225043d03022000d4280078542c1030280024421040341e0083c59100741c10303444030115a02a802d198240d0042c00c070248003c10364003141c200b5032604c1c0141e204c1c4a08075110302d0818030016030b039002910003207480d031008402e4803400d4052084000340395544400101c88a50b6000b06071158107548022403000340c0004001d48025130082c07401041424641e9014054240015042d442d03904a02000643c8a0007001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 364252383 1250 364251133 364251137
    0x1b030a0515040c0812091023030910050411010e01120f0c030524090705130803070506130b010b030406020714070305010b030304030c03140705090f07030b010c0b1305160303 76
    0x100030601c030840d0482c40c01040580701034030111800c501818002e12400189902171901d452038007c80034801c410174a000f4140300c90800440c032141100880306c0e4416102444a4883c4e2031191a1001c02485014000c0b584000d030340c1007400d641401540c0c912071082c0300c01d0501410520a851024860150710840c4213960400299449494006000c564000d01103514020840e01d41e0103446c89404901207030040100d404105d9980c40450458280c4074001178921024805107000441400000203000c100c4d04c00c200361440c90340c9100d101f00c0b2802c41c2c5000036280d400324100400800e8610001990894015a03000d86481e40c07580315802d902e03480d90325130800e9601415082091200a10909000400441c040e514103481e507202e04060000c14000608500503006504038003000c00c004100082202400d54401840c1c4054844d0b81050201d07080004603082c0211008150301c03a030714080e401684800c3c044000d4842004095000d0341131001128607114444081c960180d41d0100c03103008620903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 364253633 1250 364252383 364252423
    0x91e0e10031709060a140f07050f1207080d0905150112030801050102011a010e03010f0c052205061902070e09030c480618040b01020f1b030a05 63
    0x1d490414610454503040790100d0718140000052540da2a003101c03080c869626042c280c44a640e91100c0662180c128100c16800300010080304008000c00c2d400401408007040d03c1c40c000e090744910340700e84503a4034001c0c2040030800160384c403006242e11103101c16009008981a0350040100218807000c00c1c1c005492010002318140100341e848a80075003d082e0a2009020300702008016200141920003000e051088101c515640b85d1425444040c0062031a4014041010306c0040645181c0c000440b4402003401c203d0f08010740310100c200341d42101c0c00a030020346081e0615505100b8502501c20001c2107000f40c0d0f0002500010340c8441c103005070540800b541c0c3d5205c0d0141764030314004c2400f40060950a20000f10174240080345d186038510060103c0c0182000c2941408c40b4194000b100540d9024901240c0300101038140b4503207126003001520100250141d420042e0f80c0e809580303d00c0500744c3c0c00180030301d030780301d44410151640f008003070101c1c3c0d4082c140f5a01d10341040e400b8040d004280c109 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 364254883 1250 364253633 364253639
    0x16061b020a20090a052403060624030c190f090e180111030115080609040b06030a05010608060a11070c060509030f01020304141c0203041e12240c091e0e10 68
    0x40030300e06d1240d002041c111080000ca00340c0070075201c800041105200341c02d603a421510042416003060000c607408101c847d130f280781050008c8515042488240c0002c0b51a0002c1a0310600682180c400452141c80e05d000c41850f103400800070708001042d506217804c84011042000c142402916800c1c00040c50403034480d0704018403501c0c42d4104c200d00b60b0412101c40d00f0300040d07884030b41d901c1d60010b40001e03600e075003580e540003c40c0c540041035000900d030390300c0c1480020302c1c12808104607004a8521030b06100d680c0e900e0780e00c1641781c020040b0207495028504c0040011600800007404100c00140907140080b212480241c00c9070400c8400341c0b50002c1403032515100030014408420070308240741481c0d580c8816214029a00e0085008000803038000350313a402c0000100540b03000061006800c11610b84030a07182c07078040b000d08101c2c80245c81040b4140d102c0e1166882c000c0300042d241350354a9524040c45c01078154030031500380c50390001c404440ea8020500d031203500070041c0309104100000c4902d80c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 364256133 1250 364254883 364254901
    0x3020d050f061b0d020a02010207050303430f1e0804060b030d0c080d0b040c27050d200405100305122115030316061b020a20090a05 58
    0x2c401400140c001516090058100484209680090003d2440141c0303402c3c20071016030083c0b04c1c0d440701402c20322021041010182c81d404100156044001d20800080765214060310041c00d40d12541102041c01f800e440d075064030400c1000c04982ca245056401e54002814044411706412400300000d15100100003e101c558024611191001c0c0d00801894170b000100400a01007103400500081c40000e206141d081c49400c032420407600104100a000090b0001070f082d9000001880307803000d4000c09120440800c0d01220301281d4029140380300480c0c5650700d203503403400e0f54034004240c00601400880280ca9170b00c10700f4170466522900039060340c10343c00c055280240000804040711420880b49070710a107110107020900d80480d09801c0941ca41c040c416008020840400e5011720022540f00c85e0140d01c0c115241c4610f008542c1040741400c0e0800900c280d00e60f491503140543d210716428400034101c04002c00c122210000d800300203400c81000180818403d6540b80e801070740703900c24000190 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 364257383 1250 364256133 364256143
    0x40c0902041806140d020d08370c05061602030705010501060806030f010c0c06050c070204050a240b040308070c18060905070e0901140f0402030a02030a0627020a0903020d050f 77
    0x5410014080c0c07a9084c0001c640d00c0610038002d0040c09a8a101070401900900b5180681d240141144c0c640c008000d1240700621158040250290070948060304280030b1407156800780e8008020b850242c0e500580c3c07c182c0080d0f0080141184010880f81e00070034000e1180d02d020340300d01d94481401e0b0170040300b010300c1c000804ca142c0015034580b6101f80c81d0030780c014580d80b1003140d000c0c1c0040703565560408200128028441b01035081400c01c810052100c2c06c50380031401046011201c1a440b4103a0105a4082e461500501c0c1d02c407841080b00340045000e040251141070701c20440c1449040d101c6000118031203020084e8580c0c6601c684042c8141584c50044a5000a1900d40034401c04000d10001d01040c10602c142035000c0000c1110041688445441907492000600f080d551703400c0c02d15061000313600444100114500e0102c002c0703030b0b4601c08030b1200700e8501c15040c0c0005000c84c2c0c10107240258041802d050500192185c0040142c80e0700128090160080c4054012540c0e8500c0c514200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 364258633 1250 364257383 364257389
    0x110a06060501021c02060f04140f0c01080a0606080f133e0906040c02070b0f090909060412051809010303050705060c1608091504081e030f03010608040c0902041806 72
    0x102c0c1d0a10843c0c031402e174005007440d8080350078819400141c071141009a10300030314054400b500d024480c07582c6801000020303011180e020a90350b06007642e48941e102c0c01110841d004003400070301d0141c045100d080d845070903540c005000c10000c142400300d50350740008031000480c0c8951100b44440a1405218050440f0109440e240c28081d280030140000549070040013001507100c1e075641e000c0c0600681c401c02c40100039150000e50b244c1d0392084940e520300c460300409441d40c03084c111480021403046020903102e000d107600c4a4003081c0e94062460030703a515040003544040740a41424900040d0751001c854600850107901c400d9940d003400d0405074142440203040e011103e40800043d00d40c114070070001045990070000300342e25017080600041e21022440b1084003900300208003c03c0c100d00202c4d00001c1400303000aa64904142d11240d44c1d200d0054500c01040c2410900c01041024001c02e0036a038410f204402e43d94125454415842c100d802c590001c0d504402c4804d0440c50341e1031a0f109010103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 364259883 1250 364258633 364258663
    0xb0709050d0b040c1a0702041b020d050d020f030114100e060a030c0e19061812060f14250c050601170316061505040216060b01110a0606050102 63
    0x21890a1102003820018204001461400808002018408800c0a10019207010302c00480c1c000c1c02c4040c01059a00070b40000d0f840b562800b02c10035100e140450041544006540140101c280a0310040d40c50b40c10044213191402e03000c1008502c0c1094000045010b0301e0f4a075090040041d1150a12014441400c0800c06000c100c145014a90303031580240e0707081e500303d8540070a01c0580340d00203e801c030346207070030f5503400841c58080c5100d6040c60005d481c0c140da1441d61540c44000d10b001c0d001c03250300e80754401e04100e40380c040d281c0004991541c01c90000c804a1810228450001040c9941d030350070112141c07440114508003400074441c0b5800e500a10f0103591501c078209003003d40750507031511030601c1510199002200c034400560402c0c0250307216040190f6030709001c10450b06010740900340c07e141e03100c0c000341300c0400800c1d90b00d803501c01e40d906800018031000703080e40a9510070f00201000d4400c0740c180005060000300c0c20f481000501d0034140714120100d242480d0400185c5840e000d855071000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 364261133 1250 364259883 364259897
    0x8031b070c0b16050a1110080c0f090607150618020c1203040507080304030f05010506040c1209050c040e01021b300436150302010c140d0206040b07 65
    0x1080594400d2000d903071400400a6a506010803142c5a0100106004040c0d0203007251550501072211081b03081c0d040300b0344506903040c5280300d003103401c440100c6030300c0d140740e80c180007400d1180031045c0509510035020301072915141c03980d1100c0c001c40b4038482c083c1c141c2d40d807604014040594549007240400610420650821021018040d1103121081c0005030035040440040c1c00e104041003284000d192003426a41da03144c80b0305185401c202258000e03034a42d0b081101155080c1403620419440311801e542d4940d214101041070000b5010076401901c403131050404121075a070b2140700f201d1600d0702c21000180e566006202c94010700000e022500c0301604401f11540584035980c1d114030a51141d6403280842d9a800342c2e00074210f00440e001030045844400c440017104003040351a40000c0100a01c811020114518482c141d40720b0b50760009440822480800055004004e038480e5148079204180340c9001805180d80313440c035840c0036100140d10140500051100c240b815541191301450085 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 364262383 1250 364261133 364261147
    0x60608030304150c0c060b0406030f1b08061303110c1e0310060303090e040f0b1608100312050d0f020a05031909050601030f081603110d170109020906040803030408031b 74
    0x40d151700003902018010079141d030f141d0403296907564403500184da4401c0c0198248091410032143d460012034a40100207140100880c0030303480015424403035203034030060814070f400c0c80e6001c0355102c1d04aa071001c920b102c0d07401c9c581000c0d5100300540c0c141900e074080704000549144101842c180020394500b0a0914020044c0007003507120701c501c0255880d038200f080d843e40303c519101015000d500d20141200030124180701010000726160001260a56030f40510f6895103800011024940e10004180200204d480702c0d1050040300034003005c02030000300043c02d01e2844095405c8e0780c400400c0000249000041203240201525080d2140d83c00384c10410103200c140d9078060390307920f041c040030303124161020f824410401c84408441480c3c61244158006d0561460b000c0c0c200d1307200b0300ba400c4150003082c80310041580710710043c41c3d02d0b0f0840c1088003035503482d100c1c040000b903100c15080c3e17030001000c12000c540803108100940c0150b219842c01540da2604000a04083e4030b403004040074078900f00b0503a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 364263633 1250 364262383 364262387
    0x724060e13020d02130903090e010b03090a11040603021c05120310060804060b060c07060206011d0a05060102030909070905100e102f0307060506190608060409060608030304150c 78
    0x1804194180c0740c0b040143e003940000b5401c90b0030100d094074814107004c0c03042d00f0550b00000d81003c8502038606207006907200c05c00741940d40421030b1101000c1d4014849c010225448140c5400c0222000d0000079105d500c1c0d80105035030021104080c41c0b43c0089074100402c004042000a2009090801c0c560842c01e20440094841d01d007441003074100040341003c40d00b400002c1d4029611580300074005682c40e024070201c42d441e00c2051182c0c04c058041c02000096400000c0780744510f500e20390814a281343c2c0c441d10603100500014080b541103102c03c0c04010055103416000707030302503c81030f00c40110043c9420f080042a02c01103d841080101c1903104c3d0b0843e480306d4606036651703070080c02c00f00c1000d0104050161114440e08030b0300100b650120380902c0c400404030040120314040c18080c0f110b580c0300c6042c00f51221661030080201030242004004c0c95125006854210070014404500444140c4640d0192500707074014a4040c2c2000090204100d07523200a840200755200007444503040040300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 364264883 1250 364263633 364263661
    0x51510050a0f051209010b19060e130608060916060215190b130207031d0a05100315031a0a09050309060a11061f0905040b06040b01050724060e 63
    0x30000d010b0a45102c0300c44900400a4952001000001c20118030700500000d010708160720845000d01428009481c2e0040d6000c1a2401c0c0c5410740c070f8a00c1220051401c0c028102840c44030785038815981c0c00f01040e5010180812800380d06500f0050065841102d0107900744040d03540300e88150751000b90303410110042018015408009061561041c1d41c0180c1600007810700c01d40015400485600b03002c40c1110640e0242000034083d0341c0b03c45248406440070100e843d4002c01c3c0e181d00400e101d0041109181c0508041c030015102d1a01040c107020a81e0182001e0f541c81d00300701c0381c0010f410b124102e020140314106501c01c12805091052510989032184c891152050481c0191400075a040c942401800c81c1c0410366100740840c4e49520789101041101000d40702d4200281d106943c1c0055111194080c81c0d0043d50441c03185007180d1150710400c4001c00c4094126810b0040500c495008904140c500c2280071950302030402c04030032504250f408a40c2550060b00e2252a10303010f00592048100d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 364266133 1250 364264883 364264897
    0x1011070b04051207230102010b1503180c060d0209060d060b030105011e09090c110604050114060102210904110703020a051204080c13152709020603060405040204020d0f05151005 78
    0x2051744001d010700c5c1c0100d0140180c50b0800e50001460744280c3c18030782840005510640c8000c88145110709655906510f410784044201c0d80080c0c103201c44190314059074010f018254004103054600002c2081ca0819180c03140e11084070008048010403e079600100720000b108880521004003004185000d080e01e4a18002c151001ea42d030950f1034001400754003849030b00145541118441d24062626602801c8000074030441010800040384507540009441c126201c071645c500c0035250b8000400740e045412000e05c20b94007580391070a0001451006000709180d80c041c0d8003400c2e141d41a400c10a04d06480d00d0011014503108010402444001080d02803900e4004c4604600c25a014101e1b000541a04921400801001400012001020040c035282520b051140442451101000c90221080b00e02c000c2c2d00304104100155441c45c10f80d0002d40c0c842c0c4011b000605004201b40610225400381402990b9990b0f9103042c070041c003081501102e02c0b000f044a40014418500c01d0041990003500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 364267383 1250 364266133 364266179
    0x5010903021f02071d04050118020901090b04110a020109121b021c0b01150e040c080a050403020a0506070c06140c120a0906050705030a150605091011070b04051207 72
    0x10000c1d120b41c401d0084c2d90050400800e200e0f01c64200c0c0d1010626150180c800312442c3d8030307180e00c4803080c01c07070703419010541034000b01000c0d000c1e845d10a200c805401d103520300b00d901075521001c018620b04030358050001c1c00d6456000040c0c0403124a02400039122007501042840a0221000b07020210014800030b850b9054902301050342981016a10500f941c510050108034601e0002c01c081c100e0362501c07102d4045da80d513010030117a15182407004445a07003441e580010400000194036420760380080c2d40043c800d104880907982c0d42e0315002c1c21701606580300d00003c0d07000500f003c20704c1072038003800224403103410060600d03062601d1440501e20440c524082085d031110700240310100654400b107180380d0480c00038003d502e04880700600903802102c03d81d60040c07420303003102160310074010044143c8402c0d44034686400c0004c400c100f8a41340e0907040d0820411032031401050000c0c180720400051005204658882d4245420403040701d508410361a0140d106000811410344001114039900e9940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 364268633 1250 364267383 364267429
    0xa14210d20071a0d0902060f12220f08130303020c100504080a30200c090103150f021314030607051215090403020c0f0109080a02060d0b0d080904060501090302 70
    0x11940d88001740508400103903001002042c846400c241e144003c04403c0d00000c161102a50f8240ca0482d541401d00c81c6640b42030708040105e800111003113250720000e80a00c0e150783c1061a407110045a902058001f100140c000c0d0118040d641482000700c9500c0d0401e080c4942000e0400075850f507104807000b409410308010201c603440e81c4200b0147e01c0001d000390002c0f41114103406101404850070b0610344490410790481240741201d02003003106210714010254412a441c50300d90349404040401a410201e50720303118440021200d10060030b681c044040403801135464545030717048400c58030801c14041d800c110200031505500400f220101c4060300f0703018000307032039800c8000048241030342d074240c001442c2418070091640006400180c2c18003110500c00c1c0c00c0c03e5000440c0c1e0951a032003182c11a5214264603401407421001404107031250603000075042480400092103258495410389408100040c24201400c0500400c0054042800e0200e48a465030f400301b081c20a024408080040301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 364269883 1250 364268633 364268647
    0x418063006110903071e050604140409060e100b1807081b040302180f240103020c160b04090f0b06040605090d020901180b0a14210d20071a 61
    0x89042038034140788004d02220052a25540070061445150706102d0100c1a10580001c2902d451070484082eaa60404c0020315034010800b40005003a81a80480311503480d60120304120008000d5000410340364000410006110700502030202c1c0c0382080e9980440b03400c0308004000e03400c01c000a4021032039400e60000c0036980394004005010385e030002503008032100b140404003841000218040c1c1a030f007115070541d840cbc0c1228001c3d050b01d9041285806002c0030000441c66001c0d9014040c1b0039110b40507200312481e1610340c0325560910340c010481032900454180000c48003841802c5a5070003005040040102e41070008055000c0c91140c031003017100000303504800d42c491483c1000740d282c0c050b10008803940c607a03a070b0386046820300b00000384040c0303003140d48903451030301c20f1994080358148130540c6000c140900a00c101cac9507296562803a414422151076601d01400c0200103182070380c5903500019080d00600c040d491362010304494000c1c2d030280e2414491100c503010001080284042c606640b504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 364271133 1250 364269883 364269911
    0x130503070503070b07110c0f0f0a08010501080105040312060608132306070311030c040e0c07080a0203070b0106081009020328060806070219170418063006 68
    0x118039140103045000109582c03042003404541c09005420940390b0408003150104c0d6555142c440700ca40a90107400c0c40300580c1d4a04081d03062a114140140144d0042c40d11191218295082a403020009079907860420050503400543c42c8110000d9160910909140500042c81d080014100c25201103042e00d02500b00158526840340e484043d040c00d80000c41c052100907155003003160b4220100703050082c00385840c0790060480f0302c200310b540c60035030507d41441040d400b0100010030310722000c1030401441000c030b0001405000701c0b0780c941e401503031303100b4030b501d0408106007040c0d00403401d210070002403000303821a603680841528010540182c9968416000390540c584400b860401e40d200140da03c558010a500840d05807102e01c0304031051500c038100c5c100da48000300d80d0b14401c4c082d5081c2c02040041d415a00461144441c01d10540c1420745440c00c1e0b45505001c120705200347c640d10300c000c10107a04010011050005580c00108148126510900c1100e0f920308000306042d9496000c60300c404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 364272383 1250 364271133 364271137
    0x201110c0a230f070302241b0f1603060b0a0b0d0e070915170708030a0c020a0b040905040b09010c140d110c0708010f050402010e04021602061c0b06030f130503 70
    0x158a88122103021000807403d40c0c45091078007051f0b000e02d02800983c02c1c07103000c5841000c14222810070036840d2603003c0803c1c584036400d0340008003c0c0e01071180356041083c0304220524440d4146515030034841d28619040302290001a03400e40540e0558004001e040c81200c03d1f0380c541c000b07804000c01e204414040e8681003211541000700258036040c02c40d068010461110b909036405c1c101007889103005e40703c00981e1084184a14800d0b58010031002c540a0302c100d1010b0303001e03840a0f200e850060b45a40010b0b10340d4005400034108240d4603410007051045105840e80c1000700c0800802252400000050043d10300100107800100002001d0ba90307840300ba44010307101151200541d45448110b54690744550f024030a0301d04c95030800d01c68100f06866842014000d0380d050b1540c1c8850030032074043c48041d4000662980c3e0710345682c001c04c80540c80d114002d0088004a02c1010903004544d0081c1c0201d40c46008502e02500b800e2080103c144c81d00c0c03690941010210a2002c20054686001ea142d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 364273633 1250 364272383 364272443
    0x90c0915080d090302040b0f030d050d0f0617011a0102070504020c0f030304051e070b04060c1511091206131e061103010311100f0503092b0201110c0a 66
    0xa10402c001881c1a981c4803c4510a980c400c80d4203000149160b01040b08000710407600c01e905400104402041c00e008900809003085092000b003440b14031100b01d64122105580451030120070b410710340000f80001e100f030072169450007000500d41125140002c1d50342c40540038483c0540c0c0e0004000c01402000c11a05800408000889580b45010b181c020303140e400071038200ca103186078008202c020490200d01c42c0151404640405c1c20a0b103030a2048580c1682c1003c217640380d09070044084459000c6014071144a40c0141070785039947c005009200601c04010390300d00703168000c0d6090000c0c004e65880c03034696440c0c001c1c0529110603140c00110884100c10040140300c030b45481580056003402a0107141280e018652015290000000f40905103161240490014012900d00d001e0b00303000754051a081041c441c12101c080000052013210300741181400c0c03a06c03810006007004000d40c240502c00b001c41c40c0100e420305020852000c141e8410841800820b1041007061401510315421200f201d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 364274883 1250 364273633 364273649
    0x604020a03240303090b0408060a0f0906090c180c05041a190809060105100806090421081602030403051209041812090b091008131407090f090c0915 65
    0xb000040140710401c2c2007a20048021500d034510015446226400f42c03000c4030f40c104007400d800e9441e21000030060921800f40032596990b2404540440c0310340c403030f004c507503803080300d0501d012414034000c865070701a0b000704400040e080c21090411164040300344c41c02c6030601c0d803856046410310003141c045405040304044441c2801c070200c0b5801640904258050b141020036203015989078014000e45c0d0244030310550114110350007103292410b101c81010350003801190b40c00c00f004111031490050040301401e080c006180802446206c0c241650100384800490004510349450b6a5a03161031310003d502e54042020007203507461058030b540d040313610901c021003503c500381c410a1030484030020044000d440080c0e106680499490030810443d010f04400800068951035162000c842001008024080c090040c030f20700304c0010142c0038013064180401020b0141c880c140192201101c4004040000b0103007000d0300c3c0400b15042c14403e01c16214958000300f0444003403400030240010382e0f440b50310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 364276133 1250 364274883 364274921
    0xe010c23030301180209100e0a090c030b0102070f1508091501060309110d0b011701090f0605011707061418030d030c1d0a050d030c08040801150803070b0604020a03 72
    0xd2200440154184c4003600b0365641a4030b9034031820802c9019902030590000841501244218014501c0111000c1c00505a145c295100c60b50a01503a4054241c81e01294135800c1d0f220482da01400004085c25805810310317a0540b410000100c44200c64034441d0030300c403040000c920806c9040c0101c0e502003604000c001c1c0c803565220401002410860801c9c2c890030302c0d0503844003151410403040340000307030070940560700c40c1d00b0005403610886040e031920000e59038a052138000510145401200c81e40a5500080c40d0740c505002e0349101c40d102c246035405074000e510280403240d00015138003d4080c440c4c0d540313500d070721086103141a009040c4000951620400c2104040c0030f5064000010021aa6031070001c421460340c00c89184410007240c40d40e001317440080c140980e003841c0079207140c0c5900a20313150901950b9a1100d81195115810584003a51202e08104103003008698400c0103140d144010b600e85000343d1608100120058407684c410b90b000190007880c0c1d4466080081c0b00180e000d1926 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 364277383 1250 364276133 364276193
    0x90103110d0f0c0509180a080c10060306060305330601090e0420030712020904021801030803010806010b070201050306010e030f0106230a06050d051909060b041a010e010c 75
    0x1881c1d503e944916032080d81060005421400c2d5541c21314000380d0808010040b40c0d006540e405001d0304000500c0d00c16200c1c0e44001144a422401441d0046020b010f00080e2142035042890901c5040740380500101200854002304440c0e080c0a2040361140680302c8065440e91001210080a1603000d8107500d0181e200748020b1007001145020b40c5a00070f01101c010102c0c03442455113a80140c4100b0944401ca84551f90260400c40c1407103174080e10081c00c2d00d10320f00c0001030000240d81c0c00e800c292003581020005000c84c07107041022130b000d400e0000703a107400e000250307000a255200c000c1406040121655800d900340d03c080013440000ca03000c00003441550f40300e800e90403502002d03031101074041040d00b030480c2c802d013014035051054500c10303610749281c96040c0300030030081c1c5030107410380805d0400b000a8650001191003400704c00c40c0300d80030101300720340b10004010a480c5c42103101c4090a12000c1850680d0384c0064064048900a0a200d03070400114242120300c1d0440c1002c2e44083c640400d80c503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 364278633 1250 364277383 364277393
    0x90b0a05101d01031506051b01090302070f0503010504080d09061e0c32160204060608011d01081903110109050708070b0f03010501050705030913020d0b04020306090103110d0f 77
    0x240000b0030821031452906010b9000440c180d42e00164590f541c410b00001c20301600d8815402071041100244001c1020442c0c1015942126100441074006070000c00c02404070161b11480f600c006e11088000744268100ba0f254414244a0389680c0042d140c0e5640c40b8804101142c3c21040000d400443c984c1e503031450f21a400006040c9001c4848006040170000366039a44149403456400c102080c2003c4642400d207000e440e0700c0c1d200c0c1660001c505507900d0100016a0b480c010315019261660b6050071651418644910300c101c20001e58804024020040c03102110024031072040f884440c00ca684000301c00d080070343d81300c031043c8260300055090003c030741c003030101c0068034000300c45aa00480726499614035800d400c0c0d003e104124071031031804000410656210383c01500a10340910300ba01c0ca01031558000030f821207980300d1500d0f00d00740c000c26214200d0400703214298071220255003d40c50b51802c900040d43c01d801c1404001d2002d030041c003d0704078545038084c0400720b95a000040c00c0d1100413138140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 364279883 1250 364278633 364278647
    0x20a0b0a1d01061505310306050a020a0c0305090a0e040f21050d0c140315040c0509030a0204091b0b040918030c24020d1b020102090a090b0a0510 64
    0x10350341929610140c62008540c1485810100c40c0c84000704e904030340d03001c01c3c01c03200360348007403284a07103003800090400324a508040344c2180e05401411900700e0602d1850540d0540d40000d2100303034414414481c1440d0070340c00641030303081c00e079140c9090750750b90000d880001c040400740c1c0c00c0f4014102200c400c0004001c0c0451400410902540c01c10f60200351082181070f4030191000312600242c810b0200c4943d04003550881c504480c043e0400d6401d04ca015080721100382c0048401c175004007a085110809414a44946003000307280346025807610408201007543c50003d114000d00403a03951001100348148610310042e40036060070744514607545c6644840b569000b6009902c085403505d80e060780140001c0004022155050b1541303980031312541c0f542d143d0031540c1c95a601c10403020080007544452588010070444600c94400200c18071203a9294607000cac441da0040082d6803040066240940c0c1e10080c0a003121610b01c404103080003075401050641c0b03142d5000b1504682c0b8455000c0e011500524 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 364281133 1250 364279883 364279901
    0xe0a11030f0313090b0109050d0609060509030f04180204050307030c030b0c2502040f05010f0f0e01030b190905010c030504060e0109020120010902030f0a030215091b01020a0b0a 78
    0xc2154040045520915180d214155580041e01c6000d9001c010031845600404c1030b001050500c0c000e400d43c0d0307001050351144c0d1084100e481c1507407840d0a604000d5140310380754001004034001c1d810700f02110b100032044d10540c0202d0001c00800b80001c1145c400c180c044401030003014040d40d14143c2d8134600501e40c00510f0204840c03a42091001400501d03c09099424040348a5040c0c199003141400103500031200c100d040c2d810a032525482c0350801d8903801914000d0014038074890116250664084d819845a08880004070403440100042248c40c0b03a4660400d40b0320164601030b03520b21000100820300380400920550a2180101c6055055400301e840749014000a00000c00c584804500b2101c10502c000c1c003040e01444424009415400030b4410b141e0148000240c000260300002c0c50140700c183d800d489684120401010141d060045001c20313030280085005904005400c03585808c2100000c000c05c40b40c6900043c0c5030382c400c000e6088600e400c41040100341c10b15000c0c1d00068141c601d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 364282383 1250 364281133 364281139
    0x8031512031603020d050918270c01030605030109050c01081f0312030c0c031d010c0b040606052107060c21110120030402130b060c030703020712050309010f02010e0a11 74
    0x31450400171405142200c4080030010080d00940e0030804440d60303100400b40030300109100c003001c80d2170f9540c41c9005106440204000030035001c2c03140000103060350060b0308014000c0c4d06081540000641c0007442051801c02420041c0941c0d0b501c3c2d01240c007001d1a54052010171508001c00402d210741c503061401c2411481d90103102e059810340c02501c1c1d211002c82c00500080703406190105224024143e4500014149020034108079603480e500c05824040d1416a2229505d00f001c01c076500d00000a412002082c030b041038070702c04442888a884645070f125500c18491601c100302c0401c1034055103550081c85158010b02c0341340c51010001c00c0d8988a2105030425840c1c59001585800710248082078000214280f503e5503403950f090004010300c203281c0c00c50349601c510a0309a80d41c3c2c2c10016040f0280804015a11106542002450915070b640501e0300d916481c02d400740402c20201c100c9000382c1007070a01c2c12602a451504a00510200d68a03040c45d0080808103010803611141c0403280386021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 364283633 1250 364282383 364282393
    0x30e0d021f0804050712050d08060f030d080a200409020f070b07031d03041401111005010b1213020907030c020705030d2102030708061c08131509030803151203160302 73
    0x50f940028400d080c40802a0240e0b11515281808c1485012907a0f0b201802070000a51b00c00352502117480c00075407040702d06c00710b1043c60400c5400c00d682e21401207a07401940c0200b2031000e100202c0c00d4170380320398080d200c600c0c0c2d00001c4450300341187c0b07011100220340c845030800e400d14203560010001c1c000b5100465180d40f01d0244c46c044030720000306640903038020807040b0060101d1100191035001240021403514016146410002482071240d14002e100c60340c1c516075506c02c03143c2a0020220000c1c0064120b015022171382015813584004030398000b81a0400240c4410646001d914101c1c10f1390003683d0512450303904800300c6603c07440d101c0d840e1403000d0b0740203c080310706032016082e4002110301c6000506a02e001418a1406884500c6091041550f1200d0030031144c440781190340c01019400e915070900d1a08104103107124540441036003251520210840c11680c91081b1480060b18240d01c6c043c00c44400b4076039950703030580360301403d0f040c1c82125540c031403100920070208100c41d0305a0240c011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 364284883 1250 364283633 364283639
    0x10621020306072c0102070b0415200304030305030a0e0a050f0c1e0904030c08030c03150103050601021002030901021c050a050907080c0607060e0118020a050d030e0d021f08040507 79
    0x20004d245603143c2c07010550f8034070700b500071500761036280c1400c43c1411032090600000d40500f04900820142510700000108442c2030b200280c5860f14206190031305c4c1c517681844001d1201d020050324140d80d8503103009503407900d07408a56000307015121300403582400f40320006410807800003006c07550850040300f0785d000c010141003084040480700d4005407102d01d00d80603100ea6868080002a0b2040c42801c00020401884d190100984c0084904d5440a0740c00801d12803c10b011011010b011a001d00e003d001c2e41c1b6003000001e4480300c2040d8640b141c10b8010010400d042001c1d0143ca411405a8813082c2d0150440351907440034101c1a03070482400c40c64100844c14000020034010155a02030300200044e074002e1091000c41d0b485408142c40403a0b0324542c12060380803c1c000c0d1442c108070b10081065040660041118228444d40094429100103943c13600181d0030001c62034034880110b41600c501c502d24000320f91000d06481620960a0280310341d82e1107030340c1008040740600d0140d403c81d030486403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 364286133 1250 364284883 364284887
    0x6140901060611150406090b04030c020a0f0819080405030d0201020405180402101214040302060702010e03090d17040503250608010b030610090506030a091707030912030201062102030607 82
    0x3c003011007082650800c20428040b103406660150304180306200000d44070065441d040c01c100d40a81e0300310f00044800540400754581840c00002400410340e58414030761038681e03180d90701c1502c0c20074420030b0701c0c00400942c00d0200c850265802081d010702510340d0074058a00c000d000390300902074240f181040281d040b111000074948a0f2140d0790107000758100307404101c8266405400314403481003c903102c0c801000000c40c3e22040e540118820740040c90241000f000107400d54000070f050205c150b2040c0700c3c01c031541e41c500c249140550b41058010b000341c0c4140e170300c225041c4202e8200d43c1d0140308034010340501c1c40c11807075070030f2500249851895419840300c50881d01d9000a00c10810000000d0010450780c0c90001113a001041140c02c1c40e40c5e406694002182140d0003c440350b140f01e55441c4040c07002e2020500702e5110100d0b580507100d00d007030b16036074000d458900e56014460444004803140b90400d0f00035880b80000e02010240001400b14884004089030352000d4101e010303019600115144034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 364287383 1250 364286133 364286147
    0x901060f030b1902070c08010c031b0c0812090a1205270f0a060206060a080118061d010e0d090509070e040f09170301050a0608010b030a020901030207061409010606 72
    0x4990341610324034249151076004585501509034614052003110154203160940f0082102c1032086c20209003080c0307010580741c2121242c1401b8024035080c1841c0d1140d220040c3e490700078a500504121816800342d092100007400784403d8000001106d00c10b2000b4580c000800c00c2910703219103148620828081c80c11692405080c04a10700b210b01940a2181c40c05c0340b11644010031070190841c400c4401041c006200d4008560000001d60000410301507070b81000325800b0054a4140c000f482a22040d089007040c2c28810381004d0840d61355407242c03030490035284021488480941000b444995030805056442c1c9440c00c46140108045200009460506645080c800d481540b070304001507010600384030240c100003104800c07142d6079910003000101c2c40b01420315164600300c025900c3e50304200030701c100b011140e000f80080c4101c1c40300400008501c80e0441343d1040d0b01034005601c031001d581c0181c001e4050b6400003010a1704100720040302d000c1392400c1922800049001f0702140d076681d2401d403008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 364288633 1250 364287383 364287389
    0x90601080706260604090203010f0617240601020f0d050d06060905030d0311250501180215090d0c0b03090d09080a030c0c0e040812070f09032907020f0105090106 71
    0x152442030f0303d010301c401c00e1008081c2e1000018201058070720f016070000e821591844428501c10307568501c140034064412005c1c2c59444401e8009080b2040445111480080007179640900c6000140000d04564800d000504811036040201c88850f04002e40c090700e103406c100c800d01c012914220001845a00c26000001110400707400f0b0030101c2001c2d08214040d240725411841229010441d6450210002d618000c86070300350103072a08258990b00d011800e5070b00500701c204c0f0614060300d402c4056034035060400310307542819406680d2800104080b4040c0a005080901042d00000c000205450814000c52044020f4011740304840502c480987d8036900741e000342d9065034810036045002034000d1480006460040040c02d0030b00b03545100041c1c2030b0f20200d03012901c80340c000c44c66982407003121480c9074000c545400c01903809001500005c054000520001d464041d0300c11040c1000141d40c02040040711000310b440c43c46250a403070296a0358010450158150f1030310000816084061040c82d0903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 364289883 1250 364288633 364288667
    0xb0705190f02070305060a02040501031a03250e0c12060d030905060d0f0903020a0302150411040513061401170a080d0b03070f230103090f0303110d0203090601080706 73
    0x2000404000448101030907011007802c1d44550980400402c10402010f40310703441015025a849080000040c02c5d92840709020740900052010402e031581c02040c081091400104008800d6424176001090303480b9907884072a00304103031418014020745020040055694001c1403040b1612a0340620160a606801c080e0004d50040001d00040c500080189001103032041c0200e00c89440d00322030380c120b078000242203000d41e1003404001c0c07c041d0103211407451041c0103010801c60303141075126400d00d80d07280f4040c0d911603980c1e640041c0b603c003449040b65075602e400c5041000300000403480a0580c1ca420300500844024800110901e41000a0b540300425401880c460a0410b10000d15000d0300961001544c5401031040200c2e00561040210000300243c1914584004105038402c4a409007903881504250400c0d0700d410214003261071808156500d80340010b046402ca202010003809022130301c2213418000000c0c0003400c80005001810703582c444050303514440c1d503a58240c8840d2201d80207450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 364291133 1250 364289883 364289917
    0x140f0a02090a140108101b080615270f04020f0d0b030c0d0605041101030c020c010804062405090901021314060f07080c1e070e10050402030c070b0705 66
    0x4010305201100c070380c1103003450300702140c0411114000d040503403098001d0703a46075000307060001c00840d642c026403603c0c00603074211408040180b6401440250b00800311401031a840c00240400d0f100b0104440355200711400e5082c4c1c007103190b501c6800c030b0800c421a1612640480ca080c8c1624542482100c500fa1500c603480740c45d0039500341000019000303004256515018942114445031150601002d55501c2203a0008291810341760011503009008609410540b810303082d002c40680008041080c000d003400e18034055a101c0c0b9208018201c0c3e030061080c010703811512031814400c808506010f640003100e03401e0f0640e4810000394206e001d980844214003505041c100990f62414224081c2c050010304400c6c9014400081d070322450f03104010442ccc1802002800c1c001c203007000c9c860881009880c180c01010300d0f842c2c122245e075445550141c400030010410210700d51a0303509840e0401004040e0044d034991400340c503e028243c221500030f8031884100e600007042107214101303d40b0360032400007440d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 364292383 1250 364291133 364291153
    0x228090b09040f0e07120b070804030f12110f131e05060c0304050319021e0603150102031c050601081f0b030702010b0a240201090c06030b060f0706050103140f 70
    0x40070f020b0310f400408a859441d4160031106009000fa203026202c2d80890301300c1c0103c40d00d800c0c880c0c40d2008045030200b205076418080008d62100c00e40b09110303054038011150b903140c110758800038440300f0a00c0740000c2d00020318004440748840a40401c5200c5c00740650340c540d035540240807190708021000045401204244154605100a010b0501940044a003043e440d000404d00c2c01c4525600441520099400c1404525110341c4441c8824622140360040389214004a641400003a03d903203000ca40350034000c80380742d10030001e41e4000e541c0400440f525003103080e240303001440207a41c0c06002416000009a41d0383c0c40380400c0749440c04102c540b01485280c41040c0b913440d0000b80c908070441d500d80c2003014142d501e003002400604401940310a403880100d0718542c2d5580c10b401c11006590600c103102c004100d140c40c0d424219143c43c200801d0300d00e01c1c6000107a5501c1044c6440e604004041a0082449800e90003181030724407410111451503c00e8144599600318100403180652245c0f01d0343e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 364293633 1250 364292383 364292389
    0x60b0702060705150a090b1617060103090506010906090e0a0314070606050409051b030c030709090c0503060106030c0912020907030f020c010c05181219020d060228090b09 75
    0x421009000e80c041e1804c40c5880c0300740000c1940244d076000c802c0740c0c40b1043e00c41484000402107400c0710010b0020707000564250303005802e10b2401c01e9180c60820040e00043c19a900a420800d031460344031003990355039170319221144000c10301c500a40b000c445c6043c01302c103001800000d6504070280c050b1110341022900c0c078504105070740601012111651580710006807030b2518000d090800c0d12500c05010101480c0030540c408050b420066842580b003003070503000507280440c1d848250380a00c03c01150b00f00f8a81404000c3c072800358001d80c0c042c4515800050016815800813001240a51790150090b03920300c1c030800e85150240c0d022b0741c40404940031440c4039001e030303200440d500d040000142c206401003002c542124075032050030001c038000050f0b940c40410364070402c21148108952481101440200e40caa45e07201c0c4140e00d1491700d8800e80700c1015035951100d082d829a900080075035543c0104800b080d810716035174820007110381d030420001080c18007900281d420b03a40c4003451142041c0d0580c0c20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 364294883 1250 364293633 364293637
    0x103020607060f0f0203070e030c090105010c060b0d0503070c21080a110721021306030b01031e020333091f0b04090c0303081008030712051204031809060b070206 71
    0xc4030f4401e80d54080040440101c0d0015503c41c420a0b11194039006c1141c00781070510110003090b41c482c1110304014001d60fa042291103030a00d42080002503220404004900c880303001c0400a80340f4403010403080100944401c052040c0c440e4540d10245a9031480c1a1150003d00c0700c800030880501408142c184601c98440344103410240c004030f0720105d546020100e807a61051540d840708140d800c04400950400002c803010990108104025081c03441e00c548010040c1030000801c0101014240b05040c00384a0b4010101500101610203200140500c603029101036189510544008030344030640049aa105034403610a91000c6c00c40740d03002c5200341d14090009054074030100d580d00f10011454455120340c0c040c00c0d10803004450f2043c15030030702a1110100500d0b1203a0012015814000404c012080e940e1250b0f1010b00ca8400c1d070004031064410b0700074400e440105640000812050541c00740105005904801900e100c040e291200c0b40140d51142c050b03005400d20400000e00141080c0c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 364296133 1250 364294883 364294901
    0x6010302160b01180c0503130f0507030c0b0a1106090a1403071a010509102403020403050105040515070f090317040b1204031b0b0f04080408030d091a010302060706 72
    0x1c55444016582d034120140100381c0003802202c02c1e01d0341141901c201c0340f140c1d51100459003441e03419441c0010601c500841ca0346802000201c1100142c81001000c022513405180d003c0840454551200b04c62041c6400c0700900340001030b00446000d4110b080412618010320304000607149400b050b0700d501c1c0442c0681d00d42c0070640d200401c9900c0201d81291004070400c0c4651f0643c0190794907040401c039045001401d5072044100d481d004100380c0c2110f00341c101d0b030303a119480200e440c5100c00005900a0040b40e0000d4402e500f460100b2042120100d10600403c014a066000c9074685c010102c0f288406101e006000c0792890800f0320200c2c1071803802c1c010310800010850300c0c1079250b4608040541090801c5c00c66803105a0500c0105504403018001c0d22402d40101480395006442d0703914010006059000d2124a40300071609200e0600101d6002c1d02c0e0b04c1c4c00303c0740d6600d90f038100c05d0014007101307800351144180e0345084203039591034100240c1200c2d00140410704005e12600c0e90b800600500c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 364297383 1250 364296133 364296157
    0x516060e1f21060305071d0f0703090c1409070306050f06180d23240a0905030a020c0a09060308031b04030507061e020f0d12020915070c0602030f0306010302 69
    0x10603120340351244862442082030b1a4400821120b1071490080e10384100e503003010817425038698140c02540e10445e0f8241d8002d007485170014007502c6142054006200d420310140030300d000014003150344041031a00348640c00040c3c40c00000c9a840b140124100c41c1c40e8003074a64040289030701c010302482e00d100030300a603502018621208602840015020000312181200d8108203048800d0440c105240f0480b1341480070340113400c107800040c1c1c0c2042201075a280c5806109440740c0840c00c0722116610141540342d104046968a045842c0f0195407101c010741c1080c4541c07426180803c0041c2c0302d018400450758425400b030f045484018040387c0b002c4240300540c8440d5030921000000c290104462001850300b81c441f02a0748248600e00c00781b038900038210300e0540d4030081a40603038000c0066621031005661928015804200b98060040d01c5001c1450f5403250078940c0c2c0c2c00307004102c0b100420b0220320800100324419564101643c03280550702d43d40124003001e10001d112035019800401c1c000e00741c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 364298633 1250 364297383 364297397
    0x30b040b0d0b040203100e150c0c06010314010e150c0a050f0703090504050618070f05071a061206070c06020f0702040e0f0105100e040813050d0516060e1f 68
    0x4101003059907940e01c00645401c41088140000e50406109107021908004402c3c450000c061042c1903444011040c07a001c504140400120011800f4007903401002c00c02c0d003900c0380d6503074a04000303d0b03064464101c2c0381a9482c01c80360410362000001c00741d61280c1e04100c040701c1c40c1d40b0010b440c407694000c041c51400707000e400c0180805010495004040c55480798480b4a00e241c00c0c0b6003408121035000705100e000b000305c0c5132414034412122807a1a0700c00707000e1915802e51416054116400d004030b01c0c005182c01d014103078282c074524141c64101c2c0b0821081d2181200a280a03145507a40d03402078840c0404500340c100040041400c0360028500c26a4026040e8601807180c1e010078200d585070205101c003a00101c00c00500c564003802065004501100894402401d000240100ba00040c3c00100b403001d0000350051b038407945544a600403e40100071903040d032640d05144d0340b0342090044002c00782c007400343c0205140b40144004402e500b4003602c900c1e0900c0880310741074103051406071900c051001c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 364299883 1250 364298633 364298651
    0x40f0b0f0f0c0f07090501080303060f010327021c0b01171608010207200109180f05040f050105282a0512060303040b07030f0309080a08010602100b0a06030b04 70
    0x181e000034491560980010300118101c42002c40c03d01010b134104100d01030501c00100102e07907000040c1c0b50031540c1107a101360416401401030303000f02425800c2e01080030701ca070441108000c4103192000302e9802510076100d0300f41700c5490240310410a0130020909441440180542a40034040c1c0c207203402c540f4111004918100c41c1031102010540c03101e034140c3e400089070005c1000c002a450301b0320300c022295078140003c01c40003030207280c0240036407000d031804180180e01c40d030a5600710202e002181c05c801c101500301410404020308030107805483d99820140416004500284c1905001a0b0b200710000310541800300300c00900380741108202d030401d030068190320f8200491761040320412a61111a40c3d804001c100220102e0020320940c0701e0b82003804100114101002214a243d034149404000b80800001c254000c01c0b83e0080034001c0c09000c01c0209000350000c400505982c00ca4003111101c191258400c001d40d20b0194403250000380240b000c001c402c0c080e42054160030401070000c00e861071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 364301133 1250 364299883 364299907
    0x3040b04030c060e0d0203060a0b1801080604054c05010e09120909040201030b060d0504030323041101080901110d090303140c040b070c120303060f0605040f0b0f 71
    0x150401c2e80c25040404080003030a070403500b102401c0744192070300c0042d0340c07050300020780359040104603112003034940303000760500c0e542c041600c1c0b003c90400f08901520358403146505d940c0d000c00c840c00ca41611480540d43c042c0314411119004840d4850350b100c0501c60390b00d0545240b41e0316400550300b112a4190400320f110b0b1103000b0b081c00307003249040d000380502e400d0f180107141070f041c0040c0c02d40704c00d4104517100c039136180c154409600a40a0a011035000d00034000308100780b2030031075901412468042840105a031541101c1d01d00100e801e0100c82c040012a1b06a400e01c000791002000410000c004807110b501903201d60f039100d0180000084c100200301c48418090740120028181039545030240c40030107030544107d524242d04203645942c1440c101074103206511441c05080303070715040841d1900401c111039440c20090300350402400081c5c000c51402402410560185030762304041d800b408030b6018400c10031348040b0755261106082d8a840c001e40020a640701003a00e0b260b4040800140350300312 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 364302383 1250 364301133 364301137
    0x311181303081602060109020703230a20101515050d050106020304060f1b0609151b0e1e100206070e0301020a0c0b060d1506080105090c180903040b 65
    0x81110000e810110280e8075008060b00001040b0101c2c403d502e0641c1a200c5900080d4181500d205980c0141d889002d810203954100c000b545007110001400c1440441300407030000b40494120700e45495042c600e605c82200c9441c41480d84140d1543d2000054100c092026000344c3d1841d61a00ca451580355112151800f5000c032624541c800301e9400a51100341703400f14429a4018001c40c8041c50500f42090401021442d22401d44003c1204c08500400c81c21071034200c0900c25640202c0401a120440ca8000380c0d0492903001c1510301e616286a0070050350021181d000114025911440c0a810b0017042000a608260300e4542e01168a0958411900c1d0410103030002011600141043d141c113220090660381d544948902903401404600302c520b4014402d114000d40c0003401d10810350310f070008100a03450f030782d00c003510422007403c010b66894541d510441c00e541e6450000e02c85644e07080441c0755034001119445410041402e410921810200d0903e40c0041000007560724040d9560f95001c20b51b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 364303633 1250 364302383 364302391
    0x908071e1b0303021203010819050f0d1e0908120c070801020c01090b09120a0f1710060e06030c0702090709090f0c0e18010e060103380910031118 64
    0x240300d14807001e20600d0b40401060380220681c080b000c0ca10360610307120320f44503040900340d080038140400120003001003e0154903402c000c018110f540a9215210050114070204070120125110303410200d640d51203481d0280c10380f501c0100820845e12180a500300660010740690b03100c0c081c508000c00d610740c00307000402d20398510400101d10446681009a0103100140c0000c42c55481036070100f10040c0c502040d514445241c0c10034000760741c0740110950315052404103d8040000680c100001207400403100400d0700ca40c0d60b5501c80406212080c850b143c8801c1c1d600c03641001d0280a10001843c100940342e41c81440c07858050b1280303039501d0068041d03a5010804c0706180380c840c400400c15940c4000e0100384a2030440e0001071004142040c249400e8041c055103c01c40c58030b400050b8640d009400207a00000503410380e02e10700003402d007200241c90340c2d82c41515903c0c107040c00066141c03400c80841070095504800c5142c2c0940355940e1001c41110103020641c1101100103040c400294a10300c281c45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 364304883 1250 364303633 364303673
    0x60f0c13031211030711040f231803040501201510051306050d02090402150a09030b06060f120901090c0b0a08010e13020d0c05220507030908071e 64
    0x300105954014080f0510a03a456400303500c280029404110852110800c500d4140c1c0d00045141d04504440040c00d25484480500d4444074071604500c410000b9580c40b5011100b4045145030240340d54540301d2049104071400500300b59144420010b82e0080c292881510504032420541240b0412145180440c0d0140120301c500f80c04100909091004d42c07000b42d2103a030104002410f10001410b000681d080280c0166082c00000c0d00b19101c401900d494520f460620035261800314500804142c00c6000c01c1750307440d0911000c00c410f400c029054600c6407600110302c17420000d203010103da2144000f4100c10041d03417144560404241140d0103e0090440201015910211004090205074042c1d1104105040f82ca0070041020070720f0325a40310003581215890624000c60420b1262070340d032508800c0d8010316082d0000d8032143d01c500c00210601050100384a541c0c2c0e8440241d044448941000e07181820800c0480000f40b01c4800e65540142400e81001c04600d46072500704c03080c58103092070b0203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 364306133 1250 364304883 364304903
    0x311061513240602070b03070f030b0d05031b010f0507091205070e150f0307031104020d1b0f09080307150b040f0609020904060e060d06050402060c030d0504020a090c02060f0c1303 79
    0x842e9410b025010203094146c00c0540b4600700000c1c0200055402c6d2100010143c0d5908900419600c603003c2c0480c0c990030070100ca445420440c40c0003001003451070300035003d610742054414410124003c0c140f0416040d01c9130702d105441d00000c5182039000c020200d07900d000e01078000c18052881107500d07000e4144610314040020480040c00130a6541c1c083d110321940c014081040020000101d42290071300503500581c49616104d49480648032001081441100030750b07407000500d074801c40003144103583e43d450500e090340c2c0d080601e4892284c9403000d4440040d4a8481c0a506201d41003d80c02c0c0da406080018a04114118042210101d411502d000340d0001140c41141c5018020700d40907143c41024030400c1c3c1000b1000451401c1000d10040c8030986600000d815591601c007522201c02c0e160341034a55480708526a10028101100d040b0300c141d118030008a90850f642c8100c690b040310781d40003801c807a185c0304c06003250800010003840d0744071420081c08041820710302c4680300031841602000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 364307383 1250 364306133 364306139
    0x70206060a0902180f01030b0913020f09090c010f0e100804030801080c0d140c0603090a0213020c101e021b100213121e0807031106151324 61
    0x108040555a20210b03110740184190b0035169140301108100c402c00300c841e014030032400401038001d44aa1003049500075408402c020700e004580307c0c510096403088032400c50042e00304081082d1010140d0b02000e1581c072642d00a00154018401d54078161000d0926444034204500007403a003031040d032a0200010170a50600041603086110070303003d4914071014101900b003004c08241c448042040c09001e21009061113201c00c48280408040f03044007174190340d524600203882907920055030714201c0c000c40000d208405074150f1482a6011400180c0203880d80c14030b90320201d0050000e140409030617096044041540307440920007401c984060801d05456080d401c80c506003410020000b460f400341c01002950504029000c20005555800c40d80c1c0203503481c82d080001c254000f1204001c00281e0600c105400d00080d000500b42041c0700c0c1d5114034107940d07605078040d00e2398000d90340d00c6580e5061240403480c500e480010502c40b1380320580001460000e0301c0c50403601361003041c58864405050300c828 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 364308633 1250 364307383 364307389
    0xb0c010b0a080c2b0b190603080403030f0c03080133030f1d030406050a0207080a2f1f0e091305240a09020d020a080102130801060f0b1c0507020606 65
    0x80072210158400f910f0490503004e140d0035003491110b001403a60b02e140d030000c0c2080d05100c0494034440a01d5a0420065840746000045d07540103010a5010504901c0c94502c120300c5a6121078a150741a1307a100d109918020882107482d181c0c000003090000401141403a1200740d41c4500d180019079503001c252601c00308514001c85200c0c60407078070b10000c0b41c001f01255203c00800c9804540080ca4402d503540d0423030304124245060340d0007810715401403a03201c1080c00040504810410300d44400000c03032000c0c0d011241c104025140c01d0b66004550321030200d41d03188581058414810060031300181d2003031b82c0c5000542d0040112115400d2101c055a078406214040000305199000b100d01c04440b0400720602040010000340440d41c0240c03603540380e40441d2603d8011813201580507000701c08180e00c80c90424080d400c204064460b08804041c0081c4030362050003000100d4034990f0400d0204c0b400d001000301d0304c5d0b0001361050340000c1c44d02041c50210006105141c481d030303066400341c503040c1414010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 364309883 1250 364308633 364308649
    0x6040b0109150c0203070b0d0f050c0a020d050c150115030c02030c03030f0c1c0c020609070b040308090a21120e100f030f06060203030406060e010b040b0c010b0a080c 73
    0x402030401980032400c0c048040c546910307003294152828007000c60740b840c0c4002480d201894102e000c00c900e000c14502c400d50880c2e00101102000500140001d43d80ca59520f00311740a0341c070781d110041c6c4c0400080511517000c0ca000302542661001904c10f41c1c1000307064174048080c2030340801559881c5901074048242c4c5446000401c103000e201071850701906090040d964000070b091140758100c40004110a080fa060444240d48a0490080c0e00c130b02600d56150020198801c4480150181d0b0000901ca141b000c110b107030a4400e8486c046040c02c0c1580c84841c8183c1204030080c0e00b03c0c900c40d00105d17803a24001004900011021700c1141c01481a2401080c0240c0507040a018271104440361007060781c03032403001a07600d5400c1c6060354410704c01c01d8048000c0c02c5440d4580d8580d51a059006c00e1041e808030095110b180610011f100c0565100780c04401c04000f40f10b442d0750510140401d00810420600616843c980b0000108140c2030360400924412480c0c1d0003903040b030303001440a803228240035003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 364311133 1250 364309883 364309901
    0x3071115070c030b070201320711030403080d0f14040302010b0117010b0a141b0705101403090102120c0322020a090e01060305162d03030f050c01090b0604 68
    0x44014281078056541681030b034000c1c040100402d034a980003416082c0b0035800803108000c2e1200001482c40500800642c1c5e2504070f12031404a4449000622a540070703121500131030000c140114039061460b2a00e9031140c01461408102d2500c424602c00c80d4800350050040f2140314059003203103420f1602d00607085508088030385051080b0307240c000c0311400c03683c030030f8504440c41600204e0780c803a42d01104030340d030841e01c0c8511348a408003c00c48904138421001d0b0503524405e03401c1290f180302d46440400280c0240c41910380300003400450350285001501000d99000003000002604180040c03842401d400c408440511041070301004002d411403080c40c20030f40d000303040f04c0e182514444a40108030294824018182000d44410750300e11440025884070004540040948000c1c0000c5011022082c2c0d0341c2c07050f60740500110010301454502c0051000d03078042601c40c0440c410b46155020703110690400b0058051203410301c10395410781401e00815441c2881005030024520b000010407040b200030320 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 364312383 1250 364311133 364311169
    0x20d05160618060507060507020a060603051c1107060c0317010602150a23060f0901080106080138060708190908190809040b12010902130903020a02130b03030711 71
    0x40e0801085800c681205d00d09600000042003941d5110400da15042c0782500040c5150301d0175000100b13208000c01c504007101e5081c00d402010841031801120f191200003281c8849401150f070400c802e0b401000424001440303820802d95201140390a0952a4826844070700540c100a004030b10380981e9181166000c02e504004100009641d0202d8a004e00f5021078210440c0b00b00002c198943c3e21954000100d072002010402c856840c2d070b48990190103140300d4401c00b0740c2008070054210f00c0b041040c688001d41461080d211280e4081c0c817000b000d008610b0a0341288040020720003040c6107400500f55112001842075407002c00d454010305105003980308821070340220b02c1c1302001c55400b00c030780100c035a0090340140e11005040d0020780208090003083c2d600001c2609240503036071040d00000036090080b6079103403080c07a41e903000d03200313a44001c85c004005030040303d440030051815000110b13001c20100000100d1342c490034040303491580f20000694200801c10b1109940d482c0074000040104200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 364313633 1250 364312383 364312427
    0x201060b0a0507170409020c16050d150c050f0705010e1015090911030304080d0905041b0c0606030c140a230607060b0904030905030606100e0607020d051606 69
    0x40c2000b0014001c0500052441e424400000c07080c48221302641d02405400c0c0d4110340c0d41540d0501c05640d0041030384020914003500b0f40008030392400c00308605909820400c2500101e00c401c4544008080c0000e0a00600c0401d2003c007103600c06c0000030b0405948a080001059103400c4e90342c6181c4400034540410040c20a220781c00c400344400008002c40c6c9010b400801d001c0f003585000d0b6078ae6980180d13030541503c0b000c50002211900014000d000031925250094415182e50500040c0c3c0e81c8820369684486404a5540115200e600c2030380e00540a4440000c0d125104d40e03c4041c018000e51050054000502401c4038030f24107a5074100040c0592254440f1401425214100c51501d05a55034898500403402d10180700c3c8a800c00d50513a20b00811903000e514040c900507100226601465000f4401c031000078030b2604101b1514003000009031102258950460100841c5a001d441d04a800000081c11400020000c206140c400d20310790009503101c0341800c0c0001e00c640c0501308402035880070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 364314883 1250 364313633 364313647
    0xc0f1a0114090411010c020303070807050327010509130b090c0309010f14150a09020a050403030e0108070918060503150a050907060804060f02090d0c0e1302060301091805030a0f0201060b 82
    0xd1030f44d00c0503040000c0c2003480341c0d4000e078000a42180611070000d803200743d001408100300b100110041480c0c148284014024503031107002e00c4036411501000ca80800e508210300501031a0454445042d440842c0000c200e01c0001004202100720035120203660742c101000b803000e071001c00e00130700c0f00100049900b04881003803010f1050480700b02070039500b414142031109800a0f210100c043c00604144c49040d581e414049900500a80c400d110640c00940340b9502400301c1e6105023a807500440175680d9180442d41450620b104140c00996040b0304160788650003d20f40d10b0500002422056048032041c1c01d2521005020584000921410302ca402c24102800f4498010303020a80140d00a280003400050b01c5280c0c100921030924959840410550668100704101040400780c9000c103a007001c081d1201c1e448681c2414200f00c000b54402b00034030040c41005070a40c40701d9801c0602204210750300086d511075608550041030814001603185030000312341502402644000c041c0015014501b1030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 364316133 1250 364314883 364314893
    0x1222060c0e010e090c03041e030f12020708180a051003020702040b0901030f060216020405040b18010608070506090307090207031206051e09270d0206090610060c0f1a01140904 77
    0x94001c4c03405c680303002c01101080910565640c80c0c0080c5000b10030144080300c107400e0140000001c9902000012960b1a9151140202c1d00941d07200740c1d0300c0780a603414910104000c645e101030180b070454110507041c44c005403680d10007460003118085510700503a034100c90b00500c019109041c48042c0911303041001000001d07000c1140d541c04c290400c0d80142c403992680a00c0304a6540d4a4001e94020b041000380014032041c0c4014600410074014020700292021448901380c560324403ca40154014880802c494104000100446400141910300139500c07100c2100498000007030607070011743c94051280003010309105220242c4021124210f201c41e01d4030090f05406189002c1d14094046c48011500280203880c913a0350a040c014004020011006103503a9900c3c0240702d14001403040d040070410b40503010a0a9019003000c090200c2c060b400e00209640f025010041214182c038040318120100d000d20034003d000c3c00116104075859450203041154001d000341416114211420602001503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 364317383 1250 364316133 364316149
    0x241505030c061e0403050304180f06030b011203050f0316020d030e03030106030e0a060f1506030506060406030e03121005011d091506072108010b0705031222060c0e010e 74
    0x1070f10004180000e4030324512a038a1402903900c0100345200200d0040b8110b42d0701c0000503180f059603442080142d491030841401d6490701d10019040e000785000600c07440c000d0000d0a481c031030203405d0035071510b080b041c01210a54811510400580c0c09452080c500325818003094079a6061490706101106100d09000c4d101e110610800051554550381c0440b525000d00400040e140c000c04100050124140100081e180040f1007580030050b069000c5106070103403041a00030711029014a0502d418006d069001780540d5400d01040c2c8802d100c04c0e20750000c201c2c885403040401e8540a51403030b28180000d0240c20311641c1d000320f84c419200c3d0740605c503122010855481209510702c9804c0725a0540801c3c928031a041c00030700320824042500464118800007013140c0410b6584090490381d039510b0404040c020400002c3c0309800400101140140441f00c19404c011420181400003039480b0320503a01c002c030144121009a10f900091101540061400302d400c5000c5c20600050b6032910001408030f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 364318633 1250 364317383 364317397
    0x20f0417150f01050f1c030c0c090608030d0e070e100602072102130b0607030302090306010f1802030a0b060307030906060b0429090405010f0311060702010507030c241505030c06 78
    0x814118200ca041c0b036603441e120101a84854040261406c001e0500404d12003110005a46209950f03078002504a818030a5a007140c2655001c0c40c00c3c41b80c909580390241540e0104002e41c0d10612034007040d4140e158030264001d5145030300e000200d904c1c1920203803c0034201d81c40800c0400420f4040d1080d020343c2684400e80b0740e41200c08182a4605210582c010301030440301076000100403401004140e00b69004011a810417001c840150380c1c0c0b01d480409180c0f00c1e016000803840941031226540d1f00c19009160460321800c0c0226603d001480804c03240e8000321002e000080d10707840340605200742e6100d01c00c090804810142d01c2c0c242400000e0b104140300100c0d5211030825035011520402d100c609407008194024010302c4a96540c150100d1180780c0d5001c1030310440c1404851508500c0c001c41242c40d20740d81a100d039420200d580d1015124041c503032000740d5111180f070406860016000140d0203041101c1d100009041262100c41450a01c050f08400c0c0a13a120801c3d081441e0f803100c09a4000e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 364319883 1250 364318633 364318639
    0xf0a05010c060f0606110106080d0e01050c1002120402190b09010f0203040b070302010204030b012c06030309030a050d1103090a030813180504031419030f020f0417150f0105 76
    0x54152503280140041078080d1144580504e0018042400381d446203042207500c003241d000f8841d6948840c415602c0b091a83d04110100302410701403041d650086001d45640c081c001d042c1c6645108140680c02640d00503049900d900d80e10364100700451914000c189000b40c410b0010074220b42c104000448070740700340c6121034180544200201c205c3c80c800c004035005042c0c03100c1c101c1c0d1104954580a4040c0d0824081103070502d008000111f9441e2207041038103ca02e151407064101c03d00064800383d10800c0c09032080c1c1d014041003000040944082001e105c000b40304400410803080070309401045c108800140701d401d60010081540f29540e2210410140e9130400c1256580d80407003103c1c3c440c128a2540003026a540a2141ea80c038601280c2c09648030b14000d45a141c076100c12003403102e00901c503040040b20050b4041c031038a00b5145c42544846504100c0b610018a040d40401c1b0210850300280e0bc414a5440f5010f15220046001d002600303022251180340003d50a10090550b032511b014040c00d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 364321133 1250 364319883 364319897
    0x70c020114041e0603060611100216051516050f1209070509070507030207090209180901060911091311041202011b051605030309030705010507080408060f0a05060f0a0501 75
    0x252484a80307040701c0080c40c00c5031003240c918844040c00e00700180303d03104800102c0d00d800f03400126a03000d944250991800c50024000c13405100c01b5030002500aa4980b044c0700c0808a8040000354080000e1810040a444e030020a4038110400b07080003120707505500104001402081008075031141a00c2402c20380794030300c00380d903900c2740103191070140360780c0c00160301c0070b0001d0500042503001002084002e002e5805d84880030b85403031601c01a84120101c0325080b05c1e00031b0000c2141515100766030f41113060f140c00400c000e0b0755010341c0800d13103508409000d0308050006205001d4030f00441d1400c0401c0550106024600761081454100d015510a082c0300c840d07003a40007411680f1410040303880513150034100403240464113089589240c00000c080c40990703c214042140d1400009441070300710014010507a05003044011071307054011180803210040700744800b2843d04400d20500d0b216450220b0052480e24140035840280c507c080c04150152030f410b5280c0029850701c40340c0340150b070000c0c00c0c842 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 364322383 1250 364321133 364321157
    0xf0b0303070212161728060507110123150108060603040c05030109080306091506041415120603060109020408030d0902060c0105040c080f011a0d030c05011503031205070c0201 77
    0x260600150304428108000d8441000c108050717626034404c4241c0030f0104646100748180c800c222010310019941e03c8110100c04a18000f49050304030650041092500300c910110512025081d20700c100d641503210140207050b120711030021541c0030340c0034044100301780310280d00c0130002c0d040300d8002e0041805500000300103020300c0185203009004102c017800030080f031403450500c0584d540040e180d842c468040040801d030251628002440c5800e07005007214a0280381a2000c860707503011981c0d00b0780050000c84545002000c1c10060000341c09540b00c0002c403840c08400f01030510780705810017080700d44144014041501e0010548019000d20303940011450a14000107100d40100c062507403180d801d28080100b00319200084008840d403c004446518114801582c00d80d02ea050745c8091000b41c100301c4100c02c1c9000c0c2d54001016019040c0825819807940b2100c3c00d40e4080071005003a00c005182c20020540c2c040309998141018600420813420009002042c2c00c0c1c9100c0081d04100381040e0308 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 364323633 1250 364322383 364322419
    0xf010b0607023304050907030516081f090e010506030601080a0b13150f05090a0201080a1a03030d051b0403050606010804021f090510030203090d08100e0c0d0f0b03030702 75
    0xc0080c1c4044484540003201e00f480034002d560140c00340341e008004d0390000c0b504240c002e00595000e071131610b1071440f400d0085802143c4614006283c41c104440c1d50704080310304518021000090a148500031495401c120080c900359800500024040e90208004125507000420800300e0719610041c0405541ca4400086030b00884048002e80030b00320500380c0200d1130350a50300284650100c0036081c07050790344407841c2a480f2428040d01a01081e1144000307201288143c0c0321140c061500030b08886007a4015020900d503070446610b0b891074554550500510350300324024071140d050340740000c40c6071a046645043d00c860010b000c0c94140210280031404540d1100c000703005244800241c202103841403800201209600e01c141405010090800410f1a1103402103074030401025000300303458220f1070011680c0340001441510000007141012800c41e03801d010f0300e03010f0003d000300ea98480050007600e408903035844d800d542c090341c076101c2c1e54140d81e28040140c50385a9012075616491800c90010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 364324883 1250 364323633 364323679
    0x1c0203121f060e0307090b060d020309010f020c1b0d030c08090409080f070b15060304140a0f1a07080907061202040503060a060f0b040807090e01091b080f010b060702 73
    0x40e4140e0081c1294000c901907a0266607044452011801c884050399200520000c45400c030410700d400c00402c120350f4041000d150011504030304d48000015106d80b06c4140074049130040b20010181d500302ea807215072280c0b18480c5010300c00b80c0451f0b40000348a0b040d80c000c0c007081e50b4444010204840410320400e00d80d00c6a029148135a0001200ca59441494904002c603501000c1304844420b414000300c1d100c68140b0751049072000000d0311503840c58456440c8e10140d800d201510340040c2c8036050034400003c5c044205a0003080c890001d031000300d65240e0002c048001c0003002d03681048007034420840c9030440005e080c021660f56003000f1a902500b0301442c0040e01c500d030001c83c2c15115007030506c0401441640101c0c1200c00030241c0c58041a154895241036100381c1c800d0382c60341c0e88202021b0011002c10303400800c01107031070000003c0f200340e50754481c11a9050001d51100f01c4003d050100004c08043c00103040c0c1810441c002c20040d900749000030900e001c0d601002c3c0c010200040949801e12211b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 364326133 1250 364324883 364324921
    0x1109090d020a02040b03191209060509330409090c060305070c060b0607080f0c01050105060a051801051b07150c03021f0e0322090519050c0f07141c020312 68
    0x140800d200b0159080009001023074002c4000000e000100010b4043e200b50b06554441200400100400c1a500510b10340301505800f44000e18461044104140e50424010401030501501c0440e0343c440c06e0070901c910586a82c0320f8401c0c9801c01d010044c289900049040f945980400002080106840451840e0240c64001030200300c0024a6000220340300d00a007802c1403602d4004d203c16a01d80e01407080313602070501d4450110b8414880003840098070b0003007407a0000107240c0641000012035002c96800600c43c129001608429828081002258038005090046040100302c0076010356009542c2c4442c490010703c0c005010202e072200030f011390449950301e00c82c0421240c9431201c04143c0f4003d8840141d000101510785000010594294011188034200c1044420300d4845181801005800010b040c000c084c08204800c02d181da40c0c58024011a6002e14140d0601d44664580545000c0070440781c0801d48110650501d41581d0001c215880704203c0548940c80c0d844030b000301010b80a902c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 364327383 1250 364326133 364326163
    0x301060b03270f0f010b030c0f01021506040207080414090a050105030a03050f09182d0c0d200703030f0515120715080601120c0f1107121109090d020a02040b03 70
    0x402e120ba0321015000408451000c9092300c0040910b102048540100280d0382400b5810000480032500514603035280e11900240c009031500103e640c40f151554480e03080b250a1340010501001541412031000364000341d044400c000950402c40043c2e50b541408000800300900024620008143c6105403610302502030500092202e07210020201d2050842e10880211410052169000e2002c070311410010f401c1600008180c88000d00301080c1da1010b01c0011401d900c94120113000c07101071030f003907031070311507910300720341c03900c1203454004c1c159560700708100c5880d410207080c8001014403003900000c6210880d145512011290542400c1030b25a601056018200782c042003060360300420403a106240903a40c070785000c00c82c008464202c884066100c400952940f0f4a40d003403500a6000e0000c02e200c44007143c1d2038507542d980b1213892054680c0d040728000c541c02c841040307505120010980254502014100c0341c000c40400950b58550320b640644506d40725940d40c0301c03607203040c048485403103c44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 364328633 1250 364327383 364327393
    0x204050103050f0d021b09042f010e0103060b090405060d0b01150f020d0206040314040b0c0706390f0b1e060102010b061b15010f050301060b03270f 65
    0x90408540312040c0107200f09403409100c40d03041c06240f02090500107039040c100b0b41030340c036001541404101c400007001100c1801790f05007500039151030204140c90580c0c00d000c20001074016030b000140781c1142c084106051500741321051004041510036204e002c07800f51400202c60b65100f000030321010b14032901401c40c3c1e14007800440c20482c4506010441403940d1a480000001103e080b86d0303400768540c51f800160007001c01701c2e0000348500c103d0008001d09100c22400e080e201d043c0d44545600030090301106070b000d01c90400007650012445480325400e01c49104002c032081210001100c010042041d024141004610421031f42518010829800c000c100c2c0441ca400703042049040407000044800c1098280061203541c8140182681150003420060501c07030380c0c4140c01e41001c42010f040701180a0741411040c8884000321250003042901443e14013540ba11041c503007140c2c2a5007090b200d2820400812500c407003d440c403004825016000b005044154007061400c2443c1100340074100d0080d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 364329883 1250 364328633 364328639
    0xf031419150b01080f13111201064106040e09011a040b0a0b03040f0501140a05070f0806010e010e280803070b0613060e01030b0a0b031204140d02040501 67
    0x2400c641d114084009100c00c20003005100015100d00d08100c5a001c0c0c054203401c00240785624100c1e50700b80d4544200980c0d01003000740f2001030490700d4000240756150395100800c100341c1601e003444058031404900c24010f164001110716110395030481d11041d038400c0d20025030285403900c0c2c0c01c603401098414514a203034200215a64040c01c4010b10094482010380120840340c80c2c24810f012085200034801c110b05440c000654405802c0144151a50301241c0400000309800380164903220220200741e00039441c0c80b400c3c00044a0303015040c0800c100b100001d010566803c000c4c40c50f040002400c00301884060900122401207200e10101d0304400602c0041050700c01a2200c881d4008001034141c100030b1301c40c100150b4901400201814461003500841e02900b426603a5100048520303c001c105580c8407018210b101000781c0c4110380000341e12040144d5040d03107200b200701d00c003011805441041d401e40e120000c4c80c0203a0040c1d2142c00904c1180c0001960380a044401c19039019005010329a5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 364331133 1250 364329883 364329893
    0x2601030c08160b180105090901030b01031707020109050f0d060c03020301140405150d02210615220507110a0f02150f041202060c03120a060602070f031419 68
    0x205031281c0402407150801080a01c1074410300c150036035220b140c61a00700030306103c010b512441d92240850600070200f04d455826150089500d020710300420b4509229450b6150040d52001c00040025031400140704d07650040c0c0c1d00c402e8501c11a42e01b214818001c400c144d0014602c02520400140b83c18580420081955010340181d8100c4200541801c50f02c1751450034882600c504958840c601a07803481483d07070a00c3d01d0020790034101d0000d440750110340a0300c2c441c08400081c000e003001440e40b1010400c94502d40e00e035214070a51390161203021a0000f000302d00381008800b0444030341540e41314130008004d60321900c03d40150b091081c007101d02280042c04c1c99118034001d21001d900540c03840c80c01c1d09949113040c0895840d100c0302a0701030300c1c040c5007a00210042810481c120303072081e8100f0540390780170010400342c41443c03048808401035052409150080714665403144055412500003001040d41c00e07071464003101e4010040740e480c1320a1b003030510b0a08165100199000c000b104a10381400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 364332383 1250 364331133 364331153
    0x50d110c0a02190e19090b090709110a120c030e0a030809070b0c0604032303010e0604050f0c090d02190e070f02011a0d061d0102071e080a260103 64
    0x14003c3d9000c500c10000c90a1441070400240200c030112502e05000c101450b01d00c040b4a03400b014185c40001d40110301d550703200252442038800160b00e0b0b1200d801400460003501c510300394004240c1201d403034445007501c040d180a80f5118076a050a6443c440184c1484c040c0c0c00c01c200c4000e488040d24280001417501405102007a80c443c1002e00c00d014020520303807003540441e680740c9826001807155a440340e50442d0101ea18015400c603210074a03000d14500400000914041c08942090710000d1034084180030403680020b00c501c0501501000348401009004d0407502559000d5a08820503030190012800700c44050442c105540282080000d081e116071151900031440caa0300c181ca600c0131454109c1c00d81d4650174100b8440080d542c2d2068035481d00010140d040c0d0310a2101051040c24080700da0030429050011a1150350002074001c100503860154a4100704429a106502442500c94000e6402044842c20602c4400c14064a074030032140800d02060403444c0340c030003c41da140c4c50584452 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 364333633 1250 364332383 364332403
    0xa0e010c0921080d0f0e030a1b0804150305010302030c030c0a12020409140c1f021c031e02090a06020a1106070507170c0901050d1713090608030a080117060106050d110c 74
    0xc5c602c1d10080070000e5201008a8410030310030f03a0f548030f40d10341c1003890700181003650408a41e6070300104800980b401644d000ca036050100d6440000b83c039807441c0145800c3ca42080a041d00c02e03040800080866900c40c3c4000d001d8175001c0400d10721803040e920100c0c0003408009070181940d0f006440f209110340001440c0d8070040320030350b050404040095008041c2c0c0c00c00e10074000258008040c1140020b0000c8501205c0b5903180c0350214002088811240e0842c6080320280c100b5600000c0d841c5040c00e0006115006120398070082c44e950708a500ca000707a0421028000c1e104041c002221402d104e4104404000780009501d440261014251103d03034802c2503000540c010004070000280c01e06d489800c22128a4022140000c0c0b1a0307002c13039181144d408400d005012250107107010800b6019440303210080c240b01c40045540e007002c01d41c0600740303280c141e001100004030031004c02c00c040c3c004035005044500c2401c1064032041001c08100c00f516100b803100034000030115002d00b600c040050300200d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 364334883 1250 364333633 364333661
    0x7030f06080105240307030b061e10090603061403060103060e1213090c0503060f012a0813140604030b0603070506070b0601031a0102150402030f0102030f0a0e010c0921080d 76
    0x4140004d00a050f1103200381e00c805001c3d1080d540004945081c6010395880040107089a0043c00d11220700048041e03110320407c100251a080c400e2142c240c0611508015000718101c0840d26203100000079605c52050000402c13041d100c03001001040004c1080c005140400c228003501c50280da1109000c4450034482d03844018200305c1004044c60152048901031b2001505271a03040805e9030054842c4415410741480c81c2100840e00ca4001d2410106407070024421458903550f42c140c1010b2071180d24907a040b88034a00b241d525001c07003a640d0325040f107044076409140c0e0101c03a583d000c0080d080000740d40c0003070381040c40090b00c60100403039082d40c0c03032084609881c00c010703841c00c80710000e5101283c21041c1e0b0150b80035440d02c4003002e4003034801c07a500c240f00504440b11114504e4043e801da800944003010720400803004d02c2210030340c3c0d020b40c00030240d44000030404288035020003042c14842c1e00c40c260440d40c1e22104d09401e035505001480c0c1e455003002c011540c03503030800401002442c0782d000000d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 364336133 1250 364334883 364334941
    0xc0304080d090b090a29040b0d051b03040b191805010e01050411130f09080a02120c12030702030c070e011406030108100e1c0201050117030a0807030f06080105 70
    0x50b083c80e28070554039401005006882040e003810f0645c2da500302ca5000104640c0c5c05038201c650b081c051000200060411078446d5522800d07004003600c01d80c0d101524407402e005014001d0744081d403511080e40e500a0700311054807201d03240c1c5100d0109208800200801450510106861000021220700c42c400d110b040200b10682800c41d5840c200c40b01514000c14116014402400e1407a003c1c0f000003180c0c441501c00104a89016442c03000c460303640318220b0b1030142c0401c001d50f0294040c807a900d51a40c140300450302e01300f9a62541e644481c8909501501d0043c08008201441d20810946041014410448020725120360140003000c1c3c0c00d100e40419181201c00034034840c01e046c4241c078100c0b0390180082008001c8910b14001070080c51a10201a00c28602d0402c560030140c00200400c00c0c05800024055062248580740030a0b141c1040b4840d80c01004034a240f1136101540a07403040c441d01c0c0008003401507428030406003c0c0d5a00c80100c540c01c0c40140503c035140e003c0115250380c19002941 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 364337383 1250 364336133 364336139
    0x1c0309061103031015030e07031a0903070b04030507320609070605040911090a03150506010c03122007050309030d020a030c08034803150d05030c0304080d09 69
    0x40e589200441e44d00c0055050f50310200714200c0c11802c000001d00c0b0505002c2581019441514500300e016401501c0075001002e03603601c1d0484825549070413032400806035140c01c1c01c5482e610080e0034003403c000c0030484001415024403910418039078684001070a813000e00240300605215031b810b00c50804401c1e00441010419a00700044c00204550717140d100c0314280b80c90200f8090017084850200c04048804000900c880da4880c0f00b102d001d50302c207200c851040d1880004100c2119401007040d81844258940079020942100c8403048003800705a020580e2900c1c0104030880c2d00701040d00082c03104004c50307190200700022000e1301c0781710025021525819410780c1d01700daa82802d50000307408512420302c0500400d0100c001035510480340000b001321003040b250035120480c440020448409a040c50f01c0d003c000e44846400b02d41c003100f840490660402c489600304c90404c60100f03500c5a58061400410058248143c408603110b0500b13a0b070306c590b5944e401c291500545181480001c2030b0070404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 364338633 1250 364337383 364337417
    0x100203010816270f0609090309030302070f051503040201020a060c11060606090a1a04031208161e1b0b07031b031b0806011206081011040302090601030b1c030906 71
    0x5601c0b40c0741c20b4041c0d02c0036143c80782048020804500e05410080e00c03504046244840c0d4007660341414403c0d030f951038485255050007414142941c00c24002072032030f102c2c10070607913803000311000c0c078100c007243c2650742c1e5192032005038640b4035900001000c0d1420810030a030b0391170300140981c0700a107139201607076910741e504010890140b29600c0315540c011101c0f08103004613402e90030801e4000581c04d01c01391070151030340c403000002d403c0ba110300000504101c04000c10240786000d030426181442c00c041281c25811b0300da4182c4201601c04103000c0000c20500b407050500100c80c1586510f070040c502e0900c5040840c2d00502030603400000c04441030240a001120900ca40b00320704010305c0c0710500030059200140200d8a040015003032904102100350090300b80300d2903126503401064520004c0c40050340048040c07003070340d42c0c0304803607112004103200400141c0c03500b070900c41c1d1004091800203881e1611f440010520042c15810440c604000c109000030150410b102030280c60558594552440b003001013 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 364339883 1250 364338633 364338659
    0x9010b03030a300b0a1710050915090607031a0f010509030c090a090303110f041e0b030f0105030c040c051c02070807050703030e0901053102120a06150f0c05100203010816 75
    0xc6c282d00c0d50300c09002c11654940f00e03445507800030349940030703202c41c000d880041c0c41010405031102d90706a08440c4c18010a240c051083c1e420f1021094074202c03481000200281142101200480c140080011409050355091100003000f00c0b0043c4540a5820001040c80c000c00c0302010440c0031a150207820350342144000c003a544a043c2d03905000c0e203130038180070351081d086203402d403115041c3e0240360b008540c2113098006544117960f40480e00055600d0305040501d4000002c400c18091403411400d4004958030908071008200c00c4044c6003044421100da40300207114808010303040d80c40214400003000408900c2004032030003a900c83e01204c04410130081002400e1082d01d42c000d41e1500e80305072001c030808541c400b02d0740b11421b030b030030b00541e400c44042030340e20008511041c0f904120820010302018402c4030090440c20344240b40211071090081d100c134040024180034015511608000c00404000c0400d0720720342c0000035516540d40d040f1456481c00ca264000c500108142c2c0c001c5801c82d0301d003c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 364341133 1250 364339883 364339919
    0xe01020d20070b0114030c12010c08060f010f0e0f1507030206010504050112061e0606110f0a0302060606030406020403080a051c0e2e0507021509010b03030a300b0a 72
    0x76400f040c030791034041c044142d040908031154040c0654154201643d4a030a90035520914080000c0340700c44003600c008201c1400242068410800911850b0341640d0022205a40303440e103040c814409940b031400541410300c2d4264096021319001c884800d120340c08006000068400e030200c56890341c807401040107a400c00d000780400142d0ec0301442c0013249a64210b000210700700e044a13519850b0b001040810344250780c0080c80812040c0c4100e000399201001007e1002140c00003400410000395402500e441014195034840c01d804008241070204e281c3c11034000759404901c050361420065400380007034110240316211221030105030080d0013060b0240f5141c022600016114450300b601082ca0580d12000011040c1d0481d0500340b00d014069204181c050103039900244684450341d101c580d0745036130081c8401401e904040151807103031400019200c0f0b048141c100380c0e01003083c0030704410400442003e01d01c03110f045001020404545039100c0c460a68082e2104a05140c5544001e46800c420711 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 364342383 1250 364341133 364341143
    0x120a0314040c1a1806220f0609060e06090d050f10140601110a0303020d0608060a091103190b0711060a0b010909200f0c0d0809060a05040f0303050a0e01020d2007 71
    0x104d61090540f400301c00034038903e003034000303000106043d864074200d42c02540d82041290303901d60b003010300c1426041612100100312600c0e00d40e4102d000311003c5495406551548c50051812019040400c102441160741000103007040b64224401540740101902c98404803042d0200e80d02c1c04210503522072541c034024802c1c0072000f050007203940d581c01c800a50150341c103481925903034040454410740922401c0c2c020130a681020808030b050f400c000304014203825030240b1985c880b20902c0c1d22000358078034010405401200b0041d40c1c0d9101d240548000396682d0040009004103010490410015402040c00380d1080e40c480b444d060302d0354112011920350803004000c50070015002100a500340d00201030410000045a040814000d03845141003000d240782c0c0e01140d00300302004048882000a250702580e00b0500f480103040c2501c40760381103000b440015080540b078100281c6900f0b001d40000030f40c80111002155219030f001c0d0080000c040c6c0216001040014103d1041020b4a00083c0c0300d8140d080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 364343633 1250 364342383 364342417
    0x302091005060a0e01090f0603060e060a1d1b0c011d0d051b070b040303080a0506030106060903060513140a05010e060f06060a0207030209100302040b0a08120a0314040c1a 75
    0x1c3e04156503460646400f036040180304140807450708200605540202400e803404030b41c2605114000b40d860342c0c010300060081d0401d00c3c0421406642c005443d503584003881d90340d0901c0e00c0d41614a100c1660201c442c00b03400b6030010750548086c034154448030802d01c0000c01f040840000242c4c0680715610030030000d0020710305000103030304c0219200581134403804200807182950741e0364181075507540042d4425008100d00d817040000741c1c2d9807170041c5548010118020007469080c4900540003030b900f800081c012a41e2540002c121500e00b41c00f443c0f8280e0081001440d00a058900c1a0b8840821100b15655401c007205826005d00024941d8001c00002c001c020503540c0e40000e22000380c001120101c00c42c81850800005a00c404402d20301420601c2803041c4118110b0040c002561024001580243c1a46000304401907001c08c90b000c60343d500343c0e0003070b0392000c6101c41200901222031000b041583c5080c24482000441d07080314007190011076071100034881d0120071003c20b01561041107050401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 364344883 1250 364343633 364343647
    0xc020c120312070e0306090c09011802070203060f06180103020901030323041401030c1b020f0f0916180305210f0706090c080102040315020a03021909030209100506 72
    0x95503404103035503140c0c21079050108030007400d003490302c09403610408259a2850000d0a003410300401c2d6200c020702d0000c00b0704180729400302d92091014810012600301100d011400300704182c04842403150020b0466009040802c007803040ca5406450561143c20030754103d071040c10324100750a04880e002003500c203d03a0b28645098680103061801e050306803e0401414150440001c094000350207200c0080d10740c007800b0f900160880f24005a09424031404810900c02c820616240403000c50b41940c00308080d00004000c5510354540000e103640c040030304000c001c500c87e0316402015012040f652004072207440c1441c010103001441c04090b002c0e800c0700c40c03030042910f20f440403206195503a0300790034680755691244c2c0300d444e0003030b00c0d003140c64584403d840801d02003060348203070207820000021840c0502d5550b40e0380001c0061000a0445170300840d80825240c0281e05440c0d8054059039405800013003a0001001c20403e8001248101c903440c011800514440f010681034400182c2021302c2c083c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 364346133 1250 364344883 364344889
    0x6090b0f160503120f060103020304051b04020408070909060f020f070f0f1202030304030210020c071a040b1c1406010c06090c050310150e04030f2303180d030c020c 72
    0x4070020340090380707101c450034100c0040c41c100018003038021001ca01c41e0312400c1c90380c482404410b029111b581050b0043c41448085800071400032040c480b811410180480d0883c04203020b0f0143d54414412405044000203102074190800070240e07119640c00c1020000d0a40300380201d02900c81e0444c00f824051010a0000b5820012003034013501030450ae15110b03060780e80321091a81d101011500507003020061004140c0c0402102d144000c10b03140a42c24040340881c081d03601e809170b20803205410792841590604621200442d0040d14070000c2403551051201c0c0c0001e0f0883c48550280469460841886881c0e80000511802000143c0d5080d08044060f261a80901071410007610034010a05000580d903608014172190b030b40803a040881c5074030f4800c0800280c8051540306000c1007014204001c00694000c00c618980d20039414140440c02c00c0f1901c1c104690241c0381c2c0407600b05000810b0183c0d0000729400d2140d02c0e44082c00311118960000c3c0b080382500c210002c3c1d031001d42e200c101071240030f05d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 364347383 1250 364346133 364346137
    0xb03031201030b07110604031d0a080c061b0601062a05060705090f040e1006140a12050f030309011505041503121407080310050607030f20011508010606090b0f 70
    0x2000c24035005c541020000c681e207040001c1503904170045540d0310400881d008e040b24141119280c1101c01841d8103107805034054a81000b400900c0c4119000148008104411499101c451460000702c841542e103661014041d0781e81015442e0740030204501c0611050311018010003481d510002418094682200030341d2180c1259142a600032503000441480d030700ea9108060821004000502206012010040407101c090b013101c8400f10030480302080741d4548034000790407514092100110100f80b8141182007040c0b6840300159400000203010040005400041c00d900307114546100465540303007000119183c0c00c031400302c1e0300303a81142003011a01c1c4486440501d03145040c80500c44c0441c45c011540742c0e000140c1124041c1c0040103104000341c008840e00701400c003d40c1c10601d018525100034009a400e94459000c2282c000c41444034130b10754400c02100301146030300a2100e0307040d0341004068180d40380036040303580d0701e44080050310b140b01c2c0d16030200312100000400e103884549031401480b5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 364348633 1250 364347383 364347391
    0x61c080a080601030b030d1706060c03090d02041b1707050909070309020f0a0303051308060c07060207050a020a1205010e2107081e030114040506090f0405070315060501030b03031201030b 82
    0x41a40d030903004002c0c1d10305020031010309107623644100303040c0421800444d134420090b0445000b890b0601c44961461800022141030380070484100807440010310006010b041c040040ca000e4a03039040455903104d4202d4040c1213085610002c694403545d41900481e0307a0b005000b8403540c010380220200b800540a948101400742c0080c00c0c0004280c00c44d0042519219594000c4001450004160f25000300501c80c90740a041203030041e01c0c441c00d00f03110480050103019000f8201070b81c0055900100038040251446d000d5014113041101d179602c1751030b29658040c0c05c2c4c0a4035554200b551030b1342c0d10400070501c07410580182141000d40300c4040c07149096a044118100e4150340c0c100f1201d02c42c2d0302540c185209100200e071180d507480d81400d0181c40c045a416044a0040e42445c040c4111a42e40d02e81c4207030310240001c403490b43e0b9075860a02c40c2c41c15101e40e00190103111107140210a0025039004042500c0f004e881c01d200080f11401415a00e20a403102d09000c0d117074000040c000104980c480c036402c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 364349883 1250 364348633 364348637
    0x102030402090c1c0c0507060b0405010303050307080c04030f080306010e0a050616080c060c07140d1209030302090907021c11070303031805010e03090103060b131419030b061c080a080601 82
    0x2520084d00000c0c00725910344c03001c000030403c003041c2c030002c10002d802182c0404109884c03c1c040f030351440c3c0d00a022404064044000c2c0800040000c018500350402d980055810029a081d005132908100c1195402514064005141d0010515450520080100441d03501900252800e081035001c1042581118030441d0104410842609440c008109507409001070208031580c60a5a14040d40c0c0c0c03d02e0903a896103290400c44081e0380c6ca0303802c500046000000030340045a051041d1504600a200b0b04820a601c030380c0c040e00740500b40760700050b4003e2052100241390003010714010141c1e0804084288140d071030340401c2d03050001900c41d41200c00036154502001c464050203a83e03542c01c2d01c51020800303070342c0c1d40f0105912907a0b40c0d25016407402440c3c40540c203850001000ba0302403100c00c540c0500507065032500c542c40d1040c0c48000407113071984000c1e020400615240c6c0340038104523034181c464034440d84036444800004c0451025000c042d41c1e20480c500d280149004080c2e4030004010042d0341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 364351133 1250 364349883 364349917
    0x17090a090f02121005100f09090c050f071b050f0607060c0c02210c0f1e030709090b10090b06180109030812190204061d06040305070303020d110102030402090c 70
    0x5054405283e040c0260342d03c0c0c0315850702500340400d00200c00344500c003040c108030302d00c05080003140d04400b900054810a4101159041da56101550940b02d000590361702c0700000220641844030003030880c914102038007a49848240d80300d0400c0311044507481c0c034552002c41048080000f0f0001d900a010300b071602c6c108417044c2076258000a00194812105041e024034020002140c044203004103174055104841c450242203a031804144c4041054200000081d00c00d0000070b001c0d5070400c00c120042c4041c0c502400440018507004843d18403c0c0d404d41001c40c50144003048204903800b40311080b260103013006041004480d030a0501d81042402c040c14080381550110114030200c008041100010002503c1d50a01041c10700340656503400000c0440c0c410f010900c1310a40c0f20801c144058071424010408040620001c0c8072445190b01c01402841031610010401d074001c2904400030320342d40c403165190304190715250300343c0c40704a41c002d500c400200c1c0025108043c800c01391031813a02601c2408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 364352383 1250 364351133 364351147
    0xf070309151b0c0e160206070311030711120d0204030b010e0402150a2601080c031c050c0c1201140f0610030e0a020a030b010503160b030609060d0c060c17090a090f02 73
    0x31345004299030394120041c82c80c0c07007090401c0d010014503401501c00d15041100c03d140b0001d2600901001e0300c41c40401c000c40703141c40c0248104105290f650301c80c0c20441551072000101c0800254040c1c481192a007543c13200002d400020300716078503c210380150880901c103400001c0f010b982d6120807115000d01800886036814202a180f40f001c0640c1d1078038409015504101d00a0302d48021400014469402015000c0b0050107400303051841c072089003051602ca9407842c0c1c1d03890400c401030004680181c40c49444500390301c1c054000381401c0d0b602d0200303400340b03172540c0e000c40c0c01c0103c003125140d0b0001020051040d400d486540502500e1800000791018004240d000911010131640280c8020803030302c00502640c40c05120401100c0462501080c1513864040200254000149141d00c80c01c820340c005459601c0384003607009401c1d8480315107006a9103c4038003500c110054003042d11240c412503400791171000c5420489000d200f000b04404a1140382c501c00202406000115060384c40e003c7c4121 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 364353633 1250 364352383 364352399
    0x1d091f0305030f04050406080a0201021e070e0f07030e03031501050304110d0c061d0901050d240c020c0a0815041e0b091b1509030a080f070309151b0c 66
    0x58086100c0f81c0407600ea403145814100f0003a80c10703075000452150403100b03040c1e00503a000034800da0040c0281c0c6e100042c4152484000342003070590760003401655001c90402554103d144100da124401e147ca0800070481040c9009980e4001210031001103400b401400080b907002c2e001441e03010f40300c0c000341c583c000ca64001045400681400851300b40203030410034000d042c0c0140310350a40c481580b64203c440c041080001d285c000040c403606000700040c03174512060100000c81c10001501c208074204e02c0040d004c4c6210000c0c04030369003450040c01628040784181c42c05003440421500c3c80002040c46500c4d00f0303000240c0c0000074004a41c481c0e4520072591040d040d1400303405d107039406204500c04034a0542c0c4a142007040746100024a280f94021780f02259890600884084090345603558680188ac00480d203080c2840d032000d03001c0c1102296441c81000503000402c4894880d5883d00351850342d030403002d0389036111020828040317104809120748001e0000600c0f16031500501b13188182d0b96840c0c1c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 364354883 1250 364353633 364353637
    0x30e0705101d01020c1311090904030504171504030305070903120309030215010b04060f03090501051005310c0c020a03060b090f06010e09040326071d091f030503 71
    0x6074000c02c20042c0204140280c5100110360000d0a00107040d00c00c510100003540e05504160b00c020403981c1394400380d100c400c0807042c1c0740801c001910350030b041c1c106428041c106800c14030502103100303218190780ba44d0b40c20101d2038954110701000040c030f85031580d5a00307a01414004010350b003008100c1000102152031400b800c4081000b640700000c50300b51504000341402400d855490002e4480300c0108140112141281c00300c411034548500c0c00050840101d0281c0003501c0c0141056080200703000c12000400d122801715401111904445111840d9000000001c0c1800e1401d0000c030300b1815841c014550026600d041c032518007280200e5255001607601241504103030b030840d0361100c0c51640c905100c2121a040807840104880b0761803c8030000b86040d0304d0140080c0902c1001c0045070404bc040e40c00b86550f201c4108011219242c84503900c00074502c200c4100000880851407111000d141c50003c010750f0002828203549540c82da0008140c0d5a41c0b480f04a0f03428051010000c041001400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 364356133 1250 364354883 364354909
    0x3031902010b03060c27181003080301080d120509100b03030c100501140307030f030c02131407081806010e040201170a0207110603010b0d0f020405040e060a2a030e0705 74
    0x203280c0b52910f50050042034144503000c1d44004604800c0301106c129a621030010f4603a0155080303080041c0d0303d00da45110316100755071001b00540c501200118140e1404100c1000000855880301c41038000142090259001a02d6001454100b07aa44407400b0f655900644403620014040b00d01e840200c0d15035a240ca12103910400d09269600700602c403042103100c411140da0320440090640c80c1c00c603100c00030b03a0035411800034184094a5541411500c1d0b101042c6400f42040900f006513222182140c0c165590489403100011458000580c03541074206500c019069844001c0000d80c0c28a6407c0c00039660240c41a030621081e88400841c507041031480c14480d26805e4000341e100c00041c0313081c0b500783d01e2064200344a9002400140840d00b00c2c0c000b40c1d5003212403241c0c0454051070134601c0600a202c3e40d040740c0c1c0c100e82412040c82001ca00000ca86001e066080010090743c0340301d82001034640808124185220701038910103880c203200c1e8215217682480303001511a080d950380d00085000140d15 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 364357383 1250 364356133 364356151
    0xf06011d040e1b0a0506030606040b03060d0204060b0a0201150f0b0f07020a03051f1a300a02130501051c0302030d05160f03060f210206210702010b03031902010b0306 73
    0x1525580441c00c0004581000703045c11396165065040845c0081d04500a40c040ca084603400032001076060b41d18200030a50107500900100100b0740c4030500000c02c0d80c04824801d002d5070034045a0b1201c0c3c0d03a0086d10b10221049405110240c40c10504205860380c4001310302541d00c01e061101c880075030741300d100c0d120003940b00b40001c021410010348019030301c240c400b1060f000716141c050903090041800381c0f090b2510600711050b403d500320342c22008a000e4100300250b40300840d9030304c0c2699800c40001d40d070341e001802110001c040704d100c0304848054542c01d000311504402c03910b074690034a030040041d044a03103209005581c04d010280261708125130782140e05200d405120b1890005a60300702200c017205146616007032140a06005ea0420200d02c140b142c00c03003400c240500503101408072041440c02c1076004002e41d964000300072000070b85036403a0500f00035502110300448c149500512611014181c058044e6090001180400644481500c0020f0940d5210219100b040e134041c800070744103401c6c0d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 364358633 1250 364357383 364357423
    0x307090e0a12030e0307141f020901021e0705010e0a0e28020702031209010203130e01050f0a0602060103020d080f0a030516090315020a17100503060f06011d040e 71
    0x50308000d203070320040c02d0008052500d4407001d80c070903c501200311184c8a800c2050400306c408100704580c03070200b159001c03021040580300c52410764480e41c0c005100511090b82214001078080c81c860041208030515040e00c3c3d40850401c00555004440a00908600404281d603460b950010b51442c010204d130204a8003d1000c0c2081205000c0c88011403004070000f02182001f0090340880d40c0c414005c40e104d2010300f004508115241c0c800c00413036500c18510300484258a594528400140d8000c2c002d0a00c01d040c403d06c07040c000e041c0749059004484080d402410103910f07680030b0150444000d142600c64007002c0000305000281c2400402440c44555000580c62400605881981074041c0c4003400b0802103001c1000818258500e1444060040c2c0b001030f42c0b45600c410999140c40d00c0c01019131107800c1c0800700041c1000000d0040200c0d141070301a01e50319520700d003030200d444004807085408101c2d075100001d1011001000740c0d20000380980000703480e11180355503500d4445445c808041c07200035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 364359883 1250 364358633 364358653
    0x905030d020105010504140c0a080a0b040c090503150712110f120402180702070501050903010b0901060c1203060f0b0a03061e03110901050d1203110304030507141b040b0307090e 78
    0x1052203001c4100e00c140e81400d0080c2480080230906209100700c0404214840c008503901c3d985c01e911450414600400c10040d0541c00380e0040c02d00740241c42001d11034040c841d40440c1225130344481611075886a684c0c08d10000c0d4078055000100680d06a0145541007800500c0b4508208001001d008040442135042031401c1d2040000c8076803861039800910482c0c50602211a0300082d2010a40b4000d0811a84a104030f0b00400d00500b9003045080d4003074003507000050500e40000c1100c2e031181c090540707521903034603843d019804d4464610403044400c40b081d03002c008000000c40501004c2800b4a000316505d540c854480c1120542d00b82c0c00c0b03905264507041081041440200850511802c1e40e01490303561600f4001510707032925a00242684800c030040c8030b81d1920070707030201004c40c0050000d95180d0406080041051300706820481d800304c22070340603c4094500140071035501d14480702d8031180c2004841800090068074141c40e82521501202040e810518010403024800c078500402d40d48038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 364361133 1250 364359883 364359889
    0x203090120011a1c05062a0f03040302060705040f0b0306010314090606040b0103050c0f070503040b041d010509360109080a08071d0f060d0525050909160905030d0201050105 76
    0x20050360300340c00503801501900001200840c10031fa005891200702441e01e403200a0010002c4000858000c00603000910008006001d00c007460117940242d007158080d03580c255064405206034010707520900a516803c210802d8200c0c003c41d804601031402141c244100c48072240d034400c0c00d45100c06241c11080c2000707a2812b00c0d210b807100100c406d180510040c10300d9403040c20b07944200522030b0b81141001a9101c184141081168024000742c2005a034032541d034a1402c10055202110b49002608080001002c1c070303060743d81c14010390428a00000da082080c1060340da0321015411f5280502e400308240308031840070308c40e441040d4003030790710140c2c1c524000e04002d0030024000d10b071900340302040303400003929107407141c140c052a40309071012039011201d0000942603001da0407c0b4103100e0309000402c80a124040102041c480070034100d40e07000c02d22908262443d00908181d207401c420403a0021f074152103081c106071341403065400c00c4101e075070720b03680400d00781601c08841401503910ba07070042245e41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 364362383 1250 364361133 364361149
    0x15030308100308030109020906040f08070e060d031b02030f240c0a0206070c0606090606030e0c030d2a0c0e070810030807080702010311031005031902010203090120011a 74
    0x1a004828041c855421580d40000902060144640003580070561540c1034a4041c00c40e405400030440c2811120b50300d06400303685203800d0203981d44500d0114007040650400c2251103880d0390303040c2c40314210410340301110707a02c0c041c281009076403510400c440310710300c0b94050007000c0d1032054070090300c21b24000304183c65000728401380100032802c000700080c248041c0d012500e1074124100340f03420000300b44103081c01c6003c2d00941e0002c0034401c1c501540003480507090b92001480c0b0a80c0019620045075210030541c40300610303241d140105848401d0b013143c84004c440783c02e8100e600751180c500f1224041c1c0740d2000034a46130b0403c0c00c41c0a980000e1103142070300400a00d500000d03441107150403c1c119074404009004980b0024250a0003041c040f045a0182c1c020180d2400381444041d01c1c0d01e8409404030728503034148500b50003801b4114907403060403441000303044241c0e0183c00561038040504011514400d1400040c4070403982c41500d000d1200b0300f80900320040200c801d03414940604501004000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 364363633 1250 364362383 364362391
    0x40b0a02062401080705070b0a06210c050d0203070b04080a14120a050d1407030605040b030102091c030c05010c031d06090a0605060a0503011509140f04080a0c02030115030308 77
    0x381c04807049a03641854140d61698030b80c0d400e107000c1603962079034035050301c441c003540c039004014594070410800c0c42c2e1020b0307000b481110100d915404120050a40343c8400f00784111000d0702a0680100c01e000740c0c102881d0107162103101500f2a0305195031004080010740054000b00501c4c0c006050b20b200b403100e0000c983c4a00244031000d40b040c0000810411880e1051804a100780000400e0445816000d07602105001d003c80c1c03146c10321031514860040051405001d03842c0b16503e006040641ca050502c26101018005046002e44500100c211f22507220311100031030800100028400c0020403c1c0100c0680c614652000b142c0c240c40030b41e2300ca1a50b401c10000c1c440700d6010340d04000d400c0000182a4040a8001400141980f501c00225a0034021030b0002a0903608201000710701c0c1d901104040101c0d07104100c200405128041e100e004040250341100c21206084042004030b440d04006040c1100541070644505200354082400c0d0b0b0a00c000200d0880760190040041c10381210040c0e40c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 364364883 1250 364363633 364363651
    0x114060f090409020d0b0403020f010e0d0e0f03010b030709020909010605090306131b030f0c0503070602150720060a0b0312070b0405030c15070e06070c090b0103090206040b0a0206 79
    0x1040c010140c112228000c5425082c482d0f80c0341c0601509540b240744540010781d410048020301807501c0d003406556240c42194803200d542c40c014201101e880d001c590301e412010300d0390b118410205500700700860f0100064409600d5540e07507007241d0603a5000c01000700248a80400542c465001d07130700b00451004168400c00520104110441103603270041030f40d961002200b00100903d241500b07107807a03040b4000d900102c000d100200c001c400c4c00013003098407800d940301700110181c09484800f80760b1100340d684642400340c2d2007003007a041f41c208480905980004d1500c0e0444c01000c1041007000741c800440d58041c8690007280a0100000860040c4108803100350003c10610752503031001318052161120180030014480041010030000307004642600032034404440360038103a040c0003104000305513041d4000c204141e910381c40c542002016140c00300c0c0c100001c0350000e468040041c002c0c0c00e085184604055071001c4080060b0741d40c50140000c4c002c0101450384845a45002a1410741c015104d240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 364366133 1250 364364883 364364887
    0x60804140316080d0f020a020102090a080c011b1104090804080c010906050412020607140102220302030619151401020118050a03050f070f0506070f0c0c05060f0706020c010203011406 80
    0x24101c0441c1069541c8543c8014065604e200ba0601c8100520340c400c840c15a0500000c1e000105543c1500030b484034901c11100030305542d54850000e580c406014180d64007042020140b0080400b880301c600e0001d6002d5070481c3d0300c4d20b601400050403580070100407260751a0108042c88201410030440c040c01c070007070038500012814071101600030300892140180e0000406c0c580300854071980195081030768444145da040c0a94144502d01031340240003601c0d07d0300e030114000304490711019910310882c0e40203006004c0039203542d6954042e01005030056007007152a19811282c0c0040135000e10010140c990f07000f00080c0d0082e0009003540c116034910b42010700b51b13810b040f02169000c91950002079040c1417003a41c130356402c10044140e014468024003207500c1c2c4144c2c40244030380411540d201301d02a23590351034841710ba00810b0701c1c2e40c080590f018210611000c014005070614000801c0151034200c24142416030340c0c0d661005a912185403654165004001002502c00c250b8600880c96000c4807614 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 364367383 1250 364366133 364366147
    0x9270c03140c090310061d092e06240e15090904021c05010608150702100507020f030a090504060611060a05070c080313030206060604050114030612070608041403 71
    0x5110000b0340503040c104000181c503d0107941c108100d020000c41d010b070038401c1a503958a684d40c003142c010341c50940c1465400000c0c5048030081000c0501000b0741d5055200f20003070264140b160504551422400761b52031002140c4910500d00302501e4011070340c00b04e0b0000c1710340c440007446503041d04060360241e01c407140003260883c3e165003541d0346000103071020851039550340001045400e16a80300c6100300d1080039103a043c0722064000d10150345602d0308070342c042c8010304400005548101d0300360f00140c0002140d180418403a4105603003101e010310440f0807481916207090b0440d40201c10500220300c0c135200c100030500700303801450000c0c2094103111000004040d9030b16181ca05c01041d041305d05965000103003049015501004406030000603081e204d283c1501d0f0000d003003128032010760241c452100050034030305d0310000700d030180c96040c3d443d024081d10b940e8807280b154001a1200368001d5000811000d5044100000e03c01444d1130307910348c3c1e814140790801a41141c0808000e8002d904100154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 364368633 1250 364367383 364367411
    0x9010e040510090207110a06020a11060f030103060e2b11060105010827100f0b0405010b09100c0816030f08010b0a0809030c010e10060e012409270c03 66
    0x204220745840f0310142c5c5d18070311860001c0c2c0d100e404042c1550f00009041001c60b026500140e882084c51094000070301c5035208000704010382c0110594003c140008200600000704146c11451603100080100c0303801c50b1000149031400e0240c405405840d40c0c210500c1e02ca0746030300050410003001d200015000755410100000c0112800800440403520b1394038000c0c1d203d44074580402c02d80308401080d60300c0501c80d00810005000050311003412a801c1018034681c03441c1512a02d8101c900d04200203150505001c00d000f5124441d840000601c4680802c143c040f83c504030085c1008044184e1344080085c4610300500041d50000c44034042044810042c00002e42010486080b000c0d10700b05040d10390740ba501d8003460341c81200d21110055003000f040c0002140001200040b104403807a060014544801d02c409000e002441808040e031141c03102c9010200c1d8601d0012824551460309007441c98940c0306001003241d42c085a01500c00c200e0341c3c041c2c40c000d01442903202c1c11501b86003d0010020702100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 364369883 1250 364368633 364368661
    0x3091504020f0402030717130b060f031c02160f0501090b1312080d0c09051005070503030a18020d030807031a210102130905010312020106080607050c0a0c0b09010e0405 74
    0x8550150743e002011400d41800b401440b007e82082c1003181403a441e101044001c0c0d1020402c2c21146150940003240301847c200c02242070542018004103040022010b440d8141e07210044d00d502507000702d07a50403128046142e503602c0507011401e5100310706450103000404406c21507100000f510b005000714070b00380f9180d4802104550083e240c04001c550981030002403031150103040a0f003a45002901000341340c000340c911b012510b0490f10051140c855050a031200c0c0719a29004006400c01c000080030120355500241c501200116203921001c1140e0224078100c000c01019000f1659034406c0003842075140c02080c400180e103010315240ba281500120340c0035205450070304e8048207004504880c1c0031095050310590040720b210008425501d1040b28002d20085c0130984000c5c0241c031890280c140140150000c42e04020001c140940e10350f41d00b2180c5801204c0080c500d0300503480d89a012680f03622060020380050782e80c250355220400000f404a0050901341c9015605090400c4519408050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 364371133 1250 364369883 364369909
    0x209010b03060d12050d0f0f14010b040902130906230d110d110913050f121210050301020f0d0b090c0f0a050729010b16110103090204110309150402 65
    0x1e80e00580764136103031054600303003d42c40214058514202090303105a907030b5048503001c00d0200c00204440d900400c151421001c003402884524002007104006801c1c060740108401094000020251313130b110341c3c513001616203c0c2c2c4416540ca00b540001440e221002085a804410444400d03160004c196030300e80d2206280c0050303611a9030240314420501482040340980c1490003422100f052078086d0181e224060803401c04e4400d80f00f002840e483d6010001a1020151040222230b410310010900024001c640280410242030541500007240d450900181070310034621505a515020012540c03411200100b11952145030b8820500c0300c00c010103011a803420500444a6582d0b4400710400e0380c1500c40c01070000c01c54003100000c0e405401e00b2410b2604101091004000c41d40d03030f109250722031801041803040304000c004081000180740800c42c0050000d06040124021419400180455056205034144058000300b00800034034203004540f2942d10351841402e880c200794000c5800c04200305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 364372383 1250 364371133 364371143
    0x12150a0902030901140a0c0e0f0904061e02270d020a030312110408010605041103090c130603080a0e0109090e0a0f0602090d030c0201030615020309090406150b070209010b03060d 78
    0x3022802118084d009170241c0c02020300781c00807a0504100711401082601c01160005400c10321030000c91030700c0c40c0021407502d00103065100c10b03252602c80c000100707440341000e102c0c00d01001c49004a450180081d04500a60320001c0150300350740e2900440302c00414400d18031500580d20300d1401a07942c81c4c5481e013039a070135240c06c2c0080076615803144001c00b15007940c81100c0e031020500250020054018806440302920f007845000f0414944034110300040c1c441300c1c4a034120304a2460103003010081188180400000421002d60f640c840b4803041d4041c0b0405000117070160f84848455030802c900100804001d5401c00c0210300200360b0301d44402c03000744000d010355810301540f0288400790f0169805014010410441c0150720314000c2c0c1880c81c4d00400724046070400c0e10004d08030313071000351360000703041d040d00a149002c170001c0411400580c024801c552141d85e651b44502080075201261000d0034140000550310200742c010828518070581c080c3c40440c10810400c0016208c0c0140105c29a03481 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 364373633 1250 364372383 364372387
    0x5061911070f06150914010503010f06030206190e0a0e07021c020c060714060106051b0a030503060907180f0905090106060906050f04030203340b090112110703030212150a0902 77
    0x7140319001507500645c807050b00740d81000b0301c0601c1083d06a82083c100e65046000300079162400040e14203031038480c8406540f009050201d8220200803038101000d114003407425002012074203002444481180d002030154501100410410a40400882d0146000080c900d40d0791140d50600039035461606600d54019940030428400300b0000480c03038004020708600b6a2125a1100c0e00240706400c2581c0707500000d048004800800c0c2c80115006070400c2d0559a101d240d99030758001c3c0700360b116001d0504410002e14940340c00d0b11200e0700e0710f100b001e00101203039030401607d0590110f0036100042d18101059140003020002c00390000381000441d802420b155482c1d901c01001d4294502440c3d001a4040c0200c0240e00200c00c0701e0a40380060945030140d40c640c507011820606c3e0307074106038000c81c60060b1003004015070a40c011311002c0a905000c00c408100c0c0d140d81d40881c04207411091048001c00c3e00800d0308901c1010064520368498140715049440c9114440000c0c0000102e228440e40380d580 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 364374883 1250 364373633 364373651
    0x60e011e0f180305030c0d1707030c11100204230901050f01140d050703060605070b070e030118050c09070206130b070e120d081005090a020307090305061911070f06 72
    0x410b40c044401865210a41c1c40c5a0b80c1d042007510b9a00c00040380d40c80c0c0c050300c3c0483c401c0c0c9000d50290544642540854502d6540d00107084c2c0003410804903000034010f14410b40f06072401c080090f105c10615020000d038176940780450101c0ea0000d04000c102d0805081d2a024030703d6103584840f1411268219103681d08401c1000050340c2c0b8200940915004904c000340c080404d59580e00302c6801040107643c100003440d5503280484560050b400d0080c05820b83d03d011070601c0c0d02c54801406c200d00c006000082030403a6034880c2c1103000c0c1c480000c8845811a0020483c5450003c0d117a640c0020640043c2500c0e10380030503880c0c5640e810324401002c100a2001003840c0905c190756142c1c24a00140090a0b000384040311240d4a90310401d03a400054200d00008000d440a410480d00700ca001030600f0f8081e4641401f1480039402c024419820041c000c0000004a0401c0107028052001003440840444900c60344800307031294440c2d81c03010f00c04208107020004182011103500c03990031440c00940501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 364376133 1250 364374883 364374887
    0x26030604050619121122050c0c0d031e090210031503170910032c0a0b0f010f060311160218010612240b160b040c060e011e0f 55
    0x194000d004600d1040c9040f020694010490308181502d0040341050226098003082050940000100030400800040740a14000140e04696000680541001d007000000c210340c91502102502d402c00080e00c0704040c02d0030344a034184150b1028011300040c0722640c51a0003160031503440070240c0041650340c14140315021001c1c4a803a01460b07012456541c10111699980c1403600030703c942e10303c1080c8104035400041d000b0700c98070f621014039110304201d800050300041d890392024810000c0ca0301070924000001244084418070500d8420903448003541405004030310f00841b41c0010302818075003090021010708100c1580c08101d00b80408012804140c40850400504000c0d00c1a18034010000850f0040e0441007500741510903450802201040c00c1110821079412100048401070000741031000c43d00e20001411000c00072805014801810340d20800d04035002c0b074042c1c8240e00e94480600c4100d900c0318598100600074a4104c0207245a104141400b0501041c5981071000540e05118154 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 364377383 1250 364376133 364376149
    0x112803060e040606090c030e0712060f36020f040b040b0306090319090f06030e1509100506060a0905060901020703080f030f16080a0209060408010f09260306040506 72
    0xc110003100700303824242480d0410282c0380b0350040043c0c15081003104082d0522030701c01d000c1c079549034100900c2030b14030b40440d004204900d0941681c1e42503c8034007803081c49800c0e000b00b60650726510303555040070007080110031018000300c45004040404a1034440907030707620900310b40468000c8074000350706040780001400920b0205180e03500b5015600c1000300201000c0044d01c100303980c00040c0078648d115034504650909980c019243d9165004500780201c0c1d200c2d03071001c1840c10802c0200c40841904c409603040f015012248080c00d40c1c0111480c000182c02c9006040d000742c81a14000d06165103000003805010150143d60701a60000c04c1c7c00000340e200704001801103801040803a070f101d41d82800c0c94270302c0d03104039001c1c420200d28002281c101e040c6001041102880c0342d6640711507480f0000d1000c080d5105074100b9074812030078000416100000c0c171a007085d900d445240080c1c03007003081c0b412030003600c84003511115040c3c1a00354070040c40c15000407a41e01240c1210300203001d983c0c80780007646103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 364378633 1250 364377383 364377389
    0x30105040f240501141309020309150906060a0b0c0303190609180b0606070b04080a0306030c1706060102060105100809120712031823100f06060311280306 68
    0xe616100e03074000049505002d9070580d00207a84603294488881d0b502d009900c00c0000fa10704c08a000c4604010a221a03809150005904001d9442d00d801d01d85c5055000402035441030701580210040c8103035480e01070741d175000520080f48020b080c070380c0c0c0a0001e900c0780402800081e80148004000456402680c0110b0140414030401c020900480c00140021010a8011180c001240c80814000d103420401d9a46aa50089900010781d4590382c80259680010030041d0034551074080100000b001a2050000350400c0c54800f0400c140c08003039a4038080b0f000d4115410340d0001e4005000d141c841d611458848800d82c01d03e01c040e40c40c5c0014a40c50444501144441904089551000c102c0e4030410031b803005100e60340c1800381c07000d80003589640b032503450801050b05680c0f20790144a80c04421642c220110304100f42d4030700d401d0241c0381e14280d60001e00c2103900140e540308140907c075014070a0481d80754000403440d0415008048840d450460040d180300d80e0601013513580b1481740709030084405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 364379883 1250 364378633 364378661
    0x30320071508040f0c08031b0a0f020d0c090f020306041a03030a11030f07050304051801141e120c041104080d140403060f051905101404090c080a0c0503070803030105040f 75
    0x45c140c0c0d20107030741d901d90300150021006080130000c07400311040c000410a203103c1d0041009000c01d0f10681c2000702c130204681d0202c60315030b43d100b400201e6610611a00d1201c039034201001d6504e290020401044800300307141104042c400e5102d40d43d46460000a035161125a420101c00490203509400d24500803901c103928000000a06542040f10110161049490a0ba0140301e46050350a034110510002d000b00101301404040740710103840d140054040c5512050001d50b450030101000c500440804c5044444640c800d0210800d07070b003402e10550803003104141c05141014104140b00e038030f6681160f04403080001018092a41c07110301000c07180210f92060081000c0044141048003414048540c02c0b1640d00b505c0300512192403e02849110380c0d0346c10244107060b400c0188c02c8200321803100c502500190b94009400000d80030f0041000034161120090098010614126901c444650881c03400703900440c104000c07482000054a0542d50100d07000724040032a029140c0c001c04060300d840038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 364381133 1250 364379883 364379903
    0x20a0903060e0a06150e07030906060509040f020906010f0e0f1c0605040b01090504020d02010f020304090204081c020a0b0403080c120a0b0102010506031c1d0406030320071508040f 79
    0x24200b000529040c9548541d40034460088003066513031030300515108201ea041403070b000040d02207100c0d600000d2114880c090000d00c9640b03940101e1422142164202d810060070300d403510a502d4800c403115842002481d003440b481c5200c1038010001e10b0902d41250040207d4140fa0f07104da5103005e08a59101100e95040c1e20b00061800c1c56005000305035003d0703032050100c42c00410032100b0782c01206e10454010f0f01942d4000301d42e074011552400c5c50001e82007180000d010109034403881e800100000c00100c801022004103800020b0540d181500c0103001359401000032a0004042c410559485501070074000c16903900c03d07070507003482c1c404d100100c071001e000031f41040721007405944151054a8280d00800c641d580300c0301410369511035a16404011001c181c40e0002132841441985010044030707840c079181100d0070b4040f4040d40c41542088010424080c05d0400310a0699200005511036200400007940303481000c004140208164400300241c140000301401b010000a1807101d031300c149080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 364382383 1250 364381133 364381151
    0x3010506180d1403031e01050a05090a3e03060a1a071a010806070e1e03010603021519051204140a020a06020607111c0c020a0e040b01031703040b0a020a090306 70
    0x4c0d16940121080c04203000d0340c80020100121031400581a15000341514446a051500308443c00400414109007540c681d00d030250807131552001c0300b071200c003001c6140f640c080134015180c69500c414040342c00441402c0c0100709299880c11039910490b564600e40302400d03000740440320402e104080001e0004000003a001262070440800705d4101c64001c82610301c00e4607442c904441002662800756030002005216100c809045e0392402c291160082c00020040c0e039990203c0e41c12600e5032101d81981e04007003981041c17006000e0310122003800720700e011450049440b80035200301c0009000500442480c0c240610b51003070400c020200190010000c020a5681d208001c0d07990108881c2c802c002182104603540036840003803003043c042c082041d2108100d8419908891714105e142c0e0a0fa401014a0700c0050340441820020f0b00403170141c13460132015811800e10007901c1802e88a02c3da00d001c41001001b01003100515120342101c1030690241c2c1d1950003003421180700326160005060203161914170 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 364383633 1250 364382383 364382423
    0x20a15080f4b01150e01051303080d0b1305060f010203070203030d150f06020d081302090a0f0204081623010807080615030106030f1103010506180d 65
    0x744140508456248180e8071014188004140185902c2c0c0d00c1000040490041424000c0e601d0710742064142c2d0340d80700d40180c00c2e00074006400e0340700c06582c018120a15110320752000035000d902c8402c0c208a0720301600114025140710a601c0302400c458804aa140b840c04510b030081039250000901d541d03d41f280d03c05008008060507241d541c45506820a441d0381d81d40088140c40026400502542c20803100b82c1c80751019120101c4004030103900103101140c0c007280b501d0414090300603580144144803601001130085003000c1c01c13035846210824140030040e60380350343d016406444030300301007240f00c508468600640101d0f00303c4a59801042d4900003051802c0c40060200e0304a003003050030992280c0c0601174141c1c560021a0f00142e00300c000198805c0c000c841a941000d00a482c4403058190403030042d505400c01c0c0c010800094031640c880340800650f00601071421180e40000f803540d45448006107852160031003019600d21218900142c039a01e42844030803468100b00c078201240204004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 364384883 1250 364383633 364383647
    0xe1501090501031104051e030d020d0201050c04051e0d0c2c0411010815100c030e03010c02100f0e100518060403080601080a0216081b0610050d020a15 66
    0x501800a80c0c851000039156100b40201d00540d04101c0080d803501c0c1c1800284006a40500c541400f00395046044000700d860070003109800360302e543d0203040b03203000f0440000c0c00e484010700035601900c001e0000703000360340c1c0340c4046140100201403001c5100007000c001c51003c03158030402408041c0c02c0c0d0400140c04c0ca40c0c00c0c40404034841d220288564201c1c0b4201000002000d407806420b940c520210144030394051004550400d407a2710040d41c18080030720000b5103191050040000103aa11140001099003200d016100c9403001c40081c407031503603e038400a644d4101880c1ca04219502d9401001034012181c0c032101c825034013481580c10800c0481c5003040641001e64001003990000790040e031000f0000702d1818010b5500d6900d1000d240c0301c09004503051200541074403086039080003950003602d201902500c0d680c2c443c0c600c0039214121410701d0100401400c9190716503820040030480031801d250096020f881d41183e410080100c180080f0756a980b1541015801055490001e200c107500901 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 364386133 1250 364384883 364384921
    0x260d091406011e0e011d040f0606031110030c020a02040c050c0102070c290f070c1511160302030616090b0309030d060b0a020615040f0c05070c0e0720070e 68
    0x120f566245640714000b00110400344070380f4a082c400405161984414003400713903081406203584140c0300c1850b850b841c08485481d881200d07505a002181180b41c1406501c0444080c92400d08100d4070f000c042c0003940301c10450000074410340d81c6200c0d61042c54010010b031148000014000c540390000c6281010b02d40000d40a0b00308040d103100c4907610300c241121450315000800c1b5581e207080c4801c1d03064941d42500038540c04c03102d82e1441c07070300440c1555020302c1850f00007500d552a85038800e6207070100d6003450451000e00303c404801c800d090025031000191550030031283d400752821303054184812a4480c9540d0040c0d110f000c070000c18807541080000c0a401101401501000301da961303000107010a02c5034120050150300f20a00080c04d508030003a83d80301014020f0070124841a09405850846420f402041c0220f100820000148a1081d00c122f020341101c11241d066030510850140582c20b025891401d02d10351508031803082442030003400e0050400c1c114242c0d5074180b1400d00009065000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 364387383 1250 364386133 364386179
    0x3110f063609160e0a090908030609010504051605031e041a060d1101030207050c0405070302040e060a08060c0d2415020d120b010e0904030309260d09140601 69
    0x41d08071045250211100d4040d162003811003039030109580c41625100e0304000501e50107100c0c6140019586000e0045502d07440c032541e04d5503503e14001b420020420010307081540100c2c034210801c485120381d09000300f43c010080c200300e80c0702d031385403c20f040d005032292055245441005041c4001c00c20348107000310307200701c2038902a009945c0d620244000031443c90809024840e1a40c504401c0c0d50003a0b006082d00350040c4280c0740010101c02c00b080640f070007075500c40f00082d40020100003408c000502d80340c00550446466416078503142d0300c1d0340e83d180c0c080c00d907603540800080c03801d08915203580b15a43d81100f00030850900100004052005c0550384a40707480740e450001844811440400c80100c103082c1d41d00d0b074007070543c0c2c4048020018980d40c0106030600400e11310003006030341c032000043d21443c482e6078085440d04080c038080c01c24006e03800100080003c80c41d0580c07619a03068080e1103e1640540000034450690b091032101e106035035003410301e0390007000000701d030441c0040020703403411070b0350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 364388489 1106 364387383 364387477
    0xc020a0f0506061905030a080906120a0204051201051e0a020708043804030615032a08120409051f06030f0501060903110f06 55
    0x30003035410758808001c00005141140f84100c0216064991021261800d00481e80e02c842d50780004080002c00701e406c009a8a42105445c3c6e201c010221000742c604002403140029032050080700e01a56900d80380400e02c1c81c05006250180d0018015800340740d040c0c80d04100d0500b000750007401d040e5000c0140b400812072480140002e000c02001c0c1e007802d0b0001e000d0721071a01003140c0243c1001c00e4400e01100d2001e01c007400740c9085903080b000c082040741c03400c0860801d0b46680d800040c0903203121414440020208941400c203603246410880760b00b6101d08400b5641c0384cc980c01403800c00002c0106020311403640d0421074005007120480800c081d180d82c6603040980781c0d0780011001030707a104503000c0480c855020b07090050015050002c480e40c20360316050028455921003501502e02d074103211490b034032002c04403005c902c9039060241e11481c00d40654005003105000110b088448 = true := by decide +kernel

theorem cover : BRFrame.Cov 364208633 364388489 := by
  have h0 := BRFrame.cov_init 364208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 364208633 ≤ n) (h2 : n < 364388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
