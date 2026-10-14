-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3611
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:10:21.173972+00:00
-- url     : https://prove2.me/submissions/c9d4c2f4-10d6-487d-9f7d-9ba088d79b5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 649280575 ≤ n < 649460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 649281825 1250 649280575 649280603
    0xc220602030c07050105090d020d020d05160329150a030c080102071103060702070e04030302090910231f17041103120304030c03080601032c0124060305060d 69
    0xd480c2c2d00b240d141c0c841c061142410108881d80540140c60031900080c00071540c001c2c1580800c0b6041c0e40c0d042007660800780c10f400c3d8501203070040c045d07402e090a4400960103c9455403800103145d100607441c4200c0d40030480e0540542c901c4040f40c1e244c01804255449010302c5510000808014080d84001c00d91540c5220000d504a011b40190600701d0017205407402c02010340c0280f548411040718800e0058000036010701c0015078401d5855041802458010f003070040301380104102400070788810705c644901ea042001011003003005000500525043e4a10191140d40490100030809810012410703455850400c014441d0b0300c00d140e5294007a001440e90b00786410710051402c00144118000d0050710f18010641044000300e038090390381070b5a41e00108005032400c80d0b00080103080c00e810903072124100321a259099004003210818015101000e0403640425400c640280c856891071540703503800307a003080c242102c032101200c10f10b081c0416140c0d81c000004900da091100c00402c5804081e80c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 649283075 1250 649281825 649281827
    0x11206080f0d0509060301050420030108060f0a0905120a0c06050a05070e01020607080a050a0906020712090501030603020901170705060310060909020702060921150a0c1103030c2206 80
    0x7100001030303000040e2881518400e4080b190f500c40c503000c56810040c01c100402c924205035010b40c04444014605500d2003400183c0034400f98000c0e4405011030340801c0a00c6036a801d004003c80e0000e80980702000001000d0740c0e0203481d424241040000c1090109042d050107001c0c201a00150b54041420051362410f48901d03001404252a070800042441003a03020039400000d0940c060341c05512011900da849013190b6014000c020440340784162a03401440c00908c450028096941c8038080c184000d10541100824025556200604050070041d040015071212450b05054071800c3c11110b03100444840c19624040055200e280c212100004222494118100580aa58150f0f40748c244440c1d03907a5525050f0f00036144040d51008003002200513a1800c401c010401c90030340c80c00440242030100445040c00505440c030610003d0850030010401d1440c80744001502c8142003c3e02501403020486641b400020703e5100f2130f407400515608143e07102e5540205003480b21660400c03141e00e90b60 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 649284325 1250 649283075 649283083
    0x10b1215010e011802030c0f040b1e0405060d0203090319091701140c0702031c05070b090303040b22080a030e16150f03021b03031006171501120608 65
    0x190103481000042520340346070301d0b40c81c102e40ea15500040c10b00c0c002c0704020001e500c0a414007621320b074100003401816100c06c02400080c6412981c240c1c88414011180c4d6000703d00003841419a881048148056919001170b02c0c07003490b40c500010f88907901c42c10702038a10302c1a090086844040802062800340d8452011388c140c410103040c82c8850350358031030500e0a0b00c005590115442514000040d0402054006405d004d0700050455100f404200079081d41c00110102010015600151060a000c181c01115802c221004011451450581c80340030ba40c0703030301400c000300c03244d0700030803e105203040042640401c5400113107455580c000c003070000d0000e00e09860115450b0103007104104131840350240c0c3c03104480c0c400031042c500e8074694208071904a600c400b0001415400c1c080c040310440d00c10250385006080d140290341d603050034841c0c110291030550000e410032552010071803070b10340c80007103142d00720b20003000200c0d41c01c100100594025039425000400c140c9014400078550394001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 649285575 1250 649284325 649284343
    0x3030e060a2c0d05072102250f0e040503070602030a0f18050a170409020706061706011d1b0309010c08010506090307030b06030109021e0316050d0f020102010b12 71
    0x1107549440410b54461400e600340c944209203000360081e00030111414020b00c01809203e01c903c0b01c00000600c0119a1300c0e001b25114171800c010382c03040300744280420400b540071004a440002d044030f1207140c51a1600300d075586000c1d040e101d15000010070100b0000300241c9040d59407020040d92a450b04c0d0080c04011b180003030319041c0c0704d41460000c54511059401080c034103a04480038017070010403500c84140040c08000c180381e100c4010000000c00314282d101401d100307131003220040760151400080703607d48290144800303090b0b048100100884005c00c1d0301080d9426490801d162940e0718070081c101030304441c44030300d0400140081000a03071941907002c410001c8054880352040e903200e406000050055400458141e40020001c3c4081034036040040d50140300140007062440c000e5000c20603000c103039507003032101c501030f403482c40110314007401380e0440003142c01c0c00413682e94540000a10310310006100644030308014080c60095903c01c2d0003a84000c0030242c05958885505420300e59035180d48 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 649286825 1250 649285575 649285601
    0x2151608060406181a030a03050304020a0905061e060708070303050f01060305150f0319030210061e03020f191203030b120616170f0702060a090b07030903030e060a 72
    0x34000c2c60a442500d081e0792142420203042e511042000f001001e041d0f1600190009480481c4401e80d42000000ca409200342c1d5000e45a00b0b191042c804050040c1d0800c03441d05080004000154070b9200c920030010f207140103a030320020300c0e200203e41e06105801c006031910000003461014541c0607003000340508580003000340540e9070f6080c11805c4a90a6a502240d2460b140d514815403800c40504010400b0050aa80310380103058100b00071401e01c070038110050303005035490303c80d4851117100d1007004001030200b91240301c14070308210000c402d050000078450a014025030000d6101ea40423000c0034688992402d560310303110700c40c0d0307000c08804010850020781820f8100d10756041c10a1500b440b124040000d260321341724640700618482c91003071a2820001002140319886407d4220301c0e019402c1d041d40d416a5040500b0000e08000d40245070881090601c0d81c1400092503083c205a885051440d0009401c40c00d4035040f000707400c0c400700001062054200748003c2d0380155100c01004504c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 649288075 1250 649286825 649286837
    0x13110f07050d0f1b0503131401260106030e0c04060306020903121216050712091a03160302090a081608190b0a1a0d03030603171315021516 61
    0x40d0b9801281e02c2440143d8800c0002c1e404090384d01d5020b041403a404030184160180c0307040c40d0300100501c1a003001640300401015010090030225600140390030381c24000c402c0b40480c00151060700454000341031049600f050b581e034244a0340c00c0070500c03070101d1100e001041845101c0c1d072800c103480030750015a000c030320174040c074060440e04286100c1180e000705c0c103c3c00000103655490007076260030b039680302840042c030804004050010b60207000b03136082090517850303455143e03040503064034001c440051a244062420000d02440c10003810303100d21041c580d4a07000da07544800c2c00202d14103508a0b404400e882c460b90703c080150b0099110041c054521010131601c6500d10b9200c04400c904650b800036181800c0c1c0400714030f8541e0550000002d070f805045c411046400c0f141d012540441c6440c000343c0c00030f44c1c2c42c1003d004108418941c5a09030141d0410f0781e04110450070f002040c000300f0303c94110350880100074040030074028800c0400d080384480d0081d900d0314240244144800121031004000340c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 649289325 1250 649288075 649288093
    0x10305011506140c0703082106010e061c1d01090b0708010b071209170f01051f050d05071a180102011407050702040b031b03010f020903060613110f0705 67
    0x1d04203600404582203960340f04a40c1190011249036540704242d0b01c6542c2c00340000c0400810132000080005070850204401d098030344440d18000100054000d07030402043e1811424a0b554440513100c0001444044404840505a40c8402049207203803008100017100b1190079503140c194032a400c1e0b01d009107207006c0c081e0703211401214041c00034041e131200da20090104501098030103400048032a418100300350080d031180f2400704c100801c0040506141c6c001419024942c00a00501d900103414400b680f030340f41642003c48aa900d001c2c00b89034018241464030100b8080200b000758001e111600040c3d01c0c100040c070031282a640a110750424080300d0418008180d44140b040b0002440c2940540c10b490b00c501008807000d45c01440c1c181e078099255150200300f035905018600c3c01070b10421a0007408802c540501d401d540c55544111040b5105100d862a5501d001c0380c080c0c0d1003001100c0d040800806461050010140759200015054010408006045441004109903801394040750070243c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 649290575 1250 649289325 649289351
    0xe010f05070e130b0607081b0106090209100201060506031f03080f090a0b09060403140c040f1517060f13120e0a0b031b0d09020603090d0e1002120f160b01030501 71
    0x30b0722070b40c01140c10140422140340890104000741108c91260325002c50031120545c0503d003900c1268214010740c51740012080003a1420850080d207180c1a4002845410f142c140011054000208169510003500c2e201d4440c0840700101c0d030002e5980b081c00142c440e2450100c0c01d030290403a04100c0e0040d800482d0200310005e040d405c1d01c428200c0200000d1405085a0320a514441c42c0c40004031203102e40e84510f00c050792a80954a1000d207000000610650ac418404412102a6000c40000005240b10500c40800400d00a0b0b01c2014854020307000d8a60f144400d10081030384a019048134140d84003e12100e80c031000c4ada000076400c42e441c40003d03481c0d0313100c401d103031006540c9802c0204030503c41e20071441a040c0a82006040aa00001c01410310340110f0a190320445a152154102040b5210413903000702d646100140f05940f421a804018240655038281844500005050100d104160803c4800454011015407400c004041c012072070310304505d43c030a000c11079665081c00315580080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 649291825 1250 649290575 649290581
    0x302130311040507210f0e03160c05040e070306020702030312040f050136031e080928081321120203030702070e060303130b04061e0e01030e010f05070e13 68
    0x8802090f121210040030003039203800400b02260500c100980790001640090f01c148040c9c083c0e81e00d072882105980e247d525100460703c42507044107210368544010180102e20001d0140182c03680500e00594501c11400041c1c03030341c025000041d1248940c10200b008000b07900040c1e0701c1552080000384944091075511030801030703440c140d1204920200305900d01c64865814002c14441c02070a00c440039000d0000301c0d40b1440c0340306040314003041c044400e10035103d504102d542d49081940e004c01e5000d4180601c02415032174035101c0030b40b80210100d04544041c203419000d000800b5210b5018520704030305400382000304013040c02a500406601d00d00b0301020b002200700c6e446010954090407996080500d5102100070151115405100070300860710f0b5602000854006000017509164039146030160040442c82c0d41d5811100d00480c85a501403103130340005a188504900742404500d442c0e000d0081401030004a6180c80d440b401e100521091a41100e0090255602550b03110b02c0079480002200603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 649293075 1250 649291825 649291847
    0x50c070e0c0f0d09021207050117160f0504080a2901152d031b020d0207090c11011410050402090a0501030c1206150f020f1b010302130311040507 64
    0x15440d4100710014024802c44010480460441c0c8001031020f46500461404412a820007803243c0c00a0340c280595a00301000000c590218644007181d0300d0b102280c007541344402d0020105100d50901e00110307007800b8005840203480c9100498814110b0740c101051407a0600c1c2e124001d08034241c11070280c003022404503034107803102500c190040034550703172007114580d0354280b0360036087c510f041c0d60b91070380c5042c035a02044000c034550380410460001c03850f9041e03807511441d4040566014040c40b890b182d401013618011260510700000b9001e00d20807003540c0540c0c440c8500c03c219440c0420707074142c150404e01c00c24001c400c0c0d4100701c54019118000d00040303100b20040194041c80c1b00d6002c00c001e600c25000100c0c40102c0c0c3c617280010302c85c0e80c480f4000303450103a0070100d0303107900c04c0c5103604c902030780401c00034a108410b10007080807600075002c468451026401c0040b94030360601003100280d02035011640c0010004490080d2540e0703a040800c1c005a500742c0e01d07403080b0b050602040301c00780b0a09469036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 649294325 1250 649293075 649293091
    0xa0921020a0308060307120503040f060507050a0201140d14010f050f030316030c051203011d0609070f050f2a0d051615020a020610050a0f1a0903030703050c070e 71
    0x3850780c00c0e601d041d03c0480700205404c1d414801c208001c2110399032100c02e03404052259005503200e41c2484400910042150800402c00000380a0b91010400c000b448641940e02801c10700344d030500481030625584624bc1401081c0381c105128044c0076031701422102d04075442000390b00c1c80d203502c44007007040444030740c040c090303040d8010b00018040010440e1481e03501403003800c1c05600240e15691703403810007481d54000f012082e004401040b6036078500d002c01d5500a005c2d407a101c2c081c80e0450010396807000c0903018004014958190010041c00f68045882500990301d4054840f0070080010042c1c0c0c0c803c0c18101c12020700c4008011000030000340c003400b206aa40c4655003010103001c01084070842401c0c00ba2102c0514252241160b03045100801d001c5525a02901f414540a40000c2420000381e02c040d01401403410100305800c2d4681c0840141c481c9100c528403800036201d800c806501560491036030500000641c50109034100c1c005280062018050300d100c0c65450904082e00c140c2240e400c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 649295575 1250 649294325 649294333
    0xc1e0a090905060d02100206040302060604110313060f24091505090a06210201031b1b1104110c10110a0e01020a17130b031311180a092102 61
    0x20240e000305412583d80a000130f0070100a0410903000180b950440c621542c1c0035801003020310040c558148012540030006803011b00c00b6420542c4800308070f100040c81c0251440560220304100902908006903201000380c0610113004a07200c00040b00e0030000d124086000403010008003400c0a00489105c00c42d00c5061014961408062042c0700d20010180d48050303507202c00c01300d030f10000e902c0d26007062401c030a09219007640600c0050215050503650f801d061513110041d05055a0003804444492200c2043c4c0c0703480b101130701d00001d80980c159101070740035050000a4a410f180d41000d4480e40061038110703450400749244090407140f5800f24041c5640080001c0501280074140313002c82c4076010b1048a0785a00076458409407101642910080001d000940140400d0800c1401c0040c0062290203481c6007043c3c204c44000143e0410011700d2881d050f60122102d60310700010700110140e41e106002c551800b0380c6104004c182443c811945004940d846088000d4050502300f51040030360010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 649296825 1250 649295575 649295579
    0xc160905090d02280c030506040302030a0e061306031109030703051b090f1f0e1005040f0209130b06040305030a020a05012009090903040b0705010e15060a030f02010c06050c1e0a09 79
    0x4416604150901902d02c0b90703170f40500000181c002c0050b640308078000e501a545410250b00000d11205240c031102e44580c0c000c4c406001c0350000031000e10115121810000b404034507140c045411801103480e00c55040c01107100000c00d12802144091001d200440103850209437441007001c02c7c101502c035503c0d8410398100040418001c021f1158001c6920f40c00304020703a558a4400364001b0040b9250710100041d0300d0200654201406000000c1081c0c003802e42c10021550003161003020007000c1d4580858949a0402c2543c03615811107001e50b07040400d9035070f10900e840001e0356074800203030216801d628060340781d132012603060f025402c820b00a443c0036207450700840810050035009044050709020421000502e841107000070000c00d44104c0c00070030603800251816041c0320000d01c0303440069025404029440e0755060b0084180c90784aa844050301030300e400100d4103082c07402c070003c12003440c0009002c4180c841e00054500000364404041c0e4600f22070000c5030042c0950306024000c00c65000381 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 649298075 1250 649296825 649296883
    0x14010906030b040f030e0904121101110a1214010803070309050609060304080c100c0f0815010f050d021207050309010c0903030e270403050c070b130b0c160905090d02 73
    0x41c008014060301d0402c1d80c03412001b0008081d494180c8086407201c100280c05c1c46c00a401805010300307100007074008c100c4001c04c14040c091750310807244540d04004d01d09035000032400c0c403a40300d03114564a40d41e8101503513844074031a0340d0300d42c4010300580c04981c01c81e100140754980134040701c18400c1c0c040c0082742191141d541e82c600c00c2d0450341c802070a07406011500c2d000c000c9644102001c02c0100d030781e18001d002682c100a45124000ba0085003004007010300d5041d42d9070002100d074181d4400b4580559541c000c1103480c0024094800755071410b200a4052194a0b68030030041c6000b0042d400003048941e001c2030054404000a201c0100421580701c02d110f464600801c0425104500c440c1c00502c1d1071244051142d8400d0458089002c60404101c00017116400c2000c4006000180701d014601610f485640a0001c2548a81965000e0001d80c1081107003080c050480181e004d101c0003c11141c0392006d2802801040b9083c0140b132203024a603400c01d074400900c08080c0e116405000c1070344001661 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 649299325 1250 649298075 649298093
    0x30a0203060a090b030a11011205040c0512060609011509181d012f040803120709050339040e1b011809020c0a0206030703050702120712030b12030406020114010906030b04 75
    0x210190520216840d0320389480e00078012b40c0c0c452840f80880c1c989160034901005600707102c04815030196800001000a5038441c0a01141980e43c600340d510440c14000c8012950401942c014801d0f46080d011000e000c11f582e03422400101080e042d00326075000010b18950b007240c10394051403400c0d131255000c1050002140321840c4050524181d003074076003038440480ca441c41e400221655012111002009000b5034800000380140c41c08a02605c43e40d201002034007a101406045110380401500b01401103058003401c058800b64050000c5c050403460040d01c0e0340f54445401d20440c000c14825566816600c2040039017200959401d40d080f096044c014000000e4000c0c0c0c0c1020b07514802d0b441070002680d114030145104007020350300070601c0d1500a4000f4113007100e00400e0510350350288040000150a000c40040c18000c0c1d242c00500803001e907000650300041c4e84034011540c000080c01080702641900140c401c00c080107840307031042c1d0b46d500c001421200940f002500302ca030100c0c04038001900c540f03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 649300575 1250 649299325 649299353
    0x804120807120216060615080a050709051e0102100b0307060c050709060f0f0b0424141c060b04031110030207020925031e0b030a0602030a0203060a090b030a 69
    0x80b82401002c001c800e0341404030380c00352803800e08a04d45a90034208120503401101c01402c0d07100008800600b070a480138200c1c2d08054284400c44d502e41c0000303050070340b203454008000d10005200166461401100f001c041c4000c020481c014043e1600421401903c0d0050801420f8098001d2180c1c4d86000021140200c004004480354000c1003000981c80d0707028080d110141443c2000c1424542c94803060002c910002e60100030441c0c0e06000c1040490780e01c800240c0e030306c0340101134803584c841c28820841e0380c07040c003446074002070307101290035807801e1210360f41403a44822101d020407182c1c1d2107407400135160250b480028005050f0240301d6000f401e00c0181421031100c0d43c1405420603043c0d80c0041c03080c0d001202c0507a80f07411038090001c01c0a00143c044070302424030323080030424000200c2040e4558105010444001c03603c078400d1000c151410004003034401d07000241151242420041d0502a50058440d5403051003c1070380031030548528400d04c8101c01d4028000e06041419540721f411004080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 649301825 1250 649300575 649300577
    0x3060138040e0618071b17040501020d080f010515091e011b080d0221041209150e100c051518190b1b07031e140d09020402090604030b160804120807 65
    0x2006100c0005100090b4100ca02907d4410080c0c645082400080c500f0590504620802c000e40003406982c04140d003c5905551080c3c40d10300c4030102c0703051416641d1003040407098001150080e24a51440444001a4410026a282a20601c80c42048004054106805442003034200101101e00f05140d00815408152410010108110900c0703001c10000072101548c94040d40681101c84c0f0b5442414a40640340c1e50000380c4103210300d00300003040c2c0b881d9034107814094040d1090b1079406138050b080b00203144c1d5100e0300305d86245040007410045c6120940d48007040325088241200d0b0319001185114080c00e401c0c400c200c1005607500c8000f003031480035000e1031005c1040b040c1494224043c000403d44580640c8401c0100302c2c1500c1d00003c84121448500100080482c1251103944484111003444035004804500c0d02401d00008009100b10082142d10800009001007081040e03944280302d1500c07a000e900000300040d40a44120380c040b0b1700101038405007500c920049000b0454140c0000113 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 649303075 1250 649301825 649301867
    0x60a0e0d14060702030304020102060f01180903020325020f0102030a021009062703231803010204051f0e04020a0e09150907171503060138040e061807 66
    0xc0320909802c164003526001c00581000042006650b01000403031307045840c8180c118020340c900783c0850042c420002a04c41c0700303920340c4080000d05108100361090601040e003005881c2a00241c004d403d00c4001500301c0c00703800036007052400c0d0360010050f5561203209030068003101c0031186048000300310748001110b00d5652103001c0242c2c002002d0811954203028503a00c40003184904001e800e004e040700071450b10b00c81a128903000141003105542c2100020b190f0510524414030009001e40125004240c00c08101c21600348904402140f4603c021b10b65128a03104048080c1444240d1040c1100d6802041d1600c0c1c4401c2c81c4c2c1058140c856110345480e40c000640700f510400504480c00a4500c8800601500220300007280d2800404c2c3d00080e000c0c0205003030061890110b5182e030380502c01c6049254250300071850002500756821f44051075101100c125a0821443c0c0318150030502802614400c004c0000d40b05040c0003507086050803412091142aa852036422500031140e411f04000c1100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 649304325 1250 649303075 649303103
    0x9010603060507030f18050705010f1b030e0909060c03010302060d0e0f030c010b06041a0c03040807120b150d060b060706180b0c12011e05060a1805060a0e0d 69
    0x101c1c0d40300e4103009074410f07500442d000e00c0c510202416a251a13600c22040079481500390000381c000900101142e0081c00d0084028405034001e541c134010724000c403119089412007032401c242d80120000080344c01120a485075848418446544d07800440e1030303230464034041005002610327084000d0803084880d40c00c081410510201c00c43c1c1854010700d18120140c0c804100254000800e0007122072524086c1c44080c01e261811008503060352100740c0c150f00314600069860440c003030900031039018003014412030342120b56030541c04030a0b00004a0031b640206254021803c075210500d400016810001d2004a0340041915904010300003004103c1c0e1000b020807921001a0300b6002d00c121140c00c00720588101c2c2407505002241c1c82c030090004800a80030007501c002c2d0b1208411039410b40d00650314030041e036040b800002c0708144081d0403459020f80c000c1443d5200c5640503107101040500403810720003403039495090110b02d0254011020114643d599001850300f0301641c2d0044941c050b14547c06051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 649305575 1250 649304325 649304333
    0x1d0703170708120603011808090904050a12020d0315030305270406081b04090210180513050a111303080313170c0f07030b070807030e010c02010209040b0f100809010603 74
    0x3030710540320300200f05154020003059240070322409641c1941c00b2002d0144000d159240401e9100d41c0c0e0071903200e5424100450305000d410040f40000d160300c400304803400596a90701a540301e2280d122840024207240c01c88c400b58040c0e00d44882140d5140e220300b414500b1001486a10200c0a806140c1450030314902d003804e60b480e8010344c00200002e0b0090301225071070302c41400e103500e05c0e682422300603410000da10006886a880c0070480005a02c1c0c00080c1800600c1d00403240c4e080c652200e030f8850071480c6440c621003010b03401a4010503c041080000200c40d02c05d150203030050100c814502803081c0390410210301120000c551080d803450b20549001c03203599071110200c5140810702a19031012841840307a4070300b0080e0b9000000240028842a40745964110840d04028024003c01c998400812102d501a801c010715031030228001b07212500120340c0090003500301c0d52503180300707605042f081c02150400c0d000c04244010f0181c10361030408210081507900c141302074540304441d940d8041c000045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 649306825 1250 649305575 649305577
    0xc09030201081612150e16050316030902180f07020a020a2706060903121e03020c0f0a060e10022104020111010501030804050114210a1514041d0703170708 68
    0x603100c3c10352454040ea044c1031810582c03c8008215008185d0302c2101a11001d400c0419279034082e4020f4000c00c0c65148145045025000e051402034014507141d1544e589250203503102d61141d41d8012400c0351580d1031200490b40e441c0c030b00b04060f4000a11035801d1100c103071817440303004002c80d04406282c910b031240d20b00041151842d07882040054240380052040001e0308805404600040c40d14040d40c01d018210300103800030034040c0794140755002840c040401d01c01d2060703001c1608900261440c000c000d051286c064040b220b0b00429900420700204440c440034801e480c0c200340c0d0030450a0761500001e010b81401507015006a0501040320000c00079102c09004841c080c61280081f15140c074a40400500031207428800c5d0104800241301c02c610f03150301c92407a0f00105001c800c86682503160216807070020300c482030341000701c000c00311b03004980c801e640d055074411240f0076102000340040714000204400c3c00c0d00c003e0512900100020000300309080040c1c020428003000c1c6904d4008250703105800c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 649308075 1250 649306825 649306841
    0xf03050a05070501050a1b0f0213141f05091008060103080c070b070b0a0b0a09020408031b060708161e080711062e031403030a0c09030201081612 64
    0x41a80a0000c46080000c103008050080000703081c1031342056000c290103007503034529110074015100c9a11600051280303070412001e804d034029040f005d00e1000c1000120260580d020048441500700002c80c040840021500300034840b0403c80302925030a28080001e1240c01402404a000c8680e01c046120401805454000d500c0703011345559030100d2118550500017258030503102d000c4248540c4010449400049901c10300d1403400164101c400c00008200c18080d80100b005984003180c04a11a4070001c020130208801c00c5014980c1c039a04807555586102c229403d03400100c0400200b1000543d224400508c1c00941c10614100c201441e1400c6495400309800030000d501c00d0706100c14244c01c49035044101c42548040c100d5850442d050b500c07510303c08000110001c0030a00408410b00b842e400c0a00a19032000d81d42d220501e501d104190340c1d80054a040c0c59040c5031480d00704503140104c10400480c1d81c10f8481d01007d9075050380e940d80c04001e02c0c03d00c0c1c0c1440585c41c802d0071200c000d0700c10244 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 649309325 1250 649308075 649308083
    0x20f070606120f150f020d02040503060a0203010f0501050a0c080d0b09090703080f09030a0611041d0912030406091704170309030606040e12161a1e060a0f03 69
    0x248425203418410151005039100140b078140800c40718001c03601c03c0903528201c0703820801401390041040307035100040c8008045803a41c1031022801400c203c607039400a000b00c86d0102c04880c19600c030071703c07284100c1c8000c0c4500c00391400040003c11965000344064000c590490800c40d203100d986440302c1d40070f980441213041545070358000c1095107251040d2121b03001030040b0f000748440c90070f640d140180b0f4400e00946d00746980c4003051041c5150303400c004003904a5801201440001d200350608240b54006000d081d8105681c030550313038150002c80d000d00748600d0002c001804141c500043c0607440b0b600c00b4100b42d807910b0b258401380010401142c640c08444001c03455407540c5520740480701401c070103a001182d010b90000c214001a55a0000d80755070800402c5800141c4c80e42c400405c41d16020413400d41100b00000800c0e030701180010608081412800b40d072074846200b10020380c16888001c00c46401e2660411036641140341c116000990364440405086500016100c0540d03914a45007548122 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 649310575 1250 649309325 649309327
    0x2010b1e15070b040602030615070c03032f01050709060c03090e060409080c1f060807030b0a1b1d0907170907081009110d0c03030c03050f0a050a032d0e10020f 70
    0x8401c60138504011803041d007022720b02c14203141d00c9545d44c406802d547e210103810480780000c031030307094180100302c496030100b1034155070801c0c0500f080030382c0039243c21070311000401d040d100c002503054060f14100c1016070f8150b031000c000600b810324000c8079210180100d90801d40e203402110004005d032005007002c441d040020031240e10705080c1a80092254852441c12900b007040804c00c4250001d843c800307482d4071000e0070003d60366aa01e41030042907420040864032600c903441020b4550403401d90b485c040389030703108001100c4004041c440310702d6041d5503002c0025011005501d0b80c0e06070451706904004148203803960039540303503203a601d820315440c1c075100c80c255680c2a441c1048800004070250043c250b41e80e00441e00d050b111100c0d10201e07444040d0a0040b80c5d80ca00301014490400c0382c58030f00f0303d000e61640360056000018a103030001c6140d0703000300745000c80300000503d80c0c0c145040a2000841e41a6103000940a0384001d400d1480308411107105004100c40c2e4001940060315410040340340107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 649311825 1250 649310575 649310581
    0xa020a0606060e400b041d0606060720030c060a091d040308070c03180308090907020f06130201030204050a060c1b0812070f0b010f0602010b1e15070b04060203 70
    0x8289a01c1112050304000c042c400002c028039450090070680302e070251382203a0013041410004001d000310b50b804a50040c078101c0070f1000b45e00100d0b50028081f1000b01141c007142d692400b4441e00b8810454050020a91800304420301c1690070030a4180e0303840a03080e070b007845c0030b0040410401d400c81c1c8506008107800020920000e861800d03107800e03200703c500d40b003142ca0410303803005805900042c09490070003060303c60042c00d25001d01d890300c0d590009200c1148116583e42408101d981201d01d801d48201203900116400620004850320440c44a101410842c1c030341e00d4401c9001456100c1c207d06140d000e000020b1503507034541c082d500500b120b40765822103040da494200801e0360715440c0e50032100f01802040c010300500052a50080750441c0c031b0507907603083c4c50a00b125880342980e00140807605003000400c41000030811a401c135400b41d0024040b0313403491410460383c88400210419403201421481d21145040f1050010000c46d841c80246480119100c10075070071801c4406596907a000024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 649313075 1250 649311825 649311829
    0x70e150408010c090f05010305180a0515070503040c06120e06010b0c0f0d0e0f040612051f0c020c041d1605010e0402070f0b090712030c050d1106010b0a020a0606060e 73
    0x1e04450f49124642041c040f82000c9081080c40014044c0740d04050ba66000075021b11544280d001640d41101d007158407560091900580e40c4001e403445480401203d0049000d1a028505a84c000e5a0002007104002d09000048030402c101c5c00c141d660080c0c075206030020000d0140702d03650181407580c5102d956400e10003001441d003803203548036104643c090f140d0306040341d9100480782040d2104031421415410b03944005006041036410480240820741034030320400200246950010841249a910141c0555201400ca848001c1481e0140c0c000c4007132000b0f90300d410f50020f2800d00313201d5240303518881e00e41d40280c134040031802c0b040d8064103440c40c24460766800008104031110125025480c201c0246d0b1844100d80c40460010800c0746c0a10104510000a0000c0d01c0a40303d140d0005000c00564103008146c00c00d02da005445038000c0703000b030380c0d40c4c00e118607000c00102d81c0d040014000b607480c207146040e140d8051102d45045014241ca0b800008249008942c01071102e0799804004010500c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 649314325 1250 649313075 649313081
    0x408070503070f0b0307050c07090618050606090a0303030b040e1f0501091b031a15071a010b0304030c0609120908010b040c120c0311120405070e0c070209070e15040801 74
    0x3c0d034901034080c40c040000100760f03011617510200c00c1c0ba05079110b5075400c070200d1500c2c030f59401864070380381018004204401c0c082c49012452486080602c655140c03042401000d104446080c0e4102f2841001840424000c1d04003005004015000041041c0c00d444180d051188005150b040202d0130020444000c1d424040d89001d840c07011410082900351000030317103a41a0040614040c151106d441c1403914400c0d4042480a03d006080b42d030050700d40406900a070391040a04032190030b40b00c0b013200290507002c07000300d040c0d8a806004a15503100d949040d02c00c141000400c0390b030592038400510005010003600103504984c0d03103d0790f80084c2010640e40c00d40300300003040b50013145001950409540e0215450f203072200385010000d401590b00c1012401342203c900307180c6400c3e6000800f00254480170328528462401582a10141c6803980c007440800b50017911038a041050901c8500050314008000b243c100c0c526003841d10303220140c5404180ca040c1c140e10124016503012908102c2d6900c280 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 649315575 1250 649314325 649314329
    0x6061502010b03071401110d03020c0709090206030a0207020a120501021314010e01030c0e0303040b040501031103010f0b09040f0513020103051810150503070806040210170a05090c0402040807050307 87
    0x80024054540b032000465510380305445108a220386081000c003260740602c01c61800076600c1015141c06038003080e0090060b61240b400c0c20898807400100040e114141e118600711240d004080364515100d014140000e90010401641e001d8400000003c026032001461944248141c0001d81c4400144c010201401241c0e40600125480448162440c0e030707000c40385200e54002420005005480c0d80300803074000900100050f090304c0700250208640d03050304050f2084850981e01404603010107803d86055000c02e1080d481c61140700c402c280251211040940031401c40604002030104510700840c00362201a9249000c0c0d1000700b020006551b0305001c2c155200617814410f4110b4451125076507544c1040c0851081d0190f5242940654503c1e282001802080024121400c0d2629010090307158402581c1c124810a04402d03030401c06805209182c40140b450540b1420716a207260718107003e000c4c0105a5160ba028070b4010002c10341e19440900003500c9a80003d041d4a8102414989080002e13 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 649316825 1250 649315575 649315577
    0x40b06040506040e06040f050106470409020703050d05070804140c100528020303190b0d0204050907090e0a020102150c0405101209030305061e030d05130b07060615 72
    0x4200c10184c00100081c080d40c1003680085500840c5006041c1680140100c0d04034541c2d0465269074010a101203035203141400350301e540750030042d0b00d5401c0c5125004e50082e10380a00d1650501041004134110b030302508a1a005e030600e107142401d500c001c801203807011568071002c9140c90060006200d411540c1800032140c00004080325400c240000700caa0a58a0340745041080001d044400750100f0b9501c040c0100100407009140324028002a450390411109599417084260520300d849140d80500e18000001626a81104240342c0a10000d0b1a00a055200500c01c0c0c4100280e0800070340300b0700d05031039881006840300640601c002401c2c0122a107561030340d20159010300181b01c20100440e4200c80044641540c4150500310a548148106100c5860140303810202c205164040e001544144003c44103c00794291001d219100300058410158041c0c0c040c0b9190340600d40500c006080c0c042e4111f90142620f669951403010380c0d8000b0760111081511800104a00f41004011125403034407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 649318075 1250 649316825 649316831
    0x80c0a02121e0d061e030c1a09060f190c03080c0c0c03070b19031406060c0a08030c070618150b01030f1805070f23040905060406150503160b0307020312040b0604050604 74
    0xa507458400035000503010310343c403200c5a40200020b91410074100e8509d0003010f0241902c42003903926050741ca8000d1030380ca0040f403030585580c0f000f00d4850000041665419200c4031000d071246407004206800c5000100f2036032042a00c0403040785e90400ca402d0007010400e00f0136544e180e100010307100700050941c8480505061006580301d0002040302c0f980c0c070003010355905072a08140c1150a180c02408400685600c80010510104450200c0106002c0b400307060300303218010481e010f0361042c400302140601810321000b1089090911908503009030401450045030f01c000100c4a041140d440921561542241d19140c0b410031400f404480018448008200200307490000320b001100c2041c1040030400c914003030196410303511a8803c4100325004001c0307a4903032500d032601d400100031683d4505202e80e112440021180350020303a0202d440140300008041034030380311107000150000b401d0801540414843d80b070310010040d00d4684142c0c0981c00e14001410070740188030444001411903802181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 649319325 1250 649318075 649318079
    0x3011a060904020f2104230604060c03110f070c06081009050901020f030a0f060b0a0e150c010c050a180b03040b0403090312050a080c0a02121e0d061e 66
    0x1880c0380036a07000500030386025907564000341d44410548a044980c000080349241c00c2107448292520440c45039104620740c401d03119071000c0211000b58082110141640004c0000300003d0030303900030b210740448500f40400d605d0300c10340f040d4107039800414940d9506d02010640e171082c4004109600b00410301400c0611445c24074418146c190003a6008080c0c0303582c2c450002c909288002d6040b100e8507066685030b5501c84c1030000d0404054100070741e20b80a02c0c0d09201020441c44031017400c82d4042d1560b910340d111084c1190040c41181600e034107900103180700902c10290411402c0c0503c2c11403d8051b96442e690b9200d540020f419081a1410618400c0001c0c100740543c1c12100d0880703030400d8106032400b8070307550b40745803ca40120050704001d01d440c0c0d802010544031504440908144442d0fa12080915940d0480b10b00c40c40c01840507080050703208229161003261031400801e0382040b10544580280501040c0041c558000000000c50300d0f40c903002005003241c5449808550501c454800c0351681c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 649320575 1250 649319325 649319329
    0x8240105030a0b181006090c03050f0105040b0307080303040602090108010b091e030123060a050f03070b0703050d0e06010f120c0614130905010911070302120a1b050c03011a 76
    0x50012500030543d0824002092010b403518000c040090150f20803502542000c421031070107070000c1e1184103001400c2c120810100e50180c018035120b29418055200e2503860641004060400c2c00b03130041d00741c00317144c0c1702041916043c0002c51207240115070169403041900001001c019050f804041d003803278203100103c0c0315a1841d5850745516100ca892039070000403000000d0040c08a50031500d042c0c64040502c8400c0c1d040c1138000b5100d02811075905d1541507941c401e005440c900840c0389907040d009050144450440c01c405000903501a192507400e00d100844282d08031140842000d60950003800100700c1c0d0b0015501c41c001503c1404100000f00c0c480c3d548841488105004450900c24442c0c038142c0305003810800c0d24018801d100300c24103030303aa80d2800348008133402c0c00340004050918403c1442e410801d403c8803042035050f4002d103000100303000200d01c103030030004108080000004000c80d41c51881940c60f0b02890081e0080c4c074400c2c50440c109821584680000640000030050400d015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 649321825 1250 649320575 649320583
    0x212010b07030e271305120913020703020c0a0b0706050a0b0102031b1009240e0a0f06060510050c0f510717040c1e0f0824010503 57
    0x14044d0348003100d03d007581c01440c0c9081000c2c241405041c96060030425610078294011404070300540030f85007400b03680c03c55540f651041c60103898001c00c0fa40e08007068042c2c26401840098041c0c03040c1c0c0c144050050024401d40840d50000006800208010013031140e28031900e0b8018020340c90420001c005440040d440c1e01403030050150800709400c0c03043c50204180308000c078000c101041042800000d00c1d01001c21a02c0e07402d01070070700342d01c140700c416899501d210310090420742c44020200c412a40c2d540c03540c41046140c04440454440c0350000302511a89040320002078103883c4c03585c40d41000700040345490303400d071043c01140d409100c0364560f6092a92080700c46200382c0f0000b42c2c5c0440c04120405480d14462601011024191041120f031141e034000140a04c005a840c3c3c002c80455081100b0424420f9802074171040307030024200000e003d507000c408107180e500e4080d08a00c580d100c001034210841c0d139004110a4000440700d080010840203a5006138002120003040342d410700c270200c0d980d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 649323075 1250 649321825 649321847
    0xf1205011422020d060c051b07060c2d080c011a06091219050109121416020102100e01060f05040917032502030909011706042901090212010b0703 64
    0x81541079040e41951600d0107520042500042c0030b00c2134484a000081c5175501202341070401031402c2000800b0001b003c103c800031500c0c2561a07207035850300d41d00ca11ba8801034060380d5088004c200c0c0b5210300483c0c1c2c1080c0c2c032694980a03084464651a403684105d09507070f00d07002003196403100e1300c41e00090340e0740c1c030002d40710f501205a9140440c9243d05249500d083c400744003000d842c1c00010400410044c054001d0a091442581c1c8040c0b620207140090303411500071030075103c0c80e131801d0054a80f0b10090548004603240140b04036111030407480c0b2a14101c4020f40002800d5075103428051141380407001140c0000c201c2a40c1c00c020981003501d50b124100d8092810040207400040400e0f501e942d0804a01c0003401940c85004c00128041000380d0b03a54003040c0d45074017034034842e40002480345c0c8035903036141c20803040b4014094130380d0b40e0f90b10044180350807000d0700107040e081819200701c070840d01806030180041040040c1d0b510039600c8034501c80030301640903020400d230030010400040d81c032200e6204 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 649324325 1250 649323075 649323121
    0x60201200901020109020402030903040501140a0801140a03080c07080606100203030a150f0b03010e0c0304110f040e071806080f070902070809090f040b09011802190f12050114 77
    0x52144900c1c00100d0160619120107076002e40084280040160040020011900b09032203444030980d00c1c8501e00598000c0c1240840401d01c2500104000b00e06000081c07035043c4020401c1e0181510f03581c40117a15040083d1610040d0701800051051020401100f50003da0032100c018107040f42e00b000a5132880000c058a605580380d070301015200000400103c0a8484104248a11510b5440f42082a0400d01c100a500c0c0e00c0319022036030700e02007003084070f000e960013402e040b450050410034441c0c0300c0c8010000756009075695000039243d95041c000003001d0b00348000e41c6082600105004000c1d0713841a0000302c00b6401912104c0c80361540062078030100d03640e05102589648050800b03866030300a00e0009504040220104501d02c00e40205040c41030344181c4c40d0001c01d4407034044003030885001c0e0030f021000017440e0010b00d01524040f18851103400c42e119904642e00d4484150384800c0c10254802440c50241d07426203810002e003805810300c1c40d000a03624000510700702440d814840f0016142d24 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 649325575 1250 649324325 649324327
    0x30a030e0f120c07090c0804110103110906030402010e0a0f03020a0519051507020d0321060b0f0f0c0109050c12060c07020d11180a0608070311010f020f0f0106060906020120 76
    0x84800d80f03043c0103a8000380b00701c040400000c0610072014104010072201200c0400e0601c80c00c070625030013072085942c0c03820740035613807400c011445e003e101c05640040d1083e0b05001842c2c403208195650341030144054240b41d01c000328910b06c0d610601102900d5500020701c154680308072011084003403581c0008442d002ca4030340159200d481c0d1400124841c1c44000307504246580c01c12810b05400c03000c1200c0d42c4407080600466100c00d52120012901c2a000780201c43e070041260320b11091074000644000700140c02c01c0e80ca051340300f048040c03c43e92070080031140742d003044034004014584980d80140d918a0100500454a01402d01610610a0500c000c0c031441000c4030b41400d010203071b103c5901d408005010b02403e040d030391100d00d401e680102c9030701d0a4682001000710705c981c80030a03420200da50148002540b8a50b80005448440121a09204500c220803c03001461402c010308440c4c042100000549641840c10082c90451541c004900351380c140f4100c02401d60034070540d218052543d290813 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 649326825 1250 649325575 649325587
    0x40b0606040f030809090a020c060106031509050a09020f190e1e090a021003020a0815030f1009120f0c02091801060810050a0c090e070201180302030a030e0f12 70
    0x169140242c0d0060401000103440c04010010390303400402603440216141726296035070980341c0c2d09902c19581c2c00091500b01d400104900c600a0308844c901440e500082807055455289040c01c894080301c440c5552074503180c92a0545c201001c0703000080e07400f6078100300c00d801d03175041c40c8c000c01c066481180c5c0028000c1001901141c43c5640c0540781c2510012445400d0404088260340c0f1440b584003030340f00340000807082e140c00d07003e44201c034500310254940a600e40d0344c498008910103030f4006056018010244105e28031074080c0010001c101599000040100917802d0851003007660304d0a120031712400202d14200c5607004002042c000342d045405d0012a81c2e80d50411105041c0d0010512480d070805c4800300741c031000451321521110200804000aa550043c6c04041c1c81e401a242000300d03014001c180041004000b442ea8000520b000114400340b5204000b2840e24275030106500517040800c6200700c6c1c540c54001d14a44034000001012140e000f00710042c0c8420002281c0460b5520000365 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 649328075 1250 649326825 649326829
    0x60306090103031110090b04021923040e0a0317160c0f020f0915040e1501171903090815090319140301032d12080a021605030a02010e0c0603040b06 65
    0x191031420a69800034416501545447d0300c5001081d20228481d42054810f210030b03040d100f620b03008031a0460039600e40b02000400101981039146002c5400c140c5400d44881c030342504010340001d1074442e50703400c0c1c486210f204620401e180c0240000c0c07001c0300700301c0303548001580c041c0501c40216080300d4807460809080c80000c01c1500c17030000f1503401580d00000c025880b030b40190703861030301c15054070148003006141c5d5440da2904000d403a8030103094042001030040680c1841c83d07980e118030340340c200c4da00619200071403941140d01c208102c0003d071a5400c02c1c0714803a81403190907032110b0303813152510042c2800c6003803c3c0c51f4015421040a0300a8081029910501c030b00d03590000791010079007440e42c0c0d503141c0c1000f02444440c4000d0744004400102008814407800c9500015940c00c01d00f040f01c0070510308000c669408001e4001f183c020b80034003403201492185040721041342d125070002e40c3c2c4d42c01c02c040040d00791040c2003082030890308500704a101a407202e0b81280d5015a1002c80d80915a0f64440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 649329325 1250 649328075 649328083
    0x9030f0818102006161b0804092a09270509010b040e1b040f0608031603083405040b0f0901030605091315380603060901030311 56
    0x10300703994402c07032900440418a8000d019000c0d04414101112400ca80507129030740e68041c151140d040081100c1d014004151003156190034013008100307900c4105441d5141c01c031041d0070942024000542e42c8000599220801c01d1800100304e1074407031020310a800080140c00001c081c070881601c04e5262414000d10fa0f007000f0b010044010a940812140c140032010320300819059407568003551400441c00c524140019a4080d1800d07900000450294100d0500020b403201f02c801d54050b6403030305004100b0100c1070000e004000e4040000d2810480d960800825080001c4d00f20300d54043d11801c0905089100c00c070804100c1003801d078000e02d818200c402140d0604c07490b4019040c0715008160510410650001000b01050176030b028070149840e4010403c6940050ba0035400403020084483d00240708500400303281c0008400c0040c40d50040c17520940c00404a8a0b40800c1d61080a600030341e8007040e00c1103030446e510680e0064114a00380c000b04180c0315040c0005000d01c180b4024060810a00b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 649330575 1250 649329325 649329367
    0x10e0a0311040b040213120611030c0f070c0f060f020d0503011802160506010b0705010e0d0c031b020a090c1d180c0f0d020702090906040b01050d03050c061005090709030f08 76
    0x440700c455507039040084101d1f991402c1140d0301e41c04d000040132021554000d0307a0159500100319490aa441d043e200001c1d031056a04551105045a001030307215030440078400109107a444c0e064a14106d01d40003420170301d111108900f44503061006020920090501c075095034815040142d5a140c0e41100350b400003601240102144601d20000c00c4400240c4c0180003540d105c1c900030300000313488038601e81c3c0703514141c1c200000080b60030700b144021a10400e10582041b0a0303544030014400300d5004102d091017036420181721581c83c1c2d2409950158000c808040010300b00f000c200e05600e07004006002003164850405140350140023140042c40480c040f80c48400c603403120a82d80ea801c0000e03607400303500201c1c000da2052072082d0024510700004500303944115442600786046a00380030401010b400b20980503010410b003030001140b1300c40c1c00c0265601a40300b01400d01e8026141c40c040102012000b4071020400c0301d100b41c00c10001e10022038040300b40b503000442c3e9440b01c81c501c44a81c8483e40070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 649331825 1250 649330575 649330597
    0x20705060a140c07180e060417070f0b150d021315080d030c080a0528060506180a06020d090b030601030b030a060501080d1b06091704090506010e0a0311040b0402 71
    0x102c0d8183d11000281030422036001d10000001c448890f20500c08413002c1740891042c0c3e030410f00009001805040c040c010081511400700c1c18a1490788444040907048181145c00a10a10500a1800441d1010310030302808403819003450f07442d54007250340d000071420000401c503141d03a0500d111804149c800e40141c02240100c0e00c12030708802d40100035005400844c0081841c0030041049000d09000310307803158442d0000c04a0002500b04005007280e00700124030741c410381e00d0501082a81d10b1600804400c01c1c02d0000c100141c04000400110320200c0d80b15000395030000015034400f9402c00008401c68000d401225101c0d512400160083c041d00038842d0391501030f80e02c80404101c4542d001e10f051300e00000490720781021560701614605c0b4426403004951410201c40800142c0540042a03030900c10409080c0e8004072003c80d0900c1c1c0c200d40c0180d181f01f921a03081040c1c0d540e00c081c408610f0042100c0e54442246961a102c200384e081c01c440c0d5011310348905810802e500c076501121184806 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 649333075 1250 649331825 649331827
    0x8160b0903130906060534210207051c021503040501050f010f080c0d0f0c080307030f03110901110703080307021f0605011b0f0b0f0f0a0c020705060a14 67
    0x80341200c90388a5010007070003040101021400700e0720b180b1511648080c2c070313085e807102454140c00c000d01c04000128004614a00380a1000e084080c04a2101512070301d441400c038410aa01e02090308840d144101400307404550006c20104041e9542103015a00301c2098801005401d0302400417861080e05405d0007404e00400000344002c21505600540c4034149030070341004666210125901030500600c030385615030380202c90b000b80c1032030a03296180840c4c1c80341040802070640340d900d50035003841e00d41c0702d42143c3d003000c0340080078140c11009445082407280380c104002100c500001042e4012880c02c107040089460003019101402c1007102c01031070700840816128984008000e6540c0804c030b00c41041c550307000401446210060003440300f5600305031240c9450080741c400819002d807803400140c6103040c11991034408228092201400340585080d1062103151001a03100390060140416000924204543c010303181e01280c0c04040d100120707265903a9056420b41180c40200001d004c200c071440c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 649334325 1250 649333075 649333081
    0x3f0304150c120801060e13020d05041109010f0605070f05100e010605040b01090b040611070f0303030c170f01050609040f050a0903020d1e030b04020d0f0b120d090308160b 75
    0x140203080040c070303580301d00121a031003261070004603a01042172040a0101d55188021013880c60411651042d01010690041c20310080003000c109540701076405032013221070784a61006030306203031f00707031b60b024080d580900e030141072a00900412601c10800060300d080c4c0b6075030740b07182000414401001c00e481c0b8180144000e101c101e00050013004644901031199103407a20f80d62065000d0074020044840400383da50405203048000d81c4d9000c0030020110103806541808115003004240c820f01442c041c1d0342c0040c840c1d10581015011690603411050240404410020507010103800d907030542d001070359403e840313504a00204000e004004241c51645084c4030801a404000b5801960b16901030348c03c030b52101d02c1912040c3c48140309010003000c010048050740e181d50f80280c100c44c8500c070018000520b8100d24203209001c50f0950148007540700e4a407450b00030715107405aa4617881c0d40202e0003a2002034080100502071010310b00c001858100c0101d07224000d400806000004641c0140c11118a85 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 649335575 1250 649334325 649334327
    0xe01030915140a0617060a0c09031211010b0a05030a11030c150306090a0b0a03060b010c06020304111216030312060e181b1804150612023f030415 64
    0x4008481c0c280c9818600030f00010700851242500c0017840d40c0c40040c081648420841e0780c0a070004001c0d10041c400e1074400000012248d0078110440c01407691444c50098450300b403d825100041c0101d445003681190a20070740d98045184c1503c0c960102084002c00388440c00700e800c00b500306a48540c01031101000c030f5880401000250f105010454007161540e481207410400c4844140e240343d00170314503001c148001041540700b80d4115a05060189854206650380c205036801107900b10b40082e4080103145060038000d034580110390301741d4041c2509150f084602050040d052002a08000404400c000c0440703079a80b04034050b1221841240c0c40381b80040445104409480c80c080f10751042901003c2650401c03240b19003080801010840d004c8022040c0c0414030101800988414510032600f110684091050a0040000d440383e615040340500400c51009150b585604c103081c2605000403061400060907040c00031080030112482d090058640d2a500960300a240511410b041025402b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 649336825 1250 649335575 649335611
    0xa060f0602010c110703110d0303020706150e060a060f12060f03030221090604050f27090c010311031f0306051f090207210203070501151e060e01030915 67
    0x51035041c4c4803400b410b41c805550135900d100b18800503010360360109440c8602d1030030a0f03c840304207001c0d00c0e0142c1004a40c2e21480100c03141030740740d03205031b0349024020003041500103245540013604440110070686842000303442d03c51018000700802004d600203e10103070003030b8440400b9141140001080a032030b4600030b50741d9680101c1d0741c8c0003e00c040e25816000e0a1031812a07280700005048a42014075040601241c4401e00c0e140541c04040e140301d5924001407501d4820f0803500b03802d40050a070a2070060241416040c01100d81058200049402202c10b0102220703001480d414104420704500f070194008551507402c01840642460103218440325420031441e034016420700540b44440d5150780e1242248254403008092441400d0014004810500c044039401e4a0b401502d00d058816070b41c45003150852200030141201c10201413144516001503d882040380c02c9946041a040040143c1280c3e440d9003030904254031050400204030154907254407252075000280903180000342c1111003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 649338075 1250 649336825 649336841
    0x608101d0f103b0103030f0305061305040c0e0601260c070206040b0c01050604090b040b150a08150717040b0408130b070201020c04020a050403020d0602040308030c0d0c23030a060f060201 82
    0x44544080190108032041c0c02c3c40c83c12660b054490071261414284240c0141c440104016441302441722203940000460003a14444d070302c82d10740c00384100e08104d0051180c10340501281d04000709041100b01100c00e41001130200c540c0d405d0b411165039104241010710b03105075230b002174029001003000520385030000041c08405500070000d11070340e503550040c041103801c00ea030054102c1084102007000700303020301d120340d0b007181560103948086001d20011403031075042e0f039011144c03503030000000801c5403c401e10410340040c41c13481d011001020180d07054480c9030010b00007074065680113010804101400080354142000e40b00c188000d65683d0190300029000024280c5c094058628403054070301d49442103400c0c0f502039843e4242001d00715000c1c00500000d1900449445508100c04000b19044901951203186409540744c3e441d49100c02410507181c80003243c03420321240034030b40511042000030450440011010068581d42e804500c04c3c060030240c1d01c42c2c10655441003020542950642024034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 649339325 1250 649338075 649338149
    0x1103010c020a0506251125030323190c02030d030501330e06040306050901020702011103040308181306060f1d09042603010608101d0f10 60
    0x159072440604140e11400090b907402c0b01d00201c40041e22a406100440100c0280c00216081410301f40100245d65000308001e50340c440e8a42030800c20141c0c00001030074002d00002089109408203540005280201d44d201c05064542c1c01c12400308034821420741d0aa46e03001011206e01c40c0c2201c00140c0108400e00070701711110400030131003501e083d20f003c4411010564603c514840c0003401800c07642c0070712060546030300c01b20800c0004042081070240e81d00421440d800165903030203d01c00500949405080e5030850f810502c007c002040904060b10403600c0d96590300d00034140c142e0001441088100200e08a40c0d1500f5808a8815440b241c14411005d41703880f14880d4204c0c900042c0310b4061031702c9406500800c004000380005516003104111031b01b480c85140d8a45c061031071411801d8000340c000c0c0000640f0302c0104580d070142080c10800400d140e49007000010b0307012440030030700c0384001c0c0051805c1d50402c1c0072841040740a9001d4000b000703009481c0d1104807880500c110610141c0907954 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 649340575 1250 649339325 649339333
    0x12010303030c020f0c0103110c030301030b01051009060801050603070e040c0e0910030506010b0c1c020f100e033f1006090e13031211070215090604121103010c020a05 73
    0x140000c1c000203041c4e900b2103141c0c2c0280030f100e440c5001180500000034841082c40414030081d00c0d00d0704104090f5010754800c1c0d002000c151b051405000000d10313241c0084c1c04009484c0010030031903420407602ca06540041c0d551a60f02c0d83d0b01c81054801c01d4403d5040394019140451441302039070300c0b22040c140404101d0346940380342c031240c02544030801207020103001034005500421003a07550f0300040a40d010000c050760000d815801e0030000350b420007070080c070158102850800b040c0400340400e91044100490404c098004e00304100c0d038902074020f80c00080500a44a1514642d1004aa0700a221031049503403000e03503001c014602c0340c01e0541d03003100b90310009280070034030a000d40d00900c203640840d001c00c0381c10354031003c843c81000580c40341030b014400c3c8183c0c40309514215000b010a00c2001114003591199203105101220600c0002d0100032142840b4102080d51190b0490b0b00722041c1684480c401400c9003811002000c031046016030541c40d1000c011141c42e004500049245c0c042ea0a417 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 649341825 1250 649340575 649340591
    0x7050a030e0909280209100e0109060f0b09240702011106011a1c05010b1c0515010c02041b0305040c1a190c0209070306081006050a050d080d021201030303 68
    0x1002c0e0441c015076140d40e89030407036008803030342200d9101382c014080002019288055611340114241e040c082ea00d0340b40c807860300b6500784880034480c0280c038014500203504000300d610303024158050607018005e1880c44078000510034206d45d41d8200d000b0114185100c9482e0080000c0340402c416030000e90100e000c914641420b103059000441d01504031050103d22191003958041e107480300740d02920b140105c000b03007032400380d400c0002441010301800201151a5546035904030807203d40c0c02035a41202014103010810019142e01074007115000428200000c040b821480000c000d03280c2084102da500000180304000307150f240e080f80740218010228440040c3c0c68210310700801d81b100f9185419004104104162030005c8d41d5414200c80c0503143c121002c0321144c6c000b03268080e090b10110002030700c0340e1060044030020b000c16020f00b021048200406840e0202003181c04070940b2405108080c4544000c0900080b0005c4840e030101d03485046550380d9843c024002c0312407007800190006840c241079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 649343075 1250 649341825 649341829
    0x306120a02061926071407030c03081305030c0307060b0303040320043909050904060c020c1003060e06010c1e0c1a0405030c01020c01080f060409020607050a030e 71
    0x142821403034001c2c050910380420002031550028400f0324240804c22800000400001110690301c00c20544e01c80003240e0381170552000304250b140122180e4208020084580040c0d001144d8107a41ca40c10700704240c05503544c0e400e010282176915400303006400000340754814000c1c044010207489105203c1002454038540c14503540b40103600000300021040a8601c1250703040251250080d640104041032003c4948010030071200890300c1c42001d8404203031540301d030004c103040d002e002e00d01da0300e44a0805480e000002c0c1c1c65000140c000762015540383c00e40e1030700901c2440800981300000d800004481107610009004100130301c51070040440000200b5042c0d03101c0c0c85240c500c40d40000c1e103103400b8074002901440c02840200f0071a80c0c03078614100050703002c504d1510108450510110943c54a2600042c5030410303d0182525045400219080c1c200d40e8018290719000b40050384888403641d101d00c00b28004114030038000c0c2d4440b40c0840d41e42e0412030001914003c00c1d12a64401003104d0306035003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 649344325 1250 649343075 649343083
    0x10501051201140a020c0a02040e03070c09020c030702011b050d0807260a0213080709060504060b09100c050a0c0306061806030210110a2909030909060d080c060a02030612 75
    0xf0708019048150100d60b42031920b40242c02c0d00c00c038035030a0303480400c40b984c0010300301d0705a0f60103410590804180c18090044511202d4001c0c000700605615002440190640f0b80c82112802030501051000e810046240c04a86548680d44101215400c90384590050007800e0308982040c00070388070820101003c00b10303801c800c4042041c44041c2005440b501c0200c8041e40049450856142d03042000160250007000201c0040010302c1000960b18148801d010641d07141d5008009540d808208041d000d8840c0b0307403007640c0200c051401c0403002900785412424658428000381c900b520840c0003200b4040150f1006084400000781809030403c11480b003000d440b202e00c03000e07500c98412513819140c50b0141c1d02c80081742c14403d060707404c111260380c0c0300101d120f18230444440000381480380c03860510071420300b50340010840340210b082ca0106800a0f001c800014540f40c006d90400302240c040044080580e170000307210310300303035241858484803980c001c3d00115089032059180b095060f440c00400b00e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 649345575 1250 649344325 649344341
    0x9050d030b101b050d0e0f0306060303070311070b070b0f0a090c0308030702030f04290301030c09020d0e010c020105040201230d0b0303091002010e0105280b130c02010501051201 78
    0x19001c000d02440321407050b1441003c1c1c40c0f00042c800781e840304600000707806000d40c2032500f9190312034400740a070071000d0061440f85440594000d900400c00d0101c0c5a60000682d0307002c030780c5480c2c080d01c0c0440141d0482c0c00e045027580000e107018000300e40202002801c0750986d11980040c45006519500c1494040540365103a1014001c0ca81900341807001c141010010b5910420b2801100e01d01203800c00b400704154010740c03000183c0102d5810042611070806091512601e40741c505605550454a401115243d184503c104880e130001d604448190180c1000340c0d03c0c82d500000308200e149240010340030b4001103d040340040c17400408900c001c4050704000440d0b1948042240c14038103040041c0006214074202c1079807500c1706205080880e03541c5401c00d412803030950b0000c5015080f14944038252403000d0300e550300c14003110007071003544c0f80c004d9044c42062500c202d001c9490452680818030340313076041100d0144103003007460881c122030301500007604a41040d500d03101350381c42030000d00c3e08880d494 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 649346825 1250 649345575 649345579
    0x40b0c120411010302091c120306051003180605010b130803031303120e032205010c200a030804080307110402090a05150d05040c0501032d090318060309050d030b 71
    0x6401003030201d00c00402c14260307000c06060040ca045042d100061840602c0b00342041c0d0400d181d003c60701044400300800180c1d10440c101844014140400a11903641444045040654407031003152101514404c0795402600101e003001107503122144075003e80d2254240403140c9059010000c0c000000000712845101d03440941c40c03010b1000d5504864004810401c1844580c0310bc45c00800441c2c14801880b40e4190002035031080c810703030a401c0b4000c04040d846207050080241014021443c50346050100c500d903000c5001250107a000001c2d1115442e4001500305040400c0105200d20004000c01e225401a15000d054400348003c20040e4428a02c0d11074001885103401c10041c100942c034804940380c880c40c184d06101180d03101c3c4080743d01c22241070b00c142d4003148080115507018415030311b15064003016403840d2008803103c00e140c02c3e24144c1ca808266652080202030521888101d10411141e821882c0341c1c598440300200a4801d0440607179040c0120000c02c54924000d1043c1d403091500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 649348075 1250 649346825 649346857
    0x210e0114030c0c0f0111091908030301090f1d031b0109150203060a1509030309050d0c03030f0210020d0506090c1305041e0c091811041202040b0d0b040b0c 68
    0x103210095056422428804203c1e120f01800248111028020f1013503000041e800b0341e40351030304401000b00b804040030981c415100c0c081d03000d0082c240d011048905407003042c400030a41c00900c080e4030009000b0315500017405140360a0100d00d40300c007c4006c100808040380700b40030751085414413030700702c0d0010800101104407802c240450114180c004c0d56002c00010524080315a481552004584500088000195001e4802d004141e080b01d601c2c4041d010548003001500d005507607290380c04409000103000d000d864444001840d00c2004010044015800306544501c0740204034000707014282c4e649403003580c190b00003c0d00001d0200a031b400c0e2180519001654514103030a1000400102d03208413076503070060030b4000c0041b00c10700a01d0031601c007550b9085020380c0340941d0500241c001c2002180002d0400600200c1d400b02401074500b40c8000d503104000301103140c40010001c1413074201c41600601d10405035010b00010499091085010700d0380800c030359035200045606840b982282030700d0111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 649349325 1250 649348075 649348081
    0xe0c040305011a03370503041206090b070503090d0c0507150809010506010f09140a0b1209010b0f010e04050619060207080f0c09190b030f07031b21060603210e011403 73
    0xb11540c171240ba500800603240b4080c3c682105040d000461002541c000341c552800f80b00300000420102c2c1d10040a14040d41541010601140c0b580750952403075042152181c0c045040c02010b000300c00050040c2c000c8850541075a290103003c4110495580d6295480c2200144440d4000c0899000c092410341c0c92940403802c4c10f0010a0b0000d41c10682e0b034024056040c082a10340e0003000600d90b90a901e1703000507462512446c0380b425070701c940400300d001c4e414100750210182d0700000c1542580c80c045802080550300c80001c181d014030700f0084048030341e04c8540001b85454001c0707000c000ba102c230801500e00350240d10048a07901d841d0300802035005000c032000100900520351003800003440c1440003142d2102160001380c6000709440c984400c41c0c00a240030401c016050750304401001d07030038440b65001791406030b610900c0b15803003d400c100388441c007000c5020481254043c001465006005210070049124104401400e0100300000301e194030090604941c0210a070210700c2c507401e030f036183c5155 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 649350575 1250 649349325 649349413
    0x17070b07030905030a08071401090b0109020a0c2a0f0b3103080d0605010c0521070c03061a01020f0d050f040503070b0d05010e040b010e0c040305011a03 67
    0x180c06000c040d030800200120110f220b503801d000d81401107000f8855240c80b040e0a0400e02d00e01c001c9060201042c1c0c1c903002c80c42000030707200325100341110300076600140c4544100710240d030400740010000308101414818441101204090159440d1002041002c0142c4600d004400301c8100d00a8a800800a00141e0740513052034450b491425248990039040b04003030441542c1411103504210f8284502048007070406119104e2000206024a4151101c0e0000e4071116190301072480b0010380e011034241c64030705240c030b2001210301d001d9000b03a8400c09240e490070004010a11080c01d18070501c0c01e0962120741d5880003400d14220411007025103908484010103881c0c2e548224000050310401780700015160b1380900c5070030700902c280c100c1c080e40c686000b4602009c03204c05030442d400e07004d02d20062001080f03403170b045681980c00106000043e03441d5401145d0705401941c5c030060682d824170140c40d5400d0004035105641582c168202c0da5406400c4c81c0f10a202c0072019081c015080e01000215081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 649351825 1250 649350575 649350577
    0xb030318040506040e03120a05070f12020901020a0b01240f050d0905100f0b0418150c03151401110f1908071b150f0e09090f030315040617070b 63
    0x60402000005c803159804802c604540000485100c0f45801000b0018a21907034001d035580031001e403600385100c43c09240d000c1c1841e5901e180e4414503590104000490fa4001c002e080c007407a030050000c043c19a074130001c0892011500d048006151401c9408084550140082d000901502d4503046c2c200655611407500a018620f400e582c244905001244010050300c00c1e503030503075218038011603403c0c11807003440103a0b10a035250b08050702c580d155a1000c15181001c16264030034a8801188940c0b5092048000e081401c1c02d5413900c00d0740d050000340c5c02c02c001c0401070b14200300380c852480d450407840300c2a07200d51500e000800305421001c1c00340540880c91003465422442248103c1c20800c440e152404894a030f080032404c043c45040043c401c001000901fa9940c00c4646070074900c42140346801051002c18172500703400b800314540850320403e0f0510030602c4000d4240112078a078a095141c224010b100c0800c101c0c0203901d03012010034006500c08114401403485001829041d1501707140d117940d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 649353075 1250 649351825 649351831
    0x303031e1306022208120a0807030207080d090317090d030903180603150b030408040b030c0c0105070f090902040b0901081e090c010f050306030a03030c17010b030108010b0303180405 80
    0x60031144009100103400c5102510500c80800c09002d11022501903041304050b094008840a85c000355403c0a98907008044a010303c4040c81c000c0010b48a02c2c000f540031b030260f000300074000031011030540c00700c0510394030004a003806a0f0301e80d41c05180d1704030190ba91810035100b120740e6411200707103210107074046d03040301409a100c0d00e0003428045400070049220415500964000ba41b6400c1c1c0050045024010201808804051614505065803608100d1140b0f200d002a20030010000075540306074801614144454200207224610700000002c2440d801c8152403408603401a40220305c489489c400d80d020b80d242d00941d0b51602c0644801914221401000c0380781d110850040407800681c94030a080c0129145001803414014400006d081a83c01602e8102000800e00400200e40d900242c0c140903e0b0b0903040002e40481d10000807148103035207059088050762050000a02007440500440c12288440000c1201008907410584c8078411079448807041c02d40c007003103681c003032400d6840f440d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 649354325 1250 649353075 649353091
    0x90216170f0d020901091d01030209040213020a02010c0f09050337030519030903022104080d020a02120f030a030b040f050a0209010801240518090c0a0207050303031e 73
    0x810699000540380c0c2640c002e41044000d1500826075101a50704040d240d4050a90540030990108450396000c4031a9030501c80a841350041801040540d00c2da040304c1c00032100700403030955403018207950184c06000300034035103000900740d4480e01003010700c01c40b030400a03501c1c010007825103904c2900311190192150322506076080055001d0081c85410082800720840c031076241e980e2610321203c081400200e03042c0c0a041030500349803503c800254007080000b502800703948400c0b440d50004c080c1800500880c1c1200b501031181c03a10352125a41c000480e041b000d40708440600c0848455202180c446410f54001100c1754420b000d500001400383e08080c8804201034000105400d221020205803074054821104445d40040d054034907580c841425405000d069443c1030188140407804410564002802800c214020483d546035403c0084051112007000345078904a0800a80300296a8059040807000d841019030019050402005982c4603c420045000c0020b8100158001c1103800415142e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 649355575 1250 649354325 649354327
    0xb07120f050a02070623041e090204030c03061a04061d090d090510020312070302030406050a0902010212070c15020303061306050d030e1309060e1608100b0117040b1009021617 77
    0x801b4141154090801044a4210010710f1200c3c0e00502880b503032260004043d56004020900110706c0d0029900100c0783d000f10b00040500c8512100040001c00d200d009600c181001070000741e040c55004104800000c0c92074100550f12003048841d07454084000c11404201203090070009490404608110002e0900580f480c1078100d032141501c0c0182140d20070b020a901100380700601125106069206001c14010070581d180390b0000303940c481d801c446143c2044400580c01c8200991180f0f114010050424070542080d0659030203522034008881250140c484008a02552440c0d40200c0c821980041c01c01400c014443e00c0866003060820201c9400c810413100c0304030000b40920806110b11f004108c0054100c01000c0c0d20350400c003503400401d00c00c82c040b840074017102da80421240210301600380700042c112524001030750b00218144c0040c4400f00d03002c0400041c0240990443c3c4125550030704901e00c2034850404d5022400741402075031405115594640000d110810102c610a132940105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 649356825 1250 649355575 649355627
    0x90608161509080d0305011401020a030804150f02030406020409050903030f060105030417190906030b1302090307030209040b070f0807050910020106080a0f0b060108130b100b07120f050a020706 85
    0x1082c9001504000800040e961311b0042101204c0c140e5001106603091003d440c2140454070002c00d5040b001c0d10141c40104118503902a54100e41c0c0030b0401c004058030155221310f464140a0001d41041c41011a4a410f050000742d481002008807481800300120104150b00d40307100455264200500844401c1c0110031100402d40314076007d040018201401958030300040c2c01c000380701702c0c402e41c8103000340b6003441c0c03060786151340302e52542c8a4011201c0e4016241c1090f44006440e1404039400a0340048900c030520003403040034240c480c07003194103840315210f07c0d407142021500342000f1112240040c005005100c2d0340d160103d44a50304045510002c90705940321000241480b04203030b400c44441902c5120481048051000c0944c88042401d007403103d80360410b03200b00c1054041b00010000d210750000112a808181c00100241043c40c240c141c84080c00d142003140d01113055041800b0442a064048400d4401c100300ca60482030303a4082c181540c82e160301617507a00b036a0f01040000748408030072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 649358075 1250 649356825 649356839
    0x10050c0606010c021011012c10150e09030f0d090c1e0909020d0c030302071d07050405011206170a02040e03040f030f0312020d0e010b0901080c01050705010b190608090109080a050304020f0d060501090608161509 92
    0x9032000300e42115000980040c0d610f052441c0511c16408210ad08d6140c02505004180f40c1483c04119010a0701c00702e404900b910000c0c3c00c400306614000c1189000120210603d41e0024001d007c2e03a0a440d001041030702c41c400ca085010800b01c4507500040c00801c000d200719442000b4888030400c1e803600200742e19841e05e00c490b00c0e0700d0509410820030307445550080d055281c14010300c1c85c1424138601541c0b0b020b0070804c241c00e000010f4040908099203003d440010940b159070070988001c00180110345030400351101e400680705511f0390304101c2d8200128032069203440054036040300c500000801c40901c00c00c00560386c40e08a220251040c0d5603962408125840307240c04c0300758203c4020300086085080c0100504803040c0030f0704880d0b6a130324050f403c03000100c00004541e18113209080894072030b695803001a043c800c413030710181c1d00110081c4692003000300030b0300324038144c0e0000d103000c0c02515128102a40d0780c1c62200d9070340100b124142400c100c0c00b02e110054802c1c802d00b92500044558803084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 649359325 1250 649358075 649358077
    0x703140d050a0209030c0a150507020118260313031b12050312010807030b010320030f0a140c2d10050c0606010c021011012c10150e09030f 61
    0x79040b40180d07000501da9145260611070380c128401c00310382d804949401e0580990150a4401e44038041c400002954002d580c000c26410028a1113040f400900541f111010703460030320549400c081100500f45070402125000c802e90300c41c440010030314004a031868503201c640100c141c1c2e6030300c180001d04801003541d002e415012100c0307038010f50045541341010a046000303440c050340812410b40046100307100040d03a03801882e0440f6001980c00c0100c4170704d02c1c5e1300c4032807511101d00c141e4503106000c0c102807017500108002c0305060003000010075035014030701c116031500002403171f16030312050050a541074070342c040580800c8011140d58241b001031010000c81d05440364030303c0c0040400c8001c12132f0040c800b0b00304000d55010000f86132100490001d940882c0c60740d500d588480040c05800a1043d0704520300354040b21601d480021990300045520741c070800d801401e400e891501c0d00408503514043c2c94603020700070342c03200e00c07441c0080e42918242d03050740c81074070180c96260580010030002880d062404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 649360575 1250 649359325 649359331
    0x26060f0a0806010e010512070b0a03021207200601050607030309050f0a0804030506103512040303080a020a0c1509020618010809010c020d0c08370309080703140d05 72
    0x9401081c1e40c3d4103124011381c030084140c0c0203520035800e0100000e8201c0d408500c079421a4011503c3d00d80351150300c0c02c198040e00a0500000703c0c03612040030010400d50000500078410112801741014030a800352068a5000c01d01031513400c82401c2008400191007507004404080c090002e0782e03015506180103c0c180500341c842502d08407400304091062007818007605400210442e507120501c0d03c0d10704c148a05640341070f4944407080200c0c403624422000e543c008500d160b00c54050310415002603148900a0f0014013083d000111003100180c1035640501c02c4940c41000c0d030311001d004480c169105d0014540c1c510070a54240d4036064503900503204e0b0381c003500e10012040d101001d8050901d000600c8580c0c000d20003119a130400a200143e940c01098070308480300c0500d400b0460034654146044548601411510002c0010794110301d00c400b0074024036840c00d9034029280b010980e403402101030f80c000070030280165101300448400280504002d0b60851604800c00e410040403541301001c40e1012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 649361825 1250 649360575 649360589
    0x106063f050105130911010c0f020a0603150509190e030f0d060510030513021306120503030604050702160b1b161a0715051e2526060f0a 60
    0x10001840140b900614020114100c11030810170308519480303000e04118848040360520400203220f40034070000403c00e00c003060300030307040b07110170f560f249030050051120004200d05130a03031440108075031030440090382c025040075803008a41c4181c00c00c503500030503240c04001001d00c8100035049440d544580034000d040091900025600d103000c040c0107001032200400010036181600300503400b4507a2014000c0c1320b4055030007107401c00303804019500520307640d0040d4222500550341d003800c1040c00001988070b2030064601344a103031500b0801340d0f070305c40060841c0802d90101c00411300c0001e0440000e017418456080003041d2a0f285540302c0360400000d0f00b034007041001c200006000324242902c0c80070a0369400350082d46441c1064803000d8145100220884616440e1004964a41402e0303846245a1111250350484c4d030401c04000e00b0034a501100811030100488403504107540502c009800c98290000e9442d070b2452200300394410240c000b4030301d03680140e01c1514422191240821075001d0010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 649363075 1250 649361825 649361831
    0x821010609032303160c0b04030807061a030a030c050c06040e070305091b0d020f18040c061701030b0403120e0d110304060905060f1909060f020106063f 67
    0x1541401080744140810f014000e80e42d0825024000718008104c0d44203540208140408014034600034902e00388551020282200125010060110000051242c1403040d0801c2041e160480c16204d0076800320110242d01d600086100e5010a001e074480c1d9040d02c0c032410a40ba0302c06070403400075620741c00540260800650045c10002407070303054030a15820218881c000c0c4500c0c04140c0064030031240b220b140d24014040e9412450071034580040c840c01c3d40c4001042010f082055488070241c03050214bc0a07200030040400000d2404d01480c6580704030030a030a034999641c1e081da12043d50440c4040d104030100018100401d04543c80c5204585c000344004000c0c0540c0482e1050003420300514603c60061900300b000108500c13034001d11498210345096443e00d444140009040c041405415214110301c801600c15000956001c420842510102d40740c4044002c15180100c0c00c9486070b00a19001c01c2c96400440d0010010042182c01e00c1200307140d50300e000303650f050032019003141c03040e2070910f41d03031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 649364325 1250 649363075 649363079
    0x50106150c0210140904200d09020907080103020904060c0c060516091a040312020a060e01050f070315060813020a1d1f090b0a0314060601030f09020d0821010609 71
    0x74000f08103283c0192540303044141d0031040050100e440c0b0a841449100741d80c2ca569442907140d0481c400c0c9800950020420b860f01161720038000076081d030384400c074071038091007000981c0940501c07543c5041c2c13030f000350410819903105c1e59020f00511801d01c0100900211500c818001811405424880c60f40c1c0d403442001030344007400181503aa903c0c0c0040c1d411160001039400c100c19058103903805c4942100d806000000e8551040c1c0c1050105030000d4060b40c10002c000003400c0054100e0741c0a2486500140300603514580b0840450b003540e00d201803061586182080f81c01c1c4030746810307600b000c020140004481e8450b0700140d13459a01ea8440502100d139550084140c8034142441503001c14480c40a194083c9905030420200720640100545240e903108411250b8961120090146a01c044a81e09041c94003110503a5100308035600c6d80003038100744102540000d2400b590102641c090060301c01210b032a512078000303070000c03801c1104108591907698a120360707044a0500a15803516080d003214 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 649365575 1250 649364325 649364329
    0x706090b0a060504050a02040302090a05131b0f0608042303090402040f030512031003170708030901020c01050109060503070302210601060f03050c03010e0402061308030a12180b070804050106150c02 87
    0x7445c020542ca5106105101c20400740c1c8603400000c0c2d2103184194005621b0755040c0d13481e0a52004420017404000f80504440f6a84d940b0390918000c0d145020300d00c42c070040d66100201c880e02803c8900505078241180c088d04806450b5011f00038180b080030589081c40d10000c045001c98005600620801030b25040030030a000c2c0c03d0007846165800c5440c22840d520302140030440d040764900c00105200a511403004a040811064401c104c0d0300510707040e500c4c24041c2d1080e0103504164040c0026510744400007684d4501841910100e81c0d01401510781d2a1454003001019207550710300099150350711340810329410062280d02d020f00140d031102401c01d1f02580b0000c0450384020680548810308100520240e02d03044419a4080d90440d0090303514512001290013a08065021455900c8041100414550040c08122200e40180020000d500d1481c0b8220000a1013540c0900348043c1e8402003401c05105180711640140200008101c5546d03070035a094481020f90503000004601c1d0103100218 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 649366825 1250 649365575 649365581
    0xa200d0e010809060402090f07030f0f020c011518020c01020405040c0201090314070b0f040212010c0e01110120071b03050304050f0402340b0115170f0c0706090b0a060504 75
    0x3503d45004203ca481c140c1c0c049400920003a025007000c032514400510b02602c00d030407161070240c41c10024081d041c02c1400c0d0401a41100d1a050300c25400c10000c44045030703410088808480703d40c094480400310000300074000394040d0032850b603555000c003c0402e041d2142d006115000241c2d17400000c1e55000b40c10010000c200c14100da8012100400805004c0351901201e00d03000401e00110280e540c4640c800030b44551507401e030310241c55081201d112445a080709041d28441c4003030300c481c18401c0441c1c07010340c200c680080e06d4200040c0311681c101888840c44000c0c01c6003a00c01d500c60389048000c4440c2d041c003a08941d00c100c65650000a040c0810f040011001064900c259019801c0002101045c1c100e0303011303034100b402100840100c0c81c01c6092046110b1075101e03040200468a0b5031140ba258420b0010141c0320004a40400d0509071780e1045107070854400d814003840f8501a4072410f4001a0303a034080755060700e4654689445501040d0f44052a6009540710040012800e2410041c03200b0307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 649368075 1250 649366825 649366831
    0xa0c0803060f092409090d05030712140105030f0d0206040605090313090c09060512060409060f0204171b090112080f0c161a0d021e0c0f0615060a200d0e0108 69
    0x31390035020074040561400a031f402e900030b0050900c1c5031030342d842083c2107611104800c1444180da04108089100c10341007030f800ca05992003039017a04d544000402802e56a41c002c03803a13a000582c025000103010404a1344159000b80782981030b689006121a501b02030050b05811001116039500d024494243d0024030400042c0001c1c1001c0e4140301d4040c00c8a06d9580c80102641d00075920b8141c01d41c2001010b030701c101078030492041e003103440d25100d4136902d80c00071030078000401511400311b50010f102c948441450a124008092803074070b03800c180c019800c400c1d45020480b40c008042c04107500c900c0381040030b00340b03070b958250017441950512000c41c1c1000f0182c0d448101c4030b481c40032003050104214012922031302e240c09405079980e08080030b41c0090060391018a8101036000c0b50310f0940840c0400c0744204003450508a48035074031400d04002008a410080982c454002c0041002c01c074001d1150403102451528619003158030010610f0802c510750406200142242011510643e0000380d41c40e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 649369325 1250 649368075 649368079
    0xa05041e0506060910122319060f0914100305070510020a150e060f090705060a020a050d02061b040503060708070c0210180f050d11130606080412050a0c0803060f0924 73
    0x5007c400c40c5e120b2000c0101c00346ca046000ca21404869023040000d4005034020710403200f50380c440d0781d030300c0c10900f008003611400300141d40001c4021848a03051441a8000d5a4010010301940c5141004104941e000b032426001035008021710784021880d0040c20040030145060003049040741540c055041c2000109465150249003042c0400c0050001b03041e1305864055034200d944110010b8160b1500540d4000104944181c15a5500b810784c0401c0e43c5010713507000006040641e484845040060003203003e110380503403010b000030740c0c00c9104400c426002062030500088855480e0089902d103801d480741c0744041004031401e40500301030040800d000385038441c415000346050070b00180c445281100042c000d4410000404d44641c0c40414480403401c00107000c2010a41d140e8001d00313489002c49058035104000003114080c180681308a86444c82a03548403180500710b9501c204084d00013a0107181c000403140280d0213152036441007540a241d403070110581d1249041010300840100c0840c640c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 649370575 1250 649369325 649369361
    0x140c01030f0c090e0709230a051017180a1406060307030201090e040501060e0703060311060307020c120f030706050a1518020d0b0a0303030b0a05041e050606091012 72
    0x5800e140c0c0954075030180d5202040304801c507110745c80116080c068a4000e5941c0150b100031031030300d83c1c1040b6a980d549000c00d41d50780c41c180b90b03a802044500c2e14211144400324401030072241c6840c18603e001070b070103583d0381e0303581351a00400e0080d0361402c01c0b428011500401184184250740c802003008a034403d00480080400c141513031300007082d200252058140c2c158661010804002080d0054005401003076150a198505010024003420140c8800e6030384800d80030800000303042400031203214002c190000c0510b032581c2424809403400d0341c400807115001d00740400003000000c0c00200085401401c01180609100e40108110381d0148040411110010020403100700d039824441300c0603c2500c2c0068882c1e80b8800640c01828004224a0344075002d1803010042503055403040400c90801d0726604016030710360703050200b203130362010070300c50300d240c6c1d426031040b180e1841d410030365110001400380750a02652001040282d400009800040313241080d1402d4500c04a109142e0750000c3c01c1611 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 649371825 1250 649370575 649370591
    0x703111909170a0f140102130618060f0f0228020a080708060f0907080a0f150c091203090e0109021207030212062b051f0b0a090207020a03140c01030f 66
    0x19501c143d003100091000581d0310007902400030000c1c4c2100c103195018025035641c07944803c60542640d02e8020600451101c1100c401c149119024440a444a503115005441051102529140086800e8404510822000610800301d0244504007c076940c2d24048802d0302c00c0c41040250701c1c0384d41090706581d0001c0340402004100042e0283c01240001d101c4003151504103100741000c00c15007118229218522100302040114043c0c1d000d810300840c00007074851101e04015041c0c5003202c07034000000e40c00740014007420340e8800020100c94440d08081a649940740c80300611074800344d0000301c0c0940e01160b80c0e8088005408010b600c000d00c1d1408600e80400c40007008080f10000d80f03894040c0780078426002008482c200c0c190100101c640c03200990400e0b526107955500408810391000d60040c1401c0c0303001003190b00a0901900004200300000c07424110420300940190b24240c4e40031074200e1001020452281c507400e0400504005800744542c03000000d41524160480d1021541c9020b01c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 649373075 1250 649371825 649371869
    0x2030c06040b190e07030605060603131707140c030c0a08030315060d05241002030904090302030f070f060b0a050f040b0406090f150b0a0c03080703111909 68
    0x24980e005601484120060703c40703110108407604a001500c0c442d514011a180040c8000203070401100d02c206010f1009030b6644062200c01d02096030301d9160700c0030000c0000009900a4040b0485040c41b11889062070525207448548011041c0c05911907080381d110b4260320700f000c4c010703514244d4040d51441041f600d0b00c92426900d200003404e048600e0400e410141480c1d4980040740d403400c003107800900a40c18444590b041e601074201401240a43d00203d94010341096000301071030352900e4002c0c504025010381884003030108004100d0840c0410045c20340413030f00d82c1c07024007a078070300407405058544107628102c0c1c101c1d10390840051290070301040810490750340c1111100c00e40404d59000c60585024404607020f0941c58000621071803c107251943d070f40f0700da5440300d18121040d446c00b098480e500ca1110720103200d403401c808000b82d00c412071400841e0107103801e203030030090900d0300080448140d10381d02142e8210031302e90300300fa0484c18880c0b00310f25440b42c0c01c01c0c064128141c290305131101d4200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 649374325 1250 649373075 649373083
    0xc0c0507050301110a08070903080414180c0d0908300c03151215151306050f27040c060809161404110d0608150411040e03090a14010f02030c 62
    0x5005170400076103030009441c003486099828015a40170810710b4580c2d0701c41c410958080403e034682401400076100c803035051216000300e980101c8541406d10300c0c02140207000d0010f000d0417072003030768842010051485120210b25002e00354901080464121aa042183e481c2442c40503001c00300000e0280180450764004481030040c04000702d4026601e440e00310151820000002e070401c840c0d0000c4010407826802c0c10313601c0007191000f01c1c1e031088180004d00c2c120040362582d0041c25005014000840700c075007400041c0030070b8004002c4104000440a00716446da81000300d40c11030340c0400c0000204682500180281d0304200b000740588050000004000700e1105075204000c40c44803444a685126111030303011010f0b01941d0341c581e507540c416194041c4064410342c8945502c0b880340000c0d0380d0011688007025405140d00204031081c48035018100009001500340c1051140810403100240d95070740d0324084001c01078000c00340300e004080800034166802d540307911000d40d0000c01c4504c98551000c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 649375575 1250 649374325 649374337
    0x601080d0c02121002091201050c0f1312050c0f0d26040e130309450509070e07171b1308071e030b0f0a0b040c0c050705030111 56
    0x316141818200780d00003d0a00b1452201c0c0c842d0502031100c1420503001d050700100307440e240c29104ea01d507051010002a081700c50894482000d210140200801e06a41d100200300350140d442841804948a44480009412060045500d0713031281c03518007001d003425a000c00c2d4000c0120389824030041640c480e0310071912981800003882007812042961a8440000d503000b0700143d5000082c1c80c80c00c00042c0c80b01d41c0300740e0800d402080a00f800000e01e100b81d2103000300e16030035002d50340307528141a15503ccd0542020410030011204c60342e801026545c2c0d075108603440780769040001d098040c070304041103045020151070700e404c021b42800c0000d0354441c03445445400081c05c0350b41d841c00d181c5404030050103000b506c0c10450b0320050702d03c0003d40742900060341c0095801c41246081203001503426408140340911000741400340c4207000074000c0003115010b50740b0841080b00814035000c4400020100c0313441a8010b07010a0341c05151109001c0100f1003000030784002e8008001840f004500000140210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 649376825 1250 649375575 649375577
    0x40f0506010f11011503141c0504031118040f060c08090d0806151c0b0a060909020a0210180b010e1015050c0106031a06010e28030c260601080d 63
    0x1d9003c220b8040c009521140e40d20a0b0300b41400c2d0700588070310b03140164540010070300445200d00c2100040c04441d035500280b09018580360b0b140703810f1a551b141101c514414032856030021200190381001900d0f109a00d2166120301d80000d41100715150820441e140d12070502e0070454584100700d001070b0001441101c240b0380b401c04d0f407451f40e1200b0014610349480c0c00d601081d4900070603842c41204152032100d00c0419440000d1010321102424850746880f60b00c20040060769030307201040240e410381d00800c080d5040744180d820480c009440101554540d280c0d0b02c2c2c210010344802c40521091400060240c44800aaa242c5080c140c8242140503502d0184100d03240c112a024038030240a2011942500701400c02402a45c4c2d503800d15501c90542e41c050301d000a1020380010321150301c1600050f80044c402802880d41c650f201035422032048140354102c02c2c450b4004008008211050341c10030080c00b4003600c2c40d2072070341c00d10b10604c02804040d00302c1080303601c0180140f191080100f0b0200200200d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 649378075 1250 649376825 649376837
    0x7151d010b010e21191e0b0703050c09031609060602070e0103080307110a0302240f010b1c06180b010801081903030f1b180311062a060105040f0506010f 67
    0x12031109000302e078070680f076141d0281c03082d421a280b49105c0d031080c181c3c0c824040c40d00da444245610070101110140e506004240340c480c1000201e84600960009801c14050359000f401c0040e0343d00442d2070300d0290101141440081c0c0d4042203000071900549000e4401880503000091810303104850098060000030302008000c00051501c5104600b2003520040400c201c030b000c100c00b4200a0348405544803c1000c0c01200035401c4180c0640324500b5010b460b820035080c1c107980c60216a20840e40004041245a200e01c40e06800106200e00560000d040f08100e41030b4000382c0c014180040b1020030003000e041c00000c4004000340d2401150f604076415003001c4804000d14a46000c030018407495200f04481c51401407031090301a6a04501e441100304c0b130302c8a00c00700310a40c65414102410b80b02c000d004490484614509080080103420111903410703858035681c07060320310841882503c02d403030842c0b5440788004010314072701409905802c0540103070800c00c500300840000c128441c204140b10601c00b07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 649379325 1250 649378075 649378099
    0xa11040b0906070203030f03100e09030a201002120115020a0807030e0402030a1e020c030412050312091c0c0201080c0a1206120b0c040f1a07151d010b010e 68
    0x100c1c1c00880f03403100c2d80141030703c0d61089240450344c4960000d86080106101d14000418045561a461030151400400031410007002d0801103c00c1a0301c1156550a01901240007980c0d100c100003404103540001c43c056101d0a4284040320743c98030592000e1803071141c4c00c000b4180135030013180c00340080350414820b0b42d0b070385100d06040c0c4440a1203104250468800020401003c02c16405980641c000c6402403442405c00b000440c10b0303000e02c2020543d240c008210800c124903101101e13100891198040e01d007098a030b460391034800d1204840300c070b1b82034002c1e540380b260401140300c401d21b01a18505115501c00075980000340581c000400401c056803000414429840c02071440e000412400724041c03141c0d9494004040d100b58140b142100d0101400001c20091030881081d1025140c4040b0f03400840c0303251000e248010000c0050078640c0c84010041800401c001004405242d0718590011402214491080400900e069072581d01c076454407040c020036a9000c5071107a400102240c40c070342904 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 649380575 1250 649379325 649379329
    0x607030e06030c0703080619210f08030108071d04060c0c020d030906020c06030112062018100f27120c06090f06090506030a0605031501030b0a11040b09 67
    0xc0c0210081e80000080104407885082200500e9864881da446500c1c0e621000244128940d000807030100c4c0c520b06a10034404d50b240c0d9010a0b0882200d8602c010b08503200381c0380c0038081e803440c046c1542c00c0f00740000140150769082060b00001d155030398000782d214681003000002400041e200410860300c07503040c40755240c400c2c0c10440c04107800514000100a0701d150103050030949114180150051012880080c44e1400c02d5904035106550241d4014039951360700d00041c401280d02908100c0b250350320103c815041d07006407088038802150188220944010000c020818100807010440c1c03020800f030906511058214005040c40580070b411006c04500b0381440d08035400c001d4a10701c000303200c04148210505401c1c1129216202c02c1e2a15494a4031000e250701240915070109044003800c110070700344800255030117051a240051802d48450001e42070030390341c400b69611408408014400c0c4031070b40350091b0b080207202c0010000400200070701c0f2454000e51084280c01ca0003c40e0b10a159 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 649381825 1250 649380575 649380587
    0x20f040b090f0414010c0203040e070201020f0309030a121b0804140d0201021209070b032d04211806140c010c120c05090d1103010f0606020d021b010806060703 70
    0x4002010070480785000091200c103100c0449041d14810044640b0703120969042c8600d059283c516409075190074140744940c00d9000004c1e00b550308566082101c40c2000340c00d00003071401b400381080030310b035907111202c07005058130400a01402240e24022040341182c0070828440e01e0301781c031402c01064503a0342e0305212060270700c082301c210070354010aa681400c0305c0d41940203044421851305045919203861450aa071151a8000c61400c141c0400204402c05000410340301c041b210000c074182203000f40c0a9500c0c02d84400d64007115520004142154450001a084013220702c11340b5085000241210800d02540c04c40d209050602c00c4885855106202601c100e429024a000092100091609000349078046200194507410b14120b5001c1c0701f10310800c11100c01c5140100040310032416a15031182e440c18200c020f5500d50b51b50b08402c13944800c18042d11000348095009000c00744045840a0b00703050100c0342d101d134407900042e4107003040d03a00029003542140080e03900d680c4940503480d003500c0b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 649383075 1250 649381825 649381841
    0x1104170c15040503070e040c06050d091a06031b060306101b1103061008030d0b120a080a1103070c15020703050a080301050109060806030a0206090f0a300f020f04 71
    0x4101c400346040001440315005100702c81c03082d07040390741240d6100c490502c160340503900102000d00c8203030100b0056200380701916001c6540d8100181083e510358800107251814a100e400c5e41004d441000090718013840003000800d0301c03803146690340242c0d00001c0c00605c00200200d03c00e00003000c0e04182c2031711600c3c07800d0000d100c1002034040c04641e030511204d000d00c0030309141d22a11800000400072451282c08108503150700e4003c5040121300e895a001400b46e085c600c98006041c00100e0141307200400000031654050300f5060382c0c990800c1d400601a24202c01c0e40e41c102e5100b04010b00c00180851a040100e9203108000440b00c2c40c981001c0b410a02650300262452140d580c0e03003070502814800071030480c0c80c242c80e110283d40e60313500c083e20300400488500b5419002000d009001d801d18100500d20040004c05039031010100c000041c1a0841035040f07031822500c600d0002100e140c03450304451b00040741030b00343e07241035206945503000030756a1280203000d820450080b4841d40c44642250300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 649384325 1250 649383075 649383079
    0x314010501020c0d081c0501030f051e06160c0f0303050105040501050a1a0d2903010b0a060e0f0102100f05060312030103020a0b070c05091e07111509030f041502101104170c 76
    0x1c81569282000500200c2200b030550712030080850280d07941c0cc051f440000484684809407901c0c0d0389081c003a10500f8111000030341030000d803002c0b00001820b0240341c0e01081d8400d0f01c1c0003e481d410030f0f040c4012904160015070281d15079100621184942c01c1480d0500507003203040d9079403041005130907005484c00d038120000c140007032141411600507086403050034000a400810180301000c00700081300049100f070102060b001c00d03d4003824148001c0e885040c60040c0111490606285c81da182110001d4500e010f000341e070362052060074641401200c800019810b001e50540d41940c0001d600400144136809102400185401c10005821881402004014003c11103446c00764042081542060565035508048000240980d070007650005007941040340204184107150003490030f00035000e00044600d1006200781d2001e40134a40042002e403040c0300306485000580c25002c0d2801c0b1402c1c0002c08450f04003540d00514000e844180c80441d40000070b050b1803000c101808504110a200b4503903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 649385575 1250 649384325 649384331
    0x40f120e0607140c0a29030c160203010b061303030e04050115181e0518041e02060403050712050706020303090a06111903061a07050d0c021f0314010501020c0d081c 72
    0x54280c0c40d0070201907480c07030a014815407031b64440c1d028411520040707510090984090020913403001030180d204a03040d2000d00006020f042c1038000401c2034200c0f46408040b42902a802c2c0308056000d14100000c2e54291401c0c0002c0d414068100c00388010180794101304090301d0403940c0d94041c0011460000c021000c807400061103400030003240c0d005130b40689401043c8010490008078050203c2c0b52141e508242c0041c1c03100c00c496040764240d9917a0b04281e9108d94140710110200e0018840603005001d599560400080c41e490510300340300080d0b00a01c05d640040c410041ca02801141501c0529441000001d0f41c56145c00b11521a00844204510134102103940490154140e80640203841c0050400e1043c000c414822003003034490702100030800e402081410340b449004041c100300007880185900000d1403c41a032110543c030342c8025400203901c802a280e00000030340c09250140c0401e1000d42140750392800840c4000754038410081c500d07000060b5610207680010205845540d82d4a028 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 649386825 1250 649385575 649385579
    0x30e0a0507061404091410060e01080106030b010e151e04151209060f1d0a17030604060e0702061f1d1015050705070506070309120501090b040f120e0607140c0a 70
    0x200300d0180e04443d800005680c0c1f5002150080c0200b05035002100142e440e98150303828801c04130081d00c2c2c5041c3c4a41404806000c50300c02c1c1e030300e1710804425079040074115601d0710f44c12404000d884480d004010407491040009200c1107941c407070150110101410b00310000c080400d1810020485114060001481e01c5a803400200c1c450b003180342401180c90142d5000344003004066143c0508a10042c902e401c0320b880310300e14401a4014641c402c00017040003400c02d60f908040403c030380c41142c003400140c1110081116040c40c98020028a00b110b00211400c2400c2000c4c4007141d506d040e0400d6145105000040c903041044a10003018103841d00c000c091216070904003818a8111000445003070059000110b0a400c0a00c10b48826039010798583c0c0c811403900d0100600c2c9400e5140548055484140090106a20740c001c540220f1003560511801d04150030001002d0103940f03d00401c000510204040390354036074007507038412908113001041c20980100c80c1031400e443d0051a94000d0459240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 649388075 1250 649386825 649386851
    0x30507020f1f1709030d0504140102030c0d0509061e04140d0909051f1a0702030703031214010b03070327060504050f030313080d0f050f0601030e0a050706140409 71
    0x24807181c840941d2968100c2031012402292145811907141c0111381c0240a4440c0c1d071580d039044280c0190042c85040742704d80ca032540071403e9034002c96040c0440000007603c440d070250107114540e440440d52005d8051400d05070030b00003c0b8200340c02124111303982900410203100e60070401c0201054004221203a5031411400034000c6a00c13403003900307201891700c00007561700b45c01521950303814140c44002401c264200420f059031910100481c9408000c00d01095005803401c010400c0511301070f03164410640141c2c4292400c0c0c83c0340b0440c03240d120580e14010054003481c04103594100445042c04107a00b0420705160161512228090305540c1001c140070080c4092070b030003179010302c2c051000d4945c0c0c5134036000850303a00e11058034009107040700622118003242452024208103800302c213000c07502200c031001500a0720310540b410f403075465004060111035038142c8918110808140040d11380500e403602c1c0c0d5511440c1910075603052102945003896103d1601044402808103008208594109004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 649389325 1250 649388075 649388119
    0x1050d1a1005010e010c05150702031b061801020a090b0c030c1002030a060602070321030b03010c0908010e12041a1c090c06050405030a17190c0203100209090103030507020f 76
    0xb040c14081001e02c40c0310701055104090080790907403c840100245041c951243d03400030700c01041801140130a2000f811000c0c0b04550301010721001100034019404c00440c039001c1c29903080d11184490b0310405c600d182964020044000f1607904c1d140701030b00c504c2c0c00c914542c107520a4214600c80ca0194403400090f0b0700081d0301a500660145008100c1c69445240581c1d4078096800050848240020801c0401c00803010045d502811442c0100e0301c1e0031814082404e46400410032000708204e4501030240300e9007440f07078101c6d640041c0b0040c442c0445013008400c5510841c00703270400561411034100340c900410402c03a003299140740042454080c1606030b000c000c6c045020200e500a4052000140e00d52044c82968161540200501070900701588c80002c2035911240c481030001d82440400070003601da5200302c1d110b91254942c0703441241e203441054180b900006e607405031180305010140c826203401c0b03038540c1580e0345428200c3d55801240001203080d81060300181d030205c61104140504a07020f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 649390575 1250 649389325 649389329
    0x1020631022b06050109060518070216170d020c060403060b06070c030f05060a0b100315080607050a02100e0a0b04060b0607080901031a0303090409030e03060709170307050601050d1a10 81
    0x504100c11798a81d0240342c01ea810340d1241d01d6024412007030320000001001c0d0041e410000c03070700407aa407070900c5171098a00d07085158040c409204d030401c4c946690074014411100e07880281e01c050710742070b151940041e000b8007840c04080c01507951101e1450081d1500c03403c0321060b541059079100015640e00c0d02c80507079000c040040b0303800c1c00b861001c81c03410307106401a031031088801080000c0c1c200c5d4047c0218010040000c5142e40b07102980e600007100d00040c0912070140c0159034807540e8504030400302030300e050312030820310a075949820903007490010f011400409082d4860940917903600c490030b01c2e43c068805c1503035003544103400142c044e00f04440100100f00541d02070306c041c05072110f11003440100740c04440b20142c00d0740040001550740c1c90154010066240300b410410340c0c0d5140240840d240000c100c0e4107501041140c00180001c20604840103008072800000b5460700c0010303a02c4507150101841058041c4c010380c10341108001d4003401e91b42c03d0031303104410307580c013403500c5400300d801032243d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 649391825 1250 649390575 649390583
    0x314120117010c0c02090405031c05160c020a0905191803080618220f060209040b0303031311130c0815010302130506091807020c01020631022b 63
    0x162003100103100c07042c060600d80d01d100b0780f140d8250729103580034032040c8080140100d460340020040c0941408010015200044404800245501e040400b1600c2421626804404d00941c1481e943c0165901081c5505907010104042080d44401119128044c1001603d14156040891b140c03004005540303080300c2d0314000c4e541d54003603031180018040c918400500014020020000050480110400d003c40c3c01d010b1600e800d9525a080c6c590400507200c01c1d504440840c2c00003203880703480c0341600403403c04000c2240a940b030740c242144d205083c0509500000c2c80c0d20300584c562754450381c403520160003044101c4400d00006407064030003400828112803804100d107450813820443d510078425036100d191080c2c00c0307906c00c0342001c0800c6103540003454090342c00000c500c00740c080108000400741c042c1c5402e07001840740d802c0c80c000190504e0801013594401401c06001900f60520306950758200d142d5881030702ca103242d443d0010078542d40f0b00b0400c2d111102c00300c4141c0303100e1442c0d00c100810780a0003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 649393075 1250 649391825 649391849
    0x270a1a1f0323241005040e010501030606020d120b12010516021b060906070c0b070c0b03160f0e030d05090102010605031c20010c09030203152203141201 67
    0x60882418100c04085511602c030071800c000380d0124100300a002400010295021404059000240a06283d4808100011030214040142c140c1a0040c50702618007401c0910510341403200096035007450031240400c0140d140042c02d40c000982c0d00002c94008050840e04030015104200384c080e14087d611070008006032452885102d00c04107050300c2c00401c0c001040d44040292080050341c1d0080382e54650310240810101000541269002d0010081540300685030005828040c4040105500c2840b45007401c004101c035503c561174030320b10769107918180120080d03140d80301159035103072840206405220740494200d005400402405615030241d0003403010a40781c009040e101e00990910380f040804101c490b01c3d10b58014585d004110b0100780c040540c80000d11043c40c01c0d6a0540e8103c1c0204103440c80a2055043c28402021800080e200c280309905005c1c0001c51140e03541011005405d0403002c083c41010f10444030301100c101052010303a142d1140340d8042001c03000c00e01c11000701080e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 649394325 1250 649393075 649393091
    0x503070f080c090d150204090c181404020f1204050c1c050307030f30060504020c0d0302030c0f0c010c110a0503160201141206270a1a1f03 61
    0x2208141040c4a07030b009081160030060000203010780c0c07925082d0300315410804c03a1840310025035644080c0008000310308000c01c0104014801400e600405800d4064040c0f01c2c1c1750a01441c00000030a182458050b175005980d062866803074031181c0038403592200b04044150500050120004880e03c09ea40100e03072030719082c000410300800034007160000510715002071094201003801180204003094842c00e26a48041109204521408aa49141c5442c0394010f01111032a07040d445003c01401083d40c04502e00311424810a039100369090300b00c0201a00000014011083d000a65400342046e00c48252981c0c601c505c45c0e40030380701c02c15079680040c0b8511256480004005450211550048061881c10300700d00202c0c1c0c04e10031101c07070903810b0000f141d0080341807007254001410b07051410180c2e071842e41000802c2205004510045a201442c80941d248240711282c02d00350700f10380c9251000a07550b02c509400d4141520185440e944076041c0d400c110b03814072441002101c9101c4541c2c0030000b040d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 649395575 1250 649394325 649394327
    0xc0616030906240636050a060807090b030603100e190b0a0e03030402011209111503090615010e041e11120c031003030f0908010204090209011803080f13090504030503070f 75
    0x5549080030030100306001050344500300003481000e1803210010300c00417858542c030104201159075480701d00021132580810917610340c05000c0c0c2020300501d581c84c502d14105036000a5035001050746070ba024503525060720591205c200140e814403029440c050b17086074158108051152400c0321030074a858103154124011030804022a441294140c42d114400040c1f4425200101019002142c10903074001c20310045236542c8140007022461303401c6046e07aa02d0f1909202c5d08040004c1c20108607482e8112035507001c1d07a0000081d0000d12820364000034104440c90501d1080c120280c0c0030412285400d8017003035000144801000c1c200c03155910884141c0b40c9088951644c8070860b154034105850030b5080c00002e100340034040c02c035446481e01804058407400780b582240d00540c4105450795000030700030951350700500b220031328945031a0800a85403554541c84114820040701c813100001c002490b205207075070000c0071405810306000403c01468580740142c0168010b84100b00428000c1c0e0f1160421 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 649396825 1250 649395575 649395587
    0x709020403032c03030d0912020705150a05041214060f040b06090403030221010519080d050901022e0b040902030a060b0301090f050c040e030c06160309062406 70
    0x241d03415074440020b2140c0f04191503405076100c81c1c1c614245801d030710314102540d040000e491303070074a000000545203150b450035001584120491009540101108120654130f800d032101c03e40b10001481c81d60717071001c00c0045409115640081e60001051400002030080329070421941d031240c00c04031021504c40191188603468201d07002001c200b01040020042e00b080016035070410711034180582400305d09103041c200707818100109504640304100400c0140360810300c50402d0214551160785003410240036646598586008500340040001d4801c0030383d02c200203461031502c440c49054403415400da03040801a844038403e4074000e0905881d02c1562500b840303000201e0b070740240100080c0e06650b45842c05032540d2980b681d4075546e10034640001c100721042c580d1450744580051b144e13000303001041208944d0500700300c0445c2c0e401072203480142e200004580b5084485190b00c260001202039003100030303005183e00100054149109201c2905a80c107200700d0403248405515905620b17501d04480ba = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 649398075 1250 649396825 649396829
    0xc0516030b0c1c27051c030b010804110612041b090204150f11030c010204080d080f01031412040b071208270a06110d060618061d030106080f07090204 66
    0x150340030403a034540742480d0551001300041c200e0031010380703021420340d00440e1481c2ca5140075601c54000d81411024002400c40a000c1000141410001c0c0420003000a203401002040200b607142000c50340e004995441c0c05407207004035448144c4d0a1880c0500e0074500070142c0200b08030242071100000319a1000398000e032015070765070340c184490181c5049822941207049000c0001170015444038803174068020300041c80c03500315940001d43c0d100d142c10201031071700300304450120811034028140704115824040711811a80c00540317100703201d044031500703e0410800d03842c0200140c5000400180211070b5201410f2014040c4008002d04a4002c102307a4200d541103801b5103c00340c4420b514141c030140960f1034060040c91000315141c0c01c4a0366642c1084a03048024064503d8020070b0755800c0032542c0c016440640080d00d405c4a011542c45201e0601080c00d0080c001444040000246c00307014002043c2039441d030040003440401d0303031003410700d88810940c1c8a5040d14040d80c80301040326401c500032101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 649399325 1250 649398075 649398097
    0x408060106020a021e210d02060606250602160b010501020606090f2a0a05040e10080d05030c1218070605120621010903050912010b0d02010f0c0516030b0c 68
    0x212417400e02e401301420b61040c200303040e48107050070032400c840344d41c6900d5829030f600d03440014914000c540307030f02920b4201700a066a2246031304104448480d880aa000039001403022005a032000483c07600034068040d0302d800301080c0f074294480000703000501000604841080e000d580da15202d48050080c40f100445103045203c03403842c0070940312040c450312860b01c411401c40b1407a2140c0901c0000106074000e281440010384d01140c144182440308402640040f150015140340a00d8481419154005000c01005212004c40060f510004190440d003022803e61074030051803070181da9081144c80c049803004c445125200300440c01038010070407540301c820700308100380250351030504004100708403506e219128503100520301d118034000d0040303941c81072087d00c030103031a41c10100a01500f4400311110415580c145407a00000783c4801c200c1a20040d0207213001044282c0d00c1c0400c0e1402041e503600141b50344643e51180c1c42d214003034000e1005503031040404040070348030a60700100c54041e1800c111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 649400575 1250 649399325 649399339
    0xa050a0e06060f03100e0d02070f060e040506040f14010312032703090312050903010b040c05122211120a05103b0f060114040e030c120408060106020a02 67
    0x5030b064030f804840c1e80a850740090440b003c2644100905d002e9482000162500c1d0b40081041c00c005071701440181c0181c8401d1881301c1106290060041901364048562070103503075102c0100d2116151504000d01208602c4400d012a0100c14050b2240d548242320503034080003c62408240c5611078050296100d14201e08100302020018402a60100c5000d0440c24051100e000000044800c0340700c072405038203134541c035031504248014182514651a9070034030941c941040d024100d80c125050380d200404010080101d5610615801484404180ca1480548454018000300403d00070340800210302500c0070000e04601c941d40e01c0d41c0766641e0100900c1ca030081008654440c409a0202602e00c1c098480320001a00305410054001501d85480b1990100602c080414a0042101032060721901d03004000ba58507000100302c01d90902522a4440c1c1e8031041c041c0c0c40d84104109640c0201e6a600070380b0014141001d00003490380c407510030082103006030700c000174495001148a002441e0090010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 649401825 1250 649400575 649400581
    0x180901050d0b0c1603230301030308010b180a26030f1c0207020a0b0d0c020c03030a050a051201060e1912110d0c08030c07050d020604050909240a050a0e06 68
    0x5400e00300e02c01403111562050a0081c03031491510032903440340d031a000c1e450719010784151680704000140442141008640104010000a503104002030b0441354052901901c80070290300b050840061094203c0d400304155001042214600341400c000b10240350b03112203640c890030100c90312030142c510740a1045405100c04207640c0c095085080329245441703c010f1918005a0001e003580300d0790342000b80d10110224004041c0317211886445180302590000301100d110340c13400203540b4481c800021007001404104c070741700c6074042c2040e41c1e207241441188001560f142c0d20001c00006194403a68401d41072044040300c80d4092030003420503120001031803226035402d9140c2d04604089864500d801c030030060074890110307014a050101400d0318002071075a0b24104e0352640d00d40b0100350421442801014007440050380c1d50300866085801c280c0e00350000e5901c0404690900f42000420240504d0130020300301c19812172401e6038130840c0c6c04041007107541c81e28114201140d900111300907084c0e000d8408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 649403075 1250 649401825 649401833
    0x5091905071203140f0a0e010e030a030f051b030c12040f06051602090a050f07300e0a06090219030807060504170d021201060e0a090e21180901050d 65
    0x903080078000e04182901c0d050840303c1d004d5960000150149007400480c10701031040e407145c139515100000740f0f8090703003421030100000d40303ca000c3c3e400202803081491250781000e0140044d640a8411782d810340503030152451409032260301c6420400010300620240c120840d5082042c0c3d4103807034503e901010614201b610684556209500312142001040140300c0145e880300e00039403180c0b50604001c281d609002c400480140d8000d000e000c00e001c250003514419115014858074400403171600d1109924484495400034080c5561003c40303070044c00803400030b020141d004110068802d5070000b6041840c640201e02080d1240002865a1010031030782000c21a5034201a41150040c007402c0d504119046e04e44801f684201c1c1c0c4c4100f03068001c21181c0700310b46c04c454110b00505d810f00f0182032076841c44000515000c1c060044150407643c8070600c007c1c21004101c00c5249510403061980c50424544041c1d8080c0c00164841c2e141807540e910890700c50514884c1c5904a40c0003070f00442e1084081c0e40c2d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 649404325 1250 649403075 649403099
    0x706050c1c0207180b180610080a20030405121608211302030714150d0605102109120e0d0b13020a0e04030801030f02130c030509190507 60
    0x205000318820301c50f002c6000c141d458003440500b03800c00400502080310409010040e640c1100e074403145010b0300d00300901900c0703103514007a40c50b0161400700e996a441e04403001c004c08000d6242202d84614080490001c00117400447c0514000d60407601c0880020005034a075101d42103042001c0300ba00d0406600090111000d001c1c1c9840c035019182440c0c0843d000494100030884102d40141c0084031040103508043c040c02016005804022101912100104a03582c112151010780414006000c0140007150381c0311101400008000c9140c86002407001000c3c51a0750800035500c450182499211516521401841c50f5101d00f107525181c0140006403450741c28251204c1d000a140044130000a841040070303440343c80a000100786400700e500500c9184100ea801c100719050340a801c1c4004070b0381050040e070440780c1c00801240c0d0f070307078452001ca54140d0300b5018800001c0d00b04001160540d800d90495032040014404850590706051b0081c1444603481c44094103070380103084107100e2210f0ba02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 649405575 1250 649404325 649404373
    0x40e0103140f120d091a0604060e0f0c09150d05100806070c17090d21181404060e1015090f0308090301090f0507030b1005090f0601030e01020403050f0706050c 70
    0x117845009460380d03041500c040241541c2c051500040200c949800d12075800500580320b02c010043c50410710040580b030740030749150720142001c13822481a50310304526480e183da91081580d00c400748941d4610280c40f090314010210345501c0c0b404103d40e000010594422001951020011100f07a19049041c444106981e03071000020000401d1540340d10301481c609511411035050034138984002074090b480345030b50120400004024101c41105100b0008090f261001e01d00d05c0c81d1250007002800034540b0b40e0080701001903d00403c4007a07040644c4070001c488040c004160007580604c42207440300200c0c022041540400d01e01400412044001380803044000790000902c0e0700a40c54102c04241d2101080b0342d40e43c420701c814030030070145600300b9400100713102d02c10900e01d040c1000150440001417179000840c0d5540e00042881e1310031b03081908499200c5c5c008540d20b507102d080042e22042e101280099a108c1c0d840c000800781c6c885d0301201c443d11054006001029266801504106518 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 649406825 1250 649405575 649405597
    0x601030b0f061801180605030f070302040b1903140c070501050a021e09190b0c0c040522060b090114010e030c01050318030f030a02190311090f060d02040e0103140f12 73
    0x145d42e0004560340540c0c0f0038001d095a0b40700c4540301e00c0d1950391002204130042c0303a801003600520040000b40d0a21054600c0c00180c02100c51401c015a04214010420000812082e038019400c0c8060030030140020500c150040e8000d202c075a4032825078a050784189030007031003034511170450002d22401940c060030061800801240351141c0305d01081c82100d45540008455080010341503811107002c10014071051800e544c01d12491910221844511045081c00380300301d440e14024104112499000b007030046802070107000e25503112000c1080b080328070040c940c0894003e0150380003034540091821480301050751181e1540e40c1c0d607c1c51003030342040440c05880c50b10013030044c0c0440e624030401440c401d000c2c03a030700140c854294480c0710030000780c078050300c00525140c12070900002c4040821100848015640e1001400d00740011134141c0c0302e00300b40f6086151001c500425680b03050000c5504032801040301200700320165417443d480d840200c15114141c4d11880304e03544407030505000751120f6400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 649408075 1250 649406825 649406837
    0x151006230904020c150a0203060a0f030510022203121b0206040b16080c010c0e010c020a090c12060e04020a06090e01150c0209090a0516232101050601030b0f061801 72
    0x82d05c0d08031039900b1420740310902455008410400b2908024403e070004008125284150600d9038560f19190b4480380180b0000b140c000500004c80c110308548910a4810303c603443d04026540d0800105880725011a03038001441e485c800c1c0c82442003409036010141e00106540d203000d18224004585d035109a807880c0d20562145180b001080350355001e0001c942c2950008603440385110b1008000c60100c0300c0041c14850705055540243e1259a01e0405880f04807000180d58560880240e41101503030070b006102c2c80c2005004188001104038050080344281c07a0b018415031a0071090b10007072002e028a031102401400100042c01840d1003c030792104e80ca003070005071f80c040e6030003065018004541d2021203a202107000b408214040199000a4072402c031040e420b1400c0000b1200807030140403001d0300e400d00b8011181804c0d41c4850414950621000101030007001049486d4041c180c21a03505001c280780c01f01180c2241411611300001841c01401c80f4038160811044520030f0f069254a04d0400c60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 649409325 1250 649408075 649408093
    0x1b05030f0c061b01230a060e0103050a02040515060406030207150c17040201050708071a1f050121050702060a0c050403021018030c0906141c080309151006230904020c 73
    0x10b144400441032810f0b860300d074082450040c6c40442506c4440e4402990150034000420108101081d803d205c5541250045010303240e000f4003400114551000c545e01c82e8000600080c5c0507055230090650034452500c803d501e4040a03030340c00407a00d0150100010960525250001013040501c16034000d1050600900f0202e0545459005420095049410703842303405000301c0400e1101003041c1e001c00100b0b01c01600c2d4451a9038050f0b01d008503c501814002c0c0400c2c01c01c10b01220200c06008032b10145030401c0203103042d20000b5550341040d90050030207460714038145420ba00c900119016241c02070300865040d82820812140000700604010080029100c0440081d4004440c0002040501c002094030b50030b02d40f0400f122184a8251440303001c0c40907049104400d880c006e441c0d6990041d51182d200d6a41516075800c1240d99a40b003042d0f10f02d00d00c100907415201034041c4d01a196140c5d02c416416032041c44115802c101c190801c3c01c840b40c240002c0c01300f0300d01038005068519841d820740342800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 649410575 1250 649409325 649409351
    0x9031e0a080318030f090111012c010b03190309060e24070609060c18050d020f1908010c0806013b0d05011d060408030708070c1b05030f0c061b01 64
    0x134201d903610300b5070760b240080c400b0030787e40c0e0051040307901c0c8550100800c6034030f1852400000c100050014070b8415065514800c2c0f80340c90a6002140089014068500107d10a01000400c0070200e4044001c40d03d8204003141e864451801c0091428010308a003820303a203c4120743d4031080d2022003262040404104540004060307010720184a40b080b0310120702c0f410801c50207021000005516008140068000c008039911074400303480e4a501907420a00021824000c900c0741412040d81609903141050b00260300481540480402203540e6a054555250100111106180c2c41c814100300282c65600c5d4511440400945802003c400440032100003120046001414112425501659200142d06219849610f00c0070704000d1440500725a2400b5550300d4100e00001d0a01003c02103600c0000f000c09000301141a4055000425820300b00d494004511030900c480c080d0602034021002203004000f000a82949603042c010704480c104190b0903121120118424850005592101961000d034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 649411825 1250 649410575 649410577
    0x206161406071b03051207181d0c090d0303151208030f0106030612120c060501080a020f0907140706150f031e08030106180506040b09031e0a08031803 66
    0x220300014054150752501da074002d069680200701200362903000200140001780d0003070860b002c0b408006603a004507280c502c001c44840170700d101ea000905c201c041011513804410300e07548806001a42d654101e503500c400d210111030107641e001c0c5400648500200b40002d009401040300d00152125040c0400c1d9140500010043d600318103031882c2c140003042c4203020510341c0120303001d00304030b050500140745000345c901180c81c0c240c0b41c040c0426008100008880344200d8541040580204e014846542c46840482e25001c078400100d200700c07010058050142407421083c2d20a82c8207495403d101200c801e80311099600a420482e4020750380c18022980780761250f1742101407d60480c10382d070554218500071003010700800c40e10f21007100301c0c0c15800000b0f1401085905550052038802003121805c2c00c000c6110f00b01390480c1d07a012703201190100d035414074070014000f952812005c490004010203a1107120300038a0252803401e800684d00000400d600400440d0041425640c400c0802003031a0110b0171 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 649413075 1250 649411825 649411853
    0x706021f1e180b07170105060307141e040303080609060d02031c0c060614090901050c090d02030a0204111806030c0d02070302070e0106050d0f0c0906231c05071407020616 75
    0x8203040c185c10114803e0401601405440c05643e1b1501c1c5090500d0090030f0b6401403040d55140f26000507007604000e05040229516004100ca41a2515168503000e081074108032080c1d402a020540007410342c0c500040440304064000d4003074009140c2120310304056212600854080c010380000e000300080fa0751185000400c5a003242d100c47d003407048104000340c4400b60021446038103001c1448000204d07401200c4200d04115818165458540b002c2401c02c800040e010350301914041c0010200405440103026100d2540641c51040484004000e0316000c10fa410300001030040c00003c00b4003600d03500400c449402801200e000c950ba07845080c0040a00b6080400000c0000c90450100c2d07103e4000c030040109060000d000c1c4500b5070030000c0c0344516601c145c6042001029607454640014a0726840e010108146566201a005003520fa14540c2c0408800454509000200c11a102c0d2840c20308400d0340c4c0034458900382c516002c03c00e1f42e40080407500c500c051050071010001e9000050610 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 649414325 1250 649413075 649413077
    0xa0b041506030c02012c0f1209010c0c0302030f0c0120031602150d09110103052413180c0f0513020c1e0d030c091d0a0b030706021f1e180b07 62
    0x5506c1841003c18140640b0400150040c0e0152a000b15600c9004041d6505090280307400d0340d11050354100007140940c00e5202941600500745180461000410b441c04250802c0c2c0740c401481e1a0100c0100280e400b4941043c03640d003081c0404c002c482c903400320000405000600064490340f40b08404081603000420011840c2c0c1e458a1071010007080001158691109082c20800e80c45c10510031071540380c0114645041d00b8001070a011360307698203000e688000c003001e102001903944007021400551482d15040c2c03000c5841000c0041c888819144201c103440000c0c01888003001d48114010280d00044070905440c0504c001032400725034407012a6580b0403250740242241220703450041d0485550310508000c10610b0300084c44a5801d0100410031000c00000320005039561400d52002001882c9881d0f506000302500040c400d6800526003800700024030122015690742aa02821215150b90400c43c028139880c0c00e850400700c0b94000641c0030f80084080381c02d95210307910500800000c99241d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 649415575 1250 649414325 649414391
    0x70b0a050406031a0f09091c030e1009030207150918050a05060d030f0c060b090115080f06100e0117040605181f09030c05060f0a0b041506030c0201 65
    0x400e0a0707041c001d44d04103c2c0101c407111070300740380c1d400030900300c45154403020b01680c056404504800c20410185425010903000300b000041d0194004002d011510641e0003644a4425003659400c00c2d403043c501e03410380c15001020218546580c03001d140c00c0c0c1c0c41c001024410502c0300002d41403100710300880c0e4100c400c1d0300040c451a1010000080300c3c4e002c3e0806002d90020000350002035006207209920f4002130408074944112072138104058090320812903089032000000044000060070101c0c031146ca02e450f400c1844c1e4034401056100e00e0304981c0d0b035034010030082c091891907009064600d8103450600d811510610b0329803441c625004291000c548030341d6100b0421002025920442c80540e0706907000c4c0110783e45121000152840d280e000810700c1f0340d65000c46082600036803071441304a0348202a10f40507e401c1c09500700141c8200c6084612600308480040036103880d101d1204421800c00c42180d0460800c54114020019009010190340d6602c0746024806403010507183c250a80003004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 649416825 1250 649415575 649415579
    0xf0e010b182d0106030605120a030e0603060604050d150c02190221250f0e0c180d0b0a1a010c0605040303110f091503011a031909080712020706140309070b0a0504 71
    0xc80b0f40711700302350104070003900403080f0500002d500c41c4680049e60421164940c07252030b8200003a01900c03955000c19808003403211040200102445884850f00340caa808202094120b082a42c40f261071900c08403d1086446002c801480e00401900b0180446c801410006554486044c03404c200c4601800d55042c4a5020040310b15852121034003a10b40544417000ba207103849a0f0705c9912001030a1082c41880104151030709107450342e0340c4204400c0007000c0d5440750001e030805107a41e074000d4840e41d0f5500e0a05801e100f038001d01d401664030341101a540c95012a0035522018001c01d0042c10880030940c585440500301359080b006480091204001181c0d92503100c81013007810103989032040d00745c510901c0100525551000780c0c0181c034105201c0c6030360700d9803640b0f00c1010105540d00c442d50100d1400015100740042c92024000c02d03407046c60400c0e0b0003428154240c0c1c0e107411522445001810780000c521140702088090b40d0000c040d40d04440750a915070324102c420b0340045004400160001c281 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 649418075 1250 649416825 649416829
    0x1812010902100216230901230303040605120703090512040f210213020c0303180c0904240605090c0c100911040203190f0e010b182d0106030605 63
    0x280c40b22440c0d15000a0002c0248180d03103100e00c2005210f9001880030300c1020841c0c40c070607002184070750b0704021310f282c5881d03131500781113603811204065280002c0341072070490f0840d082c00812103017a21460b8480608150090444c0c83c4043ca00400e0380c3d0030151502d024070006442000300541000034161541d80b501e082c020301c000d1400c1d50758071028109034590314506070280394215103649203406803002d0540030340c040c080101074419a550429140300c00010010308403000404c1200350f920f08000d0b00c007a0a0b0040030050880400d44018110708a0341c00098020365206401808403175503038101180d030b180d5030000120385140448120140c404002024240c560b400c0c0722044000c1d00c482d000b044805001d8a40007840210b8080c41d50007035600102003200c180642000d801c00341040781c02800740340b0031b80da03005026080b013500380381c903960800c1051200351a00c030050b44218960b40c4034920380e41d640c0b20b190301d10548141d501c403e001d5201ea90003100d0403c4824090380601829203022803410f10b4041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 649419325 1250 649418075 649418089
    0x170a05160306031a2e0f081f0b0a120f02030c030d1205040611030703060905160c02060d0914060601021605011707110109062f0403081812010902 64
    0x5506800c240c5807007400c0c4001054034100c01d155040040c4610940e0381c501340c5c04082d4000c40403690340c0c2070b103440416000b200760360381c0180255400040d5100d0281da40d0f511a036510105200c1d0035901d8041c0030030031940042158000b03442400000c0810005030380e10507110703400051041003510003400303074401c1405604041002c007400b42c1040c0c008084d254034540004003181240c4480d0840a501c94000c101440000c1d0462050700c200100d01c207507241000c100280041c091489100200c9091400089200e0540581070780840e09a480e0448099896401c00c000c1e58003d0740b0910441e60f440201c14013050f402106c0c005804040ea0003840182400400a03140c403006005604117103004641c18085664807900309004250b03000c0c00c0c41e100780c072640e40c145e4115112001c8140550b203010f0f0f1040030f021041c2c00842c50158803113291000d80905d82c400e01d0444500d01c50800c09202d0030001000040c82010051102c03a50159003108030040a50002e1104071541454601981d103480e011010f5140101d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 649420575 1250 649419325 649419361
    0x40b0d06031a06030d0f05070c080d020d0e06070204020f040801090b0a1b0f050a03110c0d0e0f0312070f0812040201170f06150904150816030c050907170a05 69
    0x15071003010b140303818000aa0344825a4500320100300402502c2011240034109540000b60b02c00000001d01c0d131209019540d8040c41c94854006100f504052040140200c4410103d05409000e552801c14550240300195000181088219004210010b2032610a00c55000d81c144900440c904508101441c2c2c029201407041c001513020b10800d00100103030b003042400e02d41a0345401c2c1280c40b1904503d0550040c40010844040a03000080e4510641c202055020410f400c40e255a5040840e503010f1250758010800c140b13030560300c0801d0302d140c0d60032010058001c0e00d10803002070f810080036544028164000500c0b2404a222040c140021503030030020803003100e00c25446004640c9031150000410f00341c007a15031401000d480c08404003550990f009c03031701c1d0040d0180080c000030040e0301c500307501c11031240300e00325003801480002c3d90410401c40051017244d0b041000c454103e400c0c0010020310403009000d00c1c060019140c058910030201d149001d101c0d154008000a0b40d142c031840f2854811842c07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 649421825 1250 649420575 649420613
    0xa0c0201020708010209010c060f0b031b120c0906010507051e03120a050f0a020a02010e010213050a06110a030f0c0615060905040204030f0f0204142a071a0705040b0d0603 75
    0x40c040c01c06d090340d2100d4142e410b25000b000c0170039a50030b2403442c0b42c0140546d9292a4140c014411410100060408248010b10041d00d13803c0300750400700079081c0c4554804a02d140d20070b00348004148550b06c180081c0403400c1c0110184c4d841c41801040000102d03074041089119a000403501c81075190741c070312180780e000250a00902c16890030050a6a541c0c00c001d1034030803011380c080340206840b0310075807240e003035030040781c000b190748001c00c1604400400080c131803c1d22803c00d001002c9078013841800d611560b07042081c0201502c56040d07070700381c0340382440b002100c0800102c05a04008a0464041c10425003a50b00144503031904150000b007561b6036075000507000d103004000c10400030306901e407000441c0b9009011071310740300703554400030740078101c0e840072003010174081002c5c8805441014056a01038003c04a01c200094000340d19a1050103204170240007a52044445001c1040d5100c072a82e01903c245005460161030f9074031100070f40c01500c01c1d02c03e0541d4032202401000442d5030141120661 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 649423075 1250 649421825 649421827
    0x60b01110a0c2907140309030d090e130b0c03060d080406030c030c030b0a1403030403060501030c0f080a0201050a0c03020a022116030b1b040803030114030d0801060906110a080a0c02010207080102 86
    0x22200281c000f902c80e9010003801c44002c411424070220040c41a142c0301c034030040540d11040f07a24030000380b00c40e48038002d1524100c079000219540c0c07004e003c0c142c1c2660394028641c0c03210b540c501d0f440c02c01540004280d141c21001207901640000c051600910280c500e54800040810100d10002c0880e181805403038149842d02c001c00f4410340d03405451342c0c00c54280c2c0068103080764104010a046000d2503000801082c00c1500100400201d68504420785584456544420380c4c0c0e4134425a94849411010740031a8003008513020444c864140800503e001e801129a043c10355800b00300c0b802026040e0480a482c0c4040d10720805405002d00d9500c9440203c04612440c2103480c1e032000c16101030086101e401e00304501c541d18880c00c2081e240284148801e0300d0f01c030f46c0d4480100903035180e020840d910030700406604030300030703070040054606a8240341c0c0c580c10664101001982d203807002c140340700781a1081040a90003c2d9480d801800341005659681c4043d18040c8006840c02000b600084a00d0340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 649424325 1250 649423075 649423139
    0x6090c03060613061502011b02060c0d1d160f050f130e07030606031b06110a0809061605010c110609060a020a0e0d0b071206050904060b01110a0c 64
    0xd4009030060b00301c4030440364000c8100240c89428000d188551000c42c14014690520f0b0b002e603010350028110710440000c0c003141801d0140101e0721241d04898a000c02642406245412003172644108160b50034542400701a140412009181030031540c40104460002d03002032024a0710f211214000b024250ba550f00440d006a0001320041c0c107155014168503510041d416440c102007020000640e08030303070200007a0343c83c0c4c00d0845004142c3c1580922030b90714640c000a8191054840000d0b00c0d10701c5010b00100c80195655201c694440c0c942903034400e40600240401c1d40d9411102c00e0158418400001c102e8907a01018080b40c03d00e41c290a2140c211100b08410054041041c50b0f0004610000507a1811410029036200780744180054021180b061023404104171411801e003d90039a0703c46a50507030456050f00d050300c90764003900d50888a00c04c04100041c0081d001b14034001414109000000c0c14074001138034245180ea425510412420410000c0d1030303107144003021544250f45d00801e035070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 649425575 1250 649424325 649424329
    0xf06080c1303080a02030a090b07050c0415180203010f0e091023040b0a0b0a0b1c02040909050a060b030c010e0f01020708010507030e01110a20030c0d03050906090c 72
    0x21a008000810218000401e1140441c0c01d8044002566204450540364960504025a41d4004007840000300b0104800456030030706100641312041e61100080c4080c905020510028101d158120071011040880c0480c40c441c0f000d0030510404003d4400580f81c1d8540884100c4840043e80548480c00014082c00074803a0701040420784120900c0d004116076103075808020890b180c58088010038044c0c801030108001e4000300311070043c008103c0a002c0441900c080000d01002841107000b410801c1001046029200d15100c420103140751005007440d90341c82442041d614204001c4902d600301080316410801644a42400c1309015002400100e4600002170124040200f01910800c90400310410701da20811500c0050008900240454101400081e0180017226168891542040d18410140c43c00006460545d0240d948524140300503024031500a003800d171a02c0303428041004204c409003010040d00219100544d000951031402c0e4901c241042d401902220300d80d0031206600c0e46503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 649426825 1250 649425575 649425587
    0x503071511100c48030908010c08010303030e060709140a0909050606150c100506031f1b031401061b05190b0115080114030109022806050f1c09020d06150f06 69
    0x3105030210130010010b2141415501760ba13586d0b002502540c24178810b10041170b8001d82150485e4070a40b018081080c03441c82460721050211180f000083e00e01408105517500302e011111086000b6240d50442501d81c40c001b0280d9000401c165047c1d4014001c2c0882420001064050701e0f1420700e00500781810718108540718200314001c41d10311500d171400319480d6030f014010b20704022700030f540b5a0300c420b0b40409440301600d190308203025664480c2c8000c1e41038500900541e103540003101500005a0f003002c2c2d06607010041c801c1e9540c201e4000d11016030004a003000781e000307803408a82940003001050314150189290503080702252249002c401c144898115078000e0558040c0000520b00076a0080424010043c00d40081d600420310400240c060340c014000c440801c40328204180311545070307042550244030b182c3c42002078a0042000d20752a034034801d0072508550f514500841c40e1002078000031640d809800096408a41d902804510008402d4500008044141401031f003e403502e540070b052 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 649428075 1250 649426825 649426937
    0x310031208091911060d140c0705030306280b0c070510080a0b120d03060e130308040b0408040f06051305010806010c060504081b030c070503071511100c 67
    0x411a640070000080003030030a011103034194007909081d02d0703a000c886c2e43e801500d44044076071a03a98031503001c1001340307103d6401c454017290803038000c52540e100c04081c06509619000d600750750981c80040c585102c0c1c4d40c1813040000b0010b00c0103286d140c0780b501d00c410b8200b01942d8849031158035a41c5000c041e00e5000080720341d10800100000a680d0030131070100e00010b29800c0020118091400c800022a17015400081612091040d040c0c032995411599103070306d40e40f5000580130071003031400a000285410304456000b0f110311103450601d6941c50521540c0d541c1a01f03c000800c4000c245900300401d018081030040c0000d203000c0d4843c1c10060000f0340152150300d0081c00090711800010140611001180c03003080148059855042d240c0c00595225008542841001c2c080c4100000b401d01d40014010140c81003c040c940b01d51210500980c1c180c0c0d04201c05d214280158000000540341900c6440d0342181c1035110114200d201541e4200b04054104c05d4500b01307000603100601d9511082030f1100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 649429325 1250 649428075 649428103
    0x13020a140109081e060f0105030303041e060c031d060c030606070c03021e0a0801020a050909090a0c06090501110303151018120c0b070b0412030b0303031003120809 72
    0x10034221080101c40345501a080890248101d031490140d150f0380e0340b41a0b509110000644096850b003645080c1c030b0010a204290b455801800442c01183d512045031030f140400981c0600c507503030142d80305000d0310341054200e004256609420000003070030340c0d00042e242030003601a06262900f00010315540c0006048a4020030b00810603e08004071080c4c540044c0d9001040d90607004050460303100e8805180783c140b80078000b000000500c8080500903541030ba09551600c0d402d0155032020f10080758002403030112580b11f0310035000c010801c0c801102c0c000e4445a40d40201441c140400582642c1200007103042d076030f00c10020010a000c41840041488500b00c940c0d0b200750f002040100c0f0b03c0d03242401ca42c4801400035000188103c910038401c90840e201d2080c0c0d00702a40c3d0f0760640c80d0305015180300a000c5020f8440000d00180c1ea4141204040040781000a01002584003181c0b07180c00c2241c19a40451400b40b040c41807201c200c44489440b486480c01c0d81b041e141510340107441d80e580e561014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 649430575 1250 649429325 649429349
    0x200a0c110117160905100905010c230c01030b010504061409031c020d0f17070806150a0c140a05073005030702120601060c0b1302090f0f13020a 63
    0x200581c86003840c4079112140d0b2610b840329080c15580201e4044080b03400c0340100d0100c4400050900301580040400003003615184100f40ca0030f0300543d8031003066401140c00001d0344010440c02c0f911100e8800412120300300404145a01e43e001400301c8104454103410304c201800100319640d80a054501c400714510500c03500c4030212400b0074584006184001c90f40c0400d00c021081c456030001340b40e042441c813aa9400a14060304100342c13080680a2826080105039100082190b4000d00c04550081d8014114041c110b004a080500907089103461000040302410681d0501400c0160410540341c80d0002d003981014603554980c0d2170741c09100c1c03102c0070400300308030003030300c1003074802810101c2d44ce000c0c030304541081c5240581d1641d200302c0c8200e01c9038401200c8075484100000710a4169040c80d103540d06072800589607005103440062041008075a0004884016203500c64960b000b0085c1d042d0400b068148040561000e0000502e2600e01c40c8040680c0c00242c0d407440c1510041b201142100c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 649431825 1250 649430575 649430603
    0x406110315010c1b120c06051c1e1a190807030b040c051c0201031d03040b0f070c031a13020607021017270105060f010f12050406200a0c 60
    0x320a0800040880318203480e507001000908200c2c41c0091744540380318030031603d480e82d11068151854051000003540e428940311147c004200e0940c402c03000b00c403d103101c144014454480200680c0c81c000c3c070600c0da0340150708840140741400d020300941c0c000700002c00c601c02c504007026240e60740e10612010b056048081d01080034000000c0b803400c0070344000390072501306005000305a81001d50b82c41040380060b03d41850080d01d1408040c04090781208074003c0c6d0710341403800714441c031190420074121410020801c00f0714002404220244010f41c4941c0400c2d0700000070003401c0c000d00c40020814500b21005580b0070380103035168403c07101a580e044842c610000a1440d04030342542c1080a0300c160f03284280244109a1220006442c440200d060344030042d4228220341401d031003040c0c2c0c5094001d06090303101013140d8010900715110281524200c4403d103610340100c0d058540544040e0781c1103644200e05554441421aa0314511b0900081da0b450800c05400007400004085005410b0304d40300100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 649433075 1250 649431825 649431833
    0x50a05030c03101e11031905070e060901090b04080708011d0703030513030227130308040204020703051c0204140d080d1e0207030806100206010608070f0c060f050406110315010c 78
    0x4891304c6100700300d030402c0340c9100300c0070700c40c3c403640290b031f0f440398826003c02038458007002c5000e058400c2e402d0399104403403400a0024812590050381d412414004855000314041d480400034100030521603004102a40c0f4020806084440b512030003035803c9540d403080c2c081d17220001180300c00c99905140141d4cc41c03103241c1400d081e40c0c400d500003d6000700400022402e01c4051054040725040614040f4020303151925850400b00960200a010a410034000790240c074040e400b40c691103000c2d0800718038011840d60010014200c0703103c80c0600650108082c040c5002142501000c000c040c0c4184c000c4100c1a01c0b2442c0c1801000b0004c03205075220414548606007010205205a006010642d00c0e998286406040001e00711001ca01035841001860300e62840080d50747e049901e1920b4101c065141c0000499002e11182500d0090020300d5203c140004c0d5244142c90711007650090010f4142803a00d050003d5440030480d00382000d2050090010405080c0040781c071804003405c0034400b4400383e1070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 649434325 1250 649433075 649433111
    0x5030601030612030c0201081005010e040506030319021f1401140a0503190501050907030b040f030e03072d180f060b04080c030607020102070809042c07050a05030c0310 74
    0x2200030000c2e40210301008142e042101c048280380b00b48c90b1a07400355034480540409140324801c4a00084218224030080d0500d40d0095402500141c01e4916281309078103035118150306440c1100050344401d100c881c100006859014810508030400d0003803003158840c1c030494030760600481036580440307001030841c0e50318603e02d0700007400090180c1c9d034400790549180c0301c40240000306031015400c000010341203903000303d000c0065940c06000340d0300c80c0d00c07140c6401c0c514a13110701040b010f000c1c002c240d1203240e03501008040300078410300782200e00c030340120040700c4140382c0c100c03ca0044144414009211341d14000780c0004414615810003c1d00380040c03032600014003156840814180740c0003a021a81c10070110b000c058403c0c099040360307495228543d04a00705c0c820040084c1c902202444081e8007841c1c95040382c200c001107039140050031004080b070703000d40051780340140309654081072040019040c0103542c0c0000306011009003880801e15008242c858902c2100e4040040d92440c54001c0004216 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 649435575 1250 649434325 649434329
    0x1e030604091b0f090501051011030c060c0d0b0103050f16020705060c210304110607080c0f0a030f05090d0b060a12050106061202250201020f0a0606170715050306010306 74
    0xa600032411000c04092041c07141540a101c0d60000043c4010514a286000e032074100c030400782600d001491100b1044540d848c084070702c0900c5000812103058001d20070014140120038011855a40d4414241c40c0c000310380710544011705260401c01080501c0002c2640c2951210900d161014a4480c1090803420311102d038102c030382e0040021070301c1600311100007041d080034460f140c0305644d01a101d001e001810300040307600501c4480b001d45000010f051607005448454850280b140c00c0c05001c1c0c2580d42844880150b03010a540442405000d040e44070194003201c0d4440c0c2070092030844202c0114514156101000e805603c600020a5090300c031a2030080040c01101c5804078407451300d141aa019100d603114540c0002c0d0301c3c42d40001d08603c80d108980288120403100a001c103040d01e4003251000e164101641580a2400c0d1a40118014001280e03074500c10031000944604010701c0c0e1080013400520214039521003001407100c030801041401d450314160908607102e94590340102d018224039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 649436825 1250 649435575 649435583
    0x6061003020c0a0309052b06020a0c02040603060902030c04061202060310051020123c070309093813062105030306041e0603050708060a021e03060409 66
    0x300d03c183d4103055005c2d2072074059400844803860720f8051200c5c440e00180303e4038000f111071a4001c50f20b000041446e8001c02c6001d4035400c1c84840420503800040072034285900c151010340d100c410741001c600e014061000c2814003140c2c10007140341050300c21a0107d4111200a00910000010492401c2c1140c078082c010540140307196240c00c0b4400c001010f00a000114a100705060000070440c2c150100b56040a105510002424a40e071484c8520300c0a40044a9140800d8600c40400c42c6985880384071180700f4150032580c0d0b8500451070024031100e1603a2085095074501b5500c4a60382c1800b52603903400e242e402c07060340c0a2040b2072480b0020005040d8603254030541070b443d10522042180c004400701d0700420f0201208420b40340c40d490a600310079a000300260000c1002400c20b18180c2d10032000c02528002290658440b4041c0200301c411030b4200741e0349039014200c1005860010446103901c6064207905500b41a601d040c441c0034604104489089004084000341c0c00d074071150300c00648a500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 649438075 1250 649436825 649436833
    0x10605040606030b0a12080a050d0f0e03090a0602280201021002032a07021005130b12060907110a110d0b0a09050c041a151207210e06061003020c 64
    0x6100c501400905013459800d000d41014600058200c1c40e092209603480c0d04144400e241c450151005c03191640880c0c003009103030b276a400000c910641103200d0485080a660000c55580038410b041103210300941d8014070466000c00c0c4500d00f2203d4039014214038a6006503c03005030b0005100603401c0c034002c80008200c04c0d10200401c010800c07228802210440c00c20121030001440002043d1544207052020350080040d0fa4203400c0e880c80f07000100b00700174021204179803040d11840341d6001760b44065035100d403440c0300780300340031441c41c25808440e041071240c100342c6a041c0b00781c8151501c9440240001d89900d140c1c0d0a001055110728405443e81da9000700449030916128032000000c00701158207903030300c1c4200640010507080512919140c1d45c040d95401e01c2c0005060b0170024207007402c1c00031011450051001c40442c9450281ca640141c2d00ca0700d8445d0410000f180c0d04031a2040381070b0045415081c840000c40c5c06802040071a0403540c00d0702c214030080c805010950180c810780100c00e2962003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 649439325 1250 649438075 649438079
    0x10c0e1302090904030905040f0c44180703050703170405060f03040302070503060603031206150c06070305070903020d02190315020403051b211612050f011b110106050406 75
    0x141c486800c90503100c04031420040209203003039402c22510410f40c0c2b1004a210070010b1820032100388056280914409880019140c4280801a04c0c460007001c0300d501c1011581800410900011701007001e2040100601da894695100d46031340e1085480058180e440c0301c03215540c1001008200c801030700024100d2541d8602601e582e0b1f000ea48125010b80060050a902103442d2402082c164000c1c01c00400850410820b030f100941c0100700608030591020201400c1c140181c21000506035608089015200382e103001040901680d4009000300104400400c01340b0060362514070301c5007580d0b0161184003158240d07075104007071020140c0024000d4a141c5114548168081c0c004105681c4200d003503958008803000416850031011800365804100e428150240303802c00d0340c0260b4080c0c50b05003110440d0040d000c0000000c109a004101c030b116170448106c060010130000f00c1d983c440540001c01c01c11007088190700c481e5008820060030880c0d40da240c8680b0100942180001d0301004104010b016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 649440575 1250 649439325 649439327
    0x9140d0f11101e0510050f0f010203040909050a0308011707030b072003040503011a091305100509060106090e07090e070c0b0c0310050901060c020f010507050f0d11010c0e130209090403 81
    0x42860042030544904060015500308918090b000413107501902c2e81e01800461008c10004000d01c0b0019411844140000110389246024820441c0d0081018004000365404c0041c200c0c401600604010109041142071105000a4000031607030030004841c110b48a4001c22201c09400c029907000d105020481070b000210040010021220118002c00c072043c01403840d924941c0140f40450f500031459000580c040c00ad5141241d400c501c500c06036500310044000c490b080f20030541d150702c071a5205100604c14650005220700203484810030b11546882c110340010b0410699004103494030710f5050210300c07032502411a4508150f4080030b80f4440d032615442c0491940c00807101c036490340001d042c0001d4035080c0720300340030305803541c81c0d03111000c0e80c03111340a1090303902c10f10a00b00d0410108000401c0420001d000f51000468400094144022503540c001d2900c1409201d0b415940d1616540100e182c0c4c02c03c48040d1040c00075150260500340c030402c1400240640c00400390080000ca00b080109 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 649441825 1250 649440575 649440611
    0x9092512051f0b13050703020702090c03010603050a0504021c0507080703140d0c0b2d0705071b061b0c09021318141302120d0309140d0f1110 62
    0x4000a00d590b80d80e40c044107410060301c80480b5841d411240b2188004851842e41c4c00060380702543e410007502d00046030740031238070f203043c00c0b1035106603040c4c040014000c0c560301d801402d800c400d200740240801d0801c0c0d0001000c0242c07902d01501c00e070346014649020842d013070143d0780040c604103064802d55aa00e051003003134490031f4040c1e800140070740c40f04d0310940c500071101403034040c0d08082080d4503035944a801410f03890007840c02c150442030100b9030a642c80209505180f0485441c1d9807662220380d64582004071900781c82c2864a220032040d01801070300c0c1c0c440120315045540c0c0340c1d1400d00e0340707050420309480c03a100c4e0017403044203000050280e0500c400724880340c12100303500145403103602103a80e114200d512040551010303016860208862002c01a00c02e82128002041150060301c00704021b440c141e84c0340e0f0710700c001c29280c2c417804041c081d46c040c403040106480c2e0017034825003240e224000d00c506005181c0c98140000c1510080001c602007162010000e01c40100b040a562052110345803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 649443075 1250 649441825 649441843
    0x1090302010e0d02030301060f0509041109030d031109060904020702040e010c0f03090b3c100803040b04091508012a021f0f020d0501170c0909251205 66
    0xd0740c00c1ca810044000d5002030015005019580503500716428520b00b02c81d03091154503800d04008003808031104030395451081540c4140295026079403009208149824006103820007404d242c94540c41c2d0309202e80078030444099180c00c40b04943d0700d214900c0002d0090103a00c401035001890040d00100414056015021016254480c83c081203038071281241500c0116600824062800000c1450f44480c22aa150340e9600034111038844035145030b100c0d008080d000340c0e07041a100d81c00e052050500160103400090f1410345d01440c40e080c141000142140300e58480c500506580e480303a016010b4003001030a0161500d03100a2081e00ca0002e00300b004100d980542c810801e50101c410548180005280c3c101e0043d420341d410141214816160000c2030b40f43c004050844c2c00308100105101644034550127055026100f45203a00c1d9419100e15088060003c140241905c905010350301c0000520010020002c52b401401d44643c00c8141d0241c0d1440d0b40001100102c060302042000804070388110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 649444325 1250 649443075 649443077
    0xf03070e0a0c031d03040e150d20060c0303041e051209010206061e0906060c010e03070c0f0305060112020409020d0503030702060708060a06081b0703050703020706050913181202010903 81
    0x14503d503958103500c5009409131511210307401000108078440030240300c10b0340b00707200300b440c4100c6501d40d1011600c40f50031700740c0486500c43c0d207101c26a02c1c1e8259207440e1b518240240d81c0c0600344035031910199500e10000d000a805400a007840a000115140104071559070040964650705080443d0f2900c0d03030032050300c3d01e001d405031000050341428807500c0d52403010033119450890030b42c0f0b2828001900da014108540205082210740094142406104140c01170b0790011076075030303125090003000040d1790b41040398500c059050030804250009542810340700c103102c500b04100401e1000400070303d51344030000d4024907084a01014028044003841c42220307150203503042075076950422101c3d64001c17910523a12081c010400c0c03103000e126420f07860b031140580c0c1c8580840145019400d04980084d44102c0000703200086403400c05074148941c100506103410886d0034032001c0c0c000501300c1e20300d040118250b140d503140841d0031003507554442442140c004841581c15031104200038060030b03a11200b58 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 649445575 1250 649444325 649444331
    0xc0a14090415330f03110a0c030e060c03030f0a0609060b040303030506030109021003020d020d1b020f0613030e0f0a031401181713080d030614090403020c0f03070e0a0c03 75
    0x1c0d010b446458a029883c208a0001d05100e000c100e41501c0140010072440c00705607403100441c1d5050412401000079540fa5115412074130590f240060807038600e010464015081070021000721100081945c2d0050b40000315050f4580d581502d0f8002018285c1c400150f82d41881d90000306172041c9070007403083c1ca00035a000e026964854080c50300fa41c03501c9500a4100c1d40105000324900d00c07907809041c8807810700d200540340800c05010310003969400501440884681ca03040800c032a01005147d11142602020b0901c40c50002c09003c81c0b5680d03d040981031003002844c40d111540c840901e491000c0340200312240191b22810b101041c400320f4007002c04603629003164000e84c01c54540050a125034000c0b15540680810040310b54160800503000c07004000307101011070741d40420700511048807025600001c0c51032900d0901144003981e003c959000d86500b109100100c3d90220391020501000d0350b022299140102c0842e140000b66404038014403140400d100703003000d20350040050607809a40074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 649446825 1250 649445575 649445609
    0x203011e230402090409020301111b1606080a062607120b060d0507050a15030513021f021f02190504180510030605071101050903030c0a14090415 64
    0x201d2019000c070030320304010707404000c0124082d240c1a00240352240000d00041604015940070a00350b80044402c044010004119140903242c0840305072841040781005264201c40c4000c10713070414403140900820800400700140d01640309401000050202c401c02450b07901441e2001c1a9420760203020304400c3c0144d8070000b50040044584071042600860400100d4440c402017054410005400b140c0f54011904000740d41d0fa580c4140e100201910812081110080c501c01411500018509012102100380d13400143e15041d807001a581c4200d403811502288040b800da1606076400810032800d20043d8283c0700045140c0c01506a00400e200018200401500180d486001c0c60080c4a4807000152000c0c800d034015400c002e4110456402607461940c40b0303251042603c0c400c881250210f030f06014040d030001024400d440d408103102002d942582040328201f111b5101d081114400c00030211742023944540340604599240500400400010b079021555914882c1548140341054100b5501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 649448075 1250 649446825 649446839
    0x307090507090b0702030a020d030801180216020402030406090b1f1a0f0a030207150e06060d0b0a1d0303100f0e061008130b0109020408010f1104051002100203011e 72
    0xa800d0150141c0d4490600c00d90411850120b140c014160680e410702c500080710026841e11510440c0365402684d401ea159030401490700c020071003260b101c50350544104500c3d86181c040c0000090350590403a400b40e07480e00c80c0c0c02e001014110700720020f000307640b1a43c203101813820740203516114124190b4510031219a10520340001c0e10b102c1e401d244109004010310401203c640d00200481c1c0802d04005040c03002544403103c400100c0791303c400810345d0345c1c4100e0b2070090007000074640c4980100c078041480102943c0ba01454280540410b40e1103490750801c1c0c0c1d414411400b24502c0220b10ba080326120314282110b0705200b50759218110150494030b201007880482500d084d4800d4001419050142680c10002c840b2420018681002d0350440000d4000085400c40c3d4180282000807000d80c803103040088060854000c01900e8400d940750941c000c81c140741d80000d4604481c030444600c030220100a80907410900c4040c4172442061002001058681084502121804040032042c61058650b16 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 649449325 1250 649448075 649448081
    0x7110f0c030a08070c0801050a060321020a06020d11030406050601030b12190c120c05040c09032102120307021c090608190b0411120606120c07030201090f11030709 72
    0x555a4264202c05003400105030200000d051003886984034055195036100d0f51400c5480036580d410b90700703850b0f40f81001030100c3d0000070205404e4000305150403560411010f50358142c0b46000400303180d00811000110141075010b2110721049400c0c079030380c07807074940703000c1c401440d04980c1c0d00e02180c03810041c00805e041c100c0d041c102003d200c0c070007804501d103a0356016421504012003110080001d0034081075189103011440c0906101d00e4000a140e07051008010589918840d21000c02c110030310104007240c03071000c1c040c15016441c20b4012401c44440012820074001c04070a006290001081c004440e600140303203072101d40b001c80c014820001c40401180c070300711580300300c00018070f0b494041007407000d1071807140482801c00c200024401c075018000c90251084441c0744140380001241404ac3c040808103000d074400801c032007162800382c106504032154030019164001d048408240d4104040c000d40c030909002c1e4120501100b152018a0400d4100f001d086201d8042e00440c2000642e90721540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 649450575 1250 649449325 649449343
    0x10062301051602030109020409140d050a1d0d120c1a0103112808160504020a20030f0f0a030c02010b10030e030910170106140415050c0607110f 63
    0x6500c0500d03008003802c1a0400742c81c107010907a8155030703d00c080380060f81d581c407903a4140d0744a01c401148101d0f0407440c2c60f080c070055280a00031b10108001c070307442276907121110164903218172030303105010604800807413071007200c58100410600505207804840c0fa0860054001140301c2c02c0103d1040c8030300031900c0300141c070a200040500006511181c80e07413620744903032441d000507039842e5524120003400c1c00c010307214594000409500311700c12101c04015418038010203008159002d514160010b80c00424480c0c0440301036502014192000107807080610485980464501015807902180481400964025200385e000700385442c0c0709101150040c000c070300c0e400e580280f802e60ba900100b034055000d410816181c8a1600080247c80132540d6a98851013616516546e00d03010b103260306405c1140000183c220f003040c44030003003882056125000483c1d00340c07402407c4520f0490007201058806008030010300e03615019000400c121642c0c4285400e828407015011107260b011072080701510b40b1030790 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 649451825 1250 649450575 649450577
    0xf100b0f040e04050a05010c080a18080301050409051e0102120a05060a0e0a06050d1202060601052d0f0703020a05060114030613020303090306091f0c08060d0201030e10062301 77
    0x1e01c0104080c0c1e02c554611940300f400364043d20142c03c85a954a82100e030740e44429000304900c401800240090340c81072401408002c8101003028015440e6490940414410031348900d846008950402a0512440d0070313944a1b001c40703c1080c01c074145024081d4020030300c036211017030401d800540450810702078540a400090221401ca60a10860300c20060000f082c8015150302c0e6070700020245c0320390182241c924010030208128540101c80282040ca018021904003e021b01400d0400044040344410b80c20705421002100100441c90012600030883d1240b041c650100e80310041c95004650190000d00c07401c161195603807502100214200074000307654050784000c000480300e0b520031804c2c00a02d030000341103d040481d80740c00a8030f051421103001c003036504151501c0328601120001d0905072450881c09020b4252480d40c000c1211800400d401d01c140103202d001820b40e4025884031f91001030b00f000790b46c0d515400711446000303803540f0700c104064a230155088000510403510208424a81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 649453075 1250 649451825 649451827
    0x608070e061b070515070c051f181703070c090c090e0901060e01230102060601080703200f041403030a0507080d0b030106060e0316060807051e030f100b0f 68
    0xc80c00d81d07510520b9110030a019580300b05003010603c4da0703481c0f40b41c8500c1400e0090055461301740c1d19003c140e001c41503121a00510250386c1110016071204108003170a0164a0007aaa8072501c0000c0d00e00e541d11644402c1c81c00c4100240c031051200d000c4002c14810340074100c1480c410b2391b200e0400088900100526002440d90344081c0030007407070484019000b11112001240103511110607a183d42001c0c0d20401d000c1c601c86100c00001c1712000924841030100340051310080c03030032100290010000900c039000f010343e0f403c04000c10f468a940c007059000b20100a203610350440030440406075005000e031450f5121314051102c0c503490000308032031050909559860421001c0d9031034120942189201403041500e5801c012419107003440380c100282138654403400420224001d160421403008034015044031040c1003404040d03000394480d90040714524101e40e0310305000516801e0015807103500901d4030400402d0120000016158138010aa509803c0e0241e5580b03201e144400d1040340803130100420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 649454325 1250 649453075 649453087
    0x305091002010e0d02010e06070212180126100b031003240207120e060c0c01140c0a050706170106140f040509130b0c12061504030209010f0608070e06 66
    0x918880c40d1400306080e000216088480c01c200a0524580031150b0006030b54601c0c0341d0481c401d0401200b9001200c0303001400e68141c04e010b08410385e2141501080d0200303044108000c1c140d2240d5003070200403180c440e124a510001d055004c0e880301c0c0c01c0c0c41c0b8024407003144101140400210b011a4022002c840041c03440d9480d5a07617101c44d1001c00c00c112003890b1000f10200a0181c880c2c001881d02c90301c00c1c0a000000c2803441406808190ba46c1c05940c000c1009000e06244ca000000324482c8108013402d03c03103484485040604003074814454010514041e000c0984200100000c54500742c0c3c07015101e0450b0b24030006080d420300b003000d1207a0b0700058800c42c0724150a40b55040207201801c90382d45a6441d050303e4001040070b01c031041d03c0002c948035400260300d06204080031503035000300c02030612a01d4010007200c01c51074070001400d0280b140d50009000d00c2e24078500422030300115400780410800e0340c0e450000300300704000c1d4401c0f603011031003140000c0c1d041031090b036500c2d000c508004c0000b41020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 649455575 1250 649454325 649454329
    0x304030801030c050a54050c1c0f020f1c24030f0516080c041514190f030c060f0215220c081e0703050717160b090405060d030509 57
    0x40c031582c281c030741111440c0449540c4007000c80041c45910a00e18806813082c1b500c8a001012114000c1190040b1403061146145040c01e162109080200d508004150304e0b104d40c0d0f20000034482c1103a92000c01c0300c002801c20700d50146050300019540e80400030000c50015800c0300c46d0318110203518101d0305000003410f00004007244a26196030340a54100d88941c0c0821859000c81c143c140c21a40d202e0340170552078201440d040c01110094182240880c0040d0b1408240d40c12002c0600400c82c41980800c040082c2d4a6204850704010030303a0444182d50320b41d90b400c02002c070000c0d84c007071407000540240904801e0750001881c2c501c88403015410309065507a5484507004000e04040074401e00c0006c100301c5000c0f60f10080a400608074190151603003411104509801022900800c003160b000031701e01300082000424044c04940328190020005130b2220001410080240343e8103a20289080c00070a0143c13080001e884203030000d0b00c0c200225100ea02c100426200e2100c0d0080004500b0010b90300c1034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 649456825 1250 649455575 649455629
    0x4030c0213110a0503011e08101a061201050102060f01080d08040f020a0305070f08120a2d08041103010b03060114011101090b07091e0b0901050f0304030801030c050a 73
    0x40304a4030700018041c0c0340c1d503440450b0354403a008000001e5000300060194818071243c21096a481182e601540b81c580341410307407589140654040c84941d00c0c010003440003082d01d510700b88200700411196403280c442d4145604d0000030302401d401482010001b424001c000d014540c1070302c00e0b40b0003c02d00d03442039a03011225607130020012a41108590320441c0142c03942c0485002a500c6240a03014442c00c02036420746028080d80b009030704c1d620000034945a6510341c1c0480b890b102070303031400300340c0e0890018283c810003082c106100301e0000810b4442e021a540510000d01681c810340680c900381001d841050309035000c0d6070001c1d0340b5800c02c2c00104280c0b8140300d07110b80c00c00740605040c1040b844002ca5503084031000f1106032019010002040180b0303521a034240e018050100c0d09452280002c041c4482c4112240280c40c05208006407400340340e0302500a540050002c080c80075541d00c2d04d494002e090f070307000b88812180c4484445001c5864074101d10028140c0e8036240f400c0c02c2c0030400c0c0c110314000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 649458075 1250 649456825 649456849
    0x30903020d080405060309010b030d0c200f09150a0603020a0807121805011b1b080d02040e01080d03060b03091906020705011d153309011e09020304030c02 68
    0xc04000003d81c035141c017009988680c0c424070001461150b0541814280284d01103135100f048104900b00c0300096010000b03003844003d454a4580c01c0c41d2480200780d0072001000000c0d40b000c650410050783c05280c0075401014081a075014240c03d540c0c444c15016030145000c0c510105400c840080e40c0d280c8102451510150605801b0421204545610035112071001c000c3d60240d442d502c0700860f038107010041e1040b0703103414076001c4255820035014044085e10140001c207007103030001e801d10340340401c0e80603203015010049018001d565200500c03a0382d03d0144407400c01181c04c4c00d90000b5402c0400068a101d00118800b0301024002185c000c80700700f580c0001242c580382d0134003002c404101c09200365141001c00d0341010554501903552a454100d16200c840781d02c2c5101000c00078000c4007442103289050180c4a107910601c031101c180200b500034400080d0300114244000034904c00702c8814150240030009990401540314400c1c0c400340d10084030f0160226441040740e000600345603021900c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 649459325 1250 649458075 649458083
    0x603061008090c0a09020405041d0a0b1302060d0e1501060509010e031204080109030801080115090209010509030a030906030f0b06040605090307090f060e01120b2d0c0711010c030903020d 82
    0x20302c0d0550f1100140c40c1030341c140c11420038240e02040611803400e00c4e1041c40003c100320030641408500c00000d466903900070300c000501001407400800c003607070f104502d400c101035401000c1a490344d80306000304008202030b41d200f8185224080d00342501050380c1c141d49060712001e641e414130b0082000c00540d01402c140c1e01250705445481405601e006845000d070029002d48400030804c1c3c3e02c0c0341401803c0e07942c1030b08030007500e034540724071145048811030081003120b011f9480540c841d0b6540c801a100b82c0140420b96030907016540c611000c040d400003d01c1e041d81e4441d141041394001e510302d00c0049480307005403d50408410482842498003c501074000c0060003401c640855454500b41c8094441c010030071110f49845140a20031040c0c05403400d4090010408a40500003107615590800000586604001e08989000c0c8a0030010340c001600d030b901c1c007c07003031070818148900345c0c044c0c0703034440e17101610f800d0428829052550b100d00070016800e5010381d40c010801c4e085400700000d400c13528800319 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 649460431 1106 649459325 649459333
    0xc0f040801390e0a0312080a0c020a110d020402040312020f01380a09111804150b0f13080d030e061902090a05030114070e060306100809 60
    0x80c40c200d49032480800040d1404910209450740001c1d02d00d070f242103c1b03180d80a4024031301d03501514039420108088180300034100d845011441004200030b0540b10300003904c0c94000085581203000500c01450565244c0c1d41e050300c50140090310000d83c200082d00810210280701d5001c0e81c4008049069804401d0383d03082d140e94401c002101406900410a0350943d1030350154400503100c40c080811000103154201422500b08072988400011103240c1542942824064034000c1020a046207080381c0c14002400c0c2250880000e01d6101001441140c080200600c000c0000f00b0140d0054182ea0500100080594401d803910540d960f00c8181801205500800b81c6050141c1d2801c0040c2c840d103020000841c44181d13544410b90542c00c004545c00d602c1c0c50184514010206500c030704440d40e0b0350300d080c880940021108140d010001e40300980c02d141c001e0003042c1e03002007802c06032 = true := by decide +kernel

theorem cover : BRFrame.Cov 649280575 649460431 := by
  have h0 := BRFrame.cov_init 649280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 649280575 ≤ n) (h2 : n < 649460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
