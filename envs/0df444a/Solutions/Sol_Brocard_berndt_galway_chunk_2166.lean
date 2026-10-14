-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2166
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:51:16.285715+00:00
-- url     : https://prove2.me/submissions/c300cab4-1326-4a29-b688-fd22e3bfbfa8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 389388489 ≤ n < 389568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 389389739 1250 389388489 389388491
    0x60509120a05030a080a1404060c12020304050d0e18071d1207050118030519050601230d21030603030906020c180408040b1605120a0c0323040b030f0604 67
    0x700045000481100d0507080b9500c0c044996984038085400a404410118000c0008030004c01c014040107a12282006045985800ca10102c130039804040c1d001c20b6401401c160449090301c0d861500403030140311404000340c20b00e005c218640c810124000401c840c468041501c24000c5098404081540300702c941085840e10514501c15040c1d595900c824021181030110b0f80c040f103840300100b400d05a0045902008071f90410349921f000c06180001000c1c100d60a1003a0f04c00070403000340400d205801c0400034044a120085450100940d41202944c02d07141849404003403101e6402051a40d02c0c44895a00c01207011460b5103401401e034412940648115006114160000d6545000c0548280380100e01c041e0240c4403420040600d11440e400245000340c00078a4424031a00c2c540740c00d0762903000744103450409010313000000c1e0340c0c13051322803031400104044008000a03008078103030040501c290354010200d012200060b03e0680c0700340c000d8910703c50080100001200d040304000c2c4e00103020b5030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 389390989 1250 389389739 389389753
    0x51201092a0909051005190f1406030d020d32120a05070e0409080d050124080114060a020a050609010f0b0d0206190507060f0b0f030604020901120c0b0406050912 71
    0x80b2140c440c0031003091707031025a40b80d00100e030289800c1071252410380140c80082124804004a4030010042e4003e40b40c036007181000000e229190202c0d00480455842e005841c181c003160174202c07113006056100c0c0b4030090250182c01030030100b5105414078a09941c100c0c0ea513900d00d44a0000c5c1c00c641c0204220281d604010800089550010480c1040316095401040c907443c1d51070000807c5c00742ca0000707002a40f80000004111011519610304039001010407200900040800c807118413090044850100d4807030200c1c1500c0c02d0200080a13042620f1061318603403030340790b601e0a040042c01e403918440d44c0e440c3c60190107221518803801d6696402120600782221403680031450b103000740102941c00c1a20170b4092001d01e4010001c0390704039544000c3c1040904081e403110341c01805213000213401802d41910240881c1400200640529002024082a68038002c294140c00544030030882d52440300c11000241a40418013420203460135031502501ca141c05030a2064040b5044040700e05c50744000c4e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 389392239 1250 389390989 389390993
    0x6080105150312090a1a040f0b04060e09040812010902090f1c0f051203070f0806180a02030a0207050307050c10080106090e060a051f030b1801051201092a0909 70
    0x3d07550075a5100824440c1c5a40703090000034002e1610b0b501001100410403c005a8804004010010340e44020b00158100f80c486000001e0360050b800390b88041000c013050101e9514000d403d032680315100d2400149401c103401e0b5803a56000702a402401c041c0e8002c1014801d070316220740080348000c0143e0340c08881e0f03040412070030040c20050002420401455880c0310a214060244500100304911084e66a040c020750041c5030106a080c8070001583c030001040440c039040088840c0c26440c88010301843e2246100c4200960001e0300347d400c107503400c10040c00000c83c240080d00000d401007000d001514002030500c580c0100904070182009550b03001801aa6040803421054449004000700380d5a900c0f80452440061500082d5000901c2c1100311609074441101859110311540c0510040407000d09200c441d00c0e005a1034000324402000502160600c03800e01e01e4400c0c150000030985051135101d0516980c40c43c800681110a00b6540719202c8a04000c160300501291104001d0a5015 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 389393489 1250 389392239 389392243
    0x61813061412030910110a050706030f1407120204050d06050f010920340302010b030f0a1709060c06010303090b12070f140a11011a0607081e040603060801051503 71
    0x38400309101e088103a060709103861046c00780b16142d070740c22030407904030101600700740da62040780b44036400029007840e950b03030074010b40750240b44c0c403c001d15180040c0c9a00e51403401e85924003500b81000701d02e50309200008032680e408549641240c05500c0c0021941084030138410903400c142c0140742e0941c10803809105481c06245806250b44504400585441c22901c0071060f03008500920b0171210282c10000d8090750700758220782070f107a100c0e4000f00088946c0100385602c0700d541c1d80d407c0d03030f080c0c0050341524007080f5a0321240380038078440e15105291245240020707941742c10016034000650703c810014410560481c4040003e016040d41d800d040180d100d0001036500d1000302400704114031144c000103a9805507140511300c06180e4130306a215100c0c144002c0c040c140f888540082582071400d01000c000d50707001c2000d500d0101a103010300c3c00d05c081c2c031040e103164400c0c0700340740384c58280100c0c0201004090024102501c001e680100b04186022021805d440f00501009011075208244008a0fa40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 389394739 1250 389393489 389393497
    0x501050a050d0b060307030e011a010e0103150b0705010902030f010510150e1e10051c050907030c1d0a23130203010207050f061008070506181306141203 67
    0x40da280840da5801000c034a900502505240c4503040301c1d01005000300d858141e04440c18504046000b00123000030160301143d4141541c032a0790102c2da0b80c0c484450203500c0f9800142c983c8000d4014030b00c41c2d6a540080ea200d42c0e1180d0410b6985940d541401030443c0b50030700c40c0200c0d44c020391000788002d007800b2211144001d1980700326030308175014054800c3d400f801400c5111040c04000c0c19900c41ca5401d9100f01141105402c000d841002d0b0540d0030704115000f003081d11a00b1030b00075194800400d40900e50001028060b044030713004e00c2901c07800000a0554200303403019000314080c00c1900429072004039181c82020f089010901c1c28910b1100084d4400b510001048105941440580d1604451080c01c0790708020b0194155000084480902c180000d211207444c60a01c00c0343d483c0d80d911000d0b1402001c5034050341c3d0640d003001d10304010f6441c2010181c0a036042c0c850032050300c0712003400020840000781d8030250040380c40b10410010301401054200c64141c060750b00480c420440c101071512440303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 389395989 1250 389394739 389394757
    0xd09080304060f09080d09091d06040b0421030606020d030506010210090320060417030709030609032105061302092202090402070b0901050702032118010c2007050105 73
    0x83c10a00300468540700d90712440080c0448000c5e40c00344030021100807d03802d0745002c0c0e159071a00f840081690b004109068500032040c10300500340799145d95580341c2c4103002c040e00c1510075450600f06150321805511352034000e80a19180005c0b01450110003a06104035541a60241840c0c1006c21440b40d0f008551b2070070b0308405003800112060344d4902a198801c0c540150160400400642255580005080350140b40035081d200060342c440c1001c3c0705240300440d07070400014900042000000c4146d00701a81c4544681010000402c407000c2c01b46d81c0802800f075510013035807548240045410104450b0030681e1030300f2029031900c6812408118030f240c940c68054041401c043c40000f0015031941a214107002c010000d641d1400c2c9410500c0014100b903920014030351a040200b008980000111101400c440d9605100d400501101c401203003002840a0b04810300c60200d20000030081c410b103841c0a489454800d100c652110009c0d16003003007194103140c1b41d40098030031310140ea0450181c6840c0c035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 389397239 1250 389395989 389395997
    0x1050f04060222060216090605060f1c05070c0b090c2220130909050c13091406090c0103050c09040b031c0f03050c1602090606090910080d0908030406 66
    0x5203800c2c03040c128040618040440f19405800120b81640c0c081454200d071142407400e0000240c6461070750046038201d1298941c031031401c000c0482c0c00800c0c60050005a8251040307540c07000f6166506000380e6004171035050026241c40030220410040d8101c544c0c10040d103100510700e209088011452054440101101541018049080c00ca20035081880540c1d2008440d0800035007030f2814402c1a003081c054003096002090012178041d07007500c1040400da1b0800010064000d100d03041c402020b04251501200585907000440481c00d1540b049080c030454500a294920303055404504011440a11904040c20001031101e500140c00a903004800119000200503100e0307000246071a12003203044120005650445000c40c0d00035081c1e27500c3d219251018819640c0d82c00c0700480c60b103d0100c5015aa1806403001c0c005820304255003584880c000e0300403464026010001484840c048036200b050380959241482403071006d100a80c1048894104500140e040c559a5910390146001d030318100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 389398489 1250 389397239 389397247
    0x1e03020a03030203060a080f01140c0f070b1b030f16050c060a180c06030213050a0e0f10080a0c1e03030804030c020a230307060e01020307030809010b040e0d030501060201050f040602 80
    0x41c0c6ea05101080104449822505603046680c1d441c3d011303100c135540030702e03e00801c1c10004907201080c81c2201c241d40714000d03285103450041e542e1042c100a0250000c00100400d440400d40d2080e440c00440c02030705490000c000c0c03446c1c40030380c105105d00a080d241e800c12074140060b60100c0d80000796160020320a54001c2442d4980b24520003019088440150081c0309034840000c0700d54150b0300610f40d0142500c0c030a041c80e030321041840140700940c415503880843d804006504101c00e034154503001048074003c0441103555110262030000155403e48045030016010000c680880c4003250030b0840070060404114515140603106813030050002c0d0620940280d0101156a04084103018050800c40180300d050540307545002c4040300c80c0c4040c042d11032a04041081c1d402400203a201d220140c1c0114580340165400b03d0f0240005801064250340351614808141c0c0c4034060082001c2c1a080200050381d59080d004040d160107900c10010f5901d0725082c440384001803460550301c00c3c0c00040c0542d031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 389399739 1250 389398489 389398501
    0xc042f0702040b06070309090c0906090303032a2a02030703170c07030308010509070327050f06010e0403080c03090d2016090e150636041e03020a03030203 68
    0x280c210101d4941d4000c0c030008285c02015081600b000c1a500101410019030845190959210086000355004503600a03401c200103071003074008039500fa50250034030a107003140e41c15a12100d0b0032030a101001c01c110090422180b9645c90b050480d480c00f0409044075064142c000c03d4441100d0301014003c200d064034442d4100b0288400c0341c2e012800e410488031965543e040007004c50b1020b00541e80705008030008030340d01030b11038050291580c01030b03c900410030b0700303143c01d0481010741c9440865403401100d40700d5402c039005121060007080303902000c5119140c1890010074245000f803240010360024814084600300000f1480480b09043c1804c690550b110510241482407903929802d50b80f048644040340728807980055000c58501d003505006107640d0000094440d2200e640303102030241008001010791800111061000f00151b4049040040c44807550040d01d188100b900369005503603042c4010860502080d1829910140d561030340d0f0380650b50f0080d15410b0314500602099004004654 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 389400989 1250 389399739 389399741
    0xa0f03093801080303160e011d0f090103060b04060503070311061b030310091d0c060a0c21170411211524010f0c05070e04050c042f070204 61
    0x540445a80c01e600c250341e074500105507a648116404108642e1805507410194000c0c440d8000c0840140c60b106c58811340f1001001406400300c41032030b400b140003080b4000c10f465900c041d81c003035801103d020900200c481c0900c000d56000f5070101d4040d0303001d01000c0022410030094000b400c802241c140b03035a00300100103981d41d00461039550689001c00018000b2160f60000c0c4181142c426010a100720000400914140102e07101101003035048030301c90040034640900101050b91706800d20101d00c181c56180d031050301170550604d1000d083d0850751803400c00e0708102c0a416181842c01030384d005240907614010013049811489020321380000c405040000040b00c0d1a01c030101c50401c440302100d41450000c0c2e442801d80e4139070000440c1c0c880e080140140c0342d0b0540165441a140c0c44500a41ca05041303079510000d00e015a02170090794008180d07a11031f030140b607008a01581c018208414000b040000301c4803d1109219003146060010300508601d41000d44803000c08200c4a84901040c00824 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 389402239 1250 389400989 389401073
    0x20a020705040e0c0907050f120402210a050f060705040b07061b0302040e10030807031206090c0e12010b01090501030c0e0405010905040c06050405031c170901020a0f0309 75
    0x10b51042c244401104200400211805410f00854800c5056254603000b41e485115280c0800c0220004001086034644990540b07508103101034944900306203c1c8040c9248004851592280fa41050b40540188241080424409448500a4003884c14010300c00360082c4202e12940c12100f4010910700c0c103000c0d543d8000108034a0091800150040c0080000e0013980180140682d400480c0042034403150440d40e910262070384620214a45030294130242c822142d0b8140311202d8a031100300100350400d03140500100c008168a50380c2040c8040410454a608814440c2900740e240c03074001c1d0307981d03a40b054468027280c4083c240060154a0340703004035641101c03000040d82142c01c00703000041100d150303404a841030b8003400d15a22120303150b400449091050340325665055121481407810600355a802c0e05000109081c207c1507003203107680110107040101c07082003d5035408140c034885a6003202c00a02110704502d030403c101d42c00c2d580c42217080220614401055011582480b5020722140590 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 389403489 1250 389402239 389402249
    0x21030c05030d0c0905030d030e070306051b0a021507020105070903110109081605010e060307050a03110412062a0219060e03030c0d06330e0d151404080409020a0207 72
    0xa000101031014080c4c84040781e481414040e02c60188580605072081c4078034a035114100f00034000319451525042d01401028118281e44040058002045640c01c0c00600118005070094202082c02e1094086501e070010440c0056904000070021203542c405c02410a803944019890b40604440e001202d203244c070358000200034481d81c0844030402000f50b901c0d4040b140d0036038034102583c4030041444241d000a0310780c0340100da401d020404240b0b00940202c41424004d01070a401c0503950920103c020700e00403810f440ca690340e4095254211a110901014550000c15000022907170070300003955100c40307501070025809110b082d841080000c0d0003407070100030030380c2c1125240e040c00070a500c11030f030010741e072980518030b0200c0c00a02c64043e448a040d515204d600c00c0b50310300384000450795148400c02c072140d0422030090403030a01d82e0303150b0f07028044060280015850344034010704050110351643e1040d20300302882004000000344400704603010744001c50001768503010481c0080e46480c04a40213 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 389404739 1250 389403489 389403491
    0x70305190608060624160302160e040b090d0507230106030c0602011a060f07030201090203060112060b06090603040224161a0c040531090b0121030c05030d 68
    0x7a981400554030380107100403a03d08455081001e1074008080c05c21020b520649014007000040f000c001c0c002d203034aa4003c4c0165220b40e0080700c0c1d4051202d2464100200c1c8086041c140401d00c025003c03040d41c0300000000a054000704108050304500800c0002009016020303250150346403110420202c040c5018001e124003901c03847c0903003089829014040c01580307401c12512150148244421071820301030100b91070020a540c805d111540078940a505664803181a01c1c0103807810041ba9009002041c401ca1200050f890408113880c3d206d00020300c5244180b048034003c1d941c000031a60080d604403005821160910801e265a09150410747d0b0542c2d0040760601e18500c003c500e115855100e0a81101d02e0400000d081c40044010340d01208d400c18148001e2103141007001020b50b5000700c07500440f1144034a044402c4180489001c01c00340561141002c41c2000540f245e0b0700e000d082038003142604080040a001200c101c5100302800f0424920b0a44060190a00440e1000601c1c040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 389405989 1250 389404739 389404751
    0x20d0f0f05040314190c050124080c030a05060a18050a03020a03080612150a1e06090501060f12020d0e0d0c030f020a080d02090a05060c15100e07030519 67
    0x184000400d030807101030380070413024140c40c40340810603003c981900c5507803510740350038940480b400c0f45c24556000d42211550360700c600c0350380112500040d08680303460b01d03d5070005c0c0c2c070300b00000542000c000441c21806644425451000100003084083d48094800000682c01c1000f4280340101f00d00150003516070b00031131451009040d40407802400282c02626140301544500090113007000750603c0c40311940d042004105441d0540140346038000d10aa103003c514880450305030420030001c02e0f100000140d94030010440c130f206c42c2c00380c1c0d03004004606040ca60b4003000d843c0078000007500c4501502c2c241d4001850000110716a00035810440045c00711500151100c80190032820040015004601040c801444440c0300103905060325500c042580d0400b04003043c507201a400c045490b640c012000e101c007080607103828024000c500744107001424a100040c2041500e90070141118143c269071080c00e0004a60f07404205800020910700020599100200d80842d40d045070034138000c1d641004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 389407239 1250 389405989 389406011
    0x712020619050301091518050c2505010507020309060a1b23060604020f070807020a0506070317010501020303070504030b0403210b0102070806060d0b280204230f04020d0f 75
    0x94041c6040e103108620070025140d0310703840b0b4400a8480d00c40d000d6040105560202e646a2a8010030f1300f001d08059560304010161103001c00d00c030212b501c0185180c0d89000541c0c117014003409880e80148690014602d844010300100e01a4450442c0d03500600001000c240d180040505030a0b5407150800e00410324040c7c10744000c00e100420454040351880b17280c2c00300f9041c0c5000d20894020560854945140001c01c3e0b8510b40c4a802c01401640e12051980c0001016120200107003800c2d8800d5407200700700d50884d00403c0c00d0320f60680041e41113520920400c0070894118045605803500500c0e011203907521071900b200c40d003840c1030505040807410904007805040c242c01c400401d00c4240c007a5910241c848003000d568803411200c60341e10480151303801012803a54980c1d80c2c0c0110401d000500301f1101800500e061028004440c0c00480d40010200170084030405c41e002040c4a000c41110545840d40005480d204c0d10515188629800980f64004d6a240c0e0700140c0c14044240c0248004800c074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 389408489 1250 389407239 389407247
    0xc030c010f0b040f0b130f020706050103030305061e0904022b080c0f0a080301090b06070501111306021f052a03060a061e0f050d15030210020f0712020619 68
    0xb0041180282e0510340504020400c0c0e0048001d5a0b5000d810900300b4511410000f000e0444840c1c49000b4546c20480d10000c14000c1c050180a10b0281e10041060300302a420b21480c3c03001480c2c415504404041200304681c0d6154409400c281c040303071902c03034131004441940303d2000d2140e4001c962400b11045001040040300203803018480d104151180c1000b0740d41d2040e140d205104000300142c408000600940c80c2a9102c0301e2a5180600700c1c90a100866403002e0071130302403601c80d441d594000b01d010030f00311910032040303009416544050200c4203400341c025148401c044402c1040707aa2103500113108040d4060341a845403060a044c600d004031107030380c2c168040d4070660307816000d0381c0c2c0d524000c54558050302610b0608407800030b4024800b5040403040b01d04002d40e000390010840d04225500300f5000340c3c00b0b00b08030b0030720039400040400d00d144104039540401c0900082950000c00703840000c07000100e21041120361580c48a006003065100265552261310310149240706036031401c00203aa40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 389409739 1250 389408489 389408501
    0x61e051501020d1d12030f0d0209130b09070e03010b0d030302040311012102071e060c0f0e030a030c170a081023010e0112020a0f12180201050c030c010f 67
    0xa80030b40b41c500340040011990014490b456540809803130655400c54104010303410590441d81d0142c80c100f00003280d9080381580310743c1c50718004172740120b0712641070b10b880e8040d5242000080010003001c0344845c085603070b60740010182014072060aa03900700c0c540b4290044001c0c4900240480d030001c18a2801030000c1d00103020560301d0401128080d0203d501501c081301c0f2800c0194400d0a1040443c8401c2d0069403008500f190410341e0b60204d989204216000d035100d06100c1c44010860728000407000f44188080d101020401c243d40800300c0042d2404a40c0501007a050300d400c5017825060f0801e0b202954210f234906011200004040003801d600400150003040318460f0000c00030b51360a005610100300c0341c90240c3d44a014241006150300441801c11079850605001d192954030044e40000c80e0861802d00004c030b03d0226482d11226448114003600d80001c0740c0404c00e11400c07082003ca1222450700003810f000000800030080c02041045d69805400080240042e030411300410014101c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 389410989 1250 389409739 389409781
    0x60b030a0c0908060106091707080607050406020c0a1811040e130521030a1a0a03051f060b0f031807260f15070903060501150e0907050403061e05 64
    0x1d20301e003003ca4803100c0811000d0480d100c56a0b04c40c04142130405110807241014a80c11081c41040d0001401752001e222103445070a1130340f40c02d904c46182c400d001e402c103107443c51070b50b04c41c8101c035109012642521003540c50780e81201d20000707108850015406030078811074200400251680d4100508860600445415203201d00150744038800c591040e00410003102800550442003440001e032440840d62018000c82031000c1000307010220000451012a4990800c1d51503401c030342071020b02036a0403040c2502c00103050104010103072618894100700d003d0041d60b500c80c0500080403901a0102015205014050070107540d111682c41038010412108110b903148800c140c0014501c600c0b4010491000d03800c0c0400140040100f441042c2e010700f0001004641449105400400410014880d20307018194070051004201003610028000c401080c42a40c4580c00c82400c000300039a11000741c60480790b00c10b20124103240c007840c02d01c80044e0140401c000091520041210403c455040460303028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 389412239 1250 389410989 389410997
    0x11031204022403070c11060304030908060606090a050f010201060b030f01060906110c011107150e09061005040b03190207050604060b030304270e120c010b04020306010c1104060b030a0c 81
    0x8440e003030400c0e8002207080400c6034058280000344d4411300441c1011005845000018100c0c20071500060094005440690001d9100c00742071080102c20001705402c600700712820740c00d0524880000e480c844072802030f14000c0e082c103070244246034003d4100d100034042032101507480e0300e000c10500d01d42403000d100b990005211000001581d070b0042d004d880320100580c01500d071210b190b07001910b08405842e44450540328240000038042c051103401040c0300d00c0741d513903038204a818900700030089102030303d41841103d01600481341c0e81c1d041300803034003100c01c0540d03034135200e0392070400c00f0000015000c1100c1e0040e0002640c001001008590070f4805c0744180c804115907409074040c1340c0d40307000e0390260f8464401044244030b01055810b81d2076040c002000740200d1805000499241450b0004605102041d400b14050401d50f0f000c0c01032000ca9032064134114298036084000a184008202e030190107001da10380314442507210b90700701ca40502107142c0710540d242000080308000f04603a00c070794070000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 389413489 1250 389412239 389412259
    0x120b01050604050f09071215060311190f02030702100e01033b0a050102160308010603090503090108131406011809050c0f0a0306140103170a02120a1103120402 70
    0x245007507000e41e400d0b01e80c0602842c400701046014000c880c9006004a42402501c011980741c80c1c4442c0190000082c8401d5154079003491300708040c1c10758000041c01561384006018040c042e0203040e05002d4801070340e02e4070940741200c9220070f81c1103100303032003010750441c0e00e04080c80034007900001022521002070b0380411002221880e41400d42c1c80610421014008500b80c0b0035402c424000c0c801000d09003101600c0c50300729113560f403a00320fa12044042e012947c42403440e6040c1900080d613a80140107904003400103148070342c1c0e40c9840348105111b0070b050107019000b290a200329003410919155204000c00824028038210940d207070300900c210304d200e00c1d03045070405104040c0e0140300580c9034000020898203a284041210801980400b0760300955000b20001c0442e070382d40106112840041000c420315419418420520f00c1030785030420307810b00308005045509900290042e003554220004035194062103104803220702004542071424440070079004810820b0400c8240260310807507222001e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 389414739 1250 389413489 389413499
    0x3010620010506030c040b010513150e1005031b0c0f060f070207060207030f06020702031f1a180601051903020904060f05090c070602041203030b0a080f03040528120b01 74
    0xa035041242d000f901a08621700d001e02034201074102c400d0804050400c54181f80c85000d8007804110303154058034001c0701600200511940203a00240b040b1000d0740d41001221840c1c0c409840740c4400340000e0400702c1c0c01a0380e0760380c41501105945055107035005807461100781c00b5003160385100983d16030b41c0004100010034403440c000201401114050f0b00601151850354a9a1541c440520300c1540c20310340811000b001a0790500c2000754941001c0d05066140022503440c0084548003047c0764016445440c03244015a10550860f20380090070f02030070020364503807004a40e140601a0030700c4900454010340761005405802400b2404000c2c6d034104009035480d002d00c2d1b4214402e101d00c0ea0448905004510040d0611008202660294030094a459079851500c2e00320000200c1c25000290340d4605500350349032002904001b0310464009140314284a2640794417485980300d60351050012002e0905a08030030b1108803000c40e030201c0b400c460181c0d15102080407480718081210700c0c2c0401e40003c50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 389415989 1250 389414739 389414741
    0x1140f09070206071d1e03121b28020909151029160305071b06120b060306060a120905030a14130306020901050705010603110a05030a080a20030301062001 68
    0x70303210500401d420510f103507812690003003185a00d0047d07010700948500d588060501c90041900c0c0444460b000b540c0c1c0801c244c2c1c182810b42203d0102565141d4001324000e01c084c07481201d0050b6011511060140c9a001a103031511003050b040e142c40031040820002c4090170b9600d843c04036081600e036051030260700d41c104514090885c0707403028102d40500015a44003031702508500c41174468104680f5140403903c4280940400440f484000b00c0c5018017840550341c004080015001008c00501c1003511610008405000c0208880e004134030106801008900c980404940c43c00903507010400c005060610f41c1d1203511040108001c607610501203101e6040d043d084a0b0360700c1d402c0021401d003e04603607454000c2d52002003082d0401501707014810105100b841004002e500c51440110380300b60700028048411070a0340041c0c03094101c0c0c0001d5001c031b5858000c8402c044110b1801d001840075200c8079084240e03842000102d241320220002c10302982000101c41c40034641446e4400644404221038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 389417239 1250 389415989 389416037
    0x12010902100309030507050610050109080a02180604020f030f161b08030a3e0a090b0c1f0207020f0406060c02040e0c0409060b041505010801140f0907020607 69
    0x303410400359021003048921030b601881465111749413051503c20107032a140d14108050728221241384a00381d04210303940c1c00ca141c1500400142011f0001c9101c940c000a001c080001d2900fa424441100024030f80d07652070341213504001c5a40b61542e140d092441c028010b000084641c14801c080005050030700038000d559420390702c00c0501a00c5e100c030500c0d0b6510700b0786400140c28181c0c480e0b140c14468801c103c071081c0b0300c0042e00d100070403054010340c10008512001691041d05551300820051080b9003644000d64100717907078596646076603070b14020404034945111810b8500d094140050916a0f0000503001080024000ca17102030070002c9101c208012104a8454400810091003040006040c6608000c03607001600080d00d01c04008140414203941d03041108442965640c0082d007510324040c411100146000c451160840d418000080d000f4003040c01020102034140076295881e40c2e40e60042c690f01400034014481ea400c2c6000e0103075980d04140c540c40c0208900b40296002c94100320805 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 389418489 1250 389417239 389417243
    0x320a0506130812120a230f04030f0918150305070b0304060b0406050a051009030c08030a11070e1909020310020318120d02090a0b2b1509050603032205120109 69
    0x3801c50354441904010003010039500d0301c140e80c06d1034004649404008882103102c1c880346410340015190501c3d008003001800c41460050100b4100c0c01e00caa149070500d0362090070220840040d6401c00b8840c07080300d80401d43c2c0014240e102c0d24001103002012140514022403043c4c1e404e004107a5003000f00800c0e240c0b14080c071a00514800d400300325510300749144209400d21410803610013510b03a114102d00d4481a003000541398000107510001a078041c40d84038149001c203015082c15420403124200e1000b002c0c010398503200002c0c3c3c420a840c496980b1600d0b40c254000c040310310000c10402d040c0040e40040b5142000d107208906034540c0c92101280d2070003024a048410380ca045110396402c0000c7d0045074607140c009910440c04250b0041e0040104500c8840340007003c10000e62149070240e98411101204406007041e000211075018410794406a9400c1c80010034140e85040102c0d1640c01910103544000341c2504100910060b81040c03801074400c1501c08040d242100b023061420399449500c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 389419739 1250 389418489 389418517
    0x5030d1d010e130504030f0e0a120b100e01080a0c0e0f0f1f08150124030c030b03031b011a010c0b18030a03020a030501320a0506130812 60
    0x221080c9610862203140a81001400c6201c801440110f10b411901c0480e0100c0100721940d60000100d6008191b80c4800c00c01142e0003200141000c1d40ea48200b001108000c01200850b4045807003e5000702490000e4031810020002d95a07407a8260750742c03807170407000a80c0c03200301004020070f440740c00410342441a8003102d0b02c640d45817a0010505107480008080703014555280c1e0b50280c2145280303030322100401078903008140c4400d034010080d44140341a80010a03000740c4225010324184410a117824101580c117000552444901d03003030707000e008102221070345800002500c0600b20489079035503100c1c59944008001c04025120200000510110f0303e50128410368084000aa019a0401c1e40680b00c810714140c41d0445008036460354120340003070004281c01044c1d644000703a05116082c0100036079880038400d1044181035429a03a540514600e0025005154031541c1d1100074141005200c0600300d00c1d03035500102841e00b204011400340c0001c0e030040541e1009051021000d03100041d011f014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 389420989 1250 389419739 389419787
    0xd1b090f0b0316080622050a0501080a030f110a0b0103080c0708060114120102040e010e0a05090c130b011116180525120207120e10080105010f022505030d 68
    0x51313601c0b03100148020b0f84021a1004d002d18500c292411840302c2501d200e000c074850518143d42402e44105800065036640111080d41c0441e90158203542030084d142040c18010444400080c203241c0c141da0b0241c8003110704400003040110b01001040d40300c00500c1078400c10381d03c1c3e41c81651203010a1040010f11034101a51641c10319080c0710018446955000051a2a40e50090089241c000b40d014080da695007a040000318902130003904c2d84443d191014010202c0e850001847d180e04c25080710464650714043c04245901801001e001c0c8000345080310044014400500506050740c000d60682c210a00c00784441e503041400b68a006001c00000a03541418a038100300755042203e400078100040d0402501000100340300170300e4060700031014007601c2802c0d64000303481c013807000d14010300401000c1d15503101d0035070000c1a14191502441e048a1010b00c20201b00e2038074024684403a400000d6070110604490703040a46001c484064090390962407000307030b080c1d0b9501d2101c444410000c0d5085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 389422239 1250 389420989 389421031
    0xa0903021b0d1e0201140a08070815090103050309040c09030206030604020a090b040b0403120206100504111e0415020f060403121b020a0c05060f040b0d1b090f0b03 72
    0x3215010000d0042c001d904102600c0e1112402e007000400e180d410100080b96040942d42e0121513000080b102ca50701900d4440400002414800c0c000c1445c0d0420207298040b0b07038402c0040b10302161080d80102160301c40d507168104241c60360310a241d030340d00c200d280045c915102d601801e1040300b105d40003881c8601395601c010900004c0d5100350b18001c2040141c107070202d980011000503201804128004e551154158a445074014040140013000e40d80803070100a0b185040e01882000d982050b10045440c0300c214002c80802c1c01194100700100300060701440b80040c000c8080c20403504032800814810502c2074007a611400100f5403100d0540000c800900440c1c05404403154101103228001681e180c0d03000100b0180c01010848001030300407500060038080d0000650010b42411291245400320119540e02076204600c90000c2021012504109100321903010310750441140200030702505400344004c104e4500ca00408607903281c18030011410350940b5060340c2c4100048c2091400103003100b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 389423489 1250 389422239 389422273
    0x1f0f1103060f030f150106030c050c031602060405040f27031205070c0b04081305010e0102030a1b0209010f0920031f0801110a02100b010e2205010e040302060a090302 73
    0x250409030140700d84c00c4010b502c042c0030003210043c516440b280e0358195051100041c19914421100400c010042c400c2e4074070f441c0040b040f60402c401d099a105026001032001c56a54011580003640c030925000008038800400e401c405680364080c080300d004101c40301000d000a80e15120040d0000d08019420002549181d0081d50000ca840c10141e05503030544d9580c4040c01c2007160111805140840c00040071185020749002609090a182c05104a001c2c0001d41c2d0f8018941c581c0100f01d0144d100c540140c1218040010160700a00b20318103568550450349660003151049005c21407400c0400d182c08100442001c001c50300440c030581c0765880d070640700408046403880700c519000e404200059034010911580a82c02c0f4410710007a00c40070314690280c00c15803048a69a00c15003480d4201d0072aa0b8800021440e050084072000801d6040b1160320241d903c081c0c28150b0010320b8a4004603001c00b03c0e04405200b14400d070708a8003c1d030b48544040056803880d0400a015a1000c11030301845500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 389424739 1250 389423489 389423509
    0x4080708130906120213060602190c0b1b07060201020306010903060509030c0d0905010e01080c071209080a0b150d020d120225051f0801050609121f0f110306 69
    0x14101d5040d041ca071034100040440e02c082d4080683c1084225000c001c5090081070014940c41400003084010f02e8075002a46440c521606070b0b6202e01b804d03da2008020344552601f02a0030041e461540318644040c5803079000078081c130f042c0007510401c80005041d600c14000c480c850f0fa01a95409807140c510341d90b46c0c7c0603000180403228640020f00070307003240f0340c0104a10b0000d09840d50310b08254500d801c1c000f41c41146134520301c504100c049400c2003030b28010700c42110b0110346e010075203001c40118660100c9149842d81c20011440c010100558141f001c04d9038400d028040c480c02001c0d80c03418820402210380309000000b500030701040d00c0c40001c603c421080440602803401554001100d8804241442401e0210031400090840c1c05108030304081000c01d1407184406883c45866210170381c054484a01442184d00c1540001556031a41e102c0050104940c1205400c4401c0031182c2179a00800c1029100400f054a240907040180c0d40c0ca1070007440780301844c0b405c0003807541d11408248019851 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 389425989 1250 389424739 389424757
    0x1061703040521060f1906030305070809120601030c06090f15140904061205120705030d05071704050c040c030b0a05151e030f0a09020913050f03030703060302031504080708 76
    0x7424011401d0f501018448103108102a641c04142d03031609442200f00e0752052140f241e001c514100301400003d8120048035170543d080502140c840e83c615002465400c000030a0350b125018010000040007400112002541d079a40c81c1c42101d69100d40c050418000d070f500c9400030783c00d4840704812050380591180203200300b02d1101c003850071001780c000ca410f03a901544151049010720740c00e1400c0c0b02d4103000f40d14030a02c0040e0b01c10301e0a020754450a650f0f000b001140200b00750381c0d0003c101d00e41c1c0a1b2124200c0180c0025803103050f85806d092050301c5420851005004a04110200f02d0541c8244550144550014000c00d441414201404116000140d1075402c961082040c007040020345449800d8602480007000d50300e207002101100034000150000003410706118603040103a48516000f80d000030340c40c1010002c000b49050407490f08403042c44030380c0603020000505c0701c04c591507002201600e0080c0d00b1540051020050030254410886000c4c180020a200e001c002982c10b00c02001426 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 389427239 1250 389425989 389426029
    0x17060d021309140f15010e1003140a0204140a0e070f17031309020418020408030306010f0516030e121f15080312190504120f0507050f070602010617030405 68
    0x3d4108154501440304102d01003a6006100c4010b148844081c0345014140c10202904542080100c181d1659100e0000411030703031410b02c54031030140c3e04001c1e4008454000b80305002c0d150030310840700002c040c29a55000e4550400c101e51445400005501e4103c60b01c815040e203403d442c2c007000030b01190242c0040740c007501041044806104200f0039141c06044486001039070780b0302d0080020b2150b0b030080c0c01001d402d4010320040206940100c00d50394000002e0a180e08403c00b03500d0106c905100d000e14003880000b21410944c1456030004040d00380c0030042e01c1c5408078586c1601519515801c0d001013171301e4019075003608102050aa0080c0213818a80c0c440340840c203031140c030704a0841d007014409607460f070140e208003c1c0c0358034949020f80c4c8210001c8000c100a040c00e0715004a02c0e01032084203410b01c089162140c4032203114004640c80d40c1e40100641c1d202c0c1048a007020b880328410711900005609040780801d4240440d80c9041070f44400000851909203020180051400f41e5503800e0140c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 389428489 1250 389427239 389427263
    0xb0609130f14060105031615030b120f0609030f19090b041701060b070b0f0c040909080409110306030a0f0c0b0f0306040c0513090519090317060d021309 67
    0x90400c925100d0082c425102d6101d1040707400042490300b941640514400d50055040140e603d0302d007008074094030409400c403840030035280c0c401da01405030000c280d604041c02030391481d84520049071043c410b0b000701c4103035081e07a100e02108568900903281007903d54441003050410451a0043c000080c9450b420001d2041e940d03681040469000340d40800c000b401404043e05a030300d02842400d000e4aa1034654600380442a00d070003810160092500301c56401503404560b4500c00c60096400030881418180050349003072402d034076984c11134810407801d10b0400d4155941802c034074050b030388a004003800a020400413516010320380941540155981c0e0700d0350300c01080200c2e110004080000700c603410650740f800e2060510080300d09211340e51080107818404000000031803510681200c003400c5020a1a40301c0401104255908882c50a4041d243c1f540680400d5008008040c110f074180001d5903095480d4814400384580000c80254085c0340c42c0150f0785e03000d00587c02a0303e031a018408031480 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 389429739 1250 389428489 389428493
    0x6040b0f0f040f020a170c070305030f09011508010207201c15020703200f060c0c010b0d050c010801090e151914101a07110d080d020301031e0b060913 66
    0x2241e0020f91041d00240c00040f80040c0c5c0b070360300d1b442140c0112902c400c1528191041e04d00030010301005d09211a1025014081034400c2002d401041c07903902c212051005103960303010580d00035409240f00319551064150a40003448809454842d041d0014252981c3e120b030048a00300c04000910040310001038013006500c80130060f102902c101840703611011808041e0400d0031007518092489240075600c6441003502405c80401d005400c0344e8200107513a00c5800c8118410302410300e80307802503000044500d00d102803040014084d070111200380c03641162a44c86090103400c2c0e441c1401a444550b010b5541c4100c0c2654140e201907010303801da280c0740001280c2042e0001075032070312080c0b184101244001c0c071029066019482e80103003034000100428005940c0304800341d01495501400800c0328092200440d107540d14010301c1d10768003007041640e40d040c08540b100250820b01054420a4482d52802c440807409140d96680c0c0750400607550181c0d58003000c221100303800411a030480842d491950740 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 389430989 1250 389429739 389429741
    0x31e07020118090213080102031015020c040f1512080f0901051902010603020405060105091c0206040b0309030d1b050702040b032103043008040c120f0b06040b0f0f040f 74
    0x7010f070140705005039070f1315000c3c000b140e800c500c00e0b0468032844e4810424008145041a42042102d06050840741003160480050b0f0410306940300e0350380c02c2810038400000313030310181c4c2c0600c580650452480103503030307200c0914950000f01440000d081d403804104080d00c0c004071401030040840c05140c220315110708c9000c44e40c07840d01802c40701070151391500382c14001c501d0240030f50f940c0b2441c2864442e08000703002000686001480e01c0744c1010700d039508407441c195252001150050301101003129580c1c28a440525620b9105400c0100308914002d080c0690070310701c041040700101c03103076107682c03c0c10080d80810000300b40e0386015961502ca08101b4145a1405400704500f4020740e0200c0c0351286041d08001340c1408102c1c0c090740b82c41144086c6018071700071503400e50030140030318075080010f6a103e1400141c41d846a41141c2c042500c1c401b0080200080d510984100d544030b80061002901c8071800c0c44166800b4182e00c0d80e0111301221000e40c00e003052a0b040c10038010041001c40c0500c41b00030050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 389432239 1250 389430989 389431037
    0x105130b1f11061f06120209030102130312020703080d02030601020a020405100302040b03010605060f030406090b0f04030215090601061101110301062604050c040c0e031005090708031e070201 84
    0x2030080741104000c2c903401801070005903403008030b4048420101e0883c0031001d64420084c0181004c1c021120000503000301c269054821141c07010b4001c55890714029024100713a43c29110489020006a074650300c1d0a2010881c48100c030703801162142402c4810f900d0802a400003000d00b411841554a02c201681e141e000d22070050040506890010381180180030503100004400e034081c3c4e04005040103941c840108584211541e0500142c4070703110f600c3c01e500a0000d80e03001600d603115003010320112241d030803100c1d406144a6007c607503042150918090785c0290480302030009410040040224501030a20140d0148000c400003c07110281401880349400a0300400700181005c03000524020089411541401c20413400c1161443c1c00c0c1d440e00e0f962400711450500507921020b020a07090b0007041e5182c000c003401400c0d2000130340c00141040040008640040b205c1c40750640c00501c0403c08003c45100111541c1e802440c0c51030b0070300b40c401c11b82c061002241088401007a008042080038188 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 389433489 1250 389432239 389432299
    0x27050403050c010606090e011202060c030301060201050105120109030207060f0201060b030a0f0e0a0b0103060207061b0c03020c12030906030c040e15090c0a080402090c04091509050f0105130b 84
    0x1502c0b802004101401c450168000c0720a020002034107100115810b0551411510320b541c81ea16902c0d041c0c1702081e20390088020241c1c0e03910005c400410500e4041d040141030758803e41c0c04441c100340d1a264103007610b44903900a0b0168002020601019208088002480f90980004940075607a0150081785034400c982c14510b1030b5131048603030081030700f6006031031460542600810b0003445a495016504ea018840145100c1e400103402c0e04002568105000c1c1c20401000d40e85045418100902220b08031002100140280400d1099a00c0d117260420711032206400118186130b01c690600ca07550b1300241130350040140030710000403103000e8060580d00c501d0000c17404240b40789405040c00a8076101600d03100a91105101034008142e01038038059000750120741c603040c0f0340c071004015420780c490740d00002d01042c1011214000035a9000000b401c45014080030000c540e1120f11401b003c0000307000303a030303070001f0448906204a0130b517400c60b0101000041c4100e0402c0c10702d40702e550414410007a8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 389434739 1250 389433489 389433497
    0x30e1f0c0b011d07030c020c06040803090909031309091b0602210f0f180306100e090d05031801060e0f0711011104050111010f09080304050f010c02030427050403 71
    0x4514108840e10306501d0041412007070b1406001900030f100c0c120b00d0300c02440681056902d0a00b514054820003000d421110040c110a64803600ca0414503140d501c1000c2c86401807941c540441d40c0702074000111900300143d03403082c440c0103041108900240c40001c0058810008590f00c02080011178160700d401404940c0040240e40b0015007200c0d00090001c2c60312400400500c4558900b54124003250700e40705807603201c1c6070b9405606500e14140b0259a61315a01403081908203c02a00300c82401c1d01920106041102d040c2d5074145615910111010b90100249060002c9401c001d001103940d1904150400046011030b1036503032909600c8021500c41c4040912001030115061f0090880025500004008e000810421200940ca480341d44901810000e08074040c4800707400039401002544c0383e6100034000c040c1d40c0e0411181c0c41c1c00984058446002c0d1000c24100b841051048a0151b60550040c0d400c051403d81020085010340b140c61980198003500f07180c1c64030461150701d100354402d840d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 389435989 1250 389434739 389434757
    0x408030318060105010905061b07060f09090e0c042d050601080a05040b1f0909080a03110a08040803040602160c06030605010e031b03030c0a150b1507030e1f 69
    0x4016240181c084038200459003241005000d80d036131050f10003094460070745000b99201e01100000f418548810701c0900035026100300490065407004664414243c15540c00c042580c59040240880310455845441c942c002c8880740d009051036033281d120035983d4044294071402c0100c013110b1007012403042804440d030710030400c10250703084081d403070b08154080c204000c2441e0955070390340401c070058040220b040010080d41c09400380d10000030064200c041301801940e00d1840c007403c05801541000c0c0206c0c0c02c0c003410b1810088a01c05558130140c2070303510406a0b40350ba840706c0d903a0754006001075a6041c1c003005403a001103200416075491910a04603483d001c0d150420080440e000c94100504202d8a4500030806941c0000c440610b54220403031f0301800c0b80c0400c000b03895403185c00c51003013180c0118581034091194080c01010000c803030301014030041101900704020280390308c0b1680c8034036038288002000700b440b030f14000040310409411203070301403000d403c540e03a40e102e4a4500400165411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 389437239 1250 389435989 389436001
    0xd0c02030c12121503031e1603020601030209010902270607060c080a0c26090a0b0403050304050c0105030124210603140f070509100b18010e0a0806070f0306030804080303 75
    0x110070f00d80c2c40300342440c0084d942040100081e850b40300300e0a00b01c8109015035400440010000216104070014000300c0405400900e000f82d182c54007440241c0c41200c690340001100e00950003103481145030585084815a103010071074a141c000d403c0311b250410b009014800c00203074a4030501d0380340e1034291101e100504c1c105414400380c4458112050410980c419414030741c807041500c00103c520400c0c1000510382d03448100b1843c0540e04240905050705850a110615800c100250f0149028006030368007818042c0041d103140c4020304c1010340c5140c42d080c5043d0305000180744001174041314680802000724651941a0121146d5030800f460740d40c40c982001040182d003541f06290184201a040341c00840c0408d80c0c44c0c100d00c0c460746008042074000150420303480c0c01c00f5405002ca22f640161126540103914256603280700c00d86011515008a01c0d4007803922084450071190468000e101c1c0f50307165142118130307451101020050640b10240840001e4041020300098000c00c0001c6440b40b401c2c0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 389438489 1250 389437239 389437267
    0x6010c080d020a08240616110406060521090d030507050d2412230a0501140403090803070b04080a0c0f08030402012705040522050d090504060b0d0c02030c12 69
    0x445c1038003400f401c040c411644a80342d80b819079240100015220303800c80001d0601c401c082201d030001c0c40d40540b6086000c22455084801381c280b1407a50007203440d4004484542000c10703202503c1d1007140b6403040b050020994802e40007140c0c03080321341c40c0240c100340e6071b500b004094801200c1241b540c4045910a03018004412022100030030b4050a840c1645402c1e88560740300d20b039010400008440a000110140341081110b00d000c2e950060080201c0100c01001d022800020744048000a0031300d40d0004440800205640d021900030b110070401c0d03216640d5048403540b02c0d26041c014000000074281c00b02d0502c4c04411000c601032050307a03035289401c0c07000515010349044100c1c090100c40c0c1d01800c400305844100019035000391000902a02e98451380010504c0990751180c600090b02c0c082000c012003c50840750050907a12200788142c1c50780100000d58420f4040e80c0b0088100b84030044040700c0c1500400e111000c40d0040d07a10307080e11100d4482c1070070b4981c1c20400007020001142d006940c10303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 389439739 1250 389438489 389438521
    0x210020a140318040902030f0a20010e3d090816030f0b09010204090f0c0905030c2407060615080703061203050a0e0a12060e1506010c080d020a08 64
    0x3030700918035180c1d0303103441c41244040e584545805555070b0040c08046480c1008501994803002040320381e80e031103518010a083c0b84e15060601c00360214074990302d295025080c840f160600041018580c0882c668104480a500351302c9a0f0140711001c8114940c030440c400940c4014105640300c001031810300c1e00c03440c40c1c092074070394242d030039a000c960405c003151100e2202002c969100c0d0b190036040e00d90030742c030744e002e8081c7c0d420610f945450041c2c142c5181c0007a600c0100304141c242c8801010701d544400705a1038803000483c10390440040001d00780189000b41d48080141040c841e61400d008040d25854220b6145400405d01c3c510b05030a200784140c0c01c03a00c0c283d40b14940d49424000d2506080910502501802004080c0716003c14a101d034103014040c50569810f001d0100c1c6851503a50b50741c90304a000040003600c2040c82c0110007000c1e00350110f040c0050590300c00e184552610f461004540406050358140d4001606001c0b01e2802d04842c0000c00345440315580300c05460031b1000c83c410710220317 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 389440989 1250 389439739 389439773
    0x809061815070507170c01110106090c1d040908090f011b0f0c0e04200102030702040905031e03010510201902090901020c100b1201020409020403031707140d02070210020a 75
    0xc5024091786082d04001055030740000e00f032030815510b1907800c05285c09001d554000a50a03070400120016050b48003003c080d01000314008043d0807440901440100d42001802401c94942044010b1041c200f20308071203c645812301d810305001000b901e00b4000550740303100c11902e0b000d500e122001800300003500070000d0289502155032a04040d6a131114411007111140f84400d115614004681e0083c4190b0321032540140042c404079401d03280158403680320044106180d0240381d1904040008141641c2c1601c0015200b40d1804890b80001d5524a100100095500c3c0064000711428807051040000d00740110404002c1969144104000a4002031603d482a03106020441c160640056030b0380074445039010018400820802003560b400d01c40381e10340915070002600081080260740108101c17400780c0d440d45400145440c0711030301e84100791055000528480b00c024500c1c0100d40050a00d0040341400600e00600c9602054003008040d1106000d600052160020b00440d45000c11081c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 389442239 1250 389440989 389441009
    0x13050603041103011b0210090609020603100e0c0702061210230306250c0215071103100b2206030c2d06090608040f0b0c0a14070809061815070507 64
    0x1445005d00a69500340c4880d003007000c5031201901014000300c3e620001e0503139000382400d5681c2c9002440d10500c4203407441041c1c012000c000000d04603810301070507185007a500030415450160520903102c500c1c0c2010340102e990803081200002c00280504682024400002900542a01e08010103040c200004d00102c0042d185c07407254668500000410300a15016040ca04008049c2d070022071724000040021982070a0000ba1a03010b100101050461000c001c074200c48a0f00c09d2409901d040c0c4902c42d001030342120824140c4103100b0f10f9900100101040200c0000f002a07503911514013960880d070015200200b640811040d08a04c2c0c81074014032815030010751056071900c440144284568031503007080050b40c0000c03804011005c03580010417074001d02501280d003000c0499445503031024101d030000c502044002c400c0e50028000366900c3c80d4221a0a5080a1b138110a0000507845074211007034212800c4905c28195a40c031030720031004c00e0440541612410709141035403030a110741c4c1000310700da = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 389443489 1250 389442239 389442281
    0x501030207020109120f201f050318010b0303070c26100207080903030d0507091e12150c02010b12010e0604021516031e030203070f03021305060304110301 68
    0x243c1d0700300c1400b50488495030032001d00200d0b0341c1020301003440f03403640050254071204070103134046100343d000c0c49841c00c0450300038040c524001c0e00902c400a007408402c2c08108140300280d40006055400c01c6415001c50022031031781030f004000307420b507404004100ca1000780000c06000c03115011405140c5541850380c6425084201308120350b41fa4407a1451403501b81c1c00040c502c007003103c540c0a840b581031010301207075102c5050321003100183c8022901240000d00d041d00004000c05003030a2914039281d0481c43d021010700300444501004120f01050781c0e0400004000401a0030500c9090400640e0303a0002458440340020400101c4036110b510055a0500d10a040403043c00700b83d0740e4215034111000540180c0c070b00203800c01030040d80100d0980c0007405140ea01131681201000700e4030b02a20b0038041c9106203905090f0201d0109450303403000285003800b6140705500aa004142c48500c20780c102181a6071000000c40907031048504842820407540e40c0006414240a054403a4040191080c90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 389444739 1250 389443489 389443493
    0x12081504050c13120303051f0317040b031005240f0d09020d0309140117040209040201110f0f01140103050604032304060807020c031204090207111f03060501030207 72
    0x50450181840c42295140c02044015110404031124207094400b071a000c44d555000142190180044c02c2d008a41440700040300c60008010b4411103d01c2040340340801411611802c140440d120010442301400b00300118006040303001441c407542e122143c1d84141401c202c2071040c81c03900c80c2c40782c50301c102c01e40c03002c468240c1e82d440503105402001807079161118214007600002d000307010802fa410944c000c0240c0141a03105030f1050585041d02c44a4110030710203801140d42050000810b802d10004101140062070200d064030303007003401450440b07200400e0000c0c1e80d0038080c002e9030b8152039a103c081210844102030081042c105010b00d810324142d03255840c0c031900c6000c01800101000030ba8044600a840305c9a11400040380060725540c40d40e448060107060842d0a03900a005441030400c0b0860318500081c51030481e40300140c40e5401c0034640300608010303400181085601780c1b010403404240d91034401501040020340e100284030044186005012101e05800803030416004000e8000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 389445989 1250 389444739 389444761
    0x12051306030f181203050c0f09130b03061518100506030901062c060d0c05040f0212130213061202010f050915041502070810090507080d0207031208 65
    0x80318a00e09022403100c0c4032461580c000d0805034902c18118600820600a00c540b0002e000c3c68100561001c101070340342c90a444025006a03086940c1c1e141c4200700c0f20400342000c610486000800107000308118404d4030000e41400404c8444050144980c01c0903074051900200040c46448807008101243c10200c159520341c00082c0111400f401c40000810568642544003000812211000b941b80d641c1d1485813030744a0907d841680740207101c0c000810801e1424560706030400d0745c000e04104107d0f24100a202c050001b27410480d1251340c0c01c0c01410a862044619944a0510302030b894205031900e204101203200251200c200c20b524002051100241c02e0400c404002d8090030a15407610907100708507500e109402c46242c000741100100240145000702400543d448a2090061003d02000881e512410751044111991116030140c0250006510440407540108117132a8034a0711003510518200c4910003100040c3d0001c0d204205004044518000c800c1440c903118226081050081c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 389447239 1250 389445989 389446027
    0xf02090a0e060607080703050a1e08190e030f03070201050f090d140721031b090317091206070906030b06070b0c0912012003040c15120906091205 64
    0x110062201c1c00410a150350b540207450a03140c0c0900c89680e940554134000303086030840408080810f241009100740c8940058990b0840c0070155501c00259443c1951001c0350000d00c1d4060a4180d070380c25600800400c00c0c8002d04d00d180c034101c1040c4d940d013080d100003421100c0040a581c9081c01c14000e02a01c88004200e2000d404514907000c416004086201c140c80d03c01d80314010b00946201c40241d002210380c0b10404008081602d04200c1242c0c1c10094041006030061000c001440f2442c0900c0012050b600b81020010500e2038581800b4403000803c1100300358020313030026680201301304190f241d4450310403c060500c2d881c05100a180701808158030780681d03c0010140c00300000041c40034180e44054a50426008020301110190400b0701030003015a0052401243c016040000e50098800e00f243d0003540e02c0a20304143d10319104219003a840ca01c148507003000001c1c2280c44011009000d89134030640035240001e54078800345400c41d0540c1c4031000340720034082c050003030702c0c001d0f12444044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 389448489 1250 389447239 389447249
    0x5091203071b03020a02090a0606022a19030605060f090609060d0b01060c03090e010501050423030303100510030e03030a0e0106050909070f0e01080a03050901180803030a0f02090a 79
    0x650322511a03000644030000291805200250149180c6050541c0000c00c10029030013580c8001d03441c0c07501200001604c050b03000d0b07900540e0280c1142008d0b20f0744280740080c10504441c094942c01e00000001d010206000910028110700c4201402440003074480c054000790102c5031040d6440b80c60700440c00090005003207522500c481c60015205850f40780103034040950010b020501582c460402401540f2603941c10f5000842011001c00c2d0034150500d409c0c10381e1030503180c450800745041030040740c1d42195104e00b1401d4241c5a40d92043d5181040514020941032014403005030900302070042c9114014805001c040c10441084603684010086a0304510280c001141038800d64911074003400c010f80c8250341052460081018070200070031290256145800c00d000c015a88202020810324207003e06c8005400c00510a00000e0190300140340c20074042c1003d07140d0a5103041401051032207540721101c2c9130800004c0091400b0148174000042e00b00242c1142085034140c01710f020b01009000d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 389449739 1250 389448489 389448523
    0xf040207030c30020312040f02151602120c0906040f11072916030218091e0705070b0402090711100902010905150a030c0912030e130509 60
    0xc89000e0500c940794074009980c000000c0e4149003524200020f80c0600c1c540354a02c4815034040c5501514070100c01c0307990038002c240a4204544460f192817040300362580d800c036404a031106402501507041d10181c6894507c000850310380c5c84060051000a40d0002200a0f507038004903600c4403d580c51014440d0010760a84000803107aa0710504c1c84000d1424047c2d4100b401c00c0170840d00300f006044052408a1840401b14031b2003180850280d1514034407e80f00411100a060011140d0303d1280d4050070021280c5005a41000785003400320b50402e030107503a0b1031602440c0041d000c500e543c0340f802039600075a140ca4050714040c2070f5142c01c4100480640000e2003541c0c040c0204260b1441074100194000196041e581c000c100701700c85000030028004200e001c03c52803540092a4074202c0c003d20103110122440514040617a281140101700103446a024401c4803800031a002d100900c6c50f0b03940074485c1d194219402600b03410003d920704040281003110b400c0c5002c00402c402e01140d81c51104401d051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 389450989 1250 389449739 389449747
    0x30b0f04020301060909060f200301030803070507020d03020c0a0f050102071a09042301080307030c0803070c05030f071401020301031e0510050a05041e0809150403151d0c0f0402 78
    0x70002e8050309a592203031541301d00b07080b2040c041c4441da41c8101c1d14002041c40401001c0a0100c1c01300003400e01e03007001001c0305e105100400104018800650340304034103141883c94134020364001801c48501450030750069000464001903401c1c000022000350040180048880346810b00013540cbc1d41d65030240c0140c280c0b04400c25000c0042003415a0142803009000b8041d181046040102d00d01809070b001d01041d0540c800001d00a10110031078909503016520681448029110003246500240c482410060364080e1b00c4c0c045031044c4050070012402000c4d080d51020603040c54980d10f90100101d015a074410001000090101d2022007601c02c2d1049819036071800d05d041083c109440f41009201c170301d0402081264918060340182d1042e84511140c0100300403003e15551b140050380d000500c419010400344941e071500346102101d403105051080d203001d407a03581d01e443d078441d14200c00e01182d4989910110301d50141d214603020303107a0f040003088840000000184528069044a4003440d4005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 389452239 1250 389450989 389450993
    0x506091210051b120112050c0d080a020c031c0c0c0b040602010204060f0219060506030712060204032d23010c090302040f090c05040e010e250f030b0f04 67
    0x52200300141002038251004441c200e048540501000c40e401c02030104400c0c103c100002280c0c0980700d207410403503600c03102c907803c041d8a522071301e82c80c00080e03d03584107044c0c01d40425520143c100d41142d00c940e2a4648a1400503c064a851280d0150074481c1d04500114004500c00141520441d540c902e80800042e55078200464107500540010b1001c2c800014049081c0d17405400401c01ca0b001551221084055000e00700e0f00d68045202c0481040003111005020941e540c0007540c00110007010354442e141e803138401c00034406a624080307810540104040003400303895031403500d03010421110244c40f4801075000104e505e40b080001419480c050000052010405600142ca451079100810451a06a002808144d081d1008921031410f2042c42d002099207809204c45d000d5010090004c658181410800034115110081400d0340d680c0e40001c442e080c6c10400c00788a42c802c030000000c0d4040040310310a00c0f481e50b80280b07042e403200d0031f01040002c08240d113403a40244150083c001e55101c034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 389453489 1250 389452239 389452249
    0x1207240804021519020d08010e06030a02100e1c0b070807080412030b060c0a0c090e0309060c120f120609130b041505090f25050d03050d1505041a0a050609 68
    0x41691003013032104a40031108507940002d40142419426115001e49a82c0c450201e4080b0404a130b50b690981c00c282c0c1c40bd00141004d6108088844403424194000c1c0088000b00d12040c0380701c0241c01000901d8a07000050080c80e0075030759001002494410301500d081c803005400034401404c0140309100103400300da20315200341d101c1280840000e1006d955040e2040c1901e0b81c4000014003903880044034540041c03100c1044c4a074180764031800c805141001408400c01810b82c120700104803460003600000009a10140c0041400311440755880ba110540610b520700c800000034400e50203000321700c090183c03640301c0840c1000300d241c2c0a00f55034410350312460300d0754800b5040890900081c0c20202400004400890800700c2e0a200707404030307554050003d10100c803a0130076002d0158040300c42e200502a5040101103481440e0107814150301d0040690110700c00c80b0040c1912802c0c20190b0003090107286000e001e003196880c045014091801c50460005501082c140324140c8182c2c0c0009a0314415103034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 389454739 1250 389453489 389453497
    0x513170a030c0c1508070225051002010e060403030207051009030801050d210302211006080912070b071b02030c06030703090515160804080307030b010e12072408040215 74
    0x71607080e4000c1c401c4c0c0300c2003d0321110040e1242405405a07103c414800c00f11505070103001303400341504c843c88500e81400d0050444480d0b01200455407542d11000c400070f001c0018600452103664016070711701031401c0850414411070b09281c46907042c0406503011a074450111410340e2412100d52000d10124640983c12900c4c0b01c21801c11b114080c0e070303415852500b5601408080d000104d604444940400140c040c1c0102180d0100254401c09014440e07280b1525059910540d05000c540d07101040f5480000c0030741020030b04a03800481d1104100480b030341304540ca0b14a5148004034200d50100b07900003903d41c031608080d030b07020340d40100003d903c0318400d4001c40c9500c0c0e044004d83c0d1014112300c4d000740c3c00000c02c868100c10b6035442016112014400d81744c0d0b62180360810843c905584981c04210050505072010314100100c1681d2180e050f507490301240b24021601004201c0c8919019a1030000c0c2d40307560f00c13201c7e5486241101c4a01036080312946034401c2c1d0440d030030b402032228500d1106090007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 389455989 1250 389454739 389454749
    0x1104081f0b09070305040b060a0509040b07032d1407020c0f0a180e1e030301090b0307150203030612190615150801231503060109150513170a030c0c 65
    0x100e92802d0291054260b40624040c5005150300056548d174030040c0007100e501c03803241640001d4900d0000340411a946c14030743d00b240c1b40303180114070100e4102c0700e0100d40000703d1350420440840340c070146001070248a440004803041d8cd04500c00d103000718001e500da080c00d602440c05041007580d8800c1075a54880c01c000a004012100c6050307500c050f1000004180b140590840d51049006030180715003864510405542880020351860b804c080600000d46000000e0035090310031540c010071481503001003036282c040c1950040d9104c1c54080c0400c40b1401d01400c4594454001030030000c0c03054114280c083d0600d41114000c540441d0400f07203a00e0582291388924150800362040c1d41c00d4a5200c41c899048941034424002d0174000e031868050110448e01c0010f50101507102102d0b007407407410000d5070b800001418035400b40307035440400400745003102d100c0d0700000e80006a0b1000d0514200c4401c0c01610056892880c12042c1050490381c030000e988014061085005607078080150310320b026400340c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 389457239 1250 389455989 389455999
    0x1603110105010b1b0a020a1a09090412030c08061f0e0a090c081806071214010807080d03020f04170a061a0f040513030806130e060105041104081f0b 65
    0x16940301669401031300b14102420601c51241c40ca807880080010710074440a4004042c07100b058a414101416002c590142500b50541032003050000e07a64022620302c5140224002130511207501301c01002c43d0741107040355007404200024030405e500c0307198810320004015403820451200b01c082c25a00f0041d0180340a9100d0250b40c004140d103132164011440c002001e448403403403500c54400607402800040d40d002c0c200d40c481e0300000c207034910030040015111040400080d54401d50165840e81d448241c0200803594046002000480400c100d000b0410f406844c0444c10700d42e100c00705904070320840c030030750362070802e4030728000c4226406100c4030401d542c3c440f40c200302c000102d13078500214884c0c201d1164400c00b10006464078a0405010700c900c580100240440601000d07a01501c0303441000d054560450344444100002100c2c9110f10506810744a0003440d884d0301d03003010802990380c3e5203070100524070203020400c00720f0301c0010030b40c103d0b0030b941c400c48400005040102d8028814042c83c42c0d401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 389458489 1250 389457239 389457241
    0x30c080a110f0102191d0f041103090c01110312060d021917060a0614040f06080a03120b030705010912030c230d0207080c040209130221060a030201051603110105 71
    0xb05505500900c0c00c4020b001840e00c400054410a950790f400d02080c040c0050078007800d21095140c002d02482c0d00300c20080c000034200d400d07004000e16035002220308104a51050041d801c140d80c0001c41c020501d1600340042d442c01c80c0494044ca20403501400440c010505644180b0031540c40020341c1e000c4d00309949034035865a9441010b8486c10044502200c80c2c0d0140034003240080c4001d024903000d5a8003502a51056034501090000600c0701458541455590f030902080c409030a11500801d140a95100180e0001141e80c1404554141c06103900c02c2d440b00f50204400c0c1d801452407000c0310044489684000950f04050318180d04510000f8112820501445091142d4802c540791400701c030000c42e410f0b54071150b01a82d41d00b07254040c841d0280c0c001c201400491415400422041c080a0040314040c0240700044080c3c0c0c01c0b4441188450000804000d40710b03c100091542c0101f0840700480201d14540001c4c02c980f03d1445048120400d182d000018503004071011444405072500070002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 389459739 1250 389458489 389458513
    0x60708040606050f010819090204110405090c04050913050a0c0e0106120524060c0d0201060614070201080c070204090f08030115020f073602090a0e04030c080a11 71
    0x15a00045404031012803910742c0220300c50620b04590141500185c54509440d21150f40c1c80c00c40c40011200c4400740ca40380c01483c00140c650b40105e10341d0108014040c4c0d100c45c01c2004201070044000d0818400d0b00092100300215903c00703c0c0c032900311b00300e0300589a22040300e06056003407809220380502201c00400b000504104c9440601c0c2c121142980c400080c401440d0000d01900c0d42518040708460480592b03203584080c4502040b0286001420940f80520707040e0764504080c0c1d0354002c40c0160355509420041d1a400c22621004590040b080ca40b4054072580040c1c801c110151072011440c0004c15964115221079010400786508034010010071150380c0380c801304a9000b401042202404144002c011600004d001107082240e500038103021410420b00c00740000d9800380e003480b1003800c0c070312150700ca454214141895040c240c0015075111207110520014207016800f407030a12034404100701c0420360020740c2e000351035807107030400ba07132a039041074111208000d80e07042440901960301c42c144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 389460989 1250 389459739 389459747
    0xc090709030b1f0b120114120f1506030a080d0b010306030209090708161211040908030a020d1b17061207080618012304080d02030403030e0705150d0f020c0607 70
    0xd0000107030200451101e440da401d400c0580030307103000000d03802d22440050020450402030407445520150411120881c0321140500c9e01c211581d08401c41c1d008101c415101d0b50041e040554000c50540040030640a41d688108043c41401d5800440035603820030818140c1c4242c200030000d68000303040206a050440c08140c44401600c50044079200c0c3c00c2014903801e1200d4000340440d0141540151946ca098544000d103000da5106107030f001e65140c151400103500303400a540a00c2c4004001621450024002c4044800203903400003850710540031268020b0340200b540300700300031b0020520601c1d11a0700100380f58444840000240b4010703601c0204940d080010200c0c0700340070480c40541d401500045950032940da150681c180361090300c00200c00b00900c07100032a0041c1c86450050328001c01c450540b000c0340c0007690304800203501d4891512000004207e824040d210464007070900d4038130314410203114410305001ca41c2c1d954560310584048179080e4140e480508100c400d0310078a2800c068024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 389462239 1250 389460989 389461021
    0x806070206010e010b070201350103110d080a210c050a03060906030c0b13050319050f01140109110c0105010f18020705030901113f07050c090709030b 66
    0x50061007420000501503162003c424120b56110390702c28900030760398004452008100720b543c0301942d80c900d0602072150444245290540c441910540d05504600d0f0250a82c1d003d0745105100d940d8603107079440841c9581089131503507042400c00e0064040c0d0520150f44114034000c00d1903071a450000c448401507001002072004880aa60800803540c841d0010422910700780800703050303d04500014000b002d215402801d000b00d0040341c1050440c2d540d00024588900c8805107205110002103500820404000340e10801110030024054036401107001c2c485500140f10724046991110019005082000101c07280c82008030001d004640c0c540e11518034514140c4104c040101100c110361880d0b002c14401c1c0c074080355100020390300d0501450011611180810b1110145000310030b0781001900040400b1000f2900e4000101c00704440f074001480902403452800185407010020400011804207403a81180421a4041c0ca42d4a4064040f102200c40760002064a01001e080c005403211502d203035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 389463489 1250 389462239 389462251
    0xf0509040c020c031f24090b150a120b010c02180c1e030106170106170c04080d030504050c120a06090302070f090209131404140c13050103110f031b15040806 69
    0x50084c40c04824460f0000b50f810907003c0c60100d446d0788203220b0000e2681200caa100c10050021390410010320141490740d001d20090008a525400b0003c2020464000d0341c04e140f4007420441c0c14841c0d1764005c10340da840800416650b041e80d000020743c04806500c140c6030510384000340001050801c00350021654028010000854900c4181e60203a89403036070f03558140c030100d98a00095104410004080060140100000342c10030300c4081240a0300308034118110090341d4000c00e0340e04003030910a0800701e13240f90060240389090f50655a610000070703240d03942c07540841e001403800d005040403420010940c01c84c61a0210302500014100d426030040c0c00010400c4804281d00c0218095002c100d40d08181c849080f40801000031700402e2103820841081c210070000d50b0031404100d00026101d005080e407002560350382d400107100b484015000c0c03109112080c0c4d05080e1508038100000d6450800c020b6601d129402640c00005075102c913050000301c51826007041c2d440300d4441a11a0721a5000c80381 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 389464739 1250 389463489 389463491
    0x1030e0f031204050c0405160309050a02060d02030f1008031c15081c080610030c0e060d0f050906010302091303020a0c09140609060a09090602070f0c03120f0509040c020c031f 77
    0x203178402034501031007594051420388059a082c2201041d09402916001c80c0c161650f000d0400080c0158807200001c3c03180e58440000183d507441e0040c0e42c02ca1015003d0000c100c00c1c0302e00403060114190000858800244459803070940c4e11003c8406000340c807078032a12400c040d00c02c42000030005800105541101c1b0301900128119040c40070480300f541b41111001d500084100796195400e00a90005c0d20215240c40c0c1240380004010119403c0d0f8480403c8009881e030f640d1410303007088118890b154100190101900055146400040c0020000b5200b0300603040e070b002e403010801d40200b14400400d0b41c4280300103e01a40c1c0d0000c2c0d0000c24090241c0791309070380200c00180641c5820000c00384503240081940001d541443c0f551402050030710401c403601982045588042aa10b184240e00b461180000226103411403070941350800410341c0d2001442245241d001d000ca4000c000c0e1075915500791800142c607031540c0c00880c54000c01e040c0301d81d014010466804e070128442c10a5158080b810b0724 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 389465989 1250 389464739 389464753
    0x6180302060c011b03021215040e0105090c0f010305010f140a0807060c0b0f06090a0f200a0f021501030b070c0210030c0e030a0302100c200a020a060e060901030e0f03120405 76
    0x3109170300b80d105040c06400801c1008000540040c0038580407180c45002902c00101600222055401c640c4240d0b03e14800e0790016403a03140602c1c210803018500c94080c6010700480d452f0030081441000d10340640a08000705020700c4501c0c1d216281844000d0101c00111901d0b50360303802d0068006030b422181030310a203c1c600d0004551403102c49a4600941000d030154615a03144a103070f90082c801400d4116106444461196030094030b0290455075461201010750350b07a00c00342010b8101c0c290301c1d03064420b6400034803645020600550035141101d411800001d0207644414048034100604172000b507000003480049d01d541540f40c1d00201051440791038103d0b00041403001c256444920010080060f84071040b5120000311641100c054444941096003c5400e0440b0292101114104680b500e80c0149444006c0d4030300740f0f0840005142c1d900b070002c0c4020b1300c100411a54407801d600d0605141e1158090090761070f081000712646004941500e03240d00d00e43c1085288640203030f80c00e8840d441292 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 389467239 1250 389465989 389466041
    0x201031107020619020f01090b1602010c020a03180b0a0503090f06160c0f080301030506040c120807020f010905150409240e130f0803010512010e0706180302060c01 72
    0x2204403812150003c050a05010038840701079450955070244404501440810385800c180900502c00300c40e1080d50044c0803803811340600c8241c1018420844216030401c0f0a2070005900443c10503a041d4151600d490b26070000c0004158941c900c0e0711450b40c8440004501c0c002907444409540152485030a5480380c0d0b05078280544e8a103804d0707955800000180d00c01011160058460f110300d240300c1c041445011549481d03030f000941090b401510b4030b80050040004101804056001038010000d40704000c0c0c1b40c3e4ac8484c01c1c24080d02d60001e010340c035042c07070155140e80505210300041c0001031100d0080c0c0c7c00504130480641007480f92500e00707402c040312102103a00d413801207160705c00410000c107141c92404513640b0354182c0141c800c071000b9000c11648008a40004c403c078040501a0f11040d660354585000c0c00f030300c01c002c1d80009500d64074064001c440e032580852030504407685450407811203000d40e446600521740d0303a48000c0d480a0300003030222070b4040c10b40150442e0300c15211461000d80b084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 389468489 1250 389467239 389467271
    0x20d02060702030901110a050d1701060807050a1101140a0c0e01030908030412110607020102070308060919050903040801020c0d020717030901081306020a030b130e030409050606071b03020103 84
    0x756811005a0424071080a03154819507134a038843d072501c812a00c04e10400c0d00c0b03441c1001c25410b11440010300000c0301100500d039000d6010f0042c8920318204239075152245000b001d80c003601e05040708010b0045043c10040509400c400500f00e0030609610031410700d50111001020707540700190101d0052080e002c0b0960180c4101c036243c5800201c0d4528507545c503038410f42e02c081104c4542044c0b10100c2d421a441e041e040007503170310914180e000180c2e900324a080c080c214040013445540304000d0b81d010003003015501e80c0b00842d0b00c00908408103160301d56a5400d0300310b000f00d4001e40d00940c17000c40e40d110102000a0240240e2582e42c0035908030a456403d000c250740c001500440055004000e00780c025445071302c40720342c0810003003104946154960b40d0300e07081e41d0250a401001031f4132480c0c41d41c02031508100c2654140c40c5a001005400c401c0020203031079008512410300200c0d960030001c0e03600d4039200b048818940e8000d0005112128986d40c518a0030700c2e03400103900103850400d40d42031200103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 389469739 1250 389468489 389468491
    0x5010e0a1b0e191104410909190503130905160f1b0807061b0c171905040806010902090604120c051e0108060904110907090315020703020d0206 63
    0x10200e0340d4007460b950410648603000d41410b1905030150f40d190010600780d1100050409006c02c03c2c0840040100b848003204007100d01c00b0b5024131412040e80e111070b4000054884103041406946048480d41c40c200c440d070514509514081130302c41060064030030401c000c0b0081500f1100300f16480085500c0b03500d050b0840c2d4003142c92400500c2540800c2d0f00240c061013403108400c0d2149040d118a041120303202404001d80082100c80d00b001144180030800d090107451180c0012107000804615200e40047c03060081030b2019140c40c01545040d010b00700ba004c1142c0480c00300491252003001030305801442d683c01132089141074040e600001c20103007514021500305150003001f00c0e042c1804c20082c410102d802e060201c03010700420800007000e4407003140d040e0490507036202c805d56028080d4005401d0303e4006110a10401c070078020031000070f06c0b410504080788400d880d0588107694564064a01e81d885070000303081c03070512481843c14030200742c0003000c04520079401d0f100004032810b426030355440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 389470989 1250 389469739 389469749
    0x108070807061808032a060613021809040c06170c0409020a0315060f090e040209010308250506070908011b05090102010b13090c050303120109090c0305010e0a1b 71
    0x100d45400c000003407082802e018010f0000310480b020b00c0ea5901031a03c1c2d684500c661191303848000c0035040c0750255000742c000e246c41215000d0b09187c40e02c0000184903c0c1030303441e60f003c020360104441500c1e070602100c0320600c06018207034100600381070401d500791076201c1c4203c01c00103140c00c90700b03690800e50030b401d03500a03840c03070003280e0500d810868054003079084948084100b654420748000181d10710914600240201d031660401800d120304014440d0041381c210075400790711242408016120206400e04494021807816213134900c035000c40c10b0b829508902c1010312041021140244070740482c14030701a103581e8881841c501d54640000b800d82c0c0300b01f10088640c0080c07811403840319019000414055a052000003140301644000445409461011a00c00c59444407040104850b410091000e0f04045009600f440b10389000103410000500890300300645840280c010085803e441c0c0b40510380c0000203200c903a082444540d55100b6915080d209803000001550360340c00b11a01040541c0c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 389472239 1250 389470989 389470993
    0x7200102120f0a031b080106020d0203090f1201091704090513021804020609040905071a0909130f0206160605070e01021e1203070c060b03070e0a05090f031902010501080708 76
    0x76a11054409190010f00440342490344401000071420540c902c5100c22000e962146095941003550082c542070401012310700b554010054240150b8900c0d5a40d4900388040301c030851514108049140074000503c0010b00302c0507148146074a142444001c1e1040d18100202041995a65002d40c0f001541140020750003412075009007150344043c9400caa88540081e1405160240c1c5402260850f60102810746d142c2e007040b402480700c0340344d20030803800300003229540f20704040d19440001c4020402070108260100414600d100300000f040c51040c101d5002002a500e800f2030b0101600d0b140c20107081110000e103090002203c40c1d0180b017140041d000181c0c0200218040c1448410100550414024882c841c0400308015400007900440c801c5080380c0e21600d80c0b6a692a004050b60000b0420030310980100d002848140c0640040f1640f1191080b80402e213034450b00c110508060844040e802c1034000041c0b458265580640e69644000d49540200311316a07072030f50303000e03240d22070350041815603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 389473489 1250 389472239 389472247
    0x3110d08011e08121216090e1f1203031d070918150b010f080c0d0209040e013602060307111e0c10030203151903080720010212 56
    0x80700101070300a40201039201114410340c0c8403441c003480c02c4c40090224000490025240c1d540105000e010750b08001d0821081184802c480e501038440b07005070240c1800c080c00d0a000480d08007451524080e46002504c1c0404000e4039002d48181a00c5030140a07804039040c0b03139100a02005042038498001483c3c4042c00025003088481ea0150125038024030304042780007809404150700c6010b05409604502000844240305000504141c402042c100d007031180341810020700301c04d0b02044482504d0803000059076221480700080061540156400c3d06603c1c0c1007644440198070b240030240900c010707160b5121661034850f91030120810203c02504040c0c144080340c1040e020300709210075040042c05480d490b5503c0083c00705050000d901c5078020354413046041d15241454507070240e0412041c0380075450762804107883d240e8224544030f001d014181c42c02443c8190500312040002560b1b02c1240281d4400040c140030b00b0b0b595001d001c1c103100c00300c2e6089004c220360001648040f0a4144100319041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 389474739 1250 389473489 389473499
    0x10e060105190e01230703020c03030a020d03090218190b06070c0b0306060715050103030315080c011103040f0b190512340c0501050a0c0c020d0c0f06090303110d0801 73
    0x15860380a003444c10b0050b0000c01903914030390503d40e64409181020203035107070140303420020300d4024159409402904108440c0400503400304541c0c805004505003c14003118520100d41e80d00e2441c101da0200c0740181080c4400f10b8082c00c10341440b1001c0c0101070110100381010000280b20300280200000064601040001c058102550b44481e0082813182040d0180d00d400c4144801c100c020000a50350703000600405030581300d10750040c070150f0304c50781c001401e114041d5620444891101d0500c440e00543e840c03280e60820488010340b11300b000b000b00840d1b444840340c000d0b800c080340401108903c0c80008011070311a505984803044090b417030005c1c5464402124451582c4080c42c803003034081c4044d040c00c515074480c10000180b0501d549024810149082440c2100d00c0507107940c3d102d0741894007043d4a07d034042c0100150903012111010758040910f02108800c9075036201022940d003442e8001102c0780c0040d03041e41124040d80319201070640e051041500d07403401c4044240803611070001804 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 389475989 1250 389474739 389474747
    0x60f1a0109060e0d05030406080a05100f030204020711040e012a050a120b060703090521030d0b01050c070e010e0f1306090809042f03220f0b0c03010e06010519 70
    0x348040c3c0180051a41a180d0340300d03030f42141e020340c2002021071000d1007844164400c034480c01d580089402110261141010404099007641d4400039102e5034020031389106101002c410b440c1002d900510811888021031150760113009003c80842c0310245100d510302032000c0d18459843c2c55000c6544031880c00840402c280c46103044803e8070a0a260b480095941c16100c030320040c40207a00a880c0d84451a240c04200001c0c04581c0803841d00c148020381200b00ca4910000c20342d1041c28252002044407042000103c85178000e0019040c41c0d80f064880c0000c00420316000a4180c940000c0000010341d01c0d903060b0310f10003c043e5850940000d400e40e65802044803540030001d01032044000f5813800c020720000a0030f40b0101c00d002c42801808203803c030700f403c00c44ca60245000f0f0b056071803142186484003265400c40c1105001c0e5482000420b5554108520005071908890b44580070241c0b42c00c0c099040c0040780c209009280002102c00c010401e10340c00b540584845c66589100100e0000050b00304171 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 389477239 1250 389475989 389476007
    0xc0207081b220c02010501090c051309051305070f03020f031c081e0a0e01060906050102120306060f0705031207031404021302090a08010e0c040204240c0609060f1a010906 75
    0x12014042d5459880114203405484103207070f82540045400d505111211044584c040106014441e003001005051494114404110f40a0110024487c4d071081c0c1c4180503020341d00c40007032160190050103c0c100071505520001d60707000391980e0b01000342c07001c145981c6000c0e81c01c1d41034046011046500c1040d00c201800765001c0000d581000c00d25207410908054420240e6400031a0740d02c620002900e00c009205090003000509424072215241c00c0005c0d4443d0b41c20384603542c508000000090030f50302c0d1502200d814030f08a05070f01d56150b0b907608090744c032500945d030740c1c0506168003804600054800e01540c0110206403401804075210303a400c1050115411448400140c0c00307111010080e036941e10032a00a04490f4004a60010f28640090401101180c1180f04a1042c002441902031140c9240c8841c001c2a04c103803000491010f064503c0c1107444801810a41803410080c00c120058001d00c46515200d8010700c404001c483c24220b004841200583c002640d41004201251044d4100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 389478489 1250 389477239 389477269
    0x9130b03010216060506010e090c09060904060e07050d060b0f031602010608060907030303050108010e06010515072414010311040b01090e040b0f0c1602011d0a090c0207081b 76
    0x610b0f0802500b007031400f0000040080c1d0710940d0b03800c00c201075941c0240e412103e26100310b80e8600d642c03034060040b42c0580110b4100500450012808030300305d40329948004c0c058003062441078014504800c6c014800e91010b191902410709044001501c12005d1003946e03c8054001289821030380e50a10944040344407070400404c543d2540030000e101c0c0b0040c040e0500540d0352002400c00203046040203419100181e1101c1203503854114940001d0801061941c10355900b1901c000c90310800012445190051850207411124100a88000003980b0b88004120783e115802c140034600c0840c00000794281c0910000c1c12130f4400098100c0b4501d802da0041e17061b040c05042015031280c4428250700c3da4030b0308030350441c0c800d290780e401c7c0440503010046050b40b01c0b2640000e24035103000c0c60039414081e00e01c0c3c00000e0602040041b010802c0502c445d811007961006400040d01940c2e544100000d0800328075014054040c0c7d05010034611000320ba4000d003070702d515080080000b11181444160b0a8240003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 389479739 1250 389478489 389478491
    0x70c050f0d060903120e0c10210c030519051009020913060e1e070210050a0b0607051c020c011403070903021e01080709030f1106041805010e010b09130b0301 69
    0x1070005001d0f104950300320f030103075440c01c2005007030b01c05400884060611700755080d804100b1940c0d50355608400d4149619240c580b0351070281050003080070183d4030001a011507802c00380c46012481e4945d0240307219050440e070756001100b4000701501100d4043c3d88810141e481000d00b80f00301c0b03105400420580300d01809009001c460009210110b070b0302d68004660080c11042030200c4035070042076110300a904202901100d060151003e035880c900100008806034907200011a0f00b03542e41d2040004440190035641d513541a03103030081c2c48401105a0168030706101c1284138000340300240d150343c034102c1a1074070740341a1195880c01c00c0503000100a05c00f003101007000440107072142240700e1140144c2c80b04904214041ea800035241c1c00d8000d04010400c500ea9004001241818100b001e140d03070059503402900c111140894418440c42c2c0010200756001c0000c1345280f413040d400702e8100d910421710740040766220090318207140324542c0080c0d400188040b801d060321143d07a201c0d01d04c240c80240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 389480989 1250 389479739 389479759
    0x1052b050c190e0c03010b0703110309100e0a0e150f030c0a0e0108010b15030c030405010b0a0f090506060705070501270e06090708100603090201090b0304060e12070c050f 75
    0x1c51940400c1c80c841d0524038100d104102c0762800103807664011001303d18030b43c00d540c18900030b0703c0c82c2d02514001504110705411030119115043c02140c0c8140d0000d41a6811342e00442005441e440012319001e0044420b640c001806403501c0803041e02800700c020101408003586820402d0201d1503205480c0d00d4000c16244210329074400807050001d1084103180c2c40d2070340c903002c101030848400c140040d00642d140c49402c440132420104881d4050b0030790412540f2922603007000e6004090f00103500d5000f20140d503020450740200c0202904603440d468050281c1d07502c16040c8666070103a0380d03006103564003031403081c411580600003040319580c4410410a50740c0c80161040540500ea40c069044241c0d100280552400c008800d00c0d88403010b030800e5070543c2812480e405906c01c0e54071a050405680340a00421603120300c040900608942650b161282000c0c10950000c0448181d42502885200004102860400151602c01d6009440c1da107241d0710700014000d14a65901140c1d0b0f200580c1a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 389482239 1250 389480989 389481013
    0x16020d050a140a0c050f0309030c090a022106030d031b03020a11060721022a0307080c0c0913050a1e021012060609051c110d03020d0801052b05 63
    0xa0160600b0003030f0b6543c3c01d850402505081d030801034a0041004607402c1081084842d4600003440c2c260240300343c8007401d02369035001a242c028081c0710400685101624501c14581880111076805423000314140c800030b80704c003007082c1c0c21a41005842100a1140000e94881070300a034060a0010340c82e00703040204c1141101000d00b4a80201d402c2d60104003541d01d01031010000714014458202c020004500e0500082c45003c0e0384001e101c04101c00c015400021540c1c00020320075106046da20002d800c0d20f0301c204060041d107407050444401c1c01480d243d00020161164a00c0744881107800402401040c0c01e0368940b916030703400f9034149100124030450300b500182c80e41828015902e02d0342d520320040c600349102000c10f8801c0d6a000c07508014000400f03020581e50a00403914010040c0c1610728141070f24581000c0c101203540070540c0c800c0c1d035038600354141500030a014903003139240d0342e400c1443c5c0c2e01c54013004128080e0b44085c4141c5083c0c080340c480c0454481454884540c0100101ca491141d04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 389483489 1250 389482239 389482277
    0x10020f0a0b04050114150d03030609060b1b0307020d0f17040b0c06070e0f06030402151903140c0a0309030e0405100f090903051e130902040e16020d050a 67
    0x244100310794105a440800003070000a1240e004801d400703407003a48590516100780c5510b076117280181ca1140840481000426009074070030300050211860a104a036030303c03100016913421084000b41800d5200c80201c1c500e00c400b004640203e9401000e00e1901455515a038030a00a400030890352400d22482428115401c400900001e14502070b040f9a80c4411007541402d01d4405440001070002c56550300000c0d6841d40701626601c0700035542e072502d0396110f00014080055849480100c00c20000d649071550002f03070041094501240c8092103403509a2401603500d80c021960980145014071006018030300c40d401404485c1c0c0a45040015000c040000130b04541081e1280041c03c101300b5010070002c110351010340300504019501704910483e5440280030b41c407803034032a504022125940c00701d0707515410042c3c60307a002c0344d00031030840181c41d40607100083d4000d000f1504540c3c0c150700007410204800240c280e0140d101e038058820204e0192041d40e150300320000300014004010225500741c020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 389484739 1250 389483489 389483503
    0xb0a2303070b091f0e041e0501080a050f0a0b06121c02060603010c08043c030309110409020a061202090603040b010f0b041d0606040909121101140610020f 68
    0x81d10045903521880010070204030040e03584801c003414103d034600310a9170001100e15180205072804078811a1000941c24100406600405c44a00e803000201c2d400d0000104085520310800844a22150b84130f80107a6800781600010105200c90000881c14100070f46d41c0142d01c4110001c079408c01440407c04003140091901c00c0b40181c0c4507504000b0146000d0203003180c00c001900b032509003810107840e00d500c241207900011026062040046447d1000c10368001b201804000012140d0f0445107001005448003460540f1f00800062526842d0300d0310740f084a641c82d50040034541300700c0ca00705007561111441161502d216a00340300c55070450725180b00030b500c502c2c411061500b6949c142040c0150030300b003a4111204405060009000c17a40d200f612803d0740301c48600d00c500d0680d48140000f15a44500d0b0000e0b00c0c284e0520308400104083e120141500d88026195415816926803140d8200c1b400310b07007259002504035001c50325500301082032800801062042d105401182d4466070700e8443c1b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 389485989 1250 389484739 389484749
    0x30309060207061512150b010c1401020c010510060e04050721020309100b06030406090c240801060e060726030405101103040c030201050a1e050414040b0a230307 71
    0x248440480804e005102840806491303071003840d840980e460b031190000f040710034070328001e400d550781749081c1e0581c010721034592a0780e40000d0520880950707048840c040e400c0070120491940c241004a03001210746501d6405440e1666101501112450300f004082c0502070b04103801d000110201c450340c64040c8200300078500b504100036940c0c1c20104482031606100c1000e00c41050b06d8205168200c0c2c1c5c554049907001900000c0100d003010301030408e1012520660b010040c0c0003800310b045074600001c00302c11490480c880c1c1b501d1110341c0e85c1d030304180c5020000003280e40c0d000101f04940000034041e103039200c0c1414696400703603002c43c444d0641843d19900556054400754001214040c2d40c3d00c05000e8800e11101a00045003541466a6010540101130100078103020f40403c40000180c420006003644401c150892885c00c1d10028002d030241d03009014603150080201c40d000141c3c1814022101d030030070041c3c8080207161420440602d080c002042c40100340500a00518a5070b5040140034003401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 389487239 1250 389485989 389485991
    0x1050d060b0f0711270405030913050a05060a050306010b1c020721050c030301060c02180a0b0114130b0708040b0a020102180f090613090b04080405030f07080307020d03030906020706 80
    0x1075128181118001d92040380305104164900030b6200481d0418210701200900d410417540ba52034078601079003540030f01410280c00400d42c801310544d0b030820b40c10140c0542420302d4100500d80306c000611054100e28001c5030b4260b030140004001d42140710700180000742c040d07000c0881580d01707002c400080c1d80c0000c20603251901001410a078807030304030000030b1894540c0e08060f480c2034071102c0c101e82c40340414400c004c180030032007600c2c030190f45600e60502038103440ca0102400b03034988000280001d18041010354002a00b4906980701f0781c005404032002c0481001c028141245000b110b9921a88603500450f406002030100168501464001d80700760300701c54001686980a0001e07030a41c8121402d60300c0e10a40c69020b00140c1c1f0b450f59802c041d00043e050355100e0007081c550440c0c1019042c407483c0141064440010842031000074000340090740d00c21416a0240d02455401d9944d81440340540b40d000e42040044a0040c500300c1c01721141d0358881d080105103000a62608000c84c0c00020041c0e07445 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 389488489 1250 389487239 389487247
    0x20c011d1306090b011d19050409050f06010839060a0207080c0604060804030309020a08070603050f07090602060705161203020702150315060310050409150b0a0b030601050d060b0f 79
    0x410f590094142d0300c2d0081c0b80200c180c1d00c0d01c140f913038100c9140c941a40d01a01c1041840400c08180010840c081c00f4007520a000c000c4180c074201d80c0d10805488140c02c54080d680001c51151008910010550100c000e8a00103590303480c44807002e6058040d603803410925001903c240358482401070540b0744403540150000618140c0800d0130401c140d80c000b44614001c000c1404040e0b0000300140e0415054070f0b0019520086102041403499039402c1401584181079000410941c56040248a584c0000b2440e601391140501628501d0725030045001503003000c400900c03898481e4011f896600c0c2d404020412040841d2aa0018044030031004400681c00183c1b000950400c0194400d154401c0e00743c103403940c80c006182c6c3c40180d2240c8407841c81581d00102240442000700c40703c401401008108200d09196860010813400c4006c0a14000c107040144400c01c1d8070b0402020302c12a4807100f02c0c285180d9030a001103803164003002616460300d60300e22000c2101c004100150116080b0301010683d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 389489739 1250 389488489 389488499
    0x18182307080105010e06250c080115050a0308030c1806030703090b07020601030b13030e04050705030601080c07110904050f070305030c0f0c060703030c020715120b10020c011d1306 79
    0x31000c1600098180552404d05c51101e0300c5400445110401109014411170940c0d00b600800c00c503d2400a0320601840380045a1240103500100500000c108405400d50340c410038001114058400600882c0302031000400c1070304480010130b43c0c01c8140d4425201ca00c0018005400e0b03400c142c070038400090342c5058083c10004801d41c1d190b00031040f80020060756155580e8040c980f400105846c3d802c000030085c000c2054001c01840256800050081c00700c1e00c0d2418004290350011140c0c513002541d400c0100395441c0341c010859101d42d80052030021036444000c103000349010301410480d140e1054105180c2e82e41c00c144808000b45101b00b000c0c40c0d1350b039142e5a405240004203850041c1e40d030803018200c0000e50f80e00d402c680c0d8040d450b041c0815481c1c9250801d03030601c00c0960250b0310b400e0404c616006402d500c0748079408502c070a0038041042861038400d02c074412441c00c503460056800101d070390350598040c3c0f103041c80d10071804e40381c036201072554008244c00c072070001c9a24016035290401802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 389490989 1250 389489739 389489747
    0x2007081206030c030601032312030709050117040b100b0a020f010b0a0807140a0f0602010606020d0509030607200a0b0a0509060906010b0703090902220618182307 71
    0x18010744101e0040504054042c0003035150f50061100801d603030042c4e50310a8510745400721440c2c141d0b031194169030441e0a103001c0114203a1003140c200340001c1c0da20f40040341940c050700d41c404054108004a854903581c0781e44508202c8006042d0210303000e142e0b140024030701d5028004141e61155640030380718550404407042e007942e001d00071040c4186a900800c0c861000c0005000c41113540070021001e4624568012520384602c6403c094000c00c81d0034008241309805420101c05c40d01582d00700c0d182021001003c071030794012000f02d15496004080802c0c2c80c0c40c8a510504148050b240340f0000c00300282904501d8541c5100044031144201e00400052040601c101b079441042c0e900900301510340f9500c45519400d05005040e00404040b5401d03091520840000b80501070051045650b0405c280c7c40a86a6401001c1e1400c0b0111005011601034441c40d9580811003d20401c0c000041c1040a241100013003503c0c0c800e003056035204040081141c02c1c0d50000350b400f84402c407100303604101e02c00034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 389492239 1250 389490989 389490991
    0x1f08010f1d03090405130503161b0605160c090501120b010e01030512030c091809010e070e010b090112020f09031204120303050402190605030114090103020a050420070812 75
    0x100c1c2079102030314034014000030040359041c0750203d500260030350341e00d503101840c080c8556010b0080c1c44081203510242c1040f0a1402656026101c8015a001c00c040c17505007145c0540a40b00c001030081c040b10041e94440352406040c10301c5803121500072a2558001d4040b00c000b6446903500c0c0c1504130b64002401014031120b400360000c0c0760b101c4581c2d0705640340c00e1394840e040c01001501c1a800800101002509001d8400b40400201065481030200700c410a1040040c0c58040c410752074594424100300001070a40d0803241c80201000c4660b280213505000354000502c40c3c0d040c490341d016001c01c1c0480503c000c0080d444c00c0c150244e12000240c05261400c0b100009400381c5038001c00050054812540150260031707854640414203030384074070104a4040b50202d5910420050100c00b0500b01d80041c0518180c549845120780805036590410418120030b100c06501303c1d210303482c01e0100381082d0300024158150301d44990101050a010020150710078a402c0d1403e5101088800c08019042c0001e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 389493489 1250 389492239 389492261
    0xd170301050f011e0831020f09091506030a080c07151404030f060225061518090c150f030605010e0916020106090f0905010606050408151f08010f 64
    0x282000000c68280e4091940480e13401003c0c0700c100c40003e01ca4103510718601030303410001602001c05881854241e6528000640708034400c000c11140c048081c20400b0005100b640319600400711003100c0c000011a0a4014103680d425000b220321490224003c44020a01c03188868000c00400e0b203410903518036144c8003500e1904100e008040072002c0000c100968050b2a000024035030081c5071303460000d009220301c03604900310107050000c103140b06460600810b062401400c050088466001081c00440c1d15401500d4a45001e21200030442c40720f90320200d502441814042d00740c0b61650000e540c441c14070300550000840440f49002d185601d030240c034000b0603080c24200c4010740e0038800985d001e1320080101c4400f4070300c580903940d0a8800d420010050525640c03c2040c0c0001e10b2074000a0302c20b220080c0e07034944c2003000004549102d102240c6c100d8000402510700c00c81040e0152000b050041c001d1040d0566444102034101041c11000c002480e0700c0000140c0303201007650207025280c0b41000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 389494739 1250 389493489 389493497
    0x14031204030c09110706060311121c050c01240303020d0f08010312091526090a02010518031005090f0703051905010f090620031509060d170301050f01 66
    0x800009110b0b1112400759501e001c0007044000c0925001c4400340070324080988190308003076000041c0078034141440082901512a8190f14101350100c1384d076100b080d0a1071202c8560191890405413007400134240000e51000003284801000e248442d00206400c0d6a5a2030b0103a42e8042007050b40401200009070028249007041c000c4001c0d002d04007203814800506100c4e04034a900ca0402d110f808030402820612814002003007628200401d600c110901301c1042840303130000040f511110b40200c5210315100402088011501d5004644680181c4540d6441400c1c110303403411556000e021508650040000006142c6000480503181850304a00d85626421403c000c0c80442c502007228004d80302100002c0c200f00c2902e01e0594010884584040741040c17901e405001080296080020842d451301c00f1003103007801108040c0500c4c44107540c0000d002c542e144d0308001c182080280140d0003200242207402082d041e031a0302c0c100307454104407040e18480c0000140101d141c00202c1101400c42072030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 389495989 1250 389494739 389494747
    0x516120513030c0302011506030f06080604020603010303050912070603050a06050913080a0207090e071d150d060f02070f03110d120203090106050d0b0901060e0f0403030c18140312 79
    0x500c49a036414030380040d04101c60341d9800f205242c000d40229405056034074079201c1c006d5490700b00600400705503c0440c1c1d00c03410300500080e450340002e9454011500103003002d103543d18565040e16170b03a20240e20310307402c10300110b40f6104440d0144014001070000d40c8022a540c504802d02c60b080340c0c4e071500310611801e0454140708141c814222104070159020b83c10380c2d46c5108000d0164030740301d031940c0030001c1c00d428154445001403010801d002180c002c0e944000311100d9581891804c64421940c1e005c0c4c00c0703503522051041307181c07211000101d2805210001000900b40240340f050342d020400541c0d19100d030450103010590b0104513a152580d6240241104000c3d100b00140460402e50400c2d0200350080086640c100382036200c18018a0002d00c07038640c0341018540000310f6001118001c0043d40f1702880061440c1207002c070301d8420710310782d88450b00d01ea442d55010383c001d10903600c2e0101005206585142d004101c0f10281018010224000034480e88003400c0510b440c440d01c402c0d50030440148 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 389497239 1250 389495989 389496001
    0x3030316030b0a060e0918010c0c0204060611030f210c0304020f01030e0d0302130b040f0611010b1005070606030b011806050d050304120f020306040305120702011a01140702030105161205 82
    0x1030f5121100f9038115481300b581d4540410219061440308201f0300385519050b600700c416508140c406812a200380e805012040c0d42d00d9041d00c1031035254420391060f41040120b00414522200201000b6554458000d40c070900d04000b00034400041343d251206030340010502066250050500025690928051111502c0c081c9150b0312025044101400d040c0c000c0b5035002500d040071440d40142000803540fa4480d5600d03450201c03031041c3c500c5030402180c00b000314a81f60f44810b005408034020098205506001000d0701110700340c2c41550240c4080b581c450010002075100400d4034006e040c0039a02810b0401c884138158216945544450f04c0b480c03c10020400042010043e5800c0384c0d41c0c85802c004642840c20030802d0080d603008001e5160280e001000201604040541000f2254060707401e506d5076002c50136422a0340e1000c120782004d008110001e1190702ca24128030750000c0c0b992520b41410b01e240c0c0407034250b80303003500d03544058001d0709149452168008207101101e03184130f07001c0c0000e082c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 389498489 1250 389497239 389497247
    0xe0109050c1516030201020a08090c03072312100609021804020309030412050304060f180902030702030403051f0b06070b04020904140f0114160e1306030203030316030b0a06 76
    0x3007400320b4000c40c2180001c022010b8100700395507603075030300888003c0c210f012494001d000f9804107544a0228020b1000f080c0002000190b894880b10080c00030607641c1d0502c04410781604080b8050364081c03411071455503443e00d54103c000c0542c00844024801c4d032244910850540312207402034141544107210703140c01c15920444000c4241019030303005a60f0b0306d50284050542c42150405c0c03a40080c5850254204103000008000f100ca15542d000404244440304840442c0017802200844191200a1104008030340c020341e00000b240c0100e070714040d9240c1e40c0c58146040507214840d691060102501c0c6507888d4000d42c04820000c490003441e00e07001356160b560f0740c0e0000e000a802480c1d260005010060105141002510024111100070568010380d40c00f80041c41c05c4075098102110100b00100d50300322496640c0300807911900d001400c6c0300107120600d142c3c2040c48010b9500c0e81800805070f03c0034001035000e03840081d10726813080f044100180c1600c01c1218014003903a02c20404110766988 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 389499739 1250 389498489 389498503
    0x1c02120306040b0105130b071703090d0e01110a050a05100902060708032a031504020a02101a04090c08010b030d0c0206030601030b03030a09030204050f0f04260a050c010e010905 78
    0x301c800003020440c41c401281d5038040c0071034444c800040c6d030f4404100c40d20601e018250140c402e04a484a0702c41d070a140906600043c3c564031219441440250b0710f5600861007844880010f1501080718041980a00d24050040109071559008001c0c1c0405000080c0700800001c0d05942007031040548640c086212031048000192200c0d2020000c91880c2500e103054119160310098500f802c0d040c99004980a40c0c401d4480f10464109121401c0b40790a103402a103075802c4103a0041c00c0d1401c188802e4801070105402e012115804958050507255110320803120389074041c0648000701800c06d01100e0864922201c214400c1e03012000001c51254440075543d511030307042d100c1c90345a803103690069000d4406900e00d65070501001c1041e007061680030703007407400712402140c00f8001d0307480c1c00705401215441038908a14040103003002801150681e070360545641d081002900b1600c0788000310351840e130004000d80c00081c00000b0b1040c0b08143c00d0184004903204d20008014215241d61b8403661034003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 389500989 1250 389499739 389499751
    0x70b030c0703020c0d080a020c2d060702030f070302100801182a08100e010e0f040f060203010905010e010603021314060d02030a06090e060f041106090d051c021203 72
    0x300005001d01094402e01440c41c080300081c100d240400480d00e030011041c0c004640010062107440e840d0021440c10a0300101ea034040340c59442d0310b82c02d14621070503240c10540318568000804104075001a2410400c0e00d00450400020302501425031040080303c41c104000e10040242c1c0300e00510000e01200b004400040c072140c0002406488003400d10303080c001c10203c190808030843c85120b4926001441a48200b00007040c1c05a10340c0ca0300070203400b8038403c1c010012100701c030342c0000762003d25031211180c1150098681ca2500016966550182c0e4405d07040701c4a0301c1d80ba5401080b900181801c41c134050f1101d414150b003803000c22158082c0030392251182000204910340c260301c8030749034a41103e81c1409551410355981c5841d03058540501842c0c82444842494008030122035040881c3c02c41c0100c103e0130014450340c030b40761201c107502c0301d4094256a006004110401241d07542e03580c0e80d01258421070103400000c005080954501890001c043c0654109109100d10214084101d0303500030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 389502239 1250 389500989 389501011
    0x30a0f0e010306080f0a060c0c0c0b070807020919050a0903020312150a14270c0a03022a0d0206130213150602031c060b040e060409060501140a08070b03 67
    0xc12200012800380503d503100b0400360054021820340982c000c90501e84e402d00070708041c000400c140c0b10071101c0d02402040a402e01c01e456000340300b003a13800802094120b01825026048c8203031030b00000c80e461010342d07000f01e5510b0180d1100007240d0b01c6002e41c503484040740300c1c20414000fa544019441c1e00c10f4089403045070241d07100140200f004a1055580d01002503d4403001c3c03526890083d407007031502d203001441400501d026240d00222908a082c022002c0111000c05440b45100c1c4902034200020540925809010110790604c0c401c0c80840b121026a030307008441d4041c0c424450410800300340207030440d080042000700b80e00703c1044a44003030798140c0e100d80c00c600c1140c124400130491201541000c02d80e00300009400341e80000038101c0074807000c40c180308030703600303a40614221031440c403c0613290305090200b0007842c401a10020b0744100050004141c802c040e035544d50403680241c1055807603150007850031410f82001c02c039050162800c3d00c000c1000303d041040450180c0402400c01c0c20740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 389503489 1250 389502239 389502257
    0xc020c13050a0609020c01060812030103081207050c03070c1e0509150303090d111c0519050a0c03030807030605030c03070e0414010903080f0c120103120e06030f090105010503030a0f 80
    0x40a801d0f40440c008000c491411510340c82042e000e58064005403044048501c00c801d51302c800801b014044134103c0b64405886031400700141051200044020001c1e0180001880104040401400140f00003407281d070009862504200410742600e2102140161402082030b0501c1251a007900d600e8214848850800031000003c0000e49580b062185180e080a640d20541040280084142c40183d408032949201d200010717100400392040e0980161a590144400400100361b00308031904880c002c0c419a0707200c502588540344d103a9815441100051a44010000910b07030503c1202e01510046025100444c210000a940c5034400c0c05020f06486541002c10204494101c40030004045c890003441031284a00707000d0301030350701103802041154a5100085001034400c0c1182c0c61280c40c840902d07000d0b401c5d43c6900306482d4540703e951060041e00040603015503500350242d4810102075401e81c40c54541005082d080d140d060340200d010303a006000701d942d040c0c2c000c0c929a001c408a480c2c46140303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 389504739 1250 389503489 389503501
    0x12090a03060e0f070e090a0f320d03020c0c1c050a0308061309050d180b12090c0105030705031305070b040306140708060f040908120705070302010c020c1305 69
    0x26912840d48010101850049111900200810700b01c00c0071501c981618015513440c00b0140e4100001c43c5d0102554010102e664009940c58036420480c0d801b41020202c54040c142a00080380900000c1480c075140120b083c0700c60603410400c4e03450b200002e1405508190050340019030702c42d804001030b4418410f010b1109041d584130803c40110542010454403941c02d1810042e14803041981d040303002c1c0031507908061007041e20340a408011a1f00030014100500c4881c4d0482e06041c02007407030300055a40c04000522805007001514a07441e5003507845c08181003003000303246048400101141844420710422014503000410780740d00410320905122803403050702d8028201203041c0c024104100001c14040140195540442c115441104454002c0e854003a030a03220301707804031190f6901c00218101541181440c1c0c0094400743e108607116400c00300040d01028040c001212200700040c0041900004d26909019031000c2040320700103048048032311070100f65080303020000348043c3c0d921070f004911 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 389505989 1250 389504739 389504749
    0x50903090a06030e191a010b0f09010806040b03010c02150a140f040305041d061915110a020423010605090a051005070f0819030b0303030406240905040618051209 71
    0x5d01074240d10912082081c0c5070460380c408020380400002081c940012138003036144400c0754003040c007001400342064462001121341c82d2000f848260055282da01c10101500d0034065166000b0a40d009440c403402080510070582800034403041c5201e081551a500034200d0a804640000404010130b5841d07555050650310b0344a00d070b01c480801e51110210300d4440f81649a0507004002c00c0b18014402d4650265103120326419005015445060716210a2200d00880c4003a080c40071001c2034078520703401070700000c0c12204820500140402104d000442510343c040c02c03207002d0211410024202010f02e0085940021240071310f0340204000200c000615011398144d881c800e40c495040c0c4071880c1b00e480d1000041d00729040700002484020140b1840c140240512641d2005c00f030f0080d03080d030396162940030150a5950400307000b0352601c001da07005240c0c0b40200901506482c440811076007001c0c588042102c0103181802030000c2c240d41500002503022589a07500c6004000040c0c8039800140060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 389507239 1250 389505989 389506003
    0x90318180105040b01020f03210a0c0801140109081506090c120736030203120c03071b080604050105100e040221030409020418181502070c090c030e01050903090a06030e 74
    0x1461fa202c0485c4509801c00d04100b40706046910700c0ba01c002903240e088804042e19620604540440c07690401480b015289074444000c008052405150051b525100305040c8107058040c24207116145c0100040ca080010020f0382140046d0251498042c250b0b9040d00e90000c090014000c00c6424442c400f0380100448a00d400310002451981d04242c1091204500020a20049009004010100500700b80200940d4002400180034600e010035a03514840341e240807200807800c01e00400c00c082509102084068131581c070480c0000750034101080ca10107180701a40c084000c0d2000070003000010303104e6000d400d01d00b07440c1e0381170385883d00e20350400e5a08600803030b040034504520116001800750611318040090600a540422192121101501d6101d000500107840b202012069a40c1214203600421000703028440908042da2650f01a0064880f0040e214000a885481c0000840404e20646400002c030000079858024140003180a680e8a841008281503441d1540e0007030010600040e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 389508489 1250 389507239 389507263
    0x304021c0f060c1701080f1509070b0c01060905010605040f0909031d010201092103050901060b22030507260615060d110301240206090a060b0d0b090318180105040b0102 74
    0xe1301c40c0c0d40e110180780d640d54403003803450165071040d000c1d240147d841365030480d4003407041e0a01818040c3c0c10154002481e03884142200819903a03007000140701509031040c0c038045c14840d40d40556451606100341c40e070401503080420140e2421048100003078103c11030741c4070004504a202c11030210034005038010441810054030141c521740030030324040360704641c3d40300169041d1410042600c413100c20500301c6155014480151000300f202e0343c9610440c5039401b4100706000c481c08581a143d554550400c6001c0e44000d05520301d2001c280840000c0c052807004d01c0413561b00074012494400004071001c10311042c0c0c1d80c0543c40010355a03640b081c407504075100c0c0509022a990f5656500e4001c0b0b0b0000182c0b5021104a50090707035414105480442c0040c050361842e0011b06190390561213040061a51006003540003081000040020f400d0404951084040e80003070754032550f000000c0b0784000c2c3c0001440c0e20511f1144800c25001028450080c15240296400074040b064103005038070f820500d5040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 389509739 1250 389508489 389508527
    0xd0b060c060103050d18150809030d060608060f0603040f080d021611040c08130308071704030f18120b0a060b0c06040c050a05181f09020304021c0f060c 67
    0x100600100080071030003102d4a9807246e203829131aa242601c0300d00107010344000c100400b44c07503000381c510a45180b82c10400b90019645801c2c4000c20300f40849200390f0000001c070700511300700170041c0381c0001c0c00341c5804029a0b4440c07461070260354058154960040052014074045a80d01c20700e1032680c16200f900000e050700c6920340015085c108826030300704400600ca2400e2000b001c828910800480780030f00c4502540040324030342a42c040d10392690052140042001c07039103c84580003984008240158040d4554104940b51440c0c000c00304042c04401070301c8804004003c00840141003280d0584a030070424601d020780303414900f030001c0c1546610040d0005004a6010305960300800e185005c4e51003a0200c001d41075641042c049050121b224083c0c7c4010314070002c810b030905801c00c0300d500030301c1001d060000910054204141c1481c40e001720b403000764007000300411824008103600e00d843d414401c44412094590354a00b010328a18001232107151114060070040b4041c8000034150111404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 389510989 1250 389509739 389509741
    0x1060e1509120c0918060c0a0519052a0304032003030f03010e0609040f02010f0201060b1b013c090b0f04150c120c050706020304240605060d0b060c06 66
    0x40c0302903540701c40941c1c3c0e92044400c4400300d0b080420310500317a10358507030780c901915142d903680118022641203602200d0078001d042000341350b10b207a131690303406044070191a801c0d1118100034035602c5001140b85c0282181072403401c1c01f000000c00006450031240d0240003501d490000110b81c100305141044856003620020590488030b4984d0400b45050344c84400708504c00b541d441c010401c00410507100608030322040c2541c4409548242c002d1003e4200d1030001060702a40c800322000d80d5070120544400c42400510a102400000c2c0201502c0302c89840010464454103a40c10440800c1510b0072a156003070342c1c83c9250240340c640c0100d840706400c401002c401d03140a0307180780040b0000b240c00b25a443c2c910503009040303804910801702c03d410380d5078800b400034005045000082000010003410b00078180020f9000541900083d8441c13407240840c1a4030051141c800d0310540100d2946145407420280148a41d440c1c030001d41c2d800010542001c00c24118083c0450040c0c400c03400640110301943d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 389512239 1250 389510989 389511019
    0xd27080d0509100f0e01030b060702090405010f0b120705010f12050406140903070c0519030618060e0f060a0236010e0f061b120a0906140301060e1509 66
    0x242c841c041d4190703101030740b21040500c00c0310140c005106103008200032951048140d403196000e60080310000d0041032030030a03290009082000c0c100c0d01114240e4444be000301c03c0d021a070103040340000c03080d01c100a000314410305640c0c8503000c901519042001e208443d5076928442d00c8840c3c220701d0110810002401d0904090700070f4000340b051840402405808a2101d0800004890240f900085a2015030b4141020005080c40c9090003225581c00e05c030002c400b00e51306200d00c00c54155a024a00144149854040180e65014441e0012504038a504115800c40070849540c02480c80c0030041c0d58503410352846492071100b02e00b503080e0b002c1040350407d0001c5688458120380f6400d0301c910105460305010440b41155032802070741c00000a02000200b5920088040210355a6406941c5403c40380d10011406420035564040000d8481c14200702c0103400ca01e68081203070b040744503e89190304001000d0a0200003060143c00307107e5107003201001000d0003040e1408140001c050401c003c80340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 389513489 1250 389512239 389512247
    0x1a1902010209100f08010b04060f031122050306070912030e18040305030f0f0c070b1017100b012a020a03050706020c09130302060f1b03040f11030d27080d 68
    0x44c0401c035010900190000c200c2028950a81d02101c0e031079a101755952086080031009000002c4607204040380c280706403202041121058142415150700b01c224440c6000205481c00c280581090180001c3c5442804201c44100d58500344036054240000da141940000c0303042d00c01c098500c0c1b11400c4020007030108159020340150f00032800d51802d0803d9854002d82880350300703029900104191410800790001070303a100161640210110070148a59035a2101d28203c1e2050b00701002941d00103060174584141c0d64844d6892580b4207103454040d800c000400203000080302107101c0e0120540744c4400e4110b54444d108500a50b030701030300780c80d000c1d9038810700a983c440346810901d2241c801100001d44074005290103c80f60764050b8000c02850b164400003e80303550003d849070340c20541404046c2c0c01003060500640c081c0e44103a0448030009014180000d03100108a5031900c25081556016807a5078030440351078082220400e44000940c0e51011069040d100c2e6002040030b000d44040d10000740e0304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 389514739 1250 389513489 389513507
    0x120114040e0c010516080408071509090507080a112206031a1e0109120308100e0411040b010c0b0103060903020d050c06150a2d1a190201020910 63
    0x105440510181d044803000c541c507403140a403a81d00203007003403000c1d42d4040314501302950134500500000785015103038800300c0c2c1001c0c0c05402c54400c103030158520b45076859001c0354003001400d10120400450802c95402414501e01410f2450041c1d03d51607070420300784458044440f402d06050b0b440740d20700c7c512100020100080d10803040841e207080e07a9405030081c1c04070881c014036001010b8540a45a0300301444110320b50704040303410040c4044010811880c0d58074803c40b564026180c103c114a41001000c0405906401490a2003054030501c4001101c103000c1c09e1091a08813008156840f03034a00480321000c20a40c054030003802c8000000a22030181d000c0c11426020781d09481d0150078040060380c15104800003d02c007507201200181404105945100f0002c400411007d22103a80d0f0300d004a660401c880303075490081260f20256580c1000c040c10740d00910410100c1c40024079500b0140e0024010343d402614100080020002118805e504541404c0f10040c104142c1141c0700500510f1015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 389515989 1250 389514739 389514779
    0xb0a09180204180201021507030e1014070908031e090604090515040209030703110d0b1f0f0807030b1b0c030304030f0302270d060c030b03070f05010906080405031201 73
    0xc9080b080d114143d0b0344038240c044807501030b00180074135000c045255070001c0c0d000300610100360303030740e4100402260301740030611241c0007491010801c14100c290072a880d0201400601c10310480c8481040101c901005440320741d00d041100c003180819006545095104120203164495400a0302080c01c60141d44001d0041240700284c40d40e400400d428403080b8424034824550542c852002000084d910460f892a10f0101034480700c84005c180e0b4030700e403100c1c03c241c403044240102815101e00c0000d21404180007003039050040791407180382035205620354030f00d401b010b008505003100050041d1185140058100b85c603c042507078643c0c0c103090300f603101d4000780d03000c40000d80c02d0b002540c2854460300aa411540c120920352100103024070140305281d05455429400180d880c0d840340214285200780524610306840c0403802070b140508141c1400d0507038200f040180000c6100b07010301e03688803a1070010354040303080ca43c9003510b450900c3c5144d8000e004442008044030b20002c01d07445c220140350130204e2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 389517239 1250 389515989 389515991
    0xc051315090203070c0215070204090b060103050718061107051005040e01170c04020a03090c090605330307120903020d0311070b071d03160e0f090706030b0a09180204 73
    0x98844090805900c010744d841d80002d810b500c040741c054600311801c44081400c003684949801229030100702960790385035081d1500c06030442044103d50301030081c2c6030311072401d10340090001001d1400d1a0902b51500603001004060151241000b40c10400a4007030a0001c000742c841c5900000300801982c0140660001d00060800004002c4172249040b070740600030034045e0250941070340c10300000703401c4800c43c40101900c5614041c0410710411210020b801c0480303001c146142020140101001d5030038200400b5104040080003058400401d8040741c076002c0142c0359a5280d503107082f2070504491072004030f450324102c50035040540010b008190654652028072600005002c100b4880c0a5144003528400e007000010b00c0c2c0a02c955809101150b0840708002e0001900b0042444c00030b50700700081842c1150641408288180300303529a00003180010039600703140008000751070b44190301c42c0e501410384a800300c80203551201804030140052900c104801e90b41d015100c0c0020701070a00c164029 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 389518489 1250 389517239 389517281
    0x120903030906040b061801090603051203040c05102606010207080f1b0f150a03150e04110a08070e1906150c030306090f0506120c0a0314010603050f0312070206070c030503040c0513 79
    0x103380e036a000c0c0c034840d680002e04ea1000c14a00700900a007a00503002203020000844541c80c0344007610083c0d82c0500c90303461400f0800d85003c0002902d00344942d0802c50b920b5205d440038603000711000409600d0923012108050101c91a9004103651040703615450307510000c0d400c050b94442c00709402420304500c146e0b4040c080d03501c4c0c42c0d04840d00018240607040b40c201c03100e8005008288070040c1b83c0b213220b101030402070343c1079a200304141c248039a60300100010034681c1d0900c0b15940800700da04000c04001c040030016945400c1c0520016070341101e500e070610408500510505010b0303070080004280c54101400b0098811914000421003111264400d180145140858000c00602c6458080000d40410940c60654440100c9810b080c03980701000d648407200070000031001d00100b08200c4102d1300840d02e4817107a13010f0300410300000b408101150f20074010406503640c05103010341b84030b0f01810080c2e0307079442e41d08207100d55202d5604015001004540e011341c4201c03680e4000301a0900c18441d2a060b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 389519739 1250 389518489 389518513
    0x312160e0a050d030e031f0c0e0f060301062303100e13030909091704030b010e0a020f180112060303020313060e0306070f0909060605120903030906040b06180109060305 74
    0x1d100d003500446030007800c0101a800001c0c000e004d000d042800060407070340d001e00c1c1013900d4210329101c0005c00300d016407154603811000390003540c8140300c6441107031683c99103840f0740040340d0309020512031101040701101041888415450301c045111900100050b0b0b06e00c0c0c80b5801009040c100d03c98120b14030b07032407800550400b00c10072141c601a03038541e80d4410841c0c901080400030300081c0100f0b17550350356420b00000401c0c40c0b005c02440114032424480990350300d424912401c011004244a0714075004024011740c980700401200d110600442491022040075401290740300441031510203603c0c6410340100906400002a2482201403803200342010b4690000b201c01d00040c01ca61505980b00300d010440a5005040c10741030300c1e85a2421503480c80c0e8031007003081a6080d035400007001c118001000c1e0980c10206103a10b81c051403400003140303542041a0300d2503035107000070006042944204042146907407449020700d10007a001303515009950312100500000c00003844100d501d40b08003107038111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 389520989 1250 389519739 389519749
    0xa0209010b09030d0815032a1509010302070321140604180206090414011404060b0c0d0c0503091002030c010b030601030c030803070306090f09020907090b1602030312160e 75
    0x80c41e01029004e0007a55144038000d41d490b030400391810801c10420150a10b4030385017002206000164a81c8003c0c1600480b07204103002001411075900403240d02000e4032120300e5200c100c80010a0038640140d0783d80141c14215010140c000707259102c5010003020006ca0100c035003203465201d01c00c81c500030041c1c403920704100c129032405141c1e441400c41407403410301500d4000e020782883d0501a001007a1090000c403802c0b0300a400341c202c1c1c40711012040b0b0071901c1e41454400c03132010f00002c504161412406065195442c0780d0351580b030040cc202110190301b0010180140d03410a0030143c459141d84500c80d201946036000003802941c0c0c4c1d880e04c50b40c0c07d0701e4640010307a1412650808189220a070558079000885e0b840105024113041e15050000303201d042d40d100301c022a86d2001c100060341d0b0138610400901c18805010501041800101445590b5188089680d500f5110b0204c110720301e100e101103420750041100da04202012842000602007000000d2980201659940d408004603001042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 389522239 1250 389520989 389520997
    0x11040501390b0709051e0607140114090f070f05040504030c0512040501030e010c05030c0c0c0a0b09010809011b0f090305061305060a05070203032409090d0f020723060f0304050a0209010b 82
    0x4040c9441c5c1041c06c045414108004d14582c0d020f00020b42d580000c00c0700007401e41d0400c1e410b64407103101c0074042100a1805000007108000c14070043c180e81c074584540b2500c96481401418851580d40c0081402c05000d140c050816645c40b009940469180184c046699009441441c1c00b090401c5440310014406104071b030b1030410340d525000d003592502c5207a0300064028041e40030640c0300344d100e1885140c0d20f00b01543c0c000c1c1120715282e40d0b42d04510780010310321030000d001100140e040c0342c1129884110481001900b1066181a43d00c20150076821186210140d20140c40c60113208144007418000c0489012081d00070401c0341d00350345499040c0e2013258422904440107800c10f02c0400c0c00019a145080d0088407031040d21520000a0400624103071030554190006501802d1001131840d0445019288440c01740060106145441d171200b503000d184a4080c1c0c0c1d2080c90201912055503050140d407019000800c0240d22031410b40307000303591158041400e0348541030001c000908140340604417 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 389523489 1250 389522239 389522269
    0x3040e04030e0a031a041106030f0612070b120103030306080d0e06091f020d0207050a0807090c030e0a0311010b220905030c010c050d11040501390b070905 68
    0x5a455511500d04458084820500781d601898804001010030241000c0f42040000c50381c10600e45e003814906100020740386043c2078010002441040a0039200420981d0300c0001560b18440d21802d1010301c500300300c040d8001b90504400411800700e8640e0403502a4166482900c04000d00d640700c0700b03100da407030007107070070017400a01c1000700c06071282060700c060550b14401406142d00800e455a40d081c03c00754111030540180e000c9038000d181250704002c904001c140641d101c0c3c503120300f00080161124818020104440c0d15100c0c0c148805101e5030008500005c00425150a281a45001401054840b0001c1110340c01c141400b1650700c1c3c440c6107298244030709007810282242100c08880a000c00b250709540900090141c0d080c039890038004c01c0920309640c0c2d503155881d1749400d1031208841e800189a000c1110a02c414406039802100c040c0d0480003151056010510b02c080703200c20400020240f0428140a2201d0402c02403500d42d17041c080c01054450340304d500d484138140a504a10a041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 389524739 1250 389523489 389523509
    0x902120a0c1a09090a021c0c2a1a04031215060c02310608010209060703081807030605010e06030604020102070614070f050d14090108041202100905010b0406080304 72
    0x400290410340b2078510030240c2c0b08003060510b014400000c2010074200d800d84400d940001d40c0314000140484440c85880f2040002c00c000541f8031001000045842680d002c084040144000607283c1c601040303a03071507441840ca1255503500071f5416080c0340184d0302140031400342001404001303028001c000605d0b01894890601c80e141500441d02110090030aa070065000114400158088080000348076a03ca0320103802da00c0440d0444111000380d03120001070703441442010b240c1d5403440200c2d039250740c043c03a1240d05521210000e07508110a803544071000d02c2201000400c100b0a900520b040f1000c44804107402d0b42d0310814036488120031180203005070080b0005100d003034050490540100c0325401c1c800d013080000e541d41500c2000703801c4140d076141c0c403000034608041d030300c081086450001484914180001180040c100b500064002031000d055500100055032007040303040500150007005101140080c10280c3c001e00d403004c2c4450140d410b00c0804207412034000b048904551001807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 389525989 1250 389524739 389524763
    0x406020c030f06061f1205090c0f010c150915050f1005191712030c12130812180318040c0905030615010309051618051e1b0d0902120a 59
    0xa51718013000d440d00003a2042c003c1500b0540d4030890781c4e110303061240000100403c01406010200005d220741c0c54441410007140c0260407000499500300340040c50200d420104883e01c86141c1021190354001054a45074503000c00c2000201107841c0c603501039030100c650394400e00e4030340091007600d0f00840020054080d10f20001c110003410700c441e805080044d9821344880b0360001c1c0d26028a548260f031749411104001c41c0403619420400c07121034100305400280e19074052941c0c5c03520b00340d000d180800501003200b80005000000050b0324512240746080a03070707560764840758403080d624001000c068000c40c6852001038190307001c0d0f007044007550030040c020401a80c0380f0310303440702d020004810141050340720302849000076010806000c040800c01e42e20b9190505080703403003440303481a00d4904441401c240034400d1218004003a0041c0f28800305100d085680d40b2104170001030807490060b000740c14001400810740200d6442101303224404c861200159600018050b0b5a40b1561001340c00c80400c0301c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 389527239 1250 389525989 389526019
    0xe0603040807030c0c0906031407060206250c02040c03050a0507030507020a06020c0c222403080a140c07050f0d2307050409062a050a1407080406020c030f0606 70
    0x2c282226213601c10701413041020f844102c0d0000303031640d5500485606000c044010303400f46061044074050555440141341c0c501e403107113855144400711001a155a01e680440b10481842210032a03d5250043c0c0240200380c0c00c9040100184401c0b43c3e450380c01c0d49403401090741540700e4042c16001d103c440e801805c8098140c0c5494000794402d141055507881001070810103910f45c40c00c20140149140c0c00000200400325a12044e10b582c0c0151002d401c039060018103112020001c01c1c01074a410912245d290928117200f5500d500d080c060070300b80e101004c1a002094040040e104040da402a07940940a060b800c0a224080440302401041910340000c001d041507414041d202c22000c614048528083e034071000309046961615060310102d459141c019500d8801d201c0a031003c4844401c40b2031030b0304258400401c10b000b10030003002003100c0d1403040400030900406565090342c0015036103a46544e6190017035034484c1010a4503005e4015800545240711020506903c03585000c3d10031840741030b0302 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 389528489 1250 389527239 389527247
    0xb0d05100b0a0302041a13090c030f0510050a0e070b030112080310150801060807180b03090c0a12110603090a080d021b0703031e120c020109050a050705010e060304080703 75
    0x5407181e203030000110040040942d49078040c2c0b2454989400e2a040d0f070b44004400d001c0011290600f5003851030410f6030510000d000e1404980c200c980210300364200c000c4520b01b003800d009600402480f914101400d00c072003c41c4c01e61201455030001011180e01d141c3d1114050003e0000f48160359001003103c6001002c14000c0e0011540324a0b6084000e0740d00da16a5039242810301244105d8000450720001808169080505550001c0307141c2815a4080515000249a4046802507100d10a400301c041283c20404001402d0762880007017030064840d0726581485018003148506a9031990207007545412400c080c012240a1091103001d060907001640740e24850354025908044034580c208505140c0860104050703010542000103444880d08d1410001c020031805910500500340201d1000102da0708904000c03202001e03882d001c1150290070809038010301210201a10700e000300000f200401c640814030700141c5a00340c0364000085e48003802e00031580401c442c001d0a0038820800b5201082c02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 389529739 1250 389528489 389528501
    0x909090602130b0d050c090f10020712050109050c040b0612060a0909050d0e04050c0406080c0702040212071b0b060402030a0b1504140303070b0103020105070501021e0a030b0d0510 79
    0x28060252412820b205600121051640110140300020460381d14000d030700d0041d2500a400c0c800524104000c0000141107268101c044921585820390224029802440000c008028900713001205600ca8103055020708512002115240584070398181c062520b03100e034554504000d8001400e01c0c140c1c4071001001040a0803082d03100290000018040106008250129200386c010f0700040314240c00c0a46030400c0e204005200e141000b04024440e061941910101c40721898010115220b191081c142071089000182d046800081c0e0710b02d00203400c0124a003d050181d9400300e4880e20002d051408529075600102086100400719025250680103903030461031358200007a0208141c1c000801d00c204030103ca10112001040420220384052070400d14074106034082c52a09245603150400c950050100034140000031403a6010b001013503054442c94250304004107125480b00d00c861626420202904000a05100380e241080c141132080706038140d441001082940c030f401d407001d009480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 389530989 1250 389529739 389529743
    0xf010608040f260a170420150d0506030d0503010e010303030b031c02010605040b0909120c1f060e010816050907110106090c081605040308070c030b09101506090909 72
    0x10742e440320114903c0c00824800c190600803068284e9410006030041d180d0b02c0e14420310121040340c5020000441d204992080021044a8031000105028070000785240c51089a07038a0425000c5058140208140c2c0b0203070240d44110125900e800d20780200301c65604c03090056140a2510000420000780242c00c498180240141500c2d10005480c802c0c01e580b640d401d2915006030b441d4181001241400d12a60013004400e95a5100078a002020640c0e1840b01e403040500591001414091891040c40f10b04200c50401101c80c150000802716080980305074058100f00440c0b0400004d88c4800c00a115200207280800c1840f80920b03010401c140c00100500c1c001c240540084441442802071146802400f20013600180d0f14083c0000100724610090044103031010b0b040c00401d1450701311043e20300f2203030b000c0501c0341c1d110b1662030301c1c41c0703e00b54540c4010702845000b000d11881d9240400e0000608031510800c105001e003802c0b026030760207030781c0c4114004900390b032505010146c0e0b5030704050b803664 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 389532239 1250 389530989 389531003
    0x3210c080d0908131a0403030c0b06030a0b04060b090c120a0b01050c0a03051b0d1e03090206031632090411031602160b18030708011806050f010608040f 67
    0xb941070703268021541d03c803564622038905980e00c00d10501c1ea000d01518541400c40c18400d081c9800c503903001d031002d120b2401c00b8003c1000c0f000094060380c0c08020001c00d03990b100c0c05a00543c180780c070f40f1344041d180300d20744503100700a908005220081004152449241c0490003c9016110700003404020412600c1260421404002400907035000b000740a245a10a0341c40a81d05e10612822031b032241120a4a40603a07000390348031070003459005240782000c091812005003680d529500c2580100300d070400c0203411000c00300070403a226504011009045041e601c1d603495a5503021001480c1620100758a04000082d04a100b900384d07800c005040403e8000e000090403401c20702410480780c000301d500500400000f00c0c0800926810300210154145402000618504110300c0345000d00400640c0000103244110304000c5076010001d0400030001580200b008102d46102e92100d10300b04c05003030b0f911034244000f05030245c0300541c260741254055540d5030b170700f52155503c0c0392241d903c13400191040c2e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 389533489 1250 389532239 389532251
    0x507030203060702071e060507140106030501090303020406030c18060c03030b06040e0415020c060c0f070c0306020306041a091308070507060509040c1d0f0a120c03210c080d 76
    0x507103040081e1030048503160000c0070b11500e0440101c0443c01d41c804c0d82c1d944101c804c0410001280c1000c01c2d00c030360b40c0d40050380080c8180e070352819600410b0181e00280ca02c1d801d10441d030080c5a00b550040c41522101c0d6000d0248000300303403003030b2040f1130391542048140f0f81020701003000300e05c1185040c4a240c4a0319000c10600300d07160008100341c000740c01156040c400c0c0024030003003021040800c80d80042d0710b402981008a040c032155100ca900500612048800146100d504200d480865506940c001e50703601c0544e03100e0804800a40088030b041d8015450f2108980004505504043d10b48400510b0307884c1e140d68654a0801004003280104c403a280180304080010304103205407800303010150344d980d803a82070110404c81510028035150043c02020110356001204a2a42503400d032015102041425103034404506455001e5004c0340a40d07103001e41840410902840c400c2c2120f001d050810800c0100c00713655008851480c60501c00f0592b01c074603900c001010040600415545920000b81e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 389534739 1250 389533489 389533493
    0xb0705090604140a05220b1201090b22081909081b1309050a3002030c100b0303071401020906040305031c150603020c0316080c1005040803040f050703 66
    0x36045900002c1d40c4120f00c0880000c82e0414a0b1001c00070113086680c24106640314001c90802600b0b03003040c014a0745c40d01c2440a0303903162540c10421214048000304400c0e00b06052000032200c0076905130341c488100105002c00100c000c80e000910700d40019605203891007056049141205c403a20080c00d0001c60a40052603c405012074454050b50111041c8090516020000d440a2502c00795480600e00032002020846c0094511241036002541600301c1d1100480c1a00c0865001010100310505251800089a022000e014032000d400704030b038240c41448400005548002680c40d070194424005803010500340307214003403e01c2c011400186403d02c844040f84280d40075400c281c4182d480080c43da0303812488240f4410325046250010803070092214003426000f0100d214840070550003050000c81d2040902c102d8602c500504902101c400c002d10b0030300d500e5040602080d02d14068462414411105406424030496200d440c540c51a0788695440c07076409100389055038540710345200400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 389535989 1250 389534739 389534749
    0x1141c0603211403010f060302071506081509030c061f080a0303060518061003021809070f02070e010501050403080a0c0f0b06040605010c0807081e0409061703160b070509 75
    0x160203000606890442c2010340003070708a0803180301983c0b140c08200300402c42c0388000c0198074181e0361a481c016a40300c08a0a081c1e0750701c4601c295000119241c810002400d0030005041c00419807a401251040d6480c1c0700d0b2a41c803401403a80307688194000c07a0000d030403e0803c602c0000502c00c0410140c83c1a034131226007a18100141004030007182d1b46080621451803c2d603032855423810544c02c0107013249090004210380c0c0e0f5000c103c1c03001b81500841c807030b104103144605003820f81001070058001071800100041c15410100c9000300980254140800d003d0f01c2d40080300d059600c1a140c40b031400e891695451005e43c4401840380c01c00c443c006095001030a48003598003001c1c000c8400c4c030910f050810400082b220b095100310f06000c011200e050002e24082d0a80390006d81100e001030700c900c500d190b080940d001580c200400b4450014001c600400142d01940035504003400c900c50300c846c00412141c1d00c2c410340307860030004261444100c0004101c580c0c000e8ac04241458800c0c200340200f408a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 389537239 1250 389535989 389536013
    0x613030501060f08010902030c1e0303130311010f0906141c0509071d0f04110307170d09120b07031806020712050301061403070512040b06040b01141c0603 68
    0x45841e51a80d0041082ca100716a6500140ca0214020098102d03180e0000b540c0b100f5100081c1e006202c4244040105050003000410042c0054142d0713540d54041d40c0f81082d805028042180c2410240c200389105501c2001c1c0c0701000700080d2034060b0300700c0c20b240054a0800071146030304500b40c000c1000f01840350f0013440740d542002400034042070f03034144203c95a041c0108c0745c000f0f07548494003607192007078204440038103500441c04ad0f41c4180c4584a9040040c40c000d691840c940e0903100d2600000b98a400290403001e140e05c03d0380a466002c880c0c510121100d543c00d10850040d0051042007001161130019082d400c0002c9040004102070340c9060040c0c50b03080300d502914030a50100d400300c01c0c02a05032450000d01d680385005440c540c1480340140100d140c40b007683c0c810410103c0054103140c02042100e14217540c90130041d02c503103020312f880c2c004c046045a07414002c074141803c8680388c3d402041040c0030001c0c0082e5007824240041100072554450852455415403290301c00404120f106070fa80b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 389538489 1250 389537239 389537243
    0xf020d060923010e100213080102120406060509150f12160501020105011a0a120209041103160903080901260108060f0c040b0f0c010f15140301021201060e061303 71
    0x12516091003081001840200001215250b41021440d258651380450424100b4404410058440516620350911555590031811042d031000031381004074003140c1c0140c2c0c451803150300d0071301400d501c6005120081e103050710703181d40705900910700d4201c0d494030700300840b015007015141c1c98020080c03003a8149091503904e01c64420309003030300d0184020350b428043c107400b42c042240c2c01c400d1b10740340c8062500c082c4500c402080400a90b040001c12810a6404030703625218001c200f84075400004001c052164802c1d900b1000141840c9a51940c2c18085c810440490703421400d4a4286034016005603088290480c4040001e00c0d040e8410a0301036248512901a04c1858000d146620389002880561000548101108101840301304481242441100d4540c030a0241041c1c55800749001c03e1301400031420b04c07510300d5043c24140042515602c94260413205941031880d80c508407182418200e10a8040c1e48882d2000c042c01071000f18011119026504c00250440d860304420302c01245041107aa041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 389539739 1250 389538489 389538503
    0x9030c0614160903021e03030c15071205190e1e03030901060e01030b27010203130b06040207020d020f031c020309010906080f0703050601030204080d0c120c050601030f020d0609 78
    0x902c012207001090103005400a810550002c41c00c50300010071030100e4222251111008034028071b455101401510404210300044652013100002008081102150301000090050304040d40321003440c02014001e4070081e401841a00c1e190400002501c13483d82200512b01c688072201ca041b201e0101440008080080a181c0341d00304607109030700b5030f209903024050100c0500d0040c40491440d400c0c49070040c0300e030740038035008506407100d05a030030611800c0c18480d94401700420030074402907071860003c68842c101040460343c44008000490080810294210450f4521400141403c0c1e01c0111005030003400c5a0100c412400d00100c03032804c580f80b000058001155111a550300041542c0c05044107003171000191070007100052b0200c500a000d00304040e180c0300820303110390003039040324040c4c000350007501d030034421640000e4509114408102c030b01550348200300309400d208030760441040760b02c640940305691854403039007c50441220160b07030086207404038000044d494401c5000c514460b502c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 389540989 1250 389539739 389539741
    0x1c1a0607050c1903030f180314030334032f040305010f0501181a10110601081605060c330f310602030f160e031009030c0614 55
    0xb003032001811998081905000a07020b09000203900510000741411041c0360854110b00320b840884820041d03039202400003070072001d489002d40da010005610a1000d01810032170950500000001c0101c03481d05484010a41c0ca901200144660001d034490100c0f051038034180103403070030103e2040304103804011541c400003501700100701c401c1c02110b40f0902c20382004c2001d50f160400714452060403003100c01d8165501e8550a418100304e040f02080c009001d41045144c9a1515001c0d040b50b500c6455001d60340f01c0c0100000d1514400182030450604d001c21859100b80790400340501c83d0060212103c3c0c500400c0038082c0c0111240c1200920200c00c180c003501e0a0061404040261501800680703040c0c502a041025855607003000d40c04114840d01c2060503403c0445480341c281c25040d1006004500002c140681c0000c20340c0d00501403454412010046801044159603940d0340d40c1880d40c064100c008003000070003180d4411062030740130b410b017a0341c00c11190b0ba44408440d50140484c1c40441d01c8c0c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 389542239 1250 389540989 389541013
    0x190204140907170a050a02090414010c05030603070f1a03040804090504081e210a0905010f0b030115150305070302040306020c06010602060601260c130602070302010e01051c1a060705 80
    0x107600f100498080c0005080c3c44030301070300c8050300d40b050140c0180c001c243c0300000c1010042e84680c22480b40e50707400c00030800780303a0300d0100500503401074445610920174180082640c2101c0c000031021503c9501040303408820440e0180e0464100820586a800301030000140500e014015203104a101c1c81d110307580c5400e0300700400011100c0d00840309088005106c045c07038201401c1c02c3c604452100380311a080542e1603002e1203010780302401c4000c103d5420031010400c081702980000c881000220000c2c4100d2211608030419940240b1504030302c0820740c180002154000da10203900040c95290161403e034a07030301c0d240180c0e403011710505619408000104402c1d64107210b100c0d041802441d0400c5840761310701c50909025407254440ea046200800030078003616541045035408102d05144003022603072250065228500c42c40182e004c90710294103a41c15604c01d504441c2d0300501ca1461985000305454403400a040f602c811101c4d8078200c4441a0a968071403001e0100c9503c5180140014402d003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 389543489 1250 389542239 389542259
    0x1206040e0a03080403021b0325050d0317010e281d030703030501050307060e1e270a050f042003060a06080c0a030f0807080f0301030305040e0f09190204140907 70
    0x6410104072903c250303030400807030781c0c02149444030301240b20449c00424024500358a11040310f544001e911141c2c644580f003c058110a941900304040034000802c0d81e030700e10710480c3d401c10880310401407660002c54000e87d26014150302d20445104000007903d1a40302c0200c04100000c140304170040c0d88040b03200b1040582c5401240d016200039006480c0e020b03d0148090305884112180d9449410221841e46444d098010104201040200100310310385a00702c001400f6400b100caa240c1041d00200000c40750822405400e000341d42c0c440c803041e0260756589590841c1800d0400800c902001d111400c1010b9800f045281c4c0100480800061404d10f0003000501d44040d00c00716a0064048840800114403144002140c103a0024045036540381e15241070031491080d448800b0144102000100602d5030010280054800a800c5035251b0f0710750007a5240898012144205280c2c0518454074000c104002650840b901c050004150019911544601c22900311384401c043c0c3e000c40340c1080305200b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 389544739 1250 389543489 389543503
    0x13120f050613150e030f0430150c03140a050601180803031506040305030c0606090a1e110f0408010b1f050909060a050d0b0a0e030c031206040e0a0308040302 69
    0xc03003000d05440110a41c2d40701901c10b41034004442140c1d0340c042a04150b5024000c1b5041400145416580d07191100d0b00c29040c0014003d01490741e1b50074a44c280c48d056015500b89041640004000300c5100c600e41896024210540800042540b07440c18280c1e203040c100c540a0003074222090101d841d240c0310340010846215100c1d0344004803402d400c00c01c128100403003243c0c0c011802d0303100e0440e01ca4000002c11404c0c42503610042003840002510414103002140880c051003088410407910f80301d0801c401e0550b800510038108214000d410520320003926808454950300f0344080a092150030f85250310607401942c0f140c401760b51a06600f487c00e1034204000d03014041070224030f2240a90305840188640a0021003501801c048004039206030b8a0000d40c40040c1401094048007002c0c07403801445c52441a43c404018508160b14100030907408001e0b6040403040070b0013541808440c08103054036500142000e9042036582e148070704c0640084c4194110107020b6100c0c031501e801c051400034a0501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 389545989 1250 389544739 389544751
    0x10c02070614070203120409060918020102031206010e13021305011404060e0f0a031208070203090f090c090303210618010510020f0d031508030c0705010513120f0506 73
    0x300c0d40c024825180c000e41141c140444000c500c41d202c000c0c42c40800c0c6840d0444941d1800d0f0350700440c3c00660501c290b0014026a42c0c0f05c041880460705007003d0600c14140c1e6140280560000d101d004010640059040d40c84171052400c011031a0440003c14516942c0903003d1003a00d80004008140f840c0385c20041d0020602840c11074901701070069030742d20394040c5000c0e103800c001c01841d81a40c10394a0b07158611418000914080003a55289040701040315046001000315401070b000a07103060010044d25084007018002e00c52803000e900c00c005e8a0075005083e0b0741086424010840c07030762020801f81505034076206851400b142c0e520b868607658640103100a22641201c4014912000d403c408181165016504503c2c2d03004200426030500c0110741c01001144141149051680c0e8150440000d22160424002c0d603503807075441d004e882c3c0c402e0100c01040ea601850003007013035500c1030004054010074034283c11100c2d5180c01080c000360310485030680360004120140c20920000380500c0b03800403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 389547239 1250 389545989 389545993
    0x30703232206020d0507050918010803041509080a0503090a090207020d060b032a01110105010305030a050702010903061e050105040b0d060f02160506040b090303090604020d02010e0405040311010c02 87
    0x21800030010742a480407100d1208050410000307280c200011901920002d021260041c003403803510040040813074021a0140e446074410101070140e0010f214080c44c140c0386100051407425081064001c0211440401501000b0703003913a0005480e43c040c04006001c52082029507503410407031041008100494200c6e283c49441001110700503036601035280c030390b1a402000800c0c800f000c40002410301480340070303a000101011540c40700400800b0308205040c1d03000d8891120041c1c00c0010702c0e003212424000203115a0041110705035240c0210041d141103841450f2810f5015140c3c1e80396016610480c02030800d402d8000194000a440780c0a0680501010340701000442107080000d0100f0251260150156641b40e00c1548491300c1d6804403a402c0405884420000040b490300c01c3c0d0715101141c0c1a20144d41c80c80204000c0c0002200f02c03406505410300078074947d00c9540801c04614141102241403100c0d15041c000d0030b45903802010303c1036000e600c2c0c038804044ca06110500303403990b490303880c001c42d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 389548489 1250 389547239 389547241
    0x1603060524010c0201051b0715050a08011a07020a0e09070b09180a0f0606081504050403090b090604090c0518060310060e0d0c0816060806060702060304030e0603070323 74
    0x124100710300351012182403800e060029458001038501c1d100c1c2030140d003440860203402452050002a815086503d008210a000c10061400b26002d0151501c20310001780301e03400401c5003a10030750007070342009025000b0034030b0415242d00081060a196000445101000041040070081402154020850340803514a0101c110300010750660180030960010002180401c40c1114503901140310111010350030050705403a00c0014108980c100d400404142064100201c542414003e0354003455040c2c4a00300030313500340f00d090b0440c0d410441c03803103401803000d2000058900c260701460030500d2035921000d540b40c002044031000308008207061400f0750000c0051003400394110902604407060780ca464000d40c200b480000b14036074050400a0400f10003d100803c4410010801442d4110300c440321102c1036944d454242d400103c06c485895118209010300c0001d4100280190751080c440e1030460148061500080d600d84c1040d01c5a00019981d004e24082c210064201c001c02d00201c0c089910203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 389549739 1250 389548489 389548531
    0x5150906090d17010e150a09092006030106050304050a0c0905040b06030d09141309061d0c10080405030c0a0c052128350702090c0a0c0516030605 64
    0x80700c0c1c0c040c0701d8401700403101c400003000c181c00c0420f4034480da0b00052900f2070066845083c0340150030070a1040d2a2981c041c204400039422412000312008000780816003581c0ca07101050710349400c0108162511f020724054640044c80c0480341070041c00c0610000141400d003420003208001e0b000384068000c0d40200302c210b440f160400352443c1120304102e40b4607011640365020501c1e003180c80400e9840c40381080d500b0b10822a07a600881a1840503c0c00c070804012400c24081d03440031603d4105800c03010b1030304903602e83d910814506034880d00401c03c481c605215010524500000103000b50303101400341c0c105009038a40418042c002d1402c007011842c030712084a940c66283c10030b4008403185c11901c080344541d0f19a0f4803100b403484035081401896a240c0403001071400052640240000501007889100313450f6080d002d50b0b40a540241c141d6400c2e03910a51804803da00140c0c0001c203016069601200203441044502c00c03107820300101d45512482c40c0313004020307540c000e011511130742035002007010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 389550989 1250 389549739 389549777
    0x31a090a020f100c020d05060603010c090f03080a030b1003050403021009020a0b1605060108060a2a030905010e1b040b030d1b030905130e060703050106091205150906090d 75
    0x11071502c100c4054101d070390984015143d21000c58030003500301d032003101040c013805004200240300e804154003d101c1c00c4017400045803252104d009209010316888024008288800058003824945007030004050303100c500042c031850450848000020b13203882c204003c055050050710580c1161803018010340c0000c3d4001507c041c41750080142000d0007040c411120214480b64543c3c1c41d800c03000759222540c503403402d107032603c200303c610009440c00d040c0440c3c5840042c1100c401c1140c441039003901d10201d50390045019214892040e901076490f004413000008041c44a010b551440d0000c01442d0f40e10f501c10710007602d6140107010300ca40c100681545103e60403a4200b0180840040f4140e00781c00d86140030f403030f880b2064101581104400c000e03034101070747c1a8030683c9414000001c5410f151385045048040d20300c01d000d20070015035100070030481d441151001e2142e061051042d21484c000d004462244500100d03081d00659001c84103000c01e20f1001e0000329030a8481c0e01d082e5558483c0018a40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 389552239 1250 389550989 389551009
    0x60310060c06020706020a0206040b0609072f19020405060913020910150503040b1006020c120a1205070210091a0d0b0d05030c010f020711010f1404031a090a02 70
    0x61101e004146410401c0b650704542585501c41011502d52001c040001c0d9034583c00c58045426070b12003004541503113044980c491089400703a842e02240c9109440c00103826007040d45201906580c1d40c41303901c3d801c4082c00704a403015888c20f000004d0140074010031040c2d500180155000340482028051041900b03441805000d80540d1440c0440d1110000700120440c180e0180c1108548509180562a0300c9002580982e015203c0d41c51340d500c604003075078106a0710307220725809070f0300800c011a41405c1003a820443c5007040e03020786400c064a6190303001c0d41072000b0a00d000180002075446c04501d001c0031000b80c030201c0b80c50702151040c140403144404451341c80241e41449004502e5940e03684040d0030584990f80c0107040200b4481c001d14000b981c0b0307040307944290b00c1e95080114009147c0c0c0a4802c0ea131b002504001d20901c5a101c92005444205060f07990303200b00306030200410010000305008000551103562450801c03440400714062007038000d130041240341c0201c034130640582d481d070181c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 389553489 1250 389552239 389552249
    0xb031509250b160f12030c0e180103020909070b1603021509060415090f060902040614010912080c0a030e0306060405060d02100e1009151b1103030d06080a050c060310 73
    0x480f52a000a09100021220003d001811203035800e440001d03555050f0002c0c04030440701d80ba070344014003003502045480c1003502c8140044411000042001d482c114800316003013103400c001d44904540b43c0000614030340c000d84000c0e41100d400050710080607030400c585c10303840b01d8161a502042c10421801c90312600d0280c03000e44420080c65000011100b80d501c00c400b51688154811091a91498400050078440c6c1081e40300e41c1c50a4000140b40642c90011480c0c04816500d0300c0826080400c00f401030040007106a421010a104912a500003000309001250194450210009141e000c040c58030a005140a004504000901940d61a075a024a500c60f40c100c1d0556600013401004440c8002120b403415031081148043c10010364010030400190b0f013921300250300c0420043c4080c0e41400655141c402541c40e000b46440115032880000d00045400900b81c0346480d0103280e02106640e03450f042600181c0090f5041c000b006401c126401050030b05845141c154030b08904088803405051141c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 389554739 1250 389553489 389553517
    0x5091c140702010e060a03200a0504060818070803070507080d140702150310030507080102070209070503070e03030304080307021006060e010c020103140901020910030b090a0b031509250b 82
    0x8500c08683c02003807019004c03a0090070050300c0302080c40004001d07081458550311101003200810740000450300489540070059101c49141c6440d00400321484140100180c2501d042c0f540c1c0c00d07400c0001403001c0002000a90011a12841a030910604114803648644643d511a60080350420703048040c42040a0450343c19584170b0300140042221807240300c54185500000000304a1500304c40c0c0fa2000599000350111010a51a40011401c0b8816607001035030100f1910001102c044c845c400541d802052072901c03140f501d411002180c03454006030f40854030300001208100d005941003044039080c0c60000d00901406150160107060103100c50619410413402c01c13450700659001c0c0d007150500780c504507003204091901900540c000d40200c00040c1c4601d1082c54651402482400b501c070b0320210040c503400f4503403070743e09105000301030450307000e600342c010100441c1e594403c0c41c81c001c1c8100c0c05d17074025055a14103941040034546c1841c000715554100d0200501018a08400f80c0701503910b0300310 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 389555989 1250 389554739 389554747
    0x15011d070314010f0801150521030c010e01020d1b2c0a080102090f10082d0901060303030b010c0b0f06010203070503130e06010801030f230f0105091c14 67
    0x8120050b00c1c42c0844007414600401c0000380c100c1013141c3d01011210564005c000c420103464111364041304500c64150b00c0018400840302405018410140c0c200d207581c2202d14204401032034500307503901e002c01e014280c1d50104541440f0140d50042455040c0c07403031000c0800744840c180190680c0e41d01000c4a040c2c0c0d4100440d03400340c064084888202910040011b00b483e80d80b00300e464041d6022400090046000c44610102d07401c004080c1c082074022038413203064640e40c002ca40214042c400c0c03184034000007600d81c0d5000346464540254001c50402001040060450801909498860129504200703690803000003040340d241106810003800f900300e00403510768000403442e5014190010305a4040002c0b0510b02c114000c1d4040d04036110056400c0301d070342c0e82100542d00e0105c00d201c003a200403441840340b0001450003400102100301e01c201001451003001c0c4d16440c00f03d055400103c00d0707540c5d40031b02002c0d0f1010418024a008040303000a280403600e4001070002481d40d4002d10351100200d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 389557239 1250 389555989 389556001
    0x121030c17090411041e08071202010c06020a0527030c06070f05071710050c1207020a2003010506040b030c1e0d06020405130603050d0c110a0b040815011d 68
    0x7030708039102078200078014018003c15030552003903640319210350b0240354a0100c0510032003080d40d412104407001032002c0d00042c1c0ca0403501c6883c4030b021510072810449001001d00001d44c0a20141103041c000341d48454030380e52424543d00084902e0341c1c620004011616119040d44d40001d40114018026a0360070380340c0c4241d140c000010096410010844e026203031001c01d4413007091088014a40f1000100d40c1030215405d07242c4200c582c151000420340c00104800131013600d040c44007a40001b80b82c0b0484109601070f03101c20741c038020348a655001d40c5110320842c0100d85024018981c1000701241d04100c800c24907c0080d98841030321040030301071402c1404c0040010804024221a06c0b0054189140401c15260410095106c0d0042c1c40c07085010341d00020b0720340818850030059a41c804010b0010455000f415117418800c201e0454020b0100101290981c942e05001001010343d0350407591070341e04103d03010303042c10513082c800780311010146d004103c3c00440e4404024068440203c100041e2610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 389558489 1250 389557239 389557283
    0x191a0c03010915030602031f090b0d020d14070b040501031425091701051008060609010315060506040f151d0d0602070506040516150e04020901170109050121030c 71
    0x21340c0050070240c400b10030458400811210b8104ea00a2200c007621165200c0503043c007144c14500c00e254110000b41c1a003001820122100d040700e50044806600d4003490000d03440c0760a0b420381006440c5640407808204550300b60248480a12905000c0e0740103103856102c4004a00e00c98001588010401c154188014021140400540003241c103201c0324400300d03600f0601a28054400d0b0940d0414940f0016250781c003c07404c035008100082800c89140d04c1c41d21010021074480c00041c800c5070f81d4540005640e03035414010801050004c2c030019030703030703217082d11808210702e21152030011300610030760100141c2c80600c0c22003440541141d5440d44a021420721000a00841d100103009102c0c0b9000d0200384040015040400b000b66654a00c01d2500d9021080c545803c13810342c00c1c041118907880c0102441c0ca5009041102c206250070000161600109030b4046000e0f071055024598490040c03000b1840c6041c02c900181180c82c603250740c200c6960f40100442100000502080c0103055000350519038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 389559739 1250 389558489 389558531
    0x201030204050901091505010c0209180c06040f0f050301021c0e070b07060902030c060c030703031d01050c0307031b09090207020f0415091505031203090f191a0c030109 74
    0x3e01611410368480e98150002c0c13505c181c1e00110328101e0728001606600c1016590803140d4041d102181070b0701c0724030142048418031416a1a039000700040020b0f50b0300d40e20f0151008194052407031b5110b515141c40898000e4054200600a0b401000001c600c0030740d1030000c40b418142d0603000580340784403c1003141011980c0d0030410048000194850034000a504400151402202034450022580f02000740d6846001400000c60b0414401c4001180c046e5004174000d040d411550700c1840e070002801030031601c0484014550900c040188540d04e0b5040c0300300100d6104c0042d001c01e20f4000048041d0074034110384902c3c5415070300058204110746030051803210000c0b02a0017030000d00e17200c81850012491500442d00811b00d01a28085440c004480c00d00071100058003030052080020b1942c1c0040e480205641803911a40409880d440010030100c02c000364202c40010480d0b0039403500030180c201101d00c592810540006000051888404a0f41151301d40f0b00c2c000303101c00b1841580d0620281d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 389560989 1250 389559739 389559749
    0x90f0b0405030d06090617210c010207050d050a02060c03360f0f010f0908120424060321020d050c0a02130614100905060a050d051810270201030204 65
    0x204040d00045c07041c00c0c40e080306003915550202e092090724080141a075130101b42c4500a21004d9545140c0d016001e00301c010032030003000c0e40c00940b410380c030b50b11018a844c04143c0c07032000160000601907240340d4180318254000c40f41620302c2c5d1035418034200e00502501d40e0007a1003a088110b1031496058030540d4940d040714007450003903840c144402c0f80c040f030700c03025a80f84240c81c550034040d181c280008140300e6511a90307070014030340e810126803140880024500510031618486151003007500340141074000c45c00201c4410010502500b1850007403405481071b81c10324210741040e0040066650041051010807109150030307901c50300e54091141c508100f000c0060f42199078000102c00802c165040041600e40324aa0039031511101800e22909590035013200002031044c0340c0c02e1256103040002003200e103c80385002c07410702c0e051380e0a07181195002e56a07580500241c0b00c4144548200788140241131a803000d04000340200281c01c6081072005504e8800c000e220000e6035403c580c029810381d00a08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 389562239 1250 389560989 389560991
    0x90615120b0a1805180a0c120809190312050304030e0411040504090b0a240e061909050906090c0a1202041b0f0e030c01090e040501060905072001090f0b0405030d 71
    0x40000d0b86001813405503080b441130041c480c0f51580c090303c0082c1510100e0741c000d030034034070031890030102c0c00e03944040c1c100445894908000e0803489607126429500a030862050500301d05203140740c83c21280625081c41000c0c00001e00400020a030010f400c5540118250344c0030807d40d1145c0d0b011410f5126903000710341e10910f00b004240510408090407842845122400c2000f00551203d164407006032218407201d4000003141070100018442c41c030341e00024040e01d4160b035440c0c180000c4012031125000381010f01e43d94030411220003010058190806d03041c001501502040a0204022410702c0c020030500144ac800c9a204540b602da0000141701c070418107540b0260081c00f0010070f0802040b441c0d0000844803d107500071031030046403030082400161030b40c1c045945880c10340c1c0c0d400200200261019541c074140024000721600415106580503503c0100d008109881844c000742440e40a11a0b07078989051480000c4000d20700144071604410b0254959540b0b1418501c0c40c490416260111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 389563489 1250 389562239 389562269
    0x12060a03060507200613080c10090308070305070c050606010e0105071e0b10140f040b0409080a090f29070c0b04030b0a02031b0c0c0603010e01090615120b0a 69
    0x40e9601042e094902c9152076005404d408403101085ea803400142c400c580c43c61149a5820000340301070008000c40c0401505a545410070701400004a0361082002ea011420560411640030f80c14480c407540102503082041d1101c42e20785940c4d50701c07903004114905204103048000e020307a00610a88403160f6000d01d10b185440c030440d10b407411844048c0421140608400041001c2d0b1503401c0b00c1205880e0088880210001e50904110054017078131074094010340c0d02c0100c01b4803a140d0b4001c8044090140c0c40d0302e035854401c4070300100000103c3d032100c00810700840c000c1c80202d07802c481111000454840f44003d10b1040751404620b8424004e008051100700d0100203040c988102c094001c5a02802191459589080b40c2000b80e1000726214001408141d842a0780320a0610251802184007000c071140e40c00490049001940281c022103405141c04004000210880c0209000b034660800d03541e007403407030021001c1c08180e203030108021200e840d95050401610341c1c0302d040d00181102d05102d500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 389564739 1250 389563489 389563501
    0x10020a02090c070b061e0910090e0105010e011d1302010504050604170c010804050d1404170106090c02070503030f0c0327010e010807020327120d020d020c0612060a030605 75
    0x25840068100c1c1c00d2030f50400045c0f164a040017501548400b5410885007400b0044200b040b0004018800c42c21a084007001243c0c0c41d4440c46212404040340c0c1c000030701c0c0e50410360700c000b0b0403005034005074400e40c1e08140c80d030504203401c0c6425003100c00d01c7c1400840140a1005a6160090b604095001500482d0014400c030b800c40072000c8106019058466280454004541d00c0c002241c01900ca0341c045941d010381181300300c16007450041002d815a061a440e1600d101c092070038810164001da459920034407031860075204213800140e8900041088620781004a80c4901643c0f0f031907080b01001040ca80950001441196010400b681c040d1100402c80802001c0600b40f40016500140c00350880d41215409403c446011391781075002075040c0f21031141080c0c42c0c1030004c50580d01e415a0400344460a880d001e2803080241e89080241c811200c002d80000e25007454080f4500855104003500c041649440c01214695454000050707800c2d644e100107d411105654001080360f0319000030881 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 389565989 1250 389564739 389564761
    0x80c060403090906050603010302130f051807051e0603070207090903050322080d090f1a0106021203010614090d0c090e0d0203040e0f180a150f051510020a0209 70
    0x80325512030740300c041d0043e8a400c42d80e000c4078030070302441c1e4101c80100700500251510405445094059a10108658512520403001d07038609843c1c000404507900c6084003806400e2009102515050318041c0c00c5086292994003003052003101c107400f84a000001c43c1a4030b209010050280a2099052001c18441c2c54020000c2d40102c4250302806802104202e10255031440a500740d0341010003141098010030540008200c10002115118600002080011600c540790142802088829001585040c1010307081031815000f80300c450ba41000144162900708400c4110302c4119003115484426100120304031182500d009020200403c800282c4c900c05030300425989103011094600803018050160ba0703030b0040b4099a0304001c082c100088004c0b1b44460059440350240c81c01242c121604850b035070425111410946c3c00582084458409503a60700807501c03004501e181c10005850103503081e200443d5079000140c0f0601941c59020a00d5200f0000707051419002030540b1642e00301074103488 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 389567239 1250 389565989 389565991
    0x905071e020606040c1805041e110304050f0d090b0d020c1c1d031002031e0106111c05160c210209090a2310090b06011d0303071e080c06 60
    0x18072860600e22800c5e200c0380b15134800041d05a1a50311072540711706000402c409004070070b82c440d006900307102d8008800c03141801001e0149846a2410343e590915040150034038503a101544110b9100c0e0020306031039030303025658408640c01006c0c0640c91300c4458000070040d118480c0380c803000b4030234140822490040300701010700d00d000a460380a44070390800125464808052404d03641604914100001c801154004590115902030820f8165003141c0ca480b003880c0c0b080e003148000900310750801144c804c081110070880100c2c1e01e0340301090140400010f11302c1c4503258001928503079200a003002c01403880600006082c0d00c001001c1d10360a1040d100c0c4803500d0300c1005900c605240b80c04146032032000304111281540051185941044036080320101d40c00805045090b80310700080090400b15170300c00c00c0120f520920000b1042d0810b240010070402d0001000701c0c4460b048054107905a0b00002202d06081d80540b5a000303189120022104802100f10f010307041c40710010700307940c1c400070208140d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 389568345 1106 389567239 389567251
    0xa120204030b040503041e031e030e0a2d06020d050f0c01151d0c03060f03070b0a05070519050304210212070f1e0905071e0206 56
    0x910500b09003280c0c02e494580010034248000301807900b50381030000b80c5803c0c0c80c2c609800c64483c0302c8042000c0e08450b89038204003102d00101030059602d650074000003884e000e04c0e6a5500c0c1c1c00169900c08114844100940b5610481680c140c0c0d400e017010f82c5c1c07080e4014407021400000a5a880d40400b4201112400c14018160065400d010740c150b0380c00d001500100710741c5040512007414030040030040e0307106d06045c20083d001e20000c080c6d9070710035001c86200070785541076404241000c800c0d81010480313400014a50b001d190300100200141d40c0314004940785990400003944022001d000d005200b0780040000b0045403219292002000030743d031401000e815010390024500000c0000c0c0204990060f0908010412680348490010240c0440103000740704251010302404209001d4065440da03200301060310588601503800c0380805070107007040058003170540690b0340c41c1c0403601 = true := by decide +kernel

theorem cover : BRFrame.Cov 389388489 389568345 := by
  have h0 := BRFrame.cov_init 389388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 389388489 ≤ n) (h2 : n < 389568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
