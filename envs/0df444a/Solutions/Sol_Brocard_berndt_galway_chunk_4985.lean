-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4985
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:22:18.95696+00:00
-- url     : https://prove2.me/submissions/e7c2f4e5-0b16-4244-b5d6-4fccb869b390

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 896402877 ≤ n < 896582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 896404127 1250 896402877 896402887
    0x1060e030f4603030b0609040c03090c0503030a02060112031106040501050601031b0206070c08091809011d10020702030312040f020901150c060e2503050709050c0a110a0204060b 78
    0x80d5544520000790450204403801c1c02d0b1071891000c254505101c01400d03d9900d000c0422142c1d2484180d8900e61302c01403043c8500b021810000b00a020010303011901a03c441d0b0300480c440c0b030080241e13034504c032980c0c1c01800360f686421030b0100314211254040c0c040c010000a403540d000001d0000c58400c2c0d0050001050742c1c100304000404035200d020595060809044000213110f41c081250307600440e80e8500081254403500b4881582e211f01200180d01118460546281610030030350188902561802040f10762410101070440e00707070010081e2260340041d4041c5000304440d6000c0d2000c036001804881c1414290008610322800c04d8038103481e03c03c240081c0ea0110700c0e00140305405018540c905c0c161401d03000c1d001409010641c1e200801c03040d228401c407811190100035200c2d000c0d00303c46110150200b242c40c074008105090105039124050315402280c0850b05020301c42c000c10345020b031545040d40d07118007155403a40c104030f0358419005045d80040075070b0340d5008190280c890210542d50fa0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 896405377 1250 896404127 896404183
    0xa0303170c04120209040309050913050c030102120f07090e100302100f020717010f0203040f1b0b0702060a0e220f0b0f0d1406070903110d0b01060e030f 67
    0x10210041203040e10100c10401031003010f070300d40b02c0380d2001c2d94142c0c1c90092075100c614040c1c42c281c12a41003d500058100200407071401d02101546843c0e0240f01a03500814460003814280d104114000414084510109000e980d400d050300da440b1415180800015441e51909540100b09071040710b4480403011040c41940303000f28844c41c43c080b10f820030b00f800700000d01000c0d4640d0018412416170126002e255074001c1000e4020206024a1135811540e070318040c580702c0c592203060031042d108030501246410803500e00170b1000060792100304805013450340950801000e58098890181008200e00740301d02c3c00d88502c6040c07400300b4140484402280d03c1c551954003101c1019060311412414248807613100c1e191031840c030614641c20f80d016852001e0905000300d140c0c01c002d4485005200b58410041015445990842524410301414018088000c200700e43c220700c0420141224212000412400b8018030680051917009800c0e2600c00340c8801c050303814503041101903000d42903084d0703041d130071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 896406627 1250 896405377 896405417
    0x6090906281e27051f030501020d0b060c060103121710050310110714032106040606030911010e0103150306140108071206020d0f06032001050c0307200a0303 69
    0x142a58585005004801c9024110400c1e58100c003e40c1c101d07034600210b0901c2440804c0240c0c003600b11a1007500722641d0f490074900030350144842801161038480d0811252400c1c20454000f800b036000149603503400c1d1707201c0c072641d040304074000000d00000310984164048982051403007000d0350110b00d16005c0ca031009250034414400342840c1290701d8218281d00c15040803041c5e495440d0401075030040d5000c215030f100e14500c21104140b42d14102140c0b5868000c100309901845020280c17007d00c0525540d803c107a055a07040507000384000d1072104020250b500c5231084403c0c581051501150f0852400080d03005100c403038001386c41c0030743c13181d04040d400b0044103000303401845400c0c000c00340039141424042d00f80e184502c0091a0b540c0001c1c0e9103450b8046a0008411070701c2e03a0804000840d901e181c0300685007030b54900c02c6125891903129411070f40c00fa9041c0c030f03900800c0b01c024502d40741455070b480150b014001c1c40c401e11654843c46138a420f8a034080d80b20040c61003a00ea00c40c1410050f84104a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 896407877 1250 896406627 896406629
    0x1020703020622030c0204090b0f180304120609051e0109020405011d0f070207050a091d0d080a0c110d05040f0f05100806040b030a03050d060506090906281e 69
    0x141c49400001015403511910300d07483d24190305854004007031a000c2c400107016225480f00900602d9101701448248000004840c0c080d90780b00c40301002d00d11503080002d480303025612604070b10310703080c0c8549001300da0143c1120300302520400a40b04400750829595203420650038100c00d091303540707441400440c03c05100e29401b4105240310034244144495030000c000b20010f1621654101080104107858000c0020b00050080100f92841c401e80314207504009110041100c202010300351000c8059180119580500001a6640f003006036501203800f005000d0300c2d0268002c0143d0181c3c60002c017801030008016068507984d89981e101d24046245c107031955160800d80300302c0e8203140200070554031644165508540c40c18194035681e58000014010710301c1c030b40406e405014003002d200401da8444000c02c4120009501006003c0d115010f202240c06607480c10341d00403a103600491401d00d00810700e4030392550400c0a40880c44403140f80b510160150342d001042c2034804007054803401005183c00740c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 896409127 1250 896407877 896407891
    0x3060a0213050616020415090507020c04060e1302101403040803060a080d080f060406080d020f070906030c17120f070c1a0712050903030711190f1a0d0c02010207030206 74
    0x1303007404c080c800385000242e00c00303000a1141d035449807094000d038103440b8454010718200c0c8003000107203848100030751140e00c01140b240c881d40c90007401080185c0c498000310b014002103400341c0c0400d1629800c1c4044449080c0c0c500c401e01011181c104903803140c82e0021807203517215040c0292207080441c14000c0201c0f15822082068026601c3d24205030340c0900300c19400b1145223042811f40d100d4102150003000d5581000855024020000040d00e40000701c070b01c0581c1c031000481c0c80d8a0390322000e50013211840e00004250400b120801c00040040c01c00034807460381c6181c181c43c03461004141c200c0040d0b0120110f01a000d10104d4183c0a010301641690f00800315140000080941c2c03180d44c015038814000010300c200496508500380d1441002903420001014007101d0380c441e054144060040110300800d845501d81c15241c0c064039162115560407280b02045909256080410f02e041490602c505640c036140700b0300c010050b000c00b500549420603166000165108010b040003414114000d01023 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 896410377 1250 896409127 896409139
    0x504170c0a020120122a2109060307080709090615050304051606020a030e0d0b0f0403110d031d0a02210a0206070b010501030c0c02030c040b13051602161d0405030903060a021305 78
    0x7a50b080f0b40461a1445c1f40d811120803080b01012031041c58a90081121054000a0100400203020741191007513004808a488404001c0d43e50030000003941e5860240740030a2250650982210740500b0240d42c00c18450410365003002d60884010f03094405036800400142e002200741414903800082080c001d0b10151020f000325450fa440b00c40c0d400390054070401c1900803080000703040c5440740304c40e04030095450041d43c5140440f0b00c03008000d801c2203c4241c0418503800004030280c80d0010302c82032000d5010704031009600c0810f0305249908110000303201140102c5610303400603501c003801850900d105803071515603541804001400c48000ca8880818030001c07035800000340e07800141500301e15200720380109450340828017013807841019170007550550341801c0034000f0583d00101c8030140d64815600f100e101c01c1402e0540324600226106071401100304c1d101034600100b03600345041e489401801100d02e403200102c0460b14055089940701071450740810440c0d1f0b650380030f101181c0200021151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 896411627 1250 896410377 896410447
    0xf0601052121090901090e070f150e011e12050c09130e0304210521041e080303041407060215010e0406110a030504170c0a02012012 58
    0x920b50740b0008985210148008035440b0740c4036104000488400030740182c240801969030b920044060555400b03014032034041d400700400e44507402618201180c2900d01101c00c81121349a00f65159040b900034581040928121200008440c0300441511070706555400304543d420b12908089400150404030700d15420000c3d01e040c3d0340da112208003020002480000c1175460b60036158654840c0d07501c64540200c6140c0d010401030440310030a40e0650007a02661a02d6000a1462a00c0305480341205c4a00e2401d00c8140505181c0d00d103408000a103100550420f60f4903012035500c1e5802c104c6080b1041140185406d0046205004101c0180700c2d500082c5071420380e140c1c4008036450140287e05c0480700000c00a402c0c4a0395800070703282014011810b9a8511030884024007419080b1002d0701c038010b10300e0070001c2885440d4220b0358410580000360409100c03581c011101e1010130f6400e50540c9101d4440d04580c80828048406400340030348510b940c40c01c400d2b02d00c40c0c4400a80c06000b44030844200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 896412877 1250 896411627 896411689
    0x9031213050d0f0909090f0506100e0c0c031b010f1103070f08060d020d030c120e13020a0e1905130e03030c0c0102040b0301030837030213080f060105 66
    0x1002c84204542e401c01d0780d4554500303c0304075400d18440d0700102c030950401c2201c2c014001d5401c400c400e014000d0741a40c03882e64480c04100e11840941c4183e0000507004000607080201c000098015200d1803019640742021804403c032668520700d000320010303503440030b400d110032600348203180d407110310700310f9150540c50034150180803803071841040001c1c000210700148140c2c0d2482a841d11580e4020609002c400142c10024242400b150b0111102c3c4c00c2004002840f5000f800070070361055000f018004010004071240d00650008003001d400d220203400f40c12034580d2200740402521031760000c4906260315110401407200144d5008a480518020848401c090080100c030f0307104504070807107a60b94100c00d001a00a11450780550f248a6002c400442002360f031a00800302090840d2178450501c01c200442c07014400e40160030f901c0c011040d0040492240241c000d49005a4202901e8144a545404c02403d000c4c00d610b140c40c40ea0004401440321740b0b0f001e50340c418951000400e03c145021520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 896414127 1250 896412877 896412883
    0x80c03120a0302092101020c06070c050a0312090b0405010b04060e060f0103050919051b0316151101060b0a0f0228062903071a0d0506180903121305 65
    0x4007141c820190001440b603241d494003818128488248041084021005480305000b0b400102a16030035000b2500841c4c00304c0d1040307040060080c1c02402500000d0400c0d50b060320342c458003401c41c4001c941c0340c881e0900840d0009507010f1080b0301820002c12000da4000c10001140d0f00394000c9207003aa6000144400c5440386011640318490a080006035034490580c80e40c03505841400d5010a43c6c54100060100000400c80440040000c103030100071600a008058503404414450000011000b4003000203113240c805096115045060003d054201c0300c003210f00751800d40d0000d070304070078001810402d0320307500c000300400a003041d2014001d204100031103940003601d5210041032540200703912a084c00f40f103501200506220561070348040040c41ca5004d03041c455070813114868010241c0000c2d401114040340f400c0300c40703447e080d68900540c001000b0700400c4081c0443ea088500c204d09102200031480c1507602611440000350348070081d840761450644402051490307912000344246c00010800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 896415377 1250 896414127 896414137
    0x2090c0f0d0c0504030b040812010b030601050304030e04150806010f0605040e040311010b100f080c0f0a110118030c170f0a1b05061e0f0c030403110c0613080c0312 72
    0x300310085116200003404440b54040c0c0d4001802d8540340344188820007848d10003d0200d0030001d111412940e0f40d40d40c1988450000b20745040c08500308100040c00640308501103500d65800400c0014100114031280c011000c2a4200c007075250300c0740006110714551040351400400e010300e446803070a4101058042180800f401c010107110030450403000c0b212080d00000c3d00b115020f0031a5514500b40700c2c0c000c1001c0301000c20040820140340c041150f8010200494611021401400d0b03d0005102021980098641c42c54202d42d56541490005814400303008280680241d40d00c0001e00c5541c10000f803004525844a6104078081040351044000c40701520b010b064542400c1040000c46101c0703503c1004c1f01c0c00d00600d180296800c000311060246101018140c2c00300c8403a8071075a0b0781010162040059a00c90081c2c90240300103000240b00300d403041003400c100d000740c40d000d0600c2000300e04590020507003400110310728601070100050802c009094031400304c0081c107000d00c100740045845d04c28 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 896416627 1250 896415377 896415397
    0x7030809010c0e131e05190b0a21020a0603140a090c09050415060605030702100506030c0f0307080105130201030b1012110405132a1209060b061602090c0f 68
    0x406062403c43c4c0c000b90701a410402010303070310360400c204040d407501c014901111a660b02c0c0c0c601003010000c103203052081100035034020f020560828203100c1c04014010b50451a1041c40142805000068542c51032032402040c190310003241d0401c91292711104013034014600c815440c50282c424000c0348080f130710382040b81e00780103002649803564107100d0010b250303010106400c6401c01ca400105c05a00c04c0040d84a408640c3c00d403034440d800079007070303e00f500c500b40c0c0c2555140e0320400c1088058038040c0c40b6410825801412120b1031a584c03400142511400c81d50100640c070482d10f010103558146c004c0d986115012206007141103540c90000d4003243d44234a202c0b0090740e4032019940060356141c1110040c000c01009500c4841c51015901c0140c43c2d00f1103240d00380c54082c00078500499402c0c0040140200c0382d05c50a40b00d44401c0103880092030414010741e145500c499410f400c42d241c000081c200d04000c0070118032086501d0061050080380503200c00076405d810403080c40e40010210940c1d01d0022 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 896417877 1250 896416627 896416639
    0x10804050703031b1a040605070302040b0d020c0102090a0603140c1914160f110a051806030c0a15110615122104030b0f0105152206020307030809010c0e 67
    0x280c403d11103540b01c1c00044d0024402075070041a2102d50303925184207403042c3c0c4203d40600c100e648101d0708500341c5c0aa03200b078884180c02030251010742d90701034000d0100c02000c10001414090305c5800035030000c415520450229a48482d07100020b611b00c8610703588900340310201840c0500701d02c00c0000880c054880b480c108100482d04904503101001102c1080d044006a140d018080c4e040210a10001d21411503860200d6401854039083c860300403030450f500208030440500c10b42020701d5181c00b0040645030b25015a243c0c0a144c0d941e11000c06014048581c1d4120118581c2400030703001c8035039120000c20503031290003044001804080000c0764500240c5485041032104024140b03017072144030304201c0b9000c0e000c2c02e168440c00110040c00c2164041c01140365aa01c848170032420810081c01410381140f08138010b00103040c040d80041c1000020040c0082d00c0c1c08480e01c83c481d14400641108005170000181d45081c5980109003d800100c0c2c04001c00818203c810050b00c8280c5101071140130350 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 896419127 1250 896417877 896417897
    0x4111c090b061c021518030d050f18030303040f020414010806070c020103020c010204150f08041a090307020d0501020309010b0405060907032c01140906240604050d0c080c01080405070303 82
    0x4265510f406a26643c007034092103420365014107894550b08a00c1100e6510707003800d1082a02c2d40340c0080c10340701580141d26246c0c0b800040644648842c0c0c446089580b4503103070300e01144421344003003005505c160f0251050002e014098810802a201c4008414910b444610018001848049090754005240c0e080081c080e113004d10050700a8041c08031401c40030351000c507001500100303003040c0c862807500f150b44040210061540545100754103840282c85c0c0341da1110300c42120f480ae119001d400ca8221310489003000901c0d0b0000da0706500d680000c5134242d4001c0305004006409002d07142500300101c80a1015280c40d20108640c04c0700200382200309074840803c82c509082044018090240310040e400101e00c000003100c1c042c01d0603083c00d00c9580019800a06000c0010032160300940ca02e40c4840c1d20038001c00d05148803050b060a0850340030303004000010340d40c1c1d192103244600c1842024050951031400388d400d410511350351042030602c19040104000610003045d803c043c0c951500300300c0c1d012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 896420377 1250 896419127 896419159
    0x10c1205090d0e0301181208010f030c0e060a0306091b05150d020d0e07080304241d0a120308010504051015050304030e0909030c060c1c1a04111c090b06 67
    0x90244c04003040c4c1c1b04007a4603000c006100980001003406160b503101c11409036030300c09050164030520b200183c428401c0040c24040310082417496504010011b044003095030303da880300002c40e58000c1c01111094a4420900072992504c10954001d00c0200c402a1a160100014040c03d104094030354010a5000600b5121156250b20801000744250100e4002a0302d034006241e5075803180c040d08001d018603245540300d40c8600410f03080303040c419940b00c0c143c400c041c00a00d0078081001c1c503e580d01c54403c140100340c2020707a05010440307500036640c075612545840c09001c2110300207401c002400925500900030746444007650035a02400b860b0541d603950705c1b4182101e1000b08054072540c001400010702c0a900301c004082c1c508c410070041501c0d0b0325121541c1a50b524408c0407251240721612a110809040f10365020205000c10014440000d08480740000d04441d8601402c212079440030070040b010003e02203001030140c400e810304010105250b11071300b00c0791000030405c0344503441c194014086 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 896421627 1250 896420377 896420381
    0x23060406170a092108060415120311120a0e06130b0c030405100e040b093610090506010b0322150e1e190b0c04080a05010c1205090d0e0301 61
    0xb0040c0c00c0900d546a45441c43c03407220036080341c0c00c10b56001645c0c1501180311858940b2a0074401c180b06211102c1c80c62400e003820119620007030303043d0184070009941c0300d1680001d104070600c454034540b41c15641c00560b000900b44803045001140100b5040c4400e030700041c00f240010381610754075091142c0314a4460110b503d544100d800c07a40e0000f20066145c04074541140d54000390035011a4240310b0300b00d0b001c090015203c42114548003100c80700b0518015000141000010044588245250f581170840d840e860710740d0410480f594a0f65603503200c424881e040c040d85000d040404440d92650920114011f00c450036205080c075034011440f820002c001e4500300303026079001c0c0e00406000304d40b24440c2c40c030f0700c4500c0741020241c0201c80c402c0f03a074081100441c3c0382d9200c1d08654a9401c05900c151640a550880103000d805125000c200c00b00d460300f0100104080f141c07180c400400d40707041c0700340010580500c24141d07611280c201014414040f01c04940038000903920300c1c05d03141d004201400680 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 896422877 1250 896421627 896421641
    0x8060c180d05070906050f0916082a0301050a082b0302040305060f040c082e2007050705010806130f020405040e0102090909030f180307030b0123060406170a 69
    0x709100d000d000150200c690b03040401242d5040700c10114101f007100c20311130341c07000403211070744100e0035005102d88840c06030a407a600710103142080c101813000701c0c0380d4092030414209100c100c0400480104128a4822072800141501d0405070181c120303002000245020200c0c46403e10020203404c120305107100e07130f042d80c00850b088012506941085004e0b006100801e540541d05e20f030b00800c010464800c0003c1018510801c1480300420410390700c01c1d46146144c45412084032901d903040340b2400780054940141098070406001e548503841e10700113103800c4055000c581400134880c104403096032880c28240c00401e6240000c9220f0b40c106881f100284619000141d01c60325100000030000e8056000e4041c40006030340c995a1503c0e0f014419035a4010700e041c51000e040208041c031404200c904481d1140b180103001c236641e03141c0340d65980440500c260803c1c00448800c11000540151b0300681e10310514094440300d1401c0d08141c402414036409818081c241ca540b100030070181030306540300c14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 896424127 1250 896422877 896422883
    0x203070605070c0515010b09062206180501021203010b03070345020a120c050d140d0e010504060f0e130209030d0504050d02090415050a1508060c180d 66
    0x105140003440540082203c10782691984902462001c01a1900c00c1842c1a24185000d00342040103840801c04150312042c1c00039441e0f034140854020110342004494060151521100d24081400c100308556008035402681158040c42e1140c110b50084406c407810741d9030300072030700383e5968030074000340c02806440c141d000c24100ca0f11840864800211407411400010380701c100c20b820101039115211710720607070300658010001503040000760201e040d0800c00342c3c8610010740c9401d03900c200082a0000d41c1000f56801d1400f4440740846420501421480c90060700b85060510403020000301640140c0c02040c0611103116810b41880340103001c1030702c001c6030041520580301e4004140b00d0180d085420744074002d210f141c0041d088240940143c40c196030303026001421400003074007008880c2030054025070304c01e00e50143c0c01002607514003469200d421089008283c1c502c07480603e503002030a651128200d0381044091020a001c00f5044500b0704610341c1210840c0b1181d2000910300900641e002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 896425377 1250 896424127 896424131
    0x906080a02040302060304172b11040e0106051612080103020f09070f080a1103160810120b04081209070807050612061519030b041802090402010f090510080a0b0102010213120302030706 81
    0x429482c03e40e101d8109d082d048002404030b240c840c1450307602030003036010f0072503414045001072040038801c1001d0300101e010440050b20030301040c2c50f6425829460748403880002d142900510075401c0c0250240304600301540e510703c45180040008101c021342c28000810000140041441921035070004d1107514054040e660303490800d0080e1680c00e10302069000041014180003803208002c6040300011100ea2803214917100d1556554084020341c010b00071a40c06105001040c0c2c0348060000c030505c47c01c0500018180ca600340b541c6a45496540c0e80501d120710f5080200640e4502d107421481e80041302030398039811460f8000e101d858603000c0e410180700f400c1070040d004641c1c2076058112a480080c10b072002c11500b40f180710b040d02c103041d0340e2002035040021580810015403181e0002001110f035441d00440741340d2100c00003141020712000080018405074280100c80c1094400c018283c20b0034002145001c2400c10007900f11060b80c454054201c48401c41c02d800d02d0b00901c02c4440d01c941c40390003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 896426627 1250 896425377 896425417
    0x5190c060e010218041404050a29090f011a060409050406091b031b0302100518041b0e0904050c13021c0e0607030c0e10020309100906080a0204030206030417 69
    0x141340c41000d0000d20140300d5428004d002204410103660302c0d01540d0840302034206590035845581a071b80d0703258081110800f4210701441170f8414581c907203000c0c104682c0603210148d40c2d908454207603447d80994610026098851200c150f0303a28003201c0803914248030200e05a51a800c11a0007080c6100001d000615140c0e03080c02c0c1c0e5280001e200c01904d204030015100b0400b9002c00313400314009400000c0d0000041243e070702507580120b018000101030351003500a151b200d400428259440300d01e509a42104854150242d0b580148103600d4001007036421a82510307041d08c0d816038a6461000c50b500406441c284850140500e80448a00800e00081094050840c1c6030304070082401c81c490a4047c02010042005a403090241d40c26054155481720307401c1340801d0820400c0a0000d94007819031001300604046074450b4100c64204d2480394481446844c5406d1001d460200c001300b400302d1552040005000503556507040e2508a40c00502d418542210b0b1820040d20340f1903200802d4402c001030740 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 896427877 1250 896426627 896426647
    0x106081203060a0611100b1908060a180f030315031406010911121611010e03030f061804061d1b0324060f0316090c020d05190c060e0102 60
    0x950040406a9124078081d40e101400c4814410074028450725400181c1c141004143c0c6d900030030f0f8018001807030507103e170744450501254504154030011032031f00720000700b1400040030b03c10800c0c281d856880c4108480742903581d00103490704152001f41416519251040d02c42840040180610381c8102d00064280c151451076980303200034400c08003201c1c20054030350203091800b01502c00300c495031282e581c51034079405a10091990700c9003071a07080040401d5403254084090242c4200141500050b5685c2e0170030740440b010301c0c02c0080445000303808c4040075200615040d2513040c1c0c0580c12550002d10441e4110040042c80c485100a200c00e04c01d1184034901454461440103090200300c0490b031041c00c6002030341404541910040e44248180000074141c0c1c145654143d0100070f00a00b0f0f504241c040d01d050010110f5150004501a81d5418810301066010061000d8030541c6080450801d400c150001c5202c0c29025907420400900b040001c0800801e40c1180c0701071100b000c000d64907007d0040e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 896429127 1250 896427877 896427913
    0x1080a0312111e0d27020f0f0d14010c050a020d0f181403011a0a05040902030111130e060303131403010b0a0b07020a0506090109060f0e04060b0702030f0114061002010608 75
    0x794a04425203821034103ca940c03042c0001302d05c0d0004420303030301c440382c0b4aa80030004840d40301d0002c250084007101091489036034820106510901c1a5030080c1c000d10000101c50846120208440520004200d003003044d50300003e441000c1c000500c1c140c242018a02c0007114080e000102c64003044040d05004140c034404102e01d100c61041c2a00200b1030020100340403005840501b04031074000c40740100602081c10b00f5040b0082c1350b400a400401d01c50442940721880760f103c151094846a0b0105c01401190218070032a60048802c0340214180b80300c0c03c619025000c00ca21520a401021121086480c0ca00703400c08014100000d190241d4079a42d921a421030764030044c4102c2c40340c80c24900200e030714504442640c400c1641a900d0460341403d0070704c1514000d201c007001c01c00b80301c240b00703510000b541d41c1e0103460041c04a4143d06500d660151050502c4d03d1075010000ca5680d041000d180300c00100e0f080e40c603500807011074100b04010440320b420313801485903030091103240c0101c00340300c0130a2000c4c1d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 896430377 1250 896429127 896429137
    0x402070519050f030a121503081602010314010b070b071110090f0218070909090c0608070c060c0509100e2b1406070e01020a0503030a02131d0702010501080a0312111e 73
    0x40400c1c40280341458080c03000201f280002003c1ca907040c445ca81d449260000d561401d07510605000034038108c610f80d01c00700003c0907031108100d06030003e2100104451180d1aa0700180607040000a88250700078150321600560b00407080540e80d030040c1c0c000d2140030308039148519009003407440886060ba0000d54000300443c0e5041c0440c018030400034403081d4510800c003c0319041a24009824145681280e0020006d044a8200800781140d0f80100b000c51165804c0300c0140c1c1ca455580b62000418400c24244d00c507801020b1110746010072642d51240c8828001c0401042c10f0303151803000f00300e103004a8840005020386500200c501c2c0020701d030b400080e41400750300703c8c0d1502403001800c080126942e1514240c010325a03001400415868141500135043d43c1c014807800844070354843d02400c1c8101c454030782c815411442002440b104c640c0a11500f40544104c8024003400f40c402c2d1405014040300181c10340f080c40d51042c128a80001c0d400c142d0700c40b209145c840302c0c200742c5141062800e682007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 896431627 1250 896430377 896430407
    0x30c091806120c061b0a020307140a0f0b0d2403050c1302042336090d021509010f0501060207060908073b0a0213050402070519050f030a 60
    0x1202c1e01000300c900005001c4005000003007001e0724002030240d0b010178400550004d03000c144108090400180d03018000f240280c5900c08601e111405100100040f000490340102a003a00e250000d100e00d5181000310740c6015044031001c44c0601300342c04103444848201411a650003800040841008000300d805546004201d49110a0401c0483c14a08a110b00d204080c5c14044401c111440c03d0a80b132002520f07110000e1020994403c00d040044d01840007244940c4460541c01029040010b44c508040e0840701c11401410140074403034020f03680d461980881200b152144000403d0400e00750405e05440d40074105c2486156520b0300082c0d41e4161070b0082001142d451b48020542c41000a01c42c01241c8064216400c0c210040b0040034450082c1e1148000800781c0c0e104000d204a01a440e10740100c0c141d02005039140400218100b0031041d6412040c031039801000400c01003140012070036074002a48400c9084040c403450201c0c40c0c881240030202850002155484945411003860318100071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 896432877 1250 896431627 896431639
    0x13030c09020a0507030f0c0501021306020d0e0604050409060f020a03140702010b03060c0d24090608010506030a060509070807030f0201170702072d030c09111e030c091806 75
    0x500c484000099016841c950300000b103040c012140030900c5001031501141c070380d080c07a0840d00126120107080e81c2c05984105a840030b000310801125504114400c2c02620034503000c02c1504064001a00503c01d920949101d1031300c0d0418401444503d0344403418a100e0001c04550381c090f12400600034101c0000c55202d0b400c14040041c08040c010b00980200c0b4200070f02030300035030f0740d4403402ca4400d40180e00e10400003a651450f14141e20920b0030101c41812403134900c034505a15182514040c1e8019070400c02050b410b040a11000391000034070607441a0340040d003c2940e981d0307500003d02e024080d1388801c40d188140c240000601605000c060b0040c0d000703030b80720802000c0030114007054150603501c0c440180d002d50420003402010411481c24148540c04000b516a028404c4040e06c00711a0800d03141c02c10200b0040103003d0340b80c070660044180b032059440c200b00c510a01c483caa541c086040540200002000075001c142c04030440d0800c80d40245000b01381d0007110004899010200d5005000e1f82c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 896434127 1250 896432877 896432879
    0x4020c070801061d07030207110d05072408010b031f0e100906030807200a030c080f120d1e0603080d1401050d02010c0203012027010525020613030c 65
    0xe1940d1031070340013103000c841e014000781e201c1100850096000c1141900c2214410000454a95a461108280900420060242c242041c22880000440e209628240107100d60280c8000f074000305c80e0340c1112a084400c5450f130351812004222541041802c0c0d402002c0200007080101c030038400c1d6809000d2a4142496194030f960b4000201c074254000a0900b17042804000300149943c140344c013080101d812401031807500d401c0400c84112030b541046428603510a030910042204000c171f00b0328000c101d002040c0b03c00c41040259210f1082d04c1c19088440e8444005801901440c0000490120b2444003005000d580f030611207055042103140140300c908021100101400078414141030b00c400030540f0440003080c2e801034a040304d00d075400301c0e0955281e402c0c2400500080c3c1a1a900412101e10176540d4510840001d4414030200d030300d420311800b50440614180d07485410b84254040d00035144440403c00c892000741c045a80c04020b60203940000c040c105543c4040740c00084911038910038802e0307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 896435377 1250 896434127 896434139
    0x120c0307020d0207051509040915090605060316050d061b0503060325171603050d0807020109030207122609040c0201140c0f0c060705030609010e04021509060904020c07080106 77
    0x10030700f500c9171991243d002e5014484030304903100180034600000b0f000240d807507501d0b80c0742095043c005c4920350409035252089000e2019a004070380c1c1c844401c501a0501400041c41441074a4030f6024441c00364100208000801485038481400302600817107207500c3c0e02e0210401009039108842c0715029020310582060780d8000d14017401080c03021100840d107884e05091108074001d003403000c1014644079030301100900d008203004d24070103940940054080f0b5030f00c0d0400603100040241c60740046a1401c0114008a9400b1501c08241c030799680000f01400352906001815a03828412400d000950002d20400b0b000c02100828030f111040d9000d11110149102c103900322142c42102c4810081c0c2500050b51160700c1200a00c1540d00401100e4200f0700040c400da450140100c800001044000080c4649450100302c42c50050400007501c844d2881c01d0390110f100c0300c2c215180042051b401182c00015980e0740010b68000c0800a0400c40d100c0e0302009c0416034910241c403c181c0c05510b00300021880e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 896436627 1250 896435377 896435383
    0x5040c140316051203071b0e0603060907050d0807022101050114150714030307110610180b03120a032009010c1113050109021908060a090908120c0307020d02 69
    0x30204802c40b0380c6075481d19250601c00d1001800718500c1881c00200b003410000f42544d48004280482e21035080055824410251050340025188030701c01d90000d070410045070b90018044043e250141c545101c80840c0d45070001c0b041c01780d80e00080d8081c60401c001000c5c0400418600080d01a10000f0320490f680c6039849100ca1910350503c50308044a140b205600031440d20080801d10305c0340c9451b80e10321940b0025141190015075500d030003d41c3c0141801d008010030810f20b50807010b00b041000c0114684400b606e040c1c0283d4103041c2c2c1041e01c1310783d010086d9905104030092807600c080a55a80c40e1100c0000b00104444590135143c2140d020107170a4202c0c01805944a200d03068507441c6959001351221100036015020300c2e5801580141d1140d509070160042e18002e00482d13001580b0381801c07046401e84600740100300420015842c0401c40fa0383e40e111140340c1150204080080d00b27104c3d500307100d170350341c13241120000e6110300110070700010106240046214400503800d81d42c2c803035210b882c00c03a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 896437877 1250 896436627 896436643
    0x8091005010602121b010608060912040501200a0804270c080601050705010e0a120206060117010b16020d050303060102160b1215041409011d0604060903020f0105040c1403 75
    0x1005074082ca00402810142c80000c0ca0400007003107145c0942d40c081002c031401c0d00c006400454183c0c08c16000d105042200f00700c20800351280c0754010742050304020000301510f04005c012103200b0491940090491307028005210310940003e0500d5640d619003001d007450094002e4200d03d0f4803020110040301c0c0e085440785a0040c50980c0d100c6800c1d0329807500441d4150444242601c0655030b0307501050741400100071103107803107202c0c9203404003420540102034180800180414140400514940810803034008038074103560b621202903440340c9140110040d13407a00444002c0d001f41c3c5070002d54040c0803000003d103110f01d50036400c0b02d480c501135a0760a14440ca60744940e400d2241c061003819515406911a107a01031100d64245144240803000241510000315040031080c032001c0504c10961400e0003540001002207242d14a45020380160580c1c0d80002800030701000d958003c802d04052003804544a2000c180000380910b04042c00c10068580292094044400c03540318520518180400e03008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 896439127 1250 896437877 896437889
    0x2a040b060406081801090506041403031501270b0c1c0512061f080f090a05070306180c090f14040503030601081015050309011a03120a031503030809100501 68
    0x81d0400e4546201615481d50103050a8480081d82880e81e01d020300034415a1041c83c0104024000b50a0030708241050a910f650720140390f81080041200e0311002191000d0303002c0007841c11030001c118221810084100000404524501402c00090320940e0b0401400d039400060042d078403400380030214030b4a0100c1451078200418024000303e6181c9440400c00d540c080c5003d0022040c0760103402d0101c481540c5200c0c2c00000c201d1860505c1200c81a910800e075100c0d80e0000100031030b1100b902c0f91961607081d0b101c0101030700d4440d420014041e00340b400e480178480d4400300015000703843c1c0c03140c00c015000c44000600424607141042811042d11008130f03000c0c5801001540c6191561001114034481c000c211092855100400142551500445406020103640c441d42c803410b2000358103083d1000c68001d510340d0244000c4050721540c0104a00c00307404048a5031590382d29552105502a00d88040308000b4081085000014150003480c40d0f4413803c086030598005035105800c1da41100ca00380100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 896440377 1250 896439127 896439139
    0xb0a1e080f070806040b06040902030703050702010b240903010c050a0e041e0b030c19051e150d0e010204060302040810110d02090429010f0c21030207052a040b 70
    0x410b920a0140054a40041000d04003283c0256141c010a03420b81c05680240c0e08107600000300581c150b41441079a400068610007440505640d400203400c0e50905805c00b0040221019403217a10910701d011980e1a91026000340f00000c000d060152050704541c0c0504045102c0315800086468140f14207201030a02441c0e00d09084840c03190703440102101025189c151084044489555540c4e0f10300c8248000c11384128504c56081c041801a40c4c191034040e44403941d81c2903d0940e140d41c40c01c0c010045802480d148070b0f03c82c1c0c030b0505c072140640002058070715254030008010507002d074141c00501c1602c04001c00c41c1d030011101d84c00c41080380c00c24000c50441e10300c288090290402c254005003072001d0024004174111800e02c02007054054440005907034180761415403c410358210448819555040c2020100d000c8251611024200c200455880392505007080104540c0260305543da4035400000320303007454000500100c127107a401e404c00c2189002c0380d4240d81e420300d444e0190400c840b001801c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 896441627 1250 896440377 896440381
    0x6051c0b010f030b18180f060606030c0304020d080304051507051303020103180209090d02121602010f0c06020d05090c0a050a030f0206190801050103110403050c090c040b0a1e080f 79
    0x220700800100113500d521240d541c03080000d03440211308060068296581c03122105407100b02640c60401c564003015031940200b4200011503031a0825a41c0c0034001c2032502c1e41c0e81d610f070303c0017405e5042812001410721102109200030b0040014a01c65001003a403c4808a602c5414054441e8010a00030803251060000709100652090300116520b401c0301007a115280000c0d40007946030901141c038a406e95006000f40180158100401202c270311025038402c0c0f800348804c8108460021045010b414400c00d0420110580e01c00c048800006802030b4046440300c0c1d081c80d2880c05014182d64550b1607119000810105240c41801c01c801c540006104181d41ca24556810400c001c460340c00740e074060003c0c8107000c4e0500c40340c07065180a8006079100002903041000140484500c00c0e502c0e003501205000a00c00a000041d80c81031044003220308000c140e544101d044954841d941202e400e2010104070807003115007040008007520a07115a2006040c1c03506402c840d8130104407033f5030000008440c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 896442877 1250 896441627 896441657
    0x9061e12010e03070609060b040204180504171c0b010f090e09010213060207031502040e18120a03090302060105090c09060a05090418060b0a081f0603060606051c0b01 73
    0x8500440203a22001084121100d00a103007150030400040c0d80ca0303a00c0390010010402136114460000b0402c4404504050504048060740a104405030b0100b655400c089014018161840e2064030a8405819501d01902044803c98050655100a03090420480400395030168601c10701c8820265500c0d0907503407524040807c26071000d00325100c00c0d582001050101301d09062750307001a00c00c2c0e8004090300e601d9850654ac402070751100a40306640305020078000800d12917403807600501d681603c00c0717003041c040c0080d904100b800d12230061320080000d041c243d083e8058206020040c020780030340e15960380e41c1c0d0500090800032100c000300500200011803075486e1040240403104082c1c5012802c0201d440003007022144161119a01d80003814a1a02001130f203001e10b904c110426503101103058a0101325641d1520001114030710003084495900c050215940542c00540d00914180030060f61500c0141003588034140721500d054400d00c05038400c00a81c0a1b0b035003904010303901e00d940d10010b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 896444127 1250 896442877 896442889
    0xb160206030c212509032a0f03150902030309040614040e0a020f010c0f0b0705120a1a130e0604060c030506011701140406150f23070b0402030c030a05010b09061e 71
    0x11100e1092082c01880030001c500290b528034010080d0203501051002c0704400187c810b4070300e0b44072032410381071504c0038000100802100345101c1800100403548064620004e0300754040c02c019982c20a107480d8000440e0b0080c0d404400c0b16130020f55007005030b181e040c8241502c940700350901a40010032009002080d5220315102c41c0554001c0e03074144541d00d400e80e1818444075007501c5070340c00294041400c082c00d200d4029542c1d048034034414204402c82080b40c00c022204503140640d4866a604000816110380c03a800440b503055a4106494240c03402e4a80500102403420404000030718150002c5d50039401141c000d60160b00104001c0c90340da00e0440d03104d100048002e601c64101b07840c1d060010b626003011010703000c1035180d5200daa91080b00c86400400f100300307000100c0c4884a500701e01e486552541c10880d0040e40d0400810b800550304d90010925008200b01c1c2c1680601c60f442c10034051110640c001040080d00301c50075142c0d0b0302d403030703080007061490340c0101007940c00200d90540c5245444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 896445377 1250 896444127 896444191
    0x2f090406200a0c1106070206030702060406051e0f0601090807060302071b18020331170a05041e080d080f1b03130201020703061d06011d010b160206030c21 68
    0x6104501e07064065008c00c07a00d4000355080d00140c1d00020902c8204038807030084a41c403482c2c4010040749501e00484200481e42c01400c0303a000041d5030710101c0c526074840e0360f48bd00980f292504540c0030320b42d1749a00070025800400113803424040c1c00c15000491341409031a00481700410721807007056000c0310007070000b540098000c0b0344660f85089120400000f40a40c1020a25200004400406941440018601400d241c2d6080d00010044001e003560490252001d80e40d1402c04031406e106240881606086642c204070b88900c1251001c2d0324095100704070034070400c0928001180380d1141400d20b000548202000c0b40c9841c070510005207424556410800c40d240144111481d25950b078075100f08551084026404c54892101d5401000b54100403040c010001c2c150b80c1410305040720007803810001e0600030784114210000c1c0550070105401c410008283d00181113903035a0810741c180503895802100381170058211039030751115012030090001c0c4105980003000c1a092041100580d401000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 896446627 1250 896445377 896445379
    0xf0f170109150903030c080601050a1b17090a141531210b04020f180f0403140a0801050111211b0601032f090406200a0c11 54
    0x6520292004181ca50804020b4202600790014007010b541c02c0c001c066840f829080c0f42803007100c0c3c051010781c2c1d0f480021942000340301c1c81c1c6050380c54141d43d22480d16810364a00602000110031402c0841c006ea1002400b600c40100c8500e02883c0c2d41e0040c07150400c40f4040581d612085100d594a120704000006011984003200c0a0500c02134125100c5410300a0804002d0f03400400c060900c60b002400c20081c51807070080e481035517207032040c1c1e481540c0745800900c002d000b2051241c0504c0300340c4620011400030b080051281c00300e0301e00544280400ca400322400e03000103d01c0402c4195840c0500104d440030103c40d038035000560700702001954071043c801e22001c03040c80752184000442000d0f6039020882c056040066a5509403040084005d03506501e030b030b5411b03403c100c0c01000014207a441202100c0b6244080b44400303280781e40b5001428400400741c039001801901000208022170b40041d0040b107501907011220302d00c1d40c04118003030252844070b0000c03900756802170001c03a4408668658020f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 896447877 1250 896446627 896446631
    0xf0807031209051e1c02060f0a0c02091302010915051b030c0a1505010b0408061b1e030406050912071704090c0503040c120807020603150a060203040f0f0f1701 70
    0x140c1c0b44040f07080344602e412200003100130501c01e49035601d001c03440c56040b9503505140141c02061500000c0c4903100d040100c404910f0300181006141e4002c05417207003001d070000e01a41d4030740703056100c42c04075900100c4220300040e5404c5021942c1d1240c2a1117000354241e5964541c24144403600b0190a88d080402c0904140320900070940b034000104030b18849a44151a440207400524900307500f990010307081030301041024001802550780000d54a54441c140c812036540729440c600c63301c9000c3c400d107160f00c3c1030448031b5441240103610110065009912500c010081d0365502c0d81c6c00c68941c004c5241d8640005000c2003814042080b6000d40741407000740c1c41c2d40c10300c0d090355860b40c2d000720380d00c400c0c400d03020403400b0080000303200442181344000c0c10600d664000030149a41e580d5031600c10400000d1040e40c012020454031140c9a481c114500c00140c5090030a98684002954a400501c100d10f001010000081480100c8146c02c0003121410030414664500341808000712048603d040b001c070359 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 896449127 1250 896447877 896447879
    0x504031206060e1f0215040c120b0601020d2c01050c151806070206010b180a0308091c020f0108180318011202161e02030a05010c090f0807031209 64
    0x550380d44a040c000300742c2510740981040e441018402c18000c0940d900381d10f62611040b00e210b054011450b041c5850303031aa10003c5a6a0ba49007100d07001c07040e030300300f02e440d81d0304926400700700400c10070098000c1800760221600040b540d00121503c640034a68074040403e40c084140b0889012380710030300090014100642004085241c2078a811140d615102c00503607110144a00e1b048071214002c60b0251040280c41c00d072504080103552000d061080d05050300000401d1813900040c05102e04070706600030604420300d0760b0703818507645941026021512506100003958111740c1000e00400315294040c04110550043c44010340d0001001858403480042a204115403800e091008205ca804ca81c003e0381808060040010715110050442d02c0341d15104001464080b001000013610866000e01240d058054520182c0e0180b05140300081d014400c100c0c0340030401c40103410208864649641d0840c1c1f01d50b540d0281c441e1804207109114090700024024004500e90808510b40c00900d401c10254003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 896450377 1250 896449127 896449157
    0x121505090c0603090a020a0501110303011211130b0a0510020c0405060406031a160518120313180b060301030f0605130c09090512031009090f060912090506070b010603050403 76
    0x364401c462840c4c0c01c0d0002014281107140040c00c1a020348028a0881c0318210242e0740140d8920060050710a02c0856112030001c0241031080b42c0c8000d03e001d001c006030f42401603458005841c0f41105ca80c415010640041020304000a072415519004d5005100500003042400001c09029140780d80041e00c031200400802c83c0710310541c400020700040703500d161600000b1144014055481501044810001181c0800c8100281582c140003107604140c0031481c0b0f1710700c5156200f000340c65429081140e00006d291000400c030b0301a01020205d042c0085981c0c2000c015940c802400024604602e206140010a5081d880b80d503021040c9481c2590080751600c0d500410007095001408107034403840b11200b008402d2010200d030b1441041107504609100700714142442c002e02422180c0c581d110a8039040c0700168402c91405034000104110000c014101007010fa40351040440214601220000303a03402d1800071240c0c1941c0100031a00240d09000d0120007078a4042d00503000c00410109007800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 896451627 1250 896450377 896450389
    0x90d0c0303022802012a1e02150403050312090304030f0807030f08040b0a020c12030406150803040308070609060e010519060e0f070806060c0a05010c0306121505090c 73
    0x6140290010091100c0c0c03e42c410391401c20004203140d00c0d402a6041d1801030343c002c01c4074405142c0400528460202c8103044840b5a180c442010b00030340c581c006854451101500a07040103402940c0034201a04130114018680c45184002840359000300075101d80d008801c807415802140b18820f80e441e080e540e0b1900c02a48500308010350b82d441d40003554402b0160440321000f010f00240c200090342d071402b51908201010000c01000209400003030200052000b8481c00c90325801e0700c000310740c880c03e10341070a9009004282003d0300182080c100450550000000d071800c0701c4c1d0200c482341ca8640b0686d03582010305561706044411641f81d0b1060103500000f8051580320b101801c103001d207003c80c10613003030040d03861540c4582d04842e0560b0a200f4484115a2010340c404403034144606107031a80f2001c140203105d04082ca01d99809047c00313a41c104035064206200840469070180b11894071011803c070381081000000301001c11001d120889110640c114a80c00015401503440e00362a01d008100303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 896452877 1250 896451627 896451629
    0xf0c0f0302060604060e04051213030b0f04050124090f020906071407051008060f011b0b04030f030e100c051312060501090b09182d060108010c14090d0c 67
    0x1da00290100a80b42c2800e20494004051038240c100c1d56041c80e0f03e545846000220344501550000190358580301c0780780c04c0b034200542e841159401c0c1c51a00320b08520007450295801c0f5025401c05885880107402100c01d102001e00428030409414540202207005044805803023003100d0302800081c6480e0390305c1028080b4280100520000c0c2c0340c190224600700b90181c0c04c560301c00c1e06c8072a118a4110b034045031556112009407900c0c40d00240300001601c100c0301450315601c0c13045050828404002d180022903004a02c603490319698080d1404e81030342030f03802d038041c2001c10780c4c40034000503004801508541d100ca02c050404600d0802400301c8035000c200c2a800a50041c606001103404100507403003010b00400300080c04100e0080002d0002e0402000075190aa4030482050302440000c0705200310040024040341d2001940a9a03041c6e54050f000b8140401c03290203198000101e50b030046c002d103900c0f84003d564002200e804140c41c3c000981088900a4103c0840c540120004860703081c448 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 896454127 1250 896452877 896452883
    0xf1201171c210f0e100608190816080a02010e0106060503040b07091806030c0e1b03250c110108010b0418020904060608090d05190509011704231605010f0c0f 69
    0x4102850440700845c80c000840880d041c40750726000c420070240402290f0000f030904100c4811440d0516410310b45900c0c007070542107491034100700160400b08440c3c500100a0004c003a0000d01003000c000032071600321245ca1048801003601000000c0000e000321110650100150030074900003522030f0307031407428541e840c60b43c945681c0c0d80c0c8805000b881408800c5400a00c29108181d0391860482c0c40380d0703641c1c2d1810300003003080d01010020801200c002d401e1103031005081c0004071544034054030001c000e00d07252070054030800341074a407203141544a2907803d41039440d80743c8058501803800c2c7e80c0c20460b000c5100d5500d403ca13424014440165100d0140c03030024680d81d99010968107210304840c1c1801c0a40078000c052010402c4920004521501004420300d0541045501c0d00c032514010b842070800c420a23940311460000400080003024658190410500c0700d00c0705425200e007020554590369440740100b400d404000400c060b40c13040c481c2084403e014075040c0895002580c91504000342d0030700032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 896455377 1250 896454127 896454131
    0x2110090201171611071a1c09060212070f0e09060a12050d02160303020c0103020d020702060c070303110c09040f02010c020612010905100e130303020f1201171c210f 72
    0x150900d50f500c0134581c61006100b1029001c1d141c5006031074500c100040c140001404008074120202c042d04904203520000d0304801409941e00c90328002d8000d40c050903090180e400c0000200d20714505caa81c00e00d07804c500c641c4400d10120f40050802c4842c2c0740041c07540f5401a5501c0001c545000c5004141180038451702c010003840171b0807a03019007001c030361700c0c811560b520750a8010004603a00247c3c10001240030b08005030389124840c0c008020b0705c0351a0000e50000c00014003401c20502c0020f001003224001c0c1c1d200320301500c244c4049030b11540001c80d80b685c440b0200d00841c010504000482c0d2403544141000e40740d0000550200b06c461300304201155000c0d046030010841d501d402d000e555840507500c8109401541801c0035001e09510217424038040e14034211241e82018041d604903040402090605a01c03503840c6101820018003d007d400111511168590303100b49001507112603405850702101c035225443c1d10211561403860004010020810500704414503580c814285484400200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 896456627 1250 896455377 896455411
    0xe031b06040b1308220b0a1205280b0303090405180c0306070c030302130f0807090f110a0f050f04031406060102060415020d060503011802211009020117 67
    0x509032264003e0245660302000740c2400c0008006404864001d14181001204900c548803000030641154020360203241c0001483c44d0219008110000600d6203480240029030b2401c1c0da0542c2d401000f400700b030060300d00c901503210204543e04103808003d006403c490400c018900000d0075900c00b40c821b030388085840f03100e41c180c44031f00b4041145922410b0340103002c00d0611400040685a040c0b40150400d64082541d55911070b12203102001001d200404403941c03034568100750348409892181e2040146020750083e845003440c013030303032551750315200700c00d400c0c091000000e079041a04200b01c1002c00504201c20070180311100c01400186006002c2800f0078000d0030035843c944503001d0051410341d8864010440012200e08500a80680100c8056181d080c0490800041c1035250421545942404034a441204524615a03804c9000b11403502c00d42100b8000c2c650a4041c1203008809600990060b418141c01908001001d61061500c01c242001c0c0d18001c000020007a54020361011021b10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 896457877 1250 896456627 896456633
    0xb19030b010806010b0901110f120408010f060510050c1501090605100203090922210e010f0804030c1a04060b1201020901021903090b0f040618030201020606040e031b0604 75
    0x180d4090810300d40100425410b10050642c2070040412050410005952505540205010100d060380b91b000032241d0310034411408900580081c0541740d86980381000c0380b007407001c1b180142412500c0107818142000403040701212194000c2a8541062050003001807100003c6a0018020300348950002803650416003040b0024000c240c16400310740c001c0c080c400e219540c1200d40c9410104500e0003110548400d00041d450044501c1c0251402c1d103401e03500c482c801c840c680e04100540c80340e40c400740b8603200b00b001036031030042d02c04209001810590002c2d00080c00b840030300c0841350080c0302c422048842ca0700140001c02085400300c030a25100c3d00c01e8032083c10490762a90019807160002e41c01c0c0b01014000175911002003004042c060303484c071082814103005064a2014200102c54240d40740c811840e2217540303911034810500000c0f104000c40b20842c1c100503007030b0140c0b98141d01910b0a0780314078040101a0107034010b805068001041103902181c02010305a00031003100010f0502031400d81 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 896459127 1250 896457877 896457893
    0x11071403060f010e13060615020309150406020718091203020d0b01050c03120a020c0105041223030a020a030b031609060e0603060609042925020d0309060b1903 70
    0x1e4100e041c4200c8002c0184041c003403040c0b8250744400c0300340700d448012205040920140203d42c1c021408440381a02c11402540d0204c001c0c1001070007174428211942100c00007410f07500c1240304150044c0c000c26424000302d848140242201800003001103200503083c1c903005407885040c1068808254005103002001c5010701509000301c80908001341440c05514107940c036449030641001c8800c02810024108001c0342c2d040e103449000c003030007c000529041c0b429400a0514204040104c1c005ca450403000880c03225900455800c0e0030942821a156068290080d401c5480c06006240d141c510f603468031b850070440d464010016000c1080d1451801d09014101d500981040b135108121000300304254800142c0c064001c1425103015105030394900307041520420000600d0240780c2c3c1003400d80d19190301c01400700c1c01845c000290030003040a6880703d25840040303d50803000350f04034442c2c070b62003035000b54085d100890241d20040361240c3c1c2e030342c0003802c0c01c21044030916241125407001e02c2400700c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 896460377 1250 896459127 896459131
    0x120a030c020c030c01050a140304082d070f140a060f1d0c0d1505010306020d05060603090601030b10030b0c0c0f16050402031e0a0c0e01020106140603071107140306 72
    0x2500182c00000240c0000c03036100c48101040505001000840720380c058803400282a20001095010b9101d0902d8900801980c0c00100703c1c0c0090205140c00700a40547c021040b4201100e4a4415181000958a030a088140c506040d035012808485401c0700c00000c0c071541100310702c00c920000f58078003030b00025001c455100c4001c00c4010130780c812001d0b600381e0008891540180c00c0b100038012081b913192100c00700241e040400c0b0311900b080000820010f01d900908a4001510014803080d500e02090040742d000c2100e03106d8855001c04010004100024292074000c6040d003000349e101c0e0744076100c0c2d031500d00d016900c40c09806000a42c141600409000220040c45060080c0ca801071604841010303420346401554403440c0d0000101c2c44c2d440142e0340310900c80101b900c180303816207800d420040007010044807040c041001c242003030210707620610913907080d00d040c104108046070840c07040c0700c02c0d5007006103194140300400201c80c98910040116400070300f54a0a071601603d160802d043c144040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 896461627 1250 896460377 896460401
    0x130b1824010f030f511107060b060f27011806030b130903050d0605040606021203090a0f1410020901050f07030201110307120b03030c0c12010e120a03 66
    0x3842400007542a50802020300e41082c9003c120451700e0500b4050110082c0182220030008500c4420710385214154105040560310800304100d0f0005c0080c0a0b144085101d80e60403c00f0000750300040e400e49d0242044041c0684158109900b00c100b10117079a20299007121008900b4060032503003c085d48003100545000c0c40d000138608919061344400c0b0340c4034040c4c04141603c48908010320f072222828803610134001007040c85285640e042c05803059101c25a42e004843c00d054020503603003409c1c001c803011181c0700d83c02480c041940119005d0b0340c0e00b018050038524001c640c140f00c08112000b9041d2030302e60040300e200200f01c2032000c90a14110344404a024001d00610025205a03023102c01e550190344404c001c1c540e206490301d0200c2c010a00c0c0001c00031078001c0070007484446a0b1028600102038440b0301c0800c0b2140810702090740e20700a410901003ea13110b445070384414101b40c01c100304407010510001c1944d80380b0b07004050801c80380d2807078000b0819000c20510441036160180b030038140c0ca = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 896462877 1250 896461627 896461649
    0x1020c06180a0311030708041403011a01080712090c09050609070f0921050d050c0c010311030121140105190506010f0f020c0409080c060708130b182401 67
    0x2280c1e0034103890344a1140301030144488040d1805241c5010f004560060740c0c007081c040c0d43c2d0354443d00b10341140121036226078000c1d880e1040c2c0c10550403101d00070384c407076010503129040c41ea941c8100448402081010340c5002c0e0303071030f0200d07407001418102c96180900040f20b0081070b2403034120180308608400a20010800c03604602d208030b1103401ca000f0200340c0f40044400800d40000407180310060401a0004095104402000c08500d0348480038160702c40c00780c41900c1d030840e0b00b0f200450980301d2040d08415112000c0004120342070502a9040703007840c0c120311070701e100c2c4d055403510f00c02201c00226441099450750100301c203500c0c0d00340080404420f00c00c1e041001b03081c4200002e00461000c1840c0c002c1c41111b02e014003545008118158541034024014802808140307010000360704440ca20345494030460020a007918010240d0341d114948428047c00c861050781c403400b04002003d02071403820f81050400802da00700c04d104054680c02002410340421041007156900b404050f80304142c084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 896464127 1250 896462877 896462911
    0xb0601170c0409050711030a020f060c040305102c0c040605061c09020f1011060f3c01090504170f0f0c2e0c02070501141e0c01020c06 59
    0x118805082e94241c0d204188005103d56900c2c20503194107004420705c01c507074030022468450140e4002814410380f5003400990b00b041d03c4111106102c0c0c050346c0002800d40d000418045002d11040c2d010019200d040c4a840c0d03110491042c80050045441000000c250800c84403200340341410301544c00182420380c0d030310346443c0c1c00c01e002120b810344508507200c02c0f5844000000030f40d42c40e0740b0081c0704070000400c03e01007169a11030140c00d50301144079100681c041d003400149505104014984107002d04050300d00001d402644405180e500007141441083c0c410026120420046042a02070550000009070ba8103007130a1254410701c01281402003c1d00c10003200c4411702410341900c0b4040c6004103420303119411034503c1402d1040e52a0306c6006001a1480c04030001000040d540380003c01c1041004160310780081243c0741c0d112030003414081010075142c1031490700300030002d041190403600210040d00c010248058241d0001200400b00da40100b20b824403810144041600403a4001598140c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 896465377 1250 896464127 896464141
    0x8061302010c110a0f09020a0e0d020f060f1c0f0b220b0406030f0305120106090f0e0c0c06010303050a0f08100b07050a08070b01152607020304050d0b060117 69
    0x99462000b0080090390074141c05902515180700001c003030030701e10307031400c010036200e03402d04d0020b41019040d41c0003c1c1a41c0800151400c0c6054441c031020380181c0401e00c1b060040041c000c080c1e100d07240031501036408000c0c4c0c4104562009141c0a8a100800f0110700040960a60800e980c00409868420101d031005004201c12070005844070007180280440c07c0500640050000c004c0e651010700040042c078410820140c4c0b010003070806400c41d40c05001e0f282d880359411605c1c2030150048209240880b035062100d60800d240d4190301400300c3c10103501c0c01e5855181d25040c440203030700c21000300300c0105114000030380144107040c00c2010703131a003404980f070603200d03402e5600403610908480a200140303002c28403500780038000b100f03900041c80c250f90380b200c0d2614607600707002442a01280e11090903000401407051018148040c114001c0311141c1c2c4032180052030b00c1c80058086019440300b0080042c1e40c1d00c6043c0c0004805c0e0260300c440f07034203140a00002d0800061242501940750740364041080d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 896466627 1250 896465377 896465387
    0x117060703050a0f0504050601032907140c1902130212011806080610050307090b030a140c0a170d0f09140414091b040b060405091902070c0806130201 66
    0x4020401d2a010865403039014000c0010304c180300d0303c58803050a0404000030f228000039000c0c1201e20442c2d40c80070640c0e00703000c55541409910030b108500d8180f030300819542c5208512040059148505591a12000880103032421410004605004d862084c1c031809618211095040340304c0e58100070352801d90b0701400c06900603014050391520402c040c0816074000c0c0b0580c00000640524006c9840509105940c1078480f103152007814441c2c4141400844c0041240c021002684009401440104400d40e20302d1100b10309032045884500c02e0007070001e000e83c0c0c1c00c03503014000c28085e00c1240600b00294201170511b078980103010b043c080703120b440103003c9510031030610403a03032001c1244d003010300200000780c05403400c98007240c9000e82c5c9405000000d24082403441740f6403491004608030701d41384002e002c2500c82d4458201d074000001c0c003080041d400c003201840d5119035100d203004011541c2214074002c9802c1507405640154102034280030a6504008c100d030010102031011203140750310760000301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 896467877 1250 896466627 896466631
    0x618070e0102010e061308220b13140d020d2105070b100f0303050703120f140a090b0105100924020712080a050f191d191a1c060608011706 61
    0x200015000840c0350350442c20070715040d032040c00c0c1c42181c441250380f002c2c003249e1904509419550065642d80028400020300c0b03280d070040c5800350190b04035032442d4013000032040b0030320400d03945030183d1002c4141c18404540001c54100c00c03500c1d4252a540c160401e046c040000912a4441040c001414007485581181038821a030385843d100d6912840ca180c00c584240e400c07080ca0481a040008060890b1101d4210b551002c00d070401e8141c243e80c90500d01402e9407940388000d440f00c4150001401380e030a19000f510010813803401c00d2032a030740c2d441d000da103502240c3d000200300807969100703003404a40d0305001000040c017500c2800c2000181c107845544080c882c415540060007000100c1c012282c40e008140c40c0d1402d4014540100e004c0366150290200c030310702c0a6200d4a02440180b0081c0746825404040b0381241035442111040c01c1c90042000d08080d0040d902000c0c0e401c1c0300b003d81000c6460301080c0092420a40407078400c0c60000301824520060300145009101e9400103240b41c0400690a5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 896469127 1250 896467877 896467883
    0xc0b100f0e1e070207090507020d30020a0341160302340605010506130e27010f06050402190e0111011109130e06010303080618070e0102010e0613 64
    0x442c503103d0b2001070b40b6004985d0300800d2403078149802c2201064010400301425803060310364690030550340100002d014070141d14509002002c9200c1014005194003030b209007409410700250350070381440c241a00400c9010a24484000d440c030009514805140e1310600c2400d038191840306041c84000c80c0300c1101074003030103020141d000c100400311890b1200030300c7c1c400c2c0000d003807088405c4480c40c54203100100c07818240c440d24102000000e540c10314204a0303030340b2002545140001030400c0070100c00d443d130103840300c881140b107140f000e42103002125041c4007842c00c1400000302000702034030304815144035502544c400ca105105c010410483c400b500c2804d00794034500031a0002c03600b001a138842c41018581804c9619000c030380c1404c86110750003400110022175020002400c1001124103071003a9450040e22a04032400400c00a401890700c04c0e0022030060210900c01e12800315480e2090040701c1c5400010345117140100e03030756020310036039560540c031002411140c41d103041c5217031422100d02002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 896470377 1250 896469127 896469181
    0x40b01020a15060308040e04020a06090f050103020c0f0f24060f040b01020109080d02070204050c0f0a081506070605061908070621020703020d110601030b060d030c0b100f0e 76
    0x101411142070b440f0801969012920340e48441e02d03480c240c548130300100c50407800383d440c80c2004142680905110001c841c181c030134160810f81000011006034003c00aa80d10601c41c403035604044140034441c2914140a21004103c11080c503010b4481904404035515014003400041c00115101d80c0449164200159030100d042080365004074014900e003100608148004140c401c5500580d030018900300d40200d50900c52600c80290b0034080740300d85149107001040401c54501402e010380c4549622842c0305d902c2051b401c0c0c03424046070080e44805c100302d8000e540c031000c00500d40780ca20441004012481c01c042629070910440b26503c0c4014010311b000d0081944110341100380d01c2d0380187c40c00040704c4066454034002d10b030207951100307400040c2000c05c003a2a0003141100000440d9070407203800240b0701f01103440e103070140040b41041340d2058013007081f80545400440d031030900503405444100c1100a450340383c20300000c3c034081590031010383d401d24001400b03080c1e0f0100e61000800c14039071101c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 896471627 1250 896470377 896470403
    0x2340b030613020f07020a170f0606030a06050709030c0e010303032d02032205010207021008070c0605040f02040905280b010506090d020a080708010c0516030c03020f0f010218040b01020a 82
    0x404c0c090081c904001d52025906c1804200b145142d45003071400511082290080d40c4440c00640d01d0f40d00c212030403605544015896404603585400454100358542411081140c503a03d8600d40070391030340c00449610381d0301c20041042590501c10418501c29046058001c20740d1201c903100226900e031203100c180ca4021002c40c005001c00c9811908900d18030504181c4418907181c00e40c00b0b500402c000340d215100c00105580303094064840b03d0f02c83c2c0001e82e500154010a80d403071a00820011304252a01104c4110002c0140c403640b18001e0101d00482c01013228041c103901d4034a41d1020008c40302607038030540144000040709004003c3c1550002c880c4941c40e40300f90404100e84130300c014000b035404508080d0011302d0031000b240c10303406d89004400901254001c110305454030700c907440f9051084403810443c24007080c8152000b016440c4248107071080c42004450303052070104c03800c800c81a42d940c0021412110007541c92641c009500541e03090088014500c0080d480d001e6104020300301c1030403640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 896472877 1250 896471627 896471647
    0x60911101b150e07181401090903120905161a12090c0307031a15220906020310180c020303013c0501110c1f02340b03061302 55
    0x284880202c1e030b040c00700400c4450742e2900d0303038400451041c802081d00540c14000780e800c150040290043c10b0a48011260346400e4109004000004042c0c00704043e025002c41d54880318080c80c402140a50010818400b004090b40203c04042d4030000c0f030b01040a12a074060401107054524500181f0406d090381e55421500d2802c2000404689034940103003800801081a04041c141c04450521250b000c180e481c004000400e505031122613a021007082034405052610030b4421203510003907080481c0c0441d190f5100e40c203a030015101c0100542c1004020f1204498010114111060ba44010700000c60b41ea40069120300c418080c0861440040030321003044204d2060f650000115a01c42040c1e03014600a0b14141610501445000071081c4105c07009442c8006031140394500010318406001c02001a10150f040f110245441540074081414140940324150000041c0c0c10308003010030140e407130f80090503042c80303a040040b07481418000c3c01601c0e10351001c0c043c1c086408000c0140e44102c014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 896474127 1250 896472877 896472893
    0x61406160506180f0105010b1c140103080c0c0402270111060106020736020a030e1615050a0806060703031418011d1209041107060911101b 61
    0x5005009440740e1003e2101e03070309025030b02048207103544044d03420070644e2000c00c0e0700317941c0207200e0031030582d009006900090902c00c40940c0960819000050188010105049140f009900c1922860f00c0421800c094000a025001c660b2400300d41c118600600c900001180c200c0d030914101a51460010a607050b034058991804615040300480d281980c3d41e0f2002961011785000d413040c0c100303003454001002c0d46418480134600c0150001098009041040c00c4001d4001a06031000c040c0c503102084c074100c10902200e4011668050482d00e102c1c10580110a182684244002048001c00a0004403640041d159411942c211061555440c0c203040c1100580003d00308000d0b4505a2020700c03030003411649111801c003130a4002803180803240c020050180002d04003542c640e4002c03507545290b02d10503000914001400a000190b044903100c1100b1140c1c001d400c0850301e181d03441c0920300034030160034024000d00310221012204c042448000031b04004904405a004220301000841004041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 896475377 1250 896474127 896474167
    0x13020702010516060b15040b19030618050907060c0b0a05040201180608090c15040509100b0309100b0d033005150a0905010e072304060819061406 64
    0x4a201c00c0f10800303d0305058006000005605100e01c0a2948150f0f042c14071000f990102da82800c0010b0a00348000f0030310031802e04c902d04020406546100200e07401c00001c4200b1a2912082e07030018640c94600900b07803402e02180c1004062240500c43c040019292503600c0d039010203044408145a1110310060360000f04010001076840c0c440c1c1000324480d40d2107541d02c0c0c03088c000b000031568904180340074490140c0c058088030a03201010001404281400320909410070352140b880d00c5095541c4e0350304c217015002034861500741c0e0054141404019640c0c022a0410707942120100e81c020107a030303405008084014550114007222003814042e01200c1d5081c40d145505c2c1075428061440d000d03050314100829444e009100e001925808981d00a03240b0134503040c1c1c0c1280b1035400c3c2c241c070703011360640f10700c17040c07085c94040441146039081c00d080d0200b000c0e000400882c0c48446c030303508100c1001186076408058004640340303011020040008003020350108184180d9403e80c0d91031355144210112400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 896476627 1250 896475377 896475397
    0x6060702010507031407080304020108070e010801050d031101060806190c2307061d241f081002041d0609070e0303210703060e09060f180604030c0311010b130207020105 74
    0xc519202030007200c1f401148500c5c0300760b943c506e46a5651409030303100c0c03510400c00e500203901007005000c103090110720400351a000342446c800541809150740e00b035032081e40011100750008000d110404194411040000d001c407881844001d01902c0e00900d4000d42144a41954152003140403c412109080710125500b000c03084c0701c0300001d09140c800a65015a044945205800315684040c0e02103844140200c0c11015583d26905c42200c8204510950500348040440003600000c541e4000c02c04400e00310062800541c48a00e0a04054a80344c0d40c5415402e8407401002040a1543c4018207564842100d0401852070000e43e07000c40d1a5001301040c10180c1d090350181c29040034001803110b032283d4203e40e001d03c0300c65140c0b8051065030a0560703c0c522690b110f200403402d50301081c50040d1340600c0c01d5540003950000158540c0ca40071051390181c0200311034056003000e160744031451901030491040280304c80000035002c02d1b154440c80403001d400c9503004c501102107a02c51400c03a1810f5035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 896477877 1250 896476627 896476667
    0x8030c0403060e06401e050601150306060509120106050621090a0c060e0418121701080a020f040b0406180b0f090703150305120c01060e0606070201050703 68
    0x10b00c1c1003c140d40d01820b8034801070408240d08100038580e00c0d000c2642d8a014640c600b0410825080086401c50100d1407007250312401c404a06645085840110b803482c0380518020803035949400000e400003030522495504140c01c1080034042d89403c0000c544103a0001d8135101401c07000b81d8415030051040303401c0590710940002e000519400828548882070b07020f081100d0140c0c6840030b400b581c80000d1040140015210b4004000180c001c0d22031414841005d000824011280c0200030241c0f030088500300d5140e40c0210180200c603910100c1035101a000680c40c241550401c01499a00d10019000901c03a4440c0c0070801d250f61030b1030b00008030104c8054020300045444040c0600510040c00001d03080501e4502000b1032441d040706e40c5003002c07038054940e002503202d906048000d81094409007483e100301c07800010006401300f004007024005031100544481c6820025401e6504650001194000d10380c01e000103a510b1100711a105582420025904c0c14503180540e202d404440c000d89540c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 896479127 1250 896477877 896477891
    0x15030705040c0f1202070b010e040f0f1208060103050919061d1e0c0a120f020d11040f0e0705120f0706030b01030506030a1112030904020d06050a08060f0408030c040306 74
    0x80c0c1008006600103025110844004d040360320b00d004a0007240d00240c22200f103e001041000960340c142d40d00103005914001200d0180d48902a0b5640280400c0b030b100c890340a0136800c02d80e0308c04400703500203000746820f102c0b13428850a0240e50303280703c56600c49425490f01c246403c202d807544c021407028210010007000700605020b1142c80e211a02521085070600e10b101c1000140c01003000c0041040050070181074905240d081214020655022103071541c141e0111030150362038201020007240b154490580702034080c41408140c1c0e180011001046080c14018041814046800340039141c0503a5070340c500d01d5002e01e44d10310f003984840a0f00020b0240c000d000c14010390582101000c1c43d42038a003403050341c40d4081419541c0305c800c08080c1c0004100d02d03881c1c01c64540010900c1d2401d05107070860741443d122000140c00c0368001c0014601640d1703100700c104800d04040407202d00400010000d40164a0a0190807070b05000c028002410040700000180c1000c1801c1c0035207002d9604a0070800641e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 896480377 1250 896479127 896479151
    0xb0c1810030f140603150f131a042a2405071704081b130c090b040b030f0c0c06040b040c0b03010305030307091a070311121c1b081503070504 62
    0xe07090941d007060086c000d01c0c0310110300d2046480650301032019030122400540d00d900142c1c440da43c21050442c4c560710064107200b0a99180c80c51180244c0c01403004c51101010a20110185d81c0d41c00412400002440020484101c4400740b58210708940751200030380b5210540d04445c5446003500082c1448003140343e820b410314001c00948280c54180c0121400d042c4011001000249a90f000035400f0400500365030740445c20790070200d82c59000f4140594126110345050341c058006c1d03005682865004020490402c150388000c81d0030611000d20309152003c900402521440c008102a101e01130b044d02080404c800368000034001c0c0050344800b900d17541c6074a0801e46a44c8195110800540b0b82000450509500f4880700403690220060515000b072070764059601e003815161201003409070a0040c140b9a40010040034640445004250a16410106102252400e045400062094042000c510368018030a01d4202c031a082c0c2c860042d450120000707142c0f4105800c000d40041c00c284c842620 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 896481627 1250 896480377 896480411
    0x7060e24041e030c03030f092711030708040320060412110c0105030105010c080f0a0336140a14070501270b03070203130b0301030b0c1810030f 63
    0x296802e4040d02d185102c090707595522248614040507203124180201040028002c0040150070310981c1400c1080643c0c41d513018599428500c0c180c0d000c10f0904005072070b214528071603000384914110301e2b1420341c1401c42c4010594140144000c042c00303492408038200c00e807040540a8048445400c0351900d15151403d9202c6242641540004c1080035a0081e80e0302d0000c02c40348101300041e0340d29821a860200111121403100000341c84140080003440b0300080540e005000c540708036200404d0300410403c0c07030712040c20010002c4004030380c821400e03088220040000c1040940111036100070301660328410707007030480418005180072980c06441010400100c1c03c40200e03142600d50000c2c004801e0781d08500e201c6013100001e05500c031143c003445802c0424000e1500480b9510469080080c0c4010743c620781000742e0003440b141d0070040010420404900c49181d401001034108904103840040c0740b40c0510201440e16104007140584050851304c2644001c84403480c80c141808441c403c0244056 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 896482877 1250 896481627 896481629
    0x8120903130b0909060f0a0905090304050120060a0f0b0415090b01091a0d0b060d0608070b07120809030904110c0d0c0f030c05070b040b031501090807060e2404 70
    0x941401465030004242c1007000683e43c29400240c1400380d10390b100b80c10441c0103106030b26003507842108100041a0b4110380d100c0c040c420209007000f50395036401c00d0005064a41803c681c001e0a900c007000c0030820305808141d07550001106480440c40e5150b000204000e0440b01000c550014036081900003114a034034100f50441d4080c078020042c1400007001116021058090308240008180000d40e00c0901d290040103664449800080c078100c009002a0b440d0b0310003400c249080b03852718800e01c0130032820301200c402001211030070f40c5030440301d0303076078086001c3d2400300401481201c20001d1500b2000340200c80c0c01b80c0c00140100f0116000000644075500b24984540c001e100c1c1050007e074541c040c0c00224030083d041b461240707040f140c903a82240d0b0348c40e000301c044515020380840040c41040e04d4019102802d0907404041d100c0c0b4007064a1420f02d100505080d040203c3e0440400440f0030220700c01058640500c0c010700b9503010480411b0b2100d810040c82c0b03042080a00301c0440c1281580c001c2c1c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 896484127 1250 896482877 896482897
    0x319030507060f05042a2c040302150a150b07060b1327170a0e09040c090c02060c1e090a0f03020108010b18010e0f09150a090203101208120903 63
    0x142450250300035407013502c0c1d10003c141b0001e0940c00d00c24030111783c903ca6120200700b400090f2003c0c40610010b1005115410389044025901410880d05032421815200340c0c07142542c1c800700302d80548194144d112608034858054402c00000380c21050cc103058016030680b01d809401407115000c0f030801040180050b0a00030181c8400701c1011840c40300f41003400c10229004814030380d46214242c0074004075402020018240001450036000a46440402c144150700403940c0d50b560301e01d0850084191912100c0303041c2150041c10801c420040100c054860070300c106680902030b0140b42c3c118549500c25003940e5a80601860ba002a90380311a95803131094900c00c0e81d0301525641c4c4e42280061394090f012240e2041b150084190351503500c501c055040c6107600404680a08800d4400700d2207525003682c0312035030b044031101420010306220a01000030400310303a00314558a0306040c00c600f181e1480c081c00410520100c4440300317209003903050742c01c5854032490011803070401998041da2584049010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 896485377 1250 896484127 896484143
    0x906030e160b0f12040b0a112107030b0a230307080304030209040c030213050f070518042406021605040911150408030a0201051807050319030507060f0504 68
    0x651040404212420036025000c499a2064200710100c1c5554000d400c0324004503c05101060303204c2a215403a0f4026801402645078504189914000303036101034240e0720206004002448521415070044000c49480740071403c1c26490f0580e00710080e0071418000f651217101c0880101340e41e0140c000c41c1c50000140c0002400c8000414145134039204584501262600107000400160030000c440f6030340310b407284400c0c0210720340380d42c0019005040b0500e5690b81903500c504104080c000c020140340c0007030150a0607814a0500903c10f5500c91707040d00014002c0361182c0740720541361010a04a6140302580a07500c00540d00c40c82c0080d41c50050455204011842c80b00006284c01d0a21400030301c0e0f0717044880d411100300e400040c04002c481108070b84070500403c000c0050004014000b03003510250b03560021a007820480c5000301401d2503108640442c0e041150704000c0c070340d80024100d000c03414030403200a4440842c20190341d2406092000307411113091143ea85035400499000340d203d28414011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 896486627 1250 896485377 896485391
    0x10501020105010303021f0209061603030b04151701110304031806090b0708090f03010f02090301050109060503031e0f03011214011b05070206040305071409131a07110d090603 77
    0x481c00e0701d100b8072015025800500c0c0501b8001104240300320041c03100030002d40b070200346101107001a8400701c0320842542500082104242e8580180d07203803000c04640a200d48801c409101c0d00a05840c4940b807640d840e40100040070001c290840c150300000c0091050f01c2e40780c10305006d040002c00c40c11010480b80754810104105020307030303004402d42d40038030350090070f0510555845549a1100b0001c0da40903468014400490384c00740150a52410b020704003584a41010051500351103040e003215206500b00b0600b480ba07a10300006a030301c501d155000905045202d80603c00c0544100d00000c4440c00000001103811a507420403c00e8071803180c4400d000040c180840301e42240c40030840001002410920f5841d0b40c1d103d080030305401070001b04440c3c034042c1d0f29640c2034034006596110000014201c40315000618150f40b500754008103288910102807070f15910524148081c200d0703019003030022008a001c00b441191039440c402401c40441e8016815184054444a1948910000642001c070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 896487877 1250 896486627 896486629
    0x6020408160b0306010c030e0a030c1d04021003090c0b07110a0b0306031b0319140616051606020d0c110f0c0a2904120512030103050604020f0f0d11090105 68
    0x640d040464002c800306609544034100110f031186040303501a0304000b0411a505480c0e600c150507a00218811841c10792928030b0a44c880c17010078205845003c1e104040b1b41080050303221483d44022604070742c5000903007081c5a1506100603075103a000170060440c007180880c10003c10703a01a100410040700c080c09460f40d80c00039400184002c444454140d004445040c00c210183d2100a00c0d00200400307035140c2001014402c1e0600c3c11260090750a48444a8140a10301d0203011440d044501210101131801480c0c0018101d486250280c05070740300015508400d000305581680d50384031240b0301c18045003283c154010034078845440001100d018802c007604c0101c0001440020042016003182d105a1402e007980c0c00e06641d0007000001641420f4006909001d5038009001038036452000040440036814014600a2405400300c401482000144041040010304c01d40c001d0303048915041c0c14207100301052002c83c036070781000d0f0807a2601d14054100121203822a400d03e03c00d0ba508586a03903514 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 896489127 1250 896487877 896487913
    0x1a01060903170f120c040b0f0310080312160c1a0604050f010f120503070606030c0602060705030c03060402031003170a14090120150f07030e010624020f0a06020408 72
    0x503100c00c3e1040380030030400b0403040c076500a03141d00002454070141070503a00d0003d4102030b03120300d0300400c44880000c201300c02c00d0201180d0b80003400f2400019400d212040c818402d00c0325000e840e450003450a482025030007403060b484500c011380d1004810070502c10440d400e130814079003901c2c0310b4410340c101800100c842c0f007150803990480b10341c0c1580500c150701e010010301c4140d80c60002075940d80030801648000c20000d00070a0011841880201441392505100a00b807210152003070003004020824042944000d0381a20b8111f841100c00603074a071603002503c800d85000c0d50009211501213148482107400c0c0c4400303000c1c9240b1a0300c90042412401403240c481340700d000c02c40c81c049504203404000c441440c104c3e908060040ca022100c0c8942600b403018007441c1d017210f0391040c6a00b01401c008450360306008107845a46208000c0c000309082c07002540302d15401c100182400f001784143c59170307054401c20000302041c801070241c4100030f24030304201000c0c0d4003502864800d8031482c4c007039208001d07600c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 896490377 1250 896489127 896489137
    0x1390201110a1107030f0c061d0307050f0303190207060e040e0a060903090b030a05061320031f080109020f030d0903060203060d020907081503010e0a0209041a0106090317 75
    0x180d10424074041042200340c44030f030305155080702a8400c0350b6000c000520403000c107815190250b80600c0e6051724040008204006941c081c0c01076648404003101144c0300000d019055030022100400901c4441c0302003442c40c001c80000045948090302000070700c039000b0441105a0b6010340d0341d440340301810300511007940c940858441c1ca56011403801004a8220341c070901030180b092030a18402640c601e2242211e030402d6400701c003d590348606028241c5080344402c001c0a1030441d051254145001e814610004012803803403000500100041921403800d808485115a00079480c441584540307079240200441c41040340144004a04202ca51070300080f40303000c031649569400c800c2c80c20b5948200c007031342001d05056005252070f2040d5005039109050780b0710a8000ba500c0d031080303240000b80e8107507030a03004000340e010780d240c10100ca03010713039000c134203100f225030152500155a2254030781106030f00c00400161946283c20000480c0840d030240350102280d0040c44c0c0180305040c2c0043c1c444a500c28 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 896491627 1250 896490377 896490401
    0x708120d02090616030513091404030804110315040219080d0507020f04050106050d2406051b0616020d0203090d060f09060507120e01020705030a1101390201 69
    0x418030039151645200d40042c882c80341d02900040c100b43e110f203260030700100e8200003100072640100c0c200791440c441c0c0c01108000d00035542c00703000700d00701d603408880c01c088054030160410036030100007000c0c03204e2840410740800340a002c0361052031850850504c0c0e542c041d103040b4401d200513070001614080d0385548101303403102c11024081e20029210291595841480c080ba000001843c498009995500c1040c2c000c0500d80c803810350307640300b0b100643c044420351340002d00080b030841c14004002c0e08000c0c0080940e41141040323680e84c01203000c4c550f03c0d1090450003045a210f942d007001408504510051007288070342d022501f22218540e000e9031a4006c4180440c1c01c10340c400082d00108030942c1000d4541c1d0b90b203031000110314045440d8030003603560843c1c4040102c3d070410030038100d070b40081c803c2c45181c0c1c40041c003c500f050501d5a600d51039100d03040c02c1c0b90070000d9242110000c0c02084d4400420b442d511300e02030b03401039608a400c812504ca0714596001294170555107a10007030040c01150380e541c02c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 896492877 1250 896491627 896491663
    0xc06030903030115021212060405070c080a210501080a1a040201020a0809120d260103150b0a0906031b0e1303052203110916051602060f12090708 64
    0x300340040a180000134090030811071180c00381c405402a0100020080b80303a015206089514000d000d00080d40c0d400340011003006550300a90000c03480c008199610354072645014604003072541901080d8107003071490034004a29002c0006141800002c1800d84184503480180841c40c200001ca4408070003101c020340035030481c41d00d000c0000c0c1001c00600d0389000007806d1008504142110a04e01801c60708000e0201d11440d5900c1207041d180921a0380010150295605a605590302c0740e4010592a421180e101d0300c40c40d0f080c01310340d078000ca41c1c005000001070400c1502d0b036030b0a210203000381c100035140c00d0324000308001c918a42e04081315071003101c0d1446801d0102c001c554085886602c0320002401e01c031421844064280320403142c1c0c00c0210700a88103000d44035088030411002441c05080042d50562200306000c150350880240c900d0544001e840c2c110030011400886c1e800e10a001451515160000d002c00682150240c1c80d4019070301c0d03100f110000740d12140c425a64081c44004401180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 896494127 1250 896492877 896492879
    0x504031a0a0c082a0712022d250308030a05101508061003150e0405010509030a0c1106040905070c050c0604050d02061812100e070609030807060605060309010c020c060309030301 78
    0x85001e044c1c803a001840c0310100c1d161200c55100d00c40c200302c29601c910016003000a51002c042c400c519080303030344200d000d029544d4080c03518207165280518000b1441051914008000200221030884010b40d00122030503901d25010342050002c05040341d41842e259801c00d000f0400315005002e000400300540c442e84280e03141d007020030031600400b484487c101901c2d8161181d01420306e80b0300f0070040483d550581d0756030816150160135654000c0a807421944140700100001c2c0d44402c2541c0c6054108110601d0780d00d40b01e002c01c071244a42d41044019504000601c19400d03403181d00c0c0c0308041d01440c00d55002c241100c2c01c22400d849103200e00c960005444400601518000c0c0041c128021807541c82d4080c03103801c5000c1a174040620b0041812500722944802c0c021195000b0720003188040c0018101c001d00f0100c026001c3c940e01c0c04003504d10354011400c00e04208039503010502030403009080584924090a1844c081c04d880c181410050003141e06075491402c2900c1900e0240c0358a00c055415030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 896495377 1250 896494127 896494171
    0x150f090210182c090a0201080f0a02040f0605090111210c01020c0a030806130c09060804080d06151d1e01120f14090a030c060c0504031a0a0c08 63
    0x8442020070241c07803212026000aa03800490100000c802ca90340c1800d600100794110780c511001000704030300c4c0140c2049040d00010307a4040c071810380c41110040c2045450b15010100c1000340265001005400c0a180c2d011400c9500310303000d0102c8010990b10740481d4004c9401440d2922104910034412051000410b91a100f9200240c201500e03c2c0b8001402c000740c0d80c8a01d49842c105800c107802180001d424072070386080240e107000100300102018840c0c108110300060500c001403003100d04015001021400b00552281290100051503a051003055119080719030302203010081000420242800130f4400001400320314925500144000c400c5074483c038041c0200301140d018141004600040f5a841648038070511202c00400b0000080c0505003403028001c0d0b04024080349165440300c246000007a03406480802c0c02a8440d2011441004084069949015580001701180500b8003200c40319194910110320840b0680014000450481000e8844190071340e480c2500d1143d26844545c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 896496627 1250 896495377 896495387
    0x1e03091101032f0c060f0708090a03083d0501031a0a03020613080304090b03070b030105031b0f0a031a06061903020903030d1103070207062a1a04150f090210 69
    0x80340f070702004080c0f51004103807407503051000843e50303d640b410301c8809000a9030303403246515a00060403401054140300c00d460180008800070301e0640c040c5c0e061000d42c1405101c41041d014445c0c40a40c200100020380030410001065500a0344d000910340301c00c81c284050004245440036501825140803e819a024400281d02c4440840180c43d40144001010f10b8100010001400400c100090800e89c900400d42132044960104411304028001801107036008a000d00f5052043d0b0f958004400300c90021400b41002d40201a0b8040000c08000062000c04400c400010001c0168400f166031a10100301e071070702501010005a6a442d00302c2c0c0c0115001368010100d00b00c1c014126820011390001400540d40e840309060b03001a030110038010450b03010054900a4a014204050308540b0080c414030360603200d80490040c140410050f4091001d00e40c58198154030540024520b80307401e007451840126028429200a481d00e000030003009501e00c940e0103c59401060003041c4110760400721a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 896497877 1250 896496627 896496701
    0xb030705180c1308030d140106051c09020405090c0a0f060c03080c0d0f060603050a0c2c06031006111914010e010e01060501020c0f030303040605071e0309110103 71
    0x107000b802c02503620100400e90b000001001d41d00000e40e69603001101050a4420f450340b5820b010300d030f910050001d541c01c00196500029141b40480e0a0b00107409048041c0c98620000380d042454a82845803e00300426029040300c800e8400c0c80c3d006a07255444030030450035211f040002001d1b0307149000000d10403c1800d401518005c1e420b0f00707003c0301840c01021a4508144140c803982c0e00c2c042001181d0b01402441d6004001c600c00708441e103010f441c05820350401000107034651015604c02d102e20455401003000105d4040c1055449140c038846500003001e960140a02180e07045041010800f070008a241100700300c0c0b1144140044950350700c6000001c0d10070312559a540301c070b080c070003480d100b4400e00c41d00700c03194400800c45614080000e81480c07441c100d0640a18181c1c140c0c500070f80c800000f160f8006600c00c200280d41e03964003000f00c07441040c003003601f01864415a805595140d01da0403103e40140122200310401e01c2c100b00540803144802c0b04242500f00c6078558641280400703100340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 896499127 1250 896497877 896497891
    0x220203090703060c02030918161b06020f030411030a1716141c021911030115180f0b180403110a03030203010905070513120f080301060804060b03070518 67
    0x340050b40c6070343d102810b64880104150043c0c1c0301142c40b0100d40380522075801c605c010100f0845203410440c0c0c6689084a05ea2186001d1008100745501c80d80c078a4460640303400d4000c3c0307045488451810118803644c1c4280c0b010798004c4c402c81403200417450042004d07080203500009200614015800f80c0645070403030343e0b07980c110301c001e038802c038002ca00d1805603201c1c4c01e203400010304a08010f14600d0342c42c00348000410400c40d40007501300e01001c140260462101504503031041078600c90b4000083c090402201888007e80321f5600000303412a011200b07800500c0100010f00c05490702c0300c1e18070b0403a1104800540c2c0f007030b4843d110100f0544003500043e0401e01078603101c4d440e8076030710403110318020300410300705d0000354000700400c02c40301e1500c24a07800c241c080c40d09e1440c1c40c241901c1070581400d24044c1f61030400b40709c4a00802c02482c0800050081e82c000b881d07544035a03440c07401070032000301260b00340c1e00a8200101414985404a01c020aa8800401d014010300761140382060000e0010a20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 896500377 1250 896499127 896499133
    0x2240901060b0414010801060207120f0503040503030a0f03050903030705030a090c350a0819020c1801091802092818020a0f03030503190209041401060e22020309 71
    0x3003006080742c001000a0301885024070540e0461600050203100141d2012045400200e001c2c0284043e14104000958002e00c4a01d0b54210300c3c1070035401d511a65001c9035240c84005081440300360040340405240c0e5480d1010060b583e12410480e031244801c03220840012820000502100d41d03590140c55200e000c3c110307a10086468840c03030703400103840340c045a00c1d44024009155155101c4241d9100041182300a09115101c40ea50032601d8094594011045981002482219407080017039070001240105200c2e600d0228410b901690304084c0240784405040c910a90350f1603203880c0e03c071017806902501d1007403c1d60700e4240c0d03008100c1c000e0001d070740254820083c02082d013100d0300521414206256070504a6401072040002580703050b0701802c5010200d84041000c80d41010a8990001c18115140d51a4031a01204002441000c0ca2300754401d1418090401d060082016a41a1903403030b10f81143d0400c0c410304200c0b031404800d485480c82c030702c03401e03032243c0a0310b60390059030300308000c8011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 896501627 1250 896500377 896500379
    0x306010f120f030315031b0611030904200a0807120504020a05040e0c0612070f0f0f0e060702040e06010f05010302130b07030915020a060b0409120e030f1510060224090106 75
    0x650801c038841c9900980321020300c7c010350346a03082451002802417178a824145410307280c81442c180c990003601e01452143e0703995007001c0300402c1c0b41400c0074944603070640820390b201c20103171020705580e2054484100050f03182c12101d82c0400d00d442403e0085030000c0502040c1450002008094880507000c40481e01034001c0c03905494558401510050740c0d18000c1180c0d034505100000c02c06510300c404141000300002c0201c8016030088041040c100880c9405500c80320144003140052051000081d0040d140c18080c003410f92001c200c0e075050b0340119100754070b003555800044050707008814088483c0101d00d4020090003c0400041804510a05054151665610650b07a85401c0d850300700f400347c4c008034615410046076100c0d225441008407810030003201030340c03aa4649502d130043d1041c14400380150fa003c145c0da0030482d40d8280566a411100180040c00b115001140d00f9901145c03858008040420f11900215103203020040424148072100e11400c0c000c2400301d009082c004c42c2e9542e410b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 896502877 1250 896501627 896501651
    0xe130302030c03040b12070212030c030405031c0c030e0705010f031a06041d0604091a130b1302090f010b030c03070c0b10031b0b09102c0306010f120f0303 68
    0x21380000c10094184503141e444401d22000d007500d0081044045412414441c15244e101c1c20607203400c104070140103900e0340d83e1031925070303d1840f0301c9404507601841040340c250070034482c0d00502807590982da0148119400c2c480300b10743c1e0704500c1c041c1c180802c004080c50100244a036010440d0301800454541815922002154a99206400810440b8074803083c41c0d20002102c40499041001603504208a40d282e445041c22468600c0d0800c01240b6040003044104a5074040780100c25013000340c1070300324280860a42c460791400d040c100d0013071020b000010201c242c200d0015040300c50700c4440600d140c0e07403880e642c0c190303500c0142070800b400000c25802010401c0000c0003032180b80d00d600c00c0d40c0d002e4114240703003aa007184400c44c000025010345081c02072014003400d50703121603810b035001c500c4e030383c05020107954080b01081d03800e114418101c5050f0101030100b400e10030000d41036060b50003603600c4100d0601680c1c010701980403d0f100c1c45000c003000483c0d1085641c01e00c0c2c020302e800645804644 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 896504127 1250 896502877 896502883
    0x180b130f140423030c03070b1509100602070801050903030a0b1c0303050a06081606030c09030501092a14060304020103022701111f021b07060323010e130302030c 71
    0x358040d5050700b050020304850010740310004031503c000300021414200c4c030001480e41c030b1203003c100070610032401001c45e0440c3d0411001716051100240a5507442c0b40a20900080107041c0c0f15480041c4140c03a0b000440d500e041c4215030181c0300a10240d03107182c0d9134a195074040c02c4101c503542d4011001081d5155090148150120368921075076000c02c0768100328403510b054503520b400010154120403469440f820f25810005c04030351035030402203802513400d03100341d600104640c0060415403c0c0070313007a420459a16400c018404010202c2040080410743c40310035440700c1c0c021404c0320041e0786d003251342c030b4541140610350242c03051502520700022000e030461062020390719039500e005503400081c010b603080112102000440c0e80140018400100103801000300040b805103403507800103c806800304105031145031241c10070110349481c0d649000007001006400804160340044400445104202000c641d040b9111001441c009881e110032041050b03035401c1c021070540c4020801824051424 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 896505377 1250 896504127 896504131
    0x109150201050702013b070504090510110f03130f0204020706090c09020c120309011b050717031303083103080a020901020303041e021504180b130f14 66
    0x203500114a40c1001003010f0b00b03607080b0301c50880003a07441c0d40c412050b00b104a0a540c2081e41032000d00e40d58803800c0004581086400c1e003095411034203041450080c0000003521503e40c03910a002003140100c101c3d41040240130f1b10b0103e000104041001c5250302812114480001d07004014440d400380f51540018101e03417014808070b81a0b520340d2a41000d0100541c0d0203401002d070941e05619021490b5001600c1c2e919181c2000c031490008000f0884500f002d600141c1ca00c100c03e48240303d80b1000000181154001d81400c985151a4071182400008044150780c000d00e2419050340c070b0661070703540941d041e050040103402e9820343c8180c01200c00c00015607011811114800000344150305045c001c18001c0010703d5200703003034010001c80c5c43c180d0780001244d600540007060b400701c0540c0c003035a840c43c01c02c0b1203501960110054440010300d4581d00010000c43d801b0b03600031181c480b211400001030310b517910541c3d58400d240c0304414406806a40010142030401c0c4000030380c00d41c2d06220401c00c0f91007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 896506627 1250 896505377 896505419
    0x212100203270105070503160c0c0605040509010819030c0317040b0712090c030f050307121d04140a27050309030601061103041806080105071805060a05180109 70
    0x1c00010030886002c00d0305409590800900a200380d15001c08040d00d2484094011740c007c854610031141200c1c8506000060540d0244c40201a02d559810003000da400038000c80f4860030320103000051079540052501480c541221942c04030b40b14544058450280c1d000040c0c05100202031500c01004d207003100c0341d215a1146802d400e16060159006100454120040f0322651400c110704001c41c482940982c104d950050341a0124025403401506500a00340010b0000c605203101d559900e8201e2038861542c22408901b6809a100c58200400e4541003861091004208004203080c00250380040000c2c0510050311000c410707580100c4107040d226520242d80b10381000c00c003452a0f140034402e081c010085403400017001c88001034402d40300c0c420742c403e520100030b6036a00943e06403540e1f00400010901134008104910306494054406071503c4020407001c1200d60000c25680303080e509684101ca0790303564103400c10030821815101448604d0909040c0040c1c198002121710b8a00656140b03001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 896507877 1250 896506627 896506651
    0x3200301020a02150a09050a120302090616171912060506040603060509010b0301051804052b0809010e0d0c1a040f060e0601030218060a081c08010f05010c0212100203 73
    0x758402c43c04c4d00c01c120203080741e14694200000440070440c0091010282d40c2c00100200300600d082d40c2c103800070310030341c001a9000b80010400c0c0c00703441060005881030724050b1100400d03915040201d070195110700c00c11034600d00151910881010b104d9410301c0d10012140000107802506c500001c1c2040d0001d0784018000380e01c40d2030a020909160f4201401060710905007821541808001003103c400010508459242900001c0a005080120401044410504445510400f0440b9084070101c0aa03080802d000c10040794080005105c0c01440e406604081c2400d58030100080313a035040d02910944e10580311500445001480404060060707101c0c140c00080d11400341740c80c0c825122250318440254011100400158581c0c801000d03028809e4502d00b0a07694541c0300240c444000c43d0803c4100e48991502c41030080001e0140c02e0503506152501c08280e0ba83d2000b480c0301801c54091580007d2411487c2401420318000d100716200c5001700b0350b10300a80e1114480101d0b081202c0c0840502 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 896509127 1250 896507877 896507893
    0x1080304090b0a050d02011407080a05031f05090c0a021005070f170c0d02090607121107080604080f0703020f0124080c0108150d02090c04050910080703200301020a02 73
    0x102079215180035002d050b00d0303800c0d40c1c62620f800500c144e04244806814050607038400b000300d122800440781407581c09040c1d1070302d501404030300600702c4d002122060708030540b1005040c161500c6038800021100001e201d07480c1d0740d46001c0500d03007030b42148000c082584680c1c1801d1241340038600545100d03d56555a60301142d50480d0300621040403a6040312801402c042400040e501f288201d8a0428900d1009651650b100c030209581c4d118a11000e4042c0d40c45101c0c00c0e100b00d0b40001c1c0e00b01241401c201310f40390b06803181101a15050107460081082d04100000c005032141c0b8070150800d02d011740181d60404401c1c801c01404c0da2202801300c105103001e111070048a0180005243c081e00440c0003d00b1540342d140006040300d5400b9041c801840e1050400840c542e440e403259543c0d265014007090b17000e08040d87d80880c16045406814802d0004030300281c2c0803101350b5034000c103e541902c020700c0050f246444902105010101d010711403103100c0c09842090b142400188400b801543c0200584 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 896510377 1250 896509127 896509139
    0x1a0c060a0506181012080708030403030605040b03031c05070e03070626090a03030e21030402030f0a17090f090405061006110d050d02042411161e0b0301080304 70
    0x203c07641044000f074150b000c070244070043d1005070448082e155401d4810400800303506281745a4040c0c000c004098080000c204820154150408000c450f0251414800c0f039040101301a01e0b801140d401400a0015030348200695440303801140d00f01a10f810062100c039036607800729040c46c803d40c106602003104014180e40c00d1802110303001c0d843d50050385102c0390f0709040645c07070781f02c81841d0005010143c80e4100315030524014005000380b00071003041c490000b40342d80090503d0f900104c805a200b030294225000080d42e010403058140e55101403c1c0752130f45076603c001c0c0915000208229080059505020f451b902e8242151340a24001c2000308103e14040030110401c0001d508003a0401003001c52030032040e50001050041482da500300640c444150b801c150009000701d034004842d400310581c04141156820400f500708440315503400c55110000e2213900c0d502c100c0b401110341e80511940040100c1c25584444401d8a140c0100b80545240e903401e920082d90020b8001d4030140d0030010f020800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 896511627 1250 896510377 896510389
    0x90804240e060a0c02010509011101060915080a02280810050f10051309111e03161d09010912030606020705091e1b16020a060c05071a0c060a0506 64
    0x100c0002210220b143c0000400020850500180e000b030510a0209040b0980ea000740e42000701640080b000f00a00da0f50340d100c0c5c1001d880ca11402111241c2d1042001c5040c8001060140710280c01a000d141c041440c0c0850580b01512030740050134009038080c4c0850081d80a1001d90b4a00910140104183c10654003909140234050564008044101010092600d5544074111804810200090512140e043c003400030000c00040350b5000e044580300b90480f03000000340861943c0141d0884d0010009003201c0070f110000380c011a84251004245450803140d26a4483e0380240100004240710366a5a1410308020100003901c02003601d82e64240000c40e0304103d1a0020101214030380440d08026241d40140c264032020341a04440c0d450008594421102140780c0418183d00840d0341c1d09424600b1140049050904030f12901072520000b0b40c2911500078524101d80250203406064503003d030008034003088210207503400d442400648001d20044c808540308a50748a07007c04c20307203006020499 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 896512877 1250 896511627 896511647
    0x203070e0112180212071a0d110a080c0d0f23130b04020f0a0f0b0d05060922020420030105240417070e041202010614010e0409080424 59
    0x5605480d00141d80d40f40c440320075100d421075405642e09104143e503d2100d6080c500c040d00588040c1d02000d241031244211500100b005500e00f0a041141001001d1851060310492440000186001011650040e04003000700070445038828000b400d41c510b801e048050302d0900110300f10150348080850000341520342001c5c0c1c8103204140c0c254503810b165541400311751015002170300441c2039411005040d04c4003a00c0724098911000e20050281d03031640035034120b07072040741d541030321508003004100d02d428800b40d450b010ba0b410501c0c01d00020385039141600000800042664000d4a69102c042e903080e0100410390540e01241049903650b041009002200341c3c0200f040d4400221000204194050801134800b50b031400c0310310404020704544850b10b0040c00da0002400712903054248030402451409403902c02034250000d0110b07075550010400d103406625030302800324240152011052a00d03034440340d8214821042d407800c01c0d444030301009180c01d100360070b821003c06c030f02d40741150281c200d09107803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 896514127 1250 896512877 896512907
    0x1e0c0a0e04061206020f1b0604050106060f0c022404121412030606030405010e01020d0203010914071e020f07030302010b090a18020609060d4206140d0203070e01 71
    0x482864505040401030b0b648031440600226800f0400c031440710a2038040340c405d0803460300100107c00301c00300c01d01d407280010b8034100c07000d602c1c0c02d0b4001451030017034910000d01041ca454000da984455020301c01d002e03101540c18100005070840f1080154020400350000e08580340500c1102c84103441c08581010709c4480304000742e402241055519112041100d50040b01900c00d00d840f600d6030326046001d00100b1555482035400415482c3d00d1000b19805107040b02c56881d0248541500042c04804001068a42100288009000340a40d03051045000c56840d8140b040302c500034038030760b045030a0207190340080b00140d4480c6030500007460804004c070b4000307000c03000c2001200c1d6000043c8440c2803e09000030700411012505105d5650b6003030548910741200d0074140f1038500718444600e211504c2c803d0140580080d1480752404180d600240d081c0c4903a03440400940c24101b5009941e0600310000e4002014000c10189900c03000c02c1c000b03075014110341d0b112414002052070000d88002040c035004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 896515377 1250 896514127 896514131
    0x20d050304260912010209030a02010c05030c03031918050c12070305070b0309010c140405100e090a0c020f030f09090c040519082118011806080402100f08010e1e0c0a0e04 75
    0x18001fa13650200c0e00607003255090030865540c140500d80305045000707d00c3c4a4a0b41d020100401145240d0030b048062481d280010400c0840340c2c80c03040da0a01000d02a02410a903c20741c10b032811414408044401c000c0b100b002c40300003590b20398501303203030400c0e50b04440070801000c004d110b09031009001c0c1051080c03150400117030455503421111410301951248500c100084113038100c00a00071898902c1241d0050700100350751802030340300b0020303003030958030300d8014031519400d80c0d41c2c0f00010003901c0748558a0f80115181ca41d541c4100300b0801c0001d003521980d240c080100040c255917801210f01031540300c5079441c100510703010a540c02d1642c1101d0320358043e0040c0a0070390122031048201c1d6082c0c488044150b60044505004803802c00c0030f04080c40e007000c0c0c10000850f141341c0008a4510480c400c075001c8200c0504000101c0e15010001c03101004941814010300540100040450b03008401c9000522000407050600402c804140d4000300041d0002030600300c11540f0607540c5100c00c10036581 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 896516627 1250 896515377 896515387
    0x60109060c060c050d0513261c0608150a11030f0103030503180106180f0b0a170c090f04020f150306060a0306050904051e0d020d0503042609120102 65
    0x2514400d0354450003000142e50300000c25103030b4042d5003524604082c6030f01c01c01007868150650450140c0c0250281c0d4239001031a01c620141004a080c0c031445c05046420504000d48003240203650720384024000c2d82c040d203410000c54182400c01c5503482102c08540440a5410b0402d400011150090940c0034405410400c0229056000010604695244c68800c0d6644d880f1154418040c00600d07407040740d5401d004000400c0100340720811820605040c0c1084001030300071700d150481d11265a16900800b58007800c01161900c41c1208003101c8002d01a1420a0450800603c4510040b154683c02c040001c090000350300b812800e0092221040d07400c2a14660070301000412070200a080318400e500008103503924074860341001e070003031030050200e900500313146c030f0480c2d199100c440300b1681154419562400300d42c80000c01403022640e0303801030605052004003c807601d82c001081980c1f030910001a6441e45060150a04901c1c80c00390f6000c4d8403250700d6000c100140420b4000c90500381e0041c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 896517877 1250 896516627 896516639
    0x1315080a02030a12210f06080109170f0d020403081803060403020a0605090f060a141b0405010302030601050c03130e06012328050306040f020313260c0a0209060109 72
    0x55440d0742c0c283c00200210812044130403c8541021030300c6003510324060f1705283c0458040326080310b4070f802003114041c09416100c5a0480c200d07010008080c090400e0410070a01100e0900024031680c1c81900303945182641808803801641e0040c2d100715450800080c05409000c442c16800c800924201d000d88014102500e00039504c9035a4407020302995907600208600c2c1008224007407014194909448030352070011420f400074001e8900e00c00c90007042c0c03400610310652800d800034048607a28082404c0c1420100118002e4200520b4181404820840d16011007c204080e04c0310307a00c0249450107480c01c02a01c01048070014080d0341c14031030a500e0190f1a20300950043da4118000d44a181e1100c8a00e80d200c44505140c00c04080008511803503070460590140080d803007142c0a03202408003440e5404600d040380701c1218010201800300d50b90f40700084500060110300b01c1d44680d50b000c070b401c00052070f9006610440c094285580036444950841c1402c02400f0750110702420040e04003440d0507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 896519127 1250 896517877 896517883
    0x10302070b0a1116051c05040e0c0c12070602310302060c030d061502151e04020d060f0b1201020c0304060c0c2105060a1104170102091315080a0203 65
    0x2902004100f611044409080c0c4052001c0da41c030000899140d000541c52410a940c544031480111140701104e10906c0154a01580c201c07003c03a080c3c0c03840030303809540c5c42c40c1200c00364010012004542c003640d80d47c800c6200d410006009003500503540141c0e40e8203140c1c0f25003510202c103400072100d41c108841c020b0343d00da000241141100c2c0c0654801f40e440445903a901d04520403402c510801c985848400310715422407400c040c4c04500150215a01c0780349001b820321101000701d0303003403c075001c0305008401d10303c580030b40e0780b0303046803020b41024440c420340e988002c213403200b9610b520707602c5035210145607203443c0c0480201e00038a541c41c021407030300030004070043d101e1255014101c14403104409010400100404d16001401034011000100341680302a0100c2031086c002925188161404248020700703c4c8281c05610a05034142480c0510384200031441e14003030400458295801d01c440c05035502e076584c90790303c04100060006005009418030840d0000d094000a045511800d0b503100107072800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 896520377 1250 896519127 896519131
    0x10315050d021504030506072705010e030a0b0a0515010908030f0327010501030b0f06010c030e0a090501090605040608120301060503130204020a020a020a06020d0507060f060f080f0705010302070b 86
    0x1d540501c01454980081401d016a910541d0000c04000800000b401004140700f8010071180d507641000d20700784c409928480044500031405c201205008002540c003c0326050324050300030381981c107940c130251251000c07100e08542d00d840f05610382d41001000d4040c004005643c0009003400c840c0e29003842d00d20783c0c0c0da00448070740000b00312000002c038928031540203541130b8214202d005d0102e03c494040e06640600b42c05c0c481161501d074501e01040c005400c01145612508069685001014458070112012242e519180c1d400c10050180418024258000c2038040d01319104041103007843c1400344022940b07280c0c4001d58a1300041b0f000140f80071a841107904440d10751501c2a102d4a41150702c0d60400d80307d90f002035125100080b8803591a03008038203414014000c607500000c0f2540d4100585c1c0310f0040c0342e413400001d007040000c040028400d40c444021529120b80c0000c0c50764807240320f14104000d44d0018a104c2e800400054011802042040050802842c042d8289003140d921007082a40c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 896521627 1250 896520377 896520379
    0xc09020d1a1518030102040308040f030c090b10120b030d0c17040602030a050a020106050a0608100f050a0b160512071b06092913030b01090e060f04030908070303050307030b01031505 80
    0x40d24a180e03c3e25902501594003941c1c0000c5243e0361142c0c0d03401a05002d50162000b115003490058001440401034414542c0341074010f8045143c4081e000b50072141e99103400d91005441c1d40d40c01e509282c80d2020889440501042d85510075140c001c3e0500f110206a4010080c0044108210a1007002e5002c001d031001d21420741012a01c5c1c41c5007240503070241c003150b008160001da0745e0720001542a44007607580d0181d22041441c1076800d8039180d00b444c0c2d143d007034055244c126510403c20441c04100d4002807620100780c1c1020000010f80e0340e60305060412062081e000302e0b40100e20340317090000000003000110004150181d44a00e4103d0103003031903d1521850b81818044007804c41c07070a400c00c82d44030100300080821a500e030400e90010328400711034001070b508284d000002180170340452281d603040144100082402c0d030b46059180441c80310061007141040454040050f20400802030000039500c66200c40c1e48902d4079180c01000c17604580c0f841d0b8101400c04558280101996074444203642c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 896522877 1250 896521627 896521657
    0x20906060307170c0d0207061e09111905032e05010311010c0f050709051e010305100e1507030203150f0901172e060807030b130c09020d1a15 62
    0xd136012804159018100040350118000a41041080003a912810080c1150405540340b40c2d51092000110340c00007100501b43c8404129030705442c68866048400705e031000c41e034980c80310f0b15074012030708100c100c118030460a40c50550000d8070124207502c00c2d48032000c1c11420802ea62440d10384840b28000c4910060611001c103604800340026900c1c080406504101168070369651010b00c2001811f08580c0c1820949019243c2d01504050a4006040740e41103001404a000c400c40c468004101d0402c009105114a80352000d80946070311040f4070a03155038034010f03168604001c0c1060001d00c62100d85104585d10f040041e1541d94444507181540c4418030b4008410745400300291409410901603a02a540704c144507403006000c1d1486854403002c241d00740103840da104010740e03540101c1d0100506180d84100060081c05100c034401d450240540941501a5a508100002ca83c41980403022890700c4542c60b01003920001c0d000c4080c4c14040d076212440384410704e58251a0b01880d00c145603010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 896524127 1250 896522877 896522881
    0x123040b01050706150317040612051e010b03040c0b09011e180f050a17280f031206270f0608031c1b0512131e02090606030717 56
    0x30b445503055400196000c4c00070807101090810000e099811031004484c0352150f15945550905010140c80c1103484039111080300f8030003104d2800c0501340003400c060500a028000c01c0318041011440c034000c1401e040d82d19540e080500b0840b03652841c540204144031030400000c5141c2c0d0f802400c0060b07600500004008080a501c0104d512441818032160307032074407050b004903010a00c2040c2d80110391741120b4403c85607a0741ea0f040c461700c1c0149540e0803000d4000c00400c1042e000d00408600d001098500c09200e0401a030743c90044035407210034154001410a20344000c2e03038600b4440c010181807102e0003031740c0c1c106d02891054039240580d00110a072580b1421760b10205e00320342d0451400741c034400003035070340714105520f108440003428440b0b0310400d8108035544121506000728407100c4029039564914120b4001021440f4420207400d484200f1911514980401d68003c0006e2404544c1188241c0382d1500d801003084490000d0000c1d80314403020003d00c54200c0d0481c61f4a08030034000c1520108036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 896525377 1250 896524127 896524129
    0x105101a181e041d010f140c0c010e0d09210c050f0a0803030103140d091508070e031c1d1309021c0803060103061202010c060b1903050606090123040b 66
    0x240d0110758400f0b03001414007420500340c0165001c0d48100a101800801a00c41504158020350360b02019030300c900307001c040110b00130031045e60040c10b8500011002140707010714082c201c1d140c100c08170200c80005031031940c103111000f806000101400311110762090200c0306031700c508a04c40c0061054030f02ca4807011001c48690380782c000aa0300200144000c2d65207a60f920706144940e5187c484000d60703207015000d00442c000d40200803a105031203041812407440c01d80e40c0b40a44003514054108001d00141c0300c6c000f04965000c10040f91128403003800a030081070701c068040c1140c44444040310483e40c6404840d441d50301d40c481da14070400c00d13414012420041030300114407142498400030f04028080d01c804006e001042000714080d1000b03a80802c403155030b410711420760803070340d5600a00140c1e590303402201040041e0080038844000400c17084d03810f414240100541e41c0664000c03141608850200102498a2a02140188130300e03002084191928042c452041e15091a1507100755030f100e940c0340d13103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 896526627 1250 896525377 896525419
    0x7090506030622230705090405060607140c01030e010c14072603010f0905060904031101061805010f060e0d0f0606030204020f0315060a1b140105101a18 67
    0x9503d42ca07403104403e140c0c8014480c080c0c44080c0328155103c0740a80000c006984004285204900b030740e4403a4240031101c4204006004098801a8410f00078483d02010460020041c044210440010031354a400540003605a41c01c28640c80c0c011f0345071008044010740c000343c0500000d80d500c08001d0b501c001c00d24003541d0287c3d401a00b10081024401d0020784d90411400441c140e03100083e01c00882603545e03549070f0544030204d070040d42000f40c4402090000e0b024441c998028141c0c0310022a0250f21181052580e06102030340240c2e83c1d0321f890040002040b500303c040302401c0f20b45030800544504a005c82c2e040c41c1055001014000d403488000240718280e40100e020b913134014019903032400141e49142c2c00360010303116150700035100c003003404880c03030100101c032440d40da44c0e03c810b440103082c071134401c002007244141980c5282048071030b1841c81c20b0078032682d40b05209400c181c114460400320f012031245501c10400d4080c02e400c000d031150900900540d5215154100c940203052039644000d004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 896527877 1250 896526627 896526649
    0xf0106150e06040f0e010314030a090605070213050901020904140903071713030609061b08010b0c10052e06080117010f09051c030b0a03030f14030a0506120105070905060306 76
    0x1120954020b02045d81c5220a25207030403203003c0c17100711101d040150001d50702ca02c00c181c006008184d00d4082001402c2c060009481201d00041180a04207500c00824050340c0040b2540f250ada54000b949c40994506413203012421a00055040c1c0280340055140d5a28030600e90b01800c1d2141c4401d590b204801c00f1802c0300c000ba2100100159400e07a00d18000000d000240021248030303052050103a045182c2d440504844001c6941d990f0140e442d01c031021140c2d51001042194034007400384042c401782101e000c0c0c10b0003194820380c907a8207035901410301d070000c510144c540b40d500c420386038082117555030140e80c0d1415540300c6095186c0c2c0240c900c051074018980f844400e00c109084c00385000600c20080751001812100d646040c07006d0304c03918400c0b0200c070010700b2190392108480300c3c10b102286c07241102d48484042420000e03540a0103100b8140325810849400c0ca80700e031904104200c03400c040d51114961300b0010000d20060500b103001421040950048034010a40800020340694858010380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 896529127 1250 896527877 896527889
    0xb01271d190b2106160203031312050c010501181409060a0209010314041a010b070c0b090d0b01030c0504180f0f05030d06061701050303042301050909070507050f0106150e0604 77
    0x3c145502e0080e00f1548961086450350748482100402511050000c02221f21031030704060301001000f415036800d401292180c000804210007400318030400842489940e02804001c100042814414006c24013602c00400b000380c445041c0e4424401001000200350340c000c039001d14056101c44071400101d005003002c090481060800300f044c030090081c03141c1c84144c1c0c84080540708030b07643e0700d940c9182554440c1300002044000034980c00c002c4090001c0c098035013110001c055101054003a01d0340045c503d400e80058070103045000003000f081c0340612540f44103150b055240700103030364241c40b201c2000c05500300203000d500000c40e03c6002c100c014000c44035100c8070500c0400000d502c41c0c00c01891500c00003180703100006024008200c40c500001940c0840d51040481a1180c0e1010b001103410104a410b841c1401800c1c0441402c40c0d507845580e03442031000d030b07440341e840b61a41d081c01440d2040954186002e039140070310511a01e010f046040900e402d460401250a14004001c0390681c42554081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 896530377 1250 896529127 896529169
    0xc120504060f091a010f0b04061d0306160305010f030209010306050a11030703020403060e0f1e03040306020f0703030b010311090f120105010306060e18100b01271d190b 74
    0x943c20070800e00e130144004680482d042541c4da803504507034543c0c41c01d00e010b2040c062106000401400740f003440080c081e1112015a0142e8402110100c2e03c0d0032015240620b04c0c112400e1400c0500d94184207403801045640f11514203546141c000c02ca903454103001c098405501c0d90b0001c1c400c20200e03040302c0080d00c10513031095500e10f00000020000d40250008a602508080190405003000a03640702c04079005009001c11224601000806601e003050503141c2c0d0000f0f22002000c254107201420301e40501c0c40c0c0040d600c4a482c03a0040403100340040e00c0e410706240510a4680140041c2a0b90006c0c1c0141c2300945207489030000580e401c010011010320741d41c28100044100321042d0415401c81d11107648004290b00d401462100303c41c124414100107030320140460b128003d181d04030039500f0906050600b440c0c0419117284102244c0a51301a5403035640b0801000281001c014801034008143d804400d0b0f070512181141004141e00601040701d030321103511306920390b511039030900700c80b000c5020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 896531627 1250 896530377 896530391
    0x120406122708031515090d02010c0c0b031602061005060f040906080f0105070f0206061e0d051e070b072d0309080d08010e0403080c1306020c03010b01030c120504060f 73
    0x803400c0b01d60700854003071303141103e620641e0f0982e0038541182c04c4030745864004c00d82820143c2d030070f200307040c14492802da04008400c4d803079070049400c60f554a009032681140160360fa180807000c1003c054820348412085501500070400c02c44201c051101c29290308540c0765075a05402d240d80c01d168011908001041403030080005030311032001a480e00759140e1031009000c0c42c0d460981c01e680d09031503005080090380200300021041e103427860005860320103202e1190000a400b101080350103094503011100d90380841945070701d440794110b000321001410801052401d041801d000300e80e00410900030812151202080c08039400300350b103150340403034001d82c111009040d42802000060385100b42c2c1803d0142c540c4140d8041d21130003905060300c48007080c40750030b6292a6000c80310941d00601c92a10140184010fa0b00824000e1000004125907401018404405030806084800a039800ca050614101c52105640d070840106500010124800162a504c50030300b0b50141911a40100e2181c2c40d20702 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 896532877 1250 896531627 896531633
    0x7032009100e0307060908070b0a050301170703080f090108011e0608060a17030715060f0b03150a080c0307080615010507060902031c03140105060f0c0c0405070203030103051204061227 81
    0x240c03583c112100d81088800e5696071354109c3c1c100307100d51400d81c00081e00400c01030180183d06091080688854403c81d110181d9a858807071a075008101c0184544000144d104180c2d0ba004c2842d501514820f201b030038117640d01d1815180340b50141c2c41110700f4095010f00041c059506d1710241e1000f403029100c1e84e50f500d01c146600c1078590b84084c2085400c41c4400c00340c820b605503284181400ea5a11401e0840390905010042a16400090002070114652240c088180c0c4600c00b00900a000c1c4600510008101302c2c00c050074100706401c07040f406d500c03100410143e002064607407030980d82e00382000c6658131003500b4801c000c1d0518010107505445040d1010881688441000121404d10b81c1e08008061405850a030050428890245c0c046014420150440007140c01080d82d038141200702c03803044000700081815103208032000005070b04040010018450706211490002c5a008100c41c030f02400e14501900030423440f8144504296903d11040e03400707016891248006800742e081c20b07000840340c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 896534127 1250 896532877 896532887
    0x6190512030301031502070203120c1e0c010906030e0a020d0c03200a06170415091a0a0e060714130902190f02010b0904170405090109020307032009100e030706 70
    0x302c0304503140050540820741d400400d06c25100643c0d4001e0203804d000744041c403001340b281c01c044c07120400340c040c0b158032540b60450403401c2c01c8540086005003407210f060304009005900258411802d050426010400e1314a021459804403503048400c0f010104a80c00d100c410187c050300010015101c2d1603102520380c1d000043c0d5000a40100e464040054913090121a2914042092410b41c41e8034400f10300001c100c81c6803642c140401d444002800726041d1a144c4000c1414802d01c0c03581e4403000e0600100b507185008030051035004400800d03070307401c2c15540140440c0c0c0b00d1a03801c0e02c88034085002074204111118803002805a92420b5413901c0d80741a5031001050500d00b090082485502c42002103070040c0601e00c000715009000c4096591552580d07804e80c0c1c0111081d600c100d40800c008206942c0d46481e107806022019130041c0c8903c0c181130003030210b800084600d60051070110401d01900c1d00d1004980c0180c0003074540c24000c181640b41a5150011850340a40c140142c0c0e502051090f488 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 896535377 1250 896534127 896534129
    0x1e030906061009032003120f0c01180c12032d35090c0406060f14070209011206151e09020c0304150513060e090f0f06190512030301 58
    0x200c9000c2c2c040ca50588090355075101a01c001400d10034501560411a02ca000200c806008090140e5070a10b807007a00c0f00203e60303c80b00a2880241c00801c9490010100344030303600c84480486d41000c01245e0585a103100c821240c401d04140850141341d0000b09441111700c41c8a281c04100207420040e8201c074510b00b0111800b44500004410702240007107822494105000d1001486284a121350b88220841e07041400410600031442501d000a281d510740740b00d982c00034401aa10039400d0003001c2c2c0010010702c0d01c2d600000e909801801100d02580d280c1040a04507000d001c8848210781c1c0340e03e8944081c009501a81444110000c00051360102d2600d6201240d00c1c9040c030312a009494000b00c1049000340c130100c3d80d40794800c2c0000d100381000724074401c486641500f0098200a074500150b2000d01c120f4000c040001c0311800f5030300060030011285508240200520807641c504001c80481c424802043c2912510500d0780110542100f1031365900a4030000c0c000008410324402104e0b1349a200b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 896536627 1250 896535377 896535379
    0x8030103120c0305090f03030705060f090d030c080a0b040f0e28050a03050f0d02030a0f0608030c060403051e0c150f0702060105040f0b271b09061e03090606 69
    0x412903076000040c4242a40d901c40c9038907845403410030740c0b60024803a080380820340498041c1310070061080401c200300070b1030307124481c5105a02040d29107503441c9070074408840711003070615040501b58055550807030906907110030341c910005041e00c007410004000c1c0101c500307501503ea28001c0008084040404e201210311080707903101022556801a80c0402891410080c00b9600000c1040000030b01c2000100400e140b03071501c403400c10b10198942c0d012a8010741d040c823196540d460151343c9064243c080c80c00200780c0c000c0a58100480c04000c1922114000c0005003000340020f102244030026030740d028041d040160070385031500c1360140b00d195a8810003c5480c2409004000203500340c1c103d03c0481e210740c51766400f03008203920b44000d01001c2c10302c8400a110842d02c40b226119540ca4005031b01c502c010503c1c000792a048035104d0034000c24800501070305540174124204241c96180f80701124400c95080d41d010381e40e00c0c03007000c000c64414401101420140350020500500b110005440f03402020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 896537877 1250 896536627 896536643
    0x80a0c0c060c050c0607080931110a0f110a0501020417030403020a1e030b07120c030203090a0f020d050d0804060c0f0e10020a0206130314010c051c11030408030103 72
    0x3884034001e8034910b0100c44003d05560106601c2155400c00300e020301034292003100444d06190300c450010b0750010140b542844402c2e4480281d0b1100102d4040b8404058120442000143d000c2c8110483c9841361207403c8080c41030441211448510035424440c502c40c00c0c030295140100c10f807500314081c0d4440d105005117034400510349000c6080210864007100c1d40100340d804003610706075106104251582c081440ba94241d680040414801c4020500c542030300d5481030340b00201c0b200c65400315080d041c1d2040403d4814401c02a01c0c0e40e000508040f00e5400a00b01c64107140240300080b00003a840d04010181c0c0104035010401c242c110102d40c1c00b86215080070310112060307240846640d0070003a042c02c000303007046080c03e0b000d041400b0001d0101007a44180c841172401c40e0082000c3e03034408004500a819a1a0104180b05001080c40c40c0166040b00a01c40c0a0f01c55800919600a0380501071f80207050161051200443e54810312a8540701e03110640c5a250a09203840c0c0350304244400d5035080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 896539127 1250 896537877 896537879
    0x20d0506030c030d0f0509100507050d082206150806071116171e1b0306130209090313030804051201090312050c0403020d050105150607050303070e0a03080a0c0c 71
    0x4507000c54901c100c8540500104100b003001d120071141d10007201841000e0000030000f0340142c0d165008414445641038566903078420007031a000d490300c101c80a12204000640c014010a0307500010116180140f40c0c0c0c600f1104090b50914000a28540520309880b0281c802c0015080101042c00e80c03280d0140d498140c0318560401c1045d0712000111008028020300c80d40034400e40780c145240b481c41402220071124403407000240a40401a00f0b58440259441342e1200c00c00b414140b2620443c66400368050291070034250324a02280d6003000000b0300c1480243c002400e0740008009070340c520214440f42d18021070342c03418843d95541c010300540e0701890794644d440194403014011401800d90594640103a810f0202d445001010054500065400b00300800030240c0d403030030242c0070058090000007030142482d00e410780510303111201403409580c050040d400070510102c1a258464060305110340d150340c145000411503036613a08002d000076404900b10254544c49004a200280301b042c20301c80035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 896540377 1250 896539127 896539129
    0x10e0d020f12091003060b13180e1207020f090f010906060302030c0313030203160c0503060105090112200d050a060b03010203090a030311040b0c0604030906030b0907030c020c0a09020d0506 83
    0x35040b029441d903640c1c1d0300b00120840c509214012070310900c103504d0300168094030784002602d254840c03009814481c10200c018131003807030002014a12817101040400200314a8100207449140407100c84540100205022040d9103504140b5170103054014681103c91411420120108034213000300c09500740b85c07a0780800d81d41e0003071084030301070f442650115085540304c1900006007118403404030114042030002112001d0170340c5980e43d0591140b88800d0720b05040100f170502c0d2240590003d440f8031080001004452a151864048240c00048000c0070440441001400340c04201c00b403504080410000d00c01d00c200803d01c552124401d01083c005c4501d048101820b0340402d656110b019046496003100080c069449a142c04950b211f4441c1442d68454100300b080c0c00c21040041c0b181c11600400080690090501026203400d09080044400400c00301e021200b00802000030315070b403520149803060007048010140381e0010202c0c40402d0b101c049038000703500700c0c445200242d424403004c1461 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 896541627 1250 896540377 896540383
    0x21f020a1e0b16020f0304090b12160618030203030412120f0206010504020711040203040303021e0f18030a0b0a020a031406030303151201241e1511010e0d020f 70
    0x105070807150318031030b0b600c03030301d50318092140400c1580040d40b081940d4a00a82818005880249141e1400041c1e030802c2405012103000d00d844d00040c81c0d0421000d07286404441c42200f000c2c0c921030b10f00070100304160074001003441400c2e0000fa50520012900140e100c48010000710950300c41c6141115907030b501170060b1403003a0740811030703400b603040350b0018042410141e0103441c0d024007603c41c0203c8202c600011408a0344161401d400284c1c00290b00750004450103440314128041d00f0145140070902c0400b040300340241c003039805c080b00c0e1181d400c1686a504008100c150360304034000c3c4107541040d140c09002948050301ca903010900b8204031103468011050190b03c1750348080d0103145140e9596151a008055906041c1da0240101d0308d904205c00c4c0c24480c04112400d41e0341c0070307160400e190340403403e00441d42d4800d400c01d00d401d0300300811180354404414229112440f8900e0030700341164050310346640c454002c001562900c1d48030303400800c000580805026281c0c00795082507000079400380d2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 896542877 1250 896541627 896541683
    0x60f060905070c06050c040e01030c0609060513031104060816050907020a02130506030120040612020414040f02040506070c09050601050c0312071808060906090106150c021f020a 78
    0x40890f044504880109400e40c008a41c81a45101e030360780783c16144e400d11000c0c690280c0080d034001210302001e1080039001407114026040d6420100c2c1000d454504029034100317180001041410004007c4180b030703c445d0860000380a01d80140c40391b00140b6960513014600c01e01c98148036400d0b080c042100c01c0e0010800c0c03e074581e0040e0481c1c502c188880003640240001600341d1b50103641c0d42c1d41144803140b0419446e0103244480b010035130f0f20303498840010107002101740c000c040c8903c100010483d504105d1040d08113860b00b5940814030f1074180d01258024021507000b00c0d0040030029041080110242100040d11310420040005460700c034011a045e0140300d1211005034402c006007285007482d56040c0b83c1c0843c0c00c1c80c150100c03100b644d8404034100c03000d07882001c055009405014071031006100e0298800209002088500d160084811130440c0000b020414003c004000344155100c078000b0115660340249810401031442000960f00c070512101507503001058100091780f9400c84003460 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 896544127 1250 896542877 896542891
    0xd0615021504080705061906051f0315080f010603170702090123030312070201051305060114010507140a0203190206180105072a09021314180103060f060905 69
    0x110541407012181600400341054444141c14814440010410040c0e5032082c1c401c0341c40d10b04610000000102941c4a0360440d81c0710341c1c05e41114041c1003038901d202b208031020502d070200c3c29980c00301d00c40c0c445881e02d80040f0703124000d803400b00704080c02c150805801c60744188025110448401500c40c854020114000e5101d40c80c000100070781f0305100300c2c1880d480d0305401c0c5403038051130000c00030f49582c0c41000300409540c81c036006c2001c40c03030302882902d03400441c1c074284c0a103412040c4e44150311138105000c0c4105024001c807118100e0f0b40700d04c0c242c4034060342c0501821100120351003000d949032100f00d0100d100c1d01c50012226046d00304800903506840e0b01078903036400c4c9902c1040b150380a500007802070b410000b042c01003001083c0420464607400e020108442da02c8684640300000a0080d600030100d0580104190061100030070340800444080d820003000c0b240c0d0850005a08803410140c07454171074800e40020062003440e5000d480707d141072640030040b1a80d2100071100385c0300700b16000f03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 896545377 1250 896544127 896544133
    0x809041a10031503020402220f03020f01030e1c020703080f04080f2407170f06040b121513050f0607020118020f10120207080304110406050a030809010507170d061502 73
    0x1003005007000e4000e17043d60301d07000c02e08540e942d0144208d000103c159a00924250120240c10029070510780d00e1203c0d402000e1805000d0320790ad01d0790441d03403985403a0b55090307602000b41100442d03d20038484075014540c0501c64542d94000c60a8008864116020312041740c0100c10000700341410004031400b441d560949042d980c9041100a00740d21000200300c1c106000d4407411007603080201803500340c072450b480c3c803107051242400b0003440201c801406140e07001c2c44000d030f9114a50701e00001d01030700d140c009140f60504c9594204c103d504021801f01c00402d14824480503540700e00b03011030118450700c40c80d030003081103100c000f80741d9500554062010b034000b10340e01d8040000342044400300d110707265282010410b240d04a07150500700d074400d10081d100481c0100501007000b03e00705080c800c0e07001c12a400e01650b410b100025030410000e2000070100d45000030040c1880c0d0084050728070158103c0040c40007082d000d5018010781c2e1114a1240101d1f141903400f04e001529032815810610380d40e801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 896546627 1250 896545377 896545379
    0x907060807050d18030314010e0c0706050402030f0109080316091d0709150329090c2b0605032e0c0c21140c0c09040809041a100315 58
    0x590b0a58403181e28840385544800d00c0b008004039440c281c5280398825503001842106000c100030070b801303040c0c1003214194500d07014417000e8614241554001500401c001826480724400a0325069503214050303101d500788040380040c8000b10018600c82c0c0c0c2103880c030529400c9140c90459440d2880d00030401c2c010b05201d00c04401002c801c0d000c2d82c1c494410b0170481c104681325481124408804145c80001075202d42d101e01140c2c0d00140c1c811082c2d2400100d8040d44440c0400041c01e800008001c0300c10440c0100d04040740b8603c2480300c000744021071901200c0711207018040e80181920740a00d40c004c0c031a070503840c0001a5000304400400e60000428140d08400c42e1061024050503411042001107089034080414600c9070071010043d2185544600c003078100fa0301606c004014000c01c92400014481c1b41c04840b00812521a1690100d55158040c0d42da803400c035840d4041c8903101a042840d020b1a00c101000c80c0401840d40746007103550b020030098000c0d00300d0030780780c5000422544040401c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 896547877 1250 896546627 896546641
    0x1d061003020102100207030e0d06020a0e0303070210030c0210110316050c0a0201030c0e0603010b1b030408070603110d23100f0e0601020f15071b0f0318171509070608 73
    0x400707094424440c1ca032400d406142300e000070380003045040e4280e03200d942c0080c44c008007542141014031036101c190051420300c0035940000c2c9192711008030000034991074080012842d4401d02014210440d13550003000f21000c580200e000c19041210008540502c40c031322702404501032410f680c1a1041d10005229460f00c0ea401100909142000300f82030000308010500690345034405107003e44405c0d020b8035200c00d4800140c09002445420602032504104000c0c000100c02040b600b003901d080d810003241c1021049003c0003035100e070140c000181480d1900c86100c9460003e8400308066603001c28032280e8a0301100c2e65070140341c0740310f00004000542000c01660a2180442c0e03444281401030300c0c8195403c255081c1089919070005221501e01010419142c1d040210300b00c041008980300107a5030307040d9030717603580c40418254058144025200101050100c00e01d003c1c001e041c010b144142c00341040350340584d0701c00701c1c11000f041090103680002c00c24a00050b4450032207095030f0b1081c646440b404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 896549127 1250 896547877 896547881
    0x6080a181704080f1b0d050d0311040b120411060f070201030b040e010e06070f030911091003060204082a1507030509030703080301060f1e211d06100302010210 70
    0x72445a00058051000280303003030042c040e02c070050000b02d014004107000c4460b55400d400022410610030301c20140341c01e0100d107001078400112202402c0001c0c0701c0c1c640089407505800713241d0010b0004807000800103e0744d43c01c07108550290703220701c141e40e8841c4820700821000c0d02407400a40f4103054107208900256119401182c1d0005001c0c0001800c820004c45442c207445100013038122544c00441804511684905984c80c020321524040059a0142c2c0e41d081c88030300e01c640814454141400819122100030044000841e4001811542d9a607038000701030715452aa200454510011104040d1441070404440b0b45800e000f4002e51080482c00701581035900710683c141c0c01c20038140000711080e2800c1184401a5010741c001d503850358034042000b0302001c1641590801c0200040c45c00d0680342505441d083c40c00c6d040d040c4503441880001484d100042c54003c6419581c0c1400d110011090001d4130004641e01c0442c2614626614074410905440c99448000d0059010404c0340016541c59 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 896550377 1250 896549127 896549153
    0x3160308090a3518090a0b060a03051f150905010e0a12080d0204091a030a020f131e050601030608030307020d080a110a020609070f060e04020c120403050706080a18 72
    0x15012040d03520f0140f000110b11608512800d05031800154400101413400e09003a680c02100302c10f09002801540020a0450140118202c01e07d17848001141c0c841424084c41c0119218001070030905640e2610006143c14180b22010041406070300c02250341e500c554582c484010001d40208401071500483d94030300251740c0002e652420f8107200c100301c0075a07140000e100078101c60b80c02080740d4003180b08005020304a008014841c1e4800181080161620116070302a080c04036070107841101180c04180180c0541440049040600c010036501e000385070f8890340c0134010a9908101c2c83c1d4440b240c903030342d070300c403c2d40c1034005a80070031041d10b6820720031140c40341c0c8115400804200d2a44283d524600c0b07400c600346034000358000e5410442401c00c00c100f02c0e4003c0c0300710350b00b2105030b03494088060030790200d050015015a400180400440c001049048101040d240c0650b5807550f60317040c10340e03d54402d0301560f80005c5d02d41c8045041c041c8203019403c007000547d20181120703885503452400010907 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 896551627 1250 896550377 896550443
    0x1b050303011503060b07050c0f040911040b040b040906061d010605030a05090a082b0b01200102070f05031309050106050405040b0103090c120b090a050a0209040f0503160308090a 78
    0x12541d000c10001a0440580640341c811f20082c04c8489841040003001114030503202c5c092032908610300c010400b10700e44003a0b5400c056400142c040e600a000c100034141c0b0300080341d00b0a007007214460800029601c04421100a200d48a401040c152045c5900d02400e20070107001074400e001042c200362260b072066802008203002c4525100c00350f9542d1815030423038190302151010350b4030300d07910f286002500300c40c0c605454071080110304516400a03211710680c4014001903440300319050020035003541210042600500f61400c4e00206203000c036545e40c8000d544107040e64180c2400185903d840c052181a90704070b440e100e003000d041406201c0184007500d5641e0415499102000c080303001030100310701419140c60b26402c0794059041c14000001e020b09500c150750b10049030600400c00224600b00c200381d040f00d06102d1500c441c108200741034050380020304540070000700850f000c0316903000005414481d8454519581c0c8452070f440c7c0b21081a2000b5141c0c8a500c20003400c002c0c0306007a80005442 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 896552877 1250 896551627 896551631
    0xc0901150519030515100942120b033307020d030608150402300c0a05100806011220040e010506040b04120c0513050105011b050303011503 61
    0x10102e5440003a140c0d5040c1d0401180da0781e0103000c6074020404240d111814195281d42c000a0454001014801030b4030400d455154504070075011014030b00380980c5a0001e91042c01907105110140c2920a02042051030100703510a01c90700800549000340c0140e0580100a40401100c1c468100441594203691082000d00e0b0b030824001000f841400d980039000e80e50080c0a0280b003103c0103421070300c0740d8002105941c001c980484c0c03042545103807941d0160f415035a0075180850404840c08901042c00c00d10038003030f0b0180600c207a202e000586403028050844180381c10070390b80e605004070141c8800f03040d000281860005515540a496405660382610100198100e180d25040c1002d00000000c0884d60034001000c000c40508910703003a0141c070302140c0480c601494168165220705c5139100b81302c5019112a00f07201400041c207900c0b0002c1c00f014280078408900140d491004200c240222804503000c00c0441411034058223105d201694400010f515590034018a08403440e058550001015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 896554127 1250 896552877 896552887
    0x905190504330e060a08100c031b171b030a090309050a0f030209010801270302030d02030a15060206150f03120a0f11161206240e0105030c09011505 65
    0x901d050310000320710740088a800b045641000754502d0180005004c2d00c1c03280c001c24806100211001c0781400004d00203200000d480e2901d09030a40150041504004141e03555001034100315400c111412048552640e07401141e9803000007c1d814441000e003038018051003440050031480c0d0035408500203c0c080d041c00012690340e400020380346a0160402d11030b03400b48071420401c604214003298090b049050003070040104a1008003401c501010300800300600f00d074804800d041c020b00880b01ea0020b840801d56036458210a128094038035140002c924601103180027030440e102007000c6000d83c480a482c840400c1c4c940082000d0fa040141a0315410300400540326207000c0150010013003c0b1561b218010785201c8040091701c4000913920801c1e440e000503040c0084442c40c404004165a180100d1002c00301741c03030030228010030752801c122000032400d03010306c0d449040c100c25600498921500c01181c1340c0e200c609158407140700404080d041041040140590102c400e1404561082e901d8014144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 896555377 1250 896554127 896554181
    0x8070605070c14100522020636030d030c02060a152310030504031e02031201080708100612170d1803140a020615060f12070905190504 59
    0x2c800c046500841d540c0c494031130300a1401c80d9001c0c0c55400000785045a00341054a03a598910422004000307110341c0c00080d041c1d0000704444510041003011112460f022038001d149402808908004140309128044901084501c01e00440501001c194080c20703807625550f643c40041d0555580389105524011800700e00a9400303903c658a104000b06005e01d242c11314401d114041143c00b9410781007504220801012a03041100b0888d51408030001e003410360080c140403030030750145501008100102d9400000d07450400a507a505136500300c010743d0708d0120300050345012120759109084c51408000b00038004541c1400300308060491024010749016602c00c3c040085071404072258652444082503581032603800305500c0004003400104a181c01c2141402a542d002d0050810008444080403548252502d005407007074085000e61b2561201d860360306c4080c40090449111000401c00d4500142501c0d009031607450000302421a07800142c108010f201c05400e01000038680e854a2140880781 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 896556627 1250 896555377 896555393
    0x1201080714100f2a2a0605030609040204022713060807090216021003050115031a0f040b0d0b01090e0109080d0e0a0c030b0f01080105091e0c03010203100f09020708070605070c 77
    0x8080d1081c081c1200d42c598000407840a018040c05c0c01c500c0e4144030380e041c090300e034105044070380011080702e240380b40e580d540c40000c01070310039150a085104502113405038503c4010f0700380e00c0445021140803c2624200d0340041c1203803402c0c4100c1c10698881c0c5400c02c203850295000380b07010702c0304110290020007141c0128502030907410385c0c0030001760341e100100410302c03040300441e0141d05586006e1091039100d40d00c003000e000100000328440c40c10540b401a5640d6030707030702601c0d4a4802a00e094449a154140300113208000d02c20708a8090801c4001c980c141410321845a503650b01101460400d001501c520006015a1030000560702c600d458403804514080d28080040d4401c2540c103500c5d242c4900c0c0350282c0681a88002400da040c2814007413848000304914005c0c43e450902c1c03c0748030f0840b410b1145007540740284507801d94400024020032880120b072400540351800070b000051030307550580c00103d10a07001c016056000601012000945035045190400c0c101e01c1c2c030b40c481002903111140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 896557877 1250 896556627 896556707
    0xc0d08130e100f0e0103080d0509011d01020901020105100b04030b1005220e16150c15090209070203030405060c1c060608160809070603111201080714100f 68
    0x1ca150b42c400c0007004141514025580913140e80a008200c3d0b52450740c4500d894020409895100c603203401c0024500b440942c0803002c84040b01c211800a81c40e0100307042d000b5841141303064015401c2070300081c660b09400751240b00700c440752041645840e03d5030725812200300014103032454407446504006115900c59140d000030701188212400042c1455201004440160314413200030740003601034950a21040c0d0508088540391007003803540b848240403c41d184120820010112410601910407001035644802d0001d4425202d0206946032072000380ea490108890044c03c0790b01400c0058040e0348404058000e4000554140079a00c4400c4d4240307080d25800e0300101c00203000c03c01000401e000c0c3c040ca2601968503410800810b090506e0b40030344850b0b50380258001d041d1103000d000e8001b4211001c4645030720796003c15803600e51311782d4246901c890403403040e07501a416982d2142140d00e00007902d8407074100f06441390314030483c0145064a4040303141c0d9024a0346140380c442c110315148800200c01c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 896559127 1250 896557877 896557891
    0x50f01170f010908030a0614010210021303051e0f030f0a0c1406040302010510090207030504090902150d06030c240c110a0f051002070501050a0c11062a0c0d08130e 72
    0xa4172490314a204030115503d5078001e1192203c50050903102d80d0700484d0701c00030110010700240c1c3d00e0350290344011161045602c01000c2d48100616564114013150030104c540c0d22800036200c0d02d035030b400660f035564003032414075030000201080440d001034001c51800080501c983c3e00402d05403165030174203040050445042e00588d4507102004490079924a518016017900a421410502a500c0007005d501440c0550010f0b0b6580700030840a642d5040801280981ca148405903a42c00525003940544154441202c14801c241c6004c96000c1001e01d8041c1c0250419280c60565a5030744401c540034800c944042c0c911910541035204144c40d1881030501510b84220f12107242841d200a00c201c1c1c0617840841c2085400850050140e40e9010007100e440c150140b40c050310383e81003420043c07424481c0e00380d50741c0e0003080051601e5903544421503944e403c18a49003801c40d2000210325482c0c448242c032586a034032141c00000302001507c010040d11000204e07039046155a912500940d18400c03050f1100c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 896560377 1250 896559127 896559143
    0x10020703050a030e072702190f0e0d020f090411031b01020c0607030c140319090326030a0905011b03050f0a090c05101803080913050f01170f0109 64
    0x3103142d2075054003070055060940401801d019142c2045190f041c0b0481c003842c0d9055501070158003007160680c0680700032000d00e5422030214042c07018081e005035030341e584c2140445c00d4040a1080d9290405071840c81e950040d2a905180700214100101b000c4020411600c180c0d001813541440d440c200080140b100415040c0d0450850303002c0060b01d0545000c1c0514850f203810400390300025800700325500415400604500c2d500b0301c981803141140185c5a01404e040c40b071410301d0400c298804500f60480340201d08003400ca5101003a04814011260101d0055013002c001103441c5a0490384041031312030203100009041c3d8880f801005008000b9146100000c0e1070381c0501c0038031403103007002d9600f020054400304541e00060350380300c8602003540f02d10b07031003202c0181d46808054094181404148000380c82880d50329160325041420340c02400c40715000303484008490800e0709492240900808100800301496840c03c01403494a005000200225000e0451310003450202400360480c0c0d10710a40300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 896561627 1250 896560377 896560387
    0x4030c031b1115040b090d03090e0c0301090506030a030c1412120105040c0c11010c02011407060e24010306050c0705060115020c0103051e102d2909031002070305 71
    0x40141c2c070050900f9211002100300400c02c08030410b4011a280140103494103050004241000d486400381c40d88040b51600c0900c00700040017075820015810396010403401c10054603440b080c540d0320840c0b141c008001c03884204014002c9000003054020440402040310305c05100c1c1c240c81500b64100e16101d03130700781c0c00c00801888a40f40034020100b6421103407a280c1802c24940d1a50300e5422046038259060189444180f420f5920402e01a50003403000f951041e5150f03d0fa00d84032000f0078510b5030784101801500700040e103c40075071010401086224001d880c0b0303a421a1034000c02808050b26402a05c90108014800100b050090038000c00f5020100055900d000c4400f0f410100e0a0b9240c60406251000304082c02800c0c0c6054041c96844d1400c054161742e81c9811080301c44281c0e04074940c010000103000320101c0140d0034a02c60140401a05100b45d961040c15640c2e000304081e840d200c500070130004000f100009400351400c0c442c01400c0394213485081011100300d034003501041c0c001880001e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 896562877 1250 896561627 896561629
    0x3030a140d0e010e060f060a12030509181e160305130c0f150903020927011802150703020303012c070e12121902070302030d090e070801050904030c031b11 68
    0x105c6103900c481d040075080301919040c400900f9001403405050002e04880300b450044c54800c1d02590300402002e842c110f00d001c0140c000040f0000120f800307141110151010400d00719a00103124002c1264070f80b51800c1c03117800e030815805820003c0146030308003110800440400c0d18084440000c02740038280d200c03454142307a09020070345020b021030014050703410020001a1610345107242d201107901c00d40001c00c01c002030b10151180b140c001e032000c07960a0229001960000f021003070001c0c0d208580c6175924801314220052a03024105015026070030a100400040c0150070062000000c0720f045061141842c09d40a6401c81050300c0c2d00c1c0014881d2074404000b81813041c16130741d5040b175603401400d201c3c00341a40080d1b01d1081c60510765803071103010b0640d9046802005448061036004090300e42440007200001c00180707840c401c05c03a103c0c00d100046050b560184007810305031080604404447c1e41d0b181c805440322050040c08400304165040501d5407902008e650b441c459104008184540c10b50740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 896564127 1250 896562877 896562883
    0x908070804230a0b03041a010b03160813060507020a06111b0a02101202090406090b0f010f0905060f0d14010305010e0111090f04180b060102010f0b03030a140d0e010e 73
    0x15414800710b00d0084901c0c0d650310084403000301d0703101545060782d035075aa00e0044c41894a0890391700d02c0903600000403039140000d202a5100e840c2e0b032441003c0c1461034401c1120948c40507104642d05070880c0c1401000b0800c917400c031640c041b00390b00440c0c91905040d580d0400715400090035041400300071074a4520040c1e4041400c0b18103140070001c0c076044080f9000600400144003100c028001b2079180300c1c1d00110550180d504e0800020810040265a01400303000f92042c030003080e11030107490a05087d01d41c068035441c66030002c241e035442c0c901c9007004203200c403030340c030040c01505180018815035040b0741c0c41d0b00404152a02c1c805c40e01c001545185403446c29901d19806103802d69060848000111001c0c9090300d0b4498030071070300c4040c0c03e4000f03404200240102c80c0d040040b4a801c040c000305001c1e48031403c60041a0a81c001c021074505980e49004035490b600116903d5003042040b902554401c804070350181404d10380c0d1510300070401c1101c104450710800e442c107840c0d454560903170031840c040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 896565377 1250 896564127 896564159
    0x2a1707050c060309100e0c1c0b060604030f1104140117063304090803270606090406020c010e1f1a030304150302190e1003090305090d060908070804 65
    0x30744005045003011010709440e0040d4880007071716550741c1c025840d0384010803c10000040c0d80034011380c0c0c400c1002c01100d149050110400e640491001d0301180540c28110110340880360028003154611300300c0da41d244800c030386030b0080d59801074454441840c100468418180207000e080602c50030540144981c9042c4807000309100301040c0a501403c0001450b840a042075a42d01c450740321240401900041c01007000d42d102414010003c0304225401040e9482000c55003c5400c10156500b8070603c0780c1d60b10b21088070b480d41c202c00040e02250008080b60013800b0122285000401c0c00e100040d905403804c2c3e030f04480c0d0080c000c0d03a4070680006680c83d02c60025101104070520f1031186048000c00da0364401c6110b4610401f19801d224440c01c1d100350f05580e65860000c05480061b5008180185030380310707004805220703100c0545600c00c0c29000e0311414100a038076840e55800c0200440800c181c2c80c1c1210350a540d0380e0307281c1540c613001911000003000d40e43c0c403076403945881d6030902d00f00392829444 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 896566627 1250 896565377 896565379
    0x1b0d0c2310021b040e19050309120109020a23030f010203011d060d030c0302160602031306020c210f100515120307080315102304062a1707050c 63
    0x10303011680903400b6010f48001c01c1c4252008101d864000118a10f0440d01c03220340109410120303054000c0000100081a9860040329064074030b14420345001d080f618982402903000d280c0c1001088400d42c000c03411208001550511102001c441011a0501403400500d9815035070000041c020240801c0420700c2c440700c0841c80c80c6a42c502a408112245003458000d01403110a0012108061007000380440076501c20f41c19281840d5103150181d034940000890400000f044030011803054800a0703d40f040500040c214240c0d0f0400340c600302525900b10743c00a01502903041c80c0300410344200960303402109002e0700082c00345480c148400100d0510302030b86204602910520700c8451000007603400e0306822031455641e9440340c034002e0150404060640d600201041410040d041d001545d42d001c0007a1400c4501c07200101c40f00051061059014000c08030300c03010070300303003c0014070f00021000c000f08900c80210840541c8552085440014912410507800a080c3d000c000c400c0c4030304c2c0c1550304 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 896567877 1250 896566627 896566633
    0x90d0b01060f030e06010e1302030312060a0509190f180c0e061c2004110c1002040b0a030f0f14011403071d09071503090506091b0d0c231002 62
    0x50f5a400458903644103101e45e8001c42149008200599503c403000288d40d5070003400c0380ea030313210380050800074000b045071241e01c07840c484c8000080505203241158400d6183c06c0702690b002040700b0780300004141888441e225140d81c4c41041300c0003046000740c0c28155019220603219030386011155020382d5401002d903401201090b00a0350522014800710308001c3e8003440e400c0450b200c4280d07111048041094240d0302078142050348030661905402442030202c04d80a8401c00d080700009201a84a1031043c0c242c0c100e42040a0441c65210f68011500c03040c50f40d4021842011290300c1d00250f484c0f8200c5594078805440c01000181041c98000214074000e40180c502c9520708620341000d03040800c402012002c0c8400001c61114007481404080c1508000c455a042801c9400030000e0040c0c100c100d40034454240841c00d40b00c00020500e11070f505082e2043e41c0c1c04000010b20024010300441164401c60070f4002140752280e401c444c402c2c103000c80554460300308104d020020801d0a0081e0031040d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 896569127 1250 896567877 896567891
    0xf1e06050102060705030c0d0213030302150121030c06020f0a090905090307020409052b09050a030203061b0f0a020a0b130c05040b030a1403040806010b130911090d0b01060f03 77
    0x1076000304902d54440e100e800c05c2c50300c951712125800d0303045c0319034103007411001d200103040c601c17055000c0031903010707a4025403c9696403c4183e010245411080c051306241c60248900c804503803141e4003031400320074441e1501c80d01e4010306035141c5050360016039106590803008110b80e405c040e40101d00c8001407600e50310902050504900040c1c503031117002c0003c1d00981d1114540c80602c4010000c0c80000c00c0080c48001c1d0400a0348000840c1c7c070b01c1002d000700007e0360741d1800511031406602c000c0a480c0c0080141c2102d407504011003081c0340075110350070309400b03052112892240c1d107807004d001e4064064002c0e0461264614152400100041020784000445005a40461003003140380d8295282035a000034018003290000349040512080204a8000486c8045aa14002c00a40100c40d00030003100c080c0c0c1d80307488114445000e454420700071841d0000d0100102d50b9a500300b100d0840e9000101480c096000e0041080e602581906a845101081c0100000f650244801982e640c07145000c000300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 896570377 1250 896569127 896569129
    0x702090901061712120c070b0702070504050c120a1503120801180509100c051912050604090206120402041b0810080615220207151802010c061d010f1e0605 68
    0xc2c0520b40504074017030380840004401c0b91541d02200d405581107502031000b4503100700001d5444126003c2d40740030340c0c14100070440d0103c0c6041940d49080f0b9261048003071303a07564410640140003800100a4201c90110000007180403071410032406100e683e1400342a60600c003540c03039460400c21600712040d144c00c0411081d61008184803880c4e0288060100d8490ba00860842d400d0042140c0c0f482c80c904080c1052440d9500240038403100945198240b2940ea115801c0004444031548060f40048080100c00003c006d81c60101354407501c000c3c00001c0d100b2101d00e03d55041e003451840000410105801e1240e050004506070700100302140040049180c03200211000740800c680143c042c2c2a0074141d0300b4030741601291580021a8840e0464a0302000d003000310100d1202c0004105543c82c20600306040c3c1002e4108203010303a0180c48400d03504e0299500c250050808110a0303955079492011600b0f00c0000707000307100c8e080e00003080202d81640c40c4040d601d1500c0d581c00d01280120300d49a010015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 896571627 1250 896570377 896570413
    0x2a03040e04080d110301080705010e0d030f1b0b07030f0e060106020d031d01020309010c14070b130305090310023a0203060d050a0c0311090f04080f07020909010617 72
    0x407140c0c1c0070418640ba95030740155000a0f000740560032000303031004030000c90150800541c2e82d00700c071000d1782d5515800c003881c0b0511a414801c0314000c2d000a00c01901140410f018920791203600e2046034074610355448035111151250b44c251145400a51100000e9160030740074010560501401005800c0d82e51515001955450031440fa000038191190011101c0c01454030540c544104654025541e80c500520502d00a01c140d20a4602085c045440141844544020748000a52020402c03205442d9820b10301101d1001d080c04508101741080030003130a8400307001d0300100c0300302007001580324101082054074034100c0e151f440020f40214a94010700c0e078031007014200c1c2c0104068005a0748d89441010840b880d0264001511520898800e101003028168240044034014414012025540f0041008140d82507805000300e82c641e4010a01017450a002003011280d840f620501d850516808590885c50888640c3c110b40d56500c1e0030800d9001e034110b84034070300c00000090700c605c801030395044007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 896572877 1250 896571627 896571631
    0xc031401050925090305011503121403011211061c050a0c050723030705060f0703050402010e1905040f0218090405101806020d0b03121608031302062a03040e 69
    0xb141100002c80450340c001c0c504c2c0006160040c00900010322011504c01c1d0380304103444100c400c00f259034a003030406485a05840302044405412514591900c45401d030201c4407400181c0f04008a402d511007182d40b05c6c0020800a1090f01d40241d80c10681f0743d61908540f4001c2420541e40d04101c442241103a11108030b031241e55010001d00e24147d841003200b00b504820710701c004964400028000c050000002d0794a201c2ea006600803829030f40c4040c401c405403101590001d01050b4841460b440d18503249a404540801401c10700050683d200c0000c6e041c1e512620311400f8081d80014401c3d8600d9140501210216055440d5045414140c1d00d02d55500000265545402c0d542c104003805114410079441c0d403180c0001095484116581c4c00c40010161440184d20a1140103d48016082064141c80d040004000e0040704c0302055200d200c1d132a40f00038442114401030000400059951170050304c40c0340c05521007820008410f209203112841341c020054400c1e070080c08200b01c107140107c6c20a03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 896574127 1250 896572877 896572921
    0xb0103022a0a0b0103050622020a05040509011103010f08100c050f0a021504210c05120f07050703140d0809031e2703101103010e070c05010c0314010509 67
    0x1e00c4026515489604280440038003c2c0070020341c1c80000184403000404030700501030045d4a00c0c1202801c005032140d03400d01c2c0c10094018040742010410b61030542d1280e64002d14100021580c00e071440080b005940c0260000c50031041c10b10418002034004200040078034004050400c085121740c40054000c3c01940190442d41d1400909040700903c00d1013a810b41d482c10520b42403139030925140c1118404030a09024114900f1410400c51062050000e1445070b60400e002d400c010448a002c05034940c4080300c50207450b401000090001901008968015405a40c001441480070820141440c42c418001410000d450045c03104158000c03086501108074010050590391400d40200540e000702840792107482c1160208418404109000c0400e080c4104c0685441c1c120320784d815011174030007000002e103005080c001480f201020213007041c0c003c000342c00c04513900160b0390740d41c030300791035080d210403002a0325100c158907000c1c490802c440c0584801ca60b20309440c0b07043c0c20030124000e60701a500b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 896575377 1250 896574127 896574187
    0x14060409030903050601030804090c0e4905010507050f1603030f091110020a0c050d02030f06090102130b04080d0311090a0306140f0f0f0601031b080601030b010302 72
    0x1030400c050040501400560380801544c04960b900d0825081d01e81003841508241414002d030403c1091160180c0074510800602840c0401d40840d403150400d403803141c40714250034204e403142c026007000826007200740c40051102e0500041da85000703425a01c0207005030081c0074041c0b010074049180c62043e42d10803040018914001140f82c00e04401800408400500d03e524004901e03060114403011050b08a200b03640e018030700140d10404a9540da0300110240000c1c1891400b80150718011603d50a1b19000030200c40a002101b4041801d0240079600c416260394005101901884610040f4005000104105041601d000c0669403502044074401041581d101c040c10012100705064030303640c0402500485c82d5913107901d0184028a52403040341803064074034000592050703024a141d03100d8004036903500070980303c1d081c004100303c00c041c14050500d41c880e02034103540c0004e484402101d00080d9601d1555041050000d0b041b6502c590400d810140104140201c460300d81c080d580d0000140b9a00d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 896576627 1250 896575377 896575391
    0x709030f0302010f1a0108010506030c040e060a09020a0c0c06092d080322090203040f0209151c0b06030d05041403030d181e050c0f030c03010528140604 67
    0x422401004d043d4840c8000360f24040300c3d180a0100b45216044141d401e80b1083c0302c1c1d0362100100401800b04440e040e0308808108010300c41d0b05560302c08a908584040c1001003c25266040c0034180e80100c21180001403240d0034a50502c0150b001c00c1d0014101030902c00809402c010343c020140c1c0c40007003100c2d1041c40082194802c01030040718100100041e00a03a611001100d030f00c00c50f0540c40700c01d0a02100d0300300c0c20201d00714003a40308032800380c1c2e4049911880509036a0a02100080c01804903211028000c0d10661725168440813080310b100c4006c811250080524145032810000740900d0b00941c070400741c6000280d08071044400fa19460305100c1100300c1c450b00083e207941f1031a00d1020302a81040007402801c000402c940d25242d201d086442e21848020a00b101c0c3c20030051310162240c0c1c400c000d42030003410211000c8511190103010b03140131801c81d00100382911402e4a980016103844807607500301d10095860b00b501608045024440070307845070074041200c1c10180c0050700c142d94560b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 896577877 1250 896576627 896576633
    0xa030921110706090b07060b060d091505130507060e0f0a0f0807062309040608010e070e0a0903080c0c031b010e010b0d050303070c11060721080709030f 67
    0xc5500040c4881410840081080c0d40000305081c1c841c0c00c00d5080e80c89032a101260090181c928403045d962075005003410000c190b1202c0d0003030281c0d914144e0b0441d004014021401c4114010800114051130441c008030f40314010050440705c000708105000700c1c045044000095010990004071942d600d00071060717030740010005030302e101c050b1100c580c0008502d000144281408440104861903401030b1525140d440006072050881d041c3e5070310600a0310349198008a516501900c17140e0700251001071182d46441d0380d00d0868075122410380c220f912001d0304100d000050801c8031703403000080302e0500142002c2c6d5005008008050719080c2c4501c808554a82c6000041066170700c03007076890160701c0c0e46800e4480600d0003411050303240e811650030043c1c0b0810504016981002040c1d0020040d031031580e41c00030440305040c0056041718082e01c5490202e02c95902d04000d0a038080c094140708070200b45e0000d800803002d030a014810b041c892480200500c05400c0300c0d601e800c41c3d0b00700b41d50303a802d0503042c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 896579127 1250 896577877 896577893
    0x10303120b041d0106031101091503020a021e03092b060203041b0e0403020c01050304080f03090a02031015051512091c05030a15050306180a020612041509080a0309 72
    0x800e10103881000141e43c41c100a00541001040300d0280c0502412240d00398011140d0151b14050300c041182480a0324007014800c6c0e0060450080502c180d83c0100c000b00941e05201482ca01d80f0304145c3d00101b848501841c1200d5200780c0c40301140e0000c501c500d141c21211401400d044006000903601000140900001440b808603d200480313209051070344071202c0c1c185c0b000e0b00791015001072089028069440d40250122800345030000300075800d00f840040230548541c030041070a43c06004e501c90400058504020406030a4046c590129003120050303c2c9c04128501640114403c4034191014030480c00c3c40c100300e9240c1050050108816030b5030440030f034038111042c0c003080311000036440b600c048540d01101850282d10391890900001d01d050410303480400c1c3e18010140e1580101000c500380c0e211100b094039034220b045040d25141d95403a00098101e40003005d0404001425900704400c0102c29901e150075032418200c01c000c0704149440fa240b4500500c1026800d040d03490703006400344400c0c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 896580377 1250 896579127 896579141
    0xf030c090b03041202060a361202031b031303080a09120803070e010c0209070807022b110f0c0f0604050301380d02270a020c070905010303120b04 64
    0x1821819603030300f0140b8000c081200300e803c0e82c0005010348008500b003041507008686c0d55098408141c1040295604c400c42403204040400710b0b60540c20081e0f00003d00d0a60000c82080d429070091a2254040c00e060b1054016600e402a0142c000700300095071a02028a0142601e8000f0b0245865a10307816044d5101c4800c0e030030414041e01e0240102042280c0c88000314131400d055500c9445100840005441c840c1c00001d000390b0004c0c03913800144c0d14512070f40307811f0750140d59441201c0c0b150207421203060711a0044034558008595100c101c0034500e8110007000c0c0401d1016005240340c8031600b40140c2c480308562a141e00c142c602000300070380d40c0c0c3c4841c2581e001e410001c008006800c1020081d1490192903080c8100c4445004e4100d01110504080380d4000075000d0070541043c0380a80c02c20842c0342040d03000d5084403e00242400304001c41600140c4a401400c074010303912055441618907104041d4005410309051500520000c0d620541d14070b40152800c001240e16500c000010740a4150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 896581627 1250 896580377 896580389
    0xf020a0b1b071a100b040e1305101406030c090c040605090105040312030515040c0504060c2904061a01090504020c0109080a0e0f100c022103070602030906160f030c09 73
    0x42d40c941c0b00f06070800030500d01602849120200745641c4098078250350141384100d0101083c46400034100d43d0b07100c00d03481c1c1300500c40d4090700c004070308407150b55080314004c400d07242400c0040000c10046d806d00301701b10680c9080844405425181008038003e880c812400749030100a40456512042e0b4026000c0e0303000765a00294903c80d00b800607074010010502141c9141d160b10428001c0150341c2017038800c0c00712404603a600d852605003040030541d00c1c103405400484010307550381d0b01c040000d0443e94400c2c10701c1c00040041821402c2030b0500000b61802c5c1c121410400031111400316640c1e8000d8050004c8480c150b0700542c5515030000c245004000551000e42039050001c3c011402a81c0201c1425182c00200c4948038a01c86450510090107145081003021074032a8405034090f1409070304044174080f66010144202040240761820f5400c039040845555801109018941e40e00b8800a50b00419501000760030f1108080300070000c40054942d4818141c1d00c03090000e00074401c29282008d828 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 896582733 1106 896581627 896581643
    0x5011e0c0311180a030605090f0607020102040f0608060612070302040f09150603050c191e0305060a03230a111c0f0206090a051801060f020a0b1b07 65
    0x58410380705a0001380c3c12030000000d1001e004461141841c00c0c0644030003030300c1800391403401401500c083c0c2035900500c4280100c200c0050202c049822a00c2d146680303844041c0131640921401188000c1200c4a004000286401d60000c00440e440101c805c0e00003599010100c0031a2206000700d525846440001c021152280e00116001601840c00074941380076464030440302400905814080350107140740b04800c420303040c6400449501e03130405020a1400c04006048039015003c024140c80107a00200e40107920042c19007000100881240c0a4031170509003082003044c1d4200541c891043c6074100040c208072002c00390165a031003051030801440c1c6500b0031059030001003005412001c2900001600d685031000310b2419145441d00002c15414003000808080740c62505034195400b100c201c4c00090704c161041a4490681c50502e12030010400c1814406c2c071030154003505002c = true := by decide +kernel

theorem cover : BRFrame.Cov 896402877 896582733 := by
  have h0 := BRFrame.cov_init 896402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 896402877 ≤ n) (h2 : n < 896582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
