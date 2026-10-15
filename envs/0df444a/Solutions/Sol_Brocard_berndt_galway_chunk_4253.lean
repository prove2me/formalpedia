-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4253
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:01:00.124919+00:00
-- url     : https://prove2.me/submissions/4047da14-37af-43cc-81da-f2b7d696ee7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 764748201 ≤ n < 764928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 764749451 1250 764748201 764748217
    0xa0c050106090513060b042d06030b04121211090f18130b090a021008100b07080403050c101d01050f13060801080a0804060f051b070f1a0a0c230102 65
    0x424003081b1300007400c01080302d001d00a04a02c0c8030002c00c8a8a000c1c5400341480c0007411031441c0001c0964580d125460040c500b100d04035540342240030007a1800360010543c850207000780b01d081c440c841e44460804c8450103190400782c0181c00c682d694030819900c0c3c400c00c10b020f600d4008404d425190001041c520400604416144e0045e00400718482e038801007600d0350031035006040303042407200b825012035499400604509031a19041c1000c200106204001e000481c0900b040e240c955080d814901e0415240e03d0b60303144a25041d40e0540c200310340140c1c1c800008648000c0071110112044010b0343c2c6407103003100025548000185e01048044409101020b072405980e03403000d541c1e00e400c0b21540e103100c03e49000e802240180710400865104003e2903400300c20519040342001c11050100000d00764042c1e11000680141000340329400084101e10700600007801181c41c100c082010100503407281a0b05e207820043e1028100e030a00041380040300140d0a86807941c008034142c0da4190b07000b5084520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 764750701 1250 764749451 764749463
    0x7080c04080a12170720010b0306011208040f14100e0a05040f181506050904031b110d0605040b0c0a09090c020c060c01020309100207050c0d060f020c0f120309030a0c050106090513 79
    0x10003034031600414408d0000d440c40c064014402139003404190203800000d00c4080b6405002040007040c01030740f407000b01c0004c14412036602a42c2c0000300c200040082810740c2c2c030301000f103120f480403059902c001055017122002d46c1d00041031182d42e40039401911600769000d90700080e4202034401c00001c5201c50000208000040050a480f0b1040107902e003004c0e02c0c00390006d48008025050100100f401e40c148920441c03d5015428501e00421480c0454110035200c0d02da54104010520100745540c603448000713151003034a00018202c018164070b2480c043c000100d0798401622a20302c1c0200610070099030f009042580742e400d2802594080e50040700c54135002c1c028016001d01c61003090007500e03e0542c1c04405000c03075aa0b002d0a00042d80d151010a6803440e44034201110a41c0e40c52000303041d80814200075142074140065080e10f40001c0c2d9107030b056140c070100104080030340c2c040140da01c1060f080c030f0039080c05001d501b0070354050310310380d0040f0550728906418440c1d507403c50104003440a104803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 764751951 1250 764750701 764750747
    0x80d0609060602033001060c02030f070b121f1818080403260f1305030d0504030f03020304080d031b11060a0b180403030507080c04080a121707 63
    0x4442060700c2440c4600070140c0d00c20700c03402e10300200c0c0c0141e03011400446000041c80079607a5450138503080080c0d01c03450100b141d00c4c040100f0b43c2814025280f02941003801000c44900d018a007140c03510910b8680d07802e440150000ca84001caa54408000f8589500d1007240d91603115485a035040301020310f8150002d02d071000c81510380e008011514040c580100c0032900301482d40c4c881d4000c0c0101c506100e40000307000c0e20301801170390358400500b502600403020b154540d01d5119400c03200550b19040b4900c294004040c001d1900d9000c1c040b10180c0c0c1d40000c0f11500c90b41a0300e4241d02e14003071a0404290340c010b200401100941c1544840401417064206d00244451680b0039034845030350024440f8030b500a0f10010303410846580121940c00400350554090103a102611a042e040030359003240082d03150f0301403021a03907000c1c544039000a6003426032441c040c41d0881a80e81e40107143c40c000c0220300d81c0641103c0040c05a804542d00e003a0498110b40c0600d400c207402800071160907910040c8400d80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 764753201 1250 764751951 764751959
    0x2b060203180118080f0c010501080f1002090a0b0c0316050c0901050607030f0f050c1c03063008190e1c0b01050f0d021504180b0603070305070318080d06 67
    0x5009505803541d403040c2284049032a6144e03400c0703c1d4803003014081851020070824201130803d1007824002c06017400070380007201c03000401609040d84408444030f42030050200c480300da502c01038810110b4000d0300703083d0359443c0c801078860f045003d41c0c5181881502c960050703200740040400c0c0c01d01e19840895088009030f0302c40081080398021950301800003002c40d0301000380c80b409406080000801814182c4c20b2840c0c0d500c00d00e1030a8082c83d0545c8942c11040c140c060340942600502002c1c04006000440c04000240c03452107580414911040030354840342d45005001e1940102c81200d1000500003211501008001e81510351840206026600b010000401c0001081c83e12480036071102d0742209a910f054100714007813001304100ea500c0350800c011100140d5510303520f1601c0003480d050541c0ca4a140242a002d42900c1035143c201c11401c201c1054450f9560b1021a42c2c880c240341800a03990305d80d28002c80091001d824428011051444a44140107403040681905880404240726840d19 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 764754451 1250 764753201 764753203
    0xa0b090709020c060f04060b0a060519020706020a0f0309030609051e03030c09010c14070602060901110a05032a0c100510062003070606090222030309052b06020318 72
    0xf40b804030701103940000000c591940101400c0e00c0e000f90044c000400d41251003400035442c1d070125440280440d50004149100b81b800894203000c3c8000b6002034070301240361080182d219026032800400540904015408240c000c8800c4406150803000c1001098000c0c0342055440003c401a4a800128061310104030807000088070711400180710780c5801c24064600559010080e58411207034048002083c0744240300400100d0010181d5034000e25440c02c00100c00c600315a002c0350000440b000400102c04c02d02e410034112074004984000c0301c80349000c0c10907600300480d403a0b002c501002c00300055410b00c1a070009003480c6500c014183c10030103501ca400100004003042c2c030030300d4041018036080382100d4229051000407244030400796450702085a944c64100c5003a42c2180c04619800b06200104503171110b0b010440c4101543c4000689007503440281c83e103052031042500c5803074809201e03687c07084180076800b5010203502c80d44065512500e0800060340084909205030b11a07004d4480203000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 764755701 1250 764754451 764754457
    0xa12140c031606051f14210105182d1c05030108120405150f0708041520070504051314250b07030f2a061104180209030f0a0b09070902 59
    0x4030881c8002c00241703022202e4806d00402c42806610604010002d41d6541404482c1001c103014180009441d29000400c100c50103400ca60315041d6920801d03540034a040d1030f400030251802035000e68801072140207130461500c2964120459000c1c005030b400501d80d50480080c50580385008141c0c0e0080d6050b4140115a0049100b142d601c4069502817420080022000b004020713901d00b46c1030318240040e01e402d6860360040d0300c029000406407841400069120398402005e4410340840d942002c0016055581e415141c0141d9204541e146c012956205911440c01621540049640f030700d07005c405161600c503880e80c204050000c07003403801c9801d0108010304040c16910015191801c106a54070120b80242d40b1003254014896800e4403d014019600301c502a60070000c0a03859556026140c0442501d80a10004400701c205000c2808144a400c0c940500154a0940180c50740c0101002914181d68028120054003560940e1024000d0001c0100c1c4140c542504072001c1650b1200148120700c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 764756951 1250 764755701 764755741
    0xb0d02061207020f12090f1513050102240a0b030f1002131d040b15091501031118060f071b0807210f150204080109030e030a12140c03160605 62
    0x2006c1000d0324003403500700303030141e0f002e1006824041032201c038001800c807950101c1d1035100101d1192004000c1d641c0d0410002456403c07004421f0807000c01c4060810841030050111484d1640b03c03203920ba1282c50400c40103540e56a001c045404104240c05e4440084d48072103881640e0801b030140110700314002246070001009100740020603071b9070316100c521003c88060480d441401c031050b800400e540c4e1742503c56001c2c0340080340700c180c82040400050122210f0364041d0021b01c00500c02c151210003076004141c2200d1058480350ba43e0082001689450300c11246c3c010b015040c1c0007540e0328042c0b00d4002510548000c0c03c01c48001131344a04940700020165400a01c0030f8030103100b080b0016070140c0c0b194962500c114040300280003040300c4d140a0360015005004503a40d03590030001403592208060048040036009008802c0300c0b911203842d203503041c203101d001b404001402800200701d448115090242000141c035101c0d881d84500703020b03c1d2800c4206464683c2011b01050309484600b125601c1c038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 764758201 1250 764756951 764756983
    0x1e0506010b03010e22023a2117090a02010207120b0c0a1106010b0a03150b030c0a02101107020405011d0a0b01020102070611030a111206040b0d02061207020f 69
    0xc5d0b078800000107a150f0400c6600104030310b69128440042c2c40d1206055000c1903101c451620500740800280449000040c00040140711200c1000101d9440c4100051a61840d010004081c2031684252051584260444083c9000000700545050003140840356107200741e00340d8888599030421540003a0422002609202840b404190592200e4009103203d003d00d040502c680034001c04258140f8000b6440812131500014030103000729810302c075000e051103035400541450b82c244180c85106000c000c000f590420400140890310074000c104800241103060802d000c0501c4c2a0010149504025000c0380240d0600300003045c82034681c14006101d424141560049a44500610019100c01b5440d50f066542c20811680841e41c40e015444901c481604813039546c2c103058422070206d800b00c454a2021000c18410320f6212a00e204459400c804100e0300807607901c0d900c500160041c0e070a550029071011000500004448500d19403a1080c011602942c440341503145015846041d800d0280a02d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 764759451 1250 764758201 764758229
    0x4050c090903070c1203110a0501062117030a02190f140c063705011a04184a2425180501020c0a0b0a03091e0506010b0301 54
    0x5ca600d54030701d00398160007444c006001c201481d0816080100e40c203c2501c0700d0b5141d84081c48100c0100c0514040c01060040c44000c2c0e18141d01c0764240d5170740780b042c1100c0000e4000041100710501d50181e0b404c04a10300c0250b8070300907036038901910343d028410748480882c52000040403101100d1055401e000d00940181101d0b940c2d9001d804040007500d80d8800e9161070400d0840c1c088245c0e18442c048c0c02601c8280010307075504181071207002c140c0700300c40300044290030001400407814900f2850070a0400c40030218042d0740d40b1104110083c210200031801d580c4030498452000b60311084004000b002c41d6030348440041c0b40300c1140c1c0b03600e13066205045540f9007290300d03a410311881d07a440b0382c0b14501d070450740381032060394a1008030140030408410001c1c0c0c0001ea81c5040d0414000c0b1440180f50074001071806400d8203001c1002042c1c50703c00d68808106c0400e01d00b5101d03010781c125076603142d4403a20821140d0282100121004102038040d1000d2141000210b01c0e00d90007011a41a5101d245900e21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 764760701 1250 764759451 764759459
    0x3020306060d1d0d02160905010b040608090c030d0302030609090106030503040605090415060e03070e190c0302130e09010b06030c0735270d15021204050c090903070c 73
    0xd0181d400f204804100f0340c0c0301c554100300003406a0100003800d030b800707041e00110150211000041d1500107502c150f140000420602403d4800c0b1005c0380c0b42c50801c4440d0b662121001070600e0b01c0000c6058041c0121496455801d1b030660013184649400c80388100070362605424030b4201c2e000b602004145034020001801201c2c0244007030045040014404921009243c000c020311a0b140d9002c0c0001c0780d14940c02405030700e0103000200280c021107400002902c0c00419221110340d8204600404a64480d8034407100380c42501115600d0403004010a40683c0c0c1c1d4100701c0c601c542c21683c01005528001140c84640340070402c4070b000c0e448040d000d604102c0f10351581120003002c90701080310385180600c030b00c13880401c501c40d1180d140036119803180c1354400d40c40c2014040403a0f80307000c4440d40140b03c14024541d0390340e5208200e035400100d40000807609800e51b0000f4410300000b802007030510410001004400200e22852410507252081da0f0b40316000701513640d00800000922103130321424188 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 764761951 1250 764760701 764760727
    0x2060105040b120f06010306140708041b090e102403150605090c090a090b1c0305090a080109020a05090106091809080c0303071409011215330302030606 67
    0x144000d040201640260540b03c00160318001030003500c0c428a03081000101309003d0326100d84101894000120181d81c07824480040034800e00500051034524120b41c0d180c0e40e40c6500c80403601416000700200054070b01c5040c080c0d651248600506441c90a1102898200240c940c0300141c483c03110401c145282c0c295940e020500580c0c01d80342206541e1100b000844c1d51f620310180303003d12601c0718071568501c0704000380242400c181e000880e5041c28074440d403443c5d03215040d140002c64022090b01c24040b000b490106c6691107046031682d8031440070b0f0b10100b071148044d0310140a05108440c0058600d81d11424031101080910603080480d4442c0c40400113241c4140a41450490460000500c2d0105580d24280c9030040a0865880d034070100401080c035408c001d20b41d554401640245041120b003400090211102d2001c0d058825200c0c0c0c1c0c0da0268154000b0b00c84050039989500c800c00f10385150a0013040c1a6540901e07420350640180c40182c1030103482100d01a1101a101d146020340c00e400c41c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 764763201 1250 764761951 764761961
    0x90f090207050f0303161707090605090117090c03011b05030714040f0b0306040b0411160c050307090e0d03020310050d0813090b10020c060d0e070806010311120109030206010504 78
    0x646090080015119852409000031840341c00c446c91140c81a8202040090081e4500022144506a04014800c0560b040003c100441e141490002d41d143e0b010001203a2581c10141c3c040c1050141c10284060311002051365003c1c0703007040c0d008200c0c900c0c0d000f500c050070b103a104510102240c01003000c100e42d00d1051041d20f0810f0070964030580b4180d91415a900c4a40d22030f030024030b030190044140801c40c40d240c007510b4045031046406112140c3c0501303103405180301e48009082c40c408a14541030410540d1440b51004000050540e04119a192080c00c00340140054849190042c1c10301040040c0c024801c1c1c0340640c500b403c46188490802003489803c40c413803081a20080d1040c0040e0300488801c0c0112006460110404140c244061090007942c2014810b03080035074000d40c00e00881500e808043d110640481400415207000c101b202c203040170300035000214103000d07520000c014441ca9071901a1035080c00e44542c800f41407481090b40c01c0b0740c01c03a0402130041c0c1288004100d580303009d07000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 764764451 1250 764763201 764763203
    0xb070203120c040501030e061017120c0a05070e010e060d06020d0216050f070b160201050c0f0f160b1e042111090603070306050a23090c01090f090207 66
    0x40328a004600300c0d0040380324400702c0340000114030020b8240280d590500880c1c0c8000c160000404da60b041143e00700420354182d00880b481c0710125a850002c0f11400c000766400d40b0b890f03001143d0340e54803042c0c80540310307103401c0c00a8071036105640c2e00142201c00084003e04031003c038400000640ca46000300982618145d60a9403915000e0000f00b4421480d48000c20070b104840840700254001494680d080c921814115880c94100030001c10184414070101da107403010810043d00350b0030848c0300595941c0184060910300e0320400140c80c0b0741c480c0005040541c54030700070890710740782e800340310507414803110340a0700750076040130b00c12035456000410002650782c504052190070161980c03100c801146054002e0b40c0e0309045101ea00081c808651103071041102c080d1564000da18020300400d903104140d20009000650f030b10f00041100c4825403041c450000740e80702081c020b0301c3d01c103080e41c0d140f142a0fa41c1d000d94003c00031141003d6014076204000c403041d220440600c1443c2c208c98000a40140350 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 764765701 1250 764764451 764764453
    0x10605030a15080a121107050607020324010806010b25260a1e1704060f02030c0a020f0c0f04090c0803030a0606020d020f060a050c1306200303060d0b0702 68
    0x49911030b6205200c120007500c4000b0050203400003d080c2041681c0c0e0058107082840701c00c850384101243d010502c0c0055480654000c0d940300140d03c042894144082ca0903242d03001d22030400e11322002818a503504a070090780c12603490340d8035800b14144a00c51241d40f000c003c1c00070380900001c1940100d281d020356020f0802041e1402c1380082088111210420038034030030800060000c00c40e600003005582d8051103001003500e81c0340c07501000e070104030f004121042c0c45c1162030001e01005190b8200d191002e600d5003040d901e82c1003005030707500349410141d0394101600a204d50030514020014030745054020040c055030f08007140109002c020a0b40d0701c8240c407010200390012030a503100700025070088814001c001042442e1582c02800e1031100c0011708119000700e103808000050001e08146c00000004002996807600e104004161255041c40c403a013807100b440002e01d132600b280d04d82080100e01c0300392001d559502d0322142e489100031201164082060200782e00851400d4103110340c0208180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 764766951 1250 764765701 764765711
    0x31404030305191a1e0f3c0406050f0a26030f0a030e0303040f0303151d07081e010e1302031614040e060601140f0c030301030c080312010605030a 64
    0x40000140e4442d0380314013640c0f80d98110440440e060542c1a110010000c10282041c000c8941c0012481c69a40c40c025110301a140b01000b1282602c02140800007941d1420460110300703907000c4c0050405200485120300d2a210b80003849003012102e5039503840d00100302c10310341e609040c01c1c0604003071654090071481d11800d8641c0f1112a081004125003248800503544680d1039170002019601406a6400d8a420a0051100085201041c000081d905090104020b82d00701540702c0551500c1d40300c0311000b2407160f610009070f46841d0005c0e01503c0c0550f503842440d551a0320440082103800600d00845541c0001004000450744e40747e5000a00100c402c019490030b2380010f40b40c044501ca0f001401243c21a0030030501c0803510310b01140410503038041c4009200081071a40b550002010a4103010154000c0c2c1c0308007038504100d0710360b03030a54014943c4401e80c041050b941d070b4100740030403100381401a44c041010403001083c0c0303030001c50713006140c059a03081c20000c40e0290005003010303450a80325 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 764768201 1250 764766951 764766991
    0x1b0c0602091903020a060c030f0c0f0b16030507110d0c021504080f0106060c020d0210120e070501081302030c060703030e0307031e080105091302060f030f06030706031404030305 78
    0x2000d4904030a500c00a84102c10b03811401009111503141d400503052180543c0c400000940065040a1000440c1003c00344a581424080b400000304140140340000410421040134095041c15403100d20030355082100340d803070107010740d124410456401c42c503510054034408554402d10190456034030250424601342004c07150b10000340c01c60b41005180341c1128002d05001c940910540c00101840e00d48142004002e40100e0008d800d07011020740111043c0361782c0820280200b408918610b210442040a0400c1e00401d1f615690980189400900f041c00404d40c28008603a0310307601190001e004e080c48850741030410a155014880440c00d154030381000071908601880a0f0031100d0291701c50f203141d03051101960200c020406030060a21542c0801071015803107031007a056001440081c1444600342d540001403550103100355070000e04134004204040301544c119868001c11301030301100ca4581c0c036450268141e0f00c0c070281e2241116a0100089e010074847d40187e5000812800f81c10100c090b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 764769451 1250 764768201 764768209
    0x50f0d05070911040501020d020102120a021b06070e2806110f191e11040f11220b03090606210303040f030e030d090509070314010f181b0c060209 64
    0x11410f903240c0141010038200040c1d6014031103035681d01c0e4503100842c03403c95001f07550300141e41c01a244c811040c4c3d02103403c05e80c04e400b40300c104462801c6c100407504540341c140d200400e4880d045213054002c500d401303107041401c6017980f1018a1550807400c013005042c1000c0f400c0340c00d2454003403800203e120f030000301122001c00384500c810304040c814030030707134031003420300f0310150a00c08030054510181076904884089100084140070761441213601042480050303402030040c0a03071220b18100c0c9580096804400640401c40d541084c041c009410035aa0340da03030a0989a010441c0c40b084690000c40024070181b030b03e1309140300c10320490140340301101d195110702d40c80d50300111070444110001d4485503043c55007001c4124000b02c000c5004084d070b02156500203000e1041882004e01910203000429450381c001e800c109081c824004400d215076940b1080742041881500c00c44640b0003e004041c4038400c0c0c10300544034481903400301c1c100c0101c03a003c0221200307401203506682c41d03542030001e03d541c1d0b91 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 764770701 1250 764769451 764769461
    0xd1e060503151017071d130b0903040b1209060105041503030c0c0902120a1a10030b0f062b0605090c09010915050c01060e1515070501050c0a0f09050f0d050709 70
    0x13440081c480e45040040382c1403280c0e0b924004400e5000b204d420095864500031030703a145036510080c07a6203281c46290780545036000f550458140c0d041e02140c5150f00402da1400c0b94403443c10740c000c8660303c2c6d0380e4206000480f01000800b480c5008540340070300201e03008100b462641485081c039626240e94820030041260019020407603090910400d0100c0d951560080e5403000b44500c0d20071307c0f81c02c000740015583c5000e40e051802850303201c0c0c000300c3c00c42e0383d012150b03401d00390054009940c0f13101004c20380c0c0249070104032401a00c0e205501002844c4903e200c3c11007a2100902040c4d0140ca410128640725002040038a041010028011640034981c1e0032601185040e500c0c0c19031507401294040d82525000d40018400c00701c0c0c0300800004800d41c041c84036007000300350354240510351400d101008034840c04c68003a00030340c201824054054081c1d402071002c0856a6112071610103000310844203011a03216065110a81600c41486d0303181645d44480c0b814894011507803503a94481c20b24065030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 764771951 1250 764770701 764770739
    0xc09060f030402210327030a0813090516031a0a031217150616050105070801031a040b01060806030106080a0b06030f120f130801020d1e0605031510 65
    0x30004010711086040c09903940c0b44507070100c200c6844080074540001e41d40c0c000c0c07524031807044030039450410000c000741d502581842005816640005140d01b40466243c2c0308a00c201501101044006003010b500c0c070882d4007880c10a924184440700f0128100e0103400e01c00312001c008520550112000d81d0f0303124586000b94403400d09642008100d80001d4020b410304405102ca9441c0842041001003003552281c0159504a5810303881c0c00f140300b0b140c0e02c04e4082d0f00000b01190700c0c2c0024812001d81001d8120b040761b00c03850f002000710715141c0400c026000e003503800600c0419a800103100c00780c001d058495009201600009a80390340b0081246001c2c80964190303001d9800e0b102340300050405008512107c00c0d0f11004200040d40d030060400c0900c180004541e01c060003107212000c11302c004400b00300500c440c1c0c009640321030903580c3d02802070051160440500784e9103691080410710501690003103450050240c44414007a10b01121954002445a84035200500700429501c14050b4008004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 764773201 1250 764771951 764771977
    0x30b0112050f0f0601031a0d080f0403060605031c1d120a03051c1518020d11030a0b0a080a020d060902030304180c180b071401061814040f02090c0906 66
    0x160410f0a40340d224880050302413410541883e034007540c4600c03441c07210800d101d006d80300c0528000c0c2500b4010070fa8062255003900c0d0210001c1c0000c02d0041c19000102515801c809980c0b0105c00c0d0441c0008102c0080401d1021076462100740c3c20040350503042400407040500030988071781c20be1900600b05800440110045800410103c05070050044400300c00b40300242c00f00149811303060000c40006952041844200b040c0340e4022042009405803118805520414828003640310f2402c082a04111000101245030884009407891f040301c8503011a1703990300141000c00000d40a10900e40c0081ca0207403805178503218501c0060f00d0030401400180f03d401c420790364003080c400305141a02c410305503180800010241944901e4800f4119034101e84400b40c9060340c40034a0700c1c2c01000307151100c200c142c1a5117007140018912808030031480103407412003010820b91001e00f01100071314206684c0a86106903c080c3c0f0350043c1010701c40260001c0050142c50304100c80400018100d9004191048207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 764774451 1250 764773201 764773231
    0xb040905010c02160b0309120a26061c2015030f0402090a021e0901030b0a240216030618050607030f1a010c08090109170109030807020f0d030b011205 66
    0x6580022440a0190528117841c605d18206000129981d218061003046090000940c0d422030501802840507442c5111340c1c1b00c0e5031412082245046400c0445080d4091001c02c45840812480404540d01181d440100342204620540242860b14001c01426400007194410071024408400196105502200a0910718a000c3c0f051220300c000160051200900501c0510b6241c841480e1280c501d00001340c205444480d5070700101e0113024244250344c2c010300e6880740030900201c00086026a140c00c2c3c1c90f56580c0300c0c4010000c070b030f440c0c0416009a03d4594218400d00009240da0070905021400b000044903801c4151680c80c1419005e40300c00c00840d0752002e120803800388a005442e104880101001001e424400010b0400c0e00108001014580300150a0f251607009510201c040d010301403031200c21801000c2c110340241840702041d008501e0050018031010f01c0001c4003003041e1061405480d251080150503006824402005418444e00740c09202e5901c2203445064801d4041000180da = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 764775701 1250 764774451 764774473
    0xe03121b0c010c05071e0e1003061505010e060a02010e0d12110307230f070818030c060d0c03140a15060302180f1804030908070803120a0b040905010c02 67
    0x86003801c120400ca040c407803102c0c1e500d8003040700400c81000712501c0c03810585801e400d68080b040c58181541144404501c510b0601c030415a408031600180e0384140000c1107510380c030b820807a000d620144101800100303400d84212441c1480000350030200b20a00020801000100d4004c0c1807080c406620b00004501c1610102541245d0050010244140c200a4a54202090000c24240c8444100051350b100d0f400d864264a01d01403c6402c13564098203010784401c0540342055040c1e000602d147c14a10146c1411f20300c602d804640f081d01e81c60014401450540324101c0781015005491102c0c4c14145e490040e03007200400d0b070603550b1160291550000d5001003002d0321047c170b03840307541000d010035106212020103280105001c6450380300445207502100410000070b04842d520810581d50f00d035618041c0010150001a09001da50b5907030180d07000743e5103521100e40e8030f01401c041524220b49410104144081aa10011403501c010707001146400150315940c0c203491007805407000581c0b1940f8446 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 764776951 1250 764775701 764775703
    0x12080d0f0e1c03050705090607150c020d08060901050315150d0b070809010608071707150816140904020a0215090313090b1e1c05060f010608160e03121b 67
    0x202e0040c030182010400c6060040e002071082c021508264051a400650348090208903801d00000702d8041600340320090880e00000c2d207650043c4c540801103500d03400482c0c80c03031a03d4107105040e2071014008102e2014135815801100340c024160300c1c400b2039010306401c00ba0310b6090700c20340540e01584100780d080c00c048600400301280149820056494180d080c80741002c00300b2a1411140d0019410700035504005583e41045d00301c2e03101c20981010003898032001c80d00042000d124442c0c07614298040c10b18110160340e141308000c2000003143c0c04101120482c5015405890020002d02c102d030415400c940c20110910402d40307055009500c0440c5140308142120703101c0e00500355010741444079425a801007400783c01e0b40003000400f400f407030903946c401d5281e25407804a011454820811222401d0600705d44a880940e407940c3c5076040301001041c614011202c06001d001c1c200800c4072000720300c140440b6180c60700040f8580c140a4003c0d4000c017180103501800a0007000d00e80e80040c02e0401d400c00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 764778201 1250 764776951 764776993
    0x20109090c090e0a090f030503060a180e0f060702030d020d29030607030e031204141905070609030206071b091109091006142503030c170112080d0f0e 66
    0x91351007641004940d90005448000c924000341d81810940d0f01c0c1e8031040000b6245000c6a0860510802c00c0000c0a510800c19045a00108103480640751007022440305551240002c9401e00d01691040201c00c8482d0625801014400040702e03002400c0c001481b000101001030745001000c206103180300240d60b00d4107026071a00a10242400c00c0700310b0780340010380c5c4c6a0154001110180000b131000400f030020544400000c1121401030312a102c07000300030039660700340c5000f05941501c664900072960f117005105020690390020701d80303410040d087c3e5a02c0301e04480341e98a2071402c00381520004419100707000d80000f040800d42a2a01c800a510a0240c0c4030001450012240032040c0308103e800e412a0f01c800200400c12005641c0300a00c040680141e10786080e104c00c0300d11003c00403401d0580c56400494071132616502c03111709501c40c40840a04d0b62080c02403e01d00446600701d84001015a001041c0c40f035000c0c031000c5000503c81000e034040740d20340310481449400502606403401160109 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 764779451 1250 764778201 764778211
    0x307051204112107051903050604081209030301050109031509061e0e010c0e100e030303041a06041a10270f090905100b0102100c091e080a0b04020109090c090e 70
    0x964204040850745940c641341481654060003810b40000d02038560b09034003101454101d0700710703032a03030800f803801c04420790044040c2100d0f15046800b1814120020084a049610595a4529440c00e40d2940c200780c2d140310b0040c48601e80c0d50814000019142c0c05541c1c0c4814509091051481c0b210300358000b40c3da2071111502d140c5c1d25150708003890b65049107001203031a0082d100c404480c0e45281056481113a140c00749903041c030021040200700050007854102600010950310321549441050000b50b5031458030340c0e15010902c6104800a05000800e04500c2e1030300c0c50000d041c04040d1120585005c13070449003600048825905018803204140910001c0c109410100058441a2515038854689941d454401d544850111100342e01c00c10000c68003019220341001120806400500380784582d10840c0c07031716819860101c44c5010304860100455094a0241080c211640c0d504030751001c0082080703040c4640444041128216031281101030400d585030080d405050106000e02140010a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 764780701 1250 764779451 764779489
    0x620060109060602120310092007050102030a1b0212180a090207061401030b01090506150a090303020d0e09040809061303050303010608060a24021903031a1002030f030705120411 78
    0xc2c041281a046a03003008c40c0c50320400098128550600f0348442140080d101510450100754002400019401140601d240b028100171081e40340d2180908000703400b26500151b00100c200c950b400301c8110050100c0742080542c1070700b4440d184001848500c481d00a141150f50104035041044414070400e034040d201442d6418040d0302d15900c90403004014080d0072100744d100d00200f5130302d4461900d2941c0381400c44c2c10040e2119032040008188004034801034005204908400410030b00903144045900c90140003d600c0d42d503940c60701562a0f2004c81070302e0b08070901300002d0040400300702c100e002075031051014550f00d526260008006680190078107210318001601041003400300e454030700e02d0050001a08401300da0080e8145c1c1450487e2090b2079150301180414420554194050210301c800d440f824035070f011081060141e40b444e07004a2034050b82c81002607580184140e0084c6611902c20714049150503002c081442d218202030ba421074a80c091071171580807030302c0e04904680000140da8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 764781951 1250 764780701 764780707
    0x1606051b0712030e0303090607080c070504021602042007050a12020118060b0a0e01081f0b030304260717010c03090c140a1203020304030b0c070507062006010906060212 74
    0x6030b0501e49460b010b00000e081c062407030354009807604e061041d40c4045000805607034555405041801944c0c2c008083c1258a0044034400320f03180c0307401e200742c913100600341c0306440c109440d91f07091100810000561038007060003414000261041d031001050214400c001800b1007402c00c1c0386c00101050000c081c5815039040290300c07006003002c5c40e580c8030040d03009400812103000e805d000c2580c43e4066086841840400d03c004642400001017000c0107040410340347e10340c09846a03000080f500b141d5901036068100f0802000b5076504844614800b085580010030700c182040300d03040c984011540132200d4400100300c00409000284a01000d0100a00301402022095619191444441d00800980031040e592001968a400c120b0704040c081080e0718140440c01800c2c0695650010b2004880c550703141710024418804203030644802a0381301c0c00401840741490025240a22140c5005a100c0c0d14500360b05600001001024020540301000141040c140f001c000d042141d060303045007184a0030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 764783201 1250 764781951 764781959
    0x908040b0c190308060607110d03020c03100510050f1201020a0c02100f02060121140a06110c030d02070303020c010c08010602071d0c030c04121209120210111606051b07 74
    0x44000360342d0164048a96a0303032541e051034002010b231400b066440d0040c41b5100d013181010780000c1c45684000c011001c4505804c45440c01c00143d903802c03202510382040301c0008205508148440807000900149501e00c11404034000e942283c101d1a02d12001070000441c0c0c0c415030400d10746519000c901454951003400c0802d101035a1042c0c10300c070704480402030018413004503164084110f92150311001110350000ba40d221556908110345080d20b181d8507000081182012603000c07513214070b0b4100007440c146449000b40c00000c1d0400903007038050640030480f100a070300d0284590840071410740c5a00314954140240249410801c0e0808110043d869040c00038201c00000d005e0b0340088000ea91a95a540301050102580950740c0200b080245034600102040f00c80340104501100e26940c5034060380e03a541a4043e40d1070044400b9422032000788100f89030a00c605909804401e948045442e1015680449004650319038450300000e036000c00c40b400c0103e42080015201d03190403004044050034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 764784451 1250 764783201 764783207
    0x30e0a1d040b090c06120a05012108070c0f08060708010527043002060615040b031f0605180301020c1f0f0204090506010225090f0908040b0c1903 64
    0x9400074001a44042c002101a0010800782e64200401340c041e54540a96a0f0500b0241c0360a0340c0340c030105400c080012542d1000d4048094414525003400404008103443c0d001040d4004201500c00407185d040200f11001c030261604010810040200028a002c2d40c4c01083d05d081a0809446801c1d001c2110300c1e250f191024081078982803c410b000c15407200c0c83d102403c000718840540130300c450920a00e040341c0c081c000882c0354003e25000d80708140d5400c82008092416401240750809061106001d1a000c40c3c01669010b14451a031005401050101403d000459803001c1d000170b0000540c103501503010340d1042201e4105600940c100490658900d0701c951340b60b00311065040000007852840d81c1035420084955a00000840d40c4540340c1001001603d02210b0b228054850001c096880200c06089859541e11101d00090f403103080c00c103800c0241513400c90146089480c0c10340f80b004240307002c0040004012103984241e641c5400250542000341c000788981040120303030704890100360 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 764785701 1250 764784451 764784509
    0x30c020d0806100509090f0123030703171c051501140f03070c0609050a0b091c080603030903031911030307090306020f0403050a0c0e091f0b010e0904030e0a 69
    0x488288078100300b0304038200c03242d01441d4045c1e60311020b11414440490080010380e13058a21144448008201005031411221400c085658140d801601c080000c5806003e869801c4120104020301d0805500c403240006510581803200b071a030b58009202500c951401a9400c00340c080c28550341c00099001064610b0080000da00e01c0840000009081f540c4180d160302ca0311940800200610381c081d00f4a5561454056412903100010350041140c43c00002004032003803d02200d5000f50149054089918850242c02560588800d0251075030507502031000c0c10700c00c40ca954411a4140b4215002820f440c4104a81d1680d41c101300140a9915131003000d803402d898000c00050303a1909146003148142c803640d4005803440c01807a20100070880c03803141c0d035401c80310406203002103512407400d11604c8515250000161400c2d40300c1c03003005013019030007081f802d860504084840d407032100f0114200e2403049404500007680d003d00104c551400c582000041d040074025029103c0010015640d406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 764786951 1250 764785701 764785711
    0x91e063203040501090b100504060b190e0114040315050c0703020a08160f030e030c01080717060a0b03183c0703140312060906030c130209031c030c020d08 68
    0x3800000641406025000020007960203646841076281c42e1041c1d0b506505103001c3e2610950800b000001e040312007406942c44540004071680c01200e0401080c3d0308030003100340c00741c140100040b0000300e440c1c1204c00f500055020300e41c01416071092002110840700004d04c4000c550409000e82d1000c00d0b400a0720f0507100ea40900e45594070f15084030f5600324130074104001004002891031031010075a009011401c0c0d038030b060b000c5541c142442001500d059004441e031074001800c6986100041549070901a00824003170000452107803a40c107030380f036540e00c01c465801070144030001c001c00d91300c6c3c108000700c401d000d1459107500c400122040b031090410344d280c0c4203514110300841d003180e0040511a01c03000f0340d4080740d058500070040c00e00a4aa82001c10710031240b010740000074136541440c20b81c2c18420107005010300408a20350003040082d690340398042d4103107542441000c11a840c200300810030080c0e44413030001c8600100c10024140d540e0042c1c44001c642142c554038041c41d8108120303c2e048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 764788201 1250 764786951 764787047
    0x13030b07050928062d0c020117090d23040603060e0a06140607060f140a060e011203030c052704050702031603030e10020d1401080708060604020a091e06 67
    0x86200c0a1806021400c07000b00005d03802281011005e031140c1100d200302d1824400c3e01ca162902d001604075101d8000c00716040030382071300840b13140213280744140d80024100080c000a9a5000852a42001075402c80d03000381c40882c1c0e9664003800948400b1645a600c03064401e42449040e0407d88240f6a803211200403130b004450105650040040a0b04000010303943c840d420012058041403031950340005444082145290150114281c800c0d4214503058940c0a80042d9400c606039904400414842600404110081c0b0030301c19181c1c502401400440ea40082d00c03151101004100f04c11500007030854000c0d036004010402035079052007075401e880703605428001020a1200c4003542080d003080d0070038440e240b00160003003003d4000d502c054044200e141c0e21844981e00c030a505651100180106211980802c00044440c80c040d0000c00c25000c80749040b01129a451079100136200d40003100401010400c0c01c203000c0c0036030004c03100802000d040c0c3d6280580e044120105203044132b0440180c2d82d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 764789451 1250 764788201 764788217
    0xd27140316060518010e01060e0109060503030f0a0c0506090604050d0806010c03111e010504110103050f0f041b0311030d08010b04060c060b0904030207030b0708060a050613030b0705092806 83
    0x6004041c2c00308503120300400000344219007046e080c3d00d000307203c980038000c80048030034004200ba00c601d01c59078041d15400350040d40380c1150601007540703a8000b20040f0040110903000003002035000d0240c10301890070380b0300801e07242c10945071140c01c101c0c0c40f4040004002e005410440d00ea82e0240f00e245090780c0504220800c8004c810390300b07040c80d9112010703001c02e8013242046d01c510030056010a10580c0681002c0380c000c19150011815918150b0307a140c4803000e1100031034100c0311050000e0382c002d8441c40c2020800001d42e41d98a11000540e801a59200c4446080ca15182418031100118400f2840c01280c0381d0305001c5045140c0c001c50065000300201002140304201c0c680e40015404c8000900070146443e040c03500940c0c9000d075010849080070214081070b002e50052a099000d40401014500003604001c18009280c2003008110310300c0806440000200300302540d80b038002e0045540f441c0d6a960628107200c80954840713644041c480880c2c00351000590b030390424001380c9016141a0f88 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 764790701 1250 764789451 764789461
    0x20030106030b040e07080c0a0f060e060309070305070605030a180b1302030a05070e180705370303030f0e1203040204020901090f0807090b22020d271403160605 70
    0x10042844540c244100d220707441022541c8840001d5158001f0700840c0d5000041c1d840c0e403c5590810301c18810b00001c207510060b0360400e880d110000e194080b1200e01102c511a640380c591a240070741a40c00700003c00e80000600c10784440301e0103184480110b4205494070908155503180740c0c544010308079410f09540d803800c50115601440039040080d0072004582c506a1110303c1e04100003001d8403034204a07524082c00710f00c0c255011804c00201e44004000d568902482030b64201264401002400c45009000801a42401840100d0007550007070384e00040075000e496001048611280244d401688115000c22134000c51904030303a031240d0706480240c2c41d070307100000603200c03203002d504031040301c04000b2030100c0e42d0300c0005544011600b102d9000d00807402c54605101c001c1071519110480f1000000079180c0c803ca0b20303001040360440024001420a10400030400a1a541c0142001003542014040103000038424405100020032024610b4449094110301c4c01c2003100200404503a11440028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 764791951 1250 764790701 764790709
    0xc0807020a2a09050f01092a080403110609010509070f03020307052701140108060907050d150503120706060b03070512071e03050901240b091f0807020120030106030b 73
    0x6001800c003203c040c00542400c0f000300101d14001d015022401e40340c41e4000020f86281d50b86041d80480c00d240b1041d4080c1c1c0054122001c000040c002d50511484580c262120081000418400d0014000000d1a0705142c1001400c20081e83d200d1b403e0340900140900244c3d8012441e503040716401c5501d1051300001030342d90a1120429420300d0381c40d610680c000151080d640304207640303980090b40c41c240555034900400000c00f00c156440c07000140144074020305e454240d400303805001400307100e08060f02e5440000902d0f05844c1003400c1a440b50200b00101004090b01580c0040c00e02c144004e421813502100040c00d43c02213070b04104800003254042150710b40a810001e01820081c1c920003020348103840040c0261000343c400b040198601000c0c840d102c45020303000b0a188d07115841148101e49042c804000c541c11144403036901100301400c41603400c5062654010032111034a0310140c2d441c11460190850303008040540f5140120400810340c130900310126030565080382800034817150010042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 764793201 1250 764791951 764792033
    0x80d1a1207060305270a0c090603031704050c1918020c0c06160602030a1a040c05091215040b180313090c0c0c080f0d0e0d1707080d0c0807020a 63
    0x100c005c0d01c0840c1d03c07104540404114190060b0086406512007541c0701c5c903d40440302c00344000f40008850400b8210414107a54191750014000c1c402c44580c0e5804100007421a0b050513060b0445c0b50203040200842407064048104841c0609001c50070724410009094503404e202a42c81d1043d41d0000700402e074001641e6280814a4108108644900c0d243c60b0701e100900618078844144264207203860a103240c94080d590b107048a030743e81d403814040d001050213510800314602e20201e010356050710b81d802c100401080e01c194000c112040c070318207020b03101c40e107104510130280c0110781080000c4046490340c0344205040300c0c1c00f4400020400c40d5180100c45654941b180101031880c901400030740000000740004045111100703603915581e610406131900c8002c210010340040c080010003004c20201c00c4000080502c0101c020b01d0109141c0d01d1a6459000003120038003140d0342c40c810050548e10407125684642ca40c001460074003007623210545895a150407281c0001075080441c3c0600d038400401d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 764794451 1250 764793201 764793241
    0x140d05070b040806100b07030905090c0c0118020906090408030103031d0904030c05010f0b0d0206090114070302070905010e0906042d03020c15030103080d05060607080d1a1207060305 80
    0x4420b03141c41d120704825032215005e5612940340041c1a102241182c0800304035804641d141d1a120302d9a0703c0c040500c12410001440036948200900500900a8080c052880c0c3d10f85580c50059105000f0320400c810000d029101c10b010345010410803001440040403281985d4160615030303541e8251141e40e440d03030141c00c00b6098018400c0420301c4100758010b211003401902c200c000b407018840011044040740c0880703000c00c0d4088124100c070409420701070010000e8920614043d103810740404680700341603110000c110010307842420100b103190224458540900203650866510382041e100080d074800c4050005030040038447c80d00b10000e83c160410410b100e0350280113400e81081428080d4650034404101130140c04400701400403004e00d00c00b181d058950189030b01c1c4c141a2140f03c8100103245c014095900301108201c81000b00c0d11100140c5085410700801080c134000c00d204071409184c14424490007203c4404d01c0061411008c10803605480c1c1d180340001d4166109004150800d0300303035403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 764795701 1250 764794451 764794469
    0x2906040302270c0307120b0418031e08070c02011d03060c0a140301030215070f020402030a1a040c0504060c260a0f0513030201200105010b0d0c050301140d0507 70
    0xb0b40c021100d98080000c074208100300c1c0d000341c09541e49402ea6201440200d61120001d007288031048005281588010780424015000254a8a0204d920088584d103000700703a010a403240b803000146c0c0c00e01448422207180783e1826030894100000041e010070076511000b130600480c5030121010fa0003003690741c21101d6004080f202c0c1428814040c44030740c9d1181e51071100249480c3c40c00c14030000c2c01411030341200d60242803400c01c03115458803021290400c80341201c164030302c0c0001401607a928005140914540d02002034038007003040402c20609180d4180311700540c02c041c44030b40c0d125000402c4c6d804503402410030144800c041c4c6410030b001c00d40304c8501240445500000d852120b089400707049046000e8030380c0614000c18a6043d1041c5c05007001c411f0742280102001e0005500c24203130071450044002a480504100900c40b81c2540e00c2600400d03202000400c1c8170240e04d00ca402001c0c4a5441801c01a2440d4140a200301072518001c0f9201c4c056650601901c003000010000c050040c40107a0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 764796951 1250 764795701 764795719
    0xb061e031203150a0812030907270b01020c0f210307050a020906060408120a030605060d09030e0d1104051e090f0705042903010b04090804030204050a2906040302 71
    0x1c1c0d08409507001501d40d00700c2c41d40501c2420065003040580d100548590310010248025000c501c4103103940001c1c6110000c1c0034201000175655101032002507550103152955440c00000314805040f14054101c0504640c4540031000458480341c010414140040c0c0b40c4001c0c04809203005490b040403590700380c8071840000f8000040c042d000c201000c82600c01ca583d100c05444010801195000e1801489419001701020b00001d500300c400400c9800030904000c64403c0d52400060005c1c1c00005588603910788580c4081c0030036a0041c0030410b40c0408480010740c00e5925180c84010300c550380010784c041c0f0b03071342c0307012030413240c480c0a002c031322400b80220980039454004103841e143e0000150720040c40c415240d02103034502d4140103d6688000140c45000645250121080b85010000c140d941555070340d81014500c0d1624000c1e07039186030003030000726640c030305d50f00c180421120005d003110300c01e40c07600c408410211f100001040c0f0013000d09452032801260807001074a0743c803580e0b0000b5400b107049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 764798201 1250 764796951 764796973
    0x6030607081510090f0306021e0c06071b0803010603020a02121602060c011d0706091d06040914031b060112030e19180b040c1e050703030f0501090222030b061e03 71
    0x1e50010844501c00c021b030780f02081c054090500c814082d842b050050303504900e0004100a00c110307101d40c0d01071180751a0320502c00e940e848008407030707100f80c2040000940009448d900030780c04000b0091048881c8014070b10b0807800480c0c405a603040d120009208050015001c90b8000c0c094003d43c900c41130030100700e02e24100620b40140c0d214110b1003800c02044002c400001e0220305c606510740414071540d030a46050f0b070341c44104002050b61003000c403450071040d000c0d01e510f043d080003d403816800c401728540a2a0b0440c28551030980c0c16407003200e882011007078a01c0080d0744010844818082515070120322250714480944e08405500020320b03e240c1c04d00180802400b6800030086204141c5041144540034a012150206192040c1010340d843c00c1c54151041c2c400c00041c07400d50b0203450001405c03071030f5501500a1700c00c20307032204108075004284001e14107400c444100f52003140c0d1a6500d9201d14541d03a04640950050015104000482ca4015103042c407901c0e0103002030b8000c0680e55030b4000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 764799451 1250 764798201 764798213
    0x629041a1f08090d170403032a0306170a0318030807060504030f031b120e0f0105010e0601080709060f03020f070b07090519030807021c03020606030607081510090f03 73
    0x985180c0a001900310b8010850010011840b450400019034421402022085503601d186001501c110b0070140c0c0c3d0640d035401840010706110714541758038903440303c000c41898010191035094001000107855610f4004404100080c544807c95250501900d5406045948210729440d64405004203d0008180c4100019640040d10491082e11200740010700c90b003046003105c0d0b6000295108981190500d0b052602890398840c0010b09400301083c0c94600026107401e21013050b060000f00ea46032401030180700e801d01c0480b6070106081c038045086240c900310040c0000c0c8944640820300c07100c4150384424a10030b404030f41d5040800161aa5511854901070025040c2110103d0005040f820085034928107801e115103000305280440311200c0c207640b2410803a9000c42c000300d070f01806141d045101c0ba0280905520414040c1c0c028103c80c1c41c00307106050508a00900135410010b0040401031680700e40440b0001c5c283c82506caa8019441b02003040e946404180c0100c0e81640382040300100b0001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 764800701 1250 764799451 764799499
    0xa0b0a060e01030510050a09030e0f061e130503120d0917070b070201050109020c030a0311070209250c21020a150c1202030c03010e10050d06090629041a 67
    0x45c503943c04010341d42e10340a981045907038400c00107001030b9030303910401c00500e4107898448201d40d00822443c900810140411801c03400d4140c490100440803c0c112030540711004c601c00185070550150414007030000ea0800b82e407007555100000c09503280808418820805031b4051344880010304aa584e040c0c5007000c2e0107402d030464211005600749400410404400d000f0785e11294030900055003000300581c429006031445414580784148240300220240e554a030304140920184401040361040062210f00000d40704290601031048420300b00c80012516401c0c40a48040444084803049481101b00e0900d038034000050000c060341042c0203000c1070650700c000030000454540b51004076041ca20882a800115140580800306200400c0045085030503031741d01c05c102210b002040e507103600029250308140c01d0161140b56460071110100600c5203c0e540503401800c101c103001c0446c680c03071410054410600b440c000d9490b4444403114000c502d070441491480101394041080c802c26583c0c1c071100c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 764801951 1250 764800701 764800723
    0xf09040b1518060306061203030c220e06150702030703110415030b0601091703030a05130b100609050f100f0509030a1401051e0103030509281a0c0a0b0a060e010305 72
    0xb010703940c049200b502d84020718003188071411010318254ac0d20308140c00d219030800c038000d02c031070014242ca40d205040344a0040014210b10581075aa90070844280000a403c442801e1885c410800194016980001c0c011080b0b0342d0141e00305094100a04c046406040d2401960b40101501080401004035001655125100c00e0340c40d20b030919614040b0510312020400072660980041002c190381ca4215003050ba40000c2030390302e50320f111000b5602c006c00141c045070812000c0701e007030030306006482d40034405c1c1009000403124100c0501a50700050288060341c0100c90a1148250624030050300503030503500401740003001d0b620450160700341050940150b0044d82100d52074040004e1018020034603510341701211b10070760000f42e803c5580070390340c0382d2040b030546500c1124840c0104800c044499028980c81c028401b0382107047c60300c01000071803006808000484a018803454854000c005021020319802100d40344075a2a41443c50380180510b800006081d01084000b10602000050001e030803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 764803201 1250 764801951 764801953
    0x9061509120204050a0b19170a0803040609020607050a030504080d0f02060f10080a0303060819051b1318020f030105090c0402070c08010c110d080105010804240203160e0f09040b15180603 82
    0x7038014401049e2a14040d0a004003007500138004100400c180340d201211f814400380115150a2603502e0781450803040c01411800120002010b0206100601c85030002c6501400c0000300c52500400c082e403649801801e00c0303441140c0d8400034402e044288600401440202d0603030741101c402d42070040c0940709078003c0c034803c0d200b8543c002c200310508060703070a0b203650000058990700504d03c140103600070f180d00409a000410800c0111451907610805d1490a6401d0101c10001c0745441401460002c4611852190b4545010855090340c0401c0e081c131911710031280181c1d61241072401404180c42500040120342c0f0384a920f540c80368020800b03041e0a401c0000b02c0d200d071070005600310780110f000d00605001500c00303001b0400003071a01442d000c0750a00303c0303070501261902c01c030030398200d8200712045500e200705521282ca280c0d4010103450340303002d4142c64141c140070722280400c0301d032040640010101561a000556440c0140362031140b000c1c00101034005084100c20411250113040c3c0d5038cc1c0c07103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 764804451 1250 764803201 764803229
    0x80f0406080c12010b03130227071106010b0a030f110a090e07140a03020d1505010f1106070e030a0804030803011a0a2f030409061509120204050a0b19 66
    0x50b0016815665024040404003003541e0802d03810650640000e842c1c480b0320b00f1107404500c01a40c0d515450107022440b180c403d42a00e22840e5146009140a8503a0003440008010416041404203080703055544120701a0340c0c8400e10a0214001c20141c44451000c603d002580300007801100c008110000e020340d14941501e48074000081c040600741c844101144000504501a042a0002d01078207441400c0050511114205040035030b0000c107000580781030101014841503030008404000320005251070b440040d00c40150320344c0c80c407000e0326000a000d020400b40500d41d80403c1108580c036800400709845950f40c4c075180301140c000707001e46110340c11001d02d01600d014000040c0c2d10300c00c82664807254011243c0421500030444422264403030000e2400010043c5001c0009000038005018009202c628180110003040ca000d5009020841c0201302002218100f60f00e030160541c044070001000d445d510148801403001100030341d00030b00c0380e01445010114a81c662002c40b00c840b02d03402c0d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 764805701 1250 764804451 764804461
    0x110f03010b03151f0c080405120109051905191b090203010302040b060703021b040b0d030806041815050910050a0207020933030a0501292d030a080f040608 68
    0x4803210709011143c80b00000180b074524480c800c020170700d010343c05030840e149800d40358000301e00303d550303030b0f2035141d010360b454111000800408000c01001288404800b40740f03025a56203043c0c0341c6525010404200701e8000c1c08900340551010309038081040c00803240302113035403400050b001c0c0d00248001d900ca5441c0030034030314182c240703282240d170400d60646c058014a05a00d035684003202c440092540c0040d81c9215250041e154041c2c1800150301989515440d0b2a2043c00c00041e180c0340c0c480032210003000510031002a030341c0b00b2500c800200c070350408280d9035150101c0c6850002d619000303802c000d052406021401c0300643c01402d485000380d070840c2d01c5580320b600d08003140c654001f2040046403000348184080603a500e241c1d59003203006080e5052a405501d03940c1c25120101e0980003140b20a44154100d60a400c1c0d407018510300503200c010050764815146000e10842e441240000c11040390400029a014841540c1965120018580b24100e41202001c02d8115006001c045914500460 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 764806951 1250 764805701 764805709
    0x307060c2306150105130e1305010e10060f0806010e07050c2b0e0105030a020f0f0a0801150309050606010f1e08071808120c030f0c01140609130204110f03010b0315 72
    0x444075055400346c601b90b0340c505144401400d01c020604502c1180035146040003a01c00e01581c0f034035038401d10003086c40b00404103002e4101e5003142d010380034001014100308100e11010072901d0444000c071011001c6a5219001900d00d88101943c00981d4011034070700649058400d072400c60503100444580103802c4030300d42d080e180050542d40c80c4e80801c0040c0300064241d042c1c3d40003403500b415200c95540c101014071282030019045a0321400219511000522150030101100e05200440d4030307003805640496200d081e11403001910840c1000982d11103025000d010300c405061002106807520509400804001c0c40d41c6819030b0070500086150406072201072280502006031000c6901034452200b210000d00359560292a0403191400180002c00741c02c07440c50050030450034481c0011800300001c9500c1440020001d20b42481515034a090000d100366030a400d00e0320950589000030042040440e960903801220804041c11900100204e503240101e03000e580151143c0038a81640c405501c100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 764808201 1250 764806951 764806957
    0x140a150b040203061809030c160518040308040b250f02330a060b0f090f0103021c050709090e0708010b1f08070507060e0d08010605090307060c2306150105 68
    0x4c50b0311811610344544200c40b00400c19420958280c00c49161016000707080e414002c41800d04244001030f10313800c100a040802d078640051495448801481c0740503030b4040c0980318050805811007005500141c020320300803140020b8005605d042c4910801407020050070303146054600c4006004002c000c1c504211150807030340c3c40401d001d4404003054034016200d1034608000700b4441c5d000307403a10303000201d0403100c8004110700307010340310440d903140804801d00005c1207090b0381c5681014410004101d5400c920182c1003e0701c0070756000440c0680b50700c101106c640b0802d0700100314262030030b0401407100c20009401e104403034240300240541402c00042212b201c4449000b8421040008107a4803540e108209181c0d01289c2810580d003011850303294031040f07442e040e1170789145501c46c2ca200c540a6801440f01401403115282051814090300007103a00c0d2130380f610910080c848090a1142041400f50051011035001400403219001e803075a03955030f6401c1a04c40c04800c940070b000000725544070b8822 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 764809451 1250 764808201 764808211
    0x1b0d020703060203150411040306061a1603030b0a3b060d03091223070602100e0109020607080403140a030f0f021e01050115021c0507140a150b040203 66
    0x90030a141c80d54941c1406540028000f05002541c0c040454650f9981d114660006c0450000c1a40321403c526014003246d41503003100f03203480c0c018540070941d44402c030100c40706100c5031010350b0b0000343c20313103400d60290800310440caa11405560008c1500300362016103980c584044524900c100d680d0810004440c1749110380c60302c42030101400a4000e003406080c040b51144240b801140e081c2c1d8800e04200141e52103c0200c55400700d80e010360130440440c5520504200350240035207402440c010000c0c1d900e49100d9040350760300383c030b550f22091440000c1d8042c05080d6005400241d503000705281200c0d060303006000c101c4070094021400c00482c3d8001981100d204d5040e29040d010041c545d005a0740c81c606c001424085214140c1500b00310344040c410261410020740021903503504015101d589031005440500442d0301060304024a00044004100780c0a06801c00302e50301d002a0070041210800d404000104d407041342c0b0348800300460b100d2542220070000d482006844600802c100580c8000d0311 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 764810701 1250 764809451 764809453
    0x306010506070203030c150f0708090705040c030b0411130b030f0a15091a01030b030c130b1c0506010807050d050a120224061003021c020904201b0d02 66
    0x10050010341484030042030254002004c0782e0034103505203540c07031510380000c102d91102c0001809003c10f001400076115000209802e21140500e4015261171b130f43c5441d881507510684d224401c605100c3e029503c80002040081e1003408004010441213819921107440d904c0e4060200d88009200444542503034000d007400008031000d41c0b5071030b00c04406041c3c0c007001182c10071b100c900000354070805403181c0c2126a204000c04015610382400140c22250002c40c03181c000d411110708a62a540c4582c1040d4123121240c000268441032900031602105002e4071440b0300c1c0d103400b01a14207000f0002121412a11034034100e41c411915001801508445441c00070f00a5000e03107002c0000810001d00014080e01702d00c1218000403191080b100e44111a42d112031103a142d13503050101c0c504006144a101c0002820190321b410500e0040c5040c50006051886441da8013080d84030b8280c0e601d410048aa0340010480c400d582a440c42c24a9640c4c001c4801c5c4500c1284054000344011002c6900c05c41c80209030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 764811951 1250 764810701 764810713
    0x60613060503030a0509011b030c1505130f14070605040f0609060507080c1216030e0409030e0d0c0302060a0503010602010b010207050306061e0306040f050d080f040f0303140a0b150903 81
    0x40d200751881e412011400c7c0c1805a00f1041c0c109010303200c0301001041c1d020b40e94444440f185420020840c00d000f080e030320f08140c00d020800c9940180344104450055000d801020000b215050100014024000212070350045c240000303185988a00684140c03007040c816004902e981740c5c0e082d1090700c0d140c856000814400d001c0c0c540800c0410300908500400c2400703941c00300811030382d0034407658014847d001244c4502e400c4103041c9640918515010141628100301e18551618050480030915034001e1041d440400003508000421413890f00840c0d0140041d5166a019000a000350b0401d003ea100158680b400c444059880040c80e20110317134018014020507164041413006a903001c28824030b100087d0301e003054442c0c404002491144e801100e03d80a00d8040749001401e062400440204103e8408240a6600c120048136038200303601000ca01f100c0c44d6a03180960140049108a110040501041011b44407858109035900041103e9508070380440030708020b9980a19a12150964030503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 764813201 1250 764811951 764811967
    0x60406150824090c09040302010f0e0703020904080307020a080703031a060304020a030308090307050709090b010b0c06060d11030a1a06010c0302100222030812010f1404050a0f060806061306050303 86
    0x8452080c2c000090754140c50f1001342100204104420959049006179510100d0854643c6d041c4901078542c3c80a0b0091b10616280d03800142e500c0030301403c064414100003010030001c1e80200180400d481c0c0c4610781c00c0d06c844a82c10080e009100c0c0320074014007440c001d00d40f1001d41c41d144d0300316449154020901219070b0b0560b02c0486100c10020608000c0b403204120160205908100f054024000c031a408154000c080c034242d000300343d040c0d00c0702c640b441d810b01c01c1108070038011031070561101042d10700e041003401c00c0c20505100c0141c186016054044e14030303910244014031380c041900d407480801c001025141c500044940410120b00034006820075500302d8902e04c019002843c0132405080d21403403075900500c60b03402410340c0e5070040300d00c2c07100001d420304054024160580101034200e1500c2d010340c54084160b4400754040c40181c4070f5a03a41c0b000507010001030780300440d1030102100401c10140c942440b03540e5a4400d9a11511480071107003802030410141c0103840c15900007030040c500342085 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 764814451 1250 764813201 764813263
    0x10f48080619121101031e02040906060309020a03110f0414100605090d11060c150a0e01110f09040627050c03100e0406020f030a0516030b0a12140604061508 69
    0x4400850381050f0325517480d160078246687d2406a00c1c1a403500041c1d07554689140c206c1103c109901080516003060a41c102503600d4802042c1100e410034111007550724075800042e51040d451080603840b42c507000b0700c0024200c03042403c0344580c10f0742d507030f8441540d141c00c402e4445001d120b03140b40d03001140851480015000c418109201e601c0030b0035150800c2036840b4000d08000404401410710440381c002c0100303034041c034015000b0902050008220b00c136540d062500d064450020751180380070001035804002d071500e50110000340f4006060107810401c02200420200f000b41c42e07030880505002c0800c0100040800b22800349070320880004100b2701e0401c1c5c503400340000900a5915640c280209e40801c420100114401e240c00070300016245806010103400603081842e04c000c140c0383c254120200c0c2c88902c034900550700d513040c03254100d080e41c0c50520b0040d8030860340d2010700c0c0244003e00040009070380085040302041d10020f681c6540310ba4032250f036a4501451107075984102d60074001c0c0041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 764815701 1250 764814451 764814473
    0x4032604051302040b03180601120c1403100905011b11030304260a02160b18130b0301060e060f12030d0213081e010f4808061912 57
    0xb00a40582850358071002500c5a820407207102c00080321110f8000841d01c0d060118601410240078016650303001e03070316040d6040400d4064004003121100483d007240c0d40c00c101c590107804000805000c0e11b5203510b84a17028020946075a0700301030868014a140500589074804103030036460046046940341e8482c022100200341c103400940104110440c80c0c002c1020041c44149041d800601e81184216418950040070b50310200d022841801002004131803007040c00d0740d056046442449100c18000940010030100300c0e444d9166207060000107078241c18041480c410002260107423441c0381890705004049112240b005000c0d0400c00c0b840303441c80401d5001d42036059262007820f03902526491060b14100600c80c1c880303404c03109215041300000090141c8044802c10301b0080c4005040306144040708a0301a8150900400d86c2c441e078482c0392020400000d045103100e04001d65404c00210142170200c00351070b0280a60728800c01408440d0b450b00f0110304543d03606108805040d0301d42c4a5143c000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 764816951 1250 764815701 764815729
    0xf110703050910180e01061b0210030b06040801060602070807061b030f1407080721210e03042405070803040f11040e011d0627011b050403260405 64
    0x882a48810b21880b1000b04c90340240c0700c0022001920350404101502e480e03107008608c044032031402100d1006031201411228000da580c2404160b1010000001d0b00341e025a40000c0c01030340c03900c1d40006405a0028507942110300d80d41c1501c641903101d4034122164010424120100c464051540300000d104007000800c00300d00e49410b01d4101d40b85501d00c03c0d01e41c040300701611401400f0606030148a21907444c10404400304210b40d00310303100404042c04000043c10003d00c2e540a624180642600d60342005000b01c1c5c1b01c1c01502d40da242c0b610500410841142014030510240e41e010716034407070040c0c0842c1c2549411401c442d05680d20366132048180780c1140001c5a20001080041525840b0f500520381c440c1078100000c180a1380750141d160031315001e900c40c0030a55100c4030601143d0300c508200c000e42d880e91900058680003c801810f4003410140c8012001d44c040340360350020055120f40a88142c0344105565003a00c4441044c1212200092180140b000000c10003040b0600d08a040714203d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 764818201 1250 764816951 764816957
    0x7030506010b0d180809010e181b070206030103050a140303070504091a03122d04030209040201110604080403020108090c1e0a180e0606120d0507030c1202010f110703050910 76
    0x2a110030126241381c8090040b196480042007490056801441000501000fa01c90581805400101c50400c0c10040e144084070411451064112003104048940c402e4004d4035007940c1c2e580d00e01e019561600020700603543c40c540303281501e1400d00d020003200d000700440c2d6942e90401d820440310400400d041c0d055848103c441120340801604c003401001400155646007544981c99885107241c1503c0f803807150071140c8013541c8140c14004180302074a040d01c0c2c05482c0070480c3e0341d0350310059480100300f40c5129003c1c0b01c0c60003000200100180148180d038401c1c1d81d44006500c8000a5541d02d0100e803076042e5200e0720a0154862181ca145064600444000e00c070701c0340e103036407452a071982003121071a560340d00b03441c0e4404040300c04003001115000001600c4051206600b584030341c2d1241d1060700e100d4200040050032030b00b418810b4101c5200302da00024011400b81c49200e01178020407400441f00882c50402900c1c4114115a1054804140e050748070307030b0b240194130750030000f002e04500411014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 764819451 1250 764818201 764818211
    0x10338060f04050a050601030c171504152301080103120807050415111e0607030905010f02030702010c09140f1318050a03021204060c0b0402120d0306140307030506010b0d 75
    0x12559140a064020711485400280a04100c80010292940080c500c412b001c0d219001c61008140005c0d0540d0209610b0450f002c4003c4020000300034011180c6624610400c4a5001c203048580c0c1c10b94541300c420300d4440180c2f124101c401914415024440a0a11100c110844010714081c0c140190710070414604189025110382458000440c7e007400c810004081600c092884541002101250958480741446400764501d00c10754031040240402d04164840411800300039094200b51000c141d8203a003507440386880d40e0028000e1071041501d00c0010320840c80002e101d4883c82030003090a0b000303403102c07c0301c0c41440c0c1401540c0844480610302d1655400401001c441d11202e92248a0f2003500a0003882c0b13100d0600900c1c2120204001062920403c01006141d4002c990f42103091b9000c230440c042a070b07070f80c00001c4449a41c800030250500508072030744140703070f4140e0041e021341d0300030750031804024442c2e014190f0b0b030386150100a0007640300308014409401201c000d005804044100031034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 764820701 1250 764819451 764819479
    0x305060d05071d061e0127060c022809022a0601030308090309090105040f0e060a05190b330f041d07021b180f01033806 53
    0x450502c099205090512208418400d00032880e500d03190402c0c401c0711800110101052a200120b409071030460600071055007004070b480303c010b440340d6400c1d1203000703201500b642d408004c0c0c484010380c0c208900c10085031030407587d0469807170041400c0c0402c2c0c1542480e034908120500000754000f080748010040b030310307042000c4016000700010224040c0c4020705441c0d45140340141c842c8034050814882600180105007141c0c0314070f040241110700071900821001c0b60300e07180c20b00402200d81c4c0744c0c50302d005032001c11034800e40c6074002d00e000d80c15070b0b42c0d607a003c0c15542d2403010480b80d00c0700c030082e0f102d002c088055100e110740704200c074804403135110780e2615400040c00c46440c6600001001e0a00705010804115100800a4100c0c0c04400040048145d1030300602c0252a103000648110180c1070540e800b1085031120040d2408035076896540c2e2000e8200070180c001050f2091004540520f00000600400042d5114075051618481d190a100f200400e118090001005000a4120301e01c6841c03da = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 764821951 1250 764820701 764820703
    0xe030307080a020c06031513021b06041e020d020f060f0705060604060905071b0510020f0705070504090b2404090b07030605010813030503090a06091b0519060305060d05 74
    0x11000d882103072820364400700c4440183c100524001c1c9544152010300402059152072152604410070448188102c1002d50242070001c4c05444c032040b080f400a00d40d2591150000240940140c0c0189a0050000c24243c64030001e5900c0b10002500554035a80000041c1020040c0e0154094010145400d24808100080c66504014400d5505038000010310009081c6841804082c042ca140240860320b0300301c0c0090003202c1c50000c14000c0032420540c1105001c014028051182140f5034255514030000e040304c0d500c1d8100d11415180341c01619000209868a0300c990072009504c410312001c9513540c92010840f401c044600200455465a4910303140d03940c604c2800e203024800c50440c0500c1c1040880101120b120b03400c071320f06005a40040c01405040b00c03540741000c07981494081da40e995108041410510b0384c050003400c05061040101c100031301010840305112104410b507039016580c1e0200301c8022a0010040e01184c03200c0b406100291081e000540d1145025211f6400c41d00e071035440d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 764823201 1250 764821951 764821957
    0xc030d09060e060415200a0308011e0e070504090624050a0c12050c1c0e0607020d0b0903070b0c0a09090b1c0c0501090e0405190f0b270d08160e0303 65
    0x910300180c000044014602090000300e0601b40300e1000034540181e444da40603002940c180500b07404004107240c101004100c950248001e01030b000c5041045050080018005402c14029410421700700b26020034443d04c002c001c402080f01115072082044007065040d1042e42c4412240c008001c414889100803d200005030040301e0490b6564a40d21f0038984000c40c10004501200c000040385040407110b0903510440c9114658011100d840d0ba80d0101c1c40084d10658104500928522a00b03040002c01074001c0054060a0b001e2021000d07160394a5046555500c190190503000c5103141106210b20a0035134005600182c01800e00903813000821100d000d078020790301e4211600d000d20700c1d00b031140b0359120b494070b401042d40140602c06824182c0c1c03025218044c0f016410018102940341d02c0030b014482001507441500503e80d024030b0b040682820072420042c52080c48204000b40d242092140001000402d003102c0b81c4c0c440c1d619840b2003801071b8225540d1a100d00811a4280740d04001c1c1d81c0038070003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 764824451 1250 764823201 764823239
    0xf13020a090303120212010b0c071d1e0c0d05040314033907060c02031e030702011401030308043002060f25050c160e07020c030d09060e0604 62
    0x1031582000c0c42c502d0018021208080d402c0e120b00d00500c4140300e101c0b1b003d03410905403841040e00a0725600b0101c1840e140603200ea02181071101d510010b03042603410491307041e001c0c03841c11a2080c00c11844450b06450600d054030303103400500041203240031600441e40429001442440c2030380101c0800225041150010389044041201c0b41c0c5c5d03807181e1070381a08101d2202e40b8400d80e00c0da021800341003c03c0540c4c0900e607800f8003a0341c3c588603000c403c2807090007283d01c4640110412003001100d40d45030001900b0454034000950301c0c0c400018640c0e10006201070490742d250342e0351401c0c6e07a0349a480c02c0c002c040b009241e03580308804003d200c074080c00400315100d0458899004000c00d19086290303c448040140400710b6140f2060181c1e901c515001000080c0c2e0501420003a94400f80f070140c003850b2502e0703074440038410924243d010440a0b640404a40250047c0d803c44040c00310400806454400d8603510b072000c1011900d00b045060f0003440d4605014800030304040c205903441610002030702c4c0c4021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 764825701 1250 764824451 764824457
    0xf080a0207170607031a01090918321b060c122101050409020616030c0b0c1c050609130f050706031d01020414040504060f0c0f022503020f13020a 64
    0xb0400c24410380c903110f0907070860200c46c1010000911003001900b641d084c2d0288800058488600c0700c0a00100146c0510072540b020b41605107841100e02e452115410b2840c00806054956101c01030070000078818424408003e202c42d0b5892a9800704050b136070001d0200e8106004d005c4a14054500840160903840c840200151700c000454200c1c0d204210141c000710300c0b42d80b500f6060009030f11500d041c1c41041003110141c14449040d0709003540c1d83c5801c2900140703410ba40e4810082c43d20016405004081e440030b08092203500b910b004903042c0c4000710b84240d000160f20000a141c03081d40503003442500d0080f240c1c502e1400503a1112810001e103a001100440e4484480c242c02410315050b40104101c2d070710007142402c2c24107000413a8580038185080c0304a48800c04102840156400034400105a40003001184503c581c080d20a00c40f222a030005405490505c0301101c0d02c1c00c0109500c030f00c0e0741c50803142076829039081014410744000c4040d0031030031032496424002c01501c02000303c040161 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 764826951 1250 764825701 764825713
    0x60d060c020f0c0108150603190e0307020f011d090a11070819050a020a06020a0318050f0c0a0e0a050711030a08010e100602060a2007061d06040f080a020717 69
    0x15489864000f001c43c41c14100080343c02000003111041d410310613541c00445407a5501d40f2020a0700c941d15204103002064907143c8a504075502170000010040140309840701440a07003000300648141800b0801600d44607039401d000c1219180c103011950b804019902c000450380880d6510900b190400b6100304e600200010b154540074441c8078141c100c002481c03506514284a0484c000e4542e20f100300000e24080d004500302800354003d420030b05940d03001c1a1610702d2806c2a0410700e9452411010101180c003a0079070390382c194146030392420162480c3c000c00c15026111109244010719000308405e0070081d00107510440e01c00305000030700001c070701992030300d0095045c84d90700110074402900d40d00c80085484400c02c000c90300071602c660b000040810004040200d10440110300c140070103500b41c455400914001005860b41c016117000408a06026070400300090041c6d03114010768010b0312a04255100070001100d440040940d01c0c2e061041c0c0d5403203070b0f44107410a00714041e204c1d2034240d60090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 764828201 1250 764826951 764826973
    0xf020f0d030e100203130b0601020c060c03070c090c1b02060f07050604060f0504030f0c02180106050c120f07080a03020408030d06080c0f10051605100c092c060d060c02 74
    0x204141040f0200e412011451410100d0f121012684c50300e100500d00c9540c0c100065031070303000f48081c0c3d45519010300519030301c00c00c000390140c513075120b01002c07128000c1c0381001144000345480707803450000c601d03126444100300e03079401140445001382d400caa0000e0104401408031802d40b002c0d11042e8402c0000700140e003085d10345603042d114590000c001d43d501e410200404203910240140e454020303030420402d0303c8031500100745800c20640d03800d100c4981d800e00003c1d086c0c1c1d00900521221030580300340d8101c0c1001d40c00c4181d00c1c0c0300700c000320845018140b00070300205841c8070050201c141a42001450aa5551101815a00500a194081503440e1002c212600c014040c400300000102d6408140c003192100254030a009688030504002d00856160200740d54141100f003c943c00c50222030503c040085c204c0c0207021400d42160020301c260200064100c8402c0c2041410345840c0d420701c05001c0306000321032810703000410840d4030800305501c11011613414850700c2c400d080705038090400f90002d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 764829451 1250 764828201 764828203
    0x200708010c12150e040203010902090f10120203120a05070f0305090a0504020306090a020c0a021c0c1a0f030406110c07030b090f030316030b100c06110306010f0f020f0d030e 76
    0x1a030950030902c182480f210010040c04180420f0940b01240034903034080e00c90740086401440748080080d00801807405216018410f40c180c0b520480e1075040e12500c0640b40c0782d00403480c81404078000d402d0b5218034401e91a03c0c80c81d00141c4103000081c40d0650404045032500880400d0301a016000724800103030031622824175490340350140030306460940c650b0400b030b00440d0860000030401d80c80241e0200708681c01d010300f4095030100c1900104240d0804007202d00700101110581e000300c2701701c64045000641d90030003103642400c040302c3c4445641082185001d0020b02e600c002c20460322039503142207451900e5610405001c8070320440004159050071031618509070b400c06000502203034010560011415000412282d0088040c8040fa03c0610030701c000b58007a22001060940c440740c0781072110400c81e0b0102400c01c125004000034002d020151074801d9240c8001c2c1c940c18001800e51a40c030141d2030050440100300e040c144100e0b1512500d420700e440c1041541d19070707070700080c2d110703040e085000744 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 764830701 1250 764829451 764829467
    0x1a0306100303080a11120402060d11090306070c03050d05060105070606030317151c060f050c0c06060a03320304060c0c0e0105010906120e06070c15090b07200708010c 73
    0x9504208214240e82d00c0341403e80c501540306c442e6807580d8054001800c646410080da03d0b03a00c2403080a210f5407203800c1e1640c0e41034001b001568001d20800c800500014440c6038203c40c1a9015203c1b1440c2c0f10070100640041d14000b03080b1414007108020000018450b84210707001103000b50b0320a650b404058640312100c0d58040c142000042c01400c4190310342d5100810907040b4014a000d400c1582c0c01440d0400c050030b10001c609185501d01401c20501030400001003400046a60990390305581e00344c10408026a40e0101810030140d0081c010801d51006101c801d4040140b2106100844165480351846c3d03c160030003000a4607030307080801045004001103026003400c0300013810395810a80000c0c003903c1c2e1403248500f0000b40c03a0099080c5061640460b00044035101030700d000741307050403004d062103e1100017114040964420300c0c410485503c039440030540c1c01407040045850f0b0701c0f02100c0c070140d400c0701c8204400f012910b20285181c1000104000c045840011601c05403e50010300284 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 764831951 1250 764830701 764830711
    0x260d0c0207030b0a0b0409020d0605060a06030921020a060f1b03061d06012109031d0a06050c0c0a170f1b04110409020a0c0c060203120a1a030610030308 67
    0x54859107041c00080d2450b00d48581c404c83d140d80014490680d4000540602100c002c00b035005600c1006446c2400099000a486640b068070f60b081c056a81e241f0807000c0b10949580035080d10005400804d1031603626409101c03555040c1b045540031402502ca52017200c0691141004095484040d412620141c5600350040c000b141001c105480c03801d107000c00407504003096440d18858403000644560b00503001c81394200399040c41c006d41d0004104005004144503401600412140c203420183c00401d60001d40a64074041d01c00100c503450200160340390380184d0f11298880c002c440320b00b403e9444090400c40109603000c0100c0141601048240c02c22010442c21009504a1040485c85520034031450030701340001d40700017804140301311a6000c5d174040c03500401c00ba94000504c05000aa0042c8090010b50007003944260155a400b01039a9038440c0d204400d0f0052040c3c000a000000d865101d19031268421407500043d03000e80300024108a01102c000300c41d04009172041c001d1541c0030240ca50701c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 764833201 1250 764831951 764831953
    0x180f0f061005031303020304030c090e071a0702090402011e08180105043f0507020307171e0a0b01080a060b03061302061b030c0d1403060d0807260d0c02 67
    0xd000c01c080e000b007482c0b00003030101411041c8100e210041510820842d00203582185880c1102a15a452440035144a1190300110300c10b141c0d0105004403511a82e20080581d9000207140c084140e003440054800240141d041c0702c54070110081051030309110b580030002d25940d10f0340500c5d21a65100c60180c41589210281e0f02d400c04210004000c40d070303540c0f490342c0c03900401d52844010901c41c03403203041d1724080b0311240c0b03565100c01e024064002015119062003182a0b0f1005500c1c1e40c0d0280309920202b0f1321100a50101000b22a1f802402039a50518204801070341d0317200110341c0b6140500c400030390000f400c07548075180e4201841130303512607202e00303180c02c4014150904200d140c810b0120303105200a440b56200080041d072002c1c900d21071044e4282d090044e01e496000c103e01c025200d03098045010003003041c140091130346400d660200c1e0f00c40c00d8020148000301e4056111341e90a6003200008948080001d8581711800404080c051141c580c0c00d400c15a03104000003039482a902c0d080c14107029 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 764834451 1250 764833201 764833219
    0x10513050a020607060e0304030606140405070806010c05070f0b030f01120f17272e0e1909090c0b07050607030c03060f0906150c1101030b180f0f06 65
    0x160040391041d4025011262180c450b4101e0801500500045150003103c0c80001400410080c81e80c0100046442e5460241111303010b07001800159141161924001047e0200140f52580195025046240030350304880781140c68054840b00300720b442e003205051400200c10410580d010b0f03002d01d40504000c03801c0c2031294005a41e64504000940001007000202c60580d00710b80f0b4440d030545902f4101d034080710308200484169402c64466400345540904403e544d03212a0713121015281055521103808c05e0201d03281c0c0c4a04035441c82040e03c0b4507034032841010301036039009504d40d075600c00342403500c0000072100d944d49415403008110780d00084a28805202d4000131a030041003095021545003004500c81c00304c41c508400a051300d803c42c40924410038004150703c2816403000c03058810310720800d0420620307800c05444240984c0002410b04000c50450556544250001c060300784000d89882c5441c00c401e950001c5080b411500342895042080c100403d00c8616110304c2d40100e17043d40e040714 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 764835701 1250 764834451 764834453
    0x507090606020a0825050d0809010e0f1e0319020f1014190b04090305071a0f0103060e070b4504091e03120b09010b0711040e011a03010513 61
    0x240d13038004c00107000e80d0030142200107800940d0440c0440d100c26408425910f04101c001c901502060b803d407024000d542c81c04840078040800010300110200c168130040001c980f44c0e00b0701c1c3d9003e40c0d0541e5035140501041c00003002c60800220354803001da0760380d005000900d80204842d80340c520b042025900d03150030444101c01d001403007400343d9042001c1c03d00b0001c03070740305140304000505181c0840396085490032408006050340080907188951149002041940b100d00800314420801e480c54100ac07007010004100040c0a0350200c501b000d070803c1a43c182581c0c90711001c070590490321503400c98985d20384503c07440908110f040f448001c400c01650424591095411b04110300114985000f00e5075403a545040c0800000c918002c0310418591001c156014940102a641003448803280107040004600300d91034400b03400c905940a2203401401d0802c0d941301c0f80e4581d003000f20110b401943c0c07003081e02c0c0400000c1c060724244400800f00c08a8580718070003450300f1181c2c024502d442c0a004484014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 764836951 1250 764835701 764835713
    0x708041e08030a0f0615171303020705091005090412030c02070608130201140f12010b0f0d020a0c020d080406020c010e0a090203191e0b010806090609070504030f0507090606020a 78
    0xb94110400280c001008118191404028030041d0004031045040050030482d1560040702a0381280380036813440402e407190b544103000300c0021000100545c01c4081c0a025a0801414280e8003100001d9800101550399000c04c11120045d01c0a0b10640c21072403043c490241c040c007464440b40098070003099542e1820100802c20340300a04130400d000e50b060140c405580c410072002e40064801032195a8508007101c080c0c40d1980181200181e001c01e039400062160503003420b0300d404040740d5045900d0000340c02c50447c002d51048281405000007544203001503100c40125040980c400c002071990f490402c40d020740303401007954a0504220078141c02c00f8594880c4035415086a00382c0703001580b207448880341d4001d0b107140600800042850078170102990028016820801c400d1070710300b00700c0b100102004642500d42202c42c103405c13071070900100d1800e04040c1281c5500c8222803130480c2c1096260f0741c940726021580001503d40d0f510041090105100030310454008050303070300007414101d003199142 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 764838201 1250 764836951 764836957
    0x2214040513020d03140c1005010501020c0102070f141219140a02010c15020408030d0609050c0f1204030509040c0804050d09030506010e0c0d020d020705071a0f0c150708041e08 77
    0xa042026800409034117105c5c000c240d0314a007103904260341c014001030100000504091143d13600501c0342031719010440d4008103909040e111031a20303000c4d5080c00c0440303000358000e030141c40e1340d0405400602c1e04848130050201910700040b03501901b00500c0079040003c9641c0d07081540c504a900002040d42c0141e070050360300c4010540c0a030612215000700701c0250024000e5501441060000060040d4051120303409001980c0e4028810401c3e510354000c0c08455008480382c0c01e1810740100b11103800400030840e0a83d10520a150440c680740c00c00c00032074251854040464040f4400005000c02c0040a0021001895591418000192564541075600e440603c03641c6280c1d58014040344c03481c1894401c403644000703041000d40d5240502c5022000940c001003080c1d496001c3c004001c140030784140294887c054404e0b09040c10101c5200b0b46142503404659a103d4a1003100350019a040c20010750074480c00d8180c51310201444e01d0704020180807001c420425400d180c0304001d00000f2802410b07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 764839451 1250 764838201 764838203
    0xc0503011b03180501140a0c0e0d1b050301110417030304030e130e03030f190506060d0b01020c0909160b090604090c111e010b011409062214040513020d 67
    0x200748040708104600211005403c040c2c019420b20200080d809039131203a00b80140e0360013004204285d2100b5046500781717501ea243d41c0d48140403140c41d4000c0b800c254000d141907101c041c12110059a0b840c00a0308448c4030201c1040f400e10302180400402c0c0004018404030b04000e00514518909aa001000b01c0d145003e1036225282c0036400e0b00d0120110f03400440c06040700d0040701c0e075034188501685c01021040f03134000062801101e150480070b0050042500034407014190070300305001000700300050501c1c070f0104c0e0304500c42e0400c1310f4566030f641c80c4500e0203071058601400390740c04044041c0c00804802c8d0043e001c0007030204015065516034400302d40072130702030381c400107100168290103d90059071450502050711543d1000e1861401c03003006d1141c59140302c002001141c03524001950711895258501c9541c3d40b0611030340455003422801800d0311602c0c458039504500502c210103e00300d0803130b00548150821441d00d280c1d141021f1007059000302368180d5090000d00550300284501c112000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 764840701 1250 764839451 764839457
    0x71a0306090c040e010602031b0a03080414160f0509010e040f020409030309050a060606180b220305070e0a06090b0f0d0813081b01080f0f04050c18040c0503011b 71
    0x2e040c0c0d103001e10030344015101d40d080031161541d49010003950f07600310568260307001e070103401d001c80c0d02ca00004a4240e84c079070540380c401c40e9079520f4480b0407041c050780900c0c10a5006c0c05410142c141c2c0e580e45404050502d80345000b402504141c14040104416000f41541006c4c1d4414803010444040790050b01d140d04480100d02d10351585011405403404082c010014840d9030504002c11280d0b8001d1002c1c0c035420f0341c0350701010180320700c80c3d100d0b11100c0c403c01140e0001008240070220501011580d002d4104403410052980d99135603c0c42c1a88030380c0405e0048541000b402581c480c40d010340001800304000601c103441d4000c1c0040d405501c00e0481c80c2c0700c1e100410b0090100401c40c010342d061507201d0b40c00321880350350700c91259440b02058281910046032a502c1c0c40ca1030342c001c17001d070f9004070b0000440b049555a400d141c0e0303080c1030014101f558603104120000400d552420030015100244005e081d8072030a0904d0128032103030041d080640320b0f90504c032003051144252508401c03503100500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 764841951 1250 764840701 764840719
    0x901200f0708090603010b071a010b0a11070e0705070b070f0f03020702041e060509010905070903120509040207140d020106140613090516080c040f0e0c1c0c02071a0306 74
    0x407074200250f200d07212203d60801030120002a80319500302c081c1c03482501442070b80c0a4480a40d0a90344c2110090103070800d4880103105d2124901d118007000c1102c032414030121a943d545580209440c5e2404940c81070000c0c1001130f10904000d804500303141c0003485802c00c140390f100c3c84030020301942d000701c00020070140e001c1101004c0d56280d4012454000e408065200780843e800c03000300141603140540c070700401905000181203c440c0c031656100b07a200d9076440c0c0c02e1600b50742d04c040c0240007401c41441046014403014005640c0c40c8002d0140d640b04660341814000e805883e2401c2513112a42038040d64034142041008010320402094660802c40e2034030f41d06c9280d04020081e888803034101c020203d1800080100c00060700c01c0b00c0305060003a0302c6001071a0b40d0103001c000c1600c01e50207644281c3c040c00300200884040241c06a8100900e2100306043c152040211912070a99600201c1400d40742c0310b1842d24250180841d002916071003030b103101401c1241901d0300244c44050041130082d1559 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 764843201 1250 764841951 764841953
    0x705040203091912030b0105071a100e100f0b0c10021c140a0b06070c140607061505130e0601050d05011b0e04151d0718030b0901200f07 60
    0x14800714101c0c00f402100b001d1241110308043c6181e2000e0214040480e00e00b0300d92440a60140095605581e80003080c00c04160b40158400c41600c00a090042580c0e401003002c0380a0806909841c0b144d00c840740380b030355841c0c58542d4007040c03000564410703861414100203a9420410100daaa0008405070b00c0150b900c946141c18041d880c0c0300d41080c4c01c007207403030031140b583e43d14002c00002d400f0300480141844800701c0c190070040544640b5600420385030300c11808001400c455290400f03844002003015050020603140c0009803400c2000000d4550325039039081c2300070310b00006105680390300b0f94001c06c0b0901d001e2124968401040c0161441900e506000c041041000d400100c1a43c141200303480079100b06500c054080702ca040c101a00c12814010180800e200200008003140e20071921030301c40340c0c5800ba0304a0f07004400340a640401130080513030710103041881141801507104412101041c900005100c0c2150051800540b0300e4030459a004d000e00d140d0403d030b4000312284940c455460301a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 764844451 1250 764843201 764843203
    0x1407080405030909250315050301021c050a02070b010e070f021204090b06193212100509090f060a0207050a121205010611010b3705040e060601020f01050603070504020309 75
    0x44002e07810390029170206030386425604d50030132525207051080d40c0c00c00310388074800c05090b030145036185000c808044441d2602c070445504007940008005e82e00600d0990503403290658524240c10828008400c1c50074040083d80c45000382e2901182403016201c001e01101510216104c0d40c07096000658440e10712030500c0d40d0303440459000c40044031402d892540c00300300280c00b9112005c42c5045502041c9440c240e810a104000c400086254003a00e02d403c5012015642981024003803190580b1481000b0507261160007400b402900a00020071b21a42d003100e0b031500d041001440381c69140e005000a40000350000b407078141080d802844a81407000a100442d05c41401e0550122640c0c104000003800c281c0203007192046a092000034040000010140001c4544335801d00100c41e80030b00c40c06610042011044080c00b1801d080210303516920000941130302c034602c0c02030381250800d00030b1009668040201e0000c80e4445c4000380300c83e183c4003002079114152482018000c80c1c0010001c1d100c048 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 764845701 1250 764844451 764844481
    0x509011707120f0210020c01121d01060915060e0303090108040525030c081b060d020702040e01020a08130b060d0212011515021203010308070c030b0103061407080405030909 76
    0x50000d519128a04281402c1d009501241003d900405c08030308141192840881c8180218030181c50f605181c402c00c02d8503000801001c51001840c811011140500003002e00030b9000400d20b44d0b0000c102c2c81c0420300b0b100d07014000c03944184188106010f07185075503180402036440c5240242491444ea80c0d40e410500c5c101401081101c040302c1620340c55111080b0881101001e5a0083d0519141203848158007503aa0703122001c0d080d021812200880b5243c60640002d01580b002ca250141c00c0c64400d50110b8190f072030401e40340103241d40200e42010825408072081c0d9016800c10350841c108892130701c07000c108910261540c0d01404c4d900e0720403829500c078000c0041141d04440000c200304002d4405000900e061406002c81c2c0c0400310303000c0c200841c4005800c1c10705013030003105d03a491a4a155103e5182d641b10581c11107568140500000126000b9203480d4000c501554010503420400e60210440c40c0c1c004048409202a44051002045001040e0b50340c4e500c00750b860703042c039445900c03810121075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 764846951 1250 764845701 764845709
    0x70f08030a09171917161b0506010806061005030705030a060f08030d0b0328020d170414010c0c0509090c0301020f090301140c0f180307140f0306010509011707 70
    0x4980440d9060f400c44128006200012031450083d600101610048071041c5208507032038041e0041c1d1010802e6009682c4c000500d9445500700806600c0b907034200811a112640340644540c0c0016004102c040303818441c0661018003100c1c12a165030003000041c0c29404090110420004080002407444038140d102e82d0103000c0641e01076a80300d580b50022a0380c2d90105002c01e0303010f805c100f00c0104070308000500046502100e866031190910786180d201002c40400c1c810b982c440070b1444e603640407824030f081e08a2001c2c44001d0b06580c031803d140d454a400310030040524100092000450040341d0701c0400041907070011640c5d0407040d01c5072620207181c0000c05800d1a81540300080c140c8500c2e01c0306004144a10081e4000c7c040d10f4130742041c3c2042282c04a845000f440410840545080c808000804ca21810b00a042000618070008a45001032940007442c01c0c3d040800032007400c1c94203040381c6040101c11001040c19605080200e8880d91040c403d17400e00704005055840e103044c091040714094 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 764848201 1250 764846951 764846963
    0x30e19350304020f0a03080f0c0a12020c0916230714011505042a11010908030402090a181b050301021305090f0420010903080c0d020c06070f08030a09 66
    0xe4910208814040e501c181d07402c91003070b9a80a001d84450505200d5017003202e8001c43d60310705100e40c810b013a04044d0b210ba88450351038000c000c0d580d80020040c911414031000325600504c118200002440168900074044010024035500a224500d034040300803c006070b604070510300c8e0100702c074040e80c64500402400912a420b45c2d190021241d00540c0301140c15048507510581d0b45603a20f00f80002c81d0080d0880d8510184640c41191400a2108004907603032f885250a1449401c07104c025400c680541c001120607000000c1031206518000701019040940c0302000c00c020a49442c47d01c200c82c545e03042c01046c001c401c00390069400300f503501d054011311000e030007555030310807184c00f040c0c1c088807d004e5140700d070041002066030044a02456842141e006900300301c0c1101800e205042281c1106141d0b040000f011008000518884080c011000412000309440207001c0c1c0b003c1c3c1003000300c00304240516014400c18000c11256501c542d0740d03640290a943c2d40340c968000752405004088406008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 764849451 1250 764848201 764848283
    0x15090f0b0910230c1e12060312090108160207080706080907080105060120120a05090109050306090a0b09010e01050106020a03020705061201030b0a1d01060303030e19 73
    0xa8001040c21250412050400c1080340c40024442d00c4500070f09003001e2420060a001a00310110034004007840050304070400e4080500f460458041e03401207100c001c201c90680c0501c01e85007000c014080703024280c000c81d2420070800000080881c0802408507080b640088250480c0c40d0003407100c40e01901c2e40c0700684040e242c40302c034040e1800b0000e681d1002644240100014403100622030a0301605050791281041200e00c428011900359030070795003107039005031a0f07401c4200c00c01030010a071180468035401d4503004020005010040c0c0c0d944024060f030002010010b00000101d1070300e0145600901341d40d42502c1d2009924010448040c224100b0b6103031034001310f0f40580001d07031801034910940c200ca0100b901c1e007040c0001070050160023100b81c0034040042c00009c924140c1c1c141e1003805d50000051444540c5c066000c45656051550342e20303507442e0024014958035008140810b440031000b80028034808620450760006030101078080d00381002020b12500d200b49100341e84102c07071008140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 764850701 1250 764849451 764849461
    0x40f0f0605180c040603081e040b0310050112090201210603020a06050c07090e0c01030905010b0301141f0806180f0d120506090403020c0f01091802030405060903030415090f0b 77
    0x50000da10b41d60b4401600c66060706001e5480c00f4011102600c0d400320400781130030201403000072508100d581070140310748140008503403000c540026501c1075000384048102c00d403500b4009000040180c00009802c0e040083c481d0240c1d810015a200c0e090003140981d00660142c036950b4010081504001e62101c07400d14000b641c9507010000c2c044907100074080d81d000d140e688128404039070900d0850107064101000c10030a541c060303071180c003106021343c00101d1a400b090300002d00b11440c0d03103ca40101004601840105e0507e409a2008940403201c04440c0d00c3c28510ba10342d0343c2100802007541d940c83c2d01100c82c400307132082c8500300410640108503100118110009031654400502508101d441e00c1c000820b585400c00805002c0c0d0b8043e00a0115611a0030500041e14147c2c1b141e075040c005005400106610558050351114103040c400607241d0400c2e00e0503e0404030040e11840160f4000d0092001107501c11000380003170046240001010089450950407900d58160090a2183710f801004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 764851951 1250 764850701 764850721
    0x31806031f1410020a030c030c0c09140118140415060b07050f190809240706141617102d0608071403090c120f100b09040f0f0605 57
    0x1c00e10903030484142c83c0b600343c040c030b00700e90707906886a01800150001a00c040400d01900c0307000c1d200c600602c40350a0703071a1104280d1b000d5514140504c407210800000401214100b03110303030b80f90001c0b414030500c00071600c4501c205800f039014001600403610b1021000309400650702c458001d00000d0b01240d1180d4881c20301648071810031000c65103e0203007101160b408110303c0c6078240c4940e400502d20f818025044207208104400f2608281d07101d0f1590980c0c03158102e80801380641c0ca00c01d0201190441c0d06a40e20301b00283d000c2d001d00d6550300801c08030103680742c00c552a540c40062032482100c0300d544034002c007061011603901042c806028980d20b110600c400082d0313000100328040508080381c3e41e40034210b80000c2c045442c0400501202150b84540480320000c5030002d003400111202d00510b14001002e0507110070603c25168021110540520028802c2a6980c07188010411140d0106c0e80410320303040008100420544c04018140104144c0030503000c1420b810100c01c03c21440d0002d00c403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 764853201 1250 764851951 764851979
    0x1020705150129030a0b0103270510020301050d030f03060302210c030a030203031504060302060a1707020303010501090608041a150a051e01080903070b041a09031806031f 75
    0x2030607040d842600040e240e01090f8510780703c1c880480c00d289160354001e0000300402015039054101500e943c0341d1440071407048113045403600100c880c91034444141c03070080d00e494070145207201200c0c010b1004202c1551054200000a5050b052181c0400c003150390440c014185508020b50011402d04a030f081403030050461400c21051a007283d1300c80d56001d04140d940d4445003001001030344100000303500c40c80d251150340c6e0b16460160000c01c0703081d141d90000d0082c0d002107403018001203440c1d1000807400903c101c01508a100c90014600c1c40d410a800205040e005004100920400c031001c1403c1240420541c0c4a80302c043c4554040c0d824001c90300e03281442c640072154461038400b0300c086a42d2500d060601d80c8400002c00c404070500044005480240d80104018068007050150802007001008681e2241d841100034081100e4548014604130202408940b001d40c01480201c1401c002907000720f0540ca01161850707101e03910640440a1503002c0101c4440c081a141030000f06070340a1444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 764854451 1250 764853201 764853209
    0x11d0f131b0807151d060c010605040912020d0c030e04020307050906030403091401181a0c0a05030304020a0f0302010f1110020408010f0f0b03060c09010c2112020a020d030509010207051501 83
    0x9403030078070311604c41101e101d04010904d40800c107690307034145291301e071100007031994048003c00460420786c0d500000d000c441e1001c0341564034002864000020b40d03030610101c2040405800d04940001c0c2946000b0301449111496031700596000002c104024004e0050754050040184130030343c0d03803800d4a0014056500c6e84503a05c064440704040e68125070140003a02030b09000c0d051801c01007072403c5c01c8016448401002a03003072050411035504510410301c052828240280b0056070b4034101071052001d1700c440f90f40081c0c2c8044103d6402d00060b0781c4200304044803e41c915210094080307030380030b007400c005200c146150709610005001900302819040b0074052039058108001c4003410340352210654200340d55241c3d16822030300000d0144c001c0d05d00a89007104040c035080451540640d142d01200b6105540518103244000e11041d00703a80c0301d10030402d1141b1000040d0306140311190f001e9500c0e20401e2460b001e1540ba0030000c0c0c0c1d00282581a181c107690006c00301d800e2007210001800032404203000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 764855701 1250 764854451 764854469
    0x40312060902030c0720030703140d03050c0d051512011a0303040b1c0f060e0a1d0d1407060204031127040f0312090605011d0f131b0807 60
    0x200050700d840030720a4910511403003552a00d0000b8956402611209110042010f40c4103544a003003030f52420005072000d07510501503055007080c01000c07640303010000e20250b0f0825050500f040504c11541055880c2c2c40f04225012526441d01403411100214a0301116000401d5140d09400120150403d10300498804e011803021440c407018982c880c4580d01444058841c2040300f0303000500c000c20107816007403c0d40c038002404504a580c3e181501d0f0390764456215200c0c03100a002c40e80f0005d2182c076101a00300040440019680313102140c4510f40070300b0720307410301c40c150308003542e03a9800308200c6092540c090b2086544d01d882c3d203030200464100d25150342c050b440c0c0c042c0e90003104c0f41d035082c2d00d074511080707440780d031580d1342e480c0c0d551003a0481c8040100c04204004010306c288054602603001c1d2544204001318071517041254540d40d801041410700c40d000b1b00704003030008600fa00c0703103030380c0d00020900c04070074242c2101d091014000c030440007840244c10f80c01c10b00041e1103170f02042d00ba0a07520500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 764856951 1250 764855701 764855711
    0x1020a030c0c0b01061404090516260c030a09020607060606090510080a0f09050f0d1b08070605070c021008060112020403050d08040302010b03070801050f063a0b040312 74
    0x7010407948220741e10002406002582d005000315401000c4400340c000c421040e03145415200c5407500161201945c010050340701c80407003440d40b240c000019518202204484000340f4186510001c3c00380e0003d00b1201c0981e10000124540302500d4100010064000c0e200c6550b88031503107042c4000b00050b1265030001400c050011030b82c1d00d40f140124101100d03e0756200119100d0500c1c80004000201e0b0042c540d50351018403100040341071011041d1061030300c02a2000c00c600b410090041d54205821400043d0150303400b00005030248281e03900c05d47c12072400103d035613400c6030a4403a21180c4c50080c0d4070100c0240d00502d42c640c400303205407040ca401c1e80d505503158514107154080e4010b03030000a11039040030790801c8a46101c1d6a155a1060281c40041100f1a5400c00319003464026008081c2c80c0c0d448200700910302c03009611094000c50705031200c8031002c40340400d41520303c07104811400f541c0c02100f002d6125003a401c07400c400b07294100030b2690342810316140143c6041802030003440030741c1c202 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 764858201 1250 764856951 764856971
    0x3130f06030603022d0a03080a140301060207120c050604030506100e22111306050f060c06011208090303030f1e040b06010e01030204033f02030f070203150901020a03 73
    0x24001c01080b264058100e81c2850040c0c01280300d03000142e4031034400081c5000c0d08805e690f4801d54000c0c000d50188c400c10740e98480d6140e000300486920400e4200d0b80300108010480d403030303000880740c003124002c06080f00e00070110300e00f000060180d85d020942c0501c020a020062001c0801c40601420351652400d0b03240e51361703400302c2d003800b10100d0380108589454a5504003002c492110113100c140700f0f20064080d2104080001d80c43c0705070626907007070259a10307801d0000d41051210a890010110350150800701c103070944c00c1d13407540d05020f6050364101c501640001c0100000c150380f042d800060170b40ea124070b0182d4458a104c1000c4501c02d0201c090100060201a8140800c500880c3c11030a60030307082d51114010b59002d034030540841d041503404c10002011495511421200d05099038403081030380b04115091151480c8201000e03020840c50404011403078000003200c0030f410f41d1045081d1203a5850000070b05011003000071201d6070740300008011162a065005014014450300c0c108411609 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 764859451 1250 764858201 764858207
    0x190915020a020112020f07050607111504080301140d05010207060507030c0c05070501030506010509030105010305011a03060c120613020310051309020102071a070516031511030a09050f03130f06 85
    0x41c00c00182c049446000303c2d80040700544c0090039444901440c6c2450102d0540e42d103480c10380120f034007000065510100b029001000c1c1b241c0e8000e8107130307816809400e003031035182d00409100610801c640f03019800e000c0781c15074544035130841c4443c2e00f001c000c5464540d14142207000e0304046882000181c94030704035104060090301da082000d40c20600500005c0c0c1888010360013004003811103414008140101c031025642405001d010750721540c004500c0c02c040b0340e840b055013004441c03454420340000040024001c503640030364000c9154107110180a4940502180048030454403080c03600d400041007284d079001d007284600c101c1e14241c41841c0c0307140050745071008880d00018004e0050300058020048020010807003074055808100301887c00030280d584902c0c10002c014031603654140003004100340803104000c40d202e003003040014031508040f020601c0083c403000740018500c0b5034901d021410305c6020052040440b01840031250703100b284400021040c40140704009000740c0728080484c810344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 764860701 1250 764859451 764859463
    0x6040e070b070b042d17040f330c330b0a0911090d061401061205060103060e181c020c0a17120c120a080a0b01020a051c020319091502 59
    0x540c40e817184a2610310fa603201c0c80b50b0403000c0c6460800703250a12004c1800074480710040e0041900c034000e07101d42c0018069030002c422003140d011000448102c0000685034011018904499200d03001c80b021031040b04844a2400c034030001030041d6060110b1340103d0080c641e110340410030044a5902c800d5540c4c1441c80c059400201002450074420300c81e1600c07500309500301d03000d03242c03003042c01069081c8044e141d600d00c2d007030981c80100000d00c8410a800e1924080c8690707500304e2020310b0184800c90614a00403503405d0b01802e0700441100c000c14014003d9014840703100d09840b103200040030b51034031040007540c0d9802c07418070902c0354000c410000b50400d400c00700b051a2001c0e501c050700000b04103000d600c4154200050140f00c5005122880c42417068050041404011a80380c4070b0780d038202103550320200c0d0541042d0742c2c10366005000e414089440001c001041401c80745009600061340351049055014224601e20381c6030400701e4000002d50003c41c080151422420183e007410340d900000c030390b20a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 764861951 1250 764860701 764860763
    0x120b0103020f0a1a0a051b03041d15010f05120a06080706030e1b01120509030a030e0a02011706010c30020304060e0d2111010606020a080306040e070b070b04 69
    0x1810700c034002440c184d540340251120142d581005410704401038440500359102102150403500005170500c54040300000c10600c810394620032007078600d000440501c1131890404034a040c0242d24140d200c0c110b10980031591a075980980fa00c05505021071404040d00d007034011110306010f81e0f003022528601c00d209113141e4016440080180b2914042102d07400c2000da40ca403410040050140741040b00103000d440d0080d44804001e540c1c07040c400400800700d072420340c5400e0b140d07040f0701c0a440250b030303110301c280301400ba0243c0803d40c69254040183c80718591410001c2c2003c0101e140001c2c1d0351709a04414004240d299602954241440c02c200c3c6c99200301d0180c41d01140100320610424208048c042c0d0009115101c0381d810881e45800c0410361515210b01d120019891107200d503007181d020700412009150b2800240301c10816640c030040140801000302e80159915000858030314000c01c003079401020403141481d80c3d00c141d070600b030f603680d4011142a143d140c00208820700381c0c401405c4101a00b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 764863201 1250 764861951 764861969
    0x903020c01020c13050c1225050909310b0117030313030f03110c01050a1506270906180e0a0305030c0711130e010f15050613120b0103020f0a 62
    0x700441c0c40c04040200801b5000c00107501080c458452104403039854180a8007844803083c0c5103442e400310070540914441c0e810010404284000700d01c40e140c00005c640c1210080300703480c680742c01c2400112500185807030b001b04060100106e8005010b003d017649816642d144105090346004084c01cbd80d6244400e43d0082d0702500c018aa43c004a40301c1d600c00100d80e141c5190101d80c8044020507591a03030070401030030b44180d66440900008151500c035200c6c00c403000342c0d0004d031102d18001000d810001071188891b540f03400050101d1641c00415410005491580301c01c1050320707180d03010707180302219204d00707142014580a003500480b240006c503003170710704c6d89075490720300d15590301a0011036500088030031940641100c1c42c007555503070740001c001c00c020a4880c00003203007400140c6443c01d42d02441c5687c0c0c2000c0c6420a40903181218045807401c0d03500544072240d03200310846058090070059800341c60080d0100314004200b09108034014105c078000c0b1409640102c0d05010095a031002d88582011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 764864451 1250 764863201 764863219
    0x603060108040501090c2c040b2e0b040e01090902030307020f2e120b030604020d05072106050108030c280c080f010c080903040603050a1e0903020c01020c 68
    0x180d84661045a8014402d5001045000c04c030355404507007440036084104008038a0760340706a5100c403d0008041030150701138162460400b41c54141c4c03001c201170304c40300e901d45480301120081a600c00d11700b20b40440e021100c80d0840c2e602c018101042c6c01500504050f0700e48400001303091600340c01001170164001303014510f040303859800c11140c445448429600040401d01c079210882008c0c2c5141145a201c403d07601040390304002c002c11a00401c0280514503148c4080f000640e1800180e0540c042da05591007803000c10a0b00703101e45444215405003010586490918102c2d030526203810b0f00c0c8600c148428441a601c400905440c0c1c0910010030340594010b60111400344050348100031010880c000150701d14030961110015485a41c2142000c2e5200010381030280d6400d2099205c20300b56032816841d0343c145008626101d2265204040c10551500041140e010751540010b208a0340750b010307401d41c80040c00c40800688030004c1d0603000360081141500d4154000315604000c2507000300f81c0c1803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 764865701 1250 764864451 764864461
    0x90331060e041b020106050108060d0c0b2802100c0903020904031d1810090903020312070201060e15090105010e0f04021605030309060907050f0a090f090215040602100603020603 78
    0x241d18208000c07055845a1511041495450070581d041c0030070405a0002c5003036400e043c0058544880500540e0003550200807120110b451881c201c820b0b0b0f07015142ca03641d100004602c03506d20012185000c202d81c820301c40204109600003d0722060101d5844081c000d0408020b02034038000394501c00a50042c0141000400083c440ca10060b40040700707070700d460500c000e05004291700e010104044002c01d070000003030008492406040c88001c114501c2c040c000e0491507038009443c0d000750345194011000c00000704401a0003034200f2005080100041059450078110410125a0341205103004440d14000810254400c00c80003a48060151100c0c0c00541c103d814070000350300411b4450203d0204000f107000003101440110300401c58600100500d04040d0815806e200d415808540b0130f121440c41c01415803140c00d00c50341150f402000c001000e030750030f03620711000e043c85060080d8070038081040800d03050144005402622016801c03291041500d510003000c9903006d000182d031048082c00002c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 764866951 1250 764865701 764865707
    0xe0c030a050405070e0a1a06090102030f0a0e030d05030609070f090501141201120b010815060d0302160e07181a0702060d0513060c0c0c06141209033106 67
    0xd4200f481581151005036503030541c4d01048000b030325110704031503c1c1c0c01e405519910588085296803401c6440743c0c50070f840000040e540b4450741914010803040403c0140101e8080da42c503010425000d42a294519049031000302680e00440f010b030301c2062100c004c00c81044c820f00400c0ca4404c405d80303a00d50b072141050015100d0707680c00780600d088020104407241204804201c0e00d4024003031041030302041c06040c68240389086050b008640180d011718246444903036040c0880f60001811344802c1c900c40d40354141282080f04461080c5007501a549001503500401c81081d4442c00c2e40b0391719035850783c0d03040c217a0540107180c62044281948080605114012811006010071031008007101c0c07411044803848002d075101194039160070041043c140301449000e00030442c003041c00386005069092159100e59202c91640540c40810a600b0400d40b01780d96510211041444c0c081031030070542c54034602c072503500d500c03e104000039104040207000c0c0200818001031a8489000e801100340d0341405412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 764868201 1250 764866951 764866961
    0x9100507030f050c010204031a0928080d0221040201030e01200a05190c03180e040b04020109211407080703200d060f0506150720030d11070e0c030a 65
    0x4c0412558200400000541510040508003206014000346484c003040101c1c14030100c00b240403125043c110710310951310003459000c1205c0d94030881035a00c4e5142040000300074010040340c1c0341c010b003100000b080030300c0c5210541c500c218800d907030a00480800c03d4036582038440501c80c600703540c01040d0000c09005000c8010300410400c82c6000c40c00e003030070010326600c100414000342021543c00704020b07040c103070300c642c00000a04d80c4002580c40603140a508011000c1e0003000501080e07480c030081411684503d1008000307001c0f1b4400da140200704085d01800304840c0400c1200e85012521034481e20840209003c011101100d01138040b9a145448281c00741880070744404106003400c00501107540c4e400202c0202d540100400103100040300300c1c550480b90302806c42441000e045a0f89000c440c03d240840b95001e500c25080010b9000000400d400100032001c245e526024280c0c8036503240b60701000302d112071507418003129071035503a404a900c03a180040d50041503101040000030b140421036000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 764869451 1250 764868201 764868217
    0x51605042102040c0807020106270b191d0a060e070c051c110114060a060e01090504020d0b0324182a0a05010905030a1115070809100507030f05 63
    0x20081800709650300180031240340f104000040790201341809805642485120058086404900c0c2c000001c5642800b040c0502941070209a4403131856140c191110070740040c0425044401040d19525114180e985940a2803038285040c12800003d22654041c004d10301240c3c1c4c8156640c900707844000c4212001c1503005d505481d14814071081d40301c0c0b140d1007a8a4210700b991603440038082c5407500034039030a5408620740d00801a840701d00b84913056850341203940803144a800c0140c0c07606c54010041c1d440c103910f40e00560b440f920101c1c800c050452550408081040110b0030740302e542c607540c500154031041c15000b290000e420311001030540351000c801100701ea00d604003100c2e281251400078040c00540031800d1400c42c0c5105841d060681403200307035900606824203000c10b41c5418030000c0383d640c0c0949540500040d240181001076a1205079002008032078142c0d50583d54030143c01d0012060b4004100b05004110f03031301c42013015a22403400d48500f550304d650350005503607140c07000300c90507000500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 764870701 1250 764869451 764869499
    0xf020306090a09140a060915140a0e01060803030408040302040e0307030c0204050402060409020c0c030d05121501030207051501030312050103080a030507120f1406030303010b04171005040308060405160504 90
    0x602200700c100c01c05c032046a0354403500d400300d11301001d841c01a04000384004006003482c00c1075841c1440255002d440e80d4031100030b020000b1480e4115800a01416a680c000d80306404000123220622400030001d000b40c90007980c0501c0318170b40003040948d40b03204003040940007841c00c5800c18014601a002207400c540003c14542c20b02383c48440f400100d90084080c946d5540c44504a418542804d201f4108400315900b03219003030640300245504a51802031111848042c10001c40203181e00a5055a1030640c20004480c020400820100300401082c081a00801c107051200020f6401501500741607950000781d040c00c20441d00800d034068140904000e0500c90060a603843c0c40046100d006c0c020300301600d02180e0869412403201c41520050001e90080d00708000500000c4040c0045400701c801031042501c1e0b64900081244c1881802141c40d80694188020700003810381c4000b2541c00b90100b140c0420494440001c03150030040b02ea0b41840101c3c20a1000300a90f40300d06001c101c814400744 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 764871951 1250 764870701 764870723
    0x902010c060f0218090601050a0528090e0c070f080901020705040e0a1104150302100908060f0708070908060105011d04020d1d190803060301021215040f020306090a09 73
    0x41d40701c606442e600014a0b440320340c0070409000700003440801281c814400d845283c51800c1c6130000030a03600c101c40043c001d2003c002501c85e1003a010360380c50030003580300320180c4002c08860301d002130840c8001d00c520703052119100d0124801514030400c452405a0180340c4080e00790f900d0b0b0704c1d00d5864014000950540c0101100021151a2400350000f410703900d40240001c801103150000c2d190b2143c4580714040c0d03160060b0030f046400d503019500141d03501101c0600450504810842d000c4400341c1120041d4080c44050001c0484e0008001d8091040c036141e0008a50324480210f4001c521032140c240e486d0712406c01040194081e414040d403403e120310382c4209034203c44000c03e0a030381c81234020508465451102c09000c20b607000c1d002400440c0700b4082e080c50030714131500800e4444010800341903800e001001c184103540c254122103418504400510a030b10b088016015045548944a400349060245e41d02c0180d08520840788140001810700401c1d03120081c00c6002044501801c4584c40d00c65 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 764873201 1250 764871951 764871953
    0x10804140615121204050603062b171c020c010204030f1a060d0507090f02070501051014040c08010e04261315050304140106050a0806060a0b03060307090902010c 71
    0x10300509110b0460300030016507220b64102030150380b0118640354602c07904403030300c40c040680101c811907003161821100a40c5940358480001c0007400c9030885407030441c1203288060b80c80302204428a6a00c2e018140004290081d03d03100103007407007a0f007006c45e0042d51040c040c1c038030b1010540c050a01200d0b0200010300700780d280c2d941c01049900881060300c0e640320f03407805040300c16400952507a00c00416245030000758215500d15540341f50600070303c0310752620340e540102d4200c5d00c1d40c152248241c0000091046003070000840d072400241340200e50805000030807010a41c04c4c140a00203144030b480d501c2407100e03880c0c00d0001e6148000038004a640d941d280368408050318481030b030315500d03c460105950342c5a907101c921102880d00359005809d1907045401c1901c03000d4012094980c003d8024200000c0c60816004050041c81c060700003d60002403030300045529440043c4040c407d000c2030f2511141d0603141d224000f5140003c40c0c8031641644810b00070301c0a80e683e5040511340501c103041400e105c00007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 764874451 1250 764873201 764873203
    0xc0a060504050f0a051b040605060f0304110d1b050402090d02090402031c1d041803050a0908010e0304083705031e181e010513080106030b0405150f0601080414 70
    0x1340c2c0300280c8a6500c08150810342d0100780e416000700c503408035010064541303008042600350191402c8030545807c080001014030a51f030b8511100e8040083c403040654140c1d1034185d000c01c040e0507035201c80c1d6540100100711070a140c801c560718070384010807a103034451941e8200000c1d03650040040340c0500401030402c45809850740460030003881a1141182408181d0400d0341e198116100c540c412805c0c260307040710241c0e0740352680e809540c051070400d50b500c0100301d041d00e0080c0c1d180e102c04020341c60310021001c161400700203402960920026105400c1150301e41c0700c9510800598034241c81001603c0f68421010200c0401a4500c40c03010780f4180700c46c4440900ca20258100070610340c810024600c2000014403001107003440b021200303282c0d03100c0f070992103250b1070038104891414000c0000c0c4c0ca510602c1c0d00140800101240002842800d41b01c1c40e21080021003034400301c0d00351041900c00c08020700781c600e0341c038070980c00020300385403d0f82c0e480011940c0040c05041950b1480c0c000e92881c003002c0e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 764875701 1250 764874451 764874463
    0x60903070e090109050d0c030503010e15031e10060f150c050105011212081e090a060501030f111c02060a1716020f031614010b091015050c0a060504050f 67
    0x103010b0000203508a40d0303090032401d0941040c98181002161126000040e41000c19241514140082d44605949400102d0451802100d0150b414170070f018600c4110603404020f59a8004280143c51038504d045070940180c4506000c2e00c1d055009a00040c0f2442c200b42000b022400c01503c0c240b0300d0001161502400c6500030780202a01540c560391071414003112244010f40d00041c1c0c82d00c40560f160500114040e208450f034001c90751041c1c080494400a020062a00a00e410000401040d6901e280c1a4003998501404940058040e034032314040d0700e030164000b8000b202d03541180040d03c496a0030410164010386401c402c3c011109101122401d030b14170000d205070b203801d200880300100308030040d10f020514424a0041e030b100300005503001c01128079035030203250b000d100a0a00300d0020095030140014a180c0ea0300f005c100317030400544081c0801e44004444245082404920100c01c1c1201e16126032a100001c1d41e018400b002e001458513800030741e02c41e00813020350b84880011310403542002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 764876951 1250 764875701 764875711
    0x20a03060c02010507050712030c02031c06080607020a0b010e100317070203011113052101150611161e180905150105030715020c0405190c1d060903070e 67
    0x3a52007040180540d024420780390050318600b841030034626a03a541030031329866528004201034485109004041c020415142d10640c03003110805100400802c2d2780041c00d05104040540c1300e1132000c64845400490b080705d0544e04201d82c00426030804884000381c2001619010045420320b100001085030700107444902000805c11a554000f2070040600303488124088244440c2c0404ca0681c0c2c004100729135400302c1e9410340b0090b40b0f40c80e455a008802c00003204828070300d5400c0c1060b4080c12525443d17031405640d55a02d45140c1c0240492010341d552141030b0b410300304000001d07424840c0841d01980c1002e08201c064245121a84407441006004080380303040b440030f5103a40c41c2104000084c821441e052901c0034204445614140019a88414601c581d2010424022420740980e200344410140000d0141003807082e070074400d078901207040e05040040503c0c0c1c85d0906410919100d10701c0c4001880f0000031641c40c0500b50400c0155a034070031211036a241c855400d0001e03200713007000c0416200d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 764878201 1250 764876951 764876963
    0xc1e0f0606053d020102070605070e1206100603180f03030b04060503191106040906060906030507030203071413080a0803010e2503020a0e030a0b090f030f090402070f020a03 76
    0xa00e1914041c02840c0c00c442108407051241080c040040914610243c3c0c2050f02c1c10f04011150812400c099009205010001d824641444100044160052841a142402901d40320b0510000706070840e204c0c02e040d50401102140d00404001c12071080c0c11080107881074074620303040800a942c459504030741c084812008030743c80b154000c01501d000d100f280000c001c2500501000242e0030a030881032130b5009401400d489008000e040540c0350007040d5400b41880e0314080100c2d54071440042c0c580314803031203030f034000906140009100c244a802030340d001e07a025071581203112292240410554001621021907616000d00004241000b00240c40c545405094402c0d52541051520040004010524001c0b0000620084402c044400f6120055051031400503140c1c40c2609003110417110b95914141e0501c600e2150105100404486600410018046030326070070a49854030340300d001356110002644014000301100382440e40050180a00c02ca060301414071881c2d000601e0b4000c90f403c103840b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 764879451 1250 764878201 764878211
    0x602131706040f080f031015020c01020c1e060a08040b060406050d0b0c131715010b0406032307110c01080606160c080105041a1f03020609041b0c06060506040302010c1e0f06 76
    0xd6005640791601c000d00d618802ba00b0780001110010f56242c000c401028003441021a071494079510750900c60342c40000c01400b50340d44180d0a28014900d8006450544000c000c0c400400d6880c41c1601c22002141d1003d4841c2a4100c1d540d1202000c80400a01c01c05007503104002c1224910981c00c54040a020390364035001c482c2c070035045007524014070f64501030044c5480c40018801d8010850598048500f58680030460f1220107030410200b0000226084507103580341c00f40089541c000c0d560f1107007060305400302d8012a00082c01140d503503401f928103681001007004016200051084102e00c1c550144d000700c044555140c400d1401c40303c040f5400c3e180001002d903030341080e1130140040ca42188030050b91040b050030b050403500e9030580794032009106080010300d03825282c889802c0740e0890381d024aa031380c4401120301c1010308040710132001141d10038949600030600c0e00d0003509440581e0f4041e940c44040d054940d0702c105841ca100d440320040a4040004e0400250031101500541441404041a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 764880701 1250 764879451 764879459
    0x180203042a08060c12010e0a0605040f0b1f0806041d160618060509060d140109020318010603050a020415030c060207060801151d0402090603040602131706040f080f0310 74
    0x1040080c040d01000f1500c0c420801d642018214641d801d0550715404007c22003600c84401030b0300248910b9000640142c203024072114086d0303a540c4000070000e4240c406e512860f41140103c0328860348070040001290740303540031030424140340d4000c44010401840014005602e404c5107032604408003402e00c0c80b07a0140c030040c4903150740648008a83c07850554024411810040301a15134000c07248030500071840807442d100d000d4001e0b045001e046913000b00e42c0702d0558403401c044000e5841146c8201104200c020410000d100c140302e040f044a41000243c0f2110714990f00300006060340c00c800304081c1d182e01c200070000c1071038503401d08010141c41e0010b0050170302d004006085000705034009555101170450100c2d039282c0081049944440407040d0309005014000024001c0c0506074800b030700701c6000b10410041040c070390f0051908a182240034400e2030303134a080556184880340c8081c0d809401500115000401d050154031081d8401e8502a00f0f0a590004c0c41c5e204d5001240c459000c86a2200204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 764881951 1250 764880701 764880703
    0xc0c15020315030706081b1c05060a1a040b0f19350f1b0d0b03102703030b1315050f030d180801061706010b04180203042a08 55
    0x1041200040e00130384840c03071805c1000382c01c40c04000d181140c424801c1c503103400a4600b05044841c1e08021000c4150341c130b8906500e50005040c1101c249010f69607010300400c403a00036815003e401100360440130315140c24040362210503080796000c010340190911010042a400b88020001080e4a544003265040c80501b00d150f42c40100700441c101c07145081c01c1541d04008150481d500070031601034100e26483e180c005140014032218a40103244010540c904644c8503a00041e2032000f0441c11038a8410b08601503504660001464424034907403800c028620b0b0071006a044482c1d4000d00300055021031950100d001c0621035203060320521b83c1c8107854000c10040e039260501038441640c5010b00c400c000408a90f0b1501d41d22003180500440c2c840051000c2c43e410310b0713007000d04100002440179550b84d84800480c9014000756607150b0181500100e40180b01e81c050700c00700c03040c058480400c5401e45038600001d600281052b14040c59a0308402c10403814070800400c400740c40c112250205203000c26003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 764883201 1250 764881951 764881981
    0x41d190605060f090307050a080d170106051903090503030106050712030b06160228031205030405031e28020c090408030402120a060f14010501020a02130c0c150203 72
    0x910952400d181807040d82c403000c1c20340c2d0056110325461681c60369800000307072500714607900c559807001002c0710106102902280c0c2c0d035091b200365200c0c5816a42c40c840d030003051403800d004901c00a90244081d180c4030070784040c2181c00c00140c4c2000107250046442e214115031090b040b001c046000007850004000348404d140d10580034074641007200380340d6000000d000e40b103104481d61a00c0031100c0010306550301d2101c4034840490300c5051100303406007a0254100007020780b100761207102c2405007036414180142c045a21a0394401e000d5454600c4520305240c1c4449442e440f014618407d002d641346041400c4d000301d80c501c0080e40406a80034450710001e2030b1070040c03121207006401a0081c80009a0390340c1c02d90350042e90458122807803c005418203490109100b4000d4a01400d00312145240c00c541d901030000c04200312650b0315540e8a82005a994140600e0001e42110000140d035101c0180c660142070824064984041d04018a845043c00c010342c000e29a215980d00000344031000e1500c0100b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 764884451 1250 764883201 764883241
    0x30c09080604030903060f0e0102181c1106071403070c1502010908041401050910052113150b0d050c030c0118140301090803010306150e011401050f041d 67
    0x401c45840e01d40c2c0c0041c038016440c030000f010613450302d07104c02143c4115000818400c1c4500001c5440310031600100ca1071080c0c0c0c1460501441d803c100c40d0300c14620030800114000d80200001d4a4400d01c54140199680108001c2d2000f03070350070a0059081e079050008121f414020400c6070704e41e03400c0004000919078149500815680751009c0c440004503860161401c4a0085c6540149000d03103c0069507940b00d400030b0113a1007081402c0c040c0509403c50044e00040c2010390703c00d548090b071900004e00391003064407041c0c4540c043c031054000140b41e000c1c140d4590841d1900c0828861200e90202d6015040101e08483d03076040080700402a007420044c5451882c02441c0c40c1e581012041ca00b01108003c600a04209502c880a000402d8400350003c1028992085100d41d49680d0313410944020044c8100701d003646001030400080c14241885594141c41c11112a054040d040034019681503105d131882078a809000e01001801e115080c03490002c081c181301c0701d1052894108800c2c6010404c14507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 764885701 1250 764884451 764884453
    0xf070516080c1906020d030e0f06010b0c010506030a0308160c02061c050a02070c0314190602070201110d051b0a0b04051c0c030e090703020d090c051801051e120d030c0908 75
    0xf800b04944d40d8000f4072003048009900700080c00d044148141d5040c107401c1a0411800e00c140c0000060312000040100801d041e510700800480e2a10003c140c2c5800d40b094000e000541c02401044100c5502a48128444c020342882020f5084d95404210644c00c110030b0140342d0110b41c81c100c203900e5010b0081d59400020740004500d8071005681d443e80303a0800c0d0201800c081ca14045041010300b007045220144200500c40b41401c800900d4114083d40c4001c00407800a0101000480b02e0f80b00000c1c0081a0146901c03000d080c00700110301146034410701c40c0090076500c44d040d190740119841c0e540a80c0550301400260440c071421118440ea00c0e81910703010740030010011480000305e680442c4040c0800740440d511103841c0c6407035504a0190050460210802d85840c10030b03010026024010000c4400a5450350b031890004034008404070424031805800a18107403045984c44034a900803c0d42c400c00400c144415401d410100c0e10740155444050b0101e0313591444e0110407034205003c2001042c11130 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 764886951 1250 764885701 764885749
    0x1005060d05100e19020a06030207080c0a05031908060a1503060b0315240a0e0a1d040209010501030e0309061e0a09320405190908090a05030a080f070516080c 69
    0x5e80429a082541d10404081640c042540800c02c00030000300e6004104140444449140c2e07810640d869038418038010518179248049018428061126a886040002c1c26400c0c280e180ca40103117620f608a608444c1055038071400031070b03103041d50000355016411f0740d140084034800c41c1061041445440811500c1f85401114010340160054215201d001003440d014407c0a040c80108000080c0c9801c0002c158003202d8018080016290081e44500e00071101d249a9981c8c410040d4215079420b810541e142e00100140e821909048000306015504410b2110402c0090342d0b1040302904842c0e0154001008d800702041075801c904880208884004850450406a90f91007020b8180519040340079070784510029151a01d11001c41e80c0c40c40d848ac0d028003200340c0c24941030042d0360000701990302c00c0c00000008281420009000300341c3d181d20191107850b0000601c41c06480d608070307820484552107407028624000195005d50b02c01050290005c1192079081410020008800014840041c000e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 764888201 1250 764886951 764886953
    0x2070c030c050108160c0c120b070201150f092c03180405220f06020a020c03072c041110030b03100507020d0e0604031a010302010f0c0201021005060d05100e19 70
    0x3018400c43c0c006170381801d81000025140400d10001d0a62201b1920280d103034110701030110f51009244a6003a5500030440c0c81d80284d00c15090b80c1ca01d001322107604041003010300c003500ca02e5210803000c000014683c031081c421121001c4030f01b0070f03081801a13540c202040724051200c824100203905c4034111814000c620b04170503d04601914206803402030a001424241400450341a0081c21a00044255074680035208040d56915081807128041d1085420009000b186004101004411113103404120140e640c02c1440750507028000b99000888084800300960b02c03603201d225044203546021621800380c0c0d0415003032044052085090030b0510f410040c242d0750102d65281007402ca803e159a81c40d104030049603580c05544c0000300800700c000f5801050810849803076040b28400da0b105031441ca2024811200c052203000001c1c003507808014120900300094100703a500072000341c20359000200c191945482c2041e5542c0961625903140c21407011168140501d18080f046048803924103091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 764889451 1250 764888201 764888221
    0x3090209150609030f010213080c03031b101404060606051809070e030f0a0b07021b0103051e0a1e0209030307080306042405011205060105030a0e0c0402070c030c050108 74
    0x10040c03401030010010021088690380d510140d80c1e40180c060101d40824102e10f05d1513001394050802e0080f030303514910000070218400039031801072200140266041022110801c0309080b41001492401e0140200303582c0d0490491040b08c0340c00c40d6a072805401810b19081c40707001c941058001408122040015040c00d4007041070025901c902550341c2c007903e030f44956003256403800f15241580c1c103006441e48001c1c41c00d000901c803000341e03016599030070313058503101400c0c0e942d02400304002244444031420002b9070f40c0039600c0a98092035945981c11a5601405507001c8803000b140d00302c4416a94881046000c18050000e034034403091010308501d00b03004400000d41d030780a2000c1c001e040c2640000010015100c2d0b070070860012400741e40746031b002c940304501003030210a240107003400520b03044054565010180185801510183c43d40b92964031070801c404058010440500f525102c0c51a000d81d4035240c0d4402030582034001e04214907010f00310715000e5482503459010303604100f421000e105070494 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 764890701 1250 764889451 764889469
    0x1b02010624050a1112161a1006030e030706050132180c0408031b011a090c090117010902091221071403030103030509040f140c0d0f06060f0906030902 66
    0x107420b00300b468544029071101340c5802190300050030095000320300b201c035892140d0500145030303200f03074144100344441c4002d48103003450458034031341115421107003008158041d902600035121680c09a078908422915107006446007030348548480b0b10f0001c4006010f240515280303008454581031120000c115500060310321200302040c02c42c0c48001e80c003042074110068100c44c018403900d4107980d01d6500100020740d0017845134403450707429401e20b80b110700040c00301000320800f0f00c4001c00311000ad4542d003110800d560032803100c0340d05000c4181501300c4038240441c00d0354020842624003582e1040d0700300c00e0040000c09040c00700c0c000d600904291000c0c000c52080301d007100308002135258640e009401c11030039400910012107a24003002002006050b40f00c0014400c3c550191000d100e641040b0700c2e08422030360001c1e001250781203203802003522486c10f1f000415850207140800306400c01040c003d4001c60300d4a40c40000441c00c480c00d91a440c0d500641c00f40b0040041d818100008001ca40110f14141c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 764891951 1250 764890701 764890717
    0xc05330c0a0e04060305011805070603110d0506041409160b130e07140301060503010302090c03130210030e070f030605090d0203040302040216060903120510121103011b0201062405 79
    0x100100101210342e0f00c60390b00000040d03410030f009101b0b00388030ba011242a106614002c1c2c83e14058803201040c0140240110b14585402e100103914204221080e180203010107045641c0c4140c0b22002e40d88440449a00103004040c40005005908144a00820109800e601580c0c16200501040080124802521040f240410900342c1c003a03981c4402181c080101002d80703010302c4400310020454507809009107040c3d80c400d46482b94940c9070014401442c0c04100e0f00122004c1981c3c000c0c8006003440e2080c010506141d0402080f40720315a081d0f141004c2494010f00742464501c1010018400c1034015540c1200c0aa000b8001d128032000c0020b483e0310a60001134021350300015400000304d140780050701403942005082006002c2480d00400c0803551600030013089050001140d140016014400212803000a4803145174143e030765218890a19111401d902d5503840c268042a28200f02003895031981544c00080c0003801c00d800241d4014022026000c1c032070884007070010301600002160347ca0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 764893201 1250 764891951 764891957
    0x6020f030904110f130e0604090506132402090906010903030c030e0d060c030507021002040f05040513020d0f120314070804060f0c0302070201030b0f0a030b04030c05330c0a 76
    0x2c209044440c0c203e4400c092004000300b0001803200e991030f4004851a066504034200c100c0140c03079010800c0190f440c2c114001c0c0680c0c2200002c141404e001840c0e1002c60340c40355481c0c2c0026010584000507261002e88441c0500380c000a1101c0c46181500b245984a0424201400001e0450700c0042440c14011300c0101400658814414141e61300805040e007158407503800c0c030800c0f44e01c2c41d005014042c142da1010261181a07940d8440030014003d44040c0c91030201006245460f040c01c210190401911071a9910040c102d85405a12100712250b03005006051408000b4018940020000482402c3c1404c041c80d101c00802072401c0d0381041c0d40c00240130318040400b034540307082400041c4140d01c5030398030a42c688080e9000598058028041250003602d0030408206a002800340d0401585003950303020455400c1400010b98891519407c540280750103803230920140c0e111858080c00f0072000b01b0303e80482100b0302505c8103854850010b111070340e005820302c1c10000c500d10000d0044415500134 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 764894451 1250 764893201 764893211
    0x3180915150d151502010c080a02091c050606092d09030918062704060c090308030106030203193b060a1b110a110105040e0907080706020f030904 64
    0x35418424056030400306030340d00704201d0042da1a00c801a03a10341482080c4c420310009070040c1c822401842142403c00c0c864507004d0483da141d400c034100039841078409c036510a460005140703a510302035000d2843c45118900410035810f04800304918420020074004a29a00000380b401410300869444c0381c20909020050070350b00c400c03040c00e042d0f001c0c0e2006960441064480000310800003041c15000300c0050314443c0b0002c91201000b0008190944107850649090011600044503030340054030505052503c248029125598034a069000303074010400641c0103c00e0010010341901c14841c54401c0d00e00030000048409448000320030070f10454040d2201001645041e100001560807085480e1001d80b581403400d410500c009120b1203d010302140846086014514000d0540c842c14140e84e800a00c4001ca2654612526a0140e0001810401c09203c006151042813041c9802101041c029052903404c0c807d103203152001a030f02031021540443c0749003050610201c112035288009842c0420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 764895701 1250 764894451 764894479
    0x1c060e0d1808250b030a09060b0315010e0703140a15090204061d060904020a08160809060a0e011d01020a110c1305060f0d08070302250e06031e03180915 67
    0x3c0d10000ea5110008181c40001007005d6035a6607031268101034031030042000800b050009040e9030b103441810740507904e442140180098510301102c01ea100d806480c010464492100550010703107415210203008549807000c440c101450058260041d04226008508282ca040d000404544460003041c280d90b48200d084103843e02d8113811500300303c5001d071066582d0a80340c10700404030a02116080c882805004043ca0074621594070345c1e0045035140010b1000780c86102000000b00311100f0303580010343da078000300080352001003100c500e14590300000507160000c941020748401da064214208c0360300060400c1080d070f603c4014580d950060920006081e5561030003041c404040d14025950002030451500b08012005009043c481e1195090f90600c084580c0e0764000307442d83d4004007440030b0028105011805d0300c420b045501580090031030b140b0854800c055054032031080b020f10419000040c425841c12000210140d4080e410784646101d440d1641290000d44120070300c082c8540c49060002c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 764896951 1250 764895701 764895763
    0x1b08070c080412060605090114011206030b0601180e0f18010e1f020909040c03021201090308070e0f090f1621150e09071401080906061c060e0d1808 65
    0x15021b000040c0210409503100e0070500c007681e04c440c100e01d0000e141d40314048503a10b074901494046039403005030350356503032951001512900340130050b241a00d11001c100054400411480d41c0c000c0c8100e003951401c03414072080c0782c4410403102c05400b41903070608054603d030300c10018200c2c1004c1c40b100c5080b41250b203c102c41d070019204040b06c10b5030002e0084280000c0c02607007000801100e208aa0140404450005050070b0f00c44810014022920a10000c1c00340c44c016180c44120301c02c01052041030a400e040041e12000054032406100f152410822100320b1075086905022855820011010428219000c00b688035680a02e00800c0c0c0301c0c0c0e00f001119014001d240054040240070b03084520300404203070303521034592140c8034900401d1181d0181e42d50148904500800b048005404140d44000c00d020700301401d0501c6a2808007410700b01e80200b0641d01c07904003100b0003400a800140c181e208000c0039460002c2c2418461682c01000708202e41002400042e109034520258450404042180c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 764898201 1250 764896951 764896961
    0x201030f0e2d120a0f0c0f0b0417120405010e0f0307081e0703020312011202130e03040b1c0506090601020a12030f0e01140106050c0309091305011b08070c08041206 72
    0x1000003440798845842d190718000e40a8540d02107a545e80c8103042041100884448001c82d001420801c1c200303030b0003c040354010a04035801801150b0104110150a40e058640d81c4098400044940400103110400c5020300a07070910608a03001403040c40300d050103040d1644500c1400401c101e00c0001d40d00d042c80341d070a03031001298091012042d102c4500d0f05010b1346990001c207a07103840050020001c10100819600b00e014a40c002d081840765400342c0045000500c40e000d1900030038841403100003528494400100b001c01c206407130810500c40307070117510b50075114041c201512620681c4108081d5036800504100c02a030805000500f2a1510505030001e0009401340700f800f5090030400c800315241500302d40f042045c90010300e59640e980300c3c01120280a10b040c0007045400410848407203103085100f454205484401c5980421415520741d401c48010014052420a01c0c80ca050082c40e0800865030b8810030358100841224220b0f540c6541d135100c3c0e400f50301207228058a02c0700c1440b07156440313 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 764899451 1250 764898201 764898283
    0x1c1a0906040905061e010b040b04061b021003090b0a0b030d050310031b060816090b07020103230403171608070210050712110405060717160305070201030f0e 69
    0xd4620038200400e4070185481c4005c0e07107900080610000003140b401600440301290b0488a050341040c1c242401282c200c6a1046030740350310000550880d002d66146030041244041c9070314005001d20b0549040d4202c1040184442490f81c900000c00c0196240071500d102d0310346051401540c0c039034440011012021092f0009400b4086a01849903960203244203081503031160b0311444800d50315403050032442c0910030351b402c0c00502c58480400170b85030b2070f80203012014414100800c01c4c484084100c1e900c03002e220803400c107010303a03c0203200c14581c010090041000c1821003410983c9031035081c4002040d0440080302c2040310140000d00c4091007802034070082800d08509100328241148010403030204070382800c00c01031a090800d0500d030b602400311001c440000e00002e00b0704000e07440b9070500c040201c80240854000304501c4840188503140c0b0b03914a071013500c03441d45803c020b00005045604103600c25045c00d03e006840c0f554808002030101308034032802701c5194a1540c007010b52a8620488070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 764900701 1250 764899451 764899453
    0x717040605030601302f130806042d0b13020906030706201603050a120c0f170c0f071409010b0a1d151c1a0906040905 52
    0x10046a40d960010003035000e1402640c5030002070401540d2810841c6000305600c4003080d40c50741128420307105030030544502d443e6080c2d0003100b0600c1343d5110210a400180e441740031800151100c403200c103410b9070702e010300008002417440e0715142d60707000c0014800311014501c0001e2900c1c5644101d2180c451754204036403082080000d03060100060764090203241c0c0c120700c6282410001511800c0020700d0408403000c0341da50303089a040030801d1414109950450410f00c1c003441f009060040011001e08000354464030007040007603440d083c2070342000d021070340300c01c00c10a00800c40c0340410000c82c11601c1342e52b002903058001006c0580c1280740c034418882441d04030b00034200640034200700403810404071295940c50f100c40d071001c1d404015610300300340209000070360207110000c001071040d900c921003081c030040f5100b0720007101000039410a500e461195070b16580084c8100900503444500d8103060044041404030f2100312240641400040807214040c1614000048040c0c0c1d50390403410840e60014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 764901951 1250 764900701 764900707
    0x801050411131403010f1d010f0203130602160506040302030a080f010b0f09040b09010b0901031107020102210c150115030b1f0905060301090603200a060e1816020723060717 76
    0x114400c0c0d13180c47d02d031341040d025440c12035000301003c240d0086920840580402c411064266941c44000750451900101145803402d1640009001044414000c90207a0003c540f6180c00503001031004500070041200f114614004101c13100754401641d0082d101803050a84400903900820020401c082905070310079100000041c0503540782c2e00a001c40d5038280c0c0d00340403c0c004144060720341e03c070300e420090041e4080b4048185190810310300751036030702d101c1c08002d142642881113245000842003020441c548104010080141481d21000d030192460509104d80315100000840c590113203021a5010440782d80c0301c100d502d01c1520604041d14005080c1d0381c5075619410008010003890004454204210b2440684108800400029800d00422060760582084000c640e034590904051f40c1000b080380d007082044070100d180511511000d040c802c0354550440c0c0091074014181e001d6020342e014012004900c2c0751011480517104810b5511941d54035191812b0b11385165601ca01403030310341e404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 764903201 1250 764901951 764901971
    0x20730120e01020c060f0f04080a05030a0e01020f07230a0305010f1d06040206070618060903090902040305100903140307091d0622020c0d0801050411131403010f 71
    0x2500d160140d6085a81c52441103007110006a0b41d4441ca0f0f0b200c1980540203010381c0c001d0030010801411510302c3d58800c0c81c2000c0d13991400515045440314200d655400c042600e01141e5806652210029001d100401100302c0c03100361740b91150058090000c0b000340c190500201c0c240036002600c0240070203820318000f1544c900381320b802001b8004041051034240b403e8030048128050401c80400d0184000d00030355165036080040d2503004880c2240c4a94942032035081c05410401c446040e01c2c0035400101c3d0303002c92450000d120100b960040088184140014400300d50002030b10000c0807100c0400151101d01803c0a98484504a52201c0040000070411546503400002a03040729091600b54940030030900102d00c901c3c0d0b0407541180c000401d098004a0b460303140803a1104454025801890005650380140c246210801ca000c04a03001c600100b105083c18412951107041c5a005035042a07010101140342c00800c0c4034058880180070719403d0799135000c4d030051130040031000e400c101102d02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 764904451 1250 764903201 764903213
    0xf0b060f0d03110d020304260c09010b07170c0c04111e18030a12201902010e030105070c0201050c070f27110921060903120115020730 59
    0x400c050303c60310340910081090850300020688050301c810803100c48043e6610421a001e03032440202d0264684030b0941c40c000c2980740d9400e168040d1041c141c0e59550355001c1d0405200410b04841e056000f94030400c50f4240602001c150310308101802ca40104408014103000400c0b0700507040c003c00b040100c1e01e0039031801d0070300e40014650150039002d1004980c022134201510b80350701400140003598000740c0303a03900d1489240c124240c0c41d030303107050441c41c2829007075000d00c2d0000c10119918080410445c06055607000700f510058000d0840086c401440c014100030300c0c5569801000341804004a41e07011425020b2088c40c000c1c000da490f0f0b002009940f10032654240c1881c204200407201c640c5518030110403903010342060195080c840710314119041c1c0030b1141c080707240c02c0d402d42000101108580c95003005d100c028082c0040c14011a01c0e208a0700c80010310b081d042c4c0c4641c040819504104059540100d260b00c200e84210f02c085109401d2042c81c6c82c030b0b03540440031400600da003048600e010099 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 764905701 1250 764904451 764904467
    0x20c0a030b010b2a0106061d01050409020901120603060b04060504020c100c0c050a05070501080a051e06030106030f0c0e0112150b01050c010507110d02070506041a090a0e040b0f01030f0b060f0d03 86
    0x14141d59040704058820000c1030803180700da0b21043c0022b40400080c482052140c0041608071810b15100e00600d003480f2145044079483d4004942c03007070719403280300070300d180a000b41c902600c030880301141b409442c8020140d5642c010350300c80039081d84030900080414080c0c090b01c001960040140c130a251a9840c02c6038030b882c6a8055180414001c5001c242e040e8a98803540340309081c200c1188500d110002031215000c1d800a002d01d03070540d200c0c03102100048190408003540c600c41d440ca0303085142030088c0f00a00507016001b54a00c924400c503400003242c01c00500d80002c0030302200008801d00b1610040381c01d403068094044556080c07506004505070f100010214054818040d18008800c5440498854200c0e2068075400f81040c4030a021112014026101c2401300d800000d280a611201044120116a0084541050100400090120000d4603d51040220a00710169810340d540c011540342e502e00040d10820441000542d1a128081444030115000f4600b48964503a40b8009121135 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 764906951 1250 764905701 764905709
    0xd02060d020705070e09030313020a2607090b03100203130204090503180909070b1b0d09030c08212217011b09030f0c0f060906020c0a030b010b2a0106 66
    0x1105a040000300172550a03078140c0902d4103d0051480d42d00d440111401d4042180320903648142d100707400040c02010b5841200c454641021400d0290f40445007450500003554040442d080c10301c07103048075503036010070384400c40174610344010b840340c5410000e104102c40a0034000e4100b40f52070192002d004c000000390011074510740340c0001c0420258107012020505131110212035020364028480504010b0180150200c1c065800c51040500c40000d89402c40f1004544c0c041013034403005100340320f80840305030050002040108804c030303503507101080c0680c40400c0b440461032011504510350309500441c5c02111403200002e4910980311542055070043c68006a0320303561130040010090800451072a40303c03011178856005075490741c0c480c1042d15040c000e04070740024001501190b6550308205c040c1c090b101c150f0351100c10500b4448040c1c908107210540520828400d40200006042d000f04141990b4040c400a40c0714940c030820fa2940880e40c1103a06090b41c002c181100c90300005501c00e100329 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 764908201 1250 764906951 764906953
    0x20d06140a0b0a05060c0102070b0f0105010f0519050a0314010b1c060b0315010507061406010f17071206080a0807120c03020a11011b060516090609030f020d02060d020705 75
    0x68881001c1002180e44420070300d030300210183c004004614189001d06150180c1c0c500162412025070b840c055091412104020210b41060042c011960301c02ca0315518900b06003000c40c5050251300c020b0301164170310503101c81004000108289602d1080d040764200c2d1005040129217540c642e01503030a59040505405842480f09900c0e0040e0f440ca401118111102460032520b5500d4880c3c0000506061800d95414418100309610004540b8032400e41a100e0340d219a44d46800c113003000510100204c0f204c401009030001000b8550820595655008400381c1400b0028011000d140e0002d4440f42d071010186000303440b841010303c2070318401001080e2003040c1e03d044202c0b0f0b43c001070329590891400500140e101000a80008500f074429041c2e50704141840c001c000e000c468041c4154440c09000c540b02c58544060020f500280420800b04181d141481142035003420342c000c040f0358035844050240124000c0707070001d648071210040010f58001d03210356503801c5c40d0281c84d006548141c00403119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 764909451 1250 764908201 764908241
    0x5010b010e0618040203060607050d0804050115032001020106080f0604021003290f09070c030f1d060d02040b0f071e03090b090a0819110f010507150207020d06 70
    0x7992070b100d42241d03040d28100c81421031250900301844000e410051180350003090070010100030071010030004c011100a03030b80300c0c02140307824070384a425510000c803100e0031400601402d00010303034440c00c0b030400f0741e1146c13415071f03c2182031400403409001c03030380c1c486892030042070041d803241d2401107011449903000344d602c50000c401e003041c2102105c2920303c03a110340400201940400325100c0b414014400001091480b0704500d0400245200b00196680d07004180ca01e02c1040070035812180b1a0100840c5092066000b074921080391a09844441210310402c80000c03000541da00d07540c1510040c0841031541c0e611045202e440301b605501080c025140c41040140ca02100301c501c821120806515940b44500549454400b844641000780340c10362045000402103440c41041001c60314400d040344e040c0c00f0039000342c1000744034821040e0425004064205c0510000d9030880c0072520340c0383d40035403040120040c1d9840c0100a00400c8c800941c4081c0e04500042405050b0b00b0104445440d41002c100c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 764910701 1250 764909451 764909477
    0x40f0e0a170315191a03040b060a0b03010909051009030f020f0303220f020d081b011b08100305030d0c030501080303130b0910021903061505070f03050c030705010b01 73
    0x19980000c4403002c0c10301c00b0f58000c542050030194514511145050382280685465050285036040c860802460482000c8204424080320722002031f0440c2e0141c038031000250524050303c500d4401402130b00c2c00b0075100c180890800c07070200324020a401c0c40380e804001c0c1210501d8014244440307200c00c078005200f071440890381c4440100443e409107001e40011000c40745945554802c40b450703c0010b481038201d000c4803101503144c8042c01d140c0d440c40b55010a035114040b86a4840260708880740720400d82c0b40c1114034108204a00040c40080c4190034000c41b507031703a4941300c108030b00300640005240d07010100340c5501452082d04200c00b0304505480030710103030780c81c0c00d241c50303807404212058400d00690300d200001050000c04407903001664a400d48a41c14232214001c2c007640e000c0022180c0c9100854010340b407581c5c0c1440f540000d4902a0020103c081000030001c3c400e004266010b4203e40c003000030300e4200750088040750340c018900030a4948850780c034140307280206550b407091030100d0000f81601e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 764911951 1250 764910701 764910743
    0x4060f0809060115170a0b03011b05030a020d1e0e062203180906080f07050307060504150512040b06010f0e031e0f030c0709060506030c090906040f0e0a 67
    0x52050780c401d001407050b6840c00c05402914480070220006106901d440d07004d4420059807098442c540210001c640c1c0341490081c1403c50b1045219030252408841c028200d165000301103a40054081902684518070300c5104001090b0701d8411000e00b03100d02648015064543e000b030b40480000100352500c030780c0d6048904030451030b07844602060f41c9030300d1807000c0060302961003a1302c01f001115800f42110784a444075400c40301070344c010014a174002c0007100c450318000c011800240c403042e4040d040b07103840c1003c0940240a0f0b80542100f1184051790001118801e07001e0721001c0180b11110740250a150402032442401a103007280042c541c0154603403080e00038a000b000128010780188001e07102c00c40709120255160440e089680216000a45900300802c0503003d030081d000040c01c452480c005400045a4203644414003800052003000568094841641d050380006e9424005540d00c1c80005401400783d0160384416a00d0410281c0b00302c50001050103504c1d205405012009103131190f44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 764913201 1250 764911951 764911967
    0x30818060115050309010e010501140a0b0909161110020d0b0d12050a0905060a0201020307120606090308071506080d030c08040b0601111002040b0d2409021b0f0304060f 74
    0x207408921180841028850f00c281d000796446880c0400028002c035281c410300342540e4080e4403a50742c402c0d0510f003000c154907004c1d0581000340605010585800c007100c000c03500f0000d00422000419988000c080c3c14640119501c41180000300107650351030f601110040000e422112008801c546049504182d078104400c6001c50700f078001d05113042c00c243d55901160035500004843c000c0010f03d800000d0305864440160810600b0760b000561a40f9000200500010b03118000001450074000c04200d41500b206103c410b41780c020b41d0b01c0342e5a41c16400c0080741917000c500c1c0c02103030a00d05480050b03000000b041984950760613507001e00610154100c01c64801005035070150000d0f026501140480d0300511030000300416407000e03252480ca80301c80e64000c0360080d500c0440e0091b000900700741d001c0003603c1045460500202400201c1000b213590360382c40d440310b01600400990010300c40040c0c640b140e81e0a603012017182d04980804800c0c200444d00c94101c0d100349000300b83c100324480070f0351b8060728503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 764914451 1250 764913201 764913209
    0x40f0506070f1b0e0108061f0303080a090305091011011b0801090507110a06050106020c09040b071107050301020a090f21060f02280909020a0504050d02060904090308180601 76
    0x10320302d40280c060712421100300a07075901d8110303c0405140081c554081d507003864024590300001d0701d40c034030301041c00030921016082000b0151101000503c0025000041c19812540c418400201d0505903d41521503210f90308a41764000344511000141551000e9402d0014400758000d005a15207041e102d015500424180340c04140303100014020031540f43d0141d030344003d03186054181c808112041d03504060351410f0644d1140e8403003005101490f010401c0c1e41c0c8008080d20843c0c15860241c84080d029030001d4448020072100002c42c00a10004102d08400780c1030040c0215600c1c0c0c1010401b0700601641d126205035000c28007030020313500c1c0340055072160f0840795107a0042d2840c0d0541e60403004066802500e8200d41d030900c00c0109007210291900a0702400b010308082c074200100014110010700d601000010380101302031812160b00c0b07001c6c1c03411074506440305000e01e5098070000c0c005000d8800c42d40d4225282903056424035502c52031450140c1c2c02c0c4500c020151a164122686564007409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 764915701 1250 764914451 764914463
    0x10b09030d1b1103161d070215070c0204060e0106030212060a03110111030d150924050d0c082506050408030f07110a240302090f100c06020a05040f050607 68
    0x50b0012800d04440702c07025020060990703800c00c080d490541d407152820740100e61404500685c4441c200c02020f506500003100780010708105100003a00d4860003801001d40c402c000c1c0e00006c80085445503000440600304207154500c0540c0c45004c000c00940181e0480c0c416a0302800205e0300c80d082c03000c0c1c00c4080c1c90b000040c1244001c0c0c0180117603806c0c0c030fa00341100c80c07521040142d105062401c1c842d40b400009c80350700040c205468404440240d581c0d1045c04101641006030078000d1503c40300b126021a08103039074064a444803030820014044d00f541c000c1e08940190072030300f100a00994a010007a403048030741e1081d040e03110f80d42202c403800303103000303c1c44e09a000700a01c030039804d00c10014080c4240304031184c22100100c4004600d40c00020b602c120701d031007921880850b100340450b48405030b80d802840c0c00c50030002248009408090072501160040e0f00011765122024401c030b80c00303440590400010741d51103170b1240c00206603910a100d02003030078200d44804601d1345800d10480d1a441d400c40c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 764916951 1250 764915701 764915747
    0x101103040506031012150f0c0c0b06060d0207112809020d0b040c02010f06122d050304120b070f0e10051308010b090603030c07030605060f0405010b09030d 68
    0x6050201e190320250150144403ca000d0000310100c5c0c844444880920400d00d080a2002d490705030010b0b140c0500c0b80d00c1c0c0a9040244c0e0502d2681d02c0798070724000c9034000151081c1e07030300d801000c99107522030425200889800010701c0c00910003042c403100c5555100b80c44941d032034a0044c142410086480c1e20749082016400d40400881a07103801624004100b210002100703030745d0f07100003412110212407000250b511111501e8500520b0302c18540200407a1041c420004180e645282d2200310380e030241c03003100148a110b4001d010307056044188242e40901181d54031503c076500c1d0b20310100c007a9012a0152210b000190711030384518030611212400d51112034109019404214a03884949000e50070000700348040c03800604495208002003544000001c0c80180034000d01452030f000402c0c8034040e40c010003880d0024070001403a0000c41b0340000c0006010f132030b49400604c011110304011980241084000301d00d031003030383c0020080090106d08480300503060b01020746040d0041590001c96500103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 764918201 1250 764916951 764916959
    0xa050d0c02070f080f060610020c090a15030807110303090a060c02030f0d1106010504060819030e09072c030d0f05040803040801020910110619090f0b0610110304 71
    0x580220036011124010384030310984843c82c2900001040d80110195031189129030700490092000c00c1d0408002e8035801413200184101035513501400d4802800b880c0484005804101c1d154880100c204081d00308124a5640342048112900824000e451781415591006007900d0000210b40c2c5250300940300c10220741c50031800340c2e44070690300f0342070343c26005000032a0350b28002072182031911040c58441144106240f6021858050141c00a9018070300c0d080050000c02ea00017030b0190340c1050714984011506442c40c08640e1505502c05080e040310088091180701500a92412120500200c030343c055400825108191030f40d0f4001400d03003542110b503110703401c5841003062204003006030038034074030b4544d0303d08189155605c154003561460b58049002100307850502c1c02440031102502e0318031400c40d03944003010f07160a4060300071689094001d03a10351001030729070842003026810800242c52852641054000000b048030041d2017185240d5460b45002c1c001c4414803081040040114181820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 764919451 1250 764918201 764918227
    0x2031c0c020f03010f0c030e0c0f0a03060c02070807030f030f1704061109030717120307020705131d010c18080a1b030210020a03080f060d150f110c0c01050a05 70
    0x180090503405540300c065035964181705005107080014950780c00a0414121045503081002c40d40041c1d10405002c04840d250f42d50311203209096940013040062022103024060746404010752100300c040c00765640000602c0162510118694040d454410f12100340003403c407080c0e608034203000070300d849520114000c113070550b0040b8003a410f007001107803510070500d0004c0d150855941c01003003698610303160801070103000c1c0200350140d8601e128a90840c1000000691142d4240c00b80b85e01449000b10500b090100c6904062001d0340c410703c41143d81c7d100d451000b8043d282446c440c4c80814207503030070b5861664250824500b01e80c0600c0c041c140d545915503901d001200319500141c0c258824139008000340e5120400c0f040d86204d1340d001001a102149400780042c60000e04142c0d4240901007007051544170742c100d181c2c1d4160f028900f9840c007035500d04c0e20700042a80c0c0c118110564a003040c140b011084400046c6001f0940c901180c9407280b5440044909119030b90307418000610030302003200d00d008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 764920701 1250 764919451 764919469
    0x906060a0c020609060c010b030c010809060106030b0d020a14030f03090112050a111306171303050c1203070201020a1206030c0e10051c031205222103060302031c0c02 73
    0x40b004044501d0803131030500185403a045019800c1259568220191a0303190400500c44116000c1c00e00030450728003da0565102c0c0d105201d0181030545659038810943d40d900424a0b001d5401842200032070b031902e150004c0100c0d500d034507a00a10603045059811640001a542c160005075a445a07044040e0715247c06010080c040c2c0081d207031140080e03200e440c02c100141080300e0f40e00c40007514491038601c00030036441307500b511801c401800d141800308030000e006d00ca0342040d4060800307076580d40e200b12a051400200ca101c01030500e5003c400c0c80b00c0154190010600350180c1d07a24440d008084020034000c480e43c41c40010100c000e8030300708010100000306026030080c1044100706256a4410100e645021104500640c0308001c5081108154105076010b07003041c11074104101d14501500c00705401445071125002405ca142d404038200300058402c02811440b03445011040a0745030f001501034556070108034800c8c01000c01c64401c5159a0300541901003441da1003081c807411715001e0061b600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 764921951 1250 764920701 764920703
    0x3060c0f040510050a020714150705250815160f050c010509071a0304020342040501200a03090326040c050303071502090a1a12060906060a0c 62
    0x203000005003581d4403542c009003c03d10b900e4031940c52507050b000a0034888540c000900119602002001c40d4840401200c0f08001d001c0c01959a1075545c00d1951512100c5040003501c10a40195080d030315807541c04a40490300311380101c4074280e9486000480080c070860707900e00c1051030180e000101610583c00248400c0c003034249a45424011700106007900c80c02ca4403011290700c030b0a420041400340e50002298281e00c10134a9080d81403690000340c031003174000202070b80c0485c02c100c050b6011000403079030443c80c82444000310814481003c030402e135560031070b4280d07095482d05400b4080b070311303068001c62120600790751050300d03081840d801900140380c50b4005608010b940034480c200705c014180039036482c030007c0814014a15152900c2b081840030350b0022030207070b0024007820000584110340800c2300c028003000940c41c0c2c54020041251000741d0750110b540030b00a0589a90b0115802d00200302041c5ca2801071115580d800302031101c804403d50304250030420410415001c20301c64201a1011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 764923201 1250 764921951 764921977
    0x10f09031710150e0f01030605010e04051009091a06010f090b030714041410030e030a082d16030c0905090405210a0207080724120908030702010c090503060c 69
    0x390780b5410020751103d00d20340420b002c101c4155a0000900d00000b100110310303002d01e018007c0c40c1c10200002c051108804406015944807408940100a03004018000d000e40d04010050603140e4213203d0f51006990031001d40200f44840400c5540d442003030078001c00800d54030b40a6102d490012001c6090303200070110002c01c4150b82e010248540c00c0f50041004004003620170400c4a45002005000004001c804050502d44030326401884000302c00e48250080e1420907001036502c49182a2a001d120700b1615000b02c09100c2d0800c162841c1c0c40918000c1c00c244201c0200c01c195404240c04a07204450f240d40459845a01040180b40803800c090b406441401510b004141800c410303800007002501c228881a80880ca440c0003d904111103030040080c0b10003408214030f084004d000311100c8006200801c941040d1010903580206100d004038407005400b00195202c60804191641003601c4030780065080401a09063703210700c0b8034009881c801001380c10a503c440090280941c0500c24031403032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 764924451 1250 764923201 764923231
    0xe090a0b0a020f0703111014150103090209100f0902071e08090a0605041a0f1b160b030103020406060c051b040b120102070c0806040314030a090f05010e010f090317 72
    0x43d401021000e45103582c40303902d03601c20810450442c14280b0012800d104001440e21150721003072980b400c4a1034000c290550200070000300440101c0150900da003010b504500f4090520407003480004a2008461114503503002564480a032001648222030300540f07820190741e2801c104a004c0d0300e50150291082003a54900400d200110b464075200b94010002700340c01080030840124144030343e001000910001500c0c1c20f4407d0310490300750080b4044160b8100070350f000d642c00c2110401003042000d9004041c8103069036a0002c0d0141035100b404128040c0d41801e0f00003c4040c02140040c4060307910501070201060581d05589c9800b818015031a401070b2101c0c6c5007035081c0c0b9046a2055241d050000140c1d44034101d0501c80724207201c3d132b40b00f81c1c0d07564800300422010030ba02008101d004280a00c04558136103034102150f0117000307809009001184680800010020154482204103c1000091256409016800e8102e6480b588090081500502c100070b409040348206c03035214502c01c0d82408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 764925701 1250 764924451 764924467
    0x16060807210507020a1415010323030d050115030b0108190f060b0d140402150a0311030c0702090604020a051806071202060a06080a020d0b1003120c020a0e090a0b0a02 73
    0x402e640782a80c5a1000d80c00c90702c2003005201c4503040d0b80d485d82d01040028540078210100e0038284035414803014008a180480080741182da1070280c86210b903041c0100ca85590900403c88001c120078424210b00c03850b0580d040e00d040e400f030f0041c1000e02d07005031541299035440428850307000c120003c040b081c46a48131485c01a010303061041070701400c414100980c0b50b451a9110724200c401084244414079000700030000141d60b00030b050760443e221150400d80700da0705084d00394041c041d404803507001d0310300200030420f0704400030740038005550088428298031744034241488200e20404200e00001038041011160b4500382c400c0300495511b01a0541e8a40703039040d215a050103603103e0354140140c10041c03d02134400d0b542d0040308040c002c1d1034040d110304038680c0c2c00603126130705d001c4c0020b08040c0554009611402d0221000c4011900011070b0b0680c031030890001010100c82107030032407084000242c08680c64210004c541c0c41458120000c002041d8161916050000018000c2030300a03003c100c07902c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 764926951 1250 764925701 764925767
    0x1110a060f06060e0a0b0a110f010504080c011b1202130513050912040e06040f092109090501030c0b032a04090b010e030d0e03070b0f04060216060807 66
    0x4124600110400101c40341000f10040ca18054140c0c07040c4102010700e030a00105061a04507450b1541505000c110301034028202c90412011310300036511540b038041000b041c841c84900405510f20362400800100000e074a0050a42181300641000102ca0510140481d203244d0b004103040055981d17807c248076a00c00004168450078035082c2400750b250001d01101c00b1040200d1403c2c01c580401c0c0900309400e11001030002c100080c103061066494064401d2118201c2c4e204a801e160000b01c44c021144000104502c0302000308801d90014004400020715820b8511400741071383e62282c880c5800c203142040542142d0005440c691004c1c820061480e0a94902c1d0481094000c0c00b07140c89e80c5543c9013510103c221031442118505003e00044058140d91700130406c200041d40d03500385a00354145081c00303c3e10300802a004a05440400940009120180f20286c81200c009a007100c0703521030400d503041d12034045840b0780d402058401e404544c20601941d840401d194044800e0284241195006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 764928057 1106 764926951 764926961
    0x30e01091503090809091303020c12031902070f06180504050f0a0f060b0a080a0e160b030703020f16020f0a0f05041d061e090105041101110a06 63
    0x3c01000720303040564203c1d2101a0034004240b40501c050032014003103500941c05881125156807a51600f80100d02003c030101c00590b09012040d5002e120107400c1c03074641c03019401145408200112800070120061085548024440d43c01c0c4540e00030400080e080103000b1400c2904002000c182020a160006c0d90400009038084103591910024665a0002c0380000d5001030240801a4484000c0e400307010b03156800c100c1d0904001c400d81e61400d4140084640725400c0408101508010029650016840c10003501c6c140d5000700d0901039134801c040680c0d50105074140d0f0020b5003090f00c00d400d000c400a4a02c070300101e0408074034111050540c0310b824482c6854900c14a0304401c60498060003007802070403034400e13040c80101c0c00d01128003031199980c1e1814007000074060400c14001c3d18001ca030009560804036600c2001190480c40c0c0c8800e14000e8030480003400c001031341070312031 = true := by decide +kernel

theorem cover : BRFrame.Cov 764748201 764928057 := by
  have h0 := BRFrame.cov_init 764748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 764748201 ≤ n) (h2 : n < 764928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
