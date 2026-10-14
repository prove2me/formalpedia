-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1677
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:11:05.958256+00:00
-- url     : https://prove2.me/submissions/6b3154ed-00cf-464a-b6f5-9f83eecacaa0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 301438848 ≤ n < 301618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 301440098 1250 301438848 301438859
    0xa05010e06010909020d03030b060d0c050309101404081c02040e0601020d0503130227010b0c1b0a330e0103050c0306010c12091a0a110f06150f03120301 67
    0x28120180d1000394a9810880c130342c0013690752000112106941400c1c0040e218800f200805ca0030b024035500c132060300380790070030a0460680000c0218458100182510b40d00c00842c20b807103080307469040c980342c0343c09100000100001e4103400207100061840303481c00080d2030b800d86586c003640e11030380140316540d0141b401d1000ca540c0400841c030f04444a070910740d08528100d1804600080d0361580031340316444940340001c9042c01c1510000c0e1140b508902c070079103503858000d4101c2981c045501351802344a00312070364080009000039000880c100400303e4900528243c040340015490220024041d048007003400c40501200c200b1500313012968540801900c05207002408a4070002d2621042c1c280402c100041030303901440c0700144541c8003032003440000e40c2e9001258040c155030004141050031102c50020850703100044c0140007003035900c3c1004034600c11500c2e030311490110451000c0e80e0104002c20001c4041000c020200341010b4640e10141580b480000d1600c809189144448400080140306 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 301441348 1250 301440098 301440103
    0x12080714101b090e070c02221e0c0f050706020903011505040e07081c0c0b0103030924120209220204060207081f020306010507080304060b0a1703090f030a050a05010e 73
    0x844500c02e04001c40710b41d10b44440c000c40b02c400200101d00b04242e000c6e500c000c40d0f0342c00b5aa41c8508148510422100848081e03400040510441d0801103030140014003903000002e0040082c10031407a60750b0403210401e03400a0f03807283c00c0b142c02141c001341c081c070004205442c24818881080c600d0700e4220070192400050004070307201c1005450050f00a840305005c45900010000300300c1001c1d102400401e0304000c001c44190441150041a490a1030000001d02d030f0300140034029101c00f045000550340100804401c11900340005002040e051480234194220340d90160a504001030a079480f071840691008402c2e054200000c45503a6001c1402c0c03045030780c10000803000e021144001c0c03400000104250101504c40c0290381c040680000000e101640300344282c40744294003225542d16420035283c24005803800b20b803414000c070136080340084c00c00c4103441c000c5110492440510715201444044c0084004001e0300306805100340d140130070014034200410041715018400006001e0f508000321170 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 301442598 1250 301441348 301441391
    0x109020103110702010207050f0d0c0b0c070e01031104052805040c0f050306010308070606090c0507020906010311070605040807080c10060e0f160315060c1b1208071410 74
    0x40910083c0a0300300180d800141440c2640d10444107148410b01f0711f400035a5403030306504000c0c500d04400c440040d001d601500500b46003051102a00ca0b0540c840004e224102401d1201a0400c202039012003070702d04050740415040302c408808190305107140d5844c0300e60010104504a0722540d40c904020601501100c00c02c0039110341104603118900d8040000d40d03e54060001803d8040001100400c000c03240d4000d031b00510001005208054502d500a841c0b41c00110059018296803400a40c10750b201e44100d8040d90b083c2102c1c103040840e1904c0781001444003c0044485000400102c408244a08041e00098030400000d05c2d0790300907111140c0c10f65110b039100300b51110007101400505006103c61035070050801e09001c64881034603c0440192450007907283d129611100b01060b2640d00115000e1924011200c1c08451400c0311506d408441c403511549254032400f17013000000504c0e840c0108020b50056011071400504a2401400d00007050681c0000c5542e1b0b28031118403051100b0340c2d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 301443848 1250 301442598 301442621
    0xb0f1218161e050a170304030516090c0e010207090b01020c090f011503050c03070809240702070b0f040302040c050417010605010e0121110705030c060702120a170402040e0303090109020103 83
    0x401580d140c0400319501c1e613054041c0c0d000c081c50400a42c04248010400c0d0303402190481d044600c0c41c0264403100344902107501902d6040c7d4104000c141e11940507130011028035406070b00900da000d00e820801c5c0d000300280d028090450003440c01600680c2c1d41d43c8003075401025031000304c20b03055140c02021500880107190000900d0700785010800100d5070344064036800051414400f181d541d032401a2406c0440c02548034100000180680310003e40445003030307108901c50340071075548a0f02c5146d41074050080d00084004018108070910040c02c00f0380007418100c6041c00d1050825490744080041d09200a0b100746243e0f540c4d040c01c20030356034442c640c111144820f09041c502022800517440d4070320fa4000b128110951170314001c4202c0c05420044500c41a00030050303039215120a0001501c1c1c5100343e800c0310040c8684256505078a202030121111100c036a10741c0e0090b100c01c1007101048040007042aa409a40d0f04007030411040140000c611440c002400003415503814030000d0110344820b03a65 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 301445098 1250 301443848 301443899
    0x60b0415020f07030f06111204060c09082113060c05120f07020d030e040c02031b1507030b13090501050702011409030d02030a0906150f0b0f121816 65
    0x1040b090a008202d100c03d5a40003034a20208211a0900c407015182d89603652804440025002c00701c5041004004c0c0a07600c11721042c08020744440c422070301d0410390b000700d92041d0442141118100d803d84101020036803101395460420910748021041c0b290700c0c5d400382010401c0848414108001444a212a9100d9103d401d00302241002c6106c014015214028000d540105112042c036005040784804c500300104103016050b0701c0c00d0000d4072600000101c20240c543c0c0003408800100105804003c0507904c003184400790764010013100609841c8c00b030240c00001d0854074271800c0c04280038407036000303000b00c0000ca030a08050358004c0c21a0380c004249034003014a00180070f00800c01200f141d801807442c08002d6240d03215000300790020701904200030491403804000840200c1900e40700c0d000c0b20300340000700403082e585034100910344c4584039000c10101d004201301840d1505c0e031150b032504001000c41004041a200507101d140c0400c2c0c29040100702034911080100f0401c0f00b46510b0319254481d43c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 301446348 1250 301445098 301445113
    0x14010605030610110102130e0109020a0c031803050601060504060e04060b18041e06150206040206031b0909070e030f1c1b050d08010311040c0c030e01020a06060b041502 74
    0x4010410700000c2c201622458034001d140c1841c5203e185414015003010000315596009900c00390618a480c0c410390760107039104c0d000040c1100547c130a0303e480a00507102e0301c0041229543c11603981e0b03240b0b040080020b48152000c0b000c114104440b81c040c100984900d0703556070401502409941a00404612582c20070809021a42c000011b03a040360201203a011444985500010082c4c551501c00301031090f1400042c0a8481064120004075038280c141d000360820440d504903103c0d172080758081d410003030410100c1d0030500e80381c852036004000d00d2000ca081c0b1180f03000191001c003060300d80000280a000c205803c514061201d0200350018800030b0907003003850340c0b2480d61900c1c4451814140031503082e0b60034019a803203e030060440e900009640e8808045d040283c182002800305481c00040d680c10784441c0d042a110300c92015040d51a415421100350f40c08a5107580c0c1d541d07050341103008810782400000c07001e0140c20045e00480c210591540d0a0898140280c03200e200c480d0110741c0001c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 301447598 1250 301446348 301446359
    0x108010510020706051b030d091407031a070e0d0c03111801171609020c0106090b0f090726041a040804140f0607050a06060801020f04090e0f0609030a031401 69
    0x3d01d0100302c03035041c24403644a201003003840801075140e204030410380c040020009002181a44540103e45c450420895a0500021103680c0c45155000042c94280e090b043c400c480003102d04481da002c1d00d01c5c60102d40ca68244c0003c240d402d1761080e022030f0342d044e005030148100411030b50b0301c1108e204183d0f030190528024a400c0d400c03a140601c1000003001010804028200c0c003800401e103071240c5d01d41e04041443e520700c4c85c20300940c000f0102600c55440c0002c0805ca100b000d020702d90146000900810f000081d0400700300d0751010107800301003070200300010852000c0410140d0300d980104481c042101c0d103401e00b005d07100105152242c9814246d00c804120003c1c6e1001d09550a443c404002101c1c0c5824040c042000f24402244e100c1d40510041180c00801900041306003140e4807440041c4a0300e0780e0f40e55100e0a034010440b00414200e4248014080403c56600007048591820101e503140c400b400140c908001c2c05031900100f9400004107040065007502441014030b5000c507548416601d0079 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 301448848 1250 301447598 301447603
    0x90c010509030a060203130519030201050c0301140f0310053c13141f240603092108011d01080a08070206070c0602030a020c01030911280e06010801051002 68
    0xf000808050380032011a10780761005424500b40e903403140031541040b81c2c1141060584a4a820841c015800c2500103600c40d141ca00c2505e04079601c6607805120b00b10010304002d40c0340c080c0310105825200b1100d04009159140c0144c03800750f0481100c00d01c20042402020210502d1040b90301e80740042c142003898207003c2c103440154012021104010f110909240100c4070300e8200e4035090f92441044a0f03c05085060200b4104a5030600c60400404000f59126401441c884001c40c13090000c00302d0070020700e4000c0d0429003074207129484205654a00e520441c4402c51407080b104d00080d24003005107c03035122040d4a250341503100750f10300342640c546000707241d41c1c4404680040c489a40414103804640758102940c4d101548010b6402505440d40c0001f907880d00501143c40040c0704400350354400354001d1281d001e540b5000141004d00e458400c040c04142c0041c41300b05200380300e0100d485a00d00c500100c8810242c800031159190f00e00b0550001041c102c01a0030541c420000007910031000d5800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 301450098 1250 301448848 301448863
    0x30209010b1323040509060610120207020d0506010f0e010b0313030311030f071202120f0705070b0705070c091a010c1110090e0f010608011404060f0e090c01050903 72
    0x600c0741c0c1d0345255251640b00003014035400039a82c010300352400c1030304030100c440d0705851402c02d0342d082195a40e2200e206560b01d03030955486401207207040c0d00303814040c03040070781d045590712106c3e01500e040c0071540403a0a02c040c1000980b042d8000302c006021012031070341e030440200020713151386d441c65041c1100c11703201d0300c030141c2000c10016034012050200341c006d0700b119902800002d0115201d2400000a205d4a0801c0f917074800086d40c003040360000c0c1000b0b0f00c2a9000030040c010b0b403a14681d5011210f00d84030901a00e29000d0250a210120009000440703081c0b05001503039407a40c594515251448413075085400600d103d030b0810804140300c0031815a2026154801d1034125204c1c86076040c0400c00d14901008070b03030004a00f00a90030903075004021042150100716140300d80d03944592218100c0c0000b801a08001030005004025504034159900c1003003200801c006400e966840d91130000c42101d41c8010f281c600c108080150101c2c0602540004200078240300d40b07080c80d800c0002e61101d01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 301451348 1250 301450098 301450109
    0x7050a030b0a1701140105060f04091d070308040e0109201b0105090114150108010e1e0a1b030e1f1b03270b0a020711030109030e010e060403020901 65
    0xc0c0c60070044059511240340340000c103005500d40100e03c0c140c0b02418007828045100030f90405881e8000141801c00d007045407030300d60008500d035091a04001c2c0c828040c0c6418200b05900c1e260849042d00e4141c030900410005510a0748481d549516003a503507161021f059000c103144070b24180b40070481086904400e0080128107035160f581d00115000b0055400d00a44601c80c00e40c0703450100702035880705611800340300703000c480611101d070f0700d411f40c00015582c5040018000703030f001801004404d80c2030700210717040500c80c8911090000e08800014005d42c2c2102e50103100b6480c0e43c0a1800b460070b5494016542c01985014800300c0f96151859a44503120b44892401c0410030486502980c00c0e43d20801d8128100d20b034550044441c404000c0142c9030083d086030b6802c02d03000516502801e451902030a00340d001160300216580c642d006002500012425644101101c603610310668007031180c041800e11944a04604001d05800140150392883d13140c1c4c0200000c04c81800545d542580742070445d017 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 301452598 1250 301451348 301451351
    0x30a0503090f07060801210f0b0402060d02030a091a0727080f030a1e080408030406020d0e0a140c01050306100201020c120909131a100503070314010b0301020307050a03 74
    0x40315081c6003490500c091045a40901501d480860019407110b00c550488240310717605c480c00b1030746c2075400803100300150700182130001c519900030011708015400c0303500900040040b400c0c503d0220300700081c1c5c1d004a5516441540e921104002c00428a56841e036051911003000c00900d001c0402401100041144403028107505a055103045080184840600814400e940524038000d56031980c80d000003600101182440a9048448a40380111134619131a41e8416142c1d48031501d071408036910240c01603960035000c00c000018246c480c011181101d0444c80207003c03880c050704180105a01d041c0029209030004402e0411503030307014080e87d4001c141100c101241c01d610140c140d00a1141e440701c0349440c00b600301c1b03ea803820004005840703440d106231104411587c4001c54480180c0000c0c10003080180601d10502c69114520546940039110024003006a9150701c0001d01c0c10015910032181030300801c5c003581d600f040a02440c505450158000e41c110f060421014200340180b00d4640b0805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 301453848 1250 301452598 301452601
    0xe01050909060f03070801021305010e010503010b250f020f0301020c0d050904021e03070f1e050702040924060503070806040f060209150c060f190b01020c040507021518030a0503 78
    0x183d0302e454442841140090480744041d64550b02a800703500314a00d0b600c5079401d90a400030380355018100c641012030381651a90302d16801d103503500305250401003c4e122104041404003c000d941c0200030f0741202d0245d0514443c4000520412400c500803210b8070b802039005001080b0108030000704900f01c0030702410080c0c1c0324a0f104010a000780191950030208202d10303030403400d11b805651300860042d1003a40d101000d005100205940900b40d460514503600c00401010301d005201c0c902500000c0d01c0140003180d031403940d8940e0b1990021182d1599aa110040600c0c10790604d42e02c81c1c007008040c15005081c80515001c106501c0e9200100043e1031140c070071a80c0400c0000c0341d0304480703184a008001c4801d94510003220b500a420101e1488064880c04000c191404a441c2031a8030503090040c0d055041c2007060030000280c5903e20f40e5a043d445900880c010390303a07907406114842c249590040c844600a40103504150300003070010302e9816901100c813a000907011003103980184160030016a207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 301455098 1250 301453848 301453861
    0xc04090c0c050c0d08030c1809040321020c0c0105030402042009010908010e03030103080901091d070906030e100b030106030b1e0f0c0a0c0f0f0b0106021b0303070b0a0605130213060e01050909 84
    0x30b0400041c0c0c41c41d4041c003107270700304010150028201c800402403500c0d1183c21200d412700d40e034100d10544845207420b911031101b0100546c811760086a00a201400105000c030013003122441401c0d11042461003540702107144441c5590008040c00181100d90090103400e204094543d141c0c070044c000945203840024170860b299005080b01c20040294020a0315407910030041240490025100f210005154040008559229003c1c814100401a01803d032070090710011f0750007801d004040d66095500c81a0000104011900c9a0320421406500c46130080450392280380b41c0c2c000034200b034011410502400610030242c01502d5000c0c241d410085101d10090410480101c9511002010101041130f94010001030400b002e040302e0f01d54003224843c94103c503400c40c2d1b400075002155010342c4144142c60109183e040031a4001c0c40759480040c0054903140401c010b00d004009600805130009025090142c060800034010f0000d032400b0b00c0320ce0b00510001b049440350040c854400c0c000c500205c0c0c0e2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 301456348 1250 301455098 301455127
    0x30408090a08011e0e1b0307150305100501030219050c0a0f11040c0207061b060e0d020706020c060901080115031e09030e06091005030c04090c0c050c0d08030c 70
    0x48408001c181e00d00103690740b0010740c007a020440c996548803961818806409429001d0440030040e80b030050220780e10250760208a1440700c00c002581845114030000b0161070348401401030056075a00401c1901d4101c240e10341400c444c2d0320079810035204000da42c80c07501e20407210002104003031030141e036600880c084261408060380006402010990701c800c041100301c1e4a400b4007002c040e00c09001d81010844107a0b112002d501c00d20b40860041103840f542103014500c01014075101d90030016640090102582c07615a1424003680540c0c010103007400126010010821000821142c203860401071710002405000d044c42481025a005c0e00840320103400b036003000080e11b4a92901100201140640f10054074440d40190041303102103c50050340e00384207046400001014007042c001c8041181c08a566510003031000080841c10310000c01d00c14402e029400c0c20340c041e42e80d080ca03846d281d400c0a0341800c0d110604144500c5000d0060400a54200d080c0ca50000f40c60310003d407100e608050840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 301457598 1250 301456348 301456357
    0x61704050a150b09090c0f040213090e060709081b04020f0910120605011b030503043905060a02070302100c0219090e1515010507020d121103070f020402030408 70
    0x410240500c0c40320451001c01e0391260354506822258002c01d51a111607186d141d060b0094000d8000c010f4000721040d03030905400800104654070f1051440317a0381c59103030804440c00400301004a420490501ca10140e100390144007070103105d000342a410b0100d8a4000420440b46009405503401050f078052044041d01503a0b5104800b520b10310720f00d100c200004004001c82008199860314008020459501c2122000d0750f22181081084035070445803029103d40e00300820442d40412002c0050b0260750400706007000a40030122504100e4070700c04c0c04501c0c6107c958204600a030818041c09200a038001400c900303c2c0c0e0196651081d034840104101c83c4005103410281d0011580c4124503100546d01c1918000c440024000b040400b59217000030f81c84910002e50350784070f9120070300410000300c20b9110311a100c20701410001d00c0c04d50340d54040b440000b110001074800340203030381d80c010005400181e04850ba0a80202862800c14107503a0480344100c1201e02a0156501000040403c000d581c12074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 301458848 1250 301457598 301457603
    0x2032a150706020a031e1505120a0c03080720091f09090f0510140103120203040e07020102091807050d020906040803040f0f061b240e0c010810061704050a 68
    0x6542d0340124280240203840c1d641089401b410910341070b42c01380303a102d220b80401403c07a441d0700c0b11194680401c00011468220001c141d6000d000003800c0082c01c040701010003140b24508d51512801d142c1056001c0300c645500d0642040f541400441d22651015501d581c030910709225840310310000080c9200c454040c1e08204450b85c0741c180e9803024419a185c2c004e40482c85078040322b500515150350801524030540c200d482d00d14001c0e006000296080707a143c514030301c8510441c1d09007695905004c0c41088103642c07040250f540098151090705100e0503d12410560007849251400c002600401c18401d6400038900030740d0103d8802041d58589044070010000501100c0d2a9510380024900a502d680b04800310074143c1407000404d030740940c2c002c024a4422501206000e150f40d102c810020f2000c1070300b40790040400c000b4042400c001c2c031038443d02201200007001c0d140d43c040c0014090003005083d02e0100c001c00f140c01c00415600c00310065040580325480b82241d1a6498680e16124040000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 301460098 1250 301458848 301458851
    0x1d04030309060e03340305070f0816020f040e060a0209030a080712110c010f050a0e04050406050a0b0418170408011b0905100807230c0a02032a150706 66
    0x1050301c9500000003805170054110070080b80618000980c00303a100b40c00c090060240108400b07600403c1c000e4015040090141c1c46071880e4003600c0e6901072603030740860003c2c295000c0261100056050062510190074000d0f01e04000070401403609555458000f0722102829400007200da5040e00c0603c200d0603919484151992603038154a40081001f400110381400900d4111a0160f80c10300000e00b00c04680c03042e140d0034507806000c0402ca9090380580748410038400102c019000c10b8695124261013a0300400700016203003042100c001c282d84960388880d101c0d5082031028078801a42203080d0400b59441101c0d242e41d8019800031b00d205000d04d038000001365180860350000c01c0a115034144001c0740e0f9070380e58241c10340c5910404ca0342c201007441c1ca80c00240c803100080c0c3c40500407410181703c482d0302c0700d11022038980243c2c401d021341e003d0308014029400c503015030b0045080400490854042c2540c089980c0400185008410040000800c0c40f407100c441c2d540b52407564010403500303d04c0e0001c1c0e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 301461348 1250 301460098 301460111
    0x402030108060702060f0c0307050a090506191b0c0b03040606080a050601081504080a033303050d0804080d0209130609091205030c090f0406050405010f03060b0a1d0403030906 77
    0x211035152002180c643c0094041e4a00044c9191180010035204000e020782e601c0c00c644075032204032115017001c0300b650240600e010011030703181d4a81015140c44040b09050001c3c40c0c4140714000d1410b00100c00b0810342407000e841010028070203800354025540d1a9980702d881e581c650804a000e065582d10103843c50145205050601c040420310905980300070040f03403902c0044880542042c48200da02412081c030510180c4c80d0790f44203800507810b000051510311070001e00c00810603554107601c80300b910700c6103003c3c030204100b200503c80e8910074103a03402d1100907031802c2d07240c1e0081c078814404030000a0394002003000c1503a81d804003904510725005001c112084d260304403607009010350700d03040d540c0c050300d000d982004610800c101c0f0b11600b0035070315103428015a841482503143c40781d0145503000b40c5030100480c26860314400e0303030b0003044c200c2c00c100c400c14a1030505074101e0300800b0103640a40078811050016542c02d8062206000e000700c1001041d58a6040c110018441500000c00c414203092 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 301462598 1250 301461348 301461359
    0x1202071a040c0e090312061903020307060c0c090c0c080c07031502030f0f04020109061b020904050304150201061409130b0403030507110703050a020607051606230903070b0d060504020301 82
    0x1035100192030b80702410381d0300f649500306501d64034014204942079a41000c4005001c90600300d1801246400a82d1250001501da40c002414078190340c0003480041e01401000062103003017035805005020500d0204020300c4817400c01020321030600005003a51000184151240768104800d100031900301819080f69124103007440040c0d4001c0e60030070030040310070000c5030504411081003400303154140c481000544c5824410740b00c0700d003000007a0401c205900415805602c03040c01c401c0c0f080d8443c401461340d403400d004045000f10100150700c000c40e850800240108103072000c0c03170380600e2000c0340c1c560541d0baa00c02d0070001c040480c4000400c0d07008402c0901c03007055003541215000342c00d103807521841d1b4210032036aa81e4500061002410341d60007142042d02506101d00201a054000c006441d0001d8105038120803080f419030107600024904107043e4044005142051814000c01c0621840e001d24440007036942c0c40e0328007031800d46841c00262070300e40440c00c1d400304005100250095440b5130759034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 301463848 1250 301462598 301462613
    0x1031104081906060b2802010608030705061e01030b010308033606060f090c07031407030c15020a0f030f06090f050105120a030c060203071704080a11060105011202071a04 75
    0x1114224140100412202c581400f0f0310440100c903941e480d000c00c028000d1503611b9803041c240300c065560b10710021501810a000a024441c096001840c50f130400381c2000c1c03001c0c103040018105500710040140000340804039580c0c1100d402c0200d4507241d031590010000325013241c0d01c00d602410807000b0030110580c007200d41c5288200c040300c1500d505aa07640c09100c2c0020b489114194082550340019001c0349266001e88111402481e0000448408006c0c0f10340652001506801141400e0340c11020080f240045001e40031354450150b06000c083d42d00a440d01c081d44003a842416112581088051001e910800c01441005024000f1f1000711042000400e028001d490150b25960351114040c0c600158100000340e0558540000414689840c4001c0d0009440c4d001046640310101096560607851680503034000c1b40c015503281c100c0d001c06000704450000804140e004100104510303a0000d07a88041c40e951454090781c3e03a4454603042c075003074916200404913181110240070038007000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 301465098 1250 301463848 301463893
    0x2070501110304150609020a02070308030a02120c0c0d030207030504140d050321150607080d0f050f0106020f060402010816020708010203010f15030605060912013c0504020303090103110408 83
    0x1a1000304071040c6c40e61007250591003442070030340150784003200420015650200840d802030b06040010306029280d07010307030495031301502c110203d0300e80809c80c040800403c3c0700c168030701003060900714603000d905c1d076012348075000d01c0c131541d545280c60010034a00c54441d404070607100c3d64000c007500c1e95081c19018009245512420301202070030080b00064040940c1128400c00b910f0080c00c1c1d40c10301c0601e0352490300c0356011101c108002500c41b40c1d10b191089490051030301807100702c01d0b080c03550342c10401c00900e0000e1500c4560b00315170285080c080580d03001079035690004000c070440d15440701600b41c2a49424030f40d900002181d840040001010402d0005480607114000502e000113403d04d00102c058a0003409429801030080081b1000341c54403100190503002d080b00042111600e032071107000752000c0d28039810700f2110715502007001074103116810071200303c00f22000c014a05064000c00c4d0390740a60f682060601d507640c046141003900c220250b034010706004044400300e103180102c5213800d542 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 301466348 1250 301465098 301465133
    0x20d090308090c01090315020a1202040e01181802010e040222060809122b1401060e12030f07080415020c03072102210d0c0b010801050906040602070501110304 70
    0x5195070820f81c56118648000c01c40f80c0014100c42900110400d140095200d20402024880c160500700041d02e03180c0081c1c001402c00550280aa42c5002042c4041052a0310000b444502d050760401d010b4440c3d4414035880e64081c60301d10703000c1800b980410024890026840070f00004a5249180a0028866442628001d44c0d0340d1036961607001059507205d040c00c05000340b0740d034240401740c5507491480c0c82d000d0350010308186110f003102c041040c0c812545002c4100c980c0240ca071005006061b00300d00c01c0c030500d01d019642d440c80a200b09194644900520400ca40343c8000010751405100d0b0030300a8178042c202c41c030160107402e01401800b81d518030195400e103000340240b030000540444072010701c00881c880c0380060111480280d0030004100403000d01b0b049400c80e100c00d25041000104000c5440003401d4a9070703403180000d800c00f030020110580c400f45540e0b042030104528410081031942e001603108c0c01c007517100d404030300c3d09601401d000014484400804020032040c070622558142c803002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 301467598 1250 301466348 301466353
    0x806060406060206060d0f03050403020402030106051b0d0504030615030501050702030304050610030f0305090310020a0e03011a0114030c04030819080a0c230c0604240204050a150201020d09030809 86
    0x150703a12400d0380c4445017180c3c05980800612102408204015942daa0302072180ca00a8034081d126030014040b07800a070031120000718049404005001000741440b51020298010650001414001080d43c4914000102010380b41c282e20310303240c201041c802024550100003030000c0e28102000035620340040300d080d200d501c81e00e000f289283c0114018402940e400160707007585200b4585080d59a0b9100c082c080741c162103205010340e0317030002c03034800307001c054926554503142e10f074041003018252124910161620010f01c04e2060417680c110748038081c0010380c02c01c0c981d1684d86a091242003406641c1c0081c0c0045000101d040410707849800b100440c64403a2034840003501c4203944a421628113180d00d40c00300300101d07601a40d200351140940b54507040e66001d07502e4001c0460366182444003d840c1202c1c220a121003040030300c0e001001140c480d8400f0311003181080d107040001030031040c6501c01d03080d113281040700003032186100307404842d1003d0801005010080c0d651030b0081c40100120740102d03150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 301468848 1250 301467598 301467611
    0x2407050f07061a03100e030a0e030c1003320f0618040309090501082109030f1506100215010302040b010e04180c0b090102030d0f0921030605040b0127090608060604 72
    0x604940c4680c03211084010300a6040ca0308d500e500351007024103e050950715104030105280c4591700c401c40428411041e5401103540c10701c2c1e514103842516032f04d8002c045010103030115020801c0316000154824038400c440b04d101d494242c0030032800740201802100c2c0c0709102080005140c2c101c2d5000b002c50f13040302410040d90380d1b16880c0a80b665074000f00300d005c120740c0481d08c040801111001d450400d2009040d202000795000c420341c0307003842e404652801e41d00c05030104030041c50305001c00040311103c1e0002c4e051440366a004071152040c1400000c0c400d5a0b40c0d001210140d104907100c40821102030001c1140f5510030303107501000c000d044e0040f280c82651003004201340c0c5004084d82c641c0c030f1060300110704142d49408488061b2460f03840400c00070b5611800c01c00400d94006100d000381d03002152001d00b84c0070001000f000c1c0c0d103070ae400150180f030038600312289603680180781d04521204407038182c0c40d500d410828540d2103080c5030320400040781480008a281c940200d0982c0c0541d400b00c2c1c041248 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 301470098 1250 301468848 301468873
    0xd021f0903090e0c041a0a0e2202070507080c0604030b01360504060f0b01090b0c0a080712080127020a090f0b091201050f040b1005090f0103052407050f07061a03 71
    0x6d5104008483e00000e101c1c03910a462802c10100542d109150000134114601505003103908981182d01c003035a4a45c0002ca0402c0324050611441c45c117008292076661a003410754864807e1610107210301818aa01c822407040c6107403d0350203020141e4440c02d80b0365883c0d8a501c0400300a01029036040e2040b6142c41019504400c880c0f003036020480303061311021160303450b0860840050300149640c15041c0113080000c0c0004949000500036144201003d4003c19200b038002001e004050f009401c101d14149804041c07101d40c0782082d03000c081010405651100d801c0c0046401c100d0640c8154030300e480140e800300f07000c00c035031014000242007a6045150001040541820381780d06a5202c03102840c1540820081060aa00c150b80868420002100c5940d90008100c01c05003c84d02ea0202485910061040003014001c081c51101a040314201c0314100143d148107074900545180706001c0009503404071603806d101515040c5401210400801c1c024920300f401661070181500d110f401340011a101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 301471348 1250 301470098 301470149
    0x100504031b02011b0c0f0b0304020906040209060c0d122003071407120302090909030705120d0e03040305030d0507210527010b030d021f0903090e0c04 66
    0x10860301603071a0344204840d00740510118910340000d90400c038004a250380c0484006194221440c4102e07001080107180c121042007603041c1d60000044c1c3c070010024000943c0d5010329158001c0c104032001a91060b050002407541d01c0343c06562890fa01900030070400045d003114540d8038081e078400080c80078420844910451408003c451040c0000070f20128400301d200394543c055241580e00040e140c59013544a03000301140c0c40b941f150010f41c0018401503141426240250003041c81001141480c4075540c5a54441900454450041001056151010340640c00c100110352015091301c0da038035200c1c10115140e90051030080042030601001c5112503204e07049a001009614121610f07031201580b42d10b000d8000a05003c2c00c2c1c4244006043c0702c01e00c0001d10540c40c106060002880100782c0051500304501585400d040d90017000c8806c24091a10082c0c0c80c01c0d9500480001d0020310034a010340f03108075140c000070035000c0358404000680511034020300944280e8202407248001e03480c0c4502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 301472598 1250 301471348 301471351
    0x80406050a0b0901031101030e03032e0605071416030b0405010b01080c030109050a0b0618011202310b0a0513140a090216080a030606030f0b03072105030406111005 72
    0xc2e0403d840900402c082101c10598480b0700c1814034010442e4400a1031291940d0010f49030824200b05d59003501d0f044080411117103071803480480d0072100b11480c1000c00b50503400b40042c05401c000300b00d01080078140d803d00201401c0d09061603a0a40d00392070381400e000d0b0b500103d601725002d41c60301c0701d0205158050140e45101c2c4104000390752543c4c1c01d100ca44400303044042c15212086488821040540d0384e00e001908841281d010501401d20002000600241070215a030076858410801c00d80d030368070fa04181a81c980302040b04140d14a00003e000903c0141640c405032003d5408580b810302030b94400c0c014503800c0421010701c60041e40362200386036042c204059081d4402c580010070040c2d901c07503070080c20344000000300c1100084038988407600994800c902200000e5a603030400c1c44002e406110b8203803180c90321a01003051a04420100b5500d000d240641254503080303031100e03c02c01ca0218185014150701c4030030780c0e86661740c850000e000c00c15070700c21120b198042e14000140340035080c07295a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 301473848 1250 301472598 301472621
    0x402060912030d05070507031206080c04020c120f1905092b050d05220b07020d08070c03080304060605060c0c09090304030b040c1a0c0a110a1203080406050a 69
    0x1034505410402048502249841190780c1c41c08203003d80c0d61011042d02c1070610640f95a00e51759a40d21081c80d00030103814081d29205080b81c50054240603180c80001c58192820b810b4400503610008180428030f0030b40e80d116426401000010203036117955000000e01000c0e603e203d500f02448050480a6506004d440c160316009104001403002c90b841c882c100700c02c4010038401a64580b0a030f51100c90800f1180322555021070b0000845454000b407a00c072000500c03020389120b038240350500745448454810480040c5c450440d0707200d90400e2141d01c1040f126803946c000d088103006079491819021a0304120340503901c25281a4000609040003000c8450700c80495000d0403450700f89008000407440040c10310001803000388400f1000401c2811150f004901031075484010600c0d0040e0780100d0070100402000403103051050007540d0360002207407101c440c1d1046943e540000090086000d0780c9075540720030251804070f04208140742c5c0240156001d203002d003805100c01d540300707a080002d0b140d007038054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 301475098 1250 301473848 301473859
    0x170405150703021911031e1011030f15221401031509032001090c0503070b18040b150a120204050604030b0402040e0f160603050f01060e0301090206130501090b030402 73
    0x5000e04082c41000300704c21a03101c0d0540100c1002c2032030101c0d240c20141f01011109070441c100000b40044200300842d80c117084040103200c14120450485000c0c000070700785072203070f04000000c103c440c0c0c0700e40041601101f01500c1e139103510810441d2610401e09204503003240c1d0b49020140b00d0880d2121540d641640d400c01140409041b440241200901c1108003e0741007013680744007042104010200d20382c40704029000410300000c070342001140041c556000e24440c1d8405007080000b40d40c0c10b0140c43e82d0b0f460b00802e80302d5180c00280803801800c000202d00307500c10030100b00e070440c1c465198050302c0d10354401c0d0342c0d0700080040d4141040c100d20030b5010f62a40080c081c8020000500d0346c07407900740d03c5440030740003144032600d099205180403004000c3c0240340d00700c010002009000212020000c03c4507207002d00c51410702e222074070280c04041c0a89820400c003591002510345003504103114803035024202e69510b03c3c002c1c4482400010034060380e40020f0b901407000440300c41d00e005503809590000c11 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 301476348 1250 301475098 301475113
    0xc022a0a060c050c0406090e1006120b10080303181b0109090c02100e0312130b0f06011b062702030d0507020a090507080415090b0f1317040515070302 66
    0x3402d80e080e4440e154200c460388110a02d0703540f1502c0701c5c05840000d001c0355030042114440742e5091828640d0103883c1c030404074500700c81044052520420324220b580c00c24084060341c0c07540455515409102c1d040003042c5c0c44000180f147c4028104011080402200d0039158a00c0744442da02d403010009107003140c006008058203110290060b400000340c4c0180d40100c1301105d03180f86061068a200c59040c18a43d040441c032141c031100d80380340c0300b58008440d0034900c0c40c0f50140d80d20819024009482c41d070321201030b50002a0264000c00328031400c00c40c400e069102c50501c61a01c200600102070000107501c0c06280c07000c0c00d0f034900c014000103480d401005880d07220045001103449410881050340e01014a400000d071a04652054900800559403007418614003401d0001c1d001c170103802c400d103c891915051a000c900200a410303000030140810303400544801280c90510a0700304c3c00030b8043c1075940724010000b14010300902c215802a0741d840c1214240d1450110507028000340507003d80c100e541e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 301477598 1250 301476348 301476359
    0x218090a0b0a062f07030302010507020303131226070e0f060d0b011803050f1e0c1509040212060a0b030106140901020307150c080603010507050702010c02030309040c022a0a 76
    0x134488403411464034101e80c4454180700681445290801c21051150401001402415428081d0541c00003039800298594102040f80420750320074540c000d0801c00c5003026458415108004194160026000602000b0140040c80d070b148142540c1d54404244058a02402400d10701c40303808a01500900150600d0401e03020100640a4461480e040006a4410a00c0d2102d11020b000207140654000d0808030302401c01c035454211481c218607001d8020113114240040001611200034009840c01e110340c1a6950305202d0a01504103040c0d4421300100740362080e419091089803241808a8280f0039103a40d43c2d1030004207100a005080014600340300c44c1c03041c844080018084040103104680c81d000701602c8100402d440100d0400c690350719a5482c1300025481044507030007c07400ca000700820300740b140002c0c10510404074004d0501080c29104020b40d07a0500940d8803290b8050000e01c40b110241000070b4903001e1000382d902800210704121b04c800241c00b5240000c0d40c401500407144c2c00e0805 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 301478848 1250 301477598 301477607
    0xa060515070f0c0803040f06020d031104090f090b01080a030e0d030e0108191406100905010815060408030c03041503020309061b071403090a27050405100218090a0b0a06 74
    0x18074251094043d06400042c400303401c0005200908200400c195040e0910000a007442950500f03a0109800c00501a500ca0601c400729801c550815000150341d910f89410000901028000503048213405c1e8000120144003003490714640b4480e07645d00e041c000b07020003001074881020401800084281101c00d1040d40a0214290060049020032000e00c0101ca04001940c985c40340340340985c4600350901c111400e00401258201406045c050900f42c140030000f007000030b00400c1c01d05044c00a03031034241c0b0b5486410403140504452020f80b9a0b929142000d940d6076445171042201143d46000546841440ba00c02d80e03008526940281909480d01424411404c10440d1011030460040060900050749000800c107884e036040c01454840c00ca00003040359082c0603600580d1403600c038125102c400b080019940d40303423030b210b9400000d06840d81e0030202d01c2c0c03c02c05103807041c00520004550a40c600f00204081c0102c50403214015031f40c3d220040242aa5182c003a03042d04548540400e00866004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 301480098 1250 301478848 301478873
    0x90e0a05190f092114090604091505010801060908120307031107060c08010807030302060a02030406060b070b060a09020c03030708072709050907060507240c080a06051507 75
    0xa0307030440480c0d0640440c122012480b0b60541c07140d442c80041e08000070001aa0b44429041c4404210b0410104020700b1329940d010003841050000516041c031070741c4070b10030395001d402c0c002d0301080b13800b000c0d1890b4440300d00c440c01014003140c0035034000107240d88502000800e45400340c016011103981844502c6d40c540000d8116030130f01d525250007100358290000900038143c0100f00100340d60300b03c1000501204010780000030150050801480400d4001814030341010644000596942d640c1c2490001426181c210714003110740000c40303c2c14800e5000925010f03850886928850b10b40d03031490001203106030030030310100740c00c1440050500d074020100303507600c18203600300a0010400d40c0c0003001c2c10a492184850004850541407002291a10503240d0100088009240c0b203070501c00040e200d80103012005000d4544400740a501500e503e42000070030000103400e1050100030240541060306c1181d10310310561030316000254515150000f030004507064441b2916106c00e41d120501c80504 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 301481348 1250 301480098 301480111
    0x30f0309060203130b010509090a0308040812090d2c0f0103060801050703020d0b0a03030c08030c120112140c100c020d0b0405060f0f040b07200d050901030606090e0a05 74
    0x25690002030100c1c0d00c6000551150710300c40d9902c0002c0310035140130329120300107800141c020340703802302000038001002844140c1e098143c20500040e13540c43c507208201d48503c0340700210209001c2e044c4010b4100004502100c1b108686411070072101c25404103056001c0d9000a00c038003104102140c41c0b50030951000c02d080c00d4180740100d62140c4900341a42518016126500041d50006000d900b400e094451290074000031541e40e00c0892071620000c00c1031a1944025100c84000800700740a080c001084070746240350148007000c03030340c0d4580b0420348071240302c60296131414030402141502c10020504280c0c0f448000e0240601461882d001c656030b411201c01260080d8038602c181d00483c0b039480000d4440c9125000900c10f03860001078007206040c001d08950040c0f6800300500000400c0c1d015410384c00030301403408510440751690500c20800b20400c07101028010b41044810f00340e8050018000340301c00780c80c140b001c2556140203c900303035142c2c41000450217817000440d043c80c0301c64000303d40144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 301482598 1250 301481348 301481351
    0x8070b06010c0f0b10090911040513050a050a0215070b010b0309030c0303011415071505060d1e0620030a0902030a0213020711120d030903030e030c031206090103050a030f03 76
    0x46043d076850808a0403584265444400700c2c04003c2c0a5a20301184409001550f40030300010300f6a5495111000c0f240000601c59034030b43c0e000070000c81c110485420640d402c4411181c8106690815946840300b601c0c0c1a07005040c1da590031804d40070340c207045500c026802840920503a1070680d207070b0919000540042c005010401c4005c0b91500704001940c0646001e99403490880001c2e401c000c80038180001c1340707590300c50034420b0b180410303481550900e1204107184040344a40e00c4c100060000002d0083c0102a100300600d2241001c1101d03600b00800b610546003045804c120b00b464405031183d619601c4c03a14101000006c1411201d600036843c2c02d440607088030401c440341d03800907129108419451080a9000c20004244000c90b8106d80101d14140d8a8104103580700301225280c1f42058060401c1c19120040f03001054400e5100140220154059075110b4004840b420303160b034402014103000208070400300c0c00038035182d601141280d44c0040103080200d180e41e001c2d907503001c40824400a05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 301483848 1250 301482598 301482617
    0x5040801090c05100f020a06111c1409160b0906040902040b0a0306060903081206030a0506071d030712021011030a030609050a05061c02061b0c0102061308070b0601 72
    0x48100340120158244035202c419440360a01c4140304a14002070b03024001c01002c000c04035006038000c01c1c808400c60b0002004181c80240a039010081d2044655101034042401c0c0800c0180b00c09a000500080c0b0000394032845850700072209560b04445184040703101110b41c0304200c0d03240000000d20600ba006000f890406da03036400c1010482e04240d024500310000041c01c103a1150389841400050035441c100159810304545034070343c007401583c0030324407802ea00a0100e420351354208103100c0b9a81e8840100c800b245071428006010094401074141310007054441030348149000f040643c140c070340c00614608540d146400b0407514141c0d0581c00c506000950700d440508aa0070300041c8549615520045015031405c801a001c6400042c5040b104916083c14080c40b03a0742d95618502c0d0915409119503014880c0c00003450a1249a03880039000d0345480425107003420228200400b20000d80a4403c030740e1700c25482d400c0f60704810350010100c803010085080081c41c101c030300d05d81100b41071511a698 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 301485098 1250 301483848 301483859
    0x1501031109160318150b130203010e0606030603010905010905030d0b0609150a05220509070203130302010f0203090d06061d09030d0c140703080117190206031b130602100b010e0904030504 82
    0x309a02c044450300c41130b26146007402d6807c0a1802140d44103040c1000c600c0c40d0b00d0006c080c92840c00180660344200c00010104d1072680c1d00350404641a90840000c2140740326034580903a884c0e000318440e01080742044203075101454000207942411b034000c0d0401c100c24400106140b62580420200300074008207200c000000e8103252100701d0348681d15030040540608100405c905010020603a00c1103610803c201010b01c603d500101044aa080c2800018a030b0004002c0c3c0c154043c242d2000e801c0038000319480188000c54012104481d10320001e01186829a4030140d445001100c0c80b00d183d620410800c1d4920384198008510540b80340f03031040e1007405240c0441d84580c050002a00064200e01c010712003031060080040445c14142c0041441314480e44441407407034540680644600008030001d28901c41c041003070400c101c0080d180e107546240402d88a050b135071031402000014410a1610a2808003a04c1141e9034584141c5813001c0c2c00845008000c80030400400480030032000307210000d21f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 301486348 1250 301485098 301485113
    0x6060d080c0616181212200a11040e0703110402040e09030a0905031b0409050c090c0d0b010201090f0f05150a0903180e070f050405031501031109160318 67
    0x41d075194586060740750710700400103140c022490013412400444150401c24a0301d002900e12000c0d0f07000400301d0ba003d00b4000c0c250340e800c0114210b01019018109800201e0328082003a2820030711521204c01380d21019401d00049447d1013900341007640c405103052010035140c1c40382003080800208054074264440c002520007078010390340f60150364008100e091400c4c0d00090401c001c1e05040d00100380101210030100d111001540c1301c2400799540d070070800c06116040c842c0c90180c0ba0050030200131820a03211010142e4032441800720b0080c40c00b0000d8482c1c1d0f2060040785007541d00f240c03909100c279100362036000104c19110401c8410b4402d486c201c1590140280d0040c4c4280d01035200010b880040341009000c9480c498002452410902c4042c0040d080d60071585400441918244e04820030f0280151034a20540c0c2120354541701d82d501c0a24000c615100c81030580344100c0c01205041044414802150341c141d0b810007a03407070303070034504e1981e5846580808072500000e140742d03445945540700c101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 301487598 1250 301486348 301486351
    0x9150c0d09020a2c1b0702010e1005070308160203250b072006220203162301030213060e060f03040507030203070e0907031205040b0c060901060609060206060d080c06 73
    0x541400a2284001e44002e004002c00c0d41c884882c0c000304600c0c035090410a0700748003c05e96006000c280070070840c0c291b911800d04034a80a0010b0140f220300400620040c00a810121080300040d00e040b00003400300503001440e041038034143d00294140138030520f41c40204010358000340d4080c1c01c0031410f01e001c20109000d45000e00034540700c00205460310308944021204d0030038440c3c0942c0c41a02400906d20701003110350319503120401d0400c0d4a502c070f0300c000380c10702184104910020007a440003180c400c215418800000401c001640b06014081c0015000da01950321240e404610003002000030394081c6501d1700d08640c009004a1402d1009000c030340f1250130985081c0c600c1e5201400910450804100c0311000e401034101214040c5440103e241d601c90040c0001400740620311100d503201e41c040c00c1690301428011014076151004411140c0c2e030742c6800c031500c0c01190300300100000c5460042240100b594a540d000d088103a450000b1b1020049101e0f50403100750740708004408032170100340441b5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 301488848 1250 301487598 301487609
    0xa0507060f1b02030702030703061505060304031706011704030f0201022a010c021203010b1810230913021b010207030801030c1e0e090f01050106110609150c0d09020a 73
    0x2690280540075401401d6074030050b18259403041001c0c1016030382c0000c028003129802003022a2000c4503d500240b9201158001c6801c04008000d200816403c0700304041d0246040690700340a0b0342c0c0300c00440303d88662850320702d5100b60400200300868480c0302904c0c540045070001604e03040f850031800f642054507050800c0440340130110f0740307a4020300b8000c180360886148020207074000c0c1e10900c681d2622040c840c1c01000c0038005204000043c1d03c0e04015080100188403200500c0c90890207008028404041901c5800e5204052814040e06064403030080016100c1d5402c1400702d00c104c1c009522881d01c00b00812020800588260320900050049a01c00c0d43d0301010b95145151440020141d90070480e8504030708910f802c1e5089440852000b01c480008040c0400d4480a2106082c8086003984044950a100020401e80c0c0c004000c1425029181c003200c09540e18080f00f00c0c1c0310b01c2100d450003e003020764404a18034071186400340008600700301d0001114402a4009000e000d1281d109 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 301490098 1250 301488848 301488851
    0x15030504050a051633052101090e0f060c090f01020109050a050d0f0503011802030a2901020709021201090c02030c010e072606060103020a0306171c230a0507060f 71
    0x140590b194000700500d5603440220b06441175024034042c1000c9803903000030001040030104584410040302c01c00500100070340c04008125584409898000d07200075488041d90b0700c50418030010050780000c10a00c107015245d959030400300001c0810a01514035150f1134110740d283e6604201055051105008080c8075000501d02406403102c06030140c2014040c081c14440140010000a51020341503081c0c07260305c16005a40380e4990703d078400140031052403d130f010809600442030842c002d00000318404002d030200c1d03540c16550490300c400d81c40380c941c411010703d1400004209004003074015141d003c040d401907904242d9110586421566051070400040e4000c100c1001a4401016044891024021810551100d00700c10755940c10303024088a040540c00500c1b5003c1500c2035003c00083c0c484030300a00c20317140c08048141e9079098692042d111710914141c0c6180054041d410140b10400c06203564103114004441c1030500fa0007060040040c0300b401c001c0b070340021300c0c18800c20760341b004040c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 301491348 1250 301490098 301490143
    0x20702090f070816110a030c03121107170c100b01200303150a1806030b0a091709040f0501080a0506090106081b0402070c060f0e090115030504050a05 66
    0x10058001005401c040240c1421000d001c1ea4680c0004916400395a40d000382c21855aa01401c0781c2e00c00803203185040c980140390080b401c06a118105201413400396540100d02108407803044100d40b1207080041c801003080111b1000601d90000c0e040c20f1804003d000ba06004000184900b4280c200310315014007070781c602c8035464968101508444100c0790751030402c10416920412036891002401c00000840100c0502002c0c0d0b0751406101d000e40408820f00d50742445010846000d007001c2d0004a542186070b00c0010655031540c4504195542c00c095040403035010891012907030360011180a42068580301500c1c01c1000501500d402000340300c1c024204407415003400350401e100a00441d100c4e9043c1042001201c4000a600d82c10f5120400d140300c0500000001030028401c00c00c0003418444031000000710b17103420008140c0c0c01421504d40303054451480e4104603071004240140b200d442d1101c481110803511036800642d01a01c40e100b04c503540b44a40e2a01c0d49440380c190116801c030a640714 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 301492598 1250 301491348 301491353
    0x2a0a0c0e0a090f030507240c1706010203070b0709030b150f030c0307300302010b01090b0906040e070324090b04090b010b0c030403060606030b0a0501230310180207 72
    0x30400c9511440080e4204004030b100e5403680b0000040303c8010381049030114002c000d101d2824960111510001c030100c0005011034121400b40c070a0041d1940890324110000c0d80c401602d5108078407402059001c0d514080d410f46e02d1070b04554001c0e140307008101400c800440012800d0340101e00491601068258141e550760410508000c1d004005000340c024501c1c0d02c059840000d96502991041605800c1c489007080600b200760002c01c1038200c80a05070b1080209041d01035000303c00058080e43c0e10030a282d02c43c192100c81b0300c508100c203900100204420050a42c0043d81c0c01e070020f03134600d00410100c480f8a0078a080980112104201c070480d61010481101184a11014107030103541c14009400c3d982c4403560030200500c070307004109400280c000c400d5201401241c0203580d103c03004014043e1074400c024001d020340345605000d42e00340d10012a545d0b010344103d0716100340003541c4140c1007035541c00300d510340d4001030300117080b11a800d00007041024040c5946603281e0640c0c41e0040e00c074042c50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 301493848 1250 301492598 301492619
    0x18030a0203190c0c1a0c03030a052a1e040302030f06060103060f03020f0d030c0b0901090b100e15040b1e0f2e090302121e0f032a0a0c 59
    0x55152405000350f280252000662000e92903088500366612484009682080c01c130040c4100c03000d40c0d059020000030414402480d501c014024117841c01300e04e6805140380c0c1076454503040f21b0200e20035810144a450b40e065550f6101c0b840c11045840c1650600e030360b0b680820724107a4240d184613195001281013014559140c402c030f030010304101c1c082644007451500030401c000c0900c3c0e40580110060300c0c0b0b840506024071840c2c128240d019940101924001818500034002d10300115082c280d1400030807450b0800c5500c003402d84000659000250b142c01c03810482034004050351a41150715050b08007026138076402c5d41c0c1c42d0041c403100054201c0c0b101c8802c001d80c40b4001000b86200310510150381da403086031480d000e441c0b0901c0c141e0745001c94200c4201603076100f08990000350f014078030000c4041007600201e4654002c01c41205600702e80040c4011154450303524810b405029441400340b150351140c1801c4400c0c20000b5001e428a11000445559050a01c818815079002c02610340810809401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 301495098 1250 301493848 301493887
    0x10240306020a0314070c0f0809120a061b0f0e0d0c060504080f0d0512150301020f0d051014010e060c1b12030403030507320115080f0d050318030a0203 66
    0x8807985507209140c850001b600ba88489000905100310007800300040014140440d00d03802c02c001e102450210451498550319051002c013260001c3c10500d001748014003094401c0a4821a502c0740c10b448003500408440404081804a0380041c909801c200803c001c94140c00c0540781940d00d03550750350700703021016183c41000c510402c0d1a40c840c081800c10a07600209443e040182d01d001d241c01d980300c01c0b500841c8903c8046031181c0c5548001020f88455114a0041602040a02e0280556964121301d04506142441a0b003501801c01450701000c1d0f21075622100307150001030401d802e040d10900c10b6883c001a820032141d0000d002542c081e030034a03000c070354090398258a200039440c00c0c0c21032350010101e0040503002000358400040d042d05042c1d1000d0b1a0030450f462180103201c240c4207281c418003070300c804c5c9120240d5403a0704030301060b0440c02150038066540309030014070501c041c1007021a4254002040301520300c80244c01103500310414802070000300d00301c0d4001d58950310103280c8175144025 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 301496348 1250 301495098 301495121
    0x120a241401180510030503040905040c0e06100f030f0e01060305070e091b0a03050d09051c0209060607050106030203071701110c0604031d1903121110240306020a03 72
    0x4004010020340707410700b046000c00d404502e000300c1c0d19250400c4408081e183c50300004c1c1580000f060110751440702c0e600861041d4083e003020511555506180c01e42141e098070f080e40c0004401d01e111825a0040011813060b510320b150010780781600e84541c3d070441d42124034142140e51500d40c2001442000c010b6800a8600300c030490b44241082c0c44d00350b6032a2201c16600c00084080d2403030000d1940d5041c0c000d0010340c0c0140580d0002c42c40e02000419404480c0506885601401090080f00e080c107081c00701c2480e806000500507407100010000b103500003941c201c2d000c0d074075503c0200041c0c0b000d21000006020b0400c0089440030300004a038295102001002c201e07650501c00841c2030400000c0c8280c1064060405034480312144145810620b01c03000d500d44c0108441214000d959200224442100c1c0540119108030750b8102c01114140007084941000760310a4a8103041940d05a201c44002901c0d00850140088040c0d24140d00880650095581e143e0210f00c8540043d05401005074070132 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 301497598 1250 301496348 301496381
    0x70314092e020c012a150b0a080118030c0c0b040b031e1311130509070602010f05151c05011a04050f0c0d1a0a090e0d0e0a05120a24 58
    0x180c42e100000c0c05a640c842c5c169500c1c40403e40345403034084020f0124042c8540013410080c1703102d2070302c1ca45000380941c02c0c241ca0140d1800f0200050620040c402c40b86452111001c000803d1181d4408548101d180e080c20307030b031011803428000381e03c1a45000510080c802c8002241c1c50340307042c403402030f0340412a0701c840f440c0130011402c000c0c0300300c46946402c64240d0710000300050f400d81c501c00b03c0d01c0000744044494400707152100740075644000282010440b15598024030203800740c00a500240d40082d50f0080c3c0040120a196030340745004214800c2c1510403d5030411b610442c1c1d00d440c0c1c2981c130b0821002070b500c1410f111103100c509040c010140d0041544401403c00d003840080c07003180d4800c40c02c01c1603096540d900008980120303003c0038aa003100003004040c2e0305446031440380c020000311a03060581d2040070035455401e4050480781c400114010302c0d1400e01031404003805101c400036181a0468002c201d040000a070311f41c0d0041d04042203141d00100007907010010302003220603501c0d480b82e220 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 301498848 1250 301497598 301497613
    0x608130f030503040303090501090c050307290717030c0702041a0906040b060d09050d020f1915060504021b190b061e090a0905010b04020a05070314092e02 68
    0x1900100480c51a55041c50119a00c0d551801d0407401096003140c01000780d420000404203109034070109a007610000c0b4146d88a495607074030700700051756170002d20300c80840040740140307421044e2102900d0164000c2d0040765401c2a4045180b44991084911814070b84002c2401415030070035124903100d40b2120b401c05144001900c000444441009200034403458480e214070ba4183c48280c1601c1152148000030301040d103181c07902641311420000003900500c100720500503071060004211400b44a4229180c14189042c1c441c0728040176204140606180c0b200000140b58030350384010284143c100c9040389071030000708100303801c0c40510b40086c2403101c02c092072440481c048003c03c0f608410100c80d0714203c0f0070780c0b101c07502c0030030342c0c42e541542c6c0710924404100091a00303030081c841c05031180c0c2c001c0052074103100400040b030107080c6100c00052030510403007000a02940c40d2500c600c2c0a00304107410030344902e000a40d51041282c03005044000c0681c442c0c1c03c3c542c03007440700403415103500142912 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 301500098 1250 301498848 301498853
    0x7090b0901300e030c060601080601170702031e1b0105010b0f0c0a050102040b0a09150c03081e19050109022104030509090c09120706120f02090607050601060813 71
    0x45018020703814403500311200340000780004502d02e40e5480c6000b40c0c288160301440c5071264898200e1222000d440c019980020240d6104030551481070505844684451100e82c1060000643c000d2040c82588010000c08a214102d910b140c2449400a043d86e0344e501d890290040404c800701a0307245450b030411005110211410040c1d5400c1d005080490346c4079482040030314980302c00000040c010354400240418041a000024080c07601a92100c02d040782d50340c0211140a81880c07807090000340000d44e1100004e104081545c2c03c0020103404030f42c0d030b40c81c68140e05800c00c826210840140500d901041c840401809a1401810355078000c5082c44946a00525903900c1c082106408081d0300f030019040600600645800c9280640f01081034606600305400d030340d010b40010b070310a02c144000c83c40c4e40c0034002001429604155504103c3d00d410b580700c00094480400440700f41602030118031a07907211a4064203149001d50010f2100394076101e405440244080d007401011101e01c08880013 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 301501348 1250 301500098 301500107
    0x60e0a03080f1e1206011b0b0a050702011b0503010f0f230d0614040209151005030a091a01090c020a0c060c061d011401151d0d14030307090b0901 64
    0xc05042c840d101680e40e18043d00309a900295501e030703040c420b400102e0039030f03103894100035101d00ca810280c903012018403110305482c100c10740b180d00c002c007031140c0000000c082d00301580105411228600010501082030281906c85501c00071000c0002000840100072010303a00304064002d01d51800c00344c0046060181010040c2044141d07503d04000d800d410340c0003500c42c2c4c03140c2e0301e03404c3e0000000c02c20000f00e0401120038503401d84060b441240c03000d0200c0c40700c2e0010f0341090f035014002003400c0c1400c40f80000c260340d1500000d01d061070040c0c0d121520300204400d6140c14004c1d42190000004940c1840303621001c882d0310403080021503000d0490600041d6089640c40192039032030030000040225494040041c000d24400c00c440c421581c0d4040002c03200540105080c80d000c000300440580c1c881803500034403010900c01c4400260b410848082a09400e013200301d0000002c1c3c030115103c030f859110141c041007001103010456200001708040507901000c5a4054241d5101407072402e43c5d0a0002003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 301502598 1250 301501348 301501357
    0xc02090a0608190c1e150f020c01140c07090f05070806010906080903090a080c030c0319060e010207050604050d02120406080412020c0a0b0702041805070b031f0f060e0a0308 76
    0x45030f18220030420501001c0d9a42c00002c044005000040c1aa0b0f0120101801c000c0d11456003a00e00c03060682d81e40034000d440003240c1c00e07e56402015045200d000440c0c0341c3c2d2164500108400042159404001d02801802c002c1c0c003080724049a00380c4407030804004c0300c03402030400e000c0000820902025a03406500e0004940c507a02d00040291600300500e0304612a841032180e10044160700001c40c210301082141d40840214290380700644220141522404107540880b14400ea1000003000140264810040c05440000040c01c1c00d00a46d00d4a24180c000e89042e510343d402049038182e040d50411400b5103c2800c1c0214604046ca00307200078101f0070f80a00020f10000da0300448004440c403c1100c42d908400c001c1c11a520180d030741c42c5034510b40e031004200f83d014034140b051101806440d403032490320a030380c44002003180521304001c0c9002600064a401000740c030072928809100504c104d6500076100313446c500c00c0179520301a405030012407003003101402404e2128081010600140030384 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 301503848 1250 301502598 301502623
    0x6040302060d0e15160e01020303160504030203070b1306020d1b03020a0f0605070e0616171c020a080a0e06010303030e10050405061b1606020a140304030c02090a0608 73
    0x71900c481c1d0010282c005400b090400b00940e01c10302c1d0450003110391801c502d0f8002d48034545090000c0c0742a0204440102c4010019409680201f0105614010b040d070841000c0c1d09501d4198102600c950000b401d0450943c00201c4400c40492081c4403440c94801d568010314481c00140a0681d0900c0d0142420198454800c01490800808410b1500900c01312001c1a840818540100414909440105410784036500010324440c2168090b08050086510820001c031951042201c144c1c2e541c000110728240d03078600e0302024014076508040c40e5280300d11480e5003210150311756610180080101c180102003000075402e0a4400452900c0828058152070301490007040c0000289101c62801c98440c00c41010b8902e0032003000144400450190302441c009290000541e090000d40d003079500402030650300714140080321000280060b030041c00c01d00c003103007881d00e07011404280380600d54200b11810f07008650008400811842d0980e5000d5010441c00e0082207441d0609892a99840c0c0b140d409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 301505098 1250 301503848 301503859
    0xe070f050702060405101106090a0335010603060504050c160209060406120309050f01110303070e011407030315050a2612070516081507080421021609090206040302 72
    0x107803425034a030b000c01c842c050a0042e02c84181911802c0004018911400040360755000761070100e041c0201c007246040c00c4980650b19a12184d1180d03804944031021001d5103140d848510f008075510210000481d8000c0005442c0000c09501d0078084c44150ba0f0000c1507090300c0c0c80304210783c2009100c401105ca50300d50301a50075031a90303900c2401040081100750401c00e4040201c0090b0310402d035101403001c042ea1000d51f101018180641e00564182c0001c2d01086250303001400001c200c07a04c504071031018404145051250b4002d0340c900002c150303210040035000252035030500142e1102081382180201000e40b07800d442d1602e418408401c3d01201c142d403290320080c802d90400c40e10b02c10002c820f8010000e00445030358100500e4580c1c0e0f142c2142c084e81c030440d000b030a8001840f10010602a440d000980ca4250036a40d0341d01046031008401001280e20605c00f1103503080c4c00f01c11340e44a9a507200c0340d400611240000d542c2441076042e41da400714034040d00389009440144c545d00150307011030b94103580307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 301506348 1250 301505098 301505107
    0x90a12020111040b090a03021507021311070f03170106080414120906090d0206041e08030c100b13060902180d15180f050106061101090c030b0601091d0901060e070f05 73
    0x40761508580c0c806940103000450809c4401e004c03000808480d0310071249058030300b081300d500405540013440142940c10083c400c02001c130344e030f110f115200d0310310a00c0e203108190100402903c024800f83c00040009030481d0801082200050081c1504051803000340505c901c2c014030f00180e4812602c5090003404041006413207600c441a60300300c440e900030300da40d86842d15079501e0104592000e41000101c5142d800000d490b41000c8201e800400004000d860f404844118240291890204168005c1c1c18140a080d600300e107842200c010b03220286015070765070b107100306401c26a03580034241d621a40c401c9820354001694041c00349039549a5100200c0d61403001100c9407040320320350a001e010803000d16002030807c0010346c803140c1620029100c2c035000c0b50041e03191508035a00517000a001c0c0054040a20108251060301c1c0e0303200d20145403810f400c54039620904403881700b2980000c0e0311030a03102031002d1810f00707000325400382c06c500f48030078500d00e40400c0c000e10f10360f103041507281480000138 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 301507598 1250 301506348 301506367
    0x5030d0c170105060a020f071d0c120402060310081603020a0512031e070c03050f0105281a040222061404090f020d0501080d12020406020a1407080105090a12020111040b 74
    0xa000e0725911447c203807070741d0507503900040032419045080c0c90222946580010300580c0c1010550b520008800042c003010b5035590b0901c4401e0340701914500f02100c480c0b8000410600c00c00c00900c01c101d00c40b59003030b80307185503105100c506030300307508110311400d2420340c0303100818000000e0300c3c40000d0003161802d40b400700d020817214030720078100050211160b150002c024031030006080740300600c01c01d00030442550380109480070120b2000d4044100c04112403a88403480c40c075089500017150000508041801c03441c0014101d0b030000c1c00e0100d5829a500080b02c4004000300c1001c0101542d0800c0300c049004142c1c2d4101d6403160380540392200d5079031901c043d2000f03040d905071401c015107010100306950b110b4404a5841d2070030b0b424000002c0071065401d4040d01d160080e5030450380150005c000c00c4060750754454a10001801800c0c040c07003082c5000444900900400e0300031040c240152505000608184e84000c15150300341040d03a040915515014100c101164219400612117036115985075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 301508848 1250 301507598 301507603
    0x507020f060c06041109070906050918100501080a0c17040f02090c04080c12060604180f140d0816050901030e0f0601050a0f0e04080c0312010305030d0c170105060a02 73
    0x1a4541041e4007103010321200350002070031401240a44191541d10300903800308a002d04c0200c5c2e00e18005101c20401300403040c043c0700036140e03050008180c600b04041800c2510040c007400c641100c5c0b00c8650807400c00207940c000160316041b00b6a58400d000300309800f5005000481083c00d4400c8500c207081c0081d090000540000c2c0c0b840d07600820541035030500d03040b030244a410500400781240500c5030a41c80b5490440504101d00ca240006010669a11403c100c02001c200c82420070210604410034001059407642941d450712480000003054030300c0b1802031a0102482e244400d0210400034407400a00e004c0e107075100c80005161550f034540d9050f0048024010442d90300c5001c0c841c100d41142c031040c0c0421498140d680664049090f943e403403140d140300d10610f1044581008020b0040307004100400001d22402c08110300302c92030055600350f0340031080b500360f0007500e5581021412401601503400b51000710006450019040800c048140031650418031949118601c0003a6010310140207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 301510098 1250 301508848 301508869
    0x1806030606031303110a0b070905090f010314010209040617071a1206060c0f0d0e0d0803010e0709120606050108010f050f0405060a08011e05070906020d0324030f050c03030a0c03050702 81
    0x2c030005e546e82c03540d00d03160400390a481911a03002080000c07034042a241040100c082c1300f810030a01c08440d6902e19160002c5089604ca924143d5540802154601d503c85025580c000c010002d1405030002c0284d983c40d003400300300d0b0442c50140302e01061821401000d03c2c2502d20440800c0e0301c52203540c980d000002c1c094410b811a0010f5401418000141580b000c61a508042805d8031140e038070001b400b040101248180d60020040d16050006009002503148403e5100145040c9270b5219615164030007c01502c19408441d856240c034030500007568060038280c01400b42c54540700600d410b000020320240600b41040d405140d0f02e0300020b2483e995612070f00010714031074000b0000c2030568007801d1042c00365010f54040c03079420f090100d8901440766281c1c6003203d0850703014200349240d108080303000d011100d0b06401305903030358a100ca00712003001c901c100045106180c0d016510078141f900310304203011043c0192294000380891002030382c01481000d81564903181013a511420307480000d00344880e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 301511348 1250 301510098 301510127
    0x1b0309030d0603080a02010507050a0f08040f02060301030b091c2c04020408071406091f0c061d0d030e0c040e102301090e030405060f19051806030606031303 69
    0xc2c1140007090010000081003135004550003441240c3d110401500c0034400ca080d0040010130681e8804c101c030b1710030040203400c2441203070300100d40d0301590001000340c2c10130380040d54a00300110902405050810070400d01d1300100c1c6441e41d40c106a518090644821490344500300d203a04603102051049022410742a114024011900d0b2a2070303601079507448856000300d250480c1c0d15200d40340e1602d000740035a40f070410700400c900d140203003c0e00004a81c0562030114030501c5005a0072000003482802000104071140c4141c111850820140500d000c1c03070020141c013414075164404810102c04191241c1c40b02040e038010442c03c903007040721846d20f2044c00c4100c070000c0c50090304aa50307a01c602c4840d0038014640d428041d407070b62540106000c48400221100c07465100700310800440c10001c1c05024401d10141c0c01034104210b00c4400740324007901100d4440003520004400742c43c0300d000c10504103842c00554105096161500201c1c03803910010b002c02c2c0042040e0a0140c00305481050088141e50707 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 301512598 1250 301511348 301511351
    0x610110c040e01050a0f0506060307030209010c050a260a14030627060414100303122304050d030c080a0b0a15080105030d080609240d03090801060e1b0309030d 70
    0x2d0715020b055009000075150345103041d042410110100c0c105001d61070040e04000d141514548135901e050300254007181c0b0b21418040514100e10100314103104c0d141510f03000c0e4840c1c00e05070f090400042c040f410015612101480103010700c4c8034150307011b0085141d243c620105a90381703031980340015281480340840c006020186440c05800141481c201c28040c6209031801c3c01040b518810604030300504071518031842c0903489003000401d00c660b06040410f45040800100011090030682c3c5034144c060240c108003820300248010010100076100881d400380c41c04100716040c500d0001c118007000741c8400051620307800034034080d50302c59200b1402131946900051040103801d00103800070714248540c510038000c03000d0b04000700c0d0059401611861000301031440c2552030801d41d01c0d4424258201480f00340c405004012603407281d80d900002036019131292107070399282c580401e095501c00d820a20301000e442042c0320903080d5161100e48450064203100c1c0d02d03596000c40007031460184482c0d01c104e06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 301513848 1250 301512598 301512611
    0x110d0804260613120806010c170703180f2d060c060e0601050904030507050a0c090902030106050f0102030a0f020c0604141309031b080904090506011d0610110c04 71
    0x104405641c03150751845160a480c255541c40c1e801040071410024080c01040c01c08451002540c81442256441030050500560b828007640791442c11100020315002941000241c9c03005043d000407840c003a04105a042e007180031705080c410460350011b4460190030b014802e0550001140316203c0a110424240c034a44444d61789100060807140d0f42007003903e038549808103050f03070000041030b802e068510240c0000c3c401c1d201c55a084500d5440044190b486024600b0544000303009048072000421244502007841c21a0703004041c00c640060380030f10300c5042d008151000c0c5903008800e070f035080203150410031440d2001c0c040c10303400d1004140e04903500820002d001b1860541022128071101800d80c0c0340102c044002520400302c41c1e224501a000c501030b8201210008003060000301501e2003840c0040c00c14000c4030200342910500030084423143c205c0c4c4014449140c080c1e0103195a0150060040b02900700031011500d9580540d200008002000b0321054101e5810010400000805030082006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 301515098 1250 301513848 301513889
    0x2030f030315130c0504060c06020919051216032a0b03040b0a1e020d020409140105040c020a0b060135181b040e0c120102040e070c110d0804 62
    0x490005200340c9203c1d4001403207100d1400080e00ca504401380c03194490510342401c00d00103940e100c0454100b15181c075000c00c0319110546030b041c1d8591041c41c8001c4190300c4107040604102180240c0ea200c60507960101c0f101508039914068500112500200156511010800c071110080100e4410040e000701d100c50010765081c0341801036104900604140985445281d0020141c07009002010880400c1d105040107601c0c1590080c515045c0c00c0c00300514140c1d0b9840402c00355400d4080ea1070381058038100421042c1464000c09405059a10180004050f5680c4800c484400502990304100c02c40144d44402990569460b8130301246011070035201602c100c00360aa030500312566014520580c01034800e40c000000d4006c0304020315a40884d02e20f10800901c002001020b00c44105d52085054004076074941d04121112002c3e440300240e81d072424150030354440c001c007400210412a03901c05c4807001c06c00300d1400100716841162508880041070a10301058060ba0f040607a001c059041c0002c41c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 301516348 1250 301515098 301515121
    0x207031101170108031206010903020d1212060602060406060f060503070305090a060e0c0406172104090e0714181503100f0e1204030209010b03070216060e010e0a05031902030f0303 79
    0x42c0c1486d00c1040441a549030310045076078150900c00250481c50b00861a40010070255880800c07100c2ea140c41d50b4000704000301c0d00251406e65102c040541c0190701030005204090041c1c01c00391402c408034100e503a2600c10000c1c0684001000380c01050b644c4c030003040761408140480e110b00d40d0880c4051000c12000c0e03c4968840c250480011311483c0384c82000100214000c032201c0700c0c0c4220001501540d040d00c6229030340314140040b001d0766000104001b00304900d56104012808900348018100300f424100705450603103c00300e41c144900504503070001a10710240c0c9aa5018000c0d00d81d8001e18a404400700c3c0c030300466200003803610390800743c00001580c0c45900881c0bda980030000c40b0140004126181a1403080f40406500701011030014480e1500c07000085400c4951403040301c5840800301a029204004c41e0401030001d00307910340344481581e2003081080c06c107204445680c1c4407450940042d6548030f02480d2160032498814407941550707401c0c000d078450091100c2c1500c4d540c1c500380c0705410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 301517598 1250 301516348 301516357
    0xa11070c060e0d030207062706050406020d08090601060c0f060c21051b091804060204060e06031006110a080309060405010e0607050a030b060d0221070c03020703110117010803 77
    0x100c9160008070b4900d0b14100c030241190301a00070345101030409000729010301c035809a170194404c42c03018100c10414a902854028081991401c1c3c07a0390804600034202954216584100b040400c2403080d0070354042012030440701c00d030409803034042040c034003050070048000c0080d140ca46404030080c1c4080c0c11455007d070b0f41c00281920b00880301141e80100482d41c00351411441c64031108280000e100c01c5a008246000009141101000c204d0000d051b07102e00454080b075643c2d4004c01d0030000c0582060800d10840011900e0900314503207008400b4060401e40f04590070030131000c001000c0e000c0c060000b505c4550f04810310702d60740e28200400d540e440906840841c1e8949c81c00c8460345061502083d11800f4006541c0c460345000e215207002c038081d184105400307a202da0208068030f12a07480d0310040c440201e805681c01102107035480d41442c0164001c0c4078906114070700d200840000c0d40400c07804d0030390354010071404201c1c510200495101001d4203c03030b07003500038a000100d0400700005c06017 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 301518848 1250 301517598 301517609
    0x1401030302100e03030c030c04120525030b040f15020403050312010603140f0405070510020d0905010509240c0a200411030f040501240e0c0a020c090a11070c 69
    0x1101c10b640451941c4003210620203c00e2070700c1c0c00900215441c0c0600d60000c1d42c1000c0054000c40c00e06440b040c55511214040d607040350164400c942c5442c0750750701d42e6203183c1911440740e41002c400340307951144014100001c10040032180420003e01c10030034901d034407299070613054a0840d200c41c0c59141c1190740e035100520b02d256404921000291440c407a0080c01d2800c0b900c001c0c6c41580e6250050391503003480c4043c00c1140d284c0100c010120381512900d940809140e519402400c09040b03d101c0a0520540d070f4205904001d010400100b03141c036aa040950b2402c0108a031030182c106000d02d165a9002d81c2034002010b005042d480002c2c04001c29074600d0450704c20140841c00d00c0340000f000221358443c0d10000d149401400011411003000700740c6a8030071300800010468601c440b03401c982541e0003104c4501c0301441c0d89401d106074a43c481550754042c1c1c080948501c2c0c0182d140700a03595207a000203403441000d6103c00039410b18456002041000841649680c840c0d0f12440d00190110890040c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 301520098 1250 301518848 301518853
    0x2009040e010204060905060d0b04020a05030f10080c010c02030f0706020f12030106170702030d140106030b06210c07060c08070e0d02090703270501050103020f0a0e060f0a091401030302 81
    0x5890030500620856048618644520901d6440d1005101c2560000c0e1218005a944c030720f0000100e48880c00105040c3e852595255968584240c00c07446113240603200140c52240580148031159001403811003546090800d2003140c1010320001c1c2c0740c500c0388061003049002e5880300058480e00020b15189840e418000d40d8411b22921024600340d010900c1403030700141342400250000c8002041c2c1c7e039040b003200d106403440c11400c0300c1100156000d284800707000484800040050319854443c10f01883c0f002c0319078500c0c4c181415401842e41104401c0040107048881c049009010085e084402990340301c40c082c01307804a00207000e41403900850b5188007043d034400e8603d0f0103240c140514400664003c1071034019171a80007044006110600b2012100490b04081e10180c5101180111516100f80008034942d0b05500c14090203026000502d4010fa04884c000d00a01c891014055032011050f1505c43c4c146007104006115140907030b000c0d10083d480c1c02d0f4055507100d20241540d040c0ca019408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 301521348 1250 301520098 301520111
    0x9010305060306090607080c090303160b10060e1003091b060207060906050a200a06021305040203060630090d020c152703061e0903031501030902010201200904 70
    0x181903c0c0c03501161310340c0130f68000e42c0c00251002d0250524981004036890b9590130200c2a001092540c0d210035001b00c00016082c10300d00400c0300c0120032039030207006508690411860000040d01004040101034403e541041d0801001c6220703912442046410051000c03201d4084003946a402d43c0a00030000103011700c11000c40ca90780200800c00458000f9618030345001d80424080310094150b00e1b000402e41c198594000400004200014046015510040c3d54400710030300300c06d0804559000a0003140181304000081d9606015100c00c8100c00d411a224614809140c10340c985007801040440c1c80c200b000d02490807800540881211925000c5803000000c000400100c00f0690101c5100704004100104840e1030541009034480b640d490300001c42042c4100180c141001121007000c1000b00b00e404079aa600207100d03440d04808604051480d600b8040c1030510060700301c82261381030540300c81d14402164401d41c40b40314110b00082c06400b0591002a251300154401c4001500c15030038008c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 301522598 1250 301521348 301521361
    0x5011a010207031515120c09020a08150321040608010807030c0b160209040818010311160c0e0f2a03280609021902010209032d16050a06020105040b06280b09010305 72
    0x1003124081511501c8004407991410359120cd22084251200d40501461048000c40c00c0c0d4030025115140700f00145a882e80c0c10310f14020a00d0701d0507840008158454082000841c405c5080d60064035600200f0700c0d41c58a1400150380c0f401882c42c0005d4120b941d050800090040c580081c240e110300d82d0380314154640103c0c0044050300c082032039070580f44034204405c3c20000740c0240429403162041d071040ca81c45503a060716a601c0c0d201100d409200080e0030341042001d0400e400d038000304111ba0303031802140e002480720001d1035000c01098564040000c40b950b44c081c0030b42c804000d02d41300315040c1c02d0101d00c2d01c6460340e0000e034208107282ea209001d01e682d00024640107009545d50000040c008080b604403907451401c5403002e203014000c40e894004149036258009010490b00c040c8043c003c007580928202c04d01c0742e50100b507804042164074000501c000a48003a04c0d5542200c0201e48071400d0900c403d4000317072074800d2817141c4028007591230742c000ba914400202920306024262403c00141eaa0b52 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 301523848 1250 301522598 301522601
    0x21003020304170306010201241a070c18020c160e01120f0605040215030114090a02040303050a080423060f010504090f03110c0909030705011a010207031515120c09 72
    0x2620020550b5052940f14054002810040c5a11010520010807140034401041ca410408500122000185d54009100d45010075a08034403003440c40c000325141140b1b0340c40d066600c801c079001e0341001c1c90306821804814203498050f20010030803101034450b80c005003141035000302c0d040e00c07440c8560b040050000881c085201e4000080c5600400340400c8407020307030f07039440003002c0007401240e0000019000c01c2e8490400d03030256001e0500c1055082e180340e07070401000f1980e5030040a50039180c0c0100000d1002036440404d4a00d01800741c1042ca00076111881c119030409060400800d0014003810b100780390384400076085014801e02d84844c407503030340c841060005130340107500081c064015031034444000910403c40051080403640a48024209100008020040c2610480da1952000c6030100601000703104c1c0212080c00044007403000010040040d4072148144009001e510340307044544007520032500320010004600709001d06035520341c1d07889038035103034a081d09980c40e80309420081000d03c0c20703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 301525098 1250 301523848 301523851
    0x9061801112d040e01030506010902270a05130f1b020705060a141201080d020c030715030609050c071b030b012105061923011e08030c01090210030203 66
    0x40100034030303120402d010740051044410303800ca11090321810582c021101c09014001500202c00d07510940e5141d0700b00a0f20380181038206503900c4d44100003040010400351201d407540e0440100358119030302c010002800d000c0301ca90240340c105495500c0001440d0059010400300e0000500c100030081da81e40c2a908070681004540c4090b9224480c144018601040503001c1c4c0420392a000b20105500c44420706039401c4010b000300b087c00300100500c500d0800340901c00c0d22003090b10041030741c0d904c0e280001c1c1d503940c401c5c8613000034901414096409e02c0e1203a00100050234145209004c43e0400c050140078650003a0702c107a407401806200306030128941000101100d0f000030743d50055900713054401e04030411114404904c945c1404005001800522906100d80c0d80c820b210b9040c480403060503800d5070800c82002c5030320106102160407800e82d092550341500e03031007201c004080c0c20008411a21145a0300210050701c004039207495141c005410071a54035102313480e2440c0c0e00b007281074280d082c0d000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 301526348 1250 301525098 301525121
    0x20903210f0903030706060e04060f090c140303250506010608010f0b03190c0306030b100503031e1201030b1b09010c030f02160905060f0105040513050402150309061801 74
    0x6041003421919100c1d40301400c9102c1c0300901356860090981c3c1c603d0111640e560009914401032010007003880400e218401101d6494401888005015503c1e40d044003254010011642d6200c0c1c1c14141541f010815030740400400808142a101c1d002111041c1d200006001c9502c3c2c4210030001c54130621a84400c0e040710103078204141c0840c10701c1d802c840550001409080c5651040c00348440c0920345014400d464103c1e501c0000c0c1e11070542c18180d03c5c8000082c2000640640c140c2c0070082c589000048512183d042c21807110b0110000c04041c0c030328402c0000c0800c0400040002005010314801018090346100801018614185000b08038030300402901d00d011401c0f100f551000309004000c06000c5d000030784180c402c0c0c026520640040b8100030340013611426502c204000f02d038207023405507041d40842403c2641c01e10303150100040048461081e004a41c0392940041000c64440b00c103403c3c2c1d504078840c8015180d20301001383ca40c4c1d41008480041884c81c406020440389a010703c40c2c8c070140e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 301527598 1250 301526348 301526413
    0x16110f030309011d030a08071a0901150302130906090308070807030b011b021207060906110f0601060507060b06030c0306011b03121a27011e1202030a0b040501020903 73
    0x80d44ea046243d100903842c0980e078041c0601150880081d00c01e0005026051142c13003800002c0c2c84040000e510400000d10011050b07140680b074a080980b030f49108802c0702c0c1c0c12501074070b000c81004020405440e074100024250303810000ea160030180c00c804454810703041c40e51059250395403514201c069500b922042804110000b100211401b9106030040390180060b0070b8071000406d42c90360528110065201400196280005000007540002c2c04020322250030001c0503400c171903055207501ea2506208941c20301600080030810081c1d2030304100031620008245c1500ea1409401d170b040d0030790080700c40da07000a0000050165150680e5405108c02d609640c0c1c1032030400014154a004201c42c4480004402c00c501e040d40440c1da50304854030302100c05240d2070000c0360070107120b52005001a040800ca00585041030140c01c0c02014070b8000311112084248111400c60002c2070601c00c03107160140120124004110611605400811150300706400310345060389148404143e440d898800d00300b221 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 301528848 1250 301527598 301527617
    0x1b07090c030b03120315100e0a1e0905010b091c0b1302040f18170c011104031407120201030c050702060d05090d030b09160e090405060a050a0603020d020103050c16110f03030901 78
    0x40c02c1100b04000026142d01f4107123010240e203800500790741c0e050f50103c14905450441d02014403003c5070300700300a0140345401c1c80194106030841905000710260a40510540d44c1240c110041007030007046c00b103400101c07d03c410705011401c803814803254001a409141400640904020103200c0c20030140b1544442d440e400701250780d00c4400711040c41d01c0480c004001d011001403031000b841070011070240051050f960380e10354680005074162000d200c4010380c1103040c0070132450051a803c450780903130900e00055443c1092030140c0f1140210000a504603902081c00c01e07410100e42c2c4818011143c1004659100405000032000d42c1c044000c0c1a0b0000403c101081300074048410b082f04540c282d041c001a0580990b0100e83d11600488007507940e5442841800610b141074420a0340000c0c0724502403000d5070071034000c5002d074510140001e04040d520400507181e101b803603054514007d81e4084012000c621f0303061001c041883c1d214400e00c40d2a1403510f1031210320300003046030410403040c0c4603c14903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 301530098 1250 301528848 301528891
    0x504240f230a1d010c05041a0306030a0b04080f040b07020a0902040807031104090f0503120907060f26070210050f01030f0b0a0b0303190305090f031b07090c030b031203 74
    0xc0c1c16243c10031015003040d0030b58010502c0c001c0c00f910521460a40d20750307031158601032409100380003c040041c0c054008009205480d20041100c41b42940c000c2c807604465100c1c0d18010085d8840c100d802d014181001c075001c0782070f10600d0010104680200c8002101d00c0d1a5001c4000300c2c403451040700c8046d40a10010000100382c03882682d94100b00401c00111100640c5490f05a460410800c560503000003842c0600c400c0d00c81030103074010211000030724100d410008054003501002950308140080510b0704003610a5459040650030702c4401c400c15035091441001c3c0d80da03100651401d0300d442c03d040005541074000401581260381022040202504546407003104102c0a0200281586ca9001201c12903c0070802054045640d4540c2404181c21600080880e00084d2840340c041e08080c0e5500790b924400015103081541045250f09400d803480d4100e860f215141d4860400c0c1340c14110000c00280e007650103002608800e46c02d80300c2284a040001500344411680846d65003166102c03802d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 301531348 1250 301530098 301530101
    0xf1017010b030303040309030b090102090105071106072102010e030c03030c1c02070305040504060803030403020d120b030f01090c060c050d0509010c02060d0507020106080d120504240f230a 83
    0x106a54488000580340c60180042401d41d0700403181500403d0910801300208500c0c500d060360f100e03d05a000314108484000024400d1141c520007403d410704e4610881e40d141d0b40e5200f06e41c40298007a41066841807000c0b03107100302d00014581c12015502e002c18240820f07002104441184800c07501840c5169035242c1b618803182c002c3c801c180d400c0818116201d40c4003c00348000c10400c2e00903201d440c0c0751340c0340504000039034045400840c80c5400174424400002d4000910308001012030070241041151045c441c0003c2160034030340c541c1841089030310f05484d2019880301d20694010202410207540366003055a0414800100401c0e40d0702c104c0c0c81c3c6031f00d94400d00c050305010005250500701101c1a4000072175641040c0c1c0e089820b984c1c0c410030b225035a13409100f0f00e0010640300000d032407044030581019011280005c0c404a99944035400201003203401100010300b4019500411f06242924425000500c0030f4009100017a107403038140030706401141c055004003110880b00049030390300c5020860 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 301532598 1250 301531348 301531379
    0x10030905070e071103040602060402040f0209060306042409050a060f0501120218040203160207140d0807050c030a080403111503191b11011103090319020c040f050603060f10 76
    0x804204e4a049103859801d0248028801070040d50b005040f80d00b01801004200c0700400004d510180c0304009a20441c3c49a40640342c0c4690304550004074540545040195421544911400225144008a014200c075400301d8011040c0b8041048411b4803814480d00300600e90140b0750204602c030540d44034050b01c0b03400611900881500c1c000c1042c909a020405a0b001595200c2a03131300d011001e200072950401c200002400b40b2080320f048800e8900101d09850100c070ac002d086100005070b000144807017001f200000300f40280c02c940e0780007142d050008880c0c20900044070044403003a07181a8603e0040903101106019100141c515150480485045180001c50340d094580b5500407480c08907140d243c00d0304103e12519025003c140040c2c0d00707821584080203400e565403042c414850090720010503102d039505d1041c00299054200807041e0302c0c00f803125160650003810101035003601c0440c0d411403800303403401364115206511880d25214581c00120740e6114074243d14001004454a46142c1a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 301533848 1250 301532598 301532611
    0x303080c0f090301060b04060824101b080318030405030606011b02090115020c01050f07030f1205090114090a050604170708040308120112030c170f030702070510030905070e 76
    0x19241901c0b642c0400c0c00d43c1d8203030b400045190300100302040720f03507001003e4690024409c0366040030780c000c42c100d83d0f80341c10b0491009401754600c0301d65484070500030f41c0c0502c0941c140d00000c401c42c580301c3c41e0106c1e4070351048030b4404146620042c181c0d84a00c0c00003d4809554005020f4409540c0303440045611441c0060744c48040701e0580101000750300d80005c0d4a0107080c1044848400ea030302d40300b02a10b4481d102c0c20013410014200f01d415140da1504d020740e09501d0780b602d071081c4000b080f040212002e6810a050072207051600d42804150181544401200050842c10700d55560f500e070034294540100900140030754100e00009000a44100c407070304501c0640700c5180782491225100c0c040306030007139082182d410100080c5440170100750080240100301e00c0c002c082c46001d0703d0303400404407181c0b03480c02400c1c10b99502c41807070030f010b40400340c8402103208020349449240560000b50384480310311500d40600c480c000201d0300e0354880d01444590507045401003801900d0040d111440c0403004103403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 301535098 1250 301533848 301533877
    0x6040b070e150a030c091202130905070f06020a0302060c030c031906120501230408070b07020a0609060506041a06120402030c1c0b01061d0f03010b060f040f050a0303080c 75
    0x2e690004502502480215540008140300040c501800000303c0c0e030070445088603400d80d1000103a603155041d03205001040c80110380b035000e030700c1e20500c0c025441c0c0203141000c0185402140c85940011121f0880b80241d00701d95050300d81c00603040c4103103c195040350002c3d1003000003a544076403204107190702d003400b00c4001a03040d40d502083d001c444800041201e19075115506480c412510f80d9401d404100360030700c1c4802c281080d54502c011481812001002c0401060000d07075038600901c60b2555003904014107100c0441a403901c0002000201c130701500c42d6142c0b10708a0b8007408400b9011111601c0640050710788408502c01c45000440107208a038144500d610301d8006840d085040c0451260355100f11069401a19040c3c2e07420805030030400402c0039106c071001012158044103410a0020355140d4441c2c0e0301c5401080c0036000101c4038581240002424910400c140e000030811645200190300440d40c0341d0f801c100301842d0602c03020340003c48450118600e061110000d000080401380d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 301536348 1250 301535098 301535119
    0x50921100203011e1706042009010b07060c090b04120f150b10030506010e121c0f110309030c040513060905100f0507091a2101090b010206040b070e 65
    0x14050240d0b48242c0241ea40300060041c200c2131691512402c0d40505807a4528015042010000e0f5595403030090001d0000d000000d0484000701015400314000200500b036400d0660f100c81c00f000040d0300c403450803100c0d5171801c0c25541d0601d100d4130105c02500c1600141600d020315055a240c007602003000c0c1030340c5105c0e80554030800501400015900103d03030010101d1f40c47c80c40402c2014040a044040d0145814501003080a80c0c1c40340c40d4107a110b0b01110501c80035101e01a400b80341000c601c401028144039504440d80c010b8220700880e080c010301d540e4400d050442107039007640300d000346840036030581e104001081603454960032040d4170054445c543e031601440d0b6240e000503a04040c4054a00750801691068032411318010104d075210f010500740008d040074000141038226030701c1030170f01950f0b408906000c1c03052500c04031203d000600318041940e00c400d6000845c461028440c049540780791032103058440d40042465441560848a02e0b40301d82d60380c12003543e45840c8061150b502011150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 301537598 1250 301536348 301536373
    0xc02011103040507031b0e0103060c0e030307060905210f220b041d01052110020406021605040e0601060503130606030f0b06300a0221010c050921 64
    0xc0145200d1801403005120945c03a604010a0401420350708401c0703c60703000824000f00c07801d4000c007811039070b21510026203030b9090001203501040248800c0e6140c040020030300700b40003107a0080400e96000740d007655010880c03030f0603410242d00e11301d181001c0e500c2d040c001e5400400c00303007015141841c0c0c8100036006100c1c2c06e240c0584814079075008580a03800109081c8208158a00e8001501d00c94004058865040600042140210b404841c0414110200002c80480280850501a810000259262500d5440294580401240e02c0d5448401c034840020189030a010361914054080e001c0c1c0a941d0901200b142c46034401020200144050005e2100148107803103050019030140d04a107800320300524207201e214202900d401e04c1590305461004030110300040f00052101c21190f072459001a071143c2d24103110040318060741c0a585c0c002d41360312040d0403081344154550b0500081000e141c0d02e080598241c012049800d80001180000040314a0b4003042e07108208540003caa80c48030840 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 301538848 1250 301537598 301537631
    0x5120301150806030c060409050402010909020d020703110a02061608040b03041202010f0b01090b070c030b01120b0c0a0903020904030203120705180406030807081b03040303020a0308130203060403030c0201 90
    0x280d20165416030229000c000d40d661000c01c20343c0084048026003a0305014000090f124015405005030065482000c40d046a004007101001848156015501d41d41d915400c03900a4000768002d23004105800b034800c0c4880e50119448c2016a4010031003030400c04011071854068441310b90444d00001c0410001c40c00d418000c001d148524420b112281f5980701901000b400d40e002e0300044114031f03040c410601242d80c2c02c003400310700743c502c1c001c0c482d40ca426550a02e45111070349584094080030b018070000c500121259076001c0040e000f1182c1030701c55101e00064131098452201c2ca200020896541440180791078000c69800038080d20450b801c0c510b0700740090503034031419203500001c21000184071161708060340011b251210111401c009041c0b440d1280403031485101c40040034103a0000d030300d03110300300510b034441c000203c444201c0c1d03210341e286e1070040d41d1008007030002d4012031303061000140c075036034410862080181e020b40a401e40b41c5843c0d40907006071054804207001d5540310010081540202d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 301540098 1250 301538848 301538851
    0x203040302150c070c0e0f0103120207121401050c03010e04230f2b020309040c050705031c1104210312140105040e070803070305070302031e07020901210f051203 71
    0x2060f581651400306152065041d00d1355400301a003c8003203003c200107660514100c50440384c001c045401c149000220032403c00400da00720750030b450180e100300000d00120004042003402d0290013003040ba158009584240e010910948500c000d698000600007806900c1c84090000062444c1850201d4030360400d003400d0303c84001c0421540a510340082006165051900d00e0442e840c01d0a0008080384000303489200301c00c8a02c0c0980c0d11038050303012141c4650100d480d45030300f0006032130f00e8140610002d1a000c2c804100c0a003a40d007442d0041d08003001c40400c07102118075510703040301c406164440d09002c8030b01d00c41d01a8203014291603001c500070003a002c3d2901da245d00a02c003c0484d03041c58100000c403036030001401e0003548000410700c21080b00004036421a505400c0c059103e140d1494201e10b1403288692552020f4400c80715211400150702c09841e00c20b208541d004210ba80f10001103854070030740395100c1c00c00390f59010001c1c00310706055905640c440c001c0742a0344030b820000c518510380c0d600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 301541348 1250 301540098 301540111
    0x10203010510050a20100b01052505151f05100e0409110a080a0b0a060e0f2503020712020a15020c0c090106020604030216030c060f0315061d030a08030a020304030215 73
    0x804564100030b070310321464007107c03000d080c20340c00e00c0e030480c0181c0b000241c2c500314003481020700c1d40300c2d00502104100b202079072410840b001b050391410300da03e030803c580e03840307401075100349880800302d803d14150107030841c510703881e40d18289210705040402c130140010f284290b54003012081560f42035124001c41c1000740801e080100500f0005103001e208c0c0500081241d0410b03490403d060058460503004107800800f02d003204406c1d62100104000d4900010160a04901c0c01d0300361950a0358141e0041c103050b07030140b0000451683c60f50b0099840f42c1c201c05004120309402d501e481da103540d90380c2c040c2403118080341c101d5202003c3e44012070500c250a8001c0000f6074010000c00c81016410040c2ca1480050b0b2054640740515550310003104c004280034010030710403064000709909109500c282e548a402e0310402c03c501303950b02c2010b0a05083c1d9119a13501d100c0c03081c410074460170700054203003100d640101054910740e110b03021100290800f5008a045000f0b03001e00e80c0040d030166150303074007650 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 301542598 1250 301541348 301541353
    0x7030305180106081c110d2304090614010f0228021c02090619061409281a1b030702091e06040b06070605060f061303060b03010203010510050a20 64
    0x50005c1070621200040105000c100074803448600d115440c04102030828040f5800d08900c00c0041030201d845000c4040d41c6004200310114000a20003625001041250741342d000c100a1012804011203001d80ca00c0354401c0907901c02c01520782e45000c1108008004001000c217542c1c55240b42e4005140800035039003d441c139a0004116200350300d440c2246a410400888043c2030307112144c014040c0440d15842024244524031603403d0401200804459242c0b10042601500200402c0a2403140d4100b02204c0203070041103002042941c0318240c07804038180003c4600c0c0c1000b64400c11188040c40140642c282804140115001600c410b803a682c040c101c0d03040840711100b4150803d40b180c243c0200618400c41c140360300000d1586401c13040744c20550704280c01007038135600c1e0030108018a145811164006000203061103d41c40142c0b20300058920902c3c0c2070004005000805007030380000e00905a201c0d19501d640807002c1c3c0510001c002403001410000101110f0030038120035951503000c072065a8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 301543848 1250 301542598 301542613
    0x9140f061201230a090506070e0a03060e150f07170a0213080d18030f0b150319050f0d08010e07110102070309080f1506060a020102040801151a090102030703030518010608 75
    0xc2c0103160204d6200c0c00a403401c00007120613848003559600041e00c0d49085c0b000e1403c02c41c910b6151a2001c0780034507000b80090140302251741d1619590409424a881d0b1070440c6030114052881801d50580203684d80d50b250b071080004610b032801e1003040645074000741a400c000700154942d44171404002000c0c1c60010301000580f00748060070310071503d40c11240c070f0042c0000500005803500c0d40c3c4e56083d13400820a0450781d591035000d401d41030140305808d82c988604d01004105080b50041ca02c0028403620039503400c02114801103945006800054020400c0310006108080b882e00c070040e8081c503035241102040c1102c060403030890740525000c0c0e0008908580911580b4009c1110006280350503004003903860804604481c7ea40003d050144a80400603003848014400d4060320080c0c024a0000c0069090928540030320044900c201100c1c010703445c0f1000c1d84d06290200303a8a1803141070b0051443c100483d41e08034010600200000d1042d4084480c00010303030b40034031031400a0b003840300c010801c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 301545098 1250 301543848 301543901
    0x40b030102120703090210022103091510060314091b130603030206011a090d020f0607020a121202061302060a170f0103031409010c021c0206121009140f061201 70
    0x41c0c5184441020039548200310101070014003c960304200010b440c2c52760b072640c88001c1014103100300383c0b000d900c03850200e400703004082801000e00812100140c5040050800e407415002d1100b80c2200c2d4407009070041c4084000070030300d00840500f003104c01846109048180503c600c100e8200303403c11f60060f4000c00c018002200580e101441032142400214140842c000001c0c0e00000c11227002070155044d01d200c0066900e9100560b14003550080034001e51686034007a00e200001d03036038020740b1400b5084480700741e107a0001c1001801200308003109055401c0c03070740a00c9003981c0460400020030540740880c45410300c4803041d641c005c8415603c0440c8551542c00d000703100030300100050201c08ca00b000503107040e86e0071401150038140d040d1350080762540c02d200e4000000d504140040d4201100148000c040040c02064520500000411102e1240c40302c103150120307030700b0f0846081c210323a40c40d000c1142c413885141d94981c0000001c01144c0f9002c0340c28601c50a41e00d0b48580c0318200081490344418 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 301546348 1250 301545098 301545109
    0xf090c0b0f071a06091806060f01020321100b030c04120203070312180e010807030b0a0204090e100608060c07140c190603110915030903041d010501020d0e030705040b0301021207030902 81
    0x30009801c0000e291b40c0101d0407041d0307884103400380020344120b9010000c45106c0e4000c0c015581c107102490b461889100c0c030a80c4403070404204480c0381e00740c00c400542c08150f04600d50300760707409a0803071900b403818681403c51500914000a80c16681442030a500000055840948800c81803107983c400e003c1e204140d00441c8030018940064034540003000042c00580400203001c41280c1c1c0001c1002102d07103a1745245002407056070006800f540c18018200903022001966001900f0a18401c0160603079a60034581c0301d480c140c0388202c1c110010891034002c2a88035a109545101c0c0e01c050340d0310b03414040c2c001028a4030102203880014404c0408108154142c03081410041d6070b20401807500b405000051291850b0401c000f00c01c500c040f0228015402c100142c1307000d4032140303140d4030000c1009032a0640d440001d1148ca80140320341146c090202c0c5c424000c09860308000360041100500b00010070000d41040710041c3d825640c02d100190117490300030050340c00744103103440c0003c08603484c0c010300c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 301547598 1250 301546348 301546351
    0x516030506041e020d0f14070f0e0f010c030e18060f0909122209060e010909020109171906090c06021f050c0405130f0f090c0b0f071a0609 61
    0x910036450700c0703460060750001e1900360703001c40703c030b5400180e8030075003400000c0060080c4560342ea111490104034010508141c0c000901540064030750500c000000782003190305200d801039864200401414a80d4594007c7d01c02d02e034154401d0800003080f0302d0040202c0c16560f2100154001000e4441c1880350030304106845d20740d81802554400501e18220119541e502c0c0c20010427080400b0000c1d880d01c1c1d86580e003c01c81c035000c56056442c0700c1643d4445491003e0706450117141200f03011900000340c00a000d00c64a00d0450741038544e848078601d801d001c0e01621010603484001ea002e03406810380c1e10b8208069242e00e191040074009442c0405003080d980b072040e10b0708203400750f40c00b4000e0700c07a41070075072144044601000c1d4404280f40c1c1d1214410003003402140d12107500480a0312400e45402081d400001d1400048a82000741811014903002940c214020217070100103640000c2c049007590384020b24004411080300c6140c8065903550b001c1080d07940b9041248540c1c40d605001d0f1518042c400036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 301548848 1250 301547598 301547611
    0xf080c071a0a061a0f0304050a0b07031a010c030c02040e030f13080f03031e060105090405090307030e100906050c01021317010f060f060f0c051606080c030c040e0a090605160305 78
    0x2c46421340030b0200b102061045038004e0403411408400581040b0042040781c9000c0d078005241d81139414101400740c040c150102c441d8034042c4464059000c0d652040038800c00a0782c041d5070300d1000c0403440c1c00b4800140500044400e50303000030484e40304601100c200529400c18404940354131240340c54191400c0840f05185c10182d50410824801c03002e25541e10b420851300ca4907551091a1940401a1210300c13030301c0e00307440e00b181c140b00800c031501d94040013915006001c0d8507000c0584060504102c0c5203c0d106181c2c030040346560740140041c034402c4029100041844000510b05105c80ca00c404020700e1035480003681d40b400c014440350440c020b015016100c0081d290a0010b541003103000c0320341c05043e004480802c080012183c062038410713203480e00ca03c1d4000064800110002c400007241c2c1195000794000f00380c0d4440400c661000d6001207900c0340c401582b0071403d00303041c040d858003c1a80940103500c80c41e00c0740c1d822000b00b48144199405086d505500780b00555244c00c0c068242c40c0b00a080c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 301550098 1250 301548848 301548869
    0x120a0512090a0510030b0405070e0f0306071b05070803040f061106090d0e2404060f08061c0302030c100209120102070507090b0114040b09030f06070f080c071a0a06 72
    0x1c00c0300e5100c1c0d8030020141d030f500300c5070b50f1204010428114014070b40002481c1d40719003040c0034031201503041401c00c1e40010054039031940388941101855911032095400e40c000400385183c85c2c03004810a111b242d6210f11407020780c0c2601e030b0345100c080c1c079541080e04404604c035188030341004050b401000b002003a051035400303001e00d80f90000c14940c40b110001c1288091003081c149500c02995100c0c2102d665481407883c120401c16040c6d14010315411034050400031458400d107803a81e650264032258031860b8010140c0031540c0c00d2490381203400900c0c503022425440140000340d4402c1e42070080e1100018140401600e402241b401c01500c40c07100c068500039644100518000300b01d0106d2a001600c1c00c11742e02280c184200c1004991058441208091149000c5408a0a000e00800400300d51204030101e80300441c0c5000e2850b101c1c4002d44004010581c0c9c1c016001d01d07a4000c043d503680c004505084d00d802d1041680360050740c11b820000e102409826042001400e00e0f081c49050702401c5002c82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 301551348 1250 301550098 301550107
    0x20307090209010206070809060703090809100e040501090209240403080d05060a0f0605030a1505030a060f0f0219120f05070f2d05131215061203080105090411120a0512 74
    0x88d10380d162000a4104010152144d03040740600c0009001c440039158041d02c1e06401d0001501c004004914040075103210341d04000000030f04401d81e00a440054400414019104104103504481c01460001d8040e0074101803000002040d0314202418510700794940c04aa5407510340c007040350303041298000380f41100c5602c01c140041503022058951200a0000000c1c4225854584010301a003035070120341e2502c82c464070001009041d80010700c00c68a80c00b800e000300b131a00d610880036405051200388510680e0322030703034160901c25146034100e8070841a00003450111030341d07090309070b40702210040c0200d180410041c8000394070040c154000ca0034240caa06030704801003240390030402d01394007060810078042550742ca1020680040300050a87c0c07040c0c0c0080ca40302c0d143c00c5808040058909010901c0d08500144c0c0390f80c0d11040c151442e41c15502d00089a081004000c5007030b00140c010b0300c020300500103000041d11003181c01003103258039100070054045c080c684903140c40c0550081e42d50b819001d02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 301552598 1250 301551348 301551361
    0x120c050a18020c15181b01020a08070c030605010b040617060604090902120a060b15090f0603070c0605070305060f0a0f2105030f0306010e030105070e090907030203070902090102060708 81
    0x20007140484215020240c1e83d041010021840e000002c04600401042c020901003400d6a0074040c0c0c1141c0c645d40e003540c1440007821008201c0e01a00724040f800340e04500c8000001402c0c0c10010840c8c54480c4400c00d01d0306840380c440034109ca900342c001e81040c0c01d00190a000854100100441c601a5690b40c00d03018607002010802074003803482008080c580301d844040466607031103610700385451030004450f5045400c0c18103034040d28001d82c2850203054078014241c0301c01c0c0d00300300712100b401c4054204c2e80000c410805200f402d9000400f087c08011008250304005840c1d40a140e02803a082d66010a131403c2030410090b1a4000c403c0c1c061086108034401c221070003c0d42000d8007183c500c41400c986680c04d40410001038000d4140041013804000f56840c04240d00d14041d5000700070a07a40c82c15082410300502d4202c2d001a94038001050104643c01c0592401895566011030000260380711280d0b01d60100346048000e8001c0c902e02e0ba008142411702c5e5a04100c0d032030b400552071070443c6550500d032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 301553848 1250 301552598 301552619
    0x20a0302042003090c0a0b030f010e07030209030d09050a05060c06191103041b0603090809100201020903030d23010b1213170a02010c080c0a05160507120c050a 70
    0x5110003801662a941c103540c80c0c40c0d4146a0008503449104080c3ea24548201c901e61103101030781c00070340316403030f1102c0c0880d6407441203059a01c503140305412000140d08280c0034844c8c0c10b10003040c46003055020440c2405a0700c040c0207049005a050701c0d103d90140c1000d04010700102030340c00413801004c0c00d0200000c0c1c0d6000240c0282c0001c0c4444a200100c480c0d0351440303014203240060755981540000c140700800c000890404440c5014101c024002034603641c04805032480407001400051060040f00742615044550300b600100d140001441d00b0140e4000c01d0464103c40c1c80080b01c10b6983e424408003028054640e03420458080405ca0b4a6040004103e030740d008041c1045506100e0340e0005825032428a0301c0903506130403000341400c41c2d501c6003013040d86501640c150303401035003090010840c0b035000d02174407806501c50341709140c00c0040c003031000c6a142d045512078511407140c1a051b0302c0442d10a001400103410640045500254241802c1c41220785651100c0d005180042d010030544541 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 301555098 1250 301553848 301553869
    0x18140c03011503061509090c0303031109060304060b1f022a010503191413022107051203070c08010203010302031e12030603030903010e0d090801050c1207021f090b1302 74
    0x415000117085400c1d030440304250089030408043c841c54103d074401413105c0c501a0b00c0c200c0c1e04c83da03020f12075140b4003074411059006102c0401e802075030510210b800298590170580070428060000e03c100e42c810340304020b8804100726540f000d03800040c0f01c00c00084954841d95642500c21035030f00070200000380020420702c0300418040d40d0030407030f000004490440740c20006100b0b00e410381007412070034440710000d004410000101e1198038800324a1520040207140010259080c00150038072603e420284a44d00c450304201c4c13481400108404800140c1040407407000e800c03603900040c0c40c0e604520605240290401480a00c154850800c054120700081c14084103051500c03041e40f00e0321600c021900d03501507041140e07415420000e8010584000040c20303030081025541784d90361140e464890701e003285e0080c0d40001c025181040401d00b181c3c147c82407103403c420640704039051203042d000c04400c02c21030b4149406030992a541c0b08020702041c0e0385601d407c04000c012221255205074005045c9000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 301556348 1250 301555098 301555103
    0x3020a0e0603070b0a0f031d0a03050a020a053c0d030c09090c0e0a17030403020405040212190b0c0a1b080c15060913021c050118140c03011503 63
    0x6100c00080031500c007400b0a4008110040d62603840b50f40800b03002d0842460301042c9400286001a80140083c08803150040c0062603400303030032404040d4804450030780c81006120150302c1440c481c074002480030850304003075800c0c10b4010781d40e07a29030b000756800c00340c1da11900c410143c20007651a00046030100781c024403801c480c10000780c46144690195030030502a80408006881c00d00001511b640044c072034081d4480448038041d40d9600c880c403c031042a40c0c02600307070b0240c3c030510040c001401c140c0c0c8541e800600082c2020101d03d41500501e240c0f10380c8480c0803141c082d803480c03a101040303001c0b0746141d002034840043c0e43c14090b00103402042408544610416414400302e04001c1c040d4000440751001d1030030f400e0320a0051890304000e1041c0040d64202d01900c60300c80090400084c41f0f204210341d42c0c7c0285049404601550860403640b0b01200c00d80fa15580c441c1c0d0091100d00703070711980448500c280c0c920343d5200200036026060220100300f6901903410440500c01d6142c001c081001602c0c1d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 301557598 1250 301556348 301556369
    0x80105130201020d0e130c02030a11010608030f0d091202030d0e01020328060305012408060f060108040503090619080f04080f0706020c030a05040317071a06011205040b07021603020a 80
    0x101e003240050020350311b0850008590340781007a943c00c5958003200030035100c2c00e079454022040080c11000b030300700c030410f00c122001c50704140a000e015201d0b4400802c80d40c03400c04004600824252103804d15003a0412901016900c0001c40103000582401032289001c1c0d4500218114940900038054610081803442c80c1d0b4217408200c8164100a58400e0000c0d5411000800200344a40d038011450890010115006024074a0014031200f00040062055509000c05041a1140c000640320340c1da0250040313811740001c1c0109201038540c0300140c1000e40d0000f51302402e020203541c02400740030300913041c0b4030310645110800c000310b544542121005c00350007001a54a01050808000038013030031008035010b010004010801d1580070740500190780c000e21041d1700b0700070a405d82400d90b01c00d80000811a582c4480c0b22500303000f02030300da194050f4042c101801104c0b4565100780c03c49408a030102c03081600c170030500007010ba0400c0b047d4440d25202010068081c116000105036403454801c01070f2a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 301558848 1250 301557598 301557617
    0xa090b0106050d0f06060305071b1203020715050f22030801051216030c0303020d020d0207140a03150e0c03010b0d02040902030f070803040e0708130314090d0804080105130201020d 79
    0x83c040e48a203045040b00d210401229480d00401405050107440c030742c00040400c0310810200e1681042d0f948026031008801903441015001a400f0350454842543c000e060f444030103428116500035103110b18002e4100e52050718107104500d140c14103070f5065812081080c031403100000d402c2400c42d410f6601c2211078083c00300b201c0c09503924081801101288130b244401000081018004100090300d200740c00b581e0000c400003004a13034503804000004010390241c10b04001c103130035042124291550152044021a480ba260b220981a84000c3c50310141e035a00021840e41400f80030201034041c0c02c500230300414034400300103010042c0610010f845141d4541e4140b0440d0360800c81c80b10003540000c152603800769100380641d226003040c403d5240788880600040c040324424020140f0512003200010f106080079102225102419460703034808040c20042d42da40c65030342e0506411294450a1600c5d0340e1800c0441c15400d541d070281c280040c02002e1001040182e8000c0381c100c3c9401d04070b14081040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 301560098 1250 301558848 301558867
    0x3110906130906050603011127010c0b070c060b1203041a071406101d040f11040f0204050a0f05010e0d0825060b030c0306010b0c10020406020606090a090b010605 71
    0x10303005000c08941900d2804182c80b0070000076400142c41041c1c120000c2002105042004e4000e1003994400301d044504400008205e916800d0011102c03481850510004211030743c889004140580c0d0060204101c01440420001d25001e40c0100d40b00a55010390720440b195038542d034902881c0150a00c5e1140c02d0746d213912042008003982c46081d0040c2c1d03040e03e070031540500740791107820640f01d03c6240b5040310710102e42940d07050118280d0400000480740c1c15a02e80d110050161540b244c1203807010451114a01c196556015800f11508101c1005a4491808042146020040c0d0100066072842c0c20200410703030700825098441c0c8005d4603024141849458112101d119841920042c40b4280000302c04113003444a03101c0b1140d00c5418204a44100b1008069891141505295055000d4001802142d0b101d6024088041c82c480454a1120302000401700fa40c000c1c0c1c01c0200140d101c0010850545001c80149400c0b00700810f0401c4022001c7e10760304440ca8050040205001000170003010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 301561348 1250 301560098 301560109
    0x7111006051f090b280503010e090705060a050c0a051f0608070506030c0a09150816081b0d09050f10050115020307080a0905090901050403031a0d02040c051c0606081003110906 77
    0x285c006212030a400c1005000c90050300c190800e00034250016201d1000841c500c20010f032a8061798030003400d0301d0521100250455035540141c3d42840140038004a0b807000aa0400c1b04041005030315031503c01103d46a85014200c0349550700c400d40c2036011000c10003841d01e50500712a00000da1003003041d40c0d41e1404105540c404065800100e104418016800d0201d0380b1000301c0f0f00807240085100144099180f040380c1d01355040e60001110030042c418680d900d0180c40040101e0741607a000410407107103507201c40381000c4140d501029641c128155060300003202e8408c05001d0304500e4000031202585820095807030080040c000c200e440000743c0407103031600902c0c54200501000f4900c904034540107210601818040c3d50490100b4140f903d03004210001d000701282031140a0301e0048035004079006c10014012100200040c450208404010360581c000c0000600800000c081071040c50034100400010008004600074103040d1800e0001034821810310b075103090212100c1c4460b0311031400140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 301562598 1250 301561348 301561387
    0x90318060a180b090301060e0609060d0203070807030501091101090807150e1005070201030b100c0609210203070525062706030902010806040b0a050907111006051f090b 74
    0x201e45a045410000d05030910500400130240240e0007801141d03070f0780307101d001c01c004c0035a049030307218103080000350141c1040c0084a001d18001811500010752f81c1150500780701c402c0c1c10585150b5100c0c6080da00303021034a00b0810003001c1c203281055035a40381841c3e0546400d254010b40400030b4406d4403071540e00c0d20403410540c8009000f000c090000480304d10251403680b060808078040790174001068070710301c0d15100380400720300680c80b10300820801d44d03140c4d8001c001d0004101d80040c1103050341d07c12080c11082049056807550004c55450050b82402407500840280c050036613250301885000f52846002550704444481c103044039038040c2e2600c5440c00035451145030090541d1050300284440c0c0c0754000c001c1c2c00d4001c0c1c032110f4845d211801400183c4401d2a52130b84c00c004080004c114604094011540c010051724101402a580300780b1181030950010215501c65181e042c24040d034a880d5034075140768000c1030000302c1c03121007051000c1c1c41c100d5144a0020350490104002e92965060f66408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 301563848 1250 301562598 301562627
    0x3080703020a0b07080906160906030c27030219080309040b28060e0123030405031c0f0c0804200d0204020706020309250504270614090318060a 63
    0x2000f0520300b146009020000031101101300c0d00c41c80010030b0100ca040868100703501c40540c2e40e40604c030704041d030903805442d10820b09000c001411b11441c1c608100014401c01c0c0c50781c2c043d41c041c3d503603296004209681080800e07068020100820030070103a00d0020031503440c91070503640072415004440000d81d650101103000c2d2089030000041e01e4404454140b080d068417159120070821184901c011609500004448200083e0510103901e041000c2c03009540d2091281c0b003200e02d000c0b0350740c400c40c05c3d0500c841641c4280b42c0e1100000000040140038060340700c20180340c002068901501d613100100c0640203002070007100d03c02038815984884008100441d0041c0007550358851a181540081d84119000d00e0380f4045e01c080c04c0701034120905054400000d42080d140c0042c10041000001d01c1c0203030070f081c00000081c00a01d5008542100140c40d40e01030400084c01074058640301401ea0001400c40c0c0381074004000e031100c440c1c000c40050380030000c2994120384a00da04d070020b81d40c03006951440d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 301565098 1250 301563848 301563863
    0x801080712060f0f0e1b090a020304080415020c0a0617150406081203060f060903251203020c011205010503070e040f0605010e090c06040e0f040f0c0803071a01060903080703020a 78
    0x103049040e40541c0040c010200318408503800485865070440c0261b110082d101d500503104c502041c3c0039140c039006513421074080c4544918041c2d8405025a100ea0b00e1004000503801030038070200c0030b01e05540102e0040c406400d2405084a42840000d00003000130714242070214510600092620340d6400712000c0c09400080707606c3d09550700e04084c09078104585082c890489100041c055041c940c0603949582c00160040980c8da80c0170042c0f85403070b008012041038403c02c040c1c0000704030b5031100ee03407928580690017400510b200d52000504c8a40c0c4501c403040b0301c0e03041c1001013000340c400240f80000c5868481352000203850f07502e81b8011807200140c02400c10f81c203000020035600d52144456015892807411103c951640c0e1051280d203028610074001c1018440000a0b9406030302202c1c6940548142c00c0e0075071140c2240d860511450384c9403c000659400822400208513102c00740029407105100f00018a61411100a001001500000f4080c40c404505442058001c01000d5080c40e4050407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 301566348 1250 301565098 301565111
    0x360b0a09020c010e07050114030a0905070e150a0b0f0a18140307081507030b061b0c0114090904060b0d08180f010314010605031b04240801080712060f 66
    0x50019400600c2c5a800c25442c01d046196240800035001080b0355040e1100e8180200415100d81c0e540c00052075401010b40303402c00c88000560a0005101038001992200c0d61410541b15264100d5110340f0a030340500864002808907000103003d89500355040c9000c55964140804222100785d55802c01404000c1c8007270340401c80c2d0345805400c2000480030341c112030815a80e1500c4a964080d144400c580c00d49140d00401c9025202344c00c010600b100103083c852034000540c903d48440700047c0740c483c00940009010207001c0d82d0129010100c40040507541d420214010001414a0005400105400e64682e6010400d8a8103006000d055403c80803141c0c550124004484401c030440101c0c3d489240f0041500c00250f0291003070780c2a03c1c1e00300a0440306030303080c41c0c0241e81e158000780580c0d00d03840c0c4810800740364044400040002d0400400c400000c2307403901603800c80c84250003c1ea038007400341400c018813000b00001001c01c21079003801c09002c41411542052801030104540590700503083c60f4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 301567598 1250 301566348 301566359
    0xc12020315011103130b0f1b010e010506010e090a050601020c1809010f14042402040807050a0b03070210110f12060a090c17060a0906120b01360b0a 65
    0x30290980301420780b02d6222071100ba8000e00d441c3d104500745c01c1c07462860403405211a108401c080c140f41890304454510300071041740b100280c20034400c194101603440c2c00690007116404c0c0211034202000f801e1130390700d41415000150720100002d1014149540d00d00006c4c0a9038400c00c5800311030b1001610070100703002c4410303074803d201c80c0444440c2000c0d03080000110500d2a80e01c03801003000440540c000c0c1302c0c0c0351646c80c0541c440c144618041842e403038000d816126841480100010080200244080e0385010280b00d001c4030703107910099000030b0500c10451901d402041c03401030700c0b05203000060f1180d07500142d030311140107186030513108003c04104107282554104e0a540501003c580c1c4800d000e58407580c001c01d41d0007100013080050003465a10154400d0055581c1d00020020701103c00740d51140d84440442e407081e400841612103418004081c4130074840c0050240c5110741802c2c01401c1a4004488903440c10b100c2d2800407010f000500700270407039a81c06503554410040c03040600b00e50381d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 301568848 1250 301567598 301567621
    0x1d0d0302210f011706041a07141605070b0304110907140301170f070305071512110a0f020a0218060612090705030f0622050a050105090d080123040c120203 68
    0x9029402000c4e0021224140c01c03440000d0b050700c10350b4009880d600e10582000e0044840c1c801a01c1c400620070022018080c0420120140010840120710410b4000340760400c18540b04250344070640c0309204000f80004103c08092000601308203440b8025140c45021084800a001104034240040040300201c0c103a0503180e0700500c01040f400845102e40604a07a407501d4828620000703045030f120800c10011075060200c1c0c040c0109150a01c092103c0000c1900400c1e2b40e40084824454140042d05409507600200c0032007048101e84010205c1500340e0b03020a000c401040129144078118400081e9030383d4800302112513024032070001c3e5809080c400c440c0c0795580e0007401124440e02484d0107000500700001038043c4034522516a0440c01248440c100d00001c412003429225806045228404a5024050035000d141104014401503070340c00001052500d040e00500a5069561041c035161141c0301100784000c80100c50009148098102c103641a50421800d02c08841c0040f00300499040352 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 301570098 1250 301568848 301568851
    0x515040b060a05010f09060e04151514070c18021b1501051005040e0402041104081b0a080a020118080a03020f010e0c06030703020f1e0903011d0d0302210f 68
    0x40d02c92025198035000107480710207400c0d1401000680c1084104a1140300302d01007042030001600c00140c41c1e0740003e450078064556000310b028030403d0503a00501c00d0b070001d80c111a42e004180c5640c20030350259180b24101b0510710501f09190703448080000103501c1a81141e5510030701900f6031011050700c5104503261030140303006284105043d0300008480c101000044481f20196807103515003400c01002c68448440138105a8000380c0e02e01d403402c1011901c8000388060306a98004120905603501c0007607003602404c0d481406118078003002c1004130b1000808030b030329683c2400d00440c1424181c14410762880c2550141040e40f040a010790181500818400100f8180c00001d105a900712030f5425540c104005403550440d4042000070b954508ca13901502d41c41200000e003601d04a010710b019503c24481644505034102c00056840381450300348030312030104d40568441d00300c68401103206c3c0d07100c005010351007060540000314030a240750084403102d81c2da0301301e2031101040d00f8055003c42d1012070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 301571348 1250 301570098 301570111
    0x604030b07110d0c03232704063005010507030c02010e06060108060d05030c1002032406041206060e0103140618030a0309051615020c010e09130515040b 67
    0x400d0480c038041100c0101c1e0012501c60310352641340d4103503195501158054007207000a0000024104821007050200000742944020381c41035200f10b200e004070340340d6148104400e0318880e034a0000200000c5020003240e00140d000a01014008040c40c0042c02100d0344004004019510380020080501e400d58456605c50031158020060800c0c5142c005542e141d00b80c4000c0c0c085845040000c046103040c1c2c02404d5400c0c80317102524141003c07844400d01e4002d5030345020084d40c0d00403040102d6285681d007803000c0315131a284080425048100807800e1486140182601103100c40c183c0c00178001184c010030b0040100c50040c194941e901e044c0801d20f80e4042510750040d00920700840c110301803500c198440b0601c20b00246107404c0100350241c1c003c00d4400c0d0122658051503107181c0c0d80446104001e4004c003203a080b0100500790b6140c0007030402c805520584c0c107006c00e00900580c1d6448540065074001d080c90520300344800c80d0305045203070100103030000c0c42c08801c5000b008104000048081e01680 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 301572598 1250 301571348 301571357
    0xd020607080c0910030e160503100203090a050a03090302010806010c030905061303020909060f060d03090504050402011b050d030e070b0f09180c0909071115060a1d10090b130c0207050604030b07 85
    0x8030220060600301f0729101c2d1581c10ba0002007174100d40c3d0065401950440c0402003125118105540c0d6036013041070039030003a8049a002a410415941c1040c01240e0242d03003440c0451592005039005440241d50340a168080c50000c210131078503803000d03411400610b400400c100610720749040c0071541c81c10301300d565081c55499a8040381032070510080b807500081d8540c452640301800d00045c8401040014401c1c1d042041d00d40c41c0c1e0303030761501d05400c480c82c29024030050200c0100c001c5001d400d6400c3c020401040354031103c002c00810724441d0540303182000020256541c0c403007103800598606e5254a5000380d40c640c40c1c1c01c0c0200c6060b48002091608400d80e01c1c04400e58500307100b51120408140240c070b4640001000c5a00c00b4140c0101070303408030009149640285d2210450f010401c6200b81001c0185643d4003030100114820084400800c10004140108114600032075503000c460445018103039242c101c8101d5160080c44148051304002d0b0850784c580b42d44c0c0c1041002a401901c00e440800c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 301573848 1250 301572598 301572613
    0x20f030c0606240a03180c0b09100503010f0e04050f010e03030103060b0904020a03020405090f030a03020a09050301051509180102130611070b1b0304090c050301080607020d020607080c0910030e 85
    0x43c0300b841c0c548410384480c5401d2801d200042c0740640107841400202a01498444000400a60600090b002070070000c0f240c1502c42c007070302c0240400ca603100900356007446030503c0100905000e17540c111059404403100a8000e46840ca000382ca060104020010035500304650b074418008000b002e5030480340101814000e00e41c14000b8003e200340c00341d03000b0750802104e480900260905410036500203004008941d010b4000c00803035829500b0490249001940004054400a90060406001d480118020442d50074800007944041d130a10300c260f8020b20000340015035001441d00d0442201400d04029582c90302d107041006030301c00d018094240403a81c000103004240f1030019100c000d03500480c0c3d07110b01d8524103006004a6014410320108141700411012a0a103100d001d5271803482100c2e1502034503541020701d26414280300070044421981300004480d0f00c02e40c001041904080d040c1071010043d100c40d00540c92a1041c4920550400c9416015007610350b49580000d20098002065a03442d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 301575098 1250 301573848 301573879
    0x813060e031e1c020a0204050408031807051c032304030c0603050f06040b040902032506050a02100f06080303091005100503030904020307020102040f081f0c0c0f0201020f030c0606 79
    0x20301c40c0c440b58407009603c1405400c41030303e107040d900c0d10b480c081ca004882c0024202d81c00142501e034110783c203c4800d5008000d20035580148884820031a0300000036060f40f500f0700010410004010034070424000070300f0700d5034083c54055204543c2c0c075040405c1141c0c00140a5800c0e000a41c05803104850071805200000384042c0301e4815140140002c07880f400950f2109010480584800214580c1c41503449031000010b90701006112131075000303c0d682c3d9000c01c030004540b4000c0c8007258400c2c41842130410102c43c0c0707141e01184010920080400000303001d48044440c000414486c0c2010b40e0341d00c000014401c1100001841d000d81c040c41c00e00901095031035001c0c8160120321071145642503801070001601070716154014544c46960340c03000501f0282e550341d01900c11103499120503034a030081103401c14070b80e1300690051022408203c061041d5903d01c00c008000d07031003049018100c000040311020031603100b409107444200302482200c2c1c41d000c00e0741501e070700c5400c00c4d25954031a004075410482c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 301576348 1250 301575098 301575133
    0x5100306050f0d1a19063201020a0311010603060504050307050c01030b03100e15070c060605010806090105060717030907061106060904140a05150a0b0109140d0813060e03 75
    0x80a5134040550b420700c1d198206980e44103407002d415135506442c1101840a01d020034400c44004082ca020f4406c13021070380a4940920b034001c5802c40c2500704490383d0150240c0d0300002c0079685503a240c5021249034090800007401015aa000140f41c10705010034042400300020107011100e02039000e0ba0643c4940c20010b5007210020f29500390540c10007010380206483c2c0354419614214060f0a803061003c80c054080303000c00c030031507559000c40c5031138991505201d0079118410281c41c0030b09102c01d1a05000c2c0000e0600e481c144920303407142c540040d8407420001c0c8000401920b00c85051465124104080e08030303201c1c0d5050141c1d50004103d804401c116034000038449003c4d40020b044880d0382e4840351101c001c0410418074a0781144a038400d02000101d04100b5800603980400c003015450400a525006071090100c0160400c80081c41c140144440c0c0d00621010b908100c03104000300c40a840c1541d283d00414024a800c03e03034551002416a400840c0817101c84d100300d056500c0880240c481c0340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 301577598 1250 301576348 301576369
    0x403091706060907030902010c0c030b041401020306030604080d0207020a061d0607020d020111120301060c03110615010806030a060e0a02030105010b18010c02010909020a0201140603030c100b060405100306050f 92
    0x10f9215400e1808204041d000760b02001e400e80c0189007100d000c910b1503c0e058114007440d4000c8403404586070402090100c061180d2054040c400020f602e1400c0041c0040d6440c0f00243c409424580300041c2850340504a9048484040c1d000d800c902503181d503800302130113054422401211a075044040010309140002c215410958024085c944c103144640045900c0c48800360006005d00c107000d0348114040c01d84010b0b600034a1182d4450340c0450480c0740041100c80d03942300c250700035031245042c00108400d2414482210303c007860404944d696240000b0b18000b03043c3d10140c6000d00d801034a00e1070100c0812440340d05d5000780e0081c80166a600d80d10341c5241700c0d8038800c844402490035405c0880d8411034170008030034014500240c02546030050f110880c2d01070580c002c0983e65845800c4032400140d64015480303031013103010310b0814100c0381e0115201c0369400300c003540b802c2d0342e41da101c0150b540d2071003170314050710f0042d050354a1110505800f4006011600800384614090100c0d2a00d916000d4141d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 301578848 1250 301577598 301577611
    0x3507060203040b0714100203070e0409031b03050d06080a060507020a03080c0705010f140402190b0a051317060a200a0e01020c060c16081204050118030b0403091706 72
    0x207500d458507100412045403c002d0f030407964000030002200c07018508000320b0450b40904880160341c0e09007007a001c0c010214420280c2d0040741008070440202c1e0f005499403007007400304107011000c51402d00d0101c41c141308500711100713454901000451904000598a0607091040718100440e4481007001d9907615445000280003600140006607403800c05001b0f44000c62080c4004074560481e29004030035101219042000c90780d9813020801940340c0005582c80e0469544040000e0324100910a081840398100070f40c14008005152040400f103903070a00c0041c800c1d082c0b0480c200b449816080c1d00da58080e19410100ea06110315910215680045031410701421142145000c00105090380c0b0000d09003600e5042d8061042c8155840e201e81d07000340a10304800c8043d2004850005016032152000c1d04404c0440c0c0c0040d00401480191000f200c1c02e03210242030070f8400c40000b542c1030104071403640005007030700c00c0340082c0000c05801018040c1a039440c0c101041039030f910b80600c15035030303801160788 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 301580098 1250 301578848 301578853
    0xf030a03051e0601110307020d0803041a22020312030f07080a151701021204082a0601050904020a030f0602030a05011205100f06050910150c210935070602 68
    0x20801c40e60081c5ca420f000301c400282660704200300350700054410500c0660542d04002e000041004101c068149540c56400040c66080c40d07040034098401c0d100345854218240e09080050103055550030407565a60103001480071f9941c1c9051140884030300030a554407004107040070003250700d15146008588901c01d001c01044803491030516640142550044035000303555007001141c40f0700c1c1d02d44034800c1c8101c3c000c6080d0359a42211420303052490001480e0140c102910320400d034407402c0080740c0e20341101e502700e4aa900e0340d10703903000240388103110364001440300c289442e01108101d004d40280d40724040000c8204110781e610328035614080080500100248c20042c0d00c4910542d20b40c1c4243c0007c035120700c2c00102d083d1120089030802c8400e0b03d0070045001000c1e000c01c00c18030080c181c1c9105e40700e039142c48004026a0341c0c0e18841d02c030010354410690580b0003401da00d60f6100d40000802031842880500d4034800ca070701130b110490400c00c1400ea00d000d81d1400d81c0d50300c40d00029100221682e81c0d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 301581348 1250 301580098 301580101
    0x507090305030a082e080727020901090509070c031e08161e052d1207031b03050f010501020303010f0504050628060e0a0b030f0403030e0f030a03051e 66
    0x60031508014005d11804130400212035200c40540b0b00c1d001ca85441c6044801c000001d81800c010510300003050740440c0e468010082e0380d812880c2c1904684034040313240c0c50003680710540720740142c40c9204a500101d4001850743c04002c20654003550441405000340c4444003244000c02c52000555441c4c8008000f003140d03600410880d040302c00075105004102d151140c62602078454892140b5444c507007440000d480401c005840c500500e585070441151503000d1550350340358118000e00c40c0180e691044950582c000064400e41c0130b60044c49101c8512000b58101000700303940540106826240546150841c2c40041031550000007100d05850000502c5080c2e28600003c02c405024002d0140b07030001c0d0440b017980804510155543c2ca0303603c1e03522200c80014201100242405280748000b846800142010040d00e007643c03040304d40000701d82030324501996403030409030b000d80304004044030355100e1482c03000501800840641520801036a040c03002ea12504168250340d20180c44140c8005000700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 301582598 1250 301581348 301581367
    0x3040206070b040309030203060c070501110307140d02130b072303190c0203010c021c0c0201050702062508041404093504180e060405060105010813050f0a06050709030503 75
    0x14816030303c01c1c0300341360201001c0e0300ca07804030b0f05000c0203a408c8200100082004004c00000307000314046040705c031014074298070381564000c10200c84c8580d000084000000c034814032910703603012900005044003100528696a0704a11840e0344014010740e00038990384441d1035002c400a0680c040102107074025810840005150304400381003459000611150701c0a00d00180c07420b005c1d4007220380194020348511b1117a540012540a020600001000404480780300140c1c0c106c0140c0b4005501900c00c070741c607401400040d2030300c82000101c451004035491140020454150003c005a61011400f26801903401061009070340c49940b0040000d251780280c0d55000100d08020034811401610714003414201d000c0d42002944150031448286441c014100c03034503c65030159482d80207200f0000e1540e03280c04e07158a61280010b004507030401c2802e0001c504020340103d00321007801d03040710a507003900890808c00e039a11010503004235981400d0500080680740900301d440203d82c0c100c40614640206803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 301583848 1250 301582598 301582613
    0x111e030f0f070e1207050109051012050720060912070f08090d0227070512072001110310080a0305070602030603030d090f02040f06060c060906020904090305130b0304020607 76
    0xc02c880304002c0342985504003a59086074a020300341005016001040c284400100b60034400e800c01800390650030a68040d0310340c050300740394a500401c2c1c40050070742c54596049402d41d80c04e040705a050004062110700820011503840e0207031140d00c0481c0d40418515190f50302d14040d4403005094004400380c03003004601103000801d0160350042c9080c411800c103a00184c6440c0011903454003c400441d084070340c071403015602c19040040c0341042424030065802c41c001d4044000c0c920000c0040325042000c103840c008007465030013200c1e04002d008151018060024a8004562017044840680780000c2c615802042006001e5015501c29140401940700c01019500140420303070948002c00141090862900c1424492403048401110080c4540100401d8503e0201091301081c81d0410400c00160800b07140145076034000e8010400b01c0d04d07820098001d0054855203500642440100800c16038484000c00d9145001007090250580f0f0b0882e10125010858000303410107000c00c030500214522 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 301585098 1250 301583848 301583851
    0xf05010e0a03020603090604050606090c091207090609142203050307170a0902030c191707080106060f0f080108030a05030a0b040603050313080c210f01111e030f0f 72
    0x90030a01d405662580070030100c3d401210b0401a80d00f000046c001040414407000d500075100302d40d02c9425003403082c0300085500c911081320b845400c400d020300c0d030ba0140903c002c0008117501c0d442007146554130942c2070b0280a020f205900e840c000d0b000025188092090b40c2100c016243e00d40d0022880700c0da8040e229540050302c0501484a4040b81203543d402c0030000c9881103002c034402041d014030910500d0314240b402500d103482003440b0f5035444002e11030440080700310f9003d400c0c0c42680b000c144442504003034164104040b65401c02c40c0108003580c1004101c5074400c40c560302d25202ca50208011280300900780690f50454008000d58880f83c0c0c420000703036810001c01840012011000390005080794426881190240c0010564050b020441c904050080917210b001d003840503600700005038a1042450001c458071300e4440c5504032000d0800100f048401c55a000b000020280c08210301c854200c828030b0004841036030304c0214000c0c03800007079038001c0c2035041115003592900719445001800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 301586348 1250 301585098 301585127
    0x70f081e0703140705040507031406011b0c03050f120711131e05012c1306021303080403051e030306010c080f040b04090b0a0506070807050715020f06010503070f0501 73
    0x2401d40c020002ca111801d40020505042d40100b07111840d080a20060703070002007064050501c1c00e46d20202501e1200b01e03445d809082440c181200029828a00341000004034000d13012403861480401000000101c88107000307240f608417560381d1075a540128143c07040d002c00500f40c5252000205150074003000e10702034010000808118004a40d142c9070000143c420308450240e143c4004020f882d40f041c3c0074200700d40c9120b0004149024610540410740800790980c101022400340610a00640c2c3e41500d84e04c00180310601c0080da070723031306041149401c680010303a83c5004080329027003444541e0790000600341e035560156040d680c038040191582c240c00031054a08035010040b141d40c000c40907000704080d1806581e01c0f5211414020441d08880091034003a00424402d0b000f44925542c1505680860303a204100e00d9503410540390040c00c280c1d85521001820f40a80d04000800740c01049141d0112181030868110b81ea90300c04060350b4090502c01c00480e080c111380c061042d94440c0001504089 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 301587598 1250 301586348 301586353
    0x30a1103062407060203040305030a1a06091e0409200d0308010605130e011206110a020604140705060a05031f0312140c100e0607020a081c0f0504050c03070f081e 71
    0x65107500c601c816070b4001c403001c86c00032710000704001c942c4040e8070400c000d4080c00b6032065030100d52100429401d2044a105d988100e00202703100c100813920400703038003090101030010702200c400c51400c007000003001603a41a8038030407a0380c40f080ca800c1000c1040f00240d01613a42d40c5a503440c0c140140d138a5840600c043c0040015000042201360350145224002c1144015040007038000341044400c03250b200c101d02507400403c100540c11664005001500a074000c80007441d400d244145130f40c131f040003d5000607002030022805109054004003d14031071441d49052204018198200c00c00442c0640001000c5030940302613022914032400300e140c5440b10721b00310a807030714060301481c61034a200400a0f000058840e040400400004e005c0da0350400f0190000303003000b0240c1e80d5107001e41c3c0603082100004c00410303142810000c58030b030402540110040400c010314100f90410a8907014601c11540c020312030610006403151140c011501141e042c08040d21000180314180c0d44480385084a81c0c5061 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 301588848 1250 301587598 301587607
    0x1062d050910110f03070b0f060607050607050d060b07050703060f021308071a040e070309031b03110105070c03021c020a0203072403050c07030c020301110d02030a11030624 76
    0x40d212070100016000031500c03001c02c18400c2903c05460108032403c0c44819030414003d980c0002d0044d090701e500802d0b8080301c16001d5441e2404203446004050000d8024811003040c0202260010020000b03040030042c04d118094582c06801c416205068000740a58450f980400100b105944030341010410746030b01600e4101e001c4080e4583d00342603004403260381c01110b42000034010f9503400240c1046020b20882c02d1038178248459102c994002e04800034591108410000c0610511801c4011250303620b40c413070081d800b400c00a00032035015003500425031070800400c42050040e0803444d103841d416401400b0041c3e48100c03280000840450400941c807841940b03100581d402d100d4500504104218000300c5e192020f0f60a8030b0034417404070401818503000c103010091030120212100030780c15050048103440c1e0341c07011030700400e0803450522001c440031a06900710b0b00190000c6000350b1170a0014001c800042843c401288070a507120b0703600161010052a01480c101ca500070748006a03620306051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 301590098 1250 301588848 301588867
    0x1050a1220030906070306030b040807061b020c0102070603060807120c030506090a050c010315030f1a1302040e03040e0112080405090f041a240a081203060901062d05 73
    0x1e1210071140065410100c100011000200a03d9034001110302d02400071510315150180d070307040d02910142040f030380059080c081c000c00713810690b03501062407854074040740386802c001d494420011881e4018020f0000000300b89119004200c2903580103400303400050310f480c071301329080141080c045918041e81c6400001266061156a116030744a001408a555040c5002c1d0705004000344014141840c00a0600c01004c8250140b0180d070707401030540301002101e00384240d0b0100d030310142d100c00d1644c42c1d08000200c1805942400c12038800d481c24000700d010710f840c00d502ca02032801800818500d03003004200070865407070540912802002c0103842c064403803001c50942d80f001c075202080036170458103010030424034810400702410141078030020b03810445400010314480851a04001013101c0f039000c0c013a1380c0e00d6403006c0101519000c071115129000440f1019810031111071707108203001070001442e1805403080e890001d031103409052070030000c0e040c141c40c0920800a800100030b0180f05076800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 301591348 1250 301590098 301590131
    0x1d0703061a0c0c1302040e010e1306050903090d111813080a11030406031a030109030c02060a020c09090d0201141306050a18060b040606030c0206010e2802090a090b01050a12 76
    0x442c04c10704002582d180c1c10101c21108408040c0d00a2042d80003050800c10740301103450880030000e40c0900d0101e000d4941c00c8040d071560045845841c0e200f5a0010b000080082c0640d50808901c01612080351208140307581d200c1c40ca10403107158890b4a440c10f15640040e0300380c00288109101420610210003820941900d182c1007504003601281d610a02c920320940e0a140003004d080c0e04900030300280f04180d40040c1414441c0780020701400d07020a1030a0340e54003d2000b40401e26005d01601301c2450034800b4036a94041010006003d54030703180c1d407007404140f000100340c440c1321002e9040074400e940b9940d000040c074006041442e040d80d01c2081017111580d040d4101d00381c1d801040f0204040300308a00704000c4070703441e45c4600141460b160340d11130810b80200300780307045441403011f41c911903949048400c030b507011010760345802110342d10180140c0b0200f94003070b080040c81502c16400d0f03152541042c4003200c0c001c1c001d15001c81d40a100c000c00086c400e0007880d0003000c95010104440400350640304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 301592598 1250 301591348 301591369
    0x2061e0d05011e15030b0301020c0d0201140f0601050313063210120602031305251505190e120c01080c07020a150201020705071d0703061a0c0c 63
    0x1000caa160001004030608040e1091100c0382902190080a85084491403540e0502d80c195000d060f21103481c00c01581e02941524980c4001200391841c1006016009008215419007214072800c0080410b240214a160003407141e103060711703070030f00c1e50b1030f101c01c050f8030314810300c02c112280ca071110794880090403591907191002110b8818100e0348509410003114082c4000c04600403192028010030221484561010a0a4110100582e01e40310380504030556214200d002e8580e00c101e4201c0030a00003540e101d9140c40d0104500e00362500e1f01e03a040765025000480114000603001e02840100b40744c81e1005250191a0381404000c00e52010040b40702060340380440003c580104440243c03a58002d504240d00c41c0c0008109464080c141d0300141c1c401c6800c1c0100c2c1060710345604080c40e510300035412200d0542d0864100e41c80c042d652482e4000803905010704da40000f9085001c580d465009000b03030401e5551105c074940c03400c0d2500c02c102803550031100040e245482207590b024990389510303c4a5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 301593848 1250 301592598 301592617
    0x2042f0d09050d09050916080606090f030102180913020117180d081b03060616030207030c32030601030204050c04030c0e070318050607120b1804031107060c02061e 72
    0xe02c1c52170300e40310402c5010003004096001d84010743d044262207680c0000c1181d4014000c487c80e82d150320701c0c040468083d178442c0380746540643c8005024600d0200e410241600fa941c1110b41403059900d8112141040700c01d440000d02080548121070b13001100440620b40c00480944502100e2400c83c1e01c03649010880881500800d0000d4184152413480062104481e03120700000c5282d400c6c2000401c4c04bc0c03103060394030061400403400c190100751080c40000004e503001480f01409a444078600d06a9070b402000380f90003801d00301e00282a0803e00380e1040d01040c00140503044030f030702e0760b0280b101078040103084a1508808000200014003402283c5010b09101c0301240c0761480c140002070101c1d10009981160022528000e0300098000039078a98000b10500c2c1c21030705c3c084005c5444000d00900805960310028022106003480c421001540c4164082e0350340c03040e10030035587d109813100030f1805a100050003510b400405400c1100c000e00f0b56a420014204d000402c02404010a401c0569903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 301595098 1250 301593848 301593857
    0x2060d021809060a030305070f32063301050d1104090b03060408030a0f06030f030302030a1103010b04050108090a210806031617100501090902042f0d09050d 69
    0x20038210b0074602211580001c0a403201d04405042d524003078080c0c0120710000300440030500b8460108104a900020403100c3ca190700795080090f8031031650020303030050fa0b100321442520000b41442e18000c03072110104400c03413541c00344448005140441010810400c9044c032408018040d008d048030704c0342a080e1409000c4c030baa00c640c1080c09110135070b0349084506119500c408144004600c041c400c894200540c200c0c0068481d880541c2040600110303400078150360f1261a0304014190981c0046115004c4254100550181a00e461500380000c1c0070328040f9100900c0700380130304e500421080f60091031050444c1d10005880d6141c5d0070b11604000360028106001148001058220018540062089020b44485200a01018500c0701c2c40c0c1f0418070555030300c0b507182080f070314144140e10005011500501ca2036840f281d040014110303e11080340a80c1c5481d2200340b9503c944800782c034000c042c1c1451141040c10088045c3d00640028010042c4241d89600c0d80001400030044003550a409440d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 301596348 1250 301595098 301595137
    0x6040f050f06030f1909050604060f0c02070303141c05090106060908030c10180b0708060a14030d050703140711041a0a17070b180f0303071e02060d02 66
    0x910030214030035001c1c94003500091040c00314003c84091240d0f401182c84600002e503245544011000d400e1959001d4400d002d03c000b13000034460717035410000c0f20401407c0148086d406078807049a41c2d01c001d103c041e0025001400b0f00703030b4041c1100010880989080903151150040540f0541156021703940c4000580d507419040090340d8100b100b110003000c0c00c4000d1030412200d0100c0340c0d100c17264a990310440c2c42e601c218001720060320300060300880d50420002807041c60042c0b0003038020001039850303510680b51864002450110000d00a80b0000081c0181c009001c1542c3c050310039030442281101803082d44654400700702000000f07007043c1c03030154070848091080003007444100c2e0550011814107081c412403640281c0c4880c601d00c422240c0400d2801e039084040003010782070030050b8000502c820b03c000b84901410041c82c52483d0642c2045801c2003090034500f04242c0c3c0c0784912039000f131040c507500010596034855045083e00c01c40c0054506482c141590350040c0807a806040e10792010560011f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 301597598 1250 301596348 301596359
    0x40f08010b0906010207030f060b010c050322080a03091a211b07050307120e040c020708150106080c0a0c02040204150305060306010f0b090a030b071e02030a0906030f060506040f 78
    0x21046410503c280003030486142540c44414002441d414040d0100e5158a81c4a0083e4400c9401e445c0c1a0b0b00801580c3d1110b002002d0029211382c041202c0180105403072006c502101c01142500d40302d907040e141c01c08010700c0c11400011543c85101558641c5800780220401040200070a0110001c00c0f10441050f10382100308d8181405503041c840700e50402481401c00003000041265040d54012078814060300788010115400c1401000880d081420f00b8880c50009400003000c0c01640d41d5103060f00e0301032290114a024501342413146d500004c108070046001181d65000810341401300b03103040c00c00011aa00843c0c140c0c2d106034840409121007880840300700340e041c4202500072500310007900c06545030207040050750b282401640c030f0004002907a02050707900d0322400401154050b08400351450719007805009000203801605520311445c4001070180c1c40402242c000c3c400907215200c000741403080441c000c20707240b01c840d40440d54880011a803552020f014100400703418440303400590405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 301598848 1250 301597598 301597609
    0xc0f030c030c1212111f0c0908010e03070f080c03040b040503010c170115030e010f021e070b160c0501060902031603110306010c0c090e03030411011b08030c040f08010b 74
    0x55005038030700c1e25400f600d2030010b4034403812160004800d01e040060b00380c0f141d600e80e007000740b4800c442c14442c29911040904141075004445e510205444d02c6400c2c0755105045800e0321041c3e900d5103441d800030000100020305648031750910502410880e0304040c0d101056034a141c1c03058000460440011030200030f5440c00f4019801e08001c40c1c44c02014640001c84c50851134103060007a00d255081340400b8446191180d8050200400c40000a00a1800141c401c0000b0f5200d642101140b1a0180070f14080325544002ca960b10740e80680c0c04042503450500f40140c40c00d60804003410000e81c0c820b58000318109005030000392002c00703030042c0c1d682400c044003011800e51748444420325081a20203c29403d02500b629031004081c280b4400d440405c0c9490701070f07082c0a401c51a5901e20301441000001000400f6502c1180702d030041000e885040e400541d00d03d5083c0c5840c6c40c602d10703504048400126560091900b124070181010706054403404081c808403c00d03005144180c6d036440c01b0904030300c1c0c80d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 301600098 1250 301598848 301598873
    0x50c01150f120c0b0a110a0c0302040b090903070605041a1609050a060e06340303140402090a0b060c0a0b0603070e1603021e070f02150f0a08040c0f030c03 68
    0x1051208402c180d007542d85142c00c05062250282c40480841d100c0f41c40307402203908503048801001900d032022603525180104d40000e020a0313000768a4a800d000d410300f0b04601d064000e0000b14000d500301019582d600024100041084a610501c8210945068034003800c15010b10300000501802c1e01c92202c00a0112189520952003001c0242007000f0302500025050010442907a1159031004462910604091505000d16040800074840c48822581c1581d08031164442d0303406000703001c0000c1034504000d0301514040d47c41601403000c52500083d5900602c80d120000d0700950600018020307490620100b00d400303031296643c0c00100012441c050081402902c1a2484444a800d11038800c2c200c00e10a00f0600003803680c0066406650940001c00c5011100081d640300d50302e6000e850401c0b0100c039290402c03401051401005503041c00c21780709860030710070508140d508201c200282201c002d6006070094403407002001c808166890f1901e0003501842c010098120000e24514003159039048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 301601348 1250 301600098 301600109
    0x1b0b060f010201020906160804030c0e090c0a180b0103150803120a0e2107120e130603240905030a030b030d021209060a030b090411040c090506040312050c01150f 71
    0x81080442d030603550341015031f040c0c6501d0344d0b1490b540d18202d02c1c000ea4a072185802c054148100e850300050320015203145503105148041c2540c41c140d41280c2480288902c5002d410a000c0b083d98552120080355408500a440705240c0454a0600745e200c200f61000705401040c005e0f000002c9040c10515040300d002e03000390380241e081114416081ca00f40e1a0090018096810b1000c1160304020404210070381c2c2650b074214005000c16000c450000e0104d026400d041ea0080b00f143d1003010410b110f920490040301cad00071101c0c15140142c6403050000000c04860020025510f07402080401c0040010345080c2c84240c4000504261680802d4907002c50150300a003154000103072154000403030340568895820a071100381d218200f4640079070242145699454010780420308100a0009086040c1d0001c2010b44c1c0400c4400914a000c4904030f016004c1c00781c02102c10401000014410089519402140d151040c1440001c03c0c80728251030710050981c4614188281c2805400a4800391600406 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 301602598 1250 301601348 301601351
    0x30c090f220629090121061a0a17060307030b0c03060109050d08090105070c050d030804030323150316031a060603060906011d10020106030506090303040c030f031b0b060f010201 78
    0x5800307080310050354502c880c540f011950100b64a946640a008292006206441060100c0d2141e4240b08000c003194450f9203003241012041441040e0751108654420300107903a80d034203080c8151240505608045c1842d03815104001d80007011810750045540207072181d00e009075980c14003100040a1b4809a0440d500c60700d00040d04000080308081100c800c80b00070300306651a6900d5040c1042d168540b5484180c0014480440030304240e48084014416031103500c041148002100d43c40c44041800a030942c4145c0030080443c0c1c160102030840d90715040000c003101c900c070313180e03c2d450341d4103122581c0110f070803003610001c2c8070803031811909a90f4441c606030341c1281145000000030b0380c0524094400c9060001c01c0c070111062801034404c01c0c00c0c4250243c0035861b03100318040c00a000b081c45210503140341c012403010400c0c0b03242c0402240c0c001c1c0c0d000010317180f80b0341c21510360f0240c0c01030410048082c041d544600c1084041c81c1b0b0210404070f4054054000149060000c0c80300200c04414a5030459 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 301603848 1250 301602598 301602629
    0x19021e01140a120e0d1b060612060203061e031228050403140c15072f0a0f080703120e1507030806010212160f081902070e0903030c090f2206 62
    0x55020255070b031b80d0b200c0c10103040c0d0265036a04111000b080c0d0ba030855402440200c1118040c080300d0340045001c0c1c4000c0e10102c0081840d614061404004080c1603135160700a442c8002510000201a0000c014650011661509944501c0c01c0e08801a9039910100b4000b00e8100b041c0058241c21650403010301c0c01418131180e0140003d07919006841811443e4040400c2c0f00040c48491910401d0480900c0000804400015440c0030850b42640d00c0d01e20030b07404a40d02041322402501c4403411100540001c2c000715081d0703511141687c0d1920300000402c10302c410b400c0b5071a80d449034440d100d00305032407d00381c0c0e460326410020075200c1c008000505551010100031300c0411421b0844000315288100080038103039900c2c1404255450031005019244040360722032141050300020a0000032680894040646d5000034407035800007140e0000761608140005804164a98010440c21390010070f0b00e209481d03c01c0c0001d400103403003c0007000360140000321110744040b0344075001c068494400b865181 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 301605098 1250 301603848 301603873
    0x601080717060c0f0c0d0503150f0310270b01060306060518060d090b0109050603150c090418022e0c020604030807020307170d0219021e01140a120e 65
    0x101c0702c025040d4000304100003000c41039040d000060780d8410f009041600d070001c0b814040141260000c0d22010a880c64884000e580c51810030850781040d1800780103044800121329505004213600b00c816944403840101c142d2a0f000c580e1202c001e40c3d8400d020b14812541840401411070f001500501c0500808108125284074040c0d0501c1904904440403542c40e91442e1464014010310200207100c0c01c40d460021541401c15009036100b1841602180e0b080c003810440c114060800b6900319409035030400c8110540e06140c0c00030b0000000704c00142180c200554003042c10040c44480c08503440022245007800c00d582084581001c883c01c0c9049a0322617100d4000544074825440000e05440000503054115101071124000500380382003080440424020f405450384071403c0d04a0040c021401c2c420301d1403000d03155803c5401e8002d000c81d100f034904d1044004c1d1030a400348040741440403c130b8610f2001c040340c10003401d190080d0f69a804801042086010545400d03071048030039034100600d518103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 301606348 1250 301605098 301605103
    0xd020915060c0109030f1d121e011e0b0114030a0b0901120204050702010c050901180f0f030309090204060905060702030f0105090705012604031b0c1202010e0a030213020711060c0601080717 83
    0x2600c04104d0b01c03107100088543c41c07540b03882781c0201c15100f40d00b4445059103ca42041d442541005510b00d0003282d00c00e40c02280c03004580850600c207010541035250104d04089480c007643c1d100040305000507048032420300140d52104264031241607100c40c10041030440c200341c05820380084550000303104029400d20080c1c150301030300c1416030410043c418006c1080000b20740c1000281703d20072140f0010764070740444039642c0c0e403e40002e4012a52007000012011003500c00c55017142d0300c540e2504101424003007000b1203032b070002c3d40a1761f01d40f00e11101a0200c0c0d1084c855540544003801c0240340d0145804005864101c0d000e0403d04207032940304040030929020183d1540c0320740d051403d9200d040c01c0c074040f05102c116045c4041d2440c8641800402d0340140d05150400040c000d0300c0e0401c6221000c0d04012001c0b40a000094020b40d102540c3e20313000486401510305039110380306292080c1010404503501d80c00920908501c1d5100f9001003044441c00e20003c006000010380d04001e03c0307880401640e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 301607598 1250 301606348 301606397
    0x51210030633080319022805070803090a030206162003010c031406040203070903080a1206090e0a060b0f0627090f1b0c010c020d08150d020915060c0109030f 69
    0x18031a8a02c2c2c0600b0522038800c1c420428042d00044041c1c0007c1c00c0d0340d0600303410345003804044415205443d008140740000205607100742c0c10041661040900319820301809420040c1d0044902808008803000500345005003804081e50310091010000b4035001c0509640614204105240c5001c00d18080703040d13216003556100e1410b03903000d65244c0b242d031011110300b51950320180000c070f400f00314030070859445201410754084540c0148100f030340f19a281c4003160a0f1b0008190994494182c04c1c0019150f5042400580700c0101101108000c0d607001c41c40a600940c2640c2b680b21a00c40404480403010a41c404000c0080da40840b071481d10b1500d01500346c4001c2c140d0745034410380c40c1e01d9503070241480c8101c0d011a02c10800900c186030f07031414003070b40c1d85507103405c0100410080c4c4005814202c16140107541210001d0200000d000c4070340900101140c05040703000d4001012010013030584500c8028a6441e54070f4000062014590900821017003205412a08001e0188940e800c060050308140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 301608848 1250 301607598 301607617
    0xe1006030305180f0a080d030b01080f04200406030c0504050c1c05060a0323060610050711120a0b04110114030406020901020f010c0c0c09020a0512100306330803 71
    0x6040c003442c03000c0010b0b1329035644d803402903001020010202d9120070114020341016450740b41070240710503060041d1903d01e0119549004502c2410002d404504200d01c0000380050a100b1002000b5400c0c01140684149800580b07204000d200200b1240c2400d115039507000c0030401e0850f06040e824080441101c10b02018424941d8584002c642e456440383c140d20020b5501201c10b01400359903e014150302c010340800c40340c89004000014205091031680c4162407800b82d5549840c0824607a100002a00b41e04a41d6400c40114001c0442e0003d0810a4450032405815041190300e00341c50600b01006610384c600d410403450306c0c29446108881402d582d0003d52014015889414400040b46003940100000300d10350b00303007800a01c4480d004880101d00710300031100c1240803501c42c0c1c2103030207900c41c904007040000c000b0000081c618207045a501d4102501d04500c6242d030741e0f40d845140c15502e1000c0c042c002c00030b08803464001d1454803090711407003414415883c00c1482c078006c00c2c1501d85c010292007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 301610098 1250 301608848 301608877
    0xe01170f0c03033f0402040e121911030f1c06050d060e1501090606020c0105070f030c03020a080a030b040513050a15061a09040c05040e070509220e1006030305 70
    0x10a19440811151900300c000340d180800c103c4061130300706000e03130ba100f910140e01840c0350544640410300080740c2c580000b454100e0440c50181c1c0b1003580402c0079242c3c0320050400801d10300c0000c000d80c080c8010540000300440d12a1115203003051650b40b00d10701e48070340498038178101c42001552a034542d25015243c00160029009030381440307040c02c1811030701c804810030441c1c00000c51042c2942d803264058601c0ca50032100a03088400054685104100b000b41903c1180c1c510000040e229a498a0b4542d1003841074640101c0316503103580301d9410050450020940380c5d284606507040c41c1c415158815584003038943c481e0000c2c1c45082e100c4000140280a504130020f012121131807503003000004202100e440702c1e1002941101e100c00d0340003042441e01c1541080440f144a610503401d03201a91500101d900141d21546000d845a5000d28242d94100300c1800c2e40c00c00040c600c010000703040c9000000444c00b03a010b000391a0038000100c600041c803618004042c001701c1d40c408191030018100082c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 301611348 1250 301610098 301610137
    0x21602040605010903110409150e16060e0f1201090503070303050f0f040b0a11040816050a0522020705010b090405060f0906071215050a080706110c010e04150e01170f0c0303 76
    0x306640000d20464206089d06d050500213018013400285081101070650400742505842c2ca8003280c10080480c051544400c803c040642645030098078200078031070440000800d220300b91b58580c115080404113401003943c0300100300380180160b02d0b4940c4800882c4044040d031516943d17040c0c410303001600c2c1d0910207545603c81e410f14190501144c1c080c0910310b0031580240a40c80d10090018828051780c0c1c020044c54900161301e061030b6200c1012511040014036000c020500c1d040000d42140c03105507560340d00c40100c42481d48804640300e000d0340c01000640003614209640030b42140c0c3c00b0308041d119038480820481016405020b941810b0300074640851a9200c0302e503000c4010720250000c42c0e02841d007a100007501400043c0e164100c440740e0311000e103541c00f0034552a80340c0581c00c0c02240810750311014004903282039402102001c26005403818241e8580c0000100b01400343c001550100000c0001a0741c80c80c2040a00c001120070030090034580240342c040f80e1a801404090325020b04001c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 301612598 1250 301611348 301611353
    0x9060807060818150c0408011808040e070302040b070f020315072304030c0f170a0201080a02091305011502010f0614060a12050c07150e0d120e01021602040605010903110409 76
    0xc60130400c1501c41c00243e05501304414003041c40c0d4030501c00c91481d90f280c02280000d20440e80036100b80c4603008242c0c0d90406140184280c40c52600501010805a0800c40402d405280202034003450f40105000311a8035110300c18545005022005044131814110410a07456448580320f04030110307140a0310784202d851601030303c160044e0b80004090894840780483ca40c115094003004455184190080d008130f0341c40b05a032940a00301c400790010700c20000158101c9001e4004185030314024180e05c810308200031000d8100c84080e0010900a90703103200001103558240a228800c0c911180d0801c03000c5c0c90140307041e000402c44843c5600070200442e8040780d00c1c1c0104c50760098815111401d004600c0c28041914080d4405141120400448280c03118004d0041c8030b5200710f0800040103142041c5117403801c1c1c2d00c0314186c00854021036290914907000a1080c00078104410a145a82c80c1402c501d10400061b200150806070421900a108101050841c006c07000d1955050702c0014200d1b6150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 301613848 1250 301612598 301612603
    0x80a03090b0901020c060f0f04030311091207150306050315180a050a0221031e091008040b13050d05070807020a0e1e01180e030409090b0109060807060818 68
    0x206000d06071107018400c0000110042d0000c0c00d5403005501541d0a99039040340240282e40d040d5403e594111141c8001780010380658080b0b814400c640c15524208401c100004002d00459408801d107600140350820400c0440041118000d0803820180b1142d42000b01007680c032001904c100080f00034500202c0c00d10326411100341800c1001400b0780350b2142e03087c1080e51b621200224100d004450000603100055025424403c40352482c001851511500c125407864440101c021508c817050704012510f040d95410b072400c0305000e404c1d12021202d14003400c04600b450300080040c2c008001d045290710010b000030030b06aa4070151400c0c007035100c948070f0078040503602400400a400c0202d2541c0894044400b50f0307194820f0380b1342ea445241c0b00c0c84c2094982446070003849804e61010410030fa085907907a0f9138202184000c49001106d007415a10782c2440e0076111202c2094511040700001801000c0700b6029000252a40c03000504449184c008002c0890703000400c940e01e2640095070408220505 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 301615098 1250 301613848 301613861
    0xc0d02130207080c070608061c021801151d0a0510030f0501061d0d05120f07080307180f0326070203010e0f0d0e0f0927010c030c0c020d080a03 63
    0x300c003021500d03141c1e649081c4142e6030024009901e140324602c0005141031260081d180304a001604420112280070040501130071090012079104022040890780c0b01e0443d50300a00030b1a2141400740c4440fa98603018218244d264130f80701e002010744000e01d0300c503250510242c0841d01c003941d00e89180d66042104500a116030b16040e94000e01300b00000030495884078010300944085050150740401032030410685011640004186404c943c4100071481d6001014111140820345140d1800c05199140c4001e40d0007101c00d03401103900444d00c200000b814254600150140791818040c19003036403140d1000072aa4003001c6034020341c11a01c1001202c5a409840c030300c0341d0290090009049280700da0b07880310780700ba86805481c858000b54002c0584164484070800d000580300356450050340c010f1100200e0000c10b500d0303070075503848000c040140e980c160901c0c1b401e441c00c000103030520310b2940080030b8440c5042c40310f0410954503015400b680d20303030581400c0c869003c40c985550b59080442074024014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 301616348 1250 301615098 301615129
    0x31030318080106090902010305130b0105090601020102091801030c0e011809020d02031506150a05030103020d1e0302030307020105070504080d0c0c0902130306060803040605030c0921030a0f030e0c0d02 88
    0x2443c600180303c0b80d2581000640a100b600c0a0003660344400e100d2000382006000500440340034401007100d801c1034101d95402060620026140c40b10b0318001c260000c0d41d10310100250110600104140304950a10700090000b070150654554544010451512015840d00300015981c0d1892011507031403a100d0928694042c0940c1d80d403404502843c101c15504944080c02040c4401140c0d000078850021103860350101e848640c1140d00710307000e001910005010465044090a581c01102070001c0c14034903070248a03900443e52864501d4000307003920800b60200007071100500c4180300c038000208140b143c1c07079070500e800040001c03a420710070a6400d01d9884408041c0c4005190700c010807003902c210b4140d0b801070760244422036549036030541d40d11462085000140090002c03170400a2210001c1032044001031142c840e542d02d4403851882e440610307000d20041e074000168584a01d07042501e0b211403880f2814101b00618510054581b540c521101180c801d4141083e00c004641e1500a1029801c2703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 301617598 1250 301616348 301616351
    0x50604060b0f0d05030d0606091203120f050115030f0219080a09080c0109061404080403080c2b0f0201140a020a02031201080a0c0905270a0209040305310303180801 72
    0x190f1424095103a41c088840703000301c1d504282c0e0204019024025180c11618212400b81001d2001d0328104c1e42101c14601d440c05175600c4521341c0600401d24054a03010f40550003105400041d48180601111400030b070f5802d500d4018024002850702040200380e80c005103003032582142d590110420004c1120030801400f00394042120342c6403450551120700454401c94040010074601d0b040c2e090326034070407140202808000c02c020f100080f0803c0151504919070011100b4040083d00d1815a6040c00358103011074400f40300001c0c10742540224000004100c2d80001c100d07020740081110424400140138098090b00000c164080510030800c40d008042500e24940e41075846070324003611801070f5441510b07805c458140103d20080b981c800e4a000c0c113501c00c40f40b144000006004202211030040c030441501540a00c14090303210000660322480c4255240e0759100c6440c070f04000c082a45200015420b130340406081d040407900030750341e41a0380d0142445458003004079458051705400307421021155 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 301618705 1107 301617598 301617619
    0x31c061d150d1a010303020c13020901022e0510150801060203030105011206051c0c0b041a070222050915070e28081b0409050604060b0f 60
    0x4600c900c1c07800f05800b50001c01642c2a4100343e0080d400350300080300c03042840c0f416400b09011462805401c40c05d09403074030f00003542d0380700014440b00c1140d07180c1c4031100c84003110702140719420440001400246401450303800c40403103900c25441e5900c0600e0721034885e41d0142c03160300c0c140e41300c550055007160300e8207004440a0814010780051580d56000101c0d86459030310788070010703483c4042c0710750780c1009619100b200e00d0035540c0018010f40040c0024016004044110743d40d44030800c4009485402a0000070083c2c07040410200b200500e0700070705454018907800c1a0710441124080c3e07074220000c100700d40841c0c001268940002484a412141da5140411f03008042c0c1583c2c41c0f0100c80341d46000d22552010b0943d8100c0b020560107590003080111074641010b0301d00740700766014001a0b44070380d591a62010080c3c07000340700700c1e2600300c004510786400042491002c0000d20f0710028 = true := by decide +kernel

theorem cover : BRFrame.Cov 301438848 301618705 := by
  have h0 := BRFrame.cov_init 301438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 301438848 ≤ n) (h2 : n < 301618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
