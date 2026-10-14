-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0405
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:39:02.053999+00:00
-- url     : https://prove2.me/submissions/059b23f4-db64-4cf6-a41d-685b8c0c8b7b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 72661872 ≤ n < 72841728 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 72663122 1250 72661872 72661877
    0xa060306170c0306010e07050c0601080a0c090b09040b06120111030a0c020a0b0402010c0303060902030711070501140306090a091403073f020f0f0a11010e030a03050a0507080705150601 81
    0x8002c0c1001c80d40e5404107100300040d80900e0400141d04034400c0301607840d0560754100340e5583c0d50b51000d0182d9500030b10013059444028488000400310800e01c55402c8000002d040303c0000d5465444400d0000700c010708084c0c01c100005150503145600303104040944400714038507910780c100282c0ca0380840741d514442c4015503008960f11000300e4602d81d00c03e81d0050f824a001c210300d108515040300070340794503401a007240f0300120511007240e4101d20200c54100d0320501310303a1002c2c0e8400045070458810206810b1800c01000481c05a051080f021035101545c003402180c90324181c3e840d4001050603101d0b1706050b81000c2403280c1041004c0b07104104052003c1200380c04202a03040541c80412422214032034004141110031505001b071042201001000003540e11305100e52020715251036114904a41401d40800310558540c0503103484040321501134000c6c100d2000a503030640b1142d002c1c905003010301209100c0030001a00800051259034443c2004d004d440c01814250405000302600c45810b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 72664372 1250 72663122 72663133
    0x110303070206120402130518010f0c0c1e1b08070602010605010e011b140307050c1c02060a050906030a0c110a03050306310c02061003020f090705090a06030617 70
    0x3699404083e02c00c02594080c00389a070351624400030748095107070401c0c2c000309428001000040724409603503070050206180213000843e0045058001c40350880c044001140300c603041007000c1a0086c9801e044400031540d24a80c03803551780c94170406103101280220305c080c9955001c0c048042d042c0a078034014111400280326132401d010018202031610165181008001c49001030a80d100c003450300300258029009031210000d400c805a242d07072011070b05590a2107144441c1682d81803517030207082ca01001030707140703544260180d0801003c0d030b1015003404104541800711500c80c8e61190000c6018190b00a00044c010312910009424503031038070009a03003500301d0100c0002203500301d811607500050444800c1001b45640b0703942601110940302c0c03070890700e050040844202599a02042c505182a0202c401c1c55440d01c4a02c0d55500f0207000007900f010440d801034013030f41000c8604940001e5a414050f0410464002150064246510407000240c0f1010200540c4101c040c2d0030702d074020820090513 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 72665622 1250 72664372 72664387
    0x1241a03090703201e03010b120604020405070203040806011202010305390c010906050718120305090f0301021309150b03010b0a02120d0b01080109090506073603110303 74
    0x94840926100244c0300c0d85001c84c02c8072a1800d060181c0d508007400074144100607500721620901c040040004502a611300058030030f05152903000469400c100b9001042c5070341d203d90030300c00504005401c0340207600c4180b101080c02c54080c041700f4060320142c40c00400030b4006000040540c1e00107890030750b40003140540e10a0741d401010801545558841410900d02028008400c3d584203080d400c1885500e40b0118404102c1207410090186031281d81e0100031802a4041d501c00844520a1041c4003c0741450310000900074405490000c900800c031104000c9250042800d81e0700100754080000e9107503106028101d483d100b80c09201c034540c1c1c0212504d9003441c2c02c0f039020388010f000c1d40c290319402265501140c0e10800070010407840c1b05558540750000742c00d0300400b62030042d40980c0841c9150002241808a610400c12101d030004018451034031410000c0c1c0c2c40020600344907540051654032071031705415503107160706920903988403040d0562030750502d0003001d501508142d200e41c000b00b0180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 72666872 1250 72665622 72665641
    0x5010603180609031e0302090f01080c0a180f03050a120813031107030c0e040b09120d1d0706020f010510080a02100504030f03030218010c020306011701241a03 70
    0x10310001da4022000150080300781000d40d4410303101281a54070f54041c119413116250305801500407260140d8200013103a4100c00150f031038440455000d103944200340094440c052040a06c2c00101000303400d682201e80c1c481c80320300700e80d4055800075241a845816100104000701d0b5540b070704141c0c1031030703e060182400d206000c0b10740004480170b402c01484074030040c4001000d10052004685c03001c0c0000c813076030385c458480d508140100c800b50707101a0000c0018844610110f0106107413170034402c0003898903da00042d40b000b8070b941e51075100c078289034040345004840108594005001c503074005200300d400c0c2031a003509654005101012465130010100100400000c040500b03c0e0b0403a143c404448113844200d420b03006561000d004900074900000900d1381541c000c200000c3c10013807424a81503082c005403050340080a00a40560000340100848070f0340e00c0001880820300000070801c81d00c0a0f0300d4041e60109903110004d82d40102c0c0701080000c1c030303401c040d00000e40b02c000003600798175116854 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 72668122 1250 72666872 72666911
    0x90614090702060108030f180306010906080d03090c05040f0b090708150316060311070c12230a020402090402070203240f010303020705270901060614070206042d03030806030105010603 81
    0x1d0341d2104010800c8c003910010109543c0102d04050110f6410f036a454400601420407449105000d0192080d65420784ac4640260819140c004085a05162800d02400001d0000d4001e0540840da03802c05c0d800319581d54503840d8094100c507a50751410342064442c040c02c20042c1d40301c541c401c4e030044010300c0d4003010741c24404044503618140019603006141c84241c80b4816094000c00241c19100d0110f010303800c801d850909a401a01e00302c1a03010012095100720a0892581c1c0007a4815800030300140703096001070400a10180c005030501065038046440d00407604070b072041d502c442d4440c0c032143e004c1d400c42c41d5521041200c0048000c5d403650310003035207420301030142070701850301700d501e8500e4044140c2c526411020720101c2400705141c035100c51030090145000300d400187d0480d851200c40425401650340d01c5800510180c60301c0e00e04442c5984403521034540c0c13014200f9425203440711303014001c0c503040258080e465102191138850201421110160081030502d03203000c105850403618801c2c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 72669372 1250 72668122 72668137
    0x105040605150702010306080717010b060f0d090302070f0f0806070503040c1502031315080703021312140d0c05010e0304030f02010e040e0f030901090801090809010503040c09061409070206010803 86
    0x110b0303999081600040f0050042a00101d03c10702c1034140c000f5801c2e64007120400258031300002001020415410414580b28034110038800820500c14a02e0260150b40941181d81c400d0040714207541c0c2c0c1c1c0e014056414280d50013105204841003040000b40014805968040807503d00300e86140351550300d40b29602000c0c0151112850a00f9080355007034000c2040ba810004030340840317414076540d582d0760340c1760b984801e209500094080001c1746c0703801c1c01ba0080e144254000004015428108400a16029900c2105644000f40f440310102001c1c03080c45008010111903a41c141c4d21070490521750300390341c01100e54070083c0d0f20400081000c2000325512440f425424a800072003072085038000f501034414418240001d00078035440307000030b2100000070f281040007070b04c1f8100301c196103441c82400c95899040c007030207058007040ba40d81c6542c8038030001d59101d0b03c50700c00c04114a0700d40641c0421251030f40c0100c0d07408440701c058a1154540004491740c45010352004060b150b060404031a228011100d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 72670622 1250 72669372 72669409
    0x160806060108130c030b0f0402040c0906051815120402031218040f02090405010e06100305090d0e150c061e06130c02030403050f030403031403131b0905040b0a050105040605 76
    0x1040400c1006042c0f030800150b070060008006e50901c03400c080c40d4071800f900c2c1240b107203203444c00c8843c0c010b004456020860380581c80c0c00d410445260b90501130300c003401604035405120000d9228454800101611480401103d0196a40340a2051503d000366207030058000000501070722038059000e5121072085101960041035030b0320320b005e17400041d0044407401688641442c00104a00c0e800c403800034030910302200c4101d020340212034154103c2d0b8040d200c401d00c6810040c4403280c0e282c010011640c1a40006e0b1024441c0681685880466080a91403100c160020410f014004143c01c9040544a4801c2101c9201e8100030001600150000c810301110030f440b095000d41d00360091054400864226003624510f01898200342e0b240e034000d0008401103000302c0704100848150905991240800c000301142c82d0240751100722080c43d020741c02c02e034141ca189202007090b003414081c50780218400c5044030f0050a013480004140c850507000140954540703082003250b5500c270381000030380c0001c0c11f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 72671872 1250 72670622 72670651
    0x10e0318040902010e041b0905011404030b06030c03060103030503070807030608030306091015020703022e081b0c030702120105221103030406020a05010501210303022a160806060108 80
    0x144010788803085000f100e6a8407a1a080713031f98895607141d0703458410704145a07490f8501d9946500055170101c3c0140c801c03150360741c1e040c0414400140d60b114919080040242100c4860080000091070008241c00c03c50010b80088140102d0582011803190054040d00702840b045040071211680ea0000400f224840c51300d0b00041481c1c0b1070190000400703000104941850b0781c80c075500c0656200307100d1000b03d0140b14407842e061928440e10025204e1114096000c01580300400070450ba0410040d21000080c0701100303081e002c042c0c4c06c9006003034001d4080040c6407100281c0c0100240c114000a103400c06904000400c840c2d88102c81140780090035000b00c4510443d980d0a06007080c0e610070364600e03094400000c0200b401740e000544070b1000c500c03035402800700343e8072050303030f4030110742228103400709450b10460843c00a4000d4001d480100122540807039080380b0305034008030b40e4840032183c6126420008805120860408411000e003039218024180c50400c480000e0035410001e0200000700080b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 72673122 1250 72671872 72671891
    0x80406051803131802070b0708070212300f010909110a0603270c0501050c0c1f1d131e0510170a02011d010201111b010e031804 56
    0x144106022002846411241c0750b03a50f044120f1074640311805242c401540802c54081426950b000f1180520f40c80b03d01c02405480d40c01c1d003900d80c214003400d407100358055003082c81401001d8a01078640c40c080884503082046400c0b011044425107422103868802104040180032100001a24119000d4010004190406d4101400e55100c00c000c080d078000c2c0c800600082d126859040003116010f000b024858509030007401001c258941d03440204001c410038001c000c50b40c060809010041030540131350721b11803e140f00141070035140582c5104002c014441c3c02403c40e0380440c5201409003040c950310303421003d00d0b00044042001164140400d0b8031110051072075004d541c5910608058403500303000d2401d000080341c8002009000d40d000300003c504800c600d07c1c2002400d04000e035010b03100c0b05150b45102000605250751400c05505564030740745105541d0140d03400a051054029840a0f4100710068042c1e0030349040151051041d17100b0300401c0c041c00303890902984820004c483c0041c00701ca4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 72674372 1250 72673122 72673141
    0x40504110f0a0f0b03010905161403070e030105040501050a0c050a020703081b0609010c03140105061e0c0304060513050909030f03040c180b010311160807020a080d120e0703020108040605 82
    0x1c140c03c8607141e481614400601110244041c5040c0c800002c07040c03203196034600403450400c4055800c00000f03854080f40d003207181c1d480b100540e0010f00e1840d003d50812038030b401003400e46030142c1d41110181e44d42c1b81040035140c2140301d034004034804c52405d1803504070410002507640600d4000a003900d000050409481e0f00300b010808074100a50b400d403925880c1c03d42c0124000c0c030041600d440882d08080360005151840f0341c8850580c1c80082845052001c030070440c3c82c0000e001014a56066010814044000010005400240515507031141c1c1c401d078002c544042842c0541c41103018514001c20b11103891004829224649143e1550b0f1b500e03903807035050000400d01a58800d24284203403203403501c1c1c2c1c0041c03038010b00e01d54042a01e060001e48440400d02c40103101d940035201c25401c07420344160000345181700070502c00b400188075550850f12707004860b00b403046a0710b0f1907003c520032500000d14030907540101500c92881e0005007000b94a15000600464070090004012580e00e9001981d0700d40d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 72675622 1250 72674372 72674389
    0x8070201050c180f1c0308090601080102041d0a060503010e030d150b090904110d0b06090708011503020c010b060301090b0a090b0303090906010216270605060f030402060706021611040504110f 84
    0x6002c007088918170b4480b03080c09040e903002510500e20781c0c060000041404201402100d0032500d0340402c41c1102d071106010500b0318200540b40c00c1500ea151140040d942c2c0d001d0007000c6c14001c008000e580c1e01c440070011441261442ea600018810040204004040884040c1c40d200030054a04007140e41c0c513440c04a000d10004c20300294050140c99104090002c0c0c0e200c8244a0b101c103540c00d0076180c65115040d03900d034009102c1c00e12400c200c0d84201c89217501c290041d2400c44401d03000401e03030042006c0000c016403c00d0f00103510807035031012000308500d8140c044200500d01001d04104c031701102000f02ea01e9118074042c0a0260402c031000c100c199108001d0740c1c2607446600026051b280c0c40e002d42d000210621100c41560903030b4024901841c0001d44100821180010400c034a01102c40080c0325094200030404ea902150505c04440402c0e446d00040c641002400341103910507010f490039103000c5400c0c0c42180c1c01546040c0070400000d440100007503204000700c03490701c503a903149000139403082d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 72676872 1250 72675622 72675649
    0x604030c020d1509030806010804020a170a200a0e040c050f0f10020a050f0c011e030b0d1506060c1a06060c1902090c090102070e0a06051008070201050c180f 69
    0x80c0054628080e0086440d13201020f0144240c0d5407050316140c0b100111015041550080e5101d40d240341c08201074202203040f00ca03500308140035035071030a1103900d660300710985a00c08200150392025000d005850801510000341407a0b0500842900f000e071036200e40c0b80300c0360107410301a05104400020035a1042c8a55549010007402d54007900d10111000b51076035104801100c0500c26582039980c52100441d030840e801e24180e41d0000d641c80b40101d00034141e000c0da40c518043c5a650070300301c00c041e1950200014203130f0160000503040d000036407640044030203580c082c40800c0b020340c59800000b40b00c0952440e4540da40b401100340ca8039a0750004286100b03078100c6040380c0c41030050b851044629014008403560080307070781d24015a40d6201070715440c8034110400d40144c005010a00076001c8204646800407021080015066241c101203100000341581c1ca20201e8540010011815030900420303501c03032550b03103259040015560107500c03220402030030305102d041c0c000742c814001c0e15010b038400440c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 72678122 1250 72676872 72676883
    0x3060406090c0c0620070201050304080c010903081006050a0503180c030106170f031810090e0703020403060c030b130c05070f0c031502070201020c040b0d0c03050c040b0a080604030c020d 82
    0x1a00d40220b030142c40d40304044001c64200741020401e041c20110410f420b500100c50010080c6408400e60045a5552000300704540d0717210184008803a28209104444503d4440d0310f41030b40030b0a00750000d84c11801a5440001042010811201290360200c1034941019407950048840e00140d00604c3c2800840111241c0644c0b8144001880c94a140c0048000500c010b080d620b0120300c8014031520382c030802100c3e070004004105000410b041545070004049200e18001811a0f05c4150305008510261000c1001a0300030609200b804401d1051030041c0d111401e00f0440c0055031170214100100c800000c540c4980c0c0c40840c6801c0c24022011100c08542c401d6644020546c80d250010408186000c141d554170440204401304001900c2151207454058004081c03070f81982e002c0101821a020704207801c850108268000100340d485088007075403203400940381d030503020000d00046070b08aa4103a840350540e5401044090700114207203801c140c040c40d110030030180c07500210b40d10001c624402410b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 72679372 1250 72678122 72678131
    0x4020d0b0a0f05070504050a2103080c0f03040302010507080f0708010302010f021f091101020601031a150306090c010216050904080f04030807060204090609060b0306091b0c150109050108030f0306040609 89
    0x213070302d60b010703005000b6035074100c81c03402c040394803110003854041c02440c00d0f151a80d104020500800e0058103410750113400124001e18140c011418888160002da8040780542c0d1a803061000080e040400151f00403004200043d00b8500540001e00310b10061102a050090700303404000c06038400e01c00e030850b20b0440440c82200c1403180b52444010200e00c1410346a2100000100071107610200d8000d04990304441c10501c0700c80010040007030048040d004017420402151001c0d81ca480a000e002c4c814041000034040460443e00003a080c03104c07100042c0045105581d00b44030f00c2c0d413107040194000e40c011810b2a100c1904000012061181c1e800180c034554010455a0403c80603800a1090b1003441806200855452000c4001d89195019440205409000082e980c3c20700b80c0095601046003807041352124030804540071564040c001d15025604142c1100611200c100642801400000d01c2000103602d0222101c0c0c40f0300401d4643d009513070000010680c0c0c1d41d6103412a0001c0d1030421010030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 72680622 1250 72679372 72679381
    0x110304081f110406080a0c21021b0c03030d0911120307120207032406030b010909020102120f030f09030702130b030f010b1e0402071203020406021504020d0b0a0f05 72
    0x108040040c04058003900c0c180008007070142c803034005075411680142c40340c50700c58603004000c0000d02024000002000140d4a4030400c0b980001e1304d54602144002c00143d4401300e01c4c0388104890b000301210f441e5948280301c0344040c4d4900100700e0300c60b0f901c100c10016a041c1a454640c0c0e04c035251650301c6130b0150412032114a0b4200100090044910654280784c0300d042d80b510503a203400e01e921000e4821030064825016080034596040068001c0305000a2400e44030780d100001c0c00c200f0b0704408220b60f940c091403021540c041000752611409502081d05204205807202414130000385107028250008002c42e1030281d041003030701e8003030b039009010419904c02041440300400302112003620a00c50302072a100c50310030612035698841e07070162201107400092005071403130f03180000c2038640040c5d0801982c00410f03140c0032007007030240d003e40d0003580d220701d0040028541071000e12034415226000c42440010f0f5556a00c04007195030054907200c0c0c650b5500030800090411082680c4418103220402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 72681872 1250 72680622 72680653
    0x141605030307020706021908031e09010b0a06081b131203020d091706010303081906030503031e1e0703090f0501050702071e0504050405010216030906030b060a0c0311030408 76
    0x110302c601440d50031141c1540d5500e03012a079421a181d03001e105480219085004541c81c440155440b000302c5c2036100c51070100c0901107a242d141250210002d954412000c0e00703915228800c0c00041856182281490604844003140c4001c000007000d0212400200c95a21030000200440240880650100342084600f400fa448421604413030b40080d40030f40001c201548030300003009100100400506441e821603505480c4900c02501da6000000700c1124a03014120303a0142002541c03050700550f803681048640499040382c4600c14500c1c40203010100811001c042c07505c001d00300005a1681040e4807090016401010b0001d00503040c20403110f43d000500c101500458003075841a400c99910f203030342e22071104a01e103032080b6240350003a8901b070400443c5025040540c1190042000618100110032805098152024100d0206201e42c00c10409190144900800b000341610300c0f616180809100815600c038a503001014400000c01ca00c500c984100180c6001c3c2c070118040795212070450750b40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 72683122 1250 72681872 72681877
    0xf030d0b032e06120f0b1005030d0306091505150906091e01080a0c0e040506031c090f06050712051605010e010605040e030403020d080d020d060f180c0e0114160503 72
    0xc00300e12604140000400c4001c9420900501d45c20106009410a903541c48480003003000e01507540240c00d0160114099500717000901ea503000a80740095002d00c0d0091000c19150100d07140d4840b2051104100409d072540d0305001c02e2591005081c075607030702910001980c203020f20000c25400c8150603007950081c4a403c0c1e03c002d01c031482603e0b003d00075605c210f01001503071001e01480b0b002035116254400981007940103250800401400e40e0004070124900144644036010410001549074108000a40040f1008030103024103180251034590b240e107852801c00c954290300710401100003a51000051040605180e040d4084024001b00e0b85020007180030b4680c90060510031803511b17000c619000c10000480c0c0c00c81c3e0f40a0102a50030b246500c03124540d40151007201109a000c00454060514034424075021b0500400c0318480c960804403d40030b1200141e2600e004546488002c2e43c2e03668100b049144100d100b480c8c60280c95a0340a620740c03490090070651421031488540358010484080007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 72684372 1250 72683122 72683203
    0x3021207030f020f011e020f0405120d08090309010804080f13091b170601030509100507170109150509060a030501020c07060e10050313110306091005090f030d0b03 72
    0x3c6a4091108540d139600701d51600b0341940300c10071125040e01e020041360300500713072016010103c40d007001d603140d003c101041861200042c143c7c03c1189545102a0409000e68000344024000d50404820100107490580d01030f1025101003004141c0c00001d00a0b8130444d201d646407020364003c000d0b1344130f8040703014003285a0000c3c01c0c40c40c4503804000081c4501c450035003040c411410443c00d521488015001464007a00700801c0340900c44500c2d00c03586503809281e0065a4942d9054034176a511700e0b03090040001a006096a1410034803102140f500300342c07a41069031801c48103541c4070b03281c80c0d000502500c429440200b065001150030b00329040f010907400c00321340346611415008501c1c0c10400c6514540840c24002042c000d001046800b829224200758841c440e60000c40069900400246030401c100c1d616081c1d80e000740817a81c000c100e14002c241c3c005010030700070049400500055608c90259604040340c03142c2e1541c0340c000710b5030200212070010661710b00039608416600303081d444200c030026 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 72685622 1250 72684372 72684377
    0x120807020709020f1207170c03010302030606090402010f030b011209150501050d02060409020a0903060e030c0111030709060c060f020a08090c10080c070c0302041a040b09040c1203021207030f 84
    0x20340050b00d010580210307030544141c109401d00e082010014014081000350000342040400d030740b01d51600c3c0354014aa40206081c01080340c882d80b5500c105860400c0080005000c1c00b00b20b028040141d8002c1e0000c40500c0c800d01b00404d061200c03800480b42040444061011182800aa6400e00054035000b0f0b202400f440014050707680c98806004030703050100d100079041001008100b004a00e0744d4050b000c8403030a4034024035903664980343d401c240c4482101c2d54015030000200b131200d000702441030301c101008042c01c80c2d0031484c04400280c4112400d11500c010300101d94100c00c1008103c0d4490030076003491010454503148030a0008104207002c407251442407040604a207501c1c9005407401a041030540d035041c0f205d9071403110b51401034120380c4044407104039001380440142d07118010b1802c04103400d842054071140350700411007074810001c4624010114082440041002004141c069030807018180207582c407031b450304034905030300e00c0345142404030301007040000c02da8070200800001c98141d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 72686872 1250 72685622 72685633
    0x3060a0c0806092a0904060b03070201050703060305191e03030903020f060f0c07081204050309040b04090f0318150906030e010c120b01020f16031a0f04020d020d12080702 75
    0x550520000b0f60f0203070b03003140f144c08103400301d68031050030041906400c0c42c01400c0c00f81881c0644001c0b4041e5502c940154070542c401204014000c0e9091007015403000680c9400c3c01090310b5078039010789070810030f84e81040004461400c1c0043c4064250b840956680384201c2060300d85103410000d00a064219080300140508421408c4d84800099010301424100780d1156107a00c0710501c540c5154403a480c01c5845540c00e100074516440301051981c8200d00940141d503a84407010200412102c62802d158401c9240418450114500d04007200c08164141022030400b03285490700402000d07980d0003c14800310180520b101a507000c400b10301224080e85052281c05400882c481c2030b01e004038880d50000b40711240c20340101c0e8031074004001c92001030040e0303404540c0d90b01a5a0a100b0f9407d01c25503c403262b50020070030412058035000c4c1205c10001d8150031414003070f00001d12540081c0c00a48600340c00d0700605c0955980900c5d10403010f6220704c0d13061400d6804139001d0240340c3c0442e140300250251 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 72688122 1250 72686872 72686881
    0x3092109060f0207090c0c060e07060906020304030809040b010504050d0501020702100801031113020c010e010518060103050706030e030d0203150109080616080a0b030a1a071803060903020c03060a0c08 88
    0x40c14841d0030b0b0301820380241c0f07401420310184000030b105941001c0200000004648007080082c45003034410102400504a100d050610107030a84466521010465100700410400b062121096441000d000c4402080d034003004030040303800f4011500b14076031161203a44c44404019055004000c15031094541d1800e18401980030346000400740b1003c1e14003030030003100c0074551403ca0465495642c4107180182071580c2c40241c2ca08440d003038401c083e01ea80d50b0f603007448113143d0361800207503013100e90360000e00040d81155107554071000140318080c2807507101c3c01a000c020500380b040ea0340101c5152000c64503441c0c01d40f14496450f01040130580410305149012a05100218641c1c9c402d0680b6068204102c09154003200c48100003010342009560705d13944440781e40d50a1200d6110b060040d1a840c178058110300f102803400b14040d0055050040b041043d014a00844403501b040fa5048400041d0700c540506040c2c2c140b00c000c42101d039050048004021035400c80f035001c0400c2c02159918080c640c0c0d074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 72689372 1250 72688122 72688127
    0x160602100b0d02060c01140907050906030a080f0307030603080a0e0108060a080705010c0f0203010603031115011802090d0b0a0e0106080a0809060a18030b15011803120309210906 78
    0x74641c03029042240d0900c40805424000010b0050242c91000011078030307452000b003d00180280c0d1104d0554018003c1007206141524007190082021806420b011595a0303550295114203950391010007000700c00205258001e900c010015034203c8080d0b5901c081c1880001c206075440004030f4040342448000c150103042ca8407a5005a030340c007800600710f03203080c08010f444a6940d0703c1c0480c0c118002d40324803801a1004e015000c01140302e511141c0820b035600c40081e040c003d82070386032295404800010885080780c91b0f0801c211213250500103940b410488041002c01041d0036010702251010f005020562a19522000d404100c1d0002004160340f1901800c4c0c4035041c0391000b91100400f40117030002807911100400c0d1500c424108651903462409005080c0d506907802990540044400c000032401c240144030580c403c00d10748016505401d0103000007030130705030001600c1c11415400c1c0c80c1001e802640714280040c1c000101c1c3d14820002e41d0305103c0742054512070000958284800a00b550 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 72690622 1250 72689372 72689381
    0xc01020a09081903140f04080105090d0203070507050603070504031a040204060501050f07080d1409060402011803211202040915050603060604030605040f0f05030d060e01080a0305030907030516060210 88
    0x40c2070612075203c1c000e68800b258541458000320400800c02c1108501c0c002980008000030400b500c0042154a80020f0341420000703900d00c5142550020004000000c45c0441d03400e0940d001103a80d0360702da440d00c55049a160040b40c10042000f540c402011420501c41929288224421182401b005031241d0044034940100c0701c80d410320b00c0d0184800320011380c01030081e0203040c070302600015a901c0c00c40c907030022802090744c0407012a08204140415940c1c428000e4082e8818005c000740300078695a183d15801c11009299607110b40003a00005900b48035010612080044c054159102d68984500400801d8900091144810625030000d071508001782541e11800d0001c00d0b440c14940380d0313180c000150800500c00c90340c2095403000200081c500640d8416002e000340001c5464104062640c404c45205410140c03d4015200c0100550080018101d40065243c9042e0382c5035142d00301601c0c9046515040207080340600c40e04590352202e40c882c0c410840e8055404ca4500b428001c2c070f0130f030031203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 72691872 1250 72690622 72690643
    0x10e060105040c020c0607140a0813090506010e01031509050c09030714030303190b04050103061b080906060d020d0206030f040c06030603020307170c19050103060501020111040608090307080c01020a0908 89
    0x10f8101402c40703415031401101507e11240151011160032001180f864101181000201da180c040881c213045040003460940c4064406c441c0200001c1c2401030000e4043c1d1a141d004904040e21851541c2912145a10120042101000a214508011003030702102d401500700b09010303204800380090017000b09078588800e005c000c0c0c0554599160801e40c40b40549540426904140d01c0302d0b20180ca03a200c0340301c4e0a0086016850010b42d45a080d1400e016640540400c1000c000445091040b070391808a02c40360001f104960b21010f2032801e101103000950504006940401c0100810546102542c21548250301c0b580000b0040c5407550002d6084948a01019400d41c2c03003282d05201c40400d00d2404081c4290350011940310202483c00a983e0b01004040b0303200d0b0f500000300c00c11843d40c040c050761000e0002400248150b007040708409045029500c1450101b264042c00710706600018004c4881c61504080b00c503a5501c001c11b0824007030344c4200c1010000650100c1b00290768440030a03003a468 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 72693122 1250 72691872 72691877
    0x20c12041502160308070c2301031415061321030219120305070908030705010e0c030a080313020117040804050f01142209020a0215010e040c0b0a030b060c010e060105040c 75
    0x11400c54440303111300d40088a0451f182003d1040105880171407500e500070007280e000c504410782200b900010255115180c13a00300c50f43c0c00e1030600000190114580c403902d9403d4580a8036443c030580c03940d6014465a02010888503603a085883e41c8841c0c9460052843c02a000c81b002000d2009482992003100400900760b10b0900701c4c030005592080e0031a540141d03191500c0c50709151079040c65402c590064004482c41e030341d2250b038802c40f02024813581c40e07920011409010b00a0701c0da200c0c10302600c4014083c5103000801890b210440e80108401c100e451901c00140c82c5901e803900e404980e0f94010b000d82841031030441d54540f010740c484d0b014482c41c00e11104985003401910a4181104108400038020107442d0a0020512644510180144502d0360380105068085004035900324501038000031481c520301300411000c50b903088080c42c02c07940c1c0d40e4403542c2d64148040c0c00b06c0040490035180d1303500c69000101598802c00540080440000001c02d0ba901642e8440030802121104880e8102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 72694372 1250 72693122 72693163
    0xd090c170a03050f04051005120a05010602031e0f040608010e0609060f310606080c07020d03080907050405010b0703030e0d08150f040f020a080c04120b040204020c12041502 76
    0x80c0c410b40103010130b481484407490030941c032400022040405407500000007000440ca101103d10f500321442c1c0c0002c42d000d0200010f5060410081d2203100714558081c5944910707240e08010b2181000b183c0142d03a04204140e140c9480d040000c0983d0340a21808070350741618400300e5514508406601d015541c0104514110442e100038048215a0394a2000d003148801004100d8440340c0040c15642c00c18141c030004140341014006000e005005d001881510024001c03100183c0f260340351000000c0d00750074501400d95038452010329102c8140c01240c2c0050034080005600030007500604080352207a1020301184003002403095544114450000009000e0360229140e8580c0c1007800d079030200083e0141c240c0d14a1200450700b5114200850002d9550000d045c001c41548040c800e07401090f20f81c810f510f810301d04203401600c1c042c40400a001d00440c04003186c1151307079690480e821868940c1c01c2e00c03074a06680d41d680e4031a1b0050704c210b0f840302c45416802e100c298404245440c28203e403101061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 72695622 1250 72694372 72694393
    0x40b09010e030c0a06080601020f0a020a09050c0c0709090629091b030c040603150303020a060f0b13050106081315020c0a0503040f08101406120c04020d090c17 70
    0x155500c0d001d907000c0790507004044a214241d202c40003500301403d1503484442c900c2c10541e000a1600c0104811903034640c0000d03003070702d006035148178808003124000180032400c0c0c0c54400321025607104514118a562160703550008580046400c0451014000c84082098003540a440580f00c849408030311040c94907c0716200d510f00c4c2406100c1e800029090716a04008105020401141e0007031b82c1c07141025902040802500e585400380c10030304030002402da4107251540e035000c3d5807824004001000c02d9211907461405020613400707590007140c01024500b00032000058200141001c0c0118000244241c0001d6140c0708005042e0311610742c040c0080d03004480440d00e0b04000d4106100000b054041c9060f680c0124404002820140c11038990410b44180307806415444c2c1840044084032160505901b42d82d81c40744088029402a400d07108051080ca503800150f0918900d20041c50707000c1d201290080d1000b83c180e000c0e180c080e108865090072035403034140706a02d803941202052019400032070001d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 72696872 1250 72695622 72695627
    0xb0618010608041202071e0302090c0f0706052203050a12020405010203091201060902040b0a030501080a0206090108071e02010617070b071704050a0b0309010f090209010b07230c011103040b0901 85
    0x80c10b0034134510640e8a50381d12007902d110516826103103c01c01e80b0382c00300309105501d0700912250704008004d406900d4070041d034031185000c1c011158098034260743d502c0090503c1c003503e030104150310140c000750501c125884c40e0140503908055207178000110941810320808001c0d100301d0b82540c405800031414100110200070540e440340382c0c940f52954860031f0004000744140040c0024004101d030f07a5480d1204144002c04480b030581c00100543c0c0b0812410303001d601c905080b50565502840c2516a5684a010960304954103414412042a55075040c54800380d040d4000170507562180d5000300d403a2419080301e0340d280740700c2c060514200c40030099040000c00203c0c0081c49030842c101141c4c181035070384001542111440e403011068480000c10450110b0b028402c00d901c8113040c807030410880003a42c0200710a103c0500511110b8040098030344244412030585071010a02c80d5422140b081140a55503207403800440904c0c00318190340518207659101000f136a0a80c0c002c58501c609142848004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 72698122 1250 72696872 72696893
    0x30609030415021509010c02060c030118050c1b07090b090f0106200319030f1518090609140c01050a0e0d02010908011a011d09040212010209030a0b061801060804 71
    0x248800d5201c0c0c0d0340c4040c40c000c418511035205140203000090071041e401f0010b401d10304010820200c00400f0001031080c0d03d5140040c41c0511030441000070595119555581184100c00c00d184040e0442c441000102800180902c1038a684903011b100155500d4140302c422041529141070b03403009a00103110842c400c401e1f031003094130040d1408440e43c800c901e11034110b520441d01106194103402020000303c0d007600170440d103d00d501208001c204d90040180850007094010014515030403403d180c190300f241d40282d00700b50340184040281501e9442c001d1640351000c1160ba0b1540505190b015007980100181c2d0340052154446030003220b0407000b00114004803103012814021820000f188079502441a46a42c0c80301c085030051f0045001c3c005415050444421a8603800804c3c1700c0b88951100f405ca1501f1903415151000303140d042e0302001d03002e4000c2480b01c07605886a00f50030740074080c455940c980141c03000d0b0745c07810701e1490080e040000c0302e1090141c0004a8520408a400164109034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 72699372 1250 72698122 72698159
    0x403020612060a03020a090f0c0c02010215040203011118040f050403021005071814210c0d060b121e07060f0507032003090a05030105010303020a02060c011b120b0306090304 76
    0x11003e140d51039030b001a03e0340c89660488450b80c7c1e9517004d00d181282451240040c180603d00701001e4020007640000c0d074880603a4100e00d5400381402c089070454509400207220800544101a00c5000020410600d00941c1c0030b107a06c1641032030503c400d07400052190600032078159003d072030744280c50045c480c0602381c060114020004a04490010004503419420241c801d00450019a5203030108120641820221202d10843c1c42c4650140d00080010f412809000940d124551600c4a0502c0e40040c80700c68185500301c07940103002181d000d80801c1d680040f1000d04500e41554400141455807071800303000307a0010805000e00141d25a004801500341103101c0d2070140803422245c0d022072091500b80ca08606954030224000c00f4514020808201901095000b0000e642c074503180255038594010340603000c0c3c180041c0301d2860541c290002c0c5803042034a1100901b5a0342000020b110701d1600c05151003c03442d0805001c404c1c070700403072023074091000c55008504284c14000f802400000f0f140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 72700622 1250 72699372 72699379
    0x130b070519060f05060901050a140a12030c050721021507050a0311100203100611070b040b070c050d05120d06090e06070f14030a0b0406090f0504050c06040302061206 73
    0x20300707050410010703030400014a0b2180502003400442c0455510a41c3c0d0302901c010300c0f40b0314030303c014010754549800a03c104d60040d0aa660b04618680c045012420700e070304980d0344480400c99000c141600b01d40c0d41d0901e140710303804640f015030740c80f100411300c9210520307001e0510380010030041c0135203803414034142d041c9018413800d071410b8026507900340307000c0148500704c001c51502c3c075140941c40c20030300991540c8240404150f24502d02804069440002406020144112607581e00c280c1e0004001b5500603080000c0c0456031a80c035100040d8040c0c202060444422460740b601103a1418003682c03002d482503000000304907092800001c1c10b003540100c000911b82c15526103002523061640d0098a11405141000d407045082409004161a41c40c601d08802c1c0030240d402d1003201000001140d5012100b4200010300384c90101c00078018280950080540e00d050070400b0001c100c456008900030f0303209100302d0f1300c152034103001c1c0045030099100c082e50001052140c03a151000c00c00030b42e0307880744005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 72701872 1250 72700622 72700633
    0x703080d020d0f1a15041509030206030c031906080a020904171308011a010c0803060a030b01270b0117060301020d02040b030a0507020c0f010507050127020114130b0705 74
    0xa00c88002220002403090100d551901ca05034a2200c8885546130181c100b550050f030544503a1340400e00c28404d52040e40710426000000113411403288643ca005154000e01c4160b59041c0b0814141c0b140e00166446440c48a032aa4983e441c0d0a10b842044101d580c50030280030704072025000c01c0000d0314000c100341c2d01040c1c1c140c031080700c8014110080c80f030380000c030b800c12692904188030301d82160490190340c649507424651840306607800c0044c40d03002503405058507a80c0d5a0b20808240159003a6100500c013103c900c1c0041401c1c070b0402480c100b40c036181e00c4070401100344c10b0054019910101c0610b4082403080c481d40503d134180301d1001c0e038040805000503292407045142070003240d20a40c001b64501c0b1011041c8020207600303004064101c002480100b208240c1d00c00040c07541c800b0000c0040c180500054000c0c01c101d404e400030307003550404868006a000c8007102410320240c103284101d00285044007482c0c500c200400607698603a00004d00000141d080111901190348840015201c91290 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 72703122 1250 72701872 72701887
    0xc0108070801181b170112050c0d0f020904030908060702060c04150e03070608060910142205010803192a140601030804090f020c0c040b15160b0c040303020703080d02 73
    0x111003a00f4108181e45c2d64a018403007800c600f0000301034060f0013080c49400c1501080c1d02041000030071500702c0701c0c100d0b240c1909801e03a2400c4980c9491401c002500410000d040205050b00912824110780b031460130365244d40e40d1902e0890b11440110b42c161096036042c00b0078007800c07a804020300f04100f05420141c2d4205003480003e85025141e5014030001000340c3d003044130500f8004602c0d0340254005d181c1c082550304244804203044461380d40c5038000d1514a08289803c140008107070502201100200601e50b1101995500c0c1e81c800c030401c101802c007690001c80c0b60380c032414941e480075524050f545040c08541070384001c40c14107840300781c40456080003c0c00b10180d05010440c000c51292405030750750703450128034409840c1d803100d415801a01c140580700f020980401c050902030701c00c0310005000d05202c80020ba40c2e0b0280ca10000b407c0c04045100160300032024000307052540900d0452842d0354884c03050030b007644564000200180c119040400c00111004090400425050009410000c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 72704372 1250 72703122 72703151
    0x1a0c01020408010b01020c030a050a020105030604020706050412080c040317090102010618050603010b06040b1602130905010902042f210a0b01090503032109030415020f0c010807080118 81
    0x16000032240f80d40d07401450580e90703010800f034400614240c0207040007030030320746403280c840b402003401070f052245c0000080c801c1c1c0d44c0c070350483d0406a400031041280c0d0826041055803100078080c184040f45614001c540d00e413201c2c009680c200ea9004942840b8218648002403440e000003201d14195034807800081804000329044c2200e14021240014540c03801000701420341c0d1a0120150048034104801c0c0702c407402c0300c001c41d900c2146080e07410306220610320100d1076106015101118082c54140c46508002d4190017100340903000321000c2c80b50b035a44200d40714140b1410344140004806200c040d4040118610140c4180d21000081e03040348444000380382064035046032040741c3c442d40d42c80748440a60708010305da40600401d40080d81400c15040c00b41c10440d6020740c00f400d4803000100011000001042200c01600d030809401504c041410030103581e52800404401d410700940d013050105502c682e4041c2e105003895590351106ea480e14283e0050f100d00142200012622107000500350305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 72705622 1250 72704372 72704377
    0x30b0609030303280203070815010917010207030305100509040f0c0905040305030403020609070819060902040903091503020c06070c060902030604030801080c0f060403060c12090807060e01050702071a0c0102 91
    0x16502108a0036512a8941084240e039013a290480580c8180180301e04598040d10042e444204699030552420310200185d031113000b240d2040020020040c858014080c06401030030205111391800d0001c6d803036003c0200c10f000f0440c00390980100341580060042205541c04404180c083c501c12072095480f00344002c01d498044a040e80403810000500c41050340c100200c55002500f03038098030060341001c0e411a2100c1e140d000484c2000b061142d010240301103036225141c03076070303005004004c040a01c3c80c01414624052058505030500a01000e2140b8080d0007141e082111210107065541d98140b41a10305001c1841c040d200745a03150107520051310f0800c0118003440c040c0d00c42052540c94402034502d070602096607035000c4d4003400c00078001c5442c1c80c0301343c50a6960200c0007003440c030a5044100c5003040c1c4142c1d83c0141c2c0b4200810427050101481c010b11240b801804184500c08030f0764241800d8030012740d40e0b000180e000030000c0100450740e4a01501c2e02e260200e04034649211004510b0030798 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 72706872 1250 72705622 72705631
    0x1201060309030e0d170a030f15090b0d0b06010305040c0b0c16060309050c120f0303010603020d0c0302030601170612101a0a0303050d020a0e060f03040b01050f060a030b0609030303 79
    0x10740d541c090030041c150000020340c0c0400c01151101c400751074aa8800c0081600c8001044142d00c01298807401c0501a030444a06002c80990402c01c0594241d11090350041e2480f4a24038146410075101050911000070b55007280c000f1080c0340c60791a102c00441c000c150050060716a4081d05201040d041101c500520f80c0c0c80c40304008054407000c02860341024042540000b0074586001c040b03000080001c40d04c07010035002168001c121101700b1000904211032403050101a0000000106819825034040e208550004004100000884074250102e1200740c2d40d445c04980582120107000c00310034546035001c40f004e090003a5218400b40d500b0715000001d1415032000341c89541103e40202005801c80c00c01c40111350380300f402c1d865601c01402134482c4840019025400162940000c0d00401c0a41d130440c2020b800c05565041101c4440201d400c107480171100c04844000000380d40c036002c82c01e0301c1085e9000f404285820006001030b402042d00b40a01a0420000d0110020540e028070165208 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 72708122 1250 72706872 72706877
    0x30b01031109010b0c070504021b06010f030c060f1b03020a05120702030c03010b0f060a0207180203040b07020a17161704031a040b0127050406060f090b0f0114120106 73
    0x1c20108000350a05800c0801030359024407070001040ea000031442d0807507200303070390040c0d48805040c0c1202809a4018442e485845100c1c00065174802c0302240c00d003268000c0401e1041d03140c9440c01102c542c1b285d81040c00c002005805031045a00c1c0145030704407507503c2401111520925503544c2c030304000c0e00301c0c5141803030a800315845040d403c1c2402268441e98044008001507651040040e4640c000f04045600511011450550150007003180038054420459013200e040c000d61220300181d0700484040310f4210303180011a03503450001458405c0658040602002c400c2140c0c003112050304681c0710f2601d40c18aaa20034004071b504502c98450310140e6210141d0388508604013400d0091040340e44944034100d00d0100000b14024245490544002c0f0030b0030420182e40c4c1c8606500c511000440280c030360301d4001400100181d6500c0601140e0f041c0f2484000c50399216200340444440148164001c0055485100c0c1c645c4644e0090180d43c00007200d80f070030720342c2c1c90180109800098000201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 72709372 1250 72708122 72708143
    0x6100f2007090f02040305120304020d0c0e060a05010305070804021005040b04090c03060605160b0a0608150a0612080304110d1202010b040b0a12030c05032214010c030206011509030b0103 82
    0x40103014480f4003034035040c800c1d0319152440c0d5815a50308440c01070700703000ba01e005c4041000c556950f0b20344240140c1042404c54400d44071240c2c00421001500d1072846000200c100240d603501034020144104200d1301c8020302607941d9002c2c0401e8070490f000040c100207040202040c40b0403120090405041d00480004403117000c01300260072100b2641109040c04424440b185401c0c1030341c1080002c01d9800003083c019925540940c90140400d0f4100c0d190324000e0700c24025103a041e00d10086d11805442d40d046c030003fa99045003071320569002c0c2024000c1e24080000070046082c15080c14601403001d82100c0010900d034031903118004207480b005005035162004030245143c0f9000301200010211040c0700c4d40b0346064400c80c014800d080d4002c082c02400c0344150140901401902d10009943c10107806c03020356081c5c041c02c07051003802407084080c041c1c1d070b4410055109071154100d141e403580091403981d00f00400b4005008903045003504102074400040300188001c0d0788a4004c61042e49090b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 72710622 1250 72709372 72709379
    0xd060602070801060f0b07080903030d0c03020c06010603060605070809030a0b0106260c07110315011403060c03040c120f050102040e0a0e0a03020601180e01061410030506100f2007 79
    0x7800c0d04c0c0c00d5031000c981d80c440f020040c4031103410b50080301d0f40c49a01400c69669880880f011a045002c0d980781002110b00e41a000140a81c060300101040483c10003034800e2607803564005c1d801c455140c043e240015405002c41e100003582840204007940005017181e4011001b1ba94101036104240c010400042e1111040e01d8051300020700007501d801020704841c00c2e80f07460001d9080a00801001038994000785250041903101489000c20000107020302081540c1c541c0c849011240e00d000c1d00e07a000b40b00d094001103c1000d0356041d00d002d5903021180034451860000c43c0120343c0a0b500d0250f0328601ca102c0b0b41000200309200420040407407200c1c01302c0501c3c04550010455a00405d880324542000701d0220019501058250540b000b0310b01031050f8513010400c9100410807101300c6212503107020f4010508005e44200004000400c641c0020b00307000c1194101c0c01e03a80b040e07646a801c04800300010440d6030080b02000c1c2e03420141d00d4100300c451600845d5425001039001201e03019000315a007130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 72711872 1250 72710622 72710639
    0x30b0d0206030a090203061e06090c16060c020c03010204051804020109170706090b0a0c08030a0f020f040302040623040c2c150c03090d050c0d0605071709030a03110d06060207 77
    0xd64007084508c040c421000040d4a00030408400400b154810b0040d100040c2d00c3c0070280003520f070740704903480c5801503411031341c5003940040044054080144c841e00c250003101e46414000c0300d003034440103004c13007500c00034218000a20707400c041d0040b81805444280800c80c404514011254a0804070081012524129003e84440d0040e00a00312804040003080d00700c1d07810241608089a1100b040303035880d0788800c140c8000349a00f12415031131900000786111510081006041900d00848041228595800300580041c90205213002e00d00c010b1142d1440f01d1134a9800848119010b0410a02d031079103103400c0215015420071105007c0085c5600e8400d01c0c2040714000c0d24034400c4103000c40c03801d402410030598900503109018410081c40c1400410000280b213541c0f581e00001e048102413100c1460400054030301181e4101c000b0714010402034040300d040a5190141a055016500d4240f43d03100c100d01070b2a285c80c440c0c031180780802844819244034414a40200744070350161800e0350424454 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 72713122 1250 72711872 72711883
    0x709090602042102040b060708030f0a0b0612150d02010f050901030609050a051006020c0109091a03030301060504060806040902010903060c090b0f070510090b0708100f0b0c0f060702030a030b0d0206030a090203 92
    0x3c6c01d02560081c0b210344000344403541165040140c0750310107401035403020941005000068141d9801940c0481c1a501c11045136041d20b0003826000002070484010300c0501003580c091400c080c0c0003407002c5c6940c0301aa070140c0010031070500c0c1898085146910b903100b01d01592020755465034011340d03c2c0100402c8541d00301d610b902810381ca101604443d00280c00080980f900e600901a413541c1d80c14909003451030080d009100c0b01d5019058a07102d6039980c20140280e0440d06c580c1000c941c441c2c00150701031806104503040c41d03905859190125055032519002041d028160009000808901140807000300010303128008c54581d40d01d655a00d240f42007800c0a14880140b00d100e81001002c000150040b0101640a146442d0046030303030750385e14034102c2c18501e00d51244c080c0400c503190126100c0a044010040800a04110740000440000540c1d0740c0ea81210307024010382060060b0307000c0c10b220b60840c2a03100c1000340380011a03000364000404c5070380161880c202c10380d512100d050171070405000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 72714372 1250 72713122 72713141
    0x90c04050c070219030305040506090303040e0f0105030601080a0f0b0a0e16060e0117010605070302100507090e16020c0402030a0902060f0307090e010b0406050d09050a0f03090f0503070909060204210204 89
    0x1a004002851591b014125010701e00400e4421400401d180c609030700c04105540007810a244a027040341450085e40481f040c0a00816029002e0303c000854142e400040c90290b03640d00109040716a62203032640500c007200034044000e041e48071465100207900811920741103188603401e000300c0c54034011000d040f40c490080c256060252803400c5015001d0b404880c1c60442e2002d0410558809407031a00b00c0c10018040f04111070381e80b81000307003d075140d4030115400560f1840c4d204e004094489481c0c3e59442d11001d0300c01c4c070041e40304603085034442c20700790003864000b0030392107011401d514180c0c0024840c0e0099100307003110308404000c02c4080365210310100000c0c1a11303002a002541401c0c10350080740314901503442409000140c6040540d00d03030b807040c40303c143c00c003050300e207090b000c0d2a081ca641300c000d08055000540801c0f01040082d00240d90f0411034000600420b40c80c3d203040642c10260000701c0059494650a000006010080006552220702e0354080481c210352507204000403100003070f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 72715622 1250 72714372 72714409
    0x10507020c01050409020915070c0303200c0409050309060721030e0a0b072c10020c0a12060207120507140102070206030103030c051002040b09010e040e0d08090c04050c0702 76
    0x8210741c0c050760400c0403502940d0007000007594a03400c0c1e0b0302141e41048120710104100c3c0b07000401c1c1301030000192810040c1c82c407940e151a0584d41c0751b1040044a460070980004541200c090007c0f545029807040d0311280c82034059a0038403800a00041d02604004416200c5142400c0650006c105500380794120806c241010451442545051991416080001001056000d0201d283c0d64064001000901c40c0710b506035259070504400d0340403245121544600607051148201195400030412a0f4244030180c0700e80c101910f01501c0d100307684843d1201b40e44ca50b50820181000c6402d2200c00c02c0c40900da502d40543d01d078006e03c1c01014158915070020000d910600c0050700690301c000480b4111b17a090325216850401d2400e0540c2060715075443c980b5446c0c40060001103440e41c9001810f104502620307000b0b0300d6800ea10900c02a900810450310058100b41044502140210850380d00705240e64200c800048000300854222002520005c0100b200400c0c0c480441c5441c83c801c01c20700f041d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 72716872 1250 72715622 72715633
    0x4050f0d02040b040c2a051f020705030a11010f110a0309030c0501020307020a05070e01230103020c0f0c0f060c0601031205071205040e010b0909190f020304080304110a08100504030c02030d1101050702 88
    0x43c7c9800741c403510a4811107840c04040700120560000d1501510031540d008016240c3d1b94100c1500500500d6059102041a500704130105000240c0c034821000307400740410b01ca0307140021544080b8010055518100c042c46041082000464000d20295100300349a8000b000c1a5180342003030f501d007650340d0380007014483c40c038001445104c00340103e414812040a80c491860060f4038010b8019005144c0039803c40c1c0b0411100b0b6120f08000159100b014405032001c190702951034003401401c5c82031411030881c0e0b81c05170300104001107084000300303407514041c6081400c2091f9999408880d80905002400054004c542407080142c90a0054014030310641841e2070503a10a0100340c21000040c0060701080d4100f10301d1805402c06e400030b600c01030400a0855a81c80c0502d0441c036240c10070f036420340b035918041455411508000e5000e030243c45101006000807942013036050301a10005008404004400c0c0800300180c40411040701c001c440340e06c808160006000c1c0f41800c50310010400303001c640c400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 72718122 1250 72716872 72716957
    0x50405011d0d0e061b0616020102090a180b12060708060105270a08010e06010815010807030f021f031b0f0e04110c071509060504050f0d02040b040c 65
    0x3480488040c802d0030303c580b035041034500284903802480e0319203040c2e407070f0a541d5885450001c51000c1c41907040c0c2e06051340d5841322600881c00c07401181d504a40021148200f0300c02c0407421101002c407144042d6000c11004807030808134030000c10807c0d003100c03160300290034083e95680111060340e01140a107013442c140a5800d0011080c2a03418082403620780c610543c0034034540b101e00078031016103071913002030044803848444103650304d00902c00e500050040c00d409495070351104250b2812500f10a00070f001d0fa6041d80c58030742029590703483c01c076440780c070f0058000c0c207200007600281d05010317454500007510074a81a20741d00000607245034204200c48080406c04454000700050b04601c0d00350750024145110404441007071064881d825000e224013000050800740c0c0a001d5200c100844ea40c0ea05410ba640c1c5082c1d40e60f000d580500c95011880035402441406c02e0382040310b1190005001040a900305008281100c466091800002e584200703400e0081c212500c0400ea0b820030244201c020524 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 72719372 1250 72718122 72718181
    0x6040b0a05010503090c040c090f050909031c020903070e1515030a0903020a0c03080a020d0e1509041b0905030d08040b0a0b010c0b0c0301030327060f0c0f0605040501 73
    0x3428060141404404030116000b00b6081080d0410810702074410080281c9881c005410000140b0840c1c0240c0201c080102d018201000c010f4000c001d070714011402c5c0301400e0380306815145174007962512540d0a10149082d1380e810043c407001410764030070481c10b83c113011400e09090b4016064071070007241c030240024a00c62000048070390200020380000340340784c01494128107080c04444050001044181e01006028550700140b02016068085842414588500b5980d40c0140f078001584040000360050240d00b00300010702c0c0c0c0000080c13001074a41d03240204442c140c40404402800109842c00501103403c0800002c80c1201180c20b0414113840d140da01c0005c041310080071402266120040080c442e401044285071040d48110600607524100020344190b4000344802e41c001801c81284900c6000d105002041060009d03480c0320300d503400c1c54401e864200c030b88071010b030401c80990701c60000705070b1022032040807904c035000104880c01c05040c501d00b540d04400c040c610080318000419106403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 72720622 1250 72719372 72719389
    0xc150a05010b120c0a1403161e02070302310c020d03020f0913090803010605030a050a0e060403030e03090402070f060515010504170c04050f09010507081612090210020a0b06040b 78
    0xf5209000b481e0340b0b00e008102150345046c081ca0980009001209110341c2c4540c2ca424012542000d40d02d20604c400718111001d0108405048000540c0001d9014000340c142164a01c551507480d014a628105403501441810280c10340803001c03103503858484860895050110300309045062a056090403540175a17038105100c0d085000e40b1a200640b0410842569a00712040141d0001d00943d02c03981e592901a040358021642442c01e00c1c5098000380d5240303814400c40341341081090090516036101e45c0c0580090605c110599001c0c4003d00500000b0b50701e0340000c00d442c900c64001c88030f05801c940b603c60300782c84020706500340f11b5900301071520141c0da07c1415107040700c01401040031b202455103482428140ea6501098015013494100038405688580e1b19000d042d050008219541d40c0e40d00441c0c801d18203580000140706081001c4400510036203040000c5400b0440c00150404c171540002c0c003242c800303510b4030050b800c00d02c485800e01103040240760380114203940178405180c07403000244114 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 72721872 1250 72720622 72720631
    0x1a0609090d051c06080706080106090e010303080429090d120c020a0305070c031a010e070903020306151c0302070807080105041e030e0406081006090e0c12030c150a05010b12 76
    0x18940c14850180b502c2550708074400030f105c25400d0b59201502e62100800d209800d00940011a2191074000f50001481e4241412203425076070790a0305484d580e6500c4480c0e80c100e0310780382e800300d910030040307040c20f1800a40c0c0b4050880000284055802c050000c0c10b040510314101641c40e00c0c1501b0940c0d41a00800c2d40f10a0700c2c3d051504580c1c030301192519503c5d01c2c4042e080030b0304200d40c00401d408501643e109881c16204068144982561000c6049a81170030354040203405030080404981d0400300d414080b508080c0042100503c1c0220003810540d00d02d0403030003035005a20103102080007070340903c03e050140000800a1000f807600d62074060754098070705003c0a400010b0b101c580709041c4161110b001814004105000542c0d85151084d030320340c81208022441231509100044510503842400001d1aa54001d802d0b064081410442c1d445c0c800d810408660100300101542c24030306104500b49500c0705005a1040d080681d007200841314160031914000c601003040d90010840507840c90b500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 72723122 1250 72721872 72721897
    0x70b010302010c02010c1a0109060b0712050f070506090102090a06140f0711060c0a0201030b030a0b0f04061e020406140301030320010b0a0b03010503160f030312091a0609090d05 78
    0xb0840c07520040300c02020046c400340c2908840e42c10517100149000c012812140388120511003943c94035800c04d5948240034006100082030424410700e5400707034016021003c60051034500382103160320380e281001c8003122448410b03503000442800314070342006048040e05003890030901c001942400d524140c483c00c214a10819004201003041041c0d201c864951010054441610b4411041d0300559a05c1c640104901003401d06510721564100055001001d07070300705154403e40d40300c005240b100010060300980d45240c13503180109808640c6080840c28100c8c0a00060389c0c3e0380340c080f000f00013030009030b1924420f880c10001000480d5004a00508070602e4101c446482400340b0405401407811103205c98002101c8580042c5000b000b0020350304980064041d505d032032800325150740d00b0036000d001e00d5080c6489542c0502c0031031704c0fa140c8003055840c142e0000803605055110607503400c0901001d01c0e020b0204604001d00d900700b8041e1580c10001080041466403c018405891070040603c110030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 72724372 1250 72723122 72723137
    0x2060406050c01061d100e09030a050915032703030402010507020f18100f05060a0f050d0f06030b04061b08060d03050f030a0203061509010804110d0203070b190203070b01030201 78
    0x294800e40c00302c0d0080ca0b451803542048054440c003c005c964040310a044012032804001075aa5031369522184100d80c05400f940c50040400019145500400744194004044513040210506104010340c0201c1c4a0705c0c1e1040792403c0c44050250007101d103082c40c40e00c1d4005005000050740c0103030a40d0359042e412200074010103c020041081c840c82281c1000095503945d00b48114400c0c45071280042d1150142d510700f0003a00d0b0001d010291040c0e107540380014a004001c1540130b40314501a00e02c1002001d8007107100000c4c0114203058a815400c103941e0b0030361203002d01c002c100c054401c0420700c3c1c1c3c0140300c06404600d4008064041c2d41c0040c0081d028035010589601054414004c545d5840f074950000781e140e0508041a030001e410849000b40519542080036903808510001d682c0c0c5894141d45039180e550300c503629040210744091042d0b4000090a29000040ea014800c4401500c0e5000c0396a84888404400010ba203030701030018000d40d08200300900100300c0c243d030001d0641e0f40a090000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 72725622 1250 72724372 72724387
    0x20d120506061606050a0b03010b06090d170703090905070819020f070b0c030601140f0304110d060f0509060c0c06010306020309030c0a03080403090f08060a05060a051503040b0a06030206040605 85
    0x24502c1c07140f000e0f5981400c10020060003040300a42c4118091001c0002c2044031b400c41d04241402c8801140401c0d030700c01e405000340d8200d4a801341c0c1040780c461040c0c0780000c070702c0c180c0721315210710b9007080b03104801080c401c3c102408040307524421554019081d24001050b820310700d030860645510140c101c2c00c110f030001058034a4503000780440f14991b620120503585440e1040030102c4940017503800d14005030540c142d1700b01e5a080b00c0f05441403e1070460f044d80c07954546030394450700381500080603078201280c2d81211b40400d0aa104001040c110780d507000c80c4c0361421200c0a03091000051211017607040502c400c0711740100026909064a41c4031f03200594a40b80c2c00303075080c0365009810f00c0b2130081c410041828101503000c144580100d21940b20b10300416294200c00c01103a11320702a141040e8880300000f031503104245c215680105010b014602050b40314004103e660350040058150180000240000c1003d03000000f0340c8401060300c10485c00b411a030004d115882548508010030201140d0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 72726872 1250 72725622 72725629
    0x2010c0309181406060f160221011d0105130209100909080403060c0503070503130309030b07020106080705030c032d031204060b04062105030c010606110d020d120506 73
    0x30000e0010301e0607544002d60021140b00140a9a030404400c40c5030f80c1000c039015042240c03d98403000c2e0b140c410340c0d0030f0000000348081481c60030203090364088404042c940118141e03864001440d94150004203086040309102c0c000c0c4d551010f008000c9a141504000b05050103076150440c0b554105e031310000703a8030740702a8103256601ca0b0f00840483c034500400d010410891000134011203100d60401e019000c10b00788151b650780001c4402502040c010000158140409154164924400d00f0441265501c80c2c40e45804003404841580142c1e5440d90180540c000420112006280c120010413220000030080380c0c46440756101c09082203500140c000384201e01d58040c50300c2c40b0f90718040360f40319104010315003001c50090390184c602c02e2510006410b181818020f44050b11000c02030401054545050403080025005c01614140070910a000c840d038020701400006040a82e80c281038100b00b58055810b00800305c20745000c1d5442008030540710798010008041c01c289182001900781d4800000c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 72728122 1250 72726872 72726887
    0x20d0f170106020a0203070e0c1207030f0f0203010812091509030a2a0506070b0402060a030e03040305011b020d0801060507061b020703200904060c0c0f0503030417090d02010c03 78
    0x40c0000582010012400c95030028101c11514021001c071014079541e07041c0c09840d1441541d01d1100354004105031800074005688103500140c0c82c0c503000644000924228045585031100c01813030340e800100400500074108941000820002e80306450407e416000410401005010642107400820078052507a8140005200742d90006400c00640c0d0040301d414400114104160356440714800d40421142804429240d006d94405a0190107440f19001c0041e103811100c0740c2030802d500e800700c42e91214014400f03040110b2103a0000316468506802150300180c840540404541c081d49648a855500c00c0480f03046500720705210740e461600d410300102030710120110040c0c0e01c2c0c01c0c01650106a80c0000c910007140e02802c54408001206144a100d150180e2501c43e03000000e031000c02d0200300304c0d50015008403080c3c2810300022103546e0f82c2d02c1c08544c4a401c00e841c00d8001104010500040a070303107503040912400014079100c69000010322050b200000070341042a681075103010540074618 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 72729372 1250 72728122 72728147
    0x20c040e0118050102070c0b03090a2d150b0913140c0d030203032e050411120c0408060c070f0305031f0f0501031a03121c0501230d03020d0f 62
    0xb4502d4600501d0706095005c0c2d03100c5002100c16000c3c10300c0000d1034085642c1500d000c0c4031210b0203441c01030003948941804480c100d98030307000c60722407821407940001150f04400c44103105002c00c0050001c503407107040032100300700303011030044041004220728459603840381c0e0b4030306920181e0080100c1c1818510307403070034a00400d2036821002c0691400180364000000d9072103180424001c1c005801e0b002e42c10107003807428043c6c40140101e0407a00b40518613080d0003054100c03210640c1c0c1800c05490a4042c80e10100945070f105050700002424007103c2030034080164802a071250182c43c10000395a0900103000040c0c002c3e080100200200d0520350080b4800000a542c20011031152034a500700030080b0000c41c411680402c0ca00b00c411250341c01010300c000361300b030401406000c0e0080d0342c01d00800103a106072908200f221103d071a04269407040c1c4107103400382c944601e00252031070120600c404000070108520b885001183c11108c001f9500180d008034035121403500100c03090480c0c4050341e44001d2800c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 72730622 1250 72729372 72729401
    0x305100626010e010f050103061803140a180608191b0c02060903010905011506180512070902030703062d061404170a03020d050a0206010303180503010218040b030706020c040e01 78
    0x504884900041b9042a4183c5e80201010000441d0010405420809520005020030102c81105403103d01c004041c007060f800c50300305a045900d04400d281003021650300018040b640f4001400a080301c0e019002001055152040299442421220011030b000124200800c42c60450080441d21004181d1301800006030003842040290b1620b40d000e07140300c0034001c580308518100018140d210b00861406100000c10119656003814188501020500805075080c4078520340001c0074030142c0300652146c0700a60380001c4840c240005140c20210401d681d03c030f408010320100c1032040b05000b85a003200e2060528181000046100342c45e1030086911148595861440c0300c00c0d103810115030749441034400d60030b40303102c5c01c3e4207902613030103000d0011040700690020005000080c05448410102200311221030192542c40c00000e00f07992140c120441d282c803501c1008407240c1403d01520712410011030103090040c0c00c1032402540c0ba10901500782c416a140d440c0000006800e50162003180e80c0c29 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 72731872 1250 72730622 72730631
    0x50907140c06090d030c09050909030909010602010b041b080703050a0b0607061b0807020d080402030a200301110307020a02151204050d11060609070309170406090305100626010e01 79
    0x1000440e00c6210843e1440002e020310700300d2882c02446403103020203000042c4c860000e0141403106110380e03084001c0040c00c082c4020031081650303680e082001d90003000c0070742c00498030030403400c207103c1030b54a0750000214a607e00d52940001c282c12148641d440855071400040554070070440c217002d007075034051701600003800040c42d0f000c2c05020382000f065000c8000c1010704482c0c5511007111501012503415006801001c2c5000080748948d2402d03401a000030110b550280c2107403503a2101010401008064800c0000090340b82e05080c09448800c1180030382e2103055203048403001c0c1d00c07414800f10080c4910600c0e1074890b842400c00c0d0a0398450a280c48000e0028a81407400d150354401d500203150100d05078509005084800191003482032002078890b1985480700320080e0045c200141c01100d8258002ca084080e4241c40701c080c00041c11643e882280c41480c6080003030030b1a071920494145070341400800c0c00800b40c40b14103010100350341070f1549c1d080f6115000d064018802d000c0d000c0015401c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 72733122 1250 72731872 72731887
    0x100c081b0a141303030201060f03170d020c030a0305090609070f1401120c030203010609080c010504030b06032407110f03071118011202040b030303090a11040b09011d090a0c05090714 80
    0x143c450b0768160780c403030340080080580ba000c4052007000c0f01d1100500b0707190342d4a25034080d1102c0102600729420215409801c100c012080079085410403030510000070b90310000c000c01442d08202f503a41060092015220307660130f0161030a000c261a00a54012484003902c41000384d2040c0c850390005945281d00304107150440d80700034081d52080c803802c0d0008074041004a055400400d240180c240141c4520b03181c103281d995103030380c41c03940107005a905005d00c014040c1400124501842c140710008007014681c41c1421003d007405a10840304c0000b81d10140028190386800400c0704d80c1107801c40240035151000b40c0c00150282c414003100c105400c503041c0002070402d1103102c11107419100300d07420f100c003240c80002c0c1540c0f070008984030111503001c0b0b0f115801050f40140300000c00580600301003880c1c030303407413000c03801c0400280d102076100d0002c0020702100100310402140c0061360300014141400e17403505d1710b800000040c0103562140b07144102244e5810700501360180d070040f400c0704060700c0d8500d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 72734372 1250 72733122 72733147
    0x403020409151521080408061005090a0606020703080f0403050f0708010b01030902030307110616080706060e0103020d03050c0705090a0c091415090f12100c081b0a14 73
    0x3014181111058100488503920030710118101040e164040b4240b07514028140301001c01841d010410359200700101301c0440c5070387c0c0034810584245006c000b1540d555140c0014015080d0008080042c80d5180c558140082680400e4010850390015400d43e207981c24500da0718030314825580000c286104074400c0c1301c035502021907030750111000b40e0003c00000e01c01c030f0010b40c1680e2000f140294141c1041042000141c2c015501d850702c506c010b0406414462901c1c081c10102e403941e00280c8900001081940c10090a4054240a01400c40d40030916501d560701140c846014100004c007841004201c507040d180040219800801e002400341555061071100d10004015203480300d40018441c074008900c6070111a40e40f9440c0c0e901034400c40d11900d48407800e03031540d009441c0580d409120403000d030280703a079000e00c9402114012005001009100c8540c7e504452041b4208000c3c000002c08000440f1784442412b200c004494100b10740c5d580c02e001c0100d640300e010000800f045580420803021a02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 72735622 1250 72734372 72734393
    0x180d0602191d0303040e010e090f0304060207030c1406040e130f0327051e03010207060f150602010c020307020d03020a05060115180b07021c06020301080c0a0501030c12050c0403020409 81
    0x1144605515000c002e42424503850b88603030701032001c5c1d03888808010000100b041c00d00b80d91100074101038030308465010360503c0c2103078820380c080401644544c0041c1300344018902010700034106214012201d003101e0001ca000c2c0e000b503104468000c1c40080009825007070100d0760141c01035202008418003a11454080e02100307016144090506494068482490350805505e080e03410051030940b203108440d49c600d5a030b4490f1003a00c0d8043d5028010280000d0050081000c2c50003007101c00300741143e008038450b0b44000164886001c40e81001c002c1c00d5007503000300450701b0460f0191207121020001e81030071380c6411003c0400512038800d81c0000110391b03038501c0c16122001c4c075660b151004440040b85400e000c0d0b5075030055201592040011900501d0125109010040202008030144005480d003004030b070001d0b8041e0703402c0d0704000e08200c1680b03070010044004d04004d082c20003040c3c05800d001056540d03020154a4080d95503004151444110801c2e04c00541d4010010301c64581310389458407440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 72736872 1250 72735622 72735647
    0x63402070608070c03090509060307090f1b05030c220503030c010c1d13020c011107050102041d0f06090703180602040515310909140d05180d060219 65
    0x26807004080f80483c2c1c440e202e03003400550140c2d00c002c800f84c113150810070f86036005800c80b58140b20308500060750b0001401203403804040e460300043d219041c804844241188142c0220800c40f080040107490364540c0b06845804c511542c420140c1c600c60603010312101000e401c43c40c0d00d4031021483c4820a01c0c1500150103039031169885103180814244c40041115281005035403018101d101c3d40c10509460307020301003000000c000882c40c001c51903e5145d480d4040e12054070140d400141c18000300380e90080840c0155a0310b000680c40d07190a011035070401c000a803000e44285084d00109150034800c0e0411009410020041000d040452a1900080d407251040600030b8170036403d6000018420000e503268031580c103124081030039483c41d1400200e0a181e44000b0f07010b081d01c10200d454245480382d02030046c421004260100c5c5000126443c041ca00f04061041040401c0740320095900300448801f07403401a2410040c807280c5150141c080d016280c15507045a15901e009071865900c0011140b10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 72738122 1250 72736872 72736877
    0xe01020d0e030a0e06030a02070b13062906090111030409090b060d02010c0f0507030c06050301061e02190f1403070b010b070506070c2303091201020c0634020706 71
    0x110740808140d035164080c20b00c101000c501d00181650707050400800541d44500c0c6e810006241c000c0716540c207100799900380c030b010711085100010f010800109104081c0c00e02040d51750540b12164084c40406c8084c41006100d010b110041344141c4141d0040700822004155034007030707a44440c1c490450000400f65401c0c182c030410b828001040050900c90189400d494041c0d40d080040e40050310360050301071120318112114483e02200101103490100b05002604080d599280d803540b42c40c1c03000f00254007403060144041e01220888450039000190181400110260b070308204019050402c40c0c50307080390000d40714011030303480d0038400c004c04001060800e104030144221a600c40110b0b94042c041e80c00000c00307560000f008070b48424004c183c44018548114581d10b40310759401c001c0500380c0310b5000844d070b0551004c502801c1d649025003008114046a000071401c010145820703543d901400740c03a41c901a460142d00c070040702880042a01c00000ea4075115180181c03000000b5070320f10f0f85c1c0c800d6000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 72739372 1250 72738122 72738131
    0xc0a020d05090607030c0c0905010305011b180e0702030f0f071412090409060207020310090204061d040b0606070503040f060206100e0f091606110c04050705041401030207060e01020d 80
    0x24003038040c5080d038400030405800281000b00c1560143d41207081d5680a0360b03c0c100400c000100350700d50740540d90295124800128942100d0076416440c5a9048102000e0005c0345120038052000012104e046030280540c078440340d00d440c00203074114459186044180000040c8080c89543c4880040041c1d03482900540d00c400f0140c0c000316101c01c0c0c0a000d106020504006068191600e80c006050440c024480189020400e600007483c16100a8049120a1b2201554015882e0501c1540000c00d101c0c0c1c8441108002014002c94480006200801c001c4921020900e02e49581c02915800781d030050489030765a8880d003410300104401d204007401480303103600282200c0ca46110b91022610030a42d2121107440340883c90758180340c000d105402070301c5503481c110500d04652200c40700a208a03161504080d03081c001030381c1402011041503000d28109420711528aa200707044900f1907018440b003040002040004a011707114121001e00258144a840b80c0180f034103500422000740922810003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 72740622 1250 72739372 72739393
    0xa0813090506010504031403131805010801020903120d0605030706120f0b0a030b07030b06041415090d030c030c0f060501170a0201080a020a050d0603030c050f06040c05010e06120c0a02 81
    0x4058400072100e143c0050000d000400c00189400607182e03603090900260381c2480e260341b00311034820409511003c441d0b05196050754080c90780344200c03409443e165000f03610b0a0780100100780d8030072400c1c00c1913002c460000b403840007001350741c0e01c043c1c0030346801015110010707a0360700001c01440c586800201550b00c0d20000e45205a001d00c26940b459001134000e0340040d2858440201244000f04800706041c0ca521072404507646040042c005801c2304c1c0c0c03103803050000480502202c400c060f000010b0040c4108017644083d1380c0c05141c0e0544c583d2514005044042030b1030211070f02e00304420018031290707082ca5280c0400409410a034160b954419104a80b450900025540c5150000001c1d01160b05400450034003801500203050446590030041e113008030310121102240d40030b900c2a0005400d2140000c100001070014810786140d120080045003403503111070010300010310915040c000d1042450740c180d01d4040030b90310fa801000329004c01034074002080c1c00d100d41c4646200300050080510300c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 72741872 1250 72740622 72740639
    0xb100207050a09020703030b030109030201060f06080c120c0d0905060703110307120b031e0a170304080306060901030f0c0207080d051c05060d080a0210050a02090d060903030209030a0813 82
    0x10200c480040c5140415440c10700410000d43c000c00e0180d08041e120403001c0c069271024064401070f94030942c000110185001c5842490551980000b010007540301e050013090741496095901821503c2c07100f42d01030300c0b490151110741c0701d100c8401c02c540f402c2000d1030052040200d803444c41aa41502e0070b010080440c65440f0039840229641c0021519110101030002001e078018540000701408540704e45032040400b07520340e083e211220949a0040c030752541004415040c05803041030100c159411400c060362003014502004100e80e016120100d4894070320703842074101440d00032102504010805a030f41c0000c0d1038030040c0c0034040c0b8500c10380c0c540600e490f1041084a41e0000300384442d030700840310b450a540c0504409800d0a60001c01040800042000d02e8010400c0160310340040003081c1840340b00100b031781d400908800721a441401422080e443c1d010042409550004000444e0192440c0950090041821058051158464000c1009641001080c0d080312061080300803950303d0441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 72743122 1250 72741872 72741883
    0xc02090606120708093d0b28170114071407110a030605070f020f0a0803040605041704081b0402041202100309050d0528051b01060f0305010b1002 64
    0x1440c001c2e0300840000340e980da1042c0c3d440382e00240340c40f0540c0d0b0144009400e0800c000e0311102000103070014130306242180854545004c01088103580280012040000054440c0d45640d1501104100b0072911035086440c00c0518006000c4001c90039980001d0166110b0092004900100035001500081165107010f100c01c2d4001410580d0014505201035881211041c4440c8000c1d030480a040004800110140510ba100300507030b07584d0b40d80310008a0402460088084802d100b00e812015a000c04950568120f036400740d04480c0c0450261118900003241c00c007807480c10100a00c0c0410040740c8070b040414060205c078841242914002041c1d010131040340b065104401035030240f00c00c0c6400605150507440550b10050500240043e007070b403103043c14070304c181d480f0400003040000c07216418142e0b8000960744040c60501400144254000a0301c0c6100f4040b031030700c013002524030701140580250404405480c0840d03c0110032603481c6011806010011b10f030511038410452200c4610380300144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 72744372 1250 72743122 72743137
    0x1709070b0301050607020102030c0f0307021503192703020106050a0603110306010e15030f010e0109020c070b25050105040308060303070b0c030606090d03020a1511030103060f0207020a060c02090606 87
    0x10607265918180421600d0341c41001c003203040d4042405661007800051050000c0019400e0245988042e140f04000c8480410322000c048c200040c4103100c3c40502c41d188041d030116101c6000140d00700c0e109070b00c02e25041c202c0c85029640000c0c0c00020201507041d0003c07800c42e502955070034111a01d840041c3d0640305e40c0050003906180a200103101036100d1000414100000307080e080c918690500c00201742c2d407084a0f21200d03650f111004018041001403020300400c0009021400c20b0110f021036601c0713652030300c2114031f02d80c40440d4040010140c000c604030000d440c0d41e042c0710341c1d001525102e0302a2008881c15408204401c000580c0e9003404012519800d504c440d505086030344003e6003090641014048a412000501c140ea5175a2030701e441d86080d042c040c0d0010058000b6610b080004652442040001c032030030306d1b030340c3c0dd4507110350003d50741529800600890710403a49030040000340500c1c50040d520410002c8000782c51f98029080c1c00c025802598050b007280c0e00c40701031041a224808 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 72745622 1250 72744372 72744389
    0xe01060b2104030306052d01140306091b120604060504090506010b13030f0f060b0604060e090c0f040e011e051309020d022214010803160302030c01050403170907 71
    0x1c041c0840d00d5a11032955031180c40382c18001000c1c0c2d01c81d070100e0315000030112641407a001c8206030740b401e5032138400304e10852102444d100080c070500c21540b071032900024200e280036000c8400030407541510700038a808142c091003590340c0c40310701c490a1420804030596090b8010b070710b8031b000402c045c00c080c080c80784079a4000c402840c2c0c2d41d1030a080c0d1700e8a544030810b0a04c8801200030048009000140000c00c0e00b4020100c141c41d1040c3d6082000c1140ca0281076148150701c100400c1040075080089559210707803c55007400507580f04464000c1500c00c0c0d6828202030318000401080401148000c1e6040e10303107603541320182400c10424a104a5024000d9030340c825103051401c8603405503038000f59501c51014146064042d02540812160103203802c002d0140302c840d108102c025101c61103100668140481940202c1d45400d00032900c078427455810340072805910001c0c106040c020012141c030384603030200801c10340c545810014101c50201c401034420000c0e5802203042d82000056020a03580c410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 72746872 1250 72745622 72745657
    0x150815010308031503030f090f04051909030c06061203020f0f03030a0203130605040302071403031e0c070e09070e0708090705011b020306040b09010c050301061e031e0e01060b 77
    0x6448203035a60704010400030310001e80d03c000c013100380c0303052000c0d00f41c2581d08502a5140c80b517010402c40c040220100190280c0e14040c01c0002c0190307800361031403114403503403070001d101403540c00c00300d070081e50003c0050549410b148001881012294441c5421406607007a14141200d00c1010358039013030283c02601c0c95034024000709a40c135402d82e0046401540405c2d1008501c0c078160340b03001c00c0d580c084800380e0160f00408401c102e18440070045500300c0c441200514a80200300501a1046500c55200440d4036004107610854060400003007000e0645c9015000591a11264140d03440b40c03203028440c106010400400d841901991500b40500d1046010b84010b03800d007401101c06c0d6041e03907400d01c1140000c0c103c01d00581c03024020320380600d0081410089600d4140110f81c25140714503158010060204010000709030b00150381c01003d4001d115030b84184503403120450207040c030380417040051021006120420a100d41c40300c812003900200034000300d5a00c0c601c0c560140140d5095006c0c42120303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 72748122 1250 72746872 72746879
    0x403020108070527040f0207080d020304061d0d120b0102150901021b0c10050a0c0f020a0902040b0a020609060106050901030207140106170f0313030b07030f02030a15081501 76
    0x5000d260752250390703442d0103820400020213603580400d0303010b015612050f078003000d0f0055080170701403e44554800380040d49028429174410009104a1100e0382803241e000c4045010006203412650a0003810700520740a110501c0c027403500e03404e105403d00b0100f08902034004504200780a003440781ea005030050884011020781401d465a001880307200c0c030355802c212013a802151800d59100b43d0400c1d10080030303032003140e5003030100c03c110448a076028410242301d00e03000700e41d0107a8001000307540b084200b80740f81024800300300090042d8004004090010a0105000b804140174101305a02903003120030f1a00d44440d0903442d440b00b03009010002d5410480d8608a501075001008100d11a40c00c03030000c164403210003030840700c0b1504400c00f1600c0d40801003030701d05c03010400280c6260150010710b01d4414481d010b850815040d11000704807101070400281d0541c007070340c8088545480b40e03409565034038010400000420100c0040951244160800b0a12400005041700d0540b90401c030030501d40d00307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 72749372 1250 72748122 72748127
    0x61d01030e01090506073c0c050f1507030f05010e06060901120c020616020c0a05010f0e040501030c0503010f02040803070609020307080703060203010608010816090c0314010803040807050d0804030201 88
    0x2005001010070b64a8860800c0061020040c1c1d038490b41c015656a291207501d03100024400c1c2950340d40c0303800341440c0b18080c6050000c045100c00e620f10617050050580d20303140340140c00d10002101024980c041d41e406403800c2c6008400c1c81d44160100e17a000c0040390380c8003950703e0440304280140e40310380d0303079050021705030341412402410015014101040741c0700302042d200d020317a088100f6800050300410103101181c0c9403c92500e040c0c04aa0020740b00d83d00000b004216030b140c01d8403d031410031a142e1107005059005503010002001d0180003440781c0d41e12802c0200960f030035441040e029608e0519125078502091080d103041d0b500c40000795113410015150700010b4040d540c816079241c024143d0014040804201d0784005520601c005600d962600001601ca49416031006026811206400e80c0d06c0d0361007004581035800b20800003c049070460000c40050004038442513980c11041d002058400700000684112051042214285502c900034403000e0b03c060b101c0102030107414003043c8015030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 72750622 1250 72749372 72749381
    0x308030a0f06120b060319030516060e0601050111072105070510030f0f051e0a020417011a0301021303110402070b0a09030f0f02070608190e06010807061d0103 70
    0x140800c1000c54101c01141088086811075408522000d40a83e8480200545800c109900080403405451410840d144000c44461b400c20300a00f0400001030350300b110300203040c2109640d908000204400c04400000c6561980280200c60119510400802c81c0003130000741001035824004108142c40d0100d1000c01ea0100318400c1100d103030250300c102065586500468221032001e958020515100004801c0201c1e81801c40500c5210b003400108402d02801c0008103908a42c002681302ca603513111600e2030000d0149810030701041d80302d2480c2d0b403085001500300c0c00030114060380e0401c004c3c03a40402c0600701e202e000350642140780d1803042040494002d800800002202070000742c601403440c3d95082c85480c040710400c060b9541d80c803100f41410b51005548911461500705680f00c1d00300150080e41d0f07054144101400c01c6003c800080201904c4503180c1c1400e09014003e001e618442002140c81c2c4c41c00340a034142034401e841000400c0351041c0710150b0007582c0c07034101c003080c400b0303207001113000d070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 72751872 1250 72750622 72750631
    0x40309080706021f0204090213060306090603021f0e09090c09011d060607080d0207030302071104140c090406050628030207210302070c0e0a06081b1002160303030501060e0303070507030803 83
    0x4d03542030000284403107141c002084c40001f074031080c280c09401e00c4009411160242c2144446504c0c045c410700058554110030006910030070b80014199010741c2048500741500000140c00000d83c0c010f03c0b0881100089178500f00004403002110f50780c0b11200503103601040b03294941e890844c0804200181002402001d100c1d01820040740303808114411030b82a03a0000300200d0003c0e5001442c7e90038130000c0a047c0c1140c2c28215000c0c0600c140303003040e9068820010348020f000c01c40000f00e440165a070b03580b1280040c200508009e85844020072000038a9081e0701590070241102c4100802140c07003442100c000d01d0b4800c01c0c1c0c0050924000d0780315030890381020500245a03081110a000c03900c03988510000b0300640382d2011305803078107a4204060b40e82a501a64107a03010f500104040340c0289201400f8201c19a90110112540e42c0100e18242c04511194048070100401105050b4143c0040d416190240c03104070100280105056617403085200181250b00100c0f41440040d0800c40115001f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 72753122 1250 72751872 72751933
    0x6010302150d050c2503080103060b03010e0a1202160806070f0908012a050f07080304020a0302060703110712020303032403010e06090c01030b03030304030509130504060504030908070602 82
    0xb01000d1030942021a1426a600091603001280096002500c000400401e4034010710070000c0210668000e401100d040c00020046502c6500052040e14258400000c80400d11f00b2a401c5403500d0501e051710340d40d0300c070030700c001405040c0282d2000250402c41c2c000b2192000c0003020142d5071103900329100401d1060200800046039030001c1c0c00301e0700740501c84c87c0003078507210b06181c7c40000100d810a00e909458080901c04140000b2984108102c03d5401254000c00d0660356070b82c0e94070000f4088402e54000070f50016021881c00d0501d9032003004050352a5001049a1500d0b4403001d2841c01c060724400e0081d0300d03900820010b00c002c410a10808005a0203590400b8804c000400081c2900d000c4001c80000f40d121310100302c211481001641c401130340a003010081c0224250100740c90f0300c0001c002034148070000851010700d4a4040134051b04d1904a00c0400450906203040345c0944030556003a0005211030101190003070005c203200c02155025002000c0040d054417410b9410480448410003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 72754372 1250 72753122 72753127
    0x2150415050103030e090121020d050307020d0b0a0609020702220b0a090c03050c0a0e010f05040306150608070f020304120512030f101403070e0a091202010501081e0601030215 77
    0x100310245025a5000c0c1d4400d455203014411100305100032500161720061640e02074003c99402181c540e00307400da080d60156074105040c012400c110385103104a02000b500b00784150f254a0a20410707114076406416400c10034441c8640d91001d06044c1d0041c030001030350020809500388030071206180046402c26003520007042822251001550000441c2e00a03190319403619003041c00103078544a065030062420f0b4074a41004c04085000781a9200000d80038184072415030310403042e030300501c103580056512640c00d2050207954a00d810b1300340424480c0c000401c40f85c10225021a000780e45544001525900440c101480e1480400110b4003010091714180152410b1545140c1080c00451068500d1840d1403030b10f061188000090120503800b081d44007802e601e030322013169404141c40044441046c98000640c86c3e00010500804801e400106902c0e04400700c22202d039019041a4120340503401590501e40c1841352803060402824048180c40e0031241c018801854400b8540b0346a1081554160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 72755622 1250 72754372 72754403
    0xe0303070e0f150d0c080c04050103020a1103160b060105120a05181911010804080a081504090303091b0803040306020a03110d06033809010e03160204061203021504 72
    0x11180c3c58200801c0548620010b00804c100c03440c2d00542090090928042c141840d00d6860410341e4081c074012a8101600007403400c8509200b1a0080c00300c01d03120080d20f17a1001d08150f140000c1041c04021035803504104000f910302c1d03000700140c0d11601d415403c04000c55554100c0e49005210080003405100c02000a80c000e4010405ca2107000302e410180180c40314980d4148007200066440f07041f810000103030204030018070300f4026140020150304021442da03cac3c4408402e0462a01d40140b45c000d071801413403134203166068104008082c023612102c400a040302c4064005a0510700a0380f0301548100000c01c00285103500a0040d00444c4c60700203504d03150001c48031295400030080c005034580b80c0106000b8018180c460500210303038100b02408088410040501c2c080e40c07107206c21006513007480020312842080d00035860740740404090300d6072061880d07c034031020789016509030f000e1850900045410241c0388410450590144c004107002c03a5007646020f15150024021281c0e01c03071074041c40c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 72756872 1250 72755622 72755629
    0xf031f08070609050310090f141504030c0c0611150408040f08060a05091c18241e050405091302090f041e1e050304081c020d030e0303070e0f 62
    0x900030b41020303940c481403145800c1c209881c000b0800c00e41d03144145480e0034400010780d00f00d01c80d820940e01071500c0005006a50b0703c00d082c013980a01000c110107250301040308055000c00c680b0302c0f881c0724030b81d038002907611180101c400c500d40484e500c10503400226000b81d80d40451025981c060300c84d540f00c0b4906038448040703800e041410780c421899580500c0500017403076040d010b00769010031900000c3c00d09081400c07080341d990245d200c4200511425007003003038011042241e05009007550b0f12484a8140303899070007000e008025145200025101c0c2d90324500c8040903156075101503160765606003800d060104110030703820003030024111412202d0408005071120680c0611410810420035030034a0f02e41814645c55903c69244181100307407829000c0000e0303003040200300660f081d204e0040c00b1304192815078a544941d40200300e003440b07895510000310b0141c04a03618168015401e4076165003044070f0543c1920219560361241e03070024000a4040c510903140d5a41980300100400f1403240030f1000f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 72758122 1250 72756872 72756883
    0xc03010b1b0313150f0504051509090708160206010510050a0c0f03030507141c110903030c0c10051206090402011205040302060402270a050c071a09060c0f031f08 71
    0x40d4144407220712010058140e04440f044d0b070a4420303007040b04180c01520f10060952046015003842400b00984000350140000c09903007031105e0290a035503ca080995001d42000701c21240080d0000310602c108400f2880810041e04a074806014065100c000b4081a9540e03004450880c082103013441c82900800c1d051700400ca8800d000780c034001514148100e008141c2040c0c49903180d915581002503001ea1070f01664221010305040a0029180300c815600343c100d4814084225072601c004160007440d2000854407004c80355048078040301c0c075031019005503154003404441405c03042c010b0f0005441c509043c0041d43e48a48149064047e020b5840300c100d00b140c006840640040e40810b00700021030400450104a5592021001c000301c1800e0b024040100c1006140d1580707251114003180310301e05008190788505502180031040041286507005c1d0707410f412184041184510804119039600788000c486401b203c1c00500da14540d104080f642d840b00a20b0b41c0049038000c40a8000380d0030700c00340701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 72759372 1250 72758122 72758137
    0xf0f1f020f060c0c07060c030e010e0303040b040b12060405040c060c020d0b0c121f05040906020412050321010510050304030c05030f090102010f05010e0403080c070222050a050c03010b1b03 83
    0x5552507111303001089103040d070550031800c1402210541c17100466000052001209001d103001c1e12038010030030110b4198000d90784100c2c4030300c4d0041008654101c0c01c0c0084e01c05a03681103240c0d007a5981f44001c010944600b61005045201c0d0420709020f20b91180b0702c43d04000d030002d8160300e0400d481d907131211200e80f801c80c0c18024000d0003142c002c0d00401c0781c88602d83c02c02004100500c00c6901d20561500550f070034444c40388503580d03400c494020410300b60103032001084bc24080740101101d038181039032603070b103c0340056524503032003041402c40300c00210301e982c143d410190600d001c0741c4840d0019109a48090429800e001d01a100e9a000810400091140c80c01c100300050701c454000001a00f541d12200000c05010305202c0140700c200352201095a020790140f4100d6406d0300d480104880d030b84101103020b90001140c001030000407044e50100064010f10781820405681e5110130078084034426140304951201c10001000886016006410032060743c080a140408070950010301c0c42d80050b2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 72760622 1250 72759372 72759391
    0x30708241009150e0306150a0f060203221203050c010b030604110a0b03040b27010905070f140a060e0102070f08060708090718090f051009020f0f1f020f06 68
    0x40003842910502c0030303010642249810002c42e5041c03c5000a86c4448005000e00c0809070035540c07940071541e4850b1400c00405003151407403580d60b00c510000352640d210407004090165002c2c60380404c003000040034011106088421114500940d40488640e0b000c0403040d44190349900c800840c4e540e00703012050150380300700721000030301607403800b8000030810a03441030b0200c4e5020300400c40400c150801e00c0f43d00410101e9280c0e05880283e1074801b482d5400c560f101581e40c0303040d03594030406c07800082007000da0f00907604103a401940c80218020071071019000e41c6d00f06044d0b02082003054001d0f190b1400003001401512400c98849011078000c0b036103544a855107600001c1440b049582001c03055802061a102511105081600c165146400e401c1420ba50079542c2140c6070600050500a00e4415131040c00c1c2c1c0c0140d45244083c0010f000440410f134402c501d00d4007007070044e00d0320170aa1000401d01809c569561480610019001000800f1a80c154084c004c460500450300b4000a40b0422a60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 72761872 1250 72760622 72760637
    0x736090b01020303011203082e210b0624040b030106020c0f01050a030b0a080d09090c080915092103040611040f03030503090f030703050c0f120904020c07080d02100b04020307082410 80
    0x10b50b03500000c054076031010b0046122b00d0082071401c000243d20681c159041c8518030b041d00c9004550300c5800c1540c03054a003000c00c0100e600c031300d40c800445c12261190708580c0402c0754081000358086e00c0c01201808500c0802c4590480c07402600100e20f0030a004090039001036a899809041480840c8070f4400070303078507a07004e2102080794414415003898500e030602443c94140003042d698890000b0340c0c00500d02c5c00c40003c09035401008034465400418480d24002ea0341002c401007550410307a002c54520b410003000800b2582e0f40402e03102150120f0803801d2005103552810340d2540e03c0902994154042d102080e60100005c0000b000820b1199a90650319088007408604050a000c0d20b1205030b002409281001c03c042002c1c0c2c1c031041c404440059444520002d035074541f000607030141d80d150107a0664814215004501c00c130599503061000d025004480c01004200d120880700d440124041401140280598150100f2440000c40e42151480222800901c0f24036401c000b40002070400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 72763122 1250 72761872 72761879
    0x8030c1f02030f010e180102070b0601120e0c040e1908042309010b16050d1e0822020303040b0d06150809060736090b01020303011203082e 61
    0x2030394048025004000303411070860500d6024980003a0040c85102802c010b07440100b84890382c080040b10b4100400d0008640c0d482d640d15001c004140d00316145400f0403842c001500280130742d8058004100003140160540381e2440c4204802469801e010603200d111300031004540340340465403940d000340900382503602e66152001c1303007854201100b4650200c08030031124400a40b11158010306542c3c15a05150b00e074510050000106140a0070180c0107100b10411054001d80044015030186801c010706c41c680d000c107800c252451002916a90480984203144082c42e401c3c402c3c85d035401c9807004090740c0c40c20b0307594682d4014980010300c021008543c1c2d16030402c403c103240c0d0711940000e0740300e05048081e454520301070703500c41400825140a015441c850f1440004107a0348203148100c00c00f1603c110648000c030b050481d01040d0180c0101c0600d800711140d00c640c00003050300d040310040070300a01d440d411a03804585104000d04400d8145910007011500701306503c1091195a0b10345460051641c40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 72764372 1250 72763122 72763153
    0x90204050619150e090f25020316060b06030703060302040e01090203061b0408030c0705011d01020303060111071a09091b0f0a02010b0405041202070905010f12170703051305010e220608030c 83
    0x888400c7c003012004949041101d0039000700075500d0081e00701c81d01c0d45070041d01e41040009010608110ba038062000030030480c05030f40550003602524004c1e80c08018044405283d00e080b03030f0150390702a50652110340001c44441c4800443c07142c0761005421182041e588640040c90b64021110140c080d811184040c4840d50780b01000d111882c005010000c000d001c04030002c1d490b40700180065041142d9030921a89081d070400c2540001d01c5035042c4400c030300825038010075141c0c02c01c0c40007620a044050215920200040703180c0d02c40764030521014a409099452209030b94841000d013029552100c075030300d0300c035540c51007600c0c419400750f0300d0540300000f01c8000078142005904403112007840c1c50014030050381150980d40079150f11b8417206e013000071541000394040700d1410481e60f20580029040d01019407250142c0381d801905005061026240d20056074075000c001c110326048190707031240118041e415480f085d07611107a9040000e04e01c0c0c66103034050440c2c0c040300e00b4414075032128580600b0a407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 72765622 1250 72764372 72764401
    0x3060d08030405210f0f070c0503030313060605240c01090b071707030c050901050903011b0c02120703020f040b0118060801060e0906100f120f090204050619150e090f 73
    0x9500c00d8404c0e29000c030610075088507008803030b460081d816000c55210100044280040050500141281d8480c43c02340712414052840c5042240c28900b070050014640c140322180d407210615002e02100005410303140103085410003285003040790b48031000480803c04044440b0701540c0303a0380c3c9030300310101c4002018141440243c4140201890590900302690348801a00c203a0030007440c02c107a844005400080c0580700b0980d1601154100f10924410907811198008200c0e1090300da144180303681c5143e03a40c07a175800b448003079000417000c41020076600d025401019203100506200d00122140d5017400c00c540e14503000003011500c5800103010a0b034000400c851a847c00301c541c1000307071820001091000d05005812401d01c4414540304480f01d000310510181410201810001841d101180102400d250403059004500c0e101c0495180d0900010070414098071001100e500b40c50481c040962000c40c034001410800b10a184a00d29540c000c2194082d1461315250009410b1811a90301500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 72766872 1250 72765622 72765673
    0xd0f0602070210020a1a100b120601170114040906111204030e030109021f0e09130213090f1b05100305090c0f0307060e0102030409020a0201051506091503060d08030405 74
    0x158817180400c400501c405404c46485100804d00319070755158080d00f910403243d2600705646e22440401d0001202d500001203611810b002d17078521140c109034404e04840220207008030582e15401d94100380990030b090308a03000c00d80c402c0e4000901c6451044a8041a400c0b400190455000c40000c1c0005d040d405900200c0c118001c030002c0103140c540d98001284050241b0a044106810140c180c5205000b4045955450030190900303029240001408000c5045a032007244582c181d2284038040c0c58040c031078121610340c8503403100c1840005440714002c1c1190714808021440f40700402151507190005039130711211454501080a0500440d054106040c00b9038050007001204e01e10012036500003800310031102281884a01d9104440c0102d00b10320854111105241c00010f4039402c0680c1540014330861603000c0540101c0c1e4240c0070004180b107207404507a88030700300480032a9110481030045801100041894070fa40f0f40da9500c4010035001110199229084440c2415614a4204646104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 72768122 1250 72766872 72766877
    0x904170a05090604081e03211305060702030408060a06060906050d09240506030309030607053702060f040312110d14061503071209020d060504050d0914060a0e0d0f0602070210 77
    0xa0808101c07800990000300c0310540742e80f2100401003a0002c22700004500d0580d0010f050f10300c0361030300e0200070b5580da0083c0f003809800e200300b034000380c03040340184200e1081d14042d82d1040c840341e140c401e0845083d008042c001480a13592072203000007a0680c440c0c9524440e4481003555548201c0f81d4480440d00c00401c0d980c000d41003009006180e58000c00c98640c4000340303040854480d168041e028a4112401d2075400d51110100303042e0170107800082e82d040804135a94210f40301c558030b072080b00640317100c241c4004020480400408a010015800410156512540841c00c0ca007170b0103050b0b020317103a0a6076004000c030a40c809114860825403c25400e8600742d010352851800d0a001c0102080089201c02050994400e002401c6546801e41501040c0d000b24007440503040608020303403a000503050b940041241c041c800988036842200e0800701c104020012401d0581d2504207072409001401c0d40c0fa4018021a05440020301080c045200030703018981c010707205c0c1180e10510000c0a1300701150001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 72769372 1250 72768122 72768127
    0x714040806060d0f05030d0207060b0415030803070203250b0601080c0304060207080f0d0e0f0c0307090b0a0b07110306130f0f0206130e040507050904170a05090604081e03 75
    0x104400040042d0014419a0340c0da036007807400d0410307410a11300004010700310300000614542201e10303500074221950050800304401c1a031141040200c5070005220b00018040e20402c00105181d540510b600c4034407801038a1501c000a019031208012070002d60064940c1aa40c113000d0100081056070b2000007800d242d0810b0801001e041c00d140801040205a560001140000c01c526031042d18110601d00c06440d450392490560800504002e0f4100c542a104044041503a1b210018454001000140103000c003141003411300d03006840190f1f101030304a5225400028448a0782c0000e12489000b8525460403420b014105414160041d102e4442c9000416280c03020560a040d2031500981c00004411190340600c0130803214014035428842e4610103004c0000c402803441c0c400c5100b14403e805841000b80c40f10100030500c42c00361405801c504004200207a0b41d6026401005007965905115007051034201c002245903025030040c08198002c502464001c0c1c0d1594004094120345c10041c60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 72770622 1250 72769372 72769379
    0x9180501050904080702030c130b09071409040504060b06030405030a0318030f0809010b0a12150c02030a11070b13050f0406050f040f0b060d1410060215181005071404 73
    0x707191000143c8064403200f80004e00004564082080000c0b890014254140806441394038500400600c19039a00030304800000030441c41c40341000075036960050000380d007007049450034000240030081c07049881503031325a04c007030369a0307034441c083e5104a100700015035448207400300c02401d03104200071518510442250482c0040e07041081c003501c042051402c0c8000f0b0b42c030a01c00c4c5015142d0041659084102e5550110f0401402d40441d00d18500a5050f078070500c070500c0a54080313890300c0f240000140c0007400741485544c40703280085500340a650440b031810f0382320802e004440d4400c00e00c04420f08000070080005041c10310f150460444200c130701b006228503100c0469240781020360340d107200319500d2020400d944c0d255403120203190006015030f62615080003100c401420f9070741d008910850721400141c0f13410301001c0e00c8800e407042035001e0044e54109442c2c00480ea000908041d02c084d645501649040b0810003100001c2080f415020030607040100015000c008030400c0800000c00402c405e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 72771872 1250 72770622 72770629
    0x2030603070f030b07030906181103010c050708040909030203040e0a1a10120203131e03080105060c0a0b06130903020d090906030308010509060d12020709060f080604060908040f03030918050105 85
    0x340d0105040c00d000c40ea150b070b01c0c40c00e2002003801d07161800f801103c0303107221000d00c00e0841d0100610ac80a0b0001c01c0401071310340d01036845020b458401055903408010038401c141003600100c01d01e9200e401101d081903140ca03a064240c100469141001c20356500c039200b548140c0c1c54400d00407040035034002503a202c00d80c400525292800c0740d12205160000041030081000042440050f0f400160a40c11180161040c07149401c40c0042a00058058400820540b524000310350000c0d142c00c000740b43c4100c0c25642c074800318200901035503009114030709154410500b1301036241d0083c03203a4042d000d03400003132001403c0c5500640003000030514103074042c00040c0c1c00c04c40311810743d103044540414a039140340000d51b103003c3c010ba004045110704104441010b400180420958104e40d0081c00343e19250b6617100c1c0007041e41d12680d8610360001c004500400c4084d030003034080c180590101494151142c012141d07001c40d941c405c60000b14000b41c2081204107030404040c482c80044014405540b608000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 72773122 1250 72771872 72771893
    0x100509010f09032f16030507080f19030509151207080907060e0a05030a0c060905030d05030f040c0e0114040f02041a0a02210c0f0c0a06030f091502030603070f03 71
    0x3c0d28260000d003407401106103d44144980c3c0b0520440071100395105c08012116003c85610041b65144036820000c03d00380f03c003040d83c0d0741e0b110081c0c00520300ca4504042414500550f201c040e010702c0780410a032016a06d4401c4101e000900c9808501e40e00c645100c0203081c0b00000411030402c0240c2c4000380944440d0214103002160704030b161504429030004009800d40c00243d001691500c110416201003021109040c42100c0e0303e278a901718401e40d11014140c44411411600000900801c00500551400c08510741c00500403040f58203403a840d01074000b2201d9003a00802d1041804540211780c51610780aa10300701a0071074000d43c103080c81c2c03200110908070142111800c100d000328103100707113601c204907421705064400445401c1c0c43c13900e21464207c0d0301060003042c40e40100c0c00c03081c13441440016403038502070019017002481843c0100440003400400d034900700c02919420110b000c01d400488003079140d0130340f090050341c0741040010940b9180d207903031001071141c02c0170324100f0200312010301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 72774372 1250 72773122 72773147
    0x2010509040b0f19050108010f030b010303120914010209041d07090c0c0606030c050f010807080601050c0f03072003060106080402100e030f100f0605030307080703030608100509010f0903 82
    0x3070128035082c0b000e00203072020003100324954004022003003505813000e541d600c42007103c0080e210f0b48140d0743c035400c00064550f501c2c04003a0803169900c00410000348104095a00394514150000350741c034403613503008404c4200407040c1c201c0741c4d0040345040c1185454800c6122580b140c8e25805a11014030301100c1c0c07111524841c00318240d549018100c1200d00409103403d0590707000d0303800c1010075104e2810301035840d1103005150207200c400041d00940d5010341c180038000c0015444031441c40d40c440c0700450b20b075444010810450b000743c1243c0e030042001040036100d03940c0f10300c9525018920209108020701980c0740f581e4400d41c00f04004110407600035280d9600103806807108500016580c2c400c1e100403446c905510740502c03450980311b15410012401c0b02c00c031070310690280700b600c0b05604064103603007240c02041c0e4560810812080007a9500340100790041c4a03080c0450031964800c0840c0c1070001d8160034070991900e610400003c0074003031040103903040c100d50040150802c2918001d0500c00f4061 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 72775622 1250 72774372 72774379
    0x60c0a09121109040b040c09020702010c12050d0603080c190803070c0c0509010603020703030509010b0a050d0524010f0f060504180e0706050909090a08070201080a060b0307030204030203060f0402010509 89
    0x7421109010080c2c03404054841e000d0711184813403c05140c43e442c2401300301e5080da0f0842c0c111402140782200750080b00c52060b0141c0d100c2010b2841d94549078504114883c440050150400c041f40590595029500041d03000e551802d407219007117910a07040c00c201010589041e000f651422001445078401d80342c0040003854400b001d0305031464548141429600901d40c864507040000490030761680050007d540700c1c4d5000c1c8007a0b1070741c2d01c0040c280c0741c420500640c00022040240300c0d904000010248050040c0300320303145101039940c965140a4121001c5440012880052100c11190b00c0060010700341200881082c41c41c00000401c3d134060b034001c0e004080c0140700300314646000d40d0400c070006c440c81810b5400c85540c4040c0a03000c1c8c5c3c03044900c07a00404204000602c10140403854150060b000880c0c903182500e0b6a0045588990040c09911501c1c0e0b604c1021490703818041c00395100c1c04960b1401603a4a003140101460000010802400f0000e1502040010f07680714050b100c0400054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 72776872 1250 72775622 72775649
    0x20108090c030703170c070f06030b04050f011814041a070203070816050a0210020102090f1206130212060405070501110c0d0305090103020409020f0d110301080d081e040b09060c0a09 80
    0xa85d608a00707110700c0341d100010b841410404507078240e0300c1e421074080301c285890402107020703c58107100655404442686820140c00300400c2041c800329524964130306c0032080051400e8017084210340415040e1016190004502ca000074462080032015070095400c1c0011801c08085a032200481e104450304078400042ea50b14000c2085410000f5401d0b040c7d0040c46d0007004150031400900035040101c4c40b901c10030300040c144255090402e01074014006050240c181ca5071a0402c2c0706010080c00e504a812050103075100210840c14880a8081d074413401c0076108851600000510b0b05000d0500c503046504400c42c4a8015528400c03c012070a0b03160400d65180c0000c0b4005030000e0142d9404509900d0001640d006c414030488000d2041c441104001c01200c0100c540a5103680000d002e03410303e035889004118580c5010343c00196220380c0008121000031030505046000d0042510100c4d001161030b4140103040c80184555680300121a41d5541416030ba8a002085100f0a200b240c0110524 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 72778122 1250 72776872 72776903
    0x120215040f0f06091b140a030b060d0206030f07171608180717070b03040c0905060d0c06020a0501060e22140303041506091e0b010201091b03020108090c030703 70
    0x700b002600b159030080c03010001100700c0d04144805c02c0103020011341c0c102c144003020071600c03c0d02c01c4440b584c1102420602d5282c0c11035403031307446404028080b207030b0000014503840700603034459004521410b080d10080086003008040034243e1a0351800c5040700740007042c10005107420090041e05014120701d4203074070030307140c411054a40c0c1c071824034000214043d1b060086050b51000b110f512121240c481110081942e80d0419015800140ca004004428247c82044404191f030000c40e00603030300a040e02e01c84030859032000a003000c980e0107100941c01000800381441004e104000003404045c0c0308580b40c2c941034008040314092074074581c000c0215004100306000102004158000302581140d070349041c1800c1c0500282000301c0c1c038805e00c506004c40880c0c990443d024940c440c0200e141c001101424202c3c00d10302a221000c0345604647d078583c46440130500d0201d800c0d0b2800f04c9002c1a501503402d6000051225000605400256100b0070040c05a40c900081c030004503038014803140c004041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 72779372 1250 72778122 72778133
    0x10c09050609010806041104060207080c09090c12030c0304060c0303050a1a01120207050a0b1602122709010f080d030603020d02010c1a0c0424020c0405060303120c0403120215040f 79
    0x447d84035400403507a0201d40416050317000140c01040d1280c08048840300010728003080300c0000111030b00b94941c0c00c401c1c9040761904008815902d021510001c1e207040c42c81c80302c0301910f55080f030f41c01800010900709a0f2004c1c5501071059940090040d1002c0c0603804004803074540900889000a04000031072600150004240d815128150340c80401c0c1c405840d02c504118036850015244117100f1000b003249102014000501621400610520316051440203081d900c1e00c840c4a50b00d0080d00c88451000021035039850746018040d0079070301c50030440c2c1401c00710b0301854507540700071200a141ca0010240050b07030f19980d030300c0c0c9035a48c24a02035903203500354030380307203034074401c5603510b0403541c0c4140090090521407100500280c80d40e04d20a103103d010381e40504082c0410034100540542c200710b1001d0011e04060300490f501560240c00c4910b1710008401c07408d00d8603400c880355514560081010b000300a08001d500c01140110310052402145031010ec0344001c40103440101059000a040c504000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 72780622 1250 72779372 72779381
    0xf0c0c020108060a0f030f0308090706140f0c190c0b0c0a0f020f030303130204050f06102706050d050c090a0b0703020a080711100203130b030c040f1205010c0905060901080604 77
    0x420292050785d0b003683c03464841100d0780d95203002c0740030500100008584100c00100c4d0b80883c1c007a0b684a1000010840350482c840c0d0001d040c10041180c10003e82400c1c4404001180120710040d90021601c142070900c4452800947c1000c0306880b020004000308420015803000f03441e4010a00003069102840000c9560520300c2d00e5603017600001c0104000107001100010026000b91414081036644042280000004031a1107503c081c4c1c0b0140c1c200308a1050522101d960392440e42c560401d000c95420ba001040e80d43e0001c1c0000b40c0c0041c3c04900e0300c00900500303130031418400d00f147c00c20742e444000030100c0845015203040000045a10070502d8070070042c048a81d5000500036a0f190100d007083e14070b117005204014014101c0303468500c5c08900c00012900805010044408018100790b60f00c0380313a9002400c01040c1c5502031002084888590035160000c10220044d40c21461891500e00d0a403042c11201e84180882c281c800c006075140c3c50108c401c2c007030007480c2080141c0d40c5c0c00f00240042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 72781872 1250 72780622 72780629
    0x7140405100e01030c17010504080403030e010207050a2904050d031202071b091a010e0d0c030206030c03040b070c02060712051204050709060506031005120a050a05030a030f0c0c020108060a 83
    0x700d55100c000800c5c44215810103042d1407a091041c8002c2c5031460045003a10000e4070010403401d81044100046441000902c0c00c005052042c1d42d411581c82c0005409074205400c000e501c0041800b44d0304a5410b0030400e12129161051010704040ca0034000601c44da0706444080c3c207118a20302085402c404035030440b0901607020110320725a054000c02d200c41c14a807400303125880c91515100c0b03012000c10203000344602d68160f40740c3c03040c0c03a4200706011001e41440800c89034151010800300040c0e80707200240d4031510381e00c4d900c591a07103000d0400c48040d0101900440c01c1c044107070305810144e02d482c01164a07a80e008001f03041582d8209408860701d200e500860000c586008090004200703000c1100f001329424424240140e0351176004200d018030054841c01c01c80c1e110441d080189040003000c070ba0001013000e054440510741503c8150503c5000c0c042182c2c2500009008596550144155071200d41e04120401162003017002c013511120000402a062055143c0042d00d01d644036400ca5000e07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 72783122 1250 72781872 72781889
    0x1060e0604090f0207020a170d1d1201090201031508100c170a060e06191a1b0321010b2205040c02010e01050a0905060f041704030b15030714040510 65
    0x10303500c0003c0140c001e4200200c00ca00c11104800300298600c4205400426500c3d20030140521050542c3d0035110003000c80f4801c801644000110749469480c4014134070138080020000c1000f854a20004046a207884c07505824112000030a205000001a08607800f1161010004410780c8056054400e80304041920650f00b003690304110f070410580d0890f00440b000d19040540540742c1204104094050401c9503031980c8000208020600d080203034020503400034003543e460446c0c541d00380c8414035554203040c20f555000040b800702420142644020f6088883c0d4071300107030750403c3d0500055100d507150411001072581080d24803612200000002400018801c0041c942d488901a000e84408008a8850351804001980303030301c0396005142c4201c0e4040e010b40003070394900d12903a054006c0a0425280c1c0080c58560080550140c0f000700051801400001c1440c5461040c0c544075030306950409001e078002810410003000700407d810880ca2046034041401ea41c0e0700140c6406da103441d80a02d19 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 72784372 1250 72783122 72783131
    0x5040e010b0c010501080f1207020621040c0501020a03050a0c020109080607020a0302070f06090e041a15030c0102011109011d270106020309060a0507020105070b0702010b011d0901060e060409 84
    0x80c0d1006079002421581800002840305070f90700c050040c0c0368018170140780d495400140002c811007580d00000c1010701d10041c4a40d0824a401c00f198a007a1ba0901d5007082110504081c03105000f000055000101801d10052001c961166002442e038000c480400f804e10207000144401c582c000c4034400040c0c2034000032a01d003858150f9000303507100c45040058016000e240c40109219044100b0101074030711a88403c1b50152600c440041400b034007c01c19207070101c600818507590640301d1116401001e2500a54603d90303d040109803d1003102c11003a4156890004c00d0071880d62000c0c103981402c582400c00d0702c14a08002c0c50b022013030749065441c42d400350304015034910421340025426201400a8120342ca56030321880160395902c200d514840e030009060100001052090300100300c042c1c410315080e401e0031900d65440b185042c06540d08030160f51180390341d41103541d01901078110048800310850040908001055880406001d0007041061801c554001d5440761811280207003486c2c4020031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 72785622 1250 72784372 72784379
    0xc03030e0303090d200f03060105090705040801060603020417060609010b0a1110052d19020d15050103050c0f2a0d030b0315070e0d0303060b0d2003010305030f0a05040e01 75
    0x40c0c2054042c1c1c242131740790f014440645640c24000f9402d035000d40c0203001086aa4240410405030850007070481041040c01c10000c1044003003070080ca00204550386016031100d00701700600c100310000c0a0004001e40c4941d042111555a02e04128112055015099500c4034072520440350003010035103034509403003000500c00d00c10342c0540c4150301c07450b00404064140f080c3c840d0000701b0090020001c1c09020014000300d031a4103641603401140e040c50070001450900c200c0c4041003551201c0c41c10404140e03c0c80c0080003076580500078540d0002c0007800746445c002d040d000300303082406401c400800c0031a81681234560100c51054095000381c440040f1a402c0344811070040190445040d000d00070b01812103068a0000e191040a01800060b19440f602d100101c1c140048580b0300b0006a04240d01c0300030001f4208002401020080051040480d610180120050780c0038036a40010880c0700b0704100410115034040709803600c0f40d951459045ea140c0400c0401c4585d4055908600c031030240000000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 72786872 1250 72785622 72785633
    0x50613091b030b04061103090a080d061203080703050106110a03110c15031602060f07031806020a0f0207051509010815041404060b03011a060f1308010b010216030c03030e0303090d 79
    0x41e4813984c403900c001c0c040301c640c61094035081e000540c1c0f02d00140d032142c0c1102d800a901500a8584000b0003500090180e58407406d002c1c00300700040c41503020070224814001481da26005031805020181000080030808034245940e5011625015080041d11207400103110001d0200d40705600000746440c04020f480d0f10411960380c0700f6203440200380c80d16420421000d001040e03c0340b0a00030300c80000f080341d480e0b103001e0b0003400603044064225001c10f960380002850510182c0021076450340e61005140440340080d290040070b81200340308078172041400183d00400380869070b141e08286456555904c400c4a64440039011900d5203030320a0400c0c11240803040301d61600b503c178038001d0509000c01c500b4581803508880d507510041c81150003602b484001828840001d2104c40100c01290749040c10001003190745903455000071016945512500340e896a04001e4005242d04900318507544c18555521480b00d03680601c40107080c03100c00041c0c811140e5007070042d00d00d010343c040d120110501051505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 72788122 1250 72786872 72786893
    0x702030430140708060c03010506250c051801030b07050a2307020a061e030e0c2106010503030406051206060c030d06051203040302060306040e03070c080c03060703050613091b03 78
    0xb044110f10a000001480e04000950503000e040301d81d080c039246900304000e203d02e40c1c0c01041d915190b071350200900c44102d00c16103801204503001e2255003003c40e04101c10002d407414100220120030b040d0400500214208052450f0080000c0c01c0c02950345645843c26030326002d0400103850841c600c80b0303004110840702070041c0601842110200324032611030005846000d02000d009c0d25842c441d10041d0001d6010740d010480d040b140d0812500702d040d490b000120740004100707000d40320500710051406092420001203014110450241d03003054144180140342c1c0c0a50300344808074025490100d00d5076201c000444040d20319001c00c0d2659180381610680140030076100712800b03400000e0703b212075004003009030303010b6030b5000340381c03628603220380c1d08101c05042906603030415408104034100018086103100f2004000903005001140f013581c04050414400506000c185400c100400507156039540c0c003080204800400020710290310b082c4101464901c451915040c0c5854a0100900000401c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 72789372 1250 72788122 72788153
    0x303020c01050c030d0902040f0f0e060a090210030c050d11090f1210020306120708100b06030105090f040c03061d01180203060f090a0b04060b04140702030430 70
    0xc80d818248203000440380b80c411070a0b8000c1541003805500b8a41c4a81c2c2c001c40d4150380001d00209283c0410860b00044543d000302c0f021402d6520084d01103903000601076590305c021120800c004100680c3c010437070002903041d03a201050342e560041d4004501420a41d188071403480300403c808012207180411507406295410301ca15401c980c401c03c81e03d400050031a080c08248082c00152001817811800782d0405059180e00920704007c0403105035080105030014030b44140103050010150744100c1c2100d955511a5000381e004000500035920342400b0a90890560345442820355900e0800c2032180d4250340000704183d0600011100b203400428000035483c20303420003000748102c100c43c0307880c41d2207011030001e405420610010f04203480b030b05d003d6948204001c0644a144030750380d80b014000c1604031003c440680d5030300b01103034980c14244180045c0703420101490849041221000e990b1303000c0c0b481000e880380010b0110008114110b690340400002c80790003100400c45a2a100448240456 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 72790622 1250 72789372 72789377
    0xd0606020f07050a17070506191b0f0f05011e0501050109050102011b0c0512030108010f1a0102070504022a070302090f151005310501052802160603060303 68
    0x5090a807076200841c0b0b1004807580200302807042860085041561000c4816650381d81c01a00400281078907200d00a014042452005080088000401500a40004104000340a00503480500182c058060f030380940350000da1011103130b50075103002e6024003031000d1050412900c040c3d50040118860700000d041e075800341c81ea10b020343e4075171004a0032510035220701103050401c2e00040007210b0140c0004034070301d0301884c25a4004164030300c41c2900d945c42a44540340ea41c0d55030700f124100c0d14a1b441000014080a1201051402860f0000b595407140d03003c2c40348500c0e400035102c000c1640c0e181422080b1802041924070060710320100075241c3c01144030580c090040c680c0060500c1400e10103c40c4200c00324840b01d00054041c1090101d4000f004121009011040041e05030070b484007205010f10319010f0414148500315007002c50300741c0640307600c054140301043c8600d41910400140070b00b070b4039004916450032000180341c22840e004502204448a058200010551991507001001900d0094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 72791872 1250 72790622 72790633
    0x10606050a021005040f0203070b0c0d0905030616050c070605031503070312050310031707030f050412020402090d170a09140109120302100213030c0503010b0d0b0a020f0d060602 78
    0x821003916580300d22446580140c01401e400300040c0707596407010b0f4106004021410313445900381d0220345890125040380140d00004552030050440801225611030402d2504009151520000c2070350340070301600b401c0946c0e81582c4a0781c5c040d8032490558000000180450f90301c140c0d10300c00036000b07510070f48002c03c0711410181615031b9420001102002c60358000f94400844407c09822031b2541c10142c0103030a1144028400000314a10b01740301c01c01d6040141d2040ea4030b540f83d14000d042c0d055954420028403609020400280101380840c0300381c99016140907a0b030307070080b90004001064062004080380c0894100c0c0000d003816802800c00740403551110751070162551740c501181c000646140740004c41006040c80700180001c416015a4800d004a8003035411100d825020b0780c001d010072000340d810140c070400a01109614030002098250000c2040d035081d00b0109030320707004e08907014100070b003c4c0d4041503070b40000d94100d500504024200e2500d074009604088041c026610610005100d007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 72793122 1250 72791872 72791879
    0x80c0903101a0102070b0c0a030503130501150e09160b0c03040302060403030503011806080606040c1701030813091104030305070f08041d0604140a0b010314010f0602070b0c1b0409081603020106 85
    0x2464220341c7d024051400901c3c0303449203030f07800311a01e6000034040b14501031078040e8100001c001b405540d2032032140f140c52034246401d140c3d1765004d0000041846c100f607401a250300600001071642c84040c0d4108002085da100c0702c0d240e2443c41c500c52507000035009280010000140f50f03122010b0350507110700d0124030216000f4950280d0503070b4903074000e100b069040030021511a1034294894800c010013401c10391001c0e11014412003030010240e10588100500003051841d4040f80e0341c2c114080c00d0030600c1082810f6441000303009602842c000101407040014241052103681440d00488503031160459903103584403082d000904000201280c00c1740c15110206110f03180c18040e04180d100c06414294040e640c24001101404403481d005060650301c19510200101c0d0756043d90282010f102517044003480d100c0001c1c41d00010340d21086c1c01c02020302c1034903100036020540200c44950300341104a003071100c600042c0105042c010090401c880000c5090b50404000c01c00820b143c042e0b00200800e40d40d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 72794372 1250 72793122 72793139
    0x417060609180d0e0109030209041109060102010e1507050f0301060905030706140702010e0609030109030c020906010f0c1b050a090c090b04050d02150d0c082401080c0903101a010207 80
    0x600000c01400d5801c490107551580388134001303016100d64140b4100d4a00d50780ca8010400350300095800b641d0007003400201d8525400c000b803040380c00c4102032000b00402c001110b080d648071544074601c400450500b5011400d017502c50000e0724181411010305980e2560344e004040d195103041c0c42280c0c040d0140c42d20014000780507c821000003c9600c60a5141c40455401100c1c103900038150340e07901070014070041070b15031001d21941c07103094800e4443c490069070a004101c404800100b03003a040010382c117460800300e81d04c0f04903401890b60241080741d10101d00c05200c400301d51180c02c01500f203050341c400003405642c9500480290742d25619000e00e9103403207040000340c0340715030b01900d0b401011031b0420a00606240a140c025145c52191141c20010b05200340002d071104d100741000043d01d03040c1806001002800d2444e402180b41e500000e00c00b800800207070100400400b42c0750f0510020070101074a403010321880e0040b03118903404100c00085414111410f00145c4511801071040440204c1c5908 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 72795622 1250 72794372 72794401
    0xd0f0201140708180d0c0c0e07050f130806070c120306050109061805041517010c020d0c03031401080127020a030611040b030903070303180f030e01050417060609 71
    0x603040c11000c902e5846141c190340404024118581c04245600101c0a80e03c0602018103101d035507595110707110b442800d082d60a8819508a03807001c204002c00c0c007a80f560401c082b200c000060410860f114401ca00700401c0324900c6034801c0041e400394070200089543d0042074000a103100ea41c90010a808105080707044031170703601030a80815001034090044601650301400351040011710020300f2916000450203450700d00325001b040d10203500381440a1007655004255800000000b01301900000900940c0c1c0d003041002700b4107000d682c6804800f032511907008262146410794503000c0c04e594901e0340600030003004a04854030060141800f002c151040600520160000c04482c1c4103421034481400900d080992400f00540402000901710520400303148640da0000145442d6101801c0c05401d03900c0055000002440c000e00210004060b41c6161444507094684021b00c1e50607500141c4842c8100d0300400c4032400c0343d4903841501c241c00507101c0e211300b000382ca5030019070311400514200322 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 72796872 1250 72795622 72795641
    0xe120d0203030f130201091e1805010f080303070804080306060c0d080402010e0f030601090213050a080a0215040302090a0c09120606051e062506060305030306030d09180e0c03030c0d0f0201 83
    0x24001000410423210b106c40020540c081301c00c4011407035680c0f410311f81208904801100d1425441c0e500410240c20069981d1000741018809107146240412006181400081009140071000f0011501e1601c1d400c094405410002007280d01d000355010002d400384030216402c07400202c039092039050604241446102124000e0024080c590800e0102000b03074001240342e0050304400c40001a0301d40c0c401040500819100000d0302071040a40144003219408038103d908404040004200580781d41055a500c881c8040001440000c0c0320011100004941d2041c48034241030700d03032031041c00100d500100480780200c5684088600041c030300d0242201d003e1465a1103541030004101a8030008250305010000880c032004141d40c1da03542508441c0b080c0c00507a107940c0040104403850a0401c801301c0002c0c0c090070145600c9252222103128102541805001c6686840450300350b400304012010160100a060300e8480440500d602d6a460580c40e0034000103042d0011005c1c000d0040c031405554 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 72798122 1250 72796872 72796877
    0x10503010e0c0f06090d08040f06180302010f03090c061706040509030703050313020a120b090624010302070204050109090203120c030d0914010507030605040b0105190e120d0203030f130201 83
    0x840c4810204666500b61040c0d103900500c0405c04044280d81d0038141500c03141c42440810b88a038240710601e484043c0b140c000e141485254003100e42d0034070f40198040c048a03424602882c80c480d031903404a0260140d190005c0c01e4900440c00420426009060261100150700171000c580d0b440c2001c101c140c41d4140e4003501c55030010000d410211344541c009641c4a00c0c80600d00540ca03a86901280780c20301554014500b881c9200c0c01d000401101d4250702d504960360310001d082038107291104000d1003000401102104001e00714000e15070b4040c0c2c060700d080c140c00400420032507946004070000741966032002c901c6406008840710910701c10400f80c510402c0d0b8000114200100041414014019500c1c103030356048084000202c020703000d000307052250b95240d80c0400c07040c0c9000c2c18001070350100c4031043e051000034030807284d1201c104000303464a1585441c004500c0003c12010602440f065520000c80303000b02148800540e80000c001c50141100d03083c0650b055032100a021144183e00000a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 72799372 1250 72798122 72798133
    0x230103020403020a0b09120703030201052d0612160b0901110307030504030204110903030703030b010e01020a02150f040b040e0402010909020708070b1b0414090702010e1207060f060815010503010e 86
    0x1030502400b01a18900d800a407244da4030710100c0c40d05501d003148c03650084006039100d90800060341c0d01608402c0c03003000100140c820340980c000f0030101e5590000d000c075024404814185080d61010400808040f95010700d0122142d00e60040c009035500c07543c403040c0440d0b420300c0000e00341e1100108507048147c0541e00d09040c6030855007000080d0243c20202a00400301340505001550140018000c02e84030b510005a030821400014000810100340785056402c4114a0405a1106807031074008144119409076903945070a80340019000380c1c0c005005050002c03c0215002502010860041c0d000b41c03242c1c1c00d11641c5d00c007200103910400800070000716050040d2000903181c00b003119000103c050016420003060020200683c20580c8044c40240070190440420b05041003160b4006110744020310071851550305407603030f5868410801c01d02c40b60005202c0103106459100e080407541034401031103c00d60b250152642e80b01d000c07072800074a000c501c000081c2840c05110b00600751107400040e04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 72800622 1250 72799372 72799379
    0x80c0f06070207141801091a03031e0304380105030105040c0501050a120e0c011b02010801030f0c050a14010f0c020a090b180103061d011512030c0606230103020403020a 74
    0x5403040755111030260040d4041709081d01c079400007031483e1301902c1040710000b03101041d0b041030f10000d01100342c0b940c080e030070810011007000030140440303a034100c00302c4145a0b01d4886150580d00200c0400030042c40c0c06151008003c03000703983c0d17203042c02d241c0c0c4015403101c1e50b40c031241050300702c520546004205068001c410009540101d01400038a40c2c20304100c2405044480800103035100b03c07030070780d2082c0c04c0895030840543c0c208030030321112855115404030800c001d82c0080d044060601003c2c1078101c003e1200c1e001c0000041c3d5210240c18003625182c1f22945c1c81d05101c50482003009801d02240120014009883c8520b086003803142d00100040886e500d803030b100d1002031480c80221034009101c80c803101c0e542036500c1c0b503035402584603140000700460a43c00d06414a801c4c00e120840a9040640d4105403507100c0702c2e01c1090781c030520002010200b01d4a0107943e0b0300d0413001c00900241c1084000250001002d100d811103420307401d07284030030300118070044080f44681d0000031f41c40700303244c082413 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 72801872 1250 72800622 72800639
    0x304021002160302012f0106080d0804080403140f010c020304060905030606090a0b0a030501150501020d081605030601170411012312060303070803010f0906090203010308091302090409080c0f06070207 88
    0x9800c6a4502c03100c0c0d81d802030701040c9200e0410943d8070300e201b86070b4540f00b0410200e2001c100250210f00c481c07405000c075042954a160192285100c090407104042c2820314000406020402034198810001c1000e02c0e80f500019403603400c54868880400c1c01c01c000040c46050105840d407046100400c41e000700e5444020700d02c014400040525007021300f0034000300000300c01340f05550352544488009a01107242100091802c00506030540c1044044004d02600c0125690900703183d1100d41012071b101d650300d400403500200404a8501c80d1a000000c2c4018448400c0d0b6003050102d0a903600039503003e90300b41c011030366402911400b601d03150411845800018417840070380c0200008059a20b840d5490f1560003841d002030f04074240584024900300842e8445101d214003e1010704ca0079800c541c550303111501240600d204032401103800d1039440a03050029070444800341c800502c10080c01d020340c20941c030507401040710046240b00b9522a181450390005000d4440c1e121350740102035060800651 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 72803122 1250 72801872 72801887
    0x8010501020a0312060503030c0f060c0f040918020d0602030604060801020f040303180b03090d1107030b130c05040c050702031005010e070f090b0a121b080c0705070b030c030402100216030201 84
    0x111300d070710340c3d580d40070440343d9060000f002070075150002007400b0003038989000c0c14480c5c0500100c280600400c110301044d900641554103e950364540021004402107418040d03952303012009501c0030b41c0b0145041044101e50140d40210010307038041000b20b440301b4646080344205400a0f90000c024041040040e00c60004000d040054980710742d045540c032030303007011302c0c2d0001da804c00441e4000007410341e074540d4000c070005240a20f900c0103294072031031600c51841201004c1c02e0f0b0000031018141d031406000c05005030400515015101f0894003400007001001070b00504402c03032090086102002e01c00003e4041c0f24145e4815100d078108030388555030107564040c2c1d40720499042c0905a403000403054070001c0036010005658580003040b07185a0074100031a8012500c61502e44061030a4403035060744549000e80c4008950040da0b960134150800303626140c030550113400c1002c07001040003649200200558084d0348280e0303a0089601014a00b070b0f890707000c019a6142c450301845005c001640c8034565 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 72804372 1250 72803122 72803147
    0x308160518031c020601080f061017031902010203071202070b0a05071202210a0905060703020903030903010f020403030e060a0512191d061b030a020c0f0303040609110108010501020a03 81
    0x21107843c802c803401d11080f0196012840340141e08000d0041206220a00c2056280c42001d00a85520f240090a500500e0302600500d616810401c2900703000328020011181d0040308440e078a148840c1c2303540000c1c003075441140c21800040f480300107503030328004034001c1c0d400c250382c480020109a0340300702c01a0700411009003048100010141800070480c0144011b01400b07001584448116224092505100308054506d0102c1850000d5145c04103102151241d0060054540580c0d105042c500291440c0200d46c0c260750b00d5483d04421910210481d40104120781c4240c42d1920b0080010f0104900c501070b00c403e0101140b0b0400803400051401d1048691240212010350a00020500304400720790041408621050f415035954582050170402961701404100070700d2208000c04c000340c40315020141c200900d640c1c0126028400e50000e101c0000010348110859889146c50700308074000d01148072043c0c965245001c11142154030550000b810ba0b101a001461003c225541c116280c000209 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 72805622 1250 72804372 72804379
    0x203090d1b0b071709131515021006090204120b0417030708090111190c020409051f1a0105041202040605060a020d030609050402090708040804050d0303090308160518 73
    0x4455810a00c80448000140000395801a2251107500e0003154443c0e07041c24844e040340041c00660170355038034805846100201710b80086002443c0a090070003406042d000008111880c0b600451103981c001290452000802e03000e02c40c1da951850f0b100c040788036500460748000c080300e5600b80401c0e0740e01e250305d0700513106e825070309101c64001441c00e200c0e0b00282c1e0841c002a880f401800f0b0740781000d00075442c50900640c0c825150025055030900450748101c8501c080c080481c8000041d03655a900c03211041c2d41090681c3e88e000e20413422100c0840300c040030715503820702c0d147e0403021090740c0c3c20380b032200b400f81070f140e2070b140a09141d85d403074140d082c488040343c0c032a48600000c1290b0311050080d003041085038000340b11583e0101707000f8050302d03201c2d00f007038189134034100400015a43e82500d40e40c04c0314041c24a050a511a810030a0280c0304540007a80c10010070200700040541c564000740410703000c2c0d03582484a44404c0d00300e002024010f03000d400081d0050103402d030b01c4c8208402d507400e5a18000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 72806872 1250 72805622 72805643
    0xf031a07051c050411010e030c13020f03070314010609080304050d05031c0b041802030a020d0c09050103030210060801020309070302100e0d141207030f03050a06050603090601080d0509010203090d 86
    0x1c082c55800940d1041d641a052501d44051000304400500984108502420500d03600f8000c0f00c0803a80d601a291700043c4100005401480c0d00768207981101d46a040c1c203000b40341d0b20b10706818045c000d845002d00c0058460082c0c400051a648511285415500704001075494645807600b006004000b00c80103a0b0203000c10001c0041706901022a0010000080780c00f203403c0d841001000201e541c3c4086034078000984240301c40041e41e003c00c2110070103034101c0d0600001e6081d403c1003000b502042c1c01c015500c62900300080141074002985c019804400c00b804c0c4030640d2038a140c0c1d400e17404252801e80e501d0744040740910041c6800c02e2074812440103450a01e203218030a2000905507141004240d81401072022241c1d0802c0d014000d52100e5041007041c145010318540d8014220800c00851600300742d918070218040c1d402c0c607040345004120051000da00d130300740030300410f481d92003c3c0704c2c031788803407241800c54180c050152050300d0700070005070007841c10000141c0600c00c620070300c0b0f50115042c0118 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 72808122 1250 72806872 72806887
    0x904020310050306060102030a02030702210f010e0d050a080403081b040902040f0503070b030a0b0316030302010506030601050102060106050a080415090f150501050a14150c0f01060f031a0705 84
    0x451014500c146900c00d00101568589402c1c10b00b403450103000c0314110341080124070820744d00003003103440c016030580e03c0c0e2200115842070f10650210004102e0703001d0084440f0110811030540120040136011401d07520341c0072049401351034500c500142c41c00407504110014012901031403245a001082483c0380102d02a41030080100e58402d811490030b0690224040c0000e0b0386074022500030706410340003841050b00741080e00300c2e28040144180750042d19003894800946040c40306e03000c01c200071300015200319103915003e4040e080442c2d43c1c078001d101e20000062158800543c42c0d04845064076050315205603408211100c5600400568110040062041c07103030103076210700312805000d815a02c81d04605c82c94032004586000300505855818040103020694400c0348a2040f0f80e010180d00308c22010030400314900c000c3e481480394000304041140d41d01030b00c5c0880c00c0c5540e0840d030350081140c2d50f15460030000490300d5010280144510410242c0380a040084081c0c00003550305113103082640 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 72809372 1250 72808122 72808129
    0x10510030509100e070f090501081905010b04020d090318050a15020f120301030c0806090304261204080f0601030f060e0f0a080a090501020102190305060d0807050601031109092109 79
    0x11460721003d1180d111240405c041c624081c0c91401400050b0012311046d490b11144569850340c00c041c00360b5000740780c0e1925080140950100c01c901401400a41d254580710450000620400500f80c012690310400264036141c03118184d804d030f032030003051605c0060030306001982240c01c507101c080552040d402c094039906810031001040c85988880140e582d030445c603000040101a0380070990b2684410148811581c001c41a01c00703542402015480b4042c140c0307856500100c0303a1710855900e001d03084d02c045803814010010401d495025044070300280d410303026070ba5a282d007440068029804100c0443c00904c2c00e4110021400144d4110341113001e8003a0316900302100b155044030408000140e0055207504280d4010027800240000c50070300305540540e8106142c2c81405000301944c0b000026446d64070140085000c50f0005d28641c0c44100c0c40c0f1301250394203800e0205036622035103111810460300d0108a40e0348500c0b015805020201a072616180f0300c040e170758508610301c4605100400c1e0589 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 72810622 1250 72809372 72809381
    0x110909090a060b0316140409080307090f080a03020a1b0308040b0d0b040c080402010f05042304060e040f080a020a0b190e0607020a170c0106030b01060f0801051003050910 75
    0x2800c000640041d4005180040c1129040b11845009410400044001e0601c0b24032100403242c0c07040c0709889040540780010000c00c01c8160044c8001c2002c000d20402e958007601500c15550001504400281c840d411640d032102501e5008005074050a00302000400d84400454422611030018400c2c949a5640c420181c102c1e40001103a40e001290801c0c5410040c000c03112249402d440800002100c0b86000300f0f8910024000b89c18400307505000e044603445481140e0003000f009524611703103c1407840c2580f15400400041744513900f00800840c003518060300c0306014541c04020181d1000b05070351000102e4102e0004072095005201c040c1001c58845410f01c0e2043c1d6210880301d00541caa12026404c0b540314220000035030f840302c000c00c034845400184011007207412010000006000040000e0f0b00d11071004249825420290004100f203403034003559050340c600340c0700c81ea150074030518201c50503a000d1141d10791081c84500310706102801796104039044030728030040d91282040c0740c03403080a56 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 72811872 1250 72810622 72810631
    0x50a2312090406030203030c06100b1611010909060b0405010801080c030c10030f06030807020909060f06010302091203130806090309060a050702030109020a0b0a17040c0e06060705101d0a030210110909 88
    0x127400032070400c440141c41144110181c1300c40710b001410412803902c000f282ca036807070b80c00401203441c0103581c4210307030301401401004125a200501c141c503161003040b90b990f0072501c642da01041d800000030500400101d0803000d01c45010f8010803c13070401d2001c00c080c600200d01054207150790341d43c1e448030795000ca00404d8040e5024000c00e69883d035492040c040b418000030300d2282749030014002d028908862001140e0091401d18000d80c517242990001b44c0c188880a010010701d10002614000c04071218000f081164010002c1d25003a68904140303540b607126100314554040c0041003511081801280905000350024000080c441216804540008000d03004210822800f15480d402941d0000d0f4019040b9041040d5484a0425941c1c0201c60b02c503d0146040100e040341c0010b200e0f072105010303507900c0b5403c442251042500a9505001801c02c565100541000c0354103600041000085100c541c0e40d00d9030051041411052700a030041c0390303400038002004802c20204d00a0307519508064000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 72813122 1250 72811872 72811897
    0xc05030c0705271b040e090606040b0a06050d110904020705070f050a14060904110a08010603051012171603030501090b0f03031902010b0a03050a231209040603020303 73
    0x541000100015140003982d83d80006108556401d01c144100c00c500d0740059100c682c00c072100302c001070820f0190081350800212100500100180a100054182d0003403074241c608000741ca04103414000002d00e01c0c000c0401150007080030520b0404c03940c5c03140426052148440c4c0c100000d8400107010b0340e014a80541d85030380000c0741401035148110301e86008000840740e52000701d2601c041c402d0b5080c02e42503143e02c5280b01040c03070381c00d603119a04109000d002e000c1080b50798a4262a0150810400b80a0100080d24000000d0000c120034002c180a5442d002440109040d0b29a505021040b85a2244101080078042c1400f2508171400a015180c825100031590350304010994048400c600901c80c4100c1100c04c0c0082c903914040115000360345020207458129054820aa024107182c6140640140040500200f801804a0b503400401e2080403403174800c4040030303201d01c0611658111405140c20a08180318001d400034000c0c8401031000c0e0011482c1030313890b000a0b0070340d04241c0c0b14214 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 72814372 1250 72813122 72813133
    0x90702031902190609050109061508010c14030c0307090f090608100c0903260315030606040903020303060409022403100f03120804030c020a170f010209150a0c05030c 73
    0x7070121114109448404548010140c0c84510791a40054822025000c2d264541c0c032a40c0d003007440b1083d044064116082102030052a409801115080c00f85200d0100c19500c2c0084506050384210325100c150001040d11904503180c0f0110b03403807030782c1c0003910b00c0301884108200041c9503a10210900001e03c491040022424a4840054100088402030314107161030013402401081d0000e6901342941d4215a0403400400c650b5842c0340241c01c4102940c8819202004100b040d00302010a0b101100094060352107944030341e0b01740819182c4090008025070010b000240c0c0504040e07000104c040d000410025241d0480c054102c0e000c00540e0840514090000420210104846c140c0c8003d00010209150302480d513102c48140c0b1880300101d004100d070140204050512074241642c4858008046480660b03a48101150003040c5840c001498001c0c10801940c8104c18429101021006031030034001410310002c81c0d069a014100b441c080c0f0200d80b6088004c80c504001804440407940020003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 72815622 1250 72814372 72814387
    0xf1305090c0102070504060b0a0c0c080708010c0e0118050f0301141003020306010f0612051b0c010905010c09080601030f0212030a0c0201080109022107090b0703020601090e0601080601030803060f09070203 90
    0x9013824040d030040c500850134043d041008030841e0f412115111090301c1c210b0f900c403e00d841c29201101c0e40b40e010310700900c10604c0110f0b00d40c03010341c0007000500c041d172207204001d03030b44100551380e100044a40740c003114a2403404000703901303108051440104008000003200c4c0c5168168a0f00302600360313140da0b59807040941c00d004600b000c015407800f40880b0101c400c1000d00d840001001c05081c0e441e082480d41e100e80c0400d00d60a00a225050050241007405448920904105000f80b10b05ea0b0250360f40d60034030320780b114a00d000318a01c03800e03100d40202500c1c8607030850b00d441503035899604040307800811800343c1c00221a03090002c0e20300c505c481c2c1d4800d12a02d01c1030000428400301a00005841392040000e03410b0800107883e0145030b8440360341036550955806000b6203004056a00c80b44860703d0000c0c13440101940482c403103040e500300311402c0140d1204046d03007940d1010240220b02565004000600200c0c10b484041c2d68000001001d1090038040e520103c2d141001c1030701c0801c0940d10105984 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 72816872 1250 72815622 72815627
    0x12040b01080601050904062706050a060e0601140c0705060310060e150711010e060c010606120209090403120f02120702060708101406040305060705130b07020303090f1305090c01 78
    0x5401429241d0041040303506190020318a0701c0080d100074020b540d07820481d28400325003494485814080c0d00b10244226050600794007401d411140300040c54940140411003100c00d00025000361810f07540c1006060b540011000290b2064642d01d0349407007850342c005010358403100158898180040c1086002e450444058641c041c000035892041c42d40300d40d44a011403024094445c010b0308140680400200d80c001a1003848807601c0c0303250131003000249184600e40540114045a040b1313994001115615035048080340201214954420300603400700e00030a20524140040070303000303500001c8141e072142c04941240d00000c0c04140b03261500b01004500c1c2d40505c60580c0c003403280e081c42c070340d0b51429000e0010344001900407107410780900310034407000c2e440c1c03482910055540042154030070700701400040d1690f00b110200403808e690450000c81c0d0720f2854415640d0080d0b001c0d000714280741d0000100210340b0080c02c5150340003071303000c070300700074040018002c903801543c171003000d001d5002510307000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 72818122 1250 72816872 72816893
    0xa0b0a110106030f08030606070b0403110f030702031002090a150c03031109090604051e0f10051002070b032d01091a01021002030a060510050306010201060609060c14121204 76
    0x1500340d01d9260000030800700d038103801045000340e400002c165483e61880b00207240c038000c141002d00507112420801040507004003041802101031003c881405da5403c00d156903d2044100094054210004c110500c80c0f40e03402529103180020008075040d5103405841d100814400b03004000034a0300758a02c814142c141c0318044c0c450884150040c541490704000c075900c607001510a03401030f070780c405c00038281d004107840341c000700074484e100320342c071801d160468001018090715000c80d4040421000a4585444a0300400f24070340e07a006049403038035000c140c00b5683c20003009252001c150765980006030310070003a4a0300100309444010360325410301c1d0460040742c174004c0c0e5506503151103000b2040243e0300050a0a003900d8040c1c000351307980e612030004502030000c991045401031000680e0b11090f0b9004801b440c0f117076600780d0007000804d54841044424103810321941340800d0000240c68007090b482070041c121046603004407107161030782211602d0743e43d10000d000e51030145288240010001d41905 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 72819372 1250 72818122 72818147
    0xd0302070b0112080a1d060c0106082811030a02061c0b06091305060402160c0603050f010f060f170108030d0605030304050907080a090507140102060f01150c050102090a0b0a 76
    0x5100100552541c0d500c0b002d0b100300525007050109200c2078025402910301068450700014101c540c8620301545024041e00300e034020b00816009086003c001c0480c0b0f072334900068218501880348060365603e9180c0030551545e0b94903094000d030b0301e44801685500d401040700b0702c208031801841450124101c0c00700c5450120492180204205c400f0300c0d5034403400710005070905d1640000b10744c1c44000c0010b00074807445400d1300e6081300700d01d0414140000104c0e030404441d00c0d40c40c148415134920507004c2c060582400390350705441d003001040c48080e00c00c10740100c9203907d50900201c69840d1013030020300c00ca000d90041c02e0603440000c4040d1000100d004000082009a00450519003420002020800014508800c121075100003440e04c00080d00803808031508001500d8100d500c81d24440c401c030340b91000b8140513210307a2010031145100c0742c0c031050484608040300f85080718044000c541040281c601603540359024800041c00b40e8a0303d29200060880c86c401c640d0340c83c5c004001800410084a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 72820622 1250 72819372 72819389
    0xe0702030702220513020901060e0109080709050906010f0e0406050c07050105040c170319110313080a030e0f030d0f03021e040510022b0306081f0f02090609130e0d0302070b01 77
    0x81e00d1704016181c45501364107441003400c000c0d8408280800480d20980e00d80e1100303d46d486a100e00241d82c21681d03001900030307103e00c0700740d5003035030303251285000307901614402c2c03141c41441a40054089850759001503000305824181e286030034140d40f601400c0d41d905075000d484078400c1c1e640411140741006401c80d800780000000c0c0d03080030545140223400c80710400d984400c0c0701c41210503062014052040f561602e20601c0e02500050302c1e024419500c88515500710040354000010034903030b1410609445030210b0007002000d03281140441101c1080e07403110a902859028001031244096003030b105180d07046038500e941e488a1500003000b501e0607500310749000f9500854000e81d070726008403481018103060315034842d190300241304044009010325030026040d4011542c2000c5280e8a02c00820b656018046040c001d080554013030408034484c00c11000e5121208008a030128104a0038080015140e030b000015040302c400344041c146840c04914074002035000504004000c0240729182c090f09421 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 72821872 1250 72820622 72820651
    0x2030a0e0c0d03050405120a050f0106090c030207150b0f0409080309010b10020a0b041b060f0e0105040506040302130f0504050d02060703050f060402031017070905010b03100e07020307022205 84
    0x1d4901804c0340c8603034091a80204244105182c611034204000c11a051b0b00c0300071212505290302c0c60b140280301a00850380b805041107000e501c1584640265440035400c00f908502c0c40c400e92480200170641460040e4000d4100100241d803651076110f0901000d02650100d0307560310b0700c00c07451800c45000d03981c0a445003c59442903424568001441452950b2019440800d034560b07081070350180e04a151003030f2300c4c04002c840205895034440c400558000c0c0c6915610f4030900e039980151400c1c0a03c0c051540c0140303040c0405c00152800000301c0c4c1c44031054640014040807902003050544004079420303501540150310566403079504000e078550010481c50100540c2c28031700341c0c2071a03440f009400030f0303c62034010010642000c03407e010040200a5410400441c200707031b0700700f55240c0600c2d2044081d84c61034640005100040c100c122886862803c2e201039506050a482000c05030307004d0400b000b14030041c810000144c445004c00c00307600c10705d46054032585075501d8400e010340b58020011366200c1b00c1e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 72823122 1250 72821872 72821899
    0xa0210090b01061409030a0606030b0601110c01210c0c140303010e07030507111e0106061704030c050304030507060909050105040b01020d080a20041e03030e010c02011202030a0e0c 79
    0x7140903940c151002807400c0480c000300d83d8004909401030703051056040c007a00b03c4102c01c01c401640000704981c0318064240311940c0d01c50064960807071007964020729411007440c460441d0700c107800402d5036622909000c904484ea42c0404030488294900c0f40010944807200740c0240110b00500060241008008504c0d540c1001490b034142d1a01804443c04d050300d6001081c0c8060017a0b144814440c6020103e4850002120141d5a04002c0606041c034a5217003582c0814072521645c4504814030005c81050320319240c60742c0c102c0755080840c5d01943c103800240000b01c0082e405000303100003468140e6030707800c2030781c01d01d20024200d80c03041e405940b059103800300b032400e1a40c0220b490700e10311607a801c298005a0f00d110110002c1c03c803507051300c0c41c2c01403000141011201114083e000355403018140404025020418401c0c25410340400782c045094018250040d41c4600000c1882d1403061402d114200300407c40c01c82640c00c190b890020dc103071910140c859104003002420406e40007141c42c002c14559 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 72824372 1250 72823122 72823133
    0x6090b340302130b0a0201140a06030f08072402030403170402010c02040506120a0320070608010b030403050d02041203080c1e03090a14031e040303050a03020c0a020301110a021009 79
    0x98400305024590046a0042101d150882e40740081036500d07403075550f40c1c0c0d411100900804680e009441324891020204042e010340e4402e12096076401a001c1040d498240c0350380e100750b0000001140c2c1120259051200001490307810448c50700080d80240e22414240303005070007480c01444080c1d030080200200000750327038414a40c1080680503180010b40b40ca07501d010910008444003190007503c40d940c07501c810542c5c0310513031002100c80c0070804401d202841c40d2079038a62050f486180d00050001005004d0b10410710002c540003032184c100349151440150311a000d0782c009610580c00508895444c1c8140b64214034480c2e031100c1c2c03031081c50b85017640201c29525510416100d00645481c00310000d90016010050b505685400800d00c03400700c028910210b50742d82c40f14080b01c40c1080515a1140124144000d07502600c1c1c2c5600e51a081001800c0200d00130341280c01000f045116541d002401360b01c082c441c00d03140030f800800e607654030100c280000c0d113082c0b59a01454003161a001060001c0354 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 72825622 1250 72824372 72824461
    0x18010e0601170f06150408030d0b030d0804141903091503050c030a1509050c04081005010308070201122d0b01020a1709010c060204080102090a061806030c02030706090b 74
    0x61025901503882e192100171410f081000c0000100354480000c02080381100000641480d5007100414800713190318074103154880d40c600c040c0c6004140c1e03460104000422901070300605030280c508447c0e84100071860101c0000c280d010980102d14001d00c1880185070317001c00c0c50058110f60a05011a00700040440d51620008041035401d969031030301e0907030708042041070000a180c003c80904c600c0c01c200000c0c0906030f00c144a00d0416101c2c110044080c91b26078000e544c122034210700100d00341410750300151401300c050b600203852180c0e20f44c90003101c80d5403010b01e810022804900001d0388440d00301100d049540d0810203506552154000c0000690f0050910307070b020711889036464403080e80e940140e603d03410200300100080d00105010860300c20542c0a800782e0750040701c524250903034030a0309444003000107140b50302d9a800c480d02030000794042c0d04043c64203510780c412246003444585070305046132441c51044409526840070720010849405d1810000e0201320306119a41c1d55107007138400e242 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 72826872 1250 72825622 72825631
    0x130905060114060d15090605100903020913020d0302010504022b0f081b0a06060501141207051902060108010509030a05070b07140414150f040501080a020918010e060117 74
    0x1c1d2450360110340350035059031030320003203240180010014a417031107003544550702500d0740d51454804000346a1400c0c030225502901c0c40e4840d080083c3c15038007130101070b510042c06040e14035182c21102005803140c542d6034140600903400010207041c0b43c41004840440781c03840240000104490541c080510072a9052003030781f02507904030709012450400c2c2c00d800340400c0700c0008122203001c2040700c080030a441c000544150003c000c09078541c40152001c1e4641c03010045c0e070400c01d1000d0326032207500c0c103038158102441f410030b00d060031409450483c2c2e803442d54010030f0068000500411040c50240074040d0003000e80c4000d1424503c041c00000c16502035180060590200900882c18075402119824149015250030907612501c1d403160f5040c60788036603062030090564a5028160505980035a0b40d0400c40f45811480c01d46081c1c011199a40e0103400c1300000e5908224058007650740c20000e150702d106101424020f1f44c50182e420741e000c1070041040c0e05001144560590514000b01c045d50321 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 72828122 1250 72826872 72826889
    0x9030406030905071203020709060603110703030213030206030718140f09070c02090a0c0f0f09180b09011502190803070804110301051f060207030b0a1d01050a02091309050601 77
    0x602d90395003810740c505605980103882c80442000903406040e4041202c105450004c901800001d6850300101c0071203014000b4070202c03130018444034001910940044c010545408055140a031301e80d000241e59520545d80c400118211204440c806039a00281400600740e000d0042081500741c2e0100313101c112040d020900c25a915400508098040e90700e000222350003811080440c42c01c1421440182a400c0507075010562401c03803110781a104610300c0505001c00c0c1d4403610114034110070101d4212802d103080804035107400004503c0e4413811180b0f40202520704078041c4140703911901030b0500c3d20745250450350b401d400103060702103403905d0101c0383c0010107071030800341030f50340c03403c00d0203c0c0e484031040503906500744020b0100b02c1c030300508200c0108440040415420742d0f0b41030140d0351032409100c018608103040d030010310b000e040350b84001c250141c0c40400345c6402024004d2071382120421603c18001c50303400301e804409410180840000d20307091880070003400c60503448003070b0f81d910144600b125 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 72829372 1250 72828122 72828131
    0x10b04060302031e0c0a0306152f06041a1609030f060612030206060301051f09270b09060f06031b1512060f0109030c060f0c120c03090e0903040603 65
    0x10a18030b0f03025800841c0da09900d020016041c02074880400358070040d0511b0020b400c240c0f010030141d12403d014030b032510301780c0c0f81c1001042020300810900003490000040011441a501400e60814031010341f003107103d03141c4410190000b08403000c1410b40500000c000f6240c003104400100d400c00303421002c0c0ca401c8042c12141d03018a10308200501510f8204178005000382b040b050406800040c030034002d0404400074085507460307198801518120380404440114000700420900c030003940440c403200b5420481d4039a0000c01941e130180f140791100e00300d408496010030070210340414003e03580c20045c0e480150180c0d080c540c0010b550b4400d410381d042001e8540d49060313030b09540d1b40c0300214041d1807038040840d201e24203001c80e40807100084911034010f00315840c01070f005600c25201c01044e81d43c004c20b55850207080040407031701742c90001800700600c0f044005080c042a980b01b10840c00c00040d5886181c06070240c60020000281d81d800344418071602818002c1a000220603581a02e04500d00081e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 72830622 1250 72829372 72829381
    0x10b071401060b0d0207110105031501180503060708070206151e0a03140109030201050108030316080709030b180c010e0a0915031401050402180609010302010507030c05070b04090e06010b0406030203 87
    0x2070040026038010492080c00081114107031129030060b2080e180140141d00700c00301c5010056a03d4401200c1403000c04850ba0307182c150307940c0901451001940041c140d440310903211004039207021016685030300490201020018000c1c0d040041d50f9110340144054801200d8a01c042103004510039100c82c03120b441c50400b66003030f03210800c0440081d50020107120101c110b0410032402015010000c1c1c00550810300003084805002040b64052581c0301c152002280342241d0031aa07824002d82500304108255500001158609180b01d0240c03a00c00485019030131442d0324240303801d0924882e40d0602104022458042da903400e0324070100d03982144003051904400035035240b5412180c000034058000d0074800381102c0301c15031005d4455442500c80031204101c0500c605a100802c90f400d0764440120750061006510440107030400901c00e00b810040c290544da211401c001e500d4220852112000c2006c2203242683d005842c40310300d1100107403015504005282465102c1c07130240d2001d1540000126 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 72831872 1250 72830622 72830663
    0x50604171e0c070906050901050d0c030506100e0112051b01090f09050a0c080f010b070201030908070605040507050d030e0d0c030503031f0b040806130602210f010905010b07 76
    0x5035160360400011a46a00400c01d54503000d420021081003284035a840118080e2081d20844080d12001000340704144e1901c01080b00e1001f480c0c10461340311740c0c1700c0b20000004804000d828003c1d068403180344182e50910044c0340b45044140e03c45820f01481040c3d110100324003141c01079094035030900e4614882909030042ea4502c02c0e40d40000e407100c030701010010303120160b58800e50242114040920617020302c4001262500415104901803041d4580108044400b0000a0001a20605012400b800346803201015034000020035600e032034542d010001041010705c4200040c0808603400000c504840d10000e01d04c071030815156010b04501d003d03400030320a600300d80d230f001950303c241200d80d28078049001da1000e0011a035a0a006c61000b0408a00c80c10751009890584a60800400c07481e6101c1c80d10b40700070b6400e03034000e0342c02690030882480050303003200f5a2100d6100500354131031390b170074484040c0c403800605a00c25010b441c0380900610620b0716142c01c5403061904001c5804c0ca41c4880c0c90034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 72833122 1250 72831872 72831877
    0x504050f03070c08100504050d03050a0f061508010803270f0406080706180e04080a11100218091e0403020708070909110d0803010501031a101707030905060417 70
    0x203241035110100701542042888560003040d0b5034000255025003a8181004003610000d4400400319000701400700c51540c400d038070165100060640110786203107801142001c840741c42c2c001151804039490071101303c9402110f024010000d20008614090144084030a04600d2486400c01d00140782c8018820fa0b6030507072141e1241c00010010081a0b642e044d0041d41d48455206140c00b20b0a40c007114880a114400480b003100c02e5070390111034503076503551982d0265200307107440c2c01441090100c490350740401300a62100f0700441c100050761500303154012070050f4055001039120344045c400700055800090b12940c1460481c0311446419211446c003070342000005e401c1950316115003040000d945041d40c01200103203004050004980c00b058060042081060700064005181040100040c0d4030941c04004125032030201e0382080716a01c40040e405412011140d030025182c1d011b101c62040051b04066000030440c1400c0041d400d1079559207880729401007000e0290300300d000c001008031407071804 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 72834372 1250 72833122 72833143
    0xd0f0602030906040302070e07051903021315031508120901051b01090b090f0c100306050301021303110306010f05040506060c06130c0f1206020d021201030b09121c050405 75
    0xa06540300d280880050b5981c0d00222000c1e00144100300001403a40c0302808610300500c0656542e51804440341c001508001c50508400f04051b401c01c4198004910280c450020b80a244002d00000d02480030080c160f49a03085403047c3c1078403401003002144e6001483da030400d54041d0050351540700050041c1d8042c00303926449220450b880d0074510240a06501200c40d40b48144000c4445403140c800f03980d42c0300002401b051280d44401d080e4220f92902e004c10f600c0c020b4071443c021401e59280c402081c01e9804c1440d9043c040d0f03001d00010300410501105101c1c160006400801e4030303601d00b401210341c140907031082501407507907407010810503101c580c21101e4280b4801e04a0f071190500c8000c81c4884a0b0b40710701a242800c0301c01c4089039040505880074200d036001003e20700d041e051500c0d21002507100d581c40007596a820010f0f03124001c80e1840241c02140280480c200a01e000740300306007403040f117110081c1c050000b0080500313030034070b001c1c1041c0c44200c6c0503400165a82d56403400c5480e0081115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 72835622 1250 72834372 72834383
    0x70f020301020f0c070501120b01020d08062403060f03010902090a110f0408061b04150503090f0d021c09030201050406110a060e0a140a0b0103020d03050418020a0201140103110d0f 79
    0xa503804c05110001902c8040310340c00c0c0d9580300d050300d144880ba0215034940740302600517080f110201054034810262941c003c103004213504d5070f00300e1892504031000c0c1207082951800001004220162801d0065048086029802400503d105900141400000600b8102a06e40e034000e46419240b00e0710070390300040c40c5d500803283e0303a40d2100030141e03840790100d400d0394900c11100f00461a0306807407019681210741e06070562030200340d103a0050f80c180d04010111403052052030349841c034280c3e003005500c0c04580141c024000e0380324520506281044001411028004124010030043c1da2180884045500501d0304100398449100c000f400c00d469400007602060802e107894503050004030f101c0d10b00e5441814400c02402e41450300c0740c0c82d10b003e10005071040c4031a00040015061402c1900400c0c0e1103440c5c401d142030340301d6040200403540701b0001e14110703a0214501350116024403070030040c0002820700108030741c9142d036a000002424001a4050511000c2040400401d560211500380e03000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 72836872 1250 72835622 72835627
    0xf0403050d23041203110d0207030c0f061b0309050d03020a0509040c0e0f03070f0b09120a08030a0e01020310091a03011a09011a1801110d030608010c02030f070f020301020f 76
    0x4a1030000c03400c0958003904c0322000b11002c19241e41c001c0c0306582100309500c04c458100310444034000000d402c81c1c07509500788041c0075240d800003a00b1203041200d40c0e200e5000040c424010200410144a880c1220740070b02d85000010317070104a00050f4919071100a15001da661810410b003120180510451b040d003090800c1c01d110081504180c403000c0546042c3c65500003001200101541d4606038811006055054401845910b000200610030160301034a100e2065800410161a0810307000042d66000d5002c028030010050901480c540c5400f904001d605504118558a600c40307618402c0b0340784641c0d0f0704c4070740015080c0342c44280020b00c0004c008225048002554006c00d40b4914801881003068000204220440070052403155401004081c00c101d400e0030000140c0f022001c005061084610010301e4400c0c2c10050b00c0c0d49103400765400f00316035161001c003601b0b6446901c15a4203540050000c1171552600d5401c1c0c419007500400c0242040c6194000b00c1c0c0207103d4124000c5410701e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 72838122 1250 72836872 72836921
    0x20304060c02010c09030804050603040602040503060c03040209060915010e01120227040608060c0c030d020c010213230d080d0203161206120609020f03030307030b030105010e0f0403050d 82
    0x10381d03009400420782038009000c902680c040c2203442e00c06134040205808802d1200380400c4c14480069a07000e48103160042c136094541c0000b9181c10400ca40c86c10000e040081040214208440803980213401512403003407038200029002c22241d81030307140c141041003420380520603a110307003c05551111002030031542e0701c101c085403200c20a2855041c5d880c3e411035003404682820070740f1030081101c52000c09004651a0030309107208940c044c1c11400007610041c02107012180d504e200600203200003000050f0b40d40f48600e540650012146d02c801c0400c4001c81c8840c0d4a00c00340983c1f81c8041c0340031103e103d112000d42c41c0810850081207551a01c26101104200288070b004801500034829500c5101201c0c03c0d24000c0001d6401c01c0c02014851060040080d00180320b640000200782c0c0300030308500050451078007280c51900100c804000184e219000788050303090030f208440c05091031101140c4607190441c0d202e1a071040c003620040030001c0002d01d00c030300741200d9440803891100001d100000800c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 72839372 1250 72838122 72838133
    0x9120c0a150206130c0501050c030909010603020703081308090f120703030e01120b10030c020c0904110f0a0b030403200d05040914040c0506090f090c0a02010605010f0206130312020304 81
    0x1e01160a005407080da00801d004c045035441003030901382e2003031328051040d092900450301a001408070170203511090100022a0756036101041c045d0256640042e21980740d0f0074003c21300c0300c01401e840420800080079002255400c022100284020785075101d00d00054004501c1810707000100311202e025011000c03040503032000e255450140d0980e100250086482c0036142201e0b081c03180641e11914028911000718001e4100c20380680160064845051200300829610751045034100d03069209000400c1443c980054400114101961808592403c0040c2c1406a100181c006821710514035101004540f20394044c40e002038884c429900d41030a87c0b5400351030303034010b800b64040b014104503c5508511411120314441ca4100340c80c200a20318000c18003180768000c00d030003600961410710b000c0c22a15410401802281a007074542d42e5100350600081c2140d07e107801590401c43c0540070303030300d28943c001040798210014407242e89509072149002e8640398081c0d14041e407000e0000c003c01c000e200c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 72840622 1250 72839372 72839399
    0x1f09030c080705030105060315150604030516030510020703051e090607351903060906060908010507050a120506010507061107050f03041d10050607050703030212070809120c0a 77
    0x41d000e070020306c480c2e05c1ea0b000300b5445403c0c4054152105100300e0000304ac2c0381b411094107800e000007038021882d00e0348070380320f0b02d080020050152500307580240381001042020042180c484010480441c2030100554004249105401010700072401e0828234003d0030784900f00325840300780700815881d5135034014071f081e0301100492100c031050b41c581c1444a4001a1028100300a800050f106c2a46040390042800141c07c00c0c505e03034a410540e881c400410345119a00c02d25015240985a05900c140390402e45401e50306c00a104408000c800d00c50445026004184414070080c04d440100e040e941d00b0004881c2e900803040003400c4541003108824a40c40da000041000901603425110b02c120f40c021441e599200700d01c02c540f0021a0140500b107000c000c1039405800c2603000000309643c90b0388000088090300305200c1500c240c0c00c030910800415404201c80c1c0100d81c510050760b800c1860b144c48402044c042c00e0807407801412003990048040106000389514408006c1010683d6619503800d02c040c103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 72841728 1106 72840622 72840629
    0x30f040902030a140727061b06090203070f080c030601031101030f0902030f16060e13390e06030405030306040b0310020304030e10030b1f09030c0807 66
    0x842c09404020b004401c0350342c45d4480c00e0380c0054900e41c010395520b0342804e002400c10f800c010f122340142c0d081d02100b000c640703106c107108820304000c0b005e0314040303d0096060181d41e80218034014101c0e440700691391040700b10b4902070340c3c01c800d041e5601020b00002c0d000c010042c2842c03182c1e6110340c014030240e0743c4050005c16902840e601080c41c01d03985270011076a41e045400d6001640300010a2400181483d142c4110500a50b40118081c0b842c1408207048480e203a14140445000003030780c0240118840701000e10440c9862002c1c802c040000d0711001c001200d48041410394505801503901545c0c1182c0514955104d05040000034602544202e4260040580b41100006640301542c452400ba407100030f9900031903020840c07020f08229007003061620b007100544107500c2c0e031403582d24504c2090f000b00502030f41800e02515500d1160340000c04c00d03404140003140c04400403039500e04a = true := by decide +kernel

theorem cover : BRFrame.Cov 72661872 72841728 := by
  have h0 := BRFrame.cov_init 72661872
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72661872 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 72661872 ≤ n) (h2 : n < 72841728) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
