-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0483
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:02:16.484659+00:00
-- url     : https://prove2.me/submissions/26c85411-a3fa-42ae-b478-75ce8d33f723

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 86690648 ≤ n < 86870504 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 86691898 1250 86690648 86690677
    0x6031416020a1a01050414010b040605031b120708060d050a02040f020f0403050604020f0603070906050a05041701050402092a09010c02030a0b01050103110a020d0c150903051806070206 81
    0x403400c618070034001e0070003040d4060300800c1001c84400b901e02c0080401d014443c0140d01c1e18240342ca01070a6800e41d60b040f40c0510903114034180c10040b04480a410141c00c0d034044080111000c03200d000f1034005401160412000440036250805c40104600009070003e40a40305240960b800710f0004107414141940581e008079172498a03006040007442844d200b0b5216101c08100030080001c080b0310107026900840b244024001040208140e03444241c6840000c155075000400002d80180c1c0a090115071074208035041980e68608240f0315050080325050381e0f50f40b40e04000c01c515250700b00603044103e506000c041c5400950a1580c0c11421030140383c02c5500c080b45e032040390b078171495842d50141d9002c0c1c03d480c0102c8080c07414150701074080c0a9039001c642401200e64051009a0236544444000e5005100015001c182a2038480c440748081c3c2e0248040d01c48002061014081c101a02e440795a40b80d50b10a0b84d500e0645000090000c040c3c4a002c1c100441d0300960707a80e000362807805003441e2a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 86693148 1250 86691898 86691931
    0xc0909040c09110403050f0105070203030f04020609090a0b0925030207020402090a06050d050601020309090f0a0e01020a024e070506040602090f010e0109090c030b0d050703020a060314 81
    0x1c107040304600c140d00859100b41007044282c03841d03041c0c0000d070045034400c40c00c98008400d010805400c1c2e4500f100d001d401a4030038400141240502c0d61070302c2e00680064143c0b4500301101d00440d00046017200e000341441d0303d8100b03203202402c0580c2d401e940185401f07212200b40b4007400b000328080111380c400004258001c2000f00035552280d0455450100003844904150b81d40e000c01740980c4c1042214a82c140d141ca000954031f540007004440e45450001c1041c07190341d8981c40100d88491000d030903030001c45e668a40f001a140d40920041200c8141e070b40003401085401c500600b5013607000c2c5029642090b02100740082c4418444131503c40b030000301004510340e01e03c50054900f5004500c80a400e62280300244018412a1740c02040250b07801e840502c501d0b001540150781c81c9804078007041c000b41001c10200300200b4141d000403611149441c0c042034040005000594001d543c00d8113640c150400c05080007140340020b2104001d10090030b0603c21400390410082c00500000c1c11541807000010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 86694398 1250 86693148 86693153
    0x1020d0e0307120605060102070603090b040303050a2301080706090f0b0912030f04052b02010807050409150501020d080c030411010c050307060509120906030a15080307050a120302030c090904 84
    0x700d000007070f08036103910200803030305401c20300d01070a000c1d00c100d80580140d42d00402c82030f02c207020301c00c8044d4000c60364101e143c031180e6040303004100c018184860540e540d450b11001200041400b0038041d40d0703400c00c00d51541400b10a50a0480551003403048c02800c2d14100002e041c0d076294141152180303400b031911540102d020801030043c808001c04540400901b83d07034000c1c40040640b050340c7c2d042e500001000603a0408400b10040f00d0f16051910400400f0240190f02c5030400c50b6020045260141c1010707501e5030741c0c0068a20030f1880400100510805001c00d5034100404a840245403400704200d092134154106030b44000780001d044000296201c451341e0740240c500496030340d8880c003126038402003410b02000400044d03a40d00b24900680ca034200001ca4080c00b1348429420050106185484130a5000024000411142c4010500f05400101030368188058909140200050141c010051802c01729110400c2045000e0520502c00d201011004a040c3c604a10301600c0b840c034945c0303460 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 86695648 1250 86694398 86694403
    0xe0c090a05150306010e100501030b010c020409170a0e0907091d100b030c0d0605060a0207090506040f0513050f0604030e011d03070f08070e0403080c13030b040309150e01020d0e03 79
    0x10b079405a0035102c3c02000040c0c481050f8490351040100b501e40d500c9040c0c40784011015038150302c1c805400603050b48406409440c10b548000e030bc40f4890350710361004010345a03038185180c014401b800040341e03118034480394909040743c5e1513070300050b0341c680762035401d05150380e18400c9003000e01207400e115040000100f401007a0187c100260a52941480d1245407881c01e07104c1d0740d0b1204040d414820b003002800a82c40c20507d081c0c0e014540c0d242c0140c01150f041840f02e00c02050014000784e0311580b180004d100c0c05076503208041c001d81c101c03402418490003d040031403510740c2c1c040400c5000d60045e000c0002007988045810003802092a00c40705e240001400002004050b802c1e070381d8035011b80400090032801301585071046844d0001982c0f0050790360081c00380300c850200c5000d00841d5018002600c100c13401001072a14141c41c2205505040d101d46602585802c112401c801085941d50140b04a980340141c402c860011854102d00f0b803540030300000c0d11400324907407250a000400c2d0030b541c1c150f50103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 86696898 1250 86695648 86695681
    0xc2603240613030212070e0a0e070e01060804031701180f0905060c0318010203060609061606020301270b01120b1c0605040c06090b0403170f0c100e0c090a05 69
    0x52409855003003503541c044810b0924407049120382580020210100e0300424080229180d02c00a83c80507a10807507000003810b4905010705550040b0440441ca4041302c9001c18040c24050740d880c41d0701c0c9020314010f0704014942072941c3c404e40d50440108540c2010301a0a580301c10701170004a00c0c44030428140e00a0304040000600c1405040c0410503032038083c4e000b56100740041c5030303410306840107502103a080784800e44515400900801298065007400002084400d0544040c0803600342c4540303030001260003e80152800b009480001205240c150b0581d1a10151650b410806c030070340304002903c4040040000411036444901c13507881560344210307149102c0e050305260340007a0300610b042402044120b4084581003020309010031070b1842a900042640c3c0d034880f01501c2c180c155201c80c2c61400c012400340d03060311020044010300c0e2125201602c10300703c28a0040c8514090280c0c8002038480c413103029907099111031081c0b547c6582c0c2d40702c283e4100341e900d803002034961140c504c4a0020b01c1c2c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 86698148 1250 86696898 86696971
    0x60708040504020a120914100207020108040b0907170105060a17060414071805040209090106120b0c0d020f070c09020a09050f1305270c010807120902040c0c2603 71
    0xd082d01b81ca003813112a108018401803420152049079141c103408508901031844007034001000000000c000985041909800510000440b811503659a80c18030100c080380040b005a179458074284812400d02e845050064298032000c149110000c00d41c640d60740034020000740c02880251500d6403200380030b00c94200a40100c1c01c00340d1490942c0315581001d4401a90100d001c2c0a0b1500000c46070700042c400c2d0010307500700141c00b581500041d01c540507092000351020032050020040d03048903440620060903850311210710951242841d0800480741e444960003840560f004020000100e036000c96001d042d01c0b401c03618404040e18800c0030924164050144a0a01e4580f50a1101004400002d001d102c16401c0c4024101710791080f0300303a01c1d01425403480e8007069001020400050245000207405840e55a0000340351180f038000606a9042a00c2400891110036001d010701c12072401491104040c01003615006a96a514080910005114002852600654446140b41c50046460406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 86699398 1250 86698148 86698151
    0x1e010e041e03030912020102130506030c19030b0306190e01051b0d14071110090807020607063e03040c030201030c0c060e06150319030e030a06021b0c060708040504020a12 75
    0x8940e400c01a000f540500e20f0400d49c1f40070107000050518220302201d01ca0180055058201000900c00114100500110303009054840103841040d03142082450310902c00c01c0c0781c50741e2401c64071140c401102c21900481516034100410401c03014021b55001d0404040d50710056900c0000340d000c03a004024452030842081442014004880e5000910b014030000c51820740e09856041508101250f4041c00d00400b2081e0038003111016160800103021024028003004c41d079012241d900c1ca00001142d0400c194489082c0c60501c4210400c1c0144402101c2101140c2e1031410961a0150fa10004d448028105078550351101c2c9090300c55401d100700d007a07200c0400c0c010181c05080d0707661142c00840d0628051084206880c256183c00510140d140009110b69002e40c1d0703490301d0031102e841c07205001035007611541c400800000c0003880100035080e2134540340e8031240c024440075400c0001d03442c0203034402c1d9424040302c4081101d140c112011aa000c4600581e03602c4001010faa00310031484103511402d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 86700648 1250 86699398 86699423
    0x1f0e070e070e100801050f0f0616050d02010605010813050c061603020607050a0507020f030f0f010504060b0a08073501020d050109051e04060e061e010e041e030309 72
    0x80460024018401c5848030140c1001c001c007402500220304400c1c40024a8603401000303182172414441207030720406071808005924020125001d03500003022990440000c44080c000c0c05402c4c0714a1800004510081c40b030580b906000900404014100c4001448400d10000070040b00300030a0100141c05044951548110400304200d10366204054001d8090103000a1a01d0310441c04c07294144d41c981c80b080d0404ca0507400303015289800740034003601031017800c801301c00294081000c14190410704c0004681e5192519002058440c50002c050040160010510901d40045111025604600000501001c0892411020701f4000f00d502c541555011075600032f184041d0010109029805018800c90f41d81e964080300711202110501e040007844000c038070003014840440768200d40030b20004034521001a010b107007003038010703248a8124010403625486949902506a0041c650948000c946141944513030400419802c00d208540090440c040d0402d0b02030341c000c2c0308158029041001c0b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 86701898 1250 86700648 86700659
    0x50a0302030a0201060609180911090109020c240c070c05060301170f0a020310020c07170d0816091202060705010c020609120403020307091d10020901110d021f0e07 72
    0x4982c03140e0000001542440000f090f01401554401c2c212541e8840b24101c1d2147c03201e00c1c0b0014030344100c04031203a04030040001c0c541c0e030b00e9081d0580649440500181d490300c90728503c600e003180000304145111188108045081c145030700d541da0101c48511002d540b401140303801850300005400c0141c4c088004000072660310a14140c500c40e07000807c045460009603600030507511400c00c0b00095066019041407511448039030007a180108204003207400f02e0b130701c0d030910106454807011071800e15848210010900e95005c110160402c40304540d05401c3c1111400080101d03e09010712491148441131241c00c545880e0b08550200d50420001c100310720008400a4561070250342180b014404d5071041100351705600100c40441e9070080040c5030f01d074903241480000d40982d001121462403011f060402d808400c2c002c90040788092100141e503280c0c0c5000240200008840d403840d01c0d440b40426074030042c0c001601601c980c040d4402c00f42c1120074030b03031048060809409260010b0048107800505e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 86703148 1250 86701898 86701903
    0x603030c100b090108010b030d031d07031a071b11010c0b1303090501052802010209060a0305162a0213020a020109050706080415050604090f0b0604110405062203050a0302 75
    0x10b2014044403061601e076643c1e42c4140c2a1420700c0902c0d685908042d02c030110300c0f4000c0e40050b0f189580d0511040310903420751011424078529900a80c3c4101da40203650706200c14140410360302ca4120300701111204d209405244608422140007098a9840328103c3d801c0d0b805007402040d00c41d400510300302d1a161014110414112030b0100b00c010903281d683c0410590f000d401620841c1c0c00800c640340c42000504180c0c2d01039591a2136100c1995400c01281e2080c3c0c45440017040e00e0325440c1c8001c0346505125040c0301c620013803864900d081000c040300c3c1c0d00b0b00c1d201941905201001984e46201407025074000603142400702c40705802c0e624800078039544810340640103242594060000e44024a81d226400d64111030200e070000c050b60308120000d01c041140313030703c21504100082c0000802d4203907940ca821802c10000c0060340c6084038103003041128945809102d12402014020b503003014980004201540030f01c0291440342203011001c03038003a1000303244c4c2d0f0004581020454280d81c40d10b0501a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 86704398 1250 86703148 86703161
    0x60209030d030b0102030a0e0409052d01020301060c06091a0907050a080d0512091603030509030c03010603170a0309080412031d0907050c0a15020316090e0105090603030c10 76
    0x103009004090340c00310034a000f07210300154200c040e00030b54503204849200f11124104403400c0c42d40f0940c0c035008200032030702c200041c40300c07103201c4484076511505030140c6084070102c40403080341c96801000103028855000021407282c075405400801c10324468507040140f22505c50780f44803807108031300030000b6003100003079503c007180c03c01d8480c01c48440d1100d9004e502da005661415000c50000c1294054543e40e60100640c441140400d4401415401142c401f001c0440d80c02680060400701da01b00907840c0038018126048000c80007000101c1ca980e442c00003404000701d4615515801007443c4141a01a0b0810601c0690003000140da650b01c4030725000240b10028015030024a41c5c200c84d5040a2003030301811010340d8010a00c3e04940d854950440b000c2d0702507900e4483c0d5010f0059460000342d44000300c0c160300c101c2c0700800741e124502561400712250182c140c1404210420303c0400c9102d0341c51206905454040d90040c805980300804030345075110300d510154441c882d90408050082583d403241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 86705648 1250 86704398 86704417
    0x902030405101e0605030304030215030601020307080c0109020405010b0307021c020304170616111f110c0a0201080703140604050601021e0102030105011206050108151c260a05030a02070501020904090602 89
    0x1009070300d41755014595280a1400025044009040351007040507128001d55805a01441100d14000b40d581e40e012464122504030021703691174040311011072500e409003038090700402d28034a0451500c80c000956944a03000c03c8aca41564612280c40154424002c95014120003810303007110554800c00c19603901c0d0219002000e110700c040c40155090b104074580031400382d400008001d0904c03030400f8100e00080c484e48000711299203010f260540c6003610050444400510050805c1d502540000760081c1130045c02c801c205403404118100340511442c6254100700192400115542c0b81d80051385046e641042c012401c0381c284c0005800704805400850607124281d030752000e0141c40c0341c0b04c42e058441034001d0070b0104412034006003485102d170b4000500820300030080b80341d07162455005419500320740001e1785c41010b01c440d507441000c06840074030000c6120303900d06032801042d4400100039002c00b03080f0121180c3c00003140c80078000c007501a40d1000c2e4008100300240300162505600a40c0301042c00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 86706898 1250 86705648 86705651
    0x4060c0c21030e030c07080f0c0102030a14040509090307030207050906100e2418010e0a03060c0c080c010605031c0f050706110f04050117010b04180e0f010e0f0a020a0902030405101e 80
    0x30340808c4000c2000f060000040e00110b09120702c40d201912100081d0001c2c1c0400a810f1100003050b6484910090003016918051541d8244509009040c1042c42c1c000c98020041141842040e032180c0c021801700c0000e41c6000c401c842d031407a0010b0281c1118185c800c2c1415000b22034500d0038030124000704582e03441401101d0581100345c0056821403c5080344c03680c064603c1c0d60400110788250004010709103185000c940c10700e096943d010300c1ea00f286401c10083c0c0c0d96007034280164101000f80200d91540c00078021040302e1070305401010030b44001c80403000c0100205a030b6080051a070000038400d141c500c111500c0f243c0c143c0c0c1411050300b0601c84c50303002400c0b1a2000c0d509504000b5890706860035045c00317900c0c00b03040605003120940070a999a0a40365501411003a044007800701c0703150b04101c0d100100320091450350541c82c006007050034000c40e40002e48401c0040c2d403607ea01c48101c0b480c6e03030409a100e0f42c0c0c40c01c0550402c04d0308208014014208040203910796241d114081092006800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 86708148 1250 86706898 86706913
    0x2030303040c05281a0913020415030204031112120409090c060513051009090f0204090b03060708072609060f0c0406050304020607020a08030f0304060c0c21030e030c0708 75
    0x445551400b1340113502400d184440280500340f007005a501039884e10112170380c9810031038000302d01c0e20209000713203d1540b5400b203414040d03070005404a036601581480d095003842c1c01d54403a80300115140300107030b01c01d4404014005541c2400d002c2c03510720304690080b2030740340c540d0342d040d00024001a02084415000142c004180d260003001600d980e40000c0c4040f0580605000920a61a00001064040c422150030020b5010424042d00e80754480d281800b41e03d0300c4c42c01c0100010f40e040e40c104580f0903000340c4100306104e540b008049512441c145418180102c004a941440b06200140000c41855402c10130082080016180f40540d00c10341808429584111085540b4011405034500040b81040440c01500d81840034140c042c0c002031200032000c2e9100b10243c51980551a0f5030142c0b94003108000078806944a07030300c03182215007402803003802203030b903001100600080010b0101c3c000489410b0a58441c6e840b95666003210011640da44200d00d40c0c2595404580c40b50070102e00c180312 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 86709398 1250 86708148 86708179
    0xc090a0c081e06012001020a020f011a090a0b06070204020a0c03080f070c02150c072403060e0106120f05090a021c0206070206030a0e01020a03020c101401090e0102040302030303040c05 81
    0x51204407180440c108100d50f4648500455600c600d5603420301071071800d091081c20b150828070003440d03440350366001010240c5200b495203095502980141802c9010905404816110310015aa001d044034000103010b940510016405005003000650058404520040d442d5006a800d07080c0794066190040b0954400b2806039500e4000c0b140380000a04e0740028034010300b410703038000b55102241c02e035050038510f880d080145800007540c44403011205841d02c942c0300031030035000d28086c90f105207001d02c2010306044c407003224041d040c070030b0108102c0913203012030414420f90b0001881c90841d51080c070160528103c016500c08a00070705900c00c1c03038861451250174500a001241c000d901401c00ca082c420180c007004000c0e04005c1074180200d88038003109200c400203100a00d0018920b450068883e01201d1002c3c0c0341c8085800e001d0541c40c44c024510400d17026080000e411034050b04000b0a203c414500c500307019000320392000350144004420700c010030040071029400d580064892182691886 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 86710648 1250 86709398 86709421
    0x6030b0a05031b01030b062a120306010c0203010e010e10060506040312030c0203120916090e0a080a090f0e220b04020603040f05060406050103030f020a0203100e0c090a0c08 76
    0x24030440b40d1540c455801c148000c6649054190862814140020400c25000201d1400d52201d2a001840d9034110181100711806850250408502d01c2c0105480881c0c01a40d110b10300c0003511203414005032030152011540c00350003036400b1000c0f0300001e10050b054102c18036a107949a105008115041001c04502c9003018429642100d8122105802d41c5050900039801000718841600450004111a48c1c81100742c0d1039048c020031710100207225045d00c41c051381755407880603003200c1040740c00e01e6042c01107203a00045040741c450300b0142d01075507028014002d403804207075544620302004840000144174070001d88800c5c466115404869034841e810740802c8011032142c00d00908012204c804200076042c508080c55200b4480c80200150300e8258a505180441c100c400300c0b04680c80340010b00805d54040203050142001c0e0000f0902d41c41c8136030000741c40f100f0200e008207041c1c3e590304240200d0700b01044001c1c44880003403d41c003035030308043c0d84802c050076003900200045482c800204060700102c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 86711898 1250 86710648 86710669
    0x50901120510150308030c0405040510050f09190e0c040c110a0305070606030c0b0a030e010606170a020d050403020304140108100e09070305011b0813021503130c0f06030b 75
    0x5000d84010740742c001226005020303000402034a1001ea080210000b84400300440c021168640440d40f03880c41c6c082000700380c40340100703c5000b10b11004400c1025464084200b0044075044618914aa6480c40c00800700010030b48141d030224100383d021900c4d82e4021136811400b00c0c0036a01031101500741e2340150ba101e454030f80311119542c480b040c0311002c6403007100038108039032040e000440c005550f91550f942e00030954000c80e680440020f00340d22180d41501c525203216110600a0160519220025010000c00224150782c01c500e1000075030010010350403036180c83c5410302e08002c181445e0400035a217410501401d0495180450b05066541c040c5100c2c1d0700c01c003041c13120b8041c0182417183c5001c12610250882a592052034008000900c0c2805150b00c030a4042c000d10b00000804040282841d001411107511328004480950140e00d803900390004c0d8840c0a41c1e210f82da03455006070358402c2030324041d000d0840c041c0f030350010450103010841001143e01c1c80c0e030180040c020380420040403030702 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 86713148 1250 86711898 86711903
    0x30c05061312110301061d180d05030a020d0906050105040e0a0519050a060908040f0b04050907141303081305180f040c0e0405070e0c03090c010e130510080105011d0a1805010c020705090112 83
    0x20364583d07840144641c0c0210360181108cc405420710030f04480c0d0030305413885010100c40c655260801804541060b01c40c44100d80011070040400c43c4464031781c1c40d00e8103424455120740c40304e92031402c0c052142c1042001c5010790302c00b1040000103921306140385150030a0040c1c2518641c1c002e40050040c0034041958180e550040024886848200082e03440c0a07614044000d032003402d2240154036101c000300c500c0114003400c8056a903821401842008331340039003026102d80d400700000c144454a10101d290302410702c0b04004003946981c2011400c48003140d0200004044503030810040220205460701155100b8041c801c440d190407071580c4003404125000545076110b854207401e150f116055110030300304050a1041c240180c162520161141155500e05180c1c0340a810003446c1806d110300340c0103011007018004a12112101c580b41f0754400b6100c030030f64076103500d019200f0703130014020f51011981c000000c105403400e1003006910f510705881011300c5828500000510740070045d0f1941481179 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 86714398 1250 86713148 86713153
    0x80306013c0314090d030b011404050d050102300105010c03170c0f0c01021908041e0c05041d010b060301060207031e020a030c030c05061312110301061d18 68
    0x303140c07251990020709407525440405807141003804030426071034980790007500400041d01082c000001c0c05000d44407051105410450194941e100243d40340b016142624000c40b20340c26000e00c60704101d1b029004066180a19840000c0550b800400c2d41c2c2c11508401115081d40280303031381c0c42d0010b48101c1d8000030041c0114000b014041c1402494040b000d41c84554200030030f007400070149485240d80c00c500034051140c0c0d0300184003414510740f0003070035402000c5403422005c03e20703150352009824403103042010029800d2141e140104030410401101800000c0d01c00c200480785800d2088040d40c000b05a00040d528103242902c190614504490681d240c680003005400d2865540002002244521074181041c8000c44030041c1d0f60442400019805880710500190660a080c0c580c41810f900440c0304a81c00c22942c4400070f03403480003400311400050410300348200da05011150b140042401d544c154600400498291440c2c1c004000c0144c103891468410b0b9907000030790381002c501140c902481e6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 86715648 1250 86714398 86714477
    0xb0a0c0311010921231b1902120304090507080a050f070203030c0702030a0b010303090f06030207050a08030a1409100c0e06070204090309030615060e0f0f01140708030408030601 78
    0x450b00701c41c0514680520f0a41700440e0340940c01d070a80c21210103ca0101c0c500010202000c94840484440795140200504100054070503200c41d00d00e690540280244d6880c0481016501c1c1402650001c103100003041c801460301d0031000f0800d44003100c409060500d49008210420b02e070131042ca01c40c0d00303030b07800541c69901c0b032089100303507500801012030380351280728428800130740d290156900840c8643c9588884a08000003002e0200071900031104141c4184130710000308000182d400807054100b40c003550399856030a01c0b040508031042c03440c098460f2100a010303102d04002442002c242c0302090401c1054985401101c00400300c0301d60035440801800700300050300e00f0707030322500704030f840380c1056483c066030b95952405503aa10495441400729a08042003c2c1b0b130409200b0b8442c8004039020710648a040000620740441c842c01c89040281001001080180000c200c40c0e4158002c8402c681300d01d07040c98107000308d510450b20780e0b001501000c1006006069811a1003104e50100c4141c80d24 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 86716898 1250 86715648 86715683
    0x825120f030e0f040f090308160909090606080a05150702070509010e060301020910031a060a05070b0603010204050a080115060318030e0316030b2703040506030c040b0a0c03110109 79
    0x141c00d140502694401000c50401c038055130b56204224464404400c0403c01d0b000608000d420068001c00302118540076068440d4116444545042038884004001464045e05c0c100b480081000f508014018414403d00d5002c0c0a00022544d0744d0803510282e020460b5911802262111140c0c881c1079040043d9074014820070340380c07040690344120080c0005082c0891000000d8120301010900000710759560300402040402d0522440803840c01e0f191a441d14500a100400c0340c401d00750040c168241000218820340d5003901203034000c0c2001818a0300f100d840d0008075000b094070000760f11034080c222600146147c00380c002c81c00110382c10004510354020540341500c805180300c40541e4140610b4810b1140c815401707100d50040c6004403007402043ca001c440e051090700601c00358242c560003c844042300400008111810703601c05840c400c4d129114440c4025417401203030013040801d540810801c00b002da001003030300d5a041c040e6660301c82501c1d070641e46a0072180484001340100025031030080c0d9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 86718148 1250 86716898 86716907
    0xc0e060915070609030801090605060405010e0607020103110409020d0b0a05010c0f260c06070305040507090c120f021314030304030809010e0a090e10021201060e0a0825120f03 77
    0x19030085441e850315000040e0b4405003215240201100419203038001441100c2042c42441c0107007500b6290b85280904260001e40000318101074184a1040010018116403207604003c00600011100b00c2d140d640700c00500b4081d401c01c50b01804014545020700400b850171908403c1103640c1038466a4000e181602d4081600b140e69005840c03050318440c440442900c00110100740017103179044141c4aa0381c5802c910300b00000a400714082500745028003012460202e1010304644400d00c000074503a149030300c00c1c0c03441078424400c4016545890b20b2179599402d1a0014803d2032411410140c6e4035896225030001c4109407100141c140d44188803c1c000107038154018400240705040140403000850000340e030100b1980c0000c90b40e00d071600059007181c20100900b06407000111000d609103802104c0306039520384148625010481320840c00c1100361102c0e03010b2009080f1101c1030b00c02400c1d410704041c110f8216100d0802e10241c9082000440110380004000c1d0b60750b0000151078900701399201100e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 86719398 1250 86718148 86718169
    0xc08030705071e061d160b090d06090506040b0105030607020a0b10090207050c03060601030b0d06111306080106020d0c0b0601080702010b030304031b080601050a030b151507060c0e0609 81
    0x1c820110521642070b2030a03031a032040509502c101e0300403645c5904401d000506030300e58414400c07150301c1130041c401a411045184004d446040d101103032540c88620008103402c030080000b031b01300ea14004105060110208a0794425030040741d480d00166038800905a070340b0012140361005030010400103001a600d84511a0001e00103100280400d0320380320b0450880c0c0c459501250f85030b00000f64113142d400c040c4805580000242800c019002400000c280400b02d00350000b004203076581d0650010b114100d06840c050301d0b01125010040703458400c0542002e0007801010003501c28000c3c542003c81c801c20807445010340c060703c00746140e1240401508c5a0b440601008155500c1e20500c0a1503201007000d040114011807501c082d910000c10300b8000407155811600b101d03000400140150b0f21100c00d81c90031aa07101c42c00f05c02c13541e43c2c143c4802000c54007001c001d900100d000c0c0c1c0346000181c90006051840e0180000308029110a00281c034801c0d003d4030a15040303803090260b0411443d2620120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 86720648 1250 86719398 86719403
    0xb0714070b0d0e0703021008160305070c03030b0402040b0708040f0504150e0907050301050a0209190807052403270d0f0f05040810090c060c0512090f09160f0c0803070507 75
    0x3100d216482c2c0d40015110304040409000123202c0000300040108814194000381c1d140c0d007810415803c041d04002c1400d202c400010341403588802610407a922141e0499009000c01c00384540c9a1240d8a80740380310394032030f204401ca41e100d2004041000e01e064442e100b02c006040c843c501000e441d05581c444003840051006426002d41c69000070b00361801e000341c510414040000613501e611150410419000310801010003000c9102309210828000a001040e00ca003200c0c80c0c01107210102c00802c0441070100d00802c91600441841109841e003401c403100300600c001c045000d08036640b00c540e511074040700f5800000e05503942d40c00102d401250010710780200d51902625094845070000e240400e9103200c161010380c1c0c1c0c9400010f03c5402401540540504d1030700102840141d12195941d0304650852800140700045410741689e8510b42c0600940010b040c460140c1350405103c11104e000010074008191480c24400d4428811600403810341e034009042030840d110400119880d80260008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 86721898 1250 86720648 86720653
    0xb04120f080d0c02010605010f020609060117240403030c030227030a06181a0702070b0a17070c0b0a0e071814040f0201020d0801120f02010e06040b0714070b0d0e 71
    0x70070030340555805100c07441c0d0004e400210700b40380340000041c48505001700307003000c5410001c1032003031035080401c5460455440d19800ca0001141c0d103107c604100c84241e000101e980040400074400181820252281c2d009071010004038043c024254281d10410340704551000c4009070510501010381c0003c040384034090304444202346265100001c882c0140b0066010410449441c03040040c801055121503030140c18651841c2040701e0081c0d9a0b215a0007007000d5900040b0780c50346250b114190502c17240580122507110b9040411002c2e00100640c40291200c40000002079a040124022003803480c000c00002d00f041c500e0180740c0020261103141c0c00000b2a212030685c00400041c510f0107000e6402441c29000482c030501c00a81351071040d030080000d012004004000d88100240e0580348203410410070243d0481c180b004903030300710121000070741c858404074020038036600c2c00024200342c500ca110310103900800080032540d240141d00c05e50602c95810048141d40c10620741195641c3d8030b66004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 86723148 1250 86721898 86721907
    0x40305090a09020408010c05070818150409050a0e0304050114032a181804110111010e0a020f06030c030612070302031b0301050f010305030a051c020304030f02070b04120f08 76
    0x501501c91030ba10808155402150600401c00284a03c80c0e1003c424240b2524200a0b07680d108914001d6400300b600c02080e1241900d140d0b242c4a109541c000e1096010607921511003004100411059801403c0b19103054804081c0c680700004480584205031a010201d10b540840390010350b000404801d080d0f81040d401c0c2c0b007101c81a000c841d602c50750b42c9102d6900c034802055042620421180d09500c00c290a202850b00e4104540c481600150000c07078824110001c000180e034105540c840401e0350b50b20300803801207a02408a0761390300c124402c03140c40100c0c0003450708101140c00261400342140c2d00400100da2186024018509001c0d9440c0544003911b640e40c0001c0c0c103140c100c51404446030509140041070b8a801c0c8911503101d184036680c003000d5411911110b9803805165403410501c00300140b00d000e000d03410400440c107502e015000f5592440c20b8940200350b040007414103005803003030040210341400c0d6001034805460895800f08080341580d00d4112030f000d960300060b030750000c0070031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 86724398 1250 86723148 86723167
    0x90103020903120901120506130902040207020d03030615032c0a0507030803010306110313060c02010e0a0804080105090f060403030209040207081215041e0e250807050901060f08040305 81
    0xc090003c0b06030026049441d5501d21002602e81d003d070016144006150034204402030382c0d00b501542c10644103560020b942500d51000c14000d11941c8406940410844811070400d64160085800d543c03045000d590741c0e280300302c0e056054401c8141e0007454869400c0c812440c03800103000d0300c000405800100c4072180d0003a1150b41c01d25032980c006448440b4000300500c1408010b010b116032071105807203181d1841c40c20312200c021070b0070a43d000418194880304510000381c030035000742c500b031050442070720f041450310f1800b03071819481413003440701d036500f030500245240a0120f030703807610301441902030407040d0360710f5408034001d600c01c1e9943c582c800d81c00e000320360215030020060095078249485090b45400d006104000810013089107901c80c038100303c135040c0d5072181d0b030070605a014001c3e0000305803071544401250818001ca50320915044003400401e5511402040500842d40b00700142c500d1a0b407240f042c010805801d00800700404d00050f070700d420280c400d07000154454082d24181d0f0602c0e0685 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 86725648 1250 86724398 86724403
    0x3020f0d0f14011815110d0608030d0f0207052112010b0a0e060f0a030b06040b030f04030801090b1c051005100311040b09011502070e0f041407030803010b090103020903 74
    0x70901520034580b485140c0e0090002440f489540c01506100e82c0c0610320243d50360868160400c0c480d0008035100d880607042c00802c0400d403039880c04100d5080c000540c8070f031540c0350f40c0d8121b041c050404a050400d602035221070b500c2201d41040d00803001e070010500d01c1d0303094910101a5159400200d00c02c10000c00b14600d032104150280c010b0700d841310703511511034100611031002c41052610a55080115502c0c0481d9030701214864070440c00c0100b410040c40c0000740f917074040d40e80403901000e00041000800d940c018103151180e03109456654035640c85914107011102140c0f50540c000000d03030041204170607114a8114401d01c40d108503403902090750100000e40b502035800c11100c1c0c000d14024020444010250031790244141c4007004010200d0b0300168a0038010b00c01ca110445500e101d00300414802d0003414003070680d8840102a034140300c01200b9410300e04075401c3d01e0f04442e40048590042000c6100c80869401141003819642000b003d075000398801c940c0d01c2e061545c2000008510f4806 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 86726898 1250 86725648 86725673
    0x90c03070608011401020601150e060403060e010203011d0c07020d02040207120207090c02150402210105070c0b011205060601200a0506100501051c02070c0b120603120a020703020f0d 80
    0x10350ba080b010354035120140c60030001d6071002d0303410354010031700501031240e041000010a1400c1c6c0ba181120403007801c0441c866101d5034001500b00703420b05081c802ca1000540040d4101c4100c01222040d404107408020700c0351301e003500d180c503c010b4100100c5015140c052051000c0c1c42c0003c000501d8880c0b21782e140c051140700d9070920030150b0490b100c20801d204442c8205070110a00e070000d001240da80307808840d00c07000000d00007071107880c0880e04940d13654907954000082c45110030007086182401000034041c45401d00c0122a43c0c4504400807603c41710581103011000d5128000348402d031209401554400d040c0d00c440f5440b070300d201c4d24030502c810701004a03921721800b80b00502a1814410700c10400b5a0060b000310381030002c20014130700c140c40205600f0200c1007000c64016107918191520002d4004164091204903030003194441c0120b080c54225030240d003003101203507202d13581c1c4401030000b80914070051000d41c100800070000f5090a2400e6001480020f204400d070a141d030341d5043d01e134441c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 86728148 1250 86726898 86726909
    0x30702310b030f010902030604020d03020f031318020a17091204140f04090c060302130906060e0109090c1d0a1d040c0602060f010312021011120a150608090c0307 71
    0xc850341d100120b82414030914020b9940c4400034420038a0710380100390b941802131f00090285000c04000b20916100740030f05020039a81b502034a92358119071074401b810940324011511800b001503240c02180007070341708503401d09426442c4d0b000300c420400d81c0c0c80741e582c0740140b2180305409805108a146c451081c01070000e856a00b503100341c140011781c01c0c81a165400340a040c000c0d840c14120700003058608000d50700702e07100c5141c0981d070f480d14001e0f520030b009882e03482181200d04004006c2003032030708030030043c15119003039071003400c00340c0d40766000300076034812440307800103d10103141420040d825444000440e0a02a00002c15590f40c0c0e070010190b51b61400400c41c80c80403040511080140c00201640202001e1000300801c2c101800001c0800c1010f2000030482c90890a2100d040303802440001414200c00340c0801c0381d60485491303e01541e1000d00c00c4810301c0310101c000340c1000001c1c81121078901c00d81038504011820000207a800501c00307050038031140709000b01600719039001c0242c50050030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 86729398 1250 86728148 86728151
    0x204020316080f01060507150b0406030305090310050601090b09040207051009050f030304020102030d0203070c022e110d03020a05070b13031704151d060a0c080105030f03070231 78
    0x10010000148003007005441c51100f14020b000400c1029070010640d40780b0358000384501440c1c00100200002403415007550340d001401e0050010038940c001001d00451041a8252000201c0241c0a00203c4008030f68090206a443c1d0090080c036940c140a4016140c014000625081213900c50519000c0840c00ac1c0c1c0409445c0ca01c0c0c41d00f00441400450990200070004508504080e8000703522130040d000c04d0900c05901100095000c2e2207120100c6030590080c01d458000304a40705400211902d04011038040c10070380340c004103a284100c3c00092041c007507401400307001c407803054100c010b0740c0070401c02800c00030140281804141800c0c006400707202c0554203144010118503019049041034148111f04001110402000c80d68200b070b1000303200c00c0d00e00002010425103850400d42004100b1111041c8900010880100350070ba01492060223036484100b0309030303030700c45c100b5907580d60007506074010350020301440006042c40e940c40000d80306110790341301c03450207000c00e5850000c001000005856 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 86730648 1250 86729398 86729431
    0xf0102030703093803071806050915040504090f05010c0207060903061d100614040b01080a091e050705090105060c0709050901061701051f1a090f0a060804050d080115050a0c02040203 80
    0x2600401c040810941030302140031041c0c48e11001030110302401780c100313004401096590b040d1030f80003003c540c0a41802001004203400c2400c103101c80c0d03d0600400c1f12158640305807191618000580780d8120b4030b2560302c1c00c4540c0c4c159610704010b0001b9403a104c0e001001c1074596802414188540b010a030941940061020724001c1d50305030395000310401c20f000703c0c6407190b4130000d0b03680080c6031030348001e1402010610380a9494501004c3d017104404443c0410115250b01c1004800f00d881c00c11204216001c005c0c0da41c840381000950b128a070841111075011820800c400d900c4d5130800d80d440250100000303112980c504902408460380c01d000c64407650354408006c940380a8410690508201d4980c0701ea10354100440c0d42061150b5201e441007800c0f000c41c03d010795684011740200c0351100940710b0305809a80d940c0143c005581510111058042c03200c0c41c4101c1032141d181d07030b812901c0144c8081e11084804000717440b40c0d8041241ca0003041004109400940c0b507500007140181c0503500441600b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 86731898 1250 86730648 86730661
    0x120070605030f15210f060c070c05040b0918010905030f0a030507092d030804140a0801020f03060111160314010e0c0a0501080709080a060603020f0102030703093803 73
    0x18080103045040e500310304c0c120107010341c96040f094000c0c03401030091003009084060340d00f40780550f0110521490712440c0c0820040c1800c02014010007881906c2e030314400b54840c0c042000351030044001d150010004400110700803650b20f10320707071200384813000003d500310b06444003411540182011802400e000482c5400182c0c184903e03a0710000364a45400700a00b4400b05003500c0e00007075903a618001e0050800300f00080740c1542d80d8011035021550680d5207503203141c00e4840b41e10311031003644a12990100040c0949040c021910200700c1024803900c1c558402005603014640d0030525052441f0f4a41d680c03075001740e0105468003540c09500100980690210120f00707544c412100c850840e01311251600c2d050300c0d910119005d403002400d00389101c0c2e6500c0d030211003090440d8458081071041038a40c80500100f50f00100517a402666a0185a00c0c48030041ea941c0c420090010005416403000f00008500300040d00b075003c446003840712013080d85804190340311035003500c1081044800802d2082 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 86733148 1250 86731898 86731921
    0x1509010608060a030201050a0905060c0c09071d10030f021804050112150f1808070c0b0702090f0901020f0a020f07050a0b0f07020402040906150e09090705012007060503 74
    0x4040900d08031407146480c1e404141000700901c0001e06000000c110860071a00a207102d40140c40702400d0291542c11030a00207030764100901049004203200350100702140e01c6204118070344140040e01c01c9024821034188506041c1d1402c4002c01c040e40c070441c000555055000401e0207002100417000007090030720400c400ca130810707400865010300d8030419100241c1000344101e0070144200000134038500c011001d00180c524041c0000307044046c0b254690800c1510f2000e80f4903d402019011380850f2644070254480c0719149010398400840400a50041c401103100c80d8001031000015040c0b13201c841e2441c1550300041074a1026810420b950217852804201d20f40060508895456030340c0e140a8441001c2d20440c68100d000400c0001c2c43c10954071250101e8000700b401a03002c10409a03200d10410029000e14403010008101d4101e691082c5011068140a50071200280090528120054500c100c041c01100c11800c00c603501103071804018001d060003042292104d55407446d00030030282 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 86734398 1250 86733148 86733151
    0x90204060b04060e0f0d021503190216060203041502040807030506093405030703150e0c03060106030b180a2403030206010311060c0105070e0f0a0b07022101051509 72
    0x6495580c02d0004101e0030341c2c0310100a042c410242c030890074000211012075201c00100310043d400500310300342418454040802107101d0b5100d0100b461041040318005010792081d032944800024101c0b510201080d0f0a42c02160000c4c030a182100c170805500da580c00aa8129911403081500310382c1c1c0070401d00106001c407a5001040320003901010160716490088103108605034041000c04920510400c91000c01070f0300030b07010090031941860754928003110f085211880380d44042d428000901d805000c005104401c4280040103440c0d9603013000011802410095400340d1b11081c03559454045462688215002d07100032000494528900e051111240c401201303003c8041041440030408a50b010401b581501d074020b0060503250700c65000601c0314060f4014582c403d528200070b00c4009900f0400000303142c03a040d070702c3c3c43c5a19401820421801020310035182c5402c0c040240c00014501035603094407640c07010492000034074401c410b03182101c07011100441e0145908100c12000d140054800b0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 86735648 1250 86734398 86734409
    0xa20071503020906030114030f01020d02180f010c0308060a1d0402040b0105030903070f020d050d03141006091a1201080705090f16110c041404060c0503060120010b0406030609020406 80
    0x190310740304581020503294801441f07041c540d400002c1c505d0003969001e00049580b0200d8000964544103083d0802000398005518540404100b44513000c4074100401c0c41112000140c40352203071030a458a083d03405810007003489031f0102c0301070800300c1c030344c01c0d010b00d0b00b02d0302d240c0304141d44441c0c41c140c4140000c40b80a54411414883e081c0300700059180000111a0b04c203034412400e40c04109984082070301c035000080000c01501408422080c0d140e0305501c80ca04030480c10081200d00e0b142c2402520b000c8040b0300507000041c8250300148940c08149041010742c0c910108160301d00200f45110f00802071080e00f208a0580241034100918039160b0328150b04086c9041c0d0101e01070400030618440c00c50b041d501c15091000c0303101c98145c0301310700340700c0214002c00260007402100c0802c00c0c0d000f40e0800481701124070314507000b0401c0105200740c00392403040c1c00c103031201803289004d20701002054400c0718100d101d41d0340310100d00c28191528010107009510484011640c40a0b62041000359105074210 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 86736898 1250 86735648 86735651
    0xe01090501050d0303020a030b06030405060615190e0a08010c020f01060812030601080601030b0a090b01110102090306010506031b0f2a19080705030a180602060702030702060a20071503 81
    0x41c0103e6540d011881081945403e00603500e109084090f00503041003040640d00803008410131090017800704400744200d04c2100c009540f42c62a0f030303004609015a4070021008444200701c45250340c02130a2144d08ca03000100400101d540c0c0c1e4070203a007035070504565a00103810566100710101c00901074200038040506c041c0c4806d20340342d8a03139070081c00700426641c108403962010800c80d9000e64412280504080d00190b101c0781c80e100c1802c0908802085240068840341c40b460084c8010303c00c1d03445141c0300070041c3c0200d9182c0f01c10001280c1016082d440e00035000040401c05000300401010318540100318540c950100b0a05600c5c03550041a2148004038004080c006121001c122000f8640b4401c6544a188640741040c1100c5d0280c210024107910000174040111034100402c1c06038104005205c0c1107007a1a041d003207840303a070141c42810246e48103110355401440c0141c00382c1100300c00c0349000d10714001c2900080360390006652a038002074000c10030500c5000f000004111039003026050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 86738148 1250 86736898 86736901
    0x70e01050a030c0315030506070f0e0306060409141507080105060315010f18031b0506070803010e0c160c03260706020906090607030518010c21090807030c0e010905 72
    0x1910a00c581c1c10350004255444484120090107079200c07408018200c40054403254032440c00700da9507401a14100c1c0440c003840c0442c2c03200303841140c901c00d8101e0054081e0420b40c40d2181840b01510b0740c0c80c0c04403102b1708008002000c9450030000614030000641542e40139003403038540034000e8001070b0000fa010304070400402c0050304c0b0707803006078410300703001e180140380403c2e41001200d094002c5840303a050b0100860700003091100c101561a150010600d03110012683c1d5004c000c154070a41c10001c00c03504041c001080200e4041500c0365010b0003080100e407a0050003040315050810f0200100c85143c000340c0140300384042003044040300b403d502d407040d2281c000e00081c51620300502030b004103c19000500e000068071920151504010042e094545a402c03500d4064400d800c1058500218054440302031101d6124a114540380e0f90016001c002084107071814004541d402c080400900000c4d0030001100c600401071007004601a841111080b828400110800101039218190703a505000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 86739398 1250 86738148 86738177
    0x31a0703140f06100516060609271b030204051e09160302090c0c0d08011e12030305041109090a060e0715080907081009021008100b0d140a0207030807 66
    0x250b0800401c030707010700b0b071300079590b104580b18458820f000da603001e00184504104015030b0000010359020810901210314071502980014a003110303030325107850b0100020343c0402d808418084445c501410461a4103403250041010750310255010321000030a0000308500305056400c840d0058000006408403846000200c2d05207241400003a00c5210032401041110840c0022100750354609011f0760000201c011019100e810240b054009180d40b18002d0406441000c1080094a00c0d203011a5a098103c0d101107000f00801042243e01c5016180920381a45d54852001d00c145a90002040640c10900d042c0c005d42d80f030300b0441c0d00994000001405841e82d10b03001e840c00c00f109482d00301d00a95030302e500c0520340955075200c0107842c051404c1080c4d203400c050f0022200d590003628a42e02880600008541049013151000201c0807003402c03d0041c6c107000401031614103100c6002056119030001a003180d00d50a45041007070f540c0c00a0304604041e0000000b41c2d00c40030a01705402c4011125 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 86740648 1250 86739398 86739421
    0x301081b030606010e030a0f0b0613110315010c0204050424020301030203030706110415050a0306150206070e03160b0d060b040e06040207060e0a03020106030606170c06070804031a070314 82
    0x303010941032050300c8a05c0c500c140c40400ca144500c80c0c010207035600b00310300c0e82485581107006603007003409001000000e9214094601a80c88262881c40d049861582c2d0451b00c100c45403000d1003441c0c108101b221003540580e9540c0201030045010b01000c815450100e0034551998806014600a00e4014801080541c1d00442a81d80d100e81012000c030740c2584c0d2485600c11445641c200083d1200c07000220f4980692003006000b11182070780341006034589881880c130f0007509200000700142d01103400554428031440d40c0e20380d4400080d0481d0f02201d42d421580c080d00c1c00729040040b0091010601403003604150040000a00f2052660351619050074070b2140c105c0b0000701100d02442d000201c82c03003000403d42c440c5294445d042d05a510700409031900034041d10040c4400d540321814a1404030f1689038803410030302a4101c00c4020301000105006100c2242c1081030b06079408c0c4801d01000000c0781c0b540786405200f400300a090922817620401c003a040380c0c05039032020f8908400c0c004020050014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 86741898 1250 86740648 86740651
    0x61107030602030c09030304150e01050c1906021e09040b01080609071d120606031501060504090908131203170408030a05060d120f170f010b1c110301081b0306 70
    0x40800565031382c1c0d83c0c2c981075413107104110002da01440b0008001604000d0042810441180c070ba80c2c0031910541031004540794080c1024030012a041002c23022044d091220f21000700a214030000f600340682042c03030340944440c1c6051402c0c107080000e0760300c5440c500b80c820265518000d0074a44002e05150f0003145460000521a20a12241300016116404610201c1900c628003c1440a455000038031040c0c40d071400341d5049000388501402d83c00c40d03021020015050300c0c05903442c1e50410345080001d10141c2110758041d6107110b01040040c483d50070f261b804c04060702c3e011041a01c0302d060f511700100b0710a000c1c0701307080c52110f480051100041c0668126038009100b100080b840c5d80362400050012040c4d4000103000302241031210301800d400050b4182390752403d448a41500320140200b400034007040708c4900b44100a00c005201c0d10001401501450110981c1448c010800c159a24200c0380b04116207a858900840108a019401c0103200c0c4207050400780303150803009034400b0035034500c2d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 86743148 1250 86741898 86741903
    0x903140f150a0603050307031d040c0f0e010c061812030203061003020c01021c0f060b09130c0c050d0c17091e0301090605042006190c0807080a08090706110703 70
    0x304045008541c1e00d40001010310380180070f91f075403000940340151181c203c1c294040c0c1e03044100560310201d450103109100f65140b0540354610010000c000458605400c03c482a06000303c80c11110041200ca10540f200c080040d803c0c000302c280c0c00d003071560813180c07018410320405004000700311407501d07204820810301c40a41005031300c544916800f20f01a01a0020210103c04401399084c2491110b800c08070f84140036010402155440c2c4190448620541228540102050603045000c14040e4000f08178551381d803402c0b400c1c4140c0c9686179410028034404160000f9110420340c42805482058140c0307411641c585203150110306008603104504c12501043d54188441c1c006060b500c080d0010459590700906c1001940307070074070f80440700d24070799581210040071050900d1000d08040e0226203845070364200c018100b58030604211158880039004031100344d400d000c4080000c1c424009410400345980340e031485441e200e43c601d441c0122079070040e8204006190110444032000c568002aa038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 86744398 1250 86743148 86743183
    0x403140702060706020307020a120e012001060e090d02060703090308040303090302030c010c02030d1103010e040f0c030210020f010e0601050a0e09010b150d0609061a090d080301060903140f 83
    0xe0300d0002400340e00036828081c0501e400082080300c00380c0d02080c50b40d001c9100d20840c100c0900380e00022512842c0c1207030401d010500843e591080403810044a00041004600108409032030714688600340c0c40a0f9260141a448004142020354050210030391086451804020701041524010410340014001a0506030b443c0c2200c828503200b48100c2e490b00200600a02c04161483d03402541e991011001102c828038180000d0101703490b0008a038106c0e410402d00c0031481c1c4454640c921300018100341291502c985400000c0162285124507003c2c83c00b0340c002c2e081b15900b601c500ca0a5801c001c03603812090304444018049640e80350074541c141c51000220302c10f556900104d0900420395400743e540e02c2600885a42001d100b008001c06001038282c0c03003406281c0d81c43c800142926518090140040303000110041e100108030013400029100610a42c4044415118404c0a80c02a0490300c001071300c241061007801500100421702c2030f0031030300030a240546080b081e51502401040c0c0044d49 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 86745648 1250 86744398 86744407
    0x70905061f030c0c021906030f0c080412020f01050c0408011409030d0b0f0a0b0a0f0f0207450e0a1a0c21060f0612010504020306180903120c03040314 66
    0x441c40740c090600900d0b4064011b0000381c2604106101a12140c82600002801c0c980aa401010a401281c010f503440b03031503d011075141c55071030101581c00c0c40741c81001c500c141ea9503201041001d01a0502641d00b8080e59941d543c20081800d080d54000081620210403040611000401c0041110b200d9040403100041c2502020004ac2c0301080c0303142100d500081081c000315410103e41c0051106880f07030b49980e40c0c01091401c040ea441325580381480c02681004030304000103028202c0740d01907180d14840d18848943d0504860045801001144803442e0707d87c3d4104000b1741d8140b00d03140501142c40d0044c94155103a40c1d4081d8807000007225603659002c8280130581b02a410000d4a2418010100305901c40b401d0310188a0450000c44a4130b00c241f82e110098a43d034202803044545d96090002c27048101c0c1e00340000d02c0003a6101421142e00141074040c14440026000c282d01e0164180c100a1a41c600c42401041031280020340344180c642420000e010000c1d402000f41c140c140d107401c60350f6854 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 86746898 1250 86745648 86745671
    0x803100302031e150103050c04020d06080f0d03060b07200a170a0204110c03030a1505060a090306060608060d0b040203010906090b0403090603020408120903030d060305070905061f03 80
    0x800040d03000039018420340380240c80b606002203007290412040c4084400c0380004c201c42c141d10342030a10000d04079030021025040c0e1400c0c180c00030f21000030443d501040c2c0c560303204400b92a098102c0960065600008603a24800d0780c140205001045441e141d41c1c10008652078801d9140e086110380d01c0a26003807a41c201042d00c1c0c00c0c181c040200b5105c0804aa00101d030080141c40304443c850403845280351196200300071000009070f1703034890100d1005601303503038806085400600c080e012807440e40303408004c009610790b01c0c0b400412000185507103900000c2d00d07501e0000b00b91000c1d604001c050003500020001c0903241d1407149000c068120a48035040d45560000c28010721741550003410303d50911007207034280b100066000f40542e100b6070b00d45c1e56482c1e0381d82c0224200e00481c001c2c0a0a50049910280440a5400581080c007001000d0b6807400c01d0800441c81114941d500031503254001001c2005640b40038806c403580820141c0765032081492240f45000014141400c24041c19039941980c001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 86748148 1250 86746898 86746921
    0xf070b1803070605040e07020a150504020d140106030303050a180b070327021201050603060601030b0f0a081f18020d11040e0309041d0a0f03020a06020a05031603020a0c0803 76
    0x20303006809000d40b6101500c44a00800c6980a4082c010000501c140428045032000072201d1015810036180307407001061884c02c07805408054000d07a4001129680400410811801000050a003d0000509520b1850301500b0341720003c08038040c00c0e1410743c240d403403503540082e02210b8a40c402c1048034039540d080c000354014032a5496030101c0141e4503c0d01403400d08500c004804840c001c0320640a112001d021103800c1c2c43c1d048480c5501034000390f010546a5001e904501c40c0000d004140209032011100400e05100065010382101e030b2140c2c02e100d1045410341109484100e0b808418008600380310412a8840c00d01e000081c0102014146007090210710075440d46000381c010001d110b2144041450b50307407608003a07080c45c862844c203503003032854002c0403443d20003035981000940403106407503c070601d0300d010f00c6c04181c0550003440600c40000d00e00748000d04c2030400075244c0ad41c40c0d082054020703510605484002040c144100000404160030420030441103522a005580c1d070390741e9207d40390 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 86749398 1250 86748148 86748187
    0x20a0209040b0c0f07030c020108092a0102010204080a0c030c05091324021801020105010f1202060a030b090f04030905060403110f060c0a05010b090606040b0412030221030403080106020f070b 84
    0x501036500170a00504042e40400a481403074000d0383c03400c0141d00c4100304140c83e0f610343c01c280002036001c0c4d0240032a6801c055503c040011050000604090791240c840e800c04411440442d078501c0503034001e008129100c0202c0026050907201c4a606240c2440000d11004112780302400d40c3e0503410f4a25a00f0300d80d01540c0d1010002d03130300c055480f9810850051030740c0c2811000d442c00f42d42880b0002c11034100707004840080750000c410241d0b00c0100d5409016542d40041140801c058403485220110346510768258080c2410400203089e900d45414010090341e52900f110f44203020401040000c94000f1498955524080362110254900f800028607135100d128040480b074001d01e00007200b03000d0306620202c401681a9007006840c0e03565410030401d4032860003211040d13241400103000703000c039940b10846040d200740120b4002c81900c0d0f07140304a0450b400001a03407060000204820141c0c0007175440d006140e240018007040061031400f80c0c0b2003181d409285440038000c6003507080d0500c401c1c00c05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 86750648 1250 86749398 86749417
    0x10206070c1b090c17060f060304110a0305061e15041509110a02010501050a031205030403030f090b06100327061b03020a02070f060206010501120e010c050307020d020a0209040b0c 79
    0x5407070b03941e24a050380103003c40701e04040100d00c40350816070340c810801e074140f4420301c2c000b4450000c00410350b08200e0b03150409402598078802005102078991245030440001d980200010030f010720b03000c42d906030010811248000c44140202c18000454881c0b40c0900440400303d5000c292851064001340103c020b940c0185030840c00c01010300e8904003000001d1481041680c0240071585e00c070307824880d4507645480700405c2c01940f1060030900c00d100d000656040351081c81d000c074040c00303540e00ea1004d035042400150b8140da0000c0501441d46089903140f0420300c07075405d0520034210071100a440c048000e4003501d050040d0016091b00b085401c1d403003041d18040c003448000c115241003500500a4000c4446100544611503001c10f40745030309130006040304c81030342c010021603003420011a00000c034000c03031407085503c55031740c88004042130064102c1900e590792a503841e490711250080c54070350350801c80070135500500000b00140e100c0c207144941c40385d08012201010f03107440705100310030311a26554 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 86751898 1250 86750648 86750693
    0xf2119110a030302030a11040b030106080c070c0e160e031b130203010e071107180c03090f03080415291f050d14240105090604180c0c02010206070c 65
    0x1c08140d01035001e07501407050000c00300003403030b00d100210095120707601030314500013414001082180d00ca525090341c0801441109810318185039140020034660342c1289007250a643e0402110f1040800e1100f00c40c1c2041c60200d50001080c0042a2181c0c46040c0262103c00c07107800c0c403005900c82c6803e2a4070120341400c215038070b40e56600030404c090003c0e1111400560034074950705901d000019140e00380ea018404035070b6002c00741c0820500809070754103241d080c1a04c07006941c2c0414030a00301c07103002c5070080d2150000d5213071901d00710b040a6010200316a490313241c5200407201c4d42c80302c5806034180c521040c1d01e104c000d06d00030000b00c80c03000c9201c1d00000c903140c050082816a602002a10600044100507c011068540383c0c042e113010486004100c03662520f00e100b00d000d00054200385032881818401d1802c0401408511564001c0d00840000f0340c0d0b45041e5903c01d42a40f0903400c0c0d034a101d161240b00c0072042e0340000e4941d540030b4210001c0040401d06401803200f0410200c140020103002d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 86753148 1250 86751898 86751913
    0x10b06070507090509010203090d0c020a050409060b0307090204061b02040b0607050a060b010c0b0f0402012c010909020f040302090c0904050411011b020108060d0501020c070303020f211911 83
    0x70301507a22030860294801040c10800411900c280500070742e4080d040200291090b181c41600c112011580e190b000d070781c811f940340400142a107a034441e0a140d1400394401003440e011103000e15162241c558440d01c0c46610400c001c104e0b0300d61124058885100c42445d02c03900381903d0001601401d1007846059205c01c1c0091042d0801000040c0340710160700c6448284501440c44005407000022164041e0518200700d00060b804211010890b50040c41414403c00d182a40e00c2c00940f29280607181101401d1020f944148645e04002c40b280106442c04042d8a440303549903409606000d2448001e005141d0780c80800d50741003945040c1d030300d28807014008101624260a141115081020b000b5000c00c5440b0ba05e901490f10101c0001c240d0b41d01a16020960f4840c44184100388103100e0065549550034069042c440906006580046000340d006007803034a88036030250304040d80c82040700100c0880d41004203460b6600c6058075003078480c0346409806c0e410815029942040321803469186401201c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 86754398 1250 86753148 86753153
    0x20f04050102151303210507030b240f030402010c140606120303062b02041509050f071d0105220f060203070302060c16120302030901050c03010506160302010b0607 72
    0x18108031042642240d5a80f843d05528224002050340c040040d6a03030004c5003070109004402c000380700c10515a24406030902004c441040f6034042d02c01000103511821a0103207032070b014811031107184c00b890311800c030b07014100319030840b0b232149503080d60103003034080009425607010348228200940c00014640004844901c5180ca4000846802d48540c2c0c0e000c0000040d6500001501e1040381c0241000000d1a0481b001d030700c000106070a29443c05d42070b41c0a050060f101c5000b005030043c0e0a401c4102007606010b0210161035000780004400900c120400524540c4074071038540307040710058032a549880e040300407078044c414500810006483d001070411844a40700c00030f07040350078240a0082968075074000300e89074131880001400503888800403c005204110052401210941d44480c1d48007055544000032444141048040303540407040155143c401c4c01100c2c1d0001d09140080d1940d07040cd000a03400b4000d821201c425948903009000c1018000d50005030000701c002d080549424862 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 86755648 1250 86754398 86754427
    0x307021503190209061606020f040f03232e050708090c01030c1706030a0b0c0d05070e0105070602031008030d0e1908120907090903090e0609010f15020a0602 69
    0x1074811039002100c002201a10a03110f1003518011301000304402c0c600b10350410000014144c0a10540380a40c5c00c20401500304040e50081c40144200c42c1100300541c61810019240001318510940086a20803c20000b0602207141e41000040104d140342c40c0824105c16150000311803041030f109440c00c0144003034039800100041c4a102c0500032200100801d0004400740c5015021080100703109030a80144406510420742d803240e0058100d41040105499110003140f0130b90741c4841240000400c1500f1900c10301909030300640c2810504084003031800000c080384220800038149a0b40440840c3e00c0204006121004100d40402c81e621410121010001844102e100c461070f841848004000840080c4246050981051045083c50710200032200e0280000300318882c28042c20001240918991081241c102e0182d40d401e0703404d07030415408069050010300501c0c441c807910001080348800482100c000e8400260b002d50b40c41034025400d80c580300304050014020b500204080141460b00b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 86756898 1250 86755648 86755651
    0x3041815091410060504090f091b061101020906120403030207020d05100c030b10030905030c0307060518030c0a110a0509010b07050705150a2a05150601020328020307021503 76
    0x80842100d4a840b0f500a0100c0a01503100b480c010445c28030080000c46020b5114016510641c50302081700320050351003000f00508190502d00c01e000a207400d00415034002c8024203c0f102020003145020900710000e80c0901030140c200c2003c9824200060400d803080d010b03998580e60103000301c0c1e00d02c070041c40c000d41c41c0c212481c100c0340e0003031510608080d014401c1c02005801440502402d01c400030110084015200c0944d0540b060310040120801e610000c0008050a90103514001b81f1030030201080100000e103041c4ac01107a82c802d100c10141500040f501c1090300d80c2c0100780d41154030010700400d00b405055071100c5da1109801c4000240717006250000e10400d481107051f2034020340c0b24030400a070981c02e040400e580300c8082c8a440c1e4400d018051100005601101d21805a001c00d61211404c43d800310302250203030420b480e601200c0fa945408640c12001c2400510b0a02c40003910070003290712501400049501802220f0701c403603009208541c24290054103640e6643d1401c103450015920 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 86758148 1250 86756898 86756921
    0xe030c0a06110a0e0f04110a020c0109151718010f0509010605010305010315050c0d020a030209040c030209060d090c050301022115010c03050a2a11040506030304181509 74
    0x100302c01a01461000e0b01280c1c0d42d84415224842c00d0b24180d0f05200442540090464100c1d5944603120950621000a0005074070260700900220b54032800060403114070340d001c1820040c40c41000381203580c014195a40710400090052442c1e512100e11042140078000d112040c1d5180050440f20741060f5000141300d80090002400500e0703030755004400f120320905c800b401e0b640403541180d1480801380c00c10354100c45600d01890500540c0c1074450226840402c412000ca50700003610040e505040c080d9500b40d044600301142052107a2010031807e100d0012000809540ca142c11010406034110f103601804021740210340300c142040b1804400c0310000c28002c003074043d60b00041c5001da10307006441d41403107041c1d4078034028511a5505403103c1c1c0003d0200707405d00180c9100d1720302c00050500402006403203082154203602c40c1d8206020b144400c201c0d07003030081e41000c0c108042520000103d03030450b00301c0c0e070410b903000720101603000041100c148607803007880400c6000112250244c100a8804c1c0307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 86759398 1250 86758148 86758151
    0x3050108060906040b09010f060608010816060905060705010e01021303140109030c02120a02030a0c140411092205010e1b0705070303030c050c060c0c0f071206020a030e030c0a06 78
    0x98035441080e41d41d00d0102c0b918a19030b03009000050024855a0382290041040000030501115481c18801910510f4011000260081004100d03054080002c40800004460f041085034100b0400034101ea10600070140500d90000d910401c21109500c0f2a11546aa1000b107403111108540540f0f941c0340d900c400e944600c02d410002003002018440d610700d00b603040d04c90703010005c12542400b000902013400070800d800340d480d4500146e00c00340f1111303001070b2060703001c02a640e040042803060781c0d404030111401985410760075041c0320620411582001406ca60700906207006a400b4003107c0d1080082d0701c4510700300000020300d08042c0c200140503031846040d06403105403d54210b62240a41000601903500940e420000729009a0000007418200d1500501e40030502010701c0c9030103000c1e0303840a080400041d5400c5030010a000b4015aa03826101512480b0310703099664194004584010b8002503000900e005054007a901059811012000341c94541e1405808103032550a01042680c045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 86760648 1250 86759398 86759401
    0x203040c0512060a0b0a0302040c030906050702070e0a0e030f0a0504080c0904080d150b0a050702030706021504030318020a090b0a05060910050c0a0506041407050a0b040b070c0902030907060305 85
    0x140341000b6010041d031903810080000e07981d041300c0d1030080e1075804100e0760400300f903100120158456000300c44051110340c50103e4445d040d031400000725031009160030708542120034144448190100c1e22504681009008508600240600342c114821251403242a04d030010b48800110740041c050320880e1800c0c400da981c03802112080c0440150100d0300140701c0e2004011220f070205081d84043c010880402c00c1100080d100c43d00391300702d1751244490780c2c0400c5000c1071002c1145020080f07203018141510250145840c001502a030550015000034241a122114000b41d5007070042e0342c5011a800030140d0032840c1d40e0b500000000d0610201450144c0107040021406090080444100e000060607140c0348500c6242d00716441c0d0403110b903132003035070042c21000400b04604001d454010741c0a143d08001d181d61341c0094074030384045903106a000f41c0c4a42c008000e4902c070780c0b0599044503000c0c1d0300659a040e02d40313030a1401007050b0b000720441c588080300b0b000c5100b800050342419100140c50404c0756 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 86761898 1250 86760648 86760659
    0xb090f06010605030402121c030f0609060302010806010c0302011b05120f0106092c0a0203061c020916260601030c1701060c03090b04030b0f0a0b0102060c03060120010203040c 77
    0x2210340900072070001c00c0042002c1001800c00c14540b0000e01c61260640b40407030149a100c0c0307615120300c90750030002901c845410b0750307403500307882001d0007007444c541c0070030a05203164006015841d000b00041e040c0310300002b040c81450700070342208014081e40303801945007200c1030714040c0103074005454100001c00343ca030002d213440c15080c04803410389078952540e50304145000504041c0c0d09107040f00800450f507101c2c034034403038415a0141f40c2c0550f03000d400158403840e03d503040c460106140d4420301580e0f00009180005621990089504180e0000c101141072032203000948945100c80d6202c00304519003c0c2440050192840c0c0070300442090b0f0b81409500d800e0041241c14089582405a0040314100100034490055074102d420034402c2c1060300b20740d59503c0c04c1c11429003140d482640e603800d00208120700310b4002054240c0c807078160b01c0d0810100703000c0344c0000c0d65031400600070074000b0400004610140c0c016500c4207a8880840070181d0b0a241c0c10100d107000c1d40082e681190502c0d0081300100300f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 86763148 1250 86761898 86761903
    0xc030317010905040c17010e03030c0417030304030e0603130f050604051902090109050601020a0507030501020403110d050a031d0307091b0504060f0c0213090822080a020f030102040905040b090f 85
    0x2030340c000c0d042ca00c210307051001310401040c0d40e080c2440d0a650308c0110300030741030b8180003841c0b2070042c6c00075643c4c6030b520f030014401c144040e9103a0501d568004108000c0000e070000f01c070080c2c2c480143c4646071256607a150072a81b0041d03988002d0a1f00b145c00c80c0032070400000190f010f200d24880d405440c125043d4143e20780e4040c28a2100070f42c01100c0d01c0040c0511080c0d5445280c1c0040144107d0b51701c80450749416003400c1a0360800d0f205650002402d009005105400241240e030a07119100a03006944030325880c0c400e03804001302005149088030803081c4840508440d01c031001030554000d40d90f17071301c0403c0090020000ca440a01701c407002e05800c1d140200c0a4504840051300c03020b601c2c480c000422101004090301c1241d03c0480794042980b0039000d88105002e06103c0e40401d507581201c00703024004014024101c02e0300302e00049007480307038031000309005c84803d5041e50300c1803c0350000710009001e4040d607080a8140c03440c1004003c107004140c00b16501501740e00c01514402c0896912458 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 86764398 1250 86763148 86763151
    0x30c142e030509010b0a0816050d0201050403140c09010801020d06080303040308011a0f030403050a030b030c03030d0c03180309030b090304081c0507240c031802060c03070c030317010905 82
    0x22034454810001411140c00380c0c0001d0343c04404603000040059007540086c402941a80200202c0e40c40b02c20070000105604680d600501002c03209148600d800342d000900ca8400c500004010502501d69119601c0081001c9441160b005081803000d68480528a000307420020821a90070f0402c1c50002e04694007104507402140c1640d01d507402c683c00c00b226180d083c42c1e018440c80e41400104460310390440750b03d0241d8060340c0b0030f0303940a503250840c1d00c004003582c0715880f100b1310a4008071111100341e500001154940601d40c10049100c80c9556810b0300200500500562001d0075048901c00300b5500022030790550344510a10100ea460340c80c803c07650b9000d1030103824a580d110442e003024819040c0e410340c03020000381c50b050785000310a0791040641c501491441e01d050b0902044807004100e13034010201882c00628040040d0351560725080d840305221100a0300443c00010030b40c12029003030086070003483e0020040c0b040d4641d60701d001070134141d88902001100d140308002248900d0701e402400d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 86765648 1250 86764398 86764459
    0x406050612010b09061e0a0908240702030405060409020d05011a0418020d020c0c1507030801140109121104060f030506061e0414091605030607030903020304030c14 72
    0xd000d0740e00b41a10a90340d64400500554052024085001100c085081b03000702d00c4400300e8015100d00340c0c8640980500c4564010034840c0d0060011136800b040d880119030320410203901d0310034650b03c0b900c1c02a0705510983c0c00180d00b141c000140811640016001401031040699040046a03a15095100710701e00c40000c55032a80e00070001004010014000ba086e104410240146803419000d081b40c01ca9012021108003a000203041000d0341c60900034040e2208490b10003a0720740803041c0d80041203280140039941031503290300705403525a48940800e0740a0310802d078089a0490060038594050514044111300c110709103100402c040d480301c1001411282c0c403d006040c90b07241c03030007040b20001c242c3c100e2031b00300b102e17004040401d0b585500442d41408052021000c00b418441c7c1c115080200410700d40401003c01081004191800244554845420319002801003410f00c1c04904510030f9520140020000c0d03000480c14a00080c03d10007855021500c03c54012614958050f0b00c501c0705071300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 86766898 1250 86765648 86765677
    0x6110a031e0e0a0b150d0f020103140903040302010809070906230307050f010806150307110c100903030f0c080d020a0e102312090307030210060810020c100c030b04060506 75
    0x100008503244c10a540200395900061031403030340076020407114181004207540c0500100b445c84c1c01c0d542c1500c200901c0c44400c510503d154604041510780d2441a440024100845a400030b04c08503014003103040684004c4d030080c001650b0f01c20117015183e00940702c0342803103180215400610700d00014180200e41014220701e002454203001520254401890541c00c104150f25010640408a0041d0321504043e100c1800300c000c81800f0924016100464501600c5000240b00d80540c01c00003140132603605260110000f0a8024100d400c510794400c020003110700411420400d80007030300500314140940d502e83c01c00c0c000307400070401c50303130202c0100c0b50224407842c40c20300700d1704c1d01095101c2240e80080c12052410480507007901048508071075000320382d0400328404081507030501500d02c0340b80b580402400040e080404c05500c55611004c400d52140e03000503a00361002d024000050140d040400801c40d00307042c18030103030140ca00444814442c502d80500821a4503000003552902c0c816040c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 86768148 1250 86766898 86766913
    0x3091c0c0e09010209040c0f1b05300c07030308090a0b0a0e0a0b01150e03061909020f09090606010206070201060b03040602070f0b151003060605120406110a031e0e 72
    0x640100c1020342142c074155001c00c5a040c5540321802200f02c08580380c1d076810034010031107400400c0c2c1d0690b49408140e2444005450001c00c1c00040c02298000c03002402a07000c20740c9941c1c10700e8040d03250110b0442c0c802c020400044a81d8085050302c03c8a00907164464135644145909448401d5840700500e0b80c8881c002188490213144e01510404210f501221128012500c9815268209903c00c55404054485100d506544004050101841907004000c1410112106990814100148420300e59120f010a05640d9442d01b24181194003802442c0c1600744008000c0c2c8814044403098094420307500458038560bc140700b50750131038065020703860454903103a680070080d511920b02030b90241502a8050082601200481c0c0102c1c0d5510002c20040c284805001d805d05000c50b0410501d41b900c04104981d6801c507003100c0c2c0f08400c0d6a02d02e481c42d5200c1c60807000070300b50600300c000200000b084103070042c0c0d09a4013a407140c42503025003101d4111142402c0c001d40341e03214900f61542e0060300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 86769398 1250 86768148 86768159
    0x103020306011704110618030f07030b0412090b0309010515030f0a0206160b090a050106060302190309050f061806150f13140c0a08060a050f100504051203091c0c 71
    0xc3d1041e00300c2d104811032800000b0000004034280c200d50102a803140102c0d100d8022403800b0407126000a06142c0a044002e1651b10380703882d540b04c010300241c090106605541030f018814108000500031406d00300e038403810105041d40c024281140d1303a400b2042c3c83c044448c840e01d000140c980d09021000c004111040c0194240080c40e081401c00945818540720340b0070009156106140c4034441900050843c00f25070f082a43c20344066611030750030304d0b104014000d000b100c2d03148040c10b041340c5801c0200d0200c0503071524514004914001c080c49005000c00d102028508400171b003103001054044801a407101c800040c501c80d40513110641c40794000c1c8e05001c5504110416140d003901c400400541c100c0608007100c0502801c40700d00070002d0000840d202d2107500038024681140b41a640e511a42c1d080c1008104000b1180d01e2140c45a55013081c0f80003110300c501c1c1110042d243c080c01d0240c8038008608020703030b80d1b009001054480c00c0c240480c6001d800403805011045600400c2001011b031508 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 86770648 1250 86769398 86769437
    0x1050a05010806071b0f140613050c040908070f080d27020405100e090c180f010512030706110304020306060d0b040609061d060f0105040c140a17180c010302030601 72
    0x85c1d07044040c1404c001c00f501e0100d030218a0501402d800f50007600d035043c01d5140701c141030220050401940103407507414040403c400280340390781410309580008948a580c10090514022204000e056006c030034031031810003503424003500740154001820312884403542c900c0540389401c40a040c4509140070340840c05850300e0340181e0b17000340703020044030a519124810903040c6141140c08113581d84c0180310020080c10b05070380c04030f4444a0081c520449003084070360143c880006100780c900c11304c0c81d2440d00180300414401c6425459001108000b029103040d60f441c02c1d0740085400764800d00807800003d10a00f0300c0b9407030346030403a444010122640c0c3c41c1d541d01002824442415181d0b00d42d60400c240010340b09031459407442100b00001e20b4246000101c107421458142c12960044d401c20f91120300454100191904680380004810b81f11020b241044034085c03410310003a603a0220500902808004540c0722120061800d42510101680007006605a01c400e864041c0014012004543c030000314 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 86771898 1250 86770648 86770667
    0x2040902060c1623100c03052a010e010203090a080d1d01020d050106090b09060711060a0c1103012c0106080d1206080705061b0309040f0e01050a0501080607 69
    0x200601e00b80a0b0140d541c501d0440b11122900c0c1081c18040180302034159115420343c482040d0000d800c0c0c4512000115040801203045d500a00003c01c50302420075010f90240c641402016880101d40d41c042804c1e180d0644d8035000341d4143d9403814a112043c1501802100e1180316138100034032284800d55035020b0113601030345410000c1599040ca04841402d00602046d80714020000540c8400300c50541e00203c5038182d00403070a01240010811030081800161550804111040780c1c80ea070907410501d005e89901c1034003590083c0005403482130990400001c20089004251520010300e50400345402c13a4000303103d064082b150103502c1254004890008102452040f0004c5a0290b1310816207203000d01501d00b44000c590000c0380003070a41203901c00c3c5401044180c00a003d80780c45c14001c03c05911030b0140401d00000b00503003428843c50100110b50405402400c200000c0c1da441c0d0035003008081040300c2e4903041d42072074003003940240a400f56606a40306080588030300d4039516070568000c0384 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 86773148 1250 86771898 86771903
    0x30708010512160f1d070210020d061d01080f03040e0109020a111005370207021207060c060c050a0e01030203060310150e010b0a090302091302040c0e01020d0504080307020409 77
    0xa04501441c030412140f1414004200c115600f030000360502101550341141400c040f45080300c44002c1094203039002481e1584d80240d00001030766071441000c100c001d040c09070003110700c7c03650f00311603400301a2041c400d0504a0b07004809031800318601110b8507440340308034407604210050400052121218903401001903422508103528080002d401403400c01075000f46910b0322aa444040180800d101000c0d088003481c20303900e41e004450406031030300c200c00e05203450a0307003680c0c04610b500454541c1c00810495080510072211070640c0d52400400400307003035000700c032420700b40346074900e09034000d0301952106d46854480ea0b40b40020140110007d400080800f42d151045000c40c01c1c9807505481440c001003800010420003070b042007040701d0100810f900c054130501082141c1e100d025800a901420b480d4106ca02c0421500e44050a040e072821a03c0041d6002d8582050034040c1a0080d07009a5151400c0c0c0988407000c2c0c03098000c2d40c06000301d03c10b40f101a0410800400145001e0b8403929180d0f1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 86774398 1250 86773148 86773153
    0x30601030204170a060f060b0d230906070f0c020603040201080c0421020406080a0f0818060d0e0f0304060f080a09060c1d150403030804020f04180c0b030708010512 72
    0xc3d5625040080486440f0450810341c02880e100340902c0301c6070046a480402002060080500c1c015585c1c00c0c901c550b01d2a21a40f60395081600d04105403204803080c004807481c600c07112424030262503134458109503218000b07d08292060740105000308090003506800030305241c11075440c0d80055401c10b00042412940300b10400020030a200c1c1d8280c40c003013811690b940100701282e01e20600c0b08031481c640141405500c000851400a05007400300662268014503840e240c0500c5581e02001d00194223903258050030205000f48508019801082c81e0013003030089270513809100d1240c41c0c80744070b00c2c00360300001442d604501d0080ca001d10320702504040805000501d4020350340307030700c02210301283c07070400001c0c0ca401c000740c4648481e0f460b454a8600c2101d1420f8000e401c3c0001e99020701c1503100c014203001c10900054259542c94506030a1400c0c06003051089480c10b101340040d406400da4101d8589280c1c000100316001d032203058074468280d0b03440b1800c06909290800a0031003080d0b42f090b5051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 86775648 1250 86774398 86774407
    0x9090615091205070807180509010204050307120f02040f0b0f01140904150308040305030406090605041508060d240c050c030921010e01050711010207020307051509120f06070512010b0306010302 85
    0x5030100704460040003079004030348005042c000d0f0003003610230282204107580e006103c10b003c3d03a500416088100d6091100c2155942c2840c0f0380180d468400d0714010f9802407414000070302d00255504070301d040e14400c5807144180b42070907005640c0c0406100501081c1c2c40d040c0410511410700c0c0c0c1c4000403884104c103c00d00010381e2592600c0d10781e0301c181c0080b41c4070b4002140400041350000d03400d8020301400c0c00c01a0500e41000482d890407030f0072100c80010006c0081c08a40f03991072700040740702c460703812010510300080c1c0032350000e21420050011075449031410a402d04128401c006440507401d440e0083d46ca0602c8450402150960b0300590815a0680f960041000002441412044000f290000c030726460000c070042c0c424205c258200c070881e4010030212005030780109020042d20400c41c3e15107541520400d4500e8240201c441c4143c0040c5121030280707a030600007503240c8100e0311007000c49070309036250b500498072400b43c119030452402100d8014041c0d40015005150312117030602d001806e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 86776898 1250 86775648 86775659
    0x180616080f0d0c020a0b0403030908090d0f1101020304050105030145050c0906030a1d0a0503190e090403030203090a08070f0221150903190909061509120507 69
    0x31588099000d4209010000b21070042e484036014184a9126a002034002c0061a8a60b00304500f0014030013410035543e04404000c205001c03003590304508015008806103040340c541034010407410303001602e003503080740590010b542c8000100d50a864041e075920781941d01e40109040d2059441844030000b2085801100d1084640c400e42c601c00100840f02c0d901e814642c0070404116030004e841c0e08442c4100300f1a610b0039407544022071303800030b10700b00c40080c030710b0186072040c03c09460214040c40700340103180c01c48082c0b000000245c151a15004891301d020100c5200a445c042841001c5680202c07900f03002a004c41e0082d0702031540007038070a00752804035030103070342d40016a4081d4070b01b162201d400307514a20035401d0206103030740b03062032200728600c1c890261050789640708600681a5260301d012000110200010300644015448150611a584125040241080c4d20030b01896400a2400c1b800290340103c0c0b81c2c1c0a000c00d4010340303504200c5410301884c20552203403180103864501ca4007c0000d074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 86778148 1250 86776898 86776913
    0x3070311010e0604030c0b0a02040302090c0702040e0d020a06050105040510030b0c2101092301121103010203040303020910050403020a060815030a06020c1204080c0f0315090a0611180616 82
    0x4505d1003565482d843c0f03c4d562030809842d42020b0007018285206020510040c1c9500500c181c2010f20b211140b078450b2120310018006d070a184d050f04055000721f44070031810903000a0725070560f0b4414101400075a0702c680c14801201c20483d000100c1e042e0040c3d0030400319002c190401e030004d240860f503502e000c00c55404003000c11614201444024400001002050018810540c5618001d16060406550100941065a41070148003981440344030f5007401c020410003541800000940295101d2801c1d040c094020740245c1c416900825501681c0700314144640d04907016660b004010707900040c02e00004a41c0784100030710700880d0580210210100b40d80c00c008444403144107580140c0d07140b82c2015010700780a00c10400040200b803d0000b0b000040d40841d00601109040d2224100b481c0c0c20800a031400c581c8080d9a07040c03c110001b80030a000020504040041c0500380c00c1c040d040b403000704101d46201d03001d808050038001c80000b100f540317880802007139804006585007001c400c05484245 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 86779398 1250 86778148 86778151
    0x507080102041d0a090201080c0c10050c07020102070f03170a0e060d05010312261302090f040201020c010c080a08040206040906090207060b06040f1e090507050a021e03070311010e06 80
    0x1088910000c00300f400c0c000909450319440200c4690611031002582d0001c0e0000201030101e12140700d01184c1c010031000e00308104294015440b41c240520704016155a000f41c1c0107200036801030041d28408511040c081c41b00c0c41c1102da00c0b00d02402c20b02903511260341950880c0200904110901501484603030310480a071200c032149100c000388035450f5140010b022a40010690107000a814404688007010040b846502503142400c0e101aa1600d4101c92401c4107079400940c800d03008014400d11103025490140b04500c01c0c2c00700d41c00b52020310300544042c01003150003440000104a102d4040b0b1003044030640091000d494582001d4880d0500026285142c00c86802c0c1030b0301280003c248101d40c010078048000c00c0e1000351416044c482c0807000d41c502400342c48600004030103400c050080352102d0400500f03113403c0030010b504101000500c1e50740252000001445011140500c610b901e5105944560224000394605034881d6000e0301c00c42e00b4400d0b821420b540e00d511010411a06000c80c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 86780648 1250 86779398 86779409
    0x20607030209010e1216081c05090d021203070302071e140102070807081b060406020a0305030c0d05010902120709081e01020c070609030309080d020604060f09020d060209030712021507050708010204 87
    0x3406c2c144805130003419074100d030383e10840c0140d000464140c0b040d80040600351400b6018a00b69540e80e0240000c2a4441c2d000380d4000c0d040400e81000c41054040030024081041c4240d081e1032480d95501c0d6040c183c2c015201e9103910b13100c08100300300a100da14030f464459205060050b01d00782e41ea5101c00c0c1d070500130564008080794100030356007146511259880e125043c0e003241c48604050400400954030407440000a09000c070000105032013585400a03100c030007024181c18800b941e100d0040501035000404250700e1440c044000c00c60407401079001205540340e080040c4040e44245103406164009080c1741c2500d035500701700040550b242400040c001e824291240c2270340a240d441d000f090248a90302c0a0581d03001901000c2c1099404a40ca50f00650020408501a07400c0741d48d12005040c4d105000354001114403078601005290b070090b103d2444101d068440580d078030307030280342c0030125034900940c40852101c11103d030301d03040c002404005008004035518075849034034141c2203034442c0c3c018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 86781898 1250 86780648 86780653
    0x100c080106021509060a0e030412060c030b01030516080604020702040906091211100209010512070f030b04020a2102090907050c060109020903031801111501050301050903030403020607030209010e12 87
    0x60080d82e80410220381c3d041c055400c00942c80c40c0240b0043e8440740090151024952150050120b00000b0401d82d000340801214a07a00e1200d0352034050010305482c00e201002c81d0a00c00580c14070342c080d215140c400c00c01c44a8112011045007002c541d0153b00820040d4019030901150004d40c444e0f00c6a100114850240010310940c0ca00f814401035a0080a4800700541c4120307070410b0840110b0020341412140c000903031500109001070701e55000d01100c81e69078040e140200000168031090540c1c9900340e5450401200c00801c05000982c400c18480e10003051546042d00a80c00c60450081007004c1c0c88100107081941c1000003400c100c04c182e070040001031000c42c810740c45070410b0010500501440390214a8050450f001c6900c0740915030442c01c81564061307001c00b03264010b01403100c405640700143c1e0525160f100d51a0310104080c000c050080d803a010018080342070020440380203c1d0150028a0a9a1070042c12400ba500c2604460304020201c025100952103140c002c410340c4900101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 86783148 1250 86781898 86781901
    0x40f0e0402040506040e07031707060c02011b0e0303070b0a090f0b0f100e0c07030903080d02070606080c0604050d0c0b04031202010e0601052d0913021903030909020a02100c08 77
    0x40005a883c013034100d0740f25030305e4280c0c103031410280000c620f8200d0b540300c03690344012601c08070010044e014640d400781c0000d0502c0010401d096040d80800b404000390664117400542d6050304540f801c00c1810840c8d01984100100da011401086030340d035002800444c045070310344070381d80d40204121195a0440e0605500018840d0348811102c00300c1e03000003140b06035510245046c108114582c0e01030a40e40d004000011001d0a0600c030741e4603580590342100d04c141c3d4074020540f15000941c0015001d0320460300d429008220403c003c21000a1030000038401c4d0f05060410041120403404454200e079855074585000071074403000c5010744004c40c0036100340c40090048c800c0103401e4400700d407201c0b2489d4014400500807641c80c10083c0380d000000019070302d142c01002040081242c0c0485015904c404880d0810011101580480780c0d8a031082d80c220f005807642c3c5880c8005100c55001c018042100c2c0c1d24140b004e2480c55001e0603806020744111160ba001403424001125900f060740d4001614000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 86784398 1250 86783148 86783153
    0xe010e010c0e03120310030204090201030902031b0a0812030105040509070915030c0e09100b18040c05120607051c0612030305010503010501080705060706020a140310060905041803030b0303040f0e04 87
    0x1240104c440740000b4071610b075141040407132800c0d65180c08000d10403a0703902c81002c203592003603000000c0039502030122800c0034030405101d41a6500f10301e4031441900c55a002040d0b0714004035040304004180e428041c196401c280c03c1102410000300a0b8010b48101c0c40002184585402002e0302482021501040f060660500942612454000550070762180d402e01000340400100346a0314090020b0015021204800040b10581e03030000c4109850055010b110510540303114a504503001242c0c6a242a200c40c0d0003903455000c120f030102e0200d2030500050688407540e9000c1081c2030003200d400194151250100140d0741f07881801074001903030307810060041b0b040900c03859025211704030041c03042d80e15040c0055031503c60094000e00081d00880c135080d038180a440c61100700081c0042040e241d1800300e607410049140341c0309400000e82e07140300000305424144030310042030f0040c01020081040d40d0700e041d806041001c20b00b6415100070400003440b1401001c0010140144010841042c207003070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 86785648 1250 86784398 86784403
    0x2062101050901050a12060902040e03040b0d0c020105011508040203070b030a051005040b060403080903161206050f070c0305071703150117131b0504050406020919030804090e010e010c0e03 83
    0x143c02c100d000341072417103050000c51105c2100c0707114560310401c045400003091000c100030384045003d0b045288000b00d004103002600f000900a44219000b0030070000c81e0440003242a28000c0c42a0147d201d840140301005a100303486140d800740c0044e00310341003d60388002e036003220362040b51866081559202400303c04000017481c000280310440701800070b41803d00c005415480b40c0d2000422440000481c43c000d5103081c01f10004001021413010b0600d50f0f580000c018002d1290412600d06140800240d400d0450705121402070003140d540e124a9141c555056540e903214010640e801d90400c4400f04d2110f502d00001c1d03100c1c50545640207801040703000007410720710380d080450041120741010001691030300e416840e8119080f442d0100040d01404401c0340e1020b00760015900706003040104418003655030020016580107489004003118001c803014292045400000c000e41c50400040002281980001c028941401e0000a041c0008002c242c00c407034825200030013046c0866080191032905 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 86786898 1250 86785648 86785651
    0x507030c030203062a0a02070f081f020301080a0b2502030d060f0803030606162a08030c0619060e0f01060f0507050c06070606090920040c020a0f020621010509 70
    0x149180c5071102c05c0d00245000184c00c14840030703a8160307004501d03030003014401c1108a00074030100e00000e0f40d0f1078441c0d06203170700d034200c2034404000310380500109101450203100322812100c070300011340082c4c040c0d030380c031842e0201020305100300744440082d41000702e100c0d0050060341a003403500195990b202141c2000e060b03a585038007481480740086010000a41c01000300c0707910502c01c40340d90340e4030020950345006c040705102020f842040c1c00c08610709203410181060300c034004007072040d140c0c0035610010b540da0f034400c0c010401c50641008011610602559040035103d000c00b00740881c0c6907031103940c03030300451100310307044c89200131008010098176410440c4500815028600607282c100251110703542d3f0b400c044845400790200055040522130703244e1000e0041c0400400911084a441c02d04503103008e414584e03d0450700a00005440c141343c0f80c071446507001440c0c2c01500c564202c5032249039100c0545d00c01642c00410400c154003420040700e94038000c170300390082292800e504010034000000340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 86788148 1250 86786898 86786911
    0x5040b0703290a080d0309050c09012322020306120118080a0302041503090b0f1302040902030705030d05030f060a030b04060203060a0302041a0306240108070c0507030c03020306 78
    0x580405000384022415480c408050800001c525030802c1d84080380741d40d80141c0c0704000c1400b611000c540c0e150b0f816000070320b01758000c100302c0c1c1e00c0c85941403c0128004080c4a54240d0304045420300304011401d00d00c0100e0b500c0000c044204100c4400343d03a0421440b5601108407003a400010460540380c984507203171f4010854170003000800b43c05080c0c003100306c410b1007024048540200b030002c912882030f0100e6004d440758480440c1e0200c0303400b50280251100c848116400212500060105402c849a45204d9400128a88112009a0207000c0144100e48041e81c142c09006030126044c0c27070400141100c402c940c0d403001c1d0b60f03281080f045003803014050320b450300c6811250410408941c20301e90560308550007610040c1d4176101e4400240b0707c0c03201540025049030409591000c0c0c3c07141d00c203200071812006e80942c0c02d5a56a402d402080344000b2004011841c03401b800402d15510910995501c580e983c00c01004002c0c0b40e4484a1070440582c1c41120111111a07042c0f0841c201444083d8002c070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 86789398 1250 86788148 86788151
    0x70e1e1c02011b080f18041a180c04050d03020102040b040b03010e09010203090a231e010608010501080a11031f020d0b2d010c0b090609060c1e030612010c0305040b0703 74
    0x7400b603581c41149105590f041d03c101791001c604920349481e46001c22410b5400180108050103041c0e0404e8101c8181c0c05620307104200d0b2030a10501140002d528034850301d8045003e91400b42005e0402000301c401c80c00a408542d401c1c000442c5045402c0c00400c050103024014544a40c98032451004100000f06404900d03401402444104000042c8125983e075110f02c1e008140c12207008101a0004503500c85000c40c41941000c00c058101c0140300041448014000d02c078141e15040b1242c00e81c0c0e0281f05440d4564040d030014004201c034070060300d0002000030191900c490500c40000344c82c82c404c400d5182d03d5907001030564118003051045401d20b0300c1c241d904039449190980b02e81071502018000e002c112940b041c0d02c213100d078800d4100c0ca541c0f5521003d401e0143c103284e050a03075903120844565640f841002c012410b25a1a117082c3c500100708000400b10300c142c548841c03411504064501e036080040c03108141c98811080c09600c1e810041c07903500290030301c3d180c2072040d804600035100f8010706 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 86790648 1250 86789398 86789447
    0x10b01020d08011a0c060f1f030201022d0303040606080d0e0105090907020f0a03020105010e0c03040b0103150f0606020303040209180304141903030f020c030105070e1e1c0201 77
    0x403500000b0321811240c00d400d20450440070f0701300110080c4100c54544101e03004407810011000003c65095009441d40c90795124445002522409851068003002e8056800034010b80c10340310342240300c0e48900741802403400701c8072150400d4500e1600103032822107806848600c1071240c441e00300309112241c02c03249010308180000d503001801a110308822a0300a0100b1030006414900810a00c014100700c0011103c10403e2414000c0c000c06084c000c00081032000710119400c06040019a4000c43c0c110410340c0b00c60f4695510000b101c0f181d20b0850600c10f440b546069401040c91189800403d05038002d103503130380f42920401c00700410007048110354041902640003c140c001050300e050313498000005001d4580e000001d4014030760f5403818450008407003000310030598082c500c030000c0300c0b80707800301c0d080d003501c032400c140c26250116182c2c0300203240355183d000703249424124600d8404045c0c0c483c43c1c00c0300c411303004a66400200c501950034204024000e50071544e0140e8100091320f40c2d0501020710 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 86791898 1250 86790648 86790673
    0x80702190201030e0f070603060e0a0c0e10090b040f030605090a1104090302030904020d0902090108060c03061e0d0c06020c0109032a3803070c1506030812010305010b0102 75
    0x1460303045010341010f6860580c10003503441084a40740544440c412200302a6031403c0081c0500064042e0309004034000300400c084c032035140034500000c40c66444084040c8090380900010440030710b0400100000018005448844203001f400504209500f0148540c1182480416a80041d041d1107075903104132441004501b0001c0e681e04004411100400c9a03042ea0408034130354000da0000c1c0b031344a4400212821245440d60009001c85d1090310180203d0380c5c0d9152044d102d00040350f008200001c10030001e41c8900d81031035a0606061000300014079144001d01084c514464600d0855000c41c2804041c80459010850358540a60919007054410300790764586001009070580c03508001381900350800c800310980d8984029108004a0001320f85084030b041c20344500f400c030000161040c041c00c0410f140100001c0380d114804030384a640440e0042d0392640f04038401e184171070011540d0740d01c0c040001400a0014402540311160302c40dc0365040d402d0440c03c507222040d840b415540601e54031441e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 86793148 1250 86791898 86791933
    0x11e02060c0a030b0a080705040605060a0c020d0f05030705060105011404260304051203130b0906031501030e010906090b01050a03170c010209060d090b09010501271b0f080702 77
    0x140024401d140c151500740001d020b0300a89040c0310341c20350040941d00702080508000a40e042294001c440a004803076590b828014584a04c8000702c0000380c621840c0409070400d9072000e160380307214111020844049444171419030300045001c0380d0325000781004115640c0c0c0700442207035902c000c0c07000d5480d2174a0000b051000f83c0c00a8a00c240c0716022042020075800c1c20310580f4010180038010010b000040b00e4032a03101d40c070110b00741c2460441d2035404203075203403480150340001201500c2f252840d1180303d810003440b51044401d07410140c4a5500d17004a960a00580f28031510441d000f1400c02080d1815080a20058110074040e002a40080001c2110f8202c000c10040180004950325a0074031030441c068851140c003207070000000202c42d420142d50398805681c85004654400705602c43d00c0e80642600c01c01c1c4216840304c10340010b0540741d055416901a42807902c01c0c000a060035800100c5224101d5000121000c9401d04015035a0305802c6941d05034801c4861003e0140d40c021034001e902d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 86794398 1250 86793148 86793151
    0xe0705010f0309050a0c0e0a1104270f0f020a08060f060405190308040e01090b0a0305031804020417071503090b071b150b0f0301060b03010b130909060209011e0206 72
    0x4043c0c50f561100240101800710f460083e0700031a00715111600c44444005600003a01e1808d10f0030b2810040700c44440328072043d941a541c0700d0584180a078003102c05002c4030110032003100c029555a14028054118501c0f940001c9a0003007c0940c41d154202006004203000401450041481070140c0d1500d0759050201c405443d0304450380790b42142c258040b003800036210340000301200c5c0c1c00600440c00002c20b0740740700c1c12101c241b20188039005031030040c003004103100d100c02400d030b5009000400300b070441c050141c030144801402c010b00346596015002da801c80c03609250348540c0c21503407090002260081e202c0c40c1a040c90700742409070011940c1c5000c1040002840007040207040d244811680308009401c480c056041010060400080a0340900030a03800a070b5622801d201d03d960a4581018051701c0121485507505905580c44e003c0761031540e91050310100300c41c1400150100311070b10740f0b1142050981c018840161546544400517101040c40c5d0100d011035460142586101340c0d0004885 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 86795648 1250 86794398 86794427
    0x5330109090f080705161e030809062203020117042001030f0504030e092d04050309150d0501050f06090f01120624030e0a030c02010504030b0106050705010e070501 72
    0x84400481c14007950110b442440242010360010b00d800a000e800540418100d45005072032820310341d40e1500c484100945050310a490010701c00401c04603c1c2c03803004e0060f01c040680101c1c0f822000c02c60301e00b9440f480ca1800768107082c1c1d0f00401d00955138000300c00116103031140d4850080781002d80360002030715100448040c0410003080000d280c0d0348a90800c02e001c4510840500003401c103894042d00c05a880041c0e58015000000001c202198130844146460130880394141c0700c810743c80000c2d0b83c1010040c02500d561004100440b01a00c601006241c8010b0003001035448041c0ca8404805856042c0d000b24420380702c1801000c613030340d50503003283c100000c1104c160002ca090480141d070440e14112032400620703e002030020f680c0303041c05503041455071025611800d1890900058003151411488448181d000c0c00345240041d0240384100c4103617005060450600e5640d5072011004202604400b00003500484c6102c1049024001c0304003050030381d40503010042c10100001c1800b88000c444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 86796898 1250 86795648 86795651
    0x6020f0307080304020f18160f0f031503080c030a02100902090a180209010b1c05010f1707241106010302060a0c060e12070203060906060901030b0a140405330109 71
    0x105017150385001d2842071680000c0c0118101c0300030707005245184071040340e01500f50700c1101e02018504e4882d45020380419219152102258520202180100404a0031030800c0c00d1117a40403000c1004040a8115600c00600a69807260344540090809000c401022007150400748280e0041c0c0e2000401e5910503040e16000480e0101035040d400f03040058507008c0d4104010b04004248400081e00404c4403056074a030f405002e00072070054808807002403181c8140303400031403828446080300b101030118040c050001c5804242c0c5800d5070f0208080c1a5060b100120000c280000f0722903004510801c0c00551003028160035031442d000300e101032240c0a040010004450044010840554818600f030640d141c100c80c42803000070407405607a8082601a4441e01c41c5400241140d60006803140c4a03500c05032002d030491746503a8561541d0100603112035070094503401e07944003069000050340d100d1030241d00102401c589843c1c0b0021030780001c0c800001000100540a0030048a1a030007034112442607030f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 86798148 1250 86796898 86796901
    0x7050a0e0f0d08031f0503060114030a06051f08030a1e0201090602130518010f0608061f09091d03030412090b07080c011802010f0c02010e06070501090c06020f03070803 74
    0x11824969000703096440400321580c00c05024400d00130b1482102c90040c1001c0700100003400b138503240600d2003010b034964410f00c0144031180c084c5001810075034001c0c08440080d0704a0ba54001510400c4030104400054003071603901c0c54411074400001802d140020b58a001040800240141c0c030090410502070070005482c0001d5200b54003003842250001402c40d15142c40c5980c450012801d40f0506100b00c0d51149003030a00720800780c0160484074001c5141c031080345400c5007503460000042c441d6500241d04c4914401c06c0142130704400254171550380b05403005060160400488104000192050300c04160310184003200008603900903820920b8241c0100d0003040c201c59001c201c1c1c01440a941c1c0105010b42007103501c50151010244010090000c001040141c5038584c0b40304a010740014016003a5500050243d000f80e03898a0042c940f4100e2041e50b9408503403298000c10084a0680d510507205080c00084000c40c00680000d00c041c014000300c07510b0380e6540340603d84026080d00e20000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 86799398 1250 86798148 86798177
    0x80106140d150b040602100b0f03100507030216030c0213020307020c06160c0e010317030402010c110307090e2d0607050c0c1309050f0601230a030501020d060501090e07050a 76
    0x6609004114441110344e070b032521024004d454058000da1030390800e003891740b420014070706001450b8811001078001c0000907a90b08000e4003034103000e040306040c5a0300700202e0481c80c2140c003c0b54812406a03e030517005940c6881404041205071503940c40b03591040c814403860a501041004091f401211841c5d2108030310708180c0ba12250004000f0040602c02000007141110001d10a0480b03010749456100c0b42ca800300a81d245110884000380007800ea008580c0001d510b2820f240d0321290040d04880d1a00c2c0c844400e81c0803115101d290084642c4014015450034112250021580702c46800c280385580b0914000c0b6030790b00c0040c3c040018448007065689030581304000d2903005802c01056010f0401c00c42c1e03c03040c000c011008083d80d02e80100c0344002070080000548074100d4014413140c412640c01d80540c0402150500720a541c46108030701c002010a500740042c09002220600014805181c50005420340115a0000d54040d1041003049902a00007054906803811810315405242c05272 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 86800648 1250 86799398 86799431
    0x60b040b070201030e0a060b0306010f0b0904050411220e0102040e011205030c070f18050f0424050c09040c020a03050703120905030c01050709050a0b090409030e0d06050601080106140d 81
    0xc680e1122039214040c0c06c0014810160400440f070841075081d60010b03601c4030b0780400d03543c10324012206002010082982182803d6000340c2c1d01600994040040b888604c0c0040c0b219800300c801500c50307403041d014480c9501054800d18480302c6480c03000f18503042c5007403802801040144a030310780759280d4541010900905204450708190b81005030761005884074805071803c02680079030310501d20341c3d03e905482640d0038800d05008600484805000e9581c560b190304400c0408100200396003e07200031865014600e0050741d02600b44c0d40300300d42d240c03481c500600c412554070709884021544482144c802098200044800458141c50001c600314450702840d40500072620000b496803000060140b021141075100e940117144580d50051a1907070360b0100294081c05000382820908100301442e030354a0709500148800d442402c188c3e21a410b640d0004500030207284045d00c4d29502c4604000941d80e0244065000d0f00a50030003008401082007a0941ca004070002500080e40e81c0c2c502d0100601c08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 86801898 1250 86800648 86800661
    0x504060614090a1212120c021e0708010e03040503100b130b04020f030703050f090706270905070f0e03070308030406020c01060e0a020702091501140307050904060e0712060b040b07020103 82
    0x72102d01545130024a41005088404940000014a001c1003504405002d028501002000d03600800e000d035004900d12443c50f004540030012840b45800000e0390101c00c5c040c0480609440028580781e601d000103150a080c1991141c21003103140c0328070010349640d01a10446403209642000400034409000304e0000c1c425003031890380c000f070003208200c59281e05030403c0e84151104142d44100782c41d11400e4907030f0307807170b1314002d0700c000c504401da1030306201c0805003094001814001c8040c000c02e80e04c0034400101c440070394501c8001002101443c90031b68204000c21214041607004040c0301d481c2d900e60419500025000500c9103400007a660303c004025041075014050704000c0485908182c0741a8000f136020038030407030003860108001918002c040407044030900049c0c58044610951032900c0200b6480141080103014091000c0681615648241d601610900201c00707480d05143c800908000520b50002c0241810901f05022808400d8160760845a000c03211036100c004a10041e07010780803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 86803148 1250 86801898 86801909
    0xf1003060f02220807050f0409021005130b04081b0f0a0906080d020c06090906010c05030703031a060306030a02010e1809010515030d0903020d030e06070506010509010504060614090a 80
    0xa00e031504280140c10b50041c0080310056a6104903030f920b400d180d056419040c46941801c1e00180d50800c9181032420800000000c0140000f80c482555070024003201d1000c14508005800810302440c407056101c0d058020788009010743e400c1a1400d80c0407540c0b106411116000040c4140010360702d501c2d0b1000c4d540a61000402c28400380c0c0e00c03401104010085407003003100a11410f40b0302640d06001054148850001800b014507051ba500c1c140035070008040c0800d8100b100403c1d50b02e000c92414400b601085209550101d001800d090081019191042c84144500c04c10410b224240d82d0004883d43d41e1942800d2091500780784000081c140c550f040b80b2500424002030800845403010340c002c1e80b060130180980800d00c2684014181e480800e14003410200b41e14003001e0016180c41100811420305c86e207400d4010040e00d10100341070750042e0100311400d80c4031078014003561411a81090142c942034078100301c52031400800400e1b052000c0d15402900300000345065a680300e80031848094035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 86804398 1250 86803148 86803151
    0x17070509060c1b0312090105180f060301090209090f07050d05041403040803040f0605030103080301091e0216020414060102030a030e0717030403060609090804030602160510060608130503030f100306 87
    0x900c260003200d0f44003482d07100b032403090241c461407240c0e04540209071017a089060350381900302580500298030111072012281c1e4440d00301c044400311941d416006501800844c50f000d42c0343c1a0141c18000c01410103415003e800c0c1d0035504000c403550780070041c0c0d0a9041c1186022405854900340072003500944590100d00340000038010415035030020041040b55032200081246580c1d6240844413800203010003400407008200400000d812034014a118000a007050b00030340704610980c4040742d1103403480e140c13281c280c200000150300d024403481030524459255002c0b41d180c4680001d441348110040741d070925a42d0420340056920401010014100300104490603000101e4030f0741d56500117200031540d01d41444c0b0045490308d00c9024542d80700c1d51000c103460070b084c215602c00009e908501c00419000c0038550780c100100d0402c11814010818080000a034581403a41c010a119402048200300c01c1000a4030400181d000003103075406604841c00006a85401c840020511441c0c2d00103455035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 86805648 1250 86804398 86804413
    0x90c0605130e130f0c05210d0309080a18080a03020105180c010e040b0f04111b031303030e060c03030f06090106030b0109061206080609030301080c0117070509060c 72
    0x180c0c10a00400c00d1840d114251241159111609114500219440006015050b444030009158240e206440c14460001d11034111344400200301d0169142a4210304565140c00104202d04180000742c5082414a01400000d580c0d4a0741c43d01c0780314940041b4100070004520101e001a480500009051900c003503581154940c10024041d0405941c0002d025050200c03c4c49030710000541009500d60603150b040081862400300002010840113190b00020700f020715002654442c0309000844290f00700107502d910300d145030000c4100f000201e9080550080021075612294400b482c0304a035810704e00840f992000c030010901501924140710750b28031002c42805910300391185642c0c4181d50550304200307030fa03030707690000c03416686e02c1c212840c00f060030624107001ca54410411124114000070000c10701694806405203440012235444e00b482c2c1000c00140002032003403103211b081d0f55003484d1050700c1010140644000e408050311080034040d0009080c0030070f0300d0b5a810356003191851419602d44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 86806898 1250 86805648 86805659
    0xd020c0105040b13050d080c1219050c07020901140a0b070c091512060f06080a150b01140a080601140a170f070512100906060f030e0a020114030406090c 67
    0x10300300a89040303c400202e10700003102c41d01c0d504003240e000c54114006110b0703081c4605064410000141c036140c40d1031403c011581c181010300c1d40f041e0080c406119107a400c3c002c0301c9034000886401401050008104000c540e000d40e13203031001a0705540107118004900c84c080c200141c0c0502d1075a0014504000208040050008003100030040304d220389000e2240c0d2030341c5040c1c4040e41c0001e00076003ca0602c0340d41c200001c11202da00044400c00b91220001d58540c070f896809103000d0003200d0440f803d00c40001c0d01c603945000d50285070160f005c03c1c24044142c0001e001c0702e14250086110210030803400d100025607aa2003001c05c608101040031019650703aa00180003040006000607940c03003a01002d0101e0641e64a8641c501c0c441c034020b9a40e641410b40c40c6054501c1004003602c018482e204450010840303c6640c4101c0c0014001c42d154504c44042c145e2018056450b04080c0e0205030704482c18400140c1d801456840c080b403003548505940380c0e22440c0901c003d0102c1ca030040c00c404026030000c100d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 86808148 1250 86806898 86806901
    0x513110a030b040b0108060606040303080403051615150902070201051b010b040504080711010810120c0803030f010602071a03280e06011e030f03050319050a09020f040203090d140d020c01 82
    0x16502120247d800a6552000340300041c41588401000180c0d030324005008a40b091020b4401e040b103007103040c0100c40f07180d20f84031184028110351510041c0e50312581c07074401c10605ca41078000c1c190320320300b9400c00e0001e40010f071003030090080c0c1000b440e000c00481c80c0070030000e50000880c80d0006000300003506240c104000c0541140108551028509070412190b6000b0300f141c1e03220300c00000380101042e040c00c80c0c0300180c50804004a030282a08a004503143e030003800075611500d00380b604419150b1602c0c0e4020718110480d0300400d1440e65a0006412075503080b012030f41d1000144d03091400e031046409903021148194005190110312700480c002c164031012901c941210500c40c10302c10040b0b1000803429a0300c1a42c0310041c901e200c4108054002400781015503031100109162110306151038040c00c0940340c044035101303185039861510404600c0d010726444211603040d00c3c114158035103590202e81c2c0308510320135403080c401155512603400c6001780450310100e0f1142400d6440325640c07041c450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 86809398 1250 86808148 86808151
    0x9080703020d1e03050d060617010306020913090b06011407082b02120402040c0318120507050601060305090d09080c090411040603051608030c06011701021608030f0a0513110a030b040b 81
    0x1000310382841f00008140e407141860b603514020a035078100081c2d02e1070340d60fa0700a40c041d64032140c00c04c0014802558490591041c11400d60203071301801e00600c0c1100005200004100c4200355089042c08100c000c04c81c000144c64484000040c1a140c401409118071421050080200d5a117400055040d10004c01345504900036807003a10300340019045038506600303842d0418885a400011401404003091207152109261503850409900e4108180c07603250418000740c0009010a032180b09028000038108448102e54146141c0036402c20705101070191205000070b4070910602248021500303100200d41101824040144108904d035a40d00d0802e494a4111117411300d899200c0c031000544203c003104480c100c1042d500034101e00da082a10b5107020001039117414072199802d10402c2003c1c075580100b804180c0c0503081841d00c81c9003d40545650300f50003003625031002d0402c0e00b84048a201d1100014040b40d2014200d846a40c1010104108840343c1d4005858112041c0c2413105000b418032400c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 86810648 1250 86809398 86809417
    0x8010c0806060a05090103020f0403080f070506010509071e0909020a23090d030c0f0209071106060a15140705031306120b01020c04050603031603050903070609080703020d1e0305 78
    0x850440c1d451400700300160140140761804030710200284030320b40d07210b6402440944540a0090b09081e1079480f80f07011034100075140b4000450000701501888400c06c000da0050104036403112407850700180040c0a0306181c2c08801c18928850a0110317501d0041c0e01d03940251410000031900d4481c0300310028100310f07007079108502c6101481c0d028884000f009048814100e005401100144c005a404a8404900030f405032101280d482c4c0403001070f503418100c0360046c000d03a40e41181c80220207aa141c1440301c007800040c801d0310000810400e2103182600300000304620f0030704118011001005d202c0f00d01ca05200204107010000700d001c0c02c03103800045e01050b20955074a8002120321080c080c0111102004100c2c003580c402c01c0316003818a000d401160b44507074040c081d0b0307042040101c012031490782c2d050401c40108001241d29041c1c0d00b01000350740024405854000446403070440c51a8469043e400042c0c085c61a8031252418001521050740c919200e0303040c00c0c0e12101d02c2d0b040007803441d040103c02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 86811898 1250 86810648 86810657
    0x1e0f0311040f0c050a1709031e160503090a0905040203100f0b060304060e060708010806060f0a08030a020606130b1507030306030c080604020102070b180118120305040f05040e1b03010b06030108010c 87
    0x22644001181203020321880451f0001c40c9803944600361313035580c00e004140d00c14a98104028810245000d4081d2030300c014801da004540321150401000005121b641120911030310b800c081002598001035507200101d0954400185e0420550b82000070b44900c4101d281c00c02c038008244403c0280715842603096424840c160f034400d4a8189085440345801c1c0300e00da01c603610400c040740c22032400041850b626031005128122107940c4011003410364224250203805a08040308000850070956010351001140c680304200c8800108002a0440c000504114802e4400300d60501094001e0f400380b00a107801c0420712a8042da41da04107965091301301d4040307005000f85440012886811340648001c204d81c2c092080100140000446010300301411503400f56008000009450041d11124214140a5543c4550310750400090000400d00342d031009004a2401074440c100d10804940482024290001e0740d90317640300707000000d02400c0c00020007580309000000024154505601c084075811540d01c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 86813148 1250 86811898 86811917
    0x61314030a210203190e09090c03070306090f020a1203170106080f060325080f07080309092d04060506040b01120e030409050405071e0f0311040f0c050a 67
    0x385601d0350030148004250400d903128075406491002c44504020106104072800c094141d1180c82031182c05035100c102141507a9030400b1581041b0710f04a03071103068480140f43c01d9040d00040b9a80e4010340c80083d144c07595400c10b6508005603a20b040c0750300b5800800e4850301e240c40341e85003202c4030700c588030440200340c40c1c68120200342003092008c0d048690310340701c1c8800c60351045601d0204090042c04298503005601801c0f0800040029188000841442480030f490030490114a00340350315541608a6000000801c0030b100000119150b0100569013041c90f5210f8440c4404c110306000b1840e02e00800c072040d0700b01d001009c8a0f000b4880d5020701014031458550310f040c40100c1c0c100102017030000b0b8107841518030000d401d42280c1d42c10b080b6182164980b03540c6d1116401194400d071000c07545034010300c8003007103410220340b4036246045801705200200c41c94800c4107e00c0c0a680c0c44001d003810384041c0d540003a80c3d46c0c0d501001c6c0740c2c200e1000c1406152100b00c00101541d002d07401e0b0001044140c00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 86814398 1250 86813148 86813189
    0x60e07020618060c0702130906061a030f01120215030712050f0603060109110403170d140f0415092003010f020408060f060a030206161a0603030a080c090613 69
    0x340ca01c1e001042d032000d0041a281d056403054141e0020301c080c2d81110007190658060b070444d11500820a00a00c00081c1042c2841404c0000704038498682041003014000c2c055810340146000d41140c9a03041030201c00c010a10200310711420700c042941084070040200602690480200385400c95043c07810491991881081e0241d64025104282c05901010060148a074503501403102c22040c160703458242aa0303591180449030b40f29100c103c00d001c02007001131502074507005021680010325108143c40c5400d060a041c0365200500103411030041903070600c1c92048a6106082d61500069200c8800c2800d543c42d0b40e55020a1040a02940ca0260324489a039030510a0703c09494107000138181b141c03100700c04000360b80000783c42c25900015145002006039203040044c03006038400c0c80501b1480c01542821074101003480e140c0c03041b8504010400c5555a00401185d000280904002003142c46958403080c00b40580d50741140c02c81b8001800441014512450300b0446581039110b024030600d40c0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 86815648 1250 86814398 86814421
    0x24010e06060c060a150f030309030209070c2406031202160f06020d0311090a032d0b01030f03021c03090204050606280309050d0c0203010e2b030e01060e070206 70
    0x100320000a0f500880c0225812401c40d80059082d06400d04d8100071590301c0d034428800a2541f580101c0c04144030703110800c11800c00d041e5440c3d01007036078202040f607000759407605120403810340c5402c075144000c011084031408042d404000a07540051400001800e410301c00307507940c00d5498100c1c14101d00300030f000501000c00450391007503601c5070380a001c5000c4481e9058001d810b8000c5035030012541072100c6409921104503070001140138003e01c001c00700208105014030b092004803042034000c400d26040c08900c0d030542060440b0b40c05041701e01e0240003418100d0910259003000b40440648200103404958107030458680b00d4021107040000317860ba003040020318030600c030350b00e51581e02c1000a034034203030500031401c0c074404510704000c145050300f40e84050500e2044030114012610b0018000e0960500344128800c3c000808014182c1e01491792560a0b155040746247d5001da081040b41308070640704e42c0103241c030480301c00001e0203655240e40742060304090444196006200b003500045800381003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 86816898 1250 86815648 86815657
    0xc02031e0304060e061e070b0a0905031801030e070311030f0c150f16081806030f040209060f060c010204060807050403080d0216020904050a0b1503030d0e24010e0606 73
    0x5401585003500d45001a00c8003041030300180e9001d0414441020300311b06400565040b821a0050280c1e1581d0514040d5040b2202501c001c500c14a40b810480001e2030010032901c400c003040b031528001c8212580101d014110240c1c0000301809162000410828112081000c4103000c5080d640003071405540a9900c010402480d54080d07a42d070280d61181c207000004021080694509901e00f41d00c040c6840001d9031030000c21914a00001002a00900d080007a414801d00440d8860b186041058200c401213601810184c40350710310f000890a66603400e42301102e040c0c0c1c042d04c400d407503200031904a4000e402510031800454842c07030004403041e22840885040e2940010b080d8240103803031550300000c0d000b44545041700c0b440e00300c5ca4405a5216411039109030300ca0001803610119511f1700711020500904040c40249114540c12040c0e900030003911a80300c0382a800040641d400e2840c01d00e4442036070b48401c8a50703990384004826040d4403e10a0581e10003c81103078403a2510000d2241e940708 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 86818148 1250 86816898 86816953
    0x111090312070606080d0e0310050103050307060b041518061a03010b0d02090406091b051c05060307051011010b030a08180118090f060f2103030e03030103030c0203 72
    0x408031040c00d00700701c004090042c02d4000e4000080c4107440d035020614100b0040c010302d01081ca00d1402c1519450204808401904d050100b4412549142c0d551540c900030088000c0c8a0b40d103640c600f056944855000303410014109044191056841c00041d140400180f100c1c8540c40c00c0c00c00c082100c1a08820b410013400030796180c075103135a1a200350b0004540003041c1e8440d850790200000040d41e034580c0605406080340300070000b9401c03802c00c85100c0000314107561a041c00b501344207080c11160040d0404200e2012048085407030f54402000900703100c129000b040d448001c0c800742c3c4003283d50008642c03241c000f05030020411a10388000309940c0c1c01848400401e13050041002036a40c01c51052107450380c44060600300004a044824220600d0140c0c2020900c259121000081c0e46000d0069500031305207800303039907200741c10400342880d9018552946020651041103640c20035202e5400714001580010590340c0703030b58481c1342c0185103a02c00d10b0203910900c84c1b110500b084500188854900a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 86819398 1250 86818148 86818153
    0x302060f03040c0504050f1906061e0504180207020a1a030705090102010e060f09010f0902060406030507021f0506130b0306061009080105010305010f0507090b0301050d06020403050a0605010302010201110903 91
    0x2000340000c0c499910003003080b079200b000d02d04006107075110b0b030003a14001c990344030f044e02c000d207481116100c100030048141e440040c2054010403085420140c0421100e10540b1a015032006407070b0241c42612895000c0e40380b1a03548c40780011100d040d030380030301150385c400c81e502d10701d90f079039103040d0003041610121510307642204001180b95580181c00621580038180008280070f05403952a500b480b4048500005d40d544450802006000a00c503008047c90703084400c001242e055004140d407030141b0700030f01083c107aa86c0b0212710501e0007044141c650038601c484081c03548005a80e02c001504003a2030355801985031044d80c248000141c054030005c0301000e002000b507036950348104403048804604000503c5120300000c07138405428029035000e1405480080f41c035401c00c1091703e0403507800500c0d1000300640403a0034080000c40b002181c0c111402180d00d01005131450800c00000e125960000f000d038410003800c003040080700d40140c0d040701d000b40c0081141440e08201c1c00550b120b4000e00307a9154 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 86820648 1250 86819398 86819407
    0xd0816030207020d0519050d0c03121a0901060507051005061c03110a03020f0d0801050307092a020f0c04051303080a0b0402040621020f09010f1806050a0806040501030206 75
    0x19210740d014211141c0000c0052101c241203403220390410f40900c03e0810030008804100062100400ca8282980700710700d4216000400d548000345100c0d0004401d0840a85400040c12010454030281040c2c1000600c030080f43c2d41e444401078056884540115401c2c0030314204000440c545110b2203208100c06003c8802001c2d05003802556403070408001c034244421944c140c485003804001c4040454403076001400100081d12803d80382402c1c1010080402900c18014000b685000c9503c4003158400000400c80500c4062140b003110710203c0000c500c0c03090303840c8898400ba80080c0b1111450075581c1138544080080040c0003c1e00c00403034840001034200c040880c0007901c00d9491039400b18141030700040d107d240100107002c2c0e07846a8040c1c8009a58020b000c0070f03914941c0d50b1b03441c103682844000c500d400490364181c1b0543c0204400141880301e180e0311501c240d800347c69000068520740500306265500d803000944030303810081c01d0b90002210100082c1d21420103101d0181629002060281007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 86821898 1250 86820648 86820691
    0x3060e041203110a05041e030812040507120803011707060f0e0d08030c040f060f1209030c0204050a1508190f0206040e0a02030601080f061509060f03010b0703020d08 73
    0x7519510710680c1c0400daa1a500f0f0640f681c4018054010a045039940b25030380ca01e0200c101282c05040c3c003900845c0c0e680e40f01c04000098008017100c0080d071074112080d445560b0750510b2828070b05903610184650031803070541010040383c0307002541070b9031035001195680b01c0103c5000da91408680502030100c7d10aa10350807640780524001092514010445c2042d826190344131002034000703031440400d440000c1424822800040702c510081c14061a0154607044541c60040001d0f4032144082c05140c1c1d01c4100500341803042480300401e80d0080c009220604107000060001c01c69114101e0341c802c01400d010411000100d1500a540d206441100c0000542d4543da182c51041c04000c0764009000c02c0001162000300c40a079110395211100142c980c98020000760407904010000c200c1d15200104020496840c54042d002108c0010006501c52204001050951240100c0c00c4001c400100000500340107000c01815403610070741c01d0300d1000c0035141080e00c8180c01070b21101086201251640c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 86823148 1250 86821898 86821913
    0xc0206070810050409120807050703170c160302070f1202030a080c0106030c0e0f1302090a09050c040f091a0108060f041703011e08060601141614060a0c03060e04 71
    0x3003280100300c2c807600056440b00014100d0b40444005c4400b04030444c0158462600a030a1682c00307281414800d01c0d00c2826a0002c21800301a000180c1c16101070021850b481d1100b81030f2100c001a070011041c0070207450801075035584a611991104410015003c03441615a0824081c1142e0107001401c0c0b26a0654480e0f2180e003200504071070b10344d40c030500000410210a4984014030182c13300d0383c814103182031000d0f120000242000321045000c0c6d640380050b254502d00e01c1e845040004002010403051620034281200c3c030103810b5202d800c0c003500c400c0421840c0d1084c03183c9803040c8082c20700001800d9154a4070242449002e88940041b00012000241c1072002940070388034002441e441c004810044403a60800e0700101000341c40c440800b50700342244000400039103840d030014072140c540a80021f01011540d4100110710300d02184104a440342041c40c118465400310705440c19000081000f680c4510846140c9512400d040c2c0c44007846019104c1c041c282c0b04500d10200180da61600c6406 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 86824398 1250 86823148 86823151
    0x6041118191206050a05220c0b2a01050405151510120b040b030304060e040b03010f021e1305010c1a010f0503010e0c0a0504150306060602060601120c02060708 70
    0xa80106036003407010360000d00c03140c03000c000c0c00d10045500144a05810242c0440d44001c113070281d030610740410300c250665400e10883c2140220030440c0e09904c05032901c0b00c04406580d100800410000c9450462001956501d2080241e40c0080078014090404501d00780c41d0169405001d50300b1414198000040d99805590b000c9403416615403407031100d5020032003008007082d011001650510640000781e00c0c2c0d005e45851800c04880c1881844608400203842c1e2083c1d120315401d10550042140c010744840d000200800300c000c000700070f013906082808000c0e42c4031007180380320162000240c080c000c50040c1680c0320500700c4042d2014031800c140040d201c1022110007a2041d00c0e480c44080c402c3c1003070b20b400d00c0c0642040001e100b01a0f142405250070740b15901d290b981c1d90340040841c036a0948400d06d101c0c040700c2003141c0200b4542045400d80e0100b54907030b04090055405c0c80c101065032900010224041c080a0780c903d20701c10011f40c18001200c03944c04a00d40180c00010104d0b410501c15010309 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 86825648 1250 86824398 86824447
    0x3030c12090a08120f010503210a0c08070b010f050d050304150e0907020a14010c0e1e030f0102040609050402030c07030c030521010315020f04030609081e03040506060411 75
    0x101e41000780b6440b40714290b040070f1a00c1c41d03c40c454404000240103400041401400250700414140e0103031001c015250007115400c0d06800d00114001070b0b050700c2a841c05c0c4001d45c008044076070754421401c0059443c03000340074826440038101c0c40095141008000389902a4000c0003a500302410124000a903074a8482001e0400c2400c44030176000341e464000b22801110b003900144034010041c03402d003407454402d0f20b141c10385915103401030301800d400010030000385408a13561864030008031158010308a0f4160200e41612a0070f8035900c840f04154010720594080392580142d140c4d03900100003d0b84421540020340c600240201030010f401401c0c00c0300c09031f02c6070a1603030810304211075a0040611001c00c01200e48803540041040c007424400821002482d10819890004400c84030500c91040740710040c071240e6103421440c1407000c0702d815507001303400e00007100c49085218603001403540c01c15241135401d070240001003401032500344200c0ca4020600d4082500f04000410030341045815031140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 86826898 1250 86825648 86825653
    0xa15030c1203020115120204050603030319050c13032d0206070303020d0b040e010207060b190608090708010c030605030c0315060d0c080a060213090506061b010e0115090c0203030c1209 81
    0x1703460302d0120302c00c40c000900300c0902c80540e06505801044113440d8044d040343d000c0c1e0420014060032521032003c000d400074040f0008500ca45400c1c1c007a812920510f0441d04444443c41004030402c01190300c42e01c4071900807142ea00902e1a50300620980c03440320035009511101c1040440c0c0000c2c00380d0058030b000c1030075002c006142d10140e8040307010b41d560321080c2c0005942c0010600d04109103803050144119051750000c01010340518810400d981a0041d50180007101d4005014030500700b0402019100c140001e104a50320301001a010b8241e5002d041e00c82d00409035070b4003060a000910305040031010040e0601074640c00240000b0100c540003d940000c41e401c07000c1003800d010010310122621070040147e8403850103000b03c8011206d0741000b0361990600301400110b0342e07518143c900d000c1402c000c140c45504002c402500500d0070f0a00c2d0041035091130b810398581030361001c441d0101c551200c2c003801842c5070184221307201d1000b103d02d2a04518107002459000c042c040341d295108022004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 86828148 1250 86826898 86826911
    0x504150219080a0215040203100b1f020a0b010504050f07080c160b0103020a05030d050307081e1501020d020f1c02010b06040b070c05090112060f0b0a06080a15030c12030201 76
    0x6101103060765140036035602000055501c64613504000d10030541d44181d90849190a00d640043e494160030710340150701035100d01c2e0041d4030b595004140d032001810f000c19081442c4e8003d501030349481c541075095400600510000420341050300503180b0810146446d16200c1c0d0b5200c0c4142c80f2448080c3c80b6075000c510921002020088450b400342c04140101c0304420190f245104010001144d50031490081d08441c01e103800c15500300003030b40c1d0054014208407aaa50b01c0c4407000700304501480c0701358081c180e4481402113a1401941e6014400400e07400d4584003007a04509903620840c8809150160b800070b038075024080b18030041d5041410051001143c66407500300056450707040340d0400e1141da0000076040341041040115071009180c1500c0e040200d62400802d0320025500d41c074090f2580b5140c00320a412002103601c0303c8400e480083c0784003c1d4a46807540141400b40c00c40d80d1001e0541384c40c4500c0700f5a03400b1110201240d9202446a030325505002c40b1200181d90200c08409641d00e518 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 86829398 1250 86828148 86828173
    0x8071e0e0406030321020c060c0306010c020414040611031302240a08101e061206050901060c0606080c0919020d0204120204051f12050304090e0f06090c0105041502 72
    0x542c40110700968030203c4004205000919081580d044500500c2c0f04000341a400ca02c00703e580c80c3d200740141c5041e5143d603100300050f580c05840f0900254400d1600c43d880560014040341c0138010b5016180412031000f603141c110310a8401a070f074144000791540751805c010f151280c5040043e034010401c07081210690401d814440d0410032540000c2107581d820007200304403400040c001480c0c140f8400e2615a291a08000044c189010303090401102d40b101c020300a043c1d4011034000d11010b0103003c40c56035224402802180c08003011581c150621600141468000500300e00820004015402c1038469500420aa882c40146007601d15024019540c0c04842c510152008141c852111800b00c03c1070f204200031100c0c010003590302c2c17200e11718030755412800e42d43c00502a1800c03a034003001c0b1245c603420014914003e07030f0320029410342000c40c003601040d07010034460002c021402c212100764648a00c841c0e00c61052401e0280040c4050108118600340b400b40c2e07138280001801038415104194 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 86830648 1250 86829398 86829401
    0xc120102070f1a0a020307050306010c021c12110303240319050703060f050f01051306030b19051b0909060406080307200109050105090904110d060506030d08071e0e04 73
    0xb00e100751004400298030350340700910100303640e0b072040354030300118514a8421000350044c0030180200f810040032101900464a4012b0501d4030b1802c81d00340f0741c54032400b40c54004541807a02c1e1104000456100b500c0568400000969002d460b90012031040c401c005185001c400b00b140b000558144910600707a41d80c40a4403103101c18040c0200060b090050035401e06400703803180380780110507861800b800c004074130010404990640d007003100d1011507954585108000380c134181d0409400305000e0000d0000c000d4502c00219034a1760026820300c036642d114820b0304c403400980b45024446103400c014001c403c0c44d1490b0a03d5000c28010400280a625110320270725580040c00300707c9110090310307035006214040311401d2b89074840034a481c41561342040d00090160241080c2c050040c41000042410806001d1080300103207000341c028030142d012410104040c08007681c1150090242e1544051a0781c413800300203206400541302d00d0311008586400c41071550b800b8004d0030400100c05101c0c05a69a81e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 86831898 1250 86830648 86830673
    0x50306040213110313230c0d0302030f0d06140103020304050601290a0c0201031416110705091f05040c05030f0702010f0c030e010608030403051e1606110d0801080c12010207 76
    0x610703405d0400251989000c481444d030071001c80d654040d04110a482040d00020070a104103029500032214140514050b81340d405481d2105891910101d1801414bc0007503225004945030324000506030b0300ea4200640480c8026039015245402200040c40040c00030303101c0400b801c0c1e04060109031541c240d103d805407034000800d00000252002218070949d80d050041551030342c640c40c400800d904000907001c10b4410160700035814403200c43c56100c2e2500b003e0014a005240145c80f075011031800004c00407c070301d1b1196680e00c0442c245d1202054034240381c49035007400ba10941380c051543d11000801904040d0040605045640341c5c0d8101e0810a6140101c0900710705075203001c5401d0030701e200e81c01e094802c0c5401482c007a9100f4001000807450000d0f449034031020880311480010454a0b0260901e8141104245800007a034800207205138403488410038401ca44094410003181100101c6a03144288658045544003480700e00c0340c2d180a4801c20031241c50344000601d410140d943c0c800f0741d0010b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 86833148 1250 86831898 86831911
    0x50307050318010f1a10050a0c02040e010e030a0f030216030507021903061b0302030f040f0f05120409241a0915090a080a0f0f030903060e01060515040503060402131103 74
    0x44442c05108803000c1d0740725041710080c08035940b141314400c80702c0061550164810403020004245150b8040d901c3e0790344034240341054440240a04424603203100c1d40d90b4007001140c0001032401e1144400d030342c421310a440e9810110503c5104504182e181203c0580041d041668031480c84902205c2410f01104001d008600c00d58000c6046100d401c803114400106030360350b10900d8010010040d0540c3e01c003440c00e520036405072885c00e955540e4205412107110103140105a0700c1403110840841c44880c0140040791201541440312540c2c41448440040d4000040c3c100c060300b405044c00301d003d40d030020741d001e900c1e0951110b040c500100700091010b80f2148240c10200000111003000f820005400b1010709035040c02024010090382c1d43c4806504000d602410300c260a403000010140308810090040d5002401403244982d40c02d80705000b02020310440f407140c01c0003100480100d082c10700303503022110010090001603880342c0a01030441541420b10050b01d640c0d040c200040c20408028501411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 86834398 1250 86833148 86833151
    0xc060702010c020d021501090e030c060112020a09061202121c0c0203010606140301090c26090f0613060e01060504110408190b0c0c010f180b0f07050307050318010f 72
    0x4002d041d0107410a100400080c0031500006468000f10ba04086140c1c1110b80e01d1798005001080380b00c2c25800d6000702006201309001e52400040c100c044658a030106600803240c07549402c0c0d13241201001c403091845040c031400304144a407805803070609909182c2c00010400c0e0344c0500f18510f01880320901e2a104100800c1c8e2030800c0b0011350601740306e002d01400150608130340f510001c041032121800f05100d00500183c840094641d414031407190704444040200c055000c200b080c038405101c0000458100030b03240b155096600700b2010024402d402052070715282d95200174240c0341c050140c860303010780480c1c5640b1080001202d44440c810080c1036520280e403240c440d41089001810044803401c02c000d5101111201c0001ca612150341c59000460a0541540c4000d6414000d000d0502c3c0d0400f145480d02d0090b103400040e00102035150000c0c807480c0c0355070031036840c01480e120b0f4040c21303540400000c4003400003444860140c0011600a80284401c607441140c0d07405850940e525009500303843c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 86835648 1250 86834398 86834411
    0x1008060d0606080d140a0903080a031113030b06030109021c0203010b1801180905100b131e0b01050309030304260a02010b040609020903150a060308030f04120c0507060f03020c06070201 81
    0x1315030040601d840c039004080720394a01724540200801c10744040c040030700340f680d000907003150300c0f8003e0748010745000d52500c10b1030700c44090b111207011a07119131000b6a070310707810140018001c0c60184503c813407040d8000c103180f41d1106440d001c2002e0007039200b41240c1544d610791804110380e0b151000c1c00060300d81156012601e40c1488281e40d1448400c0001c070403128240040e07240020b40105286000ba81c101c440020f40c0d000000c0010303031250314201ca9500326032400340c520491b0010104107402245000100b808683c0042c0e0044440303201c200c504d54206c1d0018008a000030303c00540072400c50704907111544c00003aa80341b0b100002e510000034480075039502d481d8044681014082d460080010718811400d0515207408681c0302c00e0310746035502c00c10441c3c000090706440d1540c8031034040d5801460079038692070012405d8107202c0e0140d400f500c03440d0b2803c0600400300d02c14204c52001039405805824414a40300d8191400c0d19006007004c14141c003441a0f6403a1441001000d218800560010451 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 86836898 1250 86835648 86835673
    0xf0302070602060403050418110a09050301050106050406090506070302031209011410030201170a0e010e0604020306131518020904060b010e03010203011409180a030c0605090307021008060d060608 86
    0xd1111a0340010250340000c810000880e4002e81506c0032910b40305100040d030f52000440c00300070101001d10b0500d10a0210760800d4403a030154040d402d41c1c50a034000c0140c0e989445e8140c449008601c10040066078400c42400907040c81005001500e00c28012641420301c405480202124211010242a0b5480b149205115151160319030402d6103800051015402c40c0c00084c1004550941e00d80400d0310400802c070500c210740d0043c1d880d001e044000300303c2010160820f0b9204c24003910168403a00c1400003080703401100149808207641e000510303403d82c0d5494880ca5014000168092411a280d5458000580c40307400a0034400c1c0c1c411040040c640da440000507001d002090b20f294000d03032052006001e00d4412090f40003408200b110262120703655048000344894801401000f6030048449903410550800030815805d4802c03641400183e50703000815a0340d00420f40c02a6004892a1507000b031207008140250f00310b10054011404843c098540509541042d40140000d5016840502c0e0707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 86838148 1250 86836898 86836903
    0x507030803131a07120207050c03030d0c030b060c0a03110a06090c081b0f040911030106030b070f021c050913050c0c0d03020c0a08090d1a010303030e0a2307080102070f0302 76
    0x10302010303038103240c603030350500b510028103240b0305c003d41400d040e0f400140e0000f481010002c0401e1004010210796654034040c1030103001e40061f464107408242000040a134500e0140e060f52004c1184e18010101c41c112910210341c445203110711942280500305880010400340d026640c0301c58007070458800035030300d0b0140680c80e14080020222040c00ca4005803490ba40c0d41000840900074102c80100d01454203050111620a860568950541c80c02000004001c50b04d03590758415100b03600c039041028680c480590b2204c003c4141c003000311100c0100d160409010300080e190001006c0d0403840e5108140e84400c2c210345044d42c0d0300c5840c1c200490183d50100c8204058040c03802603180540c00c0c1100041d490740d4070160f01500501ca40c04c00701e3f411849444801b0407044003038000b4401c000700103c105039540080c0080c0000d0740080d0802e8450910300b24000f83e5800b000b075000c2c1018060014035000f44543d00402e80d40581540910742000612030000d001414080e40900340301801d240c02458003a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 86839398 1250 86838148 86838173
    0x30c27010807030b1e0f0601030b031609050106020a08031b0d02160c2117070203061302030c04020705030d0b010905031006170f0303010905041a0126030f0403020d050703080313 78
    0x1700c0e084030280400040c000c48401c2141c101c1c0c5405d400600d00e031194801a006000355054072909442484244140c0d80d031a619014100da0b04803004002d80d9803540e0040340c582e8003501020b802c0e000200b0105048032032003c007100c818410141168200000c60305507005903840481d80c184900640d16048043c000d1a114860040c40c501e100031809103400c0e01e44441040d81210b01628030200081307146000c41001084074100c40e80201680d126207090403410040d6510418240c0c003030f03c20b0741400013080c01c01c1c0c8202e03001681c22030021414000011141d101406605061504000d6014030018458404008081e440c00e08910003207221424041180200044440040b2031540000d40244040001000301ca055a0a120010520340d846041160003440c0041c0c1d004804024000005140008400b00c1050395000b586d8501079070840308200e9913240512070003030740c4540c000c100420042c07400144142c02d951062050b152680d58a4440da61030b07070011544001541001002d0408100706801944d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 86840648 1250 86839398 86839411
    0x507090602031303020f0301060b0c030703020601121a04030210060b0d27150216030302120f040c0605160c0603091403030717061c11040606090302030c27010807030b 73
    0x940c1803450191141510f0001440040d006800390113466196460a400040140c14403540443d038403052891090f50b00c1e40701d0311040e80107004020000c603100c0070394041103214540221003000c4004800c3c2d80560400c2024204400b54824150108140441402128014009040c0080e25448043c1405040c0e070038841c0d68818100110340c8550381c070b40704c4035aa02446a00122001c003501350112a1070000c0c4100f8004041d07401020045100305076058005040300050090b002c01c090321000c2403040011010741e0000c0420b540c0c0141448a144903001518190391607040401006026884015101219800c0200065103c0b41d4070001c1c84000e00d41030501c2407000300150701c3c501d0400d0000745240007403200d00ca10929071402043d05944c6003001d0400705c4020305128490928145483c240c50b502801c807060056041a070f0020741940602600c40480340c01901800711002070310200f241c0c4440c122010011a80450154800700c0400403442d4080d120300c400034030f80d10f03066081c46d490031340008114 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 86841898 1250 86840648 86840653
    0x9060b0702060d020306030f03070b1501180b0a0302090607140607020a150207141b01090b120a2c070602060c0a0f031d1006090b06030403021216080a030507090602 72
    0x200300586480b411180603001403040141c4036103510001904003000031008035103511000c9411024064094085130259000044000071150604015074101948041c110240300c1540c0080050440a000400d6070440910f00145081c1000c0c0010b901600b0051045d54480300039521000411000c020300390f0842100e000400d100400317a601e4a0800c0c01c607402c4140c3c10b40e00428074604118a00016642d245101d10030750303d104202646d00304543da200c01280d0b00156000b440051121070000448641200b4403503119101c0d038413044042c0142c80f0307460320381c1202c60203d0b00d802c9662121004030107104540e40e020b131083c1494000002d181c603001038022006182d0800104e4446504041103800168003820302081c3d2005180c807161a82404640c1c500e2140906403d12040c80004c1d0f006005441c600e003000c122442c058428410140000c48000300581c0c0140c25002c0c542d040c00003d05602d13a08440303042d61310440d5a44400d03654120502e5400407a0b01c400a10407041d804c444080b0282030309100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 86843148 1250 86841898 86841907
    0xf0609140906070f1404060509100908030924040f090b030106121104091202010f1107032a02030a0317130503030105040c1701030503040f090510090509010b030f060109060b 76
    0x800c42d250300001c1c1c1984140420150080c0d1580e000381209501c80d0b0008103100e4640c1d5403184080d105038095a01c551240e05d940b40c601e00e481e07000b0400d100c01d84541d4401141040300c80801d211082d6251090709900513512454250440000340c02440a08001c2100d110401e2801c50824180c46510345168401e9041c14428004509081a5a942c080d000320742c00710365403a00d41c0894002d07c40c0c40005041c2e0444000c0c820352031a0150440344010083c04010442032800c40072043c400c0c02000700040001300810843e814800c10350b51070030060b21154407010805205030740000e1800007644000c501251040e00001c1541000c158007640c0840ca11900d41165500355070741c40c2c0c5a01c01405694812941c80d0100e21506101d0208000f0b10742110800303025a507141d0910341d82d00e411501c40d550521340c6203400800da1f80308a001b00c5010f80e01007160b04078618105010700016040041841070150360380d450309160b070341d020030462014aa40388050111541000080410f49406400c4038420071020003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 86844398 1250 86843148 86843161
    0x171303061a150702060d090206090d0b06030d031103010905100e040b1005040e0706050c03040e0103080c061f05010f1403040303140106050906070f050f031902190818040b040f060914 80
    0xc08540117640806e0000035110503501c005042c902801c01955041b0a040003031008120351940c1185c00307464214200d80003c8213444046050361144114820074040500c0108800d09041d0030054001d0628903c1c0c040f007580703841c82640f07288412a000c1c1c506107602c0c001d008101c0342c03082002001c0d002c10340f400e012003800c0000b5503075201441c0c40341c00e04024000543c0d80262205106645c060810500b581c40c0c0d6580d2030402e02c005401c101c00c0506940200f40114083c5108200840600410100102015403400c001520071516030000c0c0710500040481c7c00039480006002103110701d219407800640c054103600015000e1105800803800c0c02410820300c4c82d40d40c4e034001500c1030380754480400c0c6070885851919900b03120001a4250940c40046102600109a43c0e07240480c03002c0c50b4220303802e02141e021080e40b110b50040028060140810841c200001c00c5411100e031200c02901c0031811045040104084070b00c0280141000c9503901014000c035100c9003e26000510320541060036800c208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 86845648 1250 86844398 86844409
    0x3122003040b0c040807030308011401020607020601060c03050f390a0f0219081014060109060309030e030d02010c030b030105041e0609170405011803171303061a150702 74
    0x703000604910031100c0020b0741801c003103007268054902001541c5d0f1799950b915004c0d00386082030040015180f00720b05590480e5100084051103021164014000d5910b00402030790b040030402e00940400404200c0c8440a20b000c40080ca024812216006800e00701912044200c071142044c0c0b2001201c06802c0003800c00b00004c1d08180d0030340111748400b54010a2000030f01000003014143c0120940020006043c5008070b80700c40203454160b020300140748010304c000f24001e42140d40a01040e031101090200758807a510081041c0d200381010680c090440b00000d18100401000c100180c1d1107050403d12039a250040c60010b44090f0028812810240c1d00e0f0f0f039120b220844054500303000483c0031014440b00d07800506203260040f41081c0c2c182c2468150030395580c030501500780860280e4041c0c1c4000b01c1d00303280920482e500b080304000888a41307031070401c8990000380150400c903070340e00300030001c1002072044240480801c010410f00f619080b080c1b20300300084c103642e00e490480600c101400368443c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 86846898 1250 86845648 86845651
    0x27130210030624050d0e0313080a081b0f01050103290606090f0109090519060e070806060c010b150c0d020303011820120a05060f03031b071203122003 66
    0x490540101d00d860f01c90200c0d05409a407060300c000c41d081680d1150b400e40c02000030107207503074840824041c181d107d60207a82c0d01e500c5408028410881040b0b0011201c60505a5003c54065101610410040d01c070486007598001e803c00d646a5480c0c401507164074244514045c06000002c4080c01c0340d140c50000110705019075000a030250400000c005186da201740d080801519501c00100504c1c14a031f0640c4c1e4140284020312241c7e64034206002c1551550f00402c0c901c90a6555140f014607540c800502ca15608100d036030104542d201c2c6c84080b600d40d2400c024442e814054840c0603100c0310610111450711141101d0203056400400061001d20701c10501e2540b81c03051290080f450026082d606000c41c0003c81c201c81c90410042406401040e020141600652492909000c142c03101c10800c2007800c0c68241c0d0981c158010407001004801201602c180e8801010550310a5607036401c0c00903042030175034402c8001540b600070b4090101c006118400d0f070007200401400d28902e40441510a5120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 86848148 1250 86846898 86846939
    0x1d01031a090423070303020d0903020f1302160303270c03121202030408130f180510080f03030915040b0a0b0a1502010e011a0f271302100306 62
    0x181c400003028840c3c000c200d04903951041c5480400041c98030003c6403107100c940400c4005001d1410440758075403040c9032404c1a01d070001c1c00304c1c040308071803c10003100c2c2440d0909244a203809001e21818541d2018a130445103000f0384000c240c000c105407401001480754012103c1c0000b070000b103400230440c101a210281c0b54030007007041c1d0f5070140d40c7c003c1e03030424005620040300d240000108010048040d0282c4007030140021000337203050f11352140c1210300c00c850003890a0010600c11152408031ba6800481e0401e800104010105456101070303410031b94090307048007080e0300c000248240c649041040300052001401c0305003040c1400e035156100004050003025070252210058562540c032001010024480c00d14003400d20850108003034080c04181140ea081540fa08405c5401411406501404040000c00c2c0d0b4400c4100102000f1000385050251a0212250403a00440040300d00b43d0502480e081030841001c14500e1040200e14941e65901000700350404800300a00d900810044a6282 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 86849398 1250 86848148 86848159
    0x10b07030302070c030305040612050906130812040c03050f060c181903060608010b0103020903070614040b041404180c0e090f030301090203010509010f0b0a050708070f031d01031a 79
    0x24580c1011000ba0041050150510240000000406800800400c00c6513a03c1d141d00000992659051084075011101c0c01c00980040380002c041c102d0801611500c0ca201c0c1c9601e0b0304080801c0080c510790003045400304c400f502150381c1070083c0030b010404051a1140c0100402c414507015589049030300074a00c0c45015500444003640e442e50b600ea1680060b41010781d4000c100540d070f41409009081c5612a40129519040000455504c68001c0b00d001c0540074004280551802c00203ea0540d007041500c2c51503c404d1201090709502d0034002d00c010854407041503104802407040104581e41100d00c20070310080504030348e0018911717603c01ea007120803840f4401010780c1c6010040341003030b00403446044140400000810040c200c1d602a41c140c40e0240c1d224441c90381c030b616507400c2207500f60040190345041403110840082c8181d00518540344518145428405980e590304110004080100e02184961400440d0602110101408000f09107414840440c420b0350f041000c0b40d000c0e8002d0f0082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 86850648 1250 86849398 86849407
    0xa0203010f0b0309030a201f0b030f03030105060d0e060703150506120f0405012c010b030706020a08090a12050c010e01030b101412010609080705010201090b150409170d050603070e010b 81
    0x162020854035a8102c0c42425951329960950342303d81d142901c40700c0860501e24040d00c0103501d06000070b0500b0b4610051008500d56400c20081080742c0d00010980c0d1111a2917241c004007640041c800d050040186403004984045020705c048540c4a90b0341003107002d214103100300035540502c040041d400841c041d030b1900305615a0309110303000d80b4009507040400200400c0d00300c01241c80074010b85030380c403000c0004c03c020200c05040548618551054000603030001e01c0600104510f40d00620312910b0051a021070302d95a91010080880c0303c4205903103a4100d180a04001d5030001d00b009446c520919040052404407000207000000150080c170070050503ca81020304054002150802e41c210107991501e5a51003000810031003a42c00b501055001e40a00060345500500a80c4c0d0100c0c1e0001203054166201c28081540901410013189d0003074030394030f819010a1741005000814000040103d9841446501d018140c9902925183c02a0700000c000c00c0802c0b0311212107815034611492040d0764 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 86851898 1250 86850648 86850677
    0x6050903160b0d06080304060203091e030703030503010321050f07050a02060c07030201091703070308071e03020c070609030f0305030402010c06050906011d040b0105150f030a0203010f0b0309030a 86
    0x18003451024022031046040340102d0092409009020315030b00610701400301c41d440e402d0340b07600c80c0900d1064034050f80c000d000e010214507064042007a139016030503141e242c0c0e80c45000080d181c660a98003d8010440000040c014040c1d1241b01c1c509005040041900820700300d07070020280c0c41401a51100150701003201c200f040b00c280500c10341280c00400864a901c04001010b03101c0c0064402280840c0c152140050620f0100c200c1d1102d11002501441c1400d005440545070290010551020020042d880f0003900350700d182008000d05007681c0050310789141c00d440d03a14102c07070303a0811028030401200400024208080c447c09055240ca0a80e44945a87c030041c1d0f100060a40300400c0341341000208101048006240350403600c102800044281e2401103030310900382c0c1910040d1400c0d20100060145040c1b0003008015500c0b1280741c1031030030030207066400c800d8000382d8444001c1500007004100e94014001d244014000d1142c4a0740741d4141824029524880e00c4911424070480c1d00d082d209 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 86853148 1250 86851898 86851903
    0x10e15010809150c0412060f150e06040207030e030a0c17030c030301090b04020705030a020610120b0403080712150f081f0903050d050403051b0d09050105090f100906020708010c0906050903 83
    0x10046c40ea4018105180c1e8500792010b03103111031300400054074165049070855806013840003124181144c00c01151169024080a5800b161003a0140100f4100e40314250710704000c489240c60044220f0007025040401080b0301851000010f21190310070b004070303114180c01004807411aa140320000403042c1c000408203019008407580030b00140004100038440340e0300420014450b070f034250804141c1507219031212034005080c603c02b5000310040c0c000600028040c440550300000b99050109010400200b0b01040c0e4401d003610410040010b4010001601d00e424220b01502c4c220340a40f40100202d000840c61085480c00c0076101c584403c023075014140600d0854a104c0800310050005283c50b0401500c241d00001382481842c0740302d02614084040821220100c14856a6a884e40b0385050011140c41c0c10110004d40d00a5801801841c4c5658078060b900c9001c544c3d84034144110b10b00440a07080c0780983d4065030059040c165403159081e4400314410030b440300c1341082d5484058681c0803d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 86854398 1250 86853148 86853157
    0x10e01180305060f0f0702030f070201051303150b030c030609061f0305030310050f01030b01120c1b030e12010e06040b09010f0e060a0f0915020f0c06010e15010809150c 74
    0x81081c020310f030600480b284c071078810311311031210301c103030100c1039204c40c03070205d0b42ea1050b803201d1100e410b02800001d00544c418401440650141e5082d1160903440351a05080c0041c03103a42c43c02107954460f540310150a0510030a034200100324043c203203d280034202180c461800400128850210320030207090724030b40145280c040d61300801220f80701e18100f80c4540d6861102e000d40e0348070319049100c20050f98464004e4001051040c1c0d47e1030941501901100b000c1c1c4540b2802c071b020300450f006190303490b032060b0b072051911901982c2d441e60261074201c103100e1801c0036032106000590610791501d040310360000d101d640056118081d6200b995940c011a80100807641000710440e0900d19400072603400017030401d000303070348201e010085902500c0d03480c4201c0c1c66a010040c40e8030a103102501d402015940506a00a580201c40e442d101c800c10403103040c5002600440c0e4441c0450080c0074030300504407080c05002c03000307003001c2c110ba04140c01507a40c1c0c1e06896082c1c08440300e00900042031307012208140e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 86855648 1250 86854398 86854403
    0x1020705091815090102070b01050607030c06020a0c0503070614060a03051b0f041404140d020c0904080f0c01140c0a0509120708010c0c0209091f02090a030c2d05010e011803 76
    0xf01e10906040303081e00c4c040d51002c5c13000d5600e0744505001042601c0c00b4070850307429982c075403908900e9004645c2c2c0e11000c1d410003502c2d10107004900b07410307102040703040c0b000f421060701c03c01e800264120141d420f04101d40000d031025014240b001c4080c40090000203500340307421040e501d08040c668911000901812490302d400d0f4002e0f0400107403210450b15210b02c903014502c50030340c200c1c0f904002c1200a41c1d4083c0075500d04010392101c881c40b4651b0401c480c105801074000d0404c03600c1e02c800391090f80c0072a8071440c020a810382d5a07441d03460b01d000c0c05219450704852401d1502d1f1801003130034030042407401900d07030582c880d0603944602c03c800c0004210102c014641c0344003d2146510300000600f1035031103000182d028165560001d60081d001140080b2a942c9400301c2640d00c04d2200f01d2803000f9044103c0c1d0b075811242022001c404038041004a00050202c0c0841052685940c080d0798400360001110004840c0c0c480c000b0f008983e04150046a0000700307103441044410290081041010240d001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 86856898 1250 86855648 86855683
    0xb0f12010e060105040510030b060607050105040b0f070c0b0412031409030417010c02060c0a09030519060c02060606040b0705160b07120801050627030708030408010b010207050918 79
    0x65818104040d0881c4030103082081c20b55150340c0c0c1e90018402071b80ca04652030005e560408100b880002d0446501540044001d8070f0182021007a41d105400c5840603134007581d00b4070031081006005c158105125501c9040c915100d0f41894040e41d625254800c040c00007000c004c0b0008864034028401c1d4060950303c5903000d02c503902410b01c2c0502548942c464011a510128000340200c044441400f0320780e401070046d402000c0658450b26810b2942e00002c02403805c00c1010030001003c01d000704000396245140d410444032041e618a0b120046413a20200041076400101c01c00280c0da80e05d20603038048400c1002e880ba56540c55190076401c007442d102516448c1c41c014800402c201e5000c070041c04840e0700c982c1e8080a000f0f114079080e2601c1c42c091103400d41c040f80400c13480d024100040850038244200709000c074400004080003d00300728407070700490466400441c042206140034010048130380c0c0c081c0050400d003070602c008a4550200204012640d00d14008181c9040704100801806082d48400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 86858148 1250 86856898 86856919
    0x9050106060e0301200405010503090f160518090c090709030605040506060f060301080c0402090a1d07020115060e04020a0c020303070305090f0108060105070b060a0f091e0507020304090b0f 83
    0x30b0211240c40c071403540690318000188900740108160300d4400154450b00500301803506004403840d81c0300034858842c90141d0405031402c1001000182001e0000800d08041c15042505001d8031845220040c00841881c60900c01100e00200c1c0f010f4600301c00361742c4120680d03910801521400812303840140644d190800f0030042c40008981c0a0040000b243c802a41042020800c031a5000038012401c2c0d50b040310f00306407501d02e401c1d40105080c58014140010303c56640b540e1490070124558441424000b010400c04d0095081c89440000030142045550360303814000001d1404820f0f00101d40210340c0040d00d0680e032030203080340101c1141d0050483c0c1d5104180d2400030202d810000f0454091142c54801c50b01e00d41c05814010312401c0185d40c0c1c9030030401c1c1034032401140c50002c0c2c000d6400104100d03010415500783d0b4040c0707000e01611a8041400103c0340488180c99426a21a800d031525240038001e4456020040390100d036011395010030088401400a04081800d00c802a40410f0501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 86859398 1250 86858148 86858159
    0x907050d0c0f060215070305060f04020d020c010b03010c0c021306151112071a040c03020307061115100515042606130320071509150c02010206041509050106 69
    0x71007a4180c071114103914915940d5a80300766941c00304545810001d40c0b00c200042c81d42442680701e030f6131050b0010420180782da00306e0701140803607020080603244d40350005994823000030240a0010a22001da000300000320f02d240c1c00600b01040702000a11800403103156040d24440c44d008080541507101340c5c4114056000d0000d48100140326010582e0f019020203800201c0d454001d482406410030608800b090701c03058018183d86008000303c0c1c02d40d003c01000300158500b042214090a015107030f080c0c201e00d451180a14191020b0017032203d0301007000c10440982c005d01d40c0c55003216800e032140c200284010210000a00843d000701c05403804182240680e18081c404a11499500b001a1400740d00c841103150460340f4039a2001d00070801441d04080c130380d0800b540214540c8142c0d820355200d151101c901801c86900303240361800098400c80d0900001403040b590740307010311080c04d007100104040c0d80040c4d10b483d00200003034001343c1c2241c6c00762880005138109603496613101000308100794896 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 86860648 1250 86859398 86859413
    0xf06060e061003060602060c090102010e0f030301140a03120804141c3c03060513060f0803190507020a030803040606080c03011e0c020a1a07030b090606120907050d 72
    0x446140b48282c030900759580d90703680684106025206998042d0090750b41300c41c6008440c0e403203031b00201d04665035462000050300007440242825203444003c0d580c1c6e94905188006d143d103403108030620130f0281c01010030006100300a158020949030401c9070055485042400d0100c40884102c0842d00840e141549001500000400d845c2d44585880d01504200003200c100220300558070003694564144d040c0d1806c40151450131100c00605e00821016116008622280c8122031410700543d1102c00c184562050a003042c2e001c0c000300b800540c103218100c04c0d050007514440c85042c007800300000f002820b546892007654051500003030a59940d0400380351400040400340328510f89030040241c0c2e0b900a103010f00500c035800b600b052003105100c01c02c060840c0180584d030701110652140381c041d070b400a0340302c07441a1039480229640030050300d0f044102405440d0b44501e1284100c50328410446555603240c1500c100303034200c130030095103030b5510100b01d480e2281d11740106c2d42c4080010303240000c00455 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 86861898 1250 86860648 86860651
    0x110304050c0907030b010e0f0604170309031c0203070807110409030203030610082707151110020406050706090201140d0b011103040501050a050d020f13050f09060303090d0f06060e 79
    0x142c0c0e09258583d0340250442c11100b0b4184524001109202c104841d07103049414041803040c010611480d01c4c0d079030020700c5042420344640c1501500003188044462a040c0300008030141c3d000d0401e0030841d90700303078020344900c6a814000d081c17441c00b0038180b044c48001d648400074504040c004104413186410060360301e0708100e4000e4894540d00d50b508022520500c0301c41e0180150900b49002c102d0760304500640240f202350007142c584200070001500d161013101820404540740c40d44070700b20030106401da080c500700c1e15400b64108d004010410129500408445025401000025a007a40e07440100d80103007036a200d00b0b02014000c036145003040241d07401846002001d884801c0901411a481a100d0040d40300702c85c0800c40901c010004140500010807942c5022840185012080f4403d140140c00071880c940840c40c07012800c0c852820405800a002c00702111003c00c40c1c504000001d9480c8603216500d401040040c10407420062078540040c0f400b5030000b000d2051640343e12a01031032240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 86863148 1250 86861898 86861923
    0x603020907031a031f0207020117010312021e0601121b0b0d0e01060b071e050d081618091a04050108060a0b010507030206131a0403020f0c0a0b040302040f11030405 72
    0x85800d5103c06180c0040c050920500c56000815400304030304101000750400c020030ba061040707020702e004107507401507062030213141f08080d074202c134000c4004000d2030080c1c03070110001d1482581401580841e00001c280341120f8013014007214542c01c0d490501c01c03100701c00c82210034181c11300c100800c014240502401a000c51103408100a0520014076403d98009208896a01600700310800202b4511601007120312190080381c40800f1007940c032030380340030300c03a8204c0c10000780f4040511040c40c0201800001c00441c0d860001400c0e070301d90350f00c007030714580703134441e88281d583d0b6003c41c000e245041d41461401ca1030000c204000560750ba40d44503031581021900c8540a0b45007209000d103944c0243c060f07880041d0968014000b80c0d0b00c4162405110101803001d0301c03400f1000d640e4032101c0205d6008140f003180f19602500131020010001403504d1101404584900e500f000248040220103090300c04890701210040340400e85001c1c10802424445070000e0b01035030000800c0305102e40091001380055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 86864398 1250 86863148 86863181
    0xd0f05030f06211c12020406120b0d0c030b062409040e01060503160312080c0301140a0308030a0e010507050c03180f0301020406020703030924030203090c0a080a0302060a02030405060601050c01060302090703 91
    0x40340485c50004034800c0340034041c0411000c0b26030321600034103640a402c803000f0241c0402c020742c3c4c0356140c02480589035030089840b078513810100001c80c106004030f0890041c0d84400b00f440304034801c6840e50f0500420340f005025a0b03480855107034180c6e003504564018107000d81603c05c4402c1c41048401e40c1001404242d82d10004880b81d883c84910811a00303100d600c0c100c041504590030103410f0340d40d8039036900c00940c0c480101000030010409072401180191750401000a007410108021825a01300400140900005000c40401a03c0100880e41805a8030585142100b68400068a42d11040b01c8041d050740c80450f02180c140e40000705081a41e001303880301145565290010102010308610841e4401e40b04200034804c24080d801a6400a68075426541119812000310311110703c540e10071071855100e441d40b1070034550107011558018190310020351031850152610390380c808014000904004000a4600c4410429408400076590041c6052403500308640b009020380244a010405131 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 86865648 1250 86864398 86864417
    0x912010908072d06020d2c01050c04060203030c0a020a06020d02120601090614091c080c0709060b16020102031b07050103060806060906010f0909050f060f100c0b0a09060204080d0f05030f06211c 85
    0x4d002b803030150381c1113a00d240d00a61841d07403414405d541f50b4008010000540c80f5000340400065940e0015110b00900b00a0058444d107402040194042010300201d041c071801c10020300c8150f501100d0814280c00032003101e9038a004072004a102704801c291204860b250101304101004516002404482002c100f180c05454a4410b80b10480b421440b402d000d100c020480512940c0301c8001162000380140141ca0600c1007420f08200700f0051180314100e650001482401250b82510071100544011001400985410700208084140103460507051140182207120f0151003024840041e01905a041c4a40d00f881101d210030400c0558445d40301d102d040319807507000c0c10031801003010b80c62240e47c2c10704034010f541c48041f41000003910340360b0602c0d1603900c2c101c00329a4a000400007440008000e1030034910b0f00d1030080c4021001e81700542004410402d0041400c9450945500184100c0d1140c200983c0040b0710810f40c028000c1680180c003402c540c90805034000b1158826104681c1c541d52500f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 86866898 1250 86865648 86865661
    0x340602090d0b0118050610090302010807030b040213030203060106090308040308030a020c150105010e010503040515270f07050d0c0605090103020730081b0912010908072d06020d2c0105 81
    0x1054110343d11f01e0024006043c1000550301c15100560400d05500300002d59607880008102640c0c4910a8007122115003401001142820080a4014210b80c030344003404905517a5044030782d100b1884050526140071000c1a16004030341d045030014070b481d03002c44040c2440c000c101402c2c19000d109480c0890140a5001010750041d02164407e84e40000501491030008992141401c0007900c0c540002c402c8000c11115174508030100c0300c0049921008203201a03c4084243c600b1741301e50040d40c005c0c2110341c0c406e400908030714140d5040e039506e810110b40740c1c04031400480081c01003c4010300980e1a011580a039204401499118000d912101e4059900b8030003054944030b0701039414020071400b4010303c02c0095040d4000e000107940040c041100d610440003c2c6003541d80480082d24860f0340001c040c02004081d9440c900340303444942c0c80451144039403450483c044504040074050070f40014295000200e00e501280f41600541482c5e0b1034004a103000b02100004442c1c624265880c000200f0341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 86868148 1250 86866898 86866909
    0x50301140607051c02070f0801090503070206180901031110020a05030a030905100e0d0f0207050a030b0c16030504060e06070f0f0317010b340602090d0b01180506 71
    0x1668010260340480240040520030399900c080da00791080c0c014250154407070800c1c0711034509914525402042c0f101e0405414078052003440d031180030160701d4080d1241c000f803004401c0da00b800760110340254540c04076140341085064a5041180c2c0591604004420041864080c02c441c0c1400c1d43d4155152010200c1680d41c0d1a2405010303056900900580c505180f080c0c0003a6031581c85401a51010070f40d405808081c1c4403610b0503201c498106640c070407200347c0e108030a4104280340703200a022403803800340800d150034228000603004407060000280c2c44510141204c84001a04160703859807001802d0040503034004e03008140000300d064940d8026840e0a005031204180c003e148a201180f0399aa010100326010300200c06204000034604c9410741c030051500d00801400390202c1c3d0301d21004126450800079044552104404207044001700d40090988041060f80018010b9a07141144000f802c80302000760000c00c0200c9400021450b4450903c6103086001c200d0390a00403910388004001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 86869398 1250 86868148 86868151
    0x803121509040204050c0702090f0105010806030d05030a0b0604181e0b032d0303010602070e06010804030206190605030a0c050406080102091005090f090906070801080106051e040204050901060c060c0503 89
    0x951041c03141011801500e0182d120307980000c441e00c0802d1810303c069011500541049448450314041600108522751b001010703194080c00c1140948030510f01000064041d01000d020746514550b00d0407050247d40b164000c460107480c2c44561022a80396060340391340a41031036002c13004010404050965804401d01601582d000001c014116201c0b0406d12104200c06a0b071814016031503409294001c1d60003400118041c0c0950b40c054070351241004100c030a800c50240c006410400d14a0800002c00c1c0c0c007003145900510720811001010220401030406080c0e640c111980c0360050100c40700400c01030700403010803160181d80501c400c66072014024200d000303500f401508445444140b2140d070b44124010040321000034907080c00c00041e44041155000212076140c140ea00ca2001d01c000b03035800090b910f0042909200030f20000741000041441c414420083d0100748205851000384d590303498040e01d0241501070041d0802d5070b59148010030703081c0e10304d005680c0540780551481d00244a0012207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 86870504 1106 86869398 86869441
    0x70b130602010507020a08090f030c03010c050408070807050d0f060e10050405250b0d0f050702160f03030503040f0f12050307020106050301090512070813080312 71
    0x782c21100c02030410015035020104c0c2c00000345801c81280c0030fa40058074840c41d642c600705c0210b4542611401d00640c154200711030b9081c2e01758810060402c40d0040030856064581c1d9280d999200c0c103842c022103030030008051112000c215041c1d891251315100702000034081d210305043c0313410003c0c410350a1a0140e103c006110501c081006098a05040d0f0440502c0301e0400c1d00801e4580100342c03041a403000e4003c228400101c44a50003140c042c003943d0f0042c0000c1c42c000f48001d4540c911603080010903542c0c01c5000c01c42e62003a0740c51a0981e1303450740303a01d460f603200c649640f800203900000071a08915041a4080081d48118034401c1c4105035881341510380c1005200a0300307690030b68000e07a00982c0750101c03007800f1541c0012040f081e000e040c0d124a036224624244400c80e4403c02d240b29044c502201c50029241030000300030311a070030411710807481c0c036127070700d810414080084d4206 = true := by decide +kernel

theorem cover : BRFrame.Cov 86690648 86870504 := by
  have h0 := BRFrame.cov_init 86690648
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86690648 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 86690648 ≤ n) (h2 : n < 86870504) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
