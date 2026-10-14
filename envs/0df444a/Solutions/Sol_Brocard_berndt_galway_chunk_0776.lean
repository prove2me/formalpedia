-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0776
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:42:55.304486+00:00
-- url     : https://prove2.me/submissions/bb5474f9-64e3-4c55-a80b-09766072259c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 139388489 ≤ n < 139568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 139389739 1250 139388489 139388519
    0x80322030f0f14060a0906060e040201081b07060f0203150d1113020c01020304030e090a0b060412080408030703020d02150108030d0507090b120603010b0114030c070204020715050403020c0604 84
    0x4041c108081e400c070a031800c605030121620940c4240d01c9134404200803081c0c1d64014000b880e0007a8020001e9548440380c0700350985045802074041a10718003c1151081d41320312520508a015041504151050f0398103c20381d0790140403000450740100034401004610820489922800c0320940380c0302440b85e440c0c1140b0b03449071010f1841070901c600400200c50840e0100e4503440d82d002c000b190361745000d14000d01481c4009000078040c3c030b85403000a261103401e100c1c0200401006015505140c070b4101055143c504042045600c404280170005404408201500c0d490780300780c014288103082050002c3c94049460b482c103080071581001005114804021072f00c580700078800c0400c040e5280041984e080740190710081001070300094940307000c0003078181280501c1d000c50080c01804294801154084402d10303082e0400142003002c01c0300c03040744000404d07000b03101401c05401c01d035880c4ca40800300e041c110149540d1980701c8040100709035041c0001412144201c406909080c248800c004030220 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 139390989 1250 139389739 139389743
    0x609010b0a122c1c0801050d080d060b03190506100f0e0f0a06090f08010203070906050a090302150d200331260a051918080322030f 58
    0x40e031490151980700180c01860300c06a02000f181d03044040e4140c10359503c04064030041c1c01c14010700d64400c41680b0482d103030340c100c500003030070b03030304020700544560302d20342c0c07001c400b00900f240e07141d100003801e494590140d442803092088202380000c00c0c0c0c4100d01540d20090076039218040030001200c2d142d420801807409201640f50080010501401040004480c609000c4c0e03c0100380d03000013100b60b800003041040d41c1c031024080300401c0d07070703902d2440c00c1c0c0c041079a0b01404118182400e00030709208202034988211140303400d010150340d90f008144042400914030f942110005040001e01c0343c40d028a1011520840e11440b40009240b60300205010103003000a0461425901d1841d104141620b411035060414a00003810090f16010b1851001c0000303030640c804041400c11130310302c00d0601307451a000c0302da104e0514000d0b0103014401e00c500d5021500c4107020b4428800307912009407044907000340148100660351605a0303d1a0301c1d0801c0d4241c0300040e01c000412040c0005071409111f026525 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 139392239 1250 139390989 139390991
    0x15020f011b0c050a0c180f0b0a0303030e100603050309010305060105070209010b0c0307050609030714070e04030e01030228020105060a24051605060103020108060a080d0804020f0402040306050609010b0a12 90
    0x810b19140460a002003e035025081441e8548045500100d00d15602005903944200b000701e4a454010705003170b9007d000b04240c4c800c3e9490f07001c0020078041d4002021710040035051780d086000500c0400d04842185c1c00a03209544042501d0216581501c00c5a8004900342407031410030180d0f60000c4c0401e0814010752100700c40116889054400c100242e40c021507015080d248140740031503230203981e50810501503440a00d52614140442004141c520a030f410341d5080801e507a5840d20140d0700d030318070b1600203410540c0c20086c60040e0300389040b0440340500e079014451030480315510000e0070340b000644098407644500c0001c00042580c0d0481d608111a40040c1120000e112101550b56020b02502ca48541d2051100a4100200070031498180e9100b41c80c0c1385000e490342014450900d015005569845e4400d0310003040080c000c1ca0391540c810310040207015071003201300c0803c05a8002d41c2c8201d0301e0585910a1003100e14020300800d000d800c1c01741e03c0c24105115034400400134068048003500c09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 139393489 1250 139392239 139392257
    0x7020112140a11040b040b030411041103070c1719030f0e07030213060b0c0a120201050601120911030f010f060503160612020c0a0f0210081b09120715020f011b 70
    0x1c403031100c3c144e9004150140059446950340c03c1a10708950003102c0444131044100880246494240306c0d208900c100800081d041d07981d02c50301581c2c2d9405010040d14003003c0c45400081102c1d4101c018030201c40c4042c81405103644512024050b6404080c004604500b856900200070000007251011280c0441d070148020f41e5010701c3e2402484990040400120001460b05c142c401c005443c022052160040d00c150507031a0908074202e48080e100b050000d81e03810000c1503401600c0e0030016105000d0100b0080e00018040028580300420314110392907512841c022003038211030f10541c001044150040c020280181c03200355501c0c40c4900034801030000c92454112196101d6054076040d2490340204c9591486500b0038110f101138440049105020907030101081d01c0c0700705240781c000e083e082c2c1103507490500c608060709190043c04056410001002000d41d076407030208524070003405c0c0780681b0b0880a0090748000d0405d02c44041e00d18403a810207003900c00b202d001c071b08040306140281c5450141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 139394739 1250 139393489 139393511
    0x80a02070c05060c2104030803010b0903010f0c080114030c0612071407080301210203060601080901020c030711010908030f0909040f050307050d0306050f0109090c09030c0b07020112140a 82
    0x1d080d1504900e0f0010302c003180d8160301200000324009000c0704502a1203020381c1004903026244034500004142e030109000412009016602500c070f441b90050011442d5020940d00c0e01c00c880c0c0c50422040040da00b82e00402007000d8481d210842c00c00103401074586074040c0004244c45220700031070f29441c00d05c3e60001400e014410b03842002130604a044450b0307114120304006003541c00a0140300c1f0300001c110211501d0062203400303a400300d80c0c050040d021a545080041d00e84c01e000800c020001c0d5020001820f840b031060005007445881003e4864080c4144000144001c0c1a41c001d03400540c010081e042e521400d803001d032901c410381155030a04680e540d1400c4503083c05118802800303031001190704c1c0d08028000c1034008580d8066a800c0004503a9030b001c22009403030f514466800324110f120240101442508240d20b90081410003140c17442d566680c0c01c1c070307182c1c150f44907486240011030342c4811507a002040c1d91140d00340754010b21045080e03200d000030651000c0d00c40d41003196661844c583d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 139395989 1250 139394739 139394753
    0x9060a0e13171201090501050418020d0809060d0e06010506071e020a150f020c031b0d110d080a020115030b011203020703060c030b180106200a060f0f0c020d080a0207 73
    0x5101e0416840d02500d0f5880361041c0c450700300c2c003030054003c480d050400104d00b070b0070a881101c1e0340c125507485010241e10542c00303000c031000441c02c0561f200700b000c0101d0042031320f8441c000c00802481d0100010303055915481c03182042c0c07040c0c1007244105030812551022840a403402d45804140140903040d1840a01c0094070280f555803041c1405000c42d0041010320746c105109859a00075602a18502c81207281096110540310310344005240c096a40300115050084001d07e145128010b0007000d442c602c40007840c0781c1e6804100b00c41d070300300014102240d55420300840d0038502c50f101c00c2c10712040c25030b61018500101409807006107060b810504d07041c14800c0090342c1c006c64005204000381c01074101c1c01400b81100500c40f90050480081c4150040c0100b02143e048600300ea681c10130200036101400d8289401c4500003c00d80b00d514140c0012881034032a02040070f0071034000160144171181c0100507034141030255402d5420002d018000b00d0f07040145181d0009848600581d0b41d249032a1120b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 139397239 1250 139395989 139396013
    0xa051005041806061706060d11040914090706110303040b060112090b15060705120f04080106321011010e01110a0801080f0a02060711060307030b09060a0e13 69
    0x2800c204456400a0b101c800142d0000003902c80503500c80d8182c800842000d200240240d409a412400410400a120006030f01146111510b500064541903442d0110300c140d410028550340c40710808400d01c00c810604010307081c000e00742e03402c0000c10300341c0006685490b030200070301c09401a4517800000714540e21420b4011240c40b00c20104000c0199107003041c80800400300c90781c60014002d4100d00c0c0441c64800140c03214103070711000612001d800304042880641140483c14400c200c10b00004c65244003e00644001c0d240c0c0e011390040259031071181d20004010300500c40590350640901020680380c11881d04008003044c10699403800c10050342a0060100c182d00c69050f502e0710f10385142030701114000b041d24440b0b0f5070355580d880e42c036282c20544480303210107070040303e0307021440410050a0407409049070a000d24407070002e8103c008041b1f90741c0c0c1c0c01207546000096450b00701c95440d240c44e0604070703040941a0f0350f400c803050400c211200e0703060000e800c0e0036203104904800410850481110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 139398489 1250 139397239 139397249
    0xf0e01050d0906050403030e0c030604060905070e0f060306070309030c0201140d020703080603060f10120501060b04060809070603020a0906030b040e01020f0a120b0607030503100e090a0b0a0b0a05100504 89
    0x80002c400b16040507801024240c4003100001e0070140705070806240061010480c00c00140a0002c944032559503200500b6942002c40307090080e500009100d101980c48144200f20241503010f15207810010035003040c0004251609041c54081c420010a82c4407a1a002e0030f542030030b00075a8840c0c3d0b030010102501070141d4244141d8000607190080542c4010365034028041a81101c0c8142c40314a14042180c0045489003c8841545401c10102c03070480313584a101801140006880f94540c0d281d135500350f025402540100740118140266220304104680081c14a0310302141007507200c44008082250601c510300c205912912902c1c2250f540d171b0b1010400c50020740086681d204290854802e54001616840100d01d00380250041c0d1071180c010a1601500180071901d005182e5909481507000070b480e00c4902c05403800007240740380701c1150883c0100da1460061040c043d4510b00104801001800140d8150801c0c8112440d03031100750300c2c1005d0343d1048034030003a21160640c044400340219803003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 139399739 1250 139398489 139398491
    0x30103080a03020c070302060f0c0c0406080a0f060908030708011409090d0e06090415031e080708030a02090a06092607030816050304090b12241302030f010e0f0604030f0e01050d 78
    0x2209101c80c9e4500062140c04c00c0801950301e4004103030700308800c4844901c40c650554109881c014000303041a500e02150b01e00c100c10010f8401140c0d1909201504101d402101180030400103010840c140100451080300c100d4511845140901c2407a80350303030302e41c2000010b20217039039444643d40e40c444065980300d80000e04200712040f03100c06101316280051100780c40f003041405980e960314412076422600140c01c1a502403a03d03541daa100180c44e40300502e8151040d5003400b0b2403000341e40e06174441d8010301890361001c1e0040e082002900d42c031038480b10486110103250b0b000c6000c5590101d09001101d0300540700304c0c0c98070aa80c4100080809040008126000018010031a40001d42c0609071803542500c264031100f0b5821030b8590b42c0e1821541c9103030425102d60320700d07020003180a81c0a92151610340072161140d2a0341c0440e140243d440d100a9040c1d4454481c20302001d420400e1a800c00c000234010032407820540c8002e80900c46910300032007041104240421b190f4080c5003251310950440700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 139400989 1250 139399739 139399747
    0xb0708090111071d040201050d05161b03020c0907020102070c06080a060614030f100503100902100207050a06030e031e0a0806031204090e1203090a031103030103080a03020c07030206 80
    0x50120280d51041003110301007103007070611802c0c140b00060010180c4007035512140f1500548140c070022407500410890411804006400004040d400350134003071314200801e40d4002c80510302c00f0300060300b1070003401a4540700c6c440d00400f1030f500191031400c01900f81e80629068441000403406840390000c0605074196074440000d100e42d120400b58400c1e1030110bc02c11189407100011248000c0300800400c0303101080c401f0800705030080d6034040e00b166458506d519115a6100401c0c1001d0a40750040749050303852403841c1c00c1d41440f0507a02c2c00901144017802c051401e11002841038101c501980c0101507a0340c0c1c905a10040400464040101d8030400d80410300360b0100304007280d8401c16401e000198882d010902a04001510008090014100360304103421b2111130f5008060304070601a2a02c2010701c1412940704a800650203000c2120241c490543c09040c00703071500f006050f07081000d40c810401040451480c80c103440b02d055042c54003503542e99a2003100e074a4140302d904080d5020308005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 139402239 1250 139400989 139400993
    0x12f0702120c190e0c40080d080a0203060303040b070501090f08040602011a03060612030d0c0c120e010c0b070c0210020f10050c0d02070213050906011d042a0b07 71
    0xc20b03480f04840582c662403050341d0760028100003c0c010b81d0042c0143c0d0151058019141c5880001c10391690181b2038003480c40762210111001180e07259000c0c01950b0081d20850300c149034881394003544911466400c2d881e60a190010ae50307240304607c6000898080441c0007810008290030070300303245800020b44030741001282082c0402d13510600c03420740590b2800044c58107020071801c440780030f00c500801600c820740c0c648041c040c1954403d480c3c0541400100941c208107101441203507803036006541e80c6003102810b03180281c0800411800c09083c8041d40c51307d4aa540e9008100020349d690028140d10180c5811006035404102c040c4001d41c00f028103a1002000759001800042503000d41c0c04039030a00a80a03601000c0740c1c0705a0703440740d000804200e1005a100d0640003420100d202500f6a1190081d0b044d000c01191000da51301c40403900044d0040048074481c18030002e085031400607884143c1050342e510b4151038411441e001200d12180f44480940000220f41030003030040a15442e603e40c054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 139403489 1250 139402239 139402279
    0x5100b0d080a020d0807020109020f010e0303040317041706010f03030507080c031b0601060c02010c080c070b040f03020405060907050711030705150d05010e010510110109080c012f0702120c 83
    0x240c2030f9030300005d00c00310004400a10502486805075000341007000402c2162004585211041510070782521081200000094034021001c01d0044c241501a03100c0341130041500945140019042041c0e000c00010710013220b059014004882d40750804a6881c0900c1ca812042e0340262415600c840c0008261086400558400040c81c0c000303940548120340e0300c071a026241000c180354081d0009a2484004000a003004010030140303418504541127181d480c0d0142c00b01d070384140c03c121743d80001400c08004500b0715014450f0440300450302d24440d45080c0340000e049000303500c07001e8000340030b90042040d6a01c0078050705015210141110b01d0720103845200c15003c2d4045605182d400345000c0001820030f403a0013960381038650040900c1c0440c0d100160488514140154414841d583c5004500c005000e00c00204000881e0900100e030070b8550403104110745116a000a00b903018141c0c2168400040f0000c49a50035412903510b40f00569100d4035502c2c050201000d180c00c00b9a9902c004c15005a07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 139404739 1250 139403489 139403503
    0x91a010e06040501090225020d020d0510060e0c091003060806181b1c050f03040303090801051312110c04050901060e09030901122a270305100b0d080a02 67
    0x10560b003d005599031582a80c00701d22a160440343ca4280039403010499076903c0d007803140440e0000301034003200201a000500d2004032580c1c11075065111110203c2d01b46842c2c011100100081b412410903890710a0030054244589240039204401c1d41c09031101140c003036440880500a40403c8400500d00f401e00c001e440e6600321403a10003803040312000009044d0301c20540807410005021011a005080300446900301880703412034986c081c0950099400104002078002103009540703d8603e41d10303041d00303c0c1c00c46401034a8220030300451100310000c40c0d08a5113000f00400c0b280341500d95424200011030900200a41300d03540301d42850240045410150002800c2d1924140240215144d0400c240d942e4460305c0c4036113020400701100441d2501055210a00c49140446a505401d6080c2d645003d4a010800000c0118003c0c2c03508040c848080c81c0001d07103d4502d01d890500040c2162506070791005490038042c40b444d190a003002031601c510807a1410a54007607070f440d41301e100c000e04c081e40f200c80c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 139405989 1250 139404739 139404751
    0x120f01050307080106030c0e060a0909030e0a060c0c03081b010f0b01020c012303060d0b070c1403040b0f0d180303020a020c040504021e0103020c030a0315090606050d091a010e 77
    0x108440340420410f4040c0300d480d0803254040c103a0418107241041441002c0340041c04250b1044030840c001903403102600030440d03001d100c0d5982d10a12002101084402c0d155600a41c00301308055412400080c0301c92234540540f5002010551241070398010903030b182441ca1400c034425400d0100658180500b5000010b005900740c00742c0c1d0010b0401e000440e202464008103c21040f1050703c160806000b203001150070020290146005001c15181c85048580035525040081c0090b04524240601c01c500c45403c1056100a145014604002c20307804e03003d10003e0445e00030001440002c144015842903a07200c0c5a103c10064840d01c41c180039000790407900580c03016005000d081100c1c1d1400f803085502ca2580240350603c444000760030f89102c00b601e2078580b411700d582048040d002c004204050130746001d0698002c41d00203c0084207982401035903000c0a00582850801d21005030010141c80e44d0003205100011322684504051382108811030042650031076450000c103e014078543c1c00f921502d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 139407239 1250 139405989 139405993
    0xa060908010e0f0706110c100816080c07020103051008060103200306010b0403110411030a0e0c030303040f0f0804090515030f0705030c06070c08030a020102030420030d050708120f010503 82
    0x8201d01c0c02064032541e0020032020075801604043c402d060161000300d01b070801d07001c03c07034410550070804281142820040e0300e02083e03d0320104a4480b0100c204030400807068071701241d860910710900c540d1400303080ca00905154642001030040c4402800100042a0480031210156541d041c031102110140744000d00c5800411007856250500098040c1201c010760358151900b86582c071001d901c00866410980d00c60b80702d034402100310001134041c50099403280c1c800035608801c414001c0c5030000c007100da1406a003041c02040081282d12590700c21031600002950b03400c088904d070000c40b503c929040054440d20b040c00703200401d000000d0b2402864000e40c11100b00300780c0f145160ba0744c0d001620401e83e040d800100d900036203042140107007100c0d0b031142420f0482c241d1583c450a00f581c100f5002c0e0030040c5c4d4040308100074814140c1c01c600928411015000100c0c8110001c2174842507001c40540510074001103540400c45108100c6207845401810610b550400c007520541c585801e20030f062181c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 139408489 1250 139407239 139407251
    0xd09022b05060f190504030516111002070b04030803060a03050d020a020901061803061d01060b070317040c15050702030d0804050628090201090e09010203040209130b070c0c050a06090801 82
    0x3c40300c140310580c064601c0d0801d64100461420b03002c1c1c0a09030003081102005024804030398410600b40c40f04a441c3d06c01c08080640c805c202050003c08000d00545604561188404000d640901000c64003503a0300210100c0e903913910710b40403681c04150341d0310080052186030704403668a940400d80c072480910858881c0007503680c030002100d00c0680500c0c07a81401c800c000d000c000088080d8803480c12180000701041c10074408803074407400c54005502c00006803100003020f9042581c0403009410500180303034207c46a040585030492003440c42e0150a444080541c400c040441c02034080d14240341e030060444058003000000180701410548085450b8171601d0003244000880303007d440d015400d00e980ca0150000084a150013401c02d104090303040c0310214030045940340400883c9480f90a0003400541c2d42d08051050003100754000705250b0f561705e0b00c40107403000968441103280d001903803468002c0901c81c590820f00c0300c400065001c0356100c04120300005035140c1100340b440803100c8810082042c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 139409739 1250 139408489 139408501
    0x3090d08030108150105130c141201170105160f02030d0204090905101109010c080405030a0c0e1f0501030902130f060303030f061d0a020d0609020414010905060d09022b0506 76
    0xc0321800e015047c1e000038001301c04003290748a42d0018614589514180c01e1002c0441b43d006600e03480280c44405514071180103020b030030101040e248290005130020015458141960700922921184010401c070070401084416482002030705e0782c00214000440d5141e5850749000000c04110104a50501031401080841d18883c070468000c0450010910300d0032140000445d50800388040885161070284404035407500c00f0050001c801e4840c0d104400c2c540e041c0b014904410000804140900c284004c842c41001d1070702165104039442030902181c200903074800a207072180c3ca090040301c2e440c9002010040341005411040480740203803030401a0b1a010207015042d10317264083c885012004e00b501d4445140303a0340081c2d6104004040041c1003840520f2900d0a030740195000c84101600400e042c0130b6a01d400d1080d09110009091083d280c503e06800b140050040c46400c44600d5070319510801503403031301e10300d02001c541070600c144800d0410010303840e00614000800d65142c4603030000120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 139410989 1250 139409739 139409773
    0x130b060a03080409150306021204051204081c020a020d03032309060601051b0f070f0603020a120b010201181a011509140105070f030c0302100605010509040e03090d08030108 76
    0x42542e40200b24245082d0414610001170104185816000ba070b1641c2c001000c80e1061018102d820000c0038a00720500741410b00038a0402c50700403904000000300010000810002440c034606039840b884403200390b4004034207074100421400082d40094090a4560070183d0690042990b0600441031140c0c80340c1c200302503c00510100e80c075417120782c05080851035030341c002c2020f0810b4900400c100e24012013800d081904140c00030741103000f194400d55090044e8980c074050300000c1c010a00d4214140000d010000b0b00c01045200391071056a5207030710380036299100703400040304a10110b044200075403036417418500281460b00e910300c1c079540d440004500803010700b02c48000716a5aa480c081d0711420103640c0ea00350f500321040707281403050800c108400511444001030580e8000d4945003844080e6080c040d00f0294501c1c0003c032000d182c03080c07e00c541da8000040c1c0c0d11041064a0005100e0400007000d0f00c0c6125003080982d20040050420040222100c025816594a90150fa140c1d940d00b10300c204c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 139412239 1250 139410989 139411009
    0xf030f270a23030708090d0804030f020a0b07032c03030406120c030c17070309140c01020d05031b130e01080d020c04060501201e030c060609130326130b06 68
    0x80540c004002c85404256100d01500c41601d0003040000c6155080d43c412300c0e00e80c401d900c1150181690302900c030952416541c0c12000b44140035503207213440d5103940c0044c401c07012100350a000c2290608860000c04d0002c1a03110407050241c103e07541c0300d03282c41d00604000001c40b10401507509204440e08114401d0140745214001501d5450310090021030b01e0a20080c020842010969075142d088049210021681c5440103c0d001500041e41680300080c105601d40301e4000901104100784000c1c80b0440c030442c04c6031105c4c03136069a05d4449681d4100c5150040760710480a117040c000001c5151040864224210703a030980032603880d4061041400192100351280703501240d042c0460042c424282c800c1303942102d8210055444000380300810102c0d504050a41040907400822950140740040024640004045400302007e1a0041c941c21202055450040401076044200c5154a0040450806401d4100c0b030101440ca40300b445148507180d80d0700305450b560446004104a418015200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 139413489 1250 139412239 139412303
    0x5070b0403030c08180a060302090f090f0a0f110703021f05040b01050405060402070f05060106090f030c050d0302070306090f0201080c09030705010302340501050108030f030f270a 79
    0x70f4180c4031019141d843c0c071034100402c28890403541c0040507415940d40190750002e80026140107880303140d4001030141d10310b00000707524092144901801900c45c044c0503042e5004030899004500501d1000e841400b404500141010710701e00032500b80704241c0c02184041c1e03400070060b88080c0800c945090380381078070000d503009000c24842c94014005405c19401c29580710101500161410100c0d907240001c0201480d4151100c0c1c11210041c040e00da400304808008200001000182a046445501c10302d1602d102d854410f820609000007010300030b0110000442d0440e00400c894416410004009055060700b2030000e00100000782d1985000c000752190b07003002138000d0656a00700001900290310941e0f801c5042d19406003603000e91a102c01e101d40421981880d5100980c0c4d41d840d1050a68006030440b4429800c00c1c005038145000d001d003586e0380500d2500300c08046803101040304280780f01c0c984a40080e24100e08044541c95800103007000d036030303200d10b4200c90324070b440001071b007082440d003045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 139414739 1250 139413489 139413497
    0x2030f0307030527060703060501090e1906080d0302031605040806040f060e0d030204090609090807060f0f0e0309030c010305130803150a0f0602010b030a15051e07090305070b040303 80
    0x1040c0300341e110b0b07404180d12031200320580707013210711004902055100009146403280d2150041104a50745030150b41e00510013801d2079081c003410300304113208048000b885603540130041440404801c4190b00128000c003440c10035039910021501004010f94012121002600030140d051201d06100b203040f00e046a81c1c9502505403502c0725036800410207a1a4000c0d58241e840e04040649030070b003405125000040ca4800580c0d49161010b01c50550f0701e40d074000e41010789445400300110f1001412039541e81c1d440b40300003820809206401c0c0082000484064020346008854500960008000c2c1045007045088442c01c1c90315130011400c1d81c100b10340010003540f002a05c40f0004503d200a15006050040040c3e004022603011454000c1c20f40e00c91009101450820420283c0a01c1040c0c0c200c041a40070344842c11b01c644403e4142000a032002995545d21000a082c140607180074119104011504240c142001c12005059054a00095825000d084000a5104041822907040343d601d911 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 139415989 1250 139414739 139414741
    0x60306020a0207082a10030e0129040606052508030112060b09151002030904050c03061905101209020a0306020915120f040309080303040c140d11090702121b010c02030f03 75
    0x6d20910341d890780354510525072280c1034900012828001d41c00c60003005089001118100c09040e0086005001c07511b000e00d24000050150b15400b104803904801190014514540e402d1012040700204140186c070180f8080300200c1c0a41e190100c0740d040c50b02901003400110300ba1010480c01142c140e548910f0455400c0448107107040c042e401200782d80c01c0d40156800d0200b4440400c0546400f118012280d21001081050900d031000709402081545000c905025040001007141200801d0102e000d100408026424428803500282c001c00d501400e60100c066a03450000080d4124002c102c1c4202003800801081c09480010f8135550010340000304125101c00c0500080c0d1000070b00103404009912602003100c0741c04000070341c011031150041d80b074000c0c64900044641c02c0004003c520905c51341d000f03840483c11400078035400c0714040b20740c071034a5200c28100380d103420a1b1090350540c8182c00320340c81360390184402c0304810910343c000007131106a800242c101d03102d1141482410800d14140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 139417239 1250 139415989 139416073
    0x70801080d0905010e060c070e06120f070302010819140105030111120609061c0503090901050d0201121515030b030706050a080109020a020a17091f02030a050d060306020a020708 78
    0x40502d05d8010406000546040300500c00c05041180540121031300311000800d01126040803070641205152110203040c5425a14801035140e590901c0080d0400402c480855152421444004000c907204182044548071007101c100300071000740308c5c091003940707454640c0141035103003030444016421000710301c6410743e04c41c0e080102d11480900400d03040141c4840030035a1800700c3c0404d003c001e000e100207603202c010500410500420581005000710342407404400180d8102c09003180480d950303280801c1603540000f4000c84005594400016908100000113001d034259000e410800d90036001c0d103103400d840707200070341d0113200311001040020240401000003805030f5010f0990a02c1030320584182c0c0207140c0700c405116601e20b00d20a11404000383c8940c3e2840e0803d107031004040ca02d103c1c0300700700d0030650f0003946901a5400b8442489800200702103120125400720028580c800d60441d1203d10684000759030352014000da510b94402d50311140f200c40302c60000e9280405498540d000094000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 139418489 1250 139417239 139417247
    0x605040501140903030403080d0b03010204051c02030a0b100f0b16120c05060c0408060f01081f090f0c0e090105090c130216350d0504020102070b07030305070801080d090501 76
    0x142d20701840742400102035580d41480184000d601aa45440d02c54202c006803104a402c5501c10380e00c01c3e0300c10482040251900c6207460001a100002c8000348601800401c2c00c0118071f4000034419425001080440340040a01c842074402c2030a00c3d06050b41c450440c0205d5103e4514041088a078815030100060207080d0f0801100d01240307040210b4500e91f5031460301c2c021007907a018008280104042c420342104010840e0301003480c44110b03150b549003d03842ca441c0c00344002081e280d6052501034404529041c1c00003003e165118041a001d012035003020940340c0401c1c0500030a010200740800d803105814064a401540c0100180c10350042d218200a23005054000f00e40e18035401340b00c0340c0ca451503200400d01e0103038000c5206814801c4d8800710308079108421816540c1110100c1c22000b040c04c40f510686640642d08000081c00351903600040c2c0c54604540c0c0303d81c00010300041c5c850304040d03240d00441e009424940721207200e642c80f800925101c0000040840000d000701e2800c011940c81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 139419739 1250 139418489 139418507
    0xc050405090f040f0b0109092a1707031a090607020a170715050901090c0501050f04050f010903140c1009120b060406151707180b0d0b120a110603010605040501 70
    0x45031503003030080c0c0c02c00d64605c0c40681c400d0340100c1385656548107010078040b4a550804139640c116040031080e61008004404070070490041e101101c07400c18452040d000300b04000000307180c1000b1a030040c00341080c5008500350701142c91900c90700585012030070441c00099035003180c1c2d0b84040d0b49104c0303542a80240900c1e822480f01514810f0349070700038130032206c0d9a1184901400c40003001003130301100d0341000840c00506600040c1004000c22250104446000646003a0381044030f0701c0c1a06a011401201d1080e0960030140482b40300101045890400017403c840c07644003911034420000002d00203580701001d40c840c011030344010311800c03030005d10305010301540305100038000903046032119070007040b035070b0b01c0d550140102e03110b00c00f00c40c9140344a46e000c41d0300100c40c2c904000050080350011116282074480c640d5901008508045e070358070365030080c420280010704180c0c2d200d92800801035075190840015a01c001c840714603804c040c08e1038021a8141c0d592510b402d854980340000440c1c070740c45 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 139420989 1250 139419739 139419743
    0xf08040f020a06020d0305070e1e0d02040203010f0e0705040501050d020309070e090a1403070c050105030411130204060813030503150f03100e12040810110c0601030b0106030c050405090f04 83
    0x81480c54810040e0744030a1076502074a81580200864a05080e010f42201c0000d0201d41c14410201c98a091036a10242210309001410300c03240742c83e131004c1002c140e0591488500a51160000c000400c48508440216044030a03490404015440387e510554940c49540500780c0091020408000a240550021074000e01c00400321031142d40c0d9882c01c249801420f951500d01c541142c02c50000740b141c041400c508000403d405036107003400554605c581101a1b1050302c0c140b010105c009002e02000321035004018070003a054000c000c02c0c0105100096215024a4000c41e003503c000c28040c0d11000251007003a07a05454140c03450321540304a601018803820345540c4904448044406a01d09001940744401e41c1e0201284400000c0215414190403c0390001030b00c4003880704000d281800510041c00d0068080c0020394003580c8808100144601500842c01b84213480c000030810411340d000504031515643c082007294a507070030485162185200e1944d000701d180c3c0c00310741408084440590024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 139422239 1250 139420989 139421003
    0xf030c1e0a230d02010c03150e01090c0504090504050304090507020102070f0602030c040b0f04090b090708011401031b08010f050f06030a0b06070f0b060108130503030a0c1b0f11030d0f0804 83
    0x800441105890300b40f0b0350401c100181d4403034180e03128094050040384e00c0854525690b100d020700303200e8819402d180500ca100000f50f00c884602000c1c60040d0200c6010b1304410405001c58a09414204e03600d07417292042060907498100042d00d042e1040c802c1d2844540c0c40522820070700340e107844403006500090182100034031704000006000901900400342108404149a1107134035100a07c2c04a070b5401c4880c5020780c3e4080204a00158801c20752382c1903a4050000000300350690300100c0050124003002201a0b00070308030510101e0308403404078100d81c5101c40300340340756440da030901120650408985400078400c1c07020481090b103a42148184040251415041c02161340b20701e00300244c03d8a0544413103046109001040d60b1014504c2e0780440c10446400c40183d4954407141c0d01e1000a0440d42840d9507041401a501d2080c000c0d50001100005c150384400a80c0c1810843ca000006041300c0c2d03948a118480000c0c10301203032194806a8688513502c04018107401520f403400c0050089480c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 139423489 1250 139422239 139422293
    0x15010b07060b031f050105041b12050a140c12010602030c03040b0c030706090b10050301050412030509070519080606040c08061509090708010602010c08041e03020109050f030c1e0a 79
    0x11074403600e1310300b800404066003c12503515100a0008441d900d01359010070181c0b0481c20702e45113400402c1444d504c14001c0b0b00107566914680c081c002030804440c01c4001501050500443c00307481c40c090b00c103911494201e580c250360790b1003050b640c2c3d02c03a80c4140c0403a9081400100100354005d0040c144410030901982c1c5001300c55682c000860707054039001c5034a40c0307030502840500040805440044e0a00754020000d07400c01e40c4604050302d500c0c6080004058403100015100b200521602d40100702c00303450601000c143c1602c00c0ca50040710b010f040340c10b100342d07130000b2000e1030540100315030101540c071000b49a44a4030144a0200e48ac0c1e0f00400c2800410041c000094a0780f03182a88141100e070741d24416941041c200a0949500703420481c1000304200074000454003504006818100175004000603440600d000d9000d4203841c0c80140c03103030280c1080c0d81400350380030005016584a4005403440b002c1116006040001003004211096100e4900d1100245140d2554a01c5050300441401d030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 139424739 1250 139423489 139423513
    0x70809190f060f170402010302071203360b1807030305030103020a0501050306031519180203060106080103031205060d0f03030c03060807050d080a030b120a0515010b07060b03 77
    0x1030800210284004040d03880410464005a40c000301400341071418002c42951208018510300d008141000380007103410100c0e0843e80641d0440305a10b600c82083c2072034800620740500204006107490f4210051015148800c40e0700490500302154000c00003034581e540c40e201c103000040010f000820740d02c0040e1225210301c2c800c011460085103c0d41d85d441da658118414440d03601700c207501c480e061100c1482402007507034011a01640229034000380810903070303c007280c0f80c051013204280c51501610308142c1d81080e01c2010848103001d8000da0440d03c150340d813880e00700c2d0305a109202c0a00081c110002e9090400c000340c10007074015500905c074000d694110780f91840441180303001200840c3c2e59421740c1e182e890f054000e400090690754050800f0300d140c000030498034554401c00420b201000030380c60f00c1080c0a50f10000c82c41c031002e059006540050404180d540300991003c0c2e904c2d10404e020411b40c0541040854141c803c140303442070608000313a688001410a0b40d40b040d034140a003400b9004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 139425989 1250 139424739 139424749
    0x1602030703210f03060b0d0c031104030605091203040308070c031e11060a0c170414030f0418020301060903030c05100c03060906050d0b0112062d050a06150302070809 73
    0x107181c0311050b440d08201039001e40640a12601d440b0360080c94185081008002904001e840b1221400d81c2c000c43d014019038000c8000340a08101c0c028908004036000c0280070099001034800ea10312402c5401a80c826400492030b8002105e00400141e5642c0004004a03c243d884103800c07442810590814666081c0d0300c3c1b2401d41c1c8901c6400010120250040149000c012042c0c00c0288600108400594400010560000700640e40f201c0211200410208800d549440010a0208080d02c3e00d541b1200e6240245502034460b0342c0e26401d10030949110000c541c42202d04949558842141039451540c0a803000d024110080d1a41c0c040c01001440300cad2450300580c44103949a6400159607801c1100d903104992050300450f024001080b90200000d1200c00d5403030650f1040321042c2c014603000e10b001c0000e4049003403290080054404086101800500c0c60000c54441c0d5600f80095600c000c0881c0c112a00c40c411010801d00049440351110300940c01092a40d010300855441c1116003000300e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 139427239 1250 139425989 139426013
    0x9091707030509060d0203041218062a080301030203060a0501050d02091e01060305270309010e06040801021314030a1119051909060b040609030204021804050a0618060303051602030703 81
    0x2640d4950004100010807010300ca030309c10032005a007040152025520580c04a5903020b010f01000c0c0049103500b00b00d0344001c05016a0906071045030a41450144e15185040e5042884100d000b44a620301003803404002c2d00819068510150051841940d15001c2200f02c176001744c03c4904031178039211019541c58420440303a0284c00781307490100300c500b050301b02ca0089400401d5a80c0b00d5201200d0a210755a001104030b81403400240780079100380b00203100045461050358481e582e2036100060307012080801c11440811160300001c0d52502241c000140f44e00c50302c4035000207082000300d054a103034502e8905180d103244e40c5103e801c4141603403200b000c1584504514060264894900010029000240208009880070860b400e080c03516004c0c0c00740030800076001c000d105540209805081410001d109415400010310a11003400c01414510051510340a49044d178210103102c0401c0210f00e021b502c2c1201c0e89a40d510380303006400441c90290340c441038400c03641400340c01400000724020590360 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 139428489 1250 139427239 139427257
    0x2404020d0204141005010327080c0715120204061215050607030c0b0603030c0a121205010902070309060806060702090a15031a130b0105310b0405010909170703050906 73
    0x243e00314140104032990010456000c28101414450050520890444a1080840c0c2e8580f4110030f05070b1442c1842c1c4500404441280c1445a00f00025402100f50300e6100104600d484074218180010b403002e050744950701a00000c5103020b608203207080070b075501c030b1000f5001001e2540450307929140040d4080e4014032082e000a80680841c00601c101c0740115a00610103e00440c82c00401c041900e40380c90b900c01001c1c081d08286c46100110030301414985000e0304217000100203c1d038450080e4402234004010640018642c010007003042c40c012103140e0f0041400070034290a0240c154200604400d000341010703c101c7c0c0341e0642903101024402d400c00907610896650308196520f03015a543c1d078400034860442441c01d41204004254206022410340d032040d51211201c0044042d806100c07a01e04030404050410401848202c100d07543c08255212000c031018402640da5a2807481a41c0c008d15003d4005000055030703c00c000b00841c010300e81c0921a0900c58180800f140028010340c01c040c10f4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 139429739 1250 139428489 139428521
    0x30b06040b03070906180203040515090f10050906070c17070206210103021302030103081c0e060103080a0906020c030c0402070f0614010302100201020315060904060506030a020703112404020d0204 86
    0xb80a1b4142268804180202e031100840c150701d07282c0c540c3c0d5560518100c0c2c0b541c031301d840a0b0200d42094410f0040d40881c40301c3d4802c842020843c1c00d031190040200312078009140c060400031480e078500c540424440150090070190340b01014180c01d0400c3ea104000c00c981c0400e08008100107000070000c004c030031044030507d03540e0543c918018080c0200b518076600c402c65104000600000304280d081e40e00107160712034031207030b84a15001284001c1012869071900e030f20030b80e0700020400040720000c001081e85517481c10801690707800140e9070340c0c002c0381d00b1941c950400c00080d0740f04d06142c1d014010090060700031700054a166103c210882c4c024071101040d61000c00014419410030f52034100e28080c484c8004c40c6980ba02c204014014442d1449203845007200068019150b1342e5a0405c00c06000000c211039070301d0038110400c0c40258040d000441c04540c507800304c480004c1001c0707140d12107a8502d8403144031800c1050740300c003100c502c02001213900c80c014005050160710750b0710503c0840c0c0b0882030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 139430989 1250 139429739 139429751
    0xd050405011a15070b0703020d020d09020f2407020613061d010c020306060904170a0e0310150905071b080c0606040507120b040207050118210504030b06040b030709 72
    0x70308180d1220b0010300e00e07018032400001440d03200000421205200e130002102d0b0031945413054100c01a01c610310007006580e00204614112201e10750003e81042d02c04c0b582e12060140190501c0840300c0c400040ca00030180120010320009242401007051a10043c450313454100080002c1e0b9501d00160099030001d41081d01180406034004240d2020724400d0a000402e041c00d540025596480105400d004040303440110b01000794185d60001c03401501d8070b070203440e103040600007042c2200100c807982c801c5c4158454400920359501c541810b5085102101a038181002004c00113071202070414020810303110034101c4a44061140541c80904c1108400c0d070b42c5144007a03413407503c2c0c800752185200c2d03807074003081c480071036003200d41d9040200c0030f000040f404d44055400070b17000303026080010f003a40d42407850608002140c40c2d000c0301400e200d60840c0c080c241d41520070511081a4240500205408100c18404501450380007948120f0040000c075001c0a07400200c3d00700703035566000d15003042e2504c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 139432239 1250 139430989 139431011
    0xd090206040609060806030102040308180a050405090109020a0f030503070b0c090a030c060809010c0207060311040305060103061b030506060307111f020a02010c03050402030a02040203041704030507050109080616080c0d05040501 100
    0x17100207500098110000e40c01c160846d22110f68601c55007008080c0a00882118082610f6082c8140000c003801001000180760011449010f001500c000b24454061000c0c0072070300c00300c01400d000903650850021810014140c2d0303981c2494001518503115007000b400400e103541e0316440d1510146129504420081d1b01e0302c0300c0500384c400b01400b1415a070341040b0f40c0302400da0340002c0071070448489183c041802040c0f1500c4401a2185030400341a90091100200c140f14154012910201a6508000e545031201c1012000c0303030020b9030b00c1940203000308085244148100701040300128418141ca8000d4503403e0b088040d009150100c0180640106100c40e500b60203121760201182070341014040340c945580003d44800c1c0022000b0b01c9140c0c0400440c007031061100e186401049200c0c090b555850303d0707003019643e8400c1e51085c580029185100880c01120110704540180c2d004d8501c4141c0743c5d400b290039100d0810042124885081c02d020001c565807042c015503010703500480000403801045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 139433489 1250 139432239 139432247
    0x9030b0f04080706092d03230d0f060824071809090308040501060801090f0803100503030c01020705120901121a0415091506021b03010f0614090a200d09020604060906 73
    0x140109440f094041c040d01b8046034214a511a1004201c00c07aa5080300484001440c98011081116585807901c080c01c00240b049034003040680e0700210032106480310200440c0300081e01440110801308402d800b18a085000d04520000507210544840d10b55031510240c10032100d003400140c0000781d0103814002480000e00c20500a0030400e0024007244003a0f4030340c0c125032003066000602c80c1d48000005000304404220400103031000400756641c41c02000780a44c040e400100090310503014030384651310702915031000c6030074220040e154400140101c00c1428010003c02e010211000b07a1845451150350300c0e0f219003600c0c46c841e5401c900c03000b0708024410013291a06030001d02d001b1010350342403040790340000700581031449054404594800320808240074003000040480384a091130340100d00364941405403103440b60301b51610801a0f50320383c0e0480640328000b5010300c5541e4607070102082a08a180241144004200c01060050055021840c1c60f4020342c80300002402e9044248041540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 139434739 1250 139433489 139433543
    0x31b020618060702070e090307140f0114151c02061b01061a030c0c0708120703080609011404020c15090c030709090308011412010606110d09030b0f0408070609 70
    0x5000100014075203c50040d42c1c402c060701030f804148015800003920013404100301c40c0f25503446810054a031402036071036540e0300307401e402044440d400e00c600e0201100201050601c05c0754655940e00301c00c00050280a80e8118a201400340034031940c0700078001d44c6540c0010302c0d00b9100ca00c41d05c00c1e00e0f03504c4401c490071200c4540046035800d101030030b580ca0401a5030162034000b19121842540e440c2c6010100c0e24041c00780d842240c1c01d0282000c1140c1440800c4054100c0768040c2c0c4960104c0d0b070f2080c0c10070041e04400d010348500e94103070400060080c10282d01610700700040340103c40c0c03040d02c0c4840c141e40031030085030564055440f02054a1060a040c0601c5d0003c0442800030b000e040026038000c1c1c1364001c1400f8100340112040b440c02c085607520454a800402c2250003080095265071000342208504240860248201e1707a10f154601d201c2c1544404503a04041c440c441600e5010401458540142095940020511440010820034880d850110784a0540740006525188035201002e030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 139435989 1250 139434739 139434781
    0x15040b0301020c100e03190309120e01021c050c100b0a06080c070f0c0e090a030815060f0d1b0305070923010c020112060603050f09010c021b01031b0206 67
    0x10040c800c0b0300d1204800031340e14902100d201c002080741500714805900d140151405c00759554130100140c0c6034590941c3c010102c0c00c1c022040100800040802a0348107410348400c0c9005038050a02d00c80712623061490140e4645140c5091407400514102c613920b00403000d50b600e90120b5035201c64030301a1429641000013000c180c01c1c08031a81c58291071504d40340c001c102000d00010b4101c9060010482d0111412010349810708880156007441103030160b40e09906c0f0421030100e08003001041c505070a1480e44d40e1801c80c014140f920b0100485641c48080c1c00c659100c69045031104194101c03000749503c1c04000d042903550000f150301c1c2c6000700608500b481c2d8040e400c202140c144807070903d079040840390561002824407858003d11480100c1d220094120f200401502d00400132814039455040302e03009541614034500030740c54a50105088582040321a400359000554203842d250311401c0030120f03150305040010f1850310401144000d06800903010005800003c02c1013403240d14405013000c445 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 139437239 1250 139435989 139435991
    0x507080f070509150f0405130203060106030e030706090c030c060527010e060c0a0204050a0e010f0e0c15040f26150606280801031a040506040f051515040b0301 70
    0x103841e2078045461110084c000035000101020742d0071071600e07820b051003103014014004100501d4880d00c0c3c20800b100048040340319014801c00003610718801d0140322642e01080018602d810b00b159181c10061034444804c482c8030240110020110300450b01040080c1a01d03262540c1d600100807816001040c0f80d0100001000005034192159078408403d8407058800d4a207150303500c14840c0070070315000041d60002e40c410b00340410850102d90782e400888107900980005e00c00c0425074101d1800303554144801c01c2c26984a041c184240d45030440c0269541c02c80310b03039010724164480a49203c54480750b04030507100c150558400e2a051045504a01c2e00388082c000b804041012014a85560341e0151545100d240c003c104698011041c3c2e1044d00c041d0302c590354152924032442406001d6000910090b900a030303050140c200d000c0c0002e02c04620903540a0301500165585558030900d04c2c030000000c2d03032640306410440c01c04202c3d00000da4010105194100c40700c80c0c00c0381c00c003c01e81e00c00c10b503018045d07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 139438489 1250 139437239 139437253
    0x1060809191109070203040503070503061905180d0f080c070b04170c0102070b010501030b06040b070807110d03031b051c0509030702060f070c09090b0721090507080f 73
    0x10303540411802400ca0894092503809811418540c406a2407000e00da984110704205204126800000520442d041034013a103456603555403c1544035141110301484010100701f541500c8100c0d41c2c0402da112514800c001a40300000d2070145c43c2401c40c00a500114440110301c110468101c800785601c40c48001c1c890b482d10009546c2c0303034a0800e003e0002855101001e4074400c0c5110f01d0310a42e07800313000314402152070f82d10500700461041428400c0341c0c0824501503c051080c1030910441303042e5510080c520f46030401c95503c0c00081d522440c170035100c030f40c04d40d1404001541c581c1082c0c5d400600940d408600302c00401c02403481c04e6407820180d0b09216040060300c181c2d00e80301d0242c40d070125414100213069518800142c1c114450300400130b500210000301160b01e40d128502038681035000344542282e640c2c035665200f0807203030641340c09019020101c0c0020034042c4200b805c0440c0e031001c18017001402c5200703865801521600c103400c46441d00706e8101030002000c00c211141c00d0040720002000300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 139439739 1250 139438489 139438501
    0x106180509010b1207020f0a08270d0323190305012102090c041502030409060902040f05060310090204140f030d1e2705040b01030e0d0509040e031908010608 69
    0x43c42c0300309000b1004103030111000490309802481803100400800099800da1103162900340507a40c40a1040d04e4400b10b803040300403129129150440310607030b01030110745065045032000e0341c60f0704404c80c0f00360380c224a00941c207083c80101c4010388802c41e000501d00f40094001040981680d130b058110003400100403580b8807811007020224040d40c1e07010b50720400c081e154a881c6502900c91a00100c2c014030400c0f01035009a98000003c204540c245401000341d9602c8031000e10030317480303244550180303010f4a00043c0302c01e10340100219001201407140144446d541c0130801e069070070035808a562104241d10110041c10046401140b2200c1180903040e03500041001034510b00300c100d14220b00311440181d20034070318011201817158810034107048030507000070001d0403058a00c900855001c0c60500c1c0d00202d055000c0d000c0c100030540008041c00c001c03103003024115203940054142c1a03000380c9500180e60034503414002441c02e078210203104100300c030080d0409400814103a00c01c00c1084420702c00c00203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 139440989 1250 139439739 139439759
    0xc05060f0d0c391a04050f0a150b0303090a17010c090506040605070318150f051306080712060b03180703031706060c0115050a0603060e1b0c0303010618050901 70
    0x10300356600c1084036403c8103c1d5125503075140942040200803850040d03440c001e500441519602c1144510121035032011004440d649a01740c002c402483c0c0550300f000818044100e42140254000180840341460f40c17000c0041e10340e94465011045c904950280901d0046003801580c100401c5801c10706011840d02000c500703584034600c544d104000003c103004040502c9806156948005900507401840d1614800c2600744081500100411805000413040c24001c07001d440024071461002e14110f8030b000002c1d910940018018001c00003140304548000c245442034901401c410318426031603103840303002c6209104400e804402d031540010f8003000000c0d1304c0402c540312040030502101c0340c1d03140e40c000714806005110b04804554205030f401d040040000d56454100c3d1400c40710303403000e156207030416822150240200400e011254001655040c50005089280c02c082c42e001c500c1d0000741d02d6031504540081c1c00440001e00b4640d2a0452a80d002c0c0102010f0181200d0f03403020340d498400440c1e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 139442239 1250 139440989 139441037
    0x519020a0e0402030403260a0506040509030922110d050c0702031908070c08030d05150a050d050703050d0f0306050102070609090510030606141207050312070c05060f0d0c 75
    0x1920498000002804061003001d80d184814240344d5261258072034411f1550042600303e804c50a00391134100020103614140c0207007405192004051407610200c20107010070199032180d464281c042c00c10020080c03422500c1001d0306440d86401454480f115003007140b054440260010302070704010b01280016039404260800c1041b811000301540d107a4501d4004614044c00101410302c1015880000305020040010200078241c400c0810a96640e6903850380d00d03400010055400408018040c445800d080c0c50501919000301d044a4400d0fa0729030b542458220360003501800584940c0889007103036003502072a005004240045c1280f181070031802030a12a103441081040361320703070001c5000700e400d20103e040950707003000c401d01c80561030382c54945594900c40ca41600941c00e11003491200b043c04507040c01a41c0005000e0701d58408140c54000c44e5410a1106486440d4490b0380080c45d6a1100d0061070f85207039440c01180c903215190001e1040701c0780d1b44400e070140060f8a80b0480d005105130408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 139443489 1250 139442239 139442267
    0x30215071a09070801181511160201030b040912120e031c02120106020105100b1c0c051b0a060c0e0f01050c010f060f030611120f060d0203030d0519020a 67
    0x251100d0360301d00c0b4802d403803d02584e0007800c0039440e2408144550799500c2c40c1010250084030f503c1c4482e10b0148081046501c0c441004031115420302c81840030064040110034010300501d004216483c0c0000000c080fa80d1303981f4125a0741c0d000c44001d910135078000a0703220400000800401c854030b84083d00589a1107101c4040c048070b1000070480e584007035141d06480a00100035143c0c0c2540d03840e03000103402401d0070f407a600003480d11080c0c0050415111000c0303510000320304000b011442d2941059001a081003201d100c103005041c8010062030749442484c200d5103800c2da005042c520601d0612508030341180300340c2801c005108070040310b80c0d203401e688880064028644242c0e503030b0b1903d1006006240c41c00412080a0424000150304844001c203003040c0c0740185c90801440107c0d0344091454440c041641c8070009810b0006004106180c8038954019400f61243c2c8410710b05500203404e540c020302075003108a030780381d0600c20292504000c9019503442c0c04002c524140103080c000c0e289403811000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 139444739 1250 139443489 139443533
    0x19030c030c020a031a0a15080c100c0506150108070e01080414030c010f0603230a08090a050a0914010806010501051614072402030a090b0a030603020907050403021507 73
    0x80c000c54481c02d5443e401590840b600700c3c02c20b10b80c00240700d4020b6060350150031081c20481c0046031814820502c0e000c80b0341c0c1c44018140442140c080c0051064440400c209204070360140b203004c16818843c1602ca6400c1c13044043c3d103196810005020804003424900410034840260703a21660018601504207420886404001d0002e0680500d544540400c031480c0c0d5081c20001c0a2801540c0c10070f4060364400c0760506c00c2c1c0007041c110403141c01c0c1031101401c86588410600004260300d48000c0c0140b00010301409542c1e9118070201d01541c0b851b0b8002c05001340c0c1c552a40030b01210f0130032131501401d29a0082d154a502d4000020891302981000c59030100a001c10102044408030043ca06e2070f14a00544440c1580ca140d85a5141200b004880c8000440441c940c4240d00c040103d03a1001210713103510802a040440c90201c90300a0329008040c10b035a803802001507551540302c10f101b00e000d41ea600c2d95681c210320510408801d0300802560600050003a100010000c11070351510f4080c143c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 139445989 1250 139444739 139444757
    0x30216030c051c090302150a080f0709030206070c180510090c1206030f0b010807081207140a11030c0402070206071101140d0c1b0302070b0a090509090f19030c03 71
    0x200a400c1420301e11070843d140c414458000c0074903411001c01001c0302e00846901103e440c1c3c2d04080c5843d88103612901001503c05c0000401c0c41040c40500d80c4c20a0840c07a2a8203425140d038086031199010f45426110645054402c226007a5044500c81403500c40b080240500e050075811345040801901501c480d040d10b4900540e10300c1c0c03040c03001c0d450100c41058240a03a0344d503400c21401702c11804030f040c3c582d4005800086951000001c04104a8440310300900d017401d40c001c00078501c0c0c2c010f00000c0301c001014220300e103d003040400550301c40c0d17402080b11190b0304200000b00751400040032000c1e40118014845500035a43d050203449040f504103d02a9000035101e00480d501d4501400701c1800c4d02012030296840340c90b40e03109080b0b0380c0340340c0c4455001d01d10f2412080e404ae0641c980040040e0b201c0281400540c82290150241a05500b401030409807034400007140003400300d03000d000e9584613a40c030708030345082000740a104405d82100c0d0114461941c03401400380744e1081d40581841501c00e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 139447239 1250 139445989 139445993
    0x5150306190902090c37051303050303070806030d0f12020310050a0e0403030b0108010e24040216110901050607140703080304060507030606210b0d06090f060c030216030c 75
    0x14005090340d035030040001c503451070700341c40314172881d00130304020350041c030f041500c0c565032a0312040c1e8865840540c21079045010081c10b400c403042c1e071001da804d402c00d1400050020000fa001c1000d035026803032648410b041e500e8980e0074140703400448010103081040c41070280f242d441d080f501003134180c400300002690340d5490f0045e03d0041d0390a0ba112607017151411500003a0902c100540a00561180d5800d20200392071000458102a080c0504807052038134001150200c407a80e06010958511096600140c40d9010002030413a0004118125a0114001c1c0c880400160304143c803200c00e0100d43c9408194104000b00c0e031540141040100a2142807419024004040001500656002a000341c2e6841d00e840c003e030291200743c1e80d060209051040100c0c2c03030750007003045004400240c00c00030040d080801218001c4c0184d124283c0d04070294000134004206540211b14100303000340441c2c0009140c902d000300c1200d2160f5041c01c209071040c4411002c0d4603803018210314141e0189024442c58180b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 139448489 1250 139447239 139447241
    0x80c04050d080307080a0506090c090a030c1202090c120106120204030b040602040302030f0705060904090f0b0702010203041208090c060c0c220c080907031407030602030a0b040515030619 82
    0x5a04031039070103032129100000300640d060055224201540d540b407911303220101180280d42c0103980a951128040001803200c0601c84090710114000800300c0840307035540c6d02d803d040d0307024a4010700510a09400500d055003044404103402040382c0303810074a800c01140e00310200d04010b003e030000300440900220440b40c03490f01a600610780000662546081c01e1401703100070b42c010301c030407400390080d20310b802c190600228107901107400180c40146000700c010202700050641843c101c40080b4052800c0001c62042441e41c0d218014603000140e0381c0c1404c0c2800741540c40c00301d817801c08004c1050204010100e004c40e4510190b0010340744251120400e40e4000d090081e21840990080d400d031030707289204000c18010142000e00e00c8010042d40c00302050480d50380c0c20458035038600394080720040001401c1c03050721740151611241901e404546070360b10071084c2d85c01942e0b0b030596a40c440d81180301c1d0b03150611038103401070642520000c1c25020300000c60b844642c001c140310700c422407454200c102081e40b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 139449739 1250 139448489 139448497
    0x10f030809031e0c0a05100c03051303050619050916150e130606090803040f12050f0a06140606070f0b1b07060905060c1608090402070602041401080603031801080c 72
    0x1d910b410440c01200540c10713590101c0001030b030320440c0d180b2400a824100041400c02c80066540d60380010f0020341c5007136499a211540e990140c0504400000110700f0901c01c1c1801502e801c0ea44180f07052801901c0800ea0b003000d05005080d401c501c008448515a514050049070f9400300221503041c3c1d040303010741da2a400060b14503048018800c0d6002c0121041d409078040e201242c9900c00e0481c3c880e21055a240140e000390707252441c001000340040000100c1e0000000c1c0703e00201c41040c1e025809550604040690846059859203a43c25000100e4a4400d612a6003980d0160070241e03a40c940c40d650180d9904040e00100103070000c03e01015411505e15000c1241c510410354031324061801600a1041c200e050310b05000d08000301d800049074100301c400409400e41c0007941241702e501c2d552550b5000d04c0391190300540c20001100000d81d180086c2004003603e083d503102004000c0c0015011220007032169120b034004001c030503400141d00c01e04a605040a185ca10001d54500404103002e00c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 139450989 1250 139449739 139449763
    0x1060c050712080d0e070f0b0d0e1e120703050a0503040f0b010b071106090f01080901061a09040f0e1b150f0c070b0a120513061103010503010c0206010f03080903 71
    0x11580c2c0c40c0e0007440005001407590040c040d504020381507030310501d1a02c40806000e41d52141d400c194040000001140c00751000020440000034002c0b0030641d420301e0308500940704040010300128840f18007500384001d000201c0380c404070501d0302d0304940e0300610030700c60301c02c07603a040c0580440420300b0b00c40c0d22043c2140040d0301844101c21940c55269074400340c0c1001108030740544100300a000f05081400584071880740140c0081c50141d03880c3d006580341e0500800144107503580e19000a00111502440451048000002c555840c107500520003038603031400c000c02405023070000600c1c1f1030400040c0c50b000c400405481c0c4628a00d070340001212030340b04510400700010041844000341c4158001808402c8404040b504116511400e1a100380160501440442e01c400c82900d8000650340200da445140c6d100c002031400440d645910450b41d175039a2000020342c0110051207281800d1080000001c02070000f0a07456162942c00013681c0100c0c00010300416002c114035590b80c40420088044007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 139452239 1250 139450989 139451009
    0x70e130213090512032703030a0509030d0c0302120f040c05120109021305160207060c032f0c01020705040b061905090a0816060807051b120705030909100e01060c0507 73
    0x1100400c510203c0e03002030b206d040c1502c160310359580703240c4645a0b12049030006803002c2e5046903a1030201a00502009107000b400303000400804034180e11500c10250561400d480040e02c07060700c0e419913001c0d02c00051401804003132950510000c40c0700e16000c40221281200c0404440101040c0b5074094001d00b00000d40100a06140c540e84051a4008030b1140c01c00400c001078440022104030713604c0ca11440348a012556501420300468030503840c2c100488804103251400c40040c0b04000c90385030204201003080c0c1c01455031180190f0381032121000070f220842d010300c401503462001130254403c1186a0110002a101d159501409042906c207007142c007c1082c0046640c03030766403580301c2200865190644540c0b22008c03409602a1403102d019036070b50b40c2e409080c01c2000c0790028203034046075003050241c820343c94420924225000100305580c41940999110b45c03c0f542400503400000e00f07108014800c1690500c100c24807171a0481c116452071400000308822070074a90304102080d04008510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 139453489 1250 139452239 139452253
    0xa0c020a0609080d140402032b030c0c08030109020a27090b0a0506210705070f02040c1403010b0909011403030702011202040f090501170a05061501030e1c02070e1302130905 76
    0x501e04054000c2c6c441c40c025403c1e503800c007254138803003610f00e1420301d5032034140c40010b443c0042d050701c07039480800703c555242021441c130002c2d601d40344000d1304240c4c498900c20340c0005902d40c0c1e01c0c0d449015091070003c0100480c11288a01110303002066240c09048030a654852000d00950368403245040141805441160b461814040d490002d041e0234414103a081c00002c042080c0750f22410803a081107030000983c000e58411070b0b0800010740b444103106010841040324040c01c2000c0600294028104480080e6a542d182024482c0700d035016404031000000383c40720744180f07490100882e040e4903030900c1e112140034a000e40042c000d0089401c20041e0040540020518440a0f071005060780c00e85443c20192015009840342c0e2a60649002015504210046169984403260200c5075490504022585d140440c2e40c55203402c01680001c1800742d2050740898a59405209002c054a000c2800c175100d07141140d442d000c00121480d000b070045d4a41c918000d0b0480b003e91041c107046a00c0f0041d6104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 139454739 1250 139453489 139453511
    0x15020124061103120c090d05010f0516090e01150507050d030903090e0907090f0b030312040b06061e030402060c061005011d03070909050c120706080a0c020a0609080d 73
    0x3a0200600504012425118200460b80c00000954118030440e80c43c11086690300c68039086190004050150405100010700e4001a0203004a107003c000301c0a00092914100c4000035600618403089820301080003414441c2122184540703043d0f0b41030b0500040b0b00d01c0351a004454500c100000130b041030007081003a40c080d541c1030b0030000b0a81d0085e6100450203449454010350ba100c155900d10047c0e00030740c4104044280f0790007001207184500c1c40006c4000f004d001180c1950f101082188c0505060801c010800581060b01c5070402400da44581c10603403411001000d0003910880100384087c0800080c08642d5281c0407140480c8600702600c00310304028051204032003c40c05440d01003045250010714007107105200e02d500301001001002641d140c030700c03c04010101c62001b542d2a004224465805483c2c500041905201c0000200344445c81c3c40c400400c8860041c22080c000c0d070620888050041d8001101810b454000b0000945d5244505d001c400034441d5030171b040100341c104a810b01c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 139455989 1250 139454739 139454801
    0x90d150c030501090204060e090c1b10060603110301030318150806010305400c060c14073b010602011e050f01030311030405031005090d0c0309150201 66
    0x800c6206074800b401a41d0b29001c3c0071060b4019802000005800b064002c202442d00449160304806103030102e500c0d040700c3d85030388202e882003917480401d5684580f40001100c0003d2281710b00510492500b0020401007a045e401a448180300280c104203001c8a881d031150084e03025030005000e2401c4407000c000c40c40f1302c0076000050803201d080c00b1034034290004900800c0031220100380320f92260105050060540074a041000c0401c05894100003042a200090307000000340000c0c0000d0b444201d11452a86042400700502d034031202e44982104c542008040f1000c0920740442554668032100d00140c10b06810311036901991691207079441400000f07102c1d0b0190b1000407181d00411400003003c6d06900080e065460585080c810054220010804030384202140000d0003540400d41e4a805d90340c00c0044c0c40c101c10000c61000c92592a4241302c9100010080704140030709901346440000c1d0181c038081c00042161013102c0c10851440501031680e40300394070624100c615041d40c0300c402162858080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 139457239 1250 139455989 139456001
    0x8160303020616020303160e04020a0302131a0f070303020c0d09080d050c060a02030c0f07120e040e0601140102070504090b0601030e030f0406030c030b040c0c0c05100212090d15 78
    0x5030240c00b401002c5100c20004550200c0d001c03016400840c6035850b1005110090403050002404000e044c03102c0059541c2c4500050070102d080d568090380b6071403450005144a041544078000480041468003a110303601800c1d0345c80e40201400d20f503207940703050400b50064071980124070010301420030181002d942141403202a2140e04040b40c0803020005001c0e2014070441d6901600303503000d50001110001e086e0000c5600c0000c400c070450910742c0c481a110f24513042039600719400922040140140d80d402400a401c9040840301400940d0038403a0040c0c07104410b004d0202c038014a00c06588543c0d001304400e000401d0041c0c0b04101802490800343c2480100780c80090001e0300744200154040c47c008182c885d02d0202801c5107140c64508a8241c00600306400140e080c0b685540030180c103542d17180b052403080459521490705410071440c19039841141c5401c07007840b40e0084024580c00d01e038009041d00304410190307500317651104d084000501ea0595a04000d14141160700302186e441c08130b800038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 139458489 1250 139457239 139457243
    0x61602120105100b0a0203030a0506030c060408060a1128200109020f010302040e1306230402010201060b0301080309060c0309031c0207050103090b0412032406120c0813030207081603 80
    0x40070f0190b220038682d80a44240c0c00e55000682c8284003082c0315900366404940c000d50f0080032500308030980804503036160015880480f140e00141d080055004c000d0007000214064510b005d8542140c0019030120b07441c420140440f103c0442c245208200d016068405000e08890b03d02220340004c030740c40c80e0203003220a4080380256032525080880b5402402900c0941d46041c0b80d000309940c1d0340058840948146009a5040d5260014050082008844e5000303200c68641140c085113058000607094480d06d074809844042c00304010400c5c1400030041d61018042103415958072030000183c103245002d06030b400c60b85030041c0004c840c40d4000c04900e40000182d16000d40300320b00e50380c00045d012107440040c0035002559200c00140020800d40018503400d03101d00340080c00584510000c1d10101d07081c20843d22489407400c0038494160060740000c000c0741c81c25412300c400b68001700010b000381009454114205089001c9004040c024454003000d00342010441c1d00005a506070706040c440a0700c42 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 139459739 1250 139458489 139458511
    0x30405010306410607030306080609070b0409020703020307050d0906121b11030d050702060118022703030706020a0903060b011b020f030109080c0706110a0c0302061602120105 77
    0x74441824841801c216120f20000d0750020000030f9040052480010041d00c1440c00c40b90014020354a00d805000142e001c0d540005070706d410140c169103025005803a441e4640d01192081049160840484099640c0d2080251700d8168514040c0e03d07600484030018814041c05181c0c5201d1a40103001c41c044400c0f560350181820f03030015900c1c048440c80c281c0324603031121103100d09100303900614002000c0035041c02220719020340f11141e00e044400560390311b00181c10070401001500740300c2c0c0e00000030841401045240842d071604480c040318080510361030001c54203080c0001c696061065039001c54100b01c0c00d540d40e030a5081c2c01003101c3e9171030000300e650615101c05410745503c81d031680c551641441085000c009115000c101360742d107021070a10750542d228213581c0300140042d40070b400d020951500500304c0c2070600c100507203112440304060b0001c1c0d103c00320301e00c0403460408201048a406a810907503804000c0700060342e6491480303000e9000701e020340c20481c1030401540315502c5480c030814 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 139460989 1250 139459739 139459751
    0x120305070f05070201030209060708130e090f4c150506030609090106080a030e040e0c0d0303020a0302131401020609060c2a0d1d09060d0303051b0c0304050103 70
    0x12054031010034100400d07000070410310450340154020390081c00740e240010102d505041c01c80d03650320010b521a600d8035050300b803d003004104004581c82003030340048000000d032a0703548590303100c03c2e1759520307212400ca124034142207400e031202d00b014001c0c0860156400140d104400e5504070764500e0811152903011940b6069000c02c001d0325504644095400061446141d80c07900d508000c450340001c0c148444a542c0c0d0a00000c45101c20000d9029282c400d0319008a59805c00c0104012215005101d20300c0c1d812000070301003a55103d41c41208103079850300b00141c844a06880460007805141207080e240d454000780401d0748030400448000c610026404c56a1580c0d50203c40760316070340291004810041c05000c0e904000e04440c2c01c1c1071280a600e6965075403000c9510a041c50070700c901030312001040202040304000440360039003000c40c981c150b800c000c041c1080c00115240d400d901401908050766540859601280e203080011403041201c0b01c1c648502d41e1441454880c3d22500c500b0b80402c2c5015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 139462239 1250 139460989 139461001
    0x60d0606020d090f1505030702011d0705040b040b010207050607030504080d05091908070b070204150905060901060e03060412030902090a020a0e04090210180e0c0301030c0803030906062b120305 85
    0x92441041d521040d400f11745603030300e5610035030742a080a050a415035494244000352400890a82e4001030400c100a26001d4902020b200443d0400700246020300d082c03800c01c5030f06980005088080344d9050380e4142d907440301414100c03458050740d0810159409625020405c5591050103001c900c03108440c1180103846103040f00c0d001c141d06104a01c0c0d150400d020400030f8000020182100c54005040405c034803205114020b8801e405812200416075158103100d141c0c1048000c2d180940031703500b00240b00c3c40e4084000784ea030341c00048c4001d220800d0b5424000c0c000b4030a0304003c1190f94003130601d6455092502c00c0304041d4010900000000e0442002c1807500e2409014405049401600c00074121842c0c0c003089032a41c800c20750284250030030060000f04810800369070307849841d2684076203880e541549418110060b00303511150555100340240150802e01051361600f00000316a009107111600502da048150141d0340c40301039002c40f250384000d20083c1440c100c0324400c0e5a404118075aa02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 139463489 1250 139462239 139462259
    0x302120316030e01021501080330060402030a181112010c1b030e0a060201060302030d030501060e040b031c02070305010506010c0804090209060409090501020a02012007020906060d0606020d09 84
    0x22078000203400c0e1855603008240503079042d0a92000c1031042d81e00a11951141c860381c20401e910030141d5500008442d0b0310400446410740c460f0070559080346c8101486481c4400c0c03200e002d01190300c61580000400e681e441035134804c104928032808540c4600200e0300f46040039041c940101170284408843d4590020010300c107200c81040d0544500c0c43d5213040241e4841c42c5114182c1c02c4081c08803100c4118441e694501801c002031603554008034120b400c520505082c161503220708400e06080c540113010071900006c50104413101070710000f41c00c5803001d00013881c00c503203948107800800e604050052903030b41c00720781a0282c82c021002406562209001100d00c030031204406480c0780c0f0f0900c010b10644009400170890040024402d81c180380d19158a04203c070504002190b05030f5001a01400b5150203000d20b1110b10310201d501103044a2000c060195403085200080c414080030001403040c0d0b5450f0306803000d1000c451020008031307440e040d000e5540c44683e07420101050404200190507808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 139464739 1250 139463489 139463497
    0x405060709170d03020c03040801151712030601031a040617010e030304031704140d0507030e0a0308040b1c15031a090706140c0609101a0f010c030c080d0603021203 72
    0x500700289005140f0541c1103000b5089440e0f40d80080c001000005501c4109001d0038000b5260b40801c41100c0e8608048520701c004141d0155030741e5041805941d860b540c4601c2078a034028000e09020803c0f0305041d0070804d0500340070001c01d60061030031001003070b40380d00400c15103040385a2030000c03c407803451049040d0362404102c4004001403860540705c420b048401101d290018070032038080090000c5165003900b42800390402c1000208042a26018594000404103840340180c40b2425402d0558568480900c031364040c02110340d00005a400f20f09103441080b02d200c1e10444010080781c100d18001459464492006617203188a21005004044404901d180200040d2008000b400e2820300c0c156001700228800c59a4000c0a06c0581c05a50050107042d2046030264050004201801c82d45821901e02483e002e1428103e401440010380307504005914400d8242488280c8450605d81100c0000810710000c03c0048041001d00072064150000300c1030b00d208846400c0c1c4e940c410000300c0e030749000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 139465989 1250 139464739 139464779
    0x12050910030b0d1b080d0503070801060f020604081305060705010204080d05181c02030a11030601080d05040b13030f050c01020c040b030a020d030e041401080c1f05160204050405060709 81
    0x50f101c0030240002e03a08204d10007500d0070002140c5034540d5800800e81421150f01c40040401d4000040003400350303020501c0d5001d0455400c024208048141d0001d56540008000405445000905104400240d44e0610041c40700502c0d8581d12039440c42d101d800307908507100d02c02d103e205080d1030040742030007642030b240c100180c2c0180321100799101c410420010310a1041c0d400f45142c0422140140c0c07024031500c203005004012121840040c8800d00d0303d0703e201681b0820054000d03051607120940e000003110102e41003042007503100ea203442c01072441c5002591004180581c60303610042001f07800f06060002c460240c00b603c039039060010501c410f640c11201c20550580003101da105c010b01e040641003941a0191a00040e200641000305089407105109a41c110381d015004202d00442081001d03886901520032405001004000d55031400305c0704880018440f000c10708020141c3d29400c1c40302c1e100d030001c0c0244050305090402c1901c409050351280001200c0110120b8000c0d0142a49506c4030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 139467239 1250 139465989 139465999
    0x28060e01081315050103030302130504020f090f0a0b040f0807050108040c170a020a1706060d0b0624070b2a0901051308010f06180e0703030e0d12050910030b 69
    0x591101e600b810424a140c100b2207581040c10499030f5154003d1051034003079403003a01c2c0180d5400421041c540d50000b181d001c00e00c07880c010809911a00070400c00c0d00c00c7c0c0740064036241e100351200400190102c2007a04401821000491b001441500080b418030445100d1802c1d550b0160300d0324011658050304a0340580306128800e4100034543c4000c001c0140c0d5103031102500c40e41c80c003650019001c400d055024042c40c041104042504880c184601c640007001121030400c040415030742c200c86100002c203814801c10113000d20302600300c503210300c0201011008a0b0700707070b8030081483c2c01c0400c60300640c1c10308084805450791100310403001c440d10349840c95402010b41000a0744004443c7ca070320606030825107803a110380c000340b2003009000d4810610180080483d2590424408420420600b81c59566103400c1507458031446001003402c006590b0549009032407003080201149100005040080480c4100381806081d2540040a01814070080301d408030180f1101800310103071480e40b003880c1da100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 139468489 1250 139467239 139467241
    0x5010207060f050c010603030f140702150a1b06050f0c0a09090f020c1603030e09100306050c0c0d09030201110a0b06090901060302061c05220b090c28060e0108 70
    0x2030b8011210042a00382510f001c620380603460f00c0e0b2900b5100d0b194401c9000c1540589141c1d1550740000b2341c00200c900f6440c8031418856207400040c020108612001c278400d50001d51680c40c0b512800201c01c01c40704114520700c40b00c0d001e14201d03006000450b01249007004010119141002c081c08071b8046c80d0300c55407165603a504184452009210340d49442103c03607420405103c0e40e1340709100550024500d20f07104000e83d8a1801e01800d500b41c218a124402d02c405001c01602c40c03400380c1e810054a40020300003640da6954500a4500e01c1b80e0390141000e8403802d01c403020307100e42c40000c80055910070f90317030f500c01c00c1d2120b20410381e9031245100007805101690001829400c0c60131207943d001d032059002081c40c07641c035004030309654442900d49016840030b03240041c00b01a64002d01f45c108201d00b41c2780c0c0c40e011104880218003100c001006040821f80700204507014070402070954006401891401202d00f51081604010081a081c150200c0c403400c00260a60295421009800042e1070701281 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 139469739 1250 139468489 139468499
    0x903060c140715150b030906090706170603011107060203060a050906031504050c090c0c06010f12120e03032d0a0c1e05030f07200102120f040503100b12010605010207 73
    0x30316401c1c02c000d004251341303000ba080124400c64120740280640c0c4d83e03042e6281080040a81413401c000c0280c075003640102e604000082e0700c419144180d0f006002400c115440e14000203024044002e002c80080a0210301e10040c400c0c0b0303078000e40c00b45800f200ea1071452a56401801030348042111100c3d45070b0003c00c2160101862181000e601610910035104a6911040041d6250a05840e00805280301041c0d540b0400c5c03040104030701400142300d03c10226450450768503242c1d03d000c42c0085c5a4580f850b40d64132594050b032695090400010183ca444500e90780c040340c9400d4079046045440f2800000800601f90148226114401035684d0103e41070000c2e12200c812000351241d10170010110800c16002c618140040c1003040300c1d40050b25507512450420328009014005110162804400045000e80e00022030008240340007542507103030030f0940b520724042e002da07500c110381501404100c10b4889000d0391081c0d41c1d001040703d1032100740241200003400c80310607000e0a07000da13010f00c01c103101c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 139470989 1250 139469739 139469753
    0xa12060b1603050c03070302070807060c0c0311061908060102010c0e0d0b0403050f04030506040b06120c0108070c020406080106031a100902300103020a0902121302011704030903060c1407 82
    0x1ca81c50090a0040c5002d84030a10306240d540a544150016000000c00303121580c070902800004040a282071841e2800c1900c501c41c440d0700900c802041140000e11504441e290b48042d5956000300c0031740321a5450081e400941040c10840d2030134019442c210307210b8440c50103013040e1008040f001e00803114984840ea1960f500c85400740050301800000e016140c4024003480c014000b0318072a101400c1d060400e49800101a94041e00c090300c1000171005001c641400012036070740ca21024a002c01c0b00e6110a90241c425150800010350001d06199020811090540050b01160312449400c0c0070713255190300320110b00e00240c601c040482541c4070100b000c00c2c280d4015200040301450a0000010308400d016850010500d1500c001d8410788010025440e00b901e404005000c201001c0d4500704051090721a469002840c1d480c0c0380300118400020369101d16004014000c000e41c111415060a0030b000d04020160304c0111002424a03054034445442000f0500150754102e005504101c015a250f00e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 139472239 1250 139470989 139471027
    0x90302090606130f03031b02010e010c0c050a0807050f100c06110f04080a0201030f02040510120204031a01150318140c03060a0c0207171c03110a050a12060b 69
    0x6030301c41030501441115181c3c401c0d12400030100c42190707038401031075403901411081000100c12200519a05e00c100547d8010344420001e83d07092804a080c8249460400b1b0480120382100b03800000c1100e001c60500d40001c1c844003918411501c0304002c4602c001003244948071101110001443d84c18494001b4020350001c84c81082c00d19001418800c10540c6000e960b0410351006506a21141030384081d541c240c0700b02c043c4045600c4042d0b2420342040c01103594012185051030801c1803080c01640040050760688014640c00741c044a922160741591b114051000e006110b28154990030503180180a8480c0e13085401c59038604180c440d0f9246c40c0c065210f1072044900c6243e010b03003110f1342c60640e81400307454810051034070000b6a5092040c0300030318008440d0000d0600c0c11003001c5e0200c080c4000102680c0c500000281024403500d9620220080c1c40083e10b010800c04005c10300360303201034101003e0003d000190340c4220a403180d040680d01540e2192142c1489414208040014044510082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 139473489 1250 139472239 139472251
    0x10b03011a0a091a0901170412050f0913091b080d05090301021c05150306040206040306020307171003120f09170a0f06020301080601060f050919030f03030c080a0c09030209 76
    0x3203d800c0395503078500c0030010340300d400f062881d84000030358402568000320203441056103030582980f03524040c2e86041e81d203e81c010303003901400000300e0700710a030701c445108941e03403d00058044581c080c440d2032400003920351200d045508001200140f82070304099454041140d1003040109119841c600c0250f4050b4003560f51540c0554081040341c03303081041b03008182c98200300c100010582fa00091100000d0702004200b4030a41140f01800050303682c00c02600c094a4004e00700680d80e0b110414207440317541030a04156003000e104c50811601036604488201182d0140b8900c80d00100300308000c403200d0303881110080200342032010034004071204a100c442a61010003c60314829456100e011420303a50070300845503d43c001006000c200720070310541b80180101d00b4800040f505045d0081d00074050f14048500825081101c40746c031910301281e1500a5402c00801c66802e442802c005001e441c50520400104260341e01151030b64480348203250000794195039802000b0300b954200540042c000d041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 139474739 1250 139473489 139473497
    0x10c1103090f0f0301090302250b031f05030f0f060c0702010f0804020a180203060a05030c011205090c0904110f0109080a0602030901020c0105010f0602010b0a230102012004080105010b03011a0a 85
    0xf210500b0b840921035800c4c460300980050491024005000d8030f01841d05541c3c03042c2c01c0d800b20081088103c4102542d8101c0e4484c014051107503c40c4002ca14000030b141e02540e0b00d44500540c0c0c00c1000c40104840080485000035113000f5940c100b02541548140c2034000d0001720160086c20314144540c410642040c401025070496540d230300c0303841e003da20012605501c010b60001c2841050300d030980300d910085c5401d40c00303030002c0480c120000e0501d80c9a501c158000326100c00010b000c0b00740c1030080484000c00113200c0585400c00d42050241b0b005c0d2410554094500c2c034620406942c002c24503d400c407030b580c4008220200b61645e6007400794002910701004d41d0340a122032550400d0a019460203045d804140307404403407030140028252a407404085010342c035107800074045210310300e101d40c1c045100384541d01c1403140c507040103d005224041da0007007040000b540040c215803840000f4012146114024030603640c072640d0441c46d0b888207200700b07080407008035a9034880d013000d04050704203c509424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 139475989 1250 139474739 139474759
    0xf0702210106060e210c09041b0f03020f03070807051215070c0b0c0c0316020607150f06080613030c030918060303090909050c090c09041d010c1103090f 67
    0x5115081d02c99542084003c40da00720301418690400704030040e000031714034910803030b03503440c40c2080ca4503458886c42c090300a00c00000024248500c03024591408102e545407001c8640d40c2d00d200c0f0b0307014241404103d200f10103014500111745000036400c01941d95481c058032085140c04200000d43c2d6070b5109085031801101d0030b0f64550000750085603c12074481e194500503080710300c2c00c04140d050042c5070401300e10003448540034003900002030700c4602e0240c1c0700007001202503000148040c0106500140003607502d0200c20f00c280f210342c01002109420f051f0070310442e40c4400341c8940303445040b1848680103084008a0380481e10a500c0040c0c01c1d4020f0400c00210b80d254031418124000649600e41c4c001d46501041041550182e6990000e0024442c00c0007540a1030782e516444041481c00f16100d50f88100c00b0485c600111070840f40c00c00d400810800207078418041034000364045001d1000c05510b00300c200aa070714040e14010394041341e8440510707d840400c3c1f08200c90f5003800e0301c81c95005900c0103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 139477239 1250 139475989 139476049
    0xb010b090d050712061b0207141219030f0201020c0a06020d02040b030106051215010f200a050c0901140919061701050609150a06081b040308030118020f0702 69
    0x2121200192001200d003890340352003405c164068811098408a012040d10781700038190394041211016240040302e1281c0900c07402001449450400c0a42881805210350908040e02068240500184251100d54455810b050141e080b80030f40c650300341e03442d001622042c000402503402003180c0c0c04000c0c00182002e440b100c4407880f82e04240c04c2240420000100c4841c503100d640380580d030000307903c000300440c5410040001d2000000e040000c080c040d5110910f00580d8411a101c82c6030640c00c012683c40340624203001d030751042040462401448203000108100c121030004021428018009419036245e00745074090138a8081d910182d00d544d1ba25002c50b5a4280c4404071681031441030000c01c0d14103042d003c00c407000c5400b81540e91a05586000d440c103d07110075140808407034a60804181c02c0c0d0b10704400d03a91303811807071844c1c0010480010b004001c105081020703505131080350a140364034201d0000c101c022031081818500c45d00c0c2041c0281070040c83c100307003a5060b00c404000f400502034010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 139478489 1250 139477239 139477243
    0x160503040e0f0708091c0813060c050714010b0102060103080a021207060b09070f08070c0f05060c031f060516030203210133030c02120f0301170a0b010b090d05 70
    0x15107002c4664141001071282c001c0d408600e5681001e80b9002900a948920503041c891091401d00b000a2244150004c2d90140e80314444120482e0004024000e4128540004107140d0103034408451700c1100f044030a500520502c00e2240c01c94040e00107140a9007543c8842d6219003102c0c0005085214190303503044501c0a0b64042d140c8980309000100d8000a03c608010600c0c2d002484501000700592090b841e03541e001003440d0700314203c0e04003490165268100b030b9801b00107522002d0110720542c824489415270940c02107224045881c225012841180141d07145082136214420024500f40b00b80d1085105039410a01d400744640101ca00d4031a25290501003600e03c25401000440f40308010840d40030425111800384c843c08850041814943c03060701e84014004064004050395aa00c09050030f000700700351601007040c041c0351500d80c00b0000360441140e000f40950103204110591001500c480004e000c000b03c0d80c0000080401c1e800c0050100c2c980d04000c001aa22401051442c0e010406c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 139479739 1250 139478489 139478491
    0x3010f03020f06190905011403061503090c0d050607030c09080a0803070306090c020a060606090b030a05070207170d020d08010320030c1c0c0e0402031011070c080a050c0301060803160503040e 84
    0x1858450085c958544400900718111582100504000400402003180d41e51f1404080640c4c110141070707165183c1006603890b125611100540021105002c44103002e00010000d05c0b5210f81e99081c059000001c00849441e4485e1090f10100d921084903a0001b0380c4142c003455003c00070780303000111280d403681d0002c165a0b80031100c0d00540c110690b11000d102103801400f001e0a814108014a1854110345101601c030007003902e816285c0e500003055106109020080090401c920440000e000404815440e0050b0885000c0036108040000206900501c0005d04881e00183e4180800c241c02d402e42d4504030051031910344c18050b0050b0380b4581ea4407602500e00280980030350707003d86401d134601461a80c0380342d08407082c880940810000141e800007400e00707540e0000301012800c441105880e0f00349000700c00303000305407840600c0c0100e402d100000c0c0180c01c140c0260100c691142c8101c00f03042c201c524901030000160802c11a2508551200301a420322911542c2241d1400da03450703040710007204c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 139480989 1250 139479739 139479787
    0x510090614040f0203011103220f0f0b0a271b05030f0a061119052104080306010219210504080d0816020c09070305060f040510091103010f03020f06 65
    0xf28071a550404e5050910584000c0d2850030300840c03840c142902d00340301c0d41d9080300008001070310702440c070000c0014400807520002c1d40004210700305080342c9070102c00344070101e8498601c035140c007840c803501d0140012240d111001c4509407040c10034141e1520322500c400129120700f0a51102c0c40040c01d0b441c10000100080b405001402c0303054040d107058801e80d13003001301d030440d070850510540d02004004203a60096141a0820a0352501840074581c0039030f2000c00d084000703168605c03c000501480303100a41c130800302642a079100c1c0048110750350f03040c0700c0410702600d41068103044916200011a410100e044903051843c1840d556045591421280b00b20030800500c00310b0902034070410000d03c0143c3c0801c680080d1144020b840017181e6420380c020103600c01c15407500041640c5455508880d1004880038100384500c0c94503442d071201c1c0c40c0452150170051490100000c065101d28030980703060b01c800900c0000315a02d1a02046042d03c844008182c0c041d9007005103003000407001c07441070340f00c00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 139482239 1250 139480989 139481003
    0xb090d02090a0f060e0105090703050919050d03061e03080c010e010e0304030b010602031c0f0b100207080601060e03070504050402030c03070f050f04020a050d050408040b0d060f080a051009061404 86
    0x581e10f014070f030080c1e0303c1d203a0008560406030001407200365200c00000350301400600d00085c0036566410f03194504000b840500c1e40854400c180b210034050041024854000c203903c0902165a079041a4450382d10307106281e09442c0801c0d4402d0001520317040086c8a068243c08c00807440a03501038601d070031528551001e00007540001402c204201802c0c00140c0103214500185060480d40d01100b07554400008107200d0642c3d480281e0180340758540c0c00840c43d00c5001e4205415100b81c0c0401954601071405002d4161295100010b42144078080000e4941c9010340505042e81c0340c10140400703044080d0007240e041c0210f4020510940381002080010102c0380c0d0500c000c14030705011320200400c214100c1d4000e500400007100110341200840f0008403a4100c00103090380c813030504405900454000090071040003481c90b00c00b910a42121055a081c08a4121026238400c641070b030b2040d42c241e0050080e0440078407904801c00642c084501a40607000100345580c1203880c000010008036002c6580c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 139483489 1250 139482239 139482251
    0x11030f0d1a01050316030902010903080406050a1205060607110d0807080a080714040e0612070f1a04140108070306030605010f14040603110f04060e092103010b040b090d02090a 77
    0x4104031850040000382050f07403550604250285000030940848014142c035070111200f1640318102311070065401081e001d49581c0c45880090241d03116404000010385001c120031308120142c451103004a100034a164948840360f555842d03003070b08014845500115135540c1d500401c2d0142c005200140c42040c41d03554501c0ca403030300a030650601800070b60400c0362621400c40d8080402c01101d054528400d031003003039961410001403071902d12031910344580c0901040040c0340c00700b40d140881580d03500c0d20341841185011140313440c03e00070b0340300301116288071350284140ca502943c03005401c001c5030b2402091091b1a03032039540598401f030f03008180701940f6002c102b0030481e090507080304a01c4101c409010041c50750b00c0c0c0301310590300911800c1c4989060070b40080240d80d19445030000b403c200d01d1800c41403412000050325004201002040203045140d82c8090030940070487c2c0c1a00c400d510000c0c01d2604115a20000b0f8000103400c1da0001c0e010034108000d82d4031050084c0c400d410100307000c120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 139484739 1250 139483489 139483511
    0x10f0b09010b040f0302040506040f1401170a080a0305180f0c09060405040b01090b0f0909011a01080708010e0604020f0c0106030c05060f182710210311030f0d 70
    0x2103220140d1103114000001d100900a044035015804210303074049074089002c1d02c5000000780142100d21844024510f040340041c04071b01d0b0014014101c030041088208080a0665647d4031102c400a0041c0080ca003080b0b2443d6a5007c1e0340130a0300540d40400b11100c0c2c00019210303d00d406110b41d6143d5099200d42c621203410710b401c2840b03d44c0480c2c2640d050082c1d01b0a42d69a054001303042c081c10340c070b0076195010700303540d07032540d400c0890b045000821001c940d007001c0e07a0690092540c141c481002c01511417024002e9405011040c2c094103299032107460907842c000484509440103000303580c0c000c1d02041b000c84000740c81405841c800d10041b00001c0d00c5071542c84c14580f00a07035903022030300071356052107403038156031501c016652202507442d4042c0305003a0f124001540702e4118049030300400445140512138100660400c1e00c01c4190600c1c0b10000d540320300175440d004602c00e110f8284481001b0310540002c0c8103000c01c10503020114116800d002944240081d1a000300d40b1200c00c0903940c00c01c82030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 139485989 1250 139484739 139484749
    0x60501050706050a0b121015061e0311040b030109050109090f060509120f03091b1c111507050c1c1e0b010603090c1208030c0f0c0d03020702030c15090d14010f0b 71
    0x4423242a0440070421545082c2029250845505c04010321300756031441210540d000b41c210070403a441c0150242e9503252181c400200907003007030040e50050b61510002050004143c854140210b40140c5241c0c18490b1950b00d980c0076000003030410b180350007192207155400e4540c401074010b943d10b40181945916100d150349245c5141644040c20054214120010039240d80c8a295424087c1d05100b440c40c99442c00c160780b500071883c0ba25070f041040801409804429000504012441138040c0d17004000c4050030011071440c91500351140c101150440300000b64503940010003888042551fa111100307a46030504517030703826808000403035151f507504020030802c0003004019121040314022440441c1e10340c051a800000c00b0b64200c600002045500280c01c9016900e042c0441c2c1c04403403050f950703a10700401940100354100c0c024820403600c1d82551611607a02c0b11071210210b207550a015a003000c0100006134a5015a90300b5682c4240458000d001c2c010043c5000042201088540005051003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 139487239 1250 139485989 139486001
    0x304081e1506130c05071b050a17060c070f0204060f080d0801030507052b0302010903030b0402270622080f0f0601050409141e010f060501050706050a0b1210 69
    0x19001032078081000103e5a0700181032891852220000802c001e030401d0aa0b400c2c420b0031030180006c07540c8a0108a003100215686003070340c8069513443c040a980300030440100079004003414903038006c00001029004400041c2c000c00c1e001c0d03000304251203210780100701283c10f560000d49108016070700c01e000c1648100300980c405034036482c100002c0d40c51a01c5080c1c41e0741850103590310410401d41c0d04803040c02c0c41254080f410b00f00240810b0107400c2c0d49000390080268160450100781002d2848030603141c07910030b03600d0411510fa02c66800d0b50802003071100411010102a601c4042840305049030744840081c04081c0c60390a0640030504d060019030751400c5c2c52421820016880601c403542050300202e01c0c0b41c11110305884c041a203102e01c0c03600ca0410700c40c40e01c40101600c211512580c40c0200c0c80400140305020000030003440314001c9800e019602da6000d90350214204103d1a00051081d0344000c0c2c0c003213810f81e00020345081c120300080000702c40d9044030015602c501c0d846410030503e4860030f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 139488489 1250 139487239 139487263
    0x60b0901080c061608120109021e040303170403110109050105150301090201320a030b0112020a0203040e060315090312060a1d09070b0f040306060807031110020304081e 74
    0x10015200108000303a000e100301c040c4e280e002c4821030741c1c0780d080003800c506071075010300c0a8981e500c40e036031604a904025008680011500703107541c0d03031384004214044211420340c1d406a0f1207020300a519041c000780d02c107024008800f000303104d030780d081c26200d401e03c23030018142d20840000ca060304000301e49940340e04240303d0f698440d034074002d903036801170f80c10401c076960541c402c100c164a682c640c03400a1202104640400c64030003400240c8032a0076525900102c06034500b42c03940e11120980c1031440c81240030324800d080240c0e104100602c0031a5541a80b00c0d44100007d04503a43c8905030714007114154401d4400c425140d201040400700d4501c4008501d51109044d03403004980c0e031501405460110014208036420303103034000825440001480310344040c0c15660101c5988070985005c2440c00da01074802941c0849c070340000400c4140000c9000022240c000400001e400c1d410740400803801d042c00c04100962004010000380f009092064000c0480c044a50392241e0000c2c84a460030913204900c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 139489739 1250 139488489 139488493
    0xb0703021e2205041404020d0609080403060b1002010606020d20031318020702030a03080403050c0f2109090402042301090b04142814040b0106110f0c010f030204030b04060b090108 79
    0x38400700e035205541031b4005d070106c039024801e030420700f007041c003c1206c4040035044010010b00401400740a070803d040081c0140d0303c2400e950070640040b4201c070180c1c0a03100060b00140d842c1800386108000d0b41050184078620701c2c809200903802d041c80d550020741c0d02c201c0107004007020401210507044c08180192106002d51a0180355800680c03075000c000402000d000c504808101418403d005841042070b90004640b07140c0640003840359141c0c401030b4000d14490305107142103000703d1040c064036500e6201900e0380f039150b100c5030f080201070b214080800040f001000f0000303c402c0c2e888038583d8001c2c24034010000c2d1280c1c0322030a00081d43c3c1c2845a0800e149481000d2049044040031552201002c189082c0034642e100c1140c0790181c108500356001a401d900240302c24800000d001c0b9049031411b032200c20b603c141c02642c050300d1703001c000c500e03800c2071708244030f2214654040c282c5c0d180b092981d86801440e00d42ca0350381d0410203410a82e0241d42c050369554420b860f500b07010102c1c174050462000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 139490989 1250 139489739 139489751
    0x70506070f15060801020a02070305060702010b030c0f0622090b0604120b0402060c01020703080901050106020f070e04050c120a020a05060906040b09040e010905030a0e06070b0703021e220504 84
    0xa440c0107414001e08010107801c50400303150801c1000b0b03804a070141200c0e00c029541c1d90f800c02c00007581c1d000316000c103984074003400c004a0340e2140140f0509001d400c014029003078420501c420410300d411099242d5401407803c004d0500680d01e81c0e00c128600300080c0100c60400c80c00c0580701001c440c1c80c031595601403003041000b031042114131100000c00310360044460702c0c03954451000c0740740c40c01145070700d10b269800070074904100b40e00100e50501c1103075904001c100c1a070f80d8280499807442603620209864004050500405901e601c2e000d602c0b44c05002103031030884609004c240201d40d440442003040e003110050404528040d180040204401c907030b854100a81403001a11600ca01e1048003043c2d040013800039015201c80e0840340e003001d1040001c101e021820700340661a5400011020006102a00907486619160b020b841069420010742d401682d0b401e2403d03070003540480c00e40d202d9070613444031600c02000c10f280206400703150010401002c039016141d4602d4044a07801c002c0c0f10b941084 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 139492239 1250 139490989 139490993
    0x5030102130e070c0b1e060a0b0a05030c09090c21090706030905010f0f05060a0e15010f0c0c061e0302180402072603040b160c0308090c09040c0807050607 68
    0x6071081a2480e06492100036202c51806a503800c4400800a01140d1503a0801c2004291007154032012001040e0542041d61450100704c2440414000c170310000130140000f2403030510031405140c0c8512054812351401c900741d0001822100101d4071a0b8101000190039100113118100480000364045800002c030300701204c03025100c20300c60044100b0142d4608441c024042e0035040480da01c1f0440c3c90810158030010182c00152000319191801900d40c0c0200180d421545040244501c5040c3c00100b80d8030300b940700450762108000c9040301003025003241540422030981c00a0010071b025111100c3d2800e114111001c0c6580c1c8219034014580705004285a100c1c0942c5c10648048049800591390003681c500b04408424880c0e441075007a03504208070a10a110340c00440c09580100c0004000c1d41c1d0b03000505800c87c50200d6083d00254800c03200c000000d00a03010740d40c0001502c0240c032404051200412110391048400b95941c044e41942002100401d101c0d25024050540d0207910300581a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 139493489 1250 139492239 139492267
    0x3140c041d0706081911070c050105190503060d080c1b030708120d02120a020d050c0f16020604050d06020d050c090a0e0903280206060406150e041d1605030102 70
    0x50303c2803809105405000483c0700f903802e08201c1e9107490a030030810007880c01d545200c42c284c0240d542202c130070f4911a4081100c0d03014000707642550100f0069140d10082d0598121415040909400d400a0903142c40b00c00282d20400501405440100106200010310940d102900d4440d0649402a00440300a03c20b00c413010a26141684148071590303655164040c8120007482121115441c0318911000d002c1c0e01c003c0780d0010000c207507081c1c00c103210070780380c03020f10b60072500c80c804501c041d8a0080110750241403103d480c01c0d900c45d00040805061655581c041184c910b40700100300c45481c0c2c0001d071031030402111f00c075003900404c0700f4105509240c040004103445c6130a50060082091f02d0900149042c2d004000322084889200d00e250390740080d1401c0c090a50310101d510a01600440b000035840c7d05052161100700c03000c50f044134200c5031a1000698840101900454100b6140c0441d10701c124550600841c1c01c0e000d42000b003549a2180c00710243e401c0322a00810f03c03070390042121707005d42c0004c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 139494739 1250 139493489 139493503
    0x120105061306050315100302040c0809060903090f010e01030603060f0204290f0c011e02030a0f0b0a05040213091a090106080603030a08090f0607051803160311010903140c041d 77
    0x401c2c5c01c00129255209106540001d0b584025841814900420030040c0d00014842c0100c00c010200e80d4070b41c88010620780c480c0101e41d102e980160480001c10b00360b41c032400c000e000444041c1000034846442e0785807042603c042c080f20340c00300c90700080d041085c030552550391106544e0485280581448200a038103580c400c1c2c0340820344451010138084903224080d03200403000038200b12548114580c1503041400380d08101c540d14a8145420761543d0444c1e8a8040c078205103000034110b2940a0401c000c1000a42100f00c0e010700c035a0451001045820003441041c940554a025517801a1601ea042285848058206000f00a4280c06202850324000b09803810845c05003030100403076440b1090790b860700502d401d092035144120028805c070560854014194800c85850a942d081d600b8014103585866950708184c400c03c501e241040440c1c030f0301d01d000110000c14981840c2d21540e0b51190381d40c5d80440a036080311a00041c0c001038143c0380ca441450b0041c0c143c07804e00701500a541c0d84881c0c440314 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 139495989 1250 139494739 139494763
    0x11b05060c0a020c010908030414120303091b030a12030c050c0102030411090603070303090e150904030e03011a15090105070203031909091103041202100c0809071719111201050613060503 82
    0x180900d5105160340d42104520140e501801100c0d16483c20003c2c0310743d11201d50720001e00d0b90702d10017640003f5080114404080c540c01442c0a244022445421001170000b60841d00800c801849400681e10080c0001c5000314000c5801007405604c10040004112001d0f11843c842d61243d0010800030f81c20007405400c5402900c0c103600c01d81c1e81c0242e41d101101d00b260f103040d40300c41c84030200020950031000031841401c0c00d400800203401d50110024038a03401402d07095000d04840301600580b032410008201040040c98110b040254a03404030745590441c0da5010241c821914031510f1150f8019150802054103080038040d502082c9403580c0b180c4009007000e41201e0490032880b05c2d1038003c02401038148480c8504112485c0700d407074005c000f80800c1d608a8464001c038000003c0709440da000322258403402101602620418048080b103441c44200129440c403003012038401d99594141010441c0c1504800114462800d041008401502d907030000c03201510304441030025480002c0d0f1440162 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 139497239 1250 139495989 139496009
    0x307080706050309010c02012018150705010f05220c0b04030f0b0606160308100e01080304030b0c0307020c10020f0312190e060a0c0c02090901090b090a020f011b05060c0a020c0109080304 82
    0x130004091216a02b40c154442d0407004003030101c2c0c0185900c5004000850003030008100e02c1c0300d44007500054400c2a9041b2164507a0480c50141113400224000002071041e1804258203648000010081d0003990080d01c40c10100030035102802041d50602c2e07404201103504038a007000310240080480c0c206a40582000454000654072892281d0310401038446500107014a60b550a0110b94032780c41070000721a0214200c0205280300501d0003a03078019202c64020700100d803040c4090004442d0550050b00852140004c00064220240000c1003000541281440340340703882000000b03030015501640040c2c92404448000070300d008944560401400400803943d501c00201c119400c81800c1000b0750b01442c03607000e021b00e40c00158014121607105804050040e914010700a4403844902d101a403c51280c207043d80d259841240071442112104182102c40b84082e21160700c0c201d03040f14006804200000c05090742c0b501000061240e10302481d109003000d00342a00c0c036441e4095485010015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 139498489 1250 139497239 139497247
    0x30607081b0c2508010c0c020d0605040804030602030702010504020a05010e1012110c060108071a0307080403120905060426180402190206060108160e0108060307080706050309010c020120 82
    0x40c040501c07025560040c0b10345040c060800b240c0e0f8070b02400301507100c1c65a8a41ca0950904066030281000d00400c0d50002c0002108403034648400d405808020f00c104e448901c200008000140319202450041600e40e0001555142c10320600c0210750650b0042d50602406200c40100d0780c0c1e5445810580b401240707483d542d560700e00103821b0040c24188105141c0580017080c1c1850003100043e1103030403180400210364000e41c6e1480d10702d1150000300490b07003841c030041002945682c01010b002d600688280f50000103c1c0310b100b22501150040c03103044520f60001c03010b201c01d00c22604400c41c12002308510981c8035401103402d00010344903000c90104154111050705080f0340d610b5043d60b506c00580c0e441c28003a2024080001e44422040340c42a0210ba43d4a0100e00304008030703407003030300960100d071580121951100015241107600400c0b042c3e01d441183c0010402038414413011005009036110244c03203040c488000c5082d26240341c0410110380c074040782142e460103801c00e004401c2c0c031020314283c1c3e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 139499739 1250 139498489 139498507
    0xc0403020306062e0210050105011b03050a05070b0109050402040e030c0a03080c070c1d0703180809040b10050901080c0a0e0d140601141c080a1b060c02010b030607081b 74
    0x1381c040c080d054900403da900101c06103a0300420a01b03503e1032070351020403203681c840005558601c00002e02c200300d96080c40c0c401c0c000030301907001804003880b242030090500c0c0032a035581203120002d030403078400b0300c2e215410b010440c1460b0103102c01090f00300010750705040c0c0e501380c0c56a5880414002400300145030b0081480140080c0840304c0c4036030841c8185061549680d031a6641c540030b00c00c00d00c00070044000103000c1c4c500c28403a054800c1e017050502000c00503039444000c010f401404403035901a5860400503595560300910440403046903da940e2030300c0804002400450000740b082149071800c04c400710500b6440002154234803404c5850102c58040c2d820306140c42588600b0103070b81d910030f0100100e040c4000c2070400c922200c080b00d1344402c00e030303460100110b03180d12710000a00d19031041c01080310540c083c50103090301260f02d0002c0a4001055114001610715000321040581d6658405841c41d040601150307601c124a810240d140d0309003011003e0110f401c45d05100b03410b620106590031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 139500989 1250 139499739 139499779
    0x90a06060503060f040e030706050403020d0e0105070605070509030703050715032c03070605040c0e090109050d0806010e03060a150f030308040609020604031a07082202040b0406050306070c0b0c040302030606 91
    0x30030079204022640c542300585003400c0149000d82d0258050300c40e0600302180c0310321a0008801c0c400c01a99003038100308131643c801002d45409888602417110901881c2e000340c41c01c005041c0110b000d540203113039076031030000182c02030132a410b900702c20541405a00d8860904035072204026280c000203482020440c0214503041d07020b0746100605050900c000d005c1444003c20b104410380300c0400c82e9851548a0402082c00c0b0b0320026001490fa401c42500b010396240034541a40d40b0101c10b0519010094000000904040c411600c2c124502e64860301c0011882400d04240c002c0c1005c2d41d07184080904580380136114400003403000b00444e03154a081000c54071180d040e00c000303681c82003040028800b04404c84011078022908040012420340024190b229050700c00c481540402072401442002502408094002d05103501c0c4c005449420010f2542c8040100f207100f01e540e980c5510720101e0915181742c92100140c045600b0078410b03c001d2000d03a0f07020440300d0700040100c440703541040300225204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 139502239 1250 139500989 139501001
    0x50a1a090609120706030606030c02060601030c12150801110c0304090906090b070c0b071b08131703041809150f060e0106180e0106020a0b1b18090a06060503060f04 72
    0x5411040c03241c0740f50451a0002030480c00c0c0c0b100b5880c20301c40700303031030742011000c0741c03036505103c40181e001d980031502d075500036032103c41c0510040c94407242c0808901c0180b019505141d82c02480e8251503035042203012800c4c030034040c072944256645442c00300300c91242075803030169005040e240ca540c2d8000c201000340b15404003070700b00e51000c0290428544030801806045120b41c0c15505a141500003424140c801d8810440a0900c041110719011407070310f44071020303001201d0f803002140324001c000c1140c16143e4950310310803140c41d0042d50350320309181603201c440c41001c80320076800e4101140200050038615090000d943c1070300b000039036600300d1b01c40e0b076003c0c0110782c2c4507033f84202a200010981c2503000b48242d40080c054004980e5059a402a00ca4022024400d0324010f800030040c0714006020048519007180d01488035900c50b403601080c80707801c0d5010844041040c1400107445140b4141910500c0d800b00e240301c400c00c051480d01d400501184070040c0f0040c46032034040c144c7c01c1300307944540c090703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 139503489 1250 139502239 139502257
    0xf0302011e1e0314071e052110030317240103180506011703160f051501141203030907050f03100204030f11091b07030c080307031401050a1a0906 64
    0x10b80070b0860660190003090000d807800c94403207003540001c03035550169003024808480180c00b102da0030300f070364401c40e880c0d0082444080c030308422070300c07100d105000c01210900540c40201e10507441c40c40c42c0740117002c05074004070002060600c4810003401303a111540c0c10103140c80311010600f1075818000101c000b0107550b40312804c50f0440b04000c01c20303c14000781d0700381130710b075083c01c01040e40c80c0340038070181d40b400b030340e0000180d05214034500000038110359041044542318008a50707641e00c0c1c100005e005514241c01c181040002001c2d10f00c1207140141946109030143e6002c1c6103107003408681c50381c685120713000d00c6009605581e50840240c0b010000380001e40000341086440301d413681303041c280c011650b00c020788003081008400041c81c50f02e10b210a0080c00d26070a40e2108403200d10603008a46c1040301d058041c800140d0524000c6540100258802da4150340d00103241d008460031040c40e0841071b000a4000c00c0c02003002c0c002800b40004103003404808004254896141d2000034401d80710300c10035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 139504739 1250 139503489 139503527
    0x106031d010c0f020f010e03070809040905150a0b01050c0c0925031d060723120903090901080106050f04150f03080403151404020d03030b060307050a090f0302011e 72
    0x20b646079950f0111900d000e800c1c55509954258060a00c500d00740e034001000c8002c150400c00c8164001780b00000100800d1001410106652901d03484890030104102e02a14485400c041013000314130b40f912900e9009042420182d0070f100310b01d016103a03560205000c4034040c83c20040880c0a1640001c801400d10320003042401c135410340d24100901030b00c51910320b008e803e594004a034281040200b2000c3c411003150740c40420a840385c2004044e0444032400c03500840c1b0040103291a007029001c5942d100e0701c4520f008507554840c007400e02040c84030503889207113140d142030018440703551149003203140120704072400710708945e218901e00d1070410b107503100060b541d40110000040005880c098021640108004010881200442000d030741f218140040810390300300020b0014034040550300d4046009140010b1155004c0b404a09291300a484141c0464030114400f01c02c241c3c0700c2420030150120300c00c0d170160203203141d0029009001074040c11181c841c1c50700210b0780583c4117407043c100662040c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 139505989 1250 139504739 139504751
    0xc1818090b1501180e0c0d090c0303050702130905190302072c100602211201091e0b060304031b0b040309030b01150c060b210c0405010e09060106031d01 67
    0xb020140e0480510700901140b11a624152001503c281d4032086420125101940d50754440040580754019041688007030390724031103040420b03800641d840145200c0d0311420740c0e44000b03004200c8042000d99010409604151240b40014400f10707429a0311104030024000703200d07440c58207030300740041d0350814180c41c2070181d0038000c07810b501c80c4480c0c2c2400ba21504020283c0341d03514600b50880650050300c0150b40802c0b410240440d00d26502c2e0f4180484c414150b08100341a4400000204d080c1e1040e582d080d01d480d86120031040f83c000c9040340000d228402c224004095000c1181380c08003e001600780030352a40c202140342e075010551001294800c0140503146003c0c54050b0040945001c103480c41502c1c200041104803181c1c10131101c080e01502c0b9405040c01c1503403060b01030140400b401da0041c20801600c40801106c21001e40007120641c044d040d0140b45200f80011110160310901d105e80d5083e041c4400c10002107507960540e045480c0c0402c0380c4000c0705402c640d106189200007425845e01e5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 139507239 1250 139505989 139506001
    0x1403010209130b04112701260403031d0a0c050d050c0d0f0506070c0b0721050a0e030d1b0c03050f0f040506030403050c151603020306031002120405010c1818090b 71
    0x600000e08420404603d0741c48207015801141c8c20000301c00d8030241000444100303c40c22503500640741d4010711034035010680c00880000954041024480b2402a90012000004010800c1d19840c0504010346038400703c4070030794603007503500c07011b89a615001d446047c0b144403d0045094007002d215420a007100e550b410050030003004482c5640081c2c5003000c80d00c010941d11881180003110442c0e0030000c00c141410541c103013000810000c0c1c805203019039034a404803451803003030001d8500c42000c00c80000e111491043c0c000e0140518603448400c110489034032000084c1c0203070555440c0145001c4494440400310100c0d05988100d802c01070344104084108810154000000c1c2089241e48058030040f03a0414800c4640490507503400380640d41042902181d140710768040c5038425001421281d0b071808900c0c0d900101d03885543c6500e10017081204100601c2000d0148013400341703a91410080ca05c100440c2015070f442180581c51004c11000342125003180940c0010003040c0d0400484e41c403606083d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 139508489 1250 139507239 139507267
    0x8030409050604020a0906030236030105100b031617180f0d02060a0906090804060903030f0207060207090903120e06060a0b0304120f05070507030605011403010209130b0411 76
    0x611039041881e041000080e50740c1450b0003611403e901070780301c01e8010f9040ca0000d90194209580c901031248070704c0005e45902c00c11003e0300254a464542020011f440b61081c1801d40b24010241c002241d84050104401c0c0c9400048035440f6820752010f071080054444102c2d040913004039881c20300b046010602c81003281c40b407103a003200b0010604540c5180855203185455023818401c04025800c80400640c4a6409404c00308003244036480005508074142c1c1c504e1480c0d080f6400104c006032010009004050b0485068240750b91103000800b205894280000c0d030701c60141c0114050f9948130390710b01080500420107004a0f0005c40303418001d800104440d03941d0790600702c0300035100c1c3c160400c0008480d08264200c07070041d0341020f0860300c00f6007040e400f542e07844100d80c41d0b50200881001044041a020b0059001039481071401080359407400310000040030901c0340c07851090740f0400605045540d881d140040c44110360307201080341a200800103000745580741d80003110b8100050907400c20711907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 139509739 1250 139508489 139508497
    0x709020406020c040b1905090c090619020f070311010311041809110d0f140a0b0403021b12030d1509020403140d1809021c06030b040b0108010e030901030e0f070803 72
    0x1040c4c4080240030080000c000301c9400055005c00c0000c0741c500240480d04045040603842130300a501a850426030002290741036200020080401000391081c3d914039905100040c2001011801801d10509584032918905504100d040c189a59912a044034102e000240c03801000100175254001038401d50490142c0700500d0210f440d8800302549000e18580b0030076000c0f41a4000c66406807519080d0f858108121740c2d07142480e1030307104161444001a14006c80648520f01c03a502814800854550400000c120308041a00c603210005414800000000c2a1942490310003404140b45c0000040400a400d00c1e401140d070304e41c00010040144401c100072050340da56548122080380ca9030050840e0a07030040f068282d18042c0d00c000820103114071780c0160101141107051031a54122620241003240c1700382c0d000b2651444032100708420b101c111581c0340d00402c5408024010740d400580b4050700da12a040019051582d02e0742014100d4000b08007240b40c90007900d048900a54036400e03016543c1d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 139510989 1250 139509739 139509763
    0x30a0f05041515081f0603061d011a011e031103070903140303100509040501060902130e180601060c08070803040501050115020102090604090f0b150307030b0904050c060309070902040602 82
    0x403e101416a40089410340311044440c1031015281d0040d8104032030b80b0000c5403c1104525a4940c4004000320302c0c6441803c092a6041c0b21803010194240f58007825200100c182e56681e030f0300c001c107009071a40c01c80f500b441d41c91040c550014808429107001c4d0001c0500c0e644030f0f44100d9000c41041802c503002503190098a01030101c540f00b5010611545940b440200c1c0c04224003550502c0c1041242001010160064801d100100780d161310791540c40200d030460f803004050741312111783c200801c7c00010003090b000280221001340842d083c0389429540d520600ca02e80420070341102c0c00c8280400781051b500550381c170081055607070415082c2140603000c02c3c01415400141d820b11144080c0c014421100a4080a00b01505082c0340c41481c40007881c00a0521008903198003841c40c1035910001ca81ca40164a9040ca41d01d03800d18804c000c04580214010314003d42c83d850601c008110b00185849400904a503455541d43c1c800c1000da0a08100d0303400010554000300d4003003074440d0007280001c0c0c010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 139512239 1250 139510989 139510991
    0x30a050d0b121c09050405041a0907090203040515010e2403010e0111041a0304050601030b0a0902060c060708060a050a050d030c050607030605010f08150904060231120302030a05030a0f050415 84
    0x45e2544100000c45130305940040460540003414105606180b0526620000b80710070340b1501980e94860106030b074400c5404032000e8000c4400c0349801404045040e01600008102400e03502e40354144000c45008120300107078540d1034034000321031aa0700350030403602c1080500090120f40c01601d00c94030640c120f402646480c0200100e1949141040700c00e5911036078200d4000d100c181d207035889070411010040c01041c02d55480341c55440243c2c4852004011402e0017000070610313460012001040c11501030f11103803042c00038503401c100d56034410348040d0541c0c1080711354140100385440c00b80c030310342c021a90003000c50181c001084401d51b010360041c401c071202a00c42c1a11038042840440d00ca000c121042009000c46905032560350801c2c0c40025481782c402e03c0014582901000b000079204090428040180f142c2441740094252050014005108982007404604c8103964007940380d018503118041084804000268044140d030003003541e0355140e003070070046c508150030071024550005190369402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 139513489 1250 139512239 139512257
    0x906020d05010b03060d031101150e0406050c04060c0303021602040510030308130c060e0a0503030d0c1b0b0c03130f0b0106031401050a0614130b0a090602030a050d0b121c 75
    0xc01404013102d1007000c0040100704089069a0159032002c62684400a10b41d030b5a4603da1181c884406410081d10003010020f42524003172070702d90251000140380c4024904103200400c000c54000181d203280c0c6501d420301603103407a005640c111004980e024040e612a04110900a204901c00700b40010387c3e010b50b5610000f942c521214480300b00700000001c051486030b102c00c000c00d80c070880542c1e001c14030044ca0031140e00c3e651800285180c024908a0b094241d41e00c4000b81c0982d00501f6030342c141110030b00050002e82d01d0b5281c1c10000c140040101080e00000000146144002030808141030b5201c183c2000d0402d0300e00344820420300c24010000400c1c40d0066841c040d03000094190b04a4000400f03016289041c51412200c0d0038034003044100054050000b65608046c000ca540081c0c90681001c94031803800756030080c910f00c911381c0b000003990010031030f400ca1a9800004c43d10711404550740490080340c2903004c50680c405903104c42c030171800f07045201203040c0d0040c400419519100d90f2801c0d22 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 139514739 1250 139513489 139513499
    0x100603030e09090a020d060507051209010c0f08010e0414030705031201030605010608040b150f0301050a1b05030f070e0f030f0109060b19090504031e0206070207060806030316080d0906020d0501 85
    0x25844c80340350040d502400c91003103400010180d800c000e03800341c50f03403500701c0c10981d4405207461942c1080d6030a8045075191303010403482d10b500c02c6020f081201d0030301d0000340c0e0754035004e0f031400d44510180014062410f4001d00c0d0305840000c0003240c00641d485011247d036061544075281138082c00b03000884100d800c003000010168802c0105600139130b0014050000c9450303103400d003850301074016207045e0421500000032065a50030721895100750714070440424919000c851190703802c0040000081445801e0051150031104000c1c240c3e8059101d0410000410100340018000c54211035103688c584a2901070014007181900202e5440b8401c0c9010300802140000304004816054440c00d020030218030100b001580b00d4000c950440e0107800d069031000711060510707994451020b039802c05680300c4024010b400f54100310f114010052440c140c501800c240c40020703201e12034169400440964194108240318601d0110b4030072102d8060200100b800a141c040f01941007001d0002c5202e2070180002a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 139515989 1250 139514739 139514743
    0xe01060c15050604110c03070506060d03020303070e0d0204020f09100306080c0d0807051221010f030f020a080303151806011b0c1203030509100908160302100603030e0909 75
    0x50390075031280e070340c0c1c0c2412500c0c664200100402090303107038803e844110302c03110f9000f900014251106040c2c0619910101400c21918141001d003020b8014100303c40070310003084d03010080e40d42017500c5107880d84510f89514002900c990400101950291000401c00c099498000062030341c03030001e4824200c0080342c42e005604840c00c0707101d412002d400111800c40d0030703d880055044407074403810116061003001c1d180c20b482c00c55804a40941d2650005150076007420300c1d12014680014142c03040072540c1030001c106140e543c6480000c040403d00d6860100b1955400c555402404202049a0b1285070280015000e00c06006400340512403810030700e541c80c0305900d01e207442145c040e1102d120425407a5144680445203100903680307601c02c07010102d280c0e0500480034580034040e13500451613003030510700b190401100d000f407180c54524210b8000d00260083e000c1d0f8040701024240509404001c1c1021fa00b440b40c10700d044100075160a0000c01055000340700da0f00c806106543c051040c0e503540d0419a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 139517239 1250 139515989 139516007
    0x8090a030f0f21060602161503020c0c0d110f0d0506060f0607060f0204030213140406050a020c0729040605040b0f04090f1b092709020a080303010e0106 67
    0x54002011550044002030140184031000c9100307103003625807894400f0081c181000199510b182c4070f915150100500d59041107500c2110014485d1032042d14030701814561030002640a280c03d041d00071070200501e90060090302160000546054084041840c7c500c038081c051288040c0f003040004030b115a20b00340540301d1b400d1300c4e61100c028803403921104100000c080380c40c01455070210042100000007506030040b604000c1d5030300400b6031580c0c00c51040010f80c001c40211400c0042c03400000c81400c0540303809103504a0303000000010161508084000a071044041c080070324811084000303096082898540303403c1c00c003801d101a8000021606059030711840c8510000543c0500c4140030300d800d484018440010080170b290300d026603c0203035800350743d06000390710f07040d03580c0e410400911a000b9180c8480c921451a00c02031032070400c01c1144442c041d0450f44504c03000a00003240e4104000e030310228000c1c0c0c0040154241030368607100d60740d80303900034000d680022948800000309a03000f107600c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 139518489 1250 139517239 139517243
    0x40f090605040201030e0d020c04091110020d1d03060a05070306050a12060b0a061d010c0b09010203040c0509070203120a0e032205180c07150f0b030f030a0c0b0c0408061608090a 78
    0x81c0c00d8603027100c0100000b400d900f40098038445905205144035540e804906030324904150040c2026a00000024042922010080e808440040145051554042226a0b11800d00f201c001b85a498a6401310020305660704080d812849604d0b010803004494155410000d1142100b071103a9428281841210b0020303101c1e20020981d42c0b2018a4950b4145007d0010110180b5040244817400e441e003248400b01a40e038840941d500106220911110f10010790182c01c050b1429001c5003800c400c02581c5e41300e001c40c2c1c0641c40000e031000c0307515851690043c4403141010000c40b505c0368000f080e00440d0350400040d60800d0b905010000800d420031400c46035181c0c5900901000701d603642c41042419900242c070890f04080500c0e160f0f41112030901c00d000e01e0684078040013514040d05003d16240c4185904090f040d0b510501164180039801030310102119807141d52030f1101d13103406052907028080d43d0400c1000f40074017801c002d180b2251881c441e00c0d08610b50764508081d203492480e240c48014030040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 139519739 1250 139518489 139518493
    0x6040608072306070c03031803150c090b040602030406110703020906040515030708030d0f1b030908040b0307031b08042a0302221b0509040b040f090605040201030e0d02 74
    0x104200b408050000d03440025040b4107900606203441000440b240c0c010a0212440e1008040610034580e0240d120b80d8200303444440c01c01e459040d519508130600c9900f115401460300c40300c40525842c031400e80d1000801103500803039269504c0d408080d4883c0c0107030064500003041d0240802c4c4c8045c00107000c50440760081e051022984400c014040607140007041000b0b07941d80d6060300300c41d5450410040009001030006940c4520b24081070030190b50721012946401c034146290304030703589508841208007516078203002440014520b41a503c1d402254000501030101104200445825411200750039218060700f04809035a034005944051040d2809012400700752468000441816141c011494a031400d143c040ac0c0c0e26400154800140c0506100c00c52801c2403511a03007009024040724440c80d00c125844684103500000c02a01076858818420b03034540001d072089894940c0850760f801428142404074007240d00b4910b000d0b00060314200e001914007200c070394101d400459607030703515206540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 139520989 1250 139519739 139519753
    0x10c08101211040209030303040c05040b010e1c06150f05010f030c05090918030711120d120504060f0905030903070503010b010e06070c210515040b0103081303021e040506040608 78
    0x71542d084400d603500c0380c2e802560800c00343c001c4d0358041004d180324602c41c40790174600c0c0f0308040500064948481c00039042c015202d114500c1c96461074403004880f000c0d04403007449200d850401001070032022460400c08114542c0204002030940314680c01c0d21000c1c0c0b1101c05211400c10100c0444041c8054400050805d104685a61030611059900140a501c002c840101c1500455007140d111480032200602d801e105a2014102060341d06240710030680034151004030f01c50060602450801c0c154032846d81c4100140800103c3d500910b8000c51a1004000741c400a02d0115500d50020320000e02c07911a9590000c0d2519050052040c0c0080603034034001176284070b005014050304840d00840320010304c60400b2440440d041c003010010f844c0c1700c0340382810b000541041804c1003804e503d8042ca041c5880100400f0801e070420f41d40c1140e078408040c0d59149404102684421803642000307601c05000309130030b0002d4031000c0c0302d0010b400040f01c04002e0350301d41204010403196240305a8190390800c2ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 139522239 1250 139520989 139520993
    0xb1f02150f22080406030218030f0606090406061208070213060b0a0f0302162102151602160b04091503110d0201020a06020f0703080c03060307030b090a080c010c081012 74
    0x2404640c1d107110002c0c410203405030342d450410715009034010b0800640d02040010f1180b00c800c2403444409000c1c1c015010480004443c50f803030728002800e9501980038000030404001c4542c1c000e4005003050046500c2c0600d6a01d01985150300c4070030281d21030f050400241c45580e070584a804222662666041e241447d00c030f50995201c0c10360a461001d05509010840200c200c1083c942c50342803103150705c491402c07495041d00300c0f070fa80308003904811984141c10f80802016100c030b030f2a400200340300e640071410304c80c02c00c224500254040c0e0008a4101c1200029042003141c01520540b16100000d0200c0c42d0445281c1358501514800a0001010540c0107952400c01010002281e401071043c1da00030501501c568044c3d900c40d030910040520001114410305034030010803500020b603104c41a2a50500c500000d42d11406804090404008100403c40d048c1041004040203507101c0622354171142281c2255000300181c2202070042000c0300000703083e19000c3e60100d015650110b0106000c80007a1f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 139523489 1250 139522239 139522261
    0x21c03052e230103150b030403030b0f060a030b0102070522050c22140109030b040b09010608010906200a2304030c091b0e030703020906040b1f02150f 66
    0x80c2940d00c0282400240115041680b601c40300c85914415614840941c891000101100d52070002e40c0000b542a000030322940c4003010031250001c0d0503140c0400c51140ba840042c010100e4441c0c403d030722050000e0710000c40e43c1c054000c43c480c0c100036000d8a02241d514012f201c00120007400024845540a000400d4100784e5480b051f003003900340007641e040c2085c0b014120080c1005021841c1c4038003410f00d0070048251480e00000da03a15003840c0c20540c0610710394511740c0c0000d010308020306c49200346001440c46c0c14250302201c014408140244284811400c0000c0240030314602000d40068100e0007000b100c1d502da080f10072038007455460060030023005018681e5034500f210420481e1200b00000404503069800b0007010700b045110010707440d100c3c2013111055200035041003050090320014406640e03004141c000440fa01a600e0101c01d0307544000040080400c24107031580304480300c0e10141050680d0200310b00502441d02151020350f40d810149440440469102070031440c1c0b00b002603060642 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 139524739 1250 139523489 139523551
    0x60f0d060905010b072901120f05071806091b0c050c03070611010c0f2001180507150203030f150d0212010b0307091e051312021c0305 59
    0x1200000051441c1c41c0c909940584600382c1c007100d10010080340400c05d010070f1030761480304036003ca510520044000e06074180d694805109071002d00e000c10116005214442c2c50100c8107035800000c1e501c1c140d0300c0304003240b168912240c0103590f0300d280000104802e0b03004d22039284d141e11440c51144059455840469956803050320403940c900400700c04d000d464900700040005464262181041c2d00303281c2c84a02e00f114804605002000040c6010601c015040500c4195140c41c02510a1400c001a00c00c54050806240007907d4100c9074900b03503040c404082480800e44a21514071584000407a000701d81d20b01068601d80c01c264181c00200798418159584111180c03800352045401420a0f000908054240c80300010165100c0000f040286001c1c8802030150240410802c90603038020060503a0b1210400b0352b5000d9039848002c03c01480d440341540c1c408a80c0801f0750412286040d20007512818914048042d0b50020920750310300074024000c0034821489010404003410701c90000d000032040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 139525989 1250 139524739 139524757
    0xe04020a0b0c0c010806010f0e04050703061a131d060405250e0108090a031202030601050705070312090501080f0a1a0a12050601090c090909021503150109090b060f 72
    0x2180d140c0000c48441800141003540c801d880039004461440303002514210b40207040d039040201d8207074620303c50342d040008068050010b890014507555442c1065000b400141c1120f840c003184480b904060b08540700c014004101c6444019908541d51741541208000c00c2c00d01031000c540f818001502805d1940c0300c1503115501103503a10f00d540c8982151010140400300c401d0010f11755075aa204a035800000050308240d401000f01001c2519490003040460704000380500c4c02d40000c00b00d002d5078840c10544000d5a0410705880c0f200d55a4588170710800d200800103808245d0420700001c0a60040c070100c2d105800074190180c480d030740d50220070001c10b03200d08104460007072411000303195110b41001c01c016002070028090800f1060901a14081059010001c0d1071b05018440d0210f45c4c6c0310000004a607000710001c14010000d00c001100d03000703070381e0003000740c18004401c102400103448a017154198003072700c520b0019074490000005480c000f200d0103802c44010011313010041584401080540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 139527239 1250 139525989 139525999
    0xa03020703020c040606170708070203070201030504050705100f08090a1a09010617010204170307080a1b0821060103090308070c0206160501050f160903150905061006030f020909010e0402 82
    0xf1040c1c80003c1c1119030340d0f003200d400100020710303003030303010408490054000c20b00f828000074900e04800c4c002c1d82d82c842e00c2030007030400d5155804a010081c00308106c80203010010034034840c80c803645400901074405944048000b502e124017003a90030501040e49601181c0142403900b2603800103106041c00e00024103040079540d80c8441c0024904000b003070001d5450000000940c1d250310340010f591500c0314030f40c9403107400c1d041040300300009400113003100ea02c50307814203001803000c654411407144030f404410302a01c0c801e00055992404140442c1110010300d240c510004982ca40400441c2201c1012800401103480240819081d602850f04650800d100402d203500d081240d6014071000c2c1340e0000112001d079100d00500200c80040e140c0700c0c2e03201c00d2741d2000b40008221044000d049403600d10001d0801300c4c694082c0140e0b035009800060303860740c000c0c045600d80d04050200c0e0460440078820800080c0c600400161015124001c03680c00200c000c01d500307127903424018540b85100020780308076802 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 139528489 1250 139527239 139527253
    0x71403030403020d051924020f161505070c0c06020309130b0406231c0c05040b060909130203160f0e07270e0114010c121b050a02040e0c060a0302070302 67
    0x2415480d140c030015240701d1410310701c3da908101f91100c0c0c18521541d842640394010711060381c0c41030f00541030380d0004844800c5540c50300c01505101c094104900d4001901e40c0c02e01c020000410740210400c400e441c0314101104445540d4041240caa01407103065a5001c078800309520142c40503a00140c012000080000450755030f111840c2020046d2520b4025030170303601441a0030249000800100388001080e102544a0307081c1d69a92100c00550103114802c41c0d0b108800c0115440d9074040d10108640644104040c0c1064500c07040390f4111a04224803920490194082d0456592414400c44206051300e4041500b031124904400b13a004244408220b481c1d0070711942c1031290501c0800c0480c4018035405c1240c140180a011410141c01c000c45048001040303240c0c9980c000f0300a02026007103107054040f010024030840e1409192090902250000d9801c0c0e414801d02156003460b1510844e401c20145980400f40d9841c0c100b101192a4003050a2007044a00d50007900204a550711903c1900c038a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 139529739 1250 139528489 139528513
    0x60402010e031c120c09030206070f0620030907091503021c02040207121404050a0b031b0f04091503020d14070911190806030d0c0204020408010e010905071403030403020d05 76
    0x650000303100200003c4c81030200702269070f1244aa0b07a940c1649280102e07501d421900491264456488010880f500d140109403c1c0001a40094100d60301d030000da01016103403c030007031100c0e041511411800d00a0f040b001030910510320441140713040102101721100e00d16000c2103908810300c0d018441040c000d0040f40010703607480c03000f04684d51151104144000c01d03500d00400d4030740111a01901c3c0c0c0c80800c02480960b4900c0401d10407680689800d81d0303640d0740c1406856048901401c07019031198040313001c110b1560103101510603600040c008010f20030030b00d0062144001107110207500141e000c6028400b1501001900380034000300c00484107025070311400c8404644000c841d08414141c00f042485209458580c1d6401806076464200030030304140300000d440c0c0695410034414059901a60001c54446030161002071403400000c0000d1910b2181c0d1502900201c1011606070159000114403030b0b8555134000101c8030054015402c19040d81d0038407954800c01a010b4421f4441c40700c260035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 139530989 1250 139529739 139529773
    0x1b1311070b0a02030403180303090314160305060a0c0c1a06010c120804120807092304050108010504060e16030803070c0605150a060207082a100302030103170705060402010e03 77
    0x8010b1406000042c0e0340e10301410010880401c07888000c003800d00e0a5410000300790b100a13007000b030f01e40041a520342d8040624906113400c071002d4000800113031003040007050100110320320348601500740040c4100503a1107022164100c59240040c41040d00e484244441e40300c150410f0707031101060410f44107400403911110544c074600b07683c0c07400107440001000108014829810300c002442d051480745814086d40140500c03015000d000408002140c21a59040e034441c0c4800012001400800081d6110400c1ca030203440122000d41e400c0f41011301c10007603004001014444800c1407010550713841d09603610a01c5a6101601c07010400038040f0507a4003152040c13254a000d60703c0481600d5040c0080410301c4400c070701c140e0220003503402080007000342400204040481c42074040c005014441e88229940c03c606001000751340042c2c6c46004d80390141d8041d40114140d80c001c0b45441801c1985142c40c4085120725400204282c21a001103401540100b42001500c880242030700c0954003c009c0b007003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 139532239 1250 139530989 139530991
    0x30304090c022e060501171503030d0c090503190c0303030513020406080a050105060603070c17120f0a111819051f0318120809030408030a0507051b1311070b 69
    0x40a604810b0990f00c502414501c03402c1e008040c20700b07110605000b84203180d80b0040f4010f2550000b801d0000e001000380d03809008031000c803003c1d0b080c00c00043e101094001c1081400d402244d000b841000144c000040045800d801c030141e204480103552411685c1c214060f06001d888410b031001c441144c8001a9168002d60020b0800e41e0700500c0c912103282041400e55501a1100c2d01648042061000d45079006103100c0c03415810024844010302c00341e0360506144119440c001030b00c2d01d00000e2150442824003400d0081142c00001d0068824502c00a1502d1080880300c040310500d0b40d04200300c5091000d1181070030301d07080d1a4482c0c90750742e440c04141101109181c0760440e07008000c2d11128160075102d81d82441011800c40b11071150165109244866446841018800b000000601c014420001c40c0c01a142e001e060740d888000010016060b6082400c049800c0e0141148068078100302c1100c440b949140100303000f8500c20030304181d6004022516107403552900401000001c00c0c5280341035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 139533489 1250 139532239 139532293
    0x807090506040506090f0a020f09030106060306060807140a0c0f021201020913050921130807030201031103060109210506010b03010302040c02070305060c030a0603020904050129030304090c02 84
    0x4185071a10a003088202d8000500e0755228501c80710502c48414110781440b80c1c840718601c001aa11000c504070aa003d000d04d0503056455070800c000403600c83d906800c02001c480c55612074000a45804100340c03004800d601044c200d64406200246815100c5d00355500758138000c41a40510145540219080304c011f801054a240e40000d10000786042140e4900c0300078010050800c00380c101002002e480d005142d2056415408940c456010000144c044a4040d20f0700280300d400d45644070742d8140c5411452005a012904c0c10340c00d2540c19014100b1288184c20582d2114902c40c10101d0a00c1408203402d842013500c20300642903400a0b07000c01090340a4541c0001301d540380e40c0355104100c10340d042d050100302150019202003002507130018402d50040c0c160b00070507480703079201d8038080002c01080e440031b540b0480800a000c1809010b6011107076008403c560320000082d840020307440c00590800890701a80704100030041070f12642d01c181c13000358107441620dc4254140c026001030003c60149 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 139534739 1250 139533489 139533491
    0xf090519050a08030c0a021003110403050d1205130b09011506020319020d0801061d040606030f0e070b040e04060f020304120f03090308060f281d0108071e080709 71
    0x340114900100c50b01c00401541000f1031902d6000500c142d10740c582d20700001d002d0300038104000902d0740a03411403000001300c64102500c80d650790602c1c0b9941c1c0e00d0303600c052012070084010004844241c3c01042c0c8121101c15486074500e605546070f4414041c02495400555030350f4420724050400080541d00070003460740110380300c03500300e500000d41c20400c15080055500981300e6252082d040440b050464415050069600054100307850041f461403400c0703035203c1d02c0c20b84042411501355001600c00d140c0081c08000d144002c040e00d5541c1c5a0a00890b40121405d1204014403e81d010065a1140c452030303020500c0070480e030324942030760400e82d0100c46940d1040d002d18802a88001c015401d58410300e014000c0d1402d540300544844c0c4041e04850207051040c044403916190500e14140780328881c868510f000d28149203884216005004007221303000740244854030030001511440c140d03100d010183c11003a1404184080314801c850314088a20315032400050000e2081c0950f20080040d108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 139535989 1250 139534739 139534789
    0x501110c07140406030b0601110c04050a0f150303050313050102090d050601032d02040903030b130b0f04020f0a0509120f010c030b030f150a140411150f0a0f0905 71
    0x10800360100040481ca00030f9150220400c045104c48200e2500020203080c90403010340380403c650b00b0b100c0c8480c040783d00b15051109104c5040e440c2d03070120007200d002d0381c400c003c0100081e1604c520103500740300c0980058018408904030140c490894000307103200d80001413900901e48003281d00d000980c0c20903107654121500410500030fa1055080c15000440b400c0c586000024901184005440c80040d0050340c0e5001c0303100c10140654807201d10040014800d45800028103400000303444111003450103030603003007115140c6013440d0080d81c1061041002d142d0030030440100031903c0d42c10075030003207620407640101c00c9400788041c0300c0366a41c0c140c42c0e40041414660144080c059403500e000f090300983c40784150501c0c46030040b81f012104131980d1081d00150703d0b5040303c81e028100c3c0145401e00e802c60707136042c00f040003404142801c40b42c41c199440758420303d0110703c1a0450040e4986500844030401904520038414007480c80140700500b4201900e54940c40401c80321a81d21070030190011601c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 139537239 1250 139535989 139535999
    0x403021615080c1c0b13020a1d03010b0a06030c0219030e09041506080c0306010609060503010902031306020705010207020a05060a090b0c0f0a050a1106030c07030c0501110c07 77
    0x10212840038404100350322119031806005000c8000680007600c00c012115020039250150042241c0700d06210200480f5940440111840244018002541301d080d000c02903000300800d5000341e07035002070180c076134400c24074408000150302e003640b514150385956181d4a484050f80c80300106c1002e014541c0e40001c18442803c0040d00c1c04100e100503000e000c1103241588002a4805c17990345048170305580c0714106031a54503090b005140c1b4804031411103418500c0100e1241400148508141c604030100c070a541d907918000d0b64112045d00038000011002c01c0180403c2e1459002140c02a1072916134501c14401070300d4001c126044a41d00b1903259400081ca10194034080700500054002100c050f80307826811740c070241031842070340b041102860000c500003c0086091141e1840480d0741c50540701c689010b442c04a880307030711034141150129806a001149170034654240ca01c00d180c0e102030703036181141a132400c3d5000003c0300ca00b01d80c150b4a42055140641940d000303446600116030003480c0d0f035400c0c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 139538489 1250 139537239 139537243
    0x90507030c0e06150702010c03091517010b04050306010302010c03110a0f060f05010b0d090c05151905030408040308030c1608040611010911041e0c0518010201090b04020f0105130905040302 83
    0x28140394850100c000820b4004c2c02040119100513609007403241404043d0314042d20745c0400e42c1d01541c51010203901410b031041d001038150310300d80c0c492114001740d80e8a0f40800c1c11580141d0282d9074259003c0f00c0180010b500601102d40341c80d010b424000038440105400a00c0e1860302481118400d0f40000c011040260034000c0c100400300d58407090100d981810380c1039130030740100c0040d0039110b616a80f0180512218a401a0141c41c4c0030340815a080f1091101c0c04e21340e4402e802c22a100314200c1c000f5103196106600b03aa00581e805501a450300f403071503c62640030340000c1c004140d5070408001da4035031038002d0007225000c03600c01c0e040c540d100c81c5040c0c0003070300f180508507005550741d051240c0e070f60000e0030403c2800c21a90341250002030480340400400800aa0841d082c01e607149424180f800e00380c2c00002030001035200c1c0c0080d0344040d1035100128285c0d040e440700240900310340c40c0850014541a012503031450018500141000040d1940703032202102c65100c0c5d403c3d50b54440900040c50f43c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 139539739 1250 139538489 139538491
    0x30c13090203040302101d010e0a12090b0304030f1e02100506010e0d0f03030207120302040302040605010e0d0303111303110f01030203010f1202040b122d1f090507030c0e 75
    0xc0308045040d4035282d20080e4441d00300c517101c03d08440d51810444014603002c02da041c40261040000c000042e400c5050a82c4d890ac000740c103403003608d010300c241502d00b4440d0800c14192160315030003d081d0340b2540c1c0e007650089500314039603040c4003401080044e0808140074000106250340c1c000c10074807a0b41da941d80c01301c3d42e01809080c10002c3c20f40e540720264a61040d246c2500358001d106801f001100e080440c02806850b40041a169001440803841da5040d0040d200b40c1e8000c4400f04062580c2d0310040da22107000030603041d0081d10540d1050003003030103940300405000c04d1440c55890300440d0011240c9104958100300c903050030300c1745040258202480020759255007804d007180b541d410250b2070008101e16110b1012903c1100001c00c1c03c540300c0f900010041c4901504030b4a03259400041540ca51846a420941c0b03045808403614200b0303426040f05184149000c0600503055130581409180302500c2e511000c4240c07104140400a00c0070042c00c1c009602400f18107816504002000103c804 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 139540989 1250 139539739 139539749
    0x18060103060b09100e030312040308010f05030d0e240a05040317030105210709020414240405120c090702060f091501050607140703030f020f01060e06150d02030c13 72
    0x5100e0b01116403551004e07420708003190700300500300000b03e4000030b1652040080604103070040714103220130150031596890596000c10852803900341c840b41850350700c41020145400040d03000121389018104010310a0741561880d041100800d6200e840c040c0d15409001245c1c00604000703020420300c084010f0040d014010b400760689035514000020301070041207a4a101d5103000031941c1503010f0320030800070740204200b140554030341d030303441c210349a4450410180e14050080c10314881d1048042c0a904030380d846040e0034407400c00e42808288240001e03010024031182c4249070b0101855965101410311070042075004043d2407800131402840f4010151520140741c1c400500300b840721141c02030003415150240c58050b00e410ba01e04200e16029080847d00140f801001800310525030b00100301c4049800f80e030200c03803c0150040c2d02900306e030780030300c40e1078030f50000003000c1002c92130120040d10010303113900c56590400c10a0422001241e10035144103400002c00512011990034001c0c070003000744 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 139542239 1250 139540989 139541009
    0x10303112a10051e040302010f031509021804020d0b030106120b041e060c0903051618020a03090c0608010f09050108060a090c0914011806080703030305090a021806010306 75
    0xc100640845010210300a28a10400d80510b000e0000303031003001900c0d41441c1c22410380300c02e40054500480140e0041c04260b00103000903680b100128024040c0400c2c0c11031020380d6007000c81c54403507201d00a4101044000030b1543c59000001c0b00d03035881c0003420744401c5d500e40001d51000c0c110304150840d5496031104401d24044000c4070041018411000d40c01030708003184102001c50610348558008041100034565850100054021640319084800703480c440d8048030800390b421a06121240f12034410140c5100d20034884186002051f001341ca040001e604001c210500250340350a50f0002c00e811500000d141b0100400400080b05802d200800302101d08000550419102c0307030310b4284c0100782d084c029071662442e0041081d00800d01000f040d179001c0401c80089001205100b11100380301c4c50303824010b811100045203440303104400032241e104000b04203007451503909401400c40180031f40d81c94051802d101d00507032107002102c850400041c062044c0c4d46404400502103404640001c4022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 139543489 1250 139542239 139542283
    0x31813110a031a061902060c041404020f073e011e121e0b120705010f0c020d0602040914040507060e0a0b041511060c030106080405010b030601030311 66
    0x12010003200da07203803001d1a0105201c460020a140390503091034080f50031900010b0001c0b841902114184082040f50342595415152004058841d0007a03010b4585881c04840030002c8525160f801441ca10f419116014140009500c400007140600c0540d4800c00b07603513240c144011a411800009880da9001d90340f0114010340000800182101050703000003403c030f1046014160140d406041840080c41d010700c2850030740501020015403441ba0203600905001f40c0d014140b80000c5030840f04560b13000100111407078980115880460700c0300c54024440c0041014000da1104143c0e00503c50090f1009030b80c6910301600e02c0c084941d4900d40e01c00c0c5107000818040050404a03200085904c58601a68000e14800020b40e0480c101ea00000c1e03005400500010303502e80c101c01d580c40b251810303124201030348801120540c03100f2045406100809080006102c6030340078080c92600a0300544c0001020491403020925000d4203030000e60114210351408500d025040240ca21943d2040d0141c2d005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 139544739 1250 139543489 139543511
    0x111160909060209210106080c030303041106040902040b190e1503071205010e1f03031b1103010504030305190603050601030b060d0209040f06060e01081c050c031813 73
    0x10450603406039040203a00c9090500a02049806035032440c0401000b5507031804084002c901401c0307440c0d411000d1942030000001c1c01440219807100b4050700a0080c41c59582c4507500d0b401f441c1c55400b11b840d8043d00c14040031a0480c003030b2019101821401d000c180c1da42140b451119a5403900110b1203040045803004040a0703150f03040210045100c41c1c00315070701c5e81c55255050f82c610742c00c840c149203540d151100002d5150003d014280c0613141800241540c0d40e4402061a12040d80d404060046000c5024a190703007074680d40c8120303d5071301440e03101c076580084500003825610252010307000661505e0a110048030103280f6000803544c041010007240d0300e55540c00d41c4481d0b0520002d400d1020002c0000c5644e111008070125242d801881c44aaa142c6440c00342c10490311000700380d8005107031202c04600c2d00000030311141695021790013031900009003411000c0555a8005a40030000e0070b11245600d1082003015184594210007500b185114100c117110f81ea40d001d4080150603428451075601e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 139545989 1250 139544739 139544773
    0x201060509160c1e06090b0c030421020a0b150306010f060909020f0f0f0a0305091b12010905070603060305012003040314070213020d051303121d070308090111 70
    0x30810302c441c205542402100e050601e4a59a01d1400d4180300200740020f404000850780140c481911035141030b4450b4803055507003041e40c00210340c024441421410045103081404046c01510052481120740d107101c1d503900c1690b03042e421b03105104404207100c150b840914040c03211901400c2c1185031f40c641d00e0f280c03d4008102403454801ca004440e4002001004800c902045407040f0740c0040c0d00d203680e0f8500c8151481c241e40808a11800031b4508004100c06501c00b00760b07035228491010342815544103000411005884100910a1640d0b80e00f182000154003446504d00600d616180006c0b694a1410700318250341c3c2c14140d560013920274a0780039403580d0f0101e055130342041c1c151500c101071448907029400305115074440a1350040e01210546602403da0f0010b000e155840f040611490700c03400481d280d103466443c0010f001c43c1c01d1300a5003134001005d5002c01d41400b8024442e2003004002c540950612403190401d07a910603001542c86c1055130003124020302c401618009010b0038100e1801c1c54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 139547239 1250 139545989 139546021
    0xb150901020d020f030f0d0204080f0a120903050303061314010e01050109060302030f1308161b0e04020d020103020a090306060806091606021f060302040c18050f0306060402130305060406020a0201060509 89
    0x243d40d51b140403800b001803841c01d5065802900c14142111152400c007581c0310ba64034404c2004079a4489030011086021b8410300d0000101d903030100056041d6120b86c4200b0420645007182082d905903600048d070a800c0d24100c1a0b13008268149000080b035040c0301c00102a019160010350a050040042c410b0955542c038600b54000500303001d500304c01c45645003070001da214084d03800b84242101d41544042c40420101d08405200103041031601c1035440c501700b0203060f000c5030702950201d018003040015502130340051440c14502d01e0120403140c0c4903941c0e4003c80da1160000d0440f5030204041000d40801040040046802c407000c0c240990300c0d04600a5590362102010b5003c007003051007103580c403001d5800140c06036a00410510a0050301e440c0203002115104105508611710000042c2900701488445117255000d40907001c81c1da00c42c01480701a40c080e079202e0214000005001001c03880500550b402544102d40141c0d8403801d17100020b09545032504414414103242040c01941218850301c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 139548489 1250 139547239 139547257
    0x1207230403060e0a050604380a240602060603010506010c02090103080a0210020a05130e0105030c090c16050a05010605040501050604060c03031508031308010501030804030807060b150901020d020f03 87
    0x11038000708000d41c040c00c14030402c5000f0b186115a0042c40100300104d441e8503415031551500c03201c4c0303d2540d40c001d8580740600071001818812301010806079201c5400c084102c0c1107104107000444486005042440241c1d4881001600700400307010035845c081c002d00d600400246420340043d02c03a50001154540123100040c410503000424101c60360080c0b1189108140d2004115200c400e4654090190b920041e01356040440c1170f103001c2aa100c401036154180e0b44090020910341c8050700620950040140c048081d200e0b050005130104d048808000d641907210740050301c044400c52a1041c01d48607680c0049100341c0c108070040c0303c1901c0361000c0e10115001c901d81056807102c2c50800794010320282c111004500c003468400700f01c040c000402441400001c044011030a42e54044803800c880e401c0c00f004228600030001040824054001343c00c0c410f0081900090300d5085400140080c0c1003152200f5080a02103204061581c0521a0280816444c000f60030040e11581102d038592203100c41c0d13 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 139549739 1250 139548489 139548491
    0x20030c0603061807021c110f060f0a0f06030507060e01080a02030402010c060b01031404140f06090703030e01140304030305040b0f13141906050a060b0f070209070e0402120723040306 80
    0x31003413482040390481c0191565080b00741106c08510080840300e00b9000c2d000700f407040c50901d001e4214005040b5220f01e01c070600a4041d0f85400100901409808100126558540f44d0200210b401803002800801c0705848002d0030410700e400141c0001d000510b1032042d81c2c814020000981d07000300306640f8460380060002401803074207006900a00816116050906c1d0310800c220800068034041d6030804118011900c8a150382c440c95699540211400901034000440c2000020f00849060030144014144600c020742140403030300180d00100c8040d03000035254130503c011304c104220a582c105030501542003051030807e52412002086080c010b10f01e043c9520103104041f82800004502010310805055032403a40c10000b02030101561036003003c91a00d4000100c00c1039401c1250080c4105034505801c4c603120350204000c002d8014010828010001c40c866800d80e52440200240f14220112890303500348060010106920308004c61540c1500302c02c040065009003043d07404695000380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 139550989 1250 139549739 139549741
    0x60f03030c021c06050708151002120901170f0a1103041101140c0304030b04060e0d0c060c1202072f011211040510020615010e060d0509070320030c06030618 69
    0x10300c02c503400c901c0c4004c0e00b000c0c43c01c03041c0046281d1003c801406040301c5110301c0a41030501d400c010100b12040ba100016a128103643d5a0664070380020b0211000c0505000325058090143d00e40c20601c112004000062800200556910325108080385e110540100c0750451609540302020000c0c0001241d0601c10300d040034442880600c0101c8202c83e815005a0345c46995914040c03003640401d40717048849904120194104200020310884107620607983c5804140c0c40d6140c0100a0985159001c10083d10800781001090940002c090382e9100e410140084412401c00c2c42c12902c2642c000302030407c11100018850b03904c0080c844c1c4404030011b0004009030706042c1601d65102d07941c019500544421b09001f1999008241d00748161912125407880340c10900045490301c0d054805036034001001e0000b50b001c1800f56014540c44490310040358940c945035158002c8042c218100c142402480c683c8a0b00030342818015101e040d841a14000e00350b0926500103440070380c000da2142c04a20f8400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 139552239 1250 139550989 139551019
    0x8060904060e070803070b0a0c050a0c0f061803021c0801090222060c1b0815091603080301061106040c0e091501120c12020f010f0e03030c030d060f03030c02 69
    0x740c80791040e40c100400f01c50310241e41c2e031400b0340c41e40c01403072069600112400c00150000700d50b00468812141d15500c40b0300d000420001501c2c04101e6034002e45002d0785007410300001403400c1c400c583c1c200e0040e00d00c503111400c0d1450300070320f45401400b42c0321600803a120764681c4150040c0000313064a190800150700d44070458150034600d01307147c1082d000d40a06950006007940c11103120b10419006056140f4910000411040d144500e80702d00d4035540d0081960742e51401d2850102908042d103141075441e2a0116811429504501e8106850307102c40040100300441c1c100d20341840304e110001c00340480c1d15107500d0701c21851046220340141d100c00e0000081e2145020b01448400301c605900c1e201c19961520000d820b603403007401c001c580d0f0f860380d070201294030482c242d5400d01c40340c4d0040000281485001c01107504603044403d8106100a000380d402d02940c040c4081c10520817000001d540310002003070914143da035298841c9510740c40006092002c00d5005006800d4150181c41d00b0100d00881 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 139553489 1250 139552239 139552241
    0x190312050d0e1516020a05120919030b0103020402070c09020a0e01020f150a02250f0314030c0304020d060b061b07060804050d05031f090c030c09050310050402030c03071d01080307030806090406 85
    0x5040c007c019001c0d00c6c180703010b1010410068031260600b581c01007003030380340d220400044442600002e41500c4401c0010001031030907030000c10900b48110000411399a84803008030507600181051004200030700201d04155904210044422000c1e00041c2407000c440550f600700800007031b00944003d5000500e030301d407107414031640a0320800c98a40610b41c2280b1401c091960401a0400302c0000340d1310b000c14682100c1c000244c0b40100b1150040790b20390746940d400c20036141c14841080b58221744842c40b4540c40d80c1c501019100518240200d070341000085100709040041c190081c10a0005400900000c200001401e07085441c080c1081030b52500c40d0341c60703d10420411030141006410100011424842c0e0f81c120b10460480360f1414480244000c4003915100014000c0c95090303031208480301c0790042c540c0c12094001c1d00140075100542c0b05100841e080004507044000350301c064034120405401030301011401011864003031401c218030380e61300418108015000386c0c840c7c03850402107403c1c0002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 139554739 1250 139553489 139553503
    0x50a1a090a140705130b09010f0e0103090b01120b09070303171008060106050a0e010e100c03030b040e030c0d030b01050a0f121a190e010302190312050d0e151602 71
    0x814000076140741c00800204241d024000f500e0b171038a120980001c03548600303802d480403000161201c1c0d240c01074200c01210b0318600c42c0003d030304042d2982d600801107114406003034041c18034404542081c0e500e07420900110040940002c0351036009007810404241c0c0500206000c130b450601d000300c292500d4075404c084032056040382c41e4900400000240c0e058005005151130300041d242c0070500401e040043d22074003410901c00390081003510950800c1440b4103040c503c0140b017820b001582c484000041012500c81c41c035801510740c80043c0003001480204a00c119406c002e04e410700c940700350203000a14500880800c04148981d407503820301041e0080c044001c090481c10020002840c4c0c00041408a15422550500503462800c103031441c0041c1056040507a40b41c0040d03008240d2940e400d00c5000e0104600400da0215240d1010000804c0322500c1c0510320740c0da598072910368450003103110403a83c074030740d0711560381d070003d100c074642107500c0400d6980c40306000100642818007440c090b070030003030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 139555989 1250 139554739 139554761
    0x5090f0105010902090f04051612020c030f0703080606030106171e040b0103030e030703080304080c19060501030b01090b0d1401020c0d02060114030a1a040f020a0308070204050a1a090a 81
    0x100302000403c042d401079024040d00b00d411110b043d200c03140c030428403007101c0083d100c40030529041c0e4542c0d114039018a0340210008500307400103181c0030481c080d060660304600d2030022420000a81d2006166001c5207041d0481030445146107194540000540ba0301800c01700620000103100004040c80c40b04100040180c00361a8403e83c0d602e020b107044400c03510240011070101e480c17058002c0305428002000c0064039801180c0524544803074a61103a41d404c56800c0c3c3c030b2103100e0324140821070812602d400d81032510422012440c0c0d411487c040c0314402d0140c018214882c0380c4100c004030781e039420f003040b04516004082001034031401461103019120b60007510002e840b50307070070f4500c21550000703401d030480b0a802003042c0c001d0010b80416403507090b8000003410864400340510072408641d80c2031038029100e020b0118106034240e01080341c503420b80d071055502943c0814070905500301401307523503804100080c007000303411003400b480702e00303003800011041c007840c4080e000810b14020381e40010031440d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 139557239 1250 139555989 139555991
    0x30201020403080a03150801060501050a2003070309030302060f0606160303060e2802031303300f0e010e0607050706060509010f050102100204030c0b0a02150906070207230405090f01 80
    0x10003440740500a4840381201d00c6e800481c0e142c0029038010184112415104169213440c500b802d003c200f21005051002d20150000f004407098001075030810090283e070784079403205000180b035810013a0505400034500c108010404d03003000100d0341c078042120000c003c0105001800000c90404a000709030a4004100502002060005982100a2242c14072030000c01d02d003010158100316509a001c295000248030082200d082e0000c1c0c041e000308460008441d4440715500c003540ca82c4270780306450941c00061140d5522107200324044500411941941c2c540080c440401032052240e0b403011f0003006a410000d0101e103100070404030342c000c0c41c0103003001040084a942c641c020f44449071118801c9c00c3c0984101c42031413100d580f45000707503001c076504481412040c40c80c3c0038940e001d039401040ca010031030042d9a20409070f040001c15140c0221800c1d40140800d16000c507000c4d1a150454014840d41340268440031021034810b00c903802c041005075408600c44e161864203a01d80180c1c0320618200d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 139558489 1250 139557239 139557247
    0x120a1d0a24091d0c0708030a020d0606050910050a022b0e1c0204020a12050708011503020c0705240a02060f0a050c0d0b01050c01380306040f03020102040308 69
    0x44039452400309080301d01140840740104030080140c854094501c280c800000185061121220b0000c40701c1e5800521444490726200c400d5840340c1c084d038022101030710155070216007201540c11510a04024140d981042c40c9000c42000000d2207c25440d4103c004002c00020701000d0f9620a0003456071080400d5484603072504086043c000080e41402c101d000100c100d2141c080368070b051910548241a4021070419404403074080c172000c0d41c01091244140300c140d00d20f14090071a01c0c0301d00d5101c1c00c03403541c50007010350615a03094103030355241545508140c0180080040380601040c50000c407041110801d0150300445030503041340507040c504828064000c80d1102c2c1164020910034800e030303807280d0060016950a61040220340003034400070031107001441005d1441030315500040d12600c0c14140786003001c50b01c44655096906900505c2c0280d15004900c00c2020030701c1c9d01e0510901403154170305200c070700c07464086580c1d00e8008001418108845001d4814103000794112005140c000000342d0351 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 139559739 1250 139558489 139558499
    0x110711151605010e07060f0e0616051b0301050717040c0305030c100605061201060f090503010e0106060806031b010c0f0b0c0705100e06181009030c1202120a1d0a 71
    0x1440d000000e0a031143e50030100c40d03840c0c0c6000070801400780d034030b5070702c1c0d800d08000d462408031781400000c5041d90b004102042200c3c080746d82c0100e01c0030954821001007041850480e81500c101c04110722940c00390781404240a113240d0000d400960150400c0d8640c6103c1ea521306000030307a440140d20103440ca0000149290084c880410076411030040f44005020303583e658014481c607132160510080949606000500400c0d00c510740021400072945002c03100f05407103400003030840d600300d00c0d04600c9a40d079042c02c0014030741001341c140d8000350480c0074010303c030300d89a4803d42902803440e045040001041e103100400542d801e03032a80e2250864040703505490328180e00900d60303220402c00c0c2c0340c07032146e030905800d40030182c040c01d9400354000c030107840591a0240c0c14403101512120428031800b84006a0560040c60310818156501943c1c980c128901c503803c00780309000c081408a021500841000500085003034200c03007000040f854206034200d501d03503842e4070b40d00950780c04541c440421500055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 139560989 1250 139559739 139559767
    0x105030c0915070b060a170703080a030b03010c020d090501110607080601050d150f0b070c05041a13090308010510081506070b070c03020d0203180f010504050d08120a11071115 77
    0x200c17448060718016215501c0f00108140002d0740d84803414643c1c014007091000682d0400544002c00f49410081808440040001c0c2503810220410005033700c1030500851450b070050a1400406003824180301c4c030342c0b00c0d50f080c40d294070b80204007409001c0310501154181e40b2840031107130302d000b14050400140400e800703800b1072600c4030303c582c4020400200001c1140351070f9604503802c069003c5c082008480c5000c0c24030010304a1052000083e1b4268942d040c0292100ca0310000c061000e040000382c0c0310301c0c5280140c880b400680046025201c1190814411034000d505150042e14158140340b540168070001405442010001001466200300344162640c0080c5110001407094080e90306540d502c42c0220b070741703000f2050b012001e14802d02107840c0038206000e25100d580c5040c580246044e440c1d001256001e540060304607400c900028100c03048012094120340c0041c0030500a210902445040042e9800b51400c0a08500745aa080030456914900607032030070308400c48196110464003030405 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 139562239 1250 139560989 139560991
    0xf13151a0711010f0806040507090b0403150c0504150c0f081206030607030b0f09090109060204080604030e01020304062c030106080f190323040504020304080711030c0105030c0915070b 81
    0xd400301400c4022400560088071500340e00c0c0426035030004540e1b500001c020103804054141c0c4117016640c000403c11191040c01031020314019070390340c00b10080e01203540d41280d032005401820400140800d001070800c4c0d1000c3d0400c4039092600d03204084d02420002400c0d9808035008250340000500d40d08541d6004000a00c12030b03084080d5141a510740005070251041c1d640f42d035501c0943c0ea500300c480d03454000d01c590b80000c1840c00000700c6904a9036070031b08aa009401107905903200a0400c41015032025003040e404070207102850a0900e01701000d481100c4402d080314000e9490300c044109030326038015040448070014020701605642d0b0b040151241d0701c0410f065280c0c02090441440c100c2020780c0708020542c5503865440182e8044101040242c140201e00300c00401040005950355441c0003031402580a01c03440781d501c03042468401f0700c00d005c0e045550f0285c0c000d0604141986c1c1c02c01c09076640302c40ea80d404942d03598401c2c1c00280568224042e20b180e100700c0030a0005c18031407070800c15 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 139563489 1250 139562239 139562243
    0x9100e1309020a0504230103060501050a080a11010c02040f0c030218040b100804021903110108181b0d060501090603050d02030403050c010e040908030f040506060f13151a07 76
    0x21a10081803000d080c001e40340300e100007940110b4095010005410264810301c2c10540d1100c09035184400c0c1c014001181200f0382c01a6400da0711440140034528041c00000018281000201298401c0c0d0740c8602c26041928a40c1d07042c0304000c0114019500d0703c0e000303c001c1c03400341c0104210010310035501034000c0d08158643c1c900354640060b4110305081c28450000e041c04007e016291643d5847c3c001c603903140c0018401c0781c011000401110164240001031805141300707104400b510501c0e000010310305007008041c120495800b0588208100e0b001c1005036214480b2806c902402e05620013103001840704000c01005140b504000180036181e9501403010b40c0e200b50180d4a606000c10310407131f600d00445c000a4140e0b00020890100ca60003840010b406e03020182010410181549407950369400407150040c81c1c200d000e0801042040c2401120f6000f50100d4100181070100300c00726080c10b098110801c48156120341c00103000d980d06030703078100411443c01070710241c0b00188500825a0401b00701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 139564739 1250 139563489 139563499
    0x303100812090303070602030a0e06010b0307080705040302100f03061a1c11030a05040c050d0609060e06010b070204020c120307020715090501080c090a0302210f0a08071709100e 78
    0x911811098840102e58003040000d0095080040039220701d0000e52024013480603803692400c4404010380305101d06030007060040d49454582c42c19074009001c00100400500410034100004c0c00142c1c7e0740c04400036041054944038000d01181c1509500a101c25004138107800e05000d0145039031090701c4e00070311100c645458585800c0c071010031400c054a120f50b040411090007400040e030000450f60019600c40d000b1441d600006948402003107060a4840b01a20a152146400b409002c020300075520340045903002001290f14201040b01680100b660003845250000f4080c0d0301c07c80c041000380d8031461503400c1103959017030140c40070390703225181c0c443c140303801c0c0f21104081030407070050300f0000490308181c41d2200a03a0350740d40c85040940c070904100b680800640f03c04805615440314154403a02c0c4040c150a901c02181403091401d25041d00c00923280d405002c2500000300102e06030341e011a030111f20603002c046518002041405030b0030500d03401c21030060f508400030350b0040314010b00303020a481d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 139565989 1250 139564739 139564753
    0xc040e012c071e0909121d0603130507030b0f01080d08010b03010b0901020118030e0315130b18030a030510090b0a0b03102103030b0315060103090c0803031008 70
    0x71021402150740c20241c0c001a104001c00c4446148864040c04401c4812038500c0d12080c202c0120349880205443d100558a02e8031440e640010890209480289034064000b0150000071070a01c4000d00301c2c036000d03852811410810804000b00c60145610800040180c5020b0803484e1807141c00b4412603480344690719643c0c1e44a070050f001c4074140ca004040d4a07203036a00b032500310380302da500c5042514119980d41c060111b1205100d20f60708041446aa03440d0304150168007010300e88095000c508a07614184001e00000072154400c0502d000d5000c000c40384165a10805c0b146551884030315200306000c000b030b09041003589039210b01d1280101540000c40340e500d42221344100c07080144045c2e00080420414001000e400e405941d0200200301c00ca000076440340a103070500da900210301386c545903180808004254242c0500450b0b01000d500401e0401d0003000913000ca414050072803818107a44824050a000c5041c5060300601003c030110703644c9003081d000801ca180360701e1040e8901030007044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 139567239 1250 139565989 139566041
    0x1812150c0c0607140f130801060807120605040615030b071b0b040213110c0307050709050421030204051206041202030408100b03030d1506021605060412050c040e01 72
    0x40960700c4502015008001c5540c1d1540306444074489561007001c600c405000c2802c24015000003130182a02c2c148a101c038140c5441001402e48500d44c112808030b030851001401a6030600f0140d0b03131420341006000c10703240c07070742d0030f0a000525981d1880b40a5868800002c4181f003500d0314440e008402d942e0307400c4020b200748410740e42a10280300004026004860101d005440d19400c0d240d00078210b184002420248403000c0401a404040b00010980000c10701a0a001d001c2c008440101941c031030902503403410340e0314500e18084209115200382c0d18001108513191003076041d10060f00002c1d028412549452203a580d4408040300c089650030011020055286c0c4080140c60880d82030000038883c0107140603903030703020b041d00010664152005101c2c0d081401000d0140011100c854050114400c0c2400402804c0001034860034100000442c001c00564988404481c2201c100705c0b8036111084030b600d0301130f06154292181780d902600380301c4000c0c3e0041040d880440307a010b6460b031040601c0001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 139568345 1106 139567239 139567261
    0x1e0914011b02300a02010e011109040e0d0e1c020306010b0417030a020304030b0c120c0c0c04140106031e060305100c05090a0b181215 59
    0x6030032500c0d00d80b41c041c0003410b00740035201070a850100c07050300000148507042070100d02c15540050714060941c400e5028020001c520030080c07000c449070b8500e100d1650803500d40760340310764238201c540394040c1070001d0308040082240e101e51100c030400c04204000110081000754207100511841c10050350700740500c5005e03001d050702e4603071214202456101c0b4040320b00a182c0c9998400c00c41c0405403500007094604880d403200d20702407241c2e6902c0c5100d045014001032004042c44c0700007401500110381010740b56140c15202160711940300f40c1c7c200f005850100400030050301c03180006001b07541c880d82102070801130300780d050301c0620400301105040b60910381c01070320f00e6088815481440522406407044440c014902036007820251000594080303c03e110700d02d00c0440010340f00c004071000e051009030024009059000d001400110540c980305490080d0b00d105d09141c001071015018 = true := by decide +kernel

theorem cover : BRFrame.Cov 139388489 139568345 := by
  have h0 := BRFrame.cov_init 139388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 139388489 ≤ n) (h2 : n < 139568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
