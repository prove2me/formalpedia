-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3747
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:50.885019+00:00
-- url     : https://prove2.me/submissions/1068e288-e249-4880-991a-b5c42af0634e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 673741007 ≤ n < 673920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 673742257 1250 673741007 673741009
    0x509070b030123130513030306050303090d031d03010c05041a0a2a052d06060105030601030e120403081201140a090246210b01051b03120106110604060209 68
    0x7008402c6440c1303c0261421040080150000c5e0f16001c81d0344c025101044155220030600d51a0b10400c0d605c66002405400141d0010340300c1c108500a500c0c18900c294042c550620002e401d5030130580c5184000b9501090a100d4414100c601d00765000320b56926501d01500002c01505c0c14841c450003006d2022610103a070010f4800940070300000b5401401d0351440084101c03400810b903091101b1030040c045d00804456084000103080e801124161101415592100b00441c0544640b19010582c0e00801d894581d81840c190301030400343d40700301d60321501c60004151001e6500016803002e445800082c517616810b45070842c0d160700740e841640000d07a44000c80d0000040e80b104041c08000c1686101c070121003041210203d0f824030013080800f00700e981d103220b40c2c02c9441407503c0e0080398001c12010710000004da21a401200301d081d040c10b0540c00d00800c80206000e03135062518128407034100141400c101c9070306603015405885142840811240440c61140d559400140300818090380001e102c005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 673743507 1250 673742257 673742269
    0x5060714120112031709060403030b010c032106030204020304061b02070f05040c1407060608160515090102120c0d02010c0c08120603030d06031407050d0215031906090509070b030123 80
    0x4807510b4980c0c1c1c404509040b12047d949403800c89064001a140052641e090762080e850600c46070b40540d1581c01c0c081e030b810103100e404107011080c1207200da039074040000141ca031130000e10704c01e500903540096000704142044440040710002281150080d60b0180110611200d4400580d602030354001124010400155600c400044902d081010089154800c10825800c180305991140054810200708a5905007420b00c1d14003c050744403c030501c5904072560180c0c0608410301c4144121104514010103001c6945d00400003402d1540103207890000701030302400f400c1c0f080291032800d0950359265071241c1e0703142d0040100b404c44c1d50f81510701103102c1c0c0d81c3c10025511001202c0008201341580d03850b00c01c1000706441086003031401030b003200240790300c2d040702c5880358103402600b4090781d00c5015420700c069520082c69203210f0f042c0c4481c1d000b9496028800d003400b401d43c0000000392820040507940c038004660348038100b101d03401c20042c23042a99003c0c00c0b02016002c1c1c480c2e155507044860010318 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 673744757 1250 673743507 673743527
    0xd050601021011212a070c03031e0203030f131b090e0f060405150c07061107300c03090801020c06100906050303090603150d0506071412011203 63
    0x11858102403e80344400d03540f00040400085010b012480488510302068000c10204c500b04040d514240b034580303a8801380c8080e25540305c8102c1880b0700d0a103e40d655031480c2440c2e50802d03400a603400551903d0201c04100c20101c00c030080c0010f40c1589000884000e6501004007182c034030020500e405010000c986010b18660035030408101035840e12000c480004040e80c0901261600c100900c40b1708110700894150b0007141c00c1805400d805c00001c50030f1448080c007034184507001004021301004164148142d04c0040030200005075a882d407810045040e00103040c4581200f003007030381d1840690322404031290b91002c590908401088880c2810340326083c199001d00c49550001613000d101e0100410203602c6000488402d00b60183c641500508440300342c003c441d0164020009140c0a02e01780e000340d50f01c00e4078101141125071411010413480c00a41c10111110b178030400c244240385401188050131081001d007000c3c1400d030500d0743d0709582c500601c5001400c200e0211401c1c10301d0300c610460383c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 673746007 1250 673744757 673744783
    0x70201112d071e0501050f1204060605011707090510020106091a0306100e0a050c0403050f1b010c08070b1b040f06200c040b04020d0f020405130e030d05060102 70
    0x4480e804101020341d180c4500c100d59196400340c9040415074100b48034454588010800d52240c10b00d0034100103403800e611209000205002c140300b4450365143c521505441944540c030042002441c200015040d40c0d204c40840c0c241081c1e220410509036070244060085a030204c0d52000440e020343d4040e0700500054000c051414144441804025460403596500703c206408854040c0d0b0794610240d840607240c01000030000106011035408040c0d80c104503002207401d0401e628141d9287d5035a843d040c0b01d0449002d440d000b404c3c85900c0c00405c6004e020310400c083c24100f40d2400590b6aa8400c1d2080620042c40000074001040100c0070600d00e5650041e4a0b602c0300d030703070340303488203038008620400d48903880000301000905441c06c605480c0071246510910300816003038401c1c00800002d08000c0018942056080c020f940303480200b0301511a15095000006030313074a00700410300189407401355a03080c0290400001d0060800c0000884854109880002800d5202e03000102d00346884504e00c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 673747257 1250 673746007 673746043
    0x30d0e01140403062c0a0609020a05060a0215160f120204030602160b1e0103020f3105010518011e080312090607171602030c01050f06120f0307020111 66
    0x3c000c00c10380390b100c1142140c2401c4107031107940703040300514401444880110b40a40144240344002012038000d1814248010560381c2030310349500c085509034100c4458040183c0c080b0000c0b07041503590420745a003100241692041c0e0746251100030708854181d2503404100a4111806810030320958140c40140d0340c408015035841c8070300a40e50902d01003841c0152010300280d0003050600800708041d002d03e081408400c841a8030350380030010403c80c5458002c1d042008900c107a5001c840ba00d521101e40b80014010344054086030400740106c1c0c05c1600414054403992110f492510b107e18000c5044030b002454658000d420a203040b03c101300142d00c07803901c0e84000300761070541100c0c030705506100e500c1c05000c5490076500c0c2c0300304450a13040341c1100110b5416006c04240d0350311102a0402c2c10102c5c80c0112840d08102000060031a0012500100740d480c841c028013100b0b250908040203280380540003400c041100c140010344a2003040030080c184284a00d807941402030070300c102d0035130404000003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 673748507 1250 673747257 673747259
    0x8060c0705070602150c0702040906050c04080c090f0c03070216030309061b0c05011d0d0f0c0602120d02130510020105070311040e0c07050a020307151409030d0e011404 74
    0x104048680144808503000c2c040e00c800803c2ea2840002d00d114485004001c86580b5180c0c01c3c0e1034a01d40d40829803e0340c01070b40325603d80010a0040c0503260007107502076800c56450789804c2c0c8041c2400c1008901c1d900c500000c03410f22020030f03010000c1603000801040d100355251a2950140d107445100700c00241b42c46d80e028000018190000d080c4821a4496240c85940820489610141c1c440107803008280100002d003d0016500c0703500e040410840c20318815000c08039241c00a951101504c00458443c01c503020020104501c80c80c101c0f00400303150000703007003003841070300c3c400486e024844048041641c04a00300b12100b00f80c030b408400422018216850304060307403200901911040380c2c007401080c2400c4501d00d8441400085808450380304468001d1070301d8041480d03050703500510041e600303032207488540d4015a606111030801400108400c034100c0356091070281209905900140d01c141c03040c0440829603c000c510803c3d55085450700b540d40e10140e20040e03580311644102225480c802042c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 673749757 1250 673748507 673748521
    0x1030b03061f06030e031909050604030f051902030601330201021b160e0406090515070f0216060c020a03061a0f0613030f080f030411040b01020a0203030f0a090806 72
    0x1549161102080c400c02ca8500d85890301034003aa0400d044c10b0741164410402444511408010744901804138680010f0302c42e6150000740c0b481d005070b001682e5807140744028004000e001c100c1001c0000c3d07140340b0180c4e6511540c00103501c0e80014460080c695000540c3c187d40e100305561202d1703403c8280d5a095080e1188004000c2c001e401007603402c1c0d182040c54064064400d0002001c0448041c2e25054940890504180d100071030740207001141d24503101e050000001c0d4045c0b0141504603103d8810402c0e42ca40741c2d00041c0400580c10041c4c06541002008509a102c4058404107540d907500b04408501c0e00c51001c1480100240c0c40a132003645402e80c5032a1820710b01040d1a080c01c8203d44043c503641c035040800899104400c0c00c40c0500103000700800020f040f135104120341602a9062700d013001010495a640360340704840446038510340060121040ca4644600740800740c00b840240303071060b0b096001c41d80e43c2c8241101c020840078003140c2c40205c10b02c501404000780c5034800a0700c2d26424200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 673751007 1250 673749757 673749781
    0x503060f010e1008060c0c030c07081f0501050a15050702030d030c020c0604081908120a06051302070203060c25080702032407031a06030f0114010302070f1101030b0306 74
    0x80070b070040d042c41e8500402c155041428540f4103480f000000b03840c1c10348a1094504907903014210005c0180070501c044002e1510900c005001030400c400540030343c08100d4500b114040506941c80800783c68500144082d4445411040c140c0b40210540101032a008005452034020f480b8001e505203d0b05c0341d81002e039941030b0461120060700780c0072901c8003207412080000b43d00450103024829070082082c3c082c002400b04504151502400038946000a800036000203081d003200d4503880c441e15100300304413a05141c41c400c404001c0100e021400c2c0440c80d40020f484000180c90759444040c0801c0c08403141603404402120700c056012804a0102c180c6484002ca8200c40c8042c0e01c64015040712142d140c64000070b14044020462a21003583e4450381d0070341c0240150889191203030014070b54554141c503504000e50050504034002c4403958034250300840082502c443c0c0780c0c1014014028840080c40010310f0001d003da2184407044002d40c40c1c2c004070010040c0c000d1082c4d05204036414010550600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 673752257 1250 673751007 673751009
    0x4020309010e0d0f02061f12030206100510050a080a0b12060402040c0801082e06240e0117041b0b0a031407050409050a0b0a1503200f0309070503060f01 67
    0x151094500c0f0500d000002d0311040001c001d00009604054000340f1441d1041d01c585282e1030740610098080c640300d03018200039910104085000d41d001c0740174444075010040c04070b4001c3c24120b07032210f4071900da1480105540500803500e0305000d80000443c0510029810880c6054005051f400354180c101c84404e54581040c0c500340d004500e4441110b0600d4031404c0030605840e00100200844181290810344560b4581410356011141480741c5584441a000760b20040c81d219401c001041904451200c2840b040d15820007403201e80401c0038160390b0048006c2200c01014491044c0d1556203040c40588071412000039003580806a0012804c0880807010349464140e82e43c00b00703c9100800307070b82d2040c0e620a035050808501e042c441000344035010381100750300c5408000c1c081040121100031a1015040c0e400407529003480c0b6440340c405070fa05204c0c0d8000301410b1602c1501c0411080e0607881d25110b19030000c40d002100100003115842d04001200040001404a0390186400ea003401040302c42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 673753507 1250 673752257 673752281
    0x8071206052e210803061c29071d010c0507080303070c14070e01210f11040f022d07080d06090e03070308071107180e010b0306090a0b060f0402030901 66
    0x4803410301ea0f04121101c1c0c140070119808608113103561900001c000c01c8441c801c407140f5842d9151558000090707441545410100e40a588000070609040c02c884082c550050540f020004c0c0392240140a8070341410550403150b0a02b032021000c052030078500c1c101031648c1c102c00020700c80002408007643d8010f245000550040041034034004501d001542c82d402940300b080042e40407840144010304e043d2060f19040920300707070440702d01e8250741d9900e00550600310041d6045803808035451120704140c05508920540c021045241c0f1b000d00c3d4401c40c02000542d425103200316591092540c0f04480e008680301542c00100180e16140320291000c003030b281c18003a02c2d4481e41083c0303070751003c80e90000c1900da00a81c035848910941d501c00000f121252003024280119102da990009000080c4e0a103028136031070202800720300585007443c03850945038884001e41c000ea00210802c02e252401081403000d040d40b2100c28001ca0301c4080020703c036025001c840b140d0003480003050184580c0158844014100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 673754757 1250 673753507 673753529
    0x4031a0105010201110a052203200405060d05150c0c151005060c060a0b150d050421020a140106090e1605030c0604030f1a090304060908071206052e 65
    0x34600017000d03034050103040801040b818000c40c141039401c03c1414080c59107140745200b106549440d0002610058085880040181a0040000d0615004d082d92280c010f0310414401e01d044e54030070b50781e0040040051120002c54000c5001e00c101e46003151081c0c0e11800c02c4955040e1580c415030b1060b0350690b01c6001e070b0402590001650b05040003655012440788000c4c00b0980da445d00b10364060450314900c20ba106110842240d80c00f48403034050000144a501c00040c0ca160905d0241c0c907840b6090040004600312103d00307040b2071f41c0001c1400000d5880584a030600034462141da0140259401a2240c1c0b0300b03040110b40523200010351001c155210003405507a542e50b800605890f00b81d4041c000c0d8000200f00000c2c004030344500a00f6015520595080c0749680b01d00e0703421201c1c00404d0b1003071144c40d0400202040301c140c2c40380e19000580b5030360001e0620303d454141e040c030300e00030020b03401003045842c1c03000101c02085070780003000200900b40d802110720004120190b10032407180101003000d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 673756007 1250 673754757 673754771
    0xa12170a090c170a0602030a020417120702060c03070606030b0402031b0a0605090a1a031f1d13050a0302030a03111e090d17070b0604141b04031a0105010201 69
    0x1240d0103501103041d044522102d0807410921000c0c580c1800c0c20034141d2511581c010310000800520003148220b050b40380c0143c0740d03428150003001090345400881130710741c0325903020030106081000312050b00d541102c109582e20b00c0009003034194003c800020b42040d00c0e000b000400d00030311b61030080c400c038800c44c192189072584c045034644d074013504000b154014004003070a0000034041e034001c03c40703401c008090b49819035669000440d031026000f08000350020100a1200210b030703007540742521280340504101d2031402d20f516110003000310700c0c2d41c440f100038502c0400c03280301074000310170440f41c0c0000a50301c40b028141000303545c1c0d81c0b0011103c4006468069400c00307240e40b1100340c0f04041c1034241800151010b0101304406034110612096010360000e12100001e081c603800714031044200c2c2c183d07944a213101c1c01c2400400034000c050500a83c108425130080700c220401c00356110741b91429011211107003440700070940c081d03504024218040c20950748030b080c0781071460368101e9100340e000740200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 673757257 1250 673756007 673756021
    0xc030e0607080c0a111e1c080402190e070f080a1509050408281707210e1e01051e15010c060f0203040201080612100e0a1217 55
    0x50102200c1820004080750003103440940c012005100480c402d1420f18a082c1d201c0c101d113810100d07a500d0800e541458410070031003d11b001d02540d840302161058414001401c00780280044030000d100038801c40b02150b0003254a00e1000e082c002524485d00554020700d00a40081c00103a045e5027030602190a00e00001c81140c5d440c01024040105590f4400078645031240e2013010700b4010b0000c445a810034403030191a041e4200314210300e00e00f040b205901404e0701f808041d11041141400ca42c102d6440d108100c150b903081088240c072214036182d04020b030004d0866610040aa0b203030307000024083c01070b6000348d40d1003d13141503280305400c000030010f54455011140340b01a0502d9601940c14805c0009081050050800340900c001814440300c1c8455a60300d1900301c561864658034440e80c00b1040c0401e659000c281141e0201040e00e46005806072104540d681d000540c1c0482041c81c0c80302e9001d8200c0e0020b004144280d035000c0748501c407800c0c144e00080d04080605181d0301d92100440f00003104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 673758507 1250 673757257 673757263
    0x1709010501061218020301090807060f0c051605070312090305070f0302010c080a030b1903140a20040b060c0a150908090f030c280f0308040e1906090c030e 68
    0x480b807032503d9a5070300a14070f040003006421640c0b20903074422408490103000d41c4081c0150850580301d0720103036594010358a44007049440404101c0c00040c0b910260204980e0030a0484000c0d28661800011a5440f4a8080c0c03400d00180c01c0100381180e0130302480c0e83c1e15000100703c0c05480c880d0060300c101300d490396060b9113031035114030001c0d0000380d40e000d1000c04506410020300840c40e071481c0204103078520a02041c5418045864030410160041c07040040c0140701c55001c550130404806020480d419459401e1101841c0c3c29104070025800280c2c0c2169407558019519880c01400b102e071203522502689484210741042900d04200440034032007211054854422001c2e4022a114281050041801941c00c55220440e801d17105541c10900c60b43c0d185208403409043c6141000100e001441107410850b20320340c080440c00f403d8520a20018150505072015610f030310420b11034544e201c071400d01c1c030740000000f01510940340c0303280451b040d1400d0300943c2c0e03030141648042c040c26200c201c0c00381d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 673759757 1250 673758507 673758509
    0xe010e030405150409090f030807020f0d121d01021305011b080a0908031315090e192706140603030706050901112a0f031902070f03031709010501 64
    0x48a4108000a12851070401c410b40c1c220062910080c0c03c0c55141c0284404031580301d403040e40d4156803158441c04040d40302058030742c82021440500440d201080207541c0d90035040c040d11050090070056502074542d42d600a03001c040e200e020311b40c1007503c15001d041c000c1d84560342051001450410101d031550040c0e4810700e8843c003902000c0c09090302c030307291688a608044e0040d010000762020006a1181c01c0000c0c150f00380704a01e16505407441c000340c42ea201400444031b141070040d024402c2201902074000580c1c041d8071104050001006110348900401d0a10080c220052001a844480300c8441914403c86480b940c400c100206c412100081400c80c01c54050750b2540c42000040006000c542209821100c08000420600c0b0540c03060a81500040455440c5071507861201d03011f03010081c50841031203079020180000c1d1006024003601c900c20700b0740802d801107100440003080c62007040400010241d040c2103000c0d95449290081c5100800c2407000381c900c4121001c03d003590300604c1158 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 673761007 1250 673759757 673759781
    0x610110a032723030c0a0603151a0d091a0f01140102010b06090409050723010306050411070f05030405060307031b0e010e042703090305160e041e240e01 67
    0x2168905207510440b0744403c06021941600991708070450740d880b21704580c400751245407000f150a000302100c006010440d64011070b0045a004075802240150404490260b05d0f00300000c41c180c50241072a1200c0b100c2c44061170b64452811081081c80620030248070f05940c020740c004545a40102c00480c2a24081010103a00c18000c01801c1101d103450741c0200c002c030b4811403d0f1031096030356000201650903060741c140f0000c0805c038452515507030726210f1100601003c450400104180c901010817070300680380d0003403040740141108010700c041081650020207004088950780d1600d00001009001c2042c0c0080b40c10010000444160380644164082c01c0d4042e542c100e03500380b40c00108400b411418241c03060100c4a2a07140c007076240d400c003007582d0b00e44c02512089242480e43c9005d03403500491180d6401c0081320401c0a1162203044022240c001ea0042010041022441d000300000c1d00401d00042240c551a00030442c40302000040780300d02c0b10040300400100d400403607010b00f44c0750716585003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 673762257 1250 673761007 673761029
    0x20a120615080a050d081504060303050a0e09040c141f0203040306060b030403080712020f1b0d080f0610050d0f0603020f0a03051009030e09010e040b060402120610110a0327 76
    0x34622035440340381400d47c080884911040010090808201110780a420a40018800103540b01009412114000d55001d090b41d46c00303040d1425490b4845100418050402e1000e20b00928003495500c1c0800c1c0e18801d07000f880c0e20354110a000790080e42d2503200784003c0322600d0400f100040d0405e80a0196403240b9096125000300780d48440d130403501070b600c1603100341109900348403204040c140d4401824000001c4170440c502000c51030a40c0d441c2c05042c6000d041007141c260204041d50855405440d00203500340d41074005500b13050b0b026513603030044000b00004946000b0b82d09481340c1883e00800c085034001d899429842c5214010f0121119081c007014089502c641e8000d03003500007940c840b0340c260b030103444c0c0419200d071803074002240a0800e81c4410f0701503131044248401d00450a0000b40c001c00c3c1210b0451500c1c1ca0001115810300307000f401580315240c0e0000079080c2c030f0b00412100240e2480d060607100104c0a0b03280c0070b4000c040a22907803c440e005284d09000303404c85503160f102507c00c0c841074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 673763507 1250 673762257 673762273
    0x6040207080912190303020d0615090e0705070f060504020f01050f0403140c09090714010903020904080a0c140a03020c030a02011b05030c010c0806041521020a120615080a05 76
    0x5201280c41000a940e80f00d116101c595440540d05210318603e840c031a6801585d00c44601c1d07110010b03241c1d50f800482d031952032118054803079a00b0001c03031011140b048201030810b540d02c140640d01c1d40103006020780076000c212501010030402e0703400b042c421807003240c0c01c000b0654940011103041c0a0340710080c540b9102000140041102c00403110818042c0c40126440c00c0084800700b600d00718191800794840d0700c4204180801202080c41c0c030500c0740b0a04c1c102800d02d00d141c0002d5403c20014001a0095030001805a111441400e13151009500520000400c59207910a01d9844001041c281c005024501000d450b604d40800c400301300c41c2d0140c2d04c51890021400549000941100d4229141e1004000303103148100203021f8042c00e650580c0303400700c03685000c6003804180d9440000480d548810164140809044660200000c503420f048800d20f80c42c082c404150704c03050982103a69a25003c07140301040285541050f1410281c1e255a0318000341d0f103508440d0f40b01000c000081c415002804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 673764757 1250 673763507 673763509
    0x515010315180f060b1c1a0705070f140d0504080304030b060d05070602010b0a0608041505070207180914030a0c02010503060f120a05070609050a0b0f071a0f060402070809 75
    0x31030740240210000395820425980d0fa802040c122500e4221041a10f071700c0701052601c0c09400b0900481d640c40e28100e84c800040c1d540a020943c1c060079074582c1140c5002003050140301c1c0090f0740005a001c20700882040c000d0038201112401e080f80040e0a01c0340c8041c0300c206500c20800e5030f0454500b41c00540c207180c2150360745c12a010b8000c03d00d0742c2044245150f5001700c0c2c02081414001c144c15000058141d039020103002070000c0c5038004030140329244050000080e800c11010f82d02070700140300000e4903207480308100d0030101302d80c6c0852103071b41074140d90011a05190303000d0140c45114002e4032003410b0ac1791a40783e89074001c0e030000001041c080d941e55409035000d10021640664010300100590b6031880010701002d2200c80c060080d5801002c1079030070400c0c100003a8000d098681450002039180038002141e54170103000e41c1c3d03c00000403580000b521098000c1c3c8181701d03406410442900000b42e0a11810740e0119003a01455102d003011602030700300340c8201d50429410805551030086064 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 673766007 1250 673764757 673764761
    0x40603150b0f0a0e06100c03080727080c03060a0c170403030b04110702100e100c1505010e07030b0405010303412a031c0b0a0b070515010315 62
    0x2280d456003118003a500104030b940c0d080300d0380004d004c41c3c4100400d9401c021082c005000c00c40700c800c1080c0a841c400800100340c121030325943c0704409107801a6110141c401015802007007801045503240990000700701c9901c041004c1803600003d034200c41c40c5a549142c40c0040d170762013102000208003904415800203544000c3c0a91250203402c02080154001e80414121507611500b910492000319214046103001d6104140c0601d075450f0409000c0307003520008601c038802519010030311442054a800300725409440030010740c820b0904100c40d60350b0f205c918921034012294040020314100d900d034924642841010b0580740c165a952400140c041c02d22500c000350071038071703030241e4103804504111450440c0b01e00c03c032151020034942d255800001711040101c41e041c44894228a8800e24900030f02d000400d8501d0020000d1070600300e1207036000654014403040c60441e41002d0402404140c1401d95401803d03030074860012078504da40740c0034103001403410078000205209410051945441026 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 673767257 1250 673766007 673766021
    0x4090b0f010c140c030a0f020301150b03150d050d080405120a020615061228050f04020f0d06110301060809030a02060610020f0114010e2a1b0a060504060b04060315 72
    0xc0f408a0f2004201d03080001c0c0381c00a0710004440207498102c1c541304504007801840b8451a08095080301c1504000c1c801d43c4601004011a42d4000c5042082d680e60760340416500190b50440d069404d0030100240040074541e0450782510a481007600c0806000342c50b03012034080c0c1c00b2039400362030703a9240c80e800c00c0308644034900d11076800380003440014160f2490451080c0070395005100701c40c815451304a50714a010441c1d14101149280c84200540701820f014802e03441a41243e400252100181c0024080f20b403003480503142d180b03407980484000700c04c80010341c140c0e402e40e283c9803450b694494060b540c0b4818526140c0c0107800c0000850000e0030b00500400c0181858016641e0303416400041a08456140c1c24a4500c0d1850380c004108605a200a00b60003000c0300d802241981c1c0c0d98548000c0003800c03290301c004012000104020b0603241c0c02e03158a40b060004061700c0c814591404c104002e81801c0d282070703d0300303450100d0740e8585240501c1035000b229400403120700e44241800c115001480d60b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 673768507 1250 673767257 673767293
    0x91e03060c170a050109051b070b040201050f120f060d020d0f02060435060708010b03130b0405010b040b09070e01111c17071d04020a020106150504090b0f010c 70
    0x800c0700d000c000d110b04074420600c0d140000365070340c9000d4441007912400341c501c20392000d98403225103100300c42e1030865850301d421800750700081d100d40c0f004807450310400940315602030300800d11070180000d0461050003900401584c00e05500d03039a080181054210200030b40c8480295003c00000e14491100220240000c000e9410b00341e54805040750110461403400380d02002c0042c0c0c100d0300046181c00ba01011300f140c0100740c030b4508000301030000c1ca010300481c0b442d0b6201000207007841c01c03240d0740d4112a035070000340744155040519061303020344003050030030380f1940c104030b01c48101d414100704c114460300156840340c004401c1000151030301e0403000b6200906020b08010000c0780d100300e0000e00510320081e955290400e140d000c0884c07007108040c00358002c021208440e5010380140ca61ba440001c0000c0f940141d0350b80ca48030302079004124a90207014040b0800c016050900e810030042c00480304480c40520000c01000c080000d0700c03101c0d81d1000c0c00b0584010900010545201c441c2d070001d44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 673769757 1250 673768507 673768517
    0x120b0a030201200f010b1302031611010b03120d1a1f17010806040b07210f02070b010b040503070807050303030a02071719030f09050c10050d0906050601091e03060c 72
    0xc3d180c0403282c204a000421007003c1da4580903400f00b02c2c2403807121032500d281d10410441c02d40c2058009140c550041e4070a038410801d41070a60810054290301c0106002c5c030040032505151a10740305403002e90803070a60403020914294009a2440c031101d0007400620700103006540f01f007810b2802020003180740300420300b0001014812000600d046940b28041c04103400100440e14003071429108001b0005c041c2e00811074135184c0300c0c070311401d1119007486044c2180008603401203040c0c2844d0003401243d1020f0841c0554000002c3d1045200380100165030064040c1c620b1b0300e4403004080da84441c140714242c0c00d5482040000c007070b41e00039406409010712846a0f0600a1411100c0e941c0d10b402580e5140c01001c14403108041c0c190b05032180010007200b8550034052020251201c6032581569400b190240c07074120140d40f61144600c5c111aa8000c1510041000ca0724030b0800e88014101110545c1c041a907c800200d005003017a040b00f601022140d0140304020f0450382c896015007001040542807103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 673771007 1250 673769757 673769807
    0x1c4407030e010f02070b0c0a09032306070c0c090b06070602070606030f030206220302060f0405100c0903020906010201060e240d060c140c121b010606020706120b0a030201 75
    0x100c0070301504940d14243c03603000d030721064036007019007480c60041e2808500f04030800c02a075965400645440450341c1104906100800c00300350410190418803100003140a210300300301800e0707017018101c0001e900804240c1005920b40d400442110b4042201c260f0180042c0b141000141058000b0f09095118081c04162950f480e07480010781c8002810031409a000745c020012241403540e0300002130310703480401c0c50b810174058a02a480c0d100162441c9a0007030400c0000d42400f0781000b420480000c40c1400700460310341c150005045500c0d60000f05d10036008034004c84c0f415881402910f060324803900d0484072075286c040c09540138045040b40c000c0903d01341c000320a265036440d0603c3c80c00c04d00075074002c5192001e110005019410800700b03460b0f80d0a041c810580300341703000108282e19808695520740c0d82c48900021980d00301440303080650647c00c020300420115404511101254841d4456420080f00041458213032460140700c0350b0800c811510410240d84103d940f034040550640341d01e1154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 673772257 1250 673771007 673771031
    0x20408030f0711030f06010e0f06060f090406030b01060c1a090618010b030d0309150e0c040c02010929090309130207061d06010f051905040e1c440703 66
    0x101c60405174a640d00210b00400003040300b070180b250b00490004100d541c40c035081c1d001400d0b03401000b00704904104040b0303038003005441d6903010300060340d00300c00c0d44036036980d4840c00140001c0265104440780000c5980100c0b1024000500038000c0751030b800549a1661008402e0000a40c00c1c4945401c41d0348501c100e5510341c070140403100c01d01c0034a80d0042004251030409a0f810504a42ea02020a16209040141c048049140c03030304034000301e5000c940110306e43c0d0101c0c050842441d015100007049001c600b02544908200202450f01035040c6000d41d0341d1500098890088498182e000308002c10410b00b1030640b40d0086c200584151400074184202820140d1000b40741d0105103800c1d0700c00d80c014048829030b0b8400400802d002c64070712643e0100c0803042040881c1034416140601d03210b4042c2008600700340580b5910388003881c3c0100101e0359031b10300101400340c0340300c002c046820301ca042d002d01d070016409036100300b81014105440b1303036070301d040110b260080080006007015660100d408074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 673773507 1250 673772257 673772263
    0x806070f020703080430020a090528050f100e01050603100905270a11060918150405010e01271b0e040606030203090601120609080a020f10020408030f071103 69
    0x1411924051a1b02106591402c030700c0528651074145025120355030b002c006a0b5041e002400b60381240f03401141503142c03102032013030307009603074000c0344548071030211404140b155607020900c41c6595200c0c4d03183e076450b10718400b010311041c2e0081c0901014104014030150410307800944e040320307162400058065507518218111601600c0002140c03000800d401249940d0501030f1100b12045c07000b40a00244c590b4441107801171000c00c85000f10701c04124400680d94200d038414007040b00b0b65843d134091030003500d02240180b502d154207108901d458000b06e401111060901c2c161404044000c1e5001c1600c01e40341c2c0039640c003149842c042501e4205544820305980030350101000161102102c03003000208100a4a81b50b400c000d00b01441402005189800015850304541130580720720700c16035031820041c0141441e000e0142444070005247d480a07540020040c2c1d0f0440e0810036146074190703081540069200d80c2c410154140e20512208400352040c500802006200d60380780f0a40000440210741 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 673774757 1250 673773507 673773509
    0x40206040f06050705060c090109031119180509060601080403120b10050d05010e07050a1809090809040b090c040611030903011401061b02010f1d150d11040806070f0207030804 77
    0x40f00482c0b400200b00080000c0c5410032410104503007444c107414002441b8403440d21018040c2d00ea121050191619015401c0a0858224400b1040f6a0305c0310400c12003082200d803664844c074a4000054186100441d030940203c0c0705070350300002500d0b03030744040301e4030201b05011009183e0740780820b0949549080b500300d400a04ea41b1810344aa0980c41d418007143c00c16840600280c0003d4200700d40d6a9000084a00a6100d03040100c1800c5200502140d000003603000803121a1608982405210720600170f4100d0b01c0302201d00b8842c00480308140001400142d03002c00d038461061206100e010700500d031018448001008590030158070b40c00003400e44109031b0f00341106989a07001401340c1a40150080908822001c64a28142c1700380d000030801c114480f080400c20083d8070b01c04014829007902d10b0318451004080c01c0408040044074001c561008148022040c40c00b104143c0e41510001500c0403902080080c1000f03a071001f10555401c02194590011801500c50110004d01601c01901c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 673776007 1250 673774757 673774769
    0x21003020d1b110c091308070c09020403080403020a05030c01092304150303020609030307090608071202120f1e0a09020301020c06010932070e0328060b0d02031203040206040f 77
    0x2020310a0103204281841207412a01340549662000c001016400c1035001078040d0f4050300940d238900c81ca05004046000603000405043d000107000001c0c4040017000e072080c0c0303000322401405c0b69918030416640e0380d10400320901042c3e50400c2005035203212000d940c40401004040c05803600d40a00180407980540c6019004030103400c0240300f41607040100a6000c42403400451541c1005000038029240c2482140d0801600c080040c81003807141400090020b2440002c1d034a40d0f124510f42c44c9562811030741c03ea0142c20100c00600d00c01010100d006003810001c007005c580382c4800703088901901604c1c8040e03070190340030001c0c60310f603080c02c0140c98000d1074807950014085d6103421b0f0104100115103001c40c4140c880800a1800e40c1c141d22205400c038241e4213101c41400c03040400309041000c010090075104000603100c0803203041011960200c184102e40c00c001240340c031401c101c7c1c60848003001a4155215046420f540e2134480015900a40014600f60400740e468940081d0010b80360460 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 673777257 1250 673776007 673776017
    0xa0e1e1503041209050607140a0f0614090c010c06020f0405062101090b010f1d0613061407030c030f030626060702071406210a05061903021003020d1b 66
    0x41400f50080c04010911498900042c0140c5032000051460007007010282483d07008102e460002c8000300a4040610343c0080301d03203105619410040c005142d0190250301290816000403401e0401050303112503510161a80c140c150021b841e504004d4100001104642c2c0e81000007007030703507900c080280c075810b100a01105140c41e66902c080d080e02c00d042e40281c81e41e504040000fa082e80e00004840d002c038642d031504040500c0c2a44000701140b21010b82d0130b4111400050784014040008405000d4400a0301c6410b070a00c1070711000500b5100d1a50b010740003031a010201c00c0001e21a0b8500d2107480350b1454085411616105091203141c212000145e80d2484070074000c864000c1480321303544c49050f038006040001d08c4c02d41451000e00600c2001803052a0009070390880308a0001004c10b46d005079032400000c1d140c14181d0000804040e00d00300e105400204401a180301d102000d0410307241c2c050541d0301c00959a80c403ea01a4200c107602c2100340b0703100c41100d81c083c90000c1c00801c0e40c030295950 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 673778507 1250 673777257 673777261
    0x2607171018020f01020c04050a020903070807050a03060b061306020703170c070504020d180c03050f061909111903020111010903020c0f0102151008060a020a0e1e1503 73
    0x50519000a0410031100181428101034005400c9001401c40503010740310780c041c051559004034200305135940102c2d4000e1034401807040d40241a4060a014081581129005501c0e074603072640d160310340d00c034250348032400700c0060000500c95000300100311000707042c207070504801d00c075000c40411454000c0350042c1d00c150020024052003510841c00d1400c03d03131950307140201005c00503445203103072300500303000c6c81c1c0011f941c2203406540c3e071104683d0a807580e92800c0a000034500144111405d00c401d135010702c92a036030001c1c42480420040d0103020301211800d1741d031048001610287c00a5070050324501e0a08080040d80d80390301c11010b5000101000c50040b05086200144c074a41350100080c1d401e03031510b56100f001940002e94603040044c00c480d10030303072050030100403840c1c0130003000c2c0c820452200f002807140522100d0350000542d00c0c600250f0322240e540034144401c82c01099482000a170726070b10144042c0c10f003003039400400400c0903124080c4000d400c001c641d141e03040c80d464081d00a40041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 673779757 1250 673778507 673778549
    0x1506230f0d0b04020d020f060a08160804080a180b13081c0203030a090203070506031f0605040b0906130807080304090e1612050a120504060207090509060609090307050a030f0215010f2607 82
    0x4984bc80401d20703052083c810b0900c0d03101c086080c09000b0800043c8075800102c041940002d0040000030304d04907019580c0c80b00545d9000384680c02c5403040c0d120714421006000c210040c080c41c58441003055900441c02e5540700280c0e003024050450050b43c041c0510311000c5802e85562008510890351000c05072007a80b08860166201045540041c04004041c80240700394802d801c00c803100803104854203904c42c2d0750b00441c180d01501d01d50001e2030324460518000b86050021000d0801c403807030380c03004100d00c0c1030141c5201d40b2040d0300a40078020546241041c481912022800c06100d801142100c07074840b525925080d6000050b00030001284002c0340402070f0507810400700014290b0200d092180d807c00b402640c0d81c9040c054103461260083d080050340c9040f08005890030035403c0700880e0705042039401e0181c15044035800442c0140a51100721140c002d11054113070480c1c0d0032103000400c2c01c2c0341603a51000b4450000d804030311900305070180016107004001e800041d1801042c1c21b26005a205 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 673781007 1250 673779757 673779781
    0x41e08070b1602150108060703020c010b0d0507030c0f033201092a0b1209030c0703030503100b180418140705010908060705071506230f0d0b04020d020f060a08 70
    0x1000c0c80c0410711440005201b001c41c00301d1007603007010b414240545c4550382400340c180540781e103469064001d010050380c0000e10100162207411a80140c054901c0300ea00c400c1c1d002003001c0c203404080d00418490000d075034483c580b00e10101800380a90755881c000b03d4458a40d42c2542d15400e0251528200c1100c4810030014000c515601301c51055000201c007803506851111600407841d848804410f00800210502e00a008a4880c0c002500944840139200e00d000f0700280c0041d544002c45228140c0085110880c0000b00e401c0d0f0080c2d28030695600b0920070800010304400c110410305103452141110006096184414000d4840c1c005004e229003403500040078031142d036100c00c800b544042c082c84030440c0c0100455503959004031900c007401e2584406c0710054407580d44903001004162480d070078843c2c0189800c098041046454000c1d03e0114010030041005070100074241c0d61548001c11700601d8001030b20003a05102600300038012018100042d00e5400c07a01507000810b95900400c012040c1325 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 673782257 1250 673781007 673781023
    0x2c0102010f0b0307090506010512040b010905010b0a080a0b0a05030304030b010306050624071b1502121e160203010617060a0c1b060605040e01020d050906041e08070b1602 75
    0x1400d0204005081ca07400255241107505c125058517030b50384086125644140119031344030402120004940c207062900081e184030910640004518100c004680020090308441c1c5640c5180d88120140e03d0350007000000f0b01030001c02c00d40c002040c0a0000d1903850a001800086000301c1040d0050342c5507042c00d800303643c00108654030032103032815014150b40f4404203400c1d10154010240f612002c042c6084007841094480803d60507045020001d0300031110040c00c010300c0200c0e420b9401d8081521000c0c051400740c4e5805903860007003146100180240c00b00901600035030b42402c4030360f008403500420300b1681190030026407541da00105203107041081008036000309409404001420260304010700010103024410030144003002481c1c14084190001b001400d0000c0c410440c2a17404100307076000394002d0341c2001075181443c0001f000d0310030100381c65100d00c1d049842d80a4030851422641c5c081c4812540884142d0403d00c01300e03000c1410a903000b0f1144410180c40c8200701c4820001038505244 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 673783507 1250 673782257 673782281
    0xb130203010e0c030a02070c030c150f0509150706090506011d06010807120905121e03061309030203040806100906121a060a0302150a140720012c010201 67
    0x40004208402500040550003c2407a01442d102d80300c500c071000c0030744501c0030b02404144202d807002c030610141c03401c5001151041aa001c4d0065000041917880941003044100410b03400d0123324501c0c00c01c3c0d201000e103e03021075039180c070300000340c3d483c802198210007050358540c2c809001884880da04c07000040b2210000f66061103a4070700040001c00b03842008080404116503049940c5404c401c0784c218000b290391140a544c1918442040300300160000c10b2041d00000c0c0c0102001300f00f0b9859802c0741e0090303001409050703100b40100315170006440485011002c40c8401c210000d03c0d80740612642d80601408442d1603c4c8030301e409580c400303483d102c3c0c0240c540c20805000c9140041c020094501a409002000b02910b0b078031507002031842c3da03d81d4006908901c1080c2017804551018004107103031440c90702e90845011915640c038605008001d0000c081c0d84030780446410301038030021641c000003014507000c4c0290711907404074500c0903000622000c00c04100c10815005680a02522040c009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 673784757 1250 673783507 673783511
    0x100e0706050c0a2904050a020405160c1b0b03090d020c011407030e06270a0602010e100906020f0f1e03070e060306060415120614060f0a1806030b13 65
    0x1a04030310300d980b80c050f40d0500030100488a002e07000c0c2e02c0c0e0040c105404540c16101e46401510b024240161159a550001c9110764941000599107064080c80d80c841703038180e641c540d100b00d042c41d6a6408040c1e220140c0c0440150901400504500c1d1030005611580c041c07401f40500c0020004060301d04500040e004e414801c416011490800500c03040c0c0f00345031f42514000130b01e02c40c4040030a04620035101c031021582650200018005502c0c031141842d04400c3d221982d0842e5116401c034201e41d44101c080499800071000440c0e0000c0320780010349824090000180307004407558409001d0790010301c5c410180940030851180c811f80003120210322480d640d103100c0c514078044000620103034100004501c00c4001101165641d1900d005031400f03002c0c07402011504102402002d88032028440d80c0e002c00fa0306240000c00c540c49404c0b140020098050b041034101011400d1000b03054201c41d002c1d00030401e0810300c0d034422640d04180798000307110b00e440014040c170342541841010341d400484805054 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 673786007 1250 673784757 673784767
    0x506060a0b0a18090e010b011103160b1e010f091b020d1103040503060a0222051509040b030604031214040f03050a0c08070c050a150804020f030f100e070605 69
    0x29140c40c003125104100c500c0d0070042040200040d880c90f001c940c1002259518081749408111415440154002d0090701c3d526203480d00680c0311a500e21941e410030308100604900300001030108140142c01c2600c045404640709000b520f07040c42480264407034a8820080d100030072107401e9512413021070036152183e1784c610700e02140001c0d40c1c0e40307801f040070810840fa00441031008182401640c4c040d29005055802505141080d9000b035001018110031040305056070841c1442605da010b0111200034110412030302217070855140e40d0b0800058550815150484180103580c10321840d0710492003919611240095528458211007180c0d083d250116a541c050002250840c6d0b07051400c01d40c03503e40705988217840c0408441308200e84000904444000c142e950402600c05080070964100340e035461081a80e0b9901000039800300481c14001c58140f6010a02504100000080104014040b03d40c6401040c96240ca02140814580d40c0b0b00e5903074081417101403040c00048000c081d203107416400c1c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 673787257 1250 673786007 673786019
    0xc0c01020d1d0c010903030f020f010e0c0a061b080304020d02090703050406060f0302010206190e06070e0114210907120503090f0904021e010207090212090d03060803072301050907030506060a 84
    0xe171031408041d003880b030140c11344400d8501c20818402504214070003401031045205e5110755401c90450f8481c13140d0003481001c6480c5104150440016002180341c0038240c034907131641d542560001e881641c00c005509001c40140c2c41e401410390080a40d9940082c081c6400d0034020221455500040d865027810030040016070303400140c00341c01000180e01002400605001180141150007541145016013010055807942119107940f0020084e00c803141c03030b071020380c10700c28443c416410401d0381301d4603c6003010101240b900001e0b60004146080700d40a54440144600c113514002044556a2001132032098504014000442c429025540e03203046050590000d40031904400c2d401d102c041e50074030b010980d40c4c42045050300519500c80c085590308507501d500c1650410899014003207100b00e12614604c14031902c2000100c44400d0095400e2206941d80d1090f80c10300810760350081039004a0601c0070715802e100f003d015220303980007859442c0c5945031140c10322a000300b045109403c3e0728410002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 673788507 1250 673787257 673787267
    0x40201080912090105130f080616020111070809010207050405010f0302030f0601050303030609130c060f0f020f1b0409061107021002121209030c070e011a210c0c01020d1d0c01 77
    0x500c4070242417803038881480450100781d4080d190300082c01e0171901500014801e4000c0341840c01155400c4036400740707441091090342a6007803008a4107402e542040204013040c0b0440107085044030502c10f40710010741e1640000d0590f4801e0704005100400306e5000c1045180030418442c00708034402c090f0085600d090002516404010070880c055031f400d40000b82c121a689545d20041584812102a92600c3e804c0c010711030415800c0c10350100d11150280300115000144030020b1403141d8000303007009002092400514240b800f505030b045502c03a200703240050224041c210781d2868000100e0f44411143c010080400c61107000001590000302015090b070445104440d110700c00150103a003107031565a40185984a0710042c030406010f20782e4003242812441900f14121584e40c07900501180f2400c1c00d0b03420720301c11144030342215210382d43c0d0501c2c4401c01100c0e81e0b034820620640d85c1d0401e00d10007000303400e9a200722200141c00e130799145075020350070110640c441d0111869000f07001d40d80c0d2900c0042d203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 673789757 1250 673788507 673788517
    0x80a020307050f06040801090f020907230c2d06010501140f07030e030f010c030b01050a0503011502010209060a08010302030d0e031005091606030b09072606011e0503040201080912 79
    0x202031603403c1c007050030f140c8420f41100d0017044058001c01100b981c6080c0ba030088070158100f00e00c580342100108071018414000d004000f4003a0840403040500441d0740c071102d40c014000c4c98083d0240540028200e114010303104800d0a4500361007080f212802d01c01030410805030041410302884902448000a0200603501c80c1e121a00909680b03580c0760505544d00e0941c2c10351031354075100d03860420940380b13012b4008115403c1e041e14140103510302c80c001520b072030242c06010303000103c0610040150308000301c00381c00302409500006140c807640b80042166540041103050103c0d640c5001007045041c1001001d000c1001440c151403852406d0000030f03103420294980d5110b89480f90042010020280580e140c2e1200c5041542c04030399603104050094024184c0843c840c80c00704000580d058082c8919603042d82410210012000c401e11a03181c0e0000040c28580c100014210740450150181003800c01c0b151141d1111502c91034a0720005051190003004010507421200d03100f014070100d442038070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 673791007 1250 673789757 673789759
    0x60420061b0f1e01360201092303120306062208151801050420150d0c200c10020703080703051b01112b050a02070218010608070e120609060907080a02030705 69
    0x1060140751b8001219001107613001540760740380c90610520304034101034407410440015016111070605852141c0c00743e002c01c0317031240d800070010003103c02c000e1100d0324a411000c001500c949041920b9204151602c4505010300c842241e449092280b43d910401140c00040f408070b0080c000c1c2d00d4180c1e128140d01c001c88100d00141c07003054400c1c0802d50b480c4000d0011180712001281c0c0c0f10403160351450003400303080340340d240450555140104a00000b5070494088080c5400a250104500003803010203600400c0600440c001c1010102c001001100189505402651417507181d50b04540b8001d0b1007000c11a108150b030307141000b079519481c1d4101c00d50703081d2003030448803001c21016100b0407806584480c011003c2d80b4502400c0144640c3c20f075000d003104a00948042e14107104903004d10b8070046007806500003241c0704100040d035151041600441285019154003658410000001d140a0f404e5a407110140c110700c0801c100d212040046000910313200c40140100261900820344501c0340303010b82 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 673792257 1250 673791007 673791101
    0x2a090504031e020c01030e2a0a0306140f060913080f160b150108100306271101020f03180f01020f0303010305060420061b0f1e01 57
    0x542407601603400141050a5070801c0403481014120080d10760103c00c9140740401c2c03601110b440000b00010301c03c0030103086003860302c1e0040b210410402564104010550307100900305004400202c850080000c2000141c040e0700320750800d02e01060849000518240c01003c043d010404001c500c00d10300342040350040071140e9114242d080d1040303d48609000341c00c1651043c8180f030100115030131502e101c1c4900300203c2a0141c0c0502c011070340104c040d54440d0410850403818008111030303030b003e0408074204005e5070132015802490072504070903502c815960b4060924103286556010f0220326400502c0324051440c0c4130b03081c000405603130424249540102d021301c0208200381d000300b129040d40094a0200d039204c2da075038903105a950204450803602c040c2c115000d1203050b02e00a480300c44483c001050f00d401d000c01821003507003505400d41112054840c20301c0300803401d071060008031a01260f0100011007082410462800d483e00800004501410040703e441c00172000c80714a803249900c0080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 673793507 1250 673792257 673792261
    0x9030203190320040315020406021c05160809030c0301051618051207060908071206050a09140a020102060c030f01030f031701090b040e1f0f061206092a0905 69
    0x101c00412000152005a1880c3c004a5080208890280045030700c41c4000e11074800080300c401c3c06a02076482484056881b047c46c1d11140c4a00d80303d0003940407440d2420609203004982c0103031948101250a031144400000c440c01c8a00342404902c1c0c0545060b03000b40038a04095007901820410a40800c1c10005081880c51410b09038100d210000c000007811004126100888282c82d050180300f5000811501400010704c0c0c3c0020400360116000e5002c050040130070340c0c03a01c001600c0000c100c030100c2550342d8400000102c60782c10805580683e4401490601414400a0303d4481d003d845054078074020700410070804a103100b190b05403580326070040040b074450714060710309041c2c40c3d4000043d4030980002140300b01041e400032180303c10858050000946201e80c1d1900c0318564030500000e054100d808041c1851640c100943d03e03c4120400210a40d4a0301c5428143c42d645a00721449074039090f07a8800d0241100c0307955281020710349900a04d405900e107955400701d0b5031007400c2800303403a100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 673794757 1250 673793507 673793557
    0x1e21011e1e06030209191407110706090302060319020d0e0303060a090209032e0f0504110402070507140d020604090203060a05060a050301091d06070207050108090309151b070b13060309030203 84
    0x10641040c21080100f90343e23030420303800140509140b04041c0103507200304040050000c2c882e8004400301c0317402a2181d469516403041a00034580000c01001c60a42c0800c602c00300002280710f4075031059600d9000c0c60f10f0f03041c114100f18400c0c03010390112903628018002e0016036540458400d48916180d1000e100d200380c0c10409a101c01d00e010141020300b0b2501706402c8005031240c0220307215034415103d40d40a140e401c2c08020488c00b603003001a1866100040c01c0c041d0783c0409000180028000303040449607002c582c0040e00561040e0000b80f5203035000b03c01c2c000d132401e121003000301603c4110740072418038025510017000c50205115506695442d603416403000d83d00e028007074081c01c6018003903900d1440c207801c0181d031324509841864001034030600041d00302e05001c801d45206000081012000700d082e64046039894106220902407080104860007103407104000d0305005040126040ea00c90038100383c02c0c000100b840e440f803400c1c1030600303448000181e80030045414034548940d16600a80c4d003c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 673796007 1250 673794757 673794761
    0x4060b06030103060213060c03320f0409050105030304050d080f0733050907060c080c150114010203090d06021c05070302091e21011e1e0603020919 65
    0x9110560000c0001001109004a5400815100e000b2090100c41ca070350f1440115483d14040d80060001040d40541c10700d00002e5040101070400c003038184000d201c3c802000110150b00146501c81c1000f0001801c00c100d820303d0041e14010101107000c2c1d400c03d4540400301d072071004611001084c4000000300488284c043d0310039140b0194010b2144200041100c0361400000695207a911640c8100c111402840d080d40c001c0c607100e40d10300f80107130400c44d1901000342c0380040c6500c4102c540302d906015004043c00100b003c030344c603540c10030392640003540350082da0580340d6070310008a0b0454008000c030b42d0064a4122103481036581c130400069944040a5001240300502412041c2050511050095880d07064015160340c7c00e085440340042450302500180d0b540ca0f0740c0c1c1254021107038120340701f296848005190b005841c1100007180501c2288180310020f01000742540495030368070f00403080880c00c0b00401c0c1c001c41d4003c17800c01c06507007180c0000300f44400081900c64444a4415904445070b859 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 673797257 1250 673796007 673796021
    0x50a121a19091a1b04090e03070501020c0601061205070917010212070e01030f09021e0120030a090602162619020f0d12050d0e1005070e0d0510050406 66
    0x7000040284000502d8194a1280c544002c880c1e041010000708280320030000100102c0c01001110500c3c003868850158003911480c500032025003c10700000000c00c81c04c1c0020005288004c000d0107041d8108200645800c056884000c525403402040042050300b0402480980300100440d220007000754029030b01a200d20707101640f0101d00740b003e110080b9004900013072201026241031144c08010913900c4d00b03c506903070009c0e41c01380c8031540c101d0500d850209a00c01e402d006141080084602c0213480040c0c5205d801d240303c040d0301c0040d110502903030061f040c00141038644060450a041100401701064850040a092900500355a5412254090781903031500c0c589080d22141003101c1c0094000b07481c510703000e9001d04002010340c0054503209445124181d40442840109080044111559000401c910b0310550382c03041d04400a0700104122030401b02ca4803000f0800d407810f4840200b501d1f0f0070300e41150203850103045820002e00b011440500d902054400024a5a41e40c14400042c3c550 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 673798507 1250 673797257 673797301
    0x2301050a170325051b1011120901030b0307061d01050301030320030d1a180603070b07060b090906090705011103040b0f040b070f050d05120115090306020310050a121a 73
    0x485c5034055007070700510200034505a0480d501c000320925610151544040798480601503040b040507030a140d001c1300042c1c40c1174034040c0740c00a5403501880100e880c10440d9000940440c0c082030704c19030070a00030780c002d00c0a224286020750841d40341d951b001c1e0030710075569880c0385003440ca54101842021f00b00203850b14502055024041c4441507900c0150110500041c540074135005255810214001d0b20014000c030400303801001c070781b03242c80c3c0d440c1200d8000c503c0450f081c0d5202d201281040c1c1d94044c4040c007600303101028100e00d050440c2d12501c0d1044551000703052050320041d070048400040144d90456900200f40c65031284142d000c54520305c51038200110321b41c0c0100300342d07003405031100c1921003c41c8648125030440c1d08441060f28035000e4046000b0010340083c0050120101c1c1d070004880f25070150038511000c1d40c480e580c0100b6608115098400e0702c40300c102c104031310300d048041c001c000e10940c000130190f80620740707550110442444203410b1603026800407400c0760410303800900203005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 673799757 1250 673798507 673798513
    0x50703031b0e0f040501060918060b190816080c0f090a0605040e0907050904080a0e0a1403010b0405010e070c02120d080130030809012301050a17032505 67
    0x500c0910150481c001603680c540243c07030003100c05242d410b0510030107050750b100d07446036403120f8030304030301066030500442021070000e48550b000900e84007138901801c203402003150000b0505441050040401000804051181c0590b0007154000e0340c0180b080340d00f18401c10b1245643d05150200307412030340300364180c03150003444081001a006a110b0090f0080d01c2c0400000740315911082000c5a4074045d6000d9164480ca900303020500080050000340000d442c3ca040c07040c0716410042c0080c0a0301c9107540462512880c21600e400e035880c0a11502d000118211810070003541041d26400340902c008141b203003030283e40c0007180c00351340d10081c0c602c902c1d00c0e880003150440c1d580103030001d1000c4002c3c070403c2240162185e034920004c050341c1102c14444100031071407410311042d4400f180c1210018000c80003a55803595070f0103101c0c50310300891000c22883c5040780c8072135242500b84100103240d03900000c15404052222202c0c00e0000c002c50314201030483c5035140c03518031101200041b0340e60329402000c0d48 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 673801007 1250 673799757 673799801
    0xf0302130e060306070c0b0726150f01020714040b040b1c06061a1e040b0c01021209011413170a020109023105101502070801060b0708070305070303 65
    0x9156018030074031514058040d140942c039485c0301640c8800c043c103c010001140c0c200080e0341c0034440d0805040c07491064503000020340c0840d9604002c42e4080d1031481c44122140c0c8810201e0810402d001c0ba0f1807001c5c80106100740c60304420124420340c00038a41d1155480e000040d000b591141c00c0383e128400c008090303240c04800d04088020041201c0c20498286040240c00900138000514455410440c40c44c0c003444c0c45400300348420551010141590114402d01c80800c2c4020490041c01700d01c0b0690000690741c0b00700035600700c50103400511041560b81403030445202060b007030311056001340403c420152410b0b25450021200008203003e8600301a01184480110741e05400c400301103030090b2842c1c1e5100c001040150002c2ca03103c0c0304d2100c1081e0700a41e28031400300684c0020341c00b0503025142c2c1a0300d5210700140b4054800c00c5591801a841114144120728081c0309040c001c149030321000f46400e41a51350340b20b0390b001c1d000001d000d004000c40c0a1092601035040f02000c5c0004400c0da1442c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 673802257 1250 673801007 673801019
    0x92d09050c0301060323070e03070f0b0702030708010c021e030d090602090f0d17091503040503040e3102040b0901080d0f14040e1905040b070e0d120f030213 69
    0x190024452013000904107800c01d442c240d0039840b0311000c810104031064181d40c68040070b86610340c1c0c080c0710341d0300b52040703a01c00100c0e804c0000f0100040c1c80404052651880180109460700fa40380d0858880350b45082d40d44001c0710b400080c030400500c03000781c1c1c064100440c2c0c82c90a041d409074041100346036003455401c00801226600401305050b0032503981c4489018a0140403801503001c0c0000d00d800ca000d101040b03030301640000b0700590000101500201103500300e20308900d410503182103034680d00120b0b05001c10640d00c841294403030710981c511b070303075005d29890354030350400900450386000089603002e2000d64807641c100320040341c0081c082100e2540d644000a585422540321080015003c0d041e40c03039214880c0c11200200901c21b84503500f410700f0800c111001c400e024054105d010308401b094030810030706010741e40c401e80c001e94404281c5e1420845c0541404070b0288160b1040329041c42d80000034070b030100f4846851a281c90711065102d5081c2060340284141c40490543c040000000558 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 673803507 1250 673802257 673802281
    0x10c0c06120f0e0a0201050c03090d060507030e060705041a04230406050a050a0504020a020a05061003021e01051209070b0c0321010b070f030c021206070e01092d0905 73
    0x51101503108124440c0d1142e925400c941c140c0c510640a60070004c14000550300c15030280c08500040c0c4184c9103004c44150000314a00b54030b40c0c1c201d41d81c3d503c5904100c001501441200d480504032405001c1919064070000c103a07110300c0c018200100260104000c00148060070380f0041e0001e01c0b240404140164440161403013607001d1144510704080002c103450070700310051000c8071000381143c00e03520304140c200b00180d000030b00d00c03504510680c0c0a100101c2d404005980c0a070914410152441d4103500601050042c05045c0400803189420895045d0360f211080b5003030720007609a03081e9a600c40401d0340d070501c0d0496210f2403064034041400c011000003c4020003050390390305200006510341c0c078403410b4001424411120095400c0c0110804110018007880d13586110340b41441d0340c02c58a80c001089050745012001c59541311204000c05960401800403e409003402c00100440c40c040300c029500c40140c60ba120481180c281403d0403004207044640070707150000c018400da19015805c001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 673804757 1250 673803507 673803527
    0x804091e0c090b0d0f0209040c1e02010203060f04050a11130e0901090507060f17010e09010b090402030d0f05040b180306070c08040e04150c0e1003150e06010c0c06 72
    0x481c0303000102824a4007a60728142120959200d060400d60b00e400008005c10140c0915100d044c0c0070840160035980341d00c5000c2d8040e8541d20390745500401051030840d1084030b00c2c0d4942c150380c810403e03c11030b0307a00e44804c80413020040b10003050720365410760384e00058040000030b916055408a91940c5072051410309800340c640c4030f1107419181e600c08d80324500ba00c00409010b00b040c0c001a40911615114103030300c45864080381400c40c10103019003500700301d2482c241c0c0810080301142d022710001800a01482e041c0c0b0504a500490a003081c2d00000d860384000c9000c1020300294013004007004d8001c00542d001044600903030764440c640304850a801c84641800c80e031003070082c940080c4450340540180c01c4220b81009645041c541841460b00c0488170240064032410080580c5901c8201a80100b0740c0c9240181d0303035642104800000e219400e1814010721092606204031807495010943d4040100c076548090306e00741da00c0341c00043e641035800c482c025014134500341c0d01240c40fa801c218404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 673806007 1250 673804757 673804811
    0x30708030a0e030601031e05070e100e280f2009010f0c0c0605090609280b071e022115010b0f3a14011a0412080409 51
    0x2002c42c810b2800c0503242d840900004208100d2078111041d46802003074240149442032046403581a126040c60807982c100b00d50008564000c80d03401d001405c000444c1a400c0350340d0000801103c90700000c03000c00c030001150840607160340c07060740f8454442d41d40c205000841c40d030448da01502c3c1c0b800025600b580d01ca1039146010842490703a0385051441050202002a00240320300b2005040c1441200c0c0b583c49601084c0d4450b01c180100c040903568890740d14512032001c550450110325070108400c04102c03640c00002e00b05030521854021900c181000e10101e0408151001d0800107403000800204600ca582d55003c260200c00d100054000509100000001c0c140d00020380e80c0c071020240f29200344a10740e524003c062041d412400c01161089409513082023822030400041c07080c0443c034407000042c1c40201e43e20b800c16142a0040000d00a0241140701114a01e00d0200042c1568a100342e205030540c59400d850ba002c18130200c8000e41c0c01a07d180c43c0180160381d0062090301c5040401d403418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 673807257 1250 673806007 673806017
    0x9011d0a170d0e030d0f09050a060210061e030b060a0b030408030702100207030e0d0c08010e0d1d03070b0d180303061d0402010e130207080409090309080105010b0313050c030708030a 80
    0x101610b58020305083c0448207006000f42446007580c3c008950802000031000c0c148038621901203542d50b140030851002d403019078001e1070541480091482580c495501491486041c98031440302c0c91590500c581c107607500714030480c0380ca840b160007186800b100c0d98001c080191020080c027007080600001540a0140c541c21102c0022140003041d04074410450000c010400032001c0358003030300306051000320b00340c01a10540d050310b54610485082d00d50b400348003038264000713506001300c1c42d410681c00324841813140180149030501ca00800d5172480075000f103080b000c001007420250486ca54000c505072000d40452264402e64926003d4090100b40c01140446406d00300032002e0b10241c01030b2540b1454051f514007400c01810024089003441c4826003580c2c00c0c0d0204104004622a80024070080c02c00403000201c0110b036007002052031115811120090f41045d004021803602d9000b96900144034104403100001640341052030040140d0340f00d6054002c0a400081c8102c0c0407000c0c0c4441c5e019900c0f2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 673808507 1250 673807257 673807273
    0x3240a080c09150f09040602070b040501050601030c020f2e1104030204050106230d090803041b0f0f052205191a0307031b0e090601060f0905030309011d0a17 69
    0x41c0c80c4403da42c0031030300d40e003100040d04144c10b9840c06000250b0064004e840c014a03101440d1548901c540c4111015a01a9101c03414030940707590620525044181c5440982000305070305a071030340c40c0c0ba405c080740700305010100c01041e081282040304505c01c8039010420442c500c1a16812121600140310036841a8a090000121540900401580440101100e102c82400c1021782440d68101d58805802c0a44da55000c40001d00900011070085004942065014600b203040b10780c2c44016800c401380b20703c403200c801c000303904035010300704240c0b0780450301c00071401d2400c0951022003442c6107005020038200000e126010302000c42042020300f40d07801c144500c201c4c140c0880411901c00c810030750158011801000403030001c07040d0702e84504020003001d80c00c60380c0e00820130780d5030001e40d00c40c1c955801c0740004000c0d86801c101c1c2410f046100e803d00e456147d1030302001985a0050b0318205051240600000181d1444001e1452820b80020400204903031110303248050310352900f10700c6400d8410a25 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 673809757 1250 673808507 673808521
    0xe07050a0821070515100504060b030a0c0c0f110d08030f0601090906080c061c06060f1206060c02210f0309031603020a17010b03030301031a0a050601020303240a080c09 74
    0x1c1142c4003150400010802212252454401740400400c00108820000c2d000303e46592540100e00040c46a2100203407681829501e040c119480c42401c4014043ca115640c00001c481001e1800c0360b68220140740182440d46000c2801100000400ed190810020030030828000c5c800d42075016420a90340c403130215444155180072035031a07004590441c0c0c080c0e101c0c802a03107031550051265030044540c500e031b0000000d20380829103040d50000c01c04248515071007004c256000c1c40303000e540614060248256484c0c04c40181090030383c40c1020303018403a40212200018038191100424518540840f4040400640c03080d881e90803041400344680210b024400e145856500b101040e80e4000f0460034150345054071000306080c01440c50b0019540b92460300b440d650741800614025800f0b450030400810407542c02002c0002c0c01824441098502000d200c9183d900000380e03603016010b081c3d400b030136a4024444010400d540080c1d55800142d01101082c030201c081582040c910b01921411102c0e182c0c18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 673811007 1250 673809757 673809823
    0x30f0f061e0e1f0c0306030807290c0703050304020d0b070806030c0909060c160c0f060e04051611030d1b08010608090a081803061302030708120d0e07050a08 69
    0x542000040f00c0e500c41d0101c0d50890760300c00390715400319080000340c030380d540c0d91100c00701d030820002901c1002e414020340881c161615002c1c081402d000208080524041d000741c40d1a005405010f020480e000c000541103403180c5124010807134007c440b1102c03030f00e02101c00402d0f541e4101c920703502034003510300040f110741040340b4100c0c0543e14641c09420a90344080c0980b06a03001015507600d00b03c4150320301800f0404a8003008003074000f501280011074203005000d4900c50f04094114083d51030407007003102504410903000d1180b022490800c0040c01c01400c4d40780386004584514620a203040c1da940010350340c103000c401b00021185c5422a0507a83e80c2c009070b030141411203010109420800040c0b00041401d030041c16110315807889400c1c070070a81c20100745070488c1254260710442c02d07145400d06600c0c08001d42401403100303000424682c4000c403214010780c02914816400a512924600135024090005101901000d00340b214095524400c2540e5411110002c40f8413890b01450000c41000c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 673812257 1250 673811007 673811023
    0x50105011d0603060d0f080307020318010903050606100e04020a020601080c03010c02060127060e18030406020a031b05010e1b04090b040f030908010606020102070302070f0f030f0f061e0e 82
    0xd242906540d604d40a02004034050002141d00c5502c00020000046040c400f03103002d000154000c0d901d4605d1034001040101c0b802e00c4e058184240420200002240021240d502c44000d444480483c2c00000301545c1c01d000104905902900228070708a11560024913241200d0489c000c440c0340d8840b440600d070880300c0c1c800c00b44c00107801c00c02c011701002d4000c0c00800c0300d03515242d50101400d00c0c16038485040310120f810a1840320134130001e00401d0038a034080c614184203008051807501d442c1031070107950303074103085c0d001024080440c4652592180026a2500c080c0e0000003e00440c6040c0a074691500e030700c00e8850258040702510400c4904251082c00e10351544121750352405c0e112900c0300551401c10140480802401e1400828004020b00541e4000c211540015850399010302d4003906140f01a0011200064448003c210300404000d04904581e003080502258102c1c5003070501103a0b0503404098813031420500400c07512103c40031245036484200f0410800c10f1681002c2584540030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 673813507 1250 673812257 673812259
    0x61509090501031a0718090c2c01030b010c020306070203091201050f0106031107060c02071505090915060c0328031e05090c090108010f141603051018050105011d 71
    0x9100100507210042c1088242c0041180c10140081c0400440131360300c0c82042d070021900b0701d4440c23202c81c2110760840611703003c040c5690513620800d000c219030101d012106c041035038101600d032501c101059002c0c01840c4815600030703090320f42c1c0d4070308450069500c2c0d00c80b0344440e01406418600e003840b6001072080e180207407152100f21426900c0c0810450141c00320000c0354801c01030820030140001d0f410f101b40300c290b91240c0c02810000c1d280c0b10405a04604180840c0c0a22104011204065481d6615140d0010001169440551429011030024010032007188582d03c0f0000d5501d141d00003401c0170880101c503180801c0031030b5030240c1d022001d0b81d2031055200100c002c0c1580d81c0000701d515802550340003d901084564000ea01c03c0002c070410002e0744007401a9644188500c3c2c0f4581600819040d584580c0075120f82d030424014150f5021418641e8108040e65900800c0c041010f1140e0000200080761480f10059400c0340303a400204001c1c8140f501040300c2d207110800807440c981b421019400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 673814757 1250 673813507 673813523
    0x304140a1206111b0d0813050c060f07080c1b04141503030c0d0806090105030c030a060207050c09011509090b011b02030f0a12030c0e0915120106150909050103 70
    0x4059039640001d45507010a4003510b650a0110b9032244914480004c600b0f61810010030346681c4c1c050000d07164040140041042101000307045010840c0041c0c01401032100340d5003941c1d01c0000361491800350003048030080551000007000303170344080002035004d03694007101c0340c148400b9007920400048030420340c003564101c3d1980000581c480c0c3d0340c07801031f941c620001c0c080d02d10380000300c4401402c01c1028241100840e03104c0301800224104007071920b0142030150001c01c1d17072004140009580312005030b4021b04994000032903404004050102c1c68421002400040207561508003504150346419000c10024043d00c00c002141e80060040800d50710303068464a080e0101c0c40c2c1c0e5440c80f8203e00c41c0a982510480031419800c140c1082a10103450095503940c0542195080080c1910492081b6004008024002064541e945c80f405508954400c421040031100c0030b012450b0818000e00c0303103450f940b800c2400508007624034035450b0241000e40d600310107561035506c00801c4400030702000e02611 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 673816007 1250 673814757 673814789
    0x8010f2603094f0b04090804080d090f080303010506030703060819060e0c0a090b010c0c090506030f07030203100e150c0a141903050405070b07050a02040b010302092b080c0304140a 79
    0x907003d40e22100301c01d500a0400f28401e05281c450190640c01a070000a044c2d0241d0400c010503588444000003410000001e00d460500c3c04103c290340340018010356210320070000126580754002d6004000a099210a80e4400169843c1e41c540005040034151901810485004074016000c1440303800004010050740500b17080500306002000907451460601c000d204050021540070720322000100002c040203d050720f032860501d402c2450b501d0701103529910488040c4016a40420401d6103c2c0b40326100241e8569100e106514207da0034407001103400e480400d201c00741222400030492840710740c0b29a81c4401581a50352014490b600e0907c121481c000d030362540c410b22035000305420600a10480c2c02d0552a00300040031075008403801c455651003040c0c20070841c1420702070420b0313040003400e0071401d000b000e0020400c4000e02c6c1e0170b0090684064130320800c40b0300f0741808a103410341d000121039848901322146565a030740540240c00210301d088070000c1c00d9103440d41e5a141911203041d0f03810490 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 673817257 1250 673816007 673816159
    0xc0d051303090b0d02070501060902030a060f060503010b0708160308060306134d010201111c050a110a02010501051903020a0312030603080c0a0308010f260309 70
    0x15070130511100000c00d80820050011401c2401203034040d00c0c4c0c0c0c150040e583d040940d200740c01c481442d400060202d01032001040025001801e036811100400c140c26500d0b082c9252400881c8140c010000c3c0d001c50101801c020300d40e005c00a503118000550440700306889406110300b000003140c90060010b50805028207442155540c0404180e508901e4104ae0310911140d0030400c0c100440455840c0d00040050015981d090040600c01d00e001000c0c0c91414503480c0140000c1d4400c184185902c50311000411110011039010003c400441c0300c200341c0310411160000e010302420f110b0544600b0451003c101c04492038401d49045030350080101039490702d0740c3d170751b408291000d040030810b0555070300d000004140401c0003800c51501c160301800909219103400781441c10182c20030110700d10000030910440c1440c05441e28190941602e095034a5210101d05166209000100707410a4441068020342c0320040611007280004000000d54a02c1450011100d1642e0400000c0102090b201d12010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 673818507 1250 673817257 673817279
    0x3062b020607060204051005032409070f02120307030e0c0916081e0c0409050f07053a050115030203070509040506060d060308040807120f110a0e0c0d05130309 70
    0x2d0714410348015051650360800203003d44010420403000c110f00000300203001551010024034882400381107185800000d004c60340c1010018003072800d004210080c0550741d40204a02d4541c000ca804000b1358901d008980140607200d0b52100070428840d00c000002c562404110044c42010b0705141d03407800050748542110440d2029201e004500c00101810512030414407849103d00454000c99543d44d02e020701002c103c030f40c010051411041e015040c403d100d40c1c01001c880c5550010010b0b1a08000300c030341c5681304001456052000111440b030190350312180794109d40c2c101c1d03c070f540c1080e200f406d11003002d4098ac0700480c0c0180c00507500f000349215524090307204e03640040c0090906805d054441c0345441c1140d03030641041d03e4840c00400c003007200300e07010401c1c0d1014001d2b1441100c1e0b41030b03e03641c0b041204940550300900d607448500c440440382d2a0303c40d0307000052001c202ca040603801e150192030380e16409407070303290035150409002441e400c85005101c1031040e03040d594002040c0c507100712070745 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 673819757 1250 673818507 673818517
    0x518160e0a150810060804020d29090f0f070b03161205040b09010b060903060a050604200711041103062b0b09071505030a0203060301110f03062b0206 66
    0x50300200401010405801c424100301c2c1c00300880c3c5900f001801e10800120911000d603002c0d0f02007090071020040140c48040c001e0f0000c40d4401d04080c2000b801107018890b80c20032121145110003490200035000741d001400160030342d0441c00799146044050261074a4807994080c0c82e070b802d14200007281c4d140450360121900c00340d191400307221001440c4009003d071031b0300765001e40326041c18405002e2007281c28840d54100700811038609150658240100703444400c000c00090305c2c561b4070000a040e81d141c40e0402c04640c408a64003088a220103011416941c02064050300d658501d041e24051307078141445402e109142111010307007566110000c00440580c1603503844160300c0103000d45410043d015026165442c4505501010b514250000e585420f9a540c0f0904081c402d83d0108900603821004a0b604500006400341e501d60340c00700070901410810010100140700003890f20030b1441044095070207810119218800c540e031150b030a20b0b103d60701c511310011038100c3c009400010b1a202000340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 673821007 1250 673819757 673819759
    0x907082503020d0c050c060601110a06200301030f0c081b0f19090c0e031b010804110307061e02150106210e03070201080a06060f141306090518160e 65
    0x580380c4a184103c1900360345500d030a0801268000ca03200070101014401580d00c26030a10300074206038420360107184d9418007007101a042d030f07a460035100c49029580f0200341d620b0500c420510b0b0340f96500d29103032943d88550181a52000000030001c65070b01d4000c9010000300960321480360001e000d107030030404640e500c211490341c420300032a266109500e001c01d06030010202281c1c0012210b00b034180c082d144109404a95100e81c208050740035583c10032280180561000b071a090806a880b0318044aa0350340c803103800b80d414420750b980055000e91015121510b01c40c088007600c14410201c00607a0348010800245500c465158010312a1502c034121041d1144640c10700c42c0401d008c01040e00048801c280c1c00c42c031168100003030040030340d40c00c04600c0d074214400c0d0390100062450044003c2c14402c641d00213004200c030841d401d154841d4140c082da0b10380c041000307030303103120036074410018140c007100d445003c7c001c059880707400d40c0300080740b200c0c280310751300c82008107050700200d620440d020f1200e2031400d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 673822257 1250 673821007 673821011
    0x50c090a020c0729030105060301030f0203030f0d05240a170c060d090320100203060d0818120f120702010302040f090f06270b040605030109030e0907082503 69
    0x7800100c00100018002001c50204800d813810100b6480e040c4c10000f1214900f10902c204010080c80e1100d074100c0381100c1c0c1100c03d00049681d14030004c2d0a41c41407545000c801c034408540c40020506692001d40070742a140185120720150314801105101c0c3c48400a0b031280b007503081040284071940000c0343c0980303800709903081000001c000030800d0300070341d20007240c1680d202c074034000705078024068210b4038071106408071404400015041d0344a50740111101055004408902540c50310703041003031250360264000e43c0300c40d52450120003400080103400d1040a5240c030400030300c200401c84001b050251b1028040002e1032440343e0ba40d03680519400c90405600b000000380d40503642142001a24400c200402e8001d01046c0340d2090316480e410201745030f07003881c0708806407000c2100d0500701c1c0f281048001c5400a0840300083c000c1c044c03640300365015403e000280080640c080c001c40c801050441d0fa020094483d80003c80c4c00f140111400c0e88403d072454444e081105412842008501c224580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 673823507 1250 673822257 673822267
    0x20607032f1509010b0307090f061d0a1a18090f010c050301170c0901180615020d1d032d151503010c140c0a020a080606010207060903050c090a02 64
    0x10104000d01050400000d0b40082ea01d0280b03050500310001e410007114402030050b115940300081e241e000303a120341e032440c503070f59540d4460382ca5043c2c220800619484e130710420200800481d907102c40104580714507440c1d1034454113074043c150300c500b003c210100140c14103180c00752104140f0b81c100e0340a02181c0c420704c00c2400030700e0686003d0240c0240058103a81d1a500c03035142080c0003900400901e036102d402e4100256402c06921140a4281124400c1071400c1840804400748402030040389c11040403400c3d8030741072010a540000c0c068521070b0b020359505581c011924000c201c800a0650b225505800c0b11074000c3c0da10b441004141411006a111720603024240d51340c651501483c9000c50125004c10810001e603c44da00c0841c402c0d28200360020301a56040b100002c240b4000350441820441c0c01040c1043c00c81c100f00918004164090049940c00d516174900c10b42d01c6a01310b0b1000d0043c400c0c0175020403200d1113104000212540f0100600b110500e110400048405c020700b920b94003682030007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 673824757 1250 673823507 673823567
    0x11e05090a0912050a02100f0e0115060f08010302030d050a020f03041d0108030316050a02010905120d1b0206040201030c050904150806240d06020f07060b1c02060703 73
    0x120880c010324070814005410805840d1110b8910500c075210424040184a5100c11940100340c000103c0f51004000071545944d01c00d40000b0b102d0303001308101561030040891208001900030505442090f2540c40c504484d0200443d5401c40900000390540c00c440d44800589009a004c2c000c1c642450064a00b820103a00c0d08c0c9107140c100c3c5d0b028042040480301d10b5065042e0b10707d0361038090200c141c043c40c40e600d0402134120311844802841c030200400001c080d0b00c094800c4d4001d6482651290551300c0c3c4030301c8401000202d40000900c0645545007222450148840c010304180e0550180c000d0320055582d600158014617546400760b05101003040000251303540c42c400c03610002c2c0040c1e4550004c5040000f45850864007c00d2569244020485408403401c04031108424840c00ca407040149a103a02d801e00c040e00400101121800002c03640c4410004190012240340f0301c1502c1039101c4500345140c1c01d8056080d0075001c0d40081041014902091042080b61002000c190703005070214440c0c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 673826007 1250 673824757 673824769
    0x906180c210206070c0612020304020306150111010e03040f06020313030809060f0309030304050f0622050a0611181e0d050f07080a02090a05012111090a09030f020a030503011e05 78
    0x3074101c1d102c01714201c4c00d001442d007103403036529811600310f01107040d0300d019400b083d82da02003d0b01c4150380084c1180d450340c0d2684942100b8000b001010024003000d09100038a036501d402a006010300d0603201c880210345035100005a5005200d05412010241e140d80c0321078283c0e85c0800340391070704010108160340c2031825500c000c43c000d12030304004550700c1c036260800a081112300311980007640c0114042c007403082c1400c01c0241580c1442c2c8044c0c0d85010341072401070f180410b4004010011404d2221050101d500e000c05480410300c06241c02904c28070003c1002005100b5404002000b80011800e500f241024055800f040344244200c0f1603c05000d1088c629000c41640910080c3e170008840e40e045060000402da00084c1c181400e0089506241e401c111130110240d0050148500c0740c1c00c00305109903a40a0480d8201c00b0304404c541e404e24104c0000074104241e820340c082a540fa4107481481d1001809412054040d40d402c2e09690a0200d46551801c50810f04084c01c1a445000704d503654400e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 673827257 1250 673826007 673826017
    0x30f0a092301150f1a0c06040b01051f080c0d0e0f010b150306060301060305131a0106031a031e07080106180e06042d0503030403030906180c210206 65
    0x22004103121000141640c203407504800f079155400761004003080b10281e41c1007100296107804040c4200c4004c0340c40320a545001e04a0080014401c0320300740400c0c40002ea484c1c5059038015200c1a508004058079295403890040c18000000ca00100145100c10440c02030140d144c6000b1001c600403100016851030300726200d21790941e6944d1294142c0081c41c00000c4a164100580000350441c0750150006d0305a0105114400c18180c0744e80008204003416130740501c0c1580d0001d064400710020080201c9100024000c11000c2890400d0891301e140010b0b40011001d00010020b00300f00e85440d01e64151413842012000481c07103540320203d003594080c01034102600100030b1601d0300050108942d001d913844130041c0303225070708100c3c1440007040c07041035207100c6501d52002110900c450b07c24840910782e584030016203280804000c0c0000c1550681004008501441c0180500750303200c1004c8011010100d40141101280da2080101100418205080000c07588040c81e5400e2280c002c0364140d80710b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 673828507 1250 673827257 673827293
    0xc18240603091b04090c09050414070e070e010c350a0203190905010c030804020d02120102031f1202120c06040b0d050a0203011a0c0a12020d030e12030f0a09 69
    0x4144083d02c480d0b080c0c440c2c0150b843c00202d038288411642c941355800520094001d9400441e15031000400f0300c0904440454403207903540032194242ea9402040d8444c0005403400c90024540d4500b040896105250140030b0030b07007000d0302d400c40c0c3c0d40003165500045c3c100070041e803e151146101c00318546240300542201d6a03240c000c3d55075601c1400001084804c000206401e0082d8980184026680f0a40803484150300d402c1140d40e0303803100c0c0000742a00250741e5009500c40c0b000c150208150703034190051401608049046000424041c040c06288a424082c20403c070401c0012100503107400d000c6010180110001d0740c0781080801d001c02c40680c01a04040c0b200d050002d008568120541709595011155032421421941800303041c0d0404201d103401b103d981c0101144115850b0070501684d21165072002c8429603c40c4554006903c4001c0e5140c2d64001c20f16200701d21700003843c040b4090020410100c0064034580d02e0a05c5101c0010000d844c0c0084250340b294000c0004200c1115151940b031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 673829757 1250 673828507 673828513
    0x14130f0903021207050d1214070504030b090604080f0a272301051602010203090a0e100b0405060304062003103201051c020414030c1824060309 63
    0x40c89040103850105a181d1007600341d002041038201080002c00c14001000c0c0524084001c82071411070f48014202a011240303196078a50b003480b008a80101c004c0040360320505212905036a81c4070210389070001114080c000071800c120507a408100c000c0184512a4103003084504061075040b82800e0502003114148484034010090202e24541650000c1c1c900344045005001180c10000800754010004485418160448440c046a00910a403074440c4c0028060386401980c07151181c0b41c4100540e07100420b01c0310000d010a0b500014011103060382c501030621071550b140e07643c5040040c10a4280d0b244501e00b0380007510368a8060350000c0d80100d10505982280c41d0038a0f04140c240e64000b0340060100700c100ca800c61110418071510321000c1c0090a00b0794481c03141c00d00c04010109002c0581e20600e20004001c00e136100d03902503015641c0c00540c02c0710503000ca65018000b09014000303032a4441c0107542c00140e0301d00300780c5100d031406403a000c0242c01455082404988240c10990744400990 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 673831007 1250 673829757 673829771
    0xa021b01050103112805060d0f02120106090f0509042d0809130b1c140d050c070b1e0d020d1a0306091603081b030a0c05151014130f 58
    0x111317041c400030004a481c0341542e400410307502001c6250240500c5042d01400c004103804601c2c0306260300c02c0c844015034001c107564800e5010303144105100e09025941c08601c02d49004a0600514034000e810303a00c0180c95404240c4890b1100c1035207401c0741c3c103c4444800703030105240408c104c0ca8041c8082500c41c0d40a940c0716103640c030030414044000410002c50600d01451003080d43c2e12000104442120b18071800060361840c10581038080001c91812018441d40010401c42c0c4c2c2d20000501600304000705559629480350b10004503441002000320b50300c102c03011072002802401004058072000607100600d04144001700c1d81c16103030100c62208264000304009181030030f09008903644a8070010192000034500c9140c00c10002c2c1c0b600002e010740702e000c19000050480607441001008486c812a5110340403004010b158424010003218240130f5240b40384000c202d00f041e818010958403403040740f07441c20b0085030341055282ea44c050764001003d180d582059020751141c2d066108400d030700421a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 673832257 1250 673831007 673831009
    0x280b03190b0c090904030c020a050910030501051b0307050f04050a120b0709080d0509030c031002030907060206011203110a021e011407080d240f0e16080a021b0105010311 75
    0x1c00180182201d2034104501c00d42c0b40e1311100c10303d03405689400e154040300170300e00110704a121190412a00544241c041c803420068201082c01202d200c2e400038003066440d811259107403800700d51140c50380c4d10140040b601050090700a08a0449103c0140d03045c40c1e50780b000941c6e0501302d130740588103921300302044500348052802d980c0d50040c2c0c0c070300300b1502d011328100410b507031a107800196104014003c2035004050b84d09002e0122025001070440d03500e07049205030000254019070704004d95208610300010b0040c00404c030103040f11543e03203001401700742c95203040d5030304005080c0240250088811440040e80d9442c0b4103100c2c01ca040c8010b00c00c0c44102d00024210580f1442401c110b410244942c1c00014120320445000320840380c030110358445e0903007447d8500040e080700c0440d900130324040401c0c0051100e01c284111142200d660020303484141c0840e40252084556900081c070700800141c3c4290a0b80003001400c100c41d07400078407030509158040c2120820780086038404202c001c01001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 673833507 1250 673832257 673832273
    0xd12030207200a141203040905180d020c0103050411031912230a020705060706240510180b131e0e0703090f060e0a020a0b03280b0319 59
    0x14000300084008440542c56000a0000f82d0034840d00004450300c1422403800d881c0e24240005405d8010101c940300e035296403106020300340803218a480c6540380d5081039101c01002500d86180402500640105550500110041c120003003080c2d8030740126010b40041e54a041200c0300324224041d130140b2940200b4a4108010701c1c4000b0000c0070030502580c20031000074000105410108645289907035402040c205a0400031691301c11684024041001c0e014071500e90810440c2c00d0003030001d11254201c0c8801070466100d03600072a03810800c401844001c09008030724054100c81881c84170907a00e51f071442d11841c254000517610300e190903400802c00014803510401c05032030020b540e68000003418801c041c032011a0003000c080c101901d41e5040c0c0d00b032024a0904401d8550010000e01001c10b001c2607a07370f0f80e0b00350048120f0059002c0c903000102c0c10603c0060341c0c042c00e80c50800c000001111900031b031a40c500007107110320250307841c42011001d580400c180c0401d89071401030814200c0c15814180d113 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 673834757 1250 673833507 673833533
    0xc0303090606261522050a230d17060d0f0c090609052203180f0b03090d0f02030307030b030c09040b10090b13110c01051825050f0d12030207 62
    0x120f80904041170004c980814662400081d80c1622101002c4056081003403411554000240070030102c550300c1004162000e011925014040d8115080380c80075044c101c440503800c0404204031421900803581728903103a1301d07480c03404c2d02401c902e0881c2d034003035107442006c04050390181c1807403641d4000400101c00d0768002c5951201c0c2150098244103100022000d003a06419402001c2103588a4103030340c0d180000c040480134007500210880710680352040c1c15800d52041d0b940300c456104611800701c040c0d100f40307410b864206569000c1e50446e210404181c1c041d24082c08101e5060040701400b009503103940c08078500ca98080c81d0255050300f0714640c0a511072110340c004656941c286049111203466003000071401420110001421203202e0403c1c030083d00800e0420308407035080400f84158950503039042812480e0764011703500803078941500038140c00c0742c01c841104540021101001145091031031000c01110103040f01c100f0f40350607906c00e46207001206501e0042176000c10002d0a1102046e00c0c94 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 673836007 1250 673834757 673834783
    0x41a070e03010b1203070305030714040b0d06090c1403090c180411091e060a1805061e330406021513110d020402090310050612030a0c030309060626 65
    0x8603c02d505400005d803244100c0d9406010b20500101003221203215a80746001041505080c0352156110001d8010a500a007002c840050402c4c0c40441d103540307284240704225000c1e403103074800c0c0d10300242240001d030002000d24116016840c0c0c038104a4440034181120408500ca40b82c1441c60140750048500c015001081d000e80c04601c2000440c0e03c0d489545510b151540941440540c2da0000044803240e4980284003240046110107801c0741f9541c211a0055400700e4146001002d2401000040341c10030100b950b004281c403201c695242c5d89050000714000058980300360b1200300c480200c2d1154419031001d00180d01c91000040a601040b186541245c40710a58500c140f003aa125080111010440140318401c0006017a0841d50389504807550340c803000e001c0c2d03030240503400016001840201c84442c01403600c049039500316240030046403610241c9441704880780b1901d80b0103c0042c1801c140484400c3d54924000c40c1107100410580307402e008030005e50780c0040716840b0160500e007080074a6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 673837257 1250 673836007 673836019
    0x1180204031205090409440706021305040204030b1e151c120e0f030106051012180b18150106110a0c0807082b0305041a070e03010b 58
    0x80c00040c28540c6007040c542c0b05480e10503264400f4000190050414000c0100765201112440c4152105105652080c86808a0501c1d9090703000798240d168240805d602182c0000030401500011401e40c0034041b010041a10720184988030404101241d006800c183d4228800004100d29000103400b14058688024080c0082c0c2c203007040a591900f2240c03060030b100b0300c80c10f403d56070081d0004000d411036035040800002900d25044003d00040710928805000306509131040400d0309050041034100c481c050044141c040c02c4035001c4441d8003036014542400c50b25054000c1a0805545850886030301401904081c0d040000b1503442110f0800400c6500303400107035644039581d01d802001411659903082060080001e031075218108050120b0081160002d03c00100d150800003c0b8031007601c18404c1203810070200c120071280e9911104282d0f500d12550940d000e05190700c02d80001d074100b40f140000b03c1040358841107129601904070703050000120000b07800d918500d024050118100c0e0103842d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 673838507 1250 673837257 673837259
    0x40602070315151502010b1008070e090108070603240311040f050906041106161412040e0c0f0f03150109170312040c23180f06010e01020708120301180204 68
    0x80c0741d00300489445039100d072410303e58613481c03c64002e40242040060050901071116164040a045101c09917030340070000b0b040c1c5070f2419241c200008500d069452002c02020100d20b0288210003030101198043c1d40c50000140b100304556a40c95541c010f14400c2a0750241852048284012260602c2c40c400e1000e007400184507d01e080496920b800a400c103680880000d60030021506512543c005218041902e141800c14082404078010354400f003d0700b0f441210480202c1da131181c0c02540100248640d540001c18401c030380031801002c0f06e0f912050b41d41c1c1418401401c0550a4008a568201d40c4c3d40801c8189101d6034400702120160613030700c8132030007454410400d05650f806a80200c08116841c0c0e40482c0c00d0040800c81c0070010211810803507000b040c00100d42040780e0038284410b01942c0d4280c2d042d0341701803a03550281d2041625200317004c0707150346980044400c90303030300c442d0281980540c48011a6030403083c01012112894030b400c5d103540354905840d0b20b00c0101402c000c00003031841400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 673839757 1250 673838507 673838531
    0x14040e040615270617150603012a1407060b0910060f030207080702031e0c0904030e0105070311030f0901140f0a050d0e030a1d0a0806010501050c1002040602070315 72
    0x480c0a80c58008038030314203080007525035880001d01c04c41e0002660901c001030341410260300005e07505824030303050818050a0300c07100281401d880c1d5000c0b0010140201c2207805035140000090388108448501d1311a48062906101e5034555020200c191000340c1c4a85d850308290a001110035001507410313082e45c1c03004e03240034002089140114014010542c0000d003070700900c080c2c44169032015400909803201c88403519250464003000c0402c0341554002c00740d1510451414049680c030454160710340500d01c000c0710b0b004540c241d020600803404e02403010311200b13443c0d2007000a8072181d04d0610420b956101c1620000d8a004411486655100d03c100b103c04032812104081d00e1b85044142007940c4c4991a851045002c3c1a4481924500344030105460a80c6903000103444424030111000324030609002c01445541d01c114028906d031540060010031644d48074100a180001000c8180c4610b09c6e40da440050607641301b40c1c42040180e109290920500060380600c20303010301c54840402c03078154058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 673841007 1250 673839757 673839779
    0x1909022d010801180c02010f0e060105030d05070206040308070204290a090501031e031101091506080109021014120c030601030e07080a080a09090f050109060f1a090114040e040615 79
    0x2a5000e03480e030b03449a04172000079000b50016030308008440014808986042c2c0e00355038642007449810b22034480c110318910924003440c200e640603038024000900e042e0a40e124212a40d0000360201e8200c1d6482107008850b0740c03445074a5500121403801d03c000f48a0b4401001381d410042d4109100e09450080100005102c0c40900442603818401c4400403035924201a203200c803c840c0d003500d2650801c50600104080001d9490351600100003c010454a50608a00701c0311010f00080d0007265001000752490b0003a203031042c01101005403185050035078400d032512108240c848904104010051203510742c0c250149200d0b06036510014038842d0720b403400081c0e581000d400081c10070701c000100c0001d0305225040c04000760503810342c180401101d14070f2100060a00f441840c8250303107171100214585552003003004c2150a8002c2d1081940025030355400e80b5072103114018144204072400c0035002c1062405880140750104140e000c5103005d05064042e9000090018503003902c403001406012140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 673842257 1250 673841007 673841039
    0xc0a0207030b0c070c060f030f0c1d060c030726031314240403030c030b010f030f020706060b1309060f031221022503081909022d010801 60
    0x10510346941911003081d001061310641c8406041d08100d030402055940d0816500e107095045503808001e40c514091044c41150aa0980301e40011240b4181d00726550b4024222046c115000300f205140c0304a40e00750a10307542c003000342142c8000f4990070000c1a0031019861a0b40012405500340c5545040e201021500e008003400801c802072810200c42c0c0071070200b191402e07500c2040c03000051044055680c0428000413541140080d080c1000c0200181c400d0164001034001a129503041600200041e005465154810700c4034603403d005900100300d030381c0102d800600b514040241c0c0c44080c1e01503d280800a6040804a82d050007010000c00400b030718003400b202d800c002020300000c00820119803043c0c0801880044060450301c00440440c141d0041c1021100701800d800c00c01202507120981c80c0042c0c42c00750100388080001140e4400901c0b8170f001c42c0d02c03032190014400509a0006101d0009400b6014800380c00c40102d00012001350b100c50508242400c00360301541c5807101c0d4407214130308 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 673843507 1250 673842257 673842263
    0x3171807090f0b060702101d030601061d01032915030a06030c12020f15121501020706020712060b0a12060b040b060c0a020126040807050c0901121212230c0a020703 72
    0x411060284000c3c043d230006004010700034103840e55540e45401c0103089030f0801000b03041803542c9403500c40071903000c1e100d00c29030041e01300d07409000210601d6010b003450200501094000804e0b400728500c4502c0040118411524010001001404d49c01c1c42105141107400001d441140300e0079080140c7d540c2e0f44e0880344040304403021000000b0040040140d8083d02245858407058a414440d0f01000001c0600c00201c003a8200d0348040c1d62407c040f0384e030b083c40d80716110504086420080c085052500060399548000c0c00b24602d1517540c480800c016000e2850940ea00c5a071070301204c1c800d00d414011180710405c121030390f60034a2860500381d83c0b40c01d851070713009060007509010107201009144500b4548a0811100d1103d4501802c02c42441d600010303048540d80641101c100752841c00f0312030241600c0a81260030881c46250381d030102d0b020800401c0a080c8100100f07901d00201b00341c092180e5800c031036000d580300c4103610382c00440380c3c80019061170840c001c1032081c1c041081e80001c9083c02c40303070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 673844757 1250 673843507 673843517
    0x504082d0f031009020c0705030d17060f0102120a02030306040c03051e0901110c150f011802031e090109060b013f090311070f0303171807090f0b06070210 68
    0x1a4014000f43c0080190f02241910b400403404c00c01d820360100d503440c11908d09800740c5050610421023121814110b615031800c50400c038020940508080c001d4554042042c01101c003020202c0304421101d800610400c00107900010400015060030701510320705000034241881181080d003100b8900c10300c000740d029806070124000800c030720000d404c20307403040b140b03da00c150750390f04020002526003030008c0492007801444d8010a40701203e071002039040725140700b0083c3e9920b0302103131107001a40c4098508040e00001e460b0708440e2070880c4c0e48940c000d6440d80000a000b40361441c1c02016180500349044c144130410b06069103240700703507010b44002c1d91141c0300418002c01080300186c04a102c0980042d806103000e00081c10107400c804401d08982001c2e08661144d50341c1c0d1b902d4030036904140001400518162a13030826013404410300f80d00510803801c0a9065115080660310300b05195109481d0346880d8101c4040044003841900f01107642901c01c6440e00c4010717000309001010310383d61170f81001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 673846007 1250 673844757 673844761
    0x12090804091a130b04050603210c031921150b0f0708040e0105120304140405040212120301061107260a0c030b06090919021507060504082d0f03 63
    0x841a078460300709242c0010021091541034203070f404001c00c001c10105001d140740101041103803030009010a00001a881410035510301c40321000b461380c0004012051600c4203014888030314111002004080d001036440000c98089400b660340c41074a0745040d00d60491800030000001c494158000c0c00341c4020702c503003580e643d111640c40ca05a2181060140400d07030049400b080015400d4407440c105d600480300c12b0307040800c0558607074482c440c03031103103031a007052404440c07040d810130350404c80d800741c001403488910301c500f80e50440c103118150164003502c040010051000e5900030210f182010b1810000300807e07410007208401481c00201403641c0300e0b0507201214280304041050070411584568a20b02042d540e01d030103400c41c0420384910344a181c4403400035030070042c0064a420070955200c843d00b2070340b40b56024010710b0149903159400801d41000980c000c2189801400d000e240301d2032000b940d6020220b548205604085030407402c000b1200021100450070a080d6004902c00f000c520395a5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 673847257 1250 673846007 673846031
    0x90906060a090308030c071b0f140a030204021b010e120405091519230d0b04061d070905090f0303040b072c030d0302090a0902091318031209080409 65
    0xb24646900060410800104004020509102400e043c2c2e1044000100c0c0240580c14403107001c540740101e9540110140042001d5641107121841e0140081c01d886007003502c3c3d401040c2030740d010341000707a021000b1010640007141c00341700f81068a400341010f4681000440d10b5440940326034428140700c0e652000100e080404080e900300e159940050545880c2c1201c50080c078050780c03092040e01d103950141c01c0d000011642c407007408006d212004101c1c00d0649015500c1484058010340305a4416030340c1d1441802441e00c0101c01c0c3d1070010f480000740701c020300d031006d281c090310b400810110442e002494020000c2c200001542e80150744003100810030f9030340b2201101c848000300004000200803807913508280c0c000003030085040700240d081d11041c00310f401e0140d00364810760448503040040b00b98204480c0400d5400340640d01c00040c0380c06110380708500460182d9100c00910304400828107e01400c064024117100c2121303042101c140074030101e5441c0d0302058040e038070617462095296820440c1c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 673848507 1250 673847257 673847267
    0xe01140f1c0f050906010e0a05010e130f08040611300d0e030a1707020604030f0f0e1f020f012702060c060702160b041a0a051201150e06090906060a 65
    0xd08003050030b00300518545100040e5a449084c89880181103100000c608061081d001d4a81a68403107500e661040e01c405006c04c040c2050b0210079180e00004a0050340041c1c2d94200400050810340da50311150100c8900035820284101000b11031119280c10002c22071580c10001404041c00e40f4900351208000c8440001404101403882e1542c000081c14200c8190044010f02e03050700b90402c0b80880d5540c43d2400c1c0c0e43d61070b050b113015001c83c4a00d40004180c6104400202c0080294600354502a540e04040343c0c06001d0910304224101d2a040e1207a1081e81c100032407440d01400300004c1c04144003010540036965410341c07100020050046160b019504c503401150001d41c00b440464941b440e00003030080d02c0e03010748101203101c003a9080d030006203540500227540c00d58000701d030030410700450400c2000f110f5002c08944000d1100900003d0006280d496045000300040f04040c007840150b0309000748041c0d1129071061247c9400d01c0304005545490950503880b074426120140c0d1000a03800c1a20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 673849757 1250 673848507 673848521
    0x6030b0f041404080903031e0d0c08040f1203020d020304080415020303132334051f020f0f0619140402090c162a03031d18070e01140f1c 60
    0x10345d41408d42c1e0030a4a44000042c249841200010040411382c46021200004140d42c051300401aa503980c0c00071450300c40c50107000d403055040040c640520f00c00745100727980046070180d0740c1d064003003010490130b88410001000c40c1c0b102c5c4041c41c99450300c6410007280341d0f0b0300d98024200d0080f0703201c0a024122115801400b03090580c00701d46296250b001e450586007100600240d0314402e40070003a03010f0030403800303110544800901a400c3e440d00300b064160691880f81c00c3d04214400c1d1003000c8a548000e01c14185035100718030281c16540352016460528202c00750b01099420301c0c208103140c900070404002b0340c01c0f90341140d50280c107442d407940000440c007812000c01c10700101648204200702c040e195960b0300100681c075294004c0b0368955440c0314888144005030201e00b101040004501c0c0f80c0c3c00c41030304208001c00c0522500306042c201001d0420480310180855000000000c4540c0c001150b203692000130704080b460080c150300c1100c0c40f8021003c0034085006921030859a0841542210f8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 673851007 1250 673849757 673849777
    0x307020603131202030a0e060d14040b070e0d080a0507021519031a0108040209132f240a03020f0a030c1d03120a020a050706030b0f04140408090303 65
    0x390300c9080010340418200c1c031090044031800341e10900000050b0010058030505541c54035031030518040f000c1400561b51021404507010385e560180c51010401203407206025600400880c0b001e49031480700604a03005030021113104264284440d0001014001150003030900c1d45803054a51580e440491200d6408601c50070080c074011030040c0d508031004844a14403081d5503400e110b80107c01148031581c110300110140040d5540c80002c015040c0b0b00741d101d40140f01c00306c00a00c0401d03c5d07190503094030317050181c00e00c1e41e62441e645a1914410748008242380c0c03a003103400c1d50114640041407600301090050a1108000c0801c0c0718020350b005e541a2912220f0200c101d03999920300501c001c000782800c59291010410b444000d0101100c0324520b40d8072202c000d40100b0ba1540039104c200e100f908810410000c51080d404010006042802048014070311038130045180118141006800b1002003070b4180143e1412030085c012071400165941c0054101305c00075034a0050030040390a600c03030381440c9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 673852257 1250 673851007 673851019
    0x9060705031905090301060f031505060d0b07050304110906011d01091e08071a030601051c020705070e0a020708120603120403121206050102060a1d0a0302100c08071b05030702 77
    0xa19445801000919103135004a008001c0d654480302501c2d404009408003404030080c861004420341e0645d1300c0141c2000d0000e1005001000d143c2d180d0700d028800303c3c0c140e40095004001c0c007040107150100c00034007510498503c680c601d0300ac000202a10100c4101c0c980350b1240800b40006070340a8690341016100000d42d442d030000081c414010b0315915481a0541481b66041c00500c0d480700c3d800803400ca0121000103031640d110140111140d8008040d8480581d0380d0f00c1003c01614040d10050a00070710603800340900da840d0000c20700c1042401080c040c03415004200305c0c4005182c0310100c40310400764000d407409a494a4020038900348403640c03030b642480b000003004001d110401e000344501c45860b0740c0701c15090041c0c1001809545240c8290b5005d644880e0115480e80c080760401c0503400e4031190314048007104100701624003440d015064015030030540000701c881800b4020595410b034541800c0d00c283c01d00340e000406601813003030807407004114503504000f040700a05c22207000d6134000f012 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 673853507 1250 673852257 673852297
    0x41a010210050a0608240f040c0b0d11070f0c0b090a0611160e0a110a08040f06110328020403020d0b1b3907120f0c06020c010807030b060906070503 65
    0xc451054000ba041b10010b20b600032000070005d410700c51100307100396406003c045485203000740d010425040514007c01c02911407214200540c400c1000e8548103020f000e031440340038001e04044072a00007a410141c81e400003080458410784401e5592800c0359041d240005d20481145042d40c1001803000c64528034880c1000001040c1c0104a4024091844940200400a0441e035000d005d84195113051000c50710040008012504521040301002c0c05240d0108001180019002ea542d1044651000116860b06140640d94a649420b1607280c0004002c514050542e000200e903213109000082c00300e8840c90002d0500d441e045a402d001c16140d440164503643e0031150350011181c8400500001c943c00544070414442d400525542858080007401229040141c00c00c400000340c1415100720103640300d071000140b21145414010901580031300003007104500010105000501010205403c0000072802952440102d90200000b100c85980d1801c02c4c2c40c000c2d0450080341d464010314031000c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 673854757 1250 673853507 673853533
    0x5010e101215210b0106050d020c0f061501080f06040e16080c010f020a0c1a07020603160908060108070e1009090c0602100624050405190302041a010210050a0608 71
    0x60b41109a0b010740c030700e1030f003101c40003203401003c0c1c0000b000141015110400421007640101c00074004048410780140c03901d03001884041c42c1071041c40f0485540d5101001300500c0e00c0203a0a0320b52049400d02e0403007150305084000c524500d0000c4c0102d0300c81c070340d191092500c0c0c1f0401c00c084001d001c01d5000e070006195503440002e480b10000f580e03135800700d00c19100910344288040340441d00b032680f000d42041e6050405892510302020303100581c1c1204402c000d03040c0965180301c041c51140020310080d0241c03140d002c0000f071220304c1c0b503030200c031072a40035a00505c284503003c1407900640d64ac80d11004d1b81c40d52000188804901c03180e0207072116030729203840f1000303000069043c281a21055000c460070602002c40d000100e0740c0d14454524601c801740f140c142011700007200d403e89056603241050074035440710002120a030340303281d01c0040c2c2c40c1201010000c50600307009104e4007a0070819002c180381e1072800041d40f2070907040c0506a000355114000340c007103400d030340c88080500001e604603071390364544807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 673856007 1250 673854757 673854791
    0x616140606040b100f0804111819092607060e24070e01050c0f01020c0a050111040609030b04052e0e06040302070b030709150e04140105010e1012 64
    0x9101980503d0525000f00385500380012148654589980d418400c05485042112030340e0000d40708a480c0c012031240c4824039600c40e0006020404800300d03200c407038180720344140154074285424202c0316040940c08c4d00412003400c4289100408000740c00e01801400035a49804e100e0310000400c00c900d040d00d441580c00c0009041c0c12046140c2c841809040c4001c000c125112200b1103040001604070705051029500c604c0181240c0c1454404442c1c12008240c0341900f641c0204644440d6a44500d9203441408002d02034003080700200e24045d45864108000101111100e010142407908110b002c101081030401a4040741c501008005c40e041d415800c0d04100c10741c3c901341d0682d20324103122000c521003102040c0c09000d158144c0003051032900d06180030089400090006d018130a107400c00044412040c4041281c0504a82d03402e1040d11007841040300315a070b555500034843d40c4980040c41145d801480d0051506400c49a040544885003c120359242003400c1014a00b030034501c114000351105 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 673857257 1250 673856007 673856011
    0x130f05040b040e03160203010e060403030902030712230309040504060c09050306062103040e070c030305010602300c01020429121611150a050a06120206161406 70
    0x225400e101c4420400200b00070b80352600040740242c0c10800c05a441c0342051602c503207000c1e20140001c60303c1c5070705d900260b0414400b224151f000c01c2e01e54100104506d41071000c100131b0b00d01600c000c1c0049085898840141c80001c2c1c0c1c0302e0a0791082111003401503410011350380348200c010700a00082c649403808002400e04400110b0120707860240100b03e910b8003060309840f0344006481200c0c1913070700288110700401d030707c0f003464001d00041002140b2034a903c040c030b5128011603165202880d200340340060403104164000300c1150402048043e4000c130001800b1400000400c44540c1400101001000fa1040d07845681c0c0542c40003a000900c5111808402e0a100381107080e40207000088804010700e114810404505800c4074000600107108032802c0c500312945450010320b0310411640070741c42d02c98080c0301e00f1244e40000c001c211030a801c03400b45541c414400842030100034074101c058840900b0106c0024851140410500320425504540d485296009542801c03200040c0f03084070f44886007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 673858507 1250 673857257 673857259
    0x14071b03360609060503060402070606180b010e0a2d08070e040203011506081308040b220f080c0103021b010c0f0e090606090d0606080d05041706010506071205130f05 73
    0x78405000a1880c05489100d080300c0f0a510790768610b0f0f0340c0c0d00400c0000c1d4080030b02215550b50325800030440d030071901d03214202d98005041c00110517441e400098040d0001f50342c0240b00e850815807e00c1050010100b004085070410369803c9078542c9000100c0040314a500810100d01c030b4011300080c0d510301d80c14400d001f07500a03002000002000c8400340c81d0700c01d9a02402d40410202e002003810007840046010b0b00314002c1c2c00243c242512502d50396656407040305007440442c2221105100d1460179400c0344000c0080a00b048040c504e41660340f500c5501c09062281403540c0415070200013000460411600c6030000001c00ca44003c1c41005428410040000000501441e10f12411403e01000302405002c0081c02c0318100a50401080290484898201e034500e031199800201d0902c20040051940c41907110365445030704007500d00101001c146001202139002400412003501c1d540f04440d07186420221a41e1550f1034404140e48078441c0c0000480d412200ca600025642d03402080340041c0c0d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 673859757 1250 673858507 673858607
    0x9060801050306090304060c080c0a0b19090c0b18100c050d141b030705012a02060c0a0804020114070302060a060506180405090a0b09030307020114071b03 68
    0x41c9500915564000485582c422684200402d00105000e443c3e42d00140c0d210341012803a00c1c074078000e02c6061643d40f40b401c503170640d4800281302008a540010010001d4400c0302003003510450b44030000604801e20501c1c548800002d089500a0421038641c40240405410401101081840186030040744c600c1500c0502410010031140c0c1c8c824031640078200b03010540181064140c901c2501c034101000d100e99824070040000c800040c4085c0210ba018290003c00345104c00d800ca40042c4026a002e06190700b10340244042100207802407094584103221464808c00036640c80c80103940d0390914407600e2011302d901049183c1056400100d07a0300c0f4500c440400d01070580d5900500c01180030314885540102c00003081107070142007030303400b0300d501c01c00ea00100e9102000a44072007841d0442039903801c0e0603801c00820440001e8090041900ca1400720140c030080e454400002400b545041d815031482d54507074400c2d601414070450180b1000d50000152010503840604188055480307945071031302c484 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 673861007 1250 673859757 673859759
    0x3050612010e1e160b1321020a080f120d0b0307270c2001020f040612061a0415030209060c01020c010c051c0513050d020604030206060904020d0209070c1209060801 72
    0x180702040740c00991074143c00d00080d00b410075668a085c0d42107115039400e042c4855200180d0044510103c0001c1644900484c001103214010b00129091541081d0b0f51980034200f0803c0755600095090100c6101d11603543e103c01c2405140d901904960413280d0b03240c440c1e5240490f607110f0580403078111500700401d509180c52808410000c0d9250080d150001c2108e01c201b40e40c54070303046c80840c034804d481c01c0f00052a202d0f02941541c3c0c280c2094004e80000ba00b205040070303d070301141c420300b40600480240c0305040041e42038034212078403403400b4071000040100400c440704da0007601a14440f000c010115900c03820032800560003508020100359040d828002222500ca009504840c500c0781d0318145681c00500c2c0080880140002030321b110007140240c0e60b4400411018040c04014500a9010307000701e0901d814021301d8080c010341414428040c4005020050f41e8034406a000320758169800003690351021826944002f140f24080c007808220000c19a000c5d501c60030000030b031041c94440b00d660b0307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 673862257 1250 673861007 673861063
    0x606050d050f15090712060627080a1704051503190603030816090b040e040b071e0c0609021315090207020307050d020a080106080102030a0b040b01090603050612010e 73
    0x21903815603003003070400191581600f0310f0034500d103135640c0301103941802407003010102024000c81d9510703400311001a440100361640c0101c0610001f500072101146e0200705400c00700306d240c40d4482c00000a24205150589642600c01c2400303490040c14010806140b5102011100020b81d104a8500200c480107109981c035082592007520262505a0345230b20065441c40c840c0540110704030380600a00028040000c0c0c6601c4500050001d880119040541414540391503491140d02030709400a0248501580d5060f0207601200c000d05a45440c0001c03540d8441d04002c0028101c1d44d402a402600c01400300c03802070700c10307002245800d0104514000c0250f0702c07403683c0101e024482009515030402d050030070031460300001400499000505c0b010000360b640e40030500316803060b800390403565008030411280c0314003440b40c070020a0080d20140403007072645000a0407240b05000d480e09060307a46010907040e0310345500004402e6034100003001600c0c050210541c0c0c070103500c0b0300103400c0c440069065202e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 673863507 1250 673862257 673862281
    0xe0f12030421090321090303050d0e0f0c040e0609101d0a060614030d0806090c041806051f050a030e010e030d1e09120c03050708162303090909100606050d05 69
    0x610400ca9441d180321b1030640d40d0855260b030001301180d04ca04e8581d84026a244070030302040034103060300001090706002010500c0159030205400744520f0b040041000441400400e900292244250b00000c108a454000d0344d1b0321102c00007494228480c181450f400c020450744031000303559000c0d501c0c640d041c25200800d603413503492101e03040020720300f4000326109013001492190003545804540341499152101c40444141e40419466156110881000710b0f041c01022070203000c0e940382c1c0d206c0d00d0003140c0c0c2c030190252203107013981000c1566801d030a1405200a61246030358618043c02d80380c0d80c4958500001c00b40405400d1040c0640d05000400d1038841c01e8481c649003141e01c4a0031443c81b02607480142d8800c0480c400c1501441800c0250b4400986024014145240d855009144880442c24050440c903074114281103c80110110020b46217000010781d040310108440540c16039071500003035400c1c040e01100c2100c0050810201241c02038200b03000d00441490340904004990340c0711800c00c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 673864757 1250 673863507 673863563
    0x11071a09030702040b04090501051f0f14010806030c06030c13050306100e070905090a050106021b060313030909020d0203071206120303020a050909010603050108010e0f120304210903 80
    0xd040c0d402000b20000609013a000b01a100c08001c000142007190340e2111403d55070704940912100100700e4411540440c00640307d405044d80381001c141c2c0f0341c140703070484150000341b0444c03034180804100020450382d400c01c4441e000707100280030780342c1768200600c540f080c640001c4454a08200900004142c508000030302c103104200301180141d0310340c81c010f5000307810b150251500081040e81a4081032640300d01d0f10190091000280008142d032500700001d0400050303100c2d0036810324283c0e080781816a20310054036084818951002c0401e2a00c1c94180c07042d0032180c4c000040540041005a2101002e50107584a0044c41c2c8900b44d00d120006824011510b05020781d0381861540c03240140031038829406011407840d10308155240056600c001031070040c00340e100c0030000e46c8842c0184022407080c01014540e80440d0003d002d0100400b0b41142c68000541034841c1c10030001c000602071100351a5540b60307420030010302508200c0c1c1d28500030b0400a103804140d9010602c0e24100d80e540201d400001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 673866007 1250 673864757 673864771
    0xd0f210815090c030703020a11030301270209150901210209030601080f030706050604020d150317091c030c081201051c050c010c0825290703020703020a0611071a 71
    0x103185a039000006d400941044408030104118020710405031030040005502034400c0d94481444051a0213034100304c80003403e46032072864014400c3c003115850312030000300010b034040c501c203498800c10001269032842c400001031100e0196034030b940c100c0d80c540d070007007040181c1a815a5641c1c0e0300c40c010541d032200320021444251b4801c104140224056500030354224600400151400002c0c0017898259506540400798241100c4002c10030010403c4401c1c03190a08520020304000000f00021500c20100080164440e201d1150004040c416400b102c01583d0141203142c5030080c0100c2100e0450003402041d005060501c0c99401e079442200c8190755690380040103155000e01ca200454040345240001c5031040c40a100c0030000f11410400d80078200500510516040342134141034000c9500c070243d482000c90740055070003103100d00c5221a0b41c890762030304004d640c071491450f0032454441d100344051700075481c0120650343d0480350801080800d01854104500540c190091002c00d60242d03075072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 673867257 1250 673866007 673866031
    0xc06070314030421080a0605091006030f0908040f0602010c1815090312030b040b0d1109100902030f07030e011a0f040207320a020d0f21081509 63
    0x2035581d0196040045030700c1881032490039010607040341d82d06418405100e503480416480c80c10440004945d114180040c003017112213480c6030500301100c00d1725400a0140f94201515121050060240c5030003000c035082d40991005e40d03841d62001d41d08a0b0902a0013490010750a01600f001c42c24801c500100d4040f860b111010301c258581070892400004140d0450f09100400c4000000b084440401c0c82603040c0580303000c1540800a000c100891f003000403050300c6610444400d0b401b00e0302443c580305914405480c3e0081c59101c004500075a0000f543c04001802c0c00003080003405c0b11079a40f841e00502d050b03103061140580000c5100e0a0b641601c0356003000c0e0703140041c07404480c1f60a0400398500240500010f14000907a11895807100103000f00354078545103038003529440c41c0380c86010802403650001411701e8404a50001c1c2d80084003441c00303002400d54144203814420724a0041058001c1c4a03485154500000c40c05401944100c1e0b400c1c0d11000c890700d60300340300d040c92480302c5e1180a4480003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 673868507 1250 673867257 673867277
    0xa050106080612011b021e1504260c07150507050c060a0c1e0308010602070602031e040506270301140105100c020a030803091204060c061a0d140c060703 67
    0x80c0500480c051164a0f402d43d2541c0c480041480c1c0d0701540030f0308184507406809450710103119801c090003111401b803115808401c25074030860300c5940319034110f03601c4114407078502c1102d0010107000217004100b10003800d001400c0e10a20000041020844940300034507020810f0140b0103988900820710054400d400c81514103045203080c600231b04e6146040d00b0000d0b00c0341074903102c00c80c10351403400301d011a0600c9070350188207250300004901d0040c1000d01c018a4040d0902c4002034981c05504210403088200c1c00003044001400006c0d20007070040504856150b5030400640e00103500c410031050750f40d00c1c03a441c80d8072440c1810701484030101d03146014116540d00c1c210074030072080302c41c104ac00c0403c1032041500005903164042e2200842c080c1406c02c2c0c072410003018241c100070b4500100c104541c02008100656500b003c614070110390403117030001d520344d85880545004000740c06040da1081005d06600d040002141000207600041c00031101808203030014450300d0721079a81e0217808500500c2d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 673869757 1250 673868507 673868509
    0x70312030227010e0d1b0902120f04080a0305250302090405100803070f0606030c081b0f011704140f030d0e010b06160c0806071715010f0507051608150a0501060806 72
    0x403018006071306c12001c0c1d04c1684a0341a40d1000b104664101c40120358001034400340240e150840d15406c2019503c1108590034182d03141d00f030380d10a01a42406054542e00090102e185070540a00c40c0c0704066010810300b010824028000e503c4165007510030f0749450013184400341c0c04258502591078010083d8504540364561280c0d0b402e01140482d1005c1d00c902001c00003440c840340f040c000740820001400c29140340307502081403040c401c40d414003484440c2061109aa0302c40205c0301100140418000c40d510380342001d040a0a5031160094a81325182c0804510301e000401030a1108880408122040130101c0301800c0e2100e04012592100b400d1040104081a600005c00e43d988204890410140d6030f0b1001420100201c40b40c9022440024540100c20706400ca81d03580b00313003072014403105041c43e00c0c00a410300743c08044240c20402c020a201c420003c04002880030382407076405001c03540342ea903108155a41c151040c5912105040e1021a4400074580611416202c16884101d26565880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 673871007 1250 673869757 673869769
    0x6042604050a080303060117060901152f070504140106030e1c02030d0b03010c02060103080901020316140d170a110412060e060c0406021b03070312030227010e 70
    0x154000092000400000441c0d6466030350020090034944040c64a03450110009007085140c2c04040545a45101c00c00c110341c1d03101e01c4203c1c1036421011450a0301624404202e480c0140812551840c42040840140030540c240c1802c06003440d90b01102d111580380c605000030703250600d0a86101d154601c00500c901c0d400713504800b108010f20001c0341d04400c900b0000950002034203000c070016810004096806401034082c2d080f010318160000c0c0405441c1d03035402580c0307400520024010080106804031030b40e01c2807007201c080154480f08443c0803609414907080321080760700041424416218180400c0703004141c0403800701038440d1103902c5030f600d04030108050300d0b50078000e19110030208004115103680e02d210f1010305000d00d0000403030005007003c280c9000c1c8060a9200f2840b001d0004005480d8009403042c034100d01c0d000c1c0201d1141c000f101083c036240341030b0801004509004400f134400755040d4050300340305c41c0445200090000411855030160104901103000403800f1140100c01c1c1091 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 673872257 1250 673871007 673871063
    0x30314190507020309132d0501090507090b0a0f050f0a080a0e19030c03050d020f0a030f05010b0403031404080a05030720130509150a060504050f0c03061509040c0503010303110604 79
    0x3c40305101620f113810071f03540e60400c05180d41030601035450006009584d0f4a124482c0e018055050200c04030303080c0b05a22201d4041c44500404011880d07820007043c5202760207449031000c3c0d0048080d181c41c81e0f0035000c0c00d00c013800c4039200086858402465441c5c0b100062210b10f00c44000c0d102e1950840944080325508031500303043d014440c042010138605a194070003030181890001c0c0b903580740c0d05070364070040c285c508690710340300401d04120040c010206840201e03000c40f6418200040418085001c40d242406694030003601c0d40074904195003031020110007007102910450401514811b03030f039000c0d05514000c03a200b54100c8030180c100d28181171340385e20441c2c010781680c0849842001100c941185854101c03044d0146a403284410005414907014541e0050300500710504d1900e824500c010081c04020942441703403421601182c0d400842c0411500c11501c042c00502c003c41c154040940302d9070080c4021400115008a8401c02d00700c0405d219000d1503000c0c0010f0215100c1e0180d00c0350070240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 673873507 1250 673872257 673872281
    0x180b07081b04060c030206090109030801093210090207050705040c0248090606070f05060708041103031204060515090108010c09170c01030903031419050702030913 72
    0x420081150008039681c050401001da5644820803c042880c000b030910101802c841050781c107081071070002a40000005041d18401d040014205200d2141011140009400b104003403010b0031000340501e803c3e4040b5881002003e4030404095620b20000e4124450120090903d812141060003945000d81022000b0740440c8104d9811160340e44030481c901586445030400980010460300031481c801c2c19100c611b82170144040c0801c00fa44010801071303070700186a10300c5240c0000341201004005404500943e40010444010b840c0880024210640075901510207003030511921946203000022031700801d04404000e40f2a07117607640c410300030b0075000c1c08141c21303610603c0b250707031190b100c0600c40c0d0700a020800010a506020b440c0180c82000990442d406040e0440c0c2800d03611040090000284d24080c0390004000c8110309044005001d0032004003038140103001408510200701c05003603c0200d15043c20009900c40001c01c1ea07603407043c0d460f0550000c01c00c4000b03007184a1540c0c05036038a066 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 673874757 1250 673873507 673873531
    0x906010e0301051501080a060602070e06030f03040e07020c0913020f0301110c150a05060117100506180102070e070c0f080d230f01061d03012d180b0708 67
    0x3284000203400d4603400c848100b07034a4028100200745682c800702080c0c02240c041010003c490030520000d4035040c00f4020344029181c0540800d14640b42040041a40741e54401900c0c3c40d1900c603110b08400b410269800b000610801d00e8034003041c42c003550158000c0c118120782d56150348140d400e000050054000c05540341d50380d4034031141c010b21044c004141c080705500203404190244549070318101d801504902500e40703032000b0010141d0700071034080052440c050b5100460303a94480003000110280c1c10554100e10041441d203007a1050303084409200b0301c02d800b03460301c0c02d4582d50005400c81c41180d1030b00c000f618203c1c4850201d0b80c0442034007505409800003a141407915003c0400b55141403a00e220000000e0508442c0482c9203404141c014020310303c0f010043d454414018160402e480f001a50854001600c007420340d800d41c007e0703141951021352442e40c044004d82544004502d041140754203804d01604034001600742407c0700c0440d074800b4003c81300f1b403116a811070390500d00421510503c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 673876007 1250 673874757 673874777
    0x180a0e0c03030a0f12050114090a020d090f02090a05280e030f04030b091b09060f2d060403020303040e0c070c15030c08070903031119060c140a0e090601 67
    0x51002d1000f040016429181d20281140220008080488180030003083c1c91820005015000300d6041c0c8039003c00045940c40d06c55295540ca0600078802c4048035080300e1b15003000c0f1020400c100030070100e043e0080350543c0c25a1b0711490030300b007620000c80d40007100e2519410055400001c42001401040c140e4000117488001100c04614591004c070542e44074030004141042041003080006500c0700190002d040c44046100c0c00c2c240750a007000031584a190841c00103101a2141480c03c841d0200080c842e1003c0b4002d040c00f12a52000d025000303140d17500800c01c507400c90505404940c203c0c0d174044c004501c1d09281c80524010b40801408080c02030b8010006c1340003040741b201103034028205013611005582d04441c805002c0341c41c032070102c000b0301031880200590560416245400c0b00d402d81030128000045071070803410000c5070703003845030b2140c1e10310030400070301c030240e407065010301c1d250344500301d42c1006504280d5807170044d45e00c050000340e001e140205031410810001d581000040c14040c040c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 673877257 1250 673876007 673876009
    0x10501051309050f09010b0105040b0409110d0f0e0709140a0c03020c0303010306150609030f0b04050705040915050c03010b030412020a060603150b0103020f040e0c12071d180a0e0c 79
    0x69142604c5080850282505010000100b0f12450500c0c1c032007420f00a15081c07500b00c0c3c20440307000d54400da40b0715a0382c174003009070174002c0302045440d146800c1780200700191941c4800c04c010030180f120040729200d19180410121140d204161381e807140f1803440c00080d0754454109010345034600381d00303082680911824032582010000345020710b00c01c00000c076504a00601010102204c2d41c44101003000401041010079680c0c1079100c074890300201e2401d42940c9074240145401c40700d920054000c0c2c581240e100900070080c120100008681d001440f040d115800359a83ca40400e028a2500c02401c00200e40010042c100f440041c0e4030358010b0700c0ca2889507868042c1120f0301e5078403d03074200e1107c459451215000b4401d1000c002c40c03d003001c5050591400c4106a18025809900300d813103204400b0501d84d541950036070b2034500701451902c00c01c0c40c00040040c60200c895031005a0903042d480060b4907442c00404040700350b22040c1c1c220040e9641c62103150013510210340d6050090041104951721 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 673878507 1250 673877257 673877261
    0xe06031b2115150603010504021b0d09050f09070212070615030818030a150905030d0e0d120b010e0f0f1e03191e0201090e0103050a1e0209010501051309 67
    0x3080440081e249003940c0389140702c0c031102c0040890343c0c42001124822803598895042d681036840c02c6d1401a282d40c0c1e1038204103881c4103000403d41c0d5910422030540041c680c00300c081826140142d894174040d0700c898051001550040d80c40034096007203c10210203141c0d1a130054a0094010840850019804200542d4084868100307a46008002450348a0038105080c180302220040d0020150a44191600c442c03003148007401c400a66110a948010302030f01b007050301c5200d101101d00300848542ca0543e183c4d00c00c801d40d2400f001c141d603031600c0550005a44541e01c440720040e11506c14041180742041195040c01c0d000079070041104a4404d0103444a16080300140155032282c2c01e00c40c85501054503085101001c2c582048010100c2c000140c0c80c1d9010984442d103560800100040c2880140c030401055048015444d02c2680000180031000908100c46401258440143c0c070544c6145640c440c16040c1c0650060300100c01088294800c800078541d02c1105a141418251100d440c041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 673879757 1250 673878507 673878559
    0x32a1c0f06050601030606020d0f11032506060515070b0c0c01151a1606020c011e0504030f090e04110103020f0c0c1002030c10020c070b21010e06031b 66
    0x1c030699103600f044a030b0b5806102d8003000e8a614001032184061906005008003000700c814002c000000d2a511150b40042081da4080c1c8400b07034148545500314921b10202e4455000241c80180c103100b40080c650901e10042032140301460f18051803d00b09480d00804581b014003680d003205000c2044d8540c00f5020b204d138050b0080e1480a600510307160614400c0c618140296070800d5881c1040481c03401510620b442d4161a4000c0e00541c50740c150785803060041c80169802c18000603521030415410328164442071003140b080e1980507100b070701200215202c0400f40038012180000c5804600401e2645084a50805c0d05140251070b210760042c5003003082e0000302d4121110f5220847d216014035004000c0c0e40c402040d48010341c103000c0840c02c0d4a54602d003051202500300c3e030000e24800700c01418007002c4090034060320070316502c80c070142e030014a2590540080b071189008070008503542c0d1011000b60b0052034000c00070515031a22444880400d84048030f8182c0c800c1245480383d02400741881816 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 673881007 1250 673879757 673879763
    0x3020712060518061608090109080c0f060c040312030b04060929180103140a0204061d070905030c060d02090a0803041805060a060e030a060e0c032a1c0f 67
    0x400c003030404044032825100f0311002c0307007400e03000321007007040711418200d40090115513458010440d455800c5114010940c0d414040d240f030b078002030160307441c40001540c0c410100e6054222001540d502110348218016070000500544981d005130801074429000341c40002802480010500e59842c240011580840301d002c081c40781c1d4031003030070704da0011031280f05c074200017552410b100f02a81e48000041e9001400002d0401c06811a0048080d10801001207050707405401040160344a4550a07440c84070140e400c048840c0140c001150359120b00d0525003150070241c01401082c84681c100001600301018042d1170340e909003c49003542d9211860900240710b02c1026650381d0342440c0841120310528039041030b032075042c1800e20081d5201c84520404503140e910301459108200383c000303030600030304650203080c3c6410040c1c0c18800c40c20200742c00c0c1d14580120100c80710720f42c030469000e0340d400c2084d4409440d640c03419070740307452410100d0340c0040d90040300300710001007803c5694214030340368001015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 673882257 1250 673881007 673881011
    0x8130906080d021501030b131a011403030703090e0601121806050112050304060f140a0315081b0411070506090709050c04050f460b0a020d0302070302071206 69
    0x100300010060006003a45103943c4082c1608484261102c0008807041c4001011702005400040240c840304030469078140d88842e05c0c003c0d8504030a5402003100c0280501440c1d9141c2040402180c07900004031400c0c998191a0b014072039261444164010b070000b880d107818001c401c20019200000c0d1310414080c41c0c82071a1801d520280c1c0d04002d0112541600285109401c40c076140c13020500c00070603501144c09a1500300300241c98150100c07002140302c682100381c0702010902000715a01500807000412a5503c10030500d40d540a42c00d68401c61405468051008074600200c0c03030a040e04124902e54420034064070f440466a5218a0710304115103001c40e40d0080d1030180003140d002d00980d41c100d8107160259003040e040c000052488500c0994441c0b0405007000b041030301c8540d01f80000459213032600d40c02000f60010744042440b80c51515244569a14002d010420300c082209031b546565881c0d0081502c160016401d80c025406200c007a070652003204000030350825001c0c2403100b9940309443c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 673883507 1250 673882257 673882259
    0xc110f0d15060905060d110609091305010e1c140f0304030807090b0a1416080c01241202060d1407030f1a010e010e06160305070209151302030408130906 67
    0x1001003260001c3d0800b0320b4950400081c001c9903620489000142608820901403246000300025201e10075090700302c0d0000040c0e0f04000607900d940c49031302a15401078000b40940d403002c469068072065a881e56121400101680b51801d41c0300d4200382c214100640b02c00c92803c0300e4601512090b0304110746c00c40c00180b0f040c7c00c111032680d01500e418000c002c40420107041500100d0080d00c07680b16030b0108070100f11f010640d0340490315401d282ca02815000300c4000d6a0351740b0310440501a00c880101d4100402641c2d407072441761840c0c00044011101011003034503031044151f08200d8a0790241a200b100140c0314080c03c200b008080c03100d103000e03d0882d1000078440b0070030480a002c1ea480c0454410030205509030b89000d41e6040111a1702402007443c28119000700840066014011004890304140300c22040c4010503402000030300086000701c400d040d850b9150b141a441e808092034550350411040e040305040206250091600070f40b10700c000906100288800c080343c0201c03540180001611a14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 673884757 1250 673883507 673883543
    0xb0102070b220e0403090b031f0605180109050d02010804021807020a0b0105031b040c09080f03030103021804080f0715240f05010206040807060b150301050a0906060c110f0d 76
    0x3101034001d140f40028550a0f14060b10060040707040d5100e00c0340081030000000e902d030070f40e0160b52141e070640c2c0e04606c03280360f844034001011900003100b00318103002444844080d40d80598001d900719203000300301101905d6544e004640c0303c900600b080f60800c9000c7c03003403400002c81e61a49442003089034010001031549080c020038000c2c042c0c2c0924040d0b00880c2070102c8a0340480310981e00e002c802c2da0301040c6510104800c9a0140d000e83c4050040e008420394441001e5020005604890085441503414500c0607034072032403040251802050f15404000c4640801458405030a84030301a8955864a1950082410599400184c0c0c0c0f000441040620000c595a101001000d0100d0b0496149000c0c2071a002035074401001d040640310040c0422141d0421049030030040623180080c0050405202c0c08462042075042800740c1c030310400d09a400492000c03980e1080c1412a102c3c0d41d900c04c1d2144d03460306d80712103800329850320640001000300403000d1901e0310080b010f985480b402c400d207103041281e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 673886007 1250 673884757 673884817
    0x120201020c06030f1504140a090302120714160806010312051c050405060c0a090302010503040c0803040611010e0c01090b0c010b06041d0915010b2107030f2d0b0102070b 74
    0x9400610a40c6803081c1c1e500091f590b0a4225070002c81030100003003217101414142e03c0e064060010640e88000052100c0070000440c0c258800c40c00d00f4412241a034540c0000d2801404480c028400c203944035100400109100c6403a40ca40d4055606119207804200d80c1c0843c584034000301141105d076101c0007800200b0204200d1194030106484085041500c074110040c2050941e100c064100440480401d05015801c86142c00608072035048a079a079a5070203000d031005480040502c00c41d440c14040d40f00b00c40000c02d40d0500044165502034240341003400c3d0300c3d040d0f000002c000405d50750315050515a174499400a2001c0c02c0360141600100310246c0c42c00142c0ba000038074220441d041820b01040102c0c10001e242d040d141c800341c14070345402d140100307000000d1801c10751001c12108030007408541a09513004810040d0011b10500071a2210341400e0340e5218680071000c0b200d90700000e18400b149590340140c4040b0307414810b660f2115612007003407425410a13400c5240ca06803030308200d0340c020042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 673887257 1250 673886007 673886041
    0x2062215230c0a061b171501030e010203250c0b010506160507030b0613060f05060703022119050a020d0e03032719030f06150510030f060803090a120201020c06030f 72
    0xf03446e00400000700313589403003001d03a0082c140800c140f00309540d1030b046a01070b07000218000d036181c000710f4a071314145035410407084d01001c1884a1680d0505909821845152083c0549420850301031180e441c1c2021f000d81c0358807049800500303000100a000006078140b0280d00118041ca041a5040c1050740400821241c580d48030310a0740d180070b504100340f2580301c001d0b0080790b0044500c40d4aa41d41c41c1421303420031200c14100c4c0c2c1900841124491002c207503802030a01da508001c000b010601c20b500e41031310144034003241d03003015a0207900c0030840d49114581c1007110301c80150542e42844044105c0b5201c0ea014600f42407641e0042c40d60b100c0c06800e00d10440b641292074017265002c11440c544548400601100c4003502058859810b40c0d2881c070800b040100400002d002c0c00752000000e40010020042d1280c0102d8060400030005000c910020581c2d00281005040f01015860308913081d00032101040100d040d40944118104507985950203144070320003589844c07145151071240010781d4111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 673888507 1250 673887257 673887311
    0xc0f03040c050a05030c090109180c0603050103030f0809151f0f03110904170d0212250201060810051e0103050a0b090105010605030c0705010902062215230c0a06 71
    0x840a035921b91541c0f1002440e04560300e0060000700380780003200c40b42c802400ca40e00a0320110070003500092082c1c2c1640310314101d034065514030056007040c010440300f0540903648102c42d68041080180e400c10800d50040c0c0094640d010015820240b03403804000365415400b104a83d000643c081003030014402050045c0e40703045925012034503090380c49510080081d28007a0a11a000c40d03a0400c204080e4100c40c1c8226101c00031501914000c4002040e00505c4901c2001c4030400051002405005018180c01c0d01d00503005040c81c400b000400c1d40040000401c403060035400349035004448841110602e002e5401000684110030a0341440d40036004080c00100301a03151200404c0b00b1903112007034a1b00508402e80940c0e03501c1d0310f420402d015125000011303520002c0029015400c0080d030041a0b48508209084c0c18499914045074011418948103000810484080e410703881c407103840e65502c04842c582ca91402c041003803895070f140c640384800c105e070541d03540c01c0c07601d41040c100900200c0840c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 673889757 1250 673888507 673888513
    0x301020307050307140409090f020112090c120309030c080a020a17070605180a14040c0507050c0103240b0310090c0f030e030d05090a0b060907170c0f03040c050a0503 73
    0x1d0141000741030344030081c1000c00b0043c021046258000801c41164000c1c905910140f101410500305100780305c04011b0105e01240c0320039401301c0581500d004200240380c0001089140c1d030300d00311803d01e4030440b070a4120100074019901100040d07040e1750031005880351034010680e280d010f00c18455202c0e250f810407541506804000701c0d508100091030003d4804501d49141c4908002200401502d1890301d02e070350044030883c0100d1441306000303840c3c1d112401240c040c40389003007014080d00c092141c40800b404607003104d010072410754040d4010700c44100c4011b030f0300c9540411080c0c407800f0301c42c155088030010710000000c0c0403006640c00c41001c09400381c80802c1200c170303140440160080c031034000c4a10906444c0e16980580e20814011b6070b00c2200061014001072800070013581c0c0b61050741d4000c517180604440402c2c664286a80028800c00c080c0c0c80721052200c91185a81c1c0141d0010481e09611004200c3d40b400508100041d42c0500c2c03140d046002c0d1a414801000f00d60091a04698042e40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 673891007 1250 673889757 673889761
    0x4d060c0d06091146090b1206010f030209090103020f0f0907030b033f0d06080a0203070801020703091e12050f0f0f120c012d0b1807030e0f010c02010e0c03010203 71
    0xe030360039841d1640c13981e1151652000203c02c040075a030300700c015841030101c6c00000ca0074948204202e070940d40700d42d4090f6a2034800c807103032b528154204e0180c0d0403a0358001c00c2d118018001801c00b50b2006605131030003000d44000360944400612168421103c40000a03118880c41800f420200140c08415003607500d107140503002da8500c810300001040102c59003110b140c110400c80c0a40c2c40c112426074006d268248007158940c22010354800c000ea004034028454840c4c0040e00d46018401c1e16001e43d407564031840d415103400315074013181002d07503000101c3c481da0b00300c0050302e013018118815140d4032032409803503403481c844c40f183d00f40008a0ba4202c1660004000b03070a402c140801c121641d11480c20700c450b10359886c184078500404901440380c45540c1e10940715030f00880c00c0f6103c100165500e40043c07008458110501c10001c9103007100f0140d03183c0341d02c04540e10a000b80c1280c40d543c2410009c8500011148000300d0079074000d0315011b409070759280c510709805070080c080c074450f03104150000e61640c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 673892257 1250 673891007 673891087
    0x6030c0618060c02012607020c0909010b0d1202030f0d0915060602060c0a0e100305160c030525020d0602030604270b074d060c0d060911 60
    0x4000c0324907000341009030f5140130700c41115041010381511441b451440640d80b40c00301e0060361b190100c4503494403902000c000a14030001c14019400e0344600a001440030800c0e945e542e504501d598180704d019800309100b840301e4840154042d0200600c192000f20724440380d8102000e03c101501502a09503003841414017406400103209178002055210311a031312101da003030845418810030010365102180d20a40007685506412503802003403004119a14040c1d40d0009544ca50360038000100030520038410403403013900c03445400c813200504042c0425130010550000300c80481c01c500443d0407030b9010043c040c20f03083c0352184d00100d00682415040c152180244070100760300154000744084007880000c0c01c03480c460446401d01d6066041d482160311070b41078207840281c401208420100080c00b03400841034444504d000c0400661902401311074449402c1050303550b000c041c11050722516800002184203040c42012103170101215065260f80d0030417071a07400e00b03000b00d1100c29500d04604c90000b40c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 673893507 1250 673892257 673892267
    0x15010c020108071805030303010b0c0106060c031e11030c0d0e04020738040302030a08070e0d110f060706090b07050c07090b030111040306090c0e010819050102090406030c061806 78
    0x8040f0504015007207410902e0070086104d584c0e04203541600010000145000111002e0102490321100a015131511468110745d6111603040160000349040580c04415900c094440e054078450318040d9034400b101c02c0d00603d140c1c040140b403000c9030301012205400641c801c41c0070030706c4135013102c06502c0d04c0c3c80c9864140303203015416900742c1401210082d0401d0400a05032a0320780c0403080c2c0300c44440c1e103810704000c1d460350800640400403903c1c400018640c1c43c4502030602411800030042c050001654541da001c80b103440401c1c0b0341100131198100440d80d2110040c0441c90711800002c5404d45043c0350189c1d48941c050000c10030f001c0103106a030791404022070070340c0948048203000100e030706102e400240034001602c600c0ca0f400c10700240200a105054102c1d040185c01161800d050668849115400b440c0034881c4c3c0941e03030810602010600c1c003210b803a0031014060000036080c030015070002011110706600840700d11840f903070200030094000d0b2600c017aa50b0202d00c42c8110038500900508 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 673894757 1250 673893507 673893511
    0x10906020115030201030240150507080a0c0b010f092714240f06030c030721020925031e021b0a0c1a030103110111030f030f15010c020108 61
    0x410715802051400030848c8099081000351781d00704015524100e00003a070205551060b5025142c010072078170101c0d8028012a40740c0c0c18101c0d1b03039110b80c601603907515401d280340c004801748020010007176182400710300002d064901800c0740340b0701e94850a1408007010229070b8083ca1700c1c89000318142c07110000156064a8070741031a00800c40d2030b44901e0141189041c15191481c00d10007050000c20090800b0842030030f98400c2c404880080c409031540d00406a60300fa04401c0558150f00003841401405560300303003c1444902108008070040c00f640c001121081c045840d00314000f603010030f48a00900d007030b40c8030300d2803491800d04201800c0ca4100e200c0d80c582c2d004d915406019000618a0801540304200c81400139078103042c1d400480d0f640c90141c89d0aa110f21912004000b610320f02920568400101ca040303a92151408400005810040d107210750140b1840c81076000c14000710304200c100f900254401e1403001c814420601d001d044800b640c4e170403403a2150410001c8400c810041c3d801400c459 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 673896007 1250 673894757 673894759
    0x10810030209100b0a03090201110606130209040f0f0c14160318051c0501051803092e17070906021902041107080d0b19060305060d1e020109060201150302 68
    0x940181d0f6980181003026009030311461615400040c0a80210390590010f003109200f43e0f0341259482880b810a6518501580c0755640240702609512134001c080d03004028a08018101298403c003c0d585082103035480b5061000840e19200d208074001d501070010800c2441c4c1d44000c0b410529031100c80b1480301c1100342c1c010b060051041d0313400048480494110018000106403610340c03036010440803050007a181c0211010b6003003001280300b10842f0380921040701c1d40d400040d801e103183d42c010401080403a04201241020003201c1c0c0000050804d1600580310b003a88034100c03104d41100030310905403001448441081034010341072007030f2a070100707441800d4404c5c0c0800d1340715800d01e400000c00500d400c0710391949100c00000c82100300084200601a45145500200143d10052091004940a03014080102814040300b40a81e80c02035009540000014003038040d41c114550ba050310b403030130446091840c164200142d008640c0d00005c9074001e041148000c2c4200840c03401c10343d000c490180402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 673897257 1250 673896007 673896019
    0x162d1a0112031d060301030501140606180d0204021213170a051207121a010801080c150d020408010f0b040b0315011206020c031218030309030307050c1c050c010b0108100302 76
    0x94000f41c08284510780d03545000924150b5256580c3ca001d9008190f07001203d0444442c21000404074a0032400780e488002c8030422424003030300c00008012109500100c01c991042d0300780852654016a0322085100300241c4404d00d404140c00c1c1811460f02c000415901d0350702c0020440c84640f5540401991299100340c0d190725060388580c5001d40d500c1c2d20207850b01d2801454410750100c1001d40131034a11b000042078807039004598903007031019115181c001c3c40c40c0d04103d44040c450344012000b0000c000740110881b00509058540800509466072034104504407a11602115070314036151040e1181513004078010b0003080724400d0340c2d4003020014420072000d2200b420800040c00303c3c603011680c2080c3d00e4801d4036950b1284094a58070740a050703a41c00851030200d000b00c0a0550000112401b410042c0011825a50b60380d10841d036640c00494248000d000354018980d51421120309410208401d45030161510b11001520b82110034808400d23042100403402e002c5911404841c0d00e041e26016500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 673898507 1250 673897257 673897277
    0x40302010519020a05010e030310050306040218250503060f06070f030806030a0507030b18060f13140607080414010c0912060605030f0c0109060311162d1a011203 71
    0x4144d04050881d50042d0513035080803120003035600040021445844081804a48652544103141c1c0d201000c8400a4120010540710344c01842400c8106500c03036001d80020181ca207018008034820079082c048400440c80100c00d00c03c00785480c6c001c8a151500035509070341049016140e0203038074400044003609221042002c51100d490912010415682150803078081c0d81d5030b882d065000160489450440880042c41d04581900108001e4040d0700040c0130026523031551401c00280c4001090121a1100104a003100c1c1e0442401800d01c0b03120940c5961145141500b41418070702d4106d500c10711240d01d800c08103e13100da00050030609884440c2162940303000d2a103003010082c28507401041d854442e0b41a00c0d40c0d2810f0019000b20201c00a030b8030b5080041d035071002601960b408000307000b218841072000500ca0040c060050203540d014400c3d0ba0781403030550030b04078001c840596140010031005030041041c00300038500848001d0004c11101c034103600d014164640181c4241c0700070200401c20398 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 673899757 1250 673898507 673898557
    0xb150904151e030203010c080403020d08070513090b040c0e01020d121104080607020c06040e010b2a03040602070b181504051503150a0e0a0f14090c01090b0403020105 73
    0xc41a406020781c045100b40d90104160842003015092004910035070804c5400424103124401043c0540d0307260300104101f0686e1038046e07491040003442d14040060921580100102040d08031005124442d400038409505d04248801c0d80d00020016003070043d1542c02400c41e0368000380c46051984946042d461584640d808040944050342c100844400040b4000c1084c07070000c2600750251070240c0807201c01c41c5849040c0141ca010f24400c02042d6481d04004118079030301e040081c02d00320214000c0481040c024001e103c0b01200010060703800c1e41c0b000c5014060b0540402400c0c0160203800c03155800c1002c806015800003c0800c0d03818000c02c000b01c9070100d14003690302990003030000101200c0a580e18520110502e8008807070600741100c49194001203401c0c000588410348a460f0001c4046903103003191000502a009800d8045c40d0307584020360000c10111907010700614031240a40b00c248411000181000383d65000a1420b110030001080140e070094212500c0c400005005411f2810910f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 673901007 1250 673899757 673899791
    0x10e2b0216141318080702010c0615150914040e03121e0f0f01060311091215090303280902030a03120f0b06251b06030b150904 56
    0x10281820140101004030b1030b07030184500444a12010384042203910320a441c0c440507101c4208594250303014103120b880104011100405c116401810300c1c00703c5840d00e9950000325100303a04103d644a6296406000c00080e400030010311540500e0320310440750030080c02003214081c0c0150180f00b00c0d92400442c44012090080d9070b6502040717003040c0494030b1320458083c0a0146d4040418281300c0c0c0f034000a50380030728a01e0b2103004101c0303000d5441140c2c2c200002500240308601c1c02109040702400325000d00d555100784600c005038441e01034000c0084000202801030005810403a45410500c20001003091000b00c0205210140c0e0424a180100001d020018a00c0203130103505030040e08001c105240d0440074601c90b030074586200708040074a0780b098200b11210359243c3d41e80711104101c1d04188009520304800b5191003420391502d011a03543d109202032000702013241d01a42030304000c10565402d0b1050b0551808155031300d806480b0003844080c01d52140901051040b40d442c90384901c120451 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 673902257 1250 673901007 673901023
    0x60a030c03060f0501050d03020a1101051603030207110f030a0308070c080a020604020f1912020621070206070314061012020c0c04050901180b0703020f0f030603010e2b02 75
    0x4154100c061903203a0808501902000c80210f69150402000080506150700411401901a4050b2802d04c0c070940e9026066088104c18504012040c08140c681312142c1c154151010700c283c0f00143d44100354a010b203201410394516601c1450303050b0041186803004202012459410f00c1c000c030140d607a5002c1a100741c101e0303035009001c0d100e0104400101c5070700016683e0155008988003c10150302500b08001801c04079010345040405400c100b10a100600c02c0f00c1802d840103020300c1c14a12500b1920500340c0d0641c0844074a003000100b444546601800044d40140842c90180500b0000700411840010040e040c240211180701038003803403030300c07807203840f607204512103010756071110003500141d030b201c601c040d4251041d490318002c20090001440b032444400346c601a80d010046042d211040c046400410800c241602002905072300003028000b00000400c1c1e01d4000d48030308240080c1421a0102d4000c21541d034882c03003100200021802da00b001c040c2079074090b4403854803042003c80c141850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 673903507 1250 673902257 673902263
    0x9021e0c12030406050121031d0406080d03140f0c0910030e06070504091d1e12040b0432040f180f1704120803060625020f15030f060a03 60
    0x1002c81070108200154011504950182c0d1411189100180c000b660700072048100038041891854160300d016098010303000c0007000100300264055450100034108006100c0400020340d44078854450f120400d081c19800c1100f0b6040e805035441c050442c1c1c8801d00c00d50040b24406c1458201c0c144056110750041d0b480c000001c0107846103410070440241c0107800a020301c40c202410917000e012900c403d1450b40d5818900f1100401541c0c1400003403030440740704401a0f0815005207030944446468601c0280010200300011907501c13481c000c0e0f2080300c008240c40781c0252030386448204100314589404000d810380e04480001d00304003000c1c5440d00412034071020841da03052454041060103070640c0c52000c0c0324025881025aa01c072600b41c8802c5102d00e020304c008c00550050703044042041040034690042c000742100d480c1c04510000c03443c04a402450309041150b071100c04908504080d880400c00b00300a40354821100380c010004400c60000030084494040e44c02c00040341550f03240000c07002190 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 673904757 1250 673903507 673903543
    0x30203010e1b0d0302060f0a0204030506090307050d1b02010305150d050102070c0602010504170706110d020712020304050f0d063801021519060f09020702010909021e0c 74
    0x54541140c0e44440c020640240c424010140b03280d0b45007028004040b0103a0b241c2c3c06050143c0e522800e4141d107180180c00200c840b40d0030301010000400421020740550b02c0100155101c4010749826843d00f80c44210310010451101000b41001c42100c0032040d40d59824207000c00d150f584d030401c80b00100c40c2c4030704841c0e02034038200014003400019070051940b20701641032031a0040d1203d0082c2c1c2030300d4041c1c8005202d0101c1140542840d044040038148a500c181400f01d0602d1480c180c80043d80c116110030840c5913400a4442c081111049194108000c1030003d14200703454180040c420104444d200c5015000110308c084c2000010b03071211481d81400c1c00035590300039a001e00c441c2600c021244841c0490b03000010300d101503000180790300f2000414000709505075500b0482e100b15001320000c161001e5110301000c40c1d00c00b000d607190800351862880058403010b0701d00004100c11a56407000082c01d1042180450036015604101ea90080d00880d26503541c10305c44040c1d1402140c400d800035400c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 673906007 1250 673904757 673904771
    0xa14040504210306031506080a030809190c061805091b2104050709050c07030309020f030607111513021c060e0304180b09070e1210020a020d020a08040e1003020301 72
    0x1d0305907104c80180c0b4090260f6540280143d1581300842c0c5807030040324026030048690900013803048411640c04005c01040e038481c22140c1c85400c1c802207154500320703800780c8801380a0001ca030b80702c0c1e029a0302c0078540e90070280c01d51608001c18031105000c0c2a80e036945500150310305911002204641111107603a00c0640c26070009000320b00c0d0004190740403103541c018490001960050380c09000e0089074020701c114a07241082e038040e8000d1511840498000d02d8078070f08034409030381c18030003188a542d0540302d074550038400225050808014020303c0801da151501800703c590309010703040420641c10b0358801c0c094020721800c11010401e004004100300d00780302d03010000c3c1001201330000c8449411102081c81201400c45040d0742ca98404c60f90054450400112054461a03255200e05005480c6203888000c1402e002d0030625124007071000b091300007403a000019810000184504c4040c800340207649910317035800d1001d00c03403440791004000004002c070f4400503c846040c0000c56005000700140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 673907257 1250 673906007 673906073
    0xa0b0f090c0f192006070c2d050c03150105060a140a0f141c0c1413050316050109030321020408060405120f0f160212070f050a14040504 60
    0x6105002031050001c0c0c00c0080c48850061125206213007204448080c00040d9141082210806c812550642d4130303e6403260180e644a0300c0c01c85400c0d41d6203459101b6003c007d403034245640f5101006240368020347c13048806001c03131010f02507001d0640e01c04603141030703580d03035500022101c60b000800510780440002540008260300320082c5a080700030b40d01d1381400c10110020b02c40d15401681e08800b85942d8141300d8055211742c0d42c0c0f11a4108070641130101440014900c1080d03a60083d110444400f00d80040c14440c0d80b40030450310250604042060701300905240009101d50358a120007000d001d504041d0f00510314040a01d02c4001e20b00c40350440d12999105800c0303944900a45068400d800340c600b0190b140110602240d02140e566401c3e545041090344140c1c440c6d510000d21003800089440c010310043e99404a80021b254000d0010a00d0ba402c0201c00a04610154402e0348201c1120f80104100707014100f030300d0340500082f170340010180c1e61810038140e24000c082130700c45001c015604254207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 673908507 1250 673907257 673907287
    0x105040509100302271e0a0b041103072102040302031f0e0d050d0b0d02031905010207021206040309060804051908130f06090f0b0301051908030307030f050a0b0f090c0f 74
    0xa01d8820401c002c252504207040c20b2000000303140304118004000040c40f0110030b40c01c40200306001820000d5003034042c0410ad04160010345141c40003840c0281da000011602680040c2c0d43c9240c140d045103072600e1640000e603148180041c0c0d84e120800001c80300280320041e4042c40a003c1310000f03507417030501d01e80e200500c640d001410482502c0c5c5000c020340c925040018106105a9024004040180700d40700610864a4044401c5400350740820034800140c40c3c440b100504011004010021400d107440d005d000c40006800c210100306481c400c1002003400014000d44080000c02c40000710f0103031307080c00c10141c410664860b84611034400d0025005c00b0f001402c2042751556902c03400d00d00c0e00c4412850001c04c184c803401c985031809200520403440c1c4140202c0d20b0485a400020203e5500c2c600b070360860b04100c48550100742c0e41e1140c4501d034502405441d92000030380d0000c00c50707480d02100041c1c00421401c495801020818000385074100c0039400c0701c0c500d000342d81820b901c2d42115045452 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 673909757 1250 673908507 673908559
    0xf0a0b2d01030e0a030906201605090c0f0d020306061207120e0304030305030406020c010207050f0619060b0307080403110a111918090c03020d06150e060105040509100302 75
    0x400030b80f5202410791510310101e51900e070715034503581d000421450600111079800c200d404403905804540e0080040c10000c11144c0345001c00080040c1c181c2e4508030030800d2000c0024540401d8100c100151000198004211842c048094000580b25102c0c41c010403250300403950701d000718000741d0041c0310b0520f400c51000c210211841009000600b10240345903124003444c070004010817002c0c4007150014580c0e0300075108003141c410005040c868243c540c1c5240c105042249080c6410600034800020594281d075200103000c144103000c3c2c289804a0050a0721000b0b02c980100003a41c0d002c1800c0601c60b0030a40314460f91101110005401030034880f211b880111485d912914001e842118040e102c803924500b122054035103102032502110b01d4501a01c90610100c0d25150007510100045e551001e030081c1e441d004540010f100e1044070b45c98000d403203440c2c00209180700da62042248682c0c0c0300c070480707007514019a4130000d072351600e42d04c3c89031800341500000c0d440042000407880601345005211 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 673911007 1250 673909757 673909759
    0x150b040203041b0503070518090a120903140624042903010f0507080612070801050114120c0a140609060409020a0206130b06010e190621050f0a0b2d 65
    0x324102d80c0c4c40d800c0555884e07080c030a094003e6071084045004504400801da401400e18056800c541040d903038038000d902d00c083e02c040214407010014014030620080301402c21610340014052401c2110119685007a45501d18042e03071800741241040c3e440c3d6800c07400001c1034501082122445100c1d811034040c207505140c41c06903180c0fa0f1910304804541c094035000e0b00c02d94071030450300d0700c8560912803100031152140056200f030810010315114244206402000d400e20002d4401c840e032740800c184043c0100440c20181e0040006261702e036500c0d01048202c924104c5103412039600c1a02055842c02010a06540041c0100d000182a0b1594004268401981e42580c0c501c1d40c81001ba64a42107510710040c0013a0ba01c0000540194041c5030380c81c80c4c90700010703d241c1d10f0b1402d8420300c2c11114800d40002c2d0006d002e6600e00114000003580034041128035200c00d0003589000715400b07017500001405100d85079100e810480060316084002e000480204028080c0075a100000c0001c030080c1414007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 673912257 1250 673911007 673911053
    0x405100c031515020708060a020a0f020c0328020a090507020c0916030203040618030906020c01020f0c0f120304141806030c15300a0e0a150b04020304 66
    0x450425201e0302c91403495a802c0d50000d0101c80c1400c2d00340b008aa056a070f0320066208078400880c00301401c1001d01d101d64000040942d903080c0b01100101a2842c2940c0181594402c03013400c08603070b90104100b949108100a80f6000c0e810b080c0d8402c999100c3c10300e01a421007001e0b00d01007480b240c3e64010030303c104c1c51902100c0c06606054107000800c01d04540244c0e41c030354016030040c01c180c443e030002e540150003039401148001d0f44400170101d58680540440100740300320fa0800240b601808030314940d00c8240050003000c0d4407101f070b885d00c801c480c1031076620901611002583d10f13520400407000b250100c0c01201e40765500d8110007c580038601c1c1e03206104042c0c900b03100c0d40140d140c100c1507208200c0038000c2e050f02030f0b40c0810320100e0b01804018a04010003802123240071007400e00e440e040c1e1030403048200d840300444203210b0300014028142210290070800c0b100d0911100143c51031107107600492000007026a003855000510181458540c014000010700c02449a8640540d4024240e4002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 673913507 1250 673912257 673912271
    0x31116031a010e0403052b021b010f23060a08010615110102040506040e3c090d0806060a0c0b15030c0906220603020402070f05190f06091a040510 64
    0xc5100750341c0044030003c1c0000d1040042ca4080307d0010141d400004400d5413001154480025a0007684c1041c10266074503003030700180030b815130700034082e41d01d0005480408006101294005c01a1084201c21941c20040c01e0000310f0032645a40389140014070020000304450b9032103441443c0c01124036840383d400144501c2040040711412703c215011038100400040c9014a081f6641c01006001001c100c1140e800780b066481d00d42d65406601807071420b201100010075003000500da81c200c400b1702845003940c4201c2c41c04107203c0c1c1001d01c103904024101c905c561500c02c1010308a41c0c001074142c000f00603400d20818811501400005038100583c00c60585006160361810f0100d0300e40c01300c4005500c100802ca0320f50340110a500300780700b030341000800491078549036000710b001c0ea44440300443d50513007141c640b50140f10090161400003000103045141661072604c1c0d40b1004900c50782d0152401c2d0f62800c84404011400480f007003960307000700b11001240307000d041464690003000840c118580c02c001c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 673914757 1250 673913507 673913519
    0x108182e1e1a150c07090e0304030c06080108060f06010c21180f0e060d0606140f1207091a1e0a051e01050a0c0605040c05090c09010c123b0603040f031116031a01 71
    0x100346043c1d6000c1401400c0d40ea03180600030f548204050525414803108018000118075083c003040945a2080d570a048010282d850042490000c1c010a6000d0000e81c90180300403180b03020403e048845001011708552159000a0300780a0300060080016207003050020b0082c1404040c107000310022544890f260700020b09000468540301d140130760b20f40290b10144064001c85c1e02010f500f65031501b002003003842030008618088811024400c0344210700c02502e04074600801031201908043d1503c2c460514041d07010b1440540a443c401c0c148880861550040c0d442005264450b039000801403000b0b06183c00c1000c00d42610b400303200d02990342c000001d5003081e414400c0720a22ba106940d484209092601c40755254580c9002c01010030481140a030028011111402010680140031102c50044000949003000441038814000d400070720400020440c10742c1000030441d01418960b01104000b203005080c5000007502446440174070380c2c080140444101c4289040c03410209070aa030341d072500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 673916007 1250 673914757 673914767
    0x1005130207050c040504170408010b0909070b0a1b060204090f0b060a0c1e06140a060603050106090501030e1e0a020108182e1e1a150c07090e0304030c06 67
    0x24401400e50f034004800c025180c10700341d10003075100f401030113044000b804080d40e518180c1e1055100041681d10b070342900d105450304845198002070440c0080400610744090b04002e4003e040f815028040440c42c00c607111b004120a0842c00c60303000c0001c545d19a10752140788010200365405008451410941d4100c40c1805402c50307180c0380107921103550900c0b05640726290980d1600b04901240440d840040000d41e1500078801c090840112241c03c82c540003410300c0844090ba070002d0100342c10301e0010050903400040040c1a54801e107004102080c0b42d002182c43c11180902d9540c202c842e003d01400481340106a01d90340030b101340e8501c202e50700d4000d00d4081d05c1d02080a00707030043e0040d41d805604c100240d807090041107091542655110094040c00085441c0044103401e051020310341d55540f1040c6109207030000340c0700d41c494941c80c50b00c0000b042092503c0180010700500000d071105014000300022401017122135424081c6002c0000700a032a60414401200c0e0421088800300e203d500403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 673917257 1250 673916007 673916017
    0x180b040605070b0f0402030c040f0209130c1b03080a0c020109051f0b04112b0507050703120e0c130b06070c0509060a060e01031808030a060303080106020703020f13060e10051302 78
    0x34010308c400d440020070070000307092030300064100e02d90801005005031180c500f40d51209045441c0004c42c241d5401011300076550b01039007100a02000304528001942141d041c9401a4044d100001d50b000041000c4e03004200202025000c1d2252210440800401a40b00c00018100c2c080c180281c4111100b0300c01511230401040401c202d00340038a200d0b02c80174269a0200d800d903203440b105900d03058226402101c20658202e0002040012071805040c0c03c21240501410301640400103100d6180440340c40d58443c10445105014001c0328030a100031315007103417040390070051000d941c80085290250720800644280c1d8040d80310f820024681c2d01d40800000c080b039542e170301c0d1380c08900901c00044004045401040043e400303030300003140110b002007001d03501c0780f00c40b80741c009117507411810b01900a0741c05900400855100480034401611012801c2000050595030480c207a03040308840006800d40e80c1050030904c21003401c1000d647e401401c105d049500a1740c460000001084484050340310b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 673918507 1250 673917257 673917259
    0x2090307210b0709140f030a0f0302011b0509040b0105120106080c0f1c05010e0c040603020708040b0307020a0b01120b040f0c09020f040e01080307030906180b040605070b0f0402 78
    0x2015108000c00401d00e121002800900c40240319001002d549003420440c007503580a00003214198144001e001643c019070350307242e08030340008145000c640020350310820714178024181c0500d070a1210800d4001d4106c0c00c0d40c443c1500380c0040d81100c41070000d0154012403022444bc5060041503804ca5008100704c1c2d43e000072140327030f0109603820540b064900c00e03170140003115480410010b10700c9030301074100602170031905240c026813034400404000040c3c030300c1a00110079110412045c040041280400c80d4100c070704909000d1f03181d0032107080c01036a500456109810f5480700208010000d0790100e0128169886034007a0112030340c849201f07900446180a004000c0090798003c1070104215105140d1442c0c45401c402240f00e0319482290f0a98010000b0000f038100041002d0011072060042d090140500e08015070502c1000c3e10010903403c080e214034424000024190304560340c0003030b402d0010b001840c5c0995990356603001c00802590100c1d00c16079401e2031800218070140e031111901401a60 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 673919757 1250 673918507 673918513
    0x140318013206040504080f0304150c03060504050f0c03160c020301050124037706060402070215040b030412020309030c130f060803040914220f0203011518020903 71
    0x840e07c04041c190f201030070030340303215252035520340c010b83d0702d070044881d0254207a0703010410500c4c0c5402c4c0300903200c014019001c2540043d04104030a0900c906aa070700c150181e040e8103901c01c00c400291140700c250040070390154201000070407000504407d05020300c6c00d840010000b490440d03000c400303c0e040d95551320b222448407020000b5808070702c141c04582d1309117944030001420455a401e1038948540494040035110410500300ba03a102069030040000c8174a50030b0819000d10404640741e45d0000c4c411446144c0c04140007066460301210316015900c0c0d6000d0070381d226100e04d00d1a140341c004840c1114010034040c491540c0c1072012040d214011030150041c031480c01c070142044201010b0600700c441195075084407800f064014001d11008050040c041c540d0303203091051007410b0794006019260500b000e40c0c14080c4100181084010b4000f5220902181c0809480d200d100b00c1e40004001c1c4d807645c00c001402c4812040148201c04031609039039400d80320a44a10450305a015101c0e205602d50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 673920863 1106 673919757 673919767
    0xe0406080f0a051b150331020913032c030709022d03040f0206090909030910020607093506040501060614031801320604050408 56
    0x103159000c0a5010301c240402080ca000002217803421461800000980d40d00c031030300d801c020144a4420500c04074400c00242c6145102004800d910904060b00820032040d5090640580e07070750b040d00d0b9008006e001038400b80e04000c50552505400d51100030408140e5414003a0703c0142042c3c03080103840300059020104e00800451441941c1100800600c495078914000e4a501681c441c00484c0344030160310218985001e468001600034a17000c0510440900c0440640031800040e10038030b01c03080c20450104d0351458290794601c00305801042c01d00c6101c107080003103609002030803051a00c03c00f0300e40b034a030340400c80d10b542126a504820240710800400703014100060606260066000aa904e03071083d203440064180c4480784190214001003050039001054010b18092104001f02c1034915500c4000c08031507609411454403d000031301e0707071520b4482d6a008581088900e03041c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 673741007 673920863 := by
  have h0 := BRFrame.cov_init 673741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 673741007 ≤ n) (h2 : n < 673920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
