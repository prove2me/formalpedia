-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:41:06.016505+00:00
-- url     : https://prove2.me/submissions/42915933-a3fd-4c84-b21c-ccfbd673e5f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 914028776 ≤ n < 914208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 914030026 1250 914028776 914028803
    0x703020403032c0108270c010e010201020705121303050105090a0b06030a020a0329100303140301180b130c080a0b010e0303040311040213140f060412110f100c 70
    0x4900025960202c2000c1520f41200140195409406415000303008180c4240c04903824491520440e501d0305540385950748903001a465950308400c884c221150284002c0d8541040313501c407940d417402d280c11405203040c40018a1040801f80e03a07105006035a2000c0240035a0070040700c079070342d15a50184c059400c075001402040301442d0000344821803a6020789410000e500d145c0f2848002c0002002040444880c0a4040c010990240c032041c815501c28005090032400d509000304041c81c220601201c06000f04018421250720005901704502d2030325000c1500029000410101c0c143c40c2d66090b0786504003020802e40e40d0300104614400c19030000c08001f90101000115000001b010165401d900100702c14008a0141144040c1d2042d0140c80580307040c1140306418401180740c1c0c0907003d080704054015615240c1400d482c0300c0014215aa40d0030319040114001540d9002c070320040030100200007204481c0c40f00c01000842d0305e4001d04007900200325002c0500f1114854408403083c0010030300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 914031276 1250 914030026 914030057
    0x3021503070e040e0607081005040e16090605090c160b040327140603101a040f0f060f121518051806010501111c0e030f150c0d090803070302040303 65
    0x139182c00b10800c00014071441e1a44081590311903405031007880c01800b05000856107844500410b01011800c0c40108403903041100316180c40901c3c0d030480303000720341801800c1200381d84000c0c3c0d443d0040c03c040c4860395030350300200008012180c020402407980c48050100000e040d044030748a4188250400c081e0082c040481004d00c260130103009812020406451482d82410001c000d1944117414005281802c1d4903071180003500b002600501640740070008041c420140c0003401e010007800b015041403032840c10124040c20803004414840b041000c0c020315010b0703581140d040110f0480d440398489800c030b500c684103038000c80c1000140510355810013011640c14104142c1c640045403451014054990803c2d00440303a005841a0303811080c4a0708150004402020075960104405c646230442c002d0b9090052505140e1481c181150f5034000c0f0000388080c0f0a40240c00c1c1d0b000c403032176000c6079403500312200300002070030200c1e0050000c032000b00400212075056030051059a000b0344030000100382a44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 914032526 1250 914031276 914031281
    0x11517010501050f070f020604090b032802061c1d07120807080702031c05090a0b0703020607030b030f030c01050103052e0203040f0203030c0d08010f0305030412080403021503070e04 80
    0x10801c0d002680420446540c00100006800703541e102e02e05200c0c513100590009600c9400a400c00445565540543c3d03000d40340c00c20503031082c101c110071081410b90070052a148a42e070410400390003075200060340c8082010700144007024841c11802005a09019034070030400e440c5580c4035070410b02c5400350210703d1860010950300210340c001a8540f46c0101540c500c085504640022601445918110442c00101050b00c0a0614190380c0785511120040d003045040300d526030140030035820802c0b403000881c1e400b00e20700341c3c0078a850502054039560340b00884e28003940900810200d000204001d62a0ba406412440c1200c1c003900c00c440354614100902e68001d0001805440004c0b1032109180191180750007540e40a40110340c40080d1f8000b94020a0559108180c1020f941d001080d4400c0c1050f00701110034050103081020203407150039551095602e11a40c01201d145910012050301000060300c1100e0240d42d001d019680350220607842100135820a99401001c9054926220800e05213031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 914033776 1250 914032526 914032529
    0xb09010f0e060103020609150706050412030218040c0905030d080103060c030b131128090806062b020301060f140613050d1112031c060e0403050c031201151701 70
    0x4074041d251592130765003042441e42c041440d03a43c200c031784000207003814170606000d00306603402580c020415151501d8074101005e01d1140140900d031050051800401110f50504044c50b42a0381c0061003081c1006c06560081d10340d40455070601c0703044d400d007180d65800040107040300e02c00c89091040b11001c45003a41030303441d02000207401020f82c40d20400e0300c902030b0304080169034071000c01c40c1c5041e01100c41c04080580030489000c0018030300024046840d030280300d0000500540010303007014101760700000e1603c04a40a4140302e00d090800c074410203c4036141c41d52000e41e00500811030b65964445862140c489071292b01d0f801040f444014000307046c40d208541c43e10400c0014004040e051008000705000c1400c02516100c07454000030000e0f46070000d50002e14902c4800442d00c9124a00307074036044040b42c06900401c43c0c00c1100401c00c4141e5004036a030020350500348240c03180c8a2441c01841c5004203420320042444040000403419a80300c840c0040207070594544501114941190b00c948030207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 914035026 1250 914033776 914033801
    0x3110d050901050708040e0403171608011202031207060c14090a0306050a290f0d020604050409082205100302031009020901020705130609050f010e04080a17040b09010f 74
    0x108201c0e01d0640c03040b401413040074450030026051548032001c02251020403030701100411264018009100f09602040342c2c800000c0f500b000704004012070007424000184142008040b0011002003103540520420040c80c074903100094680740142058009008854908808204503010302c1c80c40e5800c01c800c0b1018600050941038480f45590740301c0c0e0040a005010014451740c803c4411405511110014084800210001d507d89070386820440120500c10303246218000c001d407080016121201a541110011200029003000b50306180500348203c4003c2031044031090b0340010858154000d80081e507100b5a940f0b16851500329040c1d04901c000d4401452041030103001708038074003054008090b444d4041c819201c0040d51030b40851040c0103803100311080f0a44404007417007100c0301d52050a602010a4040c0301301945095803c40b501100540f002d031a0b03100000b500b0181d0340c0a07207000039a1000d205004145480d0604040803e0001640d0305051035003060b030ba00002440303a015800c1c00030700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 914036276 1250 914035026 914035037
    0xa0b06010f0306080a06061e1d0411060304121b0b04021002030d020409021b01020a170408120403030c020607020f0717120c0601241202071110020a03110d 68
    0x89810054a400c40610100c104150701c1d480003040d50079082c4014841940b1640c00840c0300d03414000d0a041c04d000b08110030a00340c0441c5400c1210b80c40340c2c403d1046c0c41c101d15882c10b180b5100d40c03c00051140390051800d030040c5000082c00b0400c0b00640d48080c0481555a9000d850544144118448083c80b0405401c0421035000701d030161030a200841c00745030060040301d02c0c0c01d400c0b400322016130b00700d80d10580d51725501141c42000c4104228110100d1207400000318500b90020a0103010f003182000c41000d420074140024040104400071925114502803a02c1c8440c900307890001e02034081160034400501402000c40c1105000003260084c0134001300c0a011002c2c00d04200e030714120300c1d50480351b20511450b070000b0640c0c0180300c002d21030440c002d005044a5030410806824200c12024031280080000d40030b0b8251681c80481729082883c41d58026071348054a081c030f101004400b00c503e070780c0f0007280c6049071002d640008136030103000d20985401204095414040b41c40e5131070b44400c1c201081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 914037526 1250 914036276 914036281
    0x5070305010f031202010603050f0d03050c0309031c060f090e0120251a07140a0e011d150d1a0a05011b0c1e080607090315060b0d021207020a0b 63
    0x5640c02d24800c14458130f803000099035581e0f516903920700603003a01c010120b504000c2001010075131500034980e00040c0c0000441c41d50a003220266500e2056440d80385909080880100103402c2c0da400c10310080c204114085121034850340c480009003449040c54803198a0300110008000745c4a85000c00001000312040c24400c003950082e030383c451454030310501300380544030b55000640c2d1402c40c40988042001c2c1c0f005c15180020000d0102107140903403a602e0034091000950f00d0364003484031544400c0a181c003240702480a16950a004400380e0140d902600308146982c02d90f00f1080a40411562140d081c01203228081d91840c1c0d80c8203504500d9009000c0c3d0384c050105502647e0510129441041001c191041c0381d1034144846441e0f402403803246400300340c0f800080c0d0580780c801d4082d0030b086016005070309052001a2009a2501c07005040c002007103100344600e000d5a11640090800c1d0190b107a4942c81c08880c50700a500920040fa901449c0034045170703806200089804031030390700c03600b030803282e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 914038776 1250 914037526 914037533
    0x8041b260c280b07050a020a121203090201050903010f0506190302010203070209130b04050102040302040510120b07200f1006030b1909020604090e070e070509090a0e03030c0d05070305010f03 84
    0x425051502c521540800348000415494090003040b03418000d1002d008504028810041000c026600800400b1034104041c00450b0380301c0001c3c2081445420009108001c0744010381c1d01d40566455603a0551a1404400e01070301c2c00e4100380e1040c101103c12926000799500c2d002d81d102c3c1c040c04007900580c020301c0110010300b08500a1504480300748481e5020081581c1c542181b100304a030700701e81994003c1020011410680500c80c0c02c440e070004216441820302060814014043c2c8024014804103070205403418027540c03032812030349241200b00c00701c07124248925036905d621001c201c07194442c1c140c003580380820030f2042c82d007500ea2298040c855038031b80149007444001014680341d0300560b80d02e145001640c41d074004000900e504c03400411780c034203c1010f131400c10105e50300450400c16800100311500740d00c44e04413182150111001205a15142e01300002403510708410314561000109214a032641e0700301801030a00411818031490352446012410340d0f03003e2203510036000301c040051000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 914040026 1250 914038776 914038819
    0xf030301062a0f0305070512091c02130203070c210203040e10081518060603100f020903070308090a060e01021905010e01111308061608041b260c 64
    0x3500148110110068100e45810032107941c2900f003140400d000281d450304202c400e0003169210a00302c500c050800036540045081104c3c56944084c0813110100042d04640e074490240c41c80c0800c980c01152a071903e201e001d01803402e40442928000d900042d45400c0c020048174028843d60f01d5809182400e1030055200a11034004e4020602950950270118041c0f004212060381001c41940740c1c4c1850810101400c1981e10f85d04c1800e05a810034020061962400600ea060041350841e001a140d68140344004c020700440d00c1c0243d041c060b84000100b80001e4202400c83c6210440d030405900fa9680416900742080d91042800f40e08614110940d01d003403e40da6607655400303040089100e40b107184541e401c54510301d03c1000e950002003581f1002e5052420110082c0c81050002d08243c1803400700e1109031000c242c240e008011521000404110002e41803910004402802214440e04c41d51800e2900c403a0001080d0144489910480b005500250740d140c0ca01024000d104003100c409814983e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 914041276 1250 914040026 914040077
    0xc0c090f11030c071b03120302031b0705121308030708090f090112080313140a11040207030e040203100e070e010206070e01080a050901021c02041a1314041112090f03030106 76
    0x2180740c1d05e00000c0801d031035070418800403405680060b42e0380f800d241561401c844001144076100028401240025000a2244a002003101c18203480b2084d988030081650026001401c8138000403a21608000014001d08500e47d0200c0342940c2d161140000d0280400003403244941030744101d19418040380080c0b00564000308040001d03184c864950316030540c0d910b051112403c0d2940b02408810601c00005070b40250107804a6040d0700d8402951801440300002444191140d60b00101041d0341410f0303184900c00034444007085010510f00854080d2203054840741c2180503003c0c20000682051241d00f4100125030145c481c403209446ea211040000c0200500700c4102d91f60800100605009800484800b40900c40015940c2c6081a08027580e0501d03040d5140800c41e42406584e950f41d1007804608140c1c2e008509041c2d0104600380000c0c003500c0c0c080c845c0481203030006003100c150841006040c6c856403828007140e80d0a200f0640b00ca9803440248a0f0f400042d0f001050030400051410101c80d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 914042526 1250 914041276 914041313
    0xf0302090a12020906091504151e060e030a080706020c0c12030703020f0d0f1b23010533011106010f0f0e071e0c0c090f11030c07 57
    0x142440c00c400003240c070040e01074200c03525001c1c16120700021407420450055000d02c2c20344000708941041c5c2d000d200c00c0c402c0c0185203803207a91900b05048003000c1100541d0000d000f10381c940c0140d0039400540712079144150040c840040d16090903514141400212448080e620120091820025844800007504100c0d0004240c1c00303842d00c12541941e9001c008c4071132910310700c040c541d241d40c58580640782c445081c0c11740300079800c000c02002c1802d4000740031000c01219030800c043c6024500c1140c000c264403504005010000922a41e1507125010048950005c046e0000b08203644800741003641100c90104040c021810700314144d1080c0d00402c192208541042c1014180000c07501902820242c090f00301800c52080d060080000000b1050460300420700c4079a14540c0c0e050000d00101000e03810134441f482c08001008000255200c1c643d80c4400c4c2e5045441d1220f2183c42c0d008080c09032617003950940072035003001030032040840705a040700d00614110040750b01d819503075aa8151116560590b00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 914043776 1250 914042526 914042531
    0x911040b060d05270f0a0f0c091802010306170c010e120703320d080c04080607120e011104050d030201020708070c1a0339070606080105010b09030d0f03 67
    0xa000b00c00d8901800e0f0140090180104005482c4108050440d9900c1034000b8250300458000c0394010010803201c0ca0181c00056044804000c1d040c1417842d0360b12640640b4035103250141c0c1881d08110740100540040c401d0b82c00f80601030360380d4240030705c4843c061598100d982150040d081d4640c080c80c0743c0946400040c0000344060b0000c5041410856603500540b003482c2d04058001199402010203aa0f025500005820400321071400b2a035640f4030120443c01c0c802e100b00411980c4c0860025140100405011100d0703503d040720006201074100c070358004200c0e0078030400c680c48500602460740c254203036282584c140751424041001e005d500303420070340079550300f00403540100342400002c00080c1d000700240080946000c440c0100602d00d80c0d4800e00c215018030500000d00001d85100d40e482c00858a00b00d5034084990800b60600303124412400c170404005440020400c854100c80101c4007044000c003c50380e40d44030004110b1058181640c0c1c540c000c0c140800809014a0000140c0c46191800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 914045026 1250 914043776 914043787
    0xa030b01140c01020409140906130507090908091504231504030b040b0f061f1808071706060a0b0d0609050c0702040b01020d021009020609040f020901120911040b06 72
    0x109062507125880c0580ea030f03500010309014070410b90003096640c21a050340240140f40043c25191103003c003821000d8402e00508008040c403004002c1030b0090300040c041000040c02d80e14105034660b005c60209401249445048618180c2c071509807411102c039070350201d0101d41d04032014943d144a06403119484400c8003001d408030100302c4050005903214000c002c070380c1e0410b41407030704000790b0051440540ca201d640420401e51606e0228047c001b0b083d40505d00c4501d066281a42d0205e00c104030780c0d90004102c2030000d17446600103001d00469001c00d0107541e00c07107403180b4030300d0f19110115000ba8110203240d1042080c04584802425010340c0c091000880580b1141d41c1d900340c0d807040d9400c131585c042c0451010298a414400d26505420900040480184044010b5260000b8040003018255200244003d6440e20000c48401000c02001001000b400b50604002500710403812070024002c141121100c0301a03116500b200c0d030700700000c1203821b2114020000601016412507401c00400d028 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 914046276 1250 914045026 914045057
    0x1c1107060503181f020309010209040e0622080702010c05100603050d110102130311010c020418051606050d020921060916121103121603020705010c03050a030b01 71
    0x140801500056540a80da4208030070152412030004461a040f5001310302003139200d9248001d0121854581e074800350b184e684040400340240207001000d41c115041001e40078902c1404a0007a02c100748007020540706800512034502c548000c000b0040c43c820040080b0001356002d007090000c5244141c080b40d900c0300034401001c0648886910845003070b03002d800106041c58101c0207500c036082c2079070000c50070b15074120390184a4620b24400a003803d05140d441c0e201d0341c1d112719080c05802d5000340007400004040b2040394280e2607030b4230b01510079004e003050000c049070007102c05004880890f600c40707003880c4101103c02c00030740c01a5130a0346c7c060304080e03102c0c0c07800b014900e40c0c8013210904006040710346041120141441c13218041c000e03445855540c02d0160299038110700071159044140c2801034a01000421f14107600c851902000f500d01060b000c00e40100008034500f224800d500741c0300c8aa03903910043d10300c50026440180403d1007400b040d1200c510980c001d045002c414504000002124403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 914047526 1250 914046276 914046283
    0x110405062d09010b09062a01061206051602150604061d0a05070206060d03050304110d05030703140909071115010602010614060703170703020903070e070318051c11 72
    0x80c1c2408001d5001041c032915480d000a24500600200c03691515080c500c1000a945201e0038061050200d504d0800200c02400f4078400b81c4a0641c15000b04070701915280d0800d40c90000641c101c0c5e060f820100020401403078049024031100e1250000c01c014091150060036104000b440c2c2d54005507a0a4006803a441c503194082c0329980c07040404000d410511035440c1540d000400003019544a2420700c204c640304c51070080240f83c4c05180446d00d03500e8074640b00b90240d0f03180400b59485803820700070005000f008001448814420303141c05141545149455a55000d0212180d40c00103680d000074140e00c1c00307112200e030080d03c11402d44000e24907544031038075212800c0e000b680043c0e41da81d000b8001403201c0b285131007241004441042c00c052503075070000d00e20707403a0007404445403007842c01250800d40690160b8580d4800281507501071901c80a0f0131407039940c01c0b0342c0c08c0c001034207022039403807159041d13000034001c039807c000500700000c014000c6100055183c0c0e680c00c1000000f100b05c607050081403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 914048776 1250 914047526 914047579
    0x210e0307060516110d0c031b03021c03110906030a0902122a1e0a030c090c0e012d14030a050711120307030908040803070f060f0911040506 61
    0xe150026590402e0019030082d8100150000280144d140000b04110380020380d403516544146400580c1003040c2c5411600b010b140c0c1060401035000900c0401050340118401c55250508250101c1490b5442012000d5542000070341102d80c108000c88011810004d00841c1c4c424071501d0017042510380c60b0b012948800218000300d15a13088201d58051844011040300031030000c000e90b5968014440000501c602da02e01c91011500940b00300190450700c6070200c6000035a0480f20020b10255034509003405451115620702c00201c61a1103074030030350b02940c00410b20302034180b4031112001d410b090358502c0040c001203101c18401100b034408146842e080c02503100307862000001c9814201000060007001c00c00201c880325421090402d14651420030541e544500c040c600400e07080000c1c241f1410502c02c50304890004d00000400700c0030f0004010348145001e02c9604204120311748840d1080c1140c51105000306500e040090450f03c0e4501600259004800202910307103542c4950628000d0344942c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 914050026 1250 914048776 914048783
    0x605070c0509130c0906081203042301060f050108042316030606080f19110f0a0303020618030f0a0c021206010f1509030317040c090e100f0606210e0307 67
    0x21010f04004012400b0150402014024000c2c0441414021800e40700c0450b2020345d103845001000183c148402a845e0b204a240c1c144500f0b05149858802540a0441e030b001c0d2601001c400c0348c0c009101d521600f02035104940111a40030302d88030000c0300e111011030b80701806030303a0b206000c3c0556001200102282c001e52043c200014881d20303100c441410021903004405d030641080d01c455140c1c00411400b00c00d41c0c2e138008024100c3d0030ba00c40c00911203140c486512608100780403404410150005100d41c00740100010740160150254086560792040241305021418103000c14203074140500901e0704d0485c80202626540d90030b541c04c2c2842c0220982c040d01210400b0142080312051000c1d07052450b0085251050b20142582c6019090780c800c04030a03084021300000040a2043c140440d1001d03003e40300c0c0610000100010090380c0300d81d050355102150f817608409249104142c0b25203c00c5401c2900c03401c858804074560791054045450a401c802602c0b940d6045c1c010354203100410a4511 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 914051276 1250 914050026 914050051
    0x5070207050613080f030a140a0201020c1c180302061b01020f1201031a060901050f03012c0d0306080c010323090d0305010503030c150717130512130605070c0509 71
    0x2810340c40502d4003105140c81e171100c0e0410000396800320761201c0e4603082408040d00d45031b40e40d4403d400403270091045030108019030041311a042080c0c40e120024024045041d900c030301842c2c4010480a00203507403480025440031007000b00000440c0c2034141495802c442740001801c2141051014460344e000b03004804124070b00300010b00c200301c02555082002c1a69510340d1140340346c200f01044280506005091290000c5080c814150f60250804010562840c0c60410000b241a038400038224000c5200e40031800f40d800c2c901c0039140b007446000111070704c00f001029041507420055001704044a803880882d00141c4408180c61070703000d40c180c000c81c0458014900c88003001d100134200c41047e00860700c03a401c2005440301d25100003c170340340b8162445058605689410b0401d0311928404a40a0110114002000f03603240784c8000170b00590b805042540e04582c085480c41c0158818196071003100340d805c0d501448958894406407180c0c0d4420803201000d16240c44c0041e60400f411280b0000021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 914052526 1250 914051276 914051279
    0x18040f180b04120c0c0902090a030614220203070909110303131503020408151009111c05010f0b1c110d0f0e03070f020a09052502070b0d05070207050613 67
    0x26402e490603001010740c1c07400303413825925aa980d070760800302882202d0301e0380c0e00401d40321a00d0350780b54850300043d980f20b5000c02150741d02c0e215814040704101c46010719114218405010358a4000305801c142e035004000d81149070801509800411040c041501e03c1d030200048886651410802401500500300000080c1072030200c0c2c0e017405000322a00d5204240c01840108007040000481c1d9500a4001155005035550092240355903103495210300c4406042c604003055848a61005026290036407102c15102101c0d0074606081d91828403400e0001080c1100030058500000041c003107400c020b11904000c010014680c2c2e050380c4510107016807030030001031802503500c400e116410240100314020f200718070910410640300d0090b0300c0050000c10120480c0800c41d501c101810001d0140054108414140118459009401002841c11032000c85000c3c01c9182e0000a14004039000341c01c2091805280703100e40806004c010b045001036114000020030241d542902901000074000481d61009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 914053776 1250 914052526 914052533
    0x1d0615072d1506060c080304080307020a08182d0111031c0b2e05090102030f031627060c0302010207021203191107120203070e0f06100518040f180b04 66
    0x183c2c8254411400d002242c01c4040000c1c028070242c0b07501507040311585459540700d0909904000d15000e000307194200004054242e82e020364901e1038403034800ea9060400c10b07580d940c0c60081c40e100051700318609100140741ca8003503204070141140981c005050704d0420340030a000b203c01403105060181116111500302d4041d00700059041c6d034601d0844021901801a90f1601442e8000750003140100600000c4048040e40200119804a20007102466407442e280d085520140c03a0b4168900002d0014000106840d01c4120080098000d04071010030030b52505d00c05603460090390703c08905554080c003150001d0307919203c000e414007407900702440c0d55203048507003118641c0000d01d648041c03003030060640150303142c009140781c140d0b051440c03484c15070f4000c1d00000b0703d054025440100c20404031410000c8000558092038010002642c480154803180035040e00c083c06407080381e0751818a81c0f900902d592400d50041340010843c60300014822042d520758a030702240380f0354151012040703403040c0b0080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 914055026 1250 914053776 914053781
    0x1216061b030b011809150e0108160605040e060d0204060b070f0615081903110d09061b02030a15060503030d051801060302030d0c0302010f02041d0615072d15 69
    0x9520074070b44440241071888a031050b5038441c1c014403007a55918488112400550050300b8007400c03010b8699841c1c0e6948094160b40c81d1843d0300d501715a040e802b030000403550300490540b0150341c2d405420100e290340386814002042045502030f684540c64440c0001d11102440050141c207000d20601503000342d060a0040075110719004038401c054101c501000201c80100e0075001c44201107040103032000f003500b030441e040d2500c19070342c00d8603000350507075003142c3c03500402060101e44554a600054050482d100390000301c5001c00a901900700c0c0c003506000801c1119080d0001145200014800d40c072980883d203581c00c0903d1031121310b0341d95810700181d041200403a0f581d052034403000703002890450b0f0100e070302c074005440100f007840012603005003054000e401c01c090400390383c04111340b00ca5440b0b40529502d40203060300e048102103000070440300d081c4541e00305500d0b491802c900e4039003503450742c4c0c18514440030700c0b070200c0304002c02800000030356a0410318540140526440070000c0d0070b0303007501001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 914056276 1250 914055026 914055041
    0x8060a0b120c060c010b0406150905030a08030c090112180212010c21180b04120e031f06050d0c080f060708042003060108031306020106081216061b03 66
    0x21907410940080008240028205031480341030311081d0700e078403007004240e002d04180ca00703080d8028248540407401d60301c030003004403420a003591074560076503480e02070640f06e00340c558020700301e0b400400000d0325015038540207104002062400c448011084510941245c20074a20302890619101e00d6800f5450420016103100507200000c00100714068006021022131105211703040501d03845034090500c041e402042e0500e80d004209807480345c2072429020580782101c0441303502c1102d80700114458481c1d0503162040e88064000c020b800400001501d500709036030040780c4503030b4076403d0108041d00c03a8100c0100c990300c80e41100c42c207c4e040080003400c10034a2401e042c0250f008070100030043c0e62181c45e6681040e04804011084c45d894064010000c03980701c0060740511810000241000000004040d8100140d041d180d038a512640d00301d00360760461040b0342c2c155120740e0f020100c6120190040c540f0141d988000382e030000007a950081a158038184800501d00c0c40c816081c41d0300e402d0300580341c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 914057526 1250 914056276 914056279
    0x30a060e0f01021c050601181d0705031003080c100212071709030406180509130501230606360112050f13021c050a12170c0a021608060a0b 61
    0x1410014420680500c0d03012030341d400a08a6142c0317010500c6640116044283c2c20006002220305d203842c4e000b881c00d20390300003d1a04800c01690001002c02d4820801d032401155480c2c1c0403000e140c5140c41365019504485140c1107140600e0700e4016407103040380b0040600011905805e00a03250015000d0000300a1400301c04a002000c0300700300b00d81801004640c243c0728a070178005800400001c5003000c0507520b0f000340d0780041c035900c1030049500800c20603541c1c0c030344140300a0180071423075904000d030030300c11503100007040f080c2d080031415a1038144041d01611020081c3d030407035a20124400e8a030003151941046c840e641c0381d01e950352103503404008000f610301c08050a120500380100b4942055600074600d0010303101946c00c4404540c0c810103000d00e05410410068810304860070819121a02c546080303501e8640850f004046c103002e001800b0913210521a0900035549420041c49503a01c031200720302c21401001c1810aa0b1100e5220100140c007850008107450300d03081642004441d90320304000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 914058776 1250 914057526 914057531
    0x30c1501050a08190f0c1e08010b01051e1e0d0606020102090f1905030615040609050c030412020c030316050c0108061f0306090509211908090c030a060e0f01 69
    0x40c4840d48000562103106904d9004880840d103450401c0c1440070140b01c8028190001148009040b80c0c200c1101c0c10321003c0142d145000303d0b6200000b070700b210603100c115400700d13200340900d08007a8410000600e85803131100d015450000031901c1d2900c0310320411401e00f4454004294100c103c0c00d503204460191020703000843c9060011400604c521a01d101d5280c400c40862225400c5035980507040c0c4002d09000c3c0884185052080c204428000d2041c0c2c03090166180110015440320503020756400f0b0910120101e01d9070b00c4130303150342004c580d1070302000e8294443c2c2110501c154400300010f01c801820480c40c00105080ea1902d036040c41324250300c0d03504001050060220586c2c655160b074054003201e003059915400b4210040d009440180e00c034100c001c1c030704020440c1654000c0b600f900050035076081e05038880c40361130310003821380201000300b058030b04200c0f60300650901801006400c0310000d4210358065410000007441e00310b0300d440440d180e40d12000d42480c02c8008018100c1c01e004040d00a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 914060026 1250 914058776 914058779
    0xb070203040e0f0405030c01050705030603100b0a030f020612070503060a05040c020d1220072a14060f030420010906170a060f0b03101202100c05010b03030c1501050a 73
    0x107100b8001010b070140c95611410b0f00070404101007042100c00c0c00c02c502c8000e02c114509104081d200743c108031102c0c1e01a0060075401e0610030854840c0d03140040d0002d0051100b5819521200d205404c044012a0800410441000700c148800d81c42d51180e08195101d1ba82d91510700c0903c00c04084550005001d107062103813601e549600818010b0790100d051034100d0130089114010005003c1e081c0070150005d1003021410740303026154001305085800707000300d03899034a910710410201044080c14140307005541501807100b502c904924010905008040f541400260046041c1035841510111a02c242441c010a0f050b9444804052100f00900f8205411864194090880c1c000032008003648580900010300c51203042e40070b0b00140000810400c42c1d1500d90f08844d41c0f9601c2906c00c0040d10b80b281c2d41c0003600019610526019075409041c00703c005904100c2918100d424060480f420b54a8429074030480d101000600070494a80000f00144008079102255449041c3c10460240311803a00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 914061276 1250 914060026 914060039
    0x50d060b0117130b0402030c121c140712050f0a110708060c0a0e04060b1603020111040506070204050a062d0b070203070e090f0307140c030109021e1203040b070b07020304 75
    0x3450010f45800003151183c5588a200203810b00c83d41d200d445600c40803800038516004c000140711041e402000c1d450750310111250009951049440c10700b18480c1c9420820f103400079851800140803c2c002e42012800c00d07542d10307840200e507048021940e001803108c0b003210a1075013040001c50300810f0b840002c0c000e00d0400403820040d512480d03458100b401441d00c90444e064486510103001490002c404684600300d04a1108e42600e4001040c0c005608000407000030400c520101d500b15030700202500d2600f2281c0c0d0030710014000040071450019aa108000380d50200504aa03180d044094286144090100d9000b41d400360030f5088a0114842403004000680380001c0d00c00548025000802841d6075005030350b49000c000101c110f01ea400041031010800010290403161042504195001c111107030050500f01c5060030006135211301c050180000c1600e10300c007800d50311440074295640454040e00010b203168400d6000001d1301d03100080050512007104e045c075411109074030155240070324060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 914062526 1250 914061276 914061301
    0x2102010c0f2a05030a050310061110050406150b21010e0606031801020f27100f030204051e011737050709173004050d060b0117 56
    0x200c8140c00000c100091000020030186503070900d6034060204e944c3c030b41c2070b2680202260800c4c2c500303801c821400710000c10341034003031807100d0080324a00006101705144403c60401401c8042d0064680039a02d540400b04200509021030140c09601078081e0348000200c00c2e181841c28200c1303620041e402c00801030040d5803042072803d4224100b00c1d542030b180d8684148050244219100d43d4030503610020b00304140030b954101500c2e81400d90710741048084041d10b4140014402c000034a98808131001000300f80ca03020380700c80619040680740c0142041c0e110b20110740c09000c10740e0102d00001c01101035103102d41c1c2c1301d00b51000c034440001c05115241010304602d000d0003004c10100e500301c0c550305403c01690036100038a5914102040050204e03051488001d4483c022a000c0e40010944d00080e03200900300019801a04100540400b40c44066208d10781125000c000301c008181c2c001008005481e5851382c4031508600c3c01440009550041800098902402184004168800c2c07000708400c401d81070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 914063776 1250 914062526 914062547
    0x30807170412182303010b060a0806030706080708043c0b0c04030c061d040f0b01020f121210170f06160e01050a1404120213020301140118032102010c0f 67
    0xd06044d011300f60051300003409085c0c0001500e07000b040204101c6880307070340010900e0140f034040d001c1e1840d4544542c0c0846010504a41e02000303c1c0d6120b000c240010b028010150681140c0c05d201c060303840e88094241d0701912010b10280130100f01003c101c060240b500c41a540040c0d050354400d20f46803850365048542e4040380319040911002c8100110f0130407074518000d00c101c20082040010607110180b01004181140c2c00a00622505140c10069040010710f81c451010441a0600b44a51608079104050000b011540551500da10018000c8240340001314140c085201501c2110142c9085e6880d06e0001001d42c04c00d01c01c00d40c440ea0703111786c002c05c1c6101510002e20341a0380e9500d1046060390588001c0040c141d4031180090000b03042c41422410800c0c2038404c42c0c1c1501c0b1000c0842400f0140d00081c050007040b5a03118260048641c0100500126036000b00c15500646030b0766200c081e00c06145d896504c0800d506a040850925420301c40d07412460300300d00b031003030964400080003409140304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 914065026 1250 914063776 914063819
    0x103031b060621050d03061a0c0a020d03030b09070e1e010219030f09170c060703182301030c0f050309150a02121602060403080717041218 61
    0x184040c014441c15400080161456201c024010140c000310b926a50002900940f83d038080d03600300341101441b07800342400300d40303403912000b4038680403000c40c1c3c09071382c003003820a1040d1080d0769008006071191081405254002d07100010007002000500c100c2d944000d042008010764041150802d564952481043c0881c0c0c4c81107550040000300140d00d002c284065904242d002d074907a079010503921411151b41148580d541c2c4550a580b150b8640c080d401c0502c01c0c030815000203800714014180070010708200b07030003440d00a604141011246140c0031250b08545003074000c6855141101943d42020740b1080000e2a0400003040c56040080034105031108050400a001001c9902c41c0400c00c8282140c00d0611170030f45840c141899168001e40c042c42c0800a02e0300c078a0006004d283c4508000d00d0303103c1154014000030340c2c0d690f4003240c4c100d100a2991092043c4c02803007902c20181802c4207072149200304910710000301c105901074000300651110b1070704400b18100078440007101c00241c400b0442e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 914066276 1250 914065026 914065067
    0x609030506040308130203060a05010f0f03021f02070317070501051305060609040804260706050c191a010b030f060f030a03110703050118060e01110f070204060f080115050306010303 80
    0x4940b24050f0317011801c40c5000e985803142c0303000d00c445810a5807003141215640d0720544400b40d07440c16014030b21042840086d6001d004407810004c58440c280820070f42c09018816209180d48a0f5510f41319640c80c14515030384050041250800c002c82442441d410550441f0008003481c2d2075991507a0784d0000416143c092034000003c207080080c0c00007914040c120040004031460349002c04440e00c0d240540102c201d500c240d5800050150080084079500300e601c0707014001c92580310204031482000a5011034000d16014884014000d0343c20382d2502030120701501b0f90b41d070b040103c415070718520050040d600c2480c4000420209d9030707002400c86a855414280410150a20800e040c02c3c0a2a540041c04550038140c10504240341c14003030030000b5120b07543c01c01034a05890240b90803144003c0000c40182001c2000c0d0340c1c0841050054017059100500200d60b2903210001140184050fa0164000c2d0707441300d00c0d2600100101032400003410301a03000b4061985191001400300c801d0b02c076100003105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 914067526 1250 914066276 914066281
    0x130510021b0306040f0816080a030b03160509070807020304050d08040501020c12030a0e0d060501080f06090a030905130f09080a090909020303030406020c0a170a120b0d0210020f01050a150609030506040308 90
    0x107107080200c04545c1240807282c89c2c1c81142005409803402e14141031182c010050480009250b1000c050103442001d020314540ea5510369003947c0c0c0040141c1f6550941c4414807001540d82d0760b90603211045407103104040c4e1035500e080f0000e80b601503092981ca11940c02203c1d1a07401c214000240c0b189107149140040d030314882d210200da205511007001074031040c100000451040c85c0003030882c0c500300c1a0030071140b0303580c0d0b521038507074542c2e100301c0c4002c00003208004100722515210709402001031a01e50700207250b0394000c2807141180e0030280211111980414800c2c011034001c0d40080050807020001c0c0041080f82d40025160300c401031000b40810350108180103c002c0800848114940c8400381d079180440b648001c40175904070400c1c2600141c011818100324100c14022411440c901408080301806c41d5405c00a1450591040e07004501c5803003841c81b01d00009000f000e0041c190880001035030b0a21140280c24400380f600032105100500d81c2c1040000d03000940c5582c815018176210a0a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 914068776 1250 914067526 914067547
    0x6020d0914030309061803030115050d0504050c040f020c030301050d030504051011060a0606021509030c032205030c0604141309140f061308130510021b0306040f08 72
    0x103101004029100801a0400304401c050000c011801280b003035040340c1a41e6200d00d1000702c035141c1c181c914409500140b00401a03924080302c03415440380d060a04604000f07020309a001101c1d0200c41c152091b9100c0c00206060342081d00c560b610700302d0201825403070840c02c0301100f40c0d60f00c018401d40c1c2c01401c1c3c1181d00c40034140f1900c251000f0b403c0042c14038102e40d1040d0340050070f8810b482c440c600c085c01400089801c1400e18800d0300e00f15003054010f040c0080d01c0f26034400c074182c401440d401c01c80c001000112401c000c140300410080002c0c030b42c1c010704003005040d01240310000303811080c0030f40d02400d401c2540313664900503a0300f154550a80c9401050a0740045501c0942c3d906510400c42d080c100d00700100603080c4010303003801c003644003210800746c000d104043d0b4030b45081c3e07003601d0041c602082c0e0102144040c00100940b00300d000e14142e48580d030340c000c02c1540c040f5074410030068108004600e100f8800842c100f482c110118000c00d8a410305859081b4414800302004041c01c10005940c91607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 914070026 1250 914068776 914068781
    0xc21070510180509010e040b04031806170a0903020712050705090f24060f160203070311011d01080c0705100921021b0405090a050a050a060b040b010c06020d 69
    0x150501600c0201c0380300204070040c082c0210800c90b00d100188012010810703003402203020f070484961000740e403440d85940d11504141301020f0400e40400210098039007441d110940c02c0c0c8000c0c062555007108a101d200500401aa80a4600001d5034104a0790070b0111382d000070094161040c3c205c0c40103003079400740381c0540b60001c05d80c0050f07000407480b8108a16004c1c0340100745d220b03900e801c00d01940c111011300840002c1c7c0d41e09000a41c01034091060030300b01440340e00642841411040e00136954540d50300085d18140b15a4021145280141411616940e00223814800c1031100010340301d104003282c001900c170020040c0b404611090204180341031180422403800501103004041010700c40c9400d100c0803901d1001e9805074945546292103c00a01c002094004c2e070400c2e44650a031210031404101c0584000b50120300f852141e1a4540041241884100600c0d403180d00140b00c07039101440c1a800341c810203c040c52150346002114816a41c01141d9031071002d90013000180e6443c07105100400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 914071276 1250 914070026 914070029
    0xa0801092604170705040c0c0309061209020d0b0403020f07031101080a0603080d0603050f150c0906070203100e0606040506221107030504050f0402090d0b13120309140c2107 76
    0x10f542001092901c03901e401140040681c0e03c10345003800310300c419034400d03a80507022440040020301c107c90104200c42c0b00d0741d1070b0444015040e10114141c0d00580000d41007010420043c1c0785454004103000030140c040140142d44030090300505485481c42d00ca2899200d419a4a941801050000251148126030140c0d01071036118209a03101c4c815695003a000304450b00049031940710b05140403440c04c80002c5c4c1c51100c0d0400e5034116010350703241300300e03e4216000300800f15000b56081c0250070040c0d400b403021f01044c422544d800038403040d141d82c020740f40140c0503242c1c0c1d00861a220038003051382c46801c060300c0f40498500515140462070041440144cc05074451300100c180418240308142e4040010421100211640d08a028080703007004103d100b860030096000703c1c4103544800094210b140c460b0301c030120702c028201007407050301c41f41c01000c00a000c180c0001e943d800c2e00420401030809441d48103c00b00010004c0040b2140810341c4440b83e81c08092202c0014540d58141c100e08111100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 914072526 1250 914071276 914071289
    0x1020f0301030f11120709020702040603050d050a09050609100c050a0b1005040f05090303011203050f210912030a021812070608130218071214060a0801092604 70
    0x303036a5a036074182420603a407000400c0301c0001d8421101801031800355008001e6040c01d00150a0003464907002c24000c1d44000c0040380c10030f4880c900040410000c2c40340150b18500b507260150340c0d105019005110244603000a449a1414000b0954503215120791103d00c031020300b4201100c0040b802c00c00d143c5801140020010450ba00800c1410b4000c0c03103003001220401d490520500d02040700c80800c0d24411103051181e60300900041140c0700703c0c0004000450b0007410b110386844c0120320841e2007a400106500560580500507080c03000589820a600c0f12020f0003420510b00507840d0b4010522001e001a00396a07004a80a11180d0706050700d1013524000070b1900650b03c1c41d6402064480c4002c1c81000049140b110028034181c200b884e0040465600030711402401103542c150b04415140600729034204921404002e0501c8014462024004029030301440c452501400b00030003540300d6008146180d042c00c03c141d00150140c400304090016900144c1c0c0300503400b1980c3c07000ca0040380d1004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 914073776 1250 914072526 914072557
    0x6060a050d0c02011a04200a090f080102040f06050901020a061d060a0b1c08040e150603070c050106053102071a011a2109010b03010c020601050f0904050d0e030102 72
    0xd0366803e40540c44100d841c4401240101e186129004000031950903003410b9800b01914500e40546420b40f000801307210742142015030703141e42ca580400c2c52080603a00b03c02d00c00da50004081c0401c84011000d40000e01c01450114601340344500001d442d03c1d034804000300302c42c0e200d1021240104001038000c0c41c400c59035040b280549001d100400181c6040301040d401381c040e014084490802a444414a46030042c5203c2d142510b0001700000c450070092000f42c02070501c1081c00802d5560800131030107a00e2565801512402a0418508444842d4480d42c403910324802d101d541d202840030f101501030038002ca640079241c0c80039115406031240d00c0380140b07070403101192041c4803241801140e05a07100b00c0340d01841c140c41203540091501c15554444400e140d10341300003408050048800d03600100038400070520700d60070340229003501c0b03000c541040540c019000501507418210f8480f00d4040c0111269001da080c20b80b00c0c2e5440d003a40101c148108103606442060ba03031002d404a43c141c4000c25000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 914075026 1250 914073776 914073791
    0xd0315080124080102071e03020c0907080906071d0121020729040807021002010b06130e0a05041106030c070b040c15021209010e0a0510020f06090d0806060a050d 71
    0xe074241030b08488408454a0510803003ca03200b07005109860aa640c81903448864a107901c4c41c4040e90901c1050803400c500c02c40801c3e90240d10ba800c0e05600844490b00c0c2d4604070b05001d0506e50400308000c007060100324032540f40d4000c0300c100501824880c14207081102c08000216043c12070081d6850788003140e9400098107204000d0710340c12a0304141080511150b5071100d02060462100081c1c0f0003420400b0103000070801740c07410501244400c1c90341d000010b800e00014001c503407940c00059641040c01d540c03030360802400041064550f48409050b10811446c03500365a13026808000044090050f000800003403104680982156040d079000000c0c1c40041c070305440d003884c85500a01800c000e0000c0020340710030645c0001542c02d07034280902c50300c50501c00d0080046a88a91a81140d43e00c008084000600360300d5481000c05542c020f07902606411383c81040c8146080030250800c40e040e408822101d200607400b101003078000c1d000322420743c2e440d0038207401141c40d4028000340e044d445103410751 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 914076276 1250 914075026 914075051
    0x8010b07060f0c080907060f0c0303051306060e0a150b0304080a02030c0718060e040b010315110f07030207080610090f0e1014071b0b040501020c07030501060806180d03150801 77
    0x4d610344600844c1040b00c2c0f4041c0c80300d0040325246084070034030000c07030601d80000780040e009030030595003d9a00c00481c070082c0581e441d0641a210319900c01c0e400e000381c450031f12000800b5801400c8500c0c91812005003824600382000050388802040074003585800f0030009003840c42402100d0000b0202c4089418050319021a8032542d00d4510f403050f4103c1c40d00c013000030010705500c0d5840c032a60b040b90b1003880300da10f151540000d4070b003050b140081e0780e9074411507a0007000050010b0003039030f00340c1c01c40c1760f807610114034010b450901e083d00705100d41c0e4010010800c00c15039801d80300e4180c0e1405a0046441444030748160054841e03080229150301031103142d82d030303c15540c1d03100c58211a100d000042c182d44a1280a07114006d10071514074a13025592081c4010030340422060350818420800145401400450341d07080204580044985075101c81c82000021810400b0641000150b50510354203500d0200d200d50750101c82d0b40c0b100a044d103990039900300c0010701664100401480000307118202400e00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 914077526 1250 914076276 914076287
    0x9040809030706030615030b04110a0914090c030c09031f020c39030a02060f03090708010b01090302010c15050a02090a1205120d0e0312190c08010b07060f0c 69
    0xd40850081c401c1440000710b080c4203000d5001196040b28103070000341d050b41c1c02107000e80168142c0742e41085c0c440340c041041c0c1c0124030003041201102e42d500090f150a10383c43c600482800320040340728001080c1480101c2581c00c08a03504179541444041d178880402020074189400381d0000d20b003400b622070004842c01c6441e0014581c1007000c030150b605505e484d42000124011178140007090aa521601003690090301d003071401381c10b80c0101200c42e107403007590000d181c9034003100480d041c244003c001d11030100800c001481c040c10380b030740080c8003240030f040000709189540d220290400c514040d8070702c18801c00c1d0540b0300410f69000c80c24070035403a0004072100a50700c94081d150103040407034400284810018042500c070303030b80a000340c145080100003d03075513a000411074031003c955507102a000054100003e10700d40c4101021903d040c903001000c1c07020b0103503000d001040b10382044194203000b42e1050102d41581d0209a400da20b8000d9800c00c08000d107603d50703420040d14508643c010f803031900310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 914078776 1250 914077526 914077537
    0xf09050403020c0910050d050705030d0f09090c2f01050f06120c0a03141f06031a042312121614030703111204060902040b190506030411090408 63
    0x29021210b56140c83c0d01400b0f25090111103000c0488800078080c085840c00c030b40b410150f94080c40071512250f4907000000d08000d5004602ca0104508411400070142c00c109220b00401a4050030401383c2c00d84900034003030601d0100004020440184000c0044403210300305000c0d0b04015000300050719102d900900d0840003603c810380721740414035480068020000d0b8080803000040c0c0280c0700c90b880c680d1549090421811000041d020f9803401e808644482100444032928540c03000c00e4483c41c50a103032102c0301503e030707800d035014203910100004108445400444a0b2340c1d10140f02d049001d00b410b041c20114240010302c140d5400041c0800403203140305045009034951103103c600503040f10740680340121b04001001c800702040c17000405640c0258014030840c11030381c40c030a1400e0b004818400c102e80c0100e81c01c0741d256680d504c5401c10350a091044110001d0140d07a003003851031130800500a0a03545100d407a00c0340d0f03c0000018104031015078106c40e0150082e019001c00d040524094003180c200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 914080026 1250 914078776 914078783
    0x90e0a051510021c14070c06031131050607050c0901120b07030c0c02100206071103090a030b06040b1c1101021507052101090f2a180f090504 62
    0x80c0d06140703424a845400c0800606680d0001c110211050a07031011444a4005440c1400301d031042c5648211050401050024442d003413034030103a0700300203015088070031800703140981a000340610a050540d1019241c0300007030240300340700c0580d980503802c0d29905aa82116820100101d100b404010000841c0c00400d98200d072210342503030300d540081c2030860a50b200604101002000720b040f043c0a80c0c1322007180011403519022807003480c3c0201d401c6c1020b00e8007603401a1321000800490650008003101d42680000103185044003620000f00d030a040760102910302c56911010440303941d55a40050783c145000ba11504040742d03001d251590b41030b003c0005441c112410288210198400f1441801030140513090310032503200d0701412030380c07a044420b114103005440d04206100c018035070a80c50080c0019a0041644502852120140e0340511032660a2900884504c06100f0003034805800003a9280380c034118040c0040500c0300041c0c0c079648a582503890484021608034060380005125501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 914081276 1250 914080026 914080051
    0x106060305060603040f0b0a09120c06051005010206180a1502030405071d04060b010e092508220206130e010501110c0a0b0904090c0b09030d050a0207030f03090e0a05 73
    0x3280d5082c8903c510048800501030b03030340c646051001800d2050303801c5c3c01440c0e21070001900f580e96680c1c455500403213a100e6000c9010701c81c100f8200300c982e000301341d84950b209404004480c038000010355120400390510300b099850078034081036510200200251907400000d156581103605602074006d5000b510306403200d001e900c00114240300c0d05004c140b000d190300c040610300c03990f880e01d480c0010f0803010790032410400c81c0c004241c455540c84150034054464650303400d00b42c4070172813000410070026001200031301c0035800801c6401c4000410a0300c0500b040c02549940c8249880080c3c07203440341c141c0d10500100c0c011404140c621500d40042e0580308203072920314614010150003983c0d50358001c11760385d000804610501090003488080c040c10707031003e040450380d1250756442c40300000c0140c100d0740d514003011a01c0862072508200c03020040c010b9003002440c01e00e0055000352651514040a0f044620314002c034400c040c030862440d00248041c03980001c41d802c05580c2c3c40003404060b2412201c098 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 914082526 1250 914081276 914081281
    0x605010801080a0b040809060d1a0103090305070b09030c240606070f170904060806041a1e040206130801090c0b0f04180f0603080d050108060403200c120106060305 72
    0x1401800000d0580710182d00502072514070f943c400307180c680000e008880c01c0030107014140064a910000c1c115000302c00a010903092510641110f41d40c4407612030030304041c249107610300440d0b00301d0100c6025a40104542070320742d44050301986140f04203681940c1c10322541c0d45440c102d01202100c20611800c488200d50303039032160020000030740030f414005001e404004e000d00001902c04178280001ba116503210314200444030b00001c0440e00d0a81c841542c1ea0400000c00040084031745146c0043c1c03402c1402081182004c001400550768241101850301c900e40010501755611041034680400f16010800034007500c03106003c0c080e15444604580007824260007143c0c1940b11425640384883c00c095080c1010715021309900308205030ba42440c17110b951500d0310712202c4002d002d648041d50088201720b0340d40034400040c000321203050380301c16103980088061000081c0c3c8240112000301c200000100c800d0341c000640d0b42003816100105500054255030214001d40642001c41152510b480402403035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 914083776 1250 914082526 914082529
    0x30a05161202130801110405030c04090506010e04031407030c0b070201090305091903050316020a08030406050313080d0c0807030606050f040501140d0f020301030b25120b0d0f05010605 81
    0x5040d5450840003003003036411400200381c0e01e50702401e0b8448541c01021401d5954015803821210207040718070300c2d0b2000003002e0126040030400c0b0054100103403400c00440ca4642c41d4140c80d54010701034602084100404941858459860340c1c03522a02d03c80c15681c2c0743c1032442c003e00140010306045491403092400146202c0c0184540845150542c1f1528076002d28035081080c10010620380e1103002c1140c440103c0400e800300082c0001e0080c11421075148030040c010030281e00101d0b4048540d50340304210a010460703201080ea80c10002c40c0080410440c1c482c036041500d801440840c8603000d03d8141030780d110f55403100c2501e0240d181500c080241c9515200308880c036201e0750115007807a02c0100710801042d413040041e043e603031004128550400394882c00c002d044d1642c41482e483c1d25170b0088014014007949090b02e50301316501c40c0301c1c0100c000740703071002c3c206607401913000c0424001c64280e2800c6c106083e400c60070325040001d24804002010345000b0b5050240f20301c081e20f46601e40503010815 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 914085026 1250 914083776 914083801
    0x110304180606170f07080c0d06140f100504030305090f0909010507030f060f15020f06010e060a0e0403200708010c05130f0e1303030204090204141224060d080f030a05 73
    0x2851340ca00402100360b5803104180c2d14810060710445454904000300b41c44a02c1d20700c03c00010b02182c00c00e440441c0e01030004c1190107618540f106108006503220011401d0b00901281c080380e030705040843d00c91201d24001889050420704154110402c042003011045041d40a5842450151401c1090018044040080300c7c003034042d601075002228810f2040140440411405c8012072044071035880c7c01200355414000280d011820120401042c405107140c8410004080c11800390701c00c00328581034400909040014100071801c4140441481c150081403281e0b60251540c440244004a48988002c240e94084210040644a40c84021603181d807040d500d070303044800a0302e00780c845031602100544580c9100c2400c50a0503070800001500041500281c0024502e080e80503500c250388902303002c4440441610400036030491003150031000c0c83c0307004005441440180d02440d9680b043e02155010501010141c1381c03200210b90440300c3c003030a500440c41036034040d030288078644414400100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 914086276 1250 914085026 914085031
    0x3303060315090102191709011415040605060a0c03030509190b070c020a0e18060c0a050c0708190c0b040810020a0c0f121403060604050111030418060617 67
    0x381900421000340c424009203020542100700c1030b00040c900000c141070301d02070496031004403000c603000810b183d00241c203800130540d000c44401c000303001440141c041c00c1d01a0000404944040d1b00340581c0e06065211603114801404018150a17543c00d2490000742031104034141c220700090428002038a01e070380200c1d24240d010340d55000340e20040d07030584c3c0da0065058003c2600c020848080c43c200d000d40d45901c15000200194604481c0d1400c100c0002e10008a950044240550041c028010100241821070f0569030003803a280d034607000410b244506100d010b61003554940700b0301c41a08000c1411a1000044d0380c412006601481d07581e032000203050080c0d01ca03545031500300805a403511000d41e00100301413020343c6441c000040c0290380f4080754200310907055401020441d1003036802601306803a4205060344110440c19440c01c900091400c2c4650b02519041084c1c50038004000d000420544001c0d00080c5c01080108000f80c040400805030344c481c41c00018a0301101240c00750407400d81c5070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 914087526 1250 914086276 914086279
    0x1903020708032a0412021f0206041509050f011a01090305060a18020d030f0e01020a020d080723150f010303050306040e0304080d030e060c0a02030d05090c330306 71
    0x81c2141d84100341112642c0e40e40d03c2c40701e00c800f4180c1c0078192040c4518003c0014040b012400a40c8072400e0044c0f20f408000402040c0c60402d20801403007005400195490744194061302079142a4a0214044060841d45100800d80e00c04c90408007105601900201014500742d010140c0300c8040d40011108080603102c090850340200b00480d41400254021b10300c42083d80c03143d038280301d2031903002c0b5a80c003000800550000b086184551b02c0c16501c001c41c90f9203004248000d10701151642c000031a602d401910082c180c150004040080005090560f82405000d0b0103d2010030a2122440c1d210000001c0312142c200340309c8c000550001400d4203da0507250903585050460390703403030f05000090404840404440c030081c040003071051340c03c100c1c0c80800314503035601161481004018910b8090b014041d441108001d0146100702c6500006558100740200004104ca803150b080c0c081c100325400758011f4120b6404038031111041e000c90075403004200078042032103100c40300c15450340c1c0b00d0000381c481302d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 914088776 1250 914087526 914087543
    0x80105121507050d0b120a020a0509090c0108041b0b030406050c1305133201080a03020c060a0c0c0b1c050603032b0e010e06010909080403023319030207 67
    0x900c2e4a807040025060400000300000340840903840002d03500407454901100d81c1c1d03c441240e50071424070711003050003001d0945080300903060201e407041d2960301c0303503036060304014500000406100392003450001102509580c81509622201002d18a40c02201d0a0fa1314034201004290a0000f010031541c0203c02056401c0201e4202402c0040d4401d80d07222620109841e0070000300c00c000350304000420048105022500c082682820b8040568160310040c56508205140d0300401e0300440c2c20401c00c4c2c07007140c050b9500c4404a009880422048a003c0d003500700300d14020801081200043c81c50551400410202d041c1e5814807400f9034008440254140d0001d01400000300f0301c41e00d000c10038031010702c003002d04c1c140a011918111070114030405111382d1a5000100380c5a014000603015040000082c085d00b481a00c90041c28822488028082e030a004040329054200c95140c16816007070f4000030300c0f0049a145608115045060b151040b12403c0d07026400702400303442184c0c402a0b1242a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 914090026 1250 914088776 914088781
    0x3041703091f140702030406021005090334030c060605100c080f040509091b0108100e15030618010b060a02300d0504030f05091c0501020c0307030801051215 69
    0x3400c886005403007072081155200c03c41129549030807080b10388682030581c015500d5500d064002890800d40c10060802180740000b800040700000c0304580c0c04c10b88013642040c251b00030159088002d41101858020003040600d1038007010713844a030f956805401450203105c92515141001880e046c41c071200c0010444003c0c15000203035007400900004030351041020b04040d030311401714071042c1085550101da43c01051040c4205440d40100050107142880c15011519180030890038028060245100a21391940010000b9545644004032200094141c9810b401d0910002c5800000401825a02e50808681d01000e05080c1e06890407404194001c1c41041100c00348110a07480e01001580e80c0c185841001c144030b45d60400502540c1101000010030385020301b0000d211054140c40d10b401c0103401c110604466440908401400810784603403810b888080c50114020b100e54618501c0d18000172605800340b580203d0214100c481c2518014010708140c44520b03102c60329054240e80d01c0141001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 914091276 1250 914090026 914090053
    0x80c090109061d48360d060203040c050906010c0807021801080303041e1101031e061418270f030f0301151404050607030302120c0304170309 62
    0x41c2a0703040031221301d06402031260100c10001805a03010744007a82d01e075154031003444000d0b929140c4411000c52083c1818030496610000401720311425044d41010351458400c81c3c003041034549030340520020030007005c031810f61900300d02a410469040c0e580812a807000a440d041803000c003845490140d640c84a01ca11a94440c1503c2d00441c20581e040000d51042190a10300f802c03455020f01900c0f03000319140e20f440e02d044060047c2c03c00761404894411000380d0000b54603454580d44c5070300c003400d01240b1000ea90699180f03050300d04460b00700180c101400041e4119200c4c94400d0790403002d9502401904150b0544d40c902d0b0419a00e1000071620103c152925a4059211f560300c022030300140c4a0701c50741c0106030703895500204041c101503440080100b0000d10501c2e100d2180407224101040303403240100c40c10802e402580724460040300c001a6600405100358100c4030181102d200040e418282030903104501c2e00704035001c8410001e86480c00035503501031000e681c400c4000070000d0140050a20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 914092526 1250 914091276 914091329
    0x1e0602060105041808040b07020310060308090904082215020714040b0604081203010905150d11060706020409060501030b0613260d0201090c061809020306010e0604080c09010906 78
    0x1d48110098a4100c80000174801c10000c1009241714a1b0694881d1058010103040c0701000c0314039803006203840c8041000491060a41d401c840d0211400c1e4010360315130501002c103118150010310004a544004020f10900701e94034403c4c1c0700006400e04c815003010000380d94415450245241010110007035403020310341034020303120310380010348070500342076668003158501002e07014001800c0c1008801440703021858130596a101500740056a441c80410300803600280041c00c015180c0107401c4540519500d44401701c1d5038017076110008540c1c540e03642d00810014500341c040c1c140040c1c01c01d00c00c01d42d1031428001740c509070105130404640080c40c1811000300e40212034100c50b108010780745100c8000b4414000109420101e800100e0114034602d0400e480041030307001303c01803101102c442c601e03900c1c54000c8401560f240c04030069494031103000688a01d1424408a40e22280018010521110202e02c40607250005d03603c802044c2d88891000b000d0721158042e8040340d0301c4400312402580d03202d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 914093776 1250 914092526 914092541
    0xd050d0b0321030f0708070804200d230c03100e10061511060c0d09020a0b0a18140603041e060609020c0f010e0a150608060a061e060206010504 63
    0x28200c0e0b003524910030000d041030340c00d84003401c410400401040228a6003545080d800601c502d401140e51070302d450054610f80001d000500036104100c00c8600501da8031802d11a101c0c80244500c204214a203441c5402c580d062200c1d010302d002c51a4910502c28001900340c0300441c4c0100902056030000503404003c4c07404204908140c8610031180540030441d1141c0070140502000554010b21b01e000040c3c2001030003041d1702c000d94452805c12645000d58010345d211200f03032200c00318130f0a400f400010071002c110340010691141c00540c4804103a004503250b1f414031080c50041405a503110401e07080320301b800c1442904407008000140c0000c54001c0442c001c1c01454030b8440001d140c03604d414089442d035403c006015076001030345540a06040002d0b03d4500040002401a245a4100076454020300c80d0000c140b03284203c68110003e606070001c5001d04204412030302d240c5000201072018148521450780c0c40524a501d0903442c05ca440d00b80403d0303948540040c4000d074603101c240030040a01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 914095026 1250 914093776 914093779
    0x203190309061101181a060f130b0102070306020307080f0f01050102070b160f050f2e0507050f070c030309081b240415080603060f1902120915090d050d0b 68
    0x950a000502c2c80303203001390310002030091101c001d21110700da0343c0c04100d40011f4001f9104514900c907804407075440c010120a00500007201042207400d900040c0c2c90108250802484c070f90000c001c0202095105064900c07800c00c0000c01e0b195a12071b40c04036900922b00380107a41c0160400d240038000d03180303100014091074003e0741010754002019240c541c1c0c80304245000b250a81c0007480c81074190030707040050b240d2040a12015607241208502d40070084800c44034196440c94450f000a6200d50082040d64001c4c089644070643d146124034154080d520280130841c0454030868000c02e22010000c0c3c6e94408000100c121181c08a4990030410740d16403502d41c02010200d201a42400c2c01042e001400c01003100319081c807242d030000c99024240c010000c0180340658080303810080519100003805807c0f502d0aa02c0e403041d40c2c2100c40c0540a841201d24200c20901f0110a01c09c40381800100307001d401c051100b001203d9202c00040b26192180404400c0c00240103100185aaa01c268040300442c1e60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 914096276 1250 914095026 914095031
    0x2e0203061c12021605030705040e190b010306051605070303111b07051309030206042d03020a0201030c0503060f060f120c03010612150b0d09050106120203190309061101 74
    0x4507a84030031100840c8107040700c4003041c15128150b203c2d01048072041ca1003100555299803030a01c0003003540e96505101e8284541d455290780b10f04404240281d14010742c12059428000300d0a081108903c10280b02c21200d451400001070340c104901245200c1c2440542c0d10540703403004544086024203001c4c0703500034866404110300a500c20007078520f68483c080c003401400d40a80b40100700a59600c10114a04846040c40d40034000242d0104103c2c5d881540814810001d600100341600c99818022144003080001c203000c0051540004110030b140c2c0c800d9074140918020841d048071070380401d4a5030b58104c2041d40d107000031890007134086d00090440c0780000c1e0620582d50202900c0207426501d14814a00c00401400025030000245284075440300003801a00304c4854101d14002042c492022500b201050076907003102c43d50030800c0c01303a421000900c249500e40300048040d030201c0004034803d115010b40354500c2e64400b083c480c18030b501603d5603e40149082425900c00e2080c1160345034555 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 914097526 1250 914096276 914096299
    0x1d150f0c0c04020d0f060b13061b021008041e02030303060d0302030706091b0e09030906030406020903012d06180209010903050d080103020411130314030d1d2e020306 73
    0x71200c0c4051304645040c000d02140c81c940c80742c3c1c03400803900c0c182c010480e064400c01c0005088502d00241100f150582c0c6800d503500301b0340700c3e504a80040b4101009612000f120950280d6603171003c40c0317500481c01368a601644c0503481e0a9440c00d0401c040c8000e405403c01d0002070150301d000090200514002c4c01501d16000180c2c0d00c84003101c81400085070408660780403210410800c91010024180d0320f00510b2403070800185059890103102c200c1445034400000117401c00c189a0192203165401a00030700604c0200b02841680c40d0320070014200340000c041440d240d0310884c0c003552085500803070040740302421051b140b10180d070098040ca13040c42040000000003030700c100641000100c0d1580c889940754107604c1040b09031a0141d41c0680d140b07000340609120706441c00070010880341c1c00030f10400f401a8600d161400c0d400303160002082c1c13900c0c11402c440d440c42c0301509900349140060641d1101c0840411426801c0c007803044407110707075001d2480c00d528100c2903401180c01c00750050003819602c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 914098776 1250 914097526 914097529
    0x1d1501320f030c13050907052a010c120510050a0e061f091e06021504140d020f070522090804030c14010207050301230a0212071d150f0c0c 61
    0x2d80c425540c826418400007413841d1040201c0f40c40c1c20150800311010102400c0070107000340359000e41c0841c0b402ca01100d03848120542c0040e00900b110030045d00003408403d0320080c020380350448003680b50440c80e00b0000059001c0c0790207503840c010f850004001d0368540e810301041641e04680204920b4001c440003100d00440300e00094070351020421070382e07800000d5083c4010110001e5104075440f0301c01030001c005100d050740100b11740340001104504102503640e103007807103482685107100784003086c006c21912a400590106100744c101c0c1550b411660540e50711003e01c05080f1441c400b462518584001060100d80c540e080f0505035070140400c50f08140e100d840d16010500b50354802c0e2840103d01303003030b0002c03944c0601084004060442c0204603017801d110300c0c24075400d4500c42d91030300d0111000001e1018002d03079040d150101d10080760003c0317516041a010b440c0000c205a10400a103110300913a00502e00100d9609603620284000740c02c184a04050f43d1458000c2101c07200c8500421240034140d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 914100026 1250 914098776 914098807
    0x90919032109140c0a0f030b0628030201142803020c0129100807030c050706140f0906070905040e190b011a25020a1d150132 55
    0x80390003a0581183c3d25a00c010441c81e210b94440343c58004c850380c0b80c040042e940b20a038800c0480c0c0c1c00038610704681c0c2d2850002045c1c1140044807440889800242d841140c00c1c888014080ea07100382c840618680c9a010054101e0003034000d55100c0095114002c5984046a94205c1510f4207505016050103414000d0310b00b900e10191003820f40e20036541d00d003440c60b111250203a50007041a50f5001e0036401449000349819401000e220500da11410f6805000e80304008841d0aa90070080400c001c0400c4080000c2030007041d5020700310f0b0503545020800c0041c011030b007180500300750340750740c070400d4076200074080035200307240340d4a4845c0201c004042c0c040c9081c1c080701b600d01e4801c0d030b450000d643c1080301001f10004244000f240d225000e00410020b8250150781a06440045804500742c00b010710000f80700c2041380d0001d44184880c0c481a11444159040f03050280d1645591040e01300340120044070400640c3c900740d0300d0000d00c0000c06101001d8203030480e5028041650071480c111801240307511 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 914101276 1250 914100026 914100041
    0x27070305030a0e0405070c030e040b0d020301050f011706090601033c0302010c090b04050d0609050f030c0709050f0402130e07030c0302030f0705063906060909190321 73
    0x2c1100a050040c281c80c0901c2490f5004129003000b0800e447e080e01c0003004090280c503060301490703480b104a249a51007000101405500a0090244e8501011082c801c0301c1c003841501e000c8140022005103c880c041841c0340b10f00c90600042286038a161685909142d00c54052034020f0072603d94200c41c4100c80742401a001445400514a42d4452400a0844021104600401800000511044882030300311030444108903401d4050030203908150004105603c401011480350034840ca00035513001c000743c400303115520240e440e4181d84500d0340d010354070304403013070385605501000150042ca000c442c4044102c40c100c03000287c42c1070080d441840c150080d04180d07510074060808008500c0c0810120b2110381751680a8540d01e4038210100d10107005000009401ea42441c001e11104660540c1d00c13105440a54200c41074003070303800f004944407042a20406d02602c83c040015254420000c0c4c0708400e10090b00a40810030420f403000c45984012114007140a61140440d02c1444024011001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 914102526 1250 914101276 914101297
    0x1002222115091a0709290f03071d0a0b0f031f06020705031b100c030309150501080f06010b0a1209020a330c1509060e010506030d05032707030503 64
    0x1125031200040c1102c0c002c10040400030b0402d401d1240e041e004421b0341c464030a0100c0100001d003000b0614885009103000404503a0011042142c45a0b00003d24441945090418003017104240301388824121640100e80540204024089080030781c100155401101458010283e8003010982140c0c802142d0000f4016400351000b403069143c14029440784490072148000e124854101007070400c184200e00d04103120526128009060007a01f2440c52543d003c40b10240284403501d40c00010042805040e9a510450042e60702020f0f000031020306032440740c2a45403c169810ba011944a585500c0304000d8544429030580140c50b110055400342240d85200b0b85141070218603100010041080000000c496102811150f41c0100200b000e140d0402c0c8540303c0c00000c0b83d03200e8050488018001c240901d4601100d007100350652103240610002c07010381304100c42842c01144c982c0000e445542c020350072507429040e50002e0400040e10083c810060781e1026559071559070540d04a100c0a6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 914103776 1250 914102526 914102543
    0x3130b0a170907180e0a1211030a0c03120c020c0f0628030c1d01031a0d0501060911040b1c06030f0b040b0705040b0a0e03070503100222211509 63
    0x81c0107240104c2151071303040340142c10804c83c0d01035117450240c0e9080c5a00c5c02070500b020b1420640041840ba21203020342ca500841202c3d81d882c4104401450142c8500f401d90000b0000c03a41d49158a0240c001d000004104d0760040000060310010400001260312005074880d41c20414490814000c4113144444105454400e0103040d407000007030b09440d04009040c0404c4a299060200b8034242d004800b901300302841c000400301c4500c0504001c5640789020164066404401c1204001054116000741c44c480f85041c041800c00031304001e014000c1d0300030380503081c43c144103104d00082c0080c0e4040150381c40040102d101941c98844640920b16200f0942d0810b9002003000280541d58690b160005814030301107161070700c3c181d512880c034012199241c0c10040a103940220320395040081802400001f0705446801c1c203808940c074003c2d48a94500b903c00003030170b446060325400b10821401155054903107103034901c180c0101400c012600c0d01040350345071440080380c51204140e110381d2200c2485150300303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 914105026 1250 914103776 914103779
    0x70306050d032616030509030d05010b0702040c050a020307020f03010902190e06010807122a020a0c05040608030405150d110a020c03280201090801020d1b0203130b0a170907 76
    0x4008102d1401000c603003c2c0440c0007404020f24015900c140c5043c484d280c002215140c2ca40c1d00d604604c00d0071181c40e180d9080c07100100e0803503004002052060320850b42000680c142402c15101c0703002e06540003015030418000c10b405410712400f1416046402000040c070308041e54001409035180569411a20b00c0841040c045c1c030443c0d0b00440d800c400d00b42000c203454500381100070304190080c2041d00380d0f9510790280306180741042d14404007000744083e019494405101c0d0003903866030b4848041d2414040c91000240c1418107110b5402907450700d001946c60141050b0504c0302c038101806040c500701004001452401c0030038070804511180500800d5030b035809000000340340800c0b12100520a80201000315005001700070000d4007031100c5600c0241c10002c5000603a4480c425600448103940000390310741c500071055001e40284000d40b9010f01d821024904101d0f0f4a0041d800d52203000105408103005c100c0e00070303000c0c00880005240584000c0c4149828804500e004c0c2d9405106500ca00e10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 914106276 1250 914105026 914105057
    0x8270f010c11030405060706110702090a0515040902090601050a021f0603020901061706040b03031e091f09030b1305030c010e12090a0b0306031504031710031a070306050d03 76
    0xb0241002c40c00100158101420700002996078451244002d001d41e075035404c6c9050768420142070740c00c161340050204e00da83c5013503a2140040d080840d0914029003d0180d1440b05107031920668422a801800742840ca83d10304c001500e05a0161a50205500c02d100300f08800c6034000f040207005409404000c02c81501e1032040c800d0180042c1c1001c1c06210101044005040688540d5a0300481c11180452440030003004242503104107940f0010155a000d0740284d01d1041000030700c0386590a0303802a420051000700040e03c480f442d110f10000030020308081002c12100f80080360003d825a08020503c0000d035240e618684c4000900d1240e07035100c803443c2200040c1400310818000134100407034945141500020421800c9000d0045000004004074016440800044008000000b10f50ba00c60a2904014241a00d0070345041d0b452003c210019040b41c030f0144c1c00c042240d50000c640316281284000484400b00000c058004155803198001083d542d006000c000710750081e100d004000b1300001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 914107526 1250 914106276 914106287
    0x720030f0c0405150123130905190504120f2105180313091a221a09010e0612010623060f032403030424020a0308270f010c 54
    0x10b08400104480c521000c1c25640c02c06c80b0000100d0f0110000c90717540e003141250801c240189481d00f54913801220001c500344d02c00740d2090b80940050705010041100252403c000c2c0c1d00111740c001e1008010448500ca410f01541222080e181c82d800c0400403040c0c0218000311020110228180c3c4541714414400d0080422002080c3e07425001c0c05540340c802900703c1c1d801020502c0c429095400d80e500c2000c0c010b100100098842490300070208000411700400006d004403262018149051900704a6034454002c1e064542440740d01030018221030b842c200d15000000002810b09400072443d40c2c045032002000e02c100c0e009000503000356422440d440503600d9040f184e5850030340c000c0c20b00700490201a000f0f04c0a40e6848440c508001c0e4099080b080802c0f407245c43c151003103415100102e404120540c0388000c2c0b210a050040d14808013140c0700d4801c0b82d98104003840074010522450204400401c0346070000003100e290314201d01c881051080191030014820880c0c80750743d542c1c6003001029503200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 914108776 1250 914107526 914107531
    0x80a0b0601031b02060606130b0d090c0b0909060d030201090b091006060908120f16060b010e1c02060915120f0106090e0f2502010501050f12030720030f0c0405 70
    0x1040b2007a4000c3c101d5030203562884044c0c20244256808a0001001b0b40c01c0c00440000d080c43c09025030712070303050300050300c080d0003400821100c0d8001c100c00400c20050180c1030303450041c4002d00001041d1548070074040290740140d400c0d4115522071345054003081d01c070b0000c1409444044010107070010711118540881d5a560801000c01401110030000141d0009007904031000500a41e580c1e40a8400e1268070341c89054810541d501c000d160301c0d014024654884000c006080e2a03e48072400e440b02080300f101040310450924207114119900541801c9000c0d08100c44081c4c0f83d10540c0824640701d943c682c0007040a41d038102006410003981103803601846004003080e05110980c0b0303003400c1c1c5510681d00300038511402090900005045051840c0c50070f5040d240440d4900b25020308403d000b0b021b00004d01449024800b03042d0051414204201c195081640c807801550034294203036901c09244a000210660110401c1c07040145a60b050ac000100f510503074000706140800c200c01c1c48260b4400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 914110026 1250 914108776 914108801
    0x9021e28021902090709050315040615231306080606040609021908060604260c01110304051e0301050108100b0d0f030507020406380a0c0b0907080a0b060103 69
    0xa002d50080d10040560080302e0781d5040360300b09400d0707451800845890201d50b20481e03243c8074041c400c0e494008000c2d007444c003450186800380205a420100032120f00c0d8280701c0c4025100042034503034907031940d5084d01307640d07080b00400700c600c40038400301024180c4456400c10f412641011090010900e0140314400003070083c800203508100015420394407543c260301c11181408078400014401e6502c000451300034240c00c81e9001040550b041440c0c03490400031020341054402c0715901111980203801141c4214a074000035441c05040030180185c06410f02601c424052900707101c902c9580d0280602c5028002c000300034088480640403000c15504140f988500411821000c0000300d81010060300380540c05040651780c0360b409101003001009503600611490840e13600d4618000c00c0e02c40d40c82198800703501c4c0f4441c2c05140b01c40d007000c00d1090620f850301165401c400c0000003401c07015042d62203a1000240c400349651034100504010600004440900c014001c002c482c0d03030540300d0040143c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 914111276 1250 914110026 914110033
    0x305011d060d0302010e010f06030b06120601090e0307050f1c08040804090203070c0203011b0212040f06110f06070201020a030513020a0501200712030801080d0909021e2802 76
    0x39415820040d901425042c051510495103105160007500400c0700940f0040013002101203440400f030041a10b03010485450f42040c010990038603240306651440e80c52240580566481c09103c1c00c000d10a40054010a00080c001080800c005000c002014080400501803a45070344200c03015400c40710040c44144094002440041401607003034400f50b4402000040c0d698450710130a4803034600303922000754076608100e4183c65179480c5450300e8594035115000c8501282e00c4c4070500415015a002e452040c07402c80b88200641845800081d103450760b91001d40b0024158942e00720f050403421a28800541e400081e5801665072521610b9031201c010302c0c030b01051030020b03130001e1b0745034580380318503410001d000301d502e8075070b022710380002000f840504211103160340d0751144078500b03e0519000360042041c404c000a41d80c14081401036128a060303a401003500c0c203010310800250040708504007812050b4440c4d005e4900680c00401c18551541b091542c40103410420b9940b004106078402d04540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 914112526 1250 914111276 914111309
    0xa021218060712092306031b0304050c03010b041e09170703081f060f08100815040210030204060f050c070b0c010515060c0712110414070306121220030f0a030501 71
    0x741d9407170081c030365400d081b50802d60740e0700c030300d6103141e000031090b040c01c59000c0300041400100480068100100201034000f030040d2180002084216861152519003180d940054100c0d40000780d4040e00c0c201e441a20041115591010380340b485800042d8218003146602d000d01c24400300d0100703043d44025000030b184480c2414600c0080c8502c00d4185241c0600038004041080201c1c50300001c8007408683d800c0703d000c100b002990b180c10380380a55080e40501580400d00003150f1080c021101620001d483c0c084409188401c1160340780d0203507102010601520001052450410004010803200310380042414288048200d28000d08526020302c54003040010310300e0101d0100d8030a049885012900c0b04070006811310080d091018134032642c1c460301e000c2d40c480e02015840340440c01003010f03950400500e52160707038070030700c1004240c400ba090000c0c13594221160380c40b803e011800e00c520f4130b222900c4000c2c1a0640d91031074108500c0003c0752100451420200da42c181300d41c0c0d00401e8100c103528100f4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 914113776 1250 914112526 914112569
    0x1060816120209040912020304051801141c050a060e100c21110406090612021204020603070507060921080f0c070c030804030804140103020a02121806071209 69
    0x3024071039a03105503004900560f0540e96a03012403040c54110884031a0649001030080d00c950040c000c040c40307901e40011811100c402503c1042c182c130710043d00c03c040301c038190041081d104a02462202040c2158441308002042440b10703045051103201c010951551100340103041005400e0300b001c801d0314145c00000d81950205004000d265205042601004084039010180c01c41e0701481000c14400200007443c25480303010602100c085a580c1c0450010319185181a407103010403540b0303003000345008100540341c59001160440d10740d0400f1854508c0319038035401901d034162001c1e2400d8140c4003402c6448420808404c0c801c030400c1c6010402460961042c0c81c80c58009048454400d5001c12008200800103140d20007458005004c03039200c603501d140c418169440b50042c0c2e03404480b51384540c0d00d194003a009035103640e0325a4029100e4240420b01c001c1c1140c00420311300140d00c0d03404400180d01c0c2c0700d00000b030a4060084c424402e1074955050701074203c01172548041040c0e0b00c5007000181d003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 914115026 1250 914113776 914113787
    0x91112070c050601051c02031c02060907030f02010327030c140102120408030a090c090e0c01050a05030f0a0236010c0c03060906110a020a0203010e06011202300601060816 75
    0x151401200c00341d03005a0151780c410707420014484001c1d0180304070000c4200007662707401a00401101ca40c2213400607910450900e40301c003520320008240344000f100300030041d030203900703d01e403040b81c44050680321f6501140203c060b0300d40341000340d0204072001916014000580041040c0700e104500a600c1d0158a0324890340151000308090078654000c00483c0d2a4122030308606616904600c01e514491b07101c1300da210041400d03580401c020710540c0c1c605189940148251026000203071604c506603031b58101102c0040d200105980d40032542088103040d100848001000e40c000600c1420303690803103c0c25600d58039409214118117210ac4488681d0014542011038401c3d2640900c0c0460303100c0715031030904050305100f440c1c2d07100d070074002ca81034042550015181c0052402280244100042c01d00301948940702801104003200b6070101040c09070910708011100b02d0010901b9110301d41e1641040c8980f10394440a920b001d4000800410000ba40003104541142400d00704510402c0144800703880c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 914116276 1250 914115026 914115029
    0x60a0509100b030a02041d060a0603121b0210031a030c03061f0503060712140601050f0a1403180f010b03100c030e12130609120813091112070c050601 66
    0x400c0d40c45007000b05040d2401d019200340640e02910500c41505128403032044041d251900c8030b103d124001c009a180c001c240918021a41c10000740c400c40f84100c1400c8848400000380c515006c002e24404400607255190300d514001c0180e42e0000703001d000e4105001c003485640150714460381c882ca404062540d80030406130303000805c00c6442c02000100300100d117030309070342071340311799410b000d0081003003141134202d106c0d040f0001c8124810402207000341d15208842a06a4425001410520000c079030700300c0e0036000340000641402c04140141d0694940c1c0c620b40d0044500718203030700c0700d0709261f007901e40c003004456809201d401c028003910300100c000c00d50b6101e4811491540075100c0700000c811902984c002ca070394000d12019104400c46021402003141c1c070010b07080e0941d0300d01d081c001503c03a115203a14010345852000c80c1da03100089071200d0340740760003042d0078070030004a445000486011034401c04920904602081e900c42d4558560b04441c00801011401072101100d0950005200031442c03031b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 914117526 1250 914116276 914116303
    0x6091023070b060120070b030a0e0d0c0803060103271703090d03050402060702041b081506030f090309090103030f09061d2209141c05030a0b06190809060a0509 70
    0x2c61910005400904d0b85c0d0400c090340351743c003502c030011480c400200021403007007841c20f0040c0240c103c0c4070314582d9611442404003001800083e1402e00150110004607000b0398145400b08406960410746c1520350a00d001c010880200552200c0c02c0141228010f143c000d480c620003821450446113030350320b52807014134000802d070f42c8000160456484a007501d0170150080d20802030801601c458040880c00d80b0035100104107200002018640000001e00f1409406800c450446e141d0310804495524050705120071400140104601511070089a900035030003a607501d00040c0e0000b2001d0005d5040350040c50802440308904041c0c0c5c802c6941e03d04d10200151b8001c070381060b1041c00c000c284d61000320310300403071420074004200f030240c200360056000c441181511610309031408468010b180600c1c1c4000400c20502c0001c407400c00b141e220b03601040000d0300e031524120111082841006000b0351203404107050809008030710004011880c1e01c941070b100100320600705480000d60b83c2c2600244070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 914118776 1250 914117526 914117537
    0x9011b050a0c080c0d09050f0f1c061119090e04021c050106060938030403110712200a1403070902030a05090d080c1806091023070b0601 60
    0x507564810040304080e1504005155118400030032001d4a44104800000004040d0340d0040b40038a0f1003e55169840001441204409162024000011007030030700e46040028845040c00811b0003030040c0b140d4003061580c815940c1176151201d10154004400860801010780f409101a5081c1040d0b16042078048076a2400012111101142030000c0a4002c105500b0410b0010744160000c1ca9902960104c604034070443e1418051480402d00e80503280c8043c0c0e45864613402100183e00007540c01038028503020b6100380040c0e1500d1714000c0190b10199646140d030343c0020038003071905400c0010102f0402c0c0d2400103281d5000260305400f69000e51810300000190b0045251f4040200c1002414103010542d2a03141450840c0c2c0204000c44020b80c09004902440c200248900c032074610030040c000113682400d80380241d481e80240c00c88480c0750840030030454800a544c031038801c000c22680c0c0d40e41e403050b29503400403102d410141c540b594213241d15043c81100000760a11154030380c007500a2800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 914120026 1250 914118776 914118787
    0x3020114070c0c17210d110909040602130905010312120e07060f0e03010e0f0d020a0c1412010e01060603150303090e3606010b21271509011b05 63
    0x9042c00c080714080e003071403205501d1705503048400b042009000401d50001d020042d11b0380d070010300e40440c864007801a5002e00404005000a2241c2d80035000141076402c460101d144c8510380e800c01c942c82a0015208503803644a201c3c403059000c40c09002c801e0030401c0911140261503801075403442c0c2c07405003d040c041c0000010310440d110300c0000442070741c01402030085c5000d0b418210380721540c1480d001901d0091468550007940001070b483c20003680103110191040c42c4c41d151400f000481007119500c61260149224899824010b05d07018404000001419615044000e01140c00800a9601c10f040408040011a81000302a4200c1e080805104000d0b50f1703050300b00a600702d140302840460312070340c50000d4030726556403c2e800c0c25100c003804483c41d990301c0720550301d224012110080031300100a006000112030102c2090f4001d940018107103503040c452103218680d40150480c00440340e005144da104c0c5112132610f0306400c481500b000b0041320000032280c0c8401c44000d00e452041c480000344 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 914121276 1250 914120026 914120069
    0x150e0f010e0a06121a0a30082101120311070b1204050f2113030605090d03051501050901110a170307020609010b1e011b03020114070c0c 60
    0x840721a00380010700c040c9850380c4849000d003c21600264005046250442100f680392842581d248202801070006c143da511f44a0210582070601c2c12600f83c0e1114200340446099404a035409898441c190072a01d8201d0032078180c3d070819400c0c80607040b9011200c0104000d0314100300750240c0350740cd85802c0004001c4031000a1600149a011381c0d1004030019005241550950526000354483c80c180d82040c0000541141e80300300c0c0341502e18181040040c000050080e400040c030007011650780c2c0313034401540c9807900012a4000c80b501d00440d04003007013081c90580e140c407a165000800303043c85903c40000ca00002d001c2c3c001c002c880380c14840e656620782a801010000e100c00690311800f00b0741a0268041d00140681066035860094070542c804250064018010841040c4028000741d0600112620a401c26001d02c0e0005060098004c0081c5449030b400807d000300a000c0d40020601120550701c05060010052007a0300700072a410b2803400041c1c1c505405811a0071801e80070b0719141a207034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 914122526 1250 914121276 914121287
    0x61d090c0f0d180807260a12140c131e05190312020705040b0904052e0e0a12090812030a1b02060103050c060c0312040602070803040b060a150e0f01 65
    0x3481e01440c0c40300956030b281009413010007000c01c00d100c1d134804407001c1c0d1800000b41c401b80e42c42242620b542824813200010a100e4451420703090f0001c0d4020510a4200d0010100200240d030034000d8907900041803403401c2d81c0511240001d0602c81210141c1c0020440c41d814070001e28007606114100170203c0d4008190044240c45c007440c3c0240c036199503605241c50103959100b03540701e91b901031410304a82c0c8102d4502604110710070317074120000c0c003a004054040c480d400c442c02d58a40e01a01c02d2710142440e40b002c03503c114aa40ca000100600004070340381045414a0061075180d420021841024420b150010848803107202503a00c038261a17848464000d00a4403030301e0058503124842d9884c03500101d9000440034120b034081d80c00d44862031010b001340143ca101d0141d115105500401908a9030384c52031050a070300074042c050040c03c100d02a82c4d8412964026501501c0c00d500280500181d441e1010982d00100000d41e14400600d441c040c0c058226075030010503d21598450b101c0e80040c1e401503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 914123776 1250 914122526 914122541
    0x809061306090513050403052a0a0804080c060304020a301a010806100608062e0f0c02090c03040615080109110f01081906030b01061d090c0f0d 63
    0x884032451294694030010120845881a02d208940854091840070007510520340250742603960549406160b12107190001580c0c1149000302c055a20201c0c80183c0900c14100018880e4003000c0c1d9079490060607910704025040f02c28801d039030400a1200503600d00008074116001e0801c001841c03071b0030303004071034050b1044100080d42c11210010503007082079480a40c00e818041120b681010f076240d010321655948211100c40b02a590b002c001d01401e40110038640e40104001c2046100c0060300c528004100380d0f100140700001010f41d514542160810080c16241030b46141010b0b40070304a400150f5145005026403142d600c0000c00728003803143c00d40000c1507440c071990340c90703d45547c1c4c1d500341402440f00c1482900d081c154000080d9030b038a0400c00d00d55813800b0580d81e03080503840d811512040500100e02c011260360307440780008000b0341d000101d42d00038491600d4400350030390341007600c0000d100784400c06846a0306101c2003004a090342401d8540c0520401c403225225481607112a0083c202c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 914125026 1250 914123776 914123797
    0x60c0510090c06082a0c01020408030c06010302150c150a0b03160614030f0f0c0705071211010206041a070c050a06060614120109022503080403080702070e04080906 72
    0x518031484188600c40b10b800088454aa4824031142d451a24640105620804c0c214a560a501d00c248082c80618084c18030075401d1000107180550f94040300d4515031181c594420a600100010030070b61500007206d20760200241d1540b4a40f40642e1134281e141d140720403002c0700c030124020106004a00030303400f408445001408840c0740c0c01d03000003003100600301407103003030001606104240781d00c802c68410b4070b01a0b40800084006510340c440d01110300c0340010105403054000b44840e9010270303010454040107104010465100c0c0c92070f41403543d440c03207480c01c415044d980f00d0001c0c40009440b444151908042400c1407040329150910111007200c2450381c00b400701d104005400e4203008060340504100d0b1170700d403600d0380100d407a1050041e650281c000040b846035101c10040003d65450340003042020a03608035086114040c112400500c0c1000c1d0382a03002481d54400c100400d9000450260002540d000601d08645441c82110070300800606c01131003181c01241e5450b03651035200694505500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 914126276 1250 914125026 914125031
    0xf0f020417010e2b0c080c060109061a09090a150906090621030e030309060406080906060f010503070e010c06050f09150907031407080f0a150c0c08090a050604120605180601060c0510 80
    0x7981c41f036603644d00203010b100c1001d807030245d0000e100700c010390040310380c2e4000c0c10941d41011a0f0340108803649200500404039192240752902030240040e140c8406040c10000c0001d0031030400280c032040340c09940120044106540100c1034044514180440136075240c501600c101603d10003003030442c0583c0d0145900010b004c070340860201c0c0c10030721172841240e004089490366034805040010f00040c440103035000c5082040401e60751403299a40c40303034408060505241407031315a52100202d44044403501c114041605c10301c003c02d40144005001042603008004003418440c21041d140c05e1244801800102c00c1c4c44040861941070228000a00d1100143d4041e540d51030000703511801a400e040b1044400002d610300400090701c00c0b014100a2a80c80d0548085d90395140301c0e5513840394005641c00082c4004c001015911800184060410060100320750712281c54403109461002e00001062450941e04500d4040009502070454031985011140690341381003c80c02d00080c00128141e250 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 914127526 1250 914126276 914126287
    0x142515050709080123040803070903170702030d03090b01060e01030f15150302070804050f0f0901151403010b0702060912060916080115090f0f020417010e2b0c08 71
    0xc0c1c02c95400411035401800910100003ca0101c1031208402000c1102d58808080440c000c11040009164801c002d400c002c2070090700e80d22804042c1100920702c500143c800610401141800e12010400300350728101403011224655440c1030645050140004201c1c04a154246980c482d0308000700c004203642d000c12002c00c2c0120f82003100000c901640c100c1c00c500300341201d00d2500c00e2080707420854100c0240350904d803c1904201d2a000300048140e44000030020914447d074612424500a000f00380d9228101044e50201078000501c034164040968000e1004108000d8514100c54685504441080d42c642c0704100098181c030600709032504511a040400c40211070000c0c110300140c8420300e0200340c5a41d102c205500369070580c4660300c0d070001c001d50100960b06603504102c9600c00d4801001ca00a90500c1001c4100c0e0480c1c0e00141c03a891404140b181152428411130f200c010b9240c0181c4802d8115034000300400300c02040707084504041039540d6095622500100040c0703588030860580c0d88 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 914128776 1250 914127526 914127541
    0xc0219060b0102010b030609061512030d0507020111090109120204230a15030515040501020d0f020904061e140409060614091008120f04120f0314251505 67
    0x604440700c07124003661804131214001c0c42c001542500c14a1443c000704202e5441108200c1030310000c07200c81d504580100c400d6241100207201802e58036401590001e041e00c1c102d40001d09440410711040007282041249000d1668030030440c0003500c035201c01280765140a4800f250041001004245860b4020080c206a02224185050051000250621084c1c0d4402c84020201c00d1500c4000c2c220b07403044544000c0254402c04242e4004d005a00040c200b94001490340c042e07409004600c00700c242d0019420400b840c0900c501030152400c42c1e1059181011398002000381c03c02402803040104440c05100820742da550030008140e07500450610031195030300c0e581d038114140c1761b80c071a10500d004000a0020038449039003c00711142c0c2c030300410011403451012142d540c4111000b01010305d0400001c01d000d8141200b960680e84908140d0152004078240180700002504000000000c1000440c0c0c0410002450030040000048119400286880e0040307c5140900403440b11500304010030614 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 914130026 1250 914128776 914128781
    0x1012050604050d0305100e15120a05060901060b03070c051f06030320031602010302210f010807061d12060a1a060702090408072a061716030c021906 65
    0xa24442c000310749241d030040106500780c0300103c52900341a000d400c0100580c0360000c0083c1d8000d400c400c0800408140c10004c20b4003404c007691005c0560b0300c062800000c000e41005030b160311102020003002040c3c14107801c0384041c403028000e0402c1143c02c2040505001083c0302c06410100d0301104100801c2c40d28421802510241c8015004200d555012940242007400034260031f1280b480a90b20b030820b400580c1601c030405980590401d0707400d002c450003c18544010346201001e00b0a414203d04d04070aa1a01e40c4105800c000082e03002044100030301900040042c1c4a02e4100c0c0515000c0800c54011406003c0441d221003864490385013401318070081a4007042042c249010f1400b003020b0444240942d07440740031002034000071140001004680c240010b442102e01c0b50308144e07140314a204140360540c8050300a40c20391025507504005403038001e940105842545642244070340f41802910180070000c1041c07409041c2c48200300c100580c030074000c000d59204040e1201d1a8a442c90504000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 914131276 1250 914130026 914130031
    0x405061804260913050a020f0d060905090a0c0509070309060f09110102070b0f0904021905030603060709060f0c0501020408030c01020903070e010b1c0b06120703150b04090510120506 80
    0x1c4088810680c0c0802c940b100d81100d4024501620010a88011246402c005e02e0000c01c0400342a07824010340d00940c60300300040c05880c1e404a00810388030b040c10680400c41f44d02402c00c0035207070b00003201480003610000c21482102c00c110b03225403c5559044083e006400d0030701c3c000340300e50710300584802c500020761702a54446016a105016003108a8010390ba155101e00803010705c3d00e0b05002e820710030050100146022480504050b0416034103902c3d803001c604150f192000806c1020003000030909081101c6640306050b490030104403468402d001e0500000b001903a401c0140c90580b4030144800bd4046500428a0f20100c135601d16102980724001c2d0465000d0320301c24042c0c42000141c1c1c104540c1c4450680d001803402c6460500d0040e4140e950021401c0039540e00e0b511107243e06880c1e1340e008090031030700c039005000e00c0f101c1c030744400d00038102c82c1510f00708001000102000c0c0405840041601d01341e64800000040c50344034512424101c260550105030400c03203031600c1d0300400070702258150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 914132526 1250 914131276 914131313
    0x91e03100f090317070207090504051c0906030509010c0806090a0603020a0f050114390102070f0b07111207020f0d062910050d1d0f2401050405061804 66
    0x700341e41140c09283c444d2040d03400c880140c1c0100014824500d030350340702c2c90300280310360304690069401d0f00720f484042040181e00000300c1c1c3ca4003810420160107002c0e844c4c0c0007210000800220344d120001503d250b4015182c14001c0e803448000500044040d4449801b13940c0040c04003501c265104e10030b10159010303011380c1e80041c000216082d0407036000002d42d40d42e03030480150a0410280ea0421702c4101d072102c80025031203080031030044860b0400f84004c00d5214010803480e43c6040003030616841000307018018108010308800716402d81007010400408100200e100d042d0780c0d00d914000640901c1840c030074258041a43c0200404001070741c1d0102e6a004030640140c011502040015070442d1501e0546603000116480303844e1510b0b00c60b800828444d80c950100050000b004052a202c15044e4001c400203513110480c18448035504001c0300d64400300c2501017400d500e03002030505800c0c03641032184070701440d21180030030840d0340c0d80603840c883c180d81e011a504040c54642020705d0b58220944010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 914133776 1250 914132526 914132537
    0x7090b1e220218090f060d150203270a050607110307170702040b100f0302030c1611040b030c130e2b080c07050a120504090c090515091e03100f0903 65
    0x100080c24141303c01c034801d4203100355a014998624040c00748220100758100e50300381014000c0c601211151001c0d6014019010400400748070f40c104c01d00c4031814066038541c3c141e00034106100041c800141969002e4014540020a41c0307480040340c1c5140202c0d4401002e142800f0144070a0480e04001b41000a0003110300380200034260040c0910800b01110410000f51000b0510303503410b0013a0000d542102c01c5280461900081008100342000c50340400c440e4028030b1171404850f40b0b043d0241c10103a03002103028141440105002822005000060440c110345035000c04c1c00c28041400350002ca090f8401c0071400030b481516880c0001d8045440c1c2d1340200c2c5960b0042900585100251590310ba440700040c01e044041e0303105c0080400099102d0820807004200101d8803410034003072440c13202c0441c0c8510341443c0c20602000740c405900c00c10003112400501084040380e5560008903e450f4045c6010513000308841d000c80d0801240d121260791407802c080d1100d0605450ba400000f03541d0203a0b980 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 914135026 1250 914133776 914133817
    0x30f020711130207150b03030909040302060a0e070b071b030803040b010812070f0b0a240602071401020a020d110607150f0504030509100203090a06030b0307090b1e2202 74
    0xc804a014813003001e482c00000328804501d0902562145103008002001c403800d044103d400144800c50803201200140c200c202449800d55a41c012682d030051340e140030304000c1c0e0a02c9150159030040d460054424803d10702445c46803461518010061600b00641907aa0703e0681400d0b0071820080c4a40c031600e100c0c0700d01050340c441d000c10079960744551288400c11481d429031501c1803501009411803039515940d54071401c40d40ca07410a00c0301d0f0100091503084d0302601d82040641042c070654031480d50403032884032000c0160390106040400e15070440d0119501c20040c1030070000108207a40844d0000c50010764030003400010b44031041c0c411400b6200388801c001d507000305000c1d92400d0310020081078007401010224a800c4410300544030312441180c2c18502e880d000200791032882d034448800700e60750750600c1070b40c1c3c03c042c48a08060540648188560011700000c51091828500012500c0101400b5034143c3da4580000300481005600250200e801e03804180380258001103001000b00b0150a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 914136276 1250 914135026 914135059
    0x30f070908010e03070b091903030b102f030c10090c06030c170601110303130506010e010b07031d04020705010501080c19051e060a0807120624030f020711 68
    0x30b081d0090440070301450038030380c0550303036110000401f50401505000f00354180e130720035044083d00703062140242d801041d0f2403c05020b0200703041c0703d5031443c001c0007500c2100e0924008601c1c00d4051030b40b280301e0541d50303c0034540c40321411401420920051b034010801c40c0c010308440c507040211582d00440c00d0780810b0f56940425000c0f103404840c0c0101041c2013074035140301aa14030b121140e101c50306050088191000001c11415944201e801d0f001c01c0340800d19090030b000b8204411400362104c000c1c03004180d41800000704441c000c6400c0103040100a846001c50011000804c02a022002c0c206640f103a0b410702d0054040e000900659145104500030180103140806882510b200d11700100b40c1043c0c188401d10400c10708110b40300000c1e0002c46280809510350000400385000c030b540d10849981014400141481c0c141302100400f2814010184503030054100820030b003220b080d00e10011030022280907000703003450880b00701d00a88007141810501801c808050350a0004503800c3e1040c0340541c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 914137526 1250 914136276 914136281
    0x10605030928120219030c0b060904020114090f0a060f020d030605240403080313060509060c160507031704092304030f12020f19082a040803030f07090801 68
    0x660b1100308001d02071144001c1003075422180700802c0c0c10310543c0c00c02881c0100c00d070216001803c0840c00140c504282509000c4c0c21403007603400030422111000d150500d5000202840c064402d02c03842024002084003095440b16076041d0610801b41c6100c05007960303403a029088525800c003440c00b60140f0041811018802e01ca001d0035204020030030b1001071000500700d47c801e8444052641c0c4100200b00c0440401c4945014510448800034041c8036040c891505005072032024089403916031024003800000d04c900007e407680004603003041c6400001030b0601d1807130401c150384094007000790003070015604a2241d00620030354000d084244088400700c001362104e51501081c0741e1081c071802c00481d001a108550039140d01445203818004985452010030803070340502d032a2440c640e00081d0078400105d2092a0320349041540c1816405403914030000f81c10076040c59070141444206040c42d04921000d54143c1e4003804030704d0200d0361a454042c4490114081c00c1d2100c0000c44e1101d0400168035a050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 914138776 1250 914137526 914137573
    0x7030b04060f1701021b0106050114130902030411120f0f0601051003180c0e040201080106030216060203090f07120b090a050d05030a020405090a0b1f02030906070602040e0106050309 80
    0x202c0702e8603d005400501140014803035503855408008599a00003901e0045903204030400000415520381800500081303c840700407202140c0503c4141d03030325500d03030841d407040700e042c0d50b0050780d66030f164907282c0707060b0142d004060360002d9400d81e842100c0d500003407000c4d030703d0300138408031443c550481c8034242d600c0209102e066405000c46003491401440f03604041c916091340c0601040b440010360750400b40b100a03400c86500c1115420410040d503920043d240d0040c174003400e00718a001040800d41d600f00481041c0909a40d800002103000c80000708410703a01201c0140603100341503101e48100c046a9800c100c00d4031a9120b03503000c5021201c0101380c2c0b100842e4444014000400300007401d81d0503800003408007081c1e5900b848001413644603c02034510038042401c0014900c408041000440112040c2c032110b042040608080907036000000c940c400c0d0000c170307011030722440b0a10700031020744150b07000004100840c00c00012880e400c40042d41c0510240300c15500f8130b84803030084240e0807012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 914140026 1250 914138776 914138789
    0xb04050919060308190e12030d050903090a03050109020909030901051e0f0c0607030e120702060f0702060708070b07031b0e0307080118030201150e012706060807030b0406 75
    0x684041a0384049403101c0d0000e1204200300468815980e4035460040e400010038810b14507450380d0041040766200481004103102180d8100594541100031a0b4a01403800c400c21031070317a15404a403018200300161240c4141c020070b403104c0c55031240350880c080e205981c4102d00407540400860700004000c821381d4615001a9030f054204010040f1010103032030000703c00c5902070010085001d440d420700c00107082c40503201006040606055100030100c804801c010314540d0040890890b031401000100c03815260112809a190340302c0c0305003000f42d403040030402940803000050810810031480090900e0070b01814496031156541c1c401601640e08460654851a51461502c1c89050091041d454244c8024085a0f8050b8032000401c3c21141c00c84900102001c2c04246481016424002c0304030343d042182d148940585080907400c8280418025001d01e03aa08000118140c1c20000d4000303017840b00d4010510101d81d4508014040701c8040d43c0400000303040080031407250504c0d00885003161803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 914141276 1250 914140026 914140039
    0x30b030c041a130b0409111c0506011401030608010e0609060c0319110904050103030201060f0b2118150a0501170a060b0a0306140a060815060402090a08030a17010b0405 74
    0x10b82904001c4110100d21850f08a6aa140301d8060305496034412490b032280700740318a1a46070381620030001003040d08010b25202e00c88000310f5100103100450780c50304561001c1e10048060500200503805400340d0f03000707002590301e80b00c11132580350302c00905940204004000d66001d61503a849a034850b10040b1640080c0e2403004a5106002c07030554880031f88060710280041c105021000000c00f43d80d000e90058005039107821091040c481c842501c40300502c51680340341d00d0101d20b0250583e003202d40401c0e0048100b00032000a2071186016004040210330b101a1280032195401d0001032480a8441041444c5490004076502c6440d003004804040d0480090001d0a00d9070342c0c0002130300f00c1020f01c03500305039407480020005d1130354081c15281c01c8003036080c3d500615100100e4400c8924941c008035141d03028200c54024000700e0103056030004016240542d980b0f0030701e00411095501a40040154480002c40074100d0b54070103103c1e644130804420720344090742e035120445030ad4001c9020701640b009 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 914142526 1250 914141276 914141321
    0x5070f020f0612040c0315180605072001020a1803031b0813030506040b06040219052a0d0f020706051c060e0403020f0708010501030305030f180d030b030c04 69
    0x54900d40c0755156980041149141c50b40741c01002c0ca0008055400b107410021794107061040005003078012140010003401040341c81a00c1030950034464815101826907641c54000c903103500e02c22000594035078000740c41a120103850204450007984202501400511350b2071550031980d005d0300c216001c498050340c802103c6101446411450a480c420440c4d101e002040464035001c100340c42e00d030003140904044c3c90185040d0400210b0100700804040c4200d104000d00f8441c9080c40e8503c1803102c229107032258465a8542e9190f010004801c50b914001d003140b4901101103a00051200c128032041e41c8050b8a8100c0c000203907078482c23140c00703040003080c0d00b44090340c00104183c069800c001ca0009001c203401d9501c0031280c1071644140c5058006811002c0f804800c0c1c2c41c10010100102100d034001c011390361441d18001c0080c00050107c00d085015900440c84801e030315401e02e0b90310b4407140103072181c148140102500030944d01c030304140640a050f452000780d1a09108421407140000d440c0c0039003c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 914143776 1250 914142526 914142529
    0x70f0e0907050c0a02030111181c140c09180d0c1e0804030b010605071b080a060203060d240c1403070507050a0506070309110301180b06040618150605070f02 69
    0x75041180c07003e4003880750500d880017580d0240501200e00c2c2041161542e103490315440510500160344444e40500d03003900c006903d0411858141440d41e4204104680040d4001c0803541440714034030b8101d038080c0b04801404128401e0407016040048114102c070113200c00b615050b21003a8443c40e0103070240e45202c0003071803610301000c08c3d803009510503c20319107465101c0c1e0f248000a40203030000301c00203034085002010007440a020105982d2004004c5494914280807180c0d92490004003c02154010011624a40b50700e60740c80c8250390310014828503511055112045003510181c1d40003c2c0741440030007500d1368018400c00d81c040e000c00c0700c900c0c6150fa13803580030388403640042000c4076244100b030030f081c000c2034041c402c0c580034501680c0d020840b101641000d51516905000e4907100340d15112650004451440d0401e18072a4131404000b140e030340b214001401007881354061820702d01d03020303000640700c00c16510200c40054000e00c00c9500a0300e40350103c8080c010104001d0401c0110800035015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 914145026 1250 914143776 914143787
    0xf01090b040f060f030e1c180803041a1c020f1b0609010c05090a1e08030d05040507150210110f04030f0c0f030206031b0f0f0d0c0327050708010212070f0e0907 70
    0x340c8210742440d2019282c404807440ca0040300749d00034002c036000410180b10b2500c800070024894000c10307414605140040c3c030700045d0b0b01100000c0c5440300c0e40c002610841e404414040d190041a407107190640d11015640e11619000202c03014000c82d4a4580c1035181d0f03500920545001440c060000c0003002d04284158000007031031904188100c01c42c0c00c00040041041000b0a0310000c0000080b800f030601d03240152070001150080110520021402c031100c80e4000741008960034142030114010110b140700004034820032141d000d81c6c2c00002808000d001c0301112481234648100f42920b0719139a200c08144c44000c803400000e611031070410106080c2c407414481c0f1441c20802c603000038580102c1c02d00c2c61181e98170041852298220210722484520070900c00c120000300c4605060140074400592201c102c000f010b29920303024880d800c03890501400300101805064940c00866550030803002c0d81007074503070071500000001c031101d4044203010b10500d500b05030302c1c2d0044c186440e592100b8600344c42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 914146276 1250 914145026 914145073
    0x11030c040909060e06090d1b2d02100201090c2310050405100c030f02010c0e011b1e0210020a080f180d06020309010b03010e03090f01090b040f060f030e 67
    0x1a030350740710440c2126100e810b01c895405018900014045480c80c100054080950301401d80c0b48040800d020030041a50502701e03100c001d04c211040c505d40f078405072421070f0301c6a50709000ba420070b101c1c8560b202029015880910300c24050b40060400698a458140401484820f02c44003445034402140090070416008104045103040c110b0400c3e0300c1d100411401a41c0907021800039007501c008406240d001090700c0710391861403000b8480c07130508840240110762107541b2141007000000f201032020f0205140c400c0010742c048070b01580c02c1817215041d00c09003034021099108064402600507514000030b42856456404a101d5081c00c800d5900307000079400c65440144840b00100040d545650340200140a0b40d11a040040c1c407400c043d0409400c42c0c041c030451750300980c074040c498a01e90000005490004204403040580703140600b00480344d01e0f1641c0d2022074503182c0450046144071409250000b650322560755113100d940d4401c0304800b239605900c1c3e01240ca03088500e00c940c123060300b60300496 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 914147526 1250 914146276 914146283
    0x1f230709140a0b070f3807020c030601050f01050c012a1e0305180a050a03080a09020a09020703110a08070b06060f03190b10110c01020d0f030e0703060911010311030c040909 76
    0x910a2104031b2515410f285150340c1e0301040103010448103c01100c0c0c201d00d6800c00d02600c01024402240804130344d46403410f0007001d1296003559449115a03105008407030100d4001030090007225003841514601ca144404e0070640c05200324100907003103100c6c004201d15030f5090004056000380c0c0b0b0340c00358000c2401800c1c020406081c000301100c0c0640c00c000b54a102c03403184009000c82d50650030001c2c07900b000580542200d5040045450141c0c1d24003120703000f039500000c0010703070750700440c0b0b4159000301360341c0c0c0402e80c240a14800380c418005068003510f00180140003441d0380d0ba40c0c3c4010041144290590a00c004800b407011400c941523110305616801d11311075000666914200000da1f0402103503941100141c4424590200b00e0004c2c09aa090740300d0a0005040307040089202a061b030010b800c405041607907a144419002800300042d400032364004008000f03144041c00c19880002c10104064042410490064034a4000e50101e85c1324000d102c40c29420a030030482900094010902c042d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 914148776 1250 914147526 914147543
    0xc060a0801060f0909020f032e06051606050408030405070b03061005071a011e0b12040219031712070804021c0204060b03010b030412021f230709140a0b070f 69
    0x405c40200745d1000b0440c2204515901da103d1900b01202540300c02c0d50b803e40001125505003510000071080c804000740c1c1d500f0300f801d6448000c1807408030800da200d4040500028100303000d1100b4451544006c601030303070050042e03c0340551142950000b6100c01e50b07040303401c42444080b000c64148214041c0994a1113082541c801503d600304001c60b44900f03810202215041600303d03030b110071480760b201004042e01d43c2814100030000340c0c080c000880040029000e510096a40c01c116504a142d51000d550710914050750003443e051240e15503042038014403402a00c01c40442c3d078090185c4c0030b1600c140d9004100f00c02c19080c0c54401464003007514412a081b9840b03003000704100070701d04040d42c040c140b007050140d00ca1a2504000048a90070000700c0155000200342c2080301007245180300760000341e41c0340071824100b02c904948440030300340d0a250036443c07500d0170b000b01254400401400c4070030f5a04213030308031801c0c14108181004a445444130040c010024440051030b05c21002d040980100e142 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 914150026 1250 914148776 914148779
    0x9090a03080610110d0f0e03010e100207020604090203091513020d03031a06041706010e0709030803100312121b0504032d03020a021309081209010f06030506090c060a0801060f09 78
    0x40500e17041c101440040400c07410360044035543e40c04403480d103840d00100c00902050b00d136008156154030000c00d2070740541341c00140f040305540b14482110010000c10b00119901c3c5400e4400b01e4aa4801442944507600d20700c01059869840c50303444107483d41c00074003030440204142d90542c010881c9c2052001d180d10449a262034560324100544000c001e00800901000701c4c1c140c9840c28484160014000c0380da4050501c5205940b04048809a980c400b0304c4640d13a40b03400181c5081580c071648002e003c00f02e0f400284014540c06020740c82e07100c000a10910440032211880d00048500040b40c1000603014802003003c51103c0040c01c03052820025036440a8546160b42c074101c00500c8029005641b20210709021420107a618940840360b0305010802221035a84501c802d2003003000000200030b494020401c200d10a40c01807100c1051040100a40c1c0d40c0e914205490f18000c0311a405180159490f01446007003803400c0701ca03d1081750742e40a1103a820800150f480f20b600803041c00030400815030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 914151276 1250 914150026 914150057
    0xa05090937030801050a35030d020f070b0109020a050a12060e0903031603090c1202010201060504050907080f0c030606012016140a180b18070e09090a03080610 70
    0xc04014550183c2d0321242958100024424000c800342d000d0040421040c807101030840b5200c1255001e4041444892200040c400c2c5d407910b18000e141d08514007920014444409910b40350041c588103108101414442e83e903920120200c1c00b07844000e001081c4104031900859102e151b043e1300b0801050070000b891a00c51010340071004081714140350541c4008240312420000b0038404040c220a4581884581d680e80e170760031000340301489079074401c0170068100c07003c580c000c0d0480c802408015100b00080d1422040c055682e1585115507500d07030050342e013910034101011543e85003050340940107211589480004403030402c0000c03a00e00f00011299503030740750100103110300302e41da0150954a01c011401c0c0a00e003141410240a00c0780700348002c100c2000b05800d444594900c101c1c030101c0004801100a02180c4003030440e40400d651480c444040112860f006540c0c10340718482900c0404580c3d0b10608200e80d1003c640324040c0c04549030f04001002441d10300300085880c400c91401c204030170f09800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 914152526 1250 914151276 914151373
    0x21e01110a0309032703080d0237170609040c0b0a09050a1e031214120901150b03040f0f06050f0601020606060403030e10030204080f0601050a050909 66
    0x1003800780081d444100f02c03410305030300400f0001a0070080e03450360720782e200507030340024003001c1403000803e0850042100a0100b803540e05641380004107868882200b503410928414076404c0300c5800c1d190302c6034465841080351180351541d6903664400c120391380548480082110f2064020807c036500805010040b90b40351040b005091340710030503180d50030381d1420b14041141085844e0030050040c604030350f2103007030105152001421079402400e20f421640d0b105038120b40781c0e61169a43c1c0c890a20016a0381c041002e088401486004940c0003044845040300a201c1c3d00d14040c4120340d00303007000b4000b0070041010341001d5200540300b02d021078100802607440400340e4000710340c82000380390404104652541c0602034075a000c3e80441e00c1c0c81c40d007410341c2d8000d00140c0310b0584083c042d075060070118440034081c3c1d04a03000b50070003070200c0c2c003241402020a56211400d0086601415080800242a0410264190080d65410050700a24600c0c40d00742c107101035005600000250304d281036041900150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 914153776 1250 914152526 914152537
    0x30706090206091905040b010807020c010c050c0604060504260706120216051011210c070f150e030909150118180b0307063006060905040b040507021e0111 68
    0x248400b0113070302d0070b0100012a0a01101c45040c0001c1d201000300d15075002c13803000c10942090800108072403050411707503e07080103030743e2a64100710b00250110300190000003800c12548826104031040103100305440700c0503141460100325601403201071088901070b110490a8124201d00141440d40d40100010f11004c03007502550350350021010005a11035500604500381c214a1905107807003240508030710189030100142e10030080c048007181151440b5030440f940c0e40e4000342603129032412400c12400703000614028144403440e000c0f051241d481c010041c4d5501540003807911840341d407111401004140e00801c036074104080341c071500c1484032210100740064042035040403212002c00410908442d1150f000301e01c00d90101100f000042c5d0702161445da644001081340f0b0449120015811082d0b100503800008503081400204a80b544840d01d00d044a004841c240000400c101c240021914196001c83c0103803c505440b02d5981c0290844585900b1130701d00014081d00c1100985c517858110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 914155026 1250 914153776 914153809
    0x1020a151413031d210f0111250206030a0b1201091118040206071119090c140c150c0706020705010c03110301081c0e030a110a0f0803070609020609 65
    0x210750b40c42040c076074460000020100b142000d4100003180768005410303004841c05045106096103010320b2100400c2c045a08030810a000070b10a4868900c9403290700c0d00141641c030b20700c0342e802083c14820038800890b10701c15034002d4411891600c6401c0703500007a142c0c4200c203d40003080c00501014200091055085140c051007441910740c4403c1d0412a82c80e43c10658040c4050f0088144009070b90303003104503a05554054a12000f1b8140c10740482c0c0c203120109410301070034104080c00030307010190303801880083e555580c07800c10954411030503c005000b140c80d9100581c0c04003040308058180e070091182c0050303100c0422414040e1980e1500140d90281d482102d00303075160041440b81d5a0580601d0102c0344800c0183d50444d03042910155442c1e03000c0b00c406030350380d8030403411051980c040d40c061162594003809680250b00c49080150990614003451070050b9000000018440d48090450043d241c040000c0c610b0300c1a1601d44401501c680030003660301400802004403946d030340e5002d01c800c201d207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 914156276 1250 914155026 914155051
    0x17180108131a070f110304090207020316090515062809120809030607020106030203061303050d0603030c230c010e03100212070906030212010509150603010602031c0b01020a1514 78
    0x3000c403c000c0060720454000e205014040344c0040040d00003009940c191004180b0040e00c442003800001d19240000a03e48922120040701240c105a29000b007481154160904419021541c0a01c00c0070300c141a4100d80180240c8031161401c140d0180c0b07000640700500c0c1601102c2e4071107080842000d03500408484070040080c00c0d1410f810b0038801070780d10a40c6400200035491540e0013003a15000c0045c00480f04d14442d5100030700b054041d20550b2021006204200000d070345034500079240340017500064501804101442d1280e01401034621081e00c6e0602c060005030034a0001540e4075011816201d5050198020a42d8034481c40d2002d0104001c0c00000e20196041c410f5003d00307810415002502014010424804041814013400c1e044aa05450700d070403c6d95a400303007461030404030011a51108000000280069002018001211a51030a0082202901038400484402d2010640036030041d0030758102054161102d0015405001700229404840c4048203154074800c45e260740d604103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 914157526 1250 914156276 914156281
    0x50925020c1315031b0f0803040f17030c150415050402130e19061b0206010b040510030216080a110303041203050415060b0d1a150c07031a0417180108131a 68
    0x189891b0b80358000307203201000b441c40e260400d01d001210003a540111911031340e00d06d02c22440d0340707010011900680070781001d0340d4414022000100306140d00b0380d4151400744900300381c680501c0d02480303218081d82d802452205d00440020502021707110a245100440c0123115482d449051000a107500840c03196000181220344401c040c84890104a0700340e0440d8031903401480780310760b060300311001d44404903950800ca0580900480180c41414050102a03c4e4140741e41c00304041344001e041d0f110700035190b00007840c0b1170350502ca5490004640142c9840182e0500c40101c0b4040e0b80a942c005000b100c22205070400c001c52841562a250300a14108100084c00800e88009214545c8115005103150700454602400225030500340e512204e10cc03400001c200d0100901000540021917029800c850a4410403030302803407201c0d04650548880300801034002c480307000c6200b02c4c3c80c2e2400c00001141c0031041980114ac2c0d080c002884111590803e86a09000c00c06070200100440c003202503120451 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 914158776 1250 914157526 914157539
    0x271b010c0c0914090d0503040219050d031e030903020c061605030a1706010c0201081603020d0e1c1107030f0c030218070f0e030a060e07050925020c1315031b 69
    0x100090024890740c00405c0e00d00d0750307564020205c03600070b81c0448010f24504c80302c00d100c10161002c1e5000640c40044030024a040642206510004544003643daa42040d10340c8001e506849002d14003c0040e0018000d00e881d928105010707204a0713510050701c440c0c0403945e90702c071859a84540d020101003103078145030f204401401024964000b0083c41c0200c1940090340c006030010b070b0302400c0071918591001c2c0c4902100d10a5040d0745491001007010b1201171007401406441d001d100038541f9010500c0c1c0500c0e801039001e07003214810031150000419280d031540d21200801040c45004961420b00e062001015a5864030144809101050241c40d2420000b5020340bc5140c0103411406104c2d25920041d040d84d008070352a403045402c07003070200701d8051110300181420700940040d54042108428046c5505103100c89510070a00c40000c50902c0e05207440582e9520b21420480c6d92042c141c1002501c46c42d0140c010a04a855011202d05840e40306e65a800c0080180d5804079501c101000e002c1091 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 914160026 1250 914158776 914158811
    0xf190f0612150b180f0601111b180c030c031506040e0f060a03050c130f05010305030a0206070822030c0209010b0910030902090403050a0c08030c03271b010c0c09 71
    0xc0f08402c48044c1c00b000c031400314440154000406903901c0c50714800c000788040c4d004161192442a440042d07405040c5110401d4690180070840d00340564004009005107486800390203000b00e402c0f8004900f1680c40000d400b14580c40141284107070401819020019203a400240c000703402411503c00140c078001c840200345800007010907203d000543c0042012030303008104100070312025107640703101861000c14000500f00d40b040200c18a86404000424458084007030840d510150b401d648607904c0c3c10904907030191040c0c8840900b50b02c1c6102c490b410810301049900c11600c01e0134440500b041c9500000c4080509912240c0040c10003d2a44810702d03100e00c00c4000341d095410100f24060050300071640d5a000100024213200700021104003081c020120706040d80d0b881031140341d80f031400c8105200c0c075070019142514141164020007987c14401400c0120000311103005000ca49002488810f404000700e003902d0600c8103826039407001c504000c010b2009000071980103e0681e100c02030a415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 914161276 1250 914160026 914160041
    0x180a150b0319080a2a0506100e010e060111031614150402040207020402040b180406060801081f200705070f0e0408030405121b060f190f061215 63
    0x40303500854080c003608180b0b00040240b65800c141201d407120807001d010740f01000020310660030300001800d109008404007030341541052045042c1c0e0b0050700c0e9403c2c00181c0650a01641001810700e400512403800207404250b03002d201450610b41549000341250300310307070221040c4a10f5140340811101030180c0c0300c4540c0f2000f06444010414074034074200c145c00c6114041c000074401c540005030f4009640d00c68065a0160900da03207055540c29099000b806624000c4902a01850a2801c001602406440580e040b954010f01a080c46c55907001001100f142c1d82d941040d041d5500c0c0036000f2082c008540440022a600e00900d0381d500e814180b1b04c1c5041d90b2507101407540c0880580500c40c41a101113440d8009520a9986845c1d449a1420b81e040c08080340e41d060446a010486103040c58500011828442150013a40d0054a17a24000c1c1c508601c00c030383c03200b40e215540307010740303102c600e15402150030b0074110b0400503c0640b902c2c50900c1c0410208015140c001a902c11003c052907e4891040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 914162526 1250 914161276 914161279
    0x1b030b10020715050705101e0b030c0109181b20010507050a14090d080403020f03073008160308180a120512010b040f050301050c0909180a150b 63
    0x2c0340c030704a8038050a002c00060841040001320300d050801c082003105844000c1c903100140405080c860302584a51700341400c62140e00e0404103c0e21403030802181680c1060700607960704a65074106106146d0701040641d42a0601d83d40da800000c0046601d039580242e070040d03a0310201881401001b4214140d18044103170030302d9140c80103112940c1c1c0c018007100c0f118030f6141071800301d4104140004c000340c02012403a60300031010040c07510401a01100400a4a00c211511710000c02e0300e40a1594400c0b090148644648441408180e00280c5c2115030b01003404c07e1481804101059855945035001032804000589541221204143e00b01c0910b5521844605001c81ea0380b62800100e941c2d0010400c010300121111440382c42290b100e0700c110741c001900278440304110f580d0f40e040d00703400d41e0240c030990310310410800300810716141c1030240c03c0c00b560b070514669051034008020000d001030702031301c41c80c560700c80d1051460020405100003824240102c000014a40d825201c070000e403841000e049 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 914163776 1250 914162526 914162533
    0x30c04060f060e0607080a05071a130305180d0b0a05130807060207321002090906060a0201020408060f0402011808031e2b1503080703121b030b1002 65
    0x5014210628480da0110b80e214903080c07407090f8140011452501c81d40d18054007017000007407145800e5030400c0003045c013584950b280c00150030000000021400091b40c001514000c40094540442d00c980054500034403405a9131841c1041d041c001180c46484407412560b05050b002000b0403100b080c411642c0c401d910444005a14140386e489c00024031590900904066000c6110801c0c089403124100c00d1481841e0000991008400b881440c9001030b51f0408441c4640604808000000d0080c1c03451100064806100798aa20081143c290081d21702d150443d9824800052555000c00003a0b0040c01c00d1014000942480d0000401d48480c02e42800d401b00e101c90000c00407070800008441800301c5812008080e45030300382d41904980b06902000855900110031651441d20b0116001c0e40d0300c180311400c11947c64640c101d0000d00d41584405080c42c5010f020b120b010902410007030140c0000124001041038403001c0c1181ea0720145840d0100003036413041070b84140c2c10900c51008840c081130004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 914165026 1250 914163776 914163779
    0x3040603050a0b150415020109060e031b0c030a0201030216081b0d0201050708040803090705091e1302010e0d1b0b071a060a09152d15020c06070f0605070806030c0406 73
    0x1c2c0d01d043c1700d00d1040100000c110303006894100d1003035100c0e000705070b03115000340081d4015030702080d034030f4014010000490600001081c590440001d1041c0020f030050702a103912007903030300190001c2d081001013808a4a80d03030181c100181d00c1070018040e00000b824064651840c60307441500e0440b140f03144600307681c980003d020345903801c07d500547c816400f000032503481e0f03200c1180034200380980d800a6080401c2006000300200056403441551000e0b491307100b10340e625042012540d610002d0013a003c6007030131000003128240201d11007945401904200d035403901c00480d64011700080d0303109142c1c408010540c0c004000c1d65501e903590302041c142c2e02c0c0295040c40c500040b0014907910500107440d503a202e4017261798201003035080080c030708400e2240b90509204c582d00241004088036141d03450140f000840c10621501c1f050310101c241d5030046c80c3c050f60705010711401d0b5006501c1a5031081c00c185c0000c0000d005070145c64400e031070b940d6134222141003403002c4c1854414603d24407032080b03080050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 914166276 1250 914165026 914165059
    0xc070902070f0b0a2928060807020f07090f0b0102061902210f040c06230a030207140706080109020708190302070b04060501030c0603060b090114090303040603050a0b 73
    0xa034074a0749030300250700c51444d4540c3e5810740300400d6268480c1d2081d403a070709400e00900000c072100131225842034500200c28003c07031034018840942c0140c048106080c050080c49030b54416404180e2001c021300403290700b40100300c1003034900740043d442200245d03259162007950075042d0183d2403e120f000e00082c212400e0100c1c01008480a00d84500001680420745003610010203280020041c142418a0f9450910020160741d0950454055400801400c4002811031098a8480d041c0d00803518003034184101068065050303003c1140501095001d02c100c10200c0d1418003221b100114120050200c0740c50b001c8040d081e41d078168004a4241d20520000000c15a19011560300074520501324040790034441e01076000b8080d6000c00382c810b5901d40d00308010440d02d6404036060b41c3c081c80c100c10303207180d654a0840564110303001704181c0da001442000029406000b4a071405110044e045007800c0142003c280f440d00580d202d5000030b901d402c24050580100e01c104031a4050030b03102e42c01c000071001d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 914167526 1250 914166276 914166293
    0x19030201060f05031b03011b180b0a0f0302031b0a0201020a0801090e0c0d15090b0912130509090c04051626010e19020403081c1b2f030c07090207 64
    0x100340c1402010032540104241d4080d80a100b883e011141d10111210700e448c00200b084000c00b2541841108101300410014016010396464a41d26a40d45514050815003200650005401105640000d1078900c403540450f501900e52921580c1c001612068a048000d04042041e40200b11491a24200740400d040114900004140070365031244558510300c0e00540340c0400f9502e80c941c4601e8134005d8410444920425030103417035401e080b103540b050924600892449190402401c034403160308104074a082c00302035035901c09601d81c29945c1c2d80a881c0049001c1e10700c1124060940001031640e600e545030000401c035607108003503101c3c05040403000021005517406010340f820100c10903000800e182d400c00081805601c44400c159111076891404410540003900685d40c00c24000c02d05035103032206441400c4090941e14821003030019030420585603985c92103540c0384c04c607400d028020308004903046103844039260600110390303640740c622246081120030382042a002e401001020041003200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 914168776 1250 914167526 914167543
    0x609010308190522031203051e0910090305040801060f0e1b040906080706030b0402121503031611030c03030304030906030b0d02042301090b010210090804050319030201060f0503 78
    0x2c0720264001c40d019040e1028000c510449106074107203411900b400001a0400046074881c0c550310200380d210f0302040e0700b501d13011107050702040e6030031841218100c0c203400c60381d80004411066070503c03945845d10f001a160600e000b43c010070b100050402c160002441442c00801103d0162440c06041100d9201c50303000240260102c5140d40c2040e100400101c41110000c040000c0d082100f01c0d50740c0081610703100d20b813103240003003807600c0345101d601d0405008542d24503600d6034540c00a5900c3c2c22201120303110401d00c1d40e0b00b500c020b20030484c5500040580701c0c95903001d00340d615483c1d60030b00b0400d41b80c5480264020300a4109001703200011790030228400035a6164100450403614103000b1540a403503408000e07601508000310301c50003c0c11140d842c2c56041d150078402e0640c0e030700d840e100780c01d840c48240380a005902421400941201d04d43c000600300703214150340d91410b0740d164002890064114480d11a12000344030304820141c0912401000307041c440011454180740400180d251442d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 914170026 1250 914168776 914168797
    0x1e0f150503010614041a0603040605090106120807021002010b15030906071115060d021806040507110309090414010e030324010f12060305030c0d0e3a06060308120609010308 76
    0x1b6880040500940d60004d69001940a0121601d911b01810001302400080e02d40180035482d0000206120041d441d0000849410950007031411605030b0900c070003030042200d414210b560710b40b89203849a0b208502c1505106005e401c00b61241000c203400303400d041d00a8001400d000714002c802d0042c0d040803c0c0307803000c4009884a004140e94900224000c4040018000d60080c00e452078980044056114140502e00a940401c9036a541180550316800d507103002c083d01c0c1c0c0c4140f100c00c0362468000801039101e07103d00c200c010180d18030100711b0309403241c0702d8014002d40c1000c010015600d210050040f440300d00c0030f40c030150203501c1c1000030b00392454072246a020082d811f03601200784400f68208000841d80081147c1d91907a0724a8460b450341d400f800d440000829000c460251440c01840311440072445100080c0380c0324a140028030194500c05000d11000703801520003003c102107211310340040d40204e8003941d90721203009030081d400c1001480726215404090060000c14440030544035081e01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 914171276 1250 914170026 914170031
    0x90c030b0108090102130e18030a0f030518060c0a020c030a080a1d0a050d022709070b070c120c09050a05180d0f080c0706050c04080706021f1e0f15050301061404 71
    0x60303040d15585507800c00303445030b00148000212b690600758003401e4142404c1c00c1e541c080280d6196030706800440074205081582641c0a5404034081005c00d800601d014800d5004581074000d400300400d0a00000c080240c5e190b22010454440e0301f81c00000d000e021400480101c200d00c0d00740c1000402c8100341c1d02420b40110040070700c143c1103445480c28501c00444200d2402c0c0403030501100381c940703510b00722641c80050064000001d080740061080e10403e9502c022400d8081d4180000c824000c8000c500c00e9612140060340000c0c1d00c4d2852144070b026400f05200840c03d8544940501c0c0c510300c0c1005000c00b6580030040344908030b640440c03401034802292400104c5501d500d50700081d6401001c03c00b628452074003040c00024181a401072080365030001c10f80d48000d42d550410b0303032105007110015500024803940248001d110b50322460039144401e601821140d1403d440c0d800701c4e8100315040e4210b80d5079141001059107518104401030200b24028462681002c403106d0800c40861034542c00380741c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 914172526 1250 914171276 914171281
    0x3030906060b07050a0210030911040c18060203030106020d0f02030910031e06090e0f0a080f040f14040b04020f04060507020d0b091014070905060a0207090c030b0108090102130e 78
    0x5060700240002d000d0702510703584034a45410081d485a00144040348900703030007419408400d0103070040d0790003603030045022030407411407805100c0a001d400700444200547d265094208141c883d0008010304581da0003151a917040c041c010b4641103003030056070180242c11010001403030b40003044480c024010f6400d0056038542079000d8000d800d00200312149080003000b2540200709562202003121001c51040c001104034681060311081c0201450b403681d004100c200012030b550400501c0c00c41007500343d032403510756117250342180390585800c0081c01503141c030031550b020320740ec0c020b1b1901540210f504601d000750810300c054880c400c0313115030f4040c010302081c9441550b6030540c0314080583c0010b030741c41c0300c0e01d44100c0d250348400840380c105000f2460714000c81c94110754041500e00c40d261686030040c1260914081103840d0f0030500700c0b801184210f110114060380b040c000d9a82c03414450320085401d56448002402944000301444c0050784180500a50b140252048204842c3c1d05512280c0a8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 914173776 1250 914172526 914172533
    0x120b04080c1c170609011514090a0f0815070f0e060405040905010b15030603280501062903100909031b08130b070203120a030e06100f1a07030309 64
    0x151084000a600840c0340b0610540c00e900404024840002c81d50401050b55490382086103000d000e000300410250040c0c1034501f10fa02404108540000007105281462002c00000c2c012540340d030807078a10402000340800c00300700108451004101044801d00b81403801000003001c0140c00c0c5525401c019a51440c140680c80d481704540240c40f01820500440d00039040c81c5019200c00c1c80940d00868840440312112800e170000c0c1c0c0c1c01a10014054600341041544114041c0c036101030070064103030011a0103000604c00d20030140204900b05034000e11180c0881c44011000003000c1c0f00c41072180400400403070000c500914015164000000a228003090404581c0341003c41c002005d8042035030007420900a0500241c221583d0707a0007500f4a1980700c0e02ca03110f990141c0c80300290180d00000048000c0010003010341010440380c600003d1590560740c07580c6c90000103030760400b401140401e05100c0c29050000000c09005008444001454070906c0028540306040000e03040590702c0001c007040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 914175026 1250 914173776 914173783
    0xf0c190306021803060106020f10020703032a26010b0d1d01060f14011205090f0321090a08030123090a0b190612090c0b0c060907120b04080c 62
    0x91a002070046440d038101e40d1000000116602046209100d000d000048051001565500c46c2264001800000e100c1d100301c5c030065000900c1c120103060f1205111091142044003003401c0c40d6070915030300c0d0364804c140710280c0580584403202c2c040ca03a591100b403030038200c441c48680c11901c008500c2c1d991400c90005400092100c105211007003554099403029095054210000303070780b190042c07003040c20f0381c605142e07a000c01641e40c2c1501081e560001c0c0c4030748080da036110541c02080d0b441982e8080350800041e90441e40003901e01e07400d100e004100b02039602400c1e07168070350164142c4001c003031006540d16551440d010511a085408a81040c0303000d1500c07554000b541e00140181101d07881c1e081040c03402014121050800d0f0181e000c9500e10b400012102581c102203910549407030220506031401200038246d400c5050365900a0b03003d0014007045443d0003800b9071000000900058189120124180310143e840301d100c0513114000900031030040010380d60000d40c801103681c1d0b20344049844d04d09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 914176276 1250 914175026 914175029
    0xf0b120a0f0e0a03140715020a0e042c0102120412030902100f0f140409090c0335030c0306270c1305090c04030b041e0f140f0c19 57
    0x125a080158a4203031042c000395003040a84a0348070007407400341d0001c2c1c00029006160b00540b001881108414008030558000e0008507031500c2d0030540b82144a02103000d40300c2e000307011304420501d03a0b00b007521000d04070640c000c60040c100007503203403001760700200d21a85009400501030400c420320488680d07010358401e02e0010ba024003074038061213841754003620310740c04004150301140464490f441031601c11040b1000380c0001211190420f401c21080100805042c1000c50342080340c10720120200781c1c0c5070fa03040b50980341c041010b0307101e001201002e07200512040411080328003e10134004800300319404d0b20361145040c0d6021203503102e9081c0f15142040c0c011070b28243c01d005107050114103190003005007440280541c4616801d030f501c000340714201d0803c0f21070303581c035640511090000a60403440c2c690450b00848034255414401506c0c0f40503801d9100c0101d444180703440b0f40b00e0801c0450401e0b020101c2c5070340040e01c0080e8191803420388544030050024402e03060199210b0b0700080c9201c3c80c1c030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 914177526 1250 914176276 914176301
    0x702060f0d06090204050108060607030f0806011106240a270212070206091608030301050405070234060905220e030c0f07140303040e2208130f0b120a 66
    0x2c42c1c2d81e5610428802940540652400100c40200080072070a00804071440142d042c0d6803040ca10128034012140301601800c080e042001001e500040c82c0b5080080b2402a1145450900c168044452071000404040592401142c401504100000c100c3c2002e0242ca45040c0000c100d0220020042000707104030000a200e202c5240140000c0a600080c030302d01c0340e203020088032103c2d0391013190011182103a11580c0680d620400040c851400c0c542c0203550042e851b40116520044000115400030058010135200c04010040401c1c012040303444980c0102042e040512001d401e10000c12880061080e001246282e21080a0001501a0320803440c5015950a890311003e48054076502d40f105039054000078800e5007000b2410141d003070b002c042000c000030011884c1c01c0c0f50801817004400014035010241001030f02e1050280441305405103880e01c1101a56a030344071b00802214130f00c102e9008409c1c2048101c80500210002000f15082d900c40c507511640144e03104240c5c6005440e0045054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 914178776 1250 914177526 914177531
    0x70216030b06120c0a0b16050a031106070806010903080c1204060e0906120604020108090a050d0c0b090604151802060f03071115010e0c09040507020705240702060f0d 73
    0x100703100d400e080c0c0354050a8111031100003040d00c0d980b641c1c0e5036828028036541c042042d000411886801100900d0b40150400a800744100b0035150541861a40b00c41603001c81c808820344200c81001b070203200d500080904001c92030b410003000080840c4002d0100070407144002500301300c015001c0001075100c415540080c0e0b90390b40c82c2c5100900d03040c008405640500c2043c070104110340703045111800001d0110f0000e1807136039100d400444003940003a1402040e0300038002c0207801300b601440340303e0551046880b103150024581c6804002d8100040c2000015004213041c0400a82c00c043d290800503031403200030401c0e248031004a080309100c7e900095201743c0c005510000d26241d035000e18071034041519114100070003041443d866038840800140586181c40050002220301030002c0d3b00403e43c0b03405141069243e0340032600312502616414050f03401070f4006c000524000b80c1ba803c00c0600501d08504c960380c000c0d0103880c58054070034020b00c11000444c00018503d030900c1550300324034041c84103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 914180026 1250 914178776 914178779
    0x6080c03070c060c0905040c0804050d081308070317090f0a03081b04080c090c04290d0e010e0c030c030a1101050f1602090703060b030703091b030515010602120a0305070216 76
    0x3421708035042c800c0310b00840c140010b8007030706030180045038802c03504880a400580351442d02280d040000404441d01030384a10b06030320104a44d81c001d0b200c0d0130f110783c80e40e6600036401000507402c0d210081056845034000d2035501ca40b0310b03000ca42c009080394107080003559030f00c03a020b440c880d00d030410700c042d080308802040000da0341800081010355000706440307070005a2906035228625101d82d008424020402c000118101582c1034808140e26a540420500302400da0562000381e800c0710b050301045a44590070140c101800b0700509840040441c0200080528400440c1c0c0b10f0031502005021054020420680390b40950202c581511a07039a43d187e64000c1d0083d890000c030301144c0e090340501c1e030140018007090b000f0312034041920b401c011640d04581d50341e00c00720003600310004c0407110045205402d0500707410718200400514071a40c044e02810800071040300da80301b8140c0c403400865120407400c2c511406003c003150100501450041116520b49405070720f480c05507110203041d081403650 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 914181276 1250 914180026 914180051
    0x40804120b0109380a050904060b030d1b14070b271903081615022709070807090506030a0501180903020304060507060f021803100606080c03070c06 65
    0x1154143e50840c02d00704000304001030948010050007000009031071400070b0069180314807085000600d400203064000954030b45000ca03101400640d801c64042d80c65000c90342c501d01c0e05005030b0000340b1142c0741030344041100382503114001003100f8015000e50f10182c41110400070500c80c5001900c203101c0355075a5042100c01e00e241080c40050111461b0450005082c124607280314891202c1c40301c1e141c079001890464851101984c40010300074122441c43e0300e600001016580314506202601c400142c4600074142c442001c2e00b085040400602c0801003e0032032a904e00d01003a411000514146080d0360f075500301a40d40c0c1c096504103e90142c00881003242c07420050300100d06031008915440070f6210341c0201c3d00e003038624030b00300100960000d00040c4091445800a00040d6004030f00c04a20600e6443c400e0382283d0014000041c03c140c1d0b124a050241001c0103122642c08407000104034107481e0003001042200c0140060924180010115000c0f600c2500a545181e41000c41004010206e50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 914182526 1250 914181276 914181293
    0x2090a03030e030d020106050607140f07140102010f05061e030a0b040605060f03030901172e0303020d080103050a02060702010507020603070801080c030a21140a0503070905040203160804080412 85
    0x150740c030130300c0350210303048803648103008100489801410310b504050711030f580c1c81651081d049560a030340c400c05000c40a44482001302d04002d24440d13603076825800c400c0000900b07407182400f14400761410501071180a48400e00c600f04402d5480d00500240f01e052400241084e52040300a080080c501040c8428015141c0c4244d004502c00c5400d0b60844405009041d168000c0000c00713800304036080424075429180d4000e0f40d600c040c940d034410b2440c0c080503a805000020001800c0318198107040280100354040192034005c0f00c04d81402101585503070783e142c0c0d84604c4000000e001d000c011079400c0c00c690040d0280d48843c0e40c02081d079500c0e454083c000619041c000d02c2100b0031031240c130b08010400d04000c40e880750090b03002054980f40c20601c0c4141401d4400e900c1017007040065092036440d040300564081c21902203640d581c1c80d603900b00385000a18905494015510880c810802e02c40980d9481e5950b4119280c00d050807241655107040402040c043c69110342c1140d91248070040400c403049 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 914183776 1250 914182526 914182547
    0x1812030e12090418050a06050601091502030705010605030c030706050d06051c06110a050a0e060c0a05071514090409020a0b0d060303180608011a071505041401050c0f0d02090a0303 79
    0x1d89041000300d058044e4a81c0031550b210028045401540c003600202c0c40e25002154011010f0500540701039a40d03510510402c2c500c0c0800700180c20114508082141c20b014140017820200d0050003113510f1500041d0b1aa21503204140a126000480070800c805c56000100105402006099100702c104844080c890065004036095450200f275035032032000c07100c185d84030080301d0341d2401c2c200100b5481c2681d009400c1d0200c0341d8030081c24041c040c004841041940300842c0b191011b40b014914010701f10203071040c1c02e1145c03401c0c0004c1c105500c03030000340c80094850148003120003045c9082c0da070001c41e07180f50319070b004a0303005e8600082c89560009160090400c0382c0c42552611001181c1480004002c0703100d015090000700904010000200c05120361004201700d4181507141c4101940c1399460544011140440c01b070300c6404100500400c10302c1100541c40e030100070301440ca410700346c1c481c141c455942290f801d94400b0a08420701e050303540c140c41c040e14020741f0123184686c890501a1000c90170 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 914185026 1250 914183776 914183779
    0x1e070f0b07020a030503011224020403170405090406050a0f0c02070f140604030209071101022722020c03040801110d110a050405040203360f011812030e1209 69
    0x40902141c0c00d1440001c482c848641c15941da0f504590800c8040007a074181c240065488511480300048001d0304407182c0d142a007154200140ea844c42d51406400300c5c5480c030141010705106101c00c0015072210b074507455005502040015041d6110603500c4020004040f07503d807250700e02115601c0703a58000400e1004e81f5206884c101c0c642d40e50380c8002c0b0080304200403603504040203020810042c10800546034003c01e01c0e04040440f0041107803c203003260091000b2600c1061f042801e001505240b9480d00303501d0300e040d02c0c0d03861116040d07100491006220100f01080c00d50000d940e9524900500907607001e010014000e210b10352200c0e115003180d8021000395401030745022000310103a0000d10403198203c01e540c84103030400b4501400c01009400c0101440a143c0e4104403d400003507000a02e07450030101c020702104800c1030305030410301e0b003003040b550b42036140e15203994213407240502070180305000c0c3d000408211043c0c40407400c801500b0084203000152041d152802615070403a03003d440c60100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 914186276 1250 914185026 914185043
    0x204091e0510051f0513020f0c030403020109050418121803150b030102070b0703020315100518090112171210090b010c030e010c050f0609010212060405060105040b1e070f 75
    0xb9908601000c0241903010003141307407081c020801080c00c00d08400703001035224410045c140001c12540d0803155100d0010403070903400c001018400c41d80c00121420203480107071020490070b110307050f401c1c6450a40840c05010381110b41c1c08540030600c2801c2c0400000071214000e0005662031a145808050980c0201061820403040c6112800c05200340c0e1541c1e07812209008039519080816402940702408018081e40103540c88402900c03900015450f03c142680d4a03541e0b40c42080007107401d01c1d00301c1c280d03610694508004100940124059000f040e811115055500725118100c1c455072099281811390702e00068204a00d001c1580700d00303030481c0c298003028044249d13100011180f00d2001c0100134041001d4818052655205400e00c0c5400e500c240308071101000c031038504070b02c1c01000304c030000030f00c0e0340006900c56128030022000750881d509550030f100070b0602038000b8115001e030b4024110030960101d40c0f03402020489110b00010111201d6a9580304103034200324000c1c8200c3e4105070b0703130300d803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 914187526 1250 914186276 914186281
    0x31b060c0615170706270303200106060807030b0111121605010f050403120c050a0c05160803031815060603040516080a02181521010f05151005070204091e051005 71
    0x42c01e1040c17642406d5481d403078200002c0d003141c1d01a02e4034804c403a425070a0341194403032000c2c004d40920405010b048148c032900a18078001b0f0307008080d0b0388640784c0681080545190941011000141100f101d4100d003815629201c01c50720926400c2c048200141c240d60800140040400540c2e000501640c0299592445081c8070072400c3c00351103820081400040c8104400303039585100e08680759400c0c1c80745058030000e5030000c2d1800c00c000519044144141c10000a0000021118660304c62a01d0f10320041d00c90f013214081d0640c0c02620023003495002d10400000601041400d10000013a9401130544280d5180c0300d4001c1c541d242c83ca00000c03800b90380b40003404c03a0311801c1181010300c6074101d101413090320040d510510444100600f070411080f1850891a0003458081c040c001c403154040000040600d8441c0c074400e50102507405050240c0240ca412204880c3c0c80b40407101d500da0161004201c5915500c0c01240d00300c1428201d207504d100000c43c00080120210381d00d801a0320406003400540c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 914188776 1250 914187526 914187557
    0x909130303200a210f0609061a0304080307090312080a1d0a02010c210509040c051c0b0303040f03030201020c060a050601090603050903040504020310031b060c0615170706 75
    0x50001e5506521208010300c000f851443c82103803415003583d8504501122000101c02a40c1070741c501281c0800e42544a6500b4810700ba41807081c1002040d45e003c18046441c40001400d040744005040607100c0500000001d4007240120345007401164000c003030f04035083d0740400040c0103c00c00e039087c868007410f201e2154040d88112640c1d14050001501a100301e41559005450031020081c04035170f0308141c1071141404d060b1403078280c0704014240d03d07159607400360b03003042008450007800381c00b003480428071821004060150b050208090881000640c1101c8000003900d14003460b031040340c4440381c00001008060f419000341002c0b1000c2c030100c030b510b80c545560728010b450017107031210b00207000c5040801100e40300b038203c10340107069801968030305900d40c0045030990b0300449010400a20410781001004824400c9a4400c8641c013000c2d20107504001d4020700a4446c00e002070182610341010b616001c011445001c01081050b58401c0b02c45085000d80e5160744207482620081810b04001c00c0c0d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 914190026 1250 914188776 914188811
    0x42928030605150405010c030e091e010911090105160b0106050d050f280603120801030201020f031303120e1305090708060606090603070912060f0e0d090b030702030909130303 77
    0x43d88055a0908050a1100440c0c5500d003a040503020000802d0310718080341c40b61480c950090401d8144082c01505070b10307100b503421206900091403d45040844007100c0300410030f55030105001d2911035900c1c00010040800800c110001400c800c0e5400000030302e40e80c120008010400d05180b040c841596514a0107102d50412528649030850070710040001c85811030a00b084200400d0000035055102d441e00c0805e81d4210001c00042841e420040c001e543e010010003280900f950004c40c681003205001121030240f503c0010030003000b42c0e0148045c0e6014a841d0590004003a00100782226000c264001900d000d81d0a660b140c054224049059840460080c3c41100050f20749454002c0000c10f11040c0d03800182004100880301d80041600c00001100010b03042c0103510202d20513210f5060740e0102e40b51468450076550000380ca00b2107040d00080f0010480c0d4005a1845c1c0300e41d00e0540507415442000da15580c4108010100407035007800d08501c0340c94034080e80d0f0400640b443c20110121 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 914191276 1250 914190026 914190049
    0x50409020612092815020d02070b010e092a06370f020102070203030412140d02010f1401050f01080a0f020c1615120911090c0d050705042928030605 65
    0x5040300000405170f1018039030b0003e1080c0c0280d1000149005001e03111078661b04401e0f001701c0840180e132402c1c040c071900100204804900b100200403003100744158801d5201c4084080300b40191030200351658051510000f401d414001c221041481c19003440e1961648140e1040c00030205a0303c01c5108006403051007944d9495601400641c42c0905000030102038481100702110590700252100401c4003041c01101c00c25222600041032400d4950301c103006441e010034941c103c81c1082001045555a2130701d10034141002801d003066a521404101c0010780050410150802d00008a0003a0304cc40021000e030311600c0f00f4140c1c140d0ba505c074011040d20024136400c44c80000c0c1c074900e41c010490f000d940030324500ca101d081440e1400c030420000ca100700000302c034500d00d40a004988003070f51b0b8810340145d690240c042e1070505d03d894100307405442921203038040d02640742c038044403c0f420310000300111040031202226803c95500c8400c900c1c4505030460300841c001a060003000105428805029030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 914192526 1250 914191276 914191283
    0x90d1202124320030a05120a0b0d0f0f060c11060c03092e060e011809020121150909030f051e0906070b0906010f1a040504090206120928 60
    0x5a080c401c420212044402500f5203034060407494000360038510104014140c0d0006521015240e001f403804030a100c01d0000c3c08005501d051800744c007200d554900c0e03e111196400b044089000c1d0302400c106495031889000203007458544080018020b0304500040c08098011044401c6c540c0c17100800445c900054030900d1066005407034428808180c40d0076000309611510628190740503445044069842a03800008181c01000040c00040c203420b0141e00c8041038043e0512000340503600003003003c18032011100c1182c0805446e03241d55026500101e014102070003a003403d5076101c0f07594a004040c41d0f001200032501c4404032800450051054924118007446e650b80d03040c049607400103580d8021070103d0340c450410016400090540281d56010395000f40050000f98100301c1e61000400068000c04081e403c6503e50703001840c03031601180d0954030207a8000c43c0c410035500c04a41603000d12031031407130040c000c0004c00c03617040b81c001240d8034120a10889184030f1102c01d8122001e450680c140907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 914193776 1250 914192526 914192641
    0x1614010207080703300903030e09060d110f0915030d0c1703220303060302030601060e0d141c1205060913060b130603080c060f090d120212 61
    0x20000304961201c0b00c0b0030b0303140e8604003000540300a0741d04030100c4515044480071480d9806e05105066001e42c6400c642801568421a68140f10000403071120341c80f0070041c9200d40e09807084015480c0e031403d14241e00006055100141803404140d52206030a141e117a010b48100000884214496580550b10540040500e4000d40340500040b445910007480b1501c206140d0075841c11503400c0c0b10f81c500016001c0d03507001900c1806d510400d404c2c054180d00403c100101d004006286544001503003107140c6c7d20903810034080c10381c80b030b41c2802c2400311400300c0300c0000030705624946c2640240c2c030301010507030000301041140d40b00c004001c405441905c005c0000324030b4a00000000e60164002d0300781210080000c62002015034101003070300c0c00d0740c204840c44d0101140810407084200b2005410000800c0c0d607910610300303411140d942c0d24640359600100100320309403002c815910b504554031858030550396403043c5071a5001980700302c05001ca0f49007428004800b80c036244445001d01d0b001e03e2503107128 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 914195026 1250 914193776 914193779
    0x180606070602221202040510050f06090a09140a150311010503040c0b0a03090b182a0d0f051e0c2b051c02071805070c020316140102070807 61
    0x240030083d081451515969220182112125105501e01c180104004480002a44034074814401580c00242039506040543c101c1802255502034442003121016640703039440b640e100d4002554108198001040c1501d011230f0103040d01007201c492403181381c08100504c00a085a01c0309090361003240702c00340003021070704216042d0350300c10f400643c1c1203801186c650140036190464112564846485030340425602c00e10801004070750010070b42d0200002513031000307001c2031059041c0c84040d94440404c03410001c01040c601c41c203601004d004042001b521541d80b158062608042e0882c09000030340d041d21a0011010003061200d1341e015120210a01405010361070700c0c02e01103c9407000b1307098405070001d2508101000b100103500400203010304028110500c442c0c0350b1101580e04100c640086411031041400100b000c0c40340100c005840d418000790503136404c2d4086541c1d405c0060000e606004020b0041040e2248400f10019500e4040c000011503280c00c0042e41d60741c06510400180b03070041d420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 914196276 1250 914195026 914195033
    0x807020712060219121a0a03141606030609060b071502090f041104140a060923100806090c040302031b04110c1b040e1f020c0a0606030218060607 64
    0x10481e00c00da00c00d41c005803c00c40520b0743da00c030f10342c0e0b41e0300c6001c00954040084070204210340104800016038219074440107141c8800b0604240031404082c0c03030000b038512103c0c01d2100030003d890910140c102001d40072521010001c000d0055031240c00309040c00e160011981005650032500c6003507001e500602c4e21040c06c40c003039019400c460b072410350010341030104420948507070144586180ca403902455640d820f0003a048201d042500107a030284203c2c01062200f41d80140307841041c1d41d1000c0c08004400f400c1c0300c2d91001087c00224a0381c03c2100d4070760215201c6d802c80d82490291340700f100d6040c01940c80180d21101c9000d10322019605502680080900d0b800c012841024000040c00100e20364040c080410340d079900c02c0ea96411668000f01c25041d18103040505002c031083d00725001d01001b41000740380c50f40c6204101c400000c40740175846016414025604541150f4084403c0d02c00d000c51505160000380210301c07051f4010040302c4e0b2107840c0c241c0000b030143e1092130b0040c10241801e52075117 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 914197526 1250 914196276 914196299
    0xa0c0e340c020406090f0207021305040803040f02030703083010062604050601080f010b09060906030f070602210a0912030e0306040b010501020f15061201061a0c0d08070207 76
    0x340590700300780e4880002c605d11029000355520003140c840c02507659000b41c414801c10f20066010715450b180351206020008015004417a0030680208032061030362800e000003401c041455100400d8580c0009009161030f441503030120682000e41090500c1e203040101100002c80111203107080402d00b02c80078400759000780052510300042c44407900311040c05c514210f01041d4203a4040c0c80580c0030b440104485441082080704a540e041d00910680c1000c1c00841c4001c2e0015003035910a00c100c60002e919510100488119406403004441c10f456131410040d45410007445400f20305074000300300c0f0090780d5404c0304440d02045656a200010f03071601c42c20380f21502d89080114100a150b22000405590402c400d03801280103103c0c20000d9403500b00003a1030460380310040c0705290462007420710242c0a2241e80c0c2d5001e00d060301d0411000710702a20803401020f070340c0c0140c0300d041c0280291510342807012000c0c000d04a030602c2102d0482c0040c1e4401d50300240c0071200c4c540140e0002c04103200312030703200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 914198776 1250 914197526 914197547
    0x5010e01090210030c2a0c08010908030a0e010207020409060e0c0d020d060e0f010e0d0906080402031b0102100204030f03170f0c0f040b0d150504020c060c0304050a0c0e34 75
    0x3071824041424074980c5900c1b0301c26015480c92a6140c04020b20020302464080c00300040000030000c0140a00d1540e54230554000100125541c942d500041ca5841c8800c0d011a00f10980c0100108100c0429160250081a0901c510b6686104200c40001581400c1c08980041500203103010350444241c2c1c4c0b01009449486410042400307085801c1819480c00d000b0849182d4921000c0c2081c000907548c0100b9441070307070303028100f00550081407001507200450702900c010341307140242034160038420040c5c1c40d18030a2101c22150b1880040c0000500940580241480c0d07c43e595100409030940e00401c45002c09441ca0000352019201040c0002040c90040507a41c460647c6941025a6610740c44280c1c0c002441c0c1c40303170450f120f941c00180105008880c40242400b11021400c00c40d1420045985002c01085013400c0c07080013007c501401410480c12994a6000d01400c91403629415202140070041d560410300ca00810f42c00800c041080d17072000010601c10546070801c0d0592602201c2041c0071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 914200026 1250 914198776 914198801
    0x3160813080a1401110a1b0204022109150f130f0807050d2304090f15030507060206060405070c020d210c03260c070512070f05010e0109021003 63
    0xd040000031822000d00005040034040c0184102c80a0512071843c2518030720344a0b500300d408100300c0881c041d50411060312903421800c1b6048047d41c094800311300288204c100c901c8a071b25040b158000c00010514000e4850302501080d1000c0000a000c2120102d00960711145010940000140e10664044c0b44212047c0204143e03441d250407500e0342038455100072000d481a8020035029590749030860103252104809011484001c845d0300348404582c0074602441e2120742c0c0b509190032101e90703650400d00140c20701c4403652a401d562460410303920038642c820302d005030050320000f48081c0380134171036544100780540b200a00111a5400c000305885030310f00071074850300c00070101c50f03a0f940701080e1000344180c1a26800a80c4000f0705015104009030140d800450321201a0025608800d040d5503808c6817800500649416091500c40d0a0490319000d040007842c000c00d407101802a1f10085817078413401000200101c2c50001c850f03d09070f840000700a5004100c028900407164848d0b440000701511 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 914201276 1250 914200026 914200057
    0xa0b04120804030f03050315030703170f091806090c0301050f0d050a0c0e010645090507020a021201020910080907031403072d06020904091b090b03031608 68
    0xc59a41e013801c8480342282c180e0004001008121074040740e04404c000b40c8908400511610b0300c1d55485041d00d10300499040002d903c082003880a0b107458200342c1300c1150f0001c2511200254981064200b480111000c511800b4181d000c640721604220407281610005001116150203200a004030949203c0b01114507100e217560b520086050311f40c508028000100d400c1040e540b40020052116148281000110702d07050b55140c2588401d84d0402642c3e0540002480c01c91580b840895451700fa41e4481c04240341001c0810a0495005c41c20301c150501c00c503030400d00104030000b080c0c02c0340500c0c0f4100d0303003101c071120a80d100c1034000c140c010307881a00c80c003c880c030a544a98980345480c01d070001c500440d500114440c81004144141c492904000d0200482044005010440c2c00c0712005000703460b1aa00042c02072070382e180c0d500131041c0184c2003030101040d40f8031401050311030a114410f01080c01d03c0c2103d4803c1a01d804000c4424203c9480320324039004805450706e1241d0340c042c0032076601c0c0f0030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 914202526 1250 914201276 914201279
    0x10f120c0b070b100605130905090f060901060e0117030703030504150c02010902040b010f141317060603070e060a0e0a0e071203170717071709011a0a0b04120804 71
    0x160524010a0a00d1050b042c0c440f090600b08081101441181c1102042c800140a0425408403030400c0c0c1003141d0001001143d81d441d100002030400c40700714074541b654041d00c8100048142d05400c500110340d80c0100740344007a0b98440c080c00ea000380000f44040d031600304001c2c00700800e10a40010b03401600030b07490301c0d2502403602003500c2140c2450700d100d00543d448488200952501e1322034041284001c0c00c0c00d009080d40180c004184c4001a606410166004520102102c030b0403424040601001440c601012130703a80c2100b5074030300080b100d99200f48900c0d0804550010b5405d44030780201070261040c040c0e1814841074038480b1000600c2000c40580e219580040020701304003410040407401d0480b60303061007174100184260f20050015416000c26024041055407041280141c50301c940c04410490700d42c1d8000b11000d40b00411440c030300c0241c0401b440840501940010602d60704084602080716881042c010222800d22500d0680d60040c07104000c03c02d00003000c0c40c0590300c10000301b403070b1070b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 914203776 1250 914202526 914202539
    0x15040b090c0303041d060612071d0301020409060e0604060b19051606060e0f0402031b01030b100e24030a020a05040b04090510090212071b05060a0507020c0603010f120c 74
    0x44e00154070212001a101404403201c050010f642d035001141624818500885542003182d00384000c0d00782410898102612000010601119100514000c0085d56555035580d88100a80b07003601070003413440c07100d40c08103e451405110791401c94800c250f290381042c45650b5100b009804030149041031000030001d070383c1c0c1c0007500005988040d1042000040060902014291020f001081a402a4560030034040581c0e4001001550482c40c6a41c03400003030744460048003d410380c0101690042260300e03a60b1400b9410890015070600107840780b1004079625005000c1d41000023046850341070041000c035910000c160001c011444490904c0c91800c0c3e80c81c10002410760083c2e00c41e518440d520000d0003020810b500c2400018080e140007542013002c020102c500994002d04039809000c0140c0b4100810741e0003011107108517070040c00b6a1300700c1c5009040400544001c86055005018500202d03415140c140c0a0f64181c4c4d807000341d50102c0c9400c0c00303d400c0241d0100308054901003000000003130070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 914205026 1250 914203776 914203783
    0x101a030106230105040305150a020d090f0501050c090d1103030f03011212050901021f11120f0703050103030c030f121b020d0201061202130209040e1c0215040b090c03 73
    0x1440307890030b1140c9507440a07030040880e620316100c00703040120030881040401c4c00040c1008030b05001c4060b54030b9a4407002c6500000f807103071070054040f00342030100600c20b0148460000250500560003400716a840440089040c03248105841d880000c854106000c1004404d01c1e0103c040c0140884c1e16100805140307180340d8200346e004910000e80f0001107010400b4821445460700b4542c10060308105600300086e4079100c512541c810303007007024000c007880d10001e90002a490a2828841d564503202d00b111203640311302c02c4851507020b031845800301c1c0750070340300f0700c1342504880c1c00d07a0310341500341f0881d5012541d104c00d0b50300350781c20401c8501c120700d07411000d8403030390760003008408950176011204440a420320008902500a59150035400c00c00d002c084100d081c01e1030b5040b1040b0820f42c41040c0407200a028076034900c0e401c244fc0c00901522014000346c03029003c02d0f07a804407031071500740d540126919103141c040f0060080718440410005200c1041d1150090b540c141a50b200503010341c0424034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 914206276 1250 914205026 914205029
    0x506060c0604200d0b0f1515040303030b060c060f070306031205040e150901050f01022406031005060609010503071707030518010608070605131a091f02101a030106 72
    0x6208410465140803aa0841900850080d050b079913000c0010054607000e54184000301110020b00c020000a08548203000c400f204d0454018100000344410040f0082c543d0068001100400e00c1c2c0f039003004080c41c0810a031000c000213000240f15a50b140d06645000d1000a454401030540b600800700c0007400c0c4001080810b10355966581e11145841c0482d10040c20140880030100380c40510500c1503284c001c900d0f4196542513907061954804200100c0c60401340100c1460003260181d00340d000310250100d12401244108e044502001641a803d821a601a00c1043e484002080f072220207501501c050b651040081c2059a000c2c8141401480b508004807903410000e42c0d20400c01145000b40303050009100c0410000300f14090070425a42e030744038400e00405090000c04160035080800b5440f03400301501c00b400381502d034100320500b040d246800030169284155404036032281c00c9001c1291400c00321200e42c1c0103102c03150075071a204c4001d0101c000302d840314003400850000740c1e8a09004040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 914207526 1250 914206276 914206283
    0x609090209040f0309181a100c03051b030c16081b090a02070b13120c050a02060c160306020703020c2b030302190806040b0d0309060e0604051509010e01050408030a030506060c0604 79
    0x1348050205585200e031020281c601d92283d464848e550800d2540440d200007030a81c0343c1841c3c1c0d81c42e00030394181e14682d46280c040355100d110009405801600115003400c00013001d414001c1005d41311032640b07407200c40b808025600d40c4954480b204091034101509504149000e03001031610b451a119910b045030704543e00306031001d950341e4000030040010b1240270255400e2170310b49002181b0ba81e8060b100c0f5140c6a01034460352000c160030f000805d0510842c00740b903030800350041d40b9642c0c900e8000042c1d0004041903026000c3e480c10210345090584203400f442200400380900040203003c0d10307010a401d00001c1d41007507402d000150080c8640ba4800313404102c01c2d00c480d106441d1207820481034844030721890f40100030034501e080000340c0281f010320a0301c101d41007950800708108046445409154070613641b051940d845108045220b40091412131802e980d01e140302040f0310015502c9108602c00c1c008154010010704043c0c9200c2d5100b04d40086005100e9450041d94240040ca003203802d64054 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 914208633 1107 914207526 914207531
    0x121014150c1509070602121c0b0915030120190c05032b05040c05040b06091f0215071e0c02040507030209040609090209040f030918 58
    0x6281001d41200449400554140c80c440e400704056408241c1070280070740209010b032000c01c03841200300284040e9450010300b581c0c5940d07000082006182c01680e2030042098a03602d00d1403260041c441800a600251519030406086812003082c04440b040340b58256501c003040082a22202d1000b00c10381d10040107050380640310445603040050042c00005034083d071203500c07801071082c1501607221402d501e044054500c1c003151026100503200d100d10310400c200304d01d0545c1264010400c0580b0345070514412601103001c9a00081e440341c0e40d422042d5140304402d5040002e020907000c01c9114010324240340700d02800e9965424030b002062807141c90345000b818040c20070101c5165003e8010401c03441c22610090003500081205440b41d424107400060400c882d00500030291740062120840e5101d41d40c3e84245038240700801c0381800208403000403204040c00078089113104da401c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 914028776 914208633 := by
  have h0 := BRFrame.cov_init 914028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 914028776 ≤ n) (h2 : n < 914208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
