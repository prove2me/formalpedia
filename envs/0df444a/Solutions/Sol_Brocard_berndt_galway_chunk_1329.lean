-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1329
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:24:22.579579+00:00
-- url     : https://prove2.me/submissions/d39e9d21-4b4d-43ff-8a03-392330d11ddd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 238848920 ≤ n < 239028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 238850170 1250 238848920 238848989
    0x504330803090607080f04030f050c0a140616020306011d01090e0c102106030302010c110706110a020607061401060e09061003020c0f031c020408150405071509 70
    0x41d410000e0100030070078140c0c4400b10843c0e90303800401c40003c510001d01c3c080c00046000e90103112200f242da04005082a00d403100356032240941e00c0050209145945e11540c25090a1300c5194450250140700300c40c2c0f14440001a44c180705d0180001105c1c5020100c1841c013400d00c00740000d1a9988030b14034416200207034003103049904640606503580c20480c441400200e081c0c038000c44101906000f4880c030000300001082840e441d1b900c01d2003895024000d00224940c40d141800c0050005083d254403400039000e00010400302110200d071240080000302d603020380040a050b603c0304540381c86030003012078030031120100c48001c0000941c18007520b6000080b0401400045807941c6d203d003000b9046003999810b105155081c4104020300800b00203407c0c03000010300045070b80e09100355020241100c0b0300120924540100828814030030042049120810311a03250381c541d4889140203401c00c40c1c40e8114071840c80500d05a002e00341da114030548200c2d403800104100f800040a100c81c0490304d901c2d1f8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 238851420 1250 238850170 238850173
    0x9080c0a060e0c19054606020a0b01090c03020f0d0504021206070c03120f09030909060504060503030d0f02071b050a0603060b1b07180b1206060913030905043308 71
    0xc080089081040300124041007100340d44c051031450380d140780b048800d08003007030054034100d404450101b00300140320000340441b40000c0c4600f94840d5503844c40341e00140550200643c130b84003a4540c247c02501554030300c0b08107808054465810038050001400300300c03416032141400c2940c4201e400b2000c58007038042c1c2c6103a40d0318031510010741c4041c2d52740081c8009100c80c450340d40500300828601c500c21201d240e8442e40d200c00300d1618000e503440c02d5405580243c0e100e10b04d8988100800e99002044904c521740d0500301240c40e10342070210000038000c00e000a0b16842d1560801010b00d480d01e404041911411035100070f4640e210301c0110100d0325640260704002a0820010020540401e0007000078030290045031030181d01e5881c00707256192440c0600710145d07141c040351101031911440304581c8042000080c4040c1c940000041c61040340a000001484101201c2c04145803003025100e002e441d025006001c842c00b64402c0e01c51120964050b580c0900c82d002c0301e8644444518010400c60f01d4440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 238852670 1250 238851420 238851469
    0x9010c060203060a0f18240905041b18050a02250c0504020a050c0705030f07121b060c02041404031e051306030203070f0c0b070309080c0a060e0c 64
    0x159400c000754030190a25501042c0310380001286100740d0110300c051701100b05891030151000388a0b105440c0840f0381c0501524502e400450044200018601100ca1852000c01c00d40c890b1300300f1a503101d81c1d2503a041402c80304a0004601100d0022101c0c4070a030b01080e0401082d0307030701155001203025a9403180312203003d0303c02000c0c3c05486030018070510713402501e803603030405e0350b900016003240d010301140d42c00f1440100b000403072a07009201040007405c00f640a022010b9002c191a41c0f64107690140400c4501800b0304c50041c80860038042c01401000302d03010340c5090310f410340640524500c00c4224841d034202408201054207586d00180519450b4541e0690203604024800d400c8007000802c01c10070009000020440004901001c01440ca58900581c0c0e400e00c0200108010b03d159200c000340228100349600284c02c2911030740d032126880c94005000d40c0c103440c00701481c0c42580d50300006031090004071000d0125903406504059840b60448a0f030320100420302404100d0720f24a03040c41c0442a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 238853920 1250 238852670 238852673
    0x807030b0412051908010503010b0f1008090a06020c0a15020913020c0102070204020301030c031a010806130305070206190e0406050a14030106050312040806070e0f010c2d0605010b09010c 82
    0x4104035102840314180142002c040031040740c20300c80b0131345520300003414400040215080078030801075075000039200e00141d41c54602c08142a400718000000421242c0740008221513814024490020b40c0000306541c4c400c0c141d400c403a42c801420070103440260f010101c0303100010b0399100b2501506070242c5003140440d1000c90001c020340003002c100d5101c2d5020098040107a641e44015400b95125605000146056007003100d0707549022035a0210223030362280180f18011000540b070f6885820303c4c031001101800d514049500d409a064004c0d0045004520304000c5a458004004c502c103080c0d0b980116010303004104016500c0e80c0c80790507000310b964802030224802c00d1405140c00f14020700003141d225a02c102007441c0c0b10043c1740219410901103014464010705102c0141c02100c070b03280a41c83e280c3c1c80030025403142070040362141480380440000d4100500911451400300c0b400c0d0349005034901d074944107002054003800807504140341900220301010002c003661420341c8180d64103922800907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 238855170 1250 238853920 238853933
    0x31401120b15040612110312070f02060d05010801020c0129040b04091403190c0c170111030901020c070e010f0b030903040f0b09010f08041707110a080102090a0807030b04 75
    0x940121072601958102c400b99858a005440060a0003034501600310340c141000f804014030380c03001d540700750407059071050302c03100310001e07142520740108240c0c5d0541c440c2d02c0090068401c01903200c2d1401d041c20000a00764030103501910590641c88000d0040c820550281780316844070a0b231202c0d80d09806916840b01e414503900040d501d43e00500000345030145078440840800d5050f41743e0105500c0026101200d404101c1040da09032201d041c000b02c40d071500da075003005da8403183c000c0b00c850303102010045510120940140440c400c4501046075241020490903000c0e41c0030030000d100c42e118001001441c518440c0e010390483e000441440300180c240b0320781d8803030fa038030207086440341d4881480045801703050801484002c1c122044c01e00d41e03840c0107100162401c07403800f000e141401400c0e006c1002043c07400a1948a844840141a40c0c903081440c10083c0ca5003000c40c1c243d004080258049074050055004002d40c41c1c08840c0307143c8807680c42050382d651b0740107804003c0c001000600030a0000c0c2e030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 238856420 1250 238855170 238855193
    0x100302030616020709020706060602070b1c11070b01083004062019030e0f030d0f120e0307060e0706120b0d0206120118060302010519110d02010c03140112 68
    0x203041c0f05580b4016554292030007640c004030b000b179828079540c000c100216038042041c800282a5090907030f0400260719002c08488401c00151300d0ba2607100c00c2c14600328644102120340450f8000c400c00c58039612400744a90346c201c0ca98041403502000014450f90820900d091249400c00a6815103400c0c00d00e10304852102028140050050001c0309403000c1c09020300229203d00707405500600d1110079810014044d51f41268500d006985140c0c020364180ca0110380401d0301620340c20024032043c0c0604046806011408103004210320b4514010303030321680400140942c41c020b0906004180d00c41013051f4442e1950300c100390109400420b03a80c0103000c1a0460385440c440180032065504d511703004115281d100b42040c29860f254080140005400c8031039880800c1105413040182d80d066500107401071107108650a10505a101d15403c4c0ea80701b0380040d5454400e840581e500880d4200c0080e001e40041c0403400003180c00e180301c21030398240070950f150485500648680d915030094440170840799 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 238857670 1250 238856420 238856461
    0x1209010540050604150507260c090d050109060c02070e0f0703022502120304230d06021c1a0604050d0314130303030608070b041e05041505091003020306 67
    0x900486075900440c030300307101c8103201d01d005010341c91070384414120800880d04024091018000d014103071903c40c0000b100402c001845482e04038401d900d0328400c4c03442070700950092952201010b030f001410020190001071032180700f01c000344442c81d419107040c0e0b01c4a03504d02907440300b601c1c40f00c0040d001060642429403c10b015003801444c0190440120781c8402400c0c00c02826402103900c54000c40c01d00c442100c03075030310b519405181818140120040c0c000d4400361504181d00112003c02040d03903400d03030100c2d112039011804660b6000b08001803c54018142d4007200a24902030a10552942001d20200c0c5580c00512062900b41400f04120020b84ca1320070a40c10040c1040d0440f807403511060043c41c040c140c082c4220200c03455454028107030b030a65009030290390401001001910108000e903400e40e1041d030b01c1081182142d003100c20000bd0b080c0c0c0071700c2c0e1140c28015020541c001c0110104181c1d14160350030080e60781c0306075481004021314440250964400c4c1d0005100345103500c001c00310310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 238858920 1250 238857670 238857781
    0x40e03070512210c090a03060b09100305030426010e0c12010501060f110c12030c0d020c060703030e150106031a18150103060b04080609070e04031b02010905040212090105 75
    0x21080d800400c60921b03090b0812107040d591010428428980010aa030780620581000040242550b407103030345900440c49641c100b55007049082440a00c2800d965008040c1c200c000c0090002d01c03800255174007055010320307000d0401d030701c1d035031000d80d0041c02054161165510307202040c4805000c1101d0141c2c03189844c00c1c543c010070030b40c06203035504c0c81c03041001c1009200c011900c030021480030908003802c20242005550010100c09140d864031400d55030341e076825050000b401044081458240619855004811031100c0004030304680c0640c04103250b80b00c84101c5040403105102403014411252403034206074004600010b042c466a0900c03001459818580450703065a03800100300143c1154002d600f00f5008401001803011003041020000d1000310807014141c100381e10050422401740012050300e8000403035810969000701c1780c61005104c080e004640d560011450a00c0540040d2408880c0b5400d04001c14850810141c9414100da0122640c40c3c918042903140700320003503003281c140c025 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 238860170 1250 238858920 238858927
    0xd0c11060408060f01090509011404080912030f04081203060d0b060415300305030103030f140301120606050f0f0f040608010c020f0c0307060906030b0f040e03070512210c 75
    0x1800d00f8400c26004d4044030b010101254188a620300c141d030030040202c090307a0b141a40c19243d03d010042c50542094000000599600c0034001140508041c0c0c10540c1e06440001540020000c000c001001203841078801d544011040b80942e81c0b0510060ba01d8075800440940c044020807010600c043c0c10000082000403403444150341815031102c0d5520071180c010700c00311106a1902480003015a4441a201c0d0f0000a40180d07005406400180000303070030450800c40c0e0211841c0591440600714001360261902c039a034a000301c000c60704000b581211141e04200d4000b410782044184a202504010303c1e0044c00d1030858207001040e5074524007103034810340324500064511820300c038140a01c0403543c00781c1040d0040920346c0d4513080d40100d00d14020381c084401007041c103a00c94000c4081c1c0789a440c01080f421080c400050400d814000e050758494600002d01d1703610b240020040a0f100c1c0704405840003003240b0101d003251030080c070003103640c03d80f044908603c84405040215901c51130001c501d604 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 238861420 1250 238860170 238860179
    0x1030608060108031201140a030b070201060f030f0615050f13090b0f060a06080402090c070516080313060206130f0503070804180609090c090b030f060a02130501020d0c110604 77
    0x9004800ea011900d03c2e080017455040c03090b28840e0312070240900000c03100044090001160a0030801e2002810395600c0c2404109110302c02c3d0040c070010612028450740540d1282441000c90561341c40440d03d040c0307000d451442c1c130b024040c881012683c000380402c40c1d03136448405000c03c000d00040c0f100401a503a810b000002440400d41501a40d0b020100c000d561400d00c0610a021500750030040a000d094810440141d6402a01540c0030140f0400b0540710f0b6414605645091003130b404224084081c1c0c600402c5419000000c1e00100c5000140f5806c655558481684c403002d080c0c5000c1c4155040914000109500e0300c900150741d0b00c604200c0703240840341d440d5149140c000c1d400555110048400480c0175881c00d0203040e02508041004000c280c107582c3d100038980c500381c40f64099207070700c03600365103125175080c000b0380d43c58500c810030b40b42d0a2504000600003584440310b41280d400d22903001040c903502c0000d0428100000c4c0e2103046e510b80b40c0e46c9a0403140d204840945a025504000218 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 238862670 1250 238861420 238861423
    0x20706060816050603010b07021309021002010902191412070e0106020d0305100b120424021306050c030307050904090f06150608060310020306032514180a050601030608 74
    0xe00905004000c0d20750814024100c4400e0742030355209901c00e400074401440b10500000407560156411150200c80b1307151000c0c0b08009d0081e07804040e5001a2034010a0321081c0c041d004038401d28401c96004094490002c01c80300c00b202180251488031f0041c0515440340d01300205a541d03011341c5c00c07080310706943d1340f03c120750501142600401c0040e000f5441c1040503603014000d10380c00020541200d04650b04183e43c1c0101c07400341d11804e4100d9200c000c042010302040803046098140002040100c1c603045050f910041c0d03014403244a07942003541c10004145100318280c54044a03020003951943e111a24121a1600994103041c0e001340d44001401c0065014040d40000c1c030311984002c103021000310f0b02d001221005a10103001e0084240030000303542d40110b05841c940752622001070b01d988400011a10706005c00807083c6000640320010300c08001c11000c288211610000f0000d03510260070180054511102c0380b1b9042c41c0c2e03d9402107180001c460300300310f90000b0706140010f00c4560b55074149 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 238863920 1250 238862670 238862681
    0x10f14061201080a0302060108060c07031b050102180312032203020f0616030b0102011b03020f0913052a1602010c021504060f09030c0308030421020706030e160e0a020706 75
    0x43c5540c1c3c1c048081d6004141d0180581c1d80185000707009009180b8041300c842005124150300103003041130500800b010031a05001760302050380c0002c000c540328070202d0021400e040104540e10f00c02d00c0f60844017422280c020003100e22807c0a003054441301e01c119001ea2100e190048412402d5005140382c000011000700081c1d07115182c5980003408000c1c03161000f070f04860f420013042d411a414000351942145211801120018044c9401a80e0318030303000040c2d80c00d0244290440d400302c01e114207119014007a801c0036008190324412000c880896045d102c0c08144112a481b05101f0203001301103100d44041c0b202d004060044c1400084100f079540001c00c60413400040c0300d143da030089014482c0c00e03406000741c0c0c0031950604103e1112070079a01d500080107400d00c4000d000300b50010000302004050000615181001c00800352840c0398404065100c0c1058010b02c00024585095005034503000210740580f8203100c9002c49a0a08221110582c508001e0580d003c862702088604001011446103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 238865170 1250 238863920 238863929
    0x31803120302070228051306050301020d14010b0a080f0403110d08090712051c180807081204030210030911060a1d090405100507140d0b090906010f14061201 69
    0x603030f01c0515204020705180d03051800542d5000c0d0200e80c09a03030102d9061001604c608032007802c3c0c5c182c480d5100001502c15074014070f406500110714124a02110340100d6201a20000034804c03580c2c840d0360460540c0200180b001c001460340b40410050101c0d41156074203d4040c1c0342a0036100c1e1080d004a2408480c00c18035070004243c0303810003032410400d1069030f01500d210b5030440b11900c2c3c030342c40707941c3e0f940403e481c40400410422140c0c5646070042942940c0040c90110140001c0c0c1da9040322030726008036100c0e440e400d006080844207002054021102629801804c101c10310200e601300320001c140103d0112004050306c6070464103513071040050112100d0035550401c81161000b201c4042802c1c00802070f0069400000340000a24082081d0740d024440002c009000d03910490221031840c01a203100c000e0200c005082c55030040d16030841c0c0c07080300c0240e4820074503854034500030340d50b51400d11a506122446440520080b8140120062000c40040015080980e0b20401c210020f0080c0d22 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 238866420 1250 238865170 238865177
    0xb0a0e09060c1c0218210606030604150504030c0206040f090f0507080711101508161a0904060510020105071416030e060c010501080706090e06060703180312 69
    0x10030221800402140c2c1d03000851406040c14442c002c101c0940030350345002e40b040c078241c001c00d80e2010005004000394a40300c0041c106061a000409244041d02103008444c0c21401a400050101d042c00682d441c081d5502840c1e50203070560071041c030b50090101400450810030000b52110159580b400a0030103001d9109401c4400c0346031015820494400c04202507589007060100300e065034001015030303801040303030600105031000c0444450424030000e040203500e40c40c02a8a80060805070040300507101001c04450b400d101d40c18500e03040ca0103506c1250540782002160220f0031300d8040140a5410703001c0c0c000b140564507003001440f2141c2d810945070045c1c1d034600800c5503055004220409180903801d125141048001c00401000e10143d03014003030000c60785440e0b00325110702c012a240f004840e002044a941c65000e4144c0711304452240500107a200036012800b07001826915002d040c000744528600b898941d000d9070001d200085110000307001c1000080481d0760f030800311404009070740c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 238867670 1250 238866420 238866449
    0x40317191a041a1003060e01090e100e03070308013201030e0a050f160b0904020702120109030e0f030f0601210f050705010318080702121c09030212060c0a030c030b0a 73
    0x428066000b51403183c0344109810034104001221507c40c215041d10403001c00820203141d0269040c0c90694600650f6044e58540000c58811340e00200180802910994801006e41d076189500e20b812040344481c01c16607404085082d440525900c2c41245001040c180412485042c411442c02c084c0c4031030056540c3e40001c0c84000e0448800d00041d95a2074550020141080c106420203d86021705000d050049a002481c6d40030b5603101d03500d028403810414002e000043d507a14000345660141c001d15401140c0404010500d4074001c9904140003181c1030040000380c0c80c09032001c1035000070700c10703010421440c01c0c1414089403000b1040d00c00c5900440c0101074043c0b43c01c0004084174000121041044501d6090000107a400012110398035011510818a000e010004500700003135504a001d080c2281e05010000c1500559500c04881c0201c2d00ca41414180307140c12501e8050840b90307030381214410030100703e04900a0b400030001d800340f0f00e00014407519550110b00402840d4011550340e44001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 238868920 1250 238867670 238867721
    0x307030503100e07120506010201090b0103050a0213020901052d0406050a0801062313090501091406040608070b070f080a03091b03030e041d060f040317191a04 70
    0x2d00303810000c041c05030f0485500c0c42c00c20300040150344c4c2440c0c80e04100d07407503102140c0c0d907038801d402c5806499000302000ca12541d40780b4006595003011b0303000b2401003440701c0e2074030340c00e80c120301c2643c000b1641a1156842c1c40502000c03e416000460303690401c2880345088481d0381410000580b000c0c0015840709980c800805c60081c00c44041680410100410618024811421180401c41c61408035020315250a44843c0100c0883e5807904010841c501c3c150000502402d282c00035281d0085040381c041140c0c450340284010769185000e03a44071684280d1042044a00c0c840080c107802d4003800c0803102c0003810f980c40400985c801c10744c8000003a00d844104091018055002c0000d81c074070810740c08070301e141d0358009e00b101048003c00c0d0b114582e21004840c9800302c0006c107803051032103a0f05851b40340c0340540703d100c41d214060700d082d00021600348a42102c1608148603901400c0601e2140d10fa00b5200c014020103821308030000400c0302034440c01c211081d245c03406000440812014001c1140c51030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 238870170 1250 238868920 238868941
    0xf0f1201080a03021209012006060a0608010806040b130c1d010b0315100306030501181403030f01050d02010903020405040b25050f07050109330e1b01110307030503 72
    0x1078000120980100c40b200780044d4002030111004011040102e031a140040e0044c0c0b40102c00e0712550604148640f41c129444201050b80f0348280000c0713807414006c0351609000c45000c2c0b002d0050b0641d070f92200c00442d010a4658581940c0080154035498443c1030580e02d1082d4808140d001e0300383c1004014000d4074010002c01054090003c50700524210714201002c044448552041b241c00f40b0100070310005114070a0708024007035900304c07000f03011464112000c2c0500381300d5140150f81124241d6402400b041000c0105c9004080e511013081c07042e42030400b007240b62041c0c0c2100300d06200c041c01000006803128000c4274032450050140ca0000d160043c0811004c1016003c003030f8000408005803402260000203546500f01c0701d440c40d80d19020305207001030040034104406421000001b454070030190044c540b900da0325204030500c540000074040b10390255407260048140d07a411070188800c0034484c0f4600c465850318140b44c902c03811009582c00750b0942d40402400e0300000e00002c100b03c0503811 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 238871420 1250 238870170 238870207
    0x30804050310091203050405100e0c090105030304030807061107061103090607030203060d0b1e2401030216060515040c05180901050604060833010e01080f150301020f0f 74
    0x401c0010b1101031400d0740c4054401c1000004c0304107040e554004942070204c1009444c00070705040104004c01d210310952103960340c0d14002100c1c8110301c0c000c000300b220b080200070f540480760701454240c10300c0b1407555000080c0a001804c0707411020188844400b282542c00380da0803c041d004503182d505c4c10f00d000040c0c1491f00c020000820b00d401002800b4147e01ca824180d41110303000204076085031590a0001c8020f005a400c05202200c001c080c4034410000c11501c03110f034205030350740d404410721860040d4164001c2d006409a031248003180200450300c6908065030290084824040d09141d00c000501140c050348a1070b00041c3c00425101c039000c41c146c0c030203d41c800c82154210040c1d85080c00040702840385000d01c004100003e0f0100e00c890307046801c0c04c400b204449840042e0609008860554501c541a1050000303111012002d0554080c0302d40a00540545a4181051341d445001c0d8803000d2213210401d0701503500300458080700c2246d8004c1c0c05481c0008401c6c1750343d11812040501c001c5c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 238872670 1250 238871420 238871443
    0x1020f070b190908090628030e0f0a0b06150d090312110702030d21060b0901031b020c1905090a051b0309032a060a270201051b0a0206040308040503 65
    0x30f10b0458480d0208000f002650041c06085807010766a07084042a044454604084118440b00d00c544a051558041e00001ca4030707501070088903010408070000d6690b4904d0407402801001c1203e01203010313401c1680c140d454103c0c4a6030000d140c10045506002226111001a400640480800a0610124010b03130091300d04031000581400300c4ea0700000c0d01c500c2480130361001c0c8442c00031018402e00c01c503a074203011200e6503801040129a207080003812036101ca50803500007481d2122184030b2100c1e074081c11010300c5240d4002c001010461090114250300d00285079a21751703e10f03070001040e9807004410352248010103004180ca0521070341400c4c101e421803201803480320301402002a8050008244ea2032940390034098814014134143d41c4040304224002040c140c02070408118841940e900300b44007404425460901d0403540307003400750640c040c0390b40003800200c0800c40c10000d418074421164040380e0020030384602c1010f584c009101c40d4841ea00460740075001013002c10441c40d09000c0008840d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 238873920 1250 238872670 238872721
    0x602060a0c0212031308040e09060c180f01021e0a0218070c030806060f04060309050c0a1a0d020903030c1605090c030103060203131403090405160f080901020f070b 72
    0x7003045070000394071800034043c1442c29035400b000250800c03414110444e0801d803c52031321a035807070325241403480d089400c07200c2d0390352480b0710320100303214141420031551200268110800301e20705140c100050003004450540c1184190070040c1d01541140d46c1c3da28074482c100d4000c11300b87c5440e2050100f4040014250091160311104000e496038200025060090b894600700350107903100000030f8224090840c401007410130205010030910340641c00398407002e00510840d49045940ca040201d00d160034000c555901c440d079006083c980f1081009006450380c880e601508281818010a2441d00001507000b0664415035100c000f900d03c4d45a1540a0030b000c1e1006080d034a0031101081540c80107100003462141d000001a41c3c0d07000d01542c03030200a43c40084007520b0710008450f00d64981103142598852450003002c900040b1800a002503c5605a00c4020a44000801c16140300c04010455000d80d5001c000902496050381c0080c401144140d5030308806091901481031880c2c101503515040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 238875170 1250 238873920 238873931
    0x9150f0308030f0c0705151e0106020c040f0f05130c0801141501020307020a0f0f06020304030b0703050403021f1406060918062d090601171311090906010602060a 71
    0x31860440450343d01000c2d01502c07400701d072104205080c0c41c1c410f6030b1000d00140503400d40580c2882544900a0180400c1c002d00480d0300243c00d58031050f001e0a108050251b8000540d80009041c0b51300b00840c01e0b115454001400c03441c01003e0026100d0481d940c820302d80c40398485500b0099003801e5440030303106520082024407000320740b030b03550420007401081c88108521014511030381308004460392903074080d11000d0382c3d40e69090384aa034440c890140360095030b035024010441e5403000041e05d088941009207180745881d0b1050550051030042d02c250118001e0b1150158031121044a0b0b100c0070b090080000782c2e512485020810380c0304003921080c4215000c0000162695030041c5084444a40004904860315150000b8141d185900d62840646403281481030401004294000703451030207483d1009147d5590004603542c0310707040143c4840c1d1134504046006480c00d1491101c2c11b501c01c1103220500001d00000620403402140c5442d510ba00c80c0005000316941030180c41c0d0042e00154041c0075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 238876420 1250 238875170 238875173
    0x7020609070501080604060b0a0914150304140f030a0806031614120115030302030d0605100503040b0a0b090f0601090807060f1817030c011802091311030709150f03 72
    0xc40d0141840b070035040040ba180441c040340d07280d0303000d6030040c140034801607564600d00304007034080540b620075806d0601087e908404181032403044031302601c4403002054515510742c0e4400d1014075007c000b1181d24860350710100440d42c4108010420141c01d0b032604076451030300c0d00c03c062412000c054410000d101d4403400300f1203102000450504240200c0b581512610380703401080c01082806200820845094070000905802000130910301d00c0c2c40f4005d002554072007041c86007401c400703050140012410400103011600340c0c12030705c1e002981c40f40007107000c20b9910009150100b007503600d50100319400703050004660308658007030010000030003d0b0900b1031810801074142c2100c010f0030400e0003c2d110b118030840728141c42031405028000c070511403264002201c82d6403508500b408080545c43c5c1003180d80c00161a000c1d04c03054a900a01c01c41560361842e01403c410325000d28100e400703003072128000800c3d9605010765009070840d020001000d42d440401c010300e90007a5840000712180000c014070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 238877670 1250 238876420 238876423
    0x100b040b100336150b03061b0408012a020d1b0203120708040303020d110d11010b1f120504080403060c091509151b020405060a030c09050f07020609 65
    0x80070003009060008540c40809004600700d50700c2c0d1204102c24112441a44600400c103419590072806141e40800510040e440041118140002140d0540c40b143c006507111202070328424110010708403031130800d644c407000030727003950080c11000964100e403015111420802055002c1100058401820f00c800440f0020b4042661200d420007519565000c5100b0354030b0400012080508889860ba81c45c2c081d410b003404a03420500044006005803900e0304d0109102c0ea84064070b042c4424041e01d0515858002940c0d2525855040451035480749900b603020f83e65840400c14070807074100c11903480d107100754000f00b0703810010004a00703651030030040c0804a0000020341d0290b030f0748000001440d4034200810f94030108241e029000c544403d0480703402540e4402c0c502011208121550365502c0044082501c03680c12400020400b0005d80c00c1150252919400190308480c02400d03590310b44d81c503074039210039030b038056042a07000700d85070001c5c01048901071012582c091524805440c06083c4416031a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 238878920 1250 238877670 238877689
    0x207140d0804080d1118030706090b0306090a0e160e060303070b041506120c0e0f0108251724060607030305090c04020304030c0c0b0c1e011401030302100b040b 70
    0x160070000045520050030101754086800110800e0318191906a0510901c480041115040b40070340100400041d00e82c0c06203881c8400e480305100300605680c3c5900c1401040c4000800c0b4000e0303181c507241700c103e2440307003440300c400480e10702110420080c0c1001c015152120024100f54001c3c0d0041100001007210603e0780c42c5c01580c8410030300e1414079007016900140c40f03a40c0040890203e007440800c100552540c120301200c2d000340c10301c4aa030303894590008074950240b0920000da08140c0700c0111501d800c0c1d8142d05003070350044602d20500e8460a5051159020b0201820207511510603800c031700d40100300c1100303d00c0307114103130307017a81d29002001c10150300a10308000c09141e15503011628500c007c0c0401d901000025108640707900d490f0800816000880c5030070365101076007480203d10398083c00129588a54214010128a031345607000702c64450000100c50402d55807038010311500d014be04c100314025030083d40240100142031a154040b00c074400071481c4107918140d01e14501c1d464000c0079 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 238880170 1250 238878920 238878923
    0x309103f020f040522051b16020a15051305040b013f0203040b09011a0d050a050f0328090501050d0212070f021005040c0302060702010c0804090207140d0804 69
    0x268907015200000c40d081c3c000d94102c00d0b44100010091003110303480034581e040909003690240400d842d084c110070740c1c421120801c0c684842d410000c03440240b0300c92404a01d42803000d04401d0f03a182e0344442d40d0501650b42401000001ca002506185600a421755030020308070484042003a0040c81001806a185031f00c00501e45c0c507603c45c00070b900c1c0101c1c0383c3c5140d01d1304c50600e080e030f201c11450f64a58009600840b0308944c007510000c00b15620100501c10512070382c000175480c0c900341d100303081048048000d41340700b182c0358420f100d1081d001580c28428180c403030b10700200031500d409d01a05204480c43d40d00041401e81c8256088450301a5403207200c0e43d089070820b013403003552040c214128a002c0d00c2a88051002c180343d0800307000e000c0350f1000c01c042031056a6400e48880d03020030510507007961416100178120041043c014400f41c64100005c0c2402441418116400360850781e4800c0f05410561006030150b5011982c1410f02522061140ea10700344140a41041400c480f409003003d00b02070300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 238881420 1250 238880170 238880297
    0x608040507090207050d2a140a0503070615050603090a0803070306090903090302013203060402120f040b010506071a04032303060a050901050108070507020102030910 73
    0x4101031120920408014007040780003995108030314208103640c0c0303951007843d000103002d11880f50159005001d01c151341411050b02e080070900340f911245408003814000041e103000b590a52000260100011326209201e100040395050b0b04001030700200c5981d074400303806001d04104120507100041501c440c99540404285c0d2a074030b400b03900720300818071038001c081030602c1c06a404050503040080701040303c3c400d03683c1030030f25200e103000e500b4000030b06021400c66200304207030340101400c00b84c042c0d588402e0142c001410440b4516080d403028000b642c4041001154034180410304c400c143c40580502070603524103103420780c203a45d0321519070b07003103424110900514804070342018403400400c000c181f00c07520010002480c64281c8100c6078070548107148500f900e0080000c03641000a59941280c3c416100e0743c00d01d91342d000d41651144e01c5103030128110f00041003849426564103591003480940c9a5800f840500c5d6408031140030410800003180560049074840c03401e09080802a008603121503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 238882670 1250 238881420 238881437
    0x1e12040303020604031b02060705060a270807060902060f1c050c03060d0c03020405010f050f0406050102060705070f020a03080d050a151203030212090124050105040e1905150102010b04060f06 84
    0x565181c6c04600071030009622080c0001d2250070311900160b003a0240050304000c018401d58030100c03e0181800e90030500c814220080684003180c1c0140241c0740c91805200081030305c00711503000403a0313940700034402c2c102e1100c040f23007152115260402e0f41d859083e0329601005907090100303080794140401000a0310030601d00f404102040b000c00e0f07516000310390140c400d104650b1a1510040c92140c0c40c000c2d41d014100c400307205095890280102c908550060700030307041607146c4940c00c4030158002c0e40c0aa400310400c9100c2c40050321a43daa2600450003030f00c540ba11950707400704142c107941020b01510310040c18904907040c00c1162612200c11940441424800729425140950203409102e182121144840f003c0040b1040107420400d40201503130341e0000807021901c803510014180b0300403d40060000d00007840703034800d07014016401c00c146840035030242a4590203042a030b4002c9a031089049000041012035580901628025480c00c9806201c41c5041015800c41d055452003900c081100d0315 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 238883920 1250 238882670 238882697
    0x260a08160e030d0203030106020d051c0c1107030501050417090f041a0a030605011703071101080a021b01140907050906060a05120106020601030b0a05010e0406090809031e1204030302060403 83
    0x108040401c840380641a114030883c03803080039407603410074440e19015008002201400510820803245510b02c40e10505034100c2d95001402d0082c9070700031740441404003894038034019100c00c00001d4011403198001290602d010306c1d0507000c25103500c1d146030ba00141481804400d07030320507446686804081c0c43c0094145041d900c82d000c80c140c0c1c1d0b4001904031024010200c144449a08501c0c1a20022803a0700c0741800060401c0e9a0380c45100300c090f044100d2542090f4241d0312075426a900721680090141c00c203c200300c600b40100c85402c10481846c0e40d1186000d03288644a41150352190500000e4842d25250801107110440018051703845480000340c1d4620403405181902c0103114694400940c0307603140c45e4080e5440d0801c0c00192001080000000c074040300c0741c06414142e8007a0a000345103030311240c0c0c07000044c1001b800c2c1180d0103207003444208440d480404c410362900401107529038004052807405400c0078403000d14149038000412083c8003085d00092000d410541c1840d2201e084600c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 238885170 1250 238883920 238883927
    0x509090907170102070c0b120403030513061b080703020a050f1b1e060a02070f021207033f020a020904060b030601060c02100809060c0703110a260a0816 67
    0x300c1e00300c111006502c12078940380190540c050102d8078412030318200500d4503542240450b0065a807940070704521400040e001900c2030300099000701c10407005850104003503640f40c05031031103401c50000300010a03656460060348000303605d400c4450750404502d0003012180051680c820f2022000d058900000c2c0005001000c4112085508032102a1448442e280b2070250500589003800740d090701c1160003180c1e49440b54821228440d5206200b0401c0d803403540e0078480841465500c1003c14082d10300000041543c0d442d01c8668000801e21a000d401c0200383d40003002204403004003a40007405c222444000e40015a0810302ca030100c44900bd10fa03602c1c68548081d148004246816014001c0002010b5070003010026090307100304c5442906d001c1e1181c0c22503211800702c40b00c071020340c4041f0100d80d00503c2c42c002000030074020f15108841304a818040361030502624811240448140004400401c0c0111032102145031400d0603032030080c600ba001000d428024041c40e040ea080e8100310400700d0302 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 238886420 1250 238885170 238885183
    0x29040b0709054b10030b060304030f0e030607020610170c060304020604120b0a0e0102031005060f042607061b030e0a080105040c1a070512070c031703090c0a0605090909 74
    0x98082c0d2101401c6500c0c020390b040910f22020081c0545503031a1400c68860103406285542d420180c05c5a003140d4a5840c00c49982c407034643c5d024288031403a10811a56102840707118032962407900100300c913041092400400003403590080518004110a00302449400701d208075040f0070494071982c03a92518000117400c1e1107294441420010000d440c0b00420500d410f40c1c622841c039002c0100600341c03d014155082c1d210403220928492107011042c4a1841e100d4041c000b07c000c4041c4560504d600c407104107600e0f030003039961445408ae0140700782000030000c02c00d0b000980300d50701d0070601408600403828403014140c04000c0c14400ea942504900e0380740e603c0c90100415103100203001608050a100c038580341c0c00c3c000d1408040050950314580f080c10000c94120f0b45e8004000e0001c00030740501c15100740c01001086841015220001010801c00701981c030704143c0140105680e81828030305546058a5804018010b00f00712408224103074100c8103880a0440035520206591345154400b030520b407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 238887670 1250 238886420 238886509
    0x5041109030a1103071202090703150515040e1e0f060d06050c07110103020301060e01080406090c0602060f0106091d09011103010f081b061629040b070905 68
    0x100b24a207100500010128099a060f8190296817040d81c030b650000140c8041002c019401c6850640410304140c0729a1020440c5e0a07402000d00206845100003040c0144003201c02007803450205091000d06034190041c0d4001080145d080c070f12413000740c1c4000c240080201b00740c40c1c4000480002e026622528a10015507901c4802080a031a00c0e6001c00310b65004a9015142d030700702d079640e4404650091080324140d600c0780c0c0b981c899a00c441c00044554420040049031410b40b04d5900c3d20010b6590404c2c44003820305500544440c0ca00513045210703101050b8007140c00c203d50030900700030700d41a00f000c1720308103003282c0c030654007680c0c80122060141c0700b400c01040051400200005042c6221080c10050320ba041d42078034000c0860200500d411f000080d45170360303c5207003004900e00b01c9400400002016101d6030580c0701c104000c1c441c030081c44060804c1d01c0c21140d9020100810025007055150307101e2002c0c10183d40c2c8030b003880c000c115a91003c29a840c0c619100440030701c01851854070a080700c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 238888920 1250 238887670 238887673
    0x702181006121e06060221091011030310052805090703020702120c130203160c140601060c0b01090e0a080a0c0c0906141002031603091d010806150a0504110903 70
    0x1030a00c041080060209105d03560041c0078049000150341c0460358a00320b10f4118640490a0016040411003480c04180b00d580c18012011b9558140e0802400074510a842441c000b20509282005214040d10201000c0f14000c1040340c62600700c803858000c0304107942d0196003010031907032038800660007031103408000382d030001c00110701021801c400680e410029000344c1d140000080081e00003020f901084c0d1750700248004071004110701c148500006040d65006451449038088c0504000381008002e17001580017070a612842000d1003100e00002e80100b0300e940b41002101031100e61161900200607005284000000c0c00031000c6100c1d4400401141e0044880d4007250303950384014000740410710408001d503181603800609071910b080c542e07200a41030f4000d036150055107124121801c8041d03204406000b803130311001c20b00e550392900340c4c9074031800a40120b1113541031001c10b43c44c1600042a01801c040a480f180d560740e1224041c3c2c0c022150b09072001f00700f11081c80c0c80e9408a000322029035405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 238890170 1250 238888920 238888961
    0xf1b060b010c02030609010f0c090303020a08030703140f09070b03070206070e040b040c0e03010f090f0b07050f030702011e0c05040e091e0a06050705040e04030f020c15070218100612 80
    0x8000040d0b00030100312a01c0300c010001504824401cae544860a071101030090303000303005950040b456000003180c0c00381c0d440c940002c40e524055081312a5200c1a103071140403024800c10000e40c0c0700208111009890030502d5241145080c19000355a080300034030010801c40d003026907182d50b4841d80c00c2030641d500002d1043c0152407440200828034146820000d10a60900d402900380d04c449100303420344540c0124011003005c41586804001032750181c0300801b042801c00540c0130005490000c2d5004920a40c00800e801100b00450704d210700f0701030403413080285041d644000b080c0e0400b04031003c80c2c1c13525560002d20b03a02c0751481800e00f50b4920140900d003031421014030b00c004001c074410702c50a10542003008592980d031000c4401e40658041d642c0202101004100030034011a0000081a207a104540300599610042580c3c01d003840d8060030030380303c041000e40451904180c134048540c3e840e4114526443c020302d07040000c80480c0701c0e410a110721280040c43c0f00c2d0098000103982014a00348010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 238891420 1250 238890170 238890181
    0x70b0702060c040f0b0c010e060108030702281214062e06080a0e01020c070b190c05100e0c120102041805040804051c0b090601030605090a0506070f050c120306010f1b060b010c020306 80
    0xcc0741d82c0011400c0b031090194010b18017042c1940f0440d80c01400e00c55501c407003003078141a400e03241c026410406071220651410000311104041002c0b9104480b00b00c18542d1a07841d01c003641046511040e540a94005040801e101c1c55038440c2d1000ea21a01152020480c040c00b002041d0082c40f5020003a0002c0c003501c0400b180140410005287c521403100403a0741041070790804a8841c91a210003c1003a0810031064820074a55001642d444000c1c0e170688410f400260000307629000c4c4d1082041d283d0f500410301f0440320303240e141291200f1003c08824002490240e4855483c0e00c03407805050300c5483e81a0a00151106ca085040b030810340c00904034885040001d01181d80e038500b44412201141400009440e9031804203234181210f600c14000c1a40d621440c40a5503c900b090826504101c418803103042400b0f8104101d4040d2042e8607001340d600d0038040001051500702040400622489441580070118580e541c204801e401440024a40345e400c070040f902421700c0d140103949403240300d09100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 238892670 1250 238891420 238891423
    0x4150e1f05042d1e09090212010f0c02191a10120305041e0e0f180102070c05150f04290a120c081605180402070b0702060c040f0b0c010e060108 63
    0x1010220300d803215103c29961348460110800905000c0c00c01d81410399010000da2642d60080700c1100e100500c401403046010290b2400c40d100590181c40040d02e407070141040c01d4051005480110004094650601050703c0c0d10302074400380c521070981207040d040090031003800c0c0f015080161811070b981e031400c10341c1f50400501d07613013040c0500030148030241e00c2541051041d16942080380d01d2440e68030a13951311081419415400282000700f20b1045640c9442081000e10041208601c22a000040c050911084c003121541180d0b144c02301c01003c10244070b45141c094256011913000074184c101040c50f00f6402c0b40800c10045c803210f00d8010100e903051529402040420a03031010303050030445c0151014080b21070300d209544a528401101c107070100d4061244c4d0080890015a40030013100741e0203040840d040b64000d030802d40d800d40301001404011541804900e400c0358018100c1c40c00d00f803c040308048652003034410110b00590010303801000003001c1d000308604602c0c1100352100d030b41e90742105a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 238893920 1250 238892670 238892729
    0x80313060504030f09150c0f02040e01060b070b0105090405120a0c080301170105090c210109170a11030a0504050f0d0b010e16022b09090504050304150e1f0504 70
    0x41d008160081004144090480142c10a00100383d47c0d150742c1c40310644842c020600544802d9800c10f844544003800e0702401d014420041141449059685581d810000c85412043c0c10041c42251100705002c0801c0740007c40903c1407801c0c3e601c00766035040c07508003a00d40b03407100b50340148110f1001c400000c0d00302910507014564001200280030f150b4038141000e4403207581211150b849250b07030604443c80b070f50442e010440b00d00d10f8000022200c0d000d40307518038209100440c409001c180020b0001c1641c0d407050540416a100c0c000030345c00d1000b1608058441e000314011140103003a1400300030aa0380d01d88403801c10003078201c520130806584520400c4012030f4201c2d1000d103c58900e8842c035500b98030010b02c1c1480c4403041c201d2580c0e50504800c6c2103800c0e100c2241044d04020000b200810300070200e20074213000717611403401555560703d040206007102c80c0d0611a1824008201c0d00700c1d12980343c15400e48000b01008282c1c0070b1059503840f080e11240201d030008170041680e030700e01d8015404500c010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 238895170 1250 238893920 238893947
    0x92f0703090504150603020c070b0c07060908190204021e0d0b0406050d030c14010b0a09090c06030219030c110d20010204150c0501020f030c07020406050a0b0708031306050403 77
    0x1d6046a546aa0900c0152056421034014103400c0e0113007080000c5c403960140030109040c90641700f000e6544e22490281d03412005202c000b035080036034100111500f0464290050000e040940070750fa1446604c0d0800a8040c80013038051034002a1100d1214004040b03607496100390290281c54151002003840280071074091130b4041c03440d0000c041428508903104840c510351560307a586a40c8002c0d520949010209103d0050302d64035a101c8042a68503104038001408407000001806041750404114150780d90b8002003d051040040b5000c0320455010580c0340c1a15040100e00d1034000702c011a2420510b2144004c80e001e40329800488950141d0300c00401c00a5400415007074100b80d56403801c07031141e4030540e500030685000d0013048034003925010140c03501802c001800c100500105d103140307a0040385d0181071400002016000c500d0b092041c0b101030030080d81c01400032800c101e00d0790428420000003a1121002100003907440096800d07110881e03502c0b51044c4100e040518014002945c070042c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 238896420 1250 238895170 238895177
    0x9110712170703020309101d030403080d0c0c02150a0c0b130b0c090102190c08010504030905040e0c03030301090f0f020c010c0f18030314131824092f0703 68
    0x204584070f200e402586c2c01494440c000d480c0151050701e16400804031407620100e150003502d0842c010300300034400b4100940c082c03454180c0d81c585420032601142c2403110305100303204d5400c240300b01584415805410815950410960355004d043d020713600469500001010030002d0010060071031101d0400c90030741e611484c410001a100d4000c0b10809001d1802610f00580c040b00e0540854815419030070080350203070303401e21450340d15034025509490741114180c001c914115002c02480c189841110000240f11004d8008041c802d0000380d241d10042c4610b507150345d204e8040c0c030700d401020707800142e01c884854403c42d92418600907090181c00503400010229140f10310030403c40340607200c03001c0d200d81d9440940000c1130540d90190b5001320951040c41c40e100c001e0003103c102d1032800700e2500260451060102c1014402c0881405541400d81100c155990040e401d2542040361528107090b00c210303042c0411456407240f8640060342209005600011403442c040700840011002091300902030b07076 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 238897670 1250 238896420 238896467
    0x51501230402090d0605061206090d080708040201090b1b0709150506040f0905040f150608250b0a14070809041a060304060b04020c01060303050d2409110712 69
    0x108000890040d0203007150481344404803907001811540c803481c1c5c4208010003401500b090b00f000700c1d207050801c41320003070390b503008440c400022a00701c81000e41c054824034100790076107050380c00200070340d615114400001d0000324502810300c0100428004298080d0100c0f041c550f07803440e55901420503904075407105011244081001c0c1080021101610840100f0f201413516240048005090081003610304640782c504460004501400e12113101d42da146d00450320310b062030314941c28210503c43d0741e8000c07038103d0f01d42e01c0d1504cc034010f40000c40b40c0c2c8640040c0c881146010a490600342d241d81d5068a510018142c401c0129240180513034036001c0e1020000c0704500034040e1548001c071000198440014000070b000504142c02070780c0c0c2c0540141000d810036186070005030a40d00680c1007180032520102e01a04850303d240300d509030901c90800c00c00e03019420261100b091042c180650018152a404010181c8462808551000e944040701c1009841c08a46c010139880c0e0144000c240188a503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 238898920 1250 238897670 238897739
    0x301061e1d10060c050c060f1e0307021e0f0604150501080705011202070f0203030f0720090708040302030f0a0507060c09030305090d0507181b090b16051501 69
    0x41140c0e446005601001c50b402400c0c00c9095510701e0048000721111700c21035251900a80743d0402038801c170001401c1c03050720303811000c2400340e081020469654000d071040c000c02c0603041c2d0018604083c80801500c500c1140611141c6608000708c40b400422948111300c2800204072161010382080b00d418001003140e41d0b02d481e603407500c40009126050025010182855542c0340c15030051045030710440b82c500000e002e6501180c1035402417100c2d180311f1140480c86c00180442100402802e203d20b883d0464840c0c411000650404405002001044a0700b800a0b0405000b0000c035201c24000002c0643c5030600c0b80001030041e0301100381201c0290400c04044a070070b000381c100b001a65815100e441c10884014240412002c80100c1aa014810240001a41d41c02800000080c000039500480c2c0580c0f00c182c410001c3c2c40100034001000651102080b0030b88094003510641c180c020780241d031060003410800d01d0700e4130914035411100f41c2e0200000b860000342d2030903055948401c03412042c44180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 238900170 1250 238898920 238898969
    0x703050903160b030c0318010606020d020114090d0c032109031412012d09060e13030503041211010e10110c1c051201060c0b0a0b01050a0e0301061e 65
    0x340f03d18a0040000c0c80440c446821040c0510b61000c10404001818440032400500b91907c5601420250700400600009560f080c0a010320107180f00e401e8441c01e0400780200c40c1c1c0c580308040810308100980b03085608162144840810a04480e100e00d0000320004e81c40d90700074103041c8070403408114007000060800d01c1c00c0c0e00b590b9152100304003c1c0c0140c3c0c60901c0b2031080306000754404400b050743c08061081040030101e801c020b400040f00c005204d03410701021074020b03080600000c2c5da135159408401c000036888400c0300c2d8003507403140184c444813000800c140c61807940344e440f01c800d41d4200440d082984000150300340744c900168409001d500c910001c5403466104807020b550f120b8002004e02103000560072204405401e6518009140186580290705a0342c42a00068001010000ca55040c400a4405039821941c0300e00c0800148031041d00181140c8143c5500b8428800d5548c0c0300c100c25942035102000410b154828110b800c00706610054038404603001c1c50f112085070042d0031070b800d4403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 238901420 1250 238900170 238900213
    0x909190c0e1003052d0f090a0206070602090d060603050c031b03070506070f3018170709020406121413080705010b1e040c0c0c15030b060703050903 65
    0xc01070607455142030750000c12000740074000e224880503032109090003000480c0b03200d50004000000c1c18561740d410105503080e08000040d084580681c0652020800350369080c0440c2d150300d1f44210300603510700312280031070012891070b03801070951454000000b040c00004646482c101f00c08400f0b80b5240e03002c40d924100c100b1080310703000303800d85d100500510160610701c00034130400303000340340c4d00d40700f8001680d070303283c88a1038421550710102c500101303040c684450049407080c401c4141041e862040020100910f002054410001420048494107025940074492034000c1c00c60342e0300a6548989034003020b0404000e00e11803900305071600200306400401070300c41c00e0051030039034125054901c6a840b0180340750810344041d10300b035581d0f0901840e255211417000380c41402d810003280042c05000200030858580390100414031810101d00c82c002010a40287e054400c0280703c3c995050381c1520407030040010102da641c12420014248007415086400751580040850403154600007100840741d1001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 238902670 1250 238901420 238901447
    0x4090c031514010c0f1b15020c091305060a051803070c1401021e1e060f180309040f050a05010803040308032202062109030708070809060909190c 64
    0x28076400c103010000c00c858030000c401c1c41c145409090313402c1a0302d03040ca1100303450f0342c12a09001459116600c862003604188014030000340705814603105940c002c0d4540b51880300b050307c1800114001054882c542e0048003445410004031041445c10317464240092200760307407004c15030301c10f242142400c94000044a004603401039114200c0c5150810311440030f40d0202255042d0b00840034100c440e03404001d81c220000b48c54000820020105601180d800c840041c0341c081d9507000f40341080200324040015a800445100803d86004070b091215821401007081c0241d00a0406c280c3d40d030900703034a400807070088038512420006641d0710b46809550344510310000346000010b01c002030095075200405542c107001c0b040390404280c0940d00113080c41d8062601900b0855400510b50841d004010006038003a83c400c000714607061950302c80d00014010200c0081c0020750000302840d55444070310540e1100200078080c02d0590400c0902c0f0800c4d41409030000720f4051400b42c50300202d9105c1c0b1105074105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 238903920 1250 238902670 238902701
    0x14010b0f01140702040b10020a060b01080402031f060b120115020c010c0f02040605060304050d091a0d0e030405150a020d020a0201090905071119030806030c09220807030504090c03 79
    0x1282810b069540350304454000e07a0300595640c2220544d0301e92040318185164103174050a8090704070302d0540101c52450a103103040011507030130040181c40025203101e16064000440302d20103118042100030344800d8100080b44203007c9a070100d10040c42810506941c480c815aa8000c009010202d85c0c034114083c4560000306500c08500210310403240722040c0c18005000480d0300d98032a40484c2e459842502d0446e12544991a844002503100341414040d010701041c4251020060444000c2c500814440099455488400143c5c01d4070400446d001088003800308079003004c404881142c660817480e101c801601516120b580e1961000c514035003000d078140c4801e0441c03030904401c90000c0070018600b00c1480016986006400010004130720142018014141d10440c94a001452060003a01da00d001782e0108483d00860341e5004401684090005407400d288020100e041030f800e00c4142015055440000f07802040c1503205d0b00410584402c1241441251312005c01141100c000c1c040301c0405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 238905170 1250 238903920 238903937
    0xc1701050d05060105010c0302150c07030e04140106031802120c150903030d0c1107230a0b0f0c16090204140108040203070302011d06180901150c0b040c090914010b0f01 74
    0x50747c000c3c80403000c402d02900c1240c4200314001d0b039100c9001d109984c0022454004510501003540c0600d0003074012005032000e0005014041151001c0c0e41c040c001c80d020700d500c031038170200f100102c200c086c8031300740d0018003900070b4401c0c034182c4641b94440d225403940980050407200490407400307000c5900c10200a0b000b14a4000e054444100500f10a5038100803c000f100c0c1d2024000020000d07400039040102c0303450300340c00303405081071404402154485d0081191000810035514000151040f041308520100d6a44440703104007418000116042c0401081d2820045100d07007507540900143c40c800190759030481064001540d0021088034000d40c1130344070441c14001940700d480b4001f81103a00c0c01030307109070f0140507000a445070400b003850142100b401d0318481143ca048014180100b01c001006010100e0f81d940c01094080a09000350206c82c0d1840070038200240e5070781400c010b188034002044000910304c1c1600210f400c03800040420b60a01c4c00f2400249400070580c94035460503103a144a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 238906420 1250 238905170 238905179
    0x17030712050307030e0f010f0b04060e0109020903072615060603160302040504020a030b0307151b02030705060f090306010e09070306050a0b030d0207031b050a0b07050a060c1701050d050601 83
    0x9040c0e100030003d000701a120003040040c000100914449400041d0021070580c0032219054200d8521488140c4180e003010801c10980000e00c0c3c0040c1582d40c0500b025a681c07080e00e01191400f00c040d403140d020303140c612010225000600f03000140303500040050391001c141450205003a1a015101c10303601c4542040450340f0031001070341c4a40703502594100981401e607107000260072030f0411a540c101098840e0362800d403034030b0240000c0020b45404412a06801d00036a0010510000300c40100301c58510301105000395601000700200038180104521b507517000c0e8030b088203241d0304810045802031140d80004160f003940b0303104552050380128014460390345136446140c0a000007405411a4550759a104901c40e1000e10010584000c10740051500c3c03881c5113400851080303420003c2c107008000c145c00b4003880d80e07803c0c80301c0112a01d41105035113590503400d0140c1003048044006104903d000c00785218242c02c850000d010f903041a2800f1000da9942003800145050b607038000b005900100300612 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 238907670 1250 238906420 238906427
    0x40e090c0f0603040c0906080c03010501091a1e060f0d0b0301090209070c060e0d0c030206100b16060f240515031b072406050d050a031b05010f02030117030712 70
    0x1503100c0d005c0c20303410300915a5414210101c91302900003613850741103800d484c1ca29050900900340100300b440f604200f55011401641044402c54048500c940b02d042140b8441458043c01c0c00c00440e0b0041085035901030202e20301d1203a60001410024890074020020f015244c1072040310443e94010b8802d0368507644e52a4100c2d06040382c8501194501d50391f02c1d502140040401c0700301201151511804607103c80c900340640b405600074580444080341403c20f04c555030100e07003600c0c0409545540c03420489403c0c503000000e07160500201c8034030392410242c2c43c0100900c41d40c03c9144001c04081e038a030161540280309010f1980326024402d040c0400104080790b03100c0c00d07071700c0682200008180c140360140d0780c1c0c110200e40030700000e003800312550b031040f10502c032911541c0010817080390000f04051036036640c42d44401051501406201c8403824000b070201400d1500c00c0c15a07805002044a4410030440c40000d400a0040342c2808403100e410b503108800c0082160000f94000350b0b03604a114091400301d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 238908920 1250 238907670 238907677
    0x7050912060f0403120f090f02011b030f21090f1b03031b05070b0a0305160e01020a15021632060a0504020303120901390311040503070605040e090c0f06 67
    0x1a5085a524054406c0c4608540301e25811180308a00000406209000060590300c00205185c0b00701480384400c80040c0d00300007010034011040c2071011588000402c003400c1158080b500c2d42c101c0381001d02c09010066440b200d0800c4a2046440d801c40c09040c100504440000307000090100303884c10b1000400c400070b08100f2016074030490452780d055480e441c502c29030340c102c20b4042e400700382c031001030080114000d44008000c2015141c801030000700140000c0d55146203050203810611044040c848070309198040782d641a2410315000406c01c141e02e00444030305000c5040d4401d8840201f19204001070003001c07086243c01000041c0303400d4840e14104001084003030403c0342d15100422140700c00f5001101250310419845000155a18a070950308401c00d110203801c010400200d01e41900c02c4032903107001d50041b015481c000591280a0100700c00300e1180390821076051113680000511507500400820a4030303483d501d00007040e12805c0e6040d40da949080c4910741d12000300e83ca84100c1d4282103014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 238910170 1250 238908920 238908947
    0x403020409060603050d1809050c0a030504030903080a1211031003031101140f0604050f0610030e0339070302010c080f0d0c02010f1401080c151207050912060f0403 72
    0x40c0d05035417540d40c10310f07149645072404042503ca00d24060710340b20580801d0018410a2028042c500d4580c140c01054400c4a400701c1c14595603601041c1814402c0010b03034041c541c0085565500d19480304054200303070040344c50448142c01d00d05040c22000700075003624040c10802a008461a013580e800ba100e0070414222680c45650fa1a0702001c424180300c0d5590046101101c01105410300d00107020640314010035800a1007d0f0500f400394540b585003411503001914a0000340b01885149814214810703910140c03120070480c15000030000d0700380c442e21102e6a0406032927100e045c01121250b256843c42c8000ba001ca9490324003000440e0303107040200b1400041c1c80480d498040305490201c200c0da044030103500140c0d5035403100003480f0282e00c680750341c0020500c2c18104c2580341c01409a83c916050000301d0040c682c411040254180000c2582c044900038058202a89404c00e00202550031454049100c1c500307038036109007105000f09089000310014600910166520740f0300307460310000480e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 238911420 1250 238910170 238910183
    0x1003020a1209150c0203090f19090504050d11151b0903010c0905010e010c05060105150f0a020a0201120c0e0f15040f030204050901140403110c090c030403030c02120403020409 77
    0x150714800388244980024a40702d03240b828901e0192440200c1140e004004c44002d42d070042080a034550b81c2c0303034010309401100302c48400c40d20100301c100b121401a01d07072250b10f210741010280010058046030315440d80b1b8060741c50314216401302601c55500c100301c241d1202d1100c0c244001c1400403d10020450103030000843e007074a4000300030042030849000e44401c00021303c4551003804990307444400000015400d00e846048001180c0b07855894440612a0a00c00c1341e40030500c0e42ca84201e1000d032054041e2000f00c1035103404643c14042e44440e00780200b24001210b00843c0c0d8100038680c491003091b580c04d642c603903a001c4051020b2201c08a646d110280d809800200d20302c0540e039515008102170000510210003181c510f02c1230005861014100c0003650b41000410010300b140c9000c120781c0241c1510f01000e8a00343c1d09001c82c100a402c8030469000880b03542003141f42800400194040d038400e03079040064801216007240c96648030702e840600b982040104001528081d0407201a8a0240a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 238912670 1250 238911420 238911437
    0x3010305190b070f1707050703020f06062b080705070f080d0804020405070e03010f0608120a02030f18040507090315140712060b030a0518010c08070503040f050a03030b100e1003020a 80
    0x17450001e02c0601114510b0008000040385070816074140a2031a89403d071600404a504245000418001400c209e298041c10042844c080952103076092107009078001c96410750301c0d68142412600e81e000e034010507205c2060580001001500007890b40d8105d031070760b6551a21915a54200b1001d4500a8503c3c4100090406a01d690f070307030284506281c0c010b05107000105a840c003a0b6940c01c10f8441826a1013100040c08096000f030380100c1100c14864209003240d60303408051448240f00c84070b03035400c01e40042c5010700300081140c00041010541c1d001d000c0e282c4880709208010019656050813040d11595103001052006000340e08100c040c40d010707040820381d80e4484281050f1a013080720001060f40e00d034401d008069070644454003210310040d00920810425400c0500601340240030141000300000000f000d2000d12803a05031403d07800800e079048a1803d0030000c000c0d02442a20030b2141d2040c01d85c5002c09806500805041c80000c3d0211402c0781803c04240c0003508488402d600307108558 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 238913920 1250 238912670 238912697
    0x211021082802070e011d060111102309120c011d0d0f090602060112060605030f0607080112020d0807022403100b0913090201030e0d0503010305190b070f 67
    0x1da00200030788038a54108498a44165009107000900d902000c01c0c03003031800040c042140c80100c418075445840c015a801911040c004030740d01494250a40782d503002e4241c4084821020b50045501c241d038440180c04000020b640c03400386418203480342ca40e40d078001d13425108018101e40142101d014001e000103501400d07480050099800003a1a000703a400403020500303501d40144020034203051358507100b03000c80c0c200a4083e43c1d4401c180901d8075002c018080010070001950400002f415010b01601c42042c80d062005a561805868103004074144100128009003a140002080340d00240140c0c03030116103440d4a01d882d8020300b400e81e0450386000c401e50540200303481da071000400301d80002d952460b01e1840001d40200c02d40195000c031404100b402483c2c1c2d40e850303034090308491203400018080449d10050700204610a182c0410b4084c480e80d41c401c4a8111019504176806042034034604440141700d040060103414005144440c1740001c290224890780da03203c00c429450030851620a0354 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 238915170 1250 238913920 238913947
    0x15070315030f050d0512220807030201050f07051306120605030109050d020c040b0934020120070512030c12010308070201030b030c03100c120221102108 67
    0x80c0e800a40e071200d6041c5040040142c00c0108084040b0b461030054281310b004e0903070251a12010303210703102e41480d801c01010b4500502030003110031903104150542e14180c0b03140203400b9141c04c8840511003804040052030450094049407158a00c0e0046030f05402d08012007524600c51401c0000605039030340c0300201d840d407424422480d142e03010703400610f06d00d201a40004e1500301c103110181d000300d0901d041030400f1349808298682150354030411000c501c8a002d00e00d5104190282c40c5500c41039441c0c0a61581501944900d02c01020100e483d0503107603414903206164810410300a20710350161540001c0e21045201940d00300c255144a1854161800b441401c02c8100381c000f500d107808000717448411036815200340c0d0075400c403e4001e40040400e1000080e200c6000344410180c80b0b494920002d141032040d040c0d044040240e40c42192118803110320303082c80700310400034010080701010210f10381c081b28a08071030031154005206c40c1800042c0090180b01c0c4a648001c882040060100c0c4083e40403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 238916420 1250 238915170 238915211
    0x130909030504080d05040807120204141609050a210302030705010911130c0906110c0904080d0518030d02070f1509060c050405030309040513050303040b090706090602150703 76
    0x1d81c1d80715212030610450074103124002c40d0380010b0041c01c020030000b01001080070012903000030300c100d00349006800801d0207049079604241501c60309804016408030f0550a007025101903036070710b18030103480c1c809000c501c070814081c01d4190107082c1c071406461081004c0d4000c010307200344150703801d0401070340c0ca69007900c2ca05e020485500142032042580307401c10350303865114240b00d1304043c0014100350f43e001e0301081d6180a40400c20034000a805081281040b1518010720007802d50304051500c0c0c1003c8809410030b61480f203d450a08010488005080c0340081c0f1841d8400059071030261400403c5009500103441101c4001c2c40c0642000810a00c5c9201c0310004156000406d010500d803400004071050300207810248a01848240001d880010540b0703098002694001602e07120202034041c3e809400a00034041e00c00081080b00b04a01030010b54010811300f011102580d4070b0f6003003524900703094052400180d10000d603107001c900c8a101150b81106007070070006180440003d0311740321941d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 238917670 1250 238916420 238916423
    0xc0b040f1403120105040c03060b0a032a0c0b0f010f060e04060312020604060e120405041104240e040b060a030f0b060c010e070b070206120c04150e030d0206040314130909 75
    0x8180c3d00104600e05040c003440e00442101e05c0d08020b031908010503004540210748441d4105a0782c4c00c0b0b9803940c0e180d070082031051f003450303409103090403000e1481c0105201030304242256010002d2001c9140d4142012a5a050b0358405c025200c940342040c40031507030760f1501c02c0c4c15a40161603040c0000424980d10040b0304c0420282e001d081079182c2410040d0980720100c05a00b201c1d803000e007406040c00001c4041d0360903120120381c0450a404100c3c1c01624034000c54009a03241000c1c14007101030002c40c1002440080d03c141c1f1458020a03181d020001111600090b658200c0020404410128401c2d4441926552506800a6020041408150a60441803c0200c0303a035460401d01c4442e0400c102c89801840c00c80103035451304140f07502080150051150486900c1000404918107480c0303c401d440103040c4084c02218134200c8000c009103200540b840c0580039009642420405030701c0410a41d11580d010b40300c101d1603008441e40f014441d07100d1040003951291b0403031301080000c014003a490555 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 238918920 1250 238917670 238917697
    0x20603090115030f1406090c040f020d020301060201090b0a050705041716031115030903070f1e0305130b030f0c0306010c0c2c09100906060e0f010e06010c0b040f1403 73
    0x7442c1c0d2902c40300000c00e84d0309074065607003c1010007541f2800003c908840e410305070b4000c2050f030702103520100030740918000c80f84550300110000c00c41e25070540c8460310280c003514070040310362030f414451011202d085d074a900016804010512104110100c0004011940403c4070420406c0301082494514076820484054001b250045014603040080800c1d040400110382c3ca507003089a002c0c1e90700d1240c1100184071540017112039040c4200c50304102c10088400c1e20203042c400b03040c81e0007001948010b00140740f50b880d82c0d0002c1482c644d080103480c402c14410341000b520f0b89500d01440707982d401c001e000d203040003039110551000031124405040106502001d0f00d001d0300c140d100c201044121811202c440c01860405c001c03001d41c000805142602d10250009180305c01410641c01411b0f554100c0034102c0d28010030300c03a2802203055140e040790040050581140c48040044034040281403020b04109540c80c0414080703561224010505031140390810b0003891400d0380b040c00c540258103440b074071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 238920170 1250 238918920 238918943
    0x61c05060f1903051c1706121203070207150c02011d0409050c2e030c090f0b090103060906060c0b060a09110703030b030a1505060f0a090e190f02060309011503 70
    0x800c0010032015906586a045001246500d05d80c000e001c2040c400848142c0c000c0540031942903201c4420245004900030706441c1c5481000e0302c0507910350710a441c41801803042806c000b40d031030390000d81101044020703964119005000e40045130155209035104c91549070720703030408030141e44911401007940e00c40c50240c010810780c0410420858855401c001e08000140040003402203c86902143d00545090001d01903045180458046900c1d0300581c2241c4c10448000c40e125120300702600307503040244c4c2c06004083d258820320007622300c20f102e640c02050107240e9400c00680b510980c250701040161a04085036031718042174064074140501001c411100090b0302d001e055050090342020007095000b4624080305e9039540c1200c034500e1403e1242c15550360040380d1184e403018041c4c03079103100040001110310f45400e1408020a03a5601c1c000d414441c5442100742101e40841e02c040698001540c410029070507002d100c516800140307020040c0d540c0b4054a9401d040e01c1103400040c41c014007a2680c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 238921420 1250 238920170 238920173
    0x5030d120b0603070509100e0307030f2102060c07260c0706020601050906040509190507090609090c0501080c040e0103121d090a180c080609010b061c05060f1903 71
    0x111201c151145025480c2002002003841e04081107403645181034940e10701400c1c130f1210484100901a1495a05002d80030000003840b60060210031054000d04c8025001d415250450b0000c1d0b0080001e140540c1054002810445064001d0000709000c1c1d100e00170100304084c00b407400c6046248805020b10404902540c2314031007009248050061400104202d50402d000584001d1004104c00e102d41c1c0c8400c001042c4d040244642041050103200c85005441d092402c1070b102c0c0e01c0e0b8000c16a5040c60604000340050460080c00c503169000f202e10807100f4140401112440001010520740d400108000107d2110a2078803900860146104807040424820018140c5003071141c20749403005904c1001e60b00d0b80c0c03800071141c0c0040310244005481c2c0d1001318002c862000004015140105d000c01c0083d94000c00f00d401d42c4a802014003c100140c115070410226004164290b0f81040ca04240c61040290f96800541c000030010300c29890444503030b001542d0390303000144a1b111003c6a140400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 238922670 1250 238921420 238921457
    0x20403060627050c0c0613030e22020d021905071203052214010212060405070206070c0b06010e060d0e0606120309091305031611010302030403120f0605030d 69
    0x41c05060100009180052200308101500c2604202466015a99030204210908007000c48802c0b5629105903141440e2112064562050420054001ca000d10b40d00c2a00d6140c90040503032503c3e880c0040064540100b89501c2c02500b10000c070007485503080020303601941c2a1030500303080802c142e803035683e039a40526107610219124072000d41450b0600e0144903000c2203104580c5e1642c55a034030741100441c02400c02c9400c0f903140c00900702e00c2c0e500c0000c0c44030a194040d441e65102e80300558003403002e920707085c40407030366800102c501c000000c0800141d500080c451040341604080149400c2841514010010728580d022094201034144d1b9a911811500d0b41449416404001180c1251201d124a0070705a1a40f042a05240c81203615000056000880faa141c0d02c01503040030880f500d595444090b03d00a207224a0140c0c1c81d0680c945e00100c2c1503101e8001c0b244101d41c507541e81c240f800b90b9441e01c0340181005000d150f11150f164075010516031000c0002541218540d6240f05611600b02c2588 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 238923920 1250 238922670 238922681
    0x8060f0a110f03060f130216020a120201020309010804110a0f0312080603120d0f02031608090a080d090503070f05010506043206010507050a0302060601110307030c0212011401080102040306 83
    0x4580c00002800111102220030043e01d81c40030082d90802c81e03a284100004036046400510110820310200c0d10410446e100c2c0038070000c09100f92841c0248a4079071280c40c070f1582c000c2400070300581c4104840c6034076521480d4000d400511824000d00c4460304040001d8455001d03403c2401281c0650004000b842829441b050300c9203824140840c0c103051880100c0e40355031000c101e08038103c40c0001c0b02141b400c82c035484069440882e000454407410000d25a025007a03030505440002505c09004c0b44c0ca40d207021070800803065002e030304249001c08c03564031034000e492249800da5032400300b4071a80010880c8003000301000f9100c0d200000f44c62505404101c11906c800b1880084080c18401003c0c0010524080301e40c044002c01010840b1340e0749074012a001d103e010340040240c0540403521041640006609002d208241ca0781c48085603400b02c0380b944c13405420401b500148809000b0005824907031110030700e00d82e0490001c6180319040d04c80c002400300c00c1e808944a82e5000500700140309807481031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 238925170 1250 238923920 238923941
    0xf1a0f15190608100509040c1403060f040b100e0a0c09170a11030f07080f07050405040b13060e160503060105030703150c03060f06050d05090f0d08040c08060f0a 71
    0x5071404080052164540d003a9a4000da10a02c403050002c140d018000340c0c034040003400c0c0200072849619040c075103030724212482d12505107a00e0480c0d40e42d00c200c2c5008168140b04c0d2610b07009403e01c40d82c0381d807606c420f005001f425403420000c20040c085054201104058420200f158000c29141034040c0000c254443c0d541c8075285004510b030300c0921041c0c020812070403c9401600707010036060150700181c10b107400c2c01e280810310b01c2100c900003407800300230580781c00c0c6a107950142d806132503455003440309070303101210000c1c8440c0c0b021000401c5009850620401140151000120b480d521001c00b80303420510607001d0403d5035140410400c0703140030002580501000c0e805000440e01d543d4494060a80844ed0815119141c2540414032881395204e00014a400400003421958483d405049580b182c40c00d601c0a0b401c100001e07082e0200020058004480c00c8000c0c00c45034141c400072640500090011505160b0500001603000000c001d001e014140d920815803150a00c440e1031821982c03001034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 238926420 1250 238925170 238925179
    0x30607020307062313060507050405060405010f140d06051311070f03140301030b090d09061b0212010903030e0d0f0914010c0507080c030d020105010b070f1a0f15 71
    0x200800a540481910321a69200c0000700350100142403000001c08031540c0e403030900d0712020400c556040131040124806018060420141d150880101d0300c601c2540103040d00b14108020400c440c0d40300d100c1d107199400c02460003000d46ea1511040004660084140e041c00329102c0d802032141b0b15051000c000054440d40f410490343c90070110310b214900038484050520400d40103580189405040100251569211f00680e82d41e1685041d220f0316400760b4001a43c5c0c807440891485041c020b10030745081d0b03081ca03243d1440322262006c048881c0e120306d5030300301e0300180b01c00c0d1b41c0c2204000c01d019200740c0600ca070700e0118010350741d290300d1440c1100034400c0504102c50858551513280d005043c41082d035000c80802c0030380710b00b80e0005071041ca45d003a1008100e440303681c4000440d21004603407560004401c8050b40c014000ba060100e0030303a00203004414203610104210000188260240c09400344100404031044c409840a0348140100311400f0f010705c04100d04109038a0544484030181000855 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 238927670 1250 238926420 238926433
    0x211203200a11061e0c190207030c0605210601030906150503060601051306032705010504020108091f0e010e0d0918090816020406050a180606090e040314092d03 70
    0x164604ca809601052805140a400c01180340c00b49944200c8040c80043c0d00c40341160b41901400030755481042c0320a49101601c8400403400c944584103c0f031401a1004c0d4060b40c03a12480540906c18130080c0216051580d10340c10040001c0c400d004208000340c031312492500b00c40c5014140340c01d20384014001d070304225040250b01100c1440105070000d65030039150000d02c1203010b034501e061003080c1a540b1140000340c040341c1001c02c80c054001c80d100b07038401c2e030701c00c000d50b111101362540c1c500d55515085440401c04902c100d100100341c1c00442c00c0c41c44100040b50400141004030b05102076112520000b501c401c8042c02200301a4031000749280d6000e400f0400c160305a21001c51900400d6100d89241071956a804199a220f0b044500030b004000c0403d00c545640d4180444484c2c240c240d07060301d0030b00307140d0700061850042c1c4d80b40b001c840c0d00c0c107614041965161ba003100c01c1001100c00c091551401c0c01003038000c2d281c03a2030110f0200138a0a0640e4410700f600c039030b0054000b1030340800d8440e90204 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 238928920 1250 238927670 238927681
    0x501020712090b07061e0203090309030d030b0307090e1002040b04060f02030702090604020304020114180909030405010e01050c030d060e0106020f07050618030712110109211203200a1106 82
    0x400329030005800400001e40e108029215000d0640e0001b80241c3c00b078004001c0c05070001000c40100107040049040700ca8001c103c08041d410340c1c51038440280d1541100c1400c003c200303129000b079580c807147c03032081d0381c0340280c0840200100d0304030350001c1c4103542011070140580c0ea0005110000f8500900042d802c0800b9580002c10040b4000e02060065070084049011a40541c459200c0d00264410044c0c8440325408031902d070700700b500040c9110b126400041451040b000c4104c2e02641c0041e903e40300f000701007400560340d0b90300102a070040e6201c20089090405030740c4c45400086d00149210190030b524101009107091001112030302c0c1904a01c0f0104015690101110100c00004d19500e2000c070706840042d0074050241c0c00903840016203450002004089682c1c40070700d001c01d80314440322a03100c20070f05280740c140b01c00c0c048011440340301610200f6495a0402c01c101a140303004920482c0000440140401080f0582d00c1d0341d03804601803598039045481c1031410203d200041c021890403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 238930170 1250 238928920 238928939
    0x70f060902030f120a031a12010218220e030f0315010f05131502070f030501050f01211e02180108010c050c06010302131b05040801060614181c050102071209 69
    0xd83c41d040d0706250f50b6501e0001c11f06491248501d8001006020588407104514a41e010394056050143c07401d016408d1074540d4501542c1441d0619084489550341420b4098030b28001c2ca010340c0c0c8003d551000780314104040ca441001584650843c2c44044004080c100000d407485443c1000202440b40c10301401051a4020041d80d007215502500800150301090b41641080314035009a000c0c4c034070310a004402d00c101504070b1800342081003001e600356aa1100c00e242e01c000d0291950803480d80c4c80d07a000000c280c0c1040c06e5a2021034003800210f03042c81d1030b40026801c5008280e007460011301030380100006a400e1140ca6000c3c0741034140303286445403610aaa460b0841404000e10034503034070101049405099200411a802c0501881c455200980c405040d03a000b51084140300d40c24071a01245a07440703018a100c10202c14450305003000c6031642001d10309510695090382004002e08101081c90020003401c20040c02b0300300042c0d503100c2a0030000e6400951003034280900411520401000d1003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 238931420 1250 238930170 238930177
    0x9030702040b01090504060b0909010605040807060c1b0305150903180d050708011503140703030504060c02031501060e0a050901030f0f060e01050106030b010e040b091b070f060902030f12 82
    0x14112400158801c4810068403213000c07a40181c0d822501c1c024000ca030420004004014104007269152143c5c0c1c1e807900d0481d03140c0305900450a280d00400e400300300d154040e030b4042041900c030b000410320b000001e8654841c3e0303003083c0e401030b141548082c01e030143c2080c4a0346065004030106000d1883c20140d030501c02d000209030003009000d100008110420701005001081c0035105200081c8044400000191202c032401d00054800940d81e00c07400a200c10b002816400b126403640304d15003014580341c025100d848a0140503030301805040810350012803000409406040e980d102e418035011554144000e203d100d030003a9000324a41c100600200d048140090080d5a2108100341034030340e5403404c03001030300c000101030116600741000454150b40541061340504420317655401d084040208002c1603428000c4e405030071900e40c8011440043e40c45440e13101080c4514511307840c0c0012980e8904e035001c1080429519517039290207220071850b0600c10002c1c2042410004c001c11501014507502520 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 238932670 1250 238931420 238931423
    0x3050d0f030510080304180912020a02010f0203070b15130608061005090f01050d0302030c0106030c0e071718070e0f0a1811010e150a030507020c03190b0402040209130b01090e090307 80
    0x8100010703c411f054056006a25071585c840c80e86040940d00100c0a0344c3c0300c2034114201d000c5030903030484500ca00c1c0300205447c0d007a5081010141242c0302d0040d00540b081504922940013000c90800e000e45921034000c4034003e0108800070211803400303103414102949036400c10381c8946c410800b40984942d400701d4150544004440702c2040041a1805a10318032944020011550a01c04004140701006408500b1594820320202c0141d5480a080b95612200c0c45e8003034582c0c61143c0031803103901da802d40020314011160101d43d40e1a80302c2c41024803a142c01c46016001c04010710400c03201c840300c1d010300350f000080e01000751410680741c3d03a000303615100e84060504100301d0b02c4540000d83d55411014595038440d40c0f45035502d488105004018041c2211800f0251090052445a900f40081e801d1818070307030b4000082c1040c403580d0b21254907443c0900180da119400788590940d41d610740c03408248031365420500159115000e80054803e00c00d65008080c080403030020000b290340e01004071860079 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 238933920 1250 238932670 238932689
    0x1e061804150303080f15100503040308060a030b0711030d0609020705150603030a050903121207020c300f071203020f06010e04060519050c0405180106090b0a0903050d0f030510080304 80
    0x507940c950306c1c0004481c81580883d40080110005089503400c0740065004074004c6c1d80e10041c5a40e401d007805917020452100030810700c0844001000544240c2d00c400070030503900701307817458890b515001e041510010f80211900396400640c04003005010010f5220880401d15424454540b40c4002070b164021045540d040c81400100e03501d150b90203001001d03807050b1841c1069240c0701e0a984003000d031a422106403015102d4440070036460302d06200c6280e103440080c281148902240100505803d100d904446020f04c1850a0415409014071001c005840c1c0a0102000750f552400e00138a0400c44260307107449030300300c100140b1603030f81074592840c0c2c0260440004525521180b48010700600321444132080e0314a854103024810b1100790061044410844641c01746080001180304105c200b8030a00c00440c2070503100b0443d582500000e081c07413400324100718145507940e0710b4160401064031000c80c005041c1c0030b2000c617410740611655401c82c20001284c0f4017141000c3c40b19079a0312a41c0a0500342 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 238935170 1250 238933920 238933951
    0x90c05030f0c0904110d0509011a10021603050a0219080d14160309230f040504020102150106080711061303030f200309010506011b021e06180415030308 67
    0x790200030040f10301d00321015108003e4039407000112000340d003040180c0d0010600b008040b400050341402803007200304070100c600c641284200100310045148403e42c0d0294014008420f0009404503403100046020f070015140e11000c41c410481c6407400440000c50400303400f039003808030300c81c001825419060141420302501100d010261220300607013484005099035404090101a40201c2c5002100e0b803c800415041103540c2400380b1806081141b1034100c2000c4180c0b41c12440d00c1d800650f04140180103417581c51021928001070b040c1d09070480404a00d1503801d005095911502440c40070707210344041e0100e8100017043c24803040c250701c806000c1584841501030304084d6a403020741d6080342140902c0c01840b9410303c0403280c0d00115103031000d552030a00041c2583d409401000c03071200307c0142012a4145650030064003d0340e5900340c0703160340a20f0030240d1b41500c0d42c10040040d4480611194a9000250100b00588801a8000d02000103500c0e0404c0069001050f00e5000200308941001c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 238936420 1250 238935170 238935181
    0x50304050a080703091815090b0315040c03080304031d040903020a0b0c09040c020c03010b03010525020102040504091401050108030a051c0b0d08040e150a050111010f0f0e0601090c05030f 82
    0x90605146c1c1218001155144090204810035030000305249000c0480e070811a03543c4002d2022a8080c9145542640105218110080f111508103621612403d8941031840c1c0348d84410300c15410849007140400d1103078031800b0800c040e64003e211000c504a400f8000d540a40d5002034641100303200c000c0c1340007090740200e04800c8a080644024110140040264100f01d01f0000e681d075440c000d0701c6019500c2d01e818401c8905040c014103110700c0c81351140c08040100d105400d40001c444440a1046560034400417070540c0d550b00606e82441e005041002c03060880c040c0903421140181e0148582d039108024580f441504602528660b4014554a91810701180310301c0c4013601c6501c42442e07110130b054210108121032140070b80181c4c0c0807000121000e03603421141a010841e0003604940c0b01c926114200300661103640c8600840d0003510010a00384c800402c40410f99074480d08840c0216110008041032540c100061030060140003018444203205940c0502139100103010868400302180c00540e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 238937670 1250 238936420 238936427
    0xf12110d050f070906090c0c080c010b04021b0d091809031803030908060c0304110607020f09090105070212091e0d210801050103090515180a08040305010c050304050a080703 76
    0x200d0160407200303641042d40842c4009403154590302070804070502e0301a01207401e0415110700c08141d0603545840749450750766150300072a130b0441c06da0340d0019900d44084180684507800a4a85002c08002c0705040d000c1030800103041803000030003041003080e030460400810100c540c1d68900c8100c0e110f0000707001544c40c2012a0320030211a90401010701c00080001056840040c2604039894801030700c4551712411601001740c481910054070410702c00d0702c035140c280390100040035104c1c4000d1032040314024101c0401c19860b8226035032851030f5590070421009a406224044001b441c5071105403800342c0e15400145486403c003001202015600f54040313440c1c48031618a0358180e00329024800b0903204092a038800c00303803540340c1030024401c1e100000d801c0d4024001c071003409612070081c0c00b1020607924040c40150380101040300181801c1100c0b10f40a2042c00326400e41030003100002c2c1e440782035003001d5085d9079000c003040c000c00c042002084007148002c944015a035911640c26070362400a402e045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 238938920 1250 238937670 238937689
    0x503040c0f180b041b0e12031b060709060801030615090c020c0405062209030c021f090e06030604030f0e13091101180b03040602090604090507090906060e06030405010f0203100303090f1211 83
    0x24545110009c0c4506902d505003516200e41056241122002d585d0b44001319002d019502c98100494080c0c00144009981030704100b038200b142d40000f0b4480da554000b070340c00381c0317440c0380e901005a0840103082e4a181000c0c003500380e100c10155031407020001d44213880003655110740410f40c4207581d5801001b003010321444030030740b1f4181c005100382c0c8240c16052428000031001000b600218400c4240000c000607001441071003000014040c11256070785440548543c0e170703200e080c8401c11038202c01c0d50351141c2d40c01c44000c0300340c010000000396030b000700d00e0720b1500115505a1241070108440790b00401c0030b0544045001c1d10318108009449444501d410406800f5480b465070744140d0200b00865007030925404240700d10300c40d0759888592030765082d90703100301e07100ca00a80e030005400091107095402c04200a5811030700c204000500b203803098600c5812038000b03072008028800304600804c181580181410040d0081e41c60804c03100c0e2902c1d284a00038207400e100140304005440085d4201e94445401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 238940170 1250 238938920 238938949
    0xc08090f060417060f010e0a0209010915020321010503030f0d060909080c19080414010903020d060209031c0801061b0203012a020102070b06010503040c0f180b041b0e 73
    0xc41c0e00c80b900e81c0f01c4a2180782d4108120112840341ca000981e2040c0e07944e91281c122044403182d05015100c1409644c0a5070141000074144000344070001070480035040109801103a59001d1a11500ca4850032181c0781400410104007046040040c84140c2e400301c1150b0400300c00b1118a940e8407402c0303007024068101340e80040c44440c648010703401403000a80040c092069514187c42141e903030ba9181c00d40d07800c021940581003200600040c41004261a28035803218814101089201c0e540e50014410700c000d15401c944460300450510010f080800048a45405079060b811480420203c004c042920522640042210455418000e0131681303041d51050782d0040c00a00c9140351400203146e00c0506d508400c0c81501100003250421481032095440055005406028a4403510011142c540000d00b0540c0d0040d2038150001d5002128000c8400a001c0c0d1050f440e89400e404d0003010486407800ca4040c0210304203d0400c811404101d619950a00e0380c3c14100001c01e14103000c0340e68444280c02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 238941420 1250 238940170 238940179
    0x40b1b0303012319270207141903051801050d1a0102070614092106150f09010605090d0519030504090506030c0a090b0d060c0e100905010c08090f 64
    0x3240e20340784070384540c00090305211200040c1e240c140601071402200345100c080f404d14a9400d000e0514100f030b8500d104c2000100583d44401c215440300b080341c1c0600011140c100701c5882517408060240107407410005070031510b12801c2500d440c09410391256100b1500703801c0002110355602d03800307a0103445640d103182d001049030034002000d850031713010b00c41400c501500c80d007a00000c03007a00c202005903075900300c03114090034258180d003809600c5072100b8910003c0c101e8008000c8030094204041072040009466801c4a14000001c2c48000d107034071780400707000b580314100620856412100301d695912003502d0007800381c001818500d04010f9092007401966080341508024154008013804c25034817501001c00a68451004041d9190340c2a4400d540140e648003040040d00010780c004200b91502420800d04010702d55204c2d400c9401541c07101c00422024000260103041501d079a0b0301c025254205440c205041500290054141d00402070002c0c8000170490f045031103a104000742240080d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 238942670 1250 238941420 238941427
    0xf050102010b1c05281a010501020c042309060106030b090709030b0907030b1e10120f080910050a170f1906180c1b0b0f0402030307122a08040b1b03 65
    0x1003a0344d441790340340b4025551440c42c4004504040790450303001d412564140c006004010301003052001070f0100c40303041e5100320340c4217520401900040d6111886132034103501400880d810001d02404592610140d80e0041692008020740360fa0060040c2041d20f07003201c090075071565203c06092405070a42c0000b040c0d0803907801032001079403041d00308240030329850320081200e039640504100e81000920505448209180da40d802143c0c0b03d0708a0302e020743c040d2110610707140001002c00d61400c480e90030780300001c4000501d1041960b05c40c285108039820181e9024460420005500c11070300f0240964403010340bd8804c0400c1d022413076102e40000c00f40b070000c000b00031002401c0b0800400304081c1c10383c0070401140c1c3d003500c80308180f486524200c0e400408207030740b40c0b14442d209071a46401001280c05101c00c00104003c2441c0b840b0351041d80c00c2580e6400406808003802c2003a10300c1282d40304010300343c04140e83c000120428240c8003520100d22010380c94401b4580448882c1c3e451400d20b000d00d01000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 238943920 1250 238942670 238942723
    0x903142b0b1809030a0509150c03070b061c06270501050f010f0305030418060b030f060a0803180f0105091c061a0906010f03021e040f050102010b1c05 66
    0x1600616074080e0308a41c030048240c030000c001200340ca41160100807a03001000f0302d490389401400a4520343d400034152030f800d001c0c2040b544140d0f50181d40300b951340790f0010500724200000700c54050b5001d4820345030313210020411000701045072003010006103000e490300d1100721900130002e61044901507003079545070346a02e541000e500801007030f2214000b0f40b00d584008528000c611680d041102e07484001180740c24548100410607051406101900319154100010b000104001940c041d006692203000c0e107081c0001003040b0a0003c0d070180304141c00500400105c06441002e81c24900010754590031142c1c0720000407241742c4104000e042d4003c0302506601d030401d50400c0b40d40c2c0c4441c810f040401c484048203600c41842e180c1c00c941d89500840450000c0d00075449025100300d0314049080240c200b031180364540c250400484c40c00d640059011404005880c2162180c0d40281400c0c002080b01c08203001c0408c0030324580c11104019000d0710718202c1c0030000d0400901914003406200d485107480700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 238945170 1250 238943920 238944007
    0x3090402210f0c0a0f05040b0706052401020a1523152b0507081903030b0904050307020d1b0303051c1e09060b06030103080c060109090314 61
    0x510994001e001803a0019440142601e0440d00402080018500b0806420400c49031174207181c02c110100074050000046240c00c42d8040c0c2006803169201040c60301d06501c030703020b9000c8200301381c20f8100b0300c84209003542e903000701e1445034003074101d09017880d5094603c802d007019140c0101d407011414408030265250710518201340d80100a0000e502240410001c20004004000443c881c9402051107421203035010004040c07042d54442c806031038a050b510a80380c3c1c144800c80a94455003080c205542042560510800c02c45401c210f58004040c1016150550b0768014608001d001d002c43c6580c603030a0000300d4030f0410011025103400c02146880e85001803582d00302c4460701301c0d500c40e40a03400e41120b400d03009210007008240081d000e994002c070b41c21005424542019181c072381e5a01ca800fa9143c41710380c002c40c01780d40910755080d945d18840103090b00c0c03c4d0059100003402481d1510000c00643c0c04444010510060f64580b034982d070040d54040c891600d172031004248400d0329074880310b20011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 238946420 1250 238945170 238945207
    0x19020918070f030204081f1404061b020a08030106050f040f12031706030a0312091709192313020a0c050f01020f0d15030b040308040512070f1403090402 67
    0x4142d0300c000388161181425001c0c1e01480c01482c126802000d0b040c03d003800b00c401407404040541c40041117640041640c4520042e0655058a18980701d4210090707108001c585150b08a20520051203031800e60345541075940018050001000000a6041d582c0c0480005990180c80c02001500e0203e5841d092512030003103259086000c2143d04160b1150300c00f223041384e14400d81c400750141c0b51380b601c2c5a07001c0b5010540c0d0a07150546561b640103090108907010102d108050710382c12510390b2104007101700804071344000d0000c80f2851403e5000d10048a06a080c210800041c59400c10446912000240c080108240c0301400303038408209119081d9000200c44007e0b40105c042e0f584515031070107404d0a03446070200440740c502c010022000c860a1662112085140106860307056548940c0c030443e201d40240c1d4107800141400c1c051006000040c80b103000c80c050101401da01e062900e56038220700501d0750030047d21101611248070915401801104c070b449000070030840d520307602501c2440e800741 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 238947670 1250 238946420 238946431
    0x17040b0f0c10090f2a030305031e040215030403020709020309160b0c1f02160318091404021002070b0d0e070801060b0319020c19030f08060919020918 66
    0x224081603042102c0683c460750140e55044000504424020344804013100d00c05c1d01502d0290600c013403c51440c90a030110303080614401d9440c2c959030300b8030040c407150680f00030340090b0705061248103000040c0d0712420f0398417411740000d00d155129980c7d41426400c00c0c0284c0e02040b0850300000402101c0003000c25080910908051541c80741500c5079484920b40c0541c440b4200194817050150070381280c0c0b00c0748000b6a0569150141c5044000b121020052000c0300c0201d000c5604e0462542c0b00403280001100981100b1504114446c0c0e0880c00c5e5a850380080c1010b409000c0d47c00a03503011038800d000c4e43c405044a45600c40d602c0040f1224100100284070310443c4e00c0c001d1120105805a06001d0b64017240d45400350f8605548845c821a07600c504c01c84c482d49041c0350708000d101c3c030b5407805000c10900c1040c54a540da0004a05d0305000d00400c0342c000c10202040205000c20165070340d034240d10f58010004001c040285424142c0d160001e22442111550007008800b1031040725031109511031146 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 238948920 1250 238947670 238947673
    0x7030e06070f020d02011512050a020414071205060303090904030512070206060307080c1e01020a0f030806041109012c0d060203040303060e07050a050304080d0f0603060e03130317040b0f0c 83
    0x100b1313070000200e00300d4903942c4070051a1120620200700188002502d03201480c0241f040e6941c941b000d900280c111260420794201201600c800c000315980c200c0d003000003800c5140d10620007440d028000030707146e101c1c82040d903224103020000301b07043c544500c007501c40b070707081c0c6a038898803e0900302006959803104035a042e1091041080114503140d010402d000701c2c107005402c908012100300080080190a038942d01c1c118071560040a01090f40c800103603014500a4071490000d080c214180300940d65081c4030017020320800c100d43d0041e660b0041d55101c203000750600741d0b03800c0151705141c001c0002003080000d50003290400d00c1e206220301e42d802907001d603101c1e8600300213103075481d2007564010004444610109106100c48030886014000945c0d101384118001c9250401002e841400c90b0b0b0650402103026a846600b801040300c14490340702032043e0300d0015814440b8070304150101190305d0100400c120301c00b8200240700301d110003d60b0042c00070840041d46480000315100f01c0380c1c00948508405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 238950170 1250 238948920 238948933
    0x6040203010e012d020c06100602010614030604170d112a060115020709020408011d031c0e0304080624060301030c0308032e080601050a05060a0807030e06070f02 71
    0x2c10303034144a1032404803080070140c0c500800034200280702c8441164079135040c580030001c40340072800c1404040d200750141402e45420904100d0002c2c04c40d4400c1d0001c10355200d018581150b965000a881503200ba4051105440c00d40140001c03506401a180840c0c07005050043c0005204803150252448030274170164220f04045003810000310710140e4031a440c25822501c0180b0018041114421458010707004a400b00740e0755001c064120f0b417240c1d11440080c1d5440416850a0360b4440c6000c0d02d10304400c000310b0909002509024280c0700545030a40560f60b641890b252030b400c2032060390010590308041d1502403400d03d045494080c0d82011601c15481807014203c590b01e4010281c0341a80e401405030141300b4203607030b91040c1e103030f00151151034060030024030301d1405603121890070007403e103804000c90903c3c82c090b922442c068042c7c000038490b07061103000b80040d80350041559001400c40c6049450ba80300c004044c2e0080c240003840701024010542044810798001880c14805078030395003280d10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 238951420 1250 238950170 238950191
    0x5071b02131503021318020d1b0b0306090a060e1f030b040311061311010503090a0210110c0105040503030d05060a03080f09150a0e0f0f0603150108070c03120203040614090604020301 80
    0x106c03988051481480788201c007a400250428207172121041d44039030324442c4c50a004261a20300c41c0d07a140d010b100c41d450004200410b6050600c8000d8000403015020700080e401c040e000182d13504000c00701000d4a1221117090319031504041d1b9580196040700043d411070078141402444444041c2068101c0c0c850034020450721100e4000b440d11081d000384015103080e0400004440300c2d8006468550b0510a0b041a9809656a9041181a881e65840344980c001420251501303000350b00000d80e0512a05220811643d1004000c45030303200c01511000985603a4000060b682440a4002070018400407621000f085016130080010241c1141c4030300b0710010008800c0340b148240c0b031600c0c00185082456001c2d0b41803040031135001c028010058980c00d1001c0c4046070164204403044040d400208400c4403a9503081a40d1541101d01450003581c040c0305520040c0100320589600c00c1210381c0080000d06105480d0720002c08034401404002d01c500f04841d20355609c0f04181c81c04c0e44a546800130225 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 238952670 1250 238951420 238951459
    0x60e010f0e04140f0a0b0702010c050d090c18021216120f020405061201030b07020703020a2102060415080a271b080a051005071b0213150302 62
    0x504036445902902a11420315280c101c1404010300100c0344801c0b11140e030010100280720301d924049802c001410150303000e090411809002400c40015a45403030620840c1690200032204006c069000101c2e100c01ca52412080032046980102200c40d00e09442c5040700c45903800070001c201982c0011203e5898514070201c217000e480075080c0c0401e8a8121212640101e82c00504c0038081c00200181060303600c0c4081401c40c1e1218105083c0c0b081214010700c1088002010707a9044101031000f0130302d01c2d0455000c503145c10180d0041e425a108507404559038006691034040190b580580909e4039182e5400010303002d03000460100300861030100000c0c200070510711891030b0001c642c2030f0311008090000d07258240000300315029200003041c2d401c1c200d6501d6170003401400418420b00107000c0d4a41908001e030402d414080458080350408060001c0c659110402c02d040a26018031110380c624503100050281d451808072900381c03401c201c0c41480c00102809040f040740d00076228561032142d20100803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 238953920 1250 238952670 238952699
    0x7030b010e1012050114040f20030a061d0a05090a121404030605090a0201080903070506060f01020c04050a0e1b0901060309020a08030d0515011d0f0a03170702030106 73
    0x100d00203041e8039902851440c20501102c09842c0d141040e0360486050ba000720103544007604582c0501d07082c0e1180280a060600c10800d408414030401c1101d2196000d80c03160000a1300e000501c0300c440480850302180c96a80101300501d45000382c2b8000442c3c00111800390401112411407036887c100c00508038440c08251031003820391101c50140450003038001554404a000d05030f9904040c20b101c0400018214440c050140301e9560043c11000454400181700c150028506041c0c4d4201703102902c00170310000b641039040101202d5840c1014071101c0100e107000b8214000c55400360401e028401e0b4aa0030f54051340c03404c1e4051054030340b02c0740c07045001004403201c41c1c11250417002140041003842d210381c2c440240144024020119107070f42d203202c48e2071900440c4406050313558903018402404050900c0300aa4602030810f2001040c1200100b41310748901d04c1c8481c0112000540d0507450340c3c075900d241c405158409041ea0b208801c00500f0050740e000a40100c2c020744c6481000303d41c0024081c100d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 238955170 1250 238953920 238953941
    0xf090b0105030a1208090f060108031b1501090203310c080f0a0b10080706090608150d030c020f0402220b070510181401050a110f180a090c020d02060703 67
    0xa4a84c000a20011106076500801030305031401034490f400c0445c20280403081c0246101402961220203060307807000d1008142e04a801103900c10494498509054070b021411501c0680c5c0043e1a80d8481d0040d40c1c001d4071700d000800202214912007524110302c20151802c980c09401074604454442090503560100c040b00d80d01154800d180e414002200010340350f522480b24800d02401c2c90352861490310b0800c0642103000401c10200060042d00e6020080a500c0b41300342e40e905165185e00701c0490014003640c0e90203800c1148400c20384082d900c407041e0000002001410440da41d00c4d00030904154140b0703804c101c4608070007006000400c4c041450541d44000d070000c2c00b418070030500d010342800074001519035030485244c012a16002c03920b482c514065105850300040343c2c038034140071000125420a80380c0a60748209205002414281c0c00a544c0b51003207034140a1500b01d0700c03000089249503503501c1240340e507051020311007140350b0120f620384100d4929000c40b009603c1d489000d90a49016406 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 238956420 1250 238955170 238955183
    0xf15030a1a0f2d06030c03070b0d0507050406120203060102070509180601051f0c0c030203070902220612020d0609090c03170304050a02220617100212070804150f090b0105030a 77
    0x3c0d0b9600c6031441880250001e2008046641c0c540001c008641404c80c0d50b84080c12031240452084001c02050141e5a4084d403d40b078494581420315201800e40b00b0010090440180d001c000540c440e4020031040c0060180201201107500d0001e4003640e00d24a204404140c0780140030000415080210700e0344032104110700d056201c44c100c00c41c12555007200317100695841c12401d40020141c0c405200002c091300c036840000d40d03100c100200150250315024102a81c080e01c100007007090941c0003402c841d80d0500d40d04096a00c0700c40c095044042d054a40165039980e00d058a2002080000181b001c02c5074400e08145a05610342e0fa10414179000840d40509160044004100185000a4074101c14030095900c1c0707258282c0d007001c1a084500300d4005590895050079000c5501c03034104081c404a0f07928030320035460200020b07901c80c254a00500004180100000890104030385a000c07004030b00645681040880309207110107024060092068030410a51000840c050a01180e2a1440c641044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 238957670 1250 238956420 238956481
    0xf041e0c080d140316020717010203150906010207090f0f0e0f24070309032a050705030307150209010516080304060b0616020f010306090c0503041a0f15030a1a0f 71
    0xc214030040d00504180382140144180424140341140d207248d5105000300c00140c40c1c0c900445404c0001a8007446180300750300450400c20705070390000b00842521002c0d140071400c001201d50a0002c0c1242041c00541a0304040d5126001c9200042000110f0000d8049807000080540b2810458411141c40d80c0c000d826980000d2040d80690040f4401c6442440c165843c0078030740020b4601d00f40c1c09103e4910400c005207a480610100700004000381004401552818481e41d5440c15920b89846018594a80100c0c20482c01c0e8011410b030380700c500c5a40c50803540c050051622400c25402107a00b1a8100d10304000d0b00101d0401c0c1c0e05460f1011000b070a0f108403110241c00700403414881004140c1055191880802c0f400241d0050454a0845407035003034580c2454540f05044010076480040704112103802c00032902c0d03070600c9032130700028410301005045400c0b402080c100914100c001e082200600d080e11908074024082e288544950b068140c11601c07a81c6101c80300800d0a18004503104448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 238958920 1250 238957670 238957681
    0x106050a050a031b0f0b070c0503030f0403020f06070605090d020609010b0618130c0903020f0409020906090c0c06010605071103060609060f03010204080d0513060305010506030f041e0c080d1403 85
    0x101c01d00480c82c4c141c070030080d19095a1701d5404d03c2c41c1c5515003205448010104480c0100b141060444000e42802c4010310305144020118511f58011840b0207482103802280712806e40d100e072011103918a4202a0601c210b00e01408510f96905007540c8800040c031030070f000255003440605c140c01203100020b20b940d08d8200d20456400e094080c00d04a1a1310400c400e40d1400c0c849003510860000348010b07265000d141d842c6004109c1401e44c00c4480030300a905218010005aa42200d1154070050440320fa0380305444042803c0c41a0046600c600c0451050030000b00f015034000016142c014400c0e104010401d401d081810349036a0140e910641003500038002c201d091071711022400c0401400380005050594a08540d4a01007041c00884c0204400040341008400c49039031a202030034183c101403101c0d502d40b1000c6112031200500303030a8802025404201005030398581011741c078441c456110b580d49140d08245107003000510070b822045c81040c0c40c00c444c50f0301800380060709290300440d541c216501c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 238960170 1250 238958920 238958933
    0x601020a060e010209180a06060302090306040807030c0c030c0515130b0a0e0a03060f0605030615040914012423040207081201090204050418050d0e01020c0a170106050a050a03 77
    0x2c140c0184890354003405079000315220601781c82e43c21001d0004885050030614412021500306400031003c02d0300401c541c90594070001a042c6d081540f0005059907124181412289146412402442d800c0c462600000b4008030440c01c80580307008031001c2c4d81ca51602a0b03580054801c02c91204081100700d20104000700841c0050081c2c0c1e20b80c0d0401e0103500414900180090741107400c22111380c6c0e81c410100c05c024a00b8800c200c0074003c16130013030080341003110705504011128180036102e00d40701c000d42010440c0c58541d0441885400d4024001c0004046000e10034058950412010b10607900b0700003802c0030b48981a180b8208603030000404a0142403d1002950100e50f040e0350b2400100031200c2c4900c1b552007500e000303040070703940161102c4c01c0c41c041200fa0b030841126540ca0307003008240c4030007091000c5a51a800760490400700960420840143d00300400ca000040d40242c00ca83c000890321b00301101c0d00c12424801c1c00030000c00d07480e1010404459598010540c00468180e403d000080c1c070f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 238961420 1250 238960170 238960181
    0x9050d110f03040e0a0c02070806010b0d1104080d0809030301140f0a0807151101051005060d060510020a02010206180a08070c0b03040804090b030106061e050417010606170601020a06 80
    0x506001d84114014a421640c035690169101c0e00c0d808440008128401c07550b44200103e03800140b003d82006841c112915aa921041c01102541100000c48110b0b0080951100302d00751645e56800d40c80b966504405522040c0810401002c10040c80000d0b91440307001c001c8905907540c891031054407104440901036008411040c458025807800c1d00820381d242c0800040d0000e100c0c2c002d07844004180088000c04100825401100d140c2c1031005011003001c3c1c10f48841c098460680744141c4640d07100602e40040c1c1802d6102640003009030700d0b08031400b6800302c0c04a003858000c0e0204c4596858034600404040d518850480242d0450040800004c1c1118001c0c001e050207602c100e1281e03a01c0c2c01c01070b0314503030003a01c0c00c840654000408001e4006c00d40600c41208a00310000c216203841c090000c0c0c01a80e07281c40c01d540d8040e18000045c2c030340b8001d105503030180010021550042118900090003410079005200100301c00c0006c4100d0416882980c61040ba410380c058001c40195a440501030b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 238962670 1250 238961420 238961447
    0xb181608160c143304030807110a06110a23040308131512050a050906010b090604031a0121110103050703090807050601240e0f1c05010504060c0309050d 67
    0x610408081c1511410404011038200c910803000328010414901c0d1543e00a400c20190b00303102010070170001c2501320104641c4880141070881000c00e003803001504114002d04003c007010f1800020600d2024060080c1a00b202c15898004803080c4490004030b51079507030035408608402c1080284001074503100a4480008192081180c072500c82c1d44c1602054202d08070640020743c4800c0c40c003001d03501400b0340d64201e54800c408020300d0402d595419107076030341401071103603003100003030401e9007038a4810845d401035406c85e00e03401c401d41d48407100200044083c80b6864050314000701802107000c1007848070f1a081d603c4600d65000300307030f000010360103840024544814150380701c1406010520303140c000c0c06044d10030009068250305014981409200c070404840d280c955401045403002d4000d00510b49403402260310600300c0d22001c002071211142c10007508400e00d044141401044030542145020b10700c901e0040c0820076400c1070880850343d4101d00502140c2c41219944451030041d14102000d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 238963920 1250 238962670 238962683
    0x61a0f0a051b15060f030a120926010e0102090a03030309080904050c090901060f050406030e0102040b070f030207060507080f03061f050a08060913150b181608160c 72
    0x200c2c00d400300c10080b000c1d030209511640c208004188840454100c100e0f40032808980389039034000404042951110030401c010b00034030840580300d500074003541c4880b0003801c7e07440c85015807031604050f807025601780c086014401d41c28800000c1d01047c060080e80c698640c090521107180380b42d5141103010b03080c003080030340301400100580d0140780c03030718080c00c0e1041003502c031016034514600d0103005510700143d0140c2c04208000f803100c0c0000d035100c402c860456000d4036000c9030758056000618028415a030284c850344d80001034103010007004504d070003451800394081ea601640d8072107058600e0310402c440140690b05c06c000401660614002950f0000c6000e041c0100f045250b144480f15101d05c014400040340000c5860350019621000c001d6000b40309881483c5135061000b0b4485042910003c01400c481900036240740c50303103040c2d00807035200d44000c2000e001c1c01d0781c510f00142441c5081c2d030082020710741801840d04c00c038042c084841c003c3c3e402c1303c2010000180c40804036070302c1c941c0120807181c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 238965170 1250 238963920 238963927
    0xb0601140706050109091b0503030f0a02030c0717070f0b0f0a020c0405040605060f120309060313080304030c060b090405151506130e0106020d08040b0408070206130603061a0f0a05 79
    0xc19501e100f40c60180203c00c0000840c19018145a051382c0109007000501300340407003051015441c04825118891071030002d4603190b9002d41d000740d05600481d4184c41461040080c001841460420104107078442d8509031500d96849181c400000c0070180900241b01e00204084080c2c0c0300c40c1c5c4000d1804500d0780c070540b11840280300006040c0c1e00140ca0580c0c4041c2c40ba0148581803620305844c05480782c0032a141d03c2c4003441d0001060722030065101e9203116203004000680c5603003c5c00c5030013200c1540031080300da4900c0c0ad4500540500422401034448914008210b40130341040e000040c040c0b500400103040c10401b13800c42ca41000c070002e0140791007582c443c100c080c1c90f032207520262156000f01c44c9640800c50814242801d4408168082d20456121110f0101e2143d0406003ca40103034000b0000d024a0380c5904140d100c030b11611400035000030340000c02c010716011050b454819551641d80501115a80340b2903445006070315030003030309459810094000007082a900034a006051030a00c07504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 238966420 1250 238965170 238965173
    0x30e04021b010b0127050628031a0a051c06110c01020d0b09040f0b04030905130b010f08070203251202030705060709030c1403100f0903020c09040b06011407 69
    0x31041d4405510000c241e44800c0246904d680142205150b10351009055001ea49000c1da0440544054480c440c050360000031841e41051806880d1601c1c204103401000385030b5050040100140040c02c00301d41d9101c14082000c075189070450130030084a9000700240f1100c844a044100001202d1104494055a60341302e0700303041c60084003a00d0000c904200068a039010040c1b8003068131103004c54a4404c10240707041200080d280007580d8540794100244840303030398403840e09451031780c04e0b030300801c1e804264441080c2880c4416005030b00108403c0e03aa44468001c4000c040da001e010a85012016801c00d0100b0700100c0143e00e14480407050b43c1842100e000ca00d80c40b03c1c107030159023140c50801600009201414400204943c90304020689400d40910703155840d82185043c0314002c61004000c3c100101445660801c042d20031000400401c00c40c15030f11600c0e440c004c2285102c101e0150040104200c194500341d0341c547d200300d42109a8071402d47d41e00d07004441d101d0082c0303142d0b450714074140b000b1030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 238967670 1250 238966420 238966447
    0x114130504180611190f0c0209181006080303060d051f0204080610031109040f20010f180608130510060609090b1806040905030304060204090e031303030e0402 70
    0x300c407400d500140650100f42024010360f46401c8940c45441010498a200b2204101e45180080c820785000e036134007008031904803210105424081c2d1f12504a1082c0900c101d51003100400c01c0300c4100403114101d0300190103205544083c451100f15410510000e07401d4188100d16500c0c207031080d815110f902a4080004982c82583d4000c0c8541c160302003814010250100b0420b80c0080a070604405410310795507804541341c502411305801940b8803000302d401c0000c4a45040b0b0b001740c4c0128800320f620340c00882c079411819480320050001d69030400c0b8240303d50051990002d007402000703541c0c0d826414400c098600c24006428024080703440841c4001040c2d040c0300d1105104201e410100e441c0e03140080081c44985103410105059180620a503ca80e45124166140d00030111008a05980c3c030000540240524113016003180000030410041001039801401a0341100104020030340740d00704030301d69034000c41004020b006801581400070a010b40c3d412203403014020005841e01184c00740ca134 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 238968920 1250 238967670 238967681
    0x603050a060207030e01020f07050d03170403031b0905010c08070215030c0301050411030603030319110d02031014031b131404030e01050309030d021b030f070314030103020114130504 80
    0x29201da03039003c20101c0030590301c1501900754440c24401840541e1003400c00c1034440c106849440c0c810007002c0300781001c1502800c0c0400001c160960740d404149420308010700600f01c1c0720781c518940700e00300d0b0130700300440d005440004c1598010381d1510240c088030394503081c90741d1250310241d0740500300904d2400100c141100075031140c003600140a8076540b501081c40260f031410302000301482c809100700911501c00206aaa0018900c41c648200b0544504120001d00c1c502d00007820504002922500c07407007142d00154060090041e515001c1075a40399540700c03c1d002194440e5050300441030641d180d220114918036a14001066030b54070400311044e01d411240d100c00080c500b4041078040005141d0864042c0071203030000e080c03440c0756142117440a41c4034400d66409240700ca5010400d03070303060554102042918499102201c1e44c58100f130300405c0c001e40000000310000b0342c10301c2250102442c500300340da04813541a1500345074078454601041d41c541000a21407400c607045c2c00001180d50381c60184 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 238970170 1250 238968920 238968923
    0x50705030d1106070203030408180a05030d05070c0806090c01050703020111040311011b0c120804030c14090705070f080901050c0a0b0714040e06060f07150c0905031f0509010603050a 80
    0x2120640c042180b02c25051400c0100b11005540062040101007200e06040701c01c403520010300804d003110704000003002c0d074006810554061048a010003031060f0084000c00540e0b02452001c402a1754803620b09035a035100302c81e944031642221454001c01d50040d0040c0410b05e2280c0008035078031414032000481030300158011345480c2d4095001d0f0087e540c0211078006503c01845007416020200c1d220305000d289144540d081c011040c0c0c040d04148031070b95050b2000307035901c1600310180c10798542c051010401c404040c644204807070f03004039820b617019030212041603900111800b5403e040340c5429220781c020301001c0d41800000c101c2401e08003018440b4104943c13044040d40003905103404014089050700100c4980d41408220600c002c00c50548120f5000100b118000c1c0d40d4103000940c41114021544018010303003200f42c07120121046a0400304224249688840d645540d8004142e9216486070020126129212000d0758070116504000d030310135031040001ca5400e03a2039444c5403419060400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 238971420 1250 238970170 238970177
    0x70e22020f0423010908030324030309040908032502100b0604090c020a11041e0c050c0d0309020108061e010804020a05062a0708100b030a20090a02030907030609050705030d 76
    0x4103c6081d83c100410101421b0114001c3d4214500101c064042d1640c4941c641d480e00382c01e0581d404541ea040045450041c0050400c0c48070031514985541c20748c009a82043c402522005180c030248000e84d04807403403404c00d50081c07025400007042800103160b07010020750801000c0101050b040054000d001035038015500030a40c03466141000e4980308020404284501c0c18000e0030500040100b02e9103a140078040720001c0d00f26448502030f0740760310038142c54411901a0100301c0010617003640c451503059000783c07580146595400100900c03010000d000da0000365041903072880e00c0d440f07007800d5039006102030070305236005441d8400245150003900b6940c01e03448017242441c106981242d4104402c0f40e4810040043c2410001441d031148a038990b5280340741c5d034601c0c410f0091340d81040b8492803243c0010b0010400e02d03444cc1620401241d05500034020900840440c8042200b40708030391241c80040040c003480c5066a60740000b80008100030b40b081c0c41000c902103000e640030700808442c3c2c80c07a42c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 238972670 1250 238971420 238971479
    0x20d08070b070207050a0f060302030606070f0507170109020a030b04050f37030801030b0c090904140f07052107030501060b1c02070c0b1c05010806070e22020f04 71
    0xb072000307140442580003280a0300350350104002d5a0300150701d8500703841282c14050381703e03074400c80450b0300c0340120310010341840e00141c80001070180c04500c56059462000300140c040f49111442c509030f5a54540c02500400d00e9002000428035080715907400c03e109030243d07003e861a61682501d001c0c2c40d012180c0c4e188140c3c03960b00108131240c4000450100780b240702d07007101c03100c035072000b811071481444054081011080020350b00300d83d0700111556107030b00400c07240c0316051500b0034105540d07440856480d03d10890703000e440c1600d00060390360308980c0000c1c01e4404030343c206031003100000c02040800c0200d20030304801000060003809607501425092901035120144280d44090501400c0c40c0302c0580ca00c1040000c01180da6080c445081d120000b0a0940d41c6840c0c4042c00600c0c0d45000807008014504000883c00c1d0502240060203511582c2e03900001c40e0244042200c3d40c03240900c000224440c04800080e10361680d0050522607009030001030a02d0f58030520b032021345c2000c82e90100c02e1910354 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 238973920 1250 238972670 238972681
    0xb0f0702070515030a0b280905180c0105090111030408010b030d050a09051c14010b0909301303080304030206070807020c041a030d030515030c010f030504020d08070b 73
    0x1000721100408084460115004581031207075a41c0c4000340503076000303076100e446098040e103900401d01d620201407815105d0a4514140322180448035000e040840e03420140803502c940030500038800c00703d408201a120302482000151190341c400019203051005a1801000d6800d0900c0a84000c0880c0000480c00071078050405044c02d408460030401c2c010309100c0302c6007040d40107000300107a86045d1001300d00d4981c5a10502c400c00f455000003454002020039950000074107402c4125845010790b01c2c0142900c80910b610307110b101c400703210800100d030803035041403a40724082241000030308042454501140320603c0381000030300d5002a03690000001c280000c0507810401240c0c4042c09140008840c20142c81c000c0d100d10440280d1480369803903503803001900445003203d10180c000281203400d10440d03e480030b80035040403035680310211540d024580550a010a070000c1425050751601d182c0d28a00c9000e0380142000350090343c000c005c4146810000e00880010088607016482140c82132070003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 238975170 1250 238973920 238973923
    0x603080310050301140a0513121106070207050d02130f0203040b0f0601020102040501090303051c0f0c031407020a02011d040507031d0115050409031b2301060b03040b0a090b0f0702 79
    0x15444030f400b9a01d4500b50560034844c0c42070035038024030051000726041d141c48030720f5007080010000c0941013480e11a014200690012031800005080b001600ca60340d441039410790312100749102d0b0642108521a103140145030565000a1701c124407200085e080d08003401c1203040b03070421101161078035008400e2200b400411540168012001d20080d0b181c2414000003c203030070b0040c4002410310401195513940d1080c050400381d800510104200401e02c000304094014004604035040440d14000d000380018404065451084132990010300c042d20040e401180e11000c0f0380704289a803c814522080c10381d41e140145070080250340d90110b44000c230720b0780d00201351140c501ca1700c44507131412403402e41c80440e003145041201c3c03046400140203101410145c80c121200001035540c05000c829103000c00c90940110314101929440452800140c102000e080710040d0258a80c2c1c40301c00d02c0080c1c0095100d02c2880d40c042901000070806000aa941d0021100e0a560003241124880d0410603000d50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 238976420 1250 238975170 238975201
    0x207121208130507231e10170105150f071a0a090201022d0f2d060a110903030304152f07030e060406050703030c030b01050d0f060906030803 62
    0x10020301d0058209843e0b52901e994000c0c0384941d04003113521241c13482628505a039a0418014007030540402410540c5034400700b00041a0300501c145403031400e0014035440340b10722048488047d11040d06990a14003080540041000d01caa80d0000c100071003800311440b0700203001e00074410b40c00c40c1400e1031a50384d2100c00c564010500050300345800036000160381c1c002a4403030080400780c0c0c40d0702d024180d40c0450340c9a4040000300f00c030f00e00c24840340a01c0e9400000d014801d9245103000b03a075000c2c2c000400700d80000700701d03581c131034641d40f000b400314050b802180e2001c01204040755849107001c01d528042030958004880c01d03603d940d1240004154040680201c408507004ca100c2c8042e500710030003903040b5600139200500d44400c40072420500b01070007001c0c00c1d05030400050410f40c03120fa036080002e0995000590407000241010180034886012380100000404d058440c1c1d070070301040e008280002c05080e1103034100ca5072107290028130003080348284409540150520343e0740303160040c9804a600e8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 238977670 1250 238976420 238976431
    0x1302030319022b0503040b0a020405060703090302040f05270307060f0b15040501020a14011103010803031005090105010e040203190c0201020405010e0a0b0f0304170d09030318080414010207121208 86
    0x140c039a60040ca0310b0340070003103d50190780000c89a04035124000102c002b8080d0341c000d00e4000741d00081034070a060b0003881a4007128401c40e0140039a001565005c13050750000d40d00000304003644107200448180710f61182da9980c1d070341022641070801d02c0d00c4039002c1d904007040300e0103090394131003440385242007250066039403844051345035141502d00070000b90740c1d486501001c0c0400d500911280700b1500290001c0881100f5102826202c1d41c50304003141e01c0b507006841450303d595004074000381c1c50410f0203099040701c3c0c0584403c14141d11702010b110103944020800d445154140602080c16403c40c4030303108030700900782e000603113450524001401c07a41030740859910031005d00c4401c2020a03039040c111003000c8e000700111501e94443d440c1524080108101501102c1c00200d5400c024041d1540804507030350080d42d040c010261207480e240b81c0c0c10300c0d2510241c24107204110500030742c1e500c04601744d03420a06204681029548000c6621a001c480713400300c2e0f9044c1100603040445500c0284141c004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 238978920 1250 238977670 238977733
    0x14041a0f0c03010b0a0c050d0503010f1401080109050a14180f1c0c1403070b060901170a031b021305090d020f0316060227040608011103130203031902 66
    0x14103207112001524041442039542520000401c1c82a191054080c1d0280702da000003151402c0c000a80c0c050300d2030300240184d02c02c00151300c00010f00e441140c541c52007540b9040c0c66218469091004034005800024200c0402d03a45a54403002d0310118007440314440e010400300702440543d100f0006081041d2031903030047c1940030b07070248400c080396048100b00c02140c1d420203048451083ca816140b10344d02082c1e440c501c0c000070a085050281d01104144145001ca440d55540d81c2ca03100b840f940e0400ca50701003101c3c0c1d80100c000d100040e01170003200c00040e00040302002e0042241c1d00003000c03121401d8a009080d91118140950040b0420907510080034a0020308006283c100795147e0301d00425022403001004035440000384a041d41c11100001e40045070601c004040071341c5a10010400d610b01d074001c61503ca0001160001840b500320840e07420003c2600e5900c2e10351400d020f05012920503641400104070111049203944884000d042c615000307001031740380c03901c01030259070304c90b0f80c2e2030f040d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 238980170 1250 238978920 238978951
    0xb0418180507060311180913120905010e0a030521130801140105040905060406200a0201020909090127110613030c06050708070803070c0c0803130b04030804051314041a 74
    0x4200c0c0c2c0759001e50b1b101d00295000c004e55650314603808420107141e800030f0607803c42c48080b0b140950b0301181110540700c081e00d0383c200e070303650000074088081114440607000740c110742c900c40400b04140c0700043c680d00300c12070304a0034401d842e10741d96007864031540024881e81d034803a10302c00540b045001090051000701c3d0b0400681004bc2c5039143c84000081004005d160744030752a1b001000f0100f2240c64203049424800d8407440c130300901900030360200300d03181d00c03401c2e10900244074081d050103440e0400445540101c0490350b00c4bc070040280a207884c00701d980d2002d0200341284c80d111070014081044480700d000d8501480c6040c400b04181c03107900100c0400034100130030008250180100d03020300d0340c40750110790350740e440310b80c103c40f00014140c0040c24504962000201c07104c0020240c54603010180c44550860340d1841100228811440010f046440c280010003c92615004205102030200d5000c8cc6005854900c45007401080b030b030803129060310003580c0554079581710f019544100f030403c80201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 238981420 1250 238980170 238980187
    0x7030b060901121b150f1d01120b060705060a14070e03060f06031507031b091d09120705070e010e06010c020f150301080c030c0a0b0418180507060311 66
    0x43c0e08948809072944207007841a0b01c0c0320300070200c4c940042101503050600d03050b800e40001d1064035103000314000034440c400341e184000072102c80070b100b240d0140c5441c000010021202c0014121000b0749c650f00c070b0828401c80e80460003e12a180c4150340068000880550040b091146030001600305400c110841941e00d10544000a01d1600521800703407209183e0384400002c0d142114043c03203903804820034010300c0b4100750150050201c103c02c035050b80078965082442160802010701c200002c0c4d60443d14804c0c1c0c01c071101814150042c680c0401c2e18001405130750360440c15404114210b419901c610f44c10030204041c04030075805450503903804907981c14070400013049100340e010060b20030394041080c101180d07916224141880c8100c400b0540325a500e088094a90410034462030181c01400328441c0a0b190404103001910f01c1c40304098141070410301c070200d6414140140d02083e60741c6900143e440b0260040c0550928842d0000b8101c0ca410010001c0546442c080000c070b09003c14441c010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 238982670 1250 238981420 238981439
    0x607050a080a0b0d121d0108040f2f0406050405010605091005190905040c050705030f1303020a08010b040b01030b0f13020708040807030c0605040609050d0303060801020c07030b060901 81
    0x5044504a01c0e2100940d141d0780701d5140100034120426a00c9135082d200d40080044008038445110107545600d01c40340c61480d0100d58204920079514005130901001600045415040b1317680700f0b003d040c11210f03010444083c0c203458071658400c1e105000004515070094941801384801610064a092299515111001c1c055021320350810b4400d89840030004c0a841c8290140c0e50300341003529841408000040e4041c0c601201070003040d0045041c202c118800c03601800450301e525a21100641ca4071101110055858001a8050f00444601c00000016a96585010019189103000082e56902d440b0400040340e800103035440c18036040051134040d55880c3c040020b41104241d8211745444085000c0704020312580b1001400c5800109021841502c0024610b0660740b04080041301527460f824150340ca40114400c13400041c841440512450a020341d00242a602c0303810302044681d03c4500403405c0e0380141e06118099030000038200140004000d6050b040b01c000d9440e100303154103004584 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 238983920 1250 238982670 238982677
    0x1030516180e0c03070605070b09010e0c061305090c0408010b100e011818021902010e0c100c0c0b0c10060e130218090303060405060618090703060e01090c11060705 72
    0x10052907659980c2c101044051040149008000f000c0d40ca6207030300e901c40680300c3e4200d50802c4e190b1031a2100004c1300603005120f200c0f40030312440d0040c0078036400c140030444158000410240711907040080060661100d506103405616000c100648a03420000c0480c00c481d000006071784241d400d500c00c0d500d060b030814248921050207103089034016013010444800c000c047e44c480c06008045040b010010361003179010b02100010640c0c0040d28000c001022403e07280d000704840169003009503100c4040c94651a4115001a2818144407118145d00e81d8013203d4507547c082a101ca10014a5004013403040c0030b1000707040c100c44420003515040450222076440c008003d61303a8807028059800541d43d58410200c08124140e0319049117140c244000d039187e0b00b007a50390300d000e6410540451140c5c5080004d40b100c070031110b181380780c200010104102c03801d00c0c040d05038824987d60388800b2410200354082103000e04243e4801042c0500340c07602c020010851320179000c0045c1c10400034069550b80c8007045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 238985170 1250 238983920 238983959
    0x702120f0613060b1e101106100602060c040e150111010c230a02060c090409080a0906030605041b031e02070b042a170709060306050a052202090901020c01050c0301030516 75
    0x46e107046416022040d52000031240b40c081c560301c1034604001d11022002c400c007060310502e9081e60081e4503003440c8030030180500c2c01845007403012100052264000c05800e80e814000514211140c400540d1030b26003100e40050768200000e00302101c0e41042c500c21998100c4080c12094210324200030030030000d440724006040018085070001e0901259580e5801c020405a00030a90300d9880002c09006000c0c042c030351084001090030a07000150740e180034400c03148800358000e211004415034210490040000c0954200480ca03d54048207545080d4030150512501c036220030409030805090402242c002102c0f074071020a0035041c541c106211151000c011600110790340b00e002c10100500508020345500503000b414a040e41c0001448016003101e4001c0414120410441d242d5200c145000b03140244000780004124041000500306071408c2e80c1d0010312040010308144e464003440e429100d0560761020301000110050041c41014020181038013207010011040c6443c1caa400c9104101c45001e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 238986420 1250 238985170 238985179
    0x3020c070f060e040f0e070e0a0e03040f0315140c07020102010b09041a07091503051510140708040509090309010206180606060904150b2106060702120f0613060b1e 72
    0x10485c2030713040c05402c0740c001d240c0c0030f00684220540307500d01e1042914040b10700030802e90421004086010001c400c031019503140c0ca00f071080150a513207512100186400300e8200035a030342d08004008402103034046004050700b0030400d03034440403070000a095a2003843c10038450507040c0e00b1f01001030032112280f2520381800014031865600c4440a590300061644090640c4018582c44812aa4140d00041c4205c16008849010880400901000c940c00103907107000314110364440310b00040b940740900b02c2c00348134501c0329140035218404200e90303202c1594001c07515840401c00f40c40940c0c06200090340803c180c80140b80c14038002c00d10958400e0003a043c00d00516000a812502c0d840c1d582090810345651041d004e5805e41d510780c0392409a00c0307204035468420000c0f00f00e07001d1011010001c0e0107040e000300f20905002c000c2d0200103400c088000104141e102d145018540080f0900900e44240f03040b01c02c00103070a586080c4503060b01e850040481c864544000740c865106401d031317918814070314140c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 238987670 1250 238986420 238986431
    0x70e100311011e05030106090b03040210031508030c03030103031b0510050411040e0c091315050606280816050a080a021b070512010b03030304060b0411030703020c070f060e04 77
    0x180c50903404003d804407001000100c42c0c2449401000031030490354242c2c1c5115540b680c54805810b240001d5a0003540144405d5500d0030300761294015041c1520800842d06905594541175841d5500c0584c4203251604048010824160040310f541d40802d0801301490110405581e00350b02d482ea5007003446081a50754004c5402d0012800206100d49030280c410801c0c1d41901980a03aa64000444184140407801c0040c001800b102e0032585100e034058601e4040c0d620024041001c0c0078010b06190300700500340495000c41c000c180241d900d013001010003072001d01d60503130010034100004040b2111780b0300a80c0b0640f0081c0c0e200d011280e130a00303c2d180442c0d294656080c090b019110303564a403900040c10801600d10500c001c100001299811244001480b20301e074401c6003a0b80303c61940e10780c0b580041c00006c02040c0a13402180c0031800c000c100103081030319030303101d021240c0090303070078100196002c80c02c403062110820440001d031140203010f00150f40380000003400c0c1b80c2500013445c000d40d250b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 238988920 1250 238987670 238987703
    0xc081b010204030c08010e1e07092703170109092a030b0c0405040b09011a0a0c0804090b1806100c020d0803010608060307090509070603270c0503070e1003 68
    0x303505807005075501100035529103170355160381d60203450404000f0f0b2090142030880e00a000200b06014120003080000d003000f0383c0f40c4600d11000380841034000e10700d42e21040c00480070201810740d203000301e44a0307281c8031000742c031824240701007c0c0d05800020b030b02850051440c003c1458000d541c911100300d640480514600514a82d00841199000801140385641400990301240014106447d410b0b10100106200c071000c01410b440288543c065582c0200440d42c4041c82c410010300042c2d40c6403c2c14000440c165544c8860346d40681d111595499480c0408203c40c9400c0b080d00305000d00c0b4803001501c42c00c2510004080c0740170f52034800c00f0b104603039038081704648948044401c140d404c011200e03100e6230340b80005401c0b401c0485100d48039005294000c2a091150b100d018001c3c2c071918003c01e1440d0a1842c19402030051000003165854007288000e9002c1e5840c0160f1800c0d0301c24091030840c24a050f06242c9080c090b42c111010442e003420401c00c0344030790103a0400459030030440318030032501398 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 238990170 1250 238988920 238988923
    0x3140102160507080c060f070314190e1201090b1f052205010509010b03010b0f04151206080f0c1003060b030f01030b0f090c010309110303040905160c081b 68
    0x2203007580160010401407050511001061840454800c0026111a80008410040540305501c601504901d007400501c1c04030f44194180401c8050098260f441c104502d8100183c1400b15030300400003400388490312406082903038000c64243e1800c002400340303039103580c0c2d884160980203006001603448044c3c003030100906d1103403181c018a4050644482000b9000c0801c501c0450000001706240c24200000303401d0a06441590485d0102c055060440e400d0103410785ca180d026809590944005200220391a490040100041a11a25502a50040444c032034007503a202c5e03031005080c0d401c800d104151117070000c94420302410003214110345030442e68000750002c0403c0e03040302103914008003c014510b0340992031141a0b90003884444241c2d81e41c3c00a404510501320340e90303285034020051030405540207030814144544594405000f106016002c00d1031a0801e501240305242c5074030911805070702c0d81a4000c60440c0c10726000d12164035640711001079104100c600c412070f248501401c0d074403000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 238991420 1250 238990170 238990177
    0xb0606041517010b040602100f020706020301120308160906050d0f060e0907050303040f031b05131a03010902010509130f0c09080c030a021f03090602070807030807170103140102 78
    0x2003441084034038080e804801008680388000d405491102c24001241001c0e804081e02e0480301140e0041800b004003243c500c000d0800144000d03900c0d502408100700040319400070b180686802d0a02c0454090f260070001e19001001c0d06e103140f5022608e1112003141c0c0d100d01c902e000e4500d282002a903900710031090300002e0210700c161b0390286140c6034010078510035580354240100e07043d108407284c45442e40304041c0c41c0e03c42e43c800c144000708080070400c000f403110f0007030043e0700b034000c100341890302c0d0380742c000c5109003560540302d001d204d95994000034164140c0001840b0000305a0007004400c83c0c03075001900314824001d02d1031044802c0c0d5440a400f8409030088850001140d07020b01150b8280080034002440f80c0c06007895901400208a61604000030740e05c418135001420580041d44451400c0000c1040420503020141c440f911900400d000740000d1401c02c0c07040715415034507101ca040040000c64090a12800c03c03003c980325807001071581c180181074a820940e419481003030081502d0083c403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 238992670 1250 238991420 238991429
    0x218041a0915121006051021090203010e1213090209030303011e17030d0501061701061101090204020304150501050306130602090a081e01050108031303080903010b13020403050c04020901020a0b060604 88
    0x10804118440c00001360700944126081aa59056918640c0806440180d00710340307602d003803040c074803c80e10190011790021030500b40080e0000079030b019001200e604107411540000900b01002030401c0c029000502c01c480140316550045003800401c3c80000d40b42e10040c46502604030300b03640840002d1465003850001000c0400d0030181402240c4211512500300800924070503242400004540307010b0031444001d00c204101d4001c80340c8c2442026282c0c800d416222210666a641c1d5a8005803224402113006a024500024101c01b04a10f88003c2c2c0700140c026500a4110900380043c15a545000c0c0d0b180319031186000d6110040580403420018099000c40c0080c820108125200b00004c1d03071407845848584028030a176a01c5107510380da81d1050810101c460070a4940030000f15801c0380140540e00e600400105c0e0610764040080c0c48005404070074100303a07500060400807c00e0411454001d0442510154203104030b03640040d45920a408020f041712601000140199507031204807070180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 238993920 1250 238992670 238992673
    0x12010b03180313030317071709120409060311041b080a02070f03030f0c02010b0d03050c1002040303120b040b0112090c0e0a02040602070506040f1802040503010218041a091512 77
    0xd42c2c0800503411100f05501c001e801090203246080384203800f8061040c03207804141c80f4010703120080003540031040d030001e217004514020f075070010181c00c1150f0000c100130480002301046003030450a040c407000c03000070b882920452507c2040d03d02004641c61141d0051072909003201142d90302d0012001a1203444001030103001611000010150140d00101c5001e0080c032003004101000071081c0d0880c2e03c000030455010303041e00c0207072001034490002001d800bc0300009841c40105000c8030b880c1a0b80040c0c1040300841c40041c040b001d140700e035110300c4485210890b0244482200b200000e010100701c0240000c002d40c443d80c0e90b40038840800c64a0004141c0d0700120003e51401c901e02d00000d4010740034060040c000c4240004881c03401070145c80548a10340104a0a14948440080d4545a0405542c0d41c0c44c1c080c440004c0e41c1d0303000e1003c2d0015071184100c800c07100403c8801c10080f10520340c51002d0940102c0e07141600f80c1c660f02c502c168000400c03541c0341e02d00641400015842102c20703c41c00c406 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 238995170 1250 238993920 238993927
    0xf020c03030f0a1b11040b0303120c0928090207020415230a1805040f05070605040e0106030507230d05011203030b030303040503161a0702010b0306010501020312010b031803 76
    0xc419650700107104841140e920304c0c955043c0c5007099020020700c030030060440d00341460721030030314581030b48a6451240d0013030403039141c00134006505090314411103446081000105900080341400540d01c440e024488030b044032444410301c10104a41814001c6401c041c1d408110700c011500ca070b60081204926400c401d0710550340c2e0706800d030807500450044621000540c01c0c078400b81d00f0008040740640e400d2640581d150341e110007400004040042c001d5800c54001040d4001042d403e00c032240180540350340b05a40c4909002094501040c180e005404040c0740004000f4482c1e13000006080c141b001c89100c00c5c01c0e001c4030244480d00c0c080c0103a03000c005440c1400000340c0030407281d1007800302c1340309807024494840480209a22404215005417040d003041000c0ba9000302040b02c0046071340d128030804586e10300c1c598100840c2c09021a00980980c0d920150030f00349260802c07256004120034030046280c025244445c0042c0310040c0718500d880c0d0004008211180685107049125440d014112500d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 238996420 1250 238995170 238995187
    0x7211e08250210030e0604060e010b060d020a0305060108010e0403030903121d010e0d12090302150f040b010503060c1b030415090f0524030604090c0f061e020d0f020c0303 75
    0x850341c4160034120301c284100845020a14080c0c00f9440076004004003808842d80c3e00d4662401400000268110070f5513a04901e18140d6200c0001e0012042ea030301b001038071200d4215015040340d038054000d5062102e604010070490400ba103515a225a0525001c2401c0100e4030f0162155070b0389110780101e40c0d003400e451503520140b405255041140000c0244089044603034115241c42081201c40c0008160310148400060309400c030b421401d21070f1040b00c8040004104034641c3c100c00b52420b9008210100601c4144641c2c0c2e12510f016040850140c21141401d00408610707100d009044555841c5070300d690784042c8424025240141000404440803900300c4c1e41c010501c8941c0d0080141203603684501140e9800c0c03000842454174010406400103035a410b03078041c86600014000c50b0f0041c3c46e1000a4005000d100100000b003004221540490341030103005040d800d040c119152801011445d02c400040d400108503d4550803824180006041c4c0e00c41241001c1459068a0f050710000a0520 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 238997670 1250 238996420 238996477
    0x210417091801142106070f0c05010c0806103608100618110f03091009080a090b180f010207090207050c1201020c0a020609010909090507211e08 63
    0x3082e244120f5400c8000c21040104d0050301150000104141e40180005120305018226550510f1910704003043c084002d95592420740b043c5c6c1c6400d200251071102400b9240c10310100c000c2d2102c102e41040445440010081d0800c80c40031641100b55102d03d4080c1000103948483c44009040075000341c2e0601820131511002800345840342c170030710101c600c0c00c04482030004c0c45003a010b064240c1c0054505500c8043c040d030b19401c040c14030340c510300807000146c07040365080c42000f8945124801c02c3d603d40b1403110000e8000101a40403c16008041100c00801d041015041d00c5003c42100c07841969413050740103c0c50440160048400c09200161031014868001050f0484400c01c071051310700030900300301c0c6034281d01501c2000502c0d40c3c040c03401c02006241010107444000410302d0000a15551065803c0030b4075075042042e626a040140140591b24505d000d141481c0e02158511751684407540e00d10340803070000805901d03015850000102000707003880807aa070303810455942c80c074403204040401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 238998920 1250 238997670 238997699
    0x228142a0402251e0c0b0d020c0303070906020f030f0d021e0a11060601050c0a0b0a150e0f060f060313051f1b1e0503090c0a0b210417091801 62
    0x155540240120030030343e490809403250845950007416800441e02e0400406d001c1e410030340c40c030f40702c0a40a10046c6418102000a14869581d46d074030585454500b81019003802072190764503d1170741003040400800ea814100b142c1c0801f00001d8016500c3d50351188010b080741d20515010785844000656040660740661002403600d07425040d0b4009071614401518a4426585196915005040700d503003c9050204900d5010082d030b04c012952400e8610b56040f40c52854004140080c444401e0041071580c1c2818039500101c1596800743c40e41c031010003e500d0307002c0101403140198090402d0010000300b0722000d150120584089610303006003019140c0900500c54842d200c048042c003141d0a4a485043c8440080340c61a518100e800d840940445541c3c2c402000c81c0514800c1c1001ba007510b803143e502c0d000040813132050603a02e810200391082c12540710a50405511520303082440f0100340310721034000c100c1341c1110402d50740d40b08103008214001c0c842c8031841403600d514400041d2a00d89079900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 239000170 1250 238998920 238998923
    0xf0c080a06060e0f0103050a09120f08130314070312090b0a050901050708010603111c1401120b0f0a0b090a050108010f0e0601050d030228142a040225 66
    0x24080642c4a01c0b00312542c956100b2203943c40b0310380d5802c0c0d209a5000398070041d041070445502054810a0b500d683d230004403400304580001b844508111005540501407603000070700840b07260404140e54034006c240780f048203000014544005580d00425000c1d2050b1240344510110a11040e10681860138050754101c4600d80214140800503030b0494042c4603261207004152618909030342060f00803401011140030a12490701c0070440c03807885090074036044c0c0c0340400603240803451119040c21411640d0301030b4860300d0044114401c1600003135a400710769a01c141c0c41c0c0c2859103250307200c40060b40a0300205291030b410828403c20700c1901102500300354140c400c00c400030702c0f450041012070b004481070100481144e0300441d0050040303150442860060901030702c11184450f017015040c510411400d14080c00d9056081aa0410840103451384840440c20360050001c0c0f20704550002d804040030617003145204189c0710010b2a80d900c03a81511144c510000c04101e00505603404401c1c0c1030b1190a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 239001420 1250 239000170 239000191
    0x30204030614061806130e0c120712060b01031112040b011a040e0c07080d0911040e0c0d050f0d0503010513020306060a0513030b070f0801090203060607020f040f0c08 73
    0xb41c6001440c0c030030352440c020f43d0f01030109076071000c142c00003501e5204054240d1794000c125044241c000c56040c0070f68440c00203540060006800000c0401c611082584034041450b00816001c010142c0d01030502039000b0340062010a04044c8480101c005010308681d44c1340c0c24401203100350001e98403072402c91146214010011041e6200c002d80458a82c0d0980d2000003484100810301c1036038507060240740c21510a8492900700001541c803001e00390000b840c0603000c0e0340e5aa1400c000c0c04001805841464416076003048042aaa024203071100d040b0f40400340030f240c0f03030200c1c0010000c041000c22030303451000060b1010501d48101c01001d41d4428400d0358425102d040b44103105584502c03c0328011007004040c1481d046070505d00307031000e1f0043c0e000f40461140035880007001c610a0300c07480d071044081e0703960308400c0c0080d054003602c1c1d01d0040e0450909035206104102d5140c5030601200c0d03440e501280d00007080c0c0c12403030005014044115141001c1402c042d4201c10b00380d080007045005201c00e4a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 239002670 1250 239001420 239001431
    0x1506010e0d03180e0414190206040e0403020c1009050f0616030c240c020d0905090c0708070c090207020a08010911120a0606060f030605010c0503090909030c010c0302040306 76
    0x100454005401040555106081460250001c1e006030680410309000e102c5400b11980d40380005486202e0442c1d00395070440445019640707002d401c0c03244040c1e1807000c003c0311142e000f02d5008240c1d64081c5000d40301242c209400417505041c02000401500c0c00014103c80c0c0301480580001d043c81c403903208480c010309040c8001603081ca00101612200c11184180c90070f2092230f40c4007240e80d1224101e081d100040c031710210b041e104440700d85e0403000344d2180310081a1004212030007490803207401034050400505010500c0f075551090071103074111300344a01042d1250781a013444110780c0700b00c41000301400d000a00005001080350040c0103000d00849081096a95a0b0360381d600b40c174106c0300020300da0100038180b040076180000100816503030480840e840701400b0f41d00c4004841064000901040805103410b09041c1c0c5400b8040142c682813134103007020340099490968900070500c6680c8a88480d1001440d0200c04000356040d800707000c00207220340c64800314050000d50103400141d9000741840b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 239003920 1250 239002670 239002681
    0x51504060509040218250903032d030c030e01090c2108090d0c050301021606050a060602031c02121618060f030b0102011b030b030709180b04050a080c15 67
    0x2c0c1d003410b100e10b401401c042c0300c0034906000d410850074001d0170036034100100141e0320781512100400d103414104076260b079000d040c11801c006d0100395241c03281c0a1181108070381c7d100200301002c007006008600c2e040115200d4400c1c0381c15406030504007140d030b21561902d2113080038060b6a64101086400201c440407400020702d4100103440f803006000b404801c403c0011700000d003001480708000d03a0140b101d15814940f00d40009007640d00101e20440d1014609203c0810300105115503500001000c5080100d1481c180020351030380903840503240c0b4900712140307241104005130101e409400f8020541643d030300d00650250410000083c140d00054240e120495126105003a408150f40164551103030300c0d0302c071000880140602c1c3c5c581a04654942c81c6440e800301c5103110111101e40c19440219403001148141441d10303405030300484046040100b41c08441100002d40c0070400e40000d5604041c0c0c0d11403c18a00d00918540300070000d440014286001c3c00d004915050303c500300c4545100c25843d031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 239005170 1250 239003920 239003929
    0x5090a050f070f020a02040908030a050c0c0a08030a020d18032c0906240703121418160303120c0906020601090c0e030f0c0307060c0b1512010515040605 67
    0x1100d5164064003401c0104104034040c034945244042c40c1e00c1103603d000456800315064035410041158250360110078402e030302c1c04078090325610407002240c19060402190019a07140b1220201800b200e100001155040300c09804950704540c14032410300c180300c188055481e180002007416000550f5100044805000ea5200720402d411200302e0390200903031910400c100000c4c0944000d42c0224040c1103030b0710850f2403c005c2c0c0088500301243e01d07258035046c180500744001045000c803c0c0c1d0310b0445103521503200d201c0d13501c1c1c0007100c000700e0b0543c0c0031002c803140b4900b0600207e00311580150001c000101035020300e110705e251300107540902c60b03503400d04d100340c903001d02c14000e031400341c0c2004005201d40450307540488a118110324001c04603102c0d003004681007042405118001d0b421008079070b101030804015010003032170949400c1e5042e84840e121a46801005490405600074044500090741da40e4501051483d001c1d4000b0407181c00c2910700158a500c2c0303044400e0050341400300c0040c032881e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 239006420 1250 239005170 239005181
    0x60222140904060b0d05010c09060e01230a02030708220902070506010b0f0915040303110706050a0315051905191a0d1b021005060d020d0311010f02120105090a 70
    0xd480304010303442c0e035910500a065890005904421807001c01c0c00407800c00d00034090ba04034280c441304911400c00000408802400c0b4426051101c0b03140b10f070040d494070034450f05803c03020280e8a40c541800b004d04070704511a41501510301d00012982c600c000c04400000480c81150603910f03000b45940320b100c4420790040200140041e04154010032a01c49100000c2c103488682c10240c5103804508000a04251426041d505007180017040503c1019042030301d10003541101d800404880c0c3c80e1210040c2640305694480e030805032074001424007980d002c0c0300d0502410006142d00000c000d208500c000c0912240302e641d00c0381c800c085080e903a203035440d21150159828807000a9500c100900d80074210f074080b20344100b800e5990011082104550340b241e144148907540034185c1c3c0e1480c015000c050320006022180b00b00308030002c0d5070040e903600c8500c02100350f05040001694038003032601c034010300c140030800c1c2147c0c0c000505242d12400d18120641a100215031a40250311800b180c5401c030b40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 239007670 1250 239006420 239006459
    0x180c120206130b04291903061205060a1d0a15021306020c03100b03070b0c1e25060806011d0306090a0318030b01120c350a020907031107060222 63
    0x41d4200003001140071051000d5500000e9070501003000381c0d03690100084027006500035112a0440410312802001a000f21501e121001d0f12155650300f1010080d134840007041c038001c0c44a4911506025081c03296010703111000000d48250003800d1355244083e40301c1e18032071403891103030040906108100240788a64841e00c0720240003007000504040e842e1803554000540c00055100d04840d407000d0399403248200c4001e840c064040c21540d240200d000400800902e000e03c0950301c402d03070510410340c1c440da02030360001091a00750344400f40d0600c40782d0004070389403409426001e00010003901034000110b002d0b5580c40307a0b4640306003120000619a0b40d500601008081d42513007001000a02c90700060031660600a10740702c0243d03070341c9a182e06500d05007045210b540603e06100754070014a07000007110404144c801520590300264001340280400810300c0b814990f840050030080182141583e000070390045046580740410018000c400c00d00800e002c51080120b0404103c001076500392400c1c58 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 239008920 1250 239007670 239007749
    0x30c021501031203110405121e0607080403081e0403090503100501051c05070e0106080103020a050d0f020603070318080c0606010c05070e06060706050a06030204180c120206130b04 79
    0x1a19107002c110050085d18a11042070341043c480810b055854040581144600f80000d00300c2c1707254222006002d03206840149102d80001e003c00801c41d402c2403009501550501d019403035a900e22100034401c2d02c00350352031001c0032040d50400003003641002c030a0707068072421011150180b4921441030103807002401140c1e00910900c140780c40626029400c8800c00d440fa20640358400e0b240c00311244000030992040b00050324250042056040c045800d0001e4030341581d0002000e046522942141c504142000b4090040080004d204a03c2503220712103101148004c841c5182580c109001d5540101d956a1850301800e40401c07903543c0210b8141640d1070f0700c00c3c0a052164500210744240300401481b054000750100803035000035000c1c2c4100e40c400c0004010000f0114154010b20040703804001c00014001c9402d80100e01081c6401e0034401201c40740d040794151040c4c9840440d40703501554080080242002c60003080140c14040034200f80c40c0c5d100040100486000e10400390440d62100c800e400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 239010170 1250 239008920 239008943
    0x601230c10050a062702040b0d0501180b0607330f0f05060904080304032a03120c170c0f03071d0904080403080315100e0301050f040c0510020a060c030c02150103 71
    0x124081c60b4608250000005c0c401418242d699000f56070590100d0800f01c4880c1d034950041c41000082d1101071301c07005403504100400c100c2c517404521248500c84c07021340203480c0c04a9034240c0310181d10b41d01110b08910a00c01e41c10445510102d000341c2244e400032041c035404d000301408288814840c40b03102c0c45004226001c5915903840e2890650310141c019000c20001a92104c1842140407060410f18148080e09807614040d040007440e08108140010069003401400b14220b40d0000400a0b0312150401c00080f54685014000451082c00740340c15030f020700841046007881d00701284288800b0710f07400716070f01c1034810010808a04801c580080180300240824004100381c140a1540070428810f00c62801c1101030000d903098400d0006c290000c3c410a800320a00d080a00407a50030400380c02c40702c600340c201540e075880c9000c02d070b0141c1c1c2e00880700000d021818910810030207015a400c52000c101c440711500000300a012451072000151003109100200150f0000c102c40c1200d8208061580 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 239011420 1250 239010170 239010209
    0x40807091415090c070512190207060e010e01090801110c120901080a020a030e060405030a030f1104050405040813080303040c080a030f030b0d080c160602030f030601230c10050a06 79
    0x240102501300c11001c3c400380019000900c017040f00214146445205684074520052240c0da4104448020421500704230740070000e03586c21040400c0c11034000d007012542c1101c1e80c40102d440300015409008a50701302580398025801020007010a40d4805081d03622204545140340300c24403512044500081001c00021883c49599010301000825458040381c840144413001c1d160020688040d60300f0b400018803100d0054051150308841d01140d034003489002842484012140214400c2d45d0045443e580014100140314084891500081c12000001034031803040301e59030342089404490002204801140c04203000800c1d40005038907a072441c81403000d01304210080c1000b0702d1204d401c501d40b80b9001c00003512190140c610403105c0303001407200282042c4481038008a9038054420f5400801c501d100c1c1c280c4002c1266030011003030802840011030b40046044088074241c9076513140d403020420341030800003c251600941c40c1201c0510182d162403007040100d400b50702c21a044111425507822 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 239012670 1250 239011420 239011429
    0x30c0c04020304240510270207050f0304030c060906030212061504080a050f0111030f0c1608040e071206050a171002030f01080f0105160c1403040807091415 69
    0x69201e40300e910000610994004c040c0e401807445107034120100d889904128003000714011000c014444265000c044008600e02e598414402210208200d600000e0880c244802000000b519005000880e070ba599968100030040c100c550141400241d20b550002600d240b090080d101c10719405140702d910381d1644002c0051022a024245190711414800003502c56420b0000c1003a40f8020805006c4c1007aa00180508560400c0958000d010050041c0101c1c044c110b840250300140039881a9a20100301100c1c084102013030b50002d00080f40001c010a2079040e007000071b8003405041d1554040103140402d0b6400703440c0c083c002c0940140398008200410354211103c20f41250401d8181e03a5101c45c540c20030401e03a07204562401000d560b010040024110070881c80c181c0c4071100000300010306050b560300d150103518125031010440b00c0405002802603078400c0c01c0c001d00e001001c4995030795940300d0702620b8042903c5a009a00d203091400c12940c221520300034071030410139012080d401c10703280400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 239013920 1250 239012670 239012677
    0xa09081216050a0203010213030b09010507050702090703180309061206081b060915070203060a02030903040e0c1209060106110a020d02010503180d030f0c111f0e1c020c03030c0c0402 80
    0x42d0b4091050614500c09a1001c0c401007a152200c1c03920081c03074038154180b8211142c00600300c03100d80d88c901820490f410303510806032442c0590450740302d541c60712400b41c01c40103800503e050225800c8a410014201500b10b0603d6040b580191118140014030010500c00c9900714410107850340c0100030411a8445201000d41081c0c0f0000c1149051030b410801282d40b002e1301004046200c0c8000550200358501003001a6012020700019403851405644043d00c90040d8071840d207038001864081000d510810040d98144560078441d0301162400203915036a40400b0701c00c42011030950903d2022050000c10314207241900a0200181104107600444455000034010ba01d0707821130010b1140443d80a1008840894095a0100f01104c44850350380031a4000c90140c0140700300c090420701421408203a181c05455402850964021f0340e0300120040d1503503d040710828010005074044241e03401e0132408503004641d085800c840c24180505541b8814500b11011039800240d1610765072400345c004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 239015170 1250 239013920 239013923
    0x33409090c1220070620070c05150c0a03020c010801140603010e0907030807030c0201080105060c060a0f022203170703120504050a0c08150a02090d0615050a08030a09081216 76
    0x5010801d03c03000d150301503402a071400c0700c10b192102c2001d122001d11454500000b0100c098040c50040c980c1d407030341403c1e101e03071007400e02500c08030b400e00082403000d1007603820428242c415695016200d00e030003925016030500060100341c1040004c24451503501455003140300240034103103140d0a05c0b003004c1c3c0c2d8504c01480c448140c450340101100141c8040068000e0500c04d8451154500c0b80e032002520702c44050300460702603a01480244c061400002d80c1d0f94102891356400101501c004640d00040d03c25403000340e43c201e241c55010b000000450f05040216400f0328104507608420750342d82d01c0c86201d8150003800052000d140803911464a074000c40c0c00c00e100e5011244424500c0d0740c0c020360050103071301405ca550402c00b11050340340f00302c9200b42c6d40300300414800c40c90084007000050803154004000741c60940c0e210100c450601a05410308060100240545c499640d1800895542d80c00031681a0014104010004007003400144001e6000040c034200f40c24440d85004000071458500d50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 239016420 1250 239015170 239015201
    0x20705010615050913150303050c0c0603070e0f030a080c03040608060f1f0509041506020c1f030902010c0209040c051504051c150507080a2004060302033409090c12 72
    0x98051b91202c00d19980c00c0114441d0325080e4417a55074030816401c28491720b500c280106401c0040000c10b6074401e4034105184402c40e81c00c138041406a010915103000924001c225020001d101c50410034000041e00c02c0719500c1d519030300d4a81d503c0342840500760465050703179040004030500c98100c41401407016003c100b24079100b4100906c40002074242c1d001d80010102000b058031043c4129a814400c1031029641602c03803240c2e00164124161868410030041c800301135581c013401045a11a2828142041e0010f00340c007090306050415002c40e1600b4070545101c0d416060540c00540c03441d0302038400b00c4400030640c0d00c10344001100d440401d0702c030340421030350b02c5014802802e800c5e04512902d4040c1c0040d41d0703078203120702e000d0400b54102e9580407600094607910158100924030300608550030b070b0b003c915002d82c0300d4071208815440703120f1704d8140c0070340e01c030440100c005820f035401c0485810307a0441c3d84d9540641d69440884040b030b2042c10750000010040a00b9012110b120b401801140d0728150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 239017670 1250 239016420 239016431
    0x150903110402030c1c020301090b030303070206041e29010e1e190f090209070c051b010219060903081e0f04022107050307211101140a03020705010615050913 69
    0x60469040d5170080b9000401140e000c40184200310051040780e18a6000740d004515600b0301c41c6011b9a5814010001015800241400c1d4040c001c0c1e401d4a21050303501c8550307400000f495280c284c62543e086002020001c211300000100e50740342d00105401007100c10105d001c2c1e4401d90b14900702618004205001a0b801c5500484214009104640c008800072600240b400e000c1d10400101701005004001003101d100e01c1c00d0301181c0301143d00c1d51141c0000b504040c8101d8908010303410001d04c10301c100520b0301440601401e010f10754003c801282d20a5407485010307900c2c1c015102d0034843d04014803045440940c00680e200020703807146900540018260b00b0701c0f04180350140c80d403941c650300c2c0e0859030704102c13800c11076410100303c5540036003e88990205254072030701d41a6090544014094044020181190360a901500a550100c06110305007581e03801d4100c8040c0284d400310301c0032500c0d5880c0000c000741d40903168000c02c41c1125542c0d0707001d00d480482400c202500c01200c0d01c0504807965178 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 239018920 1250 239017670 239017687
    0x1b03020f1201140117061e0f0607050303090c1806010c0f0204050a0e1204054b010f0f02060604021305031504050d0207080709020a030e06010f150903110402030c 71
    0x1002590b0082100d10202464815500001480c406920300498450b030084000e0001c00da4408460000c6050404041d00c00c9a02800005802602d1f08030f140e500000001114014400c01100542c400c09048040700d0540328617605200742100d00e0300030302c0e0b01c0c41034800100f9890361240700b540d041030340125004040c1d2419500040c0031203005580400c469990340340201104041841601400f048251840381070a16150120350b032200320200000340015010200c40640718000200c441741c04140c6070113603801403602140150000d0841d0100d0100b04070b00307a22015140304009040d8200783c03c0d13020f4412921a842840081e40040c4001031004101c00d03c0411a9141000703600700702d40f1041816051801c02e41006401c10310644c10401c2150040c080900882800160300000c03a2280840142e4a10000c1d100314010b1607003500e5a201409141d0001413480740b101400811348400500303540c08400d0ba1b003010b9507011300d240f000030200c500e0b54424481a14040d409158001c5101c1101d91502015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 239020170 1250 239018920 239018947
    0x1a0421120c021c08010503150103050a240f141807090b0607050f06010303030e06070f2f0609060705130504090318060c200d0209041113021b011b03020f 67
    0xf201c000100040010004012520b81005014038600ba200301501d101d50641e22000d0b202c2080540180000c00f034046012000f40c500300c070980b9918100c95041202040c8902c900c000b42490750000000d000190000c10510071030801110400300c2001c004044072450405090050410071400680c0620140000d9001c40c2003800380e00d900c604c200c00a008030750304520b806021941c203000101c0b1540d01c032004201e00d05070807030036000c0c0030010360400d403c3c2040a0221941c0c20206d00c000c080390100c50b585c141c209420000340c468040c19015040d244c0554071554125840e0003820136001003096103400410890805505c07a818450183c600f0198000340043d9406012141d5880200003840d401986403d00542e400b0310070104081420b601814030283d0001001c4074242d08010744500002004a020003422040140780c0050140604a210103003110700c0000b5000403169100442021000e001681070601c9840c1d0b40480c400b0342030038843e400800840c000e42020400d0b10303a8400400c203254a2310320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 239021420 1250 239020170 239020213
    0xc09162102070b0108060c040305150a27031403100b090d0c0f061115150a031202160503010b0604030f030e03010513030f09052b1a0421120c02 63
    0xb64105280e0303514146200746801b01c000e0120211010600082c40060b201180c042c0201100c0d070b0b044402512503030340c00b10003420b4080001d40306581518200d28000d046808001409010b0340301d00801804c40381325200d0520003111054050002d4a40c14000c0e00d600102400c030245000d048000070100d01c0e43d40001e11481500f0100c00701039410020000c80750700007004510909200040c000e040d0034040d01013001000034003c0c009030709411600d40a01d482e81d011480066401c903a8182588003100d00194a604007440c09680112090300045114101409003403081036024107000c1c5003501e151280209402035900880410104071001c82580d40c0034040c0f6405119282c0c1000e880f00d0b014034020b03200c0c01c1c078401e014051081c1c0020400980c0c0d0351031488450509502c0201824503031154258460046507a0020507074000074a041180c1c0103603101545c402c510504100014003042d00b4281079a04110815074000b44420108a069035002e400c03108001c60030703004803503108640000d164030024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 239022670 1250 239021420 239021423
    0x30b042018060a02150903040b040b030603100903051308070311010e010c1a0105180f04080f120a0e01060e040807110a05130c0306120f060203100506040905010303020c0916210207 79
    0xd1010015001c103811034175000d50050801002585054980a101d00c840e0040b807182c074069080200025000fa02d0521200c0c8007090051020000c0170018074014010360884030303480094540120010810b41000540402640d4100e041d0310103041c514401190801000b108541c1040400c0c0e419000084011451910a01010600304071540c1010305208404c00390f08103803404803038007209105041c0c9018045542040d00180c0d156952080d030b555a002c144112801c59510720000000c1062802e0349a000c640c9030a94603000340b0030300d035444003070709590340c5c00742d90280000c401000340100140200818001181001d000d8030320090365000021101641280c1da50070076038076a808402c01d65854840d0101500c0b2503481d0549184554948903c00c40050400414042d8000080348000c5c50142010005145c01002e25070355a4498103110080d240078031048015114501d40d0302c00500d014600c1c644900d5100804c1c0022044400b011154a0303900c00380308034000030548910f50031840350b000400042c2d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 239023920 1250 239022670 239022673
    0x605060a030506030d030203070804033005060a12030207060c061103090105040b0702190f1407030c0e13080906181302070c05060c0d08070207050d12030b042018060a02 74
    0x149403c5040c14200043c01504000f01803041040001d050342200211390410713090700e807600c840801e944030100134261001606002c82c00e80b00c01d80500c05101d4100610403201a11400100c6541d45a0705250a1a500c00203000d80c10441d000d0187c5845420345100c982e0007184049041c1c406260f0f0750340f281c6c0c815100a804d5946603420081840988010103030050380c544010440e140c040d6030407407404154402c00610828541c07070104c0a000c3c6103440c83d050200c0c00782c10744000a50301e1800350100880380c03190000107a60303040040c0c45088440030546d0750310f40040306240341155440030045680e01c5446e1030f18101c0000800c2000070380312400c1d0b2600988040e42c00503610500c604000c2e48140c0c1960003203100b10404c200d412905080491903a09480803802d00c00d0301030700c0d007030011303800c0c68030a410958104400d40401410300c00980021800701e00c072a1400c0040d00c41c60024041035980180140303140018004040040300c00181c01003001000a81483c101e2203034038400520386600c00805500103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 239025170 1250 239023920 239023931
    0x15090f012c280e0703050610080303071b06050406021e09060d0c110d03060e01050904050c01261003051e0a111309140607030608100f0605060a03 64
    0x2000c0119208441d121080040c601400d10007142540441078001c06000c89041508000502540005008503400c10b03481c5043c062000c841c0200d42e0b031201180f1003501c09119400200c1d81d0302e8142c0502d0740c29600404069031460381e40170f030159060101070f600215034403034007070031000421054480d5034091407081d103015984030601c0380446c1642d11120300107039211804006d0a4444d070348400c1120b00d407070b41e0410046008000c8c002e05880441800c9512100380c0a081c415200c3c0c641e0683c00981a40c40c0003200d081c480e6291014461510000c940c001c1655004002e480b00355130151035010111070014504159480c6c2621140c074002005555100d1541c100e03020500c20860705006403921001c950720303524030602c50700c070519581c2d1180d0b44c0003800e5205583e401080e152207505401c107003919840c5091000500c20b141006082c0d407000c50800c482d00510010803821482801020100d800c40e40003016081d0002000030700400480341c0c2c0f6404d1f1507445034001002e031181000381c040c03000c6640300000c0c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 239026420 1250 239025170 239025179
    0x1305010c11010f0b010e0d0512041202090a110307231303050705010c0807060f0f1e050610021f060f0611060f040c170a150b0a0504050c1215090f01 65
    0x80d03e42c0140b108400b14203105075601c0c02d90340903002a48100781110103000c1d4030703040d0411b14100303c070795800481d20030000100030909210380f00d03000d06018402da8080c90f407613540d00404012101c0700040c3c0c0394041c03010004a104180301305905150a0711000c98601c030324451a50f00c0a041d40003c00d03804002025140410921005025980080c503080c00c2c40c02c40e55829903200d00191140d51304c010300e81c96440140d80c00002080c1d2107000c3c3c000e04240c0420841c1c03540a000c510710050364261034440e50038100040c132582042c180001e030101894005011603241c000281c110b00c0a030841188509a0f00c82000500c81c25880c0c00f40020000e540360301607000043e40c2e0240c18803100510070084440604e0600000a11541041c0b08488500050301c00e606020b111450514080000c098440010110345070503c80550740440381402d000c46998104070b41c0c900921082e18400c41341c0080301c120078004042029119400c90383c2c0401c203445810105003540001840c4400b00303541a200c040b82c1c1000500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 239027670 1250 239026420 239026423
    0xf0a060e12060601050301030f050304050303040609050f0d021f11030d0603120e0d0206030c090d0506070e010e1e061606051008011e1a030a05030304020315010e0f1305010c11 77
    0x1000c4a0030102a008503e0720318006445844103101c000d003450508046c5c102448130500646014100040c16a60b072250f44540003000045c035800f442d48101c060610070300d02450483e010544095024060711041251303801c2404590400c03060707030403d02120f642d10b03031903681c0148001c00a088884100280c1c55040d402c01b4032007070803007084100074040c202c1554000342d500c0c0400a0285070b41103c0d030541c0d075520b20180303d045008241c0c035560800300528030402000804500907105a28590703e82001850300001111a070740c03001032540d0044040941000410704000d40010f440501030075080c40c010041003114015109000203640980d911000e010700c40d1030407414a0700510401c0024020307000d80d203600b171007014620021051815510742420340d84076818140c1c00b1341d07180d0003003d60f40c0140003400c00548030f50003150120310038020804080c958000e8046060705031392a0080c0180315584013002d084a01401404410001281c0285280003030000d0007492900c058550f83c403841d02c3e82040909 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 239028776 1106 239027670 239027689
    0x30406061203110f0309060415030603080c06040507060539070b0d111c09061b02150c0a02150402040209091311030c1e0f0a060e 57
    0x1807681000d40d82e03c0301c070740c0441034075800c1684030741030750300d80c4030300425160700038000d001c1480310900b562130350320400344e081c20001344043d280c1d2600942c1e17400001450400b50702c00c90030802000070034002c1e0300003402035050a90400507100d1800740803481c62480030310300044041c81c1d00711082c4c044082d40446d060103800e4464058980c80c645003e40e0045600004541c14104110381002c0144c0032980154034515003170308640401c03203803103000c0c001d1070b10140c1e45240c4501d520304014003501102d41e40d407c003580040c0a2550540807404c51003600074540c40f4079807002d10008200603004210030840d01c00501001c0c3c09070b034a03071000030000e000d280481034014501d0010010304190220031912582e00940e95100002400e20401d5a552035402000790886e401c004901800c00307248a040b05615002000003100034500c00104400d850903501400000701e40e400c020706103090980e4072 = true := by decide +kernel

theorem cover : BRFrame.Cov 238848920 239028776 := by
  have h0 := BRFrame.cov_init 238848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 238848920 ≤ n) (h2 : n < 239028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
