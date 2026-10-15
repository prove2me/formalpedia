-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5000
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:25:09.921789+00:00
-- url     : https://prove2.me/submissions/4b9b4c5b-95a2-42e0-afcd-16389ed09ec6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 899100719 ≤ n < 899280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 899101969 1250 899100719 899100731
    0xc0307030e09010f0506120a06080d03020a02152505250b06030309131e022b18080912060f070801060c08030c07020f030d03230c070b0a06120c09 64
    0x8a60401104151207000c3c0416187c4020b24400d0303020104010900f4510a1321418045a040018030546a02c2009610090385414082c1d0010b0f0600d00713040e03542c0155240c0700e010414103201e0601c41076a401c840100c00341140800c41c004840e944a03205864050b021070040480000d0201070000d05080c0c02814840403641b00c15080503105c0c80b42c450360031751040c80382040d103400c00390680c402011030f92a19000318104800c900214240c0c1c120b15110102001c1100c404810901c802007800c6d0a50000300d0b041141c0c181845081c200d80310284000390201202045190142d1a48000f2600c00d15009040750190302c1c022030074148210f0103d48440000d60807000003d40035000b904403041c000e901208071811590391508198040d0004642668040719101d0590100d1300e050103c15108255990080b401141625281485040301007500368030000b89401c204c640301030f19003500c450366400783c44000682c803025500800351205d42c00109214003d01455000c0002820035001142c0f6854418041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 899103219 1250 899101969 899101979
    0x5060105040606080f090708120403050c040504021f3c1b1119170d05090a060e180709031703060d0b0621030405280603110c0307030e0901 61
    0x50740e03803d01c80c0741c0100744010301040e482c0d1048a00a0350029030385040710442c1c3d6071100d200b0b160620450000e1024100000c1c180240201880803200c0088103641c14401d034101230340030650079154102070a403410801c1d01d400d488144514800302181c10318445211a40c401d140000010b00209007900b0b600400c02c0d8206644c8900950005113091013040d06403408850648848440442164130281e121107200500411015200601c0c405003004d8240b103442401c106807003900c0c120050f8140024844148035015040e5a103040b0041a100780303242000345030800c81d01080f004c19200091038940082281082602d0ba445207100742102d02500e000041302c0400c40d20b19406120540303420b5001901c03442e0400200d41100d18070b03600100c000e02044501880e820003034004080f04d6461300000e80000404224525001700342e44900500e600541355a0101e03904a016000f105106400034151143d00301102d0b17100185c281c9003003050450560f43e48440c5807600070940003407450814403980f050800855 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 899104469 1250 899103219 899103221
    0xb040906020c07320a05060a031b021515030a0203030f071e0f060504080d0903020105060f0910171e10140115140912030423011e02120a0c0506010504 66
    0x1000c100c031403290190344207103011130004255031219403d4000c0401c0c8400195900c40c4001040348500ba0366000070346089040034850340c10b01542080085601508000301c12090507446103410030290002d0601c144400300100e03050400c1004040e50500000c151030401100c0c03003005003140c92080b50300d0f9103200303405913034008640c1500c0c2c40a8404c00d560300c1c0d517034000754240d03100e180c0140c003c0c40840d04007070a9482002c04d4030781108046005135121028015a0308000300c55804d074190031210141503251003000300d0600c9403144074a07181801824044c1e81c0302a014030522039140401040e0301c80d10b104800ca0075545030b800038101c24140b49041540020301642d40340407410790720b040071400c1010781040c100715410700b0a0380502803040c10400c409543d65503018004071031801460f02031900c442c600010000c01030709400e144449002c080d54500c8860ba441200e100885503048a01c9407000c00b141ca00301d04d082c0c0000c55038441920001180c050040e00030790303004c820078072503c00c4400366a211001c0c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 899105719 1250 899104469 899104499
    0x330c0c03072102030a15091106030606160c09020a05220605030a1a10020109032a0b1f081c05070f02090915010306141513020d0b040906020c07 63
    0x8181c00b0082c1041c1910b040030489885035082c0000c0854507034142680b02c054064020011140002c2e640340e018001b040440315845514000440e0074500318500700002c90030a104007500c6c08020081440d48000701b04800c07503241c01505240800b1500c072041200c0c0a00342d41e000c5811428000e0655940c1102415800c10360026100d01d541c96604584460b1450000b5010100460034040c0004024601c56120084624020152640007141001e154200600000c6200c0c9400c2030340c2410f10651649a500e8034940510140d10003403000940e600c0c070588603080c1e8640300b410030069140341000100400d0014441140312802c5420345042071259009071050b03c585400203050402c0b00c5070510243c41d1a040d01940111524203584d2541da42c100010384602098200301d940a81e80c240780708150706003d0040c2d034001e032002d20902402d031a07400000c2d44070595040314200c2d1900040c070307004525043e030080807640c0d1014000340012030b03403840d02e08069004000b080310382e4031901c08002003420311200c0341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 899106969 1250 899105719 899105729
    0x1080f0a03050d020d2310030f02100e06030901050108060106111009020102160f2903040f0606050d11090718090e03040f06080f0c18330c0c0307 64
    0x50000e0a85994195980e030480c650b6030b4003d9600f44443d0694091a020f030b0744040039100341c43c110f002d11990b050b000c1a02c028140c02610800b845c0305000089202e64440c06080c2c0499000400700a101001ca490a40f03100c44141c2000002c010701c20a44d0701500054160744c4260f05032450307a07032950300c101c400085140c21070130980d015034609690b40b01c0650095580e90300600c1910f1692103002c000c0301482c002c59000e428581c00102c81000000701d110340855410072101482042d03040c5100e203680c41400050b00207403207241520036070f100f0801c107540190300a01c00a00800070b00c01041c1446181c0c2100d480c4070394010203c000008800600c10104c0c50007081382c1102a01002c1d080a86907402800100241221440200300c0450580701c0c0004840007031010707035101c801c5458074582031050440007030710119590000748040c0812040c51100e8400205055602601000f101c03000d00c5036088030341c0319030700701e044012003004011602d0a006201d210304510440303440701035071014180e440302540301d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 899108219 1250 899106969 899106973
    0x503131401050714213001050405060d211e0212030406110d0209040e01151206150e071d030d120f0c0509040b06040b031b160b010e01080f 61
    0x400d0005000001302600512903000711805904240403e4030400d14807140c03858001c1c408941842d001414584110400c501d001c40c0381e210030410b070301d803544140c0c0c1800766512a544410008000392160040142c02c560442240c403074402c0c1c0300418201e181d4100001030000341ca00c24076005280d1a0080b200141d10240c0c1c000d0122558100c0680d01c10340018200310368003900c0c0c03600410151401005007040f00d00b4104016a02d018150800c400c4514032584070b402a4100022944900c1d00b0f50340d8030088945a0b200c10500c8406e9107005001010581e136a120b15030725000c00030410f403031028003091081a1a8075800c10081c9458121041c1c0102132400b0f0307905901115000010511034850316489884814021070b0440c01d40326440300361402503000a00041b0702145882644c503050240d5006811309503512403500c5d043c06400d6543d03210040400e054101130051a614045509045518087d01e855001c02401039600d41b0f0844007a00784200c165041c0c685002148402c000300d100d01d006c03000000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 899109469 1250 899108219 899108227
    0x30c04020c1e10090615080a050706030b030f030301030507030b1b0703200d0c020405070f0207091d0703110f010302121f0f080f01050a0603120e0319050313140105 72
    0x844000d102d040c158076020a8024422080c184400300e014031040346100701e001042c211501440c07a81c8004d503540c401d030700c154400c14544001c210081a024180e90f85890f0128141c039103070001c03902c0c05040115100c0c192000100001c140070002c0b0300381c01920301c9003c10300245d8441da154481080b00a000300c04421004000c540c0010713004070640c03030010302d0032108000c003001c0340384c042c90400c07110742800c901150002d0105411031a091156170342c002c0720707230800002c0d600c031200000750b484042c0d0050513015a9240765203110411500b150286000c0c103442140c20b000e84900e4211040968900e42c40c3c00b40300340b01c03007000e0707150b002c0d0007552940100c0346480c501d155142940d00000c5080840302030807032410035401040b04200480d584014120080003400180c4050501d1821208003e000149251510000780001840c585508a4040c118a40316401a9501c40000c0c180103800d0714000c0310f01f10104200041020100c00741c40400744a610702003d07681d46000142c1805501c43d82507000903c100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 899110719 1250 899109469 899109493
    0x80303130606030204060801021803030a14070206040906061d0108060105030a090c170c01270302060a020102160c06030b03070b040b0d02160c0e0705070b010b0c0c0a0311030c04020c 80
    0x104000680c6000e40d001046259503070f00450708440d0b454000e0025650002049a0706400481864900c000150011440d260008900408420402d070110321000300010700c003419586e9000c02d94001d841f818800300a1595031311070151139600b041e6110605909803907440c601e60b40c0038560f402d01c6907806844451955072090656401008000000c998104902101051689025182d1110b50b64035200070303c0c8001481001410800b035151582d24070b088403404200d264007a2400b04000c43e58141e508070f490360080c80c016070183c060045000908050740c03041900344006c03018100f04607020350700e0420071146004107060f250103c0d070040b04900c0e0410042048091100e50007045c0c01c61040d4401420507001001c2043c01c802408401d40300c4d1108a0300034052030070b624400035080440ca00b406807902c1403d513a00c3d1183c801c14440e0403400b450200c1c1d08a507e038004c0c08094000e000052558140d941c507441c01d00500110349600fa402880303040c01d101c1c400e003464403c07035116624810090208a0240c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 899111969 1250 899110719 899110741
    0xf0a08091e0303310201030203041a100e0f1303110f0105190507090e070e0a03081207020115080a0b060103021c020408150c09041d1e0c0a080303 64
    0x303803040303000e441848145072504404200500064498202450b034a0501d04849000741901c94034100980740131000e0b0003010b90120301407122203982800c0160700c0f565141040784000c0d4110860119a984102c100808618202255003c1c1c0e40d010142e0302c82a1100d60039100045022110940044042400710f00864000d82c5014400c0005c0d00481c0c3d00c8440d128410340c00e4500568102c100c0108401d1000144440350003140d52022441c40c2c00f10302e0f10704d014100e0410b0341c800341250042c481c102441c84403d8540f110315401841d00813044d0f070341d14201c0351441021460220ba030000103518066031610300300359654040044485070001070015403981e858440f800b000c00f525003814550b08102400d0f240040d0307034030366900d0f400380500161294644134007242040d402010013814112a8000c003c103c4115606540a901043e14006070403007050304030306500419080c4800c218454102c0ca852507030100c0001035000f90541c3c06548103d0202003d000140301c0c540211400d603041400050b0b070036409 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 899113219 1250 899111969 899111971
    0xc090a02030708070c0819030609060902070f08220305030304030305010f060c140f0616020f0a2d02031221010e010e0907030204090b0609070905030303070e03100c09050a0b0f0a08 79
    0x2400306c41e890b00e03109054841d107011521990b90302081d21241d082240a90078451007000340702c0300c00250701e02030780d40d9200d544189400100820318580454861100c0d40390b400003898101c070014519524a80701c1c10003542e03940084600301d0000782000008501022203401c0a001c80342d40307484000c4d143d91135640301c024400d903000100c400c52286d007844508048040040500815841c441d614102091601c000e0070484440201c181a51008403940002040840c50502030090260701c05000d4801d59188020354a40359400fa60601c142c000141c3c503c4143e034000d00486110310192030484420070601c20704004244103500ca110742c45001082500a04000140d00491440540d400d13292254001401c44010100541da88804003040052030700f00300a101e50801000d007001c51031245820002590381c8002000001008007050b07210500303403400c10000007101302c00728080c0f2545080450050902e0554443c40d0700c200c0e16a20000380c4d0b84241c1c1308907403181c0003040070340b494100345050036104814 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 899114469 1250 899113219 899113223
    0x30a0b1e011b0507060f020f0d0203030606070203011e0b0a0905060310230708180a11040b030c150c12131202010507350a0215040812090c090a02030708070c 69
    0x9400b0901c001400074000074010300300302d403503440b46040402c500a103000c00c1c90381e540e0b81651018100341502d54000040c2c0e80c3c030203000c540d2603640d141c8600c00b00c0d01500e0903422040c00c0352a5280981e22403070190f00441a503c0c0142e5200882c41e41e590740e03c0007a00c00c1520015010b8100c5001403031248080e030081c00700c1f980410600115810041c15508807100100c1c3c18000040c0030b081440742c1c4100014440c03901415000c0140001044e68640e4240c0c040714031405803080b540e91004000645003803080c0c40c058070b4010a03240c0341030070715003c400c0300b648a040131003224082c5400c9110091059410745484960000040d1000d5060520030101041d140d00260f040c07020034003860000566481c50b40106080483d000b2400104d080500c1c82450311012264a04c0c4ea01880340d809650750009000000d08021801d051140d1224200340400e840340000c10034401e82240200030034214001001c05001074141c82805072a84d8140c1e0000c01c83c081500d07040c0006000c0001315070140d20030004410301c02c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 899115719 1250 899114469 899114507
    0xb031b040f0204031403070203011d0606010825021506031212040c12050f0105010608090d0503180123070302090d2301050108010e060a152c070302030a0b1e01 70
    0x2d500d80d114500344003030900c01405c1302c2c0c0c4000740c0002141820b01980c0f0494000748085076849000000c1903490b8100103101c241005551400502c4014400c40e003440340311400d803140003481c0c1003c08001d40b50101a1143c804200241c3c0101e817072401c0011f8036102040004c94050700f042c0c070001000350b00d0500944280c0750801811400318400c07066483c0244054810030041641d40c4075100120309445050344502e041c0441c180c1086500d581c04a65144040d10320b240003a902e03664640c84008000c21407401078015841d040d004400301200300d029a402ea00e214405590641e9000422403e82c07003210344840d040f010103052140002da48074031404954008170300502c89044ca20000300e0840308241e0040704280e44034110724400300710034030909030480d50b403d00c14481129501010300302810759104c0d41d41e003a4807200040100d0201c40846e00e41503400c101c40d40056080c03d84008020750020740746251858070700a5070007840d25100d000e4004154008901900700791742c2c20015112103070758220040b105 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 899116969 1250 899115719 899115727
    0x5010b0c030403080a030b2119110f04090b010e0106120e07061412090c010f0513030f031101050c0a141e030a020405030102070528030c021c21030b031b040f02 70
    0x20390707845a14100e60380380c2d041c910100042619030715141044281202c07140341503072929100410f08200603030b12b01507020343d806019139425001003001800d0247c0c0280100c442030703001090102c150101c0342e04031201c0d40d442e803205850000426048071613071048561250300801d0100861801003601210208403c203800e410b00303180340100c0c024040122810010790f041143d030495150f070040d80f60407810314645001c81c106141040840069006400054208406241040c003054418965410941d1246000b40081d0920303103007840060300911144008500c0303440a910a242c464801c4d0307460003001c1c0454001c003d442d1000b00404d07500203003148040c50340030040410a13403024001840a14811001006880261a80d200d407407902c40d00384010343c0100b20380844c0800da1001c500d044941e01100c104040a0440741403140d64401342e02c0040090404c2c1940042140059850030b010003030940302407024007500e904241c3c13103051404142e21400e94a20b004d0000b424140d00a0f035500d1a0044010702e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 899118219 1250 899116969 899116991
    0x11409150403032705070614220b07050601080105131a060a0512150f01030f03050901020a1a1605040b0a0305041104022208191218060c020405010b0c030403080a03 72
    0x5404d50040142d0308502c4607100004010b0104007220061007980b42040d0030580b400304c03210751440b80e50701000998140a4070211001030306605100207010b80c008041d918502032a12030784510091150444a52903c0c0005110382201c031900c081700b6a001405104001c940d240348175100001925054201a5028011031a0380341c3c0e440c04c0c116203040800800007a4441074600a2403a8018442c00d400c07010300340100005031001c02102071056050030201d40315508000101d20741168840080c01c0d01d50603031070a1400292031a61140a400000c0d510602080e1100007954144901e125001c80904101700403c2080d10036881a500b003449403034903d000b07a22580004041c0d03003241102d40c10700d48040300100c182c05a13004004000f0008080503009180c00b4692110260662a401429000c4004040010644a0700751001a0250b04808803266034542200508050103910200e026602d80700c00881d6103647c2200b50780409905100171850541550b403001404d820840d10102450f86800b04252 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 899119469 1250 899118219 899118251
    0x6010813020a17010f270f08030a020d051b0a14070506070305010f12110918070f080c0603040b041106130b0a090b090d0818090108010c0201140915040303 68
    0x10040c8440c0041410001c240540c07913003100c002200182c0c485107400150010308007010125405111100001c2000c03401a00b48050001500c10000305521000410000d5003c4c141d409082c1103410300380300f000540c0e41d203002406500c041f0510380e00c000d1818482034002c5441780030340c1e4904c1c0e81c0c001605418003c0300e54030189800001c4c0d80c0302c004603480d01e0040c44815a10086640204005c01551303032204103e03282d2000c40c0301401255030003000032030005000300c180307450019484200d610440b1500c03a551004808100b4190141e628603020305944508a0301d0501e042e0b030302840d00a00030075465225652110000780310201d40ba90814010301114070400803c549507401858950310060b500c0790551001000315000d508250720740c100a003c1e4464035160603403d1004c01e0f03071041901d551501d2044120040a81800c98a54040404070003c502560103403c46a4440425002401501d00c1c006403800481012120206554000504805509000d41c4040d41140c06401e0019445100f2036900c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 899120719 1250 899119469 899119489
    0x70c02030a06020405010e033403050a060e01290f0409050709060612110d05100f0f090e0d1205130209010b031b030709050d082b0c0302030f0601081302 67
    0x2d00d146602182c104040d5030048644481140e040f00544200020307254100c9207072100381040400c1e4035402400904405000800710051500a07044860150282c54076002600d0103862030085e0b542000c200741090801c44119841d00b0003001e5180c1c0080b840700052000d8520b402c00029030094a071107680010a000340005005031240060200b00c2500340103028003030401070601044011315054115146800f42c0c0d094442a10143c40301043c01d81320081d11804a04050700010070749901400000351140c5078401c0320b400c840e4207000c14400c400c03500101645405000c0811404512003043e103100741d5000b43e0081e9440802c203504c80390765030516000720380185000d0704040403200000052000c4c0101042c030500a80103200c280a256181403030b03008004071070601c541801364150905403010048214251080540840c080301240038035081001d131011040f02c1004829460a80b15000d01d034802e001301c901c158142c0294130140d0701c40000454002c0030040c0b001d150804410b18a400507541c180700741c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 899121969 1250 899120719 899120723
    0x20a1d03071d0f090a0b0430050d180b060904031206030f0b060a06020d0c0807080d020417030403030927060e0a0b01023408060c070c060201050f040803070c02030a 72
    0x1030b406860030a610102401000d000c200e11039201c81001400038601244150f40940d105a401c03484465400003400f04055000c0c2d040c0b8000060080c1c0401c0e50b40c080041c0c0311450070400c3c10301407980711201f000c40d030140e8842c020b080c0300c601c3c0000522a0410803800c1d9000ba01c245084500045101509401c035000c0d40c100721010b805084445090021000040d50000804c0364500e0401d441d0040103541c40e17040d20880300502070b6410152052084c4041075803039050b085520f09540d000f0100e5018000d60050250305141d40503c02c6803501103070000300780c9080c0c0358541c440407241c0e0700b07018200c1440070000300b480b4001d8000301001109071600b40100300051941c0008001181409904002500d00c14030500b1304641c8004c0104d100a00694910b00541d95818240f22000400b82100003000320359030001c0a0074030442c0280170b030100d5118000d00b80107000d0200004801e807030303003412406e94200352804a001c0640c0408140841c104d2401150084441d060441c101c2403a540440d0400c0c4c1d078003400f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 899123219 1250 899121969 899122019
    0x3150f0a2a0306030c091505120c13061508040c0902030a020f0a02010507110f030403060b1c050d0216050918010b03011d07060302040b07030309030207050607050f0709020a1d0307 79
    0x100100086104118064001d454040c054000301e0341e0b504100703242500c1058450151a071503d00a0007060202080c0030200be0401083d50701110004c401408a51184092117800284034203919845004030b02e000d942e200340d00c100307640d241c03011030006500040d280b130f00081d9003000b0060115494900030b0041510540001c41e043c60401006011400c13085001c48141d0003803003401c43c0b801c60101c211f03401d40340e1100c2c0000740c44443c000840c0c541c0c482402da848800340c80c01c454500340b00340020511101c5015600726054080d41550a101100c0d65110310341d0801c84800c0841d00c0c1c0600c410000401480300300000907a0a2540002402e40300d440e804050121b0b04002503000140040c03103a071010308642e05056243c1840c016010400d0701c500784010741015074802038101094800e200010040c130004009640341c41e03c0b41800d5845004411108003d885080340c0002e00c4800c0f4000d43c0c1e000c00c204d40721860070b95a80003a5641055112000300d9141c01103410100f002c02d00d0340c0c902034115000d270362 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 899124469 1250 899123219 899123231
    0x50c0d0605060a0801020f09040911040603140f0106050a03080d1515090504050f040b0a090b04080d0c090602030f210a0204031e0c031e1a0603150f0a2a03 68
    0x43c0034200860380c001c02ea00d41d00420410b42100f010320304441840305c060f10002180303901801c24618125081840340e6219050500020034041e101d0300d01c0201c1100402510721041d102105a0300700c5156200b01ca401c08100f50301040401c1c46040601180940c4800103d805209084024184840c40e0407900a4880c40074103240310540c4040c5900103410299010070042c14442c1c0c00303684501e0010402400c803484400060480b00c29500200c007000d40c0048016201c0c00d00740380c84200341d004540f007030900500d8138000c2c4803a02d120b4960182200c506402952802e40500345107040c90b4008135990f1a901c000c82940d245002c445c07485944a48000440140c03900d0540c40c2400240900805400c64243c1c0d548180300401c048406072801c495101294102c21030b40144440348240c81d901028102100307000154540d14018000e03903104482c100d040d110780c03480035500c03c581342c401920700140c03000c002c200180343c1e807101d0b6120001403041c1c13100c221100d0f48450b10b850315071602888440b001030b840340d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 899125719 1250 899124469 899124481
    0x308010812041406030711060c0a03050a02091f11060f3939010e01021c02090409020604120303060603020c030712140c0615220504050c0d0605 63
    0x8402480140360300c20040345080d14012a10f402c82890500c4244201800804200c1403400740320204400d58082c82541d585103807100142c00c403500314194900101c0e09207800a5040f4010788219410b0000c014080b0506038941004100802510315845d0184104a4030302004070070104005485080504000401494510008880507013002c0555090980301c0301c00d401010720406800c040c0c41050100140c40784004c01019440380f00748200b6100d0405010002c1004001c00303100f0305411907200000b0311040c0b5441ca5140d00701d1254441c43c281c1300004e000c1d2881505a41d40081c803c3e0341d0000c2c030104200c0e41d1038001030300790350056005400722884101c11000b015003500440005040d14107085062906180707409803079100d0700d907004103144c03030b040303084030f002409101d541c0f0a4921848600b03417a2029041d2003a0780d000d056a00d000c00040e00304c0a000a40381c00a085000a410001820203001c0c0501401000e080040d00480b001d00844e161005c07645c440c1585408110300500004c0341e01d0400f6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 899126969 1250 899125719 899125723
    0x50103060b03011811011e020d020c100207091d1c030b01080402010c0308040515090d090b0a050715180b1f050a06140403140601180212040f050f0a03080108 69
    0x803907865000b64100480b481a058403200d40e000900e800c2440c0f5504500b880d40100c0c4e6001d203000b610705028007480b02082030715a0008040c014001c0c00e400300d404402040040000100108400c000107a000c980180000c91640d008005610096075000300340d00c001201c004e06100e034400f1106002d19500150541907507050055990544081c00c00c40401d0a16400080002c0002c1f40040c0a10441c0000304040107820458044811218002c110060520070f0f54140c403801c260300c00100085c52100c0104803001614111000a13140d501c17150b00d800b440d82d4038542c400c0510503c11148661381d40d40e405050074003403907101001d44190344c5406075142c810005000001c0c8003451400407402c160b814000b80e03e9514a50b4155110303420840e80c4030058001785080741c45103800080c5030100d041d4131044851000240340c0e050b5240c81a808024440241202e0304a01643c40d91240c0021103a0118000c28001e0002d800740070f00600c213540030034928013403032445d04c032042004030000f0784c5a000422800d42c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 899128219 1250 899126969 899126981
    0x905041a04030c110f2808070f0302040903021203070e0a080d020a03030f0b0a08100b03031c020307050702041d0105280b011e0f0e0d0f0f170403050105010306 70
    0x112010015640c2440c0d00c1c010442110300f00c0082503031410100415403079444000300d021150b401084503020b0f2145900c0216184c60360109071920f0a2441004503449001040d08019941640099110742d4910b408000c045c15540340d050b0306601034854800e18100c04000158803072030654403001c1031001c2070428801d04620355031092003240c1007880349160343c40e80881d4001d60a6018503010401300075010a40780184101040382c0d0344102c8002001030074540114602002d201c1015081003045005010b064603880f540e204c0c04440100f0352410011103049901464001381c2c140303411800e24860f0b034082000c4400b0111224001460a9070340f5070301340d009005032030f44140e42c28503404210411203510424040481c020b1850350780c072025014040e9128842d0341141e01c1c00550881034803503200750050a00044501c004c00021a8420b50245905103502044c004943c0a84d41c524900c049842d059008051454122034002c42c5054003964400e064014102660017800000381a501d1440d04104a441d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 899129469 1250 899128219 899128253
    0x614101409090d0e0f12010b090f010b2b0507020a020325050f28080f070608190603050102041d1e0708130203012d09080912010f0204090504 62
    0x300308041181c2d8030710104184540042c00d0816008001c224030008a4a070303000c1c017009400ca90200c55a50035000150048800e0f00c00555070501d50343c03100511000801000d0190001c0050200412220391424004560004410100d018407200308140a0016107a0540d054401030b4001904501949000e00490010700d580709648002518840020700001e2400e2143e60701c03402d02c0d0200c0800e10740f07030b0203d00c0c40c440907000900c1e80c144641c0f0140350722000c0d190058520a2144031fa000c2003080c00024803000741c0725107031901c00d1280d071891040710400541011521845854000010005d10240041d2008e0301c8018083d0315540c0034483c08440ca11001002103074040d640d02a240d0300301c401113114940004180c40e24039025aa00484640c0c10102c4e01d1000350198a014920501810803901c00350710030785605040b0358101c00112076001a03440401001d0b0450b0404c014046075803500b80c1c030300e600020340c690007c00d0710000c02c51503400300e80107035001c8034410b5203907400c0104001880f204002d07605 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 899130719 1250 899129469 899129479
    0x31205090a031a15130903030e0114041e0209061002160b0a030c03060b0702060703020a0f060903030b0d05060619030f110109050307030c0e06010309200f010906020a020d06141014 79
    0xb13007148000606605500ca0720340f84e10b60340c0b41c00300c9082c10f101c0e800c807100b8203a0408c000e01141c2c403801040480200120b4040c0c403001d030b524030b0341c0b101c0f0184548080010783d002081c0c29001c4d00c0d41410400c210480340d008000f90f1254034442c81003404608aa6401000f90400168030341d81e0000c0c004d0283c4580c1e5247c0c604051600c002841030701ea0106c02d82d9086501516455200d07051454264605645c15070080c001e4804400c02e00d0400926030406c95041e0f101741c1d400c0c004024907a00340680310881c18001451500a0300004140c1d04044c1800b9101d10501c014065a4980e2912140108503444205580e10040e0100701191540c1214521005000c16802000114950780b01d003006c4048501480c481d0000c00804605141e2294100350840c0e9080710b0004514068900c0214a1a44010380790f40184030300300c5a45820342c022107040c0e0469034650050104d80019508002d4988a02c00044550580e1800603944100103100c40c01e210707140c00140564100e003411000048072441c14140c920031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 899131969 1250 899130719 899130751
    0x50315040b222f0313030e06130914010e04150209190f0605040f03150f06150807080112080915030112111f0e010e091504050f01050a031205090a031a 66
    0x540d0f807010849600560307103104c03510007850078501141c1d52804820800da000f40046a410001038146030401c085503614071013003000f8036440c9080e1030358000900c2040218640c2800040c046016100c5098040350038100043c64900e604000800119900701055014044101f050202d05031904a800182460307042840c1082d00d043c1b50a000c511090000900a02803c2d403010b4044d40d0700d070481c043c2c1c8002d010042c8035090f16002c10f00c0e500707104140668000307107403000881c0485000f084124142e54a0402c4140000301c1622400f07011b50100340c12a03000040d142c0f48a40718001e0b14080c40c0a0030842144058118240c18034900081116404501c602c40900c00206d4440114012449a00080c1082020045480e00584001002c000c103190801e82da0310030042e0341c0460845441c46110100e400300800c2e00c0d503a143c102c007034000340030b5660031002d2b10f00180003150081101c1642d141e8980b81442c44d0130b81e10703804258032549640c011583d05084603210200c1d0000c1040c02940202000004610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 899133219 1250 899131969 899132051
    0x8060604050f191103010b0d0c08100504090f0206070c05090702060c040e060f150c0d030b03060a050414070603200a0807080c0705010e030712050315040b22 69
    0xb50341030191030100b4869000c6011407648407160031007407080c80400030858403980e41d1352402d020703030340b0141d4140c030b5252608000600240c000c48102e405940319044c00c0e280c0746d0401c002d2000a050200055803800880c08042006030f0b103860007444258810020485940d10307280c180309002002400c0b00c0c082d03401100c00c01110640040030b4800326180c4d407540403d6030303d502001c600f055202c0c0a001e50006400d0711031290500402c4020942560a14111481d16112074800c4040b40c100480e00d56042d00300c0030100701d00207500c1e00260303003080c0680310ae201c00480002c2c007075103010b00700d0784168040780c4c54115101c41440c03400c8801c0c5080681d2440189072804040d0001c190701c0000307020350103102072079000c2558a4035000690300404d6110008118003176004060540d00e8002c1c820403034010315540200c0c05607134843c0050b07034081e00003d400f03841160411420400038007001c04440d90420040303a260440e02c904207403144130219081400195400114622001006007954001600c040c03441e09100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 899134469 1250 899133219 899133241
    0x801030f0605040c0509070e0a06020c0a0b03090c370e04150e24070f02060a0506030316080318011a1210090311011b050d0b12010c090806060405 64
    0x20040c0d620050000d034681c3c03503240c41d400f0f9880d036400803034002c00d82804104545402203100c010107481140c0030180181e0b204400c82e034071798070380c0b95180e000001130100b0071500160201030750300f00c00e011040c5c0d15452400c0c004030f1818005e41e0700e03a605014501542d12080c044c29004020342c2050301d41d0030300401c1d0929a00c00c026900203000200084070003040f81c41001d000360f00003e29503040f402911000c000d4500400d00440c1c100f0000d809030101e01d80410316050003510001040402c0d81c01506c0309130f80302e031024401007000038035403034150004110446d20015201403140000c2e20420105851341040301c19048000c511345038039401d9030700d0410b1a035504003a021030403500d0b00c81200e800d012518601c07656400c011002400451003410030703611400305600300d80500c0d41c600074800208144041c0b408941290080d03105580c0100b6820840100e0815268101036130b0b000c809880c1d1384403424075502d101e003100e0440140130b00003004c400d0f05001c110030034858030b40c00c000212028045400e001c02e03441 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 899135719 1250 899134469 899134493
    0x1060b070816080301080109060b04090507170c0a1518050123160602040501120543020106080c060405060f09030f0708010b04051315152105010c080103 67
    0x781c840140890302540c2c0c1c0c006680c8005400c0e41c404405916541c1d91b01c8610301802c1004400c0f220b041c141250381c801030501d44600081c4a80003402003010500c0c00420ba45804460300701c54919000e41403101405403a0034808100038981c3c6422104a9000130b00c0061a40c08038910030130503045058001c10950380c1c48807407261180802e41c2d084030080c8061800510034401c00000400c503000882441d01400f035a54094021210280c1300d211510b011006410100c45040343d0000403541e441c02d0603d40c500244110008a401400c00590200b44103200082c08050200410380140c1d101d81c0288249030701440901548241518000e040505110010301c0c14002c01c040f141900340301040c041d506035020001ca011020b012400e8448c00350710303614034034080e0505280b0540a1030a02002c1010354512600d0305c514a60081c03c0c180140908070f40c0326000e0404d0803c1c4261000141101048003161402161280c9803d6895000808036900d0725900b51001c189401d414880c00070700410104110f031300e1013 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 899136969 1250 899135719 899135723
    0x1c08070e06120f180111071a0f0109020d0e01020c0a17040609050906010e090903031e040201270504180221190f08030a0b040b031f091e030203130801060b07 69
    0x4290f00da91001c1c210b039025007184041d6030b110f60a1003451440382c2801c60003030004a0042031002c0c800c0092a14508000c4c10541700000c011818200400240600d40c2c083d200740c0c0c1103080d001c03944007010900d0754203907081802d100b0780c80d810078664981080455010743d080034109501c641e00340b52412401034091611403003074602986105000543c2a031050003644000400144600b01c40e041c4902d199541e03070002c842e4001e51078184841660b00c405a01d00052040760b0585d00c2c03420031041c8045142c80242a104103481440c5c400c0000b04180c1e666004403124549002c9482c400400c650041240c00c0308403400701d4000c040400c44071081c40c08080750094403500036458101415940b8508407054040c0341201401c141d4010040c00041d41301600500480b27a0120340070f00403441108105612210110b0707180c80e4802c14040c040b0380303118464009500407401508160081562005816075061851404400581001413281c619504440d1000054240e078002003116a08040001c64217100c2e410b40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 899138219 1250 899136969 899136991
    0x30c0212180f090c031024030f1b020c0906060a020c0904140d080a0f0501060f0309020a03080a050c0f0d05040e0c130305010204051309020d11031c08070e0612 70
    0x28070304103071604401c200801ca005400c1ca40280382c088100d00b20303030300280c41ca800ca04011040000b402c0c0c6605801840b90400480d180421503c440c00980c0180b00c0e0382e00348089162207101c01099003500101f401d141c40c0090b006003d001c40d400d030070000788900c010803451080100384101c40d0003c1e800a000340400300161b4101280340c9440c1007021402c41e42ca54201900d100c3c04002c8051036502c1318086014242030a401c3c001c009041210744207640d800d01460000170091080340301143e00c20382291410f6800903001c001850740f20f407103d0605911001401011480014078804040e07000c010308401c2004840142403040002400140700c0c0c03203a0700c034000821402e000400c145502d131500300c032090b5800c860060a02541d91030618080d42140c81080d2084000c1c011240035110f1a0085e006526801045030a10598666030241000381034000c0c10307094810349410201d240d41401d440001d0340c032103031035504480c940702070000d1000c0b20b113403050390060405001040c511040d03800001c1d004a0300400b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 899139469 1250 899138219 899138257
    0x150c080a08041407140109080d0212090a0308040905060a050603010807061202090909060109271412120103061a100c061b030f1505030d0c05011103041101030c0212 72
    0x140012140311401c3c030741c44a4029a240060a42010f12185005840c00c0e280d8002c4d050782e40c0c04084d01d0f141d491000401580092481a0350564004020070005500815000300c0503120346809616800c10f8010028480d1b98174240422882c0081d180801003d084907094690341c10400016261072980c8140c070140407020b04850032440d01c0380c051b11032015000d00301090078906101ca045e541c0c5070078810031401c10719010102c02c40b003107d04072002456070903841008a85980d907884101c0c400140040c03180764014071203a45c0106010100038130714910080740c900e50a50460a2030022940103041e851200c5a40c0c90704480c3c0398440340350700a030040c01400c1a6060700100d0401d880035012401201100607000d24064400d1a01607010005000e1043c008210b91200c030b040440c210211402003c1d4541c0c442a410a509407140250b007000905c80c40002c00e51480b00100c030810380c2c0054504a817403d40102c01039105590611500b0203403109440188281c0c00c500424085503c92400c2001401210b85 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 899140719 1250 899139469 899139473
    0x302071106030f0403030b0f03071802042610200306031203130c050406030b04140c03071403060906070503130302191208070c020105030c18030709020301150c080a0804 74
    0x1558000c4890000d4607a40d564070304a54070440785001100c1c1180881d1030000402403e0904054401c01c140001d001040e0182c1480042119101c1546480745d10316001c10000c81c201c1c0440c104000614101c651456410100c15103007400d040c803000c03003181054a400d8440c0c3d08407103000b03120142c051074502c07203650300d8440d1404241440300548a00c645144000213000d00700e04c680c40d1440109018000d1508480d844800704019241c02c1d02c00640f081000d4008a07001c2903071228149405c01621080360012810b520109003004040d600c50302100a098074080204d0030b007444510b80c09142d0b400980500d29044a002e4001d0102a120b44111040f420f030900405008101c00d540c900030a140e0800046000d181182604111000f1880094001e401150a19004291000845505840311415a41c507003c0c40c5680340c121104910000307090b5031011a080c0c8040c4880c2c8080c1c40c840c00050303034a44c1090280040040d10700c281e038040010800300389003c103900d0026030fa40d07400c03546060b0805440328 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 899141969 1250 899140719 899140733
    0x60305072c07050c0706021605030a080f13030507181a0102100b030c0a12050d08090a06091e061a0303131203260103020102120a02030a0806120a14160b0406030207 72
    0x80340c40d005461040640c041800c0c0e4000468000c0c0d44080c0301d408c480c50761240103250b180d14901100400340380050052404c100808005070080ca600801c42001440e5aa121542b40480c2c2d580900070a001c0020780c8007041d40b80380100000c440103217501c005141d00e003400003991507180f5226001a95510512106181d034184510006610003c0080d0000740c2c41e5a03494820f0011b4003c100c50b01d12605440c85401c9003c4c42040d4030440b0f02102404100e00f8613100c90020f4129144115019220002d444100c0c110a44140c0c4885014000c0022440b808000c0100f0094107405914820352091000004441a04080b4025101000c101807240a1a0302d41030b01c2e4800802c880300030b10705201d50402d10070114005614100c0e8002d034225120700000040e041e0a070301c1004c40e0180160010066001e04074021000c442c0c1011020300a00c50031008249800c3c146458404211561240c1d10495803690301c040090f6180703800503000c1406220318180400c0e01c80d1003148186018550081180c60034403403a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 899143219 1250 899141969 899141977
    0x1d0f01140a03020309010e01092d1403031603060506091210020301081c030203070509041a040f0606110f03040e0a180b0405101a04181203060305072c0705 68
    0x106405500e40d86501400b5000e50070407a082101c9620304491001d0450301405081115508442080707000801008511110010324491241004901d0340324030025090b02c1c2070968425042c00555100d0801081c41074041403d540c2803c1014203124003400142d03a56000c44c1e0034203004035440006684510b568500b80754001000c0d528035880800006226034001ca20000000c00d80004004c01080c0e21000760100d020640f8080001403052045c200c00e400d290b4003601004a007142d4511103025440b0028044d50080c02c2c07101030140d00c4103c108038898200d04913800700c9520f600684241e450f042030b525a24092803003500b0f12001c2c60000314a2800d00740e8480c030f10806016500b44100c154508244004080c2030750200d0349445454103254804c8418419603241c50030000502c204969482d04110260403e4010f030850700c40380740e00d810000f602c0c800d00718290310030545021820070710f907091007030a10205070720604003500001c481280c114481d6034103035445445150f861f112600c6101c011209802 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 899144469 1250 899143219 899143247
    0x110d0b0f09011205060a061401030b0f0429060c061515030103030c1101020d0e01030515040207050c0f120a060c090302030312010f170a150b030607080f06011d0f01 72
    0x254079800401c0100c101c100f0043d449014900700c42079034646185031011215a8400c89030220031480c00301040d0341c0301e9080b4207406c400080c03021000904060001e0110b400c0104003c41c2481c140d0755400c000003142942d03034a00c143c100c031000c6c10310980c040c5031900c65500904160408104641400b0b4940e141d151104000c0a10090103443e90303120b00e0068407011800da41500c0080043c800030b079440d0320004020340e5981403036648034214880a80150090500039140300d4508072601918160b5840714400b92001c2e9008100404440410409104681a01a8095020310341c1062840202c65000801502c02c9500046c0046c0e596a040c0c000c9440c8002c07600000c4d0315000c00510582c9020b8900c180505940142643d20406581e90900303000c0d440001030700590380c1c0c100d207182070042003d5484001030385c0d032060004591003940c00300007410701c141101c911020a045100380070702310901140e1258041400e0901703003424403080c0030f09140c00030340a407142d100c0d01010003805e0103a4032841d04112001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 899145719 1250 899144469 899144479
    0x6010504091707061e050108150405120a201603080a050d05160206010b19210c1101051f03020f190f0305240c0d0204030c090c030f110d0b0f 62
    0x400f54038180014140c003014194001d144868104c0307081c022072194904803010f5500810381c010402555048450f001002030340c6d68001c0048001c1c0c007035a0180180203034000c5581e042c00042500401c0d0400c07c5002a42119a40c001c24210301d40c030004040e03000a480c0c10107500c83d03c881e03d40008454502c80e2800758295642082c060042c0c1d0340410403150124a003540a490013aa02d5040c6080b250050602110103450b014581c404114010031002c3c0400e0b4041c80d0080115103240300513015500ea0501d8403002486102524544400a00ca11034020040c804200d55180f0442c400c070004190900000c0e22401e01c03400c4a2803142e840300c1003080740704400ca0021003080d031344100d006078812680c403007aa80d034081d041b005030002c02c1c0004656002a00e0b101c00e608117407600e41030000c1540240c0a03115031140d0801011000c102c140c201030000300051340d0046012052480c004059400c1805000a042e0a0146070343c1401380c1081594001d001d5002e00252900c99540014160703070f88504e4840e044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 899146969 1250 899145719 899145727
    0x9010b0406141c02120a1805030d020a030914071805450d02010c02030306030d0f200c15090a060f12110408060601052503030f020c0d0f0c05060105040917 68
    0x7040008902e81c4190414402085841f42490070703481c400d844000000c020f6082000105204540d0b80d002e061000402d00d0002210364655480034280e90f0480c04004240c0d01c0780004200729a01c420400307805224620042c0524240048030114000b0304100daa00c0110303011505460824010440b0f80740529485110403150200b0848030f519504180c0c400710055003810784881d921800001103a00070400130300244000b240d8002c00321807413007040300c4000411224a10342e00000c0e110714400181c4005050143c0780b440c2582c420802c0c0e10511040e103d18007641407100e11166507800009408a0b1080e080060011000f0101280d003590448a41003a0740d1500346800302c00764030740001c0e0064a00f00c1b012100d464071348100540e02070242111540540c244c0340c054092817a429004002907030b10a05010582c60208403040d07040e0b81020340c0c800c1299101c80c0c3d003000800d620030742c07070380070711815082c444680c9a241d00d41d00e4075142c0500901d4003442c0c5450f6401c3c2001165240401c011032075540003529 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 899148219 1250 899146969 899146987
    0x5040909060e19020109230603130b190b0901030b04060f11180f0a0321141602010f0816110f15010320010c120e04051509010b0406141c02 61
    0x1112900910580c00140c00c2080480c000c447c864010000b5402d40740d034510590320769810084942d0004180d4640c1c5d24240b2075038400501d002c940540a642c1c540c40c1c1d01c03200983d1420400c100d0303598024551240c4100300040002c01c000c075000302d8115402c248003140154040403001c018042c40e45140c41840702c001000d020340c0304c0c1074100440e1408110f0f0300b04010312000007000101f500e203010141c01c0030001502d15955600c100c09001c01c2d0851420404035882d0310f681c140207035400008190010414100c00c1030304541e80200c0c91030b150702e49400d144255013440703e034248405d03003203508080c00d1090001070000460340420810705c103112440c2c00c45111503814124028030420a2100322030310403e864140344c01004107070302e03008d2000040e5035014641c0e4190319003108101044000c2010322030220852585500e4a004180c407a80c5118103849400303501c0000d205807088140d00c500f961841c2804103010303040c0d0180d40000613400c0040c06030344459012502d641243c00e00055008018070004008071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 899149469 1250 899148219 899148253
    0x15030c0a021005010312080721020c060916290711090a0c0804020f01051c05011a1e0913020409060918020114181302070b011505040909060e 62
    0x44800550303425502c2603440440c185003910030070701000b041c442d00c4440c400e40e4580b05200051b4402c050740b40c500c44401100c1000802c2d40a90449810003a80000d8642d0502d4010020710b5000b8551000808868914940304807520745540520700054141d8881c3c00c0040c0f0100d1b045038006442021a2651b4104928041411540c3c40164030b0240a0707131000101e200010340b2030b80740615000d40715215103175200ea00700005400c1e0081070364107200040c850498083c14164074120703100b545010004243d41070100f00e80704076605d6417070f10359400d00403c0164444a203a83d5951050030b0f51039186030701c0d8541000001c004410ba070b07015a405c684003080c00100c000260300f1000448400000803c880c0c81c0706110819010f840b05406400325024441020720a00d07101c0c02085829034000c640c0b0325000e55007000235001e0001c90002111141c02056030342c140010030024900510f04a8100c0c5038103100400c015085001d148901d0b280d0566413500c03801404100d40148142d1222704003174510094814022013 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 899150719 1250 899149469 899149477
    0x50303030a051b04030b2214012f090405040f080d0504021f020316060605031207021813060902240d0f020c070b07050705031e1002040e1515030c 64
    0x1001e08501c490141e0710f400b50240450302940c0e00702c00b010105540744405071542d034518171101849088141c1c102d00106028414a400c600018000415407c1264034101185001030984450401902c0f241500fa00c0c0201c04807000c038101a500813615550301d00f03142480d20551f250140502c0c10010759440c0300b082075800345100b10f108032841ca11006210101c001c15038590b00407500568401c01415107003420b100c5943c1d11540c0304250205d400c64594010a0902082c41c100001110f07011542c0300861905042241c4420341801898140c1e162110b0010072020b44080003418403951800300308103540f1110700048100d800100c00c0c0003540f4590481d24400c0d407108040300e21503450085100c0441125000700d85841903c0700003000940c0c20090340a03034a0707003c0c820840f0396204420001940e61018440e040d0502d1003101079007044c200c1100d60302d0500070191403903241c5238030400081c40441d05284080781c00040c0189100b80554403c0c01103040e00e0000146502440004020010262110f0b0020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 899151969 1250 899150719 899150731
    0xc070b0c070323040509150301020418060b0c0d050a0c020907050301090e060603061801390905060307080910050406022a0d050a1e050711010c1a10050303030a05 71
    0x41180e600101a01102600c01d29507030fa29041c00b0001001a0718190340304a4100b0b103100e40b03580603075421400181c00c9a201e54040e40c1c81008240507600f05d01e040d8030503113000f81007182d41e0758a8038114039400c82d150751540f8004c00c14070a021880505642c4106504a0040e40c05440c01c0458109110090026002480b03069034803800e05c0d0504517400300c040f619500521000c1e00a0403a6103443c2580c800250310001e0038607841d036030f500c0c0c1c01c04e5104490310766840b01041c031903164880c41403641c02c0741403522060700c03502c3c2072002022042005469083c03c0301d510001c140f5000ca00c03501d4841020b0b083c8090300c101d04107100e007002c1c2030105200f81d81e40207105664820b601e40216200d0841000c50740c03a10800150001d80103075403c00030090068000b002000014075000c1d0380003804540c450138a4070f001c1003c4001400100d03d4808006040006403203081c82401c0c03c0006022603501c2c01d10080c0c21035450041c2e26003c501142141c940e041038034004e000001c050701c0d03c0f49003412914004000031152 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 899153219 1250 899151969 899151977
    0xb030a0501050409020306070e010302090904060605090c03090601051009050d030306051906090b0307020304050a0f0f1703190909060b0c0118020607080309070f0303020105040b07051309050c070b0c0703 89
    0x601c500d00f80c46440030460340680541026a501c00c411b40e6481c12480750315061603020001d0344029a1a035810034443d80c400e07400012142d084c1414444c18100052409035410010001c1c014418000a509411510119001d10a075004818112800c0150b5031181c0d0f00300c0c840d40080020135405401400c203a8038203030340582600c08900c01000070004103204034408224003080c18403950302c0348401503912046600403070b8501543c07800807030b1848510794800b0300d502040e06005d21100f05180704c4c401c001e04480e02035040030400443c449840c0e22071901181c810700817420300d01201c00e0180c61002c000b4602510104030309030f902d845544a55021002042241d460b04c00c2c400c0d0342541040e104450107030050611424254555200841907102801d0f41909114558000130b0f90303021701b14400082c500c81d50004c200790a140c03620005881c809000c041c24050188207039407085907100c425070205c84001d10040b07001e441d000d2020300a40300e0f240000c1c2c6143d50700c50400c04c220000c8801400101e120b591 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 899154469 1250 899153219 899153221
    0x5060a090c0206150a14210a03080108010c17061c140309040b150915042112030c051e0c01020c2a01140a05121015080105060d020a180b030a05 63
    0x802c02c0711490752070003480000c05810121b0100e0b030901c0ba20301441100009510200034402c0c04c070329460a8a107403811400691258014800131400380a15100003034141485000c0780441c0d1428000c600000b42036900880c46c80c208a6020385011940a8600750400b02c41c1001c0a410054103459511690849000705e060126514241c01c0941170405540340c080c441030306000f240c40410910045501124402000612000c1080c800c00a01d1252421841444150024081c90a43e07071000c20b03d08800c06240c902100200c605412004035400340c10014030010280569890148090040b980424003561021075100b20b441710020b11480c0ea0180f500104415070036042c0780c201c51508000b00207001540d40d8041c2c040050341e44000d80f5501c1030f00e080c51070504045800481500c4011a40d0818a06803100200680c501c0303803200f14086602c0e850440c24560400c004568544144402030340c4142d070008080d007a6610a64400d02404102079080c0c10340c0c2d03541c0c1358040c0243c00a030348034421149403034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 899155719 1250 899154469 899154511
    0x31e0503041101050c030c06130c08010b0f10111c021509030a0e060d0f05060f0a1409060315010b030906240f0a0909050109051509030d05060a090c0206 67
    0x4000e903482154031040c80412a080800115055088949203140500c010310100303400041c11b12449105510012599804803d00d040076005944c56521100f40b59240c00c01003007043d01c40d2401c11650171b10585840e007020420000803501c807400c0144072090390040c2d10412140f821001041c001000141d4203d0704a41e1a824001c454072006907045280350f4810060b0106060107500c8503103081c2401000381e41004c10030700c0070000703075403401000400303169845003000342d607150950980300b003018140c620301c031424103020740031000c00341e0502024419011200082d89a42e000c20405059402140e10114035594800034001c0d2500282e80301d280e00d004504c000f4003110714104440302c15401c164000d000700c038040c2c410700c03207141ca42c54402a0020b40c4160046040c4480c1d00404040c00d1081000060040180c00c2c0705042c100134000d08001210824184140c0200020aa500130700082c01d0000d420340720301c0c0000741322650a500c0700d108130303003000340008000303401040d018030800351140004040b0b4804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 899156969 1250 899155719 899155727
    0x90f02040e091c14040f08030d0f0606020a030e060d0e0f10090b060108071713030305090c01200715080708091f0b04180804030201020706032d18031e 66
    0x62000c2401c00710b1108038001c10f86105010340e01019002007000c51a180d182c00c81410ba41c00660000d0340a81c1c4005003084030800240700d400752420000c5020400182801e40007074071080001d038081e04004001e085008565030744412611189101d400c20000e10919901032a210742100450104502505500460b210381c1c90286110095002588615507500c18006442601002d040c41e000c0117170035405101d0383c0701d54884090045221062260b03801c2d5461600030152540281190000d8000103038104540e6004a0b03e9280b2071952b040003041c1300080d017411031034032982d0340c031150300e4988404d4200880c03500044024000c104e103070741d07400b49a511035403040c3e55038285540c0d032031002e0b0300c1d4180d459060a9130751104040800c02003010801110740c0301150100c02020205071240c0700001070030800c540c0c04100319402440c00d800e00380098002c040c012469020303004010051400d4414070311481d5400c961002d0044541c8000240f504d068604000301003046042c0b00e80c20341041d80300240c14003809 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 899158219 1250 899156969 899156983
    0x9090b0303040b07051009051c0912030f05070b07050417060f150d1505070f020609120304020117040f060e01020c0303011203050c0609100b040204051c0309090f02040e09 75
    0x40a00214501843c00c060414180e02501d8103a07468000d04403c031181c0316541c00f0303402d00036008400425107001c40d0743d000c2d45040610350000d001e011000d40208250703802714410340380d0141c15040c64075034400c4a0f4020b6a280c859040018a8008048200410160400064000c2d40c5c1c403400700d0041058101211650342000b07552038a0740c034240ca40050031030304402441c03c08024001e4030031001c0c625640e03204500c0ca030745015803417003079074580742000b00c5254000b1103003041401910061007d07003042074645449105800c040b41c1c2041d070000001d015a4041c00403510848901d092800c82c0b803070182032880b0108400c9a040750001d00b403901140c0058814025140d540d070114000e545941d10b0201143c8000d82030603c12001e0020601900003400c800b405241d00c00d1600c40e0140c114405040320b4801201c0e07003403000d90310640c070601050080c0d41b190705c03c41c0d00c1e0311740f0646810101c43c1942400d850b00c403c1c0398807072074903103080038107030500480c954018008581040e400e42c40d841d220f592503292030702c03c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 899159469 1250 899158219 899158241
    0x709050a030f0204150510020a020f0904020d06050a0b06070501020a11010203100b0d0e0a05160e250908100b1503150105070807291e060114120103030f0909 69
    0xc102c501950141c0b6040e80051482d4222000461100d5528030104411044450401004d80c0140341c10300b065082031120341d6048441151000600d14081d030004119000000014040300d945500041109069510034001030400a06480d01d40340b583c40c0040c0030f0740c004005c0302d0001b90354010401c01b4002c140240c90103140d00160f00841075007032501c0e200c03e68001c40c41002020792540d010107113454003804110107182c020009001c1000c2c050188120700d8201e03034002d0043d801054200000c40e074190001c2c1c88410302c07021a0040b16100000c0840b000040c0707130031401181c000e0b0b20b000d2880c459598055041e0b1401651803500d02001008c10760070901044175070601c40e0b2020707521541190320600050400300c0c450300800d418881a6240d408210000050b428800200f00c1a0000009081c50704a07620910307001c0795414005200044542c0302402a100303a0502441941ca050f9807070500080c0d8032411034401c81003c0035030392401c000741540900285c603008105a6580800c616417507000b07000942e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 899160719 1250 899159469 899159483
    0xf010c050a0c0602250b1819020118080d020106050a150c1e0507051201151703070506090c101829130303030c03020c0a0206030903040f0e0709050a03 66
    0x12036580c01600d001c8940c80b821100d03590308108180c06a02e48000500e04000c48400150440c00c003494981c043c0b64000e440e034011140482d0351032102c07030b0000803070051244201003a07582c41e101c01d100503503100300b200745800c0121401c1800458500c0002442204584242d802404155500c0040c058103690502450b204000004540020309010f5886850708600c40d8400035051200f01020068900d00b903203045074241c0007039000700300c00d03e4069068000f03034040b035008220134150784000c40002111846640f01443d0440d00c160b030862400d00903074441039000002e4490034504a41801d40b1000100d8040c0c5c4540010214500141c1c400c904040701000c41d0040504602e041600e00c1040c00e03c00160305085d648060062600200c2c00e0010302202c0700800e805440303840c00c6140203019512103070590f008151040c8014030755842c00084144803203406031401a52611011038880c15441160881041010038581c002111480c142083c1d02c40c406650350035000945038000c0001480051101603c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 899161969 1250 899160719 899160727
    0x609050a05120f061305240402040f0b1306050a0617281a0102070e060a030f17190e04020304081c060503070f0512030306060f0f0c0601030b090f010c05 67
    0xd082a65985401d0003a0300b040b60000d10ba4a0b950a10b0030b0011a0f0b8030b04015075030724900e820000100440070803002e0b12003907009030310741100c0b01010011009001910464075807084041c0301203542e204c00c00844015060154640d04178030100b001d08602e10030180036035400390000030442d11036a0101e02c45c041c11a40301c10140c50784011409035414640b078503109030304100c0002c0c40c1482140704000402d000600c0c80c108003c20b400c00641030544590004480050813000c2002031f545054502c0103503684924094600c81d29401c0540c404040c1d01400d104645000490002948414882d2240c0600650f141407c035081d41e014441a408251002007940e0f03024050808814410b0304d5a0140384010702002640c2d543c0d600011345494082c0e0300c45101696205014809030070600c0188918440000007903256052140202d5801c1c49031f20300c1552030200100750030800400340c000b20383c00d10188030102e60f1030396124181541c03461026a6031032028401c10f02500d060310341c1802180f000e8081030f1503881c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 899163219 1250 899161969 899161979
    0x3010504021c1b03030f0e041a1512040827030a03140904060609081b0a090207170f180d0308010b1309060e040203010b01180b070215030f070305010609050a 69
    0x10307002c0b9500044924000c410b09503045405150044402076000e660f43d002c03044007160b0041d00000141010900075400e000d452041602c0205c0e174400708030400c2d6a0106000c260130540040c81c05100100e00f41c43c80080c0601007804a0300f0050410703201c0c0d41c82d0002c1c91750300c1c2c507000300c440380c20341081d103500b40e04599200400b090040d520001ca00c20400d0103e0b15198440c00010120388440d0055404a41805428460305104100940b8100305075840c10600910f2036001420343e075020712a030800c0c07070b80020301002001440c2ca2800d60020050582c00d8a03490511904540303034106070810114030940b03451a2a480c9004141e162407950184c42d00c409690811100071415406400c210703076004000740001800e25004e00c9010010240440d4108290074a40304050940c0d509a80c41c2d41000b607244622404d205032401202d007110720b844101c2d560307107400d03102140d55064a6011a40010008030400600f42c0c40d2a035018403c13903c664040003540c1c1c8a420580d034001441c01010740014003a042489 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 899164469 1250 899163219 899163259
    0x30c17010e0c04080613032a0b07020703140c010e060708090103200d1407080709060f0c02040f0234060e0a140304170111030c07020a2c060301050402 66
    0xd08000b90b940d603540b0302911040c405107449030941c1d0807800041c161801e60113142e40030b100b900b0101d0780c1d60880130326600c900c0341e0b503000071b6030420300604031f45080804038540d20300800511000f1a070140d4141202020448541d490300c002544941c041600242c0b100c2040c42c04604681010354030402550500346600300442c0100b884a0414000914542d41120b04081e00070181c4075040804034041011220500d09610601020304207506210501d0140162950000c065000355401ca1402489100c034000f0200c40c540b0700020040e400614003603070141080015002081c410550700e4550040305150210441e5a113803015a039484c0d00c190402810000e1080d13003100145a04540441c2d480c20025120180450000040f0002e2640006020880740d0650210f08170031120000081007124542d040340d210710f10000b05070300726840d0000351100031903850801000c060014074030041c091070140c603a41601c501c00c0ca03100361415010400011003074503050003264070841d130203465944045d10f5104005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 899165719 1250 899164469 899164471
    0xf0e0a110f0903070f15030605030c01080106140f0d0b01230d150f0e0603160302300105091e1204030f020d06020a080f07020a0b010b031b0d0c030c17010e 68
    0x181d414044c800c80024041c8002c40910051b04500000e40c00e02030500e00084d01710341440d440503010350488801020603a800030301e4641182c1460502c004560110400d10b03801c1c3c800c038807031142564804a01543d024906510051414400b0b884640640c0400542107485170f812140c54014608204860b94591059800140400e1400c1e80542c41300c07505c40c0406885040350360040512443c46034100409442c0070040c8103c280031515282c03000c241142c01003800689180c02e41c4050f07100c0c071a0170301f007410200e804101d031608900c0c008100d541026640c0b86d85507103245903805100d40d0801c4c91100350400102e015007440f00000030719481e152071503403100491100e4480a0b0780c04040e02c0d42e024045900d03030000b4a21400075544040640c5000c242740e214540c000340034001150b00030031102d0300103070328141000d0559440031001c50300d80d6141d0314182c000030790103034180301c4e0701e000815140c0038000e003500304409a0340f468030140061045c5090031070b648a40e040c000039481004100422403008051507403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 899166969 1250 899165719 899165737
    0x171c39051303140106061d100c020d030305040506070906050d0b01020f120301091109010c3206010306200a0c03021014100501051c0203130c0f0e0a110f 67
    0x105061190360716001d00c81507055401070f650748404041403900380c1c1080c46030a0103041e4505154980340a1110030398090751840030158011420000c84da0310309401007861045842e4010b104400700b0700e4910700203000d032105880480e81e40c811070011400c0d890091141130305403402555000d040180c80b2600e01c0c0540480001c61b4194000d000c840083c10710b044c40100c511103442140e40b0ba9a5240c4156a412540ac40d0014a40309806210400c8140e07804840c0400d9603800104411a42004042071216641203040200b034206210608403540c0d4000f0641504032400740200304141030009805010881c4c108440d40b11041042054402040c0070714a90000180640304076810304544c0641e50044860740041c1411550f004020000d0a040044111019203400c0c40c1081c1080280bd642d01d19551641038094411900800000d404d0542c00e040520a2500b08940740e10144c0d0750740e4044202803203801540c814010040008446072080e00881d002c074541c04070403900c2d044900750010b48640282501d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 899168219 1250 899166969 899166977
    0x1020307170615040f08070506040617040606080118150203251403250f0e1c0c0608041a040b060909100c0e120601031509171c39 57
    0x8409000d100044d20103495040410146641041e001920700314065200900c034110030001409038591003000c0304c107010486420600d564a4030302d02200500342c036400c180c40719882c1215500b458000d12180c20002401142070300c280c0c20042d4140416841704660b1408200b41c000c0d11000c2c9a400103544001c1c41b6050714048500380268224001282d101703842111107401020140360702d40c40c428401d0401ca1501d400c0c0101c4844010102400510040f842c540c03240841187c18496602c03d00c8124140542c0146425070140d1500d41c00341100c08280d40586408841100c0280c81c0700c0315196060040760405400009030352803100300200315100410b0050ba90040c02c03544603c1b0022401210311120341512009211607401c818403a02d1a00e0b0401110964001001080407070070b2034410280410b400c00010824481600781003012074102c040c600f441e181c0008a07070781c40801c0c00388079580c2403080c05020301c03501c100c09121b100f45003444401411080c908034200c0301580d050442500c414106410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 899169469 1250 899168219 899168239
    0x70507171606022115122a01110f0706050903030f0403080301090506191a161a070e060f1b06010603060801200d0b0307181b030c050406050702010e12011d010203071706 74
    0x7044c000c0040715202c8005007c089a0080c03040d41d07070001c03e4005401c021030020411000303c40001d5581d501c50341b0440003400400506140345490a0080f2000328400c4120959520754070700d00713040c1540c001d08c07481c0c1e005881c00d400f182041c40c08030b4480f148181412020310545050046c05030945096010754088510300304200c04010001000c1005424065018068080c95007a0400103da40007804d090400007801ca0443c0f155840c81d055800301c0c0c240c0300506480303200d0201d02d070400040d041c41e255118404c0e04000254994150440000c0e07410300c500910a04014201c0d0b40c04511090040042e080302c02e1206482010655001c0c81d9500380050840340110754590f0954140d24440c1c0305441c00c2c41d180c1000303084d20040d0540312a14699076290030407581c1d0140e00018414000c0d4090131042000019403d825a8440e6100008600c0300504012030744100c1d0764024000c0c050303010041c0400000c440007900540741171082d207110b0f280350381300c800d041c660303c0040c8001010f004241d5540440000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 899170719 1250 899169469 899169493
    0x504030c180b0d140114060a06180e190e0a030e0402090d080d0c1e050f0705070801050a06030201030b090105130e120f031e07050717160602211512 65
    0x150f031a100a004010400c01a04500da8141c02e440e90f0580c401c03029a070072000d2002c0e5849150001c1e084030000d1400e420101c0401100c207505807a1507100013600078042c000d111000e00840c07101250900480020003602000c80000f40d1180c40c1608064003040b40c0100201090602d90001c2520710b800410072080b01d0001d5581583c2c50b0003d0360a0412240d46821008410350271019259079024a100c1800280e4034000b07000300148201c50f100d449442d00030515100f040300410009018010500007800149481c0ba01540105058401a0f001900301030040301242481c0342ca142c10f07170314041c10b0700215010464000020f408440440d800a1103192140c50454098402402182e0503800100f5038900380a0400444144440081e0305c41c8040c02d01807103c8d590300711040300c2c40240d00c00d64211000101d8241d00c0d0b020f0084224201140c4120020301c41081381a6006168600303a031086040600c6000c82c01c0100f90030101c0d0340001d550440910402c4500d08040070045042c031420464010017511 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 899171969 1250 899170719 899170729
    0xf04051614010908060c0d0b010507050d1806030507121503020d0c030209100e070c02040e1006090507020f0c04020903071701020304030e150a0c0804080d090e06010504030c180b 78
    0x5030340401818070114802116541e405041003004200000081c04541813440d070000da14450910407404142d0ba50002c1040c81e40580b0664420700d80000c20360f1000b181c0d01030083e003501084054a0640c517107508001c0798540c001e20426004d51699a05c55022041c034001c1c902c0102032101d00080103484142000006a4441c0c800250309880b61042c078a06030300d1071040c464403450151200c11403484c038600602010031031124003a48041c40f880c01d4140300f0143d00204000304006079500b0014080ca40211030b01c070050781c00520488400c40302c2000075540d000310403a19104c1408410b0078517000081e0384641e41c50070350064000e100d40182030301e2100342c1e5400111188420302800311882c0c2d40100070401459080032581c81990000e482c0044001c0184140c24040e118146048081c00070081d0800188501d0106540141c6602404c40c2e6805a040750b01808061051264900c12030b0034500058803940b1400a8400302d0740d01c0070b50403101e01e0904508000082c007054014010725550100c90900b940c0f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 899173219 1250 899171969 899172013
    0x150809031b0705120102072a0e0103030f081b0403021e0402040602150c0f030103060203130b1005030f07050a1502010213032a0b09060c0a02040c02010501061106010b030f0405 77
    0x8241d0040440e1442c000602003040310b51918500e041c1d01c18440400800c00003000e0000b04040000100043c181145031418800c609812210741c440c10f203030001c410140c014032603240b071160716203400c04507660f208003401c40804c1c00c10540c1010300003444108014144002010904000c04500030420b10072034000c2002ca8020b644a400140d011441c11405011451042a0400f504146d191b140030f44488041d01140710620000782003e03400000140405020400c4c0503d16900428000f0349050150b020341005000e4010180b0078000d541420601240006250040711070251800d081545400c054410461244a038074055540801c202d82045659085490181d8420900740003480113054113100580c44030311900070302250b6420207100c410060800d40b0300840d800c4440c40c3d601d081071109141040483c0d00001c4d0440e051038401c540998041d080a41640c810f036880781480068404c803541d03030705c0c001e02c0f40c2200301a00f0800715400700c0d60a9129030f40140280c0458203400c8901030341e065088a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 899174469 1250 899173219 899173267
    0xa02030604052415010f0c02030109030519030219030513120201052e05040c051e0304110306041e021c050f0c030a051f0b0604090507080a02030115080903 68
    0x15009030300400009000c0701100320481c42c6a01803450f0003540c9080c240030110204d0f0500034040500e01d0070781d1250501d040003a07406802400201d071940b402402c41d810031440034041c030400604901d42c4c20310030f2080e82c0740380807595022404520644010740007408040c0655606241110395440440c400503018400e441140c4d000043c0b07403400300010088460340d41d00710461030342d0300e10701030041303081c20701c3d4400a4490440300040c1c2c3d4801c400c802d80d100c0c03080c0c0540c44d05070001c07041104070b008034500103507200d00e015450000403503581604164442d601214020910a83d140345106c940c2030070381e0b0305240940f0203000310991f8500c42d14078511621502008480c654071940596500c20400d111010300090183e0007800c101849645854544503150007896407200718030040c550144080d00000e100c0307080642080c1e81e60307440d15040f001801080b954200804e90000201d02143c0040c400c0301e04035512002000030b10103800900300d43d416005403001249200a02010004413690950002c1000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 899175719 1250 899174469 899174473
    0x50303010b0a09090e03091905120c030d030b15090406090e16050919150302120703110109231203030901060524040b0d0608060f010306050f071d030a0203060405 71
    0x28000c2d5002400c01c502900101d60729418000a0400c01c08000103403003051008036804c4108900d052001c1501b41c1459110a81c0106001e404000d00d4101080e1315141420070f40c00d03550075450703220b800d400b40c606480500d600300a02c40c01d0140402410b00140916030401000452001c4da90300d00d940c1036560958021400e60014060300c0b440700181d031009402010166003070141498540007140600f48020184441503454098058501c240c044072600034680c01003914000062400d0b1036a0754450b0380c00f0032140c00301110400c014960189912034103d401020341c0e0480000c103981861020f0100d1801160001402d1030700d50000c03801800950712440c81a4000101c8901e801c00700100e0505540f000c00d4408002c01c0f00f542c524484ca0101c505031602d1071040c507a01c040f00c40148005107240c1d030041803103001c0c040034031100d1290b19020714102c03806050240119200d15092003030440c03058620790b02160000d506ca0462030200301080c142e001006003901d01c41e0076035401081c1849400c8508135419 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 899176969 1250 899175719 899175727
    0x30a050603210a0518060f04060f0c12110c150306011209020901170a0f06020a0807021504060b150c010e0f06090c010c08190e031213030f0807050303010b 68
    0x1c1c1020815454070b122089002280c00384200459080c1d449081c070003c0411400203020b440c1c04980c0505030505020142034036584202d00b81c650350aa410a0085000050242028401c9140700d80c850b403900641140522020940b00e410a40d807503201c50b8074003038060103401001241e41c1e07a0340000344a01420f6800d20342d60f0f860908001898070014655582c0e9103442c0070b41c80700158640184139415140b01104003503140003d0b03140603141c070101c1440103090b0b110070000503040117500d80140c00150b07402e840d004155181c13480243d0f1200312a003114400c4404580019003c100705402094040f00c000d800482c00d038501c540b401c0c90b40c3d40000300b128101d0303458080c0a1844a003c01402d100d800c02c1501908050918850803174642140340c50560400440e00074030350a1000f91811543d907000750b0952002c06165408024100f8543e05010a2103409a900c207a8414204002261036900d21015001c1c4600d0444d40c54078070f40d40580e1010b0755002c200f0b000e2840016003c000950107024840034080d11 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 899178219 1250 899176969 899176981
    0x1c02010b0604060c02090a11030a021207090321050c070807030507271a181005040509100203040c051008100503030403080d0b0111010c0f20060c1806030a05 69
    0xa6521840025010700030070030040210300d6111800e5100d1940c11140008561182c40000003d1f06d031071507810b41d02400000503c65082103543c0101a410b00c0100640060355034650159103540e81c85c80060191194a0300f00411003055066100820b0700302e00b030042c1089030700f40c4083e1a045254002c2d84e41d0381e00002060060100401200c00200000ea0031641c4503445828510000d04005074070745105511108000ca2105180003814002400905100050746401c10032891707c500581f00310a0380c00d1f40c80b4011949040a00806200303801e01c5004140d2301e100039820740001e42c00100305a65001c40000f01042c2da990702107041c03140c2c03491035403400c006050014801c416030900740e22051095204100800004d1000c0b01560400714241000103045d4500e4801a982044000000c50f501c2d445c00407001c07c41a042100301e81c141d80240e446031344000003e18040c100707400b400e040318210f41c084070026000b07140791001811190f207400032110f80c602000c8045000307500150742c0c0c807250035210030801130 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 899179469 1250 899178219 899178221
    0x2150c040807300302030f0d020a031d0c100e0409050d09290a03020d06080615010503060a051c08040e0a0b1804021201060b1c06050a060912030306081c0201 69
    0x2025001c151000320780707400040211000c858502043c00040d12020111009050091059a848108071001320360341d801a40c203007500030750282c0c03415000301c0d18140d291001c0c445c0007865542c1c440c584c0700060800c82d1300390040001c009040c04510040005a400054541c2c030345000b8480354600c00c0000b40400001507501070324a00c1356030400c0c0d14045200004000040e0408054040500100000b40c1d503030781c02c10b1044006e44251300c50400710134140480010401000250640702c1c1400785c7c0420b100488110044901d4402940d4850744012842c2c010f20030303407502c900c80c3c401c201140e41ca0440c41c048140e0712611f05412030b501001003c0009420444400294090001d203904101e5400045006048503c8110303000503002a00a628000e4a15100082540220007404403580400c1d11061449010301c40d103403240308a0841c40c1d051180020b0070742440510102505d400d5160910174504160359510441c520395001e90405885a81c0054401c43c2030040d51002d680c94103005040e40302008010b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 899180719 1250 899179469 899179483
    0x1009020c0f0f210d09051e060a0603230307050a0b060928050408041a1c0608150c07020d12020f0c01020a0213021e070b07141902150c0408 61
    0x1010b10f40080d100140d0810b01040c0f442c84a8003031482450300d402c3c3c2a00010300402c0088401041441007000400b486035290710151000002c82c0f0858490740c3e1081c0c418070584180b80300042c4000c03100460140c072034071800e083d107142d400802c00700c90400c1c0072500e810f880c040031400160b030b0079540401480003e042c00301840da40f10901180c40b40904504400c6102c0d005407200c0d0408105541d4008134081081490440e40140346002840300558040c1100d40d1180d03020341480581801200d4024400600c6401001c04a8441402401810070b0b40b41180c003045000400410311240100702210060343d92002d070301010b501039202540b0351201c1038800303880c00da4031421060241e40140211000c0380e0b400078603030034400e90507107204480600100c0c460b400f901800700c08560b1619480e4081c0c03d41e0050342c0c040d0602e140240800e104684850400f9299000105583c400300c500c20462036401040c20320a0300c4406540c4d01c100d61410001c056800c2a81c201a110711940a10008040114000070800700c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 899181969 1250 899180719 899180743
    0x92202070803040b1b03130c0e160305010f060e2e0908060a060f0501120e010f090201090608070f0c11090a0f0605090603072601060f05130209181009020c0f 69
    0x42c2071040a601071110840c00700400b5031841c2982000c2500400c01680c034010300800302750f41c08500505000441110704030055a42178002460580001040c191085810080700d0f8140c64101070507000300284150005041c903100d2041c1f0121846080340015034241540c03040140c3d8401071078a09043c01c05050000c003502056985007005410710a05204e1100c0c001212004d00784a02c114103905881c1c0c000e0303d204002050694a00405000010610b03003188048900c01d0303840300400f40c1c80385d10070b58516000384c039114006010048040002c0d401003007201c10a03030003490b9a1403401180701c0080c1e0100030447d4218a41c0e42c58190f140c2943d40c80d4092400541740031540b501c100c0c90030304c010ac0d69994081c07094a00c031a42c0a02c2e50402541c000c0960948083e441000f44040398544c801c1e203110355024860140a84815201a110f88a0b00d209480712103030001c6c10740c104258441380c2d200100001914250b003141002034006414802c0d0b1004244079440000981804124034901c203080c48620501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 899183219 1250 899181969 899181991
    0xa09051e1318200a0e04030806010f0e27180a0213090b1612050613090204021903050a15081504060b060708070510060605092202070803040b 62
    0x8a0203196440365900c0c03240014070400010b14164191a418140718a0741020300424003105a46081100701c1c0748102282d5070641c0c0e0120790f0759543d6480300303a22004580107000541d110010a51320b43c41400b56108100355458001196800d0100040d520840d00c0481d0040c6445c0c2d035141c9200c110341c4440b15504c911684cd03280549003490341607a456414009009200302c00b00000141000026404140030b5500628042c3c654035141148681c101210312104000c2030607100514445146400340f2807052101510420088818005010150881803004c0345d0041d000e00841030114480c0c0c0003000c0d141000da07004141420a01c031043c0c22030710860780240c10301e00c04280c1400360460010310f614910300c06206070700e8030341d0300c50500a0061a020440300da01417800a030900a1010782d1002d00b807224042c1d4265a11700c1079000300d11086941034440c00002c40c1c010709c024942c520f44609032088402025054807140004424440204da100c0c41080fa02c0010100c1030205011440e104c241d449031000705c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 899184469 1250 899183219 899183269
    0x301060f0b0a0309020a0905012c16050a020a05061f08031201060507080d0603060c111612150e010c080c091309050a1a06030d0513030305090105040b0a0905 69
    0xd00c8591841200c8200302890f446400c4c0c3d80071500c612089000501c40001c1c108480d58440840c4c081d142e50000e110007885c2d04181c6140103102040d80142c1c003034079186054100603400b510064409410404401c010350103040c25100200e80c00340006403180e504080ca007403500c55241203c210341840342d001b6408980c8140010810b901c80002402c1c10f540312410b24030346070369492078078106510400b18400318003414008000208504c1d40c10010a5121341c3c2c030348104145c00b0811140c0d858404100785118034140110421201002c55514813066000e0b2040b1011080d02520003c2070726440d142c02c41040c1c0d55541f038904101d61214070103401c100c1b00c102c000d02e03103800d80740052001080041c84c90b41c055503800c610001c010041004502c2c1e141c6c0001001c02d02c6040e00d2210a50860844099019016019111500740c1c460303800c0354403000e1050a1140c8050031610203e17642c2d080700c0402814448200404252448804003a00548403d9540e4090003800c1a080c000821101810f07240c0c25000d80b8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 899185719 1250 899184469 899184479
    0x14040305060f041401090b010611010507090603020c01230703051b0301060e12240c0f030a020c0f0a0606080127030c02041d01050103210f0c1b0902090301060f 70
    0x100e006900300c08110310400c2551a1404c000481d1200303a000394009603c0d069101c800c01200800c118100c500030b45503500c0c0442c0040f02d050030f9420464649000424a03501404094020ba01800703541802200000d18075004e1148021000004c100049007200300c14100070722990315000e0b0340d51062050b915100450503070035a1840314001800f5002c1807009003803c1e00d00c244c031110396411000090a0441e41600e01c1400c80940c4040034409001480318514002050044035401700c0b02c001d907008111a1440e915444500d009400440c1c02600c1c5d809801c040c540d6640e4204440b10f400b900462001803003501d440000e07402c44040b000381c0940481c8545141d071805584c2c034ce500d0380c4c0541504018408030650b1000500404205181440007809086031404810b015401141a644102400450006c000901000e0310065078030000000b140742100c640346610a010f030f00e48403031043c0e04181d07070240c2c19140c2103032450040d084000210384c04120215540b03400d002c0c0800802c148881c10303207118100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 899186969 1250 899185719 899185723
    0xa03050f011119050d1e2306010c02061c021b1507090e07021c05040f0f0308090d060b030114070e09010e0a02090a090c0c0302210306090a090605090d14040305 70
    0x45078141c00e01c540856511401120f5406c130480250002009400c0c41c120801c00b81d000b41040485221018180114940c64050fa100c00e030380a10b41c1610ba182a1100710303420003019074440c0790794020150080003c0c408000c40e50000c2c00c860050a4903102b500e21024400b9480c0140c507400709100c03413035103c041c88220b40e00042c0302001e80d0001400611240d0b12420240e203858081c2c1407103008200e407010044070706d43e4441c02400540f14804490120941d8610b0079a030707101101d00024082c48420488121540b410076007420942b841001302056a00310b8030006402c58007072140b1694540c10709000c2110059000f10348983c0e44004071821121541070040c0309405c1840144001001030303000483c205503564020624004103809502403001140001004003c0311041d0021800f510a1f10684002c11841c000d81290150b414002e050840da244410400d144c4006085516820b03507a2400394045012401000d00c02d004003c0103081c1013601e001c008181403441c00e06191a61410301081c0000b0f040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 899188219 1250 899186969 899187007
    0xe030f0c1c0f0303020a0509100905190f09022b0b0a1706240a03050106061b0807020108070309080c060103020f0319020d080c07061e0f0c03031a0a03050f0111 70
    0x103203030040c0c80c0e2040400580b024440d021600764089c101c507600c21046944441c10100303403001503507241501c1c1120900001c8004290045003400e40180c03900b03010031403442d400780000c01104590784c40b0900070049105500c0d941c03c0c205080c0c03a51105103e4019061401c00c41008100d10070040f5000b44131140300ba6101c01024ec41c600c11800b44042c20500c200940b11040064100100500805070ba00d02c0c001e4000c2c030b450303c101c030003081da03040c0380006141c2c2c50a56a039846402840302d6107030016590045400c000000c3c60340090580d170b62150340120b420381002d4003001042500034202e6506600410120148100f225031180c1d0080c100403900b005c01c0d5449584456054840400607012494990031030f0040800400a9102e003200004880340c1c82340004104018000d0b04807908880b0b4042103801582020780d1201084c51468003400080c0320ba0300c040103040700b5907a0f00e0300c14140000007403881c0006600550380c907408515440640c1c00d003032050030040c05291003c1441c00c00c0b215149217050030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 899189469 1250 899188219 899188223
    0x1e08040b330a30080f0a0509042712090b030115030e2802030709020c10050105030c0d1e0819140301030c0302100201020f041d0a060f0b0a0e030f0c1c0f 67
    0x20420034043c02c000000003900e000c0d207180040c15440e9900140d0090054204d01c4a082c81281040c0b0a04e5054162040f40c3c04200e9882d075000400300a00d45424921101d005070700c004210147e5000a04144800040e40c007808541070808104c00449100030240c98000baa01c5090303801c90542241c8541c1000b001201b004890840104419450b000007410700d40544d002c500711900018071040040008600c003825010fa408082050340d803039405041e5100c0c84065150f4000000f4110303000415032200394217410021004d03641c01000119910700303409400102c0c40308404500820040032041d04038080e50006012a07042604562554442a4a0740c009210103402141100e0151007010301c01e4040318880c80c40000059952a40c1d80208442c0904500c0e5080104a0502c049500001d190260078200c420038100302d8812820302442c08400d5002d004104c044c010342c0b4081641d02d07107040c00708070301221800d400350000b100c1d0f550a0061086948a2280080d500c03004804002038a80c0300e0340c03503901c1e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 899190719 1250 899189469 899189549
    0x309010c0e01051b010f05010f03150905060402060c0115090213050f0f0603090a14030d060608060306010303031518270812060109080102030f04031e08040b330a 71
    0x90704c0c1001c01c80c0107168030060b02c400c0c6410540081600d0005d400d83d0022248143c006050740c0d1503940e00042100c1002d1802806500000041005860308401801002da40ca0b000040d07001300944920704422520b90001c0c1100381c0100b43c42c50207542440c4114000d00b015240e40002d50b07c2140041c103241000e15110344034850210218100c06402c0011945196002c181000b010321201070b03180d982c0d002801020030980c10040b01040d064410f920480c00b450000e002011140d007183c1d400d4000d0043c0002e07110007c100440c0000340b1142800c9203010111000d48001486000031503076514111100b0b000b0a49045900d04110000300694100c0c0d144100411904c00145c48880049a0170f4490340d11419166002106100c00c210b8040e07041c500451083d221038440c00408019103180011021010001c0380904002601060301c050807030341d005a0386851569406000c04a0f85035403403022144005403091502c0e590003d050441c84580540460402c10100b02a004c40104110b0182d0311014840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 899191969 1250 899190719 899190757
    0x1060201201803160302030c0f06160203030f070b010509151011030f0c0d081f17030c0607020a031814010509010207051201140a06080a02120a020301110309010c0e0105 74
    0x45005464030b070440341004055428140e82e100b114415030b007039400264400e01603e9803138501031070410040608003801034050b6082010700102d48130340b801d807500282d8050208118000846c0103003001031030603600c242c3c41090203505010922148400080000c200c1003800018110550f4034100c4400030039500f071808641d5404068070791402c40c056084c1200000002040390201c246c0c010031140042841039549165a54801d02501c13403130959401b0b5000c3e100d407014001d100e620b2511420a80440140c0c0440303190450010a1034900082295080010f03004002828101a480f98040c444040f41c1e0311120300680c101100110b404030440201814420000fa0000c13907a402400042c0040c00024450303405201000c181c54060080c05480034041c84500c1c0000d0f0400f90a0300c202420740e481c00c3c00402d0801826030074040d0030441110009030703a105105160380181e800740141c0c07410264800a21380c40e404c155080609684020b59480140501c2001420450b64800d0646058841e41c906038418 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 899193219 1250 899191969 899191987
    0x9011b0c0b12090f010510090e160e040209070309200f13051006090315020f07050708031c090b0f0711060a0218010504030807060f060513140106020120 67
    0x600c06859104000020340803401982c6800c0e50140075210355002c0c0d05641e0401e8000020900701c80088440d070516901c4000e0a0100c000e440e44840e41c0a5412401c5404801c4041000328000300154407a2050101c0d410030402141801d02c0c000380c01502d6418144100385041d503400b50700550000f0000c6080a1512010f01c0981d0b4800d9203032007504000e400146000c0c003c504481c050001124412080101140c000840c2441510b02d442240d4001108000805d051901c2c0800396000807045d1000301028080c40c0d001c51010300c50000141a01401141c0d21501501071501c0b4443d540c1950750810b00c2c1c1000d41001c5105802c015510650616400c903e507a03070146c0589503400c001c45040c0162060004100c06401c09030f0041c0141c191000b06d407001ca40701000112218400d5001c01803a2000c20b00c40440022190b41002030018920600881c240d40c079040418003d0308091410000151a80d542404003e50a0515405000c592000b400b1100384440404031089011440801d0b00c5400560810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 899194469 1250 899193219 899193233
    0x1912050f04031b09051305060601050f03010e090304032411120412030e010e0f15010b0406080a06090908070b0c09031509031902030c010c020114041b0b22080309011b 73
    0x1c3c0503440c6081055041189011381c6c098a1a072080740c0301e124184c08500d0640c003032016198038003281040140f440c0e0800c03888461040d4083c104080510080c080440012040445180500d07030a070400002c41640250820659101910051780c0840400008907150b580700e05041c0c0c015003002d000328510340c0e075075400c0340100100070700800c8cd5407a11403036204494000c00c014988d08082ea080300d84601d0004a140c0c0b21040030b2040d11484001000100300c214011002e6590140c0f04400001c0c00035514000300003034420220040b40c0c0a0700c001520300c100040030442980054011a0103400d1030500d00c01709541e0003e40080d9004c0140b03443c0014035900e000c104450ba8200c914100010f013103103403800650323240c00075000c080e82340d4249000c200c02c50f44144a80b84030b004002c0f1580c64036495586401900c0301400d1018900c8840f000e401048104420006000c0303001034245100e41801c04030701c107003218401034000c2d4001307030410030540e000780c1c2e40071080780c1182019074000031210030707540381c034803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 899195719 1250 899194469 899194523
    0x30905100222080d200703050a21021522080a03142a0903010212070f090501080f01030b190c0c060e0a12030f020c1912050f0403 57
    0xe09090001984100029180320b0030104500b02120030300745182c860703010715182c01c404142c032800030b10540002e00001000c880340100c2d40c0300326001e88419030341385e80f01c1c40d040000590302581d20050b202004880d06200e44403484c66003400d803016211314081c4603c6109401c1c4050281241801440d000c0461510080c5c009045694440c85e410f0b0b40d0740800c84064040c0c04038001c42071182d01c9590000e03201c0382c02c08a841400d410b02142c8140ea00127001d14884642e0031000781c4c00c0c2c0540d404d000d004250000c81c02c42c2801100d0356103501b010201d0380100182241c805400a03410840d0160a00221107800107003241500c0d0f000c00c011140d1340d24146044046491580740d40045410110b90042d1542c00880b20715107140600014807404260101c2150b43e214404c0d40108a200f0885035004101d1003603101403461a207594000d0718000d04000c0d1141340c041e11301b07264107018020101300c03010801e9006ea100b403e072006050040c2441e0030180054401c1c001c03488098000340e00600941a003c01d00b0b0008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 899196969 1250 899195719 899195743
    0x31209030106050310050a0605060c060c1602040f2403031e020102070c15031b05090409032c1806061c0609051e0703061404230403110105101203030905 67
    0x20340342c10417003000700c00182070140c032070807484d500c4c00c100401d46080c04002c071030729442881c0040110792245024020326a104580e414000707030721000d204005942e203006030482ca907161400400c0003113407101c5101000904940c0c1c442c05000c01c42003000042d402c000d80d00302000f0b46190340c2061903141d03003099001e441070160090007001c0c04500800c40b140740c01c2c944031108040ea507003040724460240c1c0c06d00b441103c0074915030118100f03000fa1302407407800b600008902c41c0f0a02e0300460030300c00d10001c50101c07084a5210146240d818243d142c5600305001180c42d220881024444c40d418540701003102d070710810342e403000c08248282040d908460b8540001000f00404403003000903281800078100500d50140300d2480803044000032440943c8213015840590f500350f107410403601d42140422000304010862452200d00804010040070340c030030801d0384568002d4441600300800c81107a00d003144d070700034501c6440d10401001030080401301e4203d010343d03e5160500240c000030700d05066141503401007603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 899198219 1250 899196969 899196973
    0x4110f210703120f030f060b1207110115060314150904260c0d0f09170f0304081627020a020c0a06050903010c090e13020d060e0607110a020312090301060503 69
    0x380403c040d602c104e40b1110250346075001c0108070741050700c110540300944a0300607022814011203046200c0588080e82111950400035203625101c0d944500356890544840300c00303401100100100d42e05805000d10006101304444d40d0380c600f051140146502c02d0f840c85005e4041d07440003030108190310740c6403e070b0084406082103050a99001c0c00c00264880bc50341091802190324411110b8000c0c841c4100c0c00c501c58036400002410100d1002002071051184c84161094561000c00b54100780000c001400079100540314240302c880710708041c04081e512440340000015403108060301c90001d10105008004405070f600e03a03200f10f04a00d000d00c0c00c0c92282e80901800340020310307075030441c3c01031505440c141c000303000100c2c105200745c40d00c5c1994402c14140700c0c00b400008800d4203080d4480c0651500c01020031107034172807035103600713048440b0f61188003085d41c4070f103091121241c2c010030049081c8140400038001c0003040d42c04242c07184d002a411a10400010034003000641c0c013900500040d00307024007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 899199469 1250 899198219 899198243
    0xc020a14011b020a11060c01090804140a0512060f070c120903030201050a020c03030115050708030f01090b060a0c02040c030608030a0c0b06060a090b07060b1804110f210703 76
    0x1030028020001d08003001d900242c40340c1c038503240d1400856074192085c2c110b008803418640b00e40034050503500884491400d55a6001c6600006036980080d00c0980318007506804d0210313a481c00c0c4580e14074290003951042807529a0f83c4000800094410340c4004912000c02041d2559032042e03802100200000b80740e014011000c031100b41d44101108101d0780698000c4c4501d48420307500e48120310507220070304447d8100f0001400307890008001c0e10300c42075141c6010f624000c6207440309000e0303410548411b03030702055400040000104601608044040494907036107030418900c03010b41459007884009005a03261806010542c2c082c1e8800801814000e041e030b5620003d41100800d44900b400040342d1301d01c0e610010400a04150068a0484a2a031110310410342803209048064028020031a00302e515011540c0c50354569400e800380b040200d00690030f05041c64588640c080c24007060301402082003c425070003e90751b5101014026854512100524042070325050a1196079040906440c10441c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 899200719 1250 899199469 899199503
    0x20901060302030a05150d0318090228090605090f0f130c030e01330906031406070206150609041130040c06030b040b181f0e0a0c020a 59
    0x30b00103604c1044075050400c099560442c0d500920300d1011045500b162601108000103401954030524040311003040107180d5a480c03414005aa01480d18030000c400211003800003007c200390100e039900c1050130040199424104001d00782c4c0191005244218031192801240f9102c000f90b121900c80f002d0044d4014886400c1e025000d0580003c0f0100000d14110594078032100c180310b20120104011001c1c2c440d15225184000462030742e00d4030701804203c81100042e1b40c0e0700e40c8030389401035118001655401d4000f0144a007041402084201950440410840301400415041a1200044981c0c0d51a6002034010a0080c032001200c4142c09200080e03600316003400301300b8100e00600020801c0300795150403050a4010000380d400a01e00b001c400c40910209002ea001211440009003001980412803000540110401125401e54400c403e041c020b0741d4240000c2000e0040000740c0d142d21207480c042044480d9103008121034451780c0e980848620b00c1e482881200304030354215060883c505110307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 899201969 1250 899200719 899200721
    0x1030f050f06131506050906040f06020705041d0c31020c0d050c060708150d060507020613200102071a0301060801120f021005190801090c0c15090f0209010603 70
    0xa0b581d00380b0908034002d807031607400c0070b40c061684544264a203520650f0720f40401a02d80b40c01100195074420428880803030f0400d182c031640c00003400154001c181c00b51411080c80700710380000794107002d110700c1441c041c640c8020002d025101d1400990710041e00300d05801c0c00704038802c02104403204440a800c1003c1c0d0a0016401030462007181c40c094941c0c541c81640152060b1280d010b1180301608800005409280903410180c0c0c0480c0d00a003400004469200164888281d00c0003100c2c01d40d41d0f13030203000a01d0350400855900100341d480c052034071403454540104240b030b40c8013560014581c202141009910174441c24004003011650700a072140010700c05441038001740200c2001070400000055007620100c008909550405800b48022516400784001c800c071441c02c1005200f010401c40da0003070403003408413210a91a0341c4060295051401d080103441c0c99105e000700300403c1012082c042070b55812104040c04e404440060012818030f8400c2e01d0148101020b544100b201000195032605 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 899203219 1250 899201969 899201971
    0x20d03120f0f05180a0312180605090f0609120714010608010203010b040e092d0a0b090a0203010e1606051813020c0105071409010507140f01090218070f03090201030f050f 75
    0x404400c100c030380004c81c62810f649928125010b00003d070a1501c00c1461040c540c0f101c0c03160841c1c1d0400907075044054445400742c2c0da064a0845c030603801003550032680300742406060f4014078440050100c001c0d40c00c0c0d460140d802014409403140800c104032115a17a07095200400a00d502e82c000e545a41c2e440d011030455400904c502c0384160341070400102126408030f6052600c00d410f1a91840f11212004e20710005002490142c1141c0b094a461310301241000b03100c00d116100003401010b0b010403910501d400c1d02c105241c203281c258004280041c01d561005441f205886003440e101c1d80782c000d84039103440c68421040a56820460460010103404900c3d0002d04845182e08024002a214128100e503502c0c00508560b000d5003080c440c0c00c2266101c1d0008188140c040c03110072030500c0c0c0000241d801c14080310300503001691741d0342c800002c40c2403003941082d414140c0c4086040a00e0050005000a000501d0aa04256a40007401c04580c0641d0001c0c00711807600804100c0e034a001a102070040700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 899204469 1250 899203219 899203231
    0xa05060907060f0504090b0126060a0b030103110907090b0412030f0f09030b0a090605090d09050303071a180321220b0a060b030a0902040b010507020d03120f0f05 71
    0x3407450114150380941c0d003594680e0500c2e500c0b00c0c5000c0c44d0071241c000400500c411b25040043c100381d803000d801c544e2900743c2d18249031905801d005c1d050060801c410070311705501c658000502400108080b400b45019200c413800c080d14182030650759010102c41031030103a0000c03a40084003190201d0324038450901d0740d02052190f1950601000481025509006548900f00c0081e82070b035400c0c0005042425403507041075190601045440955461b041030728000c58500e002e5034401503d0f00074180d405240342000b4042900034620384195911030416018031140c010891041000125906207080c0342d9070028105580d00792134465103242481c6900c035403020701c00b218003e010004079034804150074040e04031094070705460082c0f003502c2e502c03000b0742c441c001c012040700b5640b850001045c1d007148000318401c0ca01803100040f4150b113841000101c4d4141c0051030304000043c003072600140c13203041c41c500c0e000d9054105404e82c0d05c1031141c0c0c0c42c050f1241c0c80244036000d080c1850010503040d590007143c0140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 899205719 1250 899204469 899204473
    0x114010303051908042f0303040b0d0501140108010308030907032a0501052106060403020d12020111030c03010b071113090308180c06030a09060212010501080f010302131109030a050609 81
    0x6001c1040360a00c0043c1d0300a020120903085451460f046c0720400c56649460340410300b010040340000070f045030000e5001c080703126000a00200c100c0d406104907805884403544c4001070300038074070000700510b50500008101074000408a404e0140030003400000b103900c4a0080c1c0168100d00c000703020f0176a101e219154200381c00001280c03940c0034030242c070003c11504903000c5820b050948030904000f0086c00305a00604204404005a25030421a50a15020340c034802100342c40601d0090840306443c803035034003000c820b009202d1503404007011030781103e5060750800e03100c10b4642010701003260021511a0703c0b800d2182100c2d0420b48a03000401141e000f611801c42c1c0e60356450340d03c2501a60311145d070445410040300c10580b803034100007071908108150000140f4010390345d0b4842c2207a1100f001081000d10340801003000390b80c0b00000035070107010070140341c405516581c0801c00109591f4130550b4055200d461048400030b58009403646c1000050817109070811504180c2c1d101c60083c1c54000080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 899206969 1250 899205719 899205757
    0xc18091a01031707030c0203030c031b0c030309091909060501050102010b060c070510050412061401051c06270c17030307080f0a0603060510150e0d14011401030305 72
    0x150348440c403014126604001240e180e0039100c0c1e002c210703550044804409005075105800b0250302c04001900001110340000c41d030350091500d500c0c814088111014615070700c000d000c1180c0d500c002c000c0d81da1504040e80e2512441c0c03504190f07046288107452042c03075540e29024504044c040a5080a8101e032000c5c0c008000c807010420034085c003449038040f10072595104417803c00803401d02125a112001c4940f91080c101a2030f0b005008030295444010307241ea580f910000c03440e004140c06d16078010141180c91034108144c040305606591500f5002611459555800481202e0101400b4540852114040c100410306181c0103007084030038050601ca0741c0040d02412140840041183d002d680c00391540c10a42d51a105001c0c000500103107904c440c2511000c5c00800240c8074040d05006200d091882d19405007014000c2c0d0540c503000f01040d007041030400c01001d80b5110780a0680c21140c010001c2ca50341036020402c40c8c0900100407010303640c4480342e0000010706500c54050019074501e030b0914221 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 899208219 1250 899206969 899207003
    0x30a020733050d09052512200d0506010812040602100f0f1d100213120f060203041113051e0406060807030f03090503071d04050c09100e1e0c070c1809 66
    0x30b00b418501a07281001f10b240025000300da070210b01c1c028080c0382c0c1144103160864034404112003c80800b412640c42c1d00200040c015500c017485001e4000d03507181c40660503e1310b4100c0003541c0303914040f644400c650359402041180c1a194109101c02041d110f0240700c1507800300c3c42e0791b6010b006030800030000c0c022218001d1030480e09008540048042d004030f5154242402c00001040c190480101c4019140c00c01c0480040c6540c0040e40c440e901910098118910000078003103d00f030540b1100e41031610340002c010250180500e010350700d400b28040d000c004d40e140d03c1c0c148c009101c5d80c0c000c1c0d0103520940c2000004c00002281d0503070014400d583d01a02150341c0d200345641c6501d90300070165103125801f4940989401d415007650f00038020340032101e0002c0c4510208112003004e440b9001000200c14051107503d2840217015046502d608508086004071a14110908030242240032100d0000074280c0038480810700e220081e10421241040c100721420110700101001d02c4200c511201a0b8501c0729 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 899209469 1250 899208219 899208283
    0x31902011505010e10020c27162c030109060509120708041211040603150b031c050306010917010c200607052109030a020733050d0905 59
    0x4641e81a100ca00c1c8043c4003130b0400503035040d8010064214441c0c401070502960310b070000c160b90441c2030780302240c050728991034824260f50000c0c00c03655420501c00202c80030a61003c0c1369602e9000c0c0070351300c1212401d000c2007030f00d502d00210b420036410741c2070110307203801c0c0601c55000b14011040d02d0201e80e000300742c4070b00d181c032540038400d00584410303410f1104112408400b00c091081511440958000d004180b002030100c41e09070b002074603c9088500104803e4a51784100002244220018441c0b8003001681d100b40c44000358640342004004804518545d025000540250a88445624504504407010340c000c04d06a08500005850b4011005000c0a20250075000d0400300c00904026030b2552401c0e2802d501c2007210702d07260407602001e42c20700c0c02040242e9002d41c0401380034603594214a0700080c03410380b45800000700c00f0480010403401c035040600d00e003261130701e0010311460b01d000054103881074001c04000300d541c6424038a90070200600441c0e05d00015804880c1d10f09055a0103c4040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 899210719 1250 899209469 899209511
    0x30a05070e1812090a030f06050103150b09060f041d15010506040803183106050604151d1c050607080106050d270c0306061409060906030f03190201 65
    0x5071943e04800202120102c4540c000c08452202414500481b99a551002c0c02555424000e6600d00e95031001482000f030044d0b035000049840c0c2038144507011201c0c00007916204050800e0780314510113081c0342ca158603542c1210080591203030700b0185404502121580300c0049121a28482c42070400200d058030340041079605950440c0c0003541040001800303000c4035290007403541c1e4424114109038400d45100d18100818820400b021003020035103010b01e03002e6944580206108040c18441440140c103003607582d407a20803092034070014040c440c048018408200c6503009400078141c0d14400c0c1c0700301d030010700b944169104108a85081e81d84003801c8505040a0240400203081000b00450702c8800760410300d8803080702508401c0b410000030b12244200e018490480302d120001008009210b9036115241c0101740c05a03040d191840a040001e1001400030115031103070712040d01240301e82d282080880e415180900480c0c0d80e400e950045011b03000d0341041c1c0340b4010740c202101396450096920800c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 899211969 1250 899210719 899210761
    0x17361c0c020405090703060608030a0801170606130902030d1707030902010e060d061d091203090c061605070b03060f0d0b040f08251a15060309030702030a05070e 71
    0x20025110305500b040702515001c1c0100c0701030b208011012010800a00c551402000e800340156036980c0655400b4054100507842081d000750700e07c004411081010030010f501c05803c0760034091200030320107903100920680202175018414601d14120301904080b040b200c0741e1301ca110130002c0340d6401c8000c5065a05648000340012900101d080c00d42c00d004002d4400a44402808500961145c0314074105030106031514140c4a5003505006102106019280e041c920342030559195180c0082010380ea4561030300d000d805407500185c142490800d081a02e861558031400741c4190540c0c03203a4003049500141c48a501c02d200150b100d8034140391511910940700c0e030081410002da6540d88070b103120005007400a484d4410200400009622090f8100c0f1944c1c81000d403003508100c0754180007415071911501d00d03807417242401c10b04c050652400ca116040c913000300c911070381d1f036641c4000303507402c500924100941620035018000200a4040740e10720986017840d108202c151745007445080e00440c2c0c0009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 899213219 1250 899211969 899211977
    0x10e1207170309060d0b010e030d02070b0f040b0d0b0f0303090112020d0e0601150228020f061309020903060a06030314161202060403020d08060117361c 67
    0x20800201c0840041c100318499650192400c02e6021008a1070903442000f1100b4034a40d101a268195a0001c0c1c0d41011b0070001e038024402d0071502c00c0040d541b0070039030040c90341954000c122654030302820701c100c4024012aa0200e500d82041d0301c426805011078003c414424150307074140415a040010079142554030582d180008520035807a00d134003c5d40702102c1c06070070310b44070300300341680708010843d550003411100307030440c00986074003002801c11452000340d104140320100c001454000803030b11040c64640490720208a4180c100000c1d049102e243c900484183e00c40400044010b10f55014100800c0c2c15800d540d040d5564106c0324003107602d98000200400c00680c64401420741481c0605214600c280b454038541c80c4903254034400c141440b200b080180d001c00b003000100756060000e001c2c600d0941c00d02d0046403c040001070055295a0300450b44001c0c494000b0710301e2401c1d0440228100038603100a0105550062549424201200c100030640704810201e88010031540902c10041d0080e92 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 899214469 1250 899213219 899213233
    0x11d03070e04060e0105011205010b060406270e0c07030e0a151d06030a1a01080108030307031e0504030e03190b01170a05101b0e10051e07030c02010e12 67
    0xd90510303100e40600203443d1180c0d11003609110f0707142489054003030710007952008020609843c0c4a030a41d038004081c0da002d007406000820940707400009035184021940070030307031031074041c0801c8034100001c50703101c01c4c10b1003100701c14004500003c1001f800d11034005d0381ca1a50050940e0284049229688030f4004100d90340d1b8200e804040c828581100c00401c0c4500d000703144076030400040c0d0960010b80395203410315612181d008440101001412a1203801e00380320400e50702d040d24480d02c2e070100804800c14503498001103081400d4a40b00141c54406507842004107041ca03041c001c0444002c0209180688900d100341c10b0303400149a9140c890301d0b446151040301e0780c2441010b80c84119000e6511041c0c1c8501c0d00c2d104005482400788050340d4000010002c0d100c1d0380b00d42e81c10b0700d64010101040038081a000880e9a54035682602540c0c0d00c050f080c00c1e0b688210540c9a92941d131680c20f2003001d03c90012807c9801c25600503400302e00d00d0b000340d0f01c14070065404000c001c03e6410840c4102c540d640310314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 899215719 1250 899214469 899214479
    0x603240f1d0408041a0f0310060801080c0d120c0c030c0602070e091b0a030228141503040201090b0d1407050a1706190e0f01090b1e130911011d0307 65
    0x5c46507069a59114000e581007403400040b28440d0b070015514807000b40a004024850154040e21407401021900e00514a0681c0400405c40d00e60040c640900440100c00041c0c0ea001d000c0c1c1c0810241ca5848401c1450381c5035a0b00f06450b00c94218007600f0018010000300041c0d150384075921a014443d02c4020301818104e10b814110780c0f01c0c84062158100c20090000409650340f60044c1030844c10038058015284010142e91900c00ba20382c0100c03800004642c1e0810698403070040c00f000803048800002d0341d07030b220307800162000724003540001021080011030880350819034008102d0070442d8426149030780c4414400307035083c0c09501062000242d0705c00c0c440c4a200ca0021505030025000307811020000c0ea000082d540140c0c158005100d403960f40d006010416502c20601401008403090030080c00e1541c40c0003c07080d0001008050f4013807018001400c459590301000b000c0d01e85408410001070a0a140c03560100d04101140c0e408184050f5100102003180c1242c07000d2400c00401501840e4102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 899216969 1250 899215719 899215739
    0x1110c06010b090301060e130614071d040b041d0f06061003020d0b04061e080714060703030e15040b09060403210608010906090b130b010603240f1d040804 68
    0x103c2c01842d0315648030900041c1048084003014020302184484089115150400c401a1480b500c4510b0071500c03910708000c101c070b03406408403400c0942c0f2540b00440d15174030340015000e0074410303190652142c90070785404000903850440105956a100030394120800c01c4001c9522003008981703003900f004650440000082c0b0a03801070501e01e0380d07444005000007040001c01e044400d65040100b100d11801900781e43c034028500c04200920705200101100390901c1d02601c0b110b110310340e1107401550046001070401d03010340c00100300b0181c0503045a40900d420301481509500584040e0f4541c5026004609508404240d0078815901500daa0b00003071000d41e604101d000d4410650345805d44d0307801000c280c07032100f8017400d48494068000072480b0344441c1007182c41040054000d01013415414041030006481d0501d060442e00385080001d00507203e0000c03203504405598551041c89a4503c0109010211002d040107480c90f1080c1c45012101401014000120a40340a0078040701071204001030000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 899218219 1250 899216969 899216977
    0x8040803060117010303020d1106010b0d0c09150804150507020c0603060102070b03040c090e0610051e180f01052704020604030b04060608190210180f0909020301110c06010b 76
    0x40c5000195801040c0d403050f030000003a04103c00680142c10188100d5500c55049000c03400228050201549050801e02042c0301d9441240d24054480c03049081d0140140c6c180002000a281c8110f100041d0000040000f44200c4040783c6000c0568219020034400f40703e59032096442c0e800038078452011070304001054100070025411441200e4001c600e07402d0300000365004030f200700040c59469003418030303003010356001e1942141c1c40d07400a0104214808030342512001c03038030199080441c0c81c84a039200b403802080c00300d8036a0000c40a0030b4801e44050303030003501489040d40e82610400c690320b403000c000d800e007a0350000994850800c1d500c104400c1500d400b00390414401095145020380d00e945001c04900c0845041c0c0351523540c0c66003002080010b102410840385034004004611100741d000440351540c00c04082c00300003011015180b580d07000940f00c8040d101e80c00c55008450344e00c0d403108c0080c0075403100c228029400d0014000b107100e8544152203d00c3c0d02c80d03008e020543e00340310b98900281c00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 899219469 1250 899218219 899218231
    0x3030206041716030503090d080912031e010612050a1a04151a0304050706020d09030305032a250503071e0c03030806181b13030b1e0c0a08040803 64
    0x1004001800240400c1c0003c01c6000b4801d4550548916243e8450380c2008292801d11091120366030401a50410102d00303481c42411502d000340c0c59071118201081c400c502910720000d4401e0200000c034642d84c003d0f6803403013003611b458020702c902c3c2d68400b444410348510303c01c00c8030407080d440f1a0325100d240542242070303007100c03d0309058041603035890300c3c030301d50000c2c80b030300446501d4000140024014184400342c060100303070000f003101c0d41c03090300c0007081e0169a00c00a0104000070001c01d0f049882c0007020b8808585d651a4412020fa04400840441d130000150811425088141800700f8800d0307102100f401c1d400c1030285043c0223850b04c4100800300c4107114035500240050708100081c032445000300280d4041da0343c030341d83c0d45010020321170301c58400103580041400d0141042550400304980744800900b94125a0300c0e107141c510560050881030700001e00c514076038801c1119881c0c0b100c060701542c84511644c1c0380765894030b81020382d240c8550903040000401e10070000e804600307124011034006c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 899220719 1250 899219469 899219513
    0x120e030c0411091003151a0a0c020102011401150201200405040b0d061107020a09090f1b0803030915130302060106080408090910030203100c090e04140f060403180303020604 76
    0x20030400700007125402560080004242e0742e402c81717850406c00400c03810140c440f106860082c3c06c00f500c207600361402410402010000c060713030030400f10391003174101c485050508001c0c89050b50312401c190b20101c05240d10840150302c2e00f020a40d103081c1900f5050640400401c400c0d140600788020b00010300b01c81103007250090308c41c11201002495500c2210f088a0b072003004507466084510411511030681c0d4480c60302a400c0c214960041042000654512540801a0f8040400d80865001681c2d01c5a01410840c000881040070600000c203c0558210390303017103440f0162751100109580c15150400c00b800581c80f000040c060135010b5520b527a0424003d01800b41014080800a0840c0e2030464003805400c01114040086090401c5814038900c2b120700188043d004154009108a4076449800500000034001c02c041c008459085280400c1e0030301503030080000e080e40c0a035603010989045000a020701c171711008210702d04020606580d0700d03601070003003a10340d0340324001184c4030129a40881 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 899221969 1250 899220719 899220727
    0x910020607121104171911132d180c03170f0d0c0207090903050910030e0a150b090f0f0903030403050406030e07181a100503011e0504050f04120e030c0411 68
    0x65071000d4071b03a410980c0b10349286101c410b001f50a00c00c1011160780501e558900f4040d81c84080d4000001381c1c8840c0302c1c1301c0c4400380c1044442c08001d000e416140301e0344a03501080d81c500414440071518200990380a07503c11310541541c3c5c040e5011f10b1141c641410b200303100030300102d5001038090f00012290810b5104994107162030325030440864051034000c9000c54800500c1624904103541d4082c445020390400300000948414074a80b165000d40e0020410f8000800e00820203040f0b500c4040c0780400940450394034505402c541a4522007a507010b40c6071120240000c2c81d10b94000f046a00c0345505683d128200361614206074040c0c0341000040c01c075402260b02c00305e102d0014002c01051100758410200d001c1e51071000346260400300609081c046c02441c0801ca510941160480741102c0b0b10180d10914180d444212200745070207600603e80c805d080800344074011480c840401c0c041c6000e0040040740150010080d100042c01c2160580c054000a21200d07107454140c2c03184400403400e240182c64 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 899223219 1250 899221969 899221993
    0xf01050c011b0504060f0804170a12050115170c07020f0609150418020c12090d050f01140f061e0310050903041508040b040611091002060712110417 65
    0x1004410b51070080000d240030a081025a40c400c41c00c0700c040105081071581820103455140c2d0b6030032000142d05c501c00300010251034084c4940c12200202581410800c40755031581121304c0780b008038070541400030300403c1c0e5007444214801312301400384440b083c4071031a081a9500b4030100307409003080690b02c0001444040c8540c0c0302c07138405070f2040b6450b00c4d0213666903080c03450030300301990840c2e20b08400e40d2040c486000300100000e030020002480a10b256201d955040000f1180102c0d610003c1480c0103070744005981c8841500030300c401400ca1006040380380d403010314400004d44100c50050313000074103001100800c07601101c14410182e028003034540307034402083c400e41602e43c103950295082d44001001c02081c1c0c00614403001c000342900c0c08540900b46912059194a40900060035483d03803548000102100403045550501018040015a8003000d00103500c40e40d00319116400306121110b4440c420109100303030750030700f0200c0624a0810f07080822003c1c070300303c2001c000c040038443c00d00c0da0f40d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 899224469 1250 899223219 899223251
    0x5030a0f09050312060405100f090e0c0d08120a1e0c050c0a110f0301150e06030c0d20030303070c030e030c03010612060c1707030207030201091209030614060f01050c01 74
    0x45410492240b850704d50900905020403540b001b0049480c0c850002c109021003055940d09104441c07828402240d40c901d40da0f0b4080c2820000800503603c031000808003020000ba28001d00091020031026424654070402c8090966100c8981c11015030120b825180d50050568448019030041e07181c21410071060726240d80c54960b510b1402d561840403c00800580c2c5004071040540e100306900070302140000081d07414000b03805004c0d110f1480d901c00000350300ba480420500d1491349000b408030b2034064041c101038048132160040d13802401541300c01c0b4541802c00000b1a400b810940c1d9a8580604042d1821525094141c0d8410780c18081d0000e035102540c0d0900500d40600000d0b511900c0105661801c81d084401e00d01c0792000740126503011404d52140d10380c2c1c080e0320800c0d50901580e2801070703103030490041020b0701004103441419104001403a500c004e400d010b8a00c6094200f19954040c44004010320045520700e43c0210014103013241c0d540325001030240e2001c0b40001041406601215031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 899225719 1250 899224469 899224477
    0x706060b040f0806011401020a12020a060603060f0b010201151a0c030a05041706011511030c0607121a0306061215130b0a0e06010b0f0d050a0609061505030a0f090503 73
    0x42e50001201024424682c05011490041881000050003c010080082d40b078102040007e00071810881c020702d4210300030700003051050380c01356041150a84034580000107120b1500203410039440d00d00104810350051140550b4200c044941000c003900d00050383c118070066440b041d4001106000b00c0407106000c2018266040440e01e0380b40e291401c0008da0700362950b4061007981242c2c85203004100010001000005102407031800d9240d08121400e05451440b60918081540c410301007003240c42c940c441da400780300440d06a414030025203940e600002d201c0c03140c045280d140d00260046161442c184003115105103445040d074041e041d02110103051001d00b11030480984c4003410310b207810071034000720507030344800c4102d420410032009000c0c0d07070755444050090030505000020701020500c0d007142034540704005901c041c0510b14110302084c02a1800c0d200b80b0380000d08100c0f0200e0581001505c0142c8080707240d4400303040d6942d900e2140007600000500558803030750781100b20041071080c4024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 899226969 1250 899225719 899225729
    0x4081e04090605030111070c0e0402062a0c0a030819020c030609010b010806040212060f0f04091506141f120f05150108060d0b04051e07080106060305060a0501050706060b04 76
    0x180b0034546402d250075034550862511004070204186000194411641d10507240140746039403056585101080e00e40c42124008181007110100b68400c0801240c044c804120034482518000d96241082c44086025030000401c0b100c000d0040440c100480900c8840390440740c070403603050400c0c0c00c01003818414280e0701d5540694403039011642558110181c0c03504844151011032410056581d00401c10002802c054429000d920301e840040d5183c4411000310000100104010701d49890407880450440010103d40782c03c080b0300051000a02c50b80185074440034041c8405019102c43d004035007038810070f00324280b000c50923045c40390003800d01c554a00c120b0b8a81c070003d2207080050603841c7d43c0c03544080c0720303041004e04020490075845203440020030380c0e40724407410300310341322450545d06040c240700080101c90400942503d04500c0051070004036450744000300314003522948110142c50040710300980008101c2c2c0b04010651244000742030031402000001003203501ca00701342e0036030b80c804c2d800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 899228219 1250 899226969 899226971
    0x915070c0602030c0712110d0311031305090c090306011206240503010e0105160e04091202010504200303030402011d0306010b040f08061009020f1c02071a040b04081e0409 75
    0x214860b07850b405c000c1c2c1e1000d460302e14900103201000755207444840c6d4401d07501c90702414141d00d0320006c240c014610040c1c410700c84000e0300e4641103012121540844c131881068424000c0341c0c04030b21350410440845401f0900680a0185a070034441e610f120f41600b48d0003101d07142c4d500ca500604846420b01c42d01001403c0c030306d4418102d884c1c07004260030f4445074044910745900d0b003030500c045504140026000754002d82080d8040944040000e0010308111038041c1c00c2278007807060014280d90642c8954412446000c0c10a00c0314440421921000003d0321400c0d010351003003002c180903600a10080c611002d151401d24502c0034075002281c240703c42a0300010f20103501081c18803103662800540800340c14604c0082c0003d142c1560108441c580314403070301d8241c1c0d90004030910840800c0342110030070b4001d050301103981c0000c1040180294094481a05c000030320304260308205d0118540c641c0519003012048000d80c54540b908a89640003080801c251016074600f409105004006000200401c0070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 899229469 1250 899228219 899228227
    0xd0e0f15150123031b2125030f060806010b04051f17040c080d020a0303050a0b0609040b06130f0311150a030c110f0f01050109020a0c03080c040e010803030a1b050915070c060203 78
    0x1054046c0b180584160001501d4400c1000c61540d080601c1852109601d40407d02c03000740100a00100040d4000c1c400a001c4d4200210350a03c607440140304581098070302da40c03c0880304050300702e001810034400340011091542050006060080342d034110b4041d0840382600380e0354901843c9440710390b514100240c3c2001840c0070074580c051150390350003800b43c2c005201d2100c0044c00940345228540042d41b08942c0e50340450926240c02040d143c80c070f20b481e1000762030b25444040c01d0140c1c0d41244012501c0361016030300410a82004240ca112840e001c030003103800c003408030409030081c2482000c1201046205082003c8503403041041d0b04242005201421540184041180c00c0d90816004100038500421101c1e009527880155095441e03014513018406803203e051800c501d1050303074441d1907400000000810651000f000841c01101820410400030f80c40c2e48000c12a03000740441c0402061080c0041078032800c208038400e00140408a5152400c41540d07517081c480300d0207801840060340042 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 899230719 1250 899229469 899229517
    0x4030915110c010e010e13240305161a0315060d091a1003080307050903060a06050325050f041d070e15060d0e0f15150123031b 56
    0x800b044440b80700c00e20700004240400400a401c40e20800c0a482c0684030754228000070903483ea110b01c690031404040b040034108038a550039030001590000342c440f40500c10722807040606c120014003c98014200680f547c103200501c81c031140d00010705030f10b0f1040010410841c556101c00013000a620704a000049d0f10f40076042010503810754204078500401d000042c01400d810018912080303e03071003000a0380d81e40c2c5108088070b0b00c1c0101c0903203d03018803e243c05e012114803250803072400e8a006030200c4105408100e04182c4102814020b501e2a0085d81014855420200c2003100b8410380500080b9039100c2602c58800c1c00c035000d564141d61070b04050703014041a00321010302900881d944a00700380b035421850001e012803042030381c40462035641d182c3c02c01145005001509140d1400340c2a18808020013008004a0104403004409240e40c0c0a01080d9503001d1499012030f0300b841150f0102d0040e0341c000380344440c0c0c0058411600c00121201c0e810f03502c00c0100c02030000710f11525258445184c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 899231969 1250 899230719 899230723
    0x406021b0321090304030602090d0c12060f021303030e0d080304081902030c0c13090503130f06020f12070302030405121614092e03140f030a170403091511 68
    0x1141d920030b8180d40d40c80078410105030000584090702c1c1c02100042c0d0300e540020004480c14a4000004e01d40140c1140029400240c0c0b050803101030300521003407095482d0341e20600d04920441008584004c800042480885c0c441c6102e8140c0001c040c001e0309251005844401450f00b040301d080b40e1007000054404d2500010381c100b03d040c101940011800c00741c1e1880700580328285000c10304d00a102040340ea4a00c0c001036004036070260382180a52360f44814a54003480342e412a4010f00d00480360781040007072000d20014208400d4040c2c000a41008200002c80682e5944142e0090b41148005e100c00f007a581d032130841100b2000c511000420311800c1003c80c0d0003420b6541e03031100fa04680390140b4140203880e40010540d00030310000789207400a403460081d010588042d1740f1b01c100c83c0d031014030201c1004a012a500d841002c200100c1d080440388206941c0c1d01e104109d18800010700c0c64010b1080070707801100f26034126100e07041540c6682d44071826011701d030110641070000100002c507000b25103401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 899233219 1250 899231969 899232007
    0xb03160305041a060d020438030307240c052805090d0f061e060f0303051e040306291203041503020d0c110d02010516080406021b03 58
    0x129080600c0750789001d4468a5007500481c140b00144548140000d4055071404025000c07035a00400802a500c00c80000380040411700400c0801051129040d800717481003001e0100503090001c0c0254503044213603882411500107144604400102c4511040011140d4081c840600440b40d9805889071056010011182c60010200c20340c1000703061144507c0d0340c02070490301e042c070303064070f680b00901400d191078518a40d0510001d84414038249441c00302081e05c41d0f024521040740b20090101e69200d098100758040c05100c02008180104402c500c658985040407040e01e000000150401d0794079120b84e82a601310031144c9448518800e03aa412060080305441401041682d0440c0f84100304140550359118a004510b054082207a0150103103102703404071182e4003141d0304c1c14002c20400000107040c3c010a903156a05501500e01107000e44d51052090f5072280c45041600340551190200c150394540e000340054410395000c010401c00e401031036040407220340c11480110755440e4001c1c071344484044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 899234469 1250 899233219 899233261
    0x50f0d09240204050a03030f050d050a02030108120306100e010c08030108010c090b160312061e0e06011103030402220c090e09070509150f0a030b16050a082802040b03 73
    0x210610080c03096459404100094075410b048c51800e03021240c0090382c907402042c52001640c1c0c02c100810014550a4000d0f42c120360500c0c0c102c40750305a42002c01100b90000301c8610760418030316900c1b41c444500c58103d5140e50841030414010b010f02030340341c0404c10f131f00903040501183c2d1110401c100c881d5104c4080c0c070042c10381d01c02c8075040c800203108145900c181c0d000090704102c64100e111307000845030761240c0001d1164901c030014640b40a040c40300348005c1449000c82c074000d008002000e0754020f501d000140540302016510b180c0ea654200541c0280c4e003100c190700700e4074114000f240c0040b80d01c24402c078990380382c8441203038038a407480f8440081402405002d4540101f1800c0105841d03000d80c0c4c0750850324240d822500c0440034804144564012070899030b0000d007040000050008800c1020301803801c13950301c0c158003100301c4400e98942c800c1e0404a00054030080008001c3c0200a60a051030010141160404440b6406c1c070000d0342c01c150402141c3e0b207000018851080c01e80440140302d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 899235719 1250 899234469 899234471
    0x21308030a1206030b190f06080a1403090d12030204051234090b030f030a080108010b040b1c0f12021e0f150711030315120f030901050f0d0924 63
    0x10b130a550f03800c0800351014146100d40c200004100b404054250020480b03080c140f2010840381d56118400303076488a02c41c9098070a500d500340e041c1e0681c0d001000311120311201801150f41608144d807050b00440003282c1040c101542400b01148a40d582121400c0070794508004244c040c0c1c04042d09070307901d45180f81c2120024039608000c03c202c40441c080c40100c07541c400740050855182404241407449415800317007580000a1034520349134200080606948404000300001810b41d814041211540b000055010310381000c8103100c00342014000444034814001d104041e0f071559944c5920000e42d400351000358200b01200d80d0104a4050000b01844509005010a914a201d03040c0c5501c016010241085148030000315114002c40700000200d0310382d0b0440350b80f031920f100d00c0c400c03081c816081030303206034403480c044070400000003001190040240080d5240071030100055850b03502c424540c48501c00b00740b1a00d4480c00840c412085003500480030300c2d080d40c40f2070121130804114500700300752503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 899236969 1250 899235719 899235731
    0xf1b0308041701140a240905010303020601060813060b1306030c1514090f01090b0d0605040c03090512030711340e01050f0d200a06020c0f13021308030a12 68
    0xc504440384642010b12001700041e0401005040c00806015846003034801040000000780010140e01c41c2c2e040324065801e4a445980f01d44089640e40da0544201c01440f071542e400748040b803140e44c000d130030403c001030041c1000400b0b5603c00040da4510340c1f00b91012080c00004100e900b48061003200c140c03031a03142c01d030780c1082c00c2d0f580d1300801c1c0940011240a0340b50004a880a030340030f80d1400024000003c0d003e42c9030028100200d000e840103009090203642031a04514030140607015040d010f80e07010014100c0c060341c143c41192603400052080b8208481c1920850741000305004070705180c402540311050b002c110101a80424103c0b1000c0785245034100d0f0208111003c20105d141940c4040362401f04111503800040e10400b07044001415120303030b20801c07840180d509164071031507060a50301c0100c2c8958586050b80c981c1100c210068100381c45202409039071402d80c0c0d4041810b00c4007403005013403c10301c0d004040349006d150170110150380001584503c16070044410a0003444203901030000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 899238219 1250 899236969 899236991
    0xe12010614061e030c0708190311030c07110f18010302040605010504051e03101a090a020418050903040f0815090303040f080304030c05120a1e08040f1b0308041701 72
    0x2190003c0044210321010002c140d081690b50111000d10340c001240b19115000c01c044583d9203450030360b40c03074007180c5450358046481d0001002d89104605402c801418801d04d506c0e005020303868000c5140c0d03c840ea0b16082c080769503850030001c820b40014140c001e040e60440c03050000310b480070b41100341841010700081003299101e6400032002020b003e030740f40e4101d010902091a00e54543c1403803940c64140400c0b075110022540c6901d0007086c0444001c04c082d201c1010724012441680182141d850091410183d680c3e11a00101d402c00c1200d001c40e4130b8566241140031003100e4a4100e07198941182c0c445001300d0341c3da2240950018041c101031851410183d40b106641414068001d108020100014003494003c9002e88540c0c0d0b08407007a903d450041d40701e11005035104c1c07011031000c0b0300702000080031811150840c210081068542d049107880f55100c026000030380c004211780310800f05c00c1403942c42c004011103000440c40340c461151100e0034205051a05c0c43c42c2d150300f28041e0325101681c48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 899239469 1250 899238219 899238247
    0x60702030c010521150906010305090316020303040e0f070807090e040303091a07020f120309151812090a36020c0304030f0528060203070e1201061406 66
    0x106100342815641c840c014440355407082c43c1884e039504c02048090810a5210280c85000e800c80350460780c01c1103d40d03541c07006404445040e50800c11603071043c003c510650f2a16031640c44018001800c072810140d455082841c031031070482c0c9106c901d04100d01405005a00204011340103551400c0141005040c0901c0303181030724000380302800b01034444000c10203020800c2450035105289014a112a14114034060b5072055880a03204241c850141c4030000c0084040030349010f2101304014001340080b41ca508483c085000d085200600400e00d525403004c2c03005c106415010300d4a080c42174a54940a08002c81610180d2080718215101c408508101094050f044480502c04918072202c0301d00400c0b5030024081d6844210042c0720000303000c000d000e0ba81d08107841c09c40c482c104558140002840300c40d11100150300a840000700071795004000303202500919486410351910403000d00100d800507641c140d058005d0020350b5503425003400412603280f6200ca04c114140c460928040588400f00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 899240719 1250 899239469 899239483
    0x21903022104090c11100b030a2306010e060102060a06180e010216062a090303050c0102192d09121401110d0605040c05031321020106060e06070203 65
    0x24140c001c010298281e500e80070740c190b0300a030292400800400c0c054407000f410030103403960303c0729980c0300e028070030180c2c0701c0719001e499403010010f005020100b94694481910701c001645200e510b07a4203683d02c5180c42e00401261b0700030000c0c0000480281084000a13080c041c010b001114a00d0500106000050000c41d49811445c92044001030081d4495202802030003078140b8050307485c444411041c14449981c1103407507042e5006031480855500d9008810101d10807510f0356011989102082000c00c1c0500042d0401014600025140011802c42e99104052030081003000c03401210212494212415500c04244009280c41058007540c2270081c00382059449041500f01009101c50100441e00b641036880c80b6000d802440a01d104c50440b4802c2c0c0c00c100b001c09151481c107000019549428006d80f00e0341d40ca1512503034555168844001c801c0440c00e2400e82d405420715040b00710400050081e280040e01590000401a090440007480d0074001511340f4454181032010402503500400d0310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 899241969 1250 899240719 899240743
    0x103140708040f05100b0103110c0712170406120c030c1b230c031b0d0803041b1502010614062d0d060303170f0105061809040f020102190302 62
    0x45080d0740d4592500e080f0061100400409130300030403a0120001c1c096400411030003100741c80500c1014a80826540203006051080d0440da100c1a02000403008500b000380b441805452203091038202840d14402c0c5078066801080015920400c075050008248145500130b08140b40620070f241451100400c06000d4440800c0c039000d94898440c00c10441c0d1142c1242040c401c0c1140300180084200c2c6501c5400c24500f05000b03010b235a0741144100c0d0000e145012428000300b22901030b41080e140c0303485a4000500032101c50102080301804081c2034401e24000b030092022000504076041c80003030075a5055404454818403c107a02007807991140d094600c070140001d140ca0307940a084036081c07040010200711401e0003a000680e1032800c00c1c903402240c2901e009407a14550405a81491444400221013500100b038a190060100d03140031782c01448031802c0000101c4410044900048100e41c09075400c40300800b901d0a180c3c1156018001806004e47c007541d41c403a481c05549020b91250002e032a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 899243219 1250 899241969 899241977
    0x605090d02041a03011506180e0714160c03020f1206131e260313030e1504170105070516110109030f03020d030605030f03120603010204030f0f0c0501031407 69
    0x125503078821500c0c040614004010006e100c0b070180070705284e02e03620306402140c0c00610300d110342e98280d002030140081241c60b000030b8031506e035981030790894051040140200d0580d004110b080100301f10404080b000b1740c081d07042040450715501c100881100e400003590b000f00801c400e5070404900c0400c085a108411a0004034415a1807504440c1180f185440c3c0b0f4002da4042c0449040c0300300045400100c1071101695448011941d0488215010840e0b4407151103032006070010009200751249115900c000c1c00f4442d0f20302203544c200250f6081b5401c1481401d13032203d51640c4c02002409103580046040c18a5440e01214001104603540d515002030502c00703182d008c03540c2da07903c204815030046030410400580030f24180740094030b42c041100104002030038401d021940303280c00301d41c10300d0f60044280250301d82013a000c03481c005154000c1403240d05543c2444000003145403001c20080c140d10540c4a044031003581e241030701e44101c00c2d81107541011b241c0781c40b12038504c40c2452000e400004a0030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 899244469 1250 899243219 899243231
    0x1b0f0b1806040305060907321c0605131506030807080c030c010c0314091203011a0f04082103010f090e10090602090406060c0206030f0702160303020d090605090d0204 73
    0x20410710b10a0703a20052042c4110410800c40c03090214850050302d11100c100f00d1340c1034070101240420340b414194040c44000e8496101454942820a8110211841c3c0703190b000e50000e484030b00485404980010b102001c04c00c2c45000c1140350f0131a0240818192410445181191214a80c500402c080140781540000b600f10070704004100b0740301c10240d804001d024410f00100e004020f4440c82c004581c100c60b506020911008010900140c410344085201d070a5a103070503002c10000e817a60100d03030184501000301d00c0ca55480304000b8006802c1c03030b0009001c2d20070300034040c60404c0e9942200c0e1003001c00a01c014021444c0c801d8041040361401e0401142103030380f80c0555818480040700c000c01c958507001d2031004019041c1c024204415080b00c041141540e0b4910941d009030342554029070207142000080d13418184040301c5608007440b48100c0d1010404100010020b800b0741e0415000760344560765051815a11240d15006030a0b185000340c10031080074086a08000002c000a2049031514 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 899245719 1250 899244469 899244517
    0x50105070c08070b070b0c0a0c15020c1b03061e070518030123010602010b032a03060103150b06040305100b040f09060204090608300f071b0f0b 63
    0x108201c0c000d012030006840c01030b07a8841c2914900c0e071100008540c8441803030002900c035101e05003a240082c0c1c0035210007244903415074034010205207645400c480c0c55800d00c400b081550b000c0140141c42d01c841c000981a801900c410146800c0780109000006001c140301c48512503110008141c1041440c24256110f41d0b00c10300d650a0840d00310074060b090f62070304240403022030240042c0407111501d90a020380d642d80b0340b041282611810030510f60541c1c000740d0b143c8458564103045107015000e14035030440e9441d2020010f41031800a0b4030545482c040041c1c9c66584006030700c210410078904a5001c9c0c80d0600e550b442e03a4440ca50761003200403649e035035181984140c031366410106a88400e401c04119180881c94980700031b401078017070306410741d11f07013500070907190800551813400f90a1001c04a050f074a58114401601a000c40e0420f0184010b0011860310003100c0050304c01a0b02c1040740c1060003020248a4100d22003540c09044102e900340e0080140c031400e14100d46e540ca00d10119000704013054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 899246969 1250 899245719 899245733
    0xe0907051e041e0b130c1407080c0d080a0c0f090e150a0609080c03030f070b091014071d01090b0901090b0a050c120306031e0c0d05010b0112021305010507 68
    0x4080c80c209140310740c2e14061a295440d4003c09145004881c00b40c5140c40c4c80745e422049803d0052160081280f8206103c0441158806450b80e2849118071601e0495125407941c1805203012480000c41c10903410f0100c50f505500400a5150061405003040982613000605c5031803d403280121745160f080100f210b42070f4252000814100203400075440666842e4000e000c482140f00e10b074007a00a481792924607242c04800c135200030302441c0110b0308111254071010113581c00a0980282481207014004886100b8094106084102c000c0c0182514001402408000f803032844542004003000e81194903030b0b002201601920507416049480301c40380380040e950287c6540041e070300048082030100615900c04001c03c2510154003d498012102e20ba84100c10b01080e00c46a5140d0400001c4068100291858020301108201141d81d240081070118480100c9050180c0b25a5100c1483e410a56001107500360b4600714400c003140f604034000590b08000015000c1e4a04014000824101b40308031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 899248219 1250 899246969 899246981
    0x130c0909050402120d0203190203040e0612070e04030801030b060d03140306031603050706110a03120b0414090a030801141c0309080714040b0a0b030a090201050f130e0907051e04 78
    0x2040086540c0c1507605e03c0702960b00d0704040300c2000201c0c810075042c040d051002c01682d049880c0d541c0c2c981216201c05081113401002d54a81c40381612a03e000095122400c1c01124010b40c081e032a1380d0603030b5046040400c1680c00061486001d1148544c400e400640e2200e40428950b04107a0101e880b61a04000641040440f4110307008595441034088240040801c613907044800c151101c01c04003516800c0c85440d000f001c08003901161071001e50050100c82a041102441030081c400241100e904941c08469034041c4c0e00b054480d4028088c14003090740120310240901100e04030024420106c10010301d01b402e1504011240d00c0c1c22847e02400c00d4080e080d0303000948020025546c0303907505c0e00c507940e9550030520700c01031003075080090300d40442c200b41080308152648518101d03d50b42d40c0500349030150004036401ca0400c40100141c001c101980c501610000710800e0114140a01d011089411500042d050790410740046074108001e9441c5668510b00080441c0d604610071010000034004040d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 899249469 1250 899248219 899248249
    0x30809130f020f0c06010504140708101a120703050c07060b03070305030319180803010b22060c0203010b0411041503020c061e090a0507060e03030705030c0309130c0909050402 77
    0x10001c41d60f41c4001c58450003410144854400f101c440b40e0303171801040161504020101c00002164020405003441071300315542c064546114408402d5131501c0c060b0303031021180d4400003e004049040003044401c040c01c590803402c640303014069420f0510341100103205135000140503a5440d4168107480e182030040200542e006419030344c980c03030402d61300010f071404101c80b9403c3d91b1800364641c5c80e0b04c5800d4800d107a1160030820b8541142c0c201891812183c0c00520241040ca601344501c0690140d0701800c840903003265030340c005000003a84145425038460601c3c030b0384903500b0404110714180050f02504d0444242460b8100f810a04010942c024814400503030450700843d010404620094100d0700b500c0401d0340c0c0c2c452465a61150a1500c4041c030385001420380c4c100130340c02c001c902d00c00c04541d4000030004003920300e0f00000c0e50302e252550b070024041d9080c07600040b440c0b40080c6040320388100c01c0c070030380b0200340500c144500380184090202d00503d501d46903100003041c15900c03000010314280e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 899250719 1250 899249469 899249471
    0x2042003061012020a080f010801020c1b010c0c080d0e03120904051e0423030a020c22090507090605100c021306031a190e1905030705030a0c03090f030809130f 70
    0x2c0d81c124001407a0700407c5a908031248601c10001800080510840c2e1201550740044c008d00da000c840c0c9005031148018106041020001c0c0714030101c0c000c0e0030144000c040081c0207001503009004040c00700082600c0281c400c2c0c0129121911f002c0444040340c0c1410000c5400040e541e4511245105859206146101f0643c6501c208000c00403558034010940c1c00c41c00506002c1595418050303564828048902d0060300003004801c04d40c113040480b0346840d1350300f01d04400b0b00080604004201c400011081e611548191000c00211001d8450780010b40801c3da80040c2c501444403018084400300740c4000d002d0703c0700841100288460b80d1180c409142d011310b0b40300038003605c0c1c03401040c0200243d400b80d88080d00201800c0b510040ba00c921040020400b01a02405c0041d6601920000d040d410540d1240020805800051800c1c8014030a803910794079511586031302801e000f0100b0150307400048107200d1720301051010036903100030340d884108216001d9140e400349861602c05811a5482100c2c05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 899251969 1250 899250719 899250727
    0xc030204020f0c1902030606090105013002071505010506030103080a0f0e1002030702040c08010f060c230d12151701110a0c02120106050f10180e040204200306101202 73
    0x42400d51444c1c8914021070456800c4d41b6803030100040000284031300f40c08111845031080e20400f55914022040c6404940f1249811a030b184003010b0f40e010843c1107820303007144c2c00c480c48803007458807556001d0703c000d54a00d8119810355039008002e1003246180c006110240c01c064454a22030041c480c88407401900d40380f08102d034100082d41c0e94200300000c034441d0381440086040e145c4102080c40c12550514011081586024400d88405141d1081030b41d980c0c00790358414185c1d5803280603440c44030300c244005085041c03040e20000c0040c28a5829011114102200c1c1111080d04071101010f0701d298541200b00e102206442c0343c010100401010b10000001ca007400465030010b4618170918029102d407507064008a0b0304a00325591405025880024804d02d4501c0d401e0022500382042e946040c4289604103100e80800c1d44c00079507008002102003001004110306080c055078124890740c614400c0382c0c2c1583d1801e4090b0740402850030b4000c003610f01006600912070a0700702c0400c040758204640d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 899253219 1250 899251969 899251993
    0xa05030d091a100611070509090a03120e03070215090a09020901120b0d11190f03022805130f020d0219020f030a0e04020d050f0a0c0c0c030204020f0c 66
    0x2a1403526400c1d510856411400719060546a022a115000303003103161803d039003030030410340d4100307505113042010340325074000440d19813614411980141c0c813900c001c00d40082c0514000307150340c9417007d05075a030904180220807401c100005072111660f046880440180b540c0040686501400c5c3e8460b510210100b400071752420345034000c081c005020307030b10103946400498a900c140e0700907608a40d003100d151009072000c1598040304011040c00100780412002041b40000b10407051034202214214260034104110b18044e4036a40b6901c1c6000a065030810f819040d036010504280316142c000e001d2f018001307501c441c0c5980140d184010070042152205030035031010009400400002c0e4803081495111540c1d80d0001a80e0308005905000640c6044803030703001183d040501420b071640280d02401105070b13003881c9004c0c00f48074009054400e0454504080284180d5001000300828803180705411b030040f440558208007030702e030140c2d00035a54055150800000c1e02c21a0070b514581c2c00745d5228070f04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 899254469 1250 899253219 899253221
    0x1c090b0318150a0507170415061203020601150908030307110c0607060b151c1503080a0e040f1509091e030504081014060d020d020a0b0d14060904140a05030d 69
    0xc001c003604941000075540d0000705458142d0804949100c6c440908005000200541000f00c18140400070108180d952200303a0802c4884aa00880140e08000d0042c00040d40070340b8802c580741d00c3c07880d00d09221072400001c26100c5c44080e00510801c1010b400b44450b020041010b039620300d01c041c205542c1c8071400d0414200078015216580c0c82000c80c1c00004c00c2c1c01c14114103441c045020300020b07003111002140d514008010300049200400341000c00080881c19040c0a0400605680c50f9107921405000420086824101103210543d1404910f017180e0880d19038000180c0320704042c0080c0081881c208030b202d02d84c610a805040c0004040d4140801d9030180290003210400021a0007800c01661090260340090f8050720101f0058000641036140141c035a00147e80080d20f103408122081e000710f28416000c0d00309820550000a1003502201180300309645072a00440d04040e40c149407001501111024002030040100c8881d08011300388188070203151554050300b00c039076030303024060000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 899255719 1250 899254469 899254471
    0x70b040803250b070f181508060a0609090207062405010f08010806040b060111060a1a010201050411040b03070e16120c1e03020c0a060e1c090b031815 66
    0x7802d1800c0c2c81d80c1c0310b030b01c41c141c014a04640d11034114405681c03214021102141961507103000c00548406450b00240450990b0001d05900d54103803d030400400009880404007511403806520301c80d40400030f0650000201098413818080540e403641782d41804400f50200d48064150801c00000824801480d1007100d411207a080e298400b2024462038103a5098400b403051044030782150b2300060001d103c0384400d95000700141490001c2601c81d001c0c1a1520b1030864011000e00d9403020041d0503240c20100404d4000d800b44000d10903450a80e46440c49000c1803101140100d480303407074140d0745503000d00c18800640280b64101200707146c11200700d0120328203241c02c2008070704000c0b0210085050f901500d50624840e8981e540403c9480e80d01d80403c0301080354402c200b6a0910546652035024080c1c521418026480800c1400302801ea03c0d02b050300000d603041031501083c451128907508140e078481121102c02025071603940711000724481c05214480078070030b4042c160307031004100000300c0c01c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 899256969 1250 899255719 899255737
    0x106080a11090103150c11010f0606090b210c09060d0f0f051e09031e1b0312071101060f09360b06030712030c14070312050705070b040803 61
    0x40c03401c074104009122059800780000780c03000c1040c041e00801d444264000100044152401042d2111814400c9003110302d200481200103443e05000c109031a801906c5602034410000c00900d06910080c28442c008100d0341482101480040000c043d056a502a1142214040c00c1075039100c09103144c43c401480400300110704146040b0741c280ca00780e118814103129070b103100e4140c0c0c030500d01262000601d00700140741070313410310080100d5200310b500300e1081d0007038203440b0f44030945840f803a0510000d80c44400c1164846030780103000020b17421074038042468100203581000301d50484003101c0c07140584416000300383c901819000000315444942d000040700202e840340710f03103060b91064207800b80e90302281d08a80000540964480400e01560305603400c0003000301141d12443e1340d0350340c5401d0484112030950108540322010414401080c690038250300c031301d20190490714116628032101800c21783c3d89408100021602e1020440c00b0043c0001901c41011510386031580c58481503500d600424030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 899258219 1250 899256969 899256983
    0x190203030906100e01330c02041b0207060f02010f0c0f0314010e1807030b040b0906100b0f03040809130f06060203182e0c020a080a17030c0c0106080a 66
    0x61618a00b540c1d800b0031340741c5820b01100103920340000c084103020a110030040c410748514038001c0b00b1004000154a088041d222900c12217583d0042204481714280c9081e01030341d150187d00751087d400308a96082d03c40600301250910781d80c44040b8010422601c0d2018500d1801240792040c903000700c4800346039070b000d91701484602040303502a52450004e22800300d40d60341c0c0c100400d40c8135441244001100141c0c1040703604955898413091140348007a1400d540700d400a20a02c1705500c010310800f940202515400c0003040e1816440342000c0c07060111408040a0100108081043c0a8100cac3c1d944500103100220032518203410030018100c00e070f030020241d1700d0944001a60380c000f109036120b246141c02e00b8400701420300e00340000d1616200c10710048043c00d4804c410421b1018455805510300c0c2c0d40d9031000540b2610500c000c0452641040442d903120b40c1001c80050039840c00d0160055108600c1501ea0326036a140c060107005610004110703500340040402c0080c0c0001c0e04121240c01020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 899259469 1250 899258219 899258221
    0x1d0316120c150e01020903030712090b0412030f0c120e04200d02070606050604031a130809100e030d02010912030606120e151806090d05070611190203030906 69
    0x3805a40400c900300e4018401d040c04482e0090000755940480010031a0100143c40d009015000900b1580310000807264600c14240e03000754a9400103025000d07180e030001452a15003006151004241399070390060800001440300c421041c4241550030710240d220786407400b0f500319260b0281003c1c080c1c8140500031403030f0903165041d91604841d0700031840c40c0000114904030704020403102a40c456082940c44a489490007c4c82d9180d04d03005100542c019200020b5040501c100c2c0340111001412081c0802c015051000c0420003180c00c03191402e03070490340d52100010307d41058445008420707203117138035003e04042c2003103a58041d00b00507a01071048001c1c000c10314000030160704a130310a000f500c00203400c3c40300c108921800ea501070302411002c1c13800c481e030341c44409200700100c14040380c8510800100e5507a000705010100075150700084210086c100d111105240207010b070207207180c0913020a80310410246055042c00840d10040001220101c2c80100c0c40000380d901c0d030040e02d06800350311a00c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 899260719 1250 899259469 899259503
    0x7080405060f0c100c0e090408070512030103140c1c050a14031b01090308060d110d0f02011d0906060a030902030604060e061e04060f023105010302070b0106031d0316 73
    0x4400c2c3d40d05440381b030710348108292080c0280a00030200a000b11000b103400c1103807030085a0101312442c603d039031418400791789606520300503c1c1003021000c2411550b01c05030b0322915942d1811005040140c0d070f941040007003142410140e00d89010b02c00050100c014003501294492000300c000c19091081f18000c4030f5a40480e105582201d004040290000b82c25801180582c03418000c10a100f0b0f014540303820301601c50300009501d00380070480496002c2c12065400c0304558002e400c80d415001c0e00300303280740701c0240b180101d0100d54004092030f1203110009061003055019a01910f280e64020b01160b5191030a0714000f0000c04c088074004c40540310300c1c000942440c90142c1020048458203100c207425454560b00c42c0c005d42203650340d0707925294084c803040b1284e6001e11400800c00d076015100c10182c182621808418030307410b422403410140100072100105e480700e41c0040c116986880c001455402042d8041141070015941c1c1e212400001481c588110445224000d69805101d403100e90342000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 899261969 1250 899260719 899260721
    0x3050d0503091f0213230613151e0f09030303020a05120411030613080702040c0e100201050a050108160e0402010e0d0b0a0c030c1d0a120309170f1207080405060f0c10 73
    0x404100c40c00b60711a12019030142800703c06084403075100c007100001940c54243c5480c818650000785c00c0041c2c038480c580011004102c1c5584402411802d0189a0013800c4bc0010045c0f030702d9010207401d2540016034449214821002c032100407a4401d00f03404903041c20700e41000320074102d602e42e5200348200723408501d21411000200f0381043d803141c2e03031a1400380c0c60740c24070014180c206030b40e4091001d10841d41c84207880d5407000340c0f1103541e698000602407611010b00e4080710010f81200c10194000104441c100901c0c0c0484000e0380e001401011585e5518030040340c502008111054024800c20405810000c06008803409640c1c0c007881070000d038419203411022a103125032130300300042301414001c20312401071503401d00302034000c1e02d603924650700c400c00d403002001c204508070002048484c08000c0f00c0c180004e02d0000340108005001c1c02c582c002c0005590300050700301001c203004000340000c01c0001100894005003c05030100b5240c015843c4810301c2d642092071641007500401d0041d407811039403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 899263219 1250 899261969 899261999
    0x90b040b0603060a1208130902030609090607021f02040f0f09052a0903120c0c0909120f0c01020403060f0902040c030522051501030c080d05030103050d0503091f0213 73
    0x4041c4c90341c5100e900c3d100800b8404003900ca400c3d208504208600c0498003000c00f0103802800c0280e40c05603403414440141300240f64020f040310b0198124105200c1041c1d07000c1050103010400003c0410056045002000203209607400840162a1403400052403121440500115581110b0811003981c0303114182900c8644001d070500d01c00300180701005280303a00350192054140c051300b2079043d03000c5200390400541c0054800c60042c4c2c0020040f00713451604e0200c00b0361003c2c1500182100134180b0031603220a01400d2084601d0314404254460303105170950550340296000b28080c401c02201c000c441008001c0004140c1c0900d0900d41d12074a9203000340556070288139034104000356003001581d4982c3c0b114044404440034043c9201c3d400c960300400c800f0901840c014521640050b24180f42989401d0421401c0000e104040c030041010640c041a08903144005080071581c0340d8560944505018403d1109210314a019921999044007135006d40b000c0000700700030800300e68640c7c441c0d50b41800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 899264469 1250 899263219 899263231
    0xc1b12021e0d0f050c070e0a0b030c09060103020919091d0303040c1509030206041e060f120b1302030711010f0612020f04150801020a0f1106070f021204090b040b0603 73
    0xc480b1281e0200c480c4642002c801d882000d10b00310741001a051381c00750a0000550002400651010521000c00303998440c4aa02041c200c00400325031940502046a01074000c2900d810315a0109145003640c9410703400041200e026242c05002e00c1e00c86082d0340003408100d0003540d8900c1291000506d00303000004684c040c5411190119049141031400201e0310380748404c050400040c480000010784502c00a480603010040c00441c080c1c51407101c6401038003a580c0200c041101c1e4140c1707a440180c2044c88601200c440a1021520601c0100070030000340502004041e003d20000030450115032203254114814444802030040300c038907902d2101a601903028101e80e220340c500140300103107448000500500c001500120306e0200f000c0c000a40e0380166448200340d40d4000613846003840c2e00c584200300b0002e55040441d102c088410b11140e0302c80c4010a500c040c040c01102d9031001500801603050b2404907084110f40d16511605d50740040c1405091043c091420198180c5151800000f0340b440342c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 899265719 1250 899264469 899264473
    0x90703141620030d060b070501050c040b040b0f07230c0111072702040e01080c0913080c0a060606211a10090b031303081302130c1b12021e 61
    0xa03440003181000e2038440b00c0d2520384010404030030031000fa400b4a030010035180110315181c0066040543c05c1d0307007000306909410441003006001c411100c4060b60240c40e40c040c0d10a031202454140c03240c0b54401c8404c0030f0111316a0300c00c0c040c00d40d078694181c100f400a0340300950300c1e0556a80d0055070300d00c6100e40e15400c280c1004e502440981401c5246292071000ca0214221034481f00113445c080741d0150308800c58101e880c0700180441c1004002e680709201099985c48030629198400010380034810700020b01c104030001c2c410000c10003c00002801d141c0210f0108501d07036880c0030250403800998940b00e95014018034404000c0d0306486083c94a4420010300300b9488150002c100c101e50029441350180f0083d004003003615a800005584568800055120050b1180c20003a006034001000d8403803078a07042c0c0c40c2a0068540c55100340c0c0d844554440070074440142c0304292807140c41c041e2224607015101c10b880d8180034940e2400100d51420340c094903c00d505203003040090300074001d00d0709074035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 899266969 1250 899265719 899265737
    0x501021218010e07061b0609020a0305060103350903010f05011e05040902061b070f090f2711042007030806030a11010807120e060702120c2a0907031416 67
    0x160350300c6c050422082c1c4103603000940c0d09820f500041c1c49031950740064401d80c4c040c0005008108003003202c2d04d42a50a060061120032040c046610015020b01c0842d0ba504000305102c4260b8400750040c101c023601030041448a583c481c809075003200f1019107a01114201c5500c001158180380c800c210903142c01030b007214982560b4101c0094400407141d903110443c482ca650000721124880725038006400600c00204680c6002514041510944101d0081603202441c80e0140500364004010180368001c03920141210070304002002407071608010303101c681e94040351088403010300b0003e059162184e280d119050f203612040c542d072819410802071441000c458003039155805502d01c1540800d2520303125003845560f01c1a581510000c41d0f908540354840020305c40c5c081d4041c030081212a2203181018281070312440910ba950414840f2144d0031038980c081030310715a8a090220029003002b0704460b0b07050421450040003800604006000c40b01a200402c0d020b010300703115512200010394540d050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 899268219 1250 899266969 899266997
    0x90b01081506160501020903010614090f09030405030708070e0f0903070b04050c0d05300405120a05061609050904030903020405131704030302161a070501021218010e0706 75
    0x8101d04594540e00c01c1061001c1041c288003003810f0007101d4420320015854104020a040c2520402e070045010080304081108280d2185954980d00869141c484e44480c0c0354403035a02d045114070342102c1d4041c0100480419a00d4001540308111247c03060300c107283c0c0e51845072400c00c040301a5481e0040e904108001d2000c40d202152098000340507505440d070303141c14000010000c159664007205d05410036240444440540e849041c0b06200d032881000d220110503c3d0b000e820321882c0a02407182d150903581400d22703501001038048191f4040c0458030340c1d0500e00d019410600081c01043e001a10508010440b81400a001c90245505407521402113040d9402c20001e8a002440f00c1c188120240001c404110b071480c803540c50340fa0311014540d0b03a9040d402c0007414442400c5842111007003981c001c2000728981804504805c40e03c51000d500c1ea14070789021400380c8603400c001030680c0c00000034802c10410b103481143c80014480c000700400080703941e07015242c00c001e21640c40402d21802c0c401f85 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 899269469 1250 899268219 899268241
    0x131406030108073c090506090403020709090804030204060603020318010b09070e01050c070608070210050f011413020c071d09120f040305011d070608011a0d0b0904110109090b0108 79
    0x2040b03a54050801d0010706084000010782c03401c444d1112000490510f040100440c24440d6541001b07003075a40b40b12925058801a40d40d140e6841001100d1f59600384c3e102c203003d13282c1c00b0380d0081d642c0103009010140d92418000c010b90000c2d502681c005c50041c0749000c410505200d140b0100340b010300b0054466850361760964410009607203150501c01c00300210f0b00c000700e007407002c0f074098900c58443c20503070709000710028a000d00c01c49448502620f01018000d03840c0a54040504458282c402c05015100090100f229143c5010304513507000d0003c100d841002c2c0c0e01280500c03d0741c11813045109100f514605800412009a424403403e4029115104400001d040242069480c6204031407130304d81d0300e07540d0740c4c2154540841454512401c1c005215210803d00c8490010a800e2030140ca40354100804101c0300106400f0700c0f0b0303034070307900140c540515001e54211810740c0710002d2040c0014a4a070801d540817034581d249141c001203c0c03039070100e9000321503c1141010101a910f0354110396a01000748 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 899270719 1250 899269469 899269499
    0x6040c06080a1e06030512160b091c03090213050c0d090501020c101401080c031002030429090d05040f050618030d17060406120f0c03050313140603010807 68
    0x848443c0d00c40d82c00f01c0304450044580515910700440010f000362850038400e0030600040444c1b551444100b117035036290700d900f82c0f0000e44190041800400c5403162440380d841c2c1694000d070031301c0059010f41c2c1806c0da40d41503403080c03566178003c0d907821a0000d07036140c403401100c5c1c003143c1c40c42c3e403400240a00080b65280c2c0d440441d840b4410030005240c0a00f0035181d514240d020445104101c0d191150000010390340100c0500411041c1c0081181c20b182c0400661280388002d030080415a01100003014060008104541040d4000e090f003807181440f002000c80c8842124603c003d48102c2c468049180e00c520122403c0740c1c0229641d0886038144410442d0690180b1007030f0064a424811142c0346550510103207118003401e856a4002e4a4802c00b003006044004000e20711542c600042048007000c0c000305a00c49541c403550000841c03540386040016540550806440b6200106207a07e04040a420850684001fa14200785410014040080e548801d01905829811802c030401c545c1421203c1d60b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 899271969 1250 899270719 899270731
    0x5040803011e030204020409021b010905060103021302040905010f140f09060d080c0304081e070602060a022109030d0b041119110f160e040f020907030b190509060306040c0608 77
    0xb00740c0641d598000030700760b802a4004034441c42e4001041c0c3c4280b10140b818200210001000b400f0300140307500c900c0e0300c1d00b80520000c0d02440a40030040801000c60b0b040300e0140070745d95010451940c40300c1a0302c04000040c0103411020000303007090f410310300d4140ca840724130103c0240054050355480e001e01180c8042440100e50002090000141642e010320240005d804003000034102e200800d40a00c1c449210701c409142d66400c200402d0001e1680071038940e0b80120342d42000350b034448080e0120a00511a480310041181c140c03801d20508003408402046201d42d4444240f04003a50042040101c596003002002d02c0300041101c01c952841c0c40200e500340b4421401c00c1080d244400030420300381b2103458410001900003004000c1220031001440c1d01900c2010480700c41c514060b43c80003028a40174034080d1043c1d02c29000100100d100742c000000d4140050040640c1c0400240c1039000d02d10346018851085000c0f9000074481d082c0000c54a214070341040b03d00400e5460031405a840c0c01010309a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 899273219 1250 899271969 899272019
    0xb0a05060f13240906050d09020a0e16031116020d051510030b15060a0e061c02040312020a050303040605150a080f010b040e0c06090a1208120108010504080301 70
    0x5202c0044600d2a8040000c014040640070311840c2d9a003e011002c54071070f480b5040c4032001405101c5203a100090301c3c0e008940d03010005a840050000a5440c551a480380211920b004200400e80500c2c1c00300c40c80091301d6440600c01103d0600320080c150184d40d0080c3c100c0c5c044582c01401514041c0c950741509401001510240b80769550b00200d0941c0440301c422100c509400e0400802500d1900c069102c90080e8404549010000020702d40c0e00c074200b0300302c1c10041200320450407903403140110343e9044581d0000207004014044c140020303400521040d5003030701001d06558500c900228110070540d80c08000340d4503596807543e415000341009400310001012000f058401510362000020103000500300400c1035216481e02d0a0030348405d204014051400c0003c01c442d0750000141840c815042200c000f62104c80b16408030740c2501840e8030100705409001980410300c0040001440c0070072000410f211035a07240d0a200c0d0903141c040e5401480c10000300010003580418a42520101182c101c17 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 899274469 1250 899273219 899273227
    0x120901020a0b061215090d0e1e15040f090e1603140c0d0f02040b030f06070c030e0306070f09060903022416050f011a0a0308160f060506130b0a05060f 66
    0xa196152a2100b0841c4d04103011740d0080c800400300401c0600c06001e1140b400c42120721904000c00c2c0e5604200302d1902e114001048d06a525684480c1d40c00c0040013008c512585980c1c4d50048880000610f1240381012850280d80004280c004543c204a10359452201240700d4959a1002040c0c50403168000300c80c0078800e0302d02c28565900c1c0546030305500406240c2500c00a0303004000494140d20303c0035210b9409200550312401012035000e03440201420505101c41d8941000d9544010801045a250082e04100716501d908601c0780802410300f55500766419440c1d1600390b8425010b0300010b580309100c260345103010340801080c0c4a5095180c194141018240040c0780c850000c039aa040b00ea6030031240e0070b0601a94244100700c0e200b0301186145c0041c0d0881804210010600c2c0000b030000e58001541c68102102820351214065004251811000023030900c40010b2500303942c4588100c0082081c5540c10041d40142c6c1d820070300c006c00320505c0740e10f0601000203581c1309039420b107142c40d0244 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 899275719 1250 899274469 899274499
    0x619091e0f0b0a020a1b11090601020a0c0305160f0f090f0b0d0c080d02070e2a0a171605180f0a23040c02031801021c11120901020a0b06 60
    0xc20058000c031a03070400513850b001704d120094561500158550000072005000802064130240482441c00081d6803200c80307900c4400040341072001015020348034000c0742200100708040007036600c5241d100d03050b000c44829291400360300c4507645071080c2c0d690a061030b5805c0c814042c040c0d01c90034881d060b000d000142404100702003240b0f2100d00b2010380e003000b603415040051500070310640589141c076201820310a030500b1481981c00c1009840801409103007902c0f5096801c410048107a50005000416147c003103101c80205185042103101c101c5603100b10100c1c404540e14030040004180b65201d071810141c2012a1103898148004081d50146200d1001201c07600c80130000c001402c0308404c10400307012243ca40b0901700071a0243c25004a140100b240c112640c04019550480c0d01900300324100c1c0142c100407403804c0e140a5040101c00c11180a052809030400c139018846d076680d0080c4d900081341c2c1c1915114074066039225a000d40c21110812000559109103113601050040491407200124 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 899276969 1250 899275719 899275733
    0x102281505040201090902090d030c02040605030a050d030e01110301061d0a14030609061e0c0715050901150b0301090e0f120307230703030f1803020619091e0f 70
    0x80c80342400314694403401c2c801035590044180002e0104200194502140b00000c80d001e8981020003a08004000030140c0c1190740c1c42d0000001450020701b100c00180303071414042e444d00c0c201d902d89004a4901010b0000070041809400c019000404455080d60b282007000c0d00c0c444044c0303500c000511a00c001c803134030555801c02d8100c094050740400340071005450090615005000d0101c10440e8819000c00440c07071500304092402a1340910f00fa0f00c562900c6a44070000d000e00c08008203800d40780b000e00300c0c00942c0d90384840e10440e1103000038001d41d0758000c5610486a401e00030810b2078042000140801d260700d800981217145010119403e0202404c801424642880810300b0740000020a11409584c81007030582840c2651440745000c0b10356280fa1510303441012401001e140d160192481c0c0f00c007803981301d04080580c40140442d44041d600e0001d48a0100b00c4800e079000094003e80c4100ca2402d1113035a1034198807031380c00452000c12940603007040714152411a00c1340d0003184030800007886 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 899278219 1250 899276969 899276993
    0x903020a02100807031d060a090311121806090d060c090317040f050909070e132a080109020d2d030f021b010f0e010504050409030507120905010228 65
    0xc00d0f42d40d034039035081c040300050035a00c1c000851410024090f0b1541001000850500d0300720921860000d4280202c1c58196018441c0c204099810f0140c2c0c8104a85107480400034841d40ca08403a1901c00510000b017041014000d5440c1e6903007050924010b00002191540b01c18840c0c603440c100200d5944d80c80e51440c1104100c1d070300450541901080800c00c0e8442c0d1078405000d07001c1280c40d80360901e003204145507500540d219003140c00c0c00150100d111001c021204c198002e4128210790010000542d15aa0074032440022441504011000043e49030040c070410301d405500405801030340c0300035160009217640c00d00030346040c2e030340c08401d42c21100020034255907940d200703485035051a648008007a0412020983c1a042d0100c044143c0116072b900c03441110040ca050300703080380c401c04840012502d13130145401c4035400c0b40c80d00c17404070145500324010b000613602c6002c1750300310040c0c1034a0888d030b40074041c890349015921220b040e001101020b0b1034500c0741035182d180c4401120b419101e001c01c07501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 899279469 1250 899278219 899278249
    0x21030703030b04060e01031e080f07031e23031005100c0b0f0106210b0a080c03100e0c0904110d0b0105090a060311040f06080601081e0607020309040903020a02 70
    0xa41d82e044000c02e81014083c000060940440702e000c6589940c440710b075500700503007041018101c00e992000030001007074140d60b02c019520480075140c0080d403502a0600c602000241c8208503440401502c0341e03c1640780060148042c0349060203140101d48a2006400240200141203201000414071b625001407242070600e0a50310b40c51884050b0a05040c0d080d00604024264110301d40140500d0307401086000f20500c41c081d9540401c00c3c031001400081500e015025440072081c1000580101c1c009a0000e0704981202902c6a5104c242100c8044910004141081da00100307e8500c0c14900b82e4000c542c418015404040c100a0b4480001c12803000c1c445c0840312059141e0062009050100740076a012107810020414542551076040002c1c640c412614415502e824100c41c10a5441d0030100c02841841c0840c2c4455865444041d101c03294415888403142c2c071580b042d40c0d604000502103000b050300350040c5292245143c107000281c028214103800394468040b8000058890b80c5070b0501980c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 899280575 1106 899279469 899279471
    0xf060603070e0a0611011a0d020105070503040915060e03011e0e03041d09010b06041d130b070206090c0a2601110301060507151a2103070303 62
    0x2840c5881403d42064201c800091601d400c030052100c13080b00400240004441d04240c04c045903100c42500f03900c0f5102164507400740d400b50000f450428050700c181c7e450304c1d45035903000041d00c080201565140c458440104a0203078480510b180c10002140240014074007013507200d4414449459411800c1c0e03072a012550540e1041003207a00401c043c05a03840700340b851280c0b2150f00c407411540d80e4141e5003081046545813800c41c0c01c58041c2d411441980740e8414004900708a41c0100900381a20000700c502c0c50808107112010140c421101a4014412450f00e94444d600305010710309031a002d0381070f00c1010b1103001d02100c18039800705d809401d46025854900f035282d014040c820282001241c0000000c00c00580c0040103003c49401400c00c85480e804480c0300e0401c0360130344a0282e070800d1070302003049000e1410145120b1022990b100c5055a2001940c181c0d00f142d00c1460110082 = true := by decide +kernel

theorem cover : BRFrame.Cov 899100719 899280575 := by
  have h0 := BRFrame.cov_init 899100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 899100719 ≤ n) (h2 : n < 899280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
