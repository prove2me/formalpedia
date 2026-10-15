-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5424
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:49:22.958259+00:00
-- url     : https://prove2.me/submissions/52790c5b-aa43-4f31-9014-e694a93664b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 975359712 ≤ n < 975539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 975360962 1250 975359712 975359719
    0x10519051e1009170304030b07080c070602270312030a0c090f060503010501020706110309040c050d140a14090c06160c03050604031b030207030b190203010306060f05030d021c050f0c0705 82
    0x35070304101c0b0b205c0c2d0700e204030701c00180720301c0014001905180c02541001c0d800b143e410440c40c64804556200800c80e0300600d12007814071000f0004100c400200c006445004800394010301c502030000079103440781d010007002e0f08030081e240d110301c0b900f807071043c09250020400317110742203d0142c0b0f40308054000d41007400781b207006201300800002d00f03510441200e5011140350024500d0000100e041c07002406141e00c590081c480200142150729015100e0200052810602c030781007400d00b01440b800b42c8000a13800224026050180600d040300801c000c03002485c211452a59011807420b440040d80b2900707809010306808580000a000010445038852482a0b40d12038500b4000045071100300e100010190050b03102c07032014000941c00104c085c4c1c0081d00311124102c03031321119030000161780c0f0036002110310580f1144100080e50719040c0c224007400045001d0601146001002590382c04246250200620301d0714410700d603980244200e031203c2c500000190341c0c3c0c0d0086c6000071740e03408492240d03501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 975362212 1250 975360962 975360989
    0x40e011409060607030c080a0314070801030c0834181506030905061603110705010603060608071a0304020f0915030f030a050703050d0e0114010608010519051e1009 72
    0x82030b182443c211141c4942c59140e003190540c04c0d03200e12580c0d03040340d42d08000b0f02d03607110071101000e0389081d03030706100360b010b50380b0f800641d8110700d48a280e035543c9602050303041d4800070651350001000740320102410881100c0106a0b11000040790014805030301403804220f0041400181001030741110002e8281c49030681c10160340c0701822402c50300d075100054251f42081d000305605489000041d100d1854614000c101c3d074661035003080096001d0395013280c0c40d80d5141020000c014090052100070120100a00302040c80e102158041c50031000511160040000010307085584441c41441c204034041d240220900d000601c1c461200445400a40b00c2c1c80b8100188031102c20000464450359150f42e40c560810741d0b1654191816003142c0003580005440d061503102110091048440000324005110b14951400102405028043c0c100c00c0c02345940340b4502d4140201010803504840040d00c240384421200c00b200302d6040c00d01c80c4200c0e801215003049182d040c0e0b000c11304c10300761001c0710f41160 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 975363462 1250 975362212 975362221
    0xf091208010519120c03020909160f0b03070c03021005070e130c20070803030f0709080708070510030f0603060621020f01110f0111030f060f090c0a05040e011409 71
    0x254450301c1c103103200084400300d01130001c40c96004101c1c010300d21426404510760781745e80c002a1224401c039082801503210443d080c0f20b8010050fa004004c0c0f041c0c0000e40032180c00d0403186482444020800750501c00d81105a5040503c00c1118003a40c841d4407000b04105d00b00110000c0c05c11038000703c4284500058508581c039003c05104200400d025a261152004030050345803407090030925620511703005007100018119030a00080d0b100782464840301040c0d2510500c0a81407a5058000042e40da004420034400f05500048074026200112210000d2034625001200940741c0080030050319410300b00000100440750700041c090750400c170f403030400f5991407802c107040d00480654040c3d13001c0c40501d410b035030550140c4600c0c5294000d22050741c4c03010f100502d2250070340d5074144461840300d100004103e466074a0030007540e001602100c95110003000440050b54211001d00714440c048800541a00b4203130261080b940180001508013039290b07500c3da040e074440ca03400c5a80c24041d02503080000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 975364712 1250 975363462 975363469
    0xc08010203130318120807030807180b2b06030501051b0904020901020a1217100b1206012a0b070e130506040902040624020708070e06040f0912080105 66
    0x1244510042c8265600b004107507107040711224080c04008454112000012400d50b45025009080501403403100d0350742d02c00782c50028030a41d0010143c1c2e00308001e10780303c00c1e040c54441100a003200d111072440c03501c440d4840758147c005c080030100e6184449141c100f0365202c84840c1c000604503801078008026564408500e0041a1800c154012040300c00b00a070000500c0c20b5800342080b510f040c412a217447e050365030351095052003a03d0200110301c02c140905144280d481030a5480032002c1e2040c0c181c6450803184e01a03500404c24100b2245a40c1c0e4009400c0b40d2140d140c1203280200d130002040314000d010303000f08454005031016107092000340d0001d900c00e8021252214280d0002d071000c640e4809060741070004100247c82c02c0e42c0540c407084a071015030b50710f00407600a0802c81c440d01848600f449190160582d08a000c8401c3d90410801003181c01004205170701104c07404d000700c401554810b400200100701b0b002200b00541d1030101c20400740629225010710040c401d8441290f50303600c40c03040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 975365962 1250 975364712 975364717
    0xa1e06030b07020706030231031b170712021e2701080d05091e15091003050c03011e0302030109050c0907020106050901261b01030b0d0506060d031809090c080102 71
    0x2800b076510250144500301d1000036a042c1e011425030461428440c0c50341da4050ac02c0500c0c514030040c1c0c05d0302070003d0107004080708517031312002e4018005000c01858100c0c02c04401c4110040a0b10450344400d40a400c1000d0300c5c0c5501d001100102494180300d80c950601011080c01d2900103800103400c00081688000003404560b40c001c80e454050a15017034404020050034481030b00700511030070750400794164171405840c1701c0220b07085406c982c80300c16840031b01c40c840001c00c0d2964101030800040c06070074800f401c201d0f070664042d4581d0101d8101074000441543d411540025019840c005020f81849408510480004411101085a91540b610481c01d0300c5481c0075559100003c0001040f525901070b4410400790075480b4903002941c00c0b0342e802410306113078803515824681290340e002d95640e8544182c1001c4c40d1b0032641d01d49420a42d0301c0d07065507120001d00f118003075250b9031810b409042c0503541d040481021500283c206075290305001000d4402d5913402c40e0000c21041000c102c248042c0203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 975367212 1250 975365962 975365977
    0x10e0f0703080c120f0405011b17030604140c03040b0606030c0409051506070b06040c031416020c060a0e01080f0405100b0f060a02030304110d0203060a1e06030b070207060302 77
    0x1004000d081d500d448800d548032154010b10352164102007280554610050f2402d00d0709032500940f500c0c41d00c00050b2001d003006600c200410305003100c2100003074100403440c01d1141042c807070079200d99540001c6401081302aa18810800c2c0d00810440881d41940095214600c1800c516149440702014810140010b41d110121100f051000744400200c962043d9400300781411081c02d05030300d100c0814140c1d03128003803c2c4ca400303002c80204005828180a44150b00ca22071804110440c0041d03c044a030450281000c9405c0700010740000a02e80308020500070408010905030760381c0e084450280c42c44440040a0340450b8601001401030401d09a00c9440f458000024009460404940c0b50060600f01000c1341c3c460203010001d885070300c17088040c2c00708840903002195a400e0508005181c5509429014031502c940b82d020b0700140c601240880c2c05c04000321001c2008000040800620b01d0301140d4403144500e09000081486070245866004c2c454030740a81e510a511503900b10242e204565 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 975368462 1250 975367212 975367243
    0x405300307170a090b03070503180712020607080409050f0103050c011d010c03111e0705060403033c030504020f090106020c060a05070b070201050106021e10090501021614010e 77
    0x102e0000c101a41d0400500b02800c1038500358804e0783d110702c800b5000e5042610f0040000724040100f01c40c0002d03c088030346244079040000d101040c6450042003071404066402400340d1004519101005a80021780d006410501000e02082c46c1c4480140449003007480180d58610820314940141d50203a60707020814a01c00440701c801c140840e005640000a0310402c0701042004948040e2500c0c0510900310751000e81c94262068119a114482c5040429000b80d841104100010000a50444540c0e03014030b0301d00852085405c4108491f48407159050034044c9811100c594801a0765415446248601e100b02e400314a6000e01c901444858202401740c81c01680c09003503110424507012010b030804c0c961901d4038601c2c0c1210742c0d98010941c5001d42d40038016079151401400307000d80511150320940340c0044580d01d54464458a1980c0d0001003440341c1c005640c44500740140142901182c2d0100f1600b080d0414100451800420040c220b00b906266546001c0413117405903c042040320320f01001e40b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 975369712 1250 975368462 975368483
    0xc1404031511090316090e240c040f030501051012020f12120d05160c0305091306030b040c03020f030102090303070b0a14040309061d030604030c080405300307 70
    0x1128010092000301060100b100007807206040e15034003000400c1e19480c62260121042c1c0c5082c40d000c0c165602840d550085400100c90394281741200d440e1003182d5581013102d0502a00c513010102c0752881f643d0801d05291003e003101009100d01504850302a41c0849420360b0100d5480d80e062075091032080c4029800140c40456480f07c0c0382142115030000c42034815070740840301c00c00c204a400c0d8000091001c28907290820840c4406104801000c0003c00b400ccc80110b02b1040d0750300074218406d24030401d200d10302d90000d590100815501c914042c0da0b1182c409442c6081030b00f08004c500405100880c03080c28040c421605d24101030094840ca140003038011410715500d950b4002c201c0e2001040c8481e01550b5101d000d0f142c1131600c1813240900c1c02900d80c0c01c4a1410950020100d1001307a003d03440c01407542c841005103440020f074946d8881d402d07190440400c001450000e84512959200f1503020b05044132807000c01c06419544881040c3ca0300d00d1006c3c4210b2898210b840703020b800b001034250400d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 975370962 1250 975369712 975369743
    0x20d030e03040906030b0115021f15030609030315080f070608060409051e010510030b0c1c0e03040519050d080c010b06030a0e150c04050d060209090a0c140403 70
    0x69040210030654040603039042a49489808007203420690043d6841c01514004000c0c54032264459113a402c50380c03000c0c0100003001c044080b400050f4000c03011030565035202c021156000001d08802442e071110084c0310036845414000e01810350214824200d65161000060007000010154448017594028103146850444141c0d040d440080045030826140d03245000055410b10400c41102c2c0c5414a0342003031003031360b1509030850704018551200c4586104003800464640f099159003c09800e800c196180f05000310400c10364407007185c3c6030b2130030f080070351360010440044060001d881e0305580d6031021180c00e010b240e000c90103d210b0150040b0301590a00d0105142c0d80061032213074031060011030780e080402c2c04104190f000711070308074469640354001c000010040c00307807050300503d54588451600b0002c0c40c40382c4600c624803403244211070ba00400720402096406484003254010030400480c6071041d4541c0207410030b000072000017400e00c05441c0b802c54084090707d0a4942064021441421 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 975372212 1250 975370962 975370967
    0x30a0507411c0903030210200c01020705070f1503091208061f03050a050c07020a050135010f0e10060509010c02061c1b0c0803180a05070e070f020d 65
    0x1150380440c1040d00030440b08a2031541030b041610303240b40182c2d840c40b030010720b035060003820a071444480d84c80c40303428840800303541d034460f41c5055044031241d9000b85c1d43d800d921001c8d80c024440d42c24000c0c00c50050100002d00200c501c601c807002c03688010598801c00e0aa00340480841b1642000200f135001405681c0424a1003054610360000000c3d165040f0030200803003900502207001590000a0f89034010482480d00c240940364100200d02025400c12840c0e03400614000c8181c01800c1c1000200c40e400c030031450b0301400d20080e000145a001800504140c2c8518030000c09010700e0201c00c050400019042903080000d621441080f98842c0b015824248125019880a0016410004050781c940b02581c1e9960082010906c10918441c16849496820f016244085901041c0407401d902c1b21004d02e41001d80424540d46c01a10709079259210321084001c0c0030071804019179486019869410420001840d07070540715201079100c216a98203004807030140043e009000107070000442c3d805841d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 975373462 1250 975372212 975372323
    0x60518010c050f041a07050601031b330e27090d1b021302040b09041a01051b0a0506010636053001150e0124030e030a0507 54
    0x1401704541e29015458030381d54030f4030800785c00c10385417019422220245542180307000c034000c00040384100740680180c08862116100b400100003440c4440c1218100ca901c02c1d6111198004020110258100884d540c04107007440001400c031490241000b140488200140183c0010480d90340e0080c0f01c581402403c1504007640403c03078121074100408450b203011400a00f020701000d0004588680d4220100820ba500c0c24010302280a50a800824240d034040300303d80a04440003000c100c155081041a49001c000d0304019115008500002c40d00036480540b580142800000503980c0b0304901002e0140d541c6114003000b143c0241120421887c14940241c0d0a440c03500786251003600c81841c0c00046c401588594000240d640d80d4020040c1070608694001a0903500059102c56040107208140918004404001d103280842c0b680d148a00c8ac5e04030750500e01851080e261201070400000d0000e80100c0800c41d82041c0d0503101c41041c501c1488403100382e100c44c04500300e080a201640d0300290 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 975374712 1250 975373462 975373499
    0xf240408160f111306080c040b1512060a1d0403080c13060e0112060503070308091504060c061b12270c0e07140414010c060518010c050f04 61
    0x42a4600380700105012124400040d0300032040550300e04407420070404142d801d8a001100c1070b18000c0c4c240412400041c4440003040103940c0003400c0d001c1d04c800100d0503540800d0f202e040301d0700058211000122001098050034003590710300d141e0358543e00d5005031a0060407004002c40303111030005011a1042c00880e4000c18521030141c94051496800b0400d1ba41540003400850700000303007400c0702c2d40e1200d01680c101e807007000104a414280301c00240c0700c00c100c2c40003900d41e11022131840410b56a07484180320413a0341c1c0d50083d0341d842e902d04010300a480108015181d41b0f03d40701203440c1c6d0501d49d11444444441c50b40d2040c502200424a100c01083d45200801c0d00c10148031800e00001e8014800c4800c00f802180c1c0400002d25100348182000c800510305010040c0954003c21100c819801703a1301038501c1404400d412018dc100101c400c24a86107001d0081d40c1000180031015601e181c1081c54140498000e01c40700c44d41c82410789461103800c4081c003480c0000c020410002860304001840e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 975375962 1250 975374712 975374737
    0x501050303071a130506070905090601180e0718120203120703020a1709030304030312050709050303070f0503090904030c06062102090603011103090f0615090117011d0f240408 77
    0xc628245d00c50601d8220304644010114007502000d0107a03240804040e60320078002d00e4291486035081003001c0c10b604c103d1182041907036601000c20344803030207040400805040035410300112a92a4441c1080b50f6211030168024000c4035002c5294803001c5003242e03009501600148000a00f590301d08401011440d001030316075800384544d94599900b400104010740c000d580d00d12645110748091030071204040c00010070f001503440c040029403004815a440300303400140320041e108090500300d0940c858206056440300d038100800040640010340030a09500a0900700906525000c1d07460341c04c4840c84c00300328403165030321044005181c6008034a901c420050000b1880c40140d01417503a164000355035000c0319804c1003610a4a101d001c00001c0c4c1d0080d04082c004035030700640c1c00820041b00c0c06000c3c200f0442c1e0602c50542c11030b9002d411141094030780222403080300301c120101d80d03100e1a14084ca407440780038814241d42020191418420303c0c480c45840d04c0c01648070795580003469031100440840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 975377212 1250 975375962 975375991
    0x50a0207050405070c0b060315012304060b0409150602031b16121b030b0a24230a0312030209032103041104140714070f060608010501050303071a 64
    0xe00c2d4441d4010700340034038043e407521005100355103010761001d07400501e854003e030700c0440d4418450500c001118116248011804d03130501c940364102400c94a02480240c001b0700f44072000401c121000000d00403500c200908026804903103012228a070681e101d43d07001a0300a002c044948141c0d1100c0700100c13885d00341101c0320b8034822240d01c0b1190722203a102d40c00003140d600e21b030000d00810382900c0c100701a03c4213100b20402c2c29a40c44501192024111f640540d40d61200c100c03229074120003510a0713196194445400540d0748003070904410b110400244410141c5032503d0150410036812016a64007a03c40c0c0641c070b00301c0c0d0b8104c0007034104040c016418403c6110b5995040100100000d02c07100c081080360b0b40b46410304004e41000098048180500d140c60044c9400f800e50035101c42d0002d40f20b19002070200c00314024030071a0b0281001c040c0000d46d40380710b40010807070a03901100480d40303000001c2c011a139944003016100e00031080054021401304052440f034614520070140e00007000e07140c002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 975378462 1250 975377212 975377219
    0x1080901090c0e010302011e051611090a0c260a0f14041b0b0a05090f060418050402120606031f020d14040b0604022a0a060e150708040b07050a0207 65
    0x4070b03502d154888144000f14100610a40d41d101d118000001e8018032000c07500d03030319a14014407a201d0a45504d041d8000c034440c000c10011240c02c0e407210400001e01300b981034201481c4c10401000d24186410214030381e10f039408103028900ba00c001401d44c1e005152041c5a85d080c5440e806880b20392482c501c07140d03450b5485200a800c0d400d0280c050303030040b12641035851409030482046056500042003440c03051100c2d0103442e600204a402c01d140c10794003980c0e46480c2402103500d83c01142c000340010090b40c4a0503281c4025603000c541704a001700c8548400c5850300b58102e0721000141c0c0d6950301500040c440b00d03100d081c80c03190010301914003800141f40c928190319900850310f02d00c51f0032130300040c680e0a20007400301d904100381d00031004aa0440ca040c0719400b00181c0c450450070383c24032840b8000c545503000602440300100540e0001400d1080c080c084c4050383c1c44030105c800b00e000c20703907110f03020030181c610503080f2500c21a8080c0d412401521084001d03901a0802c0040000314441e968011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 975379712 1250 975378462 975378473
    0x1d1b040f060e040c08101b030b0102072705010515120403020f10050114040b030c132c0607030920060d15050a1d040204180c0608010e1f03020108090109 67
    0x10711a50241c4c078046980b9044c15445810300c101ea50f00d9600103400c02d002c84108169141c2003136055101410f0004440c0c2c8170500603410414294401c00401618112415100c100800444070340f03891607078200066a21441085407014040e00a102d07000303c02d00038038404544420710913401901a00494410800b0551201e05d000c0c1b20301e205005a43d107070001045130059809408010200455090050f40408804aa59901c01c00c040c103204100c90304a0281300c01240e4003a075030603d0502d041c01c0703560151701d51801c151501342030921041d11070400001c062600c40d1045040a652202200c0340001140340900e00b6210f0960042c1c1e8060000c0181c1801c28000d446400d00784e094032410882c2c254584410850340f1040d51340a21103480c840081c00d0002e101e285415a84140c2c11900004d441c2d904d44107031000313007203c181c00801c0c00d02d5403a004200184c00001c41812249426080358072a40d60000b107481212203107803025509200c540d4103100542c01031260036800711690f40005404072054540 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 975380962 1250 975379712 975379739
    0x1704030e1305070315060c0f02091f090b2407020d030314070e040605010e03060109020d0e0f100605010c0f0201080c0d2309120f0c01060906091d1b040f06 68
    0x8100101c1d07a240344107404a007280c2c401740700030866410a000e0a05098640d11560044420024466402c0d0400a8225066160700400400a4940380c65805031a60031b0003004108515a5920440c0318408402e051030321000030840f01c2005030526410001c007070f800c1c09a070f038802201c2242815201e4228101c0d14031061006032007040903644040300f1580307020610040354410380042e0304102c0b480c89410307034039107000580314115007a0000040e900d502000d40d9000a20007903906c05034500800b000030303800050004908002102c600010840103275290015030b4007200c2d804004041c8014140c140c0003542c043d5886503400078403030a5251500840d00c06040c00c8a01c1c2c11800c9070880305201a09080b0701b95040c00f1a800605100180b401403020700c14000305008141e0a051003003000500b08840c030b8000c1d04000001e01e008002481216290f85d02000604815000c5c141001603210306622172140c00a020b00a0241a024030540c0a8183e0240000307006c45448060302c6a442301d00021340c0502d80501d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 975382212 1250 975380962 975380971
    0xf050702130216150b0f01110c1203030f0c0a09050f0d0611070302060c090603040f1e081b0705100f11060a0c1805150904141807061704030e1305 64
    0x481681c0184c508100c507500b40d42400d00b01c0b6890840081110745a000101124040c242480711a040502200d80d15064504c18259000060880c030000907510000196000f54190140d200d00390740d48202400903400b5803000c01c000601154020041810302c42481d00708000f02801107903001d0f40c0780d03c1c0c03038040e10351080c01024404c4001031040c061503410302c549a0000d0b81048070502e00f0b000900001d0382408064000380100109000c0c0004001400c0c1c540035829082846128011655080200c00f07038200c00e130103100c0c41103803044607a08424081401d40079514014400c1c000c02090680480d003594012003003200780700d9011502e41e088601001014843e0840400100b0709031540003008016051005006034400000c00c1c0501043d034501000141e021011215162078a800310300240140006883e00e021510b200c0c03050219030200350700e503248502c1828080b10503480d941c3e0821078008440e20180c100c4601114003040000e0b103d0350040900c044024890040360002107801c0044440c19907 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 975383462 1250 975382212 975382237
    0xd150e01060f150206043c0f03030614031216020301020c0a050c0108010f0e0421020708070602030f0d090206040302030d080604060906060e01030b28030606080705010f0507021302 79
    0x204000f030000e84000310034003c1c0340302419031401c0c00c1e070710669000301e8031404014004481d400104504014403e0845000301e13024200e407158400d04042c2080025100309800013410040041041d02041c08840001c43c401740081c94100d940d445500741e030b9040b5841d41c44140007050220405070ba4240058150024024094010a8000c1c82d12a142c048019400d41c148066140100154501007040c14120351014021035620780d00e030300d0220310211400b941e81558010080c2900300223607000400d041511280da045403141600d426059903039000d000180d01e01b50310104207040108200d6007012075a644040c01603410182c5a03400039040480c2d8041010010350041304200b8140f034079006150040100f4403040100d141481d400806210b00c45480700c0c14161901403e50030f503160340c0000d03546941e0310142c102d682100030f803c41800c0d243c2440282d0b001c0b030403c080030811f01c0c000b1504801306ea505031500700c4010141d44003629581c000e40130590f40480911522800846580001c006034090f51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 975384712 1250 975383462 975383489
    0x50615120d08160305090a060203070203041212090905090c0f211b0a050117100306020d021806040e0f09031201060806030d080103030f031107021305180c0d150e0106 73
    0x201d000503120b01801ca00e40f04050410303050298004000c6134010404d40c200001683d03d5440c5a026482c5109980c1710140b00e64601d00c40b0400d0000c0c00c0b40103440d8000359036968159540e2400644155402624550030b650445501c4103118a0000710b03284100320098030140c443c94507840c10301500c0e007485030304210b02d42251045030a0500094800d100d01e00d400c03140324823170f00e042000003030004031407800c0f020351211440041510000321102500c025030b80441c0540d520001041c058000e504220001c040c0704070114284115450140d0a43d01502d003e01e81081b041d03903540b07503914040c2002401c0300f0f9481c04100990004007041f10000c9010b800e650300c411a003410a0001c3c1440e144000c400c1c2c4041140030001400041d038400711104030070050346000300e2407a0070100d100c1d032513205081000303603c0010111100c4003241035410451240440807070607080906401451900c449212401503401041c03880f000d0005140d10030140d031428446000001c0d00d0f244026007500b1503845421100349044407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 975385962 1250 975384712 975384721
    0x20a020607080c0307090e0703021603090603180807030f27150309031707051b01050a05060d0305030c07111207030b0901150b0c0a050d0e030c010309050615120d08 72
    0x400e0040f0340000201c0c10b02c2d4a10720b848400245000001d015102c034500d4000041040a4803d0301640c0e0000e050000f810825241c0d450701521104051207010302190608043c4a15400f0404d6803042c40ca80208500c0c2c07070100c85640444e000042c0186800510803401c1d40c4c1c2407044015500240e585555802d1000000c1c10040c0c040d140d0400c0420034403c0600b0002801c0c0066800745401e506040800080485515250400e650714010300c54440c1061050125500d60200150803c50103032801800c03c208175220350701800107075001c51f50040c1c0800c00401c046502e0f010a68000c1020900450003050404030700400208001c0e8840c50800442e48284014801c1c00166080503801152042c0200311030304410440104600c0a44911900c603000443c2400c00e100d810300075405016070050a2740c1c00e070001008003910407410858018040e105100c000c0d850f550080c800c20301402d42120050105507980400704440c0c240d0313202403d41110300064501010035041042d081c0c25055a101c6130401e240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 975387212 1250 975385962 975385967
    0x70315150e22020f040e160501050c1906020706020c0a02010e01030e1e0304032a060513031e0b070309050c18010b07080405031b180c04091e020a020607 67
    0x58110400141000d414004014882d00540240710004100103030074050b503000050300d4039840300e03001c1d4110f03040c2002810012004140c4000d915081034012002944500044130580035203182940c5c640d0240f140f120b429941070006026140c800c0c0009803801103c3e9035a181070741c10151141d403450b0300107401301c01113603081008016a2039007840c082143d03104080b82503907240e07000c440e10300d44500c1c20709070314451b00c506200305c070040c6400c11404001da0180c540d50f50419802da00031007051741070a0101041091103102100c460b0b042c408000b03800e45013580c40e075001074120400d003161018424402500016484100f4510030034003502c0001d00c0c19018144182080b00c181c0009125076800d54028807061200385220b4103607072544c10107a8590810b4035141e05244919040143c2c18400c0181484031640792030300001100030300703441300030100704c9145901c6c513082000e80724a111903106110920a41071168400c00003c4440c018180c81c0b104111614012603100701d4481c070040c0c102208002040d038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 975388462 1250 975387212 975387251
    0x7030503040b03060915060405040b0d06020c0a150c050d05070e0d050c150c0a032a111f021b0105070204050f01171c030c0306080d0f110304080a0204020705070315 72
    0x140000e8101b840d030341008000400d00d12030303801068425661028440c4403500c48990b1600d24035400407045643e0b02020b6640c907583d141b01982210414400c401d04501003a080c0a9040e000344941c03101d9081074041c414000180034004d00c4903013000320003a6901c0700e594030a011038200328014400303400d5421010062200203c0d060384c80c406469020000302c0952200007400f9100769405180030f6083e0b15145620401c81005079052103041e4000010400900c40b40380704e0600390301c0c422501046100c280f200030a446005051001c00903801102401841665100703c04070500c40c14580325150507503e074001070032074030305031200c10508403a08014002d41ca4006481c1c003156003c0300003010008050280d14800320002d0782510105500c40c4d02a0200a02075080a00581700c07190a40300704052015004090400394100341001441593b15902e00480210032141994400c2029001200c026000c2c480654000d60b411249031081c00000404200a03038644100000c480e40003240710010074000c40110b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 975389712 1250 975388462 975388471
    0xb010c120801062705040507030617010b040c0f170c0d1805010b060f03040f0807060608010504020102060f0c0d051e040507150806060909130b07020a170703020607080907030503040b030609 83
    0x140b1390900e0f464014215103120103d4204030750205582d600c4c4d21084024040300d9020240030802d0800c01c032a0440f06400100c0c2e030f2442500c01708002548801c0494120310340785100d0010a01500d03185521803d1042d195620450780c02c4503d01d003c92090791201141c40c0c844100c008402c1a64503403003040007e02400b8036042040716964209a441098090140310262000700504210303103540342044980e0041e40c200c541c0045040007501d96550381c00313002c0c0004a40c200d0060180713a00046a44d44500b00480c058124441c0e16800d00064190f46002040082d20030100c210001060300d0301c00420040fa24031035880703a006012880d04e400c111460080238800980c003407040180400c001c42d1108015214645400c888a0080391204010100158840080a0004003064081041d0036800040881c9000d204030300c01c840e920601c540041c5180105070006005800c03200100d005c8500c51004d07141c1054055091311466540c0c0c3d038071589035610990040803044404010058949404403c45030301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 975390962 1250 975389712 975389747
    0xd030e060310030b1b090d0f1a0601030e07060e0411220e01060e010219060b030604030302130e011a0901110703060911030309030d0f02070b030a0504060b01020a0f060b010c12080106 80
    0x7601c0215034007503450143d8a550781c0504d008040d190113012045480083c42c1d0f801c40840d09c03003e10b4820700c400088200311081703030120b41032a14054400100048510880d0341035134901e454000c03100f040001500c00c4200388100c944041c03103f04407216880b03403040e0712100c06001e41c403034261800804c4080031205a000348148407081e030494000e03980101e0f1108204280310b00803c0315031442d20b8000002c0103a600b03250340600c900c5d0200310416030036500411502408801c55a046a581c0c409086501400d01030602c051110b040100c07400c0f1400c801605040310141050482e200d00c8401042c80c000346036109030b03420751f11500c001d82401004907500b0305852080d000365103098001e02c0865558a0401103000400c080568511841031007408403201030044100b52640e2810045c42d01000350000b40c500795038035464402242c1e81c4d1b6000048003d4603d601080e804600c0c482034032070000425010720060705001944194200141d0503402001d41c10781c1341d0300c1d4060554100781004089a250a0950f0903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 975392212 1250 975390962 975390991
    0x20d0606080907121506030b070924020c0625050a1505090c090a0e0106080f06070c0f08070c0312021522060203060409020a0609080115140d030e060310030b 69
    0x1030b58000d8050701c54450300708007176011746071040f5141c50060001703a1014204144205c1807101e00d0b07030b00014000c201c440c5034031588403000301042500101d43d40745003d80d002d40d109000060103820250050f0254102071251610300b04049201c1e240d81d240075020440d200c7d040318000b0410010490352030010007159500400441c07401001030b60b9611541d03409a8420104080014070700701041c0c01180030054040300070b000b00c69071b94110540d585081c00c005c045600644001a880d41e21076040c6065a40c1c0000e00e8507005291900e900a20303902030842650020407030340c000f00120341c80440c0b40d00807940fa58010000c4120808440008075405041c1d41c1d40401d841d045c02842484401c02c8a203480d4201c1001696038880c100000d000700301d2804025040300c100840040d06680081c00201120800c10082c00300180c607600503044503259014502d030000000c1c65141540c10a0031541181d6442800e210b014040c1d541300180b02ea030400c0b85c0c140c81c02c101c410018020000b4511145400005910007142c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 975393462 1250 975392212 975392219
    0x103060e0a080306060310031217010905070509101205040b0f180c0402160c091d010506010c0308220b0a0c032703180e0601140c150613020d0606080907 67
    0x8102d0320000e014648100804008207001a0000c1d030000300441d8800d01204004001041c00741c298103200c000030401503601d0000040301c4540380103191059202c0d5840034542423000007000f0095080004101c200512001c1d813628103caa4440d50f40102d0080300443c40c580382030100da132050800101034048031103418103001003181000818030002642250090780b00c050107411000740b68201c50700502000c0070288002044c8443d03038410444464045000b59030041c035000341500780c4005a40341d900142c0d2401c41038010900c624100d54100300307070b1601c50824421032605a5189160300e0700c20f072008003001d0301f4849025010b1003003c90034245030a0a12080103420216585980c401e69290b01b040e031800c0c903c1080500c10b40640e03002e0118404020360003500d40c2c1070142d0000044400902040890f5040300801e902c030f80664030340404680051010106c1c41c9081c420300300000d040e803500184a00032004001100d400074020905000900090052901ca07000300298406806424940c01228003031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 975394712 1250 975393462 975393473
    0x40f081b07030c15140f0d110c06090f0a150e1b1f051611100906031104032402041a0903060619061d131e0203101404020906120103060e0a 61
    0x17040300314400d0142502d640c400300b0004603d12030615650a25898020301400c00c4a018002d0b20758806010100d401c66034945040d2566484038021a0b401503209020b880c1c0001c00840c001c10510080ea107000c148040c0c03d54810b07190950103101250711000e42100c0383c0c00c2d410480071308505103400100c0645201e00c00940500248030f40c090402c0c806003084660424400489411060702c0c4d405060713030b03c2c550120103000303110403510700072480024102011f4907003407060001500c003681c2d0003501c11603c0907142c42c12110700c1115a40100d031030316024400050645907100c0402c1c6030440040c002581c3e200c11100301403c0ca2030040c0303603502c258485940a1180e000c6140d01c8000e459550600140c0c01e00c4040c1c04500490705205141d512492183c036020b141c034083c4d04004041c0b0280140a405268000c111030300743d00044920403130714a000841000740d59000071195607201c1002e4801880d00509002061a07030f404280030880000c8000c004004005031442849011305400020701280760807660350 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 975395962 1250 975394712 975394727
    0xe09010f110a0c0501060302101d0102031c02090414100314070f1a040b040b1206100206160e04060308041511030306060d0e060f15090f040f081b07030c15 68
    0x20304104030568040f401003080035448400a150001c040c2e01410480000c02008811054000601c1b9580050808280e500004c1601c0401d244440203d402c5004004450003d400c4441010751040c1c1302c410101c1d80c5140810301c2e81c090b0004004030b0001c00d0641c207112a1000325084100c406900c010410800d0180203170094056407550f259100404d803680025112030b01403a001441d4503200000c00003000b02e1801c00411031940a03011001d103c0d0750781001c101c1142c1c40810310f040941c01840009803041003d82e1440181401c500380015101c0756080450101d4902e41c0040b03501010014043c4803003d005440d4000c61480382c9085031101e00400306003600c0707004c041c10030b50150310041500140d94156412601e450f01034402124564a0314800041c14120f040c0c3e24040803070401c0044a0950900403043e80c4100c0b00c041c0f000c03241d03450341e1391412914105144103855106061001d05031621034070710381c001c001c416140280a11401c41c205905115056400b000c0c0d0030340c15080960380560003000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 975397212 1250 975395962 975395977
    0x201060e0f070c0314031515070201200a06051501110f07180b180a060f081c0c0812071b12140c070b041d07020318010c0b010e09010f11 60
    0x4010100f8540c0d490f00742c607401e607490800007500d18048100441d0848a26055003082030440303908000d0b0313a25406a41c1ca521175900064006404076296042c0b420b8a188800785141040c012104d070081c0d1030b142c0c1002ca03001601c204a43e80400d603038201e910340e44090300c490540041005004080c16040e0302540d00c0308030f8420800c002c42c0e104034003194401c26505c6041080b50140180302040c0c6090b0404200040c115030700f4005616040d408200c612034401c500040e280c4480080c9201c00548845031a1501c100b42d03843d041203500c4448200250400c009031100c0706840b000c056140c1451400581000c0044c4000c60121103000d4054020400e400c2c0c0f0b082c2a000c10b803d00706880501c5e0507145804e0321820076900c0443c0710301d42d00000e90305030520090007250000c00008408118044182c00c1d141c4059411900590040c0880e0a00c031210541086482c941410080700540e151703551800d00c0c41090b8080c0ca19654607004006009800707000740c00040f2030640d010030110345030322030b052907074001c1c0305 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 975398462 1250 975397212 975397217
    0x305090a060b0a031a04120f0917070909050f070510120c0e06040810051602030a050a0e030607090806090a020a181e0b010f0504080d050304020402070b0114010201060e0f07 76
    0x2442c000542c0c46801c404070245400c494030085900040307003c10722008007a0b8080360415101d1f0a100c805a1045600301c40c0154950b4885440034900030030740d26004008000003405000718480001d41c148141b04401c203061041016240f1081000009418661140c0c0400d005011204908000540c000c000c0c010f818214100003400c80c054900440300d041400c000c445d0403000009020480690025000074110309000d4280031655400c504a10000240303180d0001503031041c8000e1050360b0141024105240c9140707000503c82c80c00d1400649400c5041e00e002010075040b1200340007540c018440b00ea8848540c000910840d182c0b44e012071010309151080b6004940c3c080004d245500319a000f5003c40d402807605017403a0040024104002c1181c125a54041717401e0305081002703180100c4c103a40403911000080d00c4030090072502a1440da1000f042280d0084c0c2c2045500c1c0012585924540a0400070300c0340500c01706c10000190840765190030158411200a0400044a88005446600c500c062 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 975399712 1250 975398462 975398471
    0x1060e0708100b030c09040e0105011e050a03030503060d0807031d0105070506010e06010315080f210405011d030105040c03061116060b03010e06070e2d1e03030703050c07060305090a06 81
    0x2c17500e50b0701402100d40696100b42041007500624005403c66410381d50600c03480c400d140d101100303510200080c0e2080710342100c0486010070100c1e0040c0081c640c4001d024101007c8412503666000e170561012600314080307220004100e088800b0446030b0b02c1a1002820002d00d46107103600c3d42548d407401449124003113100c040c0001c0300ca900c242c00080510070688506042e4648a0645a44800c01103484c0d0b20141300c3c0c1c21200321030340c894008100001061840c1c5901d01410000116085884200d0390003081d602c041c40750384651424805e40e441035014911803441c2908610748441500e030740080d201c001d03a00c14040542c4804280f070150911350392080001525030100000700380985034a00d00341c0c0c5a405903108000b50240c00c008140240201117170012084a80c4840c0203c42155800d00c039030034038060b900d502070507042c0102c02d11039400e4140022130410101e040020701d140d10086044000030700200e507444000a080043c0d80103402c05003000c0c446858804a029070741c03004200b0140050351107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 975400962 1250 975399712 975399721
    0x3140f0c150d05040221030408010c080f04120528030614030705242709011a1b1209011d030a031202090a09020703080f040b0705070501110c01060e0708100b03 70
    0x1800c902e4a110a001d1920440820300101207d440b03400501c10341c0c25030750a04025a8050f0320420800340306d41c402c032034407030180e8032192101003031110284104030501008000c2ea40c0c80360f2042503000794881a24241c1d041d1100d82030307001030a45641740d120801649540f025400a560081440b100b55482590314203c410844c140b5101c003000f000c0e5110244880020300a600d6440030030400c100d05e0440202412881d901c5810f0103513030a4244120f00c1e4142a0000c1c2c24000d840c0040200074500758800ca1107030040d95641e1072400c001909116202000f0002400002d950700555011186140c544445c00d458080f04042901c460b41080c00408005228004504c4500c00c0c0d8107841400c44c0207440b03941900c1e181c000781e00003580100416000700700341c20002607500b031051456510541d4000d00b402455101c0c00030a072195080a04116001e549a00305441c5046590000c0c040b0303001514008188140b030610142c0d240c540c060f06003003c0080c0341c0c04003c5881000b282d030808981c101e855141e6a40c0d078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 975402212 1250 975400962 975400969
    0x1e020322030606080d090e04410d1101140a050c1e03010504180f030f120e0304050405160e0f040e0d23040303080406090c03140f0c150d050402 63
    0x1a0341e040144054900b030400b250300d03007000403010490002601d640850039100d101c001d42034079040790010442e0621700707443e5040418211400810b20001d44090b211840502c0307510782494004140c402042c1c0c40444d200018503448180d008244950400030002d40241412001a8007001800450fa0907103410104650300d00381011603000d24002d104421040c5403010200110350b00030301ca950f105500748103052000e41000882c0c1800168008a40c101d002030f10b98060300c08150000d814420b02c100d2000041945c111b50040304035615049000d55075a0f41004100800c40b640902030060301462242900e4289400c00345014010300c0840e92000c02c82281000100605108920004107014110b07420f003086400c800b10120021700d1641048040c2160811003125008600c0007900150032440401e0104207140d2200300d149015004020307200b912912100036510015450f0f80c5aa481941201107102c001d200074031204008940840da49500c3e40b45071010707800f542150418450f0f031040480c04554 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 975403462 1250 975402212 975402277
    0x80318070308070503030115261f0303030f1d0601170106090f0b030d0e130e01021b03180405010f090c020f010f0213090203060a0b03070c02031c1e0203 67
    0x154001002d036500c1c00d0614200c2d403250001e203c2c0f041908040e05c040185030340078614450000e01c41c200e0306000980a225600709000e0054030894041c50094050800102c18540c20406180030361000329100081045000c01c4807203000d196802c5004408020202da500030541ca4111070021035150b4103240e00200c40345c01001513900045255181082e80c6d444074001d034101c58034024080b02550100003111405440000707032014219444011040442c615051680c040380240445000050038640d0204100743d4075250500140c6036a030003c202450030070001c0226803d2500d00351018881545800503070842c08249000b030540840d110100101050302c20000c020311704602d01c00a02169011410b0017009610418483d0454442c001010540711514021203000351700180c86011168503140f40c1100b0f80c1c00280620080080042401c0090b036010040d42e51003204000c49515001c0e40c13000050a900c20a00340d01c01d81540050a03124050f40110a0318143c1c04180840c8030320440110f407401a0780c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 975404712 1250 975403462 975403469
    0x309010c06020c011b080711060601050c070302030d050405120111070f02062a070e15040c170c030f0a091208091204080a0614011202040b040209090a0f1808031807 72
    0x30341c44d0048407044817101015040381100d0b551034450040e1a40c03201201d41c0000300003800b0055010102040d0035501c103c0003040821b20782010b60303004c1903c982c0040d0404803691140000680d000c10b0510007450485160b03d030f1204000c000308040420180150b0b0503000d41100500080c01c04503001c0155100c3c2c0c011104604600415804844c072101400d94600a90400040041c45403a001099002d1481170301801041072100c04002501c190341040054020080894100300d884c141c0c07085500c0c0c0800b4040d02031048214055200e290040750348090030300c010001c0c1c010341c6c00e017142d0002051a4000c107420f03001840c6407034000d980d100d034034241c84c0002140c2051030b0408006000030b22401d010928071001c1d48500810300c422090340626602e410303000e00501d102141401c0c5aa070040c6450351201c40c079204c000c0c1015060902d0100043d03404070045030085856526408050031101383d40c400d00480075005103045000c0c10032911000e4040c0801001d200081200844400b0f800e030b4200304100c0107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 975405962 1250 975404712 975404737
    0xe060f03040b0a1b0903120c05031c141e10120605041104060303090605070303150314010509071d0c04030506040c0e090606060706021305030d17180309010c0602 71
    0x268101442e040361650380446803c0e14841c50705141d21502401c2c40341e1034220f14129604d00305880d04644800b0500070816000c5d405000c01104854000340b028009400035009041038807410360340c041c0c0c00c1c40a0329120800300c24810445c00c204070044102c02180c41491403c1034152030342d81d0340c1d0b110000c4464503d070403139926203c06c202c0107000c02c4807a8000b01e100760b2140220301c03100c801e440c00f4401600d255010050208e060200140040c92007400a00b800034024900401e61140c00c183d035924203000c0380c009591401d86441c4903e0062001d0042d16044006007000b00005494030400015041c0b011220064192401c030200c0c40300c000e0902035a0103103400006680460a040c5090f001c03048003441581c07503008900000030358140700460014841c24002d425103152201c00d656100c029880000c1d00c101e49046120082030a4608020090418a0075100c000300410b124506403240b81000b040750031400800341a29016000100c141c03035030340c242801c000610070324505c0c14202074091180c280c1e88 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 975407212 1250 975405962 975405967
    0x1e07020d0615031103060c09132c1519090507030606240302271f020d09050a080c010e0136050f032107080c0601050415030309060e060f 60
    0x1440402c481c40503084030711580d88040003100450501d600c61004485c10050b06500784104112414040442600c00b00049000108402d007480c1040000e0440c0203d860aa4044040751071511800c100000c00301001d5020300c201c0c0e20f0075034007d01300742040c1e00c1e00f020b80c00c0d12075403c0c9040040402542c8091030b4080010701c9116141d1440c50740007040c02c040c594060b000841740212085c02031003152620790320150140c1301024a401c20451031403940f089190040d0030240079403803001402080c18a15000c1d58040d0240d45000340009000403501d03000b0910035000020300b007121440003d0000e840f0142801c1c464856a007020041e81c040700081e11151440b042e04041100d40d2190b441924016003100015800f582e4980080c0300c500c0c0c001502c1a500340e48140e41c1d03844003035915540e483c203040b042c0001c0c9203000d445980750702040d0032a29100d41c0359442240103001e00d103010300a134580c0f20040f108004d0003500d15203008150401a114000138032036840724050302510344000702c400442107484c40d681d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 975408462 1250 975407212 975407231
    0x209070f140318150108030d150302061b010e070509040b0702120a050405011e05031b0c0a05010501051203090a06030c09050a0303080603060606090a05040e012a0e03031e07020d06 79
    0x100d004003031800b040e40f90700a548440036440d03450000c0c07038140c0f1001c0e0300443c241009404410010980300d40d804040e981c60100000042e640ca000a09450444543c50f50803602952400d034292851b880710488290070108080c4042e481d00303d8800d031300c642c105041c0d01d00c6031a60b6101380c2c00e150a040c91040c1062002030314800c00ca400000a000319202aa9801c05080e0504981890198451070503400103204101040008e03a050740c908181c0502165414a080c18030305e1080d02d0b000d102c000403251a51120010044c9103407401c807420541f040313200510329103058900041c01c0007005001701018580d079000002e5015102c2c01209001e00405007180d81d02c0d0780c132030401603d0480d04a40d154480c0c49428002012403c098043c1c0b80c001c040603044011003401d0504110140604c80e01690466603140860034036000c021b68844a480b48940311849100c0c40c10f4402000054030b007030220f000368410491103812001c0401c030748022a01d00c10710541c072205a840002e989015112000d4415800d00540b50f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 975409712 1250 975408462 975408481
    0x3290f010806181018060b040306090213020417070807030b07050a090e0a14090a020a120204150b0a12050709060c08090a0609062318120f01020703080f040209070f1403 74
    0x18117aa40300130803d101d5440034400001542c0003405415000c8034144410000a4a1900700030f11040c80100356103105091880b54408a8120780c1c401d00c03076820311401c500c503070350410f21002d030142030450040c0480600316211200344160107007502c0100080040d807070b0003441c4141d40030030107400300d40200d14050038410441c20262884004080086172504046080414005107102400c2c0d4017610100c11185446911200d90303240c0903007660050384a101c0700201d000c1003502e0a0141c18501059900c2e42007250006003004600c41d02c20090915040038010301c9900503042804403041890301038150000ca103402d030140e0203a002e5958004600103030120b036083d0001117078400d40b03940c0d945100030b100b4484000c550104880c6c8524400010400580425911400007101c0c6510050695400f0001c1807020030300d071101502d00822031740d5022404004040d841006180c02030b081404c0600241882d400040409201a00010912001e00010010280503a00d420026440030b90200c0c2c0364034040910 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 975410962 1250 975409712 975409741
    0x2121c0c02210715030e0a080a08010b030f01030609080c01020d0c02060c04030b04080307020f1903080609190b2b050606040912050d0f060603290f01080618 69
    0x3284030b4664203000ca2042944500040e400d0500000103007121032900d960b4000080c8000150b400301911022102c00310841002102e5629104100340c55803421003440050030400107802035605010f0410601100c1e0350f4410741c00d41900c0d0000c1300007039036920500c1e1059652060709483c42c5203500105035504014259407010844038070b0350b02503940c9961051909502486180002000071000300086004212805c02a5902000e9401102c01c00400200c0300c910300380003e55010081c0f510090180105a84218400d8000360b081d44c01c012207050020b0b020841100507c4a10001c95441005d0b0b500c07a5284942102c00c070014607a900b8040e40c3c0003104100a410750321060380c140c410710011072460305080c0b061503800e0f604401100c01108840000301c502d50310425241020940300d074900720000385203210703a000509450700d00003004028456003d9841904205420406640300c0d5a504203449510701c0c4007a01c002440c200240e5541e010010351a0f140f6107403205000c3e98600c00b0002501000a007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 975412212 1250 975410962 975410987
    0x30307260c090909120d0f0b090c0a2a0b090a0204110903070512070501200610150201110f250303050117030304020307060c2a0504060608100302121c 66
    0x1002041c0d95181450139a842c180c0b200d03684c00d110410426031030038845690004000160390000032509440c0500000c24810096440c10010400056681400b54101907254501c110070135031000700341032845806a400280c040301400305603444000a040300414022440f600d64003d0080145400b0741d9802e200c5a041180e000f8003d03c41ca2002081c1131414604403404000e40d080200b000d241082e00441c8e044083d0002c14160300c100818405520009008031031003142c1d024500e140d803600e0b0410b05001d84c001c2c5400d00065924160002000301c00c06c81c00c40d03030b02e100000b5840783d1b10003c213820310b9402c4804081e606241d41a440141040544c503030031003412201514000c44c14405104221a207a02c81a1030007985a48101c90401260f401903030800c0006000d00c01007682820785200907200c18605818800603042070343d1091101e89010702c86d8401030b01c068580154540782c401084100c460403408064820400c070f01c4030781e56510f0704014905000700722400b4a090914841000b5103203070503184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 975413462 1250 975412212 975412219
    0x705012f0736150801090305070b0105060a091413020d0b031204120209060409120e09013f080c0109020109152f0d180602060108030307260c09 63
    0x1c25006640b07150907070b0b0070301214440007444490b0061005031002454401c44004a22540010025041000313109184c42d0900a807507590780d96103c3d1030006001c3d101600401d00c104001d0280340d00780381d400100081038800206688402c90103c2000503840c50951f000c942c51a0700003d5810704a5180f81c01941d08200b0580071180521082008aa628011401030240380704611001e48003500e05583e0300d03600480c002d0000511030450744c41f2071041a030f4170144c40c03021600f41400b52a05041031130320075004010808405030400c1036006104090300c10a002841d0544d6007010314003003504174a9903000410f43c02a406030396020303042e51030741c003901c0320250603404181614400684086c9800480103050320580d248080145a11519a81d59480c64108081001058141c5244420421800d800043e040c0c452904094000348602c82403c05c5421400442d00b0100041111f403a000007a25044100c504202e50610380c2c0181221100b6581c3c458104180711710001d1000301049107008021419056 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 975414712 1250 975413462 975413489
    0x43c0c0f06030506030319090b0c0606010e09090c010305040206090405041209080304211112010902132703121103090118151e0207080a02100e0705012f07 68
    0x7168141e0484038119942d80e0150410894108100a00c215031081c0500038181000610349032840301500d50420342081c11558801c10500c502d6607042441d002c01c003002120000218a00182815202d40403008080d040c1602d900c0420110f6a80c103007903841c038500103030080000345068101044a443e0003e14000407440c48200480c0544012003200d0699160702035070706032080041c03014a052030340b0000603100451802d2045450b6990480010780000d40e010010030703002d0450041017a4042d800300b003002a540342200c10001c02c41d00040302d45010b080740140c20002403080c20103031030000101e1b410a6040d4034040c103003807a098000c00590301911000000b0405107103205000c04a003603551401620303109054040d0070740d10609402503243d4002e1150003041415030003107882e09130780024408542d210350126400700d034540d040280c800c0a0880c0d410511000105443c450340b0703810303a406442d04015540b02c1d07203420400c840103000560041030307a07680c03c141c0c21491400e8a5540600038801501240d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 975415962 1250 975414712 975414719
    0x13b040309060801120302120306010e03070306021e0403020f040b182809030e19030b0c030f0c070f060b04020403140a060f0b0112020901022d0d0305043c0c0f 70
    0x1000c03c4410406d074035800810b84000000404160360708000c2c81d06041014442e50110580c60030320558004610490000d40c440000e543da00580e4081110004a003090174082040580c0c1c6a60100c1074484041e01c0c00904100c0d103c000c40e00ca4103441401000300e110400c2809200c00100b07418080008031952050030f4201e209050300c050b0390002201800296070395a60003ca8544061081046000307188a00c540302d40c2e80c1c1d22140d8003c011aaa11108000801002481104c002c00705074844140710707043e07151002070b54070350031003041c4224050800d50b5961451500303611554110307005990040307190012500b849541c280d9620064004907109400c20341803c0c000070641c0120600400140c59000380d50111901000082d000485414114407440c0740c802210000e01d4003a1204e40d80e0b015565907400710340d021041c90f040005050f04201840c1100300400300b0880500740003542c00d58603410310103001d82c4071107205059510000192407144018010708101c011106401100c0c48003001c1d5507829038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 975417212 1250 975415962 975415979
    0x301060501031a040c02071205030c1006030b0a020f12090c040b01030c091208130b0d1104061b061b030902130e0322081603030e09013b040309060801 66
    0x2840c00303a120f01801003c286628a140030382011480182e1171040301c50059441e8000103101c0f0314100d040e500c907000000c6900d444042030140c80040140701009101d924a1030b90391101d45079000f0500c4031000d81c080b074095080104841100c4881091008410321400d0801ca4a500c9561411119109601d003c4050005500a0041300403513040c0c0d1721403807011454000360480e1403003000382c00c940404e0200011508a180c01102c0c0001d8108549c3d030070f440b644a00341030070841d010040098002d00051000704030b050b5000710000301400f0503844e0303581d001c080c5180c4140030703003940d0701c140f02203d8080a070000c0c0c0a6140c1c0c014400035008441078082110344c101090208c3c0d50000907030000e500b0821501074052a840008409140c280e0070301e40c500380d0b03108040c0303052200c840c00c80c84421103101030410030706038401646035011500b02c2c4d4044a65142404d4810f225101545030b03c0c40c440a0300c0c14004220300c04800d540408401c03240542d03549090b2400406520071802502c1c042a0140c001080700340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 975418462 1250 975417212 975417221
    0x1021c140f04020307050103020a050f0301061106010e190c050c07030302163005210a1706091906081b150c0c0d0c0314010603050d0201111e090a080c030106050103 72
    0x740c000d80a00031790341c00c100c01100a0b602812038035003800410010103900401003030046000300026620158248000d94101c1d0401a045c0c0c410400344010b4000c1c0800034240134201c0f41404c0700075400088284414005503114020074401600e280240792000003815004502d418225170f00f0648804034548910141c86001d060b102000ca0300d08036406014454000c141800705002d02400880d8040c1074204810048048881c1034201c1d00e440c0411308445807500001204420500c100100005240400c003188600100803e6002ca501e000e41d5045001c1c00580d1044011b81a17203401eaa0000c001501221070000b00350203050b02412110410481d241c5000c000d0f9401d0300a14000380010089060802090f01500ac00684581d2841e510010003d00c8010024444d45501c00004c1011442d60905d81c6c00c1a50b070391407600643e4108214070907090414011280502800f003480c02c07004010880741c0c0014000c0b4003c1c0e90708441c5508001c42c2d5028001424028141e04030002d019580e00c0e82c0046081c6c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 975419712 1250 975418462 975418471
    0x100605060c0c09070302090a0305150708070c030c170f041502060c030103111801170d081e040510050907080105060a0506030a0b011e050703020c03030906041701021c140f 75
    0x90300404442d5800d40b600060042d040980752a01600740401d0100080710a901940300b201c891317111541410808120320702c0158850340f607040c0f4594074506450003802c10000c2c0d1000804000408180c8402c0020080b1441c502060007030100e5207516409841c1c201541c05806045c203100b00680216522034400500148070b003811008003801c1da440c2d0b542e05100c12000029641e801a40c0300e05c072100525040c0611402409004103d509445200c0452824002d01107504000c00c20742404004007031b0701980091310b02103814042ca4000740e07a41d0070600d0070105240c2990600500b01005c2c0700600300d001a07428290b8205100070440b0b03889407030411070540a60f101d4103030800d5003400007030401d8010b41c0c85114603c4060503c40c3c200016589a5546a1908148000403030b2001c40c03901700381541003041c225080c2c030983c001e515204e520070014486000301d2113070708403c210100c1c45146030170007901622800b43d080c04c103083c1c3c80c9010104540182600800718110303206180000341000044180c0140207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 975420962 1250 975419712 975419737
    0x6320405060309120a1d0a081c0201151409010e060306070507030318060f060609050607020409050f032a0607140306011b1103010c0c0803010e1503030c10060506 71
    0x105031034082440201e030001000825a802115441e101d1214018000c1035206441c0d17580c403983d00f140f07204600c1c41010036080d00703004036a246410702850400050358030910212034a012001d03c004d8404901400e0310401014082c0d407403140c006400000000000038966048425035180c1e030320365484000a0500303c402d640e140c0e11941c0810440d5000d80001e081050080c60046003008062030113124010100c0011103804d6501c20307054110a0640c46000c1c060700c45446c05003003403490301b00005d000d4021181c000e40700b10341e180c2108040001c1040482101e418160942e0386904959a050606c2c4146d000c044042002252418046c03510104d501c61080700c2c41d450780c0c20f50340038800030120950801026241803045441001580c5181900c3c0800c0144c0300d16100b14007844010241401c0d565a02c0404041c01011640e40d00010504002e69055464042d07487d48180d0742c0184620003410101c1e00581c1501002901070102c44012600419080b2281000d01c40ba642d50410300c080c81c070900110b90030303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 975422212 1250 975420962 975420967
    0x606061e02071208040b12061c05060a020906040f0b0d060909050a1b090207080d0c02210c1207060f0e120d02090607050106060203030712021911160632 67
    0x2d200e03d04a4615001400b03400d032913013003a484000c40c4016522203e80000540b50030020801c251801842010640300440745035011007c460351101d556440103011200344a80205100f00c1649480007501c0080902805d892038240d940c559480c03c030b0b4029042220301d2810441c0214024840b4010707c5009030380000100090b003102e85a40031611a032038640c0452070040540011517010358005011094002c440d001e998640201040c012038141781c0e86002590401c401002c0442e0f680302c180c0e039070f0095003800f050350350784000851030078071209a000e201c1c500004141c1009020403503020461555030904200107403885600076036601e821041d2580d045d401c041083e80362101c6503402074680420064882401c0203082d64442d82520320b26080b10006030700200c10072500d01e0f4041080309039030314503402c1140380c9141c50100c43c906400c81048901404640e56200c4840307582003200816101d514126455442c0d125030340101000040304d0041410684501420319500c1c000010007820759103864042d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 975423462 1250 975422212 975422219
    0x302060409150e101d0f16170c030402040c0212030601110703021f140a02030405010e0310050c04080706080c0414061c06060f02160504020906090d0606061e0207 71
    0x1000342c0b02428002a10658401d03000a2001081801c2da000e4031001000076071050805007100440d00c10012280100000942070042c40b0580d007041580004528285107402180c245050301c00c1303211428082d002546140c100026444c050300514061340c400ca50610501c070b0900e20490340c59a4000702ca444100040002c501c1541c0030342d046282322903c050668080a6032034000400031302e17071644a061620600000c401d45030b82d024801d40300054201109908010910400030368a00030340c0120b038148150920199480d075810801d0401030001000f040c001c43c80d01c1080c0e040c05070054883d04080b03114120b00814103900030181c0c140f08a400010503402c00d45440c048800e00314801d8040c1343c000d00b00300000b40c144640c0002c94030417184039110218005242c00701c028622580d19100030308642011144000401c80b1031005011290200c40160f2140d1410703000414a10900c0300940d0300c207180c4100c5070204810398010008480c6035407103000030040554154503580d40d42890000058110840c1030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 975424712 1250 975423462 975423479
    0x14010207171c2d0b01081605040b03103203010b0d0b06040207150c0e010c02010c030f021e010902031002210a020f0301031406010b0c1216020a151101020403020604 72
    0x482004840d490143e070703140812410540c540c20184800d07070308540390503816426581005900e070b0403030219540ba03400e480351004010203900036401414030701d49000020030070024503c01220301920340750007152002e002c1a0200888500640c85805c224114602d203407a15203811702c203030350b00305a01078a15540113030241d54049038817900a00300f9a100f40c2c01c1c828000400c1c401c00410365a100d07030744070000d6110700c10480640101e51000146042107141c00d400782c0183d901c0020000d055600d42410b480c5114441800d90034002c003040000304180e84000c40092000d415088208070700c0c001e90039581e020390b000c0810400da104810106007101503140d40c14540050b945d0321140e2207681c0750001030030309000030030300d101350361003a4000d40c0e0161301c10303109102c030385000e008160040440501d080d10702030481c00b0583d2116405010441c00d02400303c0c3c406d0011400d8035035017151990090540a46949560144100020741d040d0341c800111400c941100c90003051085074142c90300100440d0420b440d01044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 975425962 1250 975424712 975424721
    0x80d030207140d09031a060616171623120705070b030c030f070c02011b1401090803160906090e1e0f0910060f051c14010207171c 57
    0x22154055000356181140c40244803c0c0900d9916075502000c507440c50609450031045074000c00c032032200c030500b4041180e035940304a500c9003028000060310030010341000b00c0171341c00c04040c04070072410000f03504000f14480c0c0c0c52442641e101e109805490408080032000151580703111400581c07003441d904d0b2035440c041c0301805001c1e11410465540700d4440c0c0c40d00c1c40310b0b00107035108441c02c2004400c1c00300c9103902200143d44214036203461311100c036054000030030382001120b074604040c1c184c0d802c3c941800600d620402030b000a0500a01030305180c1d15007000c0380d500803110b101400048403d01074040784100100d2045034400e40d140c0b0051800c1100035011010080c002c451790f4000e00d0b0b12070b6154481c1d8012288200804c0320301801d2403070311150041c2408104071012038014504007060040c010001100b1040c0da00980740c41d4500b41352141c6008106000050150103c80060390400c4000415001892414802c83c0c145da400c2418100c000d041b030080f2400b070805285029601210342e0041d920 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 975427212 1250 975425962 975425977
    0xf071202181b0c03092b060f0e1906060f03030203030a0c1b1109070c02030a0602370f0c050d0e0301060902130e010b0405091b1b03031f080d0302 64
    0x421081e401c1c280c06806109620215011841c2d800103d1000c120745442906030b540030342d054001204c8106d9030b00c0f0210990740200002031107a0345c0da4010b001581b2641d17020000d4034043d1411900300d1402e1070845076400c40d00100445040f820b003040407600f42e00140c0c000c0c08495141c1c00540c2140c807401c40c10300241c4072600c100010045103560200c0540c042e504042caa450007006800c01d81014038007484500540100041c060052980034000140c23030000d20a5041500602c005840d002c000d020780031402c090400c0300b5000a2850030060440750010301c0004a9074240c4c846080c650b0600078243e8603480c101d100540590000400382d80e68a0240b040194182001000010b009844044020880c0c000000c50000000ca0f0141486628108107890303014280b900030302da04051030300c00059000070000305000c3c0d00b245080c840d01200c1c401c84040d0b84101b01c0e109810060791382c0c104180c036520b4000703c4c1c4401c1062103441030208548840e001110036280802c0c00740a907a0100300c1e0179400b035404a075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 975428462 1250 975427212 975427231
    0x31b1606020c0c1c1202030c0a0602070c0e180607140733020d0b0a080304032d030c1a06150f04152609030715090b01080f07120218 58
    0x1d034403c581d442511449101412070402c00b007100301800c0c44d0803240da4680b0040250340c810403007803851840008045034020351000d00503035250568a0800c0c0d0030b034066406012450301450a01907000007240340c0d400354009807400c8514544e500041203407917203c80c0f28900480601000050042240c0415070004140e042d055085408208150049101031020801c075240b0f601144400180704540682d04101604682c244075036030178050794a0302d0f4450351000504101d403540703100d6404885c101c1c500d202c61400454403010041075090241c00700607240400ca0b0f468400402201d407045601c40d000303004800290004422600d0100509910f80c4061143d0072600010b002c0001d600b1100c2401000801855403082501e03940b82825100340300700041074104900082e0204220008004103071400030360401c21943c00d402100c000f010081402101c054a03841c200000400c10030800110880e1000d00304040307442d80c541c1c8891410340c0e01020350000b5400b40030030066080072100e5a1440382c0014401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 975429712 1250 975428462 975428473
    0x1103121b19050301080f071a130b04030c03122118050a1b121205030606040e0a0c0e060702010903080c0f1b01020601060912020d03051e031b1606020c 66
    0x2911101e0001c25006000003500000103202c1034100340320000002c4002c4004000e1203041007102aa4155000083c40e18a14007240c20382056585107024130042004009186c0e503962070307007001e6010303075040e001c26a081c066580001e071325148900b21a0080742c1c111740c5d046000b6030740945008064030204184090351900c8401501c0811014407a60410904c9803803807808160101d4a01800e031040c980c400c80c0385801600d8000045a50b0030141000130516191565903a52510300046d9940500d8000c80c0c008610381041100080082e4403085074248661144084803010000704941c5100e1000000c0c000754910404000140014010301000b030346000c01d40e401c1e082001941c61920b03403100c00c1c4403845910440d030152039503014040340d07015003424a49100540d09056411607001c00c444002170042c004039105130180f41c81401a1148030341e000c000614a8500a40daa2440340c20503204880410107521085010768640c601b2152082c1588090002e520400d88034000290810825182c81c0c4c00341c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 975430962 1250 975429712 975429727
    0x40501050d0f4a0d1b060c08062407020405060a09020a02031c060e0f0403091e06031508060708150612190b010909090614090109031103121b 62
    0x80050251016003040e502c0911400328034002004400011580c42402600318404610700f103010442d051100700c2401c00c04841700740d003060a17203003e0082c000078114034074041c0c0e12040300e40e100d02058020801141d0320a074045010540940034402c1c1811103454080030000e003030060920740c0105521280c0141252078950360303440e0860030f90380003011b81ca00513040018492004c092094030907565a03440d01c0c0810145082c64003021000c00040c00d4890780c3c1c1c064038001020140300e4a03500000d881c6c074a1031442c62440300400a5202101409101c0c080b070305120303a40ca0000c80ca075444100f00e031090310041c482e5890340c1c0707000d403140040a06594044601c9400708415038903004000c0c40079442c0c0b0030524002d86880c0200f03039800103c0303141c40f280b500c1c00d01003400102c0e079001019200791518240002101d5505140c402c0052814200400b81c2d84900c03420855400300650000c0741440c002d07110480c0c031b00c1101c7c2110b5141c0c41503074074143c070100d0010045020310b08042c1c05071b1028015140384500d001c08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 975432212 1250 975430962 975430991
    0x10f02061603181a04020a0e060907141605072d0b16061503060e01090c0e130204090b040212030406020727020706052a0304110102011b05031b040501050d0f 69
    0xc21060807044d81508410700c800c50038149140001030030409071246031418540005010301d000907111104010901c0c54440804201e2002c0794039260350000401c0d10204e05141040d15040c5910a041209005c21079010b54032242891240c0200c400385074110308079040044245c1d068002c3c1c02c1c030310300d001102c0d40700342d0020700341d03224084000d05032004070400d003469450a1404c1ea13801c074072244001d03410039030074800040b800c078410000e8400345042a2940e40d1169a2140e10040710324020790b025007080001c1e400e1008604d09a030140d402034130400034050b2641c078041d54a02c02c07403044a0040c1c0c41502e08201211410250915582554180883c1034000c0d904200580e004100d050b6803555450042c00301c207910840d84003954480c24425943c020782c500000601c58040200080c04d01410060b8104050380300b940503c41d0100e00d104044000d040c6110010110340040324a540c58217815990059000820f005541c203c0f401650742d5031511036466003a402606609034042903c603200c124a00304481e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 975433462 1250 975432212 975432233
    0x340e06070b062409040c18090f050601034d0304020306060901030b0408030415050115110712060209040902030f0a120c080910120203150a050a140904080c0604060b010f0206160318 79
    0x7a0070023001c90000390702500182240c0300503040d58107042c036000320340100d038040c2e26101a1140b01600b14440c0c495600c1e94550410764882c000e84080da240300c0d243c00c40c03c1c1445016500440c0203904641082c0e540d03038248245444d0030f00025145480501c0000c00196944006581c050700c9040314805850301c0b103d0034000e03540c0a822000c0c00703107030724001d80a195502510042c040141c403801003040900e8000e110104444e01a0b000e45060b4000070320480036125a0400401c00e54040d0440364170410740b121081c1c075140c40ba03400300d640641080001903624030981074560032580010209240003844e90130031242000100418062280d01c184102840402e40b0240d0310414140304035607201ca180342d08201000c101600b0061086d001140300740321070104c3d14201e40b0340a206070785425894607240ac1c880040c0c0600c04054010b817084000300010810580c216110780034003038076046140d14081b03034180d841d40811a1990440c034220031600c4000c520980061039041140203216070b4051141c0c690300080d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 975434712 1250 975433462 975433469
    0x417030c071d060a0e24030a03081f0609060e01020a0c060e01030c1106040f03090b1317031813060b0708070308340e06070b062409040c18 61
    0x540c2082140b49091070710254810412144240400d042011000c0d40c504054031110380a01042c00b00305210b01c803604183c000020040c100d175a020482c0c42e0050509004070769403141800d518140181d60190300418400355662074448418141c1854400c8511999803001c0d9811072250700c542d00e02085010040001074041c46d5565030b19485c0d0307903001400740e480508440d001c01c01012640340e1884408915290800c1e0310043c00328802e0098102240d003640701d07030401214000c0014000c1180802030410300c0440c2d40000c501600e451074040d49079200e0180750030200078888100d4900c1400e1420000b0f545442d025034100184403a100c0031903d8036134001d404112640540090800240354000e01c1566015803003000b03001c0980b0703411a525464001d5420b01d03180d00191459000752050003a2442801a400074003070310345a00303940c02c2105841d00203890b0540030703101c1020b86490200040310180c0d000b000132441c0ad4a4000ca071420310008011034a0100c040020810410b4124880a24808000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 975435962 1250 975434712 975434729
    0x1f0e0a170a03020c03030c3c030c190f0b180321060909030406030504150908180a0f050d05030426010c0509090a0e070b1308060109110417030c07 64
    0x805040c2c5006803900841e840d00c18842d034001e100554500c44002100368034511070104034024440d40c1411420103c0300c006803a05561034000c030501c1c0390030000000e000301c002d86404546000c4030490780b0354041c0b08184806044040d1403490800400c01caa40481d800400180042240840405040d411a040004407003103c00988a2441041c1c41810355643c008004899401e00b5080400a2603541e10840c03242e41d084c942c843c00020705000e17030103401d001404102001480113912600d842003c9500104030044114100c03440c100003030804020700c00c103992098154411480c02c0800f004040e95820300211401d00c004c01c00800d4500d04480030315a007001c0520184070041d1a6422203096402031100c0500304981440b6050b055662a0030140e0400000d8000203013203003840400310308000007a0032005408000190020850b0305c40d00b0b008013104da01c04c00303036115645c896060702c045e110000fa1402c0a031031700317000502c1f081c0001201024202000c0d811285030070228407216041c82241c0d4000e004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 975437212 1250 975435962 975435973
    0xd1b0906140402090a090614011103031512031e04030b0f010e150604090c110706050306030d03270503041818060c1808010b0f011b1202030903100c0306051f0e0a17 72
    0x55801c10031112024080002541c1945859990de00d803401d540c400c1144560303c0c00343c6000c4494002d204999040320403007118225245d03490b10703588169005100071514a494030000a0b0120301c00c00109041c1d031581600702580c1d44804580d10b5207400f9000446034002c0342040300183c10140c43c81004c031200c002d0b840b24a1011449082c2c1130900205d6801102401820801c01005503004106006404d80500f400503c0705032420050003c0003125480c03803100914403007202e06200d80000a00200d03041e0b8801840d41400307080c5020180c4111070400781000c0384604109001a056411000c1d10080c02e18154407041401c51050300364940b03d030301c43c1070b81d40d540340410002420032030b9032044200000e0820000c8504d1201501d0030500240401801483c02e0840030400c0d030b4424001c485400301f004040b00d142d03400c4000b0343c0009241030b2000201103841d00c0400549420703c6401076081040503c4840510b169800c0256182c00400800c5076002e08105000320310382100071501c20318a01210020903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 975438462 1250 975437212 975437249
    0x908070f05030c031c05070f020603040b0405101401030f03140a030f0510050d0f03110a0302161707090f0908040b090a0f0803090409050c0d1b0906140402090a0906 72
    0x1403e220410003514000c1e007021481c070360080540368072007184441529006a5829180c10310103510100082c0095015000106210501096040103030040c0d0080301900c42e481e00402d0318400b250b10710316010034244079507001003012070040650101118000d00b4505141501811400e2241c1d21000d450404280d4451a01c10844001e1064541c0880b0b0a400230942c0c0c2d091500244074050f511100400c803000718425241014821128201055110b1003118610005460040d45441c0a0500f0849810144400250540341d2a103010301c20360400b80030340201414980d55201414100b180380481c10b4880500d0400910070100900090002044040e200c403030140400000c3d0784aa4416485986203210501c001c200210440b500004102c80014000405141040c2806030300604a5400790303200216034113000c1ea1108200c0c1d00407960305045081034540d420801103890a00903203002030100c21840045090507402400d088100a22040c0d50664034004041510010781080080150090000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 975439712 1250 975438462 975438469
    0xd211b08090706030525110106090f230609040f020d080301080105160516050724020f0607051830100209030a0807080f030f0f0705090f0f010908070f05 67
    0x803000d81844e10303040c04a41480003042a00100781c0840402032807040d10100c491502540381d0f14075075081ca0000380a1285d440d5420001040c1706451044400d04182051440010b40048007441703a4503091400c5468130b41600b40022114001d0085807a102c2c8200d041000da5150460028034501c5280c40980e00c2d810456828256280171b05040c040040d031b5941008038030307004825284004044900030030f892204b42007541c0761025a9006141080d41201521584040c200003c8800c41c6a81c0895040144000480c1c0e5200822910b00d00052000d001307030403003d0030f08407402d8200342c1c000b03200002c200790016044000341e420740742074140400e688600c611703140b50610094004045003c2d045007040c072544d0104c0e440e00c1c01490000d2032005c0008011042111230800e03250103174050140b00391a40360041100300c54590540380a0200102000080c4c0c1140c0314000701e6041c29800b03400a41c5000b148001e1101d54105810102d0610002c80300c08035070080b08100314402065504404034410303180c107051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 975440962 1250 975439712 975439723
    0xb010e0c1201030b160c0b1f1e0609051c11061209100e070620120714010b121009020301021902010b10020601060215040c0e070216080d211b0809 64
    0x7541c0030b01106500000101f002280c1c0a40c0c0400405038410303400708060350015030303150a070300486504000210340084291010011b10300340c4101d5122020595118402c00ca07400e20145426079207101010f03810000904440110380044401406070340c2000c030400000e1501802c22110740080340d01c840d01c070700c00151040c090b645240305904040c2103100c2c01c20308024105c441c02c11042d00e4203d4041c01c003e00740442003000c80f60151210000503201c40c082c0c80c01400842c105c4000c140c140d820070000074030a2a202018036010202d00004200c86601103040402070304501c182642d05541c2444240c042c01171160401340481000d90001845010307400c10002035001d01032445c0210b502030001400070f160009085112a0320250003406107560b00e251440c10b107415900300e18041035410051001c507540000b5415118000d03d1480c109076501c0d040c0d540d40c0c4120070000c1e038000980c0700103016048190111311400a0412a001281c0403008900c0b64410124005d404e1000031600010070004540c00d111 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 975442212 1250 975440962 975441001
    0xf081605010b061e0334090503281104111c02120f100504060315050a0c0e010507020a0e01081f0b03072114010f0e0105040b010e0c1201030b 62
    0x24402d0030b18445040e030b1601301d114241c81c2c2019420010200d00c0c20f1845c0d00b40485100000c00c104003074441240c100640342c29060030810003184c0515070124507440c02285040300700c2c1801c3c0000c2041040744000791080403446e08182d600c041008800b141c140c40d14081c2d0483c60300405482030342c500c00a1003c0500613101e041d0030000c81e1050005d10030f05282a0192600300d8506400f0600c15250001425100426684101d0303000d4917004000082184000350160340c5602071504000540d03509140368142c60303002e080b41b8005a14104c04040070342c0550080e104050018280d84509500c514041d220365002b0b0b00040c000340c1c40300140702040700290341003601d4442103d1045c4006045030000c642c0d940305074001c0c41210040e022219a0f91450303e0000045503070406100800c0480c40450349000b0030112200022940c240040080c00300c04c1405414001c0742e0090512800d03030718144024124a401a1812203034141c2040284c200c003014619890196014001c5040b01d810403071031407103624081d1003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 975443462 1250 975442212 975442219
    0x140c101d12010b1c08031b0c160e07020d090902030a0b030f0a061508100b120a03170c04140607031e0e0109120305030f090708070e0108010c0908190f081605010b 71
    0x141341c500207444d410079250003009100849481e40003510030160303503000d010000341441c4101441065140d64000e100d02c100d907120a40c0a0181c0c5070f801c01281c07200f90007078010000c074042c0c0b0750070400307003007943e008581c41414240c1c0010042240c07000642810040c1e46005003a9011079401c03018410180f1a12a4841c06c212900204130724000703125443d1074945c0842c000460762100d88402588036001d03032010601401c0e040d94001d0071140740140102c1c0800304e03e40a0041014000784030800c440c001c4400782c0300528940110a0641c1c810001c4e41e42c0144412000c01224407545604250b40340c0c0e4814050301d041d2100010603904500041403828035901c1000108007a41c0c4c16808070342c114089070741202c0040d02c10b6040d40c0d00c000c041850080035601030318141c400c8400c002200c07005109914142d544550082c0321000d68080d00b1140e1030040d000d00c4a440d0402c2d9440e2500c0d44050b0224a00d030703032140c00b0940d0055480e4542d4813168014804c40204001c8000c101d00c1001420300c100307904128200c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 975444712 1250 975443462 975443509
    0x41d1b010306080d030e0a0c08031209030a050d0e030903030c1c05090a061d0316261903022a040c1403180a0501090f140c101d12010b 59
    0x1003d650360014455240a1660f01c4140041c14041407100c21141a0844000c4200350f03540c020a40e501d51010580c0000501c440300440e034001e02c04005c80750020030965445040c0b41c022080c1d2030062a000c0140001da210420004826031070503c0600948611907000d004026426412600e02d105084941d01c1000303400c108071a4569100c100500603900302d40342c8a050320380400b80141d00d246020390b24030351501c02d00c0c00004011303024150f01002ea42180010f04100c000c1d161454089440c0e5070340c1040c02c3c1d002242c1c1d51001c0e0075240552a0074501a10444e0708890039008089010216002840410742c4100031002c0141014041c00780c0890b02c5140000300d504c0341c014010303464017010b49500752048101c80ca031200488200880090240c1110082210a61518141283c9030700c0d07100c200c4c0c1903a51034048290103840420b5000c40518080c0c030304520032050780b104039030000e501d41c5552084c0140450414407900c07501264800000b90340000599201c001040001c00a240c1928480100f00c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 975445962 1250 975444712 975444719
    0x2070509160801410109060e0f061e12040c0e070206071202090301020315210d081801090b071202040501050f0d0603152007110d02041d1b010306 64
    0x520301c2c904407100e070b082d060b0141c1c583d802200420980481e21002d20001407000d88054250800c9042c4141c20988440d214140d0780c9000b030310446a4028a591f011007800e901a899040500007400204000480540c2c510100301e10354803150090380c951030344540003504100420414203501030103070840000d50400740c40c0a0360025920741c1d0003080d00040002185407a240145150150780020800030029901c0385000501001d13050040c628481c480d443c1c95926202410114641400f0000003602928100052190940c0d83c400d014022681c1c0358100c407484210480d0a00c1072040c1701d40300341041013180c00c010301d00421210711001c081c0405072040004000d182e0f00310b0202e642d120000d88039691104da0301d00402c0b0061996038006400d1380f218107021031030382000e64007001140e00c04034086812007451337040d0145030f40030310400281030417820142d0412500d000b441c1480303100c0c03004001103903954510529121144003101c010300389600080340c580f950000c201d280300d0b40040c00e180c1040703440c0c074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 975447212 1250 975445962 975445967
    0x14030906070c140304090b03100c05030109050426090906040612020d080d020a020d170402010e122e0506040b09190605061317011103010b1c09030207050916 69
    0x301a0401041c010401003100c01c00012001954400382440c065075242c956030351002e0050311b0180c0c0c001e4400d00912001d46034000301840b27003e1101d600f5550b401d055a003400c1e6008010440604140d0752104a0f400c0c42001307800d5004002c1000c0b103481070168032a0283e109108100001a126610841c10a03170b05008000c0503a5458a0041c1c040780d80c991b1500441c00e290109204481040d00054000100e021003607800145041ca030716000d50f01d62005100080550100400945000340012200002d4100c83d2a20140b24020b41c58080103441407118400e42d07031a603001041c40c00b031800481e00351195842c115a032080b40e5101c40c0603501030102c0b40140000840310440103111095800e140c0000c030b0a41c418940c0400042c04000e817100d90385541441950925a61a104040c03141400702c100036002d4606004248410101d191329a041d0790034a40c401240d908600d10075414840b1170741d051844a40e00d8041c4400c0c95010fa0003412030b8074101030500011803c01011a940c102d003812000700581d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 975448462 1250 975447212 975447223
    0x60b21030d0207080702090906070207091104180b10020607171308071505010e04020901290a0203070c0b0408060702060c090f010e130c02010506030106030c0b09010e09090d140309 79
    0x24010710010b990b56010f00e0407450074080c1400194000d02080d080028250f40012110300840c00c03030b002c99100a54840018040e1202030104403a152000d020401203200d091307084064420b104900401c0407490700c008510b040f90400d0032040142e101034103012200303400c04c008003917007060400844420b140400f0f40f011042e0307100b2401030040c40c002030740d001400b0007240704100c05000c2c0202030026580d2190480200320003030398244e00c01c00480c00001500400c92941c0b650041c2010000b10b2140ba44122002c603039007043c40c0b040107600040003000001180c2d150f911019084040803507845900345000c0d2490f1910081c03140e002d41d88200b040c0010766640d441580c41d0140102c1f080080981c1c1c01c001211038000c3c1c0b820312900640c61500d0203104001e1500011080429540200945c0d605c0004050030b039450362201400340b00c40c2c04418440380b480480180000030060414002101900e00440c80b01034044859686903000b40135406039003a4054100c010308400c2100380c50460822120003074450303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 975449712 1250 975448462 975448477
    0x50c0a0816051204060e15010e04030e060f1201080106050402040f14030313090c0206060102121611120a0507050405010e06060d0b060f0a0305100b0a0f0c0f060b2103 73
    0x8601c066041104034482c108603180e89a42103100da0003410140f07410700107444030803643d60850140c0d8283c1010103502a09490480d40009400021519203071425070710b03c14085400c90304004100035203842c0c920342900821040030700e404401103941c5008103c60840c1d00310f4000512a13401000200401c2083c1c90b40c49041e02c480d0800c0e64100603a68000a113148119088103074201d1150000013807059441c1d000390baa0303442a17000c0d180d0507a40c50f001285c498210070907034501200d0605c0111101100b103d01c80d85030501c80c074070041402111600042c201003c0c149108410761241e07031031b072007009401c0c040d03032005000c240c9060020354103049440d9854400107050a00031000440d50003076190366074010540e052400790040c0d40d01ca00c50900c200040c0d102010300c001007030804001c661002c20120440d0308903040003142c3d50600506040840c1e03040360800c08001006211400b04003c02c0100c0303560707816644551000a081d1000b8024804131008a0b1070303000426021125144139a0b601101311180d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 975450962 1250 975449712 975449731
    0x1302011103192012091905010f030e0703051504120e011d030a0f0813060504051003091b1220011709031e0702041103130201030b010e03030a0e04050c0a08 68
    0x11000d030754030440f00180700c0d1485081c032442021030205051074104003d00074228152203651000d40314505011102e203d070701c1641c1c0040c2021040c2542c091180e4004452030701c42c2400d40c0c08403541c81e283d030b0385000780e503400f10711074800348038140b0080003a0400c0d002800083c83c201001f24803214800684000806800300c00480c2e0001d200c01c610703940074006a5552980002240007409290505043da40c00071503440741c42c42c280304404118907029406540c11180c1c014001088280c200070101c014198885049440c205180030754004031341d01548050262076452500c40200d0124100509207200300c1d08200c0140b00441c0b95180c660360b000c1e802c1c50b4070104200402070583c4074451018a540315903a04607800c4a506421214440c0704c0c1c90061004da40200d030180281406100c0070541440280c507800a202603400202c4010750083d040034a1100381414580c400842080100742145e2004819000051003a58411002d180c24401d140e08055181ca6050405250b040090301968000d00342164 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 975452212 1250 975450962 975450977
    0x3161d0906150309010509101e020d02070f050a061811210111120108030412060c0c14061609050a03060f0222090b06070b040b061503130201110319 65
    0x55074582240c0c01e542c10144910480d03591402c462101d00800080d51380b150940105818190040194004c841240586441c01c0c445d030307082d5128100c002d5001140305a000da0f0240503404c0410603c05066281724040c5014001008491130300c4412150340454501a1000c0311074540e0101d8640700c0c4104a807002680ca5541e0030041c2500b240d07403000d02c4010a07140e507003070081e000700c0007a001d005844540b013990750800d401d1345ca40002a4907070007280a0b481c001f02040f280100450960f8000c2c0c0309081050901c0c2c4000081038130340c10b086402d074112488203030f400f20082c0400c20b2010800e21511080c44c5c64005441802c10001807001c00701c604c03010340840c1e20740b00d05440464160b4110342c03003503c00329070380001c1c8101c1c16107a00350691180716002d1031178544554403525051900490740702d180e002c40303882039994a50b81c0d204904030000d0b10080c2c2004000b1031004003004940b0045000b01d4a01c0b01d80c1c10030070078900c0010002d100d1103150048603002400360011034400401e45c3c1500001a041051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 975453462 1250 975452212 975452221
    0x1b1e0703030921020610300609030e1207050f04150e011502070801110706020d180507080d020a0503160215030421032f070f060203161d09 61
    0x14050b02045501030000c030001c00510031081511a80c0f514100358030340130b403511030756170303039201ca0103100d03240300351800180ca60315400226142039001300744404207200c580900307640503142c000440b4031418003140820000100b6014034a48015181d070212400300080c5041402d1802141400c403040501d980a00c3d100c91001c140301c3c05900c5180090400103c0000d029a0340c0c1d9601c03c85003003000d44a20250250640200c0c20f802c0602541c58595005510076103841c1840d500d042c002d5100100c00242c1940c0c50810302c08650111154405c00380c002c00c024003042d41041401400c09817070318001d074251342c010f161440000d40003100b541c00481401ca460340314424203002291564080e480c0c2030032018000020001002902d8002034010886400c0b400650344500000740c0440c0c100700c201c2083c60b4002030a05488004000002e101d541400340700d1814200705030384a0f030f05100704410858500350017000b04100070324040d20b41d00f9000e01a00d0010322155090550580e03401800300a1400b5201d80400034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 975454712 1250 975453462 975453467
    0x90203060a090510090e0d0305010503070803030c0d1b090f05040204050108010e040f0b31030507170f1803060f0c1606140708071715040b04090503121b1e0703 70
    0x2000148403844041c0406c04e0070f5032405d078a900c170500d58140030074606000800d00d0b0400203180010f480c1242c0055184d51035080714100e43d038200c251681102510703a04401d2001ca0720001142e4186101d032501020707a4100400070146140e0364014034003803441031008010f246c1e4031051080c11181c07980b08800240d201c1d030900f82489918140090072680d0401c052001000f40a8003d1041c00840340190080080c40c01d074002003d02300c6900600021014080e807000f29400f40c2c2941c0c032400904003854a4018000740299064022000000d84070031030b0304036228a07041c01d10010f6480390011100300c019103000c070990107440c018800051250240300f91540100b000036440b01a281d01030240c65440c40c1b0700b0038001040310004591060000d00b00c07807020768031501401c80c0c0740c2c001c83c0280310b00c0c001501e500d401e200c001e100c400c0726139502a032108000000300b20184003e003040b90311130701c08500c036280c085049990746942d00d66151b518002003101040c04003020742072150039002110020b0f0341d945581400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 975455962 1250 975454712 975454741
    0x240c08091c0501140c0a1b08040e0a0c020d080c09040b0a170f0106030807290f0a0b090f011a1204050f1e030306061c05010f0501030b0307141c06050c03010906090203060a0905 77
    0x1800402c00150110315101520310ac54460360031400d0600c542c0d64100012602c131800e1100c2c0c04040b0310f0000200e0206540c09020b00302c9518090000560380070030000203038040d50316078400d1483c840409041550700006000107020680e08100910106186507507150a1b881230306030152804002c4001c03140541480916000c2d200b80e02407403042c40d400d02d460b03500e07200c40050380c2e03100056207070004500721800d1005900b0b100781d00d400764207182d0360f00c1e04e01e00c40103994507243c60f6082460104640284210918809030003940a10000c1070301c3d84030001030074584842e014021481780009142b00789046800811250301c5a01a40c0b070130f803580c1b001c60300d010321031031540d10220a0341c2c01d000001ca401806804a4812100d09a83c188070321400507060584420b00f82c064907108806028820407030381041d0990754820411103500d282e40501c1522000120b500654030300ea86130500000400139105180180009000006811441c5017412000141c2d0180c15100c0c00131050707140c0300010712084070320700c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 975457212 1250 975455962 975456017
    0x82b02100519050121020402030a021b0c0909030705031e07020409110f0402041d040f021c170c03030a0c05040b0c070f240c08091c0501140c0a 63
    0xa0074000740c181100e00811442000c0039001225190200000f2480c134050340700005100c40202141c105403003502440040c2d84028800c0b501540c00300700c0e00d0060400e20481c2607600703108074041e00303030000d00710b0801c035003188050400f081c0703948184407400109070080101c4203c0301800d9501150442032051030f841038020810080c1d403291501c03414009200f40c9001004c26400700b11245200f209441d4100822030080380940d9814160031034020b0704802c240901e540d00240680d405143c4145541c2c00601100c245c85035140c450000c11410000b0002036a00500c0480b04201140f403c041c0d40e2600c003552800b005194455968a40e041c08403e103000328100d601400d0131341c100568400b4a00001969180c0d40d10a00d80620481e1400249a00c5e0032983c400415092000c1000108001d400071210448000740a4590940421025019a503108120322090725010600942000e0a041850031500081c071111486203584040012222451044078200065800c0c20300586480007528180c3d500c5044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 975458462 1250 975457212 975457243
    0xb090405060420090a0b0a020318030303090a020f0d170403030e090f0a0b010c0b010803040f050f09010303050706020c034510050d110408100b060714030913020a09082b02 75
    0x1f589480c011750204c01091045030000313030300e048075449909050762880304840d18492030b00080072600043c6000741c20b1652400005014040d0319103543c44052506107040700002050f0710010f800c108054000c48038812207a82115689020b2034950088003507c60000d128003841542e0f9810010303a0b078000d0091f10542e64009103100340b11760319000700c2c590740c1e80523001c0c0c0000c0032228400018546800c580c1070070b5a480140c5582026441c580e42550329070400d0004842d240d40910140d5041c803c2080131b0b03e07a80c4000c8007008010b41c0b84d100c90081d40e5010000420720004183d154014030f46084c1c0455050081c25280d01da548a003200c4100c0d620301584518000035420440d6070341207a00f00b42d0140080e21200703070544110008449040c811104603079003058100e0004d200c160003080b03c581020940c03d0121041d41d141030009000510b060194005920700c499000c11500c88059000415030007405c00c100080c40001d03e801c04c1402c98a811141d2100081d0719a01030502c2c06100748002d0303c1039200740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 975459712 1250 975458462 975458467
    0xb0c0c1c02030c0c060c030406030506030a0f03020616031b1b1509110105031e06061b07060e03150609180a0b04030315120f031103040b090405060420090a0b 69
    0x104002510b0703030b01c075002c1807040344500b8080d00700c2440c00c442243c020201c404001c501c4d00b0301d0104281d0103004001c08241c0c0c10b004070742c0301c100440c02e880c800b04820381c86940580524a070912800204000c0d165000042601e08410140ca218000101c8600c42c0000d0521002500000ca02c00e070795011103540050461070107800c40105032119422045040748120000e40f103000c0010300440d42c90204960b520091856802203c0c01d0b0003881e14076641010002d40114a03012410301c51030000d04d02541c03141720580c00f030103042281a5100c140c00280d4038045015104203040c448280c4407030100540864031542403200420701c00ea2102c08607007100d035002010342d0610340003030511214100086405030080381c140301303101c19040745115500080e039285450b138840c801e02c640c481c800f01c0701c0ba01500701c0501011203440440072104001410080060007201641c80390040140710130f40d140075207418015405e200044880c2c40314004a032204851008400f0b40300e40481300010001c0707149030f011450030b5400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 975460962 1250 975459712 975459763
    0xf0f0609151e0a0c06091502040611010615050d18140d0f0201060e040b10030c120312050412081509070c12021b040e070e0a14130b0c0c 60
    0x250028005a103051011450b1806140400185030311034000d40300d000455000d550000100d4582c442d080c000d004030341c0209481c00c2100c0302d0040b41e100c3d40010011414480c80054811401d00803140600101041482c8040764000701410500420f040e45038203a44032940042d4081400f290f00d42000d03040003400c1ca49800c003085994642c28016540f00015500b050000341c075500500444003110003401001c0b004d5640c680701c444480b1005070450300304e50b00900c0000b0200b08540701c000080c013100d0040b4a1101ca062030040c000c5a0f4502c0008246800e0000f0400442c22001050041a016042003000c40c0c2c0e40c004006052540c03010615400103164082c418065409086030108520848500b551105400010303030b03903400340c002188440b0030600242e00761401c0c150132000305040410101d501840d2641f410402c0c848044542071400ca949000f00e141c5600080e503002c0d0000301c240019041203206813a20b450008000706580703021240000c060030412400c102c40144409103a0380784500301e98 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 975462212 1250 975460962 975460999
    0x607060204030b01030219030203060c090f130614220c050c01090303060906290a05070209010b0c011407020304150507020316030b06030f0312041e03080907140f0f0609 74
    0x201780000d9004200f41c0c0c08000741a4044010700c4192078006000700319542ea031000015495000031a400d0300440d08c06800e50b030540f55000032143c1361041160120750903080940d401100410401c0f010320416060130216152011440340c00401e1080440105003c003030701c00180c40c64801c00c1055441c2c1d601c0c10400900303150780340d44154150390002c0000d00c00c440c4d0b1044020301c1492004100b03d20400c0c00303091240011040d00c000d00d0400620300346542007500b25000552000e40903480104121400a80d01004460a2280f207050484609542d0064108984001e60300d0003107000b03820858504a07a020345c12070150087c4e8500e194010119100d0b4604510303140a1004030344400c44502c0c14503004682c0340d10340400c1c18100410844000c604000c0d000c1d50020007030342e002d0002d0300c80399501d0622001160103203080b480c0490190300c07041c0041c1804041c1c60301d04280c551086518035261034036903d5545e03445415864840045820380150b5400364009505c2c0d01c0751006a551100049410100d03810f0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 975463462 1250 975462212 975462233
    0x32a06022503030e010f0905060703020f1e1b150a020d12050702030a0c0f02040e030315010801060816030e01050108070302011103030606031303031b0905040509070501120209060706020403 83
    0x1414500c0749038803540d54000c00301070040d40b0300004020445401a200c225442256031aa1452103490001452681c8201280d0198011f210039001a0402e2020411040b030422115240c1099004032040030701c1450350756078454a800281e1070f040b014120307400d211a9100c288801005102c01e91381642c42d0f16040000c0e60721080420b0400214040c0080c00c40440741511a491013141c0c1500a07510342a203034034044542d0307800b00401300c56240781c1090150160b180c41c42241490742c11040115941d0402d110050300031680c03060000d04120b05c00006000240d071241049400401741d000741c00100748840780c1038010381807450105032a5860301c0000120703100001295400c0703038003e0700c41111041a121010b43c40f48000c5801d55003042e0104040742d1060000b10180b4140343c0a07185c00125000d0b011441070318032040340b003002c0c000343c1c1626061015140510419400903941c0c4014440c035032925001915903840c440001000d40d6021846404a13210700341220307656030f4003100840da10750700d9140404420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 975464712 1250 975463462 975463483
    0x4030803093307080c1b120301120209100311060d020c0607120f0b060301150c050d0e090610020d0e0d0c15020d05030103170d0207060504050a0204050718032a0602 72
    0x1d000c050302190800c0e000c4c5a8641c0a01000d040d070614120200c00c440003000c0925040c01c07450f208520049100503080405035000c0d000303545103038606141c103004018802c14041d00543c40703d001c8840800000703d006030810100542550869290400320300d40100a000746c080c0043c00d4001c5004001100c0c2e07100101e0036141c0c1d413090040020150700785d80801200c2000e090b264100c50104014041d43c01d00c00305450001581745064a0900c40b103985260800e800d8000c2c82e0082600080c001c41079252840060f03a0280c070035240e60301e0403045548000d50b202c0d01d442e401000d01c01c04140503140c80d00c402502c0710030aa0050100c40c1050b40d240a142026104500088011300418038081f00984c42202164103da41014041e0b5107070000140845190303002c1d400e00c0c8281d03035003080050002081805030364420360049000c0d000001d0107006000995000904020800403074840e8043d0b2403d50740b1600d0143c9400501500e1900250500550380400101200001003401000051410350008411011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 975465962 1250 975464712 975464803
    0xa052205060403030e0a05120f1e0703030c031a01120e01060b0309070f0b070611040e13050601050f15030606040e04081b120a230a0908150c0403080309 67
    0x1003120341780d2425165084041c00500320b801ca00015008507140c0b80c0501f81c16404103628906e0400c040c0a50214029414001940c0c904c004c1615414143c240c841c90403580668141402000203544254421400030500302d07040c404611030100140c41c2d158030044080c0030445c000c0141c04d454074810003442c2c004071901e10b4a0301c030311840441e1400c0b451040c0000c9600300750001e401c00740c0c0d941c2d4060140888010310000500d09010020703c8000206105004070078400d0140007201c04e90410900381001604900e010f2070075119a44d1040d210b282c2140d41412500d005181c594071348600003107580c401e99001049601040043c0001e0003003420040104c41500489000c0850f110203e0580300e6042c3d8260700c0750f5890070311002900c10f00811101c802e52021901e0100c801410440310001034210041d80070020324035400900803a40100700381f50380100c625034540001c0c41d1000f0340055610031400001c250503800f1004c5042c040d030400c80c0c07400134a42900c1c14600284021401118107800c518082c06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 975467212 1250 975465962 975465971
    0x60506060a050301030326010b07140616030c090b030a0203010815010302100c0f050d09060f020613020f21010b180402010804110d08040b0316090e0a05220506040303 73
    0x1014900501140c2403001c1c56100d0714290f0f80785803404e61314800c0300302030703103080c0304001e07401780ba52500c8911000c0c06450404046511400142001c0c00a0707410a41c5008243e4080428031902890001c4003c11900151a0104030300c0010042227421940d90740c024034000e1000b00a02c01c109603260081c60590310b1034000c88150780d19034040c0c524286820302c00a0f402c54640c0007100552881040c1d844ca206024954900d01c0c030a440d540c8500c0c020f003e080c88000208031100621240b0741c4420300b1840142240300500990401030411240504000e100034466040840d40900c0d47d107030381040702da60011440f882d0010806081e00140a0601e0300c0101e4480c40ca07450242c99424408041140211b4040e0358034401c80d900c80d03417a103961b0030840c0c2e18550312407141c0828200058076140200083c0c24104181900c9050058190310601c1c001c5001d00d00780080c0601c1404441c03141200564000c50400740480c160311400c0c00d141100240401c1d41520740000d500e44401e010000420300d000e6840f0355802c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 975468462 1250 975467212 975467221
    0x50601030e06041707061b031409070b0d150f060309020301052d07021e010204050405010e01230a0504060b030613020f0409051f0609060f1e05071115070605 69
    0x589400c002c0b00d00800001310740742000010103030000a00f43c03052280d400090705408003120700780030000314204200000d031581c50001c841c2c81c492044640012039800104100341c2440c1e41c00b10280aa40c1701da0130015641d10101a10408800d5031a0050000d11b540055040d01c500000b005000c13184d405a00940c01c00000c501454800007403141000d00c65404c1c00c0d410000e108540d8000c01025001c0300440c070174544c02940c8107920030403202600c80d02d0000181c1d5185031605010640e1016840703d1091828040104814011036283d203001000300e2115801c502c0614000904800301a000160460724201003ca16480c0e103000440c096030040f6203810064002d01c010030309078070076050f0000740c035181030108012051080d0800c981003000f0844080c8002484140541708900715848440004e44500082280c039030400300c2c8206003400383c034210b41c40d0760700d49401004090700a030f076a000308000004c4070b405115060804803100500140700741a010307a900080801c60b00100d00030390305c280c41c040115 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 975469712 1250 975468462 975468491
    0x90303170c03013c0306050a0203060904080307030908030103081b0a0809040c050714060f0a15031e0f060506100c12081b0c01020406120b0d0b0601170a05060103 71
    0xa00c6200301c20100c52850303080000c1c0134600640107805031003604080f0045942060f401d0241105840744100f02c5822902e54200942030751005015050220700c1041804070640755071039507075801508415016030300e407207410044000b000c8061028010403804000841049440703401400c01c4012a0b0451402e0508c0d0986261555242c0d20001c20403001040009064205500909800d40c1d050034141e0030071070f16403180a03c014041040c462290050f03410400022703d4000303601e40100c0f910000700b001816240a94101d409540805450240030030480e014030814110400301f01c0d0741c0b1100360810f130a080d103811406400305035440d40c810041d120b0041c0c1c0040c440c11503030a4003604001214021010345000b924100da01078030b0011a2080b49111582040000b8028490014400e0006036954a080c400800b00310200c904814110304201001030035a580b1941181c0301a0481e02d181990b884610050301c42201e96411880d955140400308105c15100340e02a43c4640e1081c3c80c14001c1c0141c0c1041c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 975470962 1250 975469712 975469757
    0x1e09040f051009150909050a02041803120f0e0f06071e120e0307120e090f190506030c03012f0708161106040e070e0a06020709110d0c090303 62
    0x1003141c512180c0208119941d11a0401e0b0356944040c40d010621320b465001000566810040035216544040c1d882c1c0214146485001c60031624402c0900d403014180e5002010010140d08403c00e140e11890682c205405070350194003036080b800100c0d485200c18070640703515004102c81040210700e80e090000e007082500950b80810034501c1d034070748010300c1c0900300d080e00602582140583c248402c2c01000e000410b00c007101074001d1100d4441c00580168842000b8912800070000a0001031000502004400091156000400182c4007103070039550034000c81d1902000c1d003001c540c190700340740708a409440c031420480180348039100400c10b00d0300100c079a030300c46101c0c8000043c05520204129415080c101c030300740100380d10490100400c04a5000000c0c0303150010b4028041c04000e19050004041e00810301202e011000d0320303152203103854600b0283d200c0003a8817421880310b407540b60402c500c160340c1d000ca40004054020402441075082e00040803084140821000b0465600382401030210034a00f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 975472212 1250 975470962 975470971
    0x2d0738030415060b09030d050717130e07030c0c02011d0913050c040c050a0c0515070816020a0528020904060b1824041e0510050a0e040305030402061e09040f05 70
    0x5014070095040110b909501c05a0147da60595548018020340d003107170028101c00445a01d881c800c1404c140d0cc2c074114000c060440b50916280c00512803680380c0212076904160b4090070800008040b00b1405140001c043e68201d80c01000030080103109120700c40c10110050240f01298000e0000ca41070204440c2500304076004280c0074084903203010300c2911070f005c2280c810400e0303030b8048811441d0f2000070b0f00b043d507403600410042c1040151300755201000f4240c1100310b2000b0b114015251316481d0321a0098800090480300592005410708250340c118031506602402c0c000c9540f5003400c0610003400700700c024a00c50420041c528003152119022240141105809018180054425204480e840c500c0c85030304262194104003400e030700ca00000c03040d50810070f00450280382840560720001321b42c0d00194890b9003148014403511001d151043d0f030203903260420903a80c0d02c1d44d00001d40107004d4500c80c036510030b40c0b251000200d80505406807408100c1034038240062032a00c20000e064442c1140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 975473462 1250 975472212 975472219
    0x31902012304080c0109080315030a02010f08070309021807030b0627010309200a0503070806010504020d060e0901060315020307020c01030504060b032d0738030415060b09 75
    0x1071018481d400c80310065500680b040d241945042c02001d580790a45901040035620200f004c03081012215240f50641c007882421409050310450541c0003810320400a0605820003007140000f486240c06940b0445505030020b20b84c2c10000040c1c040a021641e04a80500009041000c92452403d0060540b80a0941409850205c4000007000c0d201e03c082640918101500c4d203a2240c08112900034402c400000890031a10544814003480850020366000900076400650308003d54cd201040aa0550b08100c03800340e52901c0400101001c0c1c040ca80090b5410840e003010300060680543c0542e00b01c0707201da000d107640280304400c3e20301240000c583c4100583c026904481d103d41c4642e005940c071601c81d85c0000750940b04640807919046030b51803881c1d038030550080c0d076014a0941d08680d410070304542c0001c20780c0900b496a26650440820440703003480c076542c200b0301040721030421080141c0f541c0b82e201c0c2d512031030181498507070401c5000d00444614a071801c04908015502d0890b0032081001c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 975474712 1250 975473462 975473501
    0x70c0603090c030615230108070e0303040302040504081e0a0f02070e04020103180503030a0e06060306250c080a05180904030912051006060806011d010e09042303190201 74
    0x60301d4040240ca0401c1c400c04500700580d05c0412681110020a0f40e40051944010b03403000d5442c00141500341c02429020070300c010910f0340d00c2d159a00008032002d0300e5050703d020400340c88502d0041c21500a0b0388104088110600c0c210440035a0310001d40190201c0340e40c0c584042540740300c00ea84401460158406000c542c0000034003550003038008500d8414920079221601101e900c0e5641076403c260b070212069600c600405030303410820410141c1110045014182d14240702c55490745856030004902001c00b400d0b80824003490055401602540d00300500d41c0e07507040403010060060f40040002e010039a41c040c0c169200341058002079100f01d0b8151150000710782014442140d0380c100103030450f128410400521520755050192000914440e200c41a032402c0450024002400c038460407100404208940b05403681e000c0d034403000040065a04004548460404103030706001000841e007091048407984120700070000040c80c0346842006803070124520400d0880c00c5c0c610040e00c18604140d41c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 975475962 1250 975474712 975474719
    0x30818120a02030d060305164707051f1a0603061912021c120507230f06071b12021c030218090c030f091f02070c0603090c 54
    0x2080d00070511a00d01d40112402c000d9446070440544a454008840d0b50700608000490116018001000361681e40b06422140d2840c82044200c4101c00300c04048094100303944000381d840f1240c0b404050ba000f481d6142c0d45816a00b0250359600c4058841c40004400c6402c0703401024051150003c00581d801d55006552819010040e0320782015180e81d034000080080c01058620303000034000140001300c1c00c0002d000d0680100030500c000c90708130032107100c0d103420090006002c81c01c0c50a5070226a080107516480305041401c0203002000c001e1035012102140681c0301c0000091b203440100c100000c40302e6a41e1102805c9078a03011001d032001c42401544020000200380441f540f60000c50340c4116240003951072100302a507283e554404c00401d500040e00e48040e082c0c000500c041071400e071207031409801c040580c5231803440000c041420b07a206840114a905000340617070b094409040c54005802410415040020752180c20202c401d08900e004c002900350183c0100c01c86250849201c101d1a0316 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 975477212 1250 975475962 975475993
    0x260303060904020109091d0f03130b0304060f06030609140d0e1201020c0304241d04050a0b041109041b020c0d050304180905010f0504200102030403060216030818 71
    0x7005031040341841404a0040340001e0b0521171071402c44d03543d581c813611800400660a040110080c412001504204010b8240b2001c64100108942140042ea0759a6565043c080002d00f01c1000710102c55040c00400400c1c80f04e079401ca100c5140c080c80702c658282d24010740899030750f41c4801003200850808a0f10801c81d15000f04070310380a9036441d00152034828240b5032786056a000c0d400080305c00c078031b6224424005d01d4080700c88108000c241040181743c1707240508410180b05148000d449951030f0380026515001036041500b0541c0064010310903142d072a0744070945900322150480c042e40c5025042aa083c610700001a040c0e01950094201c01d5508000d201011841440641e80b5103c02c0000040010405081107001154100e000541d4040c0d8a451403d5405170031070050010300b4a000d100101d4a40c4c510786942a0b0344910900b01c041204005034118012540060301c8135101051840e000c820164440300e400d8842e42d03800410b0b90341c450402d2240e000c42d00b4a014180d00102c2c00829481 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 975478462 1250 975477212 975477229
    0x912070f03120623032b080703022a0c03150a0e01110403060209191512020a020714010323010e0115020a020f1804140d091202060a090b120126030306 66
    0x11005c0c0964060b4005000b281d0300484900a000b440154091141118242c3c0041800e81010f020714042d840c0c411121110082001c0c004220449d10f01c5c05003001c0100c00003000301e51501c00000c2d040e00c6c15240c031411640814001140c0f003110700750030700400d200290010f12500d00d101081c0b030200c5080c43d00350f441d554025045a40c4040e0001c1c04440300f00306136011031030500003c0018009284005180c8038005100c0b40e1500301241d6194010703c00d00b03100700c0d000301d007840540305000113301d10350318281c004074041d1007055551040004e9143c803102c4500708040c1d480b8103072001d41c1c4030300d034669903a0004180100800c030041700058101c015124018503181d280c1410702c4000424030015410302117a02000310714282d4007200c06041d000c2011f81c030308400b030180724078035500c13030610f0042c40303103060044a0b410103007506c000d203e0400044e10060082c001c0c1e41c2c01014020390b2030390030389035848944d8840180c1c000b0700511000d880d04110400da0426020f50407905000480069415500c0b040d0a008408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 975479712 1250 975478462 975478529
    0x10f320111030d021e210c04090e0a05011401080d1d09090a140607020709020309070801060f080705030102041809060605100210060509040b040b0912070f031206 71
    0x441128401404a07000304041e007108103600b00700591341c01124180013484202c454403e41100f00a105405003103100d41c0003071100080c9800d60381c1d101c1c0c0c2c842170035890912568101175100c62a00d0480700408000041c40114640305a000b080301840240c1000382e130a40911601009a01100302c1c1042030f40b0450901501c1d40e1120310942c07295411800203288144101c840d004164032606c141014071040d17551103a90040018054403180c1003400d8000c5d00d404860185402e95500000410080310041158500800c26400204450b9440d2200c0307092142041c03003041ca943c805d078840811a442c043c401c0b581240e02100701c000c102d1840c00c170190701400c100c410940700c00d55903520001d002e46856140384400c0c0500c1c0e014000140e03941840e0b04c115101d540103a40500d254504000001700709a0740d041d0410b81000c0c50040c035039501d4582e00d10303202440b20f0382c003c01440070500c081080000204002403038441e46800c10360b80c0b6130014000803180c42b80300e0080c0400c04001240e030710492044d08d04004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 975480962 1250 975479712 975479717
    0x90132030105042904030801060c021311070212030306060301030f0f061e060b0306100507050708030406051b0c0f06160209010b040e090d0c1101090e0a05010f3201 72
    0x1160204002401c4600c00c42d0300303a0b6030b0040001408008820400c00c1010182103d112040f68100740c3c500a1040318140940305c1401b80c01050b100035551411280038140d10301c40f80034014080d174592100b0103600034140c200c0c01400c06010382c112144012095a01c25800600011304503840e40e1190145181003910940d18a5200d50700c180c0842c450380641c544036180049000283e64690b1400703022181d0550002e11080020300c20701002c1d6603506210640c40c1d49a141064591134141003160400721554440e100500c80041c0025803550848043c0801c1306854440340048250450b2907516500e180c20700580c044050400102280b40c41400340022504002c070100851043e5400318180140a802c180d8441c0000b0404110044a240d0307980e604c5586000078080c40285180064114040030f0f000800ca05a48a0284466481541d16030300420720002d001206042001c20840180f90a01030301010541149001c01c152035030142c01c1c00005601e6075008002408074401030040315441c07019604 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 975482212 1250 975480962 975481049
    0x20a030c08070f0605270309010909050c04050a0314060a1a010f050c0109081903021336020705120405032e110c0d2c030f071707050901 60
    0x407949505c941e500c910500c01752224000d09000324490a880003102c4400c17161300400c016030060343d00045010840d06122804501c54554100b680c000e07000d11b400030b1741c100861100010a00500608080c00650000281c40d0b40d03880d043c21980649070b0107400c124801400c005400040c2d40300c1c40154405100e1440c280f410840381820403420345080b03103005e0750201c0d00803d10107840b0125152210340c84030541400c41c0351015084240200c010540b08591103490b030300b58454062240c90122517040700c041c2c01082a40700d003418440c1e00a400448013a42c161150703100c09440e400f0b9407012681030f00d000400500c9030b2400744481d0780031151410303d507501c014001b80c0d00d0300140380c480c003806c0d128441801d10541c07a034480306800d900e0152034905e42420402080c6a00c1c0308442e8811202e40e200e0740180710042c401107204003003480d21040456819003481403860029140b04144032008000e4804010780e035109507110104800d0300d00170300408600740604c00b400328405503014446404c8507000404000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 975483462 1250 975482212 975482243
    0x6040c0e2116170c09040210020a050d080109390c080a210605100509030a140d200d1107090204060905010806060a0e22020c010b01020d020a030c0807 66
    0x2030806609414040d200303402c0740000d1000842a10010702c00c2018800140b840b960401c000840d0390720060f0002e40940c41d442c000489151080c00841801904101211118500f61100800d040000d101d0621542d244c60320007000041521140380c9545030542c0c0c90307a90007a040c2d481c0c2d504000464010414050000a09000a212040580854080d80d1143c08401c040c030501220030307813a1100f110781c4043c80d03d5814002030f6107042c545000c0414030718005032500b403141e0100b440c0c443d00c4c1d40054822141d401d01d8841314040000d21524080d070316a15030200e0611041c0c1381c12001820314104225400c81c4544448092185031424400c440102c11a100c0c65501c07402c2c50b0803079205400c4031002a06484c0240a5035801c5401c25800c00415100107162101c10303034006101c8107000c43d0252043e141c00c2a003604640d04848415040b11854504555444003040c64074002c041d450300c03403400b60007104041e40c00780e8008502010079540548920b0040c5240350b907001c0b020b501121040b11194401d00050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 975484712 1250 975483462 975483529
    0xc0e180f1807080105190506151615020d20070812040c0308030a090201140403021f03020408030c01091b030b1603090606060c030908060915040c0b03040b01090506040c0e 75
    0x114025202d05103e04c50304c1e072110380386c0415503030000c0c0b03d240203040f06001a1407985503001160071050150312108220302d594584890042c4420300b05822541c00420b480b08251034643c0000a0840300000c018481130340d00d8006885401290400742c0341d8041070000141030552440039590040c403034800c6c0c0c00303003c0c1c0f2583d403500103070401e4455203191a51904c101d011560003500e00310b02412541c0031141803a10f181e00088240059414035260072182d982c0c0c8201d0a806501500d01804a00302030701d4582154103105030003450400e000381e0715134030a102000402e440c954003042c1525001294002d8a03966160038074652071000046200301540c440b60100422014419000581019501d003070be940000c0c1401010140c1540008090350048824019011030005507685695a00c01c44141c29a07264140910301d402355a0103001c06a0002082008002c40e510255041e124545070810460300c4403020b020486281c5a40000072801c2440b0078161340c80c1c251050600100e8800350548030340c0012421 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 975485962 1250 975484712 975484721
    0xd0507080c06101a04030209040f0201032a090506190f0e0a1203110615010c0201050d05040b011701060f0b0706021b0606030f0a170f0c010c0e180f18070801 69
    0x502032038002110b07080c042c4d08446070b80440c0c100180b0041908007421a00029500d0002800c02043c908500c4000021a402504000551130000c044200c1810170280680407132210741c090030300058841c072000714030303031806100380c0c0d104911003c0c000ba80c0000719001900da01e00d1031454030092008034070b503003a0710360741e4070a851001e031290010006090714146409442007894000f41959508148204540090718209000e9200c0382444d00d41b0b4042010f0005030b40302d200d040180202d59050100300824001c02d1075010341201e05210004250003480d02d185400c880d0b4a00070190b9141d007014082241510b00c0d800341c04660b015150061130041c141064555002c004500d107840741e040704c010004107140034080c03102040b02d120060b00842103150b41e5070004602e04141d10711408008180c4083c04445241500c510020f040002c0210001e103c501900810804030020702c200d1a403c414482c0851902a990140b84d0900701001c1d00e40b58599948580c0c842d46e098400c40344520b03400001c40410034000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 975487212 1250 975485962 975485971
    0x6090c0c0715090501170a0b0d06020f0703020706050a080103061d0d030506030105070311070b220c080601061103190e030a0b0a0e03090915180c12010602010507020d0507080c06 78
    0x6800b49a035602c51010305803050035804503042c001c0001c0040c5040340098030450f0b11080106000603443d03a00000100a12000780014001c94800b08000c203d13010341c0740c024130301c41d0b002c0d03002c403040550758150442d618821590520300141181004000090440d0804101c07010f4100f80d8640403110242c0031803401030a000517030f00007911041402005e042c20300c42d1a400c11580e28003070190000c0400500c4062188400c001c1005c0c0302000000d4414086440307002010104a0401d440c802c02030a0295850000c2d0051a030f0030b024500001500e00d000303800329007022103d00040c604007204010b820400c01c02600b619824064096a04591070381c2c2800840380061145a1808641c140002d851040b01e0200c80381d9952580300b00440349003542d442d00d0b00c6074000e41c041d804903821030803030010aa144520101c03000714101d4a02c20b01c07280c0d1400030007800c0510b191110b448943c1c0c0c0d80b04001ca0903500705a480390f000d40c11010044910341d104100500368203000e401d089152644031203806280c242c0444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 975488462 1250 975487212 975487229
    0x3190c0b040615142215080f010b040b10030b130507120501091a091306050109020a0e010c0c0b0d200408070e060f040203090c0414060f031506090c0c07 67
    0x40700c07100f035001444003000e0554191155060039012000c220701d03480c0308508419600300060700005400b0590001e8804000300961001c500713981704602c0e0f40d0340410340e81c0b2404650824852410a003464480d00d0314207503008040c0d00301034090343d9050300200b542c0315071250441000511980e5071720340c500520380508590b41e2030070301c0011803c5030f400440b001038105402e86ca05122804a001d10f80c0c9410b12103820007110399903502d0b140c01c00d0451601c0800b24000b03000d42c0c00e00000041c54505a409051441c0e025195031040c450051300440b24031078402802070540920721411700c100603142c400f0b898030110340c1600044599070512203c040180c4004068000c1c0703400030b4140054101030018074000c0540724284802400c0180000e400c4030200c2c03115034001d50780031000480080c01000349801501c005081040b01c0c100517400305046a00032a100c900a65810000c4040c9040014407011000c40e00c1620075000d48481c001c00c001018003401256068500b4030036211124403d0012000800028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 975489712 1250 975488462 975488471
    0x1b0f031c02092e09082410080d050301050a1410030b030a06090506090f0715030207081b0c09090703150902030c090c04060f09210804260c1203190c0b0406 68
    0x3d10700245082102e81200960307070041000007407108215907030400310000d180b00c48003003969021020710702c0500640c044c0080b0311481c9070103140d8a13000350055042e1001556a440d031035445440881500d80e00d1109250400f141400c0d84500c0c500c241d1000d0300b142d000a05603589603007140c6815042d110b08103410343c1c40750082000e0000c5200c003045100361480e0a50094650b481c50b000048104803030000596027403540000c1d40004101101040f42c1d841d061042e40c005500440e03c2c132840e616100c1c0d003d8140107100348000b1640500000500c00d04803035004d00031401030030312490710380098a002d0740e0480e05403040e00c10b944c006681c1c01001c0380c850078842450940725450050b000f00b1070600860100280288030b0b109011002121010003031550841d840c030a5040060710b4000403500c2181d1003075100342a2a000c80411210203204407002e8449203086441003000305003008507550318501800c0c00b07680704000f1140c0f02903c5200c2110661424285441d82584944511030340c510101c3d030443e41c0d15900c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 975490962 1250 975489712 975489799
    0x10050d0804081b01080703090201020a0b150f0105180d08040b0307050c0c04050f0f042102030405030c040e060f0c0702040204090c0f020708030f0f0f1b0f031c0209 72
    0x3001074204000c800341c0c240d81c0351010040040c02d81701d8080c00040400d920358180e0003d690007040780110b81540b10019091500d00010003840780700a600703141c6e208000e00382c0000c1d070b55842082aa0f843e504c4200204a128295508100c180300012030100c460440030f00000589250b2040038610410b8140c90b0b42d0381d41d16044881034200203e0031900c41c4140c2c41c2009011528400e1002d25500a44641105820f9100c50800c140e011903000d030110009580414010342040e4040050000c0300d1090b0100c812840c0100c00b0407041d1140c1051180d4240d100100194540c404041055000b151107081715203445c0f030340d8021900340c2c2d002d6082800c03c1e54846203982c0d0300c070f5408100126031020501c0500141810220702540f2031082d0003c8201c0000301007214102981028100d5010a000c10031140e42d50408070340c0c41c0a4030b1a01c00307075030b038160003040100d20181c9000303c00c44401c00b82b10416451202000d04020f0020742003a801c660300004543c0c07504502c4410b903205961260307526100000c00440307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 975492212 1250 975490962 975490979
    0xc09090c1d0106050a02011b091502010603080322121809020a090e060303041710050f13080d111b011803020a1e02090c0a030b0609011710050d0804 65
    0x142507010300c080300ca00d4801681c00000c03401d1030700e056030103d140031a038801600c08200e014164008191005500b0fa00c007803c2e9164010f510b1601325061100700d20500500207009130b0889005200103400d00004000160380a850070030700d6948800c138400110051001600d444108400710005900400c254a40b0414907282000e40100201240b070001d525000894200904600eaa885500d084001101c00b00f0303200e0354140280c40141c2060150b0924064a030f2801c0c030b540d071b451650400c078590310f40004518a181c28203591071141600200c0c0c1c1071030441541d08d20032a5031000c00360150055880c11000d82c6004008000d0012410310009a8030b0a07044051440c21a8020342d42e640704800e651107114000381d00031402800ea240c010400e2402044500844108100e8096000b94440610010020102040c0016051100d81d641d0100503a42030744040c0704c07552107001840382c013080c070000d0441844443ca08489600c9006040aa0105030f0f440c004681c0130036540d00700321000c0c0c0c4042800d101108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 975493462 1250 975492212 975492233
    0x150601181503320408041a030103120e1804030203040e090a0302011415151905030907090b090c03090f07180506190510020f0d0e01201e01090c0909 65
    0x8a02c00203c50a02020124800c0940c0154a0700b0840542030000f014005103c0640d801040c1403910301010070011042c81240743c5c0240404c0b1845050300d6081240940300d20000104000c014010700c101321000c40e07a00380d92502c014022000c600c0308020114607500105003042c0220b001b4001802d0345511894040d003540c0010f2407c0103588031103c20041444c105040313642903400286c41440c540d0800c5107010b840d031f10a00c00c0300c0c449030070f44980359002c95601c07900452040b40080e082d5141d0503202c010140945143c4501186d0210410f400f080d003040c3d03044001e50304081e6100441d00124290500340d030420001e6849040510003042000c0800c00e55801000e600010031546c0f901a0030444107000c007903419502031203028000c030000070b503c3d0500811040b01400000d5041b02c070f132403035100e000501c600c0500040354000b41600416000b40e00501809040e0340c03500d080900086002e458180c048118442498002e540d04c8010781d1020501030320f146000382000102c08a0600c1d00e509095035140c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 975494712 1250 975493462 975493481
    0x30c050c01170105060c0708031201030212010b01051b01230a1103011802070305070602030f04061a0d110102150405100506060c10020d06090f0b010201050a0e150601181503 76
    0xc00308890b0035082111102074281501c10407140180c9600c07100a445207400704030380100003035110000f25201204d1030f4840650403a842143d00c25240099508001d00b070700d008152090115006002061051414105880b034140a0000000d010308082617828449410606844990301d04141806038840581c040c0b09685e0312207000640c5035500d031644d030b0075085e407503a9117031038a4560201c1c07100101407060040b28042070b0403500c00d64072410034102041e400c0c00199421200d442c9017090404645135088111004880010051060b0a4140d00c40e0781d41445805101c034118010780c8070480011441c031311034500580c082c2004003000c0c4100584a01110005840e0074842c10050142440d182c2c000108242180320b10b0314003584a40340d0705020005001c0745c0d0400d500351810a0310819464004c0c0d404100c41d03400c244d0017030205484079143ca4040300d411858113001340e080070005448131030840b006a5082441894105000303040750103c03e002e0709064012a03e507003010540f14009550500030308141c2d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 975495962 1250 975494712 975494717
    0x507050d1215051e0a030b010f06030f0c0e21010e030315040b060a12060e01061106060f010e091305010e030d06060f2a02120a151512060f09030c050c01 67
    0x55a080800041d80801070f40d0b00790051502620304101582c40d80300c0200011a803000804c10076584270031b040d16404000c0d000e10800a481c00c01031100c8484076002e40c0041118031345030b0211504c140d906002c002c000c8844003901c88102c4040301c03401e9010034032880c2c1030380b0410409503840b0706200e604840701d000b43e00b1403540b241c0d0070010386084960f1004202e0f0034808041c101280742d0040040c00c2e2010340025031180e07020460034400010540c4e000b005842682e00d025098170401da5404041003042c16000880c5030000e8603200700321079541020b03140103412005a40c1480c41d0f0714001c0c2c1d501825115041400652a003002c40e041c0301e070341124002c40b00501a14100f95400c0ca080810042200191611740000d0319104c4209078074400c3c42c1496068625005014040c40c40002481c2950765400d40c1c50403180800700118440310035074144181c00c10303c0c41040e010402c1c0381c60043c1105a5414495098030b00302e0343c69000071181da00501c2817a030158800e48502c500b810890a141d4140300781080300745d06 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 975497212 1250 975495962 975496001
    0x714041805090708120d0905061302030f1c1206050a0f051002030313030804021801170f0f0c12150a060e060303090f0909030412050f0f07031e02010507050d12 70
    0xd24008200a07000c0175440f15040c0d21460081140c1015045074540500305006400900111403210365072a21010300940441f041448050034203554ac4541000c00e6441c00700e518111004c803032080d06144021070301040f0200d0040c0c5c8940018021078541d0b4007408500d524004100a82c1c01d04041c9075440340d01c140040c1d030642c41c101c07001400300500785400400b0000f030900041c04558403c3c0070403101c400303603001d480c030950785640413007241c5460744c01c840c5040d104091240000300310010f00b0445800341c0c00081c0c110903080d9001c2c810002c1070109641034a000304a0800c07840e0011aa0701780c801d05170480082841460449200000c40e006003c40b402038000b0040b64440b5181c91144080020040d02d00b0b025507a540c96440b820360249401201049100740c0034102072010015a5a8501d86240155409141c00c0198075603108075510000388440403d00b183d40240300c01903041c96501d40103042140ca0722150f43d40f04c2b403d00741c0010394a40414003100411140380034620030419802d400c3d800245 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 975498462 1250 975497212 975497219
    0xa0e01080304090207020d05010c03050919150e0120090118030323091e0a120c0b0919170606060306030307060f02090d050d14031e07140418050907 65
    0x980728030a80c050030f0580e60700007440d1811511b80584030a2415080340c000c00c40600d43c948001d015090075564103501e0300c104e58403410400c00c0301124002c01a4007095803406101074203d81d8000d80912100000695a41c0000c0c150800032409111120701c4030580407030307841e0743e030342c0015081d0291610719402540140005000003604030110041014070b40303e081c1145220000104958854400640e400406000020303103541c0024509140340c1c9004c40310701c024940c55805595030b0201c2205c001d0070300b403900f9000300040b4103400024000b5490280858404000540040f025000c580d03025041504040c10156440c0c441484029003200c800c90b0614590f01f01440004d540e80a40d840c094240e0b40d884c060603103144003680c1101e00c2410044d212400c000e0380e6003051038079240700c4821400403541d4810080c00b5184032800300c1e0f102342c1148000d0103c6010910000e0000e0500806020601074880c13a00d241c9100703008082d00c02001c0f40c907100c095074031b2040d04600c1503500141400e03040350300500e01403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 975499712 1250 975498462 975498479
    0x303182419090c06032a1b0c060507110f01020c12071e151e1b0c09021201060806031005190911190803030106030510091a2b0201050309010f0203010b0304020a0e01 72
    0x1690003030601d14010034800900d0581c42ca507507443c800d0080651036490000274a050300100640500740c01264403440c01c0b6045001d00c2078000d240c1c0400c600580040061020b985048651132100080d484221540ca80c5c0352145645600424480328692120f090010054600a00c842803002c00c030790700d010405210742c3d81100001e0303041c15000805104444640381074603000d42250640c10b40d0041054241c0711350f00d240ca40029400b12414161702800d07030001041d0343e0701901445008510140003803551000402c0b140c40248006408070030140310304405852426124003820901a00882c0540f403518030302410850001a0080300c0788e80c00755a00c4081041d6600481940d0440d85e9904001c240c595923013107114244209500314221607032134801465004100144807c222000607102000007080005024400580c1e489032203007103141f011000e41c01075200b40d006d190483c00c840000b10303e0b490026202000d03a0001d8021709502c44c804020401903103482c1440780d0003002124004645941032003001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 975500962 1250 975499712 975499781
    0x501020c0a091e0906140903130e0a0605030d09051e24070203070902130e06030a0212010216050a02030c01170a110f0c0303182419090c0603 62
    0x44401c1e4550b2040300c40c07a0700340343c40b40c04030b4880414001006004818505480205680c55154598504020014000680000860308140c051101580690f860320304c01400202000749401056a252900010507450400c12200282d07610344503c00f0050a01d03060100c4820708041d4035056912440b01c2c2505516180840a641489500080c6034200200b0a0000f030b846020300094051150040018800665078050070415000107010403a4a0781c4104192003050155000e60f40354200c020003400524003801440070706031701c100001d0300300f004240013168000c0d4942401d6543e500080b5004c02140b0342131041c2c5503141000d08000d00500b40560032150429001409040706607556414107d5641d01c00c0d094952114410030190f80e5446515111900c135002640c425088a40e03030071a12a01d01700c0130036144507e50141d420040c1c0008001040040f142c070281644942e10148000041e004059020300307500c09024031480500140380401c02011687ca81901620203104100845400e000040c1c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 975502212 1250 975500962 975500969
    0x50f09010c320f07050105070c080f03040c03021f12092316140301051503101a030f030703180f120302010e15270607180e0408030609010501020c0a 65
    0x7010440241c1c0510ba8142c000d118408010403401081d04088122800300030142c0f03a2041000340900d0b21640400e460150520380c1c010443c180a003c0c1400511000002c0c592040c000c102d00c11803c3d03034a4003c60048c1411414109958454082c05501036412180300d081c1310f5060b07841005442d450b038454603080d50f01c0e035107846007403803040e40240070140c0200061800c0d203542d1410802c203d542d98142e0b00404103910305550095003003000080b40500005900071030b40f81c000c1c014001c1c8031803815812009145071004d00c0c007200c0081a02d4505da84040007078071a4114058001c59480d4002d041c00b501303400151070302c0c102030881130304240070340315545201104a4aa644c0c0e601980280f03850280d000d800014020a042d200d400244008409001c45803401b5415865500825460100403100921010004114540e0000007c2140144981035141d1481d282000d049545511407824420544040c2e6064640206c040180004c905d07084400300d00401c2c09000511040301c90001084a07400d4030710 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 975503462 1250 975502212 975502247
    0x605030307022b050114160804123906150b0904020906190201051008151f0308030f01062a0f1b06050403061508100b03100f050f09010c 60
    0x80708080350440014141c0c4402d9002d0002d01c00740b2101c40010900303920840322071f01c80c10a03010f004441c00780281d003107500031a0044c02c1741c0031908007204181c614030684094500841107002c41c85010f01c05200c0000c15051903404010b419441e14200a4142c5d02c00d006000800c9040c8101045110354807802c46002c01c00950300941c4840c0c1c02000a142c81c01813503840900d6241c007000940c0055419800507205200004120207a591902c081903950008a010b91207100408000304a220740a000c0905440030520601c40860761030703583e81081a0030070746514411076020001030200e9a040388a048001030444070000c030048101010400c241c00d00301d00503000588800c5400c00748a0510003620b464041a41e02912840e5210002801c036401840292003080c6418510f8201c4803203071410808842e15000140314150048407054024a4070b80b002540c10310900354600300c2503515014003028031140d040c1c00075040ca0211540d5050300001401d45081d41d140c600020103235a04040c0c0f18645c010200b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 975504712 1250 975503462 975503509
    0x7050319030806240705010c020313030609140304030302150726150a1202011d0f010f0519051c0908180f1f09060c03020c01050a0318080904060503030702 68
    0x80c0c3c08a4464002403610040010400d1006500503542c1801040100c3c8100002c020132070360315004070384901403a02032401390520204104046040790700541d0f09203000311854845507040c406024610750150340704402580001c1080261455580e401d940e01100c1c81c18102251003001da070b00100d0300c0000802c0700b5440302c01804905048a81001003400e080e0240652004540f1025130314404400300008070300141c404903002c20b14041d2004000a201006422a03901d00b441030b006449058071010540100a424031000c40c41004000401c0c12800480c0c171681c2e900c00e01e0f800b011125800804520310518240b1615100207242501240c640714258050481e070001c05d400020b0016010005507903222080364040d4800c1684501c00042219154559610540c0e80e9001900e801c900c00c80d0150143e0400c00b055260f03540030340000c0075049114540014007a151a040442c0c03034180e0101a10358100c04100e10000e41042c2c440c910180608800442c14250154009819064000b01201540c11070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 975505962 1250 975504712 975504721
    0xf03070507020d05010e1204050303031513050123040e06010e0703020c060103080306190303050301090207061d0a0510020405090c0703090f031109010f06050a030c2001060305070503190308 83
    0x5035066403060741d80148036681004050420a0203003500170800007250181011200f00e81030944225402c40d807014000e14159510403d50301d4841060b540d41c80c1d048a044043e080680c00303548101c074007030302d84842d0f00d84036141c4604010000410441040d0b009901d008150150030800141690455100044d111225030b28000201c3c040d000b0740c281250b0750321440c0c00120800c003030300028500c00c940a881a440304072400c41c0c100c1440c0000d22000d004610100014070030549107400078a0801d0042c0408203c02d450078001084e81003c28045417081d402007440312040207802c0c0300304455020310b44d00075801c050508001501c1814040d08107103400000052041c109801079038120010001007000c1c2085542e00d0500c1481d1480281e0712a1003410064000f0400c0500e40c1e444c1d0064400d5680c41905140201c80140c0c01480b000380d040f03052010141180c505500040c0303010b108020a100003090b030920b1072804902d44940740e0032880c400d4020050700e03412603608400801a11f03405280881c05900c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 975507212 1250 975505962 975505967
    0xf060d050a0b011d12160e0a1a13050a0b130207030e0a1518090c02032107080106030b181f081908030a0f06150206060901030c0521030706051014060f0307 68
    0x1742c1c059211800110510002402e00402c182540325900d0723682c0a00c40c00b01c503400c60084501e07a884050350f001d03100407100b42a0071041d501c640c3e800354891800003000e0f503075a4009a10200a603c0d000c5065400040c050101b41d40512208110901600d44101e418280b81018905074540701d194001c00c05c0c012102e40c0d035220300c000200020480d0580404c083d040d41e0000075180d40c0300380e80d401e54094210702143ea803000071104643c4690303c00c0c0e40b490340030b90078020200e000c1c00281c00401d9002e10107000e20091540c2c0142c2c01409589a0b2103507200182c69000304040c140303141d0348074a40641142c9a001045007444602d80c10b0268081c802550740e0b0380f6440080b0013000c020300d0001d0310914100c0089005440840d00c000d0b03070940ca03003c40b05113990306000c0210b1444240001441080c01340c900300018107102c2c070280ea40c0000400810b0403910703c1d0b00314034910b400c004d0090700c42e1a02d903420b000e480c00179500c409001e4008417010004580d00c00012420500c185590b00898810003c0000c01451 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 975508462 1250 975507212 975507223
    0x30c05121608150c0f040501110309090c030105120304030203060402010f0203070506100e0132042327061603090b0a41060f060d050a0b011d12 63
    0xa0300200141141902c4000740755603480a8034107020002401c1c4040303282c000400050304e40304d15000540500e01420000110741410456583c66202d200c1401100003aa50f10351016114035814490192070f0340c940820030040d100010004612504104000d00c050307240030440e03075405502824030100040211804074070358494041c01400c6c138007440c0e0038446010004054182200ca44050500050b626180c0c0041d420081022200368034003103088000200b02c5030400c1c0c031b040b254004c10001e10440c51083e54042181070182c0d400c000ca014004111404000c60500c0366580c00e8bd040103052480742a02e41561000b010788210800703c4c506031180002c612940207082c005500c200040d5032401d04411030005003860204030300c101414500811103500b04080050b80340110510000c2181d105000500705000001c0e001070f4102c56862810222501c50340002d041001110a0005003482c1614402c0215640c1100440c100050000c005c11140000c0d001c00c0c2c14039004641c030410500c0c0600b502d61620 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 975509712 1250 975508462 975508483
    0x38070e1206011e05130b09181b04020d1d010c0201140118090f0b09010f0b03070915090501060f1101020414060c281b050904140106180b0f0a030c0512 66
    0x8289103824900d1400e682c000c040846d000340e4203a01540c031900909400d0094090f82d010350790344140c0443e1449000a440c0805c002c00280c80145803030165400030003561884514416403a00005154038888804d200b010b55240321403008110036249240b01a110703210602c40c80102d25001044881d900c4440d50001c2c0310158000455104010b00b440e0031070039020111000705d0306502c1e0403401600c9101038020b1303140c0f5100080142c0352850500103c01c0003000505072540b0260404800451126110703c1203a0203001103440e00f00b111108000d00034684040030000b02c403203074014001004002554003c402c0c50b810215012500c9004c0195201c0c9880c590008540f03c84107001582070004045100b40010a4090024000485103032207240c059410a4440c03550440203950000307002c03c0c44240b14402e008459030000c070f00c4503503441c60060420000b003105002c540d900c4920340b0300780c60b0060075900c0c4200c00742c5040110525544800c8142080c03842521b0046880d0920fa1807441420706c44000b40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 975510962 1250 975509712 975509719
    0x1908040504060e01030218060307151106040506040b1006050904090f0f08040812070f02281d0610020c01030e01020d02030c09030c01051638070e1206011e05 69
    0x5241e5800124000800a102c00d901501c4801f50107800b2103c0c00300c40d1031203107001600401f9203d03d880c003507518104107039155400308000d02e00485807412092103100d00843c0100010500c6050501b00b084600e50054202d035040600a01c04202094002c400d03500c0096080b0340000d442c00090a00204400e43d0007001007541c240d051440d0304019010b4044d00580710001c04640d002034105403441d541c5d01c908400a46405040e0881c4070041c07400204141c81c3c224030b16102802403001d007100d6035083c03d60383c0040c07412506d14201000709220600030280e1258046509032424443d2420180d11810310440c1c29041586a020031005403000b50103d800c00c0385801030440d40d0303161a01d1044001c0d0464081c0b50711901030501c0d24040d6612a00c15076480541c80c0790480400e070401e5640130020700001443c003251020405014001c0d02021417854a055800b800b042447e03d03003888020111826840420310503540598040c65030380c000203125054542c004202e011040e0f00c0c0442522040c403e80c449030b032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 975512212 1250 975510962 975510971
    0x92603040b0c0a091e0f080f06041e050709050a180f06050424150f030816020d020607031d0105041215020405030f0709110702100806130501090606020c0901081908040504 75
    0x1402c8170b18920741c00860b6007a9843c010095101c0b00243c0d00ca02808080e80210361008000c100441ca030000c051000010602e490780c2d1480180d5101810320220754080c0510f0350b6100c1c1007040c1d401c03183c007a51380e40b000c1003800d4000b0b200041d03031492007282c040880036007841d03641c500103401c21071100d05c0c05182c01307000980e00c20000ca506007000d0241c8103296a92083e0340000d034000841804010020003030703c1d40403103001d00f003504540288407041e2443c00240e1380016416500c0015031607510040c40c001c0e00036034491500c0d41c405480301070121001c40b1210704100302041b0411021103c450014a402d0f0301416000d001003881c82c00e00080d0165410160341801018080400c0a000040310345c111201d075501031100030700000c02d403a410301605601139000303450070080038889032040da803461340030000821040f000c0399001b1440b8101c42c03090300b020003190395800c000d00c20b05804000301080e00074100e42c030341240e43c18030340c40d0340d00c9104020708283e1001400c00304004010b1000282da02920002e4802c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 975513462 1250 975512212 975512249
    0x603060501080a0507090506030604080c0114010311040b0d0512070f050d11070609061d191e090510030f210302040f120c05010f0c0501092603040b0c0a09 68
    0x54a590401c60221a58814030b05c0c00158003a4a00072244201c00040140c4020381e03850304c4204455000d0802d80100d950780c2c2822840d28107000e145940a580030304c06800b0031041c51820b02089921101c42d051260383d910884400045002a050080380941e0845540721201d92a00407054001510001d2250180e0172848401c0d640c420184034200c02603004480d1610780d951010b907911300d00350280900054201d416408a0000d00100440001e0003030076860b080c040454000c095064207130448441155402e0701181882131403408134003e810301c6c45040003207082605010840301304500c0002c1c042c00c81440094240003204032032045094004640700c03220b102040000f4000e42c0540526860402141804a009000e5001d0558000d5002040401450a040040d10762807081607100c02040070b6040c1007000507600b13004401c0b40c10720410031980d400c070302c3c0c02c8001200549068480707150502801000082845e91599540009010040a03a14551b001007180c0351083c0ea0000072103000c1e90070005e03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 975514712 1250 975513462 975513479
    0x1803100203070f080c0a051e0309100516080115140a080106021902010c1403090a030b060a17070e0c071221020c031b0102130b1e0703170a0603060501 66
    0x158401c00c02903480b95003c0582032419140a601590258058201031100104550086c001040d9a00084401031264682d00300101d0391548202c0310040c0503081103000507106c1506006098108800818846801c000454010710546052142c540056500d28020519601401482401c07200c5458025501d601420014081940a1058800522508454041c4200e40c2c040508145505079280400000f031350715003d640090107412400b035800108030501d82c82e5104c281141c02944203405024440c500001004148285584200044e101c0d0f0100200f1038100421020180c0c0d820280502c42d40d01c45060f1401b05000e600b0000b00078000c174810030f05110f5001403407901c00c0f4500386000700481e0440300e4110264000c20003514543c0d4414049144000c54100520208445182c00141400c001074421003104060340d20036030303000c040041c011165000038800324044943c0b5066192401c03a142c0d80003006412001084802d55980c07c0225850404c942c02442c000c542242c001c3c061561154103e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 975515962 1250 975514712 975514717
    0x418091a0c040e010603060302060d0b04110c0a060e0601210f06050c0d051f090e0a021009290901030c0e0a0320030c1507020130060905090c010518031002 68
    0x20756403c2d580c00c100000d0140e229001c0c01c81030301e40c0685110b040540c50200000038003103079012180d00a0701da804120580d03200001805507410500010076120360207081090407100c2c48100c2d140349402410050101a0a0314060701c2540c4080b01d009054081908011010800b120300040c0440d0030282480010f8003a0f10141070340e09c1c041d410400403070702c1c2c01c4124220440c600e0a05c0200c400424030400c00311a0a0740242c00c02000700302a0f4078008031950004415591881c01000841e200c0001404915149003007078800b811000244102614040114182c43c0664000d2604242d1580304c002da401d4451000c0c488103101c0581485141070322441e003940c0d880c1d40300780c18501828600d1480f2400d8900000c1c4503845d6070780500080d601e0108a11010003550000500b6070501454071140e8980e01004034458440b1400304a6044600034143c10410503a002c03944003542c540d0401062003520400030030000b03580d003802d00b0410798404240907148482a1040c5019078140910740290400d6201e0707400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 975517212 1250 975515962 975515969
    0xa0b01090501020c01093f0b1b030c0904060b0703110c0a0e0a0f0e030d2c0d080403120c050d0e070b0d09080712050a0909020418091a0c04 61
    0x20348485903501c807001242c0c3c90b0011400c00b40060241da008101070710040a00c8108010303040c40c003940c0b54500e03a01c04070704105403010001c0500c001c19145070603c030703440240540001c016400c1121005080481040c07500014008a00c030940c0000c4440b074a40e80c903402400108482c603480e0b9107d522506028181d07185030000004c0310b029501141c1010710b4000301c07070010f0320001480758401c3d171941c8080344010140d0180d0325a0071555900c038203c0300b20042000c0c3c280d0700104940403601c051760004094040b00c41d0391501d00130b001c50a0748250012030100d2112001c1320b240c070301080c40b03035507604040300d54030101e55858070000e2510510050090b0301000074048100c4030101440041990150266505120f110704280c80703009000802c070342c210035002000c43c1c6d070041ca40d0750b0402c0a00c0d165101e250540141d16800f058000424109076038000032030b40000d0445880031804c00d8500b44441c42c051402000e294000e595840028040180c01c02c50034400d460960149541890088041c2d80c070342c0d00502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 975518462 1250 975517212 975517217
    0x30b0106210b0a09093009061805040c091e051507050a0f14010f02090f04050f150a15020102040f080a03050703141e0a170603070515120a0b01 63
    0x7070710303401e500160003040c034070000141039a9081c903c1c01d003410000b40000802240d0860160340d103070041075022540001000310400000071060092400a0b124110030f9000e0801e22030b0a0507041e04905080c040c0e8001c0301c0c01528082035042e5045d03800ca421024941001c00c2d414018103440c03030000000300b00c64007601c03810394504034054000040c40840f070240f148018500d500100740070000070b101f1980100c01620070040e28803480c0782011014292144c605000082ea903010031410b20764a08100303480c4107507001b42c40400090414039050a407051005050001c10000902407681903100e04001400402c02344845185040780800028042e40c014814044c00d40300d400320104448402048400344568236403103c503d04800d030780c1c0070341300b00078400d0103054550b6040c4100d4006030014180941069230940350a40c0d1800900b001425044100601c0d080404000040110a840028001007034030030844100440c0d4840d2940d4540350b00c5004110356151400b03c052221004103600072a04424098 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 975519712 1250 975518462 975518507
    0x40803060103110c1c02030d020c0a02100c02030a080901110601030b010e06010807050a14072418030503060409020307170705150f0702120f121e0301060c060e07030b0106 75
    0x680094114040c6041d0b90105800281051750b8055646040751003031420b80c0107503810524074000e61070490f0400b018154094100250348011440d121100d1240b01601d428204107261580c2c021035070718004c03200014003001c400109089268080c440c0c862551040b5011100190f85910742904400310070311500f82c81d101c4032000f0520660085441520a4141e83d03141410a4291901120300c02555912031030180b60400080d008200303c001c910a000c0071118514180d4800b04a00d841202c43c1d070548480b90072106010b030800a907020040760b4105030120f4001c26040e085000290a00c16507605c5058902c0041030342410f0b0400c0404c40c0d800b1076070100d41811132a01d030320800d81c80c05c0c480c2540310b032900c00c03003005503000520305910200d05108a01049804a000d00389082d4274084c07000c5e43d0382d01041d9020601c800c040030205081442c041d01c0188460943d4500030014007807101c01d06001706416100c51114512a07020401e0800540d000340c824401035954580141000b40402403000072142e10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 975520962 1250 975519712 975519731
    0x7051203092e230c0105090d0e011409120303040f2108010e0403021213030c0b12040f0f050a0b0906090c0603011214010c0e030d0e24070b040803060103 67
    0x10160852015a80d44102c042c1d9003014001c100d80c0c010b424044840b141d0301c0d01007100088039520000c0c2a001000c031000003064180001a20710f403800c00d5607188208180d0920040250b40d000b6504110350095080e0281c039514240c002034920782040c01042050f101c04401c00084c040b040700ca00c2e0302e8034002c00300900044040035440c40c0440c2901c91100c0860034a030010450524072360f00d002d51240c00781c8188c8481d000c10783c1024481e0383c02000c2500d0241d10071075090050001482c1e03140001c8c1380606242d8603202800d108480d030005c001300b0161010f16800380300704c02d100c01e54014040199025003075801c441ea403072408440704002604c04000ca8410300c400901c40380c40014040c5003e9100030005030a603072a08070341111142030010101d608480340d0203008001c00d424003415000710915107510101981000c145440c0c0441c540b0901c080010751241d4408948a81c4025105440e0345200f41c40ba0004c00d007011100c034401e8580062008680a08000038844030f0fa001d9070280304240c0c2e062141100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 975522212 1250 975520962 975520999
    0x309150909040b15090a06050a05090f15010c0804030303092102120901110f100e030313030f0509030a1112070501051b0106050a0e0a060504020a17090705120309 71
    0x5494025801c00410800300700490f1008401c5a40f01000c0c80e044200b00506030081880304074241c6428039040d869134000d00c201d25050362140040c01c000c0d24000c0452410b0000422407480c090456209803a400d402c0142c0c0b03074465000b0824403508170310a00d41d038070703564a0000c1c01004090020f07540e580e038109513040c0d60503010ba000070102001c0d5000700008138900c0411081e03503000d400458103202c182401e00000c0101801440a0b0413509009012801d50040d0160103440c07407a058130b1481c1e0410801c02040107010400002c1540c0c0500d09a0f0f400740006c982518640301e031700c061640c90f01c1142c3d864803c2101c0ea450202003c1010b40e1145000018062551381c0c800c058094036004c1740c810b00c0707801d01c40d402038403180310800006030000c644e15a40350302088240125421040c80e0030805403c0001d48111070080200400007618210314142948400401d810f1482c0540b80000d60fa56020801c08601040b81c4406048024074000f100124580300c507139a07901c500912409000c50f0311104a07107e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 975523462 1250 975522212 975522217
    0x302060315040f021804150f0603050405010b0a08060117010f0204080a0606080c0303070201030209180c03070f020c1f020718060801140106090510030f02030708060f0f031f0f0e030915 81
    0x24260914840500da8401b0080503022086500120308a00d40c00082c2c01c80202a14100034060754900007464101420442d003900e000c101c0490184e50a0541002511800602507045410000810038807281000f080e40c0076003800b95080507140c0c004034002c5041000800d000700c00078410310040101c03d80d10b0030455180c0c420560350300c1d0301d034000b4400000554002d40007090408002801d00711020400d100c00340311101d0075541003c10690120401051503085008074020000500080c00d100500744001f813003005d44000d1450305900c111a0040031070f4000c105c03103005003101d102d00388540c0d0280f00714040206150f02c5131280960030190b400c0c0003403085c2e0103000d040c3e42079952980c0c0d89c1e03810304080c00213138200075080790101540c0d8800021088034502c0a1401403490380e40e5a130050802d8020400050081820944a000c80c1c01980c041550f000030700c07901d0401d2009402e030f4640080361005009051450780306c40c04a00305004c005540c0d1021004006500040b1918580c0d00c800e000f4a038404e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 975524712 1250 975523462 975523477
    0xc04020d05070f03061401570506060d05030d05040308160509030606010f02070e0f3304180507090509010522170d09121e0c0b0702070302060315040f02 67
    0x46c090040300c418039403280501000c409045001040d0490b54a01120b8244404914502c10505034030fa05110346030382d14004d22907081943c1e1142c0e100500e544c4605448040141100e031081742c0e0209124204003090060310f002c91031040c01004540b41c1410b000c0c1803401c007229448010800b80c0c42c00b861160280040d21342a0740c1c0076004004542c1d4020040d0340d004468030140c0c01f58455803134001055000100c2180c421a804441e0340040e091102e01400c07110b803011010fa10800817010700b00c2298484c651000d0400344102c1e40456100c00403e008200100030a001401a002d05500031400591a030040c50103800650300801080e62034100c0110780300005803c0310301c0549070b040850086509000b01903001c2048004551405229008510845070400e030111004510100001c0440e600181107242d2003150200150354100683c0c80200040e10411005111080d004041158603108020040c0915800741c0301e60703680d04040d5494010900e0700c0c0348841c400c0d4148181c0500d1028076000396103e6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 975525962 1250 975524712 975524729
    0x16030807180e1b04060f1403190b0a0f030b06091501020316080f070f030306090c140c010f02070b01030501060506120c0c010e100c0305060f0906120c04020d05070f0306 74
    0x12410040b01c0d031500c4201804400d00b03480250040c056018015004000400c066150921070440c00000a881040c02e410b042c2d41c250400d2003048185021004525800007591000048150660b0001003c41919822a19108001e82004000c101800c01d0300740c00b45100b1110011b40d56946503103000359410000003240145c00610007071051072107688140e00028402c2050703904211407c0c02c042030940007207405407041d0900040c0801499054450f9501401108000b844401e28000001e01420300258940c14900d0340001c4518505000394845865025045030075960381e0003034101501d4458007030105840319464914005000d240400490b0f80c0c040b07244c103150181c0d80e19101e0b02c01941c1c008000364401b17035490300b406500f502d100b0b0220348201c8442d007000080780c2010580050444000030002c41c042c03d40d280d010707005551a07651103035024504503581500101c85441e52410624003141440e0807a002140142c0c0920617904a1489001e1540e00c2c40152190500c0450a581c402d00c1103402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 975527212 1250 975525962 975526007
    0x4080a020d031218030f0e0a150c0503040303080412020c1c031b08251a04020a170a020f040c1d03073c1404090609050316030807 57
    0x1424403990100d452030103410510034880c95403c4200c1030b01c04902904014024211464040580003510040c284136145060740c4800c42000203c3c500d9010790280b40d00200e4101c08100c3c1c154820300059018992090980351210b079a80760107082c9501c251403c94010f500030359100401c0748000340054204c0f400801c16010040d4446480c450040362081c103400300000d411030400702e401c80381942c3c4c5500d031041030300325500d0204402c3d802c01001e60308010952040c404940318045940001d0202000b441d0300c1d5030f1080c0782c480d03200090000034181d0200307003145e0207150060f00101c0d0120f1080201e40c001d90f0303181c05800c0060200403c07941d40c10000c0012410030303a89920162800840c01400b0000a001c0700c3d02ca9031200c241305400300700c03180804541000070f03c2d0b403141c4941e01c03d03080517624103034200c0401d60703824402461900c00c1b00e030758150b0040796607002c01c0081c400560003a800b1540c0240c15290f6620380213200c00700c250307403c44c82640824000800310b00c4007407141d031103040c8032000c1e04180007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 975528462 1250 975527212 975527233
    0xc0c04270303270f230703062403030203090103110405060d050604061a09030705150f0a090f0e3907060e03220b03070e040b030a0c08011e020408 64
    0x103004144494a01e4452001c3d096401070200a1195500e0440d00504a540480c91103203881d002d40c07441c07a0104182d441041d202032503100b90000d128820307603520150108800554500a20f1100c035003590488821040035000810b160f0040010104039200f130b60140840685c191030f100c0d2910031441200d4100204001240b000c8901c1c1d401550400c030010000704803540d9401c418210f6040390b41d0301401001000488031b81e5450108040c600401c81501c1110024172480080e2110340541e02c0d014100440c00100f08600900c074440f048e003d403400e1004084101d8850011408990044801c41c10720440100c00800030044010008103914441105055107001c100e00c0704e009401801040720002d49507900d80d02d6407070044c0301800b40704010740d80c1c0340c0074800d20032403e0f02d104401c5c0d4460b1078681e50820610124942c000e100f40342480003554041070f60440000440d29260385440c0c0030b0450400350001052495040d00406850440041c00c0001d07101c00340b85a40891003140709949981c0d01031903030341 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 975529712 1250 975528462 975528467
    0x1d0705030a0b030f031c0e010e03160303060f0605120a110417010b18061f02030d0903210e2e0b060c01050f0f0f0f04080f0f0c0c042703 60
    0x4400b9090180955070070300300500d0958955003110214400050242c15043ea14000510407800e400444000030700155450228a07612482085260a0103410300d209000626000350050b030b00400100d24554886c070303901d450091a54004802031f00d0014a0100070441048240c054650803e40090b0700c2c0b460240307000c101e075811402c00341d01c02c000ca540320540415a65118480b46249240b140c03c4c0030890300e00030f420000c0f840701e00d800e8807140098400c03802c41060350000c2501c0036900b01c0c005c00241550313107007801c6d5001600c503000c4100d4284103400440d116001a045041814045001c45860703100741255141070407510181e4400054400740e509125184980112040d848080c29581c07602504030724a0b0b00356082140d00e00145030f400024420140700d206140e50340110703031800c1c120b0039041560380148014000f92001e0401c1c4d4001c940c50040500310004c45000c4481008000e81c1e400d19040100c0d01d900128120780d20407458810211001d2a4540c08002c0d000194140c01e0500300850f40c0a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 975530962 1250 975529712 975529721
    0xe06010f11010b150a032304020f0a05040504150605120318120334020906120115080f0f070e19020f030406020702090c0f0d0e160e011d0705030a 64
    0x410000c0d42d00c03003180d0700b000d4861090591000c0a011009560303085c0c03004015040d50904008141c03a04901c078140c6e83d00d008124411600706604650400c0042c00b00400511042c500e034000c1c90b030140c0741c8405e0001b00110142d000b00799264030101488110b90780c008002e1b820440300c000080a40041210744070301c81070403044c4039207041c000306201ca244ca107880000f071540d0030002000c98900e030342c00300d8800d00c0d541105071000101c20a00800018540c268041900910050503141c0100001203840b020702c0030a400c121289d050b075200451000b07540e00011940c4005800201860380905450410f4070710001c40c15409642c2201c0c045602901c429594000300355111a0562a00d642400342d0b100d01d6074500c000b140500e01420780580c481526004024072901c01928074240c29404025144107900c2da0002c6e00e50036005000300041c029215100a0b0501403074100400309a2001d000c0415482c003031960007416120100c0500d0b08070540500c41c000300100c2900d925011840610005480c0f4580303410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 975532212 1250 975530962 975530987
    0x1302060313050303070207030506101401032c0c010e0306090c09040807020a0306050601114204050105180703020a0308030a02120708090f0105060603010521070306020d060e06010f 79
    0x1d4260078915151241070441d0020350b00740c001600310350420814407000b080420f82211524162030a035520b41100066440c0501b60070070305040e1100304c101c010700c01003100c400025025a10a28051600c0d00307d50703172601c14100c801808546040065050341c100042d5040c810940300c0010803511f050801009400c0300001c0046444032400c110b140300503201c403482480218031030384011946080860002d8003c4000c200b090050fa4040e2111828410414852401d4001001c2080303c008900d03484000c0040c0f0890900d0301e03420a003c091200b002030541c01548500c035841d5070f022042da201c60700240c44800501c0040d601490004081c00811840401942c0203000300d040140341802d00303040c040410314100c4034880400c681d4020031003407403010700043c00c6406100000f04010b242940c001449808180500e130700407140017407548007009540d24010146035400c0d04407001030b9520320b0228040c1d0b0184241c00345807070406d40005200c140d044110b901600050310340d0044a00003020495410140d00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 975533462 1250 975532212 975532231
    0xc0a030c05070b060d0212030a0c03080708062103041d01050906060f04060f030b090405011a01050a08010b07020f0d0f0201091520030d1104031a09032b021c05010602030313020603 79
    0x4000c0c03600c03071808000404109c80d05071584001c4002c00c0c00c014024078802040c190521860400b0002d00d9580e10410407001c1400740060812284001480c0385180602d0f080ba00c0220340302c847d24091039046d41d5099040721811140e007440e80d80c1e06030070310036103020352aa24503803c8070502c800d000c082c1c001e25600242c0e10880c40d002401d040348100240790018261b6040d41c099642d01c0c8030051084102c941c1142e110420700300789140035100f01d0002c0102c6814494041000c8001c00c08030115030b580034801d124010010160306034050142024a00c0190709102240411001c00c000190000c80a14024002c06c0645440e0381c2c40340502e001c090368008128107440203020400c0000300300c151038802e0390703042c2c07886910640c0c85908520b0580e400351401040704801c840544c0400c505082c1c0041294046481039001c11680400e8032104038444040b136940740c00700390000c03a45280032040c2e201070095540703848109001030f0342e032100c0c00d0f61a4403003515181200070034000c41d4009410041c0086400c2001507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 975534712 1250 975533462 975533479
    0x60212030411040f090203100e34080706030c0c0c120f02040e150a05060f151903020a0210090201120e0304090219020f010e03031305030c01050c0a030c05070b060d02 73
    0x101118500604c04480c6030351000d964055040c10000001c074418041e0003002001c2d01e445010385c1c2c1d107400045aa218482c501d003420850954070003400315003c844503140070a01c0d12901403985500140c020300c0e0000740762171003d05010b40320340001d28925030442008072002d41014901c0e001c104180c1c070203980200b035164007040161a0b910403910860154005403003c1180c1e4070303000e80d01c8040540680b16050030981480a1070351b9501801100290481c1c40083e02c0e801e44c0b010441c540070300824003656800305400a0529a0190000c0c24079001c0c5500351152880d941101c04221821a4070181c00070744400c170030b881c43c529150301c80780700c0080107030403a810543e5500b0120305a911624002802c3d000300d01c400460541c0400609184501c6030f4000d000707a0070f161044c0c580d030f400000c2907c0814660082d12609012050046900a1454000a003d02d00e05001808200d40c0500b5030000028689105500b0803881241a035451903400480ca0707107142c0f102000c10890f40c802c07000a80e03020003034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 975535962 1250 975534712 975534743
    0xc1903020c2b0e09181603110901230609040b0607151808070201030b1f09050306070e010504050d050106150c060b01051c0c110703030206150103060602120304 70
    0x20009200e8146504149080b0855580d1054502c840014010400c0c031100c0742c00d5a9071a682d0a01d810341c003186017610404d0340d9250107031a43c50030040d4007200600c0305110801200b800f000b40c8902903000419034602c0640d90b43c4140f21500c070060000001c069641404140502d4940300d00141010300b0000c0c4041a254501400103900c1d600800007207410310034010410340b103c403060040284025882c0c0c41903424441c50b8072080d00620600388028109642e8080392507641e5140d101486c01d032000e40c071418200351801000601405800d01800784640b240f0000998840c0c071621401c8800281a5100c600f4146480c3c2400151212150201d40c00d54070b4183c081440c2d07141c130f10320310b21800103a521140c169006081000484c2c42611140b41004001c0101c0c640002403042e120815a104000028424540450071580c5003e1800d103a8142c0c02007500000a05030700065542c00b5103c074203481c2039030400c07500064007114000e11445025810007228400103d00245c051980702d406881c066041c1d080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 975537212 1250 975535962 975535987
    0x305070e0312031b0a020615130c030504110a050109060c0606090c0207030c0b040308030c0306030715020a0309050415030b071407060f0c02010b060d0e0f03071412030c190302 77
    0xc81d6200726040750000f1040003030000d060b0f4414004281190525850b107504180d00a4991400414014a81804140c8503440b520748903540c9101a00c0d01d03030700b04500c20038114010060a42580c040c0c4258141c0400000749190041d6080210f5605840300300b080c1e80f8260081d6204008403405491065403482c0001d400300580c0101c03c0d400c8050380c0a4140142107103400307003c00115400c0702040c107030140418000501c0f88070031070783c110702540c1244e500d81e82d4a20000e4900400c03034010a080002108100d82d10715000205d00d0501482a1503008055844100784800c940004542c20781400c14148100040303010940c070705070022804e2400110445407080201101d074808081244d206a841034840096040740c820710311625901d00c000c0c00710410000015016008003070700740d0f156513540c03003405c103000303008010f02110003004009036a240d0341c0d241004802a610000d00c0c1245000d440c4a00e0140751070318088902c076200d0f01e041307203081111038401408464150031b404018141c0c00c1208400640303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 975538462 1250 975537212 975537223
    0x5030607140f0406201506040509100f0203060a0e16030b191d0f13140a0b01171501083304051608010c12090602070b0c03010306060b030601050a0305070e03 69
    0x18a03900e81c1c800014080e20200c501c6a0b0303001e05c0014640141c9045401101c1c1c404039a034104400303c03808620750300c0f114495401d00300d070302164a5800f45408540305610101c0d4000c3c1d031150400311100016503036211000a0039a50480e00c1c84403101181151218150099001c5030001c18081e000c00c640c0302800529040c810301c03680082c00302e1401c502d498006416210921a0311040d02e092608071800c042a604082d0200158001c0840030784052140088408101000c0c8482e00010304c16030780d5075512480f1142c429000d12220b070074010f40004480e103180c5080210b040325000c400a040789003060710803541811a41c800700000701c010340460302010184841c0d2034001c60240c0301030710000804400d91601e0440aa00c91007140e418044484665a08008034610100e5080008181058546816002845150401402e0395000e42c184802d1110140245050300d100740f0301041000e403580d00d2010180000c48038240010303010041982e02d28442d4007e20341052050400c04564100040044d0074903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 975539568 1106 975538462 975538469
    0xb0604060f0e13240f030c0303110c130f0e0105161404052806081b0c0a0512090f1008010e1003060906060311040605030607140f04 58
    0x1602c07292010f030041c0070030f034408000b18141d110350b00000d00d4a034003540511250402000c24002d0005d95042d007501d0300074420000c071910f50fa03400c81c2c51140301003e141303642c00381c4007500030b582c3c4480012130380750001007401069401c0462912002c503000182c26040b03981c1020b0611921032200310a10380304180500d00f510f00080410021006440303268402600700ba021129136000c0d10542e180c00803d0f500c40110644540d0381c900003140c4406040d84c2901000b0822241080b00803004001440d541c1405015103d0b201203548640c0d090030141004500d112000040e2456a460014141019444111615500c0341d0004000800b0f406050284400e01207024000c0b032249102c80c3c020000860784403030140100c521514100d000b604440c032085030000c3d0414130061007803519003d0001940d001400a01442c1d80d044821140c0c150156100d90341614100300c1c034138003604600020b1024 = true := by decide +kernel

theorem cover : BRFrame.Cov 975359712 975539568 := by
  have h0 := BRFrame.cov_init 975359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 975359712 ≤ n) (h2 : n < 975539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
