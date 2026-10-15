-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5227
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:10:07.018003+00:00
-- url     : https://prove2.me/submissions/62c130e9-7c24-4e10-9644-c17ea02e96be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 939928057 ≤ n < 940107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 939929307 1250 939928057 939928061
    0x403080f07060b06090a1703040308180f010f12090c240912030504230312130e0402011718010c020c0f040216140c0a09090309080303090c041512050303010315 70
    0x30210000304110380a500b41107d0025104403c10f00d00c0d41c5110030000800490759400103030002c1d2884100c620360f803005d4201445051000742412034180a03410208440f0070340c01070703000d4040b030f030401e040090728482e1408c210420103081d84c480180e41c502c42da4000001864820302c07500c030074070b151600070110350380318084100c80c0080700015000800c00d01040c840d2240303030700c8103d00890b48661400b03212030355800020308010350110846652180010449049251048910300424071103030921034a05c1c0c0383c0c0010302148000400242c09024001c0000d400c0b1031001243c5043c41021402004410b060940103507031000515540d601c40c281140059203185418021502601d100b400382e00000030306540d40b0945200300484940741c50180d410269000e0300c1e00c2c5a01c00050520007804110345e501c5007006001c042440c0c025001c140c10401c2080034203440002c4402e0020004d890008654120b00180204e001480c0c1000580c0202050903c061002c004080d6060f40d00804100d1300d46c251010500301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 939930557 1250 939929307 939929317
    0x405060c0a050d0f090512070c0807030b06060a1e1206091107290f0412020c060315030307021207080d031e0528051e01031a0702030403080f07060b06 66
    0x91030421940c80d1010050308524100e1303030045004a8640b4807666918180b250450060500308000b0601c08140300b20030803104020070040c3c018004607415a203a100c02d002008148901490340000c0b4040018450042d41c0b00d8035078501d003c901003142554008040b075400e05241007032a8100711021134445124440d0002e20301c03400c81c070319140c4036180d501c18080f40b01a610030085010704004a00d44a80110865132041e10440c5500c0d07607500c1c0a241c0301100c4000c1620300000c41d400840c909030662034110407241c02065065200c2413034180d03000000c0c65486840c4000b508110750303403042e00e0a030000040460a484d0032009880d0b502d09101d40131002c070b403207106030061126003103545116001d80715800702e030700210340f138103444140740c0060070300c12803158503249001290f035941c01041101d80800c2d101c91900e4413907140302d132055403460301c8030f01070109003c0e01e1007c4000c0460228400500820444004580c040c44c5c0d1510340c0e41c45003501c05140c0100b407007a140c071410104800343c1d40c685182221 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 939931807 1250 939930557 939930577
    0x30f030b0a0b0a0305180a030207060f0320030a061a03060103112b0e1c020d0903020a03080c03070212010605091024090b1c060b070b01151709060405060c 68
    0x2d00f418810030049014040150100c1d14142d1104620701000d40144001c844040c0070340c0041401a2070b10500801c6081d0426424082624100f80c1000b910542c01c0400500714031660381a84070b0300d0f40303003250008000f69400112040d1420900441071418400075600c00c1e40c098804001200d1640010030311440307081003c8a81040d044003000311250142c040075a4005034440014400030300020140c9420640c1940e0503442c00000c04a045880d810844100d05180501d0300c608100d295a001c900d50301d415010040110034080b8030100180070800175240d005030000c10511019008140640c024402ca010f0035025400e448005001400f4040c4080100c4020540e0440105410131512801f011515200c204000c002580002d4003100758029280e01030400c0030142201d070035106520100d48559101c0340c1d07444d5051050b1808180400c2410741181c0004141b07102c10200c20400303c0300c0f141403012010100f00800140200008006411882584940101d400e20b0f100c000541503980074a490b08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 939933057 1250 939931807 939931829
    0x30504080f030405010908070f05010507090b04033810050913020405331f02030f0d020c01090c0303031802030c060a03020c0d03020309070b090607230a030f030b0a 72
    0x50000c9110758001c6601600800001500508a545094483d48425000e5031004500100002441028403500342c0011240c1080d00c1c007940340c914a00d0303880c065884050a01c0080e13440700010b0f042c0e01c003d4200021811008540e06080891090780f020f01c0c15a002621842c55845c085000d003440640300340a6903015215042030911942008081c04008000c48202040c003c00020b00c1e59a0302a2880d2141184803070888a9015a06000000441060324460f44401d101318010709030700842210010742d42c0000d041c0e40d0b120b8052540303020b407050903c5c942c2150300c0e210388171040c40408810034058921030340d4103001c03c40c61a1036013030910011f0140070b03616402510104510b8a0140700521144203d401c01505255404440c542005100003000c808243c00000b00a101c1500340041c1c1c1c01b03412480a0181044802804510180200c0d20700070214824041c032524581442c400720307600100303500c0840f88031644500c0d00420b00b00040c007115010034100380c0c00c4901454107880e10320540390f2040715 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 939934307 1250 939933057 939933067
    0xc1b060c3001140d05060f06101b06200c01050103230c041d0a1101080708010b03160516060b09100303021c111608071d1501030e030a0e0405060103050408 68
    0x12041d02c0325030303000d03a580c2d000401e20581400150b09102c0355204a825903a02951848d14509128841d14400d01d041c0c00c20255035001004aa205041c000890390000c00c0010585440030b210b16420788078403c03083c5606000b0606d01e541402c150400340c1600c0c0b1a440341c20450380840703961000c01c42031150020315a00042c503c8a140d05180c1c2c4142800300e1b00c4902c04c1014181d240c003050510103001d0040e11038440c000c5459a40c0d50308000f10b01d401407443c3c40d00c809a0342c03400c5100440b50001404030380c2004085408800c24920500c261000d0328001d01c4044c41218861500c8801001107181d0140075000c17040c0020118601c0040c41030403a0340603000790929162102c0400342841c49043c0c18801c0c0120724150540c102c108100781c0710f0044200007070900c0c56050060035864444035521043c041038540d80142c1074400424006134000842c1d04e11103982101c02030058019041e000d12108840c800842c4a500303d90707002241d507141c0c030010349003001701d612108011800e88600312000f420100041203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 939935557 1250 939934307 939934319
    0x3150d110409051603200d030c03030b0f0a060e120f1b06130305030d2406120608030310060e030d08130804030602040e040213050f0c1b060c3001 64
    0x124140c035611803401e60f00a20b0310003200c00c0504000e0b0f00701b40d40e100344596a091961412050148250804943c0e4013107410075a80c00910286e0b100c1c400a04246d111051058141c50f481c90254104000401080c0000c3c0c855600800e5065421200703032051402c100c51580452010440000a41c8084080d0031b46034000301c0101c0c00d1121000700190000010000503007400200341011000c0c1d44643c010310f5544042c2d100d00415110314160282a07038443c10078860400034100072070400c07185182084c1d141131140c5c0040d080185581d0b40a0215404008104030b04480c81d0b030f1001c0d0940322a40c54118940007400241075071251b81c940e480010a54030300200b09400c000c600031283c09071083e0030b007515003a01c2e0360354079080e40c201c0e84c019140e0184010074002146402c0354a8041c0d43e41d503e0013081b59141c0180c00e68006031000c0c0003101200c2c80081c584038503c64801d03081c03031400140c100700c2d221800d00341325030380841e40b002c02c1c40980c0d0200c03029510b0700b00000d01c1c811100c030700b6031a021003003507400e2403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 939936807 1250 939935557 939935561
    0x11030a0c0e1921060e0604050d0e0a030b06030102090d2105030108030a0e0a08100911090601080a02090303040801090b1017070620060708370e0f07080303150d1104 72
    0x2c503030b0030040c02c240100f600081c0140103204502d110000600910709062814916041440500c1c1c4e0a00900c0f1a81400b582c8942080c60304403500103500c003489403a1200071900a10401d000f840d0409034402004003400fa0481c800c0442010000c103003050661211001c4856000c207000b910003a80040100d0151244260541e110b02a80240400350895039840042e15050400381414071807030310342c0481800c1c002030840454102d03005482c180303020310f0040002000c9410040020303d07141d41c04202101540c504205980c0549a800000c00040c40a0f0910f00d04d5030f41c0031268450150784850008ca0181c010b00c0c0c0c1c80b201c0741c407080000c1c407085003041c6c03080e1a0b0701c0703003020104083c9448007002d1404100070080d0038080e000c40d031a060343c0b07401c115080002d006011100f42c002840d400f94109540b003142400350101042c00d9074002484a1001c0c600c03801c00410f1740010500d44070346500807402020100095000d41c0f03414181c041d000c48404144015550403a10141500f045046502e0280c1066 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 939938057 1250 939936807 939936839
    0xc040207110f0a0f030b01081c05070b100f08030c0609030405010206130839030301060210090f02030d0f021911060d0b121e0109080f0c0111030a0c0e19 67
    0x803c01d600d160b84414560f0310030041a4002d45810003d5001000160030074400603010004420223148d0841c1a244e002d0510321071010010030040e825400200c3c6400c09406c00409406c5449114400079950003011b41d903500810a1280d0700e01550000c02c00c0341ca000011201205c4040e00503240f1640c84078610100100c0000d000d83c0c0414040111f160f408072001240e805850884004440001980130382d540324030144440c0c0c6e415580108010700c2840e8000030b2130081e03010f02c94400314501e0600d1505084034044948001d4041c495001c5041c1c00d590015122b02c041c01c240c2e4201c03600003800807a00e03140f110500b40c010b86204d00000300d1100c9030030810b005207207107888200081000e0760100f0100b20f4000214410811070380106040070198a04a06070b062000b041c0c030000e104e0180651182140c03031054000661610000040c1d2400d0190290001242d0140012107141c6a1030f00d05400d2000d40f01e400420000592601181e040b03503c0c1c0540b0005441c100031143d480310504120758003800c00e4003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 939939307 1250 939938057 939938059
    0x13090f020c4804090c080606041401090e0c04060803040e090316030c031b111201020f0a051615140717181905161502150403030b0d140c040207110f 65
    0x101c0d040e0820b40e6200d50050500030380c401e00500070203030f1030035514608000c4003803d0284140c0c1421245036110101d043d00c641540c2c200c84001550006d001d500d94034184452000d0707a003150400c00c0001d484540400500100c941001820515544c0c040d281da0300c9208416201c0c820100c0c074459031001ca40320740385021415200b41005200460360b008000c03051422031404581d2400503e400b5881ca050400d11010b084415100030b5080006900640406005541038401000000306508001d0884100b4414051750840012490039070b1072130318031010304140e4851240110690b4046103d9a00c40c0f611800000c4410701400c6954403044500054103040d0440c0031601d20649803212000d41d5600c4c1450b2046100b400100141c1240c88800600c03e209944007c50705c0003803038a004001a00414485040325509041e25083e559500e401d4000b001c045c1d1800b500000c50340d804074100404880d46d50002d0a5130405c44d507503184444108030076031042c184010315031940034880c00403609041d9070920301440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 939940557 1250 939939307 939939433
    0x190f170a060b040204181a030313030b100e0f010305011104051c02150a03090501060e01050105160c120f02011706150c01020c01180c08030a09030813090f020c 70
    0x182c1d84181b004003c1002c0d411455141d660704414a045c1a40300d0700101641042e07016509040500b500c00c242c1a403a44000b0f40300403032031000a0b0359024a20844030141c02e00211645160034204400403082200340030854043d0300e81641d038a22480450180d604071800102550001c5101d15036500111050b11012a0054220b5801e80c160740050fa024003403440650380c00151710307051401c09c070703007594071a9210310301707089040c4010302241c0d134000112360401884d00100254090035242100001d20160300c42404000d2056034502000000b05071110000d00036624200c0c0511080c40105840a0070b41e581c3c2d510040c804c8908003161070101c085e1111031500800141450807680b105070030b5400b00c4001a0a814064600808001d02080141c0240010350021410407201150161056807240030250440304081000c08101c10090303092000b6120320340062050b001003800c0d10010303401001e9072028500420b440c02d185601100c0c154400024510200307010445006d40121800c2e01d82c41004054076 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 939941807 1250 939940557 939940559
    0x6090f0a0c0b0c0a2a050a05060a0c0302211c0c020303192c071d0c220801021308061501050703230a03050703140402100e190f170a060b040204 63
    0x39220b00f90b050300b600c04907066100186400b01d1742514504542d00501e1062901c00c10a015544650040c0c84c00100b080c1000c81d0081203030705050380f522980c1c11062121910504007050801001c10160000d01050014146003081510021045e200707030901d1040145d105100003450340340303000c507520100c80007c640000c2c0c0024010070a03000006000c18694648880b001103d0103503000c0222200a0000900114a4110009084107200c0f006820344181c110301080c8141901000451242c1420003045458001c3e03030381d00a0036010303420001d03050711341103004000003810140c00305041d0704c111000408524180701e524015074054010000c25001c0080b00d05180000345640450101c0c0185509102e43d1100f040b404028280c410003021101094100b4441c041c401c05041c029940066040704c40c400340da0000c0404440d060841014140e10580c00051004510b04280c805c2084d60943c80340004100d8680c401302094403104556003010364007411051001c11401c0e44a9400500000c001501e05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 939943057 1250 939941807 939941813
    0x603031106131212020315010e0a030c05041a0405040f05010e0109020913110d06270f0210120f050a0c050406140c0102130b03060108060121110d020301060206090f0a0c0b0c0a 77
    0x203810880780f0003188541e87c920340303520350382011650010100031101c501c07080b070a40e41c0f00e80d0100d11911031075000e50f03280c400b400c103010300c3c108102c107545101800c20001c6107000d00304160f5054400c06c0648040d403030020000e4007000180100100507401505002181d11140e40000e9802d04000781070354040d04040003103485075130340003050a1145c020500070034000b01d40f0050f60800240c12409880e46000d0100c9440080c8020041d003058a804455a500e03001030300405803000b108908522010515004c1d039101c4420040d804240180701034002042a50f004540c240d03000d2059000d0100172560440c014241048048010a0200c3c50319001600740421001f000c61155065008414152008000c01500d541d0000c84190b00c03c42c24a000200e250000030741120f190301054034020031540720032120142c09140800c42d03500030f1030390340b0855403581c0d1400002d440d840c5c10f880a540b01e00520907000e40700000050f0007006d00780c01054036003141e80ba200c0e002c0c0880c0d20810030b000c4240217960980001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 939944307 1250 939943057 939943061
    0x721060503071d070e0f010c0606030605011721160c03020607080a1701052211030c07020a150504090b031f0b040c050c06011202010c0b010303030603031106131212 72
    0x2c0c5054181072950030300fa10212519200c0040c03090082160150303441826030740300f08116404042c2030070319902030038180c00c020000c1c01003a0006003500e4208000010040074286645030710b4003180702646c50b142000441004a80c000707080003200306a05201500b03401020a903560071a510a0134001110350f80c0b9400b140b12501312110540c1c85001c04624a80e100d90440c0c24030409400381d0308114420740c103110010715500c880040241d4030381c502d41d420b010540c1d19030744118114010880402e8580c0761070305240703c55a201c840300301d010342c646038400520001215151002003040d070b00d030181080e05028038030340200160301055a240c1300b50140c042082c5113081000010310140c2c80049040c00b4400d09100954001c50031034010864200010b007050400499114155580300d28420780c032104600048403625100100501004095000001016010b0f0b200d1003ca0f4400c0d00e8030031001c80b0420300f160300c40008951114016100d4840c000006083d26032010755034010341024846c9002c01c40101c42 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 939945557 1250 939944307 939944309
    0x506090919061d070206040201020a08031b1308160b0304060c030b100206010e160c1223090907110a11060f0d061d07020304150c080c0a150203072106050307 69
    0x6261a0342c0040c3c0704640010500c41d90004d054002841d0504183c0e000071740e1801c08880c06070080401001081400b0814039a4250b2076006031109522903000b40d02c0078400020611500030144100f03034180b0094050b100b2144100c44038140b101d030031507840ea200d00703001d4413010792007200305079507112400b4190381e8070004402600440e0f80100385075810001640c4031040064240901040c0151030011502c3d40a021411520341c0f0400482000300c140c0b03800d031640e040b410032008403554410030041d200740b0240c2c00341145660880d5000519128487d042d070302e00d42c007510415002d40100c2a800c000c1898070000186445001d401d41b4070f003008030448031303016070003000d01c00349a5911800e04102d803155002d0100298149a21945003074200744402a580344954030440248000c003141802140c1d01800a8020706600607551580d04c00c800007500d515a203820b202100d4400c3c0f09191820004514420b07a4410b0720340f6214844001da86c801004000d001d01c515207a13909403a2000402c264a060080c18 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 939946807 1250 939945557 939945569
    0x130203070905040308090d05090f0f12070e070f0e10031802151b1513030504050d06050f0a06030c09150305010603030e0922020621010f0807060207050609091906 71
    0x5e0003070808001880c144901c1c0148041001000c0c0074100859960444140c1c0420003104e464140d01100b6002c91150681007099404a000308000040d4030b4056421080c800d81c0e55541d40818039051040c165034854808e12429048004055041d01e224000ea01014501050f012100c0080340c2c1c55001805004003190080c01c3d1000200304480c1d2074020031004481c2148074400740c002d1b1160740980850103007005010111106941d41c030394040c5801001114081d10700a8000042406242030000240800365070745d9010864610010314298400e109103000e0f20340c0702c90404c042600d80300c49e6401404a88070319040d000c0200400000046003440741000461003a240c1d03002c1400400104022507000400344e00c20702110b103c175000702e041c0500000c5801135048405544818610440b094020080940e0b442c40305032078400865615075510015003211058411904250f4070703480c007242c4859240c400e07660841c80903c08900341e407420011313103507002260b4500551015141013900d01520510362003c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 939948057 1250 939946807 939946817
    0xb0301110405010e0a0515070c0305060f2d0106050a03112d030f0f04150e010b030705030102040e0109020d0b0d080a0e18070327030809010608151302030709050403 72
    0x40082c0e503000b4108810303602040741c4141c51075180a000c601c4808080c80c007043c10620001d0000c2c1003010007400c0001440e00413080b2801440c110428100c40c4c0303400d170341c92070380b408146020170300c1c11806c480050910b0b03030500b00301c014a900e402c1054a082d080380040106050315403103813650041c035030405040a8501c41129448030904e80190f0394003846180202d0418030b500304100017a806000040507004015045601c00da9035580c14074030b001d101d80e1400c48103003e04041405a020038150040358000d0303030890035110001e580b002014201d1149118100804012400420070500e0b0b50b405491981700981000c02c0e5010440006404c0d240950422500c0510106440c0e4810b944180041400c140035515104070080e400503030808410300400010426450341103032816260810b071800f86250300a946000547c45601d0094804074044480c0ca0b00ca61810310700150f58400050311000f40181402250540d0b15501041c810500d520718050744c0501c5a4040055403620901c0b4640c8280c1c041c2da10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 939949307 1250 939948057 939948059
    0x1022e05131a1027060803040302030d05030a0906060e04111f1803060e060a0506010c1e0606090c0e04240314070f060f120501050303160215030702010207030906080f0606030a0b03011104 82
    0x1244c007200c00680080e00c1550080c071040c401a24000380b802d45441040c20280e07280d5039a200540054238110000800706810848005200035549030041d00883c13180e040703e0700a4210000f0f029007281c80900c0030504030310b00240410024015605180103100e04030348010010344075218032042e5251021100469171000c410060b801c2c3e10f6201c0c02c0e800c44402d281c1140d0b0703d45540ca45010416080c03170702e819081c880701c0c820010440d0642c8420001d110030700040c082d4080303214001c2d00029040850074090b41c1800ca44040e803001c2814801c5030038045001c1030f04540d00310307240c007080c031044980e074551a84505100410390000030200d01004106941d84d02d48102544d620051420790841c5112a01a04081c0140f00c030341d5022064070300c001030004080100400394000280500d00e400100100c046d4008244140c940d03040d00104007140c0203803510341034190340d1039044541c2e400c101d4100540e107a440005c5412460000005d6412601e103086c0410741c501d04030700103421a810b1300300198000c000010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 939950557 1250 939949307 939949379
    0xe16050306010e040503270307030b060f19121406160e06130608070e040905070e0105090c030a110405042c12030109090201022e05131a10 61
    0x3420b0140c041e0a28840181c1010b9440c1c55072800342c500b0750341200030007040c1007000b0031900842e00ca804030001c040b510300170b540b814440707039041d416030340140034984040710304e041400d0072101c20590f01050000d542038030b45440358001d00b540f00503608580504114000c6900c1c10801c1109901030032480303a002c0c03011002c0c0800944080000d11034140103540030301181e0503030045c07941070f20100d8509042c43e51903039580c8481200c5000c0c035a81c0c9141d0252521801f902801000150082511000c0160700c4260b62150104007170988200c4510100d4a020070005204400903080010ba50f022516160b0400d615000041d080e52054503000040c0740440509450940f00105600591700354080500188a5010340303c4501e440705000b03c0001d540ca03100345c0800c40e44200000b20482c500d5440794581d4608951604105503000b1180d581000e052802042004807030380c0c0047d0b1100d5004daa440ca032a50b1b03241c0c01c582c1389400142507003400754645000141217114038407d11800c2107260490030001101c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 939951807 1250 939950557 939950563
    0x50d02010f140f0709120311010c0c0803041205070204090809100f20121b01110a09030f0c030537111212041401080a051b0a030e160503 60
    0x7001d03408105041c0000720480a082038102c07600941026240c10f110342d42c100081e108600607500c40001d01c1c601c40d0300c103400d00d070b0b0241010808802c81802404000344d88403084400ca6150000901a04400c0001c20b00048194410200e0425a03080550070300a042c3c00040c200d880940081d5010300703000075243e02502d02100b003000c80d000135003001c84071a03545c0c410090902c020000700c502171402c981000e5035106000c01402c01c8504400454640d582610030718558850b000041c82040b6608008103885600c07280010f4030700c092040d43d1048183c91a54450159180010741c0c01c0e900c4041210000c80414000d102014481810510149048490f28170f80304c0c14001e20b03030146400c0401045000e002500b00f2a5030400340000f01c072008070002e82e00030b0b081d090400c2c82008079445600010002191a10101e0300b641074642600d03008050740d02e41c081d9001391682260031003482d84003800c822101c001c140003e8801503405290000e04c24070380040080ca000494a1050810b0303d10400800080ca010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 939953057 1250 939951807 939951821
    0x103060b09090606040e01020702060417120a02060f0a2315030105010305071502030408070f030b0c0307020604080f1201030c0801051e2202060304061e02181c0b04050d0201 76
    0x3074400c4941458000207042e01d80c000540154407450312031008070040300013501030f1441740381c00a1505980780e03a25119600d0410345001810401d009030517660b54929801d0041c3d0f01d54030003940180441d550313105451803e400c40140710141c2d0542d076814440382e0304000070300c00003100011105c0c0318203404c0810110400030705a100300d42c46a8101070040c0005030010414408503813100c41000e6103400340e12416810760083c7e070441101849002d0b0000380c40f0b043e04102a040781c0c09145040345944404204448600c0200c0f07000000d81c2c040400300300010b510900070030410120340d001c503003400350000841c1e941510130381c006e443d00c504482c424400c0140a104113030b040130441084140880440001c0804000000d0645a180030304d8080781000c2d03c52038650402603940244840e50724902454034030020035003085103c0d0f0a41c0302654a0030700c890719100300d64603a03001140541070006141c04114480c01c2c0088803034070300840c40708100c0c00100d15101060080f482035024282c41d4003d100024216088 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 939954307 1250 939953057 939953059
    0x20d032f0105061002031804060e151509010e010c0c081e0706030606021e01061a0a0801060f0c2301020c0d1814090a0e030a05090a05060705030f0c1609050103060b 72
    0x204c010600240342c0000855076a0074482140381010800240082e00510440d4081c0c020451048100700e0034140a203100500381c0c0381102c540000b2101a04d074880140168282d0502192001f0f208500560060042ea58100e1141303601100381c540341e8503020300b8080685500110b07120b02d811040000d101c01d0000318060600c03072504220b000d10b8801c2c02541e84810850901d00c2c0146986c84a0b4510030a400200107401d50385000c401c0c8000c9040c500341c4071b0b4006420000041d05900c004281c0a04ca07003515407003c800c0d070341c9003c126120f40e25480002d1050b24103d00c600c0112211181003000d0a00107000000140710141c00441141400901400d4038a03a030b211180703000744000c0c462100221100c0d0000d4a0035183c0803030b00e03502c03001510024030352400c11510910001c51004003103580840180380310300c0160b80d484c1140790744d01c043c00220700614100821a800c00d000e0b0701c0c0410301c40c1002c2c003180100c2c2000c60341204091030362804108090740007549802c2e140c10040c41840402d00a440030460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 939955557 1250 939954307 939954319
    0xc0a03020c040507021c0e19050f0d12030c0306030203060f10060e0603070507080c1b0a051519090b03070903170c0a11130203180d05030f04020d032f010506 69
    0x290003d40251a04d1b21854107074401244078a000d00150310441c000208680040c0000c0c8507401400d80300300b4140e00c2482158498075450010a650342040d44c00e180041d41e000100e681c0d503049030344043d001360031910400810035588840010160342d08108241c0113800550103c4946d00384101c00c0d0034643d4980d0009024811040041c0c006a1211000c41e035100c8400d15180340c480115160007030140c41001e01915451003444001c0400060801000740310500480c3d5a40180d55200140401c0c85081015403603524424481e0100302c8400d103000d001c820240c1c2c90141e000316203602c2d00101c130380c10580c0d41c2800981415000d108008425080d00c4001480c0c0200d5402c00d02098000d60b03440d8200040106090b504917174103021900c4203c04c0c0461041056020364980c94024000b110104403c42268540d2151a02000c0118041d90489005084038404013100d03540d103809000703455882e46000c4082014100141c1400102501c2c0d802140845c0c0b080c00700d210046498690030340740082d0000f441a9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 939956807 1250 939955557 939955561
    0x21503010303030b06160305072f0f0102190b06030115090504061d0c040f0e340b120403050f070311011a0d111c051f060308040e1b0c0a03020c0405 65
    0x140c0b46c041040c0e4182c0c0d01d490826034500039850032074001c61050031071054070240650a038000040c50001e000c940c500c26120450b4480d141401203a41e48440f10704030103403c25440300207001c50210501542d20100c00303400490a54a075610901c10250294003010902d65140140020840c450080481341d40011010030400c041e11428161142c610b101c3c0e29100c2c554813060105580056000340019041c1c040a031410710b040d102c449002030681d541d4400e05440c0f41c8028401c0e05121aa000e0140c034400c49044c0d051401342000403194080142081e024000244882e04404a80c00020607805200395100401e03801107407821400d440581d6030a004c00c08507445000c00c00c1d00c402c1c1c40720003000d80007100302500308002404250554040c003030201100ca11070803084240704001417120003244140103848149416000440101d480c503000041c01003008100803c9603406002c4119000400b0800e0b15541d41c0c50140c810003254005045c010300f503088201160245038041c40842002d82060790140064 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 939958057 1250 939956807 939956827
    0x1506030b0112020a03050105160908030a0507031101020c030a0c111002030315150a0512090c01020d05070302150a0f0605090906010e1902030a0b092206020d0207021503010303030b06 80
    0x30001405039000c0c03a545185800300355070780c004c00d800c01180c014008004074140303103c559011905507620040495191100007500850010440740600740580c0c503d030400c19640d40c00c035804503000d41654074540d000c1c0240010610248001d0004212036140c1d4903a2044a16043c040c9c940c03035112147c425001e4482400426070003204803503121004050700451907016034000742d5494940140341d42101c5c8007050b040300f1181c000000b0510701d0160460b90700907a468092103035982e03110061440c010703000255038007280c5000b20003500040d07100340180c80307080d282c00d405200d0740c00c02120f181c42103584800803043c0704d4a882c46008060841031300c010807140382800030076035100018032503a0700d014902c4000a5003403941030410482c40304803050035541d906203442c908028000c0c10b5521845201c001e808589098040c40d090040d400850030b40c401003880b542c032514029044000c00c002031507020411540145d60340f03140103421008203190345840354110f00b4000c0071138210b004000e0161100b00511324034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 939959307 1250 939958057 939958073
    0xf02030f0403110106030b0a0905061008120a09090203100f050f0a2907030807021203281808191b0602070807020619080a020a09060e2704150603 64
    0x8400c0e01420050f651402e18000903004000c1c517070000e002440171707009100c0803180681001d06854004c204603007aa848600c02308082c848a03103e0442035610400c41000441c08081c042c060800c21401d0241d81d07160b441c000801030368401c49160884140702c0300d0a00c80b5500d8000c43c040513020a40d0f4449203c840140030555803042030056003840401702d039820303a8009a00f0044c801c0d0682c62680e00b9121034581c50040c0c0218015101100980505a0103590706404c400a5910504601845c420300120081104d0040f0590442049580341c69040000c410301d5607282c9e414459100f40c5a19030303918100d85280d100d41020803144820800310f40d5103040003045081161611a030071100042e56210145410b07240c510554100942241e40404c4800c030b4555091a41803201000d03403201501396a40300562012482500f540e10040348801102713208c0d0502c0b03000c0c048a8a10054040c0003034030b4400c001740c17140b12440d035402000380e041d071400c020420036140c050340d80ca40d0503014103210340c504598038a10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 939960557 1250 939959307 939959311
    0x1b0609120a050d0801090516120b0a03050607020a03031104141e04091101120e0304060318050604060203010609060306080a023f0c0f09010e0421030f0f02030f 70
    0x8440c05104190035011541400444030140e402012101c0c0f5095040c00135003140c000340300d14a205840c02e80051280e090603204d8060900d01542e881010300d501b09080310083c100c0382c00c013a42041c0c8496011001481c01c0000138081d003416001042c040c1030a180007002c4d00c04044095101c910f0511007003145040e00310400240c5c203004c694001d0401034554541d0030f01951803e40c240d1243c10032640c0c0e0300384a000910a40802d4080c0c0e80c1d5031110540009000c29a0300082c1d03904610303030040104000140c82a4003501d80b000c80d51981100c450400d480d00383c5030841c00d490030344005038000010000d058000c60003000802850034107100e43c514000ca22038440300844000703402403408100700c8654403602106618400200240f5540c0d69400c01041c00c41c1c0c3c00801c0c0840c05910484e541c44025290500c1c0e20800c450004225400302c0c1e0904901424044001c0c1080320303041681526040103a0b641c503200c00314aa40c42c1c2e0000f42d11200c0010b0f400548040b100c845040f40e10401c18044101d1403500c1113a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 939961807 1250 939960557 939960559
    0x5090730050f0102070c03020405070302070b0f09030d020d0606200d12061707060e0609060d0e011103150307091a091b07080915040617060f211b0609 66
    0x10300c0009041982c100489010580740300d510001d51041002414004d14040c2c0b0b00959040089607640d0400394103d20030038002501074400800002c4900c2c98112015034000c01010589080505500249040c2c1c0c2003008040d142c01d07122582400101e50201c2c40c0701c02054000d40040c8503501c03c42c0740f00d442d140c9245201c1d081080300c0c400702001207482d8001c44020003031410041d52081140c02501c0d12407101c2e014000004800444404030f600c0d11b10700350b8100000042856103002004d800c0d6200801c90240c2046040d502d41c065100000d08500165101c0d018840da01141980c02004040c24a09941c10000c182c2c4e1401c02d10106100501040c0650f84505032920405da84406080e64400501e4045041d26401c0005403a001c1140420282003070342015039000303004178821200b070251801140607486c0050404103480110055441c0540e40060000e007100500205800208000d4640c4180860050400a100070318440003000300b5811032003100d03004144500c1d0340307000602d60700c02c0034120707 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 939963057 1250 939961807 939961889
    0x16050306060a1a03060d0b070203030702010e1209060c100207050a1101020102030c0d0b0a080105070504060201151a03040813170c0a061407290711010b0a09230901050907 75
    0x2178003030b88a9100c1180066088480d5603103d00c4e00c014025030703075071084030060015401c080310124a004006100c0c0100407080103c0c130305000310314043c0602c80d00010b205405074810328044402e40c42d014402820083d001d60301070615200b4034102640303181341500c0c0f410304682c07040040104116880c41941c003c031803007200100302d011844000610039480c6070800c407081e510740418003d107150480000c1080318141d070000c2c40008a00349943e4001780c7c4900c0351340400400301e2811030000071104001c1d40e0062103590041d04041c4032010a6806121a400c42400300354446080c0512102c00c100500030240116806030500e410400000d02c2025032203200044004080345007410401d4064070a90880701200340480b03039003070680c4401c20210041d110000452842d112360b00c1c115a041c02a8503200e01301034a8140300d2490418400c00910104090036034091007442d1100707000d0b40250000d40160181e01c000304550034400901030524200e6800f5001d08605040008500180c11400b0901000d900c1ca103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 939964307 1250 939963057 939963061
    0x70f180f1401050705151b0f030f0c040909060603062403020405071b0c06080c07031722050a03120b090a020a1b030906080f0106020c0d021216050306060a1a03 70
    0x5841900413000014aa07001e03403000b94408980c89480345109001800c0e940200101614803c0300328800d03030010346408441080020484480034031215000b500d084162440d10384c2d00c440800440303004084c2142d40d251284010800d00401e03009074404d543c0066180e40da054020385400b40014100c0c0703c002c0c000c079104d0f000141018024003110070030138190b807440c064a07000c1c1d00e42030920b4034240c09894045407000010444109044003541c1c00c0a6050b140d8207028038005240c91500303480203100041c0c0568118409443c0c91808082504e080c1c4504000d16064415242c00380c0102c2d252110b4658030b510744214550706544a014494102800d40001692070801e850212103001e00c0034135144200d0740c02c04c0c0701c100701a80442e0090450700740e075994141e030340c9403480c0507000220280716140c01a4821010441540783c40c4030203a075030030310050901807182c3c0c111601c01e04010f05400c540b940481c0c0300310204241c0c1014403255a1008003201c80e20800c17410a0898400c0b0748011039040411380740800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 939965557 1250 939964307 939964309
    0xa030c02011d0a2303071b03080a0806040b040e0714061905040e0604291906090311090c040605030910060b0705010c020a05030f21070f180f14 63
    0xc0b00c00002c004900d00c103000000d4000c8410394401400e401120b529030b41042c2d0f44408a240090041e0329604800035524014040d11074882c00b100c00c00c41024030807088003001000800e441c00230800e401030b0307407240102c0385040410401162100c0002e1401607040c001c0110350444003107a40744c15203c903602c842d913141078140080350183c0a040e04000c000200c00b85240403107500000a48200c409080450081e0350301c000600041d1a03d10080c00480d01400c00c01070308900508100c1c040e15480540112070380d0b1043c0900300c5001a0301ea00010206d514014184244020298892807030301055035030080d2800d000d001c40c089841580f054a00b04900070000c1642041c05025484440c3c0c0f54800134803202e600e6070000606a44450030440c2c5640ca0100d1880340180041030944541d074108010350b040c603010036030304415903103c0e0a21401882503504ac0405420400d02a903001340300035980c42c0721706a8101806028912008011000c5004114003005002c1040f81184180c5840124880400d48090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 939966807 1250 939965557 939965561
    0x30109110c1e07060e060301090b1804060608070902041a030402031e031c0b012a0605010b0309010e06010f09020f071e0b13020306040f2409030806040c050a030c0201 73
    0x1d84510090003454100c1c0001000c2c98001c4403150254001e407100c0642d035800a58090b00001c600f15005007017400104056003c0ea840501c4d0801d0203072106c0b440810203041514144004c603000c03100e482e42d1306404e0040020411410018144002c0304510340341c2466581080020040e019041c010300000020781151414443c003148030b101003000111403030038209130030303225080314007040b11030380c0b0510388012100c507580602410854103071903605019480742203000f046159100860305c0840d80d11031340000181c3d103100300c5008054108451b0303201d040988085007941c2c81c500007426142d00602c0103000042c1d00c182d80004032102000f0040e0740310700c80709840c0082d0062a030054442c03000c02d655400d650f0f141c07590350040684510f00018050f80c800d24182d580140340343c400394160340a2400100010003803040414090301401800c459400c1d0b525070800c519284c03032a00318007203441d0600c250425411841007a000b5804403800e21581085401c002e00601500c9985000c0603201d074400c031071a83c000c2d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 939968057 1250 939966807 939966817
    0x4030b100e07020d1d0f010807200601140619050c0109060612020109061b0b040f0f030203180a050d020d1104020f12090a03091715040b1f03020603010911 68
    0xa5149030061401807400fa44440340d5408150115142019407000c50306a40c4021403042c400901c1c0781c0f200b184c460300449a074400180361405221448264108010f60707000c641c0303240c49409009024135030401d202e07007654110007120240900018080d0b0703502811440d12401c1905598640340751503280200304603014010701c1901034800383c0b80c40404110310500d00301e00c190300c40c005e8031540034103640d030a8111000a6120300c1452500340030000c51300050740aa8a00da0414010014020b88100f070fa02c510b480511b12510460259200055401c1128102c0228032440881222202d1035145407001180342d0040e0740780024030590405400008010017450200541c03040580708644855540c1d051a296910194210750f00300f0f40d040000b503944038005070445c1b031250701d940c544116515280c4102160101c16050800c1c9002c0c0f144140c031100f46035803409114500820700c1103081e0429001070b101c0c610b906440341448415980090026880c1d00c1c0c100e9044865041002400c414080ca8800d014060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 939969307 1250 939968057 939968069
    0xb0316020a0b0a14060d11040e010902102d050913093921020a0306090f0b06030309010f1803080d06030302060c19030507030207020621160504030b10 66
    0x144810300201c25074aa0003034401c2914002d80e051103448040c06c20503803010000004040b40c3c078900c00e024060030541c01001c0801034200c00880c00e4000c9500140341003145003040000194410345000e0411701341c02c1980303440f02c4403a80340f40c0300061021000f070941c03003400c0c0114003500f61802d0828000c420340e800800801e1300035003400180c0807030b0f155000115403a400c005180c0704d2225841016407020140200c1160070f0040740c4c1003007844605501d142d000302031005a07031024074440f000003c110680200391020340304681c0c2043c402c680f4034120394120406094680207500900281840d079030446101d04501180703082c400001000500c00c10502d011640009188113808600b80c5040040c40c1c0114060f20711a80903205680e40c1c0c0b10740902280940b842c400e18a00581420007030705406648881c1e080f00c0f0b640303800b41c9441d04580110324283e000d00e0786481c00103040004002e02002c2000d259400581c241c0300a42e4500403034070b000b00680100e000c06840018800041002ca8a2100480000303044d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 939970557 1250 939969307 939969323
    0x3070509060c0f010c020d1701030212012309101b08090102040f03060e0601080c010c03180509010b0c0c010207121b17070303110c01050a031d030c03070614010b0316020a 75
    0x140c640c403ca028041c004c03880005032090030800d0480f0b034090445405d907141c00d0003c00945a103140c0800580c0400b82e0400c0800c0d5603202d08510705a0007034050413047d5410b17140d4210017030800c01d0500d80b07091412042410582d1070007444841c1029046408084001e0306d1428100c0740c1c9030608014020b1103158820002f594842600004200107900501151603d1105a0320306a982e9100d4030345686403441c59600003182001414000b0340100c0314601c0828810450004135a261000306130b40003001e0700b29403500c1c040070035031915900b0204900c00c8452028809050180c0c6051030341d182080c0c00280007030140300291311040e21500801e00001c02010403003056000c18024810068403031050307000175000240e194101419038a4002002e0700a080103a503180d1500780722181c1140280104081d0081a91982c500c0000384501000500b600c640c20901a640c0c82445180c01e0007100c2000d001c988010541c1c0e00100985443c0c901600d9100c4100510ba881000519204a00300080114000d041e04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 939971807 1250 939970557 939970573
    0x513060e042d0b06070503090d06020c011404210207180e0102040306150b1206010503090c03160f0e09030708030c040306110a0305060409050615130504060c030b100503070509060c 79
    0x52400840342c040e5450b01030308010070000741d42800058800c14101500f9131740100162181c0d81403c0e507a1190042c020600141050b105460b40d50039103030800d06400b0341c004203009120a10800076160185032031540070000c085400c440010f900d0f08218031804c1402003003102507045242441d0071001c11821030788021565592645844801494490003100d03c1c03c800700c0000c1041c0c0300f03060842d844203003a031144802c55a1103000444196200074506000c80c000d0381c100040d5a2002c100b44526241181e0100d05500d0034501e118019601c154800380505040d1001e2021540000c0116200903421402940e44d955070250700100074425640b0040c50145003a0303000442e08020b6002c4d01c2500c40b039075400c6c13105407038402c100416507100d00c1c1c0c0540242c02c0b22002c10817010791001c880760b004001800030101804085c3c03074142111000c4074180c540b00d03100e4821044450f85480f0f0886000c1c000c5032041090f2006290040c518003005228006004000a0401c10b41e07a4101c2030307034800900e50b41203466031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 939973057 1250 939971807 939971861
    0x3070311031906120b0a02070231150308030415020408030c0703050d030203070e12101d01050705070c1401030f09060c0215010b0706050417070f120513060e04 70
    0x29280c110b0459050510b0410082030501e0112a0300d604950042e1950354681c86004082000b075118800480e488600c03000e00e00e140c01b10700040754007642000d00300c400d4030000301d12144051f181d8800c240440031488d41c00910000c0d070f00300705036500640c0022107080a036100300c0d8a40000e02c180c0e00290302e203210100c0e00c4a2750160004d554002c1d00e2240d803d0701e100d0606014240d041e4002911450041031300f4020344411400c008440ba01410b401d4011960701c1c2d2100719580e011204c01d694941c0e00301381c1440c0d604490038824020980c121642d403604504d05100d40d19080c580102c0c0780103010341c002c0d50300e00e56840c6a2090704944122030099908010005d003a10700000100495400d1001502410030040b00c84100340d5085412940c41b162039a20700506551440003c1034024411038039100c00403140c180a080050160007614455240004107043d40d041c0400d50130000000d81c020007404011000b20440e20380c480500301c5480341000340369003648070002000b80030000450844401c4e2005c8054031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 939974307 1250 939973057 939973081
    0x302072a0609060306060e040f2007022b02011d03030a03050f13020a060c0204090f0501200304112205070327020d08070309031208070e0d0c06050307031103 69
    0x100e81c101c0d120004265503a5405806031107007486108003080280e0060305250405420458000070038220000e0842c25032404a2a201c80890b05100b03040780229180c5c0441c14801e412100c0940080d0019000704141c82c3e10f161140381043c0000d0411111048aa40043c03424012110a200040a50340c6543c0055002401031030100c900107401c0041c034001c2003140c003c0c820550181c0f034000d0050f0070b10a04240b41514508800e030422a0000d035110074000c007048682c6003048005100301d001180000d0848003003000c526001d4140f100010042041c08005881c002285040e0034058034a000b20701091107903d000c0001d081c488203a000d090030300300404c5030b074150b00009070040c0783c58840f08040341c0c4203110004000703195402074000e0068458640810302050241084510030b1818280310364695440c040f18204000600001c82c0203c0d0502a50380d0b00030104d291880d1055030448000441d90700c0c3c40c44001ca0381c0c8140020b1040002c00305040600c03070b402240b20140101d5000d83e89041400341105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 939975557 1250 939974307 939974309
    0x30c0f0c1509060c020901051e030a060f0606081e041109070e04060807060c080f1b07030302011802100e0f0a030308060909060f01090b180702030307081f060302072a 73
    0x200180d1110404205a40648100130300e107500904101c1c0399038244414801c01017080c4412050b00795280522004594003007010b09002840340c0300220b1045200c9007079400762815904a00f0900070303101d04000b2040c4410580d041100b10f40710f070964080c1c413141403c81d1101c41e203062a5400c0200e5000300000c098120040d500494801d403800c0003100d0761200c42a44134a031b2030040700c001885a509110101d010600030308104004008004c4c0b0704050303060710a1000c49030000b000c00f135401c4034200700706154080c030421005420700e81c00c50350300d580c16600003000000c41c4a148410301070740070146001c549030055490500000a010b00c07042c5134417410045d040701c00c200c4003588120700c00c800249990001045107402900e01525810039030342410383c5040540740c04075200380c001c140d0030207d5100c0d21903106a9402411180c01440e0340e41045900149401e00040c20110600039650001941d44043d804010448020b0300c0d005071200c14034644142241c0e03071030b035400f18641068064182540c2826007490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 939976807 1250 939975557 939975599
    0x9060906020c0d0503011505030907050a230d021f1404141203120126070927020a060c0320071805011a09010c12120b120703030c0f0c 59
    0x2d0700000f50490031201c5100074046d0715890304001210701d000c940210301554112401d5030030b6070b00b119190004282006000d078403802003054225200d03c030802d80100301441544007507540081400058000c1140701400d02c0245050487c2c100e9801c01d41031180107448d400d00c4075040090368880c1d070390f4290520b154100c43e903035209240c0b10860004250000080340e0420008038400c008903840c0c03283d6020700c4200401c0b00810600380c0c100c01e954200707042c00800090074460000040356002d500d40149004031886101e490700c0c480b14458400f50b503035840e001c02180c0307082c07418090340700c207a01d411541c82018812081c030078103040c1e01c40140c0f17401c089551803e607207602c100c8000131900030300d560090b02d00078030030b580300000d2545890010342134050090500e90018100080c442d4440c1d550182c0f08078084d0781820000c3c808026042010110b4010f2607008082113030020305451a0709405900d419480c4001018015110400820018164a154482608a005c180d556680c800c030061102240d000380d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 939978057 1250 939976807 939976813
    0x51603060b100c0221100f0203160203120a05060d05071205152505070506131203060602120c12031906170319090510120e19080a0309060906020c 64
    0x2058500d03115001001c043c0350020300f5180c0002065002201204051940c0041030142904003202c01542d4003900c050300c07149280043e40d0345004100300c0502141190344404540041140724408261021440d030040142180010b603900c402002903a401001c81006085000b441c82c00580b00b2000c3c00d89410756800358041d43d005403c075807500710896004841c20170406542c840032a803803003c000e0360300e001116103050903442c0041c641c40d800c1c5000c808440d0490b1400e01c1c01000002c01c1803c14200005010500f01807228070f00b8070502a403a0014041803840c1000c01062507600b20070304000300c14140d03200b02d103c15980d0924545040444500d031612900b46801c01200103100c1402000e41c0000000c208003840c200803800130b80041e0010031142c19400c12031400004a881e5903144118074003030302c00d6180c0c03402c040200c0040d131040e901080b01e130345000d40101c03184400384400584062400c0c0e034041906540d41240c1241039009003012500605101c0c5003441e11410003500b03900804640381c1601c11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 939979307 1250 939978057 939978079
    0x181f0212010504230405030906040312113d02030c0a02010b0303072a0801020423100206070c0f05030307050705100c0f0302090a030503160309080a050c010c051603060b 74
    0xe1000380e0f0080011005541000c4115012204c075007000941c0191203a03040d01e20303020062000400c0d03070300035800039210342c0c14000e4a66000f83d0020346001418030b1304005040d82c1100d1282400c0b411180303200a0404806604032101004040311489036400d120301d0f000c41d22414425003a07a00f540042d000c82002d9860000740e90704134030f00001039890141c1e000c100d4811440594804d8460201c0584102cad0444100c0748010801000c28000b4102400740c2c1e02141c010294880701c1c2d440d10140490105000380750410342e00d04042d80c0407501550103907542c02d24145850461900b1000e4804100026290740004010b11108552040c000c00c0c1e0980a1021a40341e4024140b040044035a004003200c0440c40c0e41c0d015a82c0b10f4003c0d005030080c00c5004103580d044541d245c8403107085511104003a82c004191060b03900400d03402c9003c6a0241c980701c2c0042400402960b1983e640350820b130110b0b4140008900000204482000018150700c0d6805010140d184d5914220300600303540380e4268460a03503038034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 939980557 1250 939979307 939979309
    0x618030301050604090b1f120b0f03030906070302030d05090d140a080a0507020c0a0f05010306080f12070213181214090d03020f03070c0806010902070803181f02120105 74
    0x42540d041c2c410080215151070701d0680080c00410041500f10b03088088203066811092945112031241100e5445a41c410081e00c040d150858004880c620322648285054a4030f035100002038400c44002942d02c1c43d174400c0d41d420700b6807079030051240741000d03603051004100c0051070101c0c0c0e00e2080b401d140c850100903222406601080d0040c1c0031000d0006503004005040039086801c10364000d112801a03070810810507021442144003508252001d885080040000d5645031040c840144101009800b50b000d04421040d220058480030080444002c9410300c1551307903403100143c0340300c0554800c02c02070401c2201840141c080d403209840248518040c0c11916008403568002082d000758040e141c415400308120251001010a41c11441550300410701420100010700038640a14003041d402d0b441d144400703240a505070402c0020702c0c0140f09074400a01c1e07030825a13801800e040e11000b0340811660240c0c0c944403600c04000501c920411411809072410780c001c0c03d10100592007080141c1e00e0308 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 939981807 1250 939980557 939980563
    0x2130b0702030606060f070f1e05011a01020f060406090812090a02040b010201150e0c25290a02071a0c1c0b0f270103030509031603170d0e030a020618 66
    0x341c000200c1c0700f00f0801c420008c0c3c40c034400245079501c104200c0d0307182000880c9200b003241141d03608807181d0f07550350507c658040d881c1d404070520000900c010080f01400300c900540b00c01c2d001c1c0c0700030541a1104403003410801d03040c090f95030a4503a008103890030328101420680c0c51941d0b400690007586441030700b5256501c10300907003104000b00001000364601d440c0714084020310040c0a24902c05d4148500040d41c1441c416040031b42304940001403d01c4c2403801d20040d015124141078081028a4540d1082d154402c0700c843d0f0300180304000107894900c5810441020f40c80c5260480400c0482010444000241030240c00304034085441e07200d420144000c0d020840303540401056100c62206050701043c0780840040b0100c28080c001040203109910414501c540280c004a01091011079420001d041c10007141507154020741c0ca10310802e00d03586560070b2012042c1071016203020001186541b40e441500840c1d8803a100e40e088a45d60b00380c1481c02500c840d01072b80d0414814002180c244480b40c400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 939983057 1250 939981807 939981817
    0x120b070e01030516201c0927020d15080d12090b060405071101050f2e0611010b0303072a08060c181c050c06041208030a02130b070203060606 62
    0x441400c1288134034004d040d02c3e80c50301c003003440b521a050724084094030101800f102210b0906445541894184c1400141001109401010040e00c511074aa000c502c0301c2c55a0003d004d414240060303444500c0160740020348050361116200c01c120400001c0c01d034030b00042412065030113a6840c51494034080301c06043d5003982c8006401100361001280152a160784451f8000340e550070048101030107980e0482c03c1d40c5040342c40750390f510402c10401c0800c1c41507501170100c514900101c800c2d4641c0141c081c0c02c41e80d182d030088008129004800c2c0702c10071000d51205211000007021130f92266558940601154001030b0469201c1d004021204030380c40100a0b150b088d0789041b4084c0c0065541c02e40b04007a5600000120702c40c2e030000071a01c0350562211030809400b070030f42c401100d4103485a428040d10380021990714601401c800c10040105001100803480c8007648140c115549440d0718075240040e00810340b210340c1c292080000018403103c90b0f0f0003059500d00c25410395a503a034031403040088a02403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 939984307 1250 939983057 939983071
    0x120e060103020906040b15071b080a15020f0c060a14072a0818030c1e1306092d290d1223030402030a1704120b070e010305 54
    0x9000180300528007810104e910400207031000800550709000036189010001540050b0480050450240485a410801d07185900d1100c034106900e880d110035a02c09209134040c180101e9114502200e0303109404642d00700c0842000681c4403101407d030991640d1017900d51404031391418490342c1c501c5141c400541c0c450031983e01c0307580550b07100742c00030929044011010b82c0c451b4444461640040c0c099405005090a20810044414000c2d030905103450700310303042184102d000c07007284c1051011402c1400600c6000b601c030b2001c03002500e40c02d0f0700034000c1500700b40440e60400507140ea02c400004182c42003010400a40c0c42245110100c640c02c0b035204900070560080705040504802807440c0500c0c00c0b03440c0147c40060000d0107501c411440c01124011440010300840102040e003403030716039001016842c400b50070b15504061380001c0e51001c0c91a0020710507107000903490145442030b0160380040c001c0c2c01c0c80e000103203110300d4034042600d002c039602404110b544601c5041e80d4030900c5040d1003084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 939985557 1250 939984307 939984313
    0x30f21091706041a090109170703030b180a0c0c0f290f010303113c010605060702042c031306083304060f05030606090c040e0601050c061006120e 64
    0x180c0018005113542c40101074060564039440c40400041c111391381500301591142d142a1503c11a240041c140c1d500441e0f440d10990303003082112403140c201e1800c1a0030018800c000101d5444100d0180c40e4500000409447e16042c03c01e001305100c0c442403100c181c01e11a00c035050150085824a40d415142a1803038032410380c00c0001800040d000f28031045a50740c00401704c465903442c41c05904107480b0320400350300d00400440c040c95a90001a070501a507151094000d0001c0360400c0041800b41c003548001031b2140b070300c421a10040800d0b40703511000f60184088000c1082d4425107031310343d490740a840680d0020031908800500349100c0e4803440e025500d500000c4001040c801c00585c07409010281c07060b2080002c54682071035035103500c01c0c3c200404c0079080413900079142004040c240750008044a024003c0441007000081d441e604403405c0c2d03145221400c110380c4035980100c8407030007204101842d601c80c001c2031282002c031060543c41211202c1d55040d2107800300b48200303010348405900300401a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 939986807 1250 939985557 939985583
    0x1406040c0510140d0c1202070b1914042f09130804120f02042301171c0806150f04032006070b0f011d01030f2109170604 53
    0x1190103250702d030001d01c40380750860000c1c107140285195948602d1a0008140e9501784c42d03242c4540041d002003402c26582c90031810003003035881e14281c0e280700522540d034140b1140b06002007803d9603840320082800b0a0560308581c60701c0d00e804d4103600e00705e81c007001544000d01c14071071707003004840900f42d031449002e01851001d4407070301043d110b140381c00c050031144440184804030b54480304e900c42c821803074002c50407489480c4031380c018403007110200e01025400003521240b18254800354480c103030446a105100b07089040d40f54a407e810510700750311307042e00c10801d481110501d50340210028024001150001d12901c030510000040c0d2065100710342d40341a01b0301c42000400c10980d003400c080524030280d0200b01008000280030ba86c80fa100c1240e4000c070322410b001081c0c0c1070000080c003420b001d01040001040030010020800f5052100810402e5001d840c4010042c40012410441e0408c0c0c035140c40d0100b800c90058101c1c0c007580a001084910f01c4503900101100240480c016500b01b07050480341c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 939988057 1250 939986807 939986809
    0x20d08041e05160e15210115050a14010203071506030203010903030506100815270c0424021f1d0f010b042903030c1c0917061501090812071406040c05 66
    0xd90301c40507503100301b8071814004541c000307080c0241210b00c5040318491054a08080400046006682240c00a8603070710580c0015644c00004032a407150300080500703503000c03041c00c2940182c011504000e40550034203031000308240e05074014600800007103860319409117400d031046503104c400326001404041102c0c514072590814540101e003841c10035940040d140b42a04075030982d01410b46420958a900140402610100560040c204506800250b50304d0004a80c000d41d100540d1f007186514105080903800c400d07006a00000c40032051603c03011012403c240d40369210348040c2c5071880c09500302842030446181c0351007009007144680c0001103003001e41e4141c0c214000301151140e901403108000a00b070080c002c000c0024100a44140f612600d0404c44c3c00a20010156002c0700c030184160300b040ca03a003070004c40c500d94014407225a01445041c00001282e80c500107038407444c150702952180424100a01005060850155100c00600c60451a001c0d5a40400b1a006800140b042c0014001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 939989307 1250 939988057 939988069
    0x303050f07020a0e04050105011e09050709090e0f01060609030812041e05060103030e060c0318130f02070c1202060a050901021005010e180706020d08041e05160e15 72
    0x2882000300901070504540d64045501c12000f0340041041070318003c104020080240240303030142c000364400e0041128202842c1e810310b8658000d006810b51140b0000e501e02348114041c200a00d10a002404140e102c0c000440d240c03407240030a002c986d4200b6601040c0c05019500400441b80c0c0501c8032840c000442411407109240600111611203082c88400b104841225046681d140910040d005951452030050014000c51074a240281418040a411504080243c030002950f5240400b2100d10b0580001e00800c8030b1540058060302d42070a21545200507400f90043c0340c03252a103131054075103500003002d040210030b1009600200c10001d0031119407103200900140707941030044039128407290000900741c50091300010b141a2040d001c00200309240d14030751440052000c0580141810413030003c0d00c0c1e49078a01c0f4a0103000342c2001240c100518030304c4000075003039548402509044149419611400c2158190b8080b4100aa000c1240707100c814810b40105100250155401045030505c05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 939990557 1250 939989307 939989317
    0x302060d0204030803190c0206070c020f041d1f0b0f13090c090b1f200c0a0905060a060e010905010c110d0620030402032d0d05072a030305 61
    0x10340c80d6002c1c40000000781224003d540501000b081d002500704407129140e08030348207800c00c00c0c11580031006024016030421080f008241e0151150710350100c060000c980a00b994660079a00c1d01a00710b4101c250040115a4540b0b4060051040d41461012102001514280c81010b0761003000d83c410340e001480d10007000c0c0c610340308041c030104401c0b04035107039001c4244469103c211529103810100b001c51908485801807000d481641da042030141200003011500c800200000c040b1503a6040a0300007001c00ca2403551100081540e48a0f03074031064080042c000c00d484043c01440c84038004641d15000e601410f92050041e5545a907080c9801c0045510809101d07090b0f9080c1c0c040c2c03400d03043c140c5810304452846402241c01140d4204c0551140240c220102602d140f220414010310005944c007007800f11500c490b034038205002c0e40a60365800c204101000110b1094460041103440c00c82e0008090007100b4001e904801000c8010207107404092140303005140800c00c603400c14000a4040c0340986 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 939991807 1250 939990557 939990577
    0xb1806090c0a110307030201140c120f1305011a090c0a021f0f0e1b06090306060f010512010e0103030e0607151d032217030d0c02030d051302041a0a030206 68
    0x2008103044030f10203d00f07642c03000e001940180d44503c418601d80c0800c2d10040d800120003000285400c01d12030a903030030700304083d110040301030100c400b141020100a005203580394001c0c00800180b4440d44115408130110000b84e03011701141c4000a5040140009a0364010200c0d00034104a601691200c0c0101821440c0b0400071941c8403012120b02e1107622450410210100040c0000a24107245080700580104c05d83d102e804100a0014152070120308030b41c100b142074a0666a1111038001620030303006000d419072100004030000110300c640e0f100000e0403240203468541d005a024028046544681603018060800010720041e140a41d6070001103683c0c424001d07400303202e1034811000e081d1b40c00901c0c0d102c1800c0070f561504a02028124800300100440c8008808030005000310b01d40324020b403140201550707901c861840d400da00a01c1185c0d25510340d80401c12140c03424039040e40340101c40d08400d03802185400800c07141900d031316000c0d00b901300d802001e020040c2d2a5600308103d030390000da0740e0303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 939993057 1250 939991807 939991817
    0x201020717030c06060906030c0402090d080c0d1115042003030c031c0614010810030b070f0f030e120f0f0c0d1803020a0515070b04060b1806090c0a 65
    0x700003400c0c2030410001400301c000b4580d5050071100703451070241d01408040c824092030b0184205540e0000d11542c1c002d00c01c2c0c0e800350b100c449690000c0c10240707000d00003824941e400281a0840e200c045800040d10400c1d0300d0f0070f00021030303403848103a44000c0e07486004034031a40c54000c2008075030781090120798071402c40354180d0503044850110317055400500d0a0001984045581e4040c0242280101450303944502c04106a0b8503000b008614145900e0649060014800100350248072042040d00619040004407000d400d011100a008085540d004000140c00c1034903034603a58400c2c080c0601d01c5a038003004140c00f03148680c15040c6544441000c0344101410003844641d01440d4001d480c5490103c0081c1207241d01038200504101401d51a080c0000f01d003841c1400166941420082030702c070b04ad80c50007102500d644460105100310400030b4282c0d15194200010030000c1d401c050400f04c015602e00600d01e0400a0989907510181d803c1c41d40102d80c000081c0d82e605210015000c0419a4500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 939994307 1250 939993057 939993059
    0x806090c1c1e0c0c0213151d040b1302091819060902011103030412030203180610170d0801030f0201200a0201090e220611040611070b032202010207 65
    0x101e0121244898141c1500c4040c1c5941070203400d151161001c010602e05000508004a50001d1a07802103e01d500c40d246a941c4604600800415051005030102c0750002d2802d001807484805100005c0703c04880e2115140009102c45218001440e81550301a108280c2900c46103003000c01c46e40c1000381c150305072142454810340002d0548007501074030b01901c400102c120003030000501205058200c1c14840d4000c005000014450a4003a0508061803900580301d0f10385100c0300c075910304820050440d501c41c8105000b550080392105d0007c07502002401e040b040c48440100343c60b22903440c60340010070040001000031502c0000e4040e090f920500d42240740b940541c0c1d41104401c810580d50340f40f035024484510455070000d1403c80541240c00c101200341c03038121841e141c1c409290814015499020320014100440e5411141c40381d40c0c1409030f982c1719902d5180c01419441c407006003004503c00c2d41e5000032410540012640210040d156408a100c09501664014880c07090200d04510078648 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 939995557 1250 939994307 939994357
    0x30e010320030907060f08010909030c0c0b0d06051c0206030a0b06040303121503120f0c060f090507090608031e0f04030809100206190f0204170304060207060806090c 73
    0xa20403086400c15050700740c803030401c82a40c0c1e14095458100360140070748164849000340d0460525411241300c03440c08540d150a91600703c6240f180208000c10740c540089021071140044030241c1413a20500d08104030f0300d907030b030000c02000101d115500c0701d4518800030480d001d0b0030030100440d2710101403140400e12860740004a075030759200c0da02c26000208203181c0c0d166800420b0042c4d00c0300d54442c40140d80502e0440c0c0f1081800784503004132406002155179000e00d0345005a69090a10780c00c01020400724802841c01c1c0d02a00e4856000c50f694050300c90080340c201c58912a040c2070760503100045d07090400a40005104400c0b021070650398540174030820140c4d814080c0200b02031031044401ea51240012400c0c49122403d03e041d400654214008100d41901c003d5441b01c40c1e00c0d0018008500c0503c450034030002441640c0150b25000085074500c00c08880000c010011170b0101c2e4201da000a42c0e5042c1110602001e992942c3e1143c0c0403004a00480b20030340140111610141007003000820002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 939996807 1250 939995557 939995591
    0x7080714040f0e01030210080907050906132a0908070911070507090c120902181909081e0a0e0103092a05030111120a0f140f090106051c030e0103 64
    0x39000f48030058000340180110300700503126500d068000e042118141c14a00000c50300d564050182c14014014500094550398601c04036680a00c80301c4000c0108441c500b1140c40b070b01440d0b41d0400c603541ca0b106840381a480c85500d0400445071a08003400c44a420040080090001e0581c00070320300c0b4042c445038020680600c1036500400501a000030f000d40d4400014002d1003001c01460603452600c0c1038040981c5407004502c4041e8407850543e81c4c1540d803032100d010514480145180080d241003102c404100c0d406c401001e81d800300c90051072880a40703000c0f070398051003414816400181140b02c618220750094000d080f420b88a09406440c010a01d2126a40f507581000c01d034000c617050034000c0005003002c0c07140c40c1001c805440c17554507010b100014642c0811001d00700d45095542e600030003ca42600341d10511a10308010003e0405061018403440b5000042d1002d0126500e40200054640b401e8016920510400f18540403442c205031400d40e8140d899102c401e06054454000400e184203075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 939998057 1250 939996807 939996809
    0x6280b090307050d020603041212020c060114030706020d0c0c0b0a03020d0c02010b0f0f0402091002250f030308090c060409020c061e0103080d060e0f011d07080714040f 74
    0x45190951585804020507140000903400180690403c102c40c0002da1600c000300c1c5d80c45504035820111030f02100404640e2021400f0321500058408182023a1318030020078128100c030900e0305800b030082040400c042d1644c0e818864034001d03a02c04400511210302461103980c055020b000e4185042c3d40c0c6040c408165400030308070301e0000741e0011b4851031100c45840342c0c001c21841440204140e41c1400086002000d401060b5881506508681c1c6144e5032950108c61004001030000e802c500c02c04038010b9502c1034100c041c1381407080000d24486e0507401400f080b4084a01d43e0128009082c60754178283e9402c1e901400890041c02007490361001e51f1100d03402040205000710005a5030100d80c8515800e080d0090181005000519444903007190258022030640e60020341040e603a0f445001c8501c0100402c0e80104603000100041009190b440f201c2e16041707800244407441089000884641d600760308480030b00101c2c09840c0403800346803248007201d00043e1503141c018070b0682c8800c4010103206007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 939999307 1250 939998057 939998069
    0x1b051e0c191a0d1d0607020718270c06080a050c041a0d05070207080717120a11100b040c02010504030c030822051606020f0c0607020d0218010317120628 67
    0x3408125040304d40070422140c0c05100c5202030f00c4542d00300003100c808000091030084c0e001e500d82680700446100d106401d06074120400d280b1442e800503240130b5030f02d501144a0784021500300d000140010401d070003414070911949880b42d01c1d2500b40a4040100000000c440b68500d0050010820140c411b202d10303801801d041d00280403140c50f00c60443d2801000c1d40043c512107088007030210b10703c000000e129440312420b403000b40d21075682903070071194003026004003001803181c3e4601c0c603c030500651060b40d2a050a0310240300da540c5110090b400e81e2000e032402000644010003000219116900071500440c480c0364855a294814010032080203c601c41514650019280c00d220361035103100810051030a400a4560406c0581e2520703252000c04d40c406006200000e1070008640da41403140701200e60041c01d50741035240740014800c241c102400211303004510301c014642040d9100e03040d2801c5400c201c42000c19652046d042c000e14001c41c410151802d04044902c007442d11302c9080d11006040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 940000557 1250 939999307 939999341
    0xf0c080604050114150d02061e0a030615050f09010305100510120b0109060813030210050a0b01090519030f020324341b051e0c191a0d 59
    0x50703009140d10340100c0c09084402c483c0580c019202c640c6d150599841c006031740442c5d45030740301c3c1514080c0c4036800c802c1c40c03044507100c14002000070240340c01d40c1c0007106035040c20715a4910000424825a064403c001d242c441ca25014402c10801303621030b4000541c003011b00516130340516900c00100746d58403494602e00021a00e070045a24151817580b04d000d150180c24601002c8903172501e80c024120394805011007405003054180d610601d4020003103045001c06542c3c040095203080340c8928000d180b0805000c0c0016843c0e5000103143c80e040044c0b1454050f40c45880c180c3c280385a440b0301d100240d41004a03018040d403000400d0032501841005198114210105400d01d01010b800007074126480307001d1810145c0960b105144c40c80d0b4180c0100c0381c10701c2d0800c0002400c0300d1a818001c2c1d824440010414458a0742e00c47c4042140d0f1101e144800c0c55204070340c1071814200c20040e11345450b014140700340401c902c040080a003100b6600c01403042001d4010724000034451008181c0d110790001d403005031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 940001807 1250 940000557 940000571
    0x2150d021e07021005030a0e0607050c010507111914121308030301080a0204230a0e0c040501291209060709050103091a0c090d060e0606061201030f0c0806040501 71
    0x1208900c0100000766a1015480c2c0540c40d800900410001040c1e0f01c00c229012001a03a01541d0740c2c00002c1850602c400ca80700362074020030040883e07100f489c00c40d90a500b8140802d041600034001054400e003000054805200b07008180e01158104000690314007280da10344200601062100500d10704211205650328070881c0314040c2c002740c5542c8610f1090340100b004106403080800c02d0001154100c9003c200441e80780b9081089200200c5190000003011090003103614155200c00c4500c00700e0070a41c0c91003105201040308641c000d00c1200a18581b07001060441e0300400051595411010b45042c1040007100c1c007080310020807106007042d54004d80900140175046010b20006000074a41803003034414980d0340d0b4134031620f10084070041020050108580140d450150303103001070050881400c495840c2001809043c0801c8070410380d01802001c5116400d10404450380160743d90f4141c0c5160f461a40c3e2500107990021003590b002c0403451004c19640003c0c400207001e82d0080c000402e0300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 940003057 1250 940001807 940001827
    0x30804140a0614150105130303140712030c0e040e0c10110f030c0601230f04020c120304060c080130020a0311010f03020c120c0c180403080a090b0a0902150d02 70
    0x41c606044000c2c10301401f406450702e41250308031a2010790360f0600c0c2c106071070900402d9000f420f00840d0300052202e8250b03123000c2d00b8541c2c10361200e9001c80382d650306c427041d105a10342400100d47c00e14640c01c100b900102034105080c1800702120212840300c0c42c0042c00500128022820703c0300012003202c4039000065903800c4008104280c0d405440b610200001940c00001481d010325411400c5900451241d03001c03510b81d07900c507810354044201460070389225685480d500f4049030310858007221241e140643c01d0b1152845981c440f07060302c0510719107545046504000b598800020030340800a0581e25003000300603111104c2c90b03001584103140c2d907050703900c081c40098080d141018003034042500c188180a44c81d50005003a0102c001d10381651a03844803215035480c00c00b0b40041c81282c01c004150300e900c841c12018002030788154003030740c0c46506944400e80c50f030003a0f1b560804090405079100c40440e25403c203951080d00c10034030007880f112651840f400001c04a0700303c2c104a1102c2c41c0d021440e40a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 940004307 1250 940003057 940003081
    0x130f03120c08060616110a0603140c161e0503040306020726180112020705060403080c090904020f03030c07151202160602030402060c01090c06030b0d030804140a0614 73
    0x31141d01e50410310401e240040c08581140680b40780614100003003450704c2c09001c80701201224108002d0400b40b081d644800e0054080d0026070303070b0700c03482005c2080001d80c050028402d866022541045540b44540c0d0354070f4901c40c621602d09024000b1801c81e061400244080000300002d620481e40544c0343c0001d414600902e51405004444032001c6060006000a920045540082c0002d0301a0890350291004036640c0203280c181098081c0b00141d0503003400307000618144114400e0355020f10517610850b05c4040c40c0950389a0640041001d000300e401803030600f550004100010341243c6c2040081c8410a242110075840284980c61111801c42c00361350219900808185244041d4580040c401c082c0b4007c0070a10000351005a001c004541150750f1a002c85260420540013407220107000d0518400e00707402d52203001c02091030080d1405072070614001602c00303540c05446036802940c0e29250341446540100d191b03807507805008261000500180f180f078224982e8074128010a14000dd59560 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 940005557 1250 940004307 940004321
    0x10080d18080d0c0b15221808090d030c02030a030c060507050c0a0803130215180d02090a0939050405090d0c0510020a12060e06030a0605130f0312 64
    0x1405800070b04001c1c0315550880d2840d80219880100b1588660314401010740b00510042000d81c0f144915541081e491540d0501d02102c5581c18820841c0700602480821500000c4000070318191040c40070010754503007488000805400384c24800005003140c1e001a041c0b20721860308401098a08040e00d003800030030704c602a448491810325502c1c01000d032440395a03642800000402c0244000006902d28111020302035800d517002e4406402d1106176a0441032075001b10700c040c4e090389403401d950529807911803800300c40d03241c000d00043c8894032800d8411024040314801a81c2c00d2804c2c09200b0700710080e004040100f10320640080c525200020003000b286459030340300ea88034600302410b010188a01150611540c1d40c5401d103038051541d81c4c5400c5007400652100810307118804246168110f41081d08401d000d21048410000607440c2c2c0084810614141c5030130344c0591003520b401000600769482541c120007234500b00c0078850516540c1082c3c2010150003180003d50100207030070f1450150040003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 940006807 1250 940005557 940005569
    0xf15080601060e06130e01030807050f030a050f0d140108011d01020903250902180f120303060f0a0e01060c170306010c02013002041502060c07080310080d18 69
    0xc0400e525054006101c50326210034103221381d400040e07900f07040001e6560707540140b14180d030600c907540e9070381042a03850700581e10a803100d00a941801d1540c03e00402114880710b21910f6503030030008207444801c00354011450002c03040340c0c0d130100f00801840c454201802031408a0000c90b240010000c4000c6000c0c140e0b0444e03100da80180711200040e0ba010030450302c0100c2225551155100b501880909100c0940c0406862403000031808500812491118040760741aa01c00004000c0c8105018407181c464102600310780003440031a1240c07400708034071000c81c8170013480c0c1145d0303980310340c00c28610703001c2a80b0401c00710311194011402c0000e0351081141d000518484a811407403c80c0020b0018003c101c002030402912040074460020484001e00301349110000894094000c408070714029031050062280c840d03002d00e4155501e9100042181c03041d202e4044071800d00102d030759064815000030703080f4007140a9010022038011010004003244078601d645640d40314405481400c10086150040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 940008057 1250 940006807 940006813
    0x14120414070803031003021c0b0a150501020c0d12030b0616030801060c05030405010c080d02130311031f0c020309060a0807090e130b041415180c1f050d0f1508 70
    0x80416074a030f17600301d03081300c0c3c0580b03c200d11070344084d0700d06041040d40c02d00142915049010301c110050541d1000c0782c0d0303108051704203100700c1d1030310300680e078803d541508644d0100c0c11440d518001060140643c82c0c1d0011809e01040e401c0b0014006100c036003205290480145800c0d5880e0305041c2c0c0701510341d004203007909004c00241d4250716404d84a02c104d00585040c41b006100c01000c01807000e040700d0420f0304101045490b110320f0150583c0c0440c0c14401038800108111a000441c50089407602016980d604000202c4c105408a000a00741100400003540414001e50859844d5070004001340c0b1215a9540f83c1c0d03140620002d05020300340d411054522036040c2c20007403020400c5554003c0d013a00306200303940a5685280211035075000d8460000c0c00d00600991240185406034200d02460392008142c90341c10504a07134a9642042c2c02150b58012010950782c55492042d40c410b0009000c10b00e803143c81c1604000b168819510001e0070207058aa440f0b0f0300420329480c3c3c1d440d040c0581146005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 940009307 1250 940008057 940008061
    0xa0f09051203270d020f030c0a170f040b030a0c0306060f030222150206090d0f05030903121302040e01051b090301020c06010801050412090503030a1412041407080303 73
    0x111503403500840c200c501c0350480000402d00945120719000395400d2071500100d014894101c2d184c0d141c2500e500004094454052044041030011042e110b2406e02e61000341454000f6445824000c1c08102002811001c10807201c0716001d4118020005024400d003440e80d68200a00200c1c1121880b080300310805107440e5050111031f17401800d01000351818a005a2241403000c2c1100350300506903906803074400300100c0003918481e41e440c1015080704076000d0780d00644d15560215143c1390007a041c3d50004a9456200400c070780500b0145030400190412242040803004002c1c8414109989c2005188451410070003140303040d0203001c0d07030001d642c8000d00c0700b4246820480c100c540900000103c2d003201190b0710149860940c10703103030410980300031607003203595500c1408c3c020001500c0079150124080c0c40d0048007030040c10000304843d0090300070f501c2c140211101b101c1c00f908500d8103c10551702003054180c0100c0c500b01840c080e1f40204094488803146101280c030f00505980003070510340041c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 940010557 1250 940009307 940009313
    0x1090f0203120f0f030c0d06030302060106090911030601052b05061c1502210a0c080c160b0a1d0606190f05040902030106080d120c0c02130b03240a0f09 67
    0x1c0d1341c03e030000301240715100d440790800552940540100c10100519024001080c95800160f042c101c441c162506981c0e1901c0d0a0441c0959681110920b0703041410004a20613502c41c0c4002e042c001000444406104545001701c0e90800942241409043d00c0b41c042c405c41d07180160914220203000a10141e12401d640e0310000340000c00c0c000d1700e0030a540402c0fa8452300001005000c0103181c04001481c441c9880809880241481c0601800042c2d181e400034131a009404101d4641005e880741c0e41301070444d10360310b9030074080c0024030b0170780840c0c0c84520032085c2c2145402c102a841c407007500a42440e1400b0402e00548030300081c0150328603000e1038070800600c6150004a000da400956021030142158000303c0e02500056000c4c0590f071140c1c2e0510740325a54040e028900d2031443e880184070000040300d04035807a490400c030180d8441c031601c007440402030182d4080422000080c0541d46447e098100c03540d038210400d094903801c05145c01c10000b48560034400c03452a400b9039902044140c560307031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 940011807 1250 940010557 940010587
    0x270a1701020304060f0c08133e04020405030628020a020a05061518341205060f09041a070e0406080a1a0411060a2a0201080a09020f0301090f020312 65
    0x18020140b0440d40520b0742e418084400003400070168402d801408069079141180040d4103440c6c0d241c480e5800e500707000040ac0c60240201c804446c0010010442a1030f21002541091115031001d8207001030380c000000c2c141203d0010341490180380d00500040c82d92400e105007404001401c605600c20189942c2007656960018032180301c007104082d4031b0395a5a41c1d9000351402d00c449081041401202c072074200c11443c01c0200281504940e20300040b00450780c030000c180c51080d0350607507201c03000781d0711880d050808034511503009014114031341504414203040504030005940440004410000c1289a420700d40070303a0004042c0c050090a8990780c90710780907c04941510040e43d130360300e02d1010900340322010700168005180140324560b200c00d0544003901840365018031035038090a201030002841d01c40e403001800d0b290180c496410303035076411000c3c07401041c1c92041281d00808068180815442c24860300c1ca240340704840c004418001c0d8010107140041344492421044400c001c00a41d00c9050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 940013057 1250 940011807 940011811
    0x2180a0521030c010f0e16060f050c01090b0103050c1207080303011401180f420c240b09071704020406080a0c090b010203270a1701020304060f0c08 65
    0x540a800420001c58103182503100300000f02d001c43d800c200d8111241105c0d94458000c0c0340944084a0000b00120118410a40d8034420400400c030303080a280d00141c0a1401841c001c4108400002c074142143d51301e001451007a082591950b000c0110002c5900300745107840b5042a0210080018502e0701a5003541c0348014014561000c543c0d4040740c505034010f81c3e0b62034820780c522250340500b588404891000c40701c2803083c100402c9008a102068a42501e8481d640182030b000000d020090f0784241a883d0310074108503420800c096036a030300814007094040c4c1d4070350728112154411410203001001a102c02031001c505c501e036104103220b21150045a04501c080b03e41000045554413800054000d10099000028a004510f940e20800c9000428401503503480380c820403140812000499681c0500000d070450400312a111080311005200c140d0340f0300304c004200e403c0d2a034941512a070240d90740032031400740d6034000c010b2100700400d900403010031403811003007084080c1c0c0f2428010105480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 940014307 1250 940013057 940013089
    0xb040c1d040c03090807080702011d0916050c1516080f0f0402030c04090b24010509041a06040305100605010e01120c1e0509011d0303030714190302180a05 68
    0x14510440e02041e0003130300a110010b0b0020a8280c035205242000400c540c441c250407030000c2c0e080030303c1d810555904000640701440141200c000f680c7c48101d03500f40140802e0785101480428000a0000d0750204181e191500e04840308517510f04255070b4080e59030264824035014090004104a0392910103911a980036900c0035030568584c4403400400c1c10b00113a580d8103a04981402e54480600440840c424080c3c0340400c1440d0043d49080352000c86000c0704404180051810001c0c02d640d407506800001064203c4080b003a44000e40100003a8154071940c02110360380c00a5001c1450901980714550080130282404040600c089000820300002210601e1982d685c9042c4070006a1141300b00790311416800440c0e80c180340030208091700c10740240e40900d000845c2010b00031904c0450401c03418018102500550030342d15100425960305c1185001120740090034041e00d40c02c401e1100c62510580c805d41c4005907140e040c0c0f0350045a624881d00181e0041d106500108015212217216020b03001c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 940015557 1250 940014307 940014311
    0x3204060b031b0a09020a081b0705060f1e040b0a0c02032a1209090403050a03020c0d051b0f0d0e1906080a0608010e0d0e0a0e0a0b040605010807020a110a0503010f0b040c1d04 76
    0x2041180f2385018060243d0240c01403285004108a03a0021102c0038007400004160142c444540516030410800482e030042c1100d0300320000c104110629001012070844500680e42010314180707042c3d600c03060449811114400e18000d01d250304000340140941e250049603400d20f0044400003065542801410090400500060b0703c4c1e0118803a50680c2c071086010b8043d2055206541c80c01001354021080c40ca4501205a103041d00300c2c100040c5000d0088910307006001440c00960040d04c000c100307240c180e5040781d950701c200340075442c0c0c0213008800780c81c1e0340e1140c6180e4100102c42e0b400b1100c458000c0c000607850504094040440007030855040d4410346444840f2202c01c40c08500c903141c441d881454446100810b0095400b60b03038210b04044081500d0400003956900c0044898501c1a0303541d2015070401d030030321404a400c80d0441210343d0406021080d00990701e2003c2400c54038a2980405034580c1c40f020f030446844c0c50700030f031000c2c9410361030820301031031f281d0b1480b11082c400d2a10051240d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 940016807 1250 940015557 940015591
    0x141201061e1e031b020a150606270f0303080f0708010305032209020720030c0603010b0d090213020c0f06062d120f013204060b031b0a09020a08 63
    0x61184d040140300e603001c004800348025143e140603507910b00040d0100d0701c18003402c00482c441d0304641b082204841070707903030f2781110700c1200203e90310003402601c800c1c00c40a20008010174401c4403010b48400a502c81e6070f8222080c5002000c1902c940c90190010b07003005100801040403c00c000107840d007200030381c00d12184803114200826408c500c03a84c4205541c1d4000300c1c50138203115a4420004040b004071030a080082001000c06d48c9801d420600c403035000c27005000500505903841f000c0c20f907010501d50001420700d10390700011801c803c0c0f506102c0c0b8468002900c104904400d018500048070340c2801090142040000210060704e0803e600c1400400041044414801000259001080501281c4140084001071620b031707460114019115030a2160ba403a02c14981501c0340040001401d0b8852001101c500d10840c0c60400345c01681c01c9a25451a540c0a56081c4843c4aa81920310070800c01400d1020a001400c1c0c46070380411481441031208144154102207240da000703480b03913602d00c2d1034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 940018057 1250 940016807 940016867
    0x5010503060f121509030a08010b0703120513110409021c021908012004120f1515090e03071a041703070513080a050703060507141201061e 61
    0x46507000303140a500110f28421400d02080c08a1486800008030420480310b03074455900a03500d224903001e500014044200402140383d1100203071160394070902e0f10014007030042c0313000400d840c01520300f1002074801c00510010081c510b5440c020721102520103001c01400f0750002280003038003c148a440700206490b02003155241f60304031b034a540c05031071403440c25600c0e803c90500a20549000e004d65004c503040300e000c11450304081d1011500170741140c800c1030156a03201d904e54070100310111460007082c0340c4200400068010180914a50000c0c9200301f07241040440c250360800d4200000c42c0c104125550104640c07848940c8035a419502c01c207031685892524160700c148110101c000d420000c4107000401d0761090090503121400034941c604152600d202d00e4a58141710401840c0d136103e0a03007000000c220360455030303000079941000c1062101501341004103620030803800c1656214540140a500e40202c154000f498040074081282e494825015088030701c4c00d40403408009000142e0124 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 940019307 1250 940018057 940018069
    0x20102100e10020409020307090503061003060c030e1c08151e060c0a050105041b0b070311030c0106090605210601090f0219020d121b1214100e100303090501050306 72
    0x2042d00b00000319a50360343c82e0716000c000d405c11358961000508407503001501c1d00c0c00080e44c900502380401c5061207035241d40c0d905001003099110420625444002c80c00b80c0e4041449055250300204a08441c001e000203801050020000d02c0758000084101c10b03140359494031405071010345101d042003a004d07260100024840d004540c51481c01d440b585110008105064000300d014a100b2a49180c0e1508400302c400d4850b0514050202c00c14014014513010a2040041814884684007520f261840c1178844509440140d0401801c1c1a01ea04042000d400e060300e200c112440c00261400321110350690058603084180f0400039015213400000719003880590481d14100000660705c2c42d1040654400794480300ba5080500c0400c4480300d90801510660107915485081c00e003e44140340f080076803d0758400c00940c1c03902032056031204d0800d03000d1800004c40d4019840414180e000515040581e00c0146004110b0300029061900400019400c0320501c800e0328000d08010340c5a41c0c604020031a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 940020557 1250 940019307 940019323
    0x31806020f0a0222020f070b100b180d080c010608060c0702400621020102060105120c0901270c120506010e0405070305090c040e0c090705041508180604020102100e 72
    0x400b83e100141b00840426900c0041c1041845a180b04409568807400c03d50122014416150104010844035110480c52025000d107840001c09030082151b064407034003400e802ca028240805c7e0b554030400e01060404006503580060780710000e40c54908240e02140d650741454046504269481918684500846a84e90070007220607440c014582d0800400c20301412080c031030700700c401c55660790f0f000407044000d004c05119034041e002440c20744d00e00070910500f0048030180c06c550b801006c0034203180c2e0703170b401c5445802840c826102518a0062442c1d40b01016090070500b041c09143c801c0305481ca5800984148038001c038000001540c0d5110001a0b4140d18200d007520361003841c00f01000041605540520b01941c00f00c02201e03160858802408221000e06000018070b501c403070614501850200041c56029682d80741260406503039410035034031150001c81000104030303040100002d211802e03181c80305000710f00005020301d00f0a0780001c0e484100303004d2200001a11030844000e40079040243c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 940021807 1250 940020557 940020619
    0x4080c01090c03021201020901091a040503011109040c050a02300a1715090105132a080f220c170106031505010608130519031806020f0a02 61
    0x2200580741c41c507014066441c240800c030700c511611080141440414401e69041d2081a100c0c141040c0c20520500c3c0191803034601140194403c000104041c0c82c203009990041c2031402c2c81c0d94543d504902004241c0d07210803076803801c108080c014000819030000707919070111402c0f401d00ca0440316242d45202c0310703005652030303800d0b100c0e000900f130000b141c2c4030001440c038807110072050004c2d41785d185050600200301003009920490f09001407140d4174008850400c9501809000a5207000380c2c40c15410020040b0704a50080ea02c0903d00003000382c000521541c8600c0d403c007440032a15040402400e28103001410341040e40c80c01e0f65660400503401840300107480741e10300030350202c441c1a0495002c3c140b90300049414540d010049000d01c091406640c1c1a101c803500c0340e810b40e41d0740c031558625a803040310307040e541445014a04290b0041400311501058020340d1038035210f0b01017804243c559400780c0d00070400c65205841c2482e10030404103020704810343c115650240d8178021410910200c40400301071b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 940023057 1250 940021807 940021811
    0x19050901090b04030f140405030a0b0c041d040c0801050f04060b1513061b11010c11060d05011d0f01120309170102040807080c0102030301121b03061d010b0f01050304080c01 76
    0x1000034117410058440c400c03a45039842c00c0b0b50600c41d00b03c404c0c00f07001d01c0c4100c6416901510380300d00064140b0a2840d484560f20101909140e9201c20f02078061503044040416525120248801e014218503940c000c1e001e20002400581402e108100f04901b00510141c0038613510802180e0356540d00403440d66494007510340307a4644505401c0c00800489038820076000c601907001d4410510081115660419002711442190540040054590000d0150b04454203080c103840a402943d811026000000344c0c4000014603604015a039510840c2031003010314001031000030081200110700100781510070786603400090050519041d140d40505d604001040140752000103c040015400f42c4126642e610884154a60714400681c40d0046030507410f00603001000103002c1c0405024403286958440c070034003403000f241410b40a00e028055001111030984550114980b80b01740707800302005141c544020402045014005510002456203481c1400f1022000405100108094407022164403001b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 940024307 1250 940023057 940023061
    0x403020705030c0a0f090b0d08070804030b06011d0f0103020d02040e041a0106020d0c03210605130c0215041b14010201050c0901050319020915091819050901090b 71
    0x1039240c11550082500034070400d69003c40601d441a00ca4048511180c4060031890412400d400501000c940301c90304580e4884c1100b0014001034011300e005806000c1550312107003980751605a2900140c44a8100002841c5140380b090700701c001e0960040007142d4807214913031408010380280c018105424911840410300144060505031080d03c603510800c40c0310b034600488010b010901400f80a894016402022819021401003460b400d05c0e900034108600100040b0180f82400b8124005000c64141c0b202c07010003440c200b112000c907007031841c62018001c00e03860b03c0d0029550500c2a00c5044a07500100214007480307494100a600d0441c8051f040701c406484446251411100100c181c0c010341c41d100000d03032454101ca00f603c0c120300c0c059442c4c82c40c0d07803604000d1f090326042d10480106402c0d8200070080040c1d4410424002083c040748800381c9908490042202e000000086c00c00c1030710007001009413200072030209183d44444050001402c1d22350300d4200303004101a0b4030090001082c002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 940025557 1250 940024307 940024313
    0xb04060f080c0301060501110613050309060a0e040b01030209060d091407060f1b0c12240b1828110a0305090c0109030302063d21030518031504 63
    0x35007582e00399041e002070000681e11001101e45504001403081c0c96013150021400ca0b001c455000c240e602e0044044174100000c09000920940c49181044023091031041152600d0500e40103401c80301d2000d0034114140160312010403410b20032503058100040e42c611850042007003080d03201032241203c200f1100c001c0e0f04c558002e0130303180d200340150003c1031b1000c9808403d07a0342004a2146103901c0310f002c0d014181f820503044405185100d00302c4007c0c601c6000030902690700d103c0c41c1408003600e1002f203081d590301424080c004610071154244200d9403400c20520740104c0d43c0040392500000030380c400c4251029618001031083c0106202000000140c1d520044d50581089000d5801841501c40c188516001551524030500c80140583c1024000034901c0d03440c505440e6400510f1103980780440d124004000000b80b929a42002d140117860080c4082845420301c240ca00029451892088071940c6004c0c1c02c038011070080b01c1d4802d00010342d12600d41c9062144060b400030f9211000701c1414903103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 940026807 1250 940025557 940025563
    0x90109030c080718020316030221040b06120a0512070f0503030103060603060e010203040302210d0e0f011d06160c021008040b0c21070c0206070c1a0a020d030b04060f08 74
    0x100c82d1850319280400107099103021171003200d0166095032110f01d040729a202c026006508156a516084070f189104004183c002d00381144c81039100300c2500a0b41e25080301001a50040300b8909101c5901c409090740006000080000140040d00c07103c0d910b4041a180215100c41c0c2032200500a00000c8000410020603800c510190f911660051002c1b010303850055080f0701080394040c00692082c104498110040e1000049010070300306828501600306250100380e402801540840358050120440c088000784201c0c1c1071006040c0b03010712044400112032365201409850041c0e682ca12081c4002e0070b80c01001d651850a03400350402e04d442298040240c42d00000321419102d11800700c00080103450000220f85e000c03500d0043c5100e4040103003c1c66074040400034030200a2141010054015035148030181c0500c5114031b1440e29039504090301d182c05a03100c20b002407070464007445040c02190f0045050859100c0d1841c0006171003e4100000380a00440d6004c0441224115408a08086c000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 940028057 1250 940026807 940026809
    0xb04110d170c010c051c0b040204090c08150301020c06180703062406080c18210f15060a050603090705060a050d0e071409040c030501020a0c05010507020708070902090109030c0807 79
    0x700008000450000f002074403180308850320050588400e4070486c9607516a47e00100090300041c10060a10780c669101d94116800d1641110209014200700807002c0f1000039059203550058000303504040c4083e4030b041c0c2d1000041c0042480403035129006e40d800000300f1041c4021900108240544c90b000705488034009401410300010030750404010840500900d0005e00440c40c0003a514603104914100c40c48070b000b40344070035500000f6901c5105458041d15000540841e83c40080c000050b0103c41151418141c85100c200e03400c40e140420005030b170b07102044000c0724415607007960b0340c0d66000c0005091100c0e0790000c903400400031400c1c4066982c010003802c001001c0034000c01144150700e11040c1d0f510418480c00c00c004203074442c94503060074034074102ca4000b4803542e114240c03c4c4d05c80e6115826604101e0b043c41c001800c0321001c2c41803020900038036400c28482d0004c0d005282c14900007030784900440c00780e55511034002481d40034a074403455200d001560000c901f044c0003500e40442688508803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 940029307 1250 940028057 940028077
    0x103021e06210f0709060309050f0a1208090a0f0605060d02040507090f080f101527060605031302010f02120d02041d15090a0902041b02060901090b04110d17 69
    0x160ba00042c106043c1810a5001e8036a0351140c065403854081e08402402003070404840a0181c4030301c40301d01040800420560390311038904080020b00f22200102002c00007480030a1a522206901001c41d1540c0e140820868100d6030114441d0340b0900480c0000c034200784020740080c507100420000e04c2c0e1100c113001c10b5600f0712007440042a5140700c9196a5803000c0e44601047d000107402c514842010b6001c18107807071070f0714110390787e882c1e80b100c641c081e182c0e62040303208a01111101028408500d44103082c0a40702d1410544d045080103c0800c1c0101c5d844000241407284090a902a05000708440900302010f01c4540d070350b404c4040390603000b0350402d106412000701c48c40c400c02101110783c031482c0d202c0c00c1050544403944c00c031001001211000a00011804c41e9180e8040c00540c440c4d012705045c3c10740340305901404521051000746890001000c003922645050048030019801c0c030b1025130010340150f0392140f151551400203074155940c44005180415412015003002e5400000d4015080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 940030557 1250 940029307 940029367
    0x60b0c010902090901140f060d1403040501020715050a0c06020408010608101b02030f030403051b0313090c0905040e010222060801060c02062205030d02010209040b040608060103021e06 81
    0x44884c40c2030300303803141581920040003a43e00080c4c8002040c1d0030107607103d40300400c000301c6454545c403081071107115078640c100103402c0001c0a0006503010031044000700b40071702050811245e0044d0052450003201403c1303003080082c2c3c02d44018420385405031005041c54000820080c0e41e149059517641d10600c1c500d41c0c0003414803903070214175154060704500c891641d0b00a58075107101e1103004001c591004000700d05001e010f1010b01080e2180c0a0003841490a82000316a0b910140c3c03034801050b0481c0d404070041600380503060181681c06450402102c0007900e011411100d41012203019014100303540b201055911f50401c03c0110f08019003046800f1600d819403241d032103240c1110381003d070304400381d0056001c0054901d00750701c003400300e0549a0340b45000340844c0d45607000a030400304070032201d0006039004200e683c03841c9003601c903050321030004075420003503a4584950251210385c1480041d00c100140350035200d00c20b000b40c482114802004101984d110041e140c880c0111a494074110f260700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 940031807 1250 940030557 940030561
    0x203180306101e0801050c040603050f0114040207080f0304030905100e06091315080f0f07140907050d060f03200d1202150910050903270103060b0c01090209 69
    0x81008600c90340201d00450045107a5400c103454011400800c021080110078103c0c4000783c442028843e9501a005011031140c0c0c491500320018299074014040c09080194480104074100d60f064900f03420350000d903070260304c80246080041c0103004140c40c1e00002000001000109940b04482e402510011501e00f600b48050b03030700454540001640c2140c02c00001c00c6258010b14044c54003590740da41a240204000d203a44e14856480c0e030701c5500c00c2000744d003d200c0108010b14280026002060154000c007240b525140440c591201f0240142e401a000c00c40031864261040003128103140541c0e10034403e207582c48560725401d041d00e1100f0344040160100c560803040110051010360307480109030001034a02d940f51214a081102107450a5200d410f00d006035500c6500c1216100c0c4881c280a080d04241c076603080020303244020000c0b14150010410403d40c045040c044000384410303514406030b104260001a03004003515081041c902601041e18003510505400003283e030fa2090b030b0100869 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 940033057 1250 940031807 940031809
    0x418060603140f0402010c0809030f010b012a08070c05060309070503010533270f060904020a181104120210050306150d09080406080f060a2105100c020318 68
    0x4000035070f2940078520042001c1000b6600c18000e24044c24042c408152500f1000390010786440e40c103405e441426515070520391a1907807c03400d007074084803c0c0c0344110700103454000002c0c03001d01e44039002041c0500204015042c414044101e10140101525196481c01d005207001d6403285907110b010722030741c208400184041003108004400503120b0900002402046c0c80e103100d1580c1ca69034082d004039131454002041c004a0090300c06a104414140075103003804e0082c5094404000d0015002d80001000e2000503160440003000703c030403d103c0d502400d0440c0c0310740c00141070290000e80304803a000c41c0109920050840c659803c0784200c81c0311003028407414054a890000300c81096120300c0614010804508103c010b08118050410006240907950786500305500700b50000c000155482041040380006100d032030350008402c0300c40903142490302c940301042c0e40ca8084190107645820040f10b0402000f0001036038601d0368000180108460414020b42e00d40100304a01d09040900d0004521 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 940034307 1250 940033057 940033091
    0x6020f1b09010b07020310050a1a030a210e152d09061806030103080a09060c0203030d0e0f0f010b10050c030301060e0d0b10090b1f0807050418060603 66
    0x4460080d010401d00d070701c0c06054003100d810150060341c05002d60303050032074685400e1040d9485085440400a001c00406562182003070710f01c3e182c94029844035405c0400710304105000300c10742c207144001d103200154082003202ca002c2c8031903a41da00891342840100c4c034686000e0180103881070202c041022003d00788200c0c6901d00c070800d4416505407041210503010b0410300006c2103201d01c4110300c05004240e1304041182d83e40f0076842528070140204071040a56840310344d83c001803400d0f2401c0c201a060b150002520391103540700301c107169580c0d90580401c00109210075044001528140c4022201208980b8003810340c07080c00504c00c501409409440501440c19901c0750701c4a40c0007141580e00741201aa007820300301c804160b001584410380000540d01c05010f512601628403507188040c600300d44030050700e00e410b82d2280b260680e5500340042c036110300c9165450414500c1d0140302520741d000184d5091007650045c18a1036007241d82c22014207104c1d04440101c8100f9601003050308103443c00844 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 940035557 1250 940034307 940034353
    0x5220c050315040c09181812020705030304030327030515071e090b09060702060f070606090603390801050f0a0c08070f0e090103030810090509070501030f0209030706020f 75
    0x10109001c00c4061000707400403c4945404103d081b00080c0c0181540701400003400720304001c4031420340480451800c2070741802542c000305000e074019070400e821903801a010b541444080d405680007888c841140d034004a45980007540c11000b602c207041c40003450741c11741c014100d81010105002c0000260002d40b01c10b448a1907460559494100728240402840280d0003140c0d1158880000e1107584050b984400007840703a02e9050751301d070f030390b0301c002d0700d00f41c42a692160300c140c480c0e03442d0400400104030000340400075418001100c041c00e514806404031455400e0000e04c0b05020302d41000b066051055215a014071510079049070641d580210322000c0c8d51810400d40006907500c1c000c150114010340d10041401c2c5e6500307240349007106c00400704040f44001d910980006101d241807080c40b0014000c0344000e410501801d002c2d6181c030b003250603035900a503c28903040554900c46000501d600b6070541c1c00d0b00d000207040c0e41e06c05070b1303a040003980d0b0980c030a1417003954003855103160441c00010031010307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 940036807 1250 940035557 940035581
    0x3040c2301030e0106170312070216060f0210020c0f060c030c1b03070812010e07020f030f0d020403060f020304120203030702071202060d062301170105220c05031504 73
    0x600000104004401a1070f00b102c0c00e01c070642d21501c002c107203008554210758081d402c0340300964440403103a800d0004048058040070640d044849403110b0035000481c035100380c07403807414800c114050403402245070011842100610504c0400d4003000000c0115210801050071001c4900603121200c9a141d18032056440039000602001105403143c0b5000720b2800c01c0f10b0b42c806403030030140c1c9078a401c0d009a20410142c20946e5509006020f211264400690030400500c020804d80700e9900c034040e96403259040c1454804c0b000319001e4052101e03501110051540460b082c02281b401291120103908184c3d01100d0300c074508000041054400000d49200d0035269004086852401d120013200000d0b0007400e0781c1020003040b014840c0c0a2034080e180003000d0301403802c0300441e581d004021240e2114101e00f410000e036801110000800e902899055480c00c40f00344007859243c41c072070b85000b851303d00a11183e030b040c070400c0800c0341d8004001c2d600c00caa40050451500c00c40d00108003c480b07070707922a2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 940038057 1250 940036807 940036859
    0x31103010905060d05010e010c08070f080f0619030506060306061e130b030a0c03031b152307020a17040608040f060e150412050f04030f1104020f03040c 67
    0x100251901c90b04420b030000c0000d0002144045070391121400d550052201820700d81d10743c0703d0780d00403607404209558440d03e01e103485108042c89607001049404054901c1d488180340d01c0104000b55075045058103402010030700010b14960b20319005488903001c80c3d805100c1c0c000c00340020204c0c01c2903411400c079048280001c00805d41204200807400e2185007208a1045d41c900480750703140c40c00c0114038543d45c007031400d91190a1451900500d4090100c0d0480c010080c61040d203000130b984c540040f0510030340da20010800224480301f03d141015004918071442c061482030001c4030b07801207007410540c0d01030000b42d03413031002a41c0d02c1441e9100340c0c40740e0070008805200240114500384580100c1510411011414001c0b9000c0c1500d4800100c032490190341c002001d000400140d246401440000c2c0d0a050f82000609540c0a007180a41d20002e44800480c9000004004551000c43c100d41c500800442d1200b005d080020b8945c1c10031141144ca184146401003028401c030766109101400e1070f048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 940039307 1250 940038057 940038059
    0x15080405100507141206030714010e09130515010e01050411030a0513060501141810060c0525090f09020a14040204030609050604031b020108060103090302101505030c0103110301 78
    0x50700601c40181100c0801000390403450191141c0001050048090941c9070580d0804104041c208034899000f20004221000050110798000f0701b1504400e101b15160030090ba902242030300c0001001c00010303c1c81c040e200c1038080007010407000f10b050311107081c0802c03426a00c0303806100480d41d001e01c50000b00d46040c40081c1c8084003a4000e594002d44400061610f0841c1c0e99948080e142d0a030880100c40340400004811410411000c040764401400440d1460030614482c03014007440b401510208082e0007240014040100040b414490390710642200700d186a5403401c50040440c01220b8106041c0100000c80704080d0050368005a001000008218039110000d54000d2041007065001a0280000808518a0f2054481c0d90340144050502840c061a000340310802010016a03d00800b00400d00942d03130005403250700041c02c0c2000680d40c8002d0070140d15103086080a001f0b0141810042c0c450300c8200c20501c0d08a40d0150100c42400d140240190280e920800b503007146e803582880 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 940040557 1250 940039307 940039333
    0x30b0c0f091008150105030c07140f0d1d01020f100b011422080d0f080402060702100f09080d120b0a030f0f050705090112030f2715080405 61
    0x51140d080c100c08098548190391000c500402e07403650750034000c00c000c0703000c01c120018403281d010344d2940c0c01d190151443c038040e61448005c1c001e440d0090300d0210484044444601c007040b820000d41210400c841e501c48400d90020100c04070700f1003117070406010309585e10440d40002089004103584402030800807034181100c078014050200158100039522507030318600da069100410b5070410007881048100c150900c8c1c3d01c1d803c00c1a901102465100f4100d080f0714951081250740080075505d00614952950b000040040c059080e004e540001d20402001440d500100c1c60225001e064550740c00315503aa1140e9525100c02021400c00b2451904115240c0407903035211039107690300100158841030b02d940700c80c90900c0c1c01b4401102e107400044032a45c2031040c1085018000c2c40203d07000c0180790f0510811a9010300b00510040520410f60240b0070201c3c0111440385481c1c00320721041d404129031145001050310303036200f203c04a0b0800708010744c440d40f04208c0a44a50341160040040144040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 940041807 1250 940040557 940040581
    0x616201e01030c0207120c05030c0d1e0602120106051e04050d140f150703060b0a0909020d0e12070320060c030c040e1006020d030911061c09060603030f020304030b 72
    0x104140f000c40c050030b03c000c50a02181d113441e041d2580100c82214095041c407042c1464202100e410a00c42e45c9103444010024580c54071403951144034010b00d0080441c1882d1000103030080ca41e00042035112000003262281e80480035150303281c60b044014083c1a404100c08040384118011644c112580e08100c6010840884001407035040e6041241c145201c58508030b410203041d0300d2000b008031082000d0001c0140d140c090500600124800740b03240c6804c241014180002070710401345150380118561500d200250f000110180d092400d4a05004a6128240036070348240802c83c040b40d90181612500750842180300781c403100340c100400d00ca44a414242807140c00080c820200884100004a082c8021101d601e001e0048002843c079101e00b0104082c3c2001e1000442ca0101031516401c240400e14240c1c01c0d2940601c29904a60399130604481d00e82d41a0140120381a410b061000080400c03e160744078004403030103581c0c0e08041000380b0804903164815488040d207002c0d000004100805511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 940043057 1250 940041807 940041821
    0xf080108191a07030b1906080a0506031e060a06090204030f021210090b01050405010e101518030c091b05120a0603140709200d05060616201e0103 64
    0x502d02182501002d10a640d80c95041101c06200094599188002d40d0038600940740e0038000800e0300d030070f407142000d400601000c0000c0860001a440c1c0c0041241a00c00744842c4c4100e2158098604403035200c0c150350303a5075900507034280250b40e181180000c1c1d100710500c03c1d00d06490b800411030407503a0307194003040b042045200c94a900c902074007007805011030041c800c1e0111184507040c100c0181d81b4040c20403040310416408403c410140134104451000600c10b035905440002013a04821301c03807ca412a1080080007010116426060020041c01407040c030210032240225410300c00000c6000c481596101080f0500d00402c8041c00f0540c2e00c3c205420301c0300d901001310b10001070700c95a00d07240e0451a0725020070050594000143c20721840055000b07012010440d6154000414800041402103120711215a220fa40d5141c2c00f0498a13660403040f104034045039210480030032410b082c0005800d0510903514050020022007002904000300c0c468148109500000811600d040041d00a8021 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 940044307 1250 940043057 940043063
    0x2010c02060a17090a151404032106080304210210030e010b060703050304060b0307150309151104180c0503040f030c1209050102070b0304080304150f060b0a0f08010819 74
    0x44199203400da00642d4060f54441d041442c0180758400321401c0501d10240440521040c81d420904804031070142c50b1049500141e141c9014141c0d903180c40c20340c0b144043e200d11500743c45806d110000400d58000409402900d0800071011940c000074204079042c072900101c001d40111800e80030140e0107000383d010f03003c941c84060000c1a07901d921000a130241c0d010007030071000319502009000a220300c070700c11070f140354805500034081c40742050148941e00301001035403000c150303c9501c490108414802076807a40300f0103003003c0c03040403030110510500e074006002d00c500d8140a03081c16009421203024104001d030700f81c0c481038510344458443c104018518074045d003c1c02a0b00300c0180004c1c0d201c2400c04280e000310fa03698054181071500081c20107180d070b84a154912001c0c000d10020074408000c407500a980040a940e5840c4060000c3d000f910041444c0810203140c05800911400d8400040c03c0c0542241c0c2c40d080011a02d00c01038906410a0242c1d00d6103600690840041d1b0340ca1070300d40b00103280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 940045557 1250 940044307 940044317
    0x60a0e07050d020f16031d0f0f01030209040903020307120e060306040c260a0e01020903250e090a030314091b011803110f010215280c08060901060c02010c02060a 71
    0x615030b104481ca0f617005010003c07121400d50241c609047d448114140280004140b1000d00a035020005200b0014601c103940f20701140c20301c408440e80a0381c11105110400f030000d111440342802d001c0c2d1070380c21041081e100302d824040c034482c096200306801d0704982d00007400d00d804c40c0c503200240002401d5210b5000c0a000a0700c1c400103801030608455121061039598214492500381c0001d0103a480240706203155030300510100d80142c0d004541a18001c5101008000710341d90741640f00da50740042c4c2d001d8143c407090001030005107d0f01045882c4182c1c000d403400d200c8a03c0c146000f8030080c0003200c203002e07241c1000800d401030281c884a640000d2205150800c40701c103102c100c10380c1d03020659204071a640b000e10406021401c1116100ca0524024009401030800d0a80340496082004105188002290380d01980782c0d60042c507006007554080300d04108c502c403807007005843c005080d10f10030f10440c80130000107446131240078000100b5506946040341c01c942035003400350540018102c2d0341442 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 940046807 1250 940045557 940045567
    0x30a11100c0f0803100b030a0f0b03010209060915120108060403020c1c03081b04080307051009030804140330010f08030a03020309030936040b040f0501150f060206060a0e07050d02 79
    0x2021001540c0683c0c2d101c2c0740060305000080318800ac598146001e40d0207a40180900c9072036a4070318050350007540d01501c0c0500907200371459040c0700d128070342e812000c84071000004174084200007211440f4500c640c003120759010612042252506030013403016072004102e200680080d2040300b1468002d0040240750350340c40c1c050b42e41000260030076045601135500106080f02845010806e160001c0560704040200203002c0c1c03401007400130002c001420407a01c3c0c28404119a0040080b12200c04840022001c60500f0024420081803030341e20020705500e5420000c101200280d44a03421100c2c42c00045180201d6484190040c0d000180a425913002c00c0c4106403040c3c441c2c00784002c011900040c8030805000c00740030350b00100412400403061440720f50410001800b919100780d040f68108026201e181300600c0c1207400341c0b00809243d00d04030312861001920000152020042d10940d40070766090781d845006014010500340308412242406a010413070180c0524018891092510000f500d41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 940048057 1250 940046807 940046819
    0x3240307140d140d020a030825050a121118040c0f0e040e3304021003050402040207060e0d030b04050f150102031e1b0d080a1802030a11100c0f080310 66
    0xc00c0d028590000341e0000e6168104062340040c3d61944075810b00700f4958559485080c58251101c0308019070f0174030000043e0003c20711f00840c034a020302106c046060044c00705031032840300981c10030560300c3c404c0030034661680c0d01494507000d40c007040c0e409542c3e0300b40d04c20142c0600b160300c1c482d41500c03542c1007135491076090090a018005611a0320408644022620270041c03030719020a2501c4040d03082c1000e480521006035038413549003070400ca0300e00c2c0100340354845000050007403151001c020f01c03c40c03600c0080740b50400301240103079083d041c5132010006c0c42c2c00e44042c002030b144112104228030017264009400b848991462511001c018412281050041004119071281600001c011130070041196520035011000c0300180102c104050b00e04010718000c007400e10130b0068488450030b5118004001140f40c4400c4c1d042885800800321034100d03034036081c4082c80b4070304480b00c1409401070882c80242180540c03104030100d83c0c01010001c42c1105611601b1640d00003421041100c00406800981 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 940049307 1250 940048057 940048063
    0x22080301080d23030a020f040816030b0603070308031801090213090b070e03030304120315030822030506011712210105102a020603240307140d14 64
    0x2924a000003040c00d1400b24001820b41d80d1100301d030b5214008000e011404160044040e80c0d00301900740005a10341714804203032010707070007503820150852043c40c041081c922410425001281d016160105144e00d41105050f03d46415000180c9550f10800104450b010015004c50084c0328a6000084854107680001d07200e00034070f010041c0c0c10ba203800a42040c440d621240c1030b003288040c00c2c9160945071000103e41c4070701000300042e2030100d890400c04110350081d04101b0220b143c08445c0e000c06034591415180c40c4d006248480790040030a890700da01500101910000c0c1c83c1c0000040406a1824020b06400d01d0b56100b1582107001e8440020740722640000030300f030032901c50420544510045604007064150590056210700fa9031403c8000301a006000042d01c0391080c1c941440d00c402d43d84480140912148000303412a40000410400c1c3c0040210f49440c1c001002d901c000d0131700e0340c0040550b58030f03490040c084040f842c4808241c1b1407414204900034140700c2d41085541c071030304600783d80c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 940050557 1250 940049307 940049309
    0xc06020906040f0e010506070b4b150105090909071d0108190209060114090a031208010f0501120b1311041403010203090712021f0c0210031422080301 66
    0x3040e00d443c407041c41942280c984403030140a080c0c9001c0d0810400b52641c6c40740d484003402d80380c104c21855041d010a04044900d2858003840d540c0e00e110804000c09080d83c00c010141c3c150980c24086001180b24a00f4444242169100507540d039401d0a07a0001080251000503082c5820340c13140400000b140c0307040306084170302030704007040c0703041d00350301d001c13081400d181100ca586540101d44060080041c0e0b02c078010603410001c01c0c07a01e41c4c5404258440c4007028420a42030a5209050086c0003080103c1400e031030500400c541c2d910780403a42eaa010000000704180600c0c0d02244a180000d410f01016903c040d140b4000184a06050b886811000b4211000d071150848c458100003418001c0c24001941d4840401041c2d00840c030310319003000310b6900c0e101c2c10701903408103200700d000e584199994140c07006080b040001440c060307002c0d903510260031121080003c9000e0782c03000403150451801b034440c41c06e18480019100650341d448042a00c030307190648815041c996800301210011401c1200a14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 940051807 1250 940050557 940050569
    0x5030a0f2a030c03122120030c031605040b070305090103020708160c0f030213090201051908010e0a0905060f04060f02180a120203070b1c09080a11010e07060c0602090604 75
    0x450f2a0705500703021110481d0b820310841400003005291500300e0801801220803d1b41420004155200e0b820500070034584400314094410040184070719030132140f00841c0141c1088090f130380c3c0d070b1044000507950340c0107500c80c2c0201c910040c040c01c1c012074010030080c403203101c0525005180081d10b0b03540070301541080d000030100050f50f5002e4001c20001038940c0018080c442141c1040900d10381c0011040b100c60810403500f1512550070000316401070091303076503d41402071424904008404002d00c0c80300c09100303420402d103130f64000c600d0a145502c54204030782e800c00c01402c190355030340c0c0070302c00c3c00c2d88003800842d03216640d079015a241801e944082e000364021025450f0f0184210070401c4000c13001034000d00801000c0001079001070f680020200c080702c0841400d00c4e15192488600c4100c003442f212003200c0142841c2c4004104581c2000828a0380440e03254500d00d512a1141c8500700d5203034110300745090780b040ea414000329000321074580025106007009850404408003050058005610030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 940053057 1250 940051807 940051823
    0xe0f040605060405090a031b140a05071202130513060e010222121203090b07050304150b030c131b0305070212130512150103150605030a0f2a03 63
    0x101080003200e0041a8100e2001c890a0181c0d003081100c0c1503c1e1401c00034000c0c1801544464003000030300e041c4086070200e4002c0b44041c0c9001000007800c0c0c9412202104881da4090b20402060720b221010711111240d401070030050214100c980d000d402080040e04000c01311301c0c50500750000030854001c0340c10383c401540025854110b02c03000107016000300c1a04001402d11600c0a000d8184a5001a5031403a00900710f41c4280500d040c007500105203401d00900190360000420080701d8102c0c00940c0150f1160300a4044071952520203001c82d80b403415510751603005140d41071940c1c1351451250300f22074840e90380081d0211401c0c0106040c110064113260100341c6403020008001d03014401642d2103000503042502c1d00003512441d900ba41d10600595120b0711080d00618200182003114040c100011603958503035584a040c80e84024505180b591030b1241806008030b000e040c003064541c0c9103540040e006500c480956600d0b00004a84c044902e142c030500c0103140c09a43c01c14102200941c02442d034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 940054307 1250 940053057 940053061
    0x3020c0d110706050c0303070807051b1c030b030c04020306040b04140718030c05130219080f09030c0709020c01020c07030c06020127030c051f05181507030e070e0f 72
    0x1195041070110f82c0601c0c02d115083c085041441004004c40e90701c45268500110150388028080e216405400c00b0141400444040c2d04a1000001245d40c504070080c2d8280b80382c030010000c1201a00c58410903980c25401ca050715428501300703a005107800520040011a1514000d03001c1002c454004c1302455141c00580244140c090700400684804546080f4508078030b400d64035111211070051103403d0040c090740601000b20746d450f40c1911054480c00e02126207220b203c8500414800095500c00d604140d600082140c401000040b0b83e41032030503e000c0d101c038510789a0290001d4001c0c80c48850a55000c220a01d4211000d000c00000740d44615a00201350b405d01c0d00003802c542c960141c0601d1075860010510b00e802c00c6c02882c440841d407514100010321142d00d4558100050150300314105140d030300d2840243c031460782000b4440c80c07800e00d4000030044032100c007550314004805031040301c00c071120220b8961403003604143c2c0903a003910210742c0881e9944600545004046030350b04087e12038901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 940055557 1250 940054307 940054337
    0x1509070506180f06030408040e073f02040609120c0b0c03030a0b0402030105090613110d0c030e010c0801031e0c1706100303051902070e090f06010e15090703020c0d 72
    0x10f0030381207400094500c0d81c203520f095074413030302544500e01030404202d40b80800148454030590414202c80a601d24110f020b242d100a1a03400807840020645c0350070003946041e032014a0341c42550101c0385607a489118051401054620415120009840c45100301e480800c0d80c400002c01440d00e0103d0b00011562440c1c08205407046462140f01184141d0040004201541d520003c01d40c021608880e41c01d2101d012903803100c01000c2600c075242015002050607905400913601098005030300340c0341448005101d1550600321a00071588902043c0300e04d0040c40481c0391180400c6408409103608451000641c44010140ca540d40c0440140f07001a0080780078200c081c017034140c1040c040c03c030001c03003103081d43c3d0064128003800d9481600880d40c0c101c4140c62520800c01400141041f03c42c00c1d9150034100002070719080c8200c00c1c0650b5100b1140000782c01740c5050203c503c21644500701d8114040c1c4030301040410381014004800701602030040c1d14119206001017110400592501030b1440f9105d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 940056807 1250 940055557 940055569
    0x70605091003050c0307030e0a06050403080910020705191713230a0501122712140405011b05030d05011401090b0f03090a0f0302010e100c02150907050618 68
    0x81c01c0a04150805081c08101a06032081d41e0b040407860401048100c0303200c00c1c0310305d0136176520b4010700b0141c01c0009100a040d0080c401d5801420b02d403003a156400c0b01c1d90180402da100380f0800074080d0780000c1c00240700300d950a510b8134007644078051b4210030300700280d1600415040188ae070902545000d03001c000a41040b4008000e8a074060028007001d4030060011307080f07103c1403280505000c08601860044403050b407141103090301d4030b0a0810f01031040302c42012040c00d5a4001c58403500e1018096414901070031044041c1030b036454250780350604040c01100c6104a601c0000800740c0d283c12000c00042c3c01b40050801c0c2d50b5a0140000c02d036140445006541c0142c400003814000240713070901584400c51b040b0303054100741042d00f81e039035181d40368030794545202c2e40700c050b02c081005841102050350640104e03900c94448400c66000081c1001c2800c111802c241650b00035a1105641d400703060000010b803548840c1c0b28054914495035140440c07620761090b2500c580650f0000d0107800c00746800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 940058057 1250 940056807 940056829
    0x109120803060103200910050c0d050706050601020705090c130e07020a2a09020918071101141e0702010b0303030702240609062e090303020606090f0109150807060509 73
    0x18900c143d2081d1076940303200128810241d10721f0198000c86c1c14460754500480403074603440e0740041120001a03000d07c0c01000b9400c00c080413101d5506000210300c0c0d540c0b00041100aa400c02403409103280c813075040414040d40303c5140300c018036440040001c1d0750100200994468640d603009441b080040f03107480201c0540c4c44600130312902c1c0c00e880c204a220300f0526080181d90030010f00599481039100040c414100c444048d403460513140c410809100d5000000140301c10b00c0d10002e0102041480328880045030850345940e20001c1201000b041d00c0a416420f078100000d4000000c690000101182c110b40c000c5440c8c00250380802c5498000402490b502c40500a03409403c90090600f00c2c0001d142c2071026103581c2c402c0c01031130983c1c0040f0810040807200f81c0e07080d000400303508070b011001030308101c418403085d00980a80000240141000a2124429400c000c4213413000e80c02c1c500c040c0000d001e503401c0d00840d211000e001103007810341081000301800c115161140c440740c00b5000c100e0f2200320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 940059307 1250 940058057 940058081
    0x9060210090c0b280f0908011a0904080909180d0e0630010f0311040506010c03120b06030c2d0702040207080f120f0c13140109120803060103 62
    0x140141410108451414900035070300c1c07034241107581d200140c0007091041440c0072802d014104c003e01c40c2c0605a000305945031251165150000c245680f400303031500300c0b00080c41c9111701c1d149089143c6010b1402030401c9034000e20031000c0a05080315a400b00320000303411035106070300d9011100b003076940c913070104441e0141e44410300d448c0d03003410740440200d80c0038000d00301c502001c1d0181d80c6040b1008103114600d81e0181d01181549031507580c0d10000c8110242c900e20080d075004c00c40300442541d5080034011140f10f0003041e1640d005140c1665821114074000000e074250141e5998a031200302e40d0394600540c003812a00c0340d4591141c60060503200714211103111104107540080e8080d19040c2280d081d52180c80d01154010703110310b4030341000c0302103106985911103134001c002800e018a840d4240005e0003a5400074164545540d2000c00d01d50501c0f03681003411082c40503013010408060500418680c0c20382c10314000701010390303440c0c80002c000c40300704045401780d6000c01080301c1564144035851140c94 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 940060557 1250 940059307 940059311
    0x30c05011b090b0d2403060f060b0702120313060c020f030a030c081c0c0f020f1204030803100306052d0c030f1302060a030e06010b0f040b0304050a0602030709060210 73
    0xc071400140000d8014840d0200103030000c03591410807001988002d806140c400140009440c0c1512102c601310554001102e1892500c01c5c1142440e10034880c800a84000400c0c05185c44503c2d000c010049802c5d110820a41c8010442045520070032650880244026224510040c0880c41000a21403000d0010781c02079000079030070008654004840f001c82a0003200a9584460004841001c100c040080f01002810480080c841a51103030f01100030305059400d451408164410064546004c400c03491b40d03a403004e02c0240007160704400216041100e280351182829500d607501000c1c4c58003150360117200502d100542848a003d001005c59040b1005c2c0291054a4110f0118906002c09403141c0d454408800006212041108220101c0e40e001410300d629044421402000b90a10840c00c241c3c83c0135407800002d80100c5038003501e44035400c030541d041c1801d040c01810300d580d40004006494610034941e0394800301d44548010360142a803680d0720b560080c20084041c0c50903003040145c07000c4034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 940061807 1250 940060557 940060601
    0xc021506030307110108040f021e1201050609010b1803010f02090321070b0a1503050601090f11070b040305130f0302040506030f0703020f0316080616021c0e0616030c0501 75
    0x2a04180c4e121000301d5013400d00c0155900c9509010415901e8940002e404c8003a180025000c0b8040f407001000b820022030300007500400445100d42a01d070b040e16525000007201e401448118045c00191002045030120b40f5a400c0c101c0000909503925000180042a03000a00ca24030341800cac00b4404400101c0810024482e0f18803528404902c0b403100c000e8001418040820044180c030742102d0311b1807040500d2004400c1d22418030980702d0500f8070a00600f10328059901449103c1402032001c02c4031214011313800c001c095200c030018100300030701c11810003000304062020480740305102c03009000c44001c4c407840c903411481400121500901020700c00d600c010200d8007200400106103051725410340304030000d0000d0b03074040b03031500305507407408280114414004581e880c1c000407801d20807000c0300d900308030480309580280e8803000b61410441c1050600c1c052010750038005d40e4002c902c1c01e40078181518101288681c1d8410107200001140082d20445403401401400d0007070340b844000d8660181d10807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 940063057 1250 940061807 940061813
    0x423211b032103152b141506030106090b0d0f0c0b030408090906040603150908090607050f0106050111030d0c0e040204081507030b130b0f04140f0702010219050d09060c021506030307 80
    0x241450702e1950040705211082c0380208040a81d01d401c0d074103400300031541c8403c3d0039440c1c5201f2250841d0170034000d62800c9c1c800524010305008040c01c00c2c40144c0000100002d42e11401d100301d00c1d0040031341d00c1d200d03c20000034100521a00852180c1c0c0a2250b4907211841d540c10004a0381011304014815414400d0500c0401da4500c03600f00a0081041d00044005071032a00343e03814040c28041544c0248040303060001e202010a034000402d0781540200a05a120b200644a1914140052400303510034481081a031075503601801c605401c50801c40c4c118402500020103a0b8000d8110b0b1045401c002031006001010058498100000381400d000c041034104c085030310034007580b5441c1c20345603d841031003800d40c50700e2078580441413000d80240513282600c98400010201035810309950f542c0d0300002000e443c4184280c072502d5024260301201c40c5006107048a0f00d801c6240320904207a03683c00d400c00014441d100c0c1002518080d000b818142e00e0384525111000703001820320b40203400400c144000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 940064307 1250 940063057 940063099
    0x9010c0e10111213090f090b04080c120403150c09080c190302120706140309030909270d0e040905060a0c050423211b03210315 56
    0x7890840745469060295000d145074900741020200380c0201c04001801600c0e2280076585800381c5804000a211b6841c078000000c04075560740c403002d08082e504002203800a08900021b10504c0440412a010031105420380c10702a40658000c0303500b04000c4060f460260b0581c0100b541d0118142441d200346031a00c6801034540c40700c500b00c2407142020022000c58160000342c040061138015000322200030302820290f50302c482e1400f46e4070201e451859000c0c00485035404407031181c15003001850034a035003442449401203024004041c030f8801d001c40070b4a20b548012115400c1080740d0024107124440307000242c403030340207180c400f8002e9040900840c04140001030558009109950000d440310f0b1800301164907000d00d030007540440b034400085401401c142603c921a42c40c040b6841c0b0025100c40d40b0064126501090002803500072070320070241d11000c0c510a810441004c1d05440f00802051440001c66502c0c081950707881c0004030606c0080c00044625110f41030058074114203034580c5e000c2e2024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 940065557 1250 940064307 940064329
    0xa0605010e160c15020c0f060a0905120301032105160c032d080a09050a06031509020301260313060305100e09030d09060b060d02030601030b04062321030309010c0e 72
    0x1002c0d8000441c140a0b003010041d244030b85c1c0d407c6064401c181010700c1c0d0800035205080080d1044d1140c102c01001940b001001c5904a030b50009414134210407030032200d190a10b011810900b440f01c00d0000e074120300c20045101042c1881141c12040060461520440303080e10138100a140b10b655204030402a1140c5080c04441c0d03401a81171500c0c0c83c1001c03421520600190841034000c84000800188039070903030008101c604540c000075200755100da0340b400407800244100f0264481c40c000260303170340a03084102d000040b290780949203440e82c841907002081c0c1807079126400081d920010400041c5c00500b0300006001944505241402d2815045070303240505a011103655075181401000c0001b5544528071046000d00829110744819030268020341040b503503140403a060600e410114074241c400c5006645800e49002104a048542c80f541e83c000d107100301d90046101c0c440d061001c4c000c00844032640c148080110307a24900350700d00a080d2004c807a01c0409002d4141030b244165a28940620 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 940066807 1250 940065557 940065593
    0x316111b03070b0f0301030b160e04020901030f0e030a12020702030c1e09270705150a050408010e0c030d0c0302121612050a021b09180a0605010e160c 66
    0x3152030500d400000307040c06107941c0441100f220000f5074840d42000880030350b040f07030302420b02c0c0030043d6500c0108840c1001c61032002030008507804031013141444c10380e010304003003141894000b032940d07041d40c0f042c81103c511110b11140c90348086103425040750700c0140d2841e100c403020004d504003c0c0540c0401d03a074280b5105a036120317840b01c0790703003241c04521804032103070f1014001c0c00045e450405190201201d807000020851011603903106020a8000040403c101d985c05404950743c09003017201c94035590080f24058003004020480010000003d01a06884c41e407403002070200c160280c010140760079130501005050003a9400410b000c20740105080100418224410f0355407440c00b10b0301c8400b800a450024a103000d09005120303582d602002901e00c49086030201c90440c0100341000f0200f4142d8400c1903440901000000d00c0d821203100e41c242034189481c201c03117003200c40741c0e1600c0030f461090300030032a0307035000c00100801405003102081c000c1030682403000c8203180b26100c00018000c040081c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 940068057 1250 940066807 940066843
    0x316060632040504080c031207031a010801090f15030507060207050a150e0d021f02122503110a030503070e040b010c060510050409140706020c090a0f0f02030a02031611 74
    0x68117214038942201d440d05a8002070301e80d948410503d90f0b020380c10a540c00c1c400203280c20800248941001000d5024203c146c44459080c0e00e80740d006405406408201d0340c2c099118000008400711881e0400081e40c0700c0c90107408440e082c040002e00e045e925901584c400d601030f400c200801c0001d40c240c40d0b2140094a4010009031180c030100d12590070707050000b500300e40524540342e2840802c0c08800948403451382940c00c802c901c0c070b071048858010514464000480041505450b01000100900741442811311600329800c126580307061007400101540880c4001082029160340000c041705047c2d07080342c00f000048403003c0000e10401703000900a02250755200031640088206910b0401488002e0040c001c1038018980090410102001018603115414011540340e00105070844500360240400165584441003d000741c10050f8a14201542c1c47d81e0512080019000035486040341103005650f909007030410003005060100801d04016131518a13071045640407031204012200d810708 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 940069307 1250 940068057 940068061
    0x3011206090203030f19080106020303060f010c110901060930060c110102030a021b060105030a1203060f060e1906140d11030405010e0f011a060a0203160606320405 72
    0x2003491813180f05c0d240e07144c2e04008106070000d8000c81c1e403880d10340041e640d18280306903079400302a65240816900d030f5034410116010181603511a085c82040c6a0042404890803120031001c9110881c080c0c018000150450506100d402c1044501708500384072549402700304a45201581000c03144098020300c12500e0321510135510788268989006940504001c540ea41050440d0038002e51201d4286640585441029419000d001c02d460b4102c030005000b90400d10115941d21096460341e04402c3c062503900c41c070208100140c0ba0400c1d01801450f241d0a03000504402007141501418840707001110060303000740710803944040006550307100088082e85424404210700c010300f075004540c0074051804400c100c02d1080540017030000c184040c05503050360554030346403400c1e250903a25042851100450b4140c0a080440003400650010720559007001360082c041e03460003441800035582c6644458040c00200240c08564498a41c8501011703001900d041c02c9445a40c402c0d80b64500c15035641e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 940070557 1250 940069307 940069309
    0x3040e1503010f0608030301060e090906040f03110601090b0913170c0109050616030608120316031b0e19050a290301030308090c090f19060f29030112060902 69
    0x8610a10501c040f410f0001d83d03181c400050342c0340c109104020000e40c0e0f410520006003000a01c80f405420201c02611083d512500c48030101c0c459000200c0801c503050302c40a070005030501c8498068540d2070404100208c040d802c1000c0d01c103018104030032a0032412800d41c0010f5000310b01c540702900044e5002e4695040f000f1290040100d1b0101515a001c1c900420520079a280c1d9641ea00c030703140341c0701080019201e03269030343c0c4e40005c0c24016054003001c0011415182c1d580682e48076101c6645800701e00c0c0b1800c07803030003180b2004100c480c8001c65031244141c000b9123080c2001c101c0c07900c000c0000b100c002c0d243c5030000740b0341c8030030348640f1902c0e500001041300022a000403045005004565842c0d503560749140041c01000c04952078821400340800448140c03510207041800b4152100002d0456101c5118a8890b1120394070322240c5c2d10f554602c00111001c40291303c9005040900c2d10003142c0b600031a522800810301c4490501100040005224591150034940c08458001c18002001070702fa00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 940071807 1250 940070557 940070561
    0x1e061018050a17120a020d0509150c010911120d0c02030109060c200c1503100f0b0a090f0f120302030c1c12140c0f04210506010803040e150301 63
    0x5049640c000002907008221142079400365001100800100c5445a1400d101800207008400340e2400580101001c030241c7e603c2100980341582c0d0060143c03505040c0041c4d400d045510035003a60100da516407404006206164400101804040d41e0104030700e512a040540c0325071405141c01d05000c0800940b0702591025030000c0c01e0b045c0d00c44c404010f4140c2079a07000e0107004a6401a503041c541c0b041214900d21004100c4581703800c006807420380404103820303240583d5040100321101c0034406c41000251284490612401040c90031069591044000c41c018641d80c095001030300c942c0601039081001d00c2131a4004000c4801d071488264030b110760b03032408904522650810402c9440341c40a1680884180c0001e4800c50b03103aa11550300001d05102200c065502c9007200240c031401d0940003807003080441e00202a56500441d0302840c190711145e40701c1e80030032130b40e4401e44d1201c4061824020000d01308013030740c09041800b00071b50415180042c0c00d1421400204050040142407203107480c140c80035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 940073057 1250 940071807 940071809
    0x2405040f0b090421050f0a0c060b03070902220b070f0f0c0b0318011506260c090307050619050901110d030c020c01030b0105072006040e1e061018 64
    0xb40a06524181400c0c0055900022540d0b40790240741d658990a015004504582181d040060110304044500f00c060322540c64141e01a68500e8656228500c282e80c02d006e0031016242e00c0400503110402440d510f0425041c003698060115a01103042c840e1852400a0390030300d80c1d000c110148003510518100c51200204040104654451035000c6001007171480650303c0b81d11041c982c50441c0810314642d80c203880b41c2e080540e06004000390305220951007a82c2c460348080b460184500b070300012041660500c8030442e2191010301001c25410390510f81404810000d041c226445030038040308ad02a0080b000d002c143e0402403000014040740d940e4000c5001d01c1c030504101e01980c0c903100340110050040c104510700e080060003180c0300c2c031205600034860003070794041c180d45103801c181d9245d6034011090000902c0c0005515240b40d205030315a9000d0041000c1c000c28040081207003403030030011000788100700c11138003030038480020440d0540b50140740101c0e4940030301d00284003414802c8111440c0103d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 940074307 1250 940073057 940073059
    0x30306040f061703030402090a1812030e070b03040210030c080a0504150e0c030d0f0f0302030901060902072d020105030c07020a0527060307030804181b030b01032405040f0b 76
    0x314121071a03d880000c00558401c60090724100b602d556504c502c0303012901c010800e0b9403480f00d100d88290100f90700d0303810300340020507078200003d440c601c004200c0e00d042000e611a40d8403007000810002103041c0300c180316078000d8090806110110300c1100141c680800140080001a9100300140c01d02c00f014140500000b840c0800300b002907c0c001541d500c800d0119030b030901a205403011040b0b42489542d0100308019195664080611000400c4000c1d40c000f505100e1203640b10200464107521910040142622540c40207040540f190050100d81c03003048020f04c1c0d410311110b24440540d030403c080342e0b40078a440c419103a403210980b0010b458280700c3c0d00416002082411044c03047c40310321604c00203607039500c503040c2007030342d1a4000c01d07030790342c4107400001c092000c01c0c48100016501c10200904070794880e0008a481640c1200c00c207800c056100c82c5000080c3c46000a25865802d44104001140c000b509010038410403034040170701c1c51a500c5124003c580c2c407803000301d141905038011050460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 940075557 1250 940074307 940074329
    0x40c05121b190e19141315030b010b042102190e270a032d090f090b0a14030c150a02060c0703020a030e220606020c0103090302030306040f06 62
    0x124400744a00d01c19203140c040b2000c140c000340500c0491516003a01400140c0103854140883d0420455945c0759040c112940d40180c1c001e44180d86020031400303405440e0101103103101d81140b4509000c1d040b03d5044e071081484a0040009005003016480d2011a8090725061940000d4041c030110350b01d00f00341214103903003011070300c000703c2d103d400400b4450040504000a84002d20a03400307078022104583d81d41e0304698032550b4000c0000380500001d008603a07030000414140c1401e2108507070148107920b0044001100c0c40e606005041500e03131340c00b0280580b590100901c1054201084010b01a0b000312a14001e03440e00c0464039603400c002030740d10a4030203050000107000070a103a14150304048001000760050a000405088c3c0841c10340310410b409d503000b441d900d540c98030b060390380e0000d80d04401d03080968102e020008060791222942c19107038035040010240d20305000242048800856a4101810004200040795000050f0303030300458101ca000403d1030241015070b005140c43c0c0d004901d411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 940076807 1250 940075557 940075567
    0xa110609010e070602150f100308040b070c120b181603060f060510210f14040620041e080d0804120503040804030b070c080d0b030c040c05121b 63
    0x1181074024000300a0b402d0101c0301c0b144c3d1507503426a1030741b0760120b01003e09081100010300809603440c4541d0001d54808090007255102d481d0240c150740700ea048000c40010011300e070000c004010000c00018100708280e20b03c0c080c6c00344d5a516002501500711001d4500c3c0e500c40741403962062104031682c3c514507000406081d542c0c0342c4840940505101c540016160030340020301ca040c0142c5491101e000c5030307204038041e0031940480d95980444180302802c16551200b501d1550360510800030911400f82001c0c016103041d1502d01c05407448141c81c03850401014541d8100066002c041e5026200c5c09403050903051802d0f50f00c0c540c400303480c3e40081141c0c403d09406c1c0c401d0f0364108107000c2c09035008910420f014800e02c001628244016a401000e888040204101040b9950310003074001c050351404441103043c0361118041e44d0440c1c0300c41c1c0022951610515000d14007000803c0ca200b509403014064005040350103010f034015141c061b020075074064000781220240c1c0f4043d0f5080e4418580382a02c0ea = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 940078057 1250 940076807 940076821
    0x513090e0c130b0108072a110f0d03080c0901020a08030a020c0d08090304090e011404240b1021140a0e1504031b0c030515180a02060a1106 61
    0xd05500001c490180310341c075600100380c80301030242000c01c40040c3c45001064503a002c0807503140503000111241392100c4070301e0240162a400c00f007110305009841c1180d42028150401c13107086080561140302d0700d04004080c1c0002d81007400b265015a502e40200d458602ca100142d0030f0409280b0300800c020300c0001003095000c0306601400d18000d0007400c40e0480110414140d503000c02c2694102c1c100c1d8810f010400c0104501e03003100024550130000030403075100c500091940c0a200341c0341191004046074000071801d03c44001d20300c0c0380f030781c0c00801c0c84003071001c02c0801c4407504c9940d015801c1003128281e0318012036607841c0c90101e010401034104076501d0340007074190800c9010303150004464182001d6000c0d8034400601c2c41c1e4881c1404c180440780380c8540d581520b2500d8001c50400c1e05007490001607022036404114030004600800c05010f490391113030314181d55504002c04951201c2c402c0d0030210443d0307a0001c4e030400e443d94144c410307a076121070b030102c240e0b41c2826141016205100300d03400c01081c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 940079307 1250 940078057 940078063
    0x100305120a0e0108070206011509051908010507020312041103030f030a02070204060e0106051801110f07030b130c15200f0c03030a1202130807030b07180608070513090e 74
    0x1c2410035650a0380b42880b201c011030744c0440035108000180d00c000010b108800f0f0f416204c48001d115400c02e111815500d001103540400b518815000b020a20181001180428041c20342c0c0403456201861a0090024182c040c501001e0b00c00b400003505c40c054403041c0e490401c1110500cae5088609141c0300c0c90100342000c041e602820040b40204c2c05c0040000303001621802141c1a01c10f1501c40c1400c1016080c005074005500580050400071480c140411052081c0180703207038203180030040c00301c1c6030541c1032500e101da00c050007003401c00700821442400b250301c011180c82611a001000d06480021000840d60010020004240c0c10080c28000c5610540040e101c002820140103488030b00082100b05034807406580d04070408240640160391418089034010710700200400304101c10192981c089501c3d141681d00704680d280c46560500034040c0e000f5414045070486807454004050600d580201180000340c01001402004585561450009107842000d4005284104020200d01c0030840d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 940080557 1250 940079307 940079317
    0x1803160f080301170c0301090b04020f150a0302040305162402010f051302011209020105090f1504290414060706090203060c033310020f06090601060306090207051510030512 76
    0xc94403031703282e00d856942418042c49219641080801a640e902c40d002d01c0500c001ca00a415400307040e24900e05c1100c12030303501400200720559001030b00e45040d881d00d50b10b0180003088260208000f03a03010804044003c92196182d0398140d1900da19007c550000d9014103040d1000c16015800c01c001c0028140601c40700c00d9840b03000740d9580d515100d03032080003000c641c2903170310207030015408000c80340040c00c1c8014850f41625024089041107911400d000c1c0c01c1ea00f140d0400380100d41c001407400e1300060420407112111401d83c21140c9010303c0c01180500710b03144070030502d0003841c3c0030540740c09112460f4884d81c549a00607041c0d038058a8281401000c56104036a0030102c500d4030803075816856031010b010402d41101000f031110707001c0c800b0f04000c1090341409001b001c500c20b1103084044004144806c5000c0d40003040149240d506201000d401d5a500f50814988070b031040c002c800100d0700c001350003418215100254203040d15980001451048a0780003c1c10510038100c444000300e4000300181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 940081807 1250 940080557 940080599
    0x80f030a030507180b0307020a020913140d08010e0c04120302010603020915060d2c010501180c05030601110102040537050307150207030b011502061803160f080301 72
    0x2540d1810400d65010404c020010f1014000440c20301201a0110085410011a004803071301024158005001c03184110303001251a490543d078042000440294500c81c4405003000d041c030002d58000080000700b05100f00000544030801099210040508460141c841c0500c03407014540c0e03608000c2d000c0c0401d80300c2240110042c03c001041c044040000d0300300c1003401000b02c1e25240345200031802501c248101651010007000c10300c5460351007003004c18102e44d10f4100100d4158506034444161000c0c4a1200c05c0f0142003500e4442d107160300a0440364460400d080c0410742d03a84800c0124028010341e00065007140c1c8110707a0345c4601c8407152604005e4000c03154070b801c04811754480030440c0c0c44540716070368069100e103500380242d0402005c00c2100c2100751040301c09284c0e032600c0d44505030200ba07000b10f030901010f4030701c88040c035410b00c021548601180302241c44011540c120790703906d1040080316008201e0f2440301c14100b04488c26080b90742d60300082666200d5840e4200a61f00d880c0d0748440e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 940083057 1250 940081807 940081811
    0x3152203110f0115090b030102090402030115090b0f160302070305100e0f030f0717090607030c060c020622021302040806090d09050112050402030a021f02010e070b090118080f030a03 80
    0x451242205005141e0020f03007804c2c510740600c1c600807900c805440c00074817196055400303004d01d03261500c03039101035402040c00402200d84600e50744006030011805810000a0240030080c04551021210449030940e40d168181285044c503424200d00348200c5410090090041c1018142400d00540054400704c003010b060380c0f030112030780e02025941e2040700c1038644210828015a808030f0708c0b43c48000041012800000d1a0420b124005243c682c0800001c902181c080c0c1030142c103204070361180c41d00789681d034002030515003400d0140d207101c0e01c0b4000f400d40380000c01c05100d03021501c0b03003a0700784000080a1025511142c0b80c250381620740c481150101c59a100301c01c0001071051080d07a0040484206855000303032201c070000b481d009042d0042040e40c01d0302c0b984040000503151800c580c50f26418049214a01c07203042c00c40207094070b03101ca1320641c0b5030703203c000d080c440b504104c5e044800c0280c09080000b126064480044518141c551100e9030501441401382600e080102c000c0191030016507003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 940084307 1250 940083057 940083073
    0xd0e03040f0b072001110a0501270b0406020901030e01020c010e0c06181005041205070302211005061810150f021f021e0c1504020315220311 62
    0x102c88828041c07103c0c050720164410103402c0303030762001111041d140e11041c0740c800b080c1424404c01c28945015500c0480b1240c2d501d20361291941c03070f80ca4500d164400d010b0900740d214140e985480b170701440040e0003d08a41c1d40060060030b40e80c06035000c4855802c1603c020b6484030101480d1074003c003000601c244042c0034281c180f00d03c91809004464604441000c001040b245040521401164540260381882030803c03001c607034005042c0c2405055440f81008147c66411881401401d501001b4250ba0646c03001c0704006510002259500001510071800501c070341c0d4881c0018154608084101014000181801407003000c4210207403d46084a6024030f081040507002c4800890403507030003006801050b0000400080d014101400c403020150140c00c0c18002d4032026510100b00c10303441e03149040000d44d008001002d00c0010019045800340140c2c40c909a004291900d0070f06030142915404d6000240c211030a08505540304e458500c0481c2146542c1c0ca4054100f5548559179485407148881d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 940085557 1250 940084307 940084319
    0x30606060a080a1107020d061a01182304150e09061005010507051f150902042601090c090504021905241918090510030b0402060d0e03040f 61
    0xc1195440d22495480d6002035940040510080c4684040d64092520800408002d81c0e00c1c060348015442c0500d00c0091000000b601842c60303545009040c0d0f05110030b8811401000c1c2108204104490020450b000c8620844c90840c241c42d2803400318a0b80640303003a60701562400e0380d008000c00d03102185296805034480003080d60380c0700e008898004840010040c207112952280000e0013105220300110750b400c90048a80c900300440388512010a0741d40c8400d02200e60342900304580003048079040441c0b90a062408011f10011b26110f20010020500c094100510096111a4235150801498046140c484040c44080c1409841c242d20130030b401681003010180c20418101141e400424071160f05d100e4055050310464510b0340158a800c0910081d9001c081d04401900e03c00401c1d680c144486c1c025850701e46480300107801288000d4035100802804088018200080d2900156550034541d11840001c1c0076114185d48030348070702c1c240305120084620020103802521007402110303045076103e42c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 940086807 1250 940085557 940085569
    0x5060109090507150509040e0f100905030307180f0303050d060503010203160e0111150402120f0a2409060504020906010509010e12010e060903120c0a0e0f2d030606 72
    0x3440030304107400000702000745100041e400c5103ca0220304245c0d0400e41003030001002c952044441d8003280e003010034040400d481c1801041034010803d0003c20080340c0300d032030760340c0d81c1e0000034000d80c14417240d0300210550740004240b08005222030381d0003128154032807800814540007800c600040d14113000020580e40340600950344254074210030318001100754041100e150140050507814000f1606040c004044180060f40380d440003016060b80d2401c02d4030500c42d4480c20a00c13250350581150740724040b44400403c5d40251607070040c00c003010061240d0282c1016822169000340124074081e056400c010003030300300380d00c260b0080342e01000b103545020054400f4490030b01041d00103585030100d8101845c118000200d5404c1d110700000703481903d070700e405240a500b520940266403007c50f2a0f602074002c088215401460a00101e05001c164440540580c1d10407913280c0c8a109940c80ea20b500380c50380d03010210780105003d8080c034504803000d100c1c0501c241440c00c0358002e0007160002892403d0070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 940088057 1250 940086807 940086821
    0x100b0607050a06050604020904060f080d0206011a1e190e040e0c091504020703181208032a03180105060301090803062b080315090907090b01052505060109 68
    0x12001410382c0050742d98400c0002d000051020340d1107a805d1200c100e8a44952080102920940c1c03100c40e2072074100b000c441d14014a5410b44011035020000500000b0914503c23054100c00d00700d001902c1300481951102c40028803081585950008a40900c1801e448440c060307940201e910760420524a10090000f511500010324105902030184042c1a0821404d1645e0000c0c0642000c03031000d00b44c20000303003030783d00890f0309a0004061000250241c0300c000c0c41c00001f4103c8008411000c035095445190342d0100031f00c922482c50040f60400d074410458110070318100400d201d40f070b030780380350002c00700b00041690040721b40c8542c6031400040b4107041c14400d80c4034a903000f05502e0300316a5058104403041c0061140e426443c420140004c069840314a01c03815030b40d02c100310990700da00d0b042800307a003240342280c1840c0c0320340c61180501c0b590007030100b1001d060742c0f22a003005c501714140a0050710544102c1301c0341c864459001013030303c081906800508442900c203205452280e46e03100c04107030945002e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 940089307 1250 940088057 940088063
    0x31b0305071511010e0102030f0901060f030201031d07060f03110c0304050d080409050a1b081902031308030103061a060c072c04050a0b221e0b0108100b0607 69
    0x440c1d1800c1c440141c40205240e041e60491a00070f80b01c4070364454071800d4522201e81003c0f2690007009005029080130466544002190300030005903107010f4440318594024030000e4149035442a1245030741c0d80b05a075030003010392075408850703802e0350307483c0010803204a090f0780d200003e00d48039509407250b03030050844000b2218a0015410241032504004154035810001c840d0a001004002889101c038000c140c410900280c000580d2001a03080309030801424045000300003580301041070006000900070300c8041c0c043d400503265547c3c1070449164116100c4080c221381004800082088146c0c3c20420f8594151404a114a5540380510100b801564168243c1d42c10154082c0102515044800040f0940c901e140907d10b00c0a103071660307200b10684055680d9000034103217405020a08032001e40004400b044c03103c00e1116840c001c0f682c00200c04008000a2071002c41e1003012030071410344200240c00500707801155035030300029542e4007a244040c41c01d03030341844011041d0789850b409440009030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 940090557 1250 940089307 940089313
    0x1517070609051201141006030c030b091317070605040615031a0a140a0e0d0f050f03060303040302032b02030307080a0b0111010219080105091006111c09031b0305 71
    0x4205420801441101c0d082c004080d03681750354407254943d03420300c00ca0055142000364100301d070400c2c40003821b82c0c01c9024410141801c00203020800c0e00d800810301e034011081c4503090652842e42c030341031403d2100000712040c924000314054041c4141035221902480c4100d80c00c0104000d4103a2a503058107082c030028040c06140c124403202608059416a40303c5024900041c002d4a076441402e0300f81303400c1d10100c0c4140d6135480c082040340400c102005403000e035420f08142c2100111401840f6210700d91065280035000320100d1f0710307a00c04200341c50156034014260f8485103101d4189107095455120550422038290070074440040c00801140d0141c0d680d6a1013409594031826800050401628090304104000002440400080c4060007034144140040324000e81c0e8418002c100e8041070304942e125040403818040e00c01c06142304002140c19074100a94000c144031806414084a0101d0601c2003c000444503034155001d030200059038403e000428940c011200c003c0f91441240c00000e03c594 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 940091807 1250 940090557 940090559
    0x10b03040f0302030c070605070210091406070201020a08220603020a0f0804031b03020303070306080f070905060a0b040e06130e0c01031503061b0908030a170711011517070609 77
    0x6403505002800c1038060b0041342e00e05111941181c0c981006540501c0002d00041041811490315015030008035130989071036940c4604020030070203c1035003d0b0215215420010b000011139000b44020702e9615040400d4680f999400385d50100e802d60488000c0440000000c0c020175228000e1083d104000c080da40d031280da0300e0340c9000030382d54103030301400c1a0180080701081d8540034242d1552001d645200c2d03800396443e8200004007806881c5a0b03040506107401c072000c500d143c0c52000902800300c07841c3c2d0f1001320740ca8131031402207407401204e40c01106022034006000305003400c80b2444075009032415a00d18003058044000d500c2140c81c07148222525802950135010760750b1107508011440400c0c9606007403240d5881c0d07075110469190007158038000741c8c8484801c850a4100c04100002c0c8200005545440c03807860300280000d0350480703c0c0f900540c50310b020402451145000c0c80b409440361000b0000748451041c07130414140b491041d404c031501c0398205100050000324901044a2160711144601 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 940093057 1250 940091807 940091813
    0x1203020c2407050d0f21021b121305180f06131a09060604032a030f110411040b0912151e0c120c0307020f070f0617010b0304 55
    0x2024512040c1494105030012141c1044840020301da03a40c401d40041080210556000d07003c800b0b04003409082c884a0a5107000c80305400703904007070140100030016902c3c0309044440e81040c40503505038000380b0800b4100c8410950300d074002c10380d24203420a25580da036a540708111103c2c048003415030f40c81c006000801d2220080004143c4c10000003800060700c181c142540320115140140c0e00342034030351000000d01d054240038100a422a0095404514090179915a4401031004c0b1040c0784c1100c0300d0300b5201d50045c00c8400002e01860340020091007010203401e01d51403030b041c0e544010b07220300d2608000b442c40c844042d040701e0407940c6254075182044405d00c01c2140d90510003800a00600134851240d0160284902641c811440d6121034004110070102820344078000030403000d1113500800400c0d95800224008690008000f44966566a01d5000480c2002e480d2042140d56201c0c401c00445c41d415020040300035900a96288d044041603d0784c0400c0d464401c0c400d803a8400c8080000c034000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 940094307 1250 940093057 940093069
    0x106111c0c080901090b18040f0606020a030c050a051f05060d050715030b120105040b13020d0605090313080c131e051803031006030c1815030e0102040906030c1203020c 74
    0xf5401e05050107103241d550b421070855a5440a40300502d511410b0801310a00d02c0c10f80b2882003090340300402007160b1400d02c0e00c080e640740510440035013480800c10381d04003002010445544201e5100c0241d801601011155080000f000c1c40c98003080d500b40400201c4605000d1103420303540740c10000074402c1c6d80c60141e02e0601c42d030106003813608164032a49890840e866064003141d4240c4014000100e524290600402828010f8043c04000f54140c0107440542d03100b04100700460b4222000003480d884044500e80356101ea01c444d52030039002c07903500003000c80f00882c0003410390700242c4415810f030b1048002c40713040301c02d03402a1818254031030b4481c40400c0415800f5540c00505c640f480507403900e034a21000c0c6160402c8803540c40d4219801010300030103915000b0407003840120b04042e96070780c1c00c0340b41440c0b44420501924410100c0042d480000a21076000f8200002009008641c2c8036151022203015182da40001d4a41c952180c030b0001e507156250968007145074040d8054040007a0180802032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 940095557 1250 940094307 940094317
    0x3061e06230108100e1f0e01031a0c04030506040f0c140307090b0d050a05060603072408190204031a0f071e0e060d05180705030c12030d050106111c0c08 67
    0x620844c20720082011351103600e0650086091035800203050b5a00350300e545d900c4010340c001800c145400310041000070000044a0f08010f200c2e0051500c5a4a048407114240620307131001d4003604c521028002403203007040948121600412410b0040e40d107901d0b82100340b45100d00c165426510520017008240c0c0258445501c6000c0100048101c04841c0c64540c50104502010f40b050b40140d8207000b043c4c035003006408024414030000401e031000c0a440300101000030384810781400002c0000900003920003482c1c0e841644018400c54480c0d880781002c0385c0032a61200700354440000c0b840410300c90125040701e54407980c615038401000c41e1812008031245280c4e104210240603462804800e0340e650781d00900918111500c0004e990300d0a920342c03c926100c3d540030b182041e080007100744155140460241d81e040001c2e5401001020014407907442e6110301e1880013115881d0800100f5803580c007608070f206100d01c9804a500c46503200741b408943d9112540300030046920191180000340e60040504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 940096807 1250 940095557 940095571
    0x21c0e120c0d060f0e160e090109080909040c0513020904060b03040506040f0f06090809132906040312020106171b0913050d020d0f0207050904030509030703061e06230108 75
    0x1144142070013120301c3c6003442800c04064981b9801100f841012024550194490591030080c00a14096120070f6414800d030002d56028901c420005810300404400290003010003800b8110701c020706d110070340001d400c602d48a40c440c07400c11348005003081d071070301c2924040c540010160455444a83e10544c1180c0302560444004c0791038580c490100d44544200b07095240a40380441e59404501c041000d605650714030901c0c203600d030100c0241107d692146403c0032501800040c5c3e404401400000d280780681e5200404070540701c04160609623040d00301030f080380c08941c00314a0400d05800b0117512842c0841e041c0301c4200024003500098542007485c01d800c120320518604130000261225414072044c1c14071840941d10052000c0c0700e03141d00048908a804651019005203428003002076070b100006003029081040c08a662070545d0740034001040199440344c1d041080d551802c1c030403290b204000b80c03c0071120b03141000000b03010b802001b030311a14902407001d1a0002150800554007514090156 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 940098057 1250 940096807 940096811
    0x80c040b0714030c07090c171f170a11150304030c0807210e12060112230d0801120807020907020f0106180608010612030f021c0e120c0d060f 62
    0x4103901410b000401c4c0440403e40600921424030407010255155149500b007003188079944a0114607000c004190001080541e031105111070803c902d0807003099801502007088101102c5100c130400154900e01c8503c40d0a50889030610103081050308084e0714464514081c00b040050300080c0305804098080b840740d403036a401c0220700d446402401500080100e030300da403e24000c00c8002d4000a12480c2d10b402100c00b200034000ca40c580c1c0e61100c2040c0b00d0780120542e5200d12000b041080300c000f9a03644004000748001c5c140d031015156031888141c48200c00700340e89000104104104c51800c0d0005c80d040341c08142f601c82980d0a20a6000004042d041107014142400070f1640003030050900030b00f45041e421000f07070014036500e801c49200d58800201c5a243c02010880418002c1070008100c3d09800c118640011440d02130b400d043c0a0035121401c40426042180c1d10b0380c000860580079102a20f6243c54040b5101200e980c03400b010000c136500004c46040f40d000100950800507101883c1e07000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 940099307 1250 940098057 940098083
    0x3040b0d02210417093a08120105011b081303051e010f02070210050c0f0102191b032f0105040303090209070c020105040509250e010906080c040b07 65
    0x2803525041410b00c404419101c140040c441444000202407814056a03004185806452030009070141603c04428030026a8584080c013140100034102c84c410b40c10760001c0303503900005d01e07010700c5640c40080c800705005480b10001c01c2c5544a000c450186090004242007110f80704e460328107080c1c0081600d900f460402c11008030000c1d80230f01c04803000d54294045441f1503030440c004a0300f51000b801e143c070907240c0f0522005015a660b0030702c00e0101201824200c1e52600b20f81c0110f424041e800c0c154468a40c0000ba003501c46000c0260121842c0c411079980d00064450712248105001520703d0103400108040312890140100d8203601c145100990320282412500d0542070f07003990782c11601640402d0ba9101d20700150f0400e8928550300c2103081c5040c02e071150740c1d540060120302850007124050684403001408054407094024800d80c0c0d0681d40d0600c8015110f4001c0001d0381d0348002d1800107061010000b1018041d2101e03600426a40e202c841c20142000203c0c129904055000d80b42c071240044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 940100557 1250 940099307 940099327
    0x60303201209190324110702150708390c04020c1501081e1501031e140a0c0b0a090308090d120306090b1f030e0c030f060114040b0303040b0d02 63
    0x1441c00c000d500c11740d0700103000030382051099040e01c281d040c03441e401410a140a07082c00000401c03140f415030b0481b40d060140b0302902d6a0401800b0300c0038024480c1c680020760081510f502110040d003100c10541c4074400502813840101001100c100c02d00d80d035804100c0d80c441918094014010002d810400c0b90804802c01d0040100c610007a4041040703508144010b011503001c294181d424151000010100700c040600c2048416405100280082c0440301c43c3e024054044800201c41507003058500c000c4010b4122419204d210100d0121903110702c1100009a0898240a07100c820032076840d01c6041c54030b0343d214281c0c3d81d03000202a03030740f051002c01070500161180c1003090712000d840d40c00041041c01c155481088840f0715a0341071040900c0001c0003004816481003c0d1001c41c4e9185c081000445603812a1402001100041d4180a0300300e50852140340080e015040f60424900d000f20b010401060200b1074003c0ba0200e5015001003105204046408005241107000042c005141900c229 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 940101807 1250 940100557 940100599
    0x60a0506130903030e010b0f01052d040803091002010605180a0e2d010207021e12060108031c06030b0112140307030906022a0f010e13060303201209 65
    0x542c0440c00700e599a20b0019100d1401d11409848690650300345041d000d4100000c2c010303015541d000c441201e000c00c0d0303d81620306d00a880c48607200c1c00c0b428068440d526007e0044c1c594100d01200341c0035a00c0011602e10003403050081d14200c48000d80400030300d038140030300d110303d01c1e1008160900050b1030303040d02c41d01d0a504010a2041c40320280203030079072003040baa1034004001481c0741104c1681c01800140c0142c0c0e00d9440750640760783d0103200c884d9000300281c04254010f115280014250080000001e174001c000701c000c04c40f4102c502c0704120a00e216510040c100c841c1400050407001000c40107000c8410340c0c0c2000c6190078000c1030f584000f481c3c0f48070400d1171076104100c01c90006420142c2084001e070108500c030609480080c40070032010001c50307855102c0c981c2081d141d00c03403805428040c2d01640114030a15030400c2c0601041440d1900340034510150403d0700c4103c002032070409011240b0f145016071100c0c9000400c01400c80748001c00b000346a00d402140b43d195129000380402c0301c804d4248 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 940103057 1250 940101807 940101821
    0x50c01032c0c12070e0c072f0d03030204050415030503040b160f050a0209010e07021c030209090c03060a120510200307030e0f070506121521010c05070203060a050613 73
    0x30f00740c540c101000341c011988098a442c3c1baa01e0240110b00019040041124200c0794022201d402210040c0c02080640144072000c0c0c0c00c580000f500e40b0501da4903030000d03c241c1e08162803e00648540444802007135032144409082d0760018032092220203083c000808040b01c0d881076030244c841c001c2d12a581c3c040d0703a8080032101540b240c0300520441c2025402540100090256416145001c1001030746803407805421140e180000e10800f061540654162141d204000d400c10500f0f10700350401d110303680d00c2a0b841390711802d0b485d030002490307400c01500c034000558400d014245121307801700c500010f4014204070021442d640c0304034080544c54071340614801c0714607070307004214402c520414900b4400d261003590401c3c0c114220602c45600c0710800c443c0c0301c2d5040c8200c044540d503000f540344c51111110540310390081165540c03400c54400342400e650b88010030b00c001c008200a0f10740540e0103104030300b4025010b4200f00d002400c41102c560101c0c0c1e010401170981e401046003642002e04072018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 940104307 1250 940103057 940103089
    0xf06061d0906040e070b190915110f070e04150507050703050c07121b0602160509041e14070509011202042a03060f0b131a16030804050c01032c0c 64
    0x20100b554000c07110000c04501131f081880c20802401c0d030900c4d080810152001c0804c009200c000d03003407142103903410011a040040c0003016540c140382c90b900c00c01c05200c000e44042e140860608040c128080d1544505030042d800d0b078455034680151035800b56050f402c0341451058500030501c0000c0d0490594a00354920b9100e4400c43c40c0601000f40141d484944a070094400c40d80030b182c0019070f029100c031034107003603480460b081050360381c035031400c4654601c2030703000c41d840500440703c844200b1507214450a400407001090360142521182030188401091283c04150580302c0d601e84054201a4004800c299018211421000c14281d8181c0d00e030713902d40b4131080001d607100420004810048003000c090300e002c4084a19150300d0142c808402001400b0300d85200038001488004140d07048211540078000c0855003012010034180a0400d8100712400c0c0c51a000d8884800c80541c03091040c100d02d415080c601301c941204131144079011414401c602c222a205000d00001169200c0c0446400e6041c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 940105557 1250 940104307 940104329
    0x70e120703061418060906060d020f1002030903070801140a0c0c05060c0306041d1509070e010f030b01060810031205040308040b0703030b0d200f0409060f06061d0906040e07 76
    0xb000c403242541821130a0001c445a08024140702d008240820065009181182c0244081140d030000805210601c0121540102e10302e418800382d980201c007801c0051411401d0300d040d503a44003001400e80d101d03505450b18040b03007180000e403529010303803007070320342c071240c0e00d0b01d440c0850031955a0b5103000e00c1525405007508000c0200b000c00d1070302d0300407603007600d810030f1503403500801c11403105645440a4a82441403042c640005e0000ea03010841800100100f400d04200c039652600d8040c034007000c502081c0e9006151000110b80640184c10304d40c000d90510b00c00085940c074540750a059569044071590030080c041100001040c0500302074070150246c0490569603902c1840d014049a41e5035a40c1c900030020782090b203012428182d942c000682c80e40654108040c5104000781e130f07501841030720550141c07401c0c05040a01900b07a01c5043e001145840400c0300b40d446c1ea10944044490b59160000d24007000050340c5d00342481606280c1040780900301050326805c1080361400c2c12010b402c0007049503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 940106807 1250 940105557 940105561
    0x18210c08160b03060d0b0112030206150d061505210105060102010902011d1302220e0c0a110f0a050318010c08040909021207060e0a0e070e1207030614 66
    0x104054090000301680001030699840c4184034140241040c410848100004400030f410303511503114940085034041a01b40c03e5686405222164103940d50b81500184106000030b00d8558101d504164140001003198101c1d4504c1d03075400e0044c0005000440c0780300e03100100000c243c4c640846030078440e0098081800340c0300f10300301c0c0320b070845500805480c11603043c0f14080d00580d811072041c10044404111a125820390800403418011301e913031100e4204c500c00100304440d1042c00e20790204900311488603482d0b881d681c01c100111100c00303960044001a04001c90700042d03005040c0c50b02c140d01d11720283d0300b0300c0000d05c107003d081c2080600300795003d030400104c2d410309a120340c8040f8104882401e2200408180e0b4a90804a0041e0701402c10525a0f508950003950b4601e00d06500d140900c4040703a000d641c0352000105580404100c0301d00030041200d02145114007004014484c107480c1e076031903140420000403c4040701c113141134101e6900400d14040045003090040b403165000701d0ba0342000307074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 940107913 1106 940106807 940106813
    0x204030221060f0906130501090c081e0105100e090c0d210503040f0b2208181c060b0f03010e0d02010522031821 50
    0x8039800200010704011503a0700c455601c0d020160303040d035150b070000003c1211003030752441c007550131032400601c1e61201102d49581c1280903034008509500d543c2c650303206104031a084503040d074014a44001c2d00000070b901c0d0b0210713440c0c00300080100d85410445448980564001e007414150050701090014a0420410070b5518005011000145182c80c0c03862700020031405549081d07000c2001035800306d0080007502d114a030001c0509017421844d94030b0790406c041c0100a100c048850581070514205600c1644070040d20074286140d60300c60442d10a124030400a0710789119000e5034409130641e104842e1020328a6030711240200d28030030070782c1c00203009403100d881a50b05980703084000c003169040041c40c01050304094000704800c4e282e440c8010422541182c0c0756049065030500380e400a4400c0240c100072181c601010140542c60310803070821016034856a00e01d18614403507601c28 = true := by decide +kernel

theorem cover : BRFrame.Cov 939928057 940107913 := by
  have h0 := BRFrame.cov_init 939928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 939928057 ≤ n) (h2 : n < 940107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
