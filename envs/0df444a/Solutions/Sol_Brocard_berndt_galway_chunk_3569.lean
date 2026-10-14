-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3569
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:02:58.948956+00:00
-- url     : https://prove2.me/submissions/7f70a42a-b7c9-4c07-8b3e-9b87104c6b66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 641726618 ≤ n < 641906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 641727868 1250 641726618 641726621
    0x10b0a080a060c1e050a0e12010e0708030a1b0c0503010510060314010b0318190f0b162001150e1006050c060606161703070f02060405100e030d02030406060306 70
    0x1543e0b102420907003200700d9004000c42c44034000f86104c10078441c0c00035229180c00e010360002c2c5002c0e20000c048200350079940c404107010701040001ea6149116098001c12040e80c00300603200711a16542d40c40e4885209100c40c03c000078100002594414507034403000c41e0540302030040781d01c80c000c0c00c605040b6203407402100508982d60902050040f04600005000f9a1020303800c0700e8210846210141d803918a0710032190811070580d0058424030710141e80c01041100c0c40e02117403610fa01450b580040c41d510300340440324424040e0205000030300001d40070000e8004201c035140084281c0c000025a5210040f1094240309042c0c004600040700d1380108681000142c81c50000790005180460070140c940c008607903601d101804082c46540e000c14402c90588031354004c010300c80e4011410000c0d030000e42c0315070344255206945041c001274108580114450002442d2405964040300030f000070141c610403075009040c083c1204550b400704000040803900240040d40c05240140000107035a03181d40303480c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 641729118 1250 641727868 641727881
    0xe03120a09050c210105191b020d050d0219021c03090b060603060f03150a06062a030302090d060f0606020d141309050403020c031506060714010b0a080a06 68
    0x504034140307030280002aa01140502c00c2d4041520f043c40c000801041c80c00b035100c072010460040390710b01800c20416014840c411010740c2c4590b9000c0103144c2400b44e2821014420130340250250340240300201a4521071001062240070704070f001030402c000030400550141803c074041f001684009070948480c07580070040c4060040c1414200300c4009542c5e80c4200318500100190300c02c007400700019a02c0c1e100e0001c03c0c488890014103481c40d1900c1202d10400210090710301064144c508503002c2603040c02a00640700c1d920341c003c11800d08100660011b410000488021802c00d6000e202d0b24105d40c6407045d1a8444502c10038022800030b5041c4000c8044640030341c010700840d40b0440c800201242c002000529038801141d4059031107119620315103020410740e029640c2189803104000a040c1e02186045000380d045098880d144d829242c00c0403080c1e01079a265612400401101c000501c00e50b1810700000d190000200746031216000140c41e0300700ccc2e54008501d07034020001050400599124a2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 641730368 1250 641729118 641729131
    0x1a0903030709120204060b04030305070b13240902041805060c0306010c0212070513020c0d020a050303071116060c050d03050c070b0c070b0405011a01020102070809010813060e0312 79
    0x950541c50210340003032000303405101c1c0c5200008a00c4119041d516070f034000002500a40381160b58880e603c3c50020881e9000c40d909840c00c4807060040b030401070100d007243c02142c1d04040c1d134000868010300e128005202e8101e40d01d84803070342d600184006869038052102a5110594050a40b000f07a040c210300304180104000c4071078000b002000448da0700004000e404c5034040d62004188004600c54600e402039035040541d01203803102030131204124580007050190342240036990038440302007040e40c1d03a00f8070550080c01a0014800580b10700e01c030342080322900c0555011149080a042c01c040d90050080e0044400581020364900c24031000f0020440e1071a000d2900700003c0c580f0303c01404450044030002495890000040b401c0440d00030151850650001180b55032070605241460081c14102c80071040300c40d4502c0801460343c010720030360725000d030000c960701c0c50300c2d011000441b4440c5004100c02851002110348001140e034070720440010401c0c1d40000c50352135005100c00965104010a070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 641731618 1250 641730368 641730373
    0x6030108060c0c120301090603060e0606221409010906050f01063203150a060e0604051201110a0e011701060c12091206050a050f06090411010203090603041a09 70
    0x40029640c00114142d000c58a400242e4031107204000075400c0116003c0401c008082c0480086210040c07a4021411a40b14010030000e440c01c0000c05601c0e5002190308503444030310040781c060320100704030300c0c0e102d450300c4400c0c001000c40140300500a0715505490102260799904020420000f15102d0303c1c0d0001c03240d0750f25080e10341c5400c0000308562205045041c0d90401019210801054911540c0c0152101c40400e0384030701d402200c0c0140a844c0391078051081e80c0039800060400d0243d030b0140a140b41c05482c2c149041c2c101020301c4003d110a6000058565031031070200b08440084016191a2040e5560341c11803011342400106140840d9481c01c020555400c01041841d0f048281d560402d58001c5071400e10550030b20007900c0080c0c8661100407180e140100c07010801040f0f0340420701c90903820700c1c00c0120761034280359008620784c205c1303803030382c221031004e0208010866403102c4400154052045a14081400340400c1f04da80080d101110070500c81110404c2c041522290039500c00c440303400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 641732868 1250 641731618 641731621
    0x140a0b03123606042c091f06050f060903070f0e040b06040b100305060411040602030a030e03030405030f07060908120f0603010b0112151d060324070819110d0b0603 72
    0x1d82e80e200701c0c070030178041d9220b000000c2000180d049a800300100b42c0c0324403100d2864070500c070689440c003482c02c4441c442c0600340240c00881d51485140c2c2941d50151103201e40d4180712090000503480140070316810b11402c1c1e030005607250f100c01c1c130030043c10311030882003858205072070100c50580307025001074842d50400300c04030101c2d102d207141c14030009a50f2502044075241d450100d001804d0002c0c4c881090f0034000307804551550004010301c0080182c4d9000c00c4480a00c04980340c680c0000c1d14020030740d400c20445001140042400380c1203040c018000002d00140750790354280e04d980080004030328a0125404c200329511044616980200140c000340000d010b003200080c0b1a2100b03010f001055592214491500962078101c03d0140c1040503000d4115007046088071040c4e0401c03102107209205080001f59441221036449105440c01014158130751200602a0741c2240014071001e9000304001c4103240b241c500b0300900101c009041901540c462003002040309941d02c60401c80c2c002d000420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 641734118 1250 641732868 641732977
    0x50a06050f030c030c07052b0206160f0215041a090c011e02030706050c0c2536050f01090213170f0607020d12140a0b0312 54
    0x5040325030104140c032032107540359698041007001e40140308010b04070b80314600188031681107200340608c5000485448240484003c402241d40300d004403812104000340c619103041960007130414100320b1281c0d00560b42900d0302102e8415184c9000c4405456000c420aa068000810444600e80041901c0c020b400f585039048000384c061a400e00e02444185440b11400c244c0c540700344261450f50b035001901380241e040ca40d64175100e80d044941d41c030760385006100e400b40d00c1c20150f040044042402d5485074042600d4146400d06005440c0c08120300244d403000291484004c200502c0800c0c101c800c80062542401c3d041c41544050507081039899a10400c80c07004481d62649001003141c1c1c2e111921030f00c0e0020840d50609040c0d200b420303103116100e03040900445c180c0101e07c100e90310809030f0320340c544840315032b01036000d4914640030302240407015000700700f080c000758002c40400c0b100601100c00c99040201c0741c0e1043e5000800e078642240c040380c0a5192804079610490180641c0f1401ca9080320402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 641735368 1250 641734118 641734147
    0x307060f0c020c210a150b04020a0f0e1c080a031a15180619030c03091112070e0a0606110a05060112140d0306090b09010806180102120709050a0605 65
    0x1e9a40034451450785207540000d0380713420303990700002c0307154803d0303a0b80b110091803c0101d086405445902680c2400e50032892800c00c2d1090702e40c0030031075503601c146510616030155070861541920542040300e00d260410040c0b42021303900200c600c0703062040e940d480208030007000c8849840044144141d000404641941d407044c50600b080a0070101c90f65420a085603200d210300740c49115904450080756402500d1515640d15001074041e450901424003079880880455003803e0008224985541e8106494100141c9008101d0400011205041d07215440310304c0010041728420400c0d502d03240144151030b846000c613003100003c0c900501d0407051a03500d0a40301d4805004100c3e8560701c500d012418024041e81095200c0040d4041d04c080e0480d002c001400740110340112048642014422000c50809840c064100c95010000c0d04103500c440c0980507511000fa42100d02541d001d0100c440d00700c03212034059005260603203a8507400b603d040700740034104203180d015a040c0442804502c0c80504070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 641736618 1250 641735368 641735383
    0x15152d01050d0b090a0b03070602150408030702030d1104080f1603080313060c120c211107050303010801060825060503040c090c0804060e070807030605060409050f0307060f0c02 78
    0x2400c0c225200c040301c82c0500b00508210101a42c852403c00c20300c18144590392110000405c254165401c2c41c0d140c50301a641e854410900c000c51a000000040110740940061a00300400c1d2050706e103400b00303028241c2c00390f858040c0410140030000408000c01082000924400006240944640070404001c0320344040e4611015001110000c0050003c0c0802542c1075501c03580070b030702002201e002c800000d011080040e80701c00420b19107609140064059100210208004418004405589980d103030140410300d180f00c1d50450148001000250288060341c06044014000220686004280e9140014180c44c00102c420354180d0b0108403075910603590305680c07003410070607580e444915021103801507950003402c00925205a8820030396008a0a40c0242d02421041c03019409445100d0707220344080c4104070785940002e400b040014419007003164000c40040c8006281007554030392905085071802c40b040590000105801000101d1060094000703900c5001c1018000303003480603555211 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 641737868 1250 641736618 641736709
    0x90711100b01020705030609062205100b010513090203040b06010305061f021905060603070605090d0201031d0607050c06090a03080105010806120706050418051b0c1515 74
    0x480c1c011951169000308a041c00400020f02203554526001043c503885000c2540c0107581058060102d02158a54459481401307400c0340152801c403081da8805001014542e4a06061010901c05451036100c1118808000e0980f5140940d84c2c0c5000d260100c9500801401541403521740000d1048540301e0313400c0c0c55012aaa2501043d4401000400741e16000d40060074516510182084408101000c910b2030300903c0c05030122007101d0381f580c40c1921540640c00c010b9030006540b0441030003547c801d40100070a1147e202801c090f4131711400b10070f820148200c500c0d0012480028034885410810410a0b40c4000b10b20040d0441590304d9a0040900700c040c49402c1c10010f07081d0201e2070302c0e81d5030003e41164140000072a1000c0b80d03502030140440d0840d01c2852101483c581818001c0c08150040b2845110700e654191070f009031207444025550401c000c18412485503000b5081706045075182d0350300075814440342001c80d820303170001c000442c040395110480c6166081c01ba40100d586003c0245174040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 641739118 1250 641737868 641737871
    0x2040f0b0a030f02071101020f121c060b18030d0c0b0f060f090406060611010204030b070311070b0109090c09090b070f120911210309011d0301050a0b09071110 70
    0xd240003044003c0c0402c411202a041d200191003000c200d4108007084203c182a000c1c0c0305130316403401903240c03612180300b05035140100c1004402e480d108100b0180c0912009620000781042d2900d400680e541c1207a101e04a11031010b003002c9245117800c002100701c000309490640c007022003035a1092401040588401c407031010b0080419541c2d62000380700a000100a000b1260901d4203042847c0500420b01ca2000402d0030652040312049043c004c440589811600304061900e075410708900501240d20f1500044100348202c0000904248025000385500c09022607441e2550501500031005c03a03001092452800c501a8000b445000d0320f668050080c0c1030202d4488100402a1a94040c00801200c110316011f0f548007000201583d4205110341522490b40d654444981d54003281c1e10002c44011650007402072545a600c0391141015078050404800c8240c506200480e0a680043d5a180e0301e8940310082010703d410012100e0b980954507243c03440500c40e50307190650700c420316102d08480e06ca = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 641740368 1250 641739118 641739127
    0x307020d0c180b0909150f1308030a0f0b0406031104202710090b0a0201060f090f0b0f060f18031507030c0f05160c0e0c09031002040f0b 60
    0x381d116400d40200b03150055225400090b010400042010707082003845410460301241a00350b0000700745a000202d00e1500c0c440c1d44501001c0b100000000f07114141d114040d030441e0740080c2c08540658001c250010020070314010f4440c2040c1543c40c1c45a07058052407906500304040f94184041215076030301514002210b03c0221700c1c00e5405816180c40030310503480080c40b030345207504000300d0625000500080c0e00310b0302e4507007003000750711002152047c0015036500018010000c03a034005001012250000140c550750702e4811000300c11071035011014007aa1440c869500c000310380160a4030a0040b82e0a80721486034000145150091101a0b50102400b00c1c2d0b860203448030560961810070000c0460703111803000300d82d28290360000c445800c0080d080034440c0b0784042c01905695003c81c0c1c20384450341040c83c18100380c2e200c00b40c4030505076030104044030002800392147c15241e0040c0114000140d40d00765070400c2c9403078441546840d4051510400041000c4a085404102550081b100150f500e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 641741618 1250 641740368 641740373
    0x16030306121718040e0309090c0306090117190c140904030f0c08120a060612050105061c1d03091002070503071203020a12030524101b150603060b030706020307020d 72
    0x2210100c0705225003040c170b010ba0706408000004040d20702d4040c00c039201101c607902d1301c0d41d0f0001404180d60312038000d08c0340001070101105020010114410300340841f407804030303084a07000103901a1034043d60051003202c1c0030311100c4003440301d21244030000d44401a2908241d0790040165000105400400c0780c1c03c20b040042118500031900c040032104070a43c024144081d8480007032605110305c901090000d1401d804254079070255904071140288168140780c600142c2d00f8000c00c05a91a088803070395414003424490070b102c0700c2000041c4020082d52160305c0c90040c040188242d00744541994440c0c203007041280e4000030354600752190540c001d256054a440c0c01c1e441c0c070200300c0009200300c4d0341d0440300c0b02295041d48514400c50351404990203541d4061070b0b481001840400c2241c00860100414000b9030091480c034030306d039984081c002c1c2a82c8450316807145104000700203c1c2e15a440c5c42d030802c1803040900550380c0310081100640200751078074001035604d01c180c00c0300a01868440211205 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 641742868 1250 641741618 641741647
    0x71a090f1b0a12050a0b15100e0301110c2d0712020f06030103050a030c020f0303160c14030d030c051209030d0c0801060e090c0f160303061217 63
    0x88140602048801c6908075241254003100300c80006400b8001e12a00010f0f003e810106030a00036810901800c00145c003a00d40f039029800c01030043d2020f0750441403200c0980c546850100c0b451182d5510803440034840300400d42510004c02070003010400510903980f0b040b4010840c0c03000c40380034440c00044106110069081030100d020610344502030313404000344c41d1a43c2281113020038821149200410400c10400101d13000a01010707000c0c0e0312a010820000340100c2d00d60070114001402c3c034440c0c0700b5040000c2d29643c0320080c1211000b10061100042141202541001d0700c10209019010310204010030f0b45d964010100d4010180c4603000c0400260245040f1a00c018641120380414948a02c40c0340d52039200c08100c245031340c940b508109980384a081d003181600d019907150703075044100d07104210450034003400c036082c400d504004031a62094403400400c104011b16034408a24081ca090141c200c1c3c185d6404491120402c1c031840b00018002300707001c1d0075100b0b076284441d00d501101d00301e400d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 641744118 1250 641742868 641742883
    0xb070609020a0e0108070506030115030513020910030303050a020903030f160633050a06050901022d070801051303030518060f0a060603060305030405010e1306030b060a0803071a09 79
    0xa410a00c076840c00b03d070401c484040c8a06071070712182141c01a640d070308203001d160310091041c50034402030300740c2001c10548a50007082c2c01000c00503500d99900b0880d00000c0c900e000544211040c106075050410406400d0f010366688503042e0441141081010390100c0d07143e201d01d12516451050004205090590180c101c1c5007180d080329040155401450107140c88151a008035107405030150070702c00350307081c200100383c0603203002501146200d85440c1087d142900800c500c10b040d80140d42e0390141e03401d515990b401d4814068034048041032426591a41000883c2e0131082041e41840204003114240182076450207030b040c540020f281c0e40d140c565440b00c80121440810b54054601408926050f080815001310400c0b031080111594580041d01150f00d2840000c0c060b4000348400c02c0190b00501843c204001c000c1d03c81e034070066041c0505001c4070b00c2900225022154042480080c3c00c01111200240036010021440c1c01000d0b1198070112100700d864151242c901000110481c40600414 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 641745368 1250 641744118 641744123
    0x280b040513150902362803080310050103140705120c07050a0f030f020114010b0c030408120414011b260a0503011401020607080f0903090a080a03090b130b070609 71
    0x119100d503503080d840603400c1d20b6010014003105c50340884402c02c184410102c5042017000340b03441402100007204030b02040c206c2c1c1d1070001810752040c0003c040355800d80194420103068100920385802d003c005006c03102c100d030f05880a074040c00100806250000121000c0d50a10841c5281a40c1d804c201c4103c1840343c0da1000740f9178010261305e4020010380245200b44244a51121341d0003020050b412400c880441a02c0400140707210010000700c800350006002c90303a00310054901d0613440710b8a061405801b040b140100d03000c0010104440c8482c40000782c0e801c50b0034605021040c0c0410303420485810800e030007905c5000d5081c1840300b03584001d84c0000502c1c400c8c0703200c5900c074006650040d02c650400d00c40d84a55002d052020a250742c80480e0803480340c01c4075110b00159840c1c445902c401e40400a00490403888100252051682c0e02201e40009141c80341c01003e020816107001455084c242c0e200303800030745003840714103080107501c02000d041c0e44050383c440c0e072100c00740c0c14000d01414412401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 641746618 1250 641745368 641745371
    0x306040b0d0b10142d0904030c060608030f09210601060c0519020612041b030b0a0c021f0b010215130b090c0604140f280b0405131509 59
    0x241c03042000b464a914841d5101558485031640c0d510310b54085035001425082d0300c0344840e101603c203031003011107080201074402d144200b44c0c0509804030b49035100070b9405801203266503040600b00b101e140980e030050030b4400051800c2c075540851380c2d0414050f100d915481008950782c00022000009c803da00c021003080c08031b80044d6501d11016103c80c0d10320005131000c1c02002c40004003c1c128501d0543c40e25806403d5030300e441d14910810f001c20901400c1120040c40514140440400484d0210048e500541d00300c0c28500b4507240361000c503145481c50b2801d54210f01c9020040c0d1215818810741400950004140c006c01c0f4070040742840d18000f001c11350a1280414420b10400f0000b58040e541c1c41600e14149584460000740d5988412441040d400007041205000c4000301c03500c07141d1484009001c254480c916003000a02c090000384010102219440711394400e9158010100010100003d10b9840c05090501103a41c428049210341019600c4108040304c81080600381001810030100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 641747868 1250 641746618 641746639
    0x30703150e071116030201030905030c0d1707110706030203100f38071506030609110915031005070207120c05010e0f0d020f0105090d03022506090b0306040b 69
    0x840c05400a0291003550018a025507220780c4590f0001d01c1c0c0d4640e0000d40880d42c0d00d00d10750f60045010b416115021616800244244842044100440c50f03029025458144810b00740c89503843c4007440040400081101c090018800b086c404907020b02a52070601e80541d0b66500c0f11800d6240b14850f9100c100c0c4c40403044000079850800748800c8002818043c040984102400d50b110428410b5910301c90355007404208420000f40b5400f5152620003904e200407802d65603e031038a50890303580b08400d44044034210303002801450042c40d03c641c4010081c10224104003c00080f0b176640d03864441c080d00c500d40d541c01150b03000e4001c010100050100307400d101c4c3e100354149401c43c000b4007a44109404034a601c002a9402e260145202180e40d0001d043c1d100500c80613002c2103402c2448144841c1072240030481d402a50300c40c14580d500850094005102004032030344808503107519080f0702282402550402c0c0a5142e11000782000c4498001c601038a070b4442900181c010a107880145501c0f0040d2003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 641749118 1250 641747868 641747879
    0x10b120312010b09060d09030c06090b06041d0a030804060e060702030a030605060313060c031d010606090e070e10140a0e01020f34050d0b04140d020c0603070315 71
    0xc01040322040c00000c08040c1c1c0d9890000851602030425407a034428014000521135111503845920300e02c0c082d2925101401030307901d582c0100c82c1c2da402e064803180011402c2002c43e0a06005459001e6000351459091380030300c128040d00c507002c915000342040f034000045002c0c00a290000c030402c0008400b17480c0039040007039000c0e5882d4006a540703c040b0b410301c6030024480c0703800420b982c4248025a50b00c5c018040380e0f56480018546e6500c8038050590b9203501c01c15144c05849e8003000c3d40301c1d800000550609002010304078039002d61101d00ca00c0b2a00080040041d88840c2201c0140e80659050407000081030096924440325080b1090304c010210b00341c0d102950100440384030401c01e0702500c40030910354140075110050124945011802940b0528124141e90b4100e5507204200080c2e102a649401c0000e0030703002c141000346c90180300030b0280014001010703142c3c3c0880d001c400080403001802036019488001d0f582d0210f01c00c440110005c0d0200740650081244100540e03091120180c1b40d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 641750368 1250 641749118 641749123
    0xa05040c0810140109121a0406020405011121030402120604031e0c050604171e030108120c0705090a02070209040506040c05030d050316020c2706041b030e010b12 71
    0x1110380b0441d5000180000038034400c0f450003500300d102e06960b00c084282c00d1444010030303050b110301d00301c0b0b170b03500b07480c00400070400300715030030b5000302d1042c80c0c09640c076480c1c100014480861004600c000d40c0104619400ca035210000f2810044031010055441e03a5850001910408961150100900480303042004043e030085034015034180c2d071813056494116030b5200f116041420000103059038800d6010402061001c800e6468040d20380081c645454a0000c0d8280080c0080340e031b00c0740300c050100051000003010302c041070040a0b400d5104c2d0030003425440d0250740d01c404c0d00c0b44030f00940100380428031884080d011600055009003c0c60550b0807d80740103a42c88400300d4055884810541000c901440c02141040c1c9006090741c0e41c50035a03c82d0a00302e80100305509052065206024541c0d000b6164000e454100b0340580310042c19200d1907130001e0165a070010b114600c550b10342a40030101d086c02a80180107640d952800050032a62030445900404045030800e9001c2d210910141049100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 641751618 1250 641750368 641750371
    0x90c060403122304090c08040218042301020403050f0105160e041821050a020c0405270303011701110f0d0b1f0e040b010801030308090715091d090304060e0a05040c08 73
    0x422108022400b0000306c212540c3c0420703036009500000b005a01c444402020449a400c40e01514560f40144440b401447c00c220312010130304038994010a0400501805000708403811800d613009001300e190034840750b00c0310260100c040081c843c0724400040140c46650140403194101000504035109a05024110305a0980429482100b8414070040d5510680035240d407203036140c00500b2050038400402025100003040c007944606404911a0801c69401030582804000c81c0919560350501d200d0034040c240c800b081000d03581c10000825401800d4004407035140c8840044281c450707449585480103001c034804041e45c48000b000c1c006800440100d901c0c141201c0320f407102d8140e45801000c3c04140c400341021613000c514030000400100e401155001d0f0700030b881c1e50645102d2a15045a06607030001d6081400008040c09410720621841c0403240c10750002c0811988000d142c07580481e81c1e244114001c3c2030401c20850b003040700a80710315000c030000d081c00810500030080c8809004040c440e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 641752868 1250 641751618 641751629
    0x20d020f18010f3c180e012301051903020408070f0311060a051306020d0806011e14070f0b042d03030b01050d14060405090c060403122304 61
    0x704000351801903010b000d0b00c1e010602c41e5100d0303100f0300030300707859407000181940c041981030f000307198104165043c0d04400d000c0840f101d8a80080c00c540d0f64159000365011500201c452428139001808401d4211031059001007444a503080503802000040b142405292403440c038041000820140c0c59405801078004e030764000b401c480c43c841c1d8851030320000c94100c1c41f001d4525842c4c1c05600940d805c142004002440c0d41342019840c0c04985400d05000052036403101d80113801500740300c00d0059100a405401c04d00900c0d100e04c410081124490145011410400600c4102034240c1d0100f080300c41a01d41041d084082d221781000c90382030500141004941c1100c0d00510441c00319245014080c550840c1604060071101d00300340d9617416402021100ea505050003814400c1c1440a042800341003d440d503119000d086c2424600103010030380700060000c034240d070010100003605440703410582c1c0c12a40c00c0104030b541c4d404d48020580c1d2002203c81c0450030021008402445104180300a100715507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 641754118 1250 641752868 641752897
    0x12080f1e0c07141e040510050a0803030a050a0902130b030f03070c0503010608010e071503091e02010314071b140607051b03040609090e0708031b010f0e03090d0303020d020f 76
    0x2003190100004600c4d50b400640d4001614541030720181055449a80c0c000391200b0f00145943d15240003070318903402c6a1112071325038000020013903a1115405410781000c1c20303c0041c04a40d403075900083d200b0341d2001c00100c21a2ba200c4403005c10b50390400001411402030405d4a540388202e042c02c0600722114020355000f03608200000030030200501c180a159001280501541c5040c00d80c0c40030165130b114400e0f420140c841504002291700e82000404185010f02040e00200780c920014040d10307200a802c0844481900401c00c0c2d480e04003800e040550802c000b40042035001c0e1800b40107109503842c5090305486401c0c05c0110464010f0f00400842001d11340c280c183d907a085180d95528403403405504000345d01960200000000f0703400880e83da44204040d940c1e0300b40c0720780c101861500b01440808607501410283c900d00301c0c00b0710030718601e846120014401105800030441d40d80c071428909d18040c40020114006141c0f00760b06440cd8141d40c068207641c0d035918142d0355140d940200d45004c0105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 641755368 1250 641754118 641754149
    0x60408070b060d1b081506220e12070209060904020a060f02030f0310170303040809131b0e010e0301060e0c0a02030d1503060c050310170a060501030b1012080f1e0c07 73
    0x5580005081c03068200500a101e0309045c3c28401003020a4516040402511015040c809c1c00e42403020094642703d10a04a49030302e411300400082e07103030182546024580c814103110160b150b140d40001550800e061000c80e0402d0408220703c0c51003548219283c08002006010604008000d90012a03011041100072001c4508189440e03200988000300000020400107003a070401e801090b41240b8000000990025550568100900d801400d00c000664110541e1001c0d80c0002c200044440280c0080003a6410140540e411207006404850144800704d844003e462003001251082104448188155286c0100c280c0e400c090030301017101c0302411b004680c034125104101742e911603a403001c01104568901b04000040140802d40c64900340a540e40c0003011480502074107000b107102e890b4941d064035264480c0910102c4d241c010085130b0401c0d101c034801040c0c511094504d100b01c0300225660fa00555405d000300314109068105c0c0d03808010074507000a64010400e81b0490395000c03501441c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 641756618 1250 641755368 641755393
    0x1050c07120c0305120c030a03090c08010e0c0103050a180f06020906210c120f060a09021602100c080706020f0d0606020a060516020d120e0a0c140102060408070b060d1b08 75
    0x3500500040c1b24140d80709102806080f03101e904022401d80c09404119200c3e520b030f0389003600792600007010607010b0f40420101045540d041c0300e040d0b4041c951603820402c166100710b68401c852551038000d09802e13186141602884919811540c00c01c8000340540c2d501c00147c08107056001c031640003108070800e0386001410b004d16840459503602004901d0400f07a0f940c0014a11a4000151507203421140c11500440c9900003803005040f60300d0b42c50350b0741c4101c0040340304010040642d000c243e010040880b443d600001c0807141513902440e442100982c03100705905540546006000c0290750302c03414550002401d54010840741003141c043c000610040e5070721203100281102c89081800164025944010101c1c031444403c10020329102c0007084010764507450a1410b001c1c0c50307083c0c40403059640100305442d1050074951480601780040d00d05440c05132035103103c500603d803018142c4a0701c0c50000e54640d07070700310031501c1280c2e0216548100c00200c20088800b050a400390010500ca12001c1410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 641757868 1250 641756618 641756653
    0x60d02160501180807060203132307050d03020606102a0614010f050d060e070323010612080903010b101d090c0d090f0b040b0712020702030c01050c07120c0305 70
    0x94040d00021382d18031306041903840310300951004040c40b00c0ca40d9405520760004841e081c104d84014410615480e4500c9c103088d045e814a0500c1d445240f03d07040c0030840b1340010f0f801040d03a590248046903c0d80340704110306810b880c1000401d101007011410041451035502e00161440c18282c050b071410807101c611580d501003112020701452401c041c8407001040070386070400703d42019910a03d0b002c15516031505202d481c1c03d10540048032840004220009023445000700c8008003800c0c00300078000149006e50594140e1503200c2d000d08030000004031841c00361804d400c07020b45450301400c0c000b24030011060080203e4280c0b00402d002d540103140c000000d1400c010218040d0080c07900c440e28082c3c411076a41c008240d038180032112242c0303280b982404114180c1e8011312440c0101440c40303017494040401064000110a58680c46205200e1640503840014000d6480c41702801c0c0186e55140399403242e858407807240d0010103030078000c01219041103000a01e000403139105900300c030b0035281034030401103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 641759118 1250 641757868 641757911
    0xf03030a06090c05090d12031103040b07020c094302060106030b03070e061311030a0213120803130510060f0503061605030c0703050904050901022d0a0509060d02160501 74
    0x5500c040c1c6640086d01240b80f0882d03000401d0f80d24240081c400c4100b200f5003c1d681c004503010b41c2e091070304404115400da01070002041044007120140303090319140c44c440d00700c0424601d0080742a0507101701c0c1642100f000c1000d44000350408110000301b0602c3d02c0003565040309009a000003824028071950764140042e100091ba804e120190116945036800d102001600d08451130740d41e500e0b081f00f140d01c8044680218021440c02c1da0269039122580641d51480c0400e5000c0c00b40743c0d2084211001242000c81a43e4111802c48150501c002250604c286081046a044039050303240260008026441c0242241120382c00d50503604107a41d051200320072a581d1243c041d001c1034041000480721482c0e10010b006651090900d1420301807440042000c40c0c0045508000304d0313500140101308408901000d02058404407541c0040c0756003840c52403d98015200c0c50400e118010520f500c071541c0b400b0507200515000383d004c649840d000c1000d1011103100c50b030f003540e80d546090b0b4920000c4590b90682e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 641760368 1250 641759118 641759137
    0x18060106120f02040b0703080f0112080306060a12050c07150c090b0c0a1506031509030e0f2206031b0b04061b02041a010314060a170f03030a06090c05 66
    0x3100c591078503480c120150074202c01d050003182d030820010402180d050b01400703140f4000e640b248403d1802d014160154801030b0440c40010503070034070050005140100320790b80f1038800c0da01c041e265840a001595810860620356154508000400c03002182c968050030849018000f020b42072520705142c001110a41441200081c40448081c8484840c8500a0600c4030564040300c144101a40310f106135864190000b202480c1c545900b08144507021a50800342071000c0400c10201e503d9607800b0304080c030842c10403401a000900f1150181d901d5050001e0302030075031300d1104460384580162900800700d0f400121052074808140024001c0c3d048003010554449400300303860305003482d80c192000355280a42200f10034044144100503183c900800c0b40d081e160603c0c64144032003420001d000ea4011840c00b18050401c2800c008c4030396030b40901c1038203c502c181030030f1040a0b444427007141094005c035045051844000b00344956550310350721060841d40280d8040144a6600c1e00440f039500c10203050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 641761618 1250 641760368 641760377
    0x15090310060e060904050a120507020112020a0e040509031204050f190b010911040504090f06240504050618070215010b09011e020708190b06090105031504031404090518060106 77
    0x64054101510813640160040044481d0052a80d442c48680d15440b1000000a1f00c081110821940c2007503603c1079520214405508001c422500140364103021000c140c03103103407144040340e50140d081c02101c441050045001c4214074003414201c0e601c58501480b038200d481031441c40c0c60f0140076032140c044029071201c2000066460b194002000d04201c8603400c1c8110f000700b00c0000c0c103a85034031500d04c5603885050070200c84456410100d0445500b264421010007508000e01c400c80701009056059a00445001400c0c1d21048089041541c0900c03110284101410900c0400ca40000e4182d0480d2102c07a000f41040e0b0f2a0701110b0031900400d0003207404200b030410000090f0041c010341d69000412441100e40c8556241200751400550b40315910689500400010602804486c5140c2c4074405580c601c40315458240425644d00301c000c110500009498089403c043c850090a40b0381d2200703401464a858541440100030141910040042c100c4030250075542000460719904072080c3da100c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 641762868 1250 641761618 641761621
    0x801060b0f0c07050a080c0a0b03070f0c0809030102130312030b0105070602070215390c101202040b1819090b06070503040303051207090305060604180215090310060e 73
    0x2140e40d412401c052289805103c030003082035100c44401c0801042a03c0092105022000501c01c154100b60810f04227141704000300a069074201040781c110003141c0c03500500e02c00341802c041c0440d0040d820b00c141d042d4000075540600b00180b09445065038020032103070ba0350aa0038001a030848003000d540710b000c15014458034010500301c1d406000d155001a1103030401003144200010140e211102c014810010020b07043c0100c400341440400c02d410102030305041040d142121591003004111951280d4440d60f40f0500d103070303c908645052240c481106540322500c80001c2c0c0016007203038104d010b0394611200101e2070303480d10000d9103512468020403154103d05000741c00010703028116013681c10040c2044000c4c0000c0f0100002e2004502946d00c0c035448692511142421a20280c400410000090028000304074040303802c0e44c0040c4103c1d8005486484100c2030455420700100c042c0d0700407000b51807400c04034410300081c20a403100302c05961000403021201401c5421a0282e55a000d0700d040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 641764118 1250 641762868 641762887
    0x31c110d020d140d15230111150c040f0324050421031808121006140904091e170c070302040c030b030d0c020a2301180b130f0801060b 59
    0x42212910800021441954402e030501c45c0350300b29400705030194682e540d40b00c801400b0584800d01c0c08400d190004100807510122540d0b68003100707a074500c40d0f610002003035200840b402114020540088200100b030758070b0a150401d407085a4801103110309280b40e0349101d454034400d0718030495009140d0300101090201114040c0c149410400070300d41c1d903100e00c3d2003014524011004242c03098100555480005581d503080480140a140545000500c1400010703007014140719910069508546c40c0c4110000040c0034102e0f41201170700400e0384805a858920340c030020b00031003601400c80e8044902e40d090b05041e1a119418403130300b158004102c2407006180581004000e869113181c040b81c0c0185680000e41811440030052001c00d008000346011400c0a072000d6004240c00c603c010781180b0285505040908041c5046040000c20103401030743d248809e4a42000d4000801030b40e450340843d00d106007903004c41e4000d000d503000701034100264005050281405840d503880c0e000341802000c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 641765368 1250 641764118 641764157
    0x43902070e190c05130306060810020301050d030302030618190b030309010906030e1e0d0806030c0a1e03081b0105010f0b0403080a050409050703050a2a050702031c110d020d 76
    0x703a0660f0108001000b800081d0140f8120b6000554091100050340b10f01d040511807502c81c0140765615054018001040f0079a0340f091100c00c5e003070309070501580ea035448a000994014080c2c0308115800924014807068004220656140e4030901d2020014092403404159036409410380e864001168036030180402803103a00181242c1f540b000468025011105c43c01003c24a0151006038135441011182075441d0b120407032a17084402a00038101121083e8040703200f246203400b4441c1e0380d1203010441c4c43e40701d01c2451400d0007140c001600640302d24804048400391a01c1c42d65010148d801e02c400842c032440143c2401d81240c1c080b09890b40303040c1c03959071240380c65000300700d4981c2804401e1000141003d45400b41c280310700203030740d0002403502d8020484801c6559915429042000d062101c44000ea40e84100c0709104a040c1006a191500361002a1034541c1600c45221000c5d084108503800a4001c281c030800071900070705403801019411407c81e502c4014010500000e1510801481d025000d0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 641766618 1250 641765368 641765381
    0x1214241005220608030f190e0105040b070317090609010b0303400b030f0705090d031229010207080d0f080402040902040e060403030b040911043902070e19 68
    0x340001283d0169600c58250554125035460980384400043d0240c0d00e40800c04100b20764000ea00301071070400e4168000074414081c07802901030150300000c240c4289405a03070146003000c400720b041c1903d4907042c0b40b01500d40300d06490070700d800c1d030a01811080c90714020081e079941849408848800c44a01c154100310310a44100c820807580e03041118842c10401c0e142c0303c4c005019405c900c207981f4103040340c8484400c10014403100c00c00100f4000d104442d69998000c40726150145411040c000d11032070084010b104d0080490b00c24a000741e5140fa20500711155504099003d03000d81c1e001c00c0d62018401e456080d80700004000039000040029107e008020701034001d800034000080560581c3d000c9811600c0c03816600016500c800108410168140103440d16500e0550b400d0144141c0780e41c41181c6048445c0d021403155841d21003140c41d0031010403a041420349040101c030b800085510124840d035010809000050007000c10118a440800ca103950040541c254060841c2d0702400c80e9070f005081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 641767868 1250 641766618 641766679
    0x20a17090118080f060601141804061d010305150c0415020c040203010321020304120f06090602070b0708070305040b010302060a110d05180306040c1214241005 70
    0x100c0c100c1480c160070350805000c0191803c84001e02e103203c01400b9613490013000038407807410000c41c42501d560050000080e10320781c035003145130a405041c028000a005c0c0c000c0c0d420001d0401c2540300380340c107609807004c4e0080c103c0c0d026100780e03145015014540d102000f421101403210603002c0204104a2003503504981d10099240306640d8400352035800038061f0390007039100b80d0340e0003034003090a19103500b00005800c0701000c0340021482c1c02e03d400281402c80c107404401070420748283c1100001c0c4141e0750402400079138042e17000c40d6990114606070b00d007035505650990020b2a01e600042842d4000d2013002d0080d0f0f0068100d441503842d503820082e840c2d2040d440042080f002507884024504100200304110440f900e07040d407190982e030b000e500441d40d81c0d941540300b607000800388404191007036442c03001d0b45d1442480414462441c00c2844200300654901807951180312004018030303241440803509880004000301d4181c0303030722420200c440307001d00034164400c0030034803805090040ca5000000022 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 641769118 1250 641767868 641767877
    0x150f041a1b070309060f0216061409030a0c030314030f130f021815180105010e06070b010b120105040b0f061602120c09010b031302010f0e131407020a170901 69
    0x107012000c9400c690b00850b008034045188000306010b0309421080144a09107244010b02d00b60b801c0d016000c942001e28403418083c4140d80041206a100c46012102d030b045000d400c942030344d1154503000c40d000c0b0076803206400003455490004403104540e4200c84c0520301112020f1312988a1121075024000201c000700d07815480008084016103032180c40da102d40d01820625201854054103034a002070b030004074180300c0d2200c0982c410104266055141c10b6582c2864001da1000407400841c0075032140c00c0c4098801101440009104134082004104001d05026541100c1e6688c0d428001502e418800083d03115104400c079040d0303804d1001c06450900141290020000c007250085961078003c48da02d40340c1600320110440242c101140d40d01e005200000b400303461460880560280b00e280c1041c02030404c0220000c0310740541c4500ea154280c40002000800c900071107120358001403280000c102550540750f000160380d130b4008145255032540103400e003101c0850f4004039100702e60060b0b4a160501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 641770368 1250 641769118 641769151
    0x225030605040b093a0905060f0a20060406050403260a05180a1205120a0203070207050301020f0a050f1201080307030e0a1202130b03060702150f041a 66
    0x4100e40100c40c010b5000d040398041604040c4001414031060140c0241c020782d019031000d0346281e155007030940000080c00004284003900c4402c46080c40c00d648150b5200300c01041c44254a81c0140c0200303602d4003580ca500d045861910140c1d4a03400d03010a0007401034200c031000501182641d006158070500c2450840c4a0380342d640440500c1e06a02e02c0130201c00001101088064480703885003907084541c95820145054001c92300c5a550200c07110000c10383c108a64000d11110302403c10b54034101c02a0b540cd040d286010b20002c0021340003141d803800144240301b40000d0b90305040c0700b261700c5441c0c146a03c51034584c10b1901581c01d80c1c0000f0702c0e49014001004901a001400341c081da0190040c0c002550b030700c0c0e1041c14000c1500c6c9840756024030501d011201041080e41d40011003440c1c03941501e8181c200c490041201005112500307007203801d4040c83c010132150f0740e8046034049014201c074030248100d4071050807007810003608460042c11501064080c0c0c900d44c0b00c1d0154164461421184080207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 641771618 1250 641770368 641770373
    0xc0d031d0109051f0815032a03030a03050717010e132105040519300b04030917070806150d0c030c15080f0a0c260406050f07022503 58
    0x420f00c000c044070f0740946180d444c504d103503409000c194009001d0000c1c01c020080344000030b601da060170b07010b00080d0b524132101540100c00100620401d40070085c1a0798460700a828050094070040750700da40012101c403103401c42c04407075142d014181c45c040f150000441d610805001307243c1800540c180c0340c0c0043c0c0d4880b441c40c80b00400510b00c00401c5691283c2e1114507242c140701441060030158a40100064010700c9091070b21404150300910345d00820060034030b9043c10b103a0702201c009024080c5400c3d80c00704024075803c0080c01086a10a00c0d2049a42d00e12866264490041c2e014007001c035042000800c01c08855100c0250303c10600a081d00030b40c060a6880c0d4034030a2144e8000c032014800c6038010003480c018074003c4030318861981400007482c030305142c0700c04140d10001e20b0014130654448141e88024032800c200c1c4e00c5404810074002010b02d10700d85071002d05108039000c8420350b041c0310000c0d00001e01c404556004001c2c640040501d500e4005c09d80c21440e8040a0040a0003c00d1900001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 641772868 1250 641771618 641771629
    0xb1602101a151e0406080406020d061503060302010f020f0616054e07030510090c0503040b0a09050d11100207060212060102060106051b0304030506090f0c0d031d010905 74
    0x54210b440758941c0e40c1c1e42d2600d0b2910101d02c194a039030030404081888208145500042003031382c050340c0105c00582c0c4e0507414544100902454001c048040c4a101302c1c0036600d5050760000007500d000b45c98401c2c031514580003c1380d6440c6402c041d21001d40140000c0340a11141000703c070000822404c0c02e6051855025030544c0d207417034141c03405c0d80d500005520703020507281038424800e4914400c001c000b200d42010030418184000601308404050307591001684014540d0300140152055400c24030080c00300c0c05000f00260015101030314904040008244022124806e400d000c0342d20101070030b81c64208070010b403400300d0501c000b80b4103400740c02d1210b0041c0410f031004040440c812000161140f86503001e902c022900101040e0540d44940010b0002c00d4001080d9880404801c0c0b0381428000149185420342c000c81c1d00080035440782406000b54550046250201e1404610482e4401069034080140c04075070400043d000c281c144d00914040d1004c110a1000b03d0010304240d000103644101007503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 641774118 1250 641772868 641772889
    0x10302211609060f05090f04060905070309060f020c0c0d060e071d150303160813060c12020303040f1137080a1e1704030f0b1602101a 59
    0x20110a8040e82014819402520b000003030407051034074200300901d0380d4002d400e038841d00c4242c61080d10581260707801645e441d00100050201c400741030016082c0800d0260141c40c12000c02c40f00d80b4241143e0f542091b001c1e2007514100ba14500041c8520724411080c051494545503003525420b440311090031200d2010400e450042c4041d1801c0c501e042d8049035211070a00b806001c48403502c818804c10000c40ea00001916070301d904a0000340031110440c5002d141c181718400c00c0d000c0d0340b90320f00000a02c46411510701041c203801416440c3c41d00e030801754120b03100c2c80211002040d003c80e90201d500401c030450789848208201600010504d44900f080400650240030340d415411600d121400940100c00c1082d002812480000c2c030380ca503500e42e87c074580714400c00082c0d40090355a0300c0340c10620800c08803074040c41080388800d0ba922612070030810071a0005032002e0318803400b0300e0081100060350004503000d1004a0703010340a03c80c2d40060110292540c041a002055103501c1d84098594980a080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 641775368 1250 641774118 641774131
    0x412080c07030807021e0a060509010c1b090606050a022d0105040b0a0b1801091a211203040209060d050c1c0b06010c0210030c051b0a0204050c030c0901030221 70
    0x12600d49940d44108001c65070800a403a030251914a4160004d81b1f900c140c0754181e80150034044e440721b040c000102c071028003a2101504010152060002d8105440d031450142e0700440c10070301105480d0201030f5680d1140c481c03850010382c850008440c0700b44010040345032158002201503540141761407814251007080c1c8099404c44a600d0038082c1c0034a0511400b4800c06044e50304030700d20303960008072112280d014440c985080380c441c62420400c1e0385d030080c46030303003450010144603100302041c41d1813682c1100d144640c0c900344614240d90104680e180b060300c0c451a8000c0c0781c5816940d6078800c1c000c40c404500400c941900c10701c0c072117401d659117907880e11040c0b9000042d100307005080350a10501e40308014089a05120100da5a500981c403905800544503c4a040210755810800000c541d00c1c0709080c0e55020a038008142c00881c031002281c04079895000b22000c5c065500e03011241d801d070744020350b2002203242c01000101e03030550094018007890504030000b00c1e50b800c000b010140701204200d07881c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 641776618 1250 641775368 641775383
    0x203040e04050303061206010f0501030b0f090f0a060f14010516080f1e03040b0403050703110d050c0607110c04180b090106050324010509130507091b140412080c0703 73
    0x200825803c0403036406c80700380040340007014075524200d021210720106001e402e0415464224640254440b0303030b1464800c040142c1028428504060340c502c00c91000d6400314034a508001d40082c0c203031811101d100680720f0614103451a4081140103460310341c848001e80281400d415080c80108502034080c21000c0c82c9003035144d41e11041e1030707072a1141a0148000300300050060051001103400d16141ca0740c03103985818040c1d82c4000d141425180414882c0b03201b00390344500c10072080302d642e00a010f05225992141110120b80345d141090300d541448040c514031079401089580b00929098001e08440c0c0500c85a060030310800e0b84a00c6030140c8121042443c60391509400c02c85030804010800d4001621b284046001c00c0080540e00c0c5100d043c4200d0b48682e100b1000f0030310606c040b0408200f02a40071045409455580c007848001d0544011004600403500e51a910401e010b031049001e0280841c134032a29141c103240071520b0648400d1812345003c0002d01042801a20800c0303600040c5005000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 641777868 1250 641776618 641776621
    0x1b010309150f180c031e0501020d022710180909050f0f120414010e04020a0e030d020c0105071e0c031b1406070b1b04140f0301020c100203070203040e04050303 70
    0x4220080d0361059103000b0100c003d041021000c0786800c0800e40542c2d5112a41c0000c00743c403501d01040051015001034095403001a580316900159401086040202180c0c03480400705400d500c01c0070440003840d2600701c0101c00f91202142c0c4a120702c10a0700c403506581d40252070300d464808044980f0f4400c00c40d401d900c903444e0001f80d03450800c584a542d98480e8010b200c28201c2030351a50b07080c0540d220310110219514081501c50b8050700c146100c0c803001801c11512482000002449d000c0011a84e40c081d029117891744040d1b038808203807070910030b40684401d840e00c072050340d540c00e407005500e440725a04a441d4000c0e4002030805008407008600850400420070140f03448044003801c6a4000090764458080ca40c08644942003074840058020050000385c1d0760b401038440501c404a4050303004820700190110f403540c03481c107a000e031080064a0360b441d80005401814200c1c1300f0b81d04180615840580c4082e11001d864009560000c0f00c0d1040d242455511241042c0d040c4080c3e804440c40e410210 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 641779118 1250 641777868 641777891
    0x11090310060506070f02030a06021602100e21070305030a080109060e100312021f02071103030a0512150a0f180606080a091a010b070510020304051b01030915 69
    0x20030040c0c1a080c00810106107410b00058951142d0351000746600500e1034260107550701800038104098200e071082d542c41402c1211181c0d01400f1100481c4a41e04400300155014440c4d100c8140b000c130040c4c03400881411003848101040300d03c0003292010301c1081d0f0003000283d4140003500082009844604030307941030071440d00640c0c00b1a04040058440b4508006c401c08141a5200441ba00803402c4029401600d03002c0381020700c12400321903a4441e00c002e0300702580c8594000c0a065025481002060189008250b01da03c645a514030010741d09111184e806400618495040341c4980d0401c40090f007940c0c08140c0c4a44258864070102d80407580412801d0010100380b040300700c040404004050030054060000072002e06144006503136020b60b00d00300048030000ca0f06400528078600340301c0d0303540c1600340301950100008a80c64002c0004500c6040c449000b0380703000c0d5038032801a02070312014880810300d80201074015030401d45c84448000219680e050a130400840355038010401d0751100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 641780368 1250 641779118 641779123
    0x120c0308070807020d05180d0c06020111041a03092a040e03070f0605060a030609060e0c010801080712030c020d0b01060809150609090102120937121101110903 70
    0x1007444007032011030003c100c422580821146030320f41007802e200e81c0790b102c61001240300c010010039003600008450075070424443e64a918100b00d034040e0703000b402065004d849490703240c0154407820b031980170286007101c4400c031854050741c2c1c8000c100f8101c0b0010000002403000700314102c1c040188221180856616071300301400303000304140351480103501d00301e850b50b40d4210401ea440301c0504100e6540e0702143c45907032a04602c500458009206020841c03075400c2c0800105403001e2400000d100d504060365455004441041c1240c0140d0050424079140640126244090400890410210411325801a4ae07000724814205024100001627581800800f40c4440c1016100000507401580c8c041114521540044d0344134405440700c900c1c0e030f2200010f081c0603001e82012009104404000c12a02038800200d4028240392a203500c04003600046292540c143d00741c02d103011214045622401203031000c07000403120003035444d0480300c0400720b691503402c64080e0480720082c8030000640e08642d1071b08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 641781618 1250 641780368 641780371
    0x3010b0309010b062122240606140f0f0309150604110703140403020303071208070914010c1506060507110612070f02150109060501030c030b1507020607120c0308 71
    0x4d407070340c0d0329002c1010500f16044c0004200e81d5500c3e803402d00020710765102030503040c100502007641003204003180c0ca0704400140c1318010351200049160741302c4c03060380145d00a003400c843c01c5454420395803066406a070f012b9801180303019109003040184180c41c00480d0b0040d442507014002030640c507540155a0f40d2000340280116100b5400c0c09000101d46289804540d50307a41c0c541800700841004000340a00c9000b140d0004e035040c00301040420910411030480d00041c61550f540c038100c3d0390342110507984613909000380d10340366448406801c0d03254002e40c3e62820880c007680f00c004c00b9220002d542e01c15101c40c0d80040d000508080b0b6150208500120b00340d441030022941e55052451a02c0c0901186000a111034104685502c4540342c1600078000d080d4000480102c00038a0340e100c100000c040c111a21803030340043d1403d0001c0c1074441c172074410024000e2000b041400d20145c481d000e9882c640211200780ea0001082000c000004d6005048000013055600c61100b81c4001d0b08018040b03200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 641782868 1250 641781618 641781641
    0x60201150302090105040c11102c0703060c0509030703060b10031b0507020d0804031b0902070327050301050109090308010b0304050601090203180105040c0f1409061005070803010b030901 82
    0x500003030500059550034646030544100307031030008414040d00d1080b1000c0358000000041400354185008100c2e603950000ca034480018240340b68040e40c10441d03185504000001d2000c1c1c3d03080340106000291081d007181da02c1204900d80706041110ac02c0010341012403992080b1501035540b808021541056096440d4140c89030804011a0048003c50715805480c0e9800030200200080c0c11011903591030b0300040d9580e001070502e030f2200d0700e84c9028404080c4034200d4942004a2400c002850601070003140c0d442503240c0e0f90840000c158024080a0403007a05200460492400012820351024800d441c020210004045000d03403080c00c4c0600008010380044810f60b0080003080b0115800044150440d506850010307600d40d20400c003d854003008100c07401555080006000034006100000c03400e40e24400c0850615540c0c0d100320040b402c001c51403240c1c02280712400510f80b460400c0929516408604040e072400c5d46580d10a104c5500036000640e40100100034070188503824450000c81e0712 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 641784118 1250 641782868 641782901
    0x605281401090911060a0513030c030c05040506030c0925020c120703020306040803060402120103051506030601060912060603061107030306080d090e250e03060f04020105091324060201 81
    0x20b915580c4542c1003201021740076031300005282c1203540c4603e0032104800e000c80da00035030042d103a14045880f50b403d032005903050b049241c0c01007030b1381c81c1a01c00c69010301c2d0020000d200096000b0144203c042004001d03201c1d2030840e5080c1c20105010394100103011070a47d014100e0400c1100800c002401e0002d15442160f204a80034401030310001000c64005401c030f500c1a40340e44d62440058081d100320403040ca50113041c4000082006400100e020450328449a00f000e42e075030396014559100c03001d1041d500001c58014040103e59403102a01c0840e901880c0b01040190f203a85641f400e4500c01c509801c0c9004000404806042d454440e40c4041c081040242440218110004104106500482c807080c01d0210100d541c1c3d0b0000b81599203009079240909005c1121071401400904c43c049489000340180e90008801e500c0259001e8403480d4141c4405090080c2d201c00e000c040003160b410801005da543d41d2641803a05000164091403059103440007019040500081c20368004241d00440c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 641785368 1250 641784118 641784131
    0x30209061804142d06300d080403080f090d0c1b140909070b04060e190902130f081c0c0f26031006050f0d18021207060c060528140109 59
    0x150b43c5d00500d030091442e10305403001201100c03640e8801c006e60307812540f9400d1040c6a005c03126260003507490b0340b10b13a009444001c2541e2703035a01c00c030721b01500c101e6036500c1075000312241a007841e00904015101d1801505000e5000702c440200781d000171050b8004003040c0c843e803a250000ca1902c01c0815034011007502c09000c01618090540e21580214003079102400392010b070300314280d01c0360f084000b01c900300951600395450f92481c40301d0096014044040c9a06000c1d880881e5118114058108445e901d00080a840000b0f031341100c2c0b0384454842d070608004103200300f90f000c6001d120780990410b005843e407a861380103100f500341c02c5c0c60080c0f03840284803500740100304144181c3c81c124402c0321918100182d0340c1c9400c100c2c400461064031100c029880c54580040841c403050881d03a00320314403c1e07420880008403910b400380d45407840d10a01001a800b0000302d00041c0c1203410650700715181c520300001c040f0b042d51204409a100c003140d48021030784c1d424420000f460907101079006200d400400c01c1003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 641786618 1250 641785368 641785381
    0xb040207150e1f320103110d080712020c01050a090b03100305030706020a0e10020c130e0f070f05010c0b0a09020a030b01180c03152705180706030209061804142d 71
    0xc4c039014400030b0310040b003a035504240c54407180f0445107110341c030000d500d584502d146000f02e20059000007030070042c40b034104402e01c1035000c1c8080719860400c85e00c500412515105400005500040280d01e0710402c0d08800000904208090300b80300d407150b13002585589400c1002003041d010760301041c0c8a828017081d812032030740d0085881081920240e400c90487c0300085e002c034001d4014442e0354182482124520360840402046400a88684901c4420035030354401c01141c2042c0d015101070101c040c10000b00b040000154840f0102520103802d003030740d256481d02c605c809040700364441c0712642c1c001c034000d4500c1c002c5031007442d00100f81c900f4102300026100301c200ba0402c02034094421207800100ca000032030124403200820403400342c031081c4403a241c5084810030f251003a6000001620840b880460340303134080d000b5070701c031140c01400d41400d09180e05504513040e0010018190080d940c0c1000360048022a581706104c0c01c4031260640341d0312045d45912010200700201c03a41c0c0c01e00400140a00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 641787868 1250 641786618 641786711
    0x816150315090c0309020604080a14011b120f0203010f09050f010609060c050f0f070609141302160b0a06050310050f0a050402030724030b040207150e1f 67
    0x6655880c2d400258051018500703600918692101035070181c00810005803800f0009a003c2c1e550780b01d04215910740000342c155a090384c1c001910524a0600e9031034030848640316010801641405a40101f0522001c0c036008080368030030703080b00007000c038a04001e02c1800702c0703030003016040001582100384641c5030102c010205d6115018080401802c1a95401400000c01610441c6890300b0151a4404140c04c0001d0307444120303100d0380000c140084800038480d19912480c0341d030700c03101610585203180c00c840180e00070b50003010880c3d000c40c2c0980d07140010130b0710307020514412841c07514001006400c0604040c90040405913405c4410f00701820018074901c500300c0305401030000303038000c50140c5031480000d00700f04081c0c2140d074003a0080140d104211603010844090b0300000e460805c1041d40c0181440701f40d110707442d000f42c00c01f48500c03031070503401a499109a80b80b00301d440c142c961500303040640c111607903c40c421548016403180340740c0c4011074590345040c46c11100341208110703040c3d10148181 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 641789118 1250 641787868 641787911
    0x3060402130b130c110a050606091b030702061009090302120705120705030306010f110a03120e03040602070807141810051507030207080f1b04020408161503 69
    0x24000c011407001d400d080c070324642000c000c649008081e000d0708529045040024500110140001100c50740d998071100c00128900807203941090203000b02e641d44005124038090040c01a03500740803070761060903100700010051030080d0025070150409003812041a46030398825004208100c0c03414922000107500010070304000c103140000d076501c50070142030807402c244541c8956180028001903410400070040010b51280000741c0301c50030413010a43c03044521103045a50014268420204100402d0003142a031104031800000807031241e1610a4403400c50b0020b9001102685c030682c010b002c990824000440617105040000b40e4890881c000500b0800710500a8140000100003040d4980f50740c0f40c0113000b410003d01515942030015041c01d8250340000030540c01030082c4c02010503114000f003200d19206110038010a0341d000b10143e0441095419266a50300c079608010020315003005010040060754035981d00c2000c0b41c5000a230751900d0b800c011844003058a4080303440300e44144500402e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 641790368 1250 641789118 641789123
    0x10806070923030607050703110c060315040b1215180703230607050c060f0606030a1505130e0d090b12061c08130614031f330509030604 60
    0x7202d030840481061000124680185800d0700800c4204984e0640000c01403401c0742c07190340c4039249595440301d05070b2250581115141d002c1d0301080410101e40d100d503074803001014010400586c240340480054140411942901b906030480a8401e00803103040104550203e036822030040c2e00408009107035143c04c0b050000401c08044006010b030030900b055003007045210310b5811126207090880000d400364001c0b6529601c0c5104403c001480c1000028200303004020290616017151504503101001e08100540c20100340501c04001034a45c0e240004054103107028600018000c6100c003220b03040020000c140030030301c50104800c004000c0d03d0000c46611500e110301c4202e550322804001020101043e24081c10f0300c2401d618a130034440360000600b0104c00c246c0100f644c881c2d03265020b65402c903d8a443d107112002c1440011020042c80c0384d410035401808d8100050142c039190524144107049060358101ea025085080b112003100114050070b400c3d5060060620b601c000000b5034805004000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 641791618 1250 641790368 641790389
    0x15040308040c09020301091b110d1103090d06090530390c0418080307020717060105040c080112200a0306020c0c0d0c0e090309100c02090108060709 65
    0x8091180356a0b495000d40444030080d903481d40d582c2c86002c0a0700748010000503070149058083c4245001d02030032102240b1003c05000c0c900039401c020303140c040002e908071880d4001001407588030381c0e030380c11034481f26482038900090100345030900720711300026144000483c501040c1194041160544003c050480c1403c3c0c0300d031745500c0c002c200e003c10070a1420011a010304c60001c401060407651128622200c1c10003110300e210070380b9040200b0380340b01000d840408052942c06c100883c084000455010485004a80e4983e41e03800d212510f0300c48440341040d441d00a500144030500e0907000d03032030205c0420701d003412a80d4180b80d840038152081c400014801d502038100e050140380781710900310030450000c0001d224a543d90900c4c0019501100200d42c5078014101407001d00d19102041c011643e4001503409180b038280052f2010071706e40980301c207140d4841031002805c695188800002c40b0101c82c0e49a800b81c61a61050000400068001d120503800a00c10410141d07403092180c011103120031320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 641792868 1250 641791618 641791621
    0x3207120203150106120c090f0902071103060117070608010302060d020a02010b100c1b030f03050a03090f210309110d03140c0304170703030906140c1501140315040308 73
    0x2803900c00c284011000916481000183c4140c100071708150b00064002c0c18130110340440422908901e01d03005030b62110b4140e000500c00e902c8154098155148510561508242d0390030000381341c0442680103541040405150c41448081401110f00406242c00c11001c02d50443c0d00280e01030081c0c1e0391006410340d01148200505100750000b0202102c003503c1142c514000100080c4000751741101aa15841c0c5082d0100e10b0704000a40003045a03006852046070514954044074264082c02842082589864294000c101007104480502e4881c1d903c1c85c030307a480410201403940100c60010300900d45045007100115080ea180020140002c58194214207118582901c0404c1e00d4044c64a04110124a60b45400f60000040055407454181c031040002d4110f011642c0d8a2940001400902c0c410001c000043c050300445d03214011407800e032402c10000d000c2c01494030305014122100b01300d071200100800803d80c00f445407110700c10382c040c001840d541d81140038000030180001341006407190 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 641794118 1250 641792868 641792873
    0xe040e030d0c0302030601030608060903040b0721030b011e0c0204021309150611072306040810050708010f0515030901020c0d0309120c050d1218320712 67
    0x2003260a01e1030307090800c000550040740d004000b0340080b03401901003443e220002c43d02c00b0000400031b10405c1c0f02c2009601d0716050188450b041d800c1407000321241d0640c0d101039880c1400401a0301c814924542e070000d0040039020004042c420a0242c0f00c030320180080c0f1004d03199034040c1070201502e0f0161000b40e5507154105040b0800340d52035010a02441c0f401300c3c0c034103200b600b071040c010884400740d5400c05880c0c480b000b500e2301e442030751048450a4005070003a940344801e505048403682401403807581007560320a9010708210b101040541c42d90783d180100300445d83c000d60320314003400d41104840b01941c00c043c080b4000c0c0240c0c21040e2803040c004000516400c0c0250111030b0606005401c0d140301c04107038030016001c0c2c4030411080321101c03d05a48898014824021034039060340240c02080003020075641603c00d030f00101d001400c000e40b10220301442036815084541c0151103001c0700c120700140d5003841d1a41610641082c041d1540070307056030b804000005104004c0d94414a02040342e40a02d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 641795368 1250 641794118 641794123
    0x50408030307110f1519020405030607080403090308071212020c0a0b090127031d01080105040b300c0a050f091008010c05040312020703022b1e0311030a0e040e 70
    0x8040041c02ca20170080e040d0660010385901c0c60081000164120003490140c00100a034010b0b406031580590004c0001744510b845445150382281c028102015003503143d441e003001c0c5903c44c0f081036664115030110182c680d5413107141203044030300002d003c6052007818102261200c80c0d030403002d4039030407422001c0781d0400c50070340c0804480c020094014500380040c0c0042c62480010b002c0c2076000c105445a8041045120200c03c014128140d5803484243e08100c1080000c0051404142e00050210346183c28492030200352401d0003450b1020050690900c07881924140c0005051401a624007004000503100c05001e0301e6000b1040b10354645a80d6944440114001c0540c84941d146d070809a03084001e940080003082a00c0c02480c0072130300f41d0705400050740e54032405e100094100e4680003454400361600c1d11009091044000000240040c40c1c58413500f1203c21005c0d003444410402c60721f010141c001400d00f0103901d0383c401850134030760107090103006c040349101c0c1c0c1401251a12940360150905 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 641796618 1250 641795368 641795383
    0x1b0b0912030f0c01060f06051612120c05090301150509040b06010c1205070c090e0706080a0b03030c070e060d0314090402070b0901200903061b19080a060605040803030711 75
    0x52070903641e128480d442e0442c0c080c00c911b2040c042880d04010300803541922500031100030611b010306001e4140000c0d07a1701ca41008001d050403040000e15001c20380061f480780504e800303035801942d0300c83d2120300c400d00700b40c00c4840c0901c0c0d401c0384010702c00341008140c4403212000c0d406600720702c0404d15a920701005a0f00e0746018803000301340d02441b0028100c01c64004011b800158091024010302f00e8442c001c0100b2140d1b1680310070055031051508000351031040116552110216502048542d46407000c0780c42c64004507810279440d00075a1050054901301d01c2c40340d61003c42110881e00100081c0c5018213000101c40f600d0003094400920b5400030344442d0100d403811644004081064941040f01d98002c08841c0503d04d018403c01948600007070010050390b0b032014008000d000345485801c03011541c2c0c3c021140340803040741c0900030040c100c1e151100a44565005031612089807400100a02c00c41c5e4482d00240240401880203001300c600c000300756544123541c0d0500c05418101d103c46540340580 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 641797868 1250 641796618 641796637
    0x1005070314010b21060f090402010e21100213061d09160305161407020d06060e0f060117010e0603071503090c080703081c02091503041b0b091203 64
    0xd40000201c0106400060500241945280782002900601422452803d80d1010342c08110400c0082441c507100d1901f0343c0180c41410315507007404000d03000c58414040844040a0401100014103401c03030140a100c1460000728170451910030300e44900350001380940200300c01c00c456800c414500743c82030380040444800c010541d940501d000103216020020500202001a0810340440d45c03810f6420f80740502e28a80f501c4641150007000c42c0045a5080a03c0503070b0301c41e00208070003021540c1c40c0300e124054040701034191128070705000c0f07803540900081c11050401040c4640d83c40650354120b9658150f9118155070303840d544900c0006071820f002038020b641d0307006110390041d074070f19090b5020280141c0306800345905240d40d00511922102c040c4070103045860308011110f0420300c40d010b2180420f90489005040c0f060f15408141d0203440780d11850181343d400014802070202d5045640103525424441e6070b9014104418000503001e0102c106020368a40b54001841040c24015182e00d0794 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 641799118 1250 641797868 641797901
    0x40209151c051008010b0d0305250f030206010f0b040e16030e1b13230c07052a0d150b01090509040b010906080613021005120711010c050c10050703 65
    0x408404480141c0034134828190950b1131b1001110342800c0c600188401c00e074258136a903003001d011a000c04101c0d00e003081d02400c1e03034011424143c002202c0750785a400d528041d5000702250745c1886d080703501e41c4903e0341000c50902d178248420004032184030000d41d4000441101c004048440c1d18040d4050101e4004400d805e0103014082054104524080e0558840032202d01420617107034000798080303d450061407510b103218201c4204101c450400110307000074a80702298a4014192070b850708000c04010703036030a0203600c6610401d0b07040a0030754101140c0000c4942c0038000e0103d0360b84812020b00d45541c80a250344641078000a6802044a07a00402000d40b80701070916062900c00e10440c4240500c81d08140341490104911800040c0b09101d54043c1c0e500c0b20110076180c080001040100181d481082820842240100320518106008a1041c0c80e03104070808846103040c00e64800344084400c0010500403000c070320400203840052501c1010700040c2d5910f58903411009400c20079a034040c000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 641800368 1250 641799118 641799121
    0xa080f0711130905010614010c020f0a1a0301050102010c03060b071209050a030302061906060c170f0c011b020c0102030f07050a0c0b03040605060906010503041b091a0f040209151c05 80
    0x42102e03000300038210f1084c1c0080012580703a0a5001c1802c3c4c181c03035868002042c982201005081008405a44c031100902c0a04010303603440302001e90038a207811425a0940200041203e03507024010031800744030740d0409126050070940040310a0007990805003841041c00080c000c403c0c0106d04440103418041c20125000b6124280030396600000d599112601440e8a9142c0c6050304070710a94064030031580d00e030b003800c40c0c035a240c4200e030b0003150b00c403a241c0560030004580e810410500030441c1818040000c039003101d03440c01d0506e418440034504420754201345080c1020f683e000c030446584422120403983c551340e40c1e0030090714264141d400140f00780002e4001003000250440903600c5640b0425050102d0355601c4180402d814060f5261408141c09001050006a05202d416901d5013810711184600c3e0352000884192803586202416030f03886003900170b80ca802c10407003c00001c1030aa030b06600e0701d061000455152404001504803550000c43c481081080350300e000c2064850100c810300c00d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 641801618 1250 641800368 641800399
    0x1141e0c0a11450103060905190b06060d090c03080715061802161b15211107060606050d0b010f0206041b030b0108030c0706020a080f0711 61
    0x5440c601d100c15905019040022401450401100600304040504546611120301a03000e19a1088203400150150040800c1180d6850302121802140501e901007149402070511509041708150704030050a502d42e8214041070064041e00e800c5041035030440d40d81c07a03070896054010007906c2c100902c031110844000040c001a98041c00d90f060040c840500c00c040140600c42c22200c040c420285051b1000400d4003003091158040c110f07510000e1000c40c50040e10740d071040e05070b00c807081c06940c409400c03001c10b00510969100c140124800e034101080e040035003076a003a0800c011111402c2000c5d4403104444e001c805001c0039102215404102800500e44402001c1c009400011650b024103180114001003036100f010094240c031601c0d009400c4507104d9403148000503003c10030603415480c1001002000030507100398240244801c501030340c0c0318420303480101c0c00c100e1540d02100c11940300040b490041841c090448666064070000300d55614030324030300408003a1094215682c001d001081c400c01c03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 641802868 1250 641801618 641801623
    0x60f060f0a0303080a0b011e0306060807020102090108010e0603121303051006030807170c0d021b040b1507030e120a020306010b03070c060207080408010c0504060810030201141e0c 79
    0x54041114140d421811580600036041014032010300000d0646012032000c03145580040c0030040e042c5440503510845210840e07407903045541050000c0e0781c9540801c00958050401a045601c41c4003e5203005085000206421710600801c0916140540800c0d080d9901300244103d10500c0355085407100c0b01c00c1442851605c0c140b0095407a401800e0050807401014410b420581c0e0b40000c019040c038400e0f40318008641c2244440060a00302048a518410001c0188004c60090f5038014420b82c00c00051001000c6244a0040e0103903041c000c19241a62340c042e10141510b40360712010743c0700d00e4a41809c5a80d03100d80440c60760040708000c80803e81400203c1c640003158002d03401c03218141da803076150005d5031004075441400504207100c6240000c0d130b00d400034200319018503905d60400384c0380d0210608450082c0304041c04103034001020000c2d40e402c0300c0c0c0d480d8840780d0400382d0701c1910300d160000f038484200102e03c000320b004c0015494a0ac0700003d03407200301c1d0002c0c40e100c06403185c070000c0e94240d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 641804118 1250 641802868 641802871
    0x51e010e090d1403010e0603010b1306050a240809150412030c0e012c060409090516030b22051c03060801050903160507171506100e1002030705060f 65
    0x1507550165940c60b2804a02070940c0b8016042503a4040b85168a408003603010000b02034003155255488560310b10b542e580341c0400c80c0200c003d00c240058654645000c12204484076400103440d64801c03450160344280c03804042000300f400b401d0140d0f0300e03620070004a0420501c3d1540d4480b80c0d01940034003003881116170000c1c40e456010b1314208640c03004400c00341d42200f8000030150010b20394001c070010000c00c64980326150b0308003446c0700107003141010002d5900d41141c1c00400d08540c3c1c80120348140441000459211800200c0031501a411915404468440142000110000300392070400c2142190451410300780c110094079085040c0b4240c105c00d01e0490750440000a04005011896501c1072040500910703185006501e1b20202e1400149012400c0e4070580c0c903401131143c0010080b0741025407086000e004009004000c200020f450108940500748a000300020308408489030380115903e201e11800b15a50b1350000c0130390f02d0403495481841802405800b0310030078004090300844009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 641805368 1250 641804118 641804131
    0xf0e0403030513020a0b092202090a1203080105210102160201020105060a0609090c0509060a090623090d0507080a080d0b09040503040b2802030306011d030d03051e010e 74
    0x50040c3d88400340a12900401c56101a50140741401d00b00421141100103201300d000c05410f0150a4511016840d1440c184104400285400141017405e51500160500141040b000400ba1180032a1002005020705004513070040d89040000d60345100c080441c0c034103032206280259910412288081c1340741003800d80032400356080c00041451403602043c0310040d1845551a00480d40c5402801c0303003e801e00031011001d1106c10008506540c81d0701c00204542265519120013943c40d260009140d0107a00140080500c0c8500f42c0c01c03103580c02c560489560560850f90102168042e041c8a070910440d030340205280c1c410700c3c1c40740381000b0048029000b0034100e6002004071a5015041c0003106208960090030354000700812b0080c0f1001d03002611107c072500c130f2503584007000440c000d000b502200400030090703800441000719541c0d200c8a10842d240034400c500e11965503d0020a5407403088420f03000c03d041d280c00014581401c003908400e01091f0980010166580d5034900c01c440180944d0705 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 641806618 1250 641805368 641805371
    0x507090522290114190503060f18010204050108040f05070b210c0307080601201603121416030e06040f05030609060f0a05130f0b070912080301060c020a0f0e040303 72
    0x4010200c003000d066a4125031841d280a18502540d400b080718100280b801c2c1700204824200100341d50f2802c1109500c11280a43e00340303007030300304613281c0e82c061085034110304101e030b004200c181f0150360321185498009900003500c4641011514159003828503079001003107181d4000c244000760300300545410004400020781d11003d912a56001e85803032000f214841d000c510384c0d01c042044c0307507c034020103e10500c10448944401e1a1301041d0350034100050b02e285050500f09005009001c425194104281d01a050070002c42c090507000008030700070118011070050142c41c8183c01c0c14014010702c4c00744100242000e0352a901c0f00d86401c52020380340a114001c0c842c60000400144000940c540036008891149006a5901c2490b42c007405000740b011018815042000700040d00e50700085111903c60b0014a56070316041c0002008920154007a040f942d02d0106090f01045001c011a81550400d11340f52190f049a400072415809090380484c0c2c1410f24604001200d544035100c242c0298804e940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 641807868 1250 641806618 641806673
    0xa23060619031a06130e0c0408030a021b100206011505040e0108010905150c091e090f07030c020c060301031b05030a0602180108010b1602040e0a03020c0a0609030507090522 76
    0x148044c500130a1082640c8a0a0000500520303524407006035001500c01c003550f1038143c6418100342550040e04c1d103d405030340b003052100c5a16601c10096807003800306550340c030a80140392400a550380c1041c07103540301d1401d00c040f0b03e500641c0300d00101c03005800d40c4181c843e41540e40f031007407500070b04581c5010799490040c034400740044029182d040d40681c007011050307820b0840c0b2200f0000d41140d0f03c02032a00481c15901294502e0f222005458840c405451040d02a480c2500001d002d44420485d035000f15042050104c42594620302a81c2c10340f0341250001e05121218211040c8619080e0011035062042400f140e0410409030000c0c0180d5480352041070000d41d0450055036086028002c200455000b80207038100b0700c88030500810518002000424545400000c4a061245404003500140c0012213120510300300742a074030006140302d1510385507203483c0d62074041d155082e070f005a038051394441002c00c0900d01480d0b04100c80e01c12403242c038103400040d45031071194031055114082d070300280c5d0007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 641809118 1250 641807868 641807921
    0xf14030d11060109022b02120702030406020d11011d28020a05013903111524150405101d220905030a080a2306061903 52
    0x30068503424580040540784d00709140d400c00307908402ca0881010114440f416848049040703008079100740601d00603030f01c100500c828603142c200204140150743c403c12003005015400070701c003001c50040d031401601801030900d2081c05042000c090082c0c010381c0e0541c4995801010801c1840a0a00340c1d1010f40d214410303461400f5a16841c01c00f95114408101c200680d50081d0000980c9422410084070320400c400b10300c0100c0c140342c501c8044051a01d00d010010150408e0a48003030440c202d0040071110000b080003c036a110050a9a40140043c4003405e0184909800700b09072840041c1508001e10340300507582c0384c54005100c7d26103c3c0000882c2402c1c554021408802e4002480c0e000205840002d028090340e81000200c400c00d4010b24402030628070721b20300c50031100500c60700166641c1d01c3c55050041c00200003806000d00b0900e0081d0b5822181610341400c2c200d00300c00f2044a02580e6510000b50741805030850128800b84200034000710319078503601c03400e541c0000c1540090419aa032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 641810368 1250 641809118 641809127
    0x60315051f0302180c162006070f02040b060c030d050601081509012318040611041508040809130c020f0f0303010b0304020303040f0603230c030f0406060f14030d 71
    0x107102c081d400445190500074500c211540c06a8071407000484c091402c0e0b110841c200b1101006e0005407400c0c0901286050780d00c0200000c9401e40a00301c9044e8102040c6840f0070f00d940a84113402031040380c0d5406004501c0d103400090360744d501d9496050325107e9aa4090190140104807031080c006030341e110004201c3c10581c11a104181e00107440c0e003070141c0c01c0540b05803801d170400e148001180001c490001c1c803130740c650320400000001540d401015080c285010025500d070b007844140390020038441403045034034546007101d01c452030346402941c41d2924209028288140407031283c101d00400b10f00c3c0b409000a420410f200041c80c1e0843e400d18410280c002e403a10312030909111b20360000c0004000030300e103404c040e580007400102a40d03d025911015240c1489269016801003611001c0c81118000300d120849a0076144005081051070001100b29182c800102803800080180b004075081c00708036844440680000191400c1c3d071030700c80b4500d1581d80a500000b074824802c1a0080384428440e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 641811618 1250 641810368 641810431
    0x70807030b1603060e2a0d020c0708030703020d0f03020403061113050312220b070b011e05361e0a09020109050904050f011b020f010501032406031505 66
    0x160345c1450403d03146e134035041d02250300150b010300c1c007410394078900403d20941c0401008441181d03000143e66a0740c1541c01424010385900c050181d400912142010a13008a12140300080a140c103040744060710100754000c0c051504080c2081d4a23008016407a450b10708010204000401c83c0100403076616010161f43d00054034101d226140e003807284102c40424080701c100444141088400d40c02d03101c42c048141a000b094081d1440c4695000400c02e146d0f808401c0c190b103444429507800b9075810300c404545c108003151a801c00500f82c00540900004401074841000300d10081350003001c0c00c110881d01c004040e6564628540c8031090086080d0140c18843c1c1610070340d068594054603854201048101070700140140d8140c0a00030000c000e00c4400e01c6003c24022064000d5841d2a242c103000038030300502003801c641140e240000501c00b082044180318801c00700440300900d6604103416040c041c041580c00140380c0314a1404012468046402c290b1146203190b445034100410400e80e5a0403022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 641812868 1250 641811618 641811629
    0x2070201180b3f01060906050a05030c0a020f070f060f0302041208030402191d011721070227061e060a05041205060603010501170717070807030b160306 67
    0x141001661010040414400061800450b00c407600c482c8041005003000c0c10002240800081c034801488100d0704088006d001c6c00300b0f4a844c43c00c1200150010b0032a20014100c0e203400400815660040c038403c01400310700310050743c00c0d504d40a42e030319145942c4002a0003084086020088070b8202c043c842d1080e10100c0702010001c00360603107552218109507001900036030f045035004004c0704001080c00700a400400159612103204540404c800c4080e00781a0012590760710003031700702000304500203000b0000031880341c114620340f800c0130021480c0341304601009400c5038620a83c49030f15480c82a0091903415180c1340c121403595580100100c000d44a103801c0c020b00c02c50401d403400d40c20181c01800d01000c20303013003071840c03d42c0740e0742c82c07500c91610440e003160268070032000c002e540d0400b03024590040080d0100c030700e0004d00b40c21141c4e03120055030144c21400850524808500780b070403c2807400400c40300d000c3d2081c0ca92030f41070061107010201d4080c041c0c80ca01c8003400f0007061080c4510012103d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 641814118 1250 641812868 641812889
    0x90309090c03060b03150a06050c0319050405180907060c0b041506030c080a03110c031b04021b030703030e1f0513050607021608010b06040e22060207020118 69
    0xa0506940900614412038544200b40e603411010444450300b0340110301580020b41d91503405140441000348000d911740103181000002d100d90110548000251450603201101c051008044018104c900c0d00555003c035500070300000144c202221081c4015003d0260b84e01070710021500c4000566900403215002000d000c1200001004180404076019401048002c045800342c0d9986420000c80850f811141c0290000c1150034100b6400c01e1154038020f142102910440002c5000203840d504040f000c170300313810000c040c1e203003044d0340e141d0444440040131180a9081d9040054455480d0031107103044001c6843e180c14601360202c0041c000c5007645502d4a049090440150b00401800d0080c0104801a501d141d25000086040c40001d11030070341603005001c0c14070390251ba44d001cac2007240d005074210f034900f40d01d11000d500c40d2802c9500b80c8200e00c08104554545200761000c0180c128010181c44402d00100410000140c00a007030b414001d03641c0c001c440c10710010003880c00d9614841c0c0f0300c0b02c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 641815368 1250 641814118 641814137
    0xf0a11120a20010c050901030b19050d1e0302150709030b0a11070506090606010e0d0816031107080304230102060105040f1814060112081206220e010509010903 70
    0x49108030142440d800d5241580910680c10000b21420344590080c0440800d40100b00c10080d5603040c441d4449002040b15030801070500c0c82031240611129000b018040d0f082c4020b00c000303100e85603845943d50302007003848042850140c00d000751603007a0b28131030801e07207c03032203001c902500c0c402c4221400381c03900240302d107409807100c00d82240182002c031040c41c4012030902943d004a41c041c8022441501f00ca8081c00340d51a118000504901c1030003400e070b204051420140c8045180307030094031007800e18003180c000c0c1c4c0d003c2424252804011129001428402c250f00826000c0012001c3c100b12041a502e00603c02d00c0c40304201411090448480e0041c1e20900c0100400e26240d0070040d01081d1841c4000340013004145180306490f4814002c4d6904419011071310000d0500f040000e004042500c3c02e07944206051b900d00c5254482c1c0894010302e03900a5021408966130318650f00b51101c00c1e14505840c1901c20300619010340b2004e801940d03254606000240c500206018000b20356906a031180c07480b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 641816618 1250 641815368 641815387
    0x608070c0c051009050904060b0306100b1206010509130b030d03090b0f0402190b041d01060c151509090525030b0901270b0c070b0a0207030c02060f0a1112 68
    0x5081c601003e020404c05403200010700c80d10fa81301c5041c02107000381c00c00f16400d25a00b081c10319001b0080c205075400c01511070100181c03030200090b500001410507000c02d840e180d4400488940c081c80048039070040e000c0d88a64400c800d42d03440030030100030540c00d844000c001c1600940465001240141c140145500003c0ea085201003100354050301c010b1190742e42c80b05105c114850804240c1041041810008003030010030b1001c0048101c4540e0541000140d6041c124003c22207440c00780018600701c0050010b10708115a40c001d0015031401400280409a070f421443c8050a016079040d2028007901408403c0c0500111481c02e054180400c0b0360310306407035a9142205000300502c001499541c4000f00080d080070074601c0003402c034a1500410f04d441c001c4c00c01400112001c1d00039140d001e801c11115000401d203043c1030b0b6010710780c100b0060f15844c0740c0c101911a51500d00e00254007180004202101b071074200b02900400c1d010b80d8a0b1841600300c400c005035104520500c0640100081c401c1d00c01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 641817868 1250 641816618 641816629
    0x91505010509041b0c030809061b0d060306020d0902011d090601051c05010608040506010602011a011202070203101d0a051209150a120c030506010c06050a0b090c040608070c0c05 78
    0x215030054000900044030b4111020103928101d9550001203803140301005161f03108103d280c000c003d86000e0003007810710303814810301c00c000d43d01c800000302404968011103020b15401500299080304055540d591040031220003809401c004078041200e1000080d034500b00e96051481d541c030701521342105521480c00645168101e08140b50642440040550340051079020b102d000301450745072402507050600e04241400301c160408001c5a151402e9607062a1900c154110356038020f0070704031149000c0c031003c0c2021781300e0002e002e901813080d40982204034400703500c80304a01d000d000443e9091404e0840c5036031071f42d200c070070f01901c1c580c460102640880e4502d8000c00c80c074a0300504042480030310580c014004d400100040c030201b42070b14601e8400c101c0364002c1c03824445851070b040010389030040000e04004c4210702c1c050060703550b68000440c80e41503548485401d40001340004124501070081d41050f901500038000002c0c50b000c0410790f560f0180b000c090340e2960168045e4452070926041c0314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 641819118 1250 641817868 641817877
    0x1504061431020c03030406180308010501050a05041e05040b0105040b07020637030501060309031709010e0307110a06030510031101020a0803090604020f0a1505130503010606050c070915050105 84
    0x9403030600c81c1c0750700d41c04400c148010700c800a202c01c061a00ca01d4039041c10002c0b01c030800081040400308090110000364003020060564909080c41a21981d907030008070b400d4003468000040034070300c0d01068510004000000c900311641241c003030121064a40046442e80034a101c5c900b0341050610241c401442c00b00043c05040c003440001c40e02554520000040654802010104e00c800e80d520340b44940d039040c080d480c0035190a0405115540b55070740d000380806e006a0031a41c0c10260040404c05c80038003034011500d108100d6044075102d110a0030f0807070300c462200030392911030300000e03000284060003070280c180305600b0101d000c020b0500d140c0f15850a06120b4003240e0440c06680844800155400055030041d035562000344035902e00f40c4140030b00303056082641f600c01c01c00340707908220703001c40e1381045d0080c504c0c2071070a80e442d5890700820580d090000d401803035142d401c0c01000700703041c3d601c2809010701b01034080464440b184c2c4c40b51004100da02d0002d140010496604060100d5401880100b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 641820368 1250 641819118 641819179
    0xf0f2a0c1905040b150a170604091a1e01081e01050c16060207080a031b03090210200307030804030f0f050f07020120070f140d23010515040614 63
    0x700700750104242640240d0b8010041200410304101c800107c0e00d130b45111241e4030960071b81d420002c00702e050b01e031b0f059103001b442d403c140004000340024002160910341c64907800c0e080d10312200c06584031000713281c45417039525450079030608201c903500d41510b05025090090a07610728007881d000011401d4068201c00410684580750208100d000189521008080d0300002e81e0740001ca0501c101003625401c2280301c1d400d003c140c200344000c00541c0e40e07001407207040c01c003a0030070150028449050750060980c01580710001d00010650300141a00101c00c98401d030f200b03035500301d0103a400c8081030300c41c00c02d2049205c00040c014480d4001000341c0c2002861024014100742d110301565400c003400b84009140e4010b41504541000c0040c3d21200100d08058864a6403102d1040c05440201c0c4820b6003185016004000d000124280325140383c06401c001c012000091020f4076045283c150014a00301c81c0d84c1c0240e1038a84002604c02c00c54000304081d030300003004a50726140408025000a4400101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 641821618 1250 641820368 641820379
    0xc2c0303040b0d0501180212060616022d0a0f030b041a07020a0c05180a020706020910020a030f0804020102060f0601030216050106090501050a08030f0f2a0c1905040b 73
    0x1040b410040300141c006000340c01000318144d81003001c003007000081641400ca80754014841c00c19030b000e00030f51841c0d11100c241d07903085e1280c20115040d41340d481d0300c10019400c000c4a044e540b01101d4013040700c144861802e0702c01c4002c44107a20234090000407500c07076041000d091003800c0c400203d440354600e804c140070741030001c69031907142d000242214003a03500da00903a1004c45060300f0041802044801800f0480c0c5a03510040c01c500700540e403140040580000c16800181c80d8200182681a9036600d00082c00c500182101d281020b584c0c5e00e0441c00641c046640800d50b0390b14170780316560180c42035a06a02600c03090f02c440c0b4402862080140205051603000c0c00113811442c00c0e624000005e602520010644500d010702c3c45c8100c0360181c00450003800345071414440640b0001c200c0c1c5000b0510440541c2e500d001a6039a6900e000e12888082081b13602568245402091030342040d40d5002c19040d6115501d81204000c1e000c40b244200030503480840c40c0c100a02e1030b2541c8841440d0b40050702 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 641822868 1250 641821618 641821627
    0x7030b0301090606061214060f2e081e070f030b0d02091003170301122d08040314150601031509060e01060207150e04090212010e100c2c0303 62
    0x1290700968441740c1050002494504000322112043d01400c090080c41345048030086c10008080b480f09042120300c280030340c1c030580c501c1010640000440d055449610441c5203403040d0000006d182c80f80580e8000045412403d0141500800e5003045010300140e4554094000d03500c0c2066010301242800c0680c03042c0003001c1c00d03016071104e403110362040140005145000d4114948500071060007020749140710070520040c01746803840c0c03044d01c0e1644c0d01712070425020080d2080d840c180f41d01030328030120031041c0c5184103c02c001811000d0300a0724850009038803c4208101055074544c0c01e03508241c04130454001141302035001b54440c00403205050010b85a80e03480d00c05010954415a00000e042020784004200f41039043c01884003900f104080358014245401004220402e90850103201f982e862007104215a50801c4403a16020944009e10841801e107142c1c03525445251590034401d8144142c500b9070921034441d500c0c490803a02a0045e00152805030304051180070748003a80c141c0700410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 641824118 1250 641822868 641822873
    0x31a04050c0d060807030804033c060b0301091a0603010902040203091c02030310090c031b020d02070501050708030c070314031510031b0f0e060a02030d0501050a0303020607030b030109 81
    0x2403501c541d80d800c0740300350388200505400e4103e50b015408281035400c00704061000844040440c0c00300c94100f0464525603200c240d2030352840c0c4c20240a034003644106001c0200603081680100211400b0300d00030000c107400300041c103003650303544d00c8010141f4a10149407055610b40a103103642004018000081c0c3d602a540458101d07031051f00d40c40640c0c0e00c004008003548108035486030850f0b525102860035070030141401d0b4520390081c00750705085503e40d400550818825070054034104550141c900403d076041d44069110070301150380301c006008001e00810745502560854138a41c0e84504080e140d81c0d1060f103050300d0364001c41000c07401c000c0305c0c441d841d10580c0e06030041c500841155075002003ca480d8020000c0c880003503c59441031508040c032030700402910030411340d00420982488054280890780883c0d400b40104c0060b5446280400e0390102990300002a0980a6002b40108904d076240c0e01000900301a510004006070301010014001314400d070006900d040b0042e002060303160842d0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 641825368 1250 641824118 641824121
    0x5030d03410604020f0304030f1803060227150306040b060c0d26160e1e0a050d02220e0d0503060117012d0305030f1c060803070201031a04 61
    0x110007080c0c0900c0c071800c400568003210a000d0308144120b404603c2d0440e04d452030280380c00001c001a0a01a080c0d080301d200c0782c001d000c6140da41c0095030402d5600764907894140300a4100303a4132070f0303c10441181c03d034041c0b41c2441d51028642000800385110503d400803d1f01c0150b000030710003500240c031500420050f0300c541000e098040c01e41c8014090810035014018030700260303080e0f80494804103211030351006d0f1052407010f0708804c0f205451291502c21032803da03000454400103d270044c0c02181c5644155150703808030f50300034800711016041181c0e90410005005c0800c01c01035840441807582545000c2c000000914a4140203004a40390521111030360034500b00e81102000b2550000c00c0155030369001c260008001001140305c079455040401c1ca8034010f0500600c4520603121924000759250a80c80e0741004550000440e641ca0241d03100f0305200d41c20035200c0f501f066030002006000003005004e04400d494640000307604000380303500114040d2500c045080c514500044100d51b964030b07207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 641826618 1250 641825368 641825441
    0x303180303020c12070f020904020409150218060910030e0f070306020a091d0414030912011b050f1206151306120606050304080a270302010f030605030d03 68
    0x603031001a02d0340310f01d0300d8050901c0510743e00142d008030208204800581d26506241510342c050b1685842e5a80700e00c0031900510350141c02401585e1010040e14070000507070000e01d005414400803038140010b0009200345030140480c2640e1040c3c0403400e5082c4248241e00085001050b1021201c917160984847c0303003003007180c1c1c106440440d00042d0000c0340541140440c40140142c2407071060318040d010620354600406000104014881141c0019945081040d13038041c2500070b00c00d80c0748020880c0d0b40c1b80203050310310403551400d01500c2c003407620300e0003401618003140348440e00d18504078016000c42c200601c010a103503444400da10800e60000b0b5000c004d441c4a00054140d1150182000805480108410f180040b050700708a014004c2d15405800e40707810560282d0f5107503c0b40c0500c0e00917a10000d41c540c018020710848e1380d400c5100e90612106508890007038807040001e040000c070450036107825005003078059118051244a035480f82d4825003600d0740b0200c1c0d803880d2260100c040382c1301c0e505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 641827868 1250 641826618 641826623
    0x304050a0c0b04121113020d0614031f0905070b0d023103110a05100c0614070f081b030709051c0f0206071703161d1c030318 55
    0x65021401c00844a201030701901101510714241403402e5040810700c0d400702ca0040603035a803042c1041094a50028104000310149800d540310300181184c54001c08092048800d11855590a600e00b8240450f0350300d045c00080d5501009100e0803128000508107600d411191b5101d5007a0010f0a0000107001e8126011500707009030381c03100000c004800c0070400e40d03890101c0805804404240714240b4203080f08482d88000d00c0f2004a40c1070300065044002a440281c1021451020104041d40048415030740d6105000c1049040d0000448055031901200c403e8040388145460303283c0c0314054a00240d00600c144511000080c1c0b83c40e10120035002079034002c0100701c0c0350344103200c50b140c1503155041c5003140090107000900c00352541e9001030780411011b401028002024001d000441401a00078445440d90300e94034204441d201001000c601c7c0304200044c940c3d40d40b80c4e4680c1710180d00390a440d10081a00719002c00c0d140c244140c42400100850602d07aa07410725400a410701003815400a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 641829118 1250 641827868 641827873
    0x4021512041103060f2a091918090c140303070c080c130212062716031a0f1c05011a1801060f030f0609140108100603030c020f15030405 60
    0x4800081c9850100c01800b40500800148208130455a85802c07008649030101c444c06010115984000c209104903103042d0f422011400d00c8420002e100c81d501404c50f030701301940c00064403027062440212165a080100303c186141c1082120000721059808030800050a480c60150f4983d00c030016a0400d901c00009500f001c40e5600c038038940368652151200d19102c0942ca010140c000d603050800c40140100d01c0b0310071804901c00903100000c403000c03050040c1c02c113810b018109038942c0c640c081e90249030700c00000d040c00e817002c801a82403071000758515800307400409410618800c0140e144e032500e00900c1d6100c0c001e101c41d80072407400d000d00b10001c1c582c901144100344000e024890104103405010300c503501c0b030800401103035a20074640c0107800380603d00051864003004106000e082c0c203a01103048241400820006011400003490480c2e14041c200c600e41d030481042c45042c0d03580341c03001270080342c14401e03400003504044a038600c940c08010908450340111100a0050390000e42e0f040d42c00e075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 641830368 1250 641829118 641829143
    0xf0609090a090209070e0d14030408070e090105060a030203061302220203150306060901031104150b0a0f0906050f07080403170315030a0c06030f0b04050a0902270402151204 76
    0x5081040d00a5044805e9180c08201d101c0001d002c2550320704801401018607404842c1480e003404180242c41c098907110003960071440e640c1c0070648206000f900e071000994039041c0032480d1450440e02d5401141c2d0302901400b0659502d220803050306980c0c0c04140d80058400d41d8101000319a6150b02d1141c0f0f00100c00145c407420403011030707801c002c05014040e009500080c240441a03071a9075505044950003c00481c0d0140a94042000b500e0482641c8580403281d0b0740208001c211000030701400e00c440d5858021121000b030045a080c1003902ca480c02084e0b0030040441c8a8100000a0002c41d00903100207103407654036036940e032514848651a2a1040003c003d019a42c00c1258242c00750303581c21001006011130139281c03809040000e100719410300d171740c6907001107a40b001174101d265803400c024000c01182c680401d00002130001010200e1140c15420404802c200c4482500c03e04100c480304c1c003226503516a030a02101d9032004114401d064424082c403002aa681d01c00c5a100f0f5104000c2a0f026 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 641831618 1250 641830368 641830373
    0x121e2a07030339060e24090703150903020106050315100b04061b02120a03020619050c03070f020a0506070c12030203060d060f060816080706050a0903020f0609090a09 73
    0x1c02000c1c1c1c5180c5070400c186080740c0d8032100c45510f5001c02900400700c1c0240401545031010003800b6001000d4000c1c02060030710708280014140007003110402901010640c6d0301c850703071591108403038000140b450007900c0b01c0c0c2e804042a40d0001d00d00700d200c4d00001407400e4440300000e10704002844c492078412042003c014100400540c850b00510f6950482d40c10103060401c09005000380b403031190201c4000340300310815959051003441e402d8446a094542200c4107043c000c4d100c440071100324006000042141c400703016284520b42c845c40801022038110b40760044112000844601000d01b14490042c04201160050160a0041e205030301e034a44442c02510703042c0d56842c01c4154000034984140304003e6207071078014180c0903c5038060230005200322950b4104008020300d804c485214461440b8560f00848507810300400d94480d24100c0308a242d07544021a0580b1500c0440b00014113022010001814083c640107282e910040100d401c111420010400c4100100c038603401094030355100509 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 641832868 1250 641831618 641831627
    0xb09030903160305030304060b06070f0b010e07020a0201020a020d0c080d0e13020313060e1204090509060f011a030403030b0402400e06040605030a030809121e2a070303 74
    0x802400c2c1c8100d0b41c00038650b480701c1e6164000103001400751a120305001d2815039031030013100d402c0e5900c00e00c403a41e4098a41040140c00609001c1c0d0310030300340c144000c00c04c0e03140005071031046181d0590003003a403040c8640c248030051038043d00484c1e28400c524004140c0040a00640d4400c840304e94510f1943e0b0582410014481a0040f014049034410030900610482481400c061550884d0000c12000a0304e07021034504500c00c0f8940415850120300802c2021090300401d0080d000403088036080d464841c5817103080b0f0030130310a0f080701000f4944902e0b1891b45c90000f03117600c28068100001c00b80c0500b0089000c1e80e0249496500c001c0ea61560800b000301295440095690b4440343c01c2c07000d15190b070380c0200e180180d00071150007130060000a184ca03035550300248040c0102400743c450fa0b83e500e03e405001050140d900c204103000e00b01540c0c00580400c1c1c10344d0f6006046030071448400c2c4c440540e2a13040c0e0300c07c40904801070082d034071032040034007000003603c0d00480074001800c1d418650304000f003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 641834118 1250 641832868 641832883
    0xf030c0d121b051b030f040315020a0905090a02090a1202030607020d020607030207060e01020f0903061302090606030a18140c0a030807021203040e09070303110c0123070b09030903 79
    0x11400345404405540c81d10b10b98001da0a020450400301e070f603008044e0304010301c2c2c5604c01681c440ca20002411030b050107011009441123900c5198403034106103040071100c0a84c00351500d032030009105d032581089030b490164421a001615980014646002d960118408003d41d0704014001c29095030094110704003000303210740c400d03c03502c0540000c2c40321081c000d480e0000500008201a0045000018024123500150b84003031028000c6554020740c034000c4e1016088091030b28803034040c1d0300c0000c0041071070a40d01c02000703500a06038003070707660b0360410070440c0e41029010148140ea0307010340700b03d612040c4c030940c100c1034090171100e9030303840c00307036100c1ca20f841569241075008040d00716080002442550540740000d60449948103280c100c03c0320385240d400786500081518440c0c2040c411030f40700c045588030a481c02035441090001c0f500c68241d607a0800075030142d0010322011140300b240d0045445040702240c5a1030031610b0b16115850340048800140c42203802908001010720940c9800c20442c3c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 641835368 1250 641834118 641834147
    0x20118060507030e1818010f050f010f050909120310050303071a0106140409110f030c0d0b060306091305010609090503030105030105071b03110102040504020a170601090f170f030c0d 80
    0x2004d116406050a01040c003000c3c2c0b06c28106040c81c600d6001d140d1007904403080005641c54200030700d2400c1c82c43d40854a01c28412142100c0c0345007804201c9003498030b0f06500c96580302004140e05500b402054403154002411a0b410b00382c0710601080d02da40606c02003081602030b0032000c00d0801c0e40d8124400b01841a4402c2040c401800301040d503118001c2e040d90102c842c0140002641000c0c0c203551900707031254925210303505030008104a89825400050700003030782d0110313040210303520b12070a0003124032003940c0281c2d001d0340c0c00c8001070728081059030020900740b00b90004940c003a035513402c503010340e10940d0701200d43d6000071005002600303091281540c0041c1d00d01e814210200080d110296a400010000c0c0402044c1d8038505000c101c00d40440d001058050011503941d406200c2c01402050005010303070101e20dc1d50b020861342e42c49403120342c048e2024101e100030b0403860b000840e146040074040c9010580104c0580702d4040c18240054840844000050301e0041c0999100900010421009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 641836618 1250 641835368 641835379
    0x3080a030f02030603070e1f0e04031409060f0d0603050304170606030703030e090702070f0303030f0c0807020705060c0a02060706020c1009030539010f36020118060507030e 76
    0x4100e685e40c0c0000307032001104c410041c842416183c404c104540e032241c600d03040011000344e8900041031590700c0d4680d80305074002c1e40c846550310200d1140007041e10582031000d612000610480a0010406000f06040303000b04a0009485a40761380745402c513001a4001488200c00c1c411081c0c1c00e10382031000304d41c000d10403009002424150fa5024201c48010080d650140c604031000070b140754001c001d00c070080c3c403558140c20744c40e9550740b6009024010f8100040030807800c00551003a1103020b000780c03074003444454024203074040c1070201340241c2e500000400700039440303103501040150b11058000d080341c40c0282401b44e82c84503500c4d40300d0710708881070740750003407a901e000848404a40c0c0030741a0b40d02c2000013440900c0034920195000354007800c00000c0315600c00003040d0f154a220055024600b4808411002d200480181141800c0d00000300161081a0303041d4800100d407a0502d40581c01e02c61050400c0081c5280481005072030b10700310f81201e80440c1d40080d44606050b00511200400c40040b0307003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 641837868 1250 641836618 641836621
    0x7050f040209100e0a0e0103050a020a17060f0a2a0306060f051903020d0f1a0a05130b040e100203011a071101140c0d03090c06090b1902150103080a030f0203 69
    0x2040e041c1d84030305544010403e95030800c4c0040d545a54100009100c18104161596120b00b400b83d04d0740c0034000220b1041c01c940c94002803000040c0c000841c0c2800b50b00142105540d80b82244e500e5150003802490082c0d42c0d0980300e0034000b17585140801c150450030210102880c6986d02070704a0324507401900911080c65203030414180c0c040d044a00354451507083e485105203011041e00603000302d2404e010340c0303410b0803001c401e10209039120740c10910030000f0300d02900b10300c9018091440001c1c0103a135040010008080640d808903080702d00c0c14175010304005404d07521800ca030b0b800c142148140f5481980c0010042094003400321605440f02d082c07249140c90a500303070381c4101001354030885140c184207485107070708002c1005005442e00c00040200ba100c0486075400010010f0188040c22106902102e4012601c43e2150200406491034000e4036440c00043c0c16280000c0060b0034034200840c031940000b808058503030104e140c000c51090104a8541140b44405000d842ca02501c807000b2600c10f00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 641839118 1250 641837868 641837887
    0x1b11010f0209060f1602090415060b0c031204051504030801030c06050901050909040314044e0f020a0e2205030415090801090b040212012912060907050f0402 69
    0x12111040c00d48611151703038440030202c10500340305c0810041e50102c038440401040c403020240300d0490680d2540100009515039115030014040e40100310119401844200b03103d280b0404800e41241c0103504541208085149415140300111001c4002509040041040085445240020f4071040c10118205281400020601e0041c0c10700703a44100450710200b001d040c0a060304840d80d00e941c00403030f81c0e580e8407040d09480c60040c0c4c2075280340c0c8444040c4407003460b1108683c107068100b841c50721030883e143d400c88450060150540c05807801d02c02e4016000c01039841030300900003400c03c000c80c03c600745800d008020310255030382104030f10307030300c045100000260010040f5000c2d40c8030159000ca040020001c11905c0f1030b01600060080d6103880100c5062240b800c290a00c240d208454469042c00d1004006080e00d540707000000840035181c0c052040d8030203180555050384400b900c10441000c0301c0c100245010f106450000c616003055409018900b8039503404100f142044d18103529118148 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 641840368 1250 641839118 641839129
    0x7240813080901200f030901120b0f040209150a02060f090f12030709030c080601030c210b0a0b0931080f03040203030f030109051e040f020f041b11010f0209 69
    0x1401c46410000180d003024940c4c03070a1907403070f50180c050008660b2056207542101d030b62940170440701c9010410311810074801c03240a01400441c400050300105140302c0700000e01020350404141168024180c001200c4261401c5001d06402a150350007001141411280d984202c0030290040149410401c0791050b55100054030300c00180d20740034001d0f920f9030313101800c0380e030102c887d04014001c1c09500300005441e100018041e050700c0c040c0405d46016076454007181d040310900d0881902d09005004608080398200d503080364000110040450100700316000a40f4016080361414249a4040004140401c00c407855903201404040840c0b2511030b85e45070318403640981e0300d81d4401c1050000008045460a10a0b01c890010300c0c1c49003500c0e0b5844040f0b030406040200c03803051901003c1c4c080c0c207140c1c0c10710220f41c50060b9001001c0045040858007071109a010f8540420b070419161003040c1c2a03a014105003a0703012881e0750f2000e60702c030020b008403400d607800482c10b503900c94014481c4d142640e9a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 641841618 1250 641840368 641840377
    0xf0f0405030306100e150403050609010c140d2c0106090b0f15040807030c0806060a1401030b0a260606102f010c030b0f0306040b0106110724081308 65
    0x11035200c01080c10303000b81100e40070510102190001d0141c1c031b0b0301e101246154060020b403841034050700e03029034401d000c080c00c1341d07924180600024800008548004941c60040070710f50803c90002c01c401d903941180c2000228003510100842e100301704200c5001c20b080c81008050314000200b440384440260008a1a14048684902c03130703103042a0000480c0010400c407030040c000c034002e07102a55520b040c0090599030b18030840440d40100000a146840c0a04921096807002c100300700790100300c0da0046004113104c0b21410340101a80e0b6000c80c1c108542080d40c4800b0300a4800303001054840550541450340181519004405410322040d019070040d0703140380f200c003540c40d44002081d01481c080301c1b000c1200741e0610b03a6501c0c000c0c0108216a068206254080003902c0c06c0030f00103181014165504400c4a01419151905e1300500016225408200402c0008000c8602c15900c6040784514855070558900012000c071417000c031260342022003140c1c84945002c0d040103a10250b01d402c05c0620a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 641842868 1250 641841618 641841631
    0x1915050108150301060e090d090806010b07080a0c060e01020d0b040905070b0f3609160809120309070501030e03040f03020f04240e0c0c280b0a02030f0f04050303 71
    0x42840c2c0802c03618254491801042c1c0b8440c650842d08060001c50380350600b1080580014055a8012800100005529041b07400f02001c0c42e1600500707480b814419080103800e5410800c484010b00080760f07950203070b092966425800142e844158040c034508a440d410415401982080140d00104001003100001c85003110300240c2d44007801c20181c0440d104407400002c2d00041014220040512280101c0c031040c0d115640c1c281c0c2007204800c001c003410040f125101600e12110000b00d0817440341400c0c942040128040300c9080e4121a2454102c2d0011500380c0c400754010b2100300001d40e494050020300c80c2c101e81c051482c240c2040a050380c4c2c0112800301038080c1030200561000d90316164802d000b202d500c42100c0d000369151000b014881c108038816000d034000d650010400d0000f810f41121141c9c4001c0d4018251140300c2c10801103030b0703003800c802191f05e070f19404005070102c2c509002892040c149000010b0340c80c43c04108040400740060a41c90001445004110020b18000101c80e00201c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 641844118 1250 641842868 641842891
    0x10b0f011b03051b06060103050105041127150c0618030d021305100f0e010219021c050106060c0c06021b011107090c030e011406010206010501051309051915050108 72
    0x81d03550400340c8461180355109504010b6640020045000101d282070044009030fa06014503680e50003000160b80650404080e0794104000c600c040714006081d008696603031800c5410140c2c4a14001505032041400d814015180010040503644052002c2c55000b800c8550743c104c50601d100c450341e40c074085c0b540c40408003980021040000e0b8103a01c60320004040013402d00924498645005000701070305d40f45000420b294581b50001580041450440c0400390000040c800c0c0c410b40810060403448005045800982100c0c039020800c00e0103000003420b0640c8500c0c403030f0011071800c0130300544c50303511101c00c5400502d02410f04206000308540c180c20246040700f210503500304003a042440a5101d8100c00c1d1900c045501070030b07007682048440032038070b2008010f541140d031580ca5440504075545030040c2c00610050085602600281000100100380c1040d125124254141120801d45090469900301440c4144607052805610a0500e52003081c41420b441e00d00060102440540303950080c6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 641845368 1250 641844118 641844167
    0x30b09070b120c091e0f04051603020f0c010207030c02030f030c1207061b0906030e0109050604060519050408040306111603030c030b0310020c190f0201050702040b06031602010b0f01 80
    0x1180554605240040c145d0588110b09005490595050b6010074001c2c4441060148140303400d00c80c0764450603503003022040f0b9252404048000354000085841010018000c6903606131782403000d050240d120382c0303070340c242085c2034010540341c089018120b01d0960b01c10004140b03603010206e0340c044004098461580c13103003980d00c1c0460262154030421004134940489824019921562210482d03240b500c08100c01800d0b1040780e4242c8140c0c000c050160b80c8924042400a0300a0b44402d900c80b00d00e114000c1035026012003102625400d0300e0070750702c2420106040c000d000d0380b0300c80d1081000804048074901088005404460f007004003000c0d007415a10194005114000d8102c180000b00040607901740581078200b00c00290452070500145209940308140b0a0500316500c42c0810b0700320052143d141c005500444442d800480100d8025494803080205600c07a0b00c051030156006145840501102410081c21070f03c00c0c0d0002d0748074090807410800c07107980156481305a080310841032160b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 641846618 1250 641845368 641845381
    0x5011107150c11010f061a0a1e03090b0c070204140105030a170d020f0d1b09231e030606091b130f1e06080601080c0901120510030b09070b12 62
    0xc1044860b60030b5504e50070812140781912440e84000b0a45000281c40b040008100c400e0a4403800b0303211842010a0307140c4e525103510310a120b5a80e075804660314010403042042d58aa41502c081a2166000d50001245600c00c62034240a2107101800110000368150b24050019036180040d17440900314110001085c288015168100d48040c040c81c6019940c034017013031480700081d07445001a804014540a036184280340c04003104d20305000155035142c0090700f00900d051481728a10750482e08004c0e00d20141c506034440840d006000741d1180800c1c240b000b0080c05142c104440201543d01c150300c640100140e0500e000030425813500540c1b1942d881c4d44200c1d1f4042124441038002000101884900040c043d00c000680c0110070303040c0302c048000c80c0e036400040c0c800680c107444a0740451003c5e000142500040c0001e00150981450644001c1c05031003a804102c032820388421441a001c40010b06c14000309012054000256200405c4e42924166100b56603008502801c0215500600810031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 641847868 1250 641846618 641846627
    0x10b011713030e03160e010e250909060e0103020418260c120301320f06090405010906090606020c0d03030c0c150c1205070c0303020c012705011107150c 67
    0x707a41000d0b04881441174012284150581180700c0d004003034121800106031000002c0205026040b26030070750018102824000300000308054048007045003080000035040b540f401541d00924592120060550450060100340c130103c04060034010560081407000507601c0c00350326111101044600a07086130031690744840e1284003030003000b84c030518601118801448000f14103e660400b11064010091517480d01c02d050408040802c081d20101d01100904210b0556444540c1c001c260074684400c1e20005000c4520070707006007110642d5144180311000481c07190344082e0046000400307032b1010b840001028525501c2004007010b8a51800d07499072f40c0916106203c00781d04c4038901c2c06030340e10340302e0719801003a50151070f030009001200e034210050000d01c1828051002692140141d02ca1924140e01940c08281010036545d40d4028003000810480201448d01101e400c402d034a24107981011825106e14020b203030900c1c6410002c0c8000500c40c407980c60030b0041411004284140250350540c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 641849118 1250 641847868 641847887
    0x2040b0f150a021c2a06021c0c092702070b09010b09150112050c090a09060806151c0503250b0f010b180301230405010b01171303 57
    0x6812031658082100c00d03880601c0a000d0b001003075030868602800c005030340c210580b902420100401c11011010421075402a000240650900e8001c1e1000c0c60990311b140890f40021001e8201484a06140340c014189000b60319100a007442c0c10140d0720708000040840c4003241c2d1b1242840740594074024401e01190f01a1030440b608840707402c00300d15001044601800e601403038a4458441a400202c4510038200e225180364410f940e291025422209640d00074803010f000c03a994018184054002c03681e03065045800b03858030850200341f052404c503280707142403400360240c960101150010007280d02d4000c0400400d0003030010078244210340d400c2c214214400d888204240784032790700a0f01c1c0510700d0004404402c80c49032a2070240c0e40d0707503051426031940c003c0c09058a602410081141c40706800490304c44240ca0003400040c61400c1080c1e00d2502c080600d032401080d45151040005100082c0b02e410ba03205c80a080c450103510a25404501c419030040541e40c00503068442c540615100c0d50240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 641850368 1250 641849118 641849149
    0x6030f0604182001230c0f06130614010b07081303050106140103140108030306101211030603061311040207140304030b090712030509040903020a17090307170316021305010b030712140402040b 84
    0x1600d10b82449c2e030191070318171078107a03050755003a06191002806882000351141210803504480781000c00955072404507620510b003c0501440311036010000c101c081c41071500800e6201403110400c502d040015042d03d91031144d240c0443d00c410b0041280101c044112640030741c080342d070040c955410036019503100c401414902d0041d0302c0d003990410301030036010055000301c03c200c04845466450300106901410705000080c100c8400c000710041d241465005424413611408c3c1c4048014000c08071240b55411652081c0d076039880710001e11a0341403061042d00068180c101d46a26170301016200548a4072540303216501580c0c6e14262001450b01c02d1083d02d0390a68801c00c03076451100290303186052070300004070041c82400b038080c1c000b8000ca00005540c9924514a024604040c01078001104200807280c0c141d8029002540d0311120040610400e070180c41c02c0304103643c580c00c10000c02807814103001c071035005a5191802c441030052000c5903840c3e0140d4100c4001c154a100300d408910101c1c9500e420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 641851618 1250 641850368 641850373
    0x4020d080c0732091006031a041e061a030705030a1107060c110102120103080c190609050c0108041a190908071e0206030f0604182001230c0f 62
    0xc1c4482a1816903a00e24024070869150306501e00c41044900041070745c02145101d1000010401540680c01c0000c911200040e0380c0784030141d40c00030030203a4101c00c00e004400d21780e42640c0f83c40300e030309440740801921084903d600340c8181e2640780b9104d0300c8043e02c04414000c0104c00240f8a00c066005081c8200c0c08038002c6417214454a030107800b6000d5410720742c1c08111504140c42d00c1810510030707606107424500910080d41d00c0c54607210340b980e00c044040e200a0040380101254543d40b0b1000c207070068800d150008105000d8105a070070300c40c181c000c4604005281e402c0c400400c5041400394003642014080400704d4581c414104840c2c0c000c41c0411900314200b106100c240054040684805030203403610781190466460038a03401c00c1d000000950003801800440c442442d00f40c00c15074041000761000842c0d000420b112982c0810100c4102c0f07901000440c1d01c03400705030307016000c18124400c0c04c2c02122440c0d484194a485420844542c00d0427402150b00461000c0410080c039082019409 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 641852868 1250 641851618 641851649
    0x16030209042901091406070201030f091a01140105190f020a0b0a020c0609010501050303070b0a0209090a091202150a0c051c060609061d06090f0a14120604020d080c07 73
    0x207150800c400c03242d21aa004c540e00600004409034048029045c0320300041c0464a42541d6500560042c500440300700d2403281d41c0c00c2c80710006242440c24107000e20300c00c05a0030b1190300d044410038120300c0402d9400d04002041c02801c1061a4502d4041241d494500301a01c1d101c61a0038200c1c40d1146016015014410250074040c01101d1a4020000e600d81d0000781d03415550782c1d100da031b420b9400030304c95a500350380100226004940d40b010751075084481d042000d8a0442d4400020b0b20000003510001015655260400c1c1044191421446601c1d050b00190421030080c43d08144c503020010000100c0c291940c52025000d84144d0888591000e014080b040d5040c158074007000074111030007440081007240d0303001b02d4094001c2a60078814103079440d080700a07040d4001448200d800c5121810b4100700f00e00200412681d0300c00c1c40b00c0203400300007d2210981070600422504d007d4840d00407005802040621001d40c844010201465401c1001345948140f400c05140c80d207440c6a00510004d02c8e140d6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 641854118 1250 641852868 641852921
    0x70602030406300e16180905030d0504031701090506151e07081b16150909091103060601050c15041b03030c300819111b061603020904 59
    0x1c1c4510340c0130105400b10342000b041e040c141a4901110b014101e2150003003c00903100c10103c1d00500081c0340700d28150b0707040041003003025041c7e0720103542c100c0116a20310580b04881c08201610f40c01481c50325418401824004007140c00220440e0000c1020071000440080c141c1962841c9101b00c00d201c00b00d0380e07541b47c50b4101040b0302d8005001030560741203021240160000e00280c101d0071000102c0f050303000a4548080e41c1d90f5040700007015004d00801260001d80d21501d84561042d81c2d00603605401813040103000c00d0705009000340014184003003800544944600001c000002c00070703441d000c5050340c4881c1804048254402c02d00500ac840703188001c0101548100d800070413034884d00300fa003001240045014071003d0389408a5106440700d4032001c04680c07066001540003100c2001d200501e698020044065074a4860300c00b803507042c0019404030a02e1584401405010030802500e05414a92803114144000c143d001c0d00f05500894054003a50f43c991007600006a0b00071100c5031310f071844 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 641855368 1250 641854118 641854121
    0xc09050a0915060e100518090c03270a1e06020f0408060f0c12040f060e0c13111210051f030515100c0c1d10060207060203040630 57
    0x241058180b00079003070008055003d1800c03c1968000241600000e080480c411a1660041340c00d003002090196100c680d282c840d03074911030003005122145552840c280075040610f10441c000340020181c4801000542500410005042584407000d0100403041182c101c400380c919000151155100003600700d00504842c2c0100126244402030b5180c9a0760303009141d4415804070384c15000300d0010010900016440c81d26658407034400d00326034190180c203448440c1141c003480d0384c0a043d603004880b44000c511700408400700b001d0707000c030f401c1c0508038204841907618002c040c03404800d90156008100750441c0ca10240c1c01070b00d0007400300949113441424405181c45002d10040c04039240c00301142d20510400300059a400c0003401612245244450403150340302c41000641e4409446000400e400881c072201d603803480e03820323503c600c03560500b10303460441191180d10141c159441240100038854000c000e0b02e0031100d25040c0b0602010741c0742a498501103103600c540b5181540c0c0a03400c184031145 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 641856618 1250 641855368 641855381
    0x2250501080c04060c0204090501090b0f07170c071101022b030f050f06130209090901050105010e0303121b07062429090d050601080c030d1d01030c09050a09 69
    0x907a900d540648a48407080518402d502034900010890300d12035025007416004030b100640304000014003100b803501c07101902c980035190000105402c4050202490b441000f041801032040102140340c18400c0500d800c500c25480c000b00070021655460602d07070300900000310242c0103081e18050000d114840c00c0e003c0002c900100340800e1801d40c940880340050300c5486e04c51100c00101c0c5807130751034a50030007101401d0035202850f4280c00b0404006992a2242402c2c09260300350000304265040c00300242c840c10000381c8071400395005210b0b50b03005c04210849243c2105048241c440180c00d800e580007414418601d0107000e8504100703070500e001d0642403014068542c0500114903003034403007803082c4a409544160700100c1d076a40b074800390320844003802000c0300000100154030150980d41d030181800f00076805030700107400c42c03100f00c2c060303040600c0740d420f1451080c42c0210207141034845900f8165045070760b182c10075548962511401c1c0c010030820014010050070120410b9403075104001520b80e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 641857868 1250 641856618 641856629
    0x7060510060507020607060f1d01090213150905070207030c1d0a0e070b181f1202041508041a0c0c1e0303010b070804050a0b07110306250225 62
    0x400e49000a41c4901c103105a4102036802052649858465150a00641150b60070741110942c0e46070007200f0b44525182241ea144554030021403e080c01c0d004100e036035419500c511202600f8500c0001418056150364800d46140c10400541e940300e2180403468840b05400040400507012004108040022500c910205050b0036209103507503402d05601c242c5410381d60403409544000c03401e10180c47c3c0a0041c00500e40b62941000240c0300303400029038650140030001110140144c8031070b030002c2d4440107400d85403001000943c941440c20341182440031040b40381d01d0402843c48013003070402000026842003940032a51741e03080c07404d104d15029601d5010152031b0603a4400d404220030f90840b1450000b994001e10805103003941c2c40c2c00520308056000803401c41c2d0540d401c00010403c0d0740c80c0c2101d100900540b10803251a414185000d401012000c0000703072103588250200b04060250540c100d542110011160404240ca9481030b868009544e460810101d02119011040c8040540c060100c0e903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 641859118 1250 641857868 641857891
    0x503010b010f0f03021605100c08011208180415030c05271b0f0705030d0f02070b010b0a2d0206010b160314090d0309030510060b07020d17070605 64
    0x401003001503850324a041c503607001040c44074080707181a42c001d42c05080c00801e041c03a005c21248070340e5502d504001000e84c000e0b100c5030303480c000c601c0716a900c503079407a000d0a400c015113100440f6030b071949421402843d403500c404c20004400741c58a9206d5810078090303c42011444c885041c1ca03460281030034120740c0200c601681d41c0c1c01142c0504103004000d0600c41640781647c2c1c81c5e9803540b00503201019180c040345d1a500300200a81c2c008144204000d00801d40120050350310f51a0040c080d001f910010b4090390440d60062040c1030120740e0040b00d00c0d0440380d50380c64031982c455112406403168049070002c01405854101c511006804008800d1001c807203540c01d40300d0980e25141e4840450081c00150054406a803900d07034000b81c001d038030700501e41c500010828100301e00c90340040c0d550441030004800141f8810410400c1100400c11440340350030b16001030000030300f80b882c00c0c540c03806004400b0307102e000214511303810311102c1441042040c0e00008003076651000c50905a029290030744240d080e61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 641860368 1250 641859118 641859131
    0xd050403141206150f040609050405100302130f0f020c0a060f05040309060c0302101811090601020d0e12010903110615090403050706140112110907210209030610050301 74
    0xc1c42008075590901e558202c07500984502d014003003420701800c05101c07121400c210509081c003144003e0001007210b40d85204c01c1a0500302032100303984018200002280e4076045c10300040e41c40f01d001c0c4001c02c03881c03680001c006424403048005058004014025284001240041c1010118607161924000d24080c85884000c500c0f1000702d81048401030001000c0b5402449043d101d85c00d1107000c24001e104546014910390003a030101c4510704248940e0025004031038081000e58007100444030b5041703400d03030202c1c0761180001c0c1d00c415030381200c001000300c0c0080c80c1e10a55100f0040501809501d0000c01c040b4109180180c040d5280d00500c40c200c2c4505800950180b03c081d04103100180c02400782819a02c8a80d82034802da00450000c40c2c00340d4450030403949030342c0c0c550b450318001c0c000315000c0d041101e054100b8a80d40005055040e0251840d00c04000006420208449498110400c4010341c01e156040384030003070041e103620b40d44c5800f884050042041c000c004000984404a008200d00e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 641861618 1250 641860368 641860397
    0x40b04030e0a0504110c160510051e0d090b06040608030409111e031f050f06091309051f050f01030807080403050a08090907020309031e0c0909030d060602071802070809060d050403 79
    0x400c05588540c90b1320003915401640c9c010301c02c0e409000300e11082e4081540150f42e140080060340c2010b1070340c4034503039a02c40140081c0819034082e44c0e001582603404001d054240845c050322440b840c00713180c0701c40d5141c00e12a1104440c4d04126034038001c270702914041c0d029008411041c0e0394005d444206042c0001c01c4480440c40801c040b120403181c0041c591244403d1543c01e0040c160003107400298080507440065504241c580900401180701e10050101407415104c480000050701359400340e00c5180c2030030411a240320300121810b5942050955844e200103141c260f00510030394200500343e00036140a0820042000f01500e0120011601000355903241c0707008a0b80ca0048403922941a48031010082c00455401d5085a8880c46075041d680c1040c3d80380042000e8403416200400c1c0c81e4400181a09000d40c0d9102d4400501340505c0039201d01860440401604c0724500425801c10398001582c4c410025090102c90003002c018240c0e41d22460409002c3c00100030407941500403800403103a00c0403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 641862868 1250 641861618 641861653
    0x6150603051605030f060a0b0307080613090b06090903070512041a0304030f0305421f050c10181505190e010e12030403030b0603040b04030e0a0504110c 67
    0x214101c050f0b5a0508541d40c05c18260704030f880c0608040d400c054100700100d807506080d0300031072046460780c89800700c80c10480d00b4808603184100c03040c4400c0d460080000c001a80d6124217540002c401c640030801030701c0300e031040c6096118404004180d031007805454482c203a1003102810444007400c80e0440b2104807039580203018401110020001b8010740f0045540034029800150450340d2003030034480045030b40580e0074401801c620844842201100b01200510f103059440c4004101519480c3c51250760032042d40c420303514001c08000740000815040003010042111b10400c41980600703128511a900b0741419066882c0d0b07040d180c03c035007190101007655641c051540501c0190ba68059001a0001b24100030100800300203925500c401c0c6240c0c40c5002000004146d542c80c030022036070307414949009170484000c002068010745041c0b041202042404540541c41740d0113040140c15002c07000d000810104040d042240e01c076180c0340d17480c486c50100c0c80c050203007205910200d9031030500d074004030507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 641864118 1250 641862868 641862901
    0x4120c09061406030403090e0702011505100e150d2a0f12020c070905010e180a0b060609030c030f0f0d02030f1605150f04020109170706030b010c0615060305 69
    0x40d1445071140080c0300b0f8141803004590103806854101149a2a030940c50001507094032000c0060303440b00f030075034441c4044003000c4000b00011245985079802c0c4c1c48011381050300c0f01841c18840c5056042c0d0002d142c3c000c80482c0e1008030b1500d020090000411650b14103000e8010300b014412039150101100d0f28010002000c0705541c0c0d403101001103100140440c080d500c00b40c503c2d0701e00d01411030b000a83c0f240a018142c00703050a02c03034610191400c8080c1141d80c405944029160398403180030200440c24205030710382c2004c400e40c1e060b5a0780d244100032070302c2c0001d201c1000e41c2500c90343d0019414480d0105030b11540a4400b81034a001e4120980100d82d640600210882014410000c40010306010001402214070900035a0241d0515001c0803001050813111507203084145410042103680c4085400098000c0c1d24804100944a0480075950b000300e0180e01d041c55510b04c1e003401180c0c00b400c0c2d80f090080e401402404030301540844000740404034458140403d007000d0100340584d0a400d45403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 641865368 1250 641864118 641864129
    0x305130801052211060c1509030c010e0304030305180a03080a1d10080612070b04091b141207031806091b030302030a1409060f031f0807030f05010b030304120c0906 72
    0x726101c40c140410085c140d480501140500e118003681d058000c0e915a05172803080300c1020143d51180c000c1d8201b03900355954503e802c42a50000c00c4248000381e0400c064400300c5050410b000c0c441c010200116403000c4580d040603000c00780200b803804001e035020038220707440c01080c280394501c02d800c01e0600c030050490701c02c03050100c0e120a00080080c00c00f280b031219000c1d000401c40348025910b50128405903c2a0049580280c69001a400c8032502c190240e2101d4498a083c1c0f0b00c4c1e48040c0304608031406032403c104225000003000c2040984250014490010545499004421280b8080005210000381240c0a245944d410000d0401c20b01d0740c0300849030103802030343c034102c40c9a108440310129010030044030681803180c3d05103070321820090001140e415808641d00d040207807007564142072040782401c6a4050100c2888500d05c08030360001100e81c414072080c00c4203503510f00369000d0480c1c0c0e003105800d4031000c140025994910140c00100314001c00c6811480c50301d0714a8801907410900a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 641866618 1250 641865368 641865383
    0x60905011d10030f08190e01090315060b030a0b0301050105040b03030a0804050f10022107050405150f070507061b120f050909090309040612020a05090403051308010522 74
    0x80502210440402a0b000c8078400400104540300c0d60340d1113010381c607024156100350f404900b0000700850315900480800d6503081070404003800500003880ea140d640401400c050300c1007801a058100d542000000d09241c02e2480e48900c0c00c04c0400004214a00700e442c880d40c00c2c000006100d04061103000300380c5402501a500c1c19483c001e09558105018104031414402c044401403880028400708103c03801500340566120400c1c042024072074000c6803c44c4c41180300c0c105002400e50044202c4040342c0302550031242402c68540c40500c2c6004080c09915020000500c400411101251070020381c0d03020344652207140c260044001e0b009200d180c0040081030300e4034109442c2c6019901041c031041d0310303207800c92400040324085145000250384500c01c0e9440070178492030b145018010340001c0d0004082d0407201e0766254000400901d150b20940d0301480903000803406148c85001140c01101c03c280340188040d98031410305009081c00c485541001000c0503000c00c94107403510020080e1500720300c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 641867868 1250 641866618 641866649
    0xf12020c130218010507170307020a0b01050f0d060f060e09010b040e0a2d052508030906031501180807030c170618100c09080d0302040f0e04080f030c0d06090501 71
    0x199002c1d40111020f6403003003607c1e0034000481e0324841c02544110410b5010b8076403900f031441c5c0700b00315401c10303000b00307110301e80c0c0220382c5a440d22111002d424442e000381340403410304103ca40240003041c2c260840030508031030b141000010101504240800704055800300504034402202580304d041c1070b2802001038000714000c41c208001c1610404034144011151110400160b688d18a0540d1400bd181260303050408903401803180b2600a034000c0c0541c001843c5450381c00c500261040c0703c002e2440c1240d20301054000100e92080c0f0030006201e24003070400c0c22090f02d804e013242d680c100d07a100842c0c4802034800041580c6401101e00c090105182000389400d4540e0340c000e0112441c1a44e04400c2d40c441c0d5240f200000d806c50103501c5e00050035880d40410a410080c40d54244041c0341150741c20715004120070402400034503010400c8034160781c8403003440d8450b881d10080d18403d00060001c81000403041c0480c03603002d1001804000000c0908108482d5100c4c00407042d160244560f20200d900980d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 641869118 1250 641867868 641867917
    0xd0803060a0f0506070f030302091c051002041a070f050604150b030d0504050d051015030606080a02060316021f05010501020d020a08090d06020415091d1b070f12020c1302 75
    0x88160406407180c1005414550700c10b0102f03000d84d03036519445279000f191151003c1800811b10051074000c01070041549031604000070940c10380c0e4000a01e40c14100c00194680c148a0b80c461880744069001050760725604007400c040050300d80880040381140e2074420f90114502d00010010491b140f0784d2101c0f401c20b071800b000c01650505201d000d403001d0003036a5428080c440140700321528540306842001c0c446041d41000c80440e25a5041819a5407202a601740540e44080660783d02c0300884e03108840400c001c00c0700700e041509880514001d500581e81c0c102e8210101d8000905031a800c1e030841e01c8150303a0701d00490369408110390144c104c05007001039030348606110010303038107290041001601d0140d56a603821004400080e1a00008807540414420440c85003d01e44442d5103e089c2444542085002410000e80c01c50402c0b0340d860000540f5010029880c81450300c4503044a120405662146800383d00c03001e02402c0180f0480c840940d00850790414401d81f011400741c0200d0080031503e01c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 641870368 1250 641869118 641869133
    0xf0106050d030c03031b09170a0c1424040303030506220b060c0313090605120705010f0309020303030709050a0807030c0905070509030f07030209130b0f07030b0d0803060a0f050607 79
    0x280090702015140c0001d4070030078001c042401b032040f045070f0740d07042420300d81494117218020845024006411038000c600101d0142c503508815942841c40000002c0001d40001c0c8511183ca1041649841d8422040e0111381c0c1c440050400c0780d009403003e124690301c0404102100141440e004607404640041010f10348a41c1d100c1c4039109000b070040b5103862402842540f031074014a88150144040e2481031009907150b01400009081c166401300d20341c180d02440380d880340c003240240c1c1c0c100807005a8000b0294803030340001107011740250940384d036070a14100040c405d06180c003920380140d04804002400c0a0001250402c494004c1d89051009090610364401342030040c00038000c004062040f484240c2d401d124601c0011041001814010701d07601c10b028031088002e000c0f070b005200300d4041601080341215803d51284074100a44425501c485040d401481460500382e00040c06075034804c20062000c000b18011380c011900b00d20740030388d06c500d4940300544034060320f40c11000074040140000c070300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 641871618 1250 641870368 641870387
    0x305071202070b0403060501150c230c0414070207080606060909040f05010606051c0c122307020c090a0c0e060c03271903031d030708030d0507020f0106050d03 70
    0x58410b4400d1155100381180036600541c20580700c0c9603036030004002d106283c0d9581801c2d500c1d2401c003d41109059151499490054120121102a048002c4840d441d09001c581e108180081081008403603031030289010000486080c4094801e008002c180310100045c00c44c802d12000b0001481c080c04003060000c89880074104543c0d10504820100016100b030107041c0c060603056030741c2612120051203d07007610703440c3c22030045030500d8416200201c82e0b04c4a81d40784070035469200800e1302491203910340054040c4201030b08001c3c002405011445ea0b0125542e0041a01210402810349401d8001800c542c680403100d00402c01860302d0f2035240c2801405000140c402a042d20b0600c952000c40000c25011000380f02c00c0d07a288906108030b140b80034201c1c40c01500300050150f0200c4e055650190090452030310b4003503041c00d00e5462443ca070350100044000b5001c48001d03031f622000c10380d0241000d80425039490016004ea0b00c0e2015960005101d24001c54500600044900340180c601340c132407004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 641872868 1250 641871618 641871653
    0xa110402160f03050a1d0904032d02010203160305090c09180703030e1507050601140f1807080105030a05031c020712080118150315090c030c03020a090603030507 71
    0x74403015000401d040c800e0b00c070395840c0640c86407030f43c9140905000704010b040c040c81280d05150000000c0181d141c030b0b03003140e80c02503050030852a8040821807001000401040c01610a00c2c01310319000d0840d4107401960160f01030b1300113110041112101a003d0740c0c8101d6018825502008501c0400e00d0300650b1a60040da00080c3c00c181d0f00c000e20000d90401c80b41c0d170020350228085140580d018100b90041c00601c451400b0494100078142d61541e80b159030610580c0c0c481c460965884544c0d41d981010320384101e0f0300030312440f86c00c460b407040301e00401000c4403460081842c20000244605010401c2021039900001951409000c00300b1514542e585240c1b810300c040e420f01007800020140c0c69104500e1440d41c64072070b80c075894141e241c09000c0c2a071064100240c1031003030014034a50403010030001d0b644d000400c0d0403101c0000d41104003e1140c0748010b0048030f10a1000801c1c4000b0300000c8041da8003d607650030034941c540d0013070001e40f88280310040000307104000000100e1004654606d0b4101c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 641874118 1250 641872868 641872897
    0x2112050405132c0102042103050a18080a0b0615091305040606090f0b12011514060c150a0c05070c120f060f0b010215100e041110031b020a110402 64
    0x10040e150114540c4904080f09009030350005081c440300e161140c4004030101100031420a0b03443c40e0740e004003107010390000d18051000301114002d00300c0c80542010301074040e01c02141e855952a003845c100c112026034255005900c8207000340e01c1c04018100b1200074400c0239000724050700c014202000100801842502c180340d482001240d41d141d58025141c84400c40403000c269500f100b810071501480c1d0318000d4500b60f140a0550301d43c452a0321111084900712280c05c000303944a400802c5e20361080024114031405a554030181c070603d0700c808507006040400707080020250b030a200b03907032620400758041c0a0038401601017082c0e031000a00364031041c1c4a40c030030001001c45952544150f542040103410f1082e01ca2410b00c0b410751f0b0410010103200046401700c449400c000c0b010146108881c0038040005203401c000905210307181780c5049004002421000d1011051000100141001150002ca070000389108035401440050596550b40e00250b404203c03107050401c200080d8001e100030400c20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 641875368 1250 641874118 641874161
    0x50310081002070b060a0513020a124221050f100b040504020f090601230d0c02011e1805070e09061006020c010e0a211205040513 57
    0x40d0028402462049044100907072078000e107250284076081c0050000b40200a407a000f00060f6a0b444c00a00c001c200c0e460006a81d40004101252490740c69500280c01030308090503a0b445500e00303524a80c00d6100c404d111aa08070120090580e281644039068010500b5a1000e1103c268070b25450744030785011240c6079900c4811984d62504210b00c21106015540200720b1844468030039024181c031205045504002c03601e0680c0c00540e08a64105500380104102c03000500164000d80d03030080c0b8850005d0038130021b0062151210041c0e8002c0d0f0045901c2800c215031402c07406c1c0140501000b0440c102802440c1b100040d8240c00203101d180c10600182c01a00b01190104206004d1940a08409030010006140115a2031b15002c00640032812520f01464100840e9602041c0c814070ba100902c0e00c0c9203640071007000214900c2c200d401c140d4034091020504440c8003103084443c644103204903000508000308210507142c6010b00d21646801000700484400b440b200d03507000407000c2e40c0030900104003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 641876618 1250 641875368 641875379
    0x90518010c09091508070e0403030b0d0602040311060403200a18060305010c1103031b040302040c0c14060705040b0d06090e0f0111040518060411131707030b07050310 73
    0x9503200401c9075808602103039024031440300301d4083d8084192091080421040c0341255440d0b8551a61103a21005061030b004101054800e80101c020500c00030404a1141114188807000754090b2008a4042c0c6802e215071015040c070343e00ba0340840b80c02560000c07820001c4e1036a04808445642255880380e0301c2e08020810003003041404410484800703001a1180c118070b03006c0d003100c0b02d480c201e10500c00d042c00341d4140d001000084a5020400285d0f4082e100d8040e12904039602582d080294064100140e18450035400b0344100300403401000ba0104041001ca425503c690041e11400000f0341c0410040c00440f400000400c2c11481180c00004e200350303030382c50f02c03000c640111f454105240c0200304035543c0d04400340255500b203016510f2451800c2d1400c0b0024000c60400b40107070880120311030000b0650354603540030701554800113145595952800c4411a02c10350382c2c0c01a24184504451810110f0b8800101c1c2c00030703280d0100e0446119201c5050594980c2c0000305015110380c28807070080740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 641877868 1250 641876618 641876621
    0x120b09190f14100302010e040207050325020402120403080a050106120e07080f0c010801080309102703081b0106050603041b0b19090b030610080c0f0310080d02030c0709051801 77
    0xc640f54042864010b070f0f040d40300061a850002034440d21650050090300c7c08603001004807803813861035000307000c0814040f0030703d141700e081c041e40040c2d441840801d64000c03e00f01c0300001c0f4400d034400d5481940584e110030071002107410a008060008500031015442c10704182e000a034a0185d1504852526945006d5146402c280300640b05040d000013010743c40b00d50b00282c20038090150900514149042e41c1c0c00700700c4914108442c03108102202c42e55080b40b0301d44421500c8000c16126542c4050740e141d0400e04003940c0310040c40d80312846034280c00c0351a6901846040240c0300c005081d18a0364842d80c842d4070040001c501c4000300e42d14000400138a2083c060014800b00000490f012804100d9460181c00002c2c2948a40c011200407c00c000c101e40da80005110705185a00304020551a5100c40e11114010214840400c09002050001c800102c2c0c1d07001c4202d4244c2821a481070410034400c9880b800390508006d019070200f581400710031200e411aa030700100803003d080750101030300d05250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 641879118 1250 641877868 641877871
    0x6010c0c0306021801091208031305030a1e0c0201050904050405030c060103030f0801171e010e01020406050c0106050f090114010c150b042f0f0d0606120b09190f14 72
    0x9030043e41c0001c1d107a10144541300000340000b42420048903039481c0c200312990340c1e401c001004009840000005142440900c1416181c68100c5d04072074a5100c00c1d4000781141c03190881143e2040e00249a82000511414070001440d1b41030b9142401d09103c01d0610014102c0500122a2408244106031041c0340400216000398041e42e1100a4840c032a003020380031032410f802c140419504802008104900064400c02c030600c01c40306c0403003150100c0c1906004004d801007030000c9500016000812503400b401a082c4000d100008021f043d541d5800c1190804404040c150002904001044469202110022403410604100011010075654004020440e070001c0c0821036652000e2001810140b00c0ca584072101c0f04d03000c500d00e40c041101c1c00c2d044290305407020b1004c90000740340051a151807050b244581c41d0007005100d4143c035110040c087d11100001d0451a0346080a00503681c90413000e003602400c2d06031018201d030b17010301001c08040c1540d84401120984c850705e040c614403000703c2956 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 641880368 1250 641879118 641879123
    0x3091e1c0f230712020c0a080a0b0906010608070c050325150606140c0109020315090d03020a050901050a0e1e01112a03070b0c060f0105120604060506010c0c03 70
    0x10303146403444050180140310b00c65074024014036006442503540380c00d04111000c468208041c130700c50191800c0c0c00c03864291030b01401c42c1c100000c4800041c05260002c1c5c080c0a1030301c919100d0046642e00501c0302d036112001d12401c5c0000d001c441c08501694014907220f00554006c00a4901d400001c1e0350b1580185004103c1c030f6810454406480240810340704070b01c400e02e00c5000f0070304c25035284c903100500c280d0b03103a09a8494140000f80034900140c0c2540901d08440c2d01034242c9004d00c12501c0318481120080720442c005008920074121080d10a00c2210341094140e01e80c00e00300f414000044800d60130540d800b03030602154540c0054141c1d140c030f09480400000c003030040c0e102011f1a00040c4800c1c0191540d5401e584943c0c51110a880350030700d0441020030001c03030f0300c00c40d00810002034a4584c1640c40700c400c064001036516070441000c2450f074807805140b4a890850f03660390040c06a144441d40c04075031103030400404200040c61617004070750451070500d080082c403003040d1104510032400e035108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 641881618 1250 641880368 641880377
    0x140607020d0f0e0f1e03010509060406061205061311030f01150f05010804060e0102040b0c060106080105090f1f180227061b150103030e01110303091e1c 67
    0x4078881998003084a0034507202c1490706070078001c1c160000c100b508091000f0940b08030402d041640059550003601842000e0050082c08a0f00f07051141c20b4880c80d040c0e81c00c0c2c0d0f2075800c2c414007003507855801d01e40140050707000b00204500d503240c03205440d03410180b2108654840450000151580c1c0412640000d50580b0000003450f205044440c44800c5141d0302c0039580000402c0100150780c0c12024069002d50814408201c2c01900251980240315070742064081e19004a80105030b801c00261640c10780c1e030b540e250010380d030740c8032004c02164810803034428010400850010390180141002d10511000400e03050703161716212890b0403000f02c4030344000c1d022a40e0114040d404400c07c041c5020b01985160840502c02c3c1015010841500c16071900001c0200c0d0300c01423030150041080302c21100b40b5100282c440e996140d01e0b0007000031000401e11030000d8074010408100304000300440340205907010007048400c01c004140500070f0b0101c08105031600804521881019020380381c2c101c4442c007940c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 641882868 1250 641881618 641881633
    0xc06061716171b03030d11040f0e04020f1009050a082a0325030c030b07020f0f030421061d1e0604060207060b130606020c060711060714060702 63
    0xc6009500800758041d05640301c0c400d0305040c074000003183c0d02c0810044003501481440e0601c02007480c2d03208009188207030034030742071816220803038200180c0f056981241880311500d945045003209264141d802950040003201e1a50b11031404554102c1d2005032800c0030900300b030b910800144424281d0f80400417540203d064070602142004031510021120480080b20781c40f680003080da40c0c06080380f000c24503600060380d191500004031024004503801040700d010103071280b0b02116060f0f000c0e40d21380094800c0400b01100114081080040a14184c3c02103042a1500b050004605000304803510340f040001d0340070002c13032007a02405110b44401d00c0c1c400a0a8011801d0fa4580040f19841507450001810009441d41d404a809900180c00010158445089040040092150b10041176102c40c04c501075480c018071541108007184c4040c0c003a1480030b2a020103000c65842400c40040224403078400c0d4a540d0f140200c0a07205c1d80340140b01940000450090f081d10300311060741c07081c016030301140c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 641884118 1250 641882868 641882893
    0x16060815010206040510150b0316031b0e210102030c0403140d020a080306040e03070f020f04060e0621070807030b01051e090c090a030f29070c060617 66
    0x80095000c0d142031006001c50300c0c0507201c4030b48680d03c0c0604403034902c1d00c0d20f2191244108008000c405070603070220701b40e030364100250212400301b0700c00724050200e030400310700d01c6104012283c210030f074139415144c03943c84411103810825440407070f04d8181c1040103800b00b2034280304000d2010394421075200605a540d1400c5081003500102490541000c5a001030025900030b170b4081014140da650000e52140c80f91150030000d005000f080c0f490845a00c00401c1940512a40d0008010032034020303a44040301c1280c2406001c1503a611380100c40240303000d00e02007409400d084003641100704144003041000201c41c1c4945040110719400000c155005000a0080c4199400070500616048400607241040846075182d140364100b40c00e403056942100181c52000d5440441e400a54002c01a01142d9106d1402003103480c030004050b56064400c4d982031851120302c500c076000111141030000099075514004032061282803030700700d42c600e0f125500020004c4e09080000c07600c07041034024011803900e01d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 641885368 1250 641884118 641884141
    0x1b02040f29030c03031902010902122109181e040b191a011b02031c1b0b0105090a090b0406091e0b070c1a090c100302030c0417160608 59
    0x14040300d01c681c00a0f00c0d0754001e030750700004460f1485030010f041060303941c2030b00c0240c0c018904920042c2d00311080541c090a031030004100b04245501e0207285c400c00307107464103541e480ca0107540600d540007480780c00006041e6111408041e4001812140d442c003080a270b0b4860400c1503001e88007110345801200074048404200fa08181d40c54034000d81c104840b400e511660990469443c20f01d40c10310075602c003481d50140545a01e002c10340d40103800c075154101550300b41141c9001d88042000090100d60150002000c5c490f50381074009d4000502d02d44903401c001c00c210000e1006050303030a00503611540540052501c0e1f484034400c901031240058221081d041c800b00c0d4003450541c1b5405040c265240e8000038551220341c0341c1040803850036602462603444c08000071040a441c1402c078809031400c00c9101c3e0300001c0c034052545400c1d5103416400300d0940003035040e030009030740c82400b0420a005c1070000d4005005110280c0c0c503202c04440d905090300041c04604603443d0800400541c5803000c00c044540c25 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 641886618 1250 641885368 641885441
    0x905070302100f090314031b0c030106050d052119090e060d0f030813050118110613060c0206120907091803020a0209040f1a060a06050a1b02040f 64
    0x741c249201c603607100000040c113048a03400014002d220080e600000300b4001c005643c0003c41c3c00d00a1401003140b0b8038241c2d80c5c2d0a001200c1032096090403404035003030810020144480d9801002040006589819180301c4203400b404c1d02e580700002c0c0a0840301520172650b00c140b00c0f0040e19040c5903103042040989004d10001e0071b0a010b00001c2000400013048289407030402d0303416242049158070362542c0d010f0701e5080c518001c1c28940c01c10116940d00c80c1c0d00302251341c0481c0318080081907607528031300740300c210702030949404a65915860200310080c02996a18103561000300b07051f182c0720700030a1144d9040420384801585502020040c01240c1c100e2140400f031340816800080400d8160b94001d560381d079802c070700030f02886410000c141008a01074a0f515642c0d4000380ca030740384100d01012144421811109030344104580c003000118075004004840501e081c80d070700d40d00b007440d114016024584a50b90101e0f04a41d40305120f0b82072480ca4491216845954070410308681c0090441c107421404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 641887868 1250 641886618 641886649
    0x20106090e211b1005070206060102031801090f030605060102010510080304180b06120f0c0a090b03180d02010c0306080309100c14011107050d03050403020613150905070302 76
    0xd480c038100c1c1001030005075000d0305004400656034800210304410141d015040d0242c9000305001c030600c0c19044049040010000408000c005558030728008036582c92040e01d1047c05070f00b00f0800c481c0700c818040410450b510041c14200c95550751211a22940d0b41d8a51055403900da849082c00020340e428010544c111480b64405007115040104071901c900c110320880f408025100da18031b40c01c02c1d843d00b0144007018020b00954480d41c0c00c00d00410b02d600115004196014680c00040f070900c0e8410983d85801241d03074034a58024202104c0b0982c2d175001800040340d000d401c041a1900700020400e1010718070b210360010030545ca080d980502038540c2500b041c0c03450341041c1720513444d584a0315180f4800420510380410001101d040004415015602e580030340c1d403d040c10351404402003001030075654483d40c21601c4849100e0f4049049502c21b0700c000b00103800c004045072501d41020b0010307501a00961090300d02440c440c600030700f214002c002c111a6900700100070020f5144c201c00c5d0072004034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 641889118 1250 641887868 641887871
    0xd050711030d05190c02031b0102210405210a051f0504080904050714130f0e04050604060c02010b191e0b041e0504020a080603010506180a02030601020a08040b04030302010609 77
    0x80c090a00a000341c003480e06074084d1441c4080391202d000341305100890100b50003800340c82030403001a6100690000381501c1a02611415070308141004440030503040014013144094100f600f00000c10080c079082c28040c00100700d5070030000007064000e001c03401c2ea444c401c0c001480c0580c922a4240108620f100b02c003940507141c0b0f400c02c40030070304e040100c0b2480d1038101c0e00050b00e2b0750f03081f10984200b584540180c0280c00d02185511800d45040758030010b90b40c240141e02512030fa40c800c1c01d034160004840c000d0554001802085c0010002e420034405145203000102e8031400310004528140244510303074500300c1800e2010010740c00c4a072070103104244c0001c01c4800c014109801c22865100b284660030610751311100c0030707603041c0c4a429000081c000040083d9500c0300e00410041150b0740a4030a10f00c29464500070504619022501c20402c0110210300d11450303a962000c1030013900010841030550049201c440c00040d441c6000380050984a40a55121402d5040c000d003155200c0e0000240079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 641890368 1250 641889118 641889133
    0x210105040e250f031a1003020d03180b0a050304020f040207241401090e0c040c171512060f01090504080d09060b0a08011d0106030b1303110d05071103 66
    0x4000070500c00c00354450b90018410540895000528100309075206440d40904a0700210070401115071150905a58400c4001c0507181c150010a403141a840000c0d8130072141195480020301524610300000d0f00310340d0f01807510b80d885800c6079159001c91525170004500104000441c605200101d00700030060340c0840c01d00b0120368610500e000c1c0280000c50704100c0900704040304000390054040d11180f0a030403410355a46140b420050802c0e0742c00c1304818050390030940030b1800c1c980b00c1d8550070203099503142c0804090414803180490050b0212012623002c0ca8000c40e1510f4202511301205022070003009a45080d00d800c440d100313030607085808006e08103418080420300318010350b0b50040c00010001048001031074554000d00750a12096000100128002a95813041d404581040003c007041d07805800000b1035a800c130b40a500004024008810126000241c124079054010384242030042480120190051034410f5420130040064800500d010411221800c04100214150003d0204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 641891618 1250 641890368 641890391
    0x30a060f02070b0c092119030e18071d06120907030b220b0c0910052109031602030721060c080603061528080f070b160206040b21010504 60
    0x2d581e400300601c42010741c10811306828640a000340b031f041e07000b050300004c0048920314000d459243e014111505c200c0c0d1250220041c910b044080c0b92013602036a80c1c2d4124402c0451000b02c02905610070250002004c2c080703000d040c02240745003805500300c10001c024191852411b60f01700003001308541400801c0700b20995103000c0c0044d20424543d44014402115500c2007411b908602403043e031550700900d4854500b140d5500300004003c15483d007041c2ca0748d840c0da003c0d07034203803000350940710804141c1c000c01021400c2c0c41000b0802105074070050640c1d1619a07200044110b1040d6001c100045400060030201000624030070310306110741b1814200e810345428400241c031440e005103440c143d0a4071080220342e5940784418032100080040c100c2d03150701c46800d80b07403002072002d005a174400d10800da94845007101c00101c000840b444000e689160801c8001c80d0348142000d84001c03a04020705004c00304005100b50b003d0000d1504d02d414a02030450150108a44904107a11050040d0702c4d110803902d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 641892868 1250 641891618 641891629
    0x31006090e07080402040e061501030507090e010509062418040e0606010804050309061605070501030b060f1c020f09040c0306180b0a03060e060901060f0f060806030a060f02070b0c09 80
    0x2d00084606140080d66500d00210b00500f1048410000e41e010701e004124950541c0d542c0e03000f01c4482a80c003000a0381e00c3d42e5068031545024096140700340304110042282c0e140c404107d90b402240505503104080a44240718004000280301134101d8001003400c14400c4001d082c2c61864002c00c403010301140050a82d91030710354002410450400c0700400c0001c05021003041161510b220280400340ea406524a20401d821400101264035000b1120002034540c8603008502103040000d141518180c03011010350000e80c052003043e0081d40801070082c2e1140840e1001e031252410843e1015038540e9103400300402c4074800c030529000c0c5450407800b0b1041d810000f004108543c0240c200040b1941c0081c0025102c100c0b6034402048142407031051a10383c080402d5940c00b868100000b0321460fa11000800503080090040c01030a055846041020a11a207040d07031300000c02a0a0f00c0040400e40c40700c0301554807802003110b0807a0002030325807c202c2d80240c0d80740d000d4000183e5a06202240c4000b41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 641894118 1250 641892868 641892871
    0xb010305060f07050a0e030f030c030702010909050103080406050711040504080a0f1d04230c0702031204150f17040503031012021f050d09110a0509101a0c0111031006090e 75
    0x4104001b24810410320340b020800d01004600c100100c0352507086c0080860f960381d001e81000c07400580c1c850000980400140030310743c1030303c3d4490b0f0914180b03030514030100e40c07981081c5000c0c0e40c408180c120f10111030316248651405607004081c134503500c50100b1405054a00b80d45504c00801868a40c8a409007001510844003050221000728408550040149000004558031645c00c8000d0050000d020740080060400380d109070296411003c03104001e56585c029441294042402180d00d944414818544407240b0a940d0804414401c003000440383c90240c11a1300b154603070300000920421440034038045000300301d026400c0f880e600156000c109900d0f41d003402c1070189072102d804900d6441c0a9030a42e001107a00403420006460f980c105500d24050602ca04d5015012406000c2804d0401c2c040e09845101042104004149440b00b90015101c03007822046020100341f0045008403000e000302403480062032400c03622814400c10490b5441c090394840014050190f1007046408007100485 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 641895368 1250 641894118 641894137
    0x1020d0e010f020f010e011a0105040e010302061308062e08030d0e01061206140a0203061c0c0b070b1611100b13020408030a0f2102070602090d0b010305060f0705 71
    0x1c0740c188094040a91400080082c1204d155090520010b08020150f2180c101022652200d500030b54921006482c50b02c03c42c0600c4500320850700050003d42460001480707020b540e898490f480c90340e03980720f1a003022820381f81c00005118050715104590031000004800e80e1110b000407005d10700e07100c210341e61391103003011404031035031a4003100d210381c0300030b51205008200d007151002ca103220502d00030b130081900c0400c0302c0000400d10702083c1440040d1095034402d010103050101c07138001c1c5070b40d90508825500c4003156800401280403c00440c8000035003c507e10070a580403080c20440c0201401000707014480c01003104a18001407a4440020f0f83c3c40d2128000d140001c550b00680041000001c030101c81d4240c0900010b400900030100100600040302c0c1940c9200c006c98582000b1030300c00e1607000f40e2503a0461841c41c400040e0080380d000700601842200c0041c5070400d0000864003a000c403900650f00342410702e0040044c40310a12246503c6008444c400d00940740000c000b03007081c0140c8006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 641896618 1250 641895368 641895377
    0x1505040614040e010e1606090803310f1e05040207050606130b18070f0906050d0216170c1203040b04030806121f180809100c0b091b01020d0e01 63
    0x2841e2070f84a0079841060301102030001e5602401d0030700902e01c29400301d1302c42c00300040da00c030b40000365010021055619070580c490b192441d404130f903070785020400003a586900d440c030502c80300000c00c01812100300004140c460034411049004a81c840344485c3c8a51000740114010400e0000051000c1602c0f640300004950310010000c0000040004046401c611600104941450f442c09003a030716103140301d00c4030743c0d0717424411004111040b80c0031041391049c1004900188504940400b00b40c01034500e0070b01c9404940c11119158807654441c980c82d49006404070320000c1c1d0400c80047c1071003200321242c0c4801c85a8514200303940c0c1d40c034041070010005005c101150b030114034565924640180714a0f04002103880d031002201c80500a10000c46048040c0752801c490440c0e5145c0d0051b844012942005000781810790440038050049000c2e00b50008100d071607140707000010342d200910b5025000c04001007604803600d110303018224001411003030541d0300802c0382200b100d9203c0048040000f0a01c3d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 641897868 1250 641896618 641896631
    0x20307030204021e0307120f200f13090b0406081605060a0e130501050910081b03010603120e011b0b070e010234090606050d0213030602040306150504061404 69
    0x100d41c103d52801d14148410402c0c00000d00041d00c0d48015200840c1021460402040423000044c03400c40f0720342c000e240400800c0094981c8040740c008050401c80c0c940200341c2e85407481200c16910b01c004181c11110703103030b9a40c40c0d8600641c2410703c900710203090410b0007040c0c0c440c4150951640104984200c91080703c0000d00700c0c02c018810200841c601c1c2002c1c0840100740109507240003e0300e4240111405036124200144003600a6003070b140071110040007412030315840741004e844100d0348109140d01907489080000000e5503180800008802c2a92900700901c801800102400210704003582041d00407110403002c02c15000441c0c1c1c00c00403506185115911440041c0d080940310941c0380c0a041204452480d28544204501c401e80303850500d20303032a00d8070340004000b200c0d65402000d000078010320680400c18020b900801c4800360000d04003040f160303642d480b50166401600110340d131a0701e078204151000c10104c09100641400c40c1c05120440c2400c1c020303070384001a10381c0980305946540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 641899118 1250 641897868 641897887
    0x32f01050334120c050f09040b0a051f0206011208040e09150c0c010b12251511101a0f0109030c030f0201120207031b03111c11070302030703020402 65
    0x190b9842c1c0c000342c1602041c40400c580d0750142002c0c82030a8500300303003810a0722041d40d00384900221103581e42066981e60404500c20b003884020b1001c0720310241c10000c9068082405d55a109a641c0c2c00040d0501000c0301c082040e9000f410584182c1c01540d15038460400c010000d05510180c4058440b040c0c0380c0e032000d0340d40210152a01800c00407086450708900b050114120128006002c1d50358008024004600c03400c0900c140041c088480a586801a114440c5000c1800c1009011100d2884001a2260b02c429a05034101c0c01e40c401ca4011035001c80c80300080307240500800001d50f151381820003200d0240764050000c18542e514541c440d035061103080b81181e0103409007002558000150751141500d0b1320707014100d0820307100d003a80030408218900458100c60b00807180890f901d969000d0510081440544c0260b0841704214240003c140c0c40b03240c000360070402000c007a4003c100c02c0100d0552144082c2442c2d4a90114012a400407101440561030004044081320740c161001a502c0d07000c1c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 641900368 1250 641899118 641899171
    0x703030c080d151424030103020f010903140303010504141b0a03110c0a02030c06070812060f03010c020714043b0a0b070305061008160203090307032f010503 69
    0x1452940c0341c0c0c12000007044e4080c095190024a42040c5c401c04407000700c400b10046442d05502e90000c0c01c001c20401800141000515100c0000b81030500707601440e100d035940c54405d0031068980c0c605500100c01080f00b80340600a02c08410070200e0144521304028130b05002c3d80c0c2c00b101c61203c079804005040780c502c61081d444000c0c84000384020540350341740c111003542c84520b1000142d10034810503035240441c0c27402d02d00311200d480d80320030303503c0c58200c4140c0b018458140c01003100c1d5114030303042c42c1c0c00300b50b4a0030701424200808a5029204070340c10021250805010058054000d5140c0009540904070188118001070905594411188680b1300e10f41d44034135038182e00790300c11f0003020105010007000c189860b01411250301e090009503103000520034508020724448000820800124440e241820002d0401c00e6262041da0300c1d080700c1c4000300e45440442c6e4402c0398500744048004041500e01c0d0301d841c83d4512400a041d001050707a5000074168080588203014011400c40c0002000b0b045 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 641901618 1250 641900368 641900381
    0x315120f030e1207120c0608190b01020a0602040305030a0930050a050f15070f050409090c150905030f03030601020604030810031203060501031a01020303150312160c080703030c080d 80
    0x821088503090354503a55020f06a40000c0b00480d06c1d201e000b800490400c0c0203401107441010a5240d0483c04201d0120310781c0a080c1402655065000300d01d442000b142090000f040034501810003175075106080c80e0000c010100507841419010700c5518034800909050702d8920444d0313003040c841c03009005d003414180e05110030304800403d184030385192034003001070101d2400107003410000c00018903641c20b40d065901c1c007058100750300020307410401030000b04a9644402c10300c074040c9403002c40e00c2d5155070904085c6c464000350b2401260349e800080006280c100b0140d100e20840c24059421400c0800c0040c3d078501d4080d01c014180300ca02030006107440b50250800c9d0046802880c41c44100a500e00c001d4014112070040500003400e0a911640d85100481c010319096410f03030085145d640c840c1250801900004d03450f580c580100340c044a2101c0c8808054600c18040c504d469850628070710f00040c40211550101c0181d80100d2000c101003600644980410f41c0c015045a5403000c0203040c50005101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 641902868 1250 641901618 641901649
    0x70c08010509012702060f0f1905040f0b0906030a182120060c09040b093c040b100806070807030e161703090a060315120f030e 56
    0x1e04030801c80500d8054010014006000150701c880f483e03008280e0150042c030340c1e0042d4202c1000c001482c090344c602001402e030302c800c0e9505c0d14240180c202e00904106820b90b20745000030380104050010202070b07001e1200a100001c2c005140000040c0451801d01008050521059480301d2450502845000741039210f940003803800b841590b4010f4004d1800d4030500c01c500019419940d0000c103a8210b604211000c1205005041c2941c401b10100c6e00365100007000d40d08591607540c5040303141c442d458001d0250442010051015011401c00301030340c504e80e41908020b5208080b0001da010305080c2c41d41d0007039081509502c003030740c4d14590801c0c0d00c5c0740b55010804501c280010442c1c0c1c680c0c40503100b40140c1441e9818851b110049543d203076141407401d0540f034070701070b40c0c09d00308072820304003150a83c4205801c00396800d00a1a07400200048404e0340000003098942075034141c3c1d4000006201c014004c085060641c1c0e2801c2c1e00c4101202003411001024440c04400000240d030322000801c60010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 641904118 1250 641902868 641902871
    0x6010207030b09161205030d090206090a0303031a060708040b0a0917010e0105070207141c06021b160b04090f060e090a0309050a08060c0304211e0f14070c0801 70
    0x180f02030300564075900100c0064103c1480301c070110717106941d0a007a140240c1c2110045040034100c0075040010035544600326844282080303005035944840c2d452000542c06501c0c0001c0e0b0407400d080d20301c8100d20081e801441850304201c81c000085d03d00003a1015034020403c0d1644400e00d01d20240c600e910f880d00800046506011900d03542c8405421240700a69079900901031520b6283d03099035074a00a000d5050010300000e000321403814190322003000382d0000003100d01c0304d0221340c503484100c3e44015440090107200700a003040b1000c003044240c0c05400344021a05a052030588002e00d640103900030a20841d449400d03030058440c1d2604040c0190201660400d06820420340550f0b0b80d00c2c000c0800c6020405864000915140140417130b021070710305401400c0c0303d51340c030b205842c41c5d684010001c44444c04071003440d03070544024854000c400009a00c42c1e2411440c5d401c00600d04a101c00801c20400902d0603d69030040d07888414411102c52204a090310f03210300380740c9442c000b0380380e4200c000d50390b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 641905368 1250 641904118 641904121
    0x106031b0612060f120218090f1212060402090409141e1b01143c130302152203060e0d0e011b02091e13150506010207030b 54
    0x18905044080c1103410503101c0303003108040c00c507042042c0c0342184038a00c4aa02c00d94001c04c8084594206100707110701c0144040c00380340701040c402c2d10903102640c0a01c159845010949032401d002c00c10702d10b0001902c2c1819042c0700342281e09600703415000744007a02541c1c0100c0e20604c152103540100415aa010084c442006804aa56680d07030070001440ba01046c41003103410440d044c04502c04426140c88050349962152046c01941c080d50301c2d1401e14000c04041060000000710324116030121030300e0540b020078408800c0c2d001c1c25244241c0420500002040000c0101c8174181001401221f90546100004051540c2c0d9807410380504405508d1051401d01800c001c08201d00300789041d03030310540e400c1101c0f0149240151303540c11000c5210010801206203a4203560192046074640e000721042552501c5a603804903803140da050745c0e03c142110504881c4000300340c0703c0002c50350002581d44100715041c1c2035141ca408d10005054441d0040c3d40e5400414540d901c2800769602075500052442080d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 641906474 1106 641905368 641905403
    0x306050a0810150506070c15110c0d050727060f06020a0b091c050a08150d0f0c0509040305040924090203061f1101060b0a0c0311010603 60
    0x114005103e00096954817800180f45062090b00000011803402c2d5425444c3c980b500b1584040c0440c00e41c08a8070000005000d0340c46100450301c001800013941032050804c280c07904410b100c0700c0d101012aa010010300b06102c80c910040c04100001581c4e4500e1f82500070450184000680024070b0200109501070300350354105028806550304d000f803d4000d03090500c405650400460300200300b00e207103141c0200225030b029581c607410003440103041e07000981601f04a440100718004120b00e140611803420a254080e04003d4071054950900d0f00b4054501c0d0418415800e485042800e2080440d8a5070502c0b0f1000c401d181d44c0030585c50805481c076029400041c29180c10000c410f0310f02e2800c03040100070b8424108603441d85a0562190792845007515000d40101b62104020005c1c0e481840c2d003c03511080042c2c052401554050024004501501c0d4540c000781411030307142c045c1303001d = true := by decide +kernel

theorem cover : BRFrame.Cov 641726618 641906474 := by
  have h0 := BRFrame.cov_init 641726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 641726618 ≤ n) (h2 : n < 641906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
