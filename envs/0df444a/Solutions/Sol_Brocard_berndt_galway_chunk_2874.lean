-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2874
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:59:41.712076+00:00
-- url     : https://prove2.me/submissions/6c5fd61d-c6e7-4496-85a0-fcdb7b837f3a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 516726618 ≤ n < 516906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 516727868 1250 516726618 516726629
    0xf051204150e0a081801090503011d01150e13031106090604121704061a0a09090b0a050610180e090109060f15050f030304151205070c15020a11030f040807 68
    0x460310040340034102221402888400e1400300c0341c5e8010300689829945038030203601903103030034005104103a0104181900d024150000c0c00f40c1501d03044094910f20b09800780d041d802d2541c60224400f40d02228603000c0c094424101007003078003004000c050800c4401c07100c691540e04401c080100700a000341c0704c0349008519051801507041d1100e06540002402400240306580d584100c0308443d45256401c880e0700b800400d402c03030300c45d20b8a503184050080100121048201702e0041101e120281c0103140c070500001e00540e5810350015001c54a80242210a40c2c45103031004001c6950030603e03038458072402e620800031442450700d2510200302c1d092020711081a0b0725183c80c084403003140081207030445070202c5001c1c50203841714001074214804d580c07017101c2e0303e00044038030440107400c0505954206000780e000c000e83e40e100a0161149182136100400205020940c10901e5500da03000c1c0608926500d41205002011903502c0e1460b401280101c43c1c607200450204031950703041104001409 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 516729118 1250 516727868 516727873
    0xe0303040308161d01050711040f02041409070e0d1e080318011b0c020f03060708040b01090902010e040f180c0f060905030709090f08040f060806010309120f051204150e 74
    0x7604900344c0b0071100700130511904202d00003c0b0b860500550340022462007030001c00400026100245040096000d84501010049021315007140d40c941091080d00c1160b003601d0b0680c13078036401001c01101c10080c074411510603401128240a007440c01d182828070310711030061966a4109030103014210705080745074400980c10f001012070345400c06403403034140200c1030820020000c410f00c000754042c80780301c1c111601407080c07038200450b055003c500580224090140c0e0403960362500701c110203907070003804040d010400003e115007242c182948400144552500000ac40202d0039200300e82c1520b02c418203440030000c40d501800021140820040200740c5030411907195864203021a840340254030a48040a81d181180350a01000759070707242c2d0003a402810640d80f00c4d16541d4408200e09180100c000254021000500c035500034071503c65040d40000d907101401c09007200c21500d01c0c890f4203140c4200038080c442d581400c09005189030140303125441c41d0144a154005020459019404424241c3d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 516730368 1250 516729118 516729137
    0x209060d031706041d070603140103050601030305210a05060909150a020c032b050f15120709180b0601091d100b040305010515010e03030a0809010e030304030816 71
    0x30350482c20800c052029960280c0341075907408005030040c082c40381064806109580103900e10000403641d0010b581c0651000c0000746c00e4030101201c0c69009000046c542e6101200510100740218081d2a40340a4440010402c00e02288584100a01650045089500c58007400018a001d00e4126484201c0a000f0141c0340742c1d050041c0c0001c40d000e0b00402e12194001803c80f1a42002d2003296400c40003104000030707802100003603070040907401600b211050310300300108550000c2d0000942c081d02038410002e403180401010440070750207a0443c10860720a201c00012000d0030744c011148454400c524180315070310541000181c00e07000509840c10041030f4103092040d21072240010241022802c0c0d00ca00d595180c108400600a181d0400f90000401103000030400005400440c0700d801c601019140e40c038480340041d216200c540e0402a45900b0034000d110b81107100341510f0342d02c200c001001080c0034102c00c06450440e40182c030103400064100b0b04224400400c3d9468410030400c51420004c1c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 516731618 1250 516730368 516730373
    0x14070804031209290d14011503050916050f04060302090c0d0f0504230c0607060c020f0a02030304052701031112120a0f20060105030c0402070c0e062b0209060d 70
    0x41e544000b42820301c04001c19480700c0d49941d43c0c0a155516807a10341441156188d078481075405810501d81000a400c9c000082d4000c0ca010a40c1054141803040c0045100d040c0b0003000501e400903854607801c1035682c0e2002001d6501e80d03840c9030042d64000034080c0d660200f6420b0b807040c2c820300c1c2201e55220f810031080c040001c2c0101c08000303860b0404000e00390070f9a030700920242043e0725101300070b034401c6011624070705120740307980034000041c0d960702150120341c07123040c181c5d80742e00320040080c0d85501300b40410080303400d18080d01c01130007403820455158135000e42c0340c220101784281c009881e1550340103200741e00d5042c80c1085400c0030f141c0400034007a01196801d10091841105198010461010100c5a00a010705050503015601100e0f014000421403e840e988540034413a040c441e2007808440206420144215490b0071341000c401254076080c02c0214003001c80160141d50854010b000c000394400c0400c80c08108000ca054803803855611030700400460301000340986114240500c1354000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 516732868 1250 516731618 516731669
    0x171905030a0b0616030e03070f06030203060f1206010308031005040221010501090e010504020a0309060c12060605070201020a110d29070512040b0415090615060201060f0614070804031209 82
    0xd00c6174107140205181400e000401d0a004441c1c0c405030401c070880304080340c1d43d6010b40107035215020a5031642c6003100003c041000b120500202001c3c1c2c0d03000b00c1c0c0140f000c203036100011a0300903449c40700c6a4255a4440c04182241c0c40106006000d040e45116500e800c030005090600604e030074a40520a5404c003c0840c00d0b008040c46003d20559000139a0031030315003c0d40160001e01d812079010003206607590301c041d0484645071116000a4a007240128501c0c0c051001e56050580690003840591080c0d6504846c00c4003040c3c065500030050384030600064010004c4170144802e600e485c01c00f42c0c80d151021b408410000d00107405105041c840340f5204021100c50700d9000790403005141e016161410180e41c84007001d0360700307600207081610520501400341c01a0f1000314640d281801010341e1014100d0880c0d19501441002107051402004a240702c0d00d078050622081c14822031030702050f5a90428954007c0d40300b00d0301c0500061034920344642121007a001800c44000161445402d1413000d174 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 516734118 1250 516732868 516732907
    0x20303090601061b020d0f02030708120901030f0b03060c0a080105010207150c06140c040501110109110118080a150e010903050a0513050415030212010c0804171905030a0b06 76
    0x700201103a4001c04845561584650313240c01401000e4042e4440c103104600080c0c50702c050b4020300c507102c00000e52040002d981c0c040101d230700d0091030401610078011806890a00c0e0110b1080b911403040c2031085e5000d000d02c500402010074001c0c0e0310a00d1000142442105a000c58103640006808018480c0380f151003802c0100145001c618107c4030f840c04500400100c0340041a48101008000d1007601c880020800c0d64001d0f02c070031582110b40b00d0f8182c01d039001c0d5800100810100141d0180a50007041110015a9000100c4280548521031140b816003400029070708040c4101210f030a43d2807510031140c071009210024400d0068644001e00030348901194402008000214a42c01d001002413020207000010f00c00d2020a40b0f010b01c40305001250300090340b24a208107810901c004051050801070380064031003003e80d507a15180c100c0c00042c480341002540d1001c021403191860100e01024101c000340e1611a160304100b242c510441d1020104039005000410240c40b0b91130907200c400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 516735368 1250 516734118 516734129
    0x507080c010207050411120405071d040f1112060c0702041a0123070510020a02060618072607020601030314040e0a0902030c0a0b0d0b062502030c180a0507020303090601 74
    0x41000e00601b00d03024403074400c4150000080d81d1410502080103000b24088049070b2400440714810020304141103110041910003c00201021054070009080c425150340c684600401d41d43c2c4d00000702124905024003203d42410300c0e040014501c00710b00e0588600790740c5942002100040402c4500060729071780aa48921200e002c4280210380640c5d90701d412035158a0b4010141c90700c0004011003032001c2d411414200d4098040c0070300098041c18490041c98101c0321001a8882640310482d05640003500015520038000c9203400c3d0ad01740195032101c49009509940c02400a9803460800500391811000d0481540d441080200000306c410070100d500a881c0c0702000414940600c0002e107012032040c14260803514002002586d0807640001e8a00103018803014411a40b0710340802525108400c1c84420b02c00d02c0c0130001e204e01280040351120a0320290841e030300c801030500040c1c00081d0285820010b00d009004008000040d03020745504851940001c504604101d1013086e100c84050140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 516736618 1250 516735368 516735371
    0xe01030b031e01020c01050a0e0307080306190b2d0409050910140f06100c110415090b01020111130308130b0d230702190602090a0905040507080c0102070504 69
    0x80c40964082c400b08168200d0241c006075400254808240070b90030405101c2e07559460400050071080440c000e00211485081c0510728012841ea02ca6010303800260181fa0402c251080a1204212210200c0d014002041d51035031601e8803005800302c1c040340902001291aa0800c0183e1221710182c03d81d010f4418010000c41c00c1d9652075452407030999a001250755050603c2c0141c640d4102409d01280500e4500004c000d10366034135410300c407a0341d00b0a0503540004030385c08151004210407800312061114003c1002c00d1441d080c803d00c6045540c25004015140c2d80c2e425200306a41c0c091003004c00c40c4006000c61070a00c405000044250301051001400320400020056071007841c18000c90003501074014265100c2c408060300c400100032003800d8620303440c49040e400d425000e480858070300c02c146950082044186025141849690740340b81118a1502801a60400d039a0f8010300780107060b040200083d83e24181c2491403030403da42d4000d2310180c10410100d5030320b136804a045810768006450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 516737868 1250 516736618 516736631
    0x4150902091f09030b13080f090d020a031118010b04030803180d081005030a120509010e0a08100b0d0b0f04030e1c0b18070317090910240e0103 63
    0x8181d00c2540c410900d200340b660080000300035608580e411007078038081d0301d0083c59a41e91001d014103039001c101016000b0300e028091652180004802450302c0e4002903c454004091903010175141201c036002100c0e40042103c10352400d0400202107144e08600052185580d49000300e40f402c50300ca5408090440c4100000144060140c40300c1861100704000c103d60003411618002059403d0555681001d02c41d4150000356a140003c1c0221280b0741040e03200801a00350b4a094501c1d500400c040341c140040c5490a001e16514148030000034034042c4050540115035200d080121640c140c1c0301c078402c0180e441d404000c5003464981c50f52100103000e80710346c40e4860341003e803100400701d5a1140c1c88901d00810b10f400a070700c40c055011452040040c40d03000c2d02da051601000c4001d4104101403a88000420008101c0802c0c2c9411600810310a29240c0000c403800f180d03a061041f0b6052150b0340343d000b003c1040070007000d00f03c0481e400400000d40003490801c4001c0010407c5c0031007504154880301c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 516739118 1250 516737868 516737887
    0x430b0408040b1909060c02010816020c0d0b1005010f05030718090f02090907050c2517030403050c01020712150f24050f15030903040503060a0e0c04150902 68
    0x20484000d4004071094540701c5002428220010f21403103c0000002c0c450300001542c00c0c012000c1c0025150b0584039058259110607032184130046e116055400c620599030302c1c00701519505002c201860045644100615000041015003400c039802035041041c0d6410503d00c0907030100c2640c0d04000b0a103018001e00c18003071166520180300da0091440c95142054110524245500900d043e07070041c4d0350405295a090016111409403c0c542d44035a00081503502101c0d14a0030000b002c4840140304094a5841c0d00324001100140110185030b94000a0300303005100342040302890540c400d2008045850414900209032501204001c14602d0415484680351003181c0016609010388031042069036411030114403074a10000340038008031200f0754046400d080c460038610484502400a01d02032042d80c05888040c1d10081042459020038440801c0ba03a8041c0700d054020b403032804020072075190380d111030342c140140501040e200d249000c50f01000d03403006440450440c0c0d400d060058640306940d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 516740368 1250 516739118 516739133
    0xc1809060115020708010c0503070305060a053d0f020601231c0b0718081207030c0302030403060606180902090f0f0301020c0106030c0906080d0206060f01090b430b04 73
    0x1900084170b59400c00500380440c5500c50003031032140615580900540d15018103200701d03107007a40111904440b01e8002031203c032040c00010780900500c2003071055141050000c029403141c00402050000d0581040558110b50420045000d8040740c0540201c4891110309107404a261042c81801500885a0464500c010052800085400003046155454202802000a103050034a101d16412440c4042031242d000a07424045081f000300d005d10b0329881c0d8800352094840c88504800f1480708020100000b0940e00843c0000c1400d46c40f501080509400c8081d510005030b0000e420303880c81801035082a6a641c51461003808003a1025a07003002d207400440c0c064070910300107002940c02d0820010400059626007021031f40a02001c00a05803100b20711601c55058111500040c0d11500c0420b44501d4440001104924141499143d03159210481080350300030401984440d00259880f4080c4e0100c1854141e001a0b41d101202100e007100505500035021801c01074418585800043c0411905 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 516741618 1250 516740368 516740383
    0x1d0d18030219060305070f0203120402060f04121a061806041b0c14010509031b0c0d03030e070e071b06020c0f0a03140a080103080306030106170c180906011502 70
    0x5042000c4040b800c198038001105144075500010f0f24000014072454890200d2460741d8500c0d13805140381c034401c100c103015000401b41050380c0c04003003081811446044c0070020801031040c1c0c0b000e40125101c5041148420700480044c0d0f480441d60002c201d4141e8420586a40d545000fa80300010f9885000c0840d000301010240392722816071821288400907040003410740503034030541010200510720840f150030b0315001d4605140c20f900521031640740c96404400310820b406c88a00712240010344c440042d078802c06207a4180d000ca50359204442c280d10003400303140040d080d40030000600341082d1000514040c00b443c05004c40c011013030141401c01009404a681c4c540400e0111081074011000403911001c012008401040442c00034221169640c4241d41d041000754441c10400d03880c5407240d1090390300060516a040d561032201040c40400402040c0030b6222000050a030ba103951420b109018002c01d040e68040340d41d24040185803000015402d041d030303c170710000c05050740c46060241e2038800b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 516742868 1250 516741618 516741623
    0x5180406090228050315061c0606090c1d0603060d1407080304150e09070309020303091909060603090206160507030b09061608090a0b0714130302041d0d1803 69
    0x2090510f0102c0c43c0c41d08003c29051054108800700b05030b0312010180e890a4041e40003003d1036803e400a0400c3c981940c10181050b1948505100003515603110421201550170080f0310980d694455503050b544031907031382d98015045d0050000702030403e0002d0b0035800020507640c492500c418001e41086100c80c080d10341d621504044900080d03c5454481e100d82050007600c0c0d0990714140310403215803140111055404024241d07600c1502c03525800c402504c0d204c04e06a800d444108002800c68452002060040032101213022111303050801210580f06254071100405045c0000030700540d480c80c044850142c40c1121a0900b24900d00d030690428200c0d5001514010f0314400700044280c0200c0d202d445802c00074208000403140d1030b820b58100105440d206010b501a0100b0400512081e0400342c0041550a2807a00d10626050390305156000c5d00c881906141300d028200210306290145108981c410710301890103002e11422a03070348903441c000c00810400c125a00502140c50801d00c0000f654 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 516744118 1250 516742868 516742879
    0x10507150501050907020604031704080705060a09140c090f10051f26190f0207030309020a0e04021f05071a0405070b0309070b0c0106091d1006051804060902 69
    0x403036100005000300350074071405000360a6840025041840890407a104503815114103643c1a24400740c81c900c07040040c400c40b42d850040103010007240e0204039451098900010104203500e9a19010484501407210078190394071030200a0f40ca9075a80400390343c001540000c1c15030079a0782403c503008038012903100d5500900154000c0b014190540444035a011941d101d8548a60005800200d4190f095448098078441480400c41900c2e2219407045440160040441e45950b09140342040340d00000084003c203a0360103013034045040446030301c4010401ea0791700342141c1c40c250300410320304013032103d0684c550219901200602030080e400c0e02d26854100002043c4402c00035009489a00203450658083c030a4000018056054604072881080c07107102401c1101c1c074000008070305820240320002c180d505d884000c240c806942c4140c0c046034081492031104041071103861800c0104c4c1101d100d48440c1010001d00440e11030b25203091030716580214402c419074032804c01000030220480d0007503012 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 516745368 1250 516744118 516744143
    0xf02030301081f06121a060a0b0919080d02070303081015180b0d380f0301060b030a1b05040f0e070e130204091127010c0f0503040e0a09020901090b010507 68
    0x6c8072603850205402d42140c18065540c03508010404030300c0301407160071f11070041088400d0030740c1841405c610071004c58a010580b102d0711043c5983c100540c1d01d01050059218207010000e150340b02c411907801c0340c00ea0000514041c20800400030ac10240822241031202066500081e05a011b040340000c2903000c0760b80780c45403520a02030340030384040c260302200a480c000d00300164040030780758203d105107042e1903120780e034985000344040043c41600e071652656886000290b030050000042d84504864180000e05948000a04280303900c00c8401c4002c0020600040c001f000070041003905a070070842d503a01c4035550382da4080356003000002c4141d4001b525240300f0325a12980c0c3c7c02074026101085800d00c40c0001d0000c04461a0103200c2c810600519072015051000c1c84590b0011081700e41031404040d000d101d511901801307184108119000e03800010100904014082200e81100581c201400740ca203881e0000780c3c0d05041802072060302e96035010300141c0c40e80030b178048031640355120a08403001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 516746618 1250 516745368 516745373
    0x90112020a0e01141f0f1107080a080a0306080a08040302041a040903020109030e04091113060509040803010501030506060f030f101d19110a0507061e09030f02030301081f0612 77
    0x740c0c00c149082074000c02945030042c92100c220108a0b0b41607030160303148501c5000302c203c07c039580d1102d189880e105000f00d660101c0d101c9402c1c00560000c0e80160441580c8a821010040407909194800000d40e0050558100082d14080c1120216038044034089071055a10804c9200e0620820090364800e1030319a21404264045d0440c4440d14000c1d10381b28402c40041051006a07030384864024440840b040c0e1109052500c041011240c15840320300003000e50b00c0754003183c10220190f506454501d80400108015a41070049071307070000c2c040e900b15040c440518103041150101074840c0031502d14110024030300013002d0501e03030000d149010500100c41d030610f6050319000c83c1554600000c40780000b4540032104a40101527502810300241860031000c1c101c01c960300d03040036601320b48054481c0c40040b0348080074404005c0c03410b0b0031040040c4d41c10103407401800c242c4c11900640107541090004100e0701c0004a884003016064104c034080c04004ca05400e0300906041e0000729002161040700d005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 516747868 1250 516746618 516746639
    0x33140d14070201110307050a0c0507080109080c0601240c05154b040c050a03080408010c0c0b1501051201030605090d030b100e01030e0d0201020c0114010302090112020a0e01 76
    0x760780550000c120902d04070b9401070451000322098000b00c2c0301001100310702da1103022140285030040c0c3c1175036900e03621b8203680ca01f540c103040000d07035850401242d95403072400148002c3e03004214140e00142207408030b802e4800811800301d290810b001206010009121041c003044212501d0000f90000d40e02d814100362004000703000015905070150041145a002001d82d1039110014a0440c020500140302829007051001402151003880c200c0e00003c4684071400d600002e0761107a2040303030300c445c1044080c9003101d9001000720304200304580b0f000f002c14902450603800840e5000110510209440140c401d84034100e0745a41d445005000001030043c642c0c0814000c15032101540c000380c1c2001c000728150341541e20031541c0301100400031303848a070103510524488039040c140440e13080c4a0103271450601c011844490090313500001c1002a49000388a0f02a0341420a840e100341c950450300410000d00d01401000780c081004200c0c0d03015980c07128106e9006004400000c41c1543e126840c501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 516749118 1250 516747868 516747871
    0x70204060e0a0c0c080d1e090510050f060f060f040b03041112030f0406231606051e040b06010c050d0c0203070605040311090613020a0933140d14 64
    0x1400d0528103a03503480024071404c24105200d4101c41c0144c2050041070f1018020b06001341d0001c04011014100045107007540100c06109002d80040e00c0701801302000d40c41580c000a1035110510024010070485a607913051034003141c10b0946440e500e449d0080598800c9100d690040c104000d004020032041080980c0140c1e02c1c81c0341645c0c600d50110b00320141c25030328020320100420b000300500c4140501441004842c0c0d411503102e4549817420340d03088021055900201c51281c80c030429000c19000e0000c40d000e611340100d4540d00c6030091455101e010190340d03502a02c000d00c41e502c02c1010030030580c440d05480012030742020695002c42030010011300b02c02a58038080380280030f4400f000500e00c1c000d84c1034400b100e402490720203c5030480c60800c402e4010044c03d50380d00a1440080e140d070100d80b0300c00752508542c0d58480781c5540742089984c0e10035034113502421761008500e00003195031004014401c050201d030340c2018000e411890008400c00c0c003d0103824000340e4074041d414030031041692202c1c1e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 516750368 1250 516749118 516749131
    0xe0a080c0c040c0804120c0b01081005011e03150923010e03070f0b180327030f0d1214070509040e06150d050709051315090f17070204060e 61
    0x210790090090040c88281d80403003030804045520b00c0c000801141403202502c0809400345080042c801041d035401c41d8504081e000b050103548201300d0355190711003600ca07140c00341c01c6120400d501103140289102c0004514000100400b52001c001c3c174840300765400c458012940a05080d84804c020504001c0c40c14130500400f01079800d00303c2c114800301c8003204a4481c250892004450545140c8411282041c05800310141500c0c0c03184502c003ca0007803000d0001441a58407900844800c00402c000c03100f2132240030b070303c01e81204801d4802c841d0001200a64460903050808031656a0a4003100030b11006143e2418425000104100c150788600104203165080750b003003142c1cac02044106903480c10122245d0b1807001e00007424103d80e25040122a503028824000c0b20443c648a10008043e0b8205a81c0503050110401070a000c11050b043c484940c61003041c0d041281110075201c0b0101c0348070204029104172206440800c180c81c0a00c201c6010b00d801501c144212580c0d140080c241c9a01120710 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 516751618 1250 516750368 516750373
    0x5040e041406150f0d0519050c0a05091006080c1902030304030f03090506040201270806180a080906090406210204050a18060c0c0c140a090b0102100e010e0a080c 71
    0xc0405002886400c2c80203006844c16003200801c1c000c0c0005001110130070780380f91087c1003084581c80421103d0a030040d100c3d10241541c0c003402d10501c9918403664010034441c500c6201004100300140000d1000c8600c0380c0b9140c105a101c4851002ea648290f0084100e4244410038402c1c0305500040118042c138400c2d60f03400840e031001c00045048502c85080180340d5003090020078055071190b03010a035102d0000f9905c1010056403100b10f011000e1650100311150020303010081c002241c0126112440203c001401c1103103110303600c01b0b89910410440c03d05c1200b004c24010700948880c1e100c2009008015403004a840c0f07484001e42d070503207030b00d98102d01c500d0904001610300f45244c095a440d0f50005e40b542c05c004842680d500c800741103211602820442d0310316144000c207005003054001808003409280d403101080040c8999280e44d6003100070018141054900d0990f80020404601c00c02514000340a803140c00840e03001d400c10b19036040b01d5108040b0207000b8000903000404d002c40300e0004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 516752868 1250 516751618 516751621
    0x30303010b1210060c200415081011030a0509152505040f030618080301061706040203071b03020a141f0c0207120501111602130618090305040e041406 66
    0xd41c0b03003c0540280700019400780300c500001401c9030301000c201b042e05002c0402d01d558442c040340485000ba03c2031009400d5021f003c0144010034010a08000781c403080920048181c248200a81d21018043c03102c0c90382e42c0c072b0000c5c0d1107074828001c1004e102c881d05400c44c128141807002c010440c04841702c10312409810494010490301a4044a0403100c4103204440c141e455512204020f01503c0c2c038090100140e0303038150300000d80a0000710301030809603c17038040600455801c02c00c1010700401850003944100188100150060040850741e191010300c9a1032100e00d14049003417141c0c44100405524850400c12201040865100f000b40b51074000c54040403003c2121000344d4000c0118000944c001c808180001d1901020b1030018500401c004200c50001444800c080d0780904142e012040c2500320603021803912400360000c1440c89401400040e0400040643c9000004040703000e107680d403050781007018041c5069070000c100c400324400c0e0038501414400ca03400c00c2000810102d009580 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 516754118 1250 516752868 516752881
    0x2010917120d051602210c03040513020301031b05031b040b0a0905182a010207030b04080304030e030d2f1b040e0f0d1206092c011404060207030c02030303010b12 71
    0x70701b110648a5003480c41c14040091360040201da403200d10002c640c0d0004000c0400c1540350801c0042c0d622502480060380da61460401f605050064950405040d4828600300709a540005400c041407410a0301c05d0030100102c80090020a010120303c0d030001038003400007a0803003450303008a01c40c0550400c44d108070000300c540380ea00c40801802e02c003808006d42c011058042c03808007003048491018011a21480c1d220748a80c040c0c107008490454542200108100c201a409161081c0001094000b8622084c00c1400900702200380000c2200b440c465130b032565003107080c2c0148841c601030604190f4111201400912076a620003030310301800789040c0307100402500c00028001482c2d4075130b90058030f22507050b2141154000750800d0305441c4282c0341c4501180940c010b2040047c1200000041c500540440f032042d0f4091940096582c0300341d14020703500344094941188640c1c041e0303000d0300c0143c0d5090240f90540f84101d4900d400313074140c440407002180342d034007041c010500c034491122441e03103035960b01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 516755368 1250 516754118 516754123
    0xb102102092e020a1a060f06030c030703060f03020306060121020403050a17210a1d030d0608030412020607081209060403080a110708210c0a03050603070302010917120d051602 77
    0x20308001c10b00120145203d20517010544480c0c0c010130b004107a020780402c184000741650f00240c6103020b081600205005c00385416110300b1004020081c85e900c1c0030361031500000d840d84402081c050500c41118408400f011092802c41802d865044086440d01d031203080c00f030b503100b1240c8806c17100d284100318070130503510070340064600348405186009103400480002c1c00448802070032242d6001d80311644900b18008180d00fa0151415180046485e00083c02c0800c05807240740e0300c0070400303410400c4184001030b0f8052070b5031040e60301600c0316076681036503180940040c400e80c26010070040c004001e001000d000407400038082d0b4000d61f030305c440c02d8603081d0800c0201d60b1614001044080c0401590300001d0401c0c02408440d0540300200c09007003c0c1c003035031848552003290743c0380c414030b400242d60b0340854040c441d05811940c2174000301010b0303003180c1c00640450428055000b010f580382002c10441b50041201283c5500d140c10425203a96603203800c0e01c081c1c9402c0d200a108a0103000c02c04a081e80300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 516756618 1250 516755368 516755383
    0x9010909022505150406090b06120c0f03030c15420d02040c02061801060e280204060513170a030f111f0b102102092e02 53
    0x20325440d0940004103600340140c401c00c12500300c88900901001d024240c4d001d52450303202c2c901030740c80422441c040e894a80c400c20001000d651045900004103015400e00003502c070a81c0b4401e44030301180a00c1c03d00000d03d1070040e40d0303c0700d00381e2103020010003038420b40701c50040c020b00341503415400007020700b417030f070484000c01181300503512042d400c03e851401501c25040280e018060809089a480c54001ca070a60f6031140040e40907912440c107020058601003d8800104a0311008208a50404200044010780600000b00c0d101c0d210f0324030700401c0e12003442c51001e141100011591b0f00e80c0d807080a4010f40002c0000f90021030f132020002506880440400d40300a140d00c05420410038a99054402041d840c14420400010311800d94813102d0400c40c0c1403031807180340e05500c40c1c0804800d140c1c050301c1c046000c1c94003480e8101c041c00440f640201c645590340f0b50381c020100c02c4520031049007001b0b01560300303d59400598100b0a02022400b661000704203802c03034250f07483d0108541e00982e6211310307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 516757868 1250 516756618 516756637
    0x30c060709150503190e06040b070309051905011b020c0a060503010803120c041205030c010f11311508070e01050405040902130e1b010c15020a14040b0901090902 71
    0x81c200c0b52407042e030b4490401940e1211071078140c0011454610030100c111580443c0d0082541d104030240028001e1000f00c0940c409d100389001c0c040200660388031901c9d1803207407000000e00d000c90002d043c02c00a0030b4100d295448130030000b074807100b003504100a5a40c4401034140380a201d83c070780b000c0341c0b1f41d00c00d100300c030f060710039a0340194a402d605561980400d8002491f0002d6008148408550700040b040d0300340760103000740021911011986c05076402c4407096504c01400d1403900c2104418044400b0a0f02d00305511308081030100c007801c2510032180c091960899904556480001c646000740013110b22140d0700d29034078403046a44da9003050398101c15408065021500a010820061400303401280003144080c2040c003903c6404009038007680d40a5080d45000d82141014003d60201242c0c1001d080b542482e090104c0c0c0026110f200707401e010a0040c8059540010310413190600600c0c400c03d450000b0f21420ba40d40d980c8460380700b4a80c1180d00154002240020b00181c680128000c0d50180407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 516759118 1250 516757868 516757889
    0x71802071e030207030c1d06040b010e060d150308070515070e041113030303090b0a020a05030f0a0e07150216081b010c0b090606120105191a12030c060709 68
    0x1040710540c03552030340301c0001c00c81c114410701c1004000034181504000041007405211a80e444d24114090b000305001048e00b80502c0c60f000c803502ca00ea0b480402c082060a087e641d05980b0b80c468100080600481041c41041e800385c48400020032050400070072003907015409441864040c0e440004080b941131301e0860002e800010130a4051070b041d4040c5d181c94422034a120b16085524040c1c0c3c1600e0195032042c1d0110341c1e540d04400c20b008070105495800000c0d400c00f14038241030710074083c2a502024220400c0c3d017251000040d0041c1c074a50000c0d0b4154a0320b4200c0e40c450740c3c0e5002035400078010340303401c0d0018010b001078081600d1700d011f12071050310407820281c04080c01c000001420080300c825214104200c4a00700404524800070303190040107990007402980c5051014020042200c14245820360314003410031140148051800c00c0d4120440780200d0301403500055110070501010a0320f92109203141032a107501c4c40000102047c01b840001d40c0c0503541c411a050360320b244a440303159083c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 516760368 1250 516759118 516759143
    0x90907150309140f0d080c0f030a02040909050105180106061e1e03020403030e0901230102030c1014060f0a030627053d0203040809030303070207180207 67
    0x80c00c40c4144030180c0210300d40018042d8268440201002001015039078030342043c010102d500005001c00300058410f42802017080c18004c9020103030b84907601c602c0f81174200200101c2c10140454041702c00410000005010a90141c2402d42c0200300a40c0c03107190f000030044030030b24142811302070002183c02a460300144281c074549110200c20a4079000001c100c0541004612180201d41078a49032003181d40040e01d55080d0700c1c0c0640705c02e51070540d0341d103d942100300410150f030f404c070801c6000c140c0440b1442c5182c903200d00180c1c6103014180300c4095501425101c2c4055104682c080103035140c038000608000d803502424061960030079840c1a030800d50108060022031700e1a045840f190352200090b003541802441c5001410406031801c0303a060300034a010060140b403000101007009809050b99091144004503100c80c10160401800995008000201400b4916081d034074521400b80544e5900e19010300000d445200501803080c40d141a94a12190f43c03106100341c8400c1944000c000380310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 516761618 1250 516760368 516760379
    0x406060210020c0102040f0e0403090f120813030c060309200d200603181b10110106030204020d150b070515190c03020a02100b18130f080301090b090907 67
    0x80d5004040c2c03d22950340030000000ca5800c4180c111000308404104842d040c1814540141801a07581c044010564420014400e602404d0212030100340c2c4240b60550780c4544500f81d0105400c264000f5103805014080050070b1605a04540c81c61032181049400d403400c64622281c4c810340c1643c0980d009400d03500c42e8000a44002c004040b0016101c001d0200a07000c034001a04580c81210001020300201d0010000071900300204036000d180401741401c0820780c540440c910f2820171601808100ca0088800d5401c07600394070400245030060002d6640b0541e1500e0200501070940443c005400c1c101d00c0060000c2c0c2903000d0390100740e40400980341c400a0101050107221004d046820205040105080c4014542c0b0401000c0305560f1000340c0c80d2140300b60701900f042503030b0051a0340c1504004e00208140e9401103040b8080d044038005507240d40b940c40707108012040c0138600030300c0c603c031100a04048c40b40140146040380c546c01002d000c83c02c0c0140c140314101200b601c021560790b00c41c8800303114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 516762868 1250 516761618 516761621
    0x611030d18050708100b01020c13050a0f02180a0e0705090603040c180f11090901091109060a030b15191101020c030d050f0a0203041e05030405040c0e01030b0406060210 74
    0x880c0741c02000d558005558584030a420003160790b200e000994450703a00040101d03004e00480c1841142400501252821480404d07001500e00040140d00c5550b240090f0309042c441e801050b510158000442d2144043e140a40c0b003804864070191040d240b014000850062540800c0c0c480c40880c0c0c0c0e06401e0103607038014003885400261048036030900c40d100201c3d1021031002080c3c804825400301284112072503640b0b40840d100710a80b440b03114410000b41e01913032a51407401d41180c040020000e17201c0c1401110f00e041c1d000d011082a400b00002a5444000741e06800c10341c0c080764100c0345a2004020010361115a105401407004507511440c146900c09001c1c04c1c00f9540c0f5030030200094a0a40110000390031030b0300950798468900d80d0f403000e201d4651100e115840d406889200308526504068480340142001c41d403601e540c0c0c41c020f104020070420140300359002044003500038080c1183d91040a0001064021003d00281c50304000d504140b810380140d404071401074010f06000300010803201d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 516764118 1250 516762868 516762881
    0x304140103110d02190e101116030807030207060201090f0b061503190506060a0e1915030e0f0a20040e0303070207050325140d05070b0408070611030d 66
    0x14140756452102181c20842d010003095280388807400180e4034080e40300c414400580c08900b08040007031002c600c10315900c5515064854021508000c0c1c3c92000c091552450503090007001004004a030310004100400000030b0034540744684c0035a00840c0e25034908038201c6d24101e10107440300d54440d02420124802ca10842c0d0031250107071401000c00700c0111100c03841d0380255030a0b00c3c403810004004010140502c45c0ea504420100d540c0d501c1c094800364010820390102c4641c920031030f28650400c0701c07818280185070040094981224140054510180040220644501d001d008051070202d64040c041040d5400c90b0b400b89096010004541c80001003000384039081ea000380d82d4001030550006c0400103180700b80749036030050034428200410703d0305182020081120580d0b07144403150500703c40316220010b49603140603035101c43e1502800100381400341c800c0034000d40640b080226042182400130000c0d41c2c0c1030f008560000d503481030110340d8001810000340b06a0414032001150490303941001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 516765368 1250 516764118 516764159
    0xe0702070b0a0203160c0512060c1806070f060c0e030a0218101e0f0611030d0c030b0904140c010518090709080f0102030718061d0307120506100e06030304 68
    0x2139081032800d4003c658503e6a60070240c1e844454048100410329140d9a0712102400c4200034000d13500f01492141c8060080000342c400364800c9100a201c039489000644411070b030001c066505841d490308011004000b002c80d600001141243d00342c116040c0010030141041d80684200540c1c4521600c1c8200402d01500c01d10241040100c00113003000c6170031a0024215845110071481440c10741900700504480d4014410b01141e002140714010012041c0c440500200401051000300304004030002c0c024150001c0e40411800140400c0c44020345101041c10352000464162040e1500159000d015180c0f00210a0907210312a0855081800d4040d8201d02d0780d041840e0219110960a410605e110262040c2c5a42c0803040113070031a80306911319000350704440020401410031000804015010040c1d40c0306100303003100c611aa803010040d0000506200010828a440c24904240c4400d4280c61207505448150303400304100812000c2c41d030190800070000d501d0a4585180d4031000c081c2c1e032012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 516766618 1250 516765368 516765373
    0x160314040b090c10110c030d0c15060b030a0b1302030c04170a020607031d0f01120203070908030c0703020103050609060f09041b060c15060509071b0206040e040302070e0702070b0a02 80
    0x1d00d81a8488000301a00d00d001500d405c0e1282d0103d0081910385444a281c80b0b11a901450034500c3e02500302602c490740f00c0c0c1011000c645405d081c4244806401d003a8054000400004200200000540d01c049800c250850311001000c3c0700c1c48044060380800d80308a60301d10350406c400c00140b0603604850100035a0802030300e52628190700025030507000440c0907400f080300ca00b10401840412819045003c0d41141e400e044001914002081020444801031a44c0ea0000201b20b2281c0200c00c180b00130102e150440341d5400401e50065103e02003403004a0201e414000402d0407894180301292103820042c042c0c4c185079000e0810070030441c3c03002d0000d0320004003150810203070610040d1050080d045588030300b11803000e1450a0b17814a5500c0c01108030030392074050140440d680d0007225941050503840c086550511243c02e401c0071080d0548001d510070300009000400030492550184503600036000d4500b440e50742c0160034040c007002c54104005070001d202c1032101540d54005400380c0c0000307104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 516767868 1250 516766618 516766633
    0x1030309150915050a201b0f040e0709060506040b09151201030506010f08031c02031806130b010b03010b03160c021c061d070909020607120503160314040b09 69
    0x380686181409030648002000001e521505c10340150038030b655104d0b52070114400040c0350813142c1d110503208291040e45400b010308440c43c3e641c1d116010089480c000c104000c00d20582d41c0e1140d46001074482c0010250800700006028030306201a501100e01c503207a8140381809840801800003401d4820380d507400030501944140d10280d01009010310310034801010254100304a5122001555100c2441c59100300004021020818281081e1080c00c0c0f40260300c94a41070840f048249110f4032843d9944207060400c207980050484c20904a802a292400d49036200c0000342010b12090241d241a49003c0000c02c075020003c50002000d9201071400e68800741240d030004004a2034000e2503d022068101c3c16001d0207036612801002d041c9221035108008900d6030b0440e225000391045800055840d00c084045d5102d540403108425880806094a10084030b8003400700d400c10f44006008811110440380e2142c042c1c07003042100103d00064080580e110f980307000d0010402005203055005507234 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 516769118 1250 516767868 516767879
    0x91503061c050a15090f02190503150f1008300712020d03021602060c0703060e03041404150918050d120506090408071b0b07120f0305010303091509 65
    0xc1154480700d10801c0903145051190a000d00c0541c911084013221901d00502c2030000f50850139075012065042d580d880e50403d010309440e0804410354003041e0903005850340d0006908101c1c4900d4460390280040110ad51102c14942c0c807000e001d4003401e8126032120007400781f62011095605481100d211307030031440568802c0080e04640040d1320895441c0c501c6460312401c40e4044c010074629103450318046003000e2070604d114090305071120010340030b98030006040c002079406000c40006190404070600900e42e410322a2580e0307038028403c908902c5980150302005180902445500700c01c1103090312482428444502c004080380070a544050250307a04080018005008194900c0c032030380c882d501c42d107a200e003409060700d500402052007100f200003040005807c0301d00b0368440742d4108030301d0b003002d44200c0742920003130703000d900310180384007020a240040100c2d501031004501080e541300401c0000445c42074040da00e080c0001400316000300710600188620581c800b41803605454450302007075844 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 516770368 1250 516769118 516769159
    0x2003070819020d08061e0f090115090902042709050609011e0e030307080c0c3a020c01030c05090a0b0c010501060f0219060b09090105180309150306 65
    0x1c1460800048003030400e009650301840300e000b02d8260303818a02e90502d860300004011084e95842c0d064948000c41100741d207070311502c03445002108050003c0c1100d50f102c5000c01e12040601c01102d001903651a4007113070b130020038003e85040340ca0a090041c82d800d1603810b048507031444040002040c80c0d49000e0710b0041081040001d0191102c6800010203d0b018082c941503044140720070080350b8200010342644500000072240c0c40403151074030549d280c071414012200da105420100556105140d06514031850442c103840c2c450340400207010091214010754808400d0250400015820810681c915940a50090741e0090198070b84145401c61000c005000c080f2540c014440c2d0101c00b207400322604600344540d030701400c440d003849000e501813035170029512046070500c9124840f80240c14810807503503801c08078100200401480840c5484c030181d90080c803003240c4034490502d54240880b8020400b208881d00c21002070814a20002e9540d04c1c40460740c00904515084482170f06000d6075282d26 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 516771618 1250 516770368 516770377
    0x304060804111020070602031623010203061008131113020d0605100338060403050307050d11120f0c0a081806120412030b1f17010620030708 62
    0xc54032a00d002e10030b1151404c010590041c401a1141d01c050800d108240c2c00200b501d003403030740420307140c804d941451400d91580c9450415010b508102425001d690a406401075440780034284c507411400000c0880c02c640e10803080d00d0311001c031500000440c0c04501960a40408854003404026807001201e1b6102c00300c1c0d1004c1002558255190f00a108902d064010100761034094602402980074051003e140915440130310401c01e114046180300c07560b120841a644a0001000c19803150f5581c02e00a46a5005200464050080b0103106200c01e008503c0c5000b403800410007040034a11161400c40d0300d6004007480b520201c028403031101da049007086002c2c2558420003e154a0b2240740c1d06030303540c00808a520500c80c0c030042c401c03241e00f00c2d00c450b901c07a8040d030002c3c01da803072180b00b00f1401c2d802403a0703013003015401c440341561b00c1c030889015a0002ca1480030540c1c4180d8104c040b404c0074180a1028050100025402c1c2c544038032400107800a0840141c901c0156481c0002c16580c40030260b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 516772868 1250 516771618 516771649
    0x311010b0a0f0311030d0512090c03030427050f0114010903050105090d021e0604152903120c03070b090f03040e0f010603150501030f020f0d05040b0612030406080411 73
    0x100440180f04110b400c201e401c801c400e0940c020440842e0300100509180100d0404010130200f140000700120010014003200240141c190b82e07503a40c07034540c2d07030340554900900a120350175038000180c2184a2441542d11076203a0001e0010241d003403640c0c1c0c0079000016410b171410803101d540c010001c06c900380714640c0907070b456100a160341400100040d0904055076004032284240700390300c43c08000041a4107500a034011082d908030490240e002e0000c16a901801d500011040036102003801c040e1081d84110f43e08604071407024100b5000c014091056802c0b40c0c625400a00c0b0090000c2c3d0005036070758000241d5000c2d40d0380035421400082c65134220394001c0d000760b0001c205104598a032640c801c2d001d00301da880c0a12044100d0300c2580e400c12030b00d101c0c181c1015901e0004a182151031390594641c1c1c030700149019600c46010035150013509054405440402c0a900403d24030b1920080894a0b1403100c405142031034078140301510b081000030019a00d0140c0f0f924101c4040c0e5030480a03090f03000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 516774118 1250 516772868 516772889
    0x50c01020c060a050702030a080115030e0f0d030e1218040207082205010806030a0308040c1806030c050303030f010b03040302031207120b121b04020405031c02060c040e040311010b0a 80
    0x5421444007081d04c402400d40d03411b6400800c041900141e0204089045d02c000301d03040c0101c440f101e08202e0040c00303118858100e601030110f401c44020404200c5e0090a101e42e9420300c204100f8443c801c0e156101c2c1c2050214500c001c1140ca00090900b1941079011180140018202151074403110102d030312601c0710884000c9040908201010542c48507070241000380381c4206940380c94408a59110302c079806c0a0240040100041c04008844035003202900301c08515001389200000c7c0c050150000b070100301ca0004041780c001c1607509000098a108034900c922410160f4a00440c10003564000703001502140000c111030074a0364051280c05010300010b07622412001d1702002c0c13131001c48074110411071040085190f80740000c3c41c0050300030a044105520401c2c58004100010300900c100d910068241c0101b0295403480302400c01c55942c1c05409400381d4280f079441c4090384010b07210b02d00444c081c190890000c01c0c0802d10842803192829200350000410720304010008141c040542c0c00802e016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 516775368 1250 516774118 516774121
    0x336121401090b01030b011401090308070606170f011116030c050f1506031c140d0b0d06150f0b0f03130f12091a07020f0a030c0f091b0c12050c01020c06 67
    0xb241c81c1b0fa0a41c0106002082d04e0142105000000c141d2000c501c0041e001c0350012500700244581640040001d250000010020840000d00c0716110030aa50700c045441d4601818800c821402c0c6041b100c15210741507003040001c0c426501540d0a000368a02500c0038840c0c44501c0400e044104030020704100300781d02a4803140b038540201403400d800840540d02100c01540741080c1150494001c0b1131014005034800c3d111078041c860f1a0051a40c058003503804000200d08001b480b24035130000742680c8040b5040a01e01d501d50409100c2c08940d4400d41c4009003040020f041680c0a10380a140c01c5086031040e18400d5615440c2c40c4641e649046058800b000e41d18600c04940f50080846030003008480314074402d520180202c91180e00a1420190050700c5405040b00c0c1d0780d071103480d40c001840e48410810ba0036600c0e0003003022510002d005642290f4a441c21090010010320f221003200c4078255641f19001545a40d405680d5135082c0c0f007402404010700140d030290f00280054000131440f0b00050515 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 516776618 1250 516775368 516775373
    0x14100203090136060f0f110c0c0d111302160c0e010504090803130c080a080d0c110a14010f23010b0c30070336121401090b0103 56
    0x2090102d10b6685000b95803200808420b042000f00b01403904080000f5804c451150001d0240010b0b0307002002a525010184040140480290001e031603440100c514802500041c040c81038050a000340050008186806d401c0c944500d1007090038541c1c0d0780250034611001d400d01c45940b209131049402c4441d1a605008005032281410b00406040320300303018250460729402001d210140101414000800050040c800d0400718a001001102c084884002081c10024a150454103807111542d00f401c0041d1030480c411752803032180781d101e44050080328034943e8a1030f0748510b041144032030039500c070b60340504486017a12482140c2d0300c40c403911401000407031203010200c50301600864205581880800001240041d8228a51100f0f80c2406601010170201c403680d00010312240d00300100c001030715400c02d58060601c550886000d00c1107200940c030030103c2030300008008107a84941100e84400c010326001064071703406560059901c40c4c81814500b26a90035529486801d50740c0c10b8101004004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 516777868 1250 516776618 516776651
    0x702040c03051303030b0609030d051206010c02090a0f0605150a020601080f0703030507240e010b01030506012c1206091b03070504050c09030d030f0e0f0a141002030901 74
    0x50340181031904000c0b6141c503000f41c0341c0103021110007904240d503030322001d441a11400300f181c102c860002c013102c1902103050801480d40d400502219000484803012984650007040d10100c6035900034640e102c0c1c0d0f62445d40440c005c00000ca40c0a0030a515580c0010350b07600c80b590807200c0c2007041000d2903520030340004007038904801039000c604103602c0b6520307a01600d42d01040d40f00560754580b400d16614140c905017a0080e07444161703c80f18041c0361a804109400701036010880d5040558002d008a189020042d02100c508640160108640f011034211604141c0d1007a0654005014a03200c0402e5050208524424003071110780e03654014000d1000a80c0204001040e604002e611b15202002b0070b400f003500c40649105a5001c3c90b125404a8a600c0a99068800001015048510700d00b407004000b070180143e2440d42800501c1e00131000c02104d000b14410b5126500100141941909a07075000c6203030070782282d8641a0300482c110003481d6541070009500990600d0008201c540300e0303041012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 516779118 1250 516777868 516777881
    0x20303090f07050a06080702030408060112150c140906071709010207080613082a0d0f17220b1303120903020c12010b060c16120206160c1a070204 64
    0x31495800b1000400055031001503450503102145070010b601e4403110403da24500607074004041a000d504004160030301c0d1502d61102060086945e419188048551142110210b282000000d0300030000e040381d50051100a01e041c00300a03281500d4140142c66000000c900c00816440c104030018140d9129a4100040c001414a80307002e8985410510303904000c2103504c40d0010504080403442360704a00c6c110101c1c046d46c8842d0b44000c50942c00103491a07456000c900700d2000480d6a441d070b0700314484d2150b02c0c00ea042c105907004105040d21815080000d060941400070540b0300f10540c40f90001e41d60b101800d0061600390f43c043e541c212646801f030718200030315110010340c502d40302002021030707800908000c4011003607490814180041981c03a0144c09100055500041e000803950078480002456110368a500060440c03011f0301c0d41d041101050f0340c0007020354044400d120902c80480c1d4100340422076407040c003000c0701c00c5941c1c080d4014004408034002509040c040744000541c2802d020b40f0703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 516780368 1250 516779118 516779143
    0x110a0b0d06080715120e070b04080303090f06060a05090402040b04020708180603060a0303083303010f060b030106080c041503050a051f0b0705011401090b03070812030a020f070606030302030309 85
    0x11301203242a00c40c001d042c48900350389004107648820918541801c02e000b00d00c09441101c5110355a01d488104403542d9900076507512100e40324001e80050a5000882c0e00ca00032200140a990040d11740304c200958440040c10a0b6445039455207030840e10381d1113100802031203115403211031b01d401d011b80480c1040d0f11010362080c001c0104204020641c2e80d00c0f90500e0903242c1c0360603c40042d4072250322091811080076805200011b9500540400d05590061072221407000c0b002070006504942521041d50110720408034414400e00052110b03a00480807541c2c020002402e0301c0c180b0360345540071502078110a00413008241c1e02e03000e110b0300c02d0580c007519505c1002c42e4030304080c4465405c00121030382194030031000c0208000c036041d400c000e000c1d041920380c003002c00d120101e1540c643e90090000d251a006d242e1191083c9440040c0b00b8402042034000c4090340242d09085039180d4410b000a9441035619804942080140b1400207a4038032510010390b0181c0c1c0110389034500b11a07118607102200861 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 516781618 1250 516780368 516780389
    0x1509030206093001050105040c110a030f0519122405040c11030c070503211206010e0603040f0303060b040807090213080f060405010614030604110a0b0d060807 70
    0x148096100c260450b40401c0d401c2d580d02d1041c800c0c00f015101c540c4920240f10103a1451142d0307401c40000c0540003241030314802c0b14200711801c001d80080e43c000300d40c10051200c0d41c121403100c02c046800364a46004d640b8240c20120714045148001c604103130f900d00300c45808203540c01c610125491a174800d814581d0640030002000c00b0002d101040d0300c01841c41010302c5076848035580a8224846c814030150013208900722521540c80351240c5849031110b0207443d010b481f4140c1c5407081203409072012140840801d41c514904100da07181010915001049181840040040002c4c0307511038800540c482c2d40075008800c460041e0345001400d90f04160300060086105120030b000b40c0d040840c4c074000300c4540030001603503400c194950702c0c038890255008421034096901840d5403500d0100d8818420717881180200181c0761509420300e00c5400c03500080e5015848040003a000501500c81c01148090087c02034140c0c1da9a003d044c0b115500c030450b4107411503251481080702500c10000c140150070950103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 516782868 1250 516781618 516781637
    0x204050105121f080f0c040c081605040515031b0a09050409021203130e070305040317091218130908120c091003050610030501030c051011031315 64
    0xc040e40111000d050349a82c4040c04240b0069070300c5180003000300c07034040d0100345a6a8180807500c5600500f403946590085218a0302145454410a03001c8461030f20f0301c4d049920b400460241c141400c0b00c3c0181031101c100300c042034955400400d0701c0720f9500015450b680e17103081e6007024150106420041608482413003102c0300160003090304030940f002907c0000c0c0c5405540000354200c2d0000c02c60b044180000582880180d4200d007042042d02c088003c0d042a68607240c004a044920455001e800a1290b6021040c018107450607550005048030840d508002c8000d81c1484aa01101400c2c3e030401d102440e152841c03d0141000d0018910400104803d1b40e080d11059044e02c181d80c2d1407030319102c41000103400c50104605641c5c1c031000181c201d0383c1e0b1009004028000340400d640e6144a11080440c0300000ca01c00c1c010301d4162903200914110182c60001408148401c8142c0003003400b00ba0b0036031070008001007015010042004200181c1d59190484000c5142a5407a641003007144012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 516784118 1250 516782868 516782879
    0x8031c1d030d0c0e15040e01060c11060309010b030105010e0702070605070c060813060c03021b030910120b0d0f03110313060c11100806090a0603171e0301080a12030204 74
    0x541d00c04901c2c03140e0202ea100041c06080324070385000145039034444c1c0441d190043d03400030107028000b500c1914001e00c4660b40c0340c030300035074881c949040001c20360855880c000d102414210003541e001802c420000c294400d03418000b27800c1d124242c0110484561040802c1100c0b40d040241000408250520307502c2c0c01107945451241500a0044105008109010960842d0303c01c40d0b50100c0703900b00c0d20810659101d6100103003e0341c803c2189a40d0740c14080e43c803140c41d0402104030b507140c0703000600324001d42e8012902a80c403180010001103030a5a165103502007900d83c1041e403848184101c440788002c03203080ca8090505251180840d5076513000340000d61144501e101100180e070766906118070052541d141c1614482c0b0080d07059900710b03170010424800d09801412941c0900c100322445059590b40302182000c03500184809024002003415121010500c480244010000284c801d1192110b00030314407155402a4440c02c01a84000081428001458050043c1f5005032800394602840c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 516785368 1250 516784118 516784123
    0x103090b011a070818030106170a030807030b06070510050f061014040b0d02070c0e07020a02040504020a150c03020f060f0601030c091802070501050a02042d08031c1d 73
    0x500601c05011042d003100384400e015030041d2411039500000c000d41d140c80b254841007a07030b007030f400a41d0702a60030716101042c41410b000c01c07040074404c0780c0700900030441d05d618100d80b503950140c2060249943c0d10812585600d644004001d540d00a40082498030502000c6001312200209114140e4150f08240405030344e404100850013902c5151514494145409040091085600018507613100042d95960f022243c0c0140c546540038440c0d12650a0303449083c4022507a0440d20800143c0000c03003110011f14140d4042030b00540040c1800b01e881c2d0b01d950001c0f62001ba00303140c00d404540c254011008156040103946198141030014001ca070600c0300e00304c50048005000141815140c1d43c1004143c2e110b130700107600602d000390810101e100d540b982d50000f03600c00e078401d607540d50a107000100d8a58490089608841d040951540960f810103051240c400f9000400641000c51160010f1000d89c1003020304040da81c0d44078802c0400d4420408441114100da4100ca040007025049202c00c8801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 516786618 1250 516785368 516785371
    0x309030813020f01050d0b090103060c081312030f02041527060804060f09120e100302040e0a0c09080709060509070c1205090109030b0901050a0b09010b0d020a1209060506010306050103090b 83
    0x85c02c015803074000c4002100c000e460b441c03030441d41105140000005004036500840304003949030301c41003032648072018100c2485d0b0210b00d0240c4440703410b03131400400c60b1195104810390150b041d401170a040d2600310000907601c4005000d0b001a40b0b03c0039801c503480e1120361000c08050180d015282d62450600050481c01000340050086540c549030807610f040c19400400f01c41d58007401c2c03c4802e0322a0840940340c1e9284900540c001ca42072904203c2c1980240300321025a8050f01c1e840d074aa40c2d0780d4111a01402101810700104010b500380000c40102c00c006100c0904840000451100e0400c011320544c1c0360020b103003030100a200044100410b41d070901c01d040c1c9051a2a03d103903510407000041c1c1d092101940000c141c040b040d0104001241e041d403021340200c00300c070070a003c58440e24081003a4600280079007801a06d0801180e801055a94000c0c4222112424903404151035101d900e0101c031049041910b40307a40f54000c01282d5030b81840382e0005000d003402d08001003182500c0703e00d02d4180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 516787868 1250 516786618 516786649
    0xf051504061202030a02040510030e0c0f01080f0405070e0a2003130f080f040b0306030c090f0a02181e040f02040f0b03130204180606081f1a030d030903081302 70
    0x9000012172201503907074040314041e0001402c10821580b444074010024559103825802138020403c0c15803151a11004c4101c02d440141d45d102c825413100d8400307800210019004071440e10a02800056880d0701d010580d1148801000c00070701100d4120034540600c01205440c40c0500c000c00420030440004200c0c070f944d083d044404a14136400915050f41c03284201e105d50404020b003c100004e854070707240000d40c450801907007070f1884d143c4007401340190031105850000308080403034009051140c41d40d02616500c100b2340080c861014000300465003038121141240000030f0f488000082c94200750040c0d1140740c141d80d0086242516041b040e5480c01a540102282ca401c0003020540310054841c50070003036174004008109515100d00c14140c40b08481c00b040b41c8050600702d0010310060701264440c4400001440154040e801107403e000801e126a500c810b80d40d54107681082ca51810451810003855603100010449083e09010301234850052210300803440c20f918120050b1941403818181c0c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 516789118 1250 516787868 516787871
    0x105181f0906140f131a101721030403090608151c03020d080106200c03070b07140c01120902180c04180504120320030f01050a0b0c060612030f040f0515040612 70
    0x3141c0d507c0400342d404403071340069103100602034035002e90800030580c0e0300d4402660712260305801e0f0040070400540401c44028020500524080040a0044542c2688401e000c4102c4007003984101c0005c00d0310051481c0420b075480b6282000b000c050b0108000003405c222030500364590762601340c0041540701d07484205062060482403108007600d0820011022450050a43e840300e43c81c1e070504074554000842c00d5640400a400c0a4600e80b008110039002c03001c1a90345194011001052101030b256650049800102a13071390902c1c190340a5200031b01401c2140c010560755403400301c10120070756034545040c018504c2c09080c403001442c14803520200315035070708000c50b510400c40840f0702c548948042c440324181c4000304200e0060301549495042e070b84125404502c06803a51920002d07402850149420383d40a1400b00b400e510700500320f210442e400342e007106d103842a030070100c5116800580c442102c6400c140014812803034410400c1031828180c500b00340c00c0c607144c0314005105041203800307100c905 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 516790368 1250 516789118 516789121
    0x1305010e06070b090a0221030a080408070b0702010504060615050706150f090c091a0d0506030304090c030e1905030d0c1e110105181f0906140f131a 65
    0x2a25a01c040d511140e0704071210740140d02d4542c00e90b58440c1a1400d00303c0c821010310040d454101d0170780100a141e43c0900b030040d070400402c4d80c019a41c001e4050415109590203020510003c2c804452843c841c1c041d650001c40c1c60b0030b143c41c0031400e41e40a80c000300c441e2140d5440c900f2405030f0013415a4034003030b04564081100d440c92030401010b10203030740220044c12014000821006d0703151700f1944c41407480d5a0b84a074515a41c0b800b181c8131070306a410b4370b41140420010b00d2201c0c02c181d00100d4021400070266490955104808803c8172206184400400d0300c8a80300c48a0340002c3c40720450300c0388100f108200b4001281d44603512803050035200317184d40d40c0c1c608034130150a20944288020618800b4100000c0b20280c00180520603902c008448035070901e00010300000c413400c15162070700059401000450035440e00043c0540341103400200e2960399550307540c08034a0343c0c05000780d43c84025034040302504210b040924040c07402056407109106441c1140c0c0000c0c002440454043c0c0f40030315100c0603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 516791618 1250 516790368 516790397
    0xb03091005040c090606170906070c060b030c0907170a1112100e0a0203041202070501020309040b0112020f03040b090c13090302190809131e050403050d02070b070e010302130501 78
    0xc031030181c00c90b0340f201d41760a9000c01c203203401204100140c0b802d0046034840303985540071103039505000c841401c0058800100710b0001400c0da0403c00d000c03440101130743d410011080104802c1b8a0442e0301d1800902604846500308460080140d080034411030306200702e07a10710b2040030081c498090502e0100500d200041c500030048a882d001504500142c8203042c1003c48110010b50006d0b0780c156404044500383c259114000a0000203d4038181c01035400d1010300b1042000400d80302c0750041c180060260014484020780c0300030110203d4290301c5684070f0030300d42828000710300020489003695100044001003aa0350380503011481031130540201341c0860f54a0106d040c540b4485401014540383c144080410000c840a005403141c203a07120007454601ea16600e05991500d21031360308840c0480552061025560446a4400c5c02070601502c2c001d5084058800c0360310418081d10f10186400601003203039407210329165090000d1a0a50800c2904981140440c82c1803198605114600d10403094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 516792868 1250 516791618 516791633
    0x8030402010c020d050601030b040b15030c04020a0e060c030703032d0f091406060103180209041103010e0a05030301050a050618040b120f01140601080f071101060302040903050706060b0309100504 86
    0x4c91a5000d0700f03585032569a45072040401d40301343c1d400c50b03130100c03c0000a085000120783c500c0300860b00034028855002001c003800001c0d400703540b01c0000c000904250450b55102d600c010300c841c03442c61000716600d2140381001012650300c81c0b460981081400003e10842c0ca06508030030221640740c200240c6420408004401000c00c1c1c48000c00c1503e17030703080e114007000010175064840c0d0f4081c0c0f818003040c040001801b00b02062504000e51110880c000700340840c00203c89a13054078000303000010480d0070360b607450307140203034112045401d135200000500090402c164000020407054400a04040243ca21212202808410350f4092641c859840c8125a174000f03540400101e0780041d140c0c40404c5907540e901070000d40c0c034544601035001012035002d501c220161449120300c41c0d40d01e18651500f001c121521307100400300400c0c40d0b4850b40f02101690311403090300c8080303100340c4071a5075500c1c0528008081d168180e1181102d10018420050701000100d4202c1d0351251301e0000146581d0703149000303039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 516794118 1250 516792868 516792889
    0x1005060403061113180b0306010602120c0a0f0804031101021b010c0606050a08030903010513030e09070507060510210b06010c0f0b0a0204031b1406030a090b0a240308030402010c02 79
    0x100a6075038030f00d00117115840510840c90101e9020380a001450b4490103050b40c601c020300c2002c0041e40490000740c150038a00c4060009800100c080e65005005c903140c2c1c3d5001c0d8a001d40a495807034000804200700320415181d1649a6000c1c000350078640440444005030a0090170068180308800025a0130021594401c2d405403800420000d01c0130f44480d1015525040700c04218000d610346070100d443e0142d10516010056815510103030a200c0300c0040c010400400742440080c0711013405070f000000d500e40904c5100d069861904003050303140100001082c1d0b001c180c5000080240c00400004c42d07101340005610400a0811521a030080d02e03003440f04140b4100094800210601441504041d580052040f03c0c012105c8d001c060041c50540040302006120314049449603c05038240d44c2460005140c1c45558401c001540d204d281c0c03602950541700b140e890b02010354400544038a4072904110030703030729001011010141420f650760a629803002030000b81c180006980424119640c034000c58 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 516795368 1250 516794118 516794137
    0x60f02011b090503010b010509060327030307020d08010b0307080412050c10060f1a03071202070605041a091209210304030f022d090c0c01110903010510050604030611 73
    0x14048103580501c001c0254116029180c4a5401c0402d05006503200380242c60070a0001040203155807114903903007444451003402d4030420044141559000c0f003051003d075205805a0b0090000c05240420040c180e110580000350308450503c1446040755001c10050340c0245c3c0302100c070020001e21801034800d4090f202c00c0c0141c43c4181ca0710220541c0b801d4200b07000700c6843c1c01000c926a03881d80d098881021200420303012100e405d000080d1154410441c160b1219000c2c800185004410b48854040e80c0c41140d040c1ea110b410641c0c1c03c1c010b2a500c030956603104910030040c140305485c00da0410030f18490342c001c540c880c0590140403024002184007154242c00001c080b81d68503580d0745001c90300c0400c42c0c0b006034440c142d107000104d03c551580c150709500b10a000740600081e11204100a000c02000d80520030b8850203104500b00703d40d0074421106000704e900392443e116400c0500701400d4401c01080c4d1601d04050700310400858481030192000d40364040d030040742c0108420387c800e007035000b1548030303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 516796618 1250 516795368 516795401
    0x615170411030304180c0207121101031e021206090712050c0412050607030e070e01051309120e0310060e0c0304080708120106030b0102010b090109110c030307020f07080106050307060f0201 83
    0x2a24801d01c8400314180311a42c1c1c05001103a2410306c00e984034800c030b03c61840c08241f100500f0000440704100704420100504001581500480320001e0740b1041741821001d16500091100030800e00b02149540041d04540c619403e10b0490307001040541c14003400800700f03460b1004a04403c00400a56028010040e03843c909221103041c000d0382c400701a00e881e404a4500007040801c020042010b000b525803c5000403900c0e40791509000742c280d003c200c0c040f0502d0b41c07041000005201c04415400c00c1203543d903030751404009413040608000d0045c4080c00601e18100c0300700718000d143d114007a806070040405d00c3c1c507030356141041c25503441000c00c000c10340003000031490174007646058802e0507110103580402c0052607042c016401c03154401c00032940010110010004100b4540280c8860000100300c80c0c01d201944241a10390b400554034240541c0240c00b644040b8101000b0500013042050300a0018a00e8000403a48800b441e00400c410002015000c20115001b5040502c2c0340869085 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 516797868 1250 516796618 516796627
    0x2010806101e140c06040c0812030c0a052106100c0519050a0c0e041e03140c0a02061201031b060903021504120c0501020d0f0212070f0c0303110106151704110303 71
    0x6044e0b8498800f1181107030b40030031080d008100e002001800710010070708014101d1840e12990341e0409541c10104002042100400814800054010382e1000001c04100c0c0d100c41414540301304040014607801c107004000b18424080d0128038001001d0800c3c13000b503e84081c0c07034070107402c3c07031403e1501c2001e015200603081100003d1b02d80424030709510a43c0100e440e01394440d903002f02c04813510310002001e40000c404802500102e1040c5d4001c10810300d90004032078024210b03038042950f5800000325401c80d644000010001d0000305980040b82c10725882c0140b00703560414102410701d540e40e010207400388594100e5140c0603003803603080318060706c410070300a070210310146800000c1c1035141c010340340140604020b40c260180580300b03443c01261950040e1400c2c2b154080320000e19000640140caa50f60f03030200180c0420240301d904070181d4003d544a1200324043ca08039400e556041d071140c030040e0030140100042035403120b45144405c400746070140306620780c0c2c101003400c880c031050440d034103010006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 516799118 1250 516797868 516797887
    0x10309020604170d080c0702100e1207051002070b0f030402040920120c010c082a070f1409070815040516031a0102150901020d090f02010806101e14 65
    0x540f4031201803005007100d00d481402441144c00300c2056404041c0d144003442240014500062a1614180b19183c4010541500c0c400a5400300d894020002c407504040070078415400c14003030032840305c480c500050030900e00e0806200018401c503001d00444200201c04201190f5070f0b40c01040000350007800d9130b844041c501000c0c080015010444601c130b070003011403050900300c001c81c960715407034416102d94469003419110300722150301c0004695000448010b144003424043c20b61040c42041210050605030f041c000d0310254007031076400c1018070b40a00c83d415190f659030810103a078042c001c2d14101030749445003829100d5a081d440d0f0311551281c1400c04110b0b10104070020a5101009560b003400072208007a241c101c034a000e15242030068004412403080e42c0300d04030405070002c413003000042c90403a80c075030754404407908401d049074603241000c0c1c03c0b0305660f4031030600340d00480d04480b01100c40000c2c040145c0741074511a07020305e9002d074104607181164081e101f00f4090990b110010b6940c0c14010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 516800368 1250 516799118 516799139
    0x10e010b030901061a12070804170901051605060603070603020424030902030a060c090b040509060f13140117032a03040905010e25020d0309020406180501180905070311010309020604 80
    0x81c1c6c06898111210001d00e00c144255030303003030080ba000000a0f844211012a00900350300c50044a414000200305a0380c1d40d08a5408d070660b09801000542441d081c400201420080c0540c8070008160043c4030070302584075010721848001c19200075141c90b0110000d0f096003e00001ca1006e945401400a0b540c00d000e210340044a164546030b50384100700d070700c1e500341c01543d00450107942e402c00e000e034000070741724203240b404207540c3d0b50000d00915100c80064010b0084d1080010751824558906004000c4200c0d6003020b10f14044c0488051410441000e0740c02403000c3c1d24500b401c0442d00341155141e070b810b0083c4100c9029100c0e48400344219a110001c54100040582d0240800710703c1ca036900310043d400b40c44070340146449034081d01e02c10421005c21005800600d400341d90090391050005843e114040d412041c002d85403002150a40c948a03816401ca922039042c0ca00440c241460313940011000b145050541e9800003801348401002d00c0101d0050098440007500070900003000b00342c60400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 516801618 1250 516800368 516800377
    0x8090103230a05070818061308091518040615200709090c05010801060f210f09060507030c02120c10050702030c060c0f19170c0705070806010e010b030901061a 70
    0x717494441c115100c1d40b0300a900c0c000803458280746034100001040303002030341c001e4a0100707034082d502c910300380002100052001600807080c0a0442400a482404920701c0380402000780c80c1158100a03807490600d841c40300c403095071035440c20480b9000c003102d03a9000035855900903441c80d6080720714598072901e504000307044002d029503140d404000c0c005915807246040318140d40466075038040b18015210156604030703d01c00c404140e14410729409541443c00d201d01c85511144920200b02a04d0700d013400e00803120090708070700405040260703199019070000f07564102d018091008a556411b050f0920307062100c0c1080090b145820541402a000d90000c040d04008c15184195581c5450b1500c4c00340e524401d0f03042c4104080014000c106001d00a00341d98007000c01e013805e03d00c20241112102011003002269003803111340003c98200207110040095402a000040045c01194144406400902e40510903030600c8000000003400901003900050002c103c181d441c640062002c01441009801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 516802868 1250 516801618 516801631
    0x9060a12051e0117030406053406050604090c141c03180e10030204090602070f081306030216141c030903030b0405060a0b031b0301030602030f0702030708090103230a05 74
    0x107001e0010582d807031130b5203101c3c06200030400294606807a140c3d0554041e0000c0c61f1424400c000382c820007218071340303103160145106010181500440560701d0b0040c120f403c00390505001c2d502d847c0038030000130031942c5110155444814962140d40c13a00c4005411006250001c0e0001c0c900102500308058000c050360310000000708002685944501042140d03500c22181d030ad110600f4900108050b0415500c42d107004e070701401d0003604d07000641c0c5821617401000101180d11043c0003406404e00c040342000280907100754a019072810010010070136410400120107459640366003016440d07450100215a031040c03042822440d00c00c48180040d00420014100780c022909100c0c22400b0313407a10b84205072040348024040d1100c070b420440c00800540008040f032103c0f0303481d17a80d101d40e04d1510b400594000c51140f01d0140c1d5900d08030320308101e0a20040d001600b954010b1000e2000108a50b003528519582807034009141c901d5034290a8603c0c0310500805070454022084c071805881701d0708114801c95 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 516804118 1250 516802868 516802921
    0x6061502150709030836040609181403310e0603061311060417070b04030308010909110603040f030f051921140906070c020609060a1205 60
    0x286102400d00294008a0742d2078000740001d0b005000040e20791000d0a085080992004840c050719404c406010350a1602c4805200003151241d441d0701d81400b805029001601c0c0602c5031207001c481a046007021a24001c080c0240480706048040080050303554001404200c400c030702040c1c0980c104c140f0b10703481e1010003000001c04041035000700b00c0103040c06814041c0040c00181e8820042204450400a00325440c6009403c1e490f8599965000b403c058011250031401c03501d04011458500890ba50050440034018041080406d400c14042411512848004035034002d6a24001c3d030703000816151154484404000e10003441843c0c418451014400d4603400c1590100c018150382074020500c1610100c010041100340c454401c0500c1c04121a00040c09001d103203e40321060705550400102005082e07201007042907211007080000d81003a10342c00d100b400c0320b5603500440e103d80314444015000d03040002c1e01045685c07182e00313140b1080309101b8040280f403c080116a030680404006c400125 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 516805368 1250 516804118 516804133
    0x9090f0406200712120507020304090e060709061413090504050c0307270e03121b0a17040f0b010801060611031305042c0105061c03090515040306061502 67
    0x2407103880a11858a82c1ca5219541030800581e1045014400880390500b000000160820465001d00035180501c0b07071500910388460808060804407001c000308900301c0e512034001d001501c2c0e00300d15581c017910032524040010380054550f21500b80304801c170345c19400700d1030040018041c0b070a0f072000d0300580c4500295665142c4c00410182d6807201402038203400309240e41465081c9603420445885070402a1001c0754000c03031010301d5415a080603000190000c6010100820008210000f0707151528450006040030b400c40e070010401e058850f02d03000705400c003501280074486058251b015065014101c2c40d550341c1c550b500c82c1e000c0c6c18a03110b100c0116203d18210540706501005441013503c120114502ca1850300013040080e00101801910340d100403200c2c01c10040b20b200284501d17034034550000c00c00303082c00814403290b1404c04048585c2c001c404800100001da10ac4000001c4031801c0702d0030ba0344000070b0f80d0910b415108aa0000b840241b81540c001424000c17040c03000640d00e6076401741e03400c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 516806618 1250 516805368 516805391
    0x2404030932010c0b070e120a0b0601080f010b030118021909060e060f030a0902010c1b1509180509070f030c0806100f0b0f0f0a1707021c0c020609090f0406 68
    0x3c062442c4000c041240a0700050081c900c101d4114a05200041400c800301c00400c0c001030400c1034500060310036911400c10080303956080051107402456040d1150f8103036160039403103481da000601031071200070b0300c0740c00c021080b50081e0160b506c04c20340d03040385202c0d00c48801c81c060200f405510034800030035012139840940d131070450143c4828451020381c0d0b9145542c0d0f42d400d0402003a440758203e061060f82140341c00030481801e07502e42c41c412004107944000b820181640043c0341494440800c104203034405000c00030b0070001044158040140205d00740c0c0ba2074603480d0030106140c0140e00303e0f28142d90000140b02000d0b101300112182c4009480b800d4640e080140000320351802000c11452a80a007080342111100003000030840515080b07013042c05810f0804000d500c03442c05c1d90000f4024148001050000250840c1c01c0551400100f500c6000036089051000265620f0000d021300814220259260070048421400b80108040e0407460b1500249002d06000d4070143c50440c940350b07a4000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 516807868 1250 516806618 516806627
    0x212061902090109060318050d0810210f0f17070b060406050d080a030b090f0702060a1a010f09050901080312010f12020d03200f0c0102240403093201 66
    0x2d1016069407440d0450303040c080d01350050000010041441c02035855000085081400080c528010595403d00e00341406c040380c1e4a039510b01e400c946c544856074a8107450a070b00c401c0f4104101a0300c2245035120b9111414008bd43c00c0002d100901444452002110303180d80302c000038403980748101c545504548844050000b1203550f400340d2038001c0c0600a01401003502c02d4080c1507201038910300440d02e0300d881d4001c00c094640594284501e001140188484543c061204c3c42d406100c40000300000300c0303407105404081940b41011785c1404008610160400c0c82640b01c58085d00000d0400c2c0e2607940d40d41e0900b40d4030780c862081d40f252828200000703e420b2441c1301c414011110745410840d076841064007006441d010a800c200d0511070070705861240280b6064405c040044480c0c003901e81c5000c42c5c03556a0030324050a00c214115001250705110503100c584e00d80e1641c007041000c0911940e1a4a0150740500c0190000048920918005d800780101c123401c000103e07000c06410031818a641e0300644 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 516809118 1250 516807868 516807877
    0xe030706140f0f0c10090213021c200313060506010507030210050604020705010e01061815170f2a01080f060427050a02040e030403020105120604090212061902 70
    0x403401082290a0b00c88801e1000383c5440080702031804c1c034141e1080e12251520305180280500355441d004c03070806515080601107403981c01d00d101036180121203182c404030382c02c0400792550030759541d40d000c01e59800f0400c1d030403402041441c02c680e40ca04104542c481401c00c05402103881e01e0030b00c00080d103c0d5126005880d100350b4142c00810101e11070721600c0028080003884c10350416030034003810011a609001d0503940b048003100010307a02d81809880d43c40745400c81c448220050601e00c0c80e5820310810b8400004840308030b003410140c9520303880c2d0790303080000804041000344107100040600c080e40307104911810f0b800e081044003440500c801555081c5080769100140c0e2490800203001d410140c011a1108148a14499104250400c042c442c014012000e07131b4641e000c0106601141000d00c14503a003075121400071414645168002032652240e135000c880801d90003c00704c3c0068a59402c90404150b0040003122102e44540103103941e41000c80b02102030001e420094010701c45507100700c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 516810368 1250 516809118 516809147
    0x3020c0c010903030f1115160806150a0c11151305010c0804050d110a15030f0e0712141f1505031b01050d02030a09141612020f030d0e030706 62
    0x1704440c0b4040b04007a2459011000068824060001c00a0045040568861084100d0070801c50000c3c0d401200600b5140d000b400180100d03040600d07080c0000c009005e407051a1200d00d40a1080c018602d010303050100040003283c3c12480c4240304a90030143d08010b00324034503660303030381c0079103180d40790011540420340c80e00c0903041e004100010701550405441102d0118000c400320070410000034045600c6403060713803240d6080d0282c02d038030503642039046c01072030020348084c84140407100ca24000c1e562514654400c83c84820791032400d0008114542c0481130300400018280c07003440304910800c89020410070f03600152249081988219080c01c50984025101c024008088940382c0d080200b142402c3d51412a06000050002c601091298002940f00b07001c0f200d000709007542d05251461001c50700c030007444c00c80d40103803d654a62803c070120207400c90f11032201781c0141c0d03c0c1c9070004c56440542a42c65a030540645981408012b4001303184c1c125075002581280e40f180d54034802220301c54500d041c007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 516811618 1250 516810368 516810377
    0x70302102c030313110d0b070201020409150807380403032c0405071209060b03150c0901050702150705012007021c05070f17061006050706090309051003020c0c01090303 74
    0x40c0001310b013104030740307141c580400350000451b650340c0e0700c0301c0b03149000485150380182c0d0006028072420350300c0d00400004141000700031440701e003030540d150f0f12800c4500800f00610711003001001820202a5052503400780f204508940d050800c0760300386158800d02080e4081642c40000501ca80c1025a0100701e00e00440240281c1e038441000b000090b203806801801004520030302071100c0c4403617114855040c0e01c0303410001000e8070204141418a40004076404c0600c090748100000303070405404a44c0d84400c2441c1060b9115003078800180640864808001107440104540003003001c15400040400013860b902c841d1505c50343c2c00d2808505c41c0c014000c0d00030303228400c0d520201100034070211080d8456000e0715101629061a9107000040343c0c044003010206c083c804c07140070014800c1c2c07908090301400090310795040c510b001e400c80c4100032004100e43e6490000390145807107042c901c1c016000c0100188441c810000c0002d0281d0004180030703006001c0d103006040e45602840c41d5400303d82c1e01d0b889 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 516812868 1250 516811618 516811651
    0x15060a0305060102070f08070e060306060d060b010215040b071416061a0904030807030c080601090501080405100e0a03093c08071503230c070302102c0303 68
    0x4502401c0041d18890540c4280c0c000801c1407001d0700850310260031068010b0400600d048070075030104d5000750806001c0d40007502030140741c1c2c5a115004a000f0382210010460014420040345001d19494144c1003107030b4000240420082c00d002103a0050f1040d640350040d80d0030f2041d03024124840c0c60446000f8481b05003002002800942214808028240a00c0245110312000c0381030820115011800946a4130400c4902ca0b058410380e0130220b40d40c0f40100c0e0310b103003110010f0321607031150087c141406119030000d410840e08100c00315917848102020300050384101700584c3d450300d030148114003140c0343c00741c04110710101c5101740e24070244099040085041c01200d500c1c203001c0b04c440e1828503590128020070b000b4010801000280100507000b09124100c040080460300c0403d00484005500340b880865044036418a0360400214103039907035160201e1a05030300e051a0140c03203850b0076091001301d80f04c02402a8509002c0c030740025100310420132403003c90b9200e20040b143c114994030f8820 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 516814118 1250 516812868 516812887
    0x51605030303160e060703030b15030402030c0103020f190801060f021b040504031404080303010608060906090604180b1609060516030f0306090207060e010c0201020f0711030c1207030b1506 83
    0x3804040043c41428404d10380184036011902c103900100e001d402094540c804100d460410343e004c030080e00f118100460031742c1000e500080c1c6440302c02c01c889040540200d10600b20116890894071030318441d098802c074900003a44046d01080c424400c85010420f18082808407a00108007250308507244890740c0400340f0343d481044014640a4001d600300488440c020711b0b0f10f10210010800350034200300443d269854208000c09888000b01114000e00b41d9605010079600e0ba01c180a4004030122004210304510402020f8804540e04001e041c0740038003014404045034454416102d0300c295912401140c1e124403040c1c0e0207105070040d21058044d07d00c40480868855200a04803100901c1c1c027155860355400003209036000380005076405691107540c4003007004240b0031001030f4039003030000394140600700c000d0f02003c2c024400003405400c074078403240312181d40c240800510540018420380400d47c401303d4466458290703001c2203e42c090a50003040e2486a03000c0e006202a8004050b5480d111201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 516815368 1250 516814118 516814141
    0xa06090e2104050a0e0a0b041406130f0603030903050105071b0b060103093002340302030105040302060f100e01090c2102091309020f0d210309051605030303 69
    0x140c01d041880c10090201046654542d0308640040040c40520015800c0107030b020012102e4411045204501d4540e604500301c5440e090380c0e900540482e0040e01000d0314007521006400d24983c03580805251440100406070080c00340410759001c1c0000300901d0f41c5000d400c1d02e11192a041004810250071801c10010ba5502c00e0240e0040042c900072841c07450036650700780103040c0d01b0002c0301845505400000d4582c00921803080901c0300d440105084c500a40070010342e1003050205c41c412105000d0103c415498000708407004644c0038000300014a041e040c02925240b0a5840c00343d6090240041881c4070ba9a85288003501d400720b0342c00441c1c0c1d181c02040001442081c2d85c80c8148141c0c01c22002e100d01079a480b03004040390100d0051b90f1003ca010412510301070310700d20014510310f8401c00e0300158540c0c04060740050010303150844c400300e0a003003421070b180d14000b10011030302c0b142c4501c40760035916402070841d10348990126046100e203805004652580c50040c0c03901a07000b400018541d0505 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 516816618 1250 516815368 516815413
    0x30606030705220302190b03130f08030f010513050c0a0c060906090c06030c03061202150c07090209041d0604020f12030d09050c0316060e130f050a06090e 68
    0x50782440c0e840e24100c00c460081e08807040c41683c0410300d0542d070400550a00516050404600c426044815030904031302d1041408040d00f41a880070754140c43e0000c0008142ca0030320038a40003080182c983c03400c0010380300045824040c0501808000602100180590060701d02581c0244491400c00c4008041103841411003c801d070760b81074a6035400008200c143c814000c91a0007030b16841101800d005000e000c2d500c120480e001014a081001c00c5840902e018145c2010381c111841d070740303000d109501441ca501580160740701c81d0003084000182402c1e9035008000c808402d03242844402c01c50303c0e0401d081205200f4800040e0846e20010b030062400c02a030b116040d0700244408e414803c002c1d100c0d40f542d0460141741d207055907168000014040d00b04a00024141c0c00c40c010420040c0c0241400b203412803512801c414000240802001a541e006184010305011841000f192900080310b07400380806889409155140403c0030400100754000d19100c400c044000f080308182c24490054008030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 516817868 1250 516816618 516816631
    0x20c0a3017180603040b06032419020f030106020f0d08090d030e010f1e0f050412050703030b0405091507030209011d0f0306100602010b090412120f02130f050a080303060603 76
    0x1d5951182c00d9915080074500440c01214800b001c1e24021060520385140c5000318105803000c044c03072128410020344c8056210480011002006100c41d1950010b801010030f1860000710210011988030303400a22046100d0003001114580070f0802000d807010401910441445d801c01b062029425000390455996540f00000001d007003884070700e01c030b0211182003080281054081c0340c00300c80e4213024020b40b064a4000f0f80c01308400d0a140c0d85a240601d03034003280c0b006102c400b080d1a810700d4000d0340040ba50140152040c8840e20f803000c0700d5503d032a07480840d05030910780840400c000c14464402c0d86d2030110180c40c0c002d00d22052410006540c0420311245038000200c5400300c5064805110180c06403200b54941c030f400078203105000c0d094a00900246000c2c40340b007400c00c40400e8031a0000c042000880c10702444545c51000d598001d040d42200c0d1a002a000040d5104403030101c0c10800111011030104542540e190720801803414151b00c81e00030b00b68024400f2130000e15003c00215000705 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 516819118 1250 516817868 516817897
    0x304030e03010612060608060708060907051612020609010c0906050c0a020a090506030f0a08070201052206181202030709050613060b040905010504020702010f0e01020c0a3017 77
    0x990500000b829210550849444048181d201000b000304601031000544060809000340e49820a801000f06200429103841030072001f002c00d061501600403140c51920a0700d45265156403130a0001e54240d8092441c0b00620a480014802c0d1806115444000c080c40d40d61848071490504111040e81013012040710380e00401c40704c4001a07887c50404170007426610000308007413a0040806003007110400d64402c140d088a0012000030710314400301c5e007215609003059030f1114540c03c04c0d07900702e1071044038044280c00300f10400b064940e0040703401080704207940c42e11500241c40305104c804090007008002c2d00b40d400008140801303c159008198005005811500c180c0d800b40b070380c1340075200c4560098243e104002801d00105c1020300809002d810151415448d14070300303600080900f42d080303101c2c07010841064040a00e07a8406d02001207d1480101841011612040b070071220845150501440464080903024a1001003401e4854140c104000c410070f290610313000f4010f940524a140340c100d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 516820368 1250 516819118 516819137
    0x120e070303111032010e060d0804030b15030601060e0a170c060703090e0f0601230409090c080c0109080d08060102160923091b0f030105090d0206010504020f0d02030403 74
    0x400c1544100c101121628207010303e000c13903014809074000036440d030054100b80340341e0040c01403208134442c560300060103070303941030801c080e6003003242050103250030041c0903008010030b01c400400009180005000124140c3c0d9040c0d03a211740a490150104017500e401c00720010b0f0401080030049403078140b0980c10350940c0c0c0d096040c20700140e041d80c00400201d000c10070410041c070aa030108450107901507244d0b00050b440c3c2c14100000313050003c98141a1445040458800110b0110402a00d0044c042c0ca10b09011310340081c6408104164980900180c5100e403084411096129098410840703a1030390207000c000b034070300500300c41d003010041259041d44101c4c0b03204a41003d25406020040400100000d4020f0409006d200e01e020038903003002e0308a401405101d2446400b0444490107244840b484045251541c00308440b14620004558103510701002c014081c00c1c0814040503080155082d131700309130f881d501000128062403030004121740c818882e10042c0c03801c42c0d00070b40c3c10500034200903604 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 516821618 1250 516820368 516820393
    0x21305040510031a0a052406210703020d200304121103040f15230c1e24090c1215040c0f0807030b040201050721050a120e07030311 58
    0x18941c02c4019085800e009900300040708203140308068005002c50071f00503010780c08022007404585041d24151181e400040c003d410f845415400c0002d040100c0002c244610b00400043d0003074202c42310030511b8a003030504c0c0300440700341a1000e010901103c0c21403811a19151a0002c01d180701c46400b900f4855146a14002c80130100007500003001d5144161444a017041e07107100d0200008400b400611910b1348000800c140308410741c0380c503c642c3c0440d0640350302c1b00b412003500d0115004401078046174a083e403100003020225060080103280f41c552903094a101104c0300d45060201c0350556140c00818050b0054603000b500032a0968402084130080d0111108800e4020070a503401c407044080f0030401c10090038248440c000901c00300b0f020b01415031030340c0c646000c0300b100148000e04000b40011040100300a0120b070740043c44041206e4000204007400c05080e50340050040000304004001088002004c1d001c2d003142c400321500905002031442e581075820502014a4001d18001d03880c0c1040d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 516822868 1250 516821618 516821633
    0xe15130f050609011505180609070912120215010f031704030203100e0609032a010603080a050d0f060b1c0f14060906030601060f080c090d08071502130504051003 71
    0x40c0502d5000005c0000103149200c10783d45607076200710700404108026084911400f010705078003440585040c05290f540210844905202d0740000d210740402842039400d0010100e90411203c49917002c5a003004642d402801c01ca40d02449070076940c0440000900c0012040c2d8401400400b80e44440c0d420a6241d030f0010303007000f4403001310313076079450f0f0761034165907011b03010011a40c00c0b421a5000d1850032014a21a1a01da41c240d4142d01c00480c5115401680c0d0800350300c000000d503040210f294a51200f494010501da100d150400041800d01040c1c00d821035107031043c1d0b400c445850000310315240440c03038940301c5e10b810322403080c2c0b0503a540c54030003003a1061801200b52550315121940914500302080003207600c0c0c05000240a030b032000d070062001d0ba030400c210f8002c155560500004a90351070078500c03610b106108442d178024050241010420450101030241544108000b81035800710040c450203e02680303125110032980c21504014505080d441207800c66101403034181056201d8a81c0c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 516824118 1250 516822868 516822871
    0x70f060c12050c04080a020420070c0e060415031103120301140a0803030c1213020a15020613080307050706060519030201080906090d2007090c030e15130f0506 70
    0x100d240c1044a0000d0700041c402c10f98080303616a121070400d0b05003010103a40300c44803d8001c0c09160b403940c00c807514856251405400139030511000d9035460485c608500366504601c01c1c581581000f03404100c051403d80140c2000500d041d0900150030301d1500c50300c105028902406826001c0c0010b2182600b0194006501070101c102d26001e84c0c5c03032200b0034040c1642503540301940c150020307c01d0040c1400384e401260900708210203801135035160030f0b0500c030030f026140350000d41c00f44080100040d03200c42100418910040d54017910360590754420480030b04035980c00c0040c01040c041000604c0079020700044c1008038055000004d4140d00c50010840d000c5000c0b6503001d92040e00c1e0010411903900c5258680d00080c000c0c0904058103045041c540c0d10000f0303c01c0e0310148900740144071101d4007121800f91604070301c02d00300d80c509580c2d004407100030910b0303895040020782441900011503000041903040c01160b40c1280b01c0950383c4016405134100c0e05981129102803510100011850420919 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 516825368 1250 516824118 516824141
    0x120307200c0312070822120501050f130c0312020a080c0105041101260c0c030310080f12090613050306040305030105011706090a0506032509060b0405090c070f06 71
    0xe01c681c545031020903140c15840b2900c1c800e103800800244001495110031740700301c0d40d40c0100d044a0303444214121035644c00590880d144112140307200b0403c1c0203054100c1c07402580000c100c1e021a8a5048003000f03540040300028000d105040740c204000703003807104070f840e140005106903903080540b659240341907404104808400e0b91200240800c0c040020a2004454001d0800da00b6044108240c40e0042040c05101c149180310039000880400482c801c40c2d1030a812a4280d80d5a45040e243d9959004424051540c1d244240b01d20401540c01c000750300e00c5241e009900c4281130004074800c000060f401001c0c80c0c2c070000c9441c040002c00f5101000300902442c82900c0341c6840e0b60515000512880c2003480c041d003600e26103824040c1d031782c540c400d4003500b0031120003001c02c20303940b40f20200b4030b0002c104407185580744400341c1d0b002440c400c414038541600c0c0b4684013401295a0b410b804038043c02540511a44205010042609401128010664a4440c4005c0c0d140d03160070b034807028111681100e10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 516826618 1250 516825368 516825373
    0xc090f0d0816140f060f0f01030c0905090307020d060504111017090f0f07082107060b01170a09061505100507061512030201180b010504021b060718060c020312030720 73
    0x107104040c201250300130f520a07d00c101b0783c071141d0324507224090f052001d84101220346030340e000172a0305868113004540c4a0364001d02007005001079417800b000100422181030b03c0114041c5480c1189150000c00805c008007544e640c4400b00d2950000d00d0303100c000c00fa080c01204d12505c6646911074000340b0034015800141c030094007060380780c10107290400000400d0007a40e8001c0801a0503150203100a44402c1074014400051140c40080184c0300e43c801010b81c01c004500d040b0402400c18096004032403140c0c4234400c280f02e10b134052036115000d42c845000b110341c00340d0510206410141b141d00a008424060300340442c4a216044a254482455400c030f051404802e034441000e050b024051106625118241c1c0703c403000244c0c07201c140d068010b0207a284983d07000500440309948402110414402000640341c843c00c01c0d05000d0100e041c9008000c1201420f2503001500c0c6020300c0010f58125009005003030000342c481d10840d45540024040c1081c8840080b8481107141001110011024034400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 516827868 1250 516826618 516826621
    0xb0f09120a081b071a0a020a02181605030408071e08070c0303110a15110d051014150307030506040912020a020915060711040e060c090f0d0816140f06 66
    0x84480700c0c1003070040b0302503080c1d000031003c20900304c40907a00500c071184440406d4035003803072010072810076030030b00e601a6000024400d801500608405014016480302401500302c0c10f0b000d80550740b500080f600500316140500c850800b150f03440305980e00c00e01001e5901c6690314015980d901460b040311100b0360310055405d00910405420498114034255014020245c0312910f5590315400c458061000725010745501c0d41c60054031001d800d039008040d524500307004a1922402e106071010340340c0318001070000c446800302c2582c20301700e0b01d500703644079003d81c002c0c950b680310036003a4040c0a020341126007042d03030b03419180c020170ba20003041070302640c1650141403000b18078010403400380405007080070322085490b16806242da408045418096010380401e10602d13580f0300160040c40840c064030b100d030040303104000204501800805500c0d80885d00460898449800e10151910540e402400c40808104143d000740c0c500742c0309001c1c917100d09804103008040d40001e41c18100e052040034841d500c080d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 516829118 1250 516827868 516827887
    0x306120f0c09110d0e190302010b1e01051e070f030503090f0c01021504020a0306021615050f190f110901021902061e0c01020a050904050604060b0f09120a08 69
    0xc1c480300c01491003050a101c160300312005003407a0301c0b406001d0800b60b95a4040e48590350300900404510703808064141881c03c00c03c3c10068060a544040c2900c0f50b800018a464020904c052807049800180d60346410a28201d0344081c1900c420360395a513a1407404c3c81000005070301240b0f1610f1092103941c1d256201d04003903c1c224a0a4040d20500c0055007044040007081d036070006511304840c1010303c8200c070720b03100c9002142c9840f04580025003400d0001501540030480d102616020911403c00c04c20b04d4580a4001411201d0695100c121910280007003844007880307920941482240080000e00e0f0328400011104803a070003010030414007000304042c58603680511034000f10722003400400048000740e50000e0000e1055490083c150b20040404440e4444200c0540d0f0004410000840d0784200a840c007920355000700c43d04500c52070500000489505182c0600f1080f2448070f80b509040101a01031002180c105010540c1c01c5001e580c4500c60f0900c080150300d144074051802d6507034805108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 516830368 1250 516829118 516829133
    0x110a050f1b0d09260c0d170712090b04030510051e0a2003040b010302010f0203041502030d06170a0809030309040f0b1801060e010315030b04050d020d03110403120306120f 75
    0xd10710340c01d020030a0b07013225050394002c5120315240e0000c0740d00c2c4a144901d07252110a0a00b421180c031000c00000c1100002c201e41c1980701c00583c5615210760410310343d900c2d11810548664000103004d86c1050005174050a001d4001070303009060b040c480d207000406040120700d107410845410408076156642c04000700090f0740c1b4461141509002185585800c0c1c0b180040c1d80f406100003410012201c07201846c0318401d1055502030301c405003401c0e40000203c0da0083da44d400036010702c4500d40c41d101f0009040718604d080c40030000d0748400906401d604640300c660349a00500b000c0d0f0340600040103411034942d60b604c2543d41a00440318001030041c002d2040c0f140d00804032101e46c207004085001031140c1908071100000503d0709185c00708101000c0700c000580210507900003002404080207000411501050911001c841c035400c0741c0303120b85a83d400b102915103048844441d03000401050020410010b003c01c2206200e05002c14140ea60b518103121016000da070549400d03600ca040f003020403090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 516831618 1250 516830368 516830399
    0x80a0506042f0c030309060105090f1315060f0b1c0213090510030623090105130f0501020903070b040303181d0403020106150309020301110a050f1b0d09 67
    0x140c6080001c50000069a000d00e180d4000c4079940380c50748640d100402e0303008002c41d140d00450790241d94482c28100141581c5080030301a8038400c02020002445203601107245034490700c070f0925029a9841d054a4090000d5840644500c040b500c8100100c0d030012171b460b801004107590341d0002c0c1c2d00c89040d40c0c01c4414078a1612202c1c119801041120b41c142c811600b03000030743d92a00400111500c0c1c0d15903e90020304030750300042c0f0040c10003620152003141140082c40e10b00d40e0407100502c41c2d540351805401ca0314116180d0302d21558160140000c14184a03050107401c0c4600f00051a1103c040c3c00a454510f980d0b02255420b50000780510400d58080340e81e0782c6035420b40d601c000129041054540c2d000b60340980c0c48081c000e1410000b400d142c403d4024200070440c280d01c041e2140c80f140d0004001c0c00d40114160300940c2402e00a409141c9010121001c0801983d5124200110040102410b038812520b040035601c2007000e0b20080301c0227014070395040d00c40307407a0391b101c4074900b50200c14182e20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 516832868 1250 516831618 516831631
    0x6210a0c0e01050307050c1204030b090c130f020705010e2d060105060a030b040c03150b09101803052a06270d200102120703231603080a05 61
    0x5000d8a1000980c2000d20300c0c800e50400d0030074944994032400c0440c2c041c0982d024000084c802c03058000c5403216010700801c1928003c03180c45140d40d90b1700b40d66035980e04050345001d8210b001100040c4d0300e220194030042c99071001000140c03419885841da0b50039664006001780b40c03a00210007035110b030707000329800703442005c113082c1038100c03140c03040000c681c45e440144150380c000c490005020700598400e5202c0d801c8490000c00070098022407440050042c805041034156040c5a20004a07440304010255003080000030f0580c094041920000c840703070040c14080000d203074241300f004400501c040c441c040d060180c001c0e10710391040058a42c00c818a80b405501800b8130400c1212884480e800d0b80c07403401e880380000e0b85641ea1060040804d81ea4084050064040100000d0103d0400319001d00c0349982a001d901300c86481d16056001c0701e503480b4881c0c004000c12101d22403162030032030358000c8040800b58420f0044c00d0031004210321f07c1d240d40c0404200c0c0080e111004214a81449125040e0821f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 516834118 1250 516832868 516832871
    0x120b090a0e0f0f0604110d06050f070e010c1106180d030c020a120519080903161e06050706110403060f050601030e0d0f081003020a0305030c010507080c0a030e010b06210a 75
    0x181c500342d80d0785072040508041c00b00e40748403040801a443d2402890b5070568010f000f00010b14020144108803501a0bc0107800a00b0a4219404039803068451801282e0806000360780044224100030250340140e0700035840119251991180c0e0343e4482c101c80030300d4002d440b00408002d440c41003016041680d00690300a41043e4509808108001032008503040b10824112034082070307040c2a002805458042c075418450b40c003031032258284502c03a440c21a4000c01c10b550088a45180c240b418151034000c14001800a02140010036500d4001d41c25500840700c806140c00d40b60348910007503804241d8046840d40e01c40c0240310345541e240c420719100103107060140c007035026640001031243d040900c602d003c21604401281501444029110045900501d603400142d9079140541d01d07608001c00310102540b800340090396060054400a101d1056002c03c107140c004100e0040e070042c1040c0c0d00d1b031201c1d590307940703000d00325038843c1001030112030614a40c040784026421800354203000d00400d82240f05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 516835368 1250 516834118 516834133
    0x9050619261c030c09090507210b010c080d15030602040e07020604020f01180e180708161208070f0b10060302091e150a0f09170607120b090a0e0f 64
    0x4200c2c001c2808503a000c07071401081d0307101007000440310514036401a01000b8500814000d9003130300700100c081e5510180c0e641400d00300c805189082181c80b4003400a003ca83c21246260014071968001d0414034503034140052000304581e0841010891900210b616550005003403042c04420001c09a0143c064802050b581c03410b980400c3c9561940c5a01a040c002c070750b03605802902e00c8001c40d40190803412100c030114500036001802c80c0d45060010400d50140c2040411441004180d0141d00c038111140d00b513041e03240030b0001d001c4881c0310f442a90b4000051085100261040c0c1000102ca805400c0c01c09080c00d182141c02003001e40c0740e2024042c9441042901003544a076540043c10300ca600d225841d01c01c10b11000310303103461500441c140303c0510008070106000d0f0000c1c0315034803807915580c400562540310400444100d040c01d8040182e540860300003501c030352040c8510710919004100105400c1f0108000c1103540070280d41414949031153355541e40c0210400110f0b1400c1d10790801403c51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 516836618 1250 516835368 516835393
    0x151d010c0201050c0c1201020325021c03060801020307020f160f03060c03060b0f0301030b1b07060506060d1e15030f0807170316080a0c090905061926 66
    0x2403041400002d040c4000412080410041401100080c46019100c0400020018a004d000350301c220340c1d5100340c254040c1d01d4080d8400360840450070140f076800525035042e0240380b2102e90703298610700c002095120100480d034404280040d42c00b61283da0004c1c80e40741d211120103800c01071100520321807940842010040d204290b41d2030002ca0360070100c001000101400c0840c00b8042d140c02528901c2400101c004502c00d0f001c000f1812a40528184c4009840c0d00b06545000031072104000401d080610100c00880d80d664000c0c0d4121800421051410b00c22040020549d0003003a012541e60518081c0c03d0b01580d09400340191380411030415080c1c441c215519500a4501110061300d00c0704c0200790482004035026901e50305c1c2e020741442c00c1e280c1c90f10340000d001d10300b0000040b100141c611781c0070950030482401496011039860b15000201c9041041c1103009000003030a1546c8076880c03101b03044020540d90f2199000d40f1441413403080001410481c003884855100061034283c3c0304c003490040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 516837868 1250 516836618 516836627
    0x60b1507120e100302130e070903050d0509060f13031205040f0e04020d0b100e010306050a0e0d201002040303020105100b1c0c0e03010e0c03011d0601030201050c1501151d01 76
    0xc80d8610b5040041c0c0303800a00e41c1d44041c0d03080a40010401030a6007042c00a115080b147c3d1400320bd118500b1182c00c6091b40d0412605030180c415220b400c40c0c010300484080c5440751000d000c0038880c42084000c211340c1d03511001e94100d1800c41c1ca001094d07000605204502c800d10012002c0d1420400349181400d00c0e40c046041d030f40b0881d201501c001c0054020070320500c00340c00f0f050003c204800d8461075958403420100000d110540d07613801601d150090b01c1c1002c80000c1822003604403a030326004024000c10a079904801441c0940c04034034019100104c8944129201510186000740c0c000100c9141254840c64032030b1964005001c20007081c41208034034030902c81d680c603c140b03843d070011401c0820114240d80c251070300002d640c2d25508002c44507800d42c10000c0c07186880502180240f004503801111442482c40780e4071107141941003400180055401240140b0404010200302c0315810360012940c030420000303810032800140780360002c01c0c0140e4030042481da19400d0f015140842c07409900081d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 516839118 1250 516837868 516837889
    0xf0111030d0203100b03070207050a1e09020c0f0a0804030c0605191409041404060c090b04171501241403070309021507150e06090613060b1507120e 65
    0x4141c140c0000024003003146084106008100380d107200341d00c0e0304100d1806925032280740100382c041d000b2200001403c180c000740a0310070b2916025445e01d02400c02d07a68001951108080e882184207000c0d0418451800300210798056005454244e1954114030744984400d520382c1c004c000708a0140f05c034810f01e8024403140702c1010090708159034110725014084103280030340c10070164001e18110002a180c6040380116208910441c420000540c4c511026540f081032030050001c10b034403d000500085540880301d200310b03418a402c0b0ba01a400f9104003103c034000c04d030080350348580005001001048905c080b10081c0c0174509241540001c000c00d0b4041c1400b000305003404064556080c2415034840c461a80c8000c1c20b0041d40d5959030711541030075050500d01c9c0a680031820b2814101e1023121901107101030081001c02d014160549903040144600c0003025000c2d1080f80e80d0b0881480d050f44c42607104144003900a4941e602c03119a82801c43d03001054600b00c0c6d003030141403407180510350b844410304c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 516840368 1250 516839118 516839137
    0x602030f0d15050d050d0f03020a170402040603060207140606040b0603041e0c060216090e07030b04080409290109350f0105061905090411030f010908090f011103 71
    0x250600c01d0004000b0341d0026520254018840201c00c8042c4000071444040048054071038400e00205400e0132012882100c003c0710009100e210303140e101e240c0c43c04c141c0c3c0d001070000b0804203d0580b01c0d11140200d80c807008044071081000310040e000d80f9010301c0902d92140c1d080b54200030581c41403011a0051000400c0200a9032442a00038604500c62540007003207600080c01c1c2c61a10307220207001e07642c2c111101007250001562000041e8038041c9003d4104420650000b5151503881c6903540d801100d0080c0040764240824000405e004142e4840c1a1400382c1726516500b00c00c40502c00403001c2481c900c1001c3c10040b00000600541030102800ba03610144080c0e003070340007110940316000d44c2041d00352400c40740c0640c04161640450540156014410840d6143c0e140c5812120b89240400321380b00303a80d044407020b0002008602c240c01d5140071030401400f95408d010f0050348003030850703a0b1840120f68440003ca0900b4a03410180c84580b10080d0a09080c244071640b036124940ea4001d03220701c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 516841618 1250 516840368 516840371
    0x209040809060d15050a081f0b1c11040b0d0b011701020d1a120a05070b0904140a09170c0c040e0a12080708150f0f15040b03040c0602030f0d 62
    0x8982154803404200e900320b0501c4102080044c402032560030360342c0118418680b060218042c00320f0100d1010500c510180b100044105840359629000d001408075102c0c00b5602146d400071181e01c0c03510445401020038031881801004c00341000401c0115041c41314028058101d01115000041c11000755a040d0b174200c00c211100055644070303c0b13001e4411858549402410030849155502040c000e80d10400b6046840f0013614250541c2a541c500c0a080058500d91001c0010402840d501004081e400c0f070141021600b0402402c620781c0001d02a2600403005a94800c00c4050010f00d02400c9c9051460400700d61404054000d240c0e03440200c0d41f10644034641d2605a000c414004121342c0365000c4c1d100c00240c04500803000003a060f0b010071507072180856030040002e0301e6100303c078042c07540d06c2c0c82c010010300c0c0c034041140902600000d070740a00c0da0046102072001050100c0507000d00f004200c005020784e541d06c1d2a140c100303100c850300d9226006650060080028a4005005442c001000e00b43d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 516842868 1250 516841618 516841627
    0x6010b0406023d05040c0506090102100c090f170c061905031f0b04140a0e0f040c0905131103070e1902070602030a0f0b01080402010816110609070501020d0c02090408 73
    0x2e0201600025148001078880f0b850552180f95441e8001e40d11550164102c0d0034a19982c0f0248500c1c5d20507481c0d0309006801241c0380c0044882c49501400070401320b450325151458407003800320030318210354110135643d4541c2d0441090401d420003400945d180d0070340340b04e42407486008280150f1071084980b041401b80c04000910003029240c00044011001e4001c400c0c03203a607605440303100d98020f01800404140c82c40d2a621542000001e0108407207078010814402d5450880f041500309000d04101c8201d402140c00041c21341c554050340d07000d40200d180b0802c0c5138000d031410750400c0c0c1411003058002e0304920420007844d040c0b01016544003050850505c11941d02c025044003e1184c803100410445c0702005004c01c949465100c011403d003241002c103c0d0484920041d6036409080f14002d0024400710002a0541c10301c05100a503000981800c02104400483d12800d00d541114500010350100d80100019a0304001c00c2c40100f0060a1541d01c0342c1c040c3d0082142042c0040014059040018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 516844118 1250 516842868 516842923
    0x1c080a020a020a080f09280e04081c05150a08060a0209061620030f060403210e0a02280501030b1309060b03121602090a110c0d0206010b040602 63
    0xf14240e071043c2e1080c1c81c0340c0d4586101c00b00c00015041a0191b5001b000391200c04049411450b01041580120395001c003c1145007207801048440c00400403942410140b0a03001c20101445129860305451200400c50b0f14084040c03402c1500080300c0d040c45481a280108180600410400c0c3c12101d184000760369155800c003ca200c0748220b59445c082c05805c10318a00c107104000c2001c80f00242c200242181000302201019541d690032074410305039410000c00302d400a8041c4004110300c40c584a561860030b1600c1c0c01c2c0303000315a8604407624040d0800886002180313440b030300090340d00c071104018a00c2040f0020107005034500602415041c5541c0301d1404642c0ea8584100c2c182c03c04402000380440700903850690054400001018081c0c86081861800c081e0203805580010000c2c210a03841002e0355020442e00480140140507a2541e0b80280c24680380b200004012600074078000704030240004d02c000b0300d4294160310560500800340010700c00310b54007103500820002e000204909412400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 516845368 1250 516844118 516844123
    0x906040504080712030c020c060403080a270303120b03240a2702010e01030209060901050f1e120f04020f060a090503010203070c03030e03030f041509020301090803091c080a020a02 79
    0x1140c040c0c21603020344d84041c42958150810036460400da0300381c4103100304c0942031090301d008a0200a20304030f01400344854103032159541d200c403405070a0070030100b182d00c04204400c013130481d0001c1d000941030382107050181c0d00d14010010300c5c00041e401004100750b2000101d0010300d805510144c0c244802020415845140d000f00d004e41c031000c49040c102d09004e08242011003010348080703000c070b208210b070080c1640c0a842519000c02001c0d0200d4501030501c0011202648500302541c00d2801c1072001c140c0818804003468420f1003500100c9649500c03407500790008420043c400d02c5030340128010000162600541460140c4060350207036280d054600d400e54803001380380c116039055072020040101641d400510f00000711f0003528100107403450b440825450740300c01c581117942c95070b000b40071030009040c0d50215540743d03400d41000954014140d0001c0e003951482801548c000c40302100f80250480306001084401c0d0132101d21103841c0e2a620409030000100500320061950302059240403980207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 516846618 1250 516845368 516845377
    0x22205100e0f0c07300305041e0c0306020711150f0904020f09090405030d060902090306131b0b03060405010503010c0c0303020a020a320a05070311010507060e0a050d02010b090604050408 82
    0x4680c0c2007100440c17a182c840c1d200d40e512042c881001480035206100c0c00792260501482d040f40d00315030440070009820904400d070340030885407a010030380008007050306807018010702442240305c1a0203001080801c540441038035041c09041501700481e16240035080121040102e05030781c00740e210b6001c2c2c100d8801d00c0c01540180b40c0c01c0780030041000b08200000c801800546a00a4104403044e26000364804034020000c202c0d07007503030091002c140f01d0f0b034007040d000d0241480740603c0d48441c80c101500001c003115079880f0007000c2c1004003d1100c0c40c5014005c2c0c074094003095008002c007070044a402001100800310280506038005645040d0034800d01c440721040b0380081c00d880c00d40410003000041c003c502c802080b882d8002054900e06046c0104250301c0046d0800000c200782c85c1982c855104108407441902d040c40000c000c61b40c0020b44031302808010b46c0c482d80261202000905051f03003003500084c0810116458044681e1440d5a5009450381002e4280c5c0e0010313095a440c50300b510316214 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 516847868 1250 516846618 516846623
    0x120a0915050702040e1f27020402210103030f050a02030711060915120609090d03110d09050d0305070516151d07061d060406030e0109022205100e0f0c07 67
    0x30802012603007040002c2c411405d1b111544036201d04a11340560808440da00d6050300029107038100101c00100c4040801c0440e54001400145031030107203500a070a0140204c3c5000e500d5003440d0041082c1360300f01c041c82404105500740359142c04e044840c020745038071030300000909449510114402a41b500825074009100c00707041d071130140e559904400e01d40c1e04944840015130380034400241c140d040042c94036000700e030000000c2c03d000ca10049d040cac0147c1400c503045100b12000b803004e0050306016000d142d00343d60061000c0e0007404e240d11001000e0710402480c0006106003003018880e0145401e0b103a088150300214250226903550740100d000e84880141e00084495036501200c1c50300c40894181c0440c0d68580303c02071202180084100005010700c0b44680c0000300340810420503000e0b400020030b40301d80c600009041c2e0450350014030b4003030040c80240303030600c0c09090192580b4aa40301311a0000d211000807007000346003561208415a00420b02c58250280202041324841c11030155440c856 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 516849118 1250 516847868 516847871
    0x5070915140409020d0608070305370b0103060507141606020d06031a0f090d030b01020a0506070210060e2715041518030e0103050613140603120a091505070204 70
    0x903501d44283c0080d40210503041249494842d0000d0145000264442200c3d0700c90040c20211080b044d103001d056443e0080414984820009006000c10f03844441003051f205001e400501e50540c20483e0403079030000c11040c2130107184491210709258400960b03a18a1034800d420b08002e05510340013010380207218850210509182022007002034056000384074159552020721140d40341e024100307280c10103603440d18198105901c2c9403840b038440d4101c030130082c8040c011100c503541c1c55580c10349000300c12140300300141c20030070750440344420f907001d013600621020450315403e0401d092841c20b040141104d0102ca002000c10080e4001c40c140f1852150041c0c5aa01c1c109070320b06820030041c1c0c284507080000801e45032032161030000a00041d43c210300c540658079800314010920040d8000c0c00007800c110b90042084000018a9456000744036050b50b0000116010741801c1c41031601d8102e0203400c40680c9401400044d10480d4000c28400c01c480ca419801d030112440c2020a40711807080000294010f0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 516850368 1250 516849118 516849127
    0x40e0906011a04060c0305090d2907110304050d030e090406090317010303080f1b0c030403050f03031b130b0a050a2307032105091b040507091514 64
    0x2410082100da04030b81d440d0302010342090045406440c0d42c0f207070b409a00c000c05c0c41e403085400031030310030b20180c02e4039040500001d000384810349803106a5400c00145030486210140c9000c043d1a4450702c40d6003000181c140200e82d9405a00c52648a000c0c078010140208003c040010070b140c8640e420350356016000d845182e03e81401d00b811800b4048611040d00810240020b1031254230b04801800e040b00e4040c0d8400c0031588a07000041e1074000050800c0304800c6400d06d1000410088500500001d00000000c1d5a1940366150550510f046414603860302d030000d10402180205c0c40941560211500d0b544960b0f410700071300c40b10048500c1d82c00c91158203401040c400d0f00c0a8000380109105a66610f44040c240003110030640c050007903a8601890070742c00d0100c0d0b000280215825095041c640400540c942d103c8044201200c41c1290703c0c00580d844040003580314000c05400c001030328002c1e502400b042c039100380050704084080c491b041002101c05d03014210b152207520802c0c0000b40c1d032400319545 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 516851618 1250 516850368 516850381
    0x30d020d021e13090f0f0903111615030209011809060315020306060f070302120f0c103813061d09031b190503090f241b060703020a0806010219110105040e 68
    0x884272903c0100c0d001f441500d200c170b9546447c14000004403081030a0140c00e04c1c40d03400b0700300d020350080780100f41400304420440d01880c010b44e41c442c01402406000003030040c614104040500c85200703c10140070b10410603c00662600022109804c20890701541d43c1c2926240884c2381c80340456140414030004501d6038880d40c0c4007001407119055050480b1443c421700f02c150320032030f2800301c15021465560301300603055180c0e910f80c0b030003001c00341145900d8020142d4049021b46800c424a410b00c2c65079150103104218400e0003006c0090408004010240703003a401140c0c2d20700c0746600808409241e503401319002c100030014043c8201851480c84482074031807074256500e42040b00b085226198404050005023030001c80116080c00940c404be0302451f1030450140d007030b403206590600c8a002d007900c680225404000150080c200c5a41c010795070a40c84800520086028113903a045420000c0c2d011030107551507140302502c2c3d400c9194a84c4061403540183ca45110f5544108200c1d118075042210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 516852868 1250 516851618 516851627
    0x23120913051e0a0f0e0606030a022718061b07150209030307061a010e0a0312030b030d17061203030415180c18051b030702030d020d021e13090f0f0903 66
    0x10a0484c80090200012409007152500011964950550302083d4144050319050300c244501c014480c680d4500c4800e600b50b1415001c0301210b80300c48500c0103201c00e00d481902004500c0d4084088210101244020200319041d840f4021003d00a200a0b00e080100d6050940c12548010402401c40b6640c040340c3c90030034050703e400d0b0b40c0050403400d541d4203100154016081e81c000e0742c800603c559159030541d41d9003000082290802c4040590760320b02c4129940707040007141d8160169032604100c2007101e04e42681c2034500105110f002e4038207480030700320001002055941241c1c0c00f05214410794104078000005140082c25049084038111560041c8128100c4200030740e00d04600424542d51410f0022041c1c6205032000441410740c0a28140c80d1001c035005941c1000f910305c1624503041000da15402a80c006029507201554001121f40b021214203158081d08521444060f04110422004800d1102c0901c10000307920f0303d0f0100d042462a0030390040c180400c20000400c00c40883c1d0400a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 516854118 1250 516852868 516852881
    0x411030a151502030a081302030303010f090612020604061d092a070506130c030b0123030703020913080f040611190c0b0c030723120913051e0a 63
    0x128210180e408602c0ca841102002c110070300503002980b8000301618201c402c1c0200611401e40c80710b084262100595003800158000d213140540d114990741040c2e4018110307010b0360304c84e101100e0450720358070041e01c0700410380d0100c4013542446040140241803001100e85600155903008419030100030440040204184174021121000468004e82d0400b50b110340c41842c001030165884040000c4c40c80340d80110115405101c0d8031184019139584e910301c803400030300b03030442c901e4502c004010304000c04502c02030450f440b0f0f0440080c08070b641b841d00403401e445406051101e181e5a50b856200506c43e002080f5044e0b05416800b02c0e031390b29500c400040200100301600c200501542d0703011b804540700061300040303030354000d480007011910301501c41c031b2160302100204005000600010010444419100290030b40384a0800c611580e000b2406081252000346890200310a21400707010780ca0314400344990300b42c005000111904c034100001c16051142c101d104c443c00c000b4003000058031081d007000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 516855368 1250 516854118 516854141
    0x10303030e0c04090c03020607020303040e0f041a040c03080d0b060409090b0c070c0e04031214010303020f03070308060904141f1103040816060605120703120207060f030b0411030a 79
    0x2e42c2250082010030098a0000d0f0f030103400002c203400f05101601c1c0040013131941d10320003070841c1e00d06640c6440b0308070000003c540304021030312001c04010074090816019654074040b00d249030428a0250340b9803039034810501000d00030400200341c2400c1500243d02c20300340020b000b030019807240e540710260405043c06500c1250000c280da40400c030384078910825a004154440140b404a070300344209411501c000800c140c040044d070103103061004207140b050342c00c0417914809030cc0c81c66040d0301707000c2d00e0b040700200d040c440743d07008000030404250b026000980201c021602e070140c607200c0b4204040c01e110061101c0400c0d0040380300b004060b221a44100c0305901da003040c240001c41410240ca14980422140a0540710080040201342d000c00415413a109114441c0090072075240c00100e251850244400c11003a4098036082c07050250324804050308944500c0140106414010010141885e01a50506150b11141200c0301c95480341c10003420000c15541c2c042e164501080024090102d11009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 516856618 1250 516855368 516855373
    0xa180f0e01150807020d0c1b0b07020f03030c0d0c051203100609091104090b12030f0703020f01020702030705060a0903052a0406050306070e06040b1204030f08040b01061d09010303030e 81
    0x5400b1078064a0003a20420050b0081c050324858904256a00c2e64603020480b95801d066010225603950001c40e58040d104041c03007140c40b8041481403144801e143c14002d44283d0051101800c8080c0008030321008a40f0b914100035402d0f0302d403900740c2c607006402005200c80c44022040143d001d07034a10826040f990300e6a142c2846690b5118200c1c11a00b200c40c8420030542c0400c420b0100d01580e03000a4500c69005d0f12205c484401121090305540249583ea4510700c000036200052644c1049010004610310b40214504220359001035600d81d024843d5a024800c00318000e0780107030140300300300010354006060300c0c20b0f044401d040c1400d590585000102d020045041e03015241000e21440c030507288007400500003512944000d94120030001e8a0703aa003d00104000702e04083c2e02400b03420b5980b200809586282802d15001d84075110360341d445020020038500708170108000701001c5044a0a074240300124603a0034034103540460380303104080d030441e41180000041541c590701408051780d0071007e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 516857868 1250 516856618 516856649
    0x50a0204090305070309060c030c06180c09150f08060a090203120406020601051309031d1c0c0608010e071b020a120f020a06320415030b041506050a180f0e01 69
    0x41688e43d41062000a0700044403200c1031400541a540038100c83c0800d6030b400d00030b1100e2940c8040c0460529001410800d840d181650344140a4000e100b0140901c111001240740c10151000d54403580100380d11007840e283d44e06c020964501b40840c8113400c0d011108550380e242c42e2000a5660760080c403801d802050030821462003202c161140b001001c0e890368a100c2061561010305101c12034988031581d1046440c0725551030181022071550007a4480c115081206290413030140c4804016407100c61602240020005e400c0d50001855070035248848200a040c82d440c00030552100c500d4102805540e80901d901040c00803040090074103d2003260000041c0f85c4650044076020f50800e0141140c41062444d1204081c5184100c0000071420a105041c00d54602000414440264400002c43ea45502c4405681031a0141d884004ca4041d40c0040b0f951400e40010b140d4070401c10110304001084108141e003200280c4000010041100011046901c900c40722092141c20f10800ca81a000d072003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 516859118 1250 516857868 516857879
    0x4060603031704050303060103090c0f03030809060a0902010927020309150606250503071211070f150302030a0b03070b13080114060114040503010614040c0e06090d050a0204090305070309 82
    0x480c0c40c2c41554000085c60030b544038180103401802c050300080315a45400400070428200020140c00103501950b110f503000e00f8110403141c10020302400c3c6000003820812004050b0340c009404d01d042303400040c08902030300e914844102c5100340c04688954103074000400e0048410340090074107955001c0c00d0126205071102ca04100407071080ca40070491108081d00d24607100c40315a448840698000c0080d84c1c5010355940e580c00c4a1354244440741c000c04e94070344000600020401404001d03104624a01010a04007074805000c14031340140081055000800200e050600350054550703c1c0b0b0103000c03a070206859140c40006500700080c2c3d01201030300310000040750041400b440c03501c4038220404041d1910717002c0044500c021010031640303400004100001d01a2024454240140488282c014075140280304002c2550084002c060030020b942c0d4880509a68a4003211050700d405c4401400101403460034500309080030f0310103036106250009940515401100800e0174a02c2036407442d90094841 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 516860368 1250 516859118 516859157
    0x606060e21060a180605130302120a120507020f0a050304052b080a110f160e0f160c1b081504050d18030f03031508010b151806030406060303 62
    0x250705401d410703404400440c00c440c01540c03001c204100680414a8140707010b44414056600c1503d890307020010b201861414190705003c20100003c00390f4019143c00070900e001030605108000ca01000d6076150080765503917000300080d0070204000c1342034650542e410f0070820b88a820502c00c642c01110010764401044100004244211200b5603001549485649804a481d04010340e0082400346000ca485020203081021304880c40300038000301301d031402460b501c2400e03c0d50b503440400940001801d00c0000d950b80b00c06540c2c082001902800b02d401d00903021144210342d198050011868400b00b581c0801c1092000025182000b0458001c9030b107500d0419565031003140c010f02a41c1060220180c1140b1070f16041603000400c02441d0324a54030f80c1c482c0100d890740c15200b140840d6444113550f050f1040c14458a0041c11000c00804c114200803010231400446100455140305000030742c002617414086552520a038050440764607440c0501c1d001c0e0041c000c80c001503000c5841c05140d410013903180b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 516861618 1250 516860368 516860419
    0x2030903070306050604090b0c1801030902090f060102010609150f12030906080402061b061e0106051c150305150f0103020609190302040c020109030306080a03020a0b0703090606060e 80
    0x1030001c2400c0d80c61919560010b000c05021590b01940b50812100451650b080013030042051a400329035501010711910490012202510b041c141040c407050007503a41c1d102c4080d40501104149010341c0e039034500407801010300fa04903505092402d9290281c40d614000c1c071901b80d81c5002a020141911408c3c244c03103084d944038009001a0a1131001d000d00c900c80c001142d04030340b010b0200c50030403c81e0007162400480b0756482c0790305640000304108460000c1404114814604041d603401541410300c010014819030b0380b243d2410342410b441098030b8000d6807007802618101300100080070385074035045440304104000614000c040101146501c2040a0038504803617009195500e0f0941c50014026080d465124442c06040440e10004c050303100c1d401070340c002c4802a400010101550302c1c02404540454000d000b495002c1c1203184000f0b500002c0d9025441d4120302c06010a50341c0306000c40c05040c40c240c00820381c42c24407030006500d0ba0400c141400c5104201c1d204d40419162010451900c0032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 516862868 1250 516861618 516861637
    0xb01260609190303060e04240b0901050f01020f010501030308071101050709090f0e1e070e01031101200f0d08061905041808120f06060f030601140c0604030306150203 73
    0x310b000c0004042e00d41c0e906507000c4500c0703401c021400f5a0b0300c1e04408403c40d81110300340c5054645080c01c0030840656518410050f042400c1084071004d5000420030004050003441c3c09940d410603c0c088a82c020081c055210407a000207010f40e41e100d140040c071204040d80c3c5080800c0a80310307841000c69041c02128450b06203603691a880d0340c6802e1a03200a440e09000c40300d035546e519101400d1f1003005100e1405400c103c103c0e503000156500320b50038544101680402c60710400d000050002421510001d165810b09190580b0b080420020f0105806241740c681c00e0103100310420700c0009040070990100896407030310794450658510050004a8040901c0c24424804110040c001490144d02902c0c0d42c01840d40e006480e4501540c50b1300059105c0c840416103500400c08005c50440f200d144c059000030240c0300541000b04001002c3d6140c00058206814130603007002a40d5515820401d950741540c844040303036070b80c0c1414180503006041502070031500c01045440031481c18000000c4800885 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 516864118 1250 516862868 516862873
    0x60e04050a0501230c093c0102030c070b0d020415020f060105090114010f050405040f1a01022805030d020307050705011d0a14030405060a090608011a07020603040f0b01260609 77
    0x1a0340c084c1044a40c2e0101110765400624500039070080d500841c2032103140c1a1f200903a4980850059040c40c01e0080004841e0440d8004c11111704240c01c00304a040488444104050f00c0f80c0c0c041c80d2000190181e500301503070700300c20040340341100e550005c1c2c41b0481c40d04178400c0d1340c0c003640c8542c28001070711000d004100b080c010b5410140000c0d4802c41e503404011a02e40340940c00c16031a400090b080c0d0741604829a8110340721442d00c5500b4034141102001003070240010100c0742c0308000c603410316070340e0305581844552214402d00c040c0700040c412130b20010300c201c0045503179142c204000340090704000d50558081d86001c0300204c0c00c84000d09001581c0c107401e00148101c4c01c8940c5e40068a4040b5031204101d03020902000400b03031112000b80035070071500c1d01c3d80800c1c6800c00f00021300713580b0164000821442c1910080300c0154403581110b0340c41d901501e0807076880c0d45074145031000700c031a41d43c0203214106200000400482d400a03100e560b1840d00d11800d1069a044543d40d940c1405643d2040e054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 516865368 1250 516864118 516864121
    0x240305090d0f1b02040e030403140304060813060f020304030309110a050f1314010e180c061b01200408120f030f0403181e06030c0f050d060e04050a050123 68
    0x1900a04210300180d141d000030303d2003c4200da010805850301c45403070381030551021509004100541100d803030386020702c40c010b504061500b40020441c40307008c0c048010070b44100742c920040c40031a80008448800b22078003956070f41401d280c014000c2614840a035154000020403002d18031300402c40408461001700300315111002103013013001d00c0d0b82d81e0100e101541c1d511112141092444041c140c02020740300800d0a051600d0b003a41d500c02d4804894000b0340f81c101914800095403044283c4582740d002c2c0d0b0800e100f28003004c0704940108148065400b13000399a4192041074a0301c4001041a19102000d890704050074a1360000c0a0085180d40c0c040d129050000a80c0b24000c1c19000c0e6000b4028606a01b0a000c4120000058052904441c0c07450703030301211410900c2100a0860000d21151608108182c0c20510060001a0a81d0300742c04000c00041c02c90a80042c90b000039000c0d103200ca140302182d0825140030f96980a541008480035420285080040c40c0001001d0711109010310201106 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 516866618 1250 516865368 516865397
    0xb06040b030309040501081c0813030305100b0c070503070909020a0b0904021e0a140403051506060c0706090e060604180c0311070b06012304090b0a240305090d 70
    0x180c068180126014401800b40701c0c0540d40301c0c0140c0b4001d0041c00040c1542d0404080402c168649042d103c2e002d02c00c080c002d015441c2c0784200c841920325094500042d06031900e02c1c2d03040071010755031301c81400e80802003823128000c1c902041d000100d4800f18110b8144d155103000150586d848440069401504d000d4208104441c81d4020400a0300c01000103150181d4030801c05118100f61506135145880840c42c8201030342c01500c04c05600031402030366400c10303103150f950b02e40e900701c43c6407488140700d03c0d000410652786401043e910305d860f2610940f20b00300e0f11080010154000c41c41203074241d032030700008503401e401c0a01c111002e84000030b43c0901c0810015050b040030b00a46045842015918600c0301c10181240d030281c0181c9100b07400509030346c00c20308001800300340c0791030f0440c002c1d207610441e4006141c800c004440840c0d9041c10b0114485003108001945080540c5c40f80d220940e9503001155429907003102c1c0050310000b40c0b01006503844000546a5840d00004040e02080040e41e03403ca4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 516867868 1250 516866618 516866621
    0x1020a021c0210050d050108030412020d031e05071704031a10050603010f081e0606042004080606010f020f030a1d03150106030e01050405060609130602130501030e0a0b0604 76
    0x4040c0d2140c01c4010091895000c1501d00528003450000580c012031402c50445150082d140100f1900c5c0085003040c1c2003006901000603c0000244181c0c4802d41040400d40a0650118a11010040c0f154035140d000d0f030180040e0700ca842d080710002c4aa0070300c603501104490940c2d0640342c0004075000d042d1601228400d46060240221304e202e510010000350b00d5072420b004601904c0d050305000b40e418902180d140c50041c2079120140301000044541c15059400175103107901c103600311004985d41008030501c3c02100c0b119020100c0341c03880000d02142450000400e42e014002c2a82c8240c40040152000ca803120400e51004040342c108102d45e05031940316042c03000217204d09282d41c1c000c0200542c0000d181070700601c203250300c1382c06000040000750f4143c412540700c4003e1100070300039450300c2c0d0744043d00e94100070405441011940049080241f80300310790000700c0c1c0e00400865036000305034201c00d0340c04414455640002d080c00ca4181c81010701046482985034000f00041039500c0e02d0701001b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 516869118 1250 516867868 516867889
    0x30a110a0b040b2e030c050d031e050403140601051005120c090604051023041d130c08060402030c01030c02060f071202071b0902040b04090e011503080903060901050601020a02 77
    0x5822404503135402c2e07021201c06004040030303c10400001c980c2880e42c9018450100107501040c0b0500e0150030820200780c018024071200182000c0b0f10402c1090b00409464600641c0c1010b0720b0211083c05110700c0c4540005d6150607540300301c0e540e14283e03201810840f1680f00d2052001e2035030300e000300811100c0d5061400340405007401025107041a45034030101e11800607040300a0f0018245070100c8056000d901d50503010f9000c0f45006034601810002c0d500441e140364050024030b00d40c1c450020b49500361007500042c040394828490003c03a9039610f034282d960070007900e05900c00c0c02418100c0440750f021b0711461300a02002d40180409a688170a00700038624020452814004082d010942201d45880242580c61051151a101040407410121103500e240c010042e40e900c104424055020280c090f10200c45014002080542c5d280e0129405440d11031b585541840c0081808000c101c46100580381c0d800e0294100c50440d41ca03028240d080c2d076020f0310b80c140581c21884003d00035003003030020300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 516870368 1250 516869118 516869131
    0x140a120f2f1c0b0f06030a090b2a03040203030708070f0309090c080112031709160b09030613030302070203032719050d170d05010302120703050c30030a110a0b040b 72
    0x450201c0c44013011400c1030740104c5c0d014950b42d584041034410401c11550380c98110008448202c15840d21121503107000b00a4080d09107205008400101150780c100206d40445074060512900c80b011032508500403940703020210007081c0000c00104480c601031140481e001440c1e6900701199180401ca0f91461400721415010064840c2112840128250145009070b860000400d1660742c06000d11814010f10303003184400e41810482801c040e40e0000c2c80ca80c0186c1030401411881c06a840c0c20b500a00c25410001e40500022070001c0385c002d080441007810312205841031054014078000c004880726079944000c1d03840b244c0e85041c422420078158a040c890300c100201d0301c01d0154440005160b801002d0703080846900c0d2001401103003807200c1c00301aa550210001d010160550b42c0d074a0f00c2d89078011859009110445442c08620038100515600848130009004a060603404058681e0300426281c404940f900e000000350003c00100814002e802140141254072181c3c0c41e00040c00d0040c240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 516871618 1250 516870368 516870379
    0xd080307120504030801060f05030c0315012313090902091501120603061505060705031c06051206010e010f210c051c0b07140a120f2f1c0b 61
    0x304071808000d10905025600035110511071750314000d0b0040c5103203007800300801001300c144240180a40c1400540c2e8106064007095841d0004440040341c41d100d1034088a003944d0300304c0450f4502c000005004010001b4141500c0003070b07540b5810000141c60302c1c40802508040044001407421100b640d507002c8000052522a8048031101c080a0036590b1580050b03c490780d448600e007035040100c2c02074100400d4280c1d140c07800e081190302e0b09a100d0060021420103a001045c40740741604056020102520004200034004414024655600c071000d00801420400c00000440e1070078030303100b0030307000c40715059020b80005034940080c411001c0080001c542c0d46640c804007041aa64205401c51403600f10340b14224050021f05211482c400003a01800030310440300d58507400400070740d0856031700120a003088044ac2035064040d80013410046040441c00d807415410255099940340070b442c01483d010900b812882c4100761084441c450010b01004803165110505907100c00d1380c001c0c0d020140002d01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 516872868 1250 516871618 516871637
    0xf03030b131536090c031a090d051e0f0c07080303091b0907052b0b0103230105090a2703080f0402030c13060801020d061a07020d080307 60
    0xea030741c190769030040c03580a80c2256140600180040d480c3d9454044140c600601c2c0000711003400300c0b64000180b80c82c0c2c0c107503a04c0309110310502160101803001194403241001c414109005002c1d035008090f01c44040c1d500580c84905036561140c403d603445091000142c0d1000100b519500c0d05c6a40202030098040d0b0040c010002100b0003030040ba4018a1580d002c3c1d6030306e14203219054106401120909881d03400102c80d80310584503140707079036840341d01401c100741c0d50f400c10840301d23074806842d14042070b00c1584000207803041c3c6020b13005201c4912081e00c0510030070141c1c400c004421b10045901038000401000104501c1c546040e031240c02412204001450b440965100200c07200300c2401d00c802e612003410484209a0300004546d40a080e0a05140a80c2000e90000e620f50042084281c400c6882640140d0b59001c968050801051210300856445141c0c0c0c0c1640060211441681072441d8003000707001c2035082002c00c031440254000cac80e11804040e203645002c810307003010300201c0400002d140c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 516874118 1250 516872868 516872899
    0x50d0e0106061e0801030b0f060103020c01050405070510030509030307030518030307030606090801180b060f0a0f05181b180405130b13030507081803150a050c04030f03030b 76
    0x2184401078900c03a6100c1c3d07141480328101d20344011000c2404410040c1c40c80040006c1001005000e0700b00070340c004000165114900120041d0107420300000455188c041400104400000c01c1e0b41260f07010b03141056a941d250300150211902228001400c0d0420000030f14110b10a17801980d100144000300300418144542040c9180c00072904140031a9452209005142c3c0003054507000700211002441403018600990482c20340000c0300138080d00494012810f030703903145a074a142070b00001e0980041d0316541d40441841030103521500d40594001048400041184000c8900c07070a40c034200048c140c0c580da491100642d2105624208030400c0f04a00c2c1744a0382d55000342c60041040c1040100d88041c0e03814031040c1400301404200303003d490104043c000070f41140c2035546250f003020303c4039120b17111102a51080403031001403580c540030b5101c0501807036008000050041d48400d104010b00c0d5181d40d154501d0f4440d40c04040d02015800d40c2000009100e900141812803000e0041c0c411200180b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 516875368 1250 516874118 516874121
    0x1d010203120403020327061c020d02070c0911072d060c0302131707140f030307050609010b190e090c040e0d031a06090d06020705061e09060103080a050d0e01 69
    0x944080f80160000030762802c1c0d90324400e0804210100c01820441007017170400019581d4454407041610141d0503160650307030354807142c0c156548448160401d55a6030000d18160044005078000c042e40309103001c544201c0300407100c055811042e84102e8a036072016151603808450f02c01500803080d900040c1c0200c500050450107031400306986601c025840b083c1c0d6611100070808075800c4100403810544001d440c0c5c0d000001c0c03003000c844d0000302c0d074a58503a04401041c4174020000009805120002d10b800c00c0010000c0d80502c907030f408a00800c00c094801c1d0400c00b44041070f0032007085000000c0740c01c0c010036809054090f0050822400c6498000f03a2001141c1680c50740b05580b44141c00444d05c1d49402e94142c0526041c06001d9038450030300d0410f000010b92103000b480e5000313002d40100c004079010007407968100e40480f900002202c0d10b505e0b0015556641c007145008072680c03144001e021404000d000074855042e03d600c08a070364207002e00b80b8004c9403140c101ea07911120460f111821944055403e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 516876618 1250 516875368 516875371
    0x702070519053a1113141f0b0a030b03070b040612020f030402060903210d0c03020309100c050c1f0f050f191112010e090a030e010302032e170a031d01020312 69
    0x424081115a5642c0106c95031440007020030145d40340342c4900346401c0b410b0b110650f09075207200019a80302e0b0514401240100410b1b44019010b00ca400c402042c9000c481019000700c03405503507620700c82400c006801c0140e001e024251141190705101040051407d000684000c0740060b0458048034441c6e6801d10300203040101417070120794009031070a4445200c0c0500d010201407418250324508100b48020b681e6901d060100100319651814a251030340300b441262010010181283c8412036800300030400c0100f4041807100541ca01903401c545840b160180a2080d506420450026030722a0036400f110071510400300c6249a850307040c108004550f030098230458840c44244c01c49507040603400c502e5201d003d81084200d6016a2a64002a52110452445000070729016880c5e44600360448880715141039201c104109200e071302950110307081c0c0c8403030403201c07000d80008070300342180b00c000c0d29408551009000a115900242c010180d681180340c5542410705c1141e28100a940d024640c0110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 516877868 1250 516876618 516876649
    0x501060f0e0d2d060e03121306020f130602010c08011202150c100912031b180e011737020a05060c161413050702070519053a11 56
    0x103c4024005010b5a0711a41e020100305d40c000314540341c01c000c003520802500400e9644080c07800c003119020011590141c5840300050580e4545402500c4000711101181e03000300c50040d0b103000850940c880c402d040350350407107148081110b121010754080c440300100c184041010203a003042103501d404000c000500b01b48503045000604d01e050b03450308003a5903480c0901780040500700301c0c401201d03440e00640a1506021410710340d0034404001100480e4003c190b200420b201c440400008540c03c0110303027500d05070346503401c1e180e0b0051a24145191803021b03202c2c50100c2c150803e26404c41e00c144c1c007428000300780000c080360016540e60001949a60208540d02c0c1c443d000442e143d07503042d950554140c080c0c0444100e54120019045c08a0810800110000e01c240d45440c0131036a0b6600034807508024050261848618491007a45070115171003500c55140a00380c441001d41901c0d03100040214008480510104440641c0040d81d803149000b400942e10355401c41c4080006585d003c900040448 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 516879118 1250 516877868 516877943
    0x29040906060e150901050711090c09180c03070507060b030601030825031706040b0a0e19061206020a18081c0201090b0a112b0501060f0e0d 61
    0x90901e00010000075066040500544044001442d10914001030f280044820700c0c046840712034a08282c0f44407600000303003e81006000d01030002c40c034500c50082c000171405a03403403103080c400030700200748107007046907002001030080c40440c040c14030882c0100403c0740589404030b01d22040b00c001a0078000283d00031140710100248421001000e0032007190100c1d08484408000f18103520301a140d840044402d0304500303844d40c0000c8840e516a400141042c0d005001240c6d03180c1c6a00d904070780e0030425950989a850300d2081100980800c2c00307124180c41000b0003100d011007540d034580000e500003c10680c1030041c4000c6074881d81c02000c2560000300740600081692184100c2d2500d129820b5a501c2021a4144070042020981c506c02954205040940003d1104100e90a801c0c1c3e600900b80c60764000b00d0241c241c3c0210b2072244051003c401350034941000280d98450041d10741c1700d40c41e00c000010940702d140040c0039142c49015040d00c2401200c0701d900b9004444884c00103035106000061020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 516880368 1250 516879118 516879131
    0x12070b0406110718050a1103090a0318050d020d030314040c090b0409030509100504090e0f0708031c02030601020703060f0903031109061803031b0f120f0301290409 72
    0x1c0d501581050030149030720060a942420200c501d91441c1d012055921095200c1010510780e50340b03a403001201c41c583c00c50030740d2a824100102e03521280064425000900c0f01024100c0e5013084d000c044044440080c01d0b2030300f548481e401e0080f0403842e50815410315a540c4100744040408000c0d441c480c074810200070700c2c483c0c100b05031503080700c9280b65503a00841c903141c84000001e401034122000810b0450fa03113034034a1850403007169144107642000c1c2045040c5681d00c3d983d210005094840410500180c1da0403d88880311a0740c0c0380604407800380e21184c40101c0c00341c42c0204d6401960803440610650340000e403262626000d6420007814540c450342c0c0c8203601e000b81641441155029207141650700c1ca03250381d40f000a400f9000c2c4880d4680d45030000c4550003001ea038100200c0b0107031841c14642d44003c4600c610381c1074540a14510000890040c8480b4108031600041100c0031080003540042c1141d0901411011110016003c101012580300c4100c424002c02c10191008009502001c5100c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 516881618 1250 516880368 516880379
    0xa2d08090120030a0e070b130905011205030a1b08120a0b030a032307020405040501020c071e060e0607050a060608120c06070509060f0403200105090901031112070b04 73
    0x3119600d4003000c1c05400401c101920004800c0c003100c0d000740c4c03039000100d803004070b601d182414131880340e10000c00c0c60000100446405805501642121504170b000c1219a03038503c800c01000c050002c008240750020440c0c1980f25008484600500c4541d40010901965a0342d51000c00c1c2e2211444907014000502007040b4801c4038064400010300690140c001480c0c0c0d030303801500312424445211181441c1c3e060282c1020180f4068441403074000f002480b0904090030018001e51051900340c44038002c1c1980800e48040b0228401c06004103241c001c991545081800c40c0c1e080d41c2050101e0f48800d00700490b1012032010007403030304401c0c09024002040c3c1c2c540140c40d80b80c84048030511148803020b0101e4030078140007080d400d920400a042440da21401c02000400a20840c828480c14120228010042c0707e88025800121400c1e808401408118a00155024018100120351000481006000061810303080c100c0c060000780c0030301910003644c2a41401c0062135000b9010588000c42c08210 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 516882868 1250 516881618 516881621
    0x31005041b060e101707050a1209080a0f1404051c0501090317100501080103200a031109010902090603060d0510060801140106140412110d0b04020f0306010501050a2d080901 76
    0x1450301c2e0345c241840c3d807070f407a0191407060020040100e000d0010208801501d18001c05180d80b0083e0040c6042020300d0365032400040c0c5801c200c0620380004d0703c50002c0c2c50b83e1805400b05208400a00c04640d0510785840c0030004440c542c8501810461038156403180041e90074003d078180070b4420380300d0441080c0d004008100342400100382c0d442c400b46a0f04100700d2a6006805141500d400c512113455071400366421452242c58900e01503082190703828000288420030740c000c0b41030f00782140e000780703981d0381d42720124243c4c06031b440340603030107403081010428510313100411000035413054040e0b40902e40c0030500700c0c0c02c66005030b0014200ba5141d22290f04040010101a405040141005d6820b9601c2003c0c5079100c0c00343d030103442c40f0707003510048403002d04ca00402c4003100710000404c100f52440c07a52910745001401aa012070054a02070005040b500d404182c20b07050320030607500c081c18401e0603c8200c82e40050303804a00c0c9410420300c51aa685000a10580701605007501c0d00c031414248100320a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 516884118 1250 516882868 516882889
    0x1914010627290108130c17070803030105010504090902033318060402011110020d0b040f060302060d0213120c061106160521071e030902031005041b060e 67
    0x9041d0a20600c042c0e02194a408490701c46442807a184030b4075500d411900140340043c3e00b000c2c0100d440a00001095103c02000540303449041068818480d562040c1e035507640020301a15010680900091141c80450f034020300141340010b048504410b4a100e18140060603503007124043c7c0d28a4014245034a0f0304909150040503d552200c40c0c3c0c500040e1140d00e451010384020704005000c040010715110400480e010341c3c0414008650b2402c0d1800b03100020007000f02c1c014041da04028080321041203038421a070440c1c0c6c014201e1481c01100c0f1746054000d51141802c004c0c1070011300004120019419034178007049101b001039403901c0381030160184c01d0300171802129a1a03440b690400910070071082e141c840040c0d81781003642d1550340d1941e01d1100003070300b4404000007402ca5410450016840030440214050f5207904084440184804405648007a0800394269100700c190f030401181c294070455016002e40380c0440c4500d404948403450826640c440800205102040301d40c0b40381c01a49072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 516885368 1250 516884118 516884141
    0x907051207030206030a02070302031e0a030c020a1208180f01050103021507053a1e02030f03060909010e0f2104080607030b030309040612060e1914010627 68
    0x1004002d203140d0000b043c83c07100911113010b0395000303d01481014020025140038045101080f01020306011444141c1e420044000000a0801100301242d5001142d1280c0702500802c14100080e441e401c00d641402e400b41078a9400d81c215401040001c10600c83c051410505100106441d455801007000166000c2042e1504a2080104200040e0009035420230701141083c01e9540040400c2c81440034100c81c825140c5241c3c0c1c8080214060303620968224809030961101418002d82240490350390295441c13044214404201144a5207450b50010760b0004c0024004510b01d00e5007a48941044000d10051805600a2180480160681107262000042440080d003001d00d01801550344200160200040c95951b10b6182000d407400d0040300c09495001d482440752583c2c82202301148462550140c1d1450302c0c0c600c1c079003200c074004500c076000300e00d6509200b40c40960507100c0e43e01041d184040c405c620b40d60788000144600600c1500030034104412041002c20700c200b1000000c0d50703814000c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 516886618 1250 516885368 516885373
    0x1e060a0b100f0c062d0c030209012012070305040609091e0b0406050301151a0405010f12021207081906030c0b07060603050a0609050d030902030c09070302090909070512 74
    0x100442580c04544244054001d1600d03541191140c24508000c0c00c5200345e0300c0a80d400300303441110841e881644014403a40c6024100104258004110704034003a20b560240040d40c03080e10100c800111400480b50301c80c1040c140e5900c4200850150915403200074118045480030404003c1650054205802828010030074802d43c0c0504160102010042c1018881360b0b907102055003d98603641c2c041400752402900802a00c1001191104103008610407800702044800a0004e003e0404043c0d03000c41d00f040e100ca415076051040103441444010040403504c0340c0c01d0040c5001281488000c0780110304645960200d41030808a8841e285a100d00c0d1041d801d0a044003000040e0b0110040c80443d00f60420307840e10b801e01450550064482980060075900c00e185480d028004154002c464052140c0d00704c8145c0300050900381c05403100140041e605400802c5218001d09040081607408040380ca40185090043c0000555000f0144d440700c503503921614050040342003000c5880b001d09102d000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 516887868 1250 516886618 516886639
    0x111b01021c0c05100e0c1c060e0a0803040c14030105092d1c031506120209120f0f06091501050f1507080702030d0c1e02031e060a0b 58
    0x41d41d12401100c035100c0303101090a800c81c680740300c0c0810b20702456101094503400340c05241181c014007800c00b040021409042050740c114a4940050400102242e440f00d556104645402000382003420010056006a860701d0000808441c001d5100d54032504c014011181005001505143c00a400501070380c90318040c408810800583c0f1b44d030404030b07006220180e40528401c6103903e2929aaa0109031180840c50410440850002501c182c255a020010101c81c0c0b5034490700842d1a20403000401c03000c80c5940e800d140306030002e01d244200a00340202c101c0b8031840c1203147c0b0310705041c03621242d003020743c2129034000c00744045500a01640f0080c01040c080c840304906011062007420301c00c1e108042140940d455a90582da08400305c000169110300d00d03824252416070080b20104d02c607011300043c440c096402804e00400240c7c0050f0756500f905000b419000030304e181d000342642d052050450b02d1130350a02145034030b403600c90400701502e03880c24450011010f6454560906104040042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 516889118 1250 516887868 516887923
    0x4030201061a09100909020f0405040e0a0206120a0b060403200402090f01120603050f0601090b010804080a03020c150c0a030e013c09030507020f0405012303030c01020a11 75
    0x160f6800e03910482d981d02c100c108034202075074407210580c0309403251400890181d12000c5440c0141c011204240e80502413070f010001080e17187c950481e4000d41c441c2d410b10044100208040600703038044410071001400040c2c0000250041c2c106900c1141c214403e5189410070314400301504040090554095040180c1c150000302445941d00d441410000c550105c0700d00d60940d03822160040d40c00c54140c0306030201044800b03440b26824021441c0050501840c0c074015481050366034400c507046070940382062206681100a03610810b641c80301c6100f5640d04007401000e01500314016403902e03020030f42e03e03401d0345800340c240c42035441508616458002c000c414048409408810101482a07840020303034049401c018240c000b2080104940c90040c20104154000300240080c60085030017854144803c401c1109841090241106160546561050084100140150342000141500d00704801c1c000e415017242c020100c003000042d03003200f41c2c0303000d01410703ca03a480c5070801810008900c543d90 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 516890368 1250 516889118 516889169
    0xd081803090a0b191701091a0a0303081e010305100b0d061109040f11030f0606120c120f06010e1c0b0a050402040b010c0b0c0901031b020d12181104060f0b030403020106 74
    0x140b040c7d51400b0b41741c16103681e1510103549102440080100208400c076140c1c10014040c1030211600542c400035803902d00d09600e03250a5990481c0da04c50001c004070015085048060481503031202e0f000559034100b50001611801100c0c074584101d1241034880c101101080291200f030483e103403030f40303190086011540340f4940403a0780c0b04001203001e12290721400d0114269200340000c058901d451078003803200304641000100310307646481140c1080ca80720b28020308190501039801c1e5000c9801d01c4070704180c600b003459000e0006210170101c80540140b03a21141c5882c4411176030241c295a49404210071031070148540b2074500801c1ca4032410780440c2e6611001c03c41d030702034455602e1480c0400c041e15a0380c826000144000040c400c10300c41c0c8149168080d5136030030f2482e21070012072001e0040b0780704145031f40300c1c620310b000c0f02c02c1100d8a0040d060f241c001aa52007103002942094a44101103030300d10030941c0c03a00007080303d07000c00c6030341e49050f040080c210344450f00103c0c00c5a101c10248004541034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 516891618 1250 516890368 516890371
    0xa091503110105040509011508070305010509041407080708070f08010b01090b22060c020909390d03021006080312061201140c04030506090d081803090a0b1917 70
    0x71101d00d00500c010100180c030a801140d03c02940090881c0011540707156895482203110030a4803500e031541c6a01c00300317905441090150a400001a000080105000204c07007105007040c04140c894458a50106600304011604000310a074040a401c0110b044145e28020050017248000c212110000303000030521030461041c040d85c00c10104610043c00c0c4e015241a00322803c0e003070404c10740d80d601e00e0060440e80c0140416442450384000040b01d40c0b03c041581c0041d540d082100e1620b21101e10342c00b00782d81c904904071402c0f40134512541585d5854651003000d0040c025002808158055090842699000d806c000360036001440540c1994070210f050540204044a04250300c0c00840c8080f8010f10100c08071001070a89001032242c0c040782c0d80b00034070540b4061015900d80f0350303680044a41d00c2c0141300140c40001c101c040012500302d0f00c03081020881c00b102c0c085e80c0c030345010380b400200080c2c21070f00100501c03800050604406414603141c0491009a41464071080480300704a81ca500d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 516892868 1250 516891618 516891623
    0x303020d081f060f120e0c04020d0603050d08101a1902191b0501050c03030c0a1b06020a08060d030e010e0324012907020d080405030f0c0a091503 64
    0x201a02140d4907150304030031480201842c10300c10a50583d101d40c010880c1c15a0b01c0480042406401c00c4420546207018021060701003c00501200740044180030007075001c0e03100c9010a66a814000c00010414881c4080d000c030660340c1d050a5003400c0c42640705022281c1c3c04a110340864501000c0707c0007404081e1242c8404190803080415142101a82071048910f00a8034860301d0030400720800180078100806103249800c2600307840c2d00c840040d40c0c83d1084030031b148416481400012210706500001b000f002c591072070040c590014004c92002403800a0303004907401500070070b0b83c90841b40c0c40300404d540143c6c110f40a66580c581c82e2800b520303c92410780e105040000c842070204c2562002c00c204030180e440c0001040e031005025080204490382030140c00819004400758000c480d001611000c190803810405615102c500c2d402c00a0203864070301b003294203040a000006940d9414803800640314101c1019000042c2840b08202c01c001807500700d042050b00c0d0001604e2011030036180c3c803041c0d030b5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 516894118 1250 516892868 516892877
    0x111b060304060e0d0201062607170a0203070305010519140402040906110a03020409063c0e090a0201020610060f03150b07050307050105130f0210030b0402030129040303020d 76
    0x4485040c0140500383c0e18850300090301c40c0042038624150b05501c0001200c900c0c40814012003441c2072880c50100c40350212031403135803010702d0034002c0d208d11840304110845610100c0c1c0c180c00942d4046801c000059100351441e1b590340040064903103140101207000705c11201d003080040020f400e103050359140500f004c1c2c0190395034a009010010541d0218a034805113041240d01c036500c0b07000040295001c0c0c091603100c242000000902902c000110300c40600c5902d070780c482c1010500500c4000b4105101586030300c000d40d5a40000c02078030f00380000740681c175100c029080d001034038000646007400c05000c840000f82c18580410030598095072290f001480da250104107200020700075031109400da0032000042d03200044c0141008400001800c00030b101d03c00030f00c820b60702d09911040300e045c1c6181c090301c85a07a16407124010314001d011800001d8007400c0014502c2e00c038901160803030308260040c0304555942d002d440c03141c80d06103442d1100c0d02c8904042d07501c1c0c40c1c2140d40c02525800c200c243c660601 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 516895368 1250 516894118 516894121
    0xa090c060e2e090e01051c050712141c020d0f03090b1e15030705060a260702010608030f041e0801140610170f0a090503040306020901111b0603 63
    0x740d60301050800c2080385030415005100094014030b00d510003110706540480c40145001807907904050481e812540003c1046071040d201b10b6420000910a0743e00301c2d010b02920b90b0101e03802215040812440340110300811642ca460302da200e190444c201005c1200c1d84a50b28008801580081d10400a655500d020b00108080f00016009003060081c000c00702e46521042045104245ca09003101ca0b01103844140b40d42c45c0c005d0b4029056000781509901900304070814090340c1082c800815021499142541c3c11000f801c00d0340601c403c4043d0140c600e145058140030170550309000f07640c003034900400918034140e1191524101d902c1148181d01c69201482141b10320000c4038154170b0001c108490007480416544ae10098180d2003ca495622458031940081d001030722608080e140c81c800c103100e0400c6500c80072851581c01600a103145521500e03045605c00082d0281b01810046101c2e941c00350b200c184090001d0000092104401d555a0094410411000d5114a20481c0240540b9581c1ea01e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 516896618 1250 516895368 516895397
    0x15120d0e040f0f14010f03080708032205100e01060506030a05060a12060905150405060a0509030d090c0801111c020705010908281d011808011e050a090c06 68
    0x82e00c0d40305000641c00f0b01d0302080300204030103a0050038110780b4400b114845030703880d08000c3c0054522400003809992007803004400007100400110341080e000e444600802a2410134946a04c41101e812107068012402c1c1c04886503070b5014001d15a111303030000740001c40c20080800c0d268000186240b803500c0d207840c0031807032a0300c65000701d1029200c050120b8911242a0134018007410443c0e004407185e12400704030f01c483c0d01c0074410217030085034000b0140055488101060000c0c5c00064041c071858002007103151102d40b4035220300d0724040d218261400300c0c68034200321103084803216107051460034020402621204002c020f589030304c8550050051f19601a81005401407207034640041c03e2480000328050340c0122000c08042d02e0f4094118001c0c201c1e030300c4d4001c0341d014400000241a9180030070304d041d1190701441d4413030903010111051080e05542c3d101c0407425250070154844540801da40075000025042c010715600c008040004c0c800e508080d43c44501c4c8448510030700b0104401d01c400c8520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 516897868 1250 516896618 516896621
    0x10801061d282d05010e010804170409060306051b0f07030203070215030109050901090203190f02041b090816030314391912020708070e15120d0e04 65
    0x41a500071100d4031605503c036107640c10f10403203c2c02e45030440e4000f40c080514810040c210030042e610180e488000320071080f00117451082002e48100c59542170386035032040c0007905001a100a04260b14046041440c5080c00c0302100d50103014030344000c410a1000c1c69801d80802154180001e11201554904a90130224154026140e00a41c0f0805407155480108035100141d816100407141c20041e50300c44012140c01c030740100c080250142c00c0942c02d0b20323000c60340d005185000f0f4010115100180700a5000608440010700085c0b10252502d4020300c4095000d0a104083d10070390b8000c1806403c00780440244c2d041501c03000313041040c0c0b00d045503c140001d4040e198072421420554000f80c0180d05280da486c0401040020700170b40c0c03180c0c0300031070100024490b0b0002d965060104200201c948450b2201c0c1d6102c07107584154401c070030000a00e19410001d0000030b20400c1c031922124105108c811144641c0d06403424881d00c42140710040311100400c06400c1c0c0960760400000940c04d1320701240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 516899118 1250 516897868 516897919
    0x607170f060d03121104030606120f060b01090e130303050c0301081b060d02191404052b0f03030506090112120f020709060e10080d0c031202090907020c010801061d 72
    0x3c4e242d04000310b22040c400018045c006076813003510300303010140d1103481400303882e481c0c102c000d050703155183c11007408281541e00c190141e40040c90003402550301c9400102d5240d109445444a841d441e0b18900141540f42c0f0a1603000030800008a20b9540341c460010740c0c0c0c00180500341c00c214180a1400490b079260000c4940800c0e80c00c9041d52a520944690140caa140140e80400324100ca003505d12119018000c443c00c3c0c0f000248610f5150400100c07070b007241d014445d80e40f610a10082c03034000c0032910703184402c0000d0340f107590003090703918085003070104405060380f1002c0d10201010f850030002d09032580701d00038140e103071422030012910450200d180220b5548004038161070605c001c215101c003030620302e1203040c1000613040061b665204031640c5c6c00a85405000180c200401600020300c140c0300d03c1c0350750b200480054206101c2600061040600361104000350f800754489d414156048030600e4014451400c10440301c2c041a1829020a9038442c0154812000b018241000341d0052680c1c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 516900368 1250 516899118 516899147
    0x10c020d0605060a030c03030521060d03080402041404051c0521060a030b01060f02060603070518070c05070e070e040c0e12030c060106050304020a0803190e0303070605090607170f060d03 82
    0x1842c1b00ca95a0070082c0541c0e00240da06008410700c4589800941214030100c0d02520024200c3d007024003683e2021141000c010f00100d0b40726807946c51400c210f020715078015002c2c0e40180d014001d034511425140301001d1300d03001c000c01401014400c0d8204c8860031114940c000d890000d204d211175684400240000038103805c001c1c2a90900c80000c203040d030f840a03130400b103808590211071050301c41508055560341f280c82010f41c044c00700300304400706999074841c064000c940b5082c10075501c3da003503444509181c116001400a1400340d401c105689a10a098000d1000103603000c12070100b40c42da005064000e19190ac9005a09141c000440c6010805c2122001d00a80c0180c5810b07586421000b0096802920103a100e42c00401010034078440c04421900e0b581481410359600030404038098401c2d140c0305250760b40c9070005104141c00705500303010744c038030403040400946201d242514014082900d103894602404480400300034800c450300d0301060f0007e6080b20851007035120352504030381801031002103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 516901618 1250 516900368 516900383
    0x100807090902180d03020c0a0609050d030e03031905090103061d04083007080106020d08010e040212010c020604061109010e12010b1c02010210110a2001021314010c020d0605060a03 79
    0x1300300130f0542c0440d0341205098200c030b89411403a81c80c201140c41100c28041d20358050040c0500b480080e004180c4000071000240c00e0300e0500303040d1900711000c20355000d40840810302c0003a0b0450551307414400c2c04041d00740c031545240b0b03840035080a280c049900900003060344270002803503990034215554000741a8220780300c40d055524050813150000304151500404582e2110010804a0000c10000643c140b03582e5031034816031a04480c0d6034440e00141040c0d030051103091040d02e99440c280a0b00310340900903001880c050419281c1401110901a4040320030b410900190301e050380d21100700c041e5180708540300942e80e0107a520b050700510384c52403666400100d901c001c001c0c1c029075011140c82d4034003d07000e43d4008100720002030141c940c410b1125040410400c52601002d0040000341202c00e81c0f500c40e480d02c451801d0300582207a00c81090040301d0054074a00700303c50800d0340c84441056200b1720341111100c40b140e002c200cc500c25074000a200c5901c5a0000308540c89107108100159040050f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 516902868 1250 516901618 516901639
    0x70e060408011508030901301112071107090f0b030d0c05010b06030105100507030c0606090902031606050a050f0720040b1801090e191110080709090218 67
    0x41d01402844a02c50201c0d0200d00c06200007000c0001209884036820107849210030100841004c008074201c14601c0110034200c008007030b000c070b50302e07206022450341c40d504a55a0b84002c035020380c01c0008000c2c511020001421171a84c0031031800304e41c0c4402c6400081c0042141140800306074090082000100c0d018803860a0034400039610001e0741403600e00900003044007038640814041688400d009041e0040040480e07501070920800c0181120341c00780c5421122418a907035007409460032a800300b18555115140f000a43c41e0030b0254030000500442e44091062810f00c010303120780542003d0400f8018089015980e80f1509801c8648081d8401c1d141e105514000440703005404040e5082d5000724a0041e40c1d0402d03050403d09000c03202e85c0052262402d83c40c0081c07072405480c13040e1080e04103018003450402c4042d030b02d202d292041486010000326000d41c0806018107280b0000140c41000410418844a250005148130988081c410090b0b581c0003201c014068090300d072401203420840e0481d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 516904118 1250 516902868 516902879
    0xd110708030d09150908041511010608070f0b0c070b0a051c060914092a150a02010509030a080a0903110a0303090203010b1203161b06090f060521070e0604 68
    0x20f02038208070f032041c0110200722140703020550450b03490450003045188108000e201c03814000541031802e04440c9850084102c13810f0b0101d0035a81150f000846682c0090001d109140d0030001e5180503010020340c26007401030303080381c0c1941d8500d98402d9800d0ba2500003542c6510031700c00c0342112000c001180010070180300c001041001083c146c850f01e9201483c1030140c85000e00d80300702c41401828090000d02c481c0380d200200004110441800100014040c180311019441c0c0300c040800f100e0005040985400c043c440190a543d0020f08920054000300316445446070800101a000a00e00c04001684420f80c60182d40c5242c616032003120038403400c0c101c18100341d0725401c0282c42c2d504c00d4000380a503400e048140300c4440b00d0320040c1030698000f40143c1c4240340303001d82d80070b9071240508440406610400705140603424190080d80000d0480142400340c285905800c5000b003055281040c50071490718401503001605040c0c01c48030115550128510300d2144141100d8034000518103542d8960f280c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 516905368 1250 516904118 516904121
    0x190c02180108010501090b030c0112021608090f0901031a0915151e06070308131a1e010b0403080c210406030b0901030b041502190e030f07080d110708030d 68
    0x91184240d81d42c01c21300046500350540c060f284801d0409402043c519070904019208080c03c519405100b1b07a0911103618010a040c2c0384400071401101d030283c1c0c0d4405030f4180603002d07501500e424085c20000004000051141c2e101c569410465080034009445540f201801e10301d02500c107450047c4a00f0600c00f10200e100803907580100304841d00301d22050001010003060741c3d507400407a4480014420600071130302915001d544001c4245a0011301c41140d55000340507800545440303105002e178000c0000c0d1070700b000e404d02d1560041c155071000c250300d003a14043c6584a180030090620380045520a034500c0200403058144680d05100c407040103990513580039a40040c410741001a0425200c44038905141d0130480c10303a9008000c0590581e17031034440f070401070004e01c007140e180c542c20002c142050701052241c0c407442009582e40200090300d4420140307400c80300802034000b6000500100429040021b01c845051042c0c10540d1160807960b41460400401b580410450700000400c0c00f0000d0304c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 516906474 1106 516905368 516905371
    0x140d050c041e2c0303010506090d050a0b010605190503010b0405010c08160305070b06040b090a0c02010b0d0819090803070807111306050103110906190c0218 69
    0x8200c01401141c2081801000000415141d644411a0600f0b0f5203114116000294210f50402000501d54170401c103544d0300c0b4074070222890007007280600c6510488c5800025110036503030740e07240181c4503600003105801407207059869000c8050090007900c3c1650050f041b4181401d0030107006480200303000105442c1e80340c050000200c080a140f80c0c0a02c500d109582e401d0f1508100c3c54601190790000d02800d12441c01e184c3e50b100320b078480d07a1440c0d60290b5a214045128103000f1000c1e4010320b07084003829003200c4000030500034841100300070120500b0aa040034060700201500311149441d45c02180020b402c1084202d01041c1c1150141480d28040c640e281c040604045c00100d002e419007880d04400307078441c1401c2005680601c5002001c1006261651a0440c802d0004030144a0340891055591000d0020382c0104d2180040b0448154040c0118845460000d88540700d03080 = true := by decide +kernel

theorem cover : BRFrame.Cov 516726618 516906474 := by
  have h0 := BRFrame.cov_init 516726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 516726618 ≤ n) (h2 : n < 516906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
