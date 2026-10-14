-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3128
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:01.01952+00:00
-- url     : https://prove2.me/submissions/154f6769-9b8e-4700-9463-c4168621b395

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 562410071 ≤ n < 562589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 562411321 1250 562410071 562410077
    0x9080111070302010b04051501110304051512130f170d0606021b01020c13020f04080303040c1a161202030f220618060507020423100609080309060304140d 68
    0x25070320600300a0b003910820b910b51409280f809040041002280c1c1c02a400311009180840c0d014102039403440c0356006907000203500030b034608161a80c011905005040c024088442c0032402c1e1f0760300c5620a901282018040c00035132404d1280c4000400444244000324088130b041400c0049083d88a02110526040000540e12441403904161a805000302aa0704240300610301c3c00000004a420107415a800e6480140c000c201207401c102c4040035503020b07000c8602129101e2034941070000003260f00c0d01c40d843c0320600084521100610110840791203c5507141110340c103403055a5110b0752892004090001c600003809441c12482c90780e0014082140700c03542d0441c0d0303590a00c0c0b003031a0070340a0b0751110044c00800401165046417042c82c103000c48070941000c41d03c40c1c19500215003e0101c9019102020040c2c10811481d0100050301900400700c07a0104620a502c0d410103680f06040303400390a0859009011328206840c008008680c49480765080c44000d1110040452400200748182d40c08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 562412571 1250 562411321 562411327
    0x6090709050c0c07090e010b130b0f0603060607030c0303110403030804050d021c08090c210f0303061305090c04110307030f0212010902070f12050c010518120a09080111 74
    0x3242203600038640c001c091107002c145001c039918405555806580f0440e0210354480c0380300c3e00100000e40c0030b1400d80d580640117045881280c40c001d00140039181881e4452000910140c07002c7c1001019280710722030107084546041c000c2e8506503621005030204500300f41c0c40d01400340c240408080500002e600c80d0300c4040c0b0350305040c070782182480c189904103001c42d4446c441c00c80380e9642c41c560f4800c01c9503040c102444540c5403134501604000d49412815040b41c850000e901c511000d1000600307101d050b034019904600c2c1c000d0050b40d10391006481ca0769001c0d59884010180b100307984c1c01507811020110449102c130442c8030103c1c09540b0302c500d504180150103c01c004c41d543d003600405440c29603201003103150640c0403051440081042c0100540181d000c80d0000402ca10381e0070004180340c020140e0441100c2c41075000b4180c1c0c1c00002002c51950820f070119440710300c00120854000030140c0030f891104034048000160390000705801c0100155030000085804080c80f80f40d2845c62440c001c5c3c1c2d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 562413821 1250 562412571 562412579
    0x304061d030c1507020c10030e0102040605090f011d101205070c02180408070803060f0a0902090a050a14121006080a0b010b0a0801090b04090501020309010c180b030c030403050c060907 81
    0x41066080c3d03c1c28071034144800200031244d07902064010240e40b04481900c0e104041000450050144d0740c2d450005600c0054045510380c2c20a01400785124111400b01c040341d22500115481d80500d0712155420803e5840c981e8140741c002101c1074100e2081c5032542107001c410862400b03840c01500c4440124100310115000e6050000114004481d04076000403d03003010340c1c40705410300c940c8401801e110030210201b4495600c151800100d40001030030305500c0e649030078005009500c1368041030f12808030444005110304140718080100c560040e88410302c401100c041c0100307440012844543c0340111b0101102c0c0c81481d100b0200940810790040000c8510703441e14015603501a0441801d41d1001c1c0701000046030700152945c15500c10203408aa40b403005000304014100024004011b54004800c00c02041d00c1540314002600300b60392003035000215800000380307400f81ca002d00784104c2010400035441d48c10031002907400c07038441d00c0c0407443e140a4019032400c10340e058035070700301c0c0b5009800204 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 562415071 1250 562413821 562413823
    0x504050d080708070503070903020d0308180a05030403020913150506091e0402120304081005091b060a0f140403030309150b01090e040f061b030f0504020607080304061d030c 76
    0xc525052410558010308110101814071400246100100f141c0080004c84080c03213040164000c5601a1007002030350750616003e018414111400066101d4a040c1c1401c0c507107000a0300795025030800050741c6458159001d010310740f07900070050140c14801c034881c24009035007103440d090710746480500012103042010412601e00c41c058001c1c13181c1c01840c09201d981d01d6200852641180d41168690380d20700060070b400e421350003561300c8010180104d6030031481070798481d004148108407000550380f503526404240e83c441c0340002d2060b5044030042c0f0006101d00d000701410403402c080340c01c1c0140304840c401084078aa0b40503800444c0040e440300440800c200c3c070850800d207201c200c040288099401e070300c00205040c0e43ca00c2030011b03010343c100128042c4205581d89004c080d410000600c850b42483c00c00260100c0e16104500c0000c0c60a070701245010010711419000c0c960081115140004a45903510780c0e400107001600c00c0e5a54007440c180e204e0700350314181d080c2c0d19021b000e1a1a14039402d005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 562416321 1250 562415071 562415083
    0xc24010503070b030105040e0a020910050306010503030c03030711120412050c01110c0d0f0c0608010611010911010503150d0b01050f060c06070804291819120e060409050405 76
    0x5020b0b0307106220522000c02c990b8140e0341500d10542e000500396100c40e580e00d281181c40c9030041d4100400e0300070301c50070b00305d140c03e0300060301c205804441c01079980c1c00500d5640e21070318489940582050011421241c40703988810040708590003181d1140351542d9804050741e01c9a4001c0c1e008011030100e50b800c003d0300340110f120310102400c0c10302d12076071103140c000c4d101c2050a0200d842880d030035880c0310805c10350642a14006800000c1c80f40c52503220040602821000c2c014800800c078018002d000007a014001c440c02c0540c00700441c07510b005034000658240d00050203d104c04a0074a40742d2640c1e494001c0c0c100200c1c1c1c0208042c40300e9503d000184204050a0408140124403c100380030b250f40d80022034507041282460143c1c01a903d90401103060551040000e008003810190403004824881d6002d01030390500c00440c643e03c030401c4425968018102c0c1c018240d40c4a4800c1c00b021549000403403045040d142000c035010b814420008902d40d20035008a00500c2c0e683c41804107000d01001b103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 562417571 1250 562416321 562416329
    0x60d0212121306030b010c02100311040902070b0c070f061a060304030e0a080304050603062b03050301091a010f0c020a0b040801051b070816080403020402120a0506011d01030509030c2401 82
    0x80041c005c00d000028020802081c02a0044070702e00f4102400c0c91195000c5017840950319401c03a141d90711054900c0180d408044184d0300b151010300417500003c0c04c1d1040360b05541e84146451086c0740560f80d8074020301038040801c003182f95100d03165030300c949544c0011442180301e40d42c0d03d216003085008201032607009400c2040107034424881400603803108411a504580c04032205035448400c60500b540c0000c0520b4110305a409074041c401c100340d0480c010318183d4103070710000d000f082c20040c2510b0480c400c080859000500030b10341d42d19518002c13129045828001380c46034000350f4949040500b65400355019100a030355a1003006949540440e121f0306254078440c200746461140c0c0c07038501c11401500084a042d4513800400300801010508840085502500540d00e603107024031215024102100c142c0201800d10001464540c4107800040c608180403480e44110301203200110010704005082c22218401008094852101004041c00c00c6180500c0c15010b02d440e0207040500c0041070348 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 562418821 1250 562417571 562417577
    0x10b091005060403031103040f030308090d140301030605060315090a23070506030c07020d06050103031808071e1d0118051003150221091b0603060d0212121306 70
    0x30050000750781c0c140498040345d0701442d08100c14038100e212241036104640c41482898900c2200008140c0c100c11001d2040e0440300a64591030510f203403e540406500c217685544007002c01c0180001000b543c849500a007019003114040b2020581182036882d050b03503004c3c4140c4c0301c1a10b2604019102100c1d215000004424444240b1008440c554620309030240511030a0044000b860b071a40b20303001e580c84590003c18410005115081c58401850f0a0205a00240c07e5602c552003041960020724221000c4400401d407040c90036403407403058124001e012003804144000015182030303145e91903d83d64602102e01c2c00d0340d45401c8030100100b064070f20340e020b403504013001c204000040c0306000b01103075085034000b0920070a09042e00020310a0a00186580071032510304580500c0c4075170101d100e05015801c807901c060103038200c000b14207400712402c0e80c070030010000101c5500b403085065120b83d1014150110480e40d54081c14242841c051505011000115503d449140c440e24200000c007200d00b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 562420071 1250 562418821 562418851
    0xc09060f17030d18060c0f03050606070506150d02090a240f15200a03020705030a020d06021602090a15090504120f0210150519270b06030702010b09 65
    0x3900340e460f406100d01400300305645044600000c2d0402c00c60340700242e444481000a210700e6040a0501d1120070440d10003c1e00c0d090001d140341c2020b00c100e9040503005001049269244d0210b2080401e50301100c5070021841c414480060321403440b103034081d00e0340d003002040d003052114200303101980341e2500c079000c200e11070030400c80851300341e03420810303512a2a5040c0a0301c815003015a0410f03130000d5891002a0340d04191651042d000c110507904130300c42c4d030076101516682e208240da280c51404019500c00c510100d000700103880b5900921859120080d94600800c180d000a020001d0840c1d0b8050100d8a4801a01018500d500c181014081c0c000701004107050980320080c00e0400100c0e17403421309c000050240043c1c0c0c000c00c0704004203543d100060091014404020409138020710901d4003a071140007ca030410108001e49600780c41c01c004848129150100200381c00300885101e00c4180741d41d4000e0008561940001140f01c2e00d030325000030500caa40e5206000010302d00425005a0b40b801d2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 562421321 1250 562420071 562420109
    0x191401080103120e01021507080603060a1a0f040609061814070909050402120106060528052a011103040b10060f050c07080703050105071706060f0706090c09060f 71
    0x1030110710f1000c1c918034000c00031a60040042c0e1514000c1005a844a0060010440110b6001c03540ca4400c0c4819020780d003090f00c80078140815240c400d4242c00b5078040003000c2c403206003050b840301000701c0402007021500176580e4003031804441d5960031070a10100c0c0c002e920200a0036a00401050248080c003002151034034a40c02400c210150040940781c0ba00c40c00454190f580380d440c4041038a86100080044a070b4074440a841a03000103ca00044030060051440081552200c1c00707002149403219442c00c04010300c00441850101d00104040c109040a42440d8000344915481c450310303002125a2400c003420101003055004001c40035900b202c403c113001e007a5020410002098071800d200f501e03070321001112814040c50382c1150441e44280c070f03800000d00c001500710a00501c15034450403491550071036020714424085400a802080400614619003051030003460f44a010b69000a04200c180d41c5a0041134166800005810b494103410302600044140d00300041c0544070480d00480c3c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 562422571 1250 562421321 562421333
    0x20a0b01050402090402130b0a1701030b0708060307080715121b0806030c1509040b01080411010c2a140301020915030703022a0c090112110f191401080103 68
    0x5020302801983c0105004649449940588004010603012503108070f88400e01c603d060b0700280044000500d00d20745070000851340074062410790b0f82001412170307541e86545041d0380c40c44008e80080d0709403180440000b041390b410310408010300510f10907110102c1d00044d00510346e242c905541140c251800d40c1c450740c0d020a810101c0d85e80071130b1342850201641d0700300001e401c0010135400d9503008003640840c0300000030000001c1039086010ac0b0f0812402090100440b0b0205044800508080307000410001540c01000c240308032500c1581c10011070000c188809442800c010050f02032110560414800003034500550401c000058000b1428a851500014242c0481c202d840400d0a400004903101510a4044075010086080c0320302d0070030322400341c042045540c40940c24940c00b80d4294004075242041c3d02d00c2c12034850b5200502d0790031441d11100722410040c491541d20051298094406c0c0d01d0729aa0313548403070001600003554a141150000b10103580c46801410000020018000201 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 562423821 1250 562422571 562422593
    0x315010f0203211f06021f18031701060816030b0d02041503060f1806022802010905010b062a120403151a030c28080601050907020a 58
    0x4424038003640c11400108080e402d40c490b804280d50503100401c4807005584074901c1180c003a41038241c25000001144118016008081c0540c90043e00940c030b8500490169a01110003840645400581945d000700d16007610003501c0c0b0102c01090741c02496240d0f10701c41402031070042155003001d041c1440c1038541510b004102d900c44d10281030b0f8640c1203400d142c4404c140c5c0c40300960701900030482c00d0000c0c3c02d507039007083c41071004440e000c0c10400009410b1b841030140d07001003501014200c50078015569a28040d40100c60000c42550ba00c0405480000000791003681c8092940c00000d1544501d0401e2400c3d10f07641109039016450800059125007500e44a40c501129222420000e00d200700f000b0074100b414009581c004002c022401005000e41704100110105080740200114103c80111501e60031040c90302540c1034100c03000d0800e05080c90000d084070055442720801480800007580c0040c8001a0041c80a503480a0010700903401c103084480d0b0852011f00040011200941c0c1d4080440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 562425071 1250 562423821 562423861
    0x30206011203030e030f04030215090108240301140901061a03010509040c0b0d0b0a08010b0f0907050d1d011433120a03090f05180c070b090715030203 66
    0xc41e140103a102814401e5000c0f6a00d040c0a0b401e0b640d481c884620031240b20f0700140002d03031040202848600b01c9617000d03030031542c0410b0182c5455230299107041c05405001050208030301900080140750010384e034203105045c41c00c60038880142560034814122400c540c1e5642042074122001066428049181c1045e281140d42c00c9461480543d10303450700e2584a400b681c810b000589004c80d44400001c92608000c20301c00042c0c4200b2240c540d130f0b1031181d00f6500081c64103038018003244c000c00024141803070910b074454803e0a00c01d14000f0310116945c22100f898103400c25589a41c0450400c48100380920840d8011300f01d0840c000c1d007802e8100f12009401e80c2c290307034a0740080100d404188005010900000c61000300404c1860503a030b01d03040d4640380e1182084000800b03016020407100c19107081c2100f81c50b8042d101c55442802480b002c600300c40c001e0b01c1003c030f1980c188446000981e80014076441000920701501c1860314040040012254011900080c1030060041212101c1c5c0c0b100304078441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 562426321 1250 562425071 562425089
    0x90306130303051807050f190807030201023c120d05040c0f03150207020102011b080405060f01140d11150406081e06090421050408100b0108010630060302030c0306010303020601 78
    0x14010440013a41225007800023181e24180300c00001a49500402d8a1080313034003e13006c2d22540c00315604801d0444030b40c01d40c6a807154242c01001d107040c504081da940d802500100844407407032004004450b4a811000001c008141c0304d208000c1004070580da0240100500410106014110f0fa600c00c182c02d0800c005000255000c24644156032003500b042c6501f40c000c200b003078400414035400901d440d07404c036030035240c0d4442c00010542215840e1103460490700509440c40301404031100304007230502e1441c010341e01556020100405d81d694404402ca0900d030240c40540e40d103140050142c0710039402031814201449001d400381313407035144d0320792a036111070120707800042a640c0d8640ba840c1c2e0721031401800b10f5402006000941e403034010000303001340e91480c4211078015045107942000d480c00c6072840380c0007900e5a001004080d00903e100d81d06c84c8601502104201b120520003140c0c4802118032140035901d4500820540c00d05001d0301a03a4070094001d06107c1d030450310043d5503404103110307040036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 562427571 1250 562426321 562426339
    0x61315050609040b0a09020619080615041802130602010c020d020a020603040209041a07091e290705160302181b0306040e07031109070503090d1409030613030305180705 74
    0xa174101e03488104202c0d4001d240310340b0380500e01c00c440c1424202d6030035603020480d05004643c113441c0c000d01e804010030f81000780502c0c1130b04050140e203050400e02451340140f9020b2010050f041c036480d20010142040b54000103064030b4803480203291450100c3c241e01076410800a2001503241d103021250f003c4e80544005da16500d49140c4140f00c0c0001441c0d1079000250b6005000d82c55501c01c0540046583c2405540085a80310500011000fa54420780f440001401e044c02c00c1c91000000c07000c10812580d000c107040ca556170301c0d5a07040809603a6120b070300541901e03042c011841c0840c654805000d491021075880e00e81410000c165550800c0c0c030214184d004400104140c0d100d0b000305c0d000581d0072007a01d51040d030300d1410120a2510304605031150303032440e00261005220341d042d01e11860301c60300140641505600151004030b046a604955013000304550041d07614100a06401030f0399050031078101072a41d040060490340083c2c941e0504441102140c6000e02002890030f05030b40040300e1406d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 562428821 1250 562427571 562427581
    0x1021b0609010c0518041e2a0e18070e03070305060a06090c0e040b1c1406010608100e060d06050717060f0307180608011820090106110f061315050609040b 68
    0x405012880b07c0d507003c242410141001c541d1240394146865114a0140070301e00c840c0c000544402c000301c01c42681000f0010800c00d042941d2070a8260407040d14205803185003100c2e000302e8142980360708150742e1a4000000d020500800d0700c0744000422103940c081040b00f00165005020300350358881c052040c0e03211519002c00b40c0d030319042c04c480071841986000559116192220360038628408a140314040e10000140550040340d000d0310074590034680003074580c1000d40f001c1c0300140281c502a0000d40ba10100c100058040c4102400b65106803181540c00d01901c984400c2e080000340301ca800b0304403180951000c3d44000851905846158041c00000043c480102d8020880c1d44c4c00190558284090280c07464007185010725103034000c6440c0341113180818a10521010b5080085400441c0d14004002151083d0895036203c00b40c00c0640d4040ca800303520322031601100359460b030910340380805d2441c20019140c01000144400303540600907868076000150270404002c00c0a0281c490141c0018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 562430071 1250 562428821 562428851
    0x31d0906210318130507050f0304050f0a03081807030309180207020406090209090a051e4b01030b0a050c070b011d0f06030c011101021b0609010c051804 67
    0xe0349400070710482c0e882e103092902c03c02e112800a110140580d60000e0000c54081060103400e00c900b460b9101c01d0b04c1c140d4040310406280d1700040040e92540100c0c1041d549044003840012034607402030f607818405003040a4070005441241d20001620b5004400c00c000103030b0881c0078078045501e82010514240034056032000a40309684000313502603d8014080f0300e00c5817070350281c201c0080688600060750b0712000c1c0c07402203c00554641003014494005030161890b074030003003640300c49081820f01c0d9280d41240380c080c00b10316920b4414008030340c0d2550150a00c0d0000003c1c00854039035155184a5455a200c0e040c1d03680d8085c03c0c0001c0d594031100010301501e050000c55601d01e500030346c014443e60b554610120400ea980c4890356070140c02d0030108aa600798801c145008010040142c51003100b0640196820580c01200c0c0d28155000d2040808441d40c0c1c0323211b841c640c0c0508000d8101c0b841d0502000c0d0845101e88178032018000184503804580c0001d40511200d1003007580c000a003030500c04080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 562431321 1250 562430071 562430119
    0xc01050d06080613050105010f0305150c0409090f1e030c1e080a051305041e05190e011e02190c03020a0b1f080708210702120a031d0906 60
    0x1121040c03150f48140841144603100401003540240e00801c43c50b41c0382d805004104440e44000b5041d0b5006001d506070508014840541020f10002010711341665a201c410540e50481c4041e00ca109078541c0c141d0030310901c0c1ea01d40d0f44802050801410165055070013034421451290040e01250342c4594800c1060400000d01a40702d811001c100c1d03c403407103544020810717848150440700c0c0d040c0d000300c002034500341070281c9903840402c82c214410b0303509002504c0009120040c00c0d03d04010076901d1201d012210792190400300490b44001051001044c1c2010300c00700014480003410910404c818000d1015204000c6803484079031411b0142030100e42006ca15110341e414000c2d000000d41014400364044107000052001c600b00080111a55201051038490b0740c1c510030503905030000400150301c030b09546a40d1200e12140043d00f41045880d401107800c140c1c254240c940c0e02e501400f03902040c103411032800380720140c50b45000d50800d0345400109540d4100070f0503c5000e0741e03590303400b40185500c801d51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 562432571 1250 562431321 562431329
    0x306020901020f06220512121602030406080c0904060314011410030209010e0702010b060d050610090608060112090c1d010b18100c020909060601090f080a080f0705030a0309060606030203090c01050d06 88
    0x2a4a4423030450703480704046e05d5010f50720302c1200754110712101915030010080e50104c5040e510b484004c0d55490703030101c0d11548040640c1da80540d0303400700840014507240da094100040300000040c46040d01c07030103142054024010f02000200e46204000607510400001d0640303541c0c142080e8030303440d010016030250100d0040b041e8840c10202d18000ca81d2660b5000074410f010071521074504060054080d100c00b0b01c0c0707004050001781c010b400104a54050840040c0c200c40282e80060403003040d85841c441d69100c0c2e04506040910a0705c8840428200b0300c01501610091514034600620003400d000303a000d440345103034010600280400d10b0180549a030022554002e443c0301443d14041c041d035512200202c800070301155405e9004500f0004691f1100c01360b840e00310003064200001d880d4440140c009071b85004011404000000018500f440588401015030b00e01148118003840d00b1000c0e503120b0380101041520501c20050500740016032001d04890a003040381c0d4825107880500080c3c00103400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 562433821 1250 562432571 562432603
    0x30203040e1e010501030203060901031b1d011e1410050903060a0903020d05070f141c0504090b0402121305070506120906061903060510050a0306020901020f062205 72
    0x80044851100180e45000c00c0301c200100050303071322240154200e01040c1c076110740051415005000040742041051a286040078021074140c0d0b40740451824110b1007014030700840403040041001309a4101d180488150b407010844441c0e04000101e440d485c4103a0003a1312076107080b401004840d0084080b11a00d180180030f8517447d18000307004c071016042c1c070700c0124014460760406e82c0c9007070b00c81c07c292500c0315032012a10550241c1600c3c1c9030303007e1880c40300250300307405180ca022030040c0752086e5841c10015262035142e15035190103100c204840300c40304251301950041000c01e49401b8075140341a4040c0c40e01c10010003c1e40310381801c0d407800c5402d0300525080f08002031700300700208603106540c0c8100d08210480303d09980b07420070303c41d900106401c22000301c2c600a00900c00034005401c002d900c2111344000c1001c60f44d5810000d401440907a02c19143d041c0d0002d2100311950f0b061004402d0101007100070310b26410070071881100c1031024000ca6540c0c0201510007000c00c80f062100350440d83d0050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 562435071 1250 562433821 562433849
    0x2d01090b040b07031826100513111f0809070816031403070f08071505100602150c03070c1a04080306030d020c060a0c051f0e0d091203050703020304 65
    0x81040c0899801400d00340d000c00c2911000300e00129074030740c0c04006e0322803c00c0744132a9141050404c003030840c401201d072140b40c000e10006c01d80002c010302c5018403481d004081c5854240700c40c01c0074081040903881b454060a0400d1400b00c0d10962040020001c00d074519240390740e42e941500d070f039060500c10740205245000302e0911165162102c02c1d40800e80f0f000d0300c103400d080300046050305d99910940d100200603000035422100070800a1002d000727658082c0150018103070b0600501c0b0111a4103c840b49142c0040310418404664100b040310100400c008511105040c4045180517a000040c110410002015501010481c20b00310a0310144101d03050145641007a00d0100d03050380088031624064451968032486243c40041c22075420310004e803c403032400c01c204004032114201c204e030030341b028814041407800c60800042c0003c0c220183c04000a41d01c92000c03182424030440348252010054100c40501c84400c0e10308410a1681c1c6c1400c003280e94282c0c0f807800b80d0960141c1c1c0e11441194801d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 562436321 1250 562435071 562435079
    0x20c040903120b010903020906010302070f0c0803041a0a08010b0903030408012a0f0509130209060304050a0c0609080c060a020c03030304080a0306060314060904060e0d050d0b2d01090b04 82
    0x100c600d002110182002c1031203485840300044a03404442c0c40060f50140c80403010900d0342d4020750081040c80c0c080d0038000d2480d44951205800c0d040c071a070201480d5400054100841c82099280c18104038401345c2e40c529003007001344014981c0c10306015182c11000c00003040003c3c1d5800700300322402050048001c0c04602d004102e00b480c0b10450091004134403000c400d815101600c10700784554211083d480349401c0c1850002844200c9407888146004079038200078810190741c40c1000b4510491040c402010040050701d01080314118551000051029100c0240800380c000301d140c2c10b6519007560103d40315100c001c3c04038074104074441c29641501002080c407003441540c00040c40114400e440502116a460404400710b4529030500000030200070302150701d518000d080700c0d42041c0148c0c0042800c0110b400110308141144c3c1c1103101081e400210003c214919001c0e6920f0071104545000c20448070080310310000c0c503108820041200c6504c860006d503800f1360200e5010b09022680f039904c40340c50b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 562437571 1250 562436321 562436327
    0x106030507080c2202161a0403120c02030a03150e0c030a150b0415120213051804030816260a0e060123010e04140609161d01020c040903 60
    0x810b00960b50240191200000207080c04400b075500e40c59650020148071204e280d0000003504031400415143c4038204214001c102420461602c003617400c03140b000c840c03c10b8030740074000300b4030f800b81000c0705810190745001043c6c000c0b040e0b848007080c1b03007004071703009004000c802c005050070f80242c00d10400103003d00c110305500b40003442c030a580f203800030003034607280010020722040c039889141a083c0041100340881a07010b00d01180511003800d01d00b4108843c41c0300303030081c2d07084840001c581080280040226240c100d400d0030070080346c0b807038081c0e00c0e0805480007460814014110304000071940380c4d69600500c140703a20300114040b001403c9a583e45180d101180c1e40003a0754402515050030f0440300150b1340421000e048a120300c012585103940c2541c0f6207001c031001842c03581880001c40030f10500f51564081c1030020600c1c1d001308126480c4c61420080e90840182c0380d00d60140c04c03041a940c0d126042034900024070700442010000703001100040b85010f005200503900b2034200001d5004040e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 562438821 1250 562437571 562437583
    0x40b180d0b160c0f020f04020c010501080105090c010c08040902070f241a032a0d06060312020714130e030c100b060f12060d1707110f0d02040b040e01060305 69
    0x520282a8180600007041100e2000401c0070140c020003009048000603d41000b2405079543e01607c00350403c00150b0880782107079070076481005140d4449013000142402400f43c10f016050908203041d00416136102c0960a0103540034440c5100d41c0004e40c070007400080040c10034500e5000900712a83c8468032010002d80c040d895181100c0c80c01e10000c2e4500c1600000343d9500000c0c05401003103008141d0f40561561520b680107044101101d07001d0000e103481d40700510409074050b60010505510354070701039404940c10424401190082101409040006241843c8901049840b40701d101e200140844c0240011842024603200014040268030004580007262101901c801c00c8103600e801d040c0401031049030032140303940c503040003821088141d4080312500404041d0081c1c1040300c42e507031142101400814052407800c1d000c9006020800960250950b0107000e441c0102c2c401031800120b9054403410600a208644030003208000361030b241e1012180741243c0c4000e0280d0365036410481d841380 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 562440071 1250 562438821 562438831
    0xc0905100918060609230103150f030302070312030203061c02132306040c0e0103230403200a0f03050306040902060d1e0b180405070f030303021b0d05040b180d0b 71
    0x140d5451070015880798480094814214036492070041b481500e00118003e22280c0c0ba82c0c1c214864441010818280040242c405035109800500d216415401c01c3c0e101c0703d05400940c0d0802d03004000304035680d101c0050710441e20f05132100d146102951031001410450b01c0300f81415989142c1508a80300c191401c0c03002101900084e034896040d190081481b0541d441501c81c14040303000d090591006511030362190034407842e003040c0b48481b81240c40c6a0104000241d40a6000070291030110950340d400178400c1e40b144c40c03c02c004001001256660508480c50840042e003030010100000b0155110307500040700141e0700070422640ca40318507030050000c20015100030841045000c6098040c07525103c2d00c0100382000b0b100148074030f00c1d008954841d01d03008000b01c50034040e03000e000601c4c2050108104c00f80d8420b031000340e160305a2035614500d40d440c10048038072582c4014180c10160350403204840c1039882c0f000f0703c0eaa440d004003048031045d9075494160ba410070b80c5a20324105010861212900417 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 562441321 1250 562440071 562440077
    0x2a231507120e060603031e090306010b0703081f1203020102090d050d0f020a0209011a160b1806070f140c030408010203061504031a040f0203010f0b0a090c09051009180606 75
    0xa9042c940c440e503c203800c5603441d40582c410014140602c0400118070000224201c5140c0360400030700100703040010a070712151440d040444d4101c00c054100003c1988540b041c05846004043c07100d04584c210043d200350200ca40b03c520305001498400e40464905110182ca512070610003858a15036802c1085005400500c5944240802c28030225080219940042c0081496420f000c00c0c0c00c5a07007503040c0e400515500400460303402d01040a5628041800340c49000c986180401a102a0b07035580c1e15101d107950440c1041012141c0c11590220b15680145030003115121045050300780d80c890103411502ca407002140002d09508150002c40c420341003034658a4818498005c0c6050358050390000070005810303141c061100166801446038068020949070403a610290042401c43e0600f015013034046031600399442090501c464081c0041c07801e070200300316041401000514460060103100c0c480d40d0707030356800045d451107031031080061b103400304409040c7e401c2d0300144e10041045102c0c01000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 562442571 1250 562441321 562441331
    0xc0e1e030f0c062205101d0603060306040b040303241409061005070507050607050d02010c05091003180c08060f01060201060b0d1508010204062a23150712 68
    0x1140002149a0800b03203005444142013000307a0300840d003400700c0713881c000c0c00910500c100044c0690712810300d10003440e03c0380c51b09420012910340024501c6c0c0307070411550040c2c000b08140702560303c002911a912540010004540b42c5442c82c01710b01400e04c0c01e111100605092000c00010086003401400f203400318007209611081d421700b070000c1500300325070140d4801d07140070240300303114001c80c0200319240c800c1090316910703510f5400064050b0080e400c00c0d01e80d503003e00310b6000416024070070094284c207d401c2403420114820700086c04036103000c4048081640b00d0400c0140003014084140016038041600720031f164446440b47d644840032980c110135040000700004d442c50041c81044190f0f003245c50110314000040c032042c806041050100c0c0c540340142100000d01c0c680c03e1000e080503290513900c26840000d165003480401038102403002d0086901c490640004802c00c0e07083c1d0740401d1182e0002006c2100804840c10b28011000a40740d80380300b4420462150307400203020611010310142040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 562443821 1250 562442571 562442593
    0x6080d080603010c050910030b030a0303020d0b03120f0705150a0207030216030f03080c19030b04061403100e0307061b17041208090a02040e01050a0b06030c0406030c0e1e03 76
    0x300781c40480004d0b1003c1482009010301d642001480c50811204909000c91400f82c000b01080c508211000260300080d80803d103100d01c11a580110440c50000310010000481707a051240396a1040e9030589407440310028050301000381c1480b4942c0444140c69142d2018500103081202a6122130300c11001070007089409802c3c1000e0341b42c1141500c0d0032220304281229a0b65064500b02c00c003401491440c1c0003030008104a4009034001c0002c030005540c082800468002400140c030041e40040300c1c8665883c40c03582c15030700c00040103c19030750248000308a001c800c0381c0141c107511407244064a450b08141c0d565240c588200d50150740d41e603c03642c034245807202841e8000010f01003030358011700c012308000c4503e010350301c0f03140d072582c001c440401aa000311800d980000c049861003895508903944500401462080c54032a03c45160020b80e0028134515007255141028400e0b8001d00c0241980d40c26a508510300c04c10595001e89000782c10821554102807801903840d09161425100b4419042046 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 562445071 1250 562443821 562443823
    0x906081c0804061524120e0c09040602090a0f08060a02030f040308070e030f1506040e070b07061b08041106090a18020c03030709031b060c030e040f06080d080603 71
    0x10919050340d54a41e0556116640c03054090300c00d40c60803004d241074000d40414014410750305503010103048103581041c01854a8041d000040183d01214a00c0c44c111419030100e00220ba07c0b14181c0c0d007141c1710046070f0744c0c5280c03000084c040d070300310a50803c1c41110f010490b81c807103819030000d9490903011100d60359201c1001801b83d12040303500e207454130304034008500024019491070b5000030301c03418200950005440401c1c40c0001e111807030b00299114a08809203209800304050700070000303640a00c41c42c060300c2c2b1441d80e2940c1030b2040b014103101c0040d403c2c2c00d101c0a50300c540d03252460200711080110308031800030513502050b10b0640d0003d0202004a0303440c50b00c0000c031040020041e0440c03541514110701c2019405601e48100e170140d408000b41d001c19001400194030521864540f1380c409411410b05082601d1598420042020354240a008050300400905005a4540b07402c0c04000140c1000c42c014117455070215025605081d40030030000381c041a07040c01e940c040d6070707054034695503a0201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 562446321 1250 562445071 562445113
    0x11206060b03190b180901061d100b18030a030804050c04060302030606101710030507080a05060a050910090b0601120218010e2d0108183004090608 65
    0x2542e0f110342d603404000c3d1101d070840071130781c0802003100c0b200d00300c132400204050204540340c0c855a5946c220a011a580e101c0c0e03a20307204c04248600807010711b01205403140c0038440b8003c140c041c1c003000c1164411025071240180c0c0b032640103000d4030043c504d54600901104801d8804490500a85441d9515410b00380b041a04580c0c00400821254035800700707100100f8801450b0f4402c210020052481820b81001c01c94081c050560500045510f141400c6062510700c1d0030900c5507801041110000c071301d0028029401001c0064006260303120014454a009000c3d82d03900d40c8142046111000e002081440502c07940c0c003230702d49e901040e1151901c00100e101d0801102c1c8482d000f040c41d402075511520801440020241c044000d480b04140c609082000e0241e0305c02c254010704148003647e50f03011554982014000f00e0400d60400c002d01b03a262038225200c0d040c01c2030349400840d0140211402a00030356851810b100681c0d441c0ca41c00b101c07014080501a400c2c1e40c1c1315030482c1c960114008041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 562447571 1250 562446321 562446331
    0xc06050c090a05060f070c03110102070b0310031e02030d020105090105160c0609020a0f0e04031e4a0f060702010507170f0406020105060f011416080c0303011206060b03 74
    0x2c00050a00b4401040303081e030814005520240070601021002880608400d000381d400faa00d4154501000e030002440d0201a402c6020390000a100f80850f07200c141d0800c10641c0c5d40044442069801c80001c1040480c1d140c4000e0f505110750006032034130716019407296000c0c0f8003040003444240c0d6a07240c640c00c00340070701003c0f100007191030032000c0100340d02e548030602e81d078401000840041c0e41d811440700d07045441d4014048100d100c505200030550040614200044240701d0410f42402016014082808034070f04c248104a582c00304400f03440e0804100703801c2c841016050b60000450300001854984441e1040d40078210240c0440501d2600606441c1d40f5070b030503540c0030314124982d079803c50320041d0306110b01c001d40740c203100c000612929200030b040034003800e030f000143e18a002c2e07041000f0340c8002c511140c1441000401540b08410000440e01d0b42507441000a082c01c81c0d5280c9112903210b0320600c2c3c044c60102100114801c450001e1105045028201c240702045e110283e02c1018030042e11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 562448821 1250 562447571 562447579
    0xb0301200d110c030a1808030c1c140a1b08030a0c0806030307050601060c050a050604240c05030106030e0a02030d1107081c0e040e070b0418051924060c06050c09 71
    0x219001700d104511040030014410b6030052070b40c0d620580145550400e0790708510542001510080400c503c0b204000040c0071381ca000910803808196103011440b400e54144d080006110b461064102245c1100c1601d42c0d10209040d500d2800c1d10f4040018000d02c04844009255200410382901d800819960469002405803c20364030b0250191100102c1307110413500c60250701040b401040051000304d1150313008242c0b0703412602e00c0300102100d940361070101c0f0041a2400010034200d5502c0303000d580c1590000e04001035a035504144051030204052402503152241091318a17405074000d071a0034801d1882002c80c1c207196203681460f5220384090041d41c0b002c000880104074001e1242001c26560b01019100240242c0710304090ba0510b03c0c50340001600c4d0300d000600b0850441005a00c100c6420081c404129508000c62044031452420700921a030646810740813125050b50b03540701220849110340e54902ca40c3c0c1d03074406010b44c202407609942c0e1510b8400010080d644441c121039158000070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 562450071 1250 562448821 562448827
    0x6060f0324060102120d1b050c070303030507140f1e0a08060904210810060207060c0609060b1c03020c040c080a050c090301020f0405040b0d02060d0b0301200d110c03 73
    0x100250909040040480c3d0452040c203010100d02e01e550002003070004043c03440441c0f1030f41c6c03540c2d1171500e00c1008110703e010444201b101c49030200010a6140c142ca925140c085455144c58000710b50b600c90540a050b00319000040030841d0003601340040c04045640800e85003215000c0010100030f000780860390011401044c0002d05524052460a5000f407040217140002079003683c2d84c0f03a0100e095100e44011800d000c003400324510301c00700d01600402081c4028880107007010b100030944000300000511064442e420002084150b801c981c50020b000341413079010001d06a9a841d230150b0100081e0054010352030fa010350b03414180a801403454039130b21004159102c0d240048002c3c03500030010f0a1411040c440c91007540c2e428001040c061160082e80d5494505110070001150031961101e48a8000006400016282c600551340c000d2012080003500048507004a0b024207515134112540040c0700d00800d22034403a0801030026400c83d00002c06c0766403580d0300e60304d00500c581a00103849034028 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 562451321 1250 562450071 562450123
    0x3040303080a110406020109110a15030504020d0b132109030308040302071a130806090d0f050403060921080603060c070609021c030f020703030e0405060612010806060f03 75
    0x602031150410407103000083c140d25155446000c0344c01a030001d900607516801090180802401c0807542d1890468590324003e160102040c04188098001020715450701e00003425541d402c00d03440c05031500505403042c64038100e18a056070f40d107041b00481e020307001e125242c500170750520901c01160b641a22040e01c02d60031520b00391006080280101d003144140303640410006041034141c00d04203e10045e858071511581000078403c00281c00008442c0e01107010030840d5400040c014126200c681000420b450384104111010302c41c0d80c2014140b00c0c00d0561400c100080201c1018404883c5070404200700708400040300d1544044e20955819401440401d107043c0240c00100551413141c040003484200c160302080340c10100d0080d00080d012817200d0720080c10703000b6601c0314801829101130178085040d51f40c0940455449424603014690322400510140c8411081740ca11426490440015694030b400456969000f01d81c0a0300a019080321072032941400907005c0c080224011140d50700713100c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 562452571 1250 562451321 562451327
    0x306010f06081519090515030a110607020a15022113031b08060c09030d08010b0f0d0204080f0a050d0f0504030b0702010219030c08070c0b18031e041404090503040303 73
    0x42240e06901c048810b13000150301c40c40801100041c03000fa8004201443e203500545000d0b0690040c1f00e000390492032040000407218426000788860803141c69449041a001080c01c59060b9006a2030b041440e41400c0000c40e00010407104800307200c0140300108190400075001801641c02401003691072203030134000a80311104101c00f080c004210700429035030301c0030101d2030a030b02030741c01c000310090005041141c0d007003e001880d11074000b03090404540d49004000007107031082c4203072003000110104032140c0c0380240750112001400144121075a0380407520640e9103444410400325414420032003100f030400d0048192035490300164841a040a185440d9484055030003016481103550810900d00010b017445034040d0615240d681c002204050340d076000e4210074024244038140030000341044001807900400301c0e40102c0091100c0d0081b8401c15a080c910301440e460000d0100070340c42003081121011000e0000c0341d680f000b0010120000c242407100701c62525070082c100c1c0e041000284003182c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 562453821 1250 562452571 562452601
    0x3020c010e01050f1206090a05010b031803040306110c010c0305012108120118050912070f030c02100302070b0f04030e060a0e1c030e0f09130c0b0f04050306010f0608 73
    0x181001c614040f01800002c1140d404086815038017240e8406000a60415419283d446054407030104015410070f4141c80003801b000700b9150000600c5210090029018800d8034015684114240402c00803e058040940c01c501040c901640c40c143c031038425a4824018581240d0300c0c0e1444180380c40500c150142460705491381555101001c0040d4000304d6210607156000f132040d40850382c10b00101e03518100a03954082d00405644d403200703031891800c1140000326010340303a00c0f101c40c21002c200c0d1b29081e41c2e00c200e00800658002124404291b640390140c00a10032039104400e000b10f036035a550b002d140303400b50603540a000035098a40003212402e064004146040c500e04040a2140300d4400140407102d10b803003003080c811a00803082d01059000818104c038a0001c494215503060310102041d28920020568040d91450b40080c0040c0600e40d41c0c440080c001084541c0c1d600e4400140300c2c4030b41e500910440340203208100c0001081104800481e00360303145560394100f26100e10b0030218000c3e07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 562455071 1250 562453821 562453847
    0x7050918220b150102031c0c0210050702120702030c1002010b10230c120415120207021513051206010e09070e04110a09090312110c0303010b0304051e0a02090703020703020c01 77
    0x80300c10400078042c01400ca5108039607d191620200f5a0740e0320090082c1840c01c01c440c402000d80c100ba0a010302150003040103244840d806041c140c9a01585c0002898007013541074079a00311901c1181130300100d6042d0844007201d0010b0b030307181920004070070044562b00b5800081c020505448001351900a074110020014407400800302c07242c029135003400c6841c945c410f07400184884c8284000c0340101341c1065007408100303046081141441c480d5008070b4610745100009000a82001841e0119010000b100001030140582744000d14620014180c2d81d0301000c0c010001560081000504803240025401c02a18007a6841078001d03111590740b482c2c2010342c1c8a68540c420480b035000b0420444e244031320034010740265140e20601e414041000100e94031085600303030403681000505411400042203a0465034840c8640395250355908005090000340800d408c03245401448051540c0b01c00116001c0240c0200d880b51216114a00b06500700c0c0703c0c0100c020302503000702c4c0254001c0d6001c0c1d18122501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 562456321 1250 562455071 562455073
    0x15052403100c090e090a050607090b1c0f0f1a0607030f051e0a02010c08090d0207030233030726060d0c0302060f0c010f0212040b07050918220b150102 66
    0x807a190303d0441d405900840340c2101c02d1b40505d185000340b000820206800002c40c0c24500c540900703240f406c801c00d20500b400d242001c1440ca141c1c040021b165030010f043c9204000b0300b00100518139114101030310901841140a041d0446550f5180c40c00e5021a0b1044d84d040d111501482c10a0105030f503290424002c4d64500c0c0c0000c40140400c4c2650002442c00911700d9000041d10180b003040034000f0310005e810300c00746a10818003985555000120394081e80e404458004140e1410710203103184020b541e07400c030800da940b485803690321840f81c0d014500580e40c0e80c40c0c110182a60440c60a642c4080345107081c1c50001c1c6101260107410000102d5403924016400c07000c00c0340c1c40f80c02013082640440744180300b480000412050415081c800e801040000040642ca8880c58030100b03490307000b018102030b00d4078803d00049420940038404540703854030007811003d0460320321a0118400705040740e04100d8034a000501030540046a007040c560075034030081e10100c03a01c40260301046130009104282c19 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 562457571 1250 562456321 562456337
    0x15070512090c2e03090201080604150906090204060906080717090f011d1603020a0b1b0a0302150106030203040f030f0c14010b0111030c070e060d15052403100c 70
    0x4103840c2c6115042e02200307903d180000300c038084400c1a0f4501c10003000041058503141034140142e900506080e08048122000304400aa12265000b4480c21741d00c01c0c0030136442c0c214006200201c07900544111021a1503c0428070354541d0296000a0100e80b80c40c0000c00519054801c03000311600290044551000c80740c25000d16501e550840e14149800d200550f1301280c9000701c44400c016600d50b1100076420485058659070121f448818503010b0380406e24404030700c8000490514110307540e010111811240380412505000e500c82ca41c2e07407580314024811800104159001e402243d0145074410021071118019450840d10000390710f9820703041100d00c000d201d01092444d000805040040c40001034140d40080001d005038681c09031042c180d800501c01c20002280c0420524111b40384840130030100d550710000a1011281703c8c0700204040700b20710010f03400c44110342c40030388140320400480000818540c041c80c0d28400c10181c40341d1560100340000117500c0c89070091901e41526081c0116 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 562458821 1250 562457571 562457593
    0x806010f21020d03090e0c090105190315030609050c090606071101050d020d060806060f10030c140301170c1f05070609050a03050304030f03060e0c0913050c0403051507051209 77
    0xb100340081c0d02c054000605e0048280304500c6a62003807900201c0107140c49161130800000a00107000341d689418a0110000660401c10300a410544a2445804c1c0d205030003034036440d011000300380c4e840e400e0b6050322442d8210000e1782005c1700c44501940c00100341d14141966595001600100c0200b0181008010300994660125a001408491070f0101010404d2802c0c03840d15458010000d00580c0700348401e003500c480588680c10402d000301070514000c0764a03c000309081d281441503500b00308604400100003c5c10700c107905d8060200103000f0060f525000561402c2003040103040454440c000c031240084801140200000c04145105007000702d04c8110548589081040400c41540414400410801055803201000b6030350011410100112800e000300040799103402840d600c40c01c480080c506c0b032030f5a603441c982504014141010300c04ca107048100800580c110b40310860301d40c840d41540c05081150600030034480d51982d41d4080c24140f02e1006944040ca024290710031501541141c86 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 562460071 1250 562458821 562458829
    0x1091707031713050c0405010303090b070c03080f090306091f0e100f02071203051005120a050f07150815191d04030909051303080601020c0901120b010806010f2102 72
    0x600c2074003c0508214103164a0501c0c17030800e1664072a42d40b1941c0341c04014030001b83c02000d03101c19265103140c0d0b5600c0300400e02c0c2c922000c0c4003a400242100001280c0d04506034045401010700b14410b40a03a407094503040110786d80c03009010700e4411841195001620600e2450744080f0b850507060084803070001c0300181174003c803a8482c20300b804541e00000c80c901801025451302d10205500d1804201510303061207100700841490285901c50074540c2011041500100b10740328032142c0140580d81244070304030803660741c0c81d400d01c22039000f46000d500d803440d101c0c002d2140350301c103441369104820010400020030501400388400c6148480304e508001c038041010046400007800300c81c10060141c14507040207480040d05600001c8070605003805c2080c0c44010b91140c1c03449a9050030283c030181c943c0c00060741050b1508a9554103e0007117400021a09a042c50000c0e00074090700085007140d894404c810303100c1c0801d000740010408500d504000480c0030394600f03480e4401412110f48031000950000b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 562461321 1250 562460071 562460117
    0x30702071a1923090a170601080106051e040b060c0304031b09270606050414040b070e03070308070f1403030a1514010804050c04060b0315030109170703 67
    0x24041280300407070002101450400300009801071403c200b0000c0844881803a41c10180c018881019031001c1891a0385882c0c00c604070707002d8128540803d0b90380107805035940e41c82e00c091160890a600744840003440d801c00c042540704100e50007902c4c0c03180001850501010b00782c0e8a0b09190450010444154940001d00140c030103944544800c02010030f9541c01c004076500b030b64100c005114a4810300440301a0040422880340c203004001090200c0300d400d000d401400154051608582001c402d40180d819503400b5134480c80c032030501800c2c5511200400c550350714000781100e406500000341070000c503800d9000b4081e91480b9581c9065110282d40c1da2180c01c0340b28802c02d40c1c00da4004030074409141010700072608040c0603a101c600c00186011072060f500c2d0070a00c0742e58140700c2614049000e0060500001480c6d40018006000183c0c0d14001064954400c550101c01d9020b8800d1880c910b18040c007807080d0ba240c1180003501540ca54002c44441c030b42c00050304605000c569005130310000090204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 562462571 1250 562461321 562461359
    0xf031305030c1b0910090c111609180804060c0f05070e1828020f0603040503130b04080601210c0305030a02070801020313081608070602090a091803030203070207 71
    0x6048005080f200350070040e440703103210a10444941c802c100341c042521020400b00d4442100101e620300390040140c40c0d0200c4c04102c1012405058408041e858210550f21701f121a40e242c2000030040078100340240c80e03021000207107440420001000002d104051034001075014170301c242d100720301d2980e0300c500d000c1640d4060000130501c0420810400d03100e100d5020b1120f5040042c0c00e1031092007262411481610ba0b1070120068903101c10b40075921400300310360706100b01500c142d03640e05082c1865943ca400c99207000c680303038414034000301b83c0322035000a44089406c03080c02401142d08000c210340c80d00705c0005201e10796a16003444040403c094040705401180204051603a44a030860000d050581035005103034141c3c010000e002c000c100007940c02035095000bc810545819800d005140d8010896402420300c1c480460308405000466000b004400c5c0b003168030200440e500c17807521064841410f80300b54030b00061000c0e840840e0003500155408600391056452321031301d80203080710f80480101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 562463821 1250 562462571 562462573
    0x406090605070503070206040b13060f0b0411040f120f080a0906020c0307051804030512010801021c0504050c150d060e0a0e0609070611010b22140c0f031305030c 71
    0x140020511015100c0c01c0e4120405151061451415060183d5244c40280c0020103c46550f00020040a0100007480700303207500c1007080c8259a80c6101507405000d4080318540324500c1c00700085220344185c0e04440881d20b2031040141014600032103e601640c5658050310140090304d040b00002c0c00e0302008000222594a60204c10b50410b41d000303150440c0010703001d00a83c44400c00b880b1541c0c4003090750084101040d09083e240d9901d281c100c50034058400742c000f0604112001103100c1c00f064000d0300010304c2844400d0b0a42e00c601102c001030b0340d400d45002d815604949003078a80b505103030101c0143d02210548651401c40141001303000c8441650000b034007140d080c0240807a24001d4001c41d89c03e48034102c01040c990074805071454440320948119030500004842d8140d01850070f4000111202c00141110084404c41c00b094682d16107035103c2900c43c070302e010301d2885404960740c0a00c4c021361003e0900740c00d0000025000c0b50950000d021894298a0b0018400002d4001c0004040c0381c080d0304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 562465071 1250 562463821 562463831
    0xc0d06022a070b091f09030311010c14091f030213090924060f0b030115031a19032003060c0414040902040902030a0501060821040608100e0406 63
    0x810608082490007100520310211603429044010002d9018203881d0f00f5641c040e500c0000b000007880d4003a80250803801d00d103c03c040015850b40015a00c82224001e4451110104002302460700300d50021a2042c0402d86180395649400d04000142c8464400548a04914050160002c0c1100c8010081000003500010007806040510a0402c01000c00d04070610645106a0b01c1010302034000c0e9451608a2020700540e82100c59904000000c1c400d1540b0040d0107900c58800c1c040d9079000b4040c058401810150309144148130b4132404601541103d8030a0300c080419080202829801071b5400c4424410314001c0b01180852201100d4411810080d02c000320001050500b0204020000c0041ca01d003400204402d04048100f80f618201c00c0780d00244150451000400800003004065050b100c0d4540c40810440154040c0040c2c900c018100c402012448441100c1080c203a0055017681d901800100145070180300d940e900411480858001c03d9110008008a22030880702990150b490f2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 562466321 1250 562465071 562465087
    0x1a090a0c09061706060325090303110f0703140f100f0605091e1009020a0f030b031b0d0303110a021005060604031a09190b15030a20030c0d0602 63
    0x2610301006140e5410030b00c008010368070341400c422100604050080c1c100000003410002c9813418003114511604030715403840451f4100800b42412804102e000c01e24104083e800340c10001400c2e03030341802440090100c2070446d80c400c2c0002010421281c42c6200d61810342e400c149040c0410010704101e0200000d020700051186000d445c1541d03c26170103000c3d0380741403004240320420f078070308003400b2080080c54a07140c0c1a250b0080e105541e1202101c82d201281c4400c5265004002a40c9090f00365000e1000c10604002c05031246039803584040d2603034040504050b68205001d89550f118000d0a00040515001c40d40481d69400700e00c0700700041e0010640b00009446a10809412520540e070480c2840d003141c1e2511461803208080030450700031000068443d10007000440c850300019044404141082d1414010000b4241d80d602100c090b080a440031034180000d010382000e400c00154100d440700044060152150748124030f8060080d00300421071038442d090b8002246128040041e940c01e05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 562467571 1250 562466321 562466327
    0x4110a0c0602161b0f03170c0a0c0303022523040e190302010c0807120905070504060f050406050414040b040611070b22020a060f030b191a09090a1a090a0c 68
    0x1a001026900400f22060000c601c800049031f20041465140315614903900f500946800407035a00180312100002c00442059404645501180011038a00c403280c16050b0003454170322498040c45070340d0b8456201c1034141d02e241254903860368001403c0054206010007425003050594092182440f442005480402d0b0742480341d001c95110b54604441c03141007940008040c0c0d40b24199441440d5216101032041c010140a20401020000e000300216907031002410340d10142031040ca8459481c00c0000940d50400d030240101c0b140c034020003491f03d543c850f501d607100e001010b807041d5003682d51001c6282d01c00b0000401840c103035010310400c203020b20b00161065074265420f102c0c101700124643c580703070050311204034580c242c1b40f0078104201c015688010441c028501c11021a9212140c0c2c0c1c580c00341c81040e1060380007036440c3d0400455182e0340d0318460380c088e8403500c0c1c40540c22403440d20000725011016481040c3d1000600c0f80d0300544840c0e8400140203203c140c42400c185680c4040b05001e841d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 562468821 1250 562467571 562467623
    0xf07110108090a1703071824050301030f030503040f060501080c040b040c0207090203090c130f050601090605070b060d08030a0e06010501020c01020601090e07170f0c04110a0c060216 80
    0x881c001c3c85042c040d0742d142c81c0d07428486a40c1000450740813000ca00303030501070407080440040070306c05949040d580340000580c0c4144801e00d4483d0b50714144d1080307691031086c412a8140c03a00100701c5480d2584a58044030303030f9880100241c4590440801c694006800d50050600030700b015402803c0c040a01410401140d903d07000c01071040385059445a012600071401008a43c0d00c020f00603288e40e170300c031103042c10403207200030f507540c0120220340351030f0b8130001035100d100c2400c106901005550364504c01034035540418000c03030300400c10500a0000040c0651320182c0d00020207044c1042c04c1007160748a4500360402d4030350780d070b07050b484030f090f07818000b020000300380108424401002e2643c13450002035126035060141000c007581384d2043c044400d4080021000504108043e03001402c00c01c2c000b9602c0303041000201950380510403c0f2140c92600c0d00030202c6239166540d034640340c41c05241e815103c3c401d0340d500071919503409000d500d034200b2103107000e101c00758000c2c0c4000c0da03076101407903840c1301c0e0503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 562470071 1250 562468821 562468831
    0x6050d15060e040f0e12210606071202010204030807150c0206012106150e090601090209010e0103150b0301090603020901080a03230f04140108180c01050a050f07110108 74
    0x401200342000340c203501110303a00d04181e0580b0300050307038200485500302030a01000300003c40e1080c00b44914004189100800c02c0741c801e48882461380c1c0100161886854081d01c046500080c01c0c405680428880703001001c401c2d090380001131415070740b80d440f030300c10741c01510b001e407485001c1450070301d00d400c140c0c080e61400016170710245c8503541c1050040e41d60b031500ea0443c1d003129040329881804011482d0711104100a0506400a02d075564036500002040111000407003401000d00000c2d90384000e00039078510351016102c001090600c080110300804845c042c1c0719030310302d190a00041040c20b1000841c00fa14148034041007503419030040c00100314040c1e00240d03455000501d0040801e5114140c11100c151780800281c4940121006115a021700c8002c84400c502c0000c000902024800d5071041c082c1e001e0302c440e41c0c217030f642c09040c0301d02070340380c0e00180529002a91006980c0d803141c0c004217020400d504081d030606d03d04805030642d40c0c200d000125007200c1402944000b541e040f8020b10380c82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 562471321 1250 562470071 562470101
    0x60316030206030a090c0513020a0f0206092a04050103151128050403080c070906051f050c0109050313031a091b0f04020c0a030806060a020304180608060106050d 71
    0x103480c0d81d000c02c10074800103141010f00c42d528a01780042182140e82e4400902c002840e400c1e1250120320500002d6200511910100720410b0b0390400c07150010038403a111b025608054510340c2100c2c0d00007148800040d60b4600343c1c0c400d00d02c6908450b80d0b18456140614020848440c8182102c54441c003150a803032011f40c161081844040500001d41030740c4400c20740e5160402e807407051144010341d400e004e66000100503190104461304414800180c9208407040000284a420355440a201c0801481d0000c0c0d20000545964010124020802400d00c80d25080c000100c8100075100d6a007160000050a22041c0c040303003040040c041c00d4003041c01004401da80303019071400c05071a800e9440300c06050224641c180c003a100d140c190384000c0700c51500d104c09001595101007000c001d1342c440742e01404c120080f840c18408a803540c208141580c040c1c030440d03001180b403d428001d40c000b00e402140c0700314030b0076500c0da400414146014408180202102d07210541c0b2001701c81034000507202d1030a452020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 562472571 1250 562471321 562471363
    0x406080c04051c14160b0a02030918222001111e060108030f040e06030a0b0c120a15030215040306020c0d0f03021602091905010f030b060d030c14011b05030603 70
    0x1104a80d04422801c0701c61b0148080e545105034030080c1c2c10340c06000020f6070300001d5181d8005030a503a50184920800c92501c100d0076130b201480d1482c1700b8605032140070f0a412503e04d8080803d10043e201020001d0301410880410940c40c4030440c54807020240000400381e03c802d218000502c10003c550150800e03d024605101c104420301c1500d002da485a03031803409151012074540d0b14144000d60210380c00c01740304041460306c203030000000e92010502150700c0410000041e6420140e102c1c0301c03900f011040030006024655020480860742e5001c4204100707000308000800152a44000c004001e010341c0901981000300e440603200c0e10990840c0d40506004005031500065010f150804966040b11554000e031104104c48061a6035962904495881d1000200e00500520240012207203e00c0c0a40721a999120a00c160407048202c02004600b007098001c0018a8420041a009090200005542d16246000c600a6410100110200b480001402200e007028017801c01603440340401c10803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 562473821 1250 562472571 562472593
    0xa080a0b0303030712020408070b0a1b030516050c030f060609010609030c0b0a03020903120d0b01110607030209190608010302130c02120f0909040b010e011a0406080c04051c14 77
    0x14483c800100134508121121104035803041141e41030380d02a014540071901800d407a0b0500101c01d901c91021100821b0511a803269070034074124442121683c542d99a40c20103000142461030000d20b007000321480c0c00b500c5680c984035242002042e1200016000800c032905100003032020310300040e01300c2010030482880500c0810f58909400c812245405555580c4603110314003180203001d00c802c82d582c140140c1711015000031220b009000400008181004842011401911038000b492284a16500700000103005980658082c2c00120781c094907016511130220220050b03500e01e50440d0700816103480042c020750414096100f6400c800c00010010346566900c01380d9511620840d201000200180c4600c0210401090750141c903009018681a810285480b00304d420f000d001e0901c8056800c0000540270400c1b460352030300d1031407101e0b021b85017500b411400c03281030b20014180540c0c07200400000031940c0790041000107880d440c2041600c091041d140c61260340401d4002940070354000f0042c03803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 562475071 1250 562473821 562473823
    0x19110a0b0304020603070c080c1006050a060c12020a0c0905091207050a0209091e0c0301050705040f030609260c010e0d020c06030421120e03040e07082a0a080a0b03 72
    0x1e600650100c5003592250742e1888100c40c004505840200300001c082104154100e000813481c000c40174800084c04000d0b220028812010318610494001130107004c60710020400740000c1c012028403910680d004842552201001040325034402b18541e6034a10402000d08401d0010030315101c2180d180e149000042d480c0e8565842c00064082e100d1484440400c2c02c0701001c00030102d2000d40381101ca805190358030165500c0d0b40140182500a5003841e0004000313030b1054044409a4035941c108a030b600c2d046446010041c000c1c803c0031103070914400c045194402c0e0241c0e005071446180d0350943e03642d40c1e80441c0c950035142010a19002a40003000c012880d5030003280c0c101240e0b00640d1070303d490380d0381c80c28410703146051926107070b400664400c5c20703c03085644000511100401030600713010307580307240681d03a07942d00c138a00c2440d44100000c000b2405035803044c41606d41000e0524801d11044031800c040e0341089401100610221100040f000102900701a2003681304410b030204000059280c0042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 562476321 1250 562475071 562475077
    0xf0f060f0905090a0f1d2b050f13090b0f090105060306040e0c060a23040308031302010c05072702120103031404030b01083417070819110a0b 62
    0x310380710f07102110014100f0085a40810500303e0b54680034400c8010b0b0190303481203003c060030349100d60b0040a0494103010040c03944c03807101038540c14202501e00400c6908690755000480c0b01d12058904100e83c0340c00c04401071042c405004800400940240c07054100003848024280190140c505100108042c0d503448064a501000c162408910005030141c40d600744000c841c14240e10000108540d55010b0307000c40911060744510750016281440040010b545002c3c41c40024000c410800000b004481c0040c40100c1c1c072403060514005400855955074100062034020084094040181c111407024041940c3e8050002c81411843c1c00c0100b181010616014013028043c0407000b03802220703904840703085500031a0040e000da402561180c1c00151694000d80501244e1180c100d8131243e1110300d0080d02c41000e40c0c0c841d243d0440c46c94402c039919061544685000e0a0181c10f50004080c80e00788102c1c0c04000c0300b5000d14003840e507031346054407407070501c5035040d0700440d078500052080304548411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 562477571 1250 562476321 562476329
    0x312180c041109040f0c0905011803020d020d02060d140c0403030203070605040f230606041a10032009040c020303060310021e0c06040203010c020d090b0706020903070f0f060f09 78
    0x842c040d142c5141440342c40c400d20702080d400514016005404c0c8065034484505e0b55184d40c0c940c005999100011101c43c40442140341c495011010308000503d40003500012052005e03040290218850300054000c0c1c000214001000c4d854a4580b6190242e0b10441a8031002100040d4107007030039500c0007540c07800365000c01800166a4004582840481040b11159903400b40808100d4040316444414034107440010300300c1841004003042c0c40c0d02e424003e5401c40c0d9005018666008804800c2000c0d5048000865080c0b507962440503081091091130071102c03104011180340d454110500344011502079441c5030086400901c180107503a6004910502641e1a0b6500542c95074800050b902000e02d005243c444030000002c1c0d092030200010440501c664003c034001c0000022403101030b42c07600e03c02000c0e00300081c0c4240d41845010b40c000040e1000c1809450014103044009010901c1c091041e0840710894642c0340702000180b5101644501410152400d403c0c000e0b01c1803405400c01089000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 562478821 1250 562477571 562477579
    0x1020f1509070308040f1409060609010f030b060d0b130e0309011206090c2601050a0501050a26090f07060525150b0a06090803030610110f0312180c 65
    0x101040556a00b04481409541c10040003a51070b6928640c05101400c40d1003065040e002d0510302d41e0862074401c045600c42c00f03000e8a40340c0380c41c0014004540400b209000a424107030f403440c5035005515500042c04841102ca000002d2803402a001c002c0d60ba1601c1c4079800c0b1160414400002039000801583c019490a0802583d408178261450b00a030205030042800b0500e03242243d154180d000c000b10380c8503e180d0880040d0b02d50740c0300042480280900804d5000011003004101c00e501c00d000420000c0c0b024500180110700d03d9050301820b47c281c1d02200c81e40c111603028070200300c078180102090035116200804465141000c0a402c070700072586a0082c400340b038070500907403040000100c0d2039650301c0800c01020056051259004210740e5041b28003904040002142d15070054400c130058615440085066a036428200a00712650584003410031403004a1090400700804c950013099940e80040d41d01e40c2640a442612518000d0110301e200384286021308800c88081402c1180b020199 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 562480071 1250 562478821 562478863
    0xf03080405031207030501050a051e060921030702011707020d0e211e010b06040b0c0a0f050105090c150703030507180f05030607260a09020603070305070e01020f 71
    0x2003403090450042100140c803003c0410100003045602d0b500c034506803031085507541e1060ba01c030824001c00c002510b4040001001030b0341400e01501c1d0400181c4008240203010524502c5080d440c012038a0500703148110341d0344041016070031507810106401c011007021060078018600100c000b5038a2544d9003030f05e424040351103c441d006d61100c0b00042541e0700c060020007094802900c2182d524020b00c1050311044900d107804906441041c0114082020b0090216041c1410284103042030f50121a1f8400b851082c60b05410004e80e81c0c0401300d021b603025a0001a5518100305520309120701c00c00042d1088c01403d2107070700080c06010a9031142501803a0000f156a01c0315020348491189400250382c0001407900098101440031000040d55402c0d01034950548a030300301551807400c04d41901c244043c00e086950548000e4070b2445a00a401d1400403036420803c1c2c01140c40c640c000c0d690000000e40782c20030814426000030814840f00e4081c402010640a42d404068545400c1c030b0310002520030344 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 562481321 1250 562480071 562480073
    0x120503070311070f0c060201020a23090d0506220209041415090a170a08010315020d050f1608090c040e070b030a0c0f020c100e0102152703070f030804 66
    0x7a41c00035510349000d07900c0c0d41d5624040e0514000b04451030000b101c1035000c040c4041b17546403060003a40c0345850580ca81107203844c40e07088030b4500c41a0030700400380c0b804001d2000d110290344540c0b204402900420103001541444001c0d008030800c0404022040e0b14a04683c0e001611155640d0790302503000301280d091010500c45282c145540801c104018440d0001030140c084004689020341502c0350038002c960126507070101c0d6040c0901035024001c15546801040030840117004080701c540041d800510700319451030880225202500c4030b20f82c82d40741c0300c10423149203025441e02c0303554405400c06000e6413610081d055641c96031103075400e008036144c0d8691a90f03036004215103405444854106078803840d00028100003481c0d240c9042c07000607010307211305a4030f0b030007c50500743c8460003400ca0f65102c185071100351659058500d1441c1184035420207030112662210510b801091f164198007070000500481440c2d10401001c0c1248a81007009004002814480b0b4454050ba00d81801091a07441e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 562482571 1250 562481321 562481327
    0x1060e090d030e100b1914040f0b09010512120d02071208040b01051306030206030f060a0e0c0306040207030908030c0106090f11040302091b0703050a08070e060d0b040e0a0606090606080412050307 86
    0x11b4009250407007401e85010401011155900400e1030707041c0d5040000c0d040c1507103030714252501e51a405030015008001800603003800d40300b006141ca001c40031118946481030503020950f010f610844031a030b90105680041144001000b16085514030308000a4101911044441c14042c80390740c0c0708030031a20389a003001d4282d400981c0290707002840e1913203901d0b0605000c1050001100c1c0980318000e2148041000d03110700444a00460f400c1148c03508590703422060000a6201000582c103005130f600340080c402d0000c000a0407003101d20350000c601289000955000d68200c5002490700504028030300c441800000d05540c01c80e0740440c1c100740d05446078a99142181d005030350407081d03d81c00150740310505411800074401d8201c161744080c02ca9946a10841d40c66046003c40b03548014100f00072886501150007081ca2810028000038042030700840441c540b0a269104803000c9485140801c211481407007501c00400c028240503500e40303059a074000c15030401981d003100744000480440c901c184 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 562483821 1250 562482571 562482589
    0x14120a0e030418050c030c0d0f0b15090901090b01020d0c08041517101401080a2c06010f05150a030609060f050319080306010f05070501060e090d030e100b 68
    0x208903081ea03039215250f41a1403440d148020a42155500307000206005404040c02c0741e105152124006040c54811038080002d00700040c1842009070b1510704009941d991010107212140300002300543d034500040a0083c03881d4164400b048492400c0c52901150f43c020034003626179002c034a480c160035011498810070b02d00681d00f251003100100a0f0015407503400c01c1074030300e41200501c02d5030403a40d50343c0e0151401e4650b90158030040481580400543c0d40a031000039084040810045480d4002d8807109000c0e580d00903007442601c0c8400486001c1e0101070008501500107100070380c40c00c80c00c041c04254425411800242885c6000070001e808900c2580300b0f0b130140420f04814005035075140c4005d01c0300e0482c0c0c02454840d00079100d0340b0b0b407892110100b002107994442659800c40e510040199080c080c0201620300340300c402c01009001500130700c900c101030640d140b4505000d00b090390100703151628480502c014549080724005200ca000070b01d00045050185010a4031469400460301c0b00c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 562485071 1250 562483821 562483841
    0x160509130c0e0702031c0501030c0603020705030918060a14030a1209080a050109030f02010c12110f160507080d05180f040f0e16030c120f050706090305070614120a 72
    0xc00c442003031040c080e5002c4000e00d504200800e6a1b035112050f04585002c9400c00e102c000c00c821400b982c01c014030b070700940207001514080d034281c3e820440d1010110b0205140e030300408815601180c20442c15160003807811000c1c01d0b590b00b60040ca4030919010a58601c442d140181580002110500c04075101760490400b42680c1d03400d4070344000551030507601030182800c045020030040c2e44125040c2c2d205208000e46405286e8403e0403240c3c1604c6a036005280d02000001020010000c40303403110041801410b49102051104202c45860304025050902c5034012241a80299541c01c022591040c299150302107504084514014903000080070303a9142d000d819001405c003e00903c003011264440002034504005550000c00c91440180005106001c000c0141410b20000d02201c0c48c04401301c0b031000c2c801c803250024030f556a160789103404400d51040001840941003403081140601040005200c035051031419261805c940300c8150140c501c0c0c0310000f00700b0000090055101742c01c004014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 562486321 1250 562485071 562485089
    0x26070e0c0721140a050306010e0402130b07140c011d011e020d17010b0d020c07030605250c0b040605090a060f0f0e0a0308040201050a090509010611160509130c 70
    0x150804401c52202510b02d020324001040d0302806008825034440201d03038200c011603440300d1860b52042c00545542c459808041d400550034031501c6e1510100c0c20007040613003106d0240c00c0d201c500c20714240d400114120312419058201258011050743c202c0e100004444000c480e014640c011100100e40c1c054200c4030052a603908500c2101420b500030508000e01c9015070f4444400000f42492101c0524081c89a0f0340164010489505810b840d540941050b041d208103480d0040d0f925292242500c1c800d43d81420400315000311254508200074030f0380a2403405040001a1080ca5110349440d4003004001414660310340b40000c1a007001800302c4580c80d50f001e0350410110307261000c4603000307181c03030408110050b2400081001e030710000100c4800907541544d91004568403903004490381d4100391341c0c01301400913816001c91140e0320f09031482d002c2d1603141c1c4d841c128000595491460220b02000401d9640c80d07828040c40700e61150b0107015800740a91000040040c01407a204c40e942c0385645c402900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 562487571 1250 562486321 562486343
    0xa02070b15010f030b10030903020c0904120908011503020d05012018010e03102f0a0905061305010e0f030312040c0503161806051201050126070e0c07 66
    0xe80e00564203004070001c0aa903480e03424000302d6800e404075550358001a03030049011102102c2d0394401c0d0400c41ca990b01ca031040c0c6401d401d8034004501e2054040c0c07270481d841c4008950031900180d1040e00e00300104849002480184c91400840c004c1318050300010b400740d95061000340c14800f09400002002a041e40c00765543c8117440c403400f0f0250031a0f500c4c843c4504041070403070031540c802c60018004440050241240141121380c81d40240350603800024240d8020221072102c21001c407003448460706104502d0354401030900d004124210580103144511010303c40c0201000100c0035076810b9410a00f08075070507921801c005504540440c000560520001501a03540c0d091544168040c3c0e05c507d89505080da2140d0400d625420004054488076a007218100443c070140078685c00c02c0c0140340343c00100e1b2030301d48000c1100320f0b901c0d80300203025039100c400402000821200c0076003d880b80350401c3c0c1882c00c0381071540351524840d103d0b07601c220a83e01c000c100c2000550080b01d01044e881504148 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 562488821 1250 562487571 562487581
    0x10323010312211509022104060b0d03050301090609091109100f1d09030c100c210506011805010f14040503010501061e051201170a08031003020a05060712080a02070b 73
    0x1405428655640448910b02e0000e52201a4004d43c5d0490640140d418a1107034407000447d500030300280261252a1545407640c1c254403181d51072541c80d030284d5505079496061140c3d240c1a030310268441c061543c50f007881e00010803881e601d08007001e10115007079180d139150706002e8041b504668001c000000382c83d5800045c20f0011440000c480e440e90b1007118407903542c51107203c3d140c6c01841c070140794582103031010070f02c801460b5000c0b40d0350048504009100d440150700705c440000940f6001502a5030301d5060100741e40e0410a44100d003824a21620351850030080028090080800070005202c2d02c44109444001608140c5010b440060300030001c1d0341e0b6518004004070750b000c0c20311510b0845007079000c8a840c407450880d9800d2880710031140c400d03480c200103840c0300d5585100e051418000c2044070300005604070000d601a2544043c800c546501307500402410032410340c005445014200001000125524840c6c035011000d410070101560303450007400081c1c41003d81c0144038081c6c90b41004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 562490071 1250 562488821 562488887
    0x1507061d030702031c0503010b210a0207060b0d080a1b080a0207030b22110418390504090c1d0109050a02030712020a020a021e010323010312 62
    0x400746500840403185e8084481035052000800906040d0000e24100014000c14007000002c0c0b100d134032024060540c103d01c10400c038800300c1081d100505040d80008000b0144107050141c0c010f100e50456030440f400c038145c0e40d28002441105100c1c818880e00e0281c0b0003640c440c0310407515520b070b0410080396030361118000c0292030b140280012a09a02c1d4080407039440ca4810f08007030011003602c20b929024841c151103442324000c0240d4019400f80c2c6686044185070702102034410744a100d089000040d0301c0345011810480410326000140c04605410800c078002c070240d5480c2200c074251400601e1003c2d40c100a88100b055030460351031301d1000c42d0010a000340c44680035040f2100c041040140d031300c42001d20b80c16071000751010400070703031081544441c0148d280e00600069400d40121200c0c54000d90100c1c460002c41852980c122110328062581c81d60540180c10a103804d00300400342c5100080003810300204180030280c1b0b05920a1580e081150041d0030f944240c2c615012503459503c004011300c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 562491321 1250 562490071 562490077
    0x110a08041e0819020f1c05090a170c0102010501090e03030a090c05090403020c040f0207080a0e040f110304050f030712120221160f140702190b0322021507061d03 71
    0xa240144511122001d4440340030420046c11241c00d00c034880c01e40c0c50f000e130485a680240180a0780001c1c1074100161049400d603009900c481e0000240a283d50200300183c2180d00c16401a0700213414005103003d8107001100b02c80c1c0c000d5800c0c0c6c0c00611108a0b003049958a007041d040944c000070144103010034190005070059402104803000d100b007290740900c0a05a0003100b600404281040c422154207a008a0701d2140462010f40000b50b080f11600922095a9081c44900c82d0103c0c000148010300c5424000b084c058442c01e00211314041c25583c1e041c44081280600004000254107403002880702030301120881c0c52168241c4485484202ca010000201581c003414990120107500049034098400712003502040e0700c588400e01c809065881e00c030390046104a90042c040400b04441c000d81300c0080c0c01600b0f100c071155440e840c040d2485010059840070750a04a814900b0007401139440440301401c004800044a07125aa01c1c5440d038003800c0180030151204401c15001200c00d00000f000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 562492571 1250 562491321 562491367
    0x606090e0327060403080c0f100e01061e0b0f07051507120507080604091109040804061b02030d030b0301150b0a0f03020c03030406091410050a110a08041e08 69
    0x500c208400807030001440c82071200b4041600410144410000726034050302801c81a48501c0688441c2a1140c0e49941070003d0010084619903503104501c0030080309101d00c201400044520742e81e540e80c0f44200b8202c06046100380f0b011007a0024910a00c01910400d071600300d54806c4c100e4403401540221040d000700211a040b0000368880b600303c400414a0042c1c5025035003030b44981819032610010300001e0801d6640c01c2c1c800700480d08a200e481d80781d0102a51180d40103404558440e801c1c0840101400d2004c0d003054000d803a44040c50b405030781c0c04500e0744502886810001f940e13402000109000d06500c6000c020581744810000602480050082c00007082603a101c2c00030348c0c528041170f1700720701400350a0421507209000040005003240d00c440f8100b80103d1662819030058074442d4a403400c44210300d40119243e8044c4600044107000d0382c000c202d1400140b50030708029400007040c141d40207001030100030320602c8660014440d8240f159080c2c1c0c21441c0d00707643e0441c4030300083d104c1c00d00c0c40c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 562493821 1250 562492571 562492597
    0x1504270807030806060702280b1819080304050d030e040e010606180812280c0c0501090b0711130f0504021c080301030f06020409180506011e050d0606090e03 69
    0x4005104d520f40031040780d1159900806074418509403c4188600180151082290300d041f104c0100703004000001500041126904240c00b4803003a00a00108510030141c1000e1083c0c61082031204500110035241516000d581e001285480b81c2002c8500210981180760010b19040110100000640080c0b042c0c551646030807281040150005e101511507115800c0250094902e400c18004444001d0562581c80c2406843d00c0701a44c2d40486400007403052a0041119140b090040280442c0d00000416003401c1180c5c00b00d02d41005010f80e07105449009200100c8200c5100c071303680d10000301078503180c90030400708a6540107174642d1000b80781c1078030181e2040145140b17080004a0b915100c031145070703100d600c03c1c1c1180d185543e0200d11a08101045552503020310010482d60000d11401c0b0001c00494071b0300a403a01d41e030505500340041038100a074841051892040d410050458001c12680b06032043d03a0500780c0c030308000c00202140d4020040c4141415a0780031810300000c090001012848 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 562495071 1250 562493821 562493837
    0x80a0b01050f10110a06020c070303181a0901090b040f14040501050a061d0d21030506010519020109080d0203011e0302010e040f0b0a030c08010e0303150427080703 72
    0x108100e00500102c0c025a070082412100c1120644100342a00202d492141100c400313403101c1d6616070580e082048000d40d0b650010303034100189584035a0070080c42000410f100760780713030402940c0382e113449a402588082d884c001900c82e402d82d1140b43d0700740042403501219500c40c0e84070a41e01500c00d0062091107643e0700030600030340c100d01e81382c0302d0300d4101d860062030100104d103041c80a5801005502c05007100c41c0141c918405241c50700107041303000703910401003c541e44261900103a0030148240b0110201864441005482d0b41c008003102c402005441d8244555030220b8012805000100e00003802502c0c0810400f815031400d4001d1f60680d8020505c01ca2942d444404c1c8041c00340f020711000e40080d0244000b402c0a0415500990500c188500b001c5500c0c0000b0021800d0181e40394421241c0c051601700400a9080030f01c60031880f409404051850760509004000c042c40c405001c540c4580c0d60350f12040d00b03241038503c0d40b80100c041e10315030300400c950301e090000709a0080b120a40108200c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 562496321 1250 562495071 562495079
    0x403111b04060914060d14060f0f071806201c0e0102190209060f0301091202160f0e07021c050d0506090c12090705060c030d060f050303030109020c010207060204080a0b01 75
    0x640604d280c002592812480c41da902c0d0001c2060f4004406000c0d101c5c81003411807407441150510110303214242c40c80700c2c01e00301e00701011200444207006000200f00403800da46c200f038002040526108550b09458010b604003517110302c0c502c0a03e410f03401d458846c4111000c00b4035442d280b000107a100c2200303441d0381c92841c500301c00582e150310400d00200c0d80c48400e595020014030f040c1026075001f510103048a00303d1401223001c05e0071149145400e4410f5012900d12010f4683d041111b030a54450141d042e5400500c0c4c00c203054004c210314040c03c01405c90003000640c82034400c00c29200f1102c04a800c541c7c80103081c00300a400d0760301c00c5025000d100e08020009102e420201c1059000d003079003600701e0349416610803841206a00186c8028020301a4800018481d52440c1c0600b0540310007a000d1542c8940c41c0c8003040880d07a041d802564150302c4400100519074010013624115050785a02607529200107028500a11568038020941480490042140c20000451580c103e00c00c41100b2460f0341c07a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 562497571 1250 562496321 562496339
    0x2010e031623060c070f02040c02010f11091509270a11030c07140a020405070e03010f09031425061e0e03180105270a0e0402030703020103050403111b0406 68
    0x28080b41c0c0b00640c00301c408202520202402007044500810101c21111119070014081d291101d030041c005079100c03803d5491070081c0d441450050202c01c1007261804147c20007050480e1808010a100301201040c042896158803c00010103890451090001000070480b444803481c00ea5452401c10319229105410503114022070f03000f0302986040c9410500160b854900022203152402494042c0c00f5075100180c40700d014444c01140140c441e42c45010403442071500710b541c0030a141a66604202c9048003080d000030124078010015095103645003521440261131030b20b1426030103040300c0a48070040c02d000c02e5520092a0403050501004400f041d4014075094900f1360000200d1500100415074104010b110121030240c4181042401c00c0c212a0030b0308030f0b12031410070109820400c0703070000c1d0f1980780c50032111001d40a24041c0036800c0c109070300840e0b550103490100905056881000c0b509042c02050380346455450901151801003a00b0114040401c280107041c0c005c9040001c0410180300d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 562498821 1250 562497571 562497623
    0x8030117030711061612120e070b0406081810093f09090501080307050d0504212f120f060a0506041b050406080f010513050702010e0316 60
    0x240040d030b4400003d010320108545a4007941804114410f00c07086100000c0e0542d041d41e00903850764a460402e080d652101d03006130795103110010080c0c3c20a1405000c14052401a2415940d16145c90b8986545e03096a072150342c800c500700b00034070f031003003919a5419440ca5002120300303521a01c07050708083c80c078140300e1126542178148c4000390318010300d040707600343e01603903299114038500c2c505860965554032100c01261b0b42038003d408507402c0043d204040c0a020024000c00e400246803880c135191a105201407000f00c44405040300d0010070085000788884001178100320381c4400c1c0891081c4201800000f20b510300c00c008c041c013404140c442018841001300d402c240c80c03012200078205541d02c0840c048000d0400070000c0b50b00c01c0e03032084912612940c80d0350440d00c401058903001d659034100180a0728820380101000d049544da14010f2001e5100e40c0860f100448044070040b4507610703807240681c05401040c0d01303542c2c5807201254900c130001d0018840681103014055580c40c1c900d810a521101075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 562500071 1250 562498821 562498823
    0x200d08030f040201020c04060b03100605040b0a03021c11091509010e01121d0303070908030a0915030605060c03090406080303090712030c0812010504051515180409080301170307 78
    0x10103000003040007035642625640503105105980540c034042c00003a0458060ba00010103005022040040b000c4005060741c0150000c0d00303103e0704240c40c10301e03445070a1044a448034201a0046810a03c01400d120076107824000c0c5001405540c0c80141c1000785038200031049481200380903120502035403a481120b04164040c0d50b800412039900c40103480d0070b02c0403252248107035501c0c0d02e061484c01e00e24104401403002d45020b113a6030b0070190b0000b8451140c035040300106400c01c010825550303800035811380c02c86029081d00c45003114110760590041405510075508240c001a1350148510080020808203c0484041000940f6408060303501c1c0021510001d03a41e2003a00180910304001c0c09480586100307107002200d081042c1d40b001d20365049500d0540d0cca058100060080345460b0141d81d0b0300920300b412403051290440001208194240c2d80800c0380d000001d5010310b0100c415000556003540908140311814a0786000a60355000b44a5034800d0340354100f144240400c04030490700c140d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 562501321 1250 562500071 562500083
    0x1c02070501030b0310060306050405060f06090112051f020a090b04051315080f03071a070c0602030705130806070f0801121104180f1509051203060418200d 68
    0x100d040c40015001840c84591040d4107100d03200c03d4540910003401000040c61042902080e24201880d202c0e107000070203050345c10301481c0ba0040020545422090b24115014102002300054450914900f004104005142d0917040c010001c180c0380c5079900240494403241d40d62031225a40d980b640000ca0040380100c680c1b10380d80510170200c140b590307080051010845006481910b035036050312864404d01c0c40401555400128006080c886100c101807861810303006988603a00e07081c10300401060500000800c0f2582c0071020801c0030b88100151044a410342e10443d8502ea12105c805a07038020440d003803000608080c0591007950700ca02555130403038503080c5c110307c1c80300b800399a81034070701e82984140b42e04070f642c90781018515000c03032401c1b107180e50203410130312680c0d01c40d410500c0c001074184480704455820030f0002800030740c0000304200d0300c40b90b81402c29200d48070140000e01600f5104129103182211a4800051000040a0898001d8804100c4a204180c40c0074840040345041000e456 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 562502571 1250 562501321 562501333
    0x3120406121a060301030b01091b020307020d170c07030c050307050a030b06010302070605180d1b03030e12070c08160b070807030314090a02011b020a03020d0c081506031c02 76
    0xa201c4070340c0c011008240c002c12402c1e941a0303640c1e001c508150000d92042d00c485001078010420203c00c1d01c0345101c543d40100c1c44e460030a91000e0060760764032030118000c0c01040f40c0c0b451102030001d03c081c0901d580c0341611042c0d1741d81d900d10f041c02da55401680020b44407450840d46c00940e9150008500f01240d2001d8529400c1074034540300d100d05007400820903414035408202c0c100014081f403040030b126601c01c1d580008013035a01ea204501d0403c466000c50305020040180080c01200202e0030280c2960500e00440d84103041c010312400d110319241c11140011000c039000040000b800329a00a441c04031080b01c46200c140000c1c440d10140e644a107a1150342d0410002000c509000000c0c18000d02074100482c00180307600c0e50085908080340d440319a6049031030340804660707100e100110002d0320b401c9100c3c00000c140d00020b6080489100c001c0c13142d5050000081041140c15048000f4600301c016501c48040714120390890550403110175100340540175406a88c902d502d15200b101003019030007009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 562503821 1250 562502571 562502597
    0x30a050c0121050703062409050d080c060703140c040302090c0c010b1302030702070b0c0c010503091507031401090e105702060606160f0b040203120406 67
    0x140880800d41c0b1006190952400705506186600440740a413040c1c0d81c0002e4040d00d0401d550b80216200702050820501007214100a164416500c000365007003140c844207000d085140c918084d01c5031441640031b0340110710801c44405c2d0541e0107558400c4d880a4440060f6507522070081d55840740b804002d42c0946290046a120840031002e816071581c0c003400000e0302c00401000030402071501c1c01c0c040400741c001082120305c90381403102d03400038072110848508040e40018510f4850104004440c1001408400510100030802090082d090381c4100701002d4200352600030050540040c41c141208000000043e054240e44500c1c6000301046000e80403450b2401459406411140069000c10140c0441e800e03000099007805801065003227206039194004041c1c403002c014503c21204517100c5440c00080ea0250045034481d400041150110b0303460481c0c0c40c110600100c000009400c841200b0031000c1081400d003001030003280214115641c000c0070004070901032280b07014410008042446400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 562505071 1250 562503821 562503827
    0xe0c0a031a060304260a1b1716051e0606041a120106170106060801120201030216113618010c080a110403020a031b050619080105030a050c01 62
    0x410040101c00204030724181c500000341568005a07001e0321450100c01e1002c044264090311040c0d481240001d140c10b20040e0040540803170074841e901d2101c2c50004070400200040265001d5441c8802403849413100a1300c040228021b1000c4822102c0344074a91501071480d00701910781c12a020b4910041c620307076a5000c00e12000c1c048460300c103002844003950440703a698501190f10900754400000007421844d0405844201c94503811300101c0c0c3e49061020b104280c0e001380440d0548040742c90302510800d851004078000d00c540040a008030046858101c104036a5610220018404842c040b507107105540c1c401c842600d0303c0c440907082182a4804212803048059401e5003c20b000055801c0380c00d011040900355103000206000003000b00d03041091000c528806c06082c0c0848901090030709045a002c2400140540030280c8101c003080031184010041e0004103000d4800a000c45031140c40107464200d51104c80c2000c2004540b1001c00030400f410001003c040b441c0c0c0040003410070350800710041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 562506321 1250 562505071 562505081
    0x2601020c21040b0d091737080f0903070f0605071d0a0501120902042409020f1209031902060a0605091902030903040306060b120c030f0103030e0d0b041109010e0c0a03 73
    0xc0325407104d801b10140b19940c2500141040d4200b030050403080300100320175007204180900703544a9281c980d0020240d0141c1c8404125401028503007510401e44404816511394001c01070000c0c101140c40081000304440c0360001c0f4060300e840c1d00c4004405030403419072042480c4d00f40501c2c0c2c200400090403c010b61041e2111007102024202c002075420564002c2400d550083c482c80401d640d91011031008095900070400c001d1a40c0300085003007102d4071603542424420ed00200c0030b01c0342030202042c50702030f00b402182c01041c1102080d100a80c44a00d01944850003151013500c0b052904500041c5402c141d01c5462242051400310303200000301c104004000d400c041c20000c0b60748001d0201100041584c4540006890424021522520104441c9d0410100204011105072050040c80701c02000b0085890640f0f80c03605141819084c89000701d80b041d0f1082c0c0000d00000540010f210a00100e200e00b0f600c480e00a4540640c980e032030f0f6031989481c601c20744450811290400c45500018030035840 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 562507571 1250 562506321 562506323
    0x603011e111204050d090b070305040510200115060309050304092003010b04080c04180f080d020a05030105040c09060516020f090f0a0606182601020c21040b0d09 71
    0x1025040c004040c00c80d081c40b000440d004c648950011982810032038001c84010003c040e06000240f5004041d5402400c0d8000c2d4418180114040310715852003500131b440d500340711203002d40b0500e500308140d440c103801b8200d04250040b10a1031070b4000b1410b54481d00800703520b00c1e0048015407510340f92074020343c02000000540861521070005c841e1a040e00e02000314000c0404040b95130b01c4038100403e160a0069a0440e203110300c0c03404602d1032420b103401e03c0c0120317081d42001180141119909240d82d07144180c00074825a10300c00220030410030782040c003440c180c81d000d40d003c10001140340400d40710402c0b1400784201180052042d02c2c24402e42d0318a0201052025004540060440e40401d600f813205550024076540340d8420000d00c0c01e0240303d030308010002c0d0b00d0001e20f20103403500b03505044a403501600007108080118002c140601d10007449a404142c0c0c0210b642d444115030058881c0700c522064118005c1c1c1c048103004280c01c65041c0c2d000c3d50203040c101c515000d1049255001003c01e900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 562508821 1250 562507571 562507601
    0x20318060f070b01090507051c0513050304060c140f071e0b1201030b092e140106050703110c010917010938040b0c13030c0303050d050603011e 63
    0x881241e12041405007207000d20400c0115040d5041111901c15a500181700000f040b505001c403003100183d41600343c24907906080c002401d51145c400c3c20b069000940c1c4068050711001400098856015005500150107041d0b0028142e003484000e94803105e1070450884590302086040c41030030344016201c0405241c2c64920440e46603100d1416449030455070004845000001c0104207000c800c034506540f24030751002418178101c1c5003581401c2d010106040d1042c155080d2000441da40c9294800100300c602e4281e02c40c125a074a00c4001c020307921181c4224001407450071090301c01030b000a214401664161a119000c40c10500541d0704400071280681481d9221701040000c10b800b420071040002074420300b03810704c1e0b403c10315241140e08108208503458959504004c007003440f5900981c0c00459400105646030f5070b00300c01551290b1581c0015040304a02000041016007010041a1406030317010284801c0d61800704041c00c0341c640e0341d0a10415005075100c5410340c505a84810700b610013940c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 562510071 1250 562508821 562508827
    0x5070e10080709020910030e15130611180909150a06230406050609010203160606031202010c031505030a0f030504081605040608160b03061f020a0308090d02031806 72
    0x842c5895400c1c3d0002d02020740c0080c41c140241014a13803051110001c0c01c1c10f000b4450f1407160b856030360002a155150150401020a5080c0000080407216030340103103007441012452840941703551b010b40310300160402c843d04401042d08000074190f02c5105944050120100503d0f100c03092703040000e20350991140d481c2004106000c400114280115058540c0042c4003034140a000c00c5070740640000d0f05c41d160a011200050b80d0010403148444514410700078460498030f0303c03202410b0746801c0140303944404403141510560540c00503001400703a0358144510b5800c0501280190003a0003600c2c1c241d0002140b84c404100300c130194003c00351191402c180b80540c5d42d0304140c2050098046070b40c1740c1030526001c0010345002e00542014100c0351026040450b4041000c4c200c1e0101c0340700720600d1140200000d40c2da43c1d40c0b0100c808800c62103c2903140782142e600c40c002e4603040e1120741180800c04140101d00841030005001c01d40a0545c1c0045207404d82ca0708130418043d150f401c0c2d40d54001420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 562511321 1250 562510071 562510079
    0x15150518090103060b1009140d050a08040b1201210201030e1509070617010f0501120902150705010c03050105130e1c0207080d02030307023318071205070e10 69
    0x540c07101c0d000714021400020641059002c121811031482094010048624001c0c84141942e003811112018103c4400c650794a41d4500103041496624010703042c003001040001c0c031100d1301c030003c100b90040c00701e84d01c500b680ca4441006842141c458038010281a61281d00d0055000b6072002580e01b083d9011aa00307001c6138555420b06800403103029025030024a0200035084d0010008418a16541c4030400d2a42c10702c0035891010300b007845010304104414407283c0108a40d0350152080a8015080900080c42c3e05a4001c4c1e680c0080b0040b50300350300c0e02c1d03101160303903100348035035416214010200c081403d03016224034050500c1c03803040d0a841c014034450240b00401d03107214031003040701a0040c01c5514a02415641800704d02070540342550010070402c840c2d42d501094080e901910600304411040c0c0310145410b4004400806094078500e04090200b810344164078808054007207411a12203544591040010380a00341000301203601c5400280018044074860660207460b20380000d010541e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 562512571 1250 562511321 562511329
    0x31e05040c050103230c0a090b0301090b1e01020c010e12060a0e1903090303050318160302280306020306220c0801050a150305070e060a020303010915150518 69
    0x980301241c50040c100700400036941c140c000c0780d1464004a0700c1000e02c024180d84881c03081002482c01a040340000b400d1000140070350001e8018100400c03541b89c0340e6031510410802050b000c10114411000c0003400210a10310100500e00c645040c0d01a0240020b040010755001c41e40c0c1c490180c0c02414070075400f005050402203180300d00716941010580d5000d10480b203091882185060941810a140b0311021075044040002241d61500c3c22551741d9452442c0118560050128a0790b20b01030500c0f82c1100745800c1501d1015280210303100c920807078143c0c140200b0140e0019407400303107400c094000c0000c2105a400b9552201c4090b28600782c50146214043c0d4011c0b01d008500da03441c0e036a124a0701400da0000c842c0d405454280d90058480d428001502d418a481144920030035455900040f1818415481298807135409000c4d19100c2c803540300065242c0d0170901800701d110f071a0541c441b0305c0040070442041118500162215240740000c01110180e024141027018031b80c103240c0144164135 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 562513821 1250 562512571 562512581
    0x1b031b060f05010e0c12060612150a0f1a0c0709090311060112020d29011d0a020703201213091a0609010315120605012112031e 56
    0x3129850004009031620006021250b068016039a040d0000c402c1160410088084495442e411100c608551361207100041c0305106000c20440d52803148418001d0030003100002690a6604840400500e41c6891139800e02070794038401d03070141c001c5c60340100800c500d014000300b8405180b84152030080340c0369541e11044e01d144650440016608031682400701809201103800f500d51141080381c85c0500d900042d490611000c000741082a0f03000390070f010802681035281c5484001980d4000300e40e074903030020000c001070120458001c40e070b100c0000c507840d005100300d4550a5141d141e8080c040031001120083ca05928481100b501c10070a540b4000000c480190074900e80106052050904242d4400141c0e10b42681681941035580a01102c6641e11010388005200030f10300000e03001c0325808101071600c201c0d0310081190036000326840512105402003416251a001c1c2004880b0858407044102c0d90111005000107a08034158120706103e40c00000038500003914202d00c1414128a05041718 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 562515071 1250 562513821 562513823
    0xe01020307050d051c20090d020904060c0f02011103010e040c0b130f081f0203090102071a040b06100210020a140d0e121e0d0e060403030e1c1b031b 65
    0x1340011a946061140300048042031003140082031025070fa000024004007a00c90510701c0d590790380421049690748404642c82c03900c03030300200807400c2401c00307040c00c82c010102d42181c4030001d0095881030380214014081c100815540001580c03035a0301c3e014000c1d1242d84040c001f25150940d0000000f00149180058540c020203015910f5405140043c0c00d40c041400b6030010710150403000c0c00780d507001030001840c903045840c4180035035240c1d10f40b81c646009228401c1d00429061000d82d401c1c25210000b21407602c82d61003030860454545607282004a144080444840182c0c00f014002108406c41d070054201302145081049400c1c83c600c08034542c90f0049401041c060303594000e4944d00c41d40c100071040b411601409040e25041484400c8882d00b0051b00c000d400200000400004c860794039841000c40e0749940c01690400c0c1000d142c0140504080c0214004a10030f400545412042d00c030001ea010714042d803aa50b1601002050032090100c10344415028440d10121201065040490b060501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 562516321 1250 562515071 562515077
    0x10b0f090d0c081b04150513091b170114061302090a05060703031e0c0c0303051b03040f063204020f04020a0f110a0f030c0f0c1403010b1f0e01020307050d 68
    0x14070703100080c04100d900035000c2030103520400030204050b8075a0208120320480c2c8c0352002c10680414104218882c1101c0d00001d031018503102c0c002500010303200c5495850a19000a100002c0c00d541c5600c80541d06039403403036010b5412081c1522004945d4000d021420014020803803440e40d03000081c01c02e801030f03002540401d8a510307280d040f443c03e0b4015510000d0300d001c0104003028a182008040d03072000e10005080c50f0b078801c0841c511100400b04c600c0c00319108062680d903407419241150303680030001d01c116145800d001c00c1075484516083c0c0b01c941482c005c010150502030084142c180a54080c0069810101208110300b40d41c8840c0018501d548103629100d500c2e0007101c2000381203010f959401d030025000b0445440024128440032152550940781c15041ea40341030501c54001000b0050042c030b0402038403000075202c007074191070710300b220740c101c000f0814414000203108840391100028600c0300c102c0c00c072030078600c0e02451100100c84410f01c100ca0030b00030903030350f20361034996003114403008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 562517571 1250 562516321 562516363
    0x5190902040612140103030503011811180a080307150203040213090b011505030c0406050c030c010c020d1205060306190f0203040c03020a05010c0302070501030b12100c08010b0f090d0c08 82
    0x1440341e0144c0032119014103500d0140e0b602d0b40c0c07002000c034041801941040445404150703001300c066001414140058003c45a590100c8440c200030000c40700b001502951a007400000c109202000381d6103815000b480000300b9115450001d802548010000c07030f4400f0044250510101d42c5100d2064058841c0d0002c0c4619414000c842006142c1d481128040210400402c10442d10020990741111a1402c20399210055070100da4154002d10007443d910398070302030328118095400142c0075134094460701e9101d0183d40355004413090707500498074160145d02c00d40102c0c600d5211000d080c0e100b50a0035000140a90161003050300366031084e2015542402c64440600035850158a504c00501c404d08042510240c1c6543c060340b15003981c03061905146d03a904200500751642c44100305042d00102c1a1a40220014005401400c030f1070303000c90019000400108980010408544020844503441e6080c04241c00400a20200030442120689091080090344540810101c00d0526a0803e0b8081c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 562518821 1250 562517571 562517597
    0xa022e1d04110702090601021e01060f32060904090b0402091302013203010303030516022a0a0b040b0307021005060907080618100f0509060604051909020406 69
    0x102102150041407046140c00549140c00c0e058104598803242e041c1c0710310714103543d075000503401c01c1072284011100000014030004117640c107502c101c089d51000700040a8642d21201128800120f001c4040d41440d0000c0c0d0046c80c1442c11003045200f028014010740c90310800748045026074005903000c031a2295280d042c0000c518000d02c2103980001501a21118001c85400003055047c0c4002ca0490342800302e6111201503101c5490000208443d0010b9a82c03035960b40b500030300600040b181200c0b8500ca80c55400005440407078000340150664400410044802060840901003246c980d50302008145000440e04180c0d0007510081440c4c00c805500d9181034480682021085000f1142e094034141c1040166540d041140c0d03048129881c102c1c9c035660b02c01001c546a58180c0078840c2d140c1843d07004010b901d1036610b500405440e840d0001507211355407201400f21020040e039549900910904c02070040b17091441c0743c500c03040051001686e03050343c0c890a80080ba03005070412800a104a40600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 562520071 1250 562518821 562518857
    0x210d060f0b13050d020108040221031303021e030304170109020a080f071403060f0a090209240303031006181d0f090a0c050603060f1207030506010f06020a022e 70
    0x142c000c010580741420401d046a000900003180100024400c003000540300e04c6114840001c000340c03107000002c1700c0e0343d0540451901b0b050140f9100480c8150300060800e01400d0b00100c0d1403844d900b000c1c0041d418142000520541d59004045205144d962014004003613035650402c000100001c1001d0005001c03032680d0a07007400d040b9086224814100c400c008010f44000450700c0d1711409094601a0300e48980b010034000d0100c03400d0203940461f140c01445a24426003100d030850700c040800b12119070f4004000c0c9070305c0303000451301c806d034500c2c2c1d45800700440b601445101d403105170400849454a5260114503203000300e81c01d100004c2c04c2c003541c100444080c26400c101e07004450b000c02080194883e980385a1980b400d0300035076008140220204e04c1c030745c031644000a60681d000380310351030a81990043d0760740c400c050703c4286c44038400c2000010b104500c10710078409468240e80503100034a0241c003400344d051002800c10418949810311a6900a0826a4110088081e55910b201810015514 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 562521321 1250 562520071 562520107
    0x90901150b031e010f0306020913090b0a1d03190e2110110d150807090e30130906060816030b10030509010b0303030f18210d060f0b 58
    0x1c00d40020440f00180601d59580205000300c80c4c0c040405079680700c850021400e0070302c4c1454001c0946041031120300400c03401818041c031400116804014003032030612101903880324030302590040c1c0c2080041c5400c3c07a990032814104c0f0313000350a110025815140100d541032046110700201c0c5a01c40b1168a03100c0c3d0b0074818800041c81c090014440302c6044c00c00d49001d482113070f01c2c142c25141e80e07241041f1007540b4131406034018032805c015221901c5d030b12215072018040300741551a240c060f0300354070351a030f00103070050401450b0f519011000804440b110002117500039068007110840d46000003e41070001d010b000b014062a0b03580e0049800c010045002170180c01d00030109050400c1082032068590250500f6541003515004c90a41c9034903c206004003603404000d42c06000020800c51010040030308035001e40a041e10782003001c04898103040c4c5456055003561041c0e0184581ca051008808002d020400404480000c2950b9141d02e02e5445059581c03225000100202c0d143c102e142d640d42071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 562522571 1250 562521321 562521361
    0x90403050403060c081029040f0801050a05010b0412081603090e070207140d030903170703110102040b07290f0105130204080a080c1504032f0a02090901150b03 70
    0x1006150703042110028106d0f00c5103000780e031070b2142009012014104803003214a040e0005030203d81c0d403541c4641111241e40081d0041c4942982000d001c11558102c0344509412240c06540305030034242850b150040004011401341c4002a041c00003051950170007c1c44201d0360300c40e03180c0d201c0203031030500d5419201000810520640d004414208540d120701640c03000c0243d422140780c00300001c0c0d8501902d0342411500081c10075440e40304261808045440102101d5000382c856500500c00d03100040c3c02c0c0d108034080d240305000140404030000300780500e15a0303068040d240c8511440c00030348481d456040104d4144490500040040200741025032a03a03002e4580441d00b545860f0801c0103c540c3e9221441000307001c44000142031901010a2200201201280c8042101402d03d424014044030940501c10007103031911004204401c102c51200444030f408101401080e40c2c2602040180c16009100c0c2259540f120b640680040c0050b0b00c0b41c024050004c030b45134890030001c00c210b04028007220 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 562523821 1250 562522571 562522577
    0x30908030c0c2101020d0606021e0703120e0409030f0e06070f0803040507080609010f0b0919090501020c0717010b040e150405010f061202040507030501061704050c090403050403060c 80
    0x1031000d5480700400e080698107400d444035880c3d1010645252450302081e80d400740c16503c042450418100c40e0b400c9a01110169801c40c0d005080c0d82a080a00b142d6180030b0a01c3c07a48009000c03c000381c03980c2d424201103100f40c204840d00d101c02d24041000e464000c0b804400050140a0703140820b40c00101d11050b031102500c50b42e00303182d06541da28a00040e11800945111404400501046000c103c18009024403100f542c844c1c3c00c251542038041c01040030060125818404203459505120844a200c1c8a031007401d174040b042c560b03110302c2c003c0c80840000c1d65035540821004c00c0200381045140001c003051807400c0901030903251581e084074070304002144603500780a0100e503010300c001407900141c641c0036100719030ba032124500a80149240c0c5081000503040260001da580010141c1c2c0c4449402520f041c031803a075030300e00124100d850074080e102c0441d0691241440d941c160f00c0c80b0aa20511900864140d101d10702c00082105c3d400f11030480000320000350038000c000160180000b041c0180c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 562525071 1250 562523821 562523827
    0x40906141e09070b03130c080a110907050f130503010e07050405010806061f0905090403121a130b0d0503030a0501180b011202071b0e07030e0303011805040201090f0b0703090803 78
    0x16400c07500c503540c44c880e0f0100d0f11404004240061840400039410702c0c0e107c8a082c3c01640e48250841d2240040342c81039401014210b041807090a000c1d880758807e41082d0346842c03a02000303041d0701c800e07900b140c1caa01214200004020420b42c50074881c0d110420980c00040c80028a81b00c00c00041e01c405030001c031400d80010051000b42d80321030018020f40462203882c3d60702c0c1c00d001e060807103008810303071302469000805006010504d40c000c0e5001d161f21850010600485080c15002c501000121100c160440300b041c1c04200c0981095015208480c0000d103000000d2859484091454106980915100d03907280d004110844064100030b0300021010f10501c88010b19000180440804403c0c007403086400081480412070000d86480c01281901140b207030042d1a09440580610100c404602192a04250240c140c0c40041528122042d00002148003524240d4150103004090300c1203050048802d40451a0080d401020014003254188280ca5040d5810000c1154040b540901c1d160b030020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 562526321 1250 562525071 562525081
    0x3060a050603011104050a0302010e121c0f0206070e01051b060c040609081209060304140a0b07180e061005041703070506060d0305030a1517010f0507020f070e06040906141e 76
    0x2a0421230742c0900b401c11450403118042a43d0218000c5020900d001d844050441a13060a20b0b41e010394003941c0c0d820604002074607059030341c4c0e101a0fa008003c6844080319511940c401c400810401e82d00c094100e80d05244608560b03c0d12200b52650001400042428030a50b50f1122141c0000e05080000b00040411404000d10521400019a000750340000004003480f4401d010400074864040803a1510708580c10007506100040d610000001c3c646106030310046181c402070705c26602d02040014954450300200001074818a071401c0c140042404002801250201a0b10643c0c4042002d141e0329a04e52030701505000c002001d07030744580441c0c0450300209500105480e80002c0303211000800c0a11010f94400002965004020325410102c0c4000b440c40e040d002441106801001441651200d03001a82c80d1031210517601c409611040d8100f01102c0307148509030300090094400a103180301034480f4410b5a62280904811a40703d9040c401203406102191414030510400e01c00300e4188 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 562527571 1250 562526321 562526329
    0x211213050f0402070b0a0f14090619110409020c0a02120f160b070609050f01050703270512031e01120308071103041208040b1602031203090a060c0c0203060a05060301110405 76
    0x1000d412070f45440d580c1e9451f580000943e600540410011400600a51800f040c0f5181d03160740880c0c040c600074500d201c2081c4144454010322110040082110341414100501d0300d000703412840528202d44500d108030b02c0903071104102c0841c13030420507029041e41c044001501d880d100011040c40c0060010090402840409905950481e40c1c0402c01094880c02c9080c507038a0224040d880d80a0b039440d20061042c1c2940584c0303c0c6600c41501c2c02d140510040c40c00300010074102d00383c00900241c00c21010701c0c2c2c0040c0524029640281c40e02030f040f003244800c885804109000360485540c3d4010078a040e420300d03810100f030700c1d800103007803401003101030f40c00b0780a40e03ca002d00d1054000000100f603010040103a07020980b009460721241064480410441c4d50301400f003110020781c000e00600300c03440d0408044600312403044885d40014207134000c640d625a0010403242c1d80443c01c010000741c2d04401a80c05201c064010034545a000c160f60510306c00701421109011611a01d4680400c000c20468032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 562528821 1250 562527571 562527593
    0x60c0c0703030f030f0518100915110c06070512010e06130e07180c090605071e03120f051501180e0a02070210080420211213050f040207 60
    0x1506103000b034004070000c83c099000d4250b00d900304600600341030400c1040008425030b02c001c0c410020886e1411210408070008682c0c103818003070201c05103000f0140600b07910742c11080700c441c43c000c06289001003840c901b0f03003001d00139200070703001a800140c134401c100c1100030150b0250086000b90312050030184002810140d081d0154054561a005078110751074040c0000c00041c901020088034000d9400100e0006054412041c404242d6184000c00c4d4240720b20140d03060070380d0140402400c403240b50f00701140030701240c0f0220108540c0c3d240301c444003c002c0c060001406090080880d16080075190313040140a000c00c59410003840d5084007502d05118a0804116204511480c426898500e0510064405c0c20406900400d420392b2115016a01210b0700d407180c0d000380349014035460200d00c0014504070071421030754042028039000140f50381c00c01c070004400c481707031044031a40c1d140b00c59201c103a900000c443d0428846916003c11203401d00e0140c00600e21030490f02185040019a03030003040300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 562530071 1250 562528821 562528823
    0x81c090e0c03060f010306052206090b0d030e0a09090813150f0e0d05070b04030c05090601050f0c0109140c040605043c050a0c020c03010c050a0c0f080403050f060c0c0703 75
    0x900d8403103000d4042c5e4000e46c446805014041d0492085144c0300310742501c81104410900318261400c50009030a074803901c100720829400401d0381d85210b5540d101100d480c00058025a8403e4010b400020b20710124424040c0c000d1103440550b8031100d091503103458041c03150344088011500301c03442d000c191794400c100f0240d41c1424107014041980d2040450003c01e42c0b00030080c1140320300503000c584003091101034030807a40300e5001c2410198648042c041c000505440d828046038041c00044461401d44000d0444a035148000051507080c6464001004255000c500c0d6960081c52085084e0b08080c015640600310070740b014450300d950300141d12414181a4003230b10051800500001c0d54180358611945410000c0320305002c01e0070301580d0040141190089400544108200254942818080d01c0c1c0c02c25882c0d25071030704200b1400d0301511240300d07100b4111090030809815000243c40000600083c0d40124014441588041c3d6000d10b00385002c0c00c1034001c030809000d007490300b050004e0079800b43c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 562531321 1250 562530071 562530079
    0xf0601051602030607020309030d0e06030a1112010b0406090509040b0a02090102030d1e05090613030e0402040305120405030c060301081c031107260418050907081c090e0c0306 77
    0x24040d908070240701c810320300500030340c14080c00080c0000c0e154000040d0072034007411416074a045003081020780e60368000d0500113412083c18170019840c480140d100784250b500c0200e10341c0c030340000070644c080c503014242c01c20b0301c0c2c0c0000894180407480d441901e09002c2d150541e030f54403031420a61120505d4010060a40703000980001d600b0b0041c2e4421b2041d6014060303008420301283c0482c0390004a86000075280100350341c6000005130380f2a4000a4482c000c80e074007000c40c0c0440396130340ca00316110a41cbe03002503500f0507001c21001002580402000c0c1c0d140c0007240a10382c845d41008201810010300202c1c20b4820742080c0010310002c2004160320403c02d888012044441e0103d100c04d6000d001c6a000103980b0761008100c81c014092003251001c060b81c08440014022040d84072552102e0040e4003a4513690801aa10000d10103803035807082d500a41c0c404116840150b07125406464411141002c11001c021104200322440d0000d4035800945542c0c0c0030240545031050010655000040085d449 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 562532571 1250 562531321 562531327
    0xd0902040b060a0c050d0504121401060f0902040321090b0d06030b0a0b1305072c060705030c07142b020303030a02090913030804170c071214060f060105 67
    0x4555540d44004141480605590f0326010096000703014640002d1082e212405000c81d40c5451901c140c0840b025910403011401c4a100b042e22503129803003181094090640d030710200402d540101e02c94450040c02510b0002d0b80d40c4d800d40c50103150f0800c02d49034010a940007001d892002580041c02e03481996282c5490035101d54201d0600070103042242c0c0050100039108e0244903001165401116281d4010f03100c05290800c6071445030200c56040714102c00007100d00306059040c051003003c681c1d07405002c5020b01180035a54000605661010104860706d500000f00782c0c010702c01c18007015005040303007482d100e50000310f02c0108905403d010011101001c0741d441900080085100300462142c002d41125203d01c1e00c121100029400030101c0c81c46148107200240c44032512a6010000c250300d9603800001c1e440b40d5450311610441d1034803821044030140602c4501e400204540d800608000c91101c0d284455400d292035110441c3c128802c990b04060100001c0750301200b010350304843c0a02e01156 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 562533821 1250 562532571 562532573
    0x1507080405011e0903020105072f100218030609060603070306020318070801051f030c060807020a080a0305041415010b0c0708010f0b0405100e060d08190207290d09 72
    0x4010b0410791420003000303680895200308612160b01c10b00c035080c8aa0000c02031500c41c400181c98007041010713a40c0180003d040000d07101006408442b0069150740205c9018400c55205002660082904500c0c0440f01550b1484549010010b9a0f08640710a000e0845803d00d4004284c4482035400301402c0141c0002c00b040340004c4001c0122100307402c0ca0160741009840d2500c0d0350203003a003601c4060310352040d003244500101d0200855421240d104604940707040c5043c13003e44940340010b003030710103600400c1d8080020461041c001c21000d00c05560000b014505840c002951080c034003541c280980c080300941c1c90310000029031505441040c07106c60b4403000c550740301615000e199013001c0040d500b0048540b902900e5074104d10400c1070204c4083c412580c4940c1c84071b204c420b5030311406640e070b840140852400c2c2400381900d0a0a4051184945020f01c00889000c02413180221400141d1090130100300785000e200c5403080034080c0402c100301b1554181d41400740ba004004036200b6191761944194 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 562535071 1250 562533821 562533823
    0xf01110309042310030c090c020319020a0f1b061b0f11061c051302060d02090607140607030e03030907051309210908070e010b09040e100c111507080405 67
    0x551426024100c407002850b112044d25200349451008481e26000313071a001c43e801200d0b0050a010507031a0340218186260400b05d815172042102c0a5401c3d4012101c244001c9405401040600e5016401c420007540359207504001c418000d500c12400c108228601000803e400c54490b21040d800200a0048181d903007003500d21f041100c0c11701c580c00b02d80040c040628151400c00d0400002010700304104079170340c02003c5c4000d00031a07140203510203070422801088415907405441d8550018052500f072040daa40c2e0201d01a00842c690402ca41c4202e0801802d243e050040914115012020350b0860078120446a40c8182d10700806100b07203000040910034902c168480e00d2156004070b1405c2640c8440c00d002d4020410340340900d40000c00c001404a1452000a8860101d84001070b200c05140c1c41c000c001020341d04a20445503000d5103600b800305074040c5c100000c205a40360248005840104c095001d0400172000300c001d900c5400c2503002030035400c064544540d22189a003007244081c0d613186452 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 562536321 1250 562535071 562535111
    0x1205070b0f190509010603020118080706051c06090e011a0918010f14010305060f0106050d051e010305010614090c04030f0201120504051c050313020112060b0f07020f0111030904 78
    0x400380510700402c10134034103415046901160b0007071b2246481504100b5015280560a001d241040d9100507820441780d44a20001e00c02c500800420061402c427078042c40b001d40d401a4480459580c41d4402c00211150a101d0144041c6a00320100c8825030040b000c500000802001d084085036110640c0701d0520702074000c165084011401080440c115072041426020203010a0391103100d82c000040d00c40d559030300d05905880e91740d101c590802d40c078100304101421005012040202203501100c509001c0507020303034040d510900006c100f80e810000383c80481400d040200340f04031a0602400032454100c002c503000c1e41d4101c6000604510307540016200c00c4003079803001c1400b600d45010482407040100b491a40e500d403e000e18100d0b02c0c0c48003801c481500059030143c4a10f101c03040e054005601032501c6200712480110b000c030303002e591248a0000ca8100c0021015000340024032101180340610b03010a4410302400c0414807075180c0c4810594031302a02c1072043c0600c2d61810034034030b07884000130720f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 562537571 1250 562536321 562536361
    0x9061d1018080a0302011103070210090215130e0604023405030a0c0605060f1e220902150301080d052208010b0f10050d0f0204150c1205070b0f 63
    0x814031000395103a071503e039103414202d0300b5001946441c6043d880d402c00d520850380202c0c040c1e4010000308004140c000000c14100504036405a511062a05400c01550103440740c24006e403454070000c0e251a4420f0b645800080c50380e440740d4810441c4401c01c038480c2e40c204903400e04006c0c998a51100188102420a60003100030381144000321305040c01a0784006034501092054400380300c11f846400a0004143d8118205c41d03115142202c0394000c0c0c00d20044918100c040104083c0300740c0601c861420410621140090b0650b855040c101e0075410085c003440c842002c00780c8690f1841d8904001c2036228103901c0c907410100301000540140300c00c9107583c40082d2805103010440010313a540c1e401c900038920032a00740d0243d0311a240981881c500300e94a190300c0000b58407410315002032264040001c0424102d41c010803a42484080b4031003c042150350311464241c1c450030002c035910305200c0c14050000c3d5540081120400c4140001017444964503040f45600c0800320141d00e59642c100242004858 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 562538821 1250 562537571 562537607
    0x16020f1203100b07080c211204021315051906020715090306060e27030a0c140f031b19030309050a2f030601050f010810121209061d10 59
    0x2801005d0001c5c5000070316498200360201c540d0100c0100ba160002c40b6200740c40354281134180910800c5c0c00b407880355268020300c0208031000382601d14201034115081103034641c11012010005021908003d01c0012903c0a40e18605040b0351074201d00950760038141c01214100f504682d04c99801d02c0c040c043c9000070f1a44400d060100c943c07182c40380950340200300e07406050701088030103c005402c0c01031405a40340c0c105101540c42d2007441d883c01c1d900d5180b5808202c601490203442c841d41d81909104d11000c4000c014061a605c0700755180a0640c016403070310054a94003c1d000402c51710b00011101da850301c3c4d150401044501d00d07403e1040c140454444080d014a5811262251080700034150490302c10b19500b50031a0990414241580c030b01d07090040300c1e0070501c41c04c120000d0750301030000142d0002c0c0b0f40482c4800d0540312a0101181140300c8030071035610900300d041101294114049002600c098505001085245071000340c2000204008502580c203140c01d01a91610403400c480180542003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 562540071 1250 562538821 562538827
    0x30f0a0308100501053406090506060f18070c0602070b070c0201020f01151809050709020304020112090b0f0a0e0a0c0f09050103020604090c09030b0f16020f1203100b 73
    0x104014105000c121606000e1011002d000b1800b58004c0003900c1d03194409038074140405548102c1000e080141a042c22255402d0b00e802e030000442c2030055401040c484c501800351400c00801744090103040c848141d02c5101e41c40c81c4c1c03849808426042580c0820189441c1c001418541800c000074803a041010741054103400800503030035080010641018802e900711074000500c003141d6804ca501c480e0314a001034116140810402c0d9900741d0b800c88100b4518800202c887c95941d80c1458120346038481e01800350048200410342da00100403001c2c0500544041c0045080c50340c410491400050008401c0d807608808281000340c030340d008001c60b000c0e01d003c0300c018000d00c0c1040c1003c070f1680d2281402c10790402c81c01041e41d080c40e002ea14126903018098070304150030b011455024110f80d500e4030003041500309002010811903001c10340542c00000d0b40502604000321000c40b80941a91400e040d5400310320b00602000c1d0001b210960301002044e01071b12511401058005524940e001520745c400c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 562541321 1250 562540071 562540073
    0x1909030c20010e030714090a0f06150e06030c030109180c06092903042301090c0306050a1e150509090105090601080a020a0e04020609120d0239030f0a 66
    0x901103048003078241c99084814020004150742d4040900400c02c4404111032040310741d0500d11802a008449a000416100c0160b01036104461460380b00450880d00904002042c0313420814200c022001541c50078550f14289100351403610042c4151300c03400365a401d85110b09000c1e4050704200030f5000d407a03c00c1080da6058000c142d1842402809a51038116000c0401c4800710200202002d41640c441c5066513526102d40c00c940c6081c2d81548000312000c07900c400c914400b80700b01602d15105080030861981141880c82c21110020104803016103040001445d41c1c54013619280d00000450010500040039080c2020709500c82d13104a803c402184244074501806401c002d110740f010b2021142c01d030f0f90342d0107040d903106040761020f904614540b400340044041001d200d54400d0010305800c1c03400003004085820665003181d80ca8190300f060281d00181390f17060140c007802c590b048011401c0e441c44002d02d1501039920214071303044c3c00d444581a08450303c1c2030107109002918041510162441b07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 562542571 1250 562541321 562541363
    0x20d0303051b160305030717090a060c0c02030714060408191e030909020d060b07030c0203101a0f03120f090405070903030f030c0504080d02030c060c031909030c 71
    0x2058580c0c00b0b44000e07001c000c0719107030500b4058071410703001d403006100d21641c0c5071000d0f00d642d03002030701700810024490540c0903102085101d00740035885a4000f03001010183c2016011980d2000c0200c0400141c814014056074000a0541c1a11900803441c14124003079000640603200d241c0c002e9041d80550000c0300c4c442100e000c0701819a1380124407a9902c40190380b2041c0098a01d143d0040c0400c5000c3e00600041d58560702800361808014130006400d602d982e40c28405e9044030b80103c0024006010301d03c01c41c18103111000d07035088044002c1c081000b0500705002070990428503940950308000320f4000c1c070764082001000002e15010110366804c0e13089100e461725405003580381e00079070602000c900000c1c031900c82003003201c3d050baa840107101c2403120110041c0200100b0001005030500010590310401d03c103400c03802034560025a56200740110072414000010314512030414140300b04143c40c0d5100d49121aa44d0410a00054468103883c06840315441103c001e080c91212480f1200301580c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 562543821 1250 562542571 562542581
    0x30206040b0c030f070e060405040e0a020307080f07050f03030d060605041d0408030c070c030210090603050109060302060403030f170c04080c030f030d09050304090903030b100306080606010e0d020d0303 89
    0x40100c00e98180c0b941c030a04642064401941d1085041e41482e001a40540c42412403070420303000101890320307155032240003606484e40c100c2c8038021070f0400c4003c00210f150410036180200010f801800c8080600c41c0c0040d19680d00d4800d150140e0610050030300507980038412600340c7c94104208018080d1a4000101582c03c2400b580e603061044a41240101000003900d81c07085600148031880c50b0340f010014005600941c03006c4420300d54180010005030b80e103c0c001c00c02070f413543ea642ca01036403030300c60020150b50060340500ca02c0c40c900441800582c5134107080b82c0c2a00d41604100320109101c2008179208280c0d9800f0a8848070200c042c0444da04070302000300704880aa600b00c40e00c52146400300f5403103841071880c00343e8560003040300c1d03c03c0e0310a0b5006080024010003d0b0781c06c10b0f0740e8854101c143c501120f4105c00281d59110030013110700d84020b200c8000780c0c15117010052941030003d21551080b014000a040c0521440c0c1407065036180515060f0322603020f81440b01500d40303460083c010380 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 562545071 1250 562543821 562543823
    0x12060605030117060c0d1e0e0c041401080d03020f130609180b0a14121506040e0604032307021807080106030b06040905220f02011b11090a021603020604 67
    0x1d03070480404260640005100c0d4010b4150340c5e402072074803806103816001440d0b192003480ea40c440c00071104003000c5080c483c0200c800c0420f80a05181c0d803103082000101c034443c424850000703001c600144164800000d0801c00d0051905005a03503000410105c000e034060811055420f14074158007107140c591062000341140c20fa0000311608100b03140c0c0390070a40300801411600900300700c0c42080542c5280d0420b8003424005050b2082215020440500f01461008140c81008584080c080241020322613220800600740103030085d810203950003030403640840366003050144011801107000300c0364400c48441c10b81c000c061041940305514154503201c022559040420040000060030901a000d041500400145098a410300340301c1c0c088010400903044e24000506c030107441903205602e010118055000c1e160740c400005142c4001010703000354011012500c1e25055240002920603071021080038030444011481c1d58500300300d4802402004c07040141d405000c080c443c20b146d00480d100c1d0160b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 562546321 1250 562545071 562545089
    0x60c050c2e0b030d031a030304030b0f010f0509040308070306150c0302070603020906160606050603091c03090b06011b0b241c02090709051e040b030c03060c0a120606050301 76
    0x801003140080080710300c0b011000360980c01920654000d184280d0040002c002e02d200d052608203901400b091944d00503800440f46045080c092013154040100003030700419003100704000080c186008190001800340005080c0a554404102101d00a070070000190213400f80c4441c03d03241042c0001c2005440c02000da01501500c0c2012440b50310a00840b102040c020b041c2a103041d03c051074040c401d0510900035034120b0b42d1018003149a5a54000650040503c0300007031026140e00415a46142c0c0742d03c42210a25240c98901310001d001c80e80b80a034020f000342810410bc0e040d240c000303c0082411000104040d00d01801c00203c085046041e00035109406011803002c2a01e10601c100e00c0e10a802526207228604c0c85e110040c6000158198440c2461400c246035907550b40102d181c64001d580131201c50800300440c4001420039100c1d0381074058048000b04180d03072500d80807a440304030140c0f48540604c03000902194441c000d60701e218100000e000100042030740d45100034910740083c0901440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 562547571 1250 562546321 562546393
    0xd0f02030c071211061b090301020d02042111060304050f0a05012013090e0a06060602010506090f060f0114160605060f032b0c050a030201060509100b07060c050c 71
    0x4a621a44440358100002801411141c44045aa6413008106c001e0a48141c108025041c602e031428009070240040c00e01c8007503111400c03c0502404c1400088400c01c200c01340c03064040c007080120300b2001402c0c0041c1c50195030b0340c507141405801d1403203054501500d88180d1010a04000301540b0400c1c10381d1942040340350803124810540d500d44a10f03600120145840b41040c028804141e000170000c0c2041c1040b1081030b0125942c080a03a81180d0100000d40d6448041051a040c08581c503a0f00c0701c00e104004540d481c00302d0016002041b0350711aa07040050701c800604c81c082d00901126422165a1b81821030b554042c0351031005000c08898403405805803200c1c2e0159810002007468040c0710350703503101980c441181100843c040000350180204403400024401007031050048118640c029400803e05904160034092164405880245401712082d0100035139001441940d440c0740d4411382c00310300745500180840c2c640c002c01711800c800340110320010b51140c0340b80031400d890b0704540d0700c180c0b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 562548821 1250 562547571 562547603
    0x30c1e0f13030b06041107020f30120306010f120612050120070503030a09020315010b09040507020708030a03020f0c0f06041415010620120c0c0609150d0f02030c07 72
    0x8140c5280102501e8050b40c00d2007c10010300c0d09080d0758402c403e002d0081e807038180a5038004e0032440c010700b200c650388040c404030700c0107121418450765507400000c030901851403c0c0080000d24030141c80e1500000c01507040c03410704111082e608050001c10b0711884070764116495040c8140201000e201242003508482141c036001c04401c025295100c0d0010040c3d401d507a915107680340600b0030101d0803179041c054100700a81c4d4122060156010b880701240060320750702041d06100482e40060081000c1d944203600400664070004112080240f662501580783d05040f90052941d0186030210502400b075450b06c440d214600044031403040b4002c041003a003005090701d80035140c40302081400d603040e288100501183c2c3c001d150100704001c424007150018950300412038108901d0149100030010005141e1010140c100550048048100d03800c51a01d81c510700000c070350310354081c0590101d00c408240c1b900240300300e0340b2070045d0130f414000a5650b880c041340ca0034400d0380300510440d908483c00d41c82d06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 562550071 1250 562548821 562548829
    0xa0218090402090615040308070b0103050c09060901150318030f270b0703020a0b091b040e0304260a0303020a030f020c07062001090c0911030c1e0f13030b06 69
    0x15000c1d6030040c1840c462512104180104403401c206044e40556080000000040c424001810041d010f03040c0e000b010350451515505008442c020680b142d00c40c0d4003440702036524040307000e04561000c0c0700c5064000e5400c0055003c0c1c10141e4145250881c0c046a030022f1540207002c480d400c44260b03a40b0028071855800c1c03c201c0c801086201d804c4503075503807410f00c2444641d074001d12140b030082c01211100d222a03603400c0c41c6c415048442c105180c20420784000c43d03000100b09130f1404201180c0c02c0c000b10b400f0004080e82c034000c1b0b12035107080306600c40d86400d0240e440040d01001340328080c16036003410064100035002c1d40c4480c040798006498440d411180c02c00e00c0c401c0d02c0300705642001420743c4c0c40c90041c0444071070b601480c4003048035403088800d100c1c503a000d10400c3d103200d126070240b200952500c00e2800494041b0304407134074000402c0003000700345980700d0111004102d060040c00c1107140c00c050800f16500400310300504583c0d00017103a260094100140408882c4241101062503460000780 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 562551321 1250 562550071 562550089
    0x605040603020703210c02010606020f060f071701090204050f0a0e0601031a0a0906090507030e120c03070c09020d0e07060c02120102120f16090501090611150a0218 72
    0x14406000a0040c03034802d400502c800c41c040d1400c0c0200559003901c40401c00700942c064a10b45584203208102e046d0203000307560042003940050842c0c0410311060544445009014a4020100030000360b140c50041c03001884548501000c24103940e11140315100a62041c0941e078030a004003080c10445140c400030070400d40f042c800c07484610342c60307007001903018241c41e50f100c01821400900d842d03016220318010100500c00f0045c003144e010700d0501014120340d0060004004c050810880300358588002400b540706805800003da5038401012105086001e005001000511003010018404002e07401800c00f0800011040246a1006007c07517a258460b00c1040c5c00b16224050310740140c0381c0000c214a0006c40c40e400585044585041d2800070103084500d00072100030315080c8143c0c03032018145009000e9540c18442480b0703080c000041c00ca04498801d2808018440d49050030780398007444000d2102908502d0b408445c201513008401070341212410b01c00c100903034100100a40b500d5030340c2d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 562552571 1250 562551321 562551329
    0x30f010906290a0c021207090f020c06040212101d0c0a06020717010b1302070b09011116031101050421321603120b04020a080f090114010905041209 65
    0x1031100a41200202c06209410000104081c40120741c00080940c40d0756992022040f003d4000d0040d0301c0c181350b144002c941d68030590b10783c0c84c0c2c4180006d03065007000081d0b803034005404544403203840c7c130301c05a890315140f902c040e2a2800350400030402230503507034042d44890035441c036010358001250034014804050391781c1c480c06006911a00003080414407551000c03490003c000000b048503003514000c20325240703441d107a043d01030703a0000d6040c003840b010b40c20403504401414001e128290240441409600807000460655031449204000f01405441c01c2d00100c081400240030f1340c90b150800903840340e80388a400200d84102c500c08090103200d001483d614081c03501010080d0b24100c0a601400201064107400d03030101080681400c003d081d43c822041171083d5a2040303c11101c40b002001c3d1995050128041c5006100f04403034141c100250580c8a207a07500c0409090b40c03907015680c00f40054080b00d1540c10000d07000440c8041440e041141b007075000c0d0002e001d83c80243d40040701da020203445 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 562553821 1250 562552571 562552619
    0xc01020a060c0903081828090f020705011508101401030b0403020f03040b040602120306010806191d091b062706040b09030f06010f0b0f0f030f010906 66
    0x400d580018100d580586880c0d401858607007182900c036510303000258402c10b851074648110401c03880b404d15007002c0c1c2c400088802140c0460480000260035808403007809442c000d1030300c4d01464126503905905803200990040024800840b034071902c00f120b9111801801c03400d0188900f59502e00c00075020f030071952010300840010076840c607140c800d00341002804c1103013140554000c11300b96001c00c001a00c003404864802d1030f42c691400502915104260483d4102010144200506d0380c1c0c0082c0c5141c2d00420688200400b00c0c10321200c240a1585a0819000c61a003002c4d5550306c0146a00c1052069600504403051040d0180c240f50581c03e46a507016400704080141340f000c055104942c0c6801d40c404074a1400d1020103000081154001b600003c801c0c1c00c02061043c0c25190800444c04560080000f41c1901d50404a00b000501424001c46014450003e05079903841100004c46408840c0b254600d91213040c50028003400340c00038440c2c3d10403e8204400800c0364041800100c6c44a44407038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 562555071 1250 562553821 562553833
    0x15290906091210050117060f07050d0b04150801020909100f0b0d0207061e1b09090b06040807060c120207060f0305070e0a0905180307150213030c03080306120c0102 72
    0x9410440c00e00c248814070203140c0980486030f41c00c0c1c1401c1c00389502038207500c0c00443c05143e01c1d42c11b0900c2c0500003030105040510300c40070f00ca18581c0000496200202d4414045107040f407800c00300f40038050340b07100e5010707601000b1400512842e041d03000c2c102c079910032079000034507446540d000c03060b805241c00742c0c0074051b100140403c001041040180640d40300d040000d81400855262882200c1004a440c160700302504c0d04403490000c0ca120320403466402c4038030160359100f82d0100070081d68050094020080c0d4a4100c240103554140c01d45008041c803900722460fa070340742c22004000e444402000c031041c0107087c804158030b500200b103c4041e1280395440103215202c141088000e0040901081d00784001d0360400001600c4070b200a9002e8001c04001003442d041001c48a214032a200c400003030a504148910000a5019261020241e20b104809a140c8210b01a00c001d202c0c4c20741d000a1180d01c1e50381c000030401c12407a0156121300002c40790b9465102440219a490340c0344d0b6075540380184c00007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 562556321 1250 562555071 562555087
    0x90601292a01060b0d0f09030806010e0d0b0901020a030c0c1e110301020c0d0f020f1504050c0d0c05011803020d0f1707050312010b0405060d0f15290906 67
    0x40745409400c8607a1003606840000000603072403c4580c15044940e2680300041c00d0110312500d4040c000281c0d809003003c105861207918028520740d07014112904000c540405203919549071100030829a411000b8001d0b07500303000d82c055000354019071882d03010908006854882a005204000e42e090f0840d0310701040c402142102005980b51180c01c41e1407a840e489100c5898a092025040c000f00100082981c06100700004d41191808808401150301402a082c984000411040c40c40c100c522801c10340d540703861800d1801c1502040b80c01e9080303040c0c0308224090040c005001c100b1a4003e0303c807503180350000c40e2900100c040368000690414104080940001c00f11030b4008402030080e030607045180e00300f440c2480142d00c03d501c2910b2503403010035842041f9800076401801041031680b107070b2401740f4201c04a01c0b18002d04041510440e80ca12404180000c0d41e0422905861000101e2403020340702c2d0b011403c616220714449410028038450145200340000495502480081c075141c149000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 562557571 1250 562556321 562556347
    0xd03060b040603050604060902070503070312021c02090319080a12140105060a091806080c040203070c0f0507030f0c080f06010506090f010207050d080a08151c020f0909060129 77
    0x17600d026001682c522000600d1072062000c1c02d80d281c400c1c806103a8941d41424014400d0f4002002090384600c104842d0000c0b19425080c65400d02e140500503807a0340c801d07000a4105400e0110a00d100b104042ca00ca080003c0080203101300480c946502c0c45c1012003401d80000c80d20348140c00c0d1680d90400c0014002817511790003034007919420b0701c4d00350403d5032110340031100c0001546541a44940321281440454070a00410242141c01c0d00c0031800e514000c4c5008140307180c600409032444001480d40d205002e824000c40d800385810000c441c55510b024500401e484000d03110b07203c1d090040749021100300c1c0011543c01d048031001824182030055180c00c01c046400070704243d1303055110301e100018180d04c4943d0350f41049030091624a0b00c402092502900c00c0324010868800c01e2080001c0d204140c0d00c0201d0140b82c00007000424060f4000c1b407011410200c54019040da1000040040284034080007403c64182c030034800c1c00c4001d0250401481010601d51416900c00040612901c009528 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 562558821 1250 562557571 562557581
    0x18051507081b060106090501030908040b0306060c030721110a0b09010f2a1b111c0510060f05090103151d0610061707030504110319050d03060b040603 66
    0x409044000d1410501982e105a80c559469800685801078001040310310b8110200030024002803c00307000c40d100c0f555520410f440340303000d0b051450324040041403541d1141010703078030084c4041c02129540c480b5404d080440e010345c5441218810002d9400b050074a21500c014149081980d001300021082c40d40c44110200000304080c015669504080705010f619000320340450703034070303655024808911090320443c02c1c1c030304001c810501810402d5542c1b020319a050b80300c2c8858110050481900c0300a0015041c2c0350303507000081024042c41c0318081401004079001c07500d603c00100030031005540399150010030185c0d21580ba4017031100001000450b070301020480400d800c12200080c00040c034042c60325880c1c08000f4101e00b0754012020803000344070080c03000c0041c1505040c441740040408140b1107038040e005150b5010036464402080410020800d8a5442e1500074103545074011035508071822500900001d403114456442014036071030191003a0800d03600c45900451809007401802e801801d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 562560071 1250 562558821 562558823
    0xa0813030315031103240a0e0309210d020d020a02010c06090803090706030e03032701090206040b1c020705060714070b1608090106050a0911041a040618051507 70
    0x2644450300b0700414100c00d0100e5020b90320890300e0070104464507003450710341100b40101803600442c049103030341100d0305240d0702c41c1e022501d035102050711181c0c034002358218000c2d01e4481c6c0c1c01a400941d481102d03c48030808820ba95040c900700c45800246c2c0c0c2d000c03a0f50303c00031940180503030000080d103c00b552080c1030725110706000321400708000340280d423085610b52040324500110f0700100e2007440348941c140681059034502030019801c506281303040b0f5030750300a13003480741400340003000311921070180a411180c13810790001e24032a22550b58401191180e8003040d000c80070802098002d6000030780a10988039529080001040709584e04031080d9100801400d401101c21000e1100d00d0025003860001d600c91350340c42915000e9110b910602509140e0045c7c031041059050100a1009841d8401801c003220280701002c40d0f01d5803400341100040c440c030b070004190800010764804100f08044020011103000d5075030f440080b80d05140319101c0c14414019903500c01c28039034840200025201c09010303c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 562561321 1250 562560071 562560077
    0x160303050d111b0c3102310501030605060f0d0c0c0b13140604122a0507030c0e09030304080d020d0f05090f0d0503010b030a0902330a081303 62
    0x8040c140104440300c08015543c159a2012a80c80014100401c4c00101501c6010104a42898070301e02c1410b0f0a05a89035158617030350110350002c3c40103100000d003e00b91440313205500c4081c0752401d04141804c06026590200341008400186802d03c00100c5a04040340b4101d24101403064502030082e004103c500700c10421180d0700c40001c610b0550025000d41c60320f541d0018a00350754a4081441c121060480080c0d0704072004000c003003002d070b5140b80301c1c0480629001c11090070100114171300e101081840c40440540c0c0003243d0400000041040541340940705480509950f0011a0000f42c0100e81c203400340d40041c4080380010341c461001e4415010105405800c2c1140e0300f076a4811a0002410b2502c00307511201480250300c01802000d0146003880c00ad4200300c5004100640a4441031050b442c8010b000000503d19013401e07401807903902d60080031034604248441d01290075040c420381090390079401610030b4220103030040403110114229154114030390340f10071107090b40340c3e0a4102603040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 562562571 1250 562561321 562561327
    0x170103290a060e0105040c0543060b04150b070203330c0a0e1e04020a1805060a0e0103050402150f040303080618270111040305160303050d11 62
    0xa02000c049403182211400c0080c21524000c95640b8200060340094062440c2801d103001d010340c40b4044800b280d1003080c4c40765044403010f90218030b000300d6202d100c054401024081e140c0811200a00d81918050001442140c103903034100811540d59032200d0000b020201e40410003141ca00c40905441800102070320500d0b481010400c001b0200c6401d4503280c40d202c9518800070420f9a4001038008000312041d0341000180701c406401901d1980d411071040381e08110003150101e110140102882000d04190f403181170114020380010000c0c1d03d1f4000340703200b40340d02007050304000060b03494603a403d907900078901d501600150000d010180c0240d030810800000c0018000024000340950220101d00304d54031451420300034001c0740d026054900c68596030b81307110080120700004581000072000d4401000b003400b03603d2175072003410399456016035007011480b0480205c10406041124040c00c20384442030000a0490040d005030700004021030710a0040603941c5040c0c0c4d2240804590155030300e03103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 562563821 1250 562562571 562562633
    0xb0307200a080703120b0f061305030a06091403190f050705010c18090e030304020405130c0909172701090e01080a110d031209020a091b030c170103 65
    0x414501605800e45914074001208010994401d40903103640543c12420050348100c0c1b40000c4c2c400740141980ca02c01d9501040a207844440c0400c0710b40141002401c503101c030260ba21b00a005821000781c15140c00103482e6110403101e001004980301da5040e14420f400c032462944e81074030760030080140c1104015043c081800040c400b482050b80e4080c2948502c0c10340d034103000f2195141e038030981103590020b08100610341d00d0710001003540e4019a04480124440c0d44075406d0f040402c8003403c001e0142c0c5440c400008654025601c2840c6081c01001e030403100768600714401807507100f00c200801041c1260384804182031100386a40e10b01c3e03030051509400d6207666083e1003038080001c0c0c10403003841c0c10a00c1004d00300f24203203a2012245c101a9002150741c001034502405910b03040c0521030301151a482000304540d40c6a1084c405805514001c0280e4480011803100040005d099000402d10380041c40c810310b401000030141008654101c90b210340e013540d0328107002c980c0c90790076041802c1c1c090784041c0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 562565071 1250 562563821 562563823
    0x11b0606140d111311120f0108012003070c0b040809180606030402040e1e0729030c03070c08122e06050921060a0b0a030b0a05041103010c0e03060f010b030720 70
    0x2850f0305101d0024070b521f050503445284481410380c0551540d038074002c120703003d050a20f078640001900040c8401d85955a8601c00c0e0340d007016820004001840302004c2000f080310340c03406081d002d00b05440b104603003403000000c82c090120560350564003001c148009001032520760811041c1496080680e0905540c548060066002224043c50b464014100501030343c00c40c0d54003400e002100440390407400901c0c0c13095030101c0c030001d41181c1c611400000015040e50040444030407541d44a48203e0361403900c140d02411044098500031408034070402940000400d6912205001000a4000604c20718052042e41c06a010a1080703070400e42814243c5060080c40620403060000381000d8005490012022821119041c8400d4490500c804080c07010600618980703501c503042c0880050907407075504180800751072100c01c1a03030641c01c7c60034500c5055072082014500352001c0e8215103e1340c4800c00c122003025024090f4003200c400c1880060102e138403621303d105c44002061074488181c1d2070b0019039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 562566321 1250 562565071 562565077
    0x4030305180f030f010c0e030a0f150e030f0c2407030903032912030c100903020f100f06090b0d020409020118121205090a14011b0606140d111311 64
    0x250280e9540d861504d54040d0031280e080c1000700218050409c0d00c00070f036211465004910710181500e4000301075010a182d80340e02025031a00c0601c22240c88248c040d01c1280c15a100e00b00001c81e03070154041c4044240311400013111007a50156002d6607594030076100300c0040c42041c20580805450b4110800102240c00341061303001c02050b0f810401c11504420310190a10000000883e6442009505d051420100303288103d500041c60104000c25541012850007000715501d4400d07000300780c050680810715500c0000a003030242414851240c0d50341c4030300b0448400007175407900043e180c0c180500510b0154881d102d0740b0b105050060041400c4940742c01c2c286415002514040001e21480041c1321000140c01000180751509a10300000f1002042c1d00d51510302c02e1001030700078013000c21001d80c01170042094100243d1100b425007801030401001074540340c440c0b1404038215000c03c84280c18400b0400d0b581903008824101551404014001000079500c4075803001d9944010400c2044040300c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 562567571 1250 562566321 562566343
    0x7030903060f060323060c0c030414010e1f0305010b160204110f070b0405010f0204150810091104050a06030b06030c07081e07030807020601291b0a0507060504030305180f03 76
    0x360300c0005e07203001841858102c02400016825000f0b010003035400c50300000b16003c4d11207403080514010600310061303440031410341d000c0354071244901d00c040d1140d00795809421440d0080d50103124a0741e841c41e08485511a04002d400d1606d010381e409000350400303800965004031990122441e01d9507188150010360081101211130707086140034007040c40024000c030140d07605052400c51805107400c2858212188035214503040c0442d400c0014000c2d49202c841130020104031009000c00c0c1c101c2c501e60303545640240216031040c2202000030913480d20034802c5421743c8002074589851a2558141c182154010450440781d01c0c074104404520841e400300740c141ca40c1e00c88034650f82c448002340380c00742c400c0b0b000420540071540440c00400803c0041941c1c0c440649081e070b0b408903214070511135130340c2c140704010401b0204140480801054400050035150060181083d101d5031611940221348500c194400a000900706020071003400e155030320520343d02000103003100200c1441c000460b007000424a0317 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 562568821 1250 562567571 562567613
    0x31a04020f0703080f0c0306040924230405150408091009051f020303071101061a040609090b0a170a200a0503060103020d26071b060507030903060f0603 67
    0x14001c0400d500844003030780000891a0801e040d24006e074862070680802490548199210b00d00c1d4414031980c10822008407401c040400c0c0e1440800390144061302c03803e000d9070303e001c009080d56000c622180c10210700440d4050040d207441541c44c010265007040141c02034600040401c14510766a07925000300398001c2154036106020303403a28082006a031b0b503003885405c40d00d0040e811800d105070b0100c11240d004450f4203003011400c1e030320380c4070500500d2240c100101c608060b141040c10512520301a0007103442303954411400c5038490090f001030303a4010885681000c50f90310140018014200d980108120351012941280559200c0725049810321440712000c0c4503000d0302c001d040c280603002c40054007082e0001e10803549154045030780500b200300040c006419410304240e2041c0303a5001c20403244074049200d0b0700c0d51154180074510404ca44909902d400c0300b540c0011758180280192a20903806803527205c0f4091941d180c5001604850107a1036066946400c0403000401105c45e145000040b40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 562570071 1250 562568821 562568827
    0x617190e030f0a08150d050a03081012060905160e0f0630010b060405060f0c0732010e01020a150e0318040b01020303060a090b040b060f0a030b01090f0303031a04020f 73
    0x1104c1700d05110000c6036801d020780441c01005020500024a602c0e440758149001e800c1c030769842c0c0d0310380003070b200c290006080d84065407800f00501200e40c1003110340da4000d0080c0c50808840c0701030311004160921861070000c0050300040e51035804240c10036480400501364035140403050310641401e04000015280362840c407031850a60140034402d01c3c240c45401d40d40745190a09260004030540200c2d480b0b01e1305810002150300120030180f00200040c4507005a0620420648410740001340800c00404c04030280512140001d61142d20101d1070048180c02501c1549074a440740580d95000d40e4426009a032074042124a83c9020401428802e803c001141c8219681408000c156016484418110b50040c010320209694001d041001c40d4035241d0005003000c482400b140241044c0d91415610a90104101b450411840018420740c3c01542c0d00700500740300c4600550700001240a210201c5d40020030a000007030003640090601d90060305450400c883c518009001e85c1c0c041a0400e490348804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 562571321 1250 562570071 562570081
    0x2040609090b0615040506030c040806090312220809030a0b0106120e060c190e040c1e020a0308240d0f0507080109020d1e0b01030c0617190e030f0a08 66
    0xb800c110380080007140d204845480c60f0040348507a010350302505110314000000300f510030a2450885008050540c1a56403034900322200c69181c0c0c000e40400c2e040d02c02044000740203175881802140817a000c654980000100d84e4640f4500c076001a2102901449081e82400c0030403290fa44950080005a42e181442855058a0070075116645040750071640800c0510070301c41000401d440b8255910012000750f03d4148604860b0700c900d0030246a04503160601d43d481c8141d1083c00d02c0100c0d16200d5442d00d4a0f402000101d80d07a01218030302400241c1c60402040c03101c0100e01c20b0340c000d0b00d051800c1284e803025100000390410191541110222076041200040010604c240300c0200f0000c0c00800400181d030300410b1080b196404010110003032211350341000310409036450500d503008646a1459a120325040504140074041d82021501030f010a01010700448115031003600c0c0707620410740403019410010064401000342412500042c003824900f00d100c07070040d0002e80010b5550310300c03078144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 562572571 1250 562571321 562571333
    0x31d0a0b090c0904050c01081306140a0629090406030510050709060c0309050103020f1204050109020f04060605090405090106030206161b15080c0f070f200904060902010c0204060909 80
    0x100300303003e1980602044003265000c603001111a03002c0c20070450b1a0f07201440c0d0044200d00002c000d105034070b448180c40d065030300e05840c148a01220342040060fa0b4072081031480410608900342030941d03030042d990a0325080c200107000450382c050000f0071610b4480e500d5a05081c855209805002c2c0d5480c20452016400301c4d100004140350f0400b11403038059030310300402c240d100d0f000e91410715070000f84281810034244201d908104110000200a0905241c9140a08104501640700c0e08840c05c0e4040c462406224078402c8035115225140b9000341e40c07090001504008011003815583d900300040580ca4400c000e00c01e00070089441c02c01c2200038903181038403100440d600043c0c6070107030405109400200308002031540c010300b451401c07691a002003960300d00c91803c4c803c00302400440d034032041102540c0a001006c0c451020703a0010a481c0544140c801c3c0400c400c03951080c5c2660114021500710752281c840e183c010701d01124410015008a8251003055100a030920f580301444002d00c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 562573821 1250 562572571 562572583
    0x40303170c18150d241707121a070503040507170c1909050c030a0c02010203040b131103030a1d040c09030f0501091a0114010c03120b01020703170405190510031d0a0b09 74
    0xc205c50040f4821542d86c1d00c2d681d034900c0f0394040c0002c0d01010502c4601880356072100c0c10320140d41e41c0000c4026240c5043d006100b6002501c04941c07038490807001041c2140915140c901c9080864002c025050002c020802c428100562000b01c0803408040419051401d0080510550005d2122130340e230b040140102049a035045030403170071a40305105010004400c0c00669400c90b4008406c5040021070b82000e141da42114101c0342d6162000050054050740c05c0f413401c00c00807546000111401e21908140802c2d50b442b03118846c0082c40d02c490134000103514600c00b64a0034060313030000a0800e61036854418901040003c03890f0740004400400c88440c1c8030701c00c110a40e00038a4410f070f20200d41d0350082c2c2001d4009511180803a01c540010119900c00c001034001550041c5402c100038002c15980c0c1901d620a0007800e00400113101095804056000340a040b0b0b9000303030284012101004085000b4071280780b00500b112003a07802504400340c1008000d020501030080203d4504100c034545207021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 562575071 1250 562573821 562573829
    0x60501170105100c1401050702010e0c01090311040908041208040e0115090b0913111306050a02070b090604030501090302100b0f09131403040303170c18150d24 70
    0x80d034040300520a80c2c85444040800e5112803c0c0700c07000500c1450004030348120f25030551203640c0f908041152060f41504041482140030302907445440c04e1100440d80c20380c00c4e0101801c0c8864010b00c444080c00c0940c8504e400c1c5000f860340a0810303032178043c598000c08400b9001e9a220b40302003407d005c0e4aa50541d40c40c018400f03108919802c0000c3c030f00140840810380b284220f908400b240c0100c054540ea20507400004103503104220110444a000c081d03500840d2035041c856070708070302c00300c0c0e13a9001e10101c0c0c896607003903002482d03224500030108000740e00c0601080d8103d0024040040052000d0091020f500d1113078002d0481c0e50055084441260420302b100d5214050003908811b494441464580c0c2003007202c1200142000315041003140c5140b4020458400d10000070004107040e4020702681c8113022030002510507482e92200c812031070113505500300d803001c01342140b03a100340b404401c902120035000b0741e4103003054007001486040b6615441c902803218a1031050b4005030102c1c10b1140050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 562576321 1250 562575071 562575107
    0xb160801061e030e0c0312070c08032104020d0b0109020304050c06040f05011206120c0e0601080709050d02030a060c030204080c0a0602032b05070f030c02010e0c131e060501 76
    0x200c1c100410700510b0080d403841c0c285a9201c60008410500b4025038022200240c122101c0181660f5140002c0e0b02030f0340c0c1614034490a840120300c070305021040386c0701080a5500510303040e002210049810300040c208a031b00904400e00e0340005014005543d00034090743c81d0040c0c0342c0c0703468105030781800545115030340b050500700001d21082c00f032105c07102e083e00e0080c602080b610310381d948510010110764000301221410003d0b04020030180b600c0820503212003280301c4019859660040d01d51007000e640c0b50700850700840060046041a104140c3d0b058001021900c80040a440b1401203c0342b01070f6040001e80c00283c2840101c804103c0d542c0c21850a40b2400d90003403401000949038015101e0458030780440310060030401003130a200d0f80c071141c0304640401c11810401c4000e06007100d541c0c2804003281c20144604909401031048200301110f4030050242c141d288010484204074038882c0c0041c0d82d544651000119280401c000110302450a00040b0142084000740c200d0001403800c03115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 562577571 1250 562576321 562576337
    0x40818010305040b070c03051204050d0f030203100312032a090e190507050415030c1704120806130e161703180604080a0f14010b0d080f070b16080106 66
    0x1c2c0164000f2640040c00381b074140d8848500d03207000c440700d1080d0841c103042c0c0035004061100b0300501040462401d0007a0311585a64032581805078282e020031288003200e40f4408204001261000b11380420004240c0b80000c0c002a1540f020b0f4040e00d9103084080c4200c4a180c42c010150f60008108400b40c080390010501d24a00341d00017040c902c0c00e002c1d10b03401d8a81c50350007007a0210300690948003d0541051402400c1a100304001c00034202d800b402c4000417403d610150800380084051401150000c0c4000b44001d42203100742c0e00000090482344d0003611004401d8a50b180c40d116001101d42c081e8080c201301c4c210044c224541d034000307410900d641601c204140c04000400801c484000807030341c071301269018511000850500941c0e0001c0d0351402070940741c100b000311603411403070708034410741580c407100c6e4415056070b0072603094000b029000b0602002e410045899000907080300c040b03001002e40380400541d07076124600416117003c91003074000005103104030f401100c0315000d04800e2502c842 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 562578821 1250 562577571 562577573
    0x61e0504150b030a0e1203010303020a11040c0c1101120e010207020301060b0901021005070903020a0e060333040c09091401050f040b160909020a0f020c12030a08090c0904081801030504 81
    0xc0144406054800a40d60315807004503c0c050a002000d1b4040000340d0140d1250307500d040103519404440021070b1544201c1070040520310302845812141403040e510a0b0030074040340d980c284d50749905502241440401d1301c0d03103441c58050340528010300a40c1c0e0f0001d03844190900c140b500355903060f0000050b5540503c904682070368001703495004d0468800010900d03403921041035602c40100e82019400601d0000040b1b40c80311285581800740005508458034030101042031803100c402c0b00b0980c6855142a100c40800002280900d9001801810b82802642c2d990f103404040b2840c0000450301c0c002010380034101c0d24400e1046641c4811030700c92070002850103555a00700348000400510f1986005020442003502c00c000c1c0c40094161010b08642c0d485842c500075088000e10035044c2c0043c1b240380d0595510741490341d02034880d00c441e00029070034500070304070036244a10020b0049102c0d03c940420325005582c2c8a09050056000d911400d6540d11030042c481c0200070659402414107040c542400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 562580071 1250 562578821 562578839
    0x624030c15030712110c0d0903240f0f05011a040806190209191802120604240f06080c07050a031103210106020d080f19061e050415 58
    0x194030364020044141e0b2556001000d0381c4400c0107a40b00c030421072600fa080100d01c2e2044005214110745030080b12203000740c60004596100c51400300a001902c1c544081e10500754248410020090741c82001c10142d845034244812107804100100c030180c0c960f1300400c548103886030040019450490340d903160605040540e96038080103440d4100652609828250740c0c0c0803a8181c0c3c45501001302004d95400c8007188000100c081c1e8000d2100d100c0388174090841d00070040c800c44088010140e0280025952070042000078900846440907662a104501611840e5098060003929099050105081c24220014503a11008048280320301080240c1c0d4045000002e0130030145500d480c20f41020b040c1108070a00f180902800c240180c2c6403038071000c0b44428a1514076059a0f40d85c0c3c01c0390015034514000f04c541c403c0c10b407030250018a1560108102a03098085c225006021400100d01242e030313140801064a5520a200c1811800130001d01440c50503000b90031455030712045e44607583e0305005c0c1039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 562581321 1250 562580071 562580089
    0x6032405060a030f02191d030a0b181002040f05010f1b020111100203010914070f23120405010e060c0901031a04230106031107140f0624030c 62
    0x1951080748041042c03007100b0b2090304144a0f9561040041d516000d2440d500e01d015500d1101d0300300030801d910880440380c42d540900c11440d480050042100403aa91503a13000c1100203003070310480d502c1010742c42c2e005101c2004000204245548016600c81c50500c03024042031558001d241001407445003000495440009104130230400480c010800c28648016500c0040105006540d8010000c5501d0181400c3d80514103c40f81c000007448a520102d41c1c5c0e06641c5022074414020400304104200712030710070002c411100071508800c0001c40ca0b94a4848051342004103910310404c00b40c0700b00000c0101c28000c280003050b40300c0041c01d4508051401407154003425a009041640c1e46213014001c401504110310007403400307413082101d50611300401040030003141c15480401c0034603000099541c070a21421000c00151081c1c1342c140b420560b81d04000c1504150045203501c182000a45442c0c2c0521466014448040d01c0c1c056000410200340c807405054a100f500c01e80000c0341d0705d4002d0700c1d14050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 562582571 1250 562581321 562581329
    0x150e030712110c1302041e03080a0503190204090e0f0a0b13030207030f050a0b0c0903030d050403030f0e0706030c020118020f0307090504110922111810060324 70
    0x80341048a4000e01860f01d801d60301d03221658001e41840306103940c100103500800a642c80003400c0e40030101d4180e035110086065201c001c00d80c400030402c9000180c8900c029641044140d03005e06032050281a07400280e8000c2d410046c0900d685004101c1e103072204000020644101001603d0000e01c15221140d041c4001400c1000a503145400d500405100784500c501840c0d000004008075665400c1c02591a040700b1022111080660301088a5000c140103881800300024025441c0860a10082c805418023500450038107844411a0506212a014041401c403801e4001d1000701d24180c0b00505071a01c100480c0e0540e450940380c078855401008410a01340e0f0103442010b20410560b000c01d18042c410745c003558505240400380300400010074038070040880200c3e414201d9031114113160001707010700c0d80411000b000c0900c4060006268035442803040c000200321141c4141b854103481d43c90385044401d54141461080c09000254152069050381118210342c1d07010481850071008800001d400703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 562583821 1250 562582571 562582577
    0x90a0510090e03130f080c060f0708090d0b040624030201320a03060915060f0305090f030706020309071d180120071202190807080412150e030712 64
    0x5a1001c02c180400c111005100c0c11000c00c280290b899060301c010407958011301702c460041e007111107918900402039400c480c9090040c03d1810302c4990354003400340d11864480e500700b81002002408216403091940c0710b00e01a02d804102000c02c00c01c810f0082080f409450100110380d4001d20150340e0001c0110700b0142007902c41556030300000803040340c4111103408c14012040000700300030034941c55040743d000c41d0044c2405110014501129060104450160800090320000c2003c2100c0c829004a50018030b5035040c0c6104521146006041da4000101907a4054000091245c503210800a2a000303000700413441401c0c124084903100110000b600002c1c18034030140030070008403420350240c40009a00841029031190110b041d0341180c100311801e4074076400c1d112032074400f180041070134110440251032801d0759003207582d51407106420208c415219481c017400007152a0100100856006020b4075200c074100b61548001c00542d11101c2001c0c1031030700240610300000c2e01040e511344a0710f006007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 562585071 1250 562583821 562583831
    0x21c020c03070b210c0f040314100219181505040e1003020f0d11180a0c0305060a06050d060306050106080f0709050306060f24180102010e120703170a0b090a051009 72
    0x1781403940d8a0041c1c003030303210f52050001400030400100954000300c0310b003050103480c0c0450030403d8041c201c1c09050100780c0154440c0d64501e00c881d100e500c400d0201119490f0002c901d075100c08410070115180f800c12070100e034001900380702c0d14040404135030340402c22030740f81c2806904550115441c0c0d940a000705000340e0701e5000e200100a8811000c01e440303500a85010a0034000c01c0c04c840a041040d100c07006107602d08900050100e03c02d008403803288038094241c40d8080c0c580b04d012110769020360203000041c6d64070302001c070000e0720300d005080c000c001c1c0c1d943c2c070a0b03141040c82c0041404d9101404800a00001c81420041601c0203d03c0d5a4804011655086242443c501190309600d0b80a15441103882c0459038040008104014208144001c01d00c102031100c0203005a003224001d55110b501d95024804040f1103080050007412a00d1091401c1c1e2160700454507491210b440995903507820b252103503001c0206007840349503030790300c681e80c07603400c0c8034074140a0162b0070301c8140c6e4001c103404d641c0c8130 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 562586321 1250 562585071 562585081
    0x7050a17101d06091b12120d230109060b0a0c0602090a0b0a0309260409020a090e07020c030c09040209060405071b0b091203070816021c020c03070b21 66
    0x11002c100044284015507001e03240040d6034076122180074405071008610708900c034103681010342c9201c8001003000010218601e10382c031813544076004040540e80550315a240c218032551a8200c0f00c880111401201516504045e945415190700380c100c1e9100c540140480d0344881e6104c40c106c515145c01000041c2d540e5504130225032442c009811014070701c040081c0e80102668035504c15000c65000d2004203000103410500100300c1c40e00450300030820030301400300b8440150240c0c020f0418040505250490b50703a580e0408612100c21162a400f6030042c2c1c1e0b000d40b1a09050000303c900c40320071241d455952030301e640002c4401c0707070103800300b40250b40d11000103113104e004904248050b040700b0075204603c0e490345005d0b040c20500f1034041026000707841c0034001c52030090095034000ca01c1921846400d40d200c400e034031900708035194040c08610a50074548c00547c10340492030403039011035020341528905441810701d0840a5881806042800c20484880e101c0c04400c03100041500e204900c0f6680311 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 562587571 1250 562586321 562586351
    0x90c1802040b03010b070308060406060203071106070c0e2a1903060b0f070c120f021314010e0a141630020a090b1201060e1f0207050a1710 61
    0x2503500003020b0380c8800400441d107900c00b0710251010358800c0d80c4200c070035516801448141c510a210305000f50344144812030008282c808030b9100e46038054440c900742002510b80400b00c07600340e407000c82a00e00a03420300070204404032103003c680380700490400541c868000050494411101021408400f080301c0305003140c402d801c03600003465050ba283d902c4180e51010b02040e0f42c00740a0443d1140544100061601007130f605103020381d80c001e195044114195020f22200d59451903441c14866036401e41580c001c2c0c01420801d020b400348002d0440c42e46448004a002c440008a004401c01c50313000800641c180312000860b124155458052100c0000b40c0e00003405110443c1d804092080b1140c440a143c0e09a030702504202c0781580d00d00c40d2481d62003c038680c441c452000c4082d81003000000500c4994000c0b1b4102807000409000d59102230074100e0301444296624002c20b0050700020307010800f03860700f000d014015022013800c0300e194a00650030903a032110030b8081180d00340d4551100761305941c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 562588821 1250 562587571 562587577
    0x6101106010e092a030c0f1c240b01090608040209160513031505101202061c0e150117061501020a05070801050f0106030908030601030b131a1201090c1802 68
    0x10200002e1381a01d2201d881c0030024009103200325020344203810141110380f03800030316201040000f806c0d080c5105140301d50a81820341c110019568900340c410922081680c448400345441c1d0046000600400c0940c0018000c003415400f000802031500305200150b40d0352290b09030008200c1180c1e2400c0300c5c0c801000c1d9280d026042c0c042d610340750080c00020030300c03100c0d0040396103002500c00304006d80c0d60b40c2d4448800407a200d004254aa020181c80c010050030400020445408648804106074403a580d40d80700703690200d011400e0343c1d0403030031078004114402d00c0b109014101107039048001c03181c102c0c14180c0d5035100400104e80005d041d800800c0316402801202c03002904403003666021030310f84505601821003030781c0300841074041c0000041c00d076119108000626a118180c6891a1100b000450242045801d025480b0aa100452080704654402e90354070a080c1c2c03d24441110105040000d0ac03080000c840030141d0600310100001002c1c1242402614000003502d04012003504105001780 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 562589928 1107 562588821 562588843
    0xe1503010906080610141f03020705010b040501080a020103020304060615020313050604030305070602030a2a020f010c020325080403151523040b10030506101106010e09 74
    0xb8680072242c1c0502c40402440303900c480701f2003614054003004070304421020a81c001451001c00200313004424507400708480402440d0f00d060a029100c80c44d050000341007540c000300140c100121548008043d048411140c103a4941010000c1c0d9298031040c0d0010342090381d44c40001b550720f0410211403d0344c2d4540e03141410a4469a1100040e42018182075002d83c0c03106175068a0001808000314030310b00000303a0443c001c0e0215006400c0c02e07400d01d07440200d030341130044220780c55030004200c8100d007800c0741340000e841a69040b604500d0048482c000c0510000050000c280500d43c40d040f02c07058440e140400c60085131030000e08011480e0300c940400c400c0d6070302c0c2030383c4081107030030142c0076050700503202080c620321110024412903603400391100401d50303440a224081c1017040301c15101d040c4500f400700c52001c80ba03482540e60441440340303840702d203900c0700090a02c040130b215807403800f = true := by decide +kernel

theorem cover : BRFrame.Cov 562410071 562589928 := by
  have h0 := BRFrame.cov_init 562410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 562410071 ≤ n) (h2 : n < 562589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
