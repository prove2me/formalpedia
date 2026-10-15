-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4645
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:17:16.122997+00:00
-- url     : https://prove2.me/submissions/9cca1ad0-f575-47f6-953a-27591e2869c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 835251798 ≤ n < 835431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 835253048 1250 835251798 835251811
    0x40507080c03040804031e05010c050301150e0a0503070b03071b0b0a09031119210e0d030e0409030c1103070b0d0b030f1603020910030507051e0d050c0f0a0e070305 72
    0x1805c00e41c0340c6e00c6040302044036601e842000d01d085200d078010004207018a10f20104141422800c40d03141003003a40e20b000c0c05084007000c01480d10102c5a4035510001501c01400000e002c0b612104c2c0c0b02c10307803118950700980d07031040850741c64500c00f0038003541d00707520385401980405440e08680750409080f0241c18029021000c0c040c09070030300c10315041c1c100400380f01c254040f0508000a4071a083c06420b1912480d0408001c001d035030100aa410341200350340342d6002c4d0507100c84014006d01e0074221042d64112441642c070a013450311140c113140e8018858688a8024400c1c0d80d003103030020003055528044c510a00300d0044090061003800031003a40b00b880c04000c0075055038076041d1600911414008428401c60354030348800b400f03005500300300240581c0004c2c169030744010542584c48050340d4040354402d9a21074400d8506da040510a4507580582d101e9028000c04035200084ca030541c2c0f40e000b003240c15805405450000d1207030703161400c1c001045601f09001e41300706482d6424110302405008054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 835254298 1250 835253048 835253063
    0xd110114040302060613111605030d1103060a0510021b03070b04080102031b030103050a020904020a1d0f0714031605040b030c13151d01110f060a0b040507080c0304 72
    0x84010351140d41400c6218038400ea0103015180340490030004900f00c8001e80411071440d0040031000b6002c00c00480c1d5020031280003006001002c2c0c03807c0c910714803178a95024242d6080c80c0111146200840c055400303208200d4240090035241c0c0705210292f00300710420401070380407030540d581e010341048400c40d22100203002da41c405500e0708029410780c0c0c080d910118142e907001041040100440341c84410100180c1c100c1442c5514503211240d03140035420019200d070720000080780c115131300c0601c0e001c000c041e1103401038590b51820b1660804c4403002c5402c050383d0381440c00011600b40c801d143c00d11681c0d2080e00d0321411500c403030791481203110800c42c6020a100042001090054000c00518482c0a00d0241c00740d80e04004054098001001e921040b40b40b540d04c800000703481c4e042042c4001c00c086850b2107480c2c4c0342000c40122111070342c2c070040240600800d008040c031500086120f900c030382c04451081c0b0003070b01c030369080c8001c403682291918009846280880c0b000340d0540b00454020707004002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 835255548 1250 835254298 835254311
    0x6060906170705030c090f0903130b0a0207061b0f06061703070501150612020d290301050c19050a0c020402030109090b1f0909030903050d020105011a04080d1101 71
    0x24464100c846a40210818910074800c1203184581049680c02402d02540500714090002e00811401000030b0f05070f000b08a81500012440c0c1d00401c1075401030800c19542c040d880d980c45540c504154084002403005000348031010409a003c0c40002e10084160703a10409008060744400c60b040c80158412140c842d1a41e400003152110710034051003040e5041c018507581c0d4002c0c40d08034211140300300105440008003004101490b00048144031851900700e000d60340d80c22003803c1c14001c05854008041031466111545680255101418140001500204490b450f41c00700500b003400b440820004d400f80514103044098800c03800f42003030000741d06003080048400e500060603a0426080032440907500c444180c280f00468049a40040c0e45140340798401318044405004802c0b01e0048400d075a4481e80c1c550f041600c10f05410780103581100c180d81011040300f50090281c1000c3c4a5500011403a0031655030300642c25080b14100c51400001f03042e90300c0c0012040d40c0da800185a5143e69560303605 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 835256798 1250 835255548 835255559
    0xe0f01151404080a0605060915030d26240109120201180b0403050105160507020901051c0b011d100e07030903050f0c01090605071704020d0f120503150609030303040f0606 75
    0x14564000e200345d07408035003031030104107001041038010044130040080d80e1804034103440101d240443c1c00058940b00300d09a000d410503103890390840901c03040c0d5940c0b4804018110000c1c1d078000c0c03503c92032103480c21220b10442c001159941540d00440c00403003041ba502000540c0a1016520b200041032440c02d500342d969141050250003581c81a1445c1c0d4462003042044e441c4002d5035900085142001420040d043e00401c3c0c600c00c050141da03010b6944401661600091111023030001548001011b08a6842c0e2030503020229124400c26418800c29020454110506410506a4075990007844055894000c120080d09100c078080d8203002040211030020351050303004104030a4081e00101e1510320b0b03480c054046130f0004000000700005013040010740700101d2010341d00a901158014002c0125091103a9a51400380009040800c81c004242d000358200016504c40c017142e541400c0103103900f07001d000d1940b04001b08550705400c204002400070701904210303d280380c0580030004000b500e60 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 835258048 1250 835256798 835256803
    0xb1c050715110303070210060e010b0319110711360601120609050601080117102307020a05060105030303070f030e0f101d01020f030c03070e0405100e0f0115140408 72
    0x19121100103812108119681d2040c13401b4850062992013088501503150040d890bc1714040a010f0380c494410300081d004036044541c002c4408800303921a400c0e5903503070b076103080c0e100e0b903556619a5000d80d80900b080d860520342a100b200f116403d41d1800902c2e15403401554658090060016051051103244011140b4191140c24040d121a540026850518800141c01c1507016803100004050300c1d0903a2170782a03400b141d040c0700203c0c85200818460044401c2821843e0b2028030f045202c0e0001c01002090b650004441205601410690341a43d2302d030320078191207100031183e13130380400e400503054078102e17229900c00e0f6841c2410030141e441e80310101c150740313044c100b40c400d245440680310080800c198410340464908003065100071403400701304030b0198215000041100c04c8000f80400000c001501480000c8000d6500034005c10041c40c1c8241040601c0d603140c0152404800c2440008035001150104141652250f11840303103903444030308040700d19800310591100c44c03200a210010b17091508 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 835259298 1250 835258048 835258051
    0x1d0c011116060f080906040302030a05090f09090109020907020c03030702150d0c030b120a0f020d031803060225170d02041a03090d02070e190b130b1c050715110303 72
    0x80c0c0d500d075076120b080f00e10700910104000e0184500d58100341c082c000003035000421511100801e0410036100c000d260700140c08400442591900300d0341d80c004001c0328100660108511520889640b589500c1c3e05c6401c03642c4411028440381c041c3e0007002404058500040042c210030070307004840e03103800042085a401d0340d003d243c0a0012a40300c80440d15540f41c100580d00c3c00203400f000410390103810f51a1010406031001d0080c2c000c800408580c02030500c2500d00c50000f0000d0708040212684c0d0703142c500000c0d444540c82c546a4032903225090180c0c41091031040b05a5001000080303003a028440415507a071000340600720740c80d0708202c0080ca00c0b4410450152003400b0b540001e40380e1900b07044850900507141c1c846c40454211f180148440c800c2d600c0380302c0c0c100c40d000c510003004002c6401400c00518042016545c003031301d120301c0c0410b140100c1c1c02115070204156840c1d00c60703140c90200100025440741006000790040b100500c10f0020138848904840440c0c50903d8004012814545c1140c0c070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 835260548 1250 835259298 835259309
    0xa0302130f1a01171320090105150d0b041506032703050406030c03020d0f05070315051804081603050403030212040e13060905030a11011d0c011116 65
    0x115403103001000c48040c841d0b104585009030416107468001000241881040344411112400d03041c04201070b000000408145198420402482d03445260401c0a051183c40b106601c6850301200105150412448001e19900010851418100e035040c4401c041e045038001c0c20f40107070380c9210300817000c2c41445529006100ca40c50024003400440c07401c18100800104181c1100401a0350400203540802102c04070350451500080203035088008801074407400b00d41205c101e0501510200c1f401d0706500031030252290f5101085404141c2004103e02d00340c500c00c0030b43c00f443c1900c0300b1120760000400c4070742c000e20498006150401000341510380d80c0005e5001e80004001103001d1042540403c400640713000000112030806250100d09099010000c01c603440180a8400d039000300083e0784c1003c108541d000c0207994030781042030402460b403407101c5020140f96003880c0200c40400d00711030180184105a80140030090b01c05001500e000c4540784040c0114410b100340ca854a11084030f00001500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 835261798 1250 835260548 835260551
    0x1320a2c010b03010b011704080d050709080f0a03021c0504030503030c030117010203150f060d1a0a050f06070305091206010909061415040e010b041503060509070e0c090a030213 78
    0x14255000500b10390700d40060034040d0f0f01d480c41c000c4481e0f030018003a400c02c602c0301c0741d0001070342ea81e80f071b1100301400745400c0e0319942c1e030825080c49050380e0400904026030310340b4801c5903a28950600084d0355000004c2024002d038001006a240c0c02c2c0f80c0503218030039400e0906206243c13540d290780d950325640c012200c0200e0f441c00407005002000600c00b00825440e103c500079801d600b05846c01c0c0c03034507000c003082141c480d200c080010283c03a01c80e4808c0c2c801604800380b0401c00440585403030340c0141126a44d691146000034004280c0b4904640081401e80000c0e2185007410442e9400352540d0703002030f4038164040011440c180b4107800070000f86020b0000031b20007140b8180d80345000c005440d450b080902e00061000104101e00e402440c903503003d110110f4020940c02d8442d41e044d401820303102c0c0c180c1c0d04941084d0491801560105001003100d100d9141000540d68400a007071704c0d00c8a40c0610a108002c6402107250600d240020380212080240300290303950740da60005004100b480790245506 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 835263048 1250 835261798 835261871
    0x40506070b0915012301110a0c0510030c02060f0603070e0c04032906101b0c080706030605031c0e04090303050f0c091c05070f061101320a 61
    0x802c4180300103a05419040200b10403941818030141300c03624640322510b4120001500000a40c7c441e0340c0038440603d000342503038116000c90030000312186082c041c0700c0c09801500221036070315102e48501c11050045602800064a50586c6903860920191500340e1520401c0380c08908072004600c1c85005d0f8064080150340c8a28502d020a0f406c405040305c04c1040070350094480d03200480380d040d00d9100c1000ca400405240c41844103407003542c0c40c0000101e400c84520369203410800c03144160070584256108490105580c0d00049041d0384a074000c440e019044008070210690310501c0c000c003643c2590914403101c161400109084400304c140950000e0380720350600c42040c0d144c404c03549c1c001d0306049009242c40072a20100704500002c01c8400d290742c1072022007606000c42406600040d20400c0d9002030915a5014000c244102d540907044995181c0b29401e5a0306d0058181a5818600c2655104805c1100c03881d08030702c0200102840c122503200c61002d000e04402d40e03074a2015070320084280d44c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 835264298 1250 835263048 835263061
    0xf0a06141e04080601090b0618150a020a03030506100f0c052814060405120705030903030409020a0206180c0103091b1e1424072001030b18150105040506070b 69
    0x500c030046c0c1c041049a403074500c000e0350544400f0122a40c3d01c90407090300082036402e9000c54851781c442d406d19000d9000100716040900d40c0400c5441540d80281d505103c2619040204102c0c1d0a01032040000310f20340300c511000c01c42c004c50400d02118007400554240c0307442c84122401c10308070160416076115860090f14200003010b2070b690001c000c6a001031546151a564056445206101d120401e0038040350b10340030008108101d80007040b0180135030352519500ca0f1590301035008014844058041e030f100140b4002c041d0805039120030200c2006240010380040150001c0c02d80402c240ca1001d14800207502da860041400c400600c074031185020480c1200c17003d103401c100580c0043e04001c0c0319800c03c05040d56400d900300074aa9002c4013140d0140b80c3d4100511030b40c495040b0003008441c0d401c0038401c2007000407007076950920003030300d050000f803c00a041003800b001c0541208900b0711100f002c038107960390412184005107010b04000d0b03d030648502c00a5203d400500c8219090154503041142 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 835265548 1250 835264298 835264303
    0x30806360906070f0503060a080a050d1106040b0a0c030e0607020705030f0f06011a0c0d0503010317030402010804030e01110a0c090e0a0510020f090405010801050405010b0f0a06141e0408 82
    0x80c00480754010741114206648000d003901d010b02c800004100300400411850356650140c44024072002c8111760310742c1d03451714140e911400000c1036403010400341002288140c1021074054422a40000002855a80c0d07800020041803d0750340c01c010142d0343c084c1182040c0082105078020641d0350001d0102c01d2400d803c040c640f000040d0034580300c1d080014252b030300d042c000031f249042d2540328642e0310f0610044a88114030380102c42c0440560300c5041c2400045640040085045c5c0b400f644282d01829068824843d0a110649000b400180c0040006003c688600032850506405142090040400160107441d102015000307444601c451082003050414510038080300d004c0c0040900078401e090b44070783d42c40e01884199001c80507000100700b65500c00380422140040401002040700d5616500c0b41802032400300c0f001c40b041d40c42c2480c005110301c1e01d110060b150110041400e102c0d035003405011200748008021010020701d040c0502900f515215043c4130840000340411a110340c03410800a2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 835266798 1250 835265548 835265551
    0x20109020f0f0d0803040f0c06091703030c030126100e0f010608060105060c070b0d020403030210090c0b0906071205070c140a0b03061207030309050406060e0d03080636 74
    0x1072080c0b02c55503040945868540e4a00c58107500203001310f1700d0b6a07942c01e011003907806800c8020200d40c4030300e00106205801680e208166100c60304030003102103c40c11119130320703c4252840724503450184010410b01c0041c17036000b454130610021040d5440f800300c019a18140d04800b64410564542d045440481c00400110401c03c0c8084000c1c8407092402102d151500c0381806518068000059010108041004158001e0458544007551810f6840c030200003904240000c800500400760310390b0043c034007070080843c0b032038103e180101020711f0001507000720b034484d41351319400c55824000c1c1c8000c59501082421114100c0d102e9541e62005450009018003107070700700300680c402848411001d52150320b50710f010790b0201001d15580f5100c100004010b0080700780032034134034850701c2008010164840c8001d01250030a81c1c0502c911900c034002620700343c980700b84440c0c000700b10300400c50200388102c6003e80c11200c09031030b428440d68089a81d04074070388845414000d00340001c5601e1758054045c01c3d0507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 835268048 1250 835266798 835266829
    0xf07020a0f17011104031707140a0b09033c160c0f08061501110316050f0f0a02091b0d090203120a05090909030c1518031e0a03090b0702010902 63
    0x20403420002008906071350240c2d01001d0034009032943c5100d42c44c1c42c6c240c00c458a803071b04614100710ba1070001c05d425503106101002120030100d44004140683d1000041d01c0c0c8140c80203410210110140049042e4144940c40500709183c8000e100d020b00e0b15004003c006400b425034060b80d5081007030503c3c18031000d00d540802500030340800d0821880c4404036030583c00c208140c504000501502004a031001b031440203441d081d000010f2414606030000101143d00392286098480b60481090b4a07078aa91241010709425004040a0001441e007010b41c13550010040c980c1c141e5800e031852180740240c1148040764811544c0d21080020341c03408000c2403000345141d1a007140340060700c860090850150004a40c040c5c01c3c907501060040c602801035410b001c800908640003070130f0340a608003201c2030075101c00394252941e1919412442000c8219080c4412481400420010409002005178040c01413802055683c081041c002246103c480b40141382e42c1e4008582008540100040c0c0602a4000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 835269298 1250 835268048 835268051
    0x721110616030507170309010c080117071e090207080a090e04150902012304170d05121003050703140c010e2211040305061006050705060c0f07020a0f1701 68
    0x40c40810740452003903181aa41880c145889040070b2500307070500321441045842484000c0704014075803005601c1002e1304040c640e02c020050340e840e45121244840d2240c0c0c9181ca400004007400744000d020070240c050b49140b8038500549036642941c00403a00403120071a000710000034242425030744013000c9000b800500603050744604140c0e90380005100542d0084000648601e00708080d603000d00840301c40803840e02c04000017240240c50444841d401743c01020420801290001001507002038812040b8050f03446143c50110a00c00c06c0c171061400514642c030007100c0941c0480020707001c1c0500c000031449824210307103c90740248024142958401018108005003d1035100c1d6550078604882401e100400c89a030140240c0441004c0c000e580070309602e20800107000401c001000920610035800411296030b0541c03243d03401c40303051107161806445a4008000b10301404004c8008000c03402044032083c1c6000c600b81c4c003080968449a0000b031680381c02c10b4042109521841942580d00c281400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 835270548 1250 835269298 835269307
    0x19050405010816030f06092003360d020d080c1603050a090909080408060c0f070b280b130c02060f22210305160c030207211106 56
    0xb8960440140f80c402c100140c0088604018001c0d030000340c41c07181402e0b06010061f01d0307242c032102401d10344211501910768035045010b60000f8105480c003406641410100b00200b00b01c0302262000e895035081c1c0c0903121080c0c15030b8012010020854030f0a45074001d0503103a541c01c8805400d004004204065100c1c04001e4019204203000f0100021070349030a0154843c07581c00011920644e035900540314651030480004140301c285d0010300125030750700040b82d40558400908110900540c80c6100c0c0a01d003e010746400114018040c90744404002c0c107a6400c0c2d003000c0080041800c6a91810302500d0f40d8100250160900070b4044806460a86040c00f542807040c03c003c1d525040140b200c1462950400401c50466050400c5001001c03441222410714015080508a2444481055104020408840070154043d001c0c0d284100c42c116090403501000f48c0741a690144000022401c50007640c05c00b084100d5144119401c4459040d40b11020100c3c03450302c4a001c08903030444900c00ca03000e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 835271798 1250 835270548 835270559
    0xc020105071b080f03120912030a11091807030b01080112150f1d06010e10030b0603161d090109080405060c03040302030a061e0903050d0207050708060c190504 70
    0x40403151000e500155501c010302e048000810302c410190082e01a6024011000c00c00407400405001146414a0360000c59100d540c43d081d610010020070b225403401c01d0002540181065100800701d84041500900d000d0201c80050344070400b0003004007911038001c080c00b242d1941071040c0c200948007030030480070650512400c1e4107801c8000b500103050a600c500d4100c6081000e800209101084400030300202000050607044441d02809e440384506c02c01c00009440f05850003031500a003400300302c80f00d00e00e05684410309910002040c0c15018030032000c0c5120b000b0015180b0900410b600300041140382d403850340503e4180005003000e803044c0c1c10a40100081a08070007100e046510440d0425a01e1041030b820500b10702a9500295150040c021600c09100113034000741c02541c0c40440700369150441d4041c42040326030402d400740c0018024019586550100da0040c0000750040e4121880165035a10140c0b500f1021a01d00d9407018011602c0e03c0100042e030004585031003503062040c00c107410403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 835273048 1250 835271798 835271807
    0x3010312030e1c03060e0702030c0607030504030507120e0909011512110d02030f0106180b0103020720150d021b030316120905031305030d170a36020a060c0201 70
    0x45005810300303c61101e194001d900036401207008100d503a031814100d00e08130320040e442e030308400aa0402c2d4003c0400140c1031364442d01ca100d01ca00d034151201818203d0700c5d01e400450b080002000004d202c00c1c480800a56030392066230600c500d1002c8004a8841c070b042104608800b00c5d94840c0c01c8140585049900181030900f01c440c0440c0191040146141c490000038648003440c20350714865440c09401140500302c0140705209050114000d000e00e0040d44011001c03407042a001801846041611801c80380c6443c202404542c0300424549844d0304c0c1c84503584055212211051100b64001407011008030751b10100c011000c0c58070041d60175890600f0307030788860000403182c900070440490203030380144405500c400304180c4c01c401100c0c2c561703801800418642919004041c03007446082483c2002d544a204031007180b002e02012080c4503150245400040d02120714025104508000d07810442c1c205011624040003000b0100b00041c0840d0061009000303072071700150104200643d1000150340c20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 835274298 1250 835273048 835273063
    0x2104060b0a06021629031815010e04030f1206060e0a270c020319030b0909010c0e041d190303050c030402060412021f0504050108010819151103010b03010312030e 71
    0x11741421604000c51401c9291514180070440d4083c1e140100900651489461b80303103c009034031904596602a00107807810080b0303002d00c0360041c0d54400800040000307120744442100080305040101c12580c0e4910744034103651040c0c00040000c0c035400c02e0301e2407a2810141000c024442440050410130751b4001202c0c5c1043c0143c44103042e02e895040844046d84200308a84010808603d0908040848480240540740404243d4483e094550104215a0044c400d00b14aa4602d0b11303250f45a0004405020203803072204012801c60301709102550703070030006220039003c1d00c82225200e00c55600a18018044603005031040c0805c00e0148104070040e126201118140e90750b01c0070ba5010440a407000403103407601ca5500c040f0b404480c510400d00c290700207000d80162042600c42034103603a00c4001c415130310340c10101c074111398040b91008140030901032074181c801c4080044001c1211410790000c4607035a8403e80c42160303140000401002406200010504032074006e140074040d484214280c01da0b54030a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 835275548 1250 835274298 835274309
    0x203030a0f0504030c09020d050a050910090c03021f0212040308070b060f0d060524030d140706051303030c02061306020c0304050315070e0d050d052104060b0a060216 73
    0x400c1001e8440c0140305540046034803844141141e0b85440f088006500f0165441c60628100340200f6044c802e24000c452042003c907009090b448240400940505888030059400458490011000d030700c82a2003500c2101f0381045082018005c600001d00e4100b40d99540108040e0a200c284002040b00c41101e20943d0400001c41d410303112540058000c0f19040c44050748149a82c0b940b008120301900305038403425090311034070700c5509841c100d44c3c0300b4035003100240d5140e0800d03034001d046140202d020340c13800048140b40b00d041c01281e80d04c4000700d9605076180e4011a400e41149000c050341402418490500d6101418450402112207603058440e101c00500e00d80c0c010400c0300c64808100309070350041800508850080e541d4003a010340c01a000d03522a4002400c0d1407405000b4104298006c07445030740b00d0000c1090300c52080b000c441507045a01d440030b018607440d010101195849034400d00880c02030000145030083d140403c51240b0301e0b60300c01002d64024004031695442010902c804499 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 835276798 1250 835275548 835275557
    0x4020a0b040e0a110c0a0f0b1005030705120115081c14090108040326060918030304030810120305190306121106190503101410231c0510030203030a 65
    0x103e60030250071050240c022902028850701d80010141305425a110681f00d005074400c2c440d82d1640740720300b50043c5d524000c968055020a0081000b41030400403007a1000203c40002603900b1620810008440558002c04055200b11220428001000b1801d4200c20721030418200c20712103c80b0103041c4e806100d41d258103101020001400b4140541d4140c9086208030341400c0408440302610141258103540690141c0c4403400050540030101c9071400c02d4607001d1000f10308680d5155003c656106000705070a00282000200280c0c0801110720100301510075150251a000743d00b1840900c0c0c10b02d50300b0f0808141c200030040060ba80c4000358144010340216400b219420004041509403180b0f0042000400092614202559000020750301485010082e40a036a035500944130351b01d030122002d640d202c00c0c11100041018094081141180c0301c11440405002e0350000b10706040d005401d94808069922848541c1030f081841031950049504180c100d249080da00800e94a01800354401e0500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 835278048 1250 835276798 835276811
    0x6050306280e01060513050402040f0302130f0f1406010207030c0620030406080612010c0f0509030a050106140102071707030f031803051b0612060609180f04020a0b040e0a 75
    0x10800000760102500c40042c0340035842d651030400030f203143d00034008410245044840802ca030314160081b101101c0441c075052840500316020000051140c0d040e00e902d550740ca4103410354000050065654003243c90300d0008041a44103c400d6412070020611411904910001d000054a04030f148013030b580035151002441c6401440604a0110080050100d00c800b0800069503544081301034440c560580f814080c00084004140c00e0320010700c00140421070200840252a02c60000727411042001000c03100c600820341c503100d00311502c1d40c000046a0300b240180032241d58041013240c00803ea45403005451882d421a02d9031030320468000208041100d4072040145481030f821825200c070301090401d8641c0d5a442c0003642c90202d420981041e0311340500e02d81d150b1810105403407041c00c1c0407480c0c0955540c1c50040140740d034800040186d2005201c400614542810307001644604030b010a01200d07170a203401004231108640d4802405101c0070881844400ca018843d1034000c20b44101c0072a18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 835279298 1250 835278048 835278109
    0x3100c050904021204110a06050f0d0f1404020f10020c1c02030601180f02030f06010e0a08010f020c0c0d1509020d0f1209150f050c07030f050a0c06050306 68
    0xc5120380122182d116001040d004804c411181c01c2c903015a200720450300c45054a1001d00a04140c180302e0701d000309105200b03004441c6008801044d101c02c8088002031607800808044d4101e50f01c8c10150b8503c121030004010440c00c00321181d0300088422501c404032119030f600025601c400c1c4401260180320007008841d00043d2604201100643c01404e8035060b41c0c40704140003c50248207100694181010070000910482c3d1003142c0c014107400c40511701c0c070394410005440070b200c401140742d0044049180002d003080c1c2072080050340c0240000142e555880e801601e468012440c55080c810343c0d04282820009110000244407140d40b1407010802d0001400061108424030001070f150a04600a94080200c40c141440c10808180c48110809840b90070800d0001c640703081d100c000c0390003032031500c032800c0c081c00143c001d10900004444005489556034806c805190b03008413255401141c0080030808081040c0015009516103035041d882c0c608001000851264201c01c206210070216441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 835280548 1250 835279298 835279307
    0x509120915040e25170612070902041418060d1b05030a060207150e060105131d03090909030307050403021c12051905040308041521020d0b010e03100c 66
    0x1c0c83c802c00a0282850208125039183c0036003d20700044d0f0215618488035540103002904644916160303410550760f03880280003030f8000b014005085403061500009400301140000c201408900c0d030311002c202d900005028005900b16840b4641c1c0d50b07807a00300260b0b03803980400c0601071500b01d8110390b80c00e070710741d006541361810030381029415001c0c82032154144200c075002000070300d115150b080040702c99403048400700d070031890307082c2001e402440c010400c070301d400c000a00d05080303003a030b0000305501c0000805440d6030105110041940022410100f10316081c0030550f0300c0001407028601d1403900c050010072070321403400005d00c1001800d002d19442c010b44c166180e40280e01c580ba804040c800da49001e07201d13411010307150070b0f0039034980c0c488004e8520230019941202e511144071800c1508042d82aa16490110307210710030130030400300602d501c5c401d50541811050a02030b0040c0d41d940454029801d480800381c50605012090500b458280c8001504014103a1010b10000d09080507100444 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 835281798 1250 835280548 835280557
    0x120a0c05030d0c081302031506011701182708130b0307030e0c06070b0a09170d020a02010605040207031209020f060c010501150f0c0609050c0a031202010509120915 72
    0x522510011801060110740c42d48952490306142d01c031610295502841011645d1503240d0003501504407811051040703041180c1c0c01d4015005040c1404d84156607550902c803180264040c6c0b0440703022030f0504114640b40d10991501c4d20301b00d04130003003c4021b648001902120b881c40201042000580c02c50501024140341018111049560b5075a090802e0010040c2074001000c07443d0b07001d0040721022f1868101d044800c130a6002c508113210303540708940c0700000d2001050030b68001591000e140c4030146020000c15a2400009005886181500d0000e0841c0c550780c0100380500c1c0b040003d000401e801131200001c2042c014030124030f29a181c8081902c003411400d03001d0708020080f0b2900e220403810342046c0d060743c10b842e00012442c070b800789003207132450b0691145030041410004404040755030350b048910194000c41c00c8800c0218014041034500300076900c20b9070454045a042c0003480c1e428003030190408810402089929054480f510713440c132070030103c1841403103072080700010755213040c050b039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 835283048 1250 835281798 835281803
    0xa0306060b0306032b08182409010b0112020a03060816031a040c03120201200403062018030c1206010810060e0f04020301021201060915050309120a0c 66
    0x520003140d0703601000e42140c0095524a20074000d802007124034542048181203141600d2800c8080102d03541c03000e4a107070001512030001c0840c0c6404100610300304120201071100d01d0340b4403144403540ca90103080d8881c00501a914564144000104503130f03440780d401c14a01c0030842005030740700210001a001010325911541d501d000d020178a100c42c42382d040030b01c002c0704e0107080f05039000300c910080c2e4846210b00b180c005041000303100d000c7c8082071404070501110445800001b803441a181c004108507c0207410741c0c0d8210800040c24005c210060141b04800b5901c10307244030442c1800480c030741290180c00c000350707501c00d00c4403a5801c455030200500300040704050080700c4401024071200da2200e0f4240100c1e001c1d8891200360810301510ba10a0008481c3c498000003840d4880040c40741141381c02030002e90381036400f800400c09845035100c51600030812030f00e40b401c000d840e18812203968400c00054000b0321006004000404002060003641c104004084a03622020300100303031600295410003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 835284298 1250 835283048 835283051
    0x6040804051203091504051503060a0621020301121529031603290705040b030a1d011a010e1c05251e050607020d0611070b061203030f0f060a0306 64
    0x40030803c0d1703240170081c000d403503060310b20320107425081200110600c415500c894101c10500c3c8100416441101124070318280324410400d0b0500005602e01660001e03000102c4e04602451006e04022075604400498140640c0c10311882e00d83c200714048030706100c005080b80b15010565182107076414085207612048141100d1800e540720f0424010ba4101c048040ba41c05048145402448000a64440c401c441a555052410b0b0030f102c4002d0030790300050201e82c40ba88d2103006903000c41c12341d5180064440039000000480e0105000014070075804a903583c5d0510044540400094a030140ca0380b0203c042d5640351101da24662411a180601c00c56100c6412050310443d1814081940310000c00c441e02854040c56080024603405071038000352041e154054820850070300142021420090082c2c000c06000450140c16000d402c00f0343d114150445040b01e07448104800c1e071074804a803603500e000040c0154154541180041d10b091806424407652460b280d0000304c0380e83d00c030703003428000e0740c0c0c4003d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 835285548 1250 835284298 835284319
    0xa0902040612030e091e1b1303030e0310150b0702030c03030a111c0c112e082214030708040324091e0206210f090604080405120309 58
    0x800400411440c03041c40c0c410703500c05d4003041d2600c00a88030724000d503002c00800d54254031a00b9480b0f4404883c42d2841960b51014024452040c038030315003000003140a07171201507000740d802007054105441d0f561022406480d00391402d0380c452444801000f981c00021000b40c3e0340c0c0704c900010380f800e82d5080d0b480c1d5140c0710000c0e421000a40c00712a01185e61101c0003101c0c94880c07111000340400000329135003400214012099404904d1284110104c80c00c00780115140d00c2d01c1c001d20b541114820101001025500901c00e82c90b0b0740e00c40039041c1c4c45020800550502080c000002c02e00c10542d10015140c0100c4041e210180e01e03051044480c8280e007d0060351351030350f4038900810b06410814801640c1c2c8402110950522034034003a588140368010044103900c40190b4003d41124290801641c1128090181f1a803201c60050b01d281410601140c4d0030a034070b08403d40f00305135032000b055940036030444420300000455180598007034580442d0940c00c00711803450001c0c0355029030740c039081d8810344088 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 835286798 1250 835285548 835285553
    0x6050603010909140102090102030f0a0c0b0a1a030f0712030210020c07031505060108070818100f05071e0c150203070906020c030d020613032c010e0901030b0a0902040612 75
    0x43c00b1400343c51180e10690703114014401160300705d010790905140907800401111400108501c000c0400003080d041031000203421303450700750811004607034420f241b0b5944c120100d508a0340e42080700c51248220020164072002c00c0c0c01c40d4032660300b4400c0800d40c181e06c4c85c0300000c15000b841200303e00444003108540700c1c10b003001401da8401051006560f207031011016000000460302405100d41c206071101141c03922030003422a54000c00801a52070901819407118513054180030713060502e02c00b02400b00380c00703074841e066600311000504520280030350103180e070380e9120340c0915800f100b01840c100680307003540c5800c02955100380c8010442c4010300c00000c01c03401c0368001401c002501c0340c0303a0032100c102c43d05c54107050780c0340f8051085c4c00140e80180d0008801c00703101c14607900070501c03a10303140d110683d2181070132318941c50030040b42c03030900415640350040d0b50340420b44d0410200212140011540340d925031090010b00500351306410794441c0c1910040d502c45410080080c80814002d1500d10540d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 835288048 1250 835286798 835286801
    0x7020405043e0a0308070b04080903010f0f050601050319110910050d0f1e050a02210103050c030a122607182301120f0911040c090b0f0904060506030109 67
    0x1001d80006400b182800501c550402400c8181501e0f88094464600503c0e51113490304c0c900000c2c02120207070b00070000101161020702070201145401c2001295400500401c1d50a4410082c065410000309001b0000c0e18124070b03800c0f0b8524180c281d4000354000b1580b6202d191881402c00d40c94001000035030341c055469200d40140110144d42000b003041640ca842c8220507640382682c4a844503c0c6000d080d20f2200c0598403a68108003030090052400c00050915103402020308800d9007052090001002848801c0c004820044011009001c082100e950743d40b90216a89503c80c04120110603c245105c06401c01c039800103582403d098207a00d083e01e801441c89110b000017000511300341d1000205000c1e08011807680da16120803170501b006200c0011038001a800c0c50b081d10445d104c81c55049041d0a912410352814081c0303507040d00d00a122010f10042e110008010000c001c2c4402003080041c006005a6a500c4c06044125544072400c1d00000c01416107508142c0c0d00900010001074034500380d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 835289298 1250 835288048 835288133
    0x31c0c0512040e132a050a330f030506012c0103110c0a1e1704090c020d021b03071802070507080a0b010509130503031311150702040504 60
    0x22030a140200d65449060402c1c4102d1140b00810800c07229005944000d81c540001e85d0340c0f070f03601030700410250352500010100b100c20351002e02d0b0030880b030343c02400152115007041e82c54014894268010344c280b04005101e0040c020040081555450114200b60712036030b0301800401500b000010301032000c100000d0070040d070803001400b20303180c841042481008042516562041100984440315450b21411041000c0e55605401800001444c1000464540e030400001180c0d150441d1203a0600c4d54000c01c0b1001e10110f1801d5501c03492040c1c441c50340c0000c0401200409234102d0290a0760a80800c0c034004c0f40e41c010350038800100d0851906010079a02400465020310115030100b40d035034210769200d045410000d0841d0503804014003407030070305021071900980724041404074100c0070b0315000d085070010b48010030f4998075600600148007143d010340c3d00c00101200c4001c0e41c3e25080000790b900e480740e008001d015075200e20000d0b003404040651a60039821050484102c0c0e04810203e070b0406a1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 835290548 1250 835289298 835289309
    0x5120a3e0715170c18120a0302120405300d0c1104020f030a1806050721020307021509010b0406030c0911040510051c020a050d0e010506031c0c051204 66
    0x10003042c058080c0e116000c042c03a050403265040a081d15480000c481e26400070012280f40744610303c9110558465404000201d400d0b00046c001c0751105140080c24410050201e0103001024403080c031440c2d403075215440b51080e0f45800508104070f03075000c90030001c201c0b6034010954080c0c10801d60800f1340117148580b10324407400c0c05124200329041000100d002d9450b050b0840c1000f800014001007640c1d000880429001c00c4a82c4e250203aa0354003410b860381250000c0c005841c1922007020506241c0c150b6801c0310085500b907046203416400296591000058040d03415080d602003034500d0401e41c042541e5a8001d8418040d164803400c1c0f15040d002e03684a010701d068031b403140c0c9915804400091b40e0a4500003040503402044401c012942900300c201d180740000d044899890710407540744000d00490b01e40b501c400c1d480d04603140c480c0c0100c03080d032030030160180d05140030071910359404a41090940081410343c10f54a0b1444011a00c1403003200c0010124070503e12510b0340e2204000240c0210742 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 835291798 1250 835290548 835290569
    0xc06030c0703082d07020708030703030204050906041b030c0e030105090309031603110d0203030d05091b040e0c1507050a08090f0d02030c1201020903011805120a3e07 73
    0x48842410022280c8920b00403100c102c160101010458544d600150b00240c65204490b09035440c5c106150444d80724000c100c0c0800c0d80054100b0541c00d06c0200580e02039001c50701041400d5400900008101007041c01804040d600da0840c40f14602075443e880201001600800040c600b00c412140c0d6603228401c218428420382855012804040b96400c1c28ada030305c01c01c1b06440f070601d0024400355082c6114100d0b03142c0400c0c01314000150031840b541c2e21441000d0000d044948121038800c6e400c559a0706150f010710300b080324004900800140c4441002d40544110b00520318213208a03000740a820b030001d0013400388140c041d007804000000303480c6d880700407a610031a40f07071440100200401c0e8540025015041141c1d45a007030303e03050503007020720220034001610741441940041e003181c0c0b2980a181e01c0408100102c420b01004100e001e008408001110b8501a10b008002e88968541500343c160400000000180c200c00a041c102c1d80126150b41d104000c1c0999081513260b5206008440001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 835293048 1250 835291798 835291801
    0x10b0c1219230a081e04050a0c090911060703030b060304050d081503190302010209030f0a05060c0306010504151209080c0f1207060e07050613060206060a0f12050c06030c070308 78
    0x240100ba912440c61404202c02d14502802e4400c141c0d09900000c1545081045108104004584c0c5940c072030701c190700c5000a422a85003901e099840f110305508000315007407030062040c0000b4007102403418148400c0b00d14907110030306450b040303000c4e20700d600615070403500200c244030400070009220070b0480749680340d861003503450500480041b041c2c060031640c50b80c0300503d50071540c3c690090b01031029010b84005031602c072403c1d0100385850290302d59108541c0c81005001d0620106100d095001585a042c5905c2c50a08000007022070240d406607081d94a04001c847c2c05207809180c040c0d1a2504048080c0503032034a40c1819490f6810008494003d4021040b48000074000415103001c095015514070741003a2840c0c0f04e910007030032021242e00c2d10348103032040414103955440103000038403c044441c0c0d00681c200900203081c0240130b086113000c2d0700203003001c1c00701d0130302111003c2c2600c07503c1d0746030170031041c0c2c030b0a11900c0c1c15481080d4580102000085c09031101c0080010405103000ba01e505105 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 835294298 1250 835293048 835293077
    0x30a0c0203030409091b1d04020402160b092404030c0b090f0105250201050f010909020f0301060305011b0c03020d080a0209040c0f020c06040b030411060408010f32010b0c1219 77
    0xc1ca0208807020340501d5000002346c01460550b000d032007100c0700e081100b01c200c013aa0361040c0709480c0a964142c03055000022030960706581071050050003601c0314a2000e070303042c542e40103050108030583c018504420600020307000c05c002c016504200e11000024011403e081c2601d82c0110341040c80030b082d441e259400c005503c1e005001c1d807805101c102000282a80c82c20501900034201010101e900c5086800320054030f54003401000302850207113000041c0d881c1084290000041c40001200c28411484e03000d201207074020504034001c541a0420300d0132a540c41144030f00078410040e810b0b038440d01d000002d10b0f101e584034a911060300d9841d006c907a040e02141c81040340742e0099210340b404100742040001c000130041203501c1044800a02240e0600d62500003580c2075901000c8010b0045540e4821124440c0c40041180408602881021500050001e01400c6800140110443c40000044031354902204008065107294040d054644407065070070808a81c040a201c0c42c00040e05403401c0012 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 835295548 1250 835294298 835294319
    0x1c110303150a050612070e0d08040801020301050901081f0c091e030308070315150908060703020711040e030706050627010e071806110114010b1b0c03030a0c0203030409091b 76
    0x17080b403003030782105220381c0d035001c08031200310342c8600094004000c06958400640020080c00107050a81c00158407036040005109044d04140c1c0a04403c0d0310510543d100ba8400c100d050b0300c500c44c0c1e0328000c5284540780c4025210345010b540401141b8103042d100600219030707526200c1c1501d109680740c0c07049031030f400700440a03502d0302c48860308003202c0c08404010000d0b0840007a116903183c0c2c01d01d80c018a036140c10311070425070f0458402022940002d4003004221144400501d000d81c202c3e800c100a030360500c200c0d82da03030050b0700004101c2c65850001c03403032568980344036039500c181d8000400c641d40e10604220840b80c2081c40bc44050210280200301801d010303011400342040300403900240c4900e0088100d5080381102c000305a5035590b0001c0610203200c00880c035003e0312802da11039642c1c456109004501007003040c246125600002e1111001e41e8004c400c80303060b44020310300354800c180036000090451003181c1c0700030411844c11280380c00f00804c0700c8054214032030344101039192596811030b154 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 835296798 1250 835295548 835295557
    0x605040b07030b0f211501090c0c08041806081b0301050a18030c08040b0a050a1e120b0619090602060112020a06030e0a0204060f14040b031c110303150a0506 69
    0x2d80c8008600c0c00c5518500784811542824203600c2d00342c0300d80204d07620700d550a0907003034031401820180d103400502236103ea60144030520105458a00c1c0c1102c41038403008601d0092b40100c0d240003140048001100966800c480f0190a08a01342c03141809000840c0c1c40c61401812014043e5003050002914040e0078420300098040f890703107650140c0303da0741e0111005940c0c076038100c459100c1072002040d10440000035100d844110b465050341c8079020308000d0040010034401f01c40b95804491641c081503031001039925046541c0d84086940050a40060221700503202560400c6c204519080c60351a84907004d101214884c2d0280e80311641c0320410400d0807440004040d401140030341c000c0184501c02e510203103440c0440e00c25501100c060744d0000f030030349400b503012071051440c010f400e202c82031f1f18000c2079a240c007044504000d0b00c1000c4011948507001d03e000e40c002c1c4181240400b0100b4004c200b200a2144141c1c00e8a03a0303403030200c0d60940d80724640003242c0c1c01501d0040001c505401d26034200c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 835298048 1250 835296798 835296821
    0xb01090914070e0a08240a02090d02040c0309050a08031e070815010309020d030f0206090102041d04170705030a4d03040303091403030a36030605040b0703 68
    0x2a122aa25102c0a6607054002c1d01a550090b141c01c0000466010500c0702030304a141ca148030340340206a01c0c0340a03114503c050444c8000342d1042110504a98540750321160507941501e000c00d44601d882400d900510350078030060b0442c016503410408100c0d101000314400e4100500a03042c507071a0448a01031040100c854201113101c0d0780c0407848500450f0001c8440450515000c158003a07107074045500c03505d403460210086050844014a01c64042c01403d52250302c1c00002c40c00c00b403402561401c40d40c10300c2400328040703c04401080c203000c620b207046804240b4440703039140c0d90a60392404655980c030919216000035003aa1224002040b26804010003119025084601010b001c41300b0b0380b0100d518842003000301c18403402e4038030710b003040c03001d04001c60094a402d0103191520396104039a000301c02c50030b80300b0341080001945160300310200110368942c0c0503980320000700b00501842d29403420030061000d550700d50000010005150001c910403072059007521001d0300d80580560981e5081c40a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 835299298 1250 835298048 835298081
    0xa060903050307110f06161119060507060b061b061605070206131707032a0e101d01030317090c0d050a080c0a02030d051306030509150a0b010909 64
    0x3403000c14281840c840c10308800402185c0c4451481c400901968001c1c5a0011005451004001440304d04001155030034400d542841591441030101107010a050190006000c1c0118035041404000d622001c00b5820103020a0b9495481aa8050325280c00c151804050312a040c0020030700c51141c0d600c03c0034488540c0340c0a09121032030703080010b02e4201d8200403240e01984480082c4402052980d200340c450103a0142c885070b0705500740500c40059000113101002050b20f0b02010075403400880b401100c8210004125a4548064410442802d60f000f2444040da807108070313801580b0f206a46040304c0c840d46980c07140c80700c09410f0283d40709080300c200e0b615400c44c1070b18640508210303640c03c201ca84200140c8050003565940c01c101e0340c12803039440c2140c0d40a25600404c508040011320700c000624203209050480304100c2120040d01030040a08164440e004104130780d80410205600500e107001218813494030340c50380070050000100483c00100003100020b0b2140480c801c0c04079a42a1041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 835300548 1250 835299298 835299307
    0x105090c1c02070510060b090f0604030803040326161b030f230c01090204060b03040b0a091103010921030c090b03070504080d030605040b04050603150a060b04060306050a0609030503 80
    0x3624025000fa19040ea10f1340030702601005100b40b14892070026095400c0380c161614180e4042c0110003030110b034034034061300d0100000d201060181090340da200c0d90500d451500c25a4541640c00c40705000011040208048401d11441140030b208441180c01165228200c05540444125280c0c104400240211340c0d54040140b2040c418041c0d0f051101c1c10071502105402146102d20003036200700728146007030750740390341120231442d080c0205e400405084540c50b065080c142c075102d4001102410300429290740c2d8240004120a07510014400907005000b00146403480c20500c180d1025491450307080c81403d105100201d000b841040310752a1966180404141090404000d660010304110140802804006040c100c10042000d80004594020035514500810301c01903e000f02081403080741403204012503902d00155024590000e15030b00d8455469034814100209083e0f048182040340c00100801c5203901074100c0421924250360300d92680d90f84103821034407140340780401483c9400c200b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 835301798 1250 835300548 835300597
    0x100b04111e0c0706020102090306011512090303180819080c070816020406030c0e13120507060f0e010b030c1005090d060e0715030e07030302060a0c0c0204140105090c 73
    0x41d040e400040074010452070040d86512242c9400e980c1d0f4005001070b90000b0703000710300381001d000382030041c018003c60b4004908803943c094002d890008190706182d64039540a81818840c5d088648911071640504090404e1810300b5402c640c4040015014000490042c803c0c0700d214501d00361080c4c0d201d48495041c11401d0f980e4088a6200d0381107015801e95541c2c1d000090307a0780d0b21414000f94460f00304e00c0405843d00d07000c1a00110010040c0d440601282c5982c00420042c0b450317150025502e143c1baa680b1999841c01c0001405003008008500386072904981c0e0400056002d045526004c07002c440e542040c0c1c00c104842162061058030000340c0030320060b54142460f0344008889482401c001c60807400381410a07281c41c9250b4840034088190884580d002030f0103100c0c084440c0e01d0a00078100c0a411030714083d40d10903020b011551400c6d42c0d4a0a29141e61203212003145c015801030081c801c256500d482d0304503207003081c09818410b6452070040342d600440401140d4038105101c10701d103210042c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 835303048 1250 835301798 835301827
    0x303070e030109080a090e07020606130e03130305060603011107051b01021f060923011a070203070e041218150915030615030b090103140a0f05100b0411 67
    0x54849415640340c0100c0400502c1310409088040e803240d4400880c1c81c41c0c01030300035600401401210a64200c001804802d1b103401c02d56044000c4801c40c01f2070401c2d00c0e464a076241d8419501d2041e40011541d00110401002040040c02658220000d0011a411131003101e03491251541c0204140d02c900c040f501d00b04010022000072040500540b2a40c00100c2016000003428480c1b440c0107980d9440309100c84900380c8941600310614400550142c11102020000004180645101c654008110b40c800482c0c0104070b0395050781c05416540e01315520580d404c420340007502c2c00c44195001422014016200f030b034903400110310006d05c20719440d1510302c0302006a0564000340c41007002561020034005114007900075501000c1e640013a0369072410780c0103240c00c80c040c81c48500301404c12009038465a00c510000741525000140e45050f84403214082c2c0c0b414003020302c001c4c61080303d0400241440070120b150305d107900c0b100038184020800c0c5820881140d0840c8075030301c0e0f00c0f0030502564000080c1d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 835304298 1250 835303048 835303067
    0x30f120910052a070e010e071d1e04050a090b0109090501020d14150103020a09210b040308011701050c0a03241511070501210b1009170f030307 63
    0x4904100c0d181003204000d003d62541e80c0030400201402110440303603603840c100207110082c80428802107080d41401804591000007500c00001c100e10b180c65002042d500012102400c0c4000740065100900007030600c1c08054185082c07440341d0707d003000003140300340c560207400b044550010440c1e00a03800e0802c0d490040c02084825555503509000e891180d142901c0351803842801828030488604d4480c4c0082908445031601e0741c10580148041c21461703810811010a441801c0f4000d482d8585e021400300c410350f40f900000d4824110f50f01440b0902d44c111110034180c684454141c400d640300e1100d00d9081c3c86d000c4d111703c0c4103403104200c50f07006603100f80d00010000003c002e10481904468001307512801c0b13580c110320480c0201c140404d44898100c010507a400c05000c01422543c1d14150000e07003500c0c811102c8140341d20740582c0e41c804882d0290f001303103981c0c100189401c0b07400400b0040100043c4807400307561010800a0f216030056240018050340c040f80c0d0900442c5140d23502c40084a8a441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 835305548 1250 835304298 835304329
    0x30c1107121502070b04060e0c0102010b061b030c03030f07020f1501050103230403080105030d0305091209060d050a051b03090705061c020708181012110c0604050c030f1209 76
    0x1401d101350800200d24513003440c003450280c28046000380d40c007e42a410102c050748034a040d0380c90b00488505076100c480545620200701d0030010038080b00914524150b110701440ca03c40c0f03000000c01c01c00714508480d030860254003698210b0b44614030000409a0b01d10304501d4451001c55013100401c4190301c00d800000c80d4160f8915004868421142c42d11304594007500d0460100c3c5031000140020304003005102920607440c901030146080c107501c560b449454090300118241400960919203803540000c840c143c989a010410161034551a00070040c1000d89041d0301000d001115101e80400308003e41e8001c41900d00601007443c507000422070340c0e501030b4050041001240c14045080111072000d09603060003500311594072034680740140b42820981041c54490060170211604036688400305c0014020200d000041c490031f0004c0d00b510741e01401d002c2200710301c544400c0004005011400302c9601c00103908880030791034800035041e2105903480480d4003401081c08200300c1c500d011083c0308040c6030f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 835306798 1250 835305548 835305551
    0x605060f1002010c0e1905060724061a0315100207150203030a24060e1305041a2202010e0604030f0803010e09031606021b0706030c11071215 62
    0x1403803101241070089038810150160750f454540c61440c940012008110400840f00d00c8080390001c4010300380034026000c0c0c0340c0188404034002007004000d000701f8004003081e900e42c5c509183c50a81810241c800c3d4040c83c5402c0f400c24410f40040c01010007075074000e03003601420070f03101c40308038081c410650180341c183ca0840c418244005407900b00c1e1115400d000f005540030310355a290107000c000c10744a072562050544483e80f08088005e418000911060b80c0181c03411040303036448c0b14000303103074012003209220b002e0b494101404104494040194841c100381740e10f034141641c0b241d100b01251341103040c0031049400304101001c01584551100c940001006019904141c3c90752641d40c903044900c42c00b100d40e010000018442c000428904a9110301c0090046280a0032201200016015814014451900801c0c0b00c11950440c0303408100c613103118022101125a106001005405001456000720300c8180d024015400046802e6042c0c0e80a115030818042c0c0c10755038a4441860144180c8209 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 835308048 1250 835306798 835306819
    0xf0d150521071d2418010504140106081b071406060a0801050103081c09060f15140d0b190c0e0108071701180b1507110102030313060506 60
    0x40c1c0e0746040841c180040c1000310aa18184288510300d0000d16400c50200495a401e01062602c103201c5440c1d44016a801d01c04480221100c01a0800102e00070b060b078000c1060070040c8015462954641c100d40c0704440034080c03038a02e1184040d00303020038015000015001c40000d90800b028030819511075066a40140c6840e02a445030000c3c500d0700c89400c18141c11900a00840d840c1445283c0301800c9110000c02065240d5035400c0201e21800411070754002d404903618911200e00c2d804401081e8010308203104036072102c9404d10080048440002c0122040b41000c11051801c201e03007024942c6c06808030016100940351400c11a0000300024500c01ea00400c0b280300096501401c048014592500b400d20030321031001405520b00100900100308250701d100304490703598001d0320b0465218406e10710708440b56503040f801400d1440140744d0000504203224410303021610092040a02851a0b401c07110000e000482c1ca0340701c2501c44010a640d1641d040022403041d50100e90001d20052465105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 835309298 1250 835308048 835308059
    0x601300b0105072909060f150a0e04060b0108150102030d1107051c0801060f1d150f0405040606050408060c090301140702030c010c050a09031514090a0c0602030f0d15 73
    0x200010305001e044100c040b6420b0138560b5205074815030000d0114019003010301c0c1c1340c1d001c2c28044074024120503804403807400104590300c45034415800350480f50b00e010002d00c6c10303040c900068105640554002420100010240410807184a014100c160302039132130b03c01681604000341c000105482199541002100c0004070300704228000340307082001d6004039004140d0301030411a0140e000c2d40038040c03020081c407000d07584482c21200e180c0c40c0f03500300c4c14046029008120300404c3c80640084c8100c00260b48901000c41c0009001126412034050100a4032580101c0740750041e48174049496200c600440c400c07000d01000745c5000003000d000011007601503490484805010788202000d41c000144802400c034080c0144000240c2e03c1c01c1135803415844420050030010103110207800f10a007a00c3c1291103044c150001095494900e0140c0141d00300004010f44620294a003114481c0d000000051200c0c004829100c0d8159400084e5080030a40103420000e0b0400418540d0406d00100d40440d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 835310548 1250 835309298 835309313
    0x40b0901171b0919090b010906081c0207060813080a0309020102010c0c0c051909020a0e100e090a0507020c10030641130c080601300b010507 62
    0x202070001c0c001041c490038540c5641803290b0100c040720a282e408840c088161200f40042d5089000c58800340d005001480003800203110000000303084090040000039001050f421680c20341c0c03048800d50f00906101c000c9880000002013100c4007607080200c04003d0b4038040c0c00c48541c0814101b07441454a0480d9960504d20391112103600d010981e951000015540d091084817031401003418090300c1d100380f5889140c030749030030362081c0780c4240340d03070f80158100a540c0e00d0250000d282981d801d544468900401400c3c107005a48818000c942184d0980c0060740301d910843c0304c446010702400e07100e44038295000080d01c8001d000d502548030713600400c07100d41c4518401180c1c0e808581d07000501c09007030041800c1c2e240b4141c00c40c0c4200c0b4280007401c0000c00f9081100c203680d0141012140407051902000c0362070400e040007000c80580c948044a44021341100e186485100b0907030725044002021008040c0c80401c00b0304d1801c904d0301c0c070400b2309400300f22544540e90624050400908002c0240d59010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 835311798 1250 835310548 835310551
    0x2070303020304140609070e100f08030309160b090112020c06100503010c0c02011209030318200402191d1c0506070507050a06050c2703060c0c0703060b040b09 70
    0x1000241d0000400040c00b8100c501c1e96280e03844c20000e00b5003030524040b241c0d903c80d41d90044444c04091100418014031600c801403000349a03c4a481c61202d40d603981c03542d2a9041122014080e0049404141e5100200400071050781c04039900c060502800d2401124450092000304203043e40c01c002e0040401c2c0c003040007a100d040c41d03015500301a410170042c1030030750300e010700c40328103021041e2200c00041c8c1c0c0202031000c40c1e000d0f02600080041c41405c0c200d020340400700c2a242c182d4941c0060400b401008111801d0503040200c03210881051038050000f2403080b40780c0241000c808484403c0b10707a10512280704112800f00726412a400712031b0000780144c0720504064101d041c0d049038141041401d00c003040c4d1184190510038102034068885c6500d03003000d400001c4c205a41d841c0003076659254442600d1010302c08401441c03548049010f841003009030880c60320f202e071003810001031b450340700a0b08075040480c010018081e10b91441d42c40c040546154011583e004e03440b80c021580f2a2595900103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 835313048 1250 835311798 835311803
    0xa02090411012f0d020609101a04050106020d020d18031b170c090603030403032304031502090108090705100e13020d021c050402100c0609050109140f011506210207 72
    0x900e0b80c040d1110f4014905511000300800b55008a0100321310080040356a4417484107603a00803403181c4c02c1800d000744c01d020341403255601510706800446c1a540c00207803191400d48680845608100428003138945450700c0c5000541502d8182d418070004120130001ca402c1643c06000d21143c603201e41c7e1421070b20000b007880b85c071a5030184540c4021840c00380215908607000f40c018524060031520020070055002055510911b01c20301e2408080c1008400c40340156004040c42684941781000759029600880c0391500041c1d0b0100030403862900460070200b100c078000c0034921220301610090301c45a0f54443d00c0d40d448640704641051901e85070004228140000400581d42c041c140d01d09502c0c1199880c03401d480901e00810000140c03205c000d4102d071602035040556001d5000d2814101611080200800650814140c00704202c900b03001d820110315103070180c40c00101c1041c00c4500725007502144801c22610a41c003040544e0041c40440303004c01d07030f42d064504021603d40741002a40d000c030760704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 835314298 1250 835313048 835313117
    0x70f080a03060b0c0604020f010c0b040c031101111005180a0b04140313030f080d0218310506060c0a2f101d120a050f0a0209041101 58
    0x3140065062090b5000f408415400300e0030140c980070b10507554400140300a001d41441001402c0c1603000f040c03003003015544009902030354078092810f114040b5032031104a5040c00e01d260317000c819600544c112140c42201100802d402e400340c08003c00500f6014000343c1c10050301e134894003208038082c0004e0340c40e140904003a104608040c40e2022085040f104084016001801004004400c0c540d03c20100c9800c69502c109403080ba060691b8544507d8151049607440010075801c1c4241710313246022036910444802641d080550a202c02182d482004400b09403191001104860b1541e800a90844005407620b4200391440400c24501082d902c1c05407489007a820800c0e00840c18040b00810000c0d52000601500d403140300880c1034004000303030700c03030a008124244100903a050003003015400310050200c400200310308080d50b15542402c10a0341c0e6805240306000e51100009021401540d018044007610f640e00d8030784400a212143d2031074100b251201c0005d100c5d170300441c8245055001c0000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 835315548 1250 835314298 835314307
    0x40510020619060e010b130e15010e1509090c070206030403081008150c221701050109020f070816020315071e0f0c03020304050402040f0617010b16030302070f08 71
    0x40c641c450560000700b01500070b007044000e20142201d45019411142100441034440b00307181020380b0114410f422524821100108002e9141c0000c1e0b144401c056081e03d41c14000c03070403203040c44402d50218084410b40d41c0c08100229031410141c240c2c03580864801a01811310403d42e000407050b43c025102078000450304030601c0510014859420009c00102d030051441ca400c1d400c00600d881c1e0001e054108010000c500d41821030000a803826032080004200001d40b40c951070582c07844190741a0203501986020b001040b41c200c0303442111103c12641c0c2e015800e0182ca0340d600e10f000d60116100f084040e041000382d4006840801241c0c1074a040c40310042c0c841c1ca0300540080481d102600040e000c1c0041c45180e5004680003070708102854800e141007101d0000908007640355110341d601c2140c00034400100068440c2c04c0d4500e10702940c0c040d9170f9805511001d02c003071002441c400c2c0100100e00e41d003000301e10160120032030b104401071f103e8200582005c1c07983d2a800101c816851040d00e040310b0004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 835316798 1250 835315548 835315561
    0x120b03010203040c0f2903070216090509011127031603050607120c08040b0c070c150807020307030905040518010207060c12290111070f03021503010501020d030504080405100206 78
    0x10217042c01e80390401d201c0786070000d008a401b101305d41d0359840c002d0000c08203040303030b100f4081c0070070403c1007076910300e40d0a0b6075811003002024102d46528541d4038152001010314103540484100c00c030070117004180c4080c01c041d070340103503502c000380c03254503200b071807018121001c842c104000114021805812030b0300d0104406808a01030784007680100d4500041506203a4008015503041508000040f11f50341e6000c018100d24415004042c0c242c03582150005078000c4401121700810500b0399031600390b81c8a010090341d6038022980300900cc074a160f41d013486035041c268003080e4011503a561861179021282080c80c2281d208d201c081d00e90075141c4080c03041050b04140284003c6481c0c250412140400c00c1520100c50b80c0400c02c00050300c0c00007200b0215a00c02c6038549460607000b0181d44980e0341c2c90080201c10f41251100f203008100c08404170040284031001c0e01d04179041070300901101d22200030102c000b130100030006c0ba00c6500520020560392664032584d00103410640041c07600c2c2c00c060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 835318048 1250 835316798 835316819
    0x30a030c0e01051603032409061e171c170609060d080d090515041101020a03050f1606020a18052b06060504050c0a0f020c030c01120b03010203040c 65
    0x20694541404000081c07482166400012240841e242d54104590b0015030318048000e05001d8120100309550348a076084290741c0c0d01c184c0022a131500e0400c100030f551b40c020120600c10890750800f078103d40e40504002032064039018030014140704003a1a01440b40c04020355000c0c601d103000400080a0740c80c04503485042d084440c0c0c1000048541c2a510301d042d000050051b03820b44d40082142c80003040e0355450302c200e9046009013503402402d8560b0402113324104814404803000e5030000c0741906200d882e940041513142d2625019a2050b28141c28940400c14582c860702c0e07220000c4e51030400110100d0013074400341031030b207510340c1e0f820001c2c003a001003c00c8401081c1d00250301ca080c0014200281c1c0c12105410b80b01c0040d08140c00d9001441c904005008154503845030f41c019083c8402c03c084a98008020100d460b00b030b0720b98400685143c24126542c208540c520754050f0b00050045c405507004e514001042c4000b40004210061614042800d90b0816079046032110740d011800d20428525 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 835319298 1250 835318048 835318061
    0x80d080108101a01031802040e0c0a09020a08012102100518010908072c070309060f1a060c01110c061602060403170612012901031505130e0f030a03 65
    0x70310702c14030104284040c0c0c1c2c0c1c0c225401880c1c650616684003060301003140d0700c54010311425001002004a14014a4159180c400b52903d07a4410501c081c40862689603c1c425070748816071079500d005c3d8503820300481c96144a810281e0543e4800451800710060f5599000c42100c442995102c1d900c556001098804c9258903a01071818810f21800c1440001000980202240c00b41002e1f07100031803a0340030390090141607200b610103080d032031b204005c40d250701504590380452183d0f01c1000000380d102740710022036191003030080040400310309009961510790f000d401010368130800010040150850100c050340a005031401c5c681200d0b040090503000c089045030002c0150000d801945400d0368014251020241e8994004c040c4c400404c50a840322218044101901802008011306848550f05889030100d40030421a540e0080ba0921b94030a000d10344020003c007507424243c80c00d000811058504012400e070301940d071403100840c0481c1c01c00070100d1200c030100195907188030342c02c03004054465 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 835320548 1250 835319298 835319323
    0xe1006030b2403060402070f0605071202041503050c090301060e040506070c080f0f0d05010612050a022d091801060908010c09090f0e030d060f08070e0619080d080108 73
    0x52640c1c90010302d040c0c0104807288206450b00c0d040e0349a4036000010000d0060701070203000c030700c4090302c1a410805a917100741d01501403030710740c0400e0300d80100e0034809030710441c0121249100c140030981c1c083c50084d0811500080100281420b1941b1100401e08640f4268454640c1345280002e2005100052110070340103203d030b10300b00000e59160340320f81d40d42d441049901546440c000a036240e0f0700710f01006813201c850200000307001c2540c0d5218014044900401d008c0580e42c40e200210700ca103001c92007290300c14540c3e01503055003103d520080502c0c04612030050300800800f04200c6420790b503184040140c0511000e00c0c941c9550502c0001401c0b4482d50f000413915a241440c40803007950813031001d408032030642c1c3c5c01280346800e40200c0e201902c003140756060244404030f080e0140040300d400071401d0751202000d680c00c181c2e441080076074610f028402d0402001c0c58102150840c14088141701e05081d0300c40c07461a076607640b50921444c10241203070b800e00003602c2c080180300340081448814036124 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 835321798 1250 835320548 835320559
    0x2030601020304050d05030415030e100e0606010309080702090f011a0c15060613060e04200f07080c06010806220510021308012a09032006040e1006030b 67
    0x1925000203942d038461801501d20a016801019042000030800c9a0107886480c0c1c200304101120100074000d841145101c4100340240000340a07001c03018469060b01d5050300c4004c2005884402c015402403a0104094501c4001040341a000da21006100d602503002111440c0c1298900b08032042e20440099007604200002c000b40d0200d600300242508800c0840c04401d4155280c150000f0300c0ca10402d502c01c50030260903440021200e070031102180502e001580d042c00540c605001c841c3d5074000b0400740719070300602030021f8420b20420310040c05009100b03044d000c1c54254110306540c50220243d02140707050348400108046041d681a5801032021202d0210010b9501030769240d031102c20005000014aa003c104c22183e411040324010007040050001c0011030025203164401b150176400c001145454084005843c1d4802c03c0a401141d030004082d9415410180108002d102c40c440142d84c0000300780301c041032058036151918040c118100341c100c11b152070040050b0a6400030b40400c1d1003203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 835323048 1250 835321798 835321801
    0x60b04152607050c0f010603020a0f0305030d020313080d32152b051519090f060606080613060614070618050d0305010e070c030513090510050906040203 67
    0x6040808aa280e41070715038000c066a0b40d450030200c801d801060f107252404d204242d40601d08407010f6100c0816280203803401e1056544034800741ca0440c0c00c07403000074080d900400074038040d00c0c04d55005e550440ca4510b881701d15000c0d95280c040668108540402c005540c80ba6501c0d072203480710040c41e140f00614103010001e0804506a801c81c030a004111029608aa031103150316580e034110300002c48583e68070f01500540400b01141c0c41c0781c00c00b18085907035205203c408401d240b08003000c903108114101c0d81c203050300c00040310380e0090194048211500607481d000000003660310700408000e82039a9480c40030a241031810044030040f60b1009640ba00e103480b00901900354080e4402898403038143e50281d84010621b8410010444451400a070f100c0e14554075080107804102c12800c1801030b501404580d03202c0350212902c00050341c0410208030603000840c0003a0040c800390a040b44003c040e501d4040d5524604010340c2d108403010008003980030400d00c003a00c0c2003003186800140948086083d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 835324298 1250 835323048 835323077
    0x1210c0512010f0f140a0504060b0c0f0a0b0103170d050a0207290a0e16060201050f0709080304050d140a050f0111030c160819200a02031b03010f060b0415 68
    0x140780c964042c04400401560940001ba100d43c209040200703000f40c81046490b82c2c88145107801e41060400d00740c6405100b207100001d5200113003a80f80e098009002c22407503486c40d95441c44a42e05084419403509027404000a80e880c9889068424105010003680e1442c1902c0d00307a500c541c0f0b10380c0d00e440040303041d00102e541842c14200503500c40c5640b2400524982c520313030001d1800340c0142c5180c02d40500c0c0640403d203294190001e60090205441450b03103600c5090044e00d0404060144d00e000340e10a110030005840d2801b6050400d03030243c408005108140412942402c964610542d116071008095980341d100c00d01c14100c05c49521080103080d070400351101c04152080840703500580d004d4200304414132095030100c1c1c1210710601c5551085540240b000340c10100c010f6501ca075405040c40002250b10b5003c56503400850b070043c081c3c80321120f110b40c2c002c0c1e1001500b5105402d590ba8030101070030240b00d449840003074030b000300c4143d886a01c2d0010b00c42c003024511030400104a00b220020780f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 835325548 1250 835324298 835324319
    0x6030f2e06110109050d030b0307090501030c0501080606040b07030c0c03050114040c0803120103110a150c020f01050304081603090f060203040f210b1b1c060510090501210c0512010f 80
    0x40c101ca41f601081070851080001d1910f0903503000004801d01d00000041002035150a0600f20fa10a881e140d5181c1d44d20010040103014a20500c1c10007e01005040002417090110780c42c0300388922180b02c45961a500c80900b100d0307062180322214140b810900080c0525504501e0092403040011031414151038a0a44102811320006200f00c61030800c40c5459940d0a0910025185001940c49811080403000381203512000040c0c0c003911020a6140075940308030300b224800c981000915242c00194003017108060b0307100d9400d608015142d4008101c040c40b81a29800800c2c9660055844e42c0c10f008080131800c00c03990150740c0401c00141c0480740d084503003206181558000d910508160f030349504400c107000c2400300c6c102c200e44000071300070070700c40003021007450311120400100080f5480d83e041c031004400150b10a40840e030200300c101305c9584248a0400c240c075a03400b02c1180c032800506464142c80584030004003090000c684420004100c90038035004104034420024043e103041030100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 835326798 1250 835325548 835325563
    0x10e071a0306040f020a1e0f05120a06080f01230609010501050f0d050423061b0c07080105040308061c02011d1c0803010510090506030f2e0611010905 66
    0x8104400120002e8143e540340d03804009030032482c40c01990b403560680001404180b440e070807980394010044c05013911074414a0b0f4152032400036201c240c90181800400200302d0340040064002c107440b2000410941c20600c00f0303c260920080001c1100f20b10408265045a0050301c2c04c0b41d5840100c1c20450f80b44c4c1c0d000e070820304650742030a040e9501c0100d48240d180500c0340740d9488210508020500c810002203011080c074181041043c41003540b0301405043e00e40409640003190790b00e0440b00445000700c140b0040501c5c400740300403105015130b20394945081d904101e41c2034012032011030400c10681044c40c51110a0f410010701101908601c2d80041e0007144407130000449100c1240070300a841e110360114451111000100112401040c0350400341c0c1c0c0d2007400b8032400340d0103004030b0b00185401901c0d0041a690018006811b6944d41b072000000444000c0c12818100d080550051004501171450b500c0c500300039201d0f0a0340382c107100c2c0c050021310070003500455580c5484843c0010940204100c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 835328048 1250 835326798 835326839
    0x1309020304080706110720010e120f01110d0b0307060f0f170405060403091a04030b1338041221060e0901050604020a0503150409080703020c03010e07 66
    0x60312500e46042c0750106000f0240c00a024900c1d1841d2184e042045001600c10320340f165081c0e00340380050044000301c6e140000700003070104090400320521460b00704c40318407242d110711048684903040c002455003035446030401320700c0c0918000342104003041c0e1030058600c0d95006074001d00c4098503001008080c1c540d00c85042013000840101d0144c8640b06560f1140064205050580302e8109030400544403c801e07202100810011440001c1158204c001420500080c80d01541440c0c556260b100040350020124142c2080d1083c00303c0c001150690004920300190054150004061012101d030840c0420207801c41600241000002501c2c1106100e0090083c548001d5204074405060319042c0c410461605e060700b030445c0031901c50009410180702c0d1384504024002034881c5024841240b195068010004078200002a0002d0030310440803c5404090310018004040f40c8440b5a5500445412001030300418008042031409000d404c02c0d0681980c05020a1072801186400d04107240090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 835329298 1250 835328048 835328051
    0x18061e0c09040507080a06080105160c062717091c0f06110d1104030203210403080d050f1e0703110d091b080d0818010e0708070f05061309 61
    0x880240008041c0c0d142007001070300c14000d9042c034502c068041d42c3c003240d4680140c2d02d020b00c001095181401064064000311040000f8024011003c03102c81034620b50175280e090300d44640c4420950341c3c805036150040c0c0b007001450780c0000c038948184c1030311071811180718505042c80249400d42c4d411a03284144800b0351086003c9407528940700c03c82c1460008090005c5c2e240c040c0009003003000c44028100c1540003c0304001160040146089900075408080d425500c43d80aa11203440080d200e0052104c5100c62903080554039520b0044d00e44c000740c064510203840d1014000303555680c00c40c280d00005c040d4032042c1c405000c14071040185100504080405444e454600040c4420808031400402c42d602c0030f2004c2c48403810a600da12801c00350345041207204d4100020714000200b00d41c1c041907050f40e81d40d034594031414000000b46092109184c960755070b48800826101040040300000c04110018100d40f915180c802011000c4540c4407900031042013280e01d40306040b00c8a0b0304151002c0920 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 835330548 1250 835329298 835329301
    0x506030c062b020d0e030c0a03030e0f06131202010e0a0b07140c06150909030406140412030f03051012120c080c011e0204060c020f0111100518061e 65
    0x3828103422050040d58808080030b015812440403642c000f0718496078421003e01600d26010003c80e07480c41002d00c41c059a4005000b0b01c00007a100c1c0d00210800890b1001f01c80c422844140d03c0382c10104280c42d03415034201e011080c10704015009040030741074800c50001f0081c0501c2c20004548908580c42c00904501e44000021a52030203540b8941c0c5840c4c203020203035200c0201000c802d6903020141da1891743c00d40019440d03025031418803003003803054085502450034680b500324155480e94480810b00c4400f0414400811140502c045000f0228040e0345c4d02030302e09071035940c003808851b070180c84088000b0600a0611108030920382c403100041d0300c8208500b0410040e0001c0345c040c0e40d401c400400800300098013007040081500060341c1c078411054160440c42d1280f0f046400c922480c8140c101050401c1e45003805454102d004181d02801818804116015140347c5400d00e2840c25440382c40c240e40d04140940410300a001c0060900540000c019038104030000b0034008440c1014886d50f00407520 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 835331798 1250 835330548 835330567
    0x1090b030433062d17120a0c03030509030f0f1b030a09030b07090e070e150c0a1e1e0321050609061e010f090e0106021509010506030c06 60
    0xc84603000c0601006400d6884464841009001d8912844c50207508800903590491030303030b000c1a0b55400c0a0010703c0840c40c030f0114071a85c50303e1a980803022034064200c10310081d03210b40c401401d448417180d69070746404402d49009812508080c00d4018540c0c001c1c000354000490542c2203c80c00f4507401d80c110340b80e60207d088540d100304040c0985903540008207607103000a030800c0204e4140c910030400c03d0701f030b40d990b544116030800e078500c2844125060b080205602d90700444d0a102c1c0358001a03c41d505100104001c04410b0b4420390746000c25074400c4c1d4994090128207004c007103860000c041640c450b8800c60701c8400484c0b00c030844a0225403003000c0040c08240c040d1201c00002c400b650050842c0c1c05458030290010b0078202c0c1d80b0390003000c41c400061402c0c82d0a1240000140c040200300141c407052200454202c034598000106100c0c50303000c0482c0110945040e40e00038a00e59000349000c0c0c8200c09108070401025204d001c0d80d0307041a06102860381e01040801e00904281e8040d44c03036000b100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 835333048 1250 835331798 835331843
    0x1602040b060c010203010f0806070f050f090d050d023c1f061517190b090f1b031302010806060d020307030603052a040902030106050619080601090b0304 67
    0x3400c0865020500040b000d4001c0e8042d00a0760491343c120030b8419129580d8140144c594004480380e000003509280e150305043d01900240c60400c2c6c403116031504049041c0082000e01d60110015100703540441c84074a5003e60400c2035032784607121400b4403901440c6070800c15084a01c3c0c1203004410200011401c20240400c1154900c25080c0f0001c01880d40100c0348208001c000e217018601041c0805003840038001e0241d8444080e81008a6070f050140ea1041004982034040982d0812510340b50700706e044035070740c0d20005240110000da00091f100d04141122403001903440003403101d5890140200214201710106642d4015028204400166200000a0940d1040b07084000e205803000c41405500b50340741c0e01c05800e80f0f203d00304840c14820358600d070f0a442088070b000c0701e1604488054580c040d06260b000811403a1010f4000300d030b6180c407040010241d80017411070f000c100c400c2c9219000000d6001d00c2403600444207013010030000382010b101030006e00c4024006068050000307025499044403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 835334298 1250 835333048 835333061
    0x12140a0506040b0108010b091e06210312060109180b0105072f0a08070909110a06180e010614090d171b010b010207060c03020a0b070e030114040206160204 68
    0x41416280c40d442e1500e07005070120340a014090b4039603c3c0403001b060a050070300c20a40074409041d0208070300f180c0034100f40c1081d1801050b40303400c01d580c512088c400141d018a84180ba44403800559160001428680081400245401c1c100302240c0e804020305114210103001620004201043c00c030301a00040c3c416200f03a0100800c2d0311038091010441440c0070b041c2d00700d0a0180101d02c10041081b40401103005c800c0d000d10f00c13507508655010070164245500c00c0c1195485826000402d021071780006401868640c404c0020840040ba6400d44c50345410015021b4101c00d2071040c41e80d410000004c00301034461040301014040084c09142d02c3c0ea8000300b1000c020707805046008001000320a0a056410000303010000c803000c1c84003402098030600444820342c006074024840645807d20403255401c0b898029420750248015480c0424500e5290324847d00c426120988110042002d143c212405003640c0706080200b8004c1c44010383d40c1008981c044044c2203061620b150084c0001402001c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 835335548 1250 835334298 835334303
    0x20d050a0c0311010e0f060a0c020f12010c1b0f120e09010308091c11101404080102031b130308180604120302010b030d08011a0f1611060412140a 64
    0x1e441100008110100c219900200001c0c0d88420150540d01c080c0001c3c0b12418540f203600090902402d248a840b43c0242e4042e1400107002d40c030b40c7c3c03403007401084000d8264694100309944549030b1480c0e0540110544441c08070b80304948950080c9034540400910120600820000ea840b0600b02610b11070004100c1e000300042c07082c03240b0b594074640410690704c060070f15401000c0200d003418010085003005010030b5040f01848121140780420801028565242c80c41031140d00c8903800d2211010f4000b500c0508000c1c0001a41ca00b80400c014800901c03491400f1040032003003201040241c644445c41044a85c450265078940144c480c0b40c0900032480003480382c20610119000424107002e000310f80c035040c02078000300002c070191024151155402602c5502060f001c1004000070340d602d8070314120001007040c45504104500c1030445081e44200100151300e0031500c0d00209016a164408100b09800ca030101d203007900d070900305814200c01c100050710500440d00c205401b0311080c05201c0050750b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 835336798 1250 835335548 835335563
    0x609061703120a1d1c03020720120304151e120e0106080a030c1502090d1e1703100f050102101a0a0b19020c06120603120d0204091104050d020d050a 65
    0x101000d43d4541d44840c10110120300c3c0000e000f082c0d045c54068402c8614031030b0008800200d8108106c203110006024142c466040200d19862007002c00040c0080c10240c20000501c41a00c040031074010a0b00c141b400c040c0c400c4416a40407400d8050700b0071a480307010341010340c011402c45903c4644900501c0c0b15481030540740282804c035010140e12101f003c4031103100b400c0c00c0d890700c901003182d10308074041c400109030800e024410351008070702d00c4071400c100d038a02000d40c0ae151110355a289100003d003590292000d00c03010040c00101008400c0032405000c101075040f641700d1805000035500c0401c680c006021555801404c270b66115200003082004002520b5054220b0b07481510444d640d11020400150194400154185a03c045240703200c0c1741c030050946062140c022a00b20785610b000d89596803502c2844164500c41c110035015008641c3c20765030050703c503031800948800341c2d80c400d40e41d600c110034104400e00440d074481e05580190b42d010340f402801421035107440c910f4244894070140110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 835338048 1250 835336798 835336841
    0xc04020c010204061b03051204260c0d0206070912051608031c0209090402120f0703030809070e040203060106180b040305211e0c120d0609061703120a 66
    0x4030015002003080f61a03558840c0c0c00c42d4140701c60345c00462152140240015800c0007045441d07242111007580217400780544141e10b0101000d100e01e0007505800c21601c2000216000e4400c81c000e1140082241c0e0a0000d00002d280c82c800c020200717540c5000e250310344c12220b0307103420501204000c2c3c220203820308410311140e581c543c20302641da0303000544664004480040340c031801314030030300a4030082c05000e4144802030b11540d08100c142c9481d00b4103e0901c0c0b0031082010420281040032000460090325071155070f083c140d140c82c1c1002081d0300702110018a1000b4003005031030005013581110b046107030140140100000c1842d640d0402e03030000c100d034603011a0203c20f0201c003043c243c040c407034000e14095840710421907849040c011410511052081d9444034600180500e00400405811400352015648010104a03140e00318250185001e1754514050161318940d1103010050704401554001c0e0341125010151b036032040482d000c442c01108800703e00910307820f410201c582c2c203510b41000c011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 835339298 1250 835338048 835338067
    0xf1f150e040212330f040b0d0606140406210201090503060f01050a091817360d021f030b1002060702060609220f0204050103121713020d050c0402 64
    0x260b19007520352040c1d11305803140007201c02d00c0e1143c010320700d141c0314034a602e4403e801c0f008102107a1a14000140c1054881c41c24900c1582c41d12a0102030320310542000421a082110300e2217900c2c440003400380128600001881140740b2070905001c0314081e8610490350031030500c0100d6501546512140e0180325070b60a001d401325205850a060300e0701035501400d500d58030910001510644506114461410081580802c10141000c0e10b00d45031058440d1800c0001d480b400300c1d1404000c51030010340814070a160456542030504030b411070b000c880190a61101d0f400166000a413500300781240075568051111460107034200d50886400103002e900c1da01c06c0781c0c20181d1584421035800b40140643c100081d000d10701288054000d00ca40300255104060445400040901940082e201d0840c0d409500300141c0c3c860180038083c500c40d40300c2107444214004098048400000e0041d10300c1810f0040208401400f0b0b003004685070120b61664030061142030039410440c43c862403c0c0c00c140001604940d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 835340548 1250 835339298 835339327
    0xd0501050c030a0c020102070b01050904020103060e01090c031b09120c080109031d0a0602030d15080105090c010206010f0e041e05060906160206011203050f1306080f1f150e0402 78
    0xc50f0f24445000c0c0700c0c0e8901e10b40120300701e12500c00e0060421300e880005002c50704241e8903995100c2d1043c100081c520381c4403140100c070040c09a0040080f5900c0d00001080309032b00d4010040c0d4170040f09403100054801850103481515030b4000c000c691440e030300c2c2c0c903424050004403800081030484000c100a0340c260500500c00075500030782c1d140c81c2a0188442d40340d030602c0051300003281c01c1c1380c0c00703942002c410b0a2a08080c152646024009900300d0b40f000c11568400e100d041c2c09226200300411086c41703544c0002e410070760160700041d46843d01c1c4404120b01c0039100350b040c1e84241d01c481c40000700c60408001e0101d00405030300203040b03403052000700154841c1c0040c0701800340100e102103c0554560590407a40c8840034091002c0e50703040004840300280c060400b41122901c0700135054288140c4a8046258141030b51000002484ea02c007404400145c084055801c0f5003d8001c02c91000d081e07003402c12002000e4420392044002040090031180d10a020204000400a109540e1031a01c2c211851 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 835341798 1250 835340548 835340551
    0x190203040302040b0f0a05091305011b02070602030a0912030507150e0609030f0f0c12070c090b1e011206180b030d0309020901150903080406050c01050a0b01050405060304020d0501050c03 82
    0xe025030f01d003d4110742181317820300354170340c41c55070003401e00c540981400140111210040d05101a2030148104280021000c1c028100762f8803e181c2c07403000140c1c0c0d103880241380a00da41d01240a54004000d04070415601c0100d42098880c10303594008685c25a14084500348030340103018000c00e40c0285490001d081c5500009a2442c0000c2201c3c1140c444000a0361030b44107000c00e161800c03600300040040146618094003d916501c0103a0300c003290f603007440018580c000e83d011184075011040900ca551003c0c45284203031030042d00c8404d04084045580d00b6540a03501825040c0290442100400f6806401c120040c20b02d03008541c0d07440d500100088041d296100c0828400c0c0130794881145668840e00c92990101c3d002894266540d203000035000d000b12035155640200a8003480100129a08000030001844560384e17407a5600b02a4000c2402c41e00301805081c4858104080b400c3e80340c2e07122042d1415100c00720703902a030b00c1c2c8541c80001c0148400b40340c0207000d9420701d410040748031050b80146 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 835343048 1250 835341798 835341803
    0x60d02013c120b010f020318030102071a100816030b31050111392b17012601090308100e0903070f0302190501230411010e01051902030403 61
    0x3c0c0720355207641005403000e402030051400141d10500490001c210001d805006e90203014000520300406038692080c42410041603011180c940400d0100002a040750380300103104203006803006a6110b82260056009440080c0140e5a440c0101700c0a150401c611a580c0400042452181f805030307111000003000500e0a49007540f802d14400707031515141d02100c4000385ca4004500144031103415480030025059400280c41c400034643c030000c024100305003c2c048000c47d100f42c1c102e070080b030b80300150300c425401d42404010b600390701d203081c1c0302c840011241540c034841684a021001e4102600c00014105184180740d070030101c2c182c06054025000e94001c0c865504c40070b40b0584c44007513001c464281a15000802e6100300800c1e00810f00d80c118000030707a0f00c02e106a43c1e0350341d180c41d21025840311048040d41c241e5540d005202c44603840c2e8210b06d0041042815802d00c41c40c080d00d802c2c0c005400c02c40823034148000064120307010380c8110110781140079194600444001c542500070769a400a0008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 835344298 1250 835343048 835343051
    0x10020c04141b030c04033e0a0b07031d03010e031605210d0515040515280e0912070503030108060105010e090a090201030f060e040605060d02013c12 65
    0x4440d1000c82d10046030302c120011102e4916040c03a684d14075400c8092a6640c0c03003908240c041000c2e401059110b079200b00c10b00e28000304002408a0100b050301c0e1303081d070b0000310103002c02c20900300000d82241507210154582d0b00c642604e91102c002007405401e850120015074000060b2805080824a070000881070080d8100e443303403040d880301b4010304407500b00031071020041440180078a1400c2e80255038040650280491a80c7c0c100d4042016100c0968540c803002800d4201c6190501700b1014102c90b0070700c100c503c0d84a01ca00c690b0b0300e55004503a40500031400d0f10b0b01000620880d020446031400c003401c422440d42c0c4940074100262a50070030300640b100c5010340e4000042d19031088051071200c14000b86070044039180c20320424000c0403c108100c1c141500d5585d190794882d001c4c03083d4001410702d054001c040d45800c0c54004215400141481c0c4110215a0444050303640300a03061001034400000b0b80c0b049184228908207030000240c4651180040100100160b81c80340c1d03c0341801d1784442c2d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 835345548 1250 835344298 835344331
    0x30b0a0b010e0121113019020906041a0406090510080a0b01090906060c0b0f090303010b2104060c23030721090b010501110a08030610020c0414 63
    0x450b15050300304907031800610003071040f1a00b88001a202c84200400b202c00240c04034001d4025150758010000e5000b0803628030803606603915030105c00000d912602da4049031a032900c00e241c404100c0800803030011302030780401c0e581c0181d00c403201207c010b409030310441c0c0e070000380007107954603d94014002c070b00016503030340800a0349051450711102000304940700c40c01d0b40d0790b44080d008010040002c0d2141000440e030300020700780219101e040d0140c00140e640d42c807410124103282811440250483c0d050300540e4040240414012050307a05480b20781c110595035014021083c402d46c00b0308504c5524171510103040c40100403055010780411606519840d0003075a031000501203d481c000001c114a2500301300045c1032038420107102071510030101502160041c02c05c003007012074000c4c01d01100c808a801005000300e40c0c00ca14982d102c142c4050003029066080e681d10350580c0005000b640c0900d04840e40009903e009200328110b43c0005002000450107802811801c060241c4814448683c0032a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 835346798 1250 835345548 835345571
    0x40c030c06021f0b1f08150f0d0609050a081903060608090c0111030714070602010b1002030f091c0b060f0103090f020907051201060f0f0903150902030c0604030b0a 72
    0x40d0f44420b09607840814520304002c400c42005090705114460b40400d0100e001905041100d00f52803070f401155807580441d14216001c511660042c1ca0b100b4481c18014050101035070b180542410348541c03000010641c608a4a000d0b441d0184c1d8900007400c022010405201d06403805038210701240e903d907818030055aa0368002e4907804070a41d6014002d41194030443c04035401600c9084803c905082203070f242c180541c654028540c01e2495920b00c640000c5010004298240100303c0403040864031121184507407200a03503280304000c082400900c022800340c0c030585c2c40d945041da00d41c4142c580010100344501d0700c8841c1d464100da00601c104284e402403c0700c0c0d4464464058026404050036511800b20340070009175401c01040c020030802c0400c480305000c00203940b50b034024910390311a0860a9480704029000030380c140030300010070036070f010b08002040b8040030b03404006d9031140001400c04032a0001c2800e04440c12105c0790807000015000042100109090784500800b80d000c0180c084e05c1d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 835348048 1250 835346798 835346803
    0x1110301060f08010f050f1e030109150606090f090c0c0c0815070509100522080f0601050301020f04090513050d050403020a0f03210201060e0412031508030316020703020306040c030c0602 82
    0x6d00800d60441c860380024070302802d003509004418000300c00800048650f2000003425a15005011a4407013151610103080b441035007d1403016281e02d041c0700c02c1c20307400c2031140000c00c0c0f142d100fa881d0107034503403090995103800340c0700c840d0503250000030040b5010744401c0500d6640c1da0348102d080c52603410b81c0004240c1c500c128195240341c1d20007271810840d0908007070100c40603005004501d40703040d8541040107000301d5204409000f4006000078140324000d0b080c1707007414008164056400380e401008038842090100013207405840d41508005003e40300c5c3c500758008030002c454000e00300c0c8521481071200c0c90b0844050400c4a100311100c13024144c990780400e8040000d440000d10024051044500088004560342e002c880d09100000305c0307507a10050206c400340184c4050b111110100b8828980703984c540641c0c040419001c80c5244a0b07440c21001540c0e0b44001044101c4801421802040703591003403010000039038009086030440d00709410140e403d0040da1004940c554a032540001e07000d0f002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 835349298 1250 835348048 835348079
    0x6101b0f14071a0a1205040b0f16080109321902120a020f0c100b0909010905070b22090c02010b031c030b0a05040c0c03032f0c01110301060f0801 64
    0x16030f002000811021002442c0c104080b9001444850b105021540d41c0e10303c1142e2107507000303815180341810b11184603140fa0601901c5204800320fa03205044500e03820002c16030454000712000500b007400c1c50000c0d00c000c0170982c0031a444011a000c0c22940e000c00d90354243c080c1002c1d0509442402c002e03000e00c4102c1c8224a40d03c000d80a05100117686800b00354045c02b4000203100d411444d00744580c0795641454040c0d210411620b0382e6200c01c038080d00388800e2540d40310140c00020003a441081d1282e6590b10301604c10502041d0f000120843c0309000c0090f080045640014540c01e41b03529038450030050850301070034400641c60030125411a20f0005158400713480248042218148184021030103031000710505504070000301000201074480344500360600300c4e01d13a90260394a00910300102a1001548248803003032600000351000c0900c8509071180c07215075101a9524803292105c0b501507c6400f004040c00700010000154840c0c004d11010500c007080e41c0c410003241c0c0ca480d40003050030310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 835350548 1250 835349298 835349309
    0x70305060a0602060f090109020a0f0303031103060f040b03010e010c0903170a1e0c15020306090a0b060f070c12030c050105100b0d0c03240f1d06101b0f1407 69
    0x90b0f01090403071031040c110b181c1102e51b010020035002800d4000c80c0310903d80e41c2c01041c4c40307603040c00304005142c1e1610854030708000b241c40c25440c60074040c0c0040e44d00780840342004c0c40740d42d442200c020f25a03001d502c040040040c43d8000e1001c001d203900c0c094001c0074144402c0c2e8804031030514000c01199560708943c00c02245841e060020f003c0305c0c070b44200501190114509001d0702c90384000108060103400c501c40d4013900300160b681d01d4a60b081c080e40010141405210728100050015165946815152030300000f0705266203640c5c85040c9620b5218a9500049034200e10b203c1400034140d01949240c0250b014030028045500c42022580c0000002c0c41482c80a54060011150055140e0482c80070070f59103103404a000c44965a80c028030194001031040d01c640c282800300034441e2001e81c810b0050001c20418007244190010b40c012f00c000c000c05442c41180c00c004140344030760140a04a590400300802c00c08441424a03044204013803441d030580c0d1901203400c0b08000003d0025148050b80c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 835351798 1250 835350548 835350553
    0x30a1410050114241e18040603030f050f04050d060204051c020a03080c0f060901150602010614010c2904030818152703210426040503030c06070305060a0602 69
    0x44c0421300f00441050003002581ca065820050b144c2000130401049411511840c00c0e95900c4100b4548070001c0850080d0307140c019410403108001107504001c5c1944211868100300355904040010080c551050341c01055005124284080a0141a60181003917520546090080c0c1500c1240e1000148007000700a41c00300c0f4003041800090082c3c8040c1040c007091b0400c84065183d0140d00300e060110880f280142c42c0c1d0b6605842c240341e4000c01c50440201982d0008104e02818040340c0c036101944080818140041d0703005000c2048001828000140c0003034000c00e021816640003524414003c0c1d405800080442010440300c51348007001d01010000d400040a40d64171002a040c00550014100d901c40c0b21851141d00211a00d4101c00040407603d0024650321116045440c640c2010401c0318003003064040d08000005500c0100c0c0c00d202505080c00000c0400401c8807290313184500d07000740f03825000c0815003140003800003a03460700a803283c1d20b0030700c0345654441c00e0100c1840f203403040700010f9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 835353048 1250 835351798 835351819
    0x30c0909111206070e151204020102060601231e040f241706033408070f0909020a031a0f060916030506030a05151e24030a1410050114 59
    0x11401200c803549004000f07041000d0320703444035100e004640c02a4091f800404240c800b000308560b814443c10b54400e1090820480c061919904204145c8004a684450709400542000d0b200303840c1900010b120303030500e40d49030307075645817903402003003200b113116000d081c07000d808100c4644000055480c81c0c41001c2c0e6101d044540e050b040c10303280e08034003500c00c603094000d20007807041300d040b4034074024910f544440829102d40340c400303040c3c40d038007140307500550958002c141c041c443d2098440d01e260031191039000c08212640180009409001558002000d800e04c14a140d40c1d41884114524850b20040c0c441c80c020b40d85a6060006c030540071940b0300c0842c4480301628030507901907448a5000b1002070201d464091075a91100d10300505118034594051072841001881c1400151130308036041c50249070443c4e41485002c40840d03840715038070071040c00414650040c0d6510104010181c880e00007525a481c11014113a5589903003440b0100b500003030030040081010450501e0010031500050603032101c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 835354298 1250 835353048 835353061
    0x303070305030c130b131403010b03121b0327040c02100213080706080f0709030308060904060b0415140319021c0f061406030d02060c0a0207030c0909111206 69
    0x4544c402c0b0032100c9105103107031002c2419440300014040982c042e09410300000d0401404101101010181074801c0c0e0601291000302d84000c100e11140c10100610b260701c40d0403000c480e41d070420000d03881ca0103920010800d43c40c0c16800d8800c83d024010940c103200c108804280c14481902d41d03500e0300b000582c0c0890540445007100d80e0060a1070501c51340f040c04c04603102e800c1c2605006050340300c0d03c0090340010901c0342d51108204000d8120000f410007e060b580342d960042c00860004003d144642001320025050002d150030580480034020010444805440c925540d42c011314040c04491b0540300d50300403014200010b00d003680c000b04d00555240c5000540c20007079025100f44070f038005074200c17a5201380003036428911009202e101d044046504200d034003070383c007988100400c054440c0e0b12082c05411030f01d0b00880c00d15000380c450741e0103c1c4c7d10310707954405a14200711544014103101c800d0400150a00c0503a000c1c0940c2845503a04105480f0b11400f0003201900700c5070480419042540440c68 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 835355548 1250 835354298 835354321
    0x1170702070b13050a090203070809031c020d0603050d1809060e0c18180f06010318121e020f10050903120a1401180c0503090a060504080d15080c030307030503 70
    0x30401c42183c065a5241e44803408103c0380881a4084183c264021080c092901e80010316a40c0c8581448011810000d2202c0d00c030074070100315600072892581c000380102d44d1344240c2d040080034581180448404004402e00144009038410700044071101da04004110704015020382c6044440f0380851078100d440b0686032111643c4000d400c5503000140000d41c08480e214281e20111200040132608811710f0810703507421079404000d01c418105883d06603035441041061602800c2280c0014400102455842050701e00034681030031a44440d808190041403154001285406c509180081d02c00e01215a0107041c21b4507010f0780d0105e5603410030300c03903c0e030503034003031085654001003201002c54400000449240000d1080c1c2120003020300342c01c4040500e940e5130041108012061404038510300c0c02c0b80c071f2036440c0c46035540c005000e80c0c2c9403000301e424413042300c0640758501c1100200700310045d07011f1018481c8031070078412040b00d030092003a072150034540442900c0110790140c03111442c59035012820359 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 835356798 1250 835355548 835355557
    0x516080904090c120611070201051b0a08160204181208070504090501030f110d1707030e040e0606010815060a08180d0306060905040204030f0f03111005010501170702070b 75
    0x281c0199842c0a8540880c0f01c99100100620b1401c2000900314424109030080d2071380d00f000540950000c0041c41c0040c0d030f0000c01c45484103940041d4080540d10304044038101001c4440c00380ca18040840d6115130040204035603d92544212001c0102001080600306204000400540103000c1088552036050182e400c117944141c0915110340340645503000d40040b00c000b0f0300251402a0344814550400c00e08150f50030031100c00b00c030303402da90140b655980c2030030240a41c1a00500ca50104840b0304050168908000b0b98200500034040c4900d030307285003643d0b920101c86182c000b5405601044508440b2a050f44181e48090007c82c0741280341d04c000e64800a01902c51440d41d982051141c0c010300045c00424640c003904d690106505141c820003c0070106690000f03032150b07204010800002d02d080005101c03580c2d2211004010922604050b41c80f15207070311002459000701402d10001504542c4000d05a460036282c2070a80890400c0706840c0100403140000564801c03041440179102440181 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 835358048 1250 835356798 835356817
    0xc03010909020a12030207050109061e0315030816020907090303081f17011e0b030a12022506120903170c0405040e1005010504091218050d0f05010c051608 68
    0x4078a507580300c04c2600091441c11068005030440c0344140001d6030301c00d51071401007c40f0310f0200310000301c6240c1418610030f03105040081c907907030340d542c0c003035a1400300b02c4c0c0801150000c05440d1103202e4507e14200340a00044128803940040c030000303c0381401510003c003540c0e01681c03045500d607601090500c142284020340701442440100001b0038402ca441c0f10501d2101750380001c150f02014a0310790b20000c3c001c41c00108624241010b052013914002042943c031a004815400c10040c284801c0c0d082090300784802e220201070b034203000040d071850a107801c01c480e51995640b185861000c02e0400f1a0380c5002c000740040d85480d07810760719410030032072030303810000440c100740c60196644000b8084aa550490a02580045c0e03400c2848c0c0c1c2140c825640140010344091001c0f517802d5503150003c20445580c80c0c140075403c4490780c0c0c0c4480c1c0c0c1c2101e030050700e409026443c800200e13040100001c4030904085030f09600f08503c00040c0c610801c00c5d40c1c84101d20050f1902498003540d501203058200d003c40c3c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 835359298 1250 835358048 835358059
    0x9090b041b03121e03060b12100b0a050a020705010c08120613020307030605030f0606150307110d0809011d030f0c0c04060609081203070e0d23011e050c0301090902 72
    0x2c008a21404403c0200c203010f0303203840e01140784010b000001d12100d00010024075103411000c20402c1903e000f103942048090a0203000755482401040c1c002c2c0d00c0f904041d13900c81300400c0c2000070a0708603004024503101a000c80380010755410044031131007000385000b40070440900400e48543c2c2d081d00816080039004103002008244100c208080742c000301d50b404002a101ca104200d5400d050081041c070105880107810146010404540700c0f030621142800705550010004080e031f481154407140060035681030301c1816880350300003841035400740d070138034025441c210968a03448803600c0410000d0107658044d505200510350140895085241c1c200303441d0084040b0001c40b07990318131a402c050021a00c900f2621030404800524101c02c500030390403498010400d0112260b0400307200e401150003101c1d812001003252a003940c00106290501c02d210702c0740c0948075883e580c19007040d084800c01d1000c17140d8a1041c000800c0503943c0950b8500c000c1c490030030040c480b01c01290091440103001615 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 835360548 1250 835359298 835359353
    0x51e04020d051018020c030a05072102150106081e0601091806030c08121210090c0905030d05040608010e0c07120804020414060907110f030a0806040609090b04 70
    0x401e00c055503421248200ca0482c088030a0254200740300c003000c6420015103045040c04402220556a4414000071200340700d80422030710100500c41c82c00c80601e1a815061125040c0310b040043d50b142c82c1030f8104520410200000b00300c4a11400e02c0324402d102d0001c5200503201c1907051940301c941d01815460405c120180003140c0b0341040f60380c0003c455807103840005d210340b0354206803010349602d0300489415005030314145412a19030003076901482601102843c140c1303403851a5020b60005900240e1520300b004c0c903d021241d00704c0740c200c0480c0e8095040d2029014200421101841a40a8640030030503c00c010700c0320100c1021001d920070100e651301b500e806200c5d21001c44041a403104500010507030010802141064010107c4c80520740d0300c8083c00381070900002c0c8030a0002011101000f07400402c14a2001d410090281742001840649a980860b0640101150300c219400c2e0300542c1886000104441030744550799206410007144040c0ba00c03140d59410011490604c4424008407049 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 835361798 1250 835360548 835360567
    0x40b04050708010e0c040608010506010903061512111008010510080c04030c0e1501050403122102032703040303080105130f182306070e04020c060903030702070f051e0402 75
    0x8600d12802c0301c01c0e00140320510720313001040f0981f001034000b41003a90414003402803598005072080e0030b680e0701507000314081e1103005508100b51082e6100c58025010122881c0c203101000744814400d000c250380c1000700107015442912101400e200d0a5000311400302074202d000c0c801e9419a0700f041104d500c10346400c0d500e489117400541e03140c11900c00702c0150401e0140200114005002c00d40080c28070030709140c999203407550b1190701854071700240043c14001001c0c0f0100140d01c601a11071200c01192a4105840303000e942c0b141c10a03014880300205081d550003528000b00361811258944d980070350aa003090144884844c00441040030281c9408160391024402e008101c01c081d1980900d82552500c2d05001000b60005000c1c20f035034100300741c0310700c1d4042404550160700140a0400e82040b4810b480800d0081c440c141c01c51100d4081d03007050200420020001318001c1c0c50b02c0d401c840c0340380e0315180355080070400da118482e400003058015240044c1c0300c0380c08a00201009000604000b1841c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 835363048 1250 835361798 835361801
    0xa0902190303031b0206132904060f140411010e19080d08060f03150c1c0204080f16050f0414090109020310020c0c040f0b15090103051509040b0405070801 68
    0xd0700100e0101e074030750302d9291000140c980302070383d0200c951004040d14284454070b5061041d0040018100d01080d640540003018400c6800030701030704200160002e842c0c00e080000c01403444003149200e0380d040c002c600d1820040c64810700d000d26000482241400d243c0d00040d296420070101e4907812584450200007454540d164440c001c01550014010840740c4000040800000520b0203101c0c600c1a1001c4209460005281206915100107196582c2b81c82c00720650780e0080411001d000c65002203441c265060a4000d001181c89c52011034a070459492042611607554580400305c0f0703842c6d4031b0100400e2501c00c0041010181c05000011107810545121340038480c04c82e00440705a4680c1c5643c0d045003001c020804508410407000c500b44003d078542503450b440e425942d688540d0300c0b5018000c001d0038960001030356401c000d204030340591200071281215001008601e0109140c000010079981c41c0d1884540354140040002c100380da1140c1e02c0c10079410000e4030035170300d91042600204c1c40d100709 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 835364298 1250 835363048 835363099
    0x40201020a021002030702010305061503070e0103020408121806040503030d110906030a0b030d030e0d08090102090d0308010e0609070f11070e090703020301051f0302100c08030c0c100b06030a0902 86
    0x15135015564403a030a00003d801c2d203d000d4416030050110b09001083e12190300b081c0c94004d60a40342040c9012030440049000c2d01031600b00980c0c600402c4151a02c060407a00184a50540400702618005110042100b103000760700c181c80d0141c20400500745034004030f43c00b0210b244c203629100c13410701d2a100301007405600704a0b030b40124584e072049101c44520b01000107803191606807509220041d14046000c2e141c0c1c1c915081c0c401400b00f4000072580e680d400f0740680e541046c0c060034a8080008909000700440d0003881860a400c3c0c00c80c0105415003080d0040a10529094032010f40c000c0c00b864003203071411081140400030b800f03540d00110702010b900c060140944181c1e4001d0410909500405085443c040c0580d00c0d003220308002e01c82e601c50442c0500341180d8048800d0030800c5410305054800d030811880091104c9400000c0281d00c0c003240014101c91a584801c40718442e161880c200300721200d41910030b03480035044c070010304002ca454001480451019000f290708a240740103031b1707001081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 835365548 1250 835364298 835364329
    0xc040f09050a0f090c050118180203190b09011406070b040b07030b041a0d0311060123100c021c051203040311121617130806060126040201020a02 64
    0x21104180a0301102d18002c0f41c0f0302d60303c40501004804820b07940c403450500c85100c0d031410f01584140d0b4481407561804480d0007090b403841d031510703c000d051200350000c0d48202c80181540c295000201207000e09131040c0c0030301940140c0b0541c20350b420041e0084030b5503101e09404d81d21610404c5a0700004440d661510302907480b4011811850074049005010780b0b80340b2180c580118501106901002c5a04e42140c10b040300c02c0c1e8040082a40c981070844141e140d07440c040d8060710590000098407061078a8455044441d403421a6840a1903001c019903201d01407400c03c00a044030321014054a45884211083c1c94814500515403056035505810a2070406499001d007001100700401e05801c91380c24540c800a0b44080d00624603540c1d80c1614501908504030f2614941c8851030040101c4c00302d11024401008141d581c803800040c00190b01d10305207010b2551140162400b241c0b06501401d030001c041c0d48040543c070101c0d805265902d642d1240103106034114840c0183e11405a2a407812002c2c00c0203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 835366798 1250 835365548 835365551
    0x70906090605180d0303060f1e090b041107030206091009080a080619290a0c060e0102120c090a0603110a031e020a180f061b0501062117210c040f09 65
    0x42c40c2580748e10500e01c15600c03034620203183c60000c401c10f03040204280181c80e8251000501c82000b035000c100100041407402c12a500c0000c0d5400c1815000955588192000320884151010200013141510b0f10303014001c00800c001d005600174203003d4403200c0c2c1c5c400c00c094019100c40807444103204a4100030b07884603008403400385400f00e01100707a100c01041115864250340c0342c00c14030a0001c09042480d807000c0c2c0150b40d102010424a0001c0d0112020601442580b03102e501b0901d00c00076055201401c810301c10219a5030014109000b4011403840804c151a52410203800c011f040e0054403910b02e02c50361040c94555407044004241c406801240104e03507418030300f055141044841603403a80c01c074411038254000304020450b80109002d00108907840941541c121a01e44180500300c640c010310541c119030440081104140d000c1487c159001f5403444802c90080e128001ca03a2041a441a100ca10901039542c0c1c15090a40c034150069990010903141c1036450090030b0300304009411414400d17 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 835368048 1250 835366798 835366811
    0xe120a0f0801050406080d080a02160c090b03061510020f010606020102040510110303130f0b0a05091e1e070f0914061e0915040213050405070906090605180d0303 71
    0xd80e01c2200d6a026001c01e032001c0204034100030140d942c925403500b81d18204071140300000d89844164040e00c2d100b0b41200d4680364007540c0be180c0903072244000c0c000c41f5102494601c4246542c41d001603094000d03a5186c4080b208400c440b01030004041a449205065219410b55554084824400c5100800040d800161510305040c100001c4080869003903040018000490010420100c1100d0300002e02e500e6001589c907a40c40e040a241000180c040d00c0143c45000708410340c500c68200c079203d801c40f482070303504c80560202051017100e03031080c05002980c4948110a0051903810030f691980c1c0c020001c0303401141da121400b01b003d0400d0703002600f44940b10b21481c207680380030642c800e81101081301c00519950070001404a01c481c814592445442100301295180c03c60300300b02c1603608000307081555205003103d81207a408416101d0503004600d0300000403101885111588103803649a512a911f0030314103202219107400c01d5001a100802c04a414001ca0743d40910801c0e94078400c1e03c1c041881c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 835369298 1250 835368048 835368077
    0x33106240e090c09040308010e060d02191a0408030711010306050d030c031e02032b09060504021302030606030f100f03050d0f0509012102090904050a0b09030f0a030e120a 75
    0xb0040c3c80028240241d1070203092000003030b00704e1600750640c2c00d803142e1001255921030005900950704034000e9000862800c0c5000d118000c0260329040d0340c3d050f414011191801307040e500071846a8800c0c0303a100e800600c100400680000c4124462400525000c2070098955000070502c5036100c5013140480c0c00310704034204040d04110812200c08022240914000030b100000e500e9105561060034200b0103003005000d00c03a03981109684a41c1100d508200c6056549040e50051800366000e034415070b080703580c08035401a14022688543c00140c00c1c2421a12607501c0140503401c0a00780c83d541d0024000007041d20005015180001c5000788000c00c1c558080d25070140102d030b82401b40b682009000c100004c0c0a90f004a4154403003003203010180f000b080b451840c80001e014000310302d5800403104003030200380000064941c4007940504c10200c040c5d05d80942143d40c038030801d69003607410303402809000034083c0650b2103446020009001d4032007110311a0802071141d8052580d04010070003c0c1c142114 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 835370548 1250 835369298 835369303
    0x70908010507090f06080916090608010b030a0c051203071a060f0a060503180f01230708070912060f09082d0409020a05040305070308033106240e09 65
    0x200001c40e801d08040860618074030381011301c1a4042d03c010300c102c80f8080740d60010304104107007822074582c83c04105a40c40b0010000901268401e40c4440d6090000040c102c1c40c01048009415a0281070640c01074542010f0281c42c0c04a8070010f10180018018040400c0017071900444804464415001ea0700c1c0003802c004000b80d960700814050000014203008403500070301100d80160b443c20404051002d1800c0c0e65260034200402c06045508100181c2080e28030381b40c030030780c02e01c80300c1001103039030382d94400b044071008811510740c3c0000d00888020040c0381e0062030510241406814046800501140d40c4801ea4441701c104980c000b100090100501c5480d03040954160700c035030107894150f03510030300180d1240203600561114aa001848914081c0200c00722401140d000c0165400d20390b80f03080112943c1c104889040c43d500300e00c0341c1d040c9846403030b440f142000b01c1d03903600d41c03420310025072143c1c80100360300001203c00400380141c0700c002038541001c1d8002406c1d1890344a58600c2e10420050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 835371798 1250 835370548 835370551
    0x801060e0f040b06040e01020706182105030a0f090f14010507051e030901151d060907020a12210b12030a0516051207080d06050102030a0509130209090709080105 71
    0xc262030312007001d000c0021901c1160741d8014004840c003254040b05100b0050080c482c3c81c0d00100035501e00400000c020403c0c900c00e00c41540556800115103112003001d00d2031110394004400003960800c00a03880c159154400300301e600100740300042d461580e6888203845003a0140544841c540040106192842402043d46c044000c0c0760090910b001c1000342841080203a08001683c0004000900661340951003900301800c82c03440300c400140c1c0c4002055045400380c0365500341030801400035240e0b0501031140c9014065030b40c024a17856915071180286500220b035102c00b0040b06907070302100d40e9003590080843c0090708800103169000e030b50401c20070301044005240e0980042c403e0300195504542910102e840c10f0302c64900d64410b924005d820444a44e0242d0740701200800d100080c40b041c0406810300c103119035400c2001c540c0719001642d480c000c1c1010301000400401611202d410408034001c100e1348040c10150806038540e0008003017082c1100d921000510350f100410440c0e07400d01650307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 835373048 1250 835371798 835371811
    0x20a02011505190b07021201090305031e040b040206031509011509140121060801110a021b090c090406090c0302031b1306110a051e070902120609090a08040801060e 72
    0x50840b00c2c0f64a0424100d80c03000c3c442c0003050384020554a055468620b07541c80141440f1000700075440031031034040e109400a40d00b8000351181e040b04a5080d0044211341400b5540100c2401031560319039082003c1a44020094443c201168007500c0c6184c076a150b0013800380040185281c001041450014410b01c410382c00300344055800c400401d010703608400d0303101d0121035920249104541741c0f01850080c0c112640320130704561074440a4050226410064005c031180d5a0a584005c0d1030b0880c4000c040103a00a0640c1c400407c0c1c0210703202044060007000500c201801c04120943c6d280041800c03205035a5007000866000010443c0c2940d4a2441c0503810501c149068100751041406240d541c406010300c01c2480024000060a036004228200782c00781c0c80070407940380c81c0e1440307041c070850303500200028502d1240000102c3c1c800748030300035905040541d580311000da564101c2048440310000d00103000c1070003127820740004224030f1002000984920400030800e5458090032080c40c00d40280071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 835374298 1250 835373048 835373059
    0x2041b18050607030c020102162c0610030c0309050307121803030c0210350903120f071107060e0f040e0a15062c0907031a07050d020a02011505 63
    0x140107a584400994294941524129045c0c800d607200613850043c035a00700120b040300e551800200c5010648245030141d0070038101905540b41007184600511069400716808020300202950b054441c0c0c1c407800c002e0f0401d260210302c0b42a030381c440c142103900200094690320702100e088084650400e1140341d400c24040311441c003981c550f88009008000e4801d00a01c50400d403070b808289103100e105d100300c81340e1a03d503030700d19034501c0c84000c1d840d020307603080d542490f080c45840003a41d00c1801006846002c1c88260b01419680e48000b2040b124200041801007440032408440c81005400c00105024000e6901c0d40382004200204001c016505000003604c03c505009500349144008200c071005590b01c41408000c8115000344880038101e10382110800c0c6080d1000c0c11001c40000041c81794514807110384403019110300498580318080760002074100c0103000c40302c404110790000d070148c5c44400b42c50a581002003107540101641d02407122030f40140e458000c854480d14440044600806080341c2c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 835375548 1250 835374298 835374347
    0x141b0a0c0e042103021e090a060302030c1e0c06130c080c0d030e030a060e0c13060806220b070903020f09010f1403030405030307120809030a05090f01020a02041b 71
    0x440d04400e00d043c82181e181012403000c04080365000f40c040d10421070301c0c1d480030252500300c0043c0094a4000c0000980304515000c000207a040c000d1007228000c600e1007030190310703002072040d008165034994454004a014204100c1c0e0320140c06211580c000c1007000c042c50148035440c2020018a490364001050a41000003c640309644080c090340e803040e41410202c100e0089100041c0c101051950040c0956007051000c484608000c24a41d0030b203d0111451003402010a0700002200c0c03060191310b00b00d80c071400204d29103941c1c00c40b2742c54450651508202d803120903990784205005003983c44001060302d2840a000314540801150004903095070300301c885600d404a0804015220b115041c400501000d0034080c6840c1801107401410300901102c0c0d894807640b500c03240c130800c4e04040f100000c45140c042111203c022040b030700c0e000c900b0340da018109045001080102c00e001d0a481d419803140c5004000161501d006414100b060440700c428aa00d101c3c0c4040c04801130840000954040c400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 835376798 1250 835375548 835375553
    0x30609030c100b1f0503090d08040503041e17010f060909030906140c0601260a0f03051b0d032009031902060403050f0705030106060509010e01141b0a0c0e04 69
    0x180d00e01c8080c044520106403c00518046030260a004140090320103009180c1c21806800000460040c180341084440301d03681d88030201d510b0081560b00403c2e5030402c200800c8118020100c5281184065009524241d0b4984540041c0317071148030051000d0351903c010320b421030700910840000705600207091001035110f940040a00801d07005a606003c4080c280140c04403000c01034840c9544480100c600d00e5071200a050080480400e000b4100c0401d18403034212003501007505102107922100092810b4640e40c0d0aa07101d42001d03c080007104050b607110680000e01304403210200c12282c0300000c000e8002035006131000c41500b20b01d45500d60800112060340c8001030007a816440c002c0318510784000c07078800501c0600c9181d0000d4031511172580982641e00b008151030080394400c0780204040c565803d420b45d0507001c9c0201580c0454240030780b100c3c455000700f45042d28031442c1a940d520707000840e54190078108042510044560000103000c0c10444005a03005c00761940080c0342c2011b00d49075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 835378048 1250 835376798 835376803
    0x20103110306090f0417160b0c04150f02010f090b04020103050c04080c04020d3c060e0f10030203070f030312090507060f020a02030a12120507050f0f1306080105030609030c 76
    0x35100c20b00d50901c1c1c0c00082c080c0280f08250140300240c000303109580c0c88004604800584038000700380d4112340c895002c81e44006408003150115402100c0321000030300802c10030b4034035055800c0d0840c155502c8a28ac80c0007071384c452060105141c46040c1c40009410103000041c1181c0e40100703258002c2600300000d10004900041c0034090000440b40583d8841801040202901902d0307110141d2400405040b0788683c0d485640e03414801d00100003036051041400d428007951104d10a079049001900040780b400001c03080c007140d20041000003554103550740c0c0d001c40e1610140340d210041e980840d20f070500070164411072032070303041c1c034540b90a00407840340b600e510713031156451b101d080d042c00361211001c10443e00a02045e0b52882d00102a11081986401e059000b00102d082580001c0d046000381d40c590340c1c141c4075090149102d9940c55040030702e280d095803007991120050780c4041d6400d2002c4a20080035115800107801c0c56556200e41c3d525110616150803005032250b1b00c40d03007061045000d0300200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 835379298 1250 835378048 835378051
    0x3190c0804150207030e09010b09120a0201231209010b010f091a090d12020619151e170106050102160b0f090604080105240f0310020a020c031902010311030609 70
    0x41840103035284c0c21890306581c60300101101d980c010a200000090104074603004d0b1272801c20a0f191030f0702c540c150755602500c070005008003d001c00e0128901c0180b6a410807508540c00811030482840c08100c1c0219000c0d911046a0070009030303450b42650310582d40e10403104e9500e4041c1d41441132840b400d090b03a079801443e031550898443c035004141043c480d81c4000715030090355088846400c6491010030001e455004c00c9604174500312160701c40f50100c11885c8500020144a48000b8407035500b0540120441803027170000384203002d594040402d01e00e0802000500e030b62280000010805e14100000e801d112000024950007944848100715440c800340032142103030460581140d44816502c0050070a02554101c04050761030074040080a01440340300b001100034103166801c06a00107010840b02540317804500e40c25030041d48000b1000c0000b900544060101c4c1e00541e554000c00c000403034544560721000001200040500b441956010311500401e984005516840d501e058404035803107090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 835380548 1250 835379298 835379333
    0xf070b0f0f0702150301090c1d090720060612060103031704020604150806091f121e08040f0602030f0316020c03190b061e09071403190c0804 62
    0x20000c1c000100601c510119285035a000302900d00d030079911400c1c0c204c00c0e0004d0003207a40e120b161009403100b003806298002c0740c246603811101c00c03410f04402400794841d000f5004009100c081c41c21501d4891040c841d19251a045500411044c42c3c41820400723070010390150102c080d00180700503c0401d0340103403415400203c141c81d44604da240c507c0400d00610542d84031404811851485004060740500000d010391700840340341800d619110035000d9081d11703660f0491440400314504101f51203c035004400144d01404050400d07541c10030901200300f0710300300111000640020180314800020b00c041010302201d100644c1071104003581e641d503610010b001c0070004a194410242120f1081080340705003480034060f02c0204604201407920510703011b4044a51502d03c00c00505c1030f00b44980340d10385001d500c01500b0600704a8a052011001d409070826003046145030f000805d0460000c0203500445c101080744c0074400400c82c0e000c0c12103608100c494204040c5809000c003040452108042c02078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 835381798 1250 835380548 835380577
    0xe0705060c19051204030308010e150915011806050406021002041a03041b0f21050a030806060708070317010503060412030e030c010e030409050f1905060a03061401080f070b 76
    0x60707050904918018413600e4442084500160201c100355014002e10304032000c21044950f41e4607040c1c1c0462882da021401c4903040300e012800501c200740c281d041c2404001c4103041001e0381c001005002c0000c0903440c1c000b0800320b00002020804a54100300760410300803221401c605090800d0b481d2011f0407205000e0050810000c07020400b44131400007204802c0350b075051841d60445e03844018000d0400648550f04074a1a92142c081c012002c10606402c05641301d4040d00c0200034a030307415546050702402c0b03207402a03003c1c04040000364488008000780c6001e43c8811500f0868000021322001050b0002c0e4000d0f000360007400700041030f00c0d0320700e40b80c8a000c1c1000700703442c0700b0500c0c090b00c2d50041041745200e642c20f06022450460003c00107100750740c880030701032010b031382d5010540b0341c207590507a440d220818142c0c40700c0300e00c1c0020303a0101e43c0001c001070100303200b035523a03480d100c085c0c454001c038110505c1c01c100b00402101c0c40400c08441d2000c00c86002e00b02042c98401140039130b0050302101102c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 835383048 1250 835381798 835381843
    0xf0606030402010327140102120c03040309030b0103051b120c0405092a1e0112020f0715020d0501080607213902061005040f060b0309010e0705060c 65
    0x10fa009812441c0b550380d18800380303501340d20000c0c0a21400794940c4d8096610148400502810410600807940340f00d003112032145040d102d01d21014441d0b400148241c0400070000c001100185892440500a50080300204014102c190011104440e400d52083c03165408110f003100181021030380170780c0500c085500254640e1014590380c1491503402030440c3e043d000040382c1e41c20b0f5107517400080d4030305c4003600c10406e1220351700c12030014008030032021750206003420355007070b011110740d001002c0384100c200d401401c02c5055501d10200c40b003c0030f824649150042107110400d010392081c60300411943c1e0081c540ba013406103010741004000c00008040c42c00600c02500310168030342294030620f0901d940c1c80d0141c0001d55a169030f071003140003003084440b2245154504203200060090159080c040e512000754985000c20000f0301d00d0b0500400115243c5500068020700c0d100550b11480b0f00d20004140c0f1100d010085051041c80c0c0c0006105078028024110440400517417a024800d001e640c00554 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 835384298 1250 835383048 835383053
    0x41404020319061206050a090209040b0c190903051b060409020c01090c090c110105070f030e0c030d020309040b010302040e040b10180b0427081303051b0102070e0f06060304 76
    0x20400c081c0c0042c1854244840018a14120480120800d0181e20100507030345400f0700701c0c4296210b46401940c028210000304021401495416030001001e041c3c0c03a10301420003011400b010020284040824040711080083c810103219965521850115544c1d100b020324000880328007e901900c000f1550114200c60780c140b00350b10822035290407200346210903a803040c004015100034011440082e1549011140c500c00500a00c0d000d41000c0c0c079032000001a6040440040c400101c2201081c820300c00b1649454801780201d00c503503a00c030b90145039558560300900044c0c0d008040407604040c4100b004002110340b46200035040fa030b22403c44070333864503015222050b042060300090050200c44a091851204661203042202c6040d9014003049030f05090140600c40000318485010440c001c0d840d0024856a00070807540349644e01102c0b07031684946030b003403401d074400110b8022800c01144801c569030301009940010400ba080306440740c136001d40c02070a4808003601d80b501980005c0041800c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 835385548 1250 835384298 835384321
    0x209031002190905090f07120b1f0807052a030405030d090806060609010509040b12150901050609090d0c1a16111209011803081c0b060414040203 64
    0xa4200d000344040d03444258092446500c0c000d400044804541200b2000403642805603145d0310514504000c52a243d80300c42e0192038403001103075203480781640d41c442074140c0d943c0d18400d0701c01450703007030380e14003026802880c054495840501040300384031041c8002220142180140200c00c940308401e20484071143ca040ca155000d00d400882e850300401500f0800142d000b1030350802c8031120821039800b80c440c0f40c148150b0307120b603541c21400a81308110b50b150f10708250300031060640c4041d10840200d0121405039041c562100000503003c00ca62043c0b06a45409019080d040361084503840460704050007032a03a640d444034451304c00c0c0008800e0440500058203800c000d40003249001182038642050020400e0308d0101c0c45030701059426906048505000403012940c0c02c1d00024a458204002d00540310b190f000c22030441c080350440c00120000c2c0e18030014040180103256080150005003510300140d1301c985032418010301e410710041040000c2404401c0a00d00141c0c2c0050780c03034440d01c071b6405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 835386798 1250 835385548 835385563
    0x127020a08150412030504020f0402130e09011d01060503070e0a020c0a0c080118110d02060c0307080712110604060c3c1b02090c070b07021c02060f0a020903 69
    0x540740e001d000c00315084524107080c0c0300d00c1180300d041000c001455482065040b0303082510080d42080561003040341c9828030b44c0c01402d1074040800e0002d410356440d07513a21b06056007252071490694454201803c244440340c200b001156000009108441c1847c000c80c1d606c0110b886030848904045021407403100003a0f0480e0310210085040c0ca26800117406d140405040714440d0380c41d1076203058030360041100304080807035140d40d2100701d9080d02400700e4204154400f200c031059900c13140070001d9240d608030030401001f041d44640d5245440766010700f01780c41c0c030015078200c58040c810b40041044507601c0c089000c0794059400400081c2c00c030410b01702114a1905850f00a40d10001c400019018500d1514103008090300032894560300700552104a800700d9900c500d4103c100c039448140d85c010b20707040d2a8950f110310540241d9061010a4489128500083c1c50210158000719031160060701002d03550012102c0c00c7c0028045400d10062540b68400000c02e89050598040b03600c40130b0741e6082c040304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 835388048 1250 835386798 835386809
    0x10e06070c030302031306020613081308191403070b07080423070f060c020d020418170304030f080f06010332010e060d03050a0302030c0f070819020127020a 69
    0x142840c80c2c4030f18019550303500c100d00c07202110180010004005100049162282d200c2250400c528006d5903142c510340d0f00034100c2d8040d440d0003001c010541600803c8a03101404502c002c481001d152030500311a10319620200308401e401c200092000b1600700e1450031b4020006162841c1240e440c0d09201c4c00148440500b0b8000300d5980c6e0008940183c00101142665075600004038600d0766040c050300c0c4052250402034001c209646450b000d4542544031046c4041c003440f05540a503d41c1e51400000050f2101c000c481a5012081c0070605502403507050218115041454943c1850544c6c005030500040141c0e0405890340640402655440d4205144400c44041600105141d0a450785540303404d000d0002680355502c00039956141454140c818190580c03641803600c1580c840c21000703940010aa0f10440104000001c54001c50800401e4114013900665403035900d0100c8030740701d020402214000b1a030401070101c110f004031488592044450001f0070320401c071180b000c100400d0040d80728 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 835389298 1250 835388048 835388063
    0xf020a09180309080c0310090510020301080f120901090b0d0e030a030f110304020a0e18030a09030519080d0903020115030c05120703030f0e040212091f0614010e0607 73
    0x40040c481c581601c141040d02c26103c84403c551512502d65948580090f03003640369108800502d00081181e122407011802002500c03800c41901d80b07084203a074001c1e840320090341e120000505202da4280162082a40b444008500c2d100c22400000c0440c60070340170b20244100c00248d00b0459140320f40c042c00380300320b60101744c81d00c03800107601c090000c0506080403094642031560614030142804c048902c21540240f034200300c18209940740010240090140650888445e0b0304000000e0420203400c41000303541e80d6481450031464518103207181e0060364441c0b01001140c01000038202401c0d141c91042545c00010310030600d0174200e02400284002003562005c1082c080144510101c250054030403d807005c0340b2072380490035481d644180a01c03010f00001c030454811015a4400e25480c200800020005414510301c03440d49500510241c40c1c901081e80141489140f0182c805050300d41404846020402c4510740000c0000c2d4001076040d0301d0401c445810a03094a5480e070007a900401d070001c0c038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 835390548 1250 835389298 835389311
    0x11070b15030f0606030a0b090a0804030b040c080a111c06050a020904110315040903110f0615011b0f0f0803040f06182a0b0d0225020d0f020a09 63
    0xa894600c845081000c0d40a8042c1603031601002100082040c021800500141482c401e5903c030751020381c001a0410019000b18801200400c0168000e003010f107000e24400a981d0525140500c9a8189a40301c0310107034200601d103201140b1040b017660403070002035a010718003008103144450804c1e88400d009040c94038040c1842840e42059014000d544801da0301049542604264081103010449110304d044480107070007001810140c00086c5030f24840d041c19a03090001c55419810404166604401940250b00b003000080410314000341189007800c05c0303201c104080d101302c005107402d08005401e80b410b01642104020190203007201c1e044e08a0f1510342c482c100340c5081b01c48618652000d540483c01c2412200807410000c800a40c40c551210040702203401c4643c0700000c0e01d00200c44005040d1200b1000640c41d030038080102546810030b4401a070354050326402800f02d20340000b0680640d201083e2410068070380c011265629034001d05c207d00340503c1840000e4414003141c000d256464107008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 835391798 1250 835390548 835390561
    0x30e01110d0e070509010e16030f0e011a010f050a1d150a03140c1b010902100f091703030613060312030209010e1914010e0901030b0f0a020301150311070b 68
    0x14401c01c542c16400b8150b8015664032400c100c0c001000380078070ba11104c0c070342000c92104548889020000c0c80b460501090f40030141c8c00c80401c0358413000c000040c0ea51100903083c0c00314451240c180481800b42450b40001c02201002881401100c80d8013040c0b02484502a0b200041121284c500d200000c1141d110310b41e15180d000703a00d400c24840d07600483c3c10441400840da0040031403c0c410004400440c1c1000d20070b034071801109104880101c019565004c8036000340e00d41c04810001480291680307250083d0500d0010121012a40700c8200107030001d041541510300401180e4003e08100c0b201403002140207580e000614481d07100078580c08441801d036000e00d0305500501149102602d415044152500074400740c1c02c0309180769291000e0100e01400f07881c480501c081d01042042c908680e200011801192801c0e00a0b00203a544042c3d00003001402408214a0b9a00c01c0c04210198259450000004101c00d40b490140d03080c542c550f40c0d80c0d81070f07007001401c3e1600345400154840107030a200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 835393048 1250 835391798 835391801
    0x20a1808030a02070b0405060d090602220501020d0c120f18030c0f0801021219060b0414030c0d0c060804060f0f0507020d091809051c0f02070e070f030e01110d 70
    0x6560b9000980a45900015150300b0354081d01c0440f4800380003070f841c04950708144401001412022070340c00754240701c00e0410b076128849000b801200c5418a5104604045c00a49070030540b141c08020800902d801100041c001c00c3d030104021803508002d5040005400c3c00d45080c1d0507804040801c5101d1540042408012104041110501e0400d00000754841c0342450a03446090948801034081c42d001c103d18002502a1000c0902000c00005010b601c07030f0042c07442c0742e0217a0300c400080c102001c0c20741c1e114030301400003000f1240c04a40030b0505070001c3d626403502802500c9000d081c401004000ba0900189421000e003551080c01c040202d950900502c10044c00d06444101c018030803101c404040d03d01466950094070111080741f01c0034420700640030301801d10400120740e2809030300e81d075503042000c03141140c00e5103c0585030013541c44a054002464007440d64800e1582501b103000b4002e07a47e800022111110900c1c1c9004030703060016000071350141030704000400320741d100040d0101d0b091095 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 835394298 1250 835393048 835393057
    0x10020a06050709060215060f03030a080115170c0a1b1406070503070207050409061410060e0402030601120f0608070b13151e020c03030f040312030504030210020a180803 74
    0x640c0104015119220700715003800990103a07038056844410b026100b240780703c1c4441e9111800070401c0c0381c4101e1a03c0800e00710b1700210340c030f000400c4030180103004031001c0140d682c450300043c0c034005010517003281180c0d4941c0c03006454042d01101c0000c20185040c4a6014018580041e0b01200c3d40b41882e0701d000b850410215060308014055480811401481001281d0080d0800c1c1e005000250a000411004066001e011900e487d0b0b0b9040607407280b040c81c011b80b84609007200f002101a45003607005040846061141d900c118810000c001d203503078000030f03085448154200c0c0020402c001c0080a401080785400190882c03107032a00c0041c802801c0c03401856004403884022580030364580d2031000754044440c0100c04079801040b060900038074000340f0403880c4000d03c11207090304010404607081d648184131045211000050510906c100707140725666910309482c04210718600fa0703c000b9140c846280d03801c0249600042c000c0e6a0340d1044800c650a0310400300303140c11103540c9401c000c0d030b039600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 835395548 1250 835394298 835394303
    0x92104090c0c0507091d06010f05130612080702040f0e0601080c1c0308040c090e03030a0c020313051507060204090b041b0203070813080a1101080a150e060402040510020a 75
    0x41010401c81e451040100c5002c16a000b0000e000703403424000c008014150a0041c1d03605e40400065426800d0410003105009107010402c214100381480140070564009201015065091a07010800302220104400000b5001003145031614483d02c000f60240c00c0d0a9081480b440c01d16100300c80740c031004078000c3e0486080000700d590251086050202900c8980741003400341c0c484800ea00042800b03a40c1040d4040d126003080044180c0b204a40011142c8961481c10785030b10201c100842a4020b1142c085200040d000a5040858a030440028004070740a014012011000741a1164650206952015038407890554880e921240010001d1440c2c00740e55101c1c86c240706440fa00d0300c0400c584000c400020354090340c90082191200c16040d4044407004819140000780001c500c0350910641c3c8983e80f14004400070b10020500040c0903000151441c06010b142c10101c009042c1e040700b2041c100c4108801100007542c0340c40001c0c000f80190b9008079000181017140c41d151680c04101c0002407031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 835396798 1250 835395548 835395551
    0x210020a030b06210604200703030905030a020609070b040819020109171b06040305060c1309090503070b0c042603040f0f170a03120207050106051011060105030c010504030b09210409 80
    0xb81d607101040b0a594483d00c01c0800300100c7d2124a58243c0400f0040c81110b0003802d02140e100300c80d995540c42c644c42139042c14010382013241031107074181050110034024401c42d5030700c1d810682003510650b11284030071111006580030024000469018802c610020f102c0c03009903141c3c0c4000003000c151a4115010039440a96816400d010146010016101035030303007083c0180042e40e282c040c0742e1b850303078080c3c80b100d000151400300006050070180150300103d48504090f503101d03103062920030312200780501544a9014284401c3c00006820304204a00303000780d00d080384540300c1c10704883d8150b1190390131005051407081404581014400080012111000b210071031005d0355804082d101c0080900080000d4900b00d0340903907495580d0043c20050b4060382c00050159503510000c1c0034101480c410801080850205191501d402d1105900524060b07000d05070403030343e29000034514415408010940d00b00e5002080700000e00300522400d054900701d56080300706481700030070210b8106100f10001c0d42d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 835398048 1250 835396798 835396801
    0x106060207080d0537030b030c040c1b0201050714031c020a0e0909010e07060e011d0d0602031e0103150b03010c080f2a090307050a060210020a030b0621 67
    0x103080018041c00c01c40ba20782c2c1d014203080e030400ca281e1043c010480f44010824494110420385c01808051304889440341e2800607540480344285402c0c5044951756503c118607080315180f009801600c80445403d002c0a202c903c04014801a240b501868101401c6103540c00b09403445504e0001c000c1c1861041c0318002000d594040031603400781c1c41000ca0030000150388440a40c1d80381020103c090b04000326000105141244c0c44000f40f43c50610380c00500014040c4510303010b03550300404c00c0e030302658821409c4101c0c20386685c04201002c2d000030005000a90000003e00210703d0440c4500710391417000000805543d4030b04041982105020414007603c3c80d240003068035240501ca031054040d495141d14000c0c2d5204e1907002d0380442e0003040ca0001200140d180100000d2040001003c0304012550f16151200d02302818984000340e04250301482c4040b0003030040580002c0c4000d40d06010000142e9030307403213000040b0040e000140044da008400400d454401050241c1000b51400c10580e00740740c44d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 835399298 1250 835398048 835398059
    0x10206060a150302090f0603090109030306080f0c1216140117010e040212190606080d140706020a021903080412030b0109090504020a1d042006040e07200106060207 72
    0x506035200d80b850a00122011540443c000e402a002c03030200100054070078034444000c41d250354401c46959200ea55141c001c00209600f6214010142400394001c04040b84a85003007541c810643d0a1948922200c0500801040082018400400e0b00e2040070108a80d10504070303560b0300007410354501003542d242c0384003425552002c3c010b040382c503614002c26458030b481d000d02611a10075411040c042c003420810381c40004080688440141c0f0400c2c000402c0d5146c200f01901b801c8801a90404004007420020b400000c1042581c806681180005076500c20800b4141d162284095900f2840c207251403046040c940c1280143d4812405482800c0300003d407808101c040780c003400740d164045069142c080c4420301055200990140c07000d44071680150701c4806800ba41c0701c6c2003407150751505a0b04200020840c500580c0341403107103141c10403c441002d0f100018850300450190341c81c1900008001010340744102d0f45201121210b0b00c445100141802100c7c0c0a04030a010f01070152150f50700005a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 835400548 1250 835399298 835399309
    0x901180302031c0807020d0e01050702041113060e030309061b070305060c0a08060d230c09090d020f01060302090c0306030a140708070f080601090506060c0727150506030c07050307060b01020606 85
    0x20001a681d0718108c4040c2050015145600810020b88c2c00c16a0f03250b1042040c174581c0003c1c0380a01c03907201101c011038a8030750003d180c40148603043e8003075002404188919180d04095a581403c800800c80d0426003400e0058a8081c0740d600c080c142e44100400e110135004000020300e10003076242d44540b455500c0005200d00b0002c180f030000c1000802010350000740c4d132505400c500929525055510356418180007401031081a2600889a0040d80000c501c603901040700000c0140b44100038004030b03103140c0000d241900014022031a402d80000080d20640c1c082c0701900c111540182c01300310790459001000e03038580540c041e0740001c0c07080382004640981c4000c454401c644280703000301601da08104140000e80b60260025400901c14040f480007084107010810280101c04203805001e01201482801701202410304003409151500031003500782c0e4a84035400351442600c1555403031f1540005d40c61030703104241c00508207010104a07c000c00c040c6810100d44040c09a0032908540c944804022 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 835401798 1250 835400548 835400563
    0xc0702090a0c1e0c050a0b0106020607111009080415030b0306062d030109080706020a02070605030601050a080709090905030918190b0a0f14040c02120901180302031c080702 76
    0x480c2008120141288800343c010100340020700d88807005850554039103140081804044802c0011040140a010390410020750301c501645810485a1529200c09884114014001005a48071a280010712681c503040b00c0040100c5028042020f00b42c1e000180100210140c00e4800c0c010a400f140a07440c110245451040a403070901c10b602d0000412020007a83c0b4001998055403101d07002c4010620460142101c1c602420f0b016135a001c5080700203091130a40d80050042c01b03014824007100740d03480b0040d1500300d40b15081480c016152140d0075aa424001d030702407844e96080411400402c4004000f80c05500400d0b43d8482d80f820140d000450040002c03604142c40f401d1000e5603601c40229908001080c05000d8a40110b072501c81124481c040d10541000c04018040e0444401e1818540701d00e103040609440581807042403051551654800c4403e014104000064803001c10302c9a4584040255401000c8500800b98051012100000c101140c00030464103000180b02e0780c004120310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 835403048 1250 835401798 835401821
    0x2a121f08010e1b0315010303120c090b0a0c11090702010204140906181509040b010302120601061d0303090406030303060608070804080307050307210501050f01031407051c050c0702090a 81
    0xc042d070f00b803800f951541c0600c450601681c5481001c0d005400c120b059000039002c0d500036034550b558090480b052805451441d031200301000407450040100c00c4142064a000c0300e543e142100484560303042034040f20541d01c15190f484503004040c801d0031501540140300b114001480f201070220540100803c440d4100ea0f200e410817401c150301c0d54129050104185d00c181040c10360020003408501040b890142104d003141c2c80c20401e0f00501c151b10700410060070b0080c40000074400f540c1000001018064250001003444418662009003964203205580a03840e0260007040815903909005020b410749109403804161028041254207101c2c01030280f1070350b003180c070b004c0ca181c44c0c1890032a100e500040c811020031070007001182500701e910700d55100c405140c100105940d4100002c00c410044a41c04990526241101010300c41c0c00d04000c9c25403000d800e0414a4030f0b25840702000140810102c05070070301502c2c0008000c030a010000c09002d10380c0c002e5601056a0351130039141022070302d0300c1180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 835404298 1250 835403048 835403053
    0xa0c230706111e10090318080318010e04110304060203010f0602030c0316230a0c050d031b030e0907051905040e04021e0d2102062a121f08010e 63
    0xb00c201415218000c0f4a04503001c8221854840750031300c00c504440d0458400c90001d08039004851503490480f1401001d03158690182d481c24066019004a0b071f1685400d90f410301c10b601458200913a11544010503110802000d69642e10341444c104000350301c240a01e0880c000b541c10f01140071403000050b50000c0000400542c1f40000c100d0720f04020a460307060844880c0da07443c00b141c4031815980c034803210883c041c0c0b0042000e03005030714004044500c0c03078001318050003100403d0404a40d000c0c01c22159070880304031041d44201942400c40e80171071880201500042080c081c00010399202d0010030010a50030a10942c00c8031540080340c041c4228410712001d401c407580410007615003080746a000134031804404025040701d4010400440c404101a140e0450701c417000741d01500700646d00c07610041c10744041d0805107096050620941d0090449030940080b0848411070550400e085802c0c101160602d4160751030151a50a241d2524102e400510f03483c203d400900010140503589601c00640003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 835405548 1250 835404298 835404313
    0x405071719060b1213260f040b0a030c021f0f0204030b130b061f0f020c040e0c0f060403020d030f020c1807020f060705190311070506060924060a0c23070611 69
    0x251ba4209482080160354840104954902d0800740c800810042115448441d11a4031a48024080340c211074107240075500a688a4200d089040212070501000d00c100040d000310034550010090280387c200401c0c88226906008802c10072041d81020745100d449aa0119038500e41402403c20240c5035168006518401c18021140503034100307809040240f045901e00f80628000030191032001e0300d0240076412040855480d401c160101d0805c991080d140c072803500e440d40d03000c207030070071030361034000d403c00c4070181421200d54824000040c09403002415541c40c0365903009499070781c45050700c6880151182a1aa1108040c0411800d21910454845500381400b1184c040300200c01c001c40c000c2015601c142406410b900c50001e42602c40c002c400511491800d04148400d849015210400a85404407240042c1241004074440d1410655000d600c42e030341c00c0c8003522030900f420030091018035118200c44801640340d0070f410300c100381c24086499103a034842068070404244d40003c42c0d160003400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 835406798 1250 835405548 835405583
    0x110a0503130203070e011d31080d0b1c02031b030313030602031611071401110f060702011b09031101020a05160906050405071719060b1213 61
    0x1406154442100d0281c0800440c00707600082c1840c0e40c07500012001003e00c8014882420800100d680081c103a031216074445c14801c030b0035094014402214403c2508500d9646031121601d80034821040d4425034041d01e4900200c030040240c030f000e01c2864006c00c4611140a1940603050035244455000350107810181e5138490202c498802c2800c80e83c2e0144001c000790350503c969242d4100080d0301680c00143c99040c4001c90101c01060700320f2031020003003051200c0340300070801b14848003103c4088401b4059040c940c00181c038092644401034116000710700c2000c80458001c501184600301540c000c01c03000f04e001c6103011030300092014400010302c02c50410b100003101d10ba190280c24405004681c4241419a5094680100c001c04440450b0407013000300f140030050300803880940310840d020310071464180c80007400c0b003c20340c01c20b51402c9048004a02946181c1141c43d0a100c401c02d414000350782c865480004070351005880e00000e4202500148600d043c202000d01500d03030141e0080244c1010f0b8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 835408048 1250 835406798 835406807
    0x9360105060904020d06090201110d0203031b0a02100e0c060a0f080601050c1b0312130f0b07030516034103011d040309080610150905061b0309040903030e0f01110a 72
    0x2488100d0500030851110b4000ac1e40420400e08402244d90003141e80385010700032003001100c801d003083c400302424004c060029070041100d0b090001031030b20001c1c40805030960545002070a2001075002800040d01e21101c1c1d5000c03503800c40ca03c1117a2518141a10380703400455042c4a885071122441c0c0003510341c0005400c003001d805e80d40c400c004040728030481d000009011070768083c0399104900c204440d000c0003180c90419070a0300400303801901a05144281c0c50241c1684901c6d118100b038001804000b00800d40501007800c0c3d64140004a12901c0610328801880c804a0b4044244e0090b080107840c250110040201d80c1641d40700c1414902018415122914a80c2e000d08200c0c01c1c012080000305041008004061080c00c102810002035460080d082e0740100c59950400100701940a050003142c886504503003203e1402c3e40c0100054840e140701500718003402d01050f5010342440001024941c0c590004584103040038251424074060f40516400c0f034140c0c1070100225401440310314942c6008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 835409298 1250 835408048 835408061
    0x60a02070f03061d0f21130b120a0c090e1e0906090120042c040303020a0e01020a03020703170c03042405031003080706060b031f060e0a0509360105060904020d06 71
    0x1c6e051103052120780301d54907000b082140c10900846402041c50400703002280212508444d001c5e00800000303012103401001c60200d070040d144883d40c6080442e4551840c503480c0039445105111696442c188000314944519003034a54000c02d40c2006a0b044031080040091a0f228495411176460180382428004400c001d8280d0b02108848642d00d02a030384000c1c80761544075500c0790742c00581d150308040c005000c440600c023613b41150b000321122000603800043c0700e001c2d41c0d001004805080707513a000d644034520420b29669060b020100c1c0c0003c00d40420b202104610010403843d01002e600100f0464003130004880804ae440d681e0002000400d5003c0010710340f0a01030744000c922580c0710241c20311507078010303901c42c04d84810325403c9001e000445000c0c503000e04101e01e0003982c11fa9400300051a1500c2a01400b4452885240491501080e455100da840307401c203101d5401e0201c0000d4089656204208a4113095003000001100b44c40c028404510a5600400c2919220056124040100311 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 835410548 1250 835409298 835409353
    0x150219060f09050a0c030b0a020301050303030f0a0e03070b040b01080d08180106031a150907141b0f10151526101706040b0402060a02070f03061d0f 65
    0x5442e200c150100d04107005110140c1e000b0840c602d05246145000302e528807004002441c0c00d441880107000321b903000301c05c0326006004009032401e1901e5002d07801c40103042c504c1e4154218800020b0107003c2281e000c003528030640c010070852921780c0c1c0c0c0d545142e888201c1b000403207002034580c20025041684845188011603800000082c20b152a551460b01040b01400c06c0c0a12039440c50803c08140907102c04c0a050390000d45100301d590820080c007800c0c4003600c0340780302d81007440855402c81501c40100c40600c42002070302192a201d02030f06401ea2541d41100c03000b000a400d04400c0d104500100c20020101c0381c1c0e4480d28503a64070200b404603038820b6030814801664026080c06212464043c903242d0241c0406414107403068942020b404140d56000181c404070740180d020032011802d10015940d1060b01940c501d0354451155404a0810100c3c1d00010009510840084184103403984a503040185928006010700b861104003139444901c140114590f80c001c5e40c03040240130050890340e40100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 835411798 1250 835410548 835410551
    0x8070e0c310303050c0f01112703010903030209182214160801060501020604020303070308090304091107290c0a09050402030c0c070e010e040f140a0c150219060f 71
    0x440140c0c10074a80c414680c000d0b4001035000c00c0d07110302900d0510080f40e06100300c4008005005000701807020f10b001e92207607454011440450f4110a422081c00e145400030002d008200b1901c9514003c1c009410036004540900700301c5403503140300c0e240d540201d40146000381290030901922006509040202c050807070740008904228100306408000000e400481e02c050818082d04104441c0d086a0725a440f40b8115070124042c40b02585001c0211000c0c0c98140c80c00c0d0080c1d680f8400d0321495403160350b22400342549000c14080e541a412000ba100203442102000f100c0e02d12940915201c202104006054000110100b441205014000c00e503d10041c1409000b0a035900d0001d0100d8100700c4443c8c00c425000210341c001d4003024060702c00903150f1038140c40c45950500c00c00030508100104000d1000e0303620301440003441020880c0806045080c0220703405a80140340c00480b1448034824030240320181c04e0540005030020402d90700d803090000301042460302c541caa0801900c0e0a4034140d0015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 835413048 1250 835411798 835411867
    0x40312050c0a110906030d05220807030f02041112131506080c0a0b0f030c090a030611090a361407080f100f03080715060f08070e0c 58
    0x6010602c018114240540400302d0980992010b01c400d00e50010149840b0790001012102c1454011059420040c2450a0340b21052601d41180500301150340201502e8480c03d980001002900784820010702d02c00c0c0ca007808050180c60400b2854000e5042d0007148000d42000500100000001d441001d4020741c590039046208803000800ca5502d50002c0a07680c10400d8010b01504140549400a1403601c0d50f4615011003c903140701d060201a150005907400015039aa03030f0758403405400301541c4c00038010408034580c490362016940c080c0050700d00600c040840050381841205007070034500344411000c4c1e501e1764079070703445800c1584c1842004c0076155100200e4042240c0070700c1e008d1040da0281c4454500d03092130440e041800c040100340442da40c1c145002445101402c001c1c1400b20b03036106002e680c580100e4609640408020012199038a1070301e400040c6030801e030a40b4600311040c0d04140c0b006540c5403c84030442007001c8400c00a5000b00b04140507018540f0280c1c90710a101d100b9400c403c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 835414298 1250 835413048 835413067
    0xf090b030109080a1b170d1a0a0e0a09080f090301150b03010b130305030c0a020a09090c06030c121b09080304050f100909020a05310303030c0c06020715110f04031205 73
    0x5400746c58440080d00c0380082644690200070340725041c42e8540020441102d5022100040e601403484e0250510b122091004100d80c81229084500c01d580d004000540742d40001a80008580100f8100740c401d609003081d80e02014071135030714031050b2010640c03214610781c00d041c0d86c1d1000e0380c8036200305402010b81090000120f8028000f401c000c904000103407452940c0ca004005c94080740e5001100301502d040c00e9900090301c080f83d5a421103807070707040100307c030300c1140815101c2d000e0303132001e1180860500c560180102c01780911030b0f58021003520b80c10f0249884501c03032642c1e0302070307806240e0b0420320600c011035081c6041c0710940114007041c41e00f48003980c2c8603e1030340305036000581500301083c0c0201d5680b0004200d40c540313110240c1900548580f0b034020300040712500c500c5201c05028151384002d07802d40c9034815600d005035960000010342d41e414903032405c080010128250b12613807600d0650b407038003072201800803100d40d501c49102440c10907085480d512a52103111000906000c1c082204109 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 835415548 1250 835414298 835414313
    0x200a06080f0127090602040e24010c2f0102060c0f040b070f0213050105040b090f0708040501112205090106021203071205091c1b03110a0b010f090b030109080a1b 71
    0xc3c2c0c58450030f00561a60b2070508a00888c52015000c075418a9009441070301002a00084000b884401d02e40700380808070340d0503c00e80c0c220f10016a181550808030f134941030781c46140c04028a04400783c0c21181507945401030407906008a00084444d007030100300401a42c03091002a2800701d010300c2038240c035541c039603000808070f02d0400b4000003840d8079940108103500d4144215450800700b5180c464042c07400190b030380003145000f020b12051203413490228044c0a001d5021070b503603198160701590740f090040342443c401681d0004002c12107a1641c404a000d0501200c828101c4210350018148004040d24105107500002e103c0c03810010000420134001845c2d0040c00e000707200c2940a40120703619465804008d84400405001b8803e80c1e240c85881000c0c000340e00345070070750140ba010003050b0800382458200040303000040c1c5070740007c200104601d007401050300e0440b00c500304104800809007052600366202404040c120060910007500c0b01d5000781c1602011048010302c12600410329640e406 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 835416798 1250 835415548 835415561
    0x20a080915030f04060605030c011403330a0f150507150f06061107030c05060f1204050c12212a03130614030106050c0a200a06080f0127 60
    0x1500303072803203c040c00705100c3c40f441400040e1a0a4020300405030045002070b00d41c0b0b4664440c0c0400b642d00100090011548060445d2815101e10b04200d24103842d04c2c0508940c0880f00e4054454071203801c00040800c1c1c44e030700380300032542040100b05840756240b905451581010806030f504000504420b44541454400d400340d03a4100d240000d00035040c280c0c0248103510924a04803154081d820603c040b030700b69000e14003141c0d41100c0341682d442a0141e0f640481c082c00995660500f80e85007844200000030810b003041c0403055880d69200c140c60f00c0100e0f5180c01c40b6603d25000e003080300340e4002000d82180104010040e8041700c5039030045c41100c6c0c022604070040c0f0904a074002181ca041480551650800100000c0c42c01822480515155246c41d01c07062040d503082c001c0c0020042c0c000b0308103020360315249800c035a001a26105212042c1d510101003481c0c24840c1074a03d0f07020808a0240341a980150004114916240c0c06c00b00c2d01505a04240505520400d4400b61412051300d10300821 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 835418048 1250 835416798 835416811
    0xb0708072a11181311011b12030e060702070e01050a0501050d0b0307171f090b130321063b07120e060402031606020a08091503 56
    0x12405464100002041464100010506948880d001d1014100050701e95200305800c10488141a04540c0010707641e00203403000c45841020660030480169244011540802d005185401e502c8103808011a808000704400010801c1805c2c864404070f80b070b0011810110150303080005001d00850b1030940380c20801c9440400680c041d82c818019001c031546028010007065036038051850034400003038494000d8904001816650b509295180e65080087c18001c004d250303443c1400e9909521203c0e100c0008101000703d2100c000400c0705288000d100b5844040d4002d0703441040740e01c80e8800d525500703076901c0c003c1e010000c040722030b04200c014407051400d10281c0d4090004902e444d081001c040e83c00390816402079421240001440d400300408182801d48615a5815107035544a03016502314045002180c03c43e868803225038010300c00040c0b454040d5000324210b900c8140a40441c6410000a00820340140c00000ea580c00040040c000b500040710014455503d60303c040c0030340700fa1500102e441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 835419298 1250 835418048 835418057
    0x60409020d093008060f01050d0b09090d0833010c02100f1b0503120a020f04091e0e030405100203160c03140318010e01030e06040605100b0405090109090804030b07 72
    0x100103400c48400585410310700a13040c4a502807805000241024041398585c6040c0440090116003400c060382c0906003a2600900c40d0105081008009566411102460020038540800708054050319500b244031072480006c2901c80c3d0100501d50111018007262080c18044940501c10050b0345034101200c0101d42e5540c1d540c0540d40000300108a078802c2e2080140f0b400e800c1250390b001c20700110440d2007000d0340c04068650b544030f80c000d01c6d000388a580340041c036495011038049005602038016851440014040b6004000805005000c41e8114054900c07154010002001182002c0003000b24400b8980107481c100040301225500007180070500b00e8500404040c180f0400038092900b11210390f5100046041c0011517904480c407031400241c0c1814849104002000c6d680b294000d54080744d150000d40d9a5401c1030b1500030084c01007a5901c20020340e034540302180b0320003d00242d80072590f009203241c050b0b918103080a00200100041070b01c0c0340400300004400304080c64502806176510703035203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 835420548 1250 835419298 835419353
    0xb03280f14061c020d020409030c151401050f1e06040f12050f1917040510022a01050d15030807210504030b040b0711011127060409020d09 61
    0x40000c80f203100c41e84040103002c0040b007080940c0307552807580113150f819500090f055103103040903600c28402d40801800c007400702d94000126190342e04038480c1c500800f58001a41d0744c8480801c0a1005910700194005010035556001c80070000c400c542601c1001d4080d51804d41c98002d16051202035800644c5940407030703002d00080040410011421121140280802540c0ea601c98240d2210700580900014081d4070b1501403020010111401000300070301b111030300184103c003c1c2d2500a4a02d804a501642d0980c400d000f0754051240d0320b10540503514140303019140d52401009211400c2c4d2044454204803010000030f00381001880c00c1d90068200102002020110241c40b0032040400c0303003040b5007440200009101c90f886142c22980c0b11301c040d44a641c5058088540e600801d9585042c0c0d070138501d200e42401804c0e030060401504c510491180286600c6440a2030000703105c40640100e402c0008010f602210b5025145007541001c0110703400c210341d12060310044194007022003c00c207060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 835421798 1250 835420548 835420561
    0x9100e15120703020a050304080901260a05011a041a0c0a080c07050d321c0210020a0f110c031b011106040203030d020703020c18010305070b03280f14 66
    0x420480c0d0014040c5015072070260442c170001d156010203800104051000300710030b116680504294801845059180b0215140758074020500322026194014050b1030500089142c412602541e41421207981949242901e000c44a40709030021090b80440701c02c080c04542c48824081c0b0502e0175803030103010640d8030b03448016000b030300b001050342c000c501c00e41602200400180d40c8041c0115081d541070703054240d0701075465034044140155800300005010f004999084241c44030850484403a02d42d00f2554400b40d400401c90403440b0321703030442000c18a40318142042c1417007030303e009510700700c42c8081c4c0302e200e0f807401c0101e0f1a140e10041c10300041468030680751469680164181c500386602401010329003420740209449100e0025551140b41d000100c0b6030906000f00f044550002e0090150306901c42100306541410300280421601801000d0000413103208040540e80035500b061061552000b014905031240102ca010074120543c481c035a01c20310b60703045d1144100751f80300c52001134254903086 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 835423048 1250 835421798 835421827
    0xf0a03120e0114040902120f0702120715050a0608010f0e06061005041d01150513050105030a140a09122328022506051c0e030301080f011a010509100e15 67
    0x740000300c08c0f0000010402256400a091281c2030801d84201d90389540714103200b29102c080780c3c00f4100e41d41c100400d000034620700c3c0c0d100c0c0c801c9600c2070740200541210080c094044c4c505000700303000f059021300c011440c280742500c0c5042d0104d8650400c6881d007990360b41c01c21150044400900c51511040c001042102c19401200f00407500d1480d0031407400d04417003400703041d003401da01906042040200000b00020000c0c0e0040c00d07500c440000b2811203141402504000d81000d0908603010b00c0400b01304a1030300e020700584140180707002030280d481c006054440704150480f0184071590240038861607454285036001401d880141c0d0301510400400d6440d50341403400566035800c00b1102c942c2d08024040d4800d003580c6d41036030401509002c0400c0552804040d01c0000f58000c11800004000a24504005180d4403145003040081c00307104588550324182c10780c0c003000140810401c100300449860002c034010b0b50f11805041c044020f00b045404140e21074402c00d00d241d10307003800085000080105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 835424298 1250 835423048 835423051
    0x51f06060f1d030f0a080702030d08060904290702011401050306010f1e0302100504140406180504051005010b0714010203070c140102040b0d05060f0a03120e011404090212 75
    0xc9007094429620310710801407a04040960b02c901100c05450442055901031140c40711840016080320903030011800c00e03001a03400b085080b88603118004488514502a074210352180d64000e2021440c7d0ba6203490b003900c02d900c840e072620320781c040c4409040040419058a0b9014000503400041e004e0701d0207640e00c09601040e0022480703a40014010492800782500c1481903904510848134118419409112442c0482c2c1000354020006241603450b6503011028100f00c405132100e02c2c03240030506080c00100d842c10301803030b0a0701c2c6d0032001070440b80140d5003029800c030344680201c920a00e4034040a0041360000c2e004205003100001d101d2050144154803017801e07050ba00300031031941c10001d00103003d5072074101c0000c00c10200e0740c0111084910a42c152001060718101690b0f4981403268a80024001250301c640f00301001025040070741000142c2c403051b664030510515092030b076210700703460031002c0080140c10096040007040c0c0c0344069070040c00090564510158540c045007440c410150790 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 835425548 1250 835424298 835424309
    0x301060305060121090507030f2d0203070b30150a2105030f0d0606090b030411040b060c10090b01062307060b0306070c02031b010903060c020a051f06 66
    0x1a162038011340440b4081c030780c40000a0700f8001090f0300b141c0740ca42d00300045d950000d003000070705a04044c148801c00e519803005850082c0d000b21010340c24034800104404c0703480007030b40652007244244410071b0800c0c001c1c1440140c1081032000303105048159000c0201c8042504005c1c6050010b01804006c034680108030044229414031045041683e0140301500107071070444442c01507024401404402d06c00c480840c1e02068400385e44491603400003029042a00c91172000404c10080000c0f54641710041d03074016640080402107400004007080302400c41c4000940d809502000410943c240402c04201013814034640801c60009a080003240e0030b00c1680036005000d2401926440080e01c00300c16410080c1811f02c140d00c410060400000a08400800320b030580300b41024804069006404021041d20803021a4a483e2240c0107110007040302e03015490201d0b840580900000312550403103a04038005204841090320541c903020b2410721041e80c502008001000f01c1e880440880c000d0030003500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 835426798 1250 835425548 835425557
    0x12200d050c040621110d0b011403150c1e0d06080124050a0603020a031418010507111e010b09280506060d05060f060a0306140f01020c10020102040b070803010603050601 74
    0x20b8901c0058010440a40f0010300c000c00c00448030341c1540c0c900155114040c0c01850001840d070311943c1c4120271003d00500d05101c1c0c419030400806140741581d003944594142032480e0b003004410565004100100030002c0e0f5002418014014902000c0c032414004100b5500089020381c0d4100090003c80060303a00d0144d00390f0681024016516105200c03002c80d00c0918006a455016603000c6004024509803032054105120078452498190f60120801c3c5041e00002c1001d51196001500c01c590004404000c4da00854a084407040040500d03010f035081160010595421000004004a604a40c40500c2c4c01100c410a00010780d40c29580c1d0749070850716001c224506007030300000c40a002c0d0305540d810580e10b0f44001685038442604c08802110301509043d264255540b0140281010f13000d4209000384034a03006129140c40000c0c03200c1c0d40b0041e00039100b03c0707466405202c1d2007801c01100c030040d0f6400300000a2409000701c002c0910034011034996440307506141d0000d003504e4002d0881350410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 835428048 1250 835426798 835426829
    0x1106151302070b06060f1603092102010f050d200c1603030e0d061d01021b01060b0f03043909091112150c0c0f060112200d050c0406 58
    0x18240c0300c903641e00402c00b2610344e500ca5821b1142041c50740702e44001280390360240c0d0080410181c00c5034a60702616040b2407178220012002c28441c080040c200406400181058802c0300d00d0b40c042c03402485070341c00c40000444d04000e011128a08152140c0c81520701d1000050031401d0b0250610040304110701d840b0703808441c5899038600a054036130304008103206000000d0100200182c070741c030a1010364040c0da00e4242208109144500035002011840c1c0c0e05426000041086201840b034202621000422a03081128242d03910300980c10003001280c2002c0880c1289220801c124182c94256070f200c0c8402803042e4280c040300c140c0b40300179841100c0d89410108403c00154890241042c25007090b540462a200700624039480d004140e500d40298030030010a10110010b860001c049183e0820120343d50384900c03d110540e514024480e45098030500c41c0b0201c0050900544c0c08030040720480d15003003901000d00001c560f0340002c401280c041e44403210040c01030602e4007030b6100400e00b4080f022041c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 835429298 1250 835428048 835428053
    0x203010213061115161b0f02010801080304030b04081308070e01090f0204060e01030e01020f040609031106070201020a0b0403141b010507110d0c061401170c04110d0c110615130207 79
    0x13000c4001e0800d5803580c5031051202201343c82801404407460340541a03114100503414007120f8960300040a90004042e940042454080042100d0031070307500144d4009140d80715103846905801400c07407900031407020070000a200d03804011f0140a030203044140001d65140c00550022241448a0002070500504c000c115080d084218020365182c2820085080780811100c24028400e803008644031860104020403a25403010000e010790341b14420058140300c0130070402c005405a0310780280141d01c0703405003800281e07043c01a1500140301c4d0a000c0c0300222401c100090582141c002c0c0500041c141c0001344074040709004081e0003201d0740c2007080b2610b4041440589404030200c2e00d0081c008104103032000c00025134800c466046105114040558680c0f000031001203851070704401d0307442188000c0c0c11910b0507109003107500b8901c0420703e2a140442d0040405010328046020500c040410028105102804624800d00041d0010310071400001c0400850540d0b45c003201d407400d171062003140c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 835430548 1250 835429298 835429333
    0x100f0c09060e0d0c06020c032b211d0c09190c021203040305040f09111b0c0d0b06030118080304080c190503300a0506040902030102130611 61
    0x340d40c0140b512540300120200030840f4a80181d400030000c440d21400041c01ca0f13408206090100011005e403803a2145801c030041c0b80903181036124170a1402000c40940c0f07103015184c41006100845001004117408202c0c18045801805c1d4000030403140c40b140410300c52080c050308400d00400c0f0b40e042d0741824038801025814079002c00348038540c0d944c1c10185410a00810200034194800b400840d070700e00d424900141150420b101d41400a504214046003440e0b80c3d005a1920614a108480c1803189481070320000024084c040c400d68040d003107210740c3d6511140742d0442514020041510359080031824542140c8104000782e0240b240138031150300050281040701c0e00b0680201c407103901c8010082c0c481e400c3c0300311084250542c1e45005440010480040090200702e4201c0e072507140b460101301d201c4400ca40380900213600060941000900b2071269611668000c9005000000c5103500c036030219007240d02000600080c0c0303c0107102007095951000c00015400020009010304480b4070b80642c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 835431654 1106 835430548 835430567
    0x2041e030302071a07060f0b04092a0b091905030d03062112080406110f030f1605070f170a0302030a0501080321040c1205100f0c 57
    0x2a558441403506000041000ca030706241217155981c01000b00300460364940050b643d500e070058240c4075480741c80c1c130140c814000c4052803600081ea4201702c8980a404e1202e07103004003024450b540a1509640030b05c002035508150000c1da4049114803551241c200c0c94061041e038511091b0309506410800455002d00050840203000c0c0451000c66400050003030040c0c0f4100c030f00c5030800b07403080c00050317130040c0184800140c4042e224050040c9038403412401729115404030620089848a00300300b81c108090300e500c000c4a50501c800a0f1243c06003c0000d0407120300103030400e0038032030340d511201e0801c821380034155034807080b400c0003500030740080d140800340c90719000010600940020898504072080d0f14078a0202a0003c400441d040313000b042283c1c1c041146000280f1082100c051092103840740c5c000d00700030f082d0840b01c4812609602180000b0904000b54600b280350840440b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 835251798 835431654 := by
  have h0 := BRFrame.cov_init 835251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 835251798 ≤ n) (h2 : n < 835431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
