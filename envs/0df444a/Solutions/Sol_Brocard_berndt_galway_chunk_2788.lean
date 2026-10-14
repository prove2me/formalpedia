-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2788
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:44:47.779529+00:00
-- url     : https://prove2.me/submissions/f3c15e3f-ff62-45b4-9cc6-cbbeee4c28cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 501258992 ≤ n < 501438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 501260242 1250 501258992 501259013
    0x3060e011d06131e0e0105010b0a0f030c0504170105060102011a0109120c0b121506040311091009020a02010e0d021615092706050402030106140304020a09090506070e0906010507 78
    0x10350203600d58900110160b10b200d036840d0608042e060010340110314800c07036804d445061b48840103061080040c050ac05611135551000e041c2c00341400b09440c265140204c0e01c0d48075a62000400e03140180d0501c00840064001e64001c00b02640240001c1102d21640b04041041612290125074126001c1103002140691450024011801002c2d81c0d503480d00045180d5101c01c1d000001c40c1104001c101c6181c0780004030884d0707410b0a44c4d0442c2858159502c101c0d440000500381d511480114000070912004003507582c000d0300d000d10040d51107e50f8003030b011740a404108107204c2c8500842e0000c054080c4006160139a00007044110b02d805890b18840060255444603040304110140f6004121142248980c0c039003803940c4041d039005070038404500c02c1220095000b1a10460040004003c8698030a40070746010015060721642c1c0d0f201c91000481816a5900080c3c0031420124000709000004c038401c1c0c464010b9840f100c1100d1034403c2041420307401182c1d03042c0469018001c80c07001c0b820015a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 501261492 1250 501260242 501260269
    0xc0405090615030f180a03090e130c080106050102071a12090109050d081807061202130f0308030403110a05071202180c030105040e010b10140d060603060e011d06 71
    0x42c2032039018880c036440302550040f10054629802d14042c014100150070f04000980381c0c0b180a02150340c02680c0080100540b40f00e04094038031240301040c070340b01c14a01d01408141c1d0000f204041d0343d0392400007501911580c8500380c0540100300000545400b0034440341d0b690440085a286406a40090340d0844040500940340d150740c1c90381e2020008808000c0080c2464458642c00300510700132051010000b1641c5a413a0690000d0384100301c005d4004404041c0a9002e803c00b607202c40380212050107000b8150b1001c052071031011000000d2110407001140924043d03620010b0030041c03408610f44e40e000b00480184107a1007d10100301c42c1e4405a034a0b001c0b544000e080c440c42d0002c100d000445008140d80700e40420100100401031032600d07101d040680441d5100901080200900161511003086e8510f000d005c0780980b00c58460884900301c940351000e11904000e000d0300d52000800405903401501c49200748000085030f01c405041c001c108401b01030400c1d01695540340141b00d11100d80c8072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 501262742 1250 501261492 501261499
    0x7090522050a0f0f021c02010c1101020c030124050307150e011b03030501091d0a020d0303090510060317030609130203010e030412120f0801090e1009080702090606030c04050906 78
    0x1c1a030000492040310168028011850092800260300400c02c60081d120b041b0310410b5820b4550702c0050341c1004510501d203401042c00564074000300010307410300d00c083d0702003585075227419106840d002d000100182e400d000d0444030030350a44c03580245681c5030f1080c0164001010465505075580340714400c5190307802c00602d0660040048400e100c80d0385c516541d01103005c01d45a00050220b01c0f950300c2040c20b0405400060242256080000f84d182ea007800006400b420000c6881130a0600a4119109650b48241140d0f6402800d40c41d1400400d141d00044908252400c06080b20160a40540303010300001841450b42e501d84107070030000e810004100b01c1e090b549641400c450144244040c00060941c00e603410711151a40c41e0071603130001c40380811800c2c00700c10078034442c44a500401003815200c1144c000100d185900c040145006204644100610308080d070403020000090080c1064074421364160907540c54100c1046150b020454581101d0081484108200e140c0b54bea050342115024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 501263992 1250 501262742 501262753
    0x40605010b0f07110d060f0b190f0302090406140f040b100f1211030106060207090e01050f01050d141c080a050106050d11041a070c0f0605030a05181c020709052205 72
    0x755901b1055803650070707400806c680e94100c081004d0074203c50302442c1d42c031040180d1407601d042905004a110490001034052901e990014040001c1daa00c40b4514901009801d24689000011b281500104580854590001c00003040c0b6041205021200355a0940340c00340911b800c11142c118041034046003900c40c0383c1081d03612122501d0a2250740301420301c40e8041e08000342070800140540d8201580603180f6850305c0308010300100c8454825041d110300301d50348105690241091030540700c1c0008010203900a411110120303003180c417103140751600551181d0425985e402d002c030084860900c250004034404000c0c070140311085a2101c24003806065156040a480d05e4540001e50780071071081000c0341d0b000421800b401001000d01c4002c01d00580054040c03402c1020090041c0805848c0c005516101d001140b400d01c00c030024031800c8040007040f940052011001030038176194a1942c107026020708040441c031001c0764000c49120702d030039100b1011410f0316403855907100c0c441450180c4060142 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 501265242 1250 501263992 501264019
    0xf06120307120e040606180510210b1206041208070201292b0303020304140102120a06090603080306060a02030910030c12091a090111070308040605010b0f0711 70
    0x80c03100c01c40441c02c555a0b40b107640c0c440901407004444003900408140403090304008614880e50b10305609484040c0c4008050032030480090714290000000411441d044444501050090b0340c80051020070484a40a02210000d0490b843e01c074180c6002d444801c5049203078038014001c25985801a201d41700001d4001ca010105001c030022800c004105078030003440340b9010746008504107038803150031601c401202d1130a0040080040d01d018008041c150044000b8007403201d5580015071304219140295a0703100d104024200e04141116840d4110346091400704040b4282d02c0303404140c030b6000341d65514540b2030b80200042d43d04550503407030441c481002100490346038020540e5010b481d5480210b0045101a0050b1180441e100d0f01a5010315003912080402c1e00280c203510b20000c00300400140d5120003060b40c1c050240c641e003410812a0004000d410568440441c61240c0d0240c1010000b50762602020991031003000c1480300744c500140a24004105141a0380c03010100007003207250108032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 501266492 1250 501265242 501265253
    0x151503010c0c0c080303090d11070f03121101020316031e0e1509010219110f0615041a06250f030c0b1b0a0318020603090607090e0f06120307 62
    0x88882410740061101c803040400c010b503a2404602500400d0040c504600c3c2c1002c250b039a0301c40e42d140c40d80800c1200d01e081c8181100504c002c0d40503014042c169403281d9182d00300700d025448040f0700714000036040082030864984c10310940f80141c1c0c0000c890100840d880350102c000d403c18101c04800d9680344000608050600d100740c030031100384400070300040d071203402812550360401000090540d0040110309040716036200c00248020fa0b5060505003030400d00c0740c09144c1030b40035140f0310280c4105000e01c00c5c15036560b48029455002150300f40815540c2c61100d0001d00f02c10061947c014405124020400480040000300d04000301c0613241007a800361200d0700c110071020420303408610742e0040303082807100f0984c2c080c2d40050f40c805407030030040f450404c0e89518032848403000c041581e144002d03840402c06e0084108034a0b00148074980383d0900b0703000d281e11640d05460107008100b01d00f50000305c0b141c04001e001d100302584046a000ca690f034205009140100c0b40c0391240c5404104000e00001d42c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 501267742 1250 501266492 501266501
    0x1e0705132a020d09060905150705071e170c060322080d0b040b0d080d0609050108100c020d0509061612170108150412090312030b1e0315150301 63
    0x79114101e00a22070901c0318040e00300080c1c456481c04000140805100749604071645c14201c0e90140c03400102c544400e0314030300c40c0e4080d05900400c5e23030040502c000b070141d80500b11014108901e0141c200030a95078100d030a4561a9080403040e030340c20240040324240f4010000d15402252004800d02c0030b01000c000c2000511010021158200042114400d88005200c1e044442c40c0c01d603410000303000c40d040040c69114000c20014456140001c41e21100034554000b2001032803140381c02e1144e540c449900035159585c0d10542e074041440c10038074103409480040e810b60846240d4940c00d10b41000c950900c4060350142110b07540007598040740300005048192100000b44c800d07940c000307028080e21582e424207001070b440501c550b48004466800c0d50280c010305a00700354002480d481c201c000300d605403201c160384d5102404060200d983e1103026501504034a80c02d2200320b561400c9150112888640100c00e102c2098044d888a002c449455900d58425504400d00c100e400d00580b180b04000390a45 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 501268992 1250 501267742 501267791
    0x2060702030a03091d13150e0a030903140705060f070203030910200f1207050a020604030302100509070f0302010f02010f02040f03020f0303210711060f091e070513 72
    0x10355039001c104a080d6a070000707110f112441001400e842d046c44480301900b058000d40c058a0040c07041052003001c0860381c48800343d2101e48007a980d44100e24180540b01540310700c02900c0c2c440180709504820000031a005054a0005080030700f0320a03004400d520503040010300701d806d88401c2100488580d10307240e00100d0050107585d4075262042d200c69000301c3c0c80c101007480509522550840040c070313a0224107020103074034080c141a11580c046c1030492a1800384040030750010000039002c001e150307011a02c510710140b10b0005000e10b44541020715901c107103911944400c040a14818401584100c2004205680c41c1c4004180c2e4181c2211200032039100758448001641d8070f040c200704500f0001c50030201140d046001d907040c0b0140d5102404445081031800340164204c5c3c0001c0ca4040c007032052200b000810720100c5000d1702e001025404002c0d001c0d41d07441103e20640444441c40642e4080c0f240181d5000c10141c48040c2c900f0090000c4042e81d81c442c6198103403510745481404004644d1a00b04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 501270242 1250 501268992 501268997
    0x3060b16030f020d020309011b0209040f051509060f0702030c1006090f090c140102030705010f090c080319080c0d110301140105030405060f0c0c0d031a191202060702030a03 76
    0x40306480d1074081c00811104440c101950800c0a4001c1043c0d00801914440602030900110f031824400b00e040645205e0b04e4000d5000355084144010321040801003030000d841502141d01c00112a50202c80e1010700b112840c4003944480c0010380c280c0d0b0740400054002080317004690a00900418540c03c04011442c1c00d0314060360b0f80380400c100c00c105d01075000400742c2d03150200481d88840d00c41c80044580d42c081c400f8024004030030804140d20800480d505550010001c00086040345a010041c04ca0400250740d040540180402c2e441300100845a05030340c8a10110b80110343d02600f601c0908000700414121b0301c05204100041d049070040c031012400071043c103035480d03040c56240c2c400d0f4440102911704100d82403080000241002a4190b0041000e4210519503a14145da002052049041205807800741000e1240b0aa4254000d9458071440c1801000504895414480c40a23202000c041d0b400c0b006080400000b54103580782c00c1500e0001e00440e01c0e2882c40d4003c00c0c5040d8080808400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 501271492 1250 501270242 501270277
    0x150905090d031a0102030f130e0f0412030e060f071803030203070c150504030609060609090501050915090c040902060409060f060207150503010b031003060c170f01030309120303060b 80
    0x400940c107110386039031400340d0401483c02200060000350b036070043c0e852006241ca00050351040680d4104550780081c4405000c01400386031601078542c0c521400d8500b106d01042e05198100d5281c000d0141c4040410300d03c0041c0b4069441c0c00550300403440140040080c010164032190207214140c90030300c083c50181c0c0085a80d5140ca2404145e8150168010350409400d040b0408005501c18100c0f0201d0b07401c900c000c201c00046040c82d6000788400c0e440b81780c07203920700240d00040100c19088240b10380241e0050b00e021a002a140242c4e08004803520480c0380c21100f00200c0a240c0399120301c0c01c0034000350400381855262905501100c201c0c1e000750301000c126000802c565941000703d80058280d001680043c4444100f01901c03030f02060003410603080020000032100c1c204c5008940003142c22120904c01203410480141004130701d00c1e4411104c04c0018001250345903a000c1103412a54942e0b60408a030703240400e42c580d0f03401068801c41c01c05440340d070f000400c1010180900180014020000c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 501272742 1250 501271492 501271513
    0xf0c1a12010e1b030a0e03030a060e0a0902091f1a03010302120d050a050c0f250e090c090705190918051902091302070f03090b030906010302010315090509 68
    0x8520346016481801186510000c00c68001458081900c0540c081c01440d6140c1e02c0349002d0750040c1644800300c030901e102c0407080202401c0145c010341c00321107922441d0001500c412941c801a41c9141b00c008c3c0d00015030201040c0034040440c0c0b041644440441c12001240d1940d61595182d0307030101070b001d10040040700602c1580b0f08044500100170401c401000c0380600c80c80041d0090107a40e81400c01d00c00c02103540c1d590303801d0502802141030f80402c2030324003d803001d21140c1c00c002c0e004082c880345030300e80b0380011a010f2180d4030000c1c0103460500c01403031124205000c009010384000c1030b040400106000c8158140054042d0442c080380325110702d10890f0500b0005403110444000c5104101d0500d028030102000b1100c0ca07108260303104201613910f50b000c001041960046e01c50b000c50340341c80010400c05003d1038804200c01d445c03182c0e07a80000d0658624007203155000580d0b000c000d40e000a0010001580a9402071005444943c4e4000c100d65894070100d048420840300c1500b1078010b12882c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 501273992 1250 501272742 501272767
    0xc030b09010e07300212060106020106230907020c090f06010e01080408031302060c101a030c03060a0f11280206070e0f042a030c03180f0c1a 62
    0x149140c2d4080d0007404240d00c0e05442505281c0c00380d400ca044003204070009002000307000d40d001400342d00508448503800640c0c40440d0b84170707824411640107500e00240400c021507031080e0100d8403e400c0c04040b114410490070082c00d40c40281c10b007400d6200e81c04618210751103014080b403107041ca0340700441c000d142110002d840c0b2486080310780d04004000301008009075801080c3c903002070380d0100340405004a440410220711031802000c120388180c20031020603071025004040c40b081c140d448000b4203102c14081c075903110200f0b0390aa5064000707100185031800d041d8000030740c1031115103001c01c1908889407102d00c41d600914643e1079540c08034039400050510805c0071050200684000d04040ca080d02008000d48005001c1901c03441c5580e190621030354490300192036030000840c1c0750030100c12090f45003100e648003421240210b8105150241c1041c0640719541c501348051310040306103289030380c40072500034901a08880300056080041b6080340f001d40401d85c80c01d503c404041d80c848594600303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 501275242 1250 501273992 501274001
    0x403030306090c050409021c050903180f0325030f0c05280b0903030f0d140a060f120201050d090501020421120c0309080a050601060801090c0f0e0d0c030b0901 70
    0x207140128182083d44404a034490111012182c2c0c0400c0103072078000320030300070350121007401e41400c1c0c403424a0b0a000c1c1200000c801014aa00e03144080003c9141100921100c0d0900a121a40c141c0008020301507008035004050355503400c0e81a40b00005446c1d03a2056524800880180c44c441c1034004144039a08000c0881c0c13648101d00e200c0400c61740b0844900d4005212940035600346a0004208210745440400984100d583c907144100c1d101d8102c04020001441d0554444241c0f40e6090042003408540e403144c1b10580e588041c8a888107070a080c440d41401d000000102d0402c00704005452143d0010703c110b620036440381d000076a4a518040c0c0031080e0b001c414000b20071212458a02400090200ea0010f001e0516400e08000c0500a8101a1401610b030f9000450500640d40d010003080f0300820b04605031081529550b4840c1d89505003201160554003904000c61201520468454014039040e102040001c003c0240c1c0003c0d6940c00c1e01016880d80b0440e001100c00b03061201c240070a004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 501276492 1250 501275242 501275249
    0x30306060e0d022206080309030606100f0804020a080607020601050a050111150a1112010503010f1a13022a010605010203090d060504230307020307150c20150403030306 74
    0x1001000010018000345001665a0b4000e102c1e0619165201100b1101c00c01014118203002007082550f503a00d0800d52250710040c0d4252103801001c00041280c54030812552004103e591101c2c0761214a0340203440c0744001400c1a684500e00070400690742104108007846039120398050946945084c0c10b018a0482c1a0882d41c1402807800f00b4580603000003640c0c2121a94003034130681252100c0d41140e009100300c410f80c006054001038001392005460480b10304135407003a802046400b80c501d0202040341c240c5003443c071004100c500000600c0c50015180c080d1b0400c070340700040c5000d054020007600341404042c08042807180c8154111564000e104200c02413100f80060352078a03030700301c2c00644203010494004164a949002040a002d4210300604128140018081b0040003054580703549820500080303200340300b4548007050496000380c1e0b003400c50100b03881f80c0b0600303242569000c070105820840d41d003031074009100405040d502d4818024030804030502d203982d12401c500f002020f80310a82c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 501277742 1250 501276492 501276497
    0x60106110312180a08070302061e04080a0e062d0403050d110f060c040e090d050901030f020903060f011a030601360608090d0c0f0609030908030a02010903030606 71
    0x10003656000d5408401c5030b02e80c125401d90055541d45903190b14180c01812003c0c40d05502c2003040351400c001d9000c00408040b80603030211050390380d501043c03201844000e8007040c06070307a0003404500010900405000250100d00704441175664031400704400390803c41901048003022240207141c4c115100c020000005480c08861401d42142c59903603481d90381003050020013491074090691024140101002d944250080d5481c03420030031100302594015002c0d100503000d4920208403a2100040e20b490312802540700c1508000c3c0c1000154020100020b41c0c41d900d940810040c1090fa4050100500c00c1d0b80d4035048000e2f40d4101b240b5000110100c003400c6003110350400600c10183e8000d00301203200526031001c0e030b246d03e00912005050310081445c0804800307541d04041075058018218902c82c0c4441b03800c43d0700c040801c180444907070101c2c410182c0512100c07170180e00490800c1e0081a0f0180c0241448048503a41d1100c15186034000b4840b540181d40d500406010103a250142d00010086032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 501278992 1250 501277742 501277757
    0x29040b090c04030b0c0f0d05070f170109020306130f0914070608221203050a0e01020a1430040209150f0d0309051009091b05070809130207080c060106 66
    0x960081e4002d110714080980400484000500401215000c8400d0200800312060b103e180b00032121001c0c04003540c518002c642d401c039020361814401c2601c19041074141014000d9a441c11044c407000b54005442503800100d07070001c0c1c080007a07290003405030800c0584070024030740c00c06041008501c10389500703004c80c87d0480d203003c1000540c015515a000a000c00381130844501c0410340d42640f02c1a02130040c003050080040001c0c40d5015801940b048218200920600e144500024201c0c49840080b202040e44c400e51821072041c1c103005086807603040d500501e071114510004805d452030404c120107182002508120460508190391358100d0028024040044240b20010306444803000c0341e64020390b40e1076140c60038140f1529548000700301c054825910014044d0f401058502070340150701000e42800c070000a258416151905c0d01e02540c0e442e0781c01c065403569280d2090380500141944640d00146002c03943e4254801080c440d440f640074195030725210084141040c5050303001300c0501c41034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 501280242 1250 501278992 501279001
    0x902130f0f0b07120203070f0f0b1b0a031a030102070f111f0305090a21020f06060a0b0d0207061a0f040605100f110f0a03140a09060e01020129040b09 66
    0x1800945411030313031007006a00700d00e407031490480c82d50050344009082d802c40004038000380300075108011078075030041d000c9072059914140301ea540502742d25800d61400b04100080800140f1035445540041c0d610342d4880070400c0c3d020006802c0e83c01c84502a00d0540201220340200690046010250041519103c2d525414465030151031b1115504003414151214001800b40c8004e0103070221103a40071120007508030342e02c0561400d8111103070011000d823003050b403042042d43c00000d44e0b900c14107004165264190810803451002e4000b00342101855809011820009010b400b855503100307000344a05414100304001c201403056981078060007645080000d20042e00d44403441080340c2d03181c0c200f030b00030b40d6540c07001110040414031a561590040f940b840160001c0491f15010f4a03021f0342d02c949038420391918422052066440c507038080307140d80070200071107801a400c2d10410300c0140000200d210100d442d10030b009a0195400c0c0c8943d40390b5074201680d24082c40765a1580350305403007034081440c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 501281492 1250 501280242 501280259
    0x160306051c020d050f010b18010f0605070f0c0602010f0b2d060705030705101508060f0c0906070507091808090904080f0f0304110d0b0a150902130f0f 66
    0x40d400c03070150061206001c05030554595455540c00c0c5984101103541c0485407841311402400e031003091610400c2141d01140710034084030f521074144e44441c00ba090ba0680f030b04105480680c00b05d4000c5510050b088481c101240710203080b08002c00781d070307000413641d010101000301c116800441020312560100e03182aaa550388601203128014030600d0030545000440000b4409024203400100144000100c0008104012a20313125090703c0d1503041c80300e540f001c003068200d14554043c1101c03e900c62000241e1134101000041d4120464a0000d8509902900800c43c40e81c0100380995690b4400c8004200190b030501ca000380f06625548206108445582c0c1c0301100e102d4452202d10912954000c1014810113070102e5440300c0d12485416600c00d105c04540c2030356001250161905c103c280c0011b01c0d0350900046d2112400e6006d503801105079030300c5e06070000808200507003103041600c603580401c0000c0a4402018910300c1808455605450b0050308030000d25947c00010201034600380030409c840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 501282742 1250 501281492 501281509
    0x602120304031704061503150608010606050a0e0109090c081b0309030414030705090f0103052b030f0b2205010b2d070b01240c030801090e07050901080616030605 71
    0x103064451607240303407200c5c10801e02401004011920000f00c0c070340004200141c00e03c036840d540740c1e05031080c058165141c900c50f080b11801e01c03504000c07840030850b140d0801c0c400c1d418000c8101c814145648040c4e00c8d204504122161440300700c0110b41310138140102c0003000e0f041304000100440070140782d403070080f81240d00e03409203118801c0c1d489540c5114800b582d600340543e0002d0070019044aa8900e04505080c07070105080c4025241400f4503813681c99001044040c141c14042c1c00b4843e42c003150b90300201100103020311a90240702c1e5995400d45041a911241d01e480450390440c000c039038451044922008030b42043c0c0c0050544c070010072001d035035882000c043c10207038080c50b210590707820ba0001048082d48160100101203880850000c1a080c40c4008298076000d55820043c0041c0404402502c0808a03460007a0110780e01d51700401001b00141c00c4121003001c4041901e0820741c0c4d610200d040740000781c2140d000c0d604034400b0090768402e4090550443c254030300d001c1c44460b16080c00700d108034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 501283992 1250 501282742 501282767
    0x6040507090b09010207091419090203060f0604020d0905010f14040f0201031d120703030605062b0902060c0109020f0d03080a020a0c0503070c090501120203100507030b030d0801060212030403 84
    0x2100040f40d002000d038028440f040050004200c01d0003000243c9034240b4802d80f00b124a05035183c8810920300e1401464070070701b400d00d64058014509070301c0d08128017240003401080e041d401a001c0020806c414094001d10306d13541c5c4a0b1001080424400035600c0a48140782d402c0c4003000d04a00030400442e202d044030501041d02070800045043e521042407100894110101c0500e04c900c4001c0038116103500300502d0914001c0c1c0d0104001502c07503042184d10301c5442e060320f007401401310341c0407249503e042501401c0800000001422030fa00d501181041e088002c032100301d65075800b003100650800740c25410201c04112841901e0a01d03590b03018250304006040300358065804180380410701d00500401c20081d820800f260b0301c4002500d00510041418016a004d05060000028100008610480c81d0640c018081d001128200748100010f20006011008141d1580651409600d051080c04d00b405190340d90f40e450340d0f06100001e4606a080020b4101c000c038200100700110b5440039154030007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 501285242 1250 501283992 501284009
    0x9090a080f1305120f1524190303050919030209130512030412020f010209060405150d0203010b0d1a01081f050603090c010e0406030b06090a0f060b0405090604050709 73
    0xd4551000074045088065003005410054912640c4a04100040c0740000d40b5011802c880e41d1000c6d420364000e617540c090310018040784c19405814400c45054004e0310300104003a02c407405143c1c07105d00b4090220100e0b4070542c04504001456901c9042441d181e09246060066600c1c7c01491a4040b415490004010204a109031f01c2c024007042010b1044204001c00c985905490b400d0605100700a030170102100000b500c1240151542c400c03040c001d542c0100030003003081d814186440705000d010070351010480c46152080040c1050f0f0744072440514040d0251813145900c650201010400729098411070741d603521404409110280e0707000312929400707044140d0781d1a80d03031400c407400f0741d0400702a00075960001020080124020000605103140304c000d0b62400d1180788100c0c2400100c80050201030901c8070382a000840c0382c1001d4042c542c2040100b03400107a1420305241c04000c542081d0042001580005000c0250303141104081e500260300311410407243c2800000a841200c0e984166800d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 501286492 1250 501285242 501285247
    0xb0301090515100b0301170105130c05040c0219060b03060112080d020d18080901170405060115020708100c031109030c0f03010f06091506170109050a0906020a030b09090a080f 77
    0x40b6400c80c0d9520f000101078101d0741d143c5958561116001e1401010000704140d0318000003d48030600182c5100c04107038000c0c41d1a0b104900348800d00001e081c121849805500c14001c1e0f225030f4030740080c80031034218020a000280d0b03445003c20942085810b07401842181d41060700100810001011242864a0840b005941da00d51842c050301404c02c002c9a91600709400c110581400300101c014031005000341d98100c10000d032072504d0814480150f0b00070340154801c038014030413510f605140c042c0310003041c011201e40c65695800c90385031400074881f542ca040c1d160f0942071381c0030307170540255046960983d0420381001d5807800030130341d20003030000003520a0806a040318080e403020362100303e01c0041002c0074060075071a041172201420030303c10700b0010403028540004840e0703c103034040c1000201d1030100139074591070203110f84081c00000c0d14001c8180e03694080c0c0030001e1070610080000c04040d807000304041d460f9804004001c0340040c0040c0d0244c204002d1070000030070b03445c01c44644a48000c2e1a68 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 501287742 1250 501286492 501286501
    0x31404061407031218260f09011106090714090601050a0c030905040e03120f060a06030e2d010c0203090d150e0f100b030a0b0f0a0f02030115030b0301090515 69
    0x4924000320520010051701d001640a0032842c82c1954003000c5028002e1000304140820341090001e0403040603202014050002080c0341c40c00700000c0c6844101450004180c00074000c0e01410030b941a94509031a80c05240c003040180c5c800025952503540c100e42e03c451914151001038090710a0780c0c0e20300304100e01441c0315000c00d0b00421080024000103002000102e80c002410360b5258011120060070808050000782c02105203a1807610603903010300201c010798a8484103030080c1960140070041406042e05100103001c05c040802c0003000442c0c568110044601007103421282e01c402c400c402c40d0801c20241c60aa181d0a1003a607000d1380c000110031084010358212401003503140c3c0520320b98060404685143d0344001882c69000c010900200702d0b0340000c00415a030381b200450010444038a00e00024410500b140e011540907801c9074002c2680004060500200e074000d8000080c200c8642481d446441c0e45886a030502041c01e400800148006886807540ca0044c004a122075100050024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 501288992 1250 501287742 501287747
    0x30206070b1806011e09051e04060b060f19090506040b0c0a080f0a0f0801030b0f0603100f15170705151207050301050f03160b160c080a03140406140703 67
    0x5442c1c20ba004042e200503584580c503a1422200251000c02480c82809000c50201140c0c03140a004503c0751007198825154a00607401c1c419000700150388955980052a915864490007845641e804031005599500503040001610810242240c2040084941440507880e110101d8017036603184c100a50321920030b840301c5450007003124001030035018007150310b80310458024050a07824000740c440c41050f407881e400072104c0034024071010b000c005409000c5816400340c10105a04407030050309031503010f1305400c464010760304c43c03050000101d995554030786846140d040d100809410140c0001103403600703000e54070343e843d00320340219480b07188408405c02240e460b641c100d03080c8201c0180e0401c41c03071130580b0025105800900c22103009040e0054180300d01d01e00030030f80360712800c400c1504400c11820004620300a4104003005841c156001001038040340715486050000c2c0001030080507044543e1400904466040c90103071482c48040c00305004294110107035a45031002c800e8030300d45030241800c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 501290242 1250 501288992 501289021
    0x190209011d0f06041e1502121c0504140d05090d020906030a0203101e020715050a06090e0a060b0303190804150e0a050f070b04030b091e0a050d0306030206070b 70
    0x800d611500c001800140d5000c00101807280c0d880705801011741c01e40c0d400054040d6419100010016001007c400c0720907680b4001030078080301004c0c1d20342e03140d514030003440c2d003111020f0b90b00741c5550381c0d80742c10300b04c0307040d8100400c54a0b00316624100d400c0030790030008101d2200300c1920091044842500240258804100300c0b40c031150010301321521500580c080740014460002d803000002010740c00441a00010300031a440554030180340e00d00c00c2800442000104009444661140e0300d0301400182c00005006441c843c00c2012702520b4030780050714040013111015030b03940d4001e0708103005442c552004006c82010070051801c0a804999962522000032048464218580c42c0740503414907081200285034030b4418400c80403600074208007840b060713450030345229503050800108000e00004074141912900541804203c0b081007111064031b000980c42062880c0c10360303003e400030000b4420104034962060045040070418503086030007250083c8281c1350081c06400c0f281300480e20000350b6404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 501291492 1250 501290242 501290269
    0xc181e051203090301020a0503010305010e071a0c0703081903051b0f0d2304230c0f0d15050f0f010f050d0f02030703080903010c0302030c0403030e150a0305190209011d 74
    0x7150b5400c1c47d200080c0032030300203000507150b41d0300e045140e8031101030016121003034890f545481e06140d111005501c14039031011b40c00da8554080c00c04000009080720780600044005000340c80401004084018101d480040c031554a00038080809082d60000608664510741c4400c4000e5a800c3c0c1c0791044005010ba0f008030310122040c01500300d0007481c501e00082d0103188241c0e1003404800c030ba90711142c840b04034602c500c88550000e2065032258500948650f10210002d0076480c0070740742075184d00c8a241610321030704014a450301d040226801200385042d0b0f00ca0301c2c400e6108102e50421034a0f01c0e2092042c05410f00801d01a10710200b801407100c02e82503060b900a0803a030965849190410b60ba03004400d41502a41c20103000c1300000e4024000c0d02d2045900501940c101403850f1000c42e5841d40c6503041c0ca80000003a2024056111b007000200201c2500d5140403c403414940120702460740020440c44d0424030500880700075070380c0700c90001344080c4480c0c541c2c0b120014800c0020041207c044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 501292742 1250 501291492 501291499
    0x8030c0715052e0611071a03060307060c110904020f0d0609020f01170f0705130801020c0d030b01050a3b0306090111040b07080d0c181e05120309 64
    0x1001c40030441d1160700300b180314040c50020811a003849145a0784080c22050b12011091000700040c0300441c810198412110401c2040b14446943c400c0b8406110341c1c1200141c43ca898000100700c031604042001600401081c50080031705486a1100e03950307d40c00301c0509208038400b0012405554500c480d080702c0040080002d8840a000c0c030b0611300920010404030b020707641c1c00c80041119070045c0103a4000744089a0030b02070039620305904c00840d49000b001c6030103003d414000c02c10072404c011185405005410001a078501000825031300e0103c0320b41807002054284024840780380d03444419504c48070141d0400c02416400100508401451032000c0014a101182c4a001350f81390100001c500b050144c041d150f251b1903848915017601e844200d00b00c41c0030002c10003080056615001010001c1c01400e00c2c0d41880042203070b18007903802d10500800080c81e6000c00d0348604000a811100600300b5100505080c0101086211005000d21031144a12006607a4040f1040203004491948074002e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 501293992 1250 501292742 501292763
    0x4180212031201030605330306010b09060f0708220f0504200a17090c15070c030b1f14011215120602040909060e070b0c33101a090d08030c07 62
    0x40c2e0080004032220400c18803a103d10327800001c0300020702007210704611000d0300040c03400d0900c0004140e00d50021004072041d510401420054002083c5a02c0010f2900030554505520b0184007403628440d03034004510a40c68441c4c040416062000c661290703041030400395448a40d5550103480c4c1c3c41c8040c00030300c1c0c1003480d08104140f0ba0300c00700301d22080860441d426020910070000030126402100c100800000802c06e080c804203426450f0b080e40911401034140500380081207840c8070300801d41c8a032007180030004100c4410342c5c2281c00c4a081001c2850304024150800d030765291015940d21500750b6800c10040c00c00244241031301280c003d803140c0801840250440d00c4d040c80100072030401c4000c42d00909002003000c07290300c401c031a00099000300400f4070503103004004030f56801d07280c51000d11407400440d5102e03204940c00c0f807611400d20f4615202105181a0b404902440c1d192503c1030409000c01c0404117039502c401a41070040c1e00004071948130341c0c1d8140d1030785442c41020b4000d400e0000c0f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 501295242 1250 501293992 501294061
    0xb0d060509060118021e0f0f16020411030906160201090c0e1008030c2a1c0b1b0d11040b1b1002070809040c0e04180212031201030605 59
    0xc800d81240c460310b81580d07180000c0b042d400700700c0c019407440d41a81d0300c0486e40018072603034020150407a000006031041ca0b140c041c0610405a601544c020210f022032014001c056242c40d104810021441845e00d07451854808411034965800402c1000000b1409803003405480c400d43c04255640d40c0240a56021521020f00b403c2c880d0003240c8e49144006100703c0820800c4000c0b042d1100c44000c00001c203c000302c1e5850142c07120451408841e4907100d81c0c83c05000700d5481c9190051009400e50510480c2e00b00742c140a03000380070080110001506c00300f1070603580c4044034210b911408548600048801c0b0700a5400c1041c4074a50144c00303055804a0041c000e020a66000b50b042801c200c12914000809400c0c501680902d44c0302920460741440300300030340d040075008503c6aa10b1860722039031000000780024200c42d0800d09a016038031038045c0b06000c5040184035100715002c0f4100a5042c41100125500242c1c0e0500009003410348070f5010503103c151a183c1a02d266a49028100c100d560 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 501296492 1250 501295242 501295261
    0xf050411031314070e04051606080f0c190e0405010b0c03040e090106090c0207230f0f030c0402360603130302160306020c01150b180d0204090b18120d0b0d0605 70
    0x4007941d095035103000303211408101d600103423030300c1080320b1381d9449024441e9190260a50035010040820300c001c80c0030800341080050001a00720f07481c1300e60f02c55401c1c80b1038080c184000c440c0140c00561600d0300030406076504002c00404e4030120f515490100480b80d0307550810038050000e030341c0056545070500781108002d503004280503003034403007a82900b242c02c0741d0303140d07155520b4a03c1201e403504025021640b800e40d0501c5880000b407000081d00300e50702000000c1c0803804a900c0070039103000000300b2200418081c910402c82015070040e250075000d10701007040010b1003e11024014451343e106840408040500922003003101c0006103150140c91a035a08006000e58407031481082554a002044102607540888450940710300d2000c0380c3c2000c1030441c425920410203610740c0c0d4007240030701c0c260005030341c0d41c000c1603801c0c0d11462400034079003440840c1c030602d656598400c00c12504020307140418000e030794064034455907103e140415100880c001140350440c0450001d08003504000c200600c0d00c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 501297742 1250 501296492 501296519
    0x307320904021e04080738070201050c0d02100b27060d0c030b04030f0305070e010305100b0d0902040501081b0d1401091b05180c0c0118030201060f05041103131407 72
    0x31050954008080b549040b20002101941c03d510b8800f040088500b4847c0c40100c060465144181011440c1075480f06d00b41c0e107048500d11982c0010781c48044440403240c0c25009201c002101914a449820300d80700040c20728030382081e0686c08490300c180015087e0340c0d82c0d603010b00d8241c3d040b000b2082c013142caa0601c41d209590840f01035000c29610301109403054030030311895109104a9841036460f008150046010300f00203070040b4103400c0884004a04202d1860007440d20310b08800b00051014114814802510016400007400d031300310840441d40415440b0300174144840440d41d640b0711000c989407a0f00701034072101c00c1d44855864118ec46082081c07503403c061a0300c20104111420b2551041003000c05c1481074030313224052a00c5000309030740c0104080600041010b80c000820040800d0345000d00e0045c0005065006070745071641044901010386c001800345c803054605004000c84166104403500c4060a4030000d100f1820b091001e101c0f030030a00c59040078442c405d0781c080303552f102c0380c910410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 501298992 1250 501297742 501297749
    0x1050a15170438060a0501020c2e0e0a082b05071707150c0c031107080a080a0e0a0b0a180e0a2316180801020307320904021e040807 58
    0x10114000402c4c40340c40c18075508000c49030140e0040c00c540c0301d10800c0c40740071b03c020600c0f40c0200001d40b000c2e4200742c0f40c00c0d290504e1003010359550302d01d5400d000c040089190056104564641001c0c440c48644000c44922503c0143d2000326040100f81803241242c0c248030750000a448600821a501c000e030130044010652540034000030b00c8403903031402030035040300c66280365880495401006140024060304503201c080c00658241c03085190703141d24841c10101801300440340e200c400a5020803594102809079200c48003503c0d0001510b01b000c102e640c4a110b480a541e052152108013030340c906104021a001403c81c0210100090030003c3c41d1001625141035000c2d403400034019032000030040c00950520541000645003240642041e056445002d51b1010700700b9100802404200203200b40003c40c0100c8150f51910b8005640e004207103280c050003040d070000484140300d0045c03000c0c0c9150980d11140002c450060ba219014428480c0140c0c0c507103070340c0301e246002050000d84c100d00400c424044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 501300242 1250 501298992 501299093
    0x30c0f04091a01020f0606120f06180607030c0f08150a030507051212040905100801050906010f080d021f060302040906020408010b0a150f032301050a151704 69
    0x10000d004005989070b000d404245d0050f0341c003032000290103241c05540001e007010002e0903103060380510504c1078207013001242c80701c0400010005d18080008100007a50303000b409464100f1424850345401407416580c590003e0811403d00c002c284505510010310489000080ca510a010b031380307290540c2c55240b90301c40d4603c90b400200c6e8600340500040744550f20300c4a034000b02458a0f091240792401040003800c166803a0201d140e01081b82402442480e004007250001041e29605d801c0d0407140039502a00f2481e03040d0404220f5070303002600080d080101d80c0c500700c0c100c0c003c00e10749424000108510390000c2d61080c100244002171006903070050080e901e030340000340700301c500050074495961014030038203085c040d655094003910b81c0700f4418510402968600859200411030086440c82001c84070324500152400040065140c91031941c0000c1c0840d07294200307001c038034060262046030604030700002040518006420002d44041e02d90662015048d0313815071800101da5045210014203c0a94 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 501301492 1250 501300242 501300281
    0xa0320041d0a02010206100e0604020a030e0703060204262d07180b030105040302070608130c24030b06120411030708031818071b0b01300b0705030c0f0409 68
    0x1602c1c80c02c1c02003640c4e21000380074900c2e249c003020b10000303520802024080590700c0c00440c000c1d440034171000c00154091200940c0341d9043c132182d103e88103071060500b0107018181520304003101300840c4007444130306c4076210340c854908000b800138001c010681d907800c2e00f0301901501044030700441600c0b290b801428801000204440c90505089420548018015900c0480100920b0b449560150f42c44500d101100d150102980c1d502d80800d03000ba08070880444031201d88005007841c400c07403016a142c0030b01e8280a41d040c5540410000d114039845101001000310018050000b100325291400c600941141c0c409036668841c242c40e600807203418901085013441180541c50044c0d0a030900341c882d403035000105c0e00c1d1010b080d40d6400a00c08103200a0000c2100500404c078081c0815000f801e4524041c0f41a515410314250400c09500c1c41444200c1e140c042c0d10f01183c5000390f00c81c1c3c0700100d803d1103030356500c4140480340c150107440800c40c0700e20000500490600042e800220b00c1010032841c02c1e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 501302742 1250 501301492 501301501
    0x3011b03140906040b190e031c0c020d09150905150301030317010e0106050d2003150909030a0311120907030209010e040510110f0d0207030e0a0320041d0a02010206 72
    0x79160b00003610054110002d91021600003030200500c284020040c1c00300103103800079181f0351401c0d5003211041d41c51200744065000c2009545000d0f401c0700b41c010344090a010012508007400c0c8000304e000d4264101030302c405a40b0054050721210010300801007281c80801c2e04009060519442400228000380703002075496649032940501e04d05851802600b01c0c8580e0904101b11229080800000c6480c1d0b1102c140003483d002c6081d6000002e5a07100c006907480c9000041802806210100c050103450380c20b080008061000c006d80c0c2c24500640350105c0d8000d201c540440c0d80e40250080280c0c01040781c0e013030100e00d00b800030b200c1c030440e44247c400591030b1303980700008281090103d401406c1508002e0904070002020790010001c61640800142403a148000c80201d0b42c00c15044040c0c0150f00140000078903800c01c0804070340c2c1030103e07000c2c89814119035a0f22904480000140c25101c415542c400c81907032603030019190000b402d941d810556451002c0c9541e9122003240681c050f000b13460103e03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 501303992 1250 501302742 501302761
    0x308070515010b0708090d08070605150334170604060c11030711030712110406051c0b0703140a0c120c0e0f0a030c06020f011b1d03011b0314 62
    0x4038101c0d5400f200d01c1c0d09003243c5454030b007070310f900400e41240d00c0540d49a00c04000b807042c5000d0621180506800151407902c801009080614452040d220b60b01c100400340d91080034101c0d44070190710601c03041440d40c8c0c0311209020842026001403040442c14643c0104005000031120301c294001c032024003200504400595400b80000b641440c150002c1207130101050240d1800c401111028048441d030541c0e8000e0000182c007180411100140c00c25071700b20b00c0e8a1700d4003075100503040844165500b000c9210b107030030745605e184c1c1c4010111450381d0300062609000768007100740f2480d030a1140f009841c2121403030004003802c40b050740c045144858108011425440780c03e1003180c0540b5404942c2000c141080310380300c40d4080080c0d0201030441c010000442e0041030b0402031006400038900c00e0821b5040500359151103110608028000300c1440f40d0799848051044100e4004100c00c0c101c0b88420003090244c074440441c01000b180034000f219410303a250703200e0402c1c0215492122060780304e01211 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 501305242 1250 501303992 501304033
    0x3021e0a11240103020d020307030b09070305010b03030c06011710060909030807030b060f0705030903030703210905060703020702060c062701090f03030b06040911040501093f020a03080705 83
    0xb9110488424001400181030100032203480d140000d046500c1c4d40e94076600c000001d00103e466203015005102d0800400c03c0900401341501070490256040001032100c4039507aa605100c0c1a0f003029081d800c9502d50081405903000c07a0f120024180074083d00c846400700030340950700003213002480d81030004801c6480f82c0b0940b2000d120091049260400c400300007001c5401040003502d040c0000c02841c1e1060740e040006080041c826241d615417400340701800f111f046007103c0f804170202e080c0380800d030000d4808503080f54082d00c0c50400584031013445c000b04040c3e0055038400c01651041c40d0a0082802980c0c842d110480c001074607004003200d102c160b05007a00c5088000401c05181258100002806a007001c042c44034041c0071079040030354130000740090361440980c005410b400048c00b4006541d1090480000d01040100441808150b40e48030340c800303812081d41031051130300300a044012144492003055081e0028400c80c1403507141d0905d14410713401a50f04440340d00c00d28014881e010002e0a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 501306492 1250 501305242 501305293
    0xa12240509100c02100203090d1b050a20030a05010f0b041509051e010b0307021002070b070804060e01020f031005031c05030c070c08010b1201051603021e0a11 70
    0x107000b00d90000c12030380e8042c0c2001c0d42d074003055001d40c0031500386080062000c1c3d8403401c1e00400400c00c1072081a0060002e0000342e5810b40c141910502d014041980042c1203a4070310782c81603c1e011968050700b110350703010000c2071049a15000e1a94140144041500882240c8051040800002400c0020001105c4050080303228407a00301f00d0030000c103900c0342d1245501c042081c52010301502c90b0500034240403400d8000000041012040c441d0b6250304004040e100040518214074261440e228078544030001400c0070100078803400000c04100700c580141c4440038056000355151010100781810720780040307901070740c1584074140001c5c0310b160001e46907208682c0c1c0790760314480380c180d00307800c0b100340c1e100401d048150b210411084001400c105903881c01042170f00b000003007141c01c1ea801c00c0340110710b007444417039268105020300c10780c0c03240d2039101c90307407111179080040e40c80000c600c1900f851182e140c1c210b016004082820003210b600074000c0d0b4105448030007a1040303006120720660290415070b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 501307742 1250 501306492 501306511
    0x105061e0102072d0605030f0c040b390a05150f06121912080610080732090112060e0a0e01090512130617040209060a122405 55
    0x8420403114203001030114a140040c80301c4003013101c0501640c5240702030350b8094000620300000700081c02035503516031508010004849840c207490003018440500480d102029408800c004450994001c0d815480103611102410110703510000641e60301c0d8030b80712174261090f00440140030005103252000601c500402c2d40145501e8075030310284241428036052010722071180341c4c6443c04201d6070710b050a44080c4100d222549025400340002c149000141c501d50091080088101503141c00c46001d903807040d104d2600d01d500300c030090103c900361704e128000c1c1d0b120840e5443d481940c460380d410042881c40020388032100346404041c1000704a4416200b8043c0880d41c1c0000b080000c07241d50805c079110b106900011401c4459600c4403800d104408161400719800028851841004081c890008103013909003200d0860f612a0341d00074000000344024482c000200015007980d4030702c02e807100903000380302201581140038a411100341c180042d1300c190340700e0b034040c80f403242410034000d052080d403148 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 501308992 1250 501307742 501307753
    0x30f0d030b150d051009092604270e06040b0c0d02190207090b0109080303040f0204110703030f050112051c030f02160204050a020f0f0c0c0d03020105061e0102 70
    0x604046004000107100305900c01074012000380000e41c0341000d0040103440c020001001e0410001110201c146680013055003801c00700c202d404101282c148100c02401c0040d17828580c02d80a806100320700c140d800074002078503c1b01805d10300c802085058034000344421400c0010a60f6203a820395aa94101c4008001c07201e0000040c4140040d8400780001d0a0001c50242c00c02c1d100d040030703188106000c0015001607001ba0420890030b0f40500503c0361600c030a00303007840014100310016403648001040600480d40704c5e41064110340340c603400f580c0106405c40300e05888101f9482c001b000ba103449584102c03105e040000100e408170250706941440c660100040101c903401d240d1003001c0d10b8130b502d4a401032646d52000481c44140e580000d100c003008112100c2c1d42c082103807041008607000500300740300c0b562040c88403c4695202c1801c943e01c00031694240e98881c0540340c642441c0c484018602c2d900b04101d075407548105501500400d0003141c0032140f03000d041d16540c10f1043c40c050b44603a03450041c1c0c8003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 501310242 1250 501308992 501309013
    0xe03181f03020702031203010e060f01030507050409020f07060c0503072706080402010905120c030f032508041a0d0c0c020609060c15010605030709060807020d08061801091a030f 78
    0x1d9000f8403259101806441c901000b602c0d41c1d0341c550b0405d03480100d408041004224881c681b880009032801d409080801403418032000040caa4022409401d040581c0024124610b00b1158140c0721a1a0b2265040c0a00f224004d0000c06c00d820503038495001c0b03048541600060701690441c403045c3c03032100c007003900018500300b01100e4a25014006034180619004007160540311032041c501d459271500001d00514400c84249031401e070401c950407005070428802c440107122000c54103402c1d80c00940d030082d041285070801c0b01345841964840038140c54241c5100011085681c05000380c0302001c801040440d4000209a81c501d020090003035000b0000c1145201ca85401e002a00711800c01a0450710b09154104007464061001c3c2c200f9000314402000b008030059002e0a0103016020502c1c010b803043c02c000b500a503480c0400445001401401000240305807540090300c1900640b6001300c0001c1d5a480203240003e0840b140301d0a0301750325511100c2424200040c60280169501c4020100f03240c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 501311492 1250 501310242 501310247
    0x714031209010509040c0201061a04140904050f0d020703021c0c03031211071401060501090b120c2205040e070501080408070204062408060a050303030f060604090e03181f 75
    0x1201d014036061180c20300031a03045494a2241780c0720321000d5000043d000e07040c082d61030300b250301c0c00d030242c018414100401d0081c0f031954809200c814034140c1e141100f58a880c60081d0800183c964910744038403540c14503503501c941c0050084210380c001d840d0f0419086042c40f4072040503083d00700141c502c000d2130a041000070f00c9480b40301807500002800140050301c40a403840c0c554002e03074094032214090001800c1e18402031213103d00a02003400d00c90040351401d0240305190040705042da0f0705500b060000b0b01196140c404440c1449200c0c507111094811a1442e030500c03e1040c007903540201d00d00036000405500026558041d548141c68a99130707031380c44c0e540e10080780c0e0000c0ea040b80c0254448200181480600141160703e4810101a2a00880d1110018a1490010807803849221640020070094070f005c821079810007c1071110260a80da9000410400d204583c041d00c01d82c1d04c0c1902c04c80200c407011018103007003841441c6c03c6125903040c60401c000500860f202880b0805484110180ca90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 501312742 1250 501311492 501311497
    0xb04060f080705040f0f0509011d0c0906040504060e0a0509060c0702040917030c1207020a0b0f04020a0f0906170105100e1308030412020f1216021305160207140312 72
    0x520b1511528060f100c40c0c0c40030030342e8417a620089250300c0c070320024880313031410643d490b0142c04000b074400d821251124505421040103440d007103401ca40000c100720140c480700100d0f8040c1002900074056a50b0300d4036101c181200403140d080ca42c9190102080d0b0703054010072041d01401c800807803103041000c2c40d0204030003010980c03812110344048210032450000c40031701840c456400c8c0324055031100c40d00310b41a8402d01300180100d0031500305000e43c1000500c0c2600858010b03860120701c00300b40e581c0d1300c00b10300c000fa015040b0300e003150080800041c8400d0190090425030303028100c094888000c0d01c01c201d0a9840035104600520880b017810b200400c04645059842581e10b40420b0010300c4544038007007903a10a450517150020462000b008840c0c040200d17140000d000703030090210f01038000c500c1c0880d006140345100900d55003800c0206541d038003200203400901401d0200030780d04111030600010741001c82a4005405818400180084c080d1201035690b1005005419126807651003102c490303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 501313992 1250 501312742 501312751
    0x6010f0504080613030f020a05100506030a0c0806160c0210050c030d0603050d08090d140d06181a10091809140718061809030c0f0b0609010b04060f08 66
    0x1140601000810b00030810480c2d008001d41c40f104902c0c890030307003402802c072001003400801350740c840829a070000b0b200090100e0041c02044001801d07844030000241000070100d070107030028170016800706040c10b0225081c0d0180c00b000e00610181e40d1014000c0d2012760519070069030000070500e8641d03440b40200000d200c0d0030005401d40c1c0c6080c503541104012182d00350416502e6500c030116010300030350030000311904019030200820407a80d0142000f441300000b1800742c410407a020507038902014068000c0c1000c1c00c9aa402e9a1a1408444c240401440c6819030003000c1c2c03901c1840d818013818440c0009a00ca1103541da4130403002d0030070203a560107880c4050803e12031a941d40600d00458070811480700548560000782c00e20500e40496010608507540010345c0c007503d483c00070488036070452714080c0c240c0036940001c940c40b503c03824140e4903180f1044001e00300110f45105201000f400b813045500c2031a084400d41c03601d988034140028603000d240502c0d030200b030349010103001d81c90107101203d510 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 501315242 1250 501313992 501313997
    0x1605120c040b1f05040509010b1c09150204170106050d0b042d03020d1101020a170604180b0403020d03020a091e030212030d1d06040213060f0b030105090601110606010f 74
    0x4980000101200810b90440d43c001349002c02d05011914118040074010014607a0041c1081c81d0070348001c200780400e40414144a07030345c4981e1410400680c2d0071103079491003c04210b4503140d81e88004282e007400105000c150754603280000c191031810b02ca0243c031694101c844146166500e0b82c40d1186a2050094410701d01402a590201540000b6502070010f1081d1301070040c0170b9080d03034082d01d0041c0115400a0b00d900510500b400a0381c03002042c0f50040f2149020101a103c1d01301140040c800c107205031108510109500c0180409001c01d940998030944c00c0711082c055101d401c4040380120b1710280000340b111281007248407141d00c02540c04668070354001c04010341e25400101e00c01540c118042a42d003011920b000302a80502c00c0001c00040c1c0c1d01c1c1003c0310084151096200d45000340000e208603071031200720a9250f095030001c0701801920f10010071480c0c03101d10968071900244a4184a601840700040c1594806c0c2c2174192480420f40c010946174854000542d2510b8002084008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 501316492 1250 501315242 501315259
    0x1050d0906110c0c0d021c0c0b04030813091a1201020c0f0f070b090307060809070b0d0917160312020c030721081915030f03021605120c040b 62
    0x70404920800125000d1542041c0c1d0360070280c01c0d100d05100724110b1462080c0d02e003140e10005070b00d0302c0fa42007150950700340e4002510340040ca84500d18060301d0300705840780381000c24040704210344440248240038900c44000b4840350b6880034607068998401010401c00345000030703030a079810141042c80c101044040007504000206009900d0052585441050f40d400030840a00ca19403e1108001421011016030f00d025480804a5038503091407040720104000c000c001000000c040c07092801600000d10520b54803412007032a00042c1c41205010303a048410030034800c0c10400180c003250049070341105007106002194a003070f500180e407141000c1107a07400300700030f0381d00070b00a2000b4007074244a109024034940c2d000031b6075001910900d6100c01481010320a11141d005502d803500115000343c640410600082d00b0346903545801e540c00100705180000d41102003640110350310002d810713032080c007419642d42c4200b0040c205401d90341c505199000181c540ca15814a074000105152020b0081507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 501317742 1250 501316492 501316511
    0x2150c070321050a0b09010501020703020303090f01030e0d110c0109030f110114070b01030b1b0301030b090a0204060801020a020f01060b040315090b011d0702030a35010b0703021905030901050d 85
    0x10281e65044035401395540d5608103d410920301401d42601401c0d0a01c024208127045d5404a60303a4807a501c161445080c20030760f03a035810f0b84290041c4c0c9000303080506071102c1c0c0341c8400000d00000c403e04001e08c002d02941403103940c3c6501c1081c1240449800807030504c200c04090702c1d5100440240e0009504100b000c01e5100c0c200700c4541c0040c038050340314006811b815891030234096207842000d040740c4da400c031456048035030020581c1e05980c10340c0d400c4201d440040d02e4401101c0c0c43d082c50040d00a4000c2d040401c0081e94203010b5000d0b20413850a41c0942e00001c2e030b501a028221002d5000b01c2076450b400b44028004070b48000238290354140585800248083e1a8441c524189000d031700c900200441041d6140c40d03036140b4500d264109450780015030828404650140002030f0800800c80c40c083e01d6070006a080c0390300f10340c0908500c8560300d00714007561265800c000560010200768003610400440151a5031990002400b441d0040302450508000c1c13001100d503a0300c55000c15251548072031406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 501318992 1250 501317742 501317807
    0xc0f0c050715021b03030f0f0c010b031006050306102411010f050403021504050604060515041b090b190c03210b040609020313030807090e010e060102150c0703 70
    0xa0740b110020f90001e151180844000d005640c00040140d80650414000500586c642c0c009460034041c0c42480c2d5a01e612001e100203004103004520f490741032146010302005080b03d80d00c2841614019410ba0312165290340c14040140c455101d850005a02160011025900303682d2504920210740740801d03503034491411113070070740e0100e078403166406554400380300815404200c1350a810104050701d8686160a44504c0d8542030000c0000c0d21540e20381c80000c106042403107500100100042041154491401810140c4025913864a000c02c80700400032030f9218100c0151030b00e05030741c0054240400e103040b100321107400c640901241800085c401164072410300c0c440700c54032031041300d00018000920004210650f025548940c0c1494410401d001c100e00d088001c2e0701380d094044c205600c80380c45080d4210745021f0950b00c5503194010100020404100c000b1805005d42404d90031903c2189529821003880f80041d64030218616040000c0c1e40020b0260120f61203110003104503010700c91010104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 501320242 1250 501318992 501319019
    0xc05034b01050a0c360506180a14030a062d0b0f0609012705060c150c0a1e020727060f0b090118050301090f060b040c0f0c0507 56
    0x3000c40c50b51034104012011100b403007107000501041c0f40c1550812040d201c0080040440381e4903403042c90f590080c101410303a50800120080c1009003801d40d85174145000000c05000c480c0006200315403000c400207000c148040448882c0d43d004001e008900c0c49035450301c00600003610062061080101e01940c003240e4032011000a290003500462034103110401c01c1615a42c110289106800030f10644144c1d90740030079299820304030212807500403a107107a0066001261503010b01c0e401400080d100f281508089000750046220107151412500d94007014050b90017041c0504000510000001c5001500b900001c0003442150047c1c6580d50789035081400c84607000c40808903c5000510514580080ca1148400415403403004442c06070501c80c1c07071203681c440d800c0190304002d500c100201e09650b0500c1d102d0003e02c0001c008009840300d0b4a40003d80380b4a080099800500d0300c8140301081c1001e010b0111503841c0740d03950f104070315010f400650700d0480f401000e4800344950000800c00e40c10303c040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 501321492 1250 501320242 501320383
    0x72f09060a080f030a17040f061802060a020a020f0d1703220303060509090a0c05040c0203271e0a050409140a0c05130b09010605280c0c0503 62
    0x1d15982c5241e9503001c1c0c20403038100e1080390100154810000841d864549041000d0303401803010448ac00c1440c621001d000030810040d5020a0008003030504c00d0300000d180100c5032080c0c403030480024008040015450a0400c041e001300c00f400c203c003411005590003543c2c0405440d5080102130600c00132520a078400b03140c11030100303a0f980b40c00d1001c6e14201d11501c0c1e1081251004290400b07240d51034450b402030314030410b401030f030302c0c1d010386442c0c41d0003401a2028001183c010503180030030592400300d03002c01e1203000d50161040e02a0b2100d9003034548620f02807103001821040940e072030002440002c0c40d4041d0203581c402864403000c403500205106000c51603025141c92100da03414031041040b03500c9200d1114400c64a400f0118480e81c441460407070460340141407254130f0319a5140400c6101203000d98003468410035400b0300c0b040c2c41d00300c1105518140910703020040b55485500f1300d0b603264503241109010745101c1c03280084003c0d0ba00004000005080000242a10102500b120741d403220036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 501322742 1250 501321492 501321523
    0x60409060902090a05100221040e0a050a230408070c03021c0209090c010e0f04110c07031a071d040209030102072a030201050706090c0b0708072f09060a08 68
    0x9001a03d0314000c50400040d000c1211012001c00346100040d5071003100340c0c40d40700c018240e038400c04007806504e02620000d20f1901031140c594506108003800030030342204c403c54014a08501210008080880401500e00c20a081c05450303c441c1c0390b40c5040d41040e24229100000e03002d010006855034a100e0b0b0b902c0c4d50780301241a1f60718291040160ba084000c1000c0466400f640b45d521580e81d1182103000c0c2c104055500100010389100420042d080e0740407101500700740040c905c4500840000c8000c2142c0c0580d141d281403204481c04114581000d0f2105400190681d4805200d16400c139146140381310028001842c1140302c00120b42a600202016100d211550131024006004503031151358000c80f80d501c001c0494203550029245024000010740f0180e40d810003001004400d981401c09400800d000300e454460514000d9140d40c032149084685892000d12208954001404a0080320b20441c40034516181001407280101000f01040d038820b600700740004601c01d0078410809042c0904 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 501323992 1250 501322742 501322747
    0xe1b0c06041106091302030a020c070e01080c01020d14031302030609031b03030f0705030403020703021f0f0806060a120f050c04080d0c121b050d05030a0b030a0c14060409060902 78
    0xa003851490000003180c2d203402101e0030000f040d8281d4078551030300038040c8030503070050f01c5e03459410f00e6400a01404003109068802d4400108400000c0208207049841c04c401326015800900c0049860303100005026002c2181001c5580315a2a0364024682c81407607182c000040c4001a00060b01d00801030703402ca815038000140e000c07003200040c00020300120741d82004511303605040e40141580c400050984040001c0400070404251080c05164003c64006100512203068403006c20701100c0388030807000102e51800303030690480c1c0c090303280f442c0705800040070315041240007a002c1e07030b001c14036030030881103945c3e02c1140e800d00b0700e2103200e101c3c01081e403070204031b03211401e242e18103240040034030154044c004042c0100c0001804507844c1150411300d858003c07040202c940c110701c1100b40c2081c00504500815081ca94603a1307100303015500c510151802400109401010706480700c0c0b03800c80103000c0c84592182407005503c2d070b8000d2151180050302c414070301581c9001c590100e5a42e80c00801000d44c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 501325242 1250 501323992 501324001
    0x40f020d0c14030a080f030631140f061309060513061113030320030a020a03082206020a0e0604060513060e090a0507090915050306070206010b040e1b0c06 68
    0x403002c0754084080d0024400d13003a41d0f8503283c126004070b004a80035694008009a4242c50310b80352059601e254402402495811042903051141811078113880c40c0c0c9000003000c1469a12000b00e801440060030440c4a5150325040c03000b440180100d146000b80c44055110015200740304142c4a032183e031125004c0451180fa255003560900120914049014013100b083e00010200b04400ca0340e150400241c18402c20007036842c400c0b60442c00318000d02001c107036214045d80114004500600c0b03030307a400b1020356400300c02004407011a2071509582d07101c0310415002407101d030f0003482c00c41207a04001540c039007114000b40c0e0652158101400094010907e00180a0740c1c103640b002820b124200b49403440d50b01400300720588402441d55034031a403610080392016000703040d0f80700503181ca07000501090341513409020b41002148601400b9200310400201105c2c804148c10381038410721103403e071030245050200308054002410300000e00d1150081e0315024900040203200861080d40a44020b180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 501326492 1250 501325242 501325259
    0xd0308090606060f12070207050607050a03090b030106140711030604030f0906030c2a06020a170a1b0c0512071208100312050d140f10090b0906010305040f020d0c 71
    0x3a010074090ba0062044540348013040d000e940c086945082180416550120100e24042041e0700c02d540000d0000352140a1002c0031440407036450080c0c5503400040c1d51010805581c0c40244288000651910803207031020300c10800902e2040d00692000c02d5980b04000000d0506105980480105600d100030191403504510a00002d18142c182045001a1110301a01c14403032240d02404802d29140404800440170103e0240c07603030884011512440725110160024800c4000c0500389141c2000080209809008400640e200040030160b18100340c1801d8498921410086501d4068a00e0f002500d003180d40c00380800c54010b001644204e09011400740a5040240407a404c400d4407400c10720100c1c841e81039038804140341c1d02d4103650701d51501d01990014102e018040200c1c1c8000414020048003060301d039400780f4034003000041d10030390380d00d0400120341e281c142c0346411040c180c0c002500b0b50b0081c0d1082c0ea0041c014082d215901c8545d0380002e14040d00350504072101c1e080d41505100e041d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 501327742 1250 501326492 501326503
    0xd0804051314010e0f070305090c0d030216090c0e060301030f0b10030602070b04030f11060c0c0c03030c0307110d150b04060e240a0501140a090807060207090b01030b090a0c020c0d030809 82
    0x1c46e40d040810240c106507003116100c800211056010f07071030441c10201094420091120601000c4100148054440320b5440151402d08030f0340f000540340360302d40040d501e0308208481c102c039802002a007800c404caa545031401d1900a000c4010f10423140000408a0300324001041960700c2603450f00000d00d068a000f0b4051075002c2c1c4154200105006d194251030b0000480e150810080e2079000c0d19010000d404e00d14280030448166018040801c0c60b0042c0708000010b04210f07032080c130401c40d00d88200383c00e101c081c1d1100400504450008142080040102d030700c402e05080300644007090098544955902105080d40d90103001c00241c0c00c0040c90002018425221070002c8440c2148149848002414400c1210924203807800c00910b0b009401e00807240440103190007029180450b40c3c0d264065100d0f0032a21651610508000c072603c03103503100b445894030000c8014052202d0351500304c98000100b2402c40c1100651040d821081203075075030717400c2c0b0a010503c01d50b1000001d03c1c00030b607210b0400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 501328992 1250 501327742 501327751
    0xf180501060509090c0910120e030a0903170403021005092d0103020c07031208071107060c1b0314010e0f0d0203030f0705070c0f0503010b0d0804051314010e0f 70
    0x145018014030800e9441012240e08100c00c45a0100a4441100c00ca090307100e007540d1554000c2c511580b000400b038010200d01c486642c8220100407160b13045050315180c2c45805013000000e00221010310000d000648000940106c0440c5181429200e41c0071070a8000d0000300003000c02c0022403161401d240c0741c03001c000c11910312032114030340104540c1d486203012081c5031204d042c11340203d4250046002041039000543d0051003203580e6001140018000250554214001606854a006513840006502c00440d59540c0d24010b882440b501c2d0b00c030109180d40c041c00b00700011340720000b0118241441042d502d10b409400004c1a02c2c0b489c0885140c40305804007052243c0084c1c0103170300c50540200030f803a4440244203486905664040c401c0701c032441402d00003400c0040c02040412420300303d800780001d03620240c0003084407001c503074204220200382e000002e000700020402030001e820603031a00451035000e00300c045441c8100c5100d92510090076041100c142c011101000f410068803401140c22 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 501330242 1250 501328992 501329039
    0x504060b0a0501020607122c060a0509030a03020f0910020c0102071a040308070524070905030c030607140c1504020a1208040e04031e080709051e1e0a0f 67
    0x540d00c1e20300082d4503100b005040c1001d000442000f882420103580003600e46500013401c85400c6201800390300d111018008e0701c407481d0311982c00091842101031081c3c3d4022006280207608110054000310082d40c0142040e400d000414414050241c03a80d42c40384842c5c41207500508015003110000a103800d1640d03000d80050001010001503d052183c212001d40f030704899600e03550102400e02070f19110b56150101041c000202c0100420400ca1074814000c050596400b00d075250344508042c1e4580c00c3c103030b46582c15000f80b404600c142d80102802603c0600d0b9942c41420203c5c180e54403810500c610281504045607802040b0071440c041e42e002010b41801b62030901028501c1e2640d940d47d00540c0540c02c1750030012008a01814000c10301c481240344e0700007030100c9098401c60700400800040d240c3e10f0104602003400b14113450074090000461034801d40342d00a0209200401941c0507041c80c4010001d41c00e5036002d40c0035190400b4030700c080d003070004441383c40500d82041482d0079118662401e0b207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 501331492 1250 501330242 501330259
    0x9180a0f0b1e16020723180c091908030a0c060c09030503040b0304020a0f1e0501050a1b0c0302190e0112123605180103050a14150a0504060b 62
    0x18064101c103500c2d03401628002c10508050050380d8103a10f4420300c0d030403501c09060f40b0b0401a1400c042c9100b00702e20341000307a45003007031201d90041d40d8030200e400f66501440200300303014002050903c10080e111115a680a6501203a034031080d06013140d009242c0403000170780084681e41032003ea4025100e9040480c503110328070a1071030f1510741e101c1c091409800101072b0000007141c2550350340e0315450081c250188000d03268507a2031440c07c914a0034426951590307000402d0004080d801035060342c03003030b84003901c0da18029404020f1685240802c02c00494005000400200240c1c45190340000900070500d9000043d900b083c188a41c00c05c416440607909010507d000c030005160802c1141600815080c0445d03869990040050002e82d400300c6489c1130302c1d41800c000030350707103607110701d041114400d65154041108030000042081800d00024000d036100258820000350404019007820100100761000e1884060310b50210384030540758550b03817586407003d11080c0b0160b442800120302d0215107444e03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 501332742 1250 501331492 501331531
    0x4140415030c03020d060e06130b0a0605090a0e030715090507120302030f30070e01080c0a11030d0510030b01080115050f040e010501150816090509180a0f0b 69
    0x110b110003a0000074000d210081441d820040703170350001d101c1d039041a001da807020b241803160310005000a002c25500ba110000101e582030465101d00800c4c0d407000350480c9440ea403800181400307003864039400d20086c40304200c000003141030f21a80d00c09000f9240c90120b10400c080c10440e1400000d038000024004450b4042000250004101e400003400c05002c40d0711100446255003850744160400c14007092440101c000180d240c11010b44900c03c0e507200c0000040d6884011a440b0104070769545601d0010442c0e1008c05000b280030310126413150307088920306007203005d800c8180d50081e11003d0000382144028420861881400e40c05007420310004c05c1021440460010324010354428940180002c0252180b60740b01c5070000301120180c0c400900a41d6581e0000c04110340d5032903512400110b0302408030f0300786228100203c100b45050341d40c40c102941030408010130000301800d003c20035408481e42000c00b01c2c003840390524040c01000b0140103100241000303600e03503070001c1c12000d16956060204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 501333992 1250 501332742 501332753
    0x7060902040c08190b0d080307030608100905030d0b060405120303071d03030a0842031c0f09180903020f030306030a08090d0512190e1c05120414041503 67
    0x404d1240c00000101d40040c003200402d24800a030b04c00502428000420807584a40540041045912171002ca81100c40c0e14584070003100c2c190340c0c2c000c203513400c10860f41405910a800c184402d000c0103219510307081d56074001a120b504080300c0740e0240d81010007041a0543c1012189010b0301c490700d004803c1d00021000680c0341d1081a0444080c841c1000201d824800c510f0380d42004000e80c250545000c0c91403008000881d80340c45581140c1300318900245200381004585074103e22028151104c440c1c04110041e0780b40300070074410704200103420000246214001400b40036007403030904002840c04041c1802810a03404a40d400030640c0100107009113901c0000340c0640194001d030159454222213400076000c2100e0703110181191054580240140c03005000500800c1400e464041568448900640b180c0c1090203c0340c0d8450150b0442217854410024901c4c8214840d405551000e07124142e10302040c0c2158024581c0d846440003000483c1c1000d00c205452121040c0c801e0301c61602d190303a40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 501335242 1250 501333992 501334021
    0xa140606060d0e1507030204030204060b2a0f0102190201051b04270204080f0d0206040510051f0f0603060b040f092403050307020103141501030b01020c030307060902040c08 76
    0x8962440e90f0b0507848036411400e01003030141e2080d0545140d564100302074014080e4200707000c141c1c0b1662900000081c028183c40440f440150f0214801c0e07e07039405040e0017440400c0c900d074524100c0c000c0161240c00310800784011b08100c10030090320310a4081c0518000c2c02c480d00108021034260b2403440300c0181c0001402500d04403410516141460401d203414030079070596142c0f038144a140007040100d10364401040100104080c6021510700d10101c0900303e98400040d200903015402802c2881c458110940169a12410b610425460b0100e4070b00c2031000303141c060340000c40b664081e407401d010310307035043c090440100b420614460409081000b02001c0051034071420400b155205561440c2c188030020503030014403000e000906096403401c203907459501c0800100e002038548410b0510281a2015850049460010180a22176040300540c018810000c1c103505510520000d16059a0208002c6c24a1441400d01268005051050106680e1030300c980070148480e240c100b25686601040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 501336492 1250 501335242 501335257
    0x603070302120309130603020f0d030e041a0d0302010c02070914010b0a0908030705070503010c080112140319020f0c010206090a030c080d020d051005151c020d020406020a14060606 79
    0x2890600b0514a85015203948503203442c0b2900500c00c650f0519840040b0f5011a00700c3c3d0080c4c0d2402d40403035500c0c080040c00040c080005010451110807060181040e82c01100c2041d80356404c12103104501000901d0412650801c800603034458004049180d8140000401410049000c1c4086001c0758000d0030151014084c0e40341005000c510151024800d401340001003901700e003601e40d90081d034184981c8944040c007071030380a0340c00c144d0b0a0071418415503178a812a02c0522502e00002055502c0c4140400035580c01c41962209204511000b42c81c4410201c00c1403c50300102820140300401c181045104407000741550016010424881c02c0401d001e10794507818540003100007901d1900e803c1c5405509001d002d0103102003061140e045082d40f04600800741001001860707a510010050300c2c4810740703409110b90f1014058018410040c00888250b031042c060090f09044090803600102d800c50b6000b180142e10807a905002d01400c842e10204060f41030380a003c10340b0b01200480d1403445190b5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 501337742 1250 501336492 501336499
    0xd050703050306061e04091815020703120f0c0e180619030506040b1f030804120501060302041a0a0605030c0316020f100506100516020103022107030f0e060603070302 73
    0x2c0000c0b038581e1104c044a172089901800c00c0e108202c1040d4a01490b0418012648041c0c17400c1c0e250081811003600302103406512440300c6c2c440480c4d07001100040c0d00700c007000b102480341c02c0070b00b0000509540944011203100140c00204443d124000415055090b00c1403409251244502c0310010200c2840c0c1e03a10900a0700d0402e0428054412400b400c1f41c190300240a0307018140c04e00041003260a5254007400345801580544030f9072084000c03d4913864840105180c40c10002000140140c1042c1c60481c2e006000016025540380c02050aa951303d512240580c045001c481d0600d14107910708501a1100e40340481c00c524040b00d0b0121144000382005a4006500060788121031003003000008030400c04059800030040e045102c400f07004103449507480360301404500440544124142d420f866105203110240d00c5041c0c006600039842f04641310f03226518002c0d41d1f0042c85c002501680600080e43d000103802c41042200012205180a5243c50b84c100c5024410155800503540f000ea82c1c04a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 501338992 1250 501337742 501337747
    0x6091b1b060507080709060e0919020f1b01050705180609060c0319031107050a110f030304060f0206060907021c03061205070533030a14040f030207080d05070305 71
    0x45010044200000c1030081001c0c0c00e04042043e4142e0011a480c003c20341c645424031229100c10341510b8002e0241c09032500301004500251540300c514401c00c440e02c81c0580d00514203144900d41c1c14490303010008241281141045820321506d0911445070300040602d4000d0801284409104400405d985d210b4401d000c081240c404d00c1d940c6004441c1307602103030011680d030358817007a1845000241c0d50700501e000c072385000000581d8040400448034078640c0000582540d62055503018072b4070719100580ca4200640b00c80116158608000400c083c01c1140c4688400d50b141c00e100070303d0218001d14082c0140d82e10414032060540029101d40c0c0040b020030340100021243d0350440c010115984604440f80081410400380000450000d09031103041e241200d545403008004182071484c0a07514080d01ca52503564202d00b002c00d0003468120540307120210300044080c00210030404291000d032000800c4200820405804001c02801048044064501300c1d48405014000d80540f201c0030f810300100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 501340242 1250 501338992 501339017
    0x5060907081308071b0608160810050d050111030106092102010c0206090103091b03061514060c0106080304061e0c03020c01050a0c0f060204031502090604121113050a06091b 76
    0x31905c1e049088284170819041d034603a034903402406c00109940009400460700e5a9070311451203100070900c100078014030390340c0b51031501d41032003198501c0c1d01040d41c86550b02d15000407101480303030042d4001d02a40da621540030782001c542c0d45171851030140114900c03425100c1500181d0300b01c02e060300516011074030607460740d104200590240100311001011546800800f00c0c404a2001501041e28020241005501400c480a01c4918007034025011450031101813107000c4d141c420001c2111140200c00410b8943c0e450a0381403a5070050313000031010030807031040016000d00d0007000c0c6200c50000c1c5044d0800418540300a902c604801c202c180c10040b0010300c0340f080c28080c0014690b525440780011034031036143e0034114000e4000c0e02040340c0407440d03c000140301d6a110300a544c1a060001d1190349000e16090302ca50180110f40c8040721900b0403c1c40c546201d0703840303140380460040d09170000320300b82c5001c0c1c114804451554114111103444e220000501d50400c40c0c0c20001c104090038103071800911f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 501341492 1250 501340242 501340253
    0x209010e04060f1b02010b0117061203360618130b03030c0a030201051602030306042a0c0209070306030c091d030d020408152401030204180506090708130807 69
    0x1c00741c2c03041c2e1482c1040c81614042d030001c41d584242c803046a0080001a501c080116040d4074416000b540c498274200106100f032030300f1403003000a00712400440c3d2034101c42100140c0c8143c2d138111030f10090340c6a1102d44820900a41d0200615441103d1803031816199482c4c040c100c0d440d40d00081e024110741c0c01a0351800d80c0b0b90307005000c004c0000702165100c1c808005800d41c4d0300c0000c4406c4006500b800d001c9140e036020741c036488080f491140c0245045030307690741c140001002000060101d40d01c01d410b000310955986281141d40311640d50b0f90341000d032054014801c640f80d02502d4641010320b055410000700f0711640b01070b010340300c00c4d0314082042c6054008440209101c01c0c40340c6580c0c000010030000000c1d056009000320341901d015144da84020145014480790200c07403588804c0040380081405401013001c040d50007505040040c10301da126020b02c0e048001c0c22810001e500da0341ca0030b105c5c041c5400410154410014a00005a403500450f40c0078001c2c1c4403580144100c4011505500700702 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 501342742 1250 501341492 501341501
    0x80f091e010f0e010b0f0301090f060e0709090f0b01060206070212090a08010c0513050a0e0712150902040911030601020703020915060f07022713080705030301080f10090209010e0406 80
    0x7808408140b2072222081c4540307008004060070349106c0c00c441c0c0034032017860a060081e0003d454014a55210110080d1590809455488419030303850041c2040440ca1402c98410105268012101c2d0aa102101e2809074a52201070b0040401d5600440070085a82d0b4009126900340d20009090b680310b0010001188260125801c101425404c01e1500010180e10401900805080e0500d01d40c4031560355090055541160007141d00885081c40054101806580002c0c0301001c2113200140e40c41c0078454406111240344c0101b4281900000c0070880b001c4280240c00c04c10b85c0701c42c4100e01d10b00300400041c1d03450b80c00e0f12000f401070724004001000c5004003d8411030400740a00706566a0501c001c030115141d008641c00c0b40301d00c02d20400c01d40b00603805070420000002400681100380c0b50b85c904900a40c803109421036545030100b01c081d0000306c0c103002139402400048020080340000000303075410190300c0d0108149940c600304134000503039a6604d04d0b80c1113031618108c52942c4c0d21942880300142 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 501343992 1250 501342742 501342761
    0xf15051201090b18060f091e01030b06030f070503030406030c020f010f060f0b0702090f061201020d020d0b061204080a030b03011505040b04020f04050609061201080d080f091e01 78
    0x840400c0001249242a045140500d80403101c403d10008840c2c409269441c05441d00d0350440d41c034440420281c207001c00304030381103001c03d001c1d00c0c4440100e01c0c1f20719000009810450b260140601072140c0c0303050800c6107000ba10001030107494410700306000f00341ea030700440c0f144204040e2104550b4041b036009120584240361312200070f00c900c042075400ca402805051082000d40c658060700010542500c5040da40c0680d0700400480d056202c0c045110003104014140c240d01000040c080d6010250900c0281649443d0840240e101c10241502e80211800380503442c1c01030b101001120b10340d010300016180e00c240d0240c202925503050120882c010507854014940641c17138000285540c041e01c0d1461412503404032400c0c003e0320000d1042c0b0040c0d0003490481090440c052009006518168029212504001c0d0807541050400a4208000c500c280d0040c034558011042480301c0d645d1040c20103a01211a5801441d982850710b400c81d501c40807120008580741c0f07404100c200200080d0064880d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 501345242 1250 501343992 501344017
    0x4181b03140705130507020c04090602090307030f20060a0c05341a040603020f070c0b0a0f03020f070308060d08030a0b01080a09050a12030603150c1205010f1505 71
    0x840e0551070440d41d482d41207000f402d1040e841d4900c400e114400c04d0181c28030480d4250302a0050411000a00c005400e04540407104981c00784046480380c1c5003003107408000c6005a429202440303c40c2041405104420a0084042c00b80a84510703151034000495002d2410340c40c0001c401c0b00303142405807d140b0140310304411098588280c0c003080d1424440d0000f8020707130703041030300d4526664081d1003800f503401940029600400d000400074180682c0c060310414403e00d4007145003552683e40c4440c080d4035a00f007846030030303c0414510310503a0b0292181d400800281011407030031a40e044540030a0091041c000c0c10455510001029501c40e0b902205515510000031626030620141020180c003440192a00044036040068402d9050340581141c41d038105e4003604460300c0c01c1d125100d80b075540c40d90310750a140d120349000001404159140c02c3e66500c0420005d0940001c000040c40e580980344d101c02d20302d09010042c000e269404c844402241c0145031281e981c04c03c20740381520b01d030007000526081d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 501346492 1250 501345242 501345263
    0xb0402060c0712031106060111060109021e07030f11011104180e060901020406020c031609110f07080316080402100503090a0804300b060913060504031d04181b03 71
    0x1301504281001c100d43c46100640e203041d0388220044907000c0d0f0604104409601c0040104240b5150781d009041c510160b44040e02c4142403100d03a50600d61058404900144e0341c0204004115840030324000030800c94002400b81e51040018000c00e400307039010321900304011422a00700340607030b540700c111101c100d14159441894024200ca000b500b2078816800940503c1c15482c44501d004504800c02110103001e102e60b440c10712114400901002c04883d4880b0000c1100646803c040000307458a640304c2c0220707550b00e00d0710b82100b040180c0180900d009001e0301d030050100580d214402501040050700e0301c0d030f88030b071b49911009140c001d90000c0500300200004000c1540c01c1030030220081480c64954030500c81c0b22100c2d01d07000f800c90a86018048018881c0411b1007454094a1290000500444401410081c2d00c0354000c0b07405c10f0b1411004a000c0ca0400711921595840005003400c0480d0100551001400541d4001019820040882012145100c102c10400101c40091038205280d004d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 501347742 1250 501346492 501346529
    0x1d010504110f0301020a020303160903080310360f18060509010605060325021f0506040b060c0c1302160c080115120f3306090501030b0402060c07 64
    0x40454558581e66018110380e860398512410140221003075010130354000c40c40c0d540c99000c0d648210f0300049410301001011003002010403220000345001d0000428a03240a910f044d4038003104846d601242c4144181e4000c00004040003445001150400c000c4045401000c001d4120001d00548505032040c0460810700c5003030184581c88144510200c0008210f47c41d115402c010700345c00215000c0c82c0c03101e4414507010f851792142c1c220b404034603e5801201c074550043c0f02e1550f12184064859036110350344000304013281c505070191200c0c06030b0035602240707000c901e803a006490380d120031212401522040e80641146030642e0445170b000d0980011110180384a250041258515100e030302055801d0514003c00380d0019410041101c0d00e405160401000e281c0c3d503000c211140d1a41521b04c40480c00c11042581c0e24042c0d500200c12008801d004403a0841641908072000c6400580c4064641030061001445100380c59410036011035619440d102424091460080160401c40791100e1040070718 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 501348992 1250 501347742 501347753
    0x7050708011a030606040209061c1415040c090317180a14030610080a030e01030e15100806041707241a0405040b0f060406030f0c09060e0c07061d010504 67
    0x24000004101d098071005e803120310810050340620014150320084c2003000c01852186645001c01c0c401d110030340414021020300e030180f01007008032440000341c041946103050758680703403040c040c0290f0740d42021501141551607003106000385001da94518000001d84140104034445040e0205800600d485a80c0d602e130000c1d00e00209400307906034003078803856010071181d14010203140e0a0304c1003240101110f442036201203c400b45030340e02807810705594800c40199184284190202c03114262004038644c100010b1013503403651326078020251600b02e83c05000000301001000f803000c22101750000d40351030080c10300ca1030800900c44a0f518203002103c100e00c560741c9540008500c607088200d12009010b2800038002566000c0750000d00c1315000500045280303800b850159000007010300300046103134403542ca125480c00d0021060f0383e030540d41034040244129074003a003c0500000700981d843ea05000c00100814058080001c11b21910ba48a00c01c2c203080e1680c221982503d00c1000348098141410324 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 501350242 1250 501348992 501349031
    0xa03020a03120206010e010311360106021915050417030106210606021c26040b060406031703040219090504120503010518040c0b040e19060b03010302060705070801 72
    0x46002d0f0140000004180c1e101c1e60f06d59040341e070821003414507420048200480000c40d031000070710006200310107000d002850b0529152044c4c058680380720300d50401078040d1401041c0707004c0240c8030049000d52030005100f4451a0b041d5044440e020600d40c45514007050066008900418a00340c084000158150300081d04c011500c07080c0d040000b940d0407401e510091340c142e0301402d4090b034001c201c20301c48102c0c00005500107580c240ba011315523500c4c0c0c1d40b041d40304401d0103003081032411070b00d41030005004002044135007118048804100681c51562000c0ba0fa400c0e030340701c0440c460408000a415502c0780010480351030310058804090f152510603150042000b07407000c0c0d8203072130150070f4904038602030021241038440003480007220900401071040c0300c0780c0061044403c11340b0b0a500080294000016001401c201c4286680901d80010343c11012803004280010086c1000c1c0100703c1e03880c110701207a043d282c060300c000b0780c0d50780c250074100d00d01450303079100012070b40ca0284204540c0032014107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 501351492 1250 501350242 501350273
    0x9090b1c05060103110306062b0203010c050a02070e0f0408250308190504081608040f0e1905070c021315080c010917120a0c080403060207020909010504200a03020a03 73
    0xb405d020381401c44061541d0340000315401900241c40c2210030400503413040140d040350b645499130b8440742c80c1c20b6003c03078252070182d28088081540402c082d000b240c1c041c0030b914060151584041154503140080d0003460101800142c01580c0009502c107518250307503955420241e0703181806600b55a545030007008100100c60500401c9403070070700390b101603039a03010b410700854100d07440c1ca05000303194100c03100d0f29412842c01c07204c0040801c000100422032030040350061580b06020a070910f03024959641c10303035642c1079068989282104100f2000e8100207100c00759a015601c500080805c10360140c000c00e03188012070b03810040e540000400903000100c0c406000c40030703620f581e20203903200150074007001428840c14072a00031034114610709044a0113410a03500c1890030024a00031504ca50b04560302c1600203540351500002c0000541c289044480e4200300540e000700603528060300c5030400c1800e17041c1d24031910004214050000c0e40e8154076500a1074008242c204620355a181c45c1156910812 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 501352742 1250 501351492 501351503
    0xc060f0305040201090e27010c090501090803071506170106081b01021e01060b0309071e060e090408041701020909184902060a0c09090b1c05060103 65
    0x8020041600c41d0040900843d03060b1117540d0118100090104c80351401040001e03000140000e52081c080403440d04034414800a000241e5580614001006408d160704010705004650408020310f4000000b1100750356040051401c8841c4445100e001900300c540c440c0007030380c1f0341403944c02083c00706500140450381503030221004081d08018200e007641c03641a406015030828802d444481c0300d84050311050190381d0340000398054640c0c3d11009136030420f0740d068080d640200014030004d00490140c009030500c00704802e03005498900c008010410409055004500300d50100302003089480035500909103154990b0080c040401116000350000c400086c45141c401d00807900802500340c3d003a07900380758500a08114020b11000c2100e820318a86810140070f811000c0414207034401c40920001520500621103410059000900d08003018043c110f201c1d15110107041c1c49900300741000203c403811031000c80d0601600000402d00c13500c0d24080c000c07182284d03800c00108500440d445058a00c100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 501353992 1250 501352742 501352757
    0x1e0f0903010b0910060c110d0507080d020a110f011218170403080f0309151501030c020705090619080102070b1006032009040902191a0306060403030c0516030c06 71
    0x200d04000b10601c013a0b9008050040a0005100041c03149018200ca075000d8501d0725100c02e55600804d901c0000c02c90261411380100b202807015010500074800c4600a80c40140001e070510f437500000d1160b4151801e10500e218018020280d002c2d4100740c4004144250410005e9142e4403100402c900e61001201c80000c2003078111141d905490540b401e40341c02000e82810954240403028150303002808100f05071058007002217402d01d078a200076101c0c219a0104200d610751100000d010355002920500940d005142d050040d80c48010140d41d000000711298801241910307401c0c00401e083d600541c0655000161380c3c000c2c42203d542540c02940016103080300300d551408220101c0b9202d41c0d004040818400945000d5500300010307111035000200001100643d61780041c0303800140044d04003054900280c1000040d24811522009042030300b44a4a14a042c000041c020310440c00001c050101c480740d0042401000c00900041446102c0250406e68690030301d019141280e1141d0000a45035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 501355242 1250 501353992 501354011
    0x1050702031b073b0703270203150a14010803090a060203030702030d09061b0e09070e0a1511030403110307050f0d06052509090605030304050102060406021e0f090301 73
    0x3c18904a812254059801c5100740500700b64a03220071884480c004200001c2c500c0565000c500c41d4002d120390340340040c983c03000c03142c1c0720004c0943d1100700500c8901200420007503100496103400f03145054601c207031260b440c02501c90080c201443d134440440c071000000f10f101c0300000010062094100c411480c2c0641d03c0d14102c0ea41e22040365201c005800c144150345032701081c0c1c1c00c80440d49105542c0451101060400504030100a00c408000544c0954911482e41844201a50024040d161404d8090604804a0581510381c80740110446104500481c414030a072501010f80c00c614094070361702e507901d0411450145075040c03564468040c0900020300c81c504042c00d596140009841e030031034420705446600040000422840791880070354502d580c3c1c4603940700b00c00d59810342c42d1100201a41800440030482da000d03004240070394020803040c00142c0e0005040303a170066001c080569150580440000e44e1340c4454503220103d08089030718000701d510500a0040b094040d4020446100d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 501356492 1250 501355242 501355297
    0x703060e100207120c0201020c040e012301052b0b0903070317070e19050405010f180501081f0902100f17010311060901090302060d0501030c150503060d03110105070203 74
    0x101c850003000d60000d5140740b81307214003c9410f100c4c5180140190752244c00d40001140c142c0703080420126103a55a01503403192001c1c80b810030040150b407500040e0240d1b0410740030514162003000402400f85d040c240344106020070447d0701c80e0003540250642494100005519a2a040807008402089003030042281d5141c0c04128103100e0107031a43d07444003c1410101b130010055240c100e080e617000d404400400c4685980c05124000d000101e01a40d000b85030807a400c03955500380f20303045981c2d42448010000c05a00066040c0802c0040880040c00c100040d0341000a24498034025080480800001d20164110042c108003d4051301c80c0340d00720201c12000809544240001020084588442c040a0070b2517000781c800148181000c0042c00e48a400242c41d40c1c00110a030111662103000503c104665101080e00604c5103116a04442d85086805040e03800000d046a0095000e04891f000307151040f0000607503522108020001030a10000003500c950045118040a81090014508460 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 501357742 1250 501356492 501356497
    0x3051803190e0d05391302160c080c0a0608100e181603020f0901060503040f0c03020913120509062d040f05010801050909031e0c0703060e1002 63
    0x2400003160714205546001500c1800d00b825410741c10160480c1c201000800030040d0340e1a5102e04d01c0e00804001d00490000400003001854003d10034000080111035100e8025500010a00040160b1964030344550000a07003c840d4002e0b0890b810001e00282c1c030640130410401015081d00d1506415480d13150580741d501055a030304550704811402000040d00000e049500110003036041244240200500c07403401c0c0803280b80b13034801c61038550f041045140002d030f190201c0368162881040c540c034014001d000c9000040000c0d000e2103c84c80c0480410203110145000395500a0404c0410b080481c0090b60880d601c403003c580100804044414290144d81a01e6403420024880b504c0c0081901c000020318404039004041c40c06038007050844200c0c0d003400790000c0c0460b094007000c050b2400000405404060380700700e000d080c0c0c000502420032004030480d02a608041e4068080106542c9090954810f94202d00018000c020002c001c000d41c81c0c1101d19031703c010b0348c119a070012a200f4003100300d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 501358992 1250 501357742 501357757
    0x3030c03010e160f180f0e0109051006120f110708091207120f02041503150c0e010c030305060102070506030a0f051803042303070609180b0f0105091c0303051803 71
    0x30b404d41402c1214a403080300e50007040c2c01d400c41180409655044690841c040d00d400c004081e00da41c00051000218132300c106076212603d4010030f01d0032480d02101a0000071181c25103e180340d107034005002c0280c09a0441c402c2c00c0d10f41d940d10b5170b440c411070030b1140d400e402080f01d0a12403d6120360202c02a140043c4800585821000511546401b40d60320843d10100000c01c0741c1041c3c51b501507800444ca4071400380029400f03104d0b103030104c1d1001c8017210201c8180494910900012140300c0c1ca642e44d01010280c09158582800291511002c0050b85003061640c007a6a00901c000200b101a04054200d0b0b005400c844105101584a0228000014406268586046d0300c10f11003041900007403511614400000c001080003d6041c802090070075102d070b0001c4020900641e02003102055466450204e00a10300d010403156000380e000410f0f95203283d000904101010076800860b07030f038842c81e17002c0c81041102d1889003c69076181c081e0141034121050450701001c03a10205003848048114ac215 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 501360242 1250 501358992 501358997
    0x81225050a0309060f021204051009050d080c090a090e0d26071209200603040203060c0f0c0708011b05040b040b0d0e0a0f141b130e03030c03010e16 65
    0x20424940750840003840d1190701640d45a8540345034145201040c80248000ba0209566450520f45170070310528000000c41404030f100d01e020031500108070080340d140d441400c246031402c025100e141c00c8102500500400541c080c3d038101c0300043c552216400000412000401e650320107400c840c050b59501d40021108100303220342c21907001c1841c8034001c2941d0115690900ba2800c0c0c1c1c0005c0c28000302c960f164000c45580c50503003d048d0160002c1c0d01e4058980302c0c01c882d62441c40ca49a400701e521840c01810034108a01c000c1340441c2800d620380300340d65820b540e100442d40e50903a02c25600f40a0000f928040208503004007400c0c0780544a03070121415030b0480000700e0314192034918501c00c02c1e84103080c2c1441042c2e4440035100d03008400d011114a2038001c29810300000c0381c604100840b2410340760481c032954400071007440070110012100122440c1192442c0041011000c4480036103480b514500c0349000000800c0452800e001c06141070301c076035030500301a036038401005a6004402032a00d602 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 501361492 1250 501360242 501360247
    0x1501091502120c0f120717041503090204110a090f05040207021e0616060b10020f100e0f120d050606040303090302090a090b070f02060604063008122505 67
    0x888040784020458403001204840030040c444681138103045c55001e5800c1c40a00004111061050341c1d681040f9102000701c40c146054030342404040440a08000b00703060545074018602507507a59440000c031034503400c0d225550740300d0302100208829882d01486030801e00c0b0075804909810140300f510080c9034043c0248108907041c820800b007034421100d0f41399011908000c0340c204088000301044400d8490100441c11908030400c0102c109420040c500456020f80f8200c040900c0000c1e001e007009401d44800910841050b03111418890a641140d211b131103901d0aa0843d40d0a01d0014011a504000104203946401040100310300c62840041c0004d0003401050015142080c00c85402c100c00b048001480041f40d070303ca80c0840c00444282c00866961071280c00700070b405018295000008807420840c0d1400d15400381c080d044d40c4503220110390030103010368100c401440848404160071020442c3c84144440340d83c11000d1080798540c0498422507036004c40f0045001703002c050a04107454603030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 501362742 1250 501361492 501361513
    0x10e0f2a0306062112091309020a090e1c050a090b04050603180c031005010f0e010305031615020c0d09081c03051512060103030305010b07030203040306090c0801051501091502 77
    0x4810004900122075104c444984500d0341c004000f10f0302c0c003500d608080d0341c07240074090800c404030209103010103990341015031078801070b40d502401d2401d85044c0380000070140c1960021300d181c1507407060340302e00703410201142866844d00080980803856860352500090303030b1200c0320a41d5901492240580040091020500103003d101a03800c080000800b25080b0901c80000207141946880c80100082d6689c0c005001190140310f0305000f1b8007218000814070b500d142d0721550b980c8290001c07103030191085504403040059141c14030303141c1884480c082d0b40300d420303210100e600c0c0e299000c0084045000c075840010b02d0350b00030440480c8a107004001c1c04044101341e00c00d50252070020140140d0b1445110f820749581c2d9000b2000c5107101210b40140050b605514000d4100c40d17040c0c020f20300403502400500d001981c0081250180ca40c040e0b0b012a0641d05480c0c00070000c1555000b04005501b802c081210040c02e032051012415400d0342c41100223039803074190000f400200a44100180c01c00310301c00303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 501363992 1250 501362742 501362749
    0x5040e060f120d030e0d0c020a091802090109050f070e1c0318030302010509190c1211040507050304030e2b020a03053415030e010e0f2a030606 63
    0x14907007003000381c2000c5001c100680c00303909082c1d00304541404682e80d28410503c07404108a03c0403007080358100041d80400c2900054420b0005208005082e5201d000a0407200450102a5003640c2e01400840342e9507146c02c0340074040c0408a6410040b03072100000103011501c500b00111145001800089940701c60401140408140344010303418080b2100a403c080c407450200c080086002c2d500024041c01c0042d80541000314600700400c0d00303941105950b0120f036104c100ca40842d91050f503100644561842c00d60302d6807044040d540ea0040c64403040080850304000210b01c120b2281d80c4424490319020708002500c07806003141011a600c8031101e200c481076241c2106510760004101c114419174030365855180140307035070071400342051640750b402c5100404d007400310101c1d29080c2c08044503800d10343d03100340401c0e089070940701301a26840d81c0c4031080c0003940070304c00f611501c0003542c1c0d6800c2e1084995136124294111070846209020754194012460450100b802000030082c2c0080d44402d001c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 501365242 1250 501363992 501364009
    0x903080901020127030806090103230c04020409020a1b0b1602010e0303090703020109150e060706150b0301140406080304060c1505190e1f11040e0f040606050105040e06 74
    0x41c10340d0751300d03448200d03030310000c09840340c00e10380401e200d882000c002c1c03600409040b00541014007940400c0d0052001030723140f0b504156006043d90b40e02c2240d0f00602044c0345040100080160041e10026000c650315000c0c0c2c00a0038522140e440c0e0000e20b801c03141c2104920308903c8406040c015060020800240b03104206d000c15420910011841506e51621581990300669044140c1d41c4007008c20411541c001b030303558006050780c9154038112140104c0c040c042100c4064003c0c82210000703402e204101c034030303403104020a00c40358000400544500d11108154828000d9a105814240052080d8680350141070261030050707001c2c508080c030f0300340c058600c030704032610403240314514000140b010303101c03881214421090b158001140d1412035650008885841001c0102134000c814500f0f40304003415080c58181680c86000a64490701c400300c1811801143c0103a03d00d005200180001c1480c0c10181c1c40c000d80c081c1500700f040ca90303a00f0040d645ca10445c03003104194105103002512030f1400c1c140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 501366492 1250 501365242 501365257
    0x180702030f040f0906060203030f2d090601090f02040305030405060f0405031c1d1e0112020a02071d090607050705332809141e010c03020a090308 64
    0x4690800c0c90100c1c220410b50002d40100054002c2c60504000d892518020340005044a002651860810881c00000d140008090460344a09542c0072040c1c1c20090b00364034031600ea81c00f4450520b00340030198549421003842440e40c02402d0a0780d522404079180300329012641d120000f1460949801d080c02065081804c617400c50302810710000503680c806002c1480c00c04490303514002868070100000d05402c10f00c0e4600030304a621120802402d480d0030040350100e07001682c202202015503c0100c0d80032100d40308403d2014000308080540d2500018007030150340840d072a100b0080d0039145000091602114403611940c81300000c00c61250040008188850045043d121a81c0b48031001401c0e509048600104141c2d00b2101c240c18003400c032140715041040603034110101e0003064050406152005442c0320200d03030300c1d030f402c0c401c10110030070b50016168010b00340c680303c168180c0d10300044509000c41780b0f0b01d03508045080d84024444c0c130880d500400c46403100c49005045441d4611275410944 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 501367742 1250 501366492 501366497
    0x203040e06040b060406020a061a06030a0b040e0123060d080301180908030c0702041532040507090509011401051b012309551b141807 59
    0x30680f40305900e0303050080024003019002480301c07165a16000045484c15041103c1c5140100c0c0a80ca282c0d0340e4004580e00000380c0c0001082c251082c1e4001001003440004480d11903103020304140e0048510360080d0f00e49501c07070400410940d540400e00005044a42005220300130400c0140f10f031001c0c2c0c2c00c200301d40007130b64680024001450f80d5009810ba10595a4110500002c1400411854140101d84d00b0341045001505018501148403820721100d61849019900840d0714024089032442074904400004105018509003500c0241002c00f450083c503019503c040c0001c61180b12110f052005190107035034443c505410b8010b40740e0102645951412075540b110020300784000c0c0960f480e00c414000c003250840c0c60518110841c80c1c64100320102b00140c0c48800c0c1c11a184441d9a0345100f049030940b001c48030004d040d8001c12030240b1506a1808404010a42e80c051000031114030b204138100a201180240d1601040d0354614811548680c3c0f01c49941003410f0404001ca403ea40c2164890 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 501368992 1250 501367742 501367751
    0x3060f180703080304210c210e13020301050f0105130302010f09180e0d020c0a0b0d14010e1e220c05120318040903080c070c1a09150a0203040e0604 65
    0x2640c440f40168002c0e5400d85901e446041030f80e02d00405980d40d541c11442c03a0600c030201d1003556032441000c149004081d254400341d000c0a52009008520841407840020291080401c0480b1901e009420a00505004181441400c811035000c1c4044400400c1e84401d00803000b49154011600740305404500002c11000200000c2c2910340c03100c40b480003010134078000c211003c29503025842c001e0240c003103c0c21135200c05150030084c1c0714800315a007980d812043c07941d55071624440700e0010303240856401a0b00c01042000140f028140c8001038040c080c40c10203094643e4a98490003072152090760b01c4441c4615140d0780403403c40c0b032000d2400001c2e2007408041a070035902e00c0022030002c03240d844000340d41c20019601c010422290000e02b180d000445080200c1c0c2d600b918000c00c00c0c0d8005009440340c2e200020204140308400703035210700401c030645519a40a840e484070313071555041241c2e118003a000301c1c1d010080e41c122290941e00b01049070b41c025410646400006510300e08043c2003a07401c0780e9079 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 501370242 1250 501368992 501368999
    0x90d03080a0f0603061e09050343030e0402040b0f0c010e15070806040218010c0c0503190212010e030304080d0e0105010f031e030806010e120a1a1014040908130f08070503060f1807 79
    0x66003092b01d48a0035a07070712651040580c2000380c515484d085c1005d1150b031042100b4030881140b403040c1e810048007074046030744400daa00451801400a504000746900c10000d441c0340e0308048141440c03041249640d02e040340d48070a802c0c0b0040e401400413039164800610001c0c1c7c1c0035441507a01c440b595010700c10b00e0041d5279490010034144070320350482c12104c0c445210100154200140384420200d140c1d0000c109a10900c6030141c0c817804050001040b01c1400500f000400119820100d6010700a4000300242c0d60741c1c90041c40703003102c54407040790f070136540724148071207061800780b1b84540c90317090b4407211003940e18080111405c200c030f51401d84e8020380000251151140401c02c0034035030391184565001d600c0a9080041c03a52a008220352800c3c00031860900c2481c401001c0e000803c04155400b03d25802c0d54584000710340140128240490b07210640001c034000c2104074002100c7c86181601c0700c3c41c4e00c0e10b05140e118041100d566501c822080c02140414400c1c42185861186580558510549 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 501371492 1250 501370242 501370327
    0xa0b06090d0b070f05090f151210030c060f02060f060315130b2d041401090309030b011a030f0603011e021e090d03080a0f0603061e090503 61
    0x880c0300041c0c1e55030340d00404000d0071907006034074011381884900b411030900380c0300c000003244074007801409800340c084220f00185040c8104181d44002d98405043c1c2c8179032070030f400c04152190440c071041c0e0fa903402c541d000041d418015030f91038103206080e902800b42e6a40341a11071a2892000d00751540501ca011101c100300013143c01224003e042c3c12264124070522800d103820a01c0015102c03032072803103800c1c928058211000e00403903690566031400304c4082d40c03141401860180b0329000030400d5400d18011000309a8425224020b5a00c00c0ba2150f400ea600c1e19052100c1c200d260840307500300b01007007010800041c0301c404402e81c00940240045501245101310b00403c05032084081001074001c00c2c0101c030102c00c01682000142030300313589800c1c0303071401000030300381d012020000d0144403030400815501c4030030b504008011091402c051107040c0e81e03447c4c61001811030115000e0501c21141101c1d5404420307000b05d05e80b068010b0000e5041a00421010041030002228150f0070000011031030b240b2503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 501372742 1250 501371492 501371509
    0x9030e0607060605040b040b0607060c031d0c0a0806060303070221031204060b030a030c0201030f1b1808062703091503010512121e070503040f17150a0b0609 69
    0x18032541c0c010441c989030000b41701c01c0c0c907611480c3c107114a003062581107030b07a2a200d007950091a0050008258032038050700a42c001c0801481c40c000c000c0803503485d00e09407030b00003035403640d548010390300004121741d114005922850240ca0444e4141c000b0000743d809484e0852400902101081d40452400b03401c20501e403460307101c5086401c44009070310402040c0081d44c4114100d0000030323009442c6c0b0000b503550003030020510f0303840203060640d1024452050b401c254003140313111045411002c0305101107140640040000d0b40e00c0d031186154514085640e400100c2c50500888180300460f10b1080030b6202d1b001c220003000f02d0f25a02d48028800d1381080d48e20441e0714024200813000d01985c2e541414144029203c3c100c3c141c0303259600280c0300d02c580b111040100c80c0001d00d240b4840200d105c0c100000c4071140b10714540a800ea210118000c500c07241c00c400b401d02142c00c41c02048a0301d546000551303880d414041072040840c0311800008450301940d8001000d4090b006000c185804061700003e641803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 501373992 1250 501372742 501372757
    0x9020a03051b030c04030b04061b0809011a061207111207060b042c10050f060405010e01150302090d02060d1a060403020a03330b03060c04081009030e06 67
    0x103601c030402c0c800402da0600c91004090480540940740d03141c00c407604022032081744801031004a0703060004e41400f400d94448280043d03000c0081e030500382c100300003c080d0001642c058040d5440d154a54040840903c0e00c00b415000180c00a070030580c00544010f40120000d16800c00e1241640c02d07407400a0301806441008a0ba16480e5621414241007440403614600000d41c0524a8480e903400f001081c040ba019040110380d01d10507541c020010401d092407400302e031000100b0304150038001c00303403030807491140f1402058400b04056a82e44903c200082c000f0311446d1a0208070902d1405841c0c0310f43c005001c0154094240c0c4001d00c003a034041500340e0b10a2105031680d541c1d40b0000f0700d400010300c800d00f40d201c0c0d045420b01c0c00d0900b55000540d41d5032292000030210076803018084100988000010440910180c8120010001803002c0015105202d50f0a10030301820002462908801e804d07581509c2c07016000b4180a120304811354000c010306801601403007040600c54005603102001410300703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 501375242 1250 501373992 501373997
    0x605062404081c0e0f030c0d06054204111c06090227040906060b0c070905040c030f020109081002040e0c0a05070f03091211011205101202010909020a 66
    0x99a1800c40300e40d041034482c40c82e0703004003032843c0300c03284815a0003100303024524812034811400d8003800380000e240c09458002d031500040700d0400c240c24046940e00040c452807103606142e00e0015620780d9141401034142c0b2042c12601d03207014207404902c20108510081101a2000442c03c009540780070407500004c007001c00c03161007207103140d10b5200d05010340001041d12034000c3d400d01d080311160f00c50070285111010031201000100c22100c1e134568200c4901150031220410a45444440141d050b51010301407448a00c107407000010100b070342b8400c282c80741d40c1051800c074501d03045a03036040d03031624200d00603410003440002c0031030410401d00143c0510700300d05600698451803c1c1c0c9000250a0090411000d44000e2007000f014907008000c880e80603234480c1d014513050b4118036007543c03941c0082d0440b504154500340000b041040c46815244000c0c02621851081d58800c1e80300001c4c1c400c11103c1c03000101400c1c0341004035a4020f039003000050720505040350301c540c8640015040b0b81040000000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 501376492 1250 501375242 501375247
    0x8120c0405300601030b01090905070506130302121f020c0102071407080d0c080a050a110d08190b030703021002030f0706050f160e0108041109070f080c09010c06050624 74
    0xc404540520415900b075008068420707507165899400102c6014450700c0032040d1259151800c100c014040103024140052010b5100e6106500c41103030752040d808100d0048001041c1c0707508a00000518003200001c0076101034540c811042104040e4114100c0e10b0007541d000e00c80000000c8890300d00207a0349004070f0041401030700c5d048070380f440c0c0844042c2c5003060101002c55103021070000000c0790440c4540e42001c0d84d85841c0c000c001c0304c0c1244100c8860b10280203944401610540c8614030303c6c0100000c0901105204c040300451044410b44048039605500c42903041006082601a48000800c0750064900740b50480c01550382c180d02c400b10071101c0036519810009031f100684001600f0010440440c5003071100144040d011901a0200a06001c4c000b40010100045002152100748019003a441a070034581006054480b9030b40903d0041507802000410020301c00d400c0d10580c090580d1042302098854440000503c80503210039042118074040b8160034a000402c8030014440045055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 501377742 1250 501376492 501376549
    0x60f140603070b1809060109050901030f030f090803090f060d0f020714030703200a020a1e06020d021504021504080a0308161d0409150f0b0d08120c0405 67
    0x50400350aa008140600003d0102c0e13968030a07000c8841e01c10741d0041e42c00414507111200140c84084080d17002135072010300d200002c010460719401c0c84500d544607854007200d0342d400074000c0d620507049000b8200e10b64410300885d58985000e0303040f007120781d00142400b40703400c82c03400b015000d8401101d1907043ea1600040d034001003009110310f100050104c44040c600f02046954024994007081300f000c0c101c2050102d807222203020034000040030f01e0740108038580e855070300c011a0a01402c1040b501040c20300c200e8001903030b10300108200440c191981e003d004003001403800d0b044c1075100500700b039800000c001070a001081c620340041c00540142030050401c075a05150091507110000c00342082c3c1c3c1540c0b098100c0c2c40b5004030744880800b01840c6590280d2880030003040081218410180030301c03400182102c000b00d80c3da801030302c2040d4547c80034041307000404180441c0812801e0700405805003000603c10301e80a0340010b5802c0110035002c4c600c0c15654800041c1d000ca410300c10300b4041900041d00a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 501378992 1250 501377742 501377749
    0x12062d0b1e060f0304080d140103030e1504150c02030a0302150a0e0a03030f020d090b010f0801060b0a05031f08010506120606010f050f1b031306050f030c07060f1406 73
    0x12511007080300803031404034600304007140c054000c07000060401400803010808020880b4103450803003100c60700030440d42d81c03481c1070050000b800388400d40200d08000c020101c1410114000341c81c105003080518509440d01b0400c01e07200f48407003e050104140d601c0000e0059809000000d1103e00946c000c1803000b000f5244048480c2c405854424914a4095070b00030094010480a00302909400c00040c00ca10010204000e03100c1c3d0740c0d1120b25240751502440030006d0b04605541a100030340d23500c2070ba0b01e40f5910800e0072140a0301414504542c1800302c0112b217803148006580c800844010410035044580d0f60071030300c030070f2038201140e90394450080008a0512100000352661104010452401d00900103001c01c0c1705d0303291080411400140d2404240c501204440c4441442030403103d5001c2d0070fa250740e07203d0f00001082610318404400c00030b2400e109800b555500f242c6200003524503121074a0480c80c5030312401084840c075444410554000c0100d20840381c3e48150384040300c40034a400000c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 501380242 1250 501378992 501379009
    0x2070506062b0201030b190f06170f040f020604060e09060f010c060b1c050a05060a0e060718150c030f0f0e060306061204030c03030c0912062d0b 64
    0x11074041e0001803032031920802030300d00e425544610120078814000e85400102d000c0d101d100c002d84c7e007045a1000058803120144014021a02d031204447c3c0b1141d2140d00c01c8602e5100d4101040038100301102050543d10784203041c1350042c0c0b15944403075483c0390503030104881d5003080d44540d01080f079001c0110b00c58281480300c160300120840d030320781c00c05002800181c482d05002d500901040d03506c1c691190b00d5126100300c01e00c010000302030b5035a200c20341c0c502166500ca19810407100c80c080c440201d030703013010680640c0d99001c20007400b500141d036800384121482030300e4035800c20102140010004c0c2010002c030b40392140003115918048981201e0a01800d4080d144084504000b003011201c0d4010303912030350700d40301340e081100d04079900c0c0c41e540c00041080c0201108201d1481041041c00205500301d603210b08640d110791402d000c805402c0700b0607101d4038450b1041d0342420400702401b20014110382e03c0031440c1040a49246004425148810140700b28850780c80001550340301500a40d00d801e450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 501381492 1250 501380242 501380251
    0x80f0a0b1e1603060503010e21211b03160206131e0609020301151a03190e0f01093c0303020f04031e060501060302090d022106010902070506 62
    0x1d0200003503186a415102400005180480441d58000303a000c00a01c40e41058006080080003404003180c1a660b03540c0741d10b850140820402d08614020f4030049002080c0c0b031b04c042c03407100b400301c0c8601702d0108002002d80007004008070007110782400d030000c89003002460007000101c5007000d2150074100b02a180401c00381c10000070b0a252040c0314002550501600112519140b43c505640c4103803800c02c0141400000c02503155081401e074034030a504801c003100c22102d08411085001032203085542a80c0f0054a400394003160b422001504142e4a4108803030484040045800c00310415043d0b42c00c450340c070b4000316020351601d0741040807070140146550700c00700c08610703d080605209020304000c200c0001c0040c240340d004900a11580205002da500030343c1c210018188001c691105003d01389881e00d03080312020701d4207002003105803203071003615211080a080318510740219020050f0256249803160300c1c0c1c1c40c40851420000c04103001f0a0f00030319007680e0158440b15603180039420a0801003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 501382742 1250 501381492 501381511
    0x5150901050f040b040e280c020a0f05010b010905180c130302030d09060f0306210f05060a05040213022a0c0d050c1f141326070e010f031407080f0a0b 66
    0x10208410440c10150f8002880442400034a82318440002e0b800e00450440c06800c3c5050340c0c003040c0601506412010079110240c3c2c4607280c0301c0d160010408000441103610826110820002e0160701164004180007080021641051079803a40042c3c0f0b0211030425000010310001c1007080181e4001300043c558024906061042c203045c04ca10301c00301d40382e8894250301041c0c07c061a10500c881a1001c044064102c401c7d92118078103402000d010385003c0d41d040307008500c42f000d03814252034280f0a075900c11590200f500180904210f4620103419a901810b507940142040c44000d540c803100c0e01e502440c030540c050300c4801005001c00c0202220f07240a03a10348980303406140b6490760700181724807010029814140d01c1383e030504003a2003402030f107401143d8000010362001c1c5980076480f040042e003100f940c0c00c072030644d03454100500c0752190030711450704642e20400741403000944010f02c00c005403404c0c0040700c11060340c0701c184038500224421025665040f2540c51018030050050303c581c0440c180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 501383992 1250 501382742 501382771
    0x70510050a3810180b0301060e012006090d141602010507150c05190e03060c0f130e061809060408030406180305030a1505150901050f040b040e 63
    0x152907490664800035240c0c0000d40241d48800e06141d042c42154050070806448034104035900900070340020f041000348180070880314000280e1103040c6040700d040c0e50320f9540301c0d251503280800540b4854040407140d6007404103000d03185034811080060030b10540c814002082024805107000c0e11100c545810015400c1042126590111001d203400300c0070360382807030000e54407507242c01c01c031808410701d440c0c100511b8100b496010760283d0000103844d00a000c49099a80082e031818140e81031103600b0300c0e07503816400c14000600703000c80c80320291010108213905031340340030700d035000504c0c0d44c00307050b00f1012407a200d200a00c06107007070241d110001c1c118030309003280342803d00240259440078010310040c12808000001010015190000c008001c64003044c01d880c80500e20b409400d5030003c0355140c20161920411200f440700720290740d021900b02809402145044004401ca294448011b0780e05021007005031055500e1400028030013003444903032003904c8034101b900400c00303404064100394088411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 501385242 1250 501383992 501384011
    0x20703020904020d080c0709051905040c06081305030309010c0314010303211b03050711070303090905040305040512030702150918190c02060906070206071d03070b070510050a 77
    0x80107411a0490340454011821840350703d0142010f00c556200803400c0c0c00b40e10000101841c45070000742c040d00c444110281e41e51a1100c500d0704840302140c003c0c0013164510402c0007402d00902c02590800c6000395805110655030f107884c0d00d180d1080e80c00a04980d0358a003000c00ea19070600c2840030402c450003071408154995100241101019241281c0c22004d1041c4124079001300c0d071050034800a86200d001f1082e02ca4100070300144002c480e500007040496050404d01c403000b203000d50036a98075403030340b002007403c10310908002c21b8018811010300c00100804603040d603402044503819219400259903808141c814400c0411441c00340c0103d41c00148072007586940c03a00c407540420300350507100701c250ba680ea6074540722003446408202a21444d004071210343c10360120301da03841000710504543c01521100300032a501c9804a071014001907889031007040076400c0c4100c01000d50302c0201150041901e07109000c0c02030f8000b00d8101c8a039406000b84050a13a018000c0aa000c50741e980c0802c80c0c1c910 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 501386492 1250 501385242 501385249
    0x61706011e150302090a09092310020702030a02030f0a05070e0106050409020901090513140c0a1e110d090312030e0c0f130609151707060806010c060e1c02070302 71
    0x480d401501000c8809030b030030b205014400d5054840c4048010806601503541f00c0c0c407100208880320058a54034010300c2200c2140070302d8040d890032602036400601000310581c2c03001000350454482264103000311140140541c0d420070100c0e1400f0309070805050402150301c0d00d40d00e4001140d02c83e20b10140d0320401084459003010565044810020003d6a510074010040341c0d20340c0582c010680c09a1000b602c820802d94a501145004c810709184070400d80380e2403c00b004038040c0c0c04c100000661035007050038101c00b19004480d21704080b801c202d00f42501d610251401c0c414101c24031800100b64000401c28031168000ea401005040d003402c10845081070820350301e6420103131080f07008038ad84a02010160311162411501c035a0310704030800c4810f8894044202800d09000a04599407050501092401c030b983c03610381303400350300d00d00070800e80d403600c4e00564050750010800c50511102c01641000304070180500c14411100300f014000d0030064a13118600102c42c079450300219448020203000688 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 501387742 1250 501386492 501386549
    0x103030c0b18060108060601170c040b091323070f09030b27070302181509070c0b070f08220b060d0c030c0807060e09060907110106170601 61
    0x181c100c03010402640d41c4801450a58200182011243c4640b600003d00c001000c030344a0b024101c00d0380c1d4214000f00c04240d4500100301500c4004038054104400c1020300104070041c6031190014010185030460075030480c0482d140340c101010014031106070011417900401c420396000080d814240c03810103440d04000c00416680c04000c101403850b0f00440c9071000000d003000300f0b4102040440703201d00c1c1086601e5480d44002c0c44101d01541c003000b41d283c00c5c4c044580304688558104aa2a520f0125007000c0100d0040003404800a0084c1d00e08201301003241e80785201c1c412052619504841ca078040001004010000d150840a1919014414801c02c000030b0b00000075420800d00070309a29241c001640c407030424280101050000400002000f140d22240011038401109482c2030700e50300c00d0281e81050b1342d0241558050f0303049000070a64034206050030f410907124980126000611008a42103c0c02a080045560b20341164070728044400c22585014061100b22003000281c2c403144901e46a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 501388992 1250 501387742 501387767
    0x50f04020a17101a04080d02010c12230f04020910080307031d09010f1a0f040303111f0b0a120308130f02040c080702010b15030601120204150521010303 67
    0x2d201c0c0300102e9007039000d20035000040c00905807100d614600c0310f40d00c00c1950388184103c1d51540681003154803801e0042c0720b1202c1010a580fa1151111020342500c40200700c03207070005454640c00f940c0d801010342c29181543c8550203e01410341e0310304084c0100324000b1801000030440c0c50124100388800034020090f280001e40c181031100c4800487c10540c54007191901020b508140080000190a20700070407200841d00d4100305507225503008a9014814450401d040741d01c5e24081104000291080101c00d03081d03140074043d0b4142e683c5020301100d00d04400c2d51010306840e140c0c0707038000062520350900001408011400444e0024964003e8110000107054044c00300740d003044901405510814051481c1d802401000142c15041c4050031500341554280015868025458401d017400203039100303582030104683d0705540c2c5d020011100c8221444140909135001c5c403002410b202c0358440c0350900c003220380301c00c0c1e210080c01082450078503080320304225103030304100100301180e00502c141c03150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 501390242 1250 501388992 501389027
    0x106111b0102120c0703020d030e120f03040b07050c120309040b09040b0604050402011101020a0302250c03060c03020702030318011803170304030e030d080402090a0c090b0d0908040b0301050f04020a 87
    0x64421030081300e4106001ea5201070341062150b00c03003500b051b6010342c890301c41c03c20441345408408901c2a07401c0d40d031909844480f405501c100b00070311410880d0000780040381d11590858500c40c03000e00c086122400070b02682a200c2e8000b05000c0b00c03c0c40d103401041c01422055480078240c0c5000d8803540c14101c4041c14980c0101d60f14004202035903c01c821070010713031230f4542c001d65986400e490018020750080c0c1d0078182c881e0348800168810041122074500064000c6900303002c150035512104018800e102807041456420000480162014006401106403403214030904d1a81c4500160054069040107241041c060900f400018055121140480007180c0d000d43c480d03450703150503600003030003944c803070b41c18410071040600c0380b039011014603c118404d450045181e100c184a2000380d6124040e4100810010340c028005042c01c0406072000c10a00b46010452081c103444c0c0c210180e1141e0000c40001c1c2c0b0004c01031142c3c0c140b21101d422031100070b50f030840c0b9120740400d0080011050070002030a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 501391492 1250 501390242 501390247
    0xc120f0e060c1b16080c0a0302060714070503122205150d06030b09031c0c02030403030c0c12080d06050a14041e020a030c120608070308030405070b030106111b010212 73
    0x3c0c0c0e1030300c2d410340303418401c10125182501d038101260300c018018850a5103610440c0080040f50030110003860803641d01901e41070814213aa55080d085588811040b0014440d000c1e0000c0c650b901001407103c2548062903440d91010b1904070342c0c02243c24051549101d91203c0c8003000243c0740c0c040118800b00c2c0c000c41c684e440d15001501040607105960024000c0741e0304a0900c9001d800c04001032640c000003083e0342d14600101408076095408580d403c4025800038041040403a0080482e140ba0034410600f0499050301d5001e10b4a00707201001040e00c00040c040b0302c144140099208020242c14201c40e8801c020f4503008d064507805c1c40c07e0040c2030045450320140210305050440d2400d041030314210641d02c4205050f4000c00900408045100184100d14162038505d070381d11901003a00e01101c003514005055031200c01c0e15a001034400c41d05449101d4000582c00481c00146000c0c1185030364601058010030003a0b480e01030100d00f4282c04481c5c16082019581e0009451185a1480ca05c19074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 501392742 1250 501391492 501391507
    0xa0207051606210b04050408090909070e160504080f0604020a06090302060f0a020c1018091107020f01170703051e09060622020409051b0412020402031008010c120f0e060c 75
    0x30f025240354440c0d45d8000e0705060510080140c03c0000e80341700036007612101801c1d60341185069075801c0d140720b01001c0c1056600810011003205900300c0b0821041e042c424902076480d41c8892074540405000513071a0484420b000443c40d14140c018004c0500b860898801c60440e00012040d108e00242d501d404c020000d60001020300038804544800c800402c1c4602d08402e80d00c01800d2401010380d0004011111074012a841480d17224140c0c20a103120901c90801074079601340312684a6600f01e041c1800049041003400c0d50445825600c61405a134002c2000e0404039000c405020200c550300c0d10b1420301c50100100044005075481c1c1c04041160070300c0800803800222400e4045030402040028000640492010b00360340181d405159160341e54807030070a0781000d40d2003500690080308603010591001c0000751030140c02440d082401100080022a500c4841900311040c4582000c0458160050100076254500c6040100610030800340b01680c4d41d1141162500c400a01c5339003618004518603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 501393992 1250 501392742 501392807
    0x290c030f1e0a020d020106080307050c0603060d081303031704080d050c0c0708010212010807030b071218060e100501050d080d1b1d03011824050a0207051606 69
    0x3071180c0d00c03035940c81a03507403006507100a481d01d030382c0d000c075a02640c2890300014150303c00004940c4006c1e08407026121f81002c010070032500364005400c1d25405941600d108020171030490043c4528001220001c40709480c6140203000741c138006c0880d5000d050f9100801005c02d292804546043c00c08020014803503540c1f2000349a40e0148000400740da12075040c0210300c4420540c0100702d0203000311400c2110b83e0341d480c00c0350754481044c00001c003139070081008684024058141c030440720a0340710001c81c0306201c40306e0740b0324401a48501903031250b45560003010800c005001480000d01004824010740d8100f0300828018155100000c018400c0000c05032f050030300c20381c4819034500880312004020141d00c040101f0300c0d14410210700d02c000c4861000c07240762405100c1c13900a14030b00c14509202042d1130300c46901c41640e803091003241c074403e42000804800907200c0d161040403003400040e02c074401800e080d40313400520603010700d40c08080740e4240030564000800c02603024461032122149807180082 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 501395242 1250 501393992 501394027
    0x150103021c080f0403110306010f0b1c11030103031b080f070201030f150608070801060e0409050a021906030e0c0306041112011814031e1605030301290c030f 69
    0x28008000110740c1801d03c00c502d2000300b04882c004c10382c200ca4a0076070410543c48600c20710520385001410b910810040c11030001404a804000740c00b80c180c10204400941a28801024403075046e0000006108040d08007400c11013040c0800949011250103548804951240f07400380041100040b807020704580c401e411440c08a51040400e20011640d42280440c0380c0e028020311010503030840024580d203200314403c9049825950740c6040b50902c1505000080500080684040c0241c170300700d00240c0c549140000d010b000c40d044500203d850b144008045036000590118150403007c3d943c80b25a0f0b000880640054004a040c1401d0f4008000500d143c1d0b000314404c0c02ca0750034074956072505034603041c1050981d4094828017000c00142814180c5900c01c803849482441404a54080300c41801005418a0307007807210854403000c0107455040c031b590030907408001603000c80c00070351803028004a141d0400d0041584070078203004980d0072031a1240160404407910400200d0b030190050040d009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 501396492 1250 501395242 501395299
    0x507030c1512240e09010b060f07030e0f040e0c0307061403041b03140303040b0609160c020a0f0801020d06090603080d05060d020d030806041401080d2006010b180315010302 76
    0xf00340f0900d68a6200700d2000c00100c9524860354038182c841d0069007800003c0f2001101e44100c4107140c42c85c01e5505580d40200508104e400c40001b400052a03512148150241c94a0798401401240c90300c1080500d810b403260446410030000c0304584a001d0b94290940e50095802056031001049900e0b0b0558184183d520140500060301c142100461000c001180114000e1040003516130b1906d003032003400c00040c2d40040c54840001c00603030f40103200d910541e44451000780f100f1589a552a1509041b4055070803c0f11640d500042c0c042455109100d400d0003030400341c03028840b161031a211030b8201c0c003a40b55080542929540068450380d68003592030f031819802000c0c080040300c41e00380100a90b00803102e480c0900c0c60a01405664560000124102d4044000602821030400c200b210351242180f124030b110480038040000001b0240300d590301900103c2141d54842c4900181c100245241c4c1a4103070183d003051080c1c0c1c52000c020f14a840c1074070740540d0448241e800d8403c84440d110322000b0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 501397742 1250 501396492 501396551
    0xc0619080a02190c0308151503040303090804080c120a0308011a090307030602120f0606041a0c0d050c15060a0311060d1d010b1507030305040302190507030c1512 71
    0x44603001843c4c0c00500d0501814080e9030303070032803e9aa40081001d0f0500b24003504e6070003080a050420404285001503034054070910340401e1134503465807504d03032035082a08010060341200444a0342400c052001c1c1c1c0c01c280440c801000c19400c07585001d49803a030180100c500c2c200000886007681401c003400c50b02c0800d0040d0403110110382d2410128000d4004580314424005c044022600141c40d0911076809a40020003c3e86410700d015000304205002113a5031298420600924000726820701126401035056120166503010241c20b0506160410702c00402c007564400501c44140c407080c0b001019641d01444000c2c480481c5400280c090041c0da00c00343da524106540c1841c43c1134140140b0030521081c00003880301c0c20340a020015080b203003072080310b12070340c0030300454010030310075041150820b00070b00564001d52000f1441ea850464050340c242c40301e42c000c0c02c1c10801c000001c801c02c4014070183d8042000c01110707420050504600286179030b482138980c49110324060b0460105001000580d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 501398992 1250 501397742 501397777
    0x120a120201020306010801061809050703061223071d0403031b09061206140d060204030f0602070308060103111912022703060709170111030f0402030c0619080a02 71
    0x1500074040d500840300b6500150b10540006006c50081208198003018002c1042c2c03014108030456004100041c804400c05803114400a50440d02068042a4500810f450302500d03d282c00107800d0040c01182c850b041d9070122200300000c20b5020406071280c500302168030625111403c0c1180a0100e1205d00b1591685500d0501145a00180190111516500d90340b02d5000c00c040001c085502034440c4c03500d26454040c0000d114501403002c141d031148210702c014241038603030b100c203031020302d091f13500f107411070390008441c0d092540181c03000764481c5091805100c030040450f10045a4024000c0c0c6010310f414666040c1401c40c0903a0340c240712006c242c2d00443d2154101d0034180e5504200300e080313100143d0007502000d0942004103450748540b05948440050625011b016040501e80c44408002950b0702d042100c45c95101c88001c0d4061140703550101143e0400e40101414401c0e10751107240321b5201008a0710610405c1244c6072070300701c50f905204441d50b07107541c00382001c1d120b00c3d0700e40304207a11070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 501400242 1250 501398992 501399023
    0x712020c010b011e050a0509030a0b09070608091b060931050a020c1c1404030b091902011e02071206091b050f060c0a021f0f1b02120a 59
    0x158854160342100f42e070360075804003000013510303401c51a0940010000d0020814000c2d6103019031300408015602808640c81800c0c4c0f500c43e02d04440e000d540d020001c0d000a00100800c1d40d1002015400c008072101400511003050403481c0c4403980c000d81e040c000d403004a41d1444541c0c0c2c4c40d6038021904106810500101e40c0c0010144110500202d8000800d1030680450901142c510a0720702400c07401000300403880032522001030050006070504108180710004014864a09000d04003c52040100c0041c0c3d050010700a0304103622030b44884500712107090a0740c0980e07800340032080e4440c0c8944800080300302442089082c842d1a03001007080c04441d80c590000c210302544400c941ca80241c51404203000083c01032403480d0610702c28994401503020700c0040741c1c075080d4000d0a00b41e80b59000c44108216981c0420040c0c0001040021900c01c200651204181c12110b408032182d5145070219585024000c8880104640f40010340610401606007440d0481004a9500b1a4100c20901c445190 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 501401492 1250 501400242 501400267
    0x50406050106020d030608250f09020d0b030c0a031401060b0313051e0304030611090405280606230c0303042108040b07080c1b01020304020f060405100305071202 71
    0x30038400e210040c0310303082044070300d544a4480c81c0c013a00c036a1000340c00600c8072200792036503141d04404003250741c030b00c4100c0000d01048186642d000400c45460050b854082d200c902c0000c6903800815540241c0002204012641d00c156500c42501d9200f00c07103e100220221049005018641040c64088000014050701c51401c281c1038444500c00c0044400002196003c0007800d200044a454981d1082c80140000b501d0f0340c004081100c1d0f03111946044c500e240c000030741a50710948100407507058544151345c50b80c01240da070452401e0f0002d400c0c0305161030088020511801c481150280e0b007044082d4001d0604280f080300c4015281808503030300c9050909012041d09003401e1388440445a02c1d0b0f00c5c0c81c4040c01034450610440e040191606d155444020550340403500908140ca102c000b0031078000300100100c0c40003504038401d40016143d1a041c4184a403916624211501c0b07007606010800940c1e0741c6d030b0441c2011014030320780400d051b00c030210241e4043da01c4803058241c03580082083c102000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 501402742 1250 501401492 501401501
    0x518030a050913020a0914130911090a0209010c080708041505130602070308030a0c020c09011205070e060d12020c06162a05150f0301080303010e09120405010c02060d050406 76
    0x600031184001c2c0300d0001e03d4250100d22030b62126a020400c140020000e1306400508918040ca01130080402003c140f80b0180844403c2d00049480c141c2c94610888141080c4501c01e40c4048071000c11450051598006400300750701d12002082e40d080054000c00300208501a0780050001b2145035403201062000a8080d822100424410004815001038124030024201003100d0300403424602d191584502c5401401c02904820198481c0150f0304881d0340328002c1481c000e00491400305030340d0845e0f1811505180e15944481050310900e0103002e451359400304245545588081004e044d10078040c016030428000302c107100e92003403000c40c410400303c501d0b200d07018080b0722400c165011240c00307480c0001070a0720010400f402100c11081441541080d507030fa41040c6c41c405520381d0500085155041170740d44242c000031b40517000031004000401ca0344100c0c5030032400040140c52030f41c0b1a031030364030b00d00d006511450741080148150401551900d5049910b41c0c00d00b900709100500d403d082400141 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 501403992 1250 501402742 501402757
    0xd02011e020a1b06050301060e030102070c060e04060e011410021618050901050f010e1005041b020105070207030302060a110c010c0f0e0a050306010e0403031107051609050c0d0518030a05 82
    0xc810f04103050b003507051034103a10141c90b00e0f900d9060442c1d0a040e000c81780303101807800482e05503600b0020a800314050300900c1008144641d41c004880070b540c01400140ca15651103545001c01c04001401808100003907150104010b6440034442038030100120700d004500c0c50003071808103040c603004c42c0c20f2a0130000081d80c18040c000c14081a292201c001d4201d40f8122410303e0110241001449102c590600c11a080410102042d0882d0b4907540050204c0700c00c4201d8640410300209600300c0c040c9c082c080d69900c042540082d250f945d00c0d50305c0182d00e0349802081500f01d035a0703804401d0003c440180039109040d003854000c004034082100c02429040e6070894a50129215030b614000714034110381614280c032805000340c01203034a004040740c0781c00400f41c000c6062644a50808095083d508054503400740108001c1c010b5034000055803030007100c075421601249080c141000140000c2c401281c1c0d00c600001000074843d41c41000e10780416150b00040a00303800001035441e00c3d141e100c005480d48 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 501405242 1250 501403992 501404003
    0x31002090a030b160f09060806040b0103060b0a090810061a030a180614090f03040e0915041a01050301020306100804260405011b0c03020d060b060f070308071d0d02011e020a 76
    0x8030b070400b4015102c02d1b95610031000000c2103034002032160309168010420a01c1e06040c003003540c0d6221862080300c0d410000c1c1600008600060401400c003080000c4081104034400c1001120b0404e07840848000362140c0c0800d107824000080b1f070381c1b03c1b1141d0026118115920740365000752054941174019001e05003000320409503000200d00031240120f068440c4000c4140103500e06858420f9041c034804004001f03000d58060100e5070380c4a65120030045115502c0b41f02d021198084180180c000c4010680003075020ba84148200005030304c079000c4003803188142e420403034195900c031f150401c4564a252101c400034040c1b4800005d449586d40040c0c01591400d80b1441c2c40040c04058403800d2000710f04015003141401c8004102505000c0e11000300c081c001c15010540301d04060104034594008a1914441500012038405041d8450700d000d401c80705914110302905002d0029001d9403403190107180c8112420842442160301600d480505101072503400065080c019001039158004000c00356034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 501406492 1250 501405242 501405257
    0x50c0105060a050108061210061403100c080408071104290303031911160c0306062c0a09060e1507091d0a0612060b0a080309031002090a030b16 63
    0x10907103002160181a95410f03503410070f80f540c1b9031007004212455600b0032a002d01511100d000c014106004804c06801b00150014590001005240c54a200c20550007582890803240c0c1c00050341c481d8405402c2500243c000b5124074040c20004482c454000f0030550041c64540038215814500c0341c1d141aa080d1703c41c11034002203c0038145500c0707200490322100c081851103074041c400f48090b0311110a00c885900d195040000b82000c2d507030744500c5100d0994205100310010020880b0324010b200103400c0c01103c00b01c1102100440310a91035160907140c07044042e100c0010034080d42688806041070b000780c0180000e1400f104540c0e1103d440c5205101c10034528000907498a006100c00030840f50818402c0c00755000c02031030102904400b07030006103211340314600010314100500c0350960050041c2c0c00000d01d0681441000101c800d9a031015140f6041408280400d50f0042000c81d52a0044140580d0350240078002850800080d04020892100c4a0a11802c401490501c2a222426444460 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 501407742 1250 501406492 501406501
    0x270807080d200a050d17060607020609040b060d02070602070b010b0c0330090303060f01140702010c0c090504050f010b0f0904030e030a0b010b07020a0e0915040f02040c050c0105 78
    0x6854410a20300d14010400450200401c95107010502180003807800c03d44261501d9981c0e100d040c00e80242c0e000c00006d08851101103100308103100650000c900321180c0e403070501c0e0b0780d000c1a01c9000305d0008502c0b40b0741c6d4403910546516514201e900c081d00903441190b0b201003502e041002500101d00680e1451002e2002142900d01207044540049595000b10304240c19010313000c032a1340008030941e104041115850155403014104076000c2c1c2c02e414051030301d0327151060a0040c184d02d04840141002841c0c21904030708107544046504c1d02d9028646154900700c0c900b0024820400c83e030202a4182c5085c0c20842800004500318248600c0a0024000100500100704000103230805482d0700100c2100402c002034000e1040122555000c0c1c20303a240000c10351600c907841c400c00d0740440c610000004842d02189040f8a030480980422551113140d410a04000e0f95140c0311100d50004420300f11020a0a101001c00510b000c16402032041c40001607884000305640c2005041c4d100315800d240105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 501408992 1250 501407742 501407759
    0x2d03030a0c080705030405060a0302071208040b0a0c0203160f020a0b0708090603130c0906050f060c0706050304031103040f06171302090705040905010e060118080703080a270807 78
    0x21a041a810394464003814016114400302e684100350032162480308100006503602c0d49805060004941d480050b00c4400e9810100c07038810030701d02e01d502008801c60800001904a100003904880c0322400010240009a0164036502c80c0c00000864409000780c20380402c410f003440e066006100b82d03054014a5a204284012070149420051401c041840041c4180c20100051a802400350f101a035906040307445003a10f00084d40c0105420b203845500a0010f4180741100180c540c41c02e9a940b4036041c1c0b012241501d0300440d000d01400c0040000108062610507080c00300316066400a0340e40c1c440c3d560300301002c168003c0c4907840c0414929800030b0041007814000c107129500c0040103918050300b40d03007040710340354008000200b880000c1c04040340319011441042d0203448142c0e24030090381080390024005500c0058108030126529000f8464482c0110300101141e910069141c0c5a0380503d9007a14040984001c800b80da0400303d2080020111028000040720150340544a1058881090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 501410242 1250 501408992 501408997
    0x50c0a060210090809040920061606090206040503061e01060c02010c240e0a02031525090306050a09030f02120406080406021e030f010504091509030306052d0303 71
    0x14180035800031542402000690f41100000300d1148007502d2034407400a0010b01181c410a0003a5030903c50000f01c44030900c943d144c1005e1a000880b1141d013444c0c041d124902c00c440e0b55a50007054961100826400c548030f400540340680001810340e44c5602d064007030300380e22032101c3d081c9010300090384000281d040d01900788040c0030346d0103035a070070f481c81c01c0b985501241109031034002c0b4640d4188807400120000d1344c401c0c4100000c804000c0d003011811030040501d80b4140034040c18290148070240010450890710f64480064242c522942c90190034000f60b07110045580b0141040307003000308001e003202c11a445400568865118022526074070a400c030b035154132501000d0310070744040005100d81401469010f501030301c121030142c42c0038000700c0079894519042c00c10490b0380f400401400201e0300c41c80e58032400b415040e1010003840d00191100f041c4050b4920010156039603c4130b114003814400d800c05800b170407000c2e000c10040818150050421002e003901c2d44003040e80c142c2c2c0b960451402004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 501411492 1250 501410242 501410249
    0x304140105160f030b0a09060f260c120109020414090f010c090b0d1107050a15090809060901050c0d09081213170316060204051002150a0b12070e0103050c0a 69
    0x40f01858049010010b5000341001c510f400e600030601c4100081c3d840c0d50b80500d00141a407416100b481c14907010816010364010012040c030072105100004400e0000904020541d00407101c501444903074940b13160040568801c0a90080d0402c4109501c040b03000032004d015900800c01c41c0d0b01c0e035203800051800ca03003643d070555000030361403181040b905440c10040e0464020341c100009010545407101c1e0032683c45494211115040f01100b0070900240001110b600b0100d4901031010301a6640c54031024810076011a100c0c042c04288050759911900541d1915502c1c1d90488201e01107070a009440560720b846a10341d10710136200705200010340d6200782c075550b0111f00c0c5803c0d00b00e03091100c85945005401100c00d16440140940320280000e068040d00007805210300582d540d0910041c0150007031005c0304202554060002080f5504105900c80d622104084000440811000016032104017030004507950340f00320440030448000721a0150b0499102e0411500e8040c004800e101201e0118071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 501412742 1250 501411492 501411497
    0xb010f030c0b0333041b09150f030c0309050607120b010509030714030f1006030203010605010c0b07030f021603020c040c180e0703021306120b03011107110609030102030414010516 79
    0x840c0710104c00390400ba0500b80c2c06220740ea10318000b42d9400810200e07416803184100340c40f01ca002c514055a004000440504145a40787c003108510b032001070000000e10010360100350f40c440151910503c43c1e40064051a0302500703880680c01e100c50001d00022044101c0d00f44149030444000036580034400f11031a01c100a0003410050b443c0071110310754009029969038050080780c103410001401406801d040511152000400c03500b180145821180f040d003055051090030a55800130409a100c0b05911120a01e00400c0094442c1c90200283c000e0a0b030000c100e05103408600101a0041810340c81c13550240d404006002000b642120100214549081450031404007888003d03580b6904561050031801c1c054038010a005545420414551000e0b000030304490b03608801608070700860101940881c024410313074222003156411441342c2100103040c0060039000c5111070b21800e007501c44444008000b19141d14283c02c00c2500e41c118000d146c103c55103004009007961340744140d038080d82080766 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 501413992 1250 501412742 501412771
    0x130312020d090f261014100801050c03010b07021807230a1b050708062517010501050c010b090a021b060714091c0302010606022e180b010f030c0b03 65
    0x104c1c1424000d66000d182c3d05240150804410b0b00f4400d40601d0107540b00380c91201daa18602104100300740c03a9641c0244080c0d0b4140801e0002400000b0140c80c1524070520050780d413400c0030710016500990200691031401c0d0358200700642e00e80c108100040c0111100100404070f400c00c941c5040300d10804c05914041280d070b000908810282c01c140c0d221640c03040c02200c030426111202d1033b1404400700c400302400c03a8810080301c3d082d4100c8004490b5000c3d582070412040c03060f08101c05510b0030501902b81001808a80c02810540035086018861406403268009041405200340030b580301401d911034150403000507100100c0000341c03080c41250b09a656155088503c22484d9143e8044190913620402060380141d8246100c40c80324071041c4250000680240750843c064100710131004950000c0051245090005101284d241100760455100103000b0000340610422880e0f403ca0103040c000361480081103200c55a004c15003524010b1981d0984141d0700c1c2e00d0807007180310841d0b0940102154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 501415242 1250 501413992 501414029
    0xa0e011d0a061d060103080a030f0203090a120201061e09060501050c0a02010e120102120f011a070206070303020f0a030e0601050603130219051305060f01020c09010308130312020d090f 81
    0x743e40c00b09540f0000494140c41d5181402c0e1a1854054203800a8800490004070306401366010f2140fa400e61030072102c15400c3d841c00710000c5817500d140c010050300a210702c5140c28909407007940aa0060481a004080c23518207020b14642c045010740039030340d6090320340000420715602840a0b40e102c00c10810080c6203000803640110307504a005070005400c4410001101c04141003030000c2c0c04207072650120210741d4500031144403030781c02040c2c1c000010700c40c00c60413a04d019484941250042c980555020b603441c08a840d0480080c42601c144040c4004080303051309406602d50001010036288000710f50069032244208500b03480b0650799035603c2d60303007141e041c00141000c180340b40c002602c2420407102d50b87d4407004111140c14070108c031080d80f81c2d258100011840c2c20307402004000020310080c007661755000085040d103101800098129803002c030324035503402c20300150407028640c0300300c03801c00c0c2c0000c012000e541d6034000d540c46404204030203030114030103a003000b625045440c00d01e0b140080c01c21 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 501416492 1250 501415242 501415253
    0x60311030c0706180809010320250b0108060a0c1d010c1104050112060609061409280f050f1015090e100e0a020906070605130b0a0e011d0a 61
    0xb010480d18036803683d03c00c0a45030503072456035010720b01035541e003983e81c2161400141100c04000381d07007141e0042c000035400c0406507482981c00080c80080e138040080081090400b5507007031003400030028154040003160f08480407030300c0c602034240440c0610040340b2804041e54007240554844401e000820104561580301e110701c120300c2d5024580250000c81c0d008081000d6913004d0700a6480c407150078020f401004814816940142aa06001c1141074105005c0821202c1d500c2c02c1c50b0b01c207402580c0032a072061200b20a41b200d040b40c90b41d00080080030746140031301915811100c1030015203020005005100320f441d91078815591024900e0105040c100d24566900303800103920200b0411103004140714264215060003050410180c450091420b00441c0000314000c010500c0240184404225500ca41c820750f20320940c40070f000700c0d141c2d86042c1c290103000000440030b0651401d8a06001c00156664041c28031100d12200078000d602c40e060700042616000c2480303080320390000100801241 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 501417742 1250 501416492 501416497
    0x60c16080306131a010906020f0a03031116060c080603010905061801020405030a08071b120209070309051b0108180312090118110307060305010503190201180608010f060311030c 78
    0x1001015800f0546822198000301c904a80d0211426a64840f01400e1980c1043c8244000c04152005200d04421542d0180d22031000c0d1b00018181500c5d224484040f48800c419100000d4640400541000340d80c2480f0015250500e0010042580680490241d007010f004951502c5c0d080b800401498590440e80050740100580540c044e5509010106803590b05001d05c86800740650901031300c0700410308081d483c102e001040c44424607900241008000000e0002c81100754040f02e00c10290f543d604825406070049450003032141c040c401640101c864802003294840500780d0320802165035003043c1c1c00c1d02800c0c590f046401a401480307200c0c0b0106403020055803010004c07001240076a2186400f200000b15188101c40d0003c50350003140300340c201040000d000b0500c0c0d25092003103500d03160120787c807406842c1400741c7c02c50a88092509590058182256080e10314860010322641e905008006480c28007401c00306060340c81c400a03025200303004590101c91401c1000b840c513118a0344c00205503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 501418992 1250 501417742 501417751
    0xb09161a12071b0308041a071d060f03070507050601060801180b030c060a091d06130b031510170d091e050409140c040e0304052101060308040305060c160803 69
    0x3e01c124030f504194220660514040d11030744941285003094a03000c1010302038118042c0c2910944020030640c650301100c02048008800b0511000080d0320001c620b180c070035440d8030489860300209203c07100381d1150040c5441070142e420b46e0075a90f2100d6045034400002e10a203040a68212001d1000b44c2030380e481085c2c90300e0001e003124641203c00c0d001c146690006003001010a01440c42000740da103204900c800c024a81110b00140b91a01100144100c03080c4100e42d102e075661108032200350f07101005402c80c40071511080440328900a61220302115082c090240d4010140d0040d100b04100090480c5042c0481d4544400c2e0701c0c03c110313000103041890690440c0c440f0840700001201d0322644201c40e142802078120300010300b020b004c3e1030701d490118111140030701e1420460520903600402030300d040d0342c030840303c140106913420b02c0d441042500314003840187d484c01200004124901000384102d920a4040d01c02565a4401200b0f03540a02c5401140c0714028040c2c2074000f5481e5002598003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 501420242 1250 501418992 501418997
    0x1140301150b0f130f060e011d03120a12110405030c0402030c030c09010507060f0f050603030a0c17040f08010501030b07110303070f030908160b10080c0d020406030b09161a1207 78
    0xe1382c0e54002069840410b9400a004103a114807401081d5a000d005009108400b00000310000c15400121340e94102c2000c03001d41c8080086071205078203126141448206c91203101c00d00483d18894001d8240e54058800c0c24400e2203600c101090604083c0240e034810b8030040da04c0c0d170540c0d0322041b001d80c007a80130245d11810032804100c5e00001460501c2030710a003c0d41c4442c00181d0240440038102100d0000d80701038440d600038040c40040c0307580025243c69055107c3c0c845d074499051401c1e402d030355006603000700b1200c1207810404603d8841c15444141240d001d00100070090f100c60b4000d5604175090051000190005c0000414450154031801c903041f103149000141d0b054140c0703548050fa00480d003038044940a0074008014482e2181c03815810803281101d0044203807800b004150355810105031280039940c02c031507450a541c2d981d80304100a542000300e080181c54500101511400000003881c4c000e01c00d1000400d00c801c640c4d001c0983c0d4a621410986029021421001181c00c0100310b03204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 501421492 1250 501420242 501420277
    0xd030e0a0f020f031504020f04020405060a0e0415081b1005040306150306020708091f052d071b12032a06020c03090117101509080601140301150b0f 65
    0x249078a0401882c005041c0205451720603003024410090502410400d142c07269005000501060b80e5650444901d0803050820707411441d641f0307003c40c01610992094500300f015460000a210307401048c106080c4c01800ea061000103551400c01802c2c121240b4200d002650500c010b000180d8180e1001110602d0282d90035400c0f82d9039030b80c003420b0364818071044480400108401405007081e0300445c246000d461081da100c100d216000901c0ca00801d00614072848603840c001541824000303100d207051310605e008554864030f9013414801c0005c086c00315000c0401140000500300d41a940d07804a0070391642d00c0ca0801b0380701e1f11903000205070040d55014410155001400080c1480c4001c02519075408059a121880800050440c00110705184100b0a80604105200c00c00030070140980300c4c1c403040c0500320400064215800c40f5903412010140c41444004205030102200015001c5801c500900c407a6400342401e14103450303075101d25610b00c0070600080f114005050064068042e071104010f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 501422742 1250 501421492 501421519
    0xf03020304120f020f0a230a05181006020c13050612011d1501031a04080f04080705150a0905040b130f020703090e07120b010507020d12020d030e0a0f02 67
    0x500c400030040480d0f581141e1000ca5003141020300340040915401c51351000d00501d40b03000c051214410801d0740901741c4400d052180e541c4d4945044001509000e003803240440c5820108801c42c1d2419030b04030010400d180c40c0040d0301c0344001a030b0300100a01400702150806620342e21000703014050301069204070007066a815926007403041c40102c214041801c0d0210f40e90151040c10164a040156541305c0c2510040c4007040502000c90400700811030780c005580c0d0349041481d40d030b004c0e040720010b81c10000900007074000d0001850b00c06440703084500c091004842944400075100307150300d41000c1044000c00f00424500f0b80c0c4034070030514020700b12550040c5822400c000b140c000480d00541940d0105211007030542c00584132025084c5010304680c5400c3c006405000c2019100c2101856a200c91543c1941d0344100c4c10784180b65406401c8400c44240c03440c101c1c840d401174011042c0140301e01e25016007124841e001e41209001548007400300c9a402e0780324040400000c0f10203a81001c080215007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 501423992 1250 501422742 501422759
    0xa02060d060506190f030c090e06040b0d050a0203100c0e22020c1e010b0310051302060d05150901060f1b080f03070f021b010c0c05060f0c06010e040507030f03020304 73
    0x7086542100100146503a484100281080040c10380c804101407803c130303150b008a500525000c058502840c080e546c540d03110b00008025000103082c80d40c000347c0d4dc0c0100c50030001c00050082c0140d02c21410745418141c190f40720004c8600791121040017509030032501105003000d1000d4640300612600380302044103c0d6030110140d80c00038210340e03050ba00c00049140d2100c4d241c0708111017003002070300074024942e0303600c00139a444400a5a880f03005e0340d10000f050344042e007080c4503107801b9805840d950b01d81816640f8580180307002c032140301d0845542001200c03989004076800b4141e8015131141c0c406402c2c400030440704000c0e00c458130761182e0007001e07004010541e82809807441008410200350340f89016440180b0404040514030151341c000700d0301c0c4491030207400a481c07845100b1b00c1c0071254140c903800c000400202031381c046600300400240f6a41c401c0314150080248810300c408035299641da5a59007a00084111009009508003a0050000540805d0441c840c00d00a00c1180d040a0304d81141c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 501425242 1250 501423992 501423997
    0xe0402011112071407030b24030a03091d061507020d0807050d0908030406021b1906030605120604020d020616120c0b071e030f02131d13050a02060d060506 68
    0xd0b101040e801198081c00c01c114010001034814055024004492441c0e48042e0312840281174008000c0713181ca04941c2c540003405044504850080443e040b4030100e040180240c2c40c980241c0036605054002074480b201d1160341a07004000140a881040b0050300f400007158000ba80101e07070060403105403030081040f4101401d04107004101506030f00340009806001d0320184e501c13a038455001031008000554010800d50310f0300d80c880128130b141f04003100000d458407200381c10b036844c03900d144480400c1499060380b0210540704181c489850344602d49800903501c01007154000d40c0244240c50031001403d0900c00380400208944400b40c41100c183d0394459000081e82003280095243c906110a0040a4100580241e40c504050342c125509861340f42d03500444001c5201815140d5443d0f090356017255044074010044400303000e100c01d445030182200341d4950503500e91100c1d101d00200d00d07841e135503080c8001899800320007400194240d87c00d02141d078109d10801002c26982d980002041e48a0400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 501426492 1250 501425242 501425263
    0xb24070819030c08040507060311040b1803060c1303231b011d031914070b041401050906070f330e0622080c030417100c090e04020111 59
    0x184030907900c4000070024115481c1000d800c040051250500c004030b4808a144015500c072482c02190300203030080b100c08580300e107030302030782c028080003441c00d0001800b41d503080d40e2500d00314280c548588030ba2000c0c079818010a880b4650396410305004200103114544000e0250406038103072220608040042410054881003201149664a4803074030b403503a103c0c52400c2d91282c148045060503141c8000700e55504180080001a00c5000c0c4241e400c0c041e17104000c0c80c0482e0410100c5a10948421081c0c04603001441102080d4065181000c115809001940c00405010340b40c141800203544406280040040e0195030404581264480c2c2c4c0c2c05c4d4213910445480000426180d030f0b07496230300c40c0e000c0b54401804901036400900502ca100d11414410444206080459048000e003a0600d20214032800011100300d01c00000d00150301c1141c0515140212254402c0e264025040e07045402920080640740d400618042018010a100010425041170041c541086035500f107a101c1442c2c220b0b13690 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 501427742 1250 501426492 501426517
    0xc120319060617010e01030c05011d0a060c020909060903250803161d0303030109020a0318030c0309090203010b030a0c0e03100506040b01050f03220c0b0403060f0b240708 75
    0xa00800f40003c40e0030104c0c0100940444011150b2558852403d50040c600406041040103009810400d5001c0b400e2011000002c2c068407030541d841c40041c0100c0c0307404d00704030700902c02c0000141e008400418102d01c0340c2d031154051860050030141d40008854940751a0030054031022009011400c10005036114030406150880c0c640c1c1c00c0d41000c0c1c4003034480c00040800040900708030701c032600e0100a80341140c0c0700703200158455000203070a0703024000c681c40c102484641109408181548440c00501c0c240c080c0e00c0c2c41d6540743d00c504851040e1300c024022070241c0c000400100c1d910950550212013060914940415003800f002c000a007000d591202e203201c40c940310000d0101070b00e014420030040080900b8540c0c030f0700184650302402400020404a0304c070b41c490060000d0f81040e690707080d0625910200121302d442c3c403114444000d0b0014003081d070701586070003540707002011184114221240d004101c40203000200f20f000245521240c210320099030f051001e90f00140c0104041d00340980b0301e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 501428992 1250 501427742 501427757
    0x720150108010b010c021903050f0a02040c1704030c0218071215030b1b0708040b0309010f090515092503050c0d080d051b070503090a0b0c1203190606 66
    0x50009040210060308403014030307490300f000c0d400d5984e04002070f0b201c400e5050b0b800101da00810700d030300c9407103082e0b07544091700d81e0040943c0010b1b0750310003140c8640b2146c070071201041b9050004204031203649190144e0000003000002080209000c0d810303030006148020000ac07403081030b02500d240070180503100030021800701c05524400c040e035405600f0981c0010b41c00d05180520703640701c2243c0d00c0c43c00b40a20700000943c1200c040400d00300c20454520f0340c0c004c180980d0315a9210254000c030340c000c940f1006a540b810103415a420001d0042210068000c0010b203400740e80c8002d90183c0850190a030001440f402074000448401203031400a440d0b00c0503035020400b45181405030802c4441c282241c0318035400320114002543c0c1c0e505507002d60144840c0040d50390360f1038050400c0503403040701800002c1d60100e560300800800000a0910b40c02c2503a543c0702140d51110403080030b0181e18200b90785a0011000b400a51110101440d804200d0030410f040380f8140080724421109103403c502c00143d8503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 501430242 1250 501428992 501429013
    0x80d0c02042c070e16140f0313031107030b0a020a090f060507151b18030213060914061c0c05060f070c080c100e012c01030c260720 58
    0x603c5800c0c014840402c0941c00fa1504144020b0400c821882410030321044030a10b01c0080f092005860000d0741485015036031f41808203040c030005202000450005580c98039210302d0500228100080341c0d4058008600c40e2500f85c80040a074000d40141e00400400c0680000d4a61a40c2c0c24003004002c0f54950a41d580340c40d0501e0a00015240e00394242141440080d20b5801c0441e00d0000301d01841b45861203403030340380c41e02e54600000644d00280d800510300c1094005400540c1c08403088078200740f000c2004982c00f041e0031005d0031046469076070041c132055011b14941200c48000284a1051010340c41c89a22800000c4040c1c00007a4070390600708000c2070f042c0401c02e44510003000f5145000080405012150015241c0d580d4074060310100901c414520507264054602c45007001d40301d0b01a0000070303414002c0300c1b1802e00346156040c002030800419842e00340c05400d80c9100001c55481003621002e06c500c100c00b005401030150310800844140720004458018840030300344084001a0012041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 501431492 1250 501430242 501430331
    0xd02130306230105180403050d020307080a0c0c0c06081e09010504141f090606090914010b0a060806040e0f0a111806090a0f060801090c1806080d0c0204 67
    0x1d40905038080b0040280050245550f2250090131040620707820448664683c40c00301c8a6008120107028064000702c280403c3e00c3d044400c10b03110306034080341089039180080c000c417007080701c020000d86540480038051241c24822009640d201103102c0311129a102c4a0388601c5250404480084159641d001403104200c1e00403082d4220345280c1c00204403091000410a03c500014042d040034650340b60129020001140c10010081051301010040e2200c01e0500f0000c108684400b210b6a5181c2600c044042c54221190001d032001a038a184d4a9074541d000d100c0185160124110a885100b14442440108000241e07250340714040c0f0040c1065080d05000018005031280300d02d5001a2003044400d80703903c41140d512030741804d004a1540c1c0d010415000800c250b800c01c11065081003c071105118a8182c1d220851741c501d03da42180410103030010040750318500404c00560081b02c520044644610b0018107550300041c0300041d031407100941c640c14201413948420300c0403609c040b01c1055a6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 501432742 1250 501431492 501431531
    0x110d0212090a0c27060303170c03010b09060c010e0304170f03070b0408160209010b0a080a061203140d0501181d340815010f06050f0d02130306 63
    0x541c54802803100003003a81d14400480c0c1d90380640c0842a0100385900b0012200c01c24161000c00101401c02505481742001032460501030a642400d01d03c86001c100521104002c990403121444901400c210850040002d00d52080001300ea41c5d64075480c2801803100300380014801031034450030190f03c030701807401400c0c18000c0360204404250800d006010201c2d2803c05242d0384694442c000380e90f0751a440654441440300000040d41069000001265080c00c560050042007038036180c00e012540d03262008402e540043c014112587c02c0c07807914600090183c1849860910101c204508101c0d013450010100c0c2c078264806002e004000704141c00034102441151000c0b444107004405180c074400c0040d40d00c1e50110b9005064124501e40c07229103003565414402a42082d030000c0e43c455564100147e1749070240200e02107081014000017442807815540c01040f51100c1d11140d007040314900c50030072241c000c0341000d007080360200030007072441c0c000c51103243c061445038800162098540c2690003809 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 501433992 1250 501432742 501432751
    0x2060f2b1404060b030f01060801050a06051c06110408100f1a0d1103070902030c0901020606010f0f0305150d031128080304050a050616080a06150c0204110d0212 71
    0x240c41c04034822400040c68860356803003900544041080401080864a805190450700314035510b8110080780019064000c603014400c044828401c0039210810020a20144034003c00c052641e44034280008000d6040084030304d111030402e90615a0702e07120541422601844141480ea4444404444048034441c0e9036107100700b00030015500c103026010482d08800c0301d40140001080d07071b030405501c1d9800c107c0c090140451000540d120700700201d8580b05900703c00d80b0705015015141c00078050354450b0150203090682561445840c00301c0300401c2d00106805441c40e1400350040501e54040d888a00412280394401d5a0f00f4a811030981c1c00141000c030104603141d040c41c910a9140d2001c0d800090189525400103541583c90320380b850300d1850201c0e10000200240900810040320400c0300349082c010f680d507610780406c0c65072078000040c1110b01600600a0300b121070828607081c1d502c5800c401403020f1010f8800500c02da40f4613841c29040e0000c0031189200f540010300301035000c1209040c603412 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 501435242 1250 501433992 501434077
    0x60c03041a060d14010605130b040b0907050d020c0715020607080703051612060306060b07030e0904030804110a050a17010f0e060601050d020720031504031b02060f 72
    0x4504144002035081c5944290240c02c1001034920b400f02c0352003e46c0810000c00004208003800c548070300c021000750690307203440e61103145419141c5103141881b041c4203208502c0d9580b00e9182c00700c0707408414025004915000c00380d01c2401d1010a2104000c0210a000b4a094000381380c2c61a01d444000d0460b02c009210404050500c418081e40b104905151528410141460b48030048050108070042c401580041c00d103d0a08400080c92402c0c24010049603010350740d101580e003403400510000300801c1d10300800240000c0e00040108111016000742c0d4803009101c5010181e48100041101d18070340c10041c1204118402c0d180c0f22a001d2061807003854814800340544146101d405880701d030700510715811300030001403099040c00c00d503040710801d0f9031210412104014500140d0740500c2c840c1c0c0304601030302c6018100700001c41400c10b102c0c4030740ea040d40da000c269440c0c18203960110003038010803600140709200c10b0901c02c1c00324000d03111036020f8281c42c80e00803950b20600c60080501075401c074030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 501436492 1250 501435242 501435293
    0x1140913020919211703010605040602160e0c07030201020702030d11010e06061f0c0f030804030306051804120c1406040b0f01030c140f040f1a0402040f03060c050c060c0304 76
    0x4062011160b07001d002d00340e600e03042c55284c0a42003817041a80921302410b244900040082002e54111000d00140c075195400c40b0b000a100100c0c040b4140c0ea58000e00c80c40c807901000056101001100400d030a0303203e4400542085629404281b0701114401e0650100c1c02481c000390160a013480b881c0540c4c1c00e030b20000d1a10342400808142c0804102403c079031100c2416030000015405003181a07d0181c2c4041a0f41c499005ca040042083c0000d44003140007070b040c03000024040c9400803c90107801000d20b540c0e555034580303540345640c000e15001110180b144006500c0041400052120100d00592010b020720303142600d004800310300000c0000241848640042c00030500c10a01c9409490001100307041c103208050000d001040412070542e4070900301002d03180295115005800d5202d10800101301d511030030410030043e801a8064454225405001080415240e4010845044007418824540600104403601b025400c543ca0b01340c0c480000240010001c0703500c802d4507414090080c440307 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 501437742 1250 501436492 501436499
    0x1302090903120402042c010f0c08061c0213020c0a05010f0e1005040c0e0703020a03110f0f1608040f08150105010f0e040e0d110106050405130201140913020919 70
    0x301c4207000a44060f004035618406a411000740c08036106c1d215070451500510b546440340c0060103002c0012100440d00d04001010400c1c5001d03001c0d03a802110000c028100705c04584044800d03c4541402c1030713a1205600e555003540c128070384020001d440d840c0b000f40c00035048605111b429a40c00c0d41880415501c3c10b01c0e55211500040380300e04086000d0440842c0340d071610f0520006000b0360b900100301001c07200d001e21080c43d80640c000c05050b100f585050126916140e404007160298850f501c0000714200f2620040c044200e00404d0065004201d9819004140c0c0310041c003034200e80c02040c0301c003081d885d007400420303410041605d40030304021101c502d960410000030302c0600004084414090701490366403860343c40c0d4200301c100070449412110340070207251009142d0300804a0400d01d42d464980c0100d81d506080c0142845100507507082030900d2003d50045818140b01009400c650b1818028a0002e6681001c04044164807000140c2c85903182010000c054840c0d001c584004950714a040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 501438848 1106 501437742 501437767
    0x140f04140910060f030603080f040503061305030d0b010339030204081c1701140901120b0a020a0e0d0c0f0b0a0915090902031302090903 60
    0x1148a2030040a1010012064880c141e0400d0120414001e0900910341804605194540014100c0d5280c50f950029080012000084200001d08004070700d820040e058020400c080c000d0f103014615070325269607115020b00c40c1d041c1521004040081e030b002c0c0d4401551100c0402403a442900030f000e4911046804075403418060349503400079180c140c4a4400e03038041d11080d600400310707200003030544d824000440790420100301642030340030400305a080100e40200900c102d1000014800d604006005074140c01001c000c030071a040d200b012821014042e40c0041071608010307619013410008954494401010355002003102030700310304000803082421300311100c5045090300d03562110000c8c6228400d161400b00000c1743c0440a010039060060440c0b9241000d0401c0b500142c0d58048203000d90b0411198603481c0d2000c9200a41582000d03140198000d404001441c544103401040 = true := by decide +kernel

theorem cover : BRFrame.Cov 501258992 501438848 := by
  have h0 := BRFrame.cov_init 501258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 501258992 ≤ n) (h2 : n < 501438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
