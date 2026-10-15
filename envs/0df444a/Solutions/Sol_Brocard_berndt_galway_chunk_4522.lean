-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4522
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:53:33.67876+00:00
-- url     : https://prove2.me/submissions/ea80610f-f7b1-4bf7-a62d-c15b79db05b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 813129496 ≤ n < 813309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 813130746 1250 813129496 813129523
    0x10110f1204020a170c060702010e06030f011d0601120c020708011406030f06190207020a09020301031b05060f07030e030f061602010e01051e06010e150703120504080406140c 76
    0x4082400709604055501102030502044402c2c241c803181550541d403040001d80c400e00c030303d80015815086900c035050081c200c0d90085d090325243d00300700000005001c000d0082c55100b541e2284102c02907081d8061345c0c1c1c00740c0010b03114110398000c81c040300005072108142c0c000a6104009002030610800d02c00c2c4d124900b19141c0d200050f060040c10142403011107039140300c170fa82c0310605029220070036500c0c44c4c05100d8848401680c4000920103d05041e920f82e003d2001c051001c4000410301452048150b0410480060302610648900030429203008550120f2114074050000c02c001a000b0007a8422669000741116044615081c101c4c3c07611808a5040d407460216500503000036030240556210410a48020311041c80e000104664000d051542c11000034070000200b0043d9018422240c3c2c2c410014003003894036100d600508215a00584080307000540c1410348403010100c80c4203184c0616031040744c0d10301d041c0ca4003500311080c00600c44094141d030410440a840094104600e2500c81c45 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 813131996 1250 813130746 813130777
    0xb0c0d090b0a0e1005010f060507052505031006030803011205010b0d050d39031709010c0f030902060702190b03090a12080906010b160515040606051210110f 69
    0x32109103040100e1100301100d55400e000040c1f04010b0000d11950035201c03103180c140d80302c05070340c240710385001c41091a54030300000062880d06090080780c5000243d0310164111141c142c20301504400b20380d56844058115801440144070a070000390380045610701420002c50b00b84a0700c130014210f1110210201c440758000c0400d03091140c2c2198428086540721311058a03260b20b0b00a401c84a1b41e114055681603100d940b00720000c00d800f0f020308050202c1c202c2c42c01010b900d80980c45500a00101c11032501080161030610104c81c4030b40980c46407583d026003801c2c24108645c0c00c1c003020369041c20b48011140c0c249900031070200c03000405507215145810003061610224208200750310545074031181086140c404001d0445400250319044400c001c0640e991090703170303c0105041c0400008024581e00610070100b044c010341000d1140500c3c040c07002003246035607500170854204c6043d08264165004660300d44442a1070758840800a00d0411902e4030308601d04048000ca64040c08054000347e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 813133246 1250 813131996 813132011
    0x100e040b19152306040f050105031801090308270712020f060f04330c110a060306090f0c020a060903230c0f06060604091e09051b0307030b0c0d090b0a 66
    0x2070311400003c150b05050b070b49940740c607041a0300c900b0f41c41158000c2605100c0000003090034a10b41c07203c4c900d01c88040d50300800c2242d103540f40040c10000d05039076515103c050204402c0351016050004c25107000d04600a0040c07a11381000f912825003200b0302a030340a50881c140001c1e90b21860b004100719200d018031155a81e040074283c45440d98060f000e0148944001c40400300744210000384c0c41c0c0360405091400c0340640524001400e007040740501c2e0f0300281280300001d121505030f006003098454540c1c090101d410500440411594604408001a0b00101046003c282c055020240540c001d28007020143c20341c18441c401e089c0744841c800342011000810110111050100064104502c40900047d051190016040340518080c0300e20640e92200031282e000501218080c1d5a0340c400d500780860001414010346400d0803c0181e0302d04044c1302c003868141c1c40c0100f442c0c805d0701c7e400808150542c89a49800380b8036009100254401e030341e90b10f41003000c11800c940e001d1240c40001404109035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 813134496 1250 813133246 813133289
    0x348070c0e09010e01020901050a050d09080c0a0201171b0c0c0306011211010e0901090b0a0509070207050307350f1f14011214190b100e040b1915 64
    0x540d0030001904181e4414407c41c517640e0380c850221105c00c0c0300b503d059612402c04d40301100060140f40320040c40c1c00030005003e50300c26004655650303503c0c000d8940c0c40380b900ca440e041883c0d441c000c9a9094085045480901c507284144c0301401c1d0701005541141c11030043c081c00b1900d1700c0320a80240c1d1001c4501d00e012010414100009201d1702e2080c40c06045038003083c00440c0c04900180a94210746803102c1c504101510340c20712000040c0740040940500d42003c3c1c01c06904c44480d03015241c000e0040704000b051904825a10f0042002d140043d2140405102500070000100326050700710303801841c1c40020001c40c2008000d540310310001c07103559400b07c00244c0341e0807644046444004201e8440c0104400030b40449400c007240d401803003d0130418000c1c0a01c1d42440c01d0080f00c2070320400050054010300c4030044007144aa80090804441c80c6e84940c2c901d0340c1500c08a03002000c156a56000071814403401421200c0c405030b03a9400b040f180080d0b0441d03048100e268005c003141c402900a40c00c0e42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 813135746 1250 813134496 813134501
    0xc0f0b030f070f0e04020f250209060108010e0403080a0b030d02060a0507090605040e1b0304060606021515010c03020c0307090e0d0306081507050706020406050348070c0e0901 77
    0x15030b03641040001c0301200e0201030400d20700540034901c10790f4045104840d545410084400500c0d40034401c0c142105010001e552106c0e408006a00942040c0e00040c1c1f154061307450a8180e070022040406156a1558101c0d240300c0c0c010b00e02640d003515003040216646040252040b2a22036401802c40ba24103c00070b1021118010030040401002d0041000901d800008075000d85100100e48211075a840c000a44907410240360348070060350002c1000b0601003113601440aa0f0030507400e45200000c2507a4101c400601030300d85000440240030780f00d04560040340e07060f900b1072090041e540d049210000181c14515aa480200900c1c2c42d2a00b01e400840c06100350b4103510300c41d080800030542800d1145568000c6100c6400402c3c0454021900c0b05014100741c83c42d880d44504155a40c0da11008000d220b90400c0c2c030211100d00d43c0315070412100c2094802c0d022010f0300c0121710104809540340302140794005802000310441d04001c10000f04004400040103010840046412820070040749400c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 813136996 1250 813135746 813135751
    0xb1c15020909041103150c0a0809030c1c0908030a09050409021f0201020d4b02040609050301051003081e0d0906061e0b030708180d080a0e01091104090c0f0b030f 71
    0x1d0078103075502003010321081d402c191020f0001c14527100e60b01e03a865803515859031050b074040200d40e1007010341d6a46100c182048800030070004d40c1c1e841203540e0303a1301340307090383e038003820750b0131001f040030b250003070200c3d0a081d4070241d1254001040714280050f1600303030143c18030072008030100503500002d5040ca24403480c0144003101d541c60741900ea1000c07030495402001102e5401d2055400050b01e0b0040d00350544400602000c0400b270030840d41e80741c4e50032002d48181c00920a140c000d500303050010700d02e007100c1000c100890360801c11051806040007403001680c00092084a181403007440549241d45140c441c0008813031041c0310014032030f400c18460f21400c0c0c1c0d403881d80100e0f9804440003845920b051006490b00088a07050070012512003c2450345503009c40c100140e01c074413511600030304080d8055a01c2c0d0140c202d940c010048010400c10003820f03500d41c0c01c00500740d001c000c4005581410550b201a034428000c46104040300d80324a10399440c40e0496206212004000c02400700b11003039101c0c00c58 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 813138246 1250 813136996 813137023
    0x709180216201210021b0d0903060b030f0a031b0602070c14091504091a070206011802040303080411150703020a020108070503150f010315080106090b1c15020909041103 74
    0x51a500c001c584a40c0e0720556030700d04c900103940125110750aa142154240700e00030240090f19209503a001d40188861028801501c010b400c00c42d1104607070a001c101040a20400c0003d001d0b900c940e500c056403000350441d400e4a184285e50b01c0308001c94034600c06004003030300c20303903031401d10500c1d0040302ea04003801440d445102d001e1140c180004005102600348010b41d080c0c802169500817420031080c1c0d00044030082c0d00070304406080144482c0d01181042c11390308400c40e082510300d006001442280614040100072403460030104001c60044901c55044041c010300e0500c4080440440406607040b4207400c402590048010380110344e00058030940c440d1040c90980d095180c81580c0b0303543c0045900d04a409070144240340a00c60b44290040d20320b0680203201c0005440d96090064000e0180f4418500c8480c030340601041145401032001000d180c0d00302a522410325152114400d40169150191807140d080240038415140c0918151040d80100050b595403400e203010b042c101802d090204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 813139496 1250 813138246 813138259
    0x12070812041a0307210f2a09050109060305130c03030203030403080717010501030911040507021b0907080f0901021306051c06150c020f36070918021620 67
    0x7011203684004840b000000980710701d105e41084031180c0300107011800248401d0742c2004c03003402c40a84002c100c618121603444c100c51105506000403034015600780212030001d0041001080311521a400030307900400c98039028241a11159503030ba456080c00e07481200503800c0030080000745500700e071025501400a0812911000201c2c1908500400501545045c1680c0303082500034041c00495010071030b40050010480c4d07042101c0060342c0c1d050702d00200780d003542c000c0c4c2840340c25041144419001c2e102944800d921034480030f03c82c1d803180c00010700f820803a40d070070311049a1152a0f04003010040026840d0744d951101c2c4020710003000c03908070942480c9035082020801004401c10442c1100203a0b80c030b090108114075100080d014071607034029940c40904c41441c0b50602c581d40c00500c820540f00a122040c035040405111103880d000c4600001050000500300200c00c10940e1403001c804211500500e4182001d414402c29010198155090720440c1c82c06000c0501c1c10203210fa154000302d403c1c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 813140746 1250 813139496 813139501
    0xc141c170c04030f0503130e09011a090103061e0207080d270605060118030804050306060a0305060f04022e090b070818030a021314010f060e12070812041a03 69
    0x200c02a4032079480010a200d080c0c40d04c09003800420700039a40040192103245804983e1042c5140380134071305a40c0c1603225403034580c107440040c02452021030b0b8031502500f010b4461380385441b41c0004103152014002e80e80110040015140799520060036118850188140c131603410701d00410890b0906520321010484101180b04030080d50102c000c40c45501c800b005c01c080d0f840d070004803603410048040187d01400b040c1c0c040200007100b0058070030381e0fa056003125419600c410130028180e00700d202c00b60480d002200070401104144010f0303a803203030002e80340a03260b11500e2201c0c0c0e07041e010000d13100c080c0c40c5070141303014203207522001140c0207200450700103040544940340c0c988640b1852110320b86d50b02d003019020b840d503101444000e54903900140f05800804100035488040c0c41006e0845071040425400400da05115100b410159002665610680e10280007403007940e6004c0502c650603442070320000a0000d90410010081c484d100c44181e881b545400100b18000508844000416405204 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 813141996 1250 813140746 813140761
    0x30d09060c0507020d15060b1611011e0f17041a060909030a11071208031008070e1513060f061e0c021e040c091e03120c141c17 56
    0x6010a00c80e410110000e9030350080c6c842c41c0b0040100381d01421880d41c0116541d20b05200800400009501986c10343c0d1080303200100459040141d0030300640c0001c51102c1040c43d283c412584c40d401d920290810501d2100c1c10200c4016403181224100e83e54101180c201500480c841e201a410850030382d00c10284c0e0421020f015140d00410304003000300700d040055408014070803c180d074002c081000805160304050b080464055000311440d00d100c0050800c0001c94140001d9a2012507600c259511901d8403501a0021500d680040b1540d100d12020005039501c1d85600ca544010030130340d44a055081d14044002e409018807d92072030360443c15010310b414140d000036151007890350403180c0350440c00044506900b10419818042c0c0c00620b0803503041c20307913600a8013560544164001c50f00d610444c0c02c03161800c076441c5000081410448030310075000240541503480c0c840f4814400081951702c00844245070400c5021215440000066035446042d0090f000c2c03040c581440b60780300b000d483c0c14603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 813143246 1250 813141996 813142009
    0x209040c0201092f0a260c030a15020d0c0201050a0b0f09041212110702012a030503090c0904110913080717041211011218080703020a05030d09060c050702 68
    0xc4d000c802d00e80460100400040c1ca008210704035200040001100c2da07202d280c0b20041d549034802000f038800c1902e244031400301d00000d40f4082080010001c4c0032485550752100d0703018401d90710000320680c0900c034640d00800c480c003031101070100715800018240340412103407081d11050364040b80640003070b81c0c2c501d130706031201d1981d00e5000d600308040103202c640d4903608941c0b070360b0610290b2800c149004010140380404130010001a4001d9892643d101100c0380e002054400c41c40c28802d0340006a80240300003030040703020f142d025480c40c3c159180d100151001c2111840116011110071040c7d4000b05440e250915840743c01060b0010825904150342da19828248039403d000340420b115850b0001b6090740c01411600030340740040c54000d4a4000c3d18003a110b4402960b80c031170104181c0c206e0440c866205100b0580300513120303950480140c140b5154685240d001403026811800f5030424400415002c10043c0b00848a0440000e1241600e0030b00078210381c4111000d0301002000c00ca010050b94805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 813144496 1250 813143246 813143273
    0xd110109050d0b13110d050a031701180b01051b060604050c0f0d0f0f06060f030c081017010212180705030304050f01050d14090708060105100c0b070c080d0209040c020109 75
    0x15481350700001450a1400d0311203101140c26038401c40240c6800300b0840b02148100803180b09031540c5a6440e01140c0760391207a08240241302400094140310b054032640ca03041180c0c004018101700e480c059504120519050003451040a181e0058050002d40e040900c00e02d0790104812501c10f00b0804200c107060303003600c51002001201d42d1a5440e00d180b08100d5131000b210074101110030440180d44180c0501082e43d82d00c45040440c6c5000400312106018145261081c141782c800c81c12000d05001c40740780e52800e040c1d102c0f0042e42d403c0c414101407202d0101083d015142031200144e40d10070b1b42500d1454000700307420507402070b00148030821094860078411001d4560900700070352240d1914503c0802840481e0f10407404c2009175060090080002c142e6506079002c109c141c0b51203a803200280b160282c0703482c81400015600c01408000310b81d60b401802d03005009450000e141003403541350303810f00390444c0c040c402d070781c541c0040d10301100c5c90a031081d41c0307071644c0c2c500091040d102da1362140710080c03201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 813145746 1250 813144496 813144511
    0xb01020a120905030a0b040605070306030b19020c01110c070906050102030d0e19030503060109121104091401051e070305040c211502040602060c070b070e0f0d110109050d0b 76
    0x4082070818060401e44002d0907020301103610900485c02e0143c4500d0f4180d8098916518240200d01c94502c28012141643c6d0000c98030515a1036048150310b680600f50b54100c0103076420302c01d03218030300350a00035041001d01c291800360721904a800001e0400a443c0e0003035101f80e207000b00400c05079030040709441124400180c0081c4c03103440c0c0050203092054040742480c0c44290780d0035003420141c000c0c010710300600c020799403207840342c1c0c032644094154030700200c02821041100c4420b8180b46065002018030b14883c0b070a0800c0304d17410401d85404d4500582e940c2020707820b0550200030555800d1002a0700c90000d1405000504064844140c4000d01d0b020b0b00c541104000e40025208985944c0911055417061100d0b03501d05004409400942060050b031005014280104102d4561001030707503030350307034200240781c17003903201c03180d0580320005061010707500411210004001a69015901e00000c6c0c002c00003044443e48401c00101940b00036080341c0d20582d4480207079000708040c03000e00b0790310001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 813146996 1250 813145746 813145763
    0xc09020306040f290409080d02090a0f0f060210181104020412140c0a0501050a0e180f18070f0306181e17030613091104020c011508010b01020a 63
    0x1658000704001c0c100200d1004020fa040861844d080c012250206803400c844440c0603464007a41420403054514424024140707000500c0a44800a0168014500c1d0701c0000c001910040e40c6192041c0b2640d000c0d8440c0c020315944400800202c2e4040c03207180d4100f030503007108010300e0401ca00009841200484003512002045040e2000ea44840c0c3c111405000f1503245d40503110903903c1c01501c40121006010a940200413100c199410180302c0c02c01903d50585070181401210401220089030508072158000d4031032043c501d0a608074001140209101611104249020803d4002c4416a40f040c0207040c0e02411003044a02c00b041c0b03252003600e038403007070204000d6040481ca081c0b148000070f001e03020554400c0740c007454074503101511036200e12503001301060041d10702e45a10a80401c4420507003210b05e81d17411a200344400c0e80000291486101e52103a0020340d5008a4200d800290150449070356910043c950384c850308907090000c02c0318000900c184e140a40000b0346520302130500500608 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 813148246 1250 813146996 813147001
    0xf0e0c1312150e07030203010e070503030406050304110a1203020c0307151211031e0114210f011b140304020a0608220303020d060605090901180e06100515070c090203 73
    0x300880c107600c1c500b60705000610410403901800c0d13843c1e0b00e29100413486580303405d070008002c0201044090440320014007560030b0614110b81540c003680000cac000c5034038200349a007100d001e03034540901c600500030190595080309081d26000e441c101c00e4043c03152282e8400c010402c8107410102c800700042c81507240c0161440c40c0544504060510b030b10000052002c080704000b50012407407a11a90400610094400c50341d0340c803150740242c00c41c010b09035003002c20070011030030307220b60692071140380c280c4242200c0c6020300c00c080e0b480c2107a030303a030f00044c50000704000d4403800c45500104400c1d07207003035801d070341703817560a04d60b000891060407440380c031061000000c0020442e0182c00f420b070103c0c0901124105101201d8503009002358000c000c070201b031601c4c140d000705046124005a52800300c010f4401cae54140d0034207064200b00318820407020100f90726866014241ca4040c003803240902a04282c040c0094100703010044140000c100c1c2c1d0005400c18884100480c0c82c030511041161007410005036a078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 813149496 1250 813148246 813148253
    0x403050a091d090114010803092e030e01050601030b01080f07092607060e01020d03052a0301091d030a0c0521031006030c020c0f1201060f0e0c1312 65
    0x1100a81c0a800e650b1007050342034414001103410030788a100b61800070040c584102c00e40036841c40080c040c5c154658000d0200d150703982091665055140004000e5400c68a500200100e41c1c091044031400026159014200d5840090240d031b80c000c40f090800740410300e80c03080001e025007401441100e040810a000c103094070301641c8468050f0018044c1d1031f00006940310035900d45565420003a016100706e140c0011918030030300c03d080c001340e0164080d0003084c0b000ba408030003408e40601040b12400128001004540c02c904201c1d840002b02e14020f80c89602d003050402c11903c0d80c4500010a1503000f010344a03440000c000c40f000600031b814110000d45d8142896847c2c110300e01e44015101418103041c0e50101c0e84130001d1407266403c178540108040d00c3d48401c405072400383d105400560702008500310503240c0350305600d91114000d0f09081d240e0000300e0900c2d080d10015480f51141842c200030a0102e0f01e0b03c84180c0703070301600b0150b211740b5103600f02409150801e141e10442492241e06807a00c03040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 813150746 1250 813149496 813149507
    0x40080c090406110301061d040504030e1e10090306050f040309030b0709091401032102100f0f0c0908240403030b012706020d0201110405091305012904090b0403050a 72
    0x151a20f1030b40b01500c03503854131005044150000780409510140f84010b04041c038041c01a41e100340d905503284c41c2c000c4060428402c1203400c100b80c42d8010b0102402c1c0c01e800c1e8480107081002c0f10100d075111a0601d00d18248581110005011a80c40c62680c504010110343c0200e4501c040f02e03031000503100c00c3d90b030350301c802c84404c4080c0e00305200a0303081451401c03040070703d0500207068900038020841412480b00c000d44000c0c51049402c1c0160b0413000c2010741001c4140d010408020300098007041304004d07155103004985038032400340042104400280081c810401c511741c140c0c4810080c00040c128004000800064010700007010580c0710b405e8003c86912503d10058424211112035031100300e08194410103084c10300440c80140300f10300070070781d0b070714814000c1005c096014440e031490b1a09240a119585030028445215101e50070354203030001d1000d1143d4030404d407028004101d1200c460346030408a4071a106854800c60078211150081010a0b108540140e810304ec02e035035404a0340c48c241e92 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 813151996 1250 813150746 813150761
    0xf07030c05060a0510080309010f2006040b04050706050f040302040f0b04180201080705160f021207081018030f0305040c08071202030d020313030f03030240080c090406 74
    0x400e0107070100f4009010f109130006801021000035a844858035403081c25602d01420148500103508901050390303940c0104040d03049840209551451140c1a259680c41c003801580c089801e5140842004203020061201002410042c6071561134401c5159030b81c2c0d8140110b01001e03108642d0384407920031a140310b5100031540f12007e00306010201c0980307a0307040c405049400503800308190342e000071460b40c0300b40110b5101503a0301b204038411100c15100c201206580240898000c0389540942c3c180b20420045070380200710030001030103130403010300030b640645044586002c0c0d00402c1c80200300009820500110801190f4074002a45580342d003008002d014040d030110009005101c40883c43c120003000d400c03503084c002e40071200e001040c80030480e520311429480184a241d461007e00000740b10022009606010346005402c0c00346103004010030000c0b404080032800d0035441c0000e007025001e00344d0048083d203000e035401c3d080d02d407509242c6c8844000000310f1044042800040070884168440348 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 813153246 1250 813151996 813152003
    0x140c180d050c0f040501050d06021b060c0301060201110909150307050a15170609041203020906030f011410020c0d08070f0803060109081207020904290115140f07030c 73
    0xd602140074202241c4602d0034000c50381c02141c500840c1c2e0000d0400c3d000c0d0034100c84c1e0242c18011035034001d84869000f50403c405003015840c810004198031202000524024803040d0a010750b40d5142403806401c5032000c110291050750180613071901a51040c0d030f4140d0004220612030400308401c030000f8100089604615440004028041060001001c000b07032103d4140c3c0354101480c60580007490a40700484409610003070704000900010013614004001044504015003004421800500140c01c04c442c103050280b850f400401045c04031406900d40780806891014024241c18002500c690140d4030841c0121103140e10311040101c1c0004989996401241c007605456080c6098042d0703a100ba244640010f584a2000c1040f60003c1000580c02c108007800900e40001c660034000f00d030300e00a005698043c400a0044032031f0401c4669000e40c80d6240c10380510560400242c6180b200c1c9200d4448108401c0008620882c018101203c1c40746841c220714035180c1505250494104003c0003009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 813154496 1250 813153246 813153259
    0x3050403171e0403020601082b03021e1204031419081305010e060907150903031b020d12030c020d0903110a1a030103060614030d11030409090302030306090a140c18 72
    0x441810781c08121103050f40c000206503141e50074800b00d4249006842d0701c100e44548000327031480345294001c1c2d008059147ca10100010068008140d0004941000d4a07000d061146c480400003015400a5050460380001c85490b0419022036103086054510503440018481c4039404503100880c2900e44003149a8444001d200b10203106117565180c410694140020b446804804100391050380080c01d541d000c031399121604c442c03075a02d00322401e0040000000544102c101042c4c05601c3d001028113085005040d600008110254018110b81101600700115001595011450799015030b030b2500312600004e42000d011120400191403c11590091708040e540384040c4a4007015600618101c90250307104022084d502c0110304081e544180c08940c0c590420f40c68005854000c0a42c00003801036202100d0078180c035501c2440c101d070603106043e000340e4804801c0204905c0c0402c19640c0c13091000005001d507403000c22544040c40300c09080304078031541c049852603100f82007403909c40f46010001c00c0e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 813155746 1250 813154496 813154501
    0x240c0d0504060b060c15090f1b0a2d06030509210f030f04030e010c0b060d0f0c06020327090f04052a03061b03070e0102030d020d0b0a0603050403171e 66
    0x18140d0300c811031103400000f030031028001401c0700004218000c001020801034480440c0100300e02d10100c8a4013109c50340024626400300703d00301c030300144500000d510204a4240250144038803200080b80e40400c040505003403c0203070b281d1001c90020140c8140000e140850100c1740c2e0301d0b00107030141102010042c4c002104000e04d00030442c0104d03000f2360180e118400c06a4101004560714844040017030700388610900462503909128054202ca0341c002c0030744141d0b500443d503450300c1c1c00c1502e82c09907006a00100340d002c0043e9210100101c2103881e0f4540c00703c41000000480c0b09000300900c186e8004000c1d000040074403e0a0240c0d400110b100040d0301504005030005003400d0f0580300c070f014024840c00e00060030894081c50b0321a0400600d940a90441c0c2e141007044550303d844098150440c04148403e18000016001500d8240121080418807c00503400d2050b02030950303011404040c1407c007070201094010100e81c2010038082c02252560b9213200c0341d0a0941080500072030594100d008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 813156996 1250 813155746 813155767
    0x21061230161202010905030a0804020f132711150d05091f090201020a2916030e161a0702120c010f090305060a050a06120302240c0d0504060b06 63
    0x121061040d02c03580d0707881180089400100e08944004000800a0384100001d4030b04d140038110255005100400400f1030542c1480810a540340d012190030b0510f03140d1020f40340c00992000242482d00325184401418a6142c076a1030390740100c0414980038181c4040c03000d4032042e8081c1141c4225450303110900042c18003414042d80c034460b031609a40f0511164984a03003007160740c020305c2032483c0c0590040440c401a034880c0c2c06165410403075044d010071105013424002c20601c400074800d800d03018041100006624020701650240c1503031140503049003044081541c40d003800101540d4882c210008503d23a440912402440781e034501a600010792803140d2140704c00020192240030003aa02c07031b4004045d080301544c000c0c1650200815a8010500188203621158061070340091a44000303c0c46642e60341418251606450066005030042d010340c3d112a032500030190f04800b075514814180d071402d0760142e500b600844403403c2c03120b512040402c0510a80341c0081c03030989801425175a64480c90807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 813158246 1250 813156996 813157027
    0xc0a140a05030a26030103080a03050a150305070f0b0a02121c020d0b15031b1c0914060106080c19020f0d050c0606090403050708030a090821061230 65
    0x4424000b071400901444c0f4030034005580c1203d80c440340c00f0741401041241039011b800b00070845025103507180804480580400c0810700118001c5e00039200503400c01202404002c1030380c018855416080000c610001e0740010502485ea6603210402e4488485025294440c00e08800c1840d0490010420049010300c03640041d00424084070581e40b400903174112950140011902c41085d41085140b810928130950000d000d41d9a00300700e1746440d042803030030001c121400c00c441690003400c124900e8010140030044d650152806051056040c030701643c11940718881c0c10100c030f10b81c0c494140c501400500030000001403400000c156010040c00e507a00074000e8220302c10180161003940042040781c10300030113440c0601d1f0140c1d90103140010584135541154000b819128042d582e0b4861b803000704e002e14010300316600b00d2400c1d510000b844141684140c01d0007401c4c09104400041d440f10703000400040d8469003000e500d115038510070000c0e100100c03240808444032a4044006852000c20030801d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 813159496 1250 813158246 813158273
    0x8040602010b150901030c0e0312190315150513080f010f020309060604090f140303100e0603060f09071a0903060f0c0315040603150b03010b01020c0a140a05030a 71
    0x50380204000070030308040210301040f0062800740c1d2202080440d606511940011a1010300c6013407000310304440a01280c07030300d0208000c00b01501004214041e061208554802820906140a01c1440b100c4003200c90401d10600c01c001c941c00b55204060781a5000360b0959500002c201444503000e951000c0c195120490241051141d52030310300f5040824950b807080e6400342103018010806a81c030710051100805850000340c40341c940011031180094a0038a201c00107000c1c40c000313192207040581e0440f05028032034001101c115050010001141c500107900d96000002004209050301e946484908013044c90b041245400415030207003c50403080e0006221038901074045805681c4d9006103802d000d5820b44d480040c1e50301c20400b00d00c10304100411010a01307001440016460b40e43e580e042080a200000701c4416900d1b400c00140d00c0c40d00f0300c150303d0064402c0c005800510031540006649003a6801000c01c5035640c541103031950344840c542070025007800b408440c2d06003c203050004002440c5e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 813160746 1250 813159496 813159509
    0x4150515010801150e0f0102150a020a1205090303070e2b1b0501020304121505010e1014100507060b0a0305030712020c0a09051b040b0912010c1b08070501090804 71
    0x40e0000641016a0101c3c1e8440f00203581c0362100c42040c0380070041c100c0d641b005040e04511605440340d00b980582c1054a00480900030016510303008203e0140035001c5600040508519100030494107040210803030b9880109480c14841c00804400041d010110b24142c5000080800c80008030009500c0003c5144901400c07117820101d110041ca100000258054240160418802003107460217081c1441c1004e031184040d00d524440301f010b80340c00c40340d0076440094420030090a01c1072815101d4464000790034000f914030042119403000c41c00a0a042107a4010480d00169030703000d101b000c1e442080c0c4148001c4c08441d682d030b56800c00350b80c0c1c1d4000711001d840140e00401e4101c0d0090001071060206003000d00501100c0b0710b840190b40003800010403940315508046030303481c1d90380c0e40c40d40200050180c0007441510b51800f2710501141c4500c003014a0318036890130121031456174210f100c0201e001c6a0380300c1d04030000201d14041e6924021103800505940c2018458000c01503c1e00103032080e141e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 813161996 1250 813160746 813160757
    0xc02040914010f0b060a0e240d051906063c02060603060709151439070e0109020703050d0905060601080606190e010e03070f0305010b0909070e0415051501 68
    0x400005c10105101c0c591a520200f14481042c0c1c2490400c0d03002e50382400070780d660160100310380344034010403075110645400f640f542ea0001c00035088211f48124208440781142000014200300b0003410b0041c17540624a40100c82140114481e03010b003e0109002041c4007040c40e117110344a50181d959002520214405c6c0104400995102c0c4140500401c90350007490311010f2100da01d000342c0e0b0702510300b50301b0b401c0a00300300148042c11580300406103a1016406041d80d900e10f0100719440b6041c5030144500c203c0d04101e40420255480d180c0c198107640c4152001690dc0e500c1c0d1a0944841c81628082c14a150a18140f881480400b107210351040b1020b8070b60344c2c0316545400400502e4850958140c40071500e0404203010300e03201d030551420355101070412444145002e00003915000c0154030245441722040c1041c010000280030316190709000b5620042541841d40b0a151180101d004940924184200040a011071002c00c0100014007513020401800d081010070b65514100034002e02080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 813163246 1250 813161996 813162011
    0x80f04090b0d11040f0209090f040b01092a0e0a1215290f0a0806150103090c12030905040203150306061f0e0f040e07060201110a050301060c02040914010f 68
    0x1015042d1802a551101901c0c420300e0030001000014041592034400b820307400d201c99101da407901a004c6010300c44100f210780d030600d040d00e084100b4060582088501500300594482d2107241401900c00e401d0310f8401c91a040400d40744211200c109180e101076000804840001d44080080c107103048903401440e9012410501440700019209840103031003288542c10074031001070a40b03180704454450014000101c41c001e400c00600a6241034000640c55040402802002014920514940030f0b080c03e0602030441c3e0398840400b40c110138030070058406d9081038110b0425214045090140c0340050003191a8141014000d209a448180140c0203200744c2e40465000d2921044802039000300141001d14002050411250503c12150082c1c10030081030b14001305580707500511012240e540c00901a691410000038255048a48000f4143c03108010a450007944802282d05460050034071840101c1d4510204004040c1d4940241c2404001c41c00310485e004190848100c09407091070a00064 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 813164496 1250 813163246 813163249
    0x106050301060e011b0f0c0512010b0319080a110114180d03200d020904050a0e07060c020907140c010f051603060e06011b050601061e0203180418080f04090b 69
    0x42c0d0072000401d203003c0170b00c00309000400640e4100300f0544501d02900c441d9a0343e8012803c500ba40814918141e5194140e038002810108140d4810203200785081d03843c8201380d140c801c900e200f6914100104a01d4040c042d8020009401c148020320081c6103910181ca0f002c8000d8059000c0c0400030000c42c0505000d80c07051fa840f034000d040f40200380c1c03445907080c80c01000e0054481e03400300e10744000b02c075002c3c0038007001642c40e4407030648101030034440403e0743c0c42d0fa29500d50030400139070881d40c00e0000e81c52154000d601c1c0c40940d603510503581c0c00d1400c01005030070b100a0361350144c0d29082e0010340c00d100d000316080c801504854080c00650a070704040140c030400c181c06481c07050040c00c010b0302c3c00c0000241d1540c4a50b00c06401c030342040c0401204821039846036410720b4000d0700314401052000000d144cbc440756100400803003022610203035003072000103122030b0107c209007031820344103540744c001b1b1040c000e480300e14901460390701c2880d096035120b4100d840160340c0c00520a1508041c80c028081400c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 813165746 1250 813164496 813164507
    0x41e050a0816090b030c090406060807051507030c030311030414060601360f0b0316050c1c0e0d030305100f0303090614130905040204050a020414061c050106050301060e01 75
    0xd00e10598501e40d5250a01c407815005040c0341c0c2c1401c5e8144101c4404030b010b61100302d285401b41d8099000402c84904181c0001d141c4103040d03115501680c0d600a0107880c100004094039495541031800c2d4802401c107007001c8000d001808510a1305500c0002403208004240645d070454901d1102a100b69036100c0c4015070f1844601581120300300240c00d9488140c0360b00541e480000740780d07040c000e849a034441c01c4442e048841900200301c40c100020900c65a96071081c0000c10012107403801e02d250480a48416483e00d00e111f1440401103e502d0f01801101c2c001c10440c0d014620281507d50613040700d0600a01521060f0341c0c407205810f1801c0d011482030301403e055015240c054880c001c00f640b8040c8202c400b11116100740611860074407032400d4030f54a085e0720600400020201040c90304203030042108907500078000c40b0181e0b204000800460300301c100303038080c07195084618a80355901e0f26034110f20450f0640a0811042c0b800300003094481d0844040c5040e1011551940c03071488010005684 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 813166996 1250 813165746 813165763
    0x8010c090f0503120f040f17191502030a090b09030706110a08070807090306060923060a0504020c030f2107020601261c0504060e0a15080606041e050a08 67
    0x40581140103004d0220914100a09001c2198540d642c641903880d60302032540803481c0c005480d2030b0f03511002c400c101c0c43d0030003215190000d41082144031010550b40c01e00040309460890000036000320010715075400039481204844e40190000b81c0b280703085503800c0d84a521089045442e40d2a0140806030702c00f410045e104071440b10703101c031290368443c44425503841100520104c00c0040e40400030000602c00d001e030000400904201103800d181c0e078a400b0000404009040321441c610b803007085525507840c121304084500907640140c0d200000300c445410341c0309160710200740d0980014401c850792076041e8040416214565021035680340c0300300481e00d8090030b200e0500c1400024078003608019101c8a131071403020a10007190103440d410040710303044d0303070000103200c01080000c070301000665084004040d05500481d03070120020f0400d01483c00e2a02550840c4c41003003150f000040311521504101c9000d0720a0000c0b02000424a541012008010f4014240140d640d0240020f19800c000703036001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 813168246 1250 813166996 813166999
    0x4060602010603170c190b0106030c0e211518010b030a0305091c060509151b040924080307060c0801030b18030f0d1506020c060a0c051608010c090f05 66
    0x10034041450144c0e840d94224038009080303030281107030000700302d03d400040001452003108918041d40c50308502804031801d82081c18184a0000b141c692244d44454040020104981c00e100380394076608001382c5004180d1418011600b584000e000c4080046403020110b41403010003030084072041024103840d0180c0c40c20003030110380240300c030315164030340a5003100e00e003d151502c8110100807511a0003c1c2d540c1640c481049400421603000c02088101e01540c1c0050b680c8110505c098244020001e18405ea00c02e0260071503540c50503201007480c1d500035125160350040180c181c55165004140c403648510411142503151501800703006008107141412203030003071512000340d500d001c01881004000e120603503850004000c140741d515840c0016001840d41610700003410180b441e050b0000b440242c001d030040d5406002d5004059070b801084999418140c40c0c0f00d40010501d2a1091509440c0310040081c1c3c12000c20201e641c1c2c80542c40032403e2511a035800244560394400c41030601071601605 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 813169496 1250 813168246 813168263
    0xf0f150501090b030a0b030a0f0311010617030d0203100510081e060d03030203070e03060a0c1121130801060303120b0901060801141c05030307091d0a0f0b030709050604060602010603 80
    0x240703080e206a4401e41c0950401f6064452030300181e500c100c40c02d40214000c5001c00d44228040010100034400c46010b40612080c040038a6002d1200320381c0d9001e2075500c07201c00784e000000202c0480c5203ea03080300504014114229030350040d0b00140000b003049a502540740001d115007150358504c503c0e03180c0106005400c0b44005001900e00320065400101114140807016200c0b4800d500c041042c90300c60300c0c00080000300e0459200d0f00800c9400703206420902603001090300d14243e544d40007452a6030f00c0c1d04480f0382e80c4100381c1d044118401e05690203103405500c0c000000003412341100045044407898401007108040724002c1000340310080c00b03041c00103506c1000603c918000315050b40c00100f002481c420204050b005015242640043c0c1120141c101000344071909404c040641c1c05844000340082503602496107171040204001c02031501c5641762482001104200e03444440714060160036281c4107a12a6500c8c0c0c040d00d400d449050103149009030000780140f040c4100005d90341d005240 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 813170746 1250 813169496 813169501
    0x123d021b0105151e28050603150919050a02130504091a180304031a0c0309060c030a0f14011401051615020f0408010e0c0411090907030f0f150501090b03 67
    0x24030150380c0f800425210403443c890100c102d6640c0310b04412500e8482c3d200604110682c070304054017042e1045c1d010034000c05051003030000844603c0c031420307940704043d40c0540c0203075185004003d800000041c160030080c07501085c8080d80304140c005011013140c0303003150380392580d84205110464500b504090441d0302803541640d2003915801c606a0003204800c072440300004240480c6095612542c07048500b41211042403010740746044646902500410b4802e0540c5003e008458480400034500c2c0a400800400038070160800c0c0d000601194150100b000036607080402c0c000500c0c428040c031a410202042c5040e610340c81070040701c0002d2701c0740b1103160304542e0350b07600c4100a491003400d1990243e001e04c0755a90b000317402c001410080c00300c0000401c502c202420068140b59115410300c0c065401c0c801d204945c0c0d4402c10840710704010903192810a60380705201207000b0301809400680c030605050300411110450741014981c1da2002640c5910150740d00e006444045585c030a005107258203000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 813171996 1250 813170746 813170749
    0x1b030703050a0f060815011a030a0207050a060c030903020f03130501140405120703060506030307030e010807021c0f1e0804031202090607030914123d021b010515 71
    0x4070700d42100c2e10381c202003003c00c00601d800b020f03103d00f9085861554000c4040004581d074030340a090042c1010304980f07000c290288441c054502c401880010b10312f8000036010100001005111400c41d0008001c100f4441400c1340100a03100106040c0c00501c251084485030090101c1140d591300d002c0c1500d064507a290600550b036050480b444103150030b8003480b0006941c2c96000e40350142c042c1d8840a0803096045240800c122007010740803d0180c1d2040c0140740002e41c200342120709282003420701c4140780c1d50f401c104910b01450406102001441803040c4446141c00480d10b01c00410143c40700c000201400c0040d0b50000715403d1100c00103a449808074000c01d0064200ca02c0d0004820000741ca0004900040788055000040441c0012002e820800c018024070304100300a00c01142c0e4220440780c0c01c0000c1d59140381c4051503031942c0d1b1052422540c2c3d0078100c4025a5501d441c803240c50020b56440c5100002034204010007090038485400d036050b80075040c4103d42c450700618120414a907030150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 813173246 1250 813171996 813172001
    0x207140307090c05041a04030506010b03040f0c180c08100b0702030f0313051f08070e0a0905040b06040b0922150203040f120905010c020f011b0501020d051b030703 72
    0x1602240c25014204010403002820b008100f0400c0c042e482e0580e403189014004200110f40340000031624105010a00c00240c022540c1411100026003031901c9850304d00f0301c2070b561140380701c00900c1c41d12580b4001610760282d40325a179101701501800c00003001e00304030a41d48584100c5698804500d081018070102100501401302103002504441e040036150615900d96031000c105111b5001d03a0000c10442c61030298038910713014604240c1c03c42014085070002d04004c002501580500400034000081034860000704002403464583c2401642070908001c18400341c141c0c0d03154000c42c1090050032560a2007081c10f8001d0188013601201001402405801d20f88030340012162107080b180b00000c082c0c200d0002d140901d0041c900344510010600d40074a01e05400350542d0300348611481d0400003a0780000d1903d80c00c94050b44c0960302843e807107004070340e0100d1001702e4808040c0368103110401e00005601410600750081001c1240b1b0b00c500100e40d52210300000f05400c40d410820002e130000c2c1c80703074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 813174496 1250 813173246 813173279
    0x60f0e0c0a11031813060b091e18180a05030d180f0506090f0606060f07062706060609050d08070c05120102130b0c0a0201051c18140d0207 61
    0x189000e040458092402c10f00750b5100130281014802040b00c6140c0501d0144400a0714108150302046154640310750700010b806a0480c1d944100e43d488000f41035144420f014252200c401422000f80260701d4044004001d800d072031510075404000c0410142c590700060031240160444011418401131050040140c18148070907107085800e03402401c0042c8180f104040941d201d04060421440d00280c0c6a1400c0d1195415006950003d001d101d4540c50f60b07012181d4481c8004641030f80c6903090700b40140030700b46140e5030102c0d14011080001001c0032007001c1e151250301c114020b00c0345590710042160011458080c103503100c44416585400604c1c0382d402462400d00c034621a0071b59954640019202c1c0f54551040a826500090440c00110392900c0d100042c0c04207400141c10600009225039640d110508000d040c0500000c1070861007440b00c0b100184122610414031000110840b000c00d541da16100454004400f640030f0039117120f010076240c50708074180e4000c01c1c0807854100a8440300850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 813175746 1250 813174496 813174517
    0xe0105060a1209080414030604020a12020d12020123010b1b0c03010c050d0e0f030409020717030a0b011101021633050f0106020d0f030b04270204060f0e0c 68
    0x140160b0782e10b40710700d0148520b02030262800c641c40d1460310030755102d98810b04c0340051085d0054810000140e9900c0040c1060f50a004918a000395061012868003a000388010709070824402102c8483c41e4150002c404005490014400d0301600c021080c0d80c3c4d841c203019410800c007003031080c0750100c0b869103038010010507010220790f0706503000c102003421515000c0000001072030005500030f0100300750007054983c03241000284524110400303966100c0c051806038007405900000e202c400e1081040402e01d11000d2680380d9962400c0c000003000051030254a01c40c00b00c0e96420386441d02d10030610075180380c00c0c4201000300c0084100d94900444942410750303107107844c031071aa2803000030003005d04104a500e0050740c006503904155101002c203c030164414400c5500c81018a200b06501c90000b018141450802003840d0074a03000007005441030713668100780c2c03481146152401d800325030a0120f00600a540800c0398540303801641e520f0700750324051010402c01030004542142040001401c04a50b03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 813176996 1250 813175746 813175757
    0x3051b062d070b191a132a090e010f1404090201052a0c0306060105070f021804060914010203090705151e040e0105040b012007090f0f060f0e0105060a 66
    0x2403d03500c101c079040056861600e03106401c00d56042101c07081c4603440b80320101042c1120800e12035400211880603800441e2101c5840700d07031207103102c150b441900c41b102c2c000340f03070724110300341c4038440108803a0852040941e90180c4c0d50001030101c00e00c10303c03034003900ca140700200c4014a00c00c09010103000d403058103d0410100b0418506090020201c600e06034010809152652100030700b0546041c070102030301031190300180305102c116a086022150880d9003c40220000c059900010320a14031984030203071000e040034204020401a90720203196144034142c0302c000c00d954040d84500300c1c007080358074031282e80c0410409c0c4010f00e071802e10480e050a843c4030f1285003030b5004401e25402040b013001050b24000124007031098042c01000c5a014020648081001c2004d40000030003141503007824029044a5015200c04c0003000d01c41c0b1005440c80c21028004130342e150030389600500c940480c0d1401180791000109080d0039070031198080380c084030300c4140f050b428001040603d0348543d088906008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 813178246 1250 813176996 813177007
    0x2130b0d060e07021f051e090a0c14040f06060801120804030515160c05070b181e012a0206090d140f07050603060a1e0f080706140306181b0403051b062d 67
    0x89000c00b254016005240f540462f051032034043c081a600c000c3d1100449900b48001404110fa22641c4641164000c030340341c03a448500b43c202001144110b40025006011311401c8800000c0c002c5030003405111300d1741c0d103500d5907000d4501c00c030740107a030b0f000c030080c6507800c0218100040c01d040c8000e805040010758403441c640880c10000340c0380c0380c0e13041f02051003140078103044411503800540c07041c40340f41400e12000320001c220440301e0702d050070340400a01c180c201003006041902c40308a208010f079405134591103403400c01c130f620300d9581081070311010031446102000300e030908010090b00e0052001410303000b40d00c0d04240e003458901c1880c41301981240d4031030310001120f854001c0c0000c010a1034201404d031030340c01d0030002055102801c80322159240200180040c949a07000382c404160303c0d118503044035464002d143d10b54a019050491000c0c1c030702003004424840003081c054845440c8113042104410407a01748081c6e8021000078118564001e1070f80b0704142c03141c0420400b070703085003c2c1071840c04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 813179496 1250 813178246 813178253
    0x60307090504050d02070602070f060f050c0a060605040501080a03051b0a0c06080901060603020f09040c0203041e08010c0e030307060e030f040b0a080a02130b0d060e07021f051e090a 80
    0x10380c000c5900303070343d250b1150880c072104a40500281d800740078207101134a219810070701081030340da1807441745204200d510300c0030114030f80c0f043c8160744a03408072074155a0541c0307250030071300040c00b100e010b550300c200d180c00c000140d51000001d840d402181d158072000c0c108500038141230000d840d488071040d0305010740582c074070011b1010711400020741041c1d01d0300e940c6401c0c4500b0030350071138181c5c2c1c1045050600c1002420b440c10001c6083e544400c0040320049500d81030b40c0c1c805c90450255034040d07244a61200800448803180040700410344030080020009104d03140001c480790b016036004103406d500304000c685c0104034560401c102c114840300032a483d00c280010501c20030340c0319a209603200300f004a002d09006902c031041c6d641043d804e400a41c10802b5580c000206440d10b44108000c0f070400042d20304072052a90090401000400d00c0d101443c585100043d440c0d1013500d421340481c0014400008040e001841030b00e010b95490030300e0700c02c00d01324090710081c40c40d4041e00410a61080b0800440003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 813180746 1250 813179496 813179501
    0xc0a0b1515030a060e0124020f010c02030406030506040911131b0309020315040c140103090615030b010b1213060b0a030501150515030f1003200a08030a0c080306030709 74
    0x91200400a4503503d142a0300700c401110540d41024000c038030a18010031180c820031201c0c0358078007800c6608040f001079070300b401c1e450300c0300d0444411902d5080c410076202494011004d0011501540c03024455a07481d00b080008803200c40c2c0c4001c00794070007190300030704c41d0500c91598030b100c0142500c0044c4060400f401a00041d040510301000207854000300001c500701440b0006480e48807008000142c142651020001010740c01030b9210b410700409406410b03840f82d0020040103401c500204070300000b400400040b81c00c24001500c4c0345020000000341000044112080942038800d10051615040c0700701c0d00c985203040040d9403654840760380d4182ca0792082c03030f80300003540325800003d2500410601c20350305080c40d42c4914810080d090040e504140141d0480707070306c0b03958a6043c0b60302d565040c03010014040c00d41c0016010940038104075421140002103001c01c16412290021b45503603030040c646d5248a10068540090940181940080c003000081e64000c03500030181e4106d9a01c40c0002c104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 813181996 1250 813180746 813180769
    0xa051c05010f050d02030c0907200105011a04081c030b1234050d230c030c2205040201140a030f0b010c0b0c03040303151502010b060c0a0b15 62
    0x49a03510001000040c2280c002100100016601d0201d000e02c0ca07000280c0741c480748050729000e442900001031000f40300d0482c452000c000d8403250514507510b410300c1d07402010240500d4aa0142d1a809009280020410790b000c03a04010020321b66142c112181d40e03159080e0a0b820001c0c1074444005414565030803061409000c0c4480040404005004803400580b0050480600743d41c078101c04a002020602101400c1d610160344e0880803101c5442d0405500042c241d03020422054200380b01c54030f03c1c2c00b0428001107402201101c0c5500354510400603207c01e1008818020f01080c103505000310308030f82141d640140141025091403540301c080181d00c0c1e00c01d901d03440010791b480641041c015001e100c4c00d4402c03002840c080d078501841d9a0f0346655008081d0000c10b18150100005003054402e03000004100800700d003e1007807584d100c1c5450343c00c00c00300c0c0544016501b491580b04003030a0803c1680c20300728080000304440d2140c0e48462407010006407c0c04c4500081610050a6407900c0c8810300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 813183246 1250 813181996 813182047
    0x41202160902070b06090705040506130e070809010509031912110f0c0118020607170f04060305010305060702120a050a0203120103051509030903030702060d1404150f0b150a05 77
    0x141c2e02c48a9142c09410341c900140041d06c5480798400b4410169408001da40a03900d041c0c902035a14049200c2081304031000754441c07688002d030642004a026440011325010b100b100c8024005034903201c900c0c0b030f1079005031039400d0030368941030151302c0025100315066640d1146040f0001569a01e045619586504c400c04402040a00144000002000340b09490480c3e465101c4000600700c3c81c1d00003201c1344294140030b0020784404210300c41074171911023100c0311905c401003c241d40d25907451000e0702401c404d00c4250f80e580105400aa81a400414000482c2c03130960842407401401c458295500d81040070300000310703c03080c0900c1081500340d801c2503001c0c5018800038144040d004082c00035000d4000c242e40720702c2c1c0060000034400e8800000340c0f02c6455044807081c0c1c40740148001e0b40020318554030103504000d0844184800d015015151111200c0c40e1402804041415405002503501d001816a00a2030440c800020451944054441000140380c050300e000081076085182416a48996 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 813184496 1250 813183246 813183251
    0x17030a0e13140f10061b020d170403300c060e030903010608010e070f0605031303050d05150103290f01030207080a020106051806100c02030f0a11040b01030b06030412021609 76
    0x113181402c94005000308158500100300d4110718020340000f01440700c000740180104102141005920b4000020181c10f00e07180541342c0c0e540e07050145035030b929100110106021030941c8c03105900b4a82c072031b4040051944a010360705200e50f8400c4014404040755030351074001481010791669080c01418010004507001040603043c0d0031005090001580c0800c1c0340b130306940410005960402e0a803503025030307422046460703a1268181030b10326110b689850424686420200b09002100340c404078101403013a83c04100b00e42c0b2111120b1071042000514540c3d0045101c2815901c0c6400f25900c0481c40f0103140140c100f005a540707100080e0440500c9101603510381c5014080750a02d80a2071000b402c071281e64420b80c0c200003020074000f80f0200700600800904c68440c0007036460800208025041d660100c440d0007101d030400d81c080d15030590030300b031040d810418200da4541c4240180075814038002c0c8041c1c40c50310345503207000500326080c01420640c001d03034036407140c0c801c80103c1c0740d0014800400c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 813185746 1250 813184496 813184501
    0x1b0b13050c040e0c10020d020715020a1509110a050634050f2514031c05040515210901060f0e07020d0206010b0f090d02030a060617030a0e13140f 64
    0x100114100c1c3c0e0b0f45d401007150703c8040c2413102e240d40001d014040311103816000c5440c02400070704a04007101458043c050602c0d034000030501071300d00c0d4030641d00c950040c0c4c854a0b082c00d4510400c41102c003a1f1151660041303003485840710004499418044003c245050341800d03100d0b0107040302d000380401d24240c51a410503d2214103104051003090311912192600e80e1110701c0c80c17100500c02840500074a00c0d4880419080c03489510108217884918031501c40400094841c80c400902c16801405418000d030f05004100300c89548401c2510041c0b01c0a03183d201c1e103e8034284070b102041da80209030400640d200c2270b000035220440380a03034015004100941810740b8050701e0217450300c00c0c0f56404004560000300104184804401500e45104020850700c0e030769280c4400280d03030b4a5514034040d625001d90780003c1d082000e00d5101c1c03030440302e000840c46004200c0380e00b001e0b02ea020390000707100458070303100c6030405501e4146020700d08104200c00006048800710030101c20264100d07241240044070006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 813186996 1250 813185746 813185749
    0xe03040e01090516030213060f0507200f120307030c0201050d090303050601171015050732060118020f04081905010b041503140c10050a1b0b13050c040e0c 68
    0x58290040044d41415460f150765046060044019032040c00100040326203000c801c00d10a41c2140c1030f080c0c120030822041907100d6108820b011078140820300c218881414200942003040e20102000c0d5824051400c200c15510b0542c0e0003000702c04200d041243c2081080c2d940e00d2140300c0d542865001c2c0d03500245910300000007425040301c02c003046030600340b14820003100600304d0501c802511040079004040d061501c00640d90b40c01901c8004290f01c403200550b810301c003020610a01820000c21011607005500d41300780e0b44400c401e004101000c01c560401c025012026001400008240340c6101d203002d90360a0ba01c0d040004000b101144d054807910280103014090280e40c04900d000c44080100c001c4003041c842c201841c610000380398090590864000110034041d80c40e40c0400582138480f88007404c2c40c000c00c660300c0483c8040106c0d80c8940041a4a84c0000c00d40240551043d003086207611640030211030707003c81e18001c40304c61046654006082c1c132903006460200d010300c0000c0c441940c40302d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 813188246 1250 813186996 813187021
    0x15010e1306150c0506070c060e1b03060601050703080f0405100e0606040b0f130e030c060708010e07031a0f04090516050901171c020118080a0e010207050a090e03040e010905 76
    0x41c2c40e02c10080030b002c402c0d0100f080820310036003000709800d0210b0029107034513180b006002400b0f00007a160184401c1c11107280800c00c3d030142e60782d03003c80c00c2d140c2c0c65031000d00541d628000c10350042d00051034000000c1524541030740c165005801101280c1001e01d1540ba01c0c810742d8024102204241c022105000f0b1600300740c042c004404a003126030141d030349210004aa400b0264000c0740200d591102e59441e000303a818021140710304e03002410364041d0324200c02c000d03001c03050071321542c80a1040b0400103003c280c4a4490302c284841151010580350804c20100004c0c03c40e51045181c0c0981d4540c109000144204044050f4659034003000d5411031820003080a01c0c00142e10041115446000c594080c120200c2c542c00d0b50700c410000c4030820214008102c1c01013039040c070b642102303900c400300c1041031003900405030444581c25500c0f60f444840080049803103607aa40301c0d00d0f8202407910f8080c04105503d4020800d207400900c100ca060580d00c0011210f0210282d1207003801556034000d0000d000090f2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 813189496 1250 813188246 813188279
    0x9040c081606030b010c08030703112512020309150a050c0106091d0a02090c130b1606050a0c020604060c14030115090e0f2d270d020615010e1306 64
    0xd0034400041d034002c3d1114071f0075200080810b4201655918070548a00c0c2607801d440105c02a40c0c0308a40b5019220221803200503800310540e0f0414408501d400b1361403002044400400003c1c141740c0c001b8110107655072403600420100e900744101031083c0c402d010824800d48000740740c1d1260101e20140c441e100c6404000610b541030461f9080500000f01607207942c40b00e5034000c1c85040c2419554080203126100600c10794000003103040c00045d044002c40b4550340c014201340d000d036408000d581c642c2c0e81c1050440d0f034280310341c2c400b6070403d0001402241081d44805101c1714542041c2203100e100340c0c0c1c61481a48240c12504a1054604814010302d61084003500a0440740a140806092164080401c04402400d00c01004d030b44042c0d4481440907400b5100c40094140c250410a080c043e00071520b8034401444589003c4400240c1201c00f0030004c2c1c00041000160043d005a03207918010803810111441081e0522150701e0103513229840d254445440c0c0c21400c3c000045450610b50700c0c0c3c0001040c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 813190746 1250 813189496 813189499
    0x302090a0e03120c070803091005010e070c0311030c070f030c060801050d2009190c020319030b0d050d0c0c0e0709060e0310060f082a09040c081606030b 67
    0x18000e9040312100000111510030f54000d82c000400d0340c0d003820086280c4902200101034820102c10b20102910006a6003440d444100c010720050380c03180c00383c00780d1042c103c440078005002e0800c03110129028200803601c009056003078a00c0d01010103c481c0c0f41a1240e8082e000c6140301500400c00d112140410501501442c504017a1a514200001e00c648940601c040c040506080341c3c45000070030003446080564028010130b08038a4122500420f034003904461031500d5040004082c1c540e03101000715001c413441c0c0084100903d00080342180208030304101c250300016195400000b0440401111030307d02c0d640c1da40c03982044440c2c5021040d1300c18940c4203007009100d039000d1114480c0c110580e0070659406291180805c20401d0000340790441c001c02040c0010724201001c100381050500000954107080112a4400c50034000c140701843d808004504086401420310350502e040a15203401038000d011050040340c541a0040c02d02403925509601d0840307084082041d81c0d0103020f03c1c0c8a4880 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 813191996 1250 813190746 813190751
    0xa11030405030c150c1e0f0d0912050703020612040510060501020a0303020f09090103050102090a1406032d07080412020307020d060c02011d070603060b03130206071104020d060302090a 81
    0x980400b20396039100c444030407442107038116102401c100034003065413481e02601c0102c0c1d0380724200500408014854100102c814016401c2c0d0a950703080c0041c400c0c0c04602185e440c031010301c0c41d1600c0074089287d28501280da9001e08000040581d03184805021240042c180b0000103042c5031500524001c1d400c443c20315034078200842008582e801144241071713180c05040c05684c0d00c52003404115203129600500c0d80c072100e402c0c004014020154007810714000c0c240e03003a80103161113904401921900d13080e43c03548800100001825111612000340c031540c0c5c03600c4d401600d110254044110400c0459070600002c4042c1d00304810b01014500c018140d800e070380051490f080c0c054000c00c508010f0080b003d40100d0721801c004010500c00d521503d4941c00390103445030901c80340c0600303e403541c1d01482400c00290900710701007051401041241e000e801108429070541500e9420f001c526003149000b0b0f20311042c0c801c40c250700368a986c002481d0b03040788441c0000b815070451042200300a030141580c4480c1c2e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 813193246 1250 813191996 813191999
    0x506241803150a02090604030f03091815050d060207080f0904050a020405060d05091e01050f010e010f1701020405150717030c04090902210d09080a0f0209101a0a110304 74
    0x2e403600680e030b04450316002c09a40c07102c000010070b510b4440c41d80000c1428104c0e45c50b420034540e00262800580d0801403030313905040c4111a6201c2074030100b002c880003007844000c0410081ca0003008100090340700f510050b040c844940c980480681104211100c030090000d00c00c0607a203464400d01c0c1d031100990108500340740c10240850b01c1030080c03000c8900d071039039144040b66034504200302c80b61920601d010b04020f07018042c2003030740c0a0081900d2561010a502001040300400c009419050329641d42c0072254071803030041c0070707810000703608034180043d50708020210301d686622040810a14401c2180d990300e803290725100c042443c0940b03035040c1110050090110405050048804407001c0d10000301d4201000d00018008494036912825004a82071000300090804292503140409549506036147d507166400c0f0380300c0c010400020141c103400a819401864100e070716035048022040816900b9031280022205004045505403d120b40880caa88a15078056030b0707410707501c260303401460425 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 813194496 1250 813193246 813193273
    0x2310060e010b120a060801020c0a0507141005130f150e0904020f270403080907060903021807030e0a060b100908070b0304031e0306031e11040506241803 67
    0x24010383c100381083d980e010000c60340380282500035002403c1c00d0002156940075032500c07035035507908141048a8500902d0300003e01440302141012448502608031040e10003c090f0490307095000007031110404403104000308810f0300000c1810081d0840c0c4d24190003860700c00c8805083c1d070b00000391040c49481c00c2c0d000c00005031540c001e02da08110068074120100d0500b446003500b0540c54496a03451185d03900c0c1004285680710048900840060080e5a100d40d110041212014968000650002c1c442d483d25810051404201c0750300000c2da1900240031200c003407541d0f00302002010151105c43e01c60f0700605042c582400c4100c0c078100c00c3d083c140c10036403030300070306a444102a200b034203221580400000e040c507002c1c02907485000c0061000700302d600701c404009002400c00340000d9407000400b103c03503003c11141036415520705402c018031042d0305202800f0000a800000d120a41066006003400ea01404250704c000003040f02108158558900d030075000400680b45003018403070750011001c102c05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 813195746 1250 813194496 813194519
    0x1050f060406090506011e140f03250522080a05010f0e01020c0c150f0705103204030509031006090c0903020d061109120f06250c2310060e01 62
    0x40c1030309034100e10b10b0403203e44016900c049609050704c140d400c0002c0e075814046001d400461082141c0002c0c0ca0303d422f06001d110b040c100545010802103001004034002c2c600b85401d2180441091205000510391104601810074110340703400c0b00e5503910b542007180024031600400b4591040302000b1801c0480d0030580946c0c03280c20800d464015180034003030001e10381c0308408841e01c14100400c620781e141400d1400c0e581e100b081c2c0104110003881d15040107801c02e00030b0805920040c0c5000256030300e04d2000c0020490b034801070411828041c0810076012107440030b00000848081017200000c40c0792034042c3e0402610b03005504030b820840c48100600050743e450510301ca003182c102030009418107050410003594411a0903850303010708003218401400100081883e54805020162901a150590120304c500c46c510152203211401c410306118042c03084405060541c0500e00f07501d000c1d80e050b84180074106921001600d20380004081a0007120280110700040a00d034044080743c0d890014400714 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 813196996 1250 813195746 813195767
    0x140604052a0711040204151e050d02030709080105070e010201051f1806050604180c0c05030306220507020105010314070305060112030e0312091314060d050f01050f06040609050601 79
    0x1108004030b105010b00494140c1e01480c094003410445d941c1d611001d08034220440282e614001412210001c40001901c10251003107503944d0301c034503040c50340010844010750002000181005104600001c2c0c0c08801d000d0303540100b207262205450f070080c05000900b91600104845415001c00d140d900b6400c0b500b446600444401a41c0c09204010810341600603204176440950320500119020990b80c00da04045222802d140e1410064080d8001f001d4030111819180074019030021300000d01181005454030100003416104079144a0020941004549040e529040140e5460005204010307074034a5405040c0305a900520b10103103190384003592102c050040b1124000c840301510101402042e000c0901900203003621001000c0b00038641498004004079440340d800400b22103041c0010b4401d42c1c5160881444240140c1d81e81c4082c05220b03050b03d6400c50b058071a422000c481503000388202c038003c8541e02e2030650130341400390400040d40d01a070881c0c590385181605110941e81c200d80d4640 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 813198246 1250 813196996 813197071
    0x1206090209030d1b1b170c0d12030612080c060121111809010f0606030e0606060a0e090f0603010c030501140904021201020a05090a080d080103080c010f14060405 71
    0x10b03e184c90b80e8030084900b601d03481008044140c494040c401314000c2c0000c0c0c03420358000700b49840c840d0741600b054640d2a040c0e0f445d400e0b001b902c1c144500c0013203202000c02800004e82803c000c07a906641e24062456044080c6040d1031510001c103056a90000031b2010321f00601040b800071100101003662502c0da07440d810401050700a12104100041e1502030303020300c0e0144085014108c2d4600318043c280644031000c404c99005107008004503030799020707104650010340084001c021a07039483d814404998000b000d180c0910901e154110900da4508650510641107481c03500d881d402c09100b0700d0309550881081400b454108001480300395035560407001ca40340111340e9400c0d59200c50011071032100210110560130b500006061254a81080c000d1490310310a03181c000303c05584141e0706460325000703428500040c907608010008514500040c10000300c102000285000c01c100c0c955040b0b81003001302c11040c02c10b240030400c035441d007441403650181914014800d802041d4828003070b003544801244 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 813199496 1250 813198246 813198257
    0x3403091208011d0405010906020712110706021506120718050c160b27010c0e04021207080403180e150406080c10050717070c09020f03040809060c0106061206090209030d 74
    0x10703017808003d403c4081c10541080086544540b9401c20a2421000c1e82d04603010074603100c40d0154a0100050350002c6508075030291112195000f290301407441e002d0a100d522001ca5040e40025a030188910002881e8070769115a8040703e1003020010b8800040a44e02043d0092040700c148061a03070020700c61562182c001807240d640c980d12058440f141182844a10400154a0f0f40c200c1055021000c6140c480d2141002c0100034020001030348100da041001403030f01d442c04038200f54041c2c0645500b0a1090512800c511040c00140c4104071880d4082c0040448180600c412007480c0c04441e4111001503c0a0007241e003088013841d52145140c0c03406009140c0c103030031325010078880c20070b0321412540806800000d5001c000a02c3c40c035040010140c0e60070540403000102d41c502c42c03003103407103014010403010305642d04c2741c845c1074082d0407544419400c500e041140c01c0e2803107001c0c072441c07000d0315070790b12100d000d2600e076072159040b101c1b1a000540fa1038810001d0940e00d54000449201c10f02807403a24 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 813200746 1250 813199496 813199501
    0x30c0b07030c0f06060501091e091d0114011418070810080106090c020d170105061e390606040203060a030b071e14033403091208011d 59
    0x498100c2c600e44030103009046641603500400404d0b420a01c1100c0090740e43c2d9030741c1500c411079145240c0d15004404050540407408001194168002c0b40802d40d05e08d11520300042c81c1d45480d030944401c0045e07242d081290800610070789015003c1101584400c0d1a4007800d1003808004441107000600a9810320030f00c000010b903030405685070740c0d0180600100a012199643c0c1e000d201800001c1c0070a405401224404101c0611a00b590340d0582c01d26045d040c0140d10f00400e112203a40b00c011010320340305003441021880901800144044854204811010904210580035070f000940b2030120821300703003e00e0b010040000401c40e4004904550048e900d485510002d14140c1a43c2e200600d6440300700e04002501c3d0304094109030784807800b4200c44182140d6a000c54514140c40600043e108061000c90680c80003981d0715038065600001c0d03000d00030340c0c048558100b00e40c1d414449002030f480711155400c00041e40a0840c018910f401c4c40c0c41c047d41401014814116001c230080205d5408000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 813201996 1250 813200746 813200753
    0xb04060b030f01020d090c060806090a1a0409050d09050a0f230d030f080604050c0a052212140303071e0203090a030b09160501123b06010b04030c0b07 66
    0x1602c00315801c0021540c0d00c42103003c05014020b03005017a5101e044c201000118180580d40403407054070014843e0445540d0300e4090f40013050701c44617020300c502004003400fa56841d00d100341e4148030302a1009050310114800010310022640e004240511000d040810084004449420039640ca041012401c06148001c44c071201c0c24403810698058000721012050540001441c1e611040079501e9101e50744c2c448050000707840c01552000c1d01201e007008901d40c128401d1000e094600389514a900a021504800d1018006240c010117a001c8203c8012020011100a0700d0f80b0410a44061804d519000034040e0a000c03549419022078401c92181411052023801210b00d0f40400a01581c01103850b401c100c40b080c5d0040b01c00003031902c950306801c500241c2c10043d1404903030050355208540881440c07400701800c20302409021200c5442c10740c0d201c210b482c1e00785c40e000403080210003241030700c00540c0c60700d0101d040c0e000852400c8100b0060003c2507a001c1440107450802e4440c507a41c0e41e0524 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 813203246 1250 813201996 813202003
    0x2030a0804030819030b0307061b05120306180412050306010c12030213090504050a02060904060506070821010b031b09030d090306050a020405012c03030309061e040b04060b03 77
    0x4000c02803140081e001c010400303404082c0c801504220b91100d005040040150704a55000d01445d5144e404003204214541c4240c0f0340d00d0000d042546d090304401d210340e0b180d516090030500c000044030b0000c810400281000385400644017000c038040d06250505448410003e152100443d04014001001440c503901850800000b00d510110b0004483d2503542c3c01030003034010b24100707020385907800000140400e07607002e02c0c1e00a43c2c00c4030103002e8a40c859400c01c091781c0d1043e420540c01a496500010700c0780d4031003000d80b04c500e00a40313000d030b80c0d2401d034081d0603000380c030020002c29103a40b0a80148520005201629802032003642100420200650200c4040c0502c0c1c40e040e0341071080640b6a162158004c1d800b00032288030308424006504d941b00b0400590140d401040e0002c0c540d00300c0d0114010041ca117000380300c114580502000c174002004282540c0c4103e4901c001d45c9e0100f018051941f480e942d00c0340d900c0d484610740100e0760810360f40c0d076020800d01520280000d40c80e01c00390902c41d074061 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 813204496 1250 813203246 813203263
    0x170d0b06130302090c071e030311040b120a021614010b0d051524040b06040806070503040506070504060e04090204060b0417100c051e040315021801180504090203 71
    0x1010a500c510030781d5401d141510302808224041c0013440301050030440c0748402e45000035805004081d0280799011140d00440c00404140d04140c1c503072880742500c2c0074080061001e00040c100542c2e40e0201000038001031131010700b80c0300506104000b45d462941c04601c0200c80d1030b034013840038800180d090700f4190252001160003a44200c0d2000c02004000000540d181c80d00c0c0e0000b5003040c6e41c2c0d240001d100c01410020300c803000325a19444000301d0381c07030f19910031041c0d42001440300307083c9a02c031102e071460000100c2d030001c08144000b0910003170000402003154042000e10300103280a0401c0130041c014038034801006e00458881746584210b40d5940c000740050f01034881150740301c503a154031606c0c000d8410680c1c1d81c0e8501404101e005404010301520f4104840c5031030302445d26414070040440001c0c146000710104406100c00f100159400d0ba040c13075a090340c0100540c54007441d020310014141c100c4882410300000d54010320210b802e2a20410881d40115400240c0d500300380042401c010340c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 813205746 1250 813204496 813204499
    0x3020409050c030a0f051b0715240e060a060c050a0506150a0623030711030a0504140906130f0207022101050603030c030f0310180b031207170d0b 64
    0x205010040c2103140034000e1441900030080c00e03c21710048412040490700103545e401a18042d450301c40003d00b807a0300081200c6441881c1200c034054003200048101e4404c2000d030303007104103089196a00c0c0001a0001e4001d840703134004260060801000080e4441150b200740c0c81480f803180440c0e4140007040c007030382000c1d64100c800d48202d81b401c0e0303055203001d81400039024420440d152000c12400c0c42020808105c404600010415000503500f0018941000349144c080040301d1802101c58441480075162403002c9888458840341020603120913140d450200f107020b01110000c20100342d64041c0004141c41c004a000a58284100001800f1348528000a03421880b8140103590004202810852540d2000002c03c9a500c48001301070701c5e48604800b0610540c030a0210541102d0700c1e400039034000700d2200c5000c10443c1d40700c8903103404110603000d2600036903969800c80003e08090100e81c0010360300307154103407808000307a540350002c0e001407010b00380100c000315005007902c10991080c1c00c000d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 813206996 1250 813205746 813205751
    0xd03150b0703030b0108090a0c0902131e080706031b0e01120c08180105162703140706051303080d090209180d08040804120c0306020a110c10140a03020409 68
    0x80c03030030050b0203880c0d81000540086c51103400941000e030041a40314046a010b0703440003085290665280283d04802101c1c134640313950050003c1d1500c0001e0791450446004403a010034240b5099503103080188940c810803d0504200c80d103042402c0540c5103100078240c908049040d04903280040b12a400348260030b0f036101d0301e0f20402a484079080308101d481054248140041001c101c20a58241e8600741c1d280c0c84603000e10700500f030149000e4040c5082d00c01da4060a507210384a10720080401c00400d030707c2980c82082e945146200d91909024520180549050042ca0f100c0c5009031401e00164a01c006001e6a00c041555030417058035820106045800070004400c5060005206259172180000e40f4140e2003000302c0d1820950064100318071581d00b094481c0d0401e480e200d0f07280c20405240030203c071292000390700407002074058400f40103074002c250349900c5007007a51215a4907040402c0c0b252032286525210b043ca5041d84281c1e01c5600c00c8084099076241c4015003004ea02030700039034200b01c0c44c450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 813208246 1250 813206996 813207007
    0xf021c0e09040c0305011e0e010e070522020430020109060309110307030321060608061509030d0807110a170c160b19050903101a0a12140f0d03150b 65
    0x1004031f040102d000c03009102000100d03038080d00715080701e0052035418019089914208810b2610610802030804808042285002c0c80e002500032071f4003d80012540c01071002401405588407003002e140c84000307503011550b05501d50006030044185100f140c04254403200070200b0441c0c5409030704d550b00d00290844d00000d4491038040c002e0682001401d000032a48003209826410b2030055000301c030140d8a0b030040c5600d40b4000d01c40b4600441d410412621810054030b186610108010841c034100d943d00c460650800040082041c113103e80c2080d65070b40024401320200b404d140c000c1e081c002d21a44920399501d00300705210300b0301d01480c0a81c1c52119892000007540103c40c1c0040018203c11000c03081d03100c0c0400025940c0d8000c0000039600342d800300010508603400b59001c1c4485060600369130002c0c0c03200d0b800040d01d440707054100034032045600008004120401c900021914180c0c80580000300c08501c24a41c0d9203001c1c00d0410401d901c400c10385251950041402000d0f04603030690b10740d0348 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 813209496 1250 813208246 813208271
    0x1062c01051c051c02010c090b03061017040b0115020106050306152806020c0405130303090521070203012007030e0d08040b090901050334080a030f021c0e09040c030501 74
    0x194003091300310016500308085950f20f80d200d05103a02c107480103041c1c064110f485071800c0c4140c5540d1041050b041c0000c00c03050751104040212440d1180c0c0c403d50604032658101076525a10300d540b0010041561f06202c014015550003040690b03000075140c2030303242d04c071403070b0000103e182500010120400c408080598007030500d05507070809481d019004c4400d81040c46007404204c8004907019920340115203011700c0000e220360412800e15005000700c4000300010700d0701d80c035410301c4a05110402d07480040c0303103030440c1028050100044801880e542d4407a6004900844600c10400c0050030030841c4050340700960707110349a022946800c41c1c41540c541e42c1b507103082c404560011036510700c01c000310740c00001c4520740011403e900034110680403108041001200104401e010078290907000150000b22f1b500360104100029240641d42d004035130300000101038103000141196100e08034450150b40405904480e0080400406a4082d04c0d25034ae81c2c24682c032040700c41e4000401c00d50800f210001c20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 813210746 1250 813209496 813209533
    0x4020a0206090705010c080702060a03140a15080601030c120303141806100f0918020d03020d0f03050115080a2a2709020a090905040501062c01051c05 66
    0x409801c02115a0203407100c00544c2c9680308514002c2c0001c104008c2c44005041007400b5148080746400d0120312030307405202d14140c1034030448072650416034521160300c0b86400c00e286e04000b050107030040c240139415030300c969034500600e00401c04100340c4403c000040510a6000e00d00c8030031030800c8210241012249400702030314400307034801a84960000b00d0032003494a8074600031a1a101383c203603a124a400b14260140c0034518503044020800541e40016071200701580144910941c080c0c2032445506c0301c080e11200309008440201031500c00103004c1c03072041000700400500326041021030ba50b0b410a0040140c0042c030301c4440b4040035a444e160840380052041840c0d00100c3d254000c0d00c444483c43c05d032001145004100502c0e0140a04100701052640140b070307001c1181c42e011650303079100c107140b0b000d40c0ca0683d0f088886030355800080110050241c00022800c100c44003148003000315030300d40382d400e00041c0200d80c49a82002d428420072004480d103540030f20341c480142c94150080503045801c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 813211996 1250 813210746 813210751
    0x406180c1e05030114060f0d210306060801031718041a0f0d022412010308090307050604060e2b03030605040b09040f0b0705071406060f06042601090204020a0206 71
    0xc00c1070018034080707058601030154115512554002c45007070b58410003080035207400e004180d60000c40b1840c50502203003511410b2150340350440d400c1c0f00e40d2910300030002e0403210b65601c4001005015401030000034a602e260ba0301c1f1000c1340c0511611503404001c0389550080100c402035029191181c0d0f0081d840110b00b14075844c160440718640040150341c188020f07150305080003980f028264280144041d20b94003900441d100780002282010140c1003a000d040000303030811345540101280448442c503007088850040e05064480d182014a001d10140c84007100c07010389403180842000303107240c00100d205809948448501030100d0403103039082c0035004001341e00a0501540c10043c3c829003900300425103074003c9500641c20102c0e0043c0791901c4800c00d402810440810104124000c04224005030b11107a50704000c001d05210b0a0100801c84450000314607980984014001041030002c400e07030420750401c1c900c02c05542510504100c40c0100038050b0000d62241c80851080e103c2d66000030001d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 813213246 1250 813211996 813212039
    0x412030e03160b04051531050d0f061d070b070b0f042112052403060108060a1a0d0305070212060405030421050106141e0303030406180c 60
    0x84040d55600240721920010f40a0000c0703c11080204000508100d042e08901d8086c3c185441d0a10200c194120381541d181391800c2e54a020400c01c0c24821981359440c07400520046800b0090189985e59500c4000307080c03000940f0856852118041c0d04101c201422001c031018410b0300d209e6504d40f0b00d0600c5680000a01380d80510b075402c0010000240016424000d541103115540804c101000b00c911041d080300b04c8204109801d100070008500d0b90140d507014400307005440401c4540590400c04c01114000441c3c407982c0082e00420090303a02140f02500000c0d5200086002c903000a4151058481800c2032a0410080f44241c410f150340240a03000c0c2900c01c8840051689200740d006950740004e840280481d0030802c41001074901c02101038085110000c0030010003026620b481d07003140c0440d03202c0908221203d500c0b01c1c441c60203120170484000c00050840e004030044003c00d0b540c0c040140000c080c0c07651514809000000c00000ca80040e901802c0300203400d03100c0f206582220361510400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 813214496 1250 813213246 813213253
    0x20418020d030809010b030105040c0e0628230d1101050c060405010501051c0c090f0605330a020616030207051e07090b01080415110a0512070e090c0f0412030e03 71
    0x70191f29060041074051504038010310783da5420061011070420000e82819404240b0301c03440a540e80d07880b00c1c40882150200c0000c8103d515140d4241c0c0924103000c0d08415030540e003012220569070f006561080f8681011410103900090b100603112171054043c10344c0103100d000704002c1081f005420403810380340e0584013209440c03500b000401c0000108a4020240d1000001c140012507050744000c610a0b150600405c1d4071b40e540010a01e42ca00d110440b183c044100340c054401040c4503107410110003c040712a900d880760640d402501c0d110701911541d00d003403250054a900500c6078064075421600a02036513500300326503100300c1e841d20f0101410405402aa4000602c07196644900c02c10100107031940c050b076907070f01c0d601d42c400a403d031400050407030fa88104c0d20041c0400003001e8280740c10076881c0c2c65510b81c000c190801140341e000302904101b0045005401050300c841e0800c0780c02400b01d0300381079165120381a0180c024016500520031403964000f80706d09042c3d105d0ba0b40c0140290550030b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 813215746 1250 813214496 813214511
    0x14131d010f0e070812030a0b060f0a08100e1924060c031101020a170601021f020a03050c040f15171005091b0405150405060a0305010f060201050f04020418020d03080901 74
    0x44c00d4540d140c10303544000ca00024400950301c000c664220440b1900c00800d558601407561511360341640148508200203140391081120000c0041d0225010300f25004494540d460300c48101d0790800454541c80301d40c2d68854500c0000c0b80c010132150b48181108403000d0078a941c86410007020010700001c2500000c419040c5045401c0c0103100300c45203810181c0d280e182c011005000344901e0000030300765504602c9100c01c42108218000707810b40c6044a2400e0142c7d036443c0d001d000500395074026013102c804403410041040315442418007003085a0400d00c5082c00d01c0841034081e200c005841c200c810410014104010f007884030782d40c00c2c8099803c1158808210303181d60a02d00e650f490554140c0280410403c0f00b442145012840700010014400307a003481c1c59216808030300c280c0c200ba00003401080c1c80308018444401c410344c07410301401051008016914106038841201480600043d001d207a40d242c40c40d0300c0001c210b00e07000200ba001740c142e00060500c3d242c0185100b50484001d0403035442d0902 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 813216996 1250 813215746 813215759
    0x60114030609060d081c05010807090204360501181404031d15040e04060b1906031508030a2001180212030909090f010614131d010f0e07 60
    0x50300e0103181c000d40442d036a55103034410b201104480b0a4251000c2c082880200821711950040c564504a80d80000c00c2551425240d14030746506a0010800c280c0103101c24042042c540310291606e03e448082c2c1d00d107104441070305848440b00c0d000314444060912002107440038014000061040703000350100265022510a41404401510b000f400038854040d00e502c41012842e14103c2c001000300310000c0c01d15800e07907801c2d5590040d07000980604440d810001800105e00c101c1d41a200c040d40c00342052000825000c00c103108902448091590311007a1905401c0080c0c4000094601d11040300d40d02d02c814400548400c2c06060412030044602c98065034a10042c041d0700e8854000801580d440590b80d0308205801c40d500c00c0c2c0c0040385c0f2061103004241c1e500d40c161076004a85c1d0718003910940309a5846a800d54009030844c1e40bc80400f82100306907500c2e100041540e40c03d800304001403880307a05070000200e0300403029001096083c0001c2c5008084940d00098a0904200440d002c40340d4414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 813218246 1250 813216996 813217037
    0xf030f180c0907110703050604021008160507061b050d1a0a0b09041416020f0105060109060509030a06290a030803040b4c03021e0109030206120601 65
    0x1000c00150000c00c0220020300b042c9003001e41144190900c201610188015a40341902c0e65000f1380d020b91110050005508101c80081c0d0070300b031a4540b42844c0c1c5030000500c0100c1200500b42c01c108200060488207100003540810b0329110711413010140c6001043c8014466000180729000807480c03d1100c03c0c00e1449401c6186d1249405003401caa8107207011980d54840d0881358085401c641c950084c0b401d1820380300c102d1845950046407000d2a004c1003000245482400340ba11500d5078500024880d4a80e0885008012580d1a00d46980e941a10340c0200f4100351281800030703c114103000380c4104116981c110110701840075118007000499820801046110910000d45200300800100700070a160300e000580c0910000c0c410030380d107019402d403420001140000d4124022a400c0180043c03011454040c075a01c017101c0640b10380a0541d000582c1041084809208500f820328486038107900506c001801182c000f080980c88101c0180c031482048000c44106002414118804c5c8113103500c1d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 813219496 1250 813218246 813218281
    0xc060907080d1206080601150809030a091206020c060f1b0306090708090f0a0803040201080a0b1003020d060b03090d090f03031b170d0603030315120b130203030f030f 73
    0x100c0c02041000c10009060324507190103c404281152a42004544c04004000441c002e06c40304050015002c80c156005100810107803640740a0741080160426051b030240c0c1450036214001c104020702c034150314100c0000d119080c0841440d000c5c010801c0f210b0034440120070b00c184040120900c1c10342d510084109544011039405d0f5001103014003052100788146101c50b17202c0c10100032520065490484940342c1800e21300b08a42d8010b0010802007156845052540c010b061044140000d200c180009481203010b60401010558049041c0300c1155180e00180024a1440764550340da0404001c656102c41c01c00c9103150214011413000504500f1a8613207504403901a43e40f0007801c0d000814060080f00c000ea07040d5894027081c0e00e8008849800001001c480681100006060703107149400360503200b20244821000080e88000c110080010a203502a544e01260b290a5503803111890350842d005200c000e50540320214900001320501c000941c099429281800c140c0c0d55110804491500c24 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 813220746 1250 813219496 813219509
    0x2190806120a03090b1b12180a061b080d1503020a0b0f030106030c030213120203070b090d021201060e0c0d0605041b0e01170901140112230a050a080c060907 69
    0x1000c01001000701005c043c1113a0640c809800c40d00801c2c0386280c40c584404038030213017103680300003c0305030903107031a160008000c0c901522003500340c40c6045005448503a64041d0030a076405000982410041800122610300c2550031041010f09184901c01035480905e0001328010b8044110110f5010042c8042d5150300e845d110101e807031030307080c0401103020f81014a10b074018103409100e002c25003803081c4200e001500100100084158446c01018034040865204001d070502c100901c0e074050f101d4090004280c0d4040d101d12003c1023000616a00511007540004080a0000103100100804030000c10310b00203070760703028041e05da210383c01c02c41242c6101100c1d0324806a651701c45209540218036113013001105041c030600400c20382100e06180c2c00b00300c5540c00943d42d030b088000c40018082e84d406000d05585d010f60480c02c00d440e0388440d40d4217810314ec01500c41500360b0995000580070001c127403484d5170010130741320803c0d480d04e800aa20340000c2c13862011400f400700007803807035040041c070f04040350706 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 813221996 1250 813220746 813220757
    0x1e040f09120c0606030507060c06140106021b031603060c0f0201060f410103150506041712120411121011070203010e06160804110f0402190806120a03 66
    0xc07458000d4403840c0807100e00303c8501c1d84440002010034030501a03140140100c0c1c507241014200d40c502001185e0300d80103110002103000c001400042d034009010300740703003281000c0300c4020071104000910700f0060168038541c0540700d040110401041d034111501c180c80036104c00b442044a55030903426202030b4001c004480c000100200207640344041d410700079000d414540c16050381407800c0521074200740c0c000801400510161440e0951f41403049085410741e076144074041c1401c0c0380005039207205d14885c1081141500140380f55212090205640b090390244105641d51701d20031030200f0000c011a000d4030340a599404040207814103080010240b10820040e106800c0c840120500400c40e125224000480c240550b0b40141c07824070460036854648030090400346414090140d4503820310801008000b110002c1c080064110590400900030480e000000c0608050200e0024001c0c00240c401a0092860120815410403410785c028101510f1140041c10b02c142e003240c0c0d420324400c00800090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 813223246 1250 813221996 813222023
    0xd030b060703081902070f110a06090e0c0d020f0d0f0609050112030c11060a0903050708010902010215060102011404060213050402210405120a02070e01140109090f0b1e040f09 77
    0x1078001c580204c1e0146031520050424205803180310484080c400300320742028201c4101440d525005528200401c50342c0780c0664181d051425884c9480383c082e2012408510110780003107508800e4044d40c2c2916030030207215851700300c103c021758064504c8004543c081440c1031000b1403c8111801035074143c95100d41c100c10b4500099808407050542c0800031f0703a403003a0b4a80b01200d1541c03010002e040040f80c80d40c0e030440c02030075401d18600704030640d0b00002f49680740c07011540c0181d80104003030190090b144040c40d03c1e640c9001c010b0340507081211102c020444210100010032409501802c584041200e00d001c04988800030f001c105d12503d07903000b6400800702c40180b50200c158456541c0a40702e901517440883c0312030441e076034a80013000382001581001d03009012107030841e24258014050414102e44440f01040081c15240140c003815103860b484036500f503130410f03064201050350f0340c1c0600500500e408003031820001c0341c070350201148140e040c02d0403004007078454007515501300d8210280f0261030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 813224496 1250 813223246 813223261
    0x30c050f1509150c0102090916080403050a140406030f23060f01030f02030a0506011b03050a11010e0d0e030705040b09071110050a0603020109090203040b0705090a0e01080d030b06070308 82
    0x541110021950164000f40b0340c25400c2055030240140505510015031180a60f80400950600003040040003200d54a000e4840c00d501c8022148c0007909402c1c090703580d481d08181140c00c94026516a48040d0000400182055040c0c0c000740c91841000380801c401000a0700302c01035034aa4410740c0110a0300720780411074070f03c0d142600183c2401c05060001d800000d840380d80d0243d07042100c1d80c21626a40c1c20070000156080030f1903243d20541461880713080b46c0f142c2d8010b02507000c0c0208600800c4013200e00209075040c2503006003901e0484c1c000f15200018240750042403044145038050180c010081e0008032802d290290400134240204240d40940c1d816104030f6411051a01d000d00505c1002200328034411980300351805400d010b07001040c403d0540c0000361080c100c5502040301d8031f10400411001c2149000c0e09038002d0060302c0c00950310780c3d034040001e2481c03d01d900000300020308080001130260000441c1d892440c4103450600c23942501d6000c02100e03005911020b40030a1a40e0006103c0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 813225746 1250 813224496 813224539
    0x302060f0c070e0108010605090f0705182110020406020319170c04080d080402011b0c17060f0109140103121806080720120c03040305030f04030c050f 66
    0x20865103682803840201003140b4010580e4420b0038081c3c6001e005122400080c02a41c020f0034046c0c1c0d40038602d00348400310244805005000004110b80801c41181c4841012000003404200030041100080c100081401d580600f01e43c0131600d100d66120505604141c2c001c0d20300321034054000d9801c0850640301c0e2220902e91920030010081d010740d51405441100c02d0034bc1c022420b0391011503c41c0d00300800d90345460b01c11034400045c8040301003000b006030f91014558100303039400340c3c81a00c090a10b241507560b00031950000300310611010346562207000f001a84500c200c00b101c050203004d0b641c414209045500c120620040b242d01d00e001400030544803400070703003100802e03d007040300c0c0c165114802640201a07048000061615803c0c812040d0340f101013002140c09914403000e45c5031815426035030741c41083c58060004a00800e005000c0081442a500115080300a8075540d0f20021340c81c021507442404115150a551070303010506007070200010488240c040d266a031148503e0064112 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 813226996 1250 813225746 813225757
    0x50f13020c0106081f0507031419090b0703020702041406030d050a020313030303061511071a0705030a0305090f010c020d03051302041e0f020c0a0210091208040f0b0307020601030206 80
    0x2000c2d901e6040010b0008403c010b031214904001004649040a404e03204c1e0540300301a01c81c104060501210000c520100d152481e00800f0840c81c140c0203094000140d8081c00507090b01030f03c0c0c28203890402072195099001401d00605c01c850400c014955211801c201940039140c0c15056401070050034000c41c02440100500702a50040f01d0404003040400030000400c0d07002240065103a00e801c0104074030660324102e1800d07080c140b1303404070b250706010a03a40c0d02d0244039800c114172200b118020401003500841e50015004410340b13544804201024010f0070040d00c200d1030500c00c0c2841d04a2480d01031041c0ba808401a60190810b8200300740e049019180c0542441240343e19000f280005136298880c607a400c001038856581103805180c05c840c11a07001144040c00b0f50b00402290f010403001141c298999541120780b01400c40982c0c0084501e484250401c5c500c1da030007059500b060143d40c4005d0011988040c40d8180303143c0d10b41501d50480c2c0029500301001d41d00580043c401450304402500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 813228246 1250 813226996 813227017
    0x603031e140a052d0d1a1005030a02040302060403050c1203120105190801050f0a0f1401030605130b040f1209080606150c011e0e0304050d03080604020f0301030b10050f1302 76
    0x30500000c1015418600c6040c100d10000c0590011740c809014500740102115281780862800d0074079441c8003c94808100340103c44c042040000c00189403107100e1703068038007175500640121785851f141d240950340c039180c001c80240300e03001e2149010480790700001201d2652480d00d0340b01a0756440e04050014010520109543e1034000751804036401c0340074802c403440344503001a032007114101082204102d4403c09080000710f8200b05a52032840b2840860700d0441c1e600100c005402d0b07460100c0301c9042100d01c00024403190340c3c10b05000034402c2d510500b240303070790090b01c0a00354600d464200307580e107011901c40d00a4540028002403a1841c10402560605003050b100d40c0c540611480c0c080d00310f807200500c0c000c5100442c0b04201c0b11000d5485014020b40c0200000c61506041c440080c0b00d459195500400b00000c03100010406c1d21107405448100308030320001c40d141c2d40c40380361080b21018111440d501d44400c004001941e0f281030302c4410459200a44062110413100c1c60b40380c088c0d40b2251910 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 813229496 1250 813228246 813228277
    0x6010306090507020a0c1509031e0c0f060e09040b06040b0f28120b0f0c0403060614180708010618050a0e040203100b030d210603031e140a05 62
    0x524000c1c28041c01d4443e038520350103040c900110b450001760a44081e040802c1d450340c7e5030b00c44c106954200d5041010780b80c0003042001d0f66100344400320f8541d09141401008441444400030300380c1c01030b004181c01d4506944030300004078211810300010020441e030103808901e0000c00700c0c51608003640b00c11f111aa01402c13002c0c2c400441404240600b0741040a80b11450f072021680d01d450200300400c4020384a4050040a402469207a01c00109005820030790840410404189d104074103404440055500a80c2031140d16500e292442c02d5610884031a8050500541d201c155080c448100603c281d00c0798403110f040ea401c008013243c0342414040d4580480c1040040803451759035000c1c0b080c000303000945441c001c40c80e044c0b05050030941b500220b8105941040c00150103640c0216600446172002d16000b0105220403141d9064a00500301d18403003285080030201c00d05074400b403850842410204c02d4401d40343d14020071690303445400b8010341300e000c0600c40c3d500c40a1281e80100420080035200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 813230746 1250 813229496 813229499
    0x30c06022e09061407031d0c100c120906091d010e0604060801050c1806070c03031419121512061a0619020601060807020a0b091f091a0c070b06010306 66
    0x4190444c0d40740c042c120242c109070020005481c2d410300800c1000340c8885c1c00c1104c0b0790495500d6540d40c43e00550360602c90301500e03200d00c1c03c6a204400200c1c0d2103410411106080801030009018180305020b20741c0051445400442c852204000d4441040f654003440c40c0310f07030720304a040e541900c80907005982c4140c0b40c45002801400c00d01690303015202c0c080b80c0c0303a038900080710208a10242d00500328001d080134425000803030301a205443c2240d0300340c28401d0061240440c070a401348079459151704244d1090f50780902d07050740b2105050308803025080401c00f501104003d0000c0c034003075110701880300304c013100000001f48140e00b110307a405001808040312010303800c000803255006004041009012202c030025095410000c26005121505042c000c908081b44002d40300c5040803006400c0000d000007040c11508100000385488075140106501241a5042c10002e88140d69099402840c0841c54400c0350101c1008640984130440381286060344a82c0c5034850050020b001d541030650782c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 813231996 1250 813230746 813230753
    0x904120516240b03030a030b01020102300708011a070c0b0406080f0c030c0414030c1c0309080c09060d030c080304111c030e130608070609030c06022e09 67
    0x1401034056224a42c88031403008485480505004007401000c039990800b0b807181220b8a020049407252040f925000c6010381003107005070b0180c8502840111a5103500e03204c0e000c2c5510341143d11210030000610340c0d80503150300b80102c07140e001c28010a00000140c19a000000b540003008102c1b103842003078941407550340d076480508540c02030307807000000c034441e4410401c0b00740901d07009a030301440329003040b821814415040325043c019070241e49071101d0905070000c003603034040081c0411040c000b0701164203140c0700036801c07240d00e070700070781c01c40100c1e42c2c1480c0450a40c9000c23404848503140079000c19140d076180c02c1000a59a02c208059051000414042e004039110400031446540660144413030007030454140060000f4188449014a00758080c5000003503005200850b52201214440440901003890000904030795000303403400d124030040041c0b030355040134016080b28004c810152030b0690b24101640c840702151403c01200101c944140900801c403903282d1803403240c0c5400050031000325503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 813233246 1250 813231996 813232027
    0xf27020312030f1918020607060b0a030c140f0d0f08070503030106091d061518040608011505030a0506060d08090d030903020f0d0f0227070f0305070e09041205 70
    0x101c0c0e0f410700b1102d4208104110101110306116560303040310030004000810140f50403409050402403003264000790701d0702030040c02d8210885c08130008100e40011680c914008070803002921501e852104903601c0700689140803500d9407920b040c041c00300b4004110700d0361000342c280d111240496150314184030120124204002440c081c1901e42c40d1040c0c50780c01d1444881d00104681509030b17812003140100509511446481782050a182c00d01e00e40741d4075240303102030a9802c03951217190014a042400a11260f054112412040782c190904c100706482c0c03030074140c43e071400c643d01401c2c0354004400b250103410503920015400d0b0160440c0740c10a400200061443d400f41c2d171041d80001c0b0010018402c0d0314082440e5001c2c80022901c041030602c0e15540c56030a5190700c103010b40b140350301340e120321921001e0a52036000c01585e55103011403440c0c40300000c0c1110728407031070f100c0010340f6100c0003940942c01842042e03038410008104909968076981c4050450540d0300c0710030100b240030f0141407841031729207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 813234496 1250 813233246 813233251
    0xf090114100503060a09050309130b040207080304020a080304030327090e0607020f01060f030f170f0c0f0613080a090f06020d1101060605041e051f030f2702031203 72
    0x1281140c01c081c501810189030010143c04502e0301d81c685204280005e40000440350440d0702590044501030310400840c004146420403070f0b0b08a8000500842007244c1040203601c03840c0700b203e032a803886441d014010b68070f021380c0c00b0090214042e501d4540d021001c0c7e80d5441c1c00c0400d01d0403008541d6032103150078400c0d2405405503042a61117030041c0100e00b0303010721902442e07c840304001c000c204d00e49002c442c40c800b810321000d042201d020325040306110002c516007000c1494000c0c80340c0e69250f140456140b0703500020011121340076152480402e0304000c40c1c181c7c0a40034080103d02040919100d5024540c0f05181507428850020f030700041c240e01c40c030780703240c014002078000d000703c01e901001c00340ca511601640e4007416450020b003400195041016902901c1e5940c50a4a8910490315100e080300503c0c0c100d00c1d4001c40008074020103040100c800d0042020743c1e07800788203d48503509000203aa9100c0c0040f000010b49611b2504c141688000700440b040c0018112080428213480440395035105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 813235746 1250 813234496 813234511
    0x3040630020901030e1605060d090b0708071b030503040303180501090501020d06060c0807170c031c0c0201090c03021002010b13050603010501080303091f020d0c09050a050d0b0f090114 81
    0x11a68000e250380620030380324180c1205c0c02500d180304440040c40e031035924a028017880b0b035a0100380248038200c5a0b00c90151144c4c400e4400c200e03802c2414000d8080d0f84121100400120100b40c240000c141c0001c100d14003a81c9511010b0844d12940e9041d400b03414110844034220201240c5003022540900440c03400074024400142e580789100a804181c90140c0c11410031300461f01010000911004126100a5002045104000310300395003130000740700c1d0152041b01c6100204650340d060b0062003022800c00304009040040b00b0548809900360340841030082d10000369984200058201b0428004a01056100015003003a501f0006080b0315110741d644908a80e0350420440305040c02d00c2158090403003c1c0c015070451800d0780301c4590364880428902140301181d07148400344001501035840d0440310860902412080445c001c1107003a030ba21846105558050000515040851000900799040080b041ca1a41c0b0a1301c500103010000d000d82c0e41c95940e9962801e01d00b5080c2c1072150003201c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 813236996 1250 813235746 813235751
    0xa080105010809030c07030204050403091d0105010906030b030a1209090f02030603010513020904030530150603070e0904390e070c03110a050f0706110f03040630 71
    0x50000040002000030440207a43c4c0c02000342045844000803890300700da074102c0e0007003010307591450300315503900a584c0200385c2c3d041d156281440d06c1014051084c10f0f20420b9032500c034800d070744490403030903103500d000c10b00d03050340001070000003250808409000850036070401e203480356a15403c503000c41c3d14801700000d501e940030080c0011443c083c050307150408401104103030988100d400054a800000e00028284140043d0031141c48190b80c00d1070880c4040b042100324400d43c60b4550104c0b0010458998000d01c10581617401c3c0ba2808100350f234025030381c0fa52a90101180303101400346161010340180c074a11078a06109000c540c8100300480f454144241c903003020440e040d8002c00608058009070314101d111000c200030740b83e021000300d84c0240c0500d03020b4410454404081e05200c1c040501030901e0191400c9142c441000080000c220f9246940d44024850462031850315010842031141c95500b0070001000a01c2c40341d000044001002c003c82c90341100000303e0018081022900950140e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 813238246 1250 813236996 813236999
    0x60903030112120c1403180409240e07030b04151a150f3f0c07030507150203100605030603030a030c120903020c010806010503062103070b13210206160e060a0801 71
    0x9421080c460400e4009503010f1002450a0b038ae1000448108041c0003403140b0f078096004200c1c1038540005c0068258001070380c0599407207041941240504540c1076841d003400354204040c8a0062050007030843c2c412090810b404041c40c20081c451854840c000d0b40301c0000c1c0b204402c1c564201d4000e03c4419030340314aa4440c0ca000c3d20300c07400f207a8074400c42540301804801e00ca0081404055510b680080300309a002d554009034501500e0354082d412002e0240c40d5090b1841181480d654011030141c040820081c074000da0ba4031003200c492104030341940e0036030400e10404580601941020184415500700104088801c1c24420115501c411050740103a002001090369541c00c21a05a00301400786071861842c900b04001c20400c2c0070150321110702980004003810400b40c2801900c0c3d1050b0302c0304e28860355080130300750304554040c0b049065405064980c46081e10390166400074100e0361b9542c000d4620759803100c4600e1214141401071200f44066001070004a035100001000d503c66291555000c95 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 813239496 1250 813238246 813238267
    0xf2505130f06020d0906090b09040908220f05010e0f0d050607020303040c12050a0b0c0f0d05040b011202090f130209090102030711280f060501060809060903030112120c1403 76
    0x780e0211044117025000c0402e00c6035540c403550030001d4600d001619a0b0300c0f1040404a802001542c0c0042c2252b407010400c00070b02c15403c241080408070142c8030310400c0e501c0302e40000604030b0a10500740865103020500c0280d0030425141481480c0041c1550704500c0b00303403a05401c000040300c1d404016080082040200240b800525020f00f08401e80c080ba10200c9640322a81d0303819020000d40a6507002c400a40441d285604a0381c1c0c2d40314844801d40c803003500c40d441d0303c0a0f200c2a05c08449501420380082516030245031f0720580c050300100003405a0312445040302c0f021001400e11490540401081d202586560003050300880c008000160b403480c0c0080014801007110161110030781145280b51406210841c000e144078400318450320074801603103804082c2d08a10751000344010305040001a41c1a0010b503180d01c81c0d40079909450640d0343e024002510703480240915050240d00ba40850042421290010601d00315030901041d590070507180d00000003050780c902d0046610000d0107121a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 813240746 1250 813239496 813239503
    0x204110d06060201050c0708130512010b0f040504020616110d1208070f05041a090a060201140f06030a0b040317040b071209080301090203041b0b0a080f2505130f0602 73
    0xd010364402082203042c1603007081024812064007900b20707013002ca40380701d5a00c00000010b00038a0014001000d50380d02c104510f018100cdc140d6003502c9600c20280650715070a10340600c0d403141d40c0c002c16246c03400d101078960070756224401e501a02d15801c03146500b10310f600d40345046500d0303501400d4a5213103080000300c000d001c450000e18903000c101d145c10703c051801340c0041c103070780544030780e242030159143c001c020754000c0380201843c540d4018420080020540c2d01940705910140101c55018400d6649a034032111100003920000c1e0141d00070641c15000c214100342c0140c11038800d2a201c0100b440595071030700f17005820307981541c07101482d60602044507008101c640c016541e0600c140810b103510b4450001e603010510580c0d003080d800000140410030002c41420240d008140341c40c9a1541b580041c4005801c200025400300e210080401c0c4208441f480181c852001e4075440490070004140381ea82c0400701403c0b1205112003840340ba1b10104040915601401000038003004d00341ca0890001c0c80c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 813241996 1250 813240746 813240749
    0x1416180b0f03060606090d0f060f0b0604030812150405040b010f081911031f021306030905190201052b0b01050702010c241a010f050c280204110d06 65
    0x10480c60105041d89546010035115406541210f03103c0d111000c08012072002401840001c0051070006030304002c001c260340c86251800c8000b03000b0001c0010070710a12020f441140009081381d442840607a580160039420254054007000c40c1e02d507020000310218081d650140e0381203400c06645070051140340a200852402003035414000d001016880786000005954608040c0c40d001200520031a981c03820040c40c5545503429450204c407441c421160b200039081000c6151482c95440400038419109004450708580c014018004494014204002e03120555000300c0c10700c032040c807030000700c212024524500400c0d0600d016209065000f641c1045908144c521414000c080c0304550161340c4c00252600403c1d40400807030148035403281d0302c00040c4400703111082c1440c20503041c05200c00c0c800816400c0f40c0000c1e2200103200c1005082a01d16009005004055601164040352103030a0148800d0036000c1e02070030030328012030a4012505490921007901001c1e840010a44400c01c414401c210 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 813243246 1250 813241996 813241999
    0x180906050a11090f280317040e01092412060b1503180a060501060e0108160516020604030f0515010b0307050a0c020402090901140a0605030c071416180b 67
    0x46a1a010401d0395039025070b61006000303941d00070122006841c1c401401059481c03806100480440d540745244282105000481f00744503400d5102c10141c44540980301550418000701d50160300f04aa600000c0c45620b80c580c0c901601c05075841e150500c2c0204040107004200420041500c090134100e042d16a544001401081c0d10784560300d104c0e43d04803e980c0c00040214401620b00c001142180c600021041d002c0c1c2054a40030001600740c1c0c00c01c1002402c0364003a22032020b01da60301000d4500390b401010480c40400c0040040d1030f00c0c0346600b00e40f528041e20040030365003455103a490b0031210301c402e0034049403980c3c030000e81c08655040e0003100d0340c0100300c40d0034a5403840c540003400034420b0181076104010301540c2e00492046644070b4041d01c1810710b02411000056030740d4000f8a100300807030200940601c515440204809114404981c840d544494080c0c2c40c0844554959104d0b4180140c00c2d10680600b81941a0413144800350380020040300c03903543c0428500d014000c0889a0b040c0505 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 813244496 1250 813243246 813243251
    0x51e0d140403020a0b071b0b0904050f0f07200717123103060212070305060f031207031806110712110f030c1206100e0105012007180906050a 62
    0x2c01c0140d561468040c1900d0a4105160329982103182401558025200600c01507900c0400419645a01d01c003910304000200e0b018072668440e0314100601c500181d400d506800b07001400500c00d18002c0c81e038003181503041040118410001d100d083d04021458201502c420301a201c0082483c00030026407855500850780c00c1d00d803a040c1900d0448081c0c2941400704400191968a142090030303001c08c000864100a09655172400162240010001150207101092038840032030014184103900f080144005401022004c5e14003460f403030070b03030480c01c400c80070400c401b0101c082030a03518050300020719540e00c44041c42409050700e64140700540d040306c800f170114a401000425585601c00c0c075400002d0340e03070155007130820021030300301003054283c0c0d0340003003120720001c030081d40000780f0300e1042c0300146400d0041900c45800000161082c401c1c180001c02d841109040c28804824008804900c07904440d071665444d40f84030070b5070004a492100301c5950300c10920a100d06801010392003a00050b04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 813245746 1250 813244496 813244499
    0x10f0614120f0109060e06100803041512020714010c08011d06040e010c0809150403050406050a1701060906030501080c010c0b090f07331e050904360305070f051e0d1404 74
    0x2cad501e014074812188207807400f0309125030807800ba031182c0480440d8090150b50755100d600341000751211660000361a91b00c4d1818100c4041d1082d801c03a07040e02c1d546400e084803080b4010072660000c8001d0b04450340159100345241400e4000d205070101090503454070b070560700e000d60f80141000b11010309c002c030303014040041000280c2c0c4001241c0c19501c96045c03c540700e0401d40300c01c58030702c859648402d403501040c50010072515040302c0300404642c4103550503c02a80ca4244540e194060703002040e0104400d8101140003135809a40c0f15800b0300c00e030046621211306404402e00d060a01c1c0d11400510003140c458000382d208213070010700c50412142040c0302c40c00d20700780c0082081880310b01249202140e01c0a0f00703500c600c660100e59019031300a00038041e59020040b26450f0321032140038110b10780707006c11101e01b10148d4580301448042e0141c4506050071401d441b500100034800d40225047d0041898108082c6074039038288510000400040000d1810305d10090078200c00c499440d50005800e100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 813246996 1250 813245746 813245759
    0x31005180c07031b020a140f010513030204020f1c14070305070c0b0903040e09030a020706020f120906070b0406050f0112020f2817010f0614120f0109060e0610 70
    0x1154411a0b040c900151419100803800d40c90404c0d0410007076102d52031a2000481e0401c030740000701192000c4a404d070761450000010341705486100d41282c50301c000b1541c200003510740799026001d500200c9000c2d514001180e402089000c8180c12031840c6180c0d1050050000c600200400c1d5000c811414100101d0604c42d10203080303228000030040103482c0c03010002e0340714142803050394003e01392006003046034100aa10680c581d084451014018880d543c400100103200080d039040c112052809030924144201c44462664130040b4025001a810031810300003440c15a072540c440c80c003c2c1e0000a0508141000000d10039060b8040407095158450000c00350751543c121220364182200c4164200460070410107001020094414041401c0800080e55511110040e0f003032080c610002c0010009841c119011603030341f8081c9160507980340340c90403064141504650460440d503021074100440c0b2500183c00e6900b500012540713240c44000002d081c02c4100301c0f554203c4052010135145605062 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 813248246 1250 813246996 813247021
    0x106050625020f10020c03060703050c040905060a0e0a15050301020c030f07021c051e060f0103142517030306010e0607060618061d060307050f03011103100518 70
    0x1074156000307000da01da40c0c021035071082254082071070b000c1c2c07504082061040d40a0341707070058884c01074042d000300ca0004980c02e2003403049510490740540c1160030a030403d0911002440021300f41c903040b01c03002d100800d49441000e21244504102d14022601507845038015844041a0344024003da0050004094044000c402e540108100c07410042d1180d00394000100540c8100b08888004406402e07500248200071038290141c100c1011402e011010300c40307400360307140812200c1c103113002050340042c0300040701a40b80d01d1200200400303c0b1f580c008007500348000800e21130300034118080c101030200501d1200c40030350301e000c0310004091801e618180780040c050150070400244141d5001642c072041013402c1e80300c4405040c0d11100a0003c0b2040000c5200034000d030301420706145851000d000c08600c80d80b04132445900094064449075240c03130b040c08140c640c40074490780d01d55214104060b0350030f6140c0241d0311501e1607a0fa0086103a00c4c0c00144042c0008440006840c0c82820042150401440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 813249496 1250 813248246 813248287
    0x602300a020901031d0c21120304021908030d0c1b02091b040b03061201330b1303060605030a0b1b04030203031c0e030a0804060f0608070801020c01060506 68
    0x40c80050307680c0380c0b4240102c0080c03c2601050030080c1c65582c034070b410f9140010300a40c8100050321b4040c1099600010054440480c0503c481264440185500007106200c0519080703840540306035401c00c1e1440459007108800d401401b403d81c40428400550340c003501554840c9000ca09140c024905100d6041d51011100c0501030b015800b0350011440c140140042502c182060400c0c49417101e4990200082d554002d480700b5229241c022492552124103120361106410701c030000480301025640c010a049280a010700e00300c0000740c50014080003040c008040242c010034a41e04400d06515104d011640305410050081c0c0c001c0d0703506000240b48104058100d500035128418120b00300022100c0b512694100035003501000c1400340d40350b82e080b00340100d01300c0c128606000203c001003600d0b50300d012310b015400c001703012000401c000c61000d42c090000180c407100041007040e202d03101103140580c680e03c074005aa6002403480c440e80c0082c4540d90141c08c046800600e080c00d240302c40b00111940 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 813250746 1250 813249496 813249511
    0xf0d1a2107053f06010602030a18060f0c15090507031a09252c06090c1b0705092404062301030917070308061203071b080109060230 58
    0xf96105030005501414210b000b184001080329010360b10f0b42e1000351070790411043e4030042111203c08150398002440315009444d403642e41d42c80c5c640e58890040780e07038003801c06080e11190b00d1a4540e1107841c4141c0500340c0458040c40040001e43d18501e48160b018036000c81040b4140200024018030031404944038000854182c07a00ba2007040c0a42010004200e17507110414580d503c1c4071205040e4400c14081d803100c1038280710a44107540b241c0610521103001c80b4051210b00042000705d0200100392001c540c0507031044201c130b225a8540380447c00003003060b5058403040040c5050010000e000c0354040950760003d45041c40050f280c02180c0c5200e2110b40446548514a9403090b4000d9120340c0c00030300d03119005900b103a405d22081e80e05101c00d6218500940009a0a4000903040d0601000c00d400c45855007005610b0710f030700c4d0380f07d0000c030080310908688010100c290004485d803090190f40c1199014107801039549000030541900c0e1580c44e0030202c00e410081c1540b030024203982d038120341c4c821715 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 813251996 1250 813250746 813250819
    0x702012a15060e04260d0e0d021b0103110d0c02030306030609070311060c100f0209010e01090b030a0207051c0e04180507060e0d350f0d1a210705 64
    0xd0351080000c5c1c03541140c43d5290494010803030018028054000740400940a02543c05030408040c049880c0d4a40d259221280200603021103000d500c20b9200c602214201c02001303091907181c07030261041e01c04052940c80180d001000303110041c80c007442429006007416000b054054a965207000c0c00c0c3c4500041c0b54843c100c04100b60904500602c03c80c1840d01e00d003881000030001e51400d00009410000800340001c00c0000c40300c0181d4064000c1c6410346010b29500c1c0c2c15996407a1009001c2e5001c10003c5605010b4140e1044406060099803940e000c590f49031b041072603510760144011030743e1580402000124902403031002c180302007040e405803030725480c10700310104001000c41c0002400300001070625140052540036050705034487e0a10100c580380036151349103403081c00f61b074a005042c1080c842800402486a6a002c0d65010100010340140c440f030a4250600000e11105e03689034007070074a45542485848035202c2403203084090401150250310081d8000022040c04854007208404000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 813253246 1250 813251996 813252023
    0x218070e090c16051c23070f08070c0503010f020421050111071401150303120b1302030108030903010e030c030a030e031608190c110103020702012a15060e04 69
    0xc02c20741142d5003540100303598450103603246400d50780daa226900c4807000009280e8840c0c5001d105030f18512203d4113400d01c1b01c5424a40c07015030170f15a4400b0780102e591400c0d0002c1c000010b100040500362044c02420095030707240c40e000a050075140c281c0f070803150f50303403040001b80500d41c10984200c1c2d00d0b014159079901c98042c0703031070014010304420180e607030056408602041001020585114400305101c02484049541a1001404003031400000d0204083c40c0d1021180d9a0380c0c0d000d802d501d8002808040039024100d80b0008a074020303000f9a82c140c000059560700c07070500f4003030440001503000041d4504a040703003645403030b401105000c50400d03850f1803c20f5070243c03040050700c82d0011101405c07403500310545009002640050056035043c40c000c0c12114486000d40000c00b40d0540100c9009029150180110000c1d402984128148009012104408000c0d0158480c1941c128095031007450308a04110113070600071403940d9059802c0600c14010040500903032900b10368090f1101500c00f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 813254496 1250 813253246 813253261
    0x11010f0f21020f210103030f0c05010b040513061503020619020102190906020f030a1d120f0102031509010f0905091f0501050111010218060a09030813030218070e09 72
    0x10742a0340303400381203140042110402d001c00c801c02014080320356545400b450740144a0754001031401d200240c080381180c04d031851020b000c1c2d0f0320307115103034428400000c2c400307401c4000508407039080d1004ca500d1b040c4001643e0400c600c1c1d00ca0701e003680c20000c01071104203155500084082c422031003040c56118040250304030040c001d4058610500c00c2c4c01e43c40d00000035805000346078415905c2420010300c00c100a00303401003008411645071441d140d4419041910244552000908902d4203a400071f030f0340064000e204a09000203680c03008440005a03072410303c1500118099044604c140c803c6181b040100000802c0700302c030307104855101c4400300701a903c03462010b09042e2152001040c40d2400010413400700c03041c0e44414140c490903202d4561107159000700a00301d004a64140b400980884101c401c0392a002014000c03400c06071904903000c50300c1b9590b0003540c3c2c00c03840e10240d0407480c6000c14800c5180c10304000c8082081100e100c5071070301d02103000815018070046c030390703000b0940440441c012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 813255746 1250 813254496 813254537
    0x150607020301060311190b03160e12011d0c010e090405011d010e01060b0f1e1b011407020d0f03022505101103090c010e180c0711010f0f 60
    0x203400a008010303555903420024410601700c0700082c400c03001d4055200200d02c0c804911010768018000180c210790345d08031131800445109a0200c14170001e1410660f0341c1c0e032298001495403071030710008181d070440c84150800301000c11030144900d2304158111181c90340c0c8240c85900403a070480e114241074031136081c01401004030003030a04400594500e081d0750348005401003045481268020004a0f0744c41d95204a1400f07094912509020108403103000d902c00c810740780b10810001221145000d04030503820b02014404d03031021200b651100f285e1500c0e1543d0301000f41d03100342c003800546000c08a00b50014048400b07404040700781769000c40c00c50351881ca0b000d4400d0201900b0b00256107008554104540d81e00c26104421000c0383c1400c03030500700382078100b05aa000707009200091206100000044d150440e80c1941c9a03004058180002c101a6418001c01d00620085034015925111750a019550450700d031134043c1070043c0ca0344e213408483d50210b1888120b107010310300380854408032121a0311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 813256996 1250 813255746 813255757
    0x102010e0c0420221401080109020706290f060c0a0b130f08121b091212030f04030908010203092802100201050a0f11030703020c07081f050903121506 66
    0x21a8001107005881071110700814400002041100d0b202a0341e00c0ca00e41240000714405c560016040d01c0040006000c01c2d00a420b880c1d00c14000402c41001d201003124480c00450042c03985801141540120383c10203104280d6800415140307d4a0078040245c000e0351641028401044c2010213000600e604078046840e0040c90b5004240c0a21805c003800c2030360b1113400c04152544140000000f151020091040004025140c1100d0341e052030fa0b01001c03c0b82c2103129094800c4a8000e00000c980344580b2000114030a41080e1203030b00030f9040c1414000c0240b01035412001850384104140a00b0801c001003410328180511064001c4200072802c02100c031445250007034100f00ba40c903000b05e03016019000b2a1050104030010040c3c0c8059041030b0050301d150003070754844c050b0108041880749110b60000c04010b070301c12040341c0d800347e55040b0741131401020325a2185a00d07880300580001d1500f5000d0a0780280e03140d4025820900706000c0c3d140301803400f03030896070143c00845101c0c2540d11008103452 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 813258246 1250 813256996 813257051
    0xa0c020121090b090c0f090601140c0f15090a17190801090b0a051507060204050a24090e13050f1006091407050d0f02040902070807030207050102010e0c04 68
    0x41800c1084107841c00506501c081c02c491252440e000159800340c002022481c10303c001340840c075003400c420140500341031302602003410800019003e00300041d0b1107004008103900d010080181c09208a030075814a100d0001c80c111100e40c00042c000341d120009100d04034613400030b45a140340e030646c800c5500c00340300d1003800411190041601c40e2860ba00000340e14104d5180d1481032090381d912a081010340c1800d0700400354824024020f0101840c1c00c500034280346807003135200601d015210400960080d189501007001075003285408201107800e0300482035010540c1c202401c5283c20003c480820260003080403d1110b5030f00f40308810302004009940e0b0240c0c0060544900f000c2ca200c044004c0c0005014400d032103428076030103103822000d91031814400c840e01c2d90b40d10704102400c00380d40058903110300820300b40380e003d000200341106948000d043c8180300340d80c0142d65003194500a8108400342d807049040d640b420302035941100c4081084010301a08031000200c022050800c0c0c0344112940800c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 813259496 1250 813258246 813258287
    0x9010b0d090618050c01020601051503060f1c1509240b06130e01170706120b1c0b06031c1107150c1b0b0711010302162102060c0a0c0201 60
    0x5450320021a000c1d0390341c035400b80c0c0c16500300e684120010b9030784223070070311034981c10400c2c0d03251041c1c6030003600c405075030808002044180b504140300005000d000040403d480045000e81b04c0d04101b02110348000070500402505004480c1e4507120114031140b142d245840405080c0300d1924401c80d00d901c003591602000340400c0d1184c81a441100c00301e6814000d507410820704500120f009a10032105401d0b404415006000b0541060000c0300d1401452000a0417140c49072000020f0365211100c0d903843c0d091100c0c001a441d405401c0842d040e040243c0181d0007900102d028100340b50009445000450311410700807024801d10040d6480c000065010051100006403010300c01ca40c040c81c3c2c18241d500032011070000007a041110300480d103240c414a280004200000d500103030b240082c02a910105040041c10507141403403a400282c4400d400311444100011941c1c41c1612100b02c08803008a20f2006001a1030081024806845040b94440900039124803200441e03100d601d007040703140100da494 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 813260746 1250 813259496 813259511
    0x50d080915010b0c0f0f1c020a06020a051215010207031101050d020409091101080906012c191104030506060d0f02060409020d051506030f10050a0b0c0f0c09010b0d0906 74
    0x3c95440e500b1405040c40700b4003800144002c21500000c01c60200b00060b0090048500d060351421540b01c403481303680c02035000300107194002c01c01b18405814201d04a881c0e1507038400f150808a12100c078010000e4402085a5a0a24090f42d00050703050641e5032014000780008400303c01171340c090007a010300704801c500014000c81c821110b0b8108010442c0310701c01e045500980da0005417008081100e0740d5482d0390008004111072554048143c5c030207803a007041c10801d410b55069154241c08125144501004030002e03107046903410307209181003017000711200c900742400c41e550942c0b6107502400c8180300e03041c4d07400d5503024408500d102c00700b413950081c54240c1d610340d2401074001940010100305c43d003d01d4040000c58070b00811040000d87c142c000e20070362442d40e80441c6005a03150180490b0341c4100251800704040c0c0f102580500a0800b0800403515200c0740010039242202040a2070a40c0d04140001660750300d0344c11002c0d064501c043c550782e80344c191b01d1601c2c000806054401a200c01e041201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 813261996 1250 813260746 813260759
    0x1a0a0e030c1c05280f020d0f1b06080c0904020306120303040f03030e06010501080105060a2709060f06083108030109140c19020a150204170703050d08091501 69
    0xc441c50b005101e4016205030b142d10700b00035060020009050310418040942000005a540801e0f0000c10301c000c2440360481032030384564040002032101202c10711081c000d0282030030000640e010003030203140741803600ca14060281d04854001e40303200c02d0007a0380100c0072691943da007460180d04900001c0880c0d48a14182c1454901c402c0340710001c1d004a071400b0400004000c0108040e4107941040e1a80441e60340b9041c1404825072217500e01d82e00304000380c41d000c2000b003250140808604011645010900c0c14151110102c3d4113940c0000300e140c001200410143d900000900da102e20010031240c031743d00c5050009041c0e4409601c0302c0c03074120880c80d4007000300084c01d00910b069a03071074141040743c0e020700035101140703203002e03281e081c4070550030b10a08204107200d03250003012074080c0c410740b0340f180c0d860f80d1400c445500d0003203900d10b125004102030144020b10101e81b04900218401412810f10359160303030340c4030310b240b100100c200314000c000545d612804102ca481c003150100e1a0f10559a034400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 813263246 1250 813261996 813262039
    0x1505060604140d06020a031d010b0306130305090a03050c01110a02150a0c05060f0a0b010804020a03110a0305030c0f01140c0702101e02010609060902070b0c0c210706061a0a0e030c 79
    0x105c1d1403002c080708060a0001c0740c0144540501c07103c002e0001c08ce10345038481e0300b01240f8507109088003000800c124015041c0c9643c10002d000354840c2c03009043c44030070300d400504442500d115034a01c9501c0039200d82d0240c0d642300c00320403000c3c00094440d95140c140480413280a010000050071510a21081c01142c0031005c0c00b161240141c130004002501c210401115000000c3d00c020f544074142001c00e001140c0d288403d100d240d40002c140811280c1da03a5611070030b50b003003084503c0f1a50006501d00d82a00c5003805400081080e05103102210f01d0425120070340ea0244400c00781c021401c00f001040c059003d1001450707103803000c0380926401c1a800038024042c0c1101d0082507403041c1400e034005051036060080d50075042d441404000c0703e82d600ba0761518250003154401c40f451181014200302c95030364070781601d16512000501c1d5650415400d122043d40e07515800781502d00c1c0103854010a10380010f00745c03824403070a4580291042443c200191a1510800a01b940825040a04200c04800a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 813264496 1250 813263246 813263261
    0xa0b0f0f1b0d0e03092d10050f0a030603060e06090709110912070b03190b1e091f090c2a03080403090e040f1505060604140d06020a03 59
    0x440824103660345554650011000301d00d1801e208a400384841c402c41c0e000c64106601e15500c0c0411641080d68181c0007410052010038001a84410000310100041201070342079030744081079494509400440c00000c1c401e00c03c10b50403600141001c503003110300c0c601ca034005000640e04150244000c5800c0c1c0c0c82c154460030182c0750500c00e449003001c00244175800c0e008180102c0e01445d0300c0c0e4201492181809138681c090419808180140f09000c2007011840d4043d50007022424821026a00e140c40541c00311003049000900c11501113500f0034002c080f03506103010064007138a0400160300c503800c0b0b103c0020040610410107461104000c01e6450656100343c0300109103540306660524030078106444031030120713044a601c1e45200c00c0040840c0c0104110b0703070454842c0c60101543c44d5a92010b02e00030a003034504440400451200710188a5010018164108400020040340c2040d00c0050120b2003170b489910315480103042e8a00b070680d200000405a02d0b000310055580b9000342d84014002c08a130b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 813265746 1250 813264496 813264511
    0x30406180506072001020d0206070507020a0b0a0306230303030114131a04060f0b040512031209030a1403130209090a02180f090d090b0906040503010c0f020c0103150306020c0a0b0f 79
    0x2080400541c03000916150001e4260080e00712600c4032b01045a503540076540c1640c00c90b09214000074208000d138010325403958140c0c3c0001c1c005e42072408061540c60441300c1503400c0a40700c0c0007a0081d41d00401103c1c1120742078088281408501000f0400b403445044140401500e0401c502440b41d41e011000c14040c0e4003101d01300150381d21000c000111050901400200e0791083c0403d01140c01c0c2034168694200e602e204a03810080b20445140f00c521081f02c44044c20741012610070000740e009910b0100c41c410261903035095103441c152503d0714000405c4060301c590549004500285401d01500b43c034141c014001301d001c43d02c40d803c4480c3c010020b83c0c150040120001c0003a4062402044600550380503075200c51855140c1016810960400260300740d102c2c90801001031540c1d401d106641c18140103441300007154405420190074440c0540c881d03418103040c0009500c1400420000d0020740f40d100c3e000503240d00341654614a01440d6800003025202c162080c040c807030b852014024400e07205c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 813266996 1250 813265746 813265793
    0x1e030b041b1103040b09130608190c06080114040c111e0d020a050a030e190306140c0c0c151e04170d0504060305070e062b090503040618050607 63
    0x4910105030b56481030b072103240401e41c0148841c00c01b610382038000c5000c16003044404590706840345242418404030a4802c0d000e02106c3c640c100411201c0324014000380410b0410020540c5050071302c100d54032500160611641d80ca90751205003a020704115000c0440700b000f00c039240c900001015941844044007804144a000803000c141840058501c10455103c006003540504d10b5406440212090718500d81c052281e6a40050a00c00c1c01074501c0154080c01e070125421048103011030104902901c5207500700390030000141c46030300c000390043c040c40c806d891400c00d0401007500e0011a000313a082403000c10002490f200381d0200d440c0301600070340d84a80340062141e0350f009111035a030511001c4400211340c00b440f00b00403042c000d42c0b10319440075003030800000c01d400401c005402580030141c1029140c411a048034140803907000e42c6038000c0c0a2640812580c250352300e4807680c0307026034860801045413210300c0489488404008030b0042101802c9036488060701e151000380200400b01030300b980030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 813268246 1250 813266996 813267017
    0x8010f0e0109080a2607031d0f030301050d06020d0e0717010606090510050c0a0b100609030206040e27060411091b090d21020607050a1e030b041b 64
    0x40184074402c0c41c10741c00318141c4c0c90b00c01009019110b034031000a6100c0b0f9821032000300c910500d00e001880e88160400d130780000300c102c1c1400c08103240144d1a95008029400380d401000c0801000040364150f503011030302032003203c006243c003002902c14288442045410994004400e00c000640f1500703540429003a4030140342d142b00c890303007280e074075208400000e4180f001c204501e0410742d141c01003480c26403070039500e0206001c45035460702c1d081030021030314000340c14204000000c45040d110050041490700740446842d41c0c00055240c02940181c510000301080810700e046032001507000b10402c11540d00903005000e200d00b9888020481f0255810716400603844098500180607038401c500c0342030305181806e61004c50821030f030003560641c1d0301300841c440000080f03012032840c40045812002003080380440308100904151000d40030070188202440950120f941145003e840540340c2c0e00c204002d200e146c0400c50141102902080c0c001c1e2900c00601e001e01804082c00701e202c00c0940743d101059 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 813269496 1250 813268246 813268271
    0x314030f0304031d1c02040605010306180e0f0d02060a05060105070f11240c0c010219060911060304080c0c0a050307030818030102130e0f0105010f052208010f 70
    0xe100e041011104004200000380010f4014515820700c881c010201a1010080c84003141c0042c13946500d00c605001140b1540b011803500d806114040e00c4207180a008407468003400e010500c2201640c02880c988684440513428000c00001a46a1038801210340e444098000691542800d585080c209400c240006010354018400c54040d640c1c06041c420601e41d80351140114803208000f013542c400c48a0b540480300c440054503581890f4500401941d130340302100c402d00d180030003c02c0c9031030540d000402014060308881c1c4d0807a100310342186002c11815210710b03000c6440e05803005501e41c822800300502c0140600d060180049035985421034003000f010b00f003000a07000c001c2c400d06a040d4018034040c000a1008409082091008103102c0241d229080000703013a80c00030406d1020443d22154208803000004142941088030070303c8491040d41442c00007041c2d04c40403005582413180000354880d0f00054100458180c4001c40440300d0426142e40284c1d01074a900e0805c58aaa802c052030039426 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 813270746 1250 813269496 813269503
    0x605030727030f1a0703020d051b0f13050603040c150809031c0f02040303020a1b05030d03020901020a06141f0b18010c08030a0207061a240405190314 66
    0x1c100a40400d03118240307140d030342c158501561036080700c3c00c48078801001c1460f050f29294500a02c0300d9100561a901c2d1240e1810807904d0007040b068164501c40303042c090001c94181102e01e2249125040c07555900c403503014a482e8115940402e030003100000c04c200a003d49003803181d098441c080301c003010074024801c040391856010703107028403c1d4204101d03696560350030940c151400900004003055a01d108240201240c115600c142e0168203d101c1c1e02e001c03c41050007140c540006035052400c040d040c000841e0f42c0b41203041c04901410790005000a13260b00821100c05031513406403003448082800421184100c6082d1914820340001c12034100143c418001050701382c5030403005540c10100038450000f44da14075016028140051450a01c1c0440d4150000307610511819201581c0c403030151401c0000c440c254004401200c95000a6440c1030f902c0321214081c1e070307001c00d808219600800154210a2141d64071180d44420f5108061f20000c00c810603060484e07000d54030001e02084c91410f103688 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 813271996 1250 813270746 813270797
    0x80f0a0207031e0924030507111903300c0e0603060409021801060320071a0a1b020c090604050609010e0a090c0608040615050a05010c110a06050307 65
    0x20496040c035a0340861242ca01c6038003181c91904e007003000166184004403038a404402400d061281c40076800c04000e41501811f50866861302e82102244000e0410a840c0c0e0210040f280c811080c0000c003505042c0310740794040041750340b85480b00809a64102c4202c150380107213602228181032401fa880d020f80124910706003503c000d00950714560f01d100410000302405041240c0c4040442421413108055a038014081c20180d10000f8140c03400b0380d041424084054050350000104000c103a00240104500030160038001b1034403061500c9249140000d00144582003c0107034488900c120b6082d40080c3d070507520710040d00c5600c59512514140020385004a40e5240c10540d2040100300c1b0021015041c0c1d40440d6011000805080550b1803942e8400183d12410020340c4400600040c40128480c1c0c002d4002c0c00504026860f103840d0115800c0c0030745204050501c04811140014007078144000101c041c0b00602d2800c680780c4800e009819a0410381d01c0800150391201c001c0e0180d00c01a0503001e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 813273246 1250 813271996 813272003
    0x510021f020a09051219030c11030a02061812030d0204050f0a120308090f060f011419090e150129030601140a17070207150e0d060b010507050607080f0a0207 69
    0x4003e64109800d0100200391400310500620828a042080c2c2c0300740410030f09201d01c03942c0c230794903e6152414080d0b014068949903510a803c0380b0314187c0103030b803050708031807075802203107608100c00c116540050402001507036251464000062500b1a00303840b03500070b1094a034201e65040690200b071042c419110018002c0c10708640408c3c0b1101c021901441403960702c10901d9040390329842c408000181400d40594840c10f00ca4a09001408590b400c2480000f06034021340e00300c1000d01c450b007280700b2920280c3c8119500307035648819484c00b0801c00d0000600c2e469420b001d400455039030f4481c2420051a2036000d1005039018001200c9042c000c000301c4e4002ca5059482c51a00e0140140705015940302e065102c09010062203075a0101c0a0030503942d224001e65000b03410107519049a00544480700e22040e0104240d130b404c914403940d04c0c000b03030440b6141c104900040103210700c0d0043c1c400380704004d006086c92080f80d041110840c0d000050a21496032400c10000030344840b9800d600342e0084081c000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 813274496 1250 813273246 813273257
    0xe070e01080d09230a030f0b06150a0804030807110609030909010503030403150c03020702030d030617160e0901090c0e1006050a080f060307050d060f14060a030f0c0510021f020a 78
    0x180d0781302c1c030300008820100d100420788982913659950b01300f0380b40d035108000c507001d00134103007001240d141003000301c003003103c61100c00c9207000c0c40000024030300e03000140b0041c00d000c0c0c254003042c1418480c000e00302040d8690004c83e919030402c505400d41d00d070400d1910610804c112000440c85040101c250740c11268403140b000b8095203085d0003503018100c07041400b07040540c01e12995000da0b81c10008006204001d13100041c403281042e912240d024825003682d222540f00b869040703d00708141c1d0301d0100f1a182c0300c043c0841e544038a285a03003d049a04006001c441c0c500402190100c807490106000d19800b202c0402020703034481c400d44003800340211260104861400050070300c05d480c40c80541c8580010141c0b20404c0d140c000083d9180c0110034203440d2595103103002102c0c1305551040030801e01614a02c00554504100001d40200c0c01e404000d1504028030303c1c0b0810010840030010240500800316a068085030380020768a107a4080c01c0d091044a44020350300c0d030309861086403501641030780c0d02e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 813275746 1250 813274496 813274529
    0x911010c05070902160f110108010506040b0d020912070303020616140301050405131209090506040b09040f0614042a080d051b06010b1c050c030f06040e070e01080d09 73
    0x2d80085d0049003203540102403580703800c1c00086604156002840c802d0a84904044120000410840050f0046030280008000512000c0f2900090720044050300d40007607a185440c0000c02c001c011030156005651207010b0001c4200340d00440c4440c401c90150041c10308080801c00120355401c3d0796214006100b00400040c02a03082c5034004645c0101c0000c08c2e9200c48025a5650f41240f098044860008101450603c015683c2c1d01800c2c0e0001003c850034085030003001e001440c8010068002401d0201080b80c501c01c2003015040340d030031914000c240c4640392500b4100805005035800034900c642540c02103411124541c0002d42c01a00c103103100400d86a121540300f525607900600c01d00c5d170702075492041c0380486081000040e018109624409488614924101a0f031100c4602c09400442c289010840701d00d08180580b6070140b402d0504501940f500700212f00285a60380200b00c00b80180800810700103950782015040b620804200c8103e80c0c0d06031812200b81c4600d0080310703134042180b1039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 813276996 1250 813275746 813275759
    0x50303190903200a1a090106060c0b0a0528091203092001050c030301140a0512030f090621040b01080f031608120114100c0213090309180911010c0507 66
    0x51881c0746207031041203415021240d00e6082d000241000402d2001da0744101b08904007500b805034600074542c07414010344100003903541d408550700c0200f001070340d80e030754100282c500011220715a441440031101e5000402da550340040c00350124043c10b8800702e455000c1221114072130b101d81d10006803c580c6140c000040340c0001070441e52244042d504000c01403000c1a003c00301400118020070081030520306002c27018090105034a1640c1c8a503100c0c61210840081c0c1e9030020080350b00040381c014040d603031120160005151030041510f4000b081c05d07101c00d03942c807100c2200b40e401e02440c010344000c0d0042c0e07030300c900e81a90740d4103591594030300c1d800c00c0c0404281120a80c050318050b80c89500554107109a20b580d42d0f0300400700741c0c0b110112240b00c83d40041c9a050181c0c4d03080e40080385240101c89140302d070300801c9a030800741c10005d4400f80d41d01170086c141841280c2e40009004070740050701442f03030707100100409840306042c1600e604029200710001980280405800142d00034064000e0300d03c0d182 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 813278246 1250 813276996 813277037
    0x901030b1611010f090b0109021c0e10020301090b011403090304330203071704050d2301050a0f0614010813030c080f040602010510051f050412050303190903 69
    0x2800e10140a50240c4402821900f07016814a040d940130000400e10b9a60a0500b08000306a00200601e481005148001e026511401d034003001a600f0120f60858040c0ca640d15184081e00c4000c0451f101000101d40c03a06140c0003160201e82c02d0303844c4660b0341c601e9111710081d4482a100e041d2151301c20001000361480313121209144c0b1092600d40d8014140d031045540680d5107444c40315005800c00900e190070004460340713071041480e2696001d81454200320100d4481c4c681101701a00105d40700c00340315500b074502c89400d001409494000c0c419420705000c1440507207110143c0c55042070400c00003027249000b1205040311030700c0580d101076860302c0d0380081d4003250711030740e0080d0b042100c004080703c08950240024040103005901155646151a00003421504041c2400504040a9604000e16503548062040549811000814411176400152aa0300c6903900c60b01c408080b40920b201400340110181d44540791110400010200d281c103514103d850801c8005d003c03a441d0013401030703203e103801c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 813279496 1250 813278246 813278281
    0xf010f03020903011103041b080c09040203210904060e060a030b190e0c0a06080912030c04050a0b040801050921031315060603060807030302030d050a060312030c08060901030b 77
    0xa040040c500b04441d4042400e503540c3c1d050340d00d40a4800024441040105010303030090310396681a032510b090400100b55103940585244034400e0702d00601060a550b01401080441c100817400812140c007501c001e071400b07400c0200403030f1055290400010b8540000e035a03035071185800038070048446045554121403050f000e0030010084051000d02c0c0c2d01042c29110300c800c0048a0001030400008804c2000f0104845400200c1042440c006009005c4400586a0000244070f8040d6840c0d90381d2010303040a9003d00d03402141e201c003a1000014411410a005000f660340c81e4000740706659840f8103061356448000d100740550900b070244541c0030b10b980005181c0200c075441a2480c0c0403003030345a03480042805403c00c14801c1e0340710406c2084c0d507090f120703200c002c00c4520060122203145880c06901c9001d03030003080180e507845400254104001c0d070b0200d4055176028400141e940340c3c000d402001440c0b00010741c0e01140e00400483c002d483c00800c801c0c100c0341e00c070040c043c841e036410440241c842c104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 813280746 1250 813279496 813279527
    0x1050406121d0a0f06060b28121404052812020319180503010b030a201c0312050606160201200d030f1401171515030105090c0f01 57
    0xc01960b400182070000d084002c0c09800c60100c00803150404c1030481e80d03d580710b0002d102e0100007252901101c100320202940c1e0f8030001c600150800303001070350707400303042100108080d03e0f1210700740b205d001c0c2852a9020714040c9044492040032205160076601c010030303018020318101010f0800041d48520605d048400c588192400d002c80c810030611449000e81c0d1000c00301c1c1242c0c00141c0d000600f03284000041004030001c4c00000702408c0400d0701c03003121131405054140c10b80b10904a1411900140d91003000290004282d18405401e40c41c036402582d400b10001000240c1100d4411040e0041d40e0003070000902052501c8180c40310411040d501d600708905000c10304c081d00743c00712020090711110810304800381684c10300ba6000102250880225030807110700c2e010a95110300c402d525054103603410f440181c052401381103252440c1401446048481c00540343c10040709003840d000101e41e074202a0002e120645611a5442e107582e542e0b001030381c20041c2c46080750015071240a441017662075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 813281996 1250 813280746 813280781
    0x307021f050c01060f060e09010b04051306080f01140708040507062601030602040602010e0120031008010f0c03050606091f03090c030f12090e01090518031b07050105040612 76
    0xb032901d02c42e081d200568041d103a42600c0010401c00d05402035100402a4800c880c002410760420b2010043c0780643c0c087c0e90b01810030130780600f03a603129507807007600070b05028412a00480c0c141d420b0140600841c5a4200b040382040010603d4107006040c403030f0245510070302601e41c441c2400b0041300c59500100161205914951130a050308a0406055020750300422015035120309001d000b90940340310010404452b0715207540d610102d459280c0125201c505100c60665079102e6100c0240700003407980080e099035183c1074000403002d02c0c1740d10001c02500c080d141030100d569070788100034190003042074141c0c02c2440025031038240604a42d4055641d00d9504001840ca0480e80300e0010500c11500115040310b5801240001d000750403003c204e580e078580c40c0080480c2e042078800f0320300700410300c0380c0003034991240c1c04901e14150b10030748103056400d50000c4030b07120f901e0106149400707604490800928000c0d45030100b1594400c1089609407110350b1102d803800c802000c44400242544d0300409600d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 813283246 1250 813281996 813282007
    0x4021306051f03110a1b02060f030c030f07110606090a111204050601080a02150a0e130203060f0312161a0705030108010506060415321b0307021f05 65
    0x10b0b03541c0c0d0724003981d2001c00e041c580c00640b032900240440710f8a8000c48540507040c0180610300b58014800d843c611019406401490040e10100b0400e0044118410000e4030100400004c44060b90213940300b216149958002519910f40584402020301049a40d54001c0d030001052400c1812849070012502e40c0b001030001103140d10840c55410030b103280401180e1040600c030a22104201030b901500c0f244e0040c1010400c640d000030355440c000b44580e0034201e004101110703001c3c0030713800140343c508010f0900c80842000c2c1200360020341c002c0f60480d12802c140c00001d0b540d400e00043c1d40700e030340d400052101d28152810400101d941c1401d6011208800c04444001080b64151400c600419203074070358640300c1d4103041c03880f401c2d83c000030003d6002c2c0070280400c002c00b05042c01c822452582c6070400b40903201c200300307020003d042006c62400b00284115841c540c4034080b1030041000604060720440f8400c505403000741c40b40b203040c0d00603521110319911085059500010581c0c010140d090403450705 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 813284496 1250 813283246 813283249
    0x906060b0c190c0b0c0f240105090c03190e0a0c05010305090105060112020f07050d1815020604060f0b041104081b093403150608070f110304230109080a0503030402130605 75
    0x4540f20000c8004000c12448a01207c072a841c0b0b0180944802c82c0d940100707181200c03c00245001c01801690940c50351645010036941640c44030300303003010081c01c0e07403102c0640d0f0925110750314840c406e107800640303008001016950306215150040c50140c1d92010000c015402c0e035406500310000c025502c48040120100081e03042004044000d0a500c45181030102d186034584001d100d98098543c11005502e0f841c031441c0d0100b402a4426444400040c2150080e04410020003800c407107503030030610707080000842c2900203010f0802c0b5000704003100c21440b1a0410010407038030181100b0b410686400c00300b05030704940541c42550301c0703103442c03801da0744011000d8212031158842c0001c80800d1341c0da10080c50082c0744060103400782c8401e081c83d0740359060003800101260070b080300303ea0811203a40d0079010411014402c4500174048011500400c00c02e0310380c0c1d42c00300402449658041081902c0c000741000c2d02285a480d410b8000c3e02450840da12a001e1100b404110221a40c40e96581c01d00411503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 813285746 1250 813284496 813284503
    0xc03040506070b01090b0a03050a0210030612051c030b010203070f020d0206030f060a05010804050a0b0907090204030506190c0c08090a030c080331180906060b0c190c0b0c0f 76
    0xb80c00b032490803071954900f00035141200d14518016005034140b150620210b4800241102c041da410b454280d0490b40b00c400c100e00400064000c01c29160703001d5514000c1c000000360300d401582e0b03101c0b01035114a11042c0207034204c80584c240300380541c00620203c4046180b00704441d510794009400070308000081d0b40090001d0b40300302d80d503580c1d480c00c41082c04009d05013800300d0302c080e02c004e082203403140c2013545078256a85111320b0001d00c62600d03e400030f203400c42c0901105006000880055454540340e140207512508121803000114424410404000b03106008081c1c440080c0e4495410308002a00c800c00e542d070103550100c0d000220024000005110061000000c0ac100d001558070741124410700c0d1405804200d00c2e40c109880b865208006444032503461080303402c40b02005060141d280e2620014084d8144054030352403400e82c0000346014210300400c00c01c0c807404192140c0020000c40f241184000d1030b03014040c048051014400c0c0e0354050024003200f031810341200d0f406051550310614 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 813286996 1250 813285746 813285757
    0x510171204031b1e030f050f03031e060f061b0102220504050f09100b012006060109081c2a03021608030429040f030c03120516080c03040506 62
    0x12003000304483c90003d50740101c0003001404000e0700503280584a21400c445646582c00302400e00301c120140181007040c104071000300c6d0442c00c1c0c1600d0b12441c0590080150700300e03087c0219050065200081d07618507002d24202c0250400404031410301d5034103214440c2081140c45000500e43d800c204007807083c19408142030420428201c61007901d42484144829142d002c0d10610503212410f05004403400c02180c00d55280d82c18802c00619507a40000403941e884454100d0340b11041c58205107c1d070102c022426030312403142a2607101b0390a59071801c15984401034030420030303070025000441e85518454403c010346880d4800b000b0841d202c2403c48000c20040f00317081107016038031051040e0012840802048010850140031714200f40c030300304440740b0000495640180d0b0510030300074500e0580c040000e4501034131848e881c10105684a152061041150780030a540c80d008a140030600184500d04495595036000c080100c4e442d0310b50707580d00840c0c1002c2c454a1190000b4030010407182c450f03101409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 813288246 1250 813286996 813287003
    0x1203360106061202090a05090a02090406030507061e0c030e0f03061e1b04051504150201050901180228080312010315180807080702040219090801051017120403 70
    0x4600b031500e6405400c0c59528040490101c0c018050f100c15035581c02c170f0107022070340241c0d01194907903500b281e10f000922444001d16402031920001101b8031500107120320a64020f6112039450300074680351201e042c09000c03035903000106085013400c00644244191403075a17a0240c01c4205075080d9038000b90621300121131001c50306400e4807003540085105604e054018162520400f00490840104101031069000d0396000710302a20400c0d00b603d143c0f03012140140b407001d82c1c800030080f242c44000c0c0a801c09407106511507007461400180b0200040c00d08040943c01002c001403d500444800d084a003560860340110314802c4000072410020300082007241001c030000d046943c190310f0502c0c0c0e50440f80340f000b10b007140f4103000455051351924001e0300143e000350520307445200034602030700d5501c101880250054000b25500c6158201e403022420a44c546480c0c80340c0d075580704d9540d2402c80350200d4010600b802c01c0700003000200c1c600c4a4040382d044080c8280e80000401c001311108a922035803048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 813289496 1250 813288246 813288251
    0x3080f09060702040906051519060813080a020a05120f0301090b1801060c0b090d140c0c13020d05130302071e090c0504050a060e1e120109031d0312033601 68
    0x48a003d450902482c0142c8003201d1682031021020082402020680540414480c664001c1070333440d10441d1f4021086580001000d68a43d450355000b91074200d000c4040f14544100907080c00c00051507401e440d41030b940e21a444bc1140e2902c0c1002d0060b115130030215811880d02c2c0c0161011031035000ca298007a000a0f00c0304400803c140ca4240760009005000d40d0305a080714000001c802d03401041710520800e6504426182c284141d1483d090032045204141d02045c0344002e04107440d825000340c01f0425030200c08100a07510009008820035414000a0044c0c20205007807050f00350b144480494003003182000301d442c949416280701200d10183c40d035000b003900410100158071380400020003401442c035100c0ea0702c16181e40440e0b115194510921810030b86480c003900301c1d48407001c903000c42e240d00e90002c1c030910f40e05003030160088890b00d0740300071103601020905800d4140091559842070307829103418030703650301d1516007015404400590344210303540f85514090600340108000d051034904000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 813290746 1250 813289496 813289501
    0x80706051509010f0810020f0406030509070e010602010b01030e0c0f04020d02071a010504180c030f150c0801091a01140315031b010e100e0d0302030f070302160f03080f0906070204090605 82
    0x9031500301b44d66030203400c03280100500f1040f00d48002c2520126040c1c1d050214243c0c0b1040c49103402d0811740d03005003203180b005000000b54030b907054121030030074031007a00d04102a00686080359103031038081116503000407103030210300c850741880e0340101510030b109080141130014a0352880c0210243c0000c1d0001103c1c01c10040c8424034091003070130320f04d14686104550070f41c503903074425424200c07c1c800603013000d0400b031090080c801c0f10903003603540c02c02d184020480c061401e00060160340c4c0030300804820924002104646e62204040030740344071416106c44801000600c80d0341c015900c01014091062414814000c86407410010340600c400040e58070940303162884001004517015403c07840c81789a103080c00c0022203401c0004a00040005d80e100401c41626040c1070f4a14410302061400d9072030700165141c10315a012500d010801c01d0720017840b980075542d10540c11105140e01000d031845000b0449107807243c0740b45000349031400d00a480c80d820881c141e0001000c90340d82c0d200a4940d039031910308 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 813291996 1250 813290746 813290759
    0x2a150b040e0604020907050304150c03021209010903090b0a091214070e040b061509010c0c080f07062712050705220e070b0a0309060917070c080307080706051509010f 73
    0x299280c6c080090b18181c0c1c2076152646842c0000c48901c1000100306558420396041c1d14481c1e0100c41000701c81c031170074421600741035540c0c80c000d110315030003600080e0030200041034020b507070750854040c02c243d907036010041400c1c2010b10a02a02d410b50460710307440700d103144c1d41c80607006010b000300a009032807810308945014140514480b00c02060340381308043c4030410807443e100c40010303600d04a40c01c0c6800d11207481546040700c0c504c0003607080001140310380b44444a0f038180000d80c078015100d850352506a94840c0c00c01941201386401802200c0c10081d03a000c0c401c40c441c2030070343d211060042044443c05a95031010680c3c0c040850600d001680d40b641140c409d912140c0076003204c4404e054000c00b1107910b08441c0c0300352405003e10410400d80c550a41c64248403440d04010300f00c07500507002000203440181a0401688101c0f412107409240315000103450034040180e89165030040d00302da1400c0d42c1503640d50018031000b04860b0300007a014442c001c254881403c82406050f0040d000b4201e14103000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 813293246 1250 813291996 813292009
    0x17040501080106030e0d140c0f030406141806091f020102190507050606130e15040b010807060c060518030c10110f0d0c0e0d060b012a150b040e060402 66
    0x8005000713142c28507401d0840d030040002c0703038880c2000501d40f07007121300e101c8103c46c60a44580c10710400780e403040d215031520b40d45011000304100c404075110041054003400c41000c440c0201c800c0c0410031700c101080c5442500346030300144071641d402006492854032544d1843c0d4080802450f100060398086608010030300901c2081c000f55581e0f04040781010455030700d0942d20000140454061818000c49407214692508002c842a2518055451003400d044e00703074644810842c4c040e41e0324000700000040e80303000170034a030301a00d8840e50b412000d6800c0ba140c60001d824050b01004c1700040c0860f100c40f01150078805801d005080901502024042c050403805507040441e80c1240e0240c10043c034899071042c6400c4500d03000043c0004100c290700e08100f682d4441e00860166040400c0702d5507401080015400302200c2c070b5098880707510210300c443c0c401d289100c1c01880b404d40b51030b4501c09100481c41c44c2e400103030355404500c40814403401c0c00d40031070190f03008440051207a5001c00c4c140011458042c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 813294496 1250 813293246 813293249
    0x50105030c180a0e011107030518060307051236060a2f0705030a091e1203050310081603061407020c1002010b040203010b030105010e1e0f030a170405010801 69
    0xc880b0a04080c030024846400d800c0d010740203410044d9140c1c44124902c20a41192408603000006242c4803055070401a18aa02641240045941003484600246401c00c181c0c0e0251016548042c01d01e240d0702109610510f0140c20901301c0d40d00404803e42401e108600a40700c0c0c440c12820f0609005840221890194003070a1034410505150705030b06c6628600032250164042c4a40c001480440c084e0300000303e104066000d4624007000541c0c811482c0c2002d4104111001a074030002c001d40d10011016400b40b190098144034900b150701c42c0d0200f441540503541081d50303813100701c01c040da891048902d420003144107403846075076144007001880014030589030b0103026000e256456140010000b9101d00e160280140319182039040e480b402c81c0f0075401a07401ca240070780110740d02e5850703151304111030700244680e500007001440000701728100100380400424034028101c5e107200082e0100a00ca0058000f880d406100f283c102e040810071018800b00d82d040050743d0190360354101701c00140320742c405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 813295746 1250 813294496 813294499
    0x31211010e1c0c0c090507180f23030a12020f0105090309012321061c1202032203030306060903080723150a0f0603080405120f060a050105030c 63
    0x4041c000403a00102251601400400c0b00c1c205200429520050300d01810002c0060000b1074403503400725a815680c0d2107240580324685540b10308a040c2c100c3ea06158410380504294100995010001182840c4c450404070341c070400d040c0403040d100c801092030030881c00c2040c0ca0702981101c013200d50b00d0b01030020106442c0490024850f5280a0500a55900c282c60101d41080b1581c1040c0b61248201025004540540f000301030b941c1c81491440f414610f0705a03080120031074800045059840c000d40400030b09941e40c44400030f114036603140d1181c503980c402607800960100700700c4d4202e20381003032402808007000d8901118140382941001000c80d44203801c050f05001015800b4000700b10014265040381d13500503a140140701c0c040c100c20003c1c171120200c045082c400d181c20010480310382e03ca400e100313095010b8201b0281f032980c00a00c05550032440050049007080005001905040c0080c0003062202000c80d221030708003107090ba1034100216418401c1a54520041c060b5250a100701d40100343d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 813296996 1250 813295746 813295751
    0x216090209091303030b1509010f1b030f0e0d03170c04120b1b03070309030816120b0301060e0405030322030e09041502030a0b040f0212010501050304081303121101 72
    0x1c0308082092800c001c2c02040840445403006000c0620a4000d00540040034161960240c20403181800303c0e00840801d501140c16810500c4106218007580c00c1255000c8060f0800022251000d4490000094405c820040f00c600d00044603241d40502801c90340c402e0361940072049080711602003a40b0040c2400001100070007040003842e0b055010f00c5800c13604000c030300206807030380239554518851103507410040420202c1005141901a8841d0100c00e00a8a4601840d0307544100f5030f6001ca21076503240003044082c004c000b01c4c440103130700103200c442c8090000285076803144c18100007408111001c81c2d842d0310001c20480b0500d038210b1203480c1d03000c480207501d40520a030740e030280c880100c3d0603840b4052071017100000d0500582494038560b502e070800b0700310b5032800c10385004000f519084010700d00403070500240c00090901e07442247d07481c81d200e00514802cac0e404c0000444003944064801d4540c02c40a01c501141d10030450820001148a2161207003498134001000d4080b128424038000c403642f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 813298246 1250 813296996 813297007
    0x10f1a0a0903020913230f010902060a05310302030d090b04360f06060509030a03110a0c090b0a0b03060d060e100509060907050607050c0d0602070501050702160902 72
    0x1a0803a9880003501d50445a410302030b40c907070301701c4078440c003000401404011b5a01c0d0b0070302003c0c0824101c244040d0212050354809282501840e09071501000025084882008140080d903c1000900740c80d00105c0340312481103226400f500140744104070251900c400450b402c01c2146410080110000c4450401100d514505a5901424000e40c85981c0444420781411892448003001041c1d4a441d0f04a0031f03e80100d20500c002c00404594952200707481c58404d01041e00d170302450542d40540341c020018a11300490345c1c0c086407a00807441212015220340e2160130700141c01140004040c01e401400003480e182c2000030000030320300f141d0001d900100308100340051030300c814548a0005400146c00b083c81c50707030580d0f00b80c034040c004841d031451286010180301c0b08035000b1a4460107162500c1c00c0319001d540721001c1201c903105024000b01240d024074120011030414a81032600c007806164014140460303611800d080d25803c132010b10051704180c41c0044031101402400c005044081411030801d07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 813299496 1250 813298246 813298267
    0x2030a080c0d2c0406080a06050f0903071e0c0803280906120506060f040305030403060e0102210709051008090106170c04150302041806180201081504090b010f1a 71
    0xd403640040d008200f401d11064142c944803a04514004d000340000c4030015051400e20800512060710414583e04e41b0a0128280440000070f440f902600700c1d00300d50240384002c243d1042980b2744881140c8200640c4c02c0007419020901c003a0447c070004800000f11303045086519002610141035400620091f04000d1002a40c030400301054980e54540000d0b031504c480f400280706000748500c00035880780004021080107030200c0580304882c4215424003022140c0188a07090b030050305c0504070b1210410b03078904c4040c0c019113166900243c3c0b60805514154a46012480304c3d04440f42a10126012100740b2140540c24890600101541000c440105072400340c01c035194400034040d10f06c00d5444600515074071070080c01e0080210f5000313000b0013150007100c80c100c5101a1020060b203070b01d850b02c5096034a8211329200c0000242e8141c2d111030b82d55441101c8006001704400328150004d54810f43c1800107500355400e24040e0416101e0181a180340502d0518018420030baa140040130501106848 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 813300746 1250 813299496 813299537
    0xa110c01180308030915010f0305011103010b0f0f0d02130305061807140118030507080d1b02012f011506020703081206030a08120f061e0603060d02030a080c0d 70
    0x42d298809250360f600c0c2c446400c120300d0440d80b07194858240c030801c000000c00c03030181301c0c540040b2803080009000c854050102c50b1060f010034413850380911410014043e040213060020400e015092103043d003403641502e004000c0ba0001021080814011003091040c44020001c2541c412440b000c4040c450034200000b40d107801c074610035031017082c0c1c0c40652009a82e020b054403c0014040c250030b900050340d030b410030035074649052086081038050048030b0050940b28004180c815003c00b1981c0140c2400d56004441d50400c25000c0720100d000d04000043c840c02c00862a103203010142c002240e10301144e00c9010f4060482e512400035940141000c1001442034010f85141c141844090009540c2c3d40c00407d003030041c0c070f080c0185030480c00110141c08064001240d802055600c0324554150b560100703000c00703503114400c10350b500b20350080d10640500d0100025540000007410001702e0400540c003203480c060812100b2500808089400c2100200030003064155840d00d00d40180d0345403060010126 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 813301996 1250 813300746 813300749
    0xc0304150e0a020f010905030f1b0a03120e040f020d05010320180c04080706030c0f1b0b04021c051005130b0103030f0201060f060c02040e010506060d05040510020a110c0118 76
    0x1400340910304c40341a03014a845400404000d002c1c0c510b101d020408a40d150030644045003d10358600b030802d1024280b032500075054990100c01540381e20301202080e1007980010415540c419102c403c4d1501e0402940090314485260b010040341550441c50f000175500890000d514100b1800184010a65111503003c0e44581e0342c10340303401b1103454002c2e008440d0310413500900c01e28842c030b90001031095495407041200a20039501c1c0d01c800e11b69050101d4031190b1111400c0c2414540c020740401040b54039004940007072000b040d48050001e61110160b10301c0e0361140585540d023062120107502e005e0b41c01200e83c400d000c103c122080c0003203903455000104040c003002e000c12418400080655000f588801b001e420380740200707241d16a44800c001e0030031070041b0b4101d010b5400c03c40e04c0302105405008503401900b0052203d801d00f00700380b400e6001841c004005440900c1068480b00d400c134600d100429000e0001d41e142800160299210342c0703404900e040d041e04100301c1c3d21512802c039140c9400b040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 813303246 1250 813301996 813301999
    0xa020307080d0512040501060b0a02100b060f0301170f010f021c05010b0a080a0b0a140102210d0b0d14010b0120120f0904050f1008070b0a0e01020a0b0c0304150e0a02 73
    0x40082c5c44a007005401080c21703800070300d01001c00159003400d140d000501c913460b40d0300ea8003080c00b40b070302c011091007100d000c2d004c100f03841c0600500c01405412482410f00c034040000e8400c450402001c000c481d803d6460010404103240e500003111080d580503040c5256509000715004c0c0100c0d40f400140c86150701c0f60302102d004121880000c100f5a80c0150000764200c0e07030080080154680f6040001403d8101d02049405807050303803c0020b405880c3c2180c80760300c010900312603003402d590400e00406081d44120340c5511441000807140044c0c030b16018022110482000011011400000544014001d0041402c40c130800c0c0ca21100c241400915012048c500030544c503100c12510300d5150b41350254400d043d92082c00c1a04000d03000c03c2c0011403920584002c150300f03d26607943d50940761100c40c0e80c05452400d0340c080007404081c81c0a10420000b001061044400b4050340341c8450310300280035154140e0019001043c0814000000803113529903003492410044e00314004c000f43d5990f5603124000303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 813304496 1250 813303246 813303277
    0x11160b07091205031201050d0c17031209030a03111801030207020a051305070813050a02090601111203010302010e0a060806090907051002060604270602030901020f0c0a020307080d05 80
    0x39a8191191030000020030386048220341c2440503180c8141c403900015003069181001c040002080d00c2c00402454600350014032080c44c9500b0103011204205118045a40522007082621503080001c00414400e400203c060750f16145007940013800d40f00e034000c5a402440e428800907038890b031446104400c200c0c0c03d090041e528007061000c5241442d255112070780c4006a08134890070201c082c2c0106101e040540c0d80c1400700c0d96104403100c8070040c0018043c1031540420490001820460390158114405050203aa420440e014644c601801035086541e454800300042045580181008003042011220201c1850504c0001051914002c2010303201d01c070340d4000f08642c91002d000003405000b02408051262101d0b010203591108180c4505015519008007c40100288103121b414031a4038401c600b4440d0117070301d0303500283d040038000490a55080184881c0b03140392400a00c0b0b034403150006054040501d004260400740380d070388030b5807050b040300103003003901e40d440800c8584441d1540c080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 813305746 1250 813304496 813304501
    0x20a0b1509150a17100c110a080c0a0c060f0e090717062418120712050124030b07030b0901181104030b06120d0f05070501090209180111160b 62
    0x1c0c03540c03c4a0780030303191345480701420b03262a0304007003108090313405490428481141594000c5a00003044299445181c10032011a0b002401d10402460078803a42d2046508880071034440c000c5c0c05c0c120b90b0000c0085070110300f44c05c1a068001d124401220b40803542d8004c24980321202400301003040a100c0403001c41d0100081e0035030b0311141d0b0046001b000c0c151200d035540201c407040c40c0703942c000c00500c40c442100c14803500350340c42c3c20100d400588500002501240785040d4000c12414042101107955540b030f415a0710349404201300d911250300c0c50401c108030542c5181084c000984000d08803a0415080414440454a43d0800d00303044a5203102c0045401d00791500200c001c0020136801010424006800010b21030020701c410300540c01100c1c0b40d1000c80d039004000c1e0f980c8d4183c8429001183c00710329a40389081c0188042e204007401440041104036042d0300045100d00120340c203a182860500c2c0300c040e5003000b4481e1401c002007100c81286090142c50102041941c40c1d00e00415582c4c04400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 813306996 1250 813305746 813305749
    0x20c0907020f1213170a0b0c0f0304030206040b0a140402010e01050f030a05070f1b0f0609060203040b0a0506101403280b100e24040510020a0b150915 66
    0x2d10410b0034032282503400c01060881481c11030f038040602d4080e00b07414a0740106200382c507601c0c01e030b010300707105030050051034840d940c0d0301066040185084071400091106000011002d0000c40c400c078440d501508962409290540540c00c01500e1f00705064a40032220340340d001d6210305250020b4090030126a0f41d104200125000d12406890020318a404424000322020b181c1081c0d020307207856200c00b4800d0002050480e02c0c401e50311200500c07204000c11a0000c1181d420500000c5070103180702084103940e6844440907a0f0065808030388c001004000c1100350a054071039103801440440f00c0300e494004c01540103010060303600c13020b00c107814000003007040e4480c1d600c0020519241c1c040c0121980c440c10350070308010120780030b440f4041d003207003440d59004500c04ca01c94108003500400c11200d9200f84d0084507182c0140100104101c101000302040e160f039400840b01402e4826401040f624000c0d203071800c42e0780e1010701910405200f48074022810760390b200c601a84020986c4a10300c60440c4e02e030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 813308246 1250 813306996 813307003
    0x6010e03010e01020d06080f0f03040e070504050d05060708180a03140706090506040c140907050a0e0406140415030f1b030c060528300f060f1401020c090702 69
    0x200184615032002450217180011904281d08688514040d076403881100d8502070344404460454800c02e810421050003003461400002d03420400c1d610f02141829140c8010134104000700ca4141caa681c4120100140241e200c034106d0b41c4161841d245101c10014180f5070b5a44040b02c2400a041c0010480d1403050100b0010960741a580c02031020b2110b9012410b1403500e41c0400c0d0b6003036460203005100420421f10060303c0c42240c2d00c014011815030358412108a5054111454000800010384042c07462030b5124081c40003c0e042c2c030b0302840d8008251808200441c0e0204910740031841141d507080001c20a100381d49103c41c3c2c3c10403000000c401c01741411b44030846180c0c0000f01642403c00f00480d0356548903002e000c8058507001c80720042e10440c10303044201342d100544240011f80304018181000c1403880580700c039010103000b0346507031000001050103440461100181c07403550744004200c00c08002102c04020040b0500c161a8040002c000070b45860060b1103050107110b19001180c01c1d180f082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 813309352 1106 813308246 813308261
    0x151404120807021b21070f090e1b0d060e15090c09010302040c020705120c0114030f06040506130c091a0c0304091a100908061b0306010e0301 62
    0x181e81380352000041c2d00403907046040c96680c94003540d00e03180212403400700e04c0b0242214a0401c01c1e0420300072070a40c041c500706820814800f4080c4404a50340150360075070a43c0142580c4218085000b0701c4c20f4190007404c25151080300302082c440426148080200203600c45030780c1d221040134603a10303101c0d190a543d0010890300100010f24156200750800f40b0b0600603680c07103658400020710f07118000c0344004050b0b00b08020111656030710656168804814190160643c00c20304079040800c0b1004059501a035982c40208029a880e00072001c003441c0f2410061119542003400148258514424010081e06401c5000783d240340b800d080d101c007118000010b500b02490700c01c1c2d402c060322040c40c50344520342910034031000584a90103801c00d07004030394860719100341c5082d070342c00e1500b5070040c41e504140c505010518a10030703281040b81d4010300c0910700728450381c000c040041d0042581 = true := by decide +kernel

theorem cover : BRFrame.Cov 813129496 813309352 := by
  have h0 := BRFrame.cov_init 813129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 813129496 ≤ n) (h2 : n < 813309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
