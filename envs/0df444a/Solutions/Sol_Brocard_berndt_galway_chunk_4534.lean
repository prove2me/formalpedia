-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4534
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:55:34.706045+00:00
-- url     : https://prove2.me/submissions/2e6d0906-531d-4c8f-9baf-6c1cbf4e305d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 815287769 ≤ n < 815467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 815289019 1250 815287769 815287787
    0x50f15010c0321060807050f120d03110706090b0406050c0a0c0b19060909030e150304030e120f0c010210060506070615080d020304091a060304060923032206 69
    0x215083c0b10035150102d80c0003102d8050100c1100480341c1c181a004a07014602241d0141110020707030301e1211203280c8404103d042d8540c0c101c840c25961080e002180394610030303040309001402c05001d5514090706a11003e0507940e44200c1960070f58508000d000c10401c40b0301c2219405540c0c1c1d5515420300036a03640041c0255501080a0801c05d4108042100d2480b0640161240c104a14042110a90b2151450f000c3d00040006a000c650040750080d22170410200d00840800318401091079550b0f176a07800d89401070241011504403050a0198035014000c20241c1e219050400080c244040848002071810300412492010941400010410303078903200195071359513078402c80210705c6241e4080b100c00c15407495070209016120f039a160018841d004001030050b14041c0c581030001525042c480349000c900d03610703c0c0c3c2c0c01c003804100007070202e41707607600c030461184c03203921080b80344403174900700c90340c0803094861440190f000005ca4a040c90b4100c00480d440d941c458807045c40003443d044000d4580e038a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 815290269 1250 815289019 815289023
    0x31902070b280f06140102121e090603010305031c0e070e150a060f141c020a020a0803010b09030609060c09060c150403120e0f0d0c03020a0606030501050f15010c 71
    0x140c5010003008294142c0c400c0c107620b041038801c0195821a61000015100c0d0b88242e0075459803010404006502c0401c07071488071080c03000c0b11450b20746074084111140080581d121240d00c0180150341140d540c031030095000710b000e03800950300c1d0482d0001d0120445035044100c0005032034100c0300080b003074000c18800c0440350050404400da80d03450343d116103401060800580d00030550640410481e4000c2099888006a0355a2180c081180d070304406103442600c0810381d040c040851601d19624035034006181501c800e00c10f0b95512100fa41d6502003940080e040541c01920203d40192181010402241d00044403001047c4600700812814154840c400343d42c2d00841000442261030901000654032074030f40c00318015100d1901e07050007844110ba144201c4030f8a0304101c0d0b1700c0646100050320842c28100c201c007070124008034282c2503500f60320448085080d03024500d170313a01c00711303805100d40c400450040c1d001061310314144102c06a407000c014115442d00744144441209641d104000c22807282e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 815291519 1250 815290269 815290291
    0x3080d0c090530061e09010501261f1b0203123c04060e0c0f10090f1e08032b0f0e10051501140d02070c060203031902070b 54
    0x40f80900990030620301100402e45180b00707003414800c0c0c0740e43e8411086100c40f01c0c80540e10180c0c548007807030740c2a50000e119020f11034220002c2440341c109040701d500344040d01001258101184061400044224001034000d400e03603903071103100c90601040040c00419107074406989000a11030821040700300c098001100b070001c04600c3e50441c40d00950071400b5003184440e00f25121400300c00c00c8107901d0300300c500300d9106041038545000400009607841c12158010841c04c481c4490005000c1c03801c00a840c010b00700031641600060340d8009810010150101c00c907070040e03488214041280390646a401038040344d001300401405148180040300450140a41d10303c81200d0000410b00a844189000c0712001e1601804560201380040c1408150031203403c140095a5000d02d0f001d4200c10845005000c9101205113030703007280e003c00083c075821400050060a01c0d003580c03103541c43c0c109650072060140e4400010302031841c001e125410902c5280d00b00c154900606a55036010034040502460401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 815292769 1250 815291519 815291569
    0x33103140a17040303021b012f030615040f0b0712090e0c0702011e11150105031b0a0f080d020106051c120c060f0614040e0723040603080d0c0905 64
    0x240c425012603040c01f0790a01010960840101d03894020800c60446a03101185106107401d010241034070101035003061441d481c01c41e035840d41486644000301c1011040f070310003040042080110443c1d0749019110429406454040d02e00d402e8210074081840b0805001c0401d42c1003044143c50010a5032040918000ca0303100c1e1100d20040c0c1b007501c1d582c00b4040d0740480e42c80804607107550080d01504804041e104072b4000b104080d2071070507003010a004172a015001042c6000070301c600c404600c5400e04001d000744070002d1b0b5414a42030f0031002608503240d1500700c01c801c4000a9824054500580070490b040e0340441f00707400c14003803030101d25200104012408a40c034180203000788030443c1055041581400083d4600652030010509401540d1298407540c240d40e20740d041c40d2040365055203569000f030003034904105501000d00c80d40c00c244840441d006610758020340791800b07208001c52040307040c2600c80350700b20180303000d44008a0041040003032401c0c04201a82d1104c02c003208828200d10a840a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 815294019 1250 815292769 815292773
    0x11d01021303020126070f0320250b040803060307061404030f0503090405071214010e0a0203090712030806040605010512070513091802041116020105033103140a1704 73
    0x28a03e5403070350617145014030508102c20307103070894500d00c0c800303034181d50070004078032444860000d4041c00000500601820720034009602e03501d43c0c000c8000b0f1161225102c7c02011561100d03210f1500b00e408907114007022040c00803505042010340e000d4005424941c0750080b012024800c7e0b40200d100141c0b03170070780ca4003020040c0a030034400c4420984015100380190b00d4400e0014254175041140f000a00d481e01c0d20740c100030074045d043d41c1d041e41d284900f000c1540e01c40b281c06a0185d080078210034540c2c0070300700300010b41c40b00320844c0d00c803480d100c2d8403201e4140c60280108411545d850340030034180b200810529100801c540072003680107000e8207205454195a0034040d490419507003010750716605c2d10030082c8180700c00c50345c1520001d1084805208110b0300c070b405403c85009424002c0b09059400c503e00e00117600801c007460740314208002d040041e010f40340600f021400000841c03503618400100003001d150740300900d401d2043d09105214a007041018000702401031010300c4292080e00300f008142 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 815295269 1250 815294019 815294057
    0x3050f0702040e01090341090117010303090509070e0f0d06060506040e180307170d020d050a090c080102030709050d080702040603120e030a0809010e04090b0108011d010213030201 79
    0x602411240020045019031b4540a0804d50251a10250210301c50b956494440035992802501a00150f090007120b1400003080c00c080d04401031190500000448481e500792540f600d56009501a96a604040d490441401681d01c00a01b04a0070003500142c0642c81d503e500003a5441d050f0296081a42042075050200c02000c1c2c0782c10880d4402c41c0002e000034496580d00450f40500722201d940200c645140c840e030f903500d00c6940c100601c0744503183d880300c04044554019140ea02c2da1218090729111007141194210346080316855800d5540d000c1072018446840c0504019120500003103180d03042c0a603000d04000c00c54882c00c2c1c4550000e00304e007010840c0420990b0741042e4050001c0c0310707640c1c4a2905590385903034861000e000522440e0044031524001039440348954021442510b0891440d00456000d0f040d9000a82c000d40c9610045000807004501c4500070b01d0094000908c1c0062200c04d210280c142840c030f810582e0040c0070f1441315528501d41d440480303509080c40300012607900c00f204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 815296519 1250 815295269 815295281
    0x40605060301060302180306060901260d0906080f0c1903090515090d0207030309140105160507080c011d01390308010602010e0d030b060f0c010204030209011203050f070204 76
    0x3600a403000c8000036003103402d038025000320030500c808005d45001181c1456900c02040b0380c0c40fa4004038100c0100b0440700402c40580780c42c241c500b11440c3c140204a503003440e001150f0314401c005400c00b982040000c0c2c0c455040368005c01242440003890511f481c41d02c280d8001d0b04400b0004054011610180c07501962264030325540c80402c0d03a80003128024508192442190103400500441150354165071021a00c6010341790305450384c0c01c406040a46241c07510101c040001d051200400141084c501164084c128592080c401002c245003050a6281000c03d07042145042c130094040308510401d00c01241141a0070230301c6d04242d988406401040351251044540c1602d4a02e43c1c0c4038070540044c01586108640031f0744514050381d03a20b0800324201c0d0a5055482c2d419042480340f0001c55220350003201e41040020000c80c01c195040b4002807903039004501464480e07500080400460400103400d0307004003e142010649800c454502400354403403141030034200c1c83d00050343d1003196556400700c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 815297769 1250 815296519 815296529
    0x9010807020f0d14091c02040e15221506150e210102070807060b0924151309060503011a01050a14190305090609030a0c14031e0703180302010c020607020406 69
    0x41401d070b00151070b05e50600c251b085c280d0280b81072810890100c0c1c0001004408401c46114903d196520f800d86e100f0100301b034920341d40440c1c51416006010a22695030302c4c103242e00c0290009442490027440c00842ca81d00d1310041c0c1484085044a400e681c0c82010081d04400403202105075010b044001c2802840b880b100100141e40204040c41030094aa00580c00d100042c0c41000094032060001c071307141c42a28003072411400d110700c0711102c01c0c2001c44840c4206507003003e100703003807020303c10b401070410070749810401401d603403407000300f20074582401a000307902c4034541882000000180020414852081e04a0504c95420b050050700d0490301c0c2250641510f01500e2071011001d680010b02170300702a0f400320001d01c10b020110300300127000300c1128180040c4c2d88851904050319030b529061500d0701e09801c2c209000901034140b070303c070741c0d05280401c4002c4030031801c1c0e9840140c5800f13004030b25050058002600c45020a10050343c000400f000525011a01382da12060b0910010300600b00350703040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 815299019 1250 815297769 815297779
    0x3022104140f06010b03060d031112090a0f03050303010e091c0e0306150a12020d0606170706090e15040906060b04050a090e070e090f010e0309010807020f0d1409 71
    0x4010501c080445000c01e5000004103442030301103812039140e6600428001d0b2a440b001c00c00c08140c00340303841c49803201414840e0400c1000d036406000c0c0e041c10f000389083c061501000c00070360888507182518058029009003849102c0300c40c10354480da99240014000c003030944a624000c11026a4100a2446441c683c2c3c5040002d044c28120000c08203802120b19a0092080802007007003901c0b040da840400f0740c03028090404440c0b404018104274030200d241a40c00c00c000c0301e12003010450500070710005e4540341803040f40c10034074210f038207240448070344c002420011190402d000d21701407000b0742900031508581011012500c5000100106910000205a41d00e05500044d03110404000380c01120f100f1204c602105665503410401d907040307607070350541d190070480c2c05001035800d18801381e41000701c1204403600c4018001c440703409c4840c1e110700442c442d400461139035199a44560101c1c0e0103101d83c4090300680004000c0d035569090a01d08080a000b601c241400820f02c0300000c1d505d940b0340041c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 815300269 1250 815299019 815299021
    0x6040201030b030718090b160f0311250308010512060103061e24051e06030a060b0d020702040f02040602060f04150f1a15030417120c0307121506030221 67
    0x103030020f102400341187d51802a00c00211f4100c4031010b1070b251b03840b80d5203038204c2940b07210703e00b28001c0004a40c0c05010303920600160198000080031920424403507800155000d141c2c1c100508510416440140300389001e540701408600003080d00b50440b40e10500108204003251000a1660507040c07803c1c40c0340f0700e4201142640c000c10900c00e036104220805440b03405d45c1740d0041c080d901d00e0307406c4402d09610091179030030094288040115403205c0c1d415030002d403a98640c92201e5455004d8000711448079000b00c1c0703c9055180038072624919013024a000c61602c1d2070000c001e5101c0700010310190041030090000707420310090240c18042c41124a004000d088045d1000d14018896000710081050402c140319030682849007400c101d402c1c1e0290303858150703a0b0740d0b521060030020441011610a205211030000d40a81030000c40c0142c180458041c2c170ac1c604014010000c142041d0440c02d9030307040400ba11502806107117480c1c191181464050703a60340241080c070480c28001d08000540c10f00c400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 815301519 1250 815300269 815300309
    0xf09201b070504051608010501141e250c05091312030e100e070503030c1e0307050a03120e07030803061302041505040303020607080906010603020d0b0d03230c06040201030b0307 78
    0x540c0c1c544030100c0c0346c40300c004590302d5400440e103100f90009002c0c096801048624000300c1e80d980d23050448030780e1400c0c152038100c0c11202c010080e1030107110741d02007852005048003005404003110000d40016900e05000d40b410301c6050010f0261706801501d003400551102442a1181d0000c03203591024004a401c0408541e5403a801003100c0402c0100c2402600030100d110b14020003225020124039004182d01011007550000c11001c2c00144c01c03840c4000c2019500240080c0411201980640c546180e9001004d48100a89640c003070f00015940007428207000240d801003d5035040308040d03a00040c90b0309070f050710400034841c0e40c1001003d40450660020220785c04001401075900c00d901303641c10ba448408043d42c1d042020749441000390098001440118840c1c0d02404903a0b41078480400d4406c0ca40c0089102c82c450003a0070340c0040c00480d0000c0007644509280e50017102444d070050700d0001c00251640c2c4504010f0304c000e04040c0c441c08400c004d550100f10001c042d004141c048040c640c594 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 815302769 1250 815301519 815301541
    0x1101050d0207061b0e0607200a03062301050d0309230415080c09090a02012607020f070f0506180f130203040b06090415090602130f09201b07050405 65
    0xe084c0303400000e000d041c8284c0c40c2e41456019141015071115004054008101d0050035154641c0f1784550094132019001020600724000c0e48002d944408407280300601420f1042403002c3c058000c280112000c00c1c20320300107175001c2000d0080720340c02022100e01882c90b03080d90000c21200c600c030036072081c2000d01080e00c01e0000034582080751000d8003120304900c0f6502c03d01c085104211100c0056030420550b00300035500602d041d100b02e5058a072140b409140540d243d600c000403d8401000503400000e05800c83c0034200000c50182000c4040e06010a03d45400241e9500c940410348148081c0c2c1015004103465000c0034007100038000341a012800c011484020003500125400c0e500c4107011008200e450801c4902c1d60301440c1c2204491030b45c017203c0f040b6030010b01680709007110301f15800c002114610416411280107082010354268056184c40030b40d42c2a031319400f80d80c07849040030a100c0d0340781710084400c9821103500c0101c80d803003900c0300c0c08000b400c1901503482660054140000c002006c83e003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 815304019 1250 815302769 815302811
    0x7050c1e0d0e03030d090201021006061e111e010b0d15110403120507020d140c1201050f19020903030f030a050a1b0e0d0c09020c1002071101050d020706 67
    0x4440c003201d00c2103449081c11140304100302070a5815400800885441c5085034000a070b4041c018011614034421441c1284200c4045510900c0061031b0240b00149100301220002c0d440c001e1490322100405111074a00c0e05c0ba581078065103001b40380d81545100484007034010350702d4044001c022840d0010740d8200860a29410120701c84540c0c50031400740c0f80041c01005481c00e40b500095500c40e24480b03450282c4155002040a03613111031038048900010b2520402080f0341d01d40c503c00303402d800f600002403294003038024140810590404042040041600e0240b83c1d0161660001440403030a0000740310013031054980107078050000190b0303c00d540c1211001540102101d0100300915901c1502d40f000710340301c42c0b08030000c102d50b14024a82c164481d10044500c0368000707042085030300a9030359418803000c0b1644815442034000c115000945801d220007005428107100a42c50100b442d0355035a504240303104058184078011990300c80a045c10340c103842020b0303400032003048000e1120303c4104038140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 815305269 1250 815304019 815304073
    0x1f050a0f050a240f0c05120c010c0201060326070b010e0412020c092a1c0c0903110904080d1a0a0501021f05070c0503030a06090c0801080a03030507050c 67
    0x82c18410005480c5411294403500325401050414400221441221030280c41c407421000c0002c010b43d850042403003804850340791104000300c1ca0341e44510000040c00d4134454104001964500300d0b0030004985821900c80a124449280d140e586410400301c542d1b90140c044090300405142001140c610810b0b84490300581c054444408100071132031040303964052103e806a0081c22080204000880141e950320641c02046481d2a010302d518038400712a421070468003280c00d41920319a04400314070700c6841004802c5242c6501000c1c15901c84e1015008103156890007590040e0000d0144120642558a0400c0c440710501c100a001010260003114200340280701e83c502c01e00000340c560002444030444813059000c0120401461030300002000010b00300b00511040040440002c0c1c0300340003d40c03140c00c0b101d43c00104242450100812604901e5010b028001454014040d4207c00210301014650610700032036281e03100141100d1a000710740844005100d554072030ac0c10a009114503a038206 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 815306519 1250 815305269 815305279
    0x4080c101b032d0e01080c091207050f060c03041404060f031211062211030322270914030307050a031107081b070f12060e010902010203031f050a0f05 66
    0x15035071a0f182c1c800740d0046180500803544010301c0c40715035401190a00d512400703ea5140381044504004500c094046203c0388001e80c002140030b02c8240340404d501c0308400b00c244c2c2c1e007604001000440d0790b40c80c41503000383d0310052a11103902d0103d40d03032178106034081e1200c050040041996464400e01c010040d607500c0c80491090001d00290721000282184a60f0303070350b50f8280b0205c560b1015202410201c0c0c1d42925841500e0300d41c8246a101013006100151240e01c0a404040f40001048140961900401c4149400118102070054010300c07003044000c0b4042c0000700c030b101919203103100c800e404171007078803a005c00300810424039004809010003403c0c60300e081c0b0000924200408251084182c01051003100f0f00c040704484202c0d000c064050003003c0110340c00661524030070384106005d58481c1c001044407010f100100305150140850410300b0320300038010b0b0481a80081d4580c00010700c07503079080c95200f071181c071a00600c01d10350000341006403101d80305544031a64251021000e004541c091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 815307769 1250 815306519 815306567
    0x31707021509010f020d21020408191a06091b0d24080613030302130b0706150605070c0b0904140a0203010515030f011503020409020c0c0103050a0204080c101b03 71
    0x58001b0030b1255440c682c0d56601d04260010f1141d401c2d40310140341660000350b6080c00045a180d8040054602203150011140d062103400d140c074a5618a20301c1112011140201c10b2041175101d196a0030382003402016850011241204500c13018016081500003503401c107200b03441041c0032005103040e12004100401c40e0203484005842da80c0d02d060f650601948103c811603c04607100c0d502030003610318466400035002e80e840e01c1d803022642000c8005d6503142e0b580c41034240540c040d404080c0042026003841c90a01038107454010018400d03102c0e44034084400140511242d4490f480408a00c0d22007100301d403035042c45d40b9001c000390000d002d118021802100340401281c4014207507480b0701106121480d00e60300b40182d40e2000c0070b404080c1010b041e001d01c80820190741c1c40c0042d280f0300301031400a003960486080010140c0310007901260085104100a0001e441d0205501000e04030940d82c0c020620011a02100e0410a8400340491200704429450405511108501c0241ea00302180460 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 815309019 1250 815307769 815307797
    0x504020a05190b030a02091806010f0306140d061b080405120c060403030c020115090c0f030209130915020c06040c0605030c1204030c12020f0f0c0a03170702150901 72
    0x72282c0d20061100c1e886126903070401040010000566002c003140001600788250a030204080400440e0300310b0700307070400c0300400c20103503404002c8822403000da1509121700c0c3d24090032031040803080e129040c011040c0c6440c000502003180c0000e00070b500002c4204039000381030761008200c1181510300326450b0003508460040b5000724015583e80c40c5c1c001010780519180e5560540040c0184041e010655480b07040741d2100e0000420040b0041c69401d038003042c03821450900418078003004244009051040c062034202d622800522183d100002d41c1c005030b81011400c020024568116407880c1d8a400061501000c1c0000718000740190305c00c80b8840103640d01ea0609507114003080756a003098110600640540d0341c04044091341050281c1030604108104d612034240000b4940f8001380540d00a981884000104016518145e00c0c1c001c05080d03200388100002e0303000512488080d0000d114440c41c9105091001c08981074154000c2078142c1c00c9458840c2c2000c550007481e051404500c0380086889 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 815310269 1250 815309019 815309029
    0x51203030c04061b020301050a0902011b08091509061801081e1b0c0d052502030307030e0303040b0d05010e180c04052e080d0c170a0e130504020a05 65
    0x1018035040c401e858201030816404a440a90740ca0221826030f012801050140c1c40078031506010391180c2801007041c2c441400007418901501c001500303c6c51301c0314002008245428203989080c101160100076040044241607142d004950b55075610850004020404030429174201c0a003510070707211300030556240c51000088031003003a4401c08070b0096000143c0d0220310200707010700c10700c45408214101b101076a00581750503014680c03840032480000740440000240c901c5800c40715030501c043d050b100c900390301180d101c0c082d4680080078440c91107180c4001d0303a014030036107014020b14070130a030720388440d0380ea4080500000c1c41a58a8400d00c000458180d041000d410800440d940d0003e00c0c9140c0c1d400107110060a0040047c02c203d00340302180203e03000285a8604940700c0281d94160352424940241e007800d01c07113404a02801840b18003000041c8031612101100c040081416807501d0031520309954800d00c40300341560090139103e0303a5084c0c009507400140610f009444d5100c61079202d000380a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 815311519 1250 815310269 815310271
    0x513020a0f290f16060e010612081b0d030c120c0c0b040804120803060405090307030903110112020c1506060c190f020301060b0a11010605090112050f0304060905120303 74
    0x112070580381c95a09140e501d0000542c500b81c8040c10b94546541c00746140070507000841040c1e0a40c0203d030b84002408918041d22003001030300c0008002d070900d400e940b061a0390400f200203046d80004a5100702c550b42180c0310006004134642074070b100000f40c000050003450b191400e080858501d020500c2d110859100b840300000035070b20351842c00711060b00c0e10300c0000001401160481020003000c1213003181407041d2241d060bca10241031700ca00740801003006440004152080a60003801a103002c00d91000f09501142d80001444070280c0100c001241d000b000003004500290001603403a1050500054070108c1c0325141600c4240c43d101c0c202005000d22841c01414007641c070001000c00401042078040003094466541c0762038541469001c2401d68107164003544984c0800300ba86210560020740000c10110350344001c000e540d0911000585640d418001c59000b108411415010010200801032000310800c040700c2c4c5541d500c1e040205600654080c90707019000440c107940c4040800000c1d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 815312769 1250 815311519 815311529
    0x1f050402061215030d0c05060f0c0403020625030e10080613020a0c14070e0a050c070609080d0608061e040803010b1612120608060402031f0f0513020a0f 67
    0xc546402c10103007003101c1c61032010b858503000740800c903403c4159039401c000d840074503c0c4a4481c1c0305540a58140281030010091040c0490206182040078140d86c1100700c07800e490707040721400d1310380320a00154a5040003840417801244059000c038414507800ca500061380382c60880e00511440765000d0106d072000c0040d500c881e0800c2441c080301c551005960003619040503585000c1e42040900c2c1c603916911410031951141c160005070301400400000864035502c075084e850b0520040c14140f0700c0358058454110007409050741c1d07000e200304011012080b40c0e1090b00c203074800d2100c0780d1a55500d980307078003041d43c0c2903014006802060003000e41d9005150b04c03568225442c6400c50780b81c290011425849500701c400202c0c0700400c060005403482c004a04040d00300e5544242402c50f08004004983c0c9541180405500c043e0402c801683c0c00255202003061140e0354642c84080c0c0f100280140200074400001141441c040040e42c40c00ca8614144a07402203d00207680707503a9042c40c2d00c44108600034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 815314019 1250 815312769 815312779
    0x7050d21020a1707020109020604030b250509042c0c01020d030b0a0504092405070e0f0904020f011b0302011a09071e05040e0711010609060609061b0c081f050402 71
    0x40040c3c0b11068500164404c6680c0008200c00c1c086a00080107a03215400444015140d801803181800066020230f00180880312205038000c0c0f00c01d0302501030b0148440140c49a42c40e0203006151034089001e114803900d00040380007010a00c0d64180b40c94400c4654114014401e140704007d01c9486801098525540070342124000390402040c000a003c8810302a603011001401c41c40d500005800c94588a6a01030b900058505180c03100929801c0d03004d010f02d22642c50364100c0301055458458250700154100c600100d6005403000503105c5025015180a041190003e00f070103054041d00038120380c0f200014900022550a000c0004940b010fa903164000380e07c104080c0814040300303904140004003420030740d0409956407040596020f0454040f0300081c1c84d141400c10711403090080f00080c6c98080c00510825042c8000146012400e201710002c004c02c1d404085100d44000c400074034030070781211040c51050707102d180c401c1d030f12406000d03414001c00d01c1d549264094800d51040782c0c091a40103107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 815315269 1250 815314019 815314037
    0x170f0d0c020420031f0503060412030b0d05120408010f150e04170301030f11030d05090402090609041406011101110912030c010c0f17010509180307050d21020a 70
    0x81c40020850f103000305140950314030b444001501603101940c03044051640100e42c1c0b000d80700100c118480c0c95404640250300800600c80002c5801011120342e03591881e00288c80284500020080401040c01801501030140c490310306110100050003a90300745002808a1040c280c2c14404441c04e00000115101e1280400d01c14081103401d096007013802107582e00561154000404034581c000c0c1e2003100c5d09012510b2000400c0b542d0b0404601004e011030107070141c030040c0c100c0030f0020700c140011548070780c0c0d0003d003403041507036071a0654012103405401003000d000d0184018003894801d4a14901147c400350519903003035414040d445680720822070305400d001825051014884405207009141d000901500c410710340e091084c00354140c11980d400c1988000c040c0094414981c803041107500401420052190343c6405407056000300c10489003020a92207005500d046004c1c2a01c020720038064a00a104a154030102e06100141314802c100c109101c0780a0250481c402c0c4200d060100f4800e031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 815316519 1250 815315269 815315273
    0x30605091902150c071703090a0806090a020f0109080303090c01020c0a03050a0209040204020d09030e011805010e06030a1b020706030c030b0f0103050603010e011112060f03060c180a170f0d0c 84
    0x180c180c4c044558102c2d02c000b502d44100844a15040194007290b900100d82c00c891460118030f003d000f84003c0d4060b203075900b015080a03855200d5260041c0c01610807050755809a441034008600414284003505e1301c9082021241d5111041e03081114018030621070f1442280ca411a5804102c81d4010300030075100d25141d081c04801d6a000300b00f46c2e400343d801d0200c20200f1a0600400054610030396402d460040000009407000b8403000004214042d104d8040c080d50f41c2140c80c00c1914403080b0340141c0c072a41c6800e049005402e1150b1071440100d030700d02d0082403503500040c95200703031080741e1030611034444502e0b003c03421201071420455204a2920585003994003980c0150f030024070240000ca0010410410207003034070309803070815044400000e0f0002c03e5101450344103402980c210354034189190020002070b40c1d034102503c84000001c0000e8001c8a04010003400c0c0001e00c0040c004890b407955901c1c00703101d01c001240400c6014014070749000d584034070107d1000d0380d1450584036480380300119 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 815317769 1250 815316519 815316559
    0x506120d0215150d0f0b010b090d02060705012738090a2004150b040e0a022502040c030b03071e090204240c0b0f07020a0c030605091902 60
    0x10300902d22040d1107140b1580240c42d90924403a007130340201c3d04000c403010303e40307000d112009050340002100c1e074060184410b265156000d840006404403851521250301d03062070350040a40408842d440712140055002c050711160b5071600c0c030780c0144150481c2443d4601d84401c0840d6418603503000c91540580036890700802d02100350024100e000f200c0190020390780d027030044100c07040d080e010001c0c803462342d001c01d00d0b181c094038a011554010000280b441c00e4003203101c901980c043c40303250314128400640340c180e03540e040c2ca81d07240d4111150560012803441d5907070b02d882d01e441c0a82c000c9060000211a43e03029000c4c0768441d00015000704040c41c60710380043d000e070702800941400f003044c856000807041e280b4009800946a0f04204100a000801d4071312880001515044d090bc45440d0744900414240c40c40d0551003012000030b040300d40d035a600c0480c00d00303d4000d001800400402008400c0c48003c0c1e100d6845404c0d40c104651f6488104940f0540b06079000c64000e503c10007000ca205101481 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 815319019 1250 815317769 815317771
    0x40305030a09030c050d031b02010908090103090f0602030c070b09010e0606100c051b0f0a0b0a08060414070c020102240a0f15030303020c0114130f03020f030703030506120d0215 78
    0xa03d00031001003103d6850070705051b04a030300d07440025110211b560004880c2600f5943c451041d000820280e18144c0c0c0b40d82080c007405010506150341da000520070b00058a6500c98070561281c0115528179001160000036000600e050b82d56902c0b60f000140440030500c1751043d8882154024400ca40e02d0ba400c000d440c105419602041020048080001030001c03c005001c41072080580b10801c0034a40a00801d00342d100503030362080b1600b6074100441c510600851340d142d40540703850182d5540f601e01040161041d40c6954000840b14400c103e0104e03800300c00400d01910036801e84001808400c449040d0b681e41c903012408007100c88010030a809140d034807251a0310301600000c80e000003848d0b070300840089075900640120f5000500c017024144207220703860104480c0e205440c0306013000b00c0340c0c420000151000402e0003c50b82000d0003414001c20030300702c80c0c24024040360358418103450020060882500c00c41d000d0140e404040d94400d00104207041c0310301443e80100100c10f40300788050f0010f00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 815320269 1250 815319019 815319023
    0x30118060806160e2d040903050a0c02030a0f050c010908060601090b0c1903170906012102040b04020f2206052709070f020c090702030a051c15030218040305030a09 72
    0x1302c400f1840e1548414242100c516108140383c3c001d80d0811000103002c030710040780f5034071803442c084000700007940107810f49146111303503e024625101036101103440d065054001074042c2901001010400c40001030385904da0340301f82e80700f20140d036803000241e0759460199141c0f07010604240040c1701a0107418040c00821100310101e40302844050189504601055015070005800f1003041841035041c0f40c0e43d0b0340041c406402004550300d4410440c21811101d4641102010108030f614203569a642100c909220010400c552754007841d00001165404000990080ea45242816a100c0b00215180303085640c2034444e1481c0c0100d5036907140d5501d20000380d030f0305091020700452481da151115801e01c50141d945030085280301c1404040d181003080740950344034105080800607100e5011003990946455800d140c0d03210030140c000190701400c2c2d91144440189401d0f04407502000c10180141104e0090328469000c50700554003015440003114094082750382080800c0c403204441e48143c0d403c1d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 815321519 1250 815320269 815320277
    0x70b19050d0c020f15040506070c062d27020d02060403061802130c1e0e0904060c03140106080402221e06060908060a0506010201180803011806080616 66
    0x36594114100700d4a900c00306030b00580c8a601d07141c10301d000401001c151125a004032104503c2e00d030340c91a550f101c00600d00d10800900f03050070810040250404607a040c0380442034618800a000a1403400c4400c91140481e103040c641c0c40004d020000d400050144640d01481d503000e2031503001e01960504250080ba0801000c02001000c0345d114401c007142c818844420101140c1c007801009500307509445144602403030481183c0f129600242d00c0700d614000b80b065941e01d5040f2900a603501c60034882c8003504080d4181c00c110800945621082d000c8a06860401c0403c0d90040500b206042c00d015100c0450040c4003c80d0152a180103040000006440303108074000b085001c840548001012090039503414950708120301d00580160710103440c0714900311441c603140811865070303040c2c0a0200980c0a5036035000c1010b99200f074001d180541010295881c0075400d40c60140c182c0c0d4424441c811880101314403c141407950303809038804443c2044001c10302c0c1c2d11910fa1003507080448001000901c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 815322769 1250 815321519 815321527
    0x602151503060c040612020c03220815241021020a170f0c0d0b030c03190528031d1e0a0e060307030b1503100506030f070b1905 56
    0x26507030821240b480b40d08100140b9443d03c2c41d1000113800d00c450528a00100390060014002e40c60002044d01d089080c06000d85000860361200c10b000e0811a4100e100349001381111104070707039101c1c00c070030f80902c1000c40403041e01c10000402c01101250700c603203107501004907a40030b03070800c1c070404400c5144066034400752113141c60342d43e00c00b0403607000352402400714800800102c0108480c403011948032007580c042001518002c1c0a000b050300c50b242a030900990784414600d660b48041115014080300902243d6030f40c004024822a45810601c045980d440f0b0400c242001401b50054000a541d02d0995400601c000e50342c1903690701900000c100024843d52082c24142d640c054107620104a21040e070a44400c030901440306640c03468109170191002d071820300031749840001d10704041302e40002c1e02000f03584411a4607030031004400d81075a8940320316440700701c55400d5580001e0050000710200c2c3c0b900344480b40180e84529081c418800300c01c03c02c0c000800d00c00000c203003012081d05546006407030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 815324019 1250 815322769 815322811
    0x330a020c06210f16030501290904020705010e06070306060206040f05010209100509040c0206040b041e150b041406010207361b050705061b0c0a0b040201090f060215 72
    0x403054212000702a0100d900103224200d82d4104e403c0c15514070701d10301844190f04020310620201460180104282e80201c0540c0d080e0003d00309440b200e000042055690b02090b0500c103001c2c0c90803002510746402044049030086010384581001c0300c1854026280c82d42d115200c0b104503030b5400e40705a403d55020010781d14240e60b1002c800542c3c000d262212900ca00c010340a000440d01e00d0650705041d503001c802400f02054500032043d0740b00c5c0e4041090340c0310030920307503080c0c26000d41e21100074980100805d00e483c509440da00264103c6400f60703000c010100000009a009120950b4042e0240e00040c4080c0b00d441100924406a540c01004100384944034000028091141d501e002020659604401c0e50707001c21468584001300c0700303103046410004161105074032028003030824000809034406000c0701c8090710060b110a40d401d942519000000f82c28240c003135000850b412800a5144180407034401c05001600c070654640d41e00411036011035203a22040880058085004088110701d1042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 815325269 1250 815324019 815324077
    0xb060f1c0c030c090c0c0f170409020c010b09070e01030c1407030903060f0c1709071a03041115040501210501060908010b0402041505130302330a020c06 67
    0x1103000d1049110190061441c1040b00700d00d40190850041142000c0080c510740354400c04520100340c0002812070074004520b8080300384c10003692005440100443c0000e030010983c0d02078203200310008000d0091440c9501001035128007100e51300080f81362500c12500f1b55200354841c0c8480340180c1031a1307006c060180b410080c45d0300141000c5001501700340046c020814240206034650394128418031402444131405440008a141509041883e52000500195007040541d000f0204041001c05008100050b10301d0b03580112010b8a50019001010b88035040024070008002044603649082505200044a01d680001b1001103403820500b40510b407188680f0070103000700840d4540312030705454032441307500303440c8003829241c400c901c107010800c00e40121040a4504030400c3c07800e07950380c03141c400b05104407201d10340000e50442c04061250241c44007a00d41002000000d041c11812100c881314200c8451107003a6070200140c20542c000b00c02d038141039000d090b0400c0c800804810408001039044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 815326519 1250 815325269 815325319
    0x818070f260c0f24071a1003080f2b02130b0301060909050a0f0903021614060f030403142803020310150306230a120b060f 54
    0x20300362024081e03442401020400c003110045a00280588078810000076042800c0da1180c54019448070301c031600c440e8280101c3d08805004808a5a00c40e4101d0620750494040c0a40504400440c240030440020000e151103003140e5000030000c0c0b92a002d0180c84440b41c000c0f82a05090514030100501c07003440a424044100609110040e12a02da048a0b13040c500c41d20752008040c51002c00050040302e901000300001e940b50305001042c1a142d81c0741b280010000c01c862540310910740000d29040690102d003c40c410000700510341c2d0066203481c50755502411038003006034004400c00019541c0d44840e00556032140c002e003041d9001c000b40414105840d400b013041c007940491070550b10b44680200300842075803010985002c41c114689140507034540c8105024030991211780030694011a4403a17040500544520014204040041186e29140004960200c0e1050790b00203070205034241e5403c81110003641100011034a600c0314014410710f001001c89554115151315004840308e01c0d11131081d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 815327769 1250 815326519 815326529
    0x6040306050603010507260601091206090309060315030f0c0e10081b090a0911060a050408010f0b06070f031709030d0f0b0a030b0c13170c0102030702010818070f 71
    0x1040d6894a4030801d4215000103200c0303801c0c000016075508145602c02d2621032280001800c0c7c1c24a5218140180d942c0910ba80c05000c06020f8071060720104003240c2c00298115101f600e80c01e840d2600d03450250250381d0300307817564501c038500742e8420401304003c2036403101007074050722814105988030410126108003c44078240786d00e9000f03104118030402000070907140c5180202030a800e584940000f0b06500b00500b68071034150b2500042c2c0188841c1503400e4a0815000300710382ea55400050f406031181c0c00c00d1044100303551900e00f01c08207a00c503d0003103403224a00205000e14010711941d40c0942c401e501075007582081007032801000c0132030b001c0075540d00950354000255102d5018550300070548012407003a6088034184800b04d4240c0d1100811030003940d0b4450089034040c0d540170100d003c5400b680901d1040b200e03c8950001e02c6507846000e0080d848901e0007540c4461810310016a89c0f8818540020300091040c030000b40c4104210005074240d4040c0b100307654150740c1e5282180c03860002a001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 815329019 1250 815327769 815327771
    0x30e0f210d110c1513020105091002070806070f11030f121911031609180209012a050f0105190e0c040f0203220c05010315150905041406090103080903010b06040306 72
    0x3440030449134208006034400b07120701d0040a4055030b9030000f8010701417a600c5500501c04c2c2c08440113242d00a001c4140503110000c04c9414a01e058000140822030020410740403603085880043e40d5800401115500f0200c141300e5494a09070942c0115100f500408001201c4c45d043d020307041c0c08500f40246450342c9111541c86489040c81e0012007010780c0092980d40610098080400203c0703219045c0d410701480c0d4100060b115001c580c010b86035801d9900c2905241d032a130442501020300d03ca0b400e412014014070480720000c11228849080b10410340d41c1c041800c0e030351280707011002019040900040e11003c1640c059118200106007030742c000d00c241600994000c800c2007400580e03010604609007048088001e00c4a898a450224bd0b0321405071904064694201d6102c2d910b0383d500000c010b04241918004080800e00c000348800c01c2802440e2003181407840103869800154450350040c40000c3c1004026442c60f510011941d00c804126a051354807004090102d9440b000900011401030707030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 815330269 1250 815329019 815329033
    0xd0f0c0b030709180c17100506130602010b18040b0c0f120708060406050603040f0f0b0903071506030b191d0c040b01030e100207050106030605010303030e0f210d110c 73
    0x3807000242030040081d008000d2400910740c5590340d01c41c0384804008030f06d07041d9031002d4031148034481c502e140c0c2d81c03c40e9070454000105444401d0051002c82d00300c403616402006803503001070810856903030b1000c03040c40d082141d030007240215030113141a5400105003820140303880707540b85071740e8210303000002001e4a4010f1641000b515941014500742d10071801c41d0100807c1d41000000340c41c1d408094000f034400381c00519407904000c050000c0b0301186422003000b400620300712410690365484140c0c200d80781c441c1c4800d43d4007000018011841035a0344124040b00655880d0304100c1c01e1b420305d01101d40181d44a1032444125200d07100d920841804410140c44070985140c1440180c03810203c17030341d040501d03208011640000c0410195040d08001c440943d942c10b550a20601400682c5c002405051500f0300000400d40c041d4003020b0302c10858419505580c5440280350f0311000d070000c0040856800c00c05050464540d4001000a0b511500c80060310b500d0488070480941c205c4030402609500000e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 815331519 1250 815330269 815330279
    0x171e151009050a0905060a170703260d0e12030a0e060f0c0405060d0e102406020c10050403050105090304050306241c0b0f10050405060d0f0c0b030709 66
    0x281500601040908080708803030300d00004240112160701c511800e0a980d240850110364801441600514600101d0941c0100300302da074a0312040345220450b561903400341c0f500d20407401e841d41200d0354000032402a007040c2c0c100e410032000d44840113582005026001c603803801e426040000d103000f0102a080007500c071402c804c419103010301c0944100d4403030140404100c4001c0c0e8450864066400903240c0d69111031040d2803820140c000c0b511a108031303005031605506031190a512040000842c441c0700e028441100e41c019003220898020940184c000203040b492a06104010300480c104a1500c80d1900e941c035143c1c1802c441040d101c0c1031154000140400003440d08101d046e0300082c810b10703002001030035500701039200119103190601030700084c1185001201003400010703585400c03580003580d9260a201406098004490f0342c008409a82c40100349400c02d88680c038801e09015000c80c440d00020388a80300034851420003158103c20485d00492103a010001840c083d0401751034032440c540c184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 815332769 1250 815331519 815331529
    0x601030c0918061d1014070c0203030c151b0703020604200301050a060503160f0509060109080102130305070b4008030703021c0503130c090c050903010c02030406171e15 74
    0x51002c0803005017000d124076040d0400180f81b41e0010b080d41861603030303004584082070a41c0503080c02030115000380c0aa12610a59540c0e20342c1c4192510b0f070f101c8841c0b001800c10003040e4040c0003006001a800034001400180300100f50f440700302189052100100149030010b42034820444800001540b00d44080202d801c1c01c110380194806d816402c4d9001609051800c608102241f0445114031030400c04107600d640602501c03809407151400030f40d941c034400f2800002003103491100700e8552290240c0081c182c42980156142000030344c01500d007032a041d50310344110203040d20301c480d8141480400c03400d5030600d008280000705003502c05552105510b08000e4140b656240000100844815850700c1d81c0303500104032030b482442c0320144190300b944e6060081c600f0b90303550032424016181c1005080e10030b030408050510782d44114000d00601110003803c0b80c9030b003c1d5108010100d211104030440250120342070301d42c0306110b50201c1100c03044035810755441c050181c1e6008035a98018048815a00700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 815334019 1250 815332769 815332783
    0xb040c030605090a11070f11150c03120915011203080603120a0f03150b1b19030f02030d0c0518010345050f0601080601030c0918061d 59
    0x15a040400072507181001040d840c80d002407001c8101c503900e114200318a0300c12002d40326a43d03040400003080c00c0341450a100d44410801105204410602c014818805a00201c9a00c00402c801550804102420209810700b018080010300c1c05441d01c000c030454122039115008042d4000d28504504450074081c042900283c403d50080d00001005d800c4010184211140701c1c10b5498a14180219103a0480060826500705024511080c400040e03501a2401410311f41a018110100d010343d42c070201a070707690074810102004581c5510110210f030060070404100107481c0140d07850420110301502c216900d03042070201259000c40c83c410b05489104019510708001c1c24100a80b600b000e18030803c0328a00020341d254810030030b02b50b0f41070300310210000c000700d5800c00342c01c481e00d64549401512040f0345084141540b01e410000100141d001035040e049036082590065403c0c104004240907000d440e20104004200c100c4c20b0000a540d481500c86403080e0a0a001202403010182814005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 815335269 1250 815334019 815334041
    0xd0c020f032209060320010e0307030c090c050313031815090312020c03060a0203061302040806042a061d031009051603080d020705250510091508090f100b04 69
    0x840c02105100141c15001506c5100c1e00c4035000410207507070310004071120341141d100c0700c4e0075004c0d030325000040150500303082080c1e0301c58450500c00b45441e50307012180d500048600d840700081e42c49001020030b00038444407081c0d12811290001d09600e070103009424a164440031000910281e2080060044024201118084510180c08400c1d0380d940080c1c2e4400d070207080080c40f10742c0000424107035030390b0045607070021006182c2991196170342d52800380c403080700711025544c081405003e6136001c100fa8140c0031059080003801c2d200e450404c030086640d90400c0810070450a81c0366010f0b8541c1c0d0f01080103c5200b10790702c1000ca11280c0a1800c0f90900c9a08100c4042ca4005001c0a00014601000752901010207090040c0c40c1c40035030800920745050a00400c1e4440703088003844803d4107a28024406071801501c050086a1450b0b0085a50481c2403240000c24010800000d680c0f9101d10b0003642c000f515241141c4054201e20384050078a90510900060306984411804050400d401060b00000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 815336519 1250 815335269 815335271
    0x31204051501081507030b12030912010e07060f090e090d021b0109051c0c030320070321140406030606020601080c150a02031c0f0506040b01050d0c020f032209 70
    0x9490842540c4c0e84003580c1000091001008000402c41071080c0e100c007903c2c3d2002411101c031607003016411501c07a401002d1086c040c0c86c503000c0b0b0071940d8105000740c81c14544440700910115250010899095024a14000812803c0e00300086c020004205c213500a420060150074205030101003e46440b102c1c4032404070602030070b006090281c1c0c0003150001254802c0e124051120016a0095400398146000170140100340101009059000c4c1f0202000b0381c0c2d1700f540391412010070040c5540c030a001d100090800c09000c02d103409400da45690110001c4080c182020005445030b07001e40d10741c012b50031500020742d581104102d070341d1707040215a00400e0118068042c4810001c0032501109442c0015030040c400041e2240045200300111441b00028a43c3c01007251000030f240005800c0c240320100c61682004003086c000e00d414402c140d440322050b100d4519107200580c60b02c01a281c5400c0342004c2d40900c02c8110102d01043c030007070913003554036408410041040c10031000180241d4110031002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 815337769 1250 815336519 815336521
    0x200d0c02010522030207150e03163b07110705090103080d020307090e0106090302010906300902090c071b030f17040302041e050c160204050403030207050312040515 72
    0xc001c41c99038400043c02c140340c0ca03440c0c055090505900d4107800d075102e00075030701010b070075138a59641c001c010f955640021401c0c2c41c9101500c00400c0f40e01c948900a086440c0500740b5502145000000c0c441c48802030b0b030408803030b042c1000c030042c1000c0b0811510b000100f0311443d82d50158800c24416900504801c4070301450030f5040d5100d000c02030149001c0c900008e64000023164000e40546004070040403101240d0f4000d603101d00008000e101d1a10080340481c07949076003c14034030302500d5449040101c80003c8015614415950100c1c5883c0c040ca00502c19500c040441c05600c804059510460a0b00081641e4003210715010764420f005014580010008203000d200045d80318001240043d04811120004030100200203080e01c0356900c000d500500d4032a07120b000c404d051000c2c0381c038104a0301080009a81d4101207100e10300c1010961146504c41c3d610445c01442c1c00d520490b00140a8600103007003410303d1756424034652101d002c030f0020541c030b0360400041150400044c11903a007800780c52082 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 815339019 1250 815337769 815337781
    0x312180111040306020d0e0a030203070b070314070f050c010609020705160605160606050901030317010b2b0f050c120702190201030b03150c0408061503071206200d0c020105 76
    0xd020b0341c00000c0200340c0000c0d12180075142504905800706e2600280c0d0404012450041d55031703400f04000f11071020035100000c44103406131156a007038000035506204681d80711030086804018210106007400b005024048031584244625406030040010051b994030301400e00d10700e0980002d11010040e510020b00b480f01031b9004060300d0442e00400078034010355182e0f26040020340000e401076a009071040d000003080c943c0c000121012912480e0a00100e1b90321900003c1683c0709410160480207498030300908182801007240075044030450000516040d0568414140e620540b00f08030104004194600549604002c403500004180010003070300f41c40ca1401822540c403a00042e0600d0794684010310f1a407028402001000c001812625280c078100394540c1c1d0540050052103c24440c0030002080d10601d004000078400c4005e000f401c06501e0400c5040c0324442942d4112a681e454412013688510301803000c80b508000d4813215503c941040d00c0c200112032030202c151003103a0604050040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 815340269 1250 815339019 815339051
    0x3190210051e1005061c050a0b0f0d06020c030304030c0302060a0b0a0b0f1603020d0f08040c140a0801140f06330c0f0a1b0f06031a0303121801 63
    0x120b02075500d0040181c658481d42590901c500c1c9a00480d04440b000070460081020341c0100400c01d00010000c2181d42c40e450b4261301100d4490b90015084518000d580950b481e02e80401019540301f00d502501c0c2000b81c5521034155002a51304901088950b8500c1082607014002240c1c0030401407410005010000e00064000030300d1712680b00c42500001e800b00d0080c1c5020119101d524051070814940140e07441c000350765072160301c100c0c000914441460030b291442001d4250242c1e07000030301c046e01d00b4140001c6a014854903011140d002d0054100012034490a01906044c42c18070304203200e103450695183c00a40307400422662150300c0c1044006098008050f105c84e01e50488005100d0503a9101003181091060002c0f407c0140705690204244660000345103140714401c3c44140c08c29900c06c040800302000c2c03402000c072000103403203061007403034031a038490914940780349001c010f01200080840c4c00e66200c000b580c1e64000c540f40800820183c0c14012244032120a002000210b8000c043c01c0303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 815341519 1250 815340269 815340301
    0x110720040c1403041101031407080f0106020c010804020f0301090b04080a02120f180a260c03010b060d0510090606020d020f0d050702010e190e0103030f0f0e0f030703050319021005 79
    0xc02c0d170028100301c06010307486544190344040804040406c24105100060007520040b103620300715041d80703000422200d1010800010070b91042e100d00d003041e00d030f131f50030003280b54007041103250159a40e0982d600481ca03040c1c0c44034090b501501a10ba903550325000006d0600f01c1e4041c41d043c86900400c401c150320090041100c13040344c1b44001003c1410b40791000140e4850960340041e078948d070a501c00c0030101c130142089100d803030f12540844140d8200b0f101070600742c4035400300306644002d090014002c50112500303c2584520b241c600c2c0980310f0f8664400030100e440c50381181d00142e1203801c54841843e010403c0c4003816181c0002030800320b074280070040640c40f07075100c02130401c0711040320001c40317031540d03000981044403480d04442c0f001e48a5190b01c000100911007540014500c0d1100c1c2e00d02400b9046d4a00401c0d101d54480c9840364650040c0240d42c8025020203405106228001000c54010304c05050f544c4420b8107521000c16910000134030300400e40c0d6040c0417180c0f80800340014044030720300413 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 815342769 1250 815341519 815341523
    0x16020712030e0d11060f090109080a0816051c260f0106031508121e090907030b061207031a01092907060c0504032306040204110720040c140304 63
    0xb25032950f020714003001550514000603802c10400310b000c0b0003000000015098009080c1e84110141d130340ca403601039850f14400c4002e008900100310750426407078000e2010709a680104100c0380c40b218020b0414400f0440410100001070100d242d1465500071101d10700038031210414507000600b000141103c00c440d040c41460140740c5e607440340c006082104042072004044003020395000100b5641c004c00795134840d4260403036512040c0c1d62400c0c801500703c155002504081d028001c159181c0d80700703500610380400313595404136090114405130714030300c070101d4490302040d07070f000c40d203410f241b5003840d103642c4900400d0307041c0030748141c00f400110f428000d80300d100e00d20201000710707540e614416490309200344900030308400c1c1001306101000782c0007801002120300c40e6220051011360700d108029a10b00307141041740d46420000c0410090320305a04001c9284a203c8001e600c2e005241d559a0034683c80802c00b4010544041800c0999240c1440342e80041c0380e050410146055842d000c03050107120007400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 815344019 1250 815342769 815342779
    0x301090f0e0d0f14160b06010f05090f040609090c050405090c1818060a0b0f221a1207050915011b05010f020406120c030e1209040b0916020712030e 65
    0x3c188400d48184107192414890b40c01d182d0b95115000d0340f0b00e5802c2443c000a9411a0701a404900294403c51a5504904450361164140b805403400c02000c61104164241e00503160340011a240000f846a0b4522a109641d0700b02c5091508040c030040e500010000e8219401180c0c5d80c002c191030f000b520070300f0440c048060070031030307a107a82052a00c0110106002c83c144503800400400610386e9102c01c41000044401c2c45070452a01c040003c40d10501c590b00755885401d0742c071000c0c400300c990131580c4060600001d0b40e0111400c2c201144c41e21041c6403004056a0203403000b000b090402d101502c0c0c0000c1c0c01041654051544c60006c1c1c03400348041c13803a1401120342072060080c0002036110482c6105e0503481550b985940c0c090007840000300070001007a851400040c103521074080c0c8104004113490b50094100498404070702d2085810103031280c0c0d001a100e40b860f5005584511a851083c0034030281705451002c040c0700245021040d030841e01104a200080314046900031464a000c5542124 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 815345269 1250 815344019 815344037
    0x120c013e0f1e120f13171b060906010f15110715030b1809120d0e0a0303091a0106120c03090812040c080a08030604091b0b09011d0d0210020f03030a020301090f0e0d 72
    0x2081042c1b6114803040781d42030400a1845202200d80412124080c080070000c0350340381c0e626290b000945007210f00c9800081010052113201c1c044c00362849020402d1101b080e03d040aa03074440c0c1184041207040302f040000e656640c0345010386007012042215451a0141c0c2c142442c05d1280c296889404405080e420100842c40c01800e01c21070f0400700140d0314140955126020526001e8050540c0e281c0031203076000f00c00900740003081034400e150304a0b10180e468031003c048504800307004190700b0800c10101a1900c050501155a02008080c141300c0c90341010f5092416060483d0101d4041c1c01c903166a41061180307070b02090f203803001e49400c48011a000a8542d89902d001190740808404100040030200f80010710844008090180218281c0742c410048048000b2642101c11540710a0b511850b922040005818012002d00c040c18041c0121803480c5400300e4040d145030002c5941951290300000180a10740860080000603885e160303050110300402c40200751188001c121800800c03518507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 815346519 1250 815345269 815345303
    0x4050f130908030414061920180f060f030705090a053313120302030c06150f040e0c12120c013e0f1e120f13 48
    0x20a486aa0040039001000051154905403020f034000712030a40c0d01110f280740706240c0d184003241062041024a5509200c1640140c0c00001050482c40e8842c4001c80300d12181004c5240d0001082403001d401442000d981000c0d04000c0b0b0800c680503032034081e8000348802c4110360352000c107a030f4000c0e0f428208661100c0f0020003050b8641030380e0f400a603205505107401c0590100704000002c080e419802c14200403024588000076620501121052080000030104901074100520030389051203803051381d14080d4082c00d91486c01c40e00f65524904441c0702914000c040c50695030052080105031014000580c0c90000070b0b40f1550302e4040e0a000d80c84900d2103201044050103100fa80c443e00306610790f15054041d44050003000da50f20381480100302007501800d840440049030805044807491040014244908a01e0b1500a0042c1c2c140301c100c10b120100d00c259040c0c03a4149080c031040605600e628441038000341c0780b1400f414001000c60f00f42c09100f004c122032245840303003d07001b0390004801c1e1060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 815347769 1250 815346519 815346529
    0x501051503041e0c14010e010315030f060e0601171c0f030b010908010c120e0a0b040f0312052d090303011505190c050708010507020a030f1106043504050f 68
    0x102c00b0082c42054440801700d2400d14801c44417503103c07000e036100028101c03040015000c4812a070311041014507409400c000044580420b000014440c41f804507250f540c145180f446d02200382c200000c0d5004448255400da001085100b082d011480c541c0042284000406460485408580002c0548480c000748459000d21846030040c0b54003c020400c40c03041c080300902001142407074501c01400e280800d2a021000180b000360345400c06106602c545855588040710000c4060031030138808111490f0840c101c061080e00c1c8180d805c2d280c110180b00c0000c4c910034035091426050301c0d10039402d1083c030901c0330b0000256410b660310011a9420302c1284007094549000d04030404213070005028904d000f0303552001940307007001d100c0c00495a80e00c1e2101c109500b0789000f142d614005030300500b1101c010030304c0340820b400411402d040080480000149803800c0070800c0360b0607140d01c4020381c8020040e80825030680c144441180c40c18402d040304c440500350318400d520900d445100003224402103580e039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 815349019 1250 815347769 815347823
    0x80705100f05090f011e030510170c090613050702012016080306031204090c0f0f02030a0e130203070c112407060b090a090302150402090f040c0914040501050105150304 74
    0x1010100f01516000380900031f0103403804555190208000b800c000030341c24000d4a902d20f0300c0080341c000c0c2c90f00043c80740c14080b03004002412594498401e55040a284805105582c0164203583c00860f240314031705907840901210022000c1a020100189a04007520222408180d58800344941c5d07039456480000c2e14240400035000d500400c00103000036601c4181c0c0c080c00d1142015103401407102c41a44096a03851050004034015810411a003503259200d80442d0039603050060444040c81108640305017280c01c2101c1600c0804c4505004038148204200c0c0d000c440b6808641c11a041c3c0400c407c45014500c10390340d074a555000c0450500200840f42d001048a0040503102000515043c8035903000340910050070f501600980e001001c12014801030140704903005407641340c1548a00c001c481844000410503a070f0345501c01d00c0400c4c5122640109602161448541106404c060510034211036040e40f01c50300c128403058039000e1002e243c90680c1d81c85a0001d90b0b04c1c9070030420003002e0300c10242c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 815350269 1250 815349019 815349047
    0x2030724230a090f0609081b040609020703050a1404050307090b0d1a181b0d05070308160203010e0102031e04050a021008010e0601031a0d05010b0a080705100f05090f01 74
    0x40c1c00b14901c1c1c8034030b0303104822100302c0d48050b883c0101d1690714034050350a11807e00900e9601d40045a0700c0d92003070350358071442d0403c04014100040c42d507a00c1d000300c8100d812110080340055000500f0400040d48001000241c000302c841d1589424174010010b43d9508540c480d101c08030740c40c1c1e90031500a650744000c02650360380000f0405181c0708013101c02d010fa4401201c0a1001c3c03d80d41c1101b0180d144005035000d0300a9228800c40c0d01d038459141004890010b0340d108803124802d042c000700000301c008002c4c0400b80e40300d040c0704494040a00c1010309440030440d0408103a88140100a40c01c6102d05417000d01c02c4144111401d0760320b450504e18240504080080e400c5000e0f113000f5200154846070047c100c400c00090b41d0741c51b4031006c004405640c03034441c4210884da000c4000d5152403901c6a103d015044c411000011007200300b1000c14800041c1d03601c0005a900010300c20445801e00b000c00c840e0f81d4082e85001075602541ca40042c1103400381c2041107004152055103151240d0081c10320b100007070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 815351519 1250 815350269 815350337
    0x72006010303050403051b1c0f14030414040b090703020c03121e0106020c010f030f0204050d050a0b090a080d050402012a030207080c0121151202030724 67
    0x368403410050503075030140c40125454440c110350701e04080300019410004003001032a94003141c03c4002c41c3c105d4000d0100041e281c2036541d503054000114402115201031302c1141c05151120300e8451001004c0c4203844046004a0038413910408a0f51540c0c1c11691010703da0030010384890345480704510714001c00c512081d94290401c180803000416030b203a00c1c455040c0d08c0b02051a0f030b07201c64040b42c0300c0c2e9080d10000d0101d84558000307030049001c0c0c0c0004c0500300305408014103080d61000001c09400241c00203071015048a0719904c144805400c24030340c0181d034100100030064465079201010b21940d0421038800740c2d204049002c680c1714070200c400003007032a66804180c030210249801e030386181c000c0072005486007140c0003c1041011900000200050712240040c80c03c01e010072203c10301400d84400100d03680c2030300001c4d4824014804000d400403141d200584a00c0b881814034205c032503006505e0b540b078610411280760801040ea5890700134103186c062085404c4c00701d52182d914128080000e44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 815352769 1250 815351519 815351521
    0x1111e120708060f040b030c010e03010f150f0e010605041e0302090f1f0506070f0606080303100602071e05060c101d06160c0219050415080d0314072006 67
    0x2041d8400c442d01e000f501d0442d59600c00b03007001800c0000b100c02d0b0940c644d0301504171000a1420758010344810040000103000070a001c1c400b40900030449070060050b1002208030f55062184c0a6818402005045440c000e01829410480041c1036400785d4441c0b0038041010418a5442c13035848503a0900a69014004c1509030510300e00e01080798200f16034407a0b400303140603c1086100e00e00c000380000c80d00701802251800800e034803004e50a4201306c02c15503c0700d441e4503000983d03280810046210b004110340c500c1c3c11a00b0008001d0504580d0b6004400692006074a10700744003030700310178408170b40080750056600c880b20901d4500b00300c9141c9140164500d072000d148058013604001150000b07501050751030958942e40d030041d13465549004e0b00009580d0005030340c014100001c0c0b42d034061f02c0c1d08c5a811880f9a0302c0380020281c2d400c500c50802d2114006a04021030001080040300f42c03500d07030405000d040010234508040030b000804000810051080d0b0500640d020b01d49180411001303000d40b82c403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 815354019 1250 815352769 815352781
    0x2100b0117130c2303060402060a1d06040303050307090e040314070302150a0c09120f02060307050708030c0403031b031e050717090f09010b04270510080f01111e12 72
    0x1c3e00141c4040d211244904d0003401110345404a5200d10a9900130009414513160304412100940090340c0b00408402c0e100e0103181c0386c1d45501c01380c00218403a5031015a42d1400e040c004050f0720b07284d409100c126070000305020000760000002500303a2402050750b0303100c180c1d40c20304900d40040080780f81026090303003050201c00c9505401c068842401c40d180ca440980c3e640e0320b40e1400c41c07404840586002501d5440c1c00042c03410130020740d0008607520386613091400a8440e01031a50083c8d0300f01c400039000007000c0027010341080000d580290380b0140883c90f60800c0e1406800030400140425458000001a00800e0700510940e40395640180c8200090b0650080a003101d43c810350030701c0e125003414441c01c2100e00d0081030040c140c07107020800354102032508000c04c8902103440c0d00d0491001d141e0b000ca10f05a481071040724402e804e00c0140504140ca0100620309084c913507203110320359134144428148405004022140c800511000b004501240004402414050030300c1d8861001003110600c09 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 815355269 1250 815354019 815354039
    0x11040e0c010201110c121308120301050a06080415090201090b0409060e0109050103020604120f1502030714090f0904020d02030f030307030b010215060d0201030b1c0302100b0117130c 80
    0x9400c6000e8008100c1d104a032056074080e800395281120305640038080190b00341c0c101501400c0f1a40c1144511b81e91603485080c61401c004401c00d80300d8031044080010881860504071700c0006180d0790803e0750313541c10f154940301600c11b9007030f06107115203440f88103000c00c5910455560005001e103400b0151500c1d25201c2c0780303014188030b00c26980c42d02003090010950200074404c0078122540204460710702864129a11801300e41c0400a40300084a108540042440030280d5000440101c400694034030741140e0241400f407502034204103612040c0300900d42a1200450100d4004d412202c001d0f255813907100284502c4051103009425019101d052111200c0c0000a5801070789603450a1101700d046100490361940c4204c150311600c00403c000c5002410700c884084030b2203006140c0800d20304031003c08a10101c0000c098600301c0c401682d051002d140e4144655240e1692120081c420190720707900007001d11640b8401d00c4003440e1071038003141509904192080c00703182c1c01035132159010f94952481d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 815356519 1250 815355269 815355283
    0x100503010f0f14010803031906051906111204090b1f0906170601120209031e06090d0503010305032b140115030509070e10030203060a090c120302100911040e 69
    0x82c18a003480c0f20242445101d4004505075201d51005504682c1d888214003200b0a0381a070800344959180d00210305c0361195200003034820303180856500c029242120080c1b03007042c000d00230b0383d00390440309101d0003440e508001c0f501140c009082c00705001c50711100082c0c188603045401d104035400d0f40845482140c11009031300444070030341c8400d51003514001d102c20003034504648071341c00908900b0304010200202c0c3d010300354010015046510040460744003614a400100048100d0742c008020441c00803000c011101074500c40313190682c03d551641c0d4a4540e03d01840d00c00c4c00740070045d43e66101c0c500c1c42400c1c207000504030101003400724091a120a0302c2c4120280108a540c2d4134514080700810b0180c082c10b4043c90100e00107012251800845400703040020300740103000c1105660000150341c1c00c000c0b007809007a000f070000905980ca85001c651881140c5e0003d80082500901603003c0390700072540c00070100703400002080c3d40399030f86000e80d071000082c0700c003a500c5131a08030340d4001c01130002194 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 815357769 1250 815356519 815356541
    0x509092422050f010602190f0503070b0910020f07060504023c04050402010507060b0a0f0e01051c03020a0f06020d050403050702030610050a05240424030510030b100503010f 76
    0x802c01500d402a60815884090203201c001d1317130004d2107202e5090352407030040358103030b000b110721003039054060342d8050031940440c40548882c6509401d0200381802407140c41908203a581c001c5240a8a01c08007585c00d018900d00500499500d40003d000d5450341041c44141c1e00001c90301e20440d074511003001c2031031800d20306c01050003111507912244501f06481903900540d0161201d504007101961514050007075124000d8001d11845400100c407182c0402000181814070f000c10029810001031000f10050741c4002c3c50140400400380e0086a0040395203034056401070f4054000342c040781040000f030710a11800141e05403400303082105140d4030501518183e8070880c1901c481d500c419401c60b10032003082c09015031080d4094420011450b00714090504c01003400202c0c6254550f08542881c141c1040c0c0c02a140c1d2a074156942d01c02d0720040122525031285410100860304218000745080301d600e010081c16101030388007181c4800001c040079001080024024842503054212080140944e4405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 815359019 1250 815357769 815357771
    0x403020307050d021219030b060f0705010e0303010f0b0307050c03190201050a1116050f060906061804080301050111031c150b03011d1012050304060f0509092422 71
    0x10f0741450510224201c1d583c0c08001e61810b00380000040d00c200e1000c1141c0391740f014582d54140a2a443c0c03607503005070034800f5070340e190340d03071550b8950404500f92454505448141d0704200010b104403500c600000c0b09541d44801031940741d070380e0400155520312030b00030300b4115440003140380481404050b51400d55018558000d1100e5154110848103481ea0800710700c0b4104000d1128007e13580b0a0310b242090390703000d0000c444601c08002c141343d09041007075a00902c1500090100403030350034401c4070140003003041c092035074181c600794441c01c54074041070040c1f50420610f0291725148110410a44403104446c204140c4012181c01c0302c900100807081c50002c1e0700c0840701e00010310329008400d8a04840d001042600c1d46005110040082c0c000100311404210380c3c00808201200140100400544110010343e038842c24507101030a074141a2401408000303041149108940710054401d400c035809030325201021f0701e00c10f45042e8201c2002d50361904080705e021001c0c101100c0824103903060400c000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 815360269 1250 815359019 815359033
    0x130b06012010060801150311011b060f0b010804081608070b090708010608070302030a06020307090b0a0302032502211e07061805030f1606061d0a05090c190806040302030705 76
    0x90341400d0341c01c211b00755074442569400400100e40402041750800c0e805160980c540600d00d400075542d00074010003038840a40d1013201040352140da1264144d60f12007404c1c031200c28a0103940b880c100744076840315400701d20500840c4000300001101900c83d01e55000403040c1861034907080841d1764032400d03c1403004940c20400c0000d4220400310b42241940d802074050700300140c4a85a16002e0f500151642e002c0085030b10000901c1c1c141e80000d025041100d540150307903030030311950740248211118a20290901801e150710485a000101e5041c4200c0c03500c907010014508101d00c60381030144009100e440380610301e200c0c981c54074160003000a68842d02041141c5c5080e003202c146901a445001440f41d40100840420441c20502806070356110311003900c2c08115566401050302d51950140c1c0304042040caa581450b5200a4200d030b0001c0e80302010032a503d80036080f607668075907008004d801007070301820a043c525580a00500640746c0c030fa00f00c80c500d0416141c020359a034400750094405000303400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 815361519 1250 815360269 815360279
    0x109150b04141014030307050102130f0f0b07060504020d02191d070e0108221a0f060a060f02012a0215150103020c25140603130b0601201006 62
    0x35400c0e034000c011181c12000c034641882c00800d41041c0304d1101c240d02d4070082c0038010000d102400100103003800812125002c0c0d24000d00100f900d22aa004081060030310001405482c24500580e02d04640146006c03880703440341d00218028140000000e13401000a0310307051b4045140402d00f9003160040d40c4500480c4410009582143c1000c0d80e000c000200354848107081c0d0b61060f0001034002940100300c2020024000d290a00c9090101c41207984802540c29060400d0800341141d60251341040d4000311482e12600113a042c45660098105010221498407681380c401d5001c284850800c402c44000c80031103d555a1102d4001113403880188258a0300c8544480c1e01d014450180103200003400000d21220011b4010390840c13102100c9174450003403202c8103440710050220840c4940d03603924402e18207100480001c02010002e0f580981001c10031700c540790200184154007980c015064145070346801004982042e01403248200310b4500b0301861100440201e580070703503105030800401a0399521 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 815362769 1250 815361519 815361551
    0x815120706120516081b040801050f0a0209031f0b13050a18240e03220803310b0705030901090e07081603020d020f04030b01050409230109150b04 64
    0x104c030459555180c518001c41c0c0d0750b00500720680c01401450b03030820540c2210502900c0c1d50003c0c2c2c4408030301da450720284101b1004050110343c0046c0c080c030b003d6151105480220340d58a100d13005510039a140c00e1032081501d407680e07000e00146400103080031142000500130340302402d0141e5a1140aa00d015031201c044621501c03440fa009a00c00e8554031000101c9600d25030405079888290a8544c4400d00034240c1002400240180380c0e49020850002503440c1ea02c000344510750708518001d600c00c0007602c000f56422200c002003140245002c00710380c40300980070b00102d155680500141c00303011882c042000404405495103c03400c4c2e03a00207405641d400d42404101c015214800468084004503d50056568041c0325907181c6040242c5030104000d903403002ca80c400c0c0c0030180c2d40703030010800b442040501c170403190041c10111814807203428152074006801e003e0701a41c5c0303045000300611000100c429005984101d80000c101c400107000700030b02c10f01503c15001101c0c4594600b0501c00014401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 815364019 1250 815362769 815362771
    0x150409020904060902060d02070f0311030310120c030c08060f06063610050d06090606081812210a14240d0302070e070813020108151207061205 63
    0x5081901d10307295522038000030300342540103907080001001304000c03000c542d0006009140c0704075444080340c507160400400aa104e40f0940c07800e82c0003001440220030300c5140040640b50700c020984910082840d0440003209d05901c010108410000001000d000102d400791003230101e000113003515a240c07400c03c0038130310413840d00302c84070f4289580840112840050302e00a004010004a604000010000d4064200d44c039558001580c00074032103240f0f81840c082c1d10000c004541081c0a0307581032840240141c10000d1822400c441e4000d4201c9000004000500010140d148006d40e50354144842c07240f0000b01c000c1c2c2184e07800c1168013003240d041f91886680c800070f01000082d00e458a074101e40060440d24141441210040c00030141083d50b28120a015828442d0f0010b041441c0392901a4000d0b000003808403081c860f2070810800302804d9070a0250403a41d0920b051301159a9010342440710400881c00117420800403c540000d8840004810041e07c00e191241120301e0308860191040c2d0f80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 815365269 1250 815364019 815364023
    0x11060703140f220602030702120c07050105070f141c0503090a0b0a0605130e01140403120c050408060426090105040e040203030f03070201061e3f060203150409 70
    0x2803070341c00280541410719540c54100325143d0082003007150f28109000e10014a000946030181d00205201d0301540400501058285010201d8100540c0e610a25219040d510950741030183c0003901c0d40400c43c0d0820f142c2d6005d903111b001c5808000541e80c090f55550785641c1d040e40305c0d549034034443c0e038054000d2043d01c0c405c0300480700524a200c120342e641441044082c0181380b1050300c2c0c4c0804603182e070b90300741c0401c18014030003c00224025921489400e43c1c8814141002d001116000c0c0302c08260320400103614600510004513000b0750641084a045c440c076070040e02c041c000c501c01c1c4801c00496842e884ca64030000f400c1442401000b5440d003011740f0500c1c00c2e032030115000b00700c200072410940003107560050006040d40d040c021000055441c5600031945040182d5407000e0a00802d81030041240700801c85980e07858035241466070880010040010129043c3c8950181c011044c03a0705144039207071309000f0400d4800281c070345071100203134000351003600c0d24003014030215405007031a20038008065 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 815366519 1250 815365269 815365301
    0x2030c01031a040b04060909060b0a0905010302100e01020a0c1203090905060f0d0609020a0605040801060803030103020609300a0c0b0c0a020613120807030e0d0b06040b03031911060703 81
    0x7086602c100b200402800e46041c0d0402d4481c0c40c0081e840707046100e041c144c84e00600c0c0100f19254030b8020405809425001090041e2a200042c405a100c10a60107190300040c2031100640c0d481c500181c4c5081480303c00180642182d071303404100b059500300c0202810f0300c00d03100d46030300c6521403034128141c1d50100d8266401c82d0422005090300e2500782035071015240500400905100e294000c00c424100da608030602144c00000d04011a4000344a140010101d04010711305550440d800039865206034000288610b0301407100c885140c00720101c0844141c80c101031741c01e4204049803803585494505030280d65034480090001441070703481086450040101c03010301216905a0b0030841e180e0001041c100c520514414003090048414030100e03a118000c491541d1104c185240040620341401c4010f800381c000c5071510b8000a0482641680154007190003103000030441d4086448d50040401c07080080152414410605400c200070722283d02e2000c0a03074019503503505080d4281c8401400c0d82c6108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 815367769 1250 815366519 815366561
    0x20040e0708010e0c0913110306030f030301050927012d0905060a090c0801060602010f0b030d0c060b04200301080f030705030a03020a1e020f070609030c0e040203150a05010302030c0103 81
    0x10701d0440020181c01c00020105518846c0c504103013000c4510015a030380c0c5a41c0b0000902c0381074074080083d040e404407200015803541d810131010450b20030002e000c0c0a8210300b42c258080c0c42d05890901c406a90740342c2c200801411049540724402c48003030030b0004164899011014040448a00540082a40000c010051038841d40003030b000030324610009507140518500d01040e030502c00e000301401071040b5400803c803d4843d075100000c9481000145100360b10090318240007a4000e000f00b01125001308000540c42240c034042405070140d40c1c102c4800d200792015070f0364104d4902000d1416205110101c1b00c4e82900040160307506d00c20740f10007910740c0c1c0c07040c844403062600c20340050000782e41500e80404075201d096429143e0503648245000580c00c04429000c0101c8200030150003054940741c00034105203151646411080c00c3d00690104494920000b01951020094103c0071101a1049181c61812182980041c4000c3c0022446070080501d40409982329004036207020400180f038102c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 815369019 1250 815367769 815367781
    0x904090b040b0a2d020415080f0a0515130609020d1d01050f0a020a032d0e0313030f020303130321050906030a0e0a060c050d060f080c1320040e0708010e 67
    0x71315403400c410848055001c02003c900e45416204400d00000c50303445481184c10445c541c0068204020b02650000c2e15002c10015403400224a89204500554118612690b0711a103040038040c00e4201c5007485000040551201c0c007950320030010080f010350f0910035500407130030007401c0e5030064603a502d1840d81000844c208a48a43c01403280f0315203410000f0340d25000c242c0c64900a04c0c04185900b4500201407030750280c0000d4050703c0c040104800195241406041540180403500c0c0405001844110f5280b011510708204a44031000440044490180d491070122845076044092101ca02c40e070603c0c2010a60090040e07981d001401410541035564072045400200007800c0040c0082c4160001c100c01726115109400300d245040e9030b52650703040c0b144844425612240d025405100d416502040441d0b00499034030305030201240d40e04010a4a401050050035050b02c0300e01d43c82a1901c40840d90380d1003440123100711000c00078000c54513030310f2050030b0b641d405003442550301101180001400e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 815370269 1250 815369019 815369081
    0x906030809090a14011410141c0b0301021b1002042417040b100605131a19031a090603100c0c05010614030c0915060702060904090b040b0a 61
    0x10b03101800d07100000c1c07404c0080c284107041000c00c0c0d1203401c0d88988400300510904140c3d00c00741d1401d1440c10310194102c80c24141383c11520502a003104445208400c038004818076800120089030028001c1d0b4541c07070b000001440f8000040d41006003842001c0c202d40213122140295001c0750400c00c030b600e8849404901600b46404048610010880c00c0d260255651b0070701c02855000314060b15245038245081058461800d030150800c4080c1300080c04041c0c1c0442c0c60b11211801c2c0c9103aa031020881844030011482e2500039000301c6842c0ca000c6100500e0b0b0560b0503400142220203241740301d0180d4a040061104200d401d076082d075099000003402c0050801c058204003440704291501e11001242da403941030031580310350481072000d00c0c81c035001c00149ca800c00c29004000b10031030f0900d069051140d4605070040d1403c3c0f405010725804203a180564be100403d880c0801c0c0050700500003002145001080400c08a40444a00d0041004921011164410020498640040c0c001d4003122200000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 815371519 1250 815370269 815370271
    0xa0f2d0b0f0c060709080106060c0530030718052b020312130302090c0f0d0510030f060507180f0e040615180b0303070b0133050a0207090603080909 65
    0x4010800700700129841c102080000c80d2103811503a503960050f900f0014480d096417210340c80328040022034417102000c2940419003400003020300c8402c11501010b88064540007070250020845e04401004200000d80c00040408500d85018081c4a002ea00d9600b00300b00c0061042c3c0e200d141740000182d2200950400d0810081240001c0031500c0c090300f22000e80d40c00394455903160300480010b200030011400c140701220f07080540d211a103070500d20841542c4007640104255030540030b44580102d25401c91800c00786024540200700340d00c4a981c5410b008010b8001641c0c0701000407000b020b0344040f10805084042518400721140311614600212201c1084024000740c46190f40c4852103400c1184003181c60006112000a1840b00c01d00c3e840f5040032500b100300168000e8004000000c001107540ba1072a05580c0140304544810b00c1d1041d030b00740316624422008440000401d4580706040d0000098000201e080e800c07218080d446e510180141c41a910009021a00070700c14985686820a03c01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 815372769 1250 815371519 815371537
    0x51c020105030709090e0a150c08060d0312151706071e0203160308010315050c0304140118110a3029071d030c040203060303090a0f2d0b 60
    0xc281da035120302c17042e021140340d410903100b1584401a00400c010303d84200c1c03140720303010000c01c0201c020048005480c69800400c800e1141c014001d01c0c00c105402192000500c03001407000301b10a82e103200300854034a105000e0303d169103180c1540c0c1501c82c240002c0c503d00c1207280e9590b80c40e0f0700c050b0920b0b044040e2814a105030a50100780102c000244654080c4100280241d4a1400c95403542c10010b8043d5003042c3c4440c440c5040c00100080100070f101260f41255010304500c2821004002041c014841c48201d08900140640320710113020f0051521170880c0301c01c8a90340b0080b95103120300d81c0c81c0c007184ca00c1c0801e06803091560304070341c21004401890040c0600c03002600401c040841b031a001d080b070b003d003142014048051101482c0d002c01d00040c143c810709014081e5143c120300182d030b5150381410b058840d94000001034100d031000c2c0700381d8a160320050306401e5001c0d201c1d48000c000c0b0700709000e4101300101d5592590000300d0800c2885085005c240791400c5101c0c188421101a54024188 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 815374019 1250 815372769 815372777
    0x603010603050604050726190303020906271806090c07170a020d0521100810091202061b070201090f06021f11121e04031206051c0201050307 62
    0x102c0c42c14811144030394170800203000307440c0c1040201c2c07207071080c04041d0901d828203410200050010010325420020048449480c0002c100d1a0480207880f80c0c00d0701b103410600c08038400a045902e401e0203440c0c5200c411070040c42403160320500201c280e0266126242240090100e911810002119500401001c040c2403130480c5d00d898a056a190150000041d0316002584000036641030140107046601440c2140c900b0b811086a00650040101d040c88030350f50b100041000b0348102c8449200030001038049d0b035100000c08d94400c00401089101b5030704c404400c1d5070b59134201e00c04140ca03407040c50100e4030544480402c0007445629003100c40d00b01c0c144082580c01041c43e40720400740c01e0090042c5e034001e101404045040c80c00d2241c0c840c10310303411b05003012861a8804800010345002c40044c6051407001d5840700c8402c44040101d0070340081180340402403009155210041140540d0084814014155907106020748068000c941362307a08280406024015807080c0c0065420800038a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 815375269 1250 815374019 815374031
    0x1050d051528080309060d0e0f1002040305070e0412120f020706060303120903080a0209030c0a0305010203040c0b0a0504150203071403030702100b0604090e160603060e1302010f0503060301 83
    0x810449442080d0710100810303041845140c1031400542c6102030621080070710b08100341c07000480c460b4010350b01c2d02d502c00303921546800100d82d42003105460401c20307201200d40d00f1040e106c098000390700074081903444d030140c2480460814030145040b4000c43d8406c01e441c0030b01c00300b807004946003108000c42d141a203448000e03281521308140081d01c1ca442c00769a001603001d286140c05404d104a85402165045c1841d00d07000100e03800c260500e6100d00351100250303a030140c4000080c20f14400d03800041d80710348990070100510005601542c40f80e032040780720307142080e101c2c51580b441e801085980d1001403c100000c4c07003d950b00b001c0c5607445007201c0c0102c81c103004c4a03030b845010034219034000d400240e1010040019080c2c0c10000041d1b6941100002c000718103903d00400c90300e20550145030a41600d40d01d6850200804005201d80c41100303400e036691991701e521000b000350100e80310780b4000e48400404034040440c6820403400c0658143c40740103a4071042d42090b96a90002003290381d25543c4e502d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 815376519 1250 815375269 815375311
    0x81005150d090b07080f040203100b0a05040f0516020f0601050f010c052416020a142503020a050f0315040212010c02030d0c03060e0708100b1b100b01050d05 69
    0x405142d190301c0c80351800c2800703440c1c540c0000b050404003c02c1d1648000ca41c1050001603140070904030f0241103110400320307032520070b0b030b0101d900000f00d507001640140c44c202c0c036a43d204242d036205d0340c080c06524039101e10b44c02500b001207964501d9074207509150b810050040109142400480b4214281030608070a0b0700044c1e01c031541890302d07141d20b44200c0d8445001a564400851070041c1d84001c888128800342042814025540c00c0403001c02801c0540c8007149482045013044239009840c4201401c4200d2540380007928081c180e80c1c40b0481c002d081c6614045404c0c80c080012444940d405001054991000d04441c06d41400c003410513a000f101d410112101d80900f8000e25100d90f0030340d0011599a00c8080181c812200b04010180030145007040034048901000d00003600440585045509074a4070001818040501d0780b100305802d80c0000c0c5202c040c408690440c08526000007a107400790505141541510050764006002030810400c03445016619840503822a004100e1051416510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 815377769 1250 815376519 815376521
    0x31d03100221010f0b04030611070c0f0303020705011d13110409090c051203030609070207120b0603060703060602121806180910030305120703142401081005150d 71
    0x4115400c2075240000310010b254030203416840e00400c1581a4600840d15100320f0420600031800300a0900d503c1c3c5203000b04044140f000e0342c034003582082d0079a03440b0390b031400c3c1c1c2c030031202091008401500401800140e158024594110055000c80c00c0ca038041e10719804202060801440c44000995510044840c081c5600301034000381c0b609103070010307000c0c006d410f082c0c1c0030030030075448240b042c0280c0c40c230420a4000031007038a2f0030100a8446440c19201c1c800e0a030304060302900301c200048036004001081c01035140200c0d01644e4141c056511a40304c0c0582181035440c14000c2c0c002582c08140350076410413910008150007190716001400114900f4005001079000082c00910f130030540101d00031a24008141640003240030b078414081510f5568040c0580c00b0b4003100441e4a200140092181e60003038012000ba0007003032500209502e0864042d100181000030032016646001d4610350855009a01ca2401201001e4544c20340e03d02d0401046820208003441c0040000103000100740c0340c4507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 815379019 1250 815377769 815377777
    0x2060c0a0c2306040b190908070605130f0b0103121107061808160504060506120121120206040606050415090510050307080304080c15031b040513020d0506010c031d031002 75
    0x305d1070308204181488074440c10690a40001001d00030314040302c201c0002d10384070480b1246c0390300c8840880c03280d42e81541140808813400700546640c0c03c80310076000304281030210506036849030700d040700d20a001240464050038428030303105080d4402c0c40300348082400340c0e44507203048074441c8229041685a110250401d049405200d4820034502c600b8010b92600b4090b41d0b010304800d03a00581081391600e42400300d0b40062027502c4040c00c120242c0724140481000c0079040c140c011030b0b118400c3c4100b001c002e5980c07801300c80541d0300d180350400205c0c061030507028810403a01040d4036001403e0421880800910004d0310ba201101c15682000485032401d201c914000c00e00706001c0d545940ca031540342401d0110a20380d40d846602551801c1c0c1e50700a0444c20b481d000348090b541c00e2040d65040c109452248a507030801c81e07000d101c00385050076044094000305401d8000e400c0c1401075844080041d19140036421004000c00c01e07100040e400216040712681c040d15004044545811907022000207e901c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 815380269 1250 815379019 815379023
    0x30109051e0303070918090602180906121e070306050c0409050708010b0d0b010e032a040606020c012a0303021801081b0f070803130302060c0a0c230604 67
    0x788803452109a0745038540e8007581e50401462031450055001010b18100d801041d855400326141100c03007040c650302110096611000855645034500303803820700c002c10306240341c0c40b4500d1080000c2c00b60501c2c840d041c2c000c604110081148000381f10340e640d0810a02c460500740303441507080c004041081401003174002c011038010b0543da070382408400d10075900002c00800c14088034400412500e600d01e4101d60317007071443c80f00000e040e00c8030300c0040f50114492503280d5414403032082046000304a6020f01c4c41014505000140039199181c03e110a984091040d48090782000ca070104295001d80046080c080c4480d021060350b80050f114545440c880c058140c000039404100b47c1054040e071511503a62407000d00b44003245140290b124285024842e4880941d180e0100b2414819615201902c0c3c045a205601948a150105c075180984d491030100790018480d800114401c0c2a0303520840344803200e1039484e08100b16103511004010000c040c402c00700104409011200740109000c600e000f54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 815381519 1250 815380269 815380273
    0x3020c1c02030610031a090c01050d1d0d180e0a05100e0108030a0801081606051305130f050106050f09040c050d051005040c02070501090e1f03050127020f0d060b03010905 75
    0x982103050641034003170900304066052691b001809201040014001c04002c802d03e0290b50b2490f18850b10030140c4000e10800b56607043c004021019540041004552a1220340e0f440d02203c180814511000129100d443c0010711008042503040806401980c0d11002d170301c1502ca03072981d54082040000ca000da1040c0641c1d08082011031003d03600040d4140100720340402080708a044034000401150035104010510400045501c03600341c1d4040884002d11004000001c8100d1100c050000750094042840e0400e180c0400490305c2401007003500c02e00c05c2d41e040d0103400c1c0404003043c4802083c090000070180002801000c00544290180d2480391010142daa4019460201800180c0d4201e02e038841c1035400814041c0200d0b64007044140c122048400485e166851749000c50440030b00350380c1340b0791100402020202c01d008054006040e201d00710782045482d40005511201c03040d102d400c00a51014801603407203503616041c41c2b5940043d000b1080007503070740000320000b800c4804100d8100d5640d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 815382769 1250 815381519 815381551
    0xa0b0a240306090c121a030f0606100f1b03020312070c060509030a0e040b04180b01031208061e18011404050f04080301031709030a06050f0601090303020c1c020306 72
    0x603a6141c01804000d203006407003808021540080070b0642020b108044a4403603480310b0b40078000c1c0001381c408a41000c058217a4105041c80c0c1901525900210740080c01003500f01d103d4a0000c2c894000d40d210701d48141c4c1c90340c810340c000c400099070410340a8030130780440c0b00c02d0142c905543c1c0c0e415400c40c0100d800b0748501d12040c0061401009992000780a401700d03400038000f4140140c2c00a9032206050403c03100041c0003200d060003d0700814281e0002801c0c644280b0303035641080544d06c030550680f8000c201d0384c42c070781480950446072024126881c5820803941e00700c01303500016849038011016402400d0080c185200c0f6400c2c42900001d034000e00d03c1900d4440040050308180c0b05290b0401803aa415182c517207441d03128030b144c61106120003040e8410008440b01d860f185031041d258848002010742c1c6080440c1d04022020b004240c03100b03a140d03031203400422001c1d0300400c458012240c0c95000340a2101c50701c805c00101e500074004980d4840016080c0d00010b03941442410300c1448824510901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 815384019 1250 815382769 815382839
    0x2090102010c0f02031c090b361009151517150c0a050708071101030b060901200c0a0906030302010b0d0c14040216050a05190b0a0b0a 59
    0x2d5504244030201801030196000d001c50382d01004a46402444480400701e400e8540e8500000b004070010140010341307402c0906c4a10302003a000580094040000d0f0000144c0b9900c20020940051b600010194070010708220f420b051900700d0311000c1c0c0030f050008040d107207103102401981d8442600501d810b4000009109046542210a03220104803000f011714a4080c00b1b010031340c2201030703c0d40004580204607075904502c110100d170b03803056100d404031340c84d121249007204400c8040080340b4082400c2003c2c0b210f00382800c9041d60304007081691000080056a50030102600481e80b00110300d00a03440c8040035626110044001400500c500162062a509000b800c58804a0320148206107000001000c114804001400d44410182c01c8403030b100707a440094000e214804540c1901d07080c501314070080c0702c0d0201e400318416000b041550a40c04841522640ca4400d09000400e161f0003580403130307111031031580120040300c00545400140d5443d8092500d454408030243d0301c00310800c14560350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 815385269 1250 815384019 815384021
    0x1d01031b0602030d240905010513050708060f04180b0109060b090d03080c1b0c011e0207061d040504080408190b070f0309020604060504050312120105100908010f0209010201 76
    0x4412444451260503050070100d00a40764400c480070301c9001500c2c1c0c4e00b43c0d8a429805128100890b40c1c0340c50a00c1a01c0d40c486144003e01000d00c80c6502c1240c03640e030814904010350040314442c81e803c2d9100302c0640e58400820055002021129801c1541c42c3c50944000c001d42e480f403080240141e50010311585400e1000b400e644250300582005035091050741035075290200d20f106015858140010a80c2e268014030140d8012000c81d1032403000d003400c80413181c04001c0b032031961900e42030b07030350f100e55100140d03000c40710307a40902000340160300400b000c00502c1e10038802c40c000400102120542c2c1080f20300018151034064400b5202c60400180801c0640ca04201107105046042c0c5140e4005c0c00c903480d071041c540c60040c2040705000502c1c1d4124109071099101c2c21403141e004051980381c1b80c40d000014900d030003d0083c18060300c00e52580780c82140c07401c000d4814090444070941c03096803c0906100c554041c528040c1c060151044021030401c00a004044080000000041c2c840c0304d0000024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 815386519 1250 815385269 815385293
    0x1d061909180b090a170c0c041b021c1e0903050d02060906131502030606091f0905060702031905120403050a11010503100504111209010b090c1201030303090c1d0103 72
    0x1050398021000540041c094040141ca040680b070300b0180c1b41c0e00402d04482c00c000344003d44950040c9840d10308200d4034125040120405025421580303940e0b480400c05440d100420541c201050000c81c1c1c0c1440450610041071815500e4905019019540c0d5103451402102e0034014016030424010030914202c00c100003640481401c84540f441d14064595660642c0143d070000f607080e800200003003141d103440e0b00712021080301402a40f2a20002503e103803424091020300c5000484401c80011036140400036107040c0d40e0014050f02100f2a004444000710785d0000c8100c4070f900907032003244c075100c0090002c1d00045005002510541030b040c030b01003a001204404680c10310005100344900e00480d00e08080695030140c600181403869800c0620540c001d02540d401100d1031b4500300042d8a4042d00070740e008017015201481c4580321b03c0c0c2c4001450094a0b8520b601d103840c0ca004102081c440c0e0080c0803590b00900507031a00c16180c40d0720f4100103001c00b220640345410f400c01001003001c1d4420307071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 815387769 1250 815386519 815386531
    0x20a0b041a1605091c020d060c0e010509033f04090612080d050403120222050d081801030b090c0306130506010f0507060608030c0d03061d061909180b 66
    0x14030002250b803074000d8028000c81008078090403008000351908580701401680c1d49400410803021035a10340382510140505600400000d01c1010700042c441d40200142d600c401d10090240c03000c924002d4400e1341c4a65100410020000329003406404400c0306900c0f000340e03040c1078501d80e58450070070130341005440036503008000381501c0da110300010982440a4a4003015600c8001c42c030394070f540c1000c407a1510303401c0201c1c118500c005114668004030380488003221031124001d0951035582c1041007110260840c019050303136400c00c151000e002491260300300030b0300c050400241402901000c103081000840700342d8008000041805a203141801207040c00f50000d55061040b4501b0700c00090801046422040a000010484a041000030303003020f400f40c25128100c98580c0d09041a1550318102d00a050300407038a4400c3c0803881c90712a114007111000c4481e50303242143c0300c3c0b00c01e04c942a56080100005900c0307014000c5a0840103004803030020040a0a0b224514014202640c11402c06402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 815389019 1250 815387769 815387791
    0x70503070b0609070806240c1e07030302030723012909010513020706140405011506050a0e011b05120301050a08070f0e040309120c09140603060a0b01020a0b041a 71
    0x201302409074441c440035403140041d2030707650754844812070078414001c040c804040d07031000200c3d0309985001300056124510100e5130200501980307440e246912001103000107401a00200322103001f1401a07100c1d031160460700c0052025a460654085085030b940d1401c030010340c1040320050404c54541d4090344503d100403a420045075240c00b00296031100c00d8582d9144041e004036010050014a40c480d001d045040041e100c610319191408034005e080300c0301c44c8040c0b400300903008911144180e040c4c0d00920401d84400c42244090001501c24243c0b00180e0030021a40344448400a80d051115640b040290000b8980303e5040c8010050314400d182c2201100e940540c0d01045401d0030b2050a404590f440050001170381c80b00c6c10103d03203202141e00081c08816044010b0000c0101e001481012155002001c0202203902180308a0307080c01551030b664140c0c40b047c007059080c0110360100d580c1c1d1070140101c520301c08541d85d50ba0a006800c480c15180c1c562000096142c404901d01c0c25540b1618501c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 815390269 1250 815389019 815389021
    0x13030b1e07021606231209070b18010309080d1b03051530060f070e01320c0712060b19171f091a070c020904080f070503070b0609 57
    0x1071a031803a0342907445000200061703d9504a02c01c400c001102120394207035034085540364080012428508000d5401c5145da1241550008030004008d05903101d90139110801110080781c000114040d0020110503a0206020884203203035810724400c4504429000d001410700010500002e4120f50000300000c91365030f0a50248646640c40120408403506d030002e00d5042c5200b180000c00700e16454042116441c4104400d00400318692214680f10300c03070303d540e40040c220059004440c5410000d80251244209031901c10002c4a00d039446140b03c810b00c0581d81c00c0c101d213100964944692544800c8506038070051000921036503004410315400141d0321800300c140080c1c68126004041d1040d654030041c1180c90b044800010f010b11510402d2206072125000103028000d801001401d000712801a9001c464180d16200b9448072407041105407980c1051746c00e1030702413082c00c9400400c201c61000c010459007102100345070140a40030f004178021a10b0740f210385000d24841c1c00c007814013482031903030740 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 815391519 1250 815390269 815390293
    0x50405010c03050f0705011e15030b010b030402130c031d0102030103030219060e0303040602181212180d0b04030f02072403020d0504241406040213030b1e0702 70
    0x106488103107075494500300f962650303070444160450049020080807542400b010031030b25401044403580300c0354132032010086c40801d25541114096548401072004120400400024490704050741c0d1250001d080c2c5826628903003040700858501d00b01000c08a6a28488400803c9282e0703034007108240350900841c55541140c40180d03a944680b1440760440161003544810812a500a0001c0b02c046100b1280c8a04091410f038001e9044032060018503005101e8031405131030301c3c0d414256000f03080c10203040d001410130703c90f006503405182150b0015600c04d003d20390741d4890841100205008255000d0f40f0b040c107107001841048103c018078110350101c0c2080c0403902a800072042d030381100740308600590342c0c00ca40a83c083d0080c91000030300185004104400d03c4a044801d9124a03e08180b50b28000754001e04a000c50384040101c00c5000b181d500010150306181d80100704515104030702c594403da0305d564100c0700c0c4100b00c502e8803407003e51003c001c3c800407541d00c160360002e4250014198100c025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 815392769 1250 815391519 815391527
    0x71b14010b01052701110313060305090c01091e050d1214072a03060e0a1403040605040e040f021507020102010f0b0105120c13031a2d04020a05180a0c05040501 70
    0xb10b9a21010340e10010590138032603000302081c2041c00340c00c9080d60303224140345001c0c10054080c6d116a1000c070341801c00203441c028021440c80707032080c81611408052420821030310100b03c3c85a0340440d09000d41d8801207202d40d900c812204016114260b1503000d510007000050103401c089203403154007801808000000341c18601c2030344d080c0340e82090429044401c0700100d14045019403000d0a180d241c0645215025404030705411580d0003104038903046454141c51655078803640c82094000340c000c1c00103201400140c41029046409096004614691600000c6d44c004903901c191120b414001683c00441d46c081c01089540c48445130104590400c410001e4403038030864544d2407000c043c440c0051030751925001901c15040300d90300403000700741c2c40c0e01e40109000703c1c1030501d116009920380082c01c0e40700582412812001100354070b4040a91000303d0b20303c00080079000300da00510b01d4038003050603110b614840d007100044640b5618a0708040030346504448802c8886010017404102c107000741d03600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 815394019 1250 815392769 815392807
    0x2070b01031514070e04020f031f05030708150606121609210602072a2d18060b03070c0b07030b091801090b0a050f0702010603030c0803071b14010b0105 67
    0x1090034045ea281003a50000340c002d21501120000b0b80d0000300601401841d0b0640d188000019903e0f003c3c2c049490724100342c0e454000c1d00c140c0216901401542060325000030f8183c1d0451005050581000702d51060b1504001044a034095583d0707a020750200c8030380e4000388030802000902e01242c0c130b0f11480004500140001e420140c2030315000200b40d42080384810703001001c5038505030010a0605401c03525801102c42c3d100d0300350020000c520344030400d4071314120304000d204200c02c0208203c0c900300d21141ca1015200601c6421555282c00040880c01d0400a502c01c0c04107545045140646161040303041c0000317803001d82050703c1c00f000c510803601c0320605660488090324140d0309a840315550180580380c1031700300415000c0507100380308030b0740c0540d0046401229079030070b020b041ea034500300100d080725480d220140001d40e04034401004500c01c18001c6802101d07901c3e01c0040b42c4074040701071014001701503046551501c035a4a030071014900f8070034141592400d180c5103141c030022803d14281c00700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 815395269 1250 815394019 815394031
    0xf06171b0d0903110a030518040605090402010f140d020310080109171804140f0117060c0307050f1605010f020a090504020c0a0f1a01050607031d0307080102070b01031514 75
    0x10b626121801810300480303202410030b4012088a50b4034203540b500a1045e00700719070b0b0f050301c400901d805001c02d18050084400381e90000c0e04003011681e030346e00116098140700c5141380c00c0c04411030b000c1340c850003020010101456412009a560700b0413201c08103500c0c03440c0e442400107915010004000400114034002000d144c030100a03104c000b8100d40181c8040424140d0b644240b810700081c0d00e4100b102c1001e80f0418210340c500d6501d0380c0c0c440c00740f68904494409075582e6004040060780180911011f1900b22240e40b804905110450004940592010740030708880d50201680301e08001090160107121110400298202981e03094054101d44190046902c600d40200340b80040c3c0408006a0140d1904400109903600550421a036100701c86051110b4280c4081d0000c281424400d08847c01c565141d610b80502c50700440150426004c869802c03503042c024800001a20702003400548403150080b0910034080d45035182c03089901501c4030320340c12010b08008481000c0d20001d10141e034042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 815396519 1250 815395269 815395271
    0xe0d03111c0609060f0314030903070603050901021207051c02040b0a030f09050a0b0f06061908070915050c011a0105220306090c090b18150a0f06171b0d 67
    0xc01c000008024298580280304441d141c0440050070b4203029040504490284c49410f40441013500350f1074480c403405e800540c06602c512400c000491007079010aa00205000006040c09000c0e088461401c0003a00d81800240010170150042940440c00090a04142c0c41c00c524151030580d02041a00681100006040d92a61403142c00307209500403008030342e440070540d80c54400c41d00c1c080c0307040102031701c6000405160318005407041c2000e1080780c1c0c65030000b951958818044d100d08980361003000b004481040407414000030706c04040c00808028002e50f403110344e2a81070070b050782800c460707c4c03004411001c800001001c1c002d1342c110003281c242440740d2080035207004144d40300c200b404005034001480d4a01d009500c505010104002c0420350b9202181440190f05450802002d405091002d031003020501c000f24624914001d100200b0000c00313004402442c1d5100f81c500026902c503880240850655440f1092070300480ba01380790702c4020400300c0010700e8040505080703a03008400e103902a803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 815397769 1250 815396519 815396557
    0x40b010e10020f0105090d090b0403080403060908090a06050307031503020904030c05070b031005011205040209180a06050a0e07051212090d02061305030709021612140301090e0d0311 80
    0x1030780300f80003e8200d004110001c0c4128103200320815610b4945a00000014003580d038007086214101088904594010706003d080c5030650302d07800000c0400900495620000304180b000d2074035400d200b80c004220a449240e00c0b4542654050b041c0c4c1c519546030403e103c0780703c0d01400142c3c0c2c1ca048050708243c140c0b0340100102c2c07151070300700e2600005810000c80458080200300307441064070b0003a0143c039001e0340c40e2200440307070501820603200291402540044c40400090400b8440c21481080740c0c0f074882120a0481d564403030200300c1e00d0640b0303c000c0b03042e184c4464403804001004000000c000a586161040d2030140e10795403030b189404c800032811000081e202190381d881d6190141d41c02d03002440f40b40d8562581884000020070f44c400c0364040d000d040c81c0010703208801e109a039503003880b446441c60101da003940e48281e83d100000a803814071141060103158510032001650280c04920000109070b20ba07031b9480c5140c00302e240785d40360400d420070003100c0c0748403c2d2030306407503008603000c82e000c000f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 815399019 1250 815397769 815397799
    0x1080f07230d09110132252405070c060b0f0a030303020324011e03110c03030703060807081b13090f150515040b013b03070b03070c1a0c090906040b010e 67
    0x940400e86003040e8002028002e0482030191038008402000a07940d5002c00308c4c0301030541c60040c1c0300120b5950010940b143c030000c0104446812142030080b004000c1c0350400811000511072980702d400030b4000a0340882000071030400400107404049214800d400c0054120000078907101d10503400c243d10080c848000c40c000c3d806600007620450901da412510740c80301c001d249560341c00459183d40003d0030108001070b040c0340030503080207486220000d01010594900150004110a580b0310380100c01d071a10300c54114510310884000ca8401c01010103000302074181240304403070ba0101441040d150a050181850881c030150b1481c030b03815100402c1c0d100c18440140c81d42d01014010650810008120240822703080030030301c885110b02c010003100b440201d828103503600102c1c058000341131300410114406900a01c4010301e25882032040500d22000ba0298540c44041510504021400810002a00e2502060701039011409460400451280741300080c580c0d001d24459500455403480611a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 815400269 1250 815399019 815399047
    0x306040f1b240f050a03021804050403032319050a2009030115260708010606020304060f030524030a0b1501080f07230d09110132 57
    0x30054072003081006009070358882014a040d40c03048042d42110414404481c0140902c00c000540c08031540c0e41420440c40d41d10030f90003588003415460002d1604018030015907654058075218504c40d6501140d204880d07a0403091600120041c506004091403c1009100304c080c3c000050616001c070104880e01e8042d4a5001005984890fa504001c42040c440000c0c40000041c0b040c05401e40080000809001003e041c0303078114000d9900403032810b005c0c42004801a4040d440c005032160035201025521031090313007180e495501c86409608082820002d8513086114040180020300f01070003546458006041044506890b81c0e905203064031444c000350300e04000c46c820b481e511a001051500f8821a0305510302d48440495000482031000540a1481424500d0084410342c0f200d420300d9007035071204100815820101082c0500600c000010121140180e00b1401c0c0510300300d40a0100040004102c0c02c40d40c2080b64010041088040c60084510005001e54440c003120701d0716105100e501a13 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 815401519 1250 815400269 815400293
    0xd05070c080607081f031a150901080a0b060907051b0309190314030c0607110a0206030a0b0907020708030a031805010204060f0e040b0135091018020306040f 69
    0x28810b0b100300401c01110541100949004200120b144560000f038881038890303240d00c41c00018540c0002d100301c058083c12800c889504001d08002d222056803016010882c20802680100362941c40a03201c04140603c1e000960b0700480d06030f0b0b5100091030440f9015041d84640c4122180c04550201003410b051001e005032848060006c0122845207130481e51101009040e010a895900c0c1e10303131701d0380881c010000480e5400070142d0701030300f62a503848405860704501c642541c4524082c00c68400016603a00c030003076105280080d00080c5142d850390030f105031110000c01c02c106642c090141030000d03200000035124003c0c1d00b0f103004109414081c0c8001040c1c10301e540018010f42c004113010070515081070038900a12410355403000504204820070094909002480307012525640340030202149084001b0b08584807030824001c4200288070602e808503003125400b10342d4100700410207140b5081d0040c0708003824960070000269040e03400081d01d90310040c100800030070981c02030000308000c4141032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 815402769 1250 815401519 815401529
    0x30b10090204060c020306090705150d020c1501150e09011e080f010207050d230c0109050703030926030405010e15030a090204050a05070207050f12010603080a200d05070c 75
    0x1e40d1559039600000d041040d540c20124420300400c8001a290440000d05100301d0360001c0194200c20420109e403182540844810440360340c08000e0b00300518401c02c00d00c95115105819604c2961400e20010203000072181c0e4a400c1060109400b40c00e960f910821a040d24400d0b078215420340c44c0502c1c5203c080f48654082c82c0b0501410100d01184034040d0b02905010b8020b00036162121011032003250020000c03603624040c1d5031495003000101c0c41032400762006012180001401081c1620b46910f8030308980c0c01200010141079040c8554074800740c180807030b803031074151201002c4081032180c1d449019030f01803e0304010f2005040d800940c1c5501074082c0c0030418445555890034515092000341000c0d43c420780c080c905007804509801c1261003000e02c106080d5028003e01810b020801200c2444503440356841040c0d88140c0e00010020300c1100021441201515030740c4c41400710140140d400f405010400c494802001c87c03400d003012810300050000c5241083c0d4903851464000300034188c039044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 815404019 1250 815402769 815402771
    0x7030f090516030303060605030403050f0703090e10030203010b0402070809090c090a080c0103231b0c03120a050f040c0b07230307050f19060b0609030109290c04030b1009 75
    0x9120b001402030300d2603400e407030003590140405515000290b03042e120584000740000c10800041001014480151211501c40d191000a442ea600c022912000c000e0390090384400c0c80c00c42c10011450300740300d580250078003a40e0075420000e094a411006000b013201d618003844c0040001001007001c18100c65003040e006050002164644c0c8416640d500d5204400b0701082c90080c814041e00c06800c0d0350182004d104402c10200ea0724141d4090904d007890135000394101c803c4c00281d000c07010500241034203070760180d071003000c81c40e0000040302030758005070198036071911250921011030500302d0341c0c405607000d007400070707981b030446180000c11003081ca0036601c00038480100c1d415401ca000710003405c200c1c3c010b008403034800200082645d141c0c4c0c980c12440c000d0000e4607440e400010070f02d421803117500710010702490a148042010a081d6811480d0031600c0641c42e141d06201c40c0f80d03001e00b000b01c020309406400100c1c54500340412291065010107415201e08130b0000d1080900c84074030300c0c050480400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 815405269 1250 815404019 815404033
    0x30102030903190e0907030e070b0f0c060606030f060d0524040b0603060106050a0f110114010e0c090901091a03010c11120c060a020901020f07060909060602030a0807030f0905 77
    0x1a40036243c0c0c1011103c400f5141c54003940310307400b81c861485030000b20741c0184104a251500c1406038003e001c070803203803481d60007a840c0000c3c044c100e00c006400e011207016007603552440b00c2c00c08582803c00c000d10b410300c50041407003400100c2016a00c0e80b03502c442e0070b45032510b00c8000c40c02c1c018a480d40c402c00346100c0c00020140c18029101248204d0b0007244121080f007101c0c2c507440704042d1101024011000000c0003400f210100f03511450080400b84141d051100244098203902030954400381100d10846104800400c201c030111024242e218886503a40350802410701c0014100c14418803a07001440d0301d5008000d101c4030841400407291400a00030400c6024604024080d580304d90220010380c00f404100d2030a00d01d5610440301a891110090b1007160340385581c08000f900903402540c111722514a100003c3c00c030400c50500a05055105c50481501c0d202104080c3c548540042d0308540042c4800da503000d03000b121240c3c118200b07040100e120a0b204403480002e120100d405002032250413 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 815406519 1250 815405269 815405281
    0x60606030606021f092607120509030c0f0d0b01030b06030607050406050f0f0c150403081003030917010603050d03020702032b0305040203161d100501320c010c1107140411040503010203 81
    0x7001001d04500c580140c8c04000c2aa5809481500070180015003503000507001005910b41200c000c035106034000c0407102c0c0068551220700740144260401c958000c00d031824403404d8a01000740c95840035552030018a041d0030104020004d0058a003000c085400206455610b0800360050311019070b100b0046800344150004148190780c0d0503a0181d0105003003070040780c00c83c2003140881064030b070191901ca0034189801d20405440d180c0081902a956840e4000310005100b80419481300c01240c2c0c2c096103a030030301d004142c240340f100c400000503400702c076101c944452201010005001c085080020300f40e42d030307800845d042404444c04183d80c40885000441d00f04006c03204c0c1701c407030405100d04032040d0340c441c16084c400701c09034054540803480b003598400e00c0e90100b41d5031400845903010380356100e86804843c410650800301c001c000a945030144240881c0c0c0c8540140c24001900c0000c01c1d0452070a088036480d122090305850003162500b420300b10003a01c140c1140d00910001e4002c554078940300e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 815407769 1250 815406519 815406593
    0xd09050a02090f06031b0607020a030b07020c0d0c09021c0c030906051b070f03020313030f1b0f0b070611160512070809010e01030b0d060606030606021f09 68
    0x200000300e102d0150700300801d079008807000743c1d14811032000d402040c4101407464030100324a05550720750361045042081381d005845003803c0e500114883c00400d0000d003000c60001e8240318040360b115010340c40c040750310b1b0041086100c0d244110340c0c2144005940c0c401c403610101e01000392030304000015040c03003003200306954550b000420b11802040308000031f0301e540503402290580100006682e001c1070012070b01180302c100008031210303ca80103c030b00d002000101800c000019610503a8841040d805c40420300150b05103450250400c41d10011f070a6051122181c025001d9000e170383e40c800c2c03012502104005040d44040004001c5030350302500c583c800300305d0a803000c903410750484150044103006028005590180c0310f4031940845120f05200703000004403284000b042d41541015244c141001c0e290b290340245a15003070003258080b85003401c03c40064250740c2c550380728008540c0a9a400d42840c9919126440b401038103c0c00450045100d041c240024243c100358101700c0e051403001f50700c0740300b11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 815409019 1250 815407769 815407783
    0x90a0c170c12030306060f041203030b13020304240f020c0d030b01020307030804021e0d1a0601020f19051606020706031506170702070b0d051f030203030d02030c0d0905 74
    0x50500300d480d401c850006001c603414441540916560090020840c0741c50900081c1101c9440b250350303e42819526151441e6298110300c1c20b502103941c1e460f042d403617030920f807400c914450841c000c25072075400d065032080c1000142c8206400111501d000780c82c00464940c12041031225601419521440100e10380741d1910014800080841d15150103110994004401d40350002c0c0c0503140d6030703081c1d902c5400303105049240f40500d88039000c061800d8609030b40c034003100d0301055000b0b02850840d150817100d5004540c501034201415035204010106028200140d40c1000006141401610b520306191540c9000c8004940d0088080d51400c045112580001c46a04840c05a0b40921001c0051200e20320311182c0360241c1d100003001d004906148151681c01540c20580070310458440c1965080217101a40080146003020368076002407200d24000b20708a44004030300540c520000d03501d9a80003075900d1056070703150a03c0580200003c1c1d06000b2800644010060030031060182e84194034006841e114 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 815410269 1250 815409019 815409059
    0x2006090a060206180a030503010e06010e090405031e03150d0203210d0c1409041e05100f08060702030a08180706050d182a0b0c07080f011a09090a0c 65
    0x10504075004000c4c0c10000d020a02035804d81c4a85103940d0805112003038a0300003c10950500401030118660b40c1c48010102d44101d003d240555113601c0708401186a000c0301c41e010742d414050501c00d201050928000b011203071241141c020211280c02d1010a0818542c0e026000b045204a03103134100c581b00e560000c141061800b00100b00081d00d0443c19038801d1400a01c40f0b002200c1803040e040301c1e08160340f1000d500095445200b0b00c2d5031459000c241030705c80841e40c2e003600f144140c4003048071144901d41c2c074028003c005e01903c400d10700a03100a40d40c0c001d80c3e903010b00b0801460041441c0b110605d040762075a502c42c074184d0380c0c8562a450040e110398010303501148254a401ca9900405454050b11030415a201c171030010b204c010201c00b803070f03d28011403841c401160840da000844098050003092a841440050047d4918013002d860414004d031420500d940d05100109050345079078809247d200744121440340103030b101d90070a20303d06007030f0b140e008144500c00360010a016107400340120f0029 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 815411519 1250 815410269 815410291
    0x608100209191d070c2102070b030606030a150b04030f02090108010506030607120f15050103140411040903030b030610090c02070612180206040f0504060f032006090a060206 76
    0x1801035240150400e2440303040207540703030200c0885030f104561000540041c041d10f170003c03c1a020352615091034444440d80013080710303044c22103400c0316014400940102040c03510390341549052000705040f440010a21244c2540c1c5100c0076a00c0da401c180040003404682c0c500c2c0e0340f80da0316490441e004d40b40c00750f03040e031290829a00005604005008051040384040c3c0502000c1d19849805d03501080b00300c6c0c030305840c1c944480405200e23030781c44d20075001c00504480040500924002c0050215a0781c0301d40611031204d800c04204c0440c0e40100402401001075034005002a01800c08800400f288200c550341800b0f0f603001e2002c4e031043d80304007005440b1800d0040020310b94000d026a40d982142c0f0589002c00c0100649617090001c035841118400d4021410348031703054440d4006003040d40a50010049000c9580092000f0300341840399030f028003031020701101e40600f1510f4280f9400b484180704440340200c081e21401ca91542c130140c40c0500700c046c20382c8423602d45981029490f41011244200b80b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 815412769 1250 815411519 815411539
    0x41a031b03040809011101061502061b121b040906031514010513051005060a051b0714090a090209092b0c3809010b01031116060608100209 61
    0xd8040c4104880c09240d001c0e041c0d0345020485801910035042c1038050007099569000300240301035400d030722108146455800303010300d80343c20b0454060745002a90914101c80043c0045c124494040c85440c0e0080700c800f11a07480c2042c1c84000d01c40b1441643c010913006420140c0010070420f0f102100c3c3d00444c80100306104d100b5442c0404007002809100d40360344a040d01107031040340d0320640d02454104402c54030541c0310302d440314003107199644800c0c162000110300185103d141600404045074052172034000e46142450720f440702c10a14a0f01078410700c120141400f040a10401e0303030100450660282200115141006e0400d490b0060922030716010300400c0030142030748032162407101e0909003036100d41e441d03801c0d02d44030260f42101540c210300e83c186000c202c2c2820200316209034460b03031f401115601003501d0b21004150943e816420701a0506007810644820b800c01a81a2004070000c0d00c40b100662007070781458405825a0b0744500c0c21400307101c4401544a041c0d4008202448041d40c10002c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 815414019 1250 815412769 815412811
    0xf0706030203061c0c090b03120a020a0b09070f05040c110601030c170307080d15030812180a0222020f040b0301050913050309010305130218041b0b120705041a03 71
    0x13a0403030103d0040201801c004140b0842c002c1c0d84c8958001100a8101d03648444034400c07145460780600507190246e07105030640c008204082c602140e00440402c0509941498100f550028803518041c0c0c80c8602d4607640c50903034491041c503012030254007000844030103503501d080502c0c9044c5c09024810034000c0032441c3d055001e50000403545170030341c0002d80e145440c901004400040030302e862a20411520154004049242030010300f4a4003600c0c3c141c040070342040e100000b1780d128440540d400300e40000740c0705009651000c0401d590011040c0e1101e881540c40300b07e0310000c0c80f508000d152103210110300428a1920b84002d10705075581954507041f2a10b410341044640414043c00070300a52082100c40007651103074000740c1d0014800c40c1000410906540002c80440640410044406440080206100c160900c1000080c03640150071281402d0800c3d007211031081e55002e0030038a1248001c1041030348940f04440040c810a0403d0a45c10a140f04020003540b09a40901481c54142c1040c05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 815415269 1250 815414019 815414059
    0x180907090204120f1a04060b0405100e18071806170105060a12030c021f0f030b012c090412030c020d0f0804110909030c1603020a12050f070603020306 66
    0x155814a00e1107602003c0940d241c10910407100011180002220030301032a00e80c01082e0719010b14400c020105440d428241400111000113196414100309035404000243c2c9141c4003d0b0080c3c1c015014468000542441a1034000a42e101221080c40300790101e0300328005501480994881c80e000c00406480c582105082c2c41058900c5c03071780f14040c14001c0040c0900d0300c1d06440010b1082c01c01071809081c680010b20401e213810100418203803255403503844560320402c0359004070007500b070420100171004c0000705004035025030780c1868005941d410701610f00741e042040c5890401021301d8203500e070501d01820010317001c079941e9012074100310060041134000b049111100d001a91030081c0d881c40c0307501c00c4079a038170042c0c0140e6034036960b00d0074019191511060584100341220055988900fa044850310300030300e400000214201c081000d000594414405004444034001817140651013400c2840c10148034419404c6180700e00c01002403520b416401071445200304840c1403a20f00ca1110680d9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 815416519 1250 815415269 815415277
    0xa0e01050a090c15020c0a0b190c032a0f32030f030a0905010c08070210020702030c01030c120207050c154003300804061107021809070902 61
    0x501c400900e210a001080201c0305002001c04c03988100c2d943c29820360040b8000032000c2d0803d003601000014051003806d1181c5a03074440300c60906e424407016180c1c0e1802042540032500340003080c20f0f00080401c48204044610503401e81200f11a041c500b0310346040043c055041440040202140c01c014900301c1000341c2c0c2c401e000012102071880c051103400030b0907040e03100605040d419a918000c0c080404d5092040c501050004d4858440908019001913b0326610150200340f95004006582c016100482d110940c01070a0901050340845500700b95040380c08204000c884034400300700442400400900361800700400d90700300409075201e4090000920482c2010b1141e012917141143c1016034064650400f000c0003c1c070000d403951420008022070710a0390007a00d0203000d051000658036110014a000242425404861000310080c050b11902000b080900559595895808081810302c01c4030314231580245281d80a182d500030044a08500343d403807921034400c101c8003103100c0310172b44211 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 815417769 1250 815416519 815416523
    0x20f0702030607080f220807030f080c04030213020d09150902011715010c050f0706020105010503010e070e0c031009090b0403080a0c09030212120f030124050711040e060a0e01050a09 80
    0xc3c42e03550703005900030b582a00345800143c1b8400c0c0c88001d0300800d0f801030103009a10b201c3d5a6080211f0b50102c0300821508016005d045034150401c000c200598072441b00311054071071400701588802c02074048400900e001c0402501801c00400112034400c1c896110a0040b8800d888250000d179407202041240981160b5400c00391000b004915041c0d80110000e807a414896421225880000d40c81d44d82015841d50044015079125001803166250a000d03401c41d1210701001030800500d0a4030355020250080e0410100110000205002400c806843e00c05001403403014480a0410b20b403020800004840550006800c0e00101720f048007140591403803601c040d40d80c219010b04640030030001c1071802c0d0600c0f10501c01c5550f0f81c0140c0001101402b090f03445420007684942c988591041980002c4520000d50080091100d440710b4012050340d1b10550807030f8003010303602c902d803000c20010280c10b600064644907400401800e846a500003a401020f494003d00c20b584941a640003511503100d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 815419019 1250 815417769 815417791
    0x510081c03180b0a09060e10060608090c0907200a1110170a020c0a0b25090602030a05030403050c100c030b0f0a150c1205030106090b0306150c10020f070203060708 72
    0xc103284c060760303070071400b841341c01350500282101440d40114a86080e0011690040d500d402040100700c0c3c00580c41070340a40008090054000c0c00b10000d10b4420b4010803c41c10310540d464015885480c85800c240d036039018004a562408080c1417100254400300d4143c0c0c82106048114100d0070b1142e145e80d0080d0b2180c011030041074455048520180d0440303049000d241c806c442a9601040701c07032605901880001d60303002400303201d00070382c80c200341030500140381407060383c4a0030844258000102d441d8000d01c1e00d8034640720340742c5140403a010303c101c410146140c41034051042e001d00b00e540c04401c2020712500d08010b04041101800900804201103e03440441000304002d000200078070790074000f06625080c0841e4805503640039543c4941132903400022400310051201507041040c0c04003030030500070340c035003946000302c0001d00296170005660398210b4042a00c0008480401040d1201c00716810150340b00c29108031070801940000c08141e01c40e10a90b004980c001d8021000030740101c1003010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 815420269 1250 815419019 815419021
    0x10e0a03080a0c020402070f120807080f041406042103060b0f07170f0d050c07021e01050c01060801020d060504090308071b0c0e100806010602100510081c03180b 71
    0x11100341c19000304103030358140540c1c0904403005a03241d100410380c0d2403242d101c0988074101170409511510300c5d642060180180e10050200007074201540650100d1551002c88150391207107451040381841c0031501c02e06110746800d202c1040f240b0043c900300d030703400000c40600d101e44a40c07048043c1c55036032017100c860300000c2205a48142100b0300403c81e6a00408200c042c510303000b103403c4032036448100c80000b000030209898900325101d00070150060340311a012030404c182a00003610006420200f0032035200c102d240d00703c0c1640268107807000100007400820400346d0f80c061840c040e510180c1242843c0d4a03110012625150510440c10b8407600b590703480c0415594030708180c07040b511074200302807442505008040002d94000004014100130b0703903424541d091031841c40032103007220340114403d908040018000d290780050040d002e400d0070b0401048a8171562079105035480107801801d214049e1070f450300d22041c4000b505030455a1255401c01640c881d050040d81e600b00702010040003407060b04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 815421519 1250 815420269 815420273
    0x60403080c0c0303070f0512070215160204060f0602160303050a1103070210030f05060405092a04060f030212031e25200604030b0a2406081005010e0a03 67
    0x41d0640200050841d0180c2c64a000000c2c5140c000e501c0840b5040c001c91001020000e040c0b0460062800301d481c1541010303001c0c4e001803100d08800084016486d00441e075000c694013041d008c0180c01e500548100b08450710b5500c0203015003030030b01401d0058490381c000c0d142d80d211002d50100807a909940c5690600c060400c08a8650015602d1030050f4032041c040000540e54501d02b03068220382c59100080c8201c10500982c05841c802040903100302d10f003104000014a011549070301840150b0481c4c2404003551210010160000d0041034005291500201c1d0450703071400c000081d13900031100801103896810319030707590f445020648410107591750007a42da10b070310744005002607540880c28401c440c800c07060718032068103540314240d45c0032070036035500902c52607043c1217184000d8094818502e083c0c01d40d00d0340c0c0c0d08000003400340700c0281d0b550014901d41d0240c581c0c010480f48501206110f1055a03144020412041a1b80500c00d813881c1e59000a03066010318031005d002040500503041c1d9038615 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 815422769 1250 815421519 815421533
    0xd060b1e1e18060d060641060d02040e0c0c010b0a03031b020607140c01090819140307020a12030e0907022a120f15040b0103060f2a031505060403 64
    0xa40f803035400c140c901d040341001130114041c3d0340140050702c00d00702d84c0c0d808211403602c150300791020140703081da01a684d01201e803032003910310b5a280c0001c2c1c0c1d10998901e00c0800c804024800e44c2e21507004901520300b80800820200300070494100220002c0c804401c4010400120040b1444024082054440c80c50800380300c0c6004101601d000814040c00d242094544407100e420350303000e1400a40104c40d03034040c950b80200c121800b41c1800f40040c54031104622001c00211085c40d00a0310081c0f1203441a008020100101c501e116170240488810030780c8d541c1c03031041c0500c540d42d00300c0c08940048080a21402e1406080c1e1084000ea4024404030002402083c0ca0b00c0113428803500411403030302889055101e08103808900c0000340018a0403c04c8000394508140581381e4071000701c1410b01c18000856000d145140c15250411000201090295042c034002e00680030034203c8140000003200f102e03c03188003420481078807030300c0a002410810740c1403031602503070380a20369000308144000c0c404a00e030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 815424019 1250 815422769 815422771
    0x10302160312110a020f0d031a0d15020a020303100902030c03010509130c0f1805070804080a170103060218010c031b0309030213020c0f1b0d060b1e1e18 67
    0x2c40c0000610006048580b40c00d0364081c8070344402592107813030f50310010102000104010703805480c0421024942800010903909e03070004940c4151080540791051049003100b9800ca101c4200d070031980c6840010002e5181c1e0802c680c290110448000d0005d030100c1c1310300840b489850b1000d0034528581c06d1004102d440da03800b03003000101d01050f030044000100180211000f40546040d8035036850328103156600c0b52031582d980600054144000d01180780d41104000c0d40166108140b19220084c103002150b40050424103075004610344000001030012650080201d01c02c60442c105440d84850019035460640c0c07580140040c14004005050340207a41c510009180320385003a640441d520380001c0c90b02030032400701070302075940083d910440a5081041c14200300c048409003440b641c080c881800c100140c0030310903016040845140080161980c42100c0141c4020810b240040c500c000c1c1c29125410748030142d0140c0420301b82080750080c4035000b12a2580d00410350f48400505401d5210b841070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 815425269 1250 815424019 815424047
    0x216031d0301060e090c04091e171801140a021218030f0114090d090306201c05100b07020409020a030b090a0308070903152c010b040b0103021603 64
    0x16011020351210354080c0607080003090740c4100103c072400c0c1844401d090a90329004144920b241884400024128103d00c8800b42c28020700c0d0030145000c0d08245401d0100364a50402d40303800011068282c0309612404040c003803007070380e80500000481c08070002901c1022045000f5074440c0355000ca14580210007001400a507403400d0f802c0044c0c1a001c2072a1504145a044150751150b440880030050b034003c06a1150720000100300001d128480644094100c0c00040d024a0f12621242441c1c8640402e90480e072481e88802669442118882c50b00c0c4008050103000441c2080302048138404213001d000c081c2c41d01c1074201842c2c110307294204001851b0751030b000c07030704600da000d0300001003031258a03860710802005000d008001c41c0c2e854020a1400020300c040148a4409400d20100d92030340d4100010052200c03001940100d0400955003041001c40380c40005c0c98803410700580440c041d00006c1c14030750159014402d278445c0f50010340c26409145c0755a000d81c568401464023080c411615007103e11 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 815426519 1250 815425269 815425307
    0x606040923330f10050d1a071404090b04090c0b04080607080f06010e03010902060f12060a050d150f060906051305090601170c0603040302010c0f03021603 68
    0x9400d444070001c0c25545102880c0075a000842c1182010700858180341c200b602c030548140200805241c2101103400c0038142d4114648140e0000b4084050f4441c1200079000040184450348914034014124034000d28080d800c564a00c4c011860450040304003404452059030303030500700f60411030150018052030300029405621009400b0205c0c0c0c00d1543da502500184040c03503034540c00c0c070690915042010342285c082000c2e410030006d16501000b40107400ca4000d1801c2c00141d460000060301401401601039400140081c5905240440c1401000c3c00d00da004810040f0b5030300d0030200600182a48200c44c1c110321103000b840001101100a18a01460580c001070001c0e0744040c040122200c680080451a130b888000380410700d003030f00341c8110000000009000a14048141c540c64082c1031013003a81811515410664a403020301080b08403540c0a402951280f91a0030000d029003072180b008000300d26001c3c1c0c110b4449104e40220780001c034071481c002201c91440e540c1151020044140e2903140303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 815427769 1250 815426519 815426543
    0x1050306012d080d110f070905061f05090f01020105010e06040e030c1b09010905130809030a0209041b3606170109020a050607020f04020702010c0b130c090c0206060409 74
    0x1035004464020701806203c03000b0180d204400b50041c15440210780500402da200c2c201440210400041100c150346604001080700d840d07650104031036503120120890001003400004029a900c040a0082c2c0542100c040c8000c410301d90040e400c07030340280207941c4030030070b218000f4030341c5e09258010180021107202100d181c083c2e02c0618030305118140c05040070302440b000e184030281c640300300041e01401ca00842004141050240300401a0413150000d08604001c282c00c00f10796001e0105590a90700546200c01501c1c00c1d2406552806e48054000707a240d4002d60003052812201ca22084120303200c0500b07011080030f00d99051140d00609039640309042e191100415020914100c03201c80910400020036200020b01c100030000c4019040180100b209000720701c0581d03565200d103000c40405a90050303481d0b4181c00100c81403039421401619030130080c02030140e40700d0300d2806022054040d2000040f0340381c40718290015030300d50b05a80070041c3c1c00344010032034034078041d03009000840c072074002c255403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 815429019 1250 815427769 815427839
    0x2011e0b010c110a150909141512030c12130603020a02031b0c060c0f06090d1409030a0206030c0706060816030209060d02030106060e040e010e0a08030717040f06140105030601 77
    0x100c805e540d800070001501c12808000b825064020f8100e101c003412003142c031526025036440e03404291030480c2c2c0d128100c14074000e43d031604140219110720140328144c540c00703014599006015031042850310840c40b000c80c00016218841e101b034441160b1a54041c42c07500d000030f4030080007032581507075003002d9019124400342144e035110002c0074201e003550040e00940410130300041c03c1c1000104a5441c5030010b0700041c405c00e62008a6500d0715001c400540d46903910000801e2920035100802034000400005111440c0312070b401818000e07220b1f07002031042540b0341c00c0d490f40301c001040d840980710450300e0041c0010310b84480c00c1742d80710001420b12024006a50002400e442c01584040007013403111243c2c0110b0f003418091820b80d6040100280481601c81004640d00e244fe0700014228150100c00300314114411200d40306102440442c189050400d4246023801c82c12640c0b01326104d52030803a0704025212402c40150403648018082c1c2030036860000100141c150b0704159550661410160b424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 815430269 1250 815429019 815429039
    0x918060f16170a1505030106060504030b160c14030706050c04140d152c07090c081302010f0e0909010603030e090c090103020d091202011e0b010c110a 66
    0x80305921004200c2031a09145a000075495192410507040200380b0804100d030307182002c40c0c9900110701c443c000840884400900285100a411885e41542800000581154400e02401c15680101d1034aa1140c803050245290410354a0014021035a003800388800b0410751511904603440c54020b0300c6c60444641d95940490b07004441a00d000c5001007010700490010310180100742a0640b464a600ba01680395a94031144040034a03d480761a02c2520509941d00711102004031035005070740600c1c48000109903221020b5000780c214484c6007081d68141c9a102d00b618500540c6228040d0320620304070b03001199440c0300d171480c150511580c07206030b1070305882d004100c070b00c02c0f412080001010781c02d600d0014841075190302401d02c6101e0350014080d181c4000000c5030303007125003424010703911801004100c01610385100090300707014207100005100d80d0190000600c0c1545034003000d405185070509001128020b4240c1d5000401c58407000780050304030b100d0010b4003100100841d2500e5501c1c52821 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 815431519 1250 815430269 815430271
    0x30f1110030624020c1201060f0603020304051b01050a0e06040b040e010302030609010e0303070e0112091a0a020a09050118080102030106050d0c030203071d1305180c120705091806 79
    0xb540d40e001081030081d182001044280515100d0b201418010002035030303200d01c0c140b4540320b441122103201c1d0080003507002100911500c05031280a47c1c2d03400c000b070f000350000ca0302030ba4039000e030001015241030074044200380080c0584a0742d0401d0451a400c4a5102c0c3c24041283c00010420000c82e00100c0e9101510040042004017403441d81544145820200e0140021580380c0c105080103400c1c50001c0107032640100c1c03a280040400089000490f079a0500c0c00f40c407001d261504c1a00303004c0c402c503413180001180c1e070340800c10081d81700c860189080b40f00e1006c103000041c0c0c542800303103c5988201382a500c1507030309002e0074024a0300c03070000d1803ca030310030ba12010105000003400110007100e800380d44100700e0f95040c21415460a48001383c100a46405400b28401c00070159041a035a4008414410404214200b0440c606940d251140b20001c00d1010854030900a99021600e0a00080c9070800441c01c0500040791800c0c00f80f00906101802e001c01c422000f00101060702e00401c141 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 815432769 1250 815431519 815431549
    0x81e040507050301061403010e071a0a0201180b04140a0206040902090303070503040b0a08010f03020d0b191506091e060f0221030609060f0a06080925030302010c18030f11 75
    0x100061b20000c04040c2140d0700f40080d540c1b60340010008100400121210130f519580200b905541d401074120201d004208030714000d0580c441081c3c106041c08101042075100c1e5202d41c3e00f0b00744490f8640b5100c3d07501c0520030300c003c0d8030420030030061019100980141c500c00700e0160490f81042499920141035811a40007502c4080020036030f01807050340811018018101c00c552030030554259000310724500628400601100542e40200300510b5070900b034804003020b01c0804000d1841520039921000800e44100d00014980140100e0941804050a2101a0f101c0c1c8021001842d02d9400d803501c5207094072400070b41c01000f0a0ba0311044042031070902001400c10810380d40d01c0d111081207015203000c2e103414081c10140341850300f42d8580783d5038502a00e0300d07400c0400c1c1c690740e000320740c500d46484c80401c9a5014603600074080400500f00c004010342c1d10940080c048820016411110620712951401d00c84018a4040020500c210700c240d00560003100080c4d130341d01c801e001040102449401d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 815434019 1250 815432769 815432789
    0xd0b0103050609160b0f130b13090b010e0306060d080c0f0606040f090201083106060e1302090412020703080c030a02010f0e100e10110316081e04050705030106 70
    0x20018500c0050101844130880c02c5211410182000909451400351144841c0e19007000030781c4a505041c03611001005000c240c1c40103644103101c0c945e02170740d03803010f114440e01542401841c0f201c40d07000d00310407400c009014008100c3c13641e40b10100025135103542c0c01030320416020408141402414050a5041c500c11402030400d42080403c0c4002c4071303031640b0181c090525200c44400181e034002d456640100c000304600a48144104100c01a9031072501789080110603800c0c0303002084002d800400481e852001002e4455035051420703c1c00d03d4144d00020341c040351805c0042e000070032403545012204003510403588050b48950b10309905a20012810740107500c0801c00018040c0d0901071940c40d100d18001c00d201001d500748005550781203000715106032684030015041490820000e204010076110f40c240103071610003450440c40c0d8020360f40f03000c0014000b204c080e00c01c3d0003880700c54000c40c7c41c803039041048440d40400058081000d44122598042c4c10300014890341c0c2400b6075000b4100c5008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 815435269 1250 815434019 815434021
    0x607030e03011a1c0c05030a03090f060906050d0209011e020a05120301030c06120f06060801030b070c0c050f06120705130e13060504050309030a110307090b090a09080c01091a090316030e0d0b01030506 88
    0x10322600d0170402d901c10400c00de00d0700b00038000c060340001035130041d041b01600561144050001600e40c007a00e42840e401915600c01010b01159002401410150060007681e801540d01d050500c2030344024000613100c02ca14100410031103109a6034500b08504c402400070f454200c00c41800282c0d1140d904c80000034000745c0050080c0400704135842c1d04031000d410f1607401c02c151036680700c0d40c0485900c56244500c00d01c003400302c8680c0312642110340801c001e40390100a894010409001070700303c03c00c038120900c440e150105201942d16040ca000d84a840ca80700030540c0c0039500e9030090300f001441220340b0f0100b88140c504a450401440303241c1c43c40341d04005800c89a1400f410b10300840c0760302940002d410030000c0c4456450303a80c44e598002500d00c1c130100b14000c46042c008881c0c80b484404500a40c41d10320201e05010303850800c0c0e0825050311031480442e440b180c11707031a541e024501001a00c44041d03480d11000034020b000c80c01000e800039188110a00c0d0710385400d44030038000d9109556a0b00400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 815436519 1250 815435269 815435279
    0xf15031506160b06280627031103030702040e160803040e0406150b03040c06031a0d1104091e030e0d20120a050c0307120c0308180607030e03011a1c0c05030a0309 71
    0x91f54400080404100401c0807800008030f520081c00c3c2440040c043e01c007402c0729075015403001d0040314040d80c0c000e0000d00005400489060f0340d200400302c1c2007015007a0300400700d81030380080100d6040f20504250070f1400e46880d01d443e40100f9039039000315141c00c10000000740c0d00744c1000195100c2c0b8000c2e411103040a180900141c26604504412103004242070200100c0c1ea5900c411010110b4111048da801807541d800400d00030003280c90003801625a0560b0165896060000b8108681c0b1075580c018007100306109000d450800e10100410100d10b01c00c5020380300d8490701010841000090085861002d1500c2d40c0d82031010540c026a80380d0410f48803182c01c0d0804002030340042900307120441e200181a19080c0e15405180402071401000042c41c40c900d0444118009803a00010b000741c1d9254064a0301078210380580b6200c41c000c2d420011030800f202684001d00e400c80030090446000141e0092148484d8020580100c8a03503001850104282d00c0400c04640c80504c40e4681022540c10700d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 815437769 1250 815436519 815436527
    0x5040915150b071514010e040312060e010e15090a061d0114100c0204110a020d0305090318030111070b0402090901061406090f15031506160b062806 65
    0x7006007149040c0e40600822600e0060b004540995030446200e0b0641003031500e04101508035441e12150746218070001154603148950a580a103110761036a01d00c1e0402600d403a01a100c140c4541084117030400010000e245620b60550751104821a050808075052000604d81031400d840d0004007070381e101c40c20321403000c0c4000f2610120034a00d41440701980340450404014184000c001d00404805601c0c0007114068003240c002c165000f00b090241000d0020a104260003c00241c2c0040c840c1d0900c0f28045802881014003c0040c2806103107041d02c140302e03e034810364212143c10b400d90b41c0c032000e08116410900103040414403541c00303040d00d8203150040284c04c000180c01c46115900d000009c000c84c1d4040d40c1c00494242c0c1c1903600700d4035103100a000401c55040010020382204006644410340da00140003144030303045036080c80000c040da00003030100900a080d00851034441e10030f50640404c260400150740170030000c01e01140c0740594040646031882c10303515016054101c610500040d508 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 815439019 1250 815437769 815437781
    0x308130506071107140d03051309020f0306150c0703020f010917031b0d051e0409091103070602161a04080a11010f080601050313020301060510050c0d09060f050c010605040915 77
    0xc00300c42c14443d45c1c203000a0100391000001010300400142d0303140740c242c1203c0408010003084078215224196440090199442116042c1c451402d110680c100c41100f001a13440d031000800040c110942164203002a00c11030808080c107001c10108000b0341e41c030808038810305112001025544884407000030a00c4507918858a29041d00000e11041c00103510506491b522902441e001d10b44101c681d07401900c1e0310980c1c10090710503003030141c404180300000c405800100003ea0880d4401e994601d0101d86800d503900c1001c0c0a070b0500d04082188910400e060503007041021881481c0540e60300c41ca07850840340e05e5086031003d010000000156800c40f0702501100c92504000719a441c14800007007442c030005140301b0510140e503980030f00b95102544000041d01e0041c04910300c0d04030080d00500700340c2003944414000e1155803510542148191003000440341d00b0780300ca1712807103c4044241c070a6003144550f001150f5032258001007982e298001c140030035000b0204001251409103c003016951 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 815440269 1250 815439019 815439029
    0x2030d0f06031118070305040f12020c13051308030a140910150501080c0c0f061302040f0b061603020a050304090c030506032b090b04031103060f04020d0308130506071107 75
    0x100c501c0560401800c0c154072680d005c22245000a03030350380d44c1d00c1c001458a207280f07006080c041103003215804050300003031044641c0c5000c5a4010700740000184010036200101c850000001c100e442c5800000c80c1031015540001103a24081402d1210f00684035140008485010460780417801c04070241e811480750152100012100f03a4182d0300340360010300200e0020303000c680c84442c0003411407881007051111b03828004001c41600c04178100341c00f090440f0f0085903416403003a441c0c45007010f21640503104504081c3d030003801c018281004640c0d10311952071408410b6013540201c0a6060000f90180020700190840d14800185c1d03200443c0d004040300c100030001406980704031950030392289035002ca068407074810b441c4005110b107240011641c28249a03c03c00c180e0b800030031b01000308200100e100024000540c100d60b1240e64501c8038258002081c2d50107034000c143c030400750f0007084c451000d040d400201d500700e4080690b070329900d1600d0a60308a0703641d0001113941138002c00501081c003180d00200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 815441519 1250 815440269 815440279
    0xb1002060613060e06060a0201021b1c020a020a03022404080607030614030a080307050904050108010f0b0a060509130605030d020c0f0d240902121005060406210302030d0f060311 78
    0x11303090a82001d075024028002c0d51203450042050060a8800d4044035003e10b803203902c031660303021104a500e58640c0010b444250103034030744019404281c40050300d0745445800400c1e80701494036540a106892168404400781103240c9404012048103a0000300014010399005004071f241c06040202202c0c410340044005140c0344000701e03100d03503001500e421000d420442c00c41e5261100c0700d080c0c40d00e01c038107102c042c2c0141c01c05000154007001940040c0c0c01080c441408e2120411207410844121358a02480000c03500c1403103402171700d0800c41601c002600711440300092454850001030314004c030001140c0010b9200d40c42d0520541450550000000b509545c5590889603035500c0074105040a000d5081261594260010150080e04102012078010f000888170091130b150940d150102001c03806080f81c01d140101d2420700f854420f600458419400340500d49442c0e4003010510b92000e03109a085110034008100e45075400d10610745000701c0b90301e0014000d880c51070140301884400225900c15 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 815442769 1250 815441519 815441531
    0x6060304030f0807050903190b1608041b030f0f02030705030f0c0f0a030f03080a0506030d0c02010e150f130503120405011110050109020a3b040b1002060613 69
    0x1d4025804882c44402800c01980c00d95505804980b94001d4910240c0d05202d10700010401c01300f0700e0303007d45146016a00000359952041c40c031000c2650000c0794035000030040e50001d004200308000001c182e18aa41c9405402c950ba500c4e40c2e480c103c11101d003034030109005628007046160400100000b058142d020300b642c40440300015444400f4a0f0340c0901030010740c1c1208845030303074822854010f540e00050348400500e65080c000e10030041203a05600381850301011807518900000c0745003a036101075640c003400c03144035801142c0440d083c1130300b02c1d0002c1401c0b0000d440040c2241c00b505412100c003c08a480f01c0c1002d8011141e000550700071170094002d079400103440300c0d003902202e05403034003800c140d00c440da28605010f2910120705144d0b100d451603d0004100440c050700141042001e6a8408902c0400741c118403034001c84010700031a0f41414512000e07500d0700035a010700048080108001403014060011030a214003a03807110b00181c0002042200b5450428900710000000310b80401ca5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 815444019 1250 815442769 815442773
    0x9042f041d1b030106090c0201051e01030203031902010e250b070c03020609060c010905030901080702030c1b04270204061e030609080f070b0603190c140411040803070b06060304 78
    0x114102502c2d2049a03a6100014014640782504010000c101c0510200100c001d080002402800251002c40c8400c401034803103c103075140410518182d0b50020040c514180000801131f0142c0301c2c00e10907000f99501c40d2075408080805000c0b4402d07400042e408030800000740814500d142c444c40d000030110364001d1111901040c0321512810036258141ca0040c0e44a20b0f50700051050300580b082011306600381410310301000008800340400c40f000303880ba0201511120381c16a220b000d44031840d5582e80c44036620140c0a107040c10072000e0000701400018012110307031000c840680c1c00e484c00300070306010081928210300f040d2050b00000c004d1400800c03c40c10b14030459003c506010b00c8098103a94a03007070340c0c0040c4a03208044800c00d8401c2c43c81ca545d1a0b0031071801004440003290b90300c1c4a40542c01080354540d050200c4100c0b0254030005001003036003061400344c50140c0801800c0e800968a5644038034240031200100060810f03000215291072892904510800f030007001180240020304c14480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 815445269 1250 815444019 815444023
    0x50a020a06090e0a0e03041505070210030e0a030f1b3009030321050f1e191505032a1e04090f0503130905060a05030a0209042f041d 58
    0xb4010095000100385e0f4410510740d1880c1d030250740c022041707621650400c20604d50b0494000e0510910035a100b61031150031b84015400c840c10a51a0300d4180c00c0f0480c1d07500084d10a40c1002064950b030300300720010640020302503031040c8240c10304072010341040201c01560080c1d030351070f04425000f0001c920100701082d00018000f030800d100040500140e100007802c51345001d05102064481000d0412080c60200e94201d8580d400b59105000000386003100c01c1c00b44606c4c60028801d240c07203100741501401114804001780003030a801307800d460742c4503800714265030184a140b440a4400c07150380c1070381003c4440e050b1002d6030020b603a88074108071083e0869a1080400c444100c160441d0002200f40c21401c009038200d11011008203240400111a10490f03240034668090f5070102c4410001d40d602c40c024082181014044d0720743c16480740ca0700c40d0040c0b400021860740309104a00c143c84c820340b01140c00701c000325600c1c280104207952503d25030103428188140e501201d0030b1841c80c1408c5400f030b402c2603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 815446519 1250 815445269 815445271
    0xc1c02070501110304320d0b010506070201030e01090809120a030f030e10060e10061407021203071b17032d070c0e07110d020d052104050a020a06090e 66
    0x82e050240d18499104020414004e40d00202103419007a8080203070300310701407206c01d1280403041d0072090300d18888000d410720328042d50310315034010300c4c840391642010304000b4260071903c001c904050701c0d0b00c200c081403082800f40d900400d00c02c0031020f445401d2042084540b1048400b00300f15a403066660f80007080d440b800400943e4001d00700011000700703203131a10f07091100505c0c0c10003041d1f04146000078840e0703071781c122075205010041481ca42070341c440303c04a509141070b03183c800da00a0148000b80161400100406080144100300ca250800c5a40d0b8520091400020103044454407081042a9402c2d07a11091700c524101011794a01a9500013040001070035081502c100000f841030240717a1000d2100f00c074990368100c40651191542c6564030f11101100315031100002d1071502c10702c003001c9400128510401710680162814000445040f038103604140c0421911100d05c100d080c03c0d03d014004d00c00c2c0205d004501800e05888540140071158105d40c0c030003010404a00d03020401f1a203011580703 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 815447769 1250 815446519 815446529
    0xb01050a290a111516090503030f09030a0c090c030614030607030515181b07020913020109030204050106020f0f0d090611010204170a0c1d010b07061506050c1c0207 72
    0x41c0d601c407142030000300c49003207101c02c401200f4400c00311100c40600305034441502c0b400b20310a100b00e030350380e106200720345018491007401e801d54010310a0404000b0508007620041001808a5203a1451038a07000c0d04505954017030751481b40e40d180d0415207540d050140710f0192034000180000b2151070800729a0b81ca00c024a4002016655004903660b982c5400039040a44070043c06050710190172007088043c007905036402c0340d07500340707072042c1c8020032140000369104903800601e010320603540e00c03041d228514101542241000100003011005a0301c0c0d100703d81c040c01c1564014911200c18540b042d00d4454044444219580101481c2c0d514660080203101942d0b00761400710390710401810600e000e80030b40d800015020b0103100502c2d06411001541070071460162400c59000340e640c085445d42041a104040c501c05041c60040c442c5030340e5903000713082581c8140c8000030b040d10416481e0045c19159007280300001d00024041c011032204101200d0103003084000012400c4512001941e00c440300d02c58 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 815449019 1250 815447769 815447849
    0x7030905040911102d08010f06081f09091a060a182714060a020a02061302030f07060201020d0e030405240d0c05091f0e0616020d0b01050a 61
    0x50001300b071060162650700302014400c13810004500c1180510ba503041611000001d5030407000280200d900b5415504582e03060304c603a01e45031a810012070401c5881c88440303012a0350500300060411140c801c5418032401500161186810300c1c107103070301d0b542e8007a20305803043d01b540505000700410707400e42c10040c3d00051f0b07001400411800b00030106010341110002c1d41d44450080f001070202d0b45c040144200141800d07a00b40c5e80c0c901001404a02030880810016480a000902e02208a1744482e0165000804591040d01d41d10103036841e0040503000700006035000710b200340c45619240950010700d0804000303141403d0600f03000c2010400c0400148031401c6c101c09060420b440e0b034408031540c0c0100340364144411940e03040d02609682c442c0c544c0c50300441804007400c4078a504ea8500681d481c989556802e00c01180b8010440982c22051310480e1122941d054500141d4416440c02161751051a0100c040e614010800c030050711150701980c480c041c0340d10005c8510000024a8000c280d003086 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 815450269 1250 815449019 815449039
    0xf090603020d0f0603060f1103070c02042d0c0f0c0203191e03030b010e0901030b040213021318060605040f0b071109040b04020f030c03100207050c0603070507030905040911 76
    0x9420b202070320701c06106150b50392604401100380321068008440341d4142c142e0500c00030990841a090a220880d40d000008508402e518010300d055000310100b031880c901c000c44e025801315803032000c403180c9a020540d036a648240c001c0341260002c400460104840c100300e0a003408035001b2989850040304071104031148000c10200b000200c0c802810700042c159440c000c000403034134000d0000d18504d02d045000c07a4400050000c1840c2440340c0d14141c81c0e00c10710750035554640e603080c0503484001c000306406d00f603000c0c8981e455801c4880e00040081455400c00c4030030072a6854400d045540d00c0e0000400c02008003c203210f04005100380c80e0441d030740600c036a559400340d03003803042c8011020030403690701c03207418018082441403044a50740903038001c80b21b20062000341002c040c0e60310f221004813030f05a0030002421060107115809018024042c03010364030311414000000c3ca0a50048604d04c000c80c1c00400c50105169219401c94050403056504001c420200e880700ca50f1004010000c84c81144144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 815451519 1250 815450269 815450287
    0x632060f01050f2d0406020d02060606180409030c06051513050708160c0b13031206030b060f0f030a0b0f0a0506060301090b01183209040b2701060311010f09060302 72
    0x4001281031401130301e50341c899842e480025182c10f4280034500c01032243e440490140d25044e0f00b1907030200070310300c259400d024405c010310001d886400d0060702401000450700d030100d4140d0040f80e11648642e514580c0c0700b40303c03100b00501c40d1440300084184034a0002008a2242c010a0352178000d0b507500300300040c25070702a004464014011000400c8400c201040c031001005c50032004101c00e00ca84ca403104c03a001d00c28030000c1140c00503c0003502c000c0865021802504181a5111100b800940f203035400720280400b003483c01c01c0b41c040441d61010700d0342c200b10f0503040c01c0740e015802c044c0c908018481800e10078002142400180115403616540e00950407103a8050000c1c54030300a02c1c0d11150340352540c0c0340504114451b07840086c43c43c03030060381c50001c0348070581c031a11915420f0060032003200e074445071030f80e49401400030000901030001d0341029801d0311400303004107603400c00e21002048250031443d00040c1500003110a605110012010110f041d41001500c4103958407440c0058640f0806 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 815452769 1250 815451519 815451577
    0x30b040206130305100506010e0a06031d070e0411091e060105041d011a0405060301030803181005060a060908030a080405011107050c03070b040609030632060f01050f 73
    0x60704002c0c0d1409004001080280100d81c011031032408982c2000240e840714010348140068468450f40898141018030900303003c1c1d03112030540a000b68100380004c0c00e034035400d4500701c0c0d5a040700c6845041c2c139040108009500c140e0b00460b85065440f0a03290508500000e407600d107800711880c040300c041cac0004909903c100305032001048202059032600c2da0b000b4082c818900203003d500d20b00080f40d010503580d01c000c00c0459003211800703001e0f145580e103140c0b14144142c0000d0314a20f40350021002018041400700001106e00c0d40c0c13280c001a541c20400200849410a64040d4062014029040110300004030030384e03c40d0400740c14012010354891030081d0060242940d1000101c4021413800c0600600050018a50005404854500303450300552000b600035031140300001640040d00380f00007a4590040f886103400d08054401c00ea80304403806480a4051060205411001d400c003e05454070b145907016007102070030032a1a0024a012064081c80350320f014542152000c4100d03c214088 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 815454019 1250 815452769 815452777
    0x3021321030c0201180909050f0d12090203030c0109240c0c021002010e12040609140a0b0705120d020d23060607020102070807060908160602100b0303090909030405101404030b040206 80
    0x18841e481007282d41c4a40c1b01000400d5a401e040d0b8540c030030f00d00310b280c400f403000904480c040c0c601d49580e03100c4080c185442002d01100da108076018001480baa500c3e6070001d0081c00401c5200c1c030154048c42451460700c03c604104149034140103410401420056900840421500d5805554034000303009072000503030150440c2642d540c15840380e01c2c1440030a082d490003500681c0e04a584518215683d03401c82404408450f43c259800780810360104001e100c0f440052a03900d2094090b0741c070b840e0b240292500c00350030011640385516000600e99454810900c1510101c1e16960f11003480234502c203403030a15241000f001c9900505c0c0000d804800e41e0300800c5040c006204c0344044580c11034403100024004078a5100b800341611440709506488040c3c04950410380301d65034003e240f41c092040c2d440001d4401400c815805000400202200c4c4d222118914440c0804500031940e0710314103c1800701307005201203c003080041c1c1139002e40a103030101c800c543c00c40b50400d4111440e52a10300000d045845 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 815455269 1250 815454019 815454047
    0x10e060702241b03040806070c0c03060e060613050f07110c0a181b0f030c120203090a0308070203072414090c1005040b030f0c04090c03021321030c0201 67
    0x1103400a10040c0d0242008140f41502d001c4182d030395125a0003915902d02a50140752031503080302000454181c46040b500e0703801d5000341b5a000402c1d03582e44407a400c449407041c0d40c01440d0002d20801c0341c24100f41401284080100c07004110b0b9140c42520940018400780400c0100042c1612201c0b024008004000c01c4040080056450036510810001104040e00c001544141001c1c1b2810807441c820b980081490b031140c480c00702d14109020220001c10f040000b035418001085d900d55904174451025501c10320005000b40001045420068540c2c44010030320801c40d88104030b400001f60030024030322400a0304c0c9020b5004a40c0c021601c40140450030281c030340404290080208148000a0940350a45c040d110110381030281c6c0000c8445110701d00440480b5103042011071190701c03483c1c14960f44100b621059070b007810380b28032003078041c2c58410143c440066000300341804451036441c40c1c04001c24080c8940714154407074031480c1e2600a000300014090201c00740511055900401601000301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 815456519 1250 815455269 815455309
    0x10f080c040c091517090118060e0102120f18030a0c0201050f0d0213140a24030b0603070207030c050609100c1b0b0d200313050a170c0615010e060702 66
    0x6a5552030090101c005652035402c17440d0410045a0020f01c10f125501c004041480e03203030340c03610260325010094600071000c00e080b90341c20080041000c01600c0e9541c0500c40191030303c1c1e0f59082c210055808101d26058400081d002000b6004500360403207900b401982d4282171046c0ca070b1184040304440c0d40100900348001d20f00019100440d119080d030341c1800d640e508818294034614402c2400027046030750140d0300781e0713440d00c40f0009084070542c0b115014000b854540810107084034000b0030103d80050b6981d03030169010510502c100a0604c400001600d4180c504034209200b180026444e1440f00c2e03601c00c20710801806072010701c041140348081c18603451002e9400307103076180010103240d4400302aa10302140b401c190455486851504000101e0203090310301d05607240c0b59403104070b40da504d00302200c26105142c003034400a03408038200340994651090341501c0707405c81d00302d15090540c014011060700b1051020b0343d1141c0e8008010742502c035002e40c2c0f02c98588041d44085108060203150906100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 815457769 1250 815456519 815456549
    0x11115070915030e150603010b1002010c0906030e060402010c0507080d17010b032e090f020a020c030d02121614010c090b04030c050d0f150b09010f080c040c09 70
    0x440e400503015401c840c03884000e001d0000015004400304c1d080141c09881e02d801c0f00c0e4130902d03155040100c0c0c503002600200001200e4180800240005d100d800d202c00250b5190010f0941d12600646205c0c0282114102880142140c5d1440f43d00c1d241e0042000b410321001c0c0001034180705040000d0f03006028180700b240e5024000c050003800c0c50007014046e00e0008a5140041011030f51141580c0c041c14a84828042c0c51070059080080b0314040e03000038905840c4003d0000340e00b87d0301d014010a1a110321070050782c0d641c0c1e4020003420721045d0944036001c1d44c40304041c0e0030426400039401c0c0707054031a41852600c1e4100e0841204000c0c1e940270300031702540500c04600c40c020030103501c191489076aa4a500b0102c030384c6c0c1d490700c21060280e0310000e405514013800c100403a0502c0c00c82c11200074820418884104410f0ba142008006600c00032000b59903941c111203800d00304461101d0150400c500d9201c480b62a01200c95900c60405d800d45000b141c94450f1145001d01400c8034002410040000a440c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 815459019 1250 815457769 815457781
    0x160c020a0b07060f020405031b06090310091403070506340206090601320a0906260102190e031609020c060c210408040b0d02041403070f05011115 64
    0x390b00314140540da62440c04810000890399482200d04403900a00501030045130300c60f541b600ca49840201e6904030500700841129a036040c010070549080b192800515204a07003414661049103014807a00b41d0301c2003100402180000030b207030394003000554001440800b0b58503a0040c00b00030b0050500000c1090110500361500400d0080c03040102e6011502c1e160380c0d5802c40827012041d800b00c04d440f1881e104e015007140141101004d001d8402400c0d10024607550f20500342154110380c4010b030180c0c21a49141c0740c1d006002074100e444041d0800035414001ca1010300042d01c40d0780401c04050080710108001c0c81c0c2c8041c055804c0803600300f880c0030002d5549450070300203507015100320010b9004400c00600c1d1448010305891006010010313070814440e40508450780044050f00544001c0d0040c000007032140d10f0300009111690b040c41d009615245080118400c060020700c0c1070b03101e600110f4041c0408060b0116020031184240f030580e080ca5220029541480785141c500c806480c01c0740e041201c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 815460269 1250 815459019 815459039
    0x40e25080403080702060103080910020c03070306060812030106080f2206020307090b1e090a0308070305040f060c0b04060203060411040306060f0506120f0714120f0c12160c020a 78
    0x1c8690700980380c007081c2d5910364008030707201e0100b400010101030003442402101c1c14100c41d01c0d08000300174011182040505000a440c0c00e49660046400e2600c1d01350600000714288010081e03014030490190941d410901d0240205400914030400040c0e80400501d040b00c0f00031446001e02e07001d214400811600e400d211010798411120344012179140080018004050422150050400300442840c4041c451091209900404085600842c002e0700480414407000041100a02c40e854203aa074924020810901200c0f03035102d2001e02c00300d441030070701140c0c0503541c0750740c040d5010300c00581d2583c492000800030311280031045c800b0080030a0200812196512070405c1d510b100c0c80d001d0405996000704032807440380c840c501034940220400b0507403000c0181080c030f03000314280c03d01c02001c406000b036144803500101c4444218170504020700c046110b0000c0384903040603407080c0451400596203124181c620014000e403c040c210b800f0411749080c4103000e28102164024210b0820302c0d52195445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 815461519 1250 815460269 815460271
    0x2c0f0402040c0e060712030b0303190201062705040501270b0a09020102100b060904113c031504020a1e05160b0915013008040e2508 58
    0x9001d14640301d68010483c2c05021008403c0b20014600340c030300311450340e40310304051a4600131002d01d40c440315803540c543d4040c8040c12804500c20428a80210320341c80003404c2d540141e00c160368402d03203081901c0135039030002c0480100c4d450062000c03502d9111843d1140c010a85424a5600070b00003840d40003940c8950404800b0031805240e0010043e11100d000030102e030020100203001d07038800030110380f07a040d094001220b130290080c0000e05110445000c10165104130a502c0309004c0d00140391407220f0548031664400d4125418540c615100c00c0c6c2c1e41000f10040e0180325010342c00017000003500d40ca005103d200300076601401c10b40d04d560840c400070305140c0045003c0034120184aa00240403031155066401c6030098140aa6460a2503243c1c0380c48084050080c902d1801407e03014240c11001c5032803180204030800c4808403408ac0c00d5609604040480701410b01d1109031090b00000c03a80e05400d58082e02d40001c540d042a841d19034100c00c89030208110316088503541203602111a401c06401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 815462769 1250 815461519 815461523
    0x50f0706181e033f080f0f19020913050712020f0f0a120c0f0e04050c091504030f0503121513020c010204081914060f012c0f04 56
    0x240040d56100d40c0b25440c00400c895160300140540002003000c900d24054083c030881042d520581150100c648a901010900d015024249880440500865800940380d6031040d140720240c4104e0800c01d0007081b1741e25018201307031185415030001c40d03078000855040702c00c00c0d14000d2803400c0c85103104a80d02c029200494410000c41c4646040c1c80400c0803034001c44420110b05201540307007a20101c111074064024043d29800c112031010f100e81c50550300e201b030700080c51068480d40b0610000c01d800800d0008003280080c02641442e0a00400000340310569040401c121140b803072420071150205140c1c00b6640c030152500d28100052428004080010304114640010a901955030107080c0703405100c000c0001c54002d4210980c6500c030b80c00580c0500400351014001510b4960384106991900140c0400724108103803c0e4004410804050b652201c0c2001840240a50340b4000c40c1001514605214603000200d140319291001c2e401950300c21010950700800e840141403000d20744010760000c0b202 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 815464019 1250 815462769 815462807
    0x30d12180c0833040309030204020706050f0c0c0a0f031e0e010e0406050f0409080f040303050c1e060c0c0a060f050610092d09090b150a060801090207050f0706 70
    0x10404440440b80307030f02c4110740c1d144100341e02d10003030751842c1001484010002d82c100a4800d001000580d11800280f8415000d001b021179141020001c0742101c0c400a130400303452213410810942e0a400c0851790340c40460300f00e1540e007280d007042d050a1b1054215030785255204840c60028220150304214070451040007039032401c0340030021105100450b03a1a016003039010702150900c400b103241c1500320082c1a031041080d03e0605176291100c2d07810340c009820880100340d000c01c0d040010481041090300502c0749251850301c881e4a0f4140c01d0301c80501910082c0c0213540028031209800c1c080120f84007256001008002011030484018010301003510118402c0c0011120321036890720460212003a04c8078a1000c40190741814110302011465a110258040c8001c200003404003251041910490080e000c541492819a00d4542000000c82c2c850348140000c0c201402420390010080d41521301e0008016500c07200d6007495840c00100443e0031509118400c804034506500101d001400c049440c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 815465269 1250 815464019 815464033
    0x503160b010b0f03010e0702071e0e061e010f03151401170108070b07030207050a0801050103150e030a080c1909090f0203061e060d020f030f060f030d12180c08 70
    0xc0103122a100b000c1040b03c00c03140500c010304c40706210802c81e42e0404158011550140e039500c040030300346d42c0081521035250300c0300f030410024144103004d0b10703500c0341040740c1d4180d0141031001c01070b5480065450312410009480941d6211034041c0c5d00c01620b10280c400d03e03c6201c3d6075181041d8a00b18840030b007030300007a00fa45111058002c080d070f8190503204030a0203400b00c68103041031400c050308000d100f40d045204030000010340d42c450342c42400141c104200042810b42c158140140c0a120350794607514054139020307400144200200680380308a005e17140c0a1856100d200000890b800307110b0904c0148005410300341905a00400a0b0040300e00b001c000740444400c9038141d9080b400221740481d0486000504015007080e190031001c0c1c0688014035482c06e101c3c1c4a503d01049801c1054080b19049001082c00198015050313840d0740075004030780c00a0030011030300119846864a8510740240020460941503401d60394004214804800c60380411610560604050740c4d402c03841250301c9402070301 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 815466519 1250 815465269 815465279
    0x315060a090e0606130209130c02070f14240301140a08100506100309030c0209060406230102100c0219080904091a060904020916030f051906050108060d020411070503160b01 76
    0xc002c2e14151000248800c0d040342c40b00d0b2340c00000c2c01800d11010114012008046800408409000050580654250754030b61110050042008400307200c024641d14120b03166081042400899041d5500c910f42940700041c9440490f03032410300c1d500400c515005072031036901d00085545c01144205012600340c60396084440041e01140c00000b405400210b810800a0241c02c000028913007006001c2e00018045950f0340c0e41600c100009290542c1c2d01401003a258100c0d81d040110405c60319005402304103131307002c0000295440030280b800d21002c04040110300300344111102500c1d4511030182c0240b21990043c6401e00c01340d201325005030b0409030b4070f2010a1071810154901881264050804034440d120703104418100c5402052001c101510750582800b06030329802024052035030340c561284140e80c22071a0100303507000e070f410681c1040000010480e04c4e540300154203240580617240050740c890741c01d440191f14441c0d240c000d070461100041200101504024561000d8081d0384032a000da6250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 815467625 1106 815466519 815466521
    0x103020c0a0606030506011404111c0603050d0e12070f0e090a05011401050103140609013c080601080a0210050c160303020f100b0315060a090e060613 66
    0xc1001001230130b4001503500c4420904a80c2400540b079000304040c07032402510815112420b914503001c2d80049641d014401440e001410f5a212004080010705000201d2207203134040d003440308050310440b4010a130001503d14481c0c410501a29140c9101407030742001c2c1505a082c0107140d802000180240301754030b003145a503a40031801b9850314002404135280e03101813251242d0020200565552451810743c19a00703603100480b1700d0b09602c00f03090b864286420302c14201d0303035840c12022401714809071502c08481c1e1090440304183c3e01c58841d99103807600d0080007500704041030f8150b64032030700030005030600c400050211400c0610740c421007203225216900980150300041040e17072540109004030981c1d6805050700788a100f1341e00020941c1e5035880007203d001340303c9400115409a5a41032010001c1847c9001403245440441034145c4580090f1110f61003071681421030410807004d = true := by decide +kernel

theorem cover : BRFrame.Cov 815287769 815467625 := by
  have h0 := BRFrame.cov_init 815287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 815287769 ≤ n) (h2 : n < 815467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
