-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:36:29.196696+00:00
-- url     : https://prove2.me/submissions/e5690cc3-9681-4b7f-b7f2-8ec7528c620e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 10251805 ≤ n < 10431661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 10253055 1250 10251805 10251817
    0x6020306300c04050c0702010e03030409090c090c110703030e0109120f020117070c0f0206070602160512040b0f0304060f0606050a090807030f020613050402040909030f020105010303050f07020a0305060903 90
    0x10040c2c80e0784004107024082960350860b0914981901001000010b40c069154164020005812030741019240d02070b4030200c601c7c0c01c1c4240c2d01e010030040f0401c8080703901e02620804200790314001040303540381c051072035940300c10b4007000301481040a89806140d1144003000f0040c2108600440c0143e801d0400d190604800041680001c40200002e000e41c0d8040da1340c240205050780d54000e1018240d01c8410b661682001d040381e00a1003001490040354290020b05080d00341c0b440c4080c2c803280719151080c60000d42740c00da030405810500c010440344070541c00341d840f0816201040340d038995036464408010300001c01210051450100040f030300991281c060030314403070142c6440803184d8031100c08640c0d4040a100040003074030b0b202030082c01410b100b030190003007901c0c00340c0c0ea03a14961140c0c00582640c015411810105903158416401c2c584e0046140c6802c101d540000c200550454800030480c1c4110498805102c80000d0b4203801c544425580a00940d088420b4550605203102c0481d141da0001c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 10254305 1250 10253055 10253149
    0x20c06070b04060b18010909020409050607020705120115050105030402011e08150405040507050105070804090e030304031e0207030809060409060b0d050105060a020606090a090b0a0603030206070201090201020a06020306 96
    0x1840c0d90500703052400f031700510440081c043c0160b1070600f0f004040d0a8444049170000d8984191400007442045542e001d000550080d001072800c4c5000d07c540420388041c040d1103681000b41d4180d80700b16580005040d0b0b1001c0c40d000e5581ea03181e00050315024401c4070b00c2c0700307030f03441c000035044400f5030000b0744a00030018121400a0440d0380d20070401521020f84010f0020b800480302004550301960050041d184541c0485051a0340c84621604849141c1e500d00305603000041040704150b031040c2e0300410300958490b841d01410076010f0003540c035649800001c00e0303410b00040400660f51a04c06490040c41d9001092142070749901c00000035030492412102801d0420300080b62a140400999151070340c40e500820460391b402040001c4160080d00f0002c07115629140203003c5005124040d2161041c1400400d071146149002460300d03100410701d8086916008010380140e07408902c858545411101c0580c607a101c013030002e03001e0070b414074140680b064a2158907400304214051090b1110031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 10255555 1250 10254305 10254311
    0x18090c010315030b0109180203060c0a08070c0b0403080603100c030906150503100203060d06020304120806030d17150303030106021b03030306010c12120510080c0a0305030403080307020c06070b0406 87
    0xe190342d00110000c007030200030110401c620051241004941c44144031701c8442c100480c01001e00d401103407d0203010b80c1c100000a000145210104d17821203040e03608001d81c0c0c600032a83c4035940c0c48501d411240903000504020840c404149141d07020000c1409035843c2442c204820014448054018801d03c0d400311076043c2040170b2700408642c941d50040858202030007900c2d1040201c0460b4009500c01002940e22a101c582440d000c50700034030155100390b11481000c01d80810160010b01102c034014502407083e4000f6101d1140b41c0d6000c0c0c82030340c1d040d60010703902c00c0984880d00d04d102000b040706c0c00180c1620000c000000c1d0b081d8002003100c13218460804c3c030f0f600301130000280b607164482142d003d80882c501150741000601450f0780d4114048047c6030112480100c038080e6400c0c0c1e1800e42d41140404510402880f001c48188268480316508440d2a80010302c0e6030394143c0c072070241d880054083e482c04400240b40600074494000000c0004040680e81d007150700c0e2400c6421003d40f020381d0302c946 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 10256805 1250 10255555 10255571
    0x2b0606080604090302030418090f15150506090402160506040c0501090f08030306010c03030b0306010311040b0303030f0c091504260604020f0621010b04140907050d05040218090c0103 80
    0x2490b10803600002e1300f59000e503180c94104070492044501009a8402d4166611034035004aa0001600400380b031256131041c01c5e04100042d41400d4403580003103010150700510003040180e44280440c1c1084005480160711004540441c0100991400002d003450291070100801c0180c2500400290b42007602ea00c800f8944444249915204500510426030f104202140040d03000780c03c500e00d21813092401180c0310340e0107000b1905110003a482241c000c0300d21001d80b000e80c9014001c0e4000640b090f0000e41c2540707000c0b548507800314405002c110300c980c1c0006130280e1940303502c07050401324101d00d04100d9455a9030348085048281454200800001035258803203900008a00c160059800504102c140c1c480081007203126409205441600941004001403140e184100f15000b405101a0a0b132150714114041e044040000b400d14030418141c0200001f95401c1400d44980c49800307000003078180d8551020400d200f0368080c0c18140308030036504008040b000043d460b40d010300c0c2079800303102ca01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 10258055 1250 10256805 10256809
    0x603060c0203160305090a09021303110f03070b030405010908040b0d0605090103111002010b0a0801020405030d0f0804080304032309030c100c0308090a0f0308070201050c0403172b06060806 83
    0x802051008040c20b141a190383e0301080c4140040c0010702d40080401c003100b5580d00501040b644908050072113250b4202041003440044201e0a07150402602c284010074410000251100ca45000d032080003c408000300b01488825403080c42070f140e1106003107541e9a103e0388020003d4001e42c400303940c0b0030f0500c0c40c081075604104900a049aa020035485c00040b28641000038000c000e4413241c003190740e5a00c54401c165103654040340204010400182c0d01c07030420b07090606107805402100d0a0200d0100c03a4100c1c01c0e8007181c803a902640081d6016243c0d2554641181c40d901a244200c0354145800c0e00070f2101b100400046c004031104030101d459011004050086401301e40b80341e440421307100048517021074020140320b60300c4003040e0103a44003610182d44a090f0303da0401e6007030380091390030010030900030b13024407503150014880c0e0b4010382400d1455581c12100540080d20300d947c12004908030400c0b103080a0201c0c1c1d002d042e221100300c0f225100d51808001d010342d01c26400020b0070340010603003034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 10259305 1250 10258055 10258057
    0x605010504090b0402060307110613060f0606020a02120102040b03070305010e0a0501140f0d080f040e010e16110c0901080d031a06040311010908060103030201050a06140102100b04020f0d0603060c0203 88
    0x2c0c0340d00480c040504d6403035400f007200940009050b81d00388060301d60b20003403954040c007520f48109001040224242107034100841201e038500c0540c3c0c0d0341454044284075094001401031212541102e182d80302031054044075002e401140d2040d49000c4000c802d2000c8280c040e00550305903400903006001554400e40000e080d90402c1c0300340d0301e0854034805407906a04000c00d03503203660070000c0e0941e88440341c0c95a901d1004d070b210000311143c80001040030b1049503118003206004000130344d13072142242812a2900c1c24101071410788014054181c03e04808664144661640c5540c01072401c0041c1d83c0d240d281e6611103015002402c0044d151401d1031000f000b5059454400300d6024051b281001e040d6640c815441301d11004803818480905000141e01a0820419010714483c1c0d00100d5981070000c101800d0f240b084c0c026252100590014204690f400510714813600071040002c50f907005c0017404030b0006e00c03410f45d188030360038000504090302c009184c03c279104480c40380b4401c000d001c80c030b00c00898603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 10260555 1250 10259305 10259321
    0x140307061a090606030603010e071202010801050d11010503150d03030b0906010302041406030406061701060602070e070507031805030703030c0b0109051012020105190c030e040c02030f0309150705070605010504 92
    0x7200a800002c5032040c20100080d41c1c0c1b14201500008aa0028960306841c0c0001640940080b80702c00394040d00b1541e00c140e0050052400b80c40003a44482c0d030340c1c0e401101151035140b031810000b0210004201c1d501c50f102441c04104051321100c02c0309501e040080142c588080454091001000425404d500c0b078400c44007100c00b0744840034201c080d403004020f01c5a00162056800313a40f54400411032034101c40420f1180c00e001c1c0000101141b8040e4080c0c1003600c0c5510070368072540601c007000031494010040300c0b003181c1e061410030f080501150410354000380c40e4008a406100315103001c4100342c1c00001c42c584950195030718010980c0e032424217006840b811142c000c8540740106040003414140c900315002103105040c40780c185070307021010408605c83c2d00054000104e8140c1c0d20001c1c150400c483c0700760100c0035101070180d50304031940a943c034440c00b01e81da01030a10000c00900c00c0a01803040c0f002640340d192000d03589080515000f003003500089000d07200c07145454000a242c0c54035100b4140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 10261805 1250 10260555 10260559
    0x14010903060906090501020a0c05010b0402040302060909060406080d020f010e0f070608090c040504060b12010c05180307090c020105060a080106061b0201110109080406030b0102030306030a08070c03140307061a 92
    0x4090550740c03504040c00700c6401c115000364444c07040c00c2c0060801e00140160780e183e60382c0e080050442d070030524255022818101d000d40e00c100b1040c030158440c502200c16021042d40c66414503110707440854010801c1e58010342d824010620007a48082c0c0c00b00d000c3c000c1c450358000921000c41e98010301c83c3c23103461451071014580c0c4601001c00c00b03203000c2c66245510000c00e005450a40b00321030041001d0781d01c11139040340ca5641e10390012140746403981c8060011524000200440100d162029042c2d1156480c407076100c615104038400a5541049004040c0c654400c0038080d400006c170010340a003000f51341e000d12900300d131080460500340510400045450315600d68100c582c04002e080d10a4101c0c2c42d080c0c1c1082000081c014604009000c3c19500e40c2c40341e500b060340c503445c2c444020b00b1203401324640340c1107410800500c801ca81c0c00145108a0a41201d45540d032141e2a2030a04885112680000c19440f5600b00e180514540400900006801a1418040c80380302050395031074104400c0c000c507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 10263055 1250 10261805 10261817
    0x10c02010501080d080c0f1804060803160b0c04030f080301050a150507030509010e03030a0c1104020702061902010207021008040b010b0f0318010b04060305030403110406050a120528030206011401 86
    0x2132200b900c20345000703800104c1c201740b0501e45007103020900043d81c417009075041000c2c0d0f2308494000500f494842c10f030003880391801650506100d40340340c0110b41484807000e004120801c0c0401c54010300718049500031640f242c030120401c00e06185c1036801c0e4000b4418141708101c2100002403060300e22010200200703459807054a845020380d400e0701c1c2c076084411030703504021845075000300584040004064054050300c600c04400d009207007140941c0c0642c01e800e80203e0052000e0030050f180d03041030301c0302e402601c0c025080134000080b04a0090084410103540a04024190700540341c20006482c0154041d1482e071403a80c0c0c80d1418004180700d40c0c1160807000d0002c0001402c01c101964985000490480011905071141c60000e0160703500740c2c01c00d80d5a50400102001005080300c01d013141ca10040d1002d1003060b01c1d03d80042c200c2c4900b40310f01c40b9100440e0381c401d400c024090190010070a205404540f0001d008242c07a04046100745040703025108400000c40c005500110800000f80169149 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 10264305 1250 10263055 10263073
    0x1a060105070201120f1b0206090c010201020f040603050a0f0216030809150403030b030c1201140115020a020907050702030106060f0f0201140121150207020a0f030b1308070605090d02010c0201050108 87
    0x4003e0600170b5411681d41c0e0b840d0300c08081201040e00901416016500070031035810401c5250f42090640f1450340d05582c41040022003107410602031302c040364024100003d5640d10205030384040d241c41748034a441103100261031004803080700765804a2034000e075200c075078560359102c0c107039502c55940400d0b44000c07021900041c00248680c03c1280102000303800c0d1a1039003120000718a102c030b1880340c0d030422a510f03201d440b6280c120142e143c6006003402074140c00180d00e4450065281c8112200c0a401074050034001900f06005604854030250b014000700502c03076a69400500d0004900358400024102000d40020303103205026014000c000c0034070070100342e440c159100400d241c090540800300e0034110800170102d92400080b40b4130059080c805179903600288108014201160401c8425130080401030011400d00180d942c0d11003c1500c0c0d00704c4556007410078407d0f50040200c01041c1c40d04020802c8032100c00825100203200c9150028005c44c503107130074103909859007405601d915504c82821 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 10265555 1250 10264305 10264337
    0xc0406080a090f02030a0c08011a0d0b1b0a05090103050705072015030109060f0e010e01090b01030f0504050c13200702010504080f06040b0a02030705070609020307080a1a060105070201 81
    0x1000554400c0d1182c80f002e55290380824102201d20343d095851410b0003404000c117080070300410721042140c0c481031880180110024007483c103402400f6103c9601c80e000140003143c400081032400074020003c585420300100e0081c03240e0300c61401c50f80000d00341000300d15003d008000799100950300c01c180ea00300c4550f81c242590585022016580d0080d2514126010300382c0000c011070107413011072404980c41742444200e491001040d0b101d8030482d1141701c01001850f05024a050541741481400b24448951000403005801c0038286401b200e881c0070240400c00c0800180c2070081e444c20340340e0710200d44c0c041080904071400c4012402d00516106002c2400001150042181d0380c81410064107080d2a00310007032400c1c01d0745046000541c068002c1c80103000717072a80c902c0d038000c824440a600d1868180300061950041800080002e03468a191400f150340c20301c002409450f25004032040c175407907410000000007402900b0f2800c0b00184d404220a035124604980e0b0083e010b03140e0071025008211 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 10266805 1250 10265555 10265561
    0x307110402040f030b01081510060f021507080601080603010b010e060d020d0509030d0509030304030e010e01030905030d020403060b040c0504061803051002090906040b0a050d080c030c07030b0c0406080a 89
    0x9254480d03070811001c038502d0340000d000c0c0099401181c0000c02517041940d90392814900f07411180001c501c0c2d500b0030900610302c860000c107903065880c1a09c1030410000d0141d107050807512004c100a0091000c0120075940400e1140c0302c1d440c241da4242e80b43d101c510900d42216044151640000c8001c0d500300c110341041e0300202419681c201f401441c152004482d90100c89050354004450f402c0000e004100c6211801425004001900550b1460400f5034003d04044044c81620781401922455025181c0c002d078400203010b82c10800b96995289001c0d031410003584180011180c0d00d00e0050504424103103817040d100704200035221907141c03a041420540d10001c0104117041180d408100110014800340089003424076000800b5071507603000070401240c0840148910300441c5040a440000c1d903491f9100011100180e0320290700c080d0300c1c100082c02d44647c0300b0021040c44002141040c0000001c0e840049070b02134404540d1544480301095164400e52041500080c045030102d203110140ba4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 10268055 1250 10266805 10266833
    0xb1807140c07030501060312030e030403030305090c040501090c120e031b10020a05070c09090302070603020a0207030f0b09011d03040302060d06030b07090f09060503061f05060301090e0c010906020307 88
    0x24009605000c0200e81c224600000c0340c00449290351500d800300b040148503201d07014200702504040c484408001388170740c0d5070700480c4000740402da10b400200d1103040040c0901040040f02410601096844d10100000b41c0700220000000a11254200c0360390b00d12489000000712404001c2c6291841000b41c40700014031003840940940540c08645007407013540c0c4002c099109290700c54644a658600b07007041910a150720a940103420086e840d000a58049000025a0344504006880f210200c004a19119a40e00014500200c0e001e0090a104022021a02c10b03031000c8024441c400d0001004286013103043c02c0f00d4041d40c0140f1080c07005244c24409480b07006544c071800248036907030f03803142ca02c201e0095840d400450000071051080b9401c885800d8003801d2050802d0080718940804a41d46401c01083c18005504d2400544504ca0440001e44000c001c010181526540c5582c80b2200410220944107018414172011248035401141c4040403100550091070811071240c450b41c0100c9211 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 10269305 1250 10268055 10268087
    0x2041d0d021b0d020a0f030311100204050904031404080f010e01050606070302060103080c030d0203010b030601090501050901090303050904060801050903130609050a05010302070510050901090302010501050a1413020403020d030f030b1807 104
    0x1c0c5d10b000c01d5000011010100850081d9110b10b045001c607000d041c18001e0030039690141d80d00402091005465907242c1d03035086075040c42c0aa030010800c00c40041540240d8121502c14020441c030512520342c150404075052100d04001c00007070325100c040000074803846800030003680140c001000410a0400944451405542900d2414040001c0003040b13a1090304200c40321035020007807104559100d800840a4242800d055240c050b541001038180565440010200440060000b0058035250898030080c03100303d0084c810343c202502d4003a03c070380265865000890b03600000043d0300f2f209660101c2103c0014010349074060814004501035032004032309542030b10900182400c5801e003442000e1040034100c000080e110b03200d1400038251031043c1d0025104103003100c82406000a60300b1121000d0004848011640d0014010240030380540c3d40702950101000d64800181508130312082ca00e818655810071a140340401001100c2d0b1010b189491200104400a00e405000e0f2040b0401a401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 10270555 1250 10269305 10269319
    0x301050c0c0d050346050403050301090f02090a03050105010303111c0f0c020d0b0a0c090506180112020708040914150f0a0e010b1201050607080d050604020702041d0d021b0d02 77
    0x140360907103203071051105a00d1204101c607210249001c40c00614035204800c0404144203905154031300814600ac10300516000f1640c980144801e140c0a60450b506e200029241e40461641d9040840c003d100901c400d41c04110340070750843c0d50017004201030324400c420191035086142d80f50800c0300d43c850741503502000c0c48070484c1c5000142c1e07601c690070302080e171048a13101030700d150011681d41a1600f40440d8403d000c4100014420b540d10242078441c00340c1c601c05641120040f600041b00d03030740124a04001c00c03e10000f032820602040c030000708223940d00c0100500034411018890441c00000300c8030085040703114107800c1001c0c41c004101c501802d000a042c030307911a888002000e00b042017039000561403080002c00c205a20060140c031401020229002410b2a8880e01c610b1024130920064440c0c655803800081c02960f51941a20303c06900607104000040e090194108200e40031000e4030780c0c0780f00b5100c4107214070341700080100242131020901d020511103107041c00004020084200e90080d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 10271805 1250 10270555 10270591
    0x60302070206091e010311070b1602031902010504030f05040303080a1a060d0506040606210509071502010905060108010506130504020406051203070b0708101809060e03090301050c0c0d0503 83
    0x42d070394138012000e20924100c85418101480050f01b140d800414518150b00d081c01402d01083c1c2071340250307902036900380100c00e80d444110412402d520a03903403c0d916002100700c0342115140d05610035846a44203071101d04140600907000d60701d0b07014030700c002000110500c0c0003270192007403908442c62400c042e401103852032000c00f00080c132070b81144001c1c0503034640e5041000303018038186c05203400030591400c180302800c542054010b450703107202060281e40c03520380010400b549801c20a000051a00c0144070314581c9403020300a01905112105540a1103004c0c008a134002041c85841d006000040150b00b4440f03402c107809024000003041a40e0082d075505000406841c0c81a0324003044c02c03a00007455507040c071481e05600c0314001510074000c00140100300480c0017001c204440941c0c0080780c4040c030303141c00d00210501604404000034843c41c10901c4840002c00000050a28007400702c0c000e10282e40c6182d03000c5042d0090200b60502980608603246200b40554011a0842102e40111850f04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 10273055 1250 10271805 10271809
    0x110c03030307020102120a02030412050a0207091104031202010e07060c0c3605060306040308041e0b010906050f0a1401051b030702090106051602040e0f0105160e06040f06030207020609 81
    0x41c20880d001005130b500000c5c450104081810309076440f46901c202141181019214034002100003c508020320500140c3d40304084d0007002943d00808071501e003400311075110101b00010380c0040c402103650840882d614034685006008030f410103405080103103078841c40c2400c202d611203180001034a010f40c14140110704402d501c120031a00110705038540358090390219070000b0050381c00400c0400285408240030095401049480c2c125415242040c0c9035142ca0400748030303460400300114440c0c410a440c8804010f03200203014100c1c2d5040504000d0103944405011980200c100982d0340910103010070321501101c03102d80e10380024103143c81414170441480000c1d5124548041360100e41c8042440070842c94002c5960340545035030b2910904114545e40212a483c40324840244555101c0d60f9503194542e0400001c06c9100740d0b10000d000c2070600c2514841a1102c0341c20783c000043d4802d40303491103410b00c801110704461038445209030061402d03000b00c00a4101090407a8410800c020070201c039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 10274305 1250 10273055 10273057
    0x2010e010302130e07020f07031101050310090c0f090609050303040306020d18030203090301060b0405010e0409050f0312040203010c05030c0d1505040204090203060103060519030602070501020705060f01030b0105010816110c0303 100
    0x1d0300c00f410920380703241170606000c0d1501c0c9907610754420a500c11101400001c4030340e460108aa8001e00788142c4a46070304506050101c1e0340c2c0c2003080480d203041c9503d41080c2e4402c5031010010398540760841c030310341c13120030464a00c04c45d0b0065a4040d0320800c000c20004456500810312091345171000240b0811b0716491400086200e80b00741c0040e84041035100d00c5243c2807144000410000340e26500d0f0502e050006003e501080c210306100e59562806e000c1444010720441d407911358030900303030f0740e8810014060700040c90301641c0c181d000350b19200c00d8551050142040300e02800d400c0381d0540c20072800d628020050901c0f00507080240c05080000149030b204c070300240001e0b1454030800350301da1403d000010111515640207521450501c2c00c910303004003440000d0400e5035001a00175075110543d04200d40644281d00d03000340540f10324010405000107001085041e2840b070b401644d49170344d0792001110180d60944d650800300d00314180d1155460700948101140000c0401518100c41c00000001c1c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 10275555 1250 10274305 10274309
    0x30c020301090507060f031518020714100609050606030f0f070c0c0e01060806030105010605250b090d09060c0b06120a050f01020c21090103021b07030609060c030c080402010e01030213 81
    0xf14500d5030a01c0c0b1000e4140c000d84001414403866200f02c289000c5480c9001c8210322701840b49280c2c001102024425030700031026050020408071049000c181d155140103104511071043c07040d00e8803011a1080c0303400f40403207009094280d00d840325500d80c044c6a00c200800545514107114000300e40c0c200103500f0f401028020050585540c4841d8508600a05580c100814261190b49000c0050090903000800ea03030950100d03170580c4082e85101041c03040d071400440c0f805410842520100441000700242e10701100c000d0f039a401c0d203a25030f5600191108007420030010302039038440c40061520b04084140c18500059030f01116402c001c40e0321950304103ca501c500b0311159400047c8284030200401004510b602203880d901e10b90308080b0722090281c021504040d04050f000110780340da881e4402d2880c0200700c1e0841c00c0d96866640c03450084001c10110208448050a000c0c07000c2400d8024490031000414946483c4013943e581e5004507245003007074141c0c42c107041c0c0c00e006044800070f030f01e040000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 10276805 1250 10275555 10275557
    0x3021b060c12010603090b040b18010203090706030c05040e04080715090c0504050105010f0206010b09010905180403021b06030403030506041104030b060901050d0302120702030102120a09060e0613030c02030109050706 95
    0x940d070700381c20018004165050b0013807000c0c18104100f040c005841001180d41c071607044503018026441d046030444500444400b400c6241d030010003848420340010803500100c0b880d6450800c5007294205c0c0503189070246218080c51038003841c0005011a59000003001070502c0f41001100401c90b00f5280c408a5000e80410383d0f0410182006120a04091180724050300003420401000001c001009507200c03c14002c04250000c081a003104a9000301070342d0000c0e02005165403c8140003825083c102c490132601900148030312004070040d9130072441c0303010403000701070000c500d181d4440c4c4040c1c01602c0040c25042c0c00590700c503003011100c080b89000d0030185115860f02100703418144104400741106070031042c0315441d005480300000781c00084a0300c00f680d100300c1311529070420303000290080c002d01c10000903d681900800612091039400101301501c500400c00c241800320300c06690720b138022640e41e40c47d03103032044102c000b280c081c44c0211543c52008001007405c0d041a5210390509183d03602040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 10278055 1250 10276805 10276807
    0x4030602130603180206090a0503030f030a0f0b150c0703140a03030501090203060603010302100c060606050901021009050d0c1401060b0903060a02090108161205090d090504050609040303021b060c 86
    0x200e12071000340140052400d031405001c0081a00481040d40f40880d000030310607807001a050170207890740100360004080082c00d803034035501e00010500c46a40f048030394446071488e09110340c00300b442504c0386022030440030b030003130705064006c81080c11140c0c0040390000b860700c61410000300203404034000c43d0581241c80082d1010b20424580982500c42c10303000044002d0050081091a4540c0410780e0704603501259000c1c1508a003c5060782e0040340210080c150b6414140c0110300c46400c0b10050204007070aa00b00c44282054604500888042000040c05500402c0c00748242c0e61042c413441400500a00c40c1d46001211300c0d10140c2102d056030b0210031a030b5400314200c0c400745000d01103d6484903840e801940b6090080000914a071001058041240c440c2524001c1c81480b0b84d400300180030780740d8002c0000d42401c8020598440c0f150041c0700014a20810200f8103060034050719002c0c06002c1d111480680f00c599041d401313034201860800b4004542c1032103500308031040005901408100c455a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 10279305 1250 10278055 10278067
    0x20c0a1b060203181c05030a03020304021c030c060203070306120507030614010b030f040807140714040603051e01090804030b0a0f110901080705130608090d020d050f0c0c0604030602 80
    0x340603841015803114040d500b0902c1081d03810420840506801d070400c41d45480e035180641150b4860210801c000761a42c4030118005d50026010343c0118003560003156031f00b2082c64416000d1250705d0a8010040002c1d50100001000507025000740d5001001402d000c2141921041034001c00303141188141c803940d00c200c00400910025100340484908484406c940640c101500f46000d403201074805902040c0c402c0003d818003071700c05d0a032994030340e02011242c120706101d03c641d1342d100b45500500c0517501d0b00746610f50461426204a204480c0c0c4140544441c2c0d804c0094a89610601d180350a115500e5010703080000301c1e42002000910700c20310000c0307070604144070801c088412048100650a14142031107410412100a6071a10f04091900083d03545e595081250345000b0048085080d60f49101d01180c90798100a159104424003000c071840034000c45000c0780e50b04c0d6035940f4071001c1781b410000741c14000500c100818021010208441145a1714408030710140c1c856402035914a0703001c501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 10280555 1250 10279305 10279343
    0x30c0b0a1d011407050310060f0201091403070b09010e190807060e031305030106050f0907120f0902010e18180f03130510030c020c010c050a02040207030807090905010602030d0f020c0a 81
    0x41d0f40c0c002c0c9a510b0315a0441ca4045001c58043d544c5016036801d12440030072024000d4400d40100140c50b9000740f82e61441102500042e503640c122010484040b0400800143d4a1405214003407002107400300401034203910300c0c2d4104002c040361009641c4e900c0e040050101140c900e00852130b56040610045965a41c030304d03840323001c5442507080a031007a414410308101d29642c071510130042c10030440d6240725a07240e081041c1d0301c00c1d000903d41c4000b02d08025040031141c19991241d1500c5000b07803039042c02c1002c0e010401c880c5142c62500200d0003031350103010420501d0443e0388080b201400004850b4000c07035110407980b5640141c041004040d0329500d0034001c6051056410f140041103082c103000782000700a001c0e4a60460004090401c44040c2d1443c0600404102100c0c18a4001c0c0045580c0c80180c1002815403108a034200c000c80c801c07c1d000141411f540c81894100c903010b6001d0360803c01e03200017080c0501700c0321400104240c2c083c0180b0012080030300114910074415000c241c40150420703a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 10281805 1250 10280555 10280591
    0x9010e0108060103060225081e030613090203030d09050106060f020604030801060e01090513150506070b0408030c0705010c0f020f0106051f020708060403050c120304030c0b0a1d01 79
    0x11162819518010481244000740e071a042d81d82c000409625402c5650f140c210360b06140035014411390400848100f400408001440c140a11481c10344440a40300d56101d018401a02d210307070004020801c0c00300348500c0750702c40d01e0b01d50720040a40b480d00c0304122020302540c45070442900c0c030782d540b0081080400e400401d012a00411800504090300e02500c000d400c00205100c1c6200707008541104111503031090310b4910140c80011311154210170b103440e03000028444041d15190401d000b0b5404581d40c0307000030a940d26651300c00340600c59035940355929402038001070b008502e41e0800307004107000213100b8060700c9004041c9980f2903100b0994201c000f03250003c1d88160500301d900d880130512441d21a03441d00484e81c02c4c285c60311076030141145400c81c60040ba43d48007048a0107000213000c10594050005c2640303404d02c40441d6500e11416004a580e0300c802d0343d005010078610045100003400703d10030f4a41c402c00303441c00006d01000182007110100b002d003040c0d510f96559000c079802c035071110300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 10283055 1250 10281805 10281809
    0x9060f05011e1d04060803040504051819030320071b050a060522060903050d05040e0402040b0307080d0201140f010605030705030406061211030c041a060c01200403020901 75
    0x1103440b44140705403800d000180c4100800c02020000140040d040300d0400030b981d00b0f100300014208001040d51544c0c600c0d240e41080c015140314a00b00804200031050040c0d58500d9900004082c2c0f0b40070031100422031490701344540c220181500c0b6010790803003415100b0095103515800c00c0d2155100c07202d2501c2203621503910849100e03815440002e001d0740e00c0390b20000c0251500c0b8244280e41c0d0074008900cac0550701e030860440b0b41e684040400815490350281849003181d00c250125000d41540784000e035824060f0b402003120610341c420000c2c01514058010f040318070700181c25120020303150110b0f503003082603000b04840540c0d150551112814007201019501404c02824815294100400101640300c00703880d5108003c03001c40407509006035940280020081c0361450160101c461400d003010050b2446c100d403085c0284200400e10b4140b9005417201041c001d03d80c903400c08054070401c0041c2c0c01c16040c000156603102c120f8800d8040b0b502710b0428800c0e03490b4404d81c42d00c4c070750301c100604d00e4016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 10284305 1250 10283055 10283057
    0x307080406030f0905060a0207030c06180c08010c210f060602030a0e060301030b010e04020307080a030f0801060503060d03030e03070b01090603060b061606050a09051603030906020c0f040504020301110409060f0501 94
    0x940704c14003140d0082002c9806c900c01e0b0601681e41e060b2400d04581c003843c81c5002800892800c044c6901c01046514491881071040010a40040d550f41c80c2c0e034201c0e2440641d600101ea2400c10845125480710b401074020f813039003000007406940004400086401c1c2e600b00303001503400042c06528668100002907070010003120002c0c031b55815982c611070341d03080600c01d240b500c248804c0410115501801100c002e80107139022a144505d60341402400051048060350103da03400b4004140284600f04603440f80002030a107202043d02990304034000c1084004071301c0180024008000002d001000b058000d041c00740000c5240d609504100c81160301d41500325100d82420000d49908a03000804010241d8000707100040c266a990345000180c224881e0050041c040c3c1c640f102880580c5039000c0b001c0e24000c1d03a0310b82d5805c2c0c541c031060741e0764003094552681c40b840140000042d8600b90308280d0340300307201500104d42c0d440001c3c1c81c0c40300fa402c00d40120201c117440c0c2c2d03000c0c8000e60ce40001c11000b8202 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 10285555 1250 10284305 10284311
    0x9010603050a12090812041d090a0201080408040f061101150f060309110a08030d0e0c06040b18030d02031804090201080a0b0a03080d02090301110301060504150903050307080406030f 80
    0x303580d968550360603615100801100800e4a001807890144a2030b00003401058107960104c0905088040359034068000c981c20280c44400a4182e54680c44103544140349160081c28480820380040d540000300074401c072000c4ea0100030220740c0b05040144880185a0340d10307800f60300911008142e007541d0500d6001c24a08042c60070811070102244954000c8408604000502540c0c44c20b10603104e0820b8200c03150030140e0360703070002a134000010051041210f18002080110710b03070700003da140c515a5911580c00301040c030003400007542e440001d0100c40c1000800c0159503c1700c1c40803071304100c8680c048a01607000850001c07081c003451284080c1c0c1940c00c840400854503987c0c006000c82c103015000185090383d464401701c440d1104800380d005141c02480d00c6031a80c1070707210b03507501a5002820b944d0007035007482810060341022000390b03410b90300c00d612164207050400b120305070081041c0c2922030402803088000008501d09100400500d406400c000b603071181403000c0a401c0e0740c0086c0c0719000640c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 10286805 1250 10285555 10285559
    0x7050405040302060610020102120f0f0a0b0105040b0a02030409060609170613170702150408070e0408030402010804030207030c0303020d0905100905010819110406080c030727030b1608090106 84
    0x25004c921954003010450300550421600d400c01c80c02801840c22041e42c0c0140c180c1408200c2000071000c51140d40d580085a403030781d41d01382091003501c041400b100e010540511082c010307030014001409942500b44102e07410030350350b100c04005844440d404a0003103a2855014440240080f01e4540301048080052803c0d0801b051196513a1606050241410f0031090680320f2402c407600441d4045030300285100c071083d1400002e480540d0151060100d64440c06000145180e0300100c3d0a1045030420402811940e42d5001902e002c0c500070801c40450240b010f000c80082c10345482c0d107000d1400795001305552414282c02a00072109900181d12960b803078500303071032816440f100c02c0c41511000e2030004500d0b100e101c84041c2c843e424540d5912100c2c2001c1c2901d48202c190b41c00381c0122129a605c0b901719858149100d00310348000d540b52400030314050b40741d0000389203514545034110390231a600c1840c80d98035120b034900110700f43e8020340101e07001c0c40440401641b10031466000070342304000b040024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 10288055 1250 10286805 10286807
    0x10c020601060e0105161b05130608030d110708030108010b1809100903030b03011e050606091305040c05060f0705010506030c0604031403190504060f03060e040b04051c02010e070504050403 83
    0x203e048400314100440001c45425001036031030a080090781c810036031170008a03011138007807000e02180107180c003500b02441042d06c11046401100c0c1116902d201840c41c0446da0314100c0050000e848400c42980c4040141100052a4400440c000c0841c2d4000003540810401080300058414800d80080c0c1141d00910801c031502181d60448000300003000500d001151070305070f010700401304446a05502c0c2c01d1900502c4030000d90580440c1d16101000c0080b0790390341040001c9030045120054101110a1081c0d2442201c0e521064106000d0451041102ea554000a40903802741041c410042004188130040100901070503802c804100c0282074030444031000b260007401640b0002d020403607034201840e402c0e2001e00880d24003e01036140d01036030000030040681182e000784115000500c5540199007498420320607201542c0101490491548564841281401000d40107403401d0282d12a4521034144407001103c140a072600045140c840c00c402650030305049601c0503024500b0101004002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 10289305 1250 10288055 10288067
    0x1101020403023d0c03080a06120305160602030103080702030f060403020c01050a03140405010e0d0e010903020f040f060e06040f05040b01030f03020a0506010e06120c01080a0c0302090a0b0309010c02060106 90
    0x9107a1041060007030b40583d40061200a03810f01280068075901c0d000d02140368406103601805019458908040d02c910380c2c0345044135854811507103220140d142000000340301f107008028190309889070b1021010740d615440c0c1244c1c402c0c0d000300e4602e007000601900314101070240c1d01d5411040d00150050f468141c601035143c0c3c02c00084241040000600100001e02030b6010410030040c0c404030003298070345460402d0090849551013002885074865640380300d4400d201c461100f00f010381d242592103140d6070030b1120081c030480c3e18690140c0c07904010782081c003180c4111002402c1c11440c52180e81031070014802180c014031004078809040c1020080407421820020b41140d81c0204444c061103000d0074200c2c04e018440500500034021a40002001584102240e005180031140c150701d03064601075451341c480e0032030842030101d40c0083c0040ca0003804c42e0302c81781c803651560278094a48041d1000141c00404540c00640c074005000c0240000b003042441074110725101400240300c0e42d410104081c100c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 10290555 1250 10289305 10289329
    0x1050907060509030f03120702190c050105070303020c0102070c0e010503030405010903080315031b1807080f06040e12030109060b0306090a0209060d06030b04140d050d0b0607020a06050a110102040302 88
    0x1d11030002083d02c02ca803010418200742c0c4035040107a03611214100e1440303040010550f48000188140c05e500c11030031130341445c0410001d40c000003020341249003c0042d102c80c0c0000f0001d4050550074001c02449030300a000408140344107031218000281000000c040307042c0180c04c180d009600c180300901c510398220702c2d100150380c1c020000341d46030396540203100d010300040c140150f00360060052103188024040000c8980c00804c076a07454002c441d10302d0303c0c0c5281c10200c81200006090101290150341d01450540c1c001002800c00b10781480f0406416240a10b40b45004514001c0000100140c00c1a403180601a1620310500d03440c500701400041c1007858007804508240d5400036448019503900b03000c6601008000c0d07400e004040e500d04025084240485042c1c951001c0000c08200e00306022548ad081114940c642c207090040c0729000d10020070520081c0750304120108194000340c1d49001c00100104680c1e95955550303040540d00070044199101000c000f07030700500c01880140e4600d45d070449 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 10291805 1250 10290555 10290557
    0x7060207020604030f030c0614060f0409050109080307120b09070e13021e0a11060402060406030c0905181602070303121a09040b06010e0604080c010503040203030408010507030902040c020105090706 87
    0x40c8032082800020301d0340c40f0315440108200d13040920401016004041d809150303005142c10425800300030143c600c0900111a800e40c00286d50701541c8861a2651003d0b04441c0210000070f2004050382d00c101195000340c800f9400300d01100d6050401c215540542241340c9810303100c010b02e5082816028080c41c20008800d0321410008801c100f00000039030584001d050740a0807039094030740c44600403e8039800b200b0352100185510402840902d400550039000e160b0203882503203890300d400e02c214001c03d100d91034a01044214480080c0c0c40d0b403000600c0315803070703890b034400445e40c1000004441e103030f90003807001d00a40d0409078003040401d4016414800c2210700c52404201da10b510f80190030a00300c40000303541d2010b01a801d20040c0401021098425002a2291200d1900c110104400c0b0f0082d40b142d4041c0f80c0c041e030180c2049508c1074026541143c80a0101c90400b502c5403555420b6a0b804c88810001990318a0100154503041c01103211000b11400200141d0910028442c1c8800190198034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 10293055 1250 10291805 10291807
    0x6020703152a05091203030403080114060426060105010c080f0a0309120201140106180314010e0a0f02030c01030c02030306010818070603050f010b0906070f0201020a0605180609030a05070602 84
    0x14855422041c010b441e41e450521024500c1e90302001e002d0450b8201c8010503001c3e0031080b40844e08403c00004480c0038a8140e01c500805a191a161140f004094480560004000d000008864106604041c00d018480c140c40301e441e05204011841c0100c141e100707904001c808004040816449012180b1110380c02e140c40d0307603404103a001500500a4100020700d00e03c08400110901c80d819801910800140030440740103076a945000c48019070b0440c1e01080c45d0080c003034100300140c00c2c1042383d40c603408080008a0b000e001302d40d4042c01d0402207075003034451311821071000007149020301446107810390908040207000c5428400a40e2400000c0c039090501c40c0c2030011900240340b00207001c0019001004503186c454980e80020040d00060b0b600a001800c14400410800b12043c00d03107240306805040581031200545421213000350016041c0d0660040048804c00315442c1d015880c8201201001c02a410300070044541c54114001c154548980040c0440c6030401e6100080360340c0303da0004409 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 10294305 1250 10293055 10293071
    0x40303090302010902060a110114010b0a05090406030b0108100605010203180906030a02060f040603050c04051c03180e06180402010e060d0e010c1808010b0a0909050102090d08090a0602070315 84
    0x26801459213880203903101501080020201d0351000711805c0303110000300240042920303450300c230300800d2080c001c2e04800c103c02e1001c0418180300714041d22041000034004140c1c50341d20344542401c4902070308400710542090004848416203800742c4001000c00f84005c500c0c04010014500f48640a00251449047c000011801c2550f040100007449500140106c0c0c0d680701016414030507501500c5040d001c41e04000019524028074800d6030b040704c5000e050003108185414003141e60301c01c1420104c050207007640c20b04501040c4030701400701406004403480010700341401000f1020070345440500244408d007003000b0060368403400852444a09852040e1618031032081c21000c0c1c5084503e50307a29600e0000600e400b158401d04410000740c102c00180346141d100c00c101426034440c408501d0f08011141e004220b131704000d41c00b080c4480e0107070340010300301540000041e2110034510300580b40800c011039192558a00110b900006040c1030004103511840c41c0da4000400407905c11718084075540b0044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 10295555 1250 10294305 10294307
    0xc0607020d15050a0b01030b03070b0409051f0801050402130218010503130501020c0a0c06080903031303090e0a0f050a0204030506150d02120604051002090f1009050d06050402030f0c06030403030903 87
    0x1150b5030444080d0350900c00d03884e007a00c150f4000c0c100b0702d0845000030b01388000000c8904020924400352480c4000103840c150070300011070040d00d4040c102c1c900d030001513240301c2c4240814000d01005000f00300004521030816004110300840012440141c83d8810030800520f50701c2c204c800b2b8011442801c019071680d0b1000c2c01c0141103024404003a000d94000030f100c210144001c6a02401640706608103400345845280440300100225039610b0035078010004519041101c00703207855403520a142071a4410303210003408424a1064030000d62543e2911558810b015540c01801e50024a0318021400c1a10350307114103545040142c035075401c1200d9809075000701d4680c8000300b40720540161003021608507488140ba0340d408200c41c01d80d52030191000301c0301043c50300d000301e030100b000090008005c400c03a401000030880140d00c0910500c41802c1000900d61a80b4064075081c9016400000d12858240180740c140f0a07581101c00594210500f00365150b42c4000c281c0360042d07091310b4000b413a4465450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 10296805 1250 10295555 10295573
    0x40204090e060108060a02030f220606090b0405071103040b0702040b0d050601090c0201090b01050f011e0e0a050406030309030b0a02040506030406320601031509020403081201080c0607020d 83
    0x442500c0d282801501c030701009000500604032440803084900640e168452041240000c0d0b070040c2c0d010308120085400e100030007002e180008002c0c0c1c2c461910f8a10366a07214200e50b010b9210669941d00e50200302e080e45050700c611544000315040c002d905030308002c030641d124800d5004580f01031030081005819500c440d88000340c142d80c064105d038820109800c0a6030ba0320002d2240c0d024031828049983c1d6120300c1030045c001c405501c0400300145900b4041080b142101003007840d81000f900d0002c0703400c44802e0011015084195403594601541d00c4420303c20710410b103411142c0070f2828021b0401c0040c0d8841120b004690304401c4000094070b03481c1a890182c0301e0fa902090744800c0c04418403041c40300c203500c100e039801540100e03000d02940c80014503121104000484100e400d844000a00a500980044012215020f840d0031820745031003200049800c20740042da10414007017150036821800860302030142402e60024030005003402c000030424422400d00a01500312490381c0010030032214 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 10298055 1250 10296805 10296809
    0x1090e0307080f07020a09020903030703050c0c030a110f0103060e0c090109030b0106021e060906010302060901090504090c05010f050301081b01111014070c020d0609170c01020403170a0509040b040204 88
    0x42921560f904070010220119000400d007a40308004249000603480b03940e10840c0c045000c003034082c41c20400942c5040e6419001202440c3d0580560200034076903950034418aa44244510000150a4a104c1c1800716907000742d59000d05162602c41d051004004588040c1da1043d20740c0186940d441c050b40c012640300c0c0041e80028101182c000000c6000f9070003040a01c9900d00100030045140900c640d981d0b50f03554151a2602a80c00c001c0040c00981000d0008043c2e100c0e06050107103269545802240456646440c1076880101a1006001035a40130f0452030a5842da07141c5242107504001b1030703949444412140740d03124411420500581e0f400742c004960344182c1707081542c0d050201d01911101074189600341c044818030003000114680c0c0155005100242c024000b501c0c00c81d5140e444034000c02511100741d480c200441420b054074003842d0014145902a0000580c5a601c3c41c5072411034128440c5075002e60300300c14480b1400c07036035020064410141c1e08480200302840d8034000324009104603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 10299305 1250 10298055 10298063
    0xe010b1312140d0306051e09070c02040b03030f090f04050108150a060e01120c060503090706051602040501031407050405041101030203070908060901090b1e04080a12140703051005060301090e0307 86
    0x4140c02d80f29416070300c0641100c90990300d044081c0c4d0380c080c81c41c4c1c002c4041b039040c40e0301070120008564524482c1c002d880701e091010700700048200005000071b1a68200822500c08034100290300c006a0a20064076205104151014030481d41424469034036940c1e680e0101110055100004100c1d915070340100d00141a00400d070401940c4852018000c07990b804000e4941d81d5071000c0001c0d043d4403c0c0200c80c42550408050704403541040c4080b01c1950100c4000480642c19203d4800507036514895240213510a4030400c0c600c91110040508100076644100d1040d4034060802001c1403020f80005220082444c00580c1e940c2c0f100015501c0c05996081600d59204901c10070103e401c0540c06510740e540540319420060351000211864a1941c00340c3d40c05030a80702003ca0001241c10b00500b9500300d40d4100038001d551001c45100841d107141d51400001c071503490500140c03a8052007400e400034020100c0d685402e0920001c030740d45200c184111142543e6681804094942c1442035440e11640 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 10300555 1250 10299305 10299313
    0x606031306050708040b09120901030218060f030f0901020403050c0405191d280807050a120509090901140402120a17070507121101120209040906060e010b131214 71
    0xf004070001c10b0b03440211000c440009800000c07404840000484010010801041c10300e01100440110081c6d00728050b64200c06400307800550a698074103000d03107804014003003c41d450307242c6a50b0700f0348910000f5000190036481003000f480070070b0020408c4401c0440a590101c0c09072680c0710000c0400003688500c5862919003c1900301301ca401d04004071820390040201c964800400703a14002045594070b0300380d4945c52000040c000101064040d0250038012001d4500c1842d15032a07220b140700e0340a14610004000203003500d114540001020f030000d01c060001c1107d03d01d5480710702d500d484041c0c00684240c0b14411300c2c1e00c04081c10052102c08650000c001075a6044410311741415411a40d8119200d019000022600110000701c5d403ea15401070064251100c1000066441038a000152414540c08001e18a03894a85010359800b4a01c610000160740c2e00d403a0080400380390607000b483d0604010044610f15003d8100240280d4158440100c10820703189040e903041e8601c807010415a0103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 10301805 1250 10300555 10300561
    0x12090905070206070e01050a1d060c0d020a03020111090f0409051606020309130506010c0305030408040e13020a060806061206030309030109150605030a03050714120c030403020f09040209060603130605 88
    0x15020400c2c3c1c0c0140003a031112222000d41000550b500e0081030070140006904100226120396603042d000521000906610b01d000f00f445221801c20303030032020100c096409403d0710420954240700e5840c40105189100c0d0800c2120070004803030306410358065100301d072558800020b04c44140034044500d04100d184520556540d18060741f40c1d0030080785184681320030b40031100c020b001400f80911921050b56801416030160340c06840c582c001074410703601c8910038040840c00300d414041c0d0074001c1ea0010900c2034001d1040c0304204203588160072003420042c5580901400342c4801040d0f815044104c01800c08590b1034001083c030b103000d807208459056007440b0710b081c184840c4c1070484800506440051000544500034596200c450040050016070201300400120b00790005040d030b07034400c900c01d40d030358418400e00c104466041780500d02da15400c0000c0420071450005804900000d060b10214103518090300010007000c0d00410b414001d01c40000044e841020096400014643c444801c001ca81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 10303055 1250 10301805 10301807
    0x7030b0303161b05060a050c1501030305032706010b070f0203030406030203040c08010b0f060d1404120e04050907051002071a030703060b07021f0210020d0213051206041209090507 79
    0x36a500094825400d110f4810410541d00101c00003901c001070802d5150160f4014200c5207036220041c000158026048070728064198115400d0007140a0b55078151079040ca060f0307001c007060381021a000040086004081c00c1540810a2411102c207150101c1d103c0c40716080024103800c40540095041c0000a0042122909540994011405198521989902c80071894201d0b405291074039802804041c03000900c0c546540204402101c0039008610b0401200e000d0b07000100c01d5808482c000794694a1311b040507408800404000c20440b070a00c854203081e443c00780c4078040e500829000c0c250b9181081da2281c000c1091070003d18002508501c80615880d44072450341050b20b0b40c20029041c02c0c1e0010f01004001c090f200c0c8160000c2c00050074001c45910319085103180a6003400794000e043c040c2041004607c0035203010701c0e00400141c0c0d50164651054500c102c0b91b04082e01c504e210940e6058000310002d000b95100754000240d4a1135110703084203558581c000e50003510a0b5003803601700700e225 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 10304305 1250 10303055 10303087
    0xf1101050f07020c01020304061409040e010c030e0105100302010801030803070207050303070f0b010b0403082b0c110606100207060e0409060c02030a0e0a14011214010e070f0201140105010807030b0303 88
    0x80c0c0c015070f080d1354820001100490716445a840703100e00007071170382c60006c4035004188000c0000540c000d100061f03207101c59065600751070b104560318010940e00c070181403606400707000707031581700400c2c020590b41c41e41140d0001c0c00101060201078540040400000c01d224020001c05000d08802030483e80c4460304c0c0d00d01448030075030400b4110360000240c1d00004c1c0002491060b2820b8a9001c0440c90401090400a280e080e100c0740070f20035584281c0315000b1114420b4840c81094201076502d00105c101583c1402d07180410152016001c4c4003420242c4c45940e50210340790094541c1c1d86460281584654009000b40858000141c4258501101070120076000001841099140e071100351801c1d648504000703d00f4520300c1054424421303100710121561003808000d20413000d0020004001c06d401908480c400780c00d070080c00b044074600090180403900700016088205c2c3c01c0c0300074481c141407030420401140d0184135040c18401c2c03403004514000d01036001000802005012a0740310400c0780091610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 10305555 1250 10304305 10304311
    0x5070303090902030f0a0b03011e06091404050606010804140607080106020c010908071502030f030a060e010b0a05160317090607030b030a0c0614040308040306050403030e0a030f0f1101050f 83
    0x400e255400000b00340d5218001c0d20300c01c45440044d144250354102c821405040d100000940c1556141c07040705070541041494149151041c00c0040d002d410500080c1c21560800e003039a400381d07101d1040000080d00010030507031000080c07820110503100c81c504000103101c0010181980d02511041001c0103030301000c000c2c100e5155500b20340c0c08524440043d00d01c40030f94010038090b908040401d001c81d151040c1c0300d1010001da81b040f285024280c1035041203d4105454580315a42c0b107140400c01960035200c003c0c05000180880c80ca0194494000341082c42040c10701ea0740c207091203c40006041c0140c0c070449000d509640745000614000c48100e0f141c0004603030440109180105501603030038001508402a0b80c0010305007503a508088054900d406200031000a070141008040006901c40010b400190311030000450242005e10740903069070311540c500c2002e54041903140010940c044200c00340c0b440039042803002c86800400885480c40b011031217a03c0c642c00c110a0241c032548403c0d030644 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 10306805 1250 10305555 10305557
    0x60615080a09050c010f020c0402040807030c0b0a05040302040c0c020402030702011b050406021e010605030d0f020d2606060903010e0a1208010803041e050405090a020a140312071a0405070303 84
    0x12281d900c1c0c6260314211a4400c2015010340d00c4105480915405000c03602c0e5501a01d0044030051070043c00010706a81c41078003d0190394100d4481001040504038040002c0e00540810900f00300e06088024158002e0384000303031082d510385c082e8086440c0111003c0c25896000740c025542c9103070280002e8080c0011041c2240100280100111000d100f04140c0302560303a02c2d03010308000050013800c3c103502c200d103030380722501550b071600001400e55080201820314070341b40c0c40c0c014100b840300c00c01034145500301c0c000c0303030074400705240000420112600d040c400c3e4400c440510141d81300d02d4089441380c000d56030601d07003541c81c022600b2007603500040d080346164811302555406e4010300300c040350300c56000e10903c030459000b88014000d01174805100c040d03d040d4001c0d0700c0002075071400010142c81081d12906183d40210f80d004003581003d6203000d01070224061086048200503000c02da40b81e03080041103040c2c2c103001c503407841008420301d1408440140c5044003015801d00b0700300551961600c1c03000320 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 10308055 1250 10306805 10306817
    0x150d0b1e07020102030c090103050a15060206010305070e04020d03030203040f0c09020c010506041103011203020f010603060605090907030b01090c090302030708030306180405120319050c03010501030c032009060403060615 97
    0x241d201d03105008480c82818512161410808464010341c040d0001034100d591084c1c468214403100510321801c0c0b0014036040d40200025451400c00c0f40c186451500141001040f01d0100000368581240914110f0350615005a60b0703540c0d1304180d502003040c00e0000700718050b59940080d1001c402d4014260fa41f0420000304845d8803041c1c20881140c0c61550080d60060023840100310805640c0303244010315010780151900c2a804030261402c40300203810840d400342d035968043c4600d08100c1c440c294007031742041c010082039055854011208405100c3d18819640312100c0004040c820246c03c0c00540c0c5c0a02103e03002910740601d16125001250114020b032071824120034650720b4101854012500440039010444907040c0b240c6040d80700a105105010701860210340801103072142034400e00f038003100b19880e541084001401c9d640c0d50351200c0c04150409070441056001c1400002c40d00d03024018490750f4072082c001041060040d68070144c2000e2030100000f40b0540b50400040c4140385a903912 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 10309305 1250 10308055 10308061
    0x120f01060f030f0816080d050114010c020d060b0303040302060d0501291602040b12010606110a05030412030c0b150103060f060f0305040501061e05040501090b09150d0b1e 75
    0x400340d481002d00c0080d25500c007401c140700224a1100003030040001d008038040424085450349001c6500113201428038581e43e06c0100001c013480c0c0f400700c0303400c8000d01e00036440071065000101d4194410002500c1c10b592084043d10742d540401c00c5170000e55001c1c002c907403540381161051004160901c11070b034100910070070381c080d244246151507051003000314141d4101000c040da00c1e50a00495401207070000d60f20f513201b48569444081a5240503881c0700082201ca04000b002000041e06404480d40d55022044140c00145e002c01501c0550301800d0300221980405c0c2004c48205008010240c4803440580c14004000c104402081c0c500500380c90510005070786d40d004107135800311882800700240c0d802d5880c0c003040f4460b800c03080d00319016100100c0c0882c0c84590701c1c11381c201c0341d1280d00d0450036044010815400c043c0601d07801886584020400c050249010841400380204008004840c0310760340c40f40b5665001640c07119a8015150354101e1808038118000c1d0307502c0b81400c81043e1003040c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 10310555 1250 10309305 10309319
    0x40b0a0b0d15051f0312050706141501030b03030a03110d09030207080c06090105030105060702010905041a1503010806010302090702070305030318010b0a1413020408030f03190c090b07050309120f0106 88
    0x35900d40b182c00907101344101e00d15143d5030211801c4903641c00c2080760400c0039002290300341c0034000c01000701ca0460011070800107521400c1c00310040e540c2e414135040026007400e07940e0100039104450400d060103d02070407050300038030142c0316070b10b04403124070714255051050507030001f10072043e034254008403081d168001b4100041030150803540c0b400074204100601c6981480405002c24900c1070500f1510030b130b02c0718005000e5950300c41c83c40500b8410030fa150031151800031001c0390007444208400d0f2955040c08a11502d030001404040d0140c1c0619012418151080007040000c50b0040103880c1c0b2414921454011600e102000d482558200320910a841c505010301408032100b9506c0c103e01441040203003c004150051111031442e0709100015140e001440184020020b40091940d02d2402c9000a003446080c2981c0c020070910700740c4112021900b10000d0010380e001d079032400e61291028500546035129000419800242c4440382c00c0044100040b00c0010f0025a0b009001c00c586a0715 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 10311805 1250 10310555 10310581
    0x60403170f040f0809040b031b010e09040c030609031403070306050906010519031107080711040e1504021309140a020406080d020c0d030507021801091103010e040b0a0b0d1505 77
    0x500036001403c202c1c81040060343c00c0d001015009400780001c546060540002400c0100c0c404244d0700c4015200c4058402e50791161148410400898003084075080c1504ea19000700c40a002c010304440d6104201010b050140c185200b00e14003030f052960f900e103400c0b140140134100d6449014000ca43e640045649913004000340c0e04011400d00710700d041d42c042c00000714068481900141c00c000803c10603000881c9444008084080c01399050820340d170007103400e20003156030301c01080406801240e2811540034070840040e0f00f10b601250040c441d58034158405004181d000d0307004040e80380720f50143c4900c0300c2c007107200341d42a4000c43c1c04105140c0d65509564403180341549010040c0c111004000052400b0080456194040d00d00b136802d024050b4041808021098814842c82e0712060041211000380d0050403100c04a10130340f90b046516221014000c41d40241c00241f00d01c0f104000514014201e9020640e10000142401102446070501902400c015481500703c1070900d0005195886c91407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 10313055 1250 10311805 10311811
    0x5091003031b031205100b0f04050307080316060b0f060c0c090c0c070315020c0609030c0d0216060c0f1509030905040608030a050f0c010f0b0f090705160f0203060403170f 75
    0x3450714104c110508241c8401020014500850100203a0b00820411007a02c0603007190711010752030030b07682d81c00c003406c051811100e680141c5181e40100f01180f0050030015124003c41d91040e004961401c2140000307030010b0310403500c180c20050110714450710f200002602c280604050b40c00078400d031900c1c032001c00c55109105c8580f500354041c0344100000740030402c900780701c000c9591f4014100031f0110134040c01c110042c0c0f9000120b910210325220342c1d210030320005200d400e007400202040761a900d2000c9510342c1c0e40c4145424000b10b0000003042c800c000712004201540070041041c418000d0700c0c601c0040c205400150001007500d07a010400e1f082c203100d65804c2e034200c0170045090078200c4008592950000f42141000d58080c481107a50640900440802450301c0b4400b2038801d0520b4240424441800b1140d0b21460100b82400001a0000e0447d004003001158201c1580920306108440f0106054000e4044c400d0f141088103140d40f100e44074002020041d42d03900a80ca0309644401341c42d10039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 10314305 1250 10313055 10313057
    0x807030506041b110a0c0f060207060203040e010b0319060621050105060702060918040503040510050316030f0204030b010e01080601080706050906071e120306080a030e060d0605091003031b03 84
    0x40d0a0340901c1805404902d108841190171642c59411540d07500602d0a01540411304a450003003050145907018420040904001e200840c1860318100500210a0040c4105903842e030001000c82c00706803500281003203140310020309011040e994031006100b4480500481c0c1142055030f5610350041ea1806041c0c100d4400514040c07c01c40580c080214030713404040002d030320118009c0e803040404041e40c5c0700c43c41640941c02440d1251300d4201881141d040f5150808204a42001009803008601300315003624000c030701d000114600d082c1c2d00c07000244280c0e040a02a01521000006c0d80b42c2c440c50114103071440c0e942983e0700303642e031400344aa03940313041d00030b050100d0402e024503215070519401503c0e4007030181e00741000c000c1004400046924100c0420340d4403900c1080d4001030180c0600070306004140142c010200003071f241c1c9000f8100c00012060f2803090384005411060388203950050005004010008060b608000f2500e84440d41184030031400308000d01c04034181454407501c080e8000da01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 10315555 1250 10314305 10314341
    0x71205090d02031218070305010b01030c03050402031c02030c070b07060606030608070303080402060409060603020c0d0908150a0b09012303030f040302060702040e030a020309040e06100303050a020a060c080703050604 95
    0x16114645100c0303200117201000c52070360510441c0060703100b000410300440c02440000b4074601c80600050039114010008010701d402c11040c00010b0b2000100660b0400400c401a4600112094124107521560816030030601c20684045804c0c0450340052140e9403041504014681e69014154140c41aa00c1210210340051000700f01190045100c69481351008004070318003521501503a040320100d4012000081c0c1c040b5417007808035010050440024000c1c07c110804910304204141d0341d5488652100e018074070341c408207140521a400ca064400e000030310301d010740c1d2f8440380c4045c080ca461760400c0f500c03140014141501402c0110840300030b4903412402e81c0c81d2500316000e009072a408544100d800542d90360034121201c4040c80a031011070b030036501445e501c1c0d10400800080e82c051042e450982d401103c14854040d80410751441180d52505040307032074566201c01a82041400c1001030000b03401d003030b017001d02e03503901141461080341c0d6038038108000d8071900c0c00d1000300c03100c813031801258100d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 10316805 1250 10315555 10315567
    0x2c0108010e01032103020c0703060c110a050d050703050c0706080601020d050f0702010c080c070e0105040605031b100908070e18010203070918020403081902060603030310090b0f03010203071205090d0203 89
    0x305141044c14050080c1c1005032500030344a4005107894116407003a00c0d1250b032900305242c5a41e00603001c3c00d4230b07003070300c00200030003101c40e02c0c0e054a03542e400103500c003880b0001a6010030107000b00d044e50300401c6100103071840c0b15964040981488400c0b11072034010300402050843d01ca0090068a01410419090030709002d29a4019680400c1000301903448c400244800d0340c05050800c0030b80050076038600b2101007545440c09000032360b00140c00c814425000054008820b8a0356203900895030000c4031207007444000c041c000c1c0c0b04005e0640104240c3e000300400841d001c4140d5400d0b50013140c0344520a0002d0389403910307290807404241c603a1030000f4000381013009085130340540c0c00341486056000601d869582e60310004240d101c03020310f01000300a40b8201c03045940500c00643d0003c4203402031803440c40c00e41c40440c0c041600303006141003955503015074180d41c4c6031500020f2400d40050001c41d524101008081d041541000303841c1021804e0500240500102045030400ba1846400850601c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 10318055 1250 10316805 10316843
    0x70f0b0624070f0501050703060503010b0402040b030a0203040204060b03070503090709090b040b0a0e030a0e0306010602010b010c0b0a0b040c02010b030c0105040501021e0307020402120702010606030203040b1302012c0108010e0103 101
    0x19100250a0f1499840d000c1c030400818000c1c480d2034041c810586000031600c2c5008181420b440741103d800f44034600c10310040101c9400041220f6204070b92804c010307030300e030395601c0014000c02d401d03004424402d001104000901d5040402113014a100400f100c20450755440050151090b5800041030045400041000222250459034000d0145071012450b06d41c400340c064655000925074000281c90804c85000b01c1c1000d21400d40540400d2000f400300d5008100041c03d0310000c054018810404040003580e01180d41c7d02001c404400100180f04081084d04000c1c0a0102600c120b80300e401600340c03071030b03466004004580450b417040c1c000d8002c00041c00c480390201c0207808030408441c04104901d0300141e45602c000c00c0f00c0c121401c110140b1b03081100009007120316640000051500c10002c0c800801c0b003000300568000c0000780c0182162000d03100481d448800180f00f42c100c0b0040f801450718900d8030803c1146013078000e030307104041d40e03903502c410b07010141c001c0c80301500003c503e1499480320 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 10319305 1250 10318055 10318057
    0x10f03030528020a02040e060907030305070302030c0d0908060a05072a080d0c0219050312041109040c080c091501030b060c030d060608060d03080a0b01030b0303070f0b0624 76
    0x74510710700b154110032500c002001624644240c2d000580007000240b045261074840d00300300c040000d00501c05490071581003a41c03000503000290500802040e1780307003010302c2001103c1d603000301700c81071b9220042814000741990041d805514040d00454000458010003440717054456003081d40d03000360103050608560210944070082c00c2913541d040e000d600c0070401c0710380104035140212200180103002410020b003024401d001404480d040c48040c0f0010039400801d8603800548000e0003403403525546800c203003182c1c0c1541030a4001244104120600034513109200031269908182c1c2c000000280810900d10300845400c452140b4211684242e540719038031032480d44d1000b07041e01c2c0c980b4400c40215480d5402103c0c0c1141d07099156403003404201e50054903207800c040c09035906141942035940c0900154802031000510a540d02030400c44d582c425000104011000341c00d41e640c0b00300c242000c02d409001200f00346c4140c0300c002c01103840340c02c03c0c51440200420750103d1040a0000219005032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 10320555 1250 10319305 10319317
    0x3090b040816050616030c170604050a020c0a050a050d02070302150d0902090c130f05061e0409090506040209130506070c0203010f020301060201140105030d090603050603011d07030309080105010f030305 89
    0x80302c600891800d00040080001c18041c0d00380003102c0b50241194a002003d84000d00440010003000d40105150440d03814801c036048402240c0102e032903903919a5003402406164500080c81c42002e00c10028058081500c4400030300800c25590244000f4600360f940d844030b0710000b500110034121218403079103240d000d004410f25043c80410040303065000910f010700140c1e51142040000a201400001844e640000515007600c011449918000000d176641c0034424051000c4444248a000000300c0e400868000d0410404200105510f40c00d066668840840e0120b006803c05004600310012512140c00c0259002000f0100341e90fa54104848000c0c080310101d03015901e4054000900341c40303002960181c400c03a800050803100c0320910f0000c4c1c0506038801400b94111140040032254054001c100340c1d403081c1808102c5807600c1c40401d00624401c0c0700b042e0030400c001d82c3c080c4116008107086c41200d0007665412200c940b00c29405007290030a103d4409440050102040000c1c021030250032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 10321805 1250 10320555 10320577
    0xf0309050f01020a080a050a0612021009030b01060f020c091012050115090b040b010e0a090e030d0f020903070f060813020d020301050723090d0809061e0301060f03090b0408 76
    0x2a0746030165015500f640c1010310140b01040c52a010408411220307c2101c2e03202c211002e046c400d80c0e1400c052001d0b28004114064050320a01452500c8039014943d0080115171010328844d2540e55034200500003c00c0f002c4110060294084003142441d1054006005409502103180710900e400000c01950041a0007220555282c03059545403640c084484001400507480200c0c10305100820030003280d1000c0300c1141801002000c404c80c580380e5002174025151454030005040f007100c04058511300486540014260400c00300307003039294494002e803202000a408841c44152502ca100c032960006008420010b916200012060503002c418410410f0020f00028020215500420309641c0211001c1d8041018a083c2100070707070500b40003422600140380b50074180382031800001c40500c1c0c0860080d00c000030200c0c5a216680d902c0e4110780001041c100f2492100500c1c0d0034289041c0c10900c03074000401e5100c4d14121805020b80101c580c801d5020611604079603540d581d0103c1504099035035070f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 10323055 1250 10321805 10321813
    0x5040507150207150309030305070314061003110c0102040602070501080106020312100506180901090207020609060c010e0706030603030210020304120c140706050301170f06010b03040305070c0b0a090906060f030905 94
    0x905620804613603021403500355000324212400f403c0280503510050003800030145032580d19803032140300340001c0d908074a0072207810f0002120590200c0280910a0f007401c8030240010b56001c0c80c420540c024412112140c003502e17030642d540c00055580c03030000d10604d00581c00070071420007418100010030381d01c5248210692141901c07600401c00d103801200d22007643c00a01000c1d1100c1e86404103002e80141100c410075441c01c5655808128980a08805a402501c0c042148485070b0000e40010344c3c40c40c01c010450f03050b251744020007005040340344400d40146c014103480481069140c0202d0744034641200c00001c20342504182214201070301c4100342c1d48500d845881052240050200400030301ea20b070398807a00e03941000b00c0f0b6180821400703042ca402c0d5001c045004940c810105003941140c030750f4840386450f681c80341410740d41c034861050018025044d02c0c0c008150610079802501c4880416580c060400b078070342d049501200c131240180c0000c5080300100b07070007052003a048460703494494130030b50b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 10324305 1250 10323055 10323059
    0x3020a0c0804031202070b0f0a08060f040509030a030b0306040807110f030303010f0f0b0406080f10030503030403050a030e0a051e0102070501050f18010c050703050c1c02060709050405040507150207 87
    0x1d01150400d82049a203100740984144520340d0400c012400790680100292401e0042c03007201c2600d10480c0c4000c802e022420001a482e0f9a0306990b01000d44d20240003031149180604d074440d12070b1712000a407000710346450000451400c0004a00e8899603100c0501c41c031b4800180c54080d100d00281804d694020810305041c0d0140d101403015500030a01c40b03400081030350030a20103102c1c032215900010156031050104001456001c66070350b81200018220550780c2d22140540314000c4c401d900050315511000007407004241c3d02c0401415a902180da003000084122984941c946c0500040902213a0000a124420004081892a02c890020001803800c0b110307582d03075420b41e001214001e103181240400c02103120481d4900000e400c0050008100f403111044002d81140030b034400190400101141c00750f900c400030844d680310080c5400304c55511001c0c480009583d8034040b68003a00040302d01c03800092038141401031078021640003003c4c095160606c03240d4000ba00d07a40c103070340d000c40c81010b00c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 10325555 1250 10324305 10324313
    0x3060402160b010801180f0605060a0909030206010504050a0509070302010503090f1006030302150f0a02090d021e040e030a0c021017040507030c0611030a030b120318100905030d03020a0c 82
    0x1c00c44086100340002e007102d40c9803035040ca007110034044480100400d0f03854000001084049005025079202c1c3d00094030741c13a6030000c55810f5603150811012585403142c05e8051503000252241212400c680030b000300c0d5034649054040d100140c822031a15841b50100b40015800b910203941c0c01070180d030032101c080c0301384018076142010002c9400d40c01a50b814090003415414484901108050039555030745040101194051800050240744042c2d40031885038219511142100c1e0007940091001301141205010700602d05000c000c0b40388160318000f9030071141c1c2c0000c42030b500c10003c9901c41000d44000d68003440340303a81c4607001c003504105801c190000d2420000605a0056004000910702c103411854040c0e0885c4544d004082440907080320b0580c0000000300701d42048115186c0414803c4580c0e000c07400c000c0c0013810840141c0000309501039500001c5d054010a00b900702c4802c1e0300c1c2d080c9504151100709150280a82541100050f010010f00940040900c02d0080c50402006030064403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 10326805 1250 10325555 10325587
    0x903050d020d020c0f06090a0b07050702090702060f06040b0a1a04030204060f0303020c06040e0c1303080a020a0c050603070215091006030303090614010b1c0b030604060912080103020109050603060402 88
    0x90b4002010343c0810000451081005049149a0482d000b00120b0921140d03103079840c65000802030000800d040000d940c207204a0581e02c2c4294050700c019600d0619441c080e4540004440c41d110381a081c030300140540ca0580a110000300c0e01500d002d010900f404421b10f1110f10344d401c4545844020032001005031100e1041703000900c94148140449170440c60024148150001d90314440d40c410f00c01400303800f03183c2c0340442c3c2290720444187d684940b145c111050724000b03a440038201c0c0101013901c04445401160042c0c0041c030030300c009030856480b03804005107408240c0d0f401d00140c0c005109081c550703960603034403600520b070b90048a403e203003585081c006075032494004800280d1211290820040703a0f000c0c1080d11501180401110360415812410318010710015543c90000b49842010080d4140c4c0303d05028036029094880500e0607080c1100607000841c000c4407110703000c100d482007c038494002c80c0e0580358141d48400445207004108546500060800391340240d00700301d84074494107110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 10328055 1250 10326805 10326817
    0x30c0d020c0a0807021504050a06110a020d0b010816080c091308030c18040b010c060b040b0312030709080708030307051803060708040b06010203040302090c0c0a080408060a0506040b0102100903050d02 88
    0x265650703240c5031042c0000d0801086c0b026110040600090096954140e0000261002440c0c54032641002203181464100e221001079002583c84103d241404200c007021410b031f519220403138000f8504a140d10800d4003061003040030700d0300050b40e2078a940c9829501540c11283c011890760942080307488440d981c0d40b041c2e4508841c404005a0407009a4480d0162400d1b050201d41c10850f10003a140042c10032220b501c80144010b6803464600210781d1181e10a1554000183c03ca90350040d4111800c0126401a5005408141c5140c000110000005010b20a0b1000c15001e107003151a10501a540e50b0045541c0240c0340000000e180c1407501e0401100c1e10502a80c1d070340040a040030b00b04140703070000180006045400400c8284050f8445040c6250801400300505503500103038044030342012040e8000401010b0005000501820b00146484c080c0c410302d8000c100d542c4410301000201c50180303600502681040640316185285980105c11040c00781c2404d903c2c20000d1040e61040703070302c18 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 10329305 1250 10328055 10328063
    0x30903030a0e01020601060c030c02130213030b0f090106031a040c03080a030b0a09020a020c010c110405090a121d042309030703080901020a08010509070504031707030e010e06030c0d020c0a 83
    0xb004542019a81002a180109220b0415414070b0b0802d4900410301c02115001a008000c207862829201d0401d0f41101c40c802001c0040c0c9450580341d00d0041500b10081da460243e5801c8080403c0c103006040c41814112588034591b451542071b03890003445034070002802900c60100301030000001c00c0144004003c0d0020641e0700180300c222040c104508140503400201d4031520520010350841d0700010050781405090078103400780c103050315000b00d882e2032628945401c6800e240500001c0e60340080c072250307418420250442541c8440400300c0d04040c03c0c40c02140c03000d001c0144808075081582c485002a400b0848029002403000e6800003070480c29101800960b01c00075004c0c0605922840f190703084000a0002d41c07800402d40001094202d060145520030001800858411030040c0201c1c1c0013180d208520080304412034401c04081c1e0000c550a030041003c1052200443d8440e040c240c4012100514050540d11903065442c13194100c258142c114039801c1200301002d1038208401c1542d03501c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 10330555 1250 10329305 10329317
    0x1401080a0b03160e090601032301020c01020a03140f090a030813060504050304080f03090a03080901050d060303031505030d0c080307020c030609010e0706050c030901030903090308070b01060e030d09030212030903030a 95
    0xa0001150240324005008240940000c0e0051000511440f0403100042e0890918941d524a0903035541c02846130401c40c030cd0542c40090000e44140e015082400c04003c030304040c0f80c40f0b070f80c0d05003403e0000303030b080310407042079002414080d0020f03000c0c440254200048490404001070369076154412101c003a24190313125030021400b00f007001810418404051311780c0b8007a609010303810000c40c084109500008100060106041c0c24991003a4107441c803154071440140840c580c5e034100070303004040da43e03030084002c5150034000c2018180013075504120022135580c40000050f070345914810303803c00b61080c400c50180084881c60350b5000c21149000d020344c0d03800000c0c2166000d410a2a2507081e6100d1424844240004541e483c000710556a00c01b100382804101700b4402d1034119402011a04000c040b1030b40401c0344020f00141414560680b1401e071104d2010b80d004808155681540c0100789e00003ca003031105200500702202c12070001c0500f1421079042151510021303080d034001d00446000100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 10331805 1250 10330555 10330559
    0x10507020601080c040612020d0203030708040f030c09020702010206040b18030c03120106020607050f070302070b04090207110118050d020a0b03190b0d03080a020307200a05070902041401080a0b0316 87
    0x6050012042c5201c4c1101d0802ca05442c080c10159a5000404007a102c0c505c10a480001c4d51418030480703080e10390042c4410341c0d6540382c0c8140014500d00e8003060700c0c622403128001c601c41d1014421a00c0890301600101040e596076070366080400402003103c0e408808122500f08403640c03c001401d40489640003954035220507809080644005903c08400c6501010034408056040002c0301d0781c800d01c5c404007070745c0c0707280d20304040e0b14009030743c3d00611003e100010002000d00041c0d02400005204a84c80204c001c141c43c01150101c0b2103d40c03a10190903590003c005c1407801c1785000ca402031001c0d10180400c1e5448416003200d403c1140c0154001000701d030000c00c2601306206600c5130940440c0c1441c40070341c081d00c00628120005100f2002164000081500a40206000f0b0020040302c2032940c80014820400341d150914501c04031841e00c42c1c600042a100d2440c001c0d01e050b51280c07114081380540410045904c1e00018007283c0c1d1031540c5240d02601c40c0c40a0102d0040e41056001c81d1000b14 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 10333055 1250 10331805 10331819
    0x60a08060c0a1205131209080a08030103020306090c010e010324030804030209011a07030305060409020a080709110304050c0f060d09050d0809030a02100e100905060601030b0105040b03040312020408010507020601 93
    0x1109000e00340000900d8402000700300406140b03c1701c3c215420004800c1074111850302500c071008103800c11601846062040d0f4200a02c0320021030503a803096054914030b4481d0401c880da5035080e540c1241c04146641e075043e00039403203075100d0031010710420780300084001225903102e0b000901ea0004d58a40a00190a10640c2040f9400781e004014a030200326404404441212443c000c010000301050340302c60100f5a590340d150442d04407076400034041c0c81ca459640d16801e6943c07505105803e030f01400c142c80f0601c9a2803403010f0320310840d0001c014041002e150020008196012802c440e1b000c4414802c205900070f452040f01c0f80c043c0700354028480b0381420b45000d046480c008002ca00e11ba8020080d20314141c1c1d020404002c4140d2080022a1013000042214200f08241d80c0e487d070603038603240c161000e01c1400511540214800c2c1c0b07040100344030301001141c051040780240c1c51000810000301c2c0000b07104010010340030800c0b81005081c15180c1803102d09440043e1500390050f804000144208 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 10334305 1250 10333055 10333067
    0xc12030f020d05030a090204140906040623130303140901060602011104060c060506010e04020a09031101080105060a080702070b041503060609050a0306050a0e030a09060207081f0203060a08060c0a 86
    0x31184500051044400c0100000d00e0351000803e2824400e49a050100454440b0b82148a28881e81e06031151145051401c10341ea0344001c5a0545400703003060072000c89000522280002e402c09450404038070381e0f0740c0045a42c0303000718070001c504040c0c2d5104d0f800e41c00c4109900310340c0075102440011507020300d0003031b009007907400d0320320075068034030040004001c07503074110b02070301c02c8180d0184010032150398200c011b0710142984520316070070038000071303421110544c44840a81980e1060311008400c1541c5001101d45190034092a41c11590130050344000c1d500801d130546d84010b00d44112848d070382d2200d48100340c0d508543d20894160440748044402242c05014800c00750100b0300d00f4003c094a40340000f40311003824400074110b03a507160003081d812001c03500404642c00d030b000c0440c0d503500b40422006000e422123124142c0103016621002c0341d44580070480f40300b480c83c41c840e040c1100440007280c0d00203600241080b58800080040010914801e1060710320445400301c4154652050940c05011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 10335555 1250 10334305 10334327
    0x307030f02010b0105030103230601090b090112050604020d0f08070311010c0c020f1302040e0c12070c03080f0910050702030c0d02030708041e180b0f03030918130c1203 74
    0x1e5905146a81ca126640101030782c0c112900030000146c4403d80003550a100d240168090314540545400841c420809802103600904107480280720f503a030f00c0303e4620140f40d000200070180d0b08104081005031030900b190a50442c001c0b00007032a5044c5039641c1d490039902541044011800d60341010305120300078803d80914480c3d5041c0124807110755400502d8448050301e80611560304c20103468a00d900f185d041d58040c000400801c482d07070400840f2742301d00b03420000105529034034234030000c0c1925100d001d001090940c140c9a098864032494042070404500418000791442010b0045070642c00a004590040c8a0754018682e0343d45040f022a08041102446e4015075000704000400100d84004441c201d4510f401030b076134090700d690305d101504211544120000090f081030326071040c070158419101c9850840c2c0658014034464107060300c0303005080c8525489000f642c00003143c0e1a0340c54460750300001500441505440039a25200500407030703007000b031104402240410030542c1155100c54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 10336805 1250 10335555 10335557
    0xa050402040f15051306090f060905011a0d050403050904050a09060c0e030601030b0603011805010c080a06051309030302090d2009010b03070c05030403020904052104050303040308160b090307030f 86
    0x10400e40b088540081443c828410307103004040004400507002030300d62002c000b811f10076900348481652810004003502e842d010f4440c44070f1070b100001441c10a085080c88030210440641c0741040e2403000440c004007001041502881020400072400fa5510f11170342c1e00c41c020304240000c2d800307518148501120a400810070034840308441101055500050082c1140c2d4000140c011640ea8507000c00d0241c104c400240ca102c1c0c15200143c41040019000405d0031107a90351140d0035560b0760b0508005880b1644101078101c0b88410742e02981e001e003904070800040c0281005880c0070003c2004c0f400c250b6500d002a50110081c030404908001074041080040d00203c4400c105075040841135000e81c8000740c418004d1000082c8160304125040c001c0d100250b40040038442507143c203042450300c44859100300859181c8141c42414416040420380d01690070150045003083e041d666001302981c005074800d002d000b6145d00c0300b40000e541030509481007811601958841c00c05160250070b12641c0500e000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 10338055 1250 10336805 10336811
    0x50406060509060303120a0902060304050703030e0105090618010201110d0f0f05040201200f010203010f080d020a030207150912080a0206070801050f1c0c090209010e01050c0304030305030606120a050402040f 91
    0x2c03d180d50008240d03070a4000f00c14140300b1030384800c0c4100c0010030303040a0080d0010f00200400003402320109845048034040c1d1940e0880c0ca18800044450344100584035612040922003564650003100d080c1e1408041800002900203091101802603080201100003498490b1180704524005002c1c5101014110005001303078249030b400a003010414600b001c200c007400d01252424102d00700305500c00141071400071556941c507038451a4a5811500640e5000c0c442e41206180c2107200098026001d030305030b0301801d046410040326500384a0021920004c01030155004640c8015480003800d44074442c2016a42e541081c000190501c40010701d803100b4060034900400064880000b849030805044402002d00c1144a04055a40e03006103406400303607000010205102030039030f00420000c2000d80781e5190070101c0c0001101c1e184103030525070740d05810900c0100700107401880078581207c40145202e040c00c90128000d0303501c440845031100210340380d8042c4400c0d8202803084040c418280d130024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 10339305 1250 10338055 10338061
    0x4020901050402031012050105040c050105090a0b090307090e151014040c0311070c03020306010b0a020c0d0302010605030d02030d060b03041a06040e0106030506090d090e0c090a03020d0303050406060509 89
    0x8420100500c1607500843c2c00000040c11220b1020800d07020346280100e581820b00380d400e01070b00800c82160210342c101c08058021803950b0061082d60440000240302860712410580b603e0300b16040b40703401c55094841e01c44c3c00b04448005010354001104500010008141380c44d409130381c010380c05801009050100385007407007400e1980c00f00c01103200041d9000704820848501c21401410441c081d101301c00c3c00800d040c410466007402e2482160b000704c2c11101d0320790329129030000703e00c1041100070169101c0c800e85110360a00003203800c0c400d8040e00001882d0707503031a0042400c1008440078000140c0000074044019081486a4400341c0a0310040034110318059641e01d40324032400545664440102000980ba595990062a4180050030081c401141c0d01e182c590b83e52101911030211034010004910103052041e4481e004444116503a0744907a1111044240d080d8080d0803501d42204881d0000b0001d6200c0380c0462010034480da50000e09c41c607203800c00c0c40807120160000b511401503070041c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 10340555 1250 10339305 10339309
    0x1305040c020a08070305070b0a0b03010c03110d0b130501030b01060201061401090504020304020f0301060b070201110610060507060207051209130501030209190605130207140601080a031d0915040e01050402 90
    0x222042c201d03440000c05503038050b00d050680305401100e000814031003000c41040b08030013898010f0381d031105041c1c0081c043c1e000840e41c10b9090724500c0c8000c880580c42804100c0c42000240c2240c404107001030981101c009404c8040015194240c00c2030321300c220781b41c00401507550b091003180c0080c40d6604840031802040c0c40020300c41c05407482803070f1041d900440490b042d96500102060481c8c00100200049603032144115115004540268041140f03041d6000b2800d90110324280b0841662441424050510350180c50f00e41001005880b0300e503003402454002182000304608000c1031403003568603020038404002c4007040e04c511a403401c50070600100300607118499100e80001d80004e80b20341030180c0c40440390090407e940120742c4600828100c00c260b1210758003c10f852400f074140e07040401c603201c80c2a1f5a644013849010501c1e4006810040400d10891000010344010700d202c1076000d05c40350025a42400a4440701840e01d0a0703200c0442c6ea00c0e15100b03000c008038040000340114509600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 10341805 1250 10340555 10340563
    0x616050a0c0602030a0e0f01060504060b0702060406030903050d050403020601030c06110c090a09020a091d0303040506040210050910090905010812030412020312070309020406050d080d0c0e060703051305040c02 92
    0x700420440d004000f0401c0c205842c0c22010541608008039403400540d0100380d40a0705407131155500551401c4030201d18402d520701122003954000e000c0ca0302d020701d042c4040340101610321081c0d08000c000c2c088000e80710154080c040c090b40c06a401055994154100740390004507582c402c0084c0000b6096445403808040b44045444104480c0e451403580c4000103100601200c1500035032017100d501f4089800301441d0f0000c18840e080320100f401203009c030410195603102c01c2d500600130398000e100043c0146050b450340025040145800703400c240d914404a8040001d95503403801103000580103000c1c12506100709401001e0b114001d16031703484000340320b6919105c00b5102030b0150010080041e1242c0c002c0040700c0c0d28442e2002010614901644014024448400c04a00c00c5051040001c0c803803903c2201066003130b0704803401074900900c0b20725400040c000301c0003e1090114450385100569500c0b0003a19105019454440e55101584800b4030081050340029202c0c502d041d2981c2c40840d8009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 10343055 1250 10341805 10341827
    0x80405100903020c0a06090e07090e04080711180f0604021614031b1e0105010605040506030603010605030d120f06030f0201050d0e010204031a090c01050f09010306170616050a 77
    0x200c400146401d030782c14100d0078001101d040642001d02d105001079030540c040e1646044a0039000303114203d8840c0e18084610484522036501e1001c291000305001c82c5290001303150301846507003034150881000001c21000c000c40428011008440b104000e000c0c81c480d01b1f460f03440703141280d0841c038007a02c0310242880704001754009406841d040c286415181d40801c1101c61010054114042c91501440042e0703581e000300a160714441c25403060b80091750014014141660350319101d4500b03150400d428441f01340c000804596240d902c809000810b9182801a001921b600c1da840081d01080005864203460f0a0006c800e18140b0304a010000314000061011203540d0902e081c6a03502c1602984d20060075826440d24615480014008200529101c248803030312200441c5200d0340c0d4401030303030740d4644001c42031160115901708610f003140a0326030020244c00c201410006140342c2c0368000d0b0301c130011071820982d000e548100240000328540e42050f2032845c58518050b8500b420103000142295055 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 10344305 1250 10343055 10343083
    0x80405100209030115080c030d030606090608060102010219081b130347010603020306010f0e03030c01020313060b0a06021009061d0115080c0609100c1403040303030507080405 77
    0x201d02810b02d80d03429044421520718050410082e81e8544416644034940c3d00c02d041e102e031260110301c140d014040c0c055030040b166592515603d5502e080e0080e507900c40001d100f01e0455600b00000c00014039034081404030420b056a45a0a61810081d1000f00302503e68004140b01000d100301141c1a0740fa524460540e43d006050040e1886410101c000800c2c100034ad85292a400b00c41204090003c1c04080c81da05000400441c403d9070f84500a070201d10040da0a0390000710050018a0524010f119110b200d803000b800716494603004100e203500720f800580e500607900d200740c40d4003028000503014001c2e100d08103c40c11071440f49814006503840000e02c2180610315191a00442441059030001c1c004001180c021a502c540d0050024000d00c0c2100f0500d00c0200f030414040798250000640c40c80542024100f00e00d031404010420007149041601681001002c074000c40025251090382c080d074142c030200954450b4198500035066440082c00e030b80c10055502c1c20080880d034001080c139900103035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 10345555 1250 10344305 10344307
    0x60906070212030304080a0e0111061303090b0c0c15090901060311160f140f19080f040807090b040207030905060c07090e0f061b03071206031209080d0804051002 71
    0x944080b60300701d0801102c8903100c0c00040300b0401405141c800901d60702100766070350440c0541c0d42006651102e40c406100316540c2c03202c03000850403003603061301085180c002d040c52481c40c0c0e960085140c40d42c2c020b030741e00c1c519904280c8001059051148a825a02e204091168204002d0401280000d50140300300410140c55040113201400b41c503003220401d041240000c180c0181030305000f1554000e0407001c40b25003000d03031544280642c000c07400d082d509501d00d0140088141a94900002011250098414900c100030403050000b012001b08001c211290140400d2031400078641c04484480740058000c0d8010042440025448050301c6c00350f980440301c0e16228078410071032030305e800c1e071315004140c090346001000c40c10702c0c20001d1100180541d280880b0381c0d681e510007805850914500e12008000024030201c1d04040c0591122420080e410344006002552500d03001d10b48021a0600e00201e046c050302400510000d200c500d908001b541000d4416084c1941c845541c0c0e00f083c0070648207a07034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 10346805 1250 10345555 10345567
    0x2010e150a14090d03080415060303080112050321010e070801060c080c100c11010b0102030909042a0b0a0f1b02011202070614060a1e050d1a0403020706080106090302060906 76
    0x1009078155200f014000c0e1648182c1203192801800000d0241c5090f1502c4120100c07917460b203c0301b0300941060f40d903d559007012591070711501c1c605004040d1005c4509000620070450480f410300710340e1860780c010850010391540b6141010031454005000b0304104425400140600d0b0341005150041c2644118445da841d00035004071401c2088003440d1300842070030709860840055000030b0071b41d810303812070b0000c001a033403032070046ea900d209000d440380d0020104000140401e00820140b041a5080145103407103445951700c140799800c40c1c4c0c016280225021800740140c0368003065841070b80805040405004c0c05040d1409407006031080000c1c1081600e0310f185100c5440d64041e0742c81598403007828001400b0050031184455401c07203401d8041d9046050000ba024807500300d03485042c40001800d8880c83c00c04007071141c080f51191083e40d83c0d415000e0154508254065910310950107540030302192410b01400400d03a6034181c1c08503003084401d079000d1003d83e40e400200ca500a40c1158070302c2d6101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 10348055 1250 10346805 10346837
    0xb06031507121b02060a11040f0e0907051003020a0e01030605090a0e010605061308060c071e0201050913020703080c030907090e16030302030d050105010912060207020d02030601080a02010e150a 85
    0x1c003103070914080c0500004a510300c0c9070000340c05801b6115104040c815820342860b070b800d00d03000d144540650a404c0303c50810148400640281e08007240e0300c1500d411540b680007142d44100582c1480c00020b42c001103c01407281c1c0102d80c0d240000003442d0a200301c40c5003400169440300040c0110b80215943e201645411000350322200c02440c2c0a008a81c807130151490124001e001c0b403049a4090140c10000f0b000b8840320822a8101c65100420020803016012210b91407524408200d0512008102c810300300e40d0b5121903103102030803083d03000d42e46070f26500e00104601030107800e0742101c600034005c3c0869640c0104403182079840358280001c0c0000074401c2680307012010180c0705100c1c491404040140b5901000400c01032200316814003490b642c3d6801140c071210300b4820b82c00902d004110040004180d45c0042401500081543c4511400341e0002400c3c01b00031390008030780d9030021002e1001c65810580022040e41c048440402d809100080c200d00391042c0881030b400c0020000b0f0740e810007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 10349305 1250 10348055 10348061
    0xa0506030a05010c120e0601060c0f050f0109060203090c03070308030a0903140a0302040609080606010e060a030b040501170c01020f03030a0c05040807090209010306090902031b1201050a02070b0603150712 90
    0x2d40020090140002901000c0d01180924084400341d60401c09144025240002c10504941403039031500c4140000761103020792400d9034102115140201a00c0480c0d5500c00d000d40f09189019513030050b6641003008403645000455107626000f904960010000b041420064039802101420081034070080b91030b00f2103100541490710003d10b43c2c00b203034030f082a40e850380c003030010f4a00e5901c400003015111110303076998041c1140c00c180003442c6008a41c0c01414807070040c02e015001400c01040c0ac20814000900b81c45c1c098006070020b40344511141c4a0741c0c0c0401c001e004684085c0050500c0d401440f141c0382d228840184483c1c0c0c11519945102200c0d4070540864004105100c10344110549039540c2c0380182d44503400c00d0340000c0c1040d201094140c118404d0088041e8010018400150565040202c2070000da402c50380c4011001c22a4075464000c3c01403d00c40c50f10800016910340b41c1d86812200441e014182038000c4d03002c0341c054120290900c1d101c980000e4541040e403000c4600c041c0d0b04000e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 10350555 1250 10349305 10349323
    0x30612010e010504020a120f0318091a0108060103180b040c0510020102040311060405130e010f060b030405070b040b0d0e1207050a03080a15050f030a0507080303010e06040507080a050603 82
    0x561800700d500290780410341c001c80c003c1e0302c21075040040c5a0340c0c0c8424000505401e002403c07840203518560002790080900c41a0b46481e188100b40b8140d4541d0380c00d00310b4010511282c0e000d26803941c00da410317603408840743c3d1b44540b00b401c042124080c245031070f641e030200ea1500100b508810310041414081e040445a0041c9401803444080c60758800009001c0e4210380310465038500c843c4074042407490508203440582e203001d00000b0307210341c0c16403100340500146520507406541e079008000040c602c030700076040034040c04c0900c03d40d00e00b05440c182d4a41102940079141812051206100600851003250b441d140319210224134020f5140b2942c0c103240030f14080d4030038039a0000301102003001c00b18224803020f0190f180c01000c0d0f0b8520720142d003511404101c0102102c0d01c580140aa49840d2090a81c4840007070225190141c09603220f9151801e41e4212180320350011004108054100006070341c018010313a800c1c0081c0c00c0000014103401d40141c00600e0458031140002d070141c80030480080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 10351805 1250 10350555 10350589
    0x10c06020c0d09030b0c03010506030f0a110a020a03020601080703110108090c13060302010807030c0504150903050307050606090903090306010303080c0909010b0405101d0f27010f06020607080402060306 89
    0x4840011448050003203c501d21007140c258032000e0010307400e01c0c1030000f500d040310f00103000f00b031035580c81c000e550349801f0000b05003443c00c1e581d51911481261459004d8101d0944603001040c41c224141400713844e004050303000c00c18503800400140001011f0500c0080d1050085c20084800c0d1205c10b51142003038131441d0016001a9070000446e0910865045182160b000783c807410031503210060224141e800c80415100481c4042004003d41c19040c0c0c0a41050b051500d41809601c3e180e55429085900401050720564490780c18004145442d001da150031507a00c1005501c1d0260103004281c0f620b50501c0b002d024440e07882e0005282c4c2d842c0c2c0d8200c9590389070060130001c9660b117035003421055802c90700449005034031007055414190301800d04400729041c01f103468048100902c042142201080311180d402182800c03440340340300c1310203214402960740200045078540c10328019202840711035000904543c02031081c0580690800703601a00302d50140d402540c0c071f035035280205104181c5540e07008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 10353055 1250 10351805 10351813
    0x9070504120f0b070c0c0b03060102030c03030408041a0316050912100504060c030b0306040204050601110f0105040510060e060d05011112040b0a02040303020d050705070302270a1a010c06020c 84
    0x110401c82002c01c050940d9200703200000f441d464011048940c0da5060300c00800b00c41141106012684401c0040c5a000342d0510403285070416001d03e41381180c1043d030f41159221f0300424240f1160300d00c201d04031318402c00007415605518021030b9104602c00c210701103400f401000102600b0f0b0751100e03029810f03195480400c0b202a410340102403001010200d50907520b0602d40058186030380d00c6070003605129080100140429200c1784c0070040140400351011781400420306c070003108244180300b1150251403d00000a45182038280582000c074100c0e0780e00d14144c501201800391102e1220019001034060700d01004c00e015500e0410f00400802e5500340e060800850345194200071252103034400c602c0fa802d0042d490301c0b0001d8200a13405030740401000340c2c120b180070b941c803288214003800400f40500111029a992500072600340300090304c60806460f2012750301c000b4010310a01d00c5030800c100000c10000e1400310000040f42c61100e900cbc0307a04008400b041e01c810320500307805a8180083c402d00340c13 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 10354305 1250 10353055 10353089
    0xa050d180b07080f06030a0821040b0702010506090606031303120e1605060a0503010501051c051501020c0f01080705070203070e070915020a080409050901020c0a080c070503011a09070504 82
    0x42488010202d407480000f882d4407000510103e040b03c0d5450041c0c1d0040d004041043c519640d50390380fa0015011011100c03199503840501c0c25070500e80c0f81c041d80c006c90004007181403282000f401d6590080003036002d10307441d0050003a151102e508495002024000c0103006c0130003450308031051041080300380900ca0409450890303440011402c075041401480509006a42e92828041c0e540100c5000101144017403004100c5940a040145031070000090741d03200321300c0c500c10040202c41c3c0c244c5410350841c2c04203c4000503560100103050703011104641d81764038100080c00003003412000524440801102140e84801c54904220240140601a114460900c1e160600903e440c18903c194180e044511001580340760000c60081100d540001400e454641444408805081e002e020241c01c0e41d420080180200c0050150f00d403c1407140f5001eaa030b40148034120361401901c2d8002034407903450050a110f03100840500e00f1004103042d55600e505a40d0494159214004c60f4802d1602c080d400c01c407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 10355555 1250 10354305 10354313
    0x70b0402120a0c060e09010503060a0e0a05030a050d06170a1401020f03090c030606060304120302030c07080a0e0109050a081504020402070210020a030f0519120f110702030f030705030a050d18 84
    0x900303c240c801950301e0842c040303040010000009828442c0b00e0701134000704042014038401c0d41107200444210402c803460b02d0710f41c0d0358491465000c45050000640046050a03440c902c0c0e001d00341c02010b040403c081025400300200b5143c1c0c0001c3c4000704203145104404001c0714080d0141d441e215440b00c50b56032280b801c01c4500c6e0f207450030030000302c1c400c1c0102070000d107580c5007080603280559003040954120440c80401a0700a5201600f92126a00c0600c50100054204170003401105881d40d110758010101d00000741c010300c03e90f000a8070500c20384805001c50500000e000384280c08034007050003a6203983c00824004d00c038030350010b90408022910032154903000100310000c2c43c440d94441c820900513002c2140c56009003580c1a40b141714071702d070b481c1c00c452181c22031001202d00b9040008114114070741130030480e92640d0030400201d50104410065207001d021142601103990055403500200380c3d83c3d40d45033301c00e9624890a00002044080c000d01c0183d1000b01d01049403684026060303e0360034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 10356805 1250 10355555 10355573
    0xb01021005220b04210203030103060e0c090108031c0c0c0b0a0207060204030c06080f04020d0308060a09020c0a020114070c120804030203060c03062d0103091406040c030203070603050606070b0402120a 88
    0x5410344900070b00200405d10700040070510040710100b64083c5045908595441025040c499000d950a120b03401d5604510358030740440e06e000305800c00003140d417490740c0c103030b1804805803000000c120303580340140c107407410382c1c000041c0b031041c540c03203110f0044541d9442d009030002d00a800016103043d20208000c000c101c001008902600c11940721103070183d0307514a0100414004540007900540c4d05015000041e0040c1c51301c980104e4011f0000d21015100c1441b03204a07040f0203036000090748170440c0d01040d540c0103148181c40ea0a04483e0300e25100450f190640b007c4540d11031024240c0200c1c485400307010342c1038140c03000f0710740c0203040d104142408100340000350400c1d1402e6120b9541a010742c900d03c250b40c4102d0362000c0381c0d60b001e0b8014010404c01074005080c0b050041d1543d6020800d11440d030481800035030b21070b0b0b1207104c00b0b00e0341d10300b140181031400c6055004003061620700030502495580d07040035a02e40c5a440440c021044d030700d0b44041005440d0451000c03569100718040c10080011500c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 10358055 1250 10356805 10356811
    0x3010602060f010b07141c0f090e010e0f04050a080a0207030309050405040b1528030b0702060f0a180615050301050601030606080a0203040203070b07081c0b01021005220b 75
    0x150032929240c44840540d482c08400303200b80d10304038408026034400101002444092000908280e503030040002500520140e0802c00c1a400541c070401c8100410340c04ca08030034003511420000d80784030f40c10010300c09a000c0000c0c0409000c9140403001604103c8200850a06140d0201d945501c61040340d0002c1e66940880c0411400301c1c80001e07001c40c0b182045d200c1c0360302c5160040303010b0180d070300d61759442031078039654041c495000390340300a2080944103258108281c80040c02d8010a05614500380404d40c3c06000d001201190401c0b0280b000081d5a02c5085400051083d000500c3d804404101c1e0040440e8480081196041c2001003140842441c0e04001b100c9090b0000d005581d58000110100c500c2c2e4002d90020580100104556815590107903a201784050700b110445602e40c864080c80e900100c00c22a00d0017000280543c1400500441e142d00b8600d881c0248a1904001c5c0007135219180c10b034805c00740036a2800000e80c4d4243c5181455401c0750281c40b4001d280c002030900b802c10480032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 10359305 1250 10358055 10358057
    0xa03080904060501050f09010f0504120b0f0601090e010b0901020a06060b030702010b040605031009080906070b041505010b030408030703140c040e0f070c1401020702090a0b03060906040302030a03020f0409090602030106 96
    0x40c2d0001002d50040c03045403c800080c105071850807106900644154082d6030410013003240c1440041080c00c0380358421500300d402604144203c0c6400c02201f128458003d01d41c80c100150100304105286282040d03d040d19407841c2c4050b250078405004030300d4103d403100d01404507401e0107800545002c0d524000d5010380c400f58000d100e607400a006100070303228644503054040e070212001e00c1803003880e903100c01e00051241c914240f80103401c0c80040c0b6190040007056625826620a000c10000c2d041848040c4426891003801250b00d00506a00d40c0e01000308041c1091000200054400303119600003210900389002800003030801d1b03255901c0301e80040c0198441c001800001c66512030903070451620903000380d5545900c40f4401e56690404001c1403e4403c007a42d0284030132001a982c05142a104201120000611240c0c400c10149041e90142c000100b41d0440e009000210b5030200c2100c0040143c0d08002d42e0b03401d4000384c004100e1103103a021505070380c9800c4458013080800d0700218101d91032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 10360555 1250 10359305 10359311
    0x50313060c0b090a0b01060f05040909050c011806090306020a02010b04050405030316030e061b040e0c091503040b0f15030703060903090503160e040213020309010903030606110303010509150a03080904 88
    0x50400e03201d5941c0c1d200400580b00a0000d1700400000c0d11503518060040c0c8249400d0342000c1e59a042c1600b6030720201011511604040d070850050b50384080140d00030940c1015281c0b01600d0410060700d00c044071b00024080c143c0002d052000305000750002d421400d40504100440d2a05081003900c0c0c2e08251030040c42258008100003240784a03025000712502d80001909654a402c9164159a04022100818070406100018098001c013140714441c0702a500d800355140b01d9581002000c5480300d034540c2d48524144244800705410200d05030f0300c401840031840031034a940c1d0800c8110210204401d9042c41010b1002c000c00c0007070b4000720741040c4a925413080b81c0303880f83c2c101600e0301c05402e804080c4008c80c0804101134894080d041350010f00144c100c1d140b20100c0c40118040c2da00440d1211078580d103801c2901c040581c90311851008154514095500340b504802140d01da00c018030400744102c0b2514007007100940c1c50800c1c1e00003a28002c0002610780d680780381264203a04850001c42c802d6107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 10361805 1250 10360555 10360561
    0x5060702100c09050607060e0312040302010b010912030c05010e030403080702030c030604031202181e03060a061202040209060c0114040302010c0503010f060503070e0301060f0305010b0a0509070c050313060c0b 92
    0x42d00a076100200203459010446003000c0c10f21981b5003140740165506515044403420041081c40104840690100e0810b4546003d040182c2560300701242641003024400d8100600581c1740400ca11195041c0b0302441c010710300b42007060140402c5404101c1901000400100b08400c0e1001889214401c1c0d06644200c0c100904060311500c0c00c403400303404192414a060b20540381640182014008601c0c1c1c4490703590100041080c1d030202c0c10704803041c080b261306400d52074a000c03c107a66001c25074540c207110142c1031100151241c1e41041d4028095600452030000301d6850105a4485d100c1400080007011820340740406914000c4d5004e40140d460700e401410390502c604101c034180c8420110f584940d0385403080c03c5503e5400141104200250b407640f10f8010f9130300b80104001800040d0b850740265085003002c81c00c4544c1c0c02d80241c40788007502410012601c4440340d1582c00b10b050f0600401103d00c5050540c19072040400c80e84081a4600b40421442c2d00051140b0b5114064000103140796 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 10363055 1250 10361805 10361833
    0x7031104110405090901020c01060b030a14070f0f0302070f08120702010203040b04080702040b090c1e1603080c040b0d1d01090f060506030304030c090c0f0525020105040e0405060702 80
    0x1d01209144414000c104014009802d110b510550403003d400700052610a007182d41d5401c485280d00881c1c4042000014402c0b0300409014600e15820300c0e254201c02070904400140000785003104050600c25806111405280240d0584900355007041c40030320b91006a107404402c0d80d1148017140c041001c2d403404900164414030030385c0e1080b41d0240c2641403a841c0c503161242c03e40c100c1c0c08102da000e40c88010740b08050321059180740c01810901803260f00d4102c0141441ca20000410039980f402d40e0500407541d1114a02442000454160400d115203840b9068007480c0f622840e0006140e000000600004421450b4041603d0145035400341c028031010012007401d0b241440c0003d0030002e0b000c0e000001040c0079a03c01034000c800101202d107031654039611240b022407141c2c40341e07024a41d250180e41c2c1607038011004030614145403a15502c1e14070310f90031402d20300610003100c03c291413005485400310b90194046401a00b1202c141d08410719052406681c0c2c2e400c01c95a0f20010300031040000494 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 10364305 1250 10363055 10363061
    0x10801020a2307020904020406030204020711010201060812030115170705070c0e0712110d0e0102071b050a06030b03010f0914010606030203060d0f15020a0206040c0b0301061b0609080c07031104 85
    0x40b602c40002e0346040b002d6000c0040e0301801400070780e80640d0b121000401690740f03200400c983c911980d64421410600800603084030000c1c0e008800c01d40082c100090f081c00640308427815a456a070b426003500110030400c507511403480c416402e01242510030f04c8641c0340c000020b4607110788509244d0714450703200c91420401c150192158070104002d1440d40311400400e0b0411044180682c1480d41028080f011210540707801c0200054180d5001a242c42448004008014520100103580302054074000c00300c0c07011400e80c442c8004155070350030403080c0b95500713401007130340016420010301001e4458280412060b490342c2d50bc1c04139619040c00050b0385400b034000d07a07126820007000507803030102580715007690240408040319216000c0581c2c41034801944094540c6181c1c50340185158946072811302414945500040a000c00c00e20040141070703440381c0d20170795080650880c15010995854010003911401900601c954004035a00d8001000011500101c1c0c1c042c41800360f144019900348411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 10365555 1250 10364305 10364357
    0x905071e0e01061224030c080102120c03040c050d06051602010608120702040b04050406060509010b03040b070f0507060c03020d0b0607021f09080102040b070212030c0622050105010801020a 83
    0x1884030003801006100c0c011401811a00344100d130210f40d403c0580c511007a40b00f103003e0000340000401d01d003401070100d0f2482d82405048581c000310f1a11608884c00808404010400280b1041c00400102000140c5107421300800c4090842400120320749442c0c8c016040440700002c1c0350203442c07a298071141c81401a6011030b14040041c100380d00b00c507916409190b01c11082a40c01ca62200104c00c0113071503620a0510507401400c1c0040c00c41d09050801c0086601a4040e400c0300c4814400d00000c241c130400000d400030098105150040c0311100c055880380140d12000e02072038070340300401c07000c41c1d09600105400548408104400307010101040b403540074010020b0b40012543c141e068500325148105d200460160620450156035943c50509a90094110142280010402d0320071070418403409514490300700051400c041c00716691942e5141c000b411420030412448a00b00c4610020100201054000b8024000d40da11684460301035071209080780009144c0710f02120240907500c443c455 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 10366805 1250 10365555 10365569
    0x30d0b0409030804081317010207020114030106050f03101d100b1e03060406030203030d0605090a02030103020607170d020d0e07080a05071203030b0d06050a15080d080405010b040905071e 82
    0x3c2d81d840e143c584402c0c5405c0340201940700c2c030300034501181d09060740901e50720010b0001c1c00543e42c0c8a841c400140501640c1d40485008041400148103aa400c90160b03441d20007c4030302c060700d80d91088400da890440c1580402044414401c01501c1e0a00c4007009520482000b1022418583ea50014280612902c0b070408001300f0503070008805502c0030345c02036410a0b40140089019a120340011b810b40d4800300309003011a507116030401c504d007004490300d5881814030b50b0442c00e542c0341d90007140340c510442c10000c080581d0802c515005640780000e031013940580d00c10864440c0740200c0312000400c4455580e08032481540320006001e2400944034488a51103000380611500d440d2041c14109803041d030460500d0380307422031f8090a444080694003104d018020100315428504452000c880c0c1141096a801d454003400b40401c0070001a0400100c441e46000d9440c0d5555042543c010020124295441410401e014013409400210f400980d10310060300417116440500340c040c4000e081c4076500c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 10368055 1250 10366805 10366817
    0x3010c050a0212220b070303050703020403020d02010302070c03170405030c06070c06081305030d0c0e01020703020319020f03010501060201062105060f07021c0503070314010807030b0621030d0b040903 88
    0xf0748501030760710180c401c603580001e522202d18400000c1d900c0700340e082e401c04941210085075080c00e05070316009054001e02181411440c2174116000b0034030b4100741c0c0901074141900065040308120101c69007400440c3c21141c40c0d0f0408260038000c1d00c0503807291203110311900c12204049100d107400000c40b662281c1c042e4030a90340302c0c40c1400680e40307030000030255003000b40a0100c1c0c0000c1403080c4020600d07143c480e800010035140054000e003040c4042000c0c1c1d411507102d01c00070f10050306c00207022030b414114503407500600002d620020701d0300c0c1c403d0010141c06508140000038074640542224043d550521002812a100503c011035916610200900280c2c8041c0108101442072130345503410500c24419100c0c0040c0301130080c03035908903001100001800010401002980c144208044500c904070044059403510604581d6105c0c180000740c126420480420340b143d82d850b10711141d0080c04440020b0242c1c1792040a03440e41c00c0b21101c0d81c0c5c128103045a882c51840c03d07108412066501d074076a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 10369305 1250 10368055 10368073
    0x40b030c0d1b03060c0e09070509010903060515030a060f05060603040c09020a110109030903050705060f0f090102010213060302070303110306030d0e1201060806061206070915090504020409020903010c050a02 91
    0x10404400101000e80030800507410040013061980c0240101d1800344e40721043c0100040c02448140c0d10000c0881042041c18880b94004da82d108217403004880c1c000e02c0c00306031a1079a00210a850741007603d84d0303038507206031031b069001c20200b5040181c8500345100d0800c030b2a610b050611402d44412240148078202c00072080c002d0914684c0035206064840c580603850180c3c0d40045421603100c1d000c282c2c0030850301041001004005c1054001501d07050b2100f0b4145090401c00c000180909030b40d61001c605c002c00c0082c0a0f034400d50541d400c003500601780455442d070394680038009600c0903c0650000382410b04850407603c92108990092401a0003411110b038003141c03c4414007031600046500c04061640a0302600c001d0059501418000015256604105040103400c00200d200b5040d03d40008041026040c0c00218603012035400803100f02c68140b000a0440710080c45401046d4071a02c00700700031501407141d80c060800100150300130042007200401c240c40718000c2c0c2c510340e8010380c01003180b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 10370555 1250 10369305 10369313
    0x30e06070504081c0309020d080c010506030c18060612010312030b030c01050d0c03060b030108070e0609070804150608030412110307050603010501030b1f020102070c0e04020102070501030c020f060c0405040b030c0d 94
    0x541d140c589070b9172400240b601d00035800900301c24a80003060310100d5000c10391040c0b1a40a100759600180201e00a203100307a00d070070101c1e07908001c80c07032401038107660000024180c0e00e0703203002c0710a242c408410b2810590b8503440d19007400700e120320190000134a42074403407541c0d06000410586041e0140c40b090305101d0090400c40151149080724030415442d4000020300c0107000c80503501911340b03180541600c0d8180b1a000118030700040c0700b18800d8842c40140062240c100d4030064209410480c540e00d40e00040b11702602400a65002c6101840001400110031600c1d5448600d000d00ca0141d012190380c03a2810140e0702d008501805a12180c2000100200c0d0302035800b2501e01400a0400c50f201d480e030034042164a00803210610261b500003400604000281c620040900300c070b00c1c518181d9040a0b00000d564000c0c60181506142e41c404696940c81d0007040071800d06d4044c4801c4991600d0481c49480954111303100b4540294145020804c0d80c2c500450310b40018000074000810019194036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 10371805 1250 10370555 10370593
    0xc100216120803010b25050303011404060b0409020304050a05060a0c0e0414010512011404050303040308010b0a090306020a090e04030207060908070b07060b0a0806070513050108040201020303060d03031506030e0607050408 97
    0x6d10020a1110a0041d002c0c40900d181030817103441c00394001d03588940c5040d00c8114503104801c0524800c44c0381950078003030f107248402a182590001e03032005031607503541d1801034540300344148040c001d0700c1103004105607910b03150043c10b0100d515946d51b2005032030040174481984ca0312904890100344010040c1f020703003003500451031001c01c2000042039000300b22411091490096800341c072182c000104010034150003018160040c03004a1065152169000c402002c0880500004000035000940440d10a01c40ca18138000743c07541c21700c200354504280c074019503284614070990300450f503446800141c1083c040380752000c844011440600c0e149050b40ca1000525040081c168050f072503040c0818851002c020340d501c6800c0a80b42d15569191850322500014581c1e400709040200241c00c010050342e004c800daa411100649103c100004145410380c0035000d40c40c03105851064060000443c40d50517000700000d2101c0e00f003941c86a454400c004c98946c130803070140720416131084640c070300011503040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 10373055 1250 10371805 10371817
    0xc020102030d020a1106060a082104150309060510050a03080906040e10090f0b1503040204090605070525030203090603040501020c060a0b041b080114030c100216120803010b 76
    0x12058924205554000b44100e030008911000060003c1d10552498402004455080a411940701542c107240081e0b041c1e5940044000800c0719082d4190080308021140c01e44010b48000e2a452039100707100c22004000700406c50007612110b040801103280280c441000d40e0590b0b0000d080c100e4a01c1c196120400c49502404d00c00380c100c0803c110006000d69030790586400307010901c0c940e807642031600740c2c04810b0324041c00810411924101c0200d0596983c00541420220302211541d1296a01d0002070002c241900b40a00058240400c01c004280d01000170880b07040000240381c03810f01c9144040420101d08280140541c1c1304000c1d194187c41c2540285500c244a00300261400e80d03128034160402200f61584880c140d11030580004504e407a014a1004000b08a041c060320781c44031038020489030041c81400c2002081903903152136a10b0070322002602c45005840c55850020f81c55001b981c580c0c046900c41e40d082c945142c04250007510001480d14148c200c80d10508503404c0c00c0b802d00480d400a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 10374305 1250 10373055 10373057
    0x80114040e0c040614010f020318090402040f0c0302030a060b0c03040b0921070f08011a010f02010f0203040807060507080f0708060a0314150903040f14010201060302130c020c06090102060402010c0201 88
    0x42400c00550b616130242d0380140080400740302a0f9803190001400003003504d440102550010300c020941650000c03603000007424225810740154030780c0e001240040500710f02c010b08a60400c40740c6040c158154000710b01403985400c0401400396070b10048511401201034648040d081008104a0240781501402e13203580020540f0551016000b00120007400c3c804030640b15030030540d010001c0d031100301006002022018001c1c00181d204600400c444c01092900906203c07a104a174160f82c2d01c00d500c8019180b815107811075507400c0a041044094000400494005003010700040c0c0c101d214100f2140501425180e0f9042d90b1285201a00d00250091925400c564100800408aa410381c44001d410700c04001800144401406000c124440144502e0160340304100800502c4d14880a440441c0c0c6a240d01d0110519907000407400340c1120751000c0d40c0030100544000340510280c0c000c0c000d018103a02118400860b0360240025401200c0259000d6005403000801550250314180f491600c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 10375555 1250 10374305 10374313
    0x5070203120d15030609061103130f1b0f030c06030207050601030303020304050c100f08090f0709020f0f03010b0c0708150402040f0f050a020a081e0403200304030f1101080114040e 79
    0x1c0c3c11070206228525801030301e06946a000190a01007144540403040f44105500c1d40b66141140a40c5140b08111744020088100e2200d5035060240104510210900c5801070040059881000000c03480650006a03090802e100001131030500a10031a004154020041d103030351303880c589040e0000d40004000b40c07628000d44d4400720940da40d104d18101016055110a0241c05234500020090b09008003004060340c8201e80f031080550000031045c0444503021005691140e055104025500590140081444c0080008162107580c0005400e810410108980485503552441030f035078080342180019010013600030070090304040d0400f1340e59000035900400e50808214085045900480300e00e001c06a012884804880e80f02ca1560f030041c051414116014a1700000d0303600d01100604002e0922829034095040c0a0084100c001d200d041541078079143c66403821700b4a141ea01e042c2007120343c0310f8000e808400b00d44c0610002c5040c0c074001c0100f2140d030621002448001e0500c0c1840e1416442 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 10376805 1250 10375555 10375571
    0x6120c0a02030f1c0b090105030601050409030201020417030705060903090607020f18040c050a0911120601020a080d050414030c120d0f060b0a030506150a0305150301090b1605070203120d 82
    0x40501c0041103903683e0741a115603c0301301c3c40c60140071102001d40d02c62044e82035000401540d50300140c0941542e200f2a0009106880c07460203900a01c1190b1200c0c0b05002d80860b110700400d4040090240c007801503003a601240d032544007981d12446140381c209e81c000c509110719005800d01640c030b4510310002500c8104181c1803440280402c02003118100ca82100c1c0b04418003c5003007001e03030b41c0024507080c1804d101015030940c01d0314490103501d6944000360503400018601d68800c000182e03000380c11407a01d603500c0c8a122104e0001c0d0908403000e43e80601d403002a00e03c6c0e03203800002c42e05482e22540c080c1c800d6981050071032506a0241c1c410301d9446468052239800c25002c0e1143c400141500c10348d003580c03940d5403070340176060740c50003000c1511031515150314003104444d2004990341040d40d40b0b030003d150b5a41c8000801941c0692a020342c01d98602140e260401c00652070f003d0080300d400e003080c58400c0058104882d24451800c0082d0907822903c0811100c01c640c1002e042003032015480801d02d05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 10378055 1250 10376805 10376827
    0x30b04060905010f051b07020306061c0f03030203092b08040501110a111603030503010b0708120c030402040b06040602030f0f0415090e060a030b060607030e0402030109060501090506120c0a0203 85
    0x3400f000c4d100080c3c04d5035042070052520400b0f07000c001e030000c07107007926040c41502c0e0000b0791141e4004055a0040d0380103000000c8039058980d03120080d42e07000300f2510340d400d585c0c100140250021141e081503032240c03070022403921607004c0702d021060703440412120030302541c160304840445002d0011182503480e6900803a041a1142c09002c1d041300c80d58903800b041d020f007410603250030400c00200000c0030f5618420b101080d845070450b4199501c28100d40d80d0b84480d4a0300840c14802d4008071500008003070f0502080811072002180264000c4409100c140c0f120790401586205900c50000589d204010410450304100c0140c0a55556400c10b1070805684500c3d44a0407151359580da400031303207000300921890640103550360b0040402e492558440381555521141000d026003118450305010940c8000c262040c0581c1d950304501030019500c0b541d441003190058421030140c280403825401001c21141442c0c400c2d20907403001481075508645507221181003580c011424541180010042c1c40928 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 10379305 1250 10378055 10378061
    0xa030c020f06090d08150a05010c05030913060e0a05010b090d06060f0609060906020a0807060519090809011103130e190203010f0504050a0b030a080a12090c03021c0c030b0406090501 80
    0x1110b045000d480100d02014008284400041000d080d1b152007a82800d07480c2c54443e01c80080e100d080c00c1074100c1d07007443d0903c0740c50740c0101c800a0b46c4c000b42104108001205540046080f00c08005041d501c507226250b1500a58109014005004000f0310400c5180d203004006000040e00500700000d1184c1c64040c168905209500311a02003164034a00b041358030341c00300543c4020304403480034220401d916a21718009100304840504440e03160b43c00b05108242000780750300c90b520038840403c8148014038205003240c00c079001d0103000c92040751070540c1c01400801194012680407032002c2000d82841005450910058904244546681801e002d444180e100a43c0070300b080d900e039070542070b00d13000400095890050802e005181480303841c40346a180040c10f1001117900003415619100302a80c201c1c2e001c0040c11200c5203c508040c003260511040880c1c01040e640255142c00207018040c8c1503261004104800518603041c03048100041160000941e401520070400410000250f403200e41c25 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 10380555 1250 10379305 10379311
    0xf06040306020304020a0602060c03160e04020309100501060903020d12030e060a05160c020315090c1011070605091f0309080d050609070f020309060306030304031e0b06040603080a030c020f06 84
    0x100756400010310056180c40075403800100040e1004016600c0c0801103c00c141c080070300b50a003e410610050022103000300a00f044841015008540724501500d40d142e0394820814400300380c0703281000204041b885202c81205072034010300b4258800f40c03980c0e10700d000468120320700010035958540c041402d00b8240012809640c1c0c4003004a13481c14448841c0f0400c0d400705641105110a040c00340300180c901051041036911003031100100f40c2e075981e10140c185450307180744540c4102001d180ca004180c1022607140c503120b40d601258403558a4030001c0e03c2074402c00358002da1081410380d0400860a0a0780c41071072444032441c001c81c4503da960780d808000e800107541403a22584410400c8400e0804c1c9103000e90082d40c916244480c0818564081d440340300c0c040700240920800400100c0944040007250001e5074443c000c50581043d119861000304205034040300d0844207580890014a000d0294605030b0b0303002041e080c42e108030031a060b4020044050200154003e40c20000b03000d41091000a02c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 10381805 1250 10380555 10380563
    0x80301030b10050102010506010f0c03031b05040e0a05040215030702010f060b0910080c03061903080708030f0c0a020601050f0d020312040504110c0d0f050705030a020a03090503010c080403030b0f060403 89
    0x4905000b04084500481a04014116854002088910307030340001f515019090314101142c50840c9820100e0140c03006200c0c0805913a0f804070040310307855215000300204c9200b116800e000340c80300341310641074850a0b01d029500c10304070048150303100c00042c011900500d0758000001c00141c0208070310140d44a640c00009480008620b28209092900b0318054040082c606495035103003600b0440c4140c0000392540f405084a0a0304202a4120a0700c0d01c000d160010784280d01c0300002c0c40d01c1c201c0c56104880040300001000d000c101d45d02140c2c02030b103900000356000740c101030b03007880184542c41078a08110f9038012903020003440035890620014100d0114000000c3d40e4038200000d00c0140ca600601c04111584100021000d0450100361140c0c1240d03035190880b07401c002d0a4080341c03140981d080260083c0000110561016000541112120721986510030f41699807000c1600703c0e90f03080e0741c1401181d620000140000d00c40d9000c09043d590003005503c0b80b0503258042007554006030800c035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 10383055 1250 10381805 10381823
    0xa1b0305040e010608061f050c030f03040203010b010f021f180506090c0d17070201031b02060603160303200f0f01060302090c03040201121a0409050a061104080309010e04060308030103 81
    0x2215031030040c2640e90240005090417035903810440042195038461180039030820900140c245801480b4034100e4001c15195401c60f0b48524075018011125442501d080f4442e42c43d00950940315400b4482003440a030b41030b000340511081c03502c089040008403c0701001c4013503403042d401c02031281400c024000540144000c120300d02d8800030452610003240e10700e038450210000c401d07002804110b01c030044003103000071113916601384d440182d020b08407480b014112405102503c501281d0300203901c80c403451088045850540c0d06501080c080111808040d0020b02d0107120440000d480045000d0303a1440e160840b001c4140c3d0300c0802c0d05101c001551030310503035101d44040043d803400c1c0c203400390803a4100fa15603181d814247c0c006030200110f04002c040c0c2d50745901d40f90b41540844010284001000f4000344007150f00342ca04075499260034141180c0c1d0a140081084411801030150f80640307407550b0095181145603401511240420441c443d4810345030301c8044009440d0307001460085210313400305 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 10384305 1250 10383055 10383059
    0x20907020d090603020301050d020103150b04081501050409030813050a0b01060f020601050f09010302100306080109080a180305071206060b16030f030c0203030a05060301020c07030b06040b090f0c0a1b030504 91
    0x800d400d40720f6202d04109801400140001d550310350b1020340003582400e0004015914108000c141c90702640000d4102c0d07804200007407032034400302d0781c13000f541c41150300e43c810390780c031402000101c0d040c0780c0740039001030542c4000070300c8a0f260029541c6214042c0c4111201e4030320700c0da203c001030039090700400f0010710702094a0503040c0d010001d85024244c100c80c0700042890860100c1c0340340f141440007a10403440b547d00c1d009014002d80c00600a020104000e010b0454a130414000e940c0c00f900012002421b004003100d115159103030074009803a400b0300540241c40c42c1600600c1c8015151030190b038410340d1240d0018401003040c00a207d00540d144000e003203180c540c01e01429024440f00781c0001d143c1481d840413080e55022080b40ea000b20001c100107015121100842d00901400421020b2481443d10101c20302660388081803003030304111020300c08075000d2002e20041c00c0e419521a50142141004103003820205009080b0340c0c000c51800b5060340c041c4020b440c00020001d602540442c41c00182 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 10385555 1250 10384305 10384307
    0xf130c030b0f0a030807060507090b040b0301050a1205060402060f0c0a0c05090106080709060305040606080607030617030906040b0307230304020a09020307050304060c0908010606030209040e010b1c0609020907020d 94
    0x144011031102150b5000f82e082c915200c001c3c0e00e105007640200499079803070025200c0c81c06164a90003810407c0c00c45a225a12103070fa0060030f504c00e0051030700c41c030744400300025000d4010001c1e07446568003901038602e03038550b542030243c150058401041d06070300038000d0554503001003003044a00c034090248036408520306000c2c00307114034043e0043ca0070000100100100ca07500407607410100c503594900050320303a4460a0100050109802140c140e0140d80184200c10f581354120030203990b0750941c00c010203031071101c0e529901c0c40384070801d80c2c0064041c802044541c44182c05154414854206082840c4084224040319480345818084844020042c0305c00c0d410004514000740c080464114914200380b18058110300006000502445d15100045e44c00c3c0e100c1c0349000b0040c000f88000740841c175101c040140c00380d000440e860b80100c0c5409125840c10805000f1400c20b060043e084031000c03401000e030300041d80102c4c0030031355015482e894017000684800600a126034007075409001c2600704580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 10386805 1250 10385555 10385569
    0xc010f0b030c030307030c0201050910050903060106021603030503041e0807050f0604030918110a0c02040e06040309030807060213060815030706021c0e04090501020a020f16050f130c030b 82
    0x2040d0080d844039081c102c2540b000021102403540608041080e41c00d5880101c400380b203003403452600410140c28581e013064000c0040c0c81d0044c011000c4e945180e8030f99000700d03078492402e01c0800c0810071401c8100302013402000210b4110340509a01c02c40c000f064140100c80171128036080b80c40090016845041c42024031410600c41c0620303003e0041402e03d500d000703048d90341d94050f10aa0000740ca106c01c07004002684520384003050396a016840b0034480b000a0040b400003001a80101e0030041e101350042c3c4085401c03407003140d050322181c840e2070035520b038400315812240782299441c0d400c101c41c407000e024200c40d54005141c540e4516195141595503841c0c001030902400e4003d40c48800b0030701c8a10b8007c109001c0c410000074600c1303c0402c000304115030741080e207010650458540750b5103009004040d0010400c66a05400f1070300c0b503c214020141d5641e0840c51070114410780c0e10000e100302c0c07078000c01c0b9516200300140308684160011072190122006850f468010956035101c141940c14403403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 10388055 1250 10386805 10386821
    0x20c120304021c02030d08090115080606010e0102030f0d090302070801090602040f0b030907030201030e010204170703120f09050f060708030f0f07020304030203060a02130f0b07060f0203010506190201110c010f 92
    0x783d003a46089543d020a5036030f80200400c10030f0005000028001040c25409609204404800075000c180d881c500c0980b1100242c47c1e0500092950f10b590886500020444005840b00c41041d0b280894004204004181201c0b0403400c5009516002845020074024240014081e402c0143d542d841e00b02d2400d445440e55109402c1c0c1941441004500940450090116502070a011800d00e0b840c0650714020320031a00031f0007074a0300403c80c0900f0300f4000528001628440d68406078000041102925034000291840300002e28900c014442420400c060f0348445030301030f0116003400003d50b81c1c50b001350421100800080c80e0041041440042ca0340511f4201c03a2a001640ca000c0c00c580100e0340310480203002c1b04083c1c2d00003801424000100700c0500081c2558034030051040d40f01c1000e0789440d031214000b6260141800c94142000d11240b007220b0403544001c106a15040c400d4019204070080d0101807004d5540ea44500626100c004000301300c4e2030521000002d0356901e07848044103d070284 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 10389305 1250 10388055 10388089
    0x50315040905060609041506030308010512071a0c0a12050309100b030d050310080d02060f15010c0212010e0106140405010e070e130b03100c081b031504020c12030402 73
    0x2001d602107000460020b0b045501522031400a0741c07a4180304041421560f01c08038854a014000010b1540c412403003030580b08100e80040090b0544000b8994420850080030302070719030f82040800c40c44005c0001c001c551038071026118100d03d0303903c078105040300184599002c100700100700084c1003018007030000304242d550303410028207903100301090359001441541c005020000020406c0899841008801048104100d07904175841c2000252595000d80c1e41805178151400030500c0400280382c0162541c81c1030355900841060b035000c00c148000c1616605005559480d41c120140100f03004104c0a8205200301ca02084014001d21045420503440300041c1c5901c070050045982c0e004011005c010030895100d00d0348504840740c4e50040081c1c801e4140d161041c560010f019800300d400c17943c2841c032140c8a540701959500001c110b01061141ea0000c15202000011980c031050111540b45d00b0025100500300b09154002e1860305104035401a4228800700410045141c40264032100a04c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 10390555 1250 10389305 10389311
    0xb0102101401060c0606051207050a0902030603030a050307030b04050f160203030105030c060c03040b070f17030405060604020c0c03030706051803040f0902070201141c110a0206040204050408040e0705031504 91
    0x14031072029940c40d070306016150400910b0b0b02c0c040140000c0d900280054540140100034000209481c2c560f01c42c241d116090080f15408000a02024071380700fa40d100d810040c01440c98000445802c85182c0c2c0000e02000078103a0f100034080c150b888603c2264400c01c0b0103401010305050810150500c5650074070b14000310340c801c00051040742c4000c650090300c18815100c0030344410b0304101080c114000c2d50411003da400c007040440c2803150440300d010b407030381c0500105005501d030b444240703400c1d11040b980540607501034800319146061580c018103040716504150340140070704000290030341d841542d0a658442c5c032030050180e42c024958190050045540c0110315191400c1c604500015440c400c20a105034046000b07010759004414200c0102e40402d5100e50712a01c1802070311042c1103280307444504910700322803041030b2008042122829803441e001001190b540d507080002609004108882403a820b20000801c0c0340100710302e0b0300071121521815120710b0081c604484a400c3c000110f4030943c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 10391805 1250 10390555 10390571
    0x20c06090117180607050304020a0603020a210e0f0a060b10170a02090a1d0105030c0114160b07020607020d140307180302030d020109020103060f0e070f020c06030a0b010210 76
    0xb0b007028142109481c09805419256038010303052103680e800c48501001d500454040180455000d40258895482207070507400c1c598071507008400720b002d40741c0440041290072240c0d0f00d01941d071901914070400c0048020824240308203440381840182c1030a141d140c0c1c8039550820030054980034080c11b02e601035aa0001c102c8035907000804810f10000114011115a00400c3d6282d00d150100e40340c00c90013401c7e9410b00c81c0e81e000442c6c4410b202100c419141c3c0e4012001252600d008107481a0008c0141d4071017003d030007205d040420950042e071203110b0703a900c442d540800003020807440d40d10401458008e0603540c9090407000c0c0c140ba003050003103c10011034410707413040702c542c850546c0e410001d036140035564010481c3c0c008008203039941019506100b142460300e4050790540102450074405c1e81c0610016582d402e040b16440c1807405a0011080680300150070300f442a206a04a8030152040b0703981c491800300031505543c402c1e206410f5040e00c8400c04040342d40c041202c07400301002c681017000005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 10393055 1250 10391805 10391807
    0xa08011b080f16080709030c03030807081005060a0311040509070302090a0b04030201140c010e1002030907060311040308130e01080721150c020309030f0102040602010c0f0503010b1605010504050a03020c060901 92
    0x43d000d81c2031001c0c4004c020108900318440c200380005180d000020820390364903400d016010b003e007103500000080c01076000481007981e071030405080f41c1014005500300202070310158003030600585840f105034000d1000282c47d5540c00c90041c01041251001661032003480144402ca8a0f203801c10110300c4410481040141d074000c0a150f11441603071055605c1c2d100d40310141d8054545100060424840d9147d00007840302190300850268800e001141c0200c0d0f5581019010341d450143e0645007007009220030404a910003005000c014480f290f40b0f03c81584034414085803001c06c2e003115220743d20141c4103000e010300f1b84007118038a03440200f40e82c4c3d080e107403036403aa080c484e0307222581a03e90342c884c08000240c9000300151a01170034000c0a40d020241507101c07043c000d40040c403030341005608080c00404058010f8022040d009030a0f900d181c5560f084c941300b080300d80c0c0201d010080c206004601000812800e01c5200d02480c860805001049001c0c10028a8022084034080c85400200b06c202516 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 10394305 1250 10393055 10393081
    0x5030406031104030204021c0b010207050105031603021c0c0201060501050315120304050418020301060b090102070b0306010e060a080f0106050c0706030504050a0609030801170303010308030c090a08011b080f 91
    0x115a03030318020070180d4102070702046602680c0d0000390085d00101d050f80402c03109040008180c10100002c110707451600e001207aa440c2c0e0b42c800d00c0d020580030030106034030f0000032071924502c001c2400d02500c2c0c0100420002e2802c13494900c0b450340c0319582c07280a1002c0e5030a00940d00101000d1900c43d0550820038a443c086810b6413401900c00c6002c111500c50342203050080d540101402130080129414080e0391000d5141d007124101e02c170307500e410b00100c0c1c21103c110603034140d00c4040c0d0040041c14285110f00060354000f401c15410b200c0e544009000c141c0e5442d0040158107801c0d601c3e110700f814400300098005006806c1182802401c0c400301d900c6140000c0d0041c21540c09203004a0035440e02e08196080680c09000031f00303041c0c01d1502c58000c1c076401c000f10328102c51300030001003903100505282d192240030078040101032010410120706900000c4000d8285200b0040080c24450303901c0d8640c500f1500b55160b0000300c0e1601690b5101c84a4004010030750250a0210702102450103d640c2981313 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 10395555 1250 10394305 10394309
    0x1609080c0604180902040204090905010e0105010303080412140a0903120927090c0f03020907050f030601030e030904050f07110c0d03030207080f0406020625020a020108060105070803190606020604050304 89
    0x5104500700f01800d0740300143c0c010030003240d0090310455070369880ba00c1c0e1501419036418181c41c0b540c244542d00d031010341c05109450490b03801d5600c500036900c2d00d42e5501c80c2c2c240000840c500b00143d03101805210a02480141003903021038035441c041c1780c076507d00f802092541c524001c080c41182c2070304000384081c81000e003070940850003894020303520700946c960042c0b0f80380700060300c81028554080f0f0016801344088007500d00851320692241d6500100f21080d22802c00c0d034030040c10042c408120554001d8201003141031043c41074904044518000c1012100c00325841202c003200c28050045141c1c00c0b075605030107510f8000150004000303510225510094407500142056800660481480302d40001ea03040440303086505a0307604d40c0c035080255903030b0047e1082c01107001420000700b42010859400700011030590040d01044110f0f0300150341c007000007003c0b01d06008003000004006141900210b2080f0841c3d030f0a42d00300041c0d0078000003195003580184041d0750003a014040461000020303142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 10396805 1250 10395555 10395569
    0x3120902010f05030c0408100609140c04050609010905030a03020d030e0a0206040308091903030306030203010f020412030806060d020706050103050c0a0b030c0304030504030605010b030406050a02031e0901090203061609080c0604 100
    0x40c1d2038a4070040344000d403007247c0c0304d09254000c0c51303c9840c03010902c0d0410001c44403164018401640714a80e0000758101c00e8807078184140701000300300311b11f00f0700c1000f4100510050528003416a55440402d080ca185040200c00503081040f03194241e07a014411311039000c4202008102150150380030446521072400054030380c1e500407400000310799801102c121600f030241c3e030005466640340387c0600542074500049219508107031010002c1c101610986045405c5a070b0030901202450314280c0e41c864014203600d030444000c1254001d0521a4001042c4180c4124030005083d0700d1030400341c0c1403004000303420b48180481031782040740b0300c0118140c0c0d030803920070515070384c0e280c44918003614140300d650701c0100360324202000050301c2c20b00359000d5449071b400b4120034000d80e620b60498004034401250400b0120554880307088500681901a50b84a00c4520001130001c0c41a00020715107801201e400030f0b41240302c4407141c40d0940c0407440200410313103100209500120500021103502a41c01044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 10398055 1250 10396805 10396807
    0x405040c0302030a03050a08060d02100e030a0204050108030403150212160e10030b010e040915090201030e030f09130608070509040204021b0105070e0111190f0c06030903120902010f05 81
    0x1018800a8a0305100456004084850043c0545400341541c0c000d0300d280008104007000241c890b04100001207070140e13005000d4080403018000c180c650804002005801d4400d0300301050050301d40d8800d003806060400015501c45145180130352400206c0c95600d4030030360052102424081e081c00c2e070150840030b003000c00d140e101307480715007140c9a055400080742c0c0011500101d0a11581580c08100540000c0e45c40d24403003803000701441309130743e01842c0003410a00c00e01d08050310721230582e0100011901c140350214a20892681151558004403501c10780c200700015149581d2801d40c0150642c140101c105220040ca44601240c0b104424401c56000341e9480002508564982c1c0c1110340c14440041103411028080d40c1c0d244c000d00b002c807a148041031201c803102c1d40a40c0224424039550702524000d00191507117107180c45000c446404100d60342451400004005942c4030700c0c1c2000380c5003a55000a80e501d04d410300510300c0080c480c40c003448501e0b10300fa02000d41d0348003001a400c601941482c3d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 10399305 1250 10398055 10398061
    0x2090603031204060c080c03161b05030d050a0b0114030f0c0d02030906040507080106030b0a0207030203040b040b0a1e0c170c01060305100e010606051e040f0612110406020307020405 80
    0xc80c0c203500c206a20403180b1004a401c120070410203a0185401d420710365140c0c1c100d47e0310040080607901c0261030026060212020301d009091003000358039540c210220100c2224552699100e10b0350b00400d005e50fa019031550100300c040703207091180e1020880c092800340b108900c43c01181a8500c0041c0c200401c804001c030028040c62015002c6400c02d5958120855407460941d41c22078485c1d2060710300b2a40c601445800240207081409420f0980750440c1c8240b000340c64000d0f04200942c03000504030254082440001003610803a40580000e106080c41c01340d8600d0350b817000400d40300d680c1e10b4002c6401c031759001c04245ca90780694140780032503115003681c8104490540030000350044c0f50054075550308003c00030042290104e031070628032511480510074800007191940c240da009021740b00000e02e042c00071503a00f5a00c0006c204068680f41031300c40c9055120100c64004c4100c0e40c01c04808900d040450069011103032140703190a002030b914990916060200083d00c0748600034000c0c1c411500d030008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 10400555 1250 10399305 10399309
    0x5030f0601090b090112030323040605060f03060709051903020a0303050a020106091506030504030903170405010e040e0606060d0204090c0c030210090210030e0708031902060117030406050328020408070b07020607020906 96
    0x1120031036031400c04042710074a40303898031901918003219241e00a1400d42215540740c20000b6940c1e004038025194240514108028031101401d0131032507410070f8190350400009a2290600c8401450090340ca0a68034000d06001030700f501c40035807100c4013892a0a40c449208818504900305039034a03443c0200300c544542c00d0841d80e2031040c2e00054210500115864060590000200100c2d003080e00c50088000d1030504102c100d0b40d0008010381180c0000703000171114a041c0300240185128800014149916010b0030303021241c07142d5210020906600840c0103243d010440e001c24103581c40e9003400002951fa000c00c200d04151502d01c2c080c5074403030220310580103040c0f20725405480d01204a0b5103d08d00b500200d0034030321540c080c0380094082d01c00081030204038902041ca034550070400441c90a40741002c21076096000421241104c4090912240422400d10684c44502807048002d622682840406802d040071076108030300c104c100b01310120040e16201c00f40da41c00707501141c1080b00380d900c00c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 10401805 1250 10400555 10400591
    0x70807020a031b02150a0207060905030a020f030a05010903020c0f0603150103050c0705010516080105090907030807020402190905030d031503060903050f0f030109050609010305030d09030905030f0601090b0901120303 95
    0x100080d030101c4101e000344105c0e0b581d00040c0c03000342d0096080795506a40d030f090640d07001600b030080701e070142c10110340703000903003060a217482440c000a0100c0d940c80c81340b0345525084400c0100d0807001a00141c445249034500351001401c844e10442d4141d1a6050407441c000201c106d681015062584440002e05184a080c050301c2d00c242e001002030019181000c003a81510011112010100305818004102410504000791081002030000e24545086895201e0303160001c01c42207074000d0302002001440b0000d080e00301010101a00c560382103604041c1018140200101842e0425107410f08521140241d486220304898001000007a8003860307044c00c0340c0500c140c0605d100d0000d40001d1484070381d54190000c0d4100c40070802c0c104901e494150400200c107000380708c00740041c1e0040c000201d01100c02c0d4010140c5600ca401d0502e04540c1c1e5902003803c141891501d40d0598000c00010040d45da0940103203105510100c030009010741c103080d0042d22011000383c0103020035548070090142640300079 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 10403055 1250 10401805 10401857
    0xe0f0a0c05130902120a1107031202040b040801050a050906150607020a09020a0c0c050a030b04080306040b0405190e01050103020307060f020106090203010f03050c0d02130c02011d0a0b070807020a03 87
    0x1890002c0e07007070780301c2c000500030790300070040711002050300400501c030984a4400e5210b041c0303074066498684401c903203086500316455146100d4043d400c10000803140d04020060000308002c0001244070300c0d00088900460300c00400110007600401e00304800700c0e4000c420305404c0801280c05036150300b003d0000c0703241c0361000d070052603010f4070014407400d600d0740065201c03500e41d1244803160200b41e2071b0000c0c06183c2101c2d110050502c158038000c80c0c002403640c0090741c1d101d2009000012401c0325000018180e60301550004420280c0c0907514070034028502401c070782c49240000034015940b455010075502c81491082c6410006181c641100071803013904184000c006401c0d0030741d02d9503103480280203d0000c0388002c0347d103441790412110307890801c9800c0300c0c10715800410001d0450707150318192025044d0300000d0307003c43d56a00304003201341b600ca42d13061003502c000c3c4004080703003030141c502144150401781c01d035824040b0b540200701e0401c0d400104003071610392518114110404480050610f01c9104d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 10404305 1250 10403055 10403077
    0x9100c050d0f0b03060106050408061311031b0f0303090f01030216060c02030904060815010308180405010f15020a0809010c020409080705011505100c0b1e010305010204030209010e0f0a0c05 83
    0x1102c503410880e02d0360307084080c4650702241601d02c543d07030f2180c09403114459440764035015000000010303801400505240815401100709d255001c0000c2c00090070008201c0c0810090710880068036120300f064540451102020303401145040451703070010b1078112080d0545410140c00090500c3d8420544454140369036000b001072041c410245000b035141e0700885241c602961425100242c009800138480d100001540350f821900d1b4216240c1014540c00080520b00d1030420f0848075041d51201d1003000c1c001c0150710b070580003035802c04040d0000071145071607940c119800380d441580801d1045080b915a4402401c01030150030003480442e026100440e070141074040c0101e100340501074190080004005002c401900342a01d4004001740d9803404c0a034000003408804c58640010345c0700004540152090f2421030080e41a1058200350441c03d8000b2581e03650046410002c504100030740c18094003c00301c4e080d1151804552141102400034a410501e980765030102078110300404c2103d611b1558 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 10405555 1250 10404305 10404311
    0xa02060a0c03060302060d02070b0c04051011030c0d0810050301050712091e0b06190f0e0c040e04030c03020705060306091303090b03150306090c030307260d050109050a0509100c050d 80
    0x100c000c1f00c0009400604c0140e801d410340400003035043c0400c01c00c540c151800108502d020b00141c0c0403c03540240c1a544041180c4010040010900410000d5a44850b547c1e50383d108980b60502e04014000b001754072190080e03042805002c3d809401840540e080c00107000c00040140d02414641e030004031002c035048039000003003041018060040c07103203480340341c0c02d4801d000d480300780e0602104031072014131030324000b854002d4040c090b005a8805441d08401424601410207449148141454405035000c0380461083d0600c07030b08064052040310020070003203c06c0c41c11460b105000c9001c12100400c1c0d4a40240401c0740030b4101405440400041d001401354a80c0340d1620b440007605070f00c400c2c142207100f0303c00d02c000600044000107114030108005400b41d800c22041d59980300c0040070410b82202c054804003007900b200300120024201001362031102052a514001d07801086070009080c11945508250400c0f44076040040e05111030490224002500c0000550840b00b0707011f01c621102505003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 10406805 1250 10405555 10405567
    0x40308030109020919030201050913060302090108030304021003020310060e030a0f06021b0109050d180b0a031a030307020a0b090402070c0801061a0309250503150a0c03020a02060a0c0306030206 85
    0x1c80f40e01602040900340d0f0308502d00b42008000010300301092200034001a800c00c4000690b081690030707c070881880d44400318405450f6230005007900d009800c0700c40c5a500210400095151421a040481d0018201145103051058101c07503980c0b01e500400042c002502c01c3c51945480c100014171016030401c5012821040d40d240c814069805060110601e99003954090809a0706220b001a029884170013068814206d600a95411161802520b48610805000070301c1c80003940090030281c200750340000b003d02c03901c240c0c1c40440303480c030000b180258014071130f810058a9610008003901c190f00700303954450021200050180c03254a8000300300a00c3e0a800141900c01500194180d03003200d14120920640402c802c0b20b02e00003140d0101c2030741d1081550001e003012290000c00e08142e8140f0400c546615040828540f01a050007502c03000141c40820290011510400c9074905007841d06501d041d0445200035a692070240401e01031a54464040c510320780203500000085601405043d01c0f10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 10408055 1250 10406805 10406819
    0x70b0304141606090614120405030c060403030c0810030b071d030102130305060603010b06070b04050307060207030e0307050105131703071b060305061504030305210108010e0c06072102030403080301 87
    0x603080c42003d0200389288004510315010341c54140103107582034121400c10280c00204203203024060415200740c041007091903c00c02c011302a59114601a44001c2098030446500a0445100600c1159607070f0300c0c0f44c0f00744001801d0f01c1d52242c001c1c00c80d20b803501d07101c106a04541080882c05210316455840010301d07860301440b0508500031130303003e581640c4083d900c0406141c01e0384d4482c001c4a45c4070800f0051200010501c001c00ca410602480032a420701c6999036031841260301551003a03002c140c28038944c3c0d842c0c2c0303020040c40001e0300b003c0c6405410b11880d2601d2590008450050481014030075284102c0800100107130703800d07560860100f5255402014054403079a44a010b0f10780004e041c60009940750601d40a0b110b202442e8981041c646843d6131030446003600301c2503c450b0000101e905015102010414460180164000014001d0400d404091510b0a99010759002c0d040a00000300407aa00d80050344084410b40000e040199246008a00b180f15940006110070b80204c0081118 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 10409305 1250 10408055 10408093
    0xf040c0f12020118080a08070f0611120a09200f030d05120702030306060406080408071b050301061e03030309140609070f0503010b03060c090103020405270c0309070b030414 76
    0x601d000f80c0300c1c0b0050400007007410013122031a0094a4981e07004001110005003040700070000680146030008000d05242d42c1c2409413102081c00408a0344c0100e40c4075852100b07074081c41c2e0001d074811001c1001c2c102554900440001c0d03803480b80e9400e5406116141b00342c41e09a070f1034852482c01410b50303c000340c2d00ca4010305940c0001a6003200148908000350480740000216402410001d00d114201444c2190850fa5520300074401c40b1500f07030a00100e0001140e840c504004050355129402802c0c0c01c00e000e05084075481d900c07821f40044074500d5046205240404903054035094a00850100000e0802c6a132070180440410264840c040410030b55000104010040c0c1e8080110301030299a15403c2600365004440250b41c160010030104e00000701c218000c19100324113040250038690703200006009400e0020b01c810321019000c84402441084c400c0e4a40c0c881421000f0380d00b14180164a5903840e01c02d401814842c1303100101040500c0843e401c0c41000b62008401c50340d131412408500785030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 10410555 1250 10409305 10409339
    0x9030207080a03090323030a0c020f221d060702010501030203060c0712030f0b040f02040e0c03010e04030804060b040507020d02070504110d18050105091b090408030f040c0f 76
    0x140a2040c011600c0303200891907400c000d0701980c80e00b80040c11030300c07805011a1204481c2c500c524020841c200c41d44800c0c4007a0404c1503580e241e01c0f008c0c03400750040c00208901021043d10884000d020189000c040080002c19044003c1001407014000002c407100c280c440880c1d44030600c61a800c2260b410303815004a41a24170076000d072640d039120f440d502da920b40110710b030052a164102c220085014400d81c0480e1a03144411404980c030f85084010500311000300e508041075a40006040c012100e0f82052a80c02c100400d03042407866141c065218072500001e0402020080d10401060a2254a40000d2042c00f401801049142040c440c060365650403850a0780150080c0140084c0502c0c0c035106203041790442035074840c5009030b01c4062000400e95490300c0b8181a42c0c1c1f12012010801c00d01c1914410344280005184611425482201818013280c44512079401c0504203c0010507800c180da401a480000200c40c68071285401c6004e098190450310416845100000d00d0021412440d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 10411805 1250 10410555 10410557
    0x20c0712050106090b0105030601030506010905060301060c0b0609090703080309030d021303031115070c020102120c0c150901090504090809030a05010606270e04080403060e010203180109020102060c0903070909060903 95
    0x4109591313408840151072000030b545000c1001480002c0d1a94002c3e00080ea1140381490611041600c3d100090041c1d00b0a030403250000300b94048580410050a28042d0403041c120380c0e02c0140d1922500607540c0b0791443c000240700d03050200100780365800c1003080e910481072604065444a1440c0c203c3d025001c40703480b0540c0021030a1100003201c0001183d030310340444400c84001d805948024003030ba000c00c2500c0e01281184560301800d01d1148420014200c40c031241000340001d48018803c001d0b0b41c21070083c400c0000b0500308403a0a20b0303a0400c18500454005540215840e40f0070304088105000d409050313900748c06110003400800c141075102c042980e0464403001d8a0340c07c0c0c003030412200d80d0348846032000d00c2007100301400345c004143c0ba0301d41d1152040d500d10f40703001d4990342c5940994215000c200e000380c0d000b000703001c101680300d401c1c41c002e07103e0030000b040a607040d500000d5540038003414602c90746000040d07107521501e0503c03448024180c06201401812074610f0200001d0081610642c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 10413055 1250 10411805 10411811
    0x10b010e0607110603130f1202010b031c031109030a06060303230304080c03090a06020105040308180606010e0604050301021606060801020c0607030c03020d0e030a0f0203040612020d020c07120501 86
    0x140a40741c40740c10365038071541000710a06101241014000c0c168806020880741d08000000ca60000720100400003085206028100e000e0101ca04060f081d00c9503030000718030941001e00131203607100b81c090a02002000038a404a41000740e03400010b010701c503241f2165094000c04030507c00380105a00414100d91199030754851030400f100c540744041101007112400c0580c10130100b40418011000303480300414010a50340307009c0200c0d00050302900d40e0740c07000016035160b4082100745600401010383c0001c1417102e046070528144140760b11144018030044c14084441c00c1100a81c82d040e080c0d41c09000082d008540c0e504100364200410395052408889480c10000c000c641405e06009991740c80300d090b00200309036115003800780c0151080c0281401090f50a010030156103c4c18003078141117414820103140d0764a50078a00409202080c9450b00035984104010003006520003100034001580000c01a11034030492076100c060310480c0410842480382c10804180443c4c1106841c8103d40704000030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 10414305 1250 10413055 10413077
    0xc030515060a15050f04050406030c03120309020f10020f010e010212011203050301031e05030f03011404050714070314030c0406090e0108060c09031509030a020d020114040204020a0504090c02010b01 87
    0x40e1280c154080d01c000304040f10080340d0348500500c06046203690190700c0c01c0c00e09407100c001c1030859407980e0040d500100031000410900000c0c0190700c082100d10f103802c1c461008580c01040b40004412822800f400310046a0402944244044e0b80c2c4d9000303520003480883c04090400d03000c1e400c8a06420181882900001480d484600c00c114115500d0344036641140e186132507550074105500b00d444ca640c0600e80ca03200000b98107100812840042100f030545a5040c122545000f6452141c00d0f805680740c24244080181c125451208000681030300c1c5544542602d801c070741fa1107032003107104110320340441070180d44a02000a0015070b0b0040d5a800d50f283d5503040782c030300d8041080c41400b0300d9030000700201d072101c140100100b1503410080d0488030a195901411f241040c0e040311138222580000c40c50b66150b5905224080e9480c91500c002c0c404440080410384420502030002440784d07500044618510303002d0b50030307a0002c11468400300141206604081c3c064040311241c0c5001580c95228 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 10415555 1250 10414305 10414309
    0x60408210603070b090a0f080d0806010513090b04090804030b0601080c0a090605031503030304060501090b0303070b1501020a021002060405010f05010b070210020c060703030b090105011103070b060a030c03051506 93
    0x10031442404010001d001c01481e00c0d2103201540c0c080d03060f0a80140e0b41784000709602107a810b240b0000c0030110001c0c0b01c0c40c4911031000303008040c040d00a80c1000001c0100e0f07000d00f4000e164000a8a803100c1000840449860014000b031041c090002c15120300850000180210003c801d4443c0744203890b00b14090344c80c0480144203109014100c1d0114855900c2404060f12074400b443d403104043c2040311408110f40002440c40d0000c845c11501107494100500c6510410700446200d060107400070750801c25241e9981200603801400e0705c844513210000144107030710802c034a066154014100000c544d20701c0000030b4031454100c505035020343c20008a81c9203003074a4407036607048034030410f0f54908041c0070f982048154204030040c0d504610481c4071500007503035603400911407144079440024107400c014040c0118100164003040c18025041e03040f0541000100440b2a00399015654252542d14480050044050354201400d84126a400482000800a600c42021042c5510308000e07075a2201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 10416805 1250 10415555 10415617
    0x18120b090f0d08040615090204090e0c030106060516080d0905100c050702010807080601030e06011206060e010501020c0105070501020c03030112050c0d080412030201060504180209010803090603040f0f05060408 92
    0x9140b00050000d5000070b02044203a80104004e0620004000c11180d07104c1c00e60342070380c20903000180015078030b0050140f1360008101802c128075041d0300a2110b00c0c0740c0103002c0e040d40035040100f04680f80000405041148000c111103080c3c662510030010081e02c0d040048d503800031110030920361860300f4214880b00d8012029289000d6050b510640d15a0f940c043c11144004003501940c14036807590b1030082004014405030780684045503250072455203904121098404940c419000d400c041c800600041c0da0110382c0401309031082c05d00c15520501d41c82d1207802445280052481c901005c400820101c80750b41305c15400c3c6004000319800c100b8140c04204014040f018010303d01c102c100030410074100d492807440c07130340c0c0d00074000001d41e5640e52011a080c1c0c2c50301000003400ba45101e28202c11443d040030301c070b400342410100440c1030503070000204d0350030700c805440949103444c0020180e08000f805214040a00c0c0d000e416600c10381018603009040307030044003040c1300f02c80805040d829100c0c9201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 10418055 1250 10416805 10416823
    0xa0201020d03090b0103030507050c0a0806160503040812040206040b03070f09090216030f0c05060c03070206010e07020c04090c1508010509011406030a051b040b0a1b020d0318120b090f 81
    0x4d110794145900c2c40c0e6042d10290322644003182c80d401303403100d4201269038000c0f0f2040100420070142c001450a1043d040a070343c00340080c5030038440240248000302d0707100030541e92110042400004903032a0303130000941c1401681e01024034420004100300c400765000110352460304254540c0360765540c54a4440060b13000d241140007078814920480d07004688074079050542c1403640e00740701e001d1501c240c440301d007003000880e6900042c1900005004505504009490041604645040031801c00d42030082d04c40d514452a9449a5181d241140c20300107103030200c400030480d085186848102032000581a40402d01c00c80b440388842342d00000d54004000024440c920300140601d20719514079550b0710040c0b10282c003800c00d101c0b40c00050308008940a001304050980c918410340c44240002e0020b040a0001d507418001c0004100081c006031903542d610050350381d15003000c1818810a88025003480b5040d400405603c4046411400b80107802140501406007242034815104400da60503680b50005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 10419305 1250 10418055 10418063
    0x2120c0c030d09021306090207020f0603060d080a03140f07030b03010e0a14030909010605030f070c02100302340605010509010e0f1308030a06080105090604030f03020c0307060603050a0201020d0309 87
    0x300880140310009500c0300c00c0c5213200074000d00c1491049400d501c100c2c3c6081d04052000c5600042d04002c0d4684844024080901290210b1a5242020124020302480d2100500240300401e0000700f65029400c014041c4200c1d484491292400303220040d6040016903039240407034075040d59200c07141010f004004801e00914000c012403110351f650fa003026a410709940400c3c1c042803140f03260550740c24020b20f00820b41543e9260305d0b410708052400c040c0c08054240024840c41c0d040c0040181ca41d0202c525440d09a42030044e02c0340380d0b0b406000082c0f048035850513003020141c03804011100702e0718407002d500c0d0700841003040240c0e00c500038004140c1007801010900541c40c4006000500d014400d943d0250400c68903807150101030b40ca002030f641040c1c4441183c0303616003406008917031092007116030140c05000100300c1420980c038040d00011600302c2d48010190001081c130803000c4100115980b00c0d0344030f81d0800005651341043d5480344080c401c100d00500404a0207122076205c0c0c05918419604 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 10420555 1250 10419305 10419307
    0xa081911060405070501051309050108010506090906090709020304030e0901080d11010204050307050d080423040506030109020f010305090106050d050303100b04032109030213051501110312060d080a020102120c0c03 94
    0x1845c00540d45900105090220708403114404110a48a405260700a101c007c0000c6202d0400780104841c4403c000d084510f5030788103104110031403030001010f0040314101c0c41c0059481d250380c1000c03201c0d86d14018500303030000c0412000240e01e9000090541f2290041e6640820484050b400309080c3e2141d8400d50380d040d4000b00060105280070080a8031480c41200d0341c3d07107810790301c280c101c0200c07000c01c1d80504c0b4000849900b0429040c217001e4544d000c901180204284001540000e8260f50007828040c10181d40b00001a81c605003580481c010342802001d1110030203161610681d40d910817110f902514070519400110316503410705440c242d96020f603c50300304400c2881c2c1010001c00d1035140c9810014102c1c40000075807908000708084405038140440c980ca0420b41444881e00505400b81c1003001011441c0346c1190040140c030f00ea1400310035426043e0700e9450000710380f0400c080c00a0802000000c080a200b5015802800e0503a00c0d034884031490340d0707200920081030150f112600c1090304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 10421805 1250 10420555 10420559
    0x213030506090d17062101020901020717031204020f0d0b09010b0406060206040305031b0307020312090d20010603080c1605030703020112020307020f01240e010b1b0a08191106040507 80
    0x1500b2071040f5170100d0003601400201c01240700c24040504499403c2c4140c2e503001540e480380b964140922400f400002002c00e400180700c41400365030b489a010000d8542d18250042030441d5280300702d0815a280040c550a00e000d01d0381404c0c44080019205204290304e40000d4110310b081c42e001b80c0d0203d07002074018180d02d64031031b107050b16141d00080410744a105440c031003580400c04680039600911080d4021a216121444080300c071a0014001c01c40a600c001030701070705154443d000e40c0036200c9229803a03400d1070600d07025502400464100404039800861040c101c03c0b00010920388a509201040d41c071640c2c0d039400e1644408180c000039002a0000f00d9464010b0840d03001150010080e104907900e1748002803980d4210303075101b07080342e9107a01c00c0c1b00d201d010142d410b95044094210801c0500044d49003200c510614810b0031062071212903604106c1102030402d1102c840c059804c480b104d65150007c48070425040b0816000e000868801c1684c0c2c2080f0500044c0d20b441590311000904001c1c2c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 10423055 1250 10421805 10421837
    0x30804050108040c080a0804051003050907060c0201050409020d150e0c0304030806010e10091401081005010804051002030a050f13020a090b0a080a0507091107030206010303120902040213030506090d 87
    0x3982c002c1040e14120035a240000d08080c0070809101007a006400d841d0701d49083c0010800704000840341d00e0704040c00d0900307100d036642001c0b80c4101140d006041c040746044031840140d480e409581d00c80d4088a1021814114503111608050b0030460072030345102001d07490f44d440c0c081003402641c54243d00c800034000640000d0080c40d00030303004001414919101d00800380026040c0446d41040c0d8001480707090301700030400110040c030b407006109080405c651700d44111070007809011807081034108200c0d10301090610505104160341000c1c500400c0d9903e141103107480c0041c0400390b072103c0f0003044600000710306000c00c1e5201c034000b9600400c0d40080524080401018180b031460343da034000100070700011202020001407a0840c030442c003178000140342031918422510203900751021070b041040b01c2800240c2c081420360550381d15040800c072002001070307007400409031004020340041c0f00240122005411800f8202241c1c410b0007141e0190b03880300314098480032200049008181301419541240c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 10424305 1250 10423055 10423067
    0x7060503091213080a14010509010c08060907030605090114090a0209091501030204050409230a030801060f090306020a0e03070504020c0a03050c0a1e120203030103110f0f04050721060308040501 85
    0x81d180c2200403c540c662180f503d02d003041d08000080303450803569650820116028016164032100030002048801c10303e00d030107050f82400510740d52181030142c0000d441c3c0b5020780e0000005d0306002e0b026074003541c2c49241e01c3c0100040e614065101c1c44000f8001010710400340211355902c203003d00f4004d29605d030140c0e08400080c00c1e050550601d9020301000c0f0700e645503840b03141c1c102c42c052400070a503540e14030800d0100b0140c140b00d000b4103400c00e00644d00030075080a48541150100e141400c1064140d01046640f4105600014001070000903071348588c07030b40034000138042c640031001c2d0b414480c0c0d1202044100d12903001039403029080900a8004240502c0c080d280000c0c11000f5a51115410b980303001d80da180a00d000c1d544a030100000100b0f0200e02c96440b40120020300083d4919419a140e440c400203800121911640391003c84011589514810450040c4054020b01160911180281020068510f8441101c0901a40c0c2d03107000300500904e0200c1b40c00071513642c602030801c00110350f2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 10425555 1250 10424305 10424317
    0x801110324031f020d1a060a0503090703050a0807030e10120c05070204060b0301150c0201020709240b030a0e0106050d0809060403050a1a06040b0102070510030f11030108070605030912 81
    0x814098250f2691581d241120f000941d000354a1006035201103820070001101d8809401e916003018001c20402c0d0303a1119070841e1440c4441d810036645955030404007501c0d01a00d82c100400c6c6000d40e01e1200c0c100110b02c405050514442d40340e500446154030148448000010602030006800c004044450132041d809650b54422a1604074a04841900230609583e16680503a046500000041240c44aa2422460040101c3c9010341484c03406800003962204540145210540d035034011a0200d44540d4000c42e0030381421300a401c50680c0c5800702c0441d0782007211429080c500f0030144000d0008107116807025a030b0b00903c000070b180029265120103400106201d504407000f0000400400c60400160100b507100360000941540d03071480c0e0104840700500400d02507410100c54114907a004500e00c0705466055680801581d070b9245c04401824002c04030030502850f04500010840c0c40709c0c0118180e590810440741c1091b03035031904030344a200440700080c0300e81204061000042d003010050030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 10426805 1250 10425555 10425559
    0x30627010203090703050c01090e040213061206090506070c170d0204030203030412120e0d030806150408010b030f0a03020706080402060d06060c0308060901050f010309081e040801110324 82
    0x880002144002801c82e401650515480c2d072000c6070030020041c00700700b6206800028685800038078a0301c100030b40d440d04040c1000f44140d00a61003c518036040d44d21420080c4044144ae018290315801c25800402078000700340c03071074003e040006010a005013454030f42c1584c45421004450040e11380d0720307059080030190455964082000001680e13042000e030000d826030342034940c003246c134034542a82e048101d050303024240044860200250303565000d02d01d0040c0d0f094141002181c0e14103000481c1d140e8090610102030401007000b00d000f140550002141075002da0490b03441a90b0300707103c80d035100100c00005006901c4a942481802d201c0c0315681c0d0000c0c030181c000c6040070f000181c804107940b4940c002c84006a02070000c40203169000600c1d0341c20030f0060740c03030304a07550400d000300b9004155940d050b03040c5515407440d8402c01442504840c90050000e03121142d1002c6c00840c0001540305200e00d075480e600b40209172136160100c504490140414a0380302080b41c5001d691554403020300e0001c16 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 10428055 1250 10426805 10426861
    0xa0305040f0215030f070c120f030b0a0b0c0601090207110d0c030605010b030f070c050303060d080403020a0602010e100203010501080f07020102070c060207050411040b0304020607080c1005060406090b0306 90
    0x41c01a2500c015070641d040c9401c82040d140c0c5003e403d1981c4440703000345010b080107400b422110114940a0410b111140e062400f4030140e00510701c19409000e1205180e50048040c0c440014040100406019503840702001c1d01d01076682d07281c5510980c020240d0282101040b04002c40c25440e100e1105d0303414a115070000e840182d40c0c1d45800c0b0440317074240d00000300c02d20000204111100c8840c02541c2c002481d0602c019410407680b030b040d5aa010040c00d490082c8811706111090010903c10348009550003042240e050ba22040001d010380f0384480d5215a9200b069480e41c03c0404500a49050f00c0341039541d0704156070303204410750504001a0084d0250355003080f03c4808601406070480141085400a04000b45800148400c590319401e03100c00b12002840288608048542183c0d0440d0301115603640301c41180c01c2c070758524480c0e28408603592151340c4090103140340d5a0082071045004440402c441682c60000c00d00340c44807940603da1681100c800900100301025101c0710082c0c4040e064 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 10429305 1250 10428055 10428083
    0x90b040e071b03020c010e06070308160201110f0406080c030f04020103020a030f1401050a06051c050405031605060103060f050402010507030c0c090c080109060b0a02071a070b0114030d0f050a030504 87
    0x301c2c14244654001d40050300703c0c0e4192481d6580017400200407010035180189800d2103a200104000c01c06400d900030a0441d40e805907106100350031a6a4811003c092103030f1321310315071328200419402840796001107500c07030000070101d102e100c00356880760b017441400c20381d2583c1c0d0b40d0044000b9130180e010801815a10003800042c0960381c41020380050703006013103910950604d01040705080580e0b00c518100b000800c40746c3d030556900f00058400c00f00b45a000300d16078232039140c540c1c21401050b00d8440d500c10410384d2030040c0040001c22a04a83c010700c000c200042c04180f140e0141c4800302c802030701062040002c3c40001c0e1180c040306240a00820800c01c41c1511a890101a2101480c049000895003401031100e24401e124203030040c88139007000c2d8030700749805038065213400661280d4070004011107641c01072005980201c502403603018082204641e1034141403882c4002c40003070b0380c1c040e11a84644000c1030b40214840c0441c5c0707440751103160420341c84100850207420020400c0312810803003c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 10430555 1250 10429305 10429337
    0x6090204030f0b0a05090d0e18070206010e01060306030309030b0a09080316020c0402120c07170d020408010b0114030a020904060b04090506030d021b0103020d0e0a080405040606090b040e07 83
    0x604081c0d8440e400c111039008042c1072000c0401c0000d0701c01803001c0c0c0b906060128444c000200c0e0900c921581c2403228040e0f80b0000018080040601450b13440010300c1c04010902d0340c00b00b2840c2c1a200c0003102e1480a988480045080303464078040100442d0402a040c008034400c040f4403039024051780c401140d408005d6482c1031140d0026128121502c07004c000002a43c1e0701400030668070f810170f0703d0071070404040284050413020064200e62050f0b00c001413440520185059012010f011b511302582d079101031600c800300070760180c846c40e2442e5192845a14681d8030504031001c000c1150308660381180c4031902840020b62001c40410750043d503a00b80046e85000b0003000d00000c10046800042c1e91a240c000d042c2007003074440c010030464102c45225001e0031002050815110750030718006840d030760301c400102c00411044003018080d2080a0710038041150301002001582c2040d1000c1c0704e4a030340d0709010341e1514414020040310000a0100b446416a402621940116285041038030841d00c000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 10431661 1106 10430555 10430557
    0x102070509060d080a0c080a08060a05010f090603050603070909060204051212070f020f030a1112010e0705040c03060f0303120605060306030c0904060605030304060903051506011205040204060902 86
    0x61905d20251041d8181001c555000c04850f54030b02d0702c224050984041284c01c036101d050004404503035548141c2c1c512030300310b0f102d445442c2c490b420081c081d009850300a200340c1e01442a8800010a48018042c01e03c0141c014440180d440c0e0400003400b0b05409440b2002229a0050030f07442e503140044421124081e40114142c2c10410356440003030b40341851455010303814880c240706503083c00f00740b03507800c2243c00e02140c14404403062002102d0903140412000007654000311820041401c0940201084061501e000600b1685644031418000e5280d001500060704031018248102c4107403080d0302c090401101e00c2070039490301c0000a5134400c0e07200b80c440c0c0904c5d161000300c1c040010719001440039250080c1500e407034580305d800c01030150000d0b11080d2450301c140300f184080000c802c800d19018ae541a510f600d200f030b500c866800e0140030003800c205e130030950b00c0380300243d030346000e02c = true := by decide +kernel

theorem cover : BRFrame.Cov 10251805 10431661 := by
  have h0 := BRFrame.cov_init 10251805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10251805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 10251805 ≤ n) (h2 : n < 10431661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
