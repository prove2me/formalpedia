-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4368
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:23:40.899198+00:00
-- url     : https://prove2.me/submissions/95991a27-e72d-4166-88ae-25e68e961770

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 785431654 ≤ n < 785611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 785432904 1250 785431654 785431657
    0x230d021b1c110d0c0f150509010b18010501080402091b030708010303030e0a170c030403080c010905060109050405030d050402030114091c0804080a14040e01030c0504050a0c2c0301050115020d1103 86
    0xc0c1c0c041d005040f174400030300305114006d42c03507004541024200020000403c1065001c5c403140755086403582070202d03817840a45541c010034060076021a1041021401600d0481c415590240c445191440d01001040c040700068105a03000e5010031980d0006100305905070088030100d151000c0180060402900c0d56007140c603000502904c0d99000042a8000c071a080c0200c0f009183c1086450382d403040704804a034000c15401a0549007030094070000b00320030303106005450117980c01c800210300304a5078009160051a0251003268159a2158014001c4414284552003140c40001424001c1c102da0612446184070140d040c04000216041100103488103007a214250f0241c070300601004281c4c03805000702d2049402c00c030745107581000004101f06250b0f41c4c1c001521801d88051240e5225007a000c000d803a400c06402011581181c0301805650303181034021030b20904400a4542e50001c2e80109084030000c0e00900c1c9013004a2072012a0160100f00901e12001c261410414001242e14115141d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 785434154 1250 785432904 785432927
    0x1018050346050d0e19060b030f0a030f0c0218010602070605091c1a0c0405030106090605010e010804060609060e061509180402030a06060e040201230d021b1c110d 71
    0x10b01c00d0105103050740440d154483c00166001000b11000c0c1001c0c607491070601d034001c180495040c0e0400043e018942804500c0300407041c0d05030001e0000c0300e400d0f41d0a65000c0d08a01d80c00e42041241c600d031001503078540441c40c540c40450590b483d1b070ba5042c41c83c000c4c1001c01c903411120078018200124079481e00e401d00c40b40f09082601d991400803110b18904486079201940801c04031008010901110780b20f020001d00440d1801c500800200d5a00d501580c2615814890140440e28021740190194041c1c0075551740b182c40756800040007500c40b00648120b546039040303461103142039001c01c495070070311002581c405000751564500741903401c000038820304c440204030078a40c000140460b086442c200541c41095900440600c200340d100c034400780303202504036030a03400181083c154560090200b41c2400f4074030300e07052450745802c4200b440103005c0c0d4012460260f54030200e445011140c03506004140203400c50124402d60800e06181c01400b0400b0a1080c491681200e4030b502841501300300403410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 785435404 1250 785434154 785434157
    0x50c130302060d0b040203180d020c1f12021308070f050a0b1b062d01030803060f0604050604031b0b12040f03030b2107171018050346 59
    0x160760280d40399a0f0054640c04169a82290000c01401001c0070841e542c00d0701c41c861001201c040d581e440000302d82c1d40f0740040303030aa00b0942030302081414201d807814260741700703205003042c05082d803909080307400b2a40201d000e0a001810f000040c80007075002d020100080140b140018109401e02001950b605e0040c450400b03440f1000500b40c0742d6411643d0701101d600d11140c1911040d191a2007000c04078074030907100b03014034280e1841da181c5d400c0d08100528107803500040d2080c119070301c0009100d058000000e80651011061000080e140c0d5240c0041015611441d6100b45404c0c24030108091064190000b40d000d0505111807003948102500d819880385d0040c10302d000800c16410142c0003450b2118405070881a1880d410f090303908030040541c007020340301040f5443c081d9103070f440180340b0589000c4503c0a07080010a41501805030b00442080d8560a61100a000f015500d079440c43e130002c00e050f0750803004909038032407200703a41545031100c40790b00c8844610740c40410f00b4203003d010549005030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 785436654 1250 785435404 785435407
    0x3110310170a080c0d0801050303280c05060a060501180b0706050615070302010c0f020a050a02131d010b0a0905090a06050a0e01060e0f100e01030605251101050c13030206 75
    0x1403051800c00c44021036540003080305540d408210a19921180d440c185e40012441200c00041ca41c02e00004075081c60700e12422a80090340b00c94445035a03150104002810041400d0000003c079109106180c015942101c0000380c3d685014009443c01c100c00f80680da0040030300c00c0420003035464008039a46903034000c000040d69902c6600050038601c149858039241440481c56104040e01540b1800440c030a9455440030440c00710000ca07611022010010030325009030b44860014101b010100036000d49031980412000940340c200d00e490440c0701118841c0f60744925665100b8200000706030094000c0c03000500c40c5190040301c3d036a0395005c0701c00082c04160b0b17030750000f0000c2580341d002e000c0c607031b100c07100a201c2507658810903000e5042c241d50035840b5102c01008100d6409110400800b200e58a4011030144c0c0e103140c035a44002d0500600c03404d0462860300126111402038a16071950000710f407600c0e100300d50b12030640c1e0300b1650020002c0007000c004201d401d106c4107869864404981e811074109 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 785437904 1250 785436654 785436689
    0x30801060e0d14010f060e09030d0e10051f05060a140a0c050d2102160212010b0409080418050c0912030f0304060902151204111801090c03110310 64
    0x404034500c0010280c04020319807030340f44aa40064110004421015900340000d5488502ca50541e2200b61010703c0143e1003000380078464012500810316049219040d552542c8031031007101d040e203c04807050400c901c46c0c810f21001c0e2a4106100341c001d00002d0f02c40070305116203050041c000d454865441180b010010820003d0710384141140d0011640c00030540703000e80c0c0c0e031400181c0004010341340c60640e103101502d220000d03c0345200b907410b49180748030050300c59a880d07028003c40341c4e80a80c04c0f00c0155242c0c41e507482d658565001e5107011507c80c100c0c080c0d83e249480c1e01d104074408240c2d20100c04d6800c203802c1c82240d01d180d009a8001200440f02410039041d00c1d0f10291a52149201c801010341d408410402480000c1d800102d41c41c0c029038202d0704440b148001036540c2d01c100400d6003c402c19200105011070182c03161012140005050502800190341409510300400d84c86600c2140d215040d1503c0298540208400d5051a50006085042030307189001500761a0141880d20015155807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 785439154 1250 785437904 785437909
    0xe1e0312090c0d03050406140705121309020f0306040509030a230c0708030306010314090d0311070819121404080307090b07050a0b151c0507090c020f19030801060e 72
    0x3164404203005003c1d02c02c08035603180184c2941c105129000115002e1011814015480003c468900d036100f8003074940050807200e40d21045c2c000c20001004401a0500403603014400c3c4001c05a00b8032003d0210385070700e80034040005440004200290035042840826044c40d00f001c00c035042040740510710355103442052814421030040241401103846a42000540c106010005500a40080c0d8040c006200341c01860080780c2030a4031100203d0340450903c0303c915110360f0200c01d081c007900821a1809040d03846001054000f082654814441c04040350012a00a4030007840c040f9421003d100c0f1100a9801f000350820003480600010000030004100b42d10a03020040600503d60416481f0038103824400d40d50706900c3c17811507034000944003142c0440103061003248101d4000b0004800c5070300c1c44c1d02144c00c01d10304810480d1144640040443e2001c000d001e044111601c5900400742842882d80e03107072418aa600d003030030060201800300e43c0821b03031002c0c4d602c4c195045400c00100018201c0c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 785440404 1250 785439154 785439163
    0x15040501020f0a0806030705040c08071103090a031a06040606022104120305041a040510050d0f051503060a0c0f0f0903080a03020315030d0f030f0f0f0e1e031209 71
    0x10a0310b00144005002004140c100c401c0b94010b96051b822030303da90391100140000c4903800001d402c007094031000003d10b049d21819200c1308203091103050746e00385942c41c00800c48030107182e00101e583c00500c0940b1020100b400600c55403200e4122000e000b004d10b403441c065180d03015040742c2220380b07080c2c0309290094550b4404840040c044e50124201c000c42d141001011074203d400f079525000416550040b140d80303200309039000d4400003050441e6100d018101615039500083c4c1c030111a54860054901907401885194440c003c2c0c41c901c030640903501010942054401055203501620349110b15420ba45c0c42540c040d40307082e260800d0030f80c058443c08250388854003540b0042400600042c50544654590061b43c0134011071040001001000c4081541b200818000d020000b01c0464980350858800d42091402c1d60200360f00246442d500e5034500d003611a0485049002902c60003400300c4203104020702c07008820500e8500908480380c45c5000d40781c2c031503480b82c00d050301d0211020603020303c030030b00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 785441654 1250 785440404 785440417
    0xa0207060b060424020a2102010e101a030106030c030b04020607050106140f09060102061b130314060c0a05030105040b0418030e24040e15030706081005121504050102 73
    0x51070789840d142d0790f101c100e6084a103c0800c3e11410f0140c4e03041010749000180b05002c00341d201055000383d0180c45008a81a2511505481150b403a1011140e00c28001d00c880c00344001c44d68000f01f0301a45504000c0f440c00801d4110600036031518108201088061010401341e03640803010101ca40c075079000080d00d034024494064915441e04400081c2d0341c5401c2554681c03010152051006011004100000c000003110701c14056000400003600c0d20380c80c01860041460b40c0c984282c10500d4590a09613518503d400458196048402c4070044001c20024540d1041d0000245860700ca40384000601c60702042c8581030203076490302c1a0818a0303070395030410020301c100c80e00b860301c41c4201c44c10010192041010207600411030f4403043c640c0e0340d0ac13002c4040ca110101c0000c50345840d20f0b0010b0390f240600c0c020900c2c00050021240005996028040c12000340959a82c00042d8105050b64181c0c03144c607640428800e08450086400304500400c0085d8562909044486d240c0e403242800380c068848e01c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 785442904 1250 785441654 785441659
    0x1109060103020f0a170f06030318041506050318010605450a051b070f171207090e060a090c091e06020f0102120402091b13210b0a0207060b 61
    0x4134204104590003244048240c042002c900740c16101c0d1611100802c200b81c828a4058004019010303600040c6580017210000c044c00024240e150b11040103000760042e044000040c00c0003051002d201c2d49481643d458a00304030080218034540800554603070f191213045950303644820004101d00c0f0001c01000c5540c00050010220f4060710403600d10b52031001c98200e800c6510b041c0210300071610b40d142421160010214141c80d01c0e00a8541d102080b941000803914004a404c2501198030458040c0104c01ca030f04e10409100c0c2041c1d40007503d00132990f00020103903110300c400c001142c2d43d69000d000440c0c0e1305c9000020704020340b002c00c076141201908582226040c0c0f4112040700105210000100c41341942079501080401110030b0a074401d0301d8078004002943d00104025246c040c1c10503402c0034205a070303441055044011134030950802104040409800c5c802080000708442164443c4000f03961003080c500e0042d41ca1510484024040c00d182d2a40821200204000c0394003901001000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 785444154 1250 785442904 785442907
    0x14130605010234060503181c0e0f0d030e13151502010209040e0d020c04051506030c070f0b0a1103060a0303120b12010903031d0c06030604090f0c140a031109060103020f 74
    0x8a050142180d803094401f402194102c40b46140e000102080400310101414a001c2804e14107100c05c03500c004401e010b1550000701c0d407211207542e6490505030042c162181d101c0d0022007080078104441c1000340c04a2400c203500b003480140c904070641031030a0a9600c1c01058503203120f2111002c900902070060007540042c9050b00303042a502c000590000c1051495080b80c011140c07200034403041c2c86040e585c80459070301c012120503c51a1900c080d5620110444445d4189005a20b415440e81c80c5d13010140e42d68140c1100740108940c0900402c940b6014a0582e5440c50901802090200c0c7c44d0344009803c11408049029589842d500206030040004210342590044182003a00802007140304802103460480161410345140c49540484080000a4880d8480c0401800082da100a2000c0c0d032040d902e0035000001001c10391404887d50055502d00b02190804120000d441141c110721403040014400800c005160719040c080c4404068070710703003800c0d116100142c01a0003050042c402d0380c1d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 785445404 1250 785444154 785444159
    0x309080f0c0406150813170f070b0c16020f03011e02042d0303110c09160f03021903090804151110090c03030e12060114130605010234 59
    0x180011128155002110b042250036619089a9086070039078864401041c8840300241102407040c10305000540100ca01e12090410042d64100c01d50000d1a10741d4111000b01e00e00c4140004c0c007190980c1301003503d013950715028504514001d5100342e903500911440000d210b00d10151020740082141204036001e540ca48009a5107240194000c0d00401c0c002c80f11051140140e16000c9402203403040014510820740c1c3c0c00c5481c103c5060960902c0c4025504c00c0e1000b116880d02d80e42c42991162146584a942c0100e8910b0000c00d07100c070a48400382014010b0001d12000d0000f071207016400001c60600256101e8203103001704540c01164000c0c03681e0030499034902e58181d0031020f21888158507900351030383d4040d141003040441d0400326002d098220701810030310009009281c0340c61121401001214010505e5079a5840d000302600440d003410300000043e031039801c10032100c0c039000c030547c80301b80206804e01c1c000070b41c0e0300c041c0e003581c4449000d58400384074000001d07007a51000740d0042c002d0700151034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 785446654 1250 785445404 785445433
    0x3060c020d080a06050f0d061b261909050a020d030206010611030309061501200c010207091a060f07080403050a0c06170612070e2707060e0409030908 66
    0x803200d01141c0070428100014030301001e20301ca00d1040e10740003403c81d0300400d03401d01130000031000c14400b215850f61b10001a491807040d211040d002c1405552203251460741c3c001d42032000b012240120142d290301d0824040c80b50b41c9510b903240b032400710100024040019003800e40c41d0800c4900301a4020f000269014241940403030706a05071022600e071401000c1500d8103161381c5c2e00c412a22880c40340c1040020540c1c14081c1a800742501d5014540300104100c1030000713240650312400100b01c250700641c0c84c3c4004c0d580500803280181130480c4200823590391182a94032140090901c18030982c40060204102c0022800b03032256960016640c0e5150303a180e00e0555500c0b40d038010141e41885c08140b000803040d104100c040101c180f44c40500a003621100c0034000c1354402c102d28041540201200460116007585c0700c0c0340700d036a844a200c03403498442898000c0b507881c1d1184002240c1c101c6a03050108070342111541e11010380a03a40040c0034000303070030216460b000a400000050056005440701c80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 785447904 1250 785446654 785446663
    0x18010b180f0606040b0d020a0908161509080a02060d022808010b03060d0303090311030a0e040e0d0903110a03021002010e01321b0c0a050f0102070804170703060c02 72
    0x30441d00440e1910340e107540c0d040010a01480c031401c60007800404c08030090004540181c2028685420468055602d403c41a401c20906002c04000054103500400c80407021040403607500c1c0842c24104002401c01d40520b407241400c02010f03000e0a800122040c0c02c3c495941212900304507a0400c0c40083d20714000403a100b150501e80100042d15a00040741c850030900c2220301508004004a1925000f43d40960150452942c207505016503482400f070790001c140000e001d540c81c599030315942039004200700011280000380d09040d0342c0c4441c12500c0c007541c10200c0901a05e03000b03020150090a4000058048195030708007d4000c8816000100c08540541012201c0e0a5102c0240220091180000700c0c0c600303820056010013150090100080b516200d4544d00030201d10034400c259007020303600f42c2440d0f0210351100c0166000510120900a05000c1e0406500d00200250f241c404c82d900c0c0d0501a00660180b084018490a500703c10f200c4204140c00045d6805030040c44031120502029485 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 785449154 1250 785447904 785447911
    0x1e200109050d08070f1b0501060902030a02211021020418260d09050102220509010602030705060a0b0609120304050a0f1a030c160c03140f0618010b18 66
    0xf294500740400c0070540a000704440c90303181c070394032080610100d441c1d455281100302d4003a54255614900441d00e100140021032140c0703040000582e44048802c400b1010851050f4048040f00c11070090212101201c0200790403201e41d00e0349413501d0205880400c425120071480294000d1410400302440007142c02e0001042d4001d25000c0c41c15039448095183d00f103a21079018480c40c1c41041980e0200c1e40d19400b0b40d070f5541c05000010b0900380309000d159840e03400711000b003020b10b007200c00801c00b43c90228102400b510251010b0342c24804d05545040c1e40c2c200261221120035183d50b42e04085132918402e580c64080002d2a0018640c01044519266400303405658001c038104500031910a6101101400703c03022000d420420810046582025403c054a42c14100004110203c01c20300449451003030713240078020320365101d803452401449141c8500c0003603010341c0141c0b00003c109c1c040818400d500102421081c90b81484048646004000e2405116441001c1b0140c00741d4140340400502d21 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 785450404 1250 785449154 785449157
    0x72a0b010e010602010e0a0303150b0c030c071e091a0303210a090308040219050a0602030d180b06190b270105040506180d0b01030308161e200109050d 66
    0x2490340c0f982800c90a80d849040d4031410b90b400b0541d80e1001a00c20380c007a0003020411f50200400e03d41340c04030354800350700450b04020f0650010514011006040c00000f0041c4200c1e00c0c50120220180c1030014801703441e221750040c60f50741d520007075800100c21518032034000000f0b0650366100007100504a08401002101c0700301185c0c0000a52503a01c248070300008590151143e2240381d441b5401c02c40090725a410030007440038101000500390301c1e642900000303016a900595141d01c0403403a02c40881e5841032069010221928044001c00c54003c0c070150040070a94220502541c8410007031b2104070b4a90240420744800a484040303403180003810424100c6080320f44400a4100e001118140641c0c001c01d41c0c40002000030400e10780000303c420000e0b100150140d000b074848bd450b03d4034000001d910503008506004100b0002c8180452043c02103c40c038107150b1600003417007824030f030420f02d41202d200034010540c001d0000c945100c5044041142c0150003031200700514074080e0344a0b291000f2540 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 785451654 1250 785450404 785450429
    0x30403021c0f093c0911040b0a261f050315011203112416050301140301020d06060c05060a0203091902060d2c0a0b072a0b01 55
    0x14a00c5100300081c03950b1400e6641d848488504003c007681940d480d44015002410b0603907808502e044003140840100c0c0e00b995aa80030130f0740380400c034000b0f880241079200c0005500700710600800c50402c0c150b17030b60316802c1d18001103151000038900046e0500a16840c00354134004d010008207904410074942200041e8a05c81c040355500d01c00d069480d24101203000d070340b01080006009003000700083c8074005003c2d151030a42a07061030a11410601942c618550303006280c20318000008842c170402e41c00540c1050007100c1941041801841400b041c083e2281011400d44464040d640940555917000c4080c0c40400440342c0c0c0b0304015054a22581c4203e9480c0a1080080e607440214802d482c1318640c00406041c480c04040e40380a070701c000340761040307901800510203002c217028584140803002180544e40c4a689040065100012a54a00ea8007565000e007d294001407800c01c0001c1c1c1022032400d00026110f00840b10300c4100800903444085a48000702c14410700684a401d903048030240c50048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 785452904 1250 785451654 785451703
    0x6040f0f0e0f012a05160b0601110d0e15040b0d0c031107050a02060a09090c030c0e030a02010e270406050f010e090a020d140a06060e0114180705090603040302 70
    0x140d00f60b1320384011101208040c1018542d80d101c010000b200841610315001d4600328a5200d4800c2220411000f0380b04d101d2020108006541c1111100c005074054030000d003000a004500108003200444000d07000e44180e200003041c0c510301c08196000f40c20095001500c800b10003003050020440d200482c00003a080014414180c0041c40c21902000d4209016203a0b4641c241c0900100c2d034080349865080000c03500c400143d41d89588a801c400c4507460340c003ca207880c4241001000c480854448502ca82c1102e13500c0c100517a000b2000e1400c00c3c00554140744440c140401503040c0c0d07940d4015584051078880208010400b45a000d41d125651414003001c01d0b90301e42103545003c0b581115250084d610850b90030000d0300c0c1110701072102070312815003110100580c1e0500350a207810f5002c2110f5050320343c0c3c03050000981c4444014058044840b03010f000d081000005823080145250034081082c000c0d000c9070549100b0003c031003003c80042c10440d6682000c0ca00295220f14401104620003030407e400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 785454154 1250 785452904 785452933
    0x3010f020c12070c03062412030e12070501230406170f0f010e0630060c12070f12090305250201081807180c09060806011706040f0f0e 59
    0x1565640342d000044504c00c241550365150003400c490341244a05000c070b96404015110490102d40603060000c44901e40c05d19500e000382c800f03420180024800da2103000c5900c00c220b0b002401404070341003441d01b200c0009540b0b00c56044440604080c11204000103400300b44070b50800788180024070070b00d00740d184039951142443c1030b104064910034400f010302001000300c0039540c40d846400420080003039143c0c40c800f80c00c4400c0701d280c10b814508409102e0705c0e00c140d40541400b9140e031000e4509803842c9003010380b5865400300340006142c2070030706c0741c0c0411003003a09108002c1c0071070000c05139100b0013445656060140c81c0350000d024802680240301150002078016001d20002c082e0306848844007a100c00c4039002d1a00f206240900301131081140000307025078080042d26000303010341030004141e407594400824060701d503041942030121003001d2101c540d034000d03480055105000344c140034039254100010b001d00710008404481c6801c00351041c0b4046010744c4416041e00644081790300d5034104918 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 785455404 1250 785454154 785454157
    0x31e0f0d0903080d0e15070e03030c0c0d21090f051905010809120f12010609120210030e0a0c08100605010e131b030509010b060f07140c03010f020c12 66
    0x40180004001c44410000103a03900040d0100c411181408a041c003050817034a85445419102c120440c1016001e1000c500d400c03502407a8514026006185003003690034182e9501e00d5078144d1207020b0008c50070001d041c010b0700908519060300c100241c603020071404500506041550140000310403170710b080020344d4505007100000d185e00c0301e406c00b65841e140c200155100d0400409110b49805a0522284810301c40b800824128000b0000c040e11612544900c614680d4140c20034000d00c49504420721050040440300ea10b0a5411640c170840c15280941c100e000c0c0191480904c428070071200171008202200b1190303015140d8801c125103612242c110610241c804038400c46001c107a6420b001801b60401540409542c68860750101e011244104103100c0b1030048800b4800282d51403081c002141c000313001c1d45281503000c680560400315440b40c502d84d02c0c890354030000d10303000c060900d5004514052040b10070041000303008021641c0e01032200000380d030180410120500400a0300226915440d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 785456654 1250 785455404 785455423
    0xe090f070806010c0323090d03230c070b0d06030605070507030210051911041d01091416050706110307120e07030309061206030818030d080c0306040c050405031e0f 72
    0x43e1000803003032a00c0d2500d02c0c0c1001c6c1c00c0c003070442030104004150700398035070000d40502144243e0340c0b440440481c03101441c0c200c0f01d584404c882000d0820001440c0040011800701796a80224075582d81c04181134010003c1483e50300c014409818138082190580c1c00401030482c031802a02034650741034403520b10100310b880890302d02640340d01d004503200d40088154040c2e081441c68402813403615444440b214541c00e80080700403071030a55600140452030310b600031110382000121540c3c1c40f9041c0640381c0e132120720b4024a841d04205010900b0424043d13560003000d03041e0b180402a0740d5a06001d00024110f003404020341c8081401c0c80243c0320b60180018001003102e4240d07aa4031512800e00f80102c170340a0070316171a1901d445c0ca4100c04008214584005e00c1442c0b90381c0c444080081d85201410b00703060503c9c0c207100c1404030040030005a413203400100d941c0504100c800081d481c044e10000e4586000d15000b072501031052444980350011a14907501c40c0004c840301300d48120300d41c41000340d900c06c800c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 785457904 1250 785456654 785456657
    0x20904050f070221070b0f0415140a020c01022703010c0e091803041a0a0807020d14030601020307050a08040302090610020d0e0604030203030c0c101409100e090f070806010c03 77
    0x240310341d180900c581301d44040340241041c0945051020b86842c151a40295500e40300134040109000030840b10704091031300000c3c20241070012016903640b178403003040c004218540d156000200540d0004007036040345e0440740410400e01280f1200401e20090482156078240298a80714026460900070061440000d40c01403142c0341b19945c1d018082e60307211041c0b0b210392407440288404101c04101c0700719401d0070460400f0303907611800782c41707002483c0700000303030609065400c100100da0754903a03c82024000f0002d2a43d07003035a00e848440040f4511b210740d6202414901805411404000b0100b009000b04c80c001c41c1c0c1c0c401207484960401810a81e1070042ca80581d005000000382207002d5140800100c3d40140810704040d0707243c010a08560000ba54580e0b107420000b41e02080745041151041d4608043c030b0706120a5090701d0340c0c0c03d002d200740c030206031248200303182c800c44c0f003881050301110104016181070302c1400d090101940040701501c403500459007020010340b0551113025080d1015405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 785459154 1250 785457904 785457913
    0x3161403030f190e1c15020a08070c171209120f120402041b110708010b01020c0609060d15030302150403200c0405010b130504060b0307050d1806020904050f0702 71
    0xda160010f114012424801413084010342ca400580d80c1040d15401132441c030b0100d8480c1e4000c1e00c1c1c403000951310180d400040910620420b07100960191400c0e6018030b55051030603011038a03040200c109c2c2c1d8040e10a01c50003100141d078411403450006400d016450749002c58240220805450005d03006560208200d6002404a00300b049608001d00d6002b50028000003064240071040150709628074052030b020840b0581680101202000300800504203a4000c05c0003181c40750000f521410a01001d51090101180e020160317030790701c2c0071140c2207840c1d48030400100c501e012040843c45198882030740507000b803003190403410312940085486554035584111080014040880c690001c001203a4254405c1d81c0070388459890b107200340b5020b046100d80c10f030341300c81080000f2118104641c1100b40140c4c203182c000c00001c410101640d03002580d6040150311075000d070b0b01c01402010b4000099800401d4a8055011b0224550003010100e0341602c081c8916903510f8109140c090781500c0c0c03130005900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 785460404 1250 785459154 785459167
    0x1503020609190801020f030402100804050c51040303171305010c08060a0f030f170d020d0605041a0a090221010801060f05030609030d0f090203161403030f 68
    0xe00c1d20b0110b842c11014221141d61a03150100b02d42207070490035400c046010004240810342c944200c2c5009105403628102c110f500e442c5e0345036516103c144c00340728040c401c000c0c110700e2008051700b4040ca030315202082e410074100851100c0c0c3c440180040c07409041001c54030201c641102907404035030641c1c0d05626070240408039484102844800281100c0a508040c010703800050428020000307241180e13644c041041c24a20100410310909030701c103903c4a0071200301040001e00d50900c011a8540003168011102880074081d45144074240305141090f00c00260b100800c8a50703448042a1007042c0c90030086501914860b90b42d010214062503032103c40030324100054409034009160ba2100d400b184101401c860b40341150b102802e820800343c1d81d445407401d1028440c0d0404e05001007500714000d00003418490080350310317841421002d000c190780b02d81a0078440d4640341c01044856a0140c00c0b00c0c400c1c03408205681c10800c403402065800814000985900d180000583d14900107107000d207443c080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 785461654 1250 785460404 785460409
    0x40510230d021305041101090e22050f030703030b150702150d111207140d0b03030403080301080d0f18050913020312041e0614030718090b041503020609 67
    0x1803039091a6540070581091240060710742c04a014280b03620041c001c1018102850301e0030410340000307041410814003542c2004240740d400c11440e0840c60300425009800d9041d00c1c2001902443e841c050014403600b4001030101000000800e18607010350f81c00c0040640b4102000311400c500c0009446a01080c024900946800880e003600840c26415051801d0010748036002603640e03189102e54507150110306072109200031444103a03c000b261405110394030140030107040300e016007529640c1e8a0360303a107503503012620f0800849000d940c0082d003a948039070b0366139072550340c45c21007400d40000a014115080c0020b030146004000c11982400d1400d03000307082009120402c90014404101f8941c2c110000000d62424000c0460308003110640e1540ea5042154a00c01c3d48551000d2031800441d40c1d4003000702e070b84c1c044c0340188440c000711a425030340d460f0210125002c55003400e038811101d000c00380c00a11000d00303601810061605032414884443e4000002c200130100344400384d0131020400000c841d40c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 785462904 1250 785461654 785461709
    0xf0306051011070e18010509060606070b07020a020d0804090b010807080118060312030509060f0c03150d060606031a03011b050c100212180303070c02010f0e03150402040510 76
    0x1e51003400300d40c0f0b82652101c051105000a441c400c1c1e4110014610104800c0207009981d4042c80c43d030028522404e290300031482a00c50b801c4081c0c200c1c9540c501154100c0d1007840651042c5400a101862403000d500745154030380d106118903042607152280c640c80e9940944030540c410141a2101c041582c6480b41b40e242d215015074052584965454001c00001c511018001746a0701c140e400040c103140210ba098030742074014241c40160092041000740d142c01c00000c41e9806020800d15802500340b01003c02c1031501c0d402401440d1074105400070a501e0b41c9a400580a04224031614110040210506003215400000068038250b90604d14400074000ca00500040100d00200d8440403501c3c00d107002240c2003240169a140318a0381800b61000c40e0009282e0383c003c500f0b01542c954207002e00e0240a0b203518000c02418032000510145000380a03c481c060500405426074080d5008801d1100720b825049804030302c980d26007408034126400d0b21100c04240d0345200c010b04941703408507910341d403032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 785464154 1250 785462904 785462927
    0x30c090901140c0c0105010602030f04050105090409080c06040507060c0c1e0b0c0c030c010e0913081e070501050f04020915220b040606030b0105071e0501050c0a0f03060510 76
    0x1150340351030b0603004407800505181c0c031400301000d10544400b01c00c90700b0340c00c1d5641a8008411035005022403100f060880d07003140e04650090800c0c17503942c800e42001c00c000c0d002040e406014180041071010480e1800b20324a40315602c914166025281c6404055900c5840d50001a00b170760814042807143c083e451603150710b4a0010718000d40603541d1241c0d644e05560010110100315006000308400c103007800c10015104580c01d003410300502c040400800e8101d0030081c62814000000e1444000f031041d048100d95580342d051010380108200c0150010041e405440100e440b90301c0d01e000600796201c4800051b01a82c4c0c020071035910f80d00c954514102c0c86c44000e01041d4060401401012080c058401842054603407650116060407040200070886001d5400981807500b8200400640d0ba484800c5444031a400440d45a4003052840500701e000800750004116618203400c0c00354410049000c2c0c034082c407441d5500e035004c00b501f0b14120300303961a074400d242d0040c0d00007520f02c240c0c0c1e021301c101060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 785465404 1250 785464154 785464171
    0x3060c1c090204092306130f030807090519030b010506130303200a03030b090901050906010909060b120619090b011802070c0e01151403150312030106050306040515030c09 75
    0x3010300d442d485d41000400764003071403c5000349a035031521a003101889059030003c082035143e02e6480c4680c5490104004c40300b801020070040c14002010240035800303610241401400085504065401400b03d14599010a417400700c109e00000401c0d29000c4105c1c3d2b406250495582c1d1001c0c42c2d6501501c0d403800c004170480e4100a0304a8400589200300001200300340a80e4001c6200e078801410320091020103060042207034140001c00c507140300b00040c202c0c1101e41e0792900040300e111608010300100140000f0701e9100d410260041c404010001c0c00d18018001c4d641e44044d12b103000da81520840b1440f141c0103004022204c010044520710140030381c6d142c241d60002500d00326455039290003224180e00300215417012030005110f8111040c08040030010300382441e19000030142c0d00341d4800c0c0070041c008024505c2a0005014a80303042c864103201e80750101e4a1500c0c2c0d42c4401e8040c0c030f59081211003901407481c140014100540740c03078181a070f440000e006841c00034105e03018401b503c3c200520844 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 785466654 1250 785465404 785465411
    0x10140a1a04181a012607121406041812080709080105070c110f0d12020f06091b1c0f1115070c060206010506161a1503060c1c090204 58
    0x18903140144a10b4548041251001407600882010950714180d505800780c10028441d20f1a020544414007802022004500f5900301d030340c805104440801c40b02e400c2c5820241002c41c9000311802c8100a14040e88048405001c44944060440c3ea881b04110002c1c1c4501204681c014815014401240d00100b80340707402015a03480707403806825148140c40410004c0d00071300f04030017030100041c050603a41c1310864041220000100000d0406400161301400042d481c03141500004d0082210035103a15690341950340910b40105610307290700c60010845441701008104107903514080214590202040c0d54140c5000780c1c40d201c0100881ca182c0f01160000500040c058203070307450f101d0144000c60283d500c25030301c0c0900e16144c0304403042a4032183c29035020a0041c0401d42c0da0101740c1e010040d80e110744005c003003002c3c200014a24a604500010508804180520700e0030145410305d0303040e0140e040320031944420042590310310800d0207411b00c1c914101a0b0311403002c0341d5007049000c20300052010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 785467904 1250 785466654 785466659
    0xc030907030c060810091514040e0601031218030804060e0301090503040b180303120408030403090f06050306120d02031b0c180123010f0c06090c0e10140a1a04 70
    0xc0d40842c06504400d001ca034403a0104940d4102119010001c1c140214085c03240b81440c03a80300c55140410300400352010b960703015412540d100d650020340c4200f1302900312046540d480c101640200d030f20340d001100040c0039003007030701003000d0300344900c01100d501030030040c90f040c43c16404654451009880c90344c15501d40d43c894010413000c0000e0000f070015072108a569000d5900b502c2d0050002c280c01c01e00036003082c820b000940c0584124503920a403c540c1d2582da90740c80f443e04840b01d040e81d400010944114250100d6150341c001c01461280c90241c40c4140c0da485a403c00a607a03003454090000168030811515040b0b151210114036002050412280710201220004082480300e110b01d280404900380104038030001d4519000c5c1d080007102e000c1e401c1e03901400c002000b5045e80e00c806001d00980e07032815010405030350711400406401000c032115480d240e04943c140e6440c203841040b00c603800000040741103040301000d80500e41c0e0040102c400700e13107800c2d85002080681810120817030300c00d2000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 785469154 1250 785467904 785467913
    0x6011206080d0f0c15020715050a0b090a2a02030c0312060117040f0215071208090f07082113381c02040b0c07030506010501020d02060c03090703 64
    0x21a80501038840181c22004589500149400c01045101c020007140e511104d01048210000d80c010704012240581c2c2d031680c0303080c562005a0308440c4000c1c107610300410081550029401001b440388111800c5d00c0796210184544141e440395651580609071320513508144c50f070101403070010940a0f00641c0c0c181590381e154542141c0101440f000b152001e5400c200132580c5c0700c0c07090110300c030303103900c10490703034203003511202d10030803165500030301654203041c1e011848440344059540503903200c03004112000708054000c00c4080c0c15642c1241c103108045c825144a500480d880042d1000e4000a188400804081d0b2075403101078992040c6038a42081101100c540c40100034016084900164020a0354500f1100d4207038003c0000f00a90175200401010b1004001d0803244114140d0107903011140f07410569800a100310352009031006000100c0320208080840d200c000c40f400b032016104940c0e46c80c40103a03110031146220070016082280058480c10340100510381040b242005c032a40c168a0340e58 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 785470404 1250 785469154 785469161
    0xd111902220f09060506090109020f0409090302030d0c230a02191a0906090607020313060c0c081605130612030c1a01240201110405060a02030d0603120f1412060112 72
    0x50945030340d502c1748200102414800071650041110400440ca000e00c0c0e0700d03280c2d12a000f18080d8040003034a41d2803e02c2854400c0042d02c840322a0b0140030800c0b00c054080203030452129803102c3c0446100880540c2e50000c88005840d01c04103950060040f0038a8003001030030b030010240040781c0182003a040c52002e0411360f03021511421080c4020640350801152042c03400c80700074816030842d4010801449940403186810044030050708020481305960310b40075800c0c01103a00310b28a10700c00c1c6501502151000c3c06000100c500942c0c440419107080d202202c2520b640740074a0140c121000d2000000a101b01c040c1c19400e1b005514019510707803060300c2d409070200f080c1e02000310f0b440da00c01540c01440b605040320030051404c1c00200802443e44a8800050059210300e0341b01d0400401d264083c03030b00a1044480e600b4025804001082e120f10f4550300280c0200111000110a2101000d09902420042e00c044400c038004a06000e00004011080300e401411181080b04602804251490900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 785471654 1250 785470404 785470421
    0x90d0f03020706080a05060f0d1a0907140105090d0f02123a1403150301020f18010503040309140114070b04050115180e0a050d111902220f 61
    0x10702401c11a45880320041034444c024200f0000c0e0b52520301132110303e540ba6075040040a80a48480140e400e05042c11a0380d600300da00c041205440381420421681c4010034850103850800000d2000d401401d4011141802503040384c2e42c220440560840102d200c0c40605040e5070310040207070241d884581046824444400004103140c18082c0685181d405034200301900740c1d103426201405900c10714401041848123900200901c200000032503003918130241c40124005010340250356070501d6100c10308156015031b40c2c04503110040d0001001c07a6100b02c041f207000f01d816942e444000c5050846480c48060380000480c1448410100b814542482501421085000300d0a0741c143e0324050404a09403002010f40e103940145040046c0440c444c40c0b003685130042c400c10000038601843c184202c0c908178240781c000e8802d101302000b4500d2141e021522580c2a0030380e0341511103172650924041f4600194200c02940b03c0c042c420383c01c81403079800c01081ca031308028003404200020f10340ca00364101d030601c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 785472904 1250 785471654 785471657
    0x70c031b2f0619080c07030509010305070203190903020406060e0310020d09150b0f1f180b0408030711091501030b0a030c0f0302150a0c0b040812010603020c0f0a050c010302090d0f03 80
    0x100f00a4403401c0d044111940d03c618401c0ca050710703120303c941d40182613100f62040c0f2410300d40d4560100d01072901c00c0042e1000c1e10810f1901c0b00205030003c1c800340480c0c942d488201d00c55070a062002c02c2d071611440200715200300c003400600d1809581e1030000701a411103013880940c15540c10307401005c5186030344001d00c20342d0304181c001081702c1c00b0030612500c2d81c00c002c41c1c0e034040c011080c0300840031940002c1c80810a4820318104a102c0100340c0e011502c000240d101540c8800c0108020030200404402004004e2054800c01d10f409140d2003400103805007180c0c1c102150304298180441540030b500201030b00700c030061070b107113002e9141d40c0c1d2a440600960040e64000b00180310034030442c2400c099244007241040c2d846400d000241400502c5010300c4c0c00014071901c205804501003003402c6060703c4101c4458070000d051580c5030360f4020300039040003100300d0741d51040c0520b100a4030000300d08015207540080c00f40c0100c801500054010303600102400d50042810740d0360b40040381c1d00e40c1040412612070b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 785474154 1250 785472904 785472937
    0x2130b03251a07120521090c01050714030c03031e0603100218090703020c010c02030304080304110616120801060c02090a020a050702030a120806060f0412020402070803070c031b2f06 80
    0xc0003020346e101204040c0c4401c100ba4900a02483c0d1600050140b202e0350b00340b07042c0f5600d400e41e14081c107081e4204105084140b01c003160800307282d803007c4003861040c0103450b50039000d80c680c08600000359505030707007540e099002050060160682a0000c10a0310620341003107400c08039120104850b008200ca49400003a408074507007501020a029982e100500c0348029800c508150311854468407001d44020220b000c49000c0e24240d4442c04103840b0520100d4800a05c0d4081c241010058502030607107800004080000102d00365029181030502c942c1c0250440110355901000c80000f944400001014808107010110060360100b0129507000d10884c0726155168103c02d003c2c02d010300151545224040c01d2000410511040c2d064504a95071517105c45418640c900100f0001d104002000d4000d202c000100001250007480d9001914801d50746c0300f05101d90505c480d4141d00041400400c3c1400d1590110a0424084898110352031a1080b035002840400001a102c1e0700424041c00d10148 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 785475404 1250 785474154 785474167
    0x80c0307170a181a0702070f0b0a1e0903050c090720010b211501060c06050a110c030a11010e0c0d05121209010b0102010207170d060302130b03251a071205 68
    0x40c9005550441701500051082c50704141107a00d400c081030007540040e2102191800e103440c0f0130320011201100b69038020b0711070742c58407070010000c030701d54042a640d07232050101a03403450500c0c1e45040c1c401c01569942700f603000800c0d82a102026040c501003d410740d00d1310309000640c1d4903100401c031422495500c030211528000d00e903a08000b2112200280b40b04508010400c1d260403900c02c0d80c0e01c65020000041650350384103243c000703141c02c036a41d5051800214490001080010050a80018584440c0046038500e50342d0380c01c0e5030080d290454681c20165410405042c151614000280300b0000d4a070402c8490013030040f180c0011080c5100d40101c0024810130020a221310007550170284002d524019003512035141401510501d12900b2200003101c46d80c20017a03a00c84030183d50b0043c102a91000200006805000e100c15000d10a0084180703800100ea65030703080c080584019152500d00c0d9103030080d02d1943c150b0204050403d901c1c10072a0b000000c0c49181c20b0860607507952600341d110718 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 785476654 1250 785475404 785475443
    0xd022d010e1b0a08010e0c090703020f07111306140d080d05090a03110606010c14010912050307030609060e0609060102190b0f01150e04050709120c030201080c0307170a18 75
    0x3d12580841d1240c0d14007a031a0424450124810301c1a00c2c00340c0c1d400b9102d441d640300480092007104410b43c00040b0101d499001c11801c1c0346000c1244404560341520490140960b208841503841107001050300940c03071500030304206440c90b003164001c88426040070201c00c47e40342580c108480d90501d41c3c00c05035401c0d08041c2c000c419040540603c600616440c0340000020345103611100010300302e0030982c0038450303820b40250400044c0726400394100c80340440705003000e03216810948074100803070304099000c2a0304078188541012640b9103444504c00e62200c405011000c00081e19450440c0208081a07207601c04001e656808244118802140e5140c010710118030320301c0c182c100d07041c0742c2d9998a1240b0071f10751002102190030011980000c880d1521182542c3e515540da014220382001103094030140f000b82e459502c109c0e4002c0e21030305c0441d5110340c079030402480110783c1ca8000c1000c1055040310ba28114280590258002000241502001e052901c501466280454070b0a4070082c81521a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 785477904 1250 785476654 785476669
    0x3020d020d0603051e0c01030504060b0d05070314120702060309032502010e1f180f06051c06060912030509090a0e0c0f03070b0304080f0c030703020d022d010e1b 71
    0x402d29a0b401760000301d01341e9042d501c0d48003507881035040644600108080c40710640c4a5a0b031910010700892907100c142c90081d460b00c07420f100c1512000d000d071692002d02c640c0800d4149240c0c40d49881c16107008883c1d4200903d580001d020031210344414040c02030b900515554030040788288005c68603001d109407000400802c0c68211860040039692641d110030300140750030881004a60520484440807012046050031441e4007145d04056612000203039582c11a00405200511460403403040d0f403251400c0080c1d400a200d60400a45203440811100b101c1100c11110a48a450711382d2800d07001000160082c0400e80b43c014205a0740c0b030000000003020071405104050540d204804403042000007500c40416100f180350501c0c00000040c01c006d00740301110755042a084015131103865200c04550790781c2060008501500c200c01410311240e00001d50301d00d01303280d8560000c110b40c1c198101400220342c1e141520305150748480048210b0b10003482010852104021040405075a140402896 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 785479154 1250 785477904 785477923
    0x80106030305191403010306050901092319051f020408030703050c0d09080c0d050c041a03100608071203021006090b19050904111c050c091e1603020d020d060305 71
    0x600c0b100c104020304544d000300c140c1781103e8215100060b65a20740c02d40502506080e500201504141255070060024001026603880d10f000e00303c1d0400500385441110701e44030404090300a030300c120201d601d408420b00d40c3d00701d20740300c2003000350030325655150702c074030355048160300b1030201d030740801d008145041c20003c0c0a5000881d2a104d03d40d18540b03072a0700d8445060b0300303086014074000d0415a00f031100c20418242101c90140c01008031080e401c0d8054131b8031003058079441c8a40500000c0446040903800b5407815039a03402c001d01040e5151100380301c100300104500300d040d401000c584c2080040d613032050000400c80d000005c00c003c05e600f42000a0304000360780d0390300e00c500014011302c0700b5120201d04941c015031090350341c4284a4910b0014600e503010341500030007100e50200c518100302020550404501d0107843c6100e082d203405030032005035103040080e0180d4400402c00605070b950003040c411110082d41c02d00618103e94002024140d0303000e554800c114070740382d4000f00200901000801d40303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 785480404 1250 785479154 785479157
    0xd0203090f0a08190e10030c050f0409050702010b030d0813030c120809010b010914131d100b271f0906051201140a0f061502061f1d04050708010603030519 68
    0x20004941000506e0480c0c400c024041099a9140300c1d00b00e180c09882141d611414440000b61181c0c1d42d084944050f01080b9608001542031442d421203d0034000b420b2001c101c2c407500d6101c555641c4c005000b00c0c058100034264208107482c82c981010507443c05658050000c01ea40d9100e01e4505000c1442c00d50b041e12003110704100d00c0000c10050000c8035410944250741c00c8804422410140c54250701424205002404e0075803000d803100590040066003690440b030305002445504800f400300a201c03c0059000c16094034904446a00c1192a0548583c010000c0c1c2c4000210030194055005504a070b8010791212a55000c0070300241c41e01d03011005480a40c10000e004107079110070031200317214018100090058494002c281d4412140c0c01030700180c60400080e401d00112840300954550f025601000038100c149240400d040311442054240d0360307007501c4481083c40f00d51030204041002401960a030280700320110705410280554001903000b41e80c1e141d00c44041c2031402c038aa05080c2600c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 785481654 1250 785480404 785480417
    0xb04020103110c1f0603140d02010b01031109060a0c061a0924060304030318080721020606060c03091512010603020909150f04050406051008010b060d0203090f0a0819 73
    0x3c40c101c000994005444840f03c40e02c2158042010b60402400385a00700509580700004180040d40d000104a80301c80c945600900c0020b01040c0150200c6280c10582c1030b6043d02009444114140703c802000034404524240390081d419441c0c440440d41d19a08882c5046090101810301d858120781242d002407903440d003005410300c500855560041d68461880c000d010101c0020145070227903008020011828820090000c00c82c900050f807030b40024000c5500381d4400c00110400551180e07245070240c0160010007040d01d91808001058020074031031805807000304121a03064546480400c50340160b2140345849403100010b0038012003050300020304152060041d05070310780e5601c0c0c40540003400241303891a00440d440200305001040c2d0829a0090b06010500003002401c0e8055445494003844106045885900c46426541c917030450903031085080c065946a00e0741070380115002010903040703078001041c0902c19801c0c0b028a18003941c41d030b0004a55052800c90f12140d514454856103840e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 785482904 1250 785481654 785481667
    0x7032303061005030f07140d14061f09050f060d02040803030a052a21070f09080c0109090213030c14091008102007050106180c1d0a120b0402010311 65
    0x8421704c01000b400300e401c200a81020381c0021000314107d5412811508003440003400e032005500c004401542c41c58041e005240414200b6001c0500983c1c0c0d03295030750303101c0c0c2c2007925000811410f80d00000740b031ba034403a4040080401104052005000802030f4401542d00c2e4070b403071103012046500c001c041c220303074000c0c001c03040300041c110080300000c160302d01d00c0c155140c6890b16039540003c4000c801c03a19031320309010305005015820134000361219403940c0e00c02045039146d460f0071351201c120403101800b24400000a0080c49110780103803642444540e50280501c1d6280c482c00c0004940d41d000c0003a0752414154202d03281040702020350b101c421140d00a0440f40360844441d5502074800d40303414216501d800c41440c880d0001903c0310040c500950080d00c0c2d0302d490510070b0080c141442521014150202c041d10030400500a0f555120410b44a5103504002d00e442c881c00a02c100f00c0325503004500d003001080940444c4514050135005000c41415890715100260884082c540011940c0c0c05c14000c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 785484154 1250 785482904 785482921
    0xb151303290c0f090901080c100f0f12021303150b041e0507090302100f030e061302101b030503090f07150e0414042405060a0306020703230306100503 66
    0x3810b4000c2404850340b5030380e040c0016010341c18001d0101e000d40c03102c551800040d18007000600403a1002c0c00716000e240c10a1514425601100643c07029000303c1d4214a40c1c1c014035000b456460400010640003514010302c06420500c040c15640085034409003000503114000040d22482060250a03101003206100403000c080719240d06060040103551030b100010005440b43c694040210340c05005402400c0d000000540340581400c0d00e000028644000300714001d03000205980030b082c04441900301091250284868180c0c402d83d0f88041c80944440380328a1207000c50a2000070340282d440a0b00ca0400c4040c070750030541050081c0d40d0a42c4034402c11b20812074811045d031780b842c00500304491000c7c1d0040104000c2c000984104d00d11203040020401480f54010b5503003015070010103461208082030f900fa00032548240d403645d402011444d01400000d402e90300074804140a401c10f1301c01440720090001104003207464140711543c1c0403062100340c0c141074458080380023441c1400b0b0709603d812040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 785485404 1250 785484154 785484233
    0x319030e061501030e0d0e01110c0a03020d02060708041203140703020601091a04020403050a05070e0c09010f03110c0a0201080a0c0806190302030303090303040c05010801050d03030b151303 83
    0x21082c018000400d2031020303a010b03074810758204481a05840a450f0002000381c8000340c6a02141c0c0841c45c10003400c40154000720b0300d01500f6000414646140c3c0c00d58083c403019000d0080700700d8110504000100101e106074010700014848552943c594102d6860010840150f0318082501184140311a00009402083c1203054900c020f20000d650400700d84a21900f0088056441c2c00900c000340203c02d020001c500f0041250046003215140e5980d0342d0505d9141000f2901d6070b083c2070062041c103400758070800040a1452a500c1c011511400207a003a2003113602c001401c0300140d012229107030465810a040c25440205030008200320303901031502800c1200021b02e01d074480c54210320540000e01000c0812000785801804407900c9107440030096580380d1058800341c0728000300d5140000c40d58441c285590588002600b1458000ca0f26901a0041c1a28403080c41e40000c0c42e50704015503800070b102400c210010604480752080c50750621a01000301852960404038000400a000c2a403801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 785486654 1250 785485404 785485411
    0x302070f03200a1a03060906120715090504050114011403010602071208190c060501051c08090a0e16090801150501051804060905060310050403021c090302060c0319030e06 75
    0x1020b800b6040c0160004180d601c480e000341030507000c40ca01e00c0c00030300d001c8005140300d03010580301043c0a880300410019083d00300e104000c6983c0c00340c1d0090111001c143c554039050b9803e0305000d850303141c0b5680010142c1e4000d0300140c0815642400c01846580d00c07041007001510091441407440d4103084000351502024002d21209600074284442004602012605c4100044c80d615030300d500106401810210011070546034981000004103079440c000c0c5440d1014406011a24407907a40c1c0d42e18201c2e150080240c2070f91200c10520001805129524158401d0092440d07407503040c2150380000d881c404c42c42c5c11500d5580e16084000c288804c4051800f8181c1d01d090030300a40b034000640b041d4807408201c20b1101d40142c03c00c000044e00c0f140ba500010700981007201601c6e020f40b8000214005c55008560160069004c115400d0303c2c2038140c550810605514500038a040b03449070040f811755800520400d51030b6000165080207201598058281a8180d1a0a01041c03010306d4171681e0b14403024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 785487904 1250 785486654 785486693
    0x2903301209010c0903050d1b05100207050d0e0607060b0d0b07030e0d090f09113009030a0909020f09030316060e0609100209011b0f0b0606040e0114040e16030302070f03 74
    0x7640c008e070100181d05016540e803507002c4101d4007419846540d40700a03400c807403001c075000d110361501c101d0142d0040e50300c20b0300034002a0035142010026150f040250052603065030300502e2105820380440d07084101035100702c1c0c0544010032a80c00c0c05040524001c61041c03100c0070041d03200f4007484074105540c0e480c0101c81500c000852270300c150344018a0030f80319081f901415620072010441484000c0c4152503150351084900c0b6081b562408201a02c80c40f030055100b0004000705000c1c01221311582c003034000e064080f40317401d0408080c82c02180c5140d100181c03008094928503007a00400c052800790f10043c1803803001400c458184880110366401802030649102d42c1c0101c2c080410341d00c201410102c44034115a03500311000e45061a1560360001902526841502e030002a001d050902c2140c0c05c03074448509003c0746a00c1d02005103280e98038040ea41d40c4c855101d401e16960385a04001c020b94802140b5039080b00305103985000381c90090313a036101210703030b1540200400216218441074070190204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 785489154 1250 785487904 785487917
    0x2030403020f060430050a110c030a0f17091e04090c06031b08060a0e090703080301030b0a050708130f030903060e012903301209010c0903050d 63
    0x440c6426410845144061116845504200310504c026500004550064445580f04821010000900100c04d84244030007061041041071403e510440400d04810020400c1e034512480c50300019040002004c4261103007107211010200f40320b142004400914020310754149850107010128a0341c0390310341d03540c241030b201d48460f0165a460701c1d0071090045500101c034003102c50302c50002a00411507141c091480340d1090000d001083d0280c40007074010103005080801d0580f400c0d241c04055100100088503501400d076000000030384d044007440c0694401e070034a200b285404960034080740d0008000e08100000001403080309011605c000f0303541d98111200d107484d030147d0308041d142100254001844e440c5486140390b2058010340c004291840c6101013403103011403070210b01d925a1a03000030b0650641001d03203282514010f00c2d0074a83d00b007030101880c81d42c0c41000d44054840342c10504c017804040301c08404222040a007849580c0340203001d410a00e55041c1591103d43d134a840850045003070141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 785490404 1250 785489154 785489161
    0x90f0f0e0a021224090c03010909030e030f0705090c03150d111e040c0512010e10030f03020a0605070c0b0f180f0a050724082701290607060203 63
    0x1c8980490342c1a0000e190000c080f8284803120400700030440100c0780140f02940d040812901e03040c02c809006901d60f018807400d59080c418400c0003030228001c12030a0050710034000c101380c1c0702400f10350f42c05054800603080f254071780428080798100041952903000400c0040000c1c0b02d03a2520002d01d220300554503101a000c540c038003151094031034000192302050003c8400729041501030310701c940c0201520240102c1315801e5058429000700814019049040401030201c02c4201c0c0700103a03c80d0828402494250703880d181c0030694034002c0380a400503013108840005001460103800c0c0c00c54103e04c2d003100055199110081120405070000d081e41644030046814182e04507188815103511400361075013201680706442d59040001c200702c031a409a0100004c2c490441e00300c2103401c2c20503003080e403414040c03544204d80c2484000c001d582da05588402034030a01040c004401d90508034040009071055115250900007580304011001ea42180340004140fa1655410f484540d540301c170000d03840c8c1d02c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 785491654 1250 785490404 785490421
    0x60c060b0d0618050f0705010203030f10030803070c0b01060903020d060519020d0e0708030f0a111504151a01020d03050c1909060e01030501030f080304050f0d0201020406090f0f0e 79
    0x92280c1d0010304068102035881601115180c00da001c85846001210002d940d0600c00e0303a15003507180b00d204d000d6042400000c00a400f401052907224208070452040140c903640d40d0070322500161010030004006450b22008c1040144c2074a02405082c10035846862940d40021800d03642184014081b0743c58102103a0b06590848140c8541103c4003c2952500d4100c280c2c14010001461075003103511585030009807000012080f41e11100781c070085c03646030014005042c1c2e4800c0c0d41c000f502481d4070034900030000051219141c240145d1107114250791100b10903c600090390385043c00070100592804d0254030903030b000260800ba2145a0030045815a00e42c42c40c00c134070f0b009070200e2030641c0741002c01c1950019400020002911150346800380801c0c150b000440480d802400020041c0f00d81c1c00184002c40c445001a662013446101180c903403900e0f211f41141481100c40364040581e4001c1030500115400c420a4006000c0050000c04003901c0d18445071141000d520030401e11240c070202180c80007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 785492904 1250 785491654 785491669
    0xa0507051e010f1a0603180a021f0305070e03030a110c060a08100e240f03010e0706090e15060c12040609140d0f021207090e0303100f060c060b 63
    0x40e10a8510062114a0018040c1c043c2800b51041e890051038041aa00050001050100f42c544c002d0085810341c1d580c00d40d0b0301c0c110464103002101f10710a0306038034001a40c0e2190300c88100c4101801040254120403005815114050006010f02640ca2661011910700205480000c0b00d03500e070840c3c0f01d0b0f0074500c1071410460030b03800042c0c0207000000c10503161034009001c580203c02c4c0d58400c001003a42e9a5035007103448025600c22042440c00c4020800b0400c3c10002c0718200807004180c40c03000040c0c03400203030844144008140c0c1a4221842c104119a04040b0003001400f030007540d032420b03180110166400c80359161069100310804107925041400070401c010043c0b170030b01a540d54540c0c82d02800307050b448407403080385014085094690b815013046100b10640e558440d609916502c807071f50812480f000078a030b041c55240304110b40007c100b01c41c2d008180344801c2840144d540e90405c0050800001130f244c1020b000c112080b20208403603a4800c1c0c0b0304000ca41c104c840000c1401003000000e525 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 785494154 1250 785492904 785492923
    0x11120d021b010e0909070303021203190c1202030414010b0d0803130c08100b040c0f0503161b0c18200304050a0c0b1b0d0c0b063f0c060a050705 63
    0x2010f4130100300c240040014030030140ea00036002c641003107000789a00042840700301e41781da003c0c3e2400c189003030300000c00780c00c029413490361400e0040170342c42d0080180c000c03600101d0382940d038010340303201c0d000542d0000c3c42384080c08041030703c1c840300c0a4a16252050300344006444501c81070034010200d000c1c0600440d0321030140120f081600c0e44850f240030320b00003600e44240910312551510600c5040d43c2c1c010540240718050301d8503801d0450b07a40c14400c241140b44110500240185071811016540304038642c00e100b24400d10646071013500b401500d20300748450780740303c0a50914006242c4e80052108600d0003103041c22401e05640c81d0341e1803610034101407010a0051185800400102d828502c00001e820340402040001d032200f050003401c1c03035a1319035074054180031441d00b22400001c0760614a41c50350180026020300e00c00c09245d00c1d044a02d2840d08100d403000001681c04030742c1940140c40c2c80c00700c00000c0380180700c40305119002881c0340c821880c07158140b180000d4088208003044c0710030b180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 785495404 1250 785494154 785494159
    0x30a0f090803071107030309031b05060a03060306150b1b0a0b07080403120510050d0302030f07080406201207110307060918200715050411120d021b010e 67
    0xd050461030a201e50750001d03035071500801c80301c1e00480b0168000050000417130703415540309042140b031905c0c1c00366a032130b03205104030303449071032890120395520745900919201142d035600040035840e5090070400c58001408029268000c403070100010300d0b02c83e0580e03081c0d03202c1100880c03051203441c0c0700b2803a00350b841c9802010081b8202c01c0004e41a00503072124452402511070396a05010f007102c0d0b000f00c1e00111240c5000c208103a80c144124100b0081c001135151085c0100d038640306141d610f0b01d400390448001102d0203000054103001450f0701c40300b40d00d070307007080b4002c000d124080c00039007280c540074079140110708428007090303600910041704155840000050291615152200c40051040e81a0300030590900800244280d214040703101c0c0b07503d200c42c82c0b1503086003e03c1001008201d94091602a2004543c0302d808035100042d40c40b9450007148910078400d003001140080c084486440103c0c00d2090300580313203407440d07107401095184104000b000740302c3c0c98400407070040e0382065480700c0c803a8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 785496654 1250 785495404 785495411
    0x9040c1209060614031504031d060408030c0d1103090919020d050f10300b090a1208090c13020c010c0201020c010608010c140d020f03090a020103050a20030a0f 70
    0x2082c4070695018609503031406060007100d4030b62009040e0740d01a00c1c0d101d00300000032200001d012034468842041c1d801c5d4402c0c1d50554032800400080d6041c0c0150308990895000007c1040302e4a0381001405222969400d180358000318041c409903c074081c000095000780849000604a200c90520346103502c264060210344550a1003501c90042c982140c5ca050070780c41660228940fa180400c000c1c0844003032900c00e100904903030100040c0c0d44d059801c1c44401e455024004000525481c8449200b0300041c0018400103000d03043c100c5038004500710b40c030188405441403100c02040860450100701064400c0e0703035088401c80c3c10000901c181070000406503c4c10b00c4401a86034190010000b00040304000d10034140c03220040c2c2c1c05c80c1d132260760403804a070700104890a4251800c01409c168403800c50014180507000c201c8010651044980442d0303600310421610031580c00d4070400380c02000140d0104000c0b983c0f87c440034481900603c030785e103040102000080c2c83c0000798025400798400c1c80c2051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 785497904 1250 785496654 785496671
    0xb030c130b061e0c070e19020702040b060a08090610030308060423090307020f1519050c1e061006080a090203210301030b0f0c120a090c0b04060306061409040c12 71
    0x221043c0c1081c1610748035400f50580015200c81d103081403a00811038141010000d487c00c1f403440d0001d500440d03040341c01035101c210b154425903032807018100c1c081c016200c481d094038050317442d2800c02100801e1944116441d400034004a43c0c000252684250240c81c0014002c3c007018914101e1001042d80d5030f904108a810004614404809410312610940356540c450703200500300410b0112114460118420030311029000c0c059410400000780010301300240b41510340f21803a4241040d0350b0564034403502d001138003840c1c1881002a16880880d00e1665141c0da82000f5000f40b0360354000c0d0084185540b54603001c815550140039480703ca502c821030f46000e0702942d64807000c56410911040d2250441d440c00286810701d00803500e84550710100d0300a2902c0d0750035a07510789901000c0c1000309450783c2c81d1440300c000b5800140b0313030303001d04450007249484505d011b50090548070150000400c00c403283d0092000c102291064508480c07084601040300000082c003100c044201c5e04105205a0800035603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 785499154 1250 785497904 785497957
    0x306020d0c1e05092701271e09020d05010203040b010302010e010512061026040c2102190302030f0f0d0215040f050f0706090f050103050105011209230609010b030c130b06 75
    0x100e12040e90311400000c1e11750b0b00311090404032210340611400c400301040d051484412a54482114542b00404400c02942a500c55500b241c00031501240c1e0103045800504c255a0011126001d0700c01c2443c20303902e80390070b440c042c0c1500d14016145c54011035440500d451410b00a214ad039403801c004444000b0400c84800c0c0003400c4c03141c03d48007500c0c01c034101ca10204001c4100026041c0c0c1420500d06800c030ba140b42d034240401da03041b1006c9400424074001e008070050ba800d0140e6007030052084014120400c40b100382a0608a500e2aa0419580021006020b101c03928031001e80c42500b00c40c4640c203103080b8bc00c14a08121030350301038807100e000f0341c04081615a04050740340255400001e000400716100c0c801902281e42c207020711400b00b0000c03030910301e58082582100c0740581c485e810550444035103c0c908a0340f03d5401c00192300036040202002400102441118070358003084000785280c002a0020442ea14450f0746444007007078a4020702e1140c0d843c1c420807a50092401500c04084403840700306c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 785500404 1250 785499154 785499179
    0xc13050f010803040e0f0a1d15090601061d06070b070c06050a050f190e0303010605040504140720070807060807021009030e0f0a0306020d0c1e05092701 67
    0x445200140c54103001246008000080d6000d03612200d502400c55101c400312902c00b4480200038030f9082c1e4030303a9442449860031800383d00000c3d100400400d15424000c08603144074400425200640d80005d00401141d64080065400c200010300750307050400b9180003084443c481c074000540f140007803006001600d43c0c480403441080340034003410030658641c220b5500542d04180d0784050304000c0d50011030751450204502441e0340180707510000706906541280340c15a0000d80c0103c0106402140410080c1014003d240d015214030409600c0d0740740c030100182c000040b0200110201810300318005034410b08200303500140400004545421360b841c10002c02c1418125051401401160f003038140c1c8140364010000300a0b0300d501c9146441e4859000c0c00120220703c2e0310182d010183d214000082400e40c4000c1004008e1200082401082240041c04109400703400b80302044242111202880e488003c0d244400d0703049840d4012150102c0780b6540f409140c0001101210058000140c0c4514a030f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 785501654 1250 785500404 785500411
    0xc08040e01170102030f070e01033306051c0e100e0c10020604020f1003110301090c020609160509040804051306050f030f1e031308010b040b06040302130e0c1305 71
    0x40009402c0d10148854509070f0009035012602c403030342c01c004120110300900743e004140e07406250010700040701c0d511040c011101000c85001410542e00341b020699a80003418002d40040c1c00d14510703202e1050700b204002c0c0c64600d01110b034140c0d40c2220f036540007410701c5240303428207072a2014480d844025501d2a00e5845910351030340300361100008618071a00101e5024405c0390006c14480420041078180321450014200000400d580d4040c45ca4030440f80d08051806408040303c00624a51105000b03403410340007900003501070b403061006041c866050b94010094500c16038498030715480b546420300301401a5000542c2c031122011005881d100c16606c070000300c03041182d40c0040c0650410030705442c0c242005403120380790001000c00120101030041034100903500c07800c50749861403050040181d000a50072400300d59449004c0c1480394505801901d03d545002c98a02e442d141c5190700059554200d540245101510341c1c3e44001c5d4a68140200f28142402070000b208020581e1250001400101d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 785502904 1250 785501654 785501669
    0x60a090f1505120a0e0d050301050a0e06130f060f0b120105041a010c050703051e0105060103020a09090b0d06050901020405010215060607021210060b040620100207030c08040e01 78
    0x49800051186107000812224800740d00c4661030030046400902c84030400030302c1003c0b00d50b110036002d401e910003084203007054070380b641c1ca954a0394100410030402003016440403100c0e02d071400600030141c0c1d450001500c14000c003a03000030007201c003442c140003030203140d40401c3e040c503001040020000d490f14001c140310205941c0204c2d4503a01c0305c0c104000c13103e40320149800446810b528803081c1d4026000740900354024000c4900450f0385e43d445614101c1c0702c0540424105c003500142c0455142402040e821690909056050000c03a40e0001c2044025124811075103840750000e401944130b00301d0f15038801d42c0100c1c0c24410313403a10600c128040d51041c402c160043c4240e525940020301114951802880001d02aa1904286d5020803041646458001d01c4602400805c1041c0c03102900c2400020440e0803141a112480d0903400f401e590b0103d225550038080400003200340c8403000c00c400c190114200c00041e201d0249040446140c400711800130554100080c0115000c0401c0c0c3c844d40c1242d020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 785504154 1250 785502904 785502929
    0xc050712060c0c050d03020c0a060f021209150601050d1b0302130501031a21030a0e090705120711030c030c0601151b080703030e06240103022115060a09 67
    0x1c40d40440d0f12a12080001d01150041c0c1c2c61000864131a400900e44101031070201c515802480e110801182c1e0580c040b401c034150b0000342c144000141c284025407224007003002c3c125020312042080c000443c002c1c0701d80c0c100310001440716040f2160354080d040015681c1c00040945141c81400b800940c40b4101d11080c1d204c0800f00082c541d0300c43c0c05071805451002009038012b8204030113005100c0c2d910000c4000c040c2016108480d0804100040c150301c8003940d480928a0a80b181413104490740a881c09007000010400013225030b4001d145240c1110030380c94540041c01c40a00b02504501400d0401e4a007400b00040c985154a40090200e040e40c60001250301241e07500b82082d80c0d800c030440c0c49180e130006121030181c00b182d420006480d17054064100403c43c41d1f00a030003d400c184040b580050400c00c0c400503134480c045042c95044480c0b00a08045261481203e0b042c0602c042c0301e40400e080e01c59500004c1c2c201c0302052081e188004020706081c0d203840c0d038400040c0c1406204e00074000300d00340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 785505404 1250 785504154 785504171
    0x1c020f07051b130b011e0507120305061806060304020f120a140f060103020312032809230c041a0303030103080d0b06040302010903020402070c0b16031b050d050a0c05071206 76
    0xb26204d0b000c0c2d100c40c140c5034040d01250000c0c811295201c4689080144030302401540080b41013200c0082e001c0e4182c1d90002150315004007044156180c0c40c0c4043c00c10140078080024588443c0c045030b801c035404440e03011882c0e42c003a0000340f8151b42c01d414203030705d07001e428611410850700c3c0081c045407001c40300684100030001079130b042d92079200340700180d0300d9442202840c0821000300001c40e044404141005244686103030141071154070031039416201c41d81c0d45044001e0250400380100c8030400c070f096040c00040f104030160754a95460812a04c515a00d80c43d207110b460703083c6000700310118080c094070340b00d40e502d04041c041908120008071285040002c80ca00c87d2520200300c40980360305842e40442c103815078091000a40140c03070220742c120040e450108543d55a180030f801000b50200c2c0480c5034011924000348903501103403154aa082c0107100090000b003011070100ca03039440e5890150b840c0c0d03480403000c5511141e5103402522078080d030300003c40e04405400b095007400e0700030b02040c400d0340c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 785506654 1250 785505404 785505439
    0x616050106121e0c1a0d0630170f070b0408130e0f07031a030a060203070e1801050f060d0c021b12101104080105100501141c020f07051b 60
    0x78003844020303c22404c00c1018071841c40e6203a12500030300303007010300d541c1081c1440d03e032501101d245801010104e08078000d0704040c2800719442e08080c44a070f840d1000c0c082c034603950301ca01c0d00ca90f014524034000e8002c60080d00810340841078410701a04101c00d040300b401c7c1410301034501d510151841d41c00f40c800d0403021501203849008103000f11090741440380c00c0d82d10108204d000700a21034409807042101e411144455400b00300c0f40082900031100140d907800c000f080941084000c1007039900404c07048841010b40c2100205250440d903056a40703407a20401e50000a100384980c41828402c14079004828002550000d0345080d8092040b811500040441d000c201c1c22840342e003030720704855001b100702100e40c400a820525401d203410580c5410305850b0500d65086d2001210100701124218a0030030103582d020001c400c1c0a07400c05401c038600009500900742506c050f0b000b03404055000125910500301d50302c01c4a1003540c00c142510b58010030b007a0003803c1c485e0070b83c030030510a1507060141c0d03103c85d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 785507904 1250 785506654 785506703
    0x20304080604081803100609180201021f0b1207050112020c0303041205040b070501020c160e0403050a05040e0109050a2a21050906010807090902060405061605010612 73
    0x100e45000061409549540d10280103911100102540081e448060925620b040140b115840d030500004511142010920b1080f905400b60034451000600800340160340c0120b05183c0c00180102d14610810f1910f410304060304044078201e17003205014000030000f4401203403403415a06c1c26615005026480c0070b00100303038082c0d0280703d540340d007007040414002415400306008520690910500705652880114010b80103c0c0e002e4846940000c1c0c0781c40242006d000c0080680164068040031500f000d90145000c8070092004007031007000141c403d001401403007900c00130070020f8280340c010340e11041100040e0100751103103604541840100681450b8052000b64108080c042003407aa4400903011205c4c05148400c42c005a03c05200507800400c140c090740348541c2d0110b00501c169490302e0f105501c1e0848a51252003250324185110300143c0c3c80360100c404580e0b00b01e038455207407008540d024450525100c0c000300150b00c2d180c40050350054081206640c540141484100b101020b841030101d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 785509154 1250 785507904 785507909
    0x1b0103020708030c090f0301181703010e04031d0613050306060f06190309050304030303150b0a0f050a210b01030e03070b0a0203180105070e04050a0b011d0d020d0c15020304 76
    0x102d2500307200240500c484c050250003501e0340103003211301d507400d1100400d0848401404a0a4060040032000240150040c681c1d030182da4a40b0450700e5903142140c0f070301280c1c070080c2c402000c110718203115100420407462310702400d00000709420303030f105078540381084104c072603118084c000e001d00000500c2074a00710f64450480000078000364a018168550806120300700c40482013450341d125156004240d040010304061803003900c0c001000c104040b03c2450400140c0d1141c82194020080030408981c00f0000d103180c19400e0604c43c0d21608080010b5a010b2518200c00c030486004606500c0400440d411200070b8807020389082204080350303003c3c40c1d01d03841503100c040d08035040b10300400d080c0e550550045038004180302d000441008850030460039524155402400180d403032407039101e28506407040c00c4e001503902d00d080100c152281c00280445108400100c000341070340542d001303d5198900e14100c41d0740e000780750303280ba4559458107000e113258500403540310452000d0401105400002250306 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 785510404 1250 785509154 785509163
    0xa0828080c10110c0a03050a21020d06080a0c03300324060503160e0303070b0a0f0902100c0204061e030c060309020d140106030b280b06090409061b021b01030207 71
    0x46245caa1810344803035001c000705104024000420071020700b024802d002d10f00003006000b5a079503050150b03182c20340e00300360031031209500000c4001d0001750952030305404480d80301800301061000d0a80d0b40b504956014030001070410034160121700154107034002001c1c5507100c0040540810707000c5107158098a64000c40c0003240d0100085070200040c4001c40c25450b83c286040c40c00200701c04007103421034010380700455003800daa105003c4500078600031990495443c0c082040440743e2600002c402d03000c540c0d005418020381074070341025905c1c0c03500300e040903282083c01210504c9a41400a05480355440151041030305604041040e80c030038001c2d04007042c0c0041c200c4040d1911616400b800c2e0301e141115488642d03803170070000002181242c00a01c6891841429440c130207c5c00c0d501031010b1410144058607e2803c010b41c940e9a454074180c1e2035108040e1000038034501c0c240f40003002401041d000052110044002001d102e41c00540b014100c480c4401c05032495180000540c103030302072403c0003030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 785511654 1250 785510404 785510413
    0x20d240510030e0a0206070b010305101a04090203330f070f11100507090302011214071209061404032a06020c161806050a0828080c10110c 61
    0x101c0c8580300740c2080c0383c2280d000301510ba04090503800203030181d000d5042140c0305940803004000380728052001c9001c0d1841080300348050988405e0751b6800c56074103840316200d56910180c1d1000c0d92001c0044209403032841c00300c1d0401d84024035081160344c00301d12120400c1c00d6108005031008a001e2202800340301c291700c81d10803000c40100e05031609034494001d001c5034400c20200e55070101490040794010a40b40d200d0075042030071070000601101c42820a0b080c054181003101c0c40041041041940c41662441c0c041c0a0f4907503404088040e0038a11006809031781420000715a940c1668180c1d80141e20036120000091341400a218207001c510440b480d0755a0170040c8800414880d800602030320301c003001074445c07170b2015154041c6420380907005001c202c0303031050340ca0003a11124460000a80010ac0f10841200e1825000e01c0d1384468207078141c03051703501c0340001c9007a8141c45505441f0f0f90750710518a541343e40c00c02011650b00c00c140c1342c41c80641c0342441d60304000043c8034811110584003000140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 785512904 1250 785511654 785511679
    0x60c02030c151e0d0506031c14070209011508090d02150c0c0d02010c09080a11040e0703120305040308072109032001020405040e16150c06020d2405 65
    0x10504090250300720b000100304018060a04101000c80d5007070201c405038540c40c40a52980440d800141100d00961000141c0031300c0040600014814030502c0ca81551014041d8026110341d004140d80250071042c114004a2006000310380c0300d4000343c5c20b07960054995950000b490ba46c1d140c6203c00d90168102c071841d590103a041c07c0c5007552100030340704c00a00c1d10200405203441d080c04445003c00507507494014009103940800311600030301495005005100e115124807270b0404d42c0000f500d108607600d01c401c0c1e00f403900500419000350780103003030414440300012000e4080d203800c94003100000c25050008030094001c401c3c811060500c8007000e60456145041000100703419002501031041034400c0c0c0c44081e20f414441d0340041414000982c49030310708814171050324500103104a85410440740c402d694100880150121201c1700c4205808210300c000c10796034207119a07400341c207203400000c06183da420241c2203d0103007100008403080341c111085108410300d49034000c1c15407044003006103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 785514154 1250 785512904 785512909
    0x2090a0b0a020316030f02060901060f260304030f060f020a0512060d1b09110322260304150902150d06120f2f01050c150c0310060c02030c 61
    0x40c0980c1c0c01c003401101e2074140510501040b600a0410031400994800210300100d54140310f61030b000310411000340078807410005850302c2c150241c01071070001c104813000040e4100c00011104c12010424040ea40d482d501c0741440d488805418400352403c80c107180202c00d021030180b00302c2d120305400b0340d10075042c285a01090000ca4a01600c3c19512910415280010808244800700403400196509588900c6d140040c000e84680840d820f031416018010085c0303540c2801c48801d04103201e03011441c17860b9242c1c0b42a4940000318842021400e452003024410402d40a004502072401024811207185000705008262800c2c00002900800b400f66002020344091000c1c01d6030704c0b186480401c000b0380328116040503180240c07040d220351255841d080c00f0b1015481d8840c024241100b21070342c9032080b0340300f02080030981524507070421000050803000c2c080180046910b001192005180508054160300b8094009650391158003081200020b5842d001d101401115a4040c01070280440c0c0d2104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 785515404 1250 785514154 785514157
    0x81014040b010e0a06030c1103031506030612030408011508160501110703050a060c030c141c0212090a12051c0b01050408030c06092e0f110a030e0c0402090a0b 70
    0x264a418414440a480001da80f8000214003411450346e001031801ea503424010318159040c901e64140e42c00420501000805101c0710044524043e10704036541d44a50000c5041400301c0c540e1030009010100c4c0115051006401404164503003909080e041e541311000c003601e0302822a0b08000d00d0a4105c4c0400c02175005c0c0b5a5540c11045180079100c40e40e65a407203440c1402c11090b41210210f650300e1180d207071203030107114040c5002100c1c60541c0f110004074480d0301c6540b1419814880c4c0320000b20740418000c4054040b03440d900c1d4a4400c1000905049a940d9541d04a03214100c4503046519a424091449501618989110321100100380490000348034002c0c0f5080c92104d0401808120200c2d4401d000c0004041c0321481e10010190b920f040715025040080800108420071b0913584455000f05802d611748030000900a000103505110307060f2840103004000420285020105e5000c0b0f840d0340681c030045104040d402075600810f4500d0401040307100c3e080441c3c0c1e10100114050183c0c881010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 785516654 1250 785515404 785515421
    0x90711060a0e160605370c0c120b070201110c070302150c01051003050705010206160305130209070201090b01150c03080406061e2d090b18040b060108101404 69
    0x8241c641c9500481820b10f603500d0140c2080011032000100d0317035000d00d408000e10400d400702800741c1c1207031010108009200c46682e0403801c200b02c00b1020300c1003030041040c2e1031001002e04032a103511003005c030716102c1840481110f941d80503510f4118459640b504400445110802c10b00190a4403400c41d400c0191442c4101140400820140100544a5000d200740350080003810f80791141d85c3d1862414511303007101504003504541100060200b00700710020512542c0889013004241170743c0f00421096030548040c07019500840030028000041d4040d80260780c80c5004100a070701c03070f070380740d4211401070f0741080a0180000c0c8014170b15000b0078030508526030054401e000c007160085d900c40e102040e50035030f00c2142000e800246005c109140201c5041d400f0102c2c3c41006400000c440107134804442e1a074468031500988a0141c50300d036550740c0340c10301500b4882c00208030050406042100d1007076811200c1502041075100802c000d181e1300013046049407107140e200f19120401c0003c0c44098444013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 785517904 1250 785516654 785516681
    0x7120204080f03031b090d0204230a05181b1014030c13080120160203060a0b030d0c0b0106180801091103190807080c1509070302090711060a 62
    0x80c000428407100c107105000309000020300940e2a070400c0c4015440c3d02c07411616124039031908010003541a25a6111070b01c000d901203500140d00c030312080c00c492144682c422400d0651108408020484401d98495030040140443d50171900c100e00a07410351302c000741540c03401d06040c2c2c0d18907102c0500e0040500760004049142071840b240340e01007030442c03640003500c0049040b0b20111f944004044440104001054044003d2040f9200d246600c480c2022005034181c4601e000100d162000f0f07042568440720342e501030100c41642c41c00f04c012a00620384440064464080c0c80c1ca81c440362780c40b400102201d5034210912260592901100380d81482c1180c0b01c0c40d113072020701c0000184503a800e20596036014010b480c40044003110380201420140c000301301c01c0300070000341003110200e580582520f05580d80f0a08141c0d95603003031a03c051516094402118a0402c1d0b03030100520700300081743e1401100d1082d100c08950703440c1c0c003c06403a6003374070100c043c1a0364050703030010700a4401a0044006400c11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 785519154 1250 785517904 785517907
    0xa03170a03061a03060102160e1305010e030711130b01080a0b030a1403070323040e09030412120807020109030c0f1511130906050d2603150f0406050108071202 70
    0x443c094141c2d20201e008822141c942e0100c100482c550701804225040000c00d00f0f518201402c1030345000314280050624083d00102c90b94110410100350300c08070f0302c080d540302200c0e06d80d04549030100c40a940d03090100d01803c2c000d001291801004e0003840c40d400d02c16141d07000907545000740507005005000805034584101030b89100030a55160008025403100c1000c0c0d540c69905007030103400492800d08103803005030802d10f81c0a0174600d244c140c07016140c40146000690702c0f120343e55451801941c2005c8101035181d0080c0003000380e4024102c16001c05520780644590341d20500341d080700c646003009800b04000980303110015420500c0000f14a1158194010400d20b03100102d08942402090b21450003000401017410050200150010500104180308440c2000c000c03d4881c000d01c030004040355682409442c00a520f50480720308101101d06080d164541b41c030100d400c40c0446150700b8000d500306900301145060501440c400e803441a1282000ea4851910840310000901e40c02c9651030f03030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 785520404 1250 785519154 785519159
    0x1521030f0313210f08090706030903030e16030b0f0105090f07050d050a02030105010e03032701050705030d14062d01170a1d0604120305040204020c1c08060a03170a0306 74
    0x660054020003030f0310140601c810030381031000c05841154100307200701c28030910308204400140c002a040c03040d038000e4071f80132aa8400318030742a409030a0b0410404035134007410b01c0300d2600201c100341d44011240903654003100c544a040708004102c500713014058200b0140700002e8071a0340420103a541100051030030340e2800b0344401b150011100140c8030240540d4001004001c60b45c4e0045042c0303c0d25208502640c90455280c00c81d103400b0f020004692207580e0301d182148556805041a1280c1a13040b00c00d890780c4181d0b00c2443c0700181040c00718040682e0b043c4000c5031050504801350140444008440c0407141e502c40c29080c9040c40c0441aa41003044070080302120218000703070640102c8c460308011402e219010b080f00440b003c10000c41c2040e51003d81048049000400b5400c203420a90800103519140c0b400030030044e00c02c6807204240b40c440c7c62503544210228019016020450707544030301160702e401080001880342403202400f030102e0741c0840320040c82054000d02c249491801d00003035856 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 785521654 1250 785520404 785520413
    0xf090b0a050c0a0c0503070f060816170c040e10230604231201050c12100506030103110a0f0b070813030609210302030103230a05061521030f0313 64
    0x3e01e003000071901008021030410140c1130800099026003200c03045840100d040c001e004040440003003c510582c0c14a0040c07480b91400349410605030b04008041c580c0c107140c419072904081d4003d1181c810b260300c0c1080000c20085802c0400020307240390202c14000c3c050703440d808604016258100a0740007104000004000c0951240001403d1170020388030b03440c0080034100710b0b83c041c240d1140d05c0740364107281c06c01183c1e20054084400543e80f80300d0f20308407070f11862810070400d040c2e900100d801c44070010010051000300c00000103211004c54290b1480794880b200e94204411034403d04810b480d0622004000403245809001850704d2021303890f40c015602e440302030903514111000c1d50280350030402030030342e0b00404c00420302c810303107604095145504d10741d40d0300100d1403802102070001c0030303403181e10340081d80c140081030519412004030740e4141000c0004500403052414241d1050070710540c08003c10010745044c0604030708800140d4145000301011002a500080045900200440f01540080c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 785522904 1250 785521654 785521663
    0x904051f11040312030e011a03011401050a0315021204080d0c0f090b0c1603030305012c0103171621170f04021f080103060f0905250f030807030206070f090b0a050c 72
    0x103003035003110092012448c11301d821201c9124008041c109800010311040d1609100c110440794040c1c3c81202441c480000c000090141c02d02c1d1080c02c030080814001480800005003078440d01c0020100a403601c03aa01c2640d2080d50701d942c02c00843c00c033050400c0158410805808000307040010b4a09005101014043c0f05c1860303081100440e81d5840107114501603004040d55021032156200d02c0204801000045044144801040660b0390004102c072412040c1c20384049a101c240801403a050303d103403c4862703150328024518100400011010802d10070b003c030100813030301800b915580f62620a01012040e80050080c0c1c3c1205c00c0028819400041e15004a51f51400780e0310b684180d41580b40c200d040d00c6002c040004142c0c100314400000c22008998032505050304c080061102c000c50442c11116070560b444165007040c080000030600c5510390007090700621030303801d84115a96400c01078803a07130150707440040000d070155814041d010080c8014901804e8509015080c00c0d0340d441680e240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 785524154 1250 785522904 785522921
    0x115080f0a020a181517070e040b0109031401050414030a0c11030a0c08160609060509010f1b26040f060509060f04080d0e01080118020d0b0904051f11040312030e01 72
    0x303401d088132841c02c1260302c0401c80c5124082e100b0300031507d04114200501c4401c90751034541c402c82d659211145c0c00d82c02900d080c0d000f10344c010041c05100403110354190003020203c409030358030303c840740402101030004422a842840c894545143c061a00d445941c241c4105412031034041c45100ba84001080d0f245009100801e103101c01041e905042e900d0213690300c2d038243c1c004020711040903811b00c2803680240c02e50740000f0080c070b8028003c001c0440112088420410098981d0040d40840c6080c48400548030314950018441840e00c81841e030500302c4548503610404003d0303826111b084c13118078410f80040c01c7e100001008039042c06580c18600140307038443e90000320103078400044801400c1d00640d224041407400d0900201642c07403d5949040d5400c5800940c4105600140301c9a481c1c06c03da2040b2007810f0003270110811483d041c0f40540d070303400c0c0b0346a80000301d10503a44600001d00c8603000b04050882868241c0d03081914580e5000100c514551a1009254954032803a41600c0240b0400f0780 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 785525404 1250 785524154 785524169
    0xb090a021c0c0b090603010b09220e1b060a140903011508150403090b09030703080f1312030203040338100819020d08040f0e0115080f0a020a18 63
    0x41c618a52404019009842c1d10a02c40b915081c0004e54540d80d42c0020340741112020231a0030380d80c00c51a03000500a0b00b410f64440d265540c1106054910403955000e650400452011564405644e84800881d1101c40180f9a408241081403c008a110b0b070071550504240070b10840c00c00245000103030940345040e81030022903c60203c01c11501c0004c000030640c40000480005450800361401403001583d4000c200404000280918481d207007041510011030b00a00c071b01e0380b200060044941c1d59401050502600c0c2300b4008041000a1001c282250007503250300107500e45491035942381d03841c1003600d2041c034885a014034803a240340031060410b0641e46041d4512032a0b49000c80002e440c581040e000705029500c49410420f407844240701e80039455404403801d0042d00110303d411100d5210740e400c02e50100314030400006c3da01c00048a054181d85000100060502511004560135203080760007450300310351100031954a02d0b09a000704010b80107450860a4810007108000042d201540400c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 785526654 1250 785525404 785525449
    0xf020d140a0605010e0402030709050601020c040603230f0c010c1118040b18070b0306150d23060d060914030708120105010f020304150923010f0806010c0b090a02 71
    0x10440b0502c0307070301e0142c40b500c520b540c2941042e4010a61b580b00c10701034811056655008100141c1c020000c50308d070040001c005201964a038030304101800101d81d1012100400502c1695612001180460012040f440248005040100111040352840740706456082d00d141c1c60210720f03118500300c1c3c002c41074543c10125060801d89000780d80c4820050140940d028100c081c02015100400c070b8500321000790030100d4580d00d031071001520021220405070502c1c0030021b00c8541e20b588503086040003643d04103005e01002d06000317100411890484111f40c0c000002c510010014031194001a04140581c01e950198500d41c2061851680455400d031402c540c0800c006001c4840c110034513024001c03c0ca000c201660001ca0080d50301e0299006801c110004401c540000ba4426103889000701084064450000d1404150000011508802a000506400d628002c4600500080723000d1541a500d500d50715200d0b1b03c0d4600e5114000e002280140501ca01483c0541d4601c6691448200141840b2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 785527904 1250 785526654 785526673
    0x240d05010506100518150d02131a071212110412020f040b03060118090c060804030f0e0604061d030d0905030f120a03180f1511160f020d14 61
    0xc00450070180d10401000820000003800d40c4083c040e03c1c000070303030a07100d1078031b182001104100640101d42015481510200b004421900a00740c040102c402c2603608000e041c90440c20640c0d24404d0f00380c01340400204481c00b000c1a4030481d2207040071060041d00150300780403000d10b894a41e00946c01002c0300300b08803e504003946400e103000c500781d1350121030030820208107001080e04c43d54144508001d401000580d05a4071402e60401602c05900516040045407102800381040a080c1c41c240c0c001140c0c0c1007801d8145015400c0180d0480300180140d051502c2d00d01c086031042c02c0e00848040907018081280801d4074104802000403a007038590404550400c0189450702403001403045065024041010000c82040c1c00c45031040700034030300402c0709807042005140c0d020903660024041c0500600c0e00007840003c070b01c0c8204105802c8001c0c4004254012140d059000c1c0d00d01c1c501c2e1005921002c000042d080307402c0c02000390320241c00350700b080040fa15640480b01c1d0301c204401030380d044441079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 785529154 1250 785527904 785527909
    0x20a02041b1d0d02041808070c06082a09060c01020f0928090504020d0803090a0c09060509181e030a03050a0216020f032d0c0306070206240d05010506 66
    0x1081c029000390038002d8007021000d800a00507020703a200c0680150764540c6241e0142038280c13000e0703102d15003050320155107030401d00c1c207a1055140b6101e40c0002411000c00f264422850002c81d61108040c030a441141602c602c01c491055400600443e5001104000c444041b81003070016040103004101020b4070b840c1c815043c000c0760346901082c0702c030700340400c9100d1010b10483d88083c401e496101c3c1000038995030380e1000c00d84040c41183c001d403501c08088100000800001501c2d111140b2070304000855a170b0310501d6806542550098a0380240c40c080001c00c040c00141070030720004202c80844440d01d06002000c40e1401001c1c4018115400009200c091550140141d075081907085204610700035001d0036504644901c500004d102d1000c212404200366400c0200d00091a42440b80300c4200310400301e001e00b082101d252088141c001c00107420002e02d40403844074032441081e0082d0100f03076160b50301b031009180140504d514440b81c40307500d51240d448407821708100c00c3c45407000260a0610004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 785530404 1250 785529154 785529167
    0x18130c200114010b130b070b0624040308090a0e07050309251202040e100b03060129160506010e0a0f0b060a0c08091201060e0c07080316020a02041b 65
    0x20381141aa0600d81154603a8001e041000c0c115051901d04a03110102c0d0303805603540c1c025603071000c401018003050381024021540c0240d80a03100480d40c0028412818640e4514000610503d50384118140000c0011030180c000600d1817000041040c1d501d151102152030a500307065a07804001030010007081411041082802008105800d100111500345c049034118441c0302e000d1440440700c90520b039411501c1d10740100c8040c81c10201900d2000716005640001401e03004c00e0a44244203200001501c1e04102402540315000c0b40c402000c01c080c03444c1000c0085d8000080070304507061480205008c04e805101050107029030519928180c00d02e140108103454000b00b8092202c0c0c03406e4140400b0340e491904403242c038451810007040c103040c00d04060b1128042c804280783c00c402c103952145800e16044d803010041d01c0d100350b0f8100e090b40300c0a03007280142c0034400c80141441c608002081d1490400c400b591110603d91040300c100031100e030301003019600307203510a6440707030462540070400c40c0c1c0155 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 785531654 1250 785530404 785530457
    0xf1804050f07081b0103091401050702010f0b090708040f06111b0c030a060f020903030309030a090b0a0e06130503010c0c050c0f0603190615020d14030c18130c 70
    0xb8070505003089409a110580700c994001c000d600c0180b0031056034001d821007803185400164210717003c148181c84501030301c0c0450f0803c0055280404401040105201d05c0041d404050031450300c540da01001a52a0702c0080c01c113071140030358903407580006011801003000803540310303c8940d00e994550541c0100d00c0d40d812820841c40d006118240c0301c80c4c1b000220f0390f0b545c64100300040390342591301850384001e100d940700760b1780c145c0000002c00901d03074800002030030070480c29601c07000e016a0700c02d034020107805010410400214a003a01305450319018000e85200d8202c10001104150b0701c40003e82100d003403800e0384000c80c1c80703003000000b444001c0c0410220540c00b0344031203051818110026285d44030040041038000e84a01c030f4840001202e0f80810301401d443c0c2004114982c03020806507545c268500c4010020780032480d880844906c9005aa004201c501003090904c08218004e400c00d50080d00d0041d04a0b00e501c0c1d4100228006004140c10269a51180c0c0003041818000014004200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 785532904 1250 785531654 785531683
    0x50a030f150905030904150915170606030706030f3b0c030a03080916060503010e06030a1524090605040f05160c030203040b04031202101b0e0f180405 66
    0x4a2440403400c0801181c00b150301c01c550000380c01a04180d04a4440c7c440d401c0384060fa89007403c1d8503c4d200071030711001c0950b8000c12049170240d800718005552070034102c034400d8050300503110821010303000f90040c00c0710340315005011680004100c49001d0500030b0249111600040e0400700d04240b8036070068103a0f2002800107002c0714048a0042503a9060800b4000c00b0003060100041400000b40306407000c036002d4588004a0750341d00c410003801074001303004666a400c00c40c80803c0142ca800101c00e01e8082e8403d007480e0f1107400c680500e600070440c010001e108950402e90045040004565407005445c0c0407400044076401c1c4402d110440e007103c3c5082062a2070a4140840320461680d50412001d4030301e800b209103800340c0b500301d00754010ba50240440fa10089004420882070030f2080365a6280c42d0f01321140d0034202c182c100c003170380d17250380744d210500200780f6290103400d01c60100700d0b180040150007401c810f0710b820086113180c2607003244004011040414001080018012000c460105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 785534154 1250 785532904 785532911
    0x7031d0703121d030f010b0a0e010f060f030b120d03141003080a0504080307081b160e1812070201080c1e090d021c03020c0a0f0b0f04050a030f15 64
    0xc42e600d50020b100303031100381c2d01800200701c485411907030203180380c200081d8050240d1382c81099108003a8068811450f085114203d4500046914003d001465040341d841c4200000f4540c9008400d03103a03007080240c640d0415440d640740395000d8075401c0014987c07804800c01030551403042100103003156480010200900381070310a01a080b41143d0244041d41d4000162071381d111400b40781a61507108944c00810140008a222010311002001900340d2001c0804c00428800b81502d40701c0d128401d14a034101c481000c0074040c072440740b4a110103640901300c00001055640b002c1c1c881403600e070100d0170308030900d100060040215644800819000685020261f082c091854440c3c542c1000b04081d44c0c0d0580c101040010840e0b486c28241440b09402030903e5100844201501d158960000003c1c0c2c050300c190307102c1034801d0a04e41419002c568180d20424062401c0c016100c000341e0100074110303a110b03000d1101040903600d10801100551003228210114416460003c21800c0f0b40512056810715 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 785535404 1250 785534154 785534159
    0x30e090703110906091c14070b07021e12030c0303040c08010b10211b02011a0102100905161d09010227040603140d0201110325050408010507031d07 65
    0x811040d42c10041c002c1341c180d0f0300c8001c50340105004860400b0000d90300b5143d461903005100e107031001180d14051110a5510040d03d451044d2420f101d803210094000032090b282c03031a022046100c0c0180c214004180700d040d44024411946550030600000401e07801c00800d000400c212a000640201204c2c402400070744200d80000d0200018075510364240045c200c40c0031441444205404c22000e03508004200740041e0424403040c0c2803d100c4950301540ca001c20f20000141100f0342c120003000140d00901c0450120f40c0c0101c00307004216000c981c90b100f40d040d188242012410a6006452080211020943d0321b01c400546502d0240c100c1d00264410403040d000c8160700c1d50015101c8144100c1d50320650014070100c2e00030100380d4005000502030101c041181400030494012015440d802440b100d07140403a0314019200940d92422500d0080e03103418043d000d072140d6115402503a050260400f5644c45106003034410445800e400a0341d01c0c0010b442c031102c0b0400d2481c2081d03404004046460 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 785536654 1250 785535404 785535431
    0x623030604080a141e07020907020a0c0b0c0f15041b0f090b031c020705040b0a121e06050403020a02091e01170708070f140d11010e060405040504030e090703 69
    0x416510f00e142000003009007140d000d0314030000c82c1c2d4401c02c00c0d1064080c2035a000e041079403580040004030300c18480000031409070381c4002000c405542d04103000003d064549110001994401030080f030131070140e5015103c22040034854048001144800803141f8545031602d06800d1016040107840a00004814403600e4400800f0000352060b0b09000079030621400000380c40c2c0340d00801511207460b6403262600031709a001c183c810444a040d14284100c00804040040d00442401500401d40c11150400301068000715501c5a120300c406003a540d0708240d23100d610554600300c4043d80582d006050071021818020201c1e03a00c000684101680704e1000300800d1034902040c401c210300b40e8420443c00e4042c074000c2c42450000c0c5031001c1100c0406aa90050719261856072145150501d00042d500e1500d090540030803075804d500004a80710000c008006441109091340450b0300484244004a025200e901c00d150141d03029445101d11820080200070703141e0310050410f4205810003070180c4420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 785537904 1250 785536654 785536657
    0x14010f06080a200a030c0306051e090411130b03100c021902190e09070503210304030e0a1205010f06060903020112020f19090f030c030303020304060f062303060408 72
    0x409070840c0450700c9003003406a400d41d9070780b56828001c40da5000424044c41e0307030164420150301980e80c9044c85600c0c0c1d150100280016285210040029141000243c0b450182c0d0415885441605150a02c9c203050303021601503403544c248d11005540c1e4582c071204a107400c004c00209000e032428244990486410002d48403c0403107806081c00c204180c1c0d00086584007444009484541e09000010543c0c80701c0641c1440b900b0788044403d401508070101b010300f400b081301c02510300075450703102096a12155040c1d4640c4001d100b50100310a0381300c480940d90701c50240400038015078200f100b079800d043c00c086086820518550004616108003000540e401c90740303000c103c0c0c1d02400c11144031048642c6890181c0701c1c0e00e80f429044440003490005001849180e0b0940b013109030b94000c038035030b00d43c00d4411091031180005006480e013107400b040080d11a400859202d0310800005c43d2410094068105a4500d6000a00e03032902401140f00703610301c1e5100b1603c070035804600828150410762200c83c8203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 785539154 1250 785537904 785537911
    0xf1b05060405060705010f020c010f14011d1302100e040c08040b0c0703110601060906020d090311060304110d05061b042108070b0f04020109080105061320030a14010f0608 75
    0x382c0d0002c01c4000c140b1400f9401403504a01f9044190343e01d43d100b0803107500030241d05d000d402c900c0349480c0c0403400c280750b0b03610340f58180c500d241e0105400c102868082200a1002024841c500003100a21001a29000c0350f059102500fa1607503280610030a0822040d03d03252818401042200800c1101103542c0700c0c20a60080b100d0596503941d0166800c04035483d800301c02040f03005108080000494030f81c002a000b0407200142d0988015035214402121000100c1c40003400d4020001900505841d00300c000310f410034410121683c0204921000c41d004c071007001010340e030301d401100412520742c0e0559101a40700220455240c5082d00303004110216030001d0002102000d031010400302045504822522030383d070400c185407828a030510306a0041c0d07008603012400141d25a2000824104c1401440c5c018000104480b0742031200d80d9040c070080c507050101c240d0062610600b0703102c51011500071802055802d001103114944201810307403040060740012080b400700c84040104d20ba001844170703003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 785540404 1250 785539154 785539159
    0x9060503030712030c030b0d05060105030c03030304120f2c01080a140a1a0a14030d0507030e12210301080712152406020a0b06010e0109030303020705010609090f1b05060405 76
    0x4000080205c100c000b49052050075401000c412201021300c07000140b6a8103d940440071903003040000014103441f1301080d54000c09038000a209a00240d0081d140d5420440c000d180c60031203040d9100079445000c1406e0101030714041d201c01250070304d580c40424079a004500d09824095000700c80f501c4e10301c482d0000c2000244541d96200342c070782080c1c0c02c6603400c00b00000410001c5426214070540c200c03030030003542c3d01c0c0c4244280d60840c0955401401550300d82601034480e140c550301c1c05028132600c10420359880700d01b8004c1a0640038107902e0800740303541c2c00c40300000303484e04c0f5070400c80c041b40380143c941c001c11025818100007a001072600003988070366a04450020072000303048030b034001407045558220381d1112042100070408c1030f030005100c4840340c014052420310743c03580401074516040040d42e90b400101d1213602400480d00980040c08114801c038000125969125220800c495000b80100e5481c44130a812109000e101c0000704040c0141648901c0c4192411300011214469842a40d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 785541654 1250 785540404 785540411
    0xc0602030a140d0f020c03040e0a05100e060429210316050c222301090b120d1110020a0206041e240f050108030d200409060906050303071203 62
    0x540c50807a5044140c0c0507036209800d6444803103101d125511f9030894000e5031a450354010018172000c030135006540c055400807038810304241c100495244810002400142c101d61603407209002d0400302c94045c080f41c0bc45d203992134000b1292a04200c0060f003040201101c00c14100c50a80d0420004002c550401c1c2c01410b100d00e40f40c0036468503508210000d11400d5012245000040c1d0b200c0c0f05003411b40001644d1b80c130410a40590241817041a807440130201c1c1c51720880c1005100c0303c1103e40c005031058500a20400503401d800020600d0072080340100c80002d10b03220810041000c00b000009090320920700700354102240c01800070359035200104003405940350302d040c04451042c29652842d0491700b180300d4402904856440100d04090104603408051070441c503a01c2441d06489001d040e182c1040140d440c00100d46801d902400340342140c41030140000010064090700c444c0100010141f0500c0420329900d000c42d89005c0303407820341c440d81c001d8004000c0c21002460b10200076940c00003030f04002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 785542904 1250 785541654 785541667
    0x7240e120607031a041a010302030c0c0a110306070f1409010309060c020f120a02190c080703060c020c010c031205090304050604030302151315020d140a02070c0602030a14 75
    0x40e1003180c464150200303409010184000d4a42c99000209420140306040070f40c09004400c0c442280d00000021180102900d520642c030b40c429001550888280050703941801240c0c103140381462403400b07049805004445041d0a14102404290751010389400c000102000e01e00d4064030030400580703008881c84000589402980c000d60180001c1a08038104108803a908803004e0b5540c2c08070303a0f0062191182d500c030401049042001c5548a18031036000d0004424120412800c10360840310446030081e000c900450821020044540154083c1e000455446000280a810184841c05907810000103503003c0740030076004a180803664041e542c00148503500d101c00582180126040b4640c04000007400006041c1d0000b08500d846e00702c80c0a0f18000e494074100c5080000807410010315407031880105082800e5642d0160132001e0044c440402c81464885101c64420011110200c0165020174024140101c0903900e00203001a400254903000d50303040c024010380355044076400800340c0003a11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 785544154 1250 785542904 785542909
    0x20c07050d050a0632091e0d111005040506010303090509010b0702120f0712150608070308160605041a0906010e0a09050109170a0f0c020a0306020c031e09010207240e 73
    0xc009210444000b10029483c29441c49185194141e480d00001d21454a0b84130305481035021140142c7e4040b8020701d581e005100d000d444600d6200c050264502a218410050780b80c58011984180e2242c8050001d940c194540030300405059004a4000c1c0c03c00001441300040c124200d5020540440c0c4000702c0141c070300015464402009283d80150080c0a0b000500c174040429999220348281134461409202d40c1d5150b084880520900340b550340f0080b0108003103070760709004020400042d0fa003480403e40b261101c405855013503034101c44a52042400c809000c50380ca58850300008003c001e40b015514000c3d000a010f28080c00b4071000c4c03a40c03032000d002044000d42c40421600c5d4000103025200121221140180d004104000d001c00d030b03400c07404500b0f01d1069090541300c1c0e82c010400810603013152110070094005401000b403e03c0100480941b04040c200860509101800003683e04e40e8031400081c1000d890f9405000312500d20484219079480003680700d6180b014614251000f042403100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 785545404 1250 785544154 785544191
    0xf02060d0902041a040b03031905070201021c0804110d0c0e091e061f120f061e0b0a060306060909050a0b0913060b0f0d030807090810020c07050d050a06 67
    0x40c003c0d031162609401c2c200c100d0740054642c036040c1c1c0440381009000f500a05040e04c2e03120356912500c2c007561a0200e04400390003000903041150041c4102c030003a2103500d954540000200e0542c40201c0c602000304001c01160300b2404410318400c1e2034801d60100166100341440e081c40c0180508552014001403070400c00300800c100c2440741004940155049905140c1c40301c00654030b0852441d500b444110906a054503440d04230750300c3c42e40309a00701d450758403004024112a0011078040b9128842c111442810400c1696003010b01000021001c2c48042044000507583c0d01c200c0c103240c00c0c114100051a0001c2250040710741c10030003c540381d5519442c0c40300508030349402d20381c00340c80003040c0301c803246040032510702c7c0e0380c46170804200f050100c40411480b0510007440340d901000785000c1d000024401c4e48090303001a09410883e00c070649031110107007440b0703166018601c0d40c2d5020480403181e100c100060340051070f058a035200c100140b40c0b100d64a481900740040c004e65298802c09404940301c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 785546654 1250 785545404 785545421
    0x2c0c1e040c030e0132040201080a0207390e010f0504090203010608060403050c07061e050c0a0803010b0a0201061401020c1e04150501030b010e01080a090c090219110a0f02060d 77
    0x5008000c1c06240b0303220309007041d030545024070512800580003c80401070064140c0287c0d016111010681d5618280070069440210304841d03034207021408101c015001000182d00f54401080e115040302009445d480d660101d60080d1400c00d01e400040000d030404205920540d40c050390003180e814014000301e4050102e5600c46051407190404000134585e10801030103c02205c002526203075603554200f268020500701c007401d1048604611013044c1c0c0d000d0002800c10809603410741d0000d2202d07071680305094100340e00070024040d000030740052150303080c4501300180243c491041d913460074100000b9540d04070105483d0250a0b83c00103210268039402a203000150001c4c4180b000100b100315101c000382e540d210b182c0c00309080030080c440d20f40c013401c583c105610042c0c0d2151400d03581c0003405406480442c41c151342c684c0b54010302080d5a1102e00003441991880303110515142400c4000420007008108075000c0d42c0c0281c04524001a840e040d0b416180760116034003500c03100f406102d40d00404015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 785547904 1250 785546654 785546681
    0x12032622021c24020307091a0f030405100e030d0b0d110405070212130303110118061802040f2c2119090303030c140403152c0c1e040c03 60
    0x1492901c0c18074543d42c00031031080d40155254080b4550b10f1013626200d404e0308c03002411514050240b030720181c2440c4065035100e4010012034103000c2504803038008440070140c842e02e840c6c20000e50004140d131180500d6001403000d0350b0001d83c012640c0c88401700c8401070003172184211384650200e40d10130703c01c000c030030040000d82d41d00035078505d01c8030f07110204002d0920041300070900c00c800410609c0018402c54407019103007179000e03c182c20256981401840006515140680440c0c1d007000942c5a502c0f590f144040c0310701000900c1c0807c5011841c0b801001d02c84001010701445400c1d01018012401356018506620b0741402c204010b0110505e42c019a200340901099120701d90000a03031000c8031504880c042c0d241000904031280f802c40b0801c0003c1c80b8149210000c000070000902e401c10441808400458001088805200241c0f586044540c03011401d500312440500744034408d008441e02814112010701c52070b100c00509581002d00400f00500c59542c0d20658031a05020340c0108800701c040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 785549154 1250 785547904 785547953
    0x230f09010617030910050901051602120304090501030b15013c0f090b0a020304031722030b1f030618050304080714040204050a12032622021c 62
    0x8079000580d8a4124058040c884c01c404417012070f8590142c012a045124184d540038604a04200f41c840c00118800040703800c01620901e00c0418141032015002402d00124007042035455403d0103040032002501d80c801f03041011400000c26a0408107401c1e0400101140c0103241c003c9030390740e4500201d160000d0200007410b40840040b15440804405a406180c0b00d42c440591100d801c0984da0050b4480345001d03900401c42803020804c01d0410003400340800c01024a030030303500d904811000340c100080100482121006004008003224496884695190810300c42c07030114000c0224a500c0c0e20001d00740756a100050100507541302840e058081d0008116542c030303961109107694030721003480703030501480c81e1001d261024901802202c08996008003181e0354142040000d1030941d40c62a0110140701000c1c1522904001801003a084ca44803d50305641910303246040302d0249010b80c6201c1e19081c48140340720016913503110400080c0e141440307034006071003051400090b5000541c10526181c1c54 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 785550404 1250 785549154 785549189
    0x8090406060809010e010e301b15060108040803060f12030c162303070f030b0105090a0e1b0d0b16090605120604050c160501050a230f090106 62
    0x400c440ba05026100d0b100003000740f68081282c441c00c0f56030302034076040b0640101400488605100189001e40c0c034400020401844140080007502e601039094070b030080098048884800034107104400050f00744e42031790903d42c0742c50b6000a2000f04000d00c014607540e00800171407020b841e800701c4000c4c040e60142000044030103d00c44203a0fa500400700b040601d00c281d207207075180c8600c00a10082202d034090b4010903424401180003549281d6107400750380520658600003242543c00907414015070140ea4500c00030350501091043c1d07141e00401113048513050807041c08090310000340110007071241c02d84076400c0c051001c0003d1100710b0703203c002500c44580d500c24441d100e1203403000c607501940103840c5e803250555107500c10b682500801d80c1c041a81c2943d00000b5050381017980109520004481c40c0510308400c0300c12042d60003080342000e4455a54480c100080000c542c0300f030340074081c42142da0803100b004051018071400300040a080b4000302260108130202c00940002000d00322001c2c0381c041c0f080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 785551654 1250 785550404 785550407
    0x3130606080a0303140a0e0309130b090a0c02010b01090501020307060e010204090f050a06080d0906030b010509040c0e1e060f070213020f070605060109030f12020703050f0a051203130f0809040606 86
    0x40b400d00411403030030301004190389050130700c9087d2640c2d02840145090520201c2004a2290403010309844140c41d010960215503900d4106c1c0d104000d4520009111801d04d1b20090854480c0300c46281442103600703080c0802d0703800105a40c82568007940102d612014030700780c4c0303019010310b500240025003003d00c0d01c20002e0054010a115040d90303070007040090b40d0b078594035a99030001d0b082074000c00c1061409021842c0b00f84c228481550043c1001c91034242c640b80070030300300c4070f64004440000760300c01c684000c2860105e2101c071805034912440d410300028040083c0c239521034070b24103c00c1e51400081d4401151902103440c0c1e9080a10b0000b15122075860710b0071a159400304a08640706883c1400080300c0e980200124415241c101404030040c1600742e54000d41051550348400951244400020000b101042010400350100b0f01903d518016807410350301c1d0103d101c50700c03070581074140204000704059000600c030300c0d81c0090404000041c2803d1545081c440c1208094000d07052010104505 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 785552904 1250 785551654 785551661
    0x3060801020313150902090f0a0b0603310201020d0e0411041508100807031502090307061d041a09070908030f031905131b050a0f0e010807060503130606080a0303 71
    0x107600503a401c0c00d0401d00f130b000d40011030301d080b1402540800000301181d80314403c0c80380c0c0ca07440413040c1c038009003046040c000124540c1084800c3d4141507548440e845c095042200154034003031990b0b074108000222540044e40714200490075208115501401c0c030440d681c0da8010350198520000c1030390782c542e201c102e00310095590241e00c80c08900a100420700320b040c10703d1820204d49140c40540300d40d9085680702c404642200c580030702d8440e0240503c13005503070148070940c002c0565480d540c4100c00b00e803030250000b01040144a1159190008408640900044010080302d00b00d5000200356520f41058940c4121500180c5083c800455100b074108a824002d5010301c01c0c0d40b0721080b0b148559030108090394021180308890301e40c031560107000540200703981e060002002028000950b2141d000c1083e54242d64049491584400001c01005e9424241c1038050000356000c0c10506084ca50042d1071480080c1800c00d61101c9480b0080a0058680c4034202030b001150645081c03050500f07000b0081d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 785554154 1250 785552904 785552941
    0x161704140108010308070618082101170606280602150612030a0f030b10030902100507031d0621091b010e22050103120207060e0a030b0403030608010203 67
    0x402104690420303990300560000e030480758401c03210380c40c100380c0340d507a400504a401c00280d1281060100c250014003400040c0040342c05200040020071300b00703034a0513070640060744800d4410140403501d5410741d43c0407440d181d200b00180c0368032540001407000134419180c601185001a10181d0300410440ea02041818078901000c2c00003045880b084100503001c01c4004244600368420440c43d00164000c280382c285043c294280040d2008402010a41b40c0d038080361079400180d0344801071011850b00041104a0318510710b040c90400c82c9070f64000d020b0003a44041200080c1205c01587c01c5035841c001210070075005150000d0025408286582d01200c0595228503540a45046028010840011503041c280160f65545200e6581001d00c40c0310403042c00155141c8440a201825540e900d000c0c0c58001c43c400c100c5407850340016003000382041c0c5550060001c01502c02030305d004540d61298903000743e90708000c0a400310b40300e524040d0010003050307001024a500100c108044080098650b084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 785555404 1250 785554154 785554169
    0x907030b09060f01030b06040914010f1a0a050d0501090813180c02030f070c08150f100501120c050c0616030e0303061f1107091a040504030f05161704 66
    0x9003074a9503560203480302000c94103d45884185001040420024a52583c00c280050b00024403400185c6920489000503131910307185a444070440c4841080c184100c2d91103d80c0c8082202c525407a05e400650030b450103128a61103440590510000c1c41401c0d40004201603004e450a6a513103004100c103401c1c010b02c3c2c820b203c0d001c82d24015412002229004d0f401c00000158041e514014000490900c00e802580003a0b45074040726001051074a810000c00300103101c1c81c28400030317515001d05102e40c40c00b801409001c0303043d00715a040040b81d030002e113505549005030300085100e805240e0202d965008030240a1201c0c4039000500035070301502030210401b0103440c1e07402d00802500c0072b6469600d00c01610402d41000c0d0100b064030070f0a03116a0940e80b181068a0240c0910b00740105152400000341c1090624664403003e000c51080304150340600c04000f80c41c2070000b450035440181c281c42c00902038000f070201c00a10120b24420b11a504d08860b41e00143c0c04401e80ca6283c2214100d800c039016102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 785556654 1250 785555404 785555423
    0x9012a060906050a0903080103060c0c020402180f0a03050607031802031b03060a02070b0c0d0e060c0301050a0501080c09040b0a0f06120c02070b040314011d010b0a1a040b16060203090703 82
    0x80c01008540650b080c0a60161121801380c1d295036030f80d20042c40b0003c110004c2100c0140d4cc0001a907440c0000c1140b02031440389544a2102c0104000044030600100c034031690500d4010000240042036240c1d10001c0c9090015000c12001e01c025042140c2000c0298180105c0c000400d00d2401d20102110700c1c281501110505d0fa10320b81c11108078031410001418070b103000000100c0c804040c40042442140e0780c0800301d03198071f400408038601441034402e0124148080014412820800c40e4100209000d203844200350130142e0060704203201c0e0a4416010720303281c040000950315450810750085c000c011100c40800e030b480000810162400c001011000e00b4400302030f069a20020303540c020b541466100c186003602d5075480c0010707040611816200c0d0b54941c2100d0300461360100c40071144500420002c00c0301c242eaa410071114448036004030f6110109422050801341004003540c064400401c0e0300fa03980c1c480850070782080c2c04000b000601c0390f4000020070210340300124501c07044a00c00d22084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 785557904 1250 785556654 785556661
    0x150f0a0c020c10030c03110414060702120d1110020a0512060f0a06020705090c0a200f120309060901060f060f0203040302090106030209180106080c1803070602030a110304050609012a06090605 84
    0x50494232480c440c0c500c005010410100b46440c00000410090344010100085085020030440c01e04040000c28008110041c4504600240600101c0e941024090085140c40000ca17409005c90040f10892401c4007044e0700004d0f21504d400040107400b0b07800030079181d001e580d11503000b59a203066010b2940a00d161001103140f81803880245c401080c035640b80c0043d9903204400b030030300800e400c5220307040c6846005a0390040d100c0a00c0f00031403a03001c01a01c3c5903070349488805d55103882c0c40502400752980c5010320030042200081c240c541550710381d02d8042011682c02c1400c034554040e80d00b01079801100b000000404d0364260380100010a810382c0c040880d5074000c0c4002542800920034800031640b002c00050356001048010240f140f4420304203c12503101d003000c00c1ca0140180c000401580c0000340040a00340c000a122202100150046250074105000f02e4240d01405001e5410301a0162401131155440c00d40110207841000245013480c0300b03820000083c3c5600071040e11590300e0400030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 785559154 1250 785557904 785557931
    0x706020106050d120503040218010308071419030f030608161a030403020309010339031d030405040f02090d030513060c202808150f0a0c020c10030c03 66
    0x10421851303000100b90300c1c0340c450b0b014280d5250780002d0040f68400003824203080c0c02000180c1e140e01039030007042c0a6486214601d010f4802a16a1f540010280d110000f0800040c01e032682c07144195a25103098460000c0c529010380190000c1d810401050158118080000c0840d040d020116248100714106c0041c10884010b0140f2054034042d005070030400540c0c5841d4002c0e00043d07981d980c074014000008000400d126042c801140489000340910414200d0480d450302070301c0220040b124041c1485c01d00400700640e60f1255108a6020315169200d01144030302542c141c1c0c511640c00b41c43c070751014805150040103540524074040003d000f044003c030701c0500c14400c2c1d0071404c0d840701c40d8101c0d640039078a032851240201c03100c2c60791108440c12205080f07400807107249402240d101c0d88074078007030900040700e0400103850100500c510341c5c80f00300043c14010310b1303045402040b44400050010034410089082800c00f400d21a008981d103044000d80951560004405016684d010894840e04010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 785560404 1250 785559154 785559169
    0x606090f0405031204030c020a060507030e030f070509040c030c080601090e010b090a1e0617060c0c031209011103010b1803121c1409011b02010506130b03030912070602010605 77
    0x1c020b40a036009100c184030307080601440c0d030340050080c100590280e8150740000c02e01c0e11030303070800400106c000c5000010547c1090000d4600b640840240802059102d20b031030743c0e14014440c45210b440207002081c140710b02d405200001d55085100c412001d603e0f2507025986007420311031003511078a80211540748004c18031407802400002440fa51650321155a480e0141c840700d49200b80520b40480e88641d070a80d148a070800829140c0c01342d000c49525a02014141503004000a2903100100540340030301d1f0020044950085000321000401e8640b88095401412640040f03109580c0000010401c084100b026010b0104003440c040060440c0781c06260b01c2c0d1001904c0a07144400c00c0c8541d0548034882c120340180296070040028a0400d0810072080c044429250440265920b1003142105a14903030440c07000c814500090105060074404a00c044100aa07c24407080e650568040a90b0f0305100301c4a00c1d0748000e2941e0407091041d10b68a031140400d10540c00958030701140002d143c00c1c5200f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 785561654 1250 785560404 785560411
    0x403140c0f010c1401060f080708061902030910110306040c020c01080a051f120203160605070b18030d0b10090807030b0c0f07060209030c06030105310c020606090f 72
    0x100001440040c07031005484001810300111071100203050380700403800c0c00b44203490051070300008403420145810040d9061011070381103407019801103010070503000d142e8110124a1103d00c80c0040ea01d94074904882d080440401809803614107017040300425030092005503005000480e0700f00401201c0b00c1c0705a0b91080c54100d16408141c01d1000960051055070116030301c082d1506c005000e4009410b614009210a50010482801290505020b40c10100b04120700c003405007014103003d40c01c01710b025003140198800105089000030001f416030080300e00d0b200400321810b0807242c4a407424224000070780280841c6034040e0102d11a42052140308940f101d08841000010301401070840d100d455580784c008041502c401c008000141506143c4002403207180d0081c3c0c401178a0b104100d0805040c050002a81882030400344010300c0306682d148441c10080301045a070000c101c40000d22425400c2a03400840303451441e18400340c8800e42c005c81c65500c200710489400c5403d641d8090b03024075a40d0300341e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 785562904 1250 785561654 785561659
    0xe0609180a0f0905030705010c03061a1e0a230301050d1103011127040203040c05010804020f060d0209010e4213090e0703030e240c01020403140c 64
    0x500300e4510349110200164020020820119114a852003000309481010340122080d070303c00a804000d200c0284615450b503011032905024151925502110600c0140a000040500010002d0100346060f07080164000002c0c039480c5c807560a060003078404240d20318a2048000503140c140c1c2c401d0024000c0b241600e40003440d1200d4001c1940740c03030a280200c003240c1d58041d9607440c828102c24030203001400401402e0181d5044a6501c0b04940366103082020300c4034002ea0051050000080704a9510b0302135071400e281131801540c80740001440c10740381440c01074200f100000c0d82c003850a00c680042006110030303241c080b00004100240420044554103c0f042000e148121280b40f075404030718a58146460342d4424011801414084000ea102c4840840c9103080300c03004004409a501506c001c84016078040c10406145417000303045a035132140c0c0d003071180354203480150710901d91800c200d4200d889101e120b511907891500c1300d8000d50103800141d407064072060700d41c10403850008500c135082102 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 785564154 1250 785562904 785562919
    0xa0603260f0c0f030c010b01090f0311100e0d08180a0b031302120d02010b040605090601140a03090807050c0306060909190809120d0810060519050f13060e0609 70
    0x1035070303100c1015000810290b10350f0040c000701005505041010346241c4514200014410032207100240007990181d00c184442807044104001049800c4e414240c5400d0940c1d48a2161880f0602160781d100151410b43c0d1083d240030900c000d00c88141c0c003610039070006d034081f03026281c00d00e402c014015144c0c0c0f1030001d14400c1000010390940c008a4501c0c20b0a1000c0c0041c01e254105d40b0446040c42507402104006230741d2200460007a190a0040500a003029556030203182040c00c002060601d0030700100390540d100040c40c8a001d4444d03031080c5841c070303045014a52168007070700c1c0c00ba0310f40c100c201c4031070311074840c900200d412031034080000c17401090190010b00040324036a000c48450341703000c40141d0b107507031382030100c41c000352141c641c0018148289400740805c0b00849801500c803940203070000c0320100b8000350500c0322a0700441190401e07031005490302203071072942804803118403a410881d0807000020802c00400070714089884155100d0740c6440c03c0703d01160050021301d00801035130b0b6070f02000c1e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 785565404 1250 785564154 785564167
    0x10f170412020313120501050a020403031710080703030816032903100f0b0102060906060d0209090313080706030b1801180e030f18030714090709030b0a060326 70
    0x11445403841c1d0385219005590800c2e007101ca000700c1d0600d4a070703c81d000c0080401c01c440100403003885017592001d1880c10841c1404e0542d14003c080810106a10700c82140b5000403e50075156001c410008100002c00c8601554036890000d001e0b003800d907140d02c003010010002c0b104c0180030b4051500d0510003144010804040040401048200e9800c016094011418158550002c501402e0581110500003040880400000a00d400402809100d00b0782011051001903510082030070312203901150710a03c261140c5840c00e086220340b840342d1402980618002410030300102d003403411140741d51070400459580704103000403c0c40810303a1922002000740184250140301303c0003000c8201c0ca40d000075458040b828901c1c07071503015010101c440d10012030030030303021042c214521b08400001e8014004041c81c20084c0e05007000c1c1e8800c100c0c802c801807800900682e11950502d030003076070816501c2d01e01e82007417810000201128002510740d1005644004d480740030001c28210780d54040141c1c07601d03001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 785566654 1250 785565404 785565413
    0xa090b0612030304080a0519091502010c120b01050d020c0c10020613060c031e1a06210916030b040c171b03030c030d050f01082b09050409030806010f1704 68
    0x5210200032000d00c0341c01d12048c540c00346013144149181039581c9074443c0180c24454100c1d02080c1080c07074007045a0600300c0525059038401c1c90201d1400b20300a021400441441c0143c0b4180200c003940b008003840881c654003032080014502d21004402c1c2c424100c9101009004c90321808210744041c40625205d541d94001000c650104022001320700d40000ca81d407940c4600d40031170780420821801170307480751410a24000085c140c0c595952084800c02c2ca48440201100804c030141c04400ea414551580001d01c8820309004010521213440500258540c980c41c0540142c03609450544008112007404150800c15503a643e0542e00d030000241161001a40c0209103611a00d42d1950180000c4c031444421080401c0609241a0f000c0c20220351481c118101c9001c0c07902c16800004140c1c0a4803009604841040c0c1c964400c102c6c0800d0220a000380c60001e0b43d080500e0341c401604071f0714102c4960103143e403100c1c4d0b1a00a8a09a1758066014103920b01182d84600750b003200d50502001102140014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 785567904 1250 785566654 785566657
    0x203031909080703121104080a0213020403080c030c01050703090f110a090906200a0507080702010309080309030309011b140c070801140901140126070803030a090b061203030408 78
    0x9035440880d0514640c1d4600c040d03504006821400726041d42c21a40b11181c0340c1c003030786603010a01031034207041c1460b068044d035941ca001c0c20b010b80076064984c0c4c0256842c51a0701224051a00300b00300564607c01148215603e80c81107216401d03e5192030007042c4050311034080e002c9071a4200c0b01c00b41d68140e060321411301c1c02c1c4901c100036502440800c0c001580c10a54000c800c02c26008110004807024914070254000045156200c05e4070801c0000b5050180c1190070303219000d42001401e41c07203440e1440160300501411201400008000c410069646030000c0114412150540284485075540680c03107c035070302541c07000f00441c0741034440b0200090850301511a0075001000c07900030642c2c6a4a00d42100d800c44074042c103045078030080020603a024020003c0d51042840700483d607614040f07190380c3c1d81682c50860340300b1907554542c00d0440d94040009002829100d4240d03a03803401d0000004006090301c581c01c68108030048001b0b03501d49000c2214500f000614409980f45549955a44015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 785569154 1250 785567904 785567941
    0xe010908090f03010e0f0313080c0907050a02031e0301080c0d0b0a020d020f1305031509031e1c050105010e040203091e03041e05210705040c030905060f01051807020303 74
    0x50340d80c1d072204910040f010018078003106c5101c405955503601f840d65100e070303001c4203070404103050340901e844d031200d40c440000207a84031031140380081e118101440200e085100c0d079090860b484800e11440020070300008000d40c105c03542d090880e08115003c1c02840450604000090801c100040000d410b00c10740e03070028982c410b0204170052900400c1c0407400980d401c0020740310500c0c11611418826410100305602c450a0f0000402582d8a010b0200e256244190780c078005060101d07455090710b52582d03105980149540c1441c0c45000c80d070f8000d401009100910403240002c1e141c505408036400c15200b200e010b1042c150284c04243c8650754150500255100641c00c14032081100083c82e200700050080402c030050382c000b0380b06241504110104c918185030203515803001d8040c02550000040394030464606032070110b100100b0200550003080080b00180c054000d140070003021204038002d95050f06d2049880d48907440d1301c800c0300402c4450072141c980150f882000441e81580c15000911032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 785570404 1250 785569154 785569159
    0x90601020c0a0315230105041109130e0c01090e130201300f0e06040f150c02010e0f0c0a030f230a0c060206070e0409051005010f090e010908090f 64
    0x18504041d1000c51041880c541c010b6442c1a6400c0150400c01c501c1d00441e0244e0b4030320446505480348140d15107809076010301ca0b05104543d035501c04401c15450b1800d441894100400c0b0f045031080034184076020f007910f1f480205450007007012004c5a580102514000d54215544080c040d076203044600107900d11000741079040c44103c1070011003444080c001584c1081241000100d1555008180016a0701c504c2e010155503060800b1503040b08000284594440c1e0030030300701c014080d168203100e10b600131190b10a26103503091a00c8c200d070b1160150040d0744c4200340142142d0102d500e1040c0f098031200d5911241c3d501064107e004c202003170901e9514811103018480030341e2070310700c41d81181c0e5894881031100d44290f00f000c1d0744402403210250000b001440a030000e0300580c5401e640007420701800b5203005104a903580041c0c4240801044098100c862001e0100321a5840e072a40d0000801d05108034862030303040c0140e070703d055501802003200c500e60098065060241e00c4c01001500718000c000c84c0d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 785571654 1250 785570404 785570413
    0x20706050f040f08070e0708060d15091b0503060c04060f080415051e1005030304053a05100c050306220f060f0518071b08040b27010c0209060102 64
    0x494255100500004013400002062028500f61113009035a10080000c01480160320820519444044000340310b2035102e6003002c44c207802050036000400c42c0c10800f405416025490003500d605402c0c03040c069907001c50031034840b540c07a01c1d1002c1c1180300394004c0d1302c0041d101c0f040d114102d5010345032041d0041c5c468901000c81580502c80c1c032048420480d440f9000b41d1019034480d20b1150180c034156001442040e01060080c14400401e0341c1c0d104900c5680c1c0520701e0302d00710f511000108981c075010709085640c40b0520f42011050344114041d00d25043c0d50324000c05010306402e00080c460407103100010b480300ca0441d5102c20402155801030510203610503401180140d007034406101e240003811440c80005059400d0640c7c141d5810515003201d4010242a40219000780e1080f41403540101d480ca040300c3c0d44464174001c00d00c00b01d403171240100512004100400c0440e007100c05004032100c100140c025225480030700003004c5022185040c0840e8044041304094102550056406401030044a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 785572904 1250 785571654 785571659
    0x6060706090602030118150b0912060a060e0f0103050c091b0c06011701060b030a090503190e011205040b04410105070e01051804062303010e030a020706050f04 70
    0x403419141d821500725462640000113100b190384050a180c07202031609001c1050504a4140c107082020301e00400c000b00c04003040da1b41036030352602502803040d08440d06954450422000e0000079101d2070040020100b4070700c0001c1e0407440c081e10715034103c0c6d41020003000046c001505101d840300010f000544903003001183d545a0040210013444081c03c8140106141d41c5400c0f6210b107048010402410b450341004030070010f0080c1602900e8104074100b400045070310b8103281240c41d61040038100c0d00b016020590180300150402c54010140f102038881e10880c681014145080f10000c58005242a0004011401040341382c0e50031405414141410034542003140030a03400180544000c80340003021a17104000c00b403082c000c45400212600302000346041c40d40010b0241e028642000080200201d040c25560343c5581005009201d95031444883c4400001c1a14803600e011010901030360810714040c1c818030300001140d48101041e4041c201060a1050854056004003c14515202d050001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 785574154 1250 785572904 785572913
    0x2280509040203070c1205270a05090f010f0806040804061227051b060328020a0e1207050f1201060b0c01020703080a110f0c150a1e110403020405060607 67
    0xf580616200d484003c2e00c91018601106c2140e140c0c4002e0041005c140400d01001440d404041170890085440d00c021380c4200e404284044695840154020f1140051001e060f0307030040d205e41660f403005500f1112540b5410301940d1600181c0b030003852280b04002c01c111036442807007001c01d2020406400b2076110801692038410306205c0490300c86003201401f400c0100141040b006903070000c59003402c14210503e0001a01e1800f005001c210214420702d91544000198142810b0031500c0040864483c10390040043c89440220300d59400380c6400350545036440d4001646804a940c0100f5081c01c82002406001e41d0100c005541c2900b03640700c0300f021030309840305d038054910104081c0005848100c181030091031900d001e0710100e6150318002a0b80103030603003a4101d41c10043d1131182280d03188408007015290100d61a6813801440e8641e00307021014085030040c00c9540255610704ea000852050f40c201111400d500c01c81801c50108001c00041c1800d4125941c40304000700080e04000d030f9070302d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 785575404 1250 785574154 785574157
    0x60b130c020c01030c020a0b06060c0a080a052505060c09030f1906141302012d030606080a0b1c030c050f06070201060e0c0304150e15100504022805090402 68
    0x8038000541c1110702e040809580c9442211030518130343c03005020450707090311030060b0281d0292806014040000c0c07804116041001003501c2c580e4400c4445560760700001c00108690003400c1064440e200c0ca80040c0c1401d12551202e000c0150002c001d002c290f2100f00001c0708542c07242c0060368042c010800c02e803000000c00d001100380004410105680d0118600d044011108909440ca1041d42040f040c0400c0e480f0007100340121a9081c2011400f804c140c00740344100b003003000441d005038010140c0360400b09500d900028210340d802e031120319881c2c94034403440c400d075021140710640001c881c0c0c0711020b00900400a142c0040d010381001d03200d040454460710f05110700c288080c40d2940c0580e0a1240c0d0301d60920800004140003450b80119080840c012419440081c201802a42e182501c4031030703c000e558002d01c17016401c0021207440316803ea00300d507449001181c03098208905040002004e041a0003292102600720200d00d00f02c12004909281c4d000d184410780c01000030a020f842c844c2d0300c0c0d920 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 785576654 1250 785575404 785575421
    0x240e0f0307030c050a12080706050403031404150c09080c210303011211062104050c1207060806030a020609100909140402040b0d030801060e01020c03010c080105030607020712060b13 80
    0x1181e10300e041c04c06205083c1d10550000c03401c840d2807003608020451041c20782e2031081d0b00a01c0400c0c0f0b44c499040840c064440488503510503140c0c80c0c140420006120480c107500400f42c00b0074420034941d520140c40312413035841005915004068180305614107520307003040196842c2c1d48030741c00c1202c510030503246400903040034541251811031907081c815500c6008108000849141b071a00e0303030381a210040b40a41c924011401c2d42c0345004a001c0040078000800f41f8100640180510200c0d410003035030f00c000038803e401c007003000e11010a84600300400e07101000b540180c041445d0207029020300c0000b010345090103040002580001c28102080d02580c90b440e28588038281717681c01c003401000211901c440180f4800c00c0c0c4a903004001035001150f03541111080d05048410400b07000040c0c1c2480e01c10301109a248d440e2140600d00150460b00c2c540c1a00c03016812940c642d07403017071420b0781d50b0692170284520040c0c2e0f203642e0000144140e001720500040207000609951408a442802c0c0c88080c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 785577904 1250 785576654 785576663
    0x305040f15021504030e01110321060f03061b1b010501030f12030b010c060c0306081006091503150c031d0c330a11100b01020601240e0f030703 63
    0xc181c40210360b0401c03240000c90039100e00d0b0f900e03600309550003800d00d45941205a043c060a101c006905101c00d205491140c1d4500b84088541c08030401c04120309030044070554890307800b0481c07044007030500144062140c1061a100404560390241041c201c1c0c01a10160441941d41100810300007803c2c0104c0e40211b101d04590489080c0034a486802d040704248000200352031f05070044050baa026034058202604205c000502d2680000210302034071680d0040341152041c50007070140040158041812900a84020080e08a4000c81c0341520311183c4406000c419204407a00446500390744401490440340c03c00140500d1291100100e05903031101441564019001b504010300384088841c030501710160125030044204c81e1120640e100007011017007465004100b0356005030241c5c1d00040d030403040800710782801d44012a58409003103046644c03401030003800000290350003500c59250f00011003440ca0b075405c640c030b048200c510600039103540d03034044a0300c501ca020030744050040300e000d075004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 785579154 1250 785577904 785577929
    0xc0803180d17070e06070f081e030414030a0203070b09150c07120e0d08070204020409060803131203050702090402032506090f05010f050d0e060a050405010c0215130305040f 76
    0x100307652082c10600070031042c00d129560403200c80a0745c0340c004540c0c0c03656109844011210403800d10050354010401070352103c05a003003030403c8501d05000075600c120702c01c0c0c08a8240c1c04e56800b20a0b10303030058a00708405640144030000000d9a03c2004a6020807807900b164001f83c0038549030f201815041d00c1d038007441e00d80015034a05020019200c4107009070141080c411141000340400c0440304400701c06401086c3c0801c800c0215621501154001d00d111003050101c0b82e00e43e2103150302ea502c6229003140c69495403000145129100c11001419505a01d40d1410512190280074040d04028000c07a41800364020314540c645901007450307019403203128121710a50038400050042e15041c1c02619160034020001c226a07a40100c0d8050f0360070f030380e25040c0d440d071071501210805020b504440070b04c14000d0000b001110b4400342c0c05284100d0080000380318000244005a8450200320040081c54000d0800a00d40240300c0b09031721203140c442d24007503250a41e03405e00307006d03014140c1c4c1020446a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 785580404 1250 785579154 785579177
    0x120a050d0309060b0a0f092003070248010309121206080c060f130b07110a0b030f0103030e0105070b04060b090c0418180210020a1b060c0803180d 64
    0x1e0f51007503040080c02600d1504e40c0b141000c01c212007410b2140f2503036495a84580710058110811946283c0304071a41c452142c03681406c42c800b0317440d070400d680300000c0e214004e91a0b0072002d1a000c130f0754000e00c2c0740c0201c5407450182c02c2c0400446420400d8554103160700e4075080000141500060410452655101700700c5c0b00540800006607481a801442d55a01c8011400c4069035070508403007900804180e5107a403000f00c050f140e0408500e650100b001c103a07011901b0000e000990048240c41c140c00c40382400f48503144e011078001c6020503140721007403005035070051000078010054007001e0304050408a0810402d6641e0158010040702d007140c2c5580c881c0c0281c25142070514001d60040356190400303080900f48110303029801503e01044c00c0c62520351010191080320100d15a12650b0040d14101114681c3c801c06550341414200444aa0b0401c45001d40150320251880050b04e900795500080c1c00000e1b21241c01c5500081d00f0002e009074001d58001c0c440e40704100b510600045074403658880d11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 785581654 1250 785580404 785580413
    0x303090606090207110d06110f0a17041a0703020d0e0a140d0203180a050901030b0f01091802060904020f0307020a1401060e0f101509090b04060308040302120a050d0309 74
    0x7101035005425043c01849401c00003011440ba032041444140c2e4030442c000e916091800182803c100083c0c0d0701e54000504010081001c0f0040c030121140d074507980f011341544d40681c40c0c235040444000c0c0c12104580d40408119021403c0f075500301615240260500d6001040441100e06042c030380035031a401040d424040085590340500644a11009040e201b4083d0784065228420f182c0c294080f40d00510648600d6921640d00c1c0000e004007801042c929a124030744203d6000d010360701d00c030344241c40324000104885c5502594242d501403600c030001c1950290b091003070681101c80e045a015409004241c40510303108091032103180c1c65401080d005810341440c41c1081c4004544252990401c002440f00031200503e040e003008641801480958982102d085c0d01c22081d00042008482011380310040755008038030340d040e2450b6640030441c8102e01d00401044400c01d11000341903840511040016107043c90f84282120318070000d40b0360b0410030707075202820240d00800c400c0101e50b44080482c10f01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 785582904 1250 785581654 785581661
    0x1103270402040e040b181005060306060907050d0b030307170301150306080615120a03020105011511060604020f0f0f0d050f04020102060c0a180b210c03010303050d1803030906 77
    0x48000303540440c90103041c10b103103005100c2e0041c006461500b008020030f004090724039034030580c010700780242d850801c900120320000c0c0c01c0903100240700b8801c85010813283d1a11900007805000903032a8186041d0906140300c001d08494601c4903410300040c8030000c080380c00720980d014410655044542c2d2036040000052005c40b54112031030030586081c50600566100254158028642c10310f0b40c0c0701c8460540c00a1444541d42180b80000d01a4207208010550150411070507102a10802041d19003281c808032004207013441c0c0e100d0b5030b07809003000c580641131a40c01007034082d00590345d06284c000c80044901c06613020366041c80720041c0009407000ba0076942d01c1020340149045031510507038141600000d5840402800595441c034000804886403401002982c4d501424076541042d075960b1181003c216401c240d54041c90624070b144103038141510707049c4040c41101800000c60a503421500c0480f419040f410010701030503aa51080424203902600c559601442541c0100c0d240810f0714002041c1e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 785584154 1250 785582904 785582977
    0x3f1403030a0e0a05030405060306040b2e02010c05180a0302060301080f0613050a03081f290310030308091518010e060106230f0301060507200609040c1103 68
    0x2504034003c02c030f0028001008803000c844040750081e0b1a40c650000040c010040700d001039034051101e004000710580006180d2802c0c00c5610f00301d03000c1441041080c1d0980c3c1c11030860200080c0100031175000b03080c01079002000b412018004059150b00c0342e01082d01540281c00064065110800c0c5076068102080400d5001a81e0003541d001c140d0702e903070380e2590340d4400c40c1c008081c8a02100082c3c41c1c038441030600f4060910031180f410309180d48240380100184c4043d01e1818091005600c21380340b107420002c490107050003102c0040c1d00d61441e1030440e400c81000c1d001980e24080c0721203035002001a0841103016040045280341c007000300c40841b070300b1206585034100c11030b00b03c54010840c46400990b98058400c4201e40c12800c540c8074882c6e810b0078406c050b03500a07070004c044000302c1c0c3c565011010f050882d2140300c9000c812504041440c1200b0b01d221071a940c08502045010560305054004034054041801d2986008606080040c00c607040494508008241a24000c804c40e03020b9041281 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 785585404 1250 785584154 785584181
    0x922052505040b12060d0203030d0e1e0c090c211f0e1602070906030506010e0a0e0d0302090f09043f0e031c0314013f1403030a 56
    0x181030310f440c0da08a1a402090010001580280000384050300e4100018007016801010740c0d550300035040114004090135504028244106410400e04100c80e9042d044440380b503000401702c4c1c141d0b00d4100021280024110000705e5000d0055101c03c01e4456946001e400c5003004040c514609a058068140e4218100b0f40d0b011a5111080010355981e0241a4000f26540c0c404005010415000e9240248950196136111702d4075400106001c00810350038183c950480d900d0003a034864001000a0740c1082d0460f0b600c9030001d018458a46002e03034010b092070b0001074040c9032004400800503010034801c9030180e031543c072515040d1241c0d03802010042500d41d280c40540c8001d1060400251149044a82e41001d00280c64160b894555081024600c5480060460402d50759101401005081440d040380d00107034000c000440c1c00c528981510b0320301c0000c40242d08504940070701640068455031000c1c0301c988001c1c05854045840012070f009a14001300c0216901e04081c2c0108007201c500030708041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 785586654 1250 785585404 785585407
    0x60e09060117060a030f11040c0c030504090c0c120f120c02120f04031b081002040312080c2104050c030c0d06090309090f14060f060922052505 63
    0x140d6607070010380010b0642c8034044494450394404002c14028100e60700081c03c0c0c201c2441000301000b010600302c84e0100026901800404031168042d40d81d4164400001c01050050100f404424119400b4410a08032450500788100694031600c5581c2418000310002270310b8080d0503410290480c46241947c401c1d00020800f9802141009449000d44080b5a001000c0015650046504041940d000c0c5400101006030740607200241da070380c4840c905c00e07050540510a83c078400d013206131007900e00322900423160390f64002c6503110481e11500000c003c0e50101e0301c18007a105141d6999030b4180311000841c0020580ea09190408600e041404841c05110364000c5002410603112400c05110040d2700c0b01001c5000c07072041c98151100c1140b82c20161a0301e140c540540074104142c0c00c500c5403c9001c84008050b81c50b01018041c40040384040d80b5000502041200414100b9a10720003184107906100148555144c0010003a00c209840356586a1020049520520a15a1201040c0d410783c00d246 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 785587904 1250 785586654 785586661
    0xd080a02011b052d070201030b03010902091f06030203040b011206141005090903030115142203200f0d0c0e04030c051207030e130b0d05010c0201060803040f121a0f01060e09 76
    0x41c4d5105501e4001d0425880300304480440c0c6094001101866006010180034504184504c4c2c84100f07182c440045c2598036407001400f82d02a100b03d9000d03507004900c2c48142da00b003050721800800001d03030442d042a81d580e0703001503819070007080e1805401d0740b10f40703290700038502010170070380220203040d10354190406c0004105218a000d03c0200089083c100010002441502614180241c42800e0400e00c042e1503c8007281004d806000103992040d4a0300c080032074a813010312000c2500000e648c1d0481108a07103440b9a00e0141c001c0400c003886003005000840d02c41c138002802d603005450450105481081c3c640c20084180581d0b00d21509138042c0c60b0400c1010380707004152801a2482c0740c050105105440c04040aa4102d00302e00c40740034040c400003483c2850210300078005444c503d4019441c00d8004190702070f012040342c040390009031001900904080841440118160048030a80c402d00402e000682102c110188950061240200341d507141c848068655a00150b2040c403600c0f000080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 785589154 1250 785587904 785587987
    0x15040605060904090206040e0a0b01110c010c0b060d0501020d05040c1d0103060906020f0304050a0c06090b09091f060905010e01081e15220b09060d080a02011b05 71
    0x3a82c55600e4100c8020a0420160000c6051482640c010340d07e0001914100401c1031160b42107414005c0c0300b0380e20105815060a180f5072505c06001e00c00d0300040c01c9034207040204440350100c0f504810003d1a400d0841c400fa80c68508980c421480714105607124002c102c1807242c0441248000e09003000e0894880700d80035a0b0514100050000810740b076a980c418406216681d03065805004080344525920f003458201913544410811040300c1c17814800f800440c0d994415600242269544801d250902541c801040130b203c0e0003d00414408003007040030f80c079041c8180000300007440c1e40d071100180320781807400040440942000c09414840368106011103c3c02c540001c0c0303101504420310114503280c0c6080e00d42400b588a048590020b05105000010980040c500e03040d100f500f40c1c1003012842c51030034441600803c071805a40100741000002c081140c500040404180354400082c010740c4c211030360813041d1030703169600f800604086580207a420954824184003074840c20f0100070b19043c240c0c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 785590404 1250 785589154 785589157
    0x4030b1506031b0d020910030b040509010204180b031c08100b0f031501020723030606030604050c0625150c030905100c12090501020a1205070f0806030f10051504060506 74
    0x900040f075441c001054690501554140d58110700300a16669075486402c1000740981b00590225118615041c081500c96030305200311400c4840c0200c8088c030085a540180008201c200100e0790940603400c980e4800704245202900a50456101c0500c0c50414198401454180d50031848008104200240340c060b09102520f038000c041e08006004818600c1c0101c0c205181c80d4018500c9004003c500c1170000c42c8007514280111041c0c0c100d0362a90342e00c1301095500c190a0307502410a0700703d0403440d521410001c0c0140100c0964031080060304424184800c10840c08000a81c3c000130005850348025030b07a4051585250361628007070041074515140d198641859100261401d42e680004a8a8034081c40d4181d4203002a80c000700508825030800038040d622944030030001918400406083e805a441003030302509a5036180641d035040031b50705558107003020b8040b983c0b620601c050750405034070400400034400c0092001080d10b0801d080e4101400000c03082c07441c401d030300b004418013a5896000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 785591654 1250 785590404 785590441
    0x916030f0312050711010b06090a1a120a0b0906030a0b06060a12051e072109020a120f02030d110a06050a1803050304021809150c0f04030b150603 64
    0x8144109410341850156003010b0302500a100881c2841c04000c51503800007840038404081500038003d0305280070130802948944102c0341e5100c1c040e014180406200036900c0d991090040026078a000d4403a1418050b20320304941d00c01c04c8503101e071200d02941c10041000ba030403807000e0b401000e80300055560845032000c02840607000e43c07000714241022070300c241142d00d415500000108a40e0526080390346a100c07811005507280204000401c1c0d0261245159100e0301231050f01d01051000da40c0814009480306440c180d9200d00c1c2d810010441d542c0c00200c2d400c056200d404001491041c3c0e206150822107156034a03818408100918202d20602050301540968040710020352552003180c5e010050040c0140800010481d500382d004041c0c005006600440c000c0310800025001503002c0306090b007007264002c4242c0c000803094402d0400703100e43e098010700e400c0f242c0d50070306000b0f0044201d550031942c020b545030032800042c003040d1f00f40071800c00c44601003501c0c0a403442c42e0604a203d006400369 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 785592904 1250 785591654 785591663
    0x501050112050a02090a0b03010e0106090b0409020702030307080315030106060806010c030e1906121406010509190512011d0c06030708090f01051509071e030908040302091608091603 80
    0x1640010810f01284d4111120250002c100401203500e400713000005810034004c03412102c00740b4001043d40b6004603650412120304441d034030710700340c20000c02c1c1d03019410444041741c141c80144911000207038010051482000481e079440780001158007014203413103090340700006111003103060003007590307214540e0300d5056010700b00b909a20496401081c803500501035442d442500422011074407a43c412071041c45103c1c2e610b028000328041009035004c0035420303102d450101e403040140c040c0b41d080c1128040603415804200c01d080c550380d000416003840d03400c0d0360380b4240e940d5020545800340c40070011100b5550390200604114804801180607407101030615024000000b0000307003946800c1111280c698000b0001748601d00b401d881e040c0c00303c44020060391061909000003020b980c410201e01e12120500c2c00c0f241c0c0d911443c5503082d030081000c9501074503a0300c0100008000340e1629a1014020716100c01c4425610340111030003800c03e4005011080c8580020121002008040300142c040d00e410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 785594154 1250 785592904 785592911
    0x504021005132103020f0d080412050d0f0b040608010504080702060913020c070302011115160c02040612030311070f020405060d0615051507080f16150203190501050112 74
    0xc0c111031141515980528011520f480c182d181d200c6030701c1c071030080251107602106d0300a402d4050a54036a000c0d030786403400040094000a01181e20020701c0448200541032046ca4551245102010741c0da205104020b00ca032201d03498441c40c1010300c030703060007414020000c0200b03043c0381e92140000c2c4035140004e0321820011908020036650b5071084690008035510455441c0000c8000503101c5442e4441030b404107600b69008181e003540402c0c01a04d90008131440b15160b83d50030b0f4542002400703000e0304020403038201140401600e803440703090082c040c03400728801403440510b0010b0a5039000311040888400a11060b00016400404103191503411640403c055540c7d00c04a000034101c10000303840d860400c0700c0c803c82410380805032001c2c0c1d00c1c20740d58502d44e5035031803111141c0b1380f08107140101003c03010003505460b41d0100014003d4403145400446c0d0803001c039200d84403500c01c180b00010142e40d0010a024816004030b0200c10026440580bd21096140000103131400d002d052616484585 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 785595404 1250 785594154 785594167
    0x24060a0224061e0603040311070b130e070c03020304030605070201020f1902070509161b05011e05070e180414030a0e270c0a030912031a040504021005 66
    0x74401d1801122025120340704100200c602640c10100c241c03840d9003e0490440c032035400e1100701c0d10354496064040e000a20b9030b205ea907011920395140a00f8030a583c083c000c80481c100034602c0081c40f2003001404145011420042003d04002003d04090240400004040002034010040d94100c940003500000c03140e4900005a001e840341c0e95001004041c0090100095600d0320030501380004c107542103881c45510f0303c040c4400900e0990b0318108480ea4041e194960902c255602543e1001840038a040c103802650307941e0039a916811800c00e10f40800340f07100d500c0c40e901d05c84c4540c40f01303491510501400d40100880c0c5492008848484200305040008041c041c000d102080901070034022a51740d000802e9000b40402e54616040d84a0602744212900c460b08900c10110260b81212042d82d0301c0d220b1042840d19648426110781c00d060716120b10601280780c8003822004e03800c564802207002c06149119640701460410054407a0349080c0030311001d40c8645509820318034007410466a00c14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 785596654 1250 785595404 785595407
    0x30312060e0a0222030c090b0d0503120f13080a080901020c0f03250809100c0c0602060403080703141b090603010f03020a150806190e040308040b24060a 67
    0xc503500000c040c036641100380541101140c0c02826209a00ea0030041c036400704856100e6141c826120250401d1400007040c041e4284982c0400c020303003001021286032461513512030703065030018480c82c28011380001c00c03c4901201d400191b5448101c1004641c0340c0e0382103076a655040e005510042d41082002c07000500c4402c1c007541120041c06051045418030303181803104650702d81c0442550b00d0418122010303540420800030138100410762100d065801d007a6002c06001100c0c00f020756410030011001060004039010b038820b40080c0c6615400b4085502e0306e1704001d0700886004c0c1c09001090701c1d15402802c4408070f04122900109600210005c2d00c12401000041d8094180c1d04d9a002d0740c000000214100c061400b201180d100351076203429036a8130303401340813a403000c41241004034811500180742407405480ca611411503a80c8800c501c0d82d00d802c11840440811901200800c10b17031005e10041c0000401d81c5640040500320680061040c1d00b041039449000c0301106003d000007140b9000e85c103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 785597904 1250 785596654 785596661
    0x31905060f04020a122d0503040b07170d09230a0f1b06030e070807030807110109090e031b0706141b010c05030703140105011d0d0803070203091903050601030312 71
    0x4245c9420701d40b54101a504240f00a040303c040d5051007000c4000d1007000302100000c000e031b100740d0000050350606240400f055107e80c040f1804564040403070760701041366a4580003425800b520306000281d01c16642c681124401d180808a501e910009210002c8014000801c00e154076480070212010b520b40e0303d40141101070125800d0400620080c0105034658958000000610810100d4140982d100c080e81d440d60380e80e0001400300c0200b00031480101d021003520402005c8103142c040c89885e03584140c0703400c946413000001140d400008042102c00700c10190b03041d21030000009003000c10301d07040d8042e00301c4080200c400c1c0307103001c04608502c038007034540c0260030b4000c0380c000244407404440c08001c102d58022503444000c6442c0c0080d905140c110129800c3c141d0f00180c4810500307846218025511803034103130130598403010484481c0300240000020b10f0080080c2d4005546444041e010000501c510010740c000c240c015a00400210b1030001b06941101e40500348000060040c2c00108090b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 785599154 1250 785597904 785597909
    0xf060306051e10061e050c011506180e070c02040b042f0f090d05010e011415040203040206040b0c070f0311010801090e0607030e0a020d0c05031905060f04020a 70
    0x20520700020081802c41c12009040c2e002110141801150b48880c00c142c4a008070340035903c001400f0301030042c1020703490041ca1103414118103041c1d0810171424002c60a5a030480300d209451841d105041094641000e01ca080d00301c407d11800300840c0c2095141807200d0002403010b070410154501c02019034946038003400e802d0380058800e0001c0d9580d4000302d401403220042c11088051030751625000340b00c1090644000d2aa1512054a045410303401c000c8698840d1304143c03015580c55650741d21914003445492b4801381c07100c40d92011442c108403803408131207000312510f014600410070000181c0d6100d00726001d90b00040b031210385548c0070309610340c98003403e03030008490807440300c0c004406e210b0b0340d4404174003070b040036038480c0c0c0d207a83c0311006a02601c01881c00060315500c2030011510300d5009400180266003a54212a6101c0e240d0700040c200c2c1c425072909540d1044410810301c41e13420140314181740d5070f0001111200d4060680e4810740e488400404152005004502241c21503580d050701200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 785600404 1250 785599154 785599163
    0xa110405060d08120f060111030a0f09080303041b06020c0303030a240801020c06131e0302030f120a060b03010b042706140a0905010506040320040e0d0e01020c130f0603 74
    0x49514400000c204e01e82402d4517800c61a0b0959000a117240d0305c00c1580b184919544005181807286101d0180d807079080c010804d4040c032481c2400071880d848100099445a030140d210802d51200c1444000c440b004660000030454001900700c00c519100001180c3d044010003d00107454240c06225103141c104240e94403c41c040f0504000450343c1054000c0d00300000094140c4410382c981400b28861071201440040c000407003607006030041110b10078820160350007401600d1409904401c200d02c50342c0220600782404202100348030008003035224000282c044040c0c05499541040807010b0389009509c07840341e80d4030103440f03001c6805810620900d11200c1410f070601040e900c6101a104007402d6404150107003140700c100003100810350260074121900070300010719103400d41d212940c0f030040c0080e1441e41c030703007091405040944036840342a026206100103050b00c521380e00401007180c1003c0c000103045503c200709200b520703a100c1500d07240d9904045000524140c0150311140074120590001c0d2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 785601654 1250 785600404 785600407
    0x30818060a020d020105060f09010905060f03160807290c01110310091b0801050d03020307020a030b1b0f1602030f07090209030f1f0209030f0f01060e090a110405060d08 74
    0x410715030b0005030f01c00402109070001d100d150f41d04000d0085070302503174182d16489051800100300c0808642e00070740d000724000d06800329400500011900d090103101c10907108100e8444100300e82c420a02c44032010302050340311801c4214910500101a01941c60740000d0860001928400c040c025441500d0010390511034030740b646020700060b00c0c412030610a01d144542400242d112010524205641c10640d580301d24000741d080005001d8101594001107080d440200420750250f42ca10186000962040840b14900e15011621102105840da010752800100384200d04100c180c03002038030100b5000203242e800c540a40d00010345000303411181c8000c40d01a0040229841c000d5070010404a40107604480700f0010104c603441c0d841e9a866400980c034040d503014203444172083e4000744086000182245c45204407032800328107180340d510084540c1c1e0b40d640800c00c003c600d0031100550048803600a40404e0285850f00c20030401e0052a01d0b12071640e42001541c2a62000d03a1605a15005003119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 785602904 1250 785601654 785601667
    0xe06091c0b0f0105270f22050309040c080403211103150a0501210b03030f0c030309070905070e01140d0207032028030903170d1a0a03081806 62
    0x70700b00c0304400c0c06a2400b6000341190442c07103140c502a0350183e0494010007100c0e81d0340b0b40c00e110600f4000900140304588002601000c54400101c035402e00da40940d000e90b41e5041c0340c1c0c003003008903a140070344807041c414654200404a40c00804061040e29420640c020110b014600038000301406000240480000300074883e1001c0d82aa5100e25400141d45107400f0030307100c000644801400c0300f0311002d1045465059522092150800722128102070102d900302032048140c0001504954204506d035440842000103000f01003100d40010711056404000c6410300000c0103004950042d00b0506001702d40700541003418000040300c5019410460440d00c030300140c60001e00c5040300c60030351170300b140060005a80042c0041880301200c1d00c0c0b078004403000c000c13030001c0e1000c000070302500354284250850f0000224400d145440660480a282260f403400505400c204450007180400c1221460031381e40d0b00303661541310350b01d808e0b41d401c0489661103260400d643d000c66802403481d16040000451034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 785604154 1250 785602904 785602921
    0x5091e010e100e0705061806120703060f060507030e19120201090f1202010f091a030609130312020d06031211060c030c120a0f05041202010c0e06091c0b 67
    0x41c0890800c850282d84070000702c034039104181c07110f101e404000760300000000c02c003510b440002000d0410311440250707a0201040300040e89030b08191140b0f10f2001699040050080d8540720308009458400711a00e000780c01d00030001d18a01400400130240300240d09a01c0440d074400340c44007095284090400e5805450300340c0c0c541c0c4050600c07402ca010401030f80380441c040c00300c0101c3c2c0f07003501c100741d0f4040c203803450540046854004103a092800c0c451070400100300701640800000d011300d00c42c0507840c0e0ba400c0580601c01c2d580f030010003403d0f0701007504520740002070b4801b034540008202841c000d1b0700d813000c141c7d411000708102d5100521a03800d5000d07410600344c202410200ca46407210a4812903511210165071a01c021180d03100e80b07040410005e40a41300c10003c094001c00c1907000080c2035003600f900e0004560017074505451142103605541c4009909010340d030010002441c0c0600b01c00340c0400400c40b0380c0203032191544504070145403910b4141c00041103103195608024547c0550805002e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 785605404 1250 785604154 785604161
    0xc060306090c050c2503051c0e0f03060703020c161d0f100509040309080307061505010203040303090b03090a0203100b1c0210080a11070c15081905091e01 68
    0x144000c12810002e45100450250050790105042100034000102d0a04405034000342c02000b58070034144c9140b0044040785c4100f1440c07226070000d90201d041c00c0f1074084043d105090104240b4444c140662101e289a1000701c1d0b0f01c0c1d000b5400c0d050158a40f520011f0030360602d10046a04c1d110301c0450003000501042c40c0100b80b04298114150502981702c1c0e4035501c003601012100700510310305c0394908015a05008a1040e4400d000e886d0040401e52101d5940d401c5601040080d20016203d8251080d9003001d01086002044240006c44c503013883d558014250b40994441d05003511030200001c5d102c1001484030301000c1e035004040d140f02c6002c010003031000b0711106c1d1946015030350b01e124241b10000840800c0d40b1640d0010586d12201c2c6481104031170510000700540032081d1140e004041107440da00c084d000309842107012425150a0143c0300c145089428440070411031031009120b40c04030a03003440c2850810032038020070039540343e01c562450328918003891000b6505c9107000408000040d0b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 785606654 1250 785605404 785605409
    0x3121914040c09060608191805030c1506151c02130f05091e090a150915060f1509240806040c0503180c0d1202071208030103110402070c060306 63
    0x200c802d0302442c0c03564000002c035105402000040380e4040c0101e40c060300200d036884c030b40420840c03000c0b4408406c821034800c8524011700407030b11a4408a10b0a0340c0c0841806132031904400c014030810f00f0324005000404491161720302d000702d0003000840d500001d4108840d513404103000e07002550f07140c0100c011b08048090728400e500102805880c0170400c0d240c40041540500b12400c11608800d0450705803001e0030801400c030844c280728203415000002c0b00c941450b0041c40c000f103c0000d02e0101410003492081d8031001e82640399241c900c0034451100e0b280c108605880f10b0030030f1100000d114040a8424106030303042072400902603049002c110704140c2d65245000a84e981d100001d4a6010601003505c419030004008208240000b440c2c01081c1c5110541400718442242e80c001e040502080b40f040340305d58142c072184d0000408046041d010040f10005080b41111054003510507291020344d800103010003004207a80607807858050791960141d541042c2c00000008540f03a49480240046c412403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 785607904 1250 785606654 785606663
    0x1a010f03110c0319030c021e10091203150b0a11030f030903041809020d02120a0b0901060e0906090307030e0d051603053304170c2506020312191404 65
    0xb20200c213106803082c01540040741843e001088044d0800e10220041c0c10044003001142c8074502951f00d900b80b160280b8030301203002d4241c04a0702c0d584500e0040540d51184200c03610300030218420031404e4489411251020014642401d03d60480d904450452190036001c0785000400300a01c52030000200080c01115a000050a0445403200c0a5001d603901120040c5d4801e0368140c4000243c1041501c9068549441040d03d626a20b1a42c41070040c05054500c890503a41d54441030140c0b08481104a40003900000106910302e04107441d1a9030340301d2103070300a0811520702d03501c0382c26407901c200210001e50300509440c490152048a040c100240f440f0030742c0c8510501700020f5030300c9020741002d40040d074110074029605880d0700d00740900040207001181d010341380c0c1c145c040b84030780c9a0028001c0c8180085c06400f01400001216011540aa11030002d2903410b150800c02113400104885842c7e01005003200316075034001c5910421110361074000891801c04c02c40910709403d2519103407003a40308 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 785609154 1250 785607904 785607937
    0x909090607201e0106080d05070c0503060609131a1e0105060c100b031006170f3c01020a120608030a0903021c02150409050a1a010f03110c03 62
    0x824010000b4280310707000c0400c86030021070210f80701114030803005044011040012134920307501c0076100d207070100c0141303000700052022415a08128a072040c400c002d00003100105910f00b0b00d00000f0300130b044081c00d804030945003000108100f004181071f01e401c0c00d420444c030b0300d0ba620b000182c05c1d40c01e0049075442e0700c9240c0644000310f51440c20b482552844421710000f0f044034803050541c00014465035560a03898429001030681c1ca0445001d4540500b010005030038104035020002c614007202c4480020981e04120f450000751443d4080e500269181c0d042810b080d5080f0744c0c0300320184c0050a41c81c065035400082c0022005800003440b4202030b03001001003025665a5071145d80328000d075000080001c1d0004410030251070510008941400042200403d11802e54005010022a80c0c450100c1d02c0010508200c80c2e941d9106003544288411070a00910000c48003035404c0c0c011403540c240c103000030342030351900841c03282c0d20400c0000007200c2e05590340d1a4004545580f0b400004100b80902c52 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 785610404 1250 785609154 785609177
    0x901030c080907050613050a06050a0810140907050904092105120a15090e06040201140702030607050a0203091315150912020d05061009060906060c020d0302030909090607 75
    0x101e0303914180b0401c04103000d0060310341004100320080c1e01001c0003045501070302c01c01103140da4807030480030001c009640b43c0c0740d62003483d1034018101008c02050345171200803081c81000b25200c00010540f020b60f08491580481e9180c0d2415109801081c04580c0c0144c5001ca2010400a40612000740c0100c440d580305082d40c9001c400300d82600c03c174001070908060007800314150880e036821450a8025000d42d60b0741ca0381d112480c0c8001c503401c3c2c845083c20f41c1e00c024240025940c02c100d050764a02540c0e0911032a00800b41c0100e599110064400e1b800c1050001b0281e081c50301c21f0013540c4c0441801014001566000b000100c0074144450700d07000201c94444000451a40f8891200f02c040070782c0d2511040980340210801d6000c0d504881a81c01060402c4503800141050140c2445140300c0e052800e076050421407043c00b100c50315040703003550918003441407007015041140401003e504031600b205180c41c61500302d0550084104040d008044001801041200032a181341304110039500d44a5074803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 785611510 1106 785610404 785610407
    0x6250f17071e050c01180f0801060302040b030109020d0b0408040b03010602010c0905011b060209040608011517070f050f01020a1e06150e07081b03010b0901030c 71
    0x1054400c0005910100c00108220580c2d4124841540e07240c55881e55184200c6050082a104c2040c030f5207008492903018126240580030b02e596140c2a0601800039400b00b00d10490520600d4071550405104260415030000c2040048041c1c2e038580071240b840142040c0c860080411010030101da5150046008000e29400043c9080c3d40440060506269411150401000901c0507801c0e400c0e900035420640e07040640180e81d515950b00040003400f55500400d80795090440c045812001c01a01204844d4a44041130f0582080b18202da2512820300441150f910301007420300c00c074141160070040c16001801200c10074003083e1903101100e44080502c00d1001a20b048410401a00b80960140c07845c411109030121030500b464a0440d04c002070241c0308000b40403001500030150160300d0042405030b20300559481d46c461701c8a00c0140c0c000000d540c042418407039100c070f565 = true := by decide +kernel

theorem cover : BRFrame.Cov 785431654 785611510 := by
  have h0 := BRFrame.cov_init 785431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 785431654 ≤ n) (h2 : n < 785611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
