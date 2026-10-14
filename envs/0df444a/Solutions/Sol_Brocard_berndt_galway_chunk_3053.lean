-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:57.49822+00:00
-- url     : https://prove2.me/submissions/3ccd531b-9782-459d-a7ed-2700465783bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 548920863 ≤ n < 549100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 548922113 1250 548920863 548920877
    0x50f06040f2c030405030616300b0f0418110a1d0a0f02072603130303091b060c0b0702031c02070201030605030111040504180f17130b0703030c 63
    0xb058104207441400803a00040003142d040030458001d0800807103000d00406000c0d141207090034540c44d2140309109030340e00049146804c03050480c0b80e03c0c03030903021031410000146c2040c500b0701c0441c1b4020300504104903003060b654801e9180300d417540e000342446001a03600c02580c0c7c00041c1002d540480340710064510850714280308110003a0000c01803486041540c0103944a5180c0c5041b4600400400c9850008180041400c8052201010b030703036406e540c81000328800d404503c41c040c01e12444101c070075016010224000f080864403d5004484040c4142640b0540f00035a0400388940748080e44032a001a10060540003001507480f081034001c40907000031030900240c00410418610b21124207100980d000c100c0d0000c2d03a109400c560002c00d0050f00800c08034003202c500200d20307070260007107902072801c250140d0400034107819a0542142c00000200711400c2da0380d0f508640140703220f800c074091034040c8103100c100117440c0c0d00c130002000700440300c2c0d40da5000c0780340107000c1c2e940088030041031180c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 548923363 1250 548922113 548922131
    0x1080a03080c1b0607030608250603230a0c1101150312121d010c0c0206030f04020112050f070f020f06011a040803041205071203050a050d0906050f06040f 68
    0x744140c0d0800301c0030140b2520b40390780b450203180750480070000b80c1c0c0354400c10040c45445038140d4051015545034030240c070100c60344082c6094010b8038100c0030000221080000b000a64881da0203450407101480c4030034414541a0540c100c4440199118101e042e0b4552111107800e81000005440042c403400a102200806140c0601c000381b500c80076120441300c26070900086e11a46982e14800c540e4181000807601e00743c04005880c407040442c40c0190700e000041ea045a0280400340c0b25164020052403640e692085032400c64140540224188510f103110f41004407114081d1510030b190101c81507000e4a890307400104180010401c1c082990084914400c0318800491128195400709802c550740314003400e850300c464481c962102409000c0400c0c08910755000c94a4521418014003c660506031034001110302c800000a000f0040f03482005061075060050018004a050506c0001052100d54840006884049405040b090015002c001c8107140c80d2040a54900c4200010403030859 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 548924613 1250 548923363 548923367
    0x14160804080601080a0f0b100b03090c01020d090302030709181401020c0601050a03150c20060907050a06022e1a01031409070b0d061a031014090103110d080f1201080a03 74
    0x1041c000c050812000580008c44510301600d20300c00802110305000c0d564034144001e0340c0c850780202d40300c41c01406941d041080061144502c0016290003c0151800c00d2610341e400780140382002445072a00f01100a0002148054115070020312000c00050b0351004074a20b55424081e058202c10300c540c0c0f0740b00741030001c64082091040940d4540100041c175240800041d500355552000122259642d0000042407203008150907001d0740d12101210f031110307100c01c04c00134130b41c1440c007070341c401a40013409210b079130702e14100410300c4034102da8103111180314030072900d9050310600e003000e0b81d800c00c144280c02c0722942d040c451801c500b40a070402c000c040c10711001168488101d880750070801034000c9050481c8012540c4214010f00f0442200000d44080e22060007941c4c1080710440300c410352415001030b008082e0301c0704132200c0c178005007180f02e20384c256a9441389035001010310704d40229000e83c1d10340024044400078a0a0000107115030380f92550301e030120540c1070058102502640001c40d05e02c00080e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 548925863 1250 548924613 548924633
    0xb06060301060e270c040905090c01080723030c0406080604090213090327080f1c120e07091e0b030d03091a011d1f0614160804080601080a 61
    0x4030441e824000207400307060450f030b25510344e56040e050341120b4003404502c0081d08000c20480d138641000340081c0e510b10f0301807902da01c09003010301d0110304642e001410306889440145582c0700342100c014910f1141c0480340072290805c988260b9040000141802495000722031075911400458080c0055030b40c90740491440c000d2040301002e055103d034129000c05019101090480c0701c0e07212408680a10459140ca500304107102d490b501c2e002e00101d4005141000c1030150b0780000101034900008800e601c2151591410303503240d200c06950341c41c0214040028040c94004218040c00031800c03201c46020b410b04a0b02c0c190494501c54030341034801c5503985000c102f0344c07030308983c074140020200942e09200c1c00d0210041203030680b400510001050320b441c0401c1c2003000340c0b41d000e041d190301d40c1c48030100034000035003c1030046804c0100000304500c51195825455442e001942c0505110800c0741d082d1011464000c101c1e41c400000c40c0c02c3c000070f90200023113401005030b0001803c0c1c0001d2600c071a0174103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 548927113 1250 548925863 548925887
    0x5030c0d030305060307030f05030924091509060a0810170606060703031103040501451e11030607020c01080c0f04050a061107060816110a02060a0c0b0606030106 71
    0x10548840025a44d5038007031007000015a080300a2140d17203c0f41e882c08540b40e0348688038882c400d10041600011400002020101c04140d28001615166000c001c01100b08501754504002d01c40802c2007155940b0384a010b0400e001081c0c8480304036003840c43c00200c49602036001101d81e010202401c0240308000108613800c00001d84590350b4504203420b00b01c014180038192061007030700000c2800100130f8154022175001454100706030104805c40740b1144540e00f03494211110003005c03d0034002c800c4080c1e41c41a405031041c03211000e0b078069410010f0b02c00d600042e082c3c60840284039041c1c030508040c4205940030b144c510141560504070300000c0d20802c1d02421041c0c06d140041058284400891300300d40c0603001c001d0800d540581d603420018290440074035039908034042c1200028440b80140b110034060b103001030300440000680710040740c042013034002d2840030f03108456981c800f40c2c892200920407418a03542e01000000141000c0d420303000c002d004503006000810042140380d50010f1a8205 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 548928363 1250 548927113 548927117
    0x901050606091c02150a1107060c080307120f1a0a06090e07021f0204051e0a0506130f030b09072102040504260d180c030620030a05040b0105030c0d03 66
    0x21046081c88081c803d85070030f0800a4226951030011604030f0000c001a10718041700c0d03618180c6260780d000105486401c40d00c02d480105107000b180900040000b0b02030341d03000303141d8905078a240302968100002d0340c2e0f03661040080c071a03441410440300d22840c42009522181034a000800034a0403030010543d0105104030a41e490f0351002085802e4401c0c40007a00500a10044c2103881c0c111006143c000c2d809403041911030240040f00070554500c04440403030f8904d004289a43d200d141c8014481954031048203840107051981c000308015050048a4026602690000d4440d00c0c1c8007110600c0c202c540d8101e1002c503114a00c941c86524142850840c0704ca07419103005c0760300d0725580f84c4103c20304c5039960300901c82412040342148007203403107010300090385200c003040c008048800c61180054000a0018100391092903051002c100f29810a101c85101490703050b44090070010640c16907001554221003d640b180c041c070042c007580c1000343d40944011405440582d2400001892040301c0d610000c017 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 548929613 1250 548928363 548928379
    0x6022d030126030c06070e0409051002030702010212010306062c04030c080909330108060d05070b0d0501050405071b1119030501021c05010f1703040308070614090105060609 76
    0xb81805960703840d602c03046403060459480e2107410038041c0c3c0700d03401107a84c800011903000c05240c142c81c0c1070040703420b080c1d0004064101c0d00007000284001e9031009100744150764003040b0000741d1541580500d4000c500410001901905014007942040072240407141c0c90382e04409040310031100b16071015041030340340c10618518045482c10401341d018048070168007580190030011b540840640310210005d00d4170030321800da580803aa00c45c0780c009815400380010541000900b0324204614a00e003214000d00840310401e5842d800443c05501c40181840d1007511900104000c2c206130151540141c15030503b40d0b0b521013800101e503075a01503030f0400340207503040c82010070070b6440c1c101c000c0c0c5802d04401d0369118240d44a007841400b030743c400c08007002c07824940c150740c0110344280c0c881c10341070714503019500807001e207050240d10b10014180c007030f1030242c04100800000211740b04000c11140344120b4010a071144148105c5900e120b0007440b080560b4180001c00c6007e9491000319020300740c00b160602 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 548930863 1250 548929613 548929649
    0x1938030c0f03030406180510020303040302010c020f0a020105130905070c052103070302030a0b030615030715140304050102090306160f080708180f010e15011a040b0319060306022d0301 81
    0x20350341b043ca901254200342e402c580c2e01066907011000b14030460181c1c000780466518181c00b2684c40502140d041c001c2e420415407400198422001002003101000001d803e140d00e4840003404c940096845030003040303469294504010302403010076500c0c1c0e264442032030100701441d078001141c1b0000740000704060b40000028046511580141840740001d0115440303817509420201d0045090000e9511034031900c02c002605518608508811903c00e6845001c2c03104030030342c104421b400240048400d0354080c004e05e04562410040d1078170551120381c81c848a07030b0f092040640440c5c0d0341088001040280303400c000f84147c0211210390003400d020048901c0300c0380080a03074140801d80d9a025615407e048003920980c40005001c01c910b019120250040d90b0f0703800d001c614800561070300c4100d00e041400100001010320000e5640580000c05292803c00c0c0e43c040c007070481364070f40c00868600380e001c01e104082402c03555468180c1c00180e80c0359507000c40003020b0030f90540414411602e07218040c0c034041e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 548932113 1250 548930863 548930897
    0xa0309030c0f0501061406030c090f010c05150618091b03012003010305010c08010e060f0d0f140c0f0d0215041a0706050a02031938030c0f03030406 65
    0x40590b8100c260780c81d99020724503105000e4901803044409101d19401c404a003440c250701101d0141d41581e048524040c000c0050082e4145400c09031418804e64a40c400081a030911203c0c8201d25140c0100d03103e071a020040081054086210794001d0f81c203c400c020072550005007103c8800061500741d8040841040040e0151010030701d100110600c0c1c82c6400d241c81406d034041c40c140c1c1d22900081c4000c403103100080b5451a003d104e00002c0010100100c0d02c1401c008800c60307009072001d40741d6810740750700303840d1b0750803c0400340402c0360801615542c019408009000625545000702d92101c0c10a070304400142d102c1c07018110203485034411402c0030b00d0003002c1345d04540051038200029202c081c1c1540521400d904070031000c1d07034824140b50020759140c0551088910900405414403160319610020078000c0415105480941c4194158200b4074440340b5014804c07004440c01c618041e00070b06080c5410b214401e04054000c600442c0704411550700070003551b095035094a040c100c640865010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 548933363 1250 548932113 548932127
    0x17041202091b0c0a020307241103070c06020d110705150f12010312030b01080c03160306090f06031713151e080609070c0b0a0b182e0b0a030903 63
    0x6101e0b00781c5000200d0761a11000421444c05050084064801d2643e4503014060350000c0801d8000203441c00452450030903000c1d100f010054008403044a04107880b0b40c0ea12000f8000b5500038a0141c2d220038201161107a001002c256074100384009002a54545004a0480c0c0311442c0300092102e000b1a10342180c090340c1c000c2c1d420742084202c0725200d5580d641009a0809003421007000028201705801603036502030b100181c0103580021007180b840d9a1130b102001c80c0c0302825442c00401da00c0390800116048140248100701001c00c00c002180c42c51407528480100c01412100c1400d8070510003502c09081d2034002c034040303804082d5507403801010b410b000c8505044520561050038546644200010351210082e849100142c52501c800e8440c48400d07034601d040340300002c1014180c0030000764006100c1e0020780f030490000c1d10079200b109160000000121045aa000900c1d82c8080443c00c46000c05000000d041c400450000c00a03040400350005031203000b000a05054960100e2001c1610400c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 548934613 1250 548933363 548933401
    0x5070915182a18060e190602060406090203030d09060f0b04290109080d083301140f04031407051005031b2814040e0105090402011701121704120209 65
    0x22000d44515184c83d0043c1a884509945c1401113103040c00c07080c403186c1d02120000c142e40e07aa40045c400d43d50340e40d07500b0025201880c030403070b0940020b10010000c01c109000707206400c1c1c8101e0700070501d501031504441c100d032221456940f00301c7c105a58550b101140200c28149241e8201005100701403080c01030781d55101640c04016240310f140c3c0c06540c0039034813000c241d01130a000030360b00c0e04414071202c5540d90000d0040fa440840340f4402d2070b503030003580901041940041d4458405042c01022000e50500d50895401600c2c81e50285003100704601060000b04081c020403500c0110400044000a146002c0144400d481c1c0301c0300e1321030700f4640c983c02c01600d8540280c0c0700c1e210f0302100c00c0c0d441c034030a0000b032403611408103180c0005988611010740944081c1e68012810200301d80c070300400c2242c1180b02500507814040302c041011444c141085009018103102c2c107010000007018500f030f40a0704003105c1d040e1016407040c003050042c9003c0b0042003215640403240c4490b151140c1090000600030702da = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 548935863 1250 548934613 548934647
    0x2180d1e05010e0601090b0306071817150604020703170a02091003020a0305060a18110d090b1005090f01030605060310020c0a0c090c0503060d05070915182a 69
    0x80c8400300300d4150400b840400300e450a80e00580d907241c0c10041910a018001680754021400003004030b8451001c2002044000007118241070b0384082810200c0318180a03182c054101414101c404014180719070381140040e0b030110702e860807175140181094130380c0c0c10340a005c62060001c01c4215603681c05442d0b6110b40209680c0c00000701450240084d40320302d00c01d8001c81e08090000c0c1291401c0c83c1c100c0300311a4600e9951001c2042c02803610020044007070038460203001401041e010380b50300d01c0b9090348144070744d10707021850401d200c0702d11003000d5690005110700e4040341081240c00c4c031003400c241100d601680c00310b401c1d1a100c0c0001c3c00c0640d4060000d95951000c10034018031640025110383c028000c0f40c210350000e80b205103102c16182052803035400b182e810400b05609062071000c4c0101903014100b0348900c6a1036495400c26500c6110360002e041910031800c1c42881c01030036101d030b07892980c200704000192401c1070398417001d100300110b0219205c400040d80640c0e170080e5000f40207070b8410303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 548937113 1250 548935863 548935913
    0x606060a140a0309120201050c030610090b04090507110303040804050913020d15060509240d05010e060609060103090302060a020a030605130e010507021923010c020f0f0102180d 78
    0x2030364000f4001e001074a804d484411021548055060040c07207110701800d42245160724590b905401e0000c01c000316540300e02041080000003601801ca50050409070903045030100d030b50f00f00050020b00624050f030040149400400920002420141c104d9048840c02d48800340d0756a14007410b00c140c070740a2880a500005000998001c0040300140340202c2501907108004e801c1d07c0d40c1c14030036407030300445456926990a944050022240d0135590315000e130014003856105496075190380c20740f2030303c0c08196105e0740100b0a02c100743c60302d1819030368005400c0ca000c10000da00350710001d41c1c2d00e001800c1c4600301c070b03800265401c0740740c8a42c03c507074090800074041d45d82080c82c040c50780008000303050101c00345502c0e0002055000b8400b1900701031807811400303208080841511005804a0010b41e40c04031241800000c0318403500a0182518017040c5d80c025181180e9104591401e080441038916181d900c10807a0618080c44840c03105243c0800761034240e0080c0061138a4961140214001003c203107074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 548938363 1250 548937113 548937127
    0x5011d120d230409020304020a051221032a0412050a050d0e031f02132d1503240e190507050301050904050106170c010215090606060a14 60
    0x300040030140d8016640d02c28180c6000d03003004440004024861800034401003204004560050300699080ba0008214410341684e40e40000d4480505002c90310312500b01844010381900c00f61341a080440d000c004103403940c6000105040200d00303060440b0310381d40001d458800070307020030341c20b4901a062026042c1e450010508046941d0408a401180c052013208950703c0d2180c440c012122079004041e0061080d040e50300000c2c101c1c0e4082004a1100c19824800714008000380c1d02d0450042c904070040f00d00384940101c9001c01540700007045516011071060800c10300040c0034600e60440c949160018103000101c000715003000d0f1240c860300101c2c0480030302045280540c41d00c40d01410f0001c1d404d0f8000881004034500b43d4204440c082d01080c0c0034001009141040012198410311450002820303035207501610980b079014500040b03161340800300c85111540c04200b1134100300d1001d40b40380c14520700b140070b00740e440c4401010a4000d134000300d0944103c601650f034074103070310002500180c2c580d80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 548939613 1250 548938363 548938399
    0x9120203120a020c0304031502090415050906100210110403051501060906020f0601030b0606070b04080306040f020315150c0601180b0607020901060516020d080a091e05011d 76
    0x1e059200a010a07001003484540716108036000c408058000d141400e1940e15901054601c61405c5400c0940070005510196140e10507514846e03008050910060700b064103100c03600d00b0040c841d43c0529001c40000d8022500010102d40000183d400442c84103260541c142480c0110303480208140304054401c240801d280da51103050742e160781d4a1441d40c0d0342d10b00080f0b0380d603031700580c0b840c1580d00040b0041c800f140c1480e60035580580c0107495189418015540c541d8241c50440b000e450094010040c00301c24507250050f120b001d004060154114200880406a599070103801140f08141040c0c04101e050700340c4e01600c50700410784060310459a5114001d4241070400810001c04030305e020040a22440c003d403d841c00b481e0082c00f02d80342a801e00030b094481303030300c402c1890420b9900c0090a40042c0d54803041000c99900c175107481c5880d000c0040c0041c01d084219040314254440703881e24400c01040180181040306c00910300404d1001c101c200000c0911411446070703421200c0c01c245106128 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 548940863 1250 548939613 548939617
    0x210c0607080910020303040b270f0c0a0504061404050a1e0e0c0105070302061303090515070b06100f0c020a030b011410090b0906070501141f091103061309120203 71
    0x2003015101e0700280381d0741034000c80e1241b0040303800900000c8500d002c168540301c0d030f0303004558048100010011012104448916101d0031076200003aa40c4860901411414440c41e400000d00b0196800d01519040c602c502c1c0d40e5411031039503240110354030310000d01d81900a070407982201000c007480300d901794111111100a40111103690025101d1000d030b044155110303134100c400054165000c0d03c03642d114040180b542c0c0014100c1982000007035480030500d940d40010a07680d403404100c0b00c2d661010b41e8074210105c1c0758020030151003006012410412a60040d030000d508103150f05d020030940c00948001000b80d00306420150400e240342e8000300306c9800c0042c601081e40001c4440700080d1076400f504540d900c0d2580900c9161020500030900c05050020103040c04d117204000200d4107031860000c01e072454500b1511420aa0440321250824240c00b01800014005418042c8a801400030b481d003450b220240c10306014400500507110b55001903072103004507a9001107013003c0044185402540c0c0c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 548942113 1250 548940863 548940877
    0x70c0b07031b020a09051008010e070e09120901050304211706030c01021e010207171309020903060408030c070b040803072c1512070c20210c060708 65
    0x202c1e120502080040c00010840d81c041d40e030060003405007500b85050040507040c01b42246d03400250309403020820107400c2c05034015070811500207028007848c003401d00072840c0f409088541c168000c042442000150f010440d030607100e0a00300650b40c2e407070705d282480415405d00c0003003000c2c05240001a8805910846e94002c0900780500040f90b078070341501701600c07240860040ca02580c0688001c2d400807412285e04c000601d50400010300b4a00d4546649401411100c4045844100010364000200380c81c07045e18050102c0c14011400c00c00d110001c43e640300d0000c1c001070300094010000031806041c160407208010b40c013031420009800c0a18001600e504191000740c0850030b031482c031001245185401c201d601c103c01005940070110780040c4025011a002d8040e07104208100c01041c6540c40c440d89809032080b552008000c500a04050303611800c02c001c1e0507002080400809600e503144800c07a02943c20800c0026507001c000700c1c000b803a000ea84800150419004a440c2050281d0000a0000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 548943363 1250 548942113 548942117
    0x30316092621040603050c191101020c030d090b101505071110020c0111030a08041211060112030f0509030a11060c0709090b01060201060305030a03020a140309011b050a02100b0402070c0b0703 84
    0x4203498903540400307e4000c1060210f000d0000d209441a02d034868003011482480c100001450007005c141100d05540c0221a200002c503140c5071110200107d1480b20340c2d018a02c000f00451080c01c140c201c00c4982e07143c1c940b050400c00f020501c1002d016100e400c00e001004020107500740b54041007030181d02e0b032043d11025404106c50040c540500c000210032140c0300c00a0390340b28000ca582daa91703480c030240c001d81006002c03c0a10300b021100428100002800f0305000e9040c003088800f1071030028070f8035a5044200302044400e21008105440000b048800e00c0d034400055442c0018500104080c3c0c05100744500ba50b10403c24006110f24240d441401518000c80d10b1100b281e0700e0b842c06074242c0304541f000600301d5204006a8200d180300394050041c191652a2180c12480716601000040c0c0007070360380c801d17165035858003c49000c00116207009500c5080c10414107140364050301030340300d4604c48000c3d0201c0f501c07000c004c2415501d0303a0403569215480314810780f402d40c44040051441e01300200840c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 548944613 1250 548943363 548943371
    0x70f08010b1009180f020904090b09012307050702240706110a050f16021003020306181b0c07081b0907030203150d020102030705010905030316092621040603 69
    0x820b200312a10801c0da902c41c90a44c085121200d2510002c181104031784003550790074040082c5a6449005114005000e01c5da11025420181103560842c0e01c041c02081c04000b80801c00f142052031000c0c000c1d80a001810140d8079190140045000703215640c02081100030660a80c00f6138142032405440f069000301c0702000fa06079445000c0d140d81c840c071100e5a02203002800341484001500000b03010240c040000442100f900368081141010340307401c0c0c8000329401000300451350518181c91110f4001e03803130001035181804486100c003d1505a4100d00c4408001a1102c0c049000c04c070341d90003800700710122908007515003072103160114655449807003450841c0100f44418440d001b070b81d002d105d038020b0410741c00c0390307043c1042441000603100300e0543c00f0078001a000f151080c4500c01d4a140a000995903903c2c22800001150b00c018160000b0b2007507008050203040c40400891182d401c2e0a140c0b0506500180c3c01507141c0882420020010320394035403040440034158001e001100c1d1a920f0a01c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 548945863 1250 548944613 548944639
    0x10c0f1106010e180a0605010609030b0c090109050f0301022106040e07152006130b06040212040f02030703020a0603060303021c170712020d0213090510031103070f08010b 75
    0x351914000e03c203000c403811051000c10420810f07200c641c28200d90760421100001d0990b079403181039030000d034482e0b00030440b03c6d0010030070b029400304c0465009003801c400900d480926000a840040b840c040d0b140540c10b040707141c908580b42581100c0c0d011514020003071781c0390010004008489021603446016509064520507900000620b510039604030031480c11104001134000c550303e24200604c8a40300300d80724041d10800400340a254018201c1d50030383c1c4000b4900d403c007048405000750019000368410018038000c001010102600650712801d400609005800002d26046944e00040d51044007100b0000710650036074010401c2702d100750240e80c6088101075500001a02c15080e02d4041400c4403000d4010a030310400e6140d00c00d209081c110300003011900000100e80104008020003940080d03a4254064503550903002004114024841d034501042402410310781341c40010b0600c4003402c0704110969040c00304401034007040306200c260b180c0c0c0c0d6614501034032400d42400e000349070503000300c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 548947113 1250 548945863 548945897
    0xd0c06180b1f050102190305130801020a090807120201030905010b1f09050d0b010501230f09040f2c0109050303100603051e010b0c0a020418200a090c11010c0f 70
    0x450840d07605030040c0c07010b1960240000e41c1b01e0304240040742040401c000e10303903000c200310600f02c2c05461701c00300040c1c880b2b00b04500500a0580743e0040d40325a445840100005201100000041c55080c0782c04030700c20300c0d68a4502c5c007411407000000c0e071120716440000690a824458820300c80115640d82d144203554800740044d800101c400981048031007401802554002c01038180604a03000d003143e0310002c40001e02d00d00d40c01c60459101000d0001900514518007805108130010005a081103014460003900d564140054446511000072980f1a0424542075200042054109041d695039140c418944100d074401401144086444c01d0b000c542d4428400300103021040040c140c21003035900341010b11100d80c00c00c6d0781112680c45039441200041c2c81d20b0044004411b0310103c4805208094545a1005502481c04507075000c1e198006158607594401c5180440700780c89000180741c0401a8201c40600099031684c1d80b130b43c00c01c5001e002041c3e000801441180c481d54615010b087c01e6216 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 548948363 1250 548947113 548947171
    0x6170604031701050a1a0c011e11090303030105010f09090606051b010c0e0f1507050d230d02070606031a16020c06030105091314060601030c110d0c06180b 68
    0x713668210344450350030310070201c030b5603100b02a801d418540242841d1401484030b0a5440c081c0c000044041070000741004401c680c0152025076200d0003a260501141c07030046075490105102e0581000886440c0c01d42680c01401a0405001e401400b07101c11034843c130001d8456400700c0003a5901034001d104100003c0010700c200395000d800b564480300f180d0100004c1001103461140000c1d8091a841d4900c50458541401071513014400c40c00741c003040b0b120880142c150307044c03c0710000000d4508486101c116002c40120740041741c020f4001a2242e03141e08000b8001c01180d04018000c2c200e00c12001d1b401c14400c035203503100d0044000265024030b035040c0b04985603414040306a4002e58148010f1066203844000f090f44450034084904d0407003241e40310081d10458094150050f60000000d00880d56854003503007000c0f82441c140656000c01e4400081e95400d070350001c1c04200078070210304004010303554009007601000c5142411405d0b01c64104161260815182c2d5566907007001c186403407180038010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 548949613 1250 548948363 548948369
    0x90603151a090a1e15150801030b0c0f180f1e040506030307060213030b090604030c03030e2a0f09010f050d15051003050f0f0d030f06170604031701 65
    0x5018001e41815500740b0010140240101202988449001092261003603901c44640741c1035201007214010b44140382011034480c4c0028240c4010084001e80780c607000b104441c1100c5e070104904100341d4950710050042c0c001c02e003e903100c0c000700051101032007548141c0310f40b100504440c42c15a20301103100700525428102c01041001c0900c540c800ea091a0550100e64011800303000d80c0d24001080d62404201da0009000304013000e1080400e00500c002c100901760f120034018002c0501d070415403030141883c8190a8024101611140e049503a40c0081c41500700442e049034984040d80281941e00300e03c1c21680031581c0c015060b14000c85000d1420104160403180e9400b61140850708101c10301040c18040300c41034489101202f040b280b102220b1250610a10a41348041c410354210f14085003070202c2d07010072952071b40c01912050602c4401042d44481b07541703581070000c0c91003035004010002d00703c00d51011005040460000710390758404100948a90b100340d40d007490070000c03889a500101001c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 548950863 1250 548949613 548949641
    0xe060906070c0201020c1512090c01020c0d020f1819061410140313030f0203093109051c0f050d0b010311070f020126040f0204020705060109060315 65
    0x600440c1d00a402600707080401401072040e1280d0450b1000420030310520742c5024142c01800050120303000300c21051454205102001400d058000e42000035640d40d01c0c5400c80c1c0c418009000304504642d503840e00e0b0310740d021001d032030002082c074194151980008102d0b21442c1003004103041c800c0c21440c622440043d05c82148050f118241c20ba028801f0441410300400180300c4e40c2c1031040d4002e41c04401941c882c0e10101c100320201030003440d00030001b54000018500355400ac3c040c1d03641c030765201507010b880d080b902c10301c8c0340d0010f8044418442459091045008407031800e04088140400410340c1710704a07400303c0308041c2d1480f41c2c0700d080710405401c103900d400080040c003c1d400c1d50001600104981281494045010b640c0e01042c52960f9004840c12a0452900170043c0c0071560440440003000010f41d0810203000ca20f944030704c083d034038001c0004041300b95000c01c01003196250350684206a4200049032010342c0c680314981e000b46001d01003542e009030030502d13440c17015126014a02026a0b01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 548952113 1250 548950863 548950873
    0xb070f05030a0c05040e0c1809010501050d09060b131418030708030702070b220e060a0302120a0821090115051e1c0311010b010206070503070c06060b0901030e0609 72
    0x1039075000c0c00525001c40d003d41008010840000c0090030740c46601e010348121f00701c403aa908231614407480c8035490a080346000c2d030280790040203260380000030345078482d002400218030b460446c90110010904111000e500900c940c0c006140c40d10980c0c440a8290b00503e1451403580ba500441c451340450b40d11400c00603882007000f440010b2445d800345422010500444010342e86580046081c2d4000301e0310400b8032041c0740c0106602c10b0b0300c1c6072000c0080aa24001409600782079021541544550002a008481c5c40404034030303080302002102a025080060b80d41c4400c480c1040c0740d004400e001044a0031030058020071604103041c4650300c2007050101c40f44645170b00d010f080c4811944502d02c0480507200f40072890541d6207510140040e003084600c0300055161151402400003044e420a92602d40e03d0001c030b180c00d5980000340c40390003401c9d41c1002602ca6941c0c510455113401c0419004242e1820048000b91034540781000d0425008240c0b024003085501d500340c180c0c0e66204585401080d401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 548953363 1250 548952113 548952121
    0xb0f041406010c06060b04030b0708060a081917030c04050324060d0302160306050702010e011a01180807031a060316050f03280303180803010b03100306180b070f0503 73
    0x15055500c2051013000045007440c1d940d040600c1d1030700298819992078a800c000c000310301e680000303210b07801001150744012103420010074560f110202000c2aa03403e48460004041c0f0100c598010004408202d05640e40e1400d0b220301181604a8460140a8800d071241e04183d00114860042c5d90400034410648550780c90b010000242da403046c00368203500400d102c1c4c020401c400055480078500810001c649800c1804009003100e1031152000110303490054000380403c03c01c10740c143c1c1070100f41f903c000d480151800388640382c5803d0b8007040592181400c00000c2141e401410082a58079031036414066079440c06158030340d07104d4a406407900030741080500c9685820001c1048010000d0304a60f10814180a511034038400c8202514607219820081d000301681402541c564015144014079920705940d21006140018000c0005042001c4001500d00380440207140040d40c00540900004440c0c03005401c4c030a020407011748072000300340001a2070718007468400070402c1240e036070030b0b1450741c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 548954613 1250 548953363 548953367
    0x10213170a0323071b0302090702190b0a0b031b0a1a0306041e0606080907090c080114010509060a170606030610050d02070b10060f09060503040f0512030a0b0f04140601 74
    0x403420f0010b0f8601000e2050401283e034641c00c191401100d94000701c08107056004128666400815600c111741c0104140410300250128280f021607220f0b030313031101d95240d00304004060065031a020741c052041101040c4c1e0341c0b007030180f1510f01c01d1003521880c604a4548000054400b2030034820080c486007000400e400c0e00f4258440000b8811669581c1214204111680305507000c6a000c1c0300041c003040180089a030080c001507004000e100340070007521038000c0000d4090101403081180c0e5060306a2003401503409001210740a9100428041d070725940c1e03101c060700201400e02c0c43c2000304d240c1c1c800181e490511000310303800750000808640c091009842c08940c5a4803024412442d2602401301c500050500c5510900038040342100803203240c1450001040b400340c0850301400c00908400400c00303207400c1320850b6000398100004840f4410141000c47c80c00030351240c4503da400e80001040350006165202a2603481c088500c20880c0a40310200415100203441c55032091107180d010500540c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 548955863 1250 548954613 548954657
    0x1e0e09040203010b15040302030601050609090601081801110319060807090b041b02060f07030212070503040326190621140106060203070201081f03060c03020c010213170a03 76
    0x52000b000400c2c8182e5103408036103e40d64907074552030b001d00089070902c1103107010b000b10f9000d0003043d0b541034105480003000542421002d40524144180800400c110325142d054200d0302d80c814a0080c00107030450440c944a990085562b0501c6148201d05810502100d00030300c000c0f50389041c0181541c509004401000f080e00401560f070281c0d90b5031060741142501200c0c6146020303580c01800301e0345045a051000b1550003407620082601c10402040d0b10103003a8160f603001151840c1054984d5160b00e8261040c140c0b4690501009500d1070400c0e5020640c0031060703202e9a540b02441d0703c1d80704020030000603941c0c28050602240008141c041100b117020408446c4030b80107200e030060fa24042041503007128100c0e00240e0040c1c0001441009558001c2c02240d040703501507a2010604170840206008005a4080140203644030002c1140c1c19129030140c03105144044000c5540741842032b02021001d02c0c41c07040141c01010411030381c1e0b451502040c80c541454158650044980c00000081408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 548957113 1250 548955863 548955871
    0xd02153f16050c0c120c0f0114030a0c0e041a030f01270302031204050c0a05060304110108091c0c1b060c110d0c03080d0b1f0c0c03140d1e0e09 63
    0x6106810080d05944d03102d5103111081d08017000035191081c95481446014800d0007891414071024060000040d85000122a1300646000c00058201c006c0070f011280e280c4070207456603009003441c500024460f00c101c518200d40720b0403411900100c6007030041c54207a0700b001c4103852295103260b80388101c4410081d08400b80c00e101c1d1040d03910b841820322507a1003920b02903d05840641c80000c5002c1c00b82042d20004000e00303402c0742c1c0241146400c4da0f401d01c000c801e0008141c101300703c880111302e80c0c08007080944903400e1303012400400c40c8801d40e401801c00000d01000d59150f8007260b5200d203001104d600c9802602c034603942d0001c0c6003c290f103818483d40d06591009400903010105000820000e4881c10055481800d0443c1e0302d032407171107041d015614107005461094007030910348008810007051030161f06e00d190600e00c04a840354103081c0603904259002404001c3c4607030329084468004540e0555402681d00c4401d081000b40b0303020b6100c0d04400601e80301140b2000586c0040b03241c0705140e1b581c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 548958363 1250 548957113 548957137
    0xc0210050c04030204150614040f091d07060e040b2e1101020f1801030501080309010e040914030703170106020a06050a02450d02153f1605 61
    0x1410b6984da021400700d030240b4885c01c0b10196041c0342804196400603001c0d6440c10085401c80c1420f0904000340241480c2d0306c00c1c5d074421a515680c1e401383c10021101190010602c0b0243c4019075503ca001503c00d0201c1007015200e031345070042a0600d881e002948282c40407103020442e0340e2030620440b03074510422810200b01448410321104054040900003410f103000c05000c240d464902203880000030501da00480c5050506050050180a4000050325000c00c02441c1100c4a80c901c03c000c10001c0c0f0b407000c0d015001e1403031080940d01000001000342144c0d032103680d034000f500c0171540d981181e811080c003a08005801070484440410482d0b00080d4001211403801450403001ca085070002c007109a80c082d4141d02c40411011692140d4015400c2e080003054080481c860b1000006981d030231074280007841046000075040c604420081518035801d285000c0c440c020210302e06205503442d1a5101c04070b0410030040c55241030068010507409030034080368580a80300c150700c0a8032143c01080074058 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 548959613 1250 548958363 548958367
    0x70e19050c0c1603110105070b0c03060415080601060e03210918070c1b0b1b16030f0b0610050a0c03180e100b07020a0312140d0f050a0c0210050c 64
    0x80040070320501c508407a81d45003a59880d40345280082420717407120429418460b05006440100703042c894000d070310400d807801c920740d00d40e40c500004000342100792a0a03101d0392030307180104013510001031141c1030b00d01176190024024603003010940c4da4841500d904074900d10180c80444002c0c504c034090100c08400801311100007640529a102038001220341e40d000600383c0c080102840340711089030f18040000c400054030f050802141c4031441c030840300d00c50341c03104e01c2c00d8064070742d01d030709001d2a0016545861490040c964a08028101201139101504c40100d5800803505d54580207412804407201e5441b42d50800340440010784a80d07409100036024001c400c891107002e0761110004401800c00740c040c44a01c1c1c03c0c217142e4680880350a4105516100082042c413016981f040214000c4035403160504d084200f40300001c452500315540c658400720000329900b028203e642d08000054035800b4420801996903400c0f6030242c943c0950041c0c05604420111b5103800d98039000150300078000c905881c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 548960863 1250 548959613 548959627
    0xf0f030807080706061503090614100e040c030b28090f0204020c010e0304060c05010b0d03020703120201140c0c190b06040c0c1403030108160501080115020f1e070e19050c 75
    0x480600e528489800001c3ea60344008d00c00c02c00d8074810b0620f81406503440e038000c0c2c50318035527140101c6100d01070221884424030000303041007020a11507014541c00750124441e03040c2112408100034030710305440160304505000092444a51081c200039a8105444488140142c0c0070300000303510000700401955260410480d5a0b10b04100900051001d9544c1080c4415541011402c44900608036840b6201424000e00481d5000a50304280e80d084211a40010b509482c241d0051010108607414807030300c40708106484a201026001004404003600c41c1102d4000c60580304081c0c8080c024000c40c4d441001c038440c5d0400b5400b00c4081c090a082404080348291510f40d2440c01c503011b40742841d800000103112071227061189401d8500381d10300b256021820840041d0034120705000350f40500805041d0348420620800050752100011400c4d10b0b40982c1c118800004852110107880d1544107000c4001002110300e002d83d840baa071603001c813001200141150001805015089035800e041c140811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 548962113 1250 548960863 548960879
    0x1d01110c040504030210061d1611011416030212071209230106120515060f130501090c020307050304030f080f0f12010504050405030306040b0310020f03010f0f03080708070606 77
    0x943c2c022802a00100015400c0011180c02d0319466006103a411100c01c0301c048035a00c0c40c443d600e810484400c0719000d02c101f10341d81202d80200342400d0242c15800c1185000041c1c031a540c810b40103601041201c1000303108030009909038494034020f150030300002800564003a00c0345147e90303c51840e104000ca2000d1054880c0703060003201e00d080720070209005502c8074202400b4450034000b03014105109034000d1182e101c0e0703500e03031401001d101c00108221002070101e507200b55042c1d41d41000102402e060380001800000201401d000b11660945001c03031040c2c0140c0000151004c2c56408001075140034203645d900c140c204003002084070041c40034000d0321120010b41000c0d28406a00103213160f10f4a80078440301c0c0940c801039009034080d03807402c03080c2f101156000c01200c0d0b22140c252000704004001c4000300e494010150f002002e56880850266001c0c01302d03000660403100c00079042004141c48003800351221601e07110080c0402000c0003410005482900a0082c007801103a001030103c2e514654 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 548963363 1250 548962113 548962121
    0x1b170a0201051801090b01060c0203030d050703020903010b0102061303051e0c1605041a060c1509030a0806120303160e0301090303091b0308030c0d09050703060c0f1d01110c04 77
    0x500503075199010070000c407180070f0707082030122070f454001e0001800380d03100c00c0b032078510600511017007049202d940750175500c0030411103c401900c0c02c410001d030302c2c2860008000b500001c0c0300707a200b5400c00c43e40386100d40c030018801c1d00400741440440c074690002ea4081d98903074030032000c1000340215985030f40c4c0c0d0562401c005e4074200c440321000d006a400d4901800e1410b900c103402c03062003185070445a8107840200c1c204440d43c84000c5c3c42c1180e690040201c82c03403524043c600b2240c00d43c0c01c1441045543d00000c0041c0018101e5070701e80604513203c150030001c40d8162400c0000d840c0d44184002166082110040d4082038a10b00300644244001c0020a003540c071031060a4002c40d4890b0080d40c200181404d02c00307680c2c0000f9416440c014110390312508180300c09403426036040d0011400e0340310903200d503010b0159035500c81c0480b40741540e60b2800c0006410340c41d92240c0800c42d415090190319005502c100d014030001c0c05d0741c400b140b50305001511030342c10041c80c11a50344180c201c0400c45855601c6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 548964613 1250 548963363 548963377
    0x111501140307090504081306021207080a120525080613091419030e01080601020a1103010f050109050403020f0f070608100e0f0109151206020a031116110f011b17 71
    0x218099444018070a402020410380e4403400456000742000500d60301d1301c4007500c4101d43ccc0100031070b556a01040b41150180e100319003d41b20286400184040c1c0c4950041b0b0005040203c100f40b501d1407511002074030104012a216504003680d0450800070310002e07401000028407400402c48241c001c22a030628151240f02c100151040b606444800d164010640907000402481c00005c14501000000d403034005140c00201010800401d034241c80e41c00703412445a0400d200d1040205682d02c041013400b40000340c905501600960664985a42000c102d1b03608924000d401041da2a140000c03c940c140401070a040c1130b0000f92801207000398826507960f000d0390b1400c1988181d5411b004d002001c84588001e410301100310040700300079000360104e15600d0980c00400040e1604880391080c4c01610a14035142c5010030700041d007250b4000302038000c0a0f510300644009c07211a008009010103801031008131b90205110060050142ca0a282ca0140b0640b1400c640c0c0300c500d10078400c4e80f5a50300589 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 548965863 1250 548964613 548964623
    0x1c03020f060f010302010219050715030f06090212160314040f02040b061e030c070c080f01050f0402090f07030f0204230d170d060302060a050a111501140307090504 72
    0x401194050070040240c00c6841285819000e500d0365001035510141c00d02580c0400c840090b54100b03000050043c0d13001071503011201031854410080c010000c200c01d114151450345440000b08001c1c00c0c0303209a80301484015100c0303900f600c0d01102c160002a1414502c0300301501c0e0590003458140c060002d81c0103600c2112b61214042981c4100000d0361507480c83d0724081c010a11000c54484005075110031f904c0380e12141213540351108103142a640c03088413000351544117007220024415a00042240441000308000c0050362190340d8000c44106003035402a40c0505a070f004070b9440400315141c00d070011580d050019101da05131140c90145e070080d43c07000002c40049102c4032054100441001c02c003100031503c00c1150101c95035040611602d8041032841024086403440003606a03501c100d028640040405448046003100140f4962040e001c0c1d10019003550403ea21400c0d002408044141c184075004e515a07082101e050440c81e41146d2880d814442c000c40001c01503224850180228041c0e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 548967113 1250 548965863 548965873
    0x4020d060503060f061302090d05030703171018020913060f080c0108060604090519060906180c0f0305130b0f041218060807050705060901050901060506130b03061c0302 74
    0x70108140c1040300040180c80440030742c3e020000c3c1c55846100b50003500701030395801a2900816808103040d640c00303100051207848001400c0007415084000180c154514010780556584c2d1b140401e0303010903c40c0b14052111611140d0752170508616006070000341c1015048030107040c01082c011081e506d49500c40a0b14404a000038420b01e00240310034400c2d10420708219207a03007802c1c1c0202e03185115610407a01a150303240c0200d91540d40703c8081c02411544800103100268460404000404c6684540400509007003482a0708510703600079103181005c280c42d1f5401150b01110164060240240761034000c0458920a00c001803004a40340d00414800c0d41c4a40c0c00e2078545440400340690600b01e009005401c400c111084a1410000060b104507160461490321081003d503603600074058000c101d03001d0b2104000701c0d16415807206105200d240000d220041c1d464007845281d03c03801c119000c0401071000d0a11605030404020744c1c0141c00035200907203403420b9040303e16524203103480840c016008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 548968363 1250 548967113 548967119
    0x51207120b040b09040b2208030106030c080903180301110406180b130b07032a0203060106140d020f0c0a0c0e010f0b04052e020309041d060112050c04020d06 69
    0x12074420071200450540e0104000f4010400190002030000e0005010550450000c2d0100c85030134603100944131002d03514124180c00d46020700640c0c2003401004006840c007191410010300c15041c1a00038000031b80603520f0b0903042083c9001070325209103942d40641d2200c1d8007400c0780400c0002030000309039030741d96441140e1112801d94500380455000c00c5007000b0501c003503541101c1d951040411113207010070080e0341c4d10701c0b4034054030301c225180c6140602c4103030207015054003a112480b503a2202e00c00c8050b240280c1e02c0300c109540300c41064000550310401482061488943c076401400008141c000383e500305004071118a00e80b404e0707031004440b8052000020440311b8440c43e615405440f13041c81c1841500d040c1803100099010380d02c150392240702041c001c440d2034036440711001640d28000302c8030b030074071f8442000281d941d81c0000c01c003502a502e082a0341c00e400241402c0b89038004a01800740c80140d00e00140f40342c42d0f110628007950036009003041d40d185643c4074801415184c168000100384546 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 548969613 1250 548968363 548968397
    0xb0d0204030615030809010804060b1503180d09050d0c030b0106051312240902030d031a040603020f06370306120b040b0a0609090b040c060f020715051207 68
    0xf581c01052086401002c1c00042c221100742d4407010000e01c2e10000540c1c0b94242800a800d80307030401f0350004007400441d10100c40c01c1009510801040320071419411403444460350b25589103074400001481c80100b84001e04e0840d40143e0500c0c05034100c1d800c80c54982c2c139290041442a0f00c10000f003140061604800c41c0d14400c0e00c00100b48102c1c05000c0b4001503241d195020110481070300c400000c0c400f0b21000d1264030b038011201c0790f40103008c9901c0c000e088240500140440495600311040f042e91902c92441c25006003425a90f01070910390841c800c078018880c042d000b000041895002010303048503004031100c80818500c10444603411900c04070340e4064102e030103503008030228030b5100419030041211001c46175042540240004215a00d00c04090020001a000000440e040000450a0210f000a01c50084d40110210000140c0e102c00598030a0140c00c0c4100140c0c10040042190f81c03451110124000440c3c2061483d04000c02c19400d92030f94120f40c032001184090000c084109 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 548970863 1250 548969613 548969621
    0x80f0307020f0d0f0809060c0a05010c1b020d0803040201050903100b10030204061d061b01020301090b0a0e180307020405071e0e0d0816050109030c050c04050c070602130b0d02040306 80
    0x4000d6409a070b403041140c45501031511009405404170310001001c901076120082100e8880c13403030302d095400c2e100c12850300e00d0107400c0540d000400600c940002030404100c45844500066001749a2025804195243c060315000188142d041c443e00340013020048e1002e202074610196070260015000340c0e840100070703402c05900042c0c0c0c1007520501040c0b24071a00420f41a9a0344000c8091205a0701070b180025070521171001c41030300001d0003070f508800940054020b141030b07a60418040c00070344860b400340a41c801c594450808848091030102d19546a1115940c2c0c1c0b01c68a1810340c1e240c070714290081001d03250141e030b1000015a80e00c4140080115070b500061001c55685841038a50f8020700000e8034030030100300064203081e40001e8504510518011520106901c1070003403001c2007460034003420054041070281d42c030740281d4400c0c0c80b1515261044a200e640b80781107540c10310602d0f480742c070000d4000d5140300600d07202e2242c01003601034903200546241c2121041c056074950039807420a082d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 548972113 1250 548970863 548970889
    0xb040c0b070f141006091a03030c03030126010504080c1014010612060806090c010909020408060c0c2406100309050d0302030c120a090b0f0403090b03090304080f030702 74
    0x40d0000e00601001680400c215035070705800c01031200d044208810020b040403000c40104604601d09036001803154580d410401e040c42a0621180c904407001081c540c880c8107244540141d900100014047e5030031404130115100018180c01c0110017000704032a007103601c1030350309840f0a1404030310500c00c000c0c1044400050010f044091148030a8810010003000040c0900700604c49880040c507030100982c0d100900402d400c030101d9440e400d00c594200d88560b01c2c014110f0005800d8540480c0400f501d008a030112150f2070f004080e6681d440284040d55040504069298007035010410300d40118034800c409200448500c90605051840401040818080c2200300341800c2880e1b200c00b0030300204c0c1c400c000d16214140541e0f20b50b40e80c00404500e21800c3c40041c0d101d540d4205102c08030f2a298803c410381441640d8105003902c400300c2c03da01d940021940203001034003001003440101712590146070000246400c0300d09258a13065403509250043e11020348940c8040f503420107516106c030310301c049 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 548973363 1250 548972113 548972129
    0x706050c0c0313030b34021204170706080c04050d0f14061807030308060f0a0302150a03060f080a170f0a030f0c090303020d08072a060f06210204020f04030b040c 71
    0x50001172034441140c6d00300f1980070007140e00c1c640c0d400c406e0301d0300901251070b2081d5a0f580c01a503458640d48020103181c80380c004013010788110040440d01e503004c0d000710b6014080c51014503040c20700e41390811442c800768103401c8900341c0405214100080f04c510070341044400c410064082807824400c0381c550756895580c184090741c401c0004101294100381c4940d00300360113480317849940113414081019032080b644002e400500f00b10021a01c0c0c00303002e02618415132141e03803d0012564800c0c061080d442c1c14082e070810340e04540703680300000301020080720170003802d091064200b490515080d00c2581100b400080400e48070045048003031607074450030b4001030660500c02219410342e10002c2d5a206019041000d1041d81400308284500401083c55006000501a41c104c00b08480941d480b4002034021510305040ca0b04e4118002070702c0c007a610640384030351105a95014514100040035040d00010398009908002c0d1a10200060000380080c0d8011a6a034012307042c0780c50452000902c41c0e0020034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 548974613 1250 548973363 548973391
    0xf12070206060f0604091a09040b0a18170a021f0c091208030118020904061508091b3a15180f15050411010318080706050c0c0313030b 59
    0x4040d502d00050b1400c1e1001a5000103031074055001e00940c0301f45400000d9440140c000400c01001061180c0c40d126400002003480a0aa03c4520410700410840000c050407030201c103a018222410000e4044817500f881100d03402c1040c250854116406650095a03103612130407034030310841c2c103c0c412400511003035801c241e003c41c0380d480381c1d522408180a08074040c62820f802d515540e0044d0140c40756a6001082040300c2951240410080031400410300082030000000030552240401c2c00c200088031b091442c0205074400c0c003005a40941143c105110844016110640c1c0c6403038075240308102102d0b40340340c0c0d074190f050600c1a95501c1000310700d040641000c074020700008810361000145640020b1a03040201d461030418400d41d20303443e41200d090728105c100300c03e10104004c010381c01c0da02178800700321014040e401c0b1200071004140150040e03008004040c0002c40540c80035520015800c0c140e800d100c0c540891504541c0600711501d81d94910070300500030301c08040301e1035801091a00d4468 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 548975863 1250 548974613 548974639
    0x1a030f0f0d05030417030a0c080a0b03070302061c050f010e09060907050d0222062102090412031113030b010b04150804021c0c1802070c09110f1207020606 68
    0x340d4a80001c0c4800d41000008400b10741040490741107a4040d041501c021500da00e44848482d00611000c41c1c20000500c00c2004540d440f041c0744141d0420301c034090047d0402c1130544e020320505030310206005a02580d040c0101d4000c07440c900c0f4140c090202c803100281d542d4501480c880c0d0002d8044e1160721650000001e0040c9201c00217408012151b0646601e10354021a000140c08209400e56441d4201101e88005451605590001d01034640d000107112113900c55040d4035020140b2403800a401604907804500454207000140c03103103280c0c52801003031510314580030031003940104004480f903c142610078002c010f08813407194050020100060308291602145502200c00040c03110180150b010115042d511003020f4401040b0703040070a02418006450325110440f0944100900082945221580c23020700e4000c0720000c90701b004403050461304090a0000810080d0a81e01d202c8000f00107400e420748200740034003d80e100704410704807985801c09000e0304000000b80030390700c619041c0e030b618 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 548977113 1250 548975863 548975893
    0x504060f02090916020709180201021e030f09040906090302060405060105040510030813090204060e0901080307022803060903030b031c020709020d06051305041b0302030c04050403121a030f 83
    0x1080e0301c01c1000d21031454540c4080e0040e800c06c00281c00062809040c41002c042c60100c80902d0214240300b0b0303007103442031040e580c14000340c100032101e107071040d800401004444414503c050004100c008200107160743c010b540ea80200c1d01c46503012005a0450b80411043c8101801802d00604068900b88118034202180c056000c8081c0002064110040380c1c00130307851460740440002c1c2800e2541195201c0c0c4425018220212042c1c00d28400d00000001161709000442524400d5030b0140111411902440d9442c0c1000d40092442c8084600c221000010a405010b50b5004038001d84001407606290414182001d218407402c640b1072548075141e8541c9039001130300d20b048441480300141c070748030b0030307001d24000d010700c0d5209039032020941c090b42e1019580382d1320650180344102d034204582080740c00300d400c6000c001c0c40080d40c1130300090b00c10661800c203504120b40c082c0c803c0c82c101c024075030041c480c0b20071102052540701c0b1600140d207402c00700d418200320070a440c420b400028582a4012044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 548978363 1250 548977113 548977129
    0xa080303160c110d080904060b1c09050f061905011d06010516021518031c051303021207060e06160f1e051c03180308041704090504060f0209 62
    0xe52000c01c9441e845202c1405280307007030565551401800258208a141003030b00d035940285000c1d900c124507100d03000600c80e203580c0c1143c200b08020181101210001c40502000300b0741894140c50501442c42d4920040000340321081c811013410b881d20000c10520302c02da03012200141c0282401c412140f50901414403011501035000c4000d1130042c1d07a403004ac02c0009502121180000d4101504d8166076a122003180c01070105140c4072072080f00312420400c02c0665551007000d1002800c04944444000076209400410344c070200c0c0c14501c0302d031a0340d96004c280a40c4241164110b03d4200c0002844050740c400e8000c450101e0458036941464100d0b6604407031942c107000b000b00340000204440b800c100b0504051003034404200c05103000981035040c56500d42c082806054100032a019100c10018040d1195685a0076034695212102104d5034040c0d9800c44098410380d50701c504440400e00b40c85c40c400040000d01144c003404079403410986010780540d4590586075601c21f005112955940d128088 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 548979613 1250 548978363 548978401
    0xd0302030a1407230c07080307050c01092106110d0b0405010501080106140d0f050c0304060b151909150c0201030f0905060c0f0f0310080d11070b0a1e0c020a080303 72
    0xa40381c4181400c5a803c4c3d505446140450701850080400000303e0175000710240a2030750066090b92000c040c84801103a51070018024480b880504203135070b0300d00030b00392482490f040744210800521007203100c000d01c2840d009504100002c07070311404110200d051500075540140802c3c01c201102d9410000e014000129120160381c00070700109040c4200380064200c84414030004004102c0c03802e1a4050603001e0b0310407181075850b00d091556404150a0013002c14403001e06000c207040c1081c00e02c0c031075850601d8180618004001c100c03e00400c1410501d00d04c451260015111080702071344e17900c000741c182e6003240000c4214902d003007600004101d01295807235000c400c000f11141d94003841708803410180a01038200c80034190210030450840c5105046d00140c0b01c000302210101070001004840710080000f03040782d2604910810420681200040e204500d5581030642403071442c1c00340034404200d0341040c403002601000400d005d600f8514540700c040c00b0108003441c6103141c0721007c01480d403d452 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 548980863 1250 548979613 548979647
    0x3035403160b270402070308010314150601050307031d031c050408090f0a270f0b010f080c040e09071e0605030105090a0905010905010b030d110a0206030709080d0302030a1407 77
    0x1c480d4076071403c2291405030f000742d4020400c6468a009003001404080240011164441c0c044103651560324000359103d003042c0b100205000301c0d9900742c01101e242d040913100005140c0c5401019a030f50004480c01c49480d0b0500000356110486501010001124495101d500c28170382424400031500c01c034211030302c000301610915198803400300420701014403503202d54451003c0b900c03048540c032a162111800541d078410140880078030001484119444210341c980400d003480c0314182140d000e0464160b00410880b015401c0a581e040540d00c9400d0459460030700360803008050004000c40141040220101003410404600340b80000d003480c07006003d0b16100b040300c68001a0010107580000f804140d003c4024030840301240b5055000c4c2c82c3e00901c05100f80107441011045c1c508c40c100400c00141044d0003401c1141d0a07400b4410190300142c54442004021540894001800c01507054010110350340180e40303240100d01c0301d00300c6000e411440441c00310b030700601158a5010305d44c14100d40140b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 548982113 1250 548980863 548980897
    0x7120e1203221206090201020714060d0b030111130317090117060f0d030e03060c1312080708070c0315050f0c180a060905090603035403160b 62
    0x800d00c0c0092140e402c1d400b1030460050100f4201c100710ba80d40219442520070b0f000c8501d91522800c9010401c80046030b9107030049404c2c0172110303440140b50481c500000018000007002a5081288202e42c0e0051102c0f2002c01180710041040146003c0042920045100c6040c1001d11754030000b041d5000e203000213801c0300c02d0b04000c40e50640d5051200702c88644000d240c041805010325001d8600714007114098824058900020364551a50003260742c4108034880001d1b40d02e04110046060517248001620150307800d00c405000242c850004065050048059121444c80c500d044001d40000030703e04001c1608210034081d246060490700b40d085040051201e031240019400182250015001d00394090000034000554541181c50382c03041d94025942071030f696131a030042c55a244100b91611454240001c00e640d1071134400c000e2820455002582e5103070311040e40340280c504452085800000217500850150380385020060f5002418402c14100d88117460302d001c480181c003502c90038070104040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 548983363 1250 548982113 548982157
    0x6160306051f0210050421030f180b0106020a050303131103010609060f080106050f06090a180c03270209100918170c070605130b07120e1203 62
    0xd030088000703080d0107010442e100c01244100300c4250008401000540580c4250a0425a06004180c422138100004030520780000c00d109140c060805034a80406588030742e0120105044e02813500000208035024003004640c1c14112000e42060f8011001d562204000400241c80801a203502c45a8612800380c6942c050a00100403c5240c0ba1a5410351038400082002c0c41c042e804101902c400c410862202922001c50500300e413054000c0d90350010802032090300f070b0320309800205207680000e4001000c0b241e40e882c00b040500300341c0301404801500d0300c050554095140c4614100401031360b18444040c0494a00343c0340c0514400c3c0003900903c0014001083c640c04c80f04c1010013031040b680100030075051103d0b81c3c0d6a9440758101103841803062142c9012402c204010346441703151075000b41103424a8110140c680c1d501a140811844000c0c15000420f4180d0201034500c842c02181090900c00d4960b03002803c0c1d00410503ca80b16034800002046a038038000300b643c801600c600501c07000c05007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 548984613 1250 548983363 548983367
    0x308010e04080412061407050f0708220608041b0506030f0c0c0d17090703080a3906060e091515030105180d03050601080c13030b0c2a0616 61
    0x8610f07000900e000c13800b5111882000595031141c9254141000c8030030940d00c0780c00c401c507034034811010400c0d8400710034003100c000300f400741e4014140303548c900035150541000c050f44412080100d91062001c1203d040c02c000902c102e00d10302040400710f000e90000c1c03550400002a6480c0005880311684210b07030000200141200d6084074541d01000b011280b810074405030091910203807100b15510340130004007107940d41d0780001d89070098075440143e44d4180725002c401101e0305d024120102480010081c4110501e1003005510034100d1200d291094460b201410401d05403401580400e054005071010405a60000700e6000400190880741c00340c5511002c9211130b60864481e0390036455442c107010301461016001810503032050384026105500d00013034060f0119002110f08070702250902c00060716a03404200103000c18401103d9007200c007034907034852507804e89c400c481d80c0764180c1000500c03104d03240482194142032800c05800c05041800418400e860340d10141c00f02d80401a00401c40710704d24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 548985863 1250 548984613 548984617
    0x30602030603150903040501090e0f0106112506030b12070909060e0d03060e070e180a0e06180c120c04020304080c061320010f0f031e02070b060a030308010e0408 71
    0x840c0383c50711030050705100070019105d03481072203640e0200e0300d01440041c449a00c1504c0c18824150011030038016032078901d065600c1c01c0c0c091004d00180c01400003a4081c0e002584524150005180140c44150300f0443c0c00307003c6509840b0490b11901e50300c1d41259500d200050000199910701c0340224038140b0780d03d440b030b001c1c100a80303118603140a22031342c032020154540d0184080301d1400d1340380004d540701d00304190f07100540040d440c2d4010004140c20b203003030119401c13102d0708801e41020000d14200800c130b0303050400a0030303507011003c040b00c259481300e107804c00c10100845000807a10392550a04040c06184d0342d0042c100300e40d01480e000b01c000b8040c00b240130161003440e510392041d11340602d020b07a0445052aa060421074002c08802c0070f5103170034416011000000181070310740f814080c0e05038200fa0398201402030100304054031060740300389441d098241303544405800b180c0980c603014640f43c140460440185094090840000104080b903070280301c10741103a2440c0700b0000c07640c6a5041c0b1490314 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 548987113 1250 548985863 548985883
    0x1507110f031801080106090f0306020304020607050d08040c150e0411090303160204061403030702041a0301061412030313030e01181d0c091008180a0807051204050a030602030603 78
    0x35000209207611007042042c840c55100310309981d0085660389440b4141c43d03c03455405882c03283d00c0481c009000240907640119005070008000504040c8a656494906113030218aa40007409440070720040250400d1120040c00718411568000d00050600802101d0b001303041c00d1041d13494241207041505600203c1e86401d01c090250380da501c1100101641d100103a640c203c0c061803402c42d000a0981900e05020101c0e90020003961600e1819020080580f81540040c04014282026260f550360248102c0005001000410410031650300400c08803101403405003805401c100100012010301c00e801d10101503242c00e2581c214000d000048662810065080b9a00c0c0b0ba81c03503010400c01c002e5090210840785032001c44503160707900080d1a6540c0503d4442c0c6400010740700c000003025015040b00c580c4100c4400804203003a420950f644d251000304a0300b03a800120000da001c042c401c0070703c4489412140e10144070f14040c03070301c80400c0d035241031840081c1403968007001054442d90180004074227 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 548988363 1250 548987113 548987143
    0xe0d0203030a020d0e01021902040b0a050307060c05060609061810031e141c030f110a050a18051c0302030c0703151413062c0706090602150711 63
    0xc0b9146514040e41c1c4100c060500808160901c00120040d0310014040008100c80300400110280310350031b00c409000c06c0f4266941c00b20703007842d011a20761000c00c0001c00521982d0345408a034001810070702d061407c05415035009207051010021903480b03100c1450307032080b40594840740a90b07c8180c4000303203441070380000f4441c0140c055121800c0003d05d021102542c080c203c103d03481490400e1150740c85000d0031030044020b21030341140c0d071428080d511683d810281d000006c01c894500d0b40c00710446034018002d40d00415404a0201030b0f03d540700c2c40c040c4c0750307011807601d10302071504000c00286d04080d0340c180314920300c01c05514502014030038010784002c00d003003100701c9041980781c0ca04401007455416407584d42503c0c042540d40d50a1060340800d0044566240e1103010003566150840a001d01c021200d40809826202c1888a9800c0e40e801c42652002000ba00e0030608000000304810030716400f0100319800b001d400b460b0010740101c0700e600700c0d015040c49400c400c07980c0804c904208001060f141 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 548989613 1250 548988363 548988367
    0x201080402150a020705010f030504122a050d091a0403060c09360b0f15040b0307030b18070512220c08010b0d0c17030d02030c0c07090507050a0e0d020303 68
    0x11180e50006039940507034009807101c07142d0044c23890084040390422140548508521914030100600503000080d00e210080080d0107482c1050300750301c0183c141d43c1c00440e6598800e04082442a5210b04075402800074062081800304004543c44e0140c040d40c040a0b0805070344038440200315001d10380d000004d10380c1280c9a48456003607060a440b510740908080700004807815004810307403940c402c940714100003c1500204000b00410f02c0000d40d058030001c0100c11040001107400040e800242d072140507140e030042000e4680c003050201009907845000d58070318418050103100d5810005035403200c070300e0046c1c5c903030103940301c4824040026086803d000070800e040070f400140000d9144242c1640d82580c000e204902c00401840100b1202040151030016580001d21210a402455644402101c1708590810003030f00c141400f240e0050701c40000c0004009403028042000b030040b60024842014104030314900003001a04d42c1c41600e029a04120729244440c10301d0b40c2d1004031000312600601142d17 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 548990863 1250 548989613 548989627
    0x10320040e03090102120c070b0d151203030e06060108060603060f0a080f01060e04080f0a0908070b09010f030903080a020706020d0f3317010b0414010f0b070c03020108040215 77
    0x107489600c0315542a0043c010003030341d41b0000d2996012141e812450100802c500341c41d002d5981641c1c0c000404140c1415100c40244858560484140024103a141008600031281d40b60290886894405008480e0000c2c81045210ba801c8a1200c1c0c5c480800d82c1d00c2eaa0740d40c3c8150020740706112204416034020214000400c0d07a02d40095070389160480300c002008925160303171a40c440b140d000c840092058400700700b10030415001030081c005045031030070050417240d154103240d420440710350440b186009004c620083c0541e417004a4104034000ca0034104950801514014405803005086032212038000410008101480d03049482403115007008110071103082d001c140c054200542c00c15440c0094540390001c0c00c20b1690b2840000c0c0104604d03101c04d9250038507911900000101c4ac0d4419580d80d03030101c40940702e90042c240c18160340e00350a1003560418420524a0025400c09880d410b0240469400550f080046100340c3e0780901b405c0d48690381d0751000500c2e001120346903901d00c480c041091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 548992113 1250 548990863 548990891
    0x10e01050405010c141201091d0a0f5a06020c0d1b0201030b04060e040309031b031a0c04031b050f010809061303050c030a1107060507080301032004 65
    0x1a4130181195840c00244d444d0044442ca0714010410700c0754000740c04c58010004840c655106070540b00040c00e00c50168000a800c0074100b0a2801040d6a10110005004100001d8844c1ca060401a9a1140c0548544080202c020444c201c440030f80541c210080712240070820600100c450a9010741c66080350414a400e101940042200094a1180c0d01c91030070020700032f10f40701c80b41c0d01c050301d80c081c1301001a030011000380000551740c6402580e07640d4040340091001c2301e45413007135006ea03c0d445001860751030070040324050280c0c0c44560a12440091000170b00d0608400b0000d210121491700544501e17004805600c216072000340034a0051128041c5224402c2003c2c013142c00031511403030080d001400640702280304590112854001a0010300c070307851100b4068010b6802403400030300305858042203d1541e4448404840070424151011414074000c2194201401d118078005080820a98800340d2501043c040204074a00d1450101c00c0010301c00347c000c2c42d000d4000c1c41844400406444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 548993363 1250 548992113 548992121
    0x306050c0309062719110105090112051e13030207061409120102090a0f03060c03050c12090c0909010e0f030f120a02090a090614010e0f010e0102030f0c0715090612020a02010e0105040501 82
    0x20071190844200764041b865030044064442818044e110380d442d40848001d2600200b00042c0001c10f18070722001001c3c0660680c0702661321403001018000d4044400d0702b4041e1800405078042410030141e10f201030f03d0940c4a17000c0d245074080984800c1d000003d02d04080f40a40100145141c001c21b0103500015080e100004440c01c590054100300001012180b0890643e801101c402800150400281c01c101c011142e580f64400c3d020303004e850300200c0c00e80010721801c1c0141c0b802c1c1000c0c0e4581c0d0600306142010f1001034081a2808000c6141807a090f06440507070264240044031243c44d080022005030081c1c04403015a24001d000b0000380380c65440010080c090360081c0d02da4809807005410155014240043c44668005c00e142c02d1030a00c403004543c02c58de0b040220307045000a0042000d01d1805c1401360500c415500c1c040d0261504103001c41c441d041c4c036002c100080045034081082101d4002e80008002ca0340d0f10b00150b038580361100264094072188a0200703ca61800c2c04020a211041d84 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 548994613 1250 548993363 548993413
    0x70501020417070e0a020903120906160602030610030e0a030806180c1306020109030207050f0105070f0b041101021605011b05062703071106090d0b01030501060306050c03090627 78
    0x94a0308454441000907000c034051411b40e92381591141222859006503400640b50013400182880e02d0405c41da1a8071103580540d4000b01d41d01034000c02809418684100d0481c5410a10300c2c0402c0501ea079103410503aa001200b4003e428440004040742490310381e001c07003020821035030b0003a2100e420941c6845245034805035955140c3d4814040120b0003078418050842c6940d01035008004060a000070040e001e41c4812046050040030003a02e0005006c1081300850309024600410891500e403c00300404040342d03a203541103400080915a00c06d016010b610203503a400e00e0100000e0340740c0a51881100540303c03000d0042d04c10007042080040c48030441400300602a0000e80c040c00c255221140d40b03003c1e2400092001003002d80310589402d060000d80000d160040800007a400d03203803203e00c00205c0030307001507425035111601031041c82442d0141d10b401000880d074082c91480c103060103507240d1101508034402c1c20301d4081c61031305c1c400306c490b60110244400010307100b043d21100d01c6c803940e0710b480803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 548995863 1250 548994613 548994629
    0x17071713060e120309040e01060f141e03062404090606090b0405010509010e0405011149020306031c051222030804050a02040c0908060c04080d0f050c160e150a050607050102041707 79
    0x118480760050ce03250811980c4801c09030083c031290f2244000c003100f1b50304d041d540280f20403018403612030302e0380c2e14001d08840c80d010b01d000191007806d03c2a018140c407444200c8a0156003043d0040001e07440d2201c021381140c0594040000e1601c8510301240900081c0d1355001f0405000f03e5081ca0801e03075541885088600814070f0b107560301801e00d9070061400032401c600c0901c20242c00c00d40c903c00140d00210307030100c0000c09132101b000403001c3c0100c8040d620f40d000760010768041818540050380300c60164008002c00d130710795282d080c0340006d42c0000c01090b10080403c186600070a08000f4100507855080d54000e00500010480c1480101100d03841d2007150150300c40c140c041103600c0c440d401214150740c03014001c1c0810f545141c0302034808682903031504080220800c00020903200500188003d030710380c201c1032407211345013820074440c0441c041c0c01c0e008050070800c010201580c0d54190101215002d035010b075180c035500c2c28640d009004903800003298500c1100d18403074403030380494081d040c0c030041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 548997113 1250 548995863 548995879
    0x2040501291e031e1005060306010f021c0c0506010e0402030d0e010c0f0b070f050f030403180b0a03021b010e0a1218090e010e0a17071713060e120309040e01060f14 72
    0x16501da005c1541032213101d03008001000030030b03070951141e208900d0001d503e00485001400c4007642e206c5200d500f02009001070001c5d840041000405d00034140149880014401c813400d2a40003e9210b0781c400f04150107200300e43c140c843e6141d0003a024000c2e015000520542482c40d1402c220358080381c21241f8100081300c004c401060301d400341055550407180a800c2d2411599296000e4035900955400103000d840c4500c00055542c2d009001000740f030702c050361301513140d1000d489a0350155241034050013860341441003c15102c900003c103400d40e990446581d26103510000c0058900e03605c41d40e5200c524000480c0f010a05604c1c0350008201a44010020400c10038000211500c90309a140010041000d48094081c1443e44078040e06175103004003144062040d10381d41c0400c3e240d12101600600b2030340000100907130f98105140076500403094403002100b0b1103ca0049480e4840d12155074402c0d0b980e40c0303100c0400c45096002001410790f9025010b500364030b400084101c01e158840c458855200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 548998363 1250 548997113 548997121
    0xf090c0f0e060607020a030f1a10030515151003020306100e1c2f030d02070b12041b06023003071b0b0c040302040501291e031e 56
    0x880340300408541040080c500341e501c42c1002c21005510140d02030380e101030207003c08800314006d0312110400350711610f4100e82a0911540801e00260000d006c003000742c00044041020a6000c6105044403045000403143c50741c907000e08243c5000c0408a4a82184881840c041030b07680550007180075aa080310740c4800400d10000460307480d0285a0000d030031840d600c000c80604251030b04c20b401e005e88140d00e584883c00c0c280c5008140e034800361104042d8000d444850340718604080c800900000c88610281100d40e00306402c801c0c06209a04904a200100900080c10300c0241c400c1d80944a08400303540b00403d80c1c544c80295030394070420003040b00300d090b807590f8074080091090458034129100806400d554a4040645100306212240d01c1e480810038100300015456582c00c03841104501206602c1f5030079801840116841600300070006c1542c802865010720200101809031400b00e02c0c096600e0300d0503004e4090b8070b01840980703400c090003c024040c44003281c500010003560720f0301c080502036403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 548999613 1250 548998363 548998379
    0xd06090b060a020d1224050907111e0309031507021b010e060f09031608010b0418081b16030312021207110102160b06040606020f030306041d010f090c 66
    0x4210310302040568040200424028081c0c00481c00a801d0a513000642c1200e031081c0e8002131405030800800b403801b0f80d01c240f2162403c2c4607050b42019203842c28104009200d9805075441002154107400d1140d00b190a040c5060b04004684540e10060191561980108807140e014031065502c94058011081c0d0b04030640d00c03030040c110107800b050b91540400c50010041c00030a9008100d8851020000c1029075005d031420401c8a90040c005188881c000d890060304074210707a11070710418030850801a03401a002120b403001e401c03c3c1d801103101a6550540040c0b003d10382219144121240038441c503203480060b20340e188008990007074903911441d403c1d44050004034441c060101903007040d041701081405110750701d00500007050384001460840e58a0045040164502045800321100070800032142014001c5078010005c50009020351a030816040303440303010080c40c05c3e00032951410807803e5146006c08001124040b10020000b80d02c0c42d1032104090030039060700b82c80c0c00a8101000484503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 549000863 1250 548999613 548999617
    0x31b060106141c240312140711010507020a08010e1005070f030f0209060705010902040b1c17070c030f1205030108070b0d33050301022703070305030d06090b06 70
    0x9160000b24901d8800380c562154103c04840d0011500c141d41c9826418040c3c440f030094100220b1407404810300b5600d1460600c0310f0401010092041160240070b0502e5403aa540c1a42c001c40c3d0300090f10b140f06000340c03004880a002d00e8402960160301c46100080d810811b5203e096441414002c1d592100c20b180c000b41c05480080d0740880000340081d8062440360300c40e501c407448200b4903510151908803204c000039030a80112800380c400703135561070515085207058400d9090410b8156500038808804c600400e0f01090401400780246640ca09451200c042c1081100c4669074000c02c40044c13503481c0c0c1041c42c10443c0c0e681c0120f444601141c00d80301c110740160701303890480d039406000301b03442414920b1440e10b43d0481500d540400c0d0f00c030100c5482641903071008100041000c2007190161000c400220091406980700c0d40c080d0748108103000041d6409002c003510b01c0b101d4194803460b08240303000b0034982900c6900140c490702010403000903003030050300018100d8162031400c1c0b000d01044010848a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 549002113 1250 549000863 549000887
    0x1205070308010e06010207082505030d0507260d02070516030b06120102040f2414030403200d030c0e030f030d0504080408030304030f0f030902090c0c0a05031b060106 73
    0x10400d418010000b050500c43c6255000c2e10620584142c00ea440c4000f51a01c44422032244440e003403620310220112104144200811089009003a40003010301d028115109088010309614003c231500500c02c001c2a8440a0121480a0030380e5548a0f03401c3c0b540007500704007021500c078010101e5440755507a05540c00c40c180d03604108041e0b016200ca00802002d02c2c41c00090f504070755024400010280c2c0d0400c0030304003c046180e9152441c040c1d9040c0c2180440300d440c01a030070b1242c1c441840d4610034810b020b03607074070a5041c20003c000c07083c4d84012041d50200703c404a0094415030801d100c9090b0f16800c10002601036031103000b81c40390344004040d19000402e0002c01f4070742c005c1c03056190040703107908600e8100c3e01601c1d1083c42c268842d281541950310889094011418508051808903448440c110020341c2d58941000720a00f2039000485800000d482c20b1517045021a1000d40d8041c00c2c02400ba13869403000440c2d580fa041801c0302c1a4172288030082101a00810000007030351402042c000c03a407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 549003363 1250 549002113 549002117
    0x50109051504020309122d03010303020c04020306150d060302010315050d060b0d05070308071703060913060209041503020909030a0203160f02090c0d0c020115050121090f12050703 79
    0x10701020101404001d4100400b20b00651040040c80303500c0300c0c02e21004000d42141e4900401c5d0070f140701d890056010413240e034a20b0100c1d004000410220364082104c0c1c0140b20f04650260352916030380001100407603039400048280000068078003001000390700c0041102e1003a00c0621038404003483c3c820141c0d45611883d600802103800702e00015450307600c00441503000078400741010075251900f03071401d4110781040720302c03900000d08034046c03042c0c00240f010010ad0801d04245149480301c0030502c40318026010611489101816004002454059401c0c22034040d10030003510302100b80c1c04d4105c141030b210980c01480c0c00070101e0b04508000c02203072070030411600203528110803081d10b90200003007840c0c16a40411000340140041c2d642e01c0b101030040581301140368503001d60080ca902201c1041d199082560324010007001440d402c0c18454040b684242090300b80882200c01031424098640302c074944092819841004000c1101d14807401180141c400301c00c0b8100f0144195010b110300740000d80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 549004613 1250 549003363 549003391
    0x501030218090c040e010e150f010f120914070321050418020c1c030e0a150c03020f0c0109030f08100311120105190c1e0503060d0c030b0a05010905 65
    0x20403400c000040c50b4001010f84552898030703a03107501e0502e00b41820f80015080300c004405100c50040030050214800030308507038410034104075100180c5169000c035502c0040c0290742099003a6084039a000c0480203410100e040e01051382540920b48400c107500040b102d03203a45003c042d41600200b0706042c0c03d4030940e225549800d04006601c401032402044406445408000c6c02518000900c2228180c0c0001e6034101168020f0000160656003091114509927100580710740105030218000d20b080d0b001d4a10002c0d01d9030b001c90040300a4801c2403200c404800740041d200540423415803000e05003600a80e00c0d00342000e01c4078800c0f501c0754029102c04d40b044c9004407003031012070100c003411544000c0081020721703803005014105007074804c215120902e10220b504e1143d19006c0501030503ca510280c9000ca2004803a21268010b600c071840c000010401d000c40000e8007a160350166039180fa4021200080c401d6803803078000205403048907900c440504150000cc0d150795680074440c000c84003074030008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 549005863 1250 549004613 549004657
    0x12171506030408040f0b0913090507171005010815090f0703030e060910090f0f18050901090b0c130f080a11010e0402040905040507061103030a0b0d020402030106081005010302 77
    0xe0550005030043d5951070f800c11000a1081d01d010b52a40149040c41c10715442e0000d5800b0084901e0042d1082c0c00c20505000030040081d074042401d00a907641417000c03c1a003010040c11614204520300340d00c1550b172078900081043c460001300004219148155040e5075600d4822440e19502000c0c548081035003e6982803000038010641400045c0020300140e0a0449a100092406c240c000c0020040360005100340101000b41e0f00b040041c12030040c001d05154a8040e4102c43c14400d0701204184650f1000840c1545000790010301245402454000c1103050503144d10540394011240d14039038004c0c1c03050018080201545042c11245108054065082a03445a0404100c2c80080d00c0c10000b1056401d03510317580d14800f41c0b002d001124000503480c0351628210745040c52941207a428400304441204c04400000110b951080343c4a03030114003002c3e1000450f1030004040e100079440350000c0f0011a00c0d40c2d00c1003219214800754000030415542e00c50054049201e1160a004108a20f00801d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 549007113 1250 549005863 549005869
    0xc0f03011b11150a0506040e03030c072a0303050a03050a05010b070201180902030a0207060e0a02150a050c060a2a0504150c0503120103030906050f030a0b030c0409121715 75
    0x2d0318a402d0100c042c0c950105070402d1054107084100e4250132000d90345d20520605003040c0c819442c421440a000303500d5420221011103c90082507402890f144a40581060295001c260701c0e002c45603060314015035603101d1401400c2500300301c9a0702c2c0003d281c000000c0343d40b07070a4080c15040315a070910031490810b0603001184d0b00c90718091040c05e603400348000000c500f2028401144202038185c3c0c0161504c9207850070005403050128410b01c25840480316a001d41c0d82c044072681ca0203011120143d4548031410240c80d103020f1031002402ca0301411003040f4684045801c0420410002049021808201103420300f00501103401000002d00c00d20080c4200030041d803080701090b03a9400e040960300140d40c1c55910351707840503151584004100d0700401c101a0030102080181009003091400d020390b40030203100390b002c02400c1e100440c4c0c95090600036501c0610224025110241003440100801d0a0844c2801580761a501c002203014044903d000c0341015114096807140d001c540300c0c40006010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 549008363 1250 549007113 549007127
    0x60e040f0b090403120c050309060718031e1703041101050d090b01080d030c08092505060d09030806060702090103060b030f0a2a030b19020904020c0c0f03011b 70
    0x42200d54808810001c1c0d070707070108414441d80c86942c95a04080b0303490f01c008151102c10b03801a013844014400c1c032a03100804141558000000d19041e19440e0074000d46110200d0140d1011700300d4030410070700f28a0510307070045541040c4e003e0041241c2554902528200620045070f0203403004110750441780c5150300c900c00600351901001d5020a04502d640c403281c0d2074440aa00046003079008881c007a0301d16400d0300400309006103d0034443d00341e10b841070903180c82d0402c0d001020703103a2126030300340380e041d000d107101010160401402035521412a2440c1500900900700242c000ca50014000740140c60302d041210b1400354041c201d002c2d103928540e205400b809040c130004d940f5015034402c1d43c0e0242001c1052440c0c00340030b0a0450000495081443c40d20355a4095040c103c001c1032405002054403041919000554800010003c40100100c00e0090180c4241c0ca58842e00000e60140105030001d40c0e485003000c03c851030800f19401c61708050894508004981c1742d000280f9034201c10900a0311 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 549009613 1250 549008363 549008381
    0x7020409020a1a07050d02070e13150e1501080309132a050703081f0e060a0515040504050a09110d11130c0813081903061203051209010501060e04 64
    0x10142c4111919040340041c0e1031001404803070f03c91800325242007401000c001d61445400e07507002400515007410007400300f81740000c00706c0021000c00c400c00020401d0032104a540e040d4400b01c200402d50700011469124032041c000c454000011000100304030902200300c802c0040b0042c41101c4001925800b0000780c9200780c04507401c1c44170b00e031958500441c840d04003c41185240e40307041ea030742d10514002d40604005000f9103804205803018055160750303418440240d800140c103002245d5520380015000c00c07016000b0581010324100041604641c00c0c015000b81c84084905200d5655661b60040440303200100180416107180382c00b0342c003402d0400345056036502a0780321503040441302001c504001c9503201031580f00795440ca603091050ba40510010b4000386400326a00203803c10342c603507148501a0821214190500b4105001c00714020f41c40a002030103005401035203007406003001b800642190102d10701b1359400c80c0000748103007810303c00c280c141c07410340d00c4030943e402c0a88103210050440c40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 549010863 1250 549009613 549009619
    0x31602010e03190215030106080a0902120d02011a010e0607020108040314040e010303080108010504260412050c01020705190e0606160f02040b04060608010b0705161e15050702040902 80
    0x41d604248948040c85880c605101102081c0349075402c510501c544150304040020800c501800140300e0190310214003508120810340214404a2600015592861418074030ba01481090755081c002901034001131910b041e60600141c0d268500001980d03205070080c0007035840001008040c0c010360146e58100c0d08540240380294015400c04100a001c1e03105070003102040c10004010010503a00403046809455030f80c000b40501d0801ea42e0310503002c114540411006005000c0e100644000d00c42a1070080072881c0304003041c400981862502c80e4182a41140140264030f008115400c0a0041da02c03918007040381449050701e00034844104030f2002e80026400007082000400a108244004013110b003d549400b4641c80c4c1c0384108401c8640030460a4051401e0180800ca0300e50490000750461341500200780c1c0e2000b031494403a0a06840549020301c0c0080c4000204d02ca03005001c80340450395108000d0035480e6119a81a02c0000c40c22056100203401002007030014285034024603201032001e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 549012113 1250 549010863 549010877
    0x3050a0b090f030d020c011808090907111501050a0816170a06020711040f0b0f120a0507030c031104020f03010b070201020c04020a0201150b090901150c1707020301051803160201 78
    0x9000d58155408203013203031000742d00428850600d030001e2040d50f500c0c002d4007a0703150300c0d4122a5202201070180140c41c502c2842c0c0c0b040003500d0540035992140d0301580707080c20b0702c9a00040d0300c10005140001e0040d140030f0074001c040420904ca0000b2003a0240801e21901e50003185885400041000c0d00b0340c04160318090104500300050b401e0010b44582e41c402c080d6800c0c00c1d0152002c1c04211204086603014031400c006281845844582c100310740381c070040e0740c0444040000d420603482c240846c400142244030f003810000a020412035860103491140302240e28640444003080141d000d40031104035480c6042004010003141d54009000750380c410b0040d1419400c0260019040787c000c1c002e54070150f5100c003490703455034183d015000007034502c00340c88500b015400d502141c82001d05006400300044160701d03031360a042c0900081d907003030750303000e0011300d014402d400800c7d8070764000940c202e01a6013088082100315000201c0c0e4000d004ca144002d504001d14904c0c50f83c1d042107a074000364140504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 549013363 1250 549012113 549012133
    0x71e0206072013021207090f151b080307080c03090601120219090b040b030712110612090c010e0915061c0e1c1809021b0303090c040c0903050a0b09 65
    0x481c00c419003d18055500141c540ca000e8102080d00341d4000d11150400c03070388450070700c54408071600b0881a22001d40c0c2203010030251031030650f10068907910b0802c2100e40e21007806e081148038001107200b0301031030741c40c0300b016164503072130351414081580d10b98126000311005000e52980c507202d501100c0c4c00200705144982540030504c4c8444c1d96900005e00c0a41c581d005c1070110300b02402502c0d1240760640003400c00303a10305480c82c0108640d44900030000744201c03400b4000c2e40d83d0402a1403000b4034040c10000d4504103928242d0b0b984448a1420340854042241c010700341c60000c41a920503030381407600c00e481a17001000c21034103074404d1441700b4010500b00703c8c0440c8c0e901c040c403c1102c800502d20040803021045807580c0319819040d000c1c90f0400c000400c0e00d600300d01e10f0040343c608a0310030074000b60300d030307204400d000c0034540850280288074800032080001140d0005000441e0b62030940e81040005d4040c081203400c0b199500024045921100da00340004170003001003540030b80c002080d100c4141c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 549014613 1250 549013363 549013369
    0x30c04030f0320010b0301050705070b0408030a0207140109050d0813030c03110703050105010e010506131503061a030a0f15050607060605040e030331020d0212030a0302071e02060720 80
    0x80d510503c2c0240ea035560f844e0280c83d050904c9540d400480c00c4c00c00c03a051040c80c0d5640039841e107005100170002140807011a8205410b0740503520100c2d84180148102018041510f00134901001c1c140c1da18401c03800a014924002e952460156a0301801c0250001407501c0a86200c000104201c0030080300c003035010080c075401c2c0b002c0310182d40b00d8030001c1003a5140c410540c41c038002c10f80001c4e110f9802040403121040103004071000320761840c404140c1720316220006038000d003000e0b48903280c807601061106c03070050b51200c02940f04058007a01000014540000300e82140e01c404014010b0701d51351032050000d4542800a8030006204e1710011412030388a00102d030543d075000408645a03800402400461140e0400714840001034100b4107002d240d034080103101c0d032038500c1e00290040201d08902015511000248010001104100d0b039440e046400010001c0d030080d9410743d540c1618040a00101071600e0003d006250014425401c01490351541034044111004003100405040c11155040e2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 549015863 1250 549014613 549014657
    0x50c1204090204240512090a02130203060324190e0706050306030f0c011b150c180605070b060108181c0806011707140906030907030611030c04030f03 66
    0x1041070314000d07032514640002d56400d5125408124082c0c0c1d504060643e4190388002682c010a600c01c40d1000580c5550182c2410b04a480d14040e400c450440c40e0f0035401d811382e0300150b0290200307508449440003600074640030207100100401c540c0700315001296045181d1504020302c10f4001c440007581c0030041c0e194900e409559030041002c903201008000c418a018445060303da0080c00c090104d408032400001c00e500c001a8825820a120341520400d0050b00315821002c041011420040700925441c040d024a00103030a040d400d0705c5201e030200d500352150068590940d030141c844404c549540006481c0b200e401030601c04184a1001c06200300b40701000760003544184003a66a0a00032410170062040b800200030300d0600c5201c40d28194480315045c2d0069222200c2d03c0e190310200c2242803259010b200b00f1007070541c0070340d020081c003642500100d6801c040782d1054074100010320350301e600ba00d00d50104aa2544e0a02e100340001c102042e806c0541c2250701d0311a1070a015075400c140c5c01c04000e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 549017113 1250 549015863 549015869
    0xc0a030609051515010f120e0c090105030708100e2404030e040207030e010c020303040906080304090507020f0d030b01020102040f091d01050603120d1b080a0506150a050c1204 77
    0x585440d07a150512000b48900a0356aa84040e510400d103400003c210044c04140c600c18108541034003401486403080003049802d11103c00103010304600d48118650fa0f9001d540913178410603c01d4000921844c1c005034060441e40c010002d400c00000d4401c0400041ca0304c864907074000d00405010f8120004034070504604c2d10042c8070580d00d6424541001071a0b040204000b41c0514410481c5001207500900e408007144000d00e00070440000a20103c2d0541c022540078034002810070f80040b0310194040050415210070301c5040066079264101280d480d04c040c510f01041c0c2d000380c40c030001481e00c240c00840500d9410b000161034941da81c110017006d003c4552145020340d0b50f804400e0602c0060b220284d100701c0200000348024281070001030b0301e4800011005060200c00190894109001d80003041c8804203064041e41690710000c0251000c0b8003260034032001440c050000301545011003400304010000e0642c030b0b04006d4008000da68591103c0000215481103100140c4405800c50061000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 549018363 1250 549017113 549017123
    0xb0f03030a090f0803120a05100503190308090a0b0115090807060509010f0f0f18050a030b0f010806040c0603050414070303180609050612060612100609060806090103080c0c0a03 78
    0x4428a040750f04400900c454000d0b20030384e041002104169081a004540c12580010001070389480b04da40f184043c20003a8001074260040e400c0d00000010003800070b44c0281d0083d2105000ca6076031020560b280d83c10404010300c10103e100050103000d0803106884559449424800c50311911042d080d85001041d6100d100080e600250341080f40d40d218080304800040c034203103a0040c0540300800350024203080c00c40010000041420034129000a11030350091402500e006a026120f0605c0088003000b200e00b14650000200001446000003e2a600c01c54200d103c2d255254102030045001e40006842615212205511001903490501404000354400c0c0c070360381440301d080c44604c0c500340c020740d000800b400003400041181d81c032124211598005080c02c00145952a400010001c1c000d0040c500640c6001c0c200f000608608079000c242030381c01c00d4452402895a4000803101c4000c02c0742c8880c0c00000036801000000c42c940041c0c050454400300740c0700107252740300100c0e00b034986560042d50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 549019613 1250 549018363 549018377
    0xb090a0605150a120309090f020403060203040c092012060a23040e07081c090312030501081605060a0c03020c0613090e0d141e0c0c011d0102100b0f03030a 68
    0x61407420b51050300040526401c0034010b12134980300038015010a1060071030240e01c6d2a840c41201c0e100764100d030055035001c24219200d04103404d20b0414440746008060314a45011102c2641c403071005d220300100180400344510b42a00080361091020001c3e200e507030000c1e03900340e01081c0c140800841c414404403030801030301030320800020041643c85141c0412429001000180301d9440d02141703d0440c08810204540d000e891500102e4943da8154000303064008008194032116038544c01282c1201d10440071680c42a00c8000441070b0701000e8416158000070401c841400709008109184442e4064010380d03144125200200b013042e84410016003025070748a00c24030107452188a8103080c1d02d0150700902c41c005422001500e4456010701c0c8001000b0045200001d0860955041d6141c4a10303100050316007072000000c3c0c0d80d491035003040d6030100e40c0030203c41000305a03032118003d6010381680281707903905110207050b000b00100418a038010601d003000d07102c5034500b00020000b0460306e0b581c1b55 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 549020863 1250 549019613 549019651
    0x150b130f06050a390f0b101a040e040f020a1511210403020108180703030903151103150d0f0813080c2407060c11070e010803070b090a0605 61
    0xc00c0e4600c00c1d1031101d0240003440d01d201c200e8a0055420345044101c240303c10900444c0d0500000c98116240001e060713088100803c50701811050004003216200c0c480d000700c4070310582804d07550f40224041e00070403440c01c00014001c60401000d0545280c000b0b0103141541d91200d4125599050b84410040840d0030340703190380d4001004000d0030781c50a80741e16030013072503030341c2c03085c41783c0b5070344100c7c40080d040101031004188111640031032500e41c5000c1c502211841542c03841c01400101d03081c80280c4603803100b0903991100f002c0b680189074040344182c203028610345d40c03289413030a82e89001c0c0c05035030409070030300110300011100c4081206a5009003c02070b1200340403100c045008a07246c019244e0381d0450f8030403081680310807100d0020414400c80f00c01c6020900140d00e40c1a00403080d001e4003990070b0485070900541c01c081c0001720070400f4400e40e03ca00d078403124201c80c001d4081c0b0030003c0701d0b40100032a2021800c000031040e04280040152041c102e100c0d1142010740b0010f99412085084554500c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 549022113 1250 549020863 549020867
    0x2120606120703050c040903201014100302040e01020904050a09020f0604080303040f02040e030a030c140a020a06053c01090b09240d0c05040c0201150b130f06050a 72
    0x1002200381c10402805210b0842d0f44031501c4a49856142c0d01850700e500d8090101400ba842c00c00c0b200c101510102020211130031a0750307030366420f208143c9419140c0035514007065a001131040c803440781c50300719001c82d6156600780402018000d003859000c2d5424800c981542d5242c3c001d0360300503030700344001040704c00d8540100702d134881c6420b030001d200d90310400c01048800408401c0d264032a400c400300d40c80400a900100c4e014002481c0014017074000010400c0e40c66815912100d20394042e40d58124502440c6820010680710310708542003d41d01c0701d01030800041e555045180d002d48110b01d1881c0440c04409a6000001d4904140300d00c45928009400d10200140c2143d0043c49900c000b0f02c20716401070041440b016014110364200324a0034101044c01d8003400c01c107148030070044c111110703038107242c10010703040050781c010300348143d040452410b40c01c4d205004401030755000400c45111245862074002e515404405440581d1540510000340100801c8030700300184681d03211aa07850300d080c600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 549023363 1250 549022113 549022129
    0x200c07060801050102120c0705270709061403180a080a020d030525020c1005070c15080c0a110a111003150504110c060108160902030121080702120606 66
    0xc48020071180740010407082c1ea00241030801e8581e01c801c01c50707440d61a0252641020000d802440e00b000414079500310124500c3c104c1201c0c0f0842100100c0c9035112b0184c1107840c1c0469115060003d2500001c860240440d0360096802c003141c84140a40c080492400c10b043c2100f954064452110124020344015018490b1300e240796441d28007000903203400035080140b00b26091003002d0141010007036040089c003c03c68001c80020017440c0c04020145508000c00c5580300d038070200c902c445d8800c3e000911210004690703444416a8480d41515034801036401603e030080b81404007000b29000f02c5103400c0e0418020050094000c0014030100c10303460301489004070380217600710201440d014070a050608a5060001030303a070b003290042140c408506104000780217841450105004110000401102c0042c60f100d5400c40704e4810703040c4075034551360340d0708a01091107100740100700c0c0100030303c0c0c40d00c88098108e0460b01c58501c07241009035640210710b245107c90480c0710960700000500409140c4682 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 549024613 1250 549023363 549023369
    0x518041407081b04060509190e1605091509150a0906030b0303031005040507030603020a0b0307110a0b040f0309080a0b090f1f021818040b07051204110301200c07 71
    0xc0750700c40503070f101074901849100f24070800c82080303404a411501e40d660080a5140c4103400e500849426441d2005200074810a81c0d00780c02840300709610f185140e01400548441e114010490b85a640e42000300003280e51010b4881c44d03208909042c0d249a00380d000d00034108401c00c0b541c0d011041401e0080180482d8000e040c0300388250f0060040190350f42090788050241e0b034003950701041075190540d05a0181c203c54200940c490340c40c2c0c0c4c0c0807440e0b46d052805540309615a070707148440d4001904440361102120b00e00981400e400c1e00001340400e10100c202d401241c403d1a0042c0c0d5550344581c0141440d208000403117520002206104000408003c141441385152024058510b0405000c6c505211000c0c03540540f540c020800141d0180602e9512081e0000a490341c1c086110304913914640d200d007128101d500283c250003140d01c0c18403520642d1007504160b580178405486a80381e00311190004000c0039415074032251030500d10f59030012180220444061156240c00308045c0460620920350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 549025863 1250 549024613 549024631
    0xf073b1618030b0a1e390c0f0206070212030703021b01121a0d03080118050103080301171204080106030c350106031e02010e120d051804140708 63
    0x1c4080c80850500e00d441600300c50084400507401c664008190701c0040c0c0d6080c1c0c52a1146060300400402181000020031040c80480e42040070024a42c07154209450241200000307002d2030441001442c240c3c04212213500090030541001e10a83c0007400d2381e80100103078540c2e600003281c0c0d0030070950104a1b40928980010860460b444004002880581e410740b40b09049501c0314841000302c9000c90788100000c0e0060304151810303446041c0070b04049070a1260240101c0416202100d903c082c0c81102e041e207911695070380ca182d10784081440020b5170050808024002c05001c5a8510542d400400c001c08140c00045503107451828180301551081d0304c080c40d100a1601c410300c460320070180c10000a041c07002c17020b4803283c10100701401020b03d45c2005140c0c1a02c14140000c2c0341c42d9408070744481d4400d907100350781c00c40c1100600c0428559440209500e900c10302e007402c5054040d80282c286003419000801010b0b4038040001c00f500c200c0c02d8140d800c00403280c24040d09030351000610f42d210090b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 549027113 1250 549025863 549025907
    0xe09011a010302091503040605090709050105011202031e0f0618060d060c050c01020705030301051302070201090b0913020712030c020609060c1303080d0b01020f073b16 74
    0x91484000c200c60030038900e0426500103104c10301e41d6540120008408001161251070780b600b0324090004007026108100c880c40354802c00100c0000c3c60180c01d0590b001a90380644000007070420001a400c0503160410150006002515640c001d070506881030b036000408a225043c03020a03c81400c0d0032510000e402081c0004001540d204d03610100501c5500ca000044c1d003200e9070004690a00038800f003045a940001141000d202001010b941a03c008456070034000c606032252030100d111710b0300001e01088040d030040002070450000742c40003503006801c2000348281e482c45035080341d11051040b138194258000200c03900d40d1600c40d201d26484c183c0000c2405080a0001e030b82d9a16008041498070b00c80000d074500b041c01a078a00c41c008680c000700f015150419242c051740540b034010b088500621a076484281620000141e880c201c5640b813925009001c50f80c81c0e00550300170100e2100c0d0103041c00349405001c041600e019a4070602591612964040312500c000f0060f50018000d12101002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 549028363 1250 549027113 549027131
    0x60507020a05130204030206120f060f01020a1b120f0501050106051608090f09090604110901060e0904050c1207090b040504030e0d03021c020f0618030405150d0c090e0901 75
    0x200e107a9401568402c07910b400c90030401101010182c869500001d4200001240031001040c81c01c0f003c6029420f01702d8015107503036030342050000f41a03c0c116041e00607400140060041031207031031072030403504d11404049042c03a01d507403a82c05402032a050803558040c807041c2c0e0f07405010080c4603581c05001e031803400c986090002c1c4081c2d2644d81c001c00c0054040303580084d00802a9541e180c000c50b010780042c1c150f140714a801c502a070303202c4400f00c0b016071304114846001582c914101d41e280d416102261142e04944009070240320310a60000c00c00c035502d02c80c2100308140b5684085192614448480082900d07500f0124802c09440c640b07001540584c0c241414000060b81208004160410656241c5848103442c281240350800118140c0300050002c242e115082d9400f103a044000d40c00170044403030940310403490b20703681d00000362400541c0d0018081131241d890405196560b04901f4ad40c500d04098840d0100c80c100d5040440402c040340004008002c1c0c100c10301002d690040fa220000c02810310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 549029613 1250 549028363 549028369
    0x3030318070e0105010e12150c1b0f030a0e181f0b090108040609060914030315030f0a0b040201020a060e0c0f1c030819091119060c0f03031103190606050702 69
    0x111528400b442040c60b5036008840c624108294100301001403805840750410100c04110783e0f011280c4001c520b503a5020082c40d40710300160381ea00c400c03401001146815502e5200711a103134ec801c0307020707a030129640341d04565050880001038001c04c81d20711429140145803124445088543d4411070912901703106220740d036038008003400da001d80c03c68001704200013141343c82002007013034450041c13010700c103c40c0c6001c054034000095885001048a09030403891880308060f03468100c3c00551040d54032500c04400000c0d801d841d490f030458418011500300c2d03001941e400007565071206050440758004180c0e10344600d040b07012500a104143d5040c2c107010340740000c1c1c411401c10004041d05200b8401c01007012141030740b510155101851031f0401c01c0a045280030204031811706041d6118418a42a1b0365104441400f02000c0f580e15840b061410505680d8511200d21a0031054080c1952141c90f0400e58002c2d100651151100b0007034852281407048806003107501030741144082180030301410b801a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 549030863 1250 549029613 549029627
    0x11070f06021b0d170c0409090f05071703040513020c060f160804050d081008010c0503041b0501020303180703021e041d030418091a0412020d0804060f0b03030318070e010501 76
    0x1902492107164130b0354036151240303001c0c4155440581860300d0203c200d070a00888400200c58544074038142d501c001d0344c601c060301e90303a00c00340d41d14510b41d002004104070a14101900402410070cc80015050050300e1802030300b4540111a451040000b00040180031036129a1100e031800080c203040100b814243c40d181d90354000c518a81d801e1210000c0452410442107110b00d0081440700024800780c0300c000d400030560740090f94111000c03a802103040c02c04448044040081e18410313801142155542d0040f0040d91720800f4102141d40601e20f0084003607160301858040c0d54841e096171681805c481c0050008a80480c0d10118251026a803604011180402107608541e031510105940301c80c03039284c8000401d8402c03001440300e440d1140c079003124400803c00c9449940580034410f0b900032074100681c0c5911500d001c150020b403042c00050005100c99024941000c082030000542500650119156500545e40f208807800340383d50468900804000060142220411000301c41d403400001130035403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 549032113 1250 549030863 549030887
    0x804030c0806091903200d09061d031504060b04050106050a1d150a022a1801030b180f0601060518030a020a030b07121a04290411070f06021b0d 63
    0x40d4036940303004001d0304050b010704600c1c500f205840b0a0f0507c1d8401501001c600c0c4a0400030074501d440a1381d060884400701102101d0180c0070f0704a02c6d256010700d2508100007801110f0300c5640d421054813039151031184034043c003010384035550b640741c050342c000c1c06e04009d80d0f04200624401ca5182c00c2d040d29101080510615078000d19929503200b19410b038200700703080c006142e4850008118101d00300700c0c4400350076402003e60f43e9a446640f00310201035521000d002c00342824142c070001c5140d14a000c0c6496800440c918280c0341000382054005050030020313401000000c401151081191490252698071400d048005103032440107940400c280140303a105c0544020007440000320f115000b041084020041e82404110070403455180d42c20200c110310b030302d0740070707038644440c01f5080e00c040c0000b040d600109002c10044000c161013040064148003e42600704541404050000380006070300d111101d20450000da1207055824089480c1101d52a0003141a44485000561150010f0401000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 549033363 1250 549032113 549032117
    0x204081609230711010e0c18010b0a080c040803160b060303070512210906010e0f01140f0102010b1003020d0e0102280e0d030c12051e160804030c0806091903 69
    0x746544500f0142d48410f06421464101e50904078802c4241c00c3c041029102c89808550a040c141400001007001c000300340201841e5000410441110a014040341540840c8040004c0d2910b038071500c2442c250741040f12b500108141c140545810000032446443e030141c420740043d8107140d166220103980b02c4007100c1074040680d00041e81c400d1001001c241b41c040c50190380c8a070040303060002545650710001d110700d80c0410091004504081000203005040752901042c8480b08601001046030000b4030030050f0f41559a42e80b035051283d200c4089418080d9540d03100183c9031a0401d00c0e0740c0580f0130000007401240d01c100f0915680051140044402c060428101c200c9510300e6641942c3c89941e04410550189141103074030200f6903c01812443c540c8900f44400842c66940029070b014003c5040803e030742d040810700543c00c1c17240d1802501c07420070320300c619050707031741030382e160345240d588a60015070340f4162072682800810000c100b016000b074107030001802103900c0c4071000600503600641c0181 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 549034613 1250 549033363 549033431
    0x130e0d03110c0609070801180c060e130e070306060909020a0611190f03020d170a0f020d09050f07060c1a040206120906011d040206120612010204081609 67
    0x2940144003694080b0381e80c00b0071074041c2d04044003c2940e448051103040040d609040100c5114241d0003405000140d10200c3c0e04c40180c02d1100544646106445807a08040c40c42800e28800c0b5460103159000b8203e14084c000c0d1320f0441c280310f07041d0f6240d908030716601d0b07052814200068886d000302c401121952314003462448088020b542c10311007094258410143e21070721031070a000003d080000024801d8085034050344506209654520a0008140c90006e20f640050b201c1c068a4000d0203070360121400041c45c10700006004c000f00c80c4010029030790b42e0300040e58950009000c00c6004050007090a00840c40c185a607291107081910011034103240718100d01140c111b440e0340c400e4030700c0c000e145c01c8030400302d181c040758550b5500c00c00d2181c03031404c0744000d80c00c11a581c191300289014a40241401c0c1c0750492030141e510b40c3e120007510594000d0109401141119020704c0a00090042c1c50050250b1072014100700c1221510341e084141010b191000711a400411002048450401c0400242d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 549035863 1250 549034613 549034631
    0x60507020c220506120303041101090e060d080a17100f06051606020a090b031317090609090709050d050706090b03011d0601021006030c080609011103070e0a050409060b130e0d03 78
    0x45c2d80070910040c40013680c400030050004100c05a003d02c00302c454203076110742441b607403a030030701d000c2c0b041c20782d0450303049601020300d800030070500710040a1440050502d40c1c0707011000c01c445480c1c0c0350308495024103022000820701003502d0481030800246136618181341003a0061104112521841c48000c0140e9400513600741700c5409000c48400501041d641e490f12483c02e00b0341c114014501501c11155409213011610b14030841c0025030b82c2c0c1410240415040c503c80c48140104110040e08007402d00202c00d20004540d59a00f80001c1050304c038134003801e5810f1400d140900000a45e030061030b42c6180501c014484800d1180908440c50b4140b940c561090311903c00503820460601244103065040502c0401881601c03510749085584203001c842c419a0b451a04508076034a561a0122035002000424642407040250742d042242c0141015051395603000013604480364094100c07003403500d9112403a000e00d0700e400d800a02c0101c1420a22004640d120499201c2c810604400c051560f512546 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 549037113 1250 549035863 549035869
    0xc09081504060908030f06120f030d0209060d051f050123030a062102190b070209090f162105030a14040518011a07080306010f0203070f060507020c220506 68
    0x1101400c1d007042405a5078100083e00d49903d1b14200e5415001d4040703941845030759000024003650f168404000703103081003100c00c40000070b54442802d041e409038041c010000555001d03c1042d00501d8200c00040d01c3c030f0240101451006d9242e40b01c84e050000c2003a1000d4001c05c40613001e014a908400a01d80c0e0b642d40c4200200141400c0d00101e00343c10386e00030f501c6030300c0b22502c502d00e001c1030080301c41410462820781c00c208590141e002d032180900043c0020b10050400346a4240c100c81d006082d03400000c412040c240c5091140c145008140413400410030001298031500d0313000603134801d410311020225403603440c4d07240b0907003102000300802c0903a0390b080308107504140d03805020010715886540300c0711002c0e402042000e000303400c03902c410342140b0391040c00381408850405600aa44904507030b54070005541101b107448a40c000d40c04200003100000e890465900003142c446e10b4005018140032130008e24080d4810602800f0700194181e50300141d40346a02c101c455100300c403001c5201c0e5155404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 549038363 1250 549037113 549037121
    0x4030f0c02041b0e31230c090f01020307050d0503063001050105030a0c0504150e040b07020c030f0c0d050307240b150d20040e0a0c0908150406 63
    0x50341c441d0b400042c5040441a1348494071070031104040f43c0811003c0c409007155101844200da124800780040d0803032142c0703e41e0356045200342c08101c04070740d101441c0505002402000445208a500c14009910f00c55440c00200c5026000c000384015814103410382da503d682c8081032101c00081c04004400070344a40d680d20820862030b03114a00c0c039440d45a41c00069805c0451032a0b05000325403c11001040d24100080c0d0170024030b4000d100406070524003814400200800100740396820341c08640890340d541c0c0469040d01940c89a01d814580b8030b40010000d082049148004ac880c1c1c01540448180f008002400446180700710740303038001002903241240c03031342c0702d855002040000e580e151074208451800e961504209003140030300c1503402d44000c12580040c030f11004640064180034011404d07144d98031250142040c0700061149505110180d07171075421030ba00c00814540060100001d00010f802603603c2c0100e04d080a00d0058103261459850784000301e0790240c4440b1500010b401d000710b0b604 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 549039613 1250 549038363 549038381
    0x60b030109030c0c050f0a0e04051c020a060b01050a0504140f0d14060c09150a0201090507091a1903120512040b070e190506070203010f02040905180604030f0c0204 72
    0x708860621440c0c0a0442040418242e07264407081600041354100300e103005d4040d42c0006d00f1713028072904100c2820300020f00a8030944082c41100f8000c02040e906041c440e01460041c3c009050601d01441c010044d40c1440e07900504119003807000e1340040e0340001c250782c141c1c0d8550420001c4684054081101c4ad5003552007a90301006002c1001b0a1001c0340010301c80743c030301c450103640c0700d540c03140c2d09425203105541c500c0360042511900c680d0a464100007506599007035100100d00b1032569250760b07162188980004503c4d035640c0714150800003181442d17a0a00c0c034261030500b920b1f95101c0f00b4001c0c0417120700c0040e0281032010400c2081c14421011100040d4940241020a0034581480800c50008603102804035459240d10340b0075217040d04801820701c40202c500301c2a01d0901e0700344641500848000c030307003540d228040341500c3c400c40d001130409801181c4000401e40341250720081256010518603605030000400e010100c4d5100544c1c21000e4114144090307040d15030f1000c50000d2020380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 549040863 1250 549039613 549039619
    0xe15040b0301140105181509041a040302160603110717072f03011e1a0d050c01020606010908060601050901050c0a0b0103060e0d08060d03090b03070203041811070f060b 74
    0x20a00c1e0140c0c24036490b10030b050f0380c016140d1250600d11003c50750140c80c4140c51f050103104051014100341d203081c11066512038452090300c2c985581040c4140044402928101d000d600008048410061600c8040d0010309003490144610500c860700106544140600504002c081451041307401540404071080c0607801001c03601e02d04503160380700070304407036407212201c0c40409840001100e1605018040551000c0c1c080500403000f0694407100520801c40100783d0544032046008291707480b240c1244050340100d000d0507000003040002800c1c0280217140c0c80c18013034400d50600c1614000101264410420309155540c0c40d014001641c0d640504980d90495114506d9000104280102524100c0348100001d115924140c02a10f458011164490740002e0325680000c030540340040d003000e1118003a08007070400d00d4980b404036403603520440e0b40034050307840014100f2050a481542031800a040300e0704000908034400103251074410524064114900008a1014040d4503804190300c54802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 549042113 1250 549040863 549040871
    0xc170a11060103060608010b041a040c09080d08040b0f040804090209030c120f06071d13090b010602070f061403060423270a03020a02090a02130b070510060e15040b0301 74
    0x134902080a881203024a5403e5401c01d03020740c40d10304250041800c081c00040c22035031200c0482050000030034400c0e80721400c12441c02000641b021062005020360302030380d52025240c2c4bc090801003031180c0080d100b40441056001000080349a5909032015505510743c0982e8540307034200000d00c0c0c0380d03049482650110b400b9510381060721000400c10200700201058602c00d80e103901040d14000300190102c4119910303c41c1b04981494020040c88030f20b801c01d1800142e03174045468a01c0381502c00d13042103015a101c40018021526024140c00c014001071800c3d14045000300080403190001810050165488001200d100e1046a5035841e00307d800414021040c5001685c2c9004008541084800c2c11a4001e00401100012070180da103982c15400900907030b4403e03070910000e00001842c0002d01e235802e11102c02860303032100f101c3c4000c00b2000341e82900c51216051050500d1020f8940a0445182ca00c1c10880b101403607501582c400c000194102c600112807020802404203000d009a0551030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 549043363 1250 549042113 549042119
    0x1314010608010311090919230105061206060d0209060619050a0f030b03060c070c0305033601080403050912011506030b090403120209060c01050f160c170a110601 71
    0x44209018103c0b0b0041d6050010000c0340b0061107400d90007170f80c5800b12904080d600d40c2c6e01c030040e09158124284900320068401030410080c28590721000c00c29552a51990144046850880200d000c41030546002d880f4904100001514004103488002e008049002c00a0398540c0c44006880d011030900c25208030b001c0044800a01d0b6030301c1407144102058040c6280d0030b480d0b100e8410065560710290080c11746403582d1020303c8048d00036035000c07100c4e02c6000c01e0120000d0001e1024208135070001d81c14004070344002c52104540800344a1104014201d07500280803680c0c80040c581e003007034142c00d182c0d0341c0e1203881e80403c0d142012240c02440660030901e00c8230144586110100c2250f005942c200b00404483c01000403010041d200540082c010481040c00104c03594010550503100a0000c0d20300720000008909680c001c403000c5107040b408404102070403c0352103880500c0100380c40c00b18040d10f016507550354500c0104440354403800001c96000c3c40c40e402481c400000c1c8581c0411100190b81d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 549044613 1250 549043363 549043367
    0x80c03071202130f05090724090b22060909050f130210032306120102070c140a0918030e12071205010b0301060f0602070801020313030f021203192913140106 69
    0x241071140c20b882201c23100c0156901310915144004651082d540c00c8000351034551008400d4008040c0342d4520300c40501c203c44a480031409010050406407078015455180402d04411903200504580078000c1c0c1104000c0c031504018030201340c00350704482c1c1140c10314424104078005c001c1c141028040050b410b10364090381e440c0c421414482d444c1150081c0e0308001820703416090f03002e20320f0f0040c15a000010305001c0d04440122038100060090501d403003250f41c41804d60b090366542d0704409035082d40010920140b40d40703c1c0100e90640d00c25a298a400c80351000c04d90342c1c03000f280c031407200e0411180c0c07030107002c0050a4000d1225082c00230000c0c04415215018025101c1d03040c0b04e90300241c40380d02400200b440042c025a40f03d49807010031000700b080aa101642d03150070324000102103020380d02c1c10002e14510a8003450207501103d8420745400320101450341181c05100701c0c55800c200c51798001051401d005010041d02300c0665160360f1110f0144010b00141481024403030341d070b00b0402d0012900079 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 549045863 1250 549044613 549044623
    0x60d200702040509031207080c0708130512010902090c07111e100c030207062f010501052107290703050d0513020a0314071e080c03071202130f0509 65
    0xc1c001c88040006031929651140d503071180002d003d551000c8a4000f4102c45d0290320a981c0c80241c009069181070180c1c2c0e5660580d900c900848480503d00100070b000b18206014440a14441d600003045170ba1015000583d0042004111b03a4141400246503420080020049036079000003400190000c180003030500c00c0c4e00911050039014500304491b001e40d1074819001428515015009070031080d040000444030880390120605a203411640741040c40010401c0f01d00240003000000038455040000f00802400c03281e241d070a0b481c54040300d507240c2400100d2008100c881c1c0050074180c4110b14042011420078070412a49480c0000c5900b4040c15004401014007035a000010055590707503a8400b4860300031443c020303400c10340041c01400051110340314017000c590760b0000c48035441d5a4807800207518000c000f9480d076400c005041081511410450b02c000364004402030920035042104102c1500205078000c5d104507001c401180240355281e0002c02c800c03c02030020301039860188002a50b907 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 549047113 1250 549045863 549045877
    0x170a021b030a171b0d0207080d0903080a110313021c050c0108010b0711040e010f060303020a05060108030c030d0f06230901080d0c2901170f011505060d20 68
    0x40f0b0340084085640300c1412968500c20402048601095210242c03072030902d40001480b4003545508000c4000032854000190103031b00144540403a40305400d140c000c01d201800307400d8801141c1084d1004046c4c8103101d0590703621801401000308200010b0000a80c00c04900b4801003981c0f071000d05070018840046584004058203072520442c90b6603481c00f0000611440d200908508125048245940390070f41080c140000100008107078101c9400a074021507506030300171805a07101060302010090244007460041100f00c000e1401c0c4039103622101d480e4801e2010008807030380e4428801d018402194010006000e5a9540c42d2101c0880910100c40f4800885428441e50404000266881e0005410704001c0010354402c8603402c0d26035030f880c0d0038010441c503a00508014000348801d0300711280049000b8003400900d0003940b2030480150b410209003100104083c1d040602500c1030003000783e80c100c1181d0040c3c803256583c07441101c07510010040c043c08110001c003024100c85048450502520030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 549048363 1250 549047113 549047117
    0x912050a41250f0201031a1e0f0f01020a0206030403020f0601060503011d090c130b031510060206060901030222050903091306030b0619120510050106050703170a021b030a 75
    0x440d0b8000340b404091500a040c001c04000c000103080d0300551003508030702d070b0303445580108031000c0c4401000601400c0703492604490001039a00040b910303180001440f0300710341094030703420001c001030f50000703441d0484036001a005d124000040f40c1010710800008500790440d0040e241c06584421001b800c42d8800e224110000c0284005807407000301029505000f01d0344080100660b20701c0e41e042c0700d1910030a01d4602e50541c0e07120078183c04e54400780001c1103200385022064a41c0d1400d29080b0030208000c4d00182e00310f5102ca0100642911240061415250111001c1090303101d0900990400c401140801c90b80c1401d00003800003080c000005030040881c215851541205540c00e02821280790b880098041141c410200c2c14504098400c1c3d1040c04c1c605440109091300c8081c800c281050b0580100c905601005407400e44006d039101d01805050689001ca20b040c03150746004121143c0c01d00c0704851381e0702c01c20200f020103480350304448030901480c0c0c05280100403010055240d81008400b140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 549049613 1250 549048363 549048397
    0x18080706090c0e2404020c010e01140c030115030f0e0d122405060f13030b10060804050307060c0e150711010f02030d02030405070512010912050a41 65
    0x5645500262028441c0d01c0c0210078620010a0070168581c0c90071300720703400e074205a00300315141003100c1c02e000b00103003000e242c800800c441783c85501c10301c80c10400070410700c44090f05000600050b40b042e110004005407603d1301003940310303d00d04082c006149000482007144910303100081c907140c001c1c540070b00003c81e4210030882403200050242c4140380c3c08040c80050140890148914500140501208071403014070b1818011aa5007459203110181c10a032140d41c2164208640300c8680c00045007d4040e5240c88400c500300f56a0b200d559005492000b0f0465840700950989144203038060010403030014519040440c48801008440d444030009860440050001e0304640d4019403c4401184060780154941000358415600a4201a00854050250f0413001845544e400d80c0d20050500d58000003403000b450b440c10b004100131040b40241409000e12541c000f039030300640480403800d01c4e008801044034a8035100302000201701c01c4004015110500320542c1e030085005400070a00c0019112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 549050863 1250 549049613 549049619
    0x6030f0610030c0215040c090510030c120b01052403070507060b120d0807050c0a0c08010e07051e0a091d060c1903021602030d02010f200d18080706090c 67
    0xc050720b91202001c2d0159000b144150700d0100b005c003540c0d500c14000c4150b090081e40310f400e01020f0b6081910f890700803001410041c0207000704c0c210b4910040100c109507807400c14071a541d0354005901417080320b11070855041c014030740074070503002807026448040340181e817031805813800703069508150010344440b4074110f65403600341004400b0020380442074008180380011004100c40c3d48030001c12034001c206051050310740000f0200a8402d58034841d1404808690800c2a260300311080c480100c0541d0380200380401454845446000c40600044500742d0b000300c005000c1120b040b00c59000d40a8246071003103100c41200d10307010100341c0c4a10241920f4850f1240445804540a01d1141d48003103540095121002c41c001c2c2d0041c0340710f111840e2715040d41012500000d090007000d40d6030f500581d4451000740c480030382512400c083d400c01c0380e0800c03c0aa503004180d40140c000c0c11840854141d485040303110304841c2c080340d00902c43e803114810340d4821440c41c00c5000303050014411529104070441c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 549052113 1250 549050863 549050867
    0x1003061701090506150604150503010e0f070c11030c030703150b1002151005031c08220210030908041710020304020105030420061219230703060506030f0610 69
    0x61100c9070040001c084c1d50701d40001008030ba18041c08240d90042d420080060b4503202400c0d200c5a010319038031380e240c803985030130380c11000d03514010300c200420b5040e0000c000072140c0100c0c4880b13003160840054640c2d440058082440d1402c040382d5298184601d00380041080040f40e41d07240f038480000c0c000d00001c0001d40074002c280018015800c050b811000058800004d6030390203552040300140009070255480c0040380c00c0c050180e550001d8508002d8040b80c20580056545801450960040071600d0700e04552405d41c034410718000b0b2041004000c20710310070f407003a000347d19516000f0152a5955582c1d10408a0140000a01d0b6001c0d0041c1450160a0009842500e12440e011386406203540d446c5e0741d460500400c00c50000c18200010b52801072691681d10103044040024605111103060054441c1c2d0403108241c00241507500b0a1241461150702002841c50174070b01703620010072a254414141c0c040c12154100030b0300143d0100411060303015000b01c941c000c00d000c0d1040395000041e540c003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 549053363 1250 549052113 549052121
    0x100b0408010902031b030304090905010b0603040303020901080609010506070327120b010608040f0623070203071103190323120613051005060a0c0204052a0301180f0207021003061701 80
    0x1031750762540044c071041020083d01c1d00040103262117038000103403150121000907034540090309c00383c1c0004d0780402e980941d941c1040c3c1e696040760b01106c0d810031540c94100000c20a21690740010f0030401503144515070440f200d021416000902e096094483e900e490f04481a0455001c1c1070701c1700c0411100000d04c2d2070181044900840d002405456001210749400c0702401359624036100e00f0380700d00b21610a1a00b0074150b5030141038250b000e195154080d0400544001200d0610351181d0031450110903070b0b184c56103c1c2031550744d140c242501d030001e0b104504002c1c0007513611880c040750743c000340078000105d0008100384141000c0720080c10510074030a1180c2207d60460303c000c4484c000700c00038065854201d010300007032041e529018407600000d502140aa4805982c0700c040e1251150192449402c0e286c1c08100307070500c0c00881801d540c50403000d0300360310346803964098500781e4030f00c940d1030140003540464041a0700a8481800311104110041c014000380c032811b40421510a1000115441801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 549054613 1250 549053363 549053413
    0x1e0d0b09030c120f03012c070e03070605190c020d0b160912020a06050d0f0e030705010b0d200f04090b090105060604030b010b0315130209030c010e18100b040801090203 74
    0x1285400d50f0b08044401c00041726040c900c0e52250400e4803014068458019018400e43c900e42c9c1d903040c2100c2201c1458504007071500180103202050100d00d16042c10310f0042070b0900307030501e014600600240045901c00c4c00c180342c054540d030703c603404000b8480c1a102d103208022017030395a25040c0c15517840d0701c0e170a038035000a00250b0022545d00f00300b2140340b040014210110f50024001004403c4007840301c1101d18184828002c2d810204061040c00800e10512450140584504a2210480c1d840021900d2000201e900707401d0a4110700b07142e6159090482c00c0c203d40500f003000039036051b09000803040003c50300180703a5800e010020b0f450f810320b0410f480c2140d03402030340080c460f424040c1c01b4205810040070b24aa400c41e032a10111140e80e5984041621004504010b135150020018581400440260350b410301219450800003034555900030001d030818500011070f9500d030030002012260315a480050408008140812440010f5001e202014803c030111241e0603c200c018040701c80e0848 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 549055863 1250 549054613 549054637
    0x50c090106050313081306030f150509011e0e0c03090601050f060406110102071b080d0504120f060e07080718050108070605030406090807060218030c1e0d0b09030c12 73
    0x8404160182480c141c000300c0207104007000c508015583c003c8416880103540480300098440300145856200c07441035a026910ac40003201440e030401011904562044c4902000001012411151005618980000751440d05045452414001140c580d0354205aa2031191805003d000044525124203865845000030b4034031400d09140c0303032060f181a0560045048c2554007049030b400018045841160424001403010306a5400d02c95000d1901009030480c1c0d003404410081408945010101c0c20b00c0e06601105804c1500ca042c40c0c01006003074022041d070180e10884501242004002c5030304402d07203904000b52051400a031003214150355007841054841e800100090020611941c002e5a12900a000214800c0c04603652003060741d01030300c1c0580f02140e010a01e10030303615401c120207480210460003801c40348a050002042401440e0018101d4100103540d0030b4141c031041d00c461070f6aa0054005100c0e031902174880d0b81c89901040c000429801200808000807810b281940d801036085 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 549057113 1250 549055863 549055867
    0x302042303060a0f0b1207210c0b0313061b0e0102010b0d0209040206040b030a0507090540050c0918160807030906021b0d141602210109050c09010605 66
    0x1840b81200030040e8104803401183c072903a40d00c03425102c03005041c0072411800014107d5034034241050400242c0e20019000807525800c0c56004551244c8030041a541101d4800d0350300d4481000c044101d01c40100d00801030360801c8000c500320743c091083c1d1102d495060311007041981807003004900301d030040c49200354071500d10224400541864102d19a100d40b02034011403610f43c585a414582c0d4108552080c0c03141e44420030031210030361054092005110640360038030848020391102e0001c598516109910f210003c0c2c201d2542c0102281c5c0710070040f51080c1c02c120b5801c140803540f4040e132102da2000d0081d0103056031002c0303030700340030300d105201c1c000820704140c0c035003082007007101c10030405003d900405440d03035a04804104940b00500f5000300d400b840ca0b54603084030174a40d007040102c252a10034846142c459010311181c00c01281d5148000503843c00c1c9041c81d030720001f0b002010780520512008103a400b07403150303118150301180846000b44111a540c205040400c000c091003409650002041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 549058363 1250 549057113 549057121
    0x903090b120f060f06031801060f0e070f051b0f061008030a0806060d05150a0501091a1605060c181005121008060705090a0e010509070c1e03030204230306 68
    0x4880b116600076400034004800880c481000030f030340381c0090701c0c9417485c0746443c40c104042003024807890340142240400c60021900d000303903150540320018031784014455810901808248504e04680c105030321607880050148141003034aa4a40019a8a030f2140c4960804240c0b911030820701c20b004c440c1d910000794500005d10f070302203c0d441c2c409000650081000c1c454840b204900703020712440340c0c0000714600446046001002004003230340d40034034180003401c0f4091100403620a6803407840c940018102c0c3e0b940402c00c0540840542d071000180180c00783d1402d120040312850300071f1580803c450409148000403104001d005a40ba040e0314020550402107200b50851800c3e19940c00041584070b455003a42d80c650090420400716604400100c00054250062034903c10382006080700b00d540c2e404c5581800c0126000341d0b0058052402e00c880059034004201d030943c46950180f06021401c42094100d00c1d0240282d04507000c0c461507040d040c5101c403007404181d42d0603048584014014130468071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 549059613 1250 549058363 549058381
    0x50d02100f0513030c0c0e0a09021305040b070c0f06050108070e0901180b06010c150c020f060103050706080c1c0f0c080402030a1b09060e09070807080606210a0302010903090b12 78
    0x24820300031268603068000c0041c14480307010305148140414031004c14809e01c5031041010a0f0002c400c0f1204461a000c240b00210340b00e15803003607100e5894200709001805606100e05400b40c08540100401e0030300002159105021078505d048070f40341c030784848440d111183c80d503098034900d9010341e010110811009000ca40d0b030504140d044041070504600d03414460b12054001510361342e03111801c0f519011850502541001001850070400005d06155411603840544a805074842e040810078260007046c001d022102c1194003442c03184c0a08420020310403254130241802c02a01300700c0c03070710b01419030000502440c0b843c4d100da5401409410040a159144003151098002c040b00003042001c0c0890304000c14410200a4810b0b204804100d2600441540c070340990f40e008a1304680002504010781705002900503003060048036052800304d105940e0f941910310307031606c14801d481a040e0803401e164042d030001c00302d0780c02592003210290b200e441c02402d51182240144913941e90200060001c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 549060863 1250 549059613 549059627
    0xd140907120816200109060e06030f07030b06030703050f073b030106091413030c12020102090916021203100603020c01021e04090b0d0f060e0109050d02100f051303 72
    0x4601da283c810158038154880107040d5021105003040c1c0000c110103480d0a60f00300000400030401c0d40740c84d100c5c0d05842d40c00f1030b50300e000c0030740a482948028000301c0d02042c002d403c40800030744060545600ca19042c0002006000c090700c917010002110303004100c7c2c26201d4030210001c81100b0040360501a01d0313a800281c00c10f03030b10580010440ca20f44030b20240350381c2070041200401c1404408034049080e81c0c60000d102802406034011040d00c030b0100000240c00101d44001c42e03806c0307201d08281e00c60429040c1e001e8401c5101459004281104100288142c0006640c080146600702e40f208803141044206620040e80d9210017810070703107410071245100b40c00030461031072440005030410000c500051580b08010708a04294040480c2c14024826284a00803800008580300c02c41c078200307900e410105084000020780b900c2c0d214008908189000d410030304406034000100d40b182c8683c008005d48074030501c24044029070500001d0005010300740a043d00804042964090f07210103580c2c00c2c1e40341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 549062113 1250 549060863 549060877
    0x50c07030c030f12050a0b030c04060305071208040e010306020307030c0c23030c0d210519020903160305100b040911010309051608030a09051c0605090c060d1409071208 74
    0xc3c0f484030011962540c02024040c0c035a8643c041441f00c02401003505040409071094001c3d8078000041001c11781c009034000448039800c001e40c180040a05200d030040c413668110940c520400400042004101c0d4011446480c2d155002c101e000100c11084804c0c5e03c540c038010303100d103164030310640340d04945407451040714609200716450060010015800d00030180310140100f0500a80200d06411110910219548401342003040e071a01e1442400d41c05030105400c2941e40d808104529942c83c20890990600b42e454070142001d80c0c1d030b28103039a5031910200070300c21413421300c20001c41c3c60405009841185612004036600c2e01c84407030044005003011101602c0c2e80c030400e0384009910441a07440c60180803068041e507aa07214400b0301500044180d4000e41c042c000307400081d020200c000c201c02203126480000800c13a6261501420301c0c0a401b4010154880ba00049405100b0925400450b5162110395280000eaa0315100a41c07110134074071035500401c4021250400207a1a003004050f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 549063363 1250 549062113 549062117
    0x120b09040c06140d060314120f03010e1302030a11011b0f060e0a0b070c05011b1d1504061d04060e2a04060c0c0911070f02060405040e03030a050c07030c030f 69
    0x1407040d20702190050f00c0c519030056503810848030081501f60418041510b000c0d10103a8004d03d01900c0315001140c034801403041e60303040645030b400f05412000300cc9507540c000b9002000c60381c0c51005414071702001000c1014441c04503520008c000c4600c0380083c15448a1900315411030b100c1c50603602c8140c0600181e81d6810703490f01481d0000800103418180c1d26002c1d00c01540c0c1c6d90352501c3c4920340f95003150a1480d88516084508a81c401e05c2c5600030000c1e039241e124034110520980704040802c40a40103540b40c1400d1400c0842c020520b0ba500030a00c007420030840780300520440c0c1d1401800700310b6600f405014507a0303031142d0004483c640c4001011356003623010080c45200395112840d80c201c90b0031541000c800075000c0352a4a0134041542240c9026000e4010104a605011040d41a19100e4400d004015081e00440c0c00d081d543c031002500e009100141c01402048822000151a50300840701041103919201c0862800124001519010fa40c1503c0c1c0e400c3c0e04156403402d84d41902c1924a92007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 549064613 1250 549063363 549063367
    0xf0e07050a060c0308040c1a1e07170901090f060522082a032d0c010912050111030c0c0d020601030215030c190905030f0c1305060d060903120b09040c0614 68
    0x604023091207005414220340340c40d0301d615540356001440c18119a03d29000b9440e20500132500407034444101906406504003440d41d460542000503105661203510072402110400c1300010ba071074000c03000b0078030312440038a0800b010035201c3c1950182191b0b40184490350f404150700c803a103100000341e04560b08911011a00e4110100e000191410100051142540d6400310202d804500020b0a42d01000490030246c1654032442c00020039410641c85400c0c1e4482c007007555482801070a6110030011541d040c2255603038a04100a13001070313481341c501e00d800e5200d1421001c0000d4404030720f281c143c9500030301c0d07182e480c10f8103a01d0001603000600071014803c000c11034403d03c18111500f500b8001c00d540c039001c0d071442c42e040c1054207080385201040c05680250701c0f04d13882d542d5500d0000c505840300040020740c5440b04800300f82d00d01c41d44200184900e19141e200b00602d50010301c0020110b05454003440a80900001d011174810159401400d65a80003014050b45000b030f07200c115000403002d01e41d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 549065863 1250 549064613 549064619
    0x1080d140a0f050d110a090905161d0a0308031006140412021804030309020a05010c23120309030304060501092c010b060409051b03060303030106030c120f0e07050a060c0308040c 78
    0x701118545802021701c4c0d0b00c00035003181d43e59000380340c29006041c020410020341c40c11111082d801c90181016034100644048d04c401c200d4103040c1d00701c0007070001030010400a41c50f4507040060b076006030f40540510621f5a07002910911942406240302e04201c2c03501e00306440c0000c0500b5001101c0d4080364800c0c80d2800d00002154000c2c00700d48224080c0c0e401240c8019030740180303ca051129007200d1304000c45104502c2c0803940b20b07004400100c130714161300c000c60060481c0880c1040c14801190089007400000e000c0b0611000011718015401454104200d0740d032105003104030f8079015070a0302d06061282c0d201104500c880105481d001d60000003150300310101c00005d115503c2900103010040d076440c14400480130b80000707004a414141e001c1d07032541c204a00026604c0c0014411501003644480300c04054a208070008904000168400d0250325010407068004d040300389100c4480d4070898034001050f240c020321400848442e602d0b902c2070740450b07440071542e01900601c10f0b03840c0c0309810000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 549067113 1250 549065863 549065887
    0x201020a080702310e01180b130609080a080109140c0c0c090c0a120506010e15040b030403122f0a030905030a081608010503030f030901180b01080d140a0f05 69
    0x10030040000c1c4002e82c0d0136202a400242c125481e01c82c181a49a142c2401000051903041ca4840100d401a482c80c14541e0740003407040742548000303001840d60781800510020070181c3d0700070301503940468403035036030682e219241070382100c0c040d00e003010040072008040750107000280000c01d170441094007038849510301a0041114400256207806050400141c517148003544080d01d0704044c4040740d414002d500f004000203101c8680950802c0c42140c030341d4031000c07858071507204490003850301c044540d849107054100038140c0113410045000903802c04010f90362101301b1a2010b07940322035144060381681c6188003641c0e983d8000400000a0640e0341401d240403070001c002030140d482c05c43c1da52000a2a001c03040c036507510000301d020310070700c1001001401595000701c1980c4030305416841d00c81d00d0f07564090380c0740e001d00301880c170003105640000003078030602c0003203030415050b40d110200701c070782000350b59104413504501c051101ca03440b101400426203591062141411030020b43c0b920034100542501e030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 549068363 1250 549067113 549067159
    0x8211305120c0c10120c090b0901030e0a05010f0b270708060d08040b0711030d02030409050a06120b04050c010509090a0515030d0503010603050c0c1b13110d1401030201020a080702 79
    0x16607401304a0707004801710110024000c1200001551500140031840c02900d10468015005846d0501d40c94070021070380203104000b1601620740002c028042903511024480080c040c48400c80d004442505008031190101c0c1000181c0b507080c075824a003955070305038003200c0c141e0b00a4a00c990020b0b40c3c03030000c0d0106100c44042c001918040d4104d95481c02e0616007012811f2504a4440c02500b142c00702d94034082d000300c156011100c0035640400c9941e103011301c0000a24550308200c2c2901010349620050043c00781c02d1902c0313a4801c104540c05a0b44070360065959000d0003640503030280d2074500089840140c0d4200fa40c10801542000b42c15405400c0082d0a000102d0a002c0002d0004401000303003951500440340c010900c9820170f890003682c3c9183c10340b140c906400c01c02c1c080b07030584800d2801c0e441f4460918a14146480100552624200c140700c0a6118000070003030342e0300f01407001138074610342c0c1c0e9241d0407640c1c160014002d04410742d0328424580c1003e10203903030002103030340c1d200e1000111000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 549069613 1250 549068363 549068389
    0x5100e190b091801030507030303050a0b090c0a1701210614041b05010918050711190606050a30080a17130b06010c0c0308211305120c0c 60
    0x1c54903803582d9041d010301c12990306400545014820540040000c2200032885205603500b40c84d020880340d82d00c0605a015007a60744d041c9800610203002c0010500c1c0ca000500444406550380012188504190b0700b1900d400303005400c004007028410760441c2c0000d5030382d100c2c00c602c11000420301203060040c40c0150081200c00307850809403410740540d061003d00c0600048c0409080a0034818208001d4481d800c07860351040300115a40c0021480d01ca001380704108050940c50116403a11010100c5204102400141100c2980c02d00d0008a02450842d801c2815900092500d90f000d01c8592040b41d40070a1110510550486100240020805500060030203141d582c0b11607501c4c075550401803203071107001803c01c0300324007100c15403800088190b1050b80c0c0103e02482d000282c0c502901f401942e0b01e440794401018140300144001030010784065107400707141000800040d640d509201d108103600520001050364100c90f2016803940100d101616010f607240d421250003041e41e17000724030094402c807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 549070863 1250 549069613 549069629
    0x4030602040515070b040303020c0a0b090f010b031b28030c0e16020c090c09090901060501020613080307050f09120703020f0409051b012a03021605100e19 68
    0x406109505015000d03c12400481140600d01a119280c3d15660307240a03000804141d0002098219440c007000000e03446a004509186281001c220b0903a5801d5000e000300140d5003009000f1265250110300f0606815420207400c00c940300da0000c00c15100141014810700b401c45002a1080c00d40101c548006540300d0119500307264103103d81d04481900003040c06200c040121000321409034045101c06040c40141c0e00310750151204908403e10b4004c1c10141030700000028200401c3d898150000c80444000b80c00391020354440200e04c5181d50350520707001c2d1440001708085450b02c0e11500081079410840c1e4081803c1440f80c500103032081c1882c40350604982e029200500c154070301003e40840101e0211400c00003142d182d65404d85400d00d1840e00d55480407100f00c41241c5901412800000340440b5406074040d51000002c840f401018020550040c860f1404100702e072000d03200d4550550b00000d04806d1001b03c5c2c0e030000c50b103c528034459550003000c000c0072080e03440014150280070709011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 549072113 1250 549070863 549070867
    0x140403050d0e1507060e030c011415030706080f060d12210209030a14011404050a110415090203040204112d09060f030a021306050c100515040f1104030602 68
    0x101d18000d180d2a002e14180b48a803555402d0690f0a09401049600b0305901540120300d003c2d07103464090560040700c03650320b0154206403003080c0054420300c02a114281551448034076544880c00e0503a50400e501a04011521840101e003040791440c0805034804001800e25a070f00e08580c0d903d41c03200448102000204014400c8034406d40301004000183d0040310030114141910040001d9507152310550280c8544a03401081024000a411914034224002c44000b00e9003418a407243d918008042c0c02d0342c2444100342c7d004440d240602400d00517841e10800c04004500b00800700c4020b40c40035100300d902c180d540362140d0302c900031500504204270303101c0454a454408100320201114803481030058500c010801980c0c2035445000382d0f051106103115054895440380b02c0f0700c3c0207215121000802c00dc071900f001540d40d40c00300c020180102d9001c2928074403803c0312100f5050f13a00940d45180c80c6c1c3c1200c006130040707051035071200e001c3c0f002200d004902070341800b42e41d04084d44290006c6d5045500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 549073363 1250 549072113 549072133
    0x6030204060e0d11122112070e06041a0909040c050109090b03061314060a021c0504020906130906021209010b0604080705060f040e0925080a1214040305 67
    0x2242078000700240588441c08035000f540c1d9070451061282e0b1003984544441204200c0e9036000700940c9880c004601c2098410402c2c090808081e508010b034070042602030710300040d00170742c0b20310030b91840b551000d080507081609000074038540d51030182614000041c14809100315a5901242074002c84c040c0100d1508181020001018003034960010000f450800c4850481c9450003d80203500c03003004101001095450710b80000c1c9a01507400c070758154494001844101203455008249183c1c180b01001400e04618005100351082124007943c0a00c0d1000020050b00f0b00822004200000e8080046d8404070761b61034400326007001c1404880401c280c0c00700400c25809100b1400d000a040300d07040d080900d80098155260340074002c1600888011500080202c0c1401c00d5802515042505a4091800400a075540c8980c40c0380d52a04e020f204036210400d08200700c03907500b9030b0040409401441129103461000c000703100411002c115075185000310401036000508040c0d4810320107840400c403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 549074613 1250 549073363 549073367
    0xd0506031c09090b01050405120610050d0b0403140904060905061503010b032e03080a03050109022a0f1e0105090d0503011e0918051905121b070603020406 68
    0x1c0c5040c4015400c54002201840d019080902d8804480300c034040890410f1004004035100e00503640910b8018240300720241d603100011812500c00d840d100c1c2560a602c1d03440c420001ea80c0300c500c10183c08100c035500402d011900c40c5030710150865007202d86034603250b00407010400301c030106e60280a0144d5a0004c3c02114039044800214003000d52141508550600b100d03c1ca0303501c03010b0170101202c8002000190086554440401c008221203100403156550f42010784940d40044401000246060004500d5003454801e441100d10000c01800c0050388040801c07504140f411441441b0388691180c1c040d030958100a8101c2a2003640d1044814940e003050349425036201410b0340c041341d004540c00f0084241c2c441c00b903d04590110901100d515201e00d650354801c0303066005080c0d0300d400c0415041d03254220320910952030344944125901c41c00b5a0b0800306022038a1003004095401049001302c032000401c0c060900d402c5c1c008007030340d01c2c4280f82050a2406120b680298003207a00410f04000a907 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 549075863 1250 549074613 549074623
    0x90e0a210905102c0306010b090112270614181501050913021f050301050102100612020d0203160303021b01020d2102090d061a180a0c050706020d050603 67
    0x1000940301c62040440020003d003100318004e0b4412002d440c00400b81a4195804c2a24a64100082c0582d1050f5840e461141070a600441c2010302140c81c4900310801e13080c0302d11802e03070030040c804801700962001d594030b841c41088606090303076076942700c00b03000015003010600c040c00707500c0e200860b061040d0301030070080c1001c04107001e160801c003c1a004100700d8a500c8061640001c00a80456082481d8400680c0c9000d124408844d40740c9288082d4080703540110056040c3c5034260202c81c0804041c602c1c1c00187c40190254807400300362003039075500600b010361403608501e1008049e0342420042d2211070320314038420741c41500181d10185100c4004116403810f140000700a20180c4400c0c40500c80c0601180204c0240d40503505952042d1424048a40d040c0c1341d5a000081c125840f861071400c005d4003070000c00f2400c501d00f0520407601a41840c058103010300011050080b0320300356403610380d05401805c800b400ca00a200c020011500014410b200401c40310401090010311400e14005041c500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 549077113 1250 549075863 549075869
    0x702090709030f06020f0f0c0a0c091e0b041113030209060d0201020318040b100206190213120201020c0a0b0c0c06091522030c0801110405010504090e0a2109 69
    0x72104848050000c2601010001e015542000d0050b80d2182400b4040404d4801c046552980e40c402040e4103603881070114800d10410301940303032502025168248801100d0400b903140e8501311814043e5000c40c411070300241e1a205000344000b800e00010041c040c40d40e44000c5900090064520b82402140b40c50107c19802c20800c1d02d101c190a0000d034000707580d03882449400b840d510780280b50080c1c5c40d13030b07950401d92243d034001d04040017003106c80078042d40e210400d0f681840841003c84420388a000705100f6036448020700a21a0700092815101c4084100c075203205a045002e070702c000c003415403901a0014020110103001e03642e039910a010840c1060a6a070900c1e11582041082c06095a1490780c03072a118860b0700e90590b9115013080c85803109208904295448401c0c10400205012001700c03020111954040203100090610200046c503104038003901313010400a0100344078040705a44501e145004000465001180a40750f0242d03510003128400c4104151b000c10240c1b1076030188101d001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 549078363 1250 549077113 549077117
    0x106080109090b070806041e060602060903091f020102121005040c0e011d06070c09090506011d0412050c0f030a020c010203120103060e071a042c010314030904060b07020907 76
    0xa50b00965500c12144401400500c20882c1c0705012032810750b2658440c00804440a070160107540c14400700c43c000d0302040c41584054021980002d203404004000c45e08082c000401410520205604800406002c104400210741d400d228000805180301c040c6401181440e21601625251070104001e480f1500d8170b040403c1640744102400f03980203c4095042d442c4214040802e042d20740125003140100c4802402400101c0400070b601c0f040b6500502c0c0c80e034056400d0321175503a250b040ba1440482100406098280c2c8030b00001c000c15241d031058030502420345400c6281401e03200d038162908400c800350310385503040080e80c07100c480c0e0100404c0740032100038000f45040121000015549170414800544519140c03429012403520520041026008281c00c0030032500030105425410f81090040d410740c8840b54844024407221900c17001100c11442c01c3c211016802c0d5a02c40620b00120302600010384410300508002d81c1d1030340102000f40001001231500c0704c6c103500402c100805d018104500b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 549079613 1250 549078363 549078371
    0x606112d0f0120130608190908070b010e090307020613030f0506060405240f0d08040914070c110409141905011d0706030c170c07020109080316030c051203040b0106080109 75
    0x40070400444e29030803034000e403c0900c126aa403140c6914440004030220300018900580281042000000b42000c207020311000d140907030700e613024400320020945058403250310a0055000528000d001000240e0003444c03810b903040da5030740c0c800c8900c0590201c2101c4540201081045a003064400d690f030010b204002c0d0302c03105004404062404620000c190702402494074190200d84410301d645094961065020b0703510780d03551100100515600d010300c44048032050201301460f200d5040e0128180d080054465403411100c1004003c0c491850203c0300c0100451507064103800138040103124202c2d00303400380c109a516140003070856000746a07985c00036500c1003400b1500280000e819003600c409040001b00041410000d030ba4400341c00002c0364030504018104040141c111002c1d2061328402c0e20341c650065110354000f070301c90044880b210030600307945115001007841429907010881c0180305858004c158000d241c0641c0c0e20858041d54004c821100420015034081d01860040c546210100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 549080863 1250 549079613 549079627
    0x80604020301240b03040c0b03010605070c080d0f0e0406170a021c0804030f05010605041802030607030b06190e030a0b090d0503040b01031112010e0607030606112d0f0120 75
    0x1100f20740d0301a00340d480781c000c0000340401c024100c9801c013404007900c03181d44a41e5036200c020260b9100d01070481d0303600026100000c00407800580a50413410700d480703205022114010849402484140a40d44180c554900083e2910110540c1208d11014030191041e00040d0050000c001601008851031025403403903080481c3d8498250303800c2da9405000c94031b1240650418a01400041e001507a000349007d00c05141410704a0f072050390f003403082e401d132402951b0f02c01054080307a400310251608a0401c101c09003030003845040302c10788001613042085800c0040b0300441e2404100070b10031100d140300d500610a50242c200f000c43e003a80482e203421480c40ca81030b590814000c4040c44001e088140d19081c404036669510540360540e500d0348020041243c01c401c200d503030745406980d82c07030100703103010350105d005031040c8181069004c00340000c10481d80180c01c4552200da0300700400b24404104040440040c070180f02c410249000c00d030010a005540480c580e034000b06018003660712a0003002a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 549082113 1250 549080863 549080921
    0x140c0a170d08040812010e010906060509030715050409060b0d050c0f0a0e01090b0706141302030c151b010903021b0f101407030815030120180901080604020301 70
    0x801034010051818007000c1d103d038a4500814000c6105581030346058074008105000625040c504803401208203200041d0b64150646051080350282c40e05074101801c10701a0900081d0140c41c070b0419807a14526080d56020840c08481d503035003050003089400a80d40c0c1e410250350281503006854078085520b41006c10462086601c243d01152091081540d0034100c107a000300c030420010030750068003c0e0303070300524940000100405030220034a00d51200c007082007560301c0403500c0c004940c050300603d074000c070910400040e0310065409492210f0304110040d01d00180c04c074074405030b49283c000414068254035001e42068030031300041e01d40383d041110024040d521030612013400f40040c1c4007900703c203d09a60440721500382c61a8904040d00000c1c0c04810540e100c100148641d40ba01304080901c0315480816082c0d682c10f8080e1001c80c5010070201010307203010300081030110079010019442c8075880300400c0809900341d00907001c40d003210041009600b170030700400905c007141543c2000d05882d10510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 549083363 1250 549082113 549082123
    0x908032b0216260412061a01020c09090705060705030a080f1b07140105100e010f0f06140706060909060b1f0c14190201020d03110901050a0c140c0a17 66
    0x90400410a450620b10b20041c3c80d4494071000c014080e41c2d030381da807a0214a02002c07080c40d03044464a2400c290030082241c0c0f2a100e4040101c141d0291150100d00c00400c101500081c2001445010b4050006a11396401c002032404038030880c003440e00d441041d42d019040b88001040e8250302c440210400027010f61a0305868114590303d51615100d1640782010080030040e0480d03203002c0d6103028140094504808a00000c0303920183d20054140e80766062032549420501ca21403803607401040c01d1120a00a80c91008d2070101c24586c0340c2415071580700c0c84195003651f03100075101d995400c20a000d006890054481c1c000e02a41c0082400b0700c0c0c01556504e030480080c0c0f041c100401400104100803410001e05141c10004041701c0107040030545610034240c040c4400c0307015110304250702d00d42034003902800c3d04400e034408403e0306025544e80151425803012201c28104079078000070800103054504201d80c9070500d4401031044c0d0b50b6103010b00c007d05c0b46030b80141c2e6002000032a01c1a9110300094 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 549084613 1250 549083363 549083407
    0xe0102150108190f020a030c05040c03020c33040b0a1d0d0f031d0105070f0c080d0504080d0c11011508030403060f09201306060c030f0908032b02 64
    0x403c0c1d044004542c10010074100041800a510400503100081449035400d14001940d000307d50030000e07030894050a804034031800b0b114280035040440d02820340b42041106183c0420b0840c41c500401c1100e4006e200c50324412070302155510404030a006402e48580b02d0411940c1400c010112250641344400c1c0e0f8231b1100d01e01d040b08000010007882001c1d0300c02d8010300c0400003c0000d4a04100113008014041d01c0100c1d0090001788505000301c00b844e10400514454582180794113150103107400c0ba0f100030b00001002943c282c2c1c0100000c2c010041c0768400c0c06c203541c115560b0b07009403120810205007035841407240400d829014440501003014084200c0d4100c0e9440100001c42100b4a000040540204540030700050b903d5600460400000300368018040c004540070b0040007004050441103a4141c06120f0014a00c1d41503c00000d0081114402203070042c20b210124036660701c04145168001007540340c00328205040c40c155881003804240395421003d42c103500340000d10800403070000300c1003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 549085863 1250 549084613 549084643
    0x6170d030f0e0c101808010f0b040204050114030c1902060412081e10050a06050a0f05070804030b190e0114061215071b060209181504110405030106060e0102150108 72
    0x280090744518054032103035030200c000c1401010796960f50006d89000f4030041e02c41c015500d003031a1454102c0d180520881d01910750503128900464075440381d085050b04000c214046d14035080140700b00102040e440381440c2d041e81c0c1d0081100746440e2a000640c1c0d1011003040d028030100304203204126582c0200c00100c803211460a42ca50340d60100140004003403a80b081d508400c0d010f00c089042a4031000803c145103050304d0741c24032202505811159881020000b1300415030500045c0001904404860380000c040881c81403840e031013022404c1210f201c0c0b0140e44180c0c0d942d035050082507001e01007455104804032200b181d00c00c80f05030000d803a9110812075280380e001444c001400d15010b048064666050040272501c00c1c64940380c520300035808100da00e442001e01c0d4114800c100c6007941c0d2541f0542c400340600742841441401c2c0030140c04484a1501502030a10021460361000d201e43c500418031075a410307188a07201400a8101640c141d04000113800cac180050002d9070000810801e42100c02d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 549087113 1250 549085863 549085879
    0x180d02060c090f190b1e0c07150c0213021806070507090c05040b1206010306090c0c06150e0411010806010815060901090305011407110f0c040f06170d030f0e0c 70
    0xc030009696203042c90000c42c90404c00071004c1911480031000c0e0a048800b05000118088140c441020500a050303200a081c2c1c4044024015a01c00145c0030b1820500386c20300000600166000681d4640803d901022455000c14031841c0c2c200d4030703e0460201402a00c42070302d0301da0982c50b0070703450785081e010f40d403007050302c5805180c1014440e10072030b402480d051507040d455210342c0c20210800c800c20303640c4c240040d050880c0858000a20b2041502c0c1140548821098122940d601c40152012070b00f110188a10180300187c840142504580300d54400c40c481e19940502c0740014044120182050b81008140300401441581c0c00c0700790141c0301d204440f001c1e1503203800750048881d103006400040c02035080030310406074003a0517060341d80641c950780c03100c6080c2c1d400c290b2080d907141c031904603066860b40b204014010fa800c0c264040b40d0280030300e600c00320708507071948003503094581034a8040c0f840390710140700132400550610411400074900c91045c8600d9a004141c0d07580d840000c15901e200361a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 549088363 1250 549087113 549087139
    0x30412020c10020f010c14070b0c04170c040c09030b070815060c06040302071a0a080a2003100509010501050406030b01020a050d2102040501090b0a1205180d02060c09 73
    0x3000200c0c064035009007030411000006000035240c004d020a01c02d42c40d0301380b40607054814028000c20f080300408180c07140c14007030b56031251424200c01038071010039039801304000b0481a083d11056024001140000c040a44042040c082102d000403480e8042010550302803002581019240b074000e0b60310710341401140c4030310481c02072000320151040c0d401100041d25212450002c944113200c0e500a03000e40d410a13680b03d41c9000140500301c1c40d2000560b00f00048202c3e6070040000701c0d04880c1d46c4000040043c0025161080159003d1b04590b010401104000138001d0740307003422014000a450361081075241a0010f0114061409a6028940c0782c24504c16541d1023000303154505500305044070b006c001d85c0440a0608030b06036074004d120a980c0075100c0880c1a41d4002c0702c2c00c90702c060755810107440c034001044200c0c0d0800880ad4040010b0400511407026442c00380b1400381070316840107101480700e9940b09181003004000d120954000104002140e0440d2094884085041d18402c44183c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 549089613 1250 549088363 549088367
    0x3020907020309040515030f0109080d150f1706090106050604140409050d030b040e1501060c1a0a02090a05091b18060c0109050c0a12020103020a050f03130209060a0b030412 76
    0x1690381c80300d8000d8941070401040e82c0c6c0c140d2001040d2142501522a018040e401c0e4070b090314035210000d0080641001108003142540d8043c000c14541c40300d031a20b00303d4544182c1c10500041d54030581c00d0030b5550b108020124401c3c0440754000f0054002045018031f4100807034200c1c0101d1281030802130301030482d0642520365801c01100580e000082d00c500c0d151140c2d029000300040c10709980218500351422948400c001100c000440302003054240c140e00c0c104c01120b6540d2040000c4481d003103141c03c0258900c40d16000240104924040961203640c14010310a1410b0198405803082107428240b2902c01d4800ca114640b1004007a0b802e5502c642d108603041d000d818800480d90030400008401e0041c2d8010f40c0051011072082e01954004040201080000c80d041e00543c1c2d507540008204600640c000c1d4010543c3c210300d41000c03030920382d1070059480d06170421240c100c00d009100300729004516002070b00c2d65120904880d14150542000e0300c2c075166001c000c00043c0403400740e5001c0c0240b14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 549090863 1250 549089613 549089617
    0x30c03020c030703030c0210200307022a2416080f040303090f1403120a03060909080d050c0c0c012a080d050a14060d03030b030d02011512020a030209070203 69
    0x10116001c6a50f0b9078118607004005090620024006015038168110f0340c52041c0161080c21304480d0158080d40700248002d052944043c00603025445184411090741c3c00840c2d1401d00c01c1440c81e00c40e02e00302013480500031204901f02054440321020b41000c0c055107510010344141c003c102c0071a01c5028164545000944501002c0203182071005c14000100f50380804818242d4405840000200f0398400041d15901171003aa581e44c540c10140c0c07050881c188180c0907201c1c0d00000c6c07a021800c29510b0f9241412241c0f24442910854000500613000031210b02400d0b0704917110504451030071409000c40c1c0e882e100c15140145c100841000301101ca4403101e8416482d00000d806e541040380c20516050006901c0007440c13210490902c00025100995445900242146007090b581140d6840b8104a0450340d1000c04809244d580d0b40051000e031801c2008000ca168190000248000840904030940216510040b028130a202074000180c03034103201d90080b2030b8181c1b410541e0303454001d403d0303040d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 549092113 1250 549090863 549090877
    0xd1706010c0b0a0b031204050a12060906090b0115022b02030409050106091701110409020309011407020c0103061a07290408090108070804200a0b0f040e0c0307020a03030c0302 77
    0x5003041c805010100c00d244d030245850040803411074500702c40c036282844850245100f583c8c3e210000c11400c11283c0b000d04900d01c055441240c000481aa10759218001c4500e5038100303030384009010300180940500c6004121443c10380e8002801000e00b00e03900700004451500228603015540700e0301c8070000b8000c000780c4000e441c115805104075038441d60010180cbd4402d00c03031400103040804441e0f454038011f2160b880c500145e5011180341505201e040006944050041b40c3d040d940ca51144155080c000ca0280c0141e44507809003800e000c0f800001000d540340c40d000480e402c0e002d04c0414500e8038005085440079980f10718000b166400141c94654440c1c5403800c85020108013204010800210380c00074072101c1d40989501c0e4080d290900202d5161000701c1d0001e04d0780c0320320380c2d08051101e034004010050394001031900c01c51584400c501d185c0368000c0106d64072621404034042c4880c10008407801c0c0e100d21088480e41c01c1d89860b00300255142c040040107010301d40d0350402c42c14250311a030111404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 549093363 1250 549092113 549092123
    0x212060111012c1507020327060a02010501050a09020c03030103020405090106080f0f1005090a1704080d030b031c08160e090c070303050601030203070e1e0a030803040b06030d1706010c 81
    0x1a8109442c402c00c038851440f00e01c0303510b03000300024540d00300c44190100c1c1c00348003036034019814000004110141100c00030800c3c00f0340d01014080130410384d9000b0060450001d19070000c00c6030351400050180c140000e4025006050044c8031a0007423450020903241100e40442c0c0104858070f6822206006002c1c0f508012031030b0043d0501050344940000314040030149a10841d030700c108801078400121a000d0350540080e0304030034005001304407031260300802c50940b10365091030a550740000318a0501c4025042010039102c5d06890281e25050103001103030000d203030b540d555030301c1c081328028100301c4024500301c0030a0707010000c468194401c4001006405c40a00482e1060906140d0803c00da003043d04d040b0006401c01001070300c1940b2a0003581d00812180e00c03240d414001c02001c0100080c003018001c400060f40c024000e80c981d0300c1704a418001c0d07010b03081540d5203040c5401d041300d101000500081c02075014012031004140e10031b012840b812031000181416440c1c020040718042900800503103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 549094613 1250 549093363 549093401
    0xb0f0303130305160509270105010f05130207020919150611060714091302090a0f17010b09160201090f050c180f0a0509100207050102040f0603021206011101 69
    0x20225041c1d040c0d40c0940b4060740803201d00030001c03d032001030000c030b502805800c08000c50100e0003240c5282016000e07035400c481c0601080c1ca108005c40d0031564268402203605208200822041c01d21110350172803952501d1041d1701c0d2500c40e4002caa201c4901914001180c01c642a94900c104440d44c481030b440040c0c6580d007240301395241e43c0104039004040c55185240200401300d4401c601503040c0c0e000980d400d0300b2a5040400c610104001c40080d1440200ca00340c0070055400f46036903800407940940203042c0c04000550822640c5043c9100d8200107500580c507000500c800741c5c0d40c0d13032100e40d8050701c201c2f07407002807004688003240504480c9400810812254030020100702e404075004131640c101350b40780710380301100701044284100b042c0c51032001c4a034410301041d8208402d1700706c00c0d80082400100d40d0582c0551501e14126480144242e4081e540840c0a1001440301c8442c03d008000910341507080c003514407a208c81c0200050310306410320008900c10f001400c1e080d00918418011045806 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 549095863 1250 549094613 549094627
    0x1080c0d050c040f14090105061605120d1433040c0e03120a05030411010c050a030c050d1d040504020411040b0d1805210403060603060212280b0f0303 66
    0x21030150040d0064201c00b403200180469038281c543c17038030030f0000c0300200a5101a443d150030b2008562000c40b40140c1c10803038881d0700000c030304108034103400080c215130800e03a2203502c0c000d04000c0340d141d5100e241c4a0f411480a0054044803500200c04103400346c5100c1c2c04002ea078421510f00c42c2510907555410500307208100c00116040f040740704c4210802c0d0300b40c3d040164507000c1c1d4200fa00c40d2813500004140300344085000314400d59240725030a10181046441c601c8940c49080c50007401d500c00301c00140c01010803404206050203403d0450019041c14510750000700c100c0c49036188145031150155590707200003015075540da000394466480002001f230741c0d66101c80c01094283d1000a040c0c040a040484050420b03813010744000c64030381c008026100807020380c10310000b01d0103245140c503210102800040007090080c45400015407045100595072030041c444502c1e4040020300c1d2040a074242160058070b14004521000a0b13030040c02c0c0050460310450010300c0d140c1054401c20b80501c4041040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 549097113 1250 549095863 549095881
    0x40b15010201153c0603020c120c160509040c060f0905120312010e060924060a03020406030e0f070b2203060b090a02070f060506030a0f0303200c0c01080c0d05 70
    0x20146601480391400c041d07011060852003012050404c84104042041c02c1140c0c1380b10b40d016168001024065030100740409032041d116402807260750709181c005025402e0340d00310001c0c0c800c0081000b0b40c0ca0840d03500d01911107000c021040d01c03500381403000c08100204140c2c0314800c10405000002d00c074954100fa0044255525049a2950b11445030f40e82d00200f8086401000307640f19001c01080b0441c0c56842c4074444140c5440d6030031640d4220b802003890b4040c0d80e6074034060600c2507410307a030041e15030b444e0200007820303103100801d80d00c450340010249140c00c0c000415260f0587d540f0b0b848050f074031914880c0001c1c0180c5042c81d50100500f68070b20120400c02da40d0400402c49808407600b183c01c0c0c45402e00a8100d114181000344070986c0c8242d5040002e145030030055208134018103072002507a99850700c40305c40e15441b0f030440009a03a1110842a030f914042c42c80c2d00f580103541d9841c103125254084e1039498414000d014180321410000510413055142102d00141c403042050002e400c2100203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 549098363 1250 549097113 549097139
    0x91201141608090a110a09020703080a062309091204080105010e1006021f1d0a02011209020d022407061a150d050a020c070f08060f040b1501020115 65
    0x501c4810004900024103184103030380a40c002d640b40c001030040342c0c3c03c658400c441903000340e10b110f030010034040380060140703201e01c06009201d02070740b5075540d20719125000000322400354000c4901c805003814020380e40582503800003813011095074544045d450b9030748034a14060515000804c0102e0004003c2201101074000074100d81101304070845503100c0d540d2008100c01a4052200160703c1a9440e0f0352420702c000c1101451506a88000342c5044514080108a0030303000c030000c0b659100464003021540e001e4200da4036440c20401c20840482268006880082ca4504c080d03c54400b4004010b40c1148202003000e00b0005560100c0d600c0c5020b03d8140081e000f01c034450310041050b07003400202ca0030300301c281c0003000300503030041860481407901641c02041c01a1a00102d1a0300307004501d0701c0e40080145401401c9611412100f580c54103105c145003071402040514440360300e10a00000548140106400408051000056640480c0101c1c01003485111340c01b100303000e904000422400c4404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 549099613 1250 549098363 549098371
    0x9091b03010b2d0a18022a0a0209012102090a0f09031205060a03020d08030a09020310020903121e0f070b04030c1e121103040306020d050126070501030209120114 71
    0x40303e00000007240100300071294544103401c0c4050948400d44a00c0d5840d50017031204000014003000b4010400120311115206251113007903c0d440700080c10251301e84880390900404096030401c101041d0302c4444c0300300d0b4030ba0f40030003802100c414010070f428881039004041c07000c00c0c030801000312245a06000b0501c0710a1001440000d20f0300010171401d0800d07440c0d16050303d40103005071010080c2c5641c0e28201d9403005100d018425521a80c1c00016a40ad2110304510401500056240d415001c101810b003824482c079040c079120100038034501766070720409211485e035102401540b43e1007500700b841001c0c8030b034030710040c4540f0200c002c100426030440310036241380b8041c0d51958100007180da00240140740511025241000d2300d000302c5580d80c4204041400651044141d80c1425a00c3c0c0c1c9681c00c1e60407140c0f03004140d0b134861005104040b40320480b80302d45644002e401c401c0c01c1c0c1725038880d038a4440c580103650405070009042c0582da206d1505103105642c41c04020841a400160700b2080100c00b40d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 549100719 1106 549099613 549099679
    0x30402030a150203100e011809020303071b030b090d08042405040501050f0c0f04030201081e04050c040506240d110c0d0e09091b03010b 60
    0x2d10b52203840303a21807405612410414079607641100b41d03400455014000c1da004105160050400382d00348400b80304000b82a0b5024000319095100e454800340220350070002150400261058200480c0c5c00380041c4109522010f140307a807201101241100043c0714000880c0200d444a0751803800b00741c600c400d0110304104050352800350340086038140d4590359540c003001003044040740006d900071001c4040a01d0070f440e01030709040314001d0303010107410040903070005940b040d85000c4109079a07078041024481c0d481c1c43e1603c155903404006005014504001c0801d03600e040c003000d41e56198500c101124400c400240c000a0281c00c0811f04101298540303265070130003c040c1c030007082e89044038400b908084910303d4010f000d803058000c02c00c0c040d03200c041c2003100d801000314010f04000c101600b402641d026142c000b9000d481052556540a411401031014000810240900c0d086000c = true := by decide +kernel

theorem cover : BRFrame.Cov 548920863 549100719 := by
  have h0 := BRFrame.cov_init 548920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 548920863 ≤ n) (h2 : n < 549100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
