-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:35:31.533519+00:00
-- url     : https://prove2.me/submissions/4b7110f2-a7d4-402d-a324-88a732d12ed4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 9532381 ≤ n < 9712237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 9533631 1250 9532381 9532417
    0x311010204150905010f0e030601090b0d08040303030b01090603090302030904020304061b0207050103060506040503100506030f010510050a0806070807050a0c0611030a0e06010b0a0806010c0209180f07050310050c 93
    0x704007903d00700ea54400e01d80081c0d810070703000b40014800c48807446003503c002d020b0101e6902e00b901075030240c02c1d4414202c0d0300c40251480080014140c600800c0158800d0700c000ca41c00aa200c000750240d0001d500c8041454100303204800000e501000b22240048101c44c01612600e841c100140142400c20030010f000600c84075203590a40c00045000403100309a0301480b03a01d40350001c5c000715001e14860581c042d0303c20341c40100c4501054000c0c3c0d5100c80c002d0704030f445a0416440d51070079150f0a6030b502d260592540360511107410626001806070a5010040c01c00c1d00b0803c400a005450041400040100200b20001070b944240129080160851402d001414403031102100319032041d99641c150ba8030300380741220400c60208000303041701e00c48000c0301d06100740c02c40d00781c0740784800401c528100a456140100165038040c0000e01462903442c0140d02000b40707040003840c009104518095903440803004100c07594001410000074241c1c00b10100751621000001c00c2c05005a2158801440c140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 9534881 1250 9533631 9533669
    0x30503030f0108010b06090105030a09060b060a0507050606120616050d0204080606120705060708070203030d06090906050907080d0c05010f05040807170301050d0b0702070e100f0f080304030311010204 88
    0x48407150603903401c2c02c02004020302c40020000130784524a01e0741c1c046002440091000407240d40100c12080c084c1101040c4d400198002849a5200103d5807000c01c1c00403030100c0c2440010005150b201c0c50a030f50720000c2192015030603a0740c40e4000c000340301e800300240107000304030721030001c2c0c074200e1813541070640d240c0303468415441c0c44020847c0d8490050f8280203540c090500c0000780d04088482c040e10251034038085031151f205c158011442640c040c03004100b6645008100e2040c0c0004022a407000150f9010764078012003a40c5010b4005e4000f64001101448001c00104400442580b2800c0c0243c1318a0749207415409002084081c003603a40c5480104024083c00328000c0c109039115280c01c684205404c04540340c280028040d05401c0072100c58044000b50b4151402501b000d42401201e903840da907040c24103100282218203011540180c0410807100141080403005018484002010b15061501440e6640654800502000043e10440d03480c49029411500035000500c0709200c2c41c1c80f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 9536131 1250 9534881 9534901
    0x40b072102010917180105130e010306021b1506061303051b01080106030509030405010c02033409050103050319090b040b0a1704030e27041101030b01080708010e04030903050303 78
    0x41d040d0266106800c0c401284a8941c4002c100c1c0c07080c10000105c11120100c41c001120f05030032a0903403201d41e07207203108045012460102d60714000c40c483c07032026035982c1004030f00344540c0b08855a0003089510104112802e1010104c40c00e500200a846d4113486002142000b170260300ca81d44040c000d4001c1c0d821280c8015034407000a5a009401c0e299402c2d5a6642c000072801c641080b200b10005403c28802808558401d440a01d041400141110580c05200d42901218021400414081c03500e41e0092948514400b4010b00103000485081040b580345854158aa1080d010301a010368410390f040030303074140a00860406008402c6800e616262900b07142180345d8480a0301601054114074110075000703890768021f1103140e05a880c4a60b0003c41e200303021400130007944040da0560065000c0c0f031442d440e19540303481280a40e480132060b01d0304400140031200260f001030304000d510710410942d50341024110741100e40361001030b011603079241000c80d6035010380d42000b01140400800e1280000c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 9537381 1250 9536131 9536141
    0xf01051309020d0b0321070303060e071d0f0603010b0304020a0308040b070302160303020d08040303021b0109060506010f1b030c06050f09010b0307050d110307080109030210110f040b07210201 84
    0x4001d10b020010300e0411002c055440c0e104508072030b00505060086c1d01000008006005a207219040106400b5103600c01c070f50440608035030003130005e91150901440708505204914240e0401e40301c0ca401c03c4074240201e1428401404ae0006842000004c60119100c070300b0441c0003140c00041e1151515200c1401a00d2903102140590040c4180d0a02203500740045540108070b0b40d1540040c90500c061050544519000403c01c1d4103040e4240555151010710180c0900c401821030000a0040140c0c0b1b40001221001303081141000b62414070345000d9030704000c0c0d4118050348002071171400801e901e403c4500c07010817603000303024506010038400709072280c040082c0205c5004000703000499401c030516658031400e118041c3c2c003010350884100880d01c0300d240d0050201001c0d041d9184fd644681c034150944135604003c0300164001c1484030b40b8030503039114400b00c071002c081d04103142400a641c0c042c180e000754000d00100d040b001842800300000c400d01e01c80d00c0464602c810703e03407180380c02d8041e000701 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 9538631 1250 9537381 9537397
    0xc01200703050a0b01090b0a030b040303060f060203070507090c2a020a0b040e0a0b130902010201140903190219030e01170c030106020c0103050408070f051207060b01030f02180f0105130902 83
    0x221380070002c95400401c2c000d10350740c450081c04031030815245443d103008080010b0001e4041c1652807502069004035064054007400d402d4005568442107450300718035006c8150301c051700240c45c0002d03a1241d0303030303202140e0300e180c145500c50300b80c1141111107803824451140c40020360142c80c9440c00254004010060011112458281d442641d1b0741400e140580d04403080c40e660000c074921810465281551107000035a0040c1300000e20703403001038982e11010704142d80000b6130798000b043c1350041c1c1e14182000e9143c0c21440c8080d041240c901403003490000021207004043c000c803403c0f08c01c801d1348210154a00b84007520290070540c00c2002c15101d907035100780035950042c00f0300c00c0c00d405594080d000d143d005992102c5044d140c40e03401d85400311018000d900c01c60711070140141d4542000fa118025048071030044000150000c2500700241c101c900900e0032181c80c45c01803003040c440404444c092500c00d0419a50b14010f2000000102e416101d02400d1000309106188080341d12500f0740d018000e02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 9539881 1250 9538631 9538643
    0xd060810060602030a020d031a03010f0504020405070c0302060f0a020d1820060301150c080d0501050906010903020907080901020d0c08090705060304080322080406030510090203090c01200703050a 86
    0x2502c40340100e889102e1401042c0259214a9001010910071380c00303900b4401c80140c0c1c0d44900c0e40714000003825541c0210701210310549490500c41545018454190030002505020304002040d0364040d49401c0001e00f04008075290750001035848115404942e84485001d1040104031803491944d085611031850030b48072100b00604c2500300031101001203264500042c6640c1c10360b0b02e031040c074a031148042000c840400102400c42c000003602c09003d403072948480507012032258103000a102000c403005241710f04102c920f55041015864420780e0b0342d003049192602152554520412501a114041e8003070788440c60b084a48400ca9400001c1a0007036a0700b01c2601c101542d50340800c0300a02003503030040e0a042c410404602401c0100c1c090a0300300000e40301d2440706608070307258002180c0165000c040860748034801c00080c00081c0a118000d000070704021030860a21480d15695030b04500b049038107100c0541140d230310101c1d80d5000346800300711080031034444035180d2038034584680452070102d030700b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 9541131 1250 9539881 9539891
    0x30304030f09081002070501060506030117010b04140c090a03240609020a020c1017040605090c01020a0809010e0102031204030e01020607020a0302190f0606030803180304140108040203030d060810 86
    0x7a84111100c204803140000280303d0341014242c400c0081d401450100c60565850a0024482c4c458034042c6000f4141d210f121002c0e800d51201281c02d407180c140c1c050b1321991410b840d0310002000b803031405811000c0312940d240c483e40f400011800c500340d26000940b0803801c17103a00e0103c0010500050f1100c5e104602c01b4005990741d0303100b00082c1c0c017803130b0702010241c1c01c080c07003041c01030070420441d100d11038140c500f140c800805014400c40c04c0c601074074203803109078880b410403603030310000c20110040c028288010b015214464868801c2030248604082c10044039007100d051a03031007001680c091106c1d22030300c4603075801c080c5400b0f0035035a41d12904c01d015000d06030001c2c120500104035400100d23015000b42000b01c82e400300c003013911203802c039048944404040b85940402d550f44102000356115100c1f0301d96908156102c1c040040302ca15040c0700076441040306002c16205210704403880e81080c00c042069031644c3c80002c1c21800b0b90882082c0c01d40c41c00c0710016440c0b10000b10407910223145841044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 9542381 1250 9541131 9541157
    0x10b01110601080a081e030405030915090114031003061802010201060e0106050406030c0309050307050606090c04030203030d02090312070c060e011d010f030b0604080102070c0801020a080103060c020109120203030403 95
    0x144441d001d12488405030004424040030515600041180d180c1c5c10000301d08940c0d66502c4446075420940e42526958004620107400381452240f060086107104d0405003015102c5000a15020041440b54002100400456401e1000c814400e000d142d10a40911299a129a08600c44600031400342d00540c01d140000807844640d06089069030095039445141c0380c1000010b60240c816803040382c04055540e14002d0104100703001a101241c03058000d480203080400c100441013001a02c80820860100b01c01c0006940000441784240082140940c855807140002030820561214821003050001550400c100080120b9010345002e502c03424040070407000111080d1607a5091780345c40c00e1311140f40340c41560041c100c01402883c949400f05a042c1c0c0c01c0c0109506411951040310160340114403d010001550128009003003408000c40c104030105c00024072423a011700c0044c01c1c0315650a40b1000241c07007074100503001030f0424aa4000c01e900500000d640350303c2180d0980004bc40698105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 9543631 1250 9542381 9542383
    0xa110712020d0803090a080a0f030506030f1005040510090c0801240302010c0f020a0b0a0905030a020108011a04030606060801030b0a06060e211b1302070503040b1b0a05010b0111 78
    0x4102a500600241e9141034aa6503e07206070380064412120392107110a44030014074110014482d000031503450040312400550301034142e901c0035003510b21036040300050203c074883c0081d81980020390380c58041103e032a241441418040e155160404803030405141c41c0c140010049981c08417113411000700300c8002c1d8084002c040010304070101c041814446020400356108401201d90580291a146080d845560000e544002c690307100c11118000854841d80480e00004140001c4c0426009400004043d0380000c184001c1405038030203845144a01c640c0e013003003001c04d5801865010780200840c0752113000180440d8000d100c00c861520003d4005035401c0190b0003000e003101ca0688510075114a1202088201c02d10b056484040300040b50303a07020b440c3d0080100c00341505080f82104098040f180500c5004c1c1400040e07440d596004020000000f0000011141154446202542c83c0c10040c03500c0205034040c12500e501610075140c80d00d0a002065111011a41090300c1d080780400041c0c102e0b03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 9544881 1250 9543631 9543659
    0x3130807030305090906040b04090c050a050603010803040323010f02070204061e030305030c090d230d09090207020406050603070801061e05040302060304291b0405090402040b01140a1107 82
    0x1c00145044c04030700700c14181405416080b0070010b101203030030040c0b0400301c3c0407980c8440060b01c0d0b040401008001c0c034140081002c001d04001d5800f14590340c100140c043d624070551100502000010201103080c4180051203000201c401009000042040b043c00d4080e401803a8140e1190345491000660703060685008100582d05240d0035900c240745440039111900010401d892100080102c40c01a0ba07901a1480d001c0340308401c01c2c280c11090040e42500d01181c1000290342e5071109100170803017604190000101c541d40300002d070340c801b414404500681142d501c00743c0c10420100501c0b650581018840f03050f61141d5884e5901c0d40b4480c042c00d0705142e040b6004a010520420003030000d410300400035940b003406240d50594010341d5407000201c0c0c000a50f882250940f800090210721041c10004100e103e84407500c15040c6400e06c0c000031f29981025000910032640ca141030816039003c0c0c807064051403810004603449840c252405455201c260f04000d4084c090f40402060140c0b4071200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 9546131 1250 9544881 9544883
    0x4050d050918040c05040e0102030a060e040803010e0603070b0408010209031b010c02040b0a0302061603020c010c030f08180105010807090e032a0102090a090207110a03080a031505090106020313080703 88
    0x1144908074601941c0c42002d0300c000e80705441c50700050101254030f40341d500692900d801c205000590301d00c0c19010150480f00746421840d00c4036607030814000803c40680a490654079109000c0343c558a40750002450004a540321401c503d84c003050000b583c03001940903101812065050780c2030003680f02466a01e0031084806980170541100700034015046c183d000ca900b540010b4154000300741c4980014003079410501047d901511300e034100d10304255043c0544e440c100402c1c01c15090050036a5401383c2202c040d00b09075410030903035000045000003144035011001c1203d000070016961607810482d104d02d094001e5049440c2400c24480c800388000088407101ca001989104101068a1540c00072441c1503140d07518070340d024040801e160f56028406030003444890380c010b0f80c4405614140100704103404403107218100c1c4000c01c00114032244102d400101c01c524000405d0141254105640ca1081d0005034029860b0700c000315039541c000004112901511460700d01d9550381c1d01000d030361100c003800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 9547381 1250 9546131 9546139
    0x5010f0c15020901030e0f0102091c020a09090201020a02041b0906080f0106080403090305060106050403060506030307020f01120204090911010306080d020a02040c090b03040614090d0219030908030301080604050d0509 95
    0x5080001ea1641e40d01505050b40d05140116100750441942c40c9080d0450591038901e95000801d0a0b076442e02035040080190349880e5403500d0442078000910098151081c03800c0d070b58a03801d40c041103a10a00c02401810342c01002000404c1c0e41032080e084401030000c419000c102c410f01c010030002e0180b4880c1d445220100724100c4a80c1c20b02d041280c8880c4081c00440500030704010205c0091000d1016a018000e59961161194614203156041c3c41001d049603000c0d8008101190150f102c0c108d0016001c2000e09026081c2400c3c0801c5000034441d0384d100c107103103501d072000700c41c10001d05191a0011003000d1707806021658a0321415910341104a442c00d0140c1e01400101c001410301d034000194001c0b1504100c100f5599946210f40158003c440031a0000d41d5060000d079228403680c401c0c0d400c03d07020740081181004046c800b9582d40c0c8079140340d604222800c10003c0030103102d405840050220f12040e2078595a6039040c07240e41d821709403021a0503000701c182c2c070106035200d0b50517900d542000078 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 9548631 1250 9547381 9547403
    0x60602030c190201020304080303010e0f0a0c020307020108100803070b011707081e010609050702010f1d150405070803041203030f0b01080106050d24050901050906011709010609050705030105010f0c 87
    0x180e40c1020b078900d0890220305500041c040020100c41c00d10155008182008013010303c0d140555002c440c0b090018104682549040c8198001c3c41d4000152043e555080c280288540c60344061100e021203940d104840c54480060784000b004801c03844241203a00b007881000124525404d12516404a40070341c105c2c941c030414423400c240ca4512825504142c15400028116032106016803da41040381c2e024007607034564000070845440d911500c105040715000300c1180b07103c1e54407000d4950000c010300c01000200d60380070809003c400c3c4003500c001c1c024001120b40c1d80790358444421111411031401c0d000b183c90400112150822400b4081d0b402e0380503074034150560300b860310030390302a040500401c00050380c903080d1a0f04035001149031000407401c0d0400c00e008524003410050f245405801c8a0b000e12011014030515903048601c0366051200d0030041d000940d2101041030042a095000b0300b001c50600041c003140303030741000056040e074078281d0380d5900c55041445e080c3c484130050100248100426 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 9549881 1250 9548631 9548653
    0x90519080304020108280e0c0901080303071805060a0f091403060103020907030f060305060a11040b07021519051305010201330314030a0306270207030905090f0a060602030c 76
    0x1402d10950014190800740504401c1b00020030380c51038081d06181c0703510303943c0c0d0710108024008c200c10250554102c40b40406503052042c42600c6c1d002c082c02d840e0502c002c0e0749034410000020110f200191002404c100e4840012920040c589803541a07840041040d0b180301041050501100e04400f10f0080d00401c000d910750303402d00484020040491041503520b60380c0545000c01ca001c1c6500641c001c02c0201203904200320b1200031521958000e26141d402000200181c1d6148410368a8842d0100d888010510083c491100c10784034400156000d0380002c00207a010f1504800504600341845080305196a00c030001a4201d45241504c0720442080d460700b02e40900c11110102804c0000541201a50b60b980d5161070f024002d40c141c458440c0c0002c0f82c80a030065062041c00000c0011003c101c4900e10310303c2c081c2e00d2078071b004110810510340000d100b800303250082113940b000b008082e00c9500240303071141c0c0e282d030005010b485514585080403000101148000f0654840c54030040242a200d000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 9551131 1250 9549881 9549887
    0x705060702040b10090302010e01050c07030f32070b0301030b190b12010203040b06010c0b161b110102011103010b1204021302070804080c060a080a020306010917010905190803040201 80
    0x800d8804a034015200c250b40c0d01c02c4d4403030708612a160b07202038442c06402411031001412a417202841c1e0b07410001c0c140500510302c90006024011a500403200d80100001410b01c1404074001c1e8000242100a0600ca00099100e2007584191a80980203842c0007680f58003440c210780c4002e1001401c038008510100700b40c82c55828202c0c00b02102c0d0003000600103c00c0011404c4003040c4801c0380c2c0265404802c22040c4141000308aa10030000d203003d9071500915540c071090b52030007400c0010060201e5a103012081d0140c4c07080010000710380500031210340d80d07240022030904599030640c019402c1001c105050025001940d041c0c680040c0494100040c03405450414800140142c0e13022860f07001c10204c0c0d03407a038070061460703c1c042c04040e0358071800c0503260b03441c103da0a1405c1c1e005100803c170800410f940202141c0c4c220310425009644c1b520752800498502003c1c1d00019201c40c55415032481000056100356401c80c4544195040c04803020441c80a450342c181c0003400d00d0600300b000400542c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 9552381 1250 9551131 9551137
    0x10e0a02030c1b0a050105090106060810060906050a0c050105010f03030f0207050102030307030b03030f07080415021f0207061d01021305040b030a030f090b0301080c0a080c1f090b0f0301050a05010f02070506 91
    0x100d50003282c1c52041380e6264242921002d8038404043c1e50766140034009607034403030b294a82c844c44220b50160130742d1800000601c04540380c8035a00820401060030202e0754498424403500c00e80000c000c3c0107d586416800707043c2d807801c1c48114003041ca1024420715150012802100b01c40c4141c014600b1952139010550141520a09041e4540403c10a0b410044010f03c09040d45500944030303c0c0d2254240394030405108021001c03c000c0d903000006aa042c0346e040402d0100c10910400f000da120603044c6400b0000c1c0501e020a08107a600c0004102c000b500154050041c81a886411020055031103040c403007102c200c10704480d0160020500140420300507c400360600700c0034584101100e58a40b00b0040541007a0400f401c00c1d001940781840615006183d0805026a07001408000711003400050315600c401e80566400c11b48230b00740e155040e00880d8240c009103036619616603503a11100d800d000c26402402807900c50b507005240071a4a500c240264407046d00b8039001000824145001c20007160 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 9553631 1250 9552381 9552427
    0xb01061101150902070c080604050705150702100c0c050d0308010302040e030c0f070e0f0c07021003060801020c061e07050d02030a020d020c01050a0624050706020d0e06010e0a02030c 80
    0x2640703072051045603001140c44980140030401e001130f01d415480c038140b0124059507000d2038495000e08c00303101c041900490703408110f860498122450000c0c06014030414000d10402070b503c5124008030202180d04500045002841070307070141c84858845c0100b103a25a50940c01400054001d0010300041c10079034020810b41105401316814101c0c15044207150480e03190243c0350035044224104001409500d83ea50401485032081c8103515000411082501950b00c2c0a48294081005440114040c1c0c1c03001000e0003080000350741d40e9611002c502c1d560802941d07002ea851080c00d000b1207102585840290103140c0c03941ea541d180640c0c41c440f07200a07400240442c1c0143c1d500300205004001b05100030700592a5020021589140c0303003d0850444000e0b0b8000c9122014440c03141000c0d07102404205882c4c075950800350b44406035801c25000030b0080d4620800041d141ca50356280e003840006519040310320005020169580d0310383c60328140c0c0426541d4406a0005100020800840c0201ea44500b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 9554881 1250 9553631 9553633
    0xd050403061104050406060f14090d0221070f080705030c0102060402010f17041203050f040206042d090203040209010801090308010501030506010c0c06030203070f02030f03060607020612040c0612090b010611 91
    0xc280c83c1da00145c21600294800b82c003154160f6500e0280541103180c02c0301613004c00c0d00d102c2c2002541070108000c50340040c1d00a110307a2002c0d00881291200d90301c0d42c42010703203030b804442071780e91160301440d803500c0c441c010120746104542c0d00048a1400282e414100b00060780a00760300c1e22140d0040d80d05594034403042c024007403072801c04420000d210800e10321940c040c6510307100c41c17000241c0180c11074038003074100c11801110004001c0035880d1b02c0112012180b5200e010044a0101d58500001e16444680e480341030918000008070304081c0d402446c0618021101640345990f00d401841c00c880301e2002c0200824009001009150b0103940b083d6441201070601c10183c0500e5035418240e4072b610380001001c65400704c04e001c07020754048541d0b00c1c0c0301c405000462030190b0942c0c01900c1804014115481120005806c3c0c7c02c5441e00403c3e1000010404800c004c2c60034a40fa1458003902203000e0b990002e00d81c007440304030070032683c00fc60280e00d400c41040100f607406c181c2c08484014a4408451031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 9556131 1250 9554881 9554887
    0x181b0d080c030c06040c0e0702060414070e04060603021002060106090b090117090106030302010510030c090c030e0312010302030d05030105061b01150303020c130212070302030403020a020901060305070e030d0504030611 96
    0x90039010b100521094259001410fa2072400740f50844070305140750040700303803011b00e0303c100a03640d81c0009005030003a810107004080f602c900c141203440e0402c2078002d011600b1148092004128081d0040d2064a2089980744802030150038100e0303032900248200e1001420005042280400c40e00050450403010700d001408034401c42805012400d003038400a10581d5503050070014503a0a10032a60092100b4503000101880d58448400982941c040da9656603a40c00800c00e00b203009034094080700040d502501d4603501409422160341c1c109200a0707000b07009800340d080700d035441581180d050701c000030603450a2001e0f010120308010000303007a1074400d40d6142c0526a4600740c007800d9400461295005025500380ca50a0000d0150380c141d403080806d0060002c203d103080c000300c05543c000c2003850b00680b079a4880c05e00301d01d4100c01c1480a500030b20b40d000007242c8590f26812481c810b46a94444207641c0c921441810340c1e0700c0d1444440000140184428000a030054200c03441c00f448064042c3c0c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 9557381 1250 9556131 9556147
    0xe0102090604030f0204050603010204080d03150e07020706020c091b07050a021c050106090b010806010f0e040614040e1b010507020a05030d02010207021203030105030715030f0c08181b0d08 83
    0xa2182d00c990020350f000c0703940000701001c600d001d01619500440c160001c0d42881c4c42c101c119541d036815011040241500c984101d5240c1e06d000c07958038000c0c4824004a043c0b810a00c0d001794644c40b03c0d0140900501400418000b40c0c100800c906001d2240e40c2840000b424030490208041e4201070700480b864011040382401507030f070b1441411849030070960010500a0b00f031a186085820035405511211b0418205007001d070b82002d00198409420700b0050303141c5854500441c0e41550021100f980320f803424002296a5080c454011103045080e034041286844003c003c540e80c0c1007510420044c24146a15580c9651284003c0d140c0c0a101801c0222581d4507040041c1c1003103096016440140c1d0301003272810562500012100d02c00350004061403441d410034002ca9111605400b5490841c13220700000d01a4034420381c00000002d00444081243c1808080001d01c040c0c02038034022102105854807000000340450380c40c0b4594410300d00d860981c1c86020078061241080035041e5907003401440380311 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 9558631 1250 9557381 9557389
    0xf05030c07031101020c03010504150c050c010c0507020922060209030f01020c01020a0212071e0201050d09030201050601110d05030f041b0303050702011209080d0e0c1905090f06060301090e010209 86
    0x1c059441540b64480381164040024900014440a14807980c18241440042007040050007000b1303800703a10209840030309842c02d0340d1912032040d24049942c1307081e0b42c1c04001da512001902e10f080c070841e02c00d042c5440b010001d403608034420a078540395980031070b2404000791442c0d008021210014040d2821000c20203140c0d401ca0300b0140240380c4503500064031202450341842a425047c084040c6981002c24030b481e4038000044581201c0071100014400c5410740e030052040d20a402c50b590310520180740c0c40d1070028041c20043e03a1701c43c003081240d10540243c1e200407600f281c400718182c0d911411036680015548400c0c1016000b52404002c9003000e102960100008002035400b0f0b40ba0150350703c80d50b1000601003029030354040040b5151809810004000604403001011401c60101e400301d003102d06282071400c5a5520741c0e002c110f40c0058207281d01ca182c100300486400302da0f01c0d40503503a02c18100c2c038016000c849181d8003403400c000510008190b540140c0d9006198400181002c040e0008a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 9559881 1250 9558631 9558643
    0xb030307080c010c09081906060302150a0806010503071211040b04150806010302040e011202010306091d01140708011208070503030f04110406030803070e06090301020307030902180106020a0f05030c 87
    0x180c1d1040d0000441005100d82401a503840c00c003a0316000c18941d160440d401d498040d105072160b402c0074040550301c140f00b45500184040d43d0000c1c0000c070008000c000c280c2040e8408000340b07011445d01800120a58000c4090740c0c230941581d110218a80c2841e03070510010200c0c0d001e412003609085c08085a144d150300702801c06401a85034006000c08890009020044006c3c5114100750040105020441c0d40740b400f141162038401c10040c40c0d800910058000c1d201c1c070b0b0040c0c0c112502e00140c0c620560901d007240c02201c1d048000030480c042d502e4082800042c0219040000f003040740e401081001d03003072403c0c901007600810a16080100942d501402c40d8030561311261540403013001e000501040c0306200c4030040040b58100182451640c5014a41c04014958014084009111251070700c500044071001c001c020021556807918030400f41c014085610264014120400c040c403803041045501c074180c0c3e02a80052420705601d0341d40200c484190a4100c030980400e1000a818120401c61 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 9561131 1250 9559881 9559883
    0x51c05010602150412030e0c1918090f0206090d0b0f1008010c0f080a0b0301020f070b06060c03040506090d06050907150306051509040b13050a05010b0405030c0d060b030307 76
    0x1010855500d0050000d140c00d030800250000940e1600610001507a003040040580c0d280d401c0c0401d41d00d0303e02400e10b0402070b03100601c54011845d0000d0303a00d004503549200c4240e401141c02503550700000c0c0c0c000011260200801864006004102d4015140050160405203401020319101d841c50755101c5400700d40a40e43e004010ba416000d0010310035254a0020103840800000c0103054810f120003411301519500800900408101042008205410071204080054021340d0b80300030119051081d079010590588a102c1c3d560080b0b4001d1070704004441091050700019401c1c07600345020070510f5480100c1c45640801c031000d0010002e2b01d5402403a12442e2030f400076200162030100c1204ca8441c0c410580c00c02c05250038024400d603500e0042000c2446105140143c41c1d90b00440854014440c95810719400007501085000308102c641019200d1141810f050105982e03034009011540540e02500e6030640007070b1051034050030b1400f4804031880c01481301081c10900d4001081c02c65101c190 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 9562381 1250 9561131 9561187
    0x20d05030901021005091005070e031510060203090102120d021201030b09010f05100308070503040b040b0a09050906090103030804061b03090605220b0702010b031002120601021b04090305 82
    0x14400341e1540e014410703503036242d103040740c103000514014103460740310101038880021681c0d231040461445071040f10000d940a00103400c4900406e5407031552a0f4802e4100d8503084140d50100003c50424408015640c00f107206800401d04910018170210103908120310f07409920742c0c02e02503038a6070040e4000c49030007580032789a2094181003812840e42918005a050b8000e41c0c240700c00c0c0410030802283d07a40803290041c8000b07850350050315001d4254806c0b948030130042d14012601065240c241e0300103040c100d9458a62074000b9580302c041c4923018504648643d0320a510f8001000400d00810310076034880c0c4034920000d8011200d40d0010042888500d0765000281d4840c100c0d020800c0c075101d074603008011050010002100f00b281103c9000091400500180303c1c00301061070382d07000750001003564030b004041d100d01c3c0902e000c15100940142c860002c88130342203404076544c0c0d40040751240044112440c00030708145640248400b901c0040012020400c040107184400c80d010700605610910100d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 9563631 1250 9562381 9562387
    0x11071202010b0f0a150c0501020309071d04150c02030d0606021e010e0d0c0f0c0b0702041407020a060b0102030409050c030f09060112020409020a08030c06010e01090b06041404020403020d0503 84
    0x14200038211500003442038000e481244a0407520742c2d90b1300e4800b00700c1e441c00e80e020220740020b40b000c0b2900c540b14075001b40300798008400c0c808103c0f0045a500d0656100002c2000031000c501202946c1390310071b45d800303001c0203190900e51010440c107030091022402140110781c54045e4050442e4104d9045500c44c40040e044691249840741e40c1503002440541031070b0013444040c07040c5483d81d0329a00701d1140d00081c404501b80d01c004102498410f0038120750401003407000ca541e280c0d002a501d5001d104e04902c03445c80d000c01aa03c680d049410309000d144168000d2940c0d0b4119903419000304003040c02c25065120070f20001070140c1c058002c40344501d1030700040e503480e802c004c280241c502601034005101604203c00501001c40e89421960f0b000390101d4000c683c0d0b18850010038001c2440780c20160203400006800d500d001800903a8034102c499100d980c00e05a03130380700c0a400131a00140c90300ea905c0701040dc001c000c880c001040c0405800d000910061030180c5d07a030b001642070080c0b01002c54403a0004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 9564881 1250 9563631 9563663
    0x5030c060a061505030606031018020309060c0c0a0b1b040b04050a2103030b1503011202030d08061c050c060309070801050f011d04060b19051906170a1107 68
    0x602a42e4014a05404250b00b240b0301050080c00360f010080150307001c0c2ca408000600c107010048a40d800412404006800e103007010024500654401c030740c54252031080002003000c402030301c02110305103103030301001c1d1481c0e40480c0c1d01c040b00110060022410002c1904400c0410000080104020010010141e40c1c951070720f001d00c0044000c680c0701d0080c14445c41c501802003024034207040c9166134986800500a00e070b202c0040c0780f4040410030326002000110021406442d00781820340d1450080f001c5442c20001c0300001c0701c800608540650300010400481d8484006500034880c0d102d200d501561590000d2a002c181290002c0b1070100c042d62001c58100521002032141581103298070b081040c0941c100399242401c042141d10b14062242d21100160600409501003d94410002c000341100b03120642d02142e00403050061900c1003540400c0c2c2080110280031000442e603007038036058000c032040400200c146600801e1420220746844c908418004030100901240d4450a104a040441d27 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 9566131 1250 9564881 9564901
    0x1060501110109080307050310030606061205090601050105041509030b07090303080106050309070b0c010902100504170106030f0221030f04030b060d0201020c040203070c020909070305010e120d0b0d05030c06 91
    0x405a0320140c1c1c2e4074101658000c15412030403240e220f43d441c1000f0740d4a40f9541d0507124031401d550701c0649424a003d40c041612640b100811501c0800c800e420b2200341c8881b1100ea845810a10805000c03400401080000807491040c424415215007000000207507030785c813031050301081100ca030300009460b4601070007053341080c0f00901410b21072401e141540340c8000d029079a030b0181e00880d98000c201007032144036034001f5042040d0701c1d540070701628400b030b140980141a0303400c6400f80200030360040301c00c0d030386090301440707030204491300050105410006034090000240c20300903a01d001c0c400140010301190400c10041940070b0b00001890360300e62035400d00041d0f454001d0100c2e403068807150b500c0b2700581e0780024400019141100d00581d40d4440403426180070344580c2009400141d660200110f0480208500f0101c1c0d0068009010a04c0c4405c0141d4aa44600b90701001c0700c401800403002e240d00580c0f1801c88000d014050554208441e100e00703285030001081c0c241c07213030f000c04200140c0c001307 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 9567381 1250 9566131 9566147
    0x120103050d0219031d0a17011a030309130b0f0306070503040302161805070504150504080105010902030601080a0f020d110307030b032a0a0f0b03010801150b0a08090a1401060501 78
    0x820880100f03c4901c0d1a50020b000d642d09a41d480c0078102c9010110b042552444880d0004110301e13620f10700110351010081d03001e040070340045088405590640802401e000c030490b098000020690f05c40c03a548004a44010719020030a01c0d001301d000c401c8503032030703450800c10036028042c292102d5480b1314280c5802450600400030b000800506020100b010b80b40340d80304048490120080070900d07580c3c01e0003c841130f005652100e06070307406003a607042c109500300005109484c1024028403990f03032106407141c1644030540e4050300040ca207000268a6805c2039000d040c00c0c0010500240c41c0080c0d0300f0a0707030140d94503400038095141d0700005000740d01e034052007030f44482c200640190031a05994002da0003401e044840050b170007240031a02400c255168400d00e8040c0660040c060740290705c9450800351130300300340520062076180030030700c4981500c258001e200315850381110510300780b005003088405603000381203903095210306a00500010580c0d002c08020005540c0006000c918003400100030b0302e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 9568631 1250 9567381 9567403
    0x31806060602160b1204030e030a06060b04080106090c09051507020306040606140904020108130609020a031b06050f0403110102030d09060b10080c030105040905070306050403020616030c02100f02120103050d02 92
    0xc604101c0f4080c4aa45c00740810b5125406007040c10001e2010304c0403e042c42ca0000e80102090f142a1022035220f5010014100707440850008120300350b191951a021100e081907542d02094100c0b400300102d2800d4407001840ca160030703104500304685640407034a004070549048a0b8940c580c0800e0020340d440c0a030700200044103ca0841c901c1c1442c9d00041c5c60001c029119030b181107044401d5000307010242c1c020f29551640a0581001c09580c6d040c07d9244101d40035040c080300790504000940e4601c60415070f903059640250ba546410314696522100304401c505150540c0000d100e034500650b454451349403c280078590108071989104108141c55110001e41000c0c01125400c1c0302d040d0340080262415943c0a0303e0010313100c0c01074140145044055403004240d503040c00100400c160340800c4d174500920b030024800c01c00d441c140784164290765080c401d880050303100702481c004c083c80a801c0b100c404003005100601c0d040300ca0a00e6032040c442608181c03441d520401c500032446504100c0c00d2001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 9569881 1250 9568631 9568649
    0xf0203070906080a09050307050309030601050306040503030c0714030309010b030c0301060e04060504060207050d0c021503090627070b07021005030903070b04050309040507030c09060f020c0103180606060216 91
    0x614101101501e80c6038203024040400000000160007030683d5484801000c2d00041144d031681040c0c6030250781c0342d01040c90300b40240a4a8000604d5003070024100d8020740e400000b860465889052002c0182c10001003580c1c0c00050816203000300d502880250b0150035107a00100765240440c06141c54240344509042c0030341e1410034100022100781440d650025403003640801d660b21641007420181c001d020f0041c1c002d0044681003884150894007417010741e0f00c02e84005804452a0384000c059005c100c5440e91540c0041c1d0010748061400c0c0980981d080d00e0105410822110011403803070880300303400104195600056075425854511041610040d02d450014514605904c50301d4490060440080621651002180c00c0000034003d5904c2407201034000c219510b007400005001d045094140000f1501c48030700844d0061050312000742406454004001c030000f0f000044008055041410303c060748003103008000103800d030080304010b05165000b0800030300000400c00341d00c100741d400005a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 9571131 1250 9569881 9569887
    0x4120813140a090f020d02040b04080706020a021f021204060f1704020303041206061a030711010504020105161a010e10060207030b0a0504060b0904050d030f060f050d08130602030d0f02 81
    0x82941c2d1588a5401d07980140000b042e0040f584003800080e0041032a02c40d001e42c0045404940340b0340f110054800c4403c0034003114400c560708c038010381c0c40d019100c0010f50012603510a9001d0400c08921030381c0d080305284103ca41c5d00c15512007001450300030b50440d034000b680d10340e04003110300c0e40400744400c1c114210140c0049414140d002903a284618440e10000c4080c00c0040010300c940d90317210000514071145021110740c1e00070406600e0368812203c0d030340461040d880c80c50b0050300500c5101e1203940e061319203d2810f0291802c06000c4000600c0488178105a000120350800e1b28a503401d001f84400205240d6604000740006e58140087e000b41d401c5500c6036004101050030070300380715041100201c00050341d49075810080091b11013800b08030b8000e405502800200040041c000018402c00d660400042c400c010032101070b99401e20603070201030b40b4144240160700d02800b040034914814601c0c42d01d40001e001e55550b541206901920141c0c0010036034200e00085400340c1030313052545005c01c500d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 9572381 1250 9571131 9571169
    0x60c0a06020d0b0307050a2610060302120105040f080306040905010207060c030605010203030f01090203070504031208070f030e0604020402091f02010606090501090602060f06030f03070803150405010e13030504120813 95
    0x1580d008510821801102c0020715103108c282003250000501c800c28140e55410070104828009480d244c40100c2c02503682080c1c0085201040c81440e004540c0000e168540d02c8032629010700f16000034056a501590b00c074605400503400b48020407807079200c2c200106140b40c034400042c04840450303100380d066410800400c0360481c1c92207080c60649a1120006840b6100c400701100e49000d01c0e00700078582904c0441810105401003c1240f141300250307141c403558143d03c101102560400c2d500c4012540c800c01c04580145840d402802e54040041c0c880c2035444040701740940c51001c0710440700c0c00350755625010f102050740301c04040054071080c04c201d12118a8043c00035502d000082112105d8051680415800c3d034040c451680c0b20001001100d40320030301420003003282c6d88181c13506600465880c000161340c0c2090b00a050490302044042c680c43e61300c6010f006100003950408800b000000c002c08242c43c0c00f075000354084140103001258031842c081c4841e189401c081d404c00740b8014804e105c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 9573631 1250 9572381 9572389
    0x5040506130533070306080c011101020d05040819020105040206090409170f0a030501080708070b07030309081602030c012a020102030d0c080402010f030c05040e0402060c0a06020d0b030705 83
    0x39420504124021040d0081c500300181400f41c000c000402d014020071004007411121003008514106056442040307032102c200a40486840b031041c14500d8124000b510309541c002c40c80f01b4100e910f03200000d460124200d22410884030102c9048603941d601240100402c2420810040c08000600081050381090b40008a050081c290003503c2241c581f1140801c02c54204808949108034080d40c58650308c80d039084010340d40155024000007480c10000080c2e542e0000341810494000c1009031840500b800c13200c141c42d40c08040c05809041c0c4800005000900000007007011081c1c59080288192052041604203040c3d00102410403003418240c003011b514001c00380c1240494402c000c02c07019031620060f03065024070001034282c180303000402c1003600e070030019161096101741e8628034180c0344420305504032441011030000180b0188420701c007070070b24688883d4001d0700080c2083d041c00f000324100340c60800c3c80007003224215000302e41827209588a0045d9600c540302200a0503805083c00082 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 9574881 1250 9573631 9573643
    0x3060509040605061807030f0b0607080403030311040b04080c04061202030601140f0607050f0d020304030c05040b0d02030f0c0109090209010516030c170c0601090b061b0c0303040e01051003050405 86
    0x80c0030b866907000800e041740d84a030354050150491005036241e524107101c01900508031b464203001c9690401010403460700d171403003c903100154030465040c1001e065031411002402803c007240c01d440420000410507a5002c4040e0000700404030043c1440c903058014042610203a45c400d0003c4125003000c0c000503600850024107440c1001410a502082d9800180360301c8103d00c080c54005400141c200c0a010002c199864108042000c548401285c0312040380d4034822440060542e002d403000c10b01c098940394104044150000b050300c0110721003900001d082452503d0072040a5000c0b0003101055608000380f0383c01401030702011030801524200180141c4a22004019040c035400c4c04103041601075103c54075016003240003210002ca8101400d440395020b80e000c032841d0b1040c100006400d00460041d06030304103014103250f040c540c02c10710310318000400d080c40a16074003944911581c0c544040020344010580790007140c03c907524260610501d80100301850080508080802020807070004038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 9576131 1250 9574881 9574883
    0x609010807020102040906030b0406060510020601120510020315040614060a0c17072004150e090a060e0a02040b0a0302010e1509060403060e0d0309050c06130e01030318060306050904 80
    0x840802551501c0c412802403046402c25200d5902e41038000c8140152844514811481007800f0800342c2c0d03da40c1000a004251210100147d0280300148070349001258968142ca2141007150000300d9044200b0042e40c00c111100b04901084030104060343ca40350003198020f04030400503040c509000d4022501a03c5424031480c240501d100307400041200480c441c0d01d2025041c075110f0746030446440d21085002c0c9600c100e02c40c24182516102e9180340c54410080c001001c16485460036203002c08080307980400500c840d06c0340c0920441c00001c60303164082e0204c180400009043c0c43d1429104020440b10184400340c05043c505c8070900060360064507d880303400d8200d41c9050b202145102c2c000051003007000150704480701050000800815070015101c003c1c120050f211807a2104200320b00711061420043c0c40eaa11643e40950305050140007803113800d03070038001048503684815801039092401c1c0e00032400100454040c2d00c501540842c410094045032030180030203450305000074108000940 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 9577381 1250 9576131 9576137
    0xd080105060a0f020f0304080304230a050112020702100206090f0303011404090c090e010203060103050609040506040b090102090918070e0c07080d0902090406090203010507050705100209010207080303040c03030f0509060901 98
    0x40401c1d031070350017084240c210042000072281d0310350725500349a40700c1d002445a441c6032008400c168403d12448040d1a14070314001d41241d0446150000440e18030b580e071034140103802e50030099a005a26842e5406a10540c60740080401303041c20f5400d075251481c0c1566011658006100511a804024580e000c0e420002c8401080d00400380c105913001c126580c1c0151a001c0c6030111a414004040d006036124032400d032003c012540c0d58509100c40f445080310001c00e00e800080014000800c0d066201d90081a00300005040c1000d000100e560390100750380c4410003c4000381020002e450400078007000e0040c2c040c42c52030506201805950034020300e64010520318001c550030080203095803004035142d400a0802030035043c10304002005100c4040300340d00a508040000c0c400d107000b0002c403002c050f8004010025104550300c204000d400c1840c00134114060310300c2c0064102400c002940c080c6004643c0140d02c140340d4070740a0b065140007505070040c010240042c0c0440d03903c100540720b00d02400e003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 9578631 1250 9577381 9577397
    0x130e030403060c02031303061b0309030c0609030504050d03080609130b010e06030a0b0a052401020309010507020a03140318040b01050304150605060301060f09050603040b18030f070807050d080105060a 88
    0x3101641503024420740ba09041311b000b100001441a81d400150070310004681035040764681c090114155088a0000b802040d83c808001002901c0c940c44550f4942c003070318290b410540c80b0320018521300d00c00c50050b000207142c039083c0107a91414910381a00100c503802c010303800e080c081c0d990301d01442c814441d040c0145d0710000060001e440500040309520303031083c148409072a100e0351250041030b0584500340464250b150403104410041c02c09050044141c00a5050000010044034507a100c1c0c10203d030044004c41d40000010070195820240f9803000b000b650301e501b034200d614100034000300d800034411400c06031648016600b0074200d90b0002d401c001c1500b103902c1010001c1001e0129680403541001c0000000034102d0b078018000901c5c6c1d00c0d540c0d20141c4155562007002294002568080c210145c070b2404994441c0b074001e20b104002c40c50005580c01c001c0c0d011070b921016001802c7c25520740c41c0c000b074070200b0044240b00c8652405800e081040d00c80d41840e000c00c1e1240603421316841401070301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 9579881 1250 9578631 9578651
    0x20d02060d0209040606030501060f02010510051003060503010c081f0e040f0206070f03050a02010e060606030c160606030812010603020313021002160308070314030c0a0e0d080309060402130e03040306 88
    0x382c0445002c2c032009001480070039683e00780240201824815400010f0f0580017000c0780610600520303004420144048044600706802c1212204400b908802803554402000070952801e00403d003450001c0e4940c0081c615040004016a1600741881c0030000b00030101402200c41c00007031590002d03009014504c540945201180c45032181030000341c0b00d1a40343c0410303420560300030010881290654000c1c840784e83c1c401038480c4d4880d002e6a00c250f1151080c40003808005100c00502250003200c600c64040e1112510754204845454000341d890300e000040b1500c0d5440f0070340c0007a0060203107240c214994030300121824400000e0300e82c028420390b03440b109640610b108104070421040b1103030701c030f00c2c450342e40b80740c4036013254400703081100071410800c5020003174501c0e00d0507a403140300f00300b4a00c1d03d01020407400b11001c4036030f4220319a010201c043c414010501c1c4801440c81405c81c10021f0005041c40d0040021020f001010500e5046c2886009a201500801aa012a0b81c403070300100e8001d0407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 9581131 1250 9579881 9579907
    0x9050a0603021f02010b0307051c0305040b040902030a1a0306040f020a0f06050d0b0301050f01030f0510050405010f0e010203190b0d02060a0c03030507050406080106050a1e121107020d0206 83
    0x41e500c0698007050190310804018280100b21402c0040b03034000301300300d9192000345903d503541449107a81c0102c074045080c140b85e800d0b484500b00075200349031131440c0c00d4031030b0103002ca9070b0090b82160091542c01320070407040e12040e00c510340300720451030158180d1408010000340c0d5080c3c0104020444a585d1042d0021501d882900c00007400d1035440c0d044003143c80f41c40041807504841400104d490070880044194141031080034041c40d03d148002079160309545540348a000b40c80f50483d828450807544480035602840341c5402284540c002280d02c80d00182003c099541c10641e108050744100140451884400000700603901071441c00b0403031500c1c1c1c8000800b03800030480e0107500076100140d0800030581c011400e00c0902d02c02d480400c605d45682404440c0f90107240141000709e00400018002280101e0291050046070715203480280c1c0307a02c0d044405180400540c0020400a0b003035901204d105011b6904a0312000801e2401c1a1040d00000c9a50700342c1035000c1c0c0501c800003004141640 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 9582381 1250 9581131 9581141
    0x306010e1801080102070204150302060910050409110a020609070b090103090501090c030b040515010501050702040203040501090f0308010807080a17090a03080f0a080f0609010905060609040501080d1103040803030109050a 97
    0x340a001c601e600d07680d540503050103503000311400ca10941c40d00510350f003134183c1044402c007a42c0e0064800d50801c0413004c180b111600e40508130009000c0180300c0040d51304100d001d00004442540d8105858640f600d002914042e80a080801d542e0401242441003078585015105803010034680820104c405092107401030141c6080900a851002008410b1203d20806540228030840840313460855101103000195001c0c06a00d00041c000c1080b04058907141d001303150000d024100006581203690b59070070540400050171008140c0541c01000304d2201448a032008120b280d0181407004e003070303640d41d0703000600e00c071001400e890300800d211400340c81d03021340309000e0b5511034040c9035242d02458000701d950b0060000b80c00020510030006a2100741070785105e0051030080c04528041e402c100481c006088010481600300781d0600c6695442c0d61103016040c002e1017100f01820003503600490051641035104004c0030203600400081141c542e000080300e045500c4040c000800c1d4a40e0004080505 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 9583631 1250 9582381 9582409
    0xf0b01081b21150a05060f030403050d0204080a03110601050103060305030409050c0903030a0302040807050105070b04020909010b040c1d06030106080f0601050d090501021c051005010309020f04050103050706020607050f0306010e 100
    0x1d000030400380a4071100c0690f8a03960849078828015134070803c004c1584545c4007080ca01420920109001034000ca019020706102080007604094540807000e181464000703007600021120300107120049002e100c618003504007031a05001c0c05056446007a500d00c12880b6243d685955000001c0306508020141c80f48003c0044c142c1c0c0e55a4801c401c01000303504140101c58490007120070000d0190701920450703000d140e000340d03181090799482d0200101000000e0044805540341c1400103503540e5130348540b00c4140300c6900c40700c0249161084045403e0140c0300030034002c0e130041005200180d00031100542c0030101e1080f446e01c0c0d075900c80040710103000e40d10700360042900b08500202040810340150144003a0705e810312960441c06058881580c03021786440850a100600501040d44240c0116400e40d0010b02a2414031102c1c3c404102107450980c0107540c3c5812100d4144031f540c2e410701401350440d21500d00b8a09141041c1c900d00c016120107044c0700e050201412080c251074590600e10b0b5008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 9584881 1250 9583631 9583687
    0x5060106020703060c0306060e060a0306050a0f03050f06010b070803040303090b0406050109050f07050a12111603020f0a0c060305060d06090501020406091d0105010f09080a05010f0b01081b 83
    0x1550351158081d50701c040d10300040340c0725400c2000c6024440c2c030a101d44021101d00342d84402d0445217110500480d64840324580b0101a05c540c3c0114079600c4401c0c21300c00800c0c2c80d80100c405d503840d40c00c0042c10245280d0000b8169001040100a540c03050f0301540c05264104180550f03940300d0745016001001300c40c43c002c000d4001c3d01c0800c028040c40c2d03030159040310003880c000e114581d02c40350392925a034012a04003010034001d01082c0034481c03069034884051008002c0005865a2489910116822010400c160b0b148840d00c0403040617410310115006000c103600428802403595a5440d09e4642d9000c4e0300c04040e501c0d0300003046c43d510f41000f501d100b5040300c820040100c503070800a020350310900581e00807491030380000401d01080040c40c650340b292880d20a90b207900b804011220b04a640021200b004080007001c038016009000c969440d610840000030703410110440b900980300082c5450341400340340c000f000008503000c0f0b04003a0342d05e010513009070b40301c0162140f02c4000110280741403036 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 9586131 1250 9584881 9584893
    0x102040e011403100e01051503010b090703050a060e010909020102010605060a050304020f0103090b040308060906010e0307030803060402071509020a0609050303030402040504050f010c03151502120304061404050604060b04150b07080705 103
    0x345c00640c48240101005070100400e091400145402d880805074a1a000072405000403c4580700b544420703001681d240f80402c12650f5400942480c0c942130f00034138086541c99011208540c2c0920403480202003d4903850b0801074440c0003d000d6010042019000384008074040586a00c69800454210740c07180c42c014a90501e41001050007008840050203402c10380c1c0496003d40c01200100b0400800400030800e0a0440c1d444d0003054001a002c681c02c19001d205410000c1c420441c0d00b294041c40c218006040ca0381401003200100b9958001c005010400361b00348400d403800b004030703a0f1081e0152008213035910341d40f070454a407003049104984154648155404017581c17640052201c0c11040591000c42a02c42c04021b94070614094040056841a0354103443c0c10070b102d02440d80213004140c0007480a5204000c146241c10840d01203ca9030021801c00c0200421032145040034038054401308117000006000d0151148580106200014041040e408120300714085410443d03101c01980c40c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 9587381 1250 9586131 9586151
    0xd08070305090301140910020702030a020d03020d09050405130b130206030a020901020c030313060c1704030803071b0b01090f020c030d05040314090f090402040207061b0f020102040e01140310 84
    0x481c07904011020391103542402c00003c01032030130012650140240320060000c10fa55880b01100075801030500326014011441c07060050381e5008619404d903400307074018003081b2084003002801e690b059049a032189140c070090141150707042c0c1610031026130025aa800948444008107039102540300c0081d4400000400c214083c82d00790040d00982d602a002c07103115100f039030105512401f40350a1400040104c4104001c45440b65031450760a074000d91030901e00c4070083c001241103501a80096400000010034051080d030b1084200f180c0c103400288014544030303c1d50750101039200611511040b50b4a58003440000c1040760b0458003400c0300e043c01c59070b5400805403000c0180004440990106241924508400c01001b0446014207001040e0340c0e0007800a800308400b40c50042d2060b40c100c0d509003c40e0340007641503c41c05054000c00c02c0c2c048280300c0301c4c8400410036001809240c0440e40180420800220301d698010306581114044480320a50000440e2802c811500715141050811003604 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 9588631 1250 9587381 9587387
    0x507060b0406080c0109080304120b06060c0a0605011a0c120d020f0c0d080c0f03060103051803071b0f21020102030708130315020301080303040204090302010e0f1c17010b07020d080703 81
    0x41081400e880e103d41c03091f0384501e100d8032800359209040038001c0c980307003a100042140d200140d0011004003858141001006400d01d05000540100e0714182d032180140007605002910350303111035003410014600403c0d012032a40311a08642c007850700c0003010640300381904054040d140300d102c140c003038907440d0070b00c81c01360b55610b010340003500d0701003019140400e80e8003d0000c101e0303402c402a42501861a02c0e40c0c4c2c0110b006100040104081e0088180140e240d80d0060000342506401500310781d560043c50a4602c0542c60b844e4804032210780408800c000f0207205008075400851841840601e480311400181e0440c4614200240000340015605078098440701c401d2040d0ba002e07104c3e900500c1d909004850403484280030700d6400b94000d1001400515203504170a000318841d1001103004003103529401c0c80c0451441001c3c9581d0081c1c0384100884000703581d1840f00c0340061400505a0021800314007a04006015803031203850000b1303145056480300800c10309079961100c200359a0340440c0c2801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 9589881 1250 9588631 9588643
    0x3010b0315040b07020105010f171603050604030e10020a0f0c09020a0504090b0102010b0a030b130c080106060e0916050304051213080c0406030803011205070f08030903060a050c0a0507060b040608 86
    0x315118440f0402160110344148200b5060380c1c420300003ca2654100b681d00148000a202e2151a610414404000040d07503c022000154440c50082010342481d140243c1008000c00d03807103009403160507000014907400900c9081c1c00d504011403843c103420a04041d540382e00fa907040303151514000141306007103030b9000000700210b62a900003009840c041030300482c00e81e0ba12801155005070110014400304075880a11500044040c10a0042040943e12a08030f40754581c02100542d640d40020001103800106c092092041242d17011200e141c8400c0c0c110800c03842c19003c000b000b1380400010300b0040100006140b03849141c0600d80c8030003c07a8480d107001c1195001c2c141031703809280409001d03401c141c01410107683d400051a411603003040300d10380c191a11040240c0d200d00c135070440022100700303007200e4102030505e01015507543c2d00c051040c075107084006050064410325100c10001d241c0710000030740d99250054544140d8800241c2403010107852441e0321658402e1400500040c120400609 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 9591131 1250 9589881 9589883
    0x30307090b09030a030302030a0b10030606030c03060b180607080c0a0c0e090c04020c070b0403061505030f07060c0c0e0702060610050c060115020a0b040602071e021003090203010b031504 82
    0x168902807522000010300c0c1d80500c28407241c06901415101000038000d4028583c000740c40c9200041040c80c1c0e800103a0317103408501403c00030907501d500070b02c8055454090080d40c00002c7c2001e0021920341844e040b1103100302201803d51140303280880c100b035a207240c100c99140b03400c05601a1606800c240b89502e0f0868840e040b00d0a001d0303804d00107064401500a00d1184215002030480c8003140c006000295210b000c0003400c5024140b400700d01d417400080600040c43c0694000a2030072550050040e07040116000a031080d400b01c40384c10482e041c0020000291802498034200c0b00301c86140c00741c2c401c1625000898030340c1d00c14040224540c1d00044980c41082c0c2100d1040412040501c20ba80d548510046510303039401010052140c0c0e42118907012030007400740304480c114401500d4010344210155400c0b00d030b81c0d400040400510018601101003114440c0560032040780d0b0f42e0014000b6461906400c080c562a642c601c010b643c1e080d4010584480301034180c80440c410010b2004042c50106c0f4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 9592381 1250 9591131 9591137
    0x3020612010e0115020d08190903080a0b040902060d020f12040302010207030e06030912030405070306020301080a0302010b040216110406170d08010f0b04060c0507090c050c010507020c0901140102120705030307 92
    0x800000c1c01c6600c013500a0014041e60040e000c10010790408940b40315000b00700d10809002c014802010012a00c565019640243e0340c459290410740c00a0065900f040d80203807140f402d041d400d4001d40c0d12402140c40d08245090300503aa030346801e800110a001d200d1149469001d80c108220034907030190000d0610078401d544a0300200400c0c0b0030443c040c0415074111905500010500c2040c0c01040001d60700a409102103410a594a68402003680d10903001120a0b402610a010800d50240190080d01400311019820851440f010f0115001050f81c060a1030165a0850f5503d40b0303298800b60181c603000219040e440e9075900d8441c2e032200b0500c1c0d0f1032f001546807000050849555803c42069409100f1110300c1d252901900700c0e520040d1610030f940c580034040000175040c41a00c00c4901209850326200d4891409a01c2503003180c400414880c00e5420120220203150764084c03a240c19202e8a1199015044901e40100e142c800d03840612041000d0008400c1d06006001000e184034001030b90f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 9593631 1250 9592381 9592409
    0x17090118030c06030e1e0d080a020304030210090218010303080615030f0f0c040e0f0406051e0703020a0201060e1806090d020d030207030c02090a0603060b040207080906090103060302061201 83
    0x110404160032141d20014186000e0800140000f0303200b034005080c20030749041140c408949a0044440810404415220030381c410780000c1140c2d03821401a980c03200341000d0440c11850240c5011703484601100d90081c0c030542d1008072804554680164005107945d1218117811582c613450080c003031391019a20301c0c0c4900019030b616400070580a0450b407080c82240c452405646076185084000c0c1e401a00c2414248400c0c130000c51000c0c110f660085c0700d024504810003841c00c140c10060b04446002d003041c455031200c0c0c5442031990828290103a044100d5240041e03540c000c5600484c014029600402e1240c00c00e0024010504a200c0e600644102c2c60707030070703104640c80e12000140e0b42d43c0f060720f180c3c0c09608008003043c0d00304d000c0c4c1d0140c2109802800c20102c0c0c090503a001a034040400c8485800242c1c0d1a2024400d005461113050300700107041d2411480c0800a413241c01d8039024415183d0702c40c00c0300080d0401c0c43c0e403080d0400c0c401954042c0405484901d410101001c4200900409184035084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 9594881 1250 9593631 9593657
    0x6020c0d02011205060d02030a050a0204110403020f010e061306020304050a1d0a020304020409020a180501060f050409050a06050303040f06020f03042103030b030f0a020411041508090a170901 84
    0x11840031100d056050312140301ca142d040c92100c1c09010001d024652221400c00d030540075883c284035450704140304030090000c4074a03900c1080200c800344401c1440c580741c24842400162280a6400f142f0790702420a180310703100c10381c0040c0291081c0c2825862400c0d60b54030000b011a000406001500c1d400c4403224101740d00c0d00c0d00083c040070780c2140ca504480e011008204070842541c000c642150015102041c0c041c0a900460810f64040c0e0080c02810492260303201083c3c55071140d13602525542c03400c0202c42035040d400038400c0c01280a110405030b075a0001c20309020341c1b540030300010400901030b0380d1100e50703605a050305040c2ca445a000580500501250075030000b008440a54000c950128a60075003001144008050002c0c100c061650301e208001c210707503040040a91190041c0000d00b0060400c3c4144005d40d032852442c0c4080310700601c41031150414048190900c082d0301d1401d0402d60780d0f82401d8a20303211034071030084c00c004030301400c00b040700d8480402090410800e80310b142c00315101d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 9596131 1250 9594881 9594889
    0x70302090a0c05041e05030319030e0f0d120f050103050f1e071511161a030c030f0702190302070914130602090103020409020f0a090b070b0402010e01090312080106020c 74
    0x100c0e009100020f10410003804030b16400c1da480502014810444072000da154000b0a1030b42d0f018191100407054082c2c51107940d1641070140881c1c000c1070001074010521011103a50341c44220030300400c18001048003045408840340d020060600b02c06005002c1560b4a00b8540d0b00d0300c0c84503554004c54003440000e521000d46207015851061500d00081c002146025130417a40c40b044085031404202c403a0a90740079030041081840c440c00781c6010b07015401450101c241a84c0d045800d03a0b1444104288100003425443d4001c1d00c0d230180034950303480942c0c3d4039080c0481c1000c051420301050041a491384800f45a80010b207002a034107062800c01c00c1381100b411910300d903032044684251a00b030102c214000500070b5009042c280b0018100075040584954105090303070005000d803800040082034924140303a11614020051200c2d075607951030b00c000d070b44807079084060050010341844a805c2c0c0141003a40708402042c000e40e000003822840222445004005540238800c0c00014800c1070303e1b4401c5450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 9597381 1250 9596131 9596141
    0xf05030105070504060801051512070e0103060807120204150506070302061909050a03030c18060509030c010305040b0a0209150304030201020a03110406021b0301020c01020a08010e130804060503090109020402040602070302090a 99
    0x80c003a16a1380f03450b880c01e000c10021034800100b90181034014016810601c1002b40518000e00e45522403114030181c0a00060454915034010f02d107641c08040100040c40ca55501c014072150140c03408a42c7c200c1c0c40c03c0040104259174820fa0300110001a88810b0540c003081c03d034041d041481071402e0174a94410b01c003050b582480e0b0090803e8101c000350700006406544041200042421300c040d0880c10400c003500346114613800f48002c0307900066420740301d14040c445155001000d007410800f078206912444030b103150080c515400c440d4005442103066540c05840b0000c0c60114031016524982484c009005c0e40150b00700f1004242010003410700112200161401d0b43c0301340d8010088800f460f8000050551a806165055582004900c019007007e00040c018110b058440000710352402858900078040180381484084446040d00005a4484101c400310f80701498040d0700c0751034501000d401080c5546009601a10000e00092481d401007a0320045034000c461072507032551404080c8090350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 9598631 1250 9597381 9597389
    0x1020901050901050c0f010617100c0c030c0c0302090a23010e0703020703090509010803040602060109060b0d090206090a1719020a050108070908010c08180a030c06021c05010f05030105070504 84
    0x1070030a200400b42540302e00b01030041103665400b11468035440c4029a401c54005401800340051300005000109c03004000310541e01d1581c40c400c0040701d50081000340b00341007580d0005d00b080102c02e0342000340700f80e180001d4050754005042401c41d007031595240c1c000b440d85412198048005102c1b400c2d0004203e44814100e40d41c01200c0300d540e580d201c00840c004c1d0f100c980124140002408003003030340d44504503098041c200c00c000441d40d072400c01c0d90103460110140d110003030507070070000d05212a081c00c005942c80004e01510204000300d5a00c00500e150051850b07042e040128590300244c204444110140851120303015500d80000d50700001c40b07100184200a5004515801c040040f035101c2c48450b03901c44410f20700440c10b1500c4928141c01e40c1e950031003c40000746030318140551503060910007140100410000c080d0300c0280d80e806800348a085c40003030301e0503501040000d42d009400024a2007904440420005036862324040013882c0341500840b07009601c0c0c203001a0740140503500312800e82e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 9599881 1250 9598631 9598637
    0x70206040204180b0109020903070e090c01051e0c0d0f03060308030c030402010c1a0402030601050a0627080304060809010605090105150a180303080610080c0d0218030a0c090e01020901 81
    0x140e5441e028030024002c00c454255050b1025200300e004201d0702d140283c06849912400341c0d4901c2e60720700b01850f203042c942088012541060901c103000d500010101e40050b0282040d5449030040000000c0100f1401c03e46118075400043d0f8900c0c410020a000301d6082071070f200d2000b005000b4800b10121482d074040101070880410200f502a03424201555001d4414500728401c207031a580c85504002c1c880040e00c2c40e80b42d00805000440c030301486500c5c00b4020555a10180d0751034014028aa490803209c8402100845584015805032990004001c0c00c10b00b41141c0d507031503942070b004040d284102c5001c0400e500e000c4000c505803424140300d5048074401410000300000003007817134103294003c801350f2051154100b030b84900c40300261600c000844c0a525904201d1400f042032021400e04402c00300c00b00210b0340101b0002d04801803d4440d44200140d0040e11000542460741d00c60800902d450380c94802c1d224500e0800807480005001d940f40c2c2c600902c80a03076059203aa00313034011507000d1404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 9601131 1250 9599881 9599893
    0x408070209070509220605060f070b070c0f0809030f060c04030b01080604080702120102040f030c050102010506010201090c140d02030106030c150507020d03080a230601030e0f0616051e04030c08060702 88
    0x108450305c4600f28403c0340510400686507581c1c0c000180b29901422440209003404140c80050010a503212580704200d030504100781c0800c0d50350118072680b1203500600a0b40080f841c905580c80400082c1c00079003014040b034440d8102104d500c00c90380c0251108407600e0b507a4900110300000302144090250b9401203856081641540c20011680b401040340c02003903500740030024400d8011185039000b503002c0e041165400e0b041c100020b0035100010703d01819a818440207800103401032035544200c0700e140c4102505810b04100050402d91a104081d50543c01c0a8001c0180032911141004455000b069528001060321007503809004490010f58817040340c002d40800700e8000c0000c81e90040000d1400110101841d5a00a05249600840d0f01c05119041042140d503018410300d1804070810380100510015400003d654038001044469803000301443d0010940c0590700b503c625080076080c0d07188541449c0480302207900310380310a44209040c00c00000d900f503400310381310f4040e213a164046d0035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 9602381 1250 9601131 9601159
    0x9050309010c17031501030c0219110f0310060611070303020d030c0318030804020307050103090c090903030209030f15010501080108060708060a0b04062d1b050309090408070209070509 81
    0xca545182c0800d07500d001d480c00e00c056100c450070000b103220b00820203183d0600c0744914001012502e0010001c015907121a00403440b0040950300194856400f05444844011020205034410590006941c1501c10540c0814071010340b60400420703030340c0340c0e9109030114038010030603517440d0914800500980c00c01008108981d02c65042481c6004c02e0b41008100010a1540e18660715880344090700010b810005001c21894181b094400070002442c0c10300c00100c00f0b8655500f0b00e00c40788a00d1140c0b50391050f01d0401c148c025010f440005d0001419141e404000302a900d854000070754404580c0c505200010038250701401c1120305940040f40117160b5540d403000709070360b62080900140e80c031400d00c800014a941b200001030001c0e10150380c60303c001d448851045501c10321046080703201376800301c034043d0100341e2102407141000c84040303604104040904056095209024295800120b140c04100a2280704070040c1115442520503440b10f548242c000c48503070040700d9030076a1200341e60f60240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 9603631 1250 9602381 9602387
    0x50a0302090a1815150518180405060f010603050f0a0905070305030a090602121602060d060801020f0c0d0309031409060c0303010806060a12050606120309090c0306040e010905030901 80
    0x1da07012001d0300040c003640d00d4180508070320f40d15052143e030385a2100340482d20b0307402d080c007803800420440101401c0000c0c00d0102070480c0c041d144d17401d00e111004a170068541d545043c1c80c000d4240000c0603144a506050030440d0300e4020413101b2980c00b0f9189000050321034480d2281e24858900081c04201a40307600304840c0207800b83c208180c071107210341c0c1d80200c0420424002400124130171f0f140c0000281c900000a401c00042c1403c00302c440505102140c0083d00800310034184a50490305a6621030500700d19200402094205503085c0d840480e0358605800c003a001090110460000c48030f10054050742142a21001d40307000300022042002d600541c00c1c0c85000e4203040c00010304281c04d03c03004258051940d04264400713041a40800180840c906042e10031201404032b03160520311100c0d40b44c40d80c1d40d80d800e018103403500038401410f1100c46510180162218503900801322085420030421411f4139400a42d00c081c41079180a54180e40030380d05102d1250b065a002c805103040c41ea40c28019 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 9604881 1250 9603631 9603637
    0xd0206030a0b04050a0203150a0503030703030509100f06050f09160503060102150f01051903080a1404090207030f0e060a080606030402010915050c06070e03030702040b060409090f060b03030a050a0302 88
    0x41507140c6030303403007851240c1d50b90042030704c50103004000685034038008100349503031041190010302628960741c0611090320040f044a240c0741d010300300801e07503844e2041546c3c6071003144444003124070703d0328800040008098001c42c0031543d00302c41d0f0686075403020f000c10586000030703580700c2c00360200748104024070f42c000c030091540b00c001401643c40e065510800040a80000c840078884100c1c03d0340140031a150001c0b800310051000b507030103100d50342545e803210400e216001c40300c001d2007640c122082c00d100101e41110054000403000750344441d11854081d01d1580a05104004644400305480940c1011300588600d0036181c0d42d010380d070b40c44000500219030b002a10680c100070600201007110010107800024542140d40c03481d503280e82482c803640c10710794090103c0301000411540000d69030303800415a0a041c1e0111f0700010001014400142184521b900c07903408182005006400c4c0480840440b000d00e005e17003c02e0041c040d03680d0415403603100301d40a1300003260042c0021101c4910039030107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 9606131 1250 9604881 9604891
    0x60b0c100e01060911090310090506182e0b040b0f060f12010803040608060102031215040e060709090b090103020607031b02031207020f0901050907050a14030403110601080307020d020603 82
    0x142242c4c803005002c0070341c0c0c540418107446200003c0c0c155001d00f402c101d040903d10300342400708100491642c1e05034444c2000b5100d8a03030080c281400c00d03840041489070f248115400324400314030882c114800124075001d8209030b48220306d4803002c04050304290003030442c5410001c1c003600c250301002d0100022074200b15501c4022280134070450701207a0400c0641030203031101c0c000640d240c500e0030030006e0046500402e440c1c11034005000e042800440c0203c2c1c0c0d138100241080d441c2a584244000c240100b0701c95a180b03071b07244911418040b220350070075285000e80356030002c1030142d44542014098155820311001390440c0301044000c0200c1d00c038502c070b100203201d101c54001d00c0c1c8000ba0001f030b14114214080700400400011114210324098003140d640550640710301c00c01c1e603d031000240c00d59000030599401c2c031400003607161005100c2d002c206240004440d45a440b4101401c00034211284c20265101c00d1180c0c1e80041680369001054030807996005180f641c01c00304070780c2031110329003010308 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 9607381 1250 9606131 9606133
    0x60c0c03040b0406171509060907020a0507091b08040b0f06121203010527010312020c09040803070314010b04030f06060513140106031107020f0f09010303030603030201060b0c100e 79
    0x70110309100d50000510003001ea6580300645855013080e0300c15a0580a045511450025074042400c0d4480c0741700740364085011035907844c06a80d01c074020307414649031110003401c41c050550042000e103c503078410025004038050160b0f03884c04c41c01c02615401d0003603034040d00c030025a400003400c0c110906075140e030203400609094114a00c80c154540307440c3d1120005900c1c450084014811810042e03100080814400208101d0803621000b240801806010181c103901c01d90303084443c140c0c000c001010440401420001c50f5240c582070001c03481c1c01c1660342c90002410000003a08005403801c080e8140e03920202c0e42c600d0309245075034012804000ca40308584040d258280061203a8030150700c1d00d0001140c2401040da415040301c84040540140c1041c81890300c1c1c20030050700080e1070403d40d1a00c41e815a08088103c2294000403018036074100d0460b4032066000000c420144d150f0424401c880c401d0b0003d001c0701340c40e80480700c0b082c000c1e420b40100e16444441900e003448499003100ca41300035418 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 9608631 1250 9607381 9607387
    0xd02191106040e061507030503070804060e0304090203010806090604030f1809050115020f07060f120207080f12060904020d0201031a0301020409020a0e04110304120e030d09030201020d080603060c0c03 88
    0x10082815600583d0092402d81d24034420004103007040c01e4031480b02000324000d985011000d5074060901c0c00058460002c0011980c0040d003041002c3d880646059080c400700ca44039603903800714801079842405035586501944010070014800003034258080c50381034803019200700040d01e0456013000c0c07519042000020001000901207268800c19000e03102150002504980e5110042c1c0342040c0780c40f03105250b501240c03042200651040f2030851038005450401002e102941401001c4e0084440142c50820002414540c40101d640140a5044a9001e0080340e0741e40e6010481c42c2042110069089001d6401642c010f610a6000d03400641180f00164200c1703d904000c03c2c2240c0040e041a6545030780020141600c1d0340000b070f0f804985100316028040c218141c004c03500d80c0c2c00042c0004104188401d52544442c0c0250881d00c01848040e00712141041201c600030030b480030a2005038058094280c2480c695440f03020024131804c809002081c00351616591002140e00c981420b05080c003041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 9609881 1250 9608631 9608663
    0xe250b0a0309060504060b010e09040c12080903010510030b0901020307020307080705100509030913020f0405040e0a06020a0c060b060702030d12090803040b07020601050904051207020105071e0b06030d0219 90
    0x142c42000c0c056401b0f00c000050885440001621020822448510491000040000017600c4101c40000c1e01d05c0d001d040c00080b4800d150010180c0a10320601e42d055003040e08208200204004104c102c81c01003d00042a403a142d404038201d1100f81d6050f00160001c112480c04103c18000602401e84150200c41c4440c000030210412688162801718082d017000a40e90468a010b030000c00c44100040c20441c5845900200c1403d01e1145101e040d016a46451843c800c154003880080199908080c0a5540d4460f020008121090312607044030b40d145030041e4010b5a091580c00c0e04c0070341d54042d006001c2001c2614042d6900f00030400c42d8080103842d0850080003a1710783c000f85008074820884400181007110b00a410090143c2145004035042802c110100700002100c01e0f8401ca404005c5a40b8100303400100c0d4288a51030001c0c2081e603820310307402000c203002d9120003401c0c1e0044000e1041501d42908054581c15550010360050344121902c8000c05030802d20450054451802c40500b82c50b0b07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 9611131 1250 9609881 9609893
    0x1205040f0203010c0f080915040b0c07080f030402040f0e03070605060303040b0706270210120609021602100e060706110403061401240903030503060a030606090e250b0a0309 76
    0x660b642d104d000070440400040501e81180440e40c21580c14009022010007005102d5a501f00c0244050700300c201c1b81c00071a21481039482201e85241d0410b20729a9070700b10104119401c0c5d401500c00300e004074130b13103881c5420b81c035034a00c1500750102d41c2c0d5010b9498003009441c0c0001600e0003070403680d0305000c04c01000500d08051001031402d0351140c080881c881d10f02c84005010813050821490710803509400300750040c3d0740c03600f00281181c1e150604104408400b1482001000942c20142019100040c0c0c80c4044610302107000559108071a0040d1808804000b25100b450505003190080c0050203004005041500607800c240080f00440341040c0e940e03143c450583e6008504240c910103407a0060207040c07014100b0b031030880307000e443c815203001100d82c0080840d180c3d4440503080000c0400400d0007981c81d0360f40000119003001092100940340c1c4180e500405401116001900c651104c404100c010030480050142d403400c501d4800f0361a04c80c1c0144c41c0d51006020301c0805655014420015038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 9612381 1250 9611131 9611141
    0x81506010c02030f010c090f0e0702031b0705090112120315061407080a0305011d0103020d020d030e0306010b0a020d0905100503070c0b0901050f1e01030210111b010e101205040f020301 81
    0x386980d40d10342c403520f0072308050840a4940c00c24080d64410200b0041055000011102c654944460b5041c40d8107402840a0500d8030030381216902c00c001c0c1c400010302210b03100404130501d009100c80505000b003050168200c880d103106010741d5414880003013017614051040411100c601c281035501e4102e460380c49841c184d00c0707403c500300460365031801440780411541e0000200c0200c2d0145000e954103540002e41a5501070b034000340b00d083c5400504042510905000d80001c0014003100d006503102c4c268074240d034022000c10801407040042210902d84184d41d032a0032114054200585400300000841c1c140d40018041c109014213203030032100041070078901ea0300c01d28547d000045d55040c01c212100c0c031900090008200845088079481210010000c00c90440341e040724a034900710b8070000d003541c00e0304065101000c0b030300441041400350741390b0a108407030111003680e900300081569001c0203903020002450310002099034080c44501f44c4a40e0296070031901500030040d0184c002d40c0000d003919 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 9613631 1250 9612381 9612401
    0x30201110f0f01051506030705030c0306040b060705010b040b0102070302010504090c030e06070207140a03020108060d0302010b06070501060e0c030c041502010209060d020c070e01150309150c09080601081506010c02030f01 97
    0x41e43d0340c020058602c90032a000000c030072080702c06c145181032410b8014041c0c00080c050075500400000801d4955072241d00c80c40d40c26402501590301c844230750401600030303c80000d6aa01590420560000c40c1d0700c0403a1810649074140c40d030501b05410000000c00400c40c410104091542d02c102612003602c040019511610b441da00400d105800c006c000445043c0580c40c0070301480a112083c40140c1c1c008214030b50041065901892805290034220701501441e0106900000d0000385441805419000402907071180814046640c90b1800d0782d03403c512048410034040d44082c4000d00441d14080710000c5400040e01c000350030510300500182866000301584030403a90b0005405800401c1440000000c18407803038600b0040d85880404000b00000c141c100c410180c0d248420320400c120300045080a00782d940e0304000d84800c1c0c420142094100b0f00420301c02d841000300028195800080c0380b0104014015070142c40c0e2107100055940d54100d4404980c18000e0011120717032520244682a425 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 9614881 1250 9613631 9613633
    0x8070b040306060803040e0a02070c15090302030c06040303050919050604060c0302010506040b0a36020306010909090c091d011a1504080303010510170106030203070f030203060109030201110f0f 85
    0xc924628100703040b21036503030001d000b94100f800100800302c424801160700849460026a848185d403030301007040e907901c3d0441e036003190640d45030100d005d900841010680b0b100350111500054641d003004294021440014000385c401c000145403410610500c5504290114215410f162958001019500103400c004002034013460203409260307090041d9074222005170742c10000b0010328000305d420410540a07001d5000000c1c2c03801c4002c1180460b9003c0d120b0070700f40402c41ca1100c140302e808040e5106980b030900055039400049031415007485400000e90303110011100181c03606c25054081d00720f24492a401a182e2082000700c4130003030240270700c46802d8403022149405180700308071007a6615404206607100500091110030700020072281075500c00c992600c7c01800010f0202c52400206c0c51800f02000705200002c1d1084e0503402650145405171038500154a0001003102203000440d900c50000304070450410140d40a0180c0442c0498020242e841c0c800448413010301d465045202c101007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 9616131 1250 9614881 9614887
    0xe030403080a030b0103051f03020103050702070801090602040305010b03150f041403030a0506240714010603050d0305060a09020903030702090402011404031a06010c05100f02090d1a0a0501050d06050402030708070b 94
    0x40d640c6d052051561054810aa80411610f60140200103049a000003810f15540f44041600b15008010000003801000000c3c098282a494a0800303900984000c880a600b0014001d10b145800b203079000c0d686034030352542c00f6030b82d4a10a107100d40250103082038642526040c00074480850a20095124402c408004a0181001b6080c0320350084001400c04401001802c0025100403084c1111103440e0040071010340002c21100725401001030b075100401c0c51051340034000c1400e4044d0882031003028222980014030b03030b580c41102d080c0e108507000940e054104120880051900010154200d1f0040c50700b6010390542100703245c202c0e40250010780701000080305401a40001c00c40303081c2d000d402840c001c00244080d40d139070f5694860412080800c01d0721481c61501e040441d5040e60394041000707000c040ca11800b42440043c003001c0b40800c0364407242c0c1100007007800c40c0902030349040b9640a806180581c0460f11071070001c15010f80200d90602a004001502d50320800c00c0f5400340c00708a4009a03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 9617381 1250 9616131 9616151
    0x1d04050717010f12030c02040e070e0a0c02010207030509040f0908030a020c0c030309090f04050c03150609060a0501050a050a0302040314010506010f09030b0601050d0e070b0c01060e04020307090e030403080a03 92
    0x400c400c03059111050003018980305124442c031302c3d140110f059030325041200003030711a480000d010b041c0d00c0a112030b01c1d00c030381c0f0f0740040c03100c181800700c40c003c41078100c00300079200310310f0812803e0344140309001d804520104100001800c0c264054100b200120b603001a40d00c4255a4041c06680265040b50b8550740114408902a1041c4100c440309441140158a40401c51010511408005142865041c5440005410f111041c0920169200b00600341d407000c0d00b40c42045442e1500a6031514044c0c4005c0d0009013250501506040540d00161143c600f40b91618208580e01d90003000c8020405400340300020016120350b0014214968110000c502460a0000108201d02c968003020070030450950800c00700314141c80c5039800400070700c2d0140d590348184090402600c1000401c0034644a1300b00002040b0322050701400340f40384100c3c024030065a8919076000c1045c41581d010b0750640000303100b0070070780e40140c8c00710080384540c10039a41040e589403500c012a4116400c0b44001c43e485003a448 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 9618631 1250 9617381 9617417
    0x9040c050a020c06090d080a090911030403030e0607020604171b010504300e04090212010b010801050102010e030909070215130c05090103030c140c03010905030408060109110a1d040507 81
    0xd0f2000080d0340e200d0800e82d0790f80010b1490201444042e02d0860005801c101c0303a445040c031000034180d0110240503c1c0508602b841e2541c1c811179042d00020315044d107095502402003500c6024117032a0f40100b1007620f540d114015081001038603203c0790703801040041c60824100c42c00c0c8080d1503541000240b1842c00d41030486400105000140c40781d941d00200702401001022200000c2002e80f4080200d003240d100414010651140c0182d0300640340d400c6040e41c42e00541000050003003c0c1d8511a1999070341005a003654040f41c20243c194005000c080741d241800030701c4a03405042403044070310070307402d82d248040b5401081e2202034190b0000b21080d002d00c22104040d0004000c207071400c001c15071442e18020300301c4418842c001d0400d00003c50f01440058104000701034800c00030020800544545040740d540d901610804985000704000041e00c081540300d45040441d42c40c48180c07605191030030454400355041c0c201590005100a070304050742741c81c41014410300c4103807590380510281020031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 9619881 1250 9618631 9618643
    0x7030e01061511010c020d0504060f050702061b0106050301050903070204091a0408040905010501090605040608040215030702071a09090c0717040905010504150303140c0118080316021c0507050309040c050a02 91
    0x400291f40c00346548080890780101100c00312840e0303140c4055050703403008084503540b1408202961001010480c3c1d00424a103801c031041180c0769200810650f07a0740e10a00d030a94501b03c840e610b95030030620440c00035003415080800381714401d40c60450005e99511406200d03600c00c2d1415101c0080214040c8070f00009442024003404090030000412850300000426030b110b240900c40401c401800410b0131915440303600106001e0529401b912403800c0c0c10000e40d0b641aa00c03400110100b44c00901c40d0200550040301da0583d80500801d04503520813a41180c0c561203000221800000e51120080c02000710000c2d02c003801d5407040c08205545842e00b0003050b0f90110f0380c0002e500400c00c01c2040081d0304003528904482158001c00d441c0d1a1684515004000c0c2e441007506010852130030074200260f000081d0b02c60b010305c00e80000342401c1d6076412a500d90904021480f040c006010b44111180250301030700c0320780e10580c00c4cc1d16102031200840e05490700840008040341000c0303061030256806104c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 9621131 1250 9619881 9619901
    0x30e0a1a0301030311190b160503060604030201111002120403120507080f07050d0509010906110c120d060302180f07030b21010207050303040b01051305070807030e0106151101 77
    0x4040842805025040322a00c81880300a0134400e0100762050104400d21860700800d4501d00d4011120710307913003001e1349811001c4684444c500e6004091402540c011401d403409920083d01660409040d41d00540303000c1880b10490003144181d007404401e42807240020000e121070000301d00ca0350b040c5071078007400e04c210520031240f070035040204205480d80d0110210740e0024485000728999215090191100d100303072242c03401e10500381010400c07142015005611705600c504420004020207190200c070174003c241c0a20040d0300072403880a00b60783d01d60007400405007000b00004015035613a0001e00c4506101801d01c881c1d004010411031032001d456880c0358081e106040c1407000d509200b0002e140d0000c001200d142c0700b03003402040c4c04200801d6054850003603028003120b541c0d0070642007417000083c003441010b00c00c05140c02c042011030518050540500c082c1e0304c5e01100341d142c4107015405440e200454003155903840000281141161b12401c907003002035203031003143d003160040c05801d50710005c00f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 9622381 1250 9621131 9621149
    0x90408090301110a230f0408010203061c020a0b0702190801050402040b01030606020705060c0304030501110d0b01020a110607060f0c0e091f0308030907080a0818101b02010309050a030e0a 82
    0x10041c007910382c0100e00c244c0b41e17400c10806140d0f40c0c00d6160951000d806400181070740041c0103d0045195030056005500415081324110202c9280020a0707061201d0070f40000d400981d071880400901c11900b000d0300684d03100070441ca0b00c1e4111101d58005040d0300d944100c86980d114800e01c015800d013880348107041402031a082c80140d0034040080c0d034442442c4201801a140003900e860700c90030501c00c4e40c002d076a021000748002032402031340c2e0340c0d1900300c0b140400c5c1e1103103428540c041d00e6000180028282c0c0d4090002c1d4010071044040010302d80124a00f66041130b211580c00460b20414450110080c0c103648030f08107201581400d01c41c90620050490194240d1200c4034401c0101d015489811240d01040055030380c1c0d1103094040c10402d40707a003d410a8860f00402504110a000252201e02618203100110000c2142000301d55031003400d026010468205202010080304840e11142900605010030b841000f0b68800386004601d0100780c001850740d8a1001041c03030468000300081c80042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 9623631 1250 9622381 9622387
    0x5160302040c110d0507020111010203070206040308010b0c06011205030c060c03010f0509040206030c0306010507060903020c1201150306020d09020303030a09120203030912210a0c08010503010204140d030201060509040809030111 100
    0x10ba0244d6841c180e00d00900c05020000c6820411a0303c03d811148490140000954481c101000043e54400d1b05950440102e204500042001c141e1001980c024580300f13402040603900e0301d140c04030186105070054035940000c0000301550901040840d0240181d19000d41d80c1c0c0d03242103001d404000345500403902c60350b03050007031101503641c00d01540d03007004402c030542d0740d01d40703079000140c505200d0f10000a0065003096103c83c00e16401080d41001018150382c084002070038103040b07900303c441000042842080c2400148003041c0c03294050004001d180c58001036841d603540001f495500211017014071581c80c1c00c02c0408202001c2004000c094541c00190708500301f100c01c0540382c180200f803000079490040341d01035079001c1000e00b102c180d000400c0320082e07a003007036518580038042c581603120108011038000103541c1070501c2280d08480040300c0d0841d2090703d000c00c020752100c1c0342030260115904d400010a50f55030380c58116018500c10f590140c5c1d0380003090103150944035503140303280024000f4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 9624881 1250 9623631 9623657
    0x3020306010509070c0203070603140f0402010c110a0b040e060301150608040b04020f0a090b04050609010f030b0a0f020301170d020102030705090904050f1c02010506030a051c03060305160302040c 86
    0x1580c606407441119100510754a070381d4125403a0a16510195152054181c0024000c1d010351146965031800c000303014407035580703510359100148250740c001e001404000130b0b240460360101001c0f0304e256000b440000303c290344580415203504940c10025644100740148885031800b40700302046145d0300d00c011b8804a11300b0002a202007001400030f0500340c50070000404658030b07001e00d00c0b00400024a028083c50b1513040a03030041c59240d10030f50040789040045022444c0607101c050490f4560250108141c1c1944e07207102e00040c002d0f00b40303002d0036160303940d24204080f18000740d4041e103051010006100d01c04002c1c00e160802d00207800003903901c100f0600064a0b403200c111441c0390f03000e45e0021415166894020300d4294a032448500501808004da041d4608580302d038091004070307500901c0719885800416456816408005003150300011520f010240c421061540c0400a41000112203a40c0c0e00d41d1410902e01122000303002040ca13006208618151149401c00032441c50100c28034003071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 9626131 1250 9624881 9624883
    0x1809050705040b0a050c07030807030806030703050607030b01030b030613020102060a02090d03030b010203070501060608010527042306010306021e0310051201020f0d06090507050f030f181507020d0207030203 91
    0x82c500031020340b1000050350501d010b0041080b05e03190329100084a50b00f0f5079900b0000526000700004600041c0090701241240c40c000808405aa03001005810603407500791068005140484149060540301d49a103141c560741031051510400303100100071842e4500748002402c2080c010158483d10f40f060181e000c650300c40300e46000f000e81d8036040010301911048010f0b4514060141c006040350b007014000300b203050f07200b007071681282c405481407190307200c242c0360003d0740cac008562041d8103000c0d2200010380420400008456204170001b005140340340495096420010243c1066880c00d0700001c1a9400d2044c044600b136011001045a03429401c0152035001112450b1103114403c0d00c1c40000e2000082c020b50468140403c18510b031070b5a440c2da0601c040180129100b1401c2044c500b10005a14900400c200c4100c4101d54080904e10f61754081e0f041505880078080c8604824007041c04caa010104010340c1c81c0302c1800700d004403403500c0c0c400c0000785040c8007452030204640081d0b20410044e20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 9627381 1250 9626131 9626137
    0xb0607050c0d0f0605090c010908010b090a0f0902060a0201050f0a062d050303070c0512010603081e04030b0a0b041b020307060b030102090a0f1d040b040f02010e0a061809050705 78
    0x100482c0c124001c0406820011034058100708080c013811302d00703014484c100d00005806010300350300381c8500800c1e0b0307910002c4c0b40c00c807100b240e100c40c0c10001000000d1080760540d80601140d030000a00045c0340e441c20b80201d00b41d900155000300141c0c5d5510305110082508860b02075100c118104180141400d01c40d1801e100c208840708908003942c0d00d075801c41d06d142c20100000c080c06000d0201c0c2d40343c848604280740501c00c0e503c1064000c0004012580e42c0080600900c0c041c1c2e0380000f00a460130300411611020a8600d0390304500e101c400f40b01c080001a00c4036011800340b686201c0101e0f010b02918100021120701d0001282118850000c582c070342074020040e101030070307000200050135850500200740a8420403680580c0200c20441c04a041c07200b050b01003003507680610903100b40e50351091016500d140142d8025200d40510800100000c8441900303d501d64818074000070300d25000404180850b050f600302c080491110860030b94884412100e5200511030b0080038882411301c0d00005c1d01901c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 9628631 1250 9627381 9627403
    0x1051e102c19080304030f03021009060b031911060a0903080703030509060702010b010c020d03020a1a090d0206130204090201090e070f0e12060105130905031204020102010b060705 79
    0x50400c0462440e541d0040e841c80341c00354030849440324200103400d080150292a041c105105070120b207280001d090000100c2c00030380f03100f107008500d014119250f12154171702c1a001241180300ea4249076007102101c0c041d020b555417240c3c0380452120711003c00c243c141400980c01030300514020046401007050069030000c00c81090b14910741d9415a05011584031015410182480b540098a802015416070220748604045000c1e50b08a8442c1003040b42a82c41d05000140001e1481210300e0143c505490403805840c880e00403a8003403501952210382c058440b045c40285111903008200c5200f500740f0040e5680032031f903c06007866282600041c551000c100b03001074001d99a500b403038801c59009013002d10213480c0101100c00c1625140b2402020076004000007000915100d01420150170074003035240300300034204042c001c1a0f08120601402c0c1190304691481a0b46400440e00460001d01c02040940118010b80400d4a064000a42511b29032000346004841c10001d5030003050000c02c15032000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 9629881 1250 9628631 9628639
    0x60510080604050a060504050412020601051507030302030a06090510140d0309030b0411030610050a05090402010c120e04020d020403020a06050408030703050c150a09020906060408030a0503090109081c0501051e 92
    0x94840c00c0313010300144200e8002035080f92501060100781725100042d006400c10550844060340e03200e0080c8200c04010320f0903a0090542881b0540000f806070b000366900a0090314001045561200954165002560940341e141116034041c0441448c0c80c944484460f400c0e6003400e58000c940d68020003a856920000d0811004e50012500300645031110001564009040300c2c214100960658101011886000e01c60100c404d000242da09203440b4281c8500e070143c50f03006420700162030390b40c114880544820200161009a281b0355617072440a800700f031812100c016112811031042c040c03808990b420280c1031000c10b12081100003400001c41d2a0320b0f03414600580c882d4007188510b4036102c07040e40d404a014210104000701080716920101c04140201c032542041d4480d00203101d07a44c803d45c0101c1400ea0000c011404646008900841d00000100c00001d148a8251198203160f0005660301500381c3c40403608600c2c01106c0d018042c0948030480d00d400c1a01402d2100092099030202d02a010f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 9631131 1250 9629881 9629891
    0x1203060a05150d0903080a060e0601081302010e031903030b060c030714150f0a1a0603010909020a0801020703030501080f011401050405130c091b020106051507020d140a0303060510080604 82
    0x82060b0403003e407140344900c40302c1880000d0080c40e016140304000c61302d840440d407406000060755410101440d010340d8042c1c64007041910754080c81c0820381d183d280241c2c140900c5002c01c019a4404009a00984d590000034400b0241140b800505903041d6000041c4030301400d1207440c10302c1001000b2a242d0640c4004441503817181e4405150030030482c0030f414140e079240340d0104819407055106c410701ca400c6007202001000030070038001c40181d64005526400060030300c0140024001c40d400307140c800f400180024034007560742c1d04090a80c0e120740e50403000240c480b001049155420400303014148001e8001340b00c1c12b00760200e000d0b00080c0c14402c10707219540322400b20b040c4441100140501c80d42204001080688a50303000c00a01519044042c00f0903882c054030221a1040c0705080503120014171141c4d0701c0c440e40d1a070f000103411145043e40d025818184000c00241444401d0200341c0a40e0050f000900f4942405800c032811a400b460040781c1d015134010131a540f20300180d030320050072140015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 9632381 1250 9631131 9631159
    0x2010b190b0309070b04080304030c0603180209060111030c011b020d0f03270f05070f081203040501020c060103030807090b0309060609090c0d0308100b0406090306020d0212010b030601021203060a05 87
    0x100e0913032a540403e5800900040102c1d80c0600800184156402080d41010032039450700c003242211030f103108010408400076190001403410301c20240d04207038145012480154030842d454119400030141704441e03951341003281202a01c916880340d06600d207002501c5d081c0040c24000e041001014240020141d03034814100600304240b5400000c40b800c007081e60740d003407014070304518004e074090b20580341481070410000b00808404031140035955108040d020051008020301c07669080a4002c0384c0654090044002c0d24204000e000d0085000703540c1c110320380c1400c4202920015150700a502383c1001027040181c10000000c200750081c00c00d90f0000c203071b43d8508894508084400d0445a07001c0170000f00c003401c1c140d01c540c52a018a00c0e448031070808a685000c180c4843c404c920a29001c00d050700d40800210b46554068034040040000151401c607110387c5142101000340c000c4000e03031101005203c00b82d40c0c10005000c1220b9100d00c160f146091250006041a401e403003100d111b07049c5101004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 9633631 1250 9632381 9632383
    0xa05090a080c010905060a1802060304050c060f130e060105040e0417040807050a0506041d1807030803010303030b0a030b011a0408010213060f02011a1203070b0901050702010b190b0309 81
    0x35800581044020b9201d0319950100c901030940b07464103940718800c11000c0f581071841c0c1e20540e50303001c1102074a409102096800d0280c903800080080d83c00c1e02650200c2c412644903507006041295841601d40d580340c0c2401400904580950401003021a49400700005070340c10408079801c0d640410f002d0708050351240391a48440c2d05640ca8114586004680054607031030000e490700a0714002c0700d01b070200542b21401c5c0b0169025500c82e40e00d00c0803210310508200740b40740340c01075005905080041504250302840500c0d081c0340c0d40c402c9070490320010040003810307803500c2070320b19a010403a40d9442e11886e5031500340e46c4240602614119040503401142101d0782c00c0d0440b8010085c1340000e43d00d5245591030075000319031078820000821191700e01903101c18410702c01c0030000201038030b00c200001480018400c402e480c1307108840d03061008101c400c01040220441e64410f042c0716001240d1403031300210003829503490354203040c002d110b0b074411800e04070700c0802540d054030500d0300d05a4032991000405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 9634881 1250 9633631 9633643
    0xe060409120306050f060f0307030c11010606020c010909090b0a27050105040c05060c030a0c03030b03011517010e06010302041a190503060c04140f0102100c0507020909060f0a0509 79
    0x28801c0d58819281c000d15901030b04400203c030000c5070171401910307240c0c05102440c818101e405500d0082040001c0e8018025031081c0c02c0d40105280c4001f50130b030920b00d101d003140e03c2c03508008096440b0418014031076030b1100d040d502a01c9074100034814000d2a035100c01c0c041b58003805610780e0383d40300e4507900b1b900e9074212100b0b00c00301c2c911041420380d68030b2030501e14002e103419a4159103143c0600c10209542c141a400c80c1e04820880c0001c40c038103500d000d02129036941040080701095120400c21a9641d000d000c0c4030703503807030b420742c00c0d107510340d1034018612a00700bc4690201e00316410040466001600480d60310b04403501990b01007200100c001100342003180982005502c00c0d5459648541c003445030b114941961002d40850398030b519804404904e80c02180318404195951901401c1c441c1441e00d0705541a69040c01140c40400c0b00402da001034510080d8001300140340844c3c4681589000361016411428020280c01c990816070410310302080010050007038692903001241c50344504200d2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 9636131 1250 9634881 9634883
    0x203090418020907030203040f0609050a06060b0309060601090602030a05130306020a0203040305160f060509010915020c040f050f0601180305010c0522051f030605031c0207060302030103020a0e060409 88
    0x800410055890070011a20034840a03800b9010b001c0000364051702a02c2240d0190f50040380a03000f00708169039000161001c0381c022260750041200032000600c103801000003601d5507a51898403454031101d8035213025001070159040000c50201000fa4640210480e4056089854460742d954041c0405480c002c100780d0004249910001300d81d50342d00c1d030101c054010b07680b0603801e4540904c07100c9640362a80c0c01d28041c200e007076002c00e00100040c5020780002e10302c140d010f050181c03d040e5162a14040346543d01d03808405070b0841c4817100d5a40c0390170b101d18906400f264500300b0680c104101c0d5004da40800400e024148061b001c2c10610000c1c440c40340d0002103500000030720050740500e500412035045458850741803a030325041c0040b41030710342d007800c01034520150111002c0a0b0311240c008002d0010385444043c1540c0e4040400c903902d090291089201048101e04c8448400680085c0307009641e50001040610500050005030389461041e030840348800351076111900e5000001e401000d501d44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 9637381 1250 9636131 9636139
    0x206031906051203190302121303110d0905010e01020604110607080f0703030c09051e010f030b1203090102070815040807030e090414060105040c05030414120d0204090f020703020a02010f020309 85
    0x540c0c280e400f04000010066442d40c0246480b905d10f11a009400781d0040300e501c500d0360b184400010b0700da840c8203d00c0000d614000d10340745040002000280f400c01c50500049400114602000e0196581280400d29030302c0d400c1c802081c00703250645032101031400b040d407824469030001840505000d804000c1d1120b442d00c103042c00da5600340360b01d00a0001c01c803441d80d050108124120026040c6002103d0740180b5020007503807040d00d280d6400469501c1000300c00c0505055540e41c285c842501e400c01e10f02401c49140303000b5903403054001d00192400580350710242d000e0b07200820812003090072503011908180c1c4007800030380b1420b09140130350303070b02d0030042800e07800510003002c000c01d00c501d03c020890460102d4098444590321030090009442c0307200b0b141c1c00450410800304000810501141440e81c00800655800c0712195400a03260352001d40d03e249200d4010409000f400c820380329a0184040360b60046161011170358010f0b4503400c461001906200d002c0c085000e13254028401c039071411000034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 9638631 1250 9637381 9637399
    0x32a090702010c03112502010306080102070b040512030702070b0307030f0c020303070908030c1b0307080105010b0304030801060903111e0a0b12060d03050313030c0203010c03020909090a020603190605 88
    0x15034028000c01402c02007900107420b1009032903007a141481110945580b503010505194403c0c03c4400c0604c2d543d000480c1055a41e68001440b003d0a00c0501661032042640c18540c0c181403e140e0710300912041d00610700c4400300140030721140c0010b10380b003c0326590001d840c0c0b25030321101d0960003042010340c1421080d040100c1b14510741c1c1d011000314491740098661441040e1075100b0a903490207a41071012540d8040380c0f5800c20818032080700d400030a0010102c40c0c101f5242d90540d42921000c3c1d00110904202009002c2090f411812940c0075040303030724155200740d01d141c0318106c000201c0c5180d1030083c0382c000f400c000b4081e14280c104040c2d01e0040c084108035582c03400300001a41c41030900340c44080741e540104220703180c402005014a90540c1c0e4041c20f6031213110802100d1000380e042141031080500790200162001e010701d10310040651801a19001c000f4107000399401e006080304d1a0750042c200031401a5608004e0700c0e08901680040350740c03c171040621100600031508127a50260b290 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 9639881 1250 9638631 9638641
    0x50102040603091208190213090c020105061806030a08070204090f0309060210060b0405040b01050c1203060a14090a0e0a0212101b020c01030506010311030a0b040e030702032a09 78
    0x1a0407403d1424828005403031100c2ca00b5008490525041c0e480c5520210b0102c02250501c1c3c00b500038103c8a156040c1ca04207a42d50b4902d52000c1312041d680c10000342c1d454100304100c0713203415003000710312403400d40343e500c0c192800384006070f00c030744043d4ac0c000c0503204049114420f40d1204c1e0b0040c12040d0b4002480c4d02000a2428050100c1445118410042c803801038a02c40041403402a0002c850403030740f0103401d150034081088094208000c609040002c2800540d0340524100010f07080203c0009949640c2c0c05c00b00140b004101803038100c01c0c020340d0304941c150305a48445141d640d11007200c82d07000550b908190144e82c1404c908100180d480020543c0e820351440c070100b000070a04e01800710070804850b040035260b0500c01641d07048409a002644400300383d50180d080154072000524000840080c41d00d42c041040c0c00943d40107926a0350b4185c1c4256508251003407400e201c0000c80118106200c59001076564002c20045216a0084032128107020840d20800624003400405215040ca01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 9641131 1250 9639881 9639887
    0x305180109030201091202070e060603070201090813030c090b060a03240608090d02010b0105030f070e0a030305090102010c050f1605010e06090313060503060a0e15040618050a050c091005070501020406 88
    0x802c9019605c641c00140306c0c4d07070064000030f040401c880c05405107100d19074600c0100000d0742c10007440d002c10365499044000c0092032107801026100155600000e4080c1142006080000c0a03000791038543e1620309041e129646031010b980103a80f5510b004078860740201216803103c0412030b40c0d40581c0a040c0740101d00c00e504003012500ca81038201c11680d49400b4a5012805c1ea100100782034081707001000410042c3c039545201d03580c446102c3c00c1440701821400c02050550090f0741c416000942e0102d6070011540c0c0c280212441e00301c080c0740a034208000c00c00240518070079081722a0071b403000e446c4c40c0f0040103402c1d0403001004000070107885151428012040c3c4950061500d804640c42d40c1401160150042d01070324051352010b0181208281000c030303080b40041003c2d250507141c0b08041009109903666000c2d0b02c000c1c09a2864042c450341d000c482d420181da401030820080103003413130100468000250183c44440c001103903508516040540c2c191428881c00b00054015400090013140c010b030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 9642381 1250 9641131 9641141
    0x151512011509020406030f0902060304030c0609020306040f0605090601051e01180905040213020c03030c0d1503030f02012a0507080d06080715080603060403030b0a082a01020d050a0305180109030201 87
    0xf1081e1001c0c000e446240e03412004860032300380001d40c0a0014808200841c1c0b00f40307908181039102d2040000d1120803500001d2900300e04540807981c1100041cae07101d003089103134000e10ba0000a4080204419414100015030140e8460b024101d612a1080c080c00c541e80301e149010000e8056000d00080103840b006d89130701500d0221001c0c3d00a114600e000d204001145c400c59491740b01c210301440c210780355040010384691100c5d42c181b10f01a150350f503a61141450313080d40ca008501c241ca54510a044156001e0f00b91900009010002079074980d5002e0900c0b0503580d8400300140e01c1c0340551b42e8142e14900000c0ea401410b114518507450142d000c41c0102c0d000811a050b1009100c2c1101414021201210703c0c80084074251b4140d0844404500004e009070860440c20307400400600b59661610b200502e80030340070f0241290824644c16600112801002000303040c6000e01c040c108203600380001034074510034545d01c80704060384c03200080e044000d0211500030b0000e8400007806402d425041c024007030310f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 9643631 1250 9642381 9642389
    0x60608011d0d0903020103020313050f0607120e03030a0203100e010611100911190506070501140108030909010b090109030c0603020304020f0910030609020d0602070302060103051515120115090204 86
    0x7a8146503112034074800061188807070820b5035500510a42183d0044000c0d40015007803001c002020380001001032800c0c050200b921203043c0081400c0d107005000104041620ba503600e8269217044d084808581e000b10481e0741c071411204025940f9190000c00c507050b101d6a5100c400c81541a0307001040e0036900030b98049800002c1c1c0104c3e400244e1860482c1e0440c0c0e14110700800005070302c0000941070504014105003c0104242d2132034550f96400850a10b40c000300d002c88031a59201140d2503800481220a805032003081d00460820a080010941101040c094030306400000b08044002d40c0c49490504042c2d03920152244010782d0f600c0b0090040e420a1b14100c0c411300002200c1c07141707070500d4868540b09003e50f45102114514603192800185401b15043c0e8200d41d00080c5000402c000c0c0c00101040c82c420340c01001e00d9851410524103000b144402400300181c104184403000c010f060b00b80704c014904030f0700b02c80892483c0c9601401000203094850f101c8440400000d40d10800b640940111 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 9644881 1250 9643631 9643661
    0xf010303030606030b090105040902010e0301050c130806041707060b0a0f030b250507020d0f0f05120a02030403020f010e0405010312021006030f060903050c010e0102180303030f0411030a06060801 86
    0xe80743e40c015010b0b5600d655080c1e42100140c40104941e1800d5044030303d5150040c10034001c207048000c013280c01d40e4022140c2d00c903044c0300000e5040543c10f00407030400061107180090b202c0c0741016030321501c940801c048840080c000200d900424811158044000b144d802029080741c1ca980e8201c0340e0380c0d400c040c030054804005c5400050340324007200d446010481e110100c3c0044200f00384109032140c3c1c01c080c0c1e090781c000b0030a0818074005205006082d1243d802075141004840e89481c010740b40104607c0104101c0200b44920f41c1c203103400205403010341c0e82c111410001852003400494980f11545102030348142802c3c000424071641c03d0101c4001d150a80c20380c1d4000042007070304400da450313a120041c060040280c02c030000c00c0c1d1070303440078800d070340f0a03d4a14030b01a880b00f000381c20758030b13441c441c01066580011024440d0020302001024900c003075018504525088901c52500718000b00040d1038900304000345c0c051554103008400c02c6940c0040c003080300c252100c00142c001c0c005038400d5001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 9646131 1250 9644881 9644891
    0x1060c06050a0902030601151116050907020312060d0201120507030b1f050403080d020702061201050a0504060509070c0611070507050a050301090b0a09050109020604080109030305060619050c0309090f01030303 92
    0xc03040b0207000382d454654025008000d540d00e8580000150019102c030001000030306840c0325076000d400e1040400d012000d1201c050701f81d0a1000700005100c0280881086d9403007081010081c0f504400f8003a03000100701d9071020940074500068428800401d2480d58040c0340000300000940c159000c4188580300351440e072005c030b1900712105003140006031424007140040c0410000a9070b24030081403503014070000542420200e50100b5440e40001031558000d1017000010f11560a0905505c002400225802d101507840c0c5000300e40306000c054403000800582e050400c05000850300305428400c44040715980d1040f0324203181c0d484011a0007900d1041c2c22041c400103861070140280401b040d000b05d01c0b02026201e00110b9002401080c108460703039521010034001582d101806007000304002c1c1c0020441d00c001c0d240007800c540001b490280b0440041c071640c4403200c08180e83e141c109010342000750f0344a101183e03079441d5000702c2c04050781c00320345070040221030769200c503013281242d00c2a241400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 9647381 1250 9646131 9646141
    0x106050603011a0d110307080403120504210306050a090c02010501050301020304050d0c140d080906090a08030a15030204060303051209010207050616110d050a0e010804020303030103030305060a080601060c0605 92
    0x2506100a110b44440c1007650040150940f00ca80003d010300754204400064010060000e144240c004490007400300d0404020001815081495220170412400702000b240c0351607030b9804030144054a1160340d80b0014400b00c050135001758040c60141400405001109030b07240c0d00b020180102562500c015400c1a0000070f813800c050080e0f81c02960321901601950300f113814202c1e41c0b2040d0f1003065400c01e0030f6107815180301600b03101142e042d02c1c041c0d54204581c1751009441d440c01c2c4000e4a40c000c02e900c00303409140482e03444c00589402c0070b5450b001051480103511a80c00701621034001950080c58000000200f54003c8003d1484500e040004e0b5070b80d9a5401c041403c03070043c1d1602810326084980041d420403400006c1445184040c1890240e11020040892805900f0852100800d00010300603030140c0e0403641081c40c1841c01d01c0e20402c94030b81903003c01e03228041844010189600c880100746255601e400d544098000c00301217420301c2d039681c40e006007580b48800c019507400e45800d0101e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 9648631 1250 9647381 9647389
    0x180310060504061a070206070201052104110603160809010906020f0903010501050604080706080601050c011506080a0c1d0a080303040c0f14010203030f0406020c120c0d030501050d080904060b070311010605 90
    0x707881340020038400d41049500c0d020b02100d81e1084104030304000c0700300100c0307400c03103104c000c000200414108213101610f0980341c003581111980c0e1685211311810700c108542c800381080c0e0082594503a14000485d51a5505604d0140c40ba0101c000d0016001041c0781843d421100701415500030114020310050341d03158140600b5109a005820807500a001c0c140506400380302481e4001106240c0540703840c20b842001b03401c40390071a8142101403d25002000404c3d40000d07030035000000340c03d0404c01741c5407045014144210440814450301c101011190352551940c024900501c0213034181c9549180c2844c141c61842080d0003288012560140b020403005a0404050741142060b0000e40c65602c43d455035100d0624010007c0340c3c265000c000c3c03030116003018001000e09805400c281501e4031700c1022403074141040c00038200e00b00340c07030400100180c0da5125002111260031000b540d5440702e22760045005400d05811100e148403000840784c04041c1e11500c1000708035000350080082580310381c104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 9649881 1250 9648631 9648659
    0x105040c050a0e0a030204060803091e010e0f03070306020403140f01110f070c09020a05070302010f0506010c02090703021e0405010e040902030309040216020d080304020102070608010e0a0218031006050406 90
    0x8400041c40030311480b410180524804400c100c801041d020029540340e00140c00e440003908400d169400214440065040c05e440c2902504410788103107103070313422260000700703045030540e141449540e40303603103500450b1002e00100c0003540d0025015907950f9180e041142d003401d0711071400c000134440d00003103101c60350044c4920206491381b625100d01c5c05900240c1c0d00200d401280e01a01d480414020002d200359a0b03100030008201e641d1640360700c500712403c01900b1500c030400c0b103800b200d05050030828540c1c0d001c9000007d4583c1181c20180366114868100c0090284140e040014880040080c0e007008503240a04101c80d001da0720802c13491410401e0000b0b50710810700007034043d80b050000704110301c0c0c0b42e000b40c0003449441000b680c21080303d8000580311a40c0060540d410880041403105659041c403c2c90003400003070405404552404000b40300b003032401400b0304401580442c078400307000343d00300300041c2d0b0382401030031181200f03070f42046140100b030648a540c0c03090346030401c000f808085013504 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 9651131 1250 9649881 9649901
    0x81504060824010611070e09100609050601021509101806090f0209010b1c110c030412020108010f0305121c0507080a050a0b01050304150204030b0406020405101b02040b01021204031a010504 83
    0x5802c0303251503c01c0c50303503487c0d20203003094031076000d00f03800115424110700c00d1a004056001d40440c0d00d00341480064107000c0c092071a84490358030001000703480d1800080081d6240c0414000050910300103184880d4140920341c002c151904004400041c80f0701c20b5a0120298000c071600d46c0d103a41c3c0c1d14581c0100d0b01c43c03002c5a203040c8284110078201c009183d0b01c0100d080002c0d8103280e20308002c03200501d08591050b04130640324000d410801065584c8410760b80d02414601040304003241c2035450f190340e181d181c8400e4200002c030001c1d0404400030345415803214048000c1c024400c505190501802190084079000007181c9090000b408000c000d0140844410060310740d5880c0d80c440b40c5660100d070740003102a02580360200000000219906019489503004d0403005803507500340300c104410400000d00090030080c54100f0380444c0000c01050f50003259044600149809140005034117011440c2c0202040c00c90119000040c0078926918903080303103140594240d6681c0340c0041004881c80000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 9652381 1250 9651131 9651133
    0x30403020d0807050903070f0905010f0305030403060216140604050d0e0109120203010908031003110108100b13030203070602030d0605040c0203030103080706110a090603050f07081504060824010611 87
    0x1d0361140690069250a42100302403401e90710b0544020007103440e0100543c406a000c1c802048100241010f03441568054074001a102e1f2144d807441d16044d80e02c1c021400041c00d0f103680001c8140d200050598003448481d4080341e4945d0440c2c0080340c09448980440703003a0f41c1030080c02e048440d514032514080141150584030703034021504004014111a13822300d004c0b601590781d07850301d80100361041c01852007164000a025901d604600e04540904140038449052010f81c4081c080706000b400c003040d098030308404046854402e40c1604c1140180d680d40060f4141c09000404260310380d022008050307a05040505221140c2d40c2c1307062204541101010301e005030014001480040c0c6044014001280940004101000503001e11415a4001d400d2134020a454180c108400380d0540103096110100c4001e08407185409440580414401880c45400c1422040c00c8011640c603a407081c0c02800305c80c0c044500048950940c884189480004103106100307190000407101e100d03004191004040d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 9653631 1250 9652381 9652393
    0xf08070c0b0a0b061c060303091205070501050705010906060807210f0b060d0605100e2214011103010306020d0501051c020409020a03050f06100501260901020417030705060a0203040302 81
    0xc91040b00405500a200c1e900060411020300700611181c990b46820250000010b030780da00d103107400340007030b0a15807242401418442d4400c01142011031504110b500a007407150743e80009207801c50060002d440300400c150319020010520b40d00000e02141a0359400301c000325054100340c4984008041010001d2030300e03012030840302c000b0f20005200b03904403001030060f021145845d500ca4059810454011841a180311420421507001050058011305800c0980800f608800d200e403009187c201070107410408010315145c6c1c2a9000d500141c1c920f90440c0003182c0701c1d40c6902d002006075100c24203518040d8200320011039107150040601c96000040c80407828007039415428400907020601d0243d074070880c2450004040781051007020a07601680001d01000c0c030f0800c1322044551240d4100504000e152514010120b00205940343c8486907007803002d1a613520403410901a10640e08a207241180400c0946c0b81e820001016003400c034400d200b9038806a50380e030700c0079040780000c8030080e00591150b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 9654881 1250 9653631 9653641
    0x106020a050705210d03050603060601030c020a030e0105041a07050c060a0207030f05120703030b0405012108030a0608010c02070305010c080c0d0902010909051003050c0d080307050310150f08070c0b 87
    0x60919410f50b046034180c0b98041441c564040781417140400300840801d40701d50400c00c0c18a8203105040d880142400c04202007604480025614421402d0080030b0080c201c01aa10503800b85082c0c40081103084120078413003005d0b903001c09440c2c2207807004440b11720401040307841600e003480a440d050020340d4001c01d442e92a6464044554000f058252141c1c010715041008481ca8007004000d101c0c0641c401260414201d070a200840300c1c141c0c02a98900400c02c1d080c070450031401d400d507030690b0f048805039407a40c4512200c100240515480b148284d86800c2c805186950003148000889001c1d03402002008560f40d001d0b10901e01c11102c0c3c03541d4007410444404000705544c42180d03030a0040c500300c0d000d02e854a040c1c1e42126415070300c40c03000c40b584800800c1081010000f40f80382c244191040103a810300350380e403800c2d207001c09400c22050140200000724203004080c1540001c01060700348842201020b6400360080c01941e05050001d50756200048109005240007044190b00120400313040ea24 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 9656131 1250 9654881 9654889
    0x9060d14270d05120a06030203070608010501120501061e03060e0108070e010b04050108040204020a050706050c030108070609120308040212030d050a0c110c0f0102030708070818010f020712031103070302070602060106020a050705 100
    0x10041c01d01d884103550346c1010002d43c03003c0012a020341401d4503280d20650401002504a92034401204a41e0341003000522103240e0080c00825440d800125a901c144071040044e0040d00590300030f90314040c01e0000014041c80006402c0045131aa104801402c3c1d0700c0b050105461320031402094080340c0c29802260040c10150b00520162107186803079800d2040551701c41c429504103446c14031641001000501030058140040c40040610381001c00315980703010f42a2a41240300b20015061000520000d400d540711400301d020400e5500090300c1c0e454101c4041e010040074103982c0401d04070b15140210704e44a00955814045400398170051900100c0c4108102c40003404660850441c0001c2c071400000841e400080e2581c14403900e40623840b03150400c0e01e4810700340301d4400305042260100c01040604e401180400983e80321070300003680100d203428140c40c50841a040000e4500c80061442c060550100f5014103651a55080d241540d9851501703d0f41d60b424040040c0c001e80003210200070501d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 9657381 1250 9656131 9656167
    0x40602120f040306050a0903030608010204030b01090e0102070f030305160c0503030a11040b040b0903060c03010f030f290a0c080c0f030613060806041e0809060d14270d05 75
    0x100d0701c0110303103002c0e183d540b00026a00d043d610f02040c0c0f80c0701c40d00d4808154050145c4c10241103500000c5041500e1500c0c0d52108a8041c817440e410240c2d12904808100020340481e0318464001940c0904200c080ca0000c0080400310741140d03880c0203400e006601a481a4100f43ea050303001030007103043d0b41380d00b46010010400314001c548035440c10840001c000492601405c028540d51001c140c0302c3c43e221090508151000f00182c030a04000c00043c0b10b0700031507289100a49810242e07100502500349000c2c6e002d1650040500004911007401101c00b0510b030f01324501c10513070b0f84418084500c4d020415502020262500c8140d8003003030103c2003904030400003075a8031680043c0010030022107400742d882150000d4028018641002007008180818490546420702c0800d4549a48000da92501c8031035014180940340304140020b0302200c01001a00700110444c075200c41c000050070310415003082660f031400b1035002c0303800751603240312030180c04200314500d0152503c5403460403060403901404c0003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 9658631 1250 9657381 9657397
    0x82b0e0706051b0c0307080703060e0c01080103080a020705030a06020309010f05071d041d0106030309060203040f0303080702150108031c09080409050603030403050106031208060d11150403051009030f020304060212 94
    0x2111304258060b4a54040120000400390840030740079181c00c504005c41580d410103600b51141d4001c0c3d04000300c42e6840f01c40300781102c3e000000d403a20f58015040c00c0f8141112503000307541c18482c603c0001d081c450550300850003444402c0c0200101c0a00c0642d91050b102c04940c0c501c089034540c2c01158400352118180003960318005d100107100c0c80140f0818243c542c9040e10a10300d69921002801015000b50344000540201d00044d81081d03d1f055001c582c24155002c01810840c20b00049000b05000300001c840c002c401c511020602e41e110f60f43e999803a00b00030203005002d16142120318503800c1900c40e0103035041d0000d40080c5010306043e40c00c2d010706000340078140c051004000c00030200d4000e07c101300103140f1420790030038090038800004126180c05004148988181003058000034244da90840c0100780c15034019810386100d030a0840325001d10340c00509940103810202040c0e01c05036010454191003600d404150400b102d034202e03070328040d5020304005688450580710781007818002600c049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 9659881 1250 9658631 9658633
    0x310050a11030a020c0f06010308030105041d03070f051006060c020603040f0f110103050609010608070e150c0f0105010608040c180902040e0d080606130e04082b0e0706051b 76
    0x301503544945076035030b104a480c900c10650100c0c80c180b9061050000907140b1781d03100000c0800b54150349810f2050311040c4240303031095943c0c446060a00c100d01c0440342c4640d04c02c0003560340310314041c20403c10f12011030a08880300c4c0120200003c260031103220380401d4800702d07a1080c20304240c540c03d01210394000b52080c3e41100003c0e00703200000d40e10104d030b09110340c8502e07813071741d82882c0d03800c000b4081d1400a01010301c59a4640c0040c014543d1003140319520051b01e180c11b0b92200f0701c00001c142c4640005010700039600001030801401d820009607150729001c0007008000d03582c0d03120002c031407402b001c1d5001002c41541010403c00448500003c1c46e02c0c0841c070000040e10b074410b60000d0211420040e0b160402c0e000a817003c500540c10000c0c141d40240d099407440d04c1d00c0340d4080c1040c0781018034081d00616081c2440410300780001d02c000c0d82c0c65240c1e00f1003508003801c006d00300d420212a03000426081030b401d0800d80584540042401c408039072a40e04c4031800e110000c0b01c0521209a8a801d50703200f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 9661131 1250 9659881 9659891
    0x9010c02030c0a0b04150903020f1311030a06030b0a021813020d05010e010303020d02010c050306010c170a020f060106030207030903020d0212060414010c02010603110f0109170c0f030109020310050a 87
    0x81d50300e00d0483c070000c0c84400c41e91a40c480c5449002c0000c0b6103d05a84018404901e00800158aa03508100802c2000310395070705240c4e82c00d0a0000c01403400038003c03100940c003c02000020109a03100da01501c0c065604c561041d51410452001e0744141c03000048030210301030f0030003107904003402d11650310b99402c5805070602c544412445c0490f4404d0303004c81350084c0154010001e040d018062451000083c1c8000e01c45042c000d04054110300c00500303042e0411909001e00300a000600300141802c090704048560b942c881104029518001c03074001c80c48a0042c80300014887e8007074401c948a00b68940c541040d050302d56003c02200c14401c08040c8e800400b013034060400040c05100345407085100e655191090b400c07650074a400c44003100000e800f5685444001d1000c0381c0c090f8107440701d10b04102c5890b4003401c82c80d00102c80a951544c4021000c000b42802150b4007a03000c102d18484040c1aa10400310292903400c25099402030b04010b50550414400300c808a40c0d15040158480084140411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 9662381 1250 9661131 9661153
    0xf01050f04080109110405090c0d080d0b09040b01031a040b0a0f060506070c030c09020403020a15020309030a0b040506070f1b0204020f07030302090f09010b040603090606050a03050d080f0c09010c0203 88
    0x2081d1104ca00080b900500714481007075a900d06071082940000f00080203141142803000821001002e841c400b5128480202d02001081c445070421890743da400f404000d564102440d089400720400c0c00112140300c0f16201c90f802c1e2a6000400900c1150004148415a101d4084040003082490550852152642c0c0d0204d401e84a0b00c0c0104142d6128540c00c010081c0355007400804541c0d20f810030102d880c0100702c2040541ea4078100340303007500e10b10800c02e034450580d024240d155118400e50319415024804164041c4039074802c071544500d01032001d4400664071a4230850b070340c9002c2000c7d10003040d80350425626440380f81c01e032817200078400b510040c07a100e505a00c4544030b400000c0c0850010341c00080002a600301136010b86804c80c0180c80380ca5980d410840c8504443c012409000300700340d503905582080c0720042e0010002041c1c0603090003511a102c0c1892038070b9441d03440d4032501080c0e003240494030b0303c9400311001d403064610820085c103094450004448203407415a00f030b41d043c458058048 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 9663631 1250 9662381 9662383
    0x40f02011815030e0706020a0209060a1706090c06090603010e070c05030f09040f020a08130f15050a0c08060f240f03010f0905010302010503040f0206120a0507090509060f01050f0408 80
    0x40042c04000003107640380089050000e00b500c1c54402c10b01c019400c18101042907580010b02030404070750407903403601c081e9503400c04100b20301c00d55808641c2c00007880b002d40b00404c1d80401c089004220110584500e03004040c00e1150510890f0300c5030303030005810801081420010386d5004c1d00030a052501540c1000a9102e00e86150026041d0340c480e141c001540b000303107180030700c9222400c10207007030b00b5420302c07a50040c041c2040340010190b49480d411480218200280d03c026114040da00c049140c28145540c601d05000f010102c2d0140801441c11000190160041d03012a00c00d22005018551300d20b110300c280413032403459039454244101a58213021100d2603031006001c0b8409070b042c59030b49035803401c031900e00450307140d50100625034030f051f00600150740e028003100d50041c5c004404410039596031010400d540315000d92001100807040c01e0226503040c5800060103012903035512410359403034604114854800740da640345e01c03036040503412195502030310140003140e4126007154200b65039a8089 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 9664881 1250 9663631 9663677
    0x50702030a030201020a02010e0a0b07080601050c010609050a050a09020d0809150304060b0102060610090509060d050d0804140f0c10030e060411030d080c070303090206040801060b0c0106080a030503040f0201 91
    0xb200580d40200301c20303d05550920a10000a0400b0020003009503103494002c807002c405030911040100c0840041d9440e40a14100d42042070140c00810070b4035a1400c4010003040c095991002c210f082c80c01040c00d020b414080c100700e00707800800c4404810b2403555110041c0d8840006503403c01404a0039001e0340750110090352089020b11400b003603a6001100080c01c00d007004003100c0c4180307407401d581c3d170501d45d2100020082d50b0007a1108825915110002031030700ba1201d200800c584642e907a142000340e44811410301640c4540120b0f4410380c1e00a9856440d80d1900078a0103880c4c0c01188002f0302031038422441143c59500b4100001c20001101807107003080c4d001c039001e403410310102518010a003001c00c802008030450785004a01390424010381d080d50300c10b400d8003070100b43c2c584c4110015981d50004440040560308000c0118035039903c14426250010a1030680715460300300c0c000b03448040843e071908019416a2860300d55a0350381d1b0740440c0456161400c0e81002440e09504031132070001c00032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 9666131 1250 9664881 9664883
    0xf0e0d060b040509060405060f04030207050402040305100e0d02031e0909040506160206100b0a140406030b010e040203010308070305070c050a060302091e0a1701020c0313030b01150c02060a050702030a 88
    0x700c0c841e1101000d11041d184080d10320203041c2d01c0701040102146000ca01c0b19000100b49140e2001078a450600f01d00c0c06695401c2190703c948001000010000c0010721044100328a050030f002c03141803000400d4840c860380c1e0012003d60030030400060200700200c842281c04100d8121981400d03c031201207004a001204c04030f425070b000d0703010301881c0c45001c40d1880086000e40300900103807500000103214071050748240c1e800f001e0086030f0805c615000c0c0f02580880401d8251250b1038554410000b0003400d009469240480c91035007200440d82401c3c000c680c16030703401c03c03500703482d1401c107584c2110903034801036081c2c6d4003544d5000e020030107696007031001008105981c0c000d1385640c86401000000450841c0c4049860351246c10340351a515082d40c00001c6034104444091200e040501440c060b2082d8101da00c058000042c070a039480125005140a490040c030b070845041c0c0e2184001a070300605100500085034483d0129801490800f005060480b07040c64035908000301076000ca8603003841040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 9667381 1250 9666131 9666143
    0x1060e03010603060e07180504080702010f0309060504030e0a0e010e010b1b0106180609050712020d020909010b070c06090e1311060304060915060303050f0903010e0d020303040501050c0901050a0f0e0d 88
    0x280810040c0c144d40442c41f24400e81850400c0b16050666501d40ea622614000905100c02c034603402c2c0c07804d40254046158242c0001050000d443c06190040c071940d0a61801403240886030404642c61441c041c045050710f4001ca0442111f900304043d002d05604a501250420710045200800c3c04e1f0080c0100c10080203080c81c0100c00030f40c81240c2c0d030241c5256801405803d0b14160070050000d0748500895050b1009000043e910b2403a102ca070000b81c820218800d820002070400000d186884000414a003800758046a0364951580e008444004080c0328001d40c049043e80404c0300e0007480c0140c030344100c3c0304094240f004040200805c0326170304204e60648115548601110038407141c54145283c80d48890020400103045940c050100e000d522841c051140011401075050744096000c0c042012195084540d881c014541c001c0d540d80c811036040b41e06508000101e607401d40c0340415501c1e42c10050f1180703400c207140c0070400c4401c1c055405c5003d041004103503004d001c070b840c0e0700400006140205 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 9668631 1250 9667381 9667393
    0xd0204140411030601081504090b010e0705030103050616020703061404060c030c0c03030f0b04060e0403020f0a030503010308030901060b0d02070c0f05010503130302010b030d05071a010e01060e03010603060e 91
    0x12a003a050848455401c0c000c03802e01d155203400110350411a03030302c00c1003420420f885807619043c0c41300d0300b0829000c0c1ca403c186014164800c0c012039813a174070b040368903460b8103071501d50740d440d0b003116140802e100007045988440c01080c408600e0b4a20129075080e148125100c50380d882e20791070182c1e81c0d82e0007072044200000085c40280f2a0500071081107246a040c18030900084a00042c4582402a409010160f403000c880c0c00320391080c0c02141101134000e005000361500d481503104152015a0120054442c0d071982c40100e00b8045800031201c3e40544070b5506507842c42d1510318944d8402026a4001c0d582e502c0042501442c00d030181402091043c40141c894105140c0b400407003410f50048080c10910032010000c0d82e90040407a0350017108580084280e03901450300b0f9000d0002c000640d50300d40100d0f41c1e8404081d0b480806002c01c41d00481401000c1d64540009810700102801120820ba85907c010f1140900604000d99502d4002d000025810740d00d864080c02c40740600b04500481d0400c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 9669881 1250 9668631 9668639
    0x10e01060e040e0613030e0d030f080f04020604030803060609151b01050603030301061103040b04060e130207020108070e010c0506040b010306050603060106090509040606050904140601120203060a0b0f060d0204 92
    0x110124150780442034500b0003406411181440da200e000a24544030301d0b60002c080020948117185880c801031014109188040261a014001023040c14004000070542400986009681c0f80f03030901650300074205501d01415922084820340c0001d120940082041004405584400059458012102c000300e83c6034243d20606035082002442c8089180c1e05040034841c050b07402000700d0b811a03040d82800460071440b17280f00390841c011581b00c10724200d0085030004140b60480c0441244000446550390841c2d942000a402c0b40240707080a030024518000054085000342840c1110200504000500c006155182031400d00704a90448108009070b00400800c40700740503031504101c0440c003415942d810b10070001c00c482e00b6445028401c0e13202c0e1300443d003401070326400301c0060030b03001d0000c1e400b51504d41002002c0450080c0310030304a1203510000604d15408010032848180e009015113015210a10b0150150503858101c5500861841c941c000c0d5a43e584000c6c03144080c41c120140e200d52074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 9671131 1250 9669881 9669887
    0x1b070b01051009030506060607060e0319020106060c030e0904060b04060b07050c121504240213080c01090504091406040b010602060603150403050a0c140a021513030816060203010e0106 81
    0x10410041e07081c0010f00c80140001180030840756800b020550303c3d940c8426013818440081c11480b040e4010f240000514031a9041e60740003411b2031003099400a200359030b0b980ca000c4a9002441d4400380c00030341c1c9000200d4252421643c44c076000b80c00b403040402c41003c9400000c084a643d580222080840018420b040003000e010300501d6120889030040d506030f040301042e0300e609408254584040504000904000c1e5810b40b0600103120304001c045c01c3e80ca1070011500942c80038103001c160074200c800004501e18005041307002e050042c1c1d5200d0644d0300c1d0005000190583c660f048600d6000300700c0130a0401020000c091040b4050708046020394901003001e424201c01500f410f000350449030044200018005a040e00680c2c5441e01554958210700d0884070140802d40c0142219500c1400740b1038000002010702426000329035801040d10181003500c101d10401d1500070300342201000401c04120a40050030005001500f109510b9000d0394a1030708036442604078001c4052104010b220040d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 9672381 1250 9671131 9671149
    0x50901080303010e010302010c03051611040e0706050a030b01050c010c031409010e120306010215040305030a0b0102061605070804090e01050403030b0102030c0c10090e0a02250f030302031b070b0105 87
    0x80c5040650300d5541484155000d481d01400040d0510000c0d801500c1018414000c4840030140301540b0402b558031450284240b20410300c0942c07040d410070802c40300d441c10210710201201d41076101d045c9040010841600030f880380e400540d051080600807440d10f002c082c010b051500c0c1d91a9000558000c1c21000d112020303601803c0304420f0ba242c9500e050322120300080310142008010319076a140d03502c41004034a0001400c00b5140025942403d00042540050256004940740c2406202c01c079840c800490b03072510304039891250ba424640411711040c1c0900e0062041ca801500e10610b40364407002090103131540441b00b114940c1d5500101710516601d88202000070b00c0910181d45010380003950160394048406d251403092202c40021201a401141d40c4401400d00750804504d514014403403030300a4014503030100c105050100c040c500540615070781042a03600854000c0800e8071070b00c0840003504001d001c420701d489005c05804148190501911850f849100305a18640c105014000245 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 9673631 1250 9672381 9672389
    0x601080109020a0b0a0507020d060603060c0201151505040504050423030901080606030c1801110f030403140f100c180801050910050903040b0c0a0b10061e170702010b0a0609050901 79
    0x4c03c24051000c240341d101040340e244940407034283c0c5400341300d03090200c02010385030b200810803460b0002c030315000b5030190043c4a810507d280c4582105a8620440c010340506035003030000904100400c0c062458181d0000760818000ca95a84000c01e414580f0a290181440041c07a03a40c0086000d02e450b40e440403e6642c41030058a0759130550070692150385071409140c5410b6006d020480b103022a9903c5640307200e0190ba084c10031a03600038a9000000d840790b006000a81d480084803101071000040055029000e00862009100e03403060740810100500c4401c81070801c00824425032046040524a50710192441400009480c01c01c0302c402d5145c0080e107050100342904080801c89400c801206490854084401c01a0758000260216081440405008068861540a126405c04009a1041034172041c0c0c580701140d2810001d4251060b54040382c0c6400070702c20b980500748124100c031259421001d50300001c503108010b80000703140c150103508072000240c0d94600400c824601000014018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 9674881 1250 9673631 9673649
    0x10617070e150901060507060e0d030f050a0603020306040308100b0304030807021606051b010605130203040209070509060306100c0204110901180b0405010f090e01030f02040c03020903060f0703020c0601080109020a 94
    0x1403001d00c04900310f804148244800d1000c0030034904203026064000040c8a50800143d5103110409980600141140c0300301c0c0c0c940c14500000103c2d4844103106100503290010014102030360750341c2c2c0855807580000c0c090b001c600c025002c0020112038400c051070080e0310a4480704120324203018002e00d05443c9000200212154000070448590410110381014018000021a940032000301e00e016264030fa110320b80110103048003170703101641c1e0f0b40a907004034400c6483d080580c442c0030382250f45008a6007800d600c4001000070400700d01d401142c44041a89070304090f400000d040e0005800c440300286101c0050200141400c042d40c0d0101d0158500d142d03030700604090078204619480c0501850142074148040e0040103c079460140000c04000c1241c41c01008466850b07161000590566140882c001d0b810f081301d07141450300030b0081e20745500001d4001d04803641e0390070400103404005480c110505a0801c500d10901e04d083c00001c1c082d2200000202d1801c0d01e80c414031940c205164041c61413 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 9676131 1250 9674881 9674911
    0x40506091504021e030109090209071d09040201170403080106031b0503150a030c030804060201060f0e0f042901140607080a23120709050a050a03080c010617070e 71
    0x115910307441c4080314020607a001070f00e8050212003094107400740c0000440e0480044000078028840750801c409282c82a170341e8900d1506d4440c0160340a100e01d0316401d0001056003101c18543c04c00ca551150300500504d000c0444145c1c0f010002e001031002d07903054000899010050040c0340d014010300024804404207610391122884000b442c0d4040601400d0407040066002801d540e00c00b00c0e800e014642105a102020340d480c5020b80340da503c280306180143d4241580010200424040c003012101e000050b240580c0d9226000012a01d0040084030039001c09050242540d0100d202c0301142c0c1c080799080d01080d41030841741c064180c0b58100040c402c1004221400000c3d0003402511003000c5c0a003401c00031a4440303500032515514103e51070800700c3c0040360326007696100d4000b16010314400e032105500182c42e4028890b16241601616420000c3c585e82000018205802407000710988400010081c0d12200720000c2c02501071003502c4694400d401c06c0c02a01e0700c950810f50848081c50481381 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 9677381 1250 9676131 9676141
    0x60c120e03030d050a0603020303030c040e0603010203221502030c0a0e060901020304060c0302071503050109050711060606090a03020303030c0a1d031e03070c06031d03120f090307050706080604050609 88
    0x703540d11403600300500540c2c5131004540405482d4101d003000d5640142966101c1c54a002240510340140c400d04d0100c0c0050400b02d40310f810103200f1a800303442000d08902052600c03890600302400d100301c088808a010308210180742000c2d202031401168146406641c0d00035018000f441a030241c402c4501c101c100b007120b00752607030700001107a04444084c01c1c8298007039242d0500780e00f090580d91055503081700c1d010071608142c0d810390001e4162462810104019282e000f021184041300602c0c2d8205c130b81c00140801c4162500700701030845030f100208440080c2d0748a0340860b0030350304107644803880c58002107880c0c4440303a0841c04801d164103040e03c0c08030240da082c0000955031142c5148500c15000e40342c80d188205e6106100306c41481d0740042010011503030b01c0d540140100300b0451824000e94100c143d45035031020101c1266441c1090050028164407040f80a80a10381c014020144900c402c01042002800038088030300103110544440303203140307800414041500c0e0010481441044603c007041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 9678631 1250 9677381 9677383
    0x180504020f0403060b061c02030103021e10030b060c0106030c0e01050603040c03030302031305011a03060705040303020304170c030f0109061505031504020a081509010f110a051305040501060c120e03 87
    0xd0b04894003c1c00100d9084000e00200d18940b041e19103500e9442e5a6010841e02610290000c41c101c0e8802d450488500c0c81c040520700841c140d030203502c0c0c0e00c08062040644800d1082d00029882c00b4003e00ba80d00d40ba451045071800c4070510360085503c2d2036a0b40082001000740250b143c014101560002c1ca5807905699000003c0030a000040a065001c80440c0c0c1c048940005001b01c81c1d4407000070040c080e55a107210308400c11042071035200b0720401002608803481001a80c0031680d00da0011170400b410151200700c0384036421881c0c1c100b0303c07401c05c0104190b507041040e0500568407200004140d002418884140da02c24446200d010301d00385402c03c01901c002441c844918031040e06540b650b295440052141039241d44541020721070b0b4680c0c00740415074000e0389802817402c64020010040301603950016600c2d040c1c0c655070450400d1201154030b9028000a0810f01c105070141c0340400c0e21440003500f00c1e00b00f03810000000d0340300c45482040001c0c2c0154409031b07c419080c80281c10a8402c002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 9679881 1250 9678631 9678637
    0x7020a020a06030504030e04020301030b0901240303031109060a0816020c0a030305030a0b0303030703020408011406010e011107030501060b03060414040503040b0c0c0301060617130302060406110d05010303180504020f 95
    0x28804169507130000505042c8290004284040300903c15580c03541d59050414200b0815601000e05520f0000c0640d840c0b601490203611206c000e4a100b0f420900d191402d0f0300403c40c011000e100ca8200700242e800300d80d02c3c14020300c4c03047c0369901c1e00b00c01401c0451000204091284600043d503100b00c0c00701145a80d03a54046080b01e90600e002c80cdc0c0c030342d83c0c00d000002a120580d060354241c440407080c444820381503000f41c01501c102000800c1260b0041b24401034141d803d0718a18003154070105605002d51040d0311100d41c0101e80d500f200c441d07540e2079490340e085a400364040790050002009005d070518090241e60f9a4294116000c0d03600d0910f41c0f920741e240d2240744581c200020300000c070420004018044e030200210000c0080041c160745040141c041c4072410840200ca8021000080440d800e10a00d091101d0301a40140616075907a41c4203001850107034441c507601d42c800e0003244410041409201c0c081d62080d9034102103c0c0c401c044480d0a26225000144030b280188000c1c01c040c0c04840c26 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 9681131 1250 9679881 9679889
    0x7050102100e01020d150501030b0108010308090d05190f0309090e1b0d0206030910060f06020303060405040201030212090a0c06031802100509090a020c12030105100f110a0b0f07020a020a 82
    0x6000d441d00c82c110380244281c2003c011854100b0600300c3c0c1269101d03001c80225502030700c0910850742000d0044900c02000d00008210071424440501c1c18109401c1d08506c5a00c101704444510010109400c80c005c2c50342000ca464580c0242117000709588586071200401c1004014081700e400090102d48814407244029150f0b0f20340a0070300201d86c0c07420740344420b5980250890b5685e0a00740085a143d41e0281c0c02d0b407030300d075082c02000506c0b080c10003c580210750780c581c007070b505507158501008043e01001c1e1050f0704054080c06082c45140c81d00510034061050700005041ca1255407400d03904802090784070400349450811071854582d0417001d0b5040b52075040b42c141101d48400710701680c582c010103080d80d802c10a100c0422a034807a1a600401301201c002e0220b0f000345101c294900c0d80380c80240038441d0010f03084140140703103900512404091844130700b0000005140900c0182c0741c00140070054800c0808641448150a800d8a4954000344144040c1400d40700ca40c000c600d0140403882 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 9682381 1250 9681131 9681163
    0x140106091a01120b0f060c031b0a02010203070305030a0204030b0a020901081006090303050d0204080304081b0a0302010e0402090f100e0a08010b01080105060711091303080604140105040b04020c010207030c03020f07050102 97
    0x2101c0d44d050359503240e500d188907000a09068036180c09100301e0b41d0382d8010000031002c0e0110045020f448102c00540310002c82c0d170581c000d5207010740759035044138150030181110701d50399001d101c0840061002c295880c86001ca4038030058840000d4000140841c5000c0d20302040d40c41141002d20201e90720140510070740380c260130502ea45000700a03c4400034440c0f0340c02030000340004100840c100c0004070b00e10b143d40003000a000e0381a0401810000700c1402440000c0c0440c00c840400310050915401811100d00c0c0144500c0045030701e41c02144800d400000002c001a4160f0b9001c9818078105241002500451000700701f4612048006030101d0018040c040c82101c1c0420000c0c01c11401165031650101302605410321401c00c1c0c24108a40d40081e1400c60114080b1000210079060a20407560020546031844013303920b00030900c4010b0403698402c1c0d0708a82c00300180700d8480800d000a0005610966030b1080c0030086040013420000c0801c1c105003aa00106402c1002d03030390001d51180c20624181e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 9683631 1250 9682381 9682391
    0x90e070507030e0a030f2901050928020a03110408070e06030304090c05070c0b090307031202010905011509060f030f030318020d030c05010e070b040308070f140106091a0112 76
    0x2090543e00c0310341ca6044580e025440c000c2c04020010646040d03d0301c1882034000e4104d40101549102e05002144600820312481c0130040000b4580808100c0d041240c4c860034803140c112071640c0d4202d40c0e40c2000c0302a0203540009000300c05640c984903004c491100381e01280d0510341010a2191507440b80c0c400c840206e07440300003241181e0303000d0045900a00d000781c010803006405040140c0550000e1074260381a0201c40300c001408090032007165002034005010f0042c05041d56210405054101000000c540d80c2c0c400a400041c2c0c244244c9800011035120701400900d4000e4040c25914190860050603400d4281040015400f00340d0320007035507140c00d0101d20349840809076900d803864018043d610041403030100c0289908019030b1540140144000e000090080c0c0b00d4a9503013244c4c1c428000103000070402000817602140181030240e1241e8030012042d8201c0e00c0304c4120312400341d281441fa941d24601040000c490f440360b050121540502440352480780000a0301104d50381013000360440d103038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 9684881 1250 9683631 9683633
    0x804080a03020c070602070501020c0a050906010c0c09060b030103050d0f050315040207080403110103050105040c020a1b171606021204140d0203010e0703020414010e16090302030d1d01090e070507 86
    0x650107480341545501c00f100e041310f5541c3c1c002591550584141c60150240c08101a528180000c000064400c064041001500c0b13440046803c541c0d10303071044c2d54005840001045003003c9005500050240c85440d5840b9415810083d0618840c010140148034a004e044104135400005980d40018141100c0f80b0550704030002c24080e00c0b42c3d01c4028584440040c0200420034002d031250380c540c1c1c00fa40c0401260b0380b01c8050000329454190100d000d03a1100e106080050010015080c213030301d03851000004503607110818503503964822609600b507041101d0f050758071552224404001c0050f07200900c6029000c981004a038070850040c5840b4142c0b00212b41c15035100c001c2d6880721242c0c041d0017040300c11100c0644603181c0c04035000803485035083c01c1055502242c030400c084e060714064001082e8580780c095010700458070300c240320814418601c80c0040942e606100701144081e143d20703045807204040ca54100340c00d1500624505000b03111001f4031081000da0b4080350f221105051159a8481ca = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 9686131 1250 9684881 9684887
    0x6040b010e04140a06020703081303020304050f0301150e07020607020d0806010f020a050706030506190302090a020c0f03070605010317130b0c0c0402040906080111030f040320030c0d110304060804080a 88
    0x40c1c90f210030326910444d000403040004030390041203038034002d5503000126180c0b01c440d941c410b00c0360100540143d00c2032000740300625001090280f0030100400010301c00306800050803001c40f42c0d40c41303c140801154100080d41d901800350726030003149031000e80064424a100034246040140110f810000880301c4510294000c202007208113410000304d1344550340c0c4440c0107020b0700044400301c0c091845201e41c00c1192184005803426264001e2040350203580c0c41841e84000d421010182000d4030501710410002c64040c001042c0300780c02440081180c0d03056080c01c0c6a0002c00c07603124034807e0030401c4400701c0021301c02981003d80311411741d21aa80c011404289251500b881103041e0310a00c0000c1c009000d0481da4170200480b50000d000b40101807117009005c905000c101c4024091603461800039000030701c01e410340c802d0180308151101c012000645401c2c5160030580c1c0754041507000b00044100c00342c010944180540090006611307183c10424000c026031000340004020400221700d078004540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 9687381 1250 9686131 9686153
    0x31a030604050706020f160315060b0313030207090c08040b0c16030e0901060c050a02090c0d0f150501080601090e070203041a090a0b0903150c0706020a051215060301030f02010e0415030c050306040b010e04 90
    0x10b01cbc0304200b9282c0c01c0c140b0b501d0942000e245c2003140584208003001500401c00e00030415100c4e0399880e401d40d41c0d521526030701c805401c010502c1c8444682040082c050800d59041c09140320b01907a00e820810780c545060104442041c2c106100344400310400c0c2000500015020324850380c103862b01865501d42d840da5040600850440307085443c101050740c11001c0c4654010b10b42d1044104203800c1c40c44e5a5001940d10b80c0003035035200d0018580c24024000300f01c3d4591801c0e04840307284100ca1400ba615591141c0844605600c1000c40c1e90028900995142c440385442c05000e07120502c0c3d1511440c54006a91803804d10240103400d095000001c1c1140950700980722040c0d04000f044d50307210302c08000102107901c4407a0061911190801142c803a680f192104281440c010380000e00c2d41e421901c488240c2c0703024142c200d0402071030140200441d1258056102c24200c0a498100701c1811890007400b59020303078103c01c2c02a88600c04000121752944084c1d41194488056801701c4d86440c01c180318030135 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 9688631 1250 9687381 9687389
    0x3010e06060c070f06050901031407080c071502030103030305010504150b090d0516030302070e010608010302010f05030a15150e03010b060d090507080102120f010503031207031a030604050706020f16031506 90
    0x11309903240091070640003802000b01907001d036000c1100b040c5240481070600c80a403155000505005d000a11482e0b0020090819074019a21800c4070020b864183c02070b68400d0300220000303034413540100100e0070240030300d84050448201241c020f81c14a8446c0010b03009520710a03100740462200b030340601409111600d030710261291030a20154581c02c0c040d503614898460744403500d0200c40001082d80c850b512070340c141c96050b56508012410341100301c0d040c1e080070700b204600a40d2a01c00c2c0020f400060080c0d00140b1001c60710304407030302e1f40b460b0182000da4808607079402a410507a80c080d035603079001c00302e07040d05049210000381d03110700d400c08910702695a0440e04a43d0300c000703582e1420001c1400498428000c038000030480d80e8a607010b1548a0003400e69900044031084041034496020703030819a00701d880801c1c07030b02d00700480100081c5801c0f0103480949103600b02c40000c4c004035506002c01c4000004040040075404da503800f80302c02002d46880301403e0509000c0980f000c1030603d0300040000c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 9689881 1250 9688631 9688649
    0xf1202010f0e133e12070509040f09050f01150504051302090702030909060105040501050a110f070603090c060e060304030804080906070614010501030509030406050f041509090e0303010e06060c07 86
    0x603603c601e800e100103101d64001da048094456050134440c0f03c0c0303d90b6841c000c1c066541400c1240411035895400c00182c07085007804420f004ca0b802e980c89521420070041c00303124011842c1c02c25400c0450034010810700612291b4140010342d8041080121210121343c400e80380060305d0b45e55180320210200e10104000d5110004c40300b80f004503540000503014141c01205e0030090b07912400c0c0103484078441e0344235a41c01705505200390448140070f4074211144d07000c0001507c0803014090161810200d4a41003000071a60346c1c60303047c0621405500c0800640741604051007040b40c1d13440091141d02009000804015820f00050304115811080c2d51030000054030440c3c513079500d8545803002d400041d1103404c05035000302c00024190702c00e0007450f000e0100e58001c0c0d4505402d2403811500c40c3c5c02281c000c125141d04000005086644441003080e0007900d40d035002c031040c1044000d1781540c10741c01a50080780d10a10060201083d001c6e015500458211800d5070750300b10000354541044aa98461010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 9691131 1250 9689881 9689891
    0x5070f0512030c0309010f1e2f2106010c08070c030b04060e010f0902060d090305040302060703030605090901060612090201030e0706030c0201110324120303070302040f1202010f0e13 80
    0xa44218011318051241031009109100780c1d2801c4500b1076081d0754808003038903007a0311441c1003007207560300a080c08800c0781d0251012030b040e1950421215003034080c226080d107002a12401441004465007018000f044a8075024108100001e181d901c48080140c020800040c104c420007070405003071301c000c41d07201590360150702c1d01741040d4000b003000301038151443d42058640e6499a05134481c014002d540241140d08103030304849450002e04450104605202c1d0402010001d80d0b0303042d002c1c120041c440c3d40c0c007182050501d0148241c4c01e9000e00200322980c1040b005121142d0419204e615000301a9400074842d0444d000480c0984040c0e40108001e0007624070108106515400460030b04032541c000340544004560b014581d40700c02c46a00c0362105051849003810f071803004170400c04103402800c0c01d102c0023401c80d0490035588241c402001107540098100200e070301c0e4620440c020140b1480001290039190000b0f0b010990f11201001007013149801070040d5554422408090700c8000c0302080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 9692381 1250 9691131 9691141
    0x30d05010305150906100e0603010f05040b06040c09060207030602030601030209060c0a03030b010e090f0a0209100c050d0903110f0a0807080a020f09060a03030507051507051207050a05070f051203 86
    0x40c0703880312540382d500c158003d0000101c0e10500080c8082c02144000400b0061504c4e0a01811081201508259141d5210030307000024149078083e050181d4040d40c44c180007410520108401c680c0041000d006100401c03408109090700401d5081c01c9941105025950f0b5a408004800070b200d05504a60700c1b40001c58444681d400020f030311480c2510075107082003005451070056502c071117030f409141d5101112100091840b030704c2c0780071250480c3c582c0d0000340c244600c400c0020000d50b000d4407090300140b040d850340810300000300031000c90340502d4104030000600f540ca80e200d5602ca1098160b004d00c50300c070900c99640e103031840c81e0802004200169038100d40c56548003911210a810305038401e02c94012100800d1030080f03210b0b801100020001240d29196980550302500a0f010a982e40e0168902e90341458088030340710340c4921002d55510350b072601e41d010100a151070107001d1904110040c4144d402080d040000c80306c69942101540700c170020540307400d174035116200130700c03034180c89001c82401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 9693631 1250 9692381 9692383
    0x71a010b03041403130902070f0206160302070605070f03030504020d0204110406021c0906140708030c0403061505030c130e030406020307050f010b09130204090605090c0a0608010503030a0f02030d05010305 90
    0x507001c1e600c50f0000d500c00030807560085959014010801c2420600c1c03403c01c000d000c410303600400d44c0a03c64078135007809070701a0b00007503010780200c0c80105454013100311641c2059818001c11020b00924140142003040c60f032204600c45460020080c02d159480c0007003003d5641c3c5604010300c82d50b0040050040001c0c11764000280c0d001446010058400d60090070000540c1114441515000c0d0307440000031403400c4400c8400a100399070214180f442000b011010402e010000d5100340300181402c0d0380c4d1491031610000b21883c0d4015506074494210040c00141d901140d4030031741003003c8898440c000d0108071980000c16111550003400d1100040004c2d4854010010b0b080da81e0052054a07000c1202a41d12070903100c0e8078481503848604100060080480c04200d1010a070000d0700c002940f030625681c0c80c0c210703803003074440a6907079000914990f4036180900190010b04138902e8426119494000441d5403402078522100034490204240d402c0c4c10710800c141c5103402c51840042c45296074900b041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 9694881 1250 9693631 9693637
    0x304060207050f011b0e0319110a03080a030603030e01050309070603051806010f050f0628030b12010902040e01230a1b050d0507080106050a110304090906050105041d0d05071a010b 79
    0x10401084900c1641e08280c40c001c2341d259104001c11041d8500c0c981603a580c01344050140c00c1c500da0010303944401102203007006029000040e41901c00281440c2075080c0580148081741001c0d040140c108100101c10b6000b140303000441e80a401c010500c0e48a0b1040080e600d0712144013800e152041c280001688500550400304540341610040a54403459003808924410b1203d583c07a03a149000505240c00010a0302c0e0000181c1c41c900000e40251940018440342e641c2e58460744a03a4540c5105403e618003841450800c8031000000c01850350304070701581c0105082c0e0306080400d00c807240042c02090064020504458850030b2444492001c101c02814a4011100c030200b15031410000a01550081162a058880c251906410018080740441e0300700910520f164041c00b0501001071100000e000d0b00300068803418010501d076040000f070001700d804c0503242e001417409809460440c107501040f000b00c1da446526080b5582ca035142044000908031101105e00c9190300c03800040c21011031000303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 9696131 1250 9694881 9694931
    0x51824091503070203040e0705070b090f010f290a0f0303050309010507091208070f0507060f030e010501060801050111010b060304030e0f010903051207060608070f050109090507050304060207050f01 87
    0x3101d00000d9005003200a5000031501c440c00f503881004203200030b20020214030f612060924185241030495507880080b0141500c10750442d85c4510860040184207018844000348007071001c12810b00b13085244940480820150280f2255a4043e41c410b0340311410450301500c40250190912a640d140c01490360340b00b1102815036500e410302050f800c40c0b040903443c0440e882d05054441e01d04040d116a44158440c2204403940061b000c80100000c8044c480308000b0004c0d51154641c0c2d103d100000380a40314241c00c000d000341d26102c0180300050704403a0450550303600303203407400101106640d00c50042131150140f82e80400084100002c140d80b14400030301e0520155000c0344211034400040d16025014003004195801c01240c00e056149100b01500340701d07016420100302d41e0f90720385015042c9030540d00506440d100c003280601555070400c1c4290020500788a0802c441c0c40d000100030711070300018000600c06500000c9d02024020700300b1040f00ca580308100204815003050203400181c080d4041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 9697381 1250 9696131 9696139
    0x906040608061c05070504020c030702030706110c0d1505130804080a02150c06060603090304030209090604050f0708060105060906090402030f0103020f0d0503030f0603011409030301180501030305182409 89
    0x5014820f00e0b507550480912568040003c089681c106400c00c00603401100d03c1c0350040c030003400450003580d41007101c4030003041035072128040307030b803201c0405170034241e0329003400380101c1281a88000250079441001081110085c00141c180c451107250281d0407003c05010780561008103010684800100341d01002d144200e0707081030210001c100209a5001e90400c0b0a003030f420a00c00100b19007401001103501124800559150075206d0f4001043c000040d201d003c0658030040070003040002c100040d600a030710043c010701c10349117406465640c44205000b45030064001003104002c680320203081e20001c0c8070041055440b8075200017011034850302440706910440201c210b0740341078201a004200790940000c051031031a03884c1011203801d444080d2015030159a03aa0542c0c00c1c5600d0031404a0059010394060740d5607502d80340b0000043c0007000161b450013031400c07004200080d000000c44048044000ca0542e0308601040091004001134003001a01c405040110399500da44e10000c0c001440115 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 9698631 1250 9697381 9697399
    0xb07050c1b0a060327030504090612140a0b04030c03030f140601020714030309040203150307080f010f0606050a0f0e120706081f05090a2c0c030c130f02090604060806 73
    0x41d0860945d140d611810100c02e5101d20052804414408040f541c0b60007400c0c414905a643c0305000300b00c0b94a40c1c8440c90f441c40a229000402201520340b0200b98040c00013000135102588078604030303040140000381840149038201013010301030340042965100e004820417000003180c03201c2410b0001101e0007130060044c030394045400200390325485403082d00a0700643c146244102480003d42c8050154110a60055048500c0c2d550070030241002d0008030028006825194800b81c1c20354110f0058400014249181404003650110640c5c2d00943d480c60042c0c685108080c091750400c4610001540121001c1030110700e44200007003a0b003c9442c907a4512a040c0c1c0e407104201d106080c0b042d40b1100d83c05540608000a162441300142c001090240001e0b915031a45000800382e0400390001d4a03040400b040c1000720f150a10107412011400e90141040c3c1690a0000300c1c05031426101050381342d0790308509500c5524503410703200c001c0c0c00503102075aa00c0d2a81c01c050300040c800c030f54041c86400f200c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 9699881 1250 9698631 9698639
    0x1020c011106070507020d02030708010207170702010203030406090f06090b01180501080c10090905041113090b0402040f06080a0c08010c0c0302030d0c27060305060f0306040b07050c1b0a 82
    0x148607561031450300607024265a0310344400c2180c2507400381c502a6400f80c1d4008004002d81d070140700010080091000041e45c940183c9061800d00b07241c5009a040c0b0301e0103010550150340c02200320b9a01035400040043d6455032440c258042520402025000618006440301003240b9107519506881c4001068210080e102504406a50090050701400c1d013090030000c0b034270f040111a9244c0304c4018180711052580310310300d1108503507088a06a80348000b07080c4113049070400813070740042d0301804941407000401584561450b82406000240603554440140804058560180c00a44002401da500710602801c00d441880058040d043d030551801c01555500e178028401c0800743c0381d243e0007440c00e0a06100420000f441100920814090015503801d400c1c40c1740d1100d03583c5030855510480c401c2e810101c0040031580020145401025600010400741d90001030280c1d00a0380312600000a5031072440458440c0500070300b44400e8030544034141d00d41900340800f5902e603103055811400d01c40d51 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 9701131 1250 9699881 9699887
    0xb01080c0a02071217030f070e0607030c02150c0d0302221a0307030209040204060201020c010b0405070c060203040206120c0a0f091511160803040e060a03050c060c0f07030606030201020c01 83
    0x40e401d5140242e03104100402400108241100445015003009110840401c03504401da502c100c5006800e10410b90801009980001d40080711080a0316400d01704012941d020f0241c0352001070103840307a0a010b01072584401e003941241e504c03540c800152888411000d0015020750011603c00185100e00e80403941c04014000b902c5c0112003603c101c155000b003110400070015840078140c03004250f003c00051006072901d00050005050769400103a03241c0c0300300300d240e00315420100340306d104038100014800c03445e0b4080841c2801c2a04802c0050f680d80307461001508a01c03071488034081031002102000503800f64913010b8500c0c82526151001c10041c0103400b110b51003c04c5c061030f00720114091700081401d05c01c40c0a00011001c180c100e8000000c00f0000f020502c8207544081d2160340005001d1014865001006400c4242910b50300d18560450303555584884121440034018100400d0f400002c5004000003481c4102c0b200a54400c151a0f0070a03d001e030003580010f038058444d00407c1403040d44 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 9702381 1250 9701131 9701137
    0x3050901020a0816020102040e0c040510020105070801150c151508060103030c0312091401020301080d0302040803090103050705070b040f0b070206131101020f06090f1207150216060903030b01080c 86
    0x40b0365104101e583d91103103d00300403090f41401004640d03081c03101007081c42d04201d42034041d1f1004000d0369199494a020000c2c940c086101d00011a4109414007001d250819009419144000990000b040d070b50360080303841c1c41495074050148110f4644d02038100c22558000e168508a00d140750b80720a03142c510407980c0301020310000f80010611058100440d100b030710500d9540c0d4900d103021071404260f4482c0000d4001440c101c424070b9500100411618108125600b4015414102036060616040c2900d40300d004207582c440c1415100c2c2d0001c2c2400d4410750403280c0d142e0b0320900300340c1c1c2e609290400c5e10084030007480c12248101c010020800c21030002030750500c02c0c8100d11825400d40d8241d60385103039000344101d40c103055104841da82c1100074414004140716520f0764005000103030160600d0791809440042c1c50940500402807000815580301c68101c01c002c44140150f6100503150038100e1010a030340b009020246440310355401c06a0581001da64004260703610800c90320342c0090401584 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 9703631 1250 9702381 9702397
    0xb030a0804050609060d0504030806030c010f12020a021c0203070501050c03041e0501020c01021803070e040f08030907050a08030d0605090118090f080a180902030f07180b13060305090102 82
    0xc014481080341c0e2030400018100d0b100040d0000d0300307285084d0794020689209503022400300d500390b01049040d080412842441c4d88c024644034400c203840e081c01a12080d0307001203122500da000a19016070303d008001c0c1060706e106c400455180070000c0d400094403600003000403500d42d401c0a01045206110b88140c0b80250f4001884011004038444805031a408449048903595000e1190906500d001c0c40036280b4101c00742c0780108128080c400f01820451035422500c8160540d509200205046070103e010040e0300c0001d86690303480c0c00340454506070301903100355404085554045030048000c4040d0883c449007407010310201d9100c00800c16002024010803502070444022803c03a141280c0000c1035850050050288540c600d80766102c80380c2c4070484100200340e102100e001c0c1e01074503030b40f1000284072409046046040c240050031042502911400820181901c403041c8102482d01038801401c5021000340d841e40f02c244004106a907034464403011074600400108401c0060088503004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 9704881 1250 9703631 9703643
    0x6080606060a030e010603020604090608060a06120311010b030d03090b07080103021309080702040203041109011208030412110a1103160b040302040c20010603060507020c220908040e0108010b030a 86
    0x2900c2503000703c0040c900918010070340e6489580020160b210300c0020006000808004100030742010310702031a08002a10001140c3c0c0303429003c00c480300e5680d82039400b07641e140c6485068041c1a81c1c800e8090000440792950600640864119141c3c00d0740c095040103125020007030a40d900c1d11016103400c08244000380d040348110f110074a01400d00d038403c0000c28803a0200a003454100d4020030f089810444003295050b0808003959054900380060b680181084040d0b800110520759402d5607500002c2c00080140c109a2180c1039a203000c0c10300b08008120030000c0301c0e024180e500300740302c65003045011580a401a080c4400c001942500d8a40c15101c528110700d2400d0324650a100090000d142c008003000b03894901601c0d12003000700321408113800e45001242186c2141005012508098541410755020520b4603450340c5600104940800d038001d8601840d0050018001c0500300125004002c0039000401140040c0c1c504080c50585402e03a00030858080d401c410f2640c0d0b0081501c010b092 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 9706131 1250 9704881 9704887
    0x3050601080106050d020c010207150501080607120203070e030318040b0105070503041802190302031e040f020919020a090311010503011d060303040f080d11060c0403140307050616030608060606 85
    0x261a00a50003085c3c1d41620782d070014030f04a0b040d0541402ca07040342d00104c1702041e00032110b403039000c2d40e80125405400e0b680080c241d507041c40351001d032035498202d4030f4500840c2c011001802e032900643d80340b44038800240949035225041c100e140044241216290300c00c1d031810035608015441542540c039060307032043c019443c00e41880840a0701714203016551807450380801c40451000900b029624a5488688000d6201d08043d10849003103051200c020916420703210400000c0340c41a403140c0015501501c84400c9900c900d5107080c162012160700500c0c560000a15103146640001104200c071b00de41e0000c1c03900d01000004444a110030301c182c40850145108210182501d12540c5401220060489151035924405003c1445190740724a180350449407888480d1904900b0203140d00300540d01619441c941201c3c0d4078028000d0340805400d420100c40d51448600307003042103500c595000001c6986038a00b80000707244d25402d0850410000e402e0603030009116500140c002e001d40380007403007035007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 9707381 1250 9706131 9706139
    0x905010e030f070201030b04060b0a0503040302060c130501030209031018020108090f06011a0d0606050c0105100e19090206030a02041707060c0b040302150703020a0207050d050601140604080f0102090a0501030506010801 96
    0xc040d0030a0306100340c2c00b41d551027000524183d40d400410401b5003680700ca0343c807842d050401a040540080113103061140800c411100301c42c5030002c840c1030324000d090060311800e0000100b4603003006421681081031601d01c0201c10451409011103403035100344c1e602e1005c2d40c1e401c0304160300c440b511960300341980c2c4074000620800203038500c030945014482401e00e040c804c90710014802d81e40380b60301c9200410300014501c0d103042000c0c0200e5138010b100d00c0420b2202441d003c0c0b50102054000d156450800c1540c4403500d1141c01c640101415540041c18241c82c0d0a0003100c3c08025403147c490000e54854604600442150114000d4112032181e1503117100d03042c1d0b81e15030385014180208203c0460041300c01d03076040c80d43e030700c0c1080b4080c20150342c006861705078080c0040c1c54120303a600140e00c100c0340b0345a400c5c0000c0d4001803140c1912458030549040c5c41c88200800c03c280130316002030645024411907003181540550191000e000100da03807520250340ca000560858030103841c11800580d00c040188 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 9708631 1250 9707381 9707387
    0x40209090f07051207030b0f03150f0c070f0605010602010605010c050309011202160308043e01050f070b0a0b0406030807030c05030d14010e01060807020a060c120606030905010e030f070201 83
    0x20b51200311030901a1401c0158180d0300c2807900111403c0d008655110501d00341801c08050003403031a0020b4000f01045281d19a010340e22810061054020840601c0002e168010a00c05d9800311036020116900c2c0c1002444c2010280c007003400303130a0056103041c800080303940c0700758591080e50707401c034000e113290031244001154406145411a5003580d005c01c00d10f4072207e408000d1032610b0f80241e9600805042c1490940911800d443c00c02110349c0100802c0403407003000070201030642d01140c03001800c09100e500140d03054000c29414580000e0045a21014400b00400c01c0780b2500c0100c8040028211200c01c04c0103d48143c0806403084400b030007240006805401d03500c0c011401a4222818030121512100c25600e0401a6480a004076801000815040d08540e4054400740c10304900d24907158400035901c0400700d00181c03110fa1203800f440d44d41405400501c2c4915000113050010725100c40c00a80500400c400880310303580b800306481500440803041d03400040300c0c0c515161404085030011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 9709881 1250 9708631 9708661
    0x601050d020310050d05100c111009050c0405010b1308030a05070602210a020405010e04090506040f081309020703021509060105040b03030903060702010b100801030b0112110d03050409060504020909 87
    0x4840c25042242e8007141c60390380d502d2880d051700e12030340c0109800c840034104602a6406581000188121607145040b2210081025481c041300c07484001001590760500c24a00707664070304100c1c0c0040c50b110000c100d50300d07410014040412107500c0c5246603a502c015032960713446008052340000d002400904002a4150024681c80300d2080304904510422a08501110b105440700003034030303034001004c001c42c2d42c004000c651072103003c650410080f03072581c80c1d550f01e52000400003044c480468039190304000c03089058034101d1010064034800d5545036004600258000300c3d080e0301500c01c844c070200e0070190440c16a441402200c0c007a2030964604003c1c403000e0a070015280342d0501007880b01402548040002c103200321115030022403407103038020500013051000e933252010020240018004208580b0180341115403e09500c000b415090605140c61040c04844540c0302882c0180d210030305034010b0103001500c144420801100b41e0b1081007208901c1a40c0741e09030414003400025490841c0b84c844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 9711131 1250 9709881 9709891
    0x180b030c070c0e0108010b0607080904020304050a0f05060105090903071212020c1506010801150503070503040804080618010f15090b01030b03060708010e070f052a0a080304050f0102030601050d0203 87
    0x1031904003a01a580c181e450707040c98000d0061240c00800401901200b40581d02500b0404d40d203c92409005481e4642c0920541d4071090060342c000010908200d401c00404100d02e8001c506414402d8039403030420745a100c00c0c451503104015a4003c50320030340002c82100c913400d0380607241c042c21420004081d501a82c03002446603103e5401c0c040301c07a41d00c00c03c2c88510320040d090754085105241c0324001420384481030304070000251145100c042c090350030034200e0f508045035040c1991643e4551030400090721581e004407410303004840a1080c40e0130101c400c0124094002e0081c820400c210201c4411142d2000d4401d00c00c00000000300151946644121084601890f000c280e20f807071007001c42d1900c20240c40600016410310010003600c458101e801d07800007001c4c58940f40e081041c1c0c000520f54000e00160103410501d21240000208058440b5010f2501210954a40043d503060032440c6401c115403d43e818001e080208422090600c212846408140c4600d400c02c0c0036401c40344000e40008007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 9712237 1106 9711131 9711151
    0xa0801060e0f0615070b040b0c0316080604020d14010305010b030604020a0506180325080c0102060f070e030105040c030312060605040504020a0c020402070506010602060106180b03 79
    0x80300c80c2c110300c240386141410b0315074070300080c1d500001501c0404034441c0002c090040002c030003129441140100100361140e40e40e43c52002d060f03c400c40740c005c080009102d80590302402510546c3d04840081e200601745803401101d02d08450096001c100350f85034a41c010002c00100740960706008000340c020b003029080950103e03025641500401d48912804244500d05100301c800c183d030091401000c0f01e01e244650b0708a10100d84141644142e80da0750711601044081c1c0004441c1a03110f0b040e8020181d56851011041d01d0041c06490b01080100341c200c460103540c1c09000b810700950007604c0d0411003d00d9494007900900204842c00b0142741025800c00070740b50044191001c0722429140981e41344034000c01100c0002c402140250712500c0418000c00380312000030014169459034080358516600c1ea01d081d50415650603444010440242e030078421205150003854200030309070 = true := by decide +kernel

theorem cover : BRFrame.Cov 9532381 9712237 := by
  have h0 := BRFrame.cov_init 9532381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9532381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 9532381 ≤ n) (h2 : n < 9712237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
