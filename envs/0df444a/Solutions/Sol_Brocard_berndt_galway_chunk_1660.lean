-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1660
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:06:13.137317+00:00
-- url     : https://prove2.me/submissions/f5aa661f-7fff-492d-be28-e22e8fca22e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 298381294 ≤ n < 298561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 298382544 1250 298381294 298381309
    0x9240601033918050307140109170624240c12030603071a040323010e010c020f0a020d0b0a110a020a050105010918060e100c03060302120a050a030f0e 66
    0x401c0754060800c2c0002070801089420020840c42d600c0d01c406100b48040d4600007180010307903055210301541450444c005a804902c6544102a9041d00044001000c030340410700a005010f50501101c1d21011824018080c1c0301c42040540c100d03422040090010b010f1440281c00c2900284949140180e11801c07541000d10b54508503201200000c10303c00f0508003082040e006101959848100d000010b0200440c5e114601c0f01820b802000c0869560444c0d951108240d1030790150002c0140504080103030b40079042402d03660015005078030010f08000700200740c26104581c011700216141c0380b9a954200c2d68034003d0214110030f40e0340c0d0712202242810000801c4c1010040d0000c103405c0300c1e1441e041d070035900e0582100c00082d0030080000c40b10720041c3c6510650b2a80040d01003034028081c1ca5092030219214251104c1c1814246021130785a019404130701540e000f524510620303100d20740e000d03550700c4202c88000c00302e0b0f00c00502d02c4007281c45114101c42d0646140341084035541103a000401e032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 298383794 1250 298382544 298382621
    0x11101020d05060f0a0305070b030712020c0607090905010501090b03040f050f0f010c02010c080402120109060501093216020a05070b210403050d0e1011030924060103 73
    0x40542e5081070002910b06a105802a02d1044481080c402e05558419888004603c12410140e001202090b01d503030052010300507800d0700110454036640452116941d564054440001240c003044001c16041028007500707050b540e045e15442400303882e10005107410703440140b081d64010f40051010340090303800d20020400b40182c20040c500319070b412020600711790041d8405000d40e0300d040c0c030309254660861600c0d87d00607012144854003110504146015083c0740c40000d08443c40c040001c28011541d5010030030010510891180f03070700801c038003001004446185580484400000100030b81240d000c0e441310490148141e901260041da1201d103800400d41081d02002c2011641040513000181e8808044140c8140b00307000d820144c4016009100b01c950658507e61561a4202e80394000c0240b8800005801400c12110380c8011085800d60010b69604541f8080c11525000d03028002c3d411140050b800120481c0e19240c07180150010182d1a5800646c5102d846050760089070901403a8403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 298385044 1250 298383794 298383817
    0x1303031d070303021005090a0f0f1401020301140103060f140a030f05010b09070c02010e10021f060314060c030f1504020307081605131503020702030a030f120b0f010c0201110102 78
    0x32500b10320303002e07042804100411413054507180401ca003100d000107101c50401c0d048072a40c1c41030040e506105c160342c04c0c8084c001d0090300e51025440803100e01580103504a418104400301c51512403001141503450306d00c81c10f030b01c800741040e05104070b6410f296190070075140200a61242ca42d03070313921444d0480d9000d800317540c2c80c1d41d01c6920082340c0c10100c034241c2c0e0162440c41c02d405640761560010300541d284680140c00b5a203190303800c00545000300544003902581c0c54101d80c181d030030f01020078042d0074140402c5400c24408200e040c0355840006140e80181c000501c130a0455a4036034000400f40001000d4405a140803842c0741d009440718401107028604640da41130003480c00d01016a40e09468035074140401c101044003500513088a94480107a42c9000d06584000007000000c0300030703003c0c0c6503020b175150207003030840c204042c1c002c40d041c0c13040d00c0d0584628a9000b100620041180c00e0b88011582229500d585044151b103c0d006c03000e0710600c14105204035041c415645130880e00310348440c50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 298386294 1250 298385044 298385053
    0xd0f0f02010305010911030f040203011d030d0e060f01030807080f0301090b09010605091003090515070c0b06010203070c03020103090204110309150c071e14030f301303031d 76
    0x815942d05000d100e0240000d600c1c24824941d03440b802006a100050405004240990208045541c02e4014080c654800401c01e6074501c00348003400d4680d030180b1054144075280c0006c83c0e015000100d1400e101700d0242c440508580c2c6103403243c0c015648080030469040e42c08001d818180380e00c03200903601070550b000c1d0015688012030148064614180c00c90b4050141c00d20090201e540c0e11900342e40d0b10000303841c010454200c1d5103401440d18698a05100780791701c3c100d040206880d8050342c4a030b58140141011405902c032070f4016a100e2080e050040c0009018140610155019422081006d803000d40002800300154281800030b810a45818119800461015a02ca0010104942c20442d48907081f46001c100390381d4580c1d403902140d941d800090b0507100d10014040e601c618041d074003050009032540c5189a500348030441c0c1c00041d0030084a2902c01103c01c000692131600881001d0103a6102d50b507423220b5007007040100080c401102015100d805841482002c151800c951048080050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 298387544 1250 298386294 298386323
    0x4081e0a02190e0c1b0f062406040306021c090203060112080d090606080705010302030606121b0a050304061b020d120204180b011b0b01050105071118070f030e1b0d0f 73
    0x10710700c0d4010701c41541c084e82c400c031b80000450754080340b000c2c1c00c11580d03211516280070b228090840116400c00c050381c0181e0104000050107403503002004109051122044900032401c210300450321500c07400782d01540508018401101050320010b416402100401e040c848040d5504003599115901158265140c00f170030071080b04104090f102410003400c2c25401c500e80346000c40d0b228040c1150303d0004d103a228011801402403640410103059620800b076641d2040440090590390013541c080314014070f015a6140314220003410100b030b009460307014201c601c4d40c4034004c130744459071020291043e940c01c000003c0c1003242924141804101554041450401000050111076040c0030711802803201482c4078002648603090181036035000d0034403a49602c1c00382051a68500070030070700d0350042c000441d042d03001c003099090329102e00082d61312042d0030603140d10708a0a0f201e0f122a4a401a44030340700c0e44001300c004004004014001a002c40c200c0d00d40c544854070b100d0510601641c0615906000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 298388794 1250 298387544 298387567
    0x1e241410050102060a1107080f04120602090a0b03070f0e030715080117070602031204170c0604050607020d0504060e03192f0d03050d060e0c04081e0a02190e0c 70
    0x14694010171041c020032206140c0031501d0018403840328003d1014500140360b038581900c85007658007a04000584ac1200e0b24070f0319083c0c001f94880f00700c541c4115a01000056a100d0031021240300340c0c0d89a9a25078031201c615400d0755007002002505034036025940700030408000042e80810301052554591009500d405204008240315440c1815141c01c4500241300707564001080300e018002e46490000181d0351401c212000070744000080e0051000082c41000e00080015100e00642c01041a5985501c0308001a66150202c0030000007054043c0401c200c10b07070185240320304000f8080c0030b0700e4030010740c034044507281122914201c0701e0038901490040168040007000700a030401c086080c40114000000421035200a20028100080002e80049500c00e540202c0700900802079802c0440c101080d03505007070b13000307401080410310896880105119044c1d40001c1c2d01c2407200e02038980700c4255001d121180c0c401e00103090a461030410005500c50140d1405442107441041c8a41c4800c02002ca = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 298390044 1250 298388794 298388803
    0x1c15090e120f18270f0408040326030c04031b03110609030a05012f0901020a110103021b07140414010e070c0807061406030303190c0315121e241410050102 68
    0x200604041c03170740c1000000b07009141183c040ea50082c030307050002800d10042081c8a2401d120200c0c0d954008014445c0980144015105507849086805041100c0303416544254080d0f01c0003604001400383c40c0f007480d0038003030010840c0c07000c094140e41550b0200c0c1c9400307003910f050058940304e9100745903203001040c0002c00300c200d92160500c00a0b00d40452240002c0d52075881900140c8a03144e10049084d550f07000b98101c9070a04120000d040e03e107441c040740e1546945a42c85500541c080e006000e00b00b600e0680302d03810f610b004240c10360ba00359080002000c1207550051200d410b0000022407080840c40d00c0c0040c1c034509118090200e040c85042030724030340d9250302070300c40c03402a48144148610709480745001e400844003140009009613444400300e0240c06c07031188811002444407008180c0300390801901b142680035582291040000d504410003031541d40380040c02200402c1035244020001070340600d0904001240419409004409034207428419141008a11101d00040255507010312 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 298391294 1250 298390044 298390051
    0x105030c0618060d0905160f08010c0203070f050a0206030405030715050402030a061a0a0f05030705010f171005060f0a030c020304050d03051c15090e120f1827 70
    0x3207400b07060590001022103644000c00c0810311603480410003190002150340030504543d0020219140303205d0b00d80001103540054003074000d14500020300441c00d01e00c14000c0b91181c1000381e0040d454400140c4440c180007207002070840b04ca0061080c0c140260303943c02d000e9809039005e88061075542c0f2883c03504c06801040800d05c00d6103141410100800740c1e030040342c0c0d907000c0c1d9001300001c11600342d01208055a01985040d0f15400703030f04c011001c0ba96240000d5044d00307559040d0101e4860035200c0e00156199242c0000d4180001c10949811400c0c00d45e003011550003802c4200042c0c40940c85400090351500a441c000c008954081007410440ba4980504e01403090740c0d002131850142040042280104035030780142c1405000500c005d0b51081402008449060050381009420400d4805c4240c40109200d800d0500707051141d124130310b000c080f03907040019000b1000145230500c42616041c00c1d400100c1c090000100d115a101c995443d20300d100030303840e80c41c00308040e045100d1242c20b00303a089014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 298392544 1250 298391294 298391299
    0x30711070f03020d0213090b0702070602061b0406050a020304050d200901030503031b070605070c140303010e060d150c08100f0e0703150305010c0804020a06030b01120209010c0503070b0105030c 85
    0x5070701003015031603152421160a0f0141c41642940410b524260003030090200700511064615040000150740820018240c80d019402e464403501c6001500d49820121200300c0c612680420003040101c0c000c0c8000c141c03409090054a003003075501c100188074440b070b034582135034840502500d101750b0411003181d0302a96003080b101c1c00480e5046449413581c9000c0108100d50304807403d44400035000d17220050b1100940e002c042400306180540f0000c00b04220000c007201c6202030054410f252110120599042c0c07468000480303000c0e501e0303104000803080340300f0095401c000d500d05100c56900150081101806081d2038525850a00401420b0307020303000c1d400380303030703d0380e40c0700c03800d119160095800d00d4004000349004141817100a504194cd00d0740356000800d0cc1d860041c1e5420100c0e08405958800c0e802140c9130b04907241c0c1c6100036416a1486007500340011609480c5034024841507020b000030742c00600d402c00c08000281d036070b00d196600802003621300d16402c0c00100610b2604000030444540705 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 298393794 1250 298392544 298392569
    0xc0e100e07141804050a09030f0203070506150f0402030a060f0501020a08031303030b0d140c09060306040f062705010f140a09020d08070b07030b01090602030f030901020f03071107 79
    0x1d10000c02002d060b0152641503400000c614401940d054207045142000034410040743c20000c0c103180080000a0007140826201c0d00101c40d05800402990743c0250017802419140c1da40c002111a004008901e41e0744c0002000f40030f100c0307916284042d51040038171010020300141030841003504403001d94451411580001c0300c0000003110441600e0308600d45c0c06e10000d90141929043d0040e00c0c140c07a08680149040b08040b040c89001200441c3c0d0103410300564040080200620951103000c6800c10f40560216001c90002000f01e00341703410981c01850001004502603012842c026061481a02010401c0c40b0b0201409428400d101880f840300324100110390707180c0c080c001c00c0f280040c2001221651444400159101e00743d4100019910101701c0baa01d68040c40c2a1803401c3e402c0c3d0303c80001a21749005031000754050b070140010b0700c0305170f001181010114182d201c10b07540000c0540302c665409010704c00e030400301c6c00041c500611040d1190060494a000d01e00d24041030795102004030840c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 298395044 1250 298393794 298393801
    0x3031a090105130e0309060c06010e0c030c030106050901020c1905011e0e10090b0403150e01060812090a03051915110901050d09020306180c0609100305040c030c0e100e 74
    0x5403c82d805042c6600351002040141000043e503046000b42081141c101c84005804c107031051001c50b10070b06070390b4200c282c140c003500c03291034900e04c5010444241d0700800c0d00700300500485004102405549034144105c0e0300008041c800708003107a030310a0004040d41840101407000c0d40e004001484511003405003510301d4020040e00034211003000c0d01550040e02041007d5038801d00c03c00505014100c1070300110396032940d80c40c00c05880000c550b00d10510364a000e00344c500203603040c02100100c0380c0783d40c0140400780c425a0950031a902801105074001225000040060350500030315080b483c0f6154880760550791810f001441c2c8c00e819800f414020315041c415400b0701011302c240d400c40c030f0080ca0010b80315070010204030010aa0600080d5040c8603110800c0141ea44990728804800c80080555615107041c005101160040e680401d6100401040681116110b50712041d4081d003c3c041c40403406a507034503441c0541181e604108800c850082c1000010030020b071108008201860507400e083c0b8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 298396294 1250 298395044 298395049
    0x10b010509100806030f01020f030a1d1c05070f0807050123010605070f1a0a0b06161e170d1b080402130209130b27190f020703031a090105 61
    0x5114034030002c1032100300004142542c0f8200082440c18040c10000c641ea4200c00c1d9900850740c0007250140d41450400c0701c6c0110155075043c110070000c90410080c00112040c100a04c21000c803400200e0402400340b0102012603500d2014100841c01050728680c1da04140c108079003507540c05c0004410101d1046070255204ca9810a07040c1181c2c501d1800310f85644841c40c20802207c100840070b48095000340c1080c0d680d69101d03074000d009401c8450104440c0e2003000901c041e50050010000751000030000c0180426100100d80103044a580041d104880a40c0d03540000c0e000361701c003540261070000c907190075101618440c0d0070407484440c00c602040329201c280240b0140006000a000b06184120304182c1c0490b80c054071443c00005144603024040c00315800020000041d50350f205000c00d2031403038404003500c0f031142d00e28160350001c00c20f1a0307034002c0580b48840308941d503203040c543c1d1594414484007040c070180030000e2080d6804140001148151200341041c03928642c8103000400041180e41d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 298397544 1250 298396294 298396309
    0x1107090908032202040f15091e0e0f0303090d0914060d0c120c021f060b0714030d061721220806040b04210203040603020d0207150e010b010509 63
    0x814288030700f2000340c2011240b20070000c0c1d0080003034005081403a00c1240050702e80207160014894011511a02c1e0754112010548805c540c0d410181d60780072582e1030f109082900300c100c0065202c0d048525050030051564a580c1c4100c074015401d030000c5030040e500550046c0d5820042c410562307660480441200021954422031a03600040e03a5501001e0302c078507000c4e030312060500c9920001000451010a00a51150016041400140345140d055901d240040c0f26120540b010903008a0030103150769a4090724210030080d6411501c401d2221001c0409a802084068030b403202900006150b00407000e031501c100328412242d030302d1402820000c0c0c2c12510046d03074191342e088001c0d045255400c050680021800c0d810000003400703108200710511081c0d81410740150b104111802d0540580101c1c0903079102c03801340030742c01600200300c208640c0744a034002d0314582c41801401440e10400d039032400d01c12800404a04044c60f00d07410101d245400c28031603202c951500f0b01340b00c0e280416200005400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 298398794 1250 298397544 298397551
    0x3030905120313090b011b050615030a05060f100b0d06031a04050c06030619031101090614030609041406070f090603060513020f070503070b040c050105040524130303110709090803 79
    0x180e0304c00c04800d10b41c1c030410f0303011100030031f481c0d403016403a0786402c2440d1681c02c100c5111692101d100c8180c0000c4c100000c4234203907160810040e008584403c5c0c00480c0500b00685400c0c407440e5410400310758524840c000340480c0d404102c000444034a5031800800c003405401c8042c0c0c5038504003080002244e00450726425001044600726500d0381c801000621140118034015a50a58031402104018003010f900c864a0741c00d88a09850580c2c0e404201c5510740c0c0c2401101c54414144003003455802c7c00d104490f0020b20401b801c2c4005c142a4031900d14252048409100044c0e035030001150941c2c100c20500b025088914081c8110f5003402c0201340c0c1c2041040c20000f41c20f50010b040001c10000405540140c0d90280c01d5950b640710604040740c00300e805580aa40c003410150300010380d58014003c507011580041d01c1c04416503a9400f4203100000c10000660410030104000c1140f02901007882000c0c601c251144221001c2440b1858a86200380d000800036a107803152840100b4a041c0940f90b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 298400044 1250 298398794 298398809
    0x7080904050a0f0c080103170a0c060b04060e1302040510061b050f0a1b08010203040f140f0d0909050f070927050a0c0e04140a090c050a03030905120313 67
    0x40c5600c07004002c4008101030442001510f25041007600364641c0301c82c069040328021403e102880d01e040b40300c3e03902c0d84100303008200854008644200001c22079003011700c82420090001031455541c0c5840d014299044400084502101c24000c0441c9000d01c10a81c01a110b8200b650010703080c40030142000c080c410040c0e9900311502040c030b04200040220000d183c90240980c0c100000610b402c1c0000744010750380d520a010038290210300c0b20f6052096901c19904030320002403130360880c2c070781001400e40260450114010302142d40101c14003085150700244555440340c861034a808107550440d2002740500201c044070005101d03400d5442a503080c280c903111514030108034449180c2003809502990324405041c02c020812060016990090452000f217450f100e0f10b02d9200e20800045a950025421411441c8400324543d4402c03070380180d40c42c80c4140100fa0300c03240c8a10024411161650084000606050052149041034650500900000001141400003005000c0c480c1041400b070a603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 298401294 1250 298400044 298400051
    0x30a080118140c0f041d0613140601140c0708030901180b0f0f0418060911311802070507080712030f05040b070501060e060604050312030601020109080d060608060607080904 76
    0x110354143d48102d4005102985610386000800d4a6013101800c00300d60b550f12804ca14060610007142c3e602551606440c01270702400b6030f41d00e00005541c0218250402129070805108000149000308451000f50007110011038990752008001890b00c920300011145e101e2038043e040000450304800e0ba50300d4040d03c0851911800c20000c000018002d6a1107072103c0c080810300f1a032900c1d030a40c07040003610081482406a14041d8034020403d2195058030091000c900d03008080c032196000481020404034040100e01e20307a150400c4203d035000342005c0604a500190450800c00708114000081c0282c1014014043c40c0004807107002c10040809814003d42c1c4c5050038400f407203281102d02800031883d403030742c882d14142040c034002c2150340a03141800302100040f640d2840c042003941e089420040060506a41c03808503288680c201078105070541d9256003404002400640140400e1000385500046107450500001c0c840c1070040c01160041c10308211120202e210031007100c0c0d12103000d54021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 298402544 1250 298401294 298401307
    0x5030402060f091c05061501020d0e03210315010c050d0521010915050a050d03050c010204050a0b0307091505040303110f01020415030608120306130e030a080118140c 73
    0x161160f03c10041210780c0840c0030740d08204840d04e03a045807070030342e4021801c40d05590760301080d43c81c044011400050240e4003200300d090925118207602e140e90b1602405a0b08801eaa90800005010660b1200c0f401301c2d4010041180c008001090080e07944402d203404403c1e98100d407606502d40440201c3d91040200c0090012400c0800600914011000480f0b000313403581d644441c0c000800e2203a45503210f400c4000000101464441000c405a40d001442c0c1d043d56146c640d01a252070380500000000c3e55002e20000030315235140c1682c0d200074000800c10a541c3d10f00182d00600300242500102c0800c00d881d10b4840d50b03543c0c00810754054a5150418404906111640c50f103031038003501411202c0d600016000c03c2c0030b5285200030800d003101da1014010036886180031a12440c88502d007064043d002c0c80081d030300b460900d04c0050b146214100c0018068901000f0608540c442c3c02c4060200d101c0500420492038217401c0400c440d00c51104c20030100000d50800c260a49000e8030403000b902c80444c0c0d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 298403794 1250 298402544 298402567
    0x305030a0e0a030c060c030c09060f1b081e0a05041a0d110405030706021f051305070f0302090f1311010e03031306081807120c0509040303050a0f09030503040206 71
    0x1204156180d0080390b61034160b0785001010f01040300701c1181e100d0b0034100302100d058003d000b02c50385428540c0340d900f02c00e030070040101e54201c09801e40e40100500e2070540400c00b9075400101d00101e000b1442c01d991904008002c9040412000000202e2a010080100c080394403005540540d0048019207002d6071114041c40741c1030103a0039440000d6460f00600d00f061441d110b00620840d0011f4003680c0015540d80e9059071034080c1c550100648242c040d0702001401a250700c030f40c0e4082400d8180d4007104400d9164649414000d0300114811100c0e54400e0042d45007034085c445e801041615141841e18041a01912000a204e0010308611001202c4500c580c01100d085580c0c0030f000e400c994444208141ca450b0b20800d074403842012596100c08070301d48100c810412403400052078000c0c40c14030301c2c00e98905110036034203800ba681000401400318031a40d6044819000302e000c0c0c0d80106050420102d91800c83d4802c01203040540c0c0380424000c00a5003182c29a03621617011211030303840d40302e203000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 298405044 1250 298403794 298403801
    0xf03080708190306080f0a0203060c1e0c060103030201140c1b011d010501051008040c030327080607030b040605030c1908032d13050d02010201060306050106020109060f06050603040305030a 83
    0x7810030a10b540214001c00b401e0741a80701c10708a40e88081121142d000c0780340d20703907124401d201e0042d40680165001584c0b101460b8010040c08814901c110380b07004113020103007044d0304a418001101d030404001001410741c24041c21946021042d00c440310350401000c0c0300340d1845030320303680c0056100420004100030029400b10300460300f000c40308480c4d003d007100000c0c02442c0c2400364611500c040c0c140121540e00c2421840e205541c8a80320400060030741c2c80542e242c542070b007000d142030030742030700e0691511025004e40f1004081440080c2051304103800c0160646031502107a90050740340800c01c00807541c0000758464007810544651f05140740340c0202450074000b9400c10842840002000306c500b240714001d0755a034410011005110f040b43c1c414a032400c0c428246410350400f45a90144064a0028a5084180d10500000034125500c1e940c1006450b001d074085800f50355100c01400911410340616584040c040f8030401c00c09042400141d401e0001600150400c00003000003400780440781d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 298406294 1250 298405044 298405057
    0x1060c0f0c0806181c050313080d0c031b0c0308010b0c01020d060b130e040203150603010b100201061508190b030a0b01180609150e070e09130302010e06010f03080708 73
    0x242030340e1140c41c080840146280340b480c0c040a407841040101045c1044655140d48002070f01e640300c51440d01d4400802c0c1030802112006c0e103d504081000c1001540741c0e2050722100d0000361000300302d248085000d4400e446180c07402c2410300c08210762950000750710600c80c03415681403102c07131500c841000d10301a0080c094101420340c82c0780742100105141d402200544540100d20900c0f400c140c0d15418251094030044c2ea00079010341c0305030801d100ba40003051105a100d50041c000140f08004400005d012100c144045005070b5502c4a0620001601d5034421407075042a003030011060415011828a09080005c5101c170180c0c0c4555008440d07400f880790f44101c1d40c21000807101541c58a048403100c1e20074a03030002d41c0524008001450742558021400d64101e4454888070b400c0c43c0101e0b0804603c1c000749513404000b080c07860b9103569583c0d140d040380a031040241515030480035140103421606d0000c01118503600a40040001030845d112080a503540510b00360b0b01c44400c1d140c410028091700703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 298407544 1250 298406294 298406309
    0x60221010b071101020f0a1e0f0b1005060c0c10050405031c0e0a1206090c180501031703011a0715052a03070906350412030501060c0f0c 60
    0x800000461494150140c807015014020f1080c00c0300d03002006980c0d6910000111a007600a550a038010482c140086d41c041c9001803013840450440b40c0d101c41500c40055022101e42d00303401c1c18400314045044440000c3c01042da0b54a1400c01c02c0040c8075503070764580c0c1c6181d02c501080880303204010310a5068800420000c3d0450b03911020110424154101400440340001c61840200f441450140004c0d0202c540d20401c40038504c0b20b0380c5602c1c010303140516003910f0a20a202c00050340b001c1880c070725058000c82d541c0c00219941145440440c0c90320061400030718910500c01405a0a000b00c51003e6405420340400e649407224500650300700126211605840e141c0b02c20000394403451038460000c000900e000411403e0100d00c0280a80410740e4000002000008140000da00035130200110500a150010f032100c501c03000799656030142c41142401100c1401407100f04192365143c8040c07001c0a08050101c0e6040900c000c1030b60003d40d101034005170a0f900010203000d85c1898030006001e05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 298408794 1250 298407544 298407607
    0x3050d020d061d0709061b171207030b060717090424091805030a050a020a0b0112030e0d050d03110c07080a0c0e06030c01030b01030b0306070521010b0a0c0311010203040c030b01050103180602 84
    0x1002700c2e400043d181240c1e00310100742006840321030b0703140c640106e0f038100740d00a070004507a1032207143c4c404003a04803032607450700641c0d03415034034690740e0101903c514030b8641c1104281030581800481300c180c81e03440304400b03080c04d5061980fa00140020090340e03800c211600c1c0c01d5440705200784040b403903c1c07000600900750403840c1c0008500e00124000d114070160007500d405090340501001e02943c00d4408802030040c2d04420054040580309400195041ca600201d15081100c540c086909111103540060141d5000c60b84010030016242c0c00d16000304034801164025203004008641c03268a60401d181c1016603503207030012660700036408071030b07a03802c00350465526103407200020300154010400000c0b280751030f60360300c0a54140d018140381a0360011007400c0c20320141860507208424518403c81c18400700400010b9220000d102451182d030180710a03029141ca94180a100030fa810303040241058201749519100500038400144e40c40e501c401c0c010307a10060038410300442e650011440032034864 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 298410044 1250 298408794 298408807
    0x3062907030c170a0e061623011103070f180603023a05090106032607140307020a0906080c01080406062102030613050a03050d020d061d0709061b17 65
    0x4030340083d1030f07a00e07001e840d14a0309003101d804206007401903028100c007d0b104100c154001a00c2001d407032000e4048051040789081c555580c0c5825507a5125091001c000003000b04940c41c0da03c000d80d4001421f4508100c44010758140140900051034090041450380010702590003400c131562a0000c100e03401907682c0001000700e01d91100c00f0064108101041c1014003150300300c003040c0700306001c07640d000300841107821a5042900c10207081603101440c11100740700d40e01c0414215402a420140351901441e40c40390749204200c05502260401104680b401c6000c1c4007003100007641c401058000d01388003a0b01d90b03036860448040c2080b07421005038040342e01e0001c003282002d900130181d160720031000d54071503603600c54100c1119082c402c0060113542c4074080206c0070a0182004180d2404586009413505420303503244004e551065001c038105040a1145042e41150078400940108051802d00c04552800c0401485501e480e46801c050300e0a4010001c20000018030085d04900c600009649034030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 298411294 1250 298410044 298410083
    0xa15050a090e090a030806130504120206010b04060f0309020f031f060801052505090d0c03201509010302220e0c030f311203062907030c 60
    0x40140d00020301194a0040c041001e50781c00d0181c0e8841c081d12030003412078400544048030341c1100030342180d8110035081d40b03103620b01c20f82d801120301c103031700941001d0000c1070078081c000e241180503401030007000801d00007802103540c00550a40d1503030040c0b401041414460001449140d540410142d046c03040481956030201c0b6008000c80c1e103a802c540400196903550021826144100c070038499078a4019061513102e072980c1c00c03e1442c901240b134124244510203000c154202240359040d500c2150013002042001184a041c00101c0b43c58030801d8440c401120200798000c03c2d0f0140da12039428046020003899202c0d505590070348010b404032b070207408280200d6029402380360088051034040e03030780040e082d0059070080302d0003008044080000d5641e006405501400c08078903100c00c481580c00e000741124090b002c2c00030406d0144140b106100f001d0407003c1d00315407440d4001800c0302506000380d50b508001d50320240d00009003006166076141d143c54101c80900002c0c90007400407010361908103e40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 298412544 1250 298411294 298411297
    0x3050912060a0c180e1009060905041e0201020c130e070f030501060807080304210506090d0f0f0806041a03030c07050f010306050d0f0311010e0a050606010503091b0a1505 75
    0x64182c84000c000405844204580d00740000c52090780c0c01c00007200c10014118001368503644210948001c007030041e1600901e0040d80e890b0707070010700015111010f01091060511030200c0448004240503203950980d40080e40701e8410154072845001e8a100030640000c3d03039000a81401c004105640300c8503240c00d40103880505901003a60190301c0c0c0781020410a000242c0441601d02c4040214146807600a0240c0c0051307101242c4181c00406584000004204200c1c250044d60b042015216500c000c440c002c0081c0d178800118001c000c111003901c0001904044c07041d821401c140c8000c00d204c0040e845402d0a104040c8920742c0501c000640000742072408641e50090322000c0b00c42c8a0103c00c90401107065a609000307003a40440c4a141180000b806d50500c02086407083c01d0022124440c82c84103402c40b01c800f0100c800303981100610790100513060020980c0901300742052030460402c542071582d194010428040801c40000f01031100d641c0b500e64001c01800c680c40514440051203100030a40e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 298413794 1250 298412544 298412551
    0xf0209060409061e0303080c0c12040308090108060306070c02040e0a0215040306050c0307200a0219050a12082a060a09140106051e060906181305100e040305091206 72
    0x3000b9a00428002c2013907640700d01d0032a905aa1a14000d48602c0f002d50819171040c0c50040842c8589045c1000a1081c0700c0600010350003648010b031515207001c000740c980d2600916840c4241c01150810002d1a0420101300407203805a400045110124101c2c0d403501d000b031140a50721a0403030051001c00c0c2d01480c001c3c001d6034800e000501c8291a000950f04280c0005d40300180403501c6c101009041200c101c1c91001d07146000ca003195106401500400c4942c0c0d0034040051290105500038821804d0800d5072000034002804d43c00343c804196200c003820750080c52450198075403040d4200551800c60004c044d500c0e4252001d607002c0e801c0008500c0c0003014480c2d001c03140c4a01128506504100c10310580d030441e01d02400030241c40342800c00400c0b40002000036140d0010003030201c0e66007505c030f0501a10710404602401001410b6110403c03a440044203510100c440c20141003005080d4095110303811105451800c621743c1d00c49203029651401089a056006001800000030081001600601 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 298415044 1250 298413794 298413809
    0x2030d14211819030e010c1202010b010e030705030c01051b0f1e010e06012d090605090108030f25080310030201030605010504230f0a06020303101211040f020906040906 74
    0x80b40030444480da5100c294050f112503c003021900c128000c40c1c05080d520410480500d440700702d0030103d64581000444201da5200107030340d10700454001e540c000c0300c6404021000c5000306007c41c0b4007000690b440c88100000c60412402044003460942c10b00c618020600b8002d09840141541891060b51243e520140e40805901707006c1c03051070b52006200d14410101402c000d40003030303030810061060f40c15299104001c00c5410ba1070030000000f840200030060068600f0225407649071a04000c405d05060700a280b81e500200300e01110240e2400c119540b9404a514082c21140403c0640c4015448040c024100300340c0042081001da0a0303647c04004e480c03003602c0401901c4c2d1540011030307040c05580125165007c009081d03201d21002d1080714604800001c00243c5001621070128801f0070140d880341d000f5a00100620140f06014908903000e00300c02e00702c81030303500340700e8903003000050405a045000d90742c5c44825000540700d6030112400d2040160019654541d03403e4000000c0c2402c2c441c0c0c42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 298416294 1250 298415044 298415071
    0x2060703120f0504050307030c0302031303050303090706050405060a0c0c0b0403060b030106060305011409040c15050c010f021e07171602120102031e070909150e0601090302030d1421 80
    0x40d8041c031440f0366030007941c0000c0118101b0311640c0d42170782d00d95005541502948810300c005d9044944800d0030b07001170351240d000f858503410040000ca141c004e064000409008041c40240321940301c00080d1200240d05207043c0b0b84002a074249081d41148641010b100c44c1c90003c1c012040c024143c120701c400030000d6008100f85a505c0404400f104c0c02030203000048880391040742d5140c608900c046401c05d000d2401d8013111581c035054030b00700607002403842022940104031382200c00303070a104002c52915036450079480c181811901505034010f848103481061008510300083c003828a4440b4507007450300c4400c0341d445817900c44190041d40c40744401c0348207408200c0c000c50340160600130f590296552441500fa000702d0842490302c041c1c1e0007400281040380d903c10000c0c400c00315008400b101c214820001302d159013004040002410007d10450601024013001c000580f000580102c04150794a4112040c560380c00e42d811283c46000140c1001c00d500d400350900c24400c0290140c010703243e031058070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 298417544 1250 298416294 298416311
    0x140d0f020901020d0f0207050112020f040e0601081005060403060515030a030216060203040e06040c111504120c02130e2a04060512210f180f01390206070312 69
    0x22920b01400491210050704011f80402265004811004501039090009420481e0103000c8030520f0300150300c60700103846100e080c440607581120802c2c1e040000c1a902012540c18035000c60854403551200420183c1d0b40c00001d101d080300000344201e80f1000409880e54a065420300942c3c2d1115001c0c0039010040a40001400b45d00000032217003180d828810440b003682c0c0f440c00b0071004100720410102400030007500003000410900c10500e9401c80c011090000b41414102042c034580069880c105004041e588500540c2d0341c20000c0c82d0141c00c4445c013254607504d4030042400d00e1300307011040350340c0130110b5180e8030031424803001800c1c2908151420840a9502c2040000e5686200e0904543d50000c010b000c0c0d08028078108010b45d00d015548107440c0888080003400f260384480e01c400c0010010800742d82c0c1901d0980d441041d40c060900c0c11030000c0b21810300465003180380c05a40c0000645500c00c0b0421034242160360315009070002d0555454040700c0c280900301801e4640c85818951a00216 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 298418794 1250 298417544 298417547
    0x70806181f0f0806010510091d011a070506041b1203030e1504120503040602040e0a0e070501032304050a12021005062707030e030301060c0506060901050f01140d0f020901020d 77
    0x542c0c1220500c20081c8541d0746000c00f0301c007031880010780402c10040d1140002c00c01d42c3e603045e0b50202803120380f29811650f62410100f07500c0344001ca0065641c100c405c02840000c2600013030303080e401c16000700c0f502e403549000e01014048440580c0c40803500c00c01600c00314003410341652101d03030020825004d450440103551544800c0c03a80c1150000e081c13041054419160038072601c05150f1041c800d02d8014906520380d4100b00c51240111810300740981c9071214001e00181c01d002c4040102020308040c4541090004860010f04604101003000d500001c000340a1050410800842c5508404205c90081e00300d44003e4a501c92100480402420700700412194100010009401e038045840b8120703004212225007044400541441c04060300d0322143e60343c1c804144021030080000e520740710507a000d40d20740385041c8034000700f03030511440a0100400207a01c0c0d00200c008032410074a46082021501c3e42e290340c080c0100c1754a07000e03403031900c4618078a01d40b10358001c241406003602113484078240d00c0320 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 298420044 1250 298418794 298418819
    0x50a0501050f0a021501030c1404051b0a0903080703050a081303170a09052a060f03010504180807030206071202031501050c15040804030b01080a0506070806181f 71
    0x8490004074208a000780800a0401600d407050903072060b00c03842100610080301a0800782c005541001c00c41f0740c2003240104501800c03c030005c041d5401d01191030207100e808444140409500541170740001c80640e01841102c03901d014560040c940c5031156080c0c00c1c001d0103038000000c45000710b441800480d6901042030400100c00341e1581d105181c26003030940c107801082014210301c107190344030020200020414041050106a41c07481c000781c00c840c0c2c0361a8000200c3e0380141d1030003000308100c2c039040c1015402c1128113562054402007031f40c1d0845442010035015422000c0c10402001c5854403c055004c075000d4041d111079501c4580e0940e031243c480d022032205880c50403041c0345142219078254040c102403c600340301041a41e0304144039510351a804c4804450454000d44009401c0c8200580f240d82c283c090300501005141644190307031196603d03000a03281d03c0c00e00c25000e0014100307984010350380e0008000a1080f00040c100b00c41e08100c00c1c00a816191a40600d102010a0a080a50 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 298421294 1250 298420044 298420049
    0xa0603021c05030a052817010609030c0302040c0512011814240f04020406080a050901061d060a05040c050d0f0b150903071509140a03030e1c05061e01050a 68
    0x2d014600c2c00390a00400c0c1e0322980710402c0c024166803c00c49200b60300c0c06256404c00d0b10000c644403a08928852130480f074400344140c0050b010300080a0003070000c91401c01300c620649034183d900194802c104035041c1c03418060800b141e5441d89519002050803415038900c0100314034008018020407600140002c000781c0704640741c40b40f1003030325240410314000003200c841242c6000b0305003280d10110b841c040381c1648d02540200e4041003c00c0e00740040d90360a07110716580200400000c101550420082c120014252035032000e1156440011440701ea50f1140f068008200c010810803681020315000303000c40c2c120005000001d4601a8000880100ea020700c1001d110700500f44844550340c2c21440d10207401441451b41c041c400d090b0041000380607032191100f50885910b840100f60302d40300051000c418010f004d40e0017000c40c9902000040e810813043c0325440300c00c41e51f0382d4060080050240c0550340d040300c003614034895203050004208102ea80c600442280f8400300c80d00c3da03210410f000e0f1030001c0d403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 298422544 1250 298421294 298421303
    0xa02070809040c09030503180a0b03011a0a0e03070e04150902031911030a0b040b0714090402030903070203010c031a0a0e040f0c08251403070611010905060a0603021c 73
    0x4000d03554a610b0a80c0c000320300c40d000e60030310501c1c0325204c2c0c81d074034a55007024840d6254044940301d402100c0c64442501c500505000304801d14641c10b1840e441d21601461201410540010448400d0240a081c1c100305241014046424641c0d0355419442200019a02170321024460190100c90f0421070058801c020b4004e4010215004980940c46804200c2c40058900b582d4842564840c0e940070700c506103201c0d014581215460905040008007460041c01c00340c24007000d441c1c000b030070661010a40b03800c0001190016100c0c1c0d10010791504621038000000c1d4503500e0a540300c140e2940503400078210301c090241402c15020000103204034400c007405008405203004c000a400101c28a04401540c3d2080e00c8043c5650b907034010b030f246850642c10214034441c00703116042c54000c680202600c01003070700d1039501d100700300c4070f9000c25111400c034010101040103604c11048102c4094104481181d0300c0b00c21503500b458040c0c1c4c0381d4001c01c0c0e1070008030302c0307211191441c07104001c41d00203000710543c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 298423794 1250 298422544 298422547
    0x3031d030d080a18050105060102190506131505040309090501090b03211309230105330a03020702040f05010501021002130b0703031a04060807051909050405030d050a020708 76
    0xa45400761280c40008103a1803da503142d0410070320718502030042d03c0c00c85202c0c6001156904140c000a81040182007031b03a20380442201d0304102090f40054002d801140c009540041c0c1c0381c413410704000710700c0c1a880f0403d040303007424180410541e01503001811a44994020491642c0b1a8111801c0d01d05002900d680360340302502290300b00740c05950407458509403180c900d14080f01d24240c03240700c400f59407001503ca0340d51056420074510181c03c005c281c1481290380001c5605000004104012408211100d18204100000a6080f03884070860804c92064003d448801204c001000b82d0710881c000c900071070402001d0420f103811400b400e410307220705801426028004804200c001d401440180000d4940400c001501030000c1004201c414020781d40031460081c200816440b4407002c6c050f0034010340c90000c04022440700450400c0c20f560303080b1501d21414440b21b2041c0701c104941e40128441d0361800042c8401c12000000800041800841c00d00c210782d1031042031403c9005851015000913070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 298425044 1250 298423794 298423813
    0x30a03050d150605070b2211010e130c0905060705060f04030210020409061d010302060a0302130503070e1608070f0e030a0501050f0108011104080a03032d020403031d03 74
    0x80c405401c480901001c00912140080104014121180c2c0490081440014480c013032205441c1401d80c0690017040c0036991240c4000c084000580c4d03800007a00014820441000e981e10510207000180d80081031140c03103840c101c1100c030080c841010018045411010b00203598240742080c1e03513210f90810003800705640c1d01d0711103003401c0b00e0040c0214114011529008a18842480504054810110300180850034101781c6100d40520a40700c0104483c05001000140d03110b6046071001c0030345242c0075840c2c05d2103200c200c0c2007034001e82040d40c2c0741c0900e00f008a80c1d5010003000501c640303842c031002d50265245110a65942d5026a440c50000340b0011880046900441442c450501c0c080c1c115140b0b5001c1e51640c50840d00c003902c040f000350844e40010000381109000b502c4c01c021190306d1442c134040c944100b080c0e8410f80317604014149070b02d030b49403410341000c09404492500c1d46d080820826411040680c4000c0d44540411008510b156421414243d40505034032013a420241c0140300300079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 298426294 1250 298425044 298425047
    0x40c05040e070b040b19030b0f010e132f03010e040809010c06020c010e07080d02060f060303091e040c03112b110910050a081602011d1515030a03 64
    0x3500c00c074100c10034820003100141d010342e184002c1c0000c0000800350340e181d102079030550900d208101c4002040504108655009540711440f400907d0001d0a0584188400001084d444094041983c07a214908841c2e8095001f45d081e0408004542584448028491004100f5580028000c86d0f41482200c4c0c001341c00a1340000080082110505018140300c2c01030380c0d0b04c000d9070b07c0b03403441d1341c00e03a5190b19050011210030403440c40904044400b9011092070054001c1da00c420007000c2811074484540460321781e440610840f29001c002600041301d0a03002800c01030700d540e00c5814a40140e15240b40f418149110384556401210038100300361400350494500300503c85990300c081000d901c140a0440300b10394511650340314009940d101d03500c2e840800f04000150f440031144505210b4200071803441c199008460a50021180c00481e03991034211400300d00510b0003509002d0280c00b200c100c1d040c480800592281c04481100c2c00803400d9507280421506804201e5101c5e4150b44035910300000a03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 298427544 1250 298426294 298426301
    0x7080702061b0a050c0a18050604060807330906030209012c1305010509010605070f061a190305030a0f1701150908030f09040b0105070c03060b01021005040c0504 71
    0x240010500c50411494060402d8803803440c41101c40507074010902e0a040020a0014125902d4200d801100441c500032000850074001629200203030303030340e000091340e80c0c0c0c2d030b940a0400f4040110071646404c0d00c80b040700060f1610982048151198920102d50f0381c1104c1030f4940304a062030b50380c9030260340b030030100781c000e5002000d1150600205101451100d40d601c0c0c0b40900445c5e2030007282c103a0264600074024800b0768080c00c8d007501030170100180820348544030364504403005498036940d40c0c0e12500300680d946288947c000d0500e800c000307a96a09050040010041c404211424400043c1c0380441d5250400350f80300081c5a50418407100204601802180c0051240741c182a060602c6c03401c29a40d040784e09070810a00c504403210038054103540f046c0341c1c101402d0354100451804e24800348055140c003e00b543e0314480c580791703504d0400c0341c0d00c5901581c01c2c03a5840781032404240d0301d030303c0c02c40040c00f0039103111030040c4502c1510030040206400307802c1c0540d4202c402514118200820302c0083c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 298428794 1250 298427544 298427557
    0x12020c01021c3c020706030c1b0b070c0506070801090605040510090b04060f18051806010308070311060a062d031e02030d0302030106030c08091b010908010c0816140708 74
    0x2c50050007048004515000710b038854040c3c81c1d501503d04a0b06000c1e001d8100c0d04030704840420440a0600800d4900440c4108c81071142c0081040f43d0590764224205c1e40c1c0f28030480010400c1c0140420300c14501c0d00002d446060f00c0e424841400702c0c44e22201400100c0c2c01c1100c07042e01415080ea001c0101c808641c0c8000e84c50320003d0305c0031500c40d4980551601c40c001a511242e16980e0820310311030307100410f1082c0ca410061411410810702c20504c071b01e65507410103000160482000050350801c26014800b03801156140000f80d071142d29000c8050341c0109514491540c00b20300040d10f1410711480010034894a104540880c407001f07086450382100c900a900c00f2800404016109101503501000044040c0395155800743e41c81d810310748020240c4a0701100700301404403c100b03100403030f540464500840c00c0d0683d000307a01c40b0f15003401294464429400500e00303500e050700d05c80da034560120010b84200c040c03d00d858110603850b8011a040d01459106540e04075080c031510001074500401400c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 298430044 1250 298428794 298428857
    0x1103061509030d051e040b0a03020d060504061202010909020f0a03021b0102131707060c060c020c090903040f0b0306010c17040b0d020c010c0216090b0d12020c01021c 73
    0x208000e00012910304140c0321100c201184c0702060414544e01a10b11035401541035400c420304207460b101d4220114080c2650040c24960080380702007010740c0e250710a90003002e0040091010580d61000702c616452880c00585c00039020304c0000c550b404150003140c2c010a200d510302d61404602400440003904642e06d000007081d540f00520316805400d0000c0c1c00d0703540d51000d1401510746040129000c2800035142d6040903044802e080000c16005150041d00310b41040000c1420025800c04034100203c0c204041d50203c0c0c0b1500303100c07070300400202400550f048000c040d80f0858640a4001c1030380401c80344240015040c2d00c3c8480060101c0c0001c032003500c203940300c15003442d4540310701c5080c40d04801c03e080d84495012a208084c12803d0081940c0c10050340040c100c48218014402c01040c1540107030381542d900d4041c000443c0c0c0394001c01400958101d14105040c1c81032940c000d440d60640200b0074014030542d5014141503100074003010402c162520b0704d00f07003045031010041ea040c6110000d80b1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 298431294 1250 298430044 298430047
    0x309170f0f06061306030f02090421030b0a091401031716051b09040c03022407050601030605010b0c030406030c0c060c0210051806010506091207080c01080a11030615 73
    0x32620080080c0c2200381c00ca50301030315080c5485014040d01041200d0310381105804c082080001c90348440e4065211074040c1ea880d2501d640d5810b01d0b0300100ca41c001c1411684c05030311985048944d25512607a5090382c200c03521800e240c1e440300e102044d01c2403a002d100328151104010000941307800c0a041d401070700d0701b6000341460104980080b02c030622950a0340c0c943c10601c00711107a00c0380e1201159203540121004096400d16803540f9034061030b64080240180c6c40340d02000c458a0452803010426001c01c10705659031082490682e40303400c0e080c0b10440791203003014004681e806840064802d01e11564004608007460810704501400c0c040801400f03022107110305101045d0302c0d010b01d1500d40700c10340040401d0100c04100da0b080343c000403c80f2205180c3d00000200380c41e0045511811075100311055621006050001040010880c901c5074140c4942c04001503404004074024140460907280c40351f682d0343d9100d400040d100c1c507156600c01d510041000a48501d005e64048014208000d0500d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 298432544 1250 298431294 298431313
    0x6050601111209060a020c031b10110a060c0201020c031612081306050411060409021201050a060f0509032e0b1804021e06030a06080105060402040303090e131704170604030917 77
    0x3e04080100303c0c00c41990511102c0c145d080d00382b0b203035003141c10780740307031412941c0407031803003122611800140b070010f14481e2604000008107100750192a20440504242da42e40c1256002e42803000c03109940c1113900328040c8000001440c00755040520400101c424a1880040780c1e61b20350040100501c100d03154028656080d100380c4541c0082c05c0945040c0e44e0043c0d40b00144034004031009016800b4078403495101c0c1e8184450b941c04200d80d00c580020f42041e58035101c0c0d9100182c103200c3d22101c0e80040500900c2280f80c01010207402940840d00140c0c01c0000180798028004480b000403503000004441901007401030800e5596946800100d1610090309e00001b00020200d500a46204100719183c420901055000380315075070f04440d040384c0440c80c0601e10354014010070050710640390081a25400a5645101d4008400c1121360000201200610102a4003101d03002409401203400303881380580e03c02840021514002c2d2781503100d005240d480c003900c040620002c01c0c80c1e212140a07000c000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 298433794 1250 298432544 298432549
    0x60f0b191a131d04030206060316050613050402030403030207031b0206090909100c02030d0606110a1416030c090c11121803030408070329070c08090d06050601111209060a020c 77
    0x10f1460854542d1190002402c0ca420003d1814902400092094019541844003850385004030811560162070007600c6130491410040c4a15550313001e6500b050000040104055040d801000c416229444040d5045c08610302e205010380c210750007e400c00c030100b10300420b40c41c00240c0944e00c1408070b41200e03c0b001c285400d04082d030b4409000600582c1c0049406048483d45021b0303000500380300d1801d449409900d50303d1a07591158030304041e0180c0425a070801061005209449445149070040c24101ea5640ba000481101c18840c00b400f0354980000700120314032490240903012580d07402170035003482081b00e2030f003594030155910140c01c4a1140d2140c85031428005800208822030250030510714605204064a0030350b2002c0d994602450890584400900e010a8000483d45005041d62600303280a4005205080880e94004041d10a000400116401a6100b8842a41c0307684461070740303000c85a5940d0100003a0000318005000b5000c3e981407500207403025a1081c03045440c000ca41402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 298435044 1250 298433794 298433819
    0x2030a03030608070603020c03220e0721021c0e0106050d08070506060102030a0c170d06090e160b0406180e130b061806010e010903060f0b191a13 64
    0x40450101c1c1e200d000400c03c9640604c131090040c429030030103501c0c0001c0e0106084c0c5a104a17280b03240d0600c03920044208003d9a907251034007401c40b0101114143c10114809403c00420303640405007020301c0e00349500446264025529900c455004468020004010540143c0720b807a418510665071520700058079070320342c408400302ca0b0164070380507502c0c15582455030420740c4c0280500d040d940304000240525500030410748000d60091002c0064080b664400406071081214011515040c084080343e4a01e107070b8001c0c8200007001c400c0b01c0700004011000a460f0f245440782a400d03000030303c420407501d801011003400b200c40100c5d102c0d200c283c9900e02044940d20641e49003c245461440c020100105158801d40007030f011650b000c030300b0402011582006030001e24650400030b02110381807569020f03c4840e0042d59007d042403003020f804014100c0104049a1464881e10715483d014a02c7c0c07041c16211000d88040500213001c0361800030700e003034ac00c0c1e1000d4400d80c00503100d81c80006084500f103e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 298436294 1250 298435044 298435063
    0x11d0402160b0a090c12030201020d0c0504080d11030a030b040915050613020306030d0f0309061a0118031a07090e040506060108010b0913110702040e0d02071e050415030203 76
    0xc0c1c070344802940d02c2c02c0264070401d00509482081e4070f09051000480c1c175450380002242e1107520b503001065401c1c030301207019026810b001e000144c10503650712443d94000c400b40083c0d81e00201115803030030840c0d03412600c00c041c900070180c2e03603003040001c03031540f52103904001810100a000440e203a400b0340c0d00c402d11020644012210503580f82c1c14440e4500d01101c81400110340030070154118101080001e880c0d0001000c2c050500450300000e0350400e0182c1c1100d21000d420a03802c020750041c018000385181c0c400341906c0d0002d402490461a884001171943e42580d03007140102c4840254085410f001d02000b90009003800005500019001802ca642e070f07110780d20030400391005050602c00504100b0068000c4546424140140540303515814101106c0c04000c0300041a0200d440800e5409403041441c081c8d00641401c0701002780c15000204c80f600307a0229401c60b0301080e0f494402c8042e41d50440a250803c3c106030508101c545815000b86a02c02c00001940540680c0c030703400280740c0405007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 298437544 1250 298436294 298436317
    0x60f15030501150806043305090a12050c0601090c051b070f12050312040314280305040201080f06010201060b030a0c0f0f0207170304052d0a1202011d0402 68
    0x1420302103000f0704100306120042404030010809800c050345c0d00300b810034a620810903e0040388800c0a484003885c103054190800c100720800c0b0a04010741d03619111000a24250303024116a11503000003407062041f50f501000710030291000340d09181e00a4098000349168004100c0c00740040320103403200d049d219086082c1400245070040c030700348202c00d0404a40d840320103018040400e0001281001c012a00484080e5006091907612460180c450196022603e48240008204103003040112540d16022589490101d0f003444070b0b441c412025a042100d0081c005100c800c0400c8a4131900c000301c542184050001013600c2e500d803003803006103410455a80000c6e03a120000305000ca900000322003c3c1000700d140c00c1c0e5000851800280d5102c40a01c40c0061002c074415402070014010320503903010b40030007000e65440d000800315205200c480d10b003220030b6100303911104906925114a28070100c51019407080202215500155900401c1c2c03034104140942c4d41d0b0f15501a5aa00d1000785141e8071807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 298438794 1250 298437544 298437551
    0x4050f0702060105030303070504141f02030a02010513051218100f080a1a06090a03020406030605040b0901020a0905090606190f0f081b13120f0b0a0c0804060f15030501 74
    0x1500002e19003801a40454007a030020414407901c0c507071201c2245c0540703185021801c01e2401100105034100c50803d600c000d03501e406550380320f40a0380403001302607415281c0d0003441151182e205840c4482180240207203558802010507200c0090342d070145c0794003103072024100c58041840002c142c0c2005d2607549a80001c1d10141c00841c05034000c1d4003140c02400240040120550300801c0b00c00c0c64403c580014440e80700460b104010f581c59200e46006141d01410074003890382d607840c0c480040c04041da011a18161205c00056800c0710510a85544981990f150701c842480c00c81400700c21130000c3c5c480d1350451010800c0110440c0394512141030515259240d00d1000301c0b000c0000c203803c90795070380303101003004120a0000c540d46400307010741c00015024505990305403002d00c1c4001402a40c0c0055020081e100c0c0302c400388601c01c00108001406002c65021342e07943d00040d5003c039103008001c200864000804680814559400314008440d01c00000414140c6102c1c0f9808040c904d50044840360344 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 298440044 1250 298438794 298438801
    0x1030303050f040b0f090a1b0609051206161103030711060601030204050d1103010e06100302011e0512041b090b0a06020705010f0c050705061903060f230f04050f 71
    0x6141c40341c5503200d1501c26400d11039040070b0380d9400c0c540c0000740c425a200e00c0c0c00b070301090480c0d4091204a100c507510132036403181100455103d902c17440880c030420011071243e600005407030030030701c10750411031080b84003508982d540c07000404840a02d2840c44800c1026400c00300d0000035003080250300400041d2100308100c0c1d00c1001c011702c0c04500403c2c050406006100c204419220394524010b041d500c20145100d800c0e1140100b8018103283c801034000744184014004405440710080040d68000c0c2c1e509070f000ca0914001c0070325003201c0031100000a50411402403941d90b070501c00e03a003051150f540c90040e91011901420410015007180041700d40e5201600070500d09052540001c01c05070001d003000c1450a00003070f00000c0d410303200b401401050305030f90b01001000d00052007e420014001c030785600d01d4444440800450004040109280c0710010802101810b072000854020702d5005803a441c106a44240c402041e00c411a00040d00422118140d5a98000d0a20031410480b1103092441c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 298441294 1250 298440044 298440047
    0x7060f090c05010327060b09071e080f150103061502240408030402090726180714060706020405040c080f0a0204260f0f010606030e0613020432010303 66
    0x903158049418140717005001c0903082550f15844030000039140c03c0b003000a049041071000707003080d504980c2c0d10070034240400c0040b6420502c0f907540c03400c401c5507410911315910000e841d1208207641480c005080440010080710f643c0b00c1d0080901410306d804504c1541d1107640554283c0b2000310309001d60030203505e49091000d4422402020010654030301071900302038942a00c140f00107000039002d400c1030000502501d000b03116480b02400011001c2d8041c0710502544408000180d95082c1a0200001c8100c24800006810019207240c42401d0401c99009010401103a002101c1150066000e000003e41580d40d8405c940f10310b0044e45032101b25140c1214030900750040103060300d842d68810720050003010080c900c01d81060b0b00070121000c100b21104a01440c000c1d50b8641c110b454417801070355401b0007506400c080115556500c0030b01c8901f2208100c03a88604048a502c0d60200030a41c2c9400035240c1604100840c601d50350440c4d25007c660a81c0d44020b4800e0400b070541c00280704010000c15 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 298442544 1250 298441294 298441313
    0x90311190807080f150406020901260106081509010605031305032208030703050d0506061c090501050702010c0c020d0c0b07060902030709061d060406090c030e0705033007060f09 78
    0xb41310060a019102c8000d00c1100a01c0540050800365021921021a9000c0c83c01040781488a01d510180752008124003c140301090042030001740e08400841c14495014440440000c030080800615a090072003c8070340781c1004058402c6829004040b401081e0305000038044500d89180c10220510030040c011640c20069002c10715550040100002281d804015a80203845110001c1001c0d1078603000201c0d14007c02c1780754a01019000102131103012564406c0742c0d0340c0e01c200028041a0380d1035005900301c0d02400d201c00b0100d100e400d0301070014545104801016481a000c1e040003c1c1c0f600b07018000c0d0341108070215602903583c5038210030b510302001550028444088103000c52070a1031800f00110240b600c5003042580840082005039440f60000405030400760030800446189044c014007401c4000800701860240007004940c0741000b203500034255008041d600400f4103100900b00e40103116005000404206101c140b0014a450199410b0b21190301300104a42642e401e001c0300741c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 298443794 1250 298442544 298442563
    0xf1a0a08030c030a0309151b09050603070504030f020607050610030308010b03010b0403020f011211040f080f06190e0a0b161107060c0507030219170c0109031119080708 74
    0x281d4020702c4a10400c9a000040314410115480c02250912003454500e4940030307400f01e65210141002c03005180c481840020111030841703692444400c0da601d105104151000b9141ca03400500200424008184032249800300c241c40900050320740905034031054140711007540c6030304081c0c0038640100141035111082c1401751191041c440e2941d40b400c0c84141040c42648030080c015945443d80c0c48240c2c0c0a030040401d049070181c0240000100090001e1039039000e4019801059802c0c5001301d64100005102101d41c0c010350700421172601c4404041d80600c030540c2c9100b0714a0f407a41c00350350184d24280042c1000d94800e6802ea5001e050a0120b28045c04040b40210308000038545c484d40c880500180c103104640d91070404906240d20b9042c82810305803a03400280d04110034a55031000c00c80350420f6032003219840010b403204000b11451203038032000440c6400340090b6103054144045246240b000075400002401e40010751401c000c0e460504041350f0140420b600310850401144905010710b00c00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 298445044 1250 298443794 298443809
    0x1031d12030115020f15091501080708071205120c070b040602100e06100302010f022e0b0618090c0910080a1a06030a0c0507050a0803010f0f080d0c03030f1a0a 70
    0x103a02c1340c04c5070b60581e2409440554076a5061100c0807c000e04024041841c031a48070b00c548603059a124034100da0354085a100b4100130740308202e40000c0210000010003000759001d00940702c0c0c6001d18040d400d1a801014060865001d1400c6c001410b03c0d103200101700a00a58000c1c0040700448031041d0121405c80d6402c100a40056040203494044024008240c0e5030900b4401c02d28088400e01b00d00c0d000c0340c105101c41071003d0042a0351300c211510103001c042d080c1c1d01400d11822a441060001d02d02401c0c1d124622100c01c00400304040c83d01d2403d1541c802c00b000007060400d4030071400a0308001203240410040340108043c00440d0005001d0740c04581030352081c280740000c00380c0c0418003a210041c00d0482441d035414072141100e02ca40c085810168200040310840d6901e42402c440c00e610a102c2c00000d001040e1740000c0707501d030801d2090201c0d94981c0240142c07101150b015540103420749022020160389514004100b81280310b1520f6510704403002c1c801c224190030911515a2150700403d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 298446294 1250 298445044 298445053
    0x40c050612041e08120705040504060e010515040501080a090305120109020c07080102031603050a0603021f0e010f0f0e03070f0b0702030c0906031908162f01050901031d1203011502 79
    0x50114145204442c00303981040131403402640d40c0e0301d08587c0380c05290000b50b8082d0a100c40000c900c0744140d80302d0b050b2101102e00360140700500d288291280300d030303100305e42c081050000000c04050f0a40d014020711030282c10f22500c0c04440041c080001e10090b0400c40915034082100030030302104014040103048040021803550804210f17000d00740c982c0c100154201a102d20000b00c0007681500704100841e4082e03d2100c0c0c803104200c28001903000d4040140c0010715420002c40749620441401400c1511500c40c4541000b11020445214610410054045c85140c80c001011a40000030b10010982426220340315081481054146102d1100b103a109034210020f104042d60003062440034011005000e1039219840c3c0b604146a008000300b91740c40e4610101c0c424203105462107066020b82c1902191415080b45044501d40c82000c141380c00e000510501090701a0750090780445842820002c81c5020760245072110b604d01031101ca84011280c4c0d0100040000107400310428030241e10500290 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 298447544 1250 298446294 298446353
    0x10231c142205010e2d010902060f0a02031c0f0e03042121050304030e03030313030807020a05010603050106141c0f14101401081f0203040c05061204 65
    0x41403039014101401607580c80052a00003003080135404104611030702c1e020b690714190010182c050421004a0004082c00b02c40910321042d1818070456095950043c4031604140c400200100c0e2a081300380e07080c09500c42040546202c03561103613550000c078242c00020400030b00400c41c0303000b81c42142140401c00e0344240014000b9441d080c90092218054010300c1c0e038001098140600d210b1045c18950f034854403070101858040f80d0240045105e54040d880e05826483c9141c1070680d02e01c02142d0b00c01d07980030700c0c03c0310b100000e200359016600002113104540c84d08815442d06400c451a42d070084850341e54589003004010744000d00d0402018044036403913a007a00c100313088c50b10448018002010001c01d00516000c101c01c0c1040b0402c1d010040701111601c4c11440c405e800208040d42400d01c4503001100005070850700010104500003c33041a422205e4203212003074007941000d0001c4458042c002d0012401e9140c0b040940690716014400410031708140c00d064070340c160a501c0301c00f100c01c0c01d01040b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 298448794 1250 298447544 298447561
    0x6020c03030319060f030809030d080f1906080304081b0a12082a151609030201110a0204050903031b091804020a0b0a0f030b0a0510231c14 61
    0x50301d0b03100c0081a500f5107000403034400718004003d075822401c00507048502c04000d1200c40b00181040500550894042c44030410040c2c4071064102c0740e00511401240015480c145441071109452081da8070104196803640740031030841d0010741042005a21010100a42e90080b00d0b203480410030584090708818184100c051925900e00e00180c5200400500112542200400c400042d00721655401d40c5140483d8036a880715000d01a68080520402c0032543d40b084500000390803618584580c0483d52a5a0042d10740400c204140710060080196aa01584443c0203052003003030b09802440d500c2c54203a80400440540c0710103120f01c0ca00030701c08001039132035510f603913400403401249040709607480344001441c1040b59040600d80407400305a202800da0852102c101015058a084c800780c01504140705034940b4a100d00c03035010450301128031100e405a08580e10003940c01c05580d055a1360880300842550101d64138241d00d2030215204803600403188079111080080d04500001c0c0d042c10b050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 298450044 1250 298448794 298448797
    0x10b041b050a050c0613030807020601240504080d110d020303060a0e0604150807050109090515010e060c011503170309120a2102040905060603010b0a0815220606020c0303 75
    0x380c82052200019403496400e0046040c0d9880b51507410071103210340f0b0a80c00301c02040b40508011004a035095002c992007500105281c0d041c0c94400309042030350035201425003140400503044000b80601000086000001030040e01c0da8160507440b01003c69110b0445989041514010501150414402d006003540c4003101501118001500700c0300b2a00e13070700001401400042604c074000110040300080504010a112003150000d880b04210184c1d1090380d1000c0d02e00441d109403130900f09580c45072442d030181030b00380000c402c0030381000d04098000d2080760071515000700301201800604005c00c01c011949409282c444400003c030790541c1814601d41d0303070351004101d003840700c0035000c5146c0141c60303c2a0f0106240100002441560b100c2805a560003548980507560a0701e003002c0010707910f407c1c42011a4100ca1407400c60b2491b2010400c0100c03407030705010303003035401c0c12a40b11200640c036a1900e2403902d1150300d10424030306241c1c82801003c200c4050f54462000d540200184401c01d503008030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 298451294 1250 298450044 298450091
    0xa05010903032c061b0105010b0405011b03020109081c2d09080d02270402040e040609060f020703050d0b041808030a06090e0a0302010606032c0f07090e010b04 70
    0x811204000c000a60b00400200b5154143da8000801086100300c4030782c04c01191205e4000140200302c142d0301d03021085043d2045010380f60220b000301454102c2c4480304c0791a070040310302a10000500702c0c0c00f81e8a404055000b118081091250344038107403448074240c42491406046001480051100d1654646a0140305031030558110365500c041014450300b0021569074001020b402c5640e031807008141c0d202c034484080050071001051859081030b05203071080710300303541c10301e80d0508655a45684801c06408581006c81e450b81e183d89410b01710303000e06e0024000c424400d8880035100e1407501412021520000c84a510590504003910403c002e00130b00c076114260080c802c0d0307070b40e80c2da48241c117406045540c0c01400c003145041c1c10320a0a0310040b0b4510880f9219500a1003086c0d03846a0440070384004911342400c2604803404c0d4060b40101903030030311320301c0d4240b070a55509001d0b1600181c02c3c034076a50b0141c4c80b115100d9800c81200c00081c0310303070310849100f124104a00c54914012030080039941 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 298452544 1250 298451294 298451327
    0x2205090d091707150201020c010501050a060c0b1009020414030d08010308090402071b060c12140301090902271b0c0307030f2a210c080904090b010b04050a0501090303 73
    0x30120400ba03102c00c1c04084040d010321400c5003402401000000e0007580901151307c4154607050000c83c1902e002810b0b00c0c1142d074113940d9a4486141912a24982c02010b00110154140c0480c002071002c41c0d0300151004080384203500312802c1001042c98100000c0c150080c0402c04080014000034080e80107403400f000069a0041c0c03611602e150800c01303860301201e00305000700100000121b0584c4609010303500341c4905481c940c5e41c0400e100c15600824100c42041090a0030b10040c0201c0000382c0c030103082d0b907000401c072a4040c01d0380b903142108105122240c0c4103140da00c40411103036079040016204e542e22404025481c11101000242c0c0f240078100008007040b100da200c81c0034041c0704400c005960f1805040303070403550b004106401d00c4050500022915001d03252150402d03002107a010f50a00c1c40d5a4880c0012071100c0d40e51451070390304c004803c65001e82c0d1015440042080c9000c424040e1292215480e41d0f03030309060400c090359606a006a04012104405000080e4040a030282c04100d8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 298453794 1250 298452544 298452569
    0x70f030c05040e010305010b1008040f03030510030b07030f0b011103040311011106010906151e0f0519030f0b030105041e060219080a0b01020f150903092205090d09 72
    0x1420115942d108680c490b6900340d0011001000f400010761180003020003c9400c00709040d42c032081503891140880d07021745000c900206c0030300407a0290304840d608c4101d114240c4085130710790303031029803101054414000280c2d80340502d20707118100c1d1080e90301149003420300c05141c418112605540e803046000c000d01d050250890542035034050220603000ca403855094a0241d0b8450003a03200410071807003811044040d07800808005070007407806000304405c1c03078030340e0224030442030341525090001c01880c0c0420004220040c503e0070200324542c400b60711030381d02140d4201c8854400c0280c50412004610a91504040c800020601081509131450000700b022030031469003040b0700240140450019104800307003034008541e5010b12498461a001ea100304016403001c001203a0724000607070713040c00070740c400e200e80004d420074182816441140c0d18201c038501844440030a03030a4040700d01d104407c001c0f480750b000e00958140196035011412000400308401e0262000f0301c003517901d201c0d0410302e064 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 298455044 1250 298453794 298453811
    0x5090c0d08090409172203150207150501060e210c220609022106090105010c02040b0319030f110304050d02010314430f1b230105070f03 60
    0xc45400c400103003a08854840022159a00d9403501e41c3c0c04900c5007064000e406d440c0d242416039500c00b400981c0c2e045502d0254080f1103d0b02240203501c4140c040c1d8401e44022030380c1c105590301c0d025240c042c04031a95005010448441440441007054003080b1003a281c000c2c8404416400064003009903404940042a10240188652491044010540d10b00c0d082182c04120416540c0090007100b400300f28003580300310440505036030190142c0c0c031580c3c00f04195004010940c400c2c000c0401103400188006003048005c030000307240004d00403020740c1d048000640d0006040d00042d41090784205810030b0f404540c440b600d120344912980c00385d40d1181c403550f07800a0559200c2d5110405020f1505511100d900740100d085110f50000d906c1103070080f01c50300039007040141240c01c402d024211541c1c80304803d207040741c06960400e002480e007400c02c100079002d401c3c1c11442c1c5038107180b0346008105800c10083e550b90220020b4003a0103a41c0071607810002800485680003140e141c44003911b2400065010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 298456294 1250 298455044 298455049
    0x180d0503180a0f0303020114090c030604021e0a08011d0d0c021302041509080d020c0f06030402220e100501031a040804080307050f060906010b19031e020a020105090c0d0809 76
    0x16650341010f504031160a0780401019015072001013030100e00c6c40c1139041959001c8001c1ea45e60349641d43e980c0c058102e2000b040041c1043c0882e00d4654030500c5000d02d0b11030407000030030801c00720303944400004d03916282c080321032200d007000742054120503001900c05240711500181208102c014000c2c0140044000e00c2e061240550544000d0603074402c44000049107484010600500c60045000f80c1c001e07200f082c03601c5400000c480b01008005080c1c101d034840e4000401225820041c81130b6008440c2e00c0690506008045041010100c01b07840000d00c3c003d8405010300c0c1c03402c0e40e000c44001c2e601e0f0400500c049800d25441d2056520380210182d8607a8903440d110f0083e000e01d5000c0303400b500c4041850003c12402084140b000c40e000b0088541943d5480c0b8203542c0e4500a1250780242407007005000b0150105a02d03512042c044c80c1004598501004002110554914030004007558085044c025195082c0952600300c40404000c010000b01c80c00050045152840000c00c00c09001903c0340d86074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 298457544 1250 298456294 298456309
    0x306010e06030a0f060b120f070603180b070921020a090504050a05060c0705060a0203150d210507021206060108061e10020a03090b0f0f0a0c1403180d050318 69
    0x5a40b068400e82c0000e55803429070003401d200071202d0f00c47c048628142083c55000541050320352001c1e4000e01d901c5280610680082c00b500c140215030b102600c1c404804200744842d8240204805d82d01c41900c1c1d4078002c50680c6c0f8000c0004200400b20701c410200c009030740e80140c05425a003503418005a80d49483c50014980380c0162001040f9020711000c005400c4d26803005080d006024805960072592050051000c80c801200e00c079401c070120312086a45400c019608000c3d003482418103003070f09144540c8220320840480c8445c0001100090881c007141461001c90880c000700c0802444182444000601418001000746006441c40c00308a807600501034400c51042034050100c0021a0301404000e403503a4040d80c0680220340002c00c000303110400c04c0700b221080580d1682280c01c2901741040d07400f542c0d00c211f80d0f5500b00040c98042d035020801005503030000c3c02460000795a120a4107400018442d40100103034494218001e81a004c1000481194000b10701509448440c0c1f0f40407002035500d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 298458794 1250 298457544 298457563
    0x4120e0901030b090f151303120608010203190c080a20030c120f010602250819030e03030414060d14070c030e060a051801091508160c020306010e0603 66
    0x4040c000000107005066072480c1c0141d511100b03aa0240100080c20b5a48103a9401c2c0d03004002403910000e0150110a5400850103100b45000055011701c810700710180c1d01030350005045a5070001c00e2115021406000c5241c1107842d0200f4404030a203a0006000351344020000c1d0700c0b1903110703001b80308440d08000c0d12054024402100d82d460b070070100f108554982280d0700c6036a59803121b00c0801e0480d0640e43d2998101e51480e4000c0040360980101020082c400d9410f01200d030102cbd10010807200424000e0341d1909003503c54100c0319940b581801880000131007125806500100300c00d10940054201100103076a040e185250b460382400c11000041c00d1590110101e14801424020003d078001021400704d8003c0d0b0f5103d04070f000050420001c1e21802071a040850801c21100d0701e0141700070350784e106205050503c0c00300310380d07106c548500b1600701d00d8a68000402c038804000410307004036411f00d10309805140c490352010142d03011036550070060050450a240000010384141d40400070780c4035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 298460044 1250 298458794 298458799
    0x3051903060b16060b060f0304060207020102070504060605190f050d0207480b070204051305250807081f09020612011401030b0310090305040e010e06011409010804120e 74
    0x1d880d10f0250504103151141c3e9000c6030841d0905892000720720b0032805403551641d44104903440c1d901e0f103988840c000c2d4096401281580a100d0000900365210f00c90b420040980f510b5582da941811351000c6011020009000180071007030030500a1543e02006582845e540d40400580ea81c0317807800c0c20303640b844c82003031f06090103401c3c060a003000f903560003966411240c01072102080f40001f4030002c4a041d50b035001d1820f04d01d20511403000917140c650001a00f2181008502c0000030f0076456960038042512001504013140c10184010407004d2540103004192003c083e0507401c0c00d21403116210502e480c1103050341400080c800061070080d0340224401d59000301015a41c000c0014647c5442800f4880c826604a0400c15141a54083d02800c005840010060801c035514043e0400081c5007a8805400f044010702010071119035001010340641403a043e4100d40d4900200014541d407600a44461001d5050015034001d0740c10080c12070b0426031204104000099900c000c9500b120151411135 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 298461294 1250 298460044 298460047
    0x2010e0c121f0b011211070227010303030c0933050f0a02070306060504140610050d180210050a1e030b04150503061003020f04051518060108060d03051903060b 70
    0xc4030340c859004005400c0d00b0781743c00742c40c17500400c00300b42251201092640b400b1010003103100145000d4846464a241e04d0f800355140e07081f030080400c0301d41d800340c00403408a0b5841c44c03006603840e00100c00d080104902801c142661a80384030403112403d80200c0c00c01030424540c1c00e11816030140d1706803030b2003401900006881c0d1098100c02903881889110656803245010301c00309842c02c190095580000186030202295110b000078003d0462642d0700260800505000182414055014403812030500c4c0a11806078006130040104211186900c0c03810700c5000c004102d405500b0806000406034800b00da04a00d014000701035020f4200d14504581c4103150a0304411003030096501002944d900380c00b00c071038656401084a2004550b800069800f24042000c65500e02c3c05400181e4086565028418217118500208040c1d52040748560900c2d0341240401003503583c0034482560002088a080f450300c00c2544020301648203402c0200c2e0b05ea00e545001c00c1c3d485001e40c110300000d280e01007009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 298462544 1250 298461294 298461343
    0xa05120705100f030f0c020c010f030e0d030516080103020d06050709051c050c101b11090405031801030207020d0b15061323060f13051306030b0702010e0c12 69
    0x42043e01c4001106011900d0035000e003807842110b201d9404445941c0e0010442030a2880064500c440c65800c03000405440c3c2c01c4210301400c0030300180141864949001c03070301c0d0820302c1d10790018a001d4500c490402c180440100003580d250089201c00710b4100e10000b90303503100c0090440b060446900b00640003100b07150300c0192140b6819840020340c1c0100b0548484440b041c080080c481030080103e400110290314070140303038070081c607020070780c92203103042d8240c030203a60340490140281107030217403241c0c0c1001c02c0c211040004a6001d25403c01c007481c003140b90268690000321450784000e806081070b105000042c24211803d1402a0b003c10001c02c02e03612001050307040515036a0034004d40d5400341600300c2c031000340040b203c0b0030700c1510f000400312420030f84000540110b9402160b515031a8070039130000001d55481c0c0c1e0005004040107404003080c441d0650030a6542000d02610700011a0b2405c0210f054003500850100e0a9500845d1810791259004c1d000070318280300c4104841c2c11040700d0700c0c40e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 298463794 1250 298462544 298462547
    0x15040611040b0a020f0106060801090e1c020a0b01060903030c0b06180414010b0102060c22030c0e0a0b1c11060c0102131d0403020601060f0507051504020a0b0403020a0512070510 78
    0x1078000c041c81d03030f400c070b0f031781d80044810f0103080c4ea5092007250040340300400144104200e5030400010010b0840c1280c0384651002c16000040034422004c0c1d0150b00406543e80c14801058449405041103041203c030740782c610f550003080f27041182c1c0094204242c04005c0342180e41d5040e440040710740f010403444264242400c0c2401c80c0102a044410250700c2d0090b114160b50000c101c0c1d40c49080d0101d250360170082d8040c40c4070a080c0400444400c00038200d070010000030259586040a010040e40c91650ba1419101007000c0f81d801d401e00500c598140385005055110620707039285042d51140e44101010541c0c4046034a034060b4035a0b58905500200701a01c4400d0301e200d2401c2100c0e00d08040c120415030280c011508c043d4250780140050b04800010310402c1e010700c01c0c0f150300c0e100c07600c0e095203420300d070361945410650034041c1c145d400100703c400e000071352400c0d8041c880a001482c0c0402d1a00c3d01d10350004040145c6407060501840d00c1c005041d1511400380000c3c0c0007000c0140101c0c24402c1ea2500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 298465044 1250 298463794 298463797
    0x3020607062c0712150e0f03120702061b09010c02030304050402180306010603020f180303090607140106091107023d080f01050a0509090f030a0507031409010215040611040b 76
    0x22000d00074425038000082c144e1a1100c139042154100c42c25140e5401c9085076400600380c4840410101e2080d40d0030510b03200780402c01031600405e4040c0c04202c03070a012400a050140141821740b52070001d0814401d030b0215003007160f0f5241024245228201c0e5184042400d50240750b00081d441840482c0c2c0c1d05030300112600070442040120103a814907a01d6403420740481c050843d01c005000b20501c664004030039142412140c00303900904485c21305003040005a8241d00201e400c40b0380d42c0d4401d00c2c045041c6424050385014080280342804940c007d440000032074060401d01902c6144038403040c00442c410307441c5007400c0340f59034118081c407449192050603000203201441800100c0102c00031b80a114170b03e8869050b42c80041002582618241c10050b0204024180c0c01c250b0007500d0008001034402c00c000c00032000561200ca40311201030402429000070020030b240c1c1c0d10700c20490000c140c3e07030106428080314243c4021100740d0f200c6040c0704c4014000e582d90403885003800180410074048140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 298466294 1250 298465044 298465121
    0xf180d020a060f06060507080a0903050123130503030c2a010203061e090402040c050d050f060307050315010902160501020414120c031b011211040509180303010302060706 75
    0x4105211000d40801d100d030403954184503c1c400075205010300c7e0001200600103001000c6140341c18030450b9200c1c0c1710300c1c0c21651100243d928050001c011080750100c3c40f5082940122000780c00c466480164540355220320006110240a4400040928201001c255901d0320707540342c1214a2036030050f00f42094000e520646200e84201c560122540b55484204228522450043c1c045d10351134641c2e40c203100103480d41d04014401d01c0070034040c1009403000303032003540d1007411041c0b41c010842c1091802c4c113061607600c1e08803a00a8010604100c403178a13846c0810307411a82070304001039940282d104207200111044070010419400000c0c0065900300c41d40c040134240f07034212540012000780041d0b1300c4c2d231920320390b0980ba010b41000c18000c00400b41400c500b0000c400606011044010019130035040710a00000b10001c440701040501190400082d815030148100c1100502261269074441d503901051200a00c03d9400103401c2c420020076421103000354149040300200380208008840e00002200c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 298467544 1250 298466294 298466303
    0x10080f070602060f01030c050103090204180b1005030127030e0613051906020d03090809031203041202030a091403070306060b0306030f010209010c0201051b03030717130305030f180d020a 82
    0x3000810704c400c1d040c50702181207a90142d8042141864080154003401c202c000c140d90203680c90341603503000c3e0701c00c0c140f01e402e031031054044c0750040c41c160525541c0c014503a0822400faa244c51302102c0078180d40b0101e519100301a2080884100075847d086408036880441207412803000308901003140380503100c0c0000e54204580015082c2500c09a40c1c0448081d403045d60016801000310032030040c065484505581d0060302c4507482c0041ca41c0c04203181451034502001400c40010800060118015180c20814102e102440ca40328111500501014243c0260b1120030503045040c141c642e0308004c0c0794001c42d400b070014440c955440f690069140c00442b0742ca4003d016003944041e81107010710841e0003001c016103a040c3d019520781c00445094008143c4841e4034120301109514984040000d14440c450b10b071348841040e01c80718648544004081c0820304030546c0f0080307100c0002d801c001032341c0d03101c0c271b0718048000583d03100d400541004406284c21a024042c001c81603118940c0815030401076400f5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 298468794 1250 298467544 298467553
    0x207061b090e04020907030b030a08040b0703080a0207050a02090c1c050117010504051c02010e0708010c1d0306010909030c02090f07020d0e090711030409020d020d06060f02100510080f070602 84
    0x40e8460380c52400b80888009510010340c00c001401e15003e40d110703040f09a409000c0b1a1010000d40d540c0c141e0390301175040308981c0302020600804043d0b07c000075a501000c620030550070301103503540f07480e03490341e4804000344500440c0c0c2c0020103450030b040654400140307134140f04c5e000441400741030b0f000b00300a015a050705800700c840c2c0c0c0194601405100e008541c0603000b0412110061401d81b4250410b01010b41155200c070260002204104900f1000e00300c0a03000040c01450750b01c02070003000c52100052072260007421a195640c0d804200581119038071b404c0412400d91600e4201da07038408809009500800d103605105596001c044c9040c494a1b90350211030700228807100a441055001800702d0340851a0703c006a1070510070054100b2510b41038040301e06268a03100c00e070007643c2100140c11031245d40420340c200220218000d400041c01c0070304004250000d035010003525101d41c984801c48040e15407020588902c0f00c080240010200e407001d585640e03280300302068540c00c0520403040107204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 298470044 1250 298468794 298468799
    0x2f09100c0c0510050702150c063301030b13050f0c07050a0221030c030904061203120b12030d050a1d1e01020f030712060807180f0207061b09 62
    0x520300011200d810421001805160404104400c01840c100e002007080500c681001600c0d06166125140c0c45060040c0d10b9581e004041e502d4500c2c010044e0715940b0610010745000c02e03425440980800301c0c0707541014001550001680030707000b040c0004d0380154a000d40402d60001c146e00c400c3c0107802c4400c449030646c40c8c0c001010075a000d4500040e003980c01c100140001440c00c10b80001e40000e605041030143c030703650581581140c011f03c40c900b00f40d4000048002851a10703100300c03405020750200000a0440710780b00100308041d400c9005481a6650000341c2440c0d0742c441d0041d44480d5000d040360b0740c4452244040000c2c100030744150a000307080008480b21010440504c41c0000c9503000200881d2800c100c0c024690040300b040706805540c2001052810401c2200440c807406817511145584980131070400216203440c0d02c031502c10303080040c0c207110041d11008244200e0740b940d6000703d06174020300c00300780003440749080081405140c404104a081112100e8031090070194898103040796 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 298471294 1250 298470044 298470047
    0x1030f0204050a270603050f061e2a0d02070c050411030c0313050d08041a0c030c0913050a090b09060405060c071a01030c090e030405030c01032f0910 66
    0x940d0180359407010103440c051100014581c0b50000c1e0010446440600040042c0c0040843d5170701e0300140c480e5000f00d08241e01000041160641060100200c4442c00442c0b0715000115030003d06244541c41710500950034456001500b4201c140403040d25607036480008120200951000900301e40404c403442c0300003060b01d0284942d8808040c01c00700300e482c41d81e91501411403940010182c00310b62848401010216030100030400c2900500d0f01d0301d0929040c0340c113142d0000c118076a0301c01520b0b01c60f00108040408401d080d40d8001803600d000a8413481d8950014154a044041e8508514031341410040010403603000100c080740150300500607070302c82c40c02150311500b00701c40c060010b40c03000c0041410820098002c1010074051100a05c4480c26620007012403d020390090380e1401c4040810b000003140d500c15081c0d00c94095004501c4d00d4030b0040401d03102c0c0541030784d09040c55956881b000040c03400403005000390800840915010080e0031b812009a08000681e5000e2104094041d0009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 298472544 1250 298471294 298471297
    0xf021617102f0d050405030304061d120d090b1006031b081b04050301090b0720070e04050304050d0503041e050105030a1a030d030902150703050a0e03010204150c0201030f02 76
    0x2a800d0341440c2985005004080c03044200e1003001c082c2000c01c120302a08509903209082c01640b05201940e52410181803140584d1200600b02c0595a12660340400c01a40007a0009030070010b005110303251085050040010a01c0803006401200d43ca410401580d41254400054903410380303081020f40115182214581009500c082c042100d100108021516952200c21140100c05844d481d040c3c840d404a401e440803004100c1c0e0250160042c0845c0c50713008404c403042c0c401c0c0007081054400110005543d2140315100c2c02003501002300110307041c00000d00480d80a481c1c043e2007280101e41d2440c0c00f582d03e520038442d1740e00c101c905118a0751401d1402907054200c80c4141e41d59402c5484e024004001007040c2c0c003030328940300b40400e500e5255031024403603080165410b0318009418841030050222020003a00c07801d0400404101c078a002940000a41d07500e00c40500d00381d0341803d00c3c10013103802441143c0010036240c0d8511010300141d60300c0110151414400c0c0d03424411040e15a01c0c4000307a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 298473794 1250 298472544 298472561
    0x100b180405010b0418121403010902030919080702090610020d03050604020408070b07060c0305060603070e0301090210030f0501080303040f1209030c09020322051f0b09010801060302011b120f02161710 88
    0x107d010030401082045003d0300511341106108081d206508144955980180c4020741c0c1101c80030808100d1006510301748100310f80c880b0064450071100c0741c4030708000391141c41007e00013050540d900c012800948556064501501c111011180590b4896080083c680c02041c0100e8032103048c070300035030725a500c240203c50003030340040e00e024119207039070700151442a503541e21141c16660754021400580e880030300301454003859880c009110001c00d04407a040d1030058200c074201c1c1d8410018003000408560b280035021750000055850907040c108110340100042d070024209426000c030214030b000c12940103502a1034400f1204444000c44408880740b201c2002001d0b007903400c0700182100ca40724100621820ba5101140060584010400951144401c1c1c0080480ba90340300c40c01e10445d40c001501503c000e8049030110b01d108460742c0c80c510000303400b442c030702c00b007003400080840e036035000700005076039050b810b082c450010ba00c440100c01c06c0d0308840d200208074490714020601a81c21840340c204c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 298475044 1250 298473794 298473827
    0x190207030c0f02060d05010f14060c0703030503180a060f0e0d0909200f041406030f061306091a0a1d0406050c07021804020102100b180405010b041812 66
    0x9480307040d40b0303807071a40c100c0b1400907a00403208119148501d42c651041d1400b0380307a04c40601e40610b042c178480000203100b181c030190003000300b00111040c0340300c0000d1000c110ba83c1072030301c2d6a42e80c0d03d21a00b0f07a40505094010085446015501810006e650304091088699109d04000c12114407003400e0380da5036503d54a030042030f5088000d1110150980203462200483e0b000c10341a00b203400d000000c242e00c000e04540c041c04c40450140605518503004240181089408504504046042454101c00941464412101c0e00c4401100000b1a004140100412a42000350343c41c4580e650340c68050007100070740710b600c0f12000820032107401881d586522103e01260125a5900d940703c00c0140406040070000c81414080c41307005030f031040c0000008541416580d5040e0416200183c42c007550030100c0e000441c00e102c0540010b481340d4503640e00c0b541c020f20804907240c44900f440c0740149150b11080f42c020f424840d0400095003081a18000b591003140b03003080c42c0030300803400c036100b044210007035a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 298476294 1250 298475044 298475057
    0x7080306043b0712050f010c0201020a0519170f040c0f1202190314030d0f060b0702090a09080d0207021804120f0909090c05042412060b060a020619020703 68
    0x1020000031524003686545070408980c04240ca940341e4018410254500b160305070b01c011001b084c401c0c020301651002e00381d240002e604094000e00080c0103800740c440c00480001d415001c50410740e1284544581003822421200313500d0421252040c5000000c4a05482d01c140f500400a0402c1420600200b10b494804e100d03d0010200e40c00c0080f4466803031080a20040c02e6100400840c084103055400c115030f80e0000d55459092080381c0b010b5032000c5054409851405400300512100c010445450550403140b02c2280e03134691b40d01400070b02c004a4041e04419001c24003040804c40390380203081d82c50003111807210304640c4000c2e000340b08808580007040e04010350f41d81101680220100c6650a2040c1802110f040d103514441e02107500c3d10000f03a840e281c0740c01080040f81898400e600460100000304400c8945040c5002180c01c600d111702100000c0b50b01615060002c0d036840f41564030b074005c1c14181d8600d680c0c20001d40c0c466041c0c0341c510901b250203201d00d400191a2003143d059590503101d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 298477544 1250 298476294 298476371
    0x206090c060d09020907050715142e0b040f0906050a030b04030212070515130f1b0801021308061014010c0f080d0e06011a0405091b0708030604 63
    0x1c4025089a15181450b0303496000e0301005980d08040f4521036055650f030180c03505110300f000503060380400d01c0d0034441032a1140f0054000420305400f60302c082c10401c0e1442c01503940101c01040815403000399105420f00c50b000c150181104000d0003201e07454100044000e40710881501203412502c41c40d035105840344020000680080107640e4824020700548290360010144050a03602600c01101c0c03940001020080007600d8404458025201c040381610304159a078420b1244e01c04100068101d900d680d5103500301c40481c0d2051006020490000d41d00c6043d020301e0905081500d018824060082c0c20000d10310a924200c3e45040b03c1c046490108240900c5005403004c7e4030003501581d501c0340f038642800101c0c0c080c400400803e0030b02200001c3c8100740310752050074914107801c50004150300c02109d4007009558420b035130a54504403016216915000031030f10104100e41c20b41d00840c040800d5070340c2804000009144180030a540900006035400b00081c20341890034010749032800b510154 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 298478794 1250 298477544 298477549
    0x8010605030a0f02010203070f060905010f110a0c061b0503010806060904020307060f1403090a230706031d06090d020c0307030b130311011a15040e04030c03020709140105100206090c 80
    0x210009036006005988c80c02c90603448100181c10b916100350f811544038400042003000c04d100e00d89044108000802004001030140c4c02c2c18802c0311901c2041050380170744d01c401e0140f59803018500410346088010800c846504c060300540091049541034000c440001384a0b04100a01c503102e903078002c01405c80242003078010384445420720382100820040200c03080c03c178911000114003e80f40e8900902d4031a640f403808120708802c40351207200342d03421030310040150200080d002068680a05010410160061040b240c40e111404098003074400c040600c114000c01140008228082d07609481d0001000018150345281c80d10000b4540480c800008a410a0700000c000c0210b100c1e02d04181231101e020344260035601040744841d00d070504403c2640c640e00c0e020304c0c1401d40e0080303081030fa03041c02d18116140c0d641580c001c0002d401d01080540d03540c00c25100303014500c080c1980d15030807c000c90038460f8942400c1c109001e005e000d4001038035003807070032400021464840c0345944001c00c0100f80040130b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 298480044 1250 298478794 298478813
    0x80a0b0a380313110307091b17060d03030f020711190e0403110c0315060a0501230c0f030a0206101d0610020f240105090114010302070206121f08010605030a 69
    0x13a40e0381d514a0742140626a02030282400038141340074081000b42007442e92041410604c8205014000151002611503021300034042d8410400c680551102c40b09041c150040c1000b03040c1022040d20000b406000c102c4050021407000e907041e42c8410603000c075140441952041c50150314280440b40c400a400240708820018502c500882564408031421011038030300241120780c4003108400004005041c00c20300f10040c01800d00346400c145000c0b021000744820001c800d9005c400e0f910004020105c13141c100309110704450a50120f907a20f606001c4003d4071600700350707482141030030500d0001514082001420302c10404102240f040d0340c68142c00c2014405d001c2140600754018040d40c2c80f50000e040c010b400201c50f100d10b201c0e1045040317504265107420140c009500c100c603c100140300c0c0300b4044566860400b0207080050b031311a00c500004484d4010000605d8145505a040140240c03d1000c403c404044400614010b50b80380d4056038266502c0e405066090b83c00300034080041030082e103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 298481294 1250 298480044 298480081
    0x2031804091118010608090d090909050102070b04050c0102060711060a05100801140f0723030c04050a03060b0910080c15040306050c0c0d0e10080a0b0a3803 69
    0x400400c505402c0a000c0343c6040b81405240e0b07030852100300100445078105001603403180c2c041000e02201d40d8100750262034030100c0d0054011150f0b4031500c0b8000c00c2001d504462811b42c0000391701d012031420345020b60381c544000003134500500440300407511807401004200071901c2c402c0c0140c6019942c1e055402e0003404020f1030040c0e0ba015a64000900c0d00082c17107008107035800c000340b45541d4540302a120f640004080c0200080000102a14070486c001c030060682c4e090241c078910380c0e82c1e25043c240c41c3d0715000300e8001d103501040d1590000b0811840703a0100782c00c101c0a40da020310690740d03022043c0140c40c0070f108424081c1c01080050050380303440e031204121000002c89903810242c89440311400c03103030115516107103910002916120360008104140026840d403034100d030100c041c840444c42030070745041c00c00c00344051003003c16500c0510b5089584031142c05000c80110956039084400341c0c10240c11120300b00b6141000a6044441101c66110b91551010b4002d2454841b0881c0c021980e01c0c44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 298482544 1250 298481294 298481303
    0x605042703140d0b01090b0901020715030b130b011d1e010212210a0603051207140a050d0e030a02090103230703050309090a021e0c01020706060306021201060203180409 74
    0x440d03071440d045940c0b20281101048029002440039924400508045055085880410780034420080140e90010303241d41954903200c100d1006414040042d00074100016003141d102941c424610301c81c0e6070740d41c130291075100d00340c0c1c580d1010364070450360031042c41000413800d41000f5402000156002c44071400c045a04040c4120f0704041144d54145005030003c6e01074031070f22203801ca51504c0c4070404050176900480d030082c0810807280346a81d0140c1c0d400201414029003c000704200301030103e02e0300c5840303c04607044144c802c0c0c41101e05e0700039260711240c0d0044e80420580050303007102d800c0016550f90203a42c00b4040c40e21507400c40e2550b40c01b96070410100f0200080c0e91401e800d1292050051800942c0300c0d80c0159100c0070360004100c10304000074010100144148180d00d02c3c00d0110103e0215400b071030f00d405990f510311031100c030301a10814030701a10440c1000380000801806038010081e020b07000c410810360382d03207594040343c0760702c100307203410b42880c980c0143c66502d80b81c03c3d8002d11005124 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 298483794 1250 298482544 298482557
    0x50609010e04020d05040c1517040c051e0a060c110405100812070302060601030506030a0f0804090e0309040c02070e0a020f070b07050a090e0c04090509070e040c03060605042703 78
    0x1034400207059a0000031110038117030311142400204001000d41001034100000d45101002d0510310080905102070003103041c0107040000314051180702c84501002d000302a0070b1500000c0060100500f0418814945000780c240c0c41c00081e078244106400c40b40603500122801c01d01510320200000303030202414121030012000310016030350100300100b00301200810101c64a600007400c001e400c02c00c004042d141850b00381820080103a501050100c1e9103940007a80800100c0503080c61480341c05680c00440819207000c0001c0880b1000101804900d075084a0030f10030b07404440300032030300c0d18003500c2201c0340482d900010038404c1c402c5401034440c00714113014080c1491a59112825212030030b440e0400859000141046400d44c4006010040c1400040b12040c6007003086403d003647c4a5840360706982030740c42e4081409031806001000040921400e40320007810223080402c10781c0c403a44400c03a0081d15003080040c2600b058090550800c11f00d01c807134001e000002c2c030300d0140c04854450440c204403a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 298485044 1250 298483794 298483817
    0x1a150406050c120c0d090f0f050108130210200f0607210c0903140d0905010e060c010e1e010c0210020a02030903010f06150507120507021c03030f0c050c0705060901 72
    0x5001d02070800c130720a9000070604255460b001070001c9840b0f41040310485001c880500c0b00c546941c0f210011220280781041540c0e4900300584607100c3c04035002540202c1080140107440d920041c00045444484007801c0881022500d40c0c7e40c1e481d50000351100768002600013400d03d03001e0042010103504541d4230b40ea540d14010785144c100c030038241429000c10303902001032041c012a120201628150100100407101445201410350308851050604100d140e400b09855604d520302641c40f8070702d8900c024086e442400368465200c0881d08411145034504102442a2540500401c201e103c02600581a40035104460310060340c022001e04081d480b0410524000761000d20406819010003100025098240484007450008890303588003048002d00c503800108046c0d5100603001d001d40d00700140d86041601c04907015100710003800329030b60100c41e07164043c560990022000404c01c01010000585902c405403901d01031006440c0103580022014822810820010004094141030510b0b040e203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 298486294 1250 298485044 298485073
    0xd0f11060c0307080106030902130c0309020618040e1513060204170c0f0d0206030f09070b04031a0f04030c02010c05120412021203070b0430031a150406050c 69
    0xe005890300551032400000b00400c42d548074090502401c034502d4144940085034002805103c00080a9a400d40c1e862284140540c020f42c0b06e80e210340c0d40540320f03d450303110020071030303409a581407001d9000b0f80c24440d42d0300b07a840011610317a00819800c129143c141e2191900c83c0184185400d04030b0f0480c6e0b0800021503002044042c400b1030945201c02440d16603041400e03c41500d00d5903142c28060020403000c000141d884805590340000d03400c07080e60a0750b40c1c07800640d10f000460b5200100d11000090044244681c05408000100c0b91540c0f8481688036005c56002c04482210040e001484058038207005601ca4250030510601960441d014124a0103d0001c56403117a0301840c29400700b4062001142490b100c02c3d2035030003800b4040c500700443c5440301160540300400c014030303540790743e44900342034501100c41c000e501518240d000e0f80040d403038001400603c0700c02030310324041c1d8101076001d0051400244042e06054000340c00c40c00d051602c1020b0380c1c580c000c219000e01e640035581e9a8903120 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 298487544 1250 298486294 298486303
    0xe1e03010b0603041b0e101403070308030702030a091418042102160b0327010e010c120e070302031c02150a14012301050a02031e0a0f020a02030d0f11 66
    0xc80c000c03105c182c0800c4c0d8181000312282d490b030f80300780d80c1c0c6038200c1c01b046400304100c54214220388101a90a490442c1c0a0000f400c212a0f600010003001021040c860b0250340080540318164403074036500c90207900c860403181000c40c2a18169445400d1859043c0c065200245013600544200400800400001c03410182c462a00da03106006a0040400255907900d42c1b03000b000400c080c03081c4910354103125041c18072413600303000324505080c44c50343c607045420401d500510030300340b51100030480b011651000410501d01c0c1e01c4401182d80c24001100070010001c501d010480e640240100f404030050703160741d2944030001d45180194002e07543c03401e26602c0c0510f103151080384111000185108c050301d4401d08020181c100c6580d8440003141e5103045024200091101a02400d00b16110340901c2001c070b00d10302c9020406500843c44550010328000d104024180c8020705413251840c440900608aa0705e80202002a5050340001c0303050640c2c81c0158242030720107441d407a00245278400f0b84243c6151 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 298488794 1250 298487544 298487551
    0xf011205011502190f0209040203160902090f03010213050f060c060103050c180c0403061109040f0903030513020a0312020102070f03090608100303051b030c070305100c0e1e03010b0603 81
    0x40b5040b00c49010300c62a814401c282540c04100301e0f039a03500b1900d07115103200503001c54000780030301c64010200d01035550400c0322900162001e400580c1003600c5909200183d003151102a000e20301588001c1c4041c038040c0203407001030011000610f1000d1801c020890f000c064181c816800042c00c00c000e2042c030720284509400385000e0710040c03102205800030302901c010a2400b00c2104541c201c00e12912005010440d0100c2e0340226000c10700c12401041a281482801d00c130b1a405450540010a6154585c0080c00541c1c040d407000c102c01d94448444a082c503184030302c0258400302101090000840040c00e04080c81d015100040c01c140c6155074000b0341404250003600821843d1504002c0503600007074580e840101098a48101451550094950300692040803a0801c41c800780b80e005140800030780d42110041002c0320107042c0d50342400d40c0c4515000d0442110b850400030f02c01c030703042d0040241b03005c0c1440107004580c0030847c0c500030240072020400203590654035465150030380da40300c03c0035600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 298490044 1250 298488794 298488809
    0x113a060618060314010908030a05040309050d0506061003060f03031202131706010f05060a0507381803190302120103080d0507020c06042c0405060708070507020904020f01120501 78
    0x1901c80c2141010300e413050740703403040200c2603042c001030f08000b8041d0300a0700d8012800d404041080e86441c079055400400a822054000314072030000001c1c444006003150080d00165090b0b01c0b0302242030000c4042e9040c1d406810842e0042a03801c00004c0d1158100c020094a070210041c2404042d9a00302e003188150760007100303460200845264454014407046006261702c040c441500c0317140c40d02240035800789030101c40901c003000c074641c0c0520242100d03140c14020302c0c1700c3da1b001480c3c80b00c0d10400311907625400144926030490015114243c21154221840c0800300110b051042c55a087d56141c00070054010400d0307020300c20b03505c5480a10203000d020314801c2d0049030311400b8080a600885030002c0c1550219401001c250000d82c4484088130107540c001074110002007040340780c5c015014400180d55091210000070002440004100c03680261015902c038450307502c40540c02c43c0d5500a460000c0d61001469001c14010f24142003107450754801810001440080c03104400102c4100760320510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 298491294 1250 298490044 298490051
    0x71b06210623100f0206010306020306040b030106080105100801140c1b0a060b040c05070218270601032102121c0e0703030806040905030708030a0216113a060618 71
    0x20820b01e4030008000c3d0300c0e00d4a25041c81c4c580040b40f0300941c1c03003806100240000e9400004680c403911035410030380c0100700141c001e00c880d0f540d9001c55402000200d036041e80e100b5032210042180401809a10100456208000c2a42e111007080140d1948000d10380d141c200031081c041c0703648001c01d0100503915409800c00184c42201e4905010503918800500b03130130080c2c01c02040740140e950b025064100a00560695001d607140400427038412034503e08449141a00c0d842580203810006030203050700c1c03080061030f60240400400c0c9048001d01000040503810083c03100d5180c0031490080c103075410500042d0545002990300900445460400c1001c070317600110424424560401c40850f0001d40c140c0e03080000301c3e906d4a03500c0e00c81c005c0d0300005100710300010201d540c000064054444c0d030040300341d44401c41c16030f6103840c0e1010b207504012217000d40030300c6503620070442d14040300040030020b441c0da51030340c0143c51001503445651800210348055441c207020072504031b201c0841208605144001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 298492544 1250 298491294 298491359
    0x180f040c05450a06050406021c12141504110a030b1c0b040302010c08012306091207060e0906010c1b0306020d061a040b070219030f08071b062106 64
    0x4070804095030003604c1032001c01c00003040398a40c00241d6400c02c2140d40d44a9000000a1008540080710079081104640c2010a01690960b960244078082c200340305d49080c1d800e0005c1c2c280403d440c0814900c0c204240e040c092546524060b0300019001c980003400e802c186414070000081240d400d10050340da0070f00301e07402c2200f0150244240070503000181002485907150150304040000ca4072070b0082d01180404505c80c1c144c0b1180c098441c104402000520401a00308034140e41e00c0c020311481d00082c880140725096800c0040c0039602516040e580c06c11045000e865610050669101c0c5802910708020000041485d61000c1e0501110510380032411a203480c1300c450a000d41c40026140d480c204000410841c0240e078100c8012a9040e502c0d00081058141003150031842c903800540111982c0703030180b08002d884001014080e114040c10995580a142905c6206a09018100204400080e2010010281c1d209000e03090909000400d1190321081103189089501c1d881c0c0c01c480380d0502d882e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 298493794 1250 298492544 298492549
    0xc0f0515150a030210030c050d0606030c02070e040804171005090d0215090601030b06060c010204060c12050c0d08130c0e070e0603040809130603050102180f040c0545 73
    0x205607a00c401102e45540003801e54001a560301c0c44442181c003415607404005071000d0241081d00c00c0c2101c0d03464100305032a43c40740064064000348500c5070050007810f20200380c40e21041401c1c0e0144d0740049110303040a0030b28000c51000c04084030401c000d4481c00280c2400c0030f240c0d000b042e200351000303400303440c504150180191400c00b40501d080c0001030710104104c16240d001416038112078200051503000d886643c007040c103511424501c076442e5400050b012420540013545030f004d2905c903002014020980b414101c901e405171444481c07481c1c01011043e040b40348102545504244180a00c00303800304140c0d00e24240110641c041e00d407060f2400d040042d01504244801c20382d0109a829914618041d80c62850500c54500040e10680b04034004c811f02104c540c0c00080a140e0040086507a0508035030182d140f0841c4500d00c80c440c60100740118454200b0b03025001e0422507584030039080507001c0301003151546000d05c242003d400401941c08075114001c40c0c2c141c202d5604019406200240c20a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 298495044 1250 298493794 298493821
    0x1031211100618090510090c0b031e0112150b03100603061d0105060108072304090506040b01020d0e060f0c0304170f010504020907120908030c04170f0d0c0f0515 71
    0x3100005649004c2c0b64401041020820800c40b92503880c2c0054281c0700c0340790009080100c4c3c1c02074000680d010081001801c01d190300b44c0c505078603004c00c4415907a60f4a104684403210905c0050283c000109842c1c0005165040700c050000001c01f5907604130700b01e04d0310305c0031034045600c00c1d10000d403940310784001003520301d000103c40c00c0c45400034015880c00ca03001070900c401c060041010800c00500c2044248043c100c00d1a04501503c01c466031a5900e040f42400303048240c850610a51a00c0030b110724035800020200304070b01c039945035500303901e0807001040a04d40000c0d65810b140b0004001e4030b25185000d00040016184402d2000c1e1f106811401700d6107064010310a08001703a140200340400351759040740740c60381712026151000c286440203001c7c1e0050410044000c1c005c00002c0300b800741c1005003501030002c0d00d24800c40c1175443c44404d404290744102181100035030390000c3d4070a0403d6882525240819400b44654403040c03002980e9241c60f1126500c1c001e851440c00c030017888031030000d081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 298496294 1250 298495044 298495079
    0x20f010c200307030c080309100510031109010e280c020a03090f030b010302120102190806010f050f0f0a170a0603030e0607031d040906060b0703030c1106010312111006 74
    0x3070085051035219074001c1e11108a000c0050318070340300813000610078281000f1800c207044000e5800c1c8014203081c200300a070711000303001c00ca942c00c0400500c0800f82c02c1c0810050704a030352202c41c000954a8680c1c90054040c82c00e02c0c51407003c1d0514070b03141d003084058000c040c00c0c109164020f1181190380d04005040d15460341201c4000c1c12440c1c002c1000c43c120165107170540c0e030103c03000b030030000308004524024407038a5003800c41002c4002d4107030b40c0b1030b03084160948034a81c00e03290b4151032925000308460510a2106884900d041482100102003c0ca4060182d0009900703003680070305505222151f11840c01c6030f1800300141c48032018810150310418401070081c00b0f4030427a0410506a50107440d10300f810000c064446000c21007078946541d030b80c110741e0030b00d43c00c20801c0080039202d8021142c9540004815000300341480300c0d803000719100d04010007000680300050400c5900710303601d00f0300c8445c0000050b81002512405c0380e41640e028422003211600b0340300300043c0903103003241d41c50008a029 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 298497544 1250 298496294 298496357
    0xe0d050a0b220314250b01090207030507060b0f03120d1d0607080a0227150c07120f1401020d141306020702041116032304030b07020f010c 61
    0x181409840c50030514580c0c0b86240d85400c02c0701003082c001d4540002d600400604e0030031400c1280c5203443c45c036804010509004d00410801040f81c1e00c8050600c01d81c858480c004002a10400040021403055807203036010301d07001402400802d003904006407a00391402904082780e040014205804000f0740b0800d0700c81c20010086d55020004400c03001d4413004020050028807010340f00044140c80154111015421300c101c0c80c00208222000481c00d080c10012180c0c010550407980b4080441c0b000306480340001c40e02c00810519040a60460200c1c0b0080011216485103444040000d0100c0c0100d01602491000058440701c0c07003240c2e90156601005000381030b0442c8004d04c1000c0c240e0700101140681c0240c4e0150b62402c89101003001004c01c408000118480400c641d608048200d261324415400b982d500309403801c25000c86182245580400c01100300d017000100001409505210b51221140c0160780494094003d03076070940325000c86d1100011810364880b48000e40c0240b40c0c03010380c03505 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 298498794 1250 298497544 298497571
    0x70206090706050318070b2101050904020d02101101050420100e010309020d08040803030105130203090304180e0a0503090406080f031806070606091a0301020702011e0e0d050a0b 78
    0xa0a001030b00520014000440d060224011542845020404440140b038050b5565a44860b08030528000009000923083c0c90032546000142c2c1e0b03d400b42d9124001c5800400e0940014220350030030a84044440700d020030300140b801c001541c80000c0c03040f24030550158203404120401d01c0303022010003100c00100d43c468a00240d07400b90041d44840c01041c030380000e0800058098260000074100c06001200a05040b00080c0100d04c000380440614122081905c041748003100010350b0300282c5c001102c4004540c0d000780010002520405e11445012060060004500640010103414055540020b0ba5180d00014103a5001d007480d00ca030700001c045101c00780421803256a103054a0748202c0c401030501d156414001d2501e03030356460881d4203441e0b005200304655039031100d131030002e082044003d05d180041c000d0342001e18181030086404a581c16074070003d00f6005019810501c400074481b000130841c42c0701d410b49030b075220142e500b00514011002421031110701d1034418440500180b00d418a03481 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 298500044 1250 298498794 298498799
    0xa051614071a0a080604180203120c160b0f030a1b03090201110c090408090117100812040302090621070608061f05030f190f0e06070e011d0d0b0c030702060907 70
    0x14481340e180e030441d5080f81c012808198000602c5025108143d01a501d0f01a24641070390f03007010280200400341c1020140d6200d044000201d080c0c08045100b503011100003040651000c1c1c1e0b0440c02958403405070b00740000c4011030360030540c200c010015444000b03e40d84032041402d540c1c1121440c4c4051194000070041b070865540412040000a00000c00400b404103510580360f005264410a520820500018615000c41c04035201201c5210b60441c2c2c0c003400d1120262010b542e02100c2c280d9401418000746070701d66400780441a50592401d82420b41052852000f140e0188004001041e8035660494503040140c20003039240044c80b04511440c9280e8440c840d125080019a540309050b40600d01d044c0c0d071200111000e0700c1d1215580c0304003d1034120285416585503000c0200119a034048402c41e50b110801500c0610b10303481228040f82d0f610003030702d40741000403030513017810100a4082902004070390740b02d070210801512070342c1040070080108000140e042000c10f52240711040201750151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 298501294 1250 298500044 298500047
    0x1020c041104262a010906140310051504050f0a0e040f0620070302010c08010b090411090d03050c161409040201020c0a0303120605150a051614071a0a 66
    0x3156205541d600071400000c41c0741d00d561110801c1441c4049000d4540f0001340c411062162405100412070340800461505076552040040c1c6055601c69115403000c9100b280300d007501500000c3c0804541c444c0750a0206980d00c2c4c413408070301050000711045850b107080904000d0803281c541c0c1c905001b00050308040003c51064a621a0003981001584164032aa81003000c054407180c204003c14100c1c0b038100403490f2054500910801d03000394000c2204d04428079088030303501c0c001e100b450312044003485043d0b040c1c40c0c01d0707010450700c100c400c032214039007005000891405100c0d00c8e8107401098003c80d08185242082c084003c480341c0010110901c0e6081c0300d010243c443c00e5212440c00707400c01c0d00c00141164000c05c401c00c0301140040139410b41607981c0c0b5000306000061087c42310754500386900000c1300c0c144540080600303c83c1e400e117036042442640c012981e68003c4503113425090307800310700c0401103940c0d5108040c00e00740503800b4103a801e060500e920a05400080820580c0b08100f1084070100e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 298502544 1250 298501294 298501297
    0x2205010c08061c0f0f08040e0108070e0903070309060f03140a0e0d080709060320070609060b01090506030123090405011b08010e0412020f01020c01021b0601080a0b0a06030c030f0201020c0411 84
    0x1940e000184c0071240f00e05d402d1408250007140c014000c100001c0001140300ca80000341c0e0703002c03548104120441903490707151080d01d038010010003c1c007080e0b201c40144402406455912680140c40c40c0007d442c0a0119114848040c151114980c055a400314500c0002c81485555802056070500e29039a0402c0b034801029624503110314400c16503200d80c030405a80d0b00f50100c024906040c8410340d225216410110000d12409004588040ca1704403500003650140e0400012241c4c01012507086038038224054200c110a14582a082c42d10340700701070780d00ea48800015020301e00071000000d21103c41216440000554801c1c0401d000e070400040001c3c00b20030140c99449940308001405c0300f05540c00913890f1402601c2e08048550022810000d150300560180c06204a221110100c0d19540700066803906030a004680880e000802c010010801d841c40b036641000c000f21002642035643e8a4200c11040c0b00e8104807109507d0602170020b660381040316002e4614112410856400c0380003520845 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 298503794 1250 298502544 298502573
    0x50102070b0a1211040303080a1b0c0311010b04090b0f0705030c160201020111030112020a05060705060f0702120d0227011e030603020411040e1e2205010c08061c 71
    0x4001000310f0483c5912065040262080c060402a648443e101d103006400300304c04803a050031482c03800f120320302d03428410540c1243c2c1300300c1c6840c2e401841c441a10708880c842080d00a220080d901da040030640ca0300da5100d00742c0e0142c0644441c008509003080d190189000140003001002400d0003030102c58142001201d5010141213000ba640e44c1c014401030f4003401c1400b0320b0342c07103000002c40006455101011103070f0003244211108000c0540b110100900ac0c040e000018117030340d00404c0001c8104d000410410381101880c0101c47d1a064021501c41c1d0710b80c00303803200d01003141c0c0115900040c880150025107286011b01c2011003556180c45c0020000402d90030030701680d104280040044500aa00c030001850300a00b082c421070351400e118150030b520522803c0786145800c0000344010a403426030700016000710010308416214103103041017842d01603071031315426804030070f4900c00140248a00c03840d81c400c546515010b494186c2c01c00c40b101d88188170040d292102c0c00c410500144400020a44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 298505044 1250 298503794 298503797
    0x140a050c06030718060207050f0108010b030f0c0c0d05070c082b0302040509040f1b030b04120e0402031e07020304080a0b09071503050402041109060714030f070c080601050102070b0a 80
    0x8890f0b40b400000c5602420768031500a2184100401040c0f1603800318200003a29030a89448903c64000001100c4072202485034800703948003400450107031201407503800d070404800c45500741401140d10700b040c10a0020000792020440c001500300c1000700243c1078000070184200500703011b02000038180d440d003006091517500c090300c244080012074040d03816100904406015003100f8071b001d180c100900840c0400076501002030840e00c4040e40c1c0702c44405400e40750f0101020784140c50703581c0e499003141c203d07460030424032003180d41454a64982d072000d14031a11012484203070a4201c0c0415030407166000d405002150810041070042d0500000d032485110343c1b0409560940e40c1c3c41d50f80500344001030300520341e41000f0781401c455140d81504014080c50007100c041004182d0514120b085106030b42446030498002d120490100303280040101000c01c1e44016280b03401c02c001d421140c55808600308541011f4060018800700354204080c60140c4420f000901d00f4500348000c4003c81d000b184400170 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 298506294 1250 298505044 298505047
    0x51311061603050409050c0f07030c020a0306051f1401020d050309070e0103030c030806090403210f05010f0e010905060a030f0c030605152823030f0604140a050c06 72
    0x5864850404030341c0c1d60424001140801121481c00520a5203e841903d1580c3c1c14003012500c0a820b070001c98805020102d2005d240040a503001d82d980b83e42420281d81c40200c4a02c000301058080c080d4070702c51900c850b000400c0ba110021081c68000c21504061a0080c41e040c150b00140d13000161aa0f04480d10b0400544039604d1101c464500100780c0c01a000f800300340c0d0000001c06403c80c40c540075152094980e51103d94610301448405001150045d0000d440601d143c041d030420461500ca074107048400100f01841419402400c0d62402e0380000d0001d1070304282005180070324003145002d045010010301c10350a00c5400110100154003001d00f114029152400402c04030702c007014001c50344114180994a013081c40421007403001e558481c0654100c0d80154094203448100c600229021003000c1d1045040580c0d000040c5c0341d40e400c0740c0001c20010520301495030104410000303040341a008168618062030210b05465512241d000540d00041080000910200d580c101440082d40c503103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 298507544 1250 298506294 298506323
    0xf090209031c020319030b15030703020c0a050c0307080604020f040b1f030204090c0c0507090506130207060606031d0a1e0204020307080f0c1e070c0b0a03090c05040513 74
    0x90070254008441180b40300c0c1140801a401c0d0040f000d49480c14403e210582a05002c6405405544000350440c4d030000e03070064010b0010954501079900134400d460011f0414008203000743c604a8001e100381c4944d4800004807200c0d00e000c21148000c0c201d4800502070a04117079000c0b071071869261809034401c0e5201d40c00142035841d60b107080ca102e592209104020813031000f00103002540603000740e140302400c002c205603500703000d43d10700104584d103c0c2c000d014a80c6000c000740d00820000c1c050302d03072042d854030200c190300d1494005040100d00800e00051018603051000d012948801e66101039444608079404141c00c0c0031884078100e54100d1004103081c4034800102c407101032174040007503000740b001c410b03c0351840d170004225209140300c40c070348011034540d5540c141e00c41c00780700b580400110f00d4004044d00915001f014080c5240300342c60011036291650003038140754124a10b240001703a523501c00d0b00207201206005400802c81a20200b2103801c01000c0c102c071404400c000540340b1011005071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 298508794 1250 298507544 298507549
    0x11030702240307050702030601090c0c0b0406150f08010e07030302030f13030f0f02040e06151c020a1508060d08030c09011e020109060e0304260f01111b070f090209 72
    0x3010703080890544030664030f2a0101c030241040c0c11031070007039002c3c1c4101d00c004103d81d8001d226200889030b00c0d444000304c48110f03a541003100b040041088034142d4481407100d5440701e090759890040d1a00018a01c902c07414040702900312001908448101d5110100801c00300f40c003c0105c40741c107001c1c6102c107070382c8501a104855441280e640f00401420f210001007043c040c46a200d00e4445200f12400c0c40801d44968801d80d486600303407940e20205241c1b042c40c1c0d14905d0310056068400100a40c241e605a05580001d119103d181d807105907c141da0303003160b1580c0380d404000f2540c08001207070400014000c5448034950342c080202182c0c00b1030310004044030725038040c13a2840c0d0129039082261040755400031000340a040702c000c081381c0c1c1d2428404070802d024008410341e0103854508580c21051483d5199000c00d00d990086000000cac040c103441003109001c06c1c05000480e4000c4050699540b0f50300e030b403905c00804500c1030904203401900090100b00d06840c030000c12102000009a11040410f00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 298510044 1250 298508794 298508839
    0x14010609050d050718060509130309120218070206060315010308030a1e0c23070809061c06081605010f020c0907020102120a0f050c07031407030e030d020f0d11030702 73
    0x71581e0404000d601030116070380170341c00007016104252000c3c0309940715260401d00c40320341d0100c0100454202c05d000d00112000011043c03000340010a2a50000381ca90a0164184010b40c2c1600068001c0d0040102605040103e501d00d201c030081c2c28100307989161250ba8007400040e004606690b10b4103050641d2401c2d00c26000c0740c215005504001c04070141074080d000420700c3c4c0d040c49104802070010030b14016188151a1802c2d04502c009107810001000c02410b5800f1803078100242c40410402d88004425210701e0780580700820052030310100081a15040d032019600050400c000c2d282945003c65010400c690619800d58500c1c240ea1500c2000740d000e401a2440a43d002d0180c80402845d114160098000e180c00d4080410140d00c2d060030701d1105228401d0f0283c00b1400d405071040d079024640c0014800381d402864481c0420706102e002a042c0741d90320203413200580c4030700020302a00b2418010601400c1705c43c103220740210151000c2036113900444402038880c5e5440e41c3da100000c2c100c80c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 298511294 1250 298510044 298510049
    0x30b0a0b0409080c0706020105070e0a0b03101a0a020106090c0f0f02240609011205030403030c0c03020604260c100507290103062906090f06040909020414010609050d0507 75
    0x400d115115141513006079500e466a01c201001503080002007543e030790241e4020441e9400142281490074205003804182d030340060f00140b540b480703503540000c101211985032524800b4120180e41e0345d0b806158001d0940c0d21a40121800a00d06100080c0503500207002c1c1c0044003050070880d002812542c0d0076410700c4207003030b0341b2090000c001204240c61158400399a20600d011580c0100c0d130f90702d41030302908031404618000c190b03510802050003c01d000312404030083d40b003070b1480841c00342c80341e000c12000d0304281d2140c108180324140c515920a1072020b0010881c1c01e03007000b8076020101a0015011101030185101406030005d4034000384100c0f0216600440c44d00c0303454140c2480e8007041a00031050910054406034503203102036115003c132075107451400b17079242603044201e0300d01e0702003104c0c81d8001300c1080ea10140503940030101c5c0d11010050f01c0100f8580d90001043c142a00520055840360024500302503201c1c0c0040c444a41c00c236040344165401681d040380d90300388a2070010b15080c1e294 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 298512544 1250 298511294 298511303
    0x20d061b05090a12050304030b090f0d03020304021c02061c0e06010f03030f0801180f020903011103150603061309030c0c080703030f1107030213060b0f0c011401030b0a0b0409 77
    0x102210080a4021000b03240c142d00640b107404070181d84100100c005428104001d005400c01c0004002051115140c40d40200a2178169640c6d050302020852038400044400ca004c20380100800017075150103030f48401c110073340e0318240140c0042070740042c003a441401031410345800020740440c2034104d1540f00d098000b0000c0101d6920b5615510b0b8402c0e180110b100440025942c1242c004a5504c1100e003107040b1a41644000e21031503003d00081c0c05448138080b0201407a50134800c1810903a001d01a400510210303000c003a40d030b41000206084d4a0450030300c200e001340c00420510485444251100380e0141c2e40c40340004030b0007800d01c1c040356074500741e50b0003414040c4000c0c004110700300701090001c100d91090711500c0d150131000c0b005603112200c80c004001c40f60011441000942440d0051982d9050481d00014103580c54200c12460394005003440382c00110045052080b01c4000d00c200810400190540401c3d5890355580310380c40c0700000c20014540d500c0303540c00d05c5142ca403500710b0842554003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 298513794 1250 298512544 298512581
    0x207060504140105060d1a04021507031701120c030204050408130609061206030f02122a10110634050a08071409010c05030d02040f1d0112020d06 64
    0x6402d1403881c106800709214515440c1502103580d5140c1512031052456124041038109000b180209019000c024400e91304004a03040400d1a00314040081c0b00d00d500c00d454480d800d07404829820b8002e401604103180e40001e1402500214069002030760440ba0704550114071941c4524208045004460030b02003890001400411941d070040030700c00c156541c950340d503d40b0800c031503554425144240300281a840000c003d241c00b608003016110b102d9500345007184c11b180714402190064151100e0ba4072074190004030010924030703040c014405a075035546400641b00064808060300c0e42805804124040781d4480916404c2001d81055441082c619000000d0601c1c4290b014015034401c0e26400c1c00601c042e00003c0f01c1034041d40502400728039140500d420000310b03a006403070b495185003055465110501000108002900040c0061700f1000481d511107450300110005100000f5544c040c0741005100500c414042554056442c039011540c0088200305400d02100800c40c0c5642000744224 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 298515044 1250 298513794 298513801
    0xa150b100f0215010509010e18160e01080a2310020409020a030b10020601090c1e0c03020d050c0a0f020619030615020a0f020f150c070e090a020a090c0302070605 71
    0x4101d10400410800358081d40d045038016115035075145000d001c0d4a0b0320241200042c40001405265560701020030207124500011700020f80c2e142c542c101d80040c102aa0640040c0322000d0401d11550040104a0051070005055900d00b0f2003541c04201c14001c51040003c21007800c0c1d000c21000300b20741000442107607a25107400010002c2d44c4442060380100f81455031610007800c3c1740903054000040c2d603010300b1099003031512400c0640300c40481e0340100310b440c41d410f451001041c60000c0b0000c0c119141e044030a040c5150203801c00ae907071001d08041c40700912100400d6207012801581d0158008103a001c0e81c2c80620008890380a20007400010280d0010281c0d8150707050751048041d90980d410f603100300d00080318126500c0c1d400d21001400c0c4200541c0100050406020101c4039040092441000d613480c0c2c4482c0340581c108400c12140356100502c20464040c0c1500100e40004d06400600080b100c19008900461104c3c818030400750b81d906c10701041c080c406d905a5416980c03280b0203110034203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 298516294 1250 298515044 298515047
    0xd020a0b0403210e01020d0e0a03081803010e160b071a2e0b0403080d021213021836010c050c0c040b0d110112020304051506030f0a150b10 61
    0xc01c3c05403007041c00c1211425110314003440e0341c1c0d1030601059005100000d1b00071007c80301c0071001801c03585c00c0344500d84040000380e0340601800c2c0c28a40c00601407085c03c1030314209800d42d9064603034000d068000c40c0c0a60341c00104c0c1c06451040c0c54500e526182c0d1070300e0f130f0301d403200b00e19000c8440c0803105042c2105000701481905078070004144240007110300795034405024181d81809204419044038104400c000090348c2602400203a43c684100509005082580c7e1000d0031b021960b0640100318000d28030708524000b412843d03540c3d124900100e1601d040204d0011900d1130941c2c0c4072404250340c8000f20080307849510200c0c0d00e00c0c410005d10000d4400100604150030210700e0565500610308040c00d542030501c209040303071000030842001030f2280e44840c5074049020030b8142c1003251200016015035801e000a41c0514132450080c00100309100e411070140c079010b01564401d4000324012030001c070001548101d15a0410f90101c110112070030050006c3c450001c44a41041084c150844001e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 298517544 1250 298516294 298516313
    0xc0c0913050c090907060804020303120403020a0b0c03040c0611100e070f090513030507030207031211060f3c010b130807180209060d090b070909051003020d020a0b0403 74
    0xc520035421590701c012a41d04000340e543d41110246104d83c02134008009013446044056009800541920315120070581c450030020811101900564442407003a01000000c10541f54001213030440c042c1142082e90300c0800380501c512503002040134600201e0f822b8401800410f442508481d0b04106c411700d01303c441503c0d017895200b001407101c441240001e0124950190600c5a9070401d40041110f00655080e9155045002c060701140301303602e001310024150400c8224a052144c880100e1070308116240341ca0b025000f070100b401c4090031428005040020b4060784d684010207400d4049841c0080d220848002881c9442d46941e980d0100000301421004010403829060417031820140d501d40c1c09403a40c40e0788c9446089550b58848098540008007580034142d26540100480e14202107500302c0010380f0030104c41624100c000100340300000303401030ba120300104a040020310440c5810111030140d00140d200103401540300d100080215520902160003034200f0b4001141c40b10b40b00d04088898 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 298518794 1250 298517544 298517581
    0x50702060c0601140f0904051c0903060e0610150207140402120c033903180a150606020d120903030b03191712150301061503020702030601050603011a0c0c09 69
    0x400d0043e9003640c003811b04120b01440340e0f821000510f0329035400c2103000281d03010b105036441005070214000c07001400500444035150344440c0207240d83d0070300710840c89085032a5403249158074410781054980e5900420407104888406c0145198028510080384c00b900c65090f40c1c02c8035481810400c42c04c421440c004c4c502440107246da80003000e0000044c02400002d9a40780131f07103030056a0940d42041040f4005540c048000138100ba0f80d040c039420468544641100100c0342007140c560303d86c50006842c41080003c201500c000c00780d400ad4100080c02e007440c12441201c1030380c0c48080d0403043c580a43c00c400000b04028023180d04405c1e2480310030806a09a9004441d0030291800d60411152480c00756001002a078203081120780b5468244007072560810000c076010b540b1084005051070352840b103d1a032911035200581e850490788109424000140c102c10f11400c0c00b840180042c500742060548007000d642480d940c0d039001a50705038030304605141c44503840703900b000800801c02d1885030000794 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 298520044 1250 298518794 298518799
    0x12050604110301050f0117030403060504080d051f0501050d0b060403141c0512060f130c12020c03040506030403090306181110080622060e01060f0f0e01050702060c060114 75
    0x700c24008208240c240c880c20307280002480440e10050000103d00840c10920100316812285042d42d40ea03601400c0d642c0c116402d0700c141e400401c02d03c140780d40760300509078080001031103403844101c0c2d00000041c0c00c01500420303042043c04500900980920741c005522038900a01603900d9680d01d25104810649502280d00b0f07038010300980c1800394020150400301030503d9101d250820a4441509941c2d07240200b08a62008460184015a4580003207810038809403100200c0c04092085014001d90f4201204240c0c070351041148041074076010060741c081e1030044503280da0300d803500d00b0308941482c1203810190040b8980404c814007a0f00c1c43c034500071068481d004461410b6000f030208881c0c1210309545c0b1000c0b4080c803000403603a1402c2e007101800e442801d0000c5034441a90807400c0221002904103842d40c092240c014407000d604203543c045940340d0b924100782045915600200f2000241400c207050003804101c0d1000c43d80d94601355030704d09034004110f0f225076a440c11240d07021403100d0070072030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 298521294 1250 298520044 298520063
    0x90409080f09190303090302090a020909071d030705090429070c03090905060d0b0a092001030e0a1a07120f061505040e040807170c07030c050a1508090712050604 71
    0x22031081e94030b103c481107079003540312105403e146400b1710100800040010590030340c00c2128540355610080c48034002c8d01e0703540d40c104a400340071141104001030408018440d9005100400007070783c40c800250742c010307800504004e007044a030109038481c51105078010300d203d44d158108280315034480c02400096001e640ca1810050755092f20808890040c4d4078980c20860701201e0701d01141050f115a504403004020000c2c4000580c2c40fa4107105400c010009000034039400d9040056a01d402200c0303207424418082c1002468903601d41401c4448030310b103a0000209400003d0140d80183c0c04000d03642103800003031082480e01c000305001040740d40940302541421300c0c105050944250103035015522045c03404e50050300c55803a00d00d99604000c038120341d1719224500c1d04500e010201c02414181100100400310130f0304500d03160a4025040d00558040e800750300041200020003d03249860712414100420283c0350a0221810500e464200300f10040f94001030000b004000908644154090340c0b009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 298522544 1250 298521294 298521319
    0x1403060109020c0316020a050301140103060c0e090412140a02010e0105010b030702030a03181704140609060301060f0e040e0f06220305030c070203150609070c0215090409080f09 78
    0x903001c034000c02c030300403e030384c0c1c41070100c0101d030000211a00c0005000802050380596554006425140d071100c4550032480c04d040100108030301805440d80400d0b040c200a180d901c41403001c20280100104003600c18070350302c007601ca015806408506201c140e00452030382d40f48000c50000e07004c0c0583d42100640703903107020000240c00805034180c90040320994090351401c440c40404a0151260321502c2404441020030100001d81000010390101c00c604c0f491a1154640010081c901d001c4003001802054200948082035a0300030031030341542d083e07080c155204074441c0387c201d86002c0704650040d0042e00d0448007541c07010f030004002100500d03c008a516942d035119032104185400320900c4840d01046c107070340c80064054005141d008240129040c1056026000203140846a03029410450a5075041c405541010000c069000000342803449284071141c0c04074403142c5030300d654a00042c001056044690740d036600006802c0360003104440c0c071080710300d021000551001100d40d1080b000f98055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 298523794 1250 298522544 298522559
    0x406030e0606030708062d010807060f18170c040e1b0a0b03010306020901120c12050c03040506150d050109050d08070807170408070f0b0103020f030307021c081314030601 75
    0xc2d001503c0c0300c2c401405030340c0c0b2201f050032000300480242100300c14480300c0d0640c0102500000c0c60081902500421040c3c0c43c2c45000380508810032002020000030a005503180c1a5480340b186c201d4000840680500c141d10441e02e0a100e511071259502c503040c11046000400f00082045100000b1140c01d001a0214000c0081842e4a4803030102c0c5840b080c0010400300d078155015203051903060405603507101c0001c00403c2100c00090360840400c02c1250300c0a28440944102944910015000ba285083c1500c4040e901c0b8402010311f1070003800c10800001075110742c08c030603014607071100090013100014a40300e512443c601c2281e1000400a80003d061688200c12075401001c0b2526959020a540529400e49850040055504002c00c014034000502c10a5903443d5a90040030440d00950552040200c2031650211288c032070741c1709121140140e0340e404400c018068003810060031645082c42c0c808442d0207100e06500e080c5441c0540010700c1d404560540004001c01c80070741303082d80c0c1c0b540b05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 298525044 1250 298523794 298523803
    0x12040c06030b1309050a0b0f0a140408091002120d02280c0b06030c060a0f09050a14010e120706020604050d08070e01080601200714090601050304030c0602070204020406030e060603 79
    0x6006500c06801002520b07400720f19480911128015425502200800d86400d44c08640554241d01c81803550420072504034000d1003865180304d80960b21401c1c40c00c01c0c1d00d900e0814011460b01c684504011081c07100207038000c214000a2200d5004482d4680c12801c10b40c0700250001100d088400d1040190340030f66400c841c468030b9082c0c002e500d4026402c0300b5911000c5076403600503c40ca400d4443c4220020469440e0005082170707080603550107400d085507000082c010003040d4002401007032800024008130005010172001d504003072070405801c42d41a000284000785507480042c40d4011500086038260b808100c0724800c074041c00840760190b41c1300004488129040700ca5000150001c05102c0383d40d03100e10707100c58000708145028204104100007040d004103070400c1d410001e5214084c208038002800d000b40c075803c10112031030245c503c1d1403000a00030f840001d000504201050001e1810001140e068900807034000c1e008546403506c5040c054000c04490095442c10311584001072502e142c0041d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 298526294 1250 298525044 298525061
    0x80c03011a0a120c05041803110c031e011104080303010f0b04080c061b0601090c0e0109181104080105040605070e0d020a0915080a082d0301121712040c0603 69
    0x81442e81c003685422100c44580780d80c03001c100c80c68074010400054030b85c1c507405411684802410001100c00042c54003400c401440c000e075a51540000c0311012440d900418012018140034411150800034000d1b0680101100041c0c03007545c007800303c2d0210343c840c0c1c00809076050303510014020ba0159180c00001e0464041c2d4070421501c0d40c0051a00403440c10130401924909101d0403003003490a0800b0611070600209030048a0910b6850700340c268580c0c1d00c1400070b1100542070034000c002c4e80c148858010300d10f1103040902012510345801c00740c40c0036a0400c4400074403511000300068105032030650040e1000384c400703100080440c0c0e0380710900d14000d4059004958020710b06d402036890101c80c00054140d04020b454008180031000400b030390140910b4003024821000d1903541d050300428828941e8010740d100301d0b814080114018840c100004403070540d20b9034440c154100c80c0324035001d4107004621070000300980c004148440e884d6a854182801288600794004039141c60300002c80c121403104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 298527544 1250 298526294 298526299
    0xa0311031308090f09040f0302010501050d0b01151b0c0e060f03190305040503030d020408060c0703021203041b09020306030d020d051b07030b0405100605030c010e1306080601080c03011a 82
    0xc1569400940032500420b00d0900c043c02c1c504103891244009400241c0486d015600006003050440800d030342845a1405030404a56840b0360080540303500b000124140500780010036961403181c3c1007070044a50204101e0700901d80c1d10103003c0c03840c00d0000003203507211703403401c8048090100b1254503004000c14a22203001c1c000305203460400d010046888600c102c160103000c2e040001055a481c24401450f85a40160b00513035a2481d0441503490883d00074020a4030180c1030152900003035021031590000340c10052181e40f070341c460741485080200f00c1150492911981d0b0741c00030b8400800d8020303500c20b41085003070f201c019001d1201a0703140d1000000d1400010300c02c20150700090300782c148401900f20000100c98031203460383d503407040800c41907600391000e51102c0c42220307250300b4501440e409414141d000d001c3c80301c01c000003c3d210700d04040303000d482100500c421200c401c58951018000304040c0e01100c6045d42d5815640740c40740030041c103290095081180030101111200d80f4420040d401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 298528794 1250 298527544 298527571
    0x304060924030b0111070f1d0906070c03030f050f060306060307080705010f02010605060705061b0403050d050901180e07141c0b030708070e10080604030806210f030a031103 76
    0xa41200280810707440f1505005010071500d240040130407550000d06281704248844030305180303e0b4051207040300c6855114103040410030600c181c2c00f2640a810008a00b080c10044d242890250040c0130079042440809280c401042840da42c00080f0342d004a50a400b503c80c2500d8480c00e00d41c8a842600400c3c0c01e50703001e008200040e500c101d02144007642c0610000800c81d8592000407140d80c04144161103582c0440d040c03044804481031040120308041a405240c203103103944041d208c50140030400e0031700c1404280e0400507401034405005614419581c2440152079070480403030340805076402e8000a040c0716002c40e00d500c2050880e00040007c2010a070040c081c1e48440000c1c200e5041019003501581c040050034801c104010b40c00f500501620240c50310b040546040703800000d40c402c04441d844501400082604200d45a4024a0039190720403c0d5116070300d075041d10304900e1440400f9104124181030a004003102a1481e007040b541e05010920012401e4041400309444441c42c5c88038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 298530044 1250 298528794 298528859
    0x90a050703170c060907050a121a04151b030c052706070b0a0911040203040f020112110f0c010c090e070c1505130201030641060a0203040609 62
    0x4002c030841caa00040c80040b03625100d0300c0244a424600142c84507179265010140070b0219182010f40b1201900c0040304000d030032080c03912900c0c42c80071402414007030b4081c0303000850180105050000e1200710452000d0240c24524100784003210650b614100001e40707000e000c000e0103031140c0c080b03500702c4000303c0405841300440010a000b41401d4560281d0041c01000340030001104401740318400d40d00c0003c0010100228203088000e8806c2c01da8007485907104004000c001449005000c100540a00c0c00c411010544003600c001400c82c0400e15821890214800e1414020080100000c070800002070058a50f01340041c0c44004960007a10102c0f0300003000240014406c0d08a4150540220300340900540c032801c4c0b0f102212070070f849070340e4213000e00c000010555030180a428000c1071b50000120101e0b1a20342c00d28240f60030300c900c94014080940445620142404240d13010102c0280290f40d207000c1c100000c0e5030381c1d01c00e204080c049003242c900002c02c0c043d445000c0140940d07460b0001051013 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 298531294 1250 298530044 298530053
    0x12080619300b010806040b06012613020402040906180605030a080c071d041b0501050a11030c100501050a15050306060705013b0105090d081314060a05090a050703 71
    0x1140c12011010340744003016110301041642c01503500030003846000c0c01c080e0510381003508411400800c0541800032141e5842c02d2100312409002c2d500440110b04041d5840d5202d80034189140072202961260002c074010892180c0f60b80140b00300d03443d0344140103105030001d92102c10340300d5034403c256054018190391004a13030b00301d0042c103005680d0301c2070b40c1c4099141c8010000c400000000c42d100d04030581c04120030010f1400c51156410806a10032070403d1811000070401d1145040c0315041040d0240809045c1f00c00b0400e556404084074107444648454040d54002403500344a0988210310061001480e0302c1210804008405596125441e503031390902401700c158071080084459650f541c454a0301c52800c50380070594101c805400702c440081040c2d807d05130b46680d40c02401c569145c88103125003030700009896080300f03156003800d04d078656134402403c0c40c0d01c0301c00001404a81070200c05221544010440034440c0c0c0e01e0303a804205640310603c0703007540c654074540001c00503401600f00b4008038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 298532544 1250 298531294 298531349
    0xf04020f040b0703020106061103030906150307030803010920030c0f130e1810270302120a0c030311211b1803070b1608031312080619 59
    0x1140411858078081e900c03450485903510068051300180d558a00a0000541c03014200c088008980021815070501211036521440302030700100c00e0b4200b40c00c0c062020f89080c044e031001590850049503c85d0b0303607a68000c2c06805812074042d030850420000450454070314094900440d0194415800e1408804501c26154011030b030b004004030300414005240e490094006114100781403913081948690400d00386020f5900d40308009450400c44007000144000c5c000130602c9164420018000105050076410f008031450501440c000000d1401b10303003a000a0070381045846603a040180348507600c44480c0c580902c4925020603802a150010039a000302c81e120740150f4030303075840c86103e2420944101d455000c58961050200b108031030b6a1180384c20701c0758030020540001050301c3e1449450540580290418005182000100100b810603c81080b4190801c0e8801c012540050465501814904044540ca4842e100d1801480c900d030707003580c010204540710050381109410042c61981c00d00b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 298533794 1250 298532544 298532557
    0xc030307121509021c0501061704021305010305070f150905010c141605030709060803030708071701030c03060e070312030c0302070b10060807020a0f12050c150901060501030b0f0402 80
    0xa141c0c5907582e044010000788401001000c0c0c851005a0b40c0840c0c0ca50614540100c030a00401c1d1840c5c4401003240e0340c0c008015840e080c0d103900c1800155516880000c0c00540c1200440200d00d00d014000320030413200044000c2510030010400c0c0b08199a110209103410304900e0800008100c1d610402103035000d00018064988180c854030440480402c41d0b030314000c03910258030105482d44100300950306080c40702c6030291401c450180481c0d82000101a5280b001034150030400a8520008010074400c05d440305140f110002c00c003c482d40e40382411401c0810038001511014038211001c4d042c24000034884040361350181e883d1410003e0030340c0c00c3d40141164800c010506408000070000940c0e00d82e03245214146040107084001e0130803030000e002010080c10366040d07610040c0440041035400d010403040d19405800d9451409030407804841d01d0140c0010125548a5841e54580c0424440340c054460440d010080111075520001142940c0c1c41011250b0884008807c00e822400d00750000c004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 298535044 1250 298533794 298533827
    0x230304020a1a1e040512010216020108090304030b0f04060e160b0309030f0309070614040e0a020d2301080607140304110f22061202060921030c061008030c030307 71
    0xc0081079010f801e4405451210400d5400c0000790501062408140e03000403001110021420700b52844400207100a00d400080c2c10300010034000f40c0c0d0f650040040b0703005542c0c0000542d9450500e00080090288280d600302c4d8807a0504000c0344440c04c00040e540c83d10508240841941e074075203d00091658009408011680010440040c8440469004600400c0e40000415109280280c010034402c030542407800302c40010082005086e410103d82d9401c15a5a030005988101507143d01005000c041e4810203400c0380005102c8641c0040701301e00b41200e0102d81511004e83d641d070021191006d08203200030900c003051022034003081040d61741d4129418081d00d9685011070000c00255030142058843c8403041190b10104007800700d6000c0c440080141c0182041041200da001500600500d03058500600c3c880c003185c80e1901c20128071803000758012003501e035244c04540c042c580728902110f0b40d10111084c0c20001a200d8000800c44e440418820b000c0c50039500c2d1050704858a4000320303003109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 298536294 1250 298535044 298535047
    0x91b040609090506090f01020c030d0f02040905190f0612030507020a0819170702060403060b0307051903050708030c03040320040c0806010305180606010e04021306230304020a1a 78
    0x101e00e00301d841038074011070185008001c103141000000740f400e00d201078040c1c040d07401402200d13910314000080c1ca01c80c1072070740c8000c502c102c8160b0300c440003801540d00412a003400c19041c00400d40503a8015102c0c460395075814042c080b0b0854129094032071610598440254984000010034030610180200e20301c004e00545010b9550402145030080c1f0010003100744480008007400c209010303085080f01c440e5a4070a81c2450358076000194180a0351002a11094607490340d652283d502348416005000024800702c90700250982510f000b6409000c11900752103081c501103420b00c400000d0790081307150329009510f032070b085549103102d00c858080c0e1500c05103e6601502600d5483e402500e210180582d5000c408d40342c02d800050588070090640c1c000320641190300d84101c1004900954000001e00709a11041d2051300030600911a07154a00b41039a02880049100c9501801034810030726134403008141e000031402040380c82c4c8000d58000358045003c01d010000540707500030a005a071100741070700c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 298537544 1250 298536294 298536299
    0xd0507030b0c0307020706030b09040822170d020105060a141c080901170610050a0e060414010221120615280c03050d020d060510080403080609091b0406 67
    0x2070001d41e8082e101020007050100801503a950f04000c001e00130881d91400b44064607480000c628082c4002c1c1010701708040000d02038507407904803860001402400780307000c0c02140c0d0302c06500d00103c4820100551038050b41e101c0d2200f4900c14020b490040c3300003410f9000c0c062421188a0a6003131200340e050300136007071301d1007000c0d01100701c481442c4280c01160700559903561400010003200c01c4020805000d0050002d11030300780c80d2205803152030310309401d082d50f440d2074625007920000c0c10343c44860340c002400140843c0b0018010f01d100441d44007a002c884805404280e603454040303a410002408a20510183c811101c4404820350000d40241240300001464203045485901c1080b04103000603c04030490045000c01101401010710740c03401d41c1c05003049079402002d07441144840d0541640100301e0001400856100324001c2200a04003c1d03c00c0d0600000342001500312400c1e4041018080001d00c5420005500340c82040700001034641400045001005107180703801040d0441c1d07891501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 298538794 1250 298537544 298537553
    0xe0f100e0a0b10330810120302101103011505090117090604020f040209030a060908040b19030f09020603190905030f071103010606090e07021c0c050c09010e060d050703 74
    0x241c0f0301030080103046000075820f212855010b0b0801c3d180081426001d03205a50340303d244030120395000c4005160003207264842c1002044040915001005405080c10302081055000a000d001c201880d0f83c080c00020440400b001c1c59000920815100da0425084030f12414882c0700105080c840504041c408203021742040e40006008803805010303980402c3c01d010651502020150318000200d0342075180c9640e1a01290b1500f0b0340d141c0007403056448480100810507504c5c01e8601a0200104440d00d6920441c18907114550b20880100440d2903c40d513a810314655016003245e0f00d13006000c8914503264124241da00c1e45107070354280a4240d030741c641040050000d20081000024481d4020346034152800c0c1000c3c1181100780f00d07482070703240110070407090390002c1c4840d040b503161468841041c3e644000590405100140e540307080c6040011950249800251651481c0d00850455100d16070880510014407401c1c002c2e100407540420008a0700d19050b015038141a2244e001d44001680c3c1e0340d00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 298540044 1250 298538794 298538813
    0x11060d06080105181009031e0201090227010b040f140402070f030306091112040b07210501060813030207050906040f1401291206120a14010e0f100e0a 66
    0x212841c3c0c4c1c0a55011940e4440e500f08103002106080c074104111211050b82d01a0081c3c029503c1610704444088045c80c1540c002e6214000d00341d000340021004072000c10012040c0c601c2d0101c0f41c2c5000350140000310307039090090103036000e855441001c46100da040c02c1c8040ca044076881e0125034450703000c000302070014007001c071040319075442a01c01040090400e1020010f031a100180e11310031080900c403242443d02081c444542003a082868a0a551201c110403108001c030111504445040340d100c0003504251076102038101c81c8a40d035203460790b88640a51240400d030144015005074040c1900380080d06d05075042c1500440000d000180507103003c44114141c41401c078048100300780e044010811500c07011464120b4100b03500705041e00000e820003c183d0340c041c80c8015416501d0200000c0c0142e240d4100309041d03c5a2b4504132580c00c402d900d07260503007240c03056456460b5428200100b10404000941104964130780c0c010700210b10716841c10344004c10715039038640158401e070f00a980c0820304440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 298541294 1250 298540044 298540051
    0x120f0a030e0a05120a0b01151205060312041d0c0f09120c030a0b060301061a0d110d020d0504030e010305061507080f040e0a4703030423030a11060d06080105 69
    0xc040c22550080781010104514160308c00c0161414880800301c55950040003450300003500580011683c407044d011034030749003821550032066a0000780101e1003264030201410070000910101c440c65503010b03105401d6000d0070607500038010701800819464604402910b0903040d80c20201c1c0d640c1d03910200081c2c504101c400d0f00b52101080202801a02c4c2001c1c0144c1010f41808030b5414031189030200c09a0044c0b040d168080800396440c91042c0c0d81f424500c080b16641c046543c010340d112200081e115004000981d03086010440561448140d1b500a00400307101c4c200041c6001400405810b01d01c4041c5c0c448a41101c60020402c600f149212501d80544041c200e181b500320001c0ca800d12614049903041d41e40074213200d80140007030a011510740c0e8901c2d4a0801c40c3c4803615000c441d0202c014103c614a45015454080420301140c0f0b14403072031452601c4852a06642382182e1a10701745511400703908000350846200e0782d4644494100100240001d020301d0800060141e0750f1902242100e4003503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 298542544 1250 298541294 298541329
    0x1103120a03020406020c0d050d230714010f0b0603070c0609020d0302010e100203040b01121e0809040f0b030d03180605010e0a05070e090105190e01030b0105120f0a030e0a05 76
    0xc1414004a0741c1045101000c031401e54070341403201070316111f4555a207030000c06d01d8101b002a07401c64616401d070340c0c55500301ca988000b605492f0034240c82c0c800b9004410080f003003295880c4c10f19036500c65699009103007914101419280c51a140c02000f100e8484071030344103036890398980c40d0741001a01d40ca040108624065400001c1091882c040b45007840c0581f4987c000482c01071007800081040801443d044480001c0b03103c8906503185030000d00340b10b0000252aa0300d040300302400030b0011400003012078080c1103604010800042003a281201c071044c4240760582c0c081c1c0c80d01c0003494082d600c0320b110b0303080340071031041e40402990f0b03220180c0b542600403200500803c42444403503a100c0c0185500020070b802c0140240640c41c02040040034144034441c41a10181859020700c06402c415001038420000007200641e101e003045140d80c00700b03100344e41c0a1541d8401d14800c600740850520000300410b00905900029034404680751800786071110307400342e000300c3e001034141c3c0c0b18000c9000c011100f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 298543794 1250 298542544 298542547
    0x3030a060608070207090b0a0e0a0e01060506040807031209031e020f040203091b01030608030a0903050c12030403080d020f071a0108010b030d08041a010f031203090f1103120a0302 79
    0x46a0a400e450303a503402401030016100500c03468540202d6100142c2d00301c0701001486200000000c3c144880c1039000001e00c420100c04d2001faa425900a0305081c1705110013805929614002d0142e07502c65881003011710f0300030307142c01c1c40040c0406403406995050b9203022038030a5100c0e2201c00340c0c0e200101524241c0c4034032198880031814450300074116030078201c1d011420f41c60030141c0c07291100c0c045180f070701e10007480021000d4142e009501c100c2c0540360aa00f240d132560209040903059114501040d902c0740304c1c0070029040d529002807100fa5801c5144d01560429186503519011a0005061509803903000c0c0310b031104428003080079180490241504a0800d408405101a0240103030800200390b4104902520651130010340e08500b00030600d41a80130b43d40344c1c05c140000c4460001140d400f880048000035105a18107035030310640c3c0c02140d42c1d4909158000e4180c08a0388007660041c01d12642d240d070840401c120740e14800c400d2070054240ea8407007441009680340c0364000440d0f800420750 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 298545044 1250 298543794 298543801
    0x61201060806070e0a0b07020d0302011103070201091104050c0a0f0e030114011e0605190201060906060512070305131e060501030c090b0406080c09180a0b07030c02030a0c060c030b0901080303 84
    0x240040741c444e466100f500d400710b03001d081c2a07101d10b0138861100d02902920102402a0406100f5070162a107601c41c0c2102907100d0525050081c080e103054a81a41c18a0398a80291854541445000d02807034004058515146440d041130320b0400d00003a01805201005804001944080c00707601d540350b05c0712000701c2d020346c1001c10b2100a85281d80001c04125050300c07080c48145d4207c0216140d11050305010480441680c00407409055240c100041260904034001003150304071025041100407040b0003403080d610b0010490465504441ea0303412150440c6c40800401c204c6d0b804400800000b00800c03120842548617071060361401c2c0c2c030884140c4000f60040040500d80e221300d00d20751104440c2032140703a00d045201581e80180d6060288a004884003080c180d03c4c1c0b0115103c480f030072400950b4880d1600303042c42c0c2040c2c0d03002c8506501080c1820b42c00c10080b88044104c60300600c940d10744c0d009001168454400504006c49000141640e821201c40d1651700d41d02d1541c000c00b84000119176038034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 298546294 1250 298545044 298545047
    0x602040906060c050a030503060a170106051203070f0b0a0914070302040e030a08180307120e01020c010903080a140408010e0715020a021305040f020d030309170a0f0806120106080607 80
    0x115690b0049041090200180e00003480101e80c500041d90585802a26910388000040c06402d80d684a810040c1040d11003501c070b070740190410000c45004682c40d0010703180d10070740c1c981c90b4400d5010040132080c0c80c400c6000000c1721200b14a0300724804610000b2a810141d6480c040d5000d4126500c0305540403500c200118a02402031300581028040a54204202c64002030f150280c040d142c442c90f680441c99924a260080007030b14002508490903510480c41c03000003030b2109046040c03d50041c0140741d0f10b0810f0354081c0314404103c9502503d003620340000c074001280c0500306454900d07510a808c1000140c0d800b824000d02c5400c41c08240904401450b14003c40000144800c408003550069420040982d079100c2c1c0d408440e2281940118096955280074802d4090071400254854580199601815419401012501d00c1031780e9640102e0b101082c40c3c030b02400740d503025000103045d00c0031081c00c1030300c1f0300c140d16040203000e0100000c0c0d5540c0c4141c01d007511599000014141d00800401c40441e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 298547544 1250 298546294 298546301
    0xa170109141605031b0402031902030f0f0c0412110406092409052707120c150903050c010e04110a0c031d03030a03050c16240506030a240203010306020409 68
    0x400c1d01301c008140300e03e24010700001d0a050480134511440d4040000b62010403030200204000d03c8440c01103549203000b242020504e642520060b824815060000d03000c0215107046a0a0702c1105405910124082d074030f80f4003004990020320340103516480700003884c0059000350506003954860083c40700503214407980752a041542b0a0054a003001c0501c40d04c142c01d14041401082041004180c0c1d04030b642c00e0728035024079584024a6005a4410350062226110b030340822f41c0e00c58507a60180b1401280d0440351400d86000207405600001c0c6044080d60140e0903245c410b210280c40407c0314011300c0312035004d907000301d9565404036041c400d5541c01c01d42e00200c00400180c0c02d10f030018980250b0f0300465500e010b2010758505046e968400718810030440c10580760011080039402100800900c1e00a102d0862070310f42c00c40c2c422801c0c141c01d46081680c02124803c500c00b40007051003521988800030300c1c01e10313190b5410401120b00c110803c0032106000560103940200b00c0903a44500c2c024014046 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 298548794 1250 298547544 298547549
    0x6073e0307030b040b0603030403080a02010c0e0405041106160b0a09050105010618121406040c090f0207032a0f05061b03010602061609080109050601091404020a1701091416 76
    0x2a0000725060000035075403400c481e04945c000500e0740c0e1319030301d001c0441d1035481150000b401894000c0b80d40c0c104282d05411a4902d50055540c4c0e032694030b079440c1400151801544c0080c512241e00400c82d0b69401c143c0050b080c80c504001c4801c0040040e511140c05030381c0140e03100011141c6801d0203206004c801d0040c2401001d02e031600c808400076491308500300c000980130300150f461520f103c55040c044102000a001c405e0801528202e003803514080c0c200042034401c1845035030408102c0c941082c010310030f6450540e01500c60180480d188821002c0300a88a03085086024006c0800d00101e94407100a50070340e032103080140014280045030203c980d0121103030360040c090410062040c0b542c0414010707080051003200000e0420b595900755075400caa900011419841e180065042c4480060014101da43c210750401000725440c100d112416030441e0040d4004e8401c1c90308108442c00541094410040c1100001c0c01032416030380d540c21740416940480d45940304800c003601c042d0481070348000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 298550044 1250 298548794 298548799
    0x31306063503070302060a0507121103090706050408030f1c0504030c05121804020a0c080c0703110a05180c04050604030c060305090604261201090c081006020a0206073e 74
    0xc014013030390025a0340340c000700004841a1540d020941d818002c0d1200c08104818003001e000c03c500d00b0751420b0150700b084900079260310950000040003070160084405450300d003800b443c9802c0c80f0543c0c0c0d010030ba0021400721a0450700303d0071a042c2030014480e8a0003584a5a46c1d02e01d203942d02d05102d4a0700c031280c0015041c01204000005081240c0388020101450942d0050b17110102d56400b62100c02c4d42401c05012204001282d00303860718042110020f0b01e00c41d039003641c182504481804040714480c01200c1e0455107008142103040300602c105a84800246403583c43c2986920100c0c00641156004658603e005401440000d8150140035407010000300101078501d066110824940704007011011400c4801c460071566020701d1088543c81c010714218038881d560b44603804402002e02c03071000b10008030200c0c04244038585600940c401c413091a40103110001d4a502001003c0e030101e10100c81010014480c1035455002115000c0f40c00c4480b420001c404000c0701200b045080c242c05090b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 298551294 1250 298550044 298550047
    0xe0303101502030307030504050a0c06020d03062c0405030f18040b0904030804060e0c0918060f040c0e0705090d0f0611093007120309060311031306063503 68
    0x10102d03800001d603a030040e80c0d80303000b0900f074403213041075070400c610b042002d0941c201d402c402054007500065017007070060840e602004a9070361142242060a8000d810002245504900d0300c079150003043c2e0142c00c10701801c1a01e02e40307100302502e601c8a81c4603e04180d01c074643c480005141b0f280620540981000c02d8691080d00c0c501958000c000b600000c000038150f90341c43c54003981c03d22081104152004019000e603155007410f84070509036980380c4c00c0c031401520071800051240340380709011602a0f51302c2101d80144606100b0040b0030050010460b804010b0b051092055030780d01d91003940704043c000c0c2201b10500c000c1e820300c402902c0407104580041202005211166100d0341600f80001007612a5182c17032030280441d00c0f0b01c410b076228100070507100b01c10000c500e1141000707800c010b080c441d84941c20b410ba542c14054095941101c0d0b03201c1d01070414800100070f0030302010030068051060ba0b000600b03035143c0c20b011071000d81a88101343c0c4030f03902d0f0000038104000c84c0240102c81141000a5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 298552544 1250 298551294 298551329
    0xf0f06030a061e06030606030501060b040e040311011104090905070602010516030509070923060d0209010e25050a03060816050d030e100804050c0a050108150d05010e030310 76
    0x7903560700c02041c0105100c0d540c544500001408180d01614100000e406020b9582d40742050005810b04c2c0c0029107a5518140f000070f48050780e2001c072801c0381c141d0f85078504680e86507141070b070ba1041c401030b2019a80d5240c03580c007410860181e009202400381c61900041c050b240341031003481e00319990810029a8034110503c0003010701c8050505580e0700038500070480382c1e98180205d007010f803150300c200007042c02e0451451070700c9551050f000e41540c00005a01b1169142810044a600709a0019400066031401070200c140340e07605155000080300343d2803402c0008040304840940e59080c85000044010542e0340707030035902d070240364010082c072030090200d9590014032400816140c4a004d200f0820070b4034a00415015502d50350310700d0030081c1411469402d884c401391030394108441c221001d00034102c9155440c500303e401103007560b5040c7c5d50f60300c142c3c0d6400080201c500140c0c0d0700c2c03076001a405400400050b400d0182009550325440655128100420302203480c2d40d80e03400c164090405075001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 298553794 1250 298552544 298552549
    0x1206060c1504062a140d020c060103050a0b07020a08090d0311060f160e0a060806150c0106030210080f0a0e0309061908010807060f03201303140f070b0a11150f0f06 72
    0x3c0485a07589117441c683e90307410515584002d01c04c134410303103c8034060380000005000b00032902c8103c603401034450040e55034036000e080740c650303100ba080108000d1042c009852941404040418240d109040c01d0909526211101380741c92230445884656000d41c43c200002c000c242001030102c201c80c0e003403600001c44408001008a502c600988040040d0386000074002c0d0b6964580041d4452805002d5589079405d070b074114042d103458007069010780b160f180200c0105200306803252040740d01c0054403140b82c56000844018150130740040f84288018172a12550783d503110001d00000f100801c101d9410810307480080d05016050740300320a03c3e04044010040c00e5005110441c2101c01e03032a0010300302d522a51070502c2c146070581503101c0540b02080014200a5403811030341580d02445440320310707aa06112310303641d8801c0429112035540084104100742c2070701e540640100c0109051540300c5040040c6c121785082612490b003c1401c03031902c1405500040b1540d002c0e0000d402d4644094245040d102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 298555044 1250 298553794 298553807
    0x30c0603040b0403030b06070302010f110306134206020f191a0f06040e0c0d020d080c1501060813031b0f08030702030913021206060c1504062a 63
    0x1800b030780d4840c400102090b201e079111024881001300210b859084900f1300070300a024025901d822145001d042c0c040100400301683c0c03054070010180c06004203070010f03410243c002406922142c00500c84604108101000c403003c15000360041c1040380c0458a00d05020302a01e03074801c000359000600c00000809000c030313034104442d920044114190034145844104022030108803a520403009083c1b0501006008031079000300700480c0cac140000c17031000d944281c0350021102c00b6a4800350000c00000141404510480d4981c051240c0c203007001c1b00c0100300e9003429025000400b65a06603001805001e03000104030b90415040d160000394000156800380a01c2d18203000038600783c421007000c0301000740d9203200b001d02030303030001090b45c41e810b0030307135001e5920741003054860301c990f401d8001c5643c181194429103103800070015200c045601e0381400d00c003066010b00c09140050240ca40c00422082c40c00d110729020360310030000050aa81ca0035801807204240303401400c900d000522420690303507413115 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 298556294 1250 298555044 298555051
    0x70f0606170318040c08130507050d08121609140d020d0507060824060c0f07030b010f0816121a010303080613021e03060a0e1503210403111815040b030c0603 69
    0x2591f02011410504100c0d1805040d680002da020403074000c00010048407501404200c01c24621100082d254507642c0220744030050403480015403101c2c010020402c6031039000c5100840a03254452060700c0d500800d00301c481c0b250050b601039000c000300b000700a0380100161350140c0c40c0080448000c04048010042c0003c0840081c4504000311b01c041c40c2101c28003c04211102180454200b6980d9140034803c44a007403240c040d5010910368001800341000c07645891a46281480c450001d09000f241c642c400007a450659581d4440581c0003107001810f0701a0340a94080d0b00c4141c1c242c0b410790100800e9065844140e4907003401844101119401e0b0140740d03010004070040e064480d600c82021a03c100b4050b44141c0d41e4111074800c1c0301450420a214003da01c5c4190306070761003108007500050030001c1c0c0c92410784081c1030812042022072402d500002c0100d00c0102070400995400c50031242c9001c055446594083c1d4404a900c080d1805100d03400103600d05070040d11105c0700c00000206c5500008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 298557544 1250 298556294 298556311
    0x6010903080f0a17040f0b011536090605030d170703110c0307030801090c1121190206060307050909150a0b040615080f0606070f0606170318040c08 65
    0x1c01c0c0200d001d40540c080c0f6500c80e44da40020040ca2915050044008201640646140c0079000003c240c1c4500c01c6203180340d808407501da1040e5001403244025030802c540582070f45007282d0b079600f03614400798401d1400041c807840c20049070041c184010141890100080d98061101980301c000c294202c0900f175507404510ba040000300004070300d8002081b84198880d6071810b000002e094000c16410514145c10b0f14038041c4208a1600800010f0310b072002c1902c00047c15900441c580d003c448484102003070324442403800c0c070f810005540d645021422281d2081000741e0894010042030342010440940101005c940901807800c00b0221181c0316800c0701910405180391100060b4004001e4002d107980c007202038420001c2c150340b54840409641400c000314005014a4007040304413490f10308140c06424024074003450304000b6500c0b2030f2003440d1030104a544036140c220028508526404d0301c0318001d52000599071b107d00389120396500c2c0b01e40c120740d284030306c4c54104004001ca5020b0030040e400360a2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 298558794 1250 298557544 298557547
    0x7060207030f0b0a0f0f0218090402060415263301030f0e0303040c2105060c07110909030a0315150309030c050304091401090e0d030f1d030a0806010903080f 69
    0x40c101e00d1009000200700d4245d500b41020711014416540b5402070000300448409507140902600405c0002c0409840103980580d0070310082c815080096007041d400e6505003052882d0348102d0402c60080060544203151001000342040b410204102d0b40781c0000580ea52048840912840507284800b030311407859040543d00d04d20050fa000a5501407100809408201c07904d900e450300d403003e034400560140c59a920511400c0c14000001c0303e020240960340903003d04507550300c0c5854a44240c024690544420000388045425901c48070f0300309010783c210802555480038481c03005410790341404c4001080c1040c02008120250002c001881d201244d13150105140c4950f0030300b00c42c4200b5503100913140c2d02000800088550a0342d220740146640c03100c0000c02c0340e07038a099090450350200d000007126040020302050540c03080c0d02940510010080025014000043c13861000c903009500f1403076a800052043c911a070405440c1e50311540910340400e00c113085681d007103544e029581803850303a00c50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 298560044 1250 298558794 298558801
    0x10e0a1e0b0f03010f0606030b01020f0c1e0d03020a03110a1e08040b0a02060714090105030f100b1b070f030f03030e011404240b0f09041104110c07060207030f0b 71
    0x2a0501d18080002d0020024001660150b0800c0c00804083c072600b0042450000109101c2d40086110408842e8000c0a030005824003018020300030504810101c200d080ca00c4010580c0d61032949100945000303a0040902e01c20614001c0e000c203882a809650a51000740301c0e41c0003802585000c6003c00203a4051201221107143c0855107014a800000100f80d0200b4040421540040c5151240240d40e1341c600c80102040702d000040d03c250021240051003c00001300c0d000c01340780043e0780106010704190322059071090b0402c07140c0c000403800000c002c194860710036240004c10080c405455040800c180f258074540c1d85000715030500000505160715078001c424440000c0d48174007078608010000d0f45282c94589050740d6000d084c0400014201901c4030781d0040e100f9580314020000c40c0141084480d400a42e041040c490350040040f66100b85070920030301075844600910310500640c05030191610030303e41d490742c03d00805401c01001c40d4032010040002c40c060304881c00c070264000700342c1368040d00d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 298561151 1107 298560044 298560049
    0x1b0501140a030506180123030d0801170a0507140424121b09060e0a0b030a060b0415151701031a0601020312040b010e0a1e0b 55
    0x40c00900100001070300a40c4415000304009041210350902e15803c4031304408241c1040101910f40c00d40041e1651034480401e80303014088010748102602590001c040410500c100e585c041042d041c10030170184117104e0003d42c80d8108040e660b6898859a1910400115542c014012032519820524a40d4040d412854407007030140c0c1c00079024500100402c1001049105489806c205200d04a003008400103907802004104004103a40c0e00c1c202c0c1c04003002800400d440841d5052050340510340d6030110f115806d4543c01400007404078811408107005011a100308491007a080c42c3c04100d103107114000f601986025503031058034010102c003080654600307200080202c00c5008104c09403c004c2529a540401c06204603820164581c07010718803403d0940e41603524508040040c4a4409003a03103542d40104940c1051103110480a001c90b030070680d00310810b80d016034401c1264020ba = true := by decide +kernel

theorem cover : BRFrame.Cov 298381294 298561151 := by
  have h0 := BRFrame.cov_init 298381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 298381294 ≤ n) (h2 : n < 298561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
