-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2823
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:50:51.843985+00:00
-- url     : https://prove2.me/submissions/313b7312-520b-4516-b7cb-5fcdf933f92a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 507553956 ≤ n < 507733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 507555206 1250 507553956 507553961
    0x1b14090a0e0a060c03020901081f03020907090506040311041b090e10090e0607021905070311030111070503070b01090c0e011818020c06070e13050a020f0304151104050310 75
    0x5403024072500c18110101c00180c3e181c01500911320341c0d541d01688500300b4000141c503082c40038004480d40403a007524041820f410f0f800780c408482d01101d5100c0b5549031010143d50b22945908215007201c80003401100b400654581180b160006440401c41c004131010700b5849003a80010380c170b00041d01c2c2d19040101d000c15a000b9030300008034030741380001207656501070801c583c1d0207180203503260007140c108101e10341c0510a8405d4201080841c985100c0150345080d2544030782c0c0002400085c030b00700c0a0520341c4007503002d17030074440039040c000d5031721569414102c0d030303076004a8011944a040040040383c04c461501070a84031000300e440c0d05114a071041c0055400d0a20001ca02503040c0200400081c50604001b5040304070450000040c0d484045425441c100f200003860501404080c0300e94014039181c0140204004014000c002200d489007070286010f4403546203054125480402400305001003201481269400100704000507034500d4505000d600691240030f6140c0c01840c44403802c0c04494 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 507556456 1250 507555206 507555221
    0x21804141803250c050411092106040c0905090a0b180a021903050f032b061e05031509060c0706140a060303090e040f08071e1b14090a 59
    0xc8082c0d0f03040c001402c4800084203070014183d0b4041c1c000c40d00b01828402c407104d83c0d0000c0d01c0c09443c10310000c0a0180b100b040d44c480c160300c040c01101c1000804208941208000400041c0c42007510781508040c1042c901c01c500714014041d5083c9000003054074494009034445040e80e0104414445136134094a99823003a80c84080e02d24980641c0c441200140e642d1403001004240a0025524150079410003600e440410701c61080b060b4401c012940c134020060300d40300e082da0300d0603c944156110702005400684070307d5120711815020354400c0c00e0074151801008040e01c1003070701180c50100746e00840d16480d00003603416100c640c004202092000c00d0500c014100140601e00201d10501c00380140024080d044030f004030301c140d5602c0140304066014880c400200002501680c0d2410191940c103448000c03200c006107081000210941044401e00082c0400f01121003648a000040d040114010741007400c80381c071030960403c0204411030080d58108840001401c407a12641c2c51801c00c50040141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 507557706 1250 507556456 507556501
    0x120902040b0904210302030108061f0e01140411070b010e0a180f140a0305030105040c1709011a012a0302010204030203030c070e0609090319200102180414 68
    0x1c54844100c6510707610400c60056202e14082d000411610261a0501c004418030310304250040004100200c00003495071b0b049403000c1329504100281c0d20003008559115446509140003003000005c0408121030008401c55041d541407010100011010400c0d11070b8060041207a0516001404080b1410b10341a60081400c040050308982c4070840100c00802020111081440c44075820100070200c216401c4460b41c800091035609026500500070f40814007c06024a61f259126020240b00315803c1900402085865416041c0141c0e020f02034a2001014075520301c1f40d80c010780e5994810b5241400d854005601d02d4110300000e0310b0003c0034070341c0c2142a81150740030301010015039001d01c0180560307500e403001010b22078035010751144086e000500c0c0501c1030015000b007080c5800c0c044110b0f2150300d40000f1400e603032a9410000d42e282441314031317490031080359039140000c1c0d4101540104240342c40c00b1100084a036090040000303690340156182c00756442030021034090319908440c3e440a0b042e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 507558956 1250 507557706 507557711
    0x41e0c0503100b0a0b1c2414120c0f0111030409060b040801050601050a0c1b080d030f051b0909041115070201030c020d0915050d0606080f0a09020112090204 69
    0x55500020345015440b6040741d101d0707540c03410101c6040c0f5000b20000000d2000d403520320300b4020040107445042000250b0740518135240c00715440109040c030503881c0204000c2c1007104920782c43d1800e4401a03411900600d000707580c2541640d140c4e450000e0b003101c211800903d0394007505028001128041d07002a03407000148030900000c40c84444030700805018001c0e030a14140c885141000181c00d40e1000b41c205814407408004420809900c5664442000d803c030007330402c0510f11404824084480c6c4e484441603014038040148416410382100402109411048c062600e60300407408208101c0052102d080004000030101030410850065101c2c1c0608012a402d50111005c034020265144840f60505400551441150b030140f0900390b00c00818801445020446c08010700041100e005a1844020341d200c603125035403250b03040380c1d81014454006c1c44401e50ba001c015144a1003a151000e20806100010380d0788105442040300320b41d0140d44040142403004103c10040000c000c06980003074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 507560206 1250 507558956 507558959
    0x50906030c101209330203010e040303110912010c0215010f060f02070b28020303240f06160203071a07030f0323100611060604050a090c150215041e0c 66
    0x1000e41d800380c1e017021003e000d081c0242100c14690a83e414101a403910000e1051006001c8401003e501c40d510030b40c14180059803400703000900d0b489002d840c4400d540801503985404012906402c1860011450f800f201e00e07504c030343c540c60f18074414240103802d0100b640c283d081041a2207050b41c105160954015103a110b611201444d034242d01c43c40c0b503007000ed0000e9003007040910265800c041c150103584055819818041d110008043c101005030000e10f600071002003440d690840002070400b4014a02a40d0346002030011890756141c4000741e10902818400143e03110340b20724131084050035248480c0c542009903509031115415000184100b5030340310032080d04c0d15070041130317070b146011080781d00c501d98504003100801d02d1b822034109400300036039441c542c5503403400028510742149003140c0119a03642c95009a0300208403400001c2c2c00e80c44001c0002070b04441408a90380c001049500795440200b400001d09041d000c2690010b043d04124200006244968995504054820800c468905 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 507561456 1250 507560206 507560213
    0x21302041202090c0417150a0501060c03030c1107090515010e060d05090106170f0607021908031911030f0109091e110a0801060503070801090b06090a0b090103030801050906030c101209 81
    0x3031000142c1055150300c00c280b4007e180f0b28009400360310642040701030140b5070400300c0c0100b00301c0c02c0541c0281231644034000c0403407003401541d90350b0349204074004541d26a55a01000800f03444240d400704c01e00714070303101c0c005020b500c5220300c44a02c5401520762458410004001801003100511515143d542c50b171012915502c1c003c0818840c80703040c0e000f8120307100c4803021039041c80006001c14081d54400c400044411248040014641e43c000388165181d41d5412221030401c0d840200e042c220038500a85447c2c1200d02e200510b014501800c0c80c03050303d80c0ca84140d0801c40d4070b0254003510445902202e18915099240b00f0601c46200d829003c01445207070002c0f8142400719008071a0994507000c050048d400c04100c800010801070380203100c54412915161380c200c5020701070a0180b141e0200080d100b81058100382c0c0e40140140c040d044640e92424000d02c010030a0140903c80e58008010442c58030300064429075181b0020080d000e04851000d0565400425890311102d441c2c0700da442c40e022 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 507562706 1250 507561456 507561479
    0xc03040603050f132109050405010605070b0c070f0f08210603150103081923070b01050d0b06012604060c02060c04060503070e040b10020a021302041202090c04 70
    0x42140d81c402107034034100000c00c0100c4200050400240441d080c16460100c0c040400c48903c12480121040407000d0310303c0115419003072500860742150828000160056001004090850080540c200c0c19264044881981d10981e80b0181114081c50b0201c00231070302418600324064891404a480c10301000b07500601e0075803013100110400e4510301040224102408150b02920041c2105503031981103507944040780c01082d44003034a00c1684200a403405008468000340304850640240300711005d121100c51a07446884100c8041c21a04000111070a14000121156034004844501a0313541801141d0020b001069520a8603800285005480100802f80e020398051240425403510741031019203031800140541d808481308200c10031031158000d045d250030045c1031819803801508a000940500700448015070b0201e01d40c800030058039000a00032031458804c0d0b618030900011030054104034003c0d03200e00c0109007035484031780005107801b03074605901c0201303007010380e00300354450002402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 507563956 1250 507562706 507562709
    0x203060f0103050601140310020c12030a0501060e0103021c090c1809291503030417031804110f07060f0204170c030601210302012a030b0603060303031305030c0304 72
    0x280d030005100340081131104070701403e81c1840b8038040c03110f5140401c0c0c2e201c0c05040d14020442d4081a8110f00d42c2c0180130f2000e071030040d41c0107152281880c81c000c0d030007002c080c407031030000c0359828007107030980d50081c000c0c2c50807500303951507003540100050441c0e03000d0039103041e0898801100ca4004607070628004000c0080100416000079018100e00e041021510303440007055404440c140d403103003074034a120b206640c021400320107904080c2110000c04d00d940501c0d0403108400382800c0059004040c0040602009202d01c0300c4801c0c50070a0a0501086680300405540042000c010000c5440340c1d0304001d246481c450180060700b001c1d13142da00c00c01c0340c019800080d02d1012911200701c030044200100d404421040700649480e503d846904556215403549490030010303404a02c80600d03000398809a054900c601880c4000441c90700400d400080f1031210300040380c139115440b000c900786241a04e11504014000314516200c1050100b8080000300b000c65440c40104401d10344004240301600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 507565206 1250 507563956 507563971
    0x40b0912030735180a1707020f18010605090126040203070e0105060304030c2901080f0105040b150d050d0201050411120c040f1d0a120f0f03020a0309020306 69
    0x1406411604114020030010400c6004014407a0b0503c1c58029810f0051a40150310803908058000d0b030420042e00b00280e048014181c4090200c2140f020000c080c000d1a45ca403088400340702e6202e100c07042104104c000910341c400388040c2c000622059000e14020016410141080240b0f2401c3c40e240c001d0451304010002d0702d0700401c400348400c50401304501400b070300031b2440109480d030620011503000d0200401c0070307040040c029031a40030300c1018a0810708030b203c070348036107016458070702e84100c0c620100784503900c505c2c851015200c00422040c4101d0f4020340d40030582c07401c29104d80c00b1034064010402c805603404407641280c8000210104142520b080305a0000b2070170f86068103104d08500c8500c6030090181189556800c1178100100e50040f400c80101d4bc0011007400d6080d1107030040a0035000c025990407110070b41d10f02103000044400000c1c5c0728001100080c5014042250000324840c03031030340841c0a91002c2c0309400e01a40241403410020b00e030010394146c04e5000240341100c190ba451 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 507566456 1250 507565206 507565217
    0xf072604060606170411100c1a0106021015140a0503030c010b1005042103030b100309021201150b0306190e070e0405010609120c0302040c0f0201050609040b040b09120307 75
    0x2041841c0c0c01c40c00d0443c3c2c0452082602080380740136100c89000c9803409404903c80c01e601c81f0785818513405124a0004103070044418804849645c40d801c804880a016410240c41034100360720b2148828040c00001c501390103020302c4407901e003818108842c84ca942c83c00c3e81c844490b020215080e02c00300301401018070072400104020f107284040c001c4000044041808100c030400c030a100900e900d074803018070305000300e048950341c0ca4035081c11802400b0301a001c550020300307891052802649030b0403161080b402141c5180d845036410410508a41c502c2c7d07410340c0b250702010410048141e840002e190b100d000503000000307543f04005030fa148442c45805c68a0308049100c14040141d80c441626200181c0c15a010031581d410080c1c040c000c804240b0a90809021102e111410803003070002d1800117541c00b400602410704200170140142010441c8c0000541c2b8000000d0140e10b4080c43d103e0080c1e400880c6101107445546800c2c0000320000c061080034465019100850307603c0741c00640c461440c990f5030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 507567706 1250 507566456 507566459
    0x9030703030e0312010b0a0c02100c020901050906090f070c05150106081b090d050309060d2007030f030f0207170405011103040e15150a030f0e01050f0726040606 71
    0x28048498035880400142e206001e004940441300b41001c0c150341090304e4160f100e174460380e400c8030140e02c5804029009a07803642a440459006104040128400c40764114a41c5c0c841c802d021150400702c0300190700410100100d42c1c3c1034500e8510030b80100c01450111038500c0151034442c64520040030241d280c01d4190010440c55074011107654010b1105070411000c401d4040e60b080c45130140b11a0305200b103992003004404c0003000c10481d40c105001505031901e60210044200060521540e500320519501d2019150b11400780b044554040d0f05403551000c2000103a030881c0144494205d00036416820820100031440010107600802814040907607104d0404000501c000103c034201130b410351042c441400706400780381d055580400e480107040b606008280c006628504c00303400c0c10304052400104040684c0d4140c10459039407501510500074201481141400c940007110166420300c0b010380440c400ba40701d8540d003468010558200b0000041464240983c000251001c0711038983e075140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 507568956 1250 507567706 507567713
    0x1a16180b0a1b0b01180e0604061505040e06270d120617010c121a0907050708030c0919080c01080603070521060702070b0f03040516180509061b090f09090307 69
    0x94800859500800030b106d100106240542d0b0785802920040ca281e840b08400140100d40c600e80d1001810001c01c2400850324040c135460f164035041d80ca0341c409ca0705c82d241108040e19810300900c010110600203041d5410b0054084480180b01c10f054243e2030745070740340080c55031103181c03120b00ca03014101c000054001c0403980240095425203040b150850074100c9526104280c4400500701c50310507034102c201d655640c1d0040750709108008004040f110044113100340c3c0c02181d000f40004600603a84502c8260399100c2c2c44840c5150361103000090b900501c6810b50f0342d44074000792078105801500b10307510307681c0f0390b40006c2104c7c900201e050300342e04040a07038503800502000b003170340c104110340083d00c4d103d8180301d40350200c0e00c540c0c40d406100c102d0000128003000340c10000c26035803130300884100f500700e130b20780462008910000182303240080c03c20001c101e01c4580841c1207030242010b01115a01d2080c11001d201180e080000899440034040e8405d03082603d03200b0104d0310482525018580c0c4490528 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 507570206 1250 507568956 507568979
    0x605060a120c1e03020c0a0c0e0f0a0911010302090a36050717150306010b03180f19050a050703231504140a1a16180b0a1b0b01 56
    0x4082c4080110842010584610902031a456403602d07180c007698690402c0d45035442c6c030712450f400821744424001d00041039454000058000d00c1c140d00d240310540c0703c005000d000c0c0c0f00c030b2400107031400105030340700e502942c020350080c03050a50103401c909000342e07209421648104081c1d0781e035402612020f0000d060740700c0785100d0100351000000410845c04d121074010700c0d01c0200b00d4120f000280ca0408647d49080d400520b030080c40b40142183e04075a101d842054141d0001d0301c03503621400c6203440c800b00301400812009400e816800c0101b007944200300b02601170905c449000c1c0d4142c080c800c900b402040c2e041c85810099805190702c0c04014400c3d849203440814805180c0c681038004202c000a6025000f00301504103400c070742c0c4440020381c80301f82a800e0450b02200144810100301c2002c0042e044c00c02014400d4950005070680d0300c0e1618402d0b0341351410070440e00541030380c070603003448001e00c008050000e2804624082c550b403921144400840e900191041d03854160740c0c5c0c0108a00d05a04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 507571456 1250 507570206 507570221
    0x60102070515090402030c071407090c020a020312030a061d091c2102040e0a090b100302060415020313060c0c0b16150f020d02040509011d0c09040605060a12 69
    0x1950610210b03848201001c1c500d01030003080d03612840d00000461004450002690344c0103400006000c890098028078030b95840b032920840240f01c3c20030321145100d90003c10b800c0b05003030300540503102607109041d011003143c1c002021121440d80d0f541d40070602c161009000c1c0c60460030480140c1e0030b4100001c1c42894904a41c0600705070300000481c40d00d81c164880344140d504038661250b091034410070300080002c1e01035a00201c006a07100d40400000c0b00060b0400720041e809504601016140c040781c101c0b4045c01c0d40400380d00f10340c042004114102940050343d008040510640b0300f441c0180240c070349006425445400050a60825142400584d1800c00010701080c4080c03450032400c07011024070450250809840d4030350f00d070754580c2c01c0e91b00c42c1c000c203a4001c139000003150b8540010701c281d0700a401c1802a07034001d0b10508008690502300000504552118941c4601c4541c4c800368640c00c16400901c4041e04903894aa0015054075800090703d1003003029100c03103448580d91410310701103030310f030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 507572706 1250 507571456 507571459
    0x35070618050301110a0302090112052d101202060909040302150901060f03140106030c2705010305370b04060c140901052a0120030601170403020a020409030302030601020705 76
    0x4244603044c3d00003482d012104c94503080c3c01d016844500800060700d00b9482850710715049401c2000300b1520400070440140d241c402142d44119070340004928111049c41144e801c108c207a1902d000348034940e25555501409403004007207134070300b188010204d6240d81003664124017513031041078104400c21000640940c0000441b0007044002d1800141c4220300c0000c1c80047d08003035160483d16402a02908078501642e08402c504403400c1da100b031140030080d203d8120700100183c112603100c0309070740f0f80189412660803a00a14500880c03d0210051503e80441500307a00c0341e2482003142c049061070f4203016540650160030140c6014100303a01a00c01d90041d039400c01401003003000c40c00244d001a03509282007840e2140d00c07840310b61402d00c0c3d00492002070308034280c2a005215592801500206207110801120810212401007450010b00040d242e850100f294200c00e840c4040120254682c001d0291046600080c1c0a0300414100c3c3e0050344d0580000e82c000007001450b50701001140000d200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 507573956 1250 507572706 507572711
    0x504110c240708040201051306020d030b010305010f091d0f0105041109060d08131e060e01020303010f09090213020a02070f05031617010207020a06050a1202030135070618050301 78
    0x1c90446030649014020900802d005101c0c01080640e44510155666080035105008289132102c6000c1e40d504541c041190009040c00c10080d1a544a400303002e04036001c5507000d00e217403420084c4000c041c0a51507600080c1e01c0720250302d40489007040221130151002c40340009424106800c02c40700d02400d28001501901c05501801405d80303030300603401d40c1e0035045072a0b15200d202040034440350301c11036072003041c800700341819a4200b44814000072080340c8007612000c401c10701010042e6183d000074868009503880d80d4030100f2400006130052009544001c16a10003030000b688190f049070000004c4500503440040140501d158000d0148043c1408070010882000402e074048140c00842c0640c1d1140245603039a11000d400075015110b140e98000c00b610021901d508000f080ca420006c90f100000d1001c1d5044406a0074034803c0740c0c16103440c0703280c1c450100d030500c002c440c9030101401203c007200403140002c40e604800b0302501002e4800e03542d03201c8424023aa41d49074203125868029500ca81d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 507575206 1250 507573956 507574003
    0x307050a0309052d0f030f0a321b0a0911130b0306060d271407091e1a0a080d0801080105090307030f0c0510020309060a0c05031f0504110c 61
    0x7401a0013243c034804100c403480129031840010908000c1c4c06100c5c0c03c5e05110b068149003c01c612600726070084040d5600c001c031548401e46400700014440030f5000c1194100f051900c22188050000d4110082d0140001032416170b20f142c2c81040311000c0e00c80500740403000c07480c40c01031202028002c00a1400244080c11803c0200c000b03083cae480341c0c0700c41d8400300b0303170b1002000c4a209604400f41000c00d03040e5109094503095040c5030200f070020320b80310b200a0240d4000840c0c8030030113100b000003a03943e505941041d850404102401000c20b400403c0c07900006c1000e4803260f944140405020f4006032001c1d00760980000405004924103806c0382485905001c01c0181103400007040d6a145601444c0c8017001d841c0030842500e40c8113001c14054818081d00840002d4103201e60011070141041504948684c0d5070210f540e4211016082c000e00054001c1011035103ca54445100d280500e100f208490810794890002e0308503000c8040052842d080815180804c91007400100c688915111540b01481d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 507576456 1250 507575206 507575269
    0x1030201030e1612060b04020a2105040c0b0c0c04050a0605120a0b0f0c071506150c020d080f0c16140909060c030411060d0e0706030c0806060703020307050a030905 72
    0x840190081813a0707010010010418041c50b600968030304100a041196181040d8900501c101d5944414000c1c1c0c443d1940100500469071040320710a54100110382c2c0e01c0b40c1450f5081400b540030350031020481c401c010074010325079214828540541001440094003614007000d1088000015000c81c07050f40142d40c210001c1005002415072107400e5844d800280e960718485421035005415000d03012140100d50034180011561010b0141d4000054000800300425801c032107801c54840001d41100c0c00c602800700149102000d070030400b20160344a400c00e1805030b90140b03000803190010f170640c81014820040707000070440d5070034142d85c01c0e0345a100f1441c140d00d0f5250380b84800342842c0031000c000400101844070524580303801000003407c2c240e80302c025546202c060840500c000c5030034003400d200003400c42d020b8404c118001c08180c1301c883c026a82c200800000b40c0102e20240d040d404100141c41c0051030038445418541c1c420746903240514106014062070080c0300300003c3d110044900d421401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 507577706 1250 507576456 507576493
    0x509030a0e0d020105361c020409061b031401060801080d0f020a0803150916020703030318020918070f2d080304150305360a150501030201030e 63
    0x5071030090341d203001d4540305403004a80c1441020185001002404481c1e0030310441c40c0502443d4940d000c602c00e11400081040011200aa00c08140d10100c43c1d50020f00504251b080f1035005d43c000c2c2400101421700009650000c20802000000641d8402054020400007034003140580f000b490150309030343c14084034035514020030303144a0a1000c0b801809415a10070400201c0c107660100100d1b8803420440b81c904101c4817813485440c402c10340c600010320903840c00c2e2100c09000f4190750042080600d551001d5004002078400c48030020f40c4240c208025031030300390030180182c081414211145504d40102410b15129410040e500183c4038801c10504200c040201e08846209030f0400d90501d0159070b0115480090380603d15a000100d400142031114a981d262030b4526501c0520260742c400000002e50907087c2c0c49011803102e112600d0011400c446a402815404101200c0100025840321807451031140d0f208542c894541c0d0060045503494002e000500000364010403002003d180c00e00c90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 507578956 1250 507577706 507577727
    0x2a0c0b0a020c1c0210140d0906060905070c03090b0711030105090d02061302011e030b031002180906101b0f110109060302031905070207050910050f10050409020d06030b0f09010509030a 81
    0x800c4240078241b040b221440302100d0703149100321810000d92011380380047c0500442d102d11040c0c90310300340001d140d0300d0041040c82d142030fa00d0390b00c1601c001e0510120011a41081c003056030a40301359861828181c40034803841d800ba0080500508084c54190b800030b20703080e001061400c060003800741250040c0d820010644081d449030020709460030340ba61046009227401545a6498071172014082c02001c101d50003403e031013401c014801c00501000702440b8454409403219038002801c001c0420302544502c14540d1008210340e40c18491a0607074903000100c0117121001d441c800c1001d505200d1542e00550080001c1085090950643c0f40c00b4018100d01d00096000410781030b2104001002d0743d00c28080a006094020480e1055003002198005140958023030030703004180f0503a10040c82d281095440701620000d43c1e030b080c6418105a62070700650001c01c0b01500c100d0f01c41c04040b00040d060140d080c81012505074a45003031410315485401e584000c0d0204459400401c0110816540011501c4c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 507580206 1250 507578956 507578989
    0xa02132102130902060d0f11041211152116020307060b0307080f0609120c030d020d0605040e1c050a170907150503010f062a0c0b0a020c1c02 62
    0x200140760b0700c031030100074100000d0b00a510500c0000c0584140034158803d4110802080c1300308181040e42c1d40c0f8806038440c5001d001880306903407500c0c8000030801d441119030700e440074002038186481e1140041450b00b04146480480800300b000369800041c40c82ca40303610146140a40c1e40070300401e40301070344a11660001503d265158100c404a58500b00041c41c000d0034448211030840300408035254440c10240c07003280e500e0003410340c82100102500180c480c11b0001d83d02852418251a0032030f0001c4d0321101c0d50503840d83c0c0b1482e0000e00c5075154819410003400b507201402810b040c2c08449040d1103c40c490ba0014014180024055141c0c045115034039400c0e141c1c0c82481c01e0301d8083c01c2d03900d08840d60380328005042c1c24165402089512002640c1240e00312145000c0c60764590748185c44060510101e00c0001c00070800f400c0d0018154002e54441134054034801d2051511405030a466520480d41680983c1c8080c020f103815040c4901708160f040140c0c1c5071003505608503130004a455200c1032620 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 507581456 1250 507580206 507580219
    0x9010203100b0d0b06161403090102070e07030e0d0509010f09030c060c0503070507080d0207060206090d08060d0b010e010f05030c060a031e1410060f0e01140f030a02132102 76
    0x1405110070350303440500f4400c1c00038420303038603a06d4140c1007003c00040c4070000c0750003107124110000304040c0041903c1400c40141c028258183c01e0416065010400409070742c20142c84185424000c04203214801d90500c042c0d94440d9910300c041c00140140804200c038008005058008101040b82c0d0307521002034840919040d00404c81b9070800d907145005080002c0c00034054001c0c0061410707000075001030081890b8080d1a4120b40c2d4944c01c0c0e031030f050b04541e03145250300440c0610000d80d111344d007419400b00006102001a001e251102c0b481c0d0300c4242c100d04400b108036001407080c5080d8040c80b000401040340105982280034000c01d210b8020000004245a19140c017001d41c501804411502c90b80421010042112820003da08812003501e50703a0000441c1c540c04548203224681c902c6040e080707a1200d8458880e07032001111b1b050100304000c55501405d1016070303171807201c800045000354000383c1e002d41c81d81406c21414080b036113294029503000301141c0c802e4103d0b03445044400d1860390100c920 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 507582706 1250 507581456 507581467
    0xf060e0d0f06051f0b030a050f070e01031e05040b1b090a050d020d12021f0603021c03031d100b01032d0f090b043c0510060b070b09010203100b 63
    0x200d001e03d0941120300c4e0711380400c1e02000c182d5142c5180074622402c6001414400307501c542016000c140b0065854a001131320160600d061940a5002007040345421001c1185107a840101d480844000340c904445000404080c00382d210016508240c051001e50025032034106801e000424889941c41411701640030587c5040955403150b548001c0a90409102598500700400003519050380e04482c01c40b11400103049040320401c3d05c00c0c5d80660380c1c0a031061404181040c20000c1e100c15016007101016290340c02003c10315210740c0150394500d40d0100a191010101003028150781a4004c050b04040ca403440c501d80c010307003500c5140024202e40b0303114113142e65107085180c040d002031404044881c1c07c001c60b440c00c0110000b800d500ca940100c00782e1a42411003074207070b100d015025600c1c080701441d040e240851882003041070b40c0c1c4a44540201c4401e150703003c015a09407501540034000d20303003000c10310310700784940180480d5010441c00001c5185242007003551540b0080ca004440128601148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 507583956 1250 507582706 507582721
    0x2092e0f140a0906030308070206010f030c0e040609080a021b03150f09010b0301140105041b020c0f01020f0105091c02070f09090204020d06140406061e0e0114040f060e0d0f0605 78
    0x42035030143c20328800c1072000b1901ca08003c0e24402d020f43d6003200522642300001b4492401c4600c040039070f64814040403120349841c015a040040143c8103490840d42c40c0030713034400100040c2c01003c40f0500b5401802508840817062150801c0d0040c449002c0d410102c84140c1c03054001410661040010041c00310315216007034100c0c01000c103c25031903090740c0b07001c0c40280c01c0c0389209500b90484808a070248015035419403220030881074561140c1c09a070124844d0801c1e490500c03991200341c001841200c003599505012142511400d440c12107680d00301d01c40c6191a41d40c001c4032020480d0460000f00b2441e03207040304501003180c1d41c0c8140301c07449540d1070a0300115600c40d01141c902c8010508180085615080e601d410380c480002c50510880c58054009004d50194003181d0038200030301913861400c1c40d6a50280c2e600c080001c401c50401ca40b0240c0711400e494407201a202800c0300c003281d0000642880800b80070001100420791064070a54013840c0091b501c00071803140c0c01c2d84401c020406448110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 507585206 1250 507583956 507583969
    0x935030c121f2102120312090601150e030a080a0c020a0b1206061201151718070501030b0310021602061c05060a0b030403110304170c0306010501030b010512060a0302092e0f14 77
    0x41f4840740d594102090100510002540c141600c1001c00d400183c03c192a006541c1030003c0342142d90141c02c01494a4046400761029244c0300c6d2603802c00605c02e100550020f4190320087d0482c580302ea10206041e00c2da0707988078010300e600000a0f00c841e45070000c24020402c10307060502c1000d00c6207003c25035078070042d482010080b000c00090076400801e402e2a4034050541056404040c01c5403085c114005a650300c64098101d189401901504141c41e4412041d8081c1d806602201800d01112001e14016291680200324070060708080c10010a0014011025104081d080c54031900e0207803000c1c4540d071280c1d0200c0e5041507060500020b048400985c041c154041c1d0341c801481c206149480c050880f0002c98080d403446811419154039030303240c2c00154111036004592500007002800046c098102809a05400900003020441d0056a036400200400f81c1261480c482c0742080c4080502d50004a841030640302602140c0c1c40c0c40b0b030a01c000868408000d1089100c502c012582d200d81c90340707901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 507586456 1250 507585206 507585217
    0x20303180102190b060111060705120406200403260306010503060f0a0b040e0c0c060c16020406230102010b010e06070c030203100935030c121f21021203 67
    0x40d0080c191001d10b030b003400300001e8002c842c0717540840c6106030207115490020a9580c030440541c0c4a081c101840e140c001515210b00410856486a8441c010700e041c0c006100c80c580d005111401c2e1a40d514210718155442c0d00c0380807150b04010010035180414140110b066a40c440c0c0c080c64003603140e0345c0ea0000280044d18582e0074a070010985400420b00109100c014820b80c0c41140c003d10190310303608a20b9906100b0030b0890443da800000204048040c2c01000f0211411100114000321003541c00003421a80154045203054903400303002c2c4a1505498840e4528050900080003040c449000103003900c409651158403074840051140d0030060109182406990050104c40303c00303c1080400c801041c1c0c50006039901c5003081c51100041c140991035000c0b01107015002080c1016861800c1b501d50000340404400b103405200ca48104040c00313142610034080f00004911005940c1d03221003110100b41c001e41140300c183e0032006207c0f0313000d00841030101e90582c1e180b9030015411844c1400d60045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 507587706 1250 507586456 507586483
    0x90b010608010503010b01020c100c030224070f0c03020c060d090507140301051003210908030d0c0f02010c0c02060f041e0603150302030a060e0304120503130f03020303180102 77
    0x400004240c2541c800c0030030781600c105034000c2000c08643c0c0010790760380300c06c1d4842c190322105050b040c00c030051090711500c140038800d00403a450070a00c00301a845041f03400d00319461101030b403810815410382c4040c2035101c10b1164208284103000d40c0e240251140c20f0b0b180401d0050800064441c80441280c2c89442102d4120069407030b00c0e070300e6064030510b900540c00d0352442907003841c0104e1200c0341c1680c070110480383e000c803c0500d40307001c50010781e191070034031400b440510003507450020300000d0170f01c02810005003241d00000c00c000034420140411680007240021a854804c00c14051500300038150149034044800723a4a070796404a80702054031070b0740c00c800040b0516a800070782801c203401010707040d52904e4600744580000c0c4100c4072058109480301960503400700e44104045103e6500117980300c545241603e20707098450f078001d8680411040101c80c0c41e40f00158025114055242c0c07000940820080ca0010700c2c61500066604e00410043c0b914a04a0002952030703603000b000b528680c10413 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 507588956 1250 507587706 507587723
    0xb09012a0b04020f0603090a0b0601020304030c1401170123061306111002280c0203030c0304090f09020a0b0a1b0f2a0603150302130501170c03070b070609 68
    0x280d61420401c00301040c0c4049000f40d218440200c00d919004d0b064038421200c40c00200503001300c64030380c4500100098100c0e0f06501040001101242e9100305500285c41400c6040b08103e8001d000101559602d980c02500c02d4001c0c00140071310b9800726080c3d02100f0148071460142400c0c0c2c5c00180c09841002c60044208108800001c0d21681000e408000081d201080d101c40c1110f2502d07142c20391160407006181d624002d0a00301c60101c2070f203800b404641807071804d04402c1d5410350101f80b035584400c2c85440e00e6480481d08003c011003d0041042003502d89400b80404a0943e011405109107805641d400650204a14601d203100b00034074070105000c841748032481d094905000611902002080e5082401c0d0300806148442a034420b881480700d51051840840c9403180840c0200300016184038140d01840002016030384500c0101a0300014810016481d49003171031004c0000c942c0300349807185410a04103007040341d07408a08a0708941e03c1c400d8080e42c0e1400c602e0b08000403c20310320018070901 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 507590206 1250 507588956 507589037
    0x130507020a05070f03050303040b0c07150b10090f0b03190c03020d060608060a0510090b0c0c0a1502030f090d02030f011e020f09151303200103060b0901 67
    0x40d80000d0300800c80380103406640201e501c071100082104420300010304568400c0001c07030006280c3c104041da00102c032004840c20003e0a6541c030151031214002c4040180c1c0300c00486103e480e0000d1228201815824041540d6160800d400c010078814403d044900d03d0100008120050340124160f091440400030000700116400180080d04101c40d0b000e041032500b18041900c6004081090240c90000c080016103031401d001c01000d040f420310340808018406000050000081c03016010b5030b880c0e1800303414002e4401041c02100e03407083d4050003c5d1b048400132005d54035000310444440009103074070184e03240c0840340401d00500403542d009400d8828885554101d20041d48840c0c190310b19910414501044241840144d01408145d85001c00301081802c0007860070880c15200c41e1b200c44592800d201c81103042200d14242a0302c1901c1d0b0380b100024042d81e4003001e2007524200d00d42401c0c100a86410030408001c2c50040e00d14090600c42900410036030640994101054540c0c102c040a1071039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 507591456 1250 507590206 507590221
    0x6011e050d0506011d070806040b01091a040321050d0203150a0603200a0f03020705160f090b04050c0307030c0e030d0f0305060402070b0403200d200606030c010e1305 73
    0x83c0030900c078040e1124142c2034504004a2444002405805503035664403194850004003c001c0004c420f07000c0c1802035607000040c1030380c5103035004e4804040213040c46880310b2039820032144c40105100801102c01100d00d03481242e41c0c00c0002d540b034400d0304800041e00e070380d110881070700000f0741da22140c0d90000090b0380c0040d043c1c0e0306400c100b082800004c0ca1403601000b40100407040d0103401912000b240c1d0105c80c0c034144500c02d5025280440c00f07442110318408040781030046104030354100140c0009000801c0c059241d2070700509204100640301000b09250180101109000140c8101c007015140c6a958004500c20f80c1c0c00301420300010b050b40d201d0418060b02074480901e0b510b00d0b0000c28180f0b03000a4040c03038144240c0e44020741089203d081566a43c0e01154611401c9441c10001d0405002c4440703842000c0018204203906511201070380410f0b030804078044108140c0310303a0990300400401446890214190f00000828200069044040d0b00000d2150342c00e03040d00100c6610303180030040135 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 507592706 1250 507591456 507591463
    0x6020906042607060e0409060f020f0703180605030408301f03050a1410020d090b180a03080a110c01051005090907050f280515090306011e050d05 64
    0x41100d0000b45a4000548540aa848108501c2181d000c80c2003020b80b4521810140c0101081c94400c180020300340708046006400c82c0c00442d2810001e01c00030440108058011045c071280140d1600c0c1585000e1800300003c0080c03200410007000054040385000f494040c0e5406451684c40000d041c114908401c01d45860f00007048600c0c0c0b81210612038005500380ca8400820207690700b2801a1001140c5c588803030000014064040c0c049220380c40c04064211410320241811000e041004a032070701441c100780f5505080580208400136521103070506078640001e5030703800103505090402942e030f03440400d00300400700d00102c2041c01000182c00700c440041035010030301c2401c01012440c1d03415110030520101000844000c841940700e200188814a401a0102203000004000351075480152420f00e076102907544800e40745048070b560078030081c6001903109200c0d040c4020703c1c3e03040104c00e41c0001e80d00d0388180318100c001707029882000d01d41041c00308540c0181c50007825550030b08200d4030300b040d034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 507593956 1250 507592706 507592739
    0xf30040605060607030e09100312030905010605040b01050d112106090a090c060c1506080c131109040506040207020406151715090a1b030b0a0b04050303030c03040602090604 76
    0x40d01807420000441c00d03d8030000b604c003400d8155858094090a640c10301c644890041c10115000c40e01c0c000c0007000074494840307a00c28040c80e51703020402c11240d241841c01d6134450b0700b166100e24201242400d00703903808170aa07400c0708940c03480407510059040d15540d252040c0481c1400888106a0b103424001035150007601600050726030030003a07035a50480c5001c4030012880103003030401540781004000d220301000d00429000d040100340070540c0d103000e00125010303035002141c10b402c82403800c065494405034000c51030781e0072003040c41500254a50040f241c414001d42500c110355840226801d620b441e8142c41001c0c3c2d000e003042054544030f844000194490b0401440055410841c054101700d400003014040c4000c0183c1072900071030102000b41481004100c0310940f6500c0d0b51a00150004503051700070240280c1300000e02001035814003c0f150440d030044400e00108200420640e200081140d50180184c1c00d92510f0340c8403460020301030311031b50f80e4141c0e04c00008030303001c01c03152070101d82004c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 507595206 1250 507593956 507593963
    0x607020312060406060801120302031606060501020d1809020a0908010f020304052e0207030e03060a0e1213060e15031006030b1c02040b0a050d080304031106010b0f3004 74
    0x10982d1580100029181c07503004180001c2d0301d00004200c4000b51429040d8a24806e0061704e0602118200341d5048844083c0291005030703c60408000c1543c05220440d0010514901001054804075001c224001d2500c240c45d420703580092801c0000784515001005000709400a201765030342e0001500c040c0d0070030780b0140d825000b030024199807038145036030003511169810074200320700c4411070310300009422044056081c000d04a90070003281c2c0d41880881e2162150100004103500000707102803405082c11001019100f04000381c914511030560024100c41d098503000303082c03003203030340208002c00ba2002d010000c6000200501585890340d5001c40240c1d21181d6042101400110401c8044c00c20300c07a0104c11040329400d09005810550410740c003d0402402000b00315543e040465803402e81800b00703481060010080c0801c050740100b0780c00240003804024162035050010000444c40b0b84e4800b0f0402e4840004d00718082c40c200710b11459408200a1501208621414036005030501103d044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 507596456 1250 507595206 507595237
    0x705010f050c040f15053601050f09040c0e18060f04020412170f0403050a0b09070302100f12020f0318060709180905030c030d18080712030e06070203 66
    0x81c2200b02c41c106031002c0704d01c085500740c1c1c0750b85001140d1441440b80c0c10203a04011040103840c07400380d4104080030112078080f20f08844601d00d01c41801c0d40321181380d0440e04204003000301115820404007035414108080307a00190440c040b480560788010000c11494209445943c40ca9400c40b000084078481c91041e9000c0002440ba10104003c9101d00c0c02a0070310000c0410745503011411002004482868a0898500e0103d02d076000e565690800d51046803564050a054001c00820040298000701900700425031207066500041d1071904004407041000141e01c400c2250034416104071080c600781c0541107603100a220082c0c0c80d654011590550b07000c4c903841d844505070b0000124103110f0347d00c0b03554006c54141007282c10110800c81e041ca19117056207503c0582c0c00304400b0302c0244083d0380f04c7d00045588240e16100201900d245000c21034684100c4805280032411100440d009590300c220400031120020b1802d5004201071100b8454038428030301005402500000100198404032480c17 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 507597706 1250 507596456 507596461
    0x50f0f010501060c0b010603020a0908191a010b0405120a06020d09020f0d26070501180b01120b0604230f010f09110d0207170a0504090e0109020d03120605060705010f05 74
    0x103a130b148450300d4000b0110001600100031051090b07010308803210039440d2641109658442c0e00385441c05440180205860300c610183c01c0009141c4075203820040c0c40c0030b05041d50305d045140c10302800740d44201806541013088a1001031400d00a81e030495038001c004540300c4400c208403400400c6641c0049020f4080c40070003da052410807801440c007135010000d80004988007260b5100c0c2c0e010800200f4440304244503038000603800303004226070403050002142a440030390520110300e1006a0100101da09000048400b0036152910180e10903026a804904200412100005241203540c03071081c6401c400280896a102c4c2180e00d41210700001000c10380a884540c003104036a840007101c1c0107079408204190541c03a441d00070b800403501407200307214095800b13a007100c6c035584401c5241001940008061007207240c0d620403001c080c42072a0082008080c207901150a00c1030405c006130601c1030803003a130910f2807400e80040000c2c09010702a151140350038034045010308103891410507030500b841c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 507598956 1250 507597706 507597719
    0x1406010608130b0402010e0a0305010603060c021c05251b060e06090108150301060e10060201061203020c0d150e03091c17030a1d030a030f060609170a050f0f010501 72
    0x4007001c2c210742000c42d940306078680ea03006503115081c0a009580001c220700c00040851000c1c401c013030045005030004038003c5035040d0001e080501c0300745401c1d407880c0d464140c1c0d00282d0303009080c3c441c8500700086145611714080500300841c4004d02e0018050400d0202540300350840c0c803140070845410752640158041d0940030400d15000d130141c60360014030764200080452400c5500302d135030500f000e000054096110780384407040403070807501c0c4d03d050080e085041121560900c100d070700915400e00c600d007100241d580d000f134603042c0d81d1585030711803511480044c05105141040c118030344441442000b01c0d0800b12405901e9401c035614452064180d100d044500e01d800340e6070100c00c203034400e00858002c50540c0c0e40c0c05c526003003c0c003003a824a5a072102146a10302329a40213107043d00a0700295159800035000030301340c40502205030400c90803c0010440c4a80052030041a40d00c01074806042012005d6040d1070b0250261014040c1e12849806400e04071000c038910000384203440003403106030780321074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 507600206 1250 507598956 507598981
    0x60a031e020301051e12030403210201060605120712020a121b020c12010902041d014b2a030c080712090b090607120501080a0b0c071406010608 63
    0xb0a0b10f8100d00300c440300050303290105e0800704051000a01040c1d4442c4062078544c0345420540044511104510031850103c0c407201030352504450510080c00142e042120040c11030240380c000c08203c2450102180e02180288051515602482c030b0464032920f0703008004005017190915808602d140000f40f8902500b840d482c12800c030216001402e01c4201c0794280068588031100d0a803155580390358400042c2c0d1107019446038895000840404110890492800c40d0203400803c60003044440c5159040081000c00b0b140150342400c0343c1c280b840740d1040709003e03407000030300c05459240303820079217411101030324118450748130554096500c502c1c001c1d00603822030f1403240030480441c0d10031000031500b901c00d00b00c11402041c442d0010400446035614010040d8060301d510b0040d4020004101e80300303502011100e1038414403001802154076200d41c80d500d40c136003414054000e40000c000076954440f400100e0f4640d60f032255000c03080502c08004581c546400b8091800029414800f180c0b030307040e100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 507601456 1250 507600206 507600209
    0x50a0302060718030f0305031f080106090c0201020a0f21050a0f0c020312010b0d02040308071104051e0103060f060806010902040602060f014e0204140420030a02060a031e020301 78
    0x1d811701d02e504600d40c8040d203c5802c010b00d10440c03240701c024543c14265944110030000c2110100200b1410b0820007140b0594540d100804c0842e8810303c140791400758440140344071030070703035040c00b0740340e1012034202d120400f0102008050150030a024441503a00c02c1c1c1c80514100c1c1901401c00c0882c0300132808a86038440c010880303032540a000014071a00500000a1282e84040340006203000e07a2607503155010f810040c02030b10582d280601d10103050400e402141e521084d041402d8440c6c00c2c09100c42c0d44050410700000d80019515500c4103401000e9512100c0600603207002c0391419a0354010b802d0181d441406032800500601303010545405a08085506a1b1031000d01456101000c003e144907485c002c03081611042102e1b52007105009002030518035070f60215551015400d8140180b00603036070701d4020300c94400c407001c080101090344540030f042d03000020401c591000340300c030380040e2030700420000c040d41c48034000460200494040d800700640326510704101103903c03a002078034070490109 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 507602706 1250 507601456 507601463
    0x105060a05040e101d1911070311190c1503140106050a1e03200c030f070302070b03010e01090507090b0a031113080a0b01080a030f0e0d050a030206071803 68
    0x18801400001080c0000a43c00f04c0980c01c40c0c0c1c50706a0b03400200b265113500d5843c100c0c03804040001d009050109900194441040c2601070007045070741c07000e01109204a42c0d01400f000342095000a00c1c80c810b1141c0800031400050b1110032003440e0074a140760906030f114100d41e040b1440405400203009004041000000000d002035981c0f9103502070354240d001014807401c20035a140d200c0305104480d6501d0660750700b1a03800290400004200103103600301d405040600c2c1e40d00380000400c0f1200001210040d0102215032a1504280d18080c0c0c074003169078129002c2d0010120011400090441c80141220041d410a1100d07469901d01a5180700701805411291001080030103081400307904210f4000112000755440d0014a01c0f03040c1c1c4050541e00910050b801c180704039000c0c000d511102501501c81107001d405000346039a80603012400c00c02d800028880507451500051361488401582c0c0c5030400140c8000849615000f9100c1d041100d50030080b82c2210381d5022017072402405080ae9991 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 507603956 1250 507602706 507602717
    0x40f05091006060816020a0c08060108071d010311150403050a11100909150503121327090305070b07090905091504170403201008062d030312010e0105060a 68
    0x1504960080d41704011803d15055220b040d4036a000221814508802008042c0140c803140d4104a030322401c00100381e0200c6603441e161102140400310440030903044960043d4485905041031000c2492203480303c41d85c2d20041c9021800009200001ca81000a207204904440300802884e0410203504840140c0c40005a008a0203004102c0154060701403d00104510340030b050750354000a250841041c01c0c403404081c041140c40d4100c0c2d2041b45d0304050324000d01c0121520b4403800c007c2182005003074601d0b5613141c465429009060250044641164110300c882803075240c0740401a100310381910540d4074852034000080c0c0750752404140c0000d134800e8900d04446c6d5840c0da88644c114031150076075820b03841790100000400030380b80d0550b500e59588511400161030300a401001b0742c182da4040d0346410701059904000d084c0e40d440016050307100101c0081240c041311000e112a0110403030000e103405202c00a01d06040600d0b24060504039018003009100d26030b01c0b1402e101203802203e0846c4003191 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 507605206 1250 507603956 507603961
    0x150303020c10200309180106080705130f030615050a0b070f02031510060e090103021008130b0a0b03010e01110a08071103040314100b0a05011805040f050910060608 72
    0x34040103100d044240500c0d04003e0048200216855640f00303080c40740d4079a200141c0103085080a84508126400284910000d5854104041d00a540052007013081040c00600011050703041107844c3c010303068550a14103141d860b0300d00307400207042d0281c0c0012040072002c000101498503003082d000340c40600483d9400c01182d50b03240d0354544401d00089915005102e5004209081940d4561007024159000000f02e85001c80160008c15081c0000d1302030040c0d14014009a00e440005c440c0b40501480c01d201181e6400035064200d0700c4111008101140c1d5006110414146070451038103800110000c0110540300b141c0ca81c00c88000c804540d0400034244002040a400b410074a0f51114482c00c00792020360441c9605030455000f90001c840c0d04040079010070809808100f11100307198421002c01589400ba8002601c28034144200303810800703042170155078605140340c6800188006401403000d9902c114110f0013803d011100042148550b01c2c0f03013042103410340200022141640c90f6030b50b058 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 507606456 1250 507605206 507605209
    0x3390c0a0b0c0c12060709060e0f01141903060f0f050f0405040c08100906050c27010c15230f0c0a0302090603100305060709030804170f031c150303020c 67
    0xc0d000a142055580903503880034519484a001100d00c690318100540b121b86841c40f000f0707000304600c0d000701c4e08008a00b5014400d60711180300c00c1c40a071200b402c001028030700301107400080c2d1040092000c100558039801008154041d003018099440080e900b01c80c1c180c132481c088a101c0740070f20985904c00716040710300e15507040643c01250458055012010340d42d48500c0c015280082e41500c1080c2580e81e80010018002c1a1107800d42007040305140b0340c0f0b0714858420702e800084154441c8400a804408443d0190b070140041c2c11217a80d100003a1607003000280c12920040059601400020540090500020500c0003005126000800d420251611140c003801911f0b00420200030034141d08004150450f034079030010310b2140041d4203841c0d1a140c110301d407550402c03c0160801c028040d02c1c0f201400018a40002d44040d00e05c1c01e0171241c50b005850f10504d00c2c101009420500d140000150120300780084803000c4000c40e9009018802607048400406440354684806030040e00075041c03c0249 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 507607706 1250 507606456 507606479
    0x206011a0d091a07120b1503060909010b0d0305031b03070c080702010210290103020a020304030f02150703081f05090109051003060c0e150c1e03390c0a 67
    0x7410b010f8100354418200328048456045815120400412480b03454032402c1e00445c01340100122041c0c40c076160303400c01d0700c006802e00d00010300182c0c80ba03555040001e0b8002c0007507000c9407009000034504420f001440c00d0290180d4810341e00d00308040710f856020411a0a0720003100d005041032755444091404689900f12150410f0300128110301902c4221004502c0074000d00200111191601090200c8080750309980ca40c03c0348003a042c5030040c044012020307008010750707003100d411801d600581d1a00c2d1001071000c0551643e00000c031207000c03424000381a0700154061054000c00d0000722000c070940310a41041d5224400e103648044010018401000541c0040d500408241204000340791243d03138010540345018071020015600009261a42c5400a0001540b24100c00d40e5031410503c090010b484076843c07030400780c0d100c49008420030648001c000311005034040302f6000d0100d8021202521040c040020400c014448201d603ca0102401249070300584c4001071110700c9961508450401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 507608956 1250 507607706 507607721
    0x9090c03150c0c0718230a020703120f05180613080a020c12010509070f030c120f0c081b060a020c120c09090a03110a110616050a050703030206011a0d 66
    0xba100c1030051040300c8500704040d40142800c415002e440d1a0190ba80100b00c2d11b600c2070440c4060700c0c0c0030200794188011b0354003a4010502170710140c1d807100541815607090b24240112005281b50007007100150f001a1703c550301405c07100f400c2990009882021556901060301c0f00301d03015540900b910001424180100229081c500543d4040480c03400090f241c14010f8600080c0c3e651030700704000f001841844132030003030700e003041d0102c29041c110f484242d00c2081c280034070801048a00408820b109510066810156000c1070742a004c40e209d0041c10b403034103018882514061607034000414186001c5c81601d8254850342c2c0103186422800d01080b1203005031029007400e902500240301d0070f50701c4c1c01021034131a102c1d0000500c04102c00385001419034004200000158000c0c80071a800195510940703100201d08a443e60b84880f110049102c0c8505003100c028500d00c07641c65100100080422524104c1e030280c5c0964155a0b611400d04100c07048148103c08405410043e144604070709520000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 507610206 1250 507608956 507608971
    0x81e0703021018080c0d030e0106030f0f032003070501110a1b080c0f0303060907030204030804060315051e010f08010609181103010816060f09060c022b0209090c0315 73
    0x1806103030f1030b201c1000e10703804811085215040040c1c01848260503014a0b50710000c030000030090546940c50395002c8138840b02008043c0d10b041440c071030916200d00c602980403403010241c1854081c2202d543e980c0e0790310680f03013204c00b5400c250442120304000c4060719289442d03a19098030708040c402040b0f19480c1d440008942d5020300740040c0404c10002c0080701201542c490055607242070890400915000040100c1304260041005200080702d030000d6504aa80034100031a945070b0400f0f004200c15603507009203030004920494070800b1428210311101d50706003030300d94038141c1c0015101241c0e640c038240609004034002113800c0018506821002c0c0c0c80e21800d060002e003001c659280d00c545940280d03c0609150b100180c01410f0100d5564440003e017110300700300300040e9500c500980100364a00c601360030302c030441515a0554440f12204104460300007c0241c039001c144d2201c814091220704103a004a400600044801e00001a00d400d0444010002e10300d0640098280b455100e00402c0701 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 507611456 1250 507610206 507610241
    0x70b060103110a05070b1305071a0f07080301090f0501030b1515070507051008010617040201022b09050d200d061e14060a09020c010e0a081e07030210 66
    0x24002903075144003500445166503142682d4a889046c0700749144c00185c0b00f1424650b50300c01e814001400000c4280807666160200f519142168080f07030564060542f44100706040040c4401c104440a0700960681d54440380070411179044034408003c4440c2404010081503a0758081b07820b0081001c00d4400c0110014000c41d91031805c01d5a80c641904a00d000300c58550190400703111503c1c0045d03030f464454080345400e9a41750714040c0000c200307100007003c440d500c25482001c101035900c08d004c034610070b102031050900318014413040d00940d2805501000c00103144504041550301c1d240c01040c0d09250030050320b028182c1111b44580d00f4902c84656903034028800b012110000b40310b03001d1003100c01c40c2821640e40c094940b458203421340785e492880d4841040060200325a660ba002624030a650300c5000041e1922880c2050900610502c02c17601c0c014442c451050b400c1001040c0145000b102c02440d07c008021800b0081915014140004016800454210100907820b5104040240084014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 507612706 1250 507611456 507611471
    0xa12020c031020120709080a030c0204050c300c0c1f0e0d0504090f2310090608011d060910092105030405060601180513020409020a050c070f0605070b060103 69
    0x1003504950160748004e00d900d112800b00051180c0140c01800101102005801460760960700140000c445c00c0b4000c4c032a5a450000c01c40080e078200941e6039941c13082040d00078850800642101c4100744612410560045000107540c01030510252056072030f03400000c0c2040d00504842034000c0282e2008414095038444041c10400700030081800c912100e919803950700c50910105009036014510152059410880c0032046480d1524059100d0350641507405003980f00c5400c1701c007041c10035a004000035400c2c0381d40418181340660007480c21804114541207a03092509030a41c0341c004c201c030800116081164042d901d101c0541000480a21445450f0401d410066502400c1945c1c00700c0e000004e4008010401040401c00400d5082842400c013100e101503044c5039002540d4080c040c60b03010350f484880605034000503030180e5003c1c2143d140705640b1404518001003882e0428402130a0501c580d910005000341341a2100c000e0305c200c0c1e82c07501e25140c040c1d01c80a0710741c480034000c01c0c1059070746c2c540c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 507613956 1250 507612706 507612761
    0xa0603020d15030c1e050f01030509100e25060806060c01060302030d0309140c09220b13020a0e06090a0b030f010515040c1403040b07140a020a12020c0310 68
    0x7000d00142d44582c08514006040c14176440d8840c2c4034202050101818000c01d00242d624405280d080f507000341783c04942c95503030211080c1044510780e05407088a0034003980030b911071400309455005005461030f01c00d40c06840003007005e40050510802c008940d0490200b406400c1600081c134800c10340f90000f06102c1d03565408245003204454000000955850100041198401400e200100a440140070079035a0b400003484004c006000081d160101c001202810042c07407100f001d581d03030490290350403480d01f0810034003c8005188200e120342e08104d40800d00b103100c8040c0d01c1c0910320140c20415030b030751142c25801c020101c043c4d46503454484c91062917103e007001d0040340e10074821410328032588140e810078807040e613040c10380f2202032040c1d030015a2812040001070700d610a03002158000551200803081c0c0b1b160203c005803407100d40c80010000b0030142c0015480304013500c00d94000c95454a000304c1240c0b5000204031303207640350f0400c3c2070b440c0b02caa4090700040c609500902810301d20108140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 507615206 1250 507613956 507613991
    0x6040611070317120c0702031f06030c140906030f06040807061b09081902010206040b04020d0213020901120e0303070c150920030a0305040b0307030204090e0120090a0603020d 77
    0x80d00654900000038041c800a01c1020049801a2805c0e5007542001d800da40003a495800b03000c01018000c842c4100000c074011240c000074001d6400500d9a05555100d01c0e2803401c212410161500400c920000b06c4e100b810b0000303c6049070103581001c0c04160301e4036030b40e80a01c4e5104010507560b040d11000003100c00d0b060b0040c0600c035210f0a07101c10142c140f0708010907061500c55a0070b400100c0c410b020351000360f6000f003030490344940d00070345d00d1007142d84038400260180c001d1800a5007000342200070200d14032596009150300c80098a03102c0000030254210303010750f18442c0592100d6001400443da40502554044881d07510a1202c603041d480ca000341081214403203982990740c0d50754081460300b02e801800c3c0708412444143d010300418007858801824602c04d40c842d401e41c5c04000800180200d04c243d042c0da026050440b01403200341840710b111406004110301c4441c14441d0340302c04840c031407c8201190381064000c0c240d600d61518040e0300b503000790804440803050b19268000d00c2c43d41d40b0501d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 507616456 1250 507615206 507615233
    0xa0b040b1309020907050315130e032205030715080a0e0634091205030d0213031a01032411120103050f0f0c30010c020d050306060406110703 62
    0x140c0025402c2850040210640020382030f102070201c01c0051001c051313940c3d0704070005000705491201d0000e40700d4158900500703041c9036038110341c00081100b0203459010750305043c4807444601040001501c1301c04254550000c4c0c45001f07030b181c003882100507045004244407039001d1607182000a81200b003c607640e00f4007404031907018151026040481c201c281a44000084130800c000b4014042d03452400900342c0031680c041c200b880d0f45400206020004100119910310020038401d54440e5900707008082c0046542c0000c85500d04491012521581c40d050040d04903904402d0711190040200a0b00ca80035031064546e40c070310703500d46003200e00d000302c00f030010700d070721508601726000f550300d9820168180180888015002e801c4940500d00030b0750001040c141c0300a00300c8110030030044c1c840411070304e40b030341c00101d0489c010310350401080f480041d40103113940c03803498080e6101144d140d4000c44180c0300840c0c105a01401c24882400f402e4811011001100134400c03c0741c140c1501ca848900d400c000c007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 507617706 1250 507616456 507616489
    0x130e1b0f090903031b04030b0112050703120816020c0906011b080313060c1407170c010507020115051008040b0c1e031f030209071809020f040f1a030a0b040b 69
    0x41400b45a00c19249a01202c40001607035900741b9042d0380c2da59030810410b101d5005c0e41c45010641d84d0030f024041c00317514019070780105507500307007441c41c0405401440c5c01c54030b0810b000d00e04410603d01310b0003c50032410600c0c0040254555650708001520705008165240c0d000e5440d5405040006003004001c6000b044602207800b0030070528504034081e01d00c212540000c0003940d44660f10310061403800e48290b03c0e030010640c000003420900c4d01d1550300418184801960a200a1040c450b4040d4084040100e82041001c8420b4450b01070007001141c160b0104002400302e0009004540e801114907001b8001e00d01c1c00e071414564502c240c0f1180d03120a104841c0c40400010300504804610109004c00c120202c80043c492442e0001055000c000f400c45043c020044c0d40260310100301858440908210842103445811002d900c0440c0c0c0c001e03005041032100030301004514914414034404c11032030100001ea18507174451000c01e01030b0802c110407035001a101c00301580240c0c1c1d008400800f8602 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 507618956 1250 507617706 507617713
    0x5100305010e0a020408100504050109061803080a0b030a060e15100e010905010608070309060e030a05041a0f1c0609050c0909070305060603060d022409130e1b0f0909 73
    0x6156240c11200b00c007030400390419104010400104c0e00104103034101c4144007000150700e5807941807403405401e145400904e114949000000d18100143c2544c00060099a980d1081da0b10000c03c682203e41050358180d140d0b01c8540c41900003a520b401040a00c1100000d6424102c1404182d189a0b2015103c100341c001141401f8020303d191400c1840c0181082c440034000ca5242c1703400a00701c000301801c98400c01d912420040d05114140e0401c04114080c2c10440f99100d81c2d070080100b9503040741c080d0b102c0b2440744400c0e4041580000c4195081c0c85c25000c1c00720310b44000281c904518050f86180e01202071340300c000014003803034070303114562180054032206a83c490f444001c100c01d6420040202c070038107207400301b401003d0315810156540320009aa0100034890a40001604d04130403a1600c0042c10301d80030010104100d52000d0300c0021000d54412804080c2ca045502c107845075a00c4040035544254401800300b40203001a600c0e600019006146c14901030020600f840c00803030340c00c0c44a60 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 507620206 1250 507618956 507618959
    0x60d060906150912140f070305010b040b030114071110050712180c03060506130515030c1008040605061203162a05040902041b020f10050c0d150510030501 68
    0x1128141240d415040c6880c1c54401c040c1480240a00850704c280003811850403000c1408580008120b10200106071404564005e036030381c50881d0103000780104041c0074a0501d40d441da11418140505030700952100d400082e507660305c000c1186c00c9042d5114501c114400c450801901c01101d109482c042d1a141d44c80b900010461005d42e400d0341c0202c050310301204121242070010810381c065240550b83e0114011030316841d12400110043d02d05c00c001c0304054986000c0c8440602c00c0b241135001c5140603000c0d11588942c80b0b003000141070302416a1000f045480740080c0010301698400c039440000241040d0200840d450309074696004209055140e030424080c0d08284002c0200c00e0307010303070a4018480b412105c554050b290118039886480c4c0610b0b140c82c5400219580d90304240012602c40052400003400000c00940c2d980c0888409105402001c00c2c030303c40f84100c1d0043c03c0c402d034034412000b0300c4d003e09096204014100f006106e401e64016007000f154a0782c800183c442c2141143d0313270200e050b5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 507621456 1250 507620206 507620219
    0x906030c0706330f1811041809060605180f04030320070309470c030d0b010305040b06100e030607020d110a02030d0c03210c0e01020a0c0b09060d060906 67
    0x60303c20b803c440d03c0c141020004210100c1202810003014010000205507050041075060250086800400d080181500c2080c80c0358055485003140fa03000300740a000030390303480c42071201086003820300340a44131224000804001829074110382061191800145003111030035408151802490342031005000061000249644040f03004043d000c040c4a032201c541d0029a01458005814101044d10751803281c12070f8104490440500c484441d800d9003665511144281604c1c2e610150112940314a02a030031060395219105251055512201d051400c0c0c81d13240c1000403d8046082c41c01c10030990700746e13860443e00c0a00001d401042c031a0000c140b03940c05480e003d071941c1059103944074654019276000f4050ba0740010071300f90303600040c20321900c2c0001c241011900548030320720310301c0c5c0c0c15405011160100c0740d950214070709042c0c03981d80c180e0b180e4000b00126180c80c18941c024080070040c80040c0000800724000300711841e0001c00291600305a10034075416148030307030b0005060555480c02003208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 507622706 1250 507621456 507621551
    0x30c140c15070224041710090302030405090a05071b08090d03030c2a0b0714040e2413020c010213120b070f050a0c150e010b0a0801020906030c0706 65
    0x4540040610600000716074818030178000c030302ca003d2040365004d402402c001400d000000c0d042d006950240000320007824040d581e61b1142c8a0b01e4000c901400019070300098910640340100102d54501140c00d524206000c1200d03004a81501e00d540c0800400071265141c030907034a980740c440d17100400c1c0310ba2445800707044c1008400d0311309802003140b6010350418200c9148442201d6014901036000d48810700121100b1213900703200a00b00707400040210790322600d0306516200e260301c51601409802e212259041140901c1d0050740c019001490314101c100301c58000c0d081c1c21340c100b000142402071004241100d0410766101d072040c11810900842840341d42c0034542da00050f14244441201c1103a00c0c02407891040c4100b68003080500c0c2800002c00666003413810144c1c221074030a01500042e4881d480c000c04904a0251084280040c00581d201041c001d40701c22207001401e490460703503404240b540507403003118225026640c0b850320304905026140c1ca0581151220140f00042c1803503180c0d11103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 507623956 1250 507622706 507622729
    0x513080f070f061d0136230f09040c05060a0c170910030f020913050901060e0601020601031209120602030f01060306080d050f0d1409010b0303090a030f1401020a050c1009030c140c150702 82
    0x8881e52600100a07d40c03180c1142c403461100c1580d41d081a640c0314200150402490b030022030740b156002403040701459004851260701401045014800c1d50058015601d0344215118241c000c039419540708031580c0250302c424881c80d002c90b030140c6440d926000042c10b40b1010040c2c81c081540d15004d2001c8131001748139600107040c2c02c160101d0507061210020b0341d9800144001040d03581112462720b000c911940245004101c030b00d48480c48140c0d6454640080d40040f2444580440b0360000081e410b4420300036901140d40b8540035004d903030038101084a07558800340040841d50302c00c0142101c01300c40303489954646503010b9000112030800c0d007006405e484210201038400d41c03042c0a02942c9560f01400e600031a90710511550080340607240005203034030040790048540d40302061000000f50808001e020032240340301601d1031141102c0203030080754003090020300002e480d240840001620051420950350400080700d03500002c0d880005c2d00102403491050313802402003103090071420590380001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 507625206 1250 507623956 507623999
    0x21b0708010b0603060d05120d0b09340908030c060103020102160b04050d061409060709060c0b070e190b070b180d0513080f070f061d0136 61
    0x200d59020b00c00011010700020b40f034a0b10036150700c4218001c01204101c0c030305042c07509100381500d42001d02c0c000c1d002050007404043c0542d448070009604000941c6410808541c40b660040342c00d43c00141800d600e14004801000f8490041008568040108054000000004000d1001390b0461000a0401941c0a081d012038041c0c10014401400c0e942c042d0b50941340c5c152440c1141d1129400c0c0718000e060a524881000700c86c1c0fa050247c41640440c0040c414004c079255855040d903940e03800c65901c00d0001000d0040324020010541c128840c2600e0191218001c01c424500030003000214800003081d4000d44248100290713150800c942e81c00b28a44c0407504500e0710400200c08031250707032a09080e10303501c800c03c6030020310520b0003e001d441240c0540000401c444000e422003a40f603075121900d0080614418035210001025403081ea030444c0d0002d000d54490400940d20713001500e5646006101990030181c416005501020301c01c1e030200b0400302240c018000d94600054035491701e14041189 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 507626456 1250 507625206 507625211
    0x90a050609010c020c031c211d010506030a08120408120a020d0c050a080f040c0b16060e0109020102120a05070b09010b13060b070b0402030304030602030708091507090308030a0f021b070801 83
    0x1136001d07040e61003500107514800c0c1441610b90002c079512101008e40e0b02100041203142036400510081c6c007601603501c0c800000002c20240d2030b0503007010740d40c13080c0d010300600c0079004200e12511141a40f50701ca41043c4100d145600302003d02000301005441104d00166a6902060340300d0b840199000d07281101c0c0361820f02625000e520140100000d0b0001c00102110001d907003c1800c1048440300c00000701042c8048948820740d080100c0d010101043d000c5e514642002010f45541c58188181c0c08165816002005c3c90320700c242001c5100d070003507080c00701400800d00c43c4001203914622118841d206000000803000342c1d01c801c000000c90034a00d200180340c6402000d1003184014812144041d40109990107580c6e01c610001e8590300c504e42004105a00101c02e01144941100080e402260a40300b03880d80c8a1191039450410304046500c000003134000d8a01700f02049180c0015900007001400204104c1e401140c0d003001d03680026180e1a042c0c0c603041c911100d80d001030001038068012078009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 507627706 1250 507626456 507626473
    0x60a06060504050a06110f1b0a0902211302090a0b0907030e19060905030a0c0b0a0b0d120302070501061401110601050f06090310050a0f11071a090a050609010c020c03 73
    0x11664110484c0507482c240060b1155158220000300941f2100702d001e0b10480d00101d003100203544101c141032403414002c1e20a00304c0841c01c3e4009009545007268103100314440d000b001c20a100c0c006801a00001280d500c40c080400507072141c1200d6440740d5441000455000ca03034101340a00000c004107480101841e00031710103120040811100c400c4400b0f5000d0904180b02c40c103148006000d080d034001d10300e105c006410140bc5070440f1401d80c40078020794800740c1036600c5039103000c2502c094a400035030064942c3c0f04403000807880e502107100103900d8500103007403a900d0b039582c07400c540b52504881c41d03078614540d24541960b40259210024601070000d8030349035140c41c2c08030341071940240c80301e48640c802180b9824113440c2040980180d8600302d009000c503081900005009129140d01c3e20032660410628540e44001c030001c03111020340c00100300d00e00c003009140d4450f02410280c00001c043c015901070b400030400070090740d4045c02c030107000055500b116040203498070a400016a00a4005504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 507628956 1250 507627706 507627709
    0x19030209010804200618091e0f2d0603010b010207081b0d0804120210050703020c0108040c150e09070845010f0507051303140f0609060a0606050405 65
    0x1160750803590141a1020b50340301503842e40d0382130580c01112074005a02003260401060f885483e0028020142c1d0105115200d81c1040f800200d0842040400d4803042004503400081003012180d010006121050043c40600a00000810703160005440101040248011407400303105403c0110f00c01d000600003a40352200891710741400d528a40000b4a17107454024441c1c8440c0c50b1010141d5202210603500c60301ca42c00d160012131005070690240c0d008e00450000381c1d0040044510311601600101207842001d001140c403b000100300b15280005031000142e0301e40c1c04a95000892400d8540e00342886484080c0010194014200c1040085003c2840b0009a41c02e441c034403500c91780e1080d0341c5811000c0c03441c5c80e08038895003a10700818050359409428101e041d4010b1000c81d141c280140480e45803480200c5603409202e2981074140c86072201040002d04c41e131107819250340c3c0c1d001038403070034889940d103d4144041200d0203581d5030400020401c0c003150302c0c858003010308107500b03240d400c1504000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 507630206 1250 507628956 507628967
    0xc1e030a02130e0706090303180303080109020a0c140718140105011b0b01031415060120070f0e090708030705030702010e04090c060302040f090e030702040c231903020901 75
    0x84010b40655402080c0d40c00b401c078150404035840060f1001c407002242e0307600c0000d04640d014401900011081c002d20781c10540c00000110441c0d0b0196a04400759003002c22100082d8070000041c020b01c88100b00280000e400c81449a08441401024244040c6003140c00c030352610070309c584024054a01042400b0b0b803400c544569040d00c50a00c0c01c0800c2d01034440c1004ca218001c088050b00c1c10710044000001c1000c9804a084443c3c0604191041d00f28041001500c0e11000e80b0140d01041c0307a02c40749069034500000301500713144120f00301c5008558650f228043c5203603e800c5400444d40e5001003000c0300404009a60003052940f00135490030711162145500c0b8040d40310002d041050042c03440141d640c80d0307080254103d8000c0d00c0c0c1c01d401d56440703801600a5115118480d182c0f10790080004400d01c0340e10034842d000e051640514a008429801c00c00140b00031006403090140440c030043c840c0d0441840b05200100d40c00c481030342c40d01c158480f114800708480c08a0101030040141c101c040e644003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 507631456 1250 507630206 507630223
    0x50f0315011101050f04030f030e0601051c0b090a02190f1806171b01020d0801030623150f0f010c0b060a0b07080909010515040b0c03040f03050c1e03 66
    0x488006604901200040300ca2911207010080300f03600304014405000c500e080814045e03446a102c040f0b000340860825001d6074803128200e011504204010040784c00c02d6007803076214028001c2c00d80c0b803c039203683e5502c0250009407140700d03856201c815a03800b141810340c01d801241000040707a9261f24a44420340601c0c820b0f901a12414401d4000f20360407460f43c6800c10310281c440ca18500c00010f40d8400c0311640e4890901d4003c0c40c0a0a0b40c45109055001040c0c44280340d4055442455507802c50f12910040c1080400b00c0340c20b140000b4a507400c0d1f1030014800c50054150070900e1503240159401c01015514402c0c0d441d12800c0024981911680c0246440c0c000c184c0c084600615640d440002540005003640b14000d1030b00b001403884104041180141490340301106c641d00c440e40c0b075109120a0b460500420640c84001304000d10044580c2c601601d2207002d000300b120701e800d44034045110141c095900131207040d4440c02d0507070424909411280080200d0505003505403402c400003aa640404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 507632706 1250 507631456 507631471
    0x30e0c01200f01272102010f0204090b0a09110a0806030a020a06050d0608190311070506040b0706060905090309061b15040302010b0f0f0103020a020102040b040308030117190210020a021504050a06050f03 89
    0x491759a02c120134000c1d0003003076483c4da9404003152600c0d030710803002d005840340c1c4440510800c6c1090b008100c83c0407a102d030403405010080c58a0412032043e500781c91241c000340c100c0d9410720540d000744006036200345141c4042d02595030380030340b07540703041500c01c099134156000aa05900034a80c205c6022003481e070704004103901407601d0050413240760740450a200054114030381180c000a004180d014103d401080b0706441341d1b4040041c540d0740c418100854006440382246504200410a502d18094010344070b8030704a1920b15048088840180d45071880c98070641c00600341c090204030901d5028401e001010500b90b425000f02c014040000d0340d401c501c0c17500f8506159000c00e448103810710035030686020b030540d041865034075074403401d10401d560001d10418220810060142041c84004111500c01007115801e20b03024103d2a42040301210fa0511580c0c2188100b40889001d81d44120a40020400c2222255075480c24403052080c0032840350483c2c0240001006550b80004946049a903c0680d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 507633956 1250 507632706 507632753
    0x60e2808030604020c060a05070e0d020a06050702031018060f09020a090507091e0305160b0717070209040f06050c0c06010e13020607030210060501030e0c01200f0127 73
    0xb0b40703100003002400340da912104540305040c104407419031250311013406181c0e10b888002c0b140000c0001c201aa003a030043c000e401c030190050800116014202504150f03100070192204141020104011070308882002e21800c3d03503c0c681d9006022a03442007880800c1e00b85802d21500045802040250708648504052180d90300009003000b44181d01c540098040c4d0f00344841c580c080c000c9d0340041c50791180030070b81e4070f0300a40214040c0d20300f28105000c100c82000c9a91414020503071524040c03010b20301008e0030010003c11a602c0181c0d150039121741b04038030644610a00d41d2207820700100b2141c0007011041e0b24007040003e00c081c14800280340b0304542000302e03095669a83c81e0f14103890240740200003908080b000c40d11004140d004200c09185405414080101550312001141500c0c12286120b510703801a21203c4006d510420b4800302c8410800c03041540070b01c0803115940707445d00c001000d4181d81d646014809442c201481f03034213441c900c40503003001018002d032201030b10108109084801c419 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 507635206 1250 507633956 507633961
    0x2030705070f02060408150f100e0103110301061a0c0f0304060e0f12120a020d03021c021303020a12050606030d020d200a140c1206070507030309050703060e280803 72
    0x1624282141e0180c41b14400340c1c0c041c080d95501d0303521a01d005864a907020380b0f032440050282541c0a14480c112071022140300a01e910b9074454039000d442d90007082e5019500c41c07070041401500400b00041c0080b0340d0310f03a16030300c0c00c1d00f00c2c8031418040805280703030440e003081100b00940c550020b21490102e1040f034141c2503000011000411340403031488a01000c3c0a1580000385081300180506594107141d02030320345140003070504a080b84203a208290040c0c031100c90f0542070341e115501070485003817400500c8031226102d4000a410594503071010301d000c840d0f013080c01e04000c010710001b40c01100a90041103010b02e0220013130f44800d024418403042054001c90035980445202d03000505440307031030030f64410641c03604000040b1915509481d500d48500e010f4000c00741400c80e804000d5110f43c401401d0191205441100c040d8050101a410107480c1c14218010500c10b0000c00c00a52055a0000755440310903840c0d030905418200c86002410751070001c0800c001c40440d21110998000c90040d07036079 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 507636456 1250 507635206 507635209
    0x1c051b041b110601060f0203041a0903070b09040b0103052703040b03040308071704030f083105060f1b210703050402150f160302070b070803060108060402030705070f02 74
    0x4008100441d081c1d019508100441e26030072110310315040410b0380c281c4509a0301c9100643c5c00c0c0800b00307242401680204400c01041d013482085440080d100c111a03460000c104000078030340102c0350028590040c002414a540e40b4085c070a0740701c0403e0a080900840c0b42000c0000c4001003600038084210f5200030007201d403c90188200c0d00a000360900c09926070805007030040100004407468030114100f07400340d080301d01080e84243d22441e850b5903111080400c00f4412100c0403400381400c4596004541441074074080c0c0034a83c12011130362911225000c4ca241006460240d0190a150600f000788042c0600d2100a00001c0400188000c04560b25189046a60402118425a4002082c2c202d050000d005e80c10b070001030040c1e008544451802c1410040714030719205503051458030080802020014038081c060440e05103009005440b200d0396242c03c400c005074020740c0100d4103a50000f082110740d42e00610159040030341518110b04524020700c010b80f0341e01c00c04001a1190800448003803c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 507637706 1250 507636456 507636461
    0x5090d02190203070e1305060c04050f040b0301061715010608100b090609060304050102270604030b04111002030d051003110405250c03030f09020307050904150c08061c051b04 77
    0x10001d50304c17080440c0c41d12880c141144e46558200300ca043c01602e0114103154480c0c030583c3c00b0340d0300051084038500501800c203c020082c0e1981c1039095501c5c1c2d040001c0c4500040200301d84d0700e07400d80207488038009040d07002d01c070200160895000c2c0041841449808442c41c0405801e4480c24070210340d444400380001401401044210f551252b00041003000700401900903091000b40d807841e4031400c07504a00c908189140c1c00da28903400000601003040820741c004103041d005401440c1030070700c40300060b000c0340008941d50b080301301503400002c1c010719201003442a07a50045ca0301e40b0a2119505564035100060b08600002c0d01c120b0300c81000c2408507550180c0b40300900b090142020b60100043e8005d00790166600341a40481e161443d0900340311424050f851519078010050211a814001044514500680305460002d101503200361582e066209207101d85405403500d10442c036020781086400650500c1103160005032140d0540000d074000740f02e0301c4500007104140c40e905d1015011070b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 507638956 1250 507637706 507637709
    0x50114100e032d07030b0c0d0b031b0a060503010b072406090c0909060b1b030c010f14010b0c10020313020603010b120c0c06070c140a1505090d0219020307 68
    0x41c54010b00010701d0010f40303141d0040b101c019240c0f010000041c4014001a12030a0034440648034282e5080003901400c00c0000400c05000b200e0340004000413000b000c24a080403042d80408a81180310b103a4115217404850707440205024500344d440c42d814000c0820721406183c90003066450100701c0390003008000101c885108882040420a01d80e81e250311202400c01c0030003a0700030071204200812035181c580100e5040d0b034880e0604a28000441001b50100800c1981c031003810301081c805440120420300030065548030100f0040346100e03014851a4050b5010ba2000015000070408080c003e0f00104a0304443d084900b801612540c2d0029015601c00160b60003d41c00800000081840403081018040700c00d91340023806032030398842504d0310341c03442611024000b03507200100094034284a256105805e0b0f115588485407074102000c402d2802d84000030440d865003401081800c000920f00c01c0550140148000b8104882400c030040e482da41100f046496a09944200c4015501d04002280 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 507640206 1250 507638956 507638959
    0x51021021c0b04060f02070c0b0c011e050708160c14030937030302060a0504030509040507110d0e0f01230c030304030e04051021060218030c04050114100e 68
    0x1401e540d891401c401005011601242d050346070188411502c000e40c401da80c19580d0101944071940c0c00c0041d8284180c03c0700e881c80c4065906c40c1c0e440c0e0307441c03d00b903100052504075081004c1a281007000015103404001403424440344020641e00c0c410729449600100c103150040701590540410728001421441180074054000840384000c550a4641e106561100c0d0740c003d0140d900e01440840c1100e58403080c1c800680140d100c0303000724880a61603405583c2180c030908046142441c1c0901003401d40c3c2c03044458101041e002c032054403001c2024002c00150501c0b0b450441d0390182800001a5410b0b0340ca5940c0d4104125808018219035071500f0100c0c0c0002d020034600d484550030306d5400d5481c0d01c2101d0880001c4e09800c2d07181103d040c01d001da24054245403020305050f60804070030080181e071604d038190014124034400b801041241c0300a001070700c6504803070503411f0f2030842810314040808044030b0040f45008010014001d560644140c0c043d000c44045200c2c078100c020403078070f848444d820305 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 507641456 1250 507640206 507640249
    0x10c1101021c0f0806030d0804031202040f0b0c060601030603021011010e03030a23010807150201180501050601091212080c0d1a27060609010215040803090105102102 73
    0x400030b03a00b1101c01020800346540e0919682e40705824107440e410340d0603080c40070900403408100041d015100b4507101e022103100c01800c150703488014124080b229441941020300015003030219550511001e64090301c00c1c01c0c1445070303600d03603404a0410b44a142450f81001395504441c40381030020740290740d80d50524000c490700e0303082100c6440001d103400b0301800841e00c501b0b07854100005079040c104c1d048440010140c03140c2840e01e8103019040e03525990030011556500c0d507604000740e01d141717100e010340d00440000a2500c0c006002404400407904003007080f0a002042e03000040d030403400490a441c8a01d408101d0b615002e060803210b00134040508411400c105000c44001100f454030b5105004c03c0359021800b807162010290905011b03444006600c0c09100041e09500741000245130074031040c811500300c1101108169141c0000765812140c0c10000001d018410030240100c6030800000781241c4c01d05442c03e50000b01c1e1350707604561a250105042049029036407880300d490207a10240c01e24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 507642706 1250 507641456 507641503
    0x90b03060d08180307080d09060305070516150b15090607110a090506040c0e100e060d02220605031e09011d1614030c04020d021303050a060506030309010c110102 71
    0xf1140d00d0702e1805181c1e010b88510440001d044070700041407101002c841e00c41607009410036808a02a140013403e003014418104030485c0f12011040200c03400c540208018007090700d16a00d000265101038020794441c500031007410807880c260304120781502c030048400d5590390045107081c030034010f100c12840e68414545040051003000319040b040c07117840210383c10001502840426a150455442c40d035802c12070501000070840d000e149a0034000c00c0007001103082014241ca0a400d03a402152908a40c0d90f8040c01103021004101e400c0001c2c0800c0d0909a055241000c040c101e04000381a080d1000001100802d0b20540300703502104400e80042345401205200540c441d9a4500d0707002e0019900e00c03200780005e071100b02041440c044080c000c0107010b00e803044100b04000794000c0540c01c0c4090307600300034215510301000e41c600001c5204001401440c1400e080150840f00c004004a009410800550a0581e44000c284d940c3c140d00132094440103420000403031138103c042d03940700c0801003103c24 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 507643956 1250 507642706 507642727
    0xb120619030b01030302060a1112060f040f0632090703021207080106120c021b12010504050703021005030601020a03030216050a0803160905031506030a2f060a090b03060d08 76
    0xb20075050701d02980071285a40c40340c008400440c3c8000d0030101000c40c3c28001310381000340e401003494210800500402200b400703030001408030f514129001800b10341c0c0e42030801100c0c003055804494040910b10b81d0011110006003410070755240c0c096070384203070034000006044034040d0341034a414400420071813040c2e240140e405050365200780550f0780840d4103441509440001d601a03004654aa90b0203440032901900200031111207940030164494144c61005c20441000d10480788a14040e200401046156005228040d8000d00805003000404c200304200317660001600d10403a54140b400586d581d420f4969006030a0201c00018018040c8200890500014074040d500034110340662400d080c24200c0181c80b00100c40c4600c41d010f0700031020110341c000b4015071955220902500f940c0b807a0782e090b69030000c0c1a610010300180130460548251404868007920044040d00f50303851464600b000c0005005206184521b120117800040003540ca03894001605100a61207040140c58044080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 507645206 1250 507643956 507643973
    0x90715030b040b060a021f1d010c030e0f0619020c030d0b12031e0304060b0a0602010c020c09040b0610021603060905120310120204090f060b030105100b12061903 71
    0x18007501c0359040180c00c081d94640b00003101c0d54011a50010528041c2c14103c900c110070400f2810342c99255600f00c5101ca401c090079034a000403101390000640c420140c50044d0481c0c001400b0b011301030707002000c1071441e40c00000e511070308140300071445404185000c0540005c0d11502d0030400c6540404180110301d480c03150042ca480960484030b00e410340074500d045550724044e0b034144030315004803004c0d1503103280f40480095400a000d0306000c00c007401c2213008100600007561040c00180e42d60035680c008035034140001c03820900100c0d08098242801d444000342c10300060015032062040b6820440303202e000704207040c0903c2a921420488969078204640140080042a2a60700032310183c405060360781c1c001c60b8030480e910302c10f420710382e070170007aa12849901e2090f0480c5c10641c2c1d40381030030105030742c0300c41000700501c1408040b9041c00c00034141402c0d688085c00701ca0b04401a0f62060000d0f8903c0000e544070090701d00124000d50396030b0400240600b5500c100e45994400c0a9404003e100252 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 507646456 1250 507645206 507645221
    0x70804021522090b010e030d0509040b0a08060c0d0b031f021b06070203070302120f0f07150510091503081801091706090f070f090504030c02150301080c0405060904030809071503 78
    0x903243c1030a071451500915480340781e2301400d00002401042201000d10342680301410600b03026100e540e201c0c2c0c41c0e03000c0a2400e803003079803180601040841c0303402c0040c81c2806844031481040d009001d412003555401c032010407100e00512003441d00400c080200000011001154800e4982110074a00f061403029442c0d61240310103030014020030741d110300c4402d1a60100c83d44040d5107440c03a8648411440004200d4204200484882010410080c41c58080707019460107820100c440494440c034201ea5401143c10500c3d4110707130740071400020408142024141c0702a1a0810708070b200c0302032010012101d0441e01e40001280c180b9420707400140308030001d0050700c50f00b0841c2c1100c051502c0030a015035a02020f2143c1807119600c80f809025644e0643c00c0302d81c215110742001c1e20440c1c4150300007440400c0c0c02c2202c0c1c18510000c0010030140340100b0145041ccd9505940c20001818000301103040824000d102905006034040490561701c020402e0304002c1286244c62508940c60010013406040e00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 507647706 1250 507646456 507646459
    0xa020702150c1e0a02060c0a0606090c26060f030705060309282604170a0507140607020d11060708040e0c0307080a0c02010f1e05070804021522090b 65
    0x5100c0304000080c03a041280c084410b0f29001818100b0b10740e820401c0030b9001900329502400f13001c1d82c2400061441c0129809081020004105000320b85001469aa2840c0c409609814400a00214801800201500b03d03c095031680c03016645074000c40d240c210380b5886980c101d6400400c0144800340440c1101550030b00d480b14100598082c12140721800300400045d200511041e008510750085117000802e6040881c905411f042c0d54881d01011100c88030a100c803250080406102081010710003040034140b0110204070000003000820801c2c0104200203001c1c5041410b20300034050380030811044244001c5c100d503030f1840749141020b0a6003207881210150800d03c00480e4210b01506c00b42ca119000c1c1e6940c2600c5503403440780c950081c1030100440380541d503a03800146943c050301d014030140029400041c40811500021480031100001c16603010441103809010040c0c2e14ac5441210b10b090407011039448007500d0351481c0281402024051000058600000b00c05415401c5003540391070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 507648956 1250 507647706 507647713
    0x3120a1d0303030105030d080a1517060702010e03040603110708030709031509200d020a0603150e0103030c080d06120c080114190c050714250f05090a020702150c 71
    0x140c0000d1540d01e01081c020745a140d001603204650082c45030b5619580f15610800204090358409014080b20006070040161240004220711060408001caa42c210400d403000308140d8907038445003601d9000364080c40c41056240c5084021308400c48007620150fa030072685455881c0dc050002034105491031008442031b11841c020804032584038840c040d017040e000720001d808141001e8a0f495039005190555601400c211848009600c824482001500d42c9031070000310103100f6100d6144d1380080c2d07130140780d50f56180c1c401400020b5000c0040c485207030340080d03c1c54642d400148444090700c1580c1060800130445c405240500c050800c03280f080310301c084001c0018448002400c2d90480080301e610f10b81e0405041e403442c031510307103500c610707a02e24440c42c015090002c1c0303645400750885c41410803181c56010240008042a01c90a001100e251101d0141103a070315040c4d100100008a110b42407140310200c002820140e00d0707030103c0b040c40381d0061a085104030070340a8000d4a401c030030880c520621 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 507650206 1250 507648956 507649007
    0x60e0613020c070303050d0f14060a080f0c04050c27120307110907121103040507050913080307050705013b030d09210c05150f0a0b03120a 61
    0xc518400c90340c020318a2805030007030500f10b44003618550300441a4a41007a40c1e940b140c0c00e008a03d2049441071380e0441251401030504604004c181005504120700f01e400c0034000062100c0e0000d2402c2038038009440204071691800c01103111402412501c0e00b91036800341e41030441340e000500182d0f0b104411110a08103803504000507070b40303000700e5500410406506d5448a010301d410804c044c1d0000207464100c1c42a03400001c2e1205480703d41030651b4550f00003009200c1000010702c00040504400c0d00d444201e0b1409040059441c06842006000444000046412648910111303889280c21600074420401084803203581c54084144118423140d841a5600307070894043c4030011240c02e600c2c015428444166403840050078035002c219900e402400048000b04240da81401030b402e83c07502d034400c86d84a24101a81003254811b82d240a08016004024849080480498101c145114000789403008400401d180901c03180141a1260011a15200082d0301000d0403c0c100d03d40c400b40f04444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 507651456 1250 507650206 507650239
    0x22b03080403090f0b07030c39090207030c030c030c0f050a110a0f031103070f0f0e010902070c0314070b1b161a0a051905040302030c090108060c130801060e06 70
    0x140040e020384842d11001b00301c0a0701083c400e2070650311250091108142d404103400746055081072000c1c2e400c4200406450a5002c09a2221002d0040c080e040e0150b16040141e680141580035807c401010721400b07200da03d040c144a80248500c031035000c0382c4482110000d0815a030307a60001c0704100c4410022000c2c2d0001802c0044140301103800720302c90940c0c0941569200c0344000381c8030f0822138061180c01030009018000a041200a000b003524034203a0508045400524110503086103c00300d00400105000551544500c0116134020000742506900b1501031414039025030321001e240030340030811202c1e28000c0c248240f6180c003880b0842d140100100680d2010001c10b104941d000b0f108010742d189440b51010061078501d0681c07404902d40982c3c0c80804894403030700380340a0000740001c90148110306040022a401c0f00c400c81c0d1104941d890b0408203907580c0c1c0000d1007046484804940784110760702c80585100608000c2d00244891a181c0d07055003180c220407034080303104030030010070b10302c44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 507652706 1250 507651456 507651479
    0x302150c060603150a09060f0507030b01081e0a0b0105070209090f0d08270a080a091a090a091d06011202100f02030405150d0504030c170c0a022b0308040309 69
    0x10003030b40340d0440103a450148803002442540c1044d00c00d25285c1703023045040c0c080e6104151080132651130000760101d8190004041d0380c00241145a180c00c406050240510608000d41c8d0003003c2d242e01240410b5038000407902d45c002c84800039045403650041c07080e44880481e4003a4480549021201304110b1110b003203890580942e00c090b2000d0b02c2d1100b5054001d07810b00b00030011142841140c1d0303a40074030b130340c2c2c804503500031280c035000101246d1090103198406003001020058544010b820442280005024080140300312404c06544004110390258104242400548810b0540b0040e60790349120b1800100d40c88c808070b1050400c064804d031210f002d140e807039010840c25401107080a04000030b100021208110710700780c400b03041c003a0700c14003545809600e10840c400d0f07079180a05040340c03411200d00301c1c6008015000d2002403000d050b003070500040c09018103404035068629071049208441e45290f59803103004c0251600760704070046c150007024003409144240e9510130903658581d60700e0740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 507653956 1250 507652706 507652723
    0x90c150e090402060a030605030312010e151809010b0d05030c060a0c08010909080403061b0909020406050a1404082d0309100f170118061a1606060302150c060603 71
    0x10301c01d42400105001d800d06030003400000186060000d104c40d04c4030b0000e45180c0080b640890600c3d0f8035001401203020384220241c2000322015841c03450200c00d0001000180860080e84a11344d107440040d40c0b00409401103d50001c0203881100d20f0b00d89030134401c2c1c9a43c0081d40d20440c520030240889c00420311031280c081480120350380c0030156401d0000e202c01900c0c541c602070f14494028000400422883c0c03044076109101100a5440b2008540e070181c1042c055521000c2030900c140f1041000a4200c01110013442c0136140c0b074054960f400705413010a02682e000300403140305c1d4034000d0031000480001c0040044040c0e907501003045940402c0759503841030f801401d40000d40140302c0c00f000d601448200588545034181038072486255081c507080c1e60303001d901c101807642c050044001ea01c0d0749480380d800900200c401000500403241045071740c80c4030700c91a540200c60340212510500903540d1264000c0c1d54024042d40d44840c0300c101d01101d03070f0440c0c030140342d4034000c3c000032a01929000607041e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 507655206 1250 507653956 507653959
    0x3020f0a050916110d0c06150b031506041502030901080123090c090d06061809121803060608030304022815020f0111030702060f0702060c0d090501090c150e 69
    0x7290f840d01055900c2c5101d00c08601c2c2800805058507083c2642840032401a02866030f4042544003d81014000d0380e601c41c4241d61a20088107090008021000440794042d142c000d41144489400012520302e1041c1d40c09854400d90810451210359800300042030040026a900e10481c1d899403490b02041c01641c1040e1061120a510584103040208801d5888007004800508045d03140001c1141c9101c11442206e545695060512004011281a000c03a01c0050020400e0130358565410115410050038070080c06040d4203401c8100140b8600c01300a554010001d01070540e03a17020166032a041a01c1c00c9200755551414041e046481c202007804074651640c0b00d000c4207203840ca0a0102503181d0398104218000c15500e0a54100d003401140141c2c10f108485999034985480000d040c0400600300c0320421920030280000282d0018466030800700c01401c0d11380e1401300381c0c4c2d4540101020003008044d03500301001e0f030041c814500300c0481140d1086c002600c0034003103032600311032050307801c070195 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 507656456 1250 507655206 507655219
    0x15030411032806510e06060403080c0708121908250e03010b0603012403060f0e070e03030c0a0308060d0506180d02070f06050309151003020f0a05 64
    0x5580b080c41402c0084005003d0500040c2d803030031070681030300c14044442c20252031010003a400b4140342c008405403c41d0590311101c4180c28000c03d80448000f6503288502081d030541c0502045150395104c0c1180c00440d0701c080715541e9404001190f54540d0528440c5000c1c2d030003522000082c410401c804c0315007960f5180341c1c4500019072501d09035240304018111010200700380007000200351044000369811006505d0f28428450b841e000c040c02d4681054009004041c00d0004228081094030303e0815074042401c201c0240301c40038011001002c00b52f000301102180c5200004036508421030b81c6004500c20760360f4450840411051541d01e01c50314180c1210f80d4040401c0d400401c3c441c0c1d203016041640100101c01d054001e85602c0d19201060300c2003418000f80c550f24202c2050304101e2201103595900240c400e4910b84403803102e80394154030804092010000005020075424041d1000f20141e0038000240c5050590100345902c8203800203c6c025044da0040c1090b44c82c104805a00302c48008042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 507657706 1250 507656456 507656503
    0x19050c180106050d06151d0a030c03151b080105090a0504120c021212090a0f05090109050402060c0714040f1401050126041a150d02010513051503041103 67
    0x31503081c1d00c082c2c1400f00f02562020007150885031680030040d9007006d03541c0c44021224500990300814a038040c814856032124030200300203100d015544044903007200704107038004900710f4410080e00315242c9451188011128000d00759801108070f5040e91420350300507040b95102d81e8500100c4905480152141001410440700c06214518000722288068241c4900013481c020b19443c2c20540c0341c1c02204001d01080c481d0980c01c0c10140304006044112500103210301c1c0c00003003210b42a06019104610b508c030b9001906640700c031003c503802d06000c1402c44149541d105d010308180340f0000301c2c56100c1c50501c0846c258040c1c642c05803010612054600304580e919100041d00e51a048184003007520071040d4110142c00d00c0c6c0d02880d4400c3d07006c0d00d000e0748801c001d0200c42040c04401000a00301050312403511500b078407038801501c20030f603082c01c040e6942d0b201000d8041c0c0c55842507000541c44040340355403c106060440266009070f110300151507417000961708058884001c1d035030180356010440b04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 507658956 1250 507657706 507657719
    0xd1404140f0c04111b010209150a080403050d0e060f0106020105310f080d0b0310060303020c04150f1205010b040b1804240207050d05040b040504021b19050c1801 71
    0x15802000203240c03001c5c5043d004100856013070482500c02d40c4c041c0d50100d180d0b6141c0c1020071103803100128907440a172070105130520162503800c015002a003041070210700000d00080b0359002c0d60784050100101d801e03600d88015001c6001b1024000ca100550070300020445e452114a00c60111644810f904081072407030001c10882c600320040705681032801c4002d5100411410030041401d404002c0d40030900001e00010705103007140322002c16603254540001000400d42c08518a006014101c5002c20300003085401201421015009045010424a0300040d1008550701040340c091284000f44088143c0004000440343c0d103da035035400030407101d014101c50003081c0907150301600c80c2e502c1c0300319140c04907010000e00e00c08007004d4049941c00600c04051000c2003200ca0382d40c4c4070364502146468200384007442240101c2c4952401a60085440196103ea10014610003422102103a03d40000039001c01d00b9944840c41c10740700c030b000b8202911818104000b84602c0011040c11700c14003a480d002c0f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 507660206 1250 507658956 507658961
    0x203160804020402070602130f1203200717010c030e0a1101080a090b07090e100b1914030c071728020c030a0c0906090209100c080d1404140f0c04 64
    0x200220f0703015508000304000512248080d0928242042881886a027000000402100d241d00110040820442c120000a5100f1004140c010304106000440403550b4201c0d4940415070f040040c401c11550031010720039505511161080d00c0316a000c0c0b0019140182c045d8941602d007001600485041d0800310b107650042810541080e601807002400c0c6e2616113030300c40c403a001a12000c000030b102c14804c1042e00084500550001d0080703030004001071a00429400503c160362100d02c6400301041c44001c031a0207556480c0e0755a000841c0140d0728070303042c940310206602610049602a07802036078446501e818005450007440c0384070741d0344000c0080461310f41c2d441b02441c09417803c5208881004055490078030060001324840d480c50303440142070507400815184940c003c6c050700351040c0a600e00d541d640d4840c080181006091201c1ea01d041c1d824143c0d101d101c0c00709116501800c1c001743c4640240d24500680c45a03000b1507500110403911601c0356101c0f0a803694000c03003507024103001c5080c1c2c80e00c4d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 507661456 1250 507660206 507660211
    0x203071d0f1014030a020a080f15091b0c0c04140c04060815060705060f341701031101090b0306060306130b13020d0b010801061202030c040f03080307090902031608 72
    0x20704207984001c3d00038500000903482100c00b03070308203a0003240400c41c0c26001820160031014040e4107036214940002c11152945500700360300d203d444640302240402011074804640b07414030146150b5503420b078820065540c5155580140601d00c3c181a808080700204d1001d40034804450742113180500e0704604540c2200094280b00080101e03051240c466503a15000349680c600c80c1003c2e000b685410003283d5000301000f08000b8841c90f4600b03081801c0016101c101034503461880c0281101c1c44000e2084801506400400c64903201c0000044140710180559606403002640c40d05508d40d1502c54080d00b41c001078401c1c0350405024030104645e40b501d101c0d04d40d5456040c40d0005118801e0400240029041d41d025808150340056042d800340000d0007070b003214010038204004a075251035001403004803003081e0300300140c0d03021011598134400e1000316802445814580286a1703201d083c00d8119a00a40342d0382c01203148001c00003004400c81c001c0d01c0c072510901800c48800300306003a041e603242100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 507662706 1250 507661456 507661489
    0x21c050703020c0907120b0301020910031d1921080a020a11060c040302030106121208130c0902030106170403050f160609051f0b060406030b19090203071d0f 69
    0x14030040c9a03a64403100502c52043da9990b4a549481e012606d00c5011a81521009800b990040000901030348880429495100041c6000580a106281c12140c0c504071002455a0303801406948c52008440b02c01c4540e942d400340f8400c0444450452244107901d40500443d004a075a620014440e04005e0340501410155800c20f4a1011103812020707081c084111444104039038045014419410300b489143c02034551090714003c80d10040d01e03140c5840107181e40d44002c100c07180000621080807011000c6805a1041e400c890741ca8460301c01c0c0f4080c0d0424052000014041450200d0400361041064003494140d20790901c0d00004080e04240381d400100c808980f8201d01150b0400540d01d8800c02001030700401c007030b080d070421550b1602c0c0070600c2208007401540c14007c4542e1140c1d104000c0300c00702c480900f0000340e09003d000104851203540b02c3e01110003556085d00140b0805160010b6109080c02d42e5218103a80c01c00031515130318203807500d00701d40118403420a030080b414400e941440c441d49 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 507663956 1250 507662706 507662713
    0xe0109060503180715110604050628050a0203071e080403030c0e0a090e0c010215060f0a0e1504060b1204080f0c0706020705030c010e3d02071401021c05070302 70
    0xc3c141c28501e400025401402c15079800c0b020700340d9581d40000c1c07826002241c100034150a04140d07c500d50344010140410031650142d129400c07034813001500d200064013028106002c80e207041a00381c002034204881c148049041c00c8159007100100b52640300b01d58590791140c9800340c0301c0d51411001040e202c115a410b03c51629940c00395903a540d4071078801411010008036415502e0f009040c2044a0005400d0541d4005c821b202c080160784895158082c0d4141d8104144081c0e11001484000030303a072188903d2030120081c04025910307030003051001001900c052242070fa54580f0517245209020681403c403d400c400314000460110080c9540c010820b04103081a50088110313050940d075500000c00b5901001703040003141000e12180c82c041c0c0d030900b00351a5158021020840c004a29640c0400070f0034450310001c0c00b00c0e00703614031030780f10701d41d418800c0888400c1c24400f0b503071440e042c003900c0c00390381804081280c00c1d0b10010707000e1004021420101c402d000c0010081d20603030810700d002c405600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 507665206 1250 507663956 507663991
    0xb040f080405120705151303060c0c06060b03151002101a03030a080108072108090118090b030f0f0319020a2405090a030801050f0103140c190e0109060503 68
    0x6503003c00d110b040301203041c0a0020545403004100741820031136042100c1c120203101c00203201c01044440c20850b0742002c1d01040c0082ca142c0116541840400010309640c640400407640070350650286210b034084070592002615003a00b00800c60350394000420059011618200c0c2040c00d80d008040784003014801c1011109030000000c1c250780203100d441c0c2c0000c0c00c6000400c07070702c1400c002c82e90003070050045c0c22490b055081e90710601c9200d40d90380600400000110102607901ca0003041d02d503034400c1102c4d021099168200100a4041581494800c1c4280042d16603503402c007007070740c0d146140818003e42c0390207a0000b04601402c1640e01240640c01082d2000700440d00044a4004280404c000d4030121491814680304881000d420040c5550045028000090b0002407040c1555400c5400c00028011100100d02800340f41c034405a01900c00002d00078400b07001c402802491481d91002008041443c0d001c850b03800d000320489002441d54042045034500550007076402c01070100f400c44450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 507666456 1250 507665206 507665209
    0x6011e0803041d01150203192709061e1406210402010f0f020d1407060608010e120f0a031e09030e090901060308040b0309030c0709060501080c070b040f080405 70
    0x54115500c402c060070301509031202111503c20034240074000c442c1d0101d00d94203200c80025524059500340030354a030314000b44441e03207e00070b8280100e50010940d03800001d807071031070080c0c61600241c442d9400d6141442804184d2010b0102030303021520075440e880f40418034040e415003620120301e5280707800520401444165000402850002241c41a1510f503141000d2000405010f48142c410f41004050000203001c00c0d8046076006c0020724510341442c0c20003207502c81a070144584000240303820314041002564010640040c0f01c4100c10f28151210312510011100c4548079804810f111030000f000090701c20350003980280f9041c00703141000d5001d501c00349000001c4500c0c02ea03003907010458500c140c0529190511489611a09100003405000c0c595070702c40081c4d0096009040c2d4040001c0300255800400300190f8090360401000c803480f0300c0d6290b002c1b40090025000c1c0c6030003e10400002006c04101d5821542400d50000c40e0b05212f80d80c903101c00e003c01c025080200c44503002004005080e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 507667706 1250 507666456 507666463
    0xc230c070909050d090311010305040615060801140f0d06020c07120501051015050d112206020f01020906120a0b1518030f300a03020403020102010b1206011e08 70
    0x81c008800300003071502c98500303100c0e16000002c0d8019041000c50b070800d00000d0000a450701190710b00382030100d290b4440303103403d80c0a00450540d1409456840c180001d81e66484218981203a13a401a41100307002c8030000d0001c030030002282d8a810008408803100010031590003040329110490a54810940300c03a9800080e061440741510269116002c1c00026042c08003020020041030704d24030004c0b03174151f02c06800c60141903c0511059a101c41080034044420f08440020348621210701110240da076001140401c540940340061040815000c00d09205100300e42411800038005802d1070030000401c49480c000401204031345403504003809058484d64603149080a10310142d03501d42c1d0283c080708400038107070b42c04584294850348844104220204101140c0b03d520360581c04d40340f800d260322203010003030140c1c141d217043c90002c1c09a42441c0e00d54040c2003030324400d03030090000c1614902001070745401d5200800c2c1c50b0b04188010020310175a601041c3c0c00c0b0564150300001e907580d501c0300608 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 507668956 1250 507667706 507667709
    0x201141c020414030a0213020708190503160c0507030b0702100c021f06140103090512040e010e01050904030207170a080f030a050f0408221211040f0c230c07 69
    0x140d64002c01c00703000c580c04a8141c1c2c458500241d004001c03480258002039509203088000000c640c2d40040d405040c0040e0808030b40100c2c441688620b0700140c107500081c519070084444220702a9201c0401c09240c0c410460440202d801000410143c4c0c103603110103800b04805010032095100310038180e021064940241d581d040320075005441c40002005121000d81c800c031000c001003920b00320b8184481e000d00700c1485034202080ca0700080c0e04543c0d28009140852528656408000101d40013800b440141c0c0028180e4107180341c102c4d5540d0b6210280542c5840944008015030800101404a441884160f00442d540311044032009140c4e92596200e5500c0310784411540040041000000f409034090315810141642d88035001c1e1600c1d4883e8a0180034131810340a0086c10000303031f03039035079000045d15402621189244e01c04260507440d08407081c5524203030042c021418840c0045070800303a841030002418240d182d00c044880d222410368200c280307407035000b00400000d201007080709104204820 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 507670206 1250 507668956 507669007
    0xa0e090403020a20030a080d0b0d11010311070b040323120603060c0c150601030f060902090118050f01110f030a230906090d2409060509010509030304020114 69
    0x2d090901c1e03041060600380001c1e60149054540e90b080244d5803000169421020307048082c06880d2403440c07841d8000b42010b402c00b560302220482d207840038010706031940c1d004c482d0241c13410400c09102d264441d219001d560710280c042c03605000024040380c01862002110781c02c0c4180303a401c1c0c1c0c01c031036032600854000200300e09004856100700314890a0400c1610381008080101c0c1c0c0c00c0c02c41d401c00041c1d80f02da01d804000e481c0c40354100452502d034001e0b0005400c4890050050104035102c0010318025000744d016680080e490024160030800f0180c46403080d100c0180c1010010807c4000568140105d052003400c80d10034040d280300800030038800750040004594808010018500306a08041240b01102d181000100040201591200200c48190505540500810800d81444168041c1d800e1080351100109000f9a44581c0705a101c10046ca05c03482e0108055100c0740c00d8942258401c07104880c3e980d100b000411b001d90f01501140101e4056070420f01d250043c40c091480300c0d4060040c251 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 507671456 1250 507670206 507670213
    0x8040b07032f07170304182306040b012118060e070e07030c02030d0c0c0611030601030608070302030706030b06040f060816020102031014030c061803010e03040b03060103020a0e09040302 82
    0x1841103090601c4040004c084c6010380c11503019041c03612544900c250f2041b0917080701c0b400034410040800da0411900000c0c003050816840c20300d02074220380b000044850b148564a481c1ca5104658040c6030b002a8000e0140352240d40480d020b240c81004000030000c220480072207001590000c0c040c0d000d45111508a03401410002e40703070250f4403440110140030301d0141400d103480f02c1c0c813550b400800e40342491040720b40402c030489101c005441103522000090903043c20908040c07074414540c0b00840c01240f007030740c04000f00c0d0741c0d035109551184241e000007036140d04400410030003a031080c0c0252202010003016a441e05036500e60b4034002d4803090b17203c08003098400040240d1a14030003840f140c2d029240c0025441c520300980c2d4410f0040303143c0559405884c0620708bc0141d43c03020820800340c0d0f44082c01c0c0d80ea48403040d215400c2812801c10308a8420341c20840e04940480c00441954211884044900d05648401d0010741c06500701c2c050303400070003500071040600c42d903a41c1880741c0242e0080d0050b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 507672706 1250 507671456 507671537
    0x7180903020c01020303040b130c05100801050913050604080304061508100c052a2826070303020309030904020d0b040c030615030509160f0e09070308040b0703 70
    0x1c1c0c107124031030541d241990028420030001c42e0b02079114642c01503ca0844000e900710303d00c0c0540c06c0d011150003058010000141d81001c05801c1040c0d40e040e503008440d4010307180e68807002d6a510801c0c040c0020855041500884c1c00165000c02a5801c9031245030f01158803840700001d540c41002039407007180254080e0001c1090700000380b00d0440c1404c0b20b0310304a031034010200c02c86c45080c3d08125200c1c90a400100b20442003c0d02881030340c001d800905050070b044d120528080c0402901640e09441300115140707240701d8880c140c0303000400c240e142c500d40d5040071200d403015002900000c044400ca030004104100469031144020269056400b900250030301d0800203000c121465401c00d40107042c5000014821042c603c00c00141c110202e240201d041c1d40d802c0380817420002071000210400031981c0000c40d560903d03150b284203580d4540c4406015681c2c0c2070001d5a03522603840084e01c070403803c0000b4000c4005000c020208540203050108402145410103215a6203503a40070140078a103220 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 507673956 1250 507672706 507672713
    0x50108030f0409050a0e0d0909050f1303081807140108101d133c150e010b0306130b0705090a05040b040219030605030106060c0b0a05040f05060f01030605010806070f11071809 77
    0x844bd0000d07400c6480070254503101d600b000b5802c0c2c101e000036003408071140004034104040b0701280c16910703003c0f0a0b640d01c0ea40e140d0701c00000080c4000750502003070054002803c140380000c148402c903140c1c0213039449030024a04441c280404007500c1ea01b002084584418049410f6480e4424018000010f46050a42515810085072035079004503600c0804d000b960408192180b0091032007100c4500c002408140031001d190040510300340300354060003520200180003c42e005101041c1c3d004009034002942c0e51002120075204020055501178904d150520075403c05070710a01d000c02d4003420051034420026600396454504c901c0c90000a81c660800780283c6c00c0a016000090015080c14206544680d41d24600307010003c2401d44807035640e000140a1040b43c2d003002401c9504142900c0150520907255410f0361824001901d60a040a00000d84080002443c0f07104cdca000741d8031040064805e240850f40c40740e8000d290469072054100204801441d0b84440703140d681d09071b1002072074022619 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 507675206 1250 507673956 507673961
    0xa0b0307020c04050106030e0604020f0d0f0803061203250f0602120105011202040e0f0c16080901020106060e180405030c0f0714040b210312070c06050108030f0409050a0e0d0909 78
    0x8011000305030074023141e09054800090030742c1e002603044032081010310302600130801d0010b04c1c20000e000e901c0e80b0072101c81403009510040d4007501c0250b5003256494030f00140d0765668401e4280c4803030f000ca000c4035100c0340c0078088140b00f030301c55200e52406200454592a003405071b800402d1000c2c00012410010030542d83c2104912034081c070122020350810385040708500200d800280361a0a048407200050031020301541100c8080c18140c452000c140503900b449140380c2c100300c401c0d601642c80c20402041c240d00603441440d00302c000920354010494a4065000070140103807046485100c180880d46040700c06010700340045035032030000e0410301e18200307260080b1940e003041240664903000020100341c590b5955102c030340b4940505030308442c1c407000c035092561082c00ca04044024082c020f0040060780480008006400340c08c041c4035990304c464810b07449201c0c80000e4004140100001c004100d0140c00051344500d01d08000108100c01546c007034200100041c2030320000704040d030240650041803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 507676456 1250 507675206 507675209
    0x601020111210f01060f05250524012409030507060c1502030106050423060a030609050a0c12181a090d180e09011e0f11091e0a0b0307020c040501 64
    0xd0040c3c26514003079014195407040d90400042040004080c2d617100b0416287c002d81c0d4000e28074115840d80350f42442501c1744890010a010f10f020130781d4100607280c0924110b41600e0f0382c60f5117003094903a6081c221808845040c50310060124403100000840c905206000080840b6200c1004402032850300c0d443c094500b21903841040d10500040c0803650b07001058a055640b0505444030b241026004100c5071400c584045a121100040801d2120780c1500903500710303480380100384460f8a40f85e1080003a1004583c8840024049420703030390000384d1a802c12045a03641515070416190359450b171b441c00c80b030445504815083c000d81071243c1c5400c2000a034014142a02c0d00c0101110142007502800140e0312800340d01450040108603046000e52042c003500c110300b142d1030a045030401002c4041c004984420701c04510344100400b007000904100e036102440107161503000030150800b10500d03140031140a4201106500c0803a51680c01d0004500034842a0001c2c5082e41000d010007042e00d805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 507677706 1250 507676456 507676471
    0x90304061202120f100305062503021207080a0605030a060b010806091605070c05060705010b0a0602010903080f0a09080a03050103060b0a03020102030a030c0e030a031206170d08060102011121 84
    0x402c2002c2c0803040f9001c4454109414200d948503c0e1120340411828000a80000e4200d0007a00140300082c94604840022121901c6007201d10502c000d2041c1c013240200c02c1d240b8401c2601e540003a940300d110b11000343d4402465003001501b0b5031a00d022078589401503004641369a594204d0441668001500b568000c070b007100c414006103401d501a50901c00c0280e502410711902003024010030001c118a4405044040e00c00381d2103141504040d03000e440704c070800d103004003455200800c41502c103000740792000390151200c0e0303184d841d4803a00e400c860b0401400e0366204c1c1e994407840d50000300301000511441201e07603000b0680794118100340c0110f5010680b03240c03050749612010030050342c021095904820960900142c035040111065130141038107102240d0600a003a00682019080445110b17804480c503010801d4984801c652134040f040101d900c4440c0d80910300d4000c44c144034408640d0700c810184004210240a60034003034240e0450641c05c401c80314040d00580300e2144209190750b00450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 507678956 1250 507677706 507677711
    0x15090605060702010203040306020f04150f140301081f1503030503040614040218061212040306110922231602010c0503060103090305040503100b0a060f0519170903040612 75
    0x2c140c1c0040d40e01e00c12840010800d94000c201035a40c2c11009c81528000c00d8401e18005001001010003031100e0354202c0c036040814182c0c42d19000303050104007980e040c3e951110007403610002c06040150500c1c481061500d000780ca0b0040701150701811600c2c40011842074603090b0300c17400e15141c418141d5080c11241800124160200030240c3d4400c400c8020414542c1c0c840074050700d80c0701c042003486c1e2220164038039500c541f0701500d00071304070940200203ca025050412014014010705e604600c5070861255201110506030782c1014a041000c2444c0c1d041001c0c001410b0359200040d0f050304150703154103203444940c28100241d07118030609040113038500d48000c00255400b60380c043d126001c00b40003d8100f5944094001c2014095000c42e406060001c00b10391088060450020140400d905a030b8040c0041d01b40024141e801401031980b40a220703224542006003006641c6031702140c0300180c2c020000324030000d4500d8083c43c000b0b203002d055102d02842d074450904001030100c01d550407000101c9403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 507680206 1250 507678956 507678967
    0x418020307023705011d030d0b0301060b191b05011406060a1d01110a060501170d0504060503060d0f0f170c03030c090d080c011b11060a05060406091509060506 70
    0x12680707902c003880542d503801514980542012030040101c000030200941d01461906c41c00344000001c4c2004000218040c0403030f001160a2600340d5020303210340c86040b1018800c55000130741c6828090b1002c80903142c280201c1012102010b040c0e182401e0039170b03881e5580e030ba8024241d212190303010b91201d42900d401d4540840b15000170a002040001d0b03080c4001140200200e982c880c00308251010300c10001c0340e40b80c900d5130400c0d4005100030310548032403034a24528410790302c00100c1c0c144441200c41c1c403800d08041c50681d042e9000da000504150380004040c00700300c0012102c42e42c210a890080d009072080d04050701e04440042103a810032542414280040700380300e4000801c41c0c1c0c0c4562050003898a6001d03120100341d4444ca0040028a03060b80801c014440c0c3e1360552041d500c9c21a61282d40402040b1482c01b44c44660b6241900b41c2c0503000180028007460340c0380c21041c3c000c14080c10000d410381e40e86c1da442089640b940c0403442c0c3d03981108800c02566219000381c1c000790408545484c0b41c103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 507681456 1250 507680206 507680263
    0x90114031302040c0e1809070602010501050d0b0901061205030712090f030f0f08071b0504051312020c090108010c021b0a0509070903051209030d080417070503041802030702 76
    0xa000d07406000b846a03850b50203201d5102c0c890a850540c80101401004d4502a65121030f80e020a00712070034010b900c84c0c03143c0021040e00c140203181c122840600f48031181c1000c0e88605190020050000c81705641300d001c0000c21009149000f07015500400c003079910385a442c90f0180015190214090030009910418004146410b50000450350b00c1003440e5181c16080c50100e83c007040070035000d414600049441d400b8412501d001c0700901c2070000040704019110030402c03044070b5080d0b509103030743c1807003006610003c1ca110b0001c80d020340460040b100f2810700b013000104464000d0f0400c2000d80d469810200100fa010031030070b110700e424001741151650700d007004928402d1413032203031034400c1e0746140c080713041c0b2070041c14107001564001c416a0940b41000803990483c2d03220b040c0042c02481460703003243e0301f0752007103807414002c6a0080c0401c008103035504c3e01400c0340d003086c1419100d9003c00c000c00211089000007c3c0c2d601c100805d070260b22860044000303410000421b04401340e9103030743c40c01134880 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 507682706 1250 507681456 507681481
    0x3081f060206061908060c0c0d14040909111504381309090501140a050405060408030612060a060512060f0f151801050a05030309090f0601020f1209011403 68
    0x169400da0104100c04902c10b150130301d643c011001405003405000e851840440181100d0719008100d0f030498101c034404a45181118a001c005084240810700c83c100f8140c0149140900850018038118809030020f0076402980221038051980010100a0b1a1082c03188503040500c90303811800d41c6500380104880a142103040c00340c035150000c0d1603084111b010f10307050054880d00c0b0040081e10b0701e91511900030120f40c0351ba21080182c88001907008149400780300c1c070450b0b100d400b8141a48070b43c3e9070b50b111904003404142e4003200071031181907541c0c0c04002c041d10070a0705000100d4080c0c030309018810b900750403011044264100004200024401da00d03c2da4105100d15155000741e42c51941c9030030f040740b00d10185036200c5c1c0700341220710903104d02003003881c185d82d01107403030050480d540d80406039a8800c102c3c00310340051003070001440310303041204c0781540070b603040c0142c401c00d10641d907049040107030348522103480c40c2001c182a03000b568000690700c00d00248101c02803a5040220700b0104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 507683956 1250 507682706 507682711
    0x2031002040b1909080601090e060c0301050d110102100e010917270a0f0b0a03060f060e060714010e150a0b010e0d1a0705040611070b03040213110703081f060206 71
    0x12003200f1510300c0318610482862000340301503001e483c41544c654184030050b25080c2d210003580e10803e000314aa9081c00c0f0100c0b412110003c1440c50719a81070341c4c484002410362030009066000e24042c00c551141c5a008515111a0303280000400020600d006001c0126450100340c0c2c1000074002e1800c14074440003800d4010751a0f0603946224101100001e0502c1e14613041010040038000000440c2035448000e0070078040f00740c50500c2101d8490041c000392803420f10510000400204222419050810081020901500d03402c0d104c0b0004043c41401d40b4075040300f145050703003c1800a40c07031104000a1680241503030406010580303801d00000c100030844041c95101d100204000030400c402c7d0100c01c41390302480c40e0045098074003442e001d40f01e034115204860124480060005411401003030f0340c01614000788049055440340c0d000d2112071014000441e0380c01c3c0d80c51040700302d041e200202901c021803207982c50414916221007800306140c101504008502d010036401d01040750040345459 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 507685206 1250 507683956 507683977
    0xc03080f0f271c08060907050a0f050d0c050304030f080105090f0c161214040b0a210f1d010c120b0105040f1e060516080702010504030203060a050402031002040b 71
    0xa000b49505081c0c001c5014201400161034031600c150180c11900f180240d0444032101d4690a000d55201d0090081e03410017141c0000010b94104002c007802802041207a00942146c5041810001000500403c49070300d804224003099010080100f099400514178030201810320703210000303500d04400300c1c0080c0d002605043c10501d17042d00007050720050b038040d11848840c0702e855503100551418024480c0010316090f80005d5040b0b42d41052590b00107084a041f62100c1e83c0e1a458040d2099040740e4500709180c001070700d201400703d840081200b9001e0004050800c0c84001030300541041c03c090f001c081c0324042001641840300d030180b0301d50425842c02030090200b002140c1cac01c0c51400100d420748a142c01c07403c604a01c489021802500b140010140340d0000402406000c0e2201c034240e406003d90481c00a07004800031a081c00a84508040e02680f403041c11301c20700f4141c607070340080c2c02d242e41124a01a05980c1c5ca0400045d45000c100c50008241000c10441c6024209107007190782d1b01c250000507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 507686456 1250 507685206 507685231
    0x50105150d0b011403130b06030a051b01050417030c0106090c020309100e0a060509032b0c0609080f0c010b0f030c0409080c06011517070906110705100c03080f0f 71
    0xc00d03036400350f0307100710075055042a4550340c5e150200e0504606852a44141c0b81f41d042c1d0300014420b41000209400010b400c4030003428045122400021007404040b4003504100c814080065443c140d6600c54100c180c1c070b1405192100c00c41d0380740c0c0d821a0195030010042c00e00b007100c1008210b03000300c01c460080ea81070b560041141c18039801907c0e40070b202c0ea0300c00d4121080c40c000203813090b4020080c2c1181d0342c0c00c40030b40c0c51480c28170012002288100d8114000c90b02030348040c2d00924007444610806502c942e1002c14041090307181c0c426a500542540011038200290b1404121428498261000740c202c620403041380c26a000720780e03542080e20324507002d2552003c1489c01d0140c21030030b8440114154044494641e100c000c5400c60345900c0e9012804103500303000024440c251402c0803841001e2940d03074041c140c3c1c60b003c0221201e41c8400c2110303002c0d003d05140494942c840000055200300d0a44441c00c1c15003032440c1c02030001c80014a5900313960365090a10a440500d842491340040790344046 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 507687706 1250 507686456 507686471
    0x1c02060c030a1805032d0408030912010e0706260702060105010c060906020c07031703010b0307051b070308091305090c0409080c070311090a0c1413031a0109050105150d 74
    0x2481d8a203440c10000d0040d00c801b0038414101100d5072000700c400d050884052840c0c170440441048140540e00964078640c01c14402035a00d82803041c40401c2c40c0c4130950011030880c000c001c1d0030303044c15500e41050b80040e180503140381181c100001941420688021240b1140ca02603100039190743c418002c40b410403444c042c9810512600350401000321340c004a046588840540c90a5903490580c40300b01c5028403440c0d40c4444510040050780c3c100c6a00750a03103403843d602c3c5170040303440c0e610040c03100002109010941e8210382c01001081c0245204500c1d49607146070301e034204050519844a0900c0090408080000d0b90102050120b200c0e40291404070703106100740340c140d0302c03800f50640303801042c810300c6000018440f401040011807902a00d03000c94684401ea8800141e856030030a0344003003a2540d00c04483c0014200040140c0b01e0a50b070603403912a125a00c14501c4070802c65421003200820006200221580c07040d00d0040108503a5031204611107204070200323010340c1002501c02642d0341c85 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 507688956 1250 507687706 507687731
    0x515090f010203090c041d06060402031308031e090102070f020f04420308030708040825120c0b0429010306090506090d120515121c02060c030a 63
    0xc0c01128100e4080203545a1924580b290707514004011101d10407400c0c06900098500d400c82030180d59100303200500b03602d50396002444040e500142c202c1c621615030143c0e80c0041990a400755000e00e032100f4000c500350408694619151002602c03901c0b00380d104001000c0082c6200e0000010151f06031405050103500000041c01450114001c0407042c181421007030220600002041c4043c60615840d41e01c88044081c011f00e121b01c40c00001c09164040000c9a546409002c03801c0c0c0c01441400c0143c035104409a045810000b40300b2001142d812916080007008402c1501d0b601c84030461401000381e44494a07081020380b070152002c2c1601c0c030040703078250300040a01d981080e0103090400280f11540e62b0324000d4014140c4603000d8484d0701882c000b00702015404140866a4034580e540c079041c50b1504002c980040401600d10401c51201084003500380d1117103089144200e469101404030349150f182c0f0145103151403010141103400003410820010801001e0740d40041c0502800908440c0300b51 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 507690206 1250 507688956 507688963
    0x40609021c0501140f030309040501030b10090c05040501080604060f060207170a170c21280504090b0402090901060e100203040b1206030109050f031908010f14130204180c0507051509 80
    0x2888c80d0f401c18102400882401105101140a50b030155104203e2654880d1508221212088a10300146040104201562080d20900d410a20003400090b0b280d907202c1c0e02200703e514030f0380140d0145c1c1045004000c90449070900e0002075080307a000d424012259510768074840ea2000d40c0400920300132405c504005420008800c28100802500903160941002c0d201d2035004601410000c0d4401d0380b603900c2e04407501d8030004260800782c0b1980e0400d820207000b00040e1043c0e102c50b54026509000c29880390740d07108052402444141c8584036800402000c3c411814265100241590300400041014102c000c046900c8980c0c07a001c0b1305000d07182c0d000064050b01010300301078801e205401c5130030001c400c048020410800284c84c0140703010100d410643c2c00910901c03401884012038803003008004001c02002c01081e40040241e0310000b10030750000102d0f00181c001c514941103205c500b40c3c0b031960030b200c2c41d00c08424504000d400c06d00943d4400c0d0b0346041c0d01c452100017116100c041101484200b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 507691456 1250 507690206 507690217
    0xf0408030c07173d050c040801110f0708070c090903021005070f0207050405071b082502220b06072a0b0406080601020c040609021c0501140f0303 64
    0x16040d01e658494488409550301c445000f190101848034140d0355003140b00084200c00411890450301440610030890300c40a51840440807810080c52025442e040c00e034800c403031085201c90304154030340e42449011800c540c440144030010100422034080f11039640420703034541d0755002444558650091070100b50000f10740c0e20607070f02e4504041c02002015004903208518810088041260b40d43e2400200d4004500e440c8290142c2c11080c0c0c03c2c00141410340140d544071240d0300b0009a203180c1e002c4103600201f84e02c2026120700030b0202c0c25017214040b41441410041561803244044209500000e50604e842c04666007003041d801c2d145425038502d60480b42e040d0030020109612403456040070800740c40030091055a080c003444480401c0712140c8100c02c103603030140d501e81d820b05041c40d405a60905001e816581580701d404440c18256030351f400b604e40a8901c09001684445484000d8101700001145911000d4148001880490995500300c504800b0441350210141440070200e415031048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 507692706 1250 507691456 507691469
    0xa140a051b1b0406051302031003290703060b09100207091e05010f080a03110109020907030e06160e100e0d050607110f0705270108010c030b01020708120f04 69
    0x1c29000c54803201261003a07100700c0140c2d0074000d50444800700401c0362005c0c02243d520510703d40440c120114070390b02855000c2903d1400110094894075050720b41c0c00d188801401c5c18110342c0402006405c40d5030001d401000500341401911b040030007484039030042c81e0a250141c1e486c1144c050081e0300c20044e2000414404404200b8580081c00308002c2d001c044081080090a100000851000e09400003084640c01e4002e00401021581c003100d00c0011024143e2070742d9240c40400b40075030b0340c083ca800e0249100b1b0b20006075015218003142d04014000b4295444c08507800c0c1c480502c0c07a0419102c407888903007183c00302400da000c440c007610b4a000c0c00d44207503005240308003440204100040c116001d8030721600d9030303c061504200340b16900d07580c2440102c465017103100d0801a03070814010300d440701c442c4402c07490825010070880b50704000c800d03030045036542c2d140d58107500c00c9601131240800006c400e1000d004c206060017485956598185080211900002982c20f1103003440b000341c0e006001d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 507693956 1250 507692706 507692737
    0x8130201231905030c070602031e0f060f030c090705030a1e090212070609050d0f020d1b1706190603240c0c0b0403110c06041e05060a140a05 62
    0x2404101401500900301d100016003035010b8280100e4050b2055074411440c4102d294600980c0da0744010182d0009084091207002c049520158003040310101440380d010100b411200345454400c00552584080304d150194004000003011503c603c24402d9010003241401a81e80d12044003000040c00c002081c0c800300001603d44c0c8884031606d40045aa032802281c40581d420901e0b0942500e610141c0b0030440032996a200402c044c2c10020b91814060303000e19403080030014290089003180d0f820102c100c0301c10324007c040040205124035030902403c0d0b540c050107038504c0c605a80da581c42c80b000c0c0602e01c100c20540b031004000c0b03900350041409507500803075508071842c0c2101c0600c0030144441c45845550304043c0809101445410360040b2a508802c240403d42c036a900c05407040c580d00d80860815000d4805a40429103812004100400d01d41d40304409140010300924400d81c036580003a40300300000c020190007640d0210045d0542c11454070865070318005000c082c3c505204079060380b20301c41c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 507695206 1250 507693956 507694007
    0x3030e0c1009030b10210302070b0a1106010b0c0a080304020a08150702070b0910030c0e0405010b040602012a08180703080d150312030b0a0b04170f0a0308130201 71
    0x1035002c249036044a105001900c0143c6407400c091702410740303e0040c03901d5100000c00d402c1c44400502c0c1c8003030b420f40c043d005803289036840c1d00290205a01509403140490520700f44509050400c1007420700400812a2581c1054442ea0455403503070340840b0041c001d01c2012000c0b40656542c1402040104183c804a8401112a1114140c010b104440d248050f000f0100c0006080c2c4004040b00e64103034006001e1012400f100b00d0540003010081c013130320200719921092038841c3e2614403d5a010340415501103496038078142000342940c01c0305d02d4000f80c1180b07560800749410202480c140303140f1860b04000c40d95035182c9e0500c0070018070102c410900b62103010000030030301c130400c4010920307000c8a540a002210300d145e048060030324148402000180007540c41201c1510a500c0440080001802091030030b948103035443c240d030460f4204500032074680100b5498640c0800190201881c00400384c6880120740c0c030302404036040200120000307801c524042046a00c00e01d40c00c0d102d45c90544c500c25920 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 507696456 1250 507695206 507695239
    0x90f030115090c0801090506010e04020f09090a020c12121305030f070c300b06060906070c0501170c07080a03020d0c031b2109030905060d091a1303030e0c 68
    0x3c041c1035040c0b074040b0b00080b00204902004c2d000c2d82c1d201d018180c40300c151040e0404103000080d4440a040720b00e440050140b4042d07555070150050003405065400360710755140420740d070305025941c101c456030041d040080c040d98000d2204c000d076001c0e0070207020a40700718481c104641588030b02c04580300048400284c420070003890130324101c00e540001c10100015600800c038020141c40186104090710304e2900f42c800010a0003004d25404800900103a080c2180c1c0d00218100750001d10049404001c80b507028407465070f110209643d28040344881010505061007424504d1055820103007142c01c00091040b5482d00a80441d44103000c00b04003003007140c1c1450740040003031040080744080d50401d440701c1000c030b91107100042400e0748100c1c001e511125402004000819417080110b05201c00c095002400c1c2e510031001c2d00206944900c08504000c4034585260050201e141c44030082a28009000301c04078880301c840400e507450700700007854501c00f1003800c1c607009807001810b42c80360094a01d080030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 507697706 1250 507696456 507696461
    0x80708070b0606070b0a0504051e0307050c0301091208090a020a0b0c39030a0c0602150907060c02010309140601080a0b0c0c06071206030b01090203090d080c090f03011509 75
    0x366802400c80c81d845864050030001144205503014154000341008a013859070280d00403900a8412401c4401849003c0d000d80c1030707401150412802600f01280c00c1c803e00c4810702500c80002c0381280200300306582d9544000d610340600350b181081082a20010754243c0081107007014180c2c00600102c65140d0f00c03840d210b0140c4c48101081d804d0b0045044006108901045800c600082c5041090715100c460300440e007007134519414941d00d441110352000c0800d00381c415400141a0f07950181c400841c10200101c003200028018845650041d04100901d950003620700203001d130309103400700d51030038a404d004140651207002d100707071400b80400001314441d00050295079a841200c2e480d40f103541d113168200700b40c00b80d50790540f0240c0050303002651003441441304d190120b1b03607a0b000168658a0382c40b081d00d504003d07040401080e600005000201104020860301c8545500e02803841d803400c0d06400d141400382c100ba0038080e010300710385181f040d40c003904040b1240c543c0c809401c142590b0f03038203400007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 507698956 1250 507697706 507697717
    0x50a03030f0c06020f2701020a11040c03020f0d0e12030105030d050a18090b1e130513060c08010e01170c1905040e010522030e01050a110124150903110a03080708 71
    0x22144040784210405500228022107059040a2b91884103452201407202825000384c030202090750802102c520482150300ad80600345036400c00098108407500718910303103c0c4846803444100c02c01c1c00100843d560000c0d00327010800035840d080341c403001c960909a4010f0a8109110000c1440010102d420210303517005440c0c03000100c4207100c4aa00207125480395140000d03102d0382024403c5002089981c3da038010642200140c0e005201c003591070b0700c45100f1105610036507000140c0703150040054a040c04c03059400740c95200801d808070406000000d55071200d94500a00400c0e880454159412402c403d9100400014205001160314100d04500900302200c8035036500c5c940700c0340f010105800000c051003036a4180c0314051200284001900c00350082074040041124010141c03a0a14080c01100c0510400c0d10072104055041205980400840c1e0090228011003153f1442c1c040c0e40b1030341d00000c8030340041c1c11213009000b08010880380300c01d80d0000381401c1030014181d410804a0b00081c00b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 507700206 1250 507698956 507699007
    0x80d030c0c02090a0e21040b0304110a031406060f0f040c0909090b010503010e03040503060a150308070506071e270e01080a060f05010e010302011206030506090d0306050a03030f0c06020f 82
    0x507060700006c00d03400d070700c26001207901030740e002c0502c01802003010307200080d504140207400c2c1443c1c01c04224001803541c412030b0411580c0300000700322004142810007030aa0401700c102c8460365850002d41c081004441d050f007032240715907100c04544011070301409840024203501001400241e405040c8141001028490320340a0340c6820510401c265010094900703440c401800752401c1d841d03c1e0f0500c1d01520a403004424255006100000092040d400a110180c4902e000e040d19203403544015040030b03650403460700c0850300c2000c950903595200345001c42c2d400c104d01c15070440310032581140c0c640d60029001600010512400410219030000c2c1e018190351242005000019441c0171440c00e5031020f104070309010030b081005000542c01840f1014041410690000d485a40ca4440070718060050754104099001110945e580603498020304010b050103643c180101d070314584d8010045642408810104501220751600f006202d0b0122040800780c42c210588840c640c17506919070000c80135a21 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 507701456 1250 507700206 507700213
    0x302120603030a0c080a030b030a141501030c0504111314090a0c020d210507050310050a050904031b0c15110f07050f040b090c090f010801080d030c0c02090a0e 70
    0x202186400803c030341480703d19948004d0f10f404c2c2e40e035a003032542e001015280c0034561036003003030781c00ca440400c014035a080c01402004501c056108040d0700f0120300d000900c4040381d0007030046c03020070020454076048903010380b000a540c1c1103e10564040d40034411035060020f0855800050302c0c140000303c0340d6000c43c21101021152035541c0e6010884103205607038405a049850250b00d03840c001c0c450416100d42804480070450300f00301c83c00303003120800c5600102150303001c07091001c1110302c0340188020349010f688450105041c400015201d03100200b0003010801c203810b281c1004126403007205640b96026030b2581549803076846a42e419404c09424000184a65441c3c3c8400d0030300280e1504c40c442c4142c0034000d01c60400060001070800d1078500b58200d43c59150310ba400303483d0f0150340751098840f540748549032100001045080d41c0410300e9030307040103800700c01441904001704e05100000460b090020741d040341d84000b03965041c070009020b948075068404100340601d140e004081c0300481541038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 507702706 1250 507701456 507701461
    0x6021902060c0c06041b080d030e0106050d0521070c08030705010b04022a0708071202030d020313060302031513020d0c0f0f030e010e01020f070302061005090f04140d030212 76
    0x120041402014442c0c0b140d0f1307010340041340c041010480c40700241034400000000041e00c07014400e1400103c0003404000a640d0860186210400c1c440d08015001c02c0b24185028482c50311400e5661920f0380c840c1e00000700710111103004018400c215401e05a000c108905243e542d01d82c5551660232003081581e5950034800310700d00a20f02842140e0710300000018103c00c500d0000482c002d9281010044502403140a4010622002c05c01224008101d00300c00e0462000b07031132041c54102a040100e1400750751080c0203101148007414a00d03012380c3c3c3c4515005031a80c0c0e9050703480000c0c08805107100e4021007155104012168150018100c020307140001f8400f095420340115031407501740c020380c0006000320b45210401c3e0b100b0342010140106040003c80c410916000d81030890b8408291007001007000a403040030590107015896010600d14020400c00b880c01d03011640181009119001e402c4240c0c000504121000c40c2503000d02c50f1610443d0301c5640c443d040a0001d5002c20110003000c28030300e00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 507703956 1250 507702706 507702721
    0x5041104090f05100b03090a05030c01061d0705030619050402030a02030a0e0607020601140f03060c040602070801110a361409041101200604080d050a0207020a05120a0602190206 78
    0x143d41c060b910b01c4d40d00b02c0070545032000c198030542014020f2083e901940b08010041901000605900c3da07035840005041440c020121040543c030201400c00307080901d041000080e00081500d41c08081030703c0b001d5501540d91051110014540c0000340c0c82031002c0107200020001e80d02441c402d4040a808000c0942843c1145540300c0080720400c0050f4842c0005000300403440c60701050001001d40b01c0c01c0040d06032400030b41040c07400c68103501140c41c00f050412001d40d04012403001060044000c02158520b03170320310b56042c031901d115a0300340554405001007140e01018a5040c0140750444e80810703060b0504001140308841c40740c15184800020f15440d189082d100300b0f40030f281e109601e548906e210000554145155100d080c050001d03c040c04543d4440a1000900c01e6100d44141691200310101440444d04040e10054845106000da200180c6a11a00c24255602201d6683c826031800c0c541c2890520071200041c0f0080c008603101c441e07151500541000101c60f502030b116036688186 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 507705206 1250 507703956 507703961
    0x120c02070f1202030c1e030319020606061303030e210607030b01030c02031204110904110907030501030803060d050115060c0c21060f0906020304030c02030c100f0e030705041104090f 80
    0xb03030040e41c15040b4801c25540c1d840c144001c00c4c40743c1c03000302100c0c001d40741d1100060300310f82088000790021085070302c0302c4000c50760600034998024011560309050190960500c0d4001d480c82c040101408850186003042c1d64a4522804013407184040010075150b10000c05903c44009840c4030010a06010350030303400c0d42c0240100c21034000310b60b0040d070400300d80b11090716503010050810303260100758035098481ca031180d00c2110b01c640d00410904048014800a10a03203010051001080601d48001480003542e250202c3e5000301c411207001c1e0b07034010181802801041075400e000e80d40041d200c0006103890b0003180c4400d590f030140b48058846a039991a2400800030071000c5251040040d80c030100240307142c1d0102a240c03500304000101b01e00c507039a80394100d80c025541a008141c0c143d440004500d800c006c9012415026034441651810802010b00b001c41c1820f182000e0100c5008803d0303d079203081260b03030001c04000340240b0640101c1c0c2e02903e15075101d80141ea450030304051065000403540d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 507706456 1250 507705206 507705239
    0xc091c0312110a030b0d0c150809010c050d0c02010b0306090d031a0d020613030b0c0705012d0c030b03060414070b0a140a0c020901090c020712021807120c02070f 71
    0x608090b10f401c440b0340c0110002c0c000b407034403207900400030fa81c000041f90130401c03a4400340c1000840681c4502e880c540282500b980200391940743c1c2c0c18001c44240c141c0c0d0042c2a40c84907030902101191100030f10000380c0c09231014020b01500351041200300a100c3c0c40000e121200d001e96500c0802a02034503c640030b542200b011102a001004088410014107100000b8603c00e2142d51902501d036480b60389a85001000342c456940c81e11001c00c9001c00d0150038425114224446201c0140080145220380c4e1a0745854501402c142e07640c021130740e82c00740607421010050b0030040c00d40300c10349000d00d00300660042c5080011301134030402a021842d5460401201c600840c141c0340c2c00a40740080c40c503680d003944100200c0c4100805140c082c401030702d91114075030282c29801c0021908484c081c4000749481b070b07194080c401038190400310b400540c86d18046550800b014a04e13850555540202c11303100441004000c94005103071021950b5a03640c007007400401da0f1f0101a070300fa24107950f23201e12071070740700003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 507707706 1250 507706456 507706481
    0x901080a0b070908070b070c0b07021318060e0d03061a0403121106040f05210412020d14060403030c0f052d130f0b03010e0f0c091c0312 60
    0x841010004074000e8030304954400260700c0c0680c4100d4448082d1410041282d0182c0321103034000c6601d40401a508003c200606818150a801c00300c1940025100101c00b91a02c080c0780e50329036605465900d030074024552941c210300c05101e0400c1464074180e484404c4c81200300083e14240c00800e248a4072155114500101c407000c2e0300306802c0d9111202400b0244e841802030000702c00550340144000d10150b032159002d20702d4800d04242900b0300714184a40008031400b050031440c1c01c0c640494502041d1800e80b00860381c0c81004003924804110750310b81d01100507001e607407107111910f661140019158410b074460b640a006c0710490810903503071030381a1070356480418802d1148800303c10400f40d5514801c2c030350030b003484502491103500d0a411342c0402001603442100300e100744062591100d40c0030040408090017407466142c038a11071540da202610300c1007a80d50704000304010710a11001e45400c004003c02000801440005050304010b140c0c900b02c1c007142c400425080200b01c03034401c1000c5c0250 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 507708956 1250 507707706 507707713
    0x101205010512072c0f07141303030516171c0603020916181805090d0e01080c04180b010e0d080313020303160b0f0a0c05120703020c0d080114090108 65
    0xb4000c1384045403d003808400200002110f000c0c074000d60f00910305010b0440741041e003555060843c07004181c810800a01007045500f001246403c000317a87c1c3d000121707034240c0b07040f80d00c0751a00140d140080c0244072006d002890150001004414810010050b005241c1c04990302164140020f10955201d88000381d805002c0381c000882148140c0b401c0c0d2078034242854040c413610001c080115a0150681010302400c04664119070514424812150030008030300003490282c0780508000c210940c00303081641000002804a000c140071034080e500944501804c560f00360050040e404024804800d02c02e000603030414200d0342c2070815406684d005034202c4c000d00e2455950b1030b00e0041241a0f03000032030301484100480424180d0080c5811602c0c2e1051140c0b00f1107092500740e2000c15640502860344c1189002c0507000105d070444212010080c0048443d2860f6944900a600030b01032600f0f080a180100d05c640e0b070240340d0000601d07050300c4501750754020300355201040c890345940c01d0141d25402c1c0e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 507710206 1250 507708956 507708959
    0x3090609280f02060c0105010311280306091b060f08010b1314060403060908040510170a05070908010c02010c080a02120a020c1f0b030607031a090c0910120501051207 73
    0x50b811078003550818000740c001071a040c2001a46030840d0001d90044c5c3e00c0f01d01c40e411200b1140380603000c1e0307500c1d104032520b683e4062a90100500d6250301c680720080601c3c0da207804d40c50401c4028250032052508105542c80d000d80c0d0350381c01512540b54415240300003080880003059814202c01525440703400c0085200300759003810380c50b0020795109402c4991010003803000000180082c01448205441916215140d0f413800081c82407c9685034020702c18041d082503045261410028016407003c5250004174054583c003a00f5280c840c500e4020103c29420315114900c41601508903600450301c3d5a100c204654a060a48049001c1c510f440300d0303461144000b141207140b01d50041c0c610340c1d0000c03007690b06140000c3c007210b6442c0b51507414800740e075032200c62039409440c040c02019401095401c00303200d41082130f00c000400c000345107121403140c100f01300401e416801d400d068074810700020b0102c071801202d0410203040032403449a40c00d80070b42450008150360809043e09400f0301c81601c000c14815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 507711456 1250 507710206 507710213
    0x10151101051e0423010603201c060207030c0206030405030c060c090f0105031905100e010605030f01030f0c2c0c07021522090b1002060106080c070f0501020309060928 73
    0x111000c4c40d41c991410300340701401800010030700c41c0030019403040f4100c90b4096247d190071080074101d9803426114403480c08020b04034011512403904216404100142c1d9482e55180580c3c0b004600507019420030320110402c0f0030004004003d094119041c0d01300c2c0c0081c3c0c2e038070703900600798401d012055402000300c01220702c481d402400550380008130003884902c40074440301c2000485000301c07480181c4039601e001c02c10040c240684035601401803443d00c549540790106400024a0041c03000420301e00c0b00404d0b0009100408000c003010784502d100d0000b602c0c501c1a0b45212025141130a80d40c0e4100350340c0405e003500c69410803115890740c064592075044070a4600100c1c02d07003002590aa4a201c1d018050200e050310740c00c0c0c0c0c009403603c0e04000a00309441021320112240189200d0259889100140160794000c0382c0341e0b80c45600e20b00010b030343c0c115a2500f1407400c0302c110002021507001100740036107002e0224420b48515501c40841324484008401141c950400c010001413900000d00801d020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 507712706 1250 507711456 507711473
    0x80c07150e041b18120f140c15030c191206080a0209040605130c0803030f0a0911060c03070501090b090f0d0e010302090d0213060303031109090c0310151101051e04 72
    0x600c0c1c2080581e410785e07603504a6400e480c00c5200d0071600072803580044003c108184400e00c0507035650070300030186980c2c1c140100340408c01c00340c40d540d09050088001480b00300e240049a58000200300b51803c561020f000150080d01d21440d141c0329582404404075908d8030004016408603002069610b0507112500c4030401404050160703818800c0311420701011500806c036140040583c0740041d83e0300d2405803918248241c001d80982c100d036007010070040c007213080c1111205090741c3c2221000d50b00e0f8000601c0a15500c1403000007030055003854071420a100c80d100645200d240c001051321600d04002c603a040e00c03104104060404607640742c0b040380c4554860350180030003100240921101c15a035400141401800ba007900c61165103d01c014820141c2c580079001d01c403c0c00c48011405e18402d02c000035090480140141c045520100000c1c0c6169001c1c02d1400040004181181500b00103d40092510f169508110010360030640400c0175880c85032000e8501708004006c2c0308503070b20350f641d4035440c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 507713956 1250 507712706 507712727
    0xc0201210b090408040810020405010f0e03030d0609050109050703140a0b0f04060e100807060e2707080f1e01120609080a03021b030906030f04080c07150e041b 70
    0x1480c0303940701ca9603050303900ca80b0041030181d40505a49911a460708500518000c02800c40e6401d5600501c41003207245d82008039080604d0240c102001c0303c0100382d000c2460760047c0c07036426031903908002001400c0c86041c2c1c0940d060350501c0f5410320999842903003d605840b81403054080030401e507000200440f9940c0d01c02c40e80008010050170354008003000042c140d820540003e02d000344103074203008440820701d40c5c1c1e1000f0444480070b086030914120340600710090628400d4000ca9000300000094664007020f4420222040311844445c2481c0c0c43c0140b41607801c031002000b80d85038001085c140381003104151801490010f00f10800c1c2e09001140d50481070030002107803003946420700080010116000341c502107555580050300c9031615070902c001c2641071460317040741ea002048940e1050704c42c40c048903400600d02d404070240340c40e9454840443d219004400c44c103030084c480702203040d925a07842076030741071903655402004289440030082100c11201903040384101468400540303e014009002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 507715206 1250 507713956 507714017
    0x504050f06092206090c0e010806010e0901170f010603050a0c1409010b09010201150806061350270601030b10030204050903130f0b072006280c0201 65
    0x25a651781d449410050342c18815001000c5000108041506c1d40d01102069000700240b070880740c074045100c0421101501030113841506040009104082c3c103003041007076140e0085ca0020024690341c1d0411640b41d442c05a000c81d40c03250741d514006619440c110440c21240d5009004520607480d003400c5440c1c4c2d81c41194400c0c11b554a03001190300d5083c2140c201401003503180054031341c901c0e2120400c026210ba601e100000305240c4220f070700c8205202015142c648100640c46000040b1065a01c13944d00d00000e042c10303000c2c049000210400d13007444041c90240620110485003501c5000c0710005130002e101420246a22000042003c20107000d50b50340c010340c00282081045480742c004c00d0035a80c044607822859400069000c4401d4500e81c0c090004042e0260541a81c90030144c00841511502101815100b080707078260003336100c5481920034105c0024002a0f5545907603941103c42410700409850080b41420310000301402603254602c55a4140d503040010003030003103600c040703401440200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 507716456 1250 507715206 507715211
    0x1d0319032c0c120d0c06050402011403010603020415030e1510120c030212030c0718020d050f04050f010c052a07170f0a0309050607210504050f060922 66
    0x500c070310781c0400420308260101070050010503440505010001681030300090060b444156200895030707000042c100d003d81d0181001c52161030303c0c0012038041c44800004005080000000129160180e009108540c0c6100700c900c09184040400d40c100c0b00300c140c880f01103402800500310083c18510b44c45500c0817403c40d8004100b40c540e0070080345004400307011520003011543c18019864140e1003c4510070320b00e0004c40c90314480607103003074480d01c0c20f104000042210b83c100c0491050160180d42d400408031600f001945440364150032015000d031415921070040ca0f44241d240704040c011080125040d4a61b1460014136030400c50020107040600002c000b8619400302131b0001c14861000140702502e81e11616141c040880e0381004608446146150b101b03414010001ea0450040c41c21500c0484205880b58000c1c00c26504101190440d000e02e41380b080042d102040d005806042501d03c16501c07080c0d41107220090064a204918441c0e0340311400e6003e5400e0361018840100c1d00405a1601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 507717706 1250 507716456 507716501
    0x1f0f020706170c032a07050c040e0c0909030c2b03061a0901030605030102031302130b0901061b0b09030a1d0603010306090305070609110f090411121905011d031903 72
    0x850083c040c4062105c840c940018000c2c00c4c0041084414001d4100311010081c0300c49034130704c0c0e558400c50f07820001d014401101c00170f0308802041c01600c15121003841600c0f6a0220804804000c140f00440c0c00700e01109254070885041c031038400c07501614228500f21440c000075109509040e000a10f00303e04041d00d4000100392928203001950085203502c0d070050f0303003421910411541003080d013590220240381203400c8038207030746206002e0f04640450408000c000c00c0150b01100981903142d001e0405a054421f2003080c0e07400200a05034203032270745d440080d4a0f2130000265508080540c001c1c0d4404400c1c4010b0020426503448000440e1003030070032910f410340a9861000362965010195103803211928941100d04000b003070400c420f0021162100d1384d1400343e551800e110b4551484070b01600c0c0303865100c080c54808102c510045010100700300d9a01005240a5000c0c00719a284e42c1a1032a11180b09114200004181d5031025809529501c1c4401001021002810884048048130b000d0504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 507718956 1250 507717706 507717751
    0x91113050f121606020124031104180b09060610090302060904060f090207050c10080a0e03040b040e0a06050409020a380c1c1d1f0f020706170c03 64
    0x1a000521070080180c0c400c0e03d180000c044c6c00c640041040059603607100340c98960030720400422400f52507028031010b03010002a000b080c0117015841d000d0541d1504140b03030302c05200411070882d118050203012580640d0306e40d03050052200300c44072020b020960441c0140010300d4100f02504015401070400503a00303a560074500c0e01011385512200c03125034006a604103100040c082012020019a560840082030080c010008440106030b0300e880783e0351b410500c00b035180a200b180e0080000c03402c2951650703100e00740080d034510b0607295031044610700f41000600342024011540600d4003307051f81c85452a040141d840001d40180984204010034180860788400c01058800e03075005422883d1108080e00c501842c180700004242e80703d5003101031402c03040d603000030071b5980302c5203681d004048443d0480100d9013541492117820702042d0001000c0100b607520a049007032001d20740e0300b129041590b07200c0646410100c000350070a81585280003811f1402c005005503088a07203080c061030039090064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 507720206 1250 507718956 507718963
    0x4200315060403140607030203010609121704090605040501170c150d060f0905180d050c19030c12050c0613030e100203030109140c1603210204091113050f12 69
    0x200112803618400404413810601005460380c84003030f5003003c41c40d55041c10b0010309480c500344150382404952041c01001c01020042800c0041800c5200b662182e4a0b41c013500048c1c010340c018075020b54a03140001503051682404900c40e4070f096405020a000c0290a0000300181150720b900c550108025903510012180300c0c042c001d040b900303120400030741441540001d56801600d11080000c98a00002d100c11000c140d020000341503080c4030759a544010036181c1003110300d684180203c28001200d209142d005070b4480050740c070a06204045c42551007050700c0d58043c95800300026400880011170000102c2c6c44021040c0c024105032185080881c00540c11034103607a807500040e000440100b189464600441c0070381003072a0071540841c600700e0802440d90060103a4250a03141e1740d00d0301343c03c0c9801140d4172001d206500e07125410082c00c03420b0103800f079400b80c850381544500c5c16141c5030380454403109440c80c881d50a50802c40f41881c040402111040103000c0c01c3d400750010f48146507200041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 507721456 1250 507720206 507720209
    0x2151501210f0509063c130309050105030705090405130605071d010e03101d1204030201080606040e18030c0f01060e06010e060a031e021204050c042003150604 70
    0x41c107000c24801050221102607640c06000c2e0b80150b4800c1003481aa0b03200c2c404102220000c1e00380c85a4080103280f040d00c428054018011801007101c018480032010440190100b2802030700c3d50b2009030341d50704c011a56484201c074041c000840c244408800ca203001e4000c590443c0100039828000344040d2550400c40b0010366244001c24028904561030003000c50f03c050107031009080102c00e85003240c010a441c2d006074000351040554070466802c00560440481501021503021211400040161100c56500501042e0b001c81d200000080c0c492422200319000c0d00e0194424240949901500e40005e6849105100e5140000c0c011f04803040001c00209070360441100022642614000b64040140006031445c0c0c1001900e06200c1c8454076078404072074042055190016108400c4400340da4401d4400b14181c1c070031400041d20801d0944405a1280034600484c159003c03c40701004000440e40d145400700107945d40700d2224460380762340c0c0f800b0307647c0841200d00c200b21203014140010301a5125 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 507722706 1250 507721456 507721517
    0x7061403040201020a3f0c080714010507090603050c0f18031f0207020f0307080303041b0e0705040303080f151e150c0d2c030f0f0601090c02151501 65
    0x40c048100c1040031b9a41c010820038060700307041d510150f0281c01c0241082600b01020b007680c6400a00d60040200c95079400c0e00505880008000c281000303100108169030b54030404c40000d044c000070400c0c01907600102c40c88200c0015a82d0b180000000418078002e02c42911aa4580030321141d0b955094524101096101003407000141d581085d8410002000c1d20381c2c2d0042e000f40e00c4003405100c1c0f80800003c40c1c0c0c101c1d0308060500f010b04401d00c03181e40c01c400140c1001e0304900d04102405400b075008806041524800d86401245542d5201c9010081401702e0710308039407508213440b069150030440c00409058001c5c508000c0700349070340f1021641d460410030600703100a100040c01081c00c107060001c42d0342054035280001407000e414004074041ea50740080400c108540d0019501a0340d0208498030000d0090782c01c1c1c0303004042c1c100c2102d8440c2000d100d201035440c10102800a980c1c030200d10442d06d51079602c004c0003181c44a290800c4d20a101914003410300c1803410b18881911241e20210621610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 507723956 1250 507722706 507722753
    0x105010e0111100e0706021c050c031603030903080906100b0c0c09160e0907080c03070302040312080402311505061c06051c0605040510140108070807061403040201020a 74
    0xa2041d05540b0b04038251b0300102c1190007a0000903454070803048800b101000a02d4003540b15003e6454540c01d41c41000d2524801492482d6182c04154054208100c094042d89540b08aa582d0038012034950508481c01c00b0401c0e0f00322424803103840e00710060b1101154207030845001200003008211072003c02d07218410800d41c0c4000c410300e0720758005108400c144058601181504201c5000307000d103d00502550b07103c1030040002800180300303074140d0f00115001043d411902024410117420058182d8083e0f0040c00c1c654800d998000400b07590205c49a6159058140b1034500301200c030040c95030400c042c0c0104880100020140c0d40c61000e05250303400b03050000c0b011441c84220904232102544032602950b59000040681240501e4078000c1710381055021610b6035a92500c981050b01814130f0348182c524084004d800d01d07020130404c5060304e40c000c0445040544070a01c40d1795805180c40349030006491042d001c0414a40680595001841801150002240ca650324034492030f80c031480481000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 507725206 1250 507723956 507723971
    0x5040804090608060f0a0227191202030f010605010e130b030d021e1b060304030306051c060506120d0f02070317090f040c020303070c0309030210031d060f0105010e011110 75
    0x484807400c503000806c00504600c0e000361400d00305060300300f102d040311840041c070007400c0642d181c0340d50114040c1c0c010200342040946504a03400c0e1074810890607802880f030030620b00c80c00381b030510865041d10016100c0c11105501c440402c0091106c81300034000040d120030b84044203880401c000c02084217241c010b003c1c0702d08043d09441c4503101740c0444071069401307614403c00c602c80d40349c1100700079241591310581e03d1351075007019005010540e00c0160410110702020302c8165000200300c41440c450001886141c90314401c00054408503a00441690000c0c5040c894040c055a400911644180150740c1040e580703451344040030403014100184450002040140307803030701c1d680c1d8005041044508019012100e040295603000040c40e110a0081d801d01010500d8003910b13000d4003e681c01031403000e1040152400601030f20310718142c4588e22507a6800c03d0311031500440d485200f0030720010104085c1e881c1400441c1d103010303c59080343c1400b48441c1100c07854032040c080c4200a1000050124004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 507726456 1250 507725206 507725221
    0x8070203060c1b0c090115110f070609080a080f09011e02010603030e1c170f0408010e061e0c0d0f05040b040309050d0503030f040809090106080a0605090403080a0504080409060806 79
    0x782c3e000a031208260842400070300b56664110789103056420422040d058800601c06c19600303101013201e100703894410280c00c45d15000000540e001541e01e02d54850300701075521440140e81e0251801e00a002c102c0074000140c51410041c06410b00000500d03110100f43c285820f503210b0b01c0e5103074241d40010b0351170704000d205240e00800c4008014a00342d0700e12a05c0c424010b24010041d441340030060000000c0001041405150001d031076540603c3c0003841c1e030715592560514004e01c0040e4480b60b60f4007803040000c0c81902815580c0519011040c0300b45070a5880f222401002e0f4070608a09200c2556a0700040c0003030b10700d201e00d520542c4240c8040d0b0711800d050130301911040b0b031580030fa13202c1d5040200100004501109484c0c2080390081072041ca81c840746440d405600400c019550424019000000c00c16031042a4501811066a08008864032101801050b2104507405804201c641e400309121809550204e0390041c065000c81d41855141d0310a0003e940c426400110703507074041c0e418080310 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 507727706 1250 507726456 507726487
    0x20c0114010e010e150f040c03110c0a050601050904050a0f020607170a0e0f060d05090703020306161b0f080a1202180f0603070e091008030d06060f02070503071208070203060c 77
    0x210b00c43c0c14544154405e400c00090440c1d4801d89854022600c0302145089103010303802520324040001003094407a4060f14807165204048842980c03188143c3c0c1c000a014204020307001d0080d030b0804054400c14259465003000c036100c1030803ca8118404104000109440c41d00004200c49205281a0769410154008068171402c0246500c90014141100003507641c0c0c000b2210864001030000c5010358408440a0a180c8076a00213134160095070100415100a111501c03041c03595501c03008000c003000f5064014003c0c800030f005005001c5903207454042043c141c042c0c0038480d01850f11111907026408418240e030040500c840191101c241c40481915203000140c00b000c80c20741e0107904500d0200e000406100302c0a42c0180030741e0501c404995906040e200d00303005403003003804582c0d440c00e00d02c0080c0300400c4a48683d90010310340d5004c0000f140d2000c202c280494100400034500796041000c1980950740d100421158a003040022038010384050002900c42e120000f4001d4030f80c19000c844075070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 507728956 1250 507727706 507727711
    0x5031e190f0c0504050d0212010f050708010806010e0c03090c0a080309040b09241201060f031101110d080a0b09011202150a0c030804080c0f1006090e030d020c0114010e010e 76
    0x541030412401c00c52056018007500c081707681c00c48061701002d005d400859074100310303100e8450040d400d0400d18100359003a0703084540908142d607951100381e070769141030f961a02400e0082c032803600101170109034280520b2015540115007601034800100e0700b200026138054040e440070b10560408100c061192915100e0004024015a00301a862628020502c0840c8041078051a5988200703820318941d05c0e0094400704a202c43c3d00200491901c0302c400762a132161500c41180d136444003907404042c9500c0303400181d441c03c4060b0000e1030400c5040340c9c181c4108000600c50038100b03580d441340113003135500d00b200c4034001e000d51005442c0c190b20f240144454a800d1480818941c0020006802d02030b5000746240078035a00f52810109984482c0340c48417080c415010b41c07841a104030b1016400042004c80c50b400310480e180000c20a455840c0c0c092025250f41401d9965160070a00004202105030340080c035000c0c4c010000016a40d0382a8480b40446400ba0414500e00035424014040d81413068103c2d034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 507730206 1250 507728956 507728981
    0x13030309080316080a05120a0e1c0e0d150c0e0310020c03070b0c1c05090c100e06090d12020303100803090f0118030c0b0c190c030305031e19 62
    0x14075002110748401d040d50302c038190041900b0400203040f17844500c04c0707080c0e1340c4201c00054442c81500b010000c0b4005441da50064081e5030045003401a24403402605440081900c0e41344c10064503030090401203020052017040d03c1c0c241c0d05a80d290a1070010b880389400d1450b082d00ca8240719803640c0149032a203906044881e00d41d0384104401d141507040042903642966001110b50b4055958511110040c080d1440151103e2855108525034407001d80040384681c001104031440345001d4010404803002c050a0700c00800c11a24040c3d8030342c107040d0014039604c8405403000e03c1210140c0d45602c10b0754014510940160408014080784151003000700f4000c00d00c0c5030045042401080020300c5c0c100b04524a2414010019613010070340c209000a10011500000300c0c00c00744d0740d034241c046110b50040d09001381034050940610181003400001e4062141c10a1040c0b1100e425030b41d040e00c46d0751025085078109404401c800f41500c402060b014480d1150300c0c00300c00da048400541d101611108054003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 507731456 1250 507730206 507730213
    0x3120105090f010b0d0b0a060503070f080f01092d06030209010e040507060c061508030904270b13140d1d090c160b1f0609060512040c08031303030908 66
    0xc0c40b58042507180d0550780e9608400ba07030b6084481c1d0700001040300e107203a560000b814440001d41180c03c1406103204d0131545d201c0320040d83c41d42074210b540c11000c4507a40510349016006110030015079200903940302c2c0915510501c0c5892030640c1c403405080303810011080351219020303c02c600309a0203d40c0101a0359014507240e0070070f0b948035030f124001ca000d00010803880702c0d04d99051010340c3c2c00a84030301203910518011151100003a41d120f52181300c0d083c2c011414901c6107942c0140050a84c55120014170980811113503d0791211000400501207882c207550020a01c004a044e01c85122044a040d400038002401318000290005000140e040b110f140368500f500043d0702c80c06483c60340440401c1c2d45950700c910641081015003060030f4040e1400350319108000c4090b088010101c1d4072210283d40c09042d59a940049445078000c2c090a030019406010003240200b4002620b03400a00c103213a40c641c2c2c0d94072000c10911b142c1129020709848042041e0030014990800340c0300c0301800820727018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 507732706 1250 507731456 507731461
    0xb040c120c05010815130506031612060209060405120304051354020f04091718100804110306010501090e0a0e010203101a04030b0414010b09090312010509 68
    0x80000c44034103440b44074180070303071600050f42075880c030394182c0c1500c800140300040200e640c19110000b054210340300c0d80284141c500ba51001c44895a40344c00300c0b402e40d8108250444079a6444029401000e40f90ba00310109010110b21651103a04001d11807440c00021910b81d880c000400c07006000b20188002c21502d4205800c10718100000460034500d00c0180076a2111800c140d042c0c903a41100c2004101012000202c0743c41e590145c0400c4082030003152040c1108403540c040004903800c0080c002d0200c0d03440328002d00300c1200072002d0620224950020304145091101041d034801e009000000054003240401c810812a0384000105090030340080129605141c00a01448281c3c0509018450381500140300a400c1c1d806c218122400540259101c1c10680c009138480c01d05801030200d040324161501d569060070200b91022a0b800000c2007615403551f0706d40c004018981840490342e9526180050713626199110035070300808a40700116a244902c2da0100c4c1c1d20036040c2c01080c0b1951040d401d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 507733812 1106 507732706 507732713
    0x61302040f03210e0114070206030114041a0a0b0c240910021306030b0d0506010e1f0b1b07030b07030204061b031d04180b040c12 57
    0x14802d4a026400c0030f26041d420080000000910402400b5010342c07140d03002000d004003c10041c2d140c128142c000ca0300c141c1c801d03042403204001c0a4500404d600301881540c4a401d4150315a052140320100042e0301901b03640f1400c031403620081500080100140000b00c142e01c0d00c0510301002c81c070070003079410043d80210b440900a00a00921403080000c40c0221141e60b01c7e00780c841c0d0151400e1680990040c6010143c00e40c10503103088041000600c1000001c0c0600301034100304038285800b003201100e40603070075100a03001000c0c0c1020081d03003400b074083d107186040c4250010640d41494121034a0b24086900203000000b601080c0030b078094140d80104182ea030140e41d0a00e03103889581c440c1c8079a030101c101c000d001402c0c524080c0e94058410307241002d400f40040010072080036041c40c0391040d8100210642d202000d6005010411100310700c1d0000401f80060401c10315030b00b544 = true := by decide +kernel

theorem cover : BRFrame.Cov 507553956 507733812 := by
  have h0 := BRFrame.cov_init 507553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 507553956 ≤ n) (h2 : n < 507733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
