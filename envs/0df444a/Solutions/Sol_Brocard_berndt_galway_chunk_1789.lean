-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1789
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:40:44.90469+00:00
-- url     : https://prove2.me/submissions/d75841eb-e93d-4e70-bd23-8d6a0db1550d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 321582733 ≤ n < 321762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 321583983 1250 321582733 321582743
    0x40e07051b1e010203060a0b030703090f06090b0105030a0b0f060402091e10181a1c060f0b071110140403030306330e0f150712110d030216 61
    0x861614944001c580d45144140035802d0074003403401600e0940c00c030701c02565465031141c42d441c002c000ca400700c13001455000c8440d060015189000c0e450342c0080c03280031901202d155644500d200c00704814440440d025160a5005221802096982464000d0060241000009881c0c0000d41d5546c0d01e8040f00c0031420080c1c0a41c0c9010900c48071f0481b08901c024040c1e04c074204546203040b0b0584108402d12035100321300050403555180c1980b1a16150b265080e0310f400750020004249005184074070020360501c0c03108001103280c94040301220b502469041394030031420410250700418905403c4004030b160444030750107545203d850079117846c03004610780c1061100202d030000605070958410000c950300d03645c19150522206081c11507800101c074211410f14000d140001c03400b03102d01083c4a48040c0174040d846440c482c000010000f608500740b1030202030001440b44100f100a44020009020364240300d92440c1201e45180d4950328030740f031028201503005c00c5a183d622115486c1c0c0d02c4140c1c100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 321585233 1250 321583983 321584017
    0x3070f0c0506040e07120203070e060d0209181b03041208130506070914030d020a030518060324011d010e13060902031e150409110916090f0b040e0705 66
    0x2c0c40d6001d105032400c680c4078002c20040ca00c25401d03030a0034008c43e03120b450940c2e43d0741a0543d0340801c00045400403410358994030317405c3c005440140c0b2a00003803400016101420750b80b0703180c10500078041c8142c0400c40c1c151140140103000018842c1d900c1c40084003100c0c2010783c10313581c2d44a04090404980480500144920818409074a40100181d003e40d0105031903d80d4414000c010306551381182900080182e00c00d0f800c80c80403a210324058075148005d2185a54400070510010351a50025940c0c24402e4049480225030307c1240e07607001801840c207003001d606c40180d072200c030602411010071250510001d964154001e699031207018010080140c02080aa42c0702c3c0803e0009420445070095928210b024507404207030407201c0030344904041d50880070401444020310001c0e01c0000320071034512081c0b11100020b951008929407180b40c1c1c08006003141000c0c000d0080169400d94041d90040103035200a100d480e61086c00c942c1520010748a1000c0d0f619180400c881600c19101040840124 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 321586483 1250 321585233 321585239
    0xa0f0209040809031f0605060f1819030c09050717060402030c0909090d08060a03171b0105070806010e2d1c08040302030d0305070503040213060f0f081009020303070f0c050604 77
    0x48100c210802d9000d594100180e540700c405100a03841240484a027600003400960744030517101903c0c0c0380000307020344072121003800d090010040c0c09041d001114aa82c400c1070500040680b4072407640e10070494a0040912000040000101000079044a014540005c001080b6200103422660300d000050f11450039854009e03562500c45c120002c0200001e0088000305103e0b16084144005494001c0110120700c2480c0517442c4040c1e0100181900281d0b0142846411450170f01c9124403510164540b12100c4c907003040014220024008914411504d10494601f105020034440480703141201d01018403411460000b881d840c070138040e06244080031100300c001c100c2d0384409002102d1094007100c83c1d0a0701484241c0640340c00304d42200010700e00780001809460040d22516040e0400311000030801d4884003811f014007041d03002940ca00d2001d140c208101d120030040d422940b02c070b81c42c08101c2100a0303030000752039100720403000e440300d180540c040007030080c205c01450052000a2074150341d01d907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 321587733 1250 321586483 321586513
    0x5060d05090d0c080a0c0510050103060b0102010b030f0d0e0402190f0305060301050403080f181b0310020702030706120b03011a01020105090c010e040905030f0a1701080a0f020904080903 82
    0x8411608001c8500030607140010150051400286003a801409242446448103044a20101501c0142e881e03100d0b60682010280b124802c240c082c6005e0784001c240f05a0401c000380c2901c2c4803002140c0030358040380324003140f83c00109544429100c140b600b048650801c400240207405070b042d0b00500040a21040f12400f500000060220489610144059a074040c2014201c810446000d800700b5074070f000250352135a00192166002440d00d44840741d002000303211030702e41406c0001c00ca00ba41041c070310b031f107520349810804020035001d01c403800e51400e0910750220740c4070325140c410401400308503400910000d103642c005030300c0508054001c0080303c2200c0d030784091401c51107801a016501e0301c008546200e10101d000340d54040184c4800342c0300e11601091000600112030306440390301042c40050000f80c4410010300c24800a07583c1c100c1c0c01281c0014055902c2c1c01030740006020350240395500c001426a40c000448140c04031052156590755003820030852040788401c99040c040c1e600c06814502c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 321588983 1250 321587733 321587741
    0x70312050903120306090c250b150316090c0908010c02010f110702100f170c040303030501060801081b010e0310051803071e061e140a06050612040c05060d 68
    0x101c02102120044649240741c034000d03110a407640c41d0002d07070204c0056a0964084005c121140b20084070740140c01c4007803254588070550070011100d6581f040180005844003c8902003c0e04089004d8400301c074500701c08440c512030911400c00c841c1d80300d801f001d03817090013010420b0041c09100c0091204040c042d400900910b4000c2183c00c0c1c1610300700c2c00003244d500f03070b0060b101000d50107000d461000f0b65803513007540c0e800c4010140c4020015040115811034030f084101341c9c05072503115650b40d00e0380c2c1540340150580f04142c1100381001203120040050410014408003000300c040703180d5144103a140012650340704280d25050b0103110300c584254180c251648080c1c030441318155803c0d0a05c040c3c0308807941f24412850301519a01d2440b2a032441c04110145801905110380000102c4070000906046910951688200056603034500c81010007820300d04035601048078042004494200300c006103090060621500b0600360703500000b001c1150850780103000d0070b030003800261030b8040c1400f4000a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 321590233 1250 321588983 321588997
    0x905100512070e01021006060c020d1401060803030a0c020a17030601050d0c1112130603020c0c0d051b040b13051b0c031309140c03040c180b100801080d0e0307031205 73
    0x46c8141e504009a04645100d0081a0341e0680e0743c1c0c0030b2842c0650200038801d401d00320143e41c02e40010742039140c0d00009101d01002480214041d58403450300303d0140c0102d138880300c07027a800e6421500d080c000040d0390b007580001d1140c28000c0940c0769240c81d03004a465000b08000c0310816031034407040b0000e4076007212801c0e900c80c022104407040c0c440344212010135030082400303601c2401280d21007401028029009825a1102a012103021003031140c0051001603100c841600c1981007101800c80300002c1c8403000e202c0c1c45040d6024800e8240c5500401d403400072428101c0c0e4010794460204c2d42030034040495030030700300c0c40e0311a90346c0390200c0c41c50513030301c95011030041c40e4120031001d8009400c039200d02a0b00202c1c0d1501c0c0ca0010141d07168081c1450304c0e40020400c85850030000000b03d007090352028650422031100307800049200c1988240490302c00b481400304140302028004124800c0000386103981d502e0f01e440c000040c2d02052022900c0c01000307070030082260222000911010ba4000b02038029 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 321591483 1250 321590233 321590237
    0x40c12050a0813170f071503110a050a1202090901031709030a080c0d1404090b030a082206021c0e031501031b060c0f080a050405040509010b04050c0a0905100512070e01 74
    0x5500310b19002195200ca1108020103140c001b55410405501548594044003002d800c010485864a00305000301e50301c209a1500401d40100702c49410340d030b103c5c4d84c0010002210104501e440300e90300025204403414407004200800b92000760a00403201001e455201c00c0140c201c0d9949209440c2c030301060740158020048a02c100c01d10505082c1c41400d2100003580303026001481c09040045010240c00e08080d400d4043c0316842444000a440740c00820781c1142d5180da4081401100a603052080800e41c0b00c0400c550248040f00c0c0c0e1400107800561103065681001c1105071464000300c0e0910705408000a10201d11000000c140300201030041207200b000d09d880403c00b5210441038512020a0b40301411070170400486000003400c9000600c513448442c00c0403800d15941e100001c1c01e407035040b038402c066a511104027540b036081c035014043e00710090400302c82c00c0c8082c044000b0944500d070b00c40d981c881e0f010940c545400034045d000712420b45081c0b40504007146045000513003600c000b40201d0780 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 321592733 1250 321591483 321591509
    0xe0709050a02090a0512031207022103070203160c09140412030c09030605100f0b0702121230041209060806280f140108010b03040c12050a0813 63
    0x908607030544211280c560006281000450030300c000c0c0303d9066500c1443d51180e21042220b0034902030140c019a1042040342c0c020300b2000004040544d1a080e41034049031000428010b10425580101c1992013220503800742c1c544444084c102000c2c6105180d00000c03800f80340c000c100e04460000c07508148968068110000301d0b030504007046048a90308402d140014202d41c2c5c0500000b0750b0b9410190708001c00d80340808500da01c038041000c01e45800d910840e0303024800141c000442c2030910704101074a9035030015141c28100082003a01910031019015100c0d20155400034003d5107144014980e1841c0c5112421b10b494603152031055101200042c402085040400040c0c881c4074488491050902400c7d41046010320314180d034410644400840d071800725081c000ca605140b103074082000380f0803036181081c0c628003000050700c5504103800c03212082c0c00400803c004208826610b0040313904c1e9242a15070300b20745007041e60428040700b80040020500261841441400007043c2c1c040e6102092444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 321593983 1250 321592733 321592741
    0x10315080d2705060f130e07030e060105010906030e01060801141e0c0f0a1e0203180a0f170a060603050102040501030506060a17070507051c0806033702040e070905 72
    0x2510b95582e001c05030341c4681c0054040c0458102500980440070b20502c081c0d04201c6585110101c02c0710f00e410502202010208000341e07168503015002940003414058016035050000082500c0154040e440906858682d1041302000035480103008041d400b00800030f10389546905240c00700d0a86031a6110707a40301d103508070100650308000e4003482d0350101c9a850912000c082c180b494200001000a100203880b8400140e400c2c0502103000d0061b0b075000d140d40d1818090b420380c0c804c000841072400340043d480c0a0014a1109082c0421768400760a00c03c400a4030080311450045100801030440c0e040c40f000200b00070054000e0029290f09032000c0c0410b558a0041c04103502600902500194548020b00711000f02e8256498009031240340a130f1800b01c850b2203051030000325010a4045621905003400c09641c003c3c0090782141d000c40c0980000740c40c4000740c0140c91810380e10040042c84400c2911100316503054503400301ca83c0a4000d00420700c0d111001c2d6150182d91050401650810b0006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 321595233 1250 321593983 321594017
    0x1203130801150f0e012919090f0e0a090620071a041527030c05060106020d050403030809031903140a05100e090a0f0f1a010605090f010315080d 63
    0x201c1501d44460420001d03131700c0c1014021b052043c80d501140f000c0c102c0c41400d6030310f00c0240010210215400c01c8800303041e007454030090101045a01c60b019039034101074244407419501c0c02c0c0c1d45d0459a05800801d00c078600b0300301200208074181302c007400c2d81038000761001c4500014010340708450145490280303640100c510340041c0401118020005544011115075044195201ca044802c01445c0b50252640d0a080c0d03541440c8805030507404601100c41213010002c08101031805403c052010301469144404090240c0c0140d020003414422084002102c0c0e002c00c00c180d0b0700c00e900f02e600850214015031000380c0101008100e011840030f0a200041026605010b5a4050843c2e030303442e81102032030211600c110031b81c01340c100b6040b40521720042011659500c2c401c072103203024080000343c50f080d51602007005444d804024883c4200f18004000040d0440d00b503400304213007590340c2400102c110004030300510030104030a0104040d214045880a00020f0400294010781c0700c21445c41590414 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 321596483 1250 321595233 321595259
    0x11070801110f1b060106121104030f23100e010e0a050c0105070c0509090d110d080a0c05130608180c0a05221803030f09030e120313080115 61
    0x7941c451000c040109958a4400310b00070b0804450454900c2c25030940f808116060040a902000028016a030b89800766074241c8100c80c0d01130503010b031491a140c070710381e1044c0c0001b48025014141440c190507804056404140f03070141ca00041090310810403000c0c2a0380000c20081002420940c0391150a01602c0400606186903d41080c02001083c5a000044416500110317003291a0512441c0014144c0c5400d100710703000d51403000c040c02c1c1b0700340c004400504010803120300c2e46140e8490500000380e16000700484c3e030030500c070712801714285c0c00300f030300540d060312030002e13031003101042402c0c00100e0641c00707400c640c0201c91101c25100703002081104290b83c1d10207050b07205d5000d501d8180c10049460010180c4071502c2030362000e99130100405c08003100311039061784d000e805544035620107810140c1c54401c0e0344080d151994100212041503c2c02040404040038090084c202100b4407218a0301c10401c0d5114aa01038404c01204c81d21021041e0181888400c48150080800c201140340e60074494 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 321597733 1250 321596483 321596501
    0xb040c05030d090308030a180602070b07081009020d110304050604050c2e090b0f1213050a020904020f04090c15020d050f090d020a12020906030d0f03021b060711070801 74
    0x3d10145801c0c10350711413074210b60002e80114800b9944e500c251503800d44022202164502a80c40140c584000f801c28680e030030b80c02000710040244d40402c0242011034a03c0c41019115444c100588070f5102d0341955000302403007520000300820100412040180000310326105034407610548450070f14000501104805950701e0014200c0032124082403200160000c4801e40b1492411000c09550b4207021041d41d40000044800300c507000404403550701607203090365044050340391080070124103078070740c2ca1b110f411200009128200c0310000c20195a180703800003030031490048c000c100c56034084c6801404102c403442130780c590240d580c60b207041c0b02c2d002059025448629413242843c00e00408410b54942c0d10041d1a594011812503d00d0003503194071800310058400c00a01080e0b44005004001406400508452080d030010f50800e00580e440525081d020619040158031542d6411a03001c802250b080d0031385140c41804100300c9183c0e441144000100c07507110907181c8a5488185072402e03520000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 321598983 1250 321597733 321597737
    0xa0b1b0606030327060301081b0306191a040608030a02010506060a020319090909032c10030c05040503060907060809010509060411180a05070318050c0d05030403050303040b040c05030d 81
    0xc018440e014180c9259a102e403513440c0e800500310f44000000481e240c000780c0154030194880f01c1c0c5211840708041000301040021001460107241c60319480c0440c0300324103900c0c52900d88900c007020915003011150800800010030510415440b65a4142e59800c40700d20b2200560904020070003504051049030f61020f01c1c0e03405507107445031480c8a00700f03601d00040d07650208000424000b503180e03c5c9120788020707148a580d0303203101c082500940c0e100780203004043c55028981c035880e800d569a0741c10569090040141004201c5070640c000070f41c0c1c180100e5100700e406015100401170440b801003840f005480c900d848940341c07030312840425400c03140100c4040c400c941c070040c080b4012a0300f184101d42200070081c4403041c02070351070070300d8400c815050b504003c0030741e1144103014400d6010b00071900542410121254160140c0d10707060740c0c2c0c15002c03031507500422203034085c1810b011003401210003540d001800c503a81da04044c41c0080d0781050459080c1c03944462041c001c2014940407a209030000752079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 321600233 1250 321598983 321598987
    0x1e030d170a0507020a06091b063603170712090b0a03050406020c16051201090c0b07021c030e01091703030f2a21060a1809020a0b1b06060303 62
    0x11081c45000340005400a0254800d40c007007080050440c1c010000341a01c288040020880021210b03e9180c3d120380000050107283c8501881d0040c0b0140e0005418902c0b0405402480c9501c140d5154482140c0001d4540889140c114211045075001481602e1040c4002451890f5090040b580c01c0390760b02641d50b500c0002c00000c240781d48650072480e0854002c8000500d000003016006140c090448045800380700c41c07030f00411042c0780c0001600441d00b00e4800034007107401d1558030020719030311a0156080d1110086410f10542d00c0d8504611100b50480080c41840083c5040142034004414961400141c0030903002c40c192041d943d6802d02086140021400d68079560800060340100418400300035008541c91020136240b4407071090603036030071034042d541e5401889030005125603007000c03249190075820601c1195201c90722141e0440e160780c0402866581e0017828040a40000314000c1c1d4400c80301d820201305541d0780d000801e001603c40e0070015440a901d030a154a0b03000071180c00d5403642003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 321601483 1250 321600233 321600241
    0x7030c0c060e031e07091a0103050c03060d0b090c060708040e07090e040f0611030a090302010b0415210c1403010f090c2c090f060f130807111e030d17 66
    0x40c01c410342c0011102e01c1501c56140e2160036406c00c0f504454586082900400040851941c1600c1019004915800441d1452400300045480586900c00040801280200080c06090213102c90102c8001c010012603550b9a14144540c294125001c2c0320107a60400700451190340c0502c10b1081102c1403000d0003880ca958640b600003541803e03039001c0d54142d4032891202146414103000318070035413546200013042450317810001e0868030840f1130140114501458900c440c081d8008100880e030520120a03e408418850203624002074600240041c4c007184021892125184960010a4050b070081003003640b4400031006458243d400508a508a40c0341070242c82e88085d0480341c40c0e583d852840184240001141c4440d281c03c80361501c85801102242140e044148005604107081c06607012041c10201030b045000c0400d544000c15144000a00b00108107010300c00c2d545504005110940848001400d9004100b886000c1c5e84a4010820300c004035500800940304a076038100030424260f80c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 321602733 1250 321601483 321601513
    0x20a050f0d2c12070f060c050a0f0203030d0626030720040915090311120405040f09050d0c0b0c040e0a11090a0320010504080d0c03090b07030c0c060e03 67
    0x10800c14510500000a08003152a110142c3d24808600ea000c0288503480c6440940118070400d600820100720303400c0b0862000c40da0001c2c5490b045c0750002c1001c0c429030b1140c40080d103940310b4600200d40d00d07410650f001494034039104000318502100c2a091600110307424003140c41f40f041c3c040c000c094240035a5880002500d001c0310006800010b04001a1504a501c1d040c1c2c0000c54074650441c0c20f601c03540c01400b0582c1c8811071451100d441401480b140c3c800c00e4022119000740d00071180210f981d20910f0302c00c000c858003e26441c9030008140c5a02d8800c502000b4804110420142c44402240d004140200c15a4044030100c40c000d12034101c883c0c039110b408034090f280c1141c40131900102800062a03503517900c0c20100007103205040030058031181d84021100c01405d040c055051080500081098080205034511160b44c0c0e841c00039138800481c40c081d10018034030740002030320340c0022514204054002041903440e50090b4903c403880d0b035883c44219000c000c628112070f01a008141a003c0c218 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 321603983 1250 321602733 321602777
    0x20c0c010c02090f060f040608010203160201020f030103030503070c06050c030708070e0f0919060b040f1202060909090109051c031b0e012d030c0e2409040912020a050f0d 75
    0x6100800702484076040d440010223541c280d4011890596001051001505080d00c9402884545000941c10711a243c1c0365828240014400902400000400180310320b110703040c048502c1c0e41c0003804009505200f0f03050100b94000b103d100f000704000201041c400c60081c013240101a00003030007100703565031440070b00880100185c203005007964040300c9042c03032445c14007555000e40045104c4d25115403401c0d0440210b04c403d03510401c010551030840202507103400080b83c1201000741d608141e1a294070214500405c1d5030000a41140170f6894942c803489145040208403000550302480242440b400d4003045a01c4011038a000c20403246450103103500490491070712000c2c207640107440d035848500d04422500170702c00c0d6200181e40d8a649145040c2c000715501418102561132500c40500405205000d40301400c40e65580400030030b18500030350b40c0b500415007035680400c2c0340c640b034480510301941e602018041101c050003420044030090000061101205030196220034044210705130114490b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 321605233 1250 321603983 321603991
    0xe0c07080418051f09020d0b060a11100c02071a13090203150307180c090e010e0103030314090601092f03042d03032a0807020601060c031d01020a15020c0c010c02090f 73
    0x40c0c44072088d20302a50b034100a810700300b420740c0710030040140c01c0c42c1c5141041040108040c03058074141c164a80164006900c500382c43c03000710030b0359028aa07048030350304900804050302d442c1c171154100440d0003c07a0340c0295000301840319400072075240000405896175224009e40d10f1880300c400300344040d0302e6290400794144100d41412014591190303140701500700c098003d51040c0141400410402d40e0500c264210065544010038035414003614490b01c0d0391040c80b55004440c2c85049600105503e00696008903038815004011481a900045400d400484042c0d810b844002c20112a06d40c1d50100000451001d441041e01c0c0c4001c3c5c2e81c1500288090422000a42c0c0c14040e100c3c03035a1542c1c0c010f0300c030314005030b1600c0c1c5480c60854402071420b081604450100401240f0b2a0300098101c0d0104250313000e5070440c000184a1240102e1802140450103842d40c3c2c5008007100100f0199401001462440350541d00b04030b481c20300541c1c80c105203810094001404500150222600071030050b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 321606483 1250 321605233 321605257
    0x301050106093c06080915010501021518011406040b01020102160f0f14060f06120a03031112190f0c05190306050603090c0a140a0e0c07080418051f0902 67
    0x5290780240340c0c50781040844d04000e010494031000c0c05a00041006249580344d00940100515810240000d44565035040c40c1c509000d41c40c0d0208040c0358040d170a00800c884124020040030761041c3c60120400d6081d6283c5005514110781e000c2d080d441030080311111103807403076851443c000c5a51450021000400140c3e01030300e0080b81c280000c0c8000100c41308002444000f05000e06025941d2062100041c085910070060140400f000b0100400e000039619014180098040d404031344081d17080c8503015031025504094410050906038a0442003c1414800f00400819074801794000c00c854892030010049642800b00c442d421424181840080c061840d010402036958404240e80381c0054503070800030b0700402c2400d0001d0605220420050030962100b04500a03084042115442d140c055803910003500e40000b100824000c080300c03442036002c40d41035075856880e1504005880480e5480080a041c400482c00c403440030050f518003403c07d10141d1000e030740703002c03200e000a45c418103108074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 321607733 1250 321606483 321606569
    0x20f0901081e040303060611010e0c01110304170706020d0905010e1203120f16080408070605100305030301030c1805060a0b130902040e330108041718030105010609 72
    0xc0c0b2450039161601039480707502c0220300342d4280f03640545100380b1041d00d83c900760301d0304480c071184d2000010151503180d001c0c2090100203164a40f06030561155400042600c01c8102d040700c00701c01d00040701e1003211429402d40701d01ca4407460088441180764881d4900091030301c4849800c62501e810701000c44401c10080b645408402803102d40b044c2c800b00c40001c42d00701302c03100b00411040c007036201080c040c1039403a0030000c6280540d10b0080740d004003d005403485a540d4001000400401d0b40300300030f076400c00d007140c1c0c4940e503030315041d00000b00d00d0207251400c202d215462070542c2d02c24003d407402078400911400895041104100150300b1030342980e611003081b00300010703a0080e244001c00c0030384022440a40b4600c1d004e081c1001c410300740c17642c0810b2140c1140500d1590800c043c40245c2d80242442d201c1c1c90391f1110b090106424201100d43c8208150020305081030034002d203952410301c032047e4024800c60b0f0382c415080e181f4403060300c90200244109010141c841420782e40b0740001c1980340c02d075a2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 321608983 1250 321607733 321607771
    0x60112021017131103120315030703020a0e060315060627190305070506090a0e0a060518060109060503010f060509041503050604051b060f090d02031c1101020f090108 73
    0x10780b2121050750358520325000800804103210012403d000041c100303038014050b110312040840c42da8840201803250b41d05082c0c0300800e00d907400344408401103030000d0a00c4034550b118403400d107494109407060340c8070384203402c00d056180d480d520a40348034080041600307050a0701c1d41c84800d014a0304000040030101009140c680e66555200b54204602403d03001041582c25494403920740101600664410b00c024401444140c0c1c0d007403007020994045080041d00c90b15001d0940000c2e0501340c000702d90080307000c0340c01c01141d580c45071038a00c50b0078242c0c0c0c0c1d585030720b94078401034465110030300449900071440d0308103105c0030340510000c0090040c064000506545502c1041a1098150b00300320bd0750341000c000c0c401801010010035039540100d01a04010b034103200c0003c1c1c904d10804030001c40051004c950b241e00b03175440d1022406915005803da034040644503044845611815480d0341c0440e03055041807100c603005200786d03454254603451161402460701d005690391600241000071702131211001c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 321610233 1250 321608983 321609017
    0x61b0d06050406060e0909071410030b090a1a0a03110103020c0a08070f120203090f011101141501031404080d1d0102040602070e011220120f0f010e0601120210 70
    0x45005102e181c1d61040440e41170ba003000304040c009400702113140d004403024007032aa14800d0042c500d14003140c40b500d950703000c0581a40035282074440e59601030700a800f00448100c058000110700010942480180c03940001005082502e41c0005401c45558080b180c035154041d900900760300a041c005c03281100d405640e100790551048404941000794030041000b0050746200c0306140c040e4500140d810006804007240d4803850360b1010301c0c108100c1021302d0940043c29884001502d800d40160a000d00d400550660755141c8006003a00103864024074405441c220142c15010381c0c0d100180c2e500d003802c030986d202c8c041e00b042c03024000703209001c070500541440300744010001000c058024018041c54480503181e4140140d014010f0108961456000070701c0d0f858100510502927003c0e001540210400b2031811142c0301c90a1030b8501c51000302c0315aa40700010f82488024030180240f2407669417403001a241e450078480d04501402c0e0175091401840c210300402460085403400700c0b0050303448008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 321611483 1250 321610233 321610241
    0xa03120b0d0206040314150408091e0d0c060f050906030117032502010e18071110021b07050d0807110402070f03081f0605040b16050303040302150108061b0d060504 72
    0x211208015250b411b800b07442d0a1040c0194020106ca030752000c1c2c40c282d15024040d20904807210311500c0ca003001001d002000c2029540340c40000342c02820031040601e0807114080c554083c18001c0b4500c11841050b06101e40102d80d00040c016020505503441c00010000d0290005071662590000744111484441040d9940c043c1032520a02e0402c442d1640c00050030140151104501410f002c502180040c031044001079040f00c418074119141d404100307003003820142c0b500484064140000f40c41d51820740e220007580740e5003181c501900c1c0010343c2d44081200880031600d0080c0000c90601c82c000110300341c140c00fa580003c01800140c64507a090b03848006140780c420044010412200c1801694000b071140d00c05074080c0c4803185070105050500181a40c051445400707880c101c0000e440c0150130010b080e1282c1c080d4408100c80d10b07030816280280d11855903c40100b12018588000111110009001405500030950200d001c5501c034442001c030b40e03c0003440a2030340d515039000040c0c1d41c581f446 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 321612733 1250 321611483 321611489
    0x403170d0c050310091107020f1206070c15050907030b0a020403080d09050105150604120309030204050c0910020c0f0d020117090c0316050f06031f0807170a03120b0d020604 76
    0x940c940d50f91801c83e00c4840f641d20560001070880d031500c204162000e0310340c001c956480d0b030121100301e0106161000984c40c5502012203c020740030724003c1c0040c46401c043e0300c000c42845111090309460746048030600f1900201c48204490b48101070030008282d1100210b034000b00703410005031500c1e440342c8032814a540403010700c12415940b40c0001051140038400d0300d4200300802103c01c07261981100182d0075010b507005c1e045107180003241e08001c1500800050b0002e550190042c0183c4c508852445059008421283c0c080c040c9485110304251000c01d0742c00d2180d000030180c0003500c18060920224025480049062000d1000e10420510603140d039a44606280c800818604540406141c2005072407a5902800e8040c0b070410f00484d62500e20042004a007901e03240c2d241e681e824802804000640007a0941068880c80407440110101d209015a41480b1040488144040701941d48012003600680001c00b0540c07446840c256540020f040c000780140a01c030302c00d4071343d000980c00d9400f0354 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 321613983 1250 321612733 321612737
    0x4110f0c030c0f0319050307091509030f0b0a150605031501090506130f05010e1f0315060206010e06090f0f04080c0f1f06060c08070201030609060611010e01020c030403170d0c 77
    0x20684408000080321120f440304c1c45e80c5400c504504015401515210181c0540c880d4000d03000d103c1c06035184241c401c20700039a040709012528130301c00d04090b41c00203019900030103100d040500040e401408a002d60080f00c0c0c1d41d580d458555034070340e001c0c2e41ca0780d00c401c0303045810448150800291680c0b068050080c084201c40c0c08a04a450300c009105888001c1d403003107061000700c407030040e1941d854080b414404407020501c59001c514000d406c03401061070b1a0300d510075101c110300118910f81c0c0021034030306848988420903515103c441c01c12882e5841111080340c032410443c0014003a0b00364117880c680040c07250032268100038825040905045010f81001000c0d80302c002401d00e24202e48964842e11881d03420100f0080741002e0004120341004040072740400d800190351800c42e44240c1c000001000c45440c20090346445100c0140303115003500d4000590340c01d1022500d840310040c802c603202c0b01c0c1e511008600d001d1955036100002480302d001c080780d080e824062079522586a00581c80c40704401c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 321615233 1250 321613983 321613987
    0x2d0b0106050d0b19051315030807142d0705120f100c020d05160b0106050d150f060e0111100209030d09030f020f04020903150a0b04110f0c030c0f03 65
    0x1603501d00498100314034203441450003402480100c1e01c1c01d107512050342e400765410003905000e206c20380c0c080c00e03a2070911403000d6901c42001051080440c0904542ca00c1400d00c030640c080010184c60396510403c02e403007000001030004404d003040000c1c82d0781c819055541601e020a079106e000130300200310004180080e801c0440c80d0908010184100d2420b00d00d0002c5c100302107440004d00070b6880154482a40c10f1050004004c0c0304072102d80b14a80321940e1040710b80f00d1039a12500000e005400c03c03030b000e10001c0c0c241110004941c003001c3e0131070191000b00040c001460f1500310300f01c6100d613441e5402c0d03050102003003d000c0203a60601146907508441c51005d65180325030b00505241c040305110353b1040003402041440000d00341d003c00d201b007a03012101c0c1c822079942d450000b8000d1181007182541842901490a494400d80d074180384a401c22180810a81040b5400e2000f5112032070039111230341808106030b00d4400400000350008002c03100440782001c041c01d110916207008008a8126a400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 321616483 1250 321615233 321615247
    0x41b0201021803030f07060b120f010b0112090b0f0a0f050a0b0102061e0f060103020909090c0915010e0d030215040309050901061407060b060d020406200303042d0b010605 75
    0xc282d44038041600190b006600e09a04d400000d059805000402005540c880003a01c800b42c0d01c260403c41265086403d4442c04805110352500030301091021501141c40c0d076102803081a014898404416040a8034580c90b136544038802c026000000c0102c5c517079681c3c42050f5040c1001600c03d040c85015402000902c88c09681d00181c50204001d041300395014160303a00441c4802c60031812508842c00c203103060760644583c2c0068000c3d0164900340d5030054200c0c01000b411060004031418014002c2d5480340d85038444200300a580b00e8040805d6002c5107900b22003441c141001c524260541d1b0003403042d2100d08fc021041405040c0054500b40c3c00206100c0081c00146000011240104041d05150341c8540300c540303e00401c0e00440344081d010740d540d146035010a4407108115510074080319800c5544079250b0b00050700515850000034019240d01000d40c0b030003030001048a001e95000054004a140c120484c02001c16007001c6400c0c01c484130034424000101e802041070f0180c05607407a040d4407890 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 321617733 1250 321616483 321616507
    0x3021308010510150f0e031c1e0e030c0d0c0b040b0a081302010e190801061719020102070509090c030a080d15030b1303050405030a0602040e160504090209041b020102 73
    0x10b51390032024881e5404441c45501c1500400481c0b03c003480c0c2c1c01c0c00c859401d4481d000905203240f550024a001d82503661143c00c196011959000c1c1c6a5003060440000000c1d0708101c4403c0000d024040d01a4080110344119103800503000f070031144141e00b01d00c1e003e0380380d0f0b01d40303103183e000350b80a100440004221020b29a4024400d568000e0fa036040c510000010350300002c1a1103403180a1b0b5000354105241d11641e10b180d807000d0405030024130007e02502e0b503541000c01200103004184501030081c2c440c4518cc031800081c0e43e411039a0140d004101c214145070820401c001d0150004199100b010b1079182c0c05e072404c2c03050024407400394240c140c88503194031000c0300b61489020034030030000100c1014000110003811701500440d0400c0e2500c200007070340c942514284120341060f036051080004020400589030000c2056552481105240e500d80303904100300d1803010350408020490500c4103002c010b245a01500c0402e000600c003040f4513035216850f01081d4080024180142d400181a0b80440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 321618983 1250 321617733 321617761
    0x3030f070203120c060105010e040b090906010602100504080318030412060203040b16080c1b011a1008090d0e061603230a0c150e0304060206070e0904050a02010c03030213080105 78
    0x15003030200741d484c04a140c0c40940e00d54105002d8523040c04541401a5240d445030341c01074400e040080c04032080c81c18400749840d502d40d424422440140304075012000c50401034000c0c039003d035920140d180e0840d11440082501ea40907003003840c501d40b01c148000076400007002d00c0340d070402e0b000d1000103a50b401d203805c101005a0001380001102000e00351031404042e480425158017408941c4542c0c0c4500e50b144034465201c5440300c8410700b540c00c10134403090301d04111000740492402100c0c03042c07040e005604180e6080c8400c031f41040f400d410080c0310794005030144005001e4210002d0100f4075206010501900301e040c3c9080985c002805400c8805619040200f4104501e0b084c900c000d00344440303550020b00e117908002006109000395002c600c051440342d0000c1d4100081031040e00d4880361601002551110221000b000190010a001409080500c059070007560000082c00344082160019144045110411410580c0c204148601e0a80d42c00c10000030303080b00e200200f01400d040015130070138 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 321620233 1250 321618983 321619003
    0xe090c0a090902070506160e0a090e060610090e060d061e0606020105100303030905120a18050913030507170316080604020909040f0302011b030222050102070612020903030f070203 79
    0x2c1441001840041440010f403540c1c07201c0c011061241c41d4140d40300480e4003207211780c20690000305500700483d0803001c58101c0e420141d07401c412540c180e6200010085d0402a03101c100001c03e02c020702c203115556100e044660b1041000e020003200350816500e14003140c2003464107921011805d9030b000544903c03401044000c0000744021b010301e00f000c0f03505c410400603601c0004c00f1b15694603119000c0100901114021428504446444000c03901010740b620468250092044200c0d44021980c3e25100040c180a4984000d10103030b1440c81e6a07081e43c469000d89003d0312030984600d500580b8100314401984a801c4e8030428000300700200102420041010b41064400d0b8014060180e40d500c0b011581035010703402c400004021a000e0405a00500326501540c641441c154091038103560560024006104d08a40401c8607018103014040304002c0d601406005030802e0302d0800000c0d102e0301408050064580b0014075120081340000d185a100c1d100d140c40a4002241d14000d41c5400e020000c07007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 321621483 1250 321620233 321620249
    0xe2e050310060308090d030c0605151c030e040209030f0708160602010614010f0c08030c120105010309053007060e010b060711010302250c0f0501051204120e090c0a09 73
    0x400b0b030640d59030840758003402000d03a0184c1c649204a500781803103110070407901500210b04019a082403401c8081c81102c9202041c0560803420402e20100040d0780c080300c6854069444203c070b1039070281000b02a6000c0d03128560715105145d030300861103600b0700c4604018240c001c001c01c00240c009100700d92981c2c0d144e21030000d43e450901c0401c40d881c010050340403415400d103403190202e40350403010381d0080e110140c06880000c002c410890340a0345074009010070b40c0c41c110103504980c0d8480c01101503d0402d000102145c00c4480b403504107003c100d0403a0b00010951101801101660a0300003842d046204151540760301c80c40c4021003608284180314581d80309440182c54090f0b641c9480d4540160145c46034105580020420300182d50800c412007407100744a01404000c50b281000e000c0d002060040450071000e180740040d4640c0a5802c0b59800e0f180e0a46010b41c5680f15210380640440600e11201448001c9050503945e5030f0f040c04003131088114289403500d44005080c000d240307461f02e42184075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 321622733 1250 321621483 321621491
    0x604143102031b030102120f071b03020a110f041103040c08060103030903030f020715031d06100b0c1014010611030306010c06020c01060b0a0f020c06040f0e2e050310 73
    0x1001d61000701d20160328205043da00482d10f914440400d00a108140711400100064024420079041c14030340180580e07259624111244640300703180c0e03a0040030703280c01400350380b00d84605c0c00050002c16914030100e000404070402c01c5681800306007aa801119001a1107d00204103c01c00107001301d00800342958038002d100341e40c195940504100c9940c0006000d110b04052215556482009224080e080c00000216606d0000001401815803015034014130301000040d00d8405070300107400d0384500e40d060301d20300e060351030140c0d11802e96001110321a41d80c021840022038400c170500507079040780180d003605485585000e100500d1007100e40e480c40700c5604100148801a0792140c01c036403040d1b40001005a0310280340c2403481c01010070350310045001380c0101d014401250416400c0d403080c8807030b4007500d41c0e6442c0341080019521481c021208041c030392850070b112016083c040d0f507900003c000c0810200507200d1500c44404a0040340c000d111010518080c07005003000e00c8254045610040c2c244 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 321623983 1250 321622733 321622831
    0x80a0302061305070f0308070b070f050306040213050306010611060106020607080f06040b0904030207090b0402070c031212050a09030e01170a111605060105032a0603060414 76
    0x25111076002d0702c0c1065000d0624505030038401c040c854000204605059001416501c1c9055142900580c00988071444c9402c001510a4062a03906010182582c1c80502c0c565078401008025045007421145024284401140341c0d2410092140a002c0e16128500d211108000727440c0380c0350301600b160085410075000e1040386500485c0551308520100300c034008555407000410b0041200360501d9610a11503001e00013415000710388001502c0380e4201c14007000502c03806102c180d01c90f1035001420501c42c88010004120a2140c480d05480399140241c07000f096264884240d40c42507a180131038075501d440c0d000415030040a02c080c89442802e24180e21422050807031112200145100d0906032203501c0c90090600c0801103a1907503038a02080d48402c1860f0808a40d984424083d0b01c5c080d110340401229040d80444801c44c000d000e007500018030340011030500c041078101600c0c0b5900a074581c51008403c02c0b601d40b08521605106210342d02e0071171046040e00782282c100b5200104040021801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 321625233 1250 321623983 321623987
    0xc120a0c060209040905010f0b0111012705010209030a11040b040606120c02070b0a030e0105180a080c07090c02010c0e060c0a06180609050a12020610060c030905150d06080a03 77
    0x800c40d190003600068441c802c10001c200a0407403020003c006520b000c00e041462169070f80080740c0c0d64002c0e42d80710010b0185000040c00c9500042c2ca80d24070071842855038040c2c04511419101e280d101e040054100100c0b10042441c00c3c0340c0b0281240c030500c0e20a6012392a080038851203054402c100d505002880c600007025000710300195070708515503121407481e00c0060082099000810200c16400d60f502e1050030014014059011504115400c1c840400d5040c07148101f20490b800c0312030f02905803c119541c49080560200d040841c031401800400181c8400511400c1d116520540002c0341700b442c44100140f43c00315148055100341320a0001c6904c1030300000e41c00050031703030000d000034443c005510361010341000400f004088074204110346081020200c2e00c6541280300e40e5140741d448001c0710f0141e0f2100c8003110120501020f071501040302610030401c03041001d0090802d10840c0391100040740d01c040c1070440c606078100000505640381045880340d00000c08032640a040b40030415540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 321626483 1250 321625233 321625247
    0xc030c08101a010c02010306080304090f05060f01140c070f030605010e1303020c0d060b151314010807080619060206060f030304143a0b0a0504050a0305030a06030b0c0c120a 76
    0x2c2c95040004c4ca59800046901a5020708044e0400c2c1c82100d85a0740c1c0c90543c1c00142110b1a001c1a0003810310001c25103d0522070307030400b10220140c42e1841030003192101d10081e604501e030306074440c0c81030000009882c4403000320400514003500c7d0120f0550304250b507009820700e000e00006247c81c002800000400d41c0030039950503000040700c6401036141d079818907002034078010002d15031040395240080d0b4450000801084540030800b0f40b08032560355110785001c0c00d562680c40710701003040c460010b18424462080d081e4840802030041c00700c1319540f94103494103009070b0000c1015078840c2d01031000a182000303521904000440c001c0d407615083c00402e582e0050001c90703190142c403681d8900c49115215040103014508050f400400b03020900a00d220707042c11846094030720402c40d0010480c114814080c0b544215080360042424030502d6804485650004060300c00319940e64401200240780da5440318007415124042e41c3d16480030301035240c10442042d48102d80700030108a1503d440e80c202c05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 321627733 1250 321626483 321626531
    0xe07261018060503190506010510140714030d0b1c05100c051b0610050117071409060d0b18090d050306060f0d0903080a0b010c080c01090c030c0810 65
    0x4040c103090325070180a40c000e00010782186515005828003010202080f50340488014000c0b07046510503640d0f0000d02c1701403004143e410000981400f0a00204001ca400030700520b403085164a110803115100d150842d0008030f032885c1050b84450410307605240c0f000c16000c00400410501e10006899030300c05554800907440d2a030300f80d8990b44280710581c021010f41d05240450680c2c007016200600c03405803138450490708099030a400c1d40380030440e94402c1400200e035040036940718041d6201d00307074250f0b049540300c4040540460100b0907030201b0f4a811000d05206003400c0c1001c01d810030300d0300030042d0200d1582d14900d02c0240a00c00c0000c030140016503486514840d040040d07403902d800001c00c2003882800c64100405074001424180c08115602c070490312070107030307940f44190348401002a0907154503840f41030009203a2002c00010400c1c08004202c2d8a0340c18000240c450800e40c0e444c1102505944242c95221400340e0402c0465400d02540e044d1540508c410486c4081c845184408012445 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 321628983 1250 321627733 321627749
    0x607110a06051506071b060201021c05060a030c0b09011205040809010f1202040609090c030b0906040c1b080405120105013005010501080f070902120c030606040e072610 74
    0x2004030700070700c1001d80100c0480380044c20a030342e290a01e0411003500c0d12401505100c0d80c0501c5800101d0724418400e480b121070b032007582c2c6078410700303050f142d900646005403004e47d01140805c4004002a014039040c0001d2106100346074032405a10300150000035080501c803900340c01c020800000807642c4c01200c8015909080214001001d640116038110b5000180020390b480000c0c0440c1031504804038000300c0380484024000b03407880e4142202a141c1c0c8010b10f9030802c0c2c0140105a080c58190401d51142d503042c50080107207030355404c1c00c403004986078001b81c81c41c8038001400e2144d41001111f00070342e904158002d010702e516254010040c858442d211030ba006038060407081c5041500d0791303150a07558000c4004c1c0442e507100d1035510303110313030081f0000c06180c0325005000403104d0482c001d60303c100952024040c0e01d555000e400349010340c0024407143d8018003c020102c0c000c510b030005240603010750769a44040858550104c4020b0303205e48a60510110450100088a014140f401342034031171503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 321630233 1250 321628983 321628991
    0xc0102010b0d140703050f010f05060f1503070522090b060f07021e03010c03561008010306111204060b040f060303080619211b060e030607110a06 64
    0x20050b184c3c241039017500014117070300944080302c5c2c40c103005410404400840c3c40c0b0402071612100100712a40c40e0215040e170304a42899210310113642c00c40051607010845062403460200c040c80016208010781c2d2254641d100c044c5802d1020242c1d030b100e00e85503480151801840d142e540f200c000705602480c18000d1007000003402443c5e40b04058040300c000054064024440c107803175000003070f01809000410220684500050040d5516015446510584200005080300310f01c4140e92440070325181034485508019000704d1070b01d072a81d90702083d840009543e00071081d410740c50040f0a4680d0032003955003400041c0000024030201505081d04164009400035440c031074007000c20054540584031108807850301c0300000505402aa0702071150008a03411070741d8000c0018003c20315140c89c010602440301c001010340101c200d0008111490b406081140070703201d10807015400400c03040d004a00051141c4545d003856042c100000e50b00300042e4101314141010241069035540600080505040d40f9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 321631483 1250 321630233 321630263
    0x3070b0d0212182808030114012d080c09060423010201021903020703090315020d140f37060612050c1c0603320601120201050a020f010f0e0c0102010b0d 67
    0xc2840d00350348003179009502d0f035102c2d82c1d03ca182d121251050060240845c0c00c0900c180000015103241c440e601a0010030400d510104200446003c4401010307078600f2a8200100e407090703a60b18003c0c000900d071041040001030b000f2540d22028000c101c9809042d60b0050101c40010460050303400c9c00a04985001030303d502c401d04080781c640403a0b52001d403002505503070691840040790000c0010703040480e000d10407400c118031014500c503400c580340c0002140c01000300c0ca80042c01e07e01c900c090490f10406200030a90b400081105405181a403600240e4400c400c1005070340020149480b0318000c0d10400a074a03001e0340f030340100d2007180c21031900345039180400750500f4002e901103006160002404903a00345241c0f08079180b10203642e6040c201c1208524101c2000c20000740c010b050711440d40c408202c00d035050b4015100d5030020b07002c03802940103402c103802d4103180034428091803050018011484260030301d03a290410001c240c1050469050010c000340310b48908601c8488264007049070529195 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 321632733 1250 321631483 321631543
    0x1507020601150216080f0114040c030f1a090c01090506210c0d02030109050711060103110607080d0504050705040c090b090f030a0213150b03060f0f03070b0d021218 72
    0x30140a48400f44000070740210317043d280080c01c8446207000c1c80c020040008a140baa07907083d1000c03500104103000125007071001441110008015034443e18501000c0f51103420318481c8040111400e240c00d9224000203071107503920050100003031009a40c010706d080d080401c20090381040903c0a40c125070740c103000c03814007004e950880300503c2151008540b00c1d42c662000b40050101034070050002020300114a11014020070001d049a8cc0900ba490380d04005a042c03214581000790256040300050218400c0306116014140c812403049002d49152130801d07081004498030f0801d420f0400889010030300c0040809401c44404800480d6081200e500d901c0c0000e1500c4100f41c40290801c00414540c01280b805170012008208070420340880580c850106803000e003c2100d1042c0d00c0a00f00c0006905402e24180c40e120100e070260079541c020b900e4905400490b4000900100441d6000510f42100c14040304410342104e4598561220301e02e40381c8215582d1107d201c0e480c803030f001503c100f10400c51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 321633983 1250 321632733 321632743
    0x702060d15081e06161d04020f04141002061e0a0e1504061a010c0201080604060f1205010501150801180b03160e0603150109020d0209030115060215070206011502 71
    0x1014000885084071401440765404401a25890003c2d100b50000b1403401040c201c3c440c4240d600d01c2e40d504070084140307000085480c50481103550050781c00c00000c8405424000140040c28a02c2c91423607404062030b080c05414100c4d894041c04542040082c4841e550b000c1c4600401c95425905c0320780140c40d2040801d00034240e1044070300881c85141f4140b80366001c000320b0a07214500807401081041440c00304100c01d034510140982c0094001c1030944019806038014980100c1d000c4c2c400108152a410a0089045141c01c1154072021103500201005000d020b8a03014102c403200407850148909000b40c550700d01809030740148062080d240d20b5900381503202105910000f81140c601203541e8a54403405192070140340c00203d50308001a54509000038134954018200032034401c0340e071034521000c00a4100da4681100560204105030b40d0356002d00500e00301c021920070800c112460240040d1400c601c807420403e07810605000c024250340c01049441c1142e84080340e800150f108010220304107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 321635233 1250 321633983 321633989
    0x31f0b18011209230f061518040b060402180d0b011806031104021b010c053c0d0915060905090a11010c0303061806030b011a07062309060603060c0702060d15 69
    0xe44520380c07c100182c0c21484403030540d18402d546a08200102041080c180c0d40d080314040c084400200110b00c540c00c00768003c1c01c4840c00e45403005240001c460004412600c45901509c0841300e100041c4210800070255a41c050f00d610000c00c2640e02d59955028110030318580d09105540c003141c10080b00703011f1045000d0448030400200400b80c02d0b0300001d0f10f00c0d084140b024248109032400d06062002081c143c551201c00d50900902840800f410b0103003e40c0301c02146000661038030b60040000f441200c2c04200c1010b21107012804a00b03050700d450444e000208070315030f5a40940b00d10408070b401105002c2c500b070000c0c038060708491890b081c184c1c05001c1c2c0c0e5001c030900308560103542410388284e82c400401d980c0704450104403a641c43d00311401e5603241c40400d0300042420010b000010b030481e80005440c1807488200035540c0064050740c90046011a0003c0d040e802860030050b0902d000e003d11644181c1c08e08409080c4040754020800034002e60086600041c1d44824148120004001207401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 321636483 1250 321635233 321635263
    0x140f04060518091203130b1f09050a0e0d0503011e030c030605040c05120d03020318070303180501020105040c050906040902100e0901050f0303031f0b1801120923 71
    0x30b00d80e5004120b4035400c125840b16060050f03540c25003203070b00414112400b49011450382d500341c141d01d4031104819100600860540d1698650b5102420f85002d60760b4000c04410400240d94904401d1902c00d44404514a0b407080e04064982d0605a4211094a042d01c40c0da00c413441211010f18100403c04803d0f80010780601022440001002101c2d002148200e2280b4401d40c901c42c9c0d10020310454801d091180301960b000f1804041a0758860f502640d1b201040302040758410840c0c104080c1403202d640c205500283c001c11181480c24a19200040180401c0c03008020038500750b11146204119030050130310507603207000414100e50b01c46d049090210b800901400f24110030140c05131204032003046a5000362540000062245050f41403440c1107a800f070003651540d80c0f05100a80072140c940341c4800c07084603004010802815002c0503002c41403503400311707201044c05107001506002507060110911800c007007400000a030100003100d403285000d0030122000004042c0c40c1c1c100070000c020398078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 321637733 1250 321636483 321636499
    0x31f09020f0403330c020109060c090f060906090b0c1518010b04020f0f130b070b0a0f050709030308150913020103240e0601050f0c0607020105010f140f040605 70
    0x1401007503000042080b80d12035100483c610404060020745206216403032800310210030705111a00a45802143c3c10460074400002d18581c0d0360b4501c0304903031110707032034800140c100603050041c005031081c1003000e402941403609120b8540340f00148042c005026681c403000f00807a07454140f1600700700c074401c01d2403030034841103992911032500401c0c1e0b100c070517201b035044d824041b4107241400c191003200c1b04044602d02582ca0903841c0340d29941503520026520140c81c281d4940003a1108170f590203400128403a0007184103e0818003d40c0091750724200070910180d282100744084182c000c640001240d41c54105008182c0e2445412841803034010a86501300e11b4580c100300d6a440d441d90303a000c581e80300362020441c90700414103203400d681c0c07800da1800348141d1403c01072003101d52903c4d40317075400308052501034070300951071045899030f130001220001d0580c0104240007407103030280116405000e4070340c408500c00d442c00700c40d6600c07140d0201c0701c58050a2243c0050000f0707241ea400c00c02c0600b801a003140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 321638983 1250 321637733 321637747
    0x30912020c041a060306090907170102030f07210f110403060b03070f1d0a02070210020309040c0503190b0d05011e0b0a050a0b0904141003110a03030203031f0902 71
    0x3948400041034001c0c411450300940e0400502c09200c440100107018100d1402e583d50a41070003040c00c0090a034080e103110303841000401010f80501801c54204050000d610f90030140c001c000303130410240c405420310112084404007045002480302940c496a14003055105907602c142000b0080f00c3d013180880d601c001804000e01c0740381c0e00b00d414011019003c40303040039507032003404a680b0340310b01a804035004801c001c180501300082c003184d000107040c4c170014904426680060007402d040c01d541c8016800101d6020b09a2600784204000d690850404519600c0c12940004080d414202108005a07450540010340c4d00d03150184603415601c60000c104400e81001229044502c04d84002d00243c00c02c0b4170100b4504240003072004640c80540668485814032030203000642114411a822540d00e811a52000000c0c124180c0110800d154180280d419810901c10022101c81c030a4003a505540d8104000b075800003c89034850405601d18004607400070364000d079001c0ea80d12075407506001003402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 321640233 1250 321638983 321638987
    0xf0a0b0f030115080f0304060504120804180501030209060a0b0a050a020a0c061e1805040e010b0d06060807140603010e1b0403060b0906010f120b13021602090f0f01060f030912 77
    0x2107000e8800c4441129030f17900350406015070380d100b24010000003c80500003000b0303000103612040c084611440794141050785490b0400d255242031015114030300d842d40010030030360a14080c143e4020b982034030030220181c1031941c01002d610607c07410104014001411001c02071080c00b040081d641d00081325101c1035520b11006001035610038a84002e0100100040400c0303015007203481e46070301c0b0080c0d0101501d191604000041c0409110b072040307552200c3d0b40d07840f1707555036140c0c40d85080d1244100107451420321603610700c0d0107101d1b0001981100340c030303420320445d507629415a41100e5040131085030070b59401d2880034018011100f0f980d0500e60101d004005c0044d69000303555001025200703446183d0320100111903094a444501d40031440b0001601c07503540c03c6800445941c0c5020301420f070f10650020b00b940c1282d01c603602203030308850388a45903070440c41c00c40e038450b4000604944250b514104104045422401889803e052203107858644240314080e80120035402d81001a400c03a0808031440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 321641483 1250 321640233 321640271
    0x40e0f0105100f030b0604090311030703120b010e0918010605060715050c040501080708060f0d061a0409050d05071104051305060c040602030d0e39090f0a0b0f0301 72
    0x80910082d54030503000c504041d05284400440e9004209004261100c906210061910352005d4003001400b04002441c0c1038200010720a05200c0e5494001c02031130300e6080c00441d0070f0048094100000d45104580580c0c5034107046812020460140c03c0980c20300061a00400c2154170060700007802140e8641071100203400300c0c2e862540f1040602c402e5850000707881291081e406140c0c08900040301041e1418441c010030313944168040c0c800070b8a09140f50010318520700c00e903022511143c8402c07400b030205d030341644040105d08007590b05110b42003295440d5516080b800110a041020202e0303e02d0600485440166903404007410400c10343c00c00200c6d0f00348000c0361040a840340d1140d98081040344038008111400c40d4103d40c0550300300f642412154001d04841810003242d44103501c00b0a9030f42c0d909410b40ca03001d522007025024a14048100a484418a1200300303104000d90000c1041000e08240708980c010100040003460700418000244255601c01e001d90b0150f2904a0400c030750340004517 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 321642733 1250 321641483 321641491
    0x408010c0512220605060120030a021507050406050a020a02060d020c01050f04030e0f0f030304091b030b0a120f051c032f0304020a0305030d050402010f02150411040e0f0105 76
    0x9214160752510003007880141e01c00c148403006550120f9100100b00f081d803005800c2401450808520f80b1441049070210b05c0d99800e4907129000040c203407035060340400c610300c0aa0502c861a03849841c00b0b08000c2c080e4080c0f48030b090244500051401065442800fa00750707410342c0204069100c1d032545481100030341240c100c1c0c41041d0b05c3d02c80414517100a0301100d0740316661581d500034040500d9014400390340400b541c0150810001200352100e0380e014406400640b4210034005681403400b40c0c1c114005c021407200005240c9800d0f02001c90303131100080d040c00c3e00c40340906444540f07400d191201c4a0300d50840054201d0203820a66a118190a4850b902d40b8500d59030034049040b014840600c0c50500f242500640c01c00005090800b506400c0655841800100b01ca07102036607030b032074503130071513200b00000e58596546d102003208641c0c00094004044003a407005000362050042845906500580013078100982c0150100d600e40d504e4225a813200d1140003030303490b408551244c09000e04019a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 321643983 1250 321642733 321642757
    0x405091005090106380a0201021e0307080606040f1a040321022806050402030a020d0f0b0c1c09021c030c02040e030a091e030c1707080105060607110301020408010c05 73
    0x1110b017101c8080e492070b94010f040b8500007403042c403c0800039003910507401120b000066540034000c100962500c07417040c3c2c00c0f003015a401e056481ca05640300400c0329000914040c030410741407106214884090320040192a00e0b10300d40104480d051500c40e200380034070b510007017028407500c090700b80301c100c042c40b8003115207265003c4840f9161140400c800c20100c400858a02e801c080742c607400130541540010390000d0019094641d02031854021030b2441101080564103500400351040803c1a00c0b03080c0c075845400c2d40c002c0342c01c200100b102c42c0d0f524507101401e1071416444411314000e6541d903800882200f007034000e0101d00300b00580f40241269500c10001e900c1103192000c81202000048121902403200ea1f4501d00703c1401c120011071801e00d4a550036500008811000c0001008a9500006840d0303003050b03034030700d0b100040c007082c58110590086003490341040305020300d94031001c06441d80203510041507020704240c0008680240180d82c0081034075800c1450840d00540c100f0003e1061200c45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 321645233 1250 321643983 321644009
    0xb040515240306070203180609040608030a02070902090d1b0e07030f11090607170d0c1d030c100c02040e1b1503070509040203180d1128020405091005090106 69
    0x7401016207844007228640b015800400a80c201c291490000308140c1c00020041e074108410756000c24101d0346a60040d000a51000800485158040040384001d0041400952403d0b50020107d0009540313004000c00003000c000000c10504c1107000b00c000949402c0724003000903d068400103010703024065103440c1c06850000c00300305681920f0100c483d0124081d04e520f20b801d42c1c59455050076080c0144118070303d41c041c00070b01182206805229032900259491401c41d02c2e05204e0f50110040080e146403095000304000f4016840302115880c0d0348800f800d20591582450000c1303800742406060b401514040d5111405458041c507141c800c82c13074026103810034403401da041006418403095840c840892001d00c4900359920b050b07001541d10070000268900a000850f08541c5072504044504001c560140d0700c2c404c4c00c51040080048901781704450700010701180013200c1a6803a45100603029070344980c00200810302c200082040380e041c0c034800700524600ba90845009004502031450407200c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 321646483 1250 321645233 321645301
    0x90807062a0915091d070903050102070c210f020402030901020903030d0c022514040b040c082e0306020a1b0c0503010c1106070f090b07111302030c070b040515 70
    0x4200c9503030060301c4154854100550705c0143c1d0921704040100382c0800c029691a0220010320280040c0c41c4181c030904c0744180b5182880104500c0940c4a090110a40c031020380340f0000c9003400154882003074050340c00698a4554104c114068403031340803160381500c0009240da03a2501d56501001860420b60f0135204005020440d40a60a01070046901c40c10070091050281e110000303075262951a00400000d0404d4060000c03130203844659040c0004120310318200070f030b0385004102c148103052486c00d054414032540031038020741c5d9000d40006451268045241100a4002c210400d81c0943c14541603402807001d207801e40300b40c00b05018482c000d50808406005050084c88a041203103c4440904525603500104071455034400100c18108080c00500142da40b028400420764140201049490214401d06204161030b4014052807964410030420503020207007000e81b003405606c031506451944460602500c2c010613100341d0300b00500d144013441802250804032401c0e4000001c001800c03424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 321647733 1250 321646483 321646487
    0x50a0e10090b0a15050d0c020606010e0a060f0302071b03080a1205040308190f02040b1308030f030601050f0c060f16090b03060d051608070302010210090807062a0915 73
    0x70030b0060f4100c01940c60074880001c4d00c810001420110303160007401e00107590705c03002c00e03125298030301405030b080318013801b10b6941d0020300c03c400c0035016104510034901c0e00c4d000500701d415120030541055400f0982104004858600e5001300780ea104c03802400035100d0810000680c030003080200483c1ca040741aa001d0111070141a200701c6c0c164459002903518207803841510801e52030008030541d40c0d10f52409801c0b031540702402c058042d06800c1519180b0b0050880f001c40c05503002117a0742d80c0b00f4460341c43c1041c4500e0440707034802c90a103052174542040112a120764010b6039140001ca0042104200411a00407c070510030714228400c2c90250303045400990f00d615050064084014041001034543e044c0443d5265099124204440300d04d80d29140c2211766035241d408c0b22405401c02d01e4200150741e41000804001c6507240400c200200d03050740c4580d050301c51050014007143d03c5100c194401d00c403404649a4000304803010349904d561a000041038101c907800303000385100004481c004268 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 321648983 1250 321647733 321647741
    0x5061b1306080709120b13081c05070f080921192c031e03040512070509091f1a030604030e10020c09040807060902120d030c030e0d11010204050a0e1009 67
    0x7540080c0101b20700d444840c520350b42800c030240250352441041013829046403112035040d030144201d060015407824407501c01010240c002c040b003010400b8910900004102c08940e40341e00f003070f0810034441e44640c408081455801900c00d1000720104105500d0700c2e05400058412034600002403d4100c5622110b07610700c01c1c03004130421905584605e50803075a03010180d40854007070744403038112801c0c10f90f1800040d0340a03500e500540d060b5040304000300101d0802c00300385500719062074090500d1141c3c0543c40d22003483c28040c8680c0326916140d540012906400155480c000c010b015100245090f040c003424400c900c50295009100081004020602c0890380c0391020381c000700305128580300c0e80c0b24200a600319102c192a11070f6506020001030b900c0c400d5000e48500e00c3c1c0054101b070080090301900325801e0040281c1494248162484400004503042500e160b40d070034141500c1c005642060300900507508420f400c030b58610004203d040144146500c94100c420b07000200c2e6840ea80580252 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 321650233 1250 321648983 321649019
    0x1d0910020a120b120706030b0f0306010303021b01090911030405070f08030703080411040603140d1706060706200d3207110105040c1e0305061b1306080709 68
    0x109982e01d400200359803034104054841000700866100c00c1860086410020507600140100340c0d10080520707241800d66480301c040380114080c010359855903c000c2d40720591051000c52041f1280005401da0303005210a4014002c480810084007129041c07000c0d9590080e1810f581078803030002c0c005224900000100300b83c40c940070245003814459681507400d10800f41c0100d54001c000c8030b06410a8840d482640015805000b5100c40c80700203095550810111128103002c0000a41c13a14802000040c5201d400083c103940a5946040b1801c5c100d00a148030015140c05901c0c204043c100510401c0c0075040801e0341c94130421100b60700b10317101d6040946440c00042c04040c540d020a0403003401c040440d034850501e0400520244c040651942100e400f1a01100d000c84d4401c02802581e0070b03548024580000d904c2107070781da24150b8135819034442000380001ca41211214200a6040415040c2c3d43e10340882c1820700110b40c2c95510140c03080320212140400506602000903203124803944840007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 321651483 1250 321650233 321650237
    0x20f0907020d050c0106030501230f0c0405091f0303020705180114040207031107090518030711100905031212102102010c0b090d030506030d020303010e09071d0910020a 74
    0x35000c0000b094070a41c0100304001115543c401000022600a0258020340c08131142072510044c440d40b02c4d0341c4446800f03040459005018020800300e0906003048070160380c0304551a50060342e480c030b034203035000440d002e22a1190a80b80b0b400010142c0000c1c01c401690821202d101e04420b442a00b204928024815084c602d001c1d14686c12007402c1a500500b5564000d180c00306992540014484c13034039096921a0203da0b0f0b07208100900c02141c40c8006420080f0000614505145915020107a2101c0903142c2c0c810350390300e116041d03c0f41c066040f0200800f000340565003007156050346082c0541002d24171802e11160100010425210b9002100c152103c10640711008201080340c58409224503a0403418041e03820034100100c0c200c02c40552050440380009d151124048400505440019100a020354412b22404651b5a004015241541c61249003007219513207001c011450308546601c02c41701c00c2c0103c1284079006510356446407184519030101c49020100007402d9080780300d09011500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 321652733 1250 321651483 321651493
    0x4030827030c031c021c090602120a0c03030f02090319120c0f081c2d061202150403020402070b04060501140a06030f060305010e03070204060b03100b0d021312020f090702 75
    0x181a11619a4a01d44e510941c0304a450180700c40c40704540921203503005002091983c0300800004d076040000e860103407402c04c0041d0a0108200010702450b05100c8010245510342800c06618401076040d1101e800d00107084510712020740c1c01306003c100c6c4050058800300c4a80b820300d045180140320702d6041c0c030390164450b19110f5003521442540c1d0000404c0340070007110f10b00442551010b5000c1c408a2800300c5c54200b81c00700795a04100d544a410f80121582c0c0c03400c10108201178035142112048040e019100800c0c10201c1c0307030700710303c46100360382000b03500c01d02c0841c5003420300c220250050710540c8107140811860362901c1d40440b2150740c0c8039019030711540500302404001e200707401000da0f4885c90b4501280d06503d9658203800e642554101c40e10980c00854a01c5c1549403074007680004004404c005491030a00b44458004420140220b84001000150008080701542d046440f0241c81c40120b00100361544e0351400c6d41510500144d101e101c0d2050400c11514140c1c20050041e800b0fa00200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 321653983 1250 321652733 321652753
    0x906060e0a03020306010b070f020a0b0307081501050a0e1201060303031b0305160509180903130905040804030803040213150f062c220e070b0a021b0604030827030c03 73
    0x1f20480d840450102d540604920951006869005824000d4074101c040c0710340368500079000401d003440c01081c0c40c0320b134a003490100302d040e6044400c95064401a01c0c011a0b00e50b0f8002c04180e84000c080114542586048000424183e050b44440a6000c800031403000301500424203c09540d0183c400031000c0c240c143c0d41032082c0d07002c0c800414401c40003408000750350b00d201001030380c50b80003160b9241c2617800024088681500c0104208013078494a1020401d40c00c183d1600162030282e4040100001300000110741503545403401c0004071035400c4001d000d2182c00722640c0e0070904051054084100a1110114030030b0b01a020300050301011000c1c2040150911000c403500d02a5580c8950f001120800607041c940e440071800c00101790080c1d0045000000000064035054642d84505003101c001c1c40005016a404103200380c2800154012410000c2d44500240842c821540000d000b0180010081d0202046640300c3c9440c3d8440c1400342c42c49050136080c192643c1c400c00465506800c01c3d0608 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 321655233 1250 321653983 321653999
    0x40212190c2a020f060a0c060516080a02032e06170c0706110d0f060302090601110a0605060f0a03030e030c04050c0a0c08211504060614090310060906060e0a0302030601 74
    0x448a00e5000905450003451000301107503986d400980040f000828801065091000501910350800041035600c102404c204000a0052a010345110100f54002011980a165880e6420300d0814558115090240c80800003090b000c2284100004540c450384841c900202d01a4082c0c42500f40014040c501040355840074010b03ca204800320040505002d10a5000604d214200c51501042c0f03000541a0450040001c8004c0061510f81040044000c111148a0124421414030380c010804070b03003600d400c40081d0b00781c0503001f2001e4020740414000810b00d5408003620074565802c2d42601d41e4081c00720103200c16034100721001d0150110401090360b1051003a40480b601078011030242d400e28228242400b05075004002a48403e84144280071700c0c0e4105e040000c000480031a000c1115610300030001e041180c204250218541c000704000340151001c3c40b000001c281d00010070400310781c03200daa00009080c18001c0600080008135245940d050a80d1144c00f0340c0c1c0c00038000c1071680e01e00045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 321656483 1250 321655233 321655307
    0x14071511031309151a070606080109030e06301f050105090d1505010e0f011205060106030e0f120c0c010509090115110d0e012d0e040212190c 62
    0x5840c010132140e040c00100b01d40c0800d03001d000640c610510780d41e65440b9083c001c0581d010341e000400c0c140d240c80032080000c3e40011341e036024400240c410380d88035914000358401e0320b006003103450341e1100c0019050015070085004c103403040c00c5042070b0002e40c154016040c04201081d0043d039000c51010489803a151030100302c0c1d462440d1040300c003984441014803801041e51400c1e4001740d09030310310106115500700000001c43c003500450388003880d0000340d81c83c2d1550b903172810302c40c03078051503540c0c107504130412001e000c901040340700841121080030b20003030b06012991242c42011aa0301071260100c0040d803040040b6424070400a002442c181d003005607030620249510112802d2091644071321403108414070083c0c1e004d000c40e481d08418029080005820081044e28036030f0310300020a0f6204403a41d944025080b814201c0c0341c2000414029000b040003440741d902d5101d80710a62104000c10700031460601c0d401855600c0c801e10108000000584a646a1900c868041411008070168240100302 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 321657733 1250 321656483 321656501
    0x906151207090906020910050f071b032108060a030302030403110301020c0d09050102060f04051c0203090a081c050301030c060c060209090c0919060c03080414071511031309 76
    0x1075070009a5a1445601200c02d5084100c2da0a0380110300d14000e403070100300109240660742045494554543d042c040207210f00380c001000f41016511459110413030040c0200030310752044202c031074241541d89620b80f02d00000c62040014180000184603030420446010440342d05400840c00c19045603203d05a100e00c0d50183c942540d030034820400d14460401080549112548a000c03481e810140020f0038190020030861504c00d142042c003000690000d2145c665500f898441c2c4200c41134030300101e08520820500707a9028140810100b203940c0081209840c04581a510015000030510252030750b00003444085d0031120418070411405000e850441012845004c00500d45101800002c0c1c0003501500c070b04c0344440011900000d02e04080c0e481d00c1c3c0019295001340041c91821500405a0201202c010104651500481d041250300c9500c0c0c040c00180d83d05480c1002c8d103400c02c00300d842091040860000b1141c41180c00e82c04c00c0801129202c11009006c40c00340350a005280000c0c10050f6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 321658983 1250 321657733 321657769
    0x1140303070204091727150403060504050a080d06050a050306070f08070513031202010c02010905030901260c12360f07060815091608060d0804060215090615 69
    0x4042085500340310300c000c0202134291b54840d050103000e200740010070082116042c2c00307a440c4005034580e00030070106440c1169480480801d866641e4a0440c1c00d01c840d43d84020700481c004100c4428050664014400b03807001907405041c0b860b0b9034020160340790f906079440808141d202d00c072810494403899480303500104909029140c410403031010340c42800170b907000341c50300d403400c0d1105005264280201040d0290f203100a00840c4096100d55031a40702e030072581410300c101550058891903e8a504200680e0151041180780ca442d41800140380d10070100d141c90b144d8190002a2549035101031034074011400302401e042d06144821440c0c2081c5142d04c01c1040d881611072007087c4202c108100f80c060f0000e50395191490500761070007826400d8603080c082c803d0041c1c10402017140344800c684407411045141c060340b56110a008200e242c2c058500260610500107008079105400007a00c5810301e80140f80000241d90708000e0644500b011354880315296007200c6083d807540f51000480c40000014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 321660233 1250 321658983 321659003
    0x11101020310260d080a0608160902160203010e03040906050d080a030c1106090f06010b070b0f1003050601030b0103110a06050702210115150201020306101103070f080d050114030307020409 83
    0x1c1e00703e00d20b010b291507040b00000f0450001c1007889a500d01903500181854001024004040a0f141c0e503112100d0080c0c000d07456000c1605102031010752a9440940d070081c0003040304088a0081545aa05c0340c0144880c0605200700003440b418950240075000d5001282c90b82012824081240940a80c010960800c0070344c03024403500705000d10040c0e0062121300004c22049428a0259041040503804100307001c0041c0030407804a0f0784e90403403552011100e4050440c0380d0328218080c001d10041d0300054414071522001004006040c48151305032402510000110070300002000b0b00c90a142c010040015030a11602d00182003045440301428100304514000c0c48018001e24215815401c0c2e0181c03802a01c0e00401001580e20315030020304110780b0003545136141901c04200103840d400081000c10038a0500504444ea0a0050300c080c0d66000c40c0303481841c261401e100a898000000c003412143c078050001070703188881209602041409000365080204640170000105541c01c01610030103030b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 321661483 1250 321660233 321660299
    0xb0a050c0106050619022b03050c07051204140409020d060203060a0b0c1e150601050a02030f03010e06011205010501020709110c070305161e0b07051c020c011101020310 74
    0x10f01c1c00a00103042d0795030100c01ca4010074060080c87d1034800f055076582141403207008101c540044500e1004581a41004101500c0b01800160306100c0d8404c00360040c0a404540e134100342040000308200d8510040f520465041c48081004840c4466402544841e200040303d001880c00c0d000355500281c000c10108000b41d40e0170200c016503201d041446655004059a1443d06001052600810390030030000d1004100c0c10340c91249000b0003502050511030041a0940300702d20810442c0c5040809604582c6c40c0d5a42e1000038940800640b0800d0100e04160074114641c81144034050499505030300074044203242c00480b00041607000403280c01c1200801401c0c1489000b003045000462150300104083c0901030384d8011a40415000010031115500c1a45014103841c1180e0341900e6400c40381694842681ca000c607c1c00c20080c920211006544480c001c41e80c0d00800c0c2c1c040f0050003a2640c41d03a00d000c030b43d07040b0708030320013280d104a00e02d00c020424420050710400e1018404800803c0c006a014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 321662733 1250 321661483 321661489
    0x4120311100e030c07060c05030d020306030307060e1e011b0e0402040503060f060f0909030403030e1309030906030e0f120f04080604081801051804050601032304050111040b0a050c010605 82
    0x20003402c81565548002607902400b1010801d0f04010001443c01196610f41a03440395102e115403070300300100c0781e0044085450b80d41c05008407480541d01c80d07410000c90207800c032215200c3c800099560030036030340c280500c4480c00040c0a0140d06a4000d404075400d8140c84106a40007124030780c8140d0007903800e00c03010070350703403000c0151030700a200001c4a43c50600d0b00c841040000301800452500032040c000030f00c4140403000003540c003a6545800d15406104022003c900f0201518180849040c24409217006040c1c00c02694030640d415a50140842c4c808005620341d0f54400c3c1c814298941d00410078020907000c07040c050f0440f00142d562503450319a4034108103203000c1083e94142d400000c0010008031550301c40c2d4403055214800c2c00c21506206480110342d6842d03400d505480c5c040c0782c03a1000580103a119038000270f0840a40f1000c890000d07020000200361400840b021203607580f800403104000202001558201c8041c2c0f030000b0700d0130b840180304942030340183c070104200750348841010171140c0e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 321663983 1250 321662733 321662741
    0x8070c020d0c090f050a0e03040609120326060f01030203071d040906060b0408070501021b09090a0c08030702010e03010501150f02160b1c050f010504150b0a0c0311030412031110 78
    0x124140030b000c01c80382131000100084410310143d01f4159032040204010031504041700001b03c0d090003940e04c104071501d04081c1c640144640f84078030f10309820031000410120f0300c008140a48420b650b540079550b061030056049100c01d40d0740002040e0300b14010110150702c41c0030140d124101510101e032800d216a100740540325643c00c81050f030307440490140002801000504000c0009100070402c488036003c03c2c0c02c42c0304002000601507803000c00020010181040040240c40c0e200c0284440c4550b203119141e100e411048049002643d04405d02d50a1f281c1401224140c0383c0c6607c0c0b200c00320803680e500b51400130b03000c8254020341c050000180300b150b04810004004140700300600380c0d10116000b0039001d82c1031813244c4e40105880c1c48103010402d180000e280b81501c0095030000b4540407556201e200d031240d203034040000d1980000385205030f994031140351071100d8802d80f50380c6c3d00740140c4142c40e901c038010760103000d8005014804a2011a22aa8962185000c440b003500d000780c019110301015a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 321665233 1250 321663983 321664001
    0x10e0307140f0102040311061602030a030e120604050d08190504030f08090303070909111e12130f110418030c0c060c0c05060a051c05010f0608070c020d0c09 69
    0x211101071600e0340d00c03841030040d100c103501d200c4021444c16003140d9403442505108245580548404a880040c00324a4041c41461703680040854548143c140b900038142020820f546c0e0041c07000c0c4440d5521001c001980e940103c0e0302001400401e00484001c42c1c0140d401030a603078140e0b11581c12100d5a42d20780c46000d004078003d60301e20a0010484202502a007000b42032102c09071b200700204081d02c1c1d448007011007640c0f40c1e20b03800314468905456080f1345020362110341c80001410300400403200c60210040c03500030451201a5070699070142d0f0b03540e01e8440030b20007400829102e410340001403450f00360b142c1c420304000e10016490300100c28800c90001919001c4001c109908100000d001158041500402950ae084040880c0664980c88008610b11500e801060042141a221070050090721017080900c02900d204404684039803019040030310940003525044d50001c9000340c1300e00d43d15071048450f901e44c0108482c0540c00d104201c19030541c180c854400c0c581001c00e0810844c02a5050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 321666483 1250 321665233 321665243
    0x6060302100c060c1b0212030f0c07080c04020c07090509120a0f030b0405101211060c0d030b03030703080f131e02040615020a08181507060b0108010305070506090102010e0307 77
    0x400e009500c1c0550403507024603480c00c01d025040340d81400d01c04404005d03e45003541556000e0131170068051151860040160812200ca004904420100f0780044c011045480d0341c8115428024550188422032290603034500301900b01080c14080d00c1510740101d900103004004a410008002c3d14446264001e09003d8000400405d1240d60250f85800b0306100766038101c50810040c1810300b43d170103055045100c0c3c1c0003c1d441c1c41e4005d009005e4020840c40b18400d0181c4016620940c076004543c560080b00d8484e40801c2c60b151102031a400c0000c2a2403c05034192a00141c5031601658241c03030100082c4580c030203000920029000480c5495121102c404204403000740380800e104110a544540c1c10031050646912840e4100940c00a03c40c01d000d83c128a07a1580d40d800c4188940e02c141d1062034158001c101028000c50008816000f030078602e000311403c2005414203001140c3d0540d00b888040e10030380c03102c0ea0900c4140b9140b00100b00b2100c0c1400000340f009651984039040da00300c4082656 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 321667733 1250 321666483 321666497
    0x907050c010501032f0f040908070b090303060109090e03091c0f080c010617102310031103010c021c05090d0506040308070c2001170f0601030b0a031502070606030210 73
    0x104001c8172a09951500089841000d00e10b21000810b1400700d6040b107a03882030340c6540c80300080c45580421920556005000d80d4140c0c40c0c28441e642e41e940c8241c4003540000c41518000480383d10364030442c2c6803a59400061403401070801c0800c00346001c0c2c0b400258070b06680880b048002400c51210703041d41441450001d4448000c0d192701400c5880302d9121052a81011259028038440400c0c100e8a40b1030301d1000280d84464240301e5a0701041400708070808800701800c0c0400903846948a03c00c4a2046180c00aa41d01c41014503080c0e9844290382c0000d41c0c81000110500d03082100c65003009030107854841d080c10700d04c2001444044c503135442514240c1004081c4001d05500040c5c0e60703404440f50801515002c0141d07111421002d440c001d0f0300c0c0a10604010320035a130301c03996043c0108007034502200480d050601440b50030200c00e90700b00d03001c00d14060460b40c181c1000202e0004032170700b00280c101801115400ca40181d44850001c90f50380c0d944032000304c010f82d07030b076103d000c5075401c5640c50304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 321668983 1250 321667733 321667763
    0x305010801110715051803120901060f0302010c03080c09030a0f05010e0a080d020a020c1806030607020c031b0609041d060a0603020904060c120e010b09160e0907050c01050103 77
    0x10307086908005a81801c008100002c6021801c0c074000030350884040c100008441ea6010884100c3e481c0d400c8044a16010010701945d00341c50400031140940c40e410020403e581d0744001c400d6070300c001b600c002408968203018000210b80928801540070803055004da10740b100d83d800207403c1019110b000c607146240d00b44c0c20001e0080900c22410803403001001010026450345075007405c0d00807040142075017600051203010f0a8400c0c010a00c0361000901410410106112003007103e02c0100c3d1214042d102e004001141c41d2b10004a44520000150180c0030314400c404c0750503003a8119201ca035030010010025000b4a44540c454038070f1501010f40310144841465540790704003007002d010040c80d2801c020090025076205c0c030200350090ba10000c0065020a54030054501c1c100d800d2000501d03a1810140300d00c000380c1034010640c06001110f210000350317601000700006907030200c086030001d000a2246078080c10301d41d41c007603042500d81c02d04a0a200e0401c131074500b0340750b090308101c3c0c9141a0903030407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 321670233 1250 321668983 321668999
    0xb160c14070314060c19030e030310080d020703030e1002070308070503030f280b010e0909070603060611100504030c0b040c090501120510020d141003020909061e06130c030501 77
    0x10b900e40001d00f0f02910700c40c02c00101c00000c1d8002c0000d40d0620100702d043e11011103010350b0000000c41600d6040c0e907101d241000d07504a00c2001d502c03841000e030281d4503200c440711b440424a00290307070340b680716002200361520500554000404030f080540c802d203400030003c229100003400f03030f152185000355540e20340040c09003000312010344001c84000d5440280c0300ca58090740b800103404009940c0010748214010b0040324207500d401c01558000e0020400d1101d00c400120320740c0103480442d1014006265943d10490324040c10036005070741c50300105007001590015030046600680246002d42034101c03162203128200e0742c155021103281441c0681004401a1800754a0040c0902d8a01d030701c01c5c100c540c032180d2701c4600c0101045601980080d9482014956500c000504d555403000c07280c0030703d48281e0501500c58180400c0e03206852000000f421a600003d4291107400d101941869074403284052a0600c0d001900042d030088800901810075042c0d88600703a440f00e107564010405500d08609 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 321671483 1250 321670233 321670253
    0xd0203090f0d0807020a060519050a0f0b01091d0c0c0f1c08060105030f1b0703020c090a090f060c20010b0109080d05091e0904050604060b0d0b160c140703 68
    0x40c0010b0100b00d07004c1000594010402d1000c19800800101d5290b54042d4600c0308644941c42c03410800d80340100b80180003000b54004411103041c000300b041413620210040d03030351b0440380c818a501070040015440805494001d8241c10a0307041d0b210509000141c00003e017030040303a07001308000c0c2e882102c90134254031b043d032011070001c212420b001d2114185240000c0880c80300034002441c500119000c65103480010012140003421192015111051407800030b40300c0036114a081e00c41c22814010907000c2e0b68074404c50480962120300025502c410355140c030040c0140c54900003d102030529407180c00c5450a4107402d00e00304075800007030020310140000d00890000c1d0000c00c00c952081340740d2140305070003200f216404d180440360f0380b0b01c200341c0285940c4004108000180c1240c07a01042c4000c01400160070745c0940c1c031451080c0b002102c0d480500241000d1124003070b00f0104480d012a0400c181c88040000c041013034a080762002680f5102da03e208a0301c805641440c1d44012000c000b44403041c1a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 321672733 1250 321671483 321671503
    0x3040507060309030c080c0f06100303080c09010207030f1a0f01030203100c230415030605031e0a02010f050d11090102010c05090f0f0607140604060b010f08040303050c0d0203090f 79
    0x504000303c1e040d0351030041c0322481008000b0203400b000100458041e404000d0007108a00300c408550782ca1030040b460549441071031000302c0104462401049400e00c9030011f60706040d0f010780c0100b03040351031601c8110400007000c0050720000c442c5d2919804110b01d210200c1d226004c08690011503502d50310600d8500214061050740d220718005100040651103660000e1200340b440031820740d100320211301d2500d4412680a071440b031042003060700c560740d05908502e045500c120180d803801303095100c1540340c051507401451400e4108841200056000c0c200c03a0001c0b02c1c0528025040c07503038000d8000d0464648500c1c0c84800394020403c90312542c0c0c24040c1c41c0403440d0f20300d40641070030b90050100706031b04c410b2003003144104007401180c416600c170a010b40d01c07410703008180400ba20803c02002038a03041c01740e50030303200c030b81c1800c07074282595016109407441c07400e9541d5503400035511034a0803402000b01602000ca060000c22242000c140280041c2d07000381a10800340104a0820462600c0d04d95180707 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 321673983 1250 321672733 321672737
    0x11061005100c20030c0409150c0203040f031509051603050c04060b161a070903020a0f03050c0d03141309050109060506030103061a0d0b061201021c020c011803050304050706 76
    0x4118040003400d028140095101c064415454103805040045d003048440401150800d1410401100307011080c10000940c2810290401028014800072071710303032049005820700740c5a2190100f00084030f0b00105c0a240680150005441041c0d68540e42441030340450290300690303d500500074000140a15209100d04440400c402881c000c800703c0710380a0281642c0400001d100904140006510341c1a440a00d0310910503040c681684003420011a9000690040c4032849021448074040240da609898102c0c00400151408078204030b86290766040482c00c02444c0b070000743c0c5d05030216000e040405400f13a54042c2d014148002d0104548059000c0742986007840c1003004076803108812641541d4102c64003080c0c030000e196000c283c548078540b80a4010180701c06036400d10220f402c0d418021030b021103401d1014040d00700803074280c1c0a4501c030055040c1416403079540501031a40100031501d00c2c0c100100f120f107000e2640d540c1c1a41188825030201d04c0001c00c110800c1002e11460020348458 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 321675233 1250 321673983 321673997
    0x16020d0305070308150a050f0423010f1e15110d050927040b040c150906030e010e0d05090d0c08010c0906020a0803060f13060303200105041505071106100510 69
    0x2d400203886d000c0714443c3c64000d444142d460441c40e203541d000741d121160000b280744511065920b80c202e10942c24442c07003440c0018444003060b0f40711254070f18246041402e02603c415800c0041148540554280e5034052080b0110103200c00c0000388030360344c0c903e1120384880780c90300304290034401848444605d140400002440c000c2604850389011600240c014245140c02d603261f181200589115420070320b204443d668008101c0380d80314200c2c10942e01030b6541408001c0b4407070041d500341c40e24031101d0400b58000da4600d41115104002403d081c140003400d124201c00162101c1080050380d070441c000a0b5103504064a01907000111100145120f2009000490711307a03e41c900140001b400851103040e40c6018803480d9950038580354117151440508014040da246000b03010703090a0104c9181c90a500301c50b49039132030810700c5074a1081c1d81103d004807410220b586600c0080c5002011030040c454100714040c2000030422000c1d2242020050321003402e0306100401010140b10381100e0200409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 321676483 1250 321675233 321675271
    0x40309170a120f210b010f0315060509010e060d06050108070203030405070e060103090501020310030c050301060e0a050606040807060503090105010b0426030904181205071716020d0305070308 84
    0xd400d202e006141c0d2510361107549500703904407200044010b02e160b2102103495003482d5452980d200b840e040c80700340ca0310951040400415030a90b0310910460700c40310100d041c200706060041005040201051401d050100c00c02000aa12038001411082030f0541d42c2e03900b4405540c12010b541e400c4104c900045095191690721107076510fa26000d95051010580c4c04501c05c1d900941202c0040340d8400002d649a2400a03d00c545600652105031404420a070340018030f4101841070700c0503034005480418140c3e640080c840090a0041c0506400900c2000b00190144051040c031015103540e07a6802e580e030406042c51800d460042e0845880210308101c1040358179103c07045048007020500c80d20107140c0d01040b80d2429401880d4644d038225051040d00d84a6000481802400c41c4c41412948003899603d201102c00e801507020041000400f10880400c5d64080806000c0c0c0d650300344200c0325054203650101e040441c50403030031000b01e040070400c20300f0580c011030091381c411b00c1d040c514042818 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 321677733 1250 321676483 321676493
    0x100b060702061603020a081c0606030c1202090a120f150b0d1506030b0c0403060614060301050d11060d0c02061e010b0c01020c0304150f0e1f020312040309170a 70
    0x10640903885100f01102120008242c002d100c00c11010f86c0000d80a45c58040791951612094640030302c001c48140b4065001c504c081c00b81c070500d0702c081c0c42666201004100018444000c0d031041944552001d200d80d03000858220424886991621801c0f40e08070520440c60704c0e001c000580200c1e01c06a80c02e11040017400e4584420040724680c21181f4418000c110b12801001030510b508090885910181080724041192000b00122807080c10100441a65034500a44600001d507400380c0c41007080004200620782518440da07164066003503004002034003400030344503a01000501011545a002c410344c2c0c80d07014000e80e5481400c1c0c1c0b5810240f040ca458031814400e5050003500c01080001c50480c0b0340303c400354103985002d032800c0d0031681e0340c2ea00d030307040e0749800c0d034a07000c0900024401d11002c0c044944604807221801002401c84175480740a200c0d41c00b241d400c213040c0b4608501c8180010320b0500c41d4240c0041c0100c0c000d441d8494003c1c00c00003040c07107051102d03420a0b440d45c012400500040c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 321678983 1250 321677733 321677737
    0x2407031d010903030b010f0318020603220302010519060806010603050702031c090b060405040201020a0b09030426060c040b0a0e270f07030e1c0e030616021b0d0210050417100b06070206 81
    0x20740c1156a681d0300e03033713801002c5001300c040780b107010406114421904d420103405500241c0215001c1581c4480c8505074000c80081d5203890140200c0c2e030f0003010040000324080d1300459040300079030041d00c5c106021245410060490640031007800c9898050350802d00602270314454110f84141d60038001c1e45007030340010399a00003103000240303030288090014007981802d20a44010f022840b10710382140c2c00c1d180d81d02020b21100c240e003001a010701d001180e04854544100c03401c0300e0351004118280404142d06417000c1004101e0543c1180602c000c10a40340303000b2202400c0b640105a00c0280e606003c040c0b1226500c00501d05400d05140c09105c20b03440c107000401500010b00d40008041801f61604101c0b0300200490703050b41c1500c80c200034000d1004590040032000b450702c1c0e080700d0755110340c800702d001d445003440f0660b504031094107001c0015042884100c01e0415807814000d01c0c1c65a103c112050802c003642041559820030b9980c03400080c441c0c014071110b64803c5414508007011600055018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 321680233 1250 321678983 321679031
    0x1e05131d07080a060f090e060903030601091202010203040b0f0a090602121602030705031e010b0a050a030f050f1902030606030607090e09010e011802032407031d010903030b010f03 79
    0x444282c00000b40700a880d504030b2400f8014001070030020b690340c3d071001c0b030240c42c20303403c14a124010103000a090780400015248076040c16986e0f030481a00c0d108a08800d900100c10a0381140000c0001040c103401c1c00300144080c1a24403055503840c040060024a4840030303411a00464100c07c080e0a1802032660580b403000384141003500300880b203440082d00d050440d5001907050b003d04800c54406062030603490614441c0390000b405144800410800e40090600a0b03c2e44030071018428004101c6010b228660284203108407a5011103070035030702e072420181600b41c03c8030480e83d0072107404500b028840980c00460580c01807415040c180c2020700350340031a005000d118003d0100052100e017094011415802404008004001c0401510301007403452004c00d13030007031040118000412041c42910040300d05010320580c1c254507181d804601400420816900724401c203407681c01e2020084c45108055072094500060010300800058021401501c800041c546008001a1241c0118086070f010b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 321681483 1250 321680233 321680237
    0x609020319030e3120090a09020c030406050f070b010b0405030f0712080f0403060f0b0405010b09090a0b0d0b0a09053f040e091006080a211e05131d07 66
    0x1000960940040101751742c101c03c2c45020380d80076010821540407401040a5902900c8942c02da6440300c58a109900c180d88d07801e0120351040000304001841900030b4102c442c12140c1d0203281a880780c841003482a020b07082103078200b1001500700b04d9032401b000001290040f51300036060583c544100001140c1c00d940707021b010034800086428140014000711406140e0010040090304c0300d02c030100d0010808071079514041da280400104030300c1e8641040c2c802d440001414000f00382d9920002401510201e41415048130100048400160082c84081e10461a02c5000502041c81e414040e207090f030b055259041c82542244144000356a80e001594046580300a80b034040c09042c0c4042e0080c85980e1103443d2411840e000c0c4400110007003144070407030381d1410382800140d07151b110302c90b280e800c05c40c3d00802030300030210026045005400c01d2078444905081c2040c48008441c8900311101e040c410800005e2000140c1000611100c1c3c0604044c0c0340501c4166400f02054104070421300c005018542 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 321682733 1250 321681483 321681559
    0x6040206090105041d09430513020c071208040e19021b06010f0617060310020a110613080315041b0302042c01120609020319030e 57
    0x40d85074010070480d4000c1008900c00103100d6001c0840c007400e02800d031941c50346c1380500c1d51800314003050800e2113044050384d030504c0784803600113000d125040c20b12110468201c8840001c0019544e54002009074041d515001c003503901c0448101503420803009400401e400c0c101410300c0c8011034600d20a9905980c090503c150a80e150601d800007010b88100a601c5100c1c00010400c404484c007035442d00c0201107481c00c4070507990300c1c1c0c0e41d00c61603442907000300000500014034103580030710884403054100f400901650502030241c403600c0241d134071510085000c509002402545844200800755000f0160005804540c0040d61040518800035000009440100908040d80e07034550b403102444241d01982500c00c1254800040c010350054459a001282620f0003c8075000001d0000c44000361014110b43c3e180c0e00b014103000070074064101c1940c900d6a554400b0f40141c804120905418031081e004110300c00013803030000c008520800340399005000c00802c041219510034001c1d5035521510060b15 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 321683983 1250 321682733 321682747
    0x60b030d230c0c090709081f0507092d051003091a0402010503150f0310061403030c0a0209040503130b040509060d02030714150301031b050a06090303031503020d0b01090e0f06040206 80
    0x6c078402c005401820036400b65012103010000100081c416164807034030240240c0c0e07030b410700c10740d0300300c01e144076140400100841c2c1038002140303116400500465448841d070a503840307030040746100c1c0c0030806c201e010940d0344c3c950405004611000500e41e41e8002145001440c280d80001e22602000c0c103c04150100304100d01402c2d43c2d0f510880400540140454038560b080c100d1181c094174081c8980742c82c0018810540415040102c1164101d0360705900602c83c5e5185070b07090020441b001170041e00d10b8002440b0130400700900544001c001c040a98000b51210304180812000500281c9800d1003002c64100c2e000040c5c0b40402e40c2c170101e81032801081c0d108008500481c0b5034941c08107103a000c862002001104010040141c00d81765600201041031040c0ca0390b00b03000040707107640500800700315610030400000b07100c0d40202c00c900d00a04a00c49209540764041000c0441c41c4030100c1d070115200c001031141001a00c40d03880040003071001082e68141080c01c11361900c0001e0400b07030080500003121 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 321685233 1250 321683983 321683987
    0xb0108040b10030512030a2f130801020309101d030403021908030a020106060906030c080a0f111204110913060b060906041203030b0f0a2303031b0f0303150d060b030d230c0c0907 78
    0x2400521004ac001c0d90340e071030854500c03511071400b840ca440d00240f030300b41460a00f000d110155403e0741150b8006510f01303415602003000320301c5119902540ea5003034440100b1190400e002801480185070004500541005005040c0607155003000003018a0b01503042d02c61030340400e4081d001803000c100090300c40740c82c6003008c002c0c000e00244644024000540d560810f000c91100b0307031149001d02c0420010142c0101040071211003500c2160344d0180b00d00300c4c80c0c049449a404202c2c01b11005240030719107803860001c01d001d034005a100d484a010240c210005054150103900141942140c07000c0901c41f007180041c002c100316004034000c081ca80ca43c4800c41d2030009600108040000b4100d0f5124132545c5403602090200100080c12401000c8465042100000907a8040c3e260000c21110050f10700302070000c1d1028003841942c025842e41130141d204c0c0c4040c0903c24600095a50b0410119121001e0140394009040703450b51612080040b40d04103d03002c9421183e9110886070410075898841c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 321686483 1250 321685233 321685267
    0x6390804020607032c090f15100207122a0302060a18170606120f031b1f060611190602030c1e04090c030b0108040b10030512030a2f 58
    0x100307003069a404a0341c1741c1c891011002c0c1842d00c5004540c1c040150307586501c0090384a10581e0b803900601c6a040100901d031620580c8103144258a00c110380100390b07140e00c0003c410300410415561140b000d4140d901ca071000c600410f803e07010710310007048c400c4d00d158082007007481088411010001420301c150101d11075642c0040c01000c244d084c04c184108004500354580000752a00b600c00c40b41e0340c4903241d03a20004140742c078400321b480c0051800c0c09540706500c802285510f000c0803250007450080307603520020b114550190105548009a43e07420440060500f841484100044ac1d0103155100740030702e00d0702c030045106a441180540c070b03615400c030f802d0854010181c00341140c1503480d846d1641034540c00b01510031514404014405891503100690403623000080040c0050105000500403030307415181e040e0441074070200c5181c002d54a8076440c1c20006030107010070051078004140401d074680b03405401d5086041884000c03010102d00301c025001c6c200050200400f61010500203011503074408 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 321687733 1250 321686483 321686507
    0x311010c0e090a02120a0c02070e01030f081303140a140c2d031b0406120506040b040809031b150a12090c0e2d01080705010c0501090639080402060703 66
    0x40c658042c21b10401c808098485c01c80e04c20300621030706e04001035111190110354100c0e9000007504055105940720003142c2e5004d2040e9501e1b011011400000140800303c07101d801c05035001c003400d5040c00625100f100a010300c249000107600608410501e40e9132281e02005180b8039580144118141014403000c0420514010b40d050041d6011100e403070066040c6456214030403503040281a4481c401c1d0940081d0802010b001540140c00040002e038240a107160010301034038090381400c5000300001c3c5803d14907520141f4000c00c080a117141400c0c0b030340915a400c0e130508015410150843d40041205068941144645e0340381d0503182c1c140006910303008003800c1c1056a80803286411141500100d80e80b1444150f42d1002e401da14805941c6403040f01d060b45c5981d8040c2c199030b03152000440724034405d40300a40300d40d543d418541001580b5403041c04030112440d03240e1445201c442c148280d07588048034006090105107204450915402008141e105038100c8840d070310307200d060a049642c019401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 321688983 1250 321687733 321687757
    0x1200a02120d0201050a090314090406090204090e011d06240301060e01060e0a0f0b0d0b0402070f0210020d080c030c120114151201030f050312130311010c0e090a02 72
    0x164040c2400602240342c10030903800d50001c0c055a00c0c0c0c0d243c084200d6690800144c005803a1070552011701800320010b08000e140104081030054880307201c01c0407644158448805940c0d100d03c010403a110a0051420003403441c101502c2d0413100103200754845500a00d074506007030820b02956502c005001c440745070000003070020060305803140c0341c555400c2400e0284601003145445001c04c149000c0c0000000d4604048200c0c000c13504e0f00c903a14200d41c001c0388071124010b480c2c5541310003a8803103201400c892402a07041c42112249030040c007400d1aa071861102c110342044c0600c41080707800c041c00780e400443d0210341c160f899590400c5101e41e806484031480c02ca403282c5000152110b2a13034080812184100c5106d0074210388a03005d10b13018491551a201d4961107071004201284802c0d0301e81c01014003c4041d2850b200c1000540300712540c1c103e414044a004204500d400e060740002c40018014442000b000405044000640b00090b0110110701c15649400000c0c02c01040da010b48150f11986 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 321690233 1250 321688983 321688999
    0x20d0201110111070c050613060509010201091a01032f1c020316060219030e1302040312120621060507020106120b01030b070f0504120303060f0b030f0703060501200a02 74
    0x80050f072031031980940b8050b55002100314001c295454002c0c100c400c000138650364000c10743c0c41c0c18400e540c0d0381c0101d0011810f5550701c0811902240b2110703e049842060341c01416041c0d030440c80e1040054104124114005560751700c210301e9100b92005055040100707d4030528810900c103804640d850700c1d04002505402001c2d01034000151040c0504140e40e600e40907644a000380300c5040304200500d400c09000250104584155030601513100d0000085500b00985080d0b225103e5181c00080c0754613001c00959100c1101760740483d14031519010b46110f904202d036001109614207400c90003102d000c0c000c1580c40d404100920f000b54040c1c0d004208a0400034080c011505101100100074802564640c0d844d500140741a40708911190440100751600d50915040c001c590002000c0400100d00b030540d10a00862480d2075080c00c403004020043d5050383e20b2501030355000b15854003809410070300d42480e03414002603030404442c2c0d41e50440c00c80780c180903420074200d0074580078250700043d40103958 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 321691483 1250 321690233 321690251
    0x8040902042301050f2505030f0c06060a030f030e040e0f03090f043b2a030105090712020d0209070c12020615040c030f05090d020d051303020d02011101 67
    0x110a9860b1041240e08040305089a500401540c0e203205400680381075410821100030110110540036909001c506603098001d10180d680a103558088100c1c1460300002003030261004c081040035550092055401e003103003c0c99a03540d02121140000c004041c0120403079408140d4840d40d00c00403110100b1411103001c0112200001c2e1603a018203c840e000f00c8801c01040d01c1c505090041800e03056240d840e40d40d06100480e01462801610198080f410407100361001031003108111444202200103036203024141030940310880c07107000d08040c90281e4105030400030074070301c041141d004a5070101c0d00402054a2440000ca20004201d4000d40c090102824043e003194402c40c010000f40c403600304817002824103407040e80c2e1a2000c0300c40480d074031104c041000306030030590091500e001d074506011400c048403603504030960b18111500080d55005502c4032902c40d6040142d00c042d039495003400c5190952114041c4140e511501000e402042c40e98813000440e441101c041500d00c8991000700700c003000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 321692733 1250 321691483 321691499
    0x406030c05100c0506040305090112090b07110105103006050a0506030604080301090b0619020f010f1a1203090901030f170c03191803080d050a050714070804090204 72
    0x311406600d0203014142060078441c0d0160f0040d48046800100400041e40c0b02d54003110940c0c40040c030181044840d0250040c2003e4901510b40214801d01d20700c10245040c200042c24805074143c0c40d0203da042005029400320142c5843c0140c0d1001c3c0c25010802035614000002004441610913604c0c1c403217010a03051100b01c1d88414085e102c03042040c005a140c3d4410140e444109840140108904000410060700f0075800141c05010107040c103414114400c04107201d0b480151300c810301580114100390a8401c00384940b20302c41c2e40c001003c00000020450003000350011030070a074054000060092030b051000c1065409150000b05001410360b164a840c01c444150244210b0314022400b40b00c4070b0f40903102c416150790f0b0294100450910710101c15090041150030b101000740026803044006000440301c1d070b00d002d58000c2104560f5460744084050486100078004c180c91458881444080366120350071a198016035086e20b900e8a40f58208000e1b1031107941c4c0b0401086100242c00960390b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 321693983 1250 321692733 321692753
    0x30b0105040503030a2a02010f0309030c06020d1a090142020703060b0114030411210321010620010612030929030a180f05010510060c020a0905060f040603 68
    0x91b42841c4c0b403a803060740c1c4000243c2d24022a5000901042c58041546440c0388250703c601c4100e40030349051a900c0c007150700d501c0300301e0b0305c00444451540c1c0c444d040880508121004221940d40684c0c125a080d850610070400490104400f960100300d81141c1c100c44070750810318442c441640210386480e00318031000107941c45503940b04c200e030700b1410100003c8a070360041c2e504804090340392150300d1a41c0d03141c1c1d4030441e01b5811390340c0d02c03607200301883c09c2101c400080c19012481c0e0500b95009568940301d9100c0000c21503082c8052480b60f07440b11005100c00780e4400600c8020000c4040100717862030f9000c6110380034100e140c00a01d0300b201c07406a030000b4168001c1803a82260101c0054450480010645c0b08820216103140c0349a1441040804c00c100c0789540030346590609189204583c56095540d51000c4812032416070f00e6a445405101c548400d084080004040c0c6e4109011806e926a000c18142d1342c682c854030352499034909c0012004d4407945442d102e406030003081003219a45030720f4a04228 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 321695233 1250 321693983 321694007
    0x40516080108030a050306010c052b090801050c04030b340f0e09180124080606120d08060f06070b0f01080a030c0b07050708040f030b0a0207080703030b0105040503030a 74
    0x322424000a0140008011294a02c1c00d55036810316690751000103541e0511505022182d5201d1052880700e1140342c2004209501c0c0181482100307048440c100800c0241036404c5000316034503180510410104e02070841701202e602900c82849130f038480341903c1100311202450035148402d8842d01c2c5488040103c90420b00300e0716144d900c00750040314021074060032900c80c240d0700081407201145034100712400e1400d0340d0140200120b00541918248540341018030400015001c141601b8070540d04140000c5512100a6440c4507076100c011140d151707103065080ea0300c3c0c140050200031688507210400380000e020009480703140da905840c0ba08901d0395000b101c064088180500001c1a40c4c1c6010414910b0b0a4059075032141c0c0003d51784400008044c050031745030900404120341c4c00041c00c40c1c8060700080001e2005071400c0307890350070002e98003480240100d403003d104200080020304414240d400312505460001018036000c00140d5007441503421251b8541b002040c2140d415038440505400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 321696483 1250 321695233 321695237
    0xc0a0609021806100c21080108192a0e0405030c010c030507020c1908071503050601020c153a11030f070f05090a030b010e06150a030b030a02040516 65
    0x80c4560001824080c02d41075680a40c0003c4034040c0b6849284034401c500e00303c60086441d00702c02c00c54904460b40501450441d200412507110040082c1a4180010031008440307941019040d4015036800b4035400c034668090420740040c1c00a600307115030a199a00150440030907043c0c0c00c2c03d00781070155803038106ca42000c85560030414480c102500c40d004030740c000c00041e0018096800e040042000b20700c0c0e281c0820144404455000410603802c11640340241103031016210390482d529001400d0303407001881a415175200d0703000e80c4140e03110080c1800c5003e50000c00c0c1a22840c5440c80d101e01884410801e0a40c0d07801030b000c0625490364070100003088410340008114680a01c001007000c3c0c001110440c0f4920401030000350140d010700c210404c45241803601629000b000000901e042c5031036001a1082000080107101164501401a4001808668501c1010360a00c0c541110380f05503880705e0101919256081c1c1c030b90310208981048964014424081440c00034ad0070045d451044041c2c0d40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 321697733 1250 321696483 321696499
    0x305120f0406180b1621090504090204150b0306030d020c011209150903030b0f040902060d0e0f030a1e080405070312020a0c290315040b130906140603010204061707050c0a060902 78
    0x44048242c2c1e018074400c02c42500c0b0801fa10385481d080100402c040035090380c1140d02d940c044400c0e100c032400f001d00503020401f940368480c209041494646001542494250361148480c4281030b80c21a00d90444411031130004030b0050154038200000c0121060b501d0407260034008010101030b019080140d1750700050362036409540d852404c00003529400000079401c41e004200c0d04400702e205400c8800300803803500455209103220041d03249181d003c013250300001191540307010001401054255000a014a4132000382d0400f529030540300c0419100c000e154406911987c810b2600a1203041111034210b040a01e103550385204404c202d25405800c2540400390030b0031150003110301c03407e59000348650300c88009109403010912000303181700c0d080c2c19440103082d403031030107400030714080d20fa28544500c1c00031030f9115444500c0700c210100500b2840c802c0e401440280211940034001c0410000701c40c290070060b0f207400105030790500c9540d10000f400e00480340704a0a11105401c80d107001842a14448 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 321698983 1250 321697733 321697763
    0x210f030c050715053d0906030b06010c2102150f01031e030c02040e010f060602070b12100f031a070e062a0609070305120f0406180b16 59
    0xa900c0c0c450008000c004080002c2c60704540a0141d001a03801159895034075598501e40c0e000300001842d41c0068185d5500e0500d100c480707039504001c0d880051400c00d40c00d002c1c8605550741c00c00da51200410345410800c0b0100c2140c1800300180020291030071141c4201142c0d105000c0082d290821840b0300744200e41d605022a508106030000782d0b040302e40000c030545401c50700400740ba06c44a40044181d0420040048523030142c2d407244504607401d003412000080440342d11019000b035554660086065400c03400c0104959048007044544084c0402c0708100c69507190609000805d111750007402c01c0801c12040402040480c0700c9855000180c03060000b034a0ba5641d504441101c00d4241c0d582d005481800301c286185074552100102d0307102804c0c85c822107820103407854a82034044440114a90101800304180041480944c286083c00b640980c9002e2200703800f031090b40329034801c42c410010803441c0041d10a090703040700703c082c1001c1070005946081a604c0400003500d014000d403000b4404046078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 321700233 1250 321698983 321698987
    0xa0315051c020f2716020304030312020706020a09030212060c160302120d0e06010f051302090126061e0a03030f12020403060213080d021515030303180f06040519210f030c 75
    0x1207243e400c05d5034000c614090450741c00f02d07900a58000364030045902404490001640c070300140081410030744d150704d0b01c0c1d071a40c0104500a02009045001038010106210b0a41800c02c101d40c8030b4140d004030300640381000c1c0f0342289045041403d440c1c2d5003c2c0841d1418041d20650412007500012004a03034060340c030303400004001c800c82d04c030703217540700c5015044982900c1c03140d000b6201c2c020341410075003011000200342c200150718500c0b640325110624010801c01b440c11000c1d1010204003202d48594007648100031442c8002c0303e0002800380880341e00c03c005420b2003211180d4688840c1d040a42d00c075541ca150060280d00817200c03020f100c1d4641500070900500006a402c10f000c42940180185e4000504521490704050103210410b060180010120b440410003140190459081d00c02100c2c0c40544031424000c0092000781c1d25000039041c00701140d00050106041c13010f14084005894985c5464141c40d0104400f02c0000303402001d89080880e003000150082011170780f404c1c42464008402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 321701483 1250 321700233 321700261
    0x9030306080f070e10050303070f0201081006050706020327030304031b1a0a0e0708060609060a1a0903030d061e050301020418050402030708120a0315051c020f27 71
    0x1d400e4940c0c3c4007000800503404091440380c0c00c1013981654068540d1a00003003429517204030320a540d81c14445144074210750f40407a0f8240e21901030060000b5403070400340000d14505c104440504030f80e4010001ca2066070310380d1051140e0200980c040308165000e03071035240d00e9800844e82680451351200c0c03024600a8403925600401d584003001d0b003203a400c080400318540c1c038043c00c005440d82d600c0321039001c4000100036240280c44104018075003442c1c40300400c0780c07012005114034010003002000308248040409820440344205218a8985684502080c614001d20044011a80c14602c000840e018900c4030700298000b001c07400409a51180107050070b030703c80c1784108028504a411010143c0d262503201c81e0700284010241c40069507145140d501d01503884000100c0c0e10340c0000d080c0e0383d19070113210308014808800803000e0194a4030002a03809400b800009000b20710700d2141004568076460b1014084000070000a11643c0089030820b81482c642402a005144030011520403090140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 321702733 1250 321701483 321701503
    0x218040914031b010e0a17070501090203120408060a0908091002010f021903140708160c021002060906100f061d0405160e0406140f0a0b161703160e120609010903030608 74
    0x124070000ba511004005c023640300001c151215580ca0000c403006940078480b00c000118120600c90f240c50a04407000e0a10301d001d00044107949c545141c00c2d0005030310320700780d5140020407603031440e141c00300c1c0390b007a400340954614100305240b00240260f2180040c000d00c4000c00d40c03560b4108448429200300500042e026580308004c01c0090000910104400340800c40b500020328000300300f04503550101e4508480194818056085a420040709031420040c0503400000b12a01c5010345d840c000c400b0001d09558014001040407040784000d030541001d140d00d2206001a004010920300002c03201c6812038980f0441d00000e6003c402e115803450903000f00f43c15100030300c00440c041d080c084104009607420b01513158105461440000d0000c900d030016050b00c803417003918810803800340d20700019091040304640f000a00c0500c00d1041d0341d500207207042001041810030740b92041400c0c000400303481c2d1100c00807007140300e4401007143c8841c064012414462094a0a000701a26840055141e4030002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 321703983 1250 321702733 321702743
    0x30b090118021e040203040c060212071703060105071208060a051905040c0212040f290d0b03010b030f03040906090509030a1b0b070e010809010218040914031b010e0a 73
    0x401c01c1005071901c5282c0e00b01d240d003070014190f500c01d59030020a090ba00201c80940340b00060405c10400c454041c04180010100340c0030061820b050b60b518520801c0d06184132203408a000300000305142d00442c11a200fa82d00034010300c2c40b40788482002403e003002158914024100b6581c00519400d00c0d01c2d92419208410a000038100d00b4507084c0001403804004000c11072041c80406c41a42901c60f00410150660302d1a6007955400d284003400b032440c0d50603080d00c4000540304041c40e1002e110f0f090300d00c5d00190800102e0b412000c5000a4054081013400d554140100c41c840004c81200100400403183d110308244a00380d0b485010b103040710000c40d0040e909820400074611564820442c54002e40410b02c1e020107061405e8a80d84d41401e02101c0340340100342800280c100039a048000c603036100d07080d42d00961908000c21544070301d095071a071b26540103e0315888840300700060314002c3d103405000d0b81c0469888070114030750300c601002d0010400d00d6035481d041c501110f40c900412804500364200b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 321705233 1250 321703983 321704021
    0xc0c0d14040902090d081b0120030f0709090f060e01081c08040303150612141033030204230f01050f0c0109080c071d04030c080d050403020304030b0901 67
    0x44031802d00603501c44006290301c56924103c14001074841c00103001440b029140841065000d0a00c4508451410114104803541e000310030600101c40c01c210390707105090464000031358407000d0f1f00340c89000190300f05221081c00c00398180800f42c0c4a41c02441100d4010364000081d0740c6c1d40c0c8089840381c04000010f005854040c1c0e4041d40c6a016100507500030b84285000140c0e10801444030110f0032040d008400010f0309203550801440721400b075070b059a051510000c07010308001c009003240362001d10440021300005804415145072043c0321000d0f03c0c41a0081848008030a04000d000f075100d40a1241100c280d07104c2e012041703146800c0c0f2120380c5005842c002d0142046801903509400260015880310380400c02096040000e004171280365105035082d035110b900004801341010030315009401c0c0100d05848001c0c000e401c80f590250010b030181480c121817500d5045c4605148120b520b0511450f0602c0c0c180002c140c2d0000091040380d002d5003406003540c50302c5620f64280e40d03024071801d08104036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 321706483 1250 321705233 321705239
    0x302061210031406161805100e090117150705090108130f05011e090203031b07170703170307021b041e0204080f070b12070311030c0c0d1404 62
    0x15400318a504255400420102a5942d40c1c41c0c0c0e03083e4200e08a140d040c1c1c0c11031400d000c4907060456000c0807400c0d440c2402d103075040c0707803070b9410046108034815a4415140d0300398040680d40070348608071440c103002c1c2001203150b07119507010022410340c2e40c50044500c5034980c940d014440707402c07105028440d07681c3c80030f1800100380c00465240501508100344603218015100000b211000c516100d58400c200100341805204418402030082d120101b1103e81406080310050754040304881a4000034a201048401d000494500c1e20109401070392491940070381030102840002081e00489100c3c080e2103d00c14040d200c1080d03180020703503c40015901100c590810002124064840f1220107040003c80c403007200b80b84440402d07003020b641d074019800507082c4402c1e10140021070b40115a24000c26800d450a0040c01440c400c0003110704440881c0f6000c17480e1103110b80c0090702c609480c2000c16440c0c0c00c4c00c01c41488030307601c00ca40019141c4980113a80040c40c0c05610f5014001d014580600e0805103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 321707733 1250 321706483 321706507
    0x703020607080907120506060f0316090513120503090c0a05010c020111012a0908010b06120c09090c030a0f0b0f010c0305090a06020102040519030b010506070f0614060f0a030206 78
    0xc010f4003018060240c0c1c80c010078001c003101003642d440b9000340001c2082d401c102c024003000012050380640640c0200300b002d0302144003043d90300104c80812100103026a01e0400c491285440303a03400a01002e1038104100340c09600c480618003850300101500d030003030042c400b00304c003244103445080d01240904100801542c05140b40d8400c0c041c24000124000a0300300d007006034001e850a2044544a21400141d102e640c80543c00b000b80038003000810103d850400002d05500400c0a082400c00e000320000d20341001d180c1c01da0300044c00250505000d03007008401c1441507082207441e1440c032403802c65400c08045840c001c088028002402c00301400c481c0e1001120407d020b40e6084e0284002000405c81079128140854002c004e40d40c001078503103040004100707101c003001c039240410f81440b0303d081c804200c044907902d0440d03600b180c0142d40e0340464500003034813186080d00501207a20302548034811820400241d0b2044038115665524041d089081003085506030101a401038018000c3c011501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 321708983 1250 321707733 321707747
    0x6150304060f151a040e0115020f03272d0a05150301262a0402070b010f06050703021c0e120f0610151d0d080705060c0703020607 57
    0x540100c4000c03074000e0910003002c0035581d01d4505070309503803030829082040c600303010300140740c180c107490b03642e89810700e0f04942000134101809894449a550200d1090a071f000b0800343c400f02035000149e07601c440d00300030004510420303030340c501c07104214440c401c540c01e03e07141e00440e2030b804181000d00880300c40d5080c3c8104289000711120340140c1070000108081e80c4038400c240510111150523542d070b6062001e01d0252643c040c2c01200340c03c1e81400310100103c000700c1c2070710150b0054281c0d440d00c0c4001041207800c007188044116002480011003030184603600584606880c6410004291181d0300d0b81e0407950b52040c101c02a006810141c5240380384059100fa007642d02c030152918840c20b800075400555010108501e0460590241e0b4540381580018481d0a070701c058400c14600506250441441106110100c00b104004400b04182441442461008110700b0080c003011000c6107e843c0c86083e0b984084020741d02881034030300140f00b0b105164201c0e40143e900d640035001c640c543c40c070151004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 321710233 1250 321708983 321708991
    0xa170d0516030804021207080303090c01030203040c1401141801200309060d0207060203010e0f07020d0e0111010e1b0f04060b0403021c02060a03061d04120e0307080d080f0f061503 79
    0x16400e10b070742d07201b1100104590350280031014080d60b502c0c10110070031031500030b680b14103034140f45c0144100404100c124501c5001c032944c001420660b040d295004860140009440c103243c0c10021854001c00c01d0410196251807030282c07182100003a00100c1c40d404420811001c04696104110b40189400d09a000c2d10204144039805414075105544000c140d81090300000f21780b00300d403004c001e04445528040c0350013070110300140104040d501e50082821081c4a2070034140041d1760040c509090003503101030300005000003030707404030f42640e80c01c2d4242d1a0706c12400c5200e90001c500c1c05015181a01c644d9044030518440c251a0a1540e402c1c080846400c0300040303080200140b5000c0035841d840b00a203e100c0c00790f0740000c0c2c01406c20026256800c4040c0603000840140c10401c000900e08032000f4600d80014204204181c10ba480064a040c006402403040c41c02144414100d042d08180c04d00d01580401c41d104c490b9a4920328903003140d1208035500c41d449903d4080e1004104a00c10040d600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 321711483 1250 321710233 321710239
    0xf0c020c041418030f040b09130603030207030308040203030c0d020309012c0d1a0403081b0c1e01180803180613030309060609050906010f060c03050d050709050a170d051603080402 79
    0x200600d07a9841c03011364101e0b52145400030740000748c0c50300c50318281514404211030344404000490464170020340d1004907010040c14460003d01040a65604006607981803007403001311610b10109202c025100d400c6601c40c540403902046007100650302042d40964030b40340c500d05801d05540b01d842003101000d490081501c000814541110b12a407030f1003011480782d4080d46031389a450510490154818aa82c410a00e08100510100180301070124952015600302d034841111916000805401420140070501800d03511800b030008014240b0301543c46480362106140d0700352400001c2c941c65003400c4a000d8120420b8203400c0d40003174001e502800035075004210024070b594454182070222441550043d5240e4005001000300c20740c0d075a071140107040ca0f07150058543d00141c0d0040d0087c002d203800400820788600014801038410043c600c0149002400a002c039962a62501e01390150280310701e007280260541c4230480b07400341e422902c100c50a20f000020290007500d08032408170000d4800c9034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 321712733 1250 321711483 321711487
    0x4020103062d050901030b07110313090e0606030106060801060f090b0307031a030118150908030c0406080106080402011e02070503011112180606011d03010f0c020c04141803 76
    0x107078044014005010280c6400c1000c41900d80c2120004040b041c40d0384114030902d441001440001d42d44981580c200c4803900b40003d8003040c8c2e50105045000d840120440354882d00c50009064025800c910b1001c8264001d0702d4040e2111401c0c14280d4900d030040e01c0215551200401c520707803027880c0058155201c0c0c40d200703206940f100712403d041d1380241e40000010f0f031288a0010181d000b050100580c41c0120020031248104100300d000c1036004c0c1402501460080d9214800804a41c10202040707600c2041e060341ca05d00500000b00c550068015400002c003d0320001c603401d07003d040c00b54041ea405840d00404115081c1000c500304c124041c40c003003140500c00000506c1c3e107003405075403034000c240340b06152201ca60086440b581103008140c20300800070001c030b0300c42102010810640144080c68405445140c07500d0310000c0070f64481c066601507103418403130035400b01c060340304000c02c410642c00d84103442030300f404200640e01440420780d03040300d02c1c00c049408260200c03801c0c404e81d81070009a034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 321713983 1250 321712733 321712739
    0xb061005120c04091a030d2a060e0712140a05060a0c030b10030c141801050a021509060f0f040b06280b0a030e030c060a020702040e160603050601090e0f0402010306 72
    0x2094a01c117901141940198004070f10711480c00f0310034400b9403e0b29191030000300038220800c906a0103c41c260b40d00400440705d090702803000300e4025a140f01c8070f5038115410140d54035000000000c000c40c0a030380b4520b0f04100071803801c0001c680741d00466044402803002c1d0300d800c11501e006001c0c51000009042d23581c0405201c0c0c0e11a480c00054004041d103000599044220020301030b56400081d90101e03e00c1003005852001100300441c203920000e10b4041c1d1034400800c1d084c1c4c0b902860710000b0440506481c10040d044000080803841b0301082d080b0030031280c03515141c03c0149074054400510071441030000514608040010940b0f164218050fa035480006400a95070300a0350342003100e4001000440041841d01400750240411801000718500901d01c24110f44807400a0164210f50350001740340030035544d558104109120760301c4292130b48540d82c265001c1ca008010300c60a00482d0a040014a03c0e600520501c0121210110100d0b0310740ea5001c5000900030b0002c1049043c159262004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 321715233 1250 321713983 321713999
    0xb0606160b040318120309090f111c060603090812070207120f060b010206060604061101110a020105040c140d02040519090308040c0f1a0918130b061005120c04 70
    0x498041e9000e6115480101e00c003d60700501d051168018070b502d02c02c0340d82d9000009510241c11f104403041d920380007800b407800018000c058002c42e1180594550046019100c0035070104008210303425241080200c4e40d03880e02e040c2d040d42c11520010b0601141031207460305c3e20082c264070981c400e43d188103036584103855104800b8040880d0388107440804540081ea0304122a074402c5030f9078840240000c0c100c9107000c0000410130703c0750b40070341400c103c03d0030f149041202d000d41140440d05c01d42e054094950002100090081504503002d0b10075060720440054620303d2407400e2420100007a005d8929400c00c0c1d02400040c217000b8292a440380103129400b410074806100c0c82c5107040c802e82d6030140341e04150a11400e0001c0c05d4022011880c8941c60800184941080c04078200760139400c096140c141e00c02c00594100008035180d1200103510302040b03814000c010100c00c18502c1201c405405865400070303c4070400342005035101048080045001c007009141005a21422a00110380b0342500c075004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 321716483 1250 321715233 321715253
    0x10e010e0403261f1a03061908060f04060c0809030f0f0f070f0308090f06010306050403050c100e010e0c0603010603021b070b0a0305060102030a0e090c1e041707030b060616 76
    0xc003040404504c82003000e024030001104020800b01c421000b100704100800f040c1440042c0059119181041c0d5805d0210b0100c140e80004140002c140d07056841c0c5a036070340b489440e00b214100d800d685020a64001e10b4000d1803103038020000d030742c01035050108801344407405e03510a40e1040300d40602030285520003c4610018100c25201d4080c0380e0f4a201580342c058425000508108070030780116a12001e060800140c4034110307074104401080680781c50a00351454407446c060103005008290900c0048895600304400c01d041c01c8008100c01070392002c0342900c80d040e5285507a880002000100000740c400d401802461030100c440c106000c01c50001c9914007103070350b8000b00102c1d0b400314401a0094061203100d07071240081c0051498110301c01d00040c501d0b40819003039031240f240c81021590701600c01c0141d81c202e42100c584d910300f10080000900b4560014400d0403030740c02401050005129020481c40b080300d40c007018404194a400c01001495004103662107003001403840c034000480d6200c81 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 321717733 1250 321716483 321716491
    0x19020c030705061303081302040204030210030b120d091509120b190b060316110a0b01051314190b040603030e040f06051c060b04090b0708010e010e040326 68
    0x100841c1d44042501d0500c2c24850010402004550304000b102e01094121281950040642000038000000c900c00a0020701070307504042c6d000b080d620807510099070160b100d070069440440d6032211a045071503a0694800108ad417031b900007012803100700848020902809000d44043c02c044002a440724080c50200800d0103081d5410134815080c84010b418284202d0350132241008148000294240400c81a2101074600040c42004102214450303220704580789403402c50703c0540380c0d200710505003400024000c0c02880d00c10401e030720703250480c506207200d540f0151102140f078503015030740c4100b15010440001e2040c01c200f40c89030b4421445941d68070070000a1403007515031151030203421090100b02d4210310a2280d45624141c02480b442e80c0d08804007114410444d10110310b500b079850810701074541034103032a03001401d058074003003044003082170310303108040c00c0e03840c100503030782c3c2e10000161078400b84601e441401d2042c0200d00883c2c810f48189103035119a18100002c43c0c8104a09801481d04503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 321718983 1250 321717733 321717757
    0x11b09060f0e010c020108090a0b1003050105060f0d03140706330608060d0804090e013201120609150b031e0c0f0d060c020606091e0402091902 63
    0x9001032011a41120301d0440e003180600c1d02100d000d20940010340081c18841c400f0741882103580000f05428000c02005952540c403440c1d07582ca5040211003213031801c00c1070104683d20350a01000450300d04101c1980401c03860020f1001050501540302034030000c6200d000c8205003101004100c0205401e801b440303051003e03503c0c0c11159801c8404180040c0c3c40c404800c03144500b42d000c01040f010b5407105845030480d00072522024845014a4003505611459000b503c0190806c0390586504c42c040d0310496090030700c002810f503450b82100ba0a80e8265076021203e0030001c0c1d99006120640100a0b0720055600c15900050a091542c0b9242c500d02c601400c6403204a0300c824803408241020300c4242144007031040040b80030600c81242d0b913241c0ca42c59090074003074804003001c0c0c1019a80c1280c2500310b1500842c1c1002200700b001c50081d210103040310f02a000f140180c0108005c5906c141d4007904442c02c3e40030340f0036561195800c1148210020f4502d40e48140015510000203081d0b00c01041781c25404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 321720233 1250 321718983 321718997
    0x50f0a11220608060303030402150a2105090114040803370c180b1804090b04030f182102030309030f0718020c070603090224130f0501021509011b 64
    0x2016004244450007420b1500940047c4288001625080240301c0440101816030792280d04103c801c035814003500c00b0291003003d052200b107580b00c816501560080b14640006d02411154518110181c2710a07500100740301c400700f00260320703a411020300b0208548458800980035144280000d6110100c10040742c2d100d503210030740a034030b6030020403145c0c5c101c44021040500038070701142c0854900408401e020741200e144201c11640e550360780000c1c40c06500241503c0c0600301401d004003650b8003002100e0201e186101e10515481c2c00c5111001101c4590b2203a458201c240d09240020004162040341c141c80b0074040410f2a5405005032604031114000a00c800380c50311a02d00788034084140740081462041003240d84401002c10694140c80341c41c100840d54228900c040b841c0c802c0210080a420600c1c12904000b501c4204001c14030707080704c071f40012000340d02c850761070844507400d00c13880e80507a0008102c41c10540c42c088540e940111440f000280301d04071800750f031814901c40c5450100041e00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 321721483 1250 321720233 321720239
    0x6020304060b011215090b0a03290604090803070507060e0321130c050d03090801020d020309010c02060907120606090501031209080c0907111c110709050f0a1122 71
    0x80030340d280c00c1c20f00480301e041c0101d0343c41410072030101740c0d10700811040e652036821107003458440c0355142004643c0036400300c01c606078081100d42c44008006200084016031000700c1d20900e02030107000d010503000440c252039601c0302c00003558603500c040001c455040c2c644504461076281880604668600c805040c034800d0703040501e0032220403008000d00a002043d4859402041071000e402e026640c0950b02080d419020741415500c035401940302d500550300005440041001a4006d18022401d00009100c05403510078140d817902012100c18826601814040180100f0440c18410642c0100d4000034641d86451721581034074401d0700161a400740c800c014151440c0d000418174010f29018000e001c40c00c40100c0050341c4503c000c1e1000080240d18000480c40d00c80601c41c1243c00201d03116410030008410001410780d0040c4d8683c2d0806000301c010005464503140500c0307210b0b40c1d804003084510360340d403200d402c0149104582c64070840018441c5d070841c030034070002d0490039901c209903801881d46 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 321722733 1250 321721483 321721487
    0x308030a0b040e070605030403050c010204152d0f03020702120615030303070f0c021c24020c0309101701030605041b0509070e030c100c110a030c030602030705040306020304060b01 79
    0x41c0e2821954061403500e0701a002070b0902040e18816601d80b03180c420b03900e8641c0e080468072802041070318151940300040c0024452002c0303d4130318a200c2641c5a00d000c00041c0281f400703000d210f1145a038005641c144004044511a0b80d46203407a0000c0d0074018103000752034000c40c0f400841540815202e40c415428072644d4280e20104e031140150890041d461031400000042620a40078804424481d1540b004011552041c680710807107a001d031040d403040504c0d42450a80d43c00b007242d404003185c0c0d024283d0076052086001f02c0c1c1c0f0540d81040207501d440c81c0d50050080303a5408400170000c11079400101e8401c228007248413030007540640c0010545090505003401085115001441b0307010f03031884104507e0b00c408542c554003c0480c20080e80d801d20703460100c2d043c03002c404005548107518400700004150400e006215079070140390b50100702c1d0806810301400020310300000c0e001000c0c0c0f00d01000000c8550b00110342c00350640c549103081a03a03a5a440c400d980003030781c3c2111a41e0701e07821200d11a503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 321723983 1250 321722733 321722741
    0x30c2b030e04060f061202031905090a21020d120204170d030b01030c09090f0605120a0c05031b0909030d06180506030c010518040b0904060902150c0319020f070308030a 74
    0x8031300c036060000c40c1803602a010b0030250444507081402c58001c800141c00c20100020b01c02c40307030045502805140341001c1800c0d142c04000e64200d4110b040c2c0e85005a101210003620619003000c1d8005282c4080041c10a030359054132110401a803903002c00c008030302081c5040d9424210146607000b010940300c01c0700c000d400d651500e0820f40c10035152540c80b0641030380c405503020458088240c0094070700512a4500d0142240d908010b4000030380401950074003400241507501580a400c1c6402140c2e201c004042e118980d10506410302100300c03011900e1407410500c81c41d00030b544013084074070380505480c2c04030a580700382d030004a60f48010340e6822600b0303c50b4051180d000700d044002d0689442c40a00181041c0030351607201048003c03808240c01f80380c68552100c52514001400303540700d41b4280c50710201812001c081240942010403040391313030511410950b00151a05006507041c0b980051941a5099158850b6003c510a59021140040051000b94051409020748551341d01c1c000144106403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 321725233 1250 321723983 321723989
    0x714130c030c021c050301050f03030d0905160911030a0b011803030206010f1d0718031b0503150c1204020f0916031802010504180b061c06090902030c2b030e0406 71
    0xc4e501c500c1080c409560310004903815140202c03071101c258031081010030f1441c0115032140d24891700d0490322401303001b0300242c0c0d000030319003c62042011548550400090766441e82d28030f0030701725040c008030300b0484484d00401224101031502001000541c004115044032550043d00942c219000500a0b60f040b180014041c1c0180a030900105032810103484081000800034010016440f8010a031899070380c010303000a44d0030000125a41c1050361940b01c42c0b05031481018401e1003800788180c810920050203a00c9a44950f200b41e0a007180d805c1041001480100100c0e400b080c142401540d5554140015000f0100c003140c2d00200d44442c43c028007140c50b82590384014440391049080145c2c0d00c04102ca0079543c030410b49600030380d01c0d42c42a401a02040304e01e40d52040010800c3c04000c1d180c60301b103640751010404240702160366410f943d8101e80d00c441c0302941540250390010181c3c24202e00d02c010300207a17021403403c52082810404504021000101c0001d00d118042c0382c001d107090b01681c406 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 321726483 1250 321725233 321725263
    0xc030e010318020f012106090606020109080406121806050402040608210d1103090a1506140405041103030c1e060c070308090c150c0d110714130c030c02 67
    0x25400c19064010550b41c0440c0020300c034960081d110006a4801d08181c07211040e00c1c00b6911408000203003040191103103000d40c00c821031a180c80040c6040c414081c0390b803019042400145410700303101044601d0280c1c002d21005060700c0b114200c242440c4590b49100315030041d03000003200d040c5441000700380c036417a07131000c1103940c4056048040842203000641d804200469103d5841d4070040895020703009848031710340d0b461000300c02c0240c4240080364040c8564490f0001d1100c20300050503071400c4402a000303540e1200ca0315141a41241841e5000a8005002d0070035542c010106170b00003495035201081110450f00004500030300300b44003003018903d0401103805400d840c40c0648624075180962000502080207941c00b00d20b40c1d0303a040c00501c4070014040c020402c07034030140800342e082c4e51000b0004005441504002e9a04910030350301030107034140c000050312541d0310380860f10500c24400c001e01d590080c0344da0150f8900c00002e1041d001e1441d01601e0104182d9103144020f42000220718120304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 321727733 1250 321726483 321726491
    0x606170705010912050f01050c1306031a060702010203090307032d0b270d020109030f1e0806060d05130b06010c05071e0503060702010e06060f0a09091406070c030e0103 74
    0x7209a07003216000c000e554105202500c24141402c146280000110010000c0e5103020180001050700800510a411035080c2030030410359209403c80403607000003c8a084503581d01444030322031801000a0400c5401441200e041c2000380c80000d0800c441e951084901400030002c000c4420501c48400c284185240d99401070b18609840349011020005c0840d2002c031040800540c000e010032102012120b800b60454005150b03407940a402402c0c980c0013540825000355054688a1040c1424012580d1107003e000c0e054246040030b90305608042c041a074412001c2c071044899060900c1001d2086402e400b800d01410791605144071041d40c082c118604100d201d0785c070b0402040c00001d2110442c3c00c9401c5100c01c107240705135007050340750f440c0e0003031a4140101803d01001980c150800e5900056103000d413441a19048208080440032050441e0010403a0104101c2c2e05126440707514a41e000d526183c5801020f00d81e094240902240c2150204e888854584d003459848820300d180700b042820108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 321728983 1250 321727733 321727739
    0x2060a0c03092303160302010533192c0a110301030b070c020904080904050609190e030906040e090111030f01050f0103110a020f250b160f06061707 65
    0x1000c0409420702060b00c1c0c900c5060072180f80900b00300701c803c019100c0d0800c0789507100c0c92030024080c15040d21f59030710f1031076000092141003c0d0300d0030384c00004100da00118008030705078060201440080681e2289006040710001e6021018200600c000c542c201d400341314aa6144403540040d100542100e40e018503101e01300c01c404646d8012039042d260030a505010b13940e01d00c00d080754440008130009411480740001c1c0400c10089002030f207160035080b9000e1029a44070018000c00000840700d140040b0094a0794410f03c1c411540010f1002c00c403a015a440c04021101081c425130203036102c6510701c0001d1042080605003803140d0110302c51608000b80c9941031000141d900c4e040103002d081d01c2020507035030f203481c103038000d9121350a1441d81a018944810010700040d403100645c2007405654003951801100114400c1540b05010101e00c40e40c00703143e800c1c035209a00070b4014100c40c07191000104880e102040c00c080039654114442c2001142880c202816103a40c42c18a505141041d070182c0c03014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 321730233 1250 321728983 321728993
    0x50f0103031b05070f031101020d0519030e03030403080403121b14090d0b0907060503040b0103030e061b031c020a0903081e13050414100501050f1902060a0c0309 71
    0x116046a401d490441e040c1c1500c6a60a1849448402d00030024440c1c03c10020b50f20f10348441003021a401101035407900d805040040e61204140c1c00e41e8030001c2c138204550320b0030444e03183c841340d1a944945800078084144060003465070f4800c3e6000d8000c80c0e800d10402040540c02041d0000c0b00340115814410001c1803003c029840d9000c08180701030001070318000c01c105100f107003039800035040180724900c50802c80c24151040c0f4026a01e01c0c0046c0140740000c100c2d01d0189088901035940660298080c1e07185407812102d0040e18415664461000c0100b0f82102c44a5410741c200402a00007860381c03455032840340c0d00d02c112502c2182000c0c50041c0040f41d42c96030440d1400d02102d8100c4011a03031a0400099101091004104008001c03804155001015544110b540136030380c05171020130000707060803840c0b801413204503003103804012001c0040c002944144082c01c8140b4030320040609014050008250030720024810100690000301003004010700e500913101400451304041081c0040d50f107603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 321731483 1250 321730233 321730261
    0x17100e33040206180402070c060905010c0b0105060309120f0918040201020a030e15040801020d0501050a03020d0f060b091e06090c18030304051203040f0f15080601021c0903020a080105 81
    0x203403043c28007003643c00d5890f0407003e80551200008100315030704c0c001890700300d0042c0c0b0359004101c0010f4054001150650143c058945180e42054600c211a0302c1e042c20031070f10703610040500c4503078080c10950807039100000c0068843e4240c510714403500c07005001c05000240c190780c1c500d5980104e46005000c00750f40c0104000301a81d4051a11400d01c01c074240c082088450801102034001074001000100d120041d400b4000c00704030148103000599888080041501c8240030181d4041509000304d80001c1b800e030080d2460a00c00c01d000f09050b401040082e681c050701300c034a045001e5801c014061680001080b01780d000c3c800701c0f6200407034201155070003031078094102e041e48800600d120082a580c0c082041d90001d000040c0303c92074512007000415141d400a00c00e10b070056221102c007082c404903800c42e18082d2854101c0f10345e40c00c0302c010021501001c010300b5240c1940210a070741d564481d0241c202506140c0d0544464940c50700e18414481d01031001c2c0d20110b0035034501401d03c00c2c07016118030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 321732733 1250 321731483 321731491
    0x90f062102030c030607050c01110901140715050a05090606150406140c0a05010209030601120305030609070302070209010902210f04140708030c0d140a080117100e33 73
    0x3000410020326480030900e08140b50614503030620038102041210f036417202c018020b101c9071000034006480300706120115802001c1560717010071849606206000d6072080600700550140241810310407008125404503001920301503081e0752100d0801500e81c10130403104d81c200c1c07c21350300c040301c8600441c980100b074043d03401000c0c2008254280d9044000c8201e0664490080300710035207202c40c0071841e00074000d522804000303011340600740001444040a916416001e60141c40703103861582c0c0c400c10050460002440381c1c09040d030a108200c05030300e64001c158048c000340e401c0141e0310a082141c1d0740c1c01c81200300c41c8400803508032040140911032201103a8205034061140038214a031041a0780c142b87c0c0390b8101c0000c611001c2071403800c021000410740703c0f952954071148800711002c0100301a61143c00350b140c0100d05a10010040f002000c085025008040e205464603217a0701101642030710061940d01070581e01c001d65003600040200c0c802c0c1c0d10303e40c403e5200c000c030842d24159050b040200070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 321733983 1250 321732733 321732779
    0x1704030504360b0102030721031103010605071704031406010918020310090609080304211d01080402032503110901032409060926031902090a030615090f06 68
    0x4020f0071a81c0d008005842c200c07603104022402000b10580c0c20200100c140c1d101100280c10501c0c1e0040c242c8603c800c49058034842c0c2c1c0c0d41441d04065807034002484a5503250b1012020342000000082045400302da040c02107400c02030b100d594506002d010903145a40d56200c02130f0b08010130b4600581e4001003114100100311b4020811103c0fa023401c000900008001401580c0008100420000d09900c425991b9408080c200c591810112003100c0c00018002e1155a16196031600e0307101c2e40c01303040d1840c1d100c2c1c8010110b4041203140341e10000900d0300e494520700c5820300050248200100710800051812060b82c8006056145481e00b5012103108688050500c040f070640e0420542503800407240c2e1904654140400350241ca4010605d041f60001c0c02510381044c0100030350900d044003243d0195561110200381078010340000b100030b5100b4031880e40e100c59401c4000000a005008042c845625802694060351600d5040c1302591200484041140c1c07611100b07011000039500d1b0045515441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 321735233 1250 321733983 321733991
    0x5070308073e1306030803012601110306091306020408010204141905010f050708030412030509010b0906012006010e010f080d020607052b1d01050903041203170403050436 75
    0x24202009104940000e03001506c0080046107448110040565030b5644040b40c001680000c4222400c07170b4100307802c00142d001c04001003071842c5000d000c41d40c0c00030140d45c3c00c60280306107a912241241e001e58410600791b5000301e000c01c08024290000550000c050301e00081c203401d141490303c001101d50185074103006030380100c14403d500c02d00035a0a91a4000d070340301c1d070740d09060030300c18208a0075240110000f0b0030080010a00d12040c0038807211030001520710101c81c1c42d040c00649150340c52504030790790700c001f0000280c0c5c010410001d543c003e050302b018070281541481d280e25880ca0300c80d0003200e00c1d603120302d0348071900d2036001400c1507010780e0f075190298072507104515101180e0f5054800520300a00640e102500281a6216101c0885030443c0d100c40c00c1c0c000701c07129080e900d040381e400407983c0003400704001138482c006803000e240e0311910b800d00c003a81803040869940d0405490036800160041824084902820103100000011202d551202c104200d00c0181016220108041454032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 321736483 1250 321735233 321735259
    0xb040b03010303110f0106030f06110c0a0221011a0108131511160b07080112020303031501110f070e0106030b0f010c0309050d030309050c090106080f0405070308073e 73
    0x45c401d000070070744900000d000681c3c2c0d0341414a011001d002003522403901e000449400fa0a49004540107069000060000c505542c1c0802032140700700240b2a0501030b14410715204580c00788260840d6554000c020091210303004001070206038003c046080c10b141c1d009900022455003100b507401000c2446000c140d46040c4164410b15016907100301c1c071a409046a41420065840c00c006d10482d900c1d91080c1041c0e9a44401040c05045020065019082000410701c00010382d40d00100340c0006040181448209000c03062030103075204001881900100702c18054007508081d1503004064902c2c1c1848500da100e000500d12a9200c0c150b2814001d200c000c0340c041501680000008140040401c0c06114003410301501402035003200f00c845000700c0d4040081703850a07000303440c1038610943d00c00000740c0e00c074856a0020100503000b911640700b1404c4c00000101d00100a2070524400c10b0a010aa05ca02d50001c00c41d410518a0307400134880b00c032541c21200c003a001141d078904422104407042d441 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 321737733 1250 321736483 321736517
    0xe0402030a0f05030a081f14060405030a0302034909051905070e040302150910020a0e1206060f0d08041a0417060f010302090411030d09060201060b040b03010303 71
    0xd80079000824050300c11000505204010000d07001c8081d140c1c8600d42c080d41d44901c0703002d86058014000402080c1c4075000d22140040d0200040c20400c0644124a030588440002c0d18141d40f0150440042c2d000090031119560b80070203120603004001c0c00386008140c0803400c280214901107080802c00314052015040700c03080d030060b0400e00e4000003640c0c1480c00350245289100e903410410398041c4031700140042c0020361003000c680315a401d80d01400a82c2c11028403401d02c0c87c806810b80c5854450040350181d42d00240c40140580a1981c4500069441030f0307042c01003186407901c5599154000004000391a01c4020304400b1404041f1100310300ca0141c1d107881c2c0e18901a0703400415440f9101422807840804030700c0204141e50b10401080900305c66003d605a480f01c04079109514074201e4001080182004c420312500207119060820195070301401091500c1c0001c1c02400000d9618403081054607028801d000c0900101101d0701d1034a420040a10045d1106200c003d04002100640c02480c10b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 321738983 1250 321737733 321737743
    0xe01060503152a120a06060f090e0f040f170307171009020901030f0e160f06020c04021e03070801140303120412030b060309010f0c0c050c040f0b1305041505040c0e040203 75
    0x5131042001c49031801d00080c00d000802c034901030714010031031003003150010901070b580e0701c4200d0742c02603041c075983d40c0c0d01c800c404400c1801034001c4030281e450646d1500003c15450358903074045035003490740b80c0724605541d000345400b0380302403820035803140032040c0b000034065203007100c0c26244d0008000d42c3c0c44110302c0040b0014241030110f6051545400b000f602c503036101250500104941c420b4401b1940e841e900c001941401c1d610400000d40d21840f001402414a5000b03010054840001c514150a06040c0c110060340104c90650028842c100103108a1854a100142c0b40380258000c0d410004901e5180364040c2014002602e85102109c1c865072451003900000401d00c0060702d0f154581c10319001c40e81c01b03031840300000e001840c14403002e210760b2480392160402468100c40107148c810044000d110060285d41c584a203a04d840c2c1a15195a88410003801000354030040002240d20381820800400d640c0107904010751810b00c03040c40042a944086941034840d540c064540e65142d61001910b01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 321740233 1250 321738983 321738997
    0x6090c090108310f0213180f0201200a02040c020706050a05070212010e1507030903050a080411120c19050a0317070605070e010f020706050a0e04020405040e01060503152a 75
    0x400f120700160b00f04030f07480c4500c0300360500c00d40c0c02030000d074081301d0440140e036a0030000e040580c110301d90a001047c1c15801030610b013801810050190b094441100207941d00c8502480115400300306401e045044c544505142c200c2a0300c003402911f802c003403004020784254000d050420102260800c195524000011074a41c012402000300c1d0b103e18120b0ba80340e114200a0242428a09001400f91800390288158036030b4503a0f50140f03010401402030301c03404805002070300c2d0300c0c1150300b143d00740e0344401c0c41080f243c1030f264008080350007511007000442c08601c40700c0b1018000b4414104881d843d00c05140e070a580d8803880c0b041042250042e406100d00905001828080c00e2106021601d0780001100c8240c20082c1d84042c0340244028007613135a22820312034a00042c07010480c80016510a000303640b00440011b20251800d0764400001c2d0684850410f60007169644100400140c42d0401817000c0300300110403502d0491a00d40c1c1c0c40d0b4074179400001c840f81c440e00e00000181400b01007004503501c2c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 321741483 1250 321740233 321740311
    0xf030f020301082a030a0b130b101a1903091a0403051812120c070f081c0c0512030a02210901060512071202031507030506090c090108 59
    0x30780d80d540c0d82056480040e601007581080303034580c916904402c0304002000c2000003500070001d0243e1680d035600d044e41d005041081020f42c074043c00f400520103064050248000c503618040d0300d8100700e290351000250100060142d0010070440300309501481d1300386500f041600340000c0040d4141000180300198180b140c245a0401081004250b0000b004e400c00d81d4030f605034038401c0c2c110002030100713001244064401c2680600442c1c4411646403008007043c0510340c00359142180d80d0f0501d5181345e4603540054140fa0410f82d1440d0305901c1c0c800911412508910300111101c0c100d0300d0745a00c039400c0384810052180c00000094280d180f540449a03028100302e0340b0007026400c131001181003002603c0c02c6031154246800021149003840462061030fa201002e0810b991412039669032120901600b280c140c01a66044030980700000c1d11948603c4241c1c0b0003181e58507200e01041050580144a803985c03401c240700940c40350360310149544e480782410010224001c0082104007100b684240c51941c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 321742733 1250 321741483 321741487
    0x20a141509060a110c0307060b040b030102040b251a04050c0901030f060b011404050f120a030908160303051209070305010c0f1704050307080a0e03010f0c110f0304060f030f02 77
    0x40c1074400103207240c42042003c0d8100502e101d04000c030f502500c0307040c10020301e503441404188007140140c2d02c81c141081004000041200b0b00002003403d83c3c01a07800100004004240d58601110441c01c2c40c5103070000050314a00e00c01c85558101515822070203031111a80c100d40050704104041088182925008011982c1076035241341c81058896080f41c00c8402509080016145500902c000541c3d00d038100f0543d4106800c0130140005101c02e82e0245500140307040c0302036800d02041c00791440c818001d548503041a410417501c607141c8035004084902c240c6050b003082010981c00020740e00c1c02002c903603000781252215011035141400541010b4001c2d40381100c0c104c50789070002800d560841582c1c03a400440a111000c9503403000b002c4502401c40d80042083c04001060100201100070560600c1081c207001d140c042421158841c0080c5040c44e0b8901141d60300c035422060004d100c1a855001b0240ca82d85c00701c1f0b15072a40100d2141d01d042c05200e0340e241080c107029422502010041f908119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 321743983 1250 321742733 321742741
    0x605010e13030f090e0c04030327050609010201021204061d1b0603070e1002030315030a1716060f0212090109020a05300309090c0408060f0703090503030a1a10020a1415 74
    0x58647c042d200460200d030681041c0c501c800040c10034944110000003001110610700800e0010951145103454119582000750b0302c9910109400309000d94044e40000800010442c40480d001900d43c100360001d5015008100d1203104481c00c4610240d4141c0380c042d103d456000c0c0c1074408203030a240b12548069401c20280080740e0000155203d8140040420000361818023070580f68100450013401200f4040b20b00320310803082c00003d02c1c0e0910f00000c00804200705440709800c86000e40c036041e000f01d0b00001d0b10030348101480740340c581141c120300003084a04966400a0030104440c842c0f640078200107545440301890000e045184003074079910009081c02d02e158202d0f100d500c80c00c02d65100301c00c420042101c20030260252400d4540040c01801c0e00c0c1c840300310940242c40300030126010581ca8a84e5100041c1e01031000c0d600440c80c1300e201142041c41c0805248402004600b0140a00440300b00d030b8120fa80d0006200d402d95030840120719140c1450a1a94104200c2008107221131007120180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 321745233 1250 321743983 321744001
    0xc03060504061e1109040e1c09080c01031a0906010210090c080607050c0d1d1f030c08100605030c0c0706020703030207120b15120106120605010e13030f090e 69
    0x79582d80c0303024140c182124143c4484000481e8074110203c03650940c01d000410702e5081550202c0d12074040701c002c690b481d11000100c00e0488000452030000540c54120030041044204050a5030380b0090905200c84645019098101d941c5115801d01c0391a40d8000f01d4482d900070300a0012810300c0d00c209000315481c50805070603080581c0f042e00c24030311942c5c00086815100350251907140c1c080c80050301c800005044110740290000034920300d07034005541c500e00707241e80c1c10b07400408216950009130b6101c0b002d000c002c1c044031101d8804000340581030301002003140361448804107946103410016221b4550740c2100b9002d004002910390184100e40c4003003101c40d0009019012a8426400c413802d19894501c1620032000c00c420003492a482400400d949846055404100b01005882c2c041c41d00d07021210b245c2914001d9012001181034041e41000b80b12442c0680c0307016243d10401c1d103c00b0b003414030030030910751143e450140c104000c090514000d107210303d914200401200003810001d0400f03c5038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 321746483 1250 321745233 321745241
    0x1b060a0902090f040209160311160b06100f0c0c0e010b0306120309210a0c1401032003040210110706050a0e030a0201080f19020f03070e091603090c0306050406 70
    0x81c0e01c02c052420014050369503051010340310355405050304c0b840c0d0b20703156100c4110949010062041c135031640b044510b080c4034100a0202006039070040c02c0e16141038101050f8008018200b14008c1907101219010300d0b0b00035000100d00080c918185508124500b04106a01d084c0e8219000c03484410000090708401c01c03000e14010b007411203400c0400154040229a244500c1c21015049405030042c1c980e2080480504c001d007400410540c0c0f00c51000382e41d4203184910940109006600c0c203205039085503410301c5810f03000045003007101038200c0341c10601d5569000c020802131240d908000342c181e14500c203511034000e0007913640494690b19141da0000d00140c106400a4001600580d0203011f6807800250460f40c9940686821240da120b2440300001500000c0c800540c2c40b0541501e5007201d1420f1004002d85a51400c4490302d81c07c00e1030005200700c0070203011521540110090088035540010314a6140a46040000b00d050144c40c0051961050354000303084140f9180401043c000d41e504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 321747733 1250 321746483 321746501
    0x20105030a022203170a2f010f090303231918030c05160e0f040809030a1a0106051201060f0219060c0e12030d0509010605090c07030306140f04021b060a 67
    0x61a80071031520038074080601e0284002c5031b00002d294480e4072005e0b41021168000e91f01240800c0890051510211401e40f900703880540310715680c40310348605256243c8079075182080f0003810401001d400c0c58240e21480c101a00301c00310003404101c940007001e00d0b548080c004c0c04a01600141d001c81500300074101d101d0460003524a4028000c090058000c16010081a41e100d050441c255440b091840590803400900440c0d2440c0304019003049681c00b041004615881480c0c0205401c826006038040884180d006c041403090501034007003200740d020403860540e422031909001d0007120540491401c43c820024590503003402d00c43c002400101d40140b0110044d684450b21942900300500c80100900c1620744c1c1160824040300c030a001168000c4c60304034824000110745a0b4651001900340c2030240c415403d00c900001c0c90004068050281da401411010f000c0030a8030040800b189101c5480c0d105140b180d640040c0540c29103103600c1282800f841c100084420074a000000b84005042c001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 321748983 1250 321747733 321747743
    0x2061006020d05070609020325050109140306040330060608060102120d0b010e1002030304020102060a0b09010b0a05190e0a05030313090203100e04060b10030b0904020105030a022203 80
    0x6002095041c00007840c0a14601c00307580395490514152142c1000700641a0200e91502a90741c40c0da403403000040c4590300442c0400d40651820b86000300141600426500c104031a1440c000003610b2560701044903940185c160a10115810a2144514500410b4070403044451a2001600034403142988084259201911400c0140d1901001a0fa07105040c07107603540203440807c0783d407180d038103150400741d181398060528120b00c603000710000c5c03091034644080800580c40802003000b55a0b0401c401d07504039200544c01c00140e203110340401c0840c4014040c500541c07000180e00c0302c400d032140b0120348241114001010003841d01400c000c2c080000000c05922515503002d000c101850301008460000d8461504104e0447c41e24681d00d0194000500d80c0c3c1155000307110003d19a0354441d0b0091140f40708440c00222600020104070200441e900c001c020145054144407158551642464100346c0900b001901c13542d80000030006031007040800c1c501030154880f4802c007099203c1105d41524819 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 321750233 1250 321748983 321749011
    0x180b130207030c0606051f0f030e03041706012408181b091806151c030503100e070813141b040c081003080729040c0e0106121503050d0206 61
    0x10b242080003113402e00c02e480311080132071f000c10307101c8a025034064204100d8a042c00700f81411140e1541c1c3c01c41c1c00940c8a11100e40130a0b09012451000303002c15400741c8641901c81c000a801003650030380580041c0480c0060103100000b04d40b01c040c00d1050003105503021003c40d1544c841c1c00c0115182c00520803481c40c082e9000f500400c1d00300c541103100d00300e2411003000812195688c01007501e9185c210300a0960441000d00ea000060050810701d00f5100e4082d464550b074a0070044192114518107074041c0d43c92040b9107052181c0303150701c048402d4000500131096200303848981480d00718240000003a01092280506103940c808a0401c03080502d001210200020210104140d1343c03000100d4180d001d20b003103501e041c000104458050004a4010780b64054070303002e490401104903085182e0144109541d4003000104000c405001c4083c014480d920700807940360072800742c035941d1140c4101d10390b1074491090050307041350082d144004540001c22200c1603c2d40c003070301a40740e00f41a5000d44a00c281c0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 321751483 1250 321750233 321750239
    0xf050d11060601050d05040212010501060801080d0216060c021206090c090903090a050909030d020a09090b0415050607060908040605030712090506010302060f0903010507030605040e0106180b130207030c0606 91
    0x3020505501c07508040e16076601e0914000c00d0032004141c02441244e03c40302c0400c114a080000b441814060001520744039059410028007515103054401d2a000b1075021442c141e01d21109015114110740312800c0845c20f80c2da00340f0004190049a007030080031403055400b0008501030015900e04485020345038481c0c681c44000c4230b035413640314890b02c0382d4006c800302e48100641c0c148041c1203503000f01e00c1019282403c01d048404010390b84040072001c0090b01e80c88051280001c1e901c100e608500d000ca8042003013541c03200c0d5000d100380803481101d110f078602250110601c40c058101c07140d40c6a10150341e40c0d9031a140c2c0405032154009480120000303281216000d91400a4454a030034140c01c0300040155a18542c00c0000079400f11411103220315007400365411a40b400d006143c0206226280400c03503a0500c01131104942e032908a12001c0d80c18200c042203001c110842c0301c0c03030b1034030390404c00f0494254440101c0c10200c039007078084900f82e1000402400f4544d0103122409118400c94090184a2b5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 321752733 1250 321751483 321751517
    0xd02010b0f0d02030d0507031e0c030e06030403140a0512010312030b030f060105040207061d0a05010c05160f0303020c030a0903020406140f0405100803040306020711060418020d090f050d 82
    0x1540c02c070000d415620014500888a02540181850a05c6440d1007900c20760b0030b2002c04440e0081201c0b54000c909049603010400d070300403130783c0c9032b040509442d0039040d45450744009000072001c8254402d0010300280b28030300d140c450f07030464400c400d81c454510120b580d2440c0c03000c4064009050500000c0c40c1c40c10800680c580401c110110f0342000b401012941d00b000c1c00c04c8000c0d0f1205008072401592400442101c02c1e14990006c102c094050103020070721450704180e4207640150180340f0401004120401195040c01d100f0b900ccc880d0006007100340e560042c07405400031302c110700d0103680c0c42c4400314072402d045600c00000c0c01568401d9905003c0310b030b90f42c580c2d881b00200440c007555005000050900c00c9003080e521140d40010324014100050790b0314842681503034895002500ca0540000d4514284001c0080c40e203110017041d28400c1c61f02d8500460186428414120350070015000030740c0030b042d40035640000c0600c2d508400401c000c08c580385002995207902c0b24050000c00c14007142050040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 321753983 1250 321752733 321752749
    0x70804111f170711101a120c030d0f2124030317010b0403022e1d0a0b030412020c0907050d0c0c0206041418090307021c03050f0306010309050d02010b0f 67
    0x300003500410000130b031445010046c0c00a80440303c3c501c103d9801105099440504584260f0413a1f805080c8900ba1a401e242c1444000110041804403058884400300d91000311000101c5c0400840d10708810030600b940050711828688081c103c401c941241540d60200300c000048900c00d45600b0b14102c083e006030091244240f1450300c102c04140010000760601c130803500c410303d03907100f508002d001044080581e140c811202400001e2108490a1420b10818115424815044652407080d51400504031070701d100042006000c0e00d8181c2000305100d000300308038404c941e00201513060354908100003d00d250450030b84040300c0703800c0c5021400f00e140182800801540c01500c6549800d040c80c00211002c0803a0b508560411a04500c803440d0b4a00404c5141c020a0050003666a607251401041a50f02222034208000300900729040d00080d040b1302256000b800050413680c8958034100142e006241c6040702034028000d5400c4035a2559043d406443c0c084011292120141c42d00c9041c0300c520303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 321755233 1250 321753983 321754007
    0x20706060e160f080a1b020c040f09050309100c0c12060f0b01020a033e010e0714130b12010e06150f06030c1c02030103020109050405070804111f1707 66
    0x10800343c8440801041c410b4106941c45410003c0100702d0700380514000181030b124075004c20043c4c110b88105036681c41d050090b04038001e1000d03800d120210003601d5503a00d03131041910345d511036407485a444600601a0000c000c0160f000100706840c3c990782c01da140c12205900c04226040380c60203007120031f4604203104404111707106034010a035030300446c5e5080e07400e0441107044542ca0440d43c1805400030080141c00c034040c0321800140020b95502c0d80c003040c207551f080210300320150030000050150400035000b1840b0142c0c100e461078121442e1484003002090b0307003030045802284034030020750b034070905420005402d4a0401102c030141e445401c041704880500d00440d50001240d0217001c180c0c90240301564001900c0b01c4410715200318944100f581c0781000e4081c500c000c0e0040010015503030421042002040c3c1900c040c0203500d48190014403841307005000a001031005010002c0a0316054078600c0fa290313412400214441012102805006210904d0a0b04401070000074610340e1003140700e0307524 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 321756483 1250 321755233 321755237
    0x5060f04031b031e02010603020f10050a031109040603140f010b01050a0c08040503011503060e0601060915020c04021326070e0a020c100504050607030902060301170c04020706060e16 80
    0x6110400502019510103520b800d90030400010100300383c5014404019099a040c2c1d000050b145166106000300100d60354030440c03045c0d9401c50020102c941200440345400f446280000740c80701c02807202d40301d500230f500044e40c00a14002d0701004006160079450380520101045030343c000440480d803801c1c2d80c0320400e481d0029070240400c0b02c01900803080000543d10621150b400d2540790720101c2c0c00c40d041c4505c140c107244004c00303081061024920031801d6503003d01c00034102942c145803001c3e12500d07040c460440d0300d0005d003810b80e90300c0d4401d210740c80303070114001c00940d90361080e10301c004441030241c001c00c48141c4e06100f4204440c4509448015000c102c9005012100d03c0c00110440c042002407404414680820034140360715010320907950b0b013039410200001caa00f40b41c1003d43c80c200d80240940c05140c075200783c1c00090380d01c100070b40f41102e140d000c40051000300080c0d40c83c1130207880c50b085900140003080300c0003004070581100e0306560804004a400f5a5001e0202d491200c00a0800f00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 321757733 1250 321756483 321756497
    0x25030212070b22080a030f1707090b1c140603070503011404020402090a0803030a05010e0708090703020907090b030c0405030c15030f040c08030a09060207080f060c0a17010b030405060f0403 83
    0x140070b200d03580e400224a00c00c420f08020066a40e6100b41c240a4911822000200c080f0741814100343c101e06806401c070750498172140903151200010f440d255082c003c801c01c1490100700001c00c01c5e02002c101c90090349001080c080e041555241031007558083e40d00c1345c400d001d044008149414148a4140100c10f690208003060f2559000c1c04025440070003040d4000303401d032001140509080000751f002d00c2c3d40c0000002c0e55031501440c1c842402019000400f0044414240483c50000190410030b507901240e10300c603075449000050358031940c00c1e8005c104540c4040200100840c41101400841d84141c3c1554908002e0300c0c100700b0340440c0c0c0341c4000142c000c244040b4140c80350708540341c3c0c2c1c03040c4541800541c0f26101d000892654014009032000220124018481c0c103074180b10410041103034034001d00d400d90300440440d071144002001815030480c04100d20018510030041c1d9204415030410000075075848110741900c40d40215000e81e0b05210300c0d0041400c802e02c10503224400c0740c050381d030aa = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 321758983 1250 321757733 321757747
    0x20a0c050d080906040602030901030605010f17090c0a06120609020f0d0b060426070510120e031303030906020c190b030403020115120c05030109032025030212070b 72
    0x712120030800341c16100e4240601941c2c1207a12100014405024031360015621600740e84001001d540035a0069410080043c1004000300d4100a20000071480003008180598842102724a44920070795001d520580e000c40c0020810b800c03000034a0680f80e5501c09118140d240c5580e007090348558810103001da00c08000030158409107a00c074411040000341031030702e0541d03038403051000b0001101440311040400c0d80d8815844e13034108079a000920003510a035004075099040648540c0e9201080022280c035115171109021003802100c022a080c0c1203020303080c94407800c0040c0b2151182c018079024bc414140c40f2461498103100c401d980700034041480b14a981403c91100e150380001c0d0003141503640f241603808080c00040b443c4c00280409110829000c0041d0400f4685050300b54010390103039240c00c0ac40c00c00700c0d510000150b00d48842640b141c00e482406101ca0b854843d20b074510200f0704110110710401c40600903085011a4005c03590540303459145010325807903907410300c60507805640402c025 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 321760233 1250 321758983 321758989
    0x90a0b03030f070c0e0c0d0c03050f0c1e07140d0203040b0f0a0c06050123040e03090f0105040e01090218010203121b070c090504050618150604090816030906020a0c05 73
    0x10000ba610130b800d00f6900795640d5184001d14034007a02e59440341800482c801404489520400c100950395103401e00203070034050b6000e030101e1300140042030701c0380c400200028560390740d480700311075a40c481000c103503500038604040070801c16502510310329026550300e1310542031000060b10161121020a02d240105003d2200c24580c81950000306001c561000000800e900d8410709009081944032240080b9103120300e0010450003130401e41c411481c00051140100d4004141c44007031905071104081030350381c9030040c5c9450155a011001400d80c581c00403130715228a401401c0c1400d11072040e151820303407070070040ea124011070b001c000b200264180060b403481886031015a071481c0c0e80c0441403422040f9101c12400030003640001c00d00540ba44280030802c403042007440d0b800702c40d1034400020600000c030b41985400c96202154200c0700c160011980d166159405416400d60114225558000c1e04089140003200140240e01242c076a043c006181400446c001c22546e9202c0d00c1d011116041800b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 321761483 1250 321760233 321760237
    0x2070c09091a191a04020703110f150604090c0e10090c090e0415200705060106050f04032a08010c0206240607060905060f0a0f09020d0f1407060e090a0b03030f 70
    0x15501c0b14044e501034002950310340c1e03c001c0000f00d0281e074a00d040790407501151850142005143c8900d54000b23076141c0c0203401c0301d000701a0040000c660200303641c541c50030503030002030094114925001400c018418542c1c80c00001c4000c40c0c10601c401d21000d21480340c00d0710080e00601c594251000c202c0300080c00075030307841903c0e21030164441c00001c42185410074901d040c16a4441016441c20014070f0b5018845c04100080c0148280c0c9171083ca402080d6028100c03d0040d84070003090318901002080d20300102400008100c0312030b00c100400c0716901e00714607004e0302000c0301e0680940074000100d5140503982c0120104001025040c207400e0340d584091000b01e40c0048815a0a56610501d410011340c007401510700505000f02106001d00305101c000d0221440e0381640d0702c40e40c2c5800410710050300d651560f039036995080b206108041c0b4640c105030b081da050184085145016103003000c074102e500042c07110410314081d0b840c084142d641011543c00c895114521591641c0148581402e054003100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 321762589 1106 321761483 321761501
    0xb1303020f06091f0605060f07020112050c0a0f050708070c0f080102120103120516060623210f030313060b01050310090b030102070c09091a19 63
    0x107507184d841c03c0040800e0804203405a66070100401c42d070000e8002e28001e0500d40c2d0350301050345c1e41d18007640a0641203010420811980851040600c541c500c5400b403d00307102d152207000c0c0425035001c100b0400500402c18100038840001d003005021340b0a86200e1109003210508080741102150415040f14200e68810b010301850100c03446034443c110381e08a420080201c81240d0100d640d0710403d04c0c4c05606c107c007035051604000069002c4411512681000e50001c0300141c9801c4142c180b8880003540000d0801590244d2011608003010a40c0210100d40d0300b40c1170700b00a2425034000301c0302141e844400709280020300182c1d000c0e41845801c2468020300d180fa094401c4202d800d0b1500a09004c2592103c0200032a00d096048800b001d410a4415200700e079540a101e028003010001210600b00340b0b61070b40d0401d0f0030304092a0140b0586082c041030503001d0b21102c40144501c40c = true := by decide +kernel

theorem cover : BRFrame.Cov 321582733 321762589 := by
  have h0 := BRFrame.cov_init 321582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 321582733 ≤ n) (h2 : n < 321762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
