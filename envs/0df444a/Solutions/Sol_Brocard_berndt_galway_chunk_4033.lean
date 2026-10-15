-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:53.59898+00:00
-- url     : https://prove2.me/submissions/de2c0743-8490-4f44-b1e5-f893411871ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 725179856 ≤ n < 725359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 725181106 1250 725179856 725179891
    0xd06020714060a1401080f0d05070609050102040b1c06050328170921030405010c03050c070311040b04020f03040b1b0f03010608160909020d02040f0f140303030915 72
    0x75240140a03200c42545944540541e01c010304858615801000e02d10020440207080c1c512250b100d07840c1003030640400000040b04010b21001e50440038416a205008540c1d0302e941c3e820410b0140c0100d0448400b4a07540641d081160b040c90140e00309071a4000d02416100c4041201c0b1024400c0030b602030382949011401c1e25010502c60210840d005da060040960f49020740c00400c4150742c038041301c204501e44901c0709001e42000c0003042e076050b5282800c00382d00c42d01070360406513140e002d80500a8820f00c100311011040046094115603002000c1c0d0341403141c54620800c02003a805a004c2c4902c5841c014000103002c90b440b1314880307800031802030410120701d0b0000c1101103150b00400980900712000401040481e03030080b5040e80c170001071410b00c841c0e030080510082500324188964600d0a801191514a88280d075049800400c000001400d50310b680313646000014501380300f04070314100c4480b64041b450030040226480385030448050000302c400410f201905d80b101904180144060188 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 725182356 1250 725181106 725181143
    0x6190f020706020a0e10170612010c0c03120606050f0912060405150a0509031b01020d0e150603010b090103060e010f0221070f0c0816080403030c0c0b07020d060207 72
    0x40c507000e07008000242e43c540503064003400f919003200c9040e000350790394200720300d016a000a84580c40c0629905924803500c9210019070b0401ea002a08a215440c064840f00c0707040e0000f4010007218404e0301c50a030b02040d40802002128514450350020650030450341d250605144010801e4032001460020b442100c0490070b460b20004641c2214582e110180340340f050f00f104e2200603446001d100b0184801e01d0406e014a842c3e010300780d4850a1031449214090a20300d080d0191078901103030036410003c0b41150401c0940c0c94031210140078100729600c000c40c5450034103005070015208003600e000503c2c0d1950b61044c005003501004601d540d565000c041d0b845c07020a000410380040750062510a4200380c1c0c29a51646001030899014415034030315200d00d1980080c4d2079141207030800c0710799407030b41d95010380d00c0410081640000e004010014003c0201030b00007400d08a00c80c00b40d0080100c407038640741d015509114601c0007960140c005000c5100248694004020380c034410751119000a200c0700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 725183606 1250 725182356 725182361
    0x6120917030c13090504020f0d05070503120714010b0306180c0d0309151e0c0201031104030302060f01090203040c15210e0c010e0a1403070e31020306190f 68
    0x407070b01c51808400140b80c079003120200500703034054012443c1c00c220509256000443c0c480d00843d0042c003031085040c0e50418410305004010080c0009410346045440b006e542000e00d6005a00413103420091003001c0190990501c42c03602400c401030014003040c0c9812407080b80b804c034500c070703c050940b00e25281e010700c0d070b00c5500c1d02c07a414910030f40b10b0040c100e040c8120340c1c3e02c00c4158100ba0301040004401c8001c075441c0d190740b0f01903544481c28120094500c2d400100c0107080240f041a0f078049000030000200741d800111944160400c80b0443e4403a40c9940340c1500fa44010340f000703080c0001e0380da0300740308050b120100052418203a090451816103442e10400044402400c1c191405984400c1114031440500c808890024246041c0120303c90080000741d02c083d450003071206820803220f05101d40c0c1c408011410241c0340d8940300d102a80380500c0300280054510201c1240d0300380003410b145030340c5201124501210745c0203001d09030315a14041c90b01c9000c080c0030100d111043d1230354100076a1000c0791 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 725184856 1250 725183606 725183611
    0x20607080a020109060f050603280b010e090105011d270a0515100b03010e060a080a0f02180601021f02091002070807062c04110c011e05010612091703 66
    0x540010071140e400b421700d00c0417075850162050000781010108041c5642c08111080402c00708600c6a1904000121015501200201c0104203403000b100108181c96014046031065030810000c0c07000ea030301c4001035401e90b00c03800702c400c14085021011400501c60a030351001e00c25890781800c5841005e10031180c3c41c01c00c03101d00c00d5580d508140b00c0041c1d40006020aa94480103d20445814900c0c0a03030f0b03d0034600c0305218a050340c00642c0d0100e201c2d40d407601c050f1401420910126031308450113051a6001c04401c2200304e00c181d1511030304620140c418480d047c03080728140c014001014000942c824049044002282e4070381e404c0100e100c660391107503203041344003045d580201070040c24041d00d40c2c5465000e40010741031050003282c1500c0d400310940107040c20030b90419110b52000007a000704000e8200300708141d140440110301d0000d042015071004c00103018180740110f0801c03c4000305411101c081c010080001c01901c11070203049000d821031806c06200d281682102603407070002c2d81054005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 725186106 1250 725184856 725184877
    0x51017041e14010c0f12020c150708151e0405090a020a150e03070f1703160b04030305360a0b07030b0307140102030a0e13060e2d011202060708 63
    0x1d10303101002c5500241300300e450b440074504000b1031420700f40c01c0280241c40c0c40b515039508503400080303105901c070041c40005031034828010300e08601d06021502504264003103d4500711000144d4a0708290318089505c14840704882070342c5034031100c2c45000d101c0503103001000107810748103402c103100060311480030440c000c0900340d4454601e2007050000800398599007000e02e11a0b4851142404500305101d11502241c046150b01c2c00c030390b1a0018042c3c21170258038494030816030041103d1043c440016a01c41c404d6120307581c00c01669441150901c020481c41010203440012000b1307210380c03d0140202d85075450140d608075143d03100c2c1e5950301a8010b1048031040c0010761101070403d0f145c2800c200103005070003034058a5101d0045140001d540f80100070b00310f01084515242e811207501c8202040d600a0540c0d6010301a490701c41c0021a410003040d0b595040350304940340004c0868080c038807540c0000c04102c215910691030002c0c003032001c0341842000c1e44d01203010000000040c40c14001004202413 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 725187356 1250 725186106 725186123
    0x21506040b311406030319140a0c0b010e0709180207020301021804050f1b090103020c010e070828080f0c06010306060f05010815101806090906051017041e 68
    0x41007102c21054910001c1402e030552452002d016441d9400f105a844009801501103100c032401c400440d150641340444d1200314900141400c4410b034000c3d80005280c0c0a28080d0303000c0d9a0711421842c90550840365000051500c64013804a42c0300705000c1624080a80c4015007403551130b40000342244d1182d021681801c0090314100d5282c10b10307004466114008808180d890b19110a4941e50400c00c1c040c00380c10000d000a0000d0541e01a9050710b0081075010000c200901800340390a54580440c041d205440c42045407504030900e02d2400202d40c1030744884101034035050303035680c2c02050b044100c1005002c0c0702881700240581040005a0081d1300849012139070501d003000001d84041ea40d006541044401c00c108a0140710259141c9080d4100780d50190a030702c0003080c12074400101080b41200c5000c140b0300020394503404206141500d0340650100030040d511003c000410005554402c00700d4580050104c80300756456550764058010141a03c041c03444110704991807540907000c075244d82 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 725188606 1250 725187356 725187439
    0xf130f09050d0c03020d030b0406030b01120b0c0a2003071a0f010603090308060904150608030a020105010803160b1f03030804060c03051b0f041502060610021506040b 73
    0x200400030101446828204201083c030750b900c0003511a0f000a15603000d06803209041141c030340f65540304038002e6811480801c1a540c40380d800500110429000380c880c00c442d0700c00b0440c64075a0104441e04210f60340c60f214103400d4041c0400e880b01510300300010203030106000c00030100da0a801c01d030f800c40f032150050b01464600000c00c0b1200701c0060f04503c04051804000d078001070341107900990007132011561101d082c0c1e41d602d400100d840001215461041c202000004c0511002018240b0b5100a40007401079a803186450746e82c0b4041c8031071109440c0c1414410501280710b0303030326841d04403254210000203014051116180340c4070960044000400c0e81d000c0000f0b00200344107107401180a45418802404d007036100480710b41c200d0903c04154000041e10303525402d00181200d0050001400e90300001024010203901c0d07140445880d80030392601084046200e20104001d8040700605000201a4654206000003007200c09451b44c0c0104c1841c1c1d0803441503e6032217151614840c440c1c0b1620940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 725189856 1250 725188606 725188613
    0x70905011107292701090605090a091e09111e090115120f050105090105030319032304050d140f0f1809130c0b040e060f130f09 56
    0xd165007400401038000420074840502c024256600078651000800030703800c0c001111a50502c140928040b41601e22515804200d400308586100d035803098070f880b07440950368441a105482030710285c5602149841050100d49165809404d44103640c0610701030780c4030088044011280307a03807001e070751520240c842d4241524240c1e040302c2c04400c038400582c15000382000411150344040c0a5002c2c4900001103d4080502c96201c0c8a1a10b54100d82442058044a510401000c0070700030140101102d2001180904000040704c50100590080300784d00b5000d000120000d0410b001466040340c001c0c0f59640844161000d450f000e140544043c01210003001d5001c0c1160400c0e0700c1010900109205078040b03000120b044d81d074150b011803040c17591040c1086801d20b0211000300110342c032144100034480c0b816901501c03640040c2c4507109240944c0e4444003810744034007440c85020b0311403118400040c1c1e00e007420500c401c0a43d0002c0d01e112120080c02c042d034800d0300d24200c0802425640d95001c038050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 725191106 1250 725189856 725189867
    0x80c190b0f03150a0b070330061502030901022812200f0703061808160b09060f01031202121801030f18081e1207021507120f020c030307090501 63
    0x3c40d104030b580145180c6080281e4009005d4070304040d0a001068001c5803a801507080781d02010452900e0403214040d0b24040e10b4010300340c0d800740700030365800440341c514154000800c517480b140d0140c0040a021000758041e002c03a07840d0341600002070a101c0540f400080c1c600307150400400300c5884181e03e00c05981c440d00f03007100e155603036100281d001440300b03a2100b40c04140e0703000b40e90300060041507100103041d0180c1400765004008000310000a00a0507500001940c1524180b0031118064162a00c16185959150544641407050310b040c00400020340c5040b035413400440580103503070011804035200382d2550030014280842d00726a41d001003403503a1620614844100181d01007002d803021141000c1111350020300244040e00c00194162082e110288072902c0004040e41581c2c0c3c0c110801808422220565405015101e08030030b65200540e14602c142c801c1e0703642d41c0d03004c00b8004400700260142a00c000c001c54896800c00000407039440910040d4410200c079210641d00310f2411000404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 725192356 1250 725191106 725191141
    0xc0e0f090c1009180608030708030108060a050408040e1509040507140402030412031d0604030201060501081608041509020d0b07180f270c090801060f080c190b0f03 72
    0x1082d01c1e081c900d00d42d031503004540c040a03030b42d000480c1e5000c1ca031210415001003800da00500b42e9840302013407040c00c00014200460580320035400b520115224202e6840960302e060b01c004114141c24003051000e1048580340c2c6512940344d1080f041e4103000c04011491030300c800c0d24117450641012900340710414000402440b2010161400c52640c40c06480700c4000d05104e008550815407142c3c07000f1103c040003c14100300304110400e88009003040d140203402441503104050108003800000b0b1010100911445041d40c2180c98501c400e070f5540c1d0f1000d41c61040010b000480956682c0900090307107400d03103588440352107074841803020305120300081c0208500c1c802a6100e03d4080b032092104814465844080b6103d8044403a407001d102c402608450b20002c02584086e0301d8414100f410341c3c0e10201d0202250303400c17402003001e07d4442080c250079813898020180b281d0311542039140d181c05c128100c0d40c4408043c0c0400001c5903112100039926902101c000c0b18030403008010b002d4081c02c500d0440c0e2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 725193606 1250 725192356 725192359
    0x901061401090909050c060f12070c020d12090f0605040e0f071b021f02030a090b09010e0603060f060c1e01060f030b181c030b040c17040c0e0f090c 65
    0x40100d402400020300780c40080c00341040d0107465000c0c8038104413003000054000c0c0801403e482d10707984116684865904801d001b00c0584c60b1500c04200e41c0c1c1d00804034078070016009807643c00d41414940f6110514010643e03480c2c00c00c0005040081c5011301958084060301503a0b41c1c40340c0e624a801e0341805a40c04c003400c01707076070611540c1c180301215400c848181c9400e03c000c2d0240c45041100e000107003200403040242c200f84220300c4149442030303901200414588a854031880301c499216003051840c1d002e85801140070900c1c081d50008645818406907501c410b0045c0446030701c060000c04520103810803000160a0f51000040a030140d600400c6142c00081c200d000b00101da1415025420a0a82d40f0000e01401c0038030000c83c606e0903d81c582d00041040b103504131800b40b002c0c1500c418904459200b21070002e444d201c4000810b1900d0f0007108542052030360b5030a030b41032803c0001c030134075880903000b141e4500a000d400520302c51030501051040c10340b00031800192501c82c4c8028201410101040e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 725194856 1250 725193606 725193629
    0x60f1005180909071a070501090308041b03110d15090503041716090e030705060903040602121201090b03100f02030103020405010605033606040c1401050406020709050601050f0d05090106 82
    0x20403d0000010040122055003101080151307600726003440078401c18101900f0355080030741c044181500100c030140100d100d03800d00988462190781030b40c11200c55010040000600c01900c1c1154906070a624030f03064004c1000003e1900e040c461841100c101d07144c2203071660404102040b01c203000d4045280760307503110f00203880446581e060142d030021030b0340070b44810141e0310180c1c00034a2100300244e4101590240440b411420100506503503900580300c0d580041c8994589848204103400030b86458018400705900d01da42025640b2000d000030560540d003502c1348490030300b0001e40e60f000f00b0ba0000320107070700140d1321b5046006010035150305030404020b2100c10801c3c84000b0031712601d150014005c40c0341682c1e10718090340b0036501144000138a8401031040d0310a1009009036104960100d4000048192a141061006546a00942c0300c0c410158201120801c01c1340a59040190b1020051524030310740070404030361520755003104241004807903a4008201420000341b190101070311030980304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 725196106 1250 725194856 725194861
    0x106020d17060402071109040606090b040b0108150402070b0123090c0a1d03030403030e040b010c0210030c090e070f090905150f18130302071d01030803060f10051809 73
    0x1000e07003030002410307040c041e5900142513420b120f06036190852410005140440c5400d10f810001c01800c10380c0180f084036450f100a480c51481c25101e81c440111042e11130351070a0743c0308046000c000f0850300845801607001c000c03120001c0c0701c40515501900d04001c03401c002c046c0808852500313452184040f03005003120014032489848040544080042600c3c0c2204028141001e0b514100b135022a80381d090300c80414040209034028060301d141460079501000341d08560001110000d1104038041d421030a000f0b030306002d8174442d80200019000605220005965503021450f4141c2d04940030000100741241084c04141c0c085a40001031414410074071940c2071912141c08100c000d0303a40903216000400304403045d40c60741401c19a032075041e0079041c1c01e54544040b04810020304000100c00600800c40c020a104140344159616514140000e100382c0c0c2c00c6599144880d8009055144c3c03200d06003407038074103607a50604c0f469680c02842da5440d8032564a400040a05203a00004a120701c0a4004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 725197356 1250 725196106 725196137
    0x121101050a0801120c150c110402070209040f061b050406170c0a0c0c2310051806030619080706022e0b010504032f1f032408060106020d 60
    0x96043c15a910448081d209054900d0002200a41a07000315640c1c0c9440741e00c07880c01908600c0011201d4065044041031741c00b002d00b08022803003180c030f009601510b52404680030900e8020b9000c64603200d0000011603824041c0b0b50310716104034007480b60001c1c5001505100045e80a051400440d04a41c0d81e100c0c0c40c20403109a80c000d020703440300700c0e023081808003c81052260f0302850100400d40640340394400c40200b5030070074400d1700d820b03000f5006208e10b4070082c041d2481401220310201160100740420b005044c10032859074400f60100f5032040c07010307440f0034101030302c0005a0010008400103118841c50003501a09210640381d0781c0a4403542072502c900d41140420700e0010749003611000041d5081c09a005076203034050307604050105201c1200c0c05511010b40140b004601c0b20100107031404a000070208252290920100ca4417004005130f1003c10724069000350800c883c01c1101500c40d0090800605c10a83c000d078443c0390b40d988401d00412610350148403030444140ea41c81c04150000c02c100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 725198606 1250 725197356 725197367
    0x6091c050c070e1e0108010c0905030303010807090504060603140d0f020d081317030a0603150b1c03030e01151e0815090a02041103070905010504051003091b121101050a 74
    0x30a0144828140c8002013000ca64200741c0e10041410b1241e0901558403000350b20700a290407000310020070340842c4086203c0c5000003da074122404d1100402120b4140740484014040141c8101c0e03506807034080110010701c0d0313451104201c03561400244501c94040c00001c2070303a007a119541007550011806d030800320382d10090301c03640103800d107000e603d1344e00591400b038a0300384035201c80c811000c41c0030041c070134025125004001103074082c600d504d607082c3c10304030410b04030b544604a03c2d51000303140300b03a03c0d410641031405124543c0030341400100744102c81340082c02d6580c0201c4030141035102e20014440540100290521904a600754018950a1819040e40d420a46100e5003001b210a00003c0d40c20004116270701c00254054424003440300c0d803169584031600107443e1140415844880825554890313001e65044170b200415a0358000128141076005181061050320410800e00305c0c844902110520b00b00208041d8246d440c1c0840d403404c140760080802c0c0841c50401100300f146081244c1c1c0103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 725199856 1250 725198606 725198609
    0x1505061314060705120d05091902041a0603130b010f030503070206030a090c0906080d0201050405030a0507030c0602130510080702071505070203060a0e011503050d180806091c050c07 80
    0x801207064994903000081c80c40c054810001d10710f118000864608014102c050f1240d1182440c2c244a55201c038003699440341d48041510240110803021480946080d030091030f150408825039950b00101d00c40812150351040303500b1000b0003000c07403000080084540d0000d00418115144640f854110f55801b51680320f09075001c1e210792000301c0460300601103584981c619030342c00701c45242100d40d610760b150060603091246d0001c82c09400c01008149006010300303403140d40e2200c0910300d400d0803008142c0ea281c01c071100030303000c08c03d0103042100050454030040c0b40c0c8041c4032200d0000540340108101d140490380c2080400c0010311818401841e40008020060700c9000c1701d0408107882001c812a810f0280c25030207923251042005000d502c19841d132040f01384c8a42070000f8010b180c43d007041a000f035441e03403100428641c081d40c80c1c1030f140c1b8412401c3c8013400b8480081801d00c203544110552070b1500540700c4c0c1d5296000504980114201500f00e000c00e0707849410300754144a4501c0e0419254040c0c4d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 725201106 1250 725199856 725199869
    0xf180a021c020403030315060807020a12090503030c010605031903050f0a17040c14030a020105040e07180303080f01120f021002011104080f070801061802091302070615050613 77
    0x1ca0020005951034012040e64075000800710346481c0d0342e040040180080503001102200604d101081c100e12a0b0b243d1841030310160010281250b05903100c1d201d00842c0403c1c41c0400c0000c00c404225550144001c01c900180040007040c020309090030141001c1c1900c6082d00344451050341b100010b50084161182c40030101045a140d03060300000b512010016107c1405104a4038100410003541d0119003041c1e076550200c42c0101c02c406c80030306545400c01c90010f070205405000401010a12030603043d840035840c6001c4140451202c0100000304039070700f0440125400008205d854080e10402c40e00521092003d0001455180c07034090140c00c0006000e409621000030f011004d034003d400422502c1910140140c3c4d440c3d503020515115107003071580c0c1c00c450050140010780c04005005010131303100b0701c4551a4001c03280e0a2003d0081d80404500d03034100b40303500701024107521b04e40b0142050740e00540c0c0220707038512001001d04040c1065006039100d00307801d00403e01541610070349401943d01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 725202356 1250 725201106 725201111
    0x60602030c1509071e0510030207050c0102071208071e0302060403030b060415122909010801020a0203030612160b0421110103020f070206160b070f1d061e04050f180a 73
    0x1780c031440380031403031010740105400003421040c2003000d0f40d059008000550240007031303071200b001050049880f4240c520035078109178903124404003c80c0c4d0010042012511424091100302a1204c40700440207060304280c0c05604600104001c0c140c03d80946c2e04607500450744185014101001c091220070603440f814104800c03401c0c070301106083da6101d80103042440c00409111010b000c0140180d03101c44101d41c3c0112500800002c0079101402a20201c10168003d5403d568a00d024400c9200c1000d403145500d10030b20b0031a000c06a0515800c5010b402d030842600c4c3d4984c2420000300145c510400f28540c06841d054000c00403480c00c58413221400001d00c1c01590312211404080158002c0040c040c0d80581d00040341403101000800b0040351030312a050201c0f80d13541d40322003a07440800c1400e0103004038405142418442e00740c11442c1c0300c0d0807801000f0390f062600100c8006629011128030003954100010144a07500d000180f1002c412421aa181118100034054030070201000d48409005034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 725203606 1250 725202356 725202389
    0x50307030b12010e10020f040e04051c0e120d080a02030603071d040210170402010e130c031d010624031103040b04060506040506030303060f01090504060602030c150907 74
    0x14465000602031240c024a600b01d50901400114000d08000342114864030071060080e030600c3e880d000303442e80000d40e40d5815060a140c00c00390458085c0040c0202e03107a00800629000510034114031041c6554290703030300c412004000061000040b162403d0586940c88050200c1034160b00c981501d0f03001d000f01a0142c0c40340c0300d2201003450303d01640c021941340d40c090500c076100c1c0200300d20700a100300c3c001c40c1c00f000306800000058419100413840c40e42c404080c1b1b070000d0055401042e442d41d1100028151101501364040114103d030810034540e8002921020b54032100440c2c284518450b171009c074000c1002502c1c00c60306400c3c18014064084a00c070446d540800c405010f036002410703075030941d060199a4603041c9814101340e00b04680444a85240401258450074540b10300303403217010080c005624540340e25040181940111900604206400b0070101e800e032550b019080040c90b19400654490341412051801c1908506d01088c40316070810070007104130000646801251140070329680e5a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 725204856 1250 725203606 725203621
    0x201030e0f010213060905030a030e060d060b0702011103130e040f050f061801020f0d38120d0e090a020d05070e210615130908031008010b0901060503 66
    0x5084005010a99020744011400c0041064008181e4201c0004d0154a2a0746070841690741c070059001b0300e41c056210a46410001c2c0c010302040c4400c07035005200d1410551014058401d513110390b0000c040341400494140e0840d60082820740d819801c2101650410841d20010700d260f1405106002c1b042522902203014403c00000040d01c294024041d1400b4280000409036221820b40344500710701039019114a240034188260ba004098400c40319141c242120700c894090701c9103001050810140728045d0a000c04e03100c800016400c420f9090a01c6040d0308010802c02e040400b041c81d20075000f4868031640103030721218061845004503407088480e210450300200038090452003c84003441c0c0018001c8584d0030000c2e201407a4801c5030404035103c0d0a07541144503068512048020703a100f5400300340c01e405d01900309190450007500594050060781c0c041800c0e50400c107002d0b1a51400001032050828030a00301c1c0307000d4100ca40003032250000715008922201c00504ca07007410000080041200c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 725206106 1250 725204856 725204861
    0x280e01080a0903030f05090d08070c0f0305301e01030506010b0325200a0b010506030703020702030102120a0e0609030703031a18011701200c15010603060305010606030522020103 78
    0x3175800c0c4070300070401032500b0000b1650741c6551902c0503010514820018111a1040d08042c5080d548041c5504da00b441a83c0e082e1000e40010003811b0000b41035084034070782c1c500301e01142e00c45076901070111030441c1050201282d110190000c4004039030300708001400400c0001402504581005125554079603400b42180c401c2c10760500b00c890142c120030104160341c0d90016504a4035002400707400b40f05807404a0084d580c40841600802d0005110010416850100c0c0515030110080c14054940481d40e0b0001c4c1c02c82e80b103c40102c80c4d8000d00818414880e07030318814010206000380c001c10143c00c1c00305000c0d56034001d0328801020580c0b0b9410010900025000c215450310010700b20401e014144140031030140c0090054034282404014031504800d8140500e4070308c0e0b02c0780110040c40d011100a10542c0d58412410702405100300070f4803c401e0f0b05800071040c02402c950f580040e101e41189802d9082d01c0300f50303000034105420602804030f60317002034000728448544484a214450b10a2006802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 725207356 1250 725206106 725206121
    0xa02150a020111040e060a0e040201120504170c070905060d0b010b031017060402030c01020d0c1e080c0604030f0201020405060a081305010507050c07050a0b0f1c02280e01080a090303 80
    0xe60f0101080018040304c0182c10580a40401c0b40d4030000d154035403030103040190302101c01a0025070842c0d07000401e840142d10031500140503c03981d443c1d42c0d851071680b004990007030400e0481035120010803c021899880303800c1d0402011101d01e03c1403001a11100c1c0600c406004007000400000045080344041420540c0181200510400c842009220b103d88510302260103034003a0040d0b00b20003c0941c1b02140040701d000d010b8a620a071000c0640743c18901050381c10003500701d611402101008103c0c2c8402406003640c214005141616080c98000c2c0075507511070990003036a0041c0001c0c00a0354035681516040307001460040c00c1a500c44881e20482d10032000b018101c2c1d46000c0c01e201d019640000182401350481c422100160303600c00600c079801544d44528020410103004001030300300c410004049106d0f003444004a03141c0000e40c0142240e2055481450103682d1041c007414645036051083c0212109007400c8105100c0b210000c2e2160000420010003107030b40e2a1507c00301402075201c0e2a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 725208606 1250 725207356 725207381
    0x3010f02030a1515033918030c0b030406022814041a030618090c0901170c01140f030a05041e151508060709090e0a02150a0201 56
    0x4021090441a80001e50040d00c40d1140705042c40c08088551542107240702c1210340318a80204c0a0641200840040011400c00810380111000f20000441071010700030480c4014194460001e0500c6070140c40d180024842140094401b2001c0010a1694400b28101ca003003c0509690340e485107408802845071100740d42010b20403d80c0c80c8404051000a58a980402c0d1544010704142684984080c0580d1150103007141d082c5a180b02c3d6200714101441e0001c602a1a41d40510009000041d190f08211419941c0383e0090400e64801d1600240c41401441c9005940c801c0d00f40241d00140c0b14106008075906108011007041c51404121045a0b00f5101e0314800589a0134030300400000307024207440640e0030301019028120181600b0888da402554000862030000020035064005000b012f1030300b1000062070070f40010441c10074051a4032072400e9543e1000c000707017006110f00456180e00200300d502c2e0b1128005c1c1d00140c031010b50303000c4001c04007120b00c1d46a07600c3c040e0482c00f4021222200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 725209856 1250 725208606 725208611
    0x40503160f1a060405060103020f0316090f15030f06030f0b07181e0609080a1704090504030302070624050d0507260c04090f06090215160c0b121602010b0301 69
    0xa410b8080700410560049900300c07014499615040d004400364050f004049441c40c0341000440d000100400301000d0702045401c01c0b040040d550044400da0f0000c0b680961115011245030b00400d9a00d44500103109204500c20852a8155150760311020a19440201043c2c7c0d25404540c06c24065410205c3c10384443e00080c0201d600c0780702c071001c44403c81344c1128008403212008a0843c4c0550310807000d81d004030004050701d03405503c5101031441d1101c600050250104000316840c03a01d4060b86205500070344001d6a0f80c0420301e40f01d0100c0302030041c0420001220100030400c511811051021100300b1983c602030b041c900e06200742400c07000e500c02280f082c00c14070799540c1403c2c41c0100d07200c040c49490503965a000300d44280310a0f00c01d54840101010755a0240390300103aa02c3c2d006a24450014002c0c000c002e0148401a2036640580713003042c0c074180b49540120400a00b896003d0140118103051410304460040081c030000001d000b07a4440e000001980503102d100358050844298010005d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 725211106 1250 725209856 725209883
    0x2f10050106030b0109050307030302060f04030507020d08070b1510030b060423120d02060a020f130b031b07080a081b22050102160308030603010f050a0509060609040503160f 76
    0x107002070140003c3d85003c640002e000203050300d0045000317402c40f90190098481542d0f02c0721600c02000c0000c0049003031250900c0b10001584072491034682d0385100d10207a654a15903420103241407000280b80050052484103d07051f0790b180c1074000e041801c032a080c00300b80050007000142c0c860041d1741191124101288041e00c02c00e02c0040c0741d0801580503601d40c82c003000820744158a85c100100c803000981d020401150002200d58010401502c074000110f08110688080c00c409001907031112804000100c240400b000c0b1011410344224601041d0620f0541284d882e074201d8003c21401c0300501130703d80000b9000706102c520340f4813419140c0f0542c554824030000d0000c0e080b003a203480e942078003c80e1100801c075540000b41c84601c5030304030040a110a451a6140c0c4a56031004108940554072841e003840404401d003c1c081c007548024602090b40e140404205144c0480104050700c03030340d01e100610003c600c1c0401100e0440103c010850352040c101d060803100101c02d410010041c01c4076115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 725212356 1250 725211106 725211119
    0xa0c0203190219030b0621010216140c0a03021507080a0201020a02150c1209010b03070305070e1006090905090a0b13020405400501020a0c122f100501 66
    0x11007010709200301d401140307004108002d2041031500e40001002005440b010407500c0c07030001800381c100c8030542c1350003a901060700c12040c26a08203040c8602d09104a801c410b041001c10421007030701903001e0000b0000454114001030505d003151001901a050443c0d201c101e194002c41240c020940000e5410b5540103040130080c000e500403411a4010300590b908091040c11a0164501443c1d10381e800da403e0040d81904200b04810107003800f20706660702d200c7e00e000c0f61000d021140086018002503c00f6a241c01400d80c001d103070040642c00c0603100071740d003403110a4100d02101c0503143c0c83c3c00c4c0050140c0c0d810080f1843c000c109800503000ca110304c001c1002880581ca5031440f030710f2007501d080c0810b4a6050307142c9848a41d011302c0920b080e80020348080ea1903400d42442500c3c441c0355a205050000c80c0c1c8503142264840402c90001802044400061004620310410905031070f18048031040703e003030103241d00c44250001d2024804481e40a05a2821041040801d600704523031041066503500c2a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 725213606 1250 725212356 725212393
    0x20f0f0c060f13031706010e0a0f0504060906050d1211121b010504030f05210901050702120c030d0f14090102031014031011040305070b040f0b07030e060a0c0203 71
    0x700c0180303040029000240c040101072003003803442a07245d10789051401000d41d61050307481006048a0412440f0801c1142c01d64807024030354010007455801c048610304003024007050710207581110b441d16081400410041d1075040148030f007941c0208040030780b9466180200c9148181c1d0f0610300d12441480e00d40050703007610000501056450101c16134503045840411402d0301d000300c5016012038503c00440c20983d01440c014414002e03442160050381203e003440a650b61029550f071600c82e0740d02c4040001045d0104001d83e0a40c500e40545410f125130002c2441e50307441540715001d40d460b1900260f0440303074682d030803040c04800b07050404419481c1903e6458001d4008540382c0075080d4443c030001a0040001c202100902c4000c0c1c041d00516a00356000c00c060f04006a0144005804000010104070244030b403101405259916070f03521480d00307010269111064005844848040080100003034000c052076868410036076075181c032030010000c192102070a208000c1c1d094040c4c40b406249500783c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 725214856 1250 725213606 725213611
    0x1110d030b0406060e030c040209030708030c280f15020d0e010f06210209131205090f0612182505040c080910092d0510020f0904020f0f0c06 62
    0x280d03010420107685000449105c148000c0e1a074041d04002824409810301e40c000b4040c1d00000303005c481900e0769840d8203600d141d2140044014a41050803046113000194a0414841c050a45d03015904007403a141d40030205c1c810b11b0b00400c050038218544603007410740e40544922070002c510401924522104150180c0f048a03440b120365440d00c200468041c82594a0100350348965900202d100102e034244000d02001411582c1502c50500f803500025000c203181400c030082c01e581c1e040d214140030707051141703001d94801da041c80b614050011400d080100303511380c0c0c0d2192005600ba106810b4603454036003004207405a6481180110030440b00201007504024111602950100103490300908120b5a52809132142c0900350801500701001c0559508080c000c1405075000320000c0e050b1001e03c650504540b21104004002c0441a00070310205000c1c0c0d5441c00a50001036180c1603075041e01c841144074201144d0710a5a000c19a460707000d039480c05544d4401e098280c01c60350740c200010015030360301c3c08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 725216106 1250 725214856 725214859
    0x220306090f030f1103090d050102040b040b04092007020409140715180b04120512031e09120316050d060b040806070e03060f0601170a0c030b0102161401110d030b 71
    0x503e10903041e1248a20322500c03100d4003100103142000c00410800c40b189450100542d00340d9001d10010a003080c400b002800104241c0e00006d584910703248a08082d111115003614000c1030910401103081580000c59060a40c11200021a800c2074540403011103800c0701185070511401c04085800c0180440307580c902c00450700e52082c4144441500c181c1c2c0d00c0346019080c0243e43c1800200841d240000c425180544980b055170901c8e03a982603c2451900102e84112450500c07640301501010340388281500880301c0b0025000a038601c0000c01c81c68071010b0100340c90100e4582108140350301c85c000362124903216505c24001c03036680386c10380c40264001c0d014004a6014000101c0d103154040c800890b26610080c000d08140d40c2c40100d03400400300c008010606008042103122050440c403a52144101048000040d43c151102c01c014100c1d00c13817017885415507111117007401000042700401005c40d43e080400740d410720f00c203400481e12440c650300140850710803d02a40304040c0c054020100c001c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 725217356 1250 725216106 725216117
    0x402121611010b0d060203090f120909090d08011401020106081608010b12060f060a0b07060e070b0403020303030c0304050c03030408061b041d0705041505070c0504050705220306090f03 81
    0x29484212401c076850480c0c4a0b1340145100340d00c0000035500d802455000a0039000c6d1030103140b04200d0035007416001810300b1030b02080012080740c03528040d840241c02c0300b0102d00600429030042d50145c01c183d41030041e4a50119500304171402c6a1007500b00c0006807030f80c5002e41c0d46c00c64855031003009104044c01001115401d2145810302c60900000c4c070160943c4140c02400300d9101c04564030b40814001d020b8a81081c030f816008589003810f20010070380b643c85142d00240100706210750500b0140303160042101030f1020002000580e40010540b81c100d0203110181d40d40380c54500c0d001d803601040318000d50b0140404500014020008103c0f0b40c45007245c0c0244c0301c0d0500840c0815200c512032406026030301041821490b072825000e1141580c0150982001854243c03601400d00729130789071407074032400540c00280440c01c000c050f2400070000c1c281a41c043c4020300b0f0007000a4950b0190b4410701e5166002d480c03006811200d0000404c0003980c1201040141c0c0c00385043c1a42c8c0d120748040141c01048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 725218606 1250 725217356 725217377
    0xe06192003070201080412020111030f270a03030e011d06040c06210b220b030c060a0915090b13090b010c050712080403120302041e0f0b0904021216 65
    0xc030302004440d0816816955141c031543c442c0e60b0702d40703e043d1062444085660b41c001001120940320b000714042c3c01d18103541c2c0146e20707045100d03c05030707039503100d2240c1c40c2420800ca8442000300060054282d5034103040c00f01d440000a66854018810b4058401e02d540c00c516850411450120310180601c0c00384004101554a824050321101050708000010718491142840e400141768410503103e54002c042c1e0b620049081c0c80201310850708400d0706421681e40500c0d071410b07c0c081040d6246508103541d800e007020f88611002d41024018821074001041201807020b41ca842034002c10003030b00e105200f00c1d4440c00c3e403020100307240e2110300a841180d490b10000310502c0d0f000b0b19592a40c240c3c0407004080d000c0c100104420089801c070340841d841e40c8280000b20010f403600040f107598a10f2a0b0380141c495142140031070350030880f10041d42401d64850070511001c01e1104d03820f03064a503035420540e56011004042402440740d08894004a80720303406000a900a1101c42031850445903503500281 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 725219856 1250 725218606 725218667
    0x8010527010f0503122503030b15040501090e251407080a031a0a1418090616091d07050906031e180316060219020a0501050a0612030e0619 61
    0x1b8030400341048011209035180c1a0045d0250001500513840b918000c0744400301c4c0360104500c1d0410003180d151101c4041010303c034030f580c024000c8000304081000d0b13070007034106154a41e4031840c0c8080c640510f2801416181c1c01c1c00d000c1e0712000c05001e0242900d5581d407a0034205450a500407910920000e41010650310500005e12420013440e080142050b00044c81c11112501ea407101100349500800780c40b0700400852455000e481c440c04180c406080d0500e8139808440c002d40083e107a000611007040d405002c04a4941403404112510500d40d0b026511164030549150044003440307071780880700004000362074075404070348140890960851441e03a21188808508144072944018282d4014000c065000ba4605d8542042e2406403000515100c2c25401d207403204c8040d4405a405a40550441c008010342440380c542c0c0000b070380e08200081401c081600e041c000e84210f010f01004002c1003001402d03030798602251683d00400300d240d02e05040038540a88a8071080c41303040701903030310b00c0c404d4a802c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 725221106 1250 725219856 725219893
    0x1d04050c0904080d0e1905010605030c041107110a030b15030d03110a0507020a030503070830010608061206070e042901080a0905010203040f02030d0f08010527010f0503 74
    0xc40d440004142021308070320391031000340400000c0342e801d0b1040700e84070305220307108070461802c00e07000d00004101203062100341881e01000d80f2820703001e10316101140c600d642c0102c040c3d0312070b19480b016800031b0701c01033400262141c6403604042d29010350f60017402046001e040785101c1490059003611101500c00005400f122000c4545100c038031010011a03128a11480080c44450310050030745031800e46a89840e45550804082102c4242c03000420007200500c04908810381c651098000c8117110b2402e2082020fa841071080d84144840100070a8280c0c3c1c942c0c1a11880001a0046481c2881c003544000c0460040d0108540103500c2c1003044140d12178110500100c404d0000f0002e1342403000340004442d14a00140710a0089907213540003400101c081c0000d601440c0904190545a80c41e401090304102c0f200104d40240243c07a1144e8501c113400c40d400b5411188100d42c0720304220300c0520307200044c4950f6004e80c621402840300102d180a211010001134403030a400300c035800c0001107500543c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 725222356 1250 725221106 725221111
    0xd061809061b08070f0c050703050c0310020c1e0c0415050f1203190207090203010e0f0105030c0f040c1b0503120c250206090607060b0f1014131d04050c09 68
    0x20f40c045000400160003001c2c0341c0d001a00d01c3c5407440e90000e00c0c0d2076017401e11410b80c004032800c1d0004548460b40d803604200f0303010700b141c5201d01146083c1d0600030283d500c210701c10030040c070000030641c0c0a081d41c2c4103205075460b09001a006202403091003404c44420702241c000c19100e41c0340020505d9040c20181c68030b1090144442c000d510303241071350744c500d594410240f600108510a0442c08528220b00e800554020411181d843c1c2d00c1742800791b0103040b40a4141c0203980203503c994040700481c0da66400119600f0003e481c0013815648001d000c6605810721005070346814030b540d180700c041200020007015100e02030380124a15481d14151107100b4801c0802c41b010038503001e007030304c0c9407090310b900b8403108a80f0013070011f46045008404142d00341c1100e4420780340150380e4030300701c04242800d8144010034007089425180c60490f21001801c450030325014010400f0004c2402019035502649c44130240c82c0314030300540c031070720b011a40710200b0404640c1180c1502480c0a401000d00709481001e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 725223606 1250 725222356 725222411
    0x9011205060109110c120301080d03230a1104060507020f012609150108030912030301060914060c010204080307050c09070c062c070602011505150d06180906 69
    0x14280e440c0c00c00e200050070542c5001409200d0030094020b07100d00070800741e81b1015013400526201d6152179512810301c0520380386c01043c9420500340d82000c0301e101c4811042420318200640d00398540807540001081b820b08054900324002501050441d001009013002134400c03555a040300e1140d03001110101d040c020400c0040b41c0840c604580c0344402294250f00481c0001241d080038141a000003850b4000c1c1c2c81034071b16400004d060451400d045002e45801c1d0740040c029071540d40b4241c0018020052445440c3c00c030300700610030341c01030760700c3d80c080f6190416218003c0d902c40c1d40b00c0c448552680c1c090182140d5621030007401e41c0c0941462101540b00318481d0715501d4420f6841d403540c03070107030408400b410500009070303007049842c98000d03500140d6840000d001300310035810100d002c0e08441d082c80d280060000704d000c0420a40e40c1c2c0104080040703514165841d100d04c0405d1003240074084c180c01c1040500000c030f550320a21141980401519401840103010841c840c0164280002400c0c8044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 725224856 1250 725223606 725223613
    0xb0c0c042301030b1504051015030903080a110405060705160909050d0509040e0703050d0909060e060409050a051b0a09020717161502041a03010807033e09011205 71
    0x1040442c07402121540d010280300c40c01d204941040c5d0000e003c8880803075010303501c511094800d220060b004c1c00200000546803d00308415401e41d2000f40645034000d00403c9aa6110300500c03c00320f03840b034252001448041c00190311030040c0c2c076000e9290340c1006a4241182400c42000817925200d0140c1c0142d540c200b005003c0200d074201e0201c86551240902c15005a00c9800d40581c0b58410041c2c13000641c0210003070700c07a103040c0350802801000b6507171258540ca41460b000b4807e01e000c40004540044044600003010b0040340340850401d002c0782d00c05071042c010301002d441245400b0312500d0001104442074080d07192103080080c101e0145080c06400d501d009183c004485030010003c1035200ca4040c0f0100c8201800c0d43c4032003d4481e103200000c0d546401150401c840089440d440c0040d00200d180c40b81036604111081c0c0e915402e030300c40500b002803501294440070103042401c441c0c074200714080c001d514003001100d18810101742c14281c0222540380c00054400d552010140b00c8a6214024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 725226106 1250 725224856 725224859
    0xb01140904051b0307020f010b040b010206160c05030a39061109060a05130e0103020d0602030a060b0409150b0a0c080306120a030207230904080d060b0c0c042301 71
    0x51100500000b040402942c20070b6503e00e21451041000c1c40c41054241d0080024950540c0000d003035034030980025020f1803c0416111f1980c0c0c010803201d0307000403d0b400a0b44192601c0c1c4007200c2e08440504003070580c2c0000a44400c020340c1c00f182c11001c114a28004a1a02c040103040114030030450300909903600f00018042c00240a9400401e60000045109402c01c800000001c410b980080400c50214600058600c0005500c8001c41c005024020325080c0701d615503000306080041e40b2400810305a80000001c00010703060748038071302426010380c0785a2a251035241ea01c005115114007400b1119400400141c65a2136000b25440565117640f0a440c1020569881c0412b400241906a0254645403c0004450100191200f940c0643c0c000d0198074076000107028007402d030110302c2a0103800307030000c10748544039035400b590425070040d0b00c00d560b000444403400c000c14a540040e1441400050b24074504200054007944410085404024204c0c0c80444180c081003180207030390006450400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 725227356 1250 725226106 725226109
    0xe010e070e01090302151803060f04020d210905130c1e03091209031403030c09060307030e0601030605220c09150e132306040b1305010f020405040b011409 68
    0x3050300740e40181010381d603141e102e41c009480317001e4282040320394803008a5080c1544401520041c07582e1025805003c640c2040e0fa0640600c1000800190240c003a1004003030070889924418130b000b040c0104a044030700c0c140e000c0200400102d100f018401c3c00c0c040c01020080455201d50b03010504503032155280d02210213502c410b00c200040c041c1081c10350791600700002c90070f520b0080c400e0882c15a2283d1303100e41546042d40380c8948015403448140d000b0300402c081e4103080d00880b5003030401207502a03281e03994418218040c10942e0103564081c083e03200008200100e980103103000f00301e4140900e000c2c0140c0c90302112403001c4d442014100c640c0300c02d801c200182c0e00391320183d409a07008a02c0710042b501d518403819511410707140500300541c661200002d0018020712100e00042c11044440c2e81e0103101d0082d55604030190018002c1174203240071641000c5002e000300c075602e5002c0c1c001d100e001c90020080000390850300c145401181014145081e9620034040c05051482098055040108800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 725228606 1250 725227356 725227367
    0x50f09030307080115020106080f0c0111031201050904020a03061802130908030c0c01150f0e07030b241c090210020d0507200a0924150c0503160308100e010e07 70
    0x5811170a6543c0c444011030201020701c403080310414410010503281250200042c8404031085d00c00c0181c7e00309105c44030004031444515811983c048074000210784036800041c80074841c6510042540e49080f40354100310401c0d90700d4001c400e0003128501c0c9034a80d4014007005955101400800c0c4c1201040050050403050002e405001c2d80e01b000041c0314451502d01001c44d0906820043c410010002c1c02c021031401039682e40e5000d41702e864188504034164001c2880501d140025075000c0110800031b40c1d0310501c460a82d01182003900114000c1051841ca0704024070840005070300500500c802e24480900000742105040429900c503803130b06c2c4154540e8038024014074040543c80b800400c00e0720807075440d0452900a030500c0000000e441c012120410000d10000454410014401e40d04000d050700300410008100490300b80703070159070b60b5031405908612400700f01a02243c030880340c5100381940510700308e12401d25054445030380390302c911108001d81424840c0050022800c40056a031a01c40c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 725229856 1250 725228606 725228639
    0x90c0a080a0e0d080f0919140f0d1101060b09010c080a0c0506041202060603060c040603090c03060501030b040201110c030703030e0f040903020f07050d1511120109050f090303070801 80
    0x20000002c10380149600642001d807003004150001d41c80105000d9a0311242c01c00355003080404000700140c00e03040e00812001c01c0c4e03070032000c0c00042e5240b1010400040c01d12a441d000300008040e82c103007a00d88500901100d20721148410550b10f000004a642c5030541c00325001210140c483d010130f105c0c1580d030070280b6486440c6410801031314280070700000d1020080c0300e02481c491034101022411001d0028079201004148500c02c0d445030051000b4150044122410340b6420305d00030030154150b0906400b48103081e84010304440c50b103c000000d11091a2825005502c01d0380e0ba00310460104d40c100d540c0d1125080d4541d81500308220400000c1d024004202c40814081c0c50004050781c002c000800702c0704d9020060300560008002c003070301980103100020140904517442080d00c54162070301e0307181c01d1820b40801e16556950024504030300501d01a28001c540382d201c0f5440300c3da1151380c034074050070007907584131100a003102c04070302c082501000f0390313118030700c40d42e56001d182c3e10340340a111082010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 725231106 1250 725229856 725229871
    0x91203070c0303050a110a0b0402120f03030a1407020d0e041505040207060506010216080715020c0303071202010c0507050309010804080c0312100b190c05070512010f0b090c0a08 78
    0x410004001a1071281c9900045010781c440036100c484a503c041c024200420030f40d0720f90303007010900c0380010700c15541403604243c044d62807254840c0c6007403002c3e00d4071001c0c15020070544808420420b44107150740004003402100c620405042e154044140c1c1d917a1440d2401c0408101e0913891200141001d500c450500840f010500d05c0e895a41e40c0810101ea02000301034500c0c644880810060356010481d440c00d52180300c8410035031915115419444402c0c0b40100001c0e541c50a1183d141680700b0811140620380080036070b60368103190302c0c195074402e003a0755203040076508045804288a000c0c5050f00c50164100c03007d5403a0150741c00c01100c1911004108907000301050040442d015401c1000d8841f407109030094540c2070409280d0764400f541c03158010713440c8804c100702c0c00da6054684200003000510504004c006001c0c2490b14030304004554104a1f085034160411500c548015003007210424007540c000c001e465013013414043d800008851402600108100b00c0c00554800c04d40d03290300001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 725232356 1250 725231106 725231113
    0x80c1c090303090b0c091804020d02150a080f0c0409020702180108010605120c030712080d02340c0519080303100e1f0b0c030705070e0a18080912 64
    0x40111404a0380c0d62401036000035981d140701001c001c1c11004254201c10402c9a20b401c02680c0000209040d6400106a41600d074041c08181151901c042883d4450703802003100c4000c0c4010072924040d900300860100001707041324089010a494120301380e01440031540b20900e443e003031020f01000b9500c100c5080f81c00c084000d030820004409075034031034041e25483c800450464035000400c500019610f000d081e5940210040052176070340020000100da40e410084040c114050401c00740501416861410072400002c0310351500d040c030ba000c2000301c0903520040808845a8a040e0f80003000050004d191400c0050180068a040841c04c0413100107410107201d07d5858a149904540050b100501e0500c210017050080b0f01c1e09401da03990000e501520898150303802c1a0004400c180b80c40381d00c10000c400100041428001e00807030314015000002c80c0c02c07044c0e039901000450f1030122003008409180000c07881c54200c0c02c3c01d10104c26500040810300304000141084851002c030122181c2520 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 725233606 1250 725232356 725232397
    0xa0f0312060803130503061003020d0305040902181e09041b0b0d0213331e020604020319080d050612070306020703081026190b011502030a080c 63
    0x111140903610142c5441c1c40616202c003401203040d0801e202c80c0c0c100320301c40e42049042010448040a11008803901200c0c50f0001c040981001c1d80c041c07003560040e813034050000034500c6e420100c1d110320310402801035900380f1f9090102c15000f40044991b2695940c8003500c6804980410b21205021049040d000c20354003085a95041c8200300c5e40c04905524041c5030082000507140c154040b21340028624031585406c0f01240da2050901c02990070034002e502d003071054541c031140e88152031421900340308030141100c04a0b0100082d60b50320003150100c0c0300384070790081c140e607080c20314680000c2194004400b50034002c90a000d48085d0000134011034004110b1003000302406010008000154050300340181c5d82c158500303005080380802407103a41c0c1d4541035002001000c1c5204007480c110360b1944c20309408204007600c900c0c10600e80440f603c001910403100c040c00c0c06001d02d11030b812900907000b050a01c0c1a10002a82c40b400ba003102c400104114000042170307000c00314000c21200000b05035012690 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 725234856 1250 725233606 725233637
    0x10e0f091c02060910020a050f0a0309060e010f1a030c010c051009030809070501020a0309031122061403160e09071a040501180b0f0702120102030408030609070905030a0f03 76
    0x641c0000c1140041c0c1c004001c1c46200c002c107100040982c40349110561030040b2455000d415407042c1c100c0450340035400180c00362054400e41c421035140e0341c0f1090620190070089880c60203005214214441c4030300e41a000c40800307208581c217a4960740701401800782c9070680c100650707007d02c0420050300e4600998240d02c034104070900c14000e03d00c1c4241c660040c1400c01ca00c000b803034255103030011410f5621900c40071001c6078011000004072036200d91527100200380303a4081075481c1d2507548400e0400048a07140402c144494002d1000d80712426114041c50740c51404040da60000c45a000d038880d2a0500e041c4051040a100f0940c82300d0341e94100c4100307550701c43c0404101415142d203049040c40220f800d02840d0390120400c1c203018180300119aa540c10544021000c0c0700701c25541082940c006040c60841d00c40074042d0100305007400085441b450241050b0425910482c1c0d0580b040d141c071400150058024881c0400341c610160040c107030341001e0346d244001068020f0041d024408402c6018044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 725236106 1250 725234856 725234893
    0x7061d12060a06060810060c060209130e010f0f0203130303110705190c0e0709090515090a2c0604021e120d030c110a060c0c08040306090c050405010e0f09 68
    0xc2c00c2d24440080d4040c03070203000510801015044440f82c0f40880d00412074070380c0c482c00b0302034950f412020059a482c03142d000680c02d91410154001000c3c10511b5100c0880010750102000c020f45441c01e11620390802c58070003ca210480780d5120310184c92000d900400d100782d0014803214494410a840c000b00b50310b4552030700106001a0806285000940d41007100307a03d1120001d00100e11840b0040c107100301c01402154030344c060684225550000540783c004460001240500041c2101a040c2040300c0c0c0c100107800820440002c1650351600300b080407007144012a41d5502c1ca00c007604c940c2c2c445a0070803204000000710407410028450074400a5036542c00c0c061140c40d100030003460200007100000c1d0603211110101c2003800060040c109206401003420964540d01880000c1d080d1151982074070400c07001c00000d80101c1e800702d8003008010595215000c0c1c14014600c680400e9079620030401a107070240038410035002d05a0204440b800d0400c0c1203500311058800b40c82140d031070011303030040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 725237356 1250 725236106 725236111
    0x27060302090c0307030b0103090b0406150902040608010e06060a0516020112021b0606040209182e0611061003080304060617100e0a03020309011202090d06090308070207061d1206 78
    0x5290300c0c00004c2c4a1165050710407403400d0301d000c0c203090000020b1a19500c445003c014005402c2940b140d15000070f842e0030144503000303869000d500b15240c6840d440c0061001c2d0302401129038060b030746000300390640340003c00e079008207010707585261500240e1800243c40f110b241804070306004030b005c0c0401e8441140e0010700084051001951034040c0303803e0380103140020207800e4034003d80c410441040b55440c7d00c1881074041400c005070168a0701d1f00200450360306500040c00c06901c3e981921203203a41140c000c0a022034803ea0b8800e05800036000e400d60711240e003520080c40305000b90a00b0000201c00c0c0000e940c1c03090107000009015551a80d05540c4650140180704881c0c1144c0040b4080211520800a01003a5272008054083c42135401a50701d00c6071080003030500c4001c0b40d0308c0e034416000c1d40498205000141100c00c080714286454009040d041c01c048010800b17003400504410710000381c0a040300e1495613807520004058034443c0003e020303e00708541214a4a03080e02d03c224007080942d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 725238606 1250 725237356 725237371
    0x120521070c24080103050c01140c0304030c1a0f090f030c0d0c1805060f010e0a03050a0503130608090709020d0204030503070c03120518130b120601060f03062706030209 74
    0x1c0624081084035040b401200001042c80306a5005102080c000213504000c1c00c1c00382000b030702c0410880318a60307840c002c1990401c82440002000b00803c60320315001c101301c8604001c0c2c49005c26500d411140e40c0c1c0154002d0240038041403009001d1464014806000f114010341a103081e0700207007022441c403507040d02c4140c0300f0384507001080014502401e4200280ea40d044000c0005041520000c4c564003001c1485904220030209030a048c0d686d4520900000c503800b6086071840c4d94280b4010303440360090110780d0070315403016000144160040322500e200303824000140c200c0508002094000350405c3d05910881c1d51300703000220000310100020800c0c80c0c012170039001040d00d14a003509141712101d50010401009201001051141c1aa0008240301c00c80320680c628407031203034a40040c2103205525601821003000d508010401084e681e0503501c047ea512006118980760643c1903c2e405d20580403c0d441c0214408150440e044c003030000c41c4081600450b409a4035000648a680300b590f04a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 725239856 1250 725238606 725238629
    0x2070506191d031c0206091b0d06021306030b0916020c0907050c0316150621080d0f050403030b0a12020108042a0608090109030c021909020a02070f120521070c 70
    0x1d44c060301040643d6100003042c0040500b80c841034a03030710000243e03030782603401001031070b000c4c0d01003061a4046d17403100d5203070300c080c14506a40c0e8103000780604001c0124a01440c1c858001c07c0c901000081d5828102d01650010601c4401d82c400703001c2e9051004003080200481449a80c821000034801031103020b10940d55103100440ca821700030f8a4030800d405810440e80761410410601c0c00014900c03252b880c800c00100100707601828198021711904181580c0180b900100c45c018000990180c0d0096000307540402026a036041401001c2da0346000e4034442c0c001c50500400150302c0f0f156602d0b80140b00750819000c2c460700001100c403011100d004007103443c4d9101c1040c00400ea2104003983c0c0312000384000d0040c01d0781c58a010f0120940220041c1c02080c0220210b0220001c4600d054010410101c0841d0f07645e0480c8002074954419004003000f248107004001483c104840707440011a40200281c80813030b1500101c80e80d4052140c210321003600040c02480017081c8080040c41c01424045c040c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 725241106 1250 725239856 725239903
    0x60503180607021605122e050c0414030a030e04090809100917070b03010314150a0b10050c06060f01021f1a190e07020102090a0f0602070506191d03 65
    0x130b0624080c0310341080d0302450400c80484880b59000684403403141681001e01c5002034a100c4c0b442040b1807544040b1031481c00c220520401041c0d250092045841040706235619083d400d0425850b000100006400507448403100f880034900366124060340d51003900c0062504000d91b003c90795803c0004010000300d050400100552864482184941c00c200005005140e0a103a48843c0390f0006000103081035030203c80700d0300310b0030042102c20310103070240707003014183e01c0d0280c15a40a40f0f08841d920f405058241c11a052103801082921480320b1420090301c0c6944c0d4078401e0180b003c0c01a180039045210782200003411411441c1c40130b020307226400780070824010741c00036205004484903c1e9400341e810900303078000f240410034510b803d4a8120182c0c180644441c44200d0190156070508ad9001101c0140001e444100e8800a41250341d2a000e60302c05c1340e5034078100305007070082402c4800b09101450702944001d20076480c1141c40d1840f8001c024440c454900840d14286000240807402e640341880f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 725242356 1250 725241106 725241133
    0x60f02030405010b030304240903050102030a0902012003030c030604060b03180c09070c02010309050106090c020c0301060806010b16260d0e030c07180b0d0f17070c06050318060702 79
    0xa0f00700d08501c1900207500d003070b280c007900c803541c034076446a00303d904214036081e00c41d92427084081400650700000299102e0505142040040131a041c080340400d402001068241101c1c80009100782202030246056075101002e4840703650004250980c000d64139103002c40d444181ea8090750151860354010f00ca00b029543c010303031400000d51080341c8180c4a4000700254544e1115803900c0507503080c82e0210340500c181c41c1c15805400250040300c1c500703080c0524054010f40c009050344603400200c0003072006aa4611946440d40c40a010b2241240760400c0844448000820110100c07481500c03011003a00c00940036a400d0300ca06200c3d11150480056148105c4c03907103004140340149040c01031441d00800441c0320340c0c2d546640c40740c8403141400e180c180c00c030040c00b644206d10042c800b50a8000e181d07100c0c41c06611000038600c086074045202c14814408801050680d0f152030341c8a800c8038a49414614243c5043c1c10081c44011000d485e9560802800f1040c405140505032680061508006028 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 725243606 1250 725242356 725242361
    0x50307080a02070e01090b100518100c051203010b07081b03040b12360c0a030b01030309122316140a080609070501080c040915050f042f07060f0203040501 68
    0x7800702010500304114005960349141c05040755582d1070604c1580e55050b649250304061406c28000d0f4030030001d86049005e2f80d08010b4500203288103005480106554811000c5d40d030000b8002e040344d1810a200700c038002904030000705011102c0500e07280c03043c013010466034913642c015005070041c4000460304200c4191002d030301c9034100340700c0e048016030620959100e0780402022080c221103a50790528481c482034003031016011141025240201158032401c05160350b10f001c0c40f00300c0000e030000c2000500c03000400217411100b0340c0b00b00c580d410140e421940d48c0182c1d48800020309076008011078541c20b070700d100700c0100c002c000c14614503240f1b4103040c6c2000501c03105c0350312480392500312404002c8600b0300400c4003000d6034801d08155296840c1d074021b01140780540c0e00a03480031232401c0146c52522400304050012120110340329a8040c04000620dc1980c041000f40e000c6843c100f62860340310030704120541c941c0002110301c00e0400c421600c0754820b075913002050385910f640c00414042070101c2030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 725244856 1250 725243606 725243609
    0x12140313150506090a051003140606090f07080c0f0c03070c051306050a050d0f051014060627010e18040506070512011703120103051c140d09050307080a02070e01 71
    0x44100043c2c0340c40004202e01441c0204070b10340c41d66a07400000c180b03001760300c11900079640290211016214900061396104420b0764010300c546611000104d10520100c0401e2080240f9603420a081c0c4074103509950540000c4074a0745001c4c03080c0306401d0b2104003003018080c00e41c0290b20050381e00380b51000340b0076207a00ea160300300109401d00030248a03d440c0c82d801c40044400a85031108905500c0c01c0ca51042e03c140e220040041c02604608800e400350b80c1c014100011085c000f000702034031548204070f814490010800c0b10000c4010865450142c001103c1a0100d01810704548100000000500c40d0700c01038200008441403d0a00060000130005994401c000c0e0070b21b10f1074807055260510116005100302c552050032004040656a001d000761015002c0900e0324000303d507101e2a1a40d1101d14051280f144000c40b9000380311024030401a012840103001a0a46000496101d000107424210410769162204204040000c0c5131039000b004a040c0c0740d0301801d0340318101072410081d03c1e0103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 725246106 1250 725244856 725244893
    0x409090b1f060504210803040b0a060f030f06050a14180616052b02040b0c150624040b0f030601020706020115140f09010e07110f070312140313 63
    0x50707000a10016400600304c0702a54640c80450031411202d440048040c80c9513000144140c030040144810026400c2e10300d401780da00305a0502996844100401501c1c48900c009004004080c0c000004034a16078005a042401002c001c12994085040c240703000e841561074104d954081c11465144107818820590407425424084071600c01c0e41400030301030301406090003480360b81d54080c00700c285440501280c010084220643d1616515249604203412812158001c1d0040c14040c6031001c02a90845114050003080c0d1000c0c0e01480355452501800300f40c400c01c0b62201000042501016a005800304110300f1081130740d0380c83c0c6100024100007007640a0015a810905400e180d41e01c40c0708054140c601244802090341120b10000740b6070500e01c1c89140d045440c000c0042005042d0b2130b07145100701c820ba19100311080411100c07036981d640584501d15244c001c0c9205000084800d518910441d50600d8240d2403050a818a501241e00a84001c0020801031400d2004c018011881d003112100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 725247356 1250 725246106 725246161
    0x2309160e0f1323090706030b04050708042009040602030907060503040503070b2502070f0b07020a031e0c1514030412080405030f0c030403140a0c1205030409090b 71
    0x1040018586180038000980c07035030402c040304503502020001103241c20518144a0415071139141e11481e0b0340c002e03000020306203800b4400c0d5003081d015070390141da91075031281c07a507648130348a1106000c00c103061044100b01141d6041e00980e50107100ca400b56002d101e00590300d0801c944218a4a4119800501440702c02d004002c0400d601006844500740c0090301c00071280d5440382d05603400c6d02d00e001c00080c03c1d01070442c0d9201441e80024804240c1d0f085091114000352180b13110060b5004420000750710040e000f4060000541c85d40700e89000407020380341a0300400c4640d6440303445144039004409000310007543c04c54020390200740004a0f000400603285141013036104d006071030580c6001034040c4610480070604011b0200700b00c91703205681c0303411140c41d0403000280c00c2e22503100d40310688000380720b02003030011040c0c080342481e01c040d8403801069140780f400d0014100713924204e1061307525000510001490240314003500d80039501c2a0070707802c03082c075044400f1040450580e4000e0036010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 725248606 1250 725247356 725247379
    0x112021b2e0c03061a030415060b27041e0b010e01080601111614091b030403120f020a1e1106070c05120f04030c0602010b06042309160e 60
    0x742a080921034074102003926a102007040d80500103035405000f03000903084603a60102c3c1041d002c3c500452041054080e800b1b03540d006c0d40f06079000b600516019401c04c220480d44d070642e0502c40c0b4088c11007409500b0540083e03100007011640c80a1005502c1c60810300d031400d03101028811030045440034201807070a84524000200140030040883c0c3c14461380d00c0d40c51189203004c02c08010141032020407204c800d51500b0083d9400081d44001c2e500a42c07002d400305d00d101c3c0f00707100d459401e26040500b15003036944a4404031881d000279003201040668942d02002d81d10401c7c001000080000c0d00e41050f000b04000e81c061951103082c4480040208003004030116030700120f10250003148603d03200007214124280716080c00301c01502d04d19029030000b24a140031100341c025008882c0513140040c1d40664404050f03003a100668126580080208001e000200184070746070410304506c40113440c0c0e5501280450380603c016140182d40510122400f084194482d0003228900b238181d84024009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 725249856 1250 725248606 725248663
    0xa17040b011517071d01090302061e040306060608070801140f120f01090b1e040305030721050f250801120206130b0d0f0212150112021b 60
    0x151410700818000c1081c0c000210200c9226000000094180c00710036031041c1004100504210000c0d48190350145860480341780c258004c1042c03008590b00900160b2400000c840502102090007414540c610380501c0003001048092180d003026203244e8072454898204018040c1c0821016400b032800031303c54000311a129240d2081007101e8040544511603248800409030f400e0034000c4001e00d080d5072030524041c0070f0004542240703001340d44079069000f84284101d551011440e040700c0103008a07070200040f0311102d100d42c80c1034401040640c000b0f000d00014040d80030503130f80306851003054288048280103000390109150840358103100ca45000d0749001e070201400c2c082c0144604c408400c24200a001035494180880302910303103000008c0d04045d22101920400d03042000c1f0994030902d00324003000c2a03a40c40c42101e50807400070b9200b64060751800e025402c070358028111281045401c10035040e400c2d400f40042c0c02143c100c80c0c41c0004500603c54070b0307450116002c04000c00c10b810201a43c48d60f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 725251106 1250 725249856 725249873
    0x318040603261c0f060905070c170f07150b121020070b0405010c02011a09040309081c14070f0f05210309100c1e03060801020a02030a1704 61
    0x420b8040c40315940c44000c0d030344034146003d02c458842030a5003125a1805180040d03102c50500380b0303034400420640b620780c07070282e08071801120100702080040c107480004c0b95500380325110030b03101c00000a190400715401400700390800c00c0f080701d15144015040002804a00881101c0352090318004070041c0c8a9802d599201d00500100030210b564084007801000ca001400c2d00e150560b030300c0240c1d00c810514000d03450882c100e40959007540f9111a1010080c07040c02403c244070310146e40c42010805980c1000181c5102a02c22014030191580029580b1428040c2d1035840303d00404806401000403005490100307144400c0a400c041003004200060824001c000055000740d101102c1c1001450a203161150fa203000c0e035000c0350b4806c4200103050207072004500c41e0240c1400e032031141c684201031006840e1104d40071400b00b28294060700b4406100288108100110701c0d011400c41d50700c80c081401ca0344031484060060700001015000507405c9032055005040120102c881450316444600f036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 725252356 1250 725251106 725251133
    0x218010627060f020a0507030506040b1b0d020d0f050f060f04061a0309030d020403050c01090e1504180f08070b0108030a090506070c031506030b0106050c0c040b0301060b0a020318040603 82
    0x1d00203103010020300f940c400c2040044e9580d0100c1101c81d826264244260b940d0b400f101c084448200303100008490b090068001da510391040044181000c0403681c1001c041d400030820440616a00d00301e0310f8a50900e401000e0084841c900402c54905180c2c1c00d201c1da000342482c0090080d03082c0307003040190341c401c0c0000c450103860404a80d61a03465035885d2074118404c811000d01814004030f404030034000702080d40c1c02490301c03d88030ba902c11540d075984544c02c2d000803600000550840d41c3c001d003e60a060b04104100d8460020a14034030f8001d5a48039101c03104040c3c22b80740180c002c00c80d40304014856030322a0140464000440c20700c0750920005000050300d000c3d4902691000c6a004d04005c0c0e02041c8401440c3d006100300301030240842100000d02180c40151070402c103100001030000c8c001e500326466a8008005400500071840078800a49800161282c041d176948100041851840f80940300c0e880d04d070350145a8440b951902002800d00003440301e03100d00d2500008100044c075034000d211 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 725253606 1250 725252356 725252369
    0x10e0a11040b120a03030606030510080d0f180b040315050412050c100204081f1505010e1f021c210c1808010608060c040515160218010627 61
    0x4125202c000400d510506900c1104420f00c40c0300701d00c3c0c0405402d41c1003541076803119074080243d9550b0595514800300240300b0701c42503402030001200d8084c420841030005948a040034010b40401103080302d400e020780c0d48020b03ca0314020909000b00605030b6440e403c00300343c04a0500150071b141c1c8442103800341d4041c5401c1404070009110610442c1441000507108105e41c1c11903c40c0c0d0769814407900c450701d2020801188103840902284a1240d1207055034181c4481411001141030034011b4410503920160706070f0010300c1c0715606011103002054807003580000c2d4042d28008090000c41d1442c00c0800300191709000c002072400e51300e80d0303405000e074501118400300071a58400032042036601c0f10034070314081c20fa18031001c40840e1041c81501304004a941039021a0a5a035a41080450602942c080d140d030014401141d17004109402001d8810019400c05400321844180e000842e050f0603041c080c854080c007100100003280e0000403003d0b22a1160350b034080c080b454100d28008691950240c1d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 725254856 1250 725253606 725253611
    0xe0f07081504090f05210f0c0106030c060c0209090f03030f06182502060c030114130c080105120619020a0905060d09062741010e0a1104 60
    0x41c00354450018111851400503200f0030074000a4203242c01c50f80098441030f5054440d00b845503584180f00c0b840741c000840541005030030900c4e0030b4040222507102024212003503488440220108640c2c0075520000d11098540b9010003000303105020760500014800342c0c1c180c014206607a0517080100480ea03020100e90164109592603a0026110032001c6c00d1030b000b508a00000c0005408105c1d9075000100e070710924403841031541032800c90356104115101d111015042c801001049007031b140140030001c0090100900d82c0c00a50b80c1e108407030400d0304000001305008010001d50404c030340680d0008010f44e01502141c60162121801d0f050a45411150b03c0d50000b0740343c6882e40b14240001c00340038020403003035a83d5503c2c41e0840103050511000e03074000f440c000380300d03103002e1448000c0d98417240c4040e03842100c0305058558828261000c06071501156560150440e80043e0600c40320441ca44d800700307900043c180c214017500b1030300c0c1c07000c90351000c0d840389041202207008603040880000007203802 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 725256106 1250 725254856 725254861
    0x60409020406080d081b0406021207261e070f020f040e07180f0b100c08130b0a02010b030321100e13030f021c0e01020106051210060e0f0708 62
    0xc54020080ea078030210f164000c40c40a03480302c1e43e00c4200c040c0102c5d802042104c04840c00007405c0c83d030307124510803000980c0c045050300102d0000c05020308a407500a5010828965001c0d00c140c0c1d08020900d6106811000002c62960700001049401405e0610061250403c602ca9850200d207030050000a4480d00c0301c5c200f1031519998640019112030380d0344090b074411642e1528821904483c0290102c00c079405d080c0105000d81c00c82c071500502020042c40d64603c0d00811806440d82500b881c810750300324004122200055007603010400c010400c20041644d507107610f031002801c5234814980c6a1083c0c204010b10700f8980e00e210448160b81c0035400910312281c5500210038280131203075114800c46500a0108561004040740e4544010b00903100c11594261010040f0b80350751480038081c1d20b04c400403036040c03200ea1240340c5d54191508180000034100d9203410014581e0406411641220350080109400348884ca00170745008281c0d40b000a102c45c10207503175020007080700401071010000e58200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 725257356 1250 725256106 725256109
    0x61e13060f060f031a06060703080903070203150712140c0f090a1d0a0b0102030304031214180d020304081b0303041e210c15090504051e010f0e06040902 67
    0x807074100c411402c00c8070581d103507114100c0b03a04520042e1032148030210400e40d484030b84d130b50003072140c0f00040080b0b240007071079901a00d0b030b800701410110052009010040040c0c60400003000030f0400290f50a40e02c0c540340100030a008440d810302c1c0c0703c3c6403c180058440c0001100400c1d0040c400300580c54891820545c1905203000c0c41d0b010701e44c001e01d070000000d0360b540c00081e009600061a00d00104690f5409400301c25135000c03200703290059100308001804203220303200319041d018030142d0105e0400049441c8149030300f030944150001c8150782c4103c0c0c030440c0041140422540c401e001641c182441c02c24140e4442c241c0c1103d071130031401d49102c000c09075a003d20031200075016402ca0200908182d4080200c122124022000b40902c015254450b44c9218056000300f15071009000000b070f41030400c2d460340c1014945008003400300b41c040c04106942d50b4002c180c400d00c4041c84803e032580400759008002001030740902601078031490103000c58003d40718555031000302a100401d10121510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 725258606 1250 725257356 725257361
    0x21e01051210060f080f010603110706020c010c02160e0103021504080a0615360b06070501050f0606091809120406050702040f02160f060e0102120108061e1306 70
    0x20000181a003046042010080d42c0c4507022081e80e065a45031515415103d0b029036088509840748032000303800100400036a4400e40280200032080d01c001c60070510340d45d0701c0c1c1007a40c10081c003400b0242d4440120010b102e504112034000351300cbc03170804000444d14088450002c60818000a400ac8103140c440300811841030b421200141103c2003160030362340b610300300140104185444031036821030564000800b49004144903080310702602c584c81c0100c2d8040c4407806609a201900303150a500d6411130003041c1c5c0e46a01404500740940000f14031450720b01031040419100400c030768400e1400b80101030580d00c0d04821484000c611541e44403540d02c95010b45407a0901c41c5005d1442d0a500140c00310b100f6038402c000d0404c0c0341c03080c0c81c2400010340c04806141a4000d047c0141c1c10740001c5442040070400051710780026501588001810f80b0a9444260076030f40010350030560410050010000c0318420407850307600860900014216120180000c8901c0c200a0080e0400d10011414201840300c00d030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 725259856 1250 725258606 725258617
    0x13180b0a0b090403020f16050901270c030f060b0f070b07030e070303030c1725050706110310061115070e0405090705120304210f0506040b06120a021e0105 68
    0x2000300c2c0e001d240c50b280c001d664507100c09000c0000c0c090080d21921402a070b200c00b2091780c000403c0d01e03409a00300304c0105082e041c202031030003980fa4000d0482044c0316427840b031900354520b48c2d03030045140b419801098003a90b00300e034001180740c90208410300100e400042514442503001180b00890b46a03101e0880140c0b2110f0b9590b0450701800d0070010805816600c0180c10010340e4891028a040d4a00440c82c05c0c2811680810390103411103210b02c40d00e1034103c0a80c018422820518104a850b8032450101d9103c1250b1003c03c6200009000d600d16000e50346e03070000c02c01480c000e43c03904218150a80c0b656648264515040748183c0441d180e0750041204a89a41014008000c149040c4050907a140f07514031400d4001d0745000c90b0746621100200c1141e060755440040c0342c09404000030302420b81070540782c007501c0c5aa050300c42e082c0000c20903c03086000d00c0c0150b0800065050210811164131451240c0000584c41541045d00584031601c0514000561003000c0756040c4d07403500113a460b8806d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 725261106 1250 725259856 725259859
    0xf28090e0321090703350406091a1c091a0115050c03072d050606150403201909091b0f09020924070213180b0a0b 50
    0x102860050000400809000c2c14650700115007036400b40c0251610241c032064a101c102c0350410b001c10f00200b40c1c00e002814108042c0d41c2d162920105001d4811100300f803105220680e400d0004080200d03a42c030904c03060260031038040001801d070000034800410b00c140311580c4085004840e141001e4a82c1c0e5021a54017904010f000c0c490f8104011301e03204c003944c00d000b00d200c2a91004078209001c0d1140342542c5010342c03807800031807911034280c649580364030800d54445e4402d0304480a510682050038151203040307114000030a0103003401070401c041d900c04044070b4200b0310400d00c020408198060208000c2c2070b100495040d10034000b20200f0b8011541c0015517410003880e40001501c0444c03548105011805201c0d81d858400d0616030368001d940c45446100d601240d400414004d1981c10b40c02480c2c0719600030b05420b104502c40441d40b00641d2200c0c6140041c00c00032070000c0560030102c0312002c2541ca008020819032440400e0700d44100c0141c1130107422100b02c2800212043d480e13034085588100c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 725262356 1250 725261106 725261111
    0x9060b181602030405031e071d0a1b120903020c1203071109100312021c050d0b040c05030a0f0b0a0f05030f010c0816020a1515050f2809 60
    0x50464600103010161258019942220344444000d03201100780c038181d81c1e004014148403005134401920071801181030002030300600400192410003502600c4012800850140c80380ca4281e01c12412190994050750090079501d81c030f0b0780b103a5030042410303021031001000014031480c20b0400328600081e020700c0c16044100d440c00c40c496040000040e003142e51003511b9180ba01e00d14a01480004801030f00c6000224540b4407041c000100c580191180e0807186104480c9407601803080b100d5140034003008440464800240241003034914010b10040700000c0da0180700807150600001c20718400244080440360343c1d40426040b4040903006072000c020020302c060300903904d4903800d59440e582440b50381d20034480c500d0303d000a10010b002d082e4405a04d81c6a07981c0c2a6180000803002c003411090700c400714058040c4040000390145030030110900d600000140c921500b55480100250b0b64001d9841028030740d00e60402e81c0e80f61120740e0340b1504035411681c25409a400740c0c4c0d0600f001030300040000b60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 725263606 1250 725262356 725262379
    0x30706050901020c06040606050f2b03020a05030a05120612100e120d0501090c11150406390c08030606090406030c030818060408030901111606090812120a09060b 71
    0x140c0e541280090700c0c3e0440b0ac880241050604000600ca21411606101c440310b411014a50580a401780c00e824024010b8a00c044e0b110b544050956000d030b10450301142000c00c6940c000641a0f6202e03910000a89500c4080418040c0c140e41d01c100c2c855100242e140c40f810381400e407000074042c9090143c124800c0b19204ca154810031406010300f4020101c01515007500c0c4003299120303081c100094030f40310002c0c0c04d41d1859905100040f01e00104140c41007605c8101c19031654403070000b01123803070031544c0b61290004c01d07027141008420168002daa00300100101204081460b400c102e03508184201d4049548500000c0803501a020941c00500740c1c000c0000700009009103140141000c4d501c008d8060403400036802000b00c0c0f406940122a290b6005220880d0b5a500070541c0d030b01041c044008690f0b0300000310700d207800c40c610a41c00010000e1890581000842410080b1114940c9489245410404c1d85035094602d0030f0000d103001280d40d25550f0344820b000030380e44100840f2401508200c0000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 725264856 1250 725263606 725263613
    0x1002061f08150a0509060606190e09010e061008061c1e14060105030304060e090a0f0c050c0c0307060c1212050c09010f020105040203032b091407080a0302030706050901020c0604 78
    0x40000300d8103060441e013401c2c0050188813000c6800d030b01c01e01000745820b082c83c45051005500b98a40b08064040c00f01a501d1040302c2c3e076441d1681c600818007521b07003200e1441c202041c002c807401c0950b0418203125410061110554800400a04030798a040604580150500301182e01c0540190316a00e070306562042e00f02400480e181540c09480303014103d40042c0da0740d5043c99580e1107140720300030000e03040781d6071500e0915101060907084981d240001c04d03c004150508030460f10300c481c070340d80410400240b5988400040c0800030322004102d000d00b030320a19080000e00841c0c040c130b80091000001d100d110702c60b40e0003120400c61140120304100b10070701d403800480040c0e1f44a55aa640843d6400400c41a600d205004903445103a015010318100300032602844080030943c0480a0404011180d03448028502d2095111203401050418028140400300600300180c86d0812886034110840040202c3e4001040341e0140c1e5000500003000ea40c0c00785d038240280203418240005014100c18807062 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 725266106 1250 725264856 725264893
    0x91e0603150315070c0303051302031f140105060307030e03070c0608011a070515060f1503010f0e10210501230108010608072603130807051002061f08 66
    0x107038019021200d8007240004a80c6004904407590800a40c010940c0d0b00013910a80100c3c3c1c022840800304074030300d10268000381c00d24048994141e641811074941e1000c1c0d04050192920800060440381d03a0740d41007002083c200d10005080906154a4046182c10103004100702c4024681120021405903158034000b0280907081c4603440d1114800c54070360400c2c038680307000c6520282c0e20000030b0000d8842080b0010389940300924841c3d1020103010040900c0e240c20301032294100b508403056683c0d60410307140807002d880b90703040701488200b080200080503812007025010386a110b40b0600340e031b203140300c950301001100110003800c40d42000a1042c3c42c903029600416903540701e000d0503482c0d0380c0301c7c4882f500f00c0320389128a0815900808041042089120102c4100d030411800ca40b0b2035407103014a03e05d103030b0000c1e1800ca1815002c00c8100280241408032402501d0221241400000c10100095550002810340e01034000d03403003115103400380c0d40501d00b4010041c0c001030343c410030f41c90440100b2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 725267356 1250 725266106 725266141
    0xf1a0f030f070806150a1107080709021b0708030a030b1c08030f06061806030c0c01110d0e030403030c08030603010e0601122904080a03060e0a0e010b15091e0603 71
    0x40703282000800e14500e41503003402c0724140617803511810079081c440c00b200d0305407015854913900c0c09943d0004c107a10340e044c0002c1014000e0100d003d640d8014050601058418200d0041400d402203002400801c402108440350031b01149008a0b416520000241c0c0000e210200e040441d0701810640080040110141d8416a1040d035210280da41c0e400c20312102e80700304d001140c900c2d07212a0707440c03406141c11005542c00180b00e6280d1824060308008082c02c54901000031a410b10002c50f0600072003507a4003d050301469100c010f5410545980d40103043c10281c444d009201c1c0c1e001000080c5280c40940c002e5018600c01c00484020f540d64403860a04144a10000d880498064540360f0781c2005200b5000903c1c50050340f400140e40c0c4984400302160003a0034007900301074540f5070009000d00002000e6000d14800c400000e1074840c08200d290841c0d154401d4140900c5c507103003d26620503500026904064000d5420303c0c40713100103000d40700c1c0c55081c140b9403540c0190048182700124980503138a06 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 725268606 1250 725267356 725267371
    0x1020118020a0909030315090b0307240e030f0d0f170f0403051c0c080717060f0613030503071103010608060123011b03081f0f1a0f030f 60
    0x4204808010000140401030401a4010103030940c204180740140e072202d4642406441d000464501e90703080302d0707002c804030f40c0000321058441480405038a400e005140c010300900c03044100340c05810300c40f40d0001180000380c3c0103000c01e80c40c80103002c0d1014000c245065000006503203010001210140441d401c032500c500015146100c0080c4064034180c6190154040c5a5503c81641c0c46540840f1039500c55414203518002c040d40c8042c108a95000e00407480c035040d2078101661403c06402809104940ca209081142c0c030800c1c0720070340c0c50385001000d080c0750954081d565200c200c813903540300b138007103510081c06840001404400e01079000222090701804030001d001e040d035140c0100341d48120a000d9104065144907258007266540f0712004083da0044c1803541000901c05005800e4080b80081940802d60a00400c500441710851881280d04410819200b2606040040d031641c000f81c080c10740d040c401179040062000a0409032024254134021143c1e8070302d0002c40641003c8401c1e1101c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 725269856 1250 725268606 725268611
    0x90603060b0708030a1104030c060210050a02090117040305040807090f0b0103060807140a0f1e1a040911160302160504021602130e0609031e030c0307050a03022106010201 75
    0x1181c40c412500498080d1500480d0301821510b40200d02c900401ca504030400c6680d0003000000000341002048a006103120b0300170306100d00d8920369980503030b50002d043d002071034030401c04500079a0704842c0c40d40010480380c080e000680d6907403400359054800c40c0c000580c0b0380719001e0000b40d0100d079a00708612141444106001c0000c100b0010340a45181d03004d1f800c0070340c0001c41c0c00c0c08650303035094030002c1110008220b0b100066588002c4014003000d80c00080400ca40c030124a040d0404c00e400e4035000b0007001c032854422a46929002940340114061043c10b0303600d03082d400218110200c2611040d0501442c100b00c07034202803402964440c40f2211303000b0b00c440d404800013a149824404c2d00c20109440c0342240c90704075554200408102045002d040460f5919950541c4800c20009540702d40e052400550350742d20010950320071100034500c0d10081e0402001000302005c8002c064981000d21b60038080d0b2100310520061740640140300380500810f0107181032541000030000341d00d0084100f80c008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 725271106 1250 725269856 725269859
    0x3052215180201180e0609040f020612010e1b03070f020703120203091008060310020d020c1b0427030503040c0e0a020d05070e03071e0308030f2706040b04020d080a09060306 76
    0x40d415080c07103204405d403d09413400090000e0a1100c1c200b80c0c4503100d107080b5a0801c64036400034406070014400c2c41a0040300c50700501a0000039000150007000c602c041c4501c901a43d5184e402e144401022001048000c040581c0c0711402008082c02960344802d03500760022007824000e41c3c9030090080107200742c8030040813904143c0034440942c0541d4002c4c001e40a40c41d4000e07050400fa510455800e46a10780c03c0040b100a62801c2c0003510440d40703c1c4003c5406030000c031040109480040f110107240340c80a000743e5154040c41c650400c0c4040d45070400e0f03910780d070b85c9050107183e25646900075100d030030594003000f900d14200d41c0101010041914108995111084101d4814007480c2040da095440044144800d490003042080c1a80f546003034105c1d4582c0b80d40e207100c2070b03400680b821250101910300303000000d0b40041c1c044c0080f2040f460000444e045116440c1e55408002c1c1026203401c2e8101e0104041d515502a02c103040da4106051340e545018200d001800d000c924440c060019281a13030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 725272356 1250 725271106 725271137
    0x105090102220e010b2b0b030705180406111e090102060f090a020415080a050a0506070e0a03060504020103020d1112010515040612150303050309060703052215180201 73
    0x2c0100c156103a48559610076800c14120000a80c820795a2000140c1c64051245038100b49029043d00c0720b4a510340410103600701403d040c0340101b150402c0d40700d0748104485503402c4010714485940107030000804545070300d070180540403a00c505030130307a01341c5000d02c9180c003840512a40108400311003a8219810f0b503039141103030b010800003030750f4400c0140c10032640d0380054503164000780c8520000c0c03114050b03900e944103011440c12a12180c11651074024039512424860203004039540500c803030504800358442100001ca609801c2d0000610ba00e50342c00104c2c065922aa06584c02c5d4072120100b080f100c01a003032070041c15040011b503200034400c10800440e29042c01b040c0d00c1c01101000c0700341c1d400c050800c0015182d41c040031025100c021380d42c003a1001c2260f0a0b5050100445c001e40704d03281d40c0c0c10320003a13003804d003a4000c5c5030000349418481131241c288590fa420005110712139403034a500c407101d031920b40d0800e160854000101c034140b940c04040c080040e0900d49016200b41c81e11401802d1844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 725273606 1250 725272356 725272417
    0x1b0902030705030105130f0e24160f0e04060b09030f012c0c060d06180b060702010c030e36150103090201091505040504052202010f09080105090102 65
    0x1c500d040007550520041115080c25100030311041ea181c2408281c20318004150011901a101c141c4010391101d034600a10a070402220300c1032036078203500c01c0c55500e801401450329640b015403031400c103e8101c10800000348074480900190b54020070902105649070008a802d030403010040d4031a000d00c2003070100015051046406001a05d049201c0d469014018103d003655130380e0014156010320341e6a120340c0d5031480000c28081c03d40c0d040000e541d0341030000c020a110040829040010f00d094103064036035580340203881815609290459040815150495440b0754540e4003c1c0c01100b408201380d107824801c1c8403d981d04110032403e62241c86007003001d845100f01030394010800003035191902c0e00c551090700801c00c040d0060610f00b1401c0c0e550307103400b08004c3e412814403000510200f0280101e180502485800030240318000d490b1107402d44282c2e0350391003807040003030611802c0f018126002e405072000400400522008208030b00c4e103014824080d60100003031401109406843c10900480d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 725274856 1250 725273606 725273611
    0x80c0a02040e01330e01030b33130212042616021005070b180607080601080f0a0612030203030a0b04150306020306040f020c0c0901090c1d1302071b090203 68
    0x606843c0b000c6103058a0140001d0020b0130140c08041c2c11100120f0802842d032189802135100d001000700a1600009156240c00303240b01020302c8000506800580d1010028801009041100da510301c040c00c00d03503608003c0c0308890708401540700c08002c100911140e07024078900c4407004881a21040019401c1d41c01512419884030155000840444090300b0310380c000481c0900c07070b801d000d480e10a1a49580500d10b00031903484424962010b42c003039808100380304040d000000c50402c2c07601800c2540010b00302c00c80041140c0b240c4119000060901030141d00b0202c01400c1c0640042085102c40c00e000b9102d6008aa011900ca8189401c0300002d04113841a2160061b00550010b5501d0443c0d9884010350b002070407443d0700c0ad0f100c090880e00804030f840100345055095004042030001e5009003c6c00704d0050b4040103040b89480403222401d40c0200c01c2880a034400744000b03100d01c0b1107600040a6039041840e026440d44007141100400100c150420340b180300400c1d50901040c5d803400480d0691208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 725276106 1250 725274856 725274881
    0x5100503060315061e030307050102160507080102031e09013209120406121509090303050a0507200708030d0507110f0d0e0105070b070e12010b090f04020d080c0a02040e01 75
    0x645c1e81d40850981050f003208010190703446c207501501d80500b640c0107060404088d0030881120800c018082040300001c0c070041000f5402c510340041c0c2195003d80c041d540000c0405064001001c2400a60000380312000302c80400441d02100544035050030b030a0704601c0074251034407001c40c0701c1080004400c12a03804004005103000d05000d030844a05036060407645d90551a0403101c942c4542261070400601441c0f1800940b40352507080040a40b080903220705141c13443d0070240a9051341c0102840d00000022110b41031114079419081e14040743d40d031007007196010204840b08401c1880d045203014884540d20720588103120032020303491b010240403038965540030030104081c0d140103005103c20701d1b105040550400c040d984800b40142c02c1107232450002181c801d10742c101807601001841e40ca5141000070004075410a010034107030040509020001c50040d0002811503603107200503500307036502c100d14a072200b02100c2c02079500d4140c40c004a10450621905c91910041440f51b0b41018a6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 725277356 1250 725276106 725276119
    0x709080c0a030201050c2a010e0609090103081b1e010b03060124030f090506010e0a0b06030604110f040e0f07030e0c0d050705031f051003020307090c090510050306031506 75
    0x61580151801c0d4440401e0310b146000300424000011407d80d880303803000c5840b441c4010400c01e00c0b40010510350305c180c0000e100e01c7e01031006080702d80302e1680c003a0569500c8401350303560f041c0c01c591011084e0340d02c24224a44e803091501d0700b54007402d096921400452400003c0c17100c184d0030300405803078082c00d00520b00e40c1c018840d2040c1f000301c180c0780030091090700d40c2000120107140e001050203803203400c10181c80d2a444030004011004c601d0301042e90290040c1740030003030078050000065581c80040c0034684a40d03128070164003544103c104441c05011000605a9502e540385060210440110b541c01140b000d108001600c0c07030301a0080d42001031002001c1c0454594103c00c0000c4001108015507107403103400800b2a1343e840c1004000d40c0039030580c0200a4400f4015510b06c15120b0040c850400b01c006084108016100010000c0944070841e5000c00c103004038140843c1c03009aa030348143c0d88481000324484000d50400c00035401140281c00f65040c1c0104004071500200040d5402504400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 725278606 1250 725277356 725277359
    0xb0a0605120703060b0c0604050c01030c020c0423331c0f060c0203042c010e0a0f090b07021b0102060c070c03080a020610090c170405011e050709080c0a 67
    0xe41c4a541154003858500340002d04076240d00345128143c100e466521090346c0700030280400d0120810684a0800007440c051020900d2908000d44902c4041681d0303000310b4480c0c801c1d03ea607013aa0015003100c00c000000040c038a2074440e20252241040e90507044007813101d0340c0951030302c0481200d03414040401810580c3c100c2c80f481210710600080b031005403044040300c400301e0006100d9004045d06112560700440c0c41d02e04040154a6050b1072049644801001140c056101480ca030070950450302491043e210319030780c4022503005081564040d002043c540003510042040c0c00c1d00540c0601c0c2c0c2030b400c58141048030344820580000780302103d40540d10a0001a1942800388020003c00c0c1c400d0310b00049d007941c0c0f9620f80300c0c542c0151140e0400f60300404104a41803503010209002802408424842500461005002c0c010301056801c4100c031260b0005007442025040a24041c00da06902c100302825183c010000b00025100600001d00032880021002c0000490201401c80180110360b86c0d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 725279856 1250 725278606 725278627
    0x307170109063f050709061d04030305180d030207030e041404080f070804080a030f080f01050d021815040b151b0c121c05040e13060f02040b0d0b0a0605 67
    0x1040c8aa12100d4032441c3c0c0050124600b10309a55a607000d00c034000030500241040846d0068510a8120764550b82d48442c0782075905001c0300420341c100340c0500700003c46403181e41200c00f00d401c410082e02590310682100c800115455402400c2d131500940e6580d880202c214204400d4070b60403001907480701900c0d0301280200c2e10090041c04130b010b1207201e035850802c440c2d8484455401540c042070158000040b880140354101a4440940081c0d00e000c807201e180440c00c11807d100c06015203405000844003032401c54640881441d000d40d0f5074003181c40145003c0040404101440c070505006e00d040280d6101903090141c010103180103140300c024140909910185004440c60f5400e911920564800780f03030544030001c1d00014403021901800f04c40c030b1401c0c0700d0099411400603600801c07508000c1080610402240741703411201d02500d4042c1c502d82800c3c030300f001d4060000d0780400e441c800180003840594800c014a0b01900305501481036010400c10880248500d100f1107000c13910401105030038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 725281106 1250 725279856 725279909
    0x90c090803070314040f0b0408010e0309011d01090504050114031002090609040b0d08030f071106040b010b03040c0f0b0a021902060a08040c030b0a0507080a0504030905061806030717010906 83
    0x10000c4c4419050510307568001080c81c1c0c59483d400b075600e0b4180040e0a001882c000e00403500140d90040c000d6181a034088002804118100306540039100c92a03491025684a040c4500003040000e0042c840c03075848101e0000390002d6400b103d4800d01c5050300710340300c440782c5000f940d03003561000306441c0c10039182b10140b101030702c0d001003600d6000c6c2c1d15060ad41c0004e25060f010303500418144036801d803503182103d805403c03001a00047c0307066074400803c0100150020300d00760306480c403007082281c8035140c1c0d00c0c110081014940050b400c6041520000c1004003000014016511a581c03c40300080f070142440030000e000403c020390000d404100009006019603541900207101e01920041140d50307895821009405803543c01000780c54405100715540d000d012241c000c404070360104020705150703401510307842c901d218050042c5004074a100c00c250002c460700310007400140515907a40741808005104581e1641000c509281090000c6080d50240c4508000d90340b01d02c824243c0362000e50b10b034102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 725282356 1250 725281106 725281127
    0x1807080d0f050c0d03151409040f0227090d05030c0d05091509010507170603060403030506030106090e060708161d1c0308090613030e06031509040309090c0908030703 73
    0x6000b410840414a0b0100b080780541d00a0150390014021914264840144c000b40d4040d07401c41034088005a46a5100d0607004d40150b44804101140051403003c01c0c0c51401d4010001102040302010b0760002c008042e01c0c40c42100d00740162810001c48100a545038041130f02e04003c4138409100c54404141d040d440250041b076594100c400e260111045644480c904aa03a11131507510351050000184d00441016080e42440e01d061665281c04000721342c1e2004010030140030140c80320081401078800303500180203803150100901030b52260b030b00c0040c0d07141825514000001ea9841c005078803800780d00c3d195103000a059507802154140c18082248131610202c8a552001ca1303c2089130600800c00d0100c0c4445129484452051600d0300c0700c68100b0300020048103a2203054006c02000a903c9042801c401ea82200c80039100c0c0c0740c0d54a41c2e4211255824103d800c144502e0a00044c507801c08a5081290a20001405030418514003103900b02c031a442411401c3d84180008400240030710060f01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 725283606 1250 725282356 725282387
    0x60c1f090b2d01090f05060109060c06091e0804081005010f03120513060c1101113a02100c1d0108040303110d020903070509010f0b0a030209030a06051807080d 70
    0xa41802c45100d030400d41e40310a038003d0000c2c580e100403a03034074103016018403a8454400d0800184052500da00549008200c1500410640d82c80c041c4104001d88000382208211101d54084407440d01884c2907240c613031087c01140350912517211070180083e1a0b00403281070b201520800f080c07151440d03613001800c090100b601001d200e802e1040400c2205800406030041a02e6030320071000080508146466009038254181000a0f000303441120010004100700008910441c24081c005c1c50001d800b403910342a18040050340b00c5201d907035541d1307034001902050b81175012401c2044002c0388000350755556079000b80561141c44044071400b03540c0030740403080c0e0003402800c0200361800501108080c03a84850096551944e0200b601d01075030808100c044080c0030309481e030000c15418441c0e0f040000130b85100b09852000002111b82c0351921a070155000700301e026007100d141408030b1400002400c0e048492118003449802e54074081d80340040c43d08115001040540a884a1610101d403075210305050030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 725284856 1250 725283606 725283661
    0xa2f19051c110327010c031b020d050a0305030f0a06030b010303110c04140702070609080606150d050a021c0507080a021303020d140d050403050318040b060c1f090b 72
    0x4016000030710082030706494840d180c40d44044c94a243e20414103440d10050304010803900072000094011118001031445415060549656031001030141c0e22007480c001d24900846030b8803400c15822002a50041176410082c5416580d80081002140c180741300241100f14601c00400c00b00317001e075284080b03946584051342c80e5280c000d4041400c3c0e9812a01f104000d111540c10030904d10b6050040f1406403c2520300300041e5849c11454690b50030004c0d1609110700a941207840c1e8140720003048411281c64803105000905e08040041c0003900000c0c032a1061200c2c890700842c00602c00d01c40c440c482e51081d00c80c0c02c0540c54030550040203410a5207802d6408a4621020015a03501c01030070221921510210f94240e030050403203800c29080d100240c090240900c41800060000700a59030a4148404810000e40601d000600a4840c9258041d003200e40000c4422141c01301244004101003c422140f4441107080007400464000b02c03006029246088003140c0c6034002d9000c2e100c0d41c004c222611 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 725286106 1250 725284856 725284877
    0x106021c12020f03070903060c0e09160c140708070918170c0102160c05010c0b0c0c10091a101404020c03041a04090c170109020a2f19051c 61
    0x103c120b41c802da6000b40850315031942002006094099000700d40768500c1e00708542520000031405500002d0981e030f4203640055080d002c0c03544218000d2201a0300f00c0c0a806411307600c0c4d640326407110b84501890085020b0741c0000305090145004544403141220502140c005040d20344c10640c030210350801c100c5140070408040d05441c24000380c4043d00760440d0b2000700301c51034905807403815240c2c0d02c003506124040c000c002c041100703158141e901c05003010b0040da50b0324880c0c0c00e080c140003030851108040b626181c40101480ba0300c041c4451600240c041c00c10198a8241a07542d00358034a1184900780c4141c2c4529100764200758001c0d0180c40900c01c200c0b400c00e6116038031203581140c104051400031002140c1086000494040c6411040c080e003071150400108061580180f10305010700300181d070f00000c400400380d2090a400e20341e104101e41c0c0c00002905001c444480e00c00c41c40c110701142c030804d842500303000000d80c2c80c07045c1558040014105801e801c4c800d82e40040070800b011040c02400a103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 725287356 1250 725286106 725286127
    0x8070207050a0f050108061203252102150105090604090f02130219080c0304020d1410060f0501050c071e03080c06070f030504051e0709060b0c01050106021c1202 71
    0x102280942100d44035001d0f1941440001001c49030000d180c103200303460100d82e0031101c0030301004070f81c10965404d00c203034a03100c1d1500c0030300400e018072000180140c3c000c26101726183d2144c094502ea801c1d0301e509546540b502d8404803400d1200030b0140540c01701e00b4a020031014a00755200c2c084139842102c8507022240c0d08d40000e20340110082d5040f40254000441e181044142e050402192509041103006814082c52000082c0001407000780990100c03030f90081448036031100710000d051280216044004900c20703101c0984200c0c031411394680b103800e4001c41d0303960098050300c0403811501d0080c08924500f001a068034447c440c40800500c02d03000000c40881d403907500420010102d10010b259030300b08180c006080161202032102003510300001e0100051012808040d080313445803d20701642d02210010741802d2060307115040c0c0d03a10b8040d0025030300c0c1c1c0450140100b222074030020070560380e075888281e86644d0070b52a00c0400c0007056480c12030b954002c130310008001c81040401410600c8406 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 725288606 1250 725287356 725287369
    0x506010b13090f0902030f0f1504060b1210050106030606050904050c0c06010b09010906080705071203270209101d1312110c2b060e07030f11010903120807020705 71
    0x90700f11840d552202c040d0020b6041c01c2081802c001d0300c0c10300600d14518031514817500c4088038000d03945004040c00100c0d0030b10031690050100194010541e840300c0048030501c0380d582c849050685c0301181014000900713103010788915801c440198494031303e0040542c04000040100800e2000a142c0c14004c20003420001c1010358080c2040860441ea80e0030100f00140443c2060b60004003080044010003842d16840000e0311202e903404400b0404031000f4000075405840c0b03d106503a01c810bc1c1791405006209103c0c0042030340fa00a641800141c0c49030100043c03201e0b1300d80030701b0b61118489140304070120310b100090b5512031014142c145003d5130580c1da03604844038400d4044005420078400065012041c000c400390409c08568284600340301e85021403005145210000c10f41500b03002c03807814400c407034001c542d1000e41d00041c0c41c806500c0e840c15850141d070102080e0780c00c5d1502002d000181d40100315550a40303800008041140c0c440440031070325048002d10f901e04500911a00040603103500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 725289856 1250 725288606 725288621
    0x31506031321080a0b0a06030c020106271a030a0b180a060c020f0d0e010c032f3a051902010c02010b04090c0902071a0a140705070506010b1309 63
    0x1a0a80c10000000740b8028442007019003000480b0f403a00b1881c3d4029035842442c0012120740f41804510700d84e134071070700340d0040010340d1000c4039079410411031140b140264282a08030781d0800c82c040112a481140003030340212420f50040e0994820580c490118190185c06d581c003444526181c082e5844c06001c0321b041c441d5010040fa9010b03112401700100725010302c07aa09440040000800711a0804480202100d580315413141c14000075421103400c0c14802e40c0d01103040305940b03140d0356440c12181280c1d084070b40981120006802400076802c1da004c0700d12035030400756100e1440c403800c0071580107428501c040d01204a07400d1042c200801c481a04890307003064518040da400000324096800c5010703080d00d0000031200d20403441c00c48220000f814043c109016a80d0b03003603005840303100341d1420b640d0b5008160412080d50307529004211041d03480c1e8200c5641050702501c4000741e9101c0c60750075074aa004804008040b50050341c01400680d1640029000ca051035544041809030f9809030380d022140107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 725291106 1250 725289856 725289893
    0x15020a0c020f0306060d06020c0705060301030510110f0915040302040f050a0608030f07061d1e10060e04060c050d0e1b06030106050307030504020402040f06230315060313 75
    0x2120015000d501e42211090100305083d406012145020400525195001c0340700600466001c108a004c40104211090187c02c01034011036480d6140d00705955610250042e2003032550511040941d071100600c160b40c2c080c941252400d00b048900c0d8200a1102c14038088088801000c0c84000003603600c50084621400818000080c10b0a0014003901a55915007158001c3d910400c103000001c4500c00807501030642000e00001c3d040c540c0710324a08007540b4120b8140c0340344540c13a03103d40100941d400d809140a078050494a210340700a070704400342e44551017a03503181d502090004000c105503800c02541603855140803840e24050154040c2103032a07400d4440c40550142900814600c503000c040d412000003142d05500315894628000d185120090210b410552200042021515290151000380421403804c1e180141c40c0c2c2002004d21040d032042c107010900200282c0c0600b8440c0302101c1c0074001010341407200341b0115062208940c0080c0c01391614280000e11240400e03000c14120454058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 725292356 1250 725291106 725291117
    0x3080c1207061515020c06090415240309031202070c0e101d040206160c081e24132d02130509070e040303150608010518010302030309060715020a 64
    0x3076034448100c940b8800d4100924a07070070503402480e102d070001001e024046c2c0c122441c5544007080000703d0003a081c03030302d030205240451603000708444e0070305e05607064400814501c0710480c800905048083d07e20340c2001402084140d222840d81d44581d40007804440d02440440c403d007542ca040745a0140c0c002c40342c81c2e00d400301c80d040c20320000750000446542ca40020104113641e080c1500011124461a0b8a280c880503041d940d04041100307503401040100503007015075a404a1744541c180ea82250441000d055001e503000302c410403003942c049800003030070f060340c1d060307080d0703645203800a8004915005071000c03240c00b000e0342149031030811032408064008020382e07041c500f00d1040c8a9002c00488800320044d0900c0708102c01c1420009000c401c03243c484200b6a000c0e00d035414280e0040420340000207412000300004541e150300841c8050403520241c41c032159034032400c0446a80034200b07000095050300201f1101c00c20f860f148010b0040c290155441c2d090100d08031000710101c2c1c2c0700510103070200780d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 725293606 1250 725292356 725292371
    0x240516050f0118080d0213030f08090108010b1309021c18052b051e0304050105040209060316090f061701050f010b1c111909090515010903080c120706 66
    0x40c1c080c010b800f44900300790300382c403c82c0d00c0c6550b07016454001c0d035400ca401107601140290301d511890f0100002907410084c0c428558106081042c101d6004020b00e502150801d400080c50001820490b034011801c8035228000f54104a654800381d40003028451128004e0714542c41482064810055003900c0500b40848080f03c03882c2c040d04040002e0704400442240e45000c914886d0754401c0340006405600c1d050703546814100302061500d251314010b00800740040b0411040010540c0258003031802240ca05490307590b000200b5540306400c1e20380d08100014000d00700181a1035401140c045484410f010803501c0d01c628480c0c0541c50240340303030304240c2e44030010b10140c194028132950151201d12202481d00080314000701001d0048080e6203002641c542d0840b000e440c00300306443c40c080d1190690301602098100051a40740c1a02408519510740b9010860808001e480304c0c1d455101030316040646407641c0c8862449070010903142c0e0240c003c8030440c0401141c070400414019104038800640c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 725294856 1250 725293606 725293633
    0x150503041109070f08130b010b0309010e01020a1d0a050301290402040e06010e120105070306170c090103140a06111c060810021602030a03052224051605 67
    0x6100040c5150260b45440300740100c031548900752403068030050400e0b4840d5215642c400300c207810012006044c24100c0d400108005070760600039406220300c03100a018509203400054202d00c1041e040101250308240d000da280118030010110100c40104001c1e1919aa000803d0a6440b0038902420142400140000c0c2c2c3c5010a0710b56001c5a0503182181410f003015401e55203e14050151810300c0148040c0825542e07031702e901c0309048039884000b48402c0c2454903000d0083e0000d4020000044000c040351805040d000400c00c1c00703000d0080c014896a40395440303c80c4009621804038949000c0c8184d8600800e84500408880e060030b052110359406c0c1c0200704021407a00c071414041c11605001e0104624200011225100d8a41010042c0c0d0b452107002203403490034a200d00250140a9014101c0602d50003c01502c01190580c2e6540f050009444100c08964141e015a040e0240c0d190000300b541c0700c2d000c1071607401400908001e49405c4101030340540b0b40c10004001ca4041d0b000b6190036208 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 725296106 1250 725294856 725294873
    0x61516050703123f051302120609240403140705240105041401090f0b031006030c1703070602030c070506190c1d13140114041a06160c15050304 63
    0xc10035000c0104a00f20021811140391285000030644c0d01c9031583c01280c0d050440300303403402c0219030042800c0c0d6644d0004c045141c5401d0100c4010149010b0a207003c0452203245804038040c0040c08600507455596641c1607444245034410002c142206010810008204010400c240e07a08982821341d4000c3c21014090780b0241608003e02881c202418000364001d103408079410758035400b80100e0246004203c100040241249250b854401d070baa0070000210198070180070386c7c0c02143c640300900d03100d00c0c45103031003c0f60741607260956004014030008a00a9406540c0214100089c1403618600f034549602c0e11000361000c0740c4c030110781081e015039141240b0500350300710500d080000c10080a0f005060718800303020211070042d5401341c60206600e807541e01014004440d89820481c65845420b0320542010062101d8003d0b4906032403d18402e040d8648480301c000000c0180e441c1c13820070291822802c2c2c4040b011078403842da8020128030010a000d402c4405012640c03001e460b89464106800c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 725297356 1250 725296106 725296157
    0x9050d0804051f020a062418050702010b0634060c020c0306240301020f0a020f120315040207060e0d0302090319030503040b151903060506151605070312 67
    0x1107489680b8039940c501c0d500452100905da4001c440000c181a5020f080e9511140c0080401804288001c020545400300c0e5a11a801e444030581000180d803424401e03808c840c94080f03000e034000004d05c41039502d04111074110301000c11a01d000860b020200c50600780c40d0081501c00c80d40075845015106c0d041c0d50400041c0441e0404600402c204c2c105680c4441c0301c40031000310300d14900c410440d030301c96a0302d003501112a1030088880c2c032039480d003034260021b4035101c03440c0000190b030151004100c200400d09050724000d200400c0ca42c00020790300f1013000001c0d8000f410417a607450301c44001c0ca040c00402e00c10482281e4142c0c4002d42d0b100c0d03101003014103001d4483d80e440007060b48080b00001003940a0166035200b50700c12101d417010b84403d042c95000c01118100180e000000c51015081d41c14055480b0b01100d12680c4180400e44074001081000155a0a902c0c040c800c1070003850804000c0900081ca41030051042d83c4060b40c60340c64180710a00e01c1490000441d094010140e110452202d00c0720 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 725298606 1250 725297356 725297389
    0x110a05070b070309080f090d12021e01140705032215060807031a0c070c08070611030c0a02041d12040f050109030807020405040212160305161802030709050d080405 72
    0x2004c010981e40d0040396006052050b400e208000c9802c03c9a40c445110b5003c106403c071361619121040c40400a640351001104d00e02a04900000c000118405008071400a00c840764030203243c2c3c0d56500d080320503810007090fa18055054641c40800c0c6100d03160315424031402066091100e40b41d41601606580c01b5903c074402540c0248400c00c04115070321060b0818010480d0340a8207600e80b00c404410138041d804000e414095014000111450f00003017001c21110789444100c1044080c000f055200d004150380240507400031001d0071300616142c1d2040c070901180004180280d100c58820601d0110b0580010b02c08030400117040c0030840c280b0707598000410003440c020300c1d60b03801d603030700c40c0d1407030003070390030083c05a91134030302083c00c47d03032410740036040018044200c80d403030080400d4280c2c40ba51544001e4445001e83c5201404510192800d802690300503800d810f200c0400d18440c3c00298401003036602003040e2082c0204442d1350b10400b4481440c0107249060300d4030b0402e8100881c1002590100c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 725299856 1250 725298606 725298611
    0x10e12010e0f120d0203100312031e06050915310b040e030703111e0109021002061012080d0e0a050c041404110103060b0d0f2319110a05070b0703 64
    0x98140d240603c040318850707045800d0150701d03500d8400c000050ba0a2942000348214512425214210350547c404982da018000001c0100080030100c401114458056140c0201c0800001081941e2003110341100b1400074100350340b52000d084110300c9000407080c0000ca0f5015000e4020714014031030003101240d4808031420400c0604410703000f580ca21580800605104070581070340350348901805140800320740302c89882c1c011805600d01600826a044d812031094a442514040351071001034084d02c102880503015203094200184002c0803191207504941c842d004001a14681e9583d0250f000100300c544002c1404040f203140150400d50008103845c003603484e00c1c40c40948401c003180c02941290300310a48403403401c07110004034040d22098100584451000882c035540240551141400040001040003c03aa005d40342e04080d100004101032500650004110030800340c0f2041e09a234010303140300160340703581c4010000f002c1d00800c030b182001c50f4022032801d06201d40f0285c8c0941c00784491408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 725301106 1250 725299856 725299873
    0xe010c0206032e0806011215090807060e060c0d020702030f0706080405061501090626010612060806041205090a18060608070f1e03020d0e06060102120f0711010e12010e0f 75
    0x18199030306014814400c2c444071f080120310603c2410b140c1807980a17030004042c4045241801d2155103684070200894407130340b414801ca1010032002c90024051280b41d01024079109000e450000650011582641c1c1801820340700300e60b20804204120040c515601c840080e8501810a58200500140000b201640600e410034490703034811618815a1040c0c2000031040001104407240d0710120701c259091030405200100d03119402102c80c01c041a9400e07018040a9103440c0310940f95201a140180b01c030711186040fa1640340140007504035280040c02018150f640c550591800110140003910210758502050206950012102c0da0091981c140441152680217000303040540c2510b0074110005a0211241594800d0b0100c0d01d00d800700d8003003400444d604000441d22070314151907490140c851404002e1000400105039103e280160003103e062058544950326007a0418208070f04100d00b000c1604016640d01c140c509041c0740f009c0001030380e00c02c601d061603c0c0c0030300e442b00902d8aa110506 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 725302356 1250 725301106 725301119
    0x6080c0705060402090406060312021c0905060904020304020402090a0306050712060503030a0309031b08090a0f06081b040914040c08070b0f1614150106031b0e010c0206032e 76
    0x40c0c0b9074102d0f605640305c0700c0e165181c3c285030000301526000113080340c40d42c4402c0c07050558006078112020816002c110700b0111040c038141c4040b0500c0c03080c2900294148589015031400394050341d84a030014101500d803c010b08001101c0300030030341085541c29030380c1c02030050b5244e000c0c1580c00ca60104000c104080390400d00042d03a80d016860603a0209a02d544000c0c040600c00c852550904903141d5820000b10094600b00e2442d4000450450107480310420001c4c040401840c080100d0f08192588866910344e03003007841900640129103501000208800100c0b03c1440c442d0b000343c1c1080c8403000308a81041d2425101100c081d6200c1c0d4515844203805101c2c01c1e480c98215501800c810203541e07618804071070540e10380e00c4001409000c2c480941c084200b010b80201d041c40d505140b00c0645412a84ca404081d41246d915010b1099a1b81280010070000c030b00610340da003a40601414200c40c01d5000d44c0c0012065030089800d41003507802006410380c0a8544158034115a00300444190458208007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 725303606 1250 725302356 725302363
    0x3060b03150d030e030106062304060c031103070507030c14030604050309190314010c11070312050a031d03130801090f0f0c150806100e0d030806040b040501030c06080c0705 76
    0x800324400d5000444030803c040c000c60310b803442241d0150003401102d983e020050040005803c10800039114a0820000407a41798120390540e012502d032494680a20b4508a4001000e000040404d210400800000c6401005180000e512034a41400420300b004444410a0403c5400f14042d61000080c000007600100a0b18400700341680e2800c0384035102182d41d07820b40f440c2e52010b00088004222520600c41c1900401c40c4800306468031100489140e0015988016900c0090702581c030010150000700e04c18070080166504900d00420320106080e8a114840d5183e400321000703510028005038400405499403000f89038080c000c104120164071070040c20000510001c1c10003080d070000c201045000350507100501500418408082243c140140034107105940042c811100340350410001c80c4207c004000034400503007941707140c0c0c1850340c05030b5a00c000034080340d50103610b41800320680e45840c03042900070341c00b0342d0800c03003ca0316100000d070002101500030340c0101c0f01001400d01041000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 725304856 1250 725303606 725303641
    0xc040f0e0f0417040e040b0618160c030e040c230412170c0a0f020a050f0102030d0b03010f111801030204030c030b06130624081b03060d0204060308040603060b03 71
    0x901d18602480e2140301e4403d61007103030450f000305200d90050000340240346100034407819013034400d60200003820000c0e01c06440c0480f106284c070b00b4109004a07043d4443d1030408216403090a0042c1088504030018040d43c602c14091000078200d54408480040401c00350303100d180d2a80d40007441d003401d1000f515070505a10001401c404108600b40d21440f5a180c2290503006410b4151a41b291041c54010303408070f55000240d00c0b81c0b26a0001080d68a004401440700e000e058000710718007031001150300050701810220903815540d40c01d000d415004c040c01a40b45d0b1403103090913940c3d280c90341c0c010b102030454034022903410140b0502040c00018040b0514206482d00030b0384495941e9200000222680020803001a449050400c005501004084070542007641020030a01000c010b070012207180104480c034021007001154003c249200300340086410000151216180d100303da0082800e44007940d00c00c503002000040c04010103985032150030054507030000e400f403540c2480140d110812044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 725306106 1250 725304856 725304863
    0x7020c010c0f06141905070e010e0f0303030705070b01090509031c0603172104020319050304050301022809031208060105070209010b041815030813030503030c040f0e0f04 75
    0x1c10104814803401d1000301c10603562041d001c3c8110303891102d400002d10000da6501a00c0d0760000d0410082c0c403100c0c0512407003441c050759011451600000115010745007a040d01c3e80052502202c01d03d0b40e1000d000030351280801d40c44090390340b0720502d000e015008050b802010f5603840c140c28032018030008801c1301c40180800068180c018124a050002171280d580010710402c482c60141c900000910b014004c00c1e40402c1c90411500c00c900a00d00c04100c044400952642000c000300000c400074102a40069005000326401c1980350400b19003240e014609072145800a10b80840c101c401c84403401c1c90035001407500c0e90340d1601d999a91800d01004181e000140280f07040052403036403262041c0c07145a90010305104007540e4a54038030704240c0c490300801c08108910140814120500d01604d140745050100d680c9030b41b803850b100c0c140d80c0d410010b00b2000070001103d0000104d40100040d600601800b070310651342d549001d0781c001c40300206502c00ba0304200c416080200949111802c164421340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 725307356 1250 725306106 725306117
    0xa2a0302100f17010305011406091b0f1b061f08030d390e060f040e0405011e05150406061e050409060f210b010b090a09060e04050105070807020c01 65
    0x28078002d50b0f84891800c45210400f011900010a001301500000d203007541903c2d1810698403071000340000d0010403070f0031595003c4821060168039000500903e40c3c0c02d4034810260910510030704406200310500450707942c80d40054203000080605c107213041c06071400030f50341100e4503107010402900d0303000d80342140303400b16035800e035a00d0200d800c0340140c04401101c03600d0a0f0b680c0112a150200c5038502140c5a000440342d2a000419081400440b100740130880d94140c14603251103000420079000802c02c5929540f05d1940403114460003018062480d106000400c9a04e0810324102c0713083c082e6102c11340b045041640400c02181c002412030b500782100f410742c142d030040348541a01c10f0300c1140d00c80f0500038038084001840205402000082c0d0300000803011075400c1940c24040c0c00b6030001005801d00d8581c030010407040703480070001e000141000c4d25241034143d41c0c010000807600c95034081442e100004007008100582881640d0f4005664100b00e0024140100020760720f0200e10481414403c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 725308606 1250 725307356 725307377
    0x7021902040902130f06060809150603071d010603110702090112020f1216091506050304060608060a0b0906120c0d06020408060c071e051005180a2a030210 68
    0x100d4a4002102d10303038001e40f09000711000d4100e59401840e038526100106403400001149007440303401c449001c0c0707030550010080c618030040a034542e858090030301c9615100d01680022420003041080d154000704064132025585030820141c140d0707a0f10340c03203030445250812140006036100c0d0552815100032400d0b031141a40140b002c01c141151a40480d036010142040c0200003520000e900d0f03017034660310859040c2043c0d0340e8548034250750711b88070314190045803500d00340810b40c42100030f103601c10301030a0041340d83c40d0751700c2d0360300c0c00e00c507044d00c60854603034480547c1412030820500160f0080740540b4000c200710010701d051502e030450041c01510541030b41c11f00c08184039071501981c01528194003654124248100c28610036071060000f228805080440c0030060408441c2880800c0d404c00081c4c0f6201c0785801c41e40004103c0180691200c03100c0b104e0104035520300300b203980300340d92144808110304000c030041c2d581c00c410000410350f443c0d41049400c0c001070b00c4144c3c034000004d0180c1020320808 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 725309856 1250 725308606 725308609
    0x81e04050a0611041505030408032a042417010b030912180a1217130b0a030504170c122508070b0c0c192409060f020307021902 56
    0x285680340080c1c070b040d05140c0c400d620314200200500440b0703070450684c66843d01e180019541c3e40012203025195243c01d10000311051603544140940d0588491030141030b0749042c0078515079030082c3d0801a8a08036001c441d02200d8517540c94540241e43c0e0341014085070030035145614030880705004241010601201203144407800b000000c2c004080c030f05851340c80e03004900100d01c8100110107218868030250f03400152081038100c540b21411742140c40048107030b95030a94490302c1c0d80a1076004000890240c0c0010324402c0c010098100310b00300396130101c1d81e0308160034000d009015401d18110384140c2000200411200003460001c00c210715900c442e16a8a6010100900045402402c07146500f02617140104060080100901c501c64404100507480d145041111401800050000c82c0d000706210440329482d207000c000c0e11449040c4420f0300381e80300031003400081d005141b0200255200c1c40e04504001e6036006264105400a404500f54503040d400250748010141300d0b40da64401144031603055 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 725311106 1250 725309856 725309863
    0x130902010e12100606111507021009050303060102010516231b07090e010510061b060c030902031c05030402090406090f0b04110d030801090c0302040f060306080d081e0405 75
    0x140c180c0207103641c21554400b03552a4a074800010350b200f00c5868440f011a03880c5c0250600140d0b00340c003800400d001d060040c0c0410f0501405843c480c158800c6004103100f64142c0c4c000c03040c01912035401b0b035449003003c5d0b00290a403032000d045510504260702ca0080e2150703220401d840c140b8550000218090318201800003c0c2c45850107600442c8000340d41c1e41140307440000c80c00125000c0c040200f06581032400c4080c01c039041610450012130380b154041000310b201c1c181c4055010081c61207080d0040603640c400c1d00f2664000500c0000c40e86540d50383c015850709005c0c1d040c0620507205040320440082400508038480140028810002c1d480400c0c248540395002e03440d0103030300a0407014140c82e2400c01510b050001c5070700703e030000800724000c0f405007808107401c40f2065041c0c6070781d451a4205044500505046403e04081690034040040c2e070704041d0810384003c00e003640b0700143e404e090036001400c1c11895624034040c000c0c2c050501003950501018002c410001d00d0345181c9170344892400c00d04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 725312356 1250 725311106 725311127
    0x260f091c060b01080705040b0a0518041b1b1a0403110303070206041e050601030312021e0403140622140a150e21070606081f0b010e13090201 62
    0xd1199000380400030020aa070001110304001d0700c64180c1a0f542990841c0d003481180620303140280d0921001001c0350060303024012403002980d9282030480c843c00458225400c0070580300c4500c1c40510b40c40242900030009000902130310811003030b90b500d076884030782c80d015a8403855590b10019030002828544503a00c803400c4240c154050341d42c0c901305110003e6544a09070340c01c1e6000d81421010401c0d40b0b4401003685061035200016204e02d0386551001e90303038810403015200d8030740d400b0024032008080001c11300d160704071031036241c641740c40c29030030b2030f000200b9800c140c507496078401360500428014403d10464001d0390785004c0c0210500b01d103403503555000601540d00f01c0d48502d040e40d03020080b100810340c0f860b0303407000c1c410400d002e030140141da5124154074403440080414429445030847c510000c0c0f107014000d0f6008100aa5503590740d0385490b034008034001c0b041c02440c1002c00071780717030038050403c05110920701080151100c000140d51031445d69030310616503548220701030841e4080d02d107819 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 725313606 1250 725312356 725312389
    0x91409060906120a0302060105010e0d020108130314120a1103060a1203021c080a0e0102090a0e1f1d010909031e1101021303020a08030f040b07170304030c260f09 71
    0x13a43c1000ca0b10b0061b41e00d160a01801f40401c1e030802c0480901d00b040c84040c0c0d01c0e0741d0140c0d524046500c48001c1d20014008800d0305800b0000e03810074000c205148d44000b00303c01e10101c41c50307500d6494140b041e03600300d6082540d180001d507010020b101d020354454410000ba01e840e036104488101c020310301070745030440e200e0b482c8068a00c4030064402d00c40d0014002c52040700560300901030f0b6110500b1032400c0303104015a4582c0505103403414030400e075111b41d00039800001d4503100c001e180c01418178084c0030452a8405008072078098181e5a0b00701d03e01e218140104180b140900c0000304030381d4050100045003031625030801501e00c030140018826003030341c111030022a008640d03904241c0f4800d075040b2078a0000380e005403003a02001694580000444a44402e00c903010703406d09082c010050400d0f40700200507258003020340580f002855010f00154029482600c1d07603042240c6900e040c07449407403c2c11041a1901d508516844841c48100032240c0c08030320307844001d40d106100b80002d50140344804008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 725314856 1250 725313606 725313613
    0x1b06050f062404060536120c01020c2206080d0215101401111207061407020604032601080618210304020d021f09140906090612 56
    0x186100802220301d005078015210180009450b0a01e034021012100304600c18070320801c03040000178800d00151900f445500010081c80d0800d02c0031000c64203a002d07a29080421203a079982003440c0c0300242e40690310038540605240440000040c3d114400700da1107600804a042461890607509500d031201c02001010821880d621210700660700c8a0f40d540c48000b40c8204050582400d8002c19110f00c01c03415a45501485c50800c03404c08540c519603c4d030181440b074440c415040c1c0340700c1030208104214940204076198040c1342410001c1c0e8000c0c43d20030304030500107024080915804117416601c16014200520700800c0200d60b541040411200000c000e200d00e800810312210220b0b0903070081c400c91031160002c00307090300c0b020707200c840120780f010741100081d1002441d42030400c041c41d4001e0004141640d6203120790045070004001d1819030001d545112051030000e50004068005860728898072504c0390700c8000800d0002c04090b110354400c1c044c0c04005100c03581c03241c021780c507443c0009007078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 725316106 1250 725314856 725314861
    0xf080f0c090306180f0304120206070309230109060c0b0402010c02060c2505010e0d120e15090111030f040e040c0302030f0d0e01180905070c050d090e01091b1b0605 72
    0x40010783c1156122400c0d03280203801035081000000000d5078188e402000400880400e80d6081150720350000034210180a01c0d89000100001c6494004000c9101101e040c820b442c6c00c034000401514180d00514144100040124081850701c00f260303902c80da080c20101e41a0510b800010034502400c1043c0906228840140c0303044e900c401f43d10940c030520304c111b1020550711000199044805402d882c4c1d00001c903030110601044c00150704001c2150b150806121290310000402d03900403205002c20b04d25000080d0b10507440d40c2c08801424000b8420000d54100305030801c8500c40c600c243c0c440c3d00c9010854402180910043c5003c00b03009682c024115000001810100c2e82c40309072a2035500081014640e80740010350058001c1c3d0580109150788009540c104000c2400410f4043c0c80075040244404201c07000540070001c0346901c0c09151101d0021501c3c02441c0c42407054140c22a000e480d040006885400c001c00c10001c80c2d40f1403c1c01d1a042002c1c0c00c141c40380d5103e007c0030000d0701c0309080105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 725317356 1250 725316106 725316121
    0x1e11040f0b0439030f0c08070809060610050a0e03010c091802030103051f0b090406060f0801110909061503041a0108011e11040801020f190f080f0c090306 68
    0x440c00c01c0319001d41c2e0610012042d181d16039811440c40d0807062022031946408082c00d402d60000c0310141116040003d0400d0040f1419411100b41010307960102d2901004d20400d01c1d004203203142d0012750b10004000c989840d5000c2101e94070201c8050080c000301049108545010301800300340c5e0100580200300d2016124801060841144503941035020401d405144c3c3c1802c0f8000c5074180d036040001814050201c5400da128000e015070380610055903400d041c1425598502c11724021030041754080f800609096811180642c0b40e441021242e01d003000c140009910750007a01c414910440e079500786541e4410100c1d01080d0501d401a486034800003c00c0b0400000301d604d01c1c271088000120806980e210f107941401c8854201443c0c0701340041a0f400111104c40c1d03000381d101e4000c0702107918101075541c03c6203804d90708000c4150708110b0010961f1800814943c0449140b0041850081184404800c1c007601404001e00100440440b080c0014041d0403088203c441900010302214030a00d000b54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 725318606 1250 725317356 725317361
    0x10e0a08030c21060a0506070309050f060c0604030c02040b0102010606020c100e030703060603050c101e0509040f020414030c280b0c03070b071d0904021201051003050c030a1e11040f 80
    0x4403c548102c5d0034400c0400c0b0307810040700341d9078007950540791002ca07282000d04000300341e81c2400009034401020041c075003160000b4130159006074400d40f03a500c460203051040000340c449178140349045a1404408000c01030740000d012040403803c1d80d02c1103051420900c00c4030101c43c1013546981500c541900001000900d61001045074020701c2070310071424007041041864200300c1902d400141203800c02d1380148004000714407050006091082c504a1010007080903944c5591400c0d20721940800c0800030841d8003d21102819070441c06002d0b403240140016070b0f068200c40c0b1062070308045143d00c001d5443c0c036208a10103003d468a450380c039641203042e00ba90f241c0c0148022100d0610040101360a68011015040d00d6080415003800d060405001e200100b10001c00590341f0013542004003090440c00c4c4205401400c150400811190540c1442440c00101400c2c0c0e0707001e40c1c004171641c1c02103480300c00c0043d8220070a20024015548074107103078440c007800000c006d80c42403400c52810365806041e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 725319856 1250 725318606 725318611
    0xe07050c10020405011413030209190e030702030a0f0f1a041101090b190306030b010b041a0c0309010e0d05010507020d020f1b01030504080d050106031409010e0a08030c21 75
    0x212403501e00c544a002050340140d2240318007080d4031020040d620b46004019002c1c154203c004c0400c5941d4a8001400c0c80c081070300c40d0b5500c584107814182038080316010349616590364034000d5103004000e0340484d60716a81c0d81c81c007400320120440018100100742001c818039580185038100714a012085051048405840486642a2400416446501900105046404520449041800329428a00c48000420010b01015520381d030100004402901a6001c0e04a16026035156410b104030800b510040c1e408120320440c0c01d00400565078000002c4401c20402840c21103600d81c48100401d2084004241c010003035400c10041091859000036000d44001055088031640003d907405191940c4d2400d540c600002000100d1800b9075000341c0000342c01a2185940b00c2ca825a21800c40041740c02c20303048a80040c0c2c48044140d43d8044401d041c03500301e21040300820403178020b0401203607224681d040c000d000b4440840010060806042501d01191070300034001a80c030075558040d4100ba904 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 725321106 1250 725319856 725319877
    0x313080f0705101d010e100e0705120c01141305040c050c010e010902011d0102120a09050d060b0a06050f030703112a061f0b0705190308070e09060d1104060e0705 71
    0x50a8139101c1383d01c014028500880301940c0a003040e0103108010300007800c14a05c0c0f04d0305030300c51a0800205900c1e075200a1561604150203460000c98001c00109201d209051001c07c0d03c4050140b5403c241100c13041008664040300e001070085202d0500387e61b10700030000088955460b006240003020010b400407003066100740e98400000600301c40a0028501010b10180160b00c101d4038200c1004404004001c48c091500305040040e0740c400000340300d480d0490044440d561203e90305011820900300d0368001d000c0c142011814080031320058691030100030a600d08164540b0404901000140c08540d4072040c2e035038545007841420344000b40101e00d15184c81016109a10000782c41d0910750500d809461002011260403d00c3c01c20300f00c845400034441a20ba42c0507500c40c0c00c5c01e0181c20203c0c61010741c4070b07448110f01c3c0e103022900504651841e4062074001c1c000d1008000681d45c030840c61440303407580010b01c05203080b113103804280107100c40d401501d103041e2800b0078802d080f038100b005041d00422 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 725322356 1250 725321106 725321141
    0x30406090b07050a050a081f080a1a130b040327030201120c09060f1103030a050601020616020d1209050f0a0b0c040f050d0302010f0f02130b0313080f070510 69
    0x100d0031003c81c0e861140d0742013540000d006120a900305d611030785d1020340155281d000b0200308600c0d100d1042c8000c3c9180e200e0f44440e401181288200001e90484040c40d2000101115040c80d00210707480700c0e114401e100410f00d41d80400041c04040c000c01506c900006074030900403081800da20910229041400b003a800710b4080a07035030300c6e4400140a068000c800c0303960341581c2549404c6040c2c41c210660000e20042c0480c10003c4404990100003551007903802c1200403c0c00e04101001905040c009040300c40d10310b512212882450340c000a600120000c1d1340740003004903003040c58600042140003030007840e0707000b40000c10044000000701701c0311190050400886075100da1000d60001e105a04c11846130300c450080401c5240307030116488115500a00000c504004140b8000d0101ea81701160010700641c00320ba9082d40e20942403422020345a101c0b070452650030445c180303840c08501d80c0d40043c00c100c000039000741c0d02c5261109407070f00e1756440f9040320202c00700c0541c800050b06441034071803000c06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 725323606 1250 725322356 725322361
    0x131b180e01140913050f0705011106090717031b03031005010c050607031e2a030603050c0d0606030210030618050103030503152d0a090506100f030908030406090b 71
    0x3101a18100c803040095204102d6019050262507100180110a40c2c1500000f07000492003d020135038401c1000e2000e0040740c1d041c00c00262080302c44500748550750313014400b0044000800100d20003500d00701d158031302c1c00c4022465805d185105841c0040b402c0c07698184416040000000514040e0504400b0405901c2e20348004403074003906840c01605503440710300420f25850103603012550b155018046124624060501a001d5603d200c03480e40c00f14026114411548000312146885007100746001c1c03114a01c0d64a40341d0781c0f9414108650700c0b071500e0704002d81c20005c055011304002e56020384a042c0b4801d201901030001c0101e4880e40000c162410202c5100016510800b81a2649920b4280c155203598040502d40d1240900c00d58000c000c0200c0d11000300740180307070f00300340c100741d40f07282c00b000040d42c0248078841e001d0740c1c040c1d44520b04000501c0110b5070b442562803c038401c83c0c0f5024201d40310451049000e0b0480302c80240003958004140014850b507608034424240c054142c62a0a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 725324856 1250 725323606 725323619
    0x40e010b030714070206041a070501140c0d2c03120703020901050d1508060a0921020c100c120509190f060309020f030d050a0807030e070302131b18 65
    0x41c48100d5182c00058404084510b9159229000d001c21500180045080c2501c400c1140310881d40b130b070120b4508280100380301c4e0070840b00740141c0e00b040c0104019546141030009181c0d00600480400c0c1001c945c0761440358810041007900040482c40c0303030302402c00804059403180d480364410040b440d2003007400341c0060740b01c0b4001c0c000c860002006030b440510b4081d0f4503125800420825004400d121820f0500040380c1e0010011103000c0c0c0b8940200007446900c501d0400707170b802041d20203800419081c5000c00491030300800c0320569003100790341185502420070400c44aa074400f850050144031203015148182d94480090044144261000c040d120321440009110792000c4c410000b166814940c2400391511030303000040c1c40c0d403014003580c110b052000c0000741448010340001002520106074410b40541c03103c201a0080c0d2281030400050502c00105e58480350f440c00040d000d0b007608000142182d1481d80f04101c80030350141060110301e0000700051600c0240f80d4402c0225071440c1010440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 725326106 1250 725324856 725324879
    0x20f070e07050a020a12050429030708090a0807030e0f040e0c06090303040e1311150702060f09030f0f010e030a0801030f0215070807020a09060605270604030503040e01 74
    0xc0d11903810819259a403285811503450740603411940442c0907901d060310010704006083c0d8503103445031725010348881c10301010009154206e102d00c014521104010b14120400d0f8040360b4210804e4a4081c4196444607645450710031400402026204000380c03c10502d584002c0090401030111601d01c1c2c2c0100c1d900400c01610b0010b05040226000030f044207840c1d240010042c4012032000e000c1c1c3e82040d81d502c03816400024100c0d90308245c1c5200f400440c0070001b610f21705c91158402164460000c0c007600450014901850500a0140d40005046030181000a0036200c4164008040f5203003501c0c0902ca880d2a81c184000b01c3e81d0540c04d05a0070000c40101109441d01c40f45160b0301d44241d80e1864a95040340410100241c0c0c0003811b00000400f0145071030010b003204c0c3e000c3d08003696035080c20b1041c0101c01c801540405400c030702d054000d0086640c810202e541c400f07a5107034500d05552145412418122003000e149500ca0000140042001004000382c0708666200c070049034142c0c2d889408168 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 725327356 1250 725326106 725326109
    0xd05070f050711120f0706030b040606052701030921030e011b05030c070804061806030501060503070c02031005010909020a090b060f0f0d0626012a020f120406020f07 73
    0x3d440c12418190f03a0303904202002e4554210031008032030b0000c0c4100495402e103030503900700e2000262212446441400c0ca4090400203101c9490034529000c11082841c80200d0510404140320b012005400c0c0036a1003a040760403616000010401451503c0c0b812000d0742c602d4003010000300c1c0c10309200d00d405080621899500260702d112150a05c071402c8030172240e0364001800ba044c280c4060150310003040c001c2c4003a0019041c1c03611064491307104000c0c0405c01d91080c3d8489810541080e006200302c1e94004140c94210059042405580e0103504c0000d051400b001081c49280b80b401c400098000d0281c1c00c0714140c94003d840d9841d1042d202c1d00600c082e86c105107001e94201c82c0030030440700e00c040c0030001800b0381c0784a076101600348001c0f0301184050301e040c1d9010200c50141c80000c1c1840017560b00d00c1c10305d03020b9098000c00c04144019254000e9145201090160010128850320010b009101703c242c0240103005840010a42410082681d001401400d0040c815409039a540810002c0c2000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 725328606 1250 725327356 725327363
    0x2010201050f241201020c060405070f060906081305101e0603081806160b0406050a140a020d020c01090803160c03020a1506081e0606040606170405120d05070f0507 72
    0x303c6000c00e0300b69552480f81c0c603007503d4020507007007152420804203202604521603424041e00e140e00341070070900d2030584035402030320286c02c4050040002e540c110701040c003211503d091502541e40c4134004da00309450707a0000134102c0c0c003a54503c6445400c0c00d521180c08000180d02241d00704081c940c0d0202180c4c65404002c00900c03040080c8446000c0c1c50140040d140001421a40750010b8418600d2074655440c0e000c88510114034140810800c950140700c0e408562158204021000d0f8a46101c07101c0c2d01400d1081141ea0026460006200075012558101c000c10028812072419140408190303108031903440100704000b00603030155100342d20b0300c420b994155000b04000c4c2a02d403a036118141c94011f40d1178181d0342e034500c002a03510081c001700a011600502d01914074140b00009810841c000300b8a45c890341ca068028010940c112145520440c040c424034000d5075640c0c64510700d00480e08044803020500030803101c501a149410507445803040390740300c1c8110b0082c1a410759242c010781c0c0009 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 725329856 1250 725328606 725328631
    0x131d010b090f13080a020a060c0c0b15041d0708010605060c1e0c0d120f0305090d03330f0f0501050f070314130603060e01290c030a0c02010201050f 65
    0x41c180108280342aa00f040240c00038860300030300c9a90364039990f4040320000b00941c01c03450001040c07040521403840a40501d090041c4c20441a5071f42c0c145810000700792300760b050b500000c030f0507654903264421035012802d1460954080701d2880510390359009031007820400e600340440454207003001c005441c42e0800090040141203000e810070000f541890a10080700c0c4100360300204140d583c000e0051502d401890720416204003030340002c2140828080e850705140c101010b00215200002d54070841c0542e0f071900043c003c0c1c1701070706e109a2061506c610345030744a00042e28100751550500d000100c071074006a0140c030b9a62803e0018140310284034060102d030301842001018082b1000a01400d4800d280013400d20600c607401801d0340c0c02c42d0f540b1680807030003010180001c030381600c995005040b03d4802d1520562501d0101c0e035801d00d82202e0100042e82d0340140341c40065400040d582c115410b0342c103036a1110398411008000d9190a03406a00540c00d0901080c0c94000d98094280903c2040005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 725331106 1250 725329856 725329861
    0xb13021302180d060b180f1e060d03090f03110a0608012103030e060c0c0d1431080d080f0912090d0b010902040e090d0e040b010905131d010b09 63
    0x30004404500f00041c0d03803803500e480a160304c80d500c07100350b1082c0700d00140b8900400d0038500c0f006000001d0080c04844a08040a08101c81c00c071a5140540d00000c1200c10000c88403840c43c045070080c0107944012139114205401000b001514500b4804038181a58000d0050355500c0c01116890028813400914403182040c1640d02031494400300c62490103410049481e40c42100b80360700e840c0003111007d09900010a03413081c1d9803000c0c00340a0301e9010a2410310b24108041c680b6480e00e11407041462000f40c050b080c44030920b0a00308040145512030000311540380c1d510603295845403442c240348030008044500003948402c100e50441d000d109400010010401d81d54001c10240c1c0c001441d080e400001c902240d4002080400d443d80a4500d0600c00360b01d40e4030f00000590380190160103445150090090440d40c154080d140c02808101103c021509048420060f251249280c101640100b0b8021880b000c07400950841500d00c44800e03482c40d00340240a0850382219034100c002c07540600f82401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 725332356 1250 725331106 725331109
    0x10c1e14030601171519060e19170105060f0103060e06010804030210090507050f0102030a080408030402150307030b0a060e0a1802190206100f050d031101090b1302130218 75
    0x74540c041810304007400713500010f80c0822030241c000c0328040742c42e101070a041001c0703082c0304c44c041190001c5500d01200c4103082920241c4070031204024940a40a032407a181d001c2c81c882d40780207000704100201142c10410f503800550203401d045894038011039050b40d051401d544288148000c481c038248c0719410a890f41c07001140c102001500503000c501c60701242c19810340d1980b140407290b81c401d1008084052401081c461050f40c28203042d4195002840b81c081202c0e040801541e22039800b1a8cd82c1d500d0382c0704d10010f03141040c40f112141040c140070007048407640d01540142c1d44207408461010b549a81d5400031110004083c14954001110200801100010a40c1c0b071aa40c2044407015003042c0011443c8801c04001c40903410050f031140d0b0a000e14603200003c18005000c0c010314a160060912021072030700c0c107244200400b00104000c0440b40007400b0340c4541b440503840710302c0043d182044548070312041c50401003640b03c1c1500e420092103a59091080314026120303440703051682c1c95240c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 725333606 1250 725332356 725332397
    0x131205090a03061113080d1b1401090809040f2a0e2e0201060605070b0408071407060e06090f01030b0303040e011d0c1602060f0904050108010c1e 64
    0x2800c007604080100c401000280d918090120904d12903600943c4500d80c80d000540c400b900d50303004500e00e40014410054141d4042034520903800d420002c240c08034518a0011107a100b50458a00b540d4640001881007005810007030101d1001143c05000440507601443c0441e00d100c903040000f0688024031031800748407010004030000003810102010310a8401081903d58126611000304003c0750205a03150101010444a11307560300c02007000d00d00705440036115100700403018000b9000c2800140c10000794100b110001d9500042c815803811a0185c2c00c1c0d521015402000080307a00080503d40908000046e22111100102031711340980d0000015801410f040d051340c1d405000412020803036004c081d1500d4001c00c42e10038880480b80302402d1401d44650003800d40e03211440c080180c103440303004a860849030150116811070340c1d1807208840180c1445980902d50700f01e401c2c03200016034410190300c10030388a030840d02c4510445500140c20b410b1a400ca44402002c91104803200c0030030328004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 725334856 1250 725333606 725333617
    0x190e030a02010e0612011206052a0304211709032109190b040209070e09040b06060c071701060e090d032403140c010801060f0509040906150e131205 65
    0x6032038503203807401d0240e003416003141c01d8000c2c80700422110944810403212744240c0c2e07400703603112400403048000b04101041c0b08450610345400688040302007814003020354056001901915007450802228120140030001c8000c64036160a080704005880310398007008913180501e07100d901201103004240300d000381c030034003070481d032881c1c07151080021889030003031004000349000f6903440a20780b81038410403c060780000e0030340382005940b00c82e0b41039a403034610855070060792100a401150f502c0d1004901d46000f5a2007000c13152090410000c0c2c01c1d294040a0036959544100a11110f900c8403040d48080740c6c20385104407140c0c0301a543c621460b209610200d104203550444074240b0904400d1000e00703501076003081e1800350400d40c43c1d0004080421055100b03090a0170141c04940c900000903180b1190801d40310b0900500207003091160740c4540c400428540e200404004245030500005054070031030141490b43c0030428040352a04940110052420354090b1200c1500c060880d400c030344075040f4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 725336106 1250 725334856 725334859
    0x914060a140604090e07150c140a02010e01030209120d03020a0806030a080a08130206070c1d04150c02030706050406021b0c131107020907020c041104081e0a0803090102190e030a02010e 81
    0x1d0f6800441c1f69a446880b50041c0c18140d070345da1a03103074041e040c1080da1180340d5a01c000ca0b1780c482407000e070050346c000790076048415090a00503201c0d0761040220f0041c1c02d2400b1001d0040c014002d45005241d01503000e051b4135a860f9840390031075a109010b05a490b4150b68010301000401e01040d62100d100d440e40d6544140006001032078840340b980403880b0f940040344101c941043c402c20a106a1713602c85002060340d016060703011444c1c1840d8031601c1d000c002c02d01d4440c1d20b09490f0700c0c004000d54001c1089408a940c40182080f2615050402c0c00c0290030413405c6103d0481c4001e043c1040e81400208040d1040c0020b00310818110740c0005040142404d090280840707070140112009641d8000140e44101060f030080c0000711170a008220460b03402c0700842c1d4481030240018007000c14000313100312005d0043c400361501341c0104e81c3d01d5458101e441c03400a00c0c1301000410400d0140064019103003c142403071501400d40008041901c403446038a890300e80552200300c1c40c90142d80304441d60000c4150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 725337356 1250 725336106 725336113
    0xa0206032701021c0e011406190503160602010b1203190c20010801050607110d020301141003120f0221090d05070e09030a05041406040914060a140604090e 68
    0x10640c00303079003607030072002c030710f5a4140d41c0300c4d44048822100d001d00012100c02400810100c2c0111410900300f200240041d4020781d22121002c0040080081c1d200180070004c04440182040c24101d910148090007071400650900b80c003840181061100120082100800382d42021101010305e0704145c5420711001c1040000785d114000700c0d05191800e003214021070b01050380240501d0015102c1c5106a20040c06a07004200f00c0c400b141010311824060340d8200c440c52840c1040c1d000003030240820f90700000414031510140504120500703c00400c5900c508102c0d01b5040341e00740140d60a082046c0c070794001d44c129054480c00002d0805803143c032800301c030310b0040c200f0800d0004542c0e142c56402c3d040318107034400b140600010340b44114540e44180e59000840c0340104100004140c0e0050f031161401c3d00310500e0012465541e44415217005c5c2ca072403142040030303203028005410015400e070b071074500481001b0400b0807250101c0c03155146030000a09032626180c03420748284001c00e400c40c0c540f4024003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 725338606 1250 725337356 725337421
    0x603050a1203110c01020309060f1b03100e0906011505070b040201030e070305030a032a05040b16021806040e0c0108061012020a03020406090909050d03021b010603140d020a020603 79
    0xc90200107804204d0782540016103e03c1d0101e800da290030400f40040100c035084004000e504076102101c0c0801844c01b0060684030b44403000203401401f190f80014080580714030400070b80c00d40c0003924a049900103008a1071103400138206462030b10030b240020344114400400100594002d411000c4003442c444129080b80e541c0741c4540e403c50b000300c0507080010b80c803072181d60f482070803400d90a122002c0a14415079150400613014105100314403501240020114401c490000c0c500e82040c0c9180c2c003c2e20004a04801d51281d04d15030a089803980d100b21b151a1550801082c005854908140181c40d83d00b22621000b003000710f078030f02e8480d86208000002044044400150004c0c1900042540780561542d0030000c026200b03410b69008240700500d054030b98400301d0400628450910800e00b001030740c070011494452180c410306806c0c4540c5609045000081101442c1040034811030601030b10f0380c0c01c081500490f101c024850020307512a00034004654082e11512a91078000400c0e1103000d20b45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 725339856 1250 725338606 725338631
    0x2150711060c03280e030f1b1912120503060f01030515330a08010e04080c0d080106030e0106030c0509060d0209390d090203010609060b03060f01030603050a1203 71
    0x340b6182c5084ca00d00188402800c40307942e040040309580e54801c901801503445040441c0303640e607840710f140b086024014039040c40e043c1c4500001046158443c140c1c1114282c8500040050204154040707564180400191602912030340c1aa03000311401000d0f9400c208000004501a01026082c2c10540e03d01005038141035a580444034103036422811041040500c10009031218081d4000d004d02c010030410000400076800682241961007040c0294903c2e10755040c0541d4901400c05801081c0c4241d40085020039000080f00d8102c8006907000d00c1000341c4404110f00740d0740c05200080112019110520a40c038180d132949501000c068031200720040c8540001d28942001c2d076480c0d0b07840c00200240ba810756401490341c443c00c41c0050f0b82100031440f40604030040d1140c20300303201c420340e505c0d0544030456500b900700d20003e046184080c0080c680b504d501e1031481c0d105035a40e922030920703503a00d01d6155009004404c22a900603018207802c00d62910b6900ca100003480d800ba003015030b02c7c4032240e0350 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 725341106 1250 725339856 725339887
    0x807061e12020d1806050109050c03070807020307081c110c0a020103091415010303140909070804031e020d120b090105120f06010b070203011a130e03040f080a02150711060c03 77
    0x3d4400c013500300c110150990600c1ea08513941a00190581818041080031900720041140d400194901c1c051119540d403071012400c60241810080c10890001100e2208501010301d2181100b01c40500308440994110001024800c08403421820f402288442001d58043d0340482d0105005015030040001c074804a642803c00b80400003240800440050091580c040c100c2c2802038104980c1d90f1601d2150000550034010060030501002010800102010320514040241c0c090b00291101e910520507806900d6000d00324006000270040f500c2880c203a206406500610100a4109081a400c02e01800194008010700304150321072500c0e8504619410020b46000300070000089803504a01e2041500303440b4800f18405188001c2c2107091181d5940b42890070b05461441c1d03000030203103440c0c3d551a0850240d680b00010340e10060030009400300001c61051030051003203e00c1a000b68902010741c0107401507840103800516074510340074503410301c0001031912121840859040c0000103414401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 725342356 1250 725341106 725341121
    0x1d091b1c06050712090203120c0312010f150810090e0a080f071a061503070306120c091119050d060801180507080304060c1e0507030c0807061e12020d 66
    0x1051075880c0d0421004941c402130564680e4801030b4184007290641c0c00003517445000e58910003240500086181101104004842c580c0300c00c2c1440704015a942c04458031061b03c18451108013400f81911200070178031811103d4400ea18880d6559100c505140c01c800c01400c01c0c480c2d222a83c0309006d0b42d20040b03420f01001d0050050941036503991408107142110154258924202540b10014140b01c02a81c0350746001141000b1403400e19247d030380b204011009010554800070380e07410800b000b5401e100d030510000e01a1041044d040c00480c290526403080d0707210712101c0f00102d0406040405519119200a14041d01d4040e40442c1f810f4070b4410150071110300104100c9180200d00036501003080c28484240100b1241d809141803910b001c0e00503021500b4110010490200e035590052284d2410b28400101030300710003111286a10307841c000790a1074030f070b02602145204032880041c030b0174404c2c2407010f148828681040c40c25040d01c6015a1018203284442c40c003e902400b460750022010322520380e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 725343606 1250 725342356 725342363
    0x20313120f020928140609070e04020403080910020a0c0614120106020105040203070b031009051317030a0e07061704061b09030b010503061506030c040e040308011d091b1c 75
    0x42000c00c0612001a40d0740d0740c1071a04c03401c1d01340304a070380260828a4019034400360949502070103645541d01100c20b0340481c42c12030380c454030108000c02844400d03805050219416105d64405004490060341e41e01100b2070020b1190803401c03401e0040c18411444010750a4244c0c0b03d442c1000262803030810418003d070401c6006070755901c02c10055190422508008000d00c00700603145050880c14a1501a41c600032180314580b41c502003200032a4088001c22181d41003400800000000d03c0d041d17080398025111f5042c1c0c00d0402d4852004070074007141640841c0c80e5910f404400c0d03501003880325600c590080c801c0c1c0b01e1681e920004980204403850f8401659055950a0710041c00d40c6000e1240315410b800250003948904100542003035000604045942c0444240783c995480510351b040c5881f50b6080740a200d00120103000c1015001440d250595120b1400110802040d00040550400440b0100313016804140015102e0701181404800a10060601e00d89402c0c0c485800904c003401c81c104a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 725344856 1250 725343606 725343631
    0x5010303030519060e270706020d09170316020112050f060a0603050c0d09080d2c0d020c09061804050609010507021209060f04180912020313120f0209 66
    0x100e44982455110f094411180c6010400c00d030070058a1401800c00810003000c04143d007003241d00040600300700b84041540715080380d203540d803580402900c9811052607100420110768000c01d04000c0d00da902c079000c10042c40114141000c4d040340c108020001c41c42a41400451500502d0751521070252510542d1800c0c04540181004000e0294801480c0d01c080d0400d468101070241c121400700444024070900d21002c60021118100141d60744203449002000301c2c603008543c8407404001f020380070103050010b1034420740d4140c41d807030340e4403500124046801600043d0341c0004a181c90030b2401c0d0048006001c0018100d142c05080e180600180d4080d201d0307a001104001d0b0001090041c40d5108502d48050043c000b10003105d00058011081414420400030409002212002c001d8a0040410070b91480448110b81c003108000e16144d00306031009140c1800001c40c1e00c1c0008212801e03003d5000d848801d00d403524107210600e03c2030060803116246004000d0f401341e956031000c41d0041e010790344c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 725346106 1250 725344856 725344861
    0xc0504050a1b02030717030a1104060c03020d030605030a03181502150619150302160f02130203012328080616080403050c0c060d141506041215050103030305 69
    0x1c9200034500d0b4256482150302c10040074001803001c06070300076001101c100075910f0381c9401d901c0401501e20800b1003a06c400c008140020b18942c018002040e09010350281c0d60580c04402088040d5030080c02601d40582c42030340c0110005c0e1044140c07000d0401c40900c0392280546a0030740405c4408c4041440006a1007011142010305058956940111040b102c40000f403055a04126116845101d028a55841043c481480c00c1c040c2d0102c500e80c2420300d1002443c0c0c4541d01c2c01c0c03007108490342400d9000d0194080a203442c500e007442240d05881d80300070801c0d07030001c3d80c0d84000c0c0c0c182a6141616040803160f284641001c5110000150011090081f410060300b02403030395107043d400600d02c005120100f04101801d94100400719001a00f61130550b94800c61a03c400d80382011381c403149504400c002a1410398001e850744141344150301094980c919031900040c0e0000c000e600c074071580d4090780c104002c201a1500b55502070700036100300105a201d0050035659401c80700300764800d07404070f6212001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 725347356 1250 725346106 725346131
    0x9020306190510082109190312140904020c07050a0b3604022109070906172e050f040b010e07171f080c120d0503060d0c0504050a 57
    0x1d81644210982d2081e01c84a00e42641145c0d125400444240f01000700003d45200314045000c03200e09030005800c0403011550f05d0044428650a403006403940035000d0b01c981e100f070748518801ca103010700d0b0400d06070400b9004020000294000840c2f46120310803160001803580714504088020803400e0328003620b58103a5240d002c180c5940c2c50040b8200c021001c5240c181d0064105003a003851800c1d60010f1316550801001824113030a80d0704401140c1480c800c2042e00400042c0120540b10712800600009681d680410105500c40810341a1500403000305481d041d00603010060100d580403c0d0401742039200d0889080300c5003036a42d8100000c03150200802c1c810b014000c0b0740100b042c049101c10380d10748094024030004c0480700d03401e00c4c1502c8401060310143d44d032400c6030754240c001072099031440d51880f20564646003c2c5129014090300a01620121008610708000402c2604c483d4510794032030080054034044c0752812944290355050120f041c0c0c85600c15a071003403011740d0001481071034a05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 725348606 1250 725347356 725347361
    0x106170616050c0a06050a09020319031d060306090405070b031f0b0a0e090a420608011404110c030a1d060d0f020d0203040f1208160c03030902030619 66
    0x300c1e00c10900804000d4988954000600200e40d19004140012640c4a42e8615000b0f841041ca01030b41c14403ca90b01d449000249051461082e44a134031220049007a02c11703645441c3c07402c005102e52160040c4006030341130406903151503006100e0703400d4500350342d00d410f101c0300c0a80042e00c54514180c1700c510714020306400c1c0c80d48480501040622036091207901c1000a04100714140c0361406514404040b80720f0050603049007071900081d002210000304c090074803040d2030f41101c40822004080b01002300e0541d03030078450181a0f420582d10b20030240c1c20048404507510b4062480c98000303964880380000000170720043e1802d40c2884c0e000c0c6640304000d640080c0703175007010b8085811002a01d10104e07110b55400f0100e46407204190784c08a0780040c110000d00090040b804110529400042003004000154030300d441407604c140401c1c540c4030010711003124003140455940c00f456918207001107040b0b002d2456045114800d207004521590345501080c00c2c20825514621901080310300c0501950072030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 725349856 1250 725348606 725348641
    0x1c03050c0d140403080703022d06060f01021e071511210d0f020d020705010c1b051e1906062c040803100b0403081e131701061706 57
    0x703280c42d8280c1c00001030080120321480c0b2008100c1c540010f50f00082500034070200507581000003503408a100a08100b106c564020192080c032400703107078002030381440d02407928469007a061740200907100c207040070841da00d0240c442c4010503200742840000c60101100e212070341540c0e45e54410180800420451f8070701018024a6000318500410000801480c10161000d90643d86404034030034498005a000074810320205241c50f0340001060030034440c0540040c01d1506080c0e98031448806001410b003026406854000c1c01030f0070a410340d401145c02e07561514007005058043c1c944018001c022032100d4400314004031400b5843c5c2008004105d01c20b241c81c4420744421722240c440c00c0d1440c0d0300301001a401407004080540100c0070130841641e16081d10080c08109846a039a15140c0c1051156500160746050040343c03003003860102c80300440b05031000741c0500000d0070080d900300a0403800c030f643c41c0c07521002559640d04000503401030401c04886140b1303410000d07000c0350a04030110754044401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 725351106 1250 725349856 725349883
    0xd0203070213180b270307030801051507080306061603030903080112081903020f04090e06010b0403080a2a0b040519120309060b09040317060a050a050f1c03050c 71
    0xd03d29500d02010541003461a0154000d0b2141282c1d07413104940056105400c41418580f441d4400390703142c2820001c001c0920901a8480d10305a81c4d9610400014491301d50aa02903602e0501001d0300182c20103025541158005201504009900075603c5500900301b2056000a84651001007810380050480303000d4203100501c402c43d007580d503c81c0c10240c8650a200c0301ca003540e44403280500d5200764140c518203900f10b01d1441e62240e2724a0000e0150020542c40d040b42c1c01100d0001990311701c61401c40c1d0460b98000b100504000a000080d02e0002d40202203051000740d03000203403400504803c20003d494440c3c0d04103800b40c02d0604003689005c4410041d0207810200300d2034100818000030040403401042c0c6008205420b0519000e03002d00301c040b006681004200b401e1104242e00030340c1850014640c1c00c6e00b040c007a580c00e420420700340102e100e903030b03080300c1000400e00c49814203802d000c10303070340c0007401e0300504240505903007004d0695200f00364001140490030702100d5806010180c042c030781 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 725352356 1250 725351106 725351111
    0x1050a1b170306101112070528050c04020901140711120328090512160f140f0f0105092134260601060201050a06060c0b07030e030c0d0203070213 64
    0x12917204565501c884d1030f40e811061402091090402c041040059030a1058100908103031058110a0010700b98030a41110940241c4039548113904251080e9291520140c1d00c0310150140a140c0650700d0b4040681075400e0740100c2464081529000c414140c0d0140440c01140d41e00419000d60781c10100e5521a01d030000240c0c8045c600060b481480041560307021120b51a03500300c5080501e141c00e0116941580140c000301002443d0310007000d4541c221185018014440c090080420244c0c42c420865103501c42c0440701d807210303554404d8010300002c92000e00700c01440261080003908030f060b021510710850340046400d0740e00e401c412034117944120888080350300c650900012402005170780d0150115440444505031882615202d01e03c5a4a401c6000e840e902e50311040000d010349412200c1e0030b2441d050440000b64603126020310560300b90000703088801070300c1e156001c4000d400c144203042400d210074899107100c50f1040c081441240300703503002035580d8401407040c41643d101815a00c1c14091 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 725353606 1250 725352356 725352377
    0xf0f0c1c021509010239240c0a02040f060602010b06030103050709050a020d050406050103031407081e040b120105190b0d0902040e011103010302150901050a1b17030610 74
    0x1ca42c561600306664006421980711070740900100d10b0030010b4109858207081000043e00e9211020106040c002c90062119035000c0b200300c14000d40c0a111510b61032003400c0f5000300c1c01c1c0740c0c400d10302400d40500c0f80c40645000846540020b01550223000f40110740c0c0d543c8201c1008003503024420b04041d54000d44140d41158999154a601c410300c0d071085500c4551a1000107401410543c110b03980c02d103485804000e6410203040160062809000441c0406d40100503600750700c07851380a5071602580f049a2514094800000500c3c8008802c40300d18000b500340800310b40c6001c0200a089864140c12680080e50b161404204800c0200080b020020b00600d005100c1c035803100e0200c6504090302103006c2070140051000c100207105041141080d94a40701c010b0005080c004019412240202d40c2c01d098006070000003006072107a81840340c08100c0c10844800a40d0250792416030f504007002400e02d5240058441e0141d62403403c0501184503800801c201c9585000034a04010051903d01342c100d01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 725354856 1250 725353606 725353609
    0xc011b080601203a02030c0703030c050f030720040615050a1701080a030806091509090102040308040609031a0615090a0810020a0215060d0204020c0f0f0c1c02 70
    0x410083e040c6901c450410510801d151810810600000e0340094400309007007080081030851000d811000780120040c0119805007440001511081c56880c40036044841c519501a500d01044c40802ca419010301100c1c01c01c5800280080c01d80d15000d20801c074076003090f02d03650000c428503400104c0c0c81189001420301c040080120a0030305100c00c0e0910541d641443c070000d407844200c0070420800c041c000d0001281503000450495030481c0702ea20344030b4441e200c0000300030160341c00703c441070700c440c440120007a041d103072583c1400c0d003010040000600c1c2ca40c5948690000303034010f400c900b0200d45084010000c020035840144030100c0c00c55041c08031410481e0011746124218a056010742c1c0001c10040c4440e130f95620b4000c000c00f605401c0720400003004155101a42105800002500503404032181c1d005801c000203205050080041400082c1c50b400c000080d04000c00420b030b50b2180175910b2010820800071805166810402041000c4c07180c1d08101c4003020010f0464001c2071030070f0f13031003005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 725356106 1250 725354856 725354867
    0xf06080106080604021303060c0f08040b270303071d0103020a17100f08160b0c07050d060b040c0905040c030c02210c0304030803060906010305061f02120c011b080601 73
    0x15949a842c100040d40c5403800014040d0280d00f10701d603a803140041c0700004200440d03008005048280e1542c42042c6a90b132029100c000b411a00500352403c040001044280c00404002c00b84c102e004c1c84514015022030120b00d1a00115a1030b004541d03e45500250b04855145a2040010910b01549421803291f0000c12455040d041c0850442c01c020200e422040b071402020301030103007924040c540941e07032203400340c3c2c40700c0b641c0c1c0403a2020b80c2610081003840200d4115004098048020141303507261030140140642c03040c1003619030741e83d640c440aa884d41ea901414254611a56465005034200360400c011501c10425070420703d480c2144010320aa004a2140003003400ca2810100c13400d400c846500c48c9110b4001100803e01000a0120402480707101a41c09898251407400d415134400c0010350840743c2c19030380c00d940304d00e9441e089600745505030952542c2e1203840c410b45600d810083c043d09010740110704101000c0e5107400440c5c4000d40701c4d03050000c43d11004d2428889900b09030001806 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 725357356 1250 725356106 725356109
    0x1d0709050f190c0509030d03020d060b19080c07060609020c06070f020706050708040f06091a3c0c0c03010b0301112a0d0302040314121801020c0303070b01030c0f060801 74
    0x121a115600000f005010f0310650f00603040203001d03a6043d60740044001c0c003d6000b1204445118a411404109045000c00340c422013403000700c071080d410048000c161740100d4001c04901c3c0d4030030108040d10024520380100c0c0010f040c52074000d6105c051140c003880c100750004090750104242e5030b070f00481050340001e0300d2040783c1036801c1c03d075542c0105040441304c5100c0e0390426140f119140c540000c56a61040c000c1c000c42d10710b1980f0016042e258880c5400500c20143c4070070060a50301c43d40028954015401c00039086400078a41140140d10404207403600692024841900015034540701410280180b03a41244101e0003080030200d12030300c648060080e0007620f420b401c064040182411030003046102060710400031641c0301c4140d44c00040180d0301500040341d0145400741842c8072148000f40246030045116035032402e121700f01403402a142030941800c0e04521840d01484c01a440c00c1c40100b09141c040e146016456040d800d020780308014a80c40f803181c800c481d60b0108200307a8408849030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 725358606 1250 725357356 725357401
    0x31b100912081e01140409020405010f29121518180a020a03030c2a030309060516060b01030b06070b0907051804020d020d0203060f0a18050a02131d0709050f 69
    0x3145c18880340b0100c0c00034089660000d4225142900104555241d105c500e021034607202e69016501c0794440c2686072168480004540554062005a1400c800c2c0607080340e01904008258500084001c00600c000540000601403c0c032480203014900c0c2d1150040c2401c1c80800000782000c025903404503481d0a40d80c030001c0c040189045502c0f040240011400c060540c0501d1079905024034011840b442244502c011804620000f40c000740b42401031041d502003040071681c60401010640f54080a42140c02c0c2c003c0c105642d0341d16044442d03a0342005410060300a0103000b0315840c049600d145840740c0c581005205a06580070f603801d41240003900750b4816415688444507015a101240144800c160001c0d07040c002e00c002c020582c00c2c90102c240c03080325101400c0c06201025022041c140710943d102415980045420030094102150014003c04248100160242a18802c41c00c080411110181d89030041b480c10080c1421500030141c2244141c002ca40c062f040c8604050084803e0480f0803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 725359712 1106 725358606 725358629
    0x8090d08040201020a0311070b04080705040c0e0a060e0d12030504030e040b03070e0c040506040314010e06011d1312051b0c03031b100912081e01 64
    0x40e0700498068000d8002e800d80741d2001c1343ca4600300e00c02040c0c248244c1d07200040d15200301000300b0040040501408680b41000c0030003080e2800c4a40c44e00801411240c503407030a030b82d018000400c54426040c6080a0744071900801c01c19100b40384040d080c1d04402840c5051f1039003542001e032042e41f01ea0380b0b50691041300300c10441280c810000c80380d01a8001d110a00c0621000340c11a070708611848800c1d41001e0743c41c000110139030721a07082100e5240c1030314003140c0400000d000703400d000c00050018151030b42c10500504480700381c0800d0105220600e1011904c40a21401b04500b40c0b901720441c413030381d401c8040010340b185e072001c41000024080182401e0400001080128070104002d0196240150717010049200c1d942c07040d035090041c0240c9600b40c41d41c02083c03056a5505204201100c142c249200007c3d01c2c580740240499500700d007080c80200460701e00000f0342d0550380c0b84c2055 = true := by decide +kernel

theorem cover : BRFrame.Cov 725179856 725359712 := by
  have h0 := BRFrame.cov_init 725179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 725179856 ≤ n) (h2 : n < 725359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
