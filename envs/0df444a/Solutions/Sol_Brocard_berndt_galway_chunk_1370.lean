-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1370
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:37:33.137003+00:00
-- url     : https://prove2.me/submissions/20590a4f-1470-4451-84d7-bbea4633c54d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 246223021 ≤ n < 246402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 246224271 1250 246223021 246223063
    0x1207030b0901060507033906140c1206120309180f0a06050d06090503072f09010b070803100e010f090b24070f060e0f010b0f0f19081b010e040e 63
    0x20f0f020211705101303002d200031f00218040402c414004280c000941034032000381085455140d80405d400c1c24450030342d2201d50941407000081ca6442d2091405c0e000000d284140e91800441c50002004140401030000d608440e0300e00340300034090605201d036408940740c1c0003004200d06080004090060004008051306e840c1c3c0d0540c0104071040c0103465441d41e100c841d03040001d00c01d010005040085243d40d1410945040d003540841c41c07c2d20049049614010740d003442c0181070b4841c000b00364070040c1a200e034a07000300d01c0000d0383d02100d892940201084180d00401506007141c0000340c81d040d262291048034800c190b912184001d80100300e5042280044070760311403042c80d1419055105460142c005440c0403a50100c3c0c42c00440c1c100000ba0000340200030b1001e08000708000c024440d0314650304034035001c6c040e4406044c288010340784120301d00c1c0c600c00000c0d03445902d1854070340000b481184203010109181c2065070000707102d40b0801c0b421141802100f852800d51135a5000361185c84005d85041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 246225521 1250 246224271 246224327
    0x804140111030a0f0e0622020d0b0703050f10050a05010f02011e0f0b061e030408040305011a040b030d0f030506010e03030c0114180304060509061207030b090106050703 74
    0xd6000c44240c0310020340c296200e16200c84003e0041000783d549401c16824001490100324001c1400e074440c4070650003541c110f603002000014200c1403c98100d030000c81d0368928001003500c0544640c81103c45507008500c1d858489a01407541402901c0c034040200303807010501c8165a04500503095800a2034020703441102c888080303015081e008452000c80701506800c0c407070b140c3c1e0f6070040e0108000410b02401100b0f601c00c2400382611032102500c4c0b400508442014203408005c0085410038018a10a400d0940300e0300c5a900b103809001c20300300040c8422040b02841d04143c0544030348414120b000d40107101a00030003a21070304410707060030105079030b40000a2081e805800d1181103140c0c040d084079100c6840e00400c1d4024245401d561040c5480540050b142803103030b89800d800b0005110285080600d01030301030341c00307812801505610000034003e488040e08840c00d000d2045616550102ea40030b0540240622070006800c82c0e42008030420180c8086604400c10384601061302595020300144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 246226771 1250 246225521 246225523
    0xc071703041404052e0f080c03070312030b100302210603030702040506030715080109050a020f070b13290a0509070e04080c010207230a0b070305041a07050a1701030201080414 77
    0x2050300c040c881241c1d00440103452a0035205c3d12410f540c00360304010026601c1311b242a5542d82d90318007080d8107074041e190900004404007207840200403103040c040741c0034843e540090880340a00c0c03c2003000a50119801204041421115a401c95040e03044801420702d08007183e00c074403401070064025034a4402180e4180c80420026003704442d42561301c50305040070300203251000c28400c14070714600f03200114001010307600c2101e03c2012001f00142c41c0c074006075600d8035818401400c2000307030044000ba00d03011555241000300401e00e4030742411640c1d82c5040e403c04401602030200e1420504c0c21080280e56240001c0302416a40b0819150340c0e583e40700c0c0741c000f07402e00c603445589409500205880040002412a10900d007490011180103003e00c114000c0d59242c00000103002a81c9010209039824081e9002940bc50700581c5005031681e0300c00d0400900190035180c00001483c006030b00c050b1980c0c0a107000850004d003244c400c3c80c551458000800910f070290021b40b4200e108840740228040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 246228021 1250 246226771 246226801
    0xf05030717091c0f08010819030804060b03070b0903010e0a2003030f07060209091e0f1906060e0f0402030c0706051312080403080601210b03070306020c07170304140405 74
    0x1d003004815030f101c01d000e100284100100046100481c1450001046201010807103040100100e40100b40f04030594500716a0140e000c2c20a40d044c55840004a07c0c0d610306101a10207002ca4091103903644032000280350071164050403400c4103801803265070000880305c0d1850600802c01c04000c0025880010000b030540c422610b02d410b07820400284a4100309864001d808050b9080341e199101ea600d100140000c0c008421103450186000c0000590134001141501c3d0407404141c06070180c1a10403211004403a840e800800c0840d02c1d40c5503400340da2503c040d034441481d10a61382035045081601c1c0c648154050914000c02e85511040000c01d03880307811121b81640d81e0880a0385c030b034060135644080c007000401d031416400500d80000162302c03940a9038058160031031414001005504210420004281880d20968140503044d00040401e00c54006001d020341101c014028480c42c0000350590502003c0205100360020f020400c1095001d00740d001c0030040980700031a6a684242c00900c03020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 246229271 1250 246228021 246228043
    0x513200a032417030703020c010f090b0d0510080309011b0515010e07030c0f05090d0201050408030a030510050f090103150b0405011701050c03161b0b01080d0f0503071709 75
    0xa00208003071070402c040c45481d0301c11a440444119000080d00c18100d443c0d03c10340d90041c0140e4041d4680400c01c1d40b0440c0010315001d03c900d4140407070ba40b250720340c182e00d9002e036440604154035881031283c16a4085038090040c142500198580500000080c250b01504690005550f501c218a03805102050069200300c1c09049000902581c44d410a059442800c0e60b070900068079190082031030b1405210010701440140d2030311400c020300c441c00c000c0c051001c08012810400c0a2000154580c4104003034a4481070544020030b0600c2d2604e41d0b0705180c581d9030300c0315114055449010900792201110b550541e5046102103c0105842522602030942111a10f80041c80e002c0000f54a00c42e20340d030301555800b03580081c00307151111200c842d071501082c1c030001c40c00401d84126200340d60040c03498451900c080311000302184920b0320740d00240d03d403d0703002d0890b43e042280c0c01041d45a0001d42c0b2240700c0f40390b0400f01c1c00c50a00d0a4001c00000b140100c119009400f0004039144040c2000350402c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 246230521 1250 246229271 246229301
    0x31005040c210302010c0e09010b0901020a170702030c15030408130b0d0515011e0e010c0206040303030c0801080a1a060f030a060f0e1b0409020a120b010513200a03 72
    0x11840d0341c000d0000c0007192078020f50040d46005241d40036284140d500d070300311800c0105640724507420300c040d8000951000c01494158415081840002030500c50b01041d60784903880420f0b201d142c9030041c98204441200c5940c4164440d522640c5541000c505694020360842e00c1e00d500d424020000ca40e4862440d0003c0840312808507050352003070401e0b08150300c511444001d00f41494103000054a04d4140d4502504468400355011122a481504081460401454401010340780354000c84c1081c0d20503002900003c0c0c4a204001d0030940004c0458010700b107403401080c08600584400d0818102d002146c07041012076800708016682e00055404e5808004040c0c40e0261903614141000b01102414012954141004074094010103d542000014035804885c00f410054003040001c00b080c035012a40140c026001042405860005424940c45440041c0340c0303506140c20041d02200c2d64055403191400c0405907803a800300070014000780804400400d0315135801c124154040d10080b8800422 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 246231771 1250 246230521 246230549
    0xb01020f150106091205100b0103060b040e0f0c07030e0118150201050109050c0c12030c071e05062d0601031b0302130501020d02061302030a32060105031005040c 71
    0x4101840d25481c2c100c405944928181564405d426481a01d49110140072a00314503081c504003001c075040000a86414500050300640f01c0c00d519419130800d4100302c7e0324203070b048100a4141e8069110b030b40c209802020303c0d41070a500d90740040034080c5600d0310f14100010600c0040c80e030b514548658014041a00f005182c200030040020300a002c24441c00121074107150206019907000000c59812403103d0780680041c1c00460792021242d8005852440b80c10f804110362000b00d030504c0407002001c01a00300180006800f4200700d0b190a602a101a2036409540c1ea01c000342d111118035102d0422082d100c81c0415640d00d80168018896541192182074082c5400341c010365161780100b66502c00d88031100600754035035004995981c0c028040f80c0240e440000484c52040c800c401c0300b804584024200d03407400740036a035008104600040030401c00c0d40c0c0040221110f6042c0503650f0500d80c000f1000b89201d61420001a580750740207c41101c3c8282e44401160500c04608000d80c00303002c40c50b0000c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 246233021 1250 246231771 246231793
    0x30c1802041205030309071a390a0b060402030105060313110402030a060e1b0901050c0708011b03140601050307031e0c0f081807180b130b040e0102040e0a0b01020f 72
    0xe01c83d84121220b08040c0071fa10004641c5c50007521001c01c03209211208142404111040130310b420314643c0c0306145850071440c007208085003079046087d42408643c041c0c102d01c1d0f0301e49403000792044045e00103071245005100620103522804242c0307510110340080c6294030b0349030341000c0b81d41c02c420502158103e40000200501800950000c200301c680391140500b003541e036136031074a40c401c40d583c4002501120800000d00f4035031058001d0f21340640620300b5100c880d81d0f252255402c488040001c2c0500322900803004a280d90507100c3c64140d040d903883c40c505986045e0000070010320000b0450f07001d143d680c4202074048030070310f00c4038440c04104140401c0bc5518158010b012183c6050300d180c0002e0034480081d013511520070400c0410300d5200002e0201500b42159036207040800f01541380c00f65610f01c20b5860342c0d5295a240c240030011010000f81002180c006e00c02a95200e4507000c0c502d80c01008100801d2100c2040c00340d1120f14600006000300e9031100407030401c19a03400c1515180704944881d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 246234271 1250 246233021 246233023
    0x1203070f0804081314100c1e05030d1b08150a0614071a041b1d18150118020a20010b0307060f03060e06060a1d06071401050907030c1802041205 63
    0x110b2130130700300c5000f000300340d001c01c040f0703181070555100400448001a41d14103810000c08c1100f0b00781d200d0800e40b402c1c0304002c1036031f004403541c401d0501c0e07030203030040340100403985c11070002c035007000c6504483d000a10700c507404545420350328441c035001c104140058010300b500c41000d440b400c0394490701c0c4100301100c1c00030204801d0360a4800b9540780b408844d940d108244184043c60480c1c41c483d402007404d50f16041a8003903504004d103200d0b2031050102c03a030014401c0c10700465420002d4030081c040c1e55410040d00301c141d10418182240f84a20400070324118030303000040c2c14400303450294018175a08002d4503644c050700d40c0c000329582511070301c407001c100650002d20f92618220555000c02c5200d0f0341e03c40710041444241c544540010041168012285c85804004100705103c07403624101e84990020541c19404580240d42c24001a032014404450070701600d40c01039144002031290034116181d04c1142042c502c9400541c200c104402080089039406a42c024141788104030010300041c103051f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 246235521 1250 246234271 246234299
    0xb0a02091e09180c0a0303050c0c01080f010b0306030115030615050415180b060712030e03040f060f020705030613061b2f0105010909050c1005030705090114070f03021203070f08040813 81
    0x14004d03a0040d011090050351081d80f00cc0d00c2580c0540b17030b0136116443e0070303083c030110b9002030025609952101d00429510f5a000345d1075004501c2910001440d45040d13034045000c0c070481d0070192280d030030100c40c41d1101c00c1c0080c5101c00d0b6500c0d644d07944091508400f010004005586c8180d4102c0300200300c400c140f01c40b05000c585002846d0320107108801c0c4e480d0300541c482c030a5000394513080c62030b52018480b0034852010090700c10703c0c60044520480d141e600103454070b00101d6022001c86407461500c4100032590165002c41a40040303041021001500c002e000079442c0c0030185000c0341499256092240c1c441c40706131a2034402302c020030440d61101c4d0392038042d04010f00306980030b01c102e580700645400c04005903501e14a0701d070348070b07401c644886000b00c034160300c00543d150400480c2c8021071410903100b40201851481404000360684041c0380190821058512160203841c0c140108201c1d541c110700b1405030214146040d03000ca941d549080441030148040c1d00d9040c0c150701002051040c02d0b01c0305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 246236771 1250 246235521 246235537
    0x10e03070e09150c0a090e060f03121c090c0b0310030c080c04061401080601030b0d0b2d090a03030f0e0303070c1b18090507030b0a02091e09180c0a030305 68
    0x40000d4990344c1d64840c0c00540301c3d5402400000d000044100840c0701f6454880350850801021204142d03040c500027071030030b400c1c0d140c444060000010840750803003035130103070988a0180b0f11051250703010316200c0e1000c2c0d01c428810314118040000015140417440d803500c070059940081075070725a5454010003a41c5d8080e11403554042c2d417520802141c2c00c0091300944082c0c0384161340300040d41d42d43c031004402a042d030036401174018000b04a1800002c0040350800d1007078a280342000881001d001e03070b0103072144030003c149980326026030a0090094000c105001104d4041c107010412095038401c6800909500c4038107030460001000340081c0691041145080e030303025940a602200484900b1315000d0322a2152910101a1240105d201c2c01290400280d10303000ba003d68030321581e2074562a0b42c00b001120030307410007680024554044e00d4003c002c4210440b0701c060140c1500c0c140800304440721005030006044603102c54030f151042c1000c00c031034a0007260141c60340c04d00594920f405807140c1c0150103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 246238021 1250 246236771 246236803
    0x10309020d060501081006230f03010911040b04050f0109090c170f06091204031104020d060e180a0807031b05070b0705010f0506011b0303110f091c020906010e03070e09 74
    0x840146c0005c050240005407503100c02329110303000340182a100b21400c81a00103401c00c2c1401c2e50035840380d50070302c100140103000740c0c04c04400c8400c0404120445d04044007140c842c51a000c14031030054201070400307041d1014800c00040b01962801d003100162801d070b100c040d510700261450503071054007040d1140c5260720300301100c00b26115841030307a4071000160203089104070306000030400300e190030181c2c0c01c03000340117440189002c0c642c0040f9001e80d2042d0b0400095011a041804150604029415281500035002c1c00795003002c1e642c0d400c8688031344c100180070042068812144030508070380d003410550f400300c1100c0e0f100395102d010404503084071000341d84175480d10502030000f14140c0502446a10140d4800952992010401c02c18014140c0300b581015034a840d0004881c040b50000c3c011021908030790f54071860001c080218404c4044603c0440450451034040107881e410301c0e131604030a0034200415000b03c0302010030310740314850f88070801c884054400d0101703016010030700758110003544c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 246239271 1250 246238021 246238033
    0x20d0f0b06012c0a232701090509010e1c0e010212040303050703111b10051c0c021f060306060501080103030206010b0d091b060206011409040f02010309020d06050108 73
    0x3000560b15915912005444000003580020f401229503228402018000b0280a003194562172600f000140d0059040014400b1800312101450f08680c0040314291304103140c1c1034114884083c0c0103403070042c071401c62216224004a080c105007074100540300c54a001c12501c510100b0031000c041c02610111100c0480c0d03d00c0e43d02030940d440813800301d02038486400c50034a07091560340d0031900b42c3d121140540c104004280c11000c034910034003588180481d810501008811094200a80c521080015100344002040180a0301446144118801c02051000244920075000a900f0007203c185042c02510440700034400c0780185900031029a40100003c000d065240c400544a00d60b00f8000600540c2c0310390010884011180300400c0c0e01140d04078003040400e40c3e540c030060300030701d0142035402c0e41d0341d0070606202865042001900401180100c0d46018089002040400501400180561001c01a054150b90181d00079004441d0b018010000c40c1c1c01c90b0a020b07004000c28060301c4003901401d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 246240521 1250 246239271 246239281
    0x50c090109060e0f130c0b072f0409260310050a030b0f07030908031608090613060e0c2d010806011d0121020406080a0905030403020913020d0f0b 64
    0x24442c2c10181c4081c84080c00081d101c1d0700b00c504c0151802404515024860f25084000030761607180c100080c03452010150b120540f91600c508140860102803401050041d9441c0c1d90004507121583e003554240ca0004184002d410200c81e82403241402000e5021401c40c3c088048250700c0042d4440c0e00801c080d80180e685500801a4071086440054080d44065020071030554401860b1900280e03981400250800195109849a00210780403452480c07402c4100c0c1d0802d40151416502c4400100544803514211b40c2000c440054110080c00490360b030b00002c0010300b410000350860b008014100c1140070705030000c10340c007440c0041450043c0c03c0401d0704005c17035502440b003250181005841d908a511514002d10701c030030102d800c6082c100400c00901508481d4980140800c1043c20000541d90300e081c688003400654000c1c1640310ba0030f00c2d140070040451000700c1030b00c050b01c3d81110f0040054403a4002808500101000650f00c1641d00310700d03000704a4081400c1052600c110742c0c1c20b00c0e0742c1c1c034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 246241771 1250 246240521 246240539
    0x70504051e0108011a1e030f06100f030908090a0306020405150711060f09040509071e0e01030b0606041d010501080a0e0c0405061206040f0c051e1003021204050c0901 73
    0xc08030741140800c0203c00184001135000750000c05064002484600b0710740c8140301e011900c003408074940c9080c1c10001c10f01900c4201c0401440d842003040e91040700c100001d034801000a00d80c0c034080300c00c06649810b00020404440111a04c0c1040104040031203034690529034000d40c0188125486a0b1000720017040f00d004100c247c0d0300454008145004024082003401000e60041d0308501d107080080000d255696110b209250107424a1002018200d0070110390385090f200010203481030b0007601c4030803c103c09800b0200d0b41501c2e81314024036a651943d402096850207283c0000c040ca02c030304840310004400000d0740701d0490340240d84501c80c07511094490000c40e50303181e12500d400d820442e0711848074106508050340002c00507080301d21042e00244240e0801d28140c43c01c032072409078181e07502c0c240441180041c000d0901280e0309802190034a219419100070380383c0c418010f9148401d0405070034040d9056070044c111111101c0e206141900d802030300d42d860850018170404400c0004116250 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 246243021 1250 246241771 246241819
    0x702061e0103030c0311060a090506240d11090c0c0c01210c141602090606250201090308030408091905030a020f06040b07080301060806191412030307050405 69
    0x400d00640c400d40d900356102294040881141a400d2102c0391a81c0180250100301c0b00d44940041d10000644903040e00e092410503801030088020002d98650780115009505000e1903000c00071204095104450301c2c2c860f640c024440e102c95440402c180400c41d640d04100018642030030000103403180c1e0513000005540f2800103001556608003031500c1e03581c404d020361380b21807a20001c900380b920038144108005001c0358003200d0050909942c02c20307000214284204a150010301c201c440605141054108410342c10a04070300300c00f14100d244030340c0c2c156401810410050340c3c0140640c0d0740c2e450a42800ca40551000780f0490140c011821400028190111524242d07000140a010b040f03040341c0801105113100b16074141e0125007000005150000c0c40c005000302441070b0480c544941c5483c2c400b8081c007000908160041003001700c0003042d6a1100000720949002d0302c01e40031600301e16004031301c0e00c0040030101c0e01c1c644000414040c0064000c80070300304544c1c5c01c4900c855188807140c81c4005000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 246244271 1250 246243021 246243061
    0xb04050403120914030307050a03060801140f0411030d08150d05030f09060d0e0d090f0b0f07030c0c031407060201020408190312060b03060f0f03100b0a030614070206 73
    0x2400b0411520501c01d40c2d5008507514501600e04182c24041072031250b802c5034010344900d00071903000106000b8998143c02544000c2c020440200040607c0005003500706d2030080c000e0380a1140740c00007030308001100380011001000901107944900360860b02a1603030200b03660018041014060451344c61031710048140ca4640e100340914144040800c41440607000983c000d80e1000c42801b1200256000d4420202ca4011160040184e1443e074000540303408032980100e006c4812400b401e114034a400b4044803140ba2107501c1c203980e00c01290030200c07180c0340c840000031b0044554401c000705005411010f4460383d02e4150503210041d5581c0c6040c2d00b00d100d00e01c100302c51038120701c24480b59948aa480156480d010b81007100c402050315107034204032085500b01c003484010210911400e0306051081d450b0346079082d601480080d0400c00020380d56031072075120105030743d203440601b010394690400c40801581e00480c00c0c428980322401e8101a03800443e8241e00520483c000240502040318800300b200c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 246245521 1250 246244271 246244277
    0x30421021c05101d0307060f0b0d0c0e04020f12012007030909091a333d020307120207052404170a120f0e04090230010b04050403 57
    0x450410810b03c0c01500e8070f820036960905080b480c800134504144010000f07184100c00000d600d160600a440c00c41e070703441c0080b50140d400344c1c000c0d00004400320000c000f5662145800c007025030f680c0c030006142c1c003035076a00c03d5002840040c2e0024104415003180300e541c1249070603900c40001c24117840120303016641000d400a42240d104021041d0503500030389035a03008540c40c2c2d600301100d94900e41440c8c2c0039254681c080241600e40e0320b800b58140f8008007038a43c102d84440502c201c050000d8150f1a00700d01880c414660300814409680060900e880c6003907280e509602c0d5000c400c280a51a41c01c440c000707840c410b003903580b803024003803010a451040e030300001d01c1a0186060600d940c00d8208200401d03565848080001050f503210401301c06840000410040650b03100c9803600e1540c00b850750703240506002c100c2e00070010403504035080d03014400b030035100040c6080d401d0001130129100540d0300711014203a112001d10800e0443c01001c204a610002031100045040038042100c030121005800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 246246771 1250 246245521 246245533
    0x30d0c06020f2101170303161b02040c020106030c091119020307060203040f0201020c100504090e01060b070b01061e0210090213150609140a0b0c030421021c05 70
    0x3415603001e040340d16045450b0030b0a01c403056940381c02d2100c3c0c90440b48400c540050042281d070b02c441c0500d0b901c0000081c00745013107081c03092050082d50b844624103820301500b103110040603144040c0365001e10380c000f4028840c0d08004031000c1d00078071060100380e070700110b44a4045003845c0175016161034201c424800e42e203003600403035001610718003400320701003140010400c400103d2420f002840c0998010090910054124400645442000f80d206802104030101d070058468000b002e070b40480f405003001040232407164000a00606060704048121341d400300710302081c4962480401e050320400c0c1c440402581c00741030302c6c0b10b101a403081c0d50707001a80508191032840c41d0316000354003101c0c80501403c0c080e201c41300c003e0b415110215076007008030500000c1007001d168001c01c00c200610100c424802c00c10210401728901a10300d002d80004040002988540c900d42003081718000e00f4807085213014007090b48040101042c4802c0c00740c1c46041280303c801035020520140c10b40c1a0f83c0980100f0b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 246248021 1250 246246771 246246773
    0x17161107241b0507050406050108040f06050c1b0106060216080606010518061204050111070308040807030c050d110c060309100f1b02150708070503040305030c0412051605030d0c 78
    0x1001c0e080040c030180421680e20324400048a0602c0c10b011424420409001c0f15070602c0240012190f8030751023907040001c428188000f00c0d400c040340707400d4107410503004251550303075100900d814402e0010450550442c0c0c5a4a46912010f6000320151501136003034500c0d00c011031716a03913140050760007064441c1c0c12810100e000ba60044000b0041020208a414183d030846000140c80d6008240c02142c210350920400040100a2084900d4081203100190511302c0d5602e00070501c99004100030210140081d804041c54090203c640310541e0080072120300310341c0d0000003850b03401d040a084440740704101010f0407628110041e02e224010b0720380201800e8281c075410310042c00043c9810300344c1d69903882002046c40001d0450560794280d540042000c82450002d41d400700c1401044101003113800d5090000450b03001e8100d03034106405103845600c0c1d0302c42d50a658100d2045501c903149141c00d604001c0100b16006c554070580046e2107070016a0944c1d14401d054582644404140000c0c89084d4040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 246249271 1250 246248021 246248069
    0x10509090f0d050901140c0f01060b040815060301021b0a151e15030c060c0b0a02130e0c0d05071116080607050c0c0d060902090705090f01030c17161107 67
    0x2c009052610030758a00c40741e1046846d0340d1086c5015100c1341c0200a0400c80e803c024058a0002d02c1c5207250300d0700e02407500a020fa1241001c9a03060300d1103006a011500540e402d40595409400050811517035400040800384d0758000003c0c1180c41290b1091900d182c00150302c6440d84034905502c4210360b8002c0d000041e00103120b0120380800d081111b28020011941c54004d10014000740c2c2c03262001c0320207178200300c2d01040008042e684002d0041200301e111140101010007101c00c60510740c41c0a0710342000618003401805030540d8200d10b401d081100f07040d40007030308595a203010003d0342e40d000201582942c0e00b041901424501da4021000b048446100d900189641075030001a1113001da41040040c0000c4a441400d45d032031794541d0359035015403030102c080350303007242c1503040462030801d0801c0484d50f598400c084250605130b031901d500c401c840c003840000365100c60a1601c2052441d1485100c01c4486c00052004000345100aa502c50310000080520544003000d61040010381d10000c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 246250521 1250 246249271 246249277
    0x30903100b011224050f060d0c050403061b0305070201051017031b0f070f081506040204050301020d140a0608030f0c030f0307020106080c040b060324100305010509090f0d05 76
    0x1c60304110b48201c0c080c0d5060b60a1040002c0181c0001500c0581002c04000700d104000340e0700040e01c42c4c1d0b4424894402c1e07650794801c6421f140b601d088041240c03c02c0d000c05441034040c82c0d001409590526044900c208100550343c0c1d001e11107918100250746614004a089030411119101603000307690307042c01502d09501c10700d402c04814801300da00d0b109000c2000764054600801400c1907500c1882100c282c0701003803004c0d01c050020818141807162038180107690b15110003c49850303a800000102d485a1940d0301141e01400000d4000c1d59541c00e800318010081201d103014010810020010907801c650f03600400080b01c400d48015810070351b842007549840c1c0d20071003400b0b180d484100090340d12901d504001d51b105000680000941a03e008603050810f41c3c40d40b04244618581194402c03030765104010b5030307080201c03840c1207510124114521100901d03a0601c80e40e00440300b481c3c940185916410150685e5420380711075041c2e840d10181c01d90744501c907006060840e0058a041080390b4460005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 246251771 1250 246250521 246250541
    0x2040506120304090b030d020105160810030623100602070501120603051e01140115051c02031503010e0f1c03090f0305041401080c0d020a030f0612120203090310 71
    0x21591070801c45104191450b401a0f2082410b1074994801c40214502030001034120006030009001901c0c0105100003150500d00c920350500ca070000101f002c1d080800030050242d944400104207982c0c0e03c50403c04003c0b0380c88400e030940d5103c4000a1034103606072003102c04075584d41c5c00402c074840c109001074a01c00c1c44500e840309400d56840c00000850010811f01c40c413603800c0c001c06201001c40c01d20050039944000a008844101d0750b00411070300c16142c01c8150320241900e0080d44884200003076015003160707900d2580000780040300b0300c1801c41c854281100314400880003003022213000200c1984509540001000719084410038030100782030031924002e680c005140024100055581d14440034620403000d82c00200081818003030b840303a02c0e8205c601d4030710908000c1214135012000401503c40c03c403485180c1341d00498090b41c518001d411111480101100c140b00c1c00b500c1d1072681d642d810700000c05585000c107007910340c60f4a5001104917502040058040c00c040c90b034000501c0060001100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 246253021 1250 246251771 246251779
    0x5250f0c0204050a140a0605011d01030e0d03020a030c2f0a0803130c411507170f04270e1e0c09010306151206020706050a09080702040506 61
    0x80040140e07214410f1922688103034400040c1e59104500316805d500004000d4a109460840c0a01140c0c0c1c04c4003500c1410004442d00107001041c0c080100d0142c51107003d09c044034405c8003140c0300c1c41500b54024000e40c1029070b404204145013120200c0d0407942000b04034186040100802c00003080c484400303c48a400001158450a55591204000c2c0e10484001c0d00048120411070100b02000840d600103000d03164200804601c2441100031182100590244100c4039103030f5003c0c03034201c01c50120300d000d500420940c2c0c2003449003100326042e0f2046078122049101ca0604031003200612058565101960000c14107060401c070400461440e0100600c0d03685075840485141985503001d51882a9100303009031400844078410005500842d4050114030740144000381d88035111f41e122241182e4000901080c400340810040c0300d0280190051100c002000c10b8143c00c1c00440d40080440900c42d40c002c11984c2c0d2092001011508080c0d00101501400c00004025140c59005640c01c070400070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 246254271 1250 246253021 246253037
    0x1106030c0c030324040504030e10031808130605040807120203010b0a0902070c06030b0325150503091005060a063b03010e0d170c040503060103030801050405250f 71
    0x5280240b458108a451403040e0000c600c00307041c0801100840b00c10140251024800d43c00d0942d0040c0c80c9400c18a881d034020700c041500710a800340319402008403000390346264104d99181c5e080010303856000182c0300c0036100c40391000050b65403207801114101c4000f1005085014100010300d204088512011380c0d01d91340710184120745685030f005480007070409400050351400381c1e1603e55023000c5c0d036907c141e052600e04402170707a550701d0100303082018201340030000d8001600400416281c40c0940c00090302c40080d1081500c500e50014000c48c020490b000c110b5440c82c10081c4190117464040341d171650001001c0000b044039a0060007000104510081e81000d03078446400b000e46007052507040d0341691000e000f50039206003828131600410000150181864106410000e0300c103401c500100c1d0a2540d141c4005449151010305640282800a041c1c401a5a4074100244000e40a001d190b02c510302d0302c1d01044a490fa40e000d5400b00d1039a00c3c50201c28095901001e070381e03104404a402051001c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 246255521 1250 246254271 246254287
    0x100617310605150102102913050c070212010605010c170d151802030402061603020a0602030a020a0906020303060114301b0f040302090613020a0c1203091106030c 71
    0x64010284205401c0403c04528804003000a15100c4200d0f17400b402c96240c9120b00c4c2e08018a21010314159150088810541c0096004500030b0150740041218480c0b52000740074000e1000d00040012034000c5030300b901000c480845c11400c0701c032944500c902003143c0300c00e0807000480302c0c01d00c0ca00b40c8510688a5003081001d0649900391590883e01c02028007031864107000807051380f110748141001d400f4003103045107426404155a80315a45501100603134108a039402c041c82005580002940300100b507450303040c0100f584004e5041030012802203270880da0042201c502c00015030784202016599495800d01440501c20706500030741c0c8008451100c45d102101540304220104044000c074030304450b5924002800d4610400b0b007120b0404050b004006403000354240c102520140c903011110b020b02d40e01c81c60009044110598480c2c05070500100d55030709801c0c0c0181c840c05002c4d000e5401c40d04104400d030030031400c8515550000b00341c682051840c52280c2003030b901031a4001c0b40640b54074684004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 246256771 1250 246255521 246255533
    0x3150714040e0f0405011a0f060906090604031407050d0f0b04171c0c0906020a031b140d031a0d0b150d0b1005030106030803010b07031710061731 64
    0x803c9a01400340380c0380100340020032409106901a4454400428465408000004400488148420388140c5002c50381050b05d41d0b0380c0040300d18245c0c004041d203030f8131035591401070300070010040001c4042c01008000204d5050100700c4c220400c3e407049628422000c16030790380c2e41d503d0010b0300c2a02c08d084110310101c0211030100c010468001322800503a8548040c1c0f000c202a1440340c0003030b404208400800304144c640007c1c09802d000d60600300468400e14400e49d144240354035481c0134005840300c00007083e6488022488064441a503038050104d0001c450039240c00d450500c41c16500000b0090f60303071b408076028010340f07a0007a268091101e01030b10944002116a9203204003030350880d4410080c40800004090300500610082d8021b101e003074078540710343c0700d14081441492400c0e43c001071040c1c20541b040f25803085801c42502103070841e091440782900c551100d8026200400d10342150074045146280140b40b00304000112004182c000c2c580c0041548400314a52107012450781d88500040e01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 246258021 1250 246256771 246256799
    0x4020618031209030c04061428060c0201080702010504021509130e01060e100303050307031d010c02030c25060c0f05010c0c03080705120106081807090204090b0315071404 75
    0x2110314156610390b03d201c0205404c01080e007242c28403480c41c0120400c00050802c085100c8480e003143c0c8102c06184412550030a45262903980c101500000808030346a80c0008001e41070b603002f0303609c1c242c06a9500400364206d41c0c0a941c0654807440601000001002d1a0000c00c10308401138988000c6681e1925031400f5941134080c2c1c9041030b5110308082c445014440301440c1d00c007068626005801e07156071009032040c4405482078040549440501c1a40d0030000c0c4029544003045008000009914200075202c4d0051150b8041d140641421030002540010b9035002e030000943d40c080c40076240020030740d010b0700551400c0714060b5821404c0004141c0a2141c0004241c25480c1e00c00012038900d0000e00e03200004058900340041849401010904481d00c14150b5211f424010102c1c1c1307030900200c041107c2c03040554030301d111b2a1404074034114a0703005403080303a0b22500140801000e60382003640340d41c090814030b9501c8103020005401c1034410072040c803004018101d400c5c41c1c15211441c2c00100320b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 246259271 1250 246258021 246258043
    0x20a12170411040b0d1101260702010609050a0905030904050601031103010e160c030f1805221d0327060d23100506090a2d060201050601080402061803 66
    0x9401e400d00c074211402c0c0f500802e00c41210072100302c40080b103903507694149680c0c0c540d11141003106602514107440e49513041d06610045a0f11100c13040c2c501a07038000d020300058050350140604100118806440c54080c114070a9407000103181403045000a0000606000340304a04254950300c0d4060034240e924029406800200e0340c03220680f9003e104540912810340190080080c10740c2d031140403d92001e5424410401f600e0078054004207641444004245500000d610207034941c1100000075000e003807810f1b02940309506010342007078030030821007a903003c441c04111900100410a030070115034006076090130381160010340d25004540440c45a41000d88480c00041e6509800c0f500c2c070b000c104041614460400c01a001450450100c0e032031490184105070040c100030414003900d9544000e4040949134802c0c02400c2100140542c0d500d04482c0100c0c10100240d00d00049101813060013214810541a11005600e80300ca900b48030440d84400e24408003e40541c45100455a091103041085 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 246260521 1250 246259271 246259283
    0x3020d06020412260f04030602090301090506070e010912231c0504050f0409020a0b07050f03121608040506060609011106091e0a0209060d02030a0f030207030c09020307020a121704 79
    0x24080c5881c0d0014100110594141404028440341d000d054a01013201d007520f5000c200275803a002c010000c80d026095141004125000303403020080c40d01d5000c50354490064003642c9088200d48d803001074291003a400b14000e40344000300100600c4040e602c203203402c00c82d6601030854002103c20300c03070a0f461110130310382c4000280c00041d081110f8a40380000809001046404114646142d4005100c204032441001d54000d8082044c4052050600080748010f010400796a90f0b03175003050880c404a102201d40b0442c02050b80c0800400702e2046480703510071544280201001c0e180c035805c0100360f0300144075140c10000902c411225520b01805554000e0154000400c140d0f0300011801c0300c0b44106259031580360b071041400c040540e442100e541d400181c15504140800307850b002090034042c041da1f000c0d0440d00000c00c0340342010750006652085a005e0307081c85032480d44a52044c1c00740d00c41500c5e18001a4000a1568041504040101c03804607903402d01e404440c60744105500c1c0000115819144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 246261771 1250 246260521 246260543
    0x6080609060105071b26031315140301030b071e080a090c0909120906030b060702100c0803040b01030201080a02040e0402150c10020d0b0103020f03010911070605180c01080105060403020d06020412 86
    0x4481405541250001501e0065820424203050301e0304401c400f8030805960100d42761881d00360900940d0401a02840890400e90741e41e100d0800321801d001c140e50800010300060340100440c5986404981101c815654500b000c0e00c45590090160801c000d06582c950044d0400007420304e01403066440d0700d8490b030030b55100054030400280c5080400e80c420b806040c1001d8030070306199120805c865455904903085609500880b8003200c92240700c1e0002408510700005000900181e100c03424100d074800d0717840401c2ca542e48440340d03060b801913106486242403810007140040c6803250081d4868200404641c0c14408081c0d0a1032421620fa5450042d040c0c0c001070010102c001f50041d003105800078201545041c0440d408100c00344014032600b40d01668031000748031241204d41c00ca402c40354000ca010312550414078071102d030b01422190454940c0c0310740307540741c00c6c154054110075040f5a0000c00080c20a451034092200c2c3c54080c450480c1d40a0782080082020510241c090440901071004091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 246263021 1250 246261771 246261809
    0x3062a030b010806010f120e0304030c06050304060515490309050301020f04060f140d06050108160e060c0f01090803090714090402040c03150303120606080609060105071b 75
    0xb90140039107180e040000120351054091f41080503c0c843e50140307040040c1c49500340440c18150b005a800084c5040c0240900003803a40e401000f07980100c1c00f40b01704110a8889403512010b001a04524980022521030802601035030240001e4031581518641c5401c1d00e003001940d00e04808041d1064941c0c23020124010074160300c949030801074081540210710300600c8101a040718000c62048000304110342c501c0b504564450840404500c8d41c00c8a500e40303940030741c1401720242200d8010310b400254040000342c80300861203400c44542d481038941d821400124024051642d2100081507114894600f000040800911942d040b16000700780550300c80c02c0103041c0724109452a80400021b10400780c0c0d842a641c2d0324141d132030304107034115000110602c0509056000c3c00f12408103142510504000105168000406034482c5403030940400c02c20792120010745640005480090f00440c1034400504554020001001e03041e0140b6014428130100d00c0038006503080c180c0001070b40f0f02d82020605 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 246264271 1250 246263021 246263027
    0x7140706021203090705090403170702030405151204060218030a150c1805060a0903080313030201150b1206032d0c09040b070f030e0118140109080403062a030b01 71
    0x15142d0180c94045500d1400e05100241d9542024000c40348900720800200c0c081602480342440304070120340c45444c1900e80148083d403260018869103006005a4100062a071900c204641080c010b44d182c41034540c0340ca0300c2d948029000b00707000c060252002c040b02030865070100841c15020303110b00c3c403030ba0001c00202510001e65601e01c50000501180c0c0c10384200ba03245030640a419100281e940a482d00c0d80e0b80001c071014031041d40040c04c410400414058045e650040200740b83d400ba0b0000d118004100482038008c801c944107210f8441418000104a08801030809400c00c90083c1101d031100c14030804102043c03900070800190a580100d0120301620500c20107545000c01c480000f010300d45a03c0c2d000c0070f1503005105070100000700c02c541d60203074069409031121507070400080104800111140d25000429a01900e00c003c1c40094030120b284c050107885040795120188a040c035103540e842c600034061807200380d41821340918104610310301100509241400c142c1d404141c10503200009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 246265521 1250 246264271 246264283
    0xc070b09130501030209040f1b0312080f09070e0408070501020c0601170106180e0f0106081f111902010e0a0803060f010c02220b1f09060e0a0314030714070602 70
    0x101e5405062034010005699008605075006800c1750b00304010225601c1c1407100c0c0302090340041130740b03007005401109100030315120924420482c1c60300522900d684000e034400f03010459005030550300410091110300000c0d450560007510550b00c0c00c1c2070503095980c3e2802d81c1c10508540740c030380c0c0c44400108850719000c40b2445454600700000c0062604005070740e6141200c0d202d890721080c3e03d5030205061220200244a00c070810342c03000b00859070b1642101500d580002c19190301081c121111600c0b070052078852441c0c84d00501080c585040503101e045c0382100e403103c0b03051042d5540d56401944058040c003120640c24810200c1c266a46811806c005804640c011114104400805c1150040c1c42d020041180e000280503015440c1001e00384000c0541900c8604903000303207a0a0105031204105013041208035035a848011006032618800c50340102420241036020b40800c4c02000855040103080408a0207401039030301e00b0f103171511080e445000d650702c10b6015900c044800c201c420750600c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 246266771 1250 246265521 246265549
    0x30c0f0423011d16050301030f02060c120307030b06030112020906120111030103120f0e040f0207081611330d0c110705030c0f060a03020909070302070b0f0f18030c070b09 75
    0x40b004c000c1d200d0701c000801c04e0005000081000c103d10140205542d92041500c0da4140c00f031040320304440c1408051000d98000b0b907001c00220f400d03c5041891840d044050703038107840140d888980b0001035034003000050040030700059000301031901c2c0441042428000c001e280c0038039107041943d03540740d445d20401040c0800188010811150514a040ca90142041d1900b9408560105401c0171b8040701d607009120708440108105800101481805002c6000105035030003401003c5860b003000007881001d024140740d5224800c118030150898040c50b403633404a481c480600c0c1400c207000d1b951410300700c410320041076000c05d003400e40b080c0300c00c90304211042c060b00b416406031a011012201240c2c0107002008030911515010035101e94040c03080d0305403079034110003d04c0c226440c04e00781c1f809402944120f0341640c8071142e020002d4864040d00c00528021a80ca8822250b1907848130394600c4e4007004a9075600d00c900080100b0304070302c8001c0051001920f0000e9035165190f14060400c1000e514a190b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 246268021 1250 246266771 246266791
    0xc0e06070321110d060e0906010308030406090312180c09380a061809020f0a0507020a050307090e0106090509031902070b071202010506030c0f0423011d 67
    0x819400002c0d482560b0710540c15120000c00c0e400b80668800388041e024101510843d0100070030303404003840131904950304440c42c0710110324060b100d0b40c103215191403090101030400c3c402000803e001640c0c5a109450f941c0c00303458030a403d818811000e8007580d03103004201483c01d03003032284081070150100e0314800600404400700900311754440c200c030000d501c8902c200282d0005881ca40d250081080b41580c546078010050381025032525000303400c4084080341c2d130051408560011403030340e04a10883e4220108640c401d424030030070740011600c580c010030003241c00101404d80021030743c8080004001504840304089220444240d155007150b80717075840080c1d2103091805112103110701004071440c5541242c007240000c01061000c0e03240c9405503102d079110520004006040c0000c014004440daa030701d900912640d203d450070150784040801d00c0310b60103605002c0a15440ca001c3d4400452058521415441c03945421003a900f605400d900c442c0c400c0301704a03226440d000b210220140c0c800c003a99 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 246269271 1250 246268021 246268027
    0xd050a0507090b0a03020c1e100b010c140a020a030b060f0d020a050603180a03020a060615120c0e0d051e0f0307031b060213030201090b0c033a0c0e06 66
    0x1c00042c03a22229114064840302c00045001c00d01c1c0c40382e01250701c903440030030031260b81c0f02024204024a408046081e90b13280900d0720b2a41d018040e600481010781c00507964105407215644465010296082c07003d103c4d842840c21000041e1126118540251300803540c1c001d90b0310302102441079800040078114495060360600c0401a900c007a501d000752881a50304c0c0d038036543c4030600c0f00f025941e6008c0134101882030320001c104041d8002240c0032509d120b01d805000245d6130320994040071003417004600c045000e141d110b020507500c507400b0207040392880c0760640b09009650081002c0c44183c10041d1500d422030b8a0240315003080b84240e1081c201d40384010036150110212003501ca000e142001806c019881c130100c03402c3d8118810400c00075403c03950441d0f6600c1100916003210031203210490203c0c0e00c01e08001313200300b441030542e034161b0303801c101a5207010109030b81a01d5068000000700c0c040c54010b01c90800c3c450046509039130403800c1810000321000344500107030400102d1701c02141700300b00170 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 246270521 1250 246269271 246269281
    0x9070509100305010f0f0e0a0903020c030f070602100c08070c0501020d09030909050601022415131406030303010f030b040501090b01030804030b161d0a0305010e1b0409050c06130b0307050d050a05 86
    0x81f190780c0e200d852607100068500141c81c040f070601c2c0842814552521984621510f0b40201086510372505540c08881c0900102c80b4441e050741c101040800225140d08005080a0300821410200c248036100040c0380000089514007158654241640080d14160092224004603c11160004c0007400149040590001c95401d007a8054030814000300750f503004070f07030410f01c50b0b606002c4031030303000b00780c3d850b00c102010680004216420614a55285500200703541e0b050110803641a0340c403889011590508503110b14210140240089610b59078a402c1e11005c00c01d4001140d000c0c5103d54a92940c880c40c40c20030b8002c045024000010103450b250b07000c074485801400c0411003001300c94812010800e14400505d8070719295202801550070140c1c641c04e03a1a0100310b03501409802d000c804110036940c8240000c8590b00701d40100785510500310001603103088006022211044c910700391000351a000281200e40080c1c640b000031130030200e40c49002505901450394480ea68110812031490701c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 246271771 1250 246270521 246270539
    0x1611060c04030f1401061203030b0d231905211206120a050a0602130605030603030406080c1b010b090c090306060f0414010e0702060c0307020c09070509100305010f0f 73
    0xa14400205004a0000d01404100ba5800303420100d40c1104001c1005035601c0f1f01103030b20030691080442c0040e00d411844000340c0b40c641840c00b030941d04244500c0711120140d008120403001000c0e0140a446a2106a94a030420710901988203110318041e1000d100283c000c125903400c541d68000340500c0902c008080402c21140203130b840711080352030401c0601c2d500c0d5401d0404401c3c43c8003600074014000408203105054005003105060300607070b248000e90b502c000315110f00040d01c00c3e5926410070082004840d110f5034242d50854180400309141a00050340355441c40010b031003c10740c994580221001c14548003500e55800486070308841d1a01341e040002039183d5000030025440703500c6214015410f030b103031903002d152501d00c1412803c0da41d5848860012a990f4210b074100010710603580042c80c591a590b0a40b40242242d400620020482d942001202d00000f016202088014829002c0f10390700c0250b65840320b840764400060f0f41d410b081c40f0010030502500110801200c2c0f00c2c0070070803000c3d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 246273021 1250 246271771 246271777
    0x703090f0b0f070201050c0a1103060703020a141b0d0f020d0801060507030c1b09090b1305101a10050901090f06050904050a0b0a08070e0a2a0908061611060c 69
    0xc4000b842581c0c4151520068489005078000d5218910072005c1c9407080104200b501c0707005801c1101220b200340c0e20200110180d102d1005d04c500040c8041c480c010501c000000a8020303001601007885803e110320ba0003074a03202002c0744c4100000c800c551040c143e1501844041102e488a240614480d81010b102074518800c40d0001410801191140780a02c00c000f801c4007101040c103010742039025503540444014050f0301200340c03141d241210200c0e51084a038041c04240075840406803800b11000171140340181103902100d08002c0342d4160321241e582e2240d0307807041d241d55142c40e010b03202c0781110300041518030260054a007100c04600c003802020740200030340340b06845c00c60f00442e8a66800c2452009481000b0146400c060912404030341094045419001ea5085040000e100d98038540980243c500e00c00c99419012290070000107142c800341c8407a070501e071160a145110f13503030301c00820380340190807030b281e4040310456003011107150b501c4070ac0c0a5038042d4000040102d414003416244240c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 246274271 1250 246273021 246273037
    0x30201050703090b1602040605100806150d020d06090506032d0705040204060309050d18060f020c030706030c022506111005090a0308090a050c0f12010603080703090f0b 74
    0x1c155001010301c6110610068960712001544030030640d00808038504a84208070300c00e45c281107001ca034a04124080810080c0302d903485503815100c0700d0900c02c41c20188c3c3e03191140365604001c2103c24820701d0000b4061611120070000700d9038548138607d000c89601070080ca202c2c1d048900c0c6008140203c0c00e49044460300c1c034074010f0740c0303048400000f07107015032540c032060300107001080008581d501544481e0340c01e4010000e4604c4d9421f107d100701e070106c4032401141c00000060005101d49481a4040146001c1d140111004561130078002403400c82c450740914000390f2551a5030008640c1804060b0808918420320414440c0c0310b020b13025040401c3c000c150410800d80c2c0400c2031240100551002c2d06d20100c000c10035070030080c0803135441e050007036010380c046501a0301142004000040e13800d0062742000c041d10790460a0340400c06d010145c1000d8581c0844e18040b0640d19140a1284500031071062414039170701c000501d0060a0a0000d80c420000c0c061084410030221401100f00c1e9491 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 246275521 1250 246274271 246274277
    0x1d04030e0102070e0f01090c2a02040923010606030228021f050141060d0c1d060c060708070306030b07030510080102090a030201080a09080a0503101a04030201 70
    0x504031500100e01c0e0490726071210b00000e0607030060002e40c1004642c0e040c140e44402000348100104601d05070707207600310394400414110740903070302070480d50745140d1501c5c1c1148010808154140180c46040c84a00030b00c01c0261180c44964108040b080c0074800d0400134040c50609509000d10380703141e0304110200c0274043c0030703008501c9288034001c0d00c02d0040303405503500f498a0700d5050312401e07003c1c80100424044c03298040e152001c005100314900d407004c0300b88540414071903011144500500c200101019400e07401c10000d100e98050141c690050103c032007210f03501c418072030000c4112a040900e02c0081907000300d134100001418001c01260040c3c4c07000c3c444c2401103094403040d00850043c12581c6c0003800e0030004109002e01e440d41900041c3c0100c130550000018070b502c450140d0b080b841591801640840d003a003042006501601c40c0c1613000300300c5000090007403040e880d5906c4941c88000418002240041006100d40300080f514001e0321490b04124910295070082c503441e032003140070107414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 246276771 1250 246275521 246275537
    0x109050f040f050708070801050306100308090307030213090215030105090c0c150a0e0f010c052a03120709080106180207210e0a08030309030307031e150e011d0403 72
    0x407521550401c4802d0140320354200300ca842c01c10700c010042003060340d0358800a0459000001d10b482e000410354002c120101c84c503191302c0c5c5165544005640300e502c040d81c141c0905500040940d48006486040400d4064041782c12641d0303104014120f01d2a81110040f01e40c2400180400c0d100c02d11000e922103955103030380d40d846198420803454000c4d0402c4500c100c2a8040400c11008219003150b140403002c0307000c46050391031081b000382c00e903080000c05500048050003400c42c40da44d08000174030314402c081d084e03580c1c41d0028804181154014040003040654503400d200b843c0760f00009100003400345000070420181400e00e1200c107100010400c482d401e0b0045008001d219903212101104400000c040807010304542c40941500440da6095105000100001503800008000c581c07149a01074003071491a600c2c2d441c150010050040d82084501501010500e402085e200d011400181e08820703158052520740302941c03203401600801400a1042c1299001c0e42e01050131503003044d410308006035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 246278021 1250 246276771 246276799
    0x3090c05040902010c0807060f0507030513110109090920100801090207031403150f0d02090c0a021204060201060810020c0c1e0a090e2404080f0f0d020d06050a05010905 74
    0x2d4101141e28040c1050030001072807c200320880c0d0006415007400d400501c81e40d5648641a0211441110504e51480714200350b100081d40c000b125086500d0141001a215a205d2000000319482d40314121100d49003000840c202107900361200c5400e01702103481c06004081c49100914880041c820a21080d4000c00c0d0401014000c6201011220840131040d48901e031040a8000c801d89181c4c9844c003030203040005100a043c6051108580785d000303042c00c02282c85002c054040c642c010100c0d5021401210b05480d45908080c00410007002c2c954004262103003013004c0c807403e160440440031251780c410030001c40020008260140c140c101150350103a0400002006410f49800c012440d0784038044007400300301c0030f8850f880780344c10300c22130300440346924001e007507209060064948824142100c400080c000034810310080503540d021080540c24682445600310403600034290981c107003a00421480e800c429184140c400900702254103440d002d1a10001174240d02c182e00504c1e00980c00c40074191 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 246279271 1250 246278021 246278027
    0x9050c030321151806210a0b09010e010510061101020406090902070609020301020a0914031204030210090e04031e0306050a15020a120e090c040b0f091f02071503090c0504090201 78
    0x4039900e0303002c0c140048102c00c04c00500149542183c06501ca80c103041041420080408075480e9290755610007002c0701d400c16181c2094068008091648540d01c45070f0711441d0100a0007664003503003401261054550403d54007030105072441c601c2c80c040d40e00c148010000325512082038070440c1e08600005a88240e182041000381540300d0b0040d4040d07000045000740942e02203a03c4044441818030800c01700c41c43e0702016250040031301c04448a01c018001030001d8680fa00e1550000401810f1541307915544503550440c5440c00c03107051b0702248200f00b60395080d00d4901101d0740682c51070714040100e0750821000490000e42da00903a0041c0d5043d0031400b0310b05008020140c1107e070400425800d00c80780c1c42c1c009201d010030004c024002c200d000d010403008110f40c4141c5040d20140264a42080100c0c24004140e03009406d065500c03e0010305003920290003001b08844861880d40030302130181c1411244c101c0388900822600401d480e011108002c104c0490b81041030381c170212004a00006a40012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 246280521 1250 246279271 246279301
    0x51c1409040b060d050403050901090504020f0706021b0607090e15031b21030904061d1f15020f06011403070b0309070b1b0105011202091902040b0d09050c030321 71
    0xd04d000c1d2030103060200780340e0014003074202e00d04242c1e1a45043c41d01c817002d2005034040c203400710300030b00d00c140010b1001411940242c14922601010002864000e83d0004d20345001580c250b4041880701a0510401d110301d41c0035a88039200400c4007088900990102e651a2500c00d00b1001c881d409006c00741f42980c41e01b00240c51028a40180040800b1502c1c1c4680c40c4d41c49108454422481c01070000f40030141d60a0360749030078483d50050350b515504c03080f0314130b0400d59100f40c01003034084843c03001c640036400864903140c000142d40201a031102c1e1016251406c641a003005003c01680c043c000d03090360b000111007027a2003560003400c2d12919821119881d0240940080901d110003007203001301c4001a0a2001a01b4900d4009001c980d81e100150041c1018048029402180742030000764010074050300e5002c040c00c0d40300c0062415070307030305400c0d0781ca60480401444070300d03120000c98084c00f10400c80c42d5100c840480182d460102100400155000c440d484003042039945400158800342e0b602e52 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 246281771 1250 246280521 246280537
    0xc050307051c03080c1c0e0c01030908030703020304050309040c170604060b04062d0c030201232806090212010f05060307121512061506050d020f040909051c1409040b06 74
    0xc120041d10031000e2560140c01248251421f9204030100d0090710761090140314a140e8001740290315503120100102c1c00303540000c2040c1c445100410040704951110300c58419900d045039180c01242c9810340c2c0d44a803200c0094400c034030950820506024020b150401c0301d0407100399082c840c40c07400e82d4454040343d01030f0309440801d2010185240100454105600c00c403510310036802000f1540c0742c90f030f1880d4a0f01c0002c12021120140000007000e0805d00c01011070301a81c0540e2810210340c0c0d140824050780c140b40c0200b054a90003048030b001c403080a688485c00751818000c0102c1340e508010100c1e025010050908007001200d0400001c480e005501c003211701002641d100344103a40320042d440c6025201c40040b81d03070070324100348802482041ea01c111700340c0c0c51560310036140078004400701c00690842e002c1220007a03002c0000203085006403041703202c80f030711450141a0103140c0844071040f415110240e142480a0003611403003e007180c40451b4400c46080358001042c240d4000829124014200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 246283021 1250 246281771 246281797
    0xb0d0b1203040603090201110318100201090b01080f0c0603010e0c07080708030a15091a12152e0e0a09390503030f0409020c0a0c030c050307051c03080c 67
    0x5408101c02c0d13411342141a550b8000e88801c041e6402a00720103540344a9442d0541c081e1140880010342440c0c01200a144070601d8400811201ca658840840000003030b84140c8280d40010394140300e048041c80a2503071340c041102c00a0a6602d002034050860100400b07001c1e01c0710f0006458030411060344241ea004507008504692249091a4040010107800c8500f4034071000c035100004d0703050b62500440c11642403d440c1c05811408d25001d0150b80420009461014054004c211402c06800e138100c511070b00d80030001d501d840c48101072890001000411044651b0300504091159090001680d90088004500000c486000d8240018080400d11146518618800c40700556110803400643c41c6207900c201c41c18126544c40c10035607248200040b0014041c81440200203101e000d50140004050030030660307180300c03c20380d6140e04188058000b11040f141280c41442076090800c0484007404040d200b44c40c0c406152440c4000d07841072484010100024000000c520003030000a0b03580320349001c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 246284271 1250 246283021 246283027
    0x210050402190b09010e0604140409081e0310080d0c080a0903120302030603060a051303031d06010605030907050d030e09070225090e0a2a050604170d03060b0d0b1203 73
    0xe40b030f5250380c8404060f90002d030001c600ea0b051490440b040b90112144020b102c0480045c0809003c081c00c51800140d5070310005214449458095460000c010108101e5942d0380349018102c001007180b29400c45102503012550381e20400c2d810448440b049a00190fa030b03600c0d02591041100c0415564000a0bc1020036044007440260181c002d14003e01c0700301c00750342040e03882c840004102d407030468405401c94080350324032021038081e0303009405d1268802030308011300300e8400c030081c5404402e03800400010000420042604000d00400c800b03000b08881080445200351001406c0d00c1c40c28045508c181c40c10008681d98500030001c401890b50500000ca0541040010b0581d450480b0312611010508000700b654151038042460b0700d03082d40c408200c12400041003240e00481b107044d00307800c6003e11a81c0022a660743c4200142c801081c5d01c03480912040c10a105190524501400400a1504180c01032141c1c1074010700340c8202c40c0e85040d0010390310a441e40010302604c00c8030314003900c0d80400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 246285521 1250 246284271 246284279
    0x809030409020d060303032412051203070e13050f040b0c0c07030c170111070b04080d0509010204090c0e010f050d0b040e010b01080609130b060607080a03050106110d021005040219 79
    0x6800542c01c172406034800704441d400700d080300c00c20300c03082e803000707942d00480b00e44144100507981d680744116602400c11503520b403000f080c10205a5000355000c501249090503204000c0c034280b000c068500070321040c103204c1420040c3e41c180141d1070103013004190000d8180024505a1a20107550704c011644048a050303503940c0c14400480405801849600703031196480d0310000c03070140100120100803048503494100591956904884050021140240f0401c15200010800d00915014102540006a070b41e86841c185400301d48000361844240a03510b083c1c080307180c6e008802d440c045041c07401d045070f9500281000301e00030080c00c0b104c194401c0c5440007030f04003040150b1003c9034080082e00c9200c00b0791118402c222401c0d50440e0f586201c00100c000400003c0c51031400150006400361843e801c01860360364541d459040810080002555400100710340da40c0041000320402d180d50142510b4107454000035240c4500090f600d0015031120081021901e4480708030b44001c0c12450440e09280e15 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 246286771 1250 246285521 246285547
    0x6220f0b0f011e03110a120303020c100b01020309010f0905060a0903060506040e190602040f080c04051f0911040902040602030c010507090f090902120d0c0201020f0309030607080903040902 83
    0x603a908a0609080c01c000f03d03104400c482ca24603248403882094030010700d55030b25600305814000d0031369000050036400103404c0d00546070f40e40c8158469200540c0302d000d40082180b610043c43c103494842400e1085c1a107981e42c010040300d140400c20b292105501541c0242030758108559072080b50441c2e40000c10340a5198401040c4c03058030b22900040c8401e450f490208816202c0343c040d18102c6030000e4040c152811081c3e800821348034810036003d801d0541e41c1c910125104141d601542442d080b8241061103464240710f8250300c101e00d1030380300070a03c4103040d2248039100140105414141d484d07503103410104550055030000d1107645c0081d942c65849400084d100d4100090b032081c01d40c00c110103da050360040c4803003016103245060603000f0624100c0b6000c05851814800d981090000d18501e03d444c0c1c041c4824503c0d4003a6444018007295644002803030306140001c6116640c03c1827103003c0b455a80814050b8019001346808428bd2702c0c0d01c01520306600c00c55210044070361001420f0300190740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 246288021 1250 246286771 246286793
    0x3030d0c0e0a06020c120f0a031101051b030606070c030219030201110c010c0803060d0f050d18030c171e010614100f050a05040503010e100e0d0206220f 67
    0x107668007201d407003062041c0441d050b1070f0b00400001d40c03c507a0308a01d140c1006d44032103040c600203a044a101c00c140390348081c01c000b450340045d40007a00d4440d948078000402d010351900401c0c0384070303080c1403d080d0102c0350340c6a0002a10151003064000b810340280f04400c154032014640050481300700b0381800717100030108441032100301c2c04141c800a02c0c500500000c10318004121043c0c450b0044502c0d00d03650340c44c0c1980000c080c294050802601d480210300000e0f800e00f03006110310010a96010110405009040400b04105182c403143c00e050000030071001217141100ea8100b081d0340000003682981c0e007060b5030080c6414100d101020380664803041504810100d5155442840d104442d00d4180840d88040c0081c98003c91416035100300300c9032150004004000d0940380032400c00d51100006800d6a6010100c00380e0340d404502e200b03000314040d2040d04544030803680204004610503038082d464500c000c0a8460200c0c4900810620800c49117200750007a6001800048140003840d00440c009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 246289271 1250 246288021 246288041
    0x3060503151e04050c0d030c140f060c0f16080715090b06060918041113020c07090b1503190e030a1805150309010e01060b04061112030f130203030d 65
    0x509115144080d18125280c064083d0b80c20402502190b6001801d00403941c400c0c0d84114100400e1408030008a90f150141c40d09620b9010301400000300c1d412502c40c036285014020107191310081005076241c9a1407405c417000d080c0e03000c500450303641d06410700c003c403401205005420a01100020001e20b00140d11002d010740c0306000560240c0c840f20b017448840d00402400703907004500b42450f51000d85404800c654020300c9040e10a109070303111360100f400703034403001100b0140381d07008a54184100028401f035006041c10303c804111141207880000c0c034114450400000701c00d000404035075803200d04000040c00d101515400d002c030040d8400059900d0f80001240307000115001d041d0681000c00040301411260010190341e211009501c1b00001a48003030581d0061750f40c2c60342076000c140028013903c8000c104c8030800da41c590b0b01e00f040c040c1c22500031545102050f04008900c07071b851454042669000300e07009881d00b015540741074114490305891034001c1d525100208200d802522190401d0003c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 246290521 1250 246289271 246289291
    0x305101205030415021209121c03090201090b07020306160903050109030504051c020310020f0c15100b031603020705191b0e090703060e0a1e060509061302010e010306050315 76
    0x506480b04106e856229007240d00c20500802c0141105030728040c81d0700f0380a2041241511200c65480001401e40a0764542c2c000100e9101c10151081d982c120200b040284807007442c1500c0d1040070307070000361101030092600103000c4000b0241c3c907a02e442407203003c019540c00030082080095a04000d0429041880390314880c40c0c20003258003042c030781c0300c5c16140030507400350083c90b140440b00d440c2000f070b401865982c1d010040601420f00c0b40e0604100a140440c043c95440703441e81001d0b1000c0b40004520f4000b03c151715010801c1c8000141c050801d030fa81d0000300e03e00142c459080d8540103040030b03070550014084400200662051044403c640810010f00e1981410103603a26480485666000c0312104501d0b00300302e1082011642d66048000503490810903200590025a41c41160700f040100c410701d640c5074940441f04101c428416a504000352000411480c0341c00c80102d01070402012009040016140400d90f240e4001d800c13080203014020241c2d07001116070140d8441220044410b1020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 246291771 1250 246290521 246290549
    0x31804090515240301150b0901050d060902031602062a0409090c05010e0a032004020f0a0306051005090f1003110406021b0103060503030a080c190216060e030d03051012050304 77
    0xf15207014491440c4c12018880002d402c1494281c440c07003aa080b644030a0306010041090144102e014440c80c0003900b08020010388a0404080d082c0ea50904d00c1e01000540d4041424400840010155030304c5d104814601c464107007114084c40911b901440d40b026100c2800e050b038407010003418907600700039503a0a03a2001c00b0891404e0803c980e58030284406401000310b86004040c0b9021003c10802640c0090400340c50b140b42e40a0691940e40040102c00000e0fa46100c24081d518080c0c05020410f007052900301d0805003041c0000c0c11402d03103514114891014a00c3c120f011a010703400044000c01c0ea40328071a20b8a955800203134840f054030b4185119a004200c001c80258020f1045da4180c40000cac005608149603c082035036049800b8140600c2f42c04241b0000c0d01841304a142000451440d60181c840303c1c02040500ca0101c00701d420003400d100b284626942c8a88000489010b800710390314011502e600c404a103045090010b400c9040007100c070200d00414800008000c1084507030211552803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 246293021 1250 246291771 246291841
    0x302120c03040b0c041203080901200d0b0103200304140d0e03150c0a0c03020f0604060b09090c060306060f070606030321050c0403060c11010c0e040b0102031804090515 74
    0x2040717110324001c10107940e01501c149008203102d41405640704200700d00005485009101d020101e4000c0b048070042c3d8500012034190051484c01440c0ca040b60a0030b0500a60502d001104000050280c00c0300601902100140c28060030201500d0000070800a0300d0303045400840017050500b014501e14024495815549245072040f0080e80c8a101c0380040d06041c0b20444004545028148105130118401d03070007104104c407002e0059501032813244800265201505080c002028801070490201307400c98003400a880d11104110703a80444215a5190f5503048220b41d488076014421010f0817051410902108041d005000e001c01145043e0300910725040c107008190580c0d204503035a1062290070720081000400c260080f100f414a1400d02210302c21200c00c2c01070031a00c0d00c401c103100090b180003407901c01d400c1500c9407244841d401c0c4040c0d487c1900507800d40c0c40c00f0036101c4201d0701890362035091a09000301484402c0c40b50711841c24031b2080b070a00c40181040b08010701203400b40180401170b482 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 246294271 1250 246293021 246293041
    0xe03030907051e0d02010c080c0705011119020f010c050f03090f030307050714130203160e030f030f031e07020c03061014010c060b0a1d070804020a150302120c03040b 73
    0x1c2046403d1040702e4400a0a005206000011400407414040c40c10f14080004070004040e0172114414401402000c1c40c2c903000400f80e40404d40050846c1c0c1001014124240307040c44184141d9405640040304015490b00485940c5200d11000d0018081e0a640c403040b80004801404102011079050b04502c805c1c074201030300c1e48030f03049008015900c01d802c200310242141c400306107940390085c280c850407640e42c080741d0227991040310602c100c0350f00700750428102034000b0482407001a080e002025a00b86030980b031641ca04c02d4940140200c0004800102c0b40c52468031a40115014443e0003116810209800f175501c0c0d80310f4001d1741c801d0260b0702c0000c00201644480170300b211400441c050380e00400900548030350710358804c2501d0240d1140b0030302000d503c8035080d000c0141180403a5061800000526803503080700504200300b001090000e100c0565142003149054485220300240c0b012440d080550091040b207210101d10b258180c100f1042d0061607002d540b20303a001e0703140860243ea03031450f15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 246295521 1250 246294271 246294289
    0xb0601170a050a090b091f050c0a08040f1b09050c0703090501110705121f0c05270a0905161e0e0a0b03040516090b0d0602070201020109060e0303090705 67
    0x54040880000544040c1e20307500031940144480c0c0c00082c100055854642901c01c080350306800f030380e10594501c072844003000580125004015020085406d044580c1c0c2c98a2190452400c10003542f02c1c0864107202000301c0090350705a0180084c42040d00f15045600d4890040c03240b520303100c1c5004009602c01c10300600700e4070003550658611344228200340c019210018002c1c013822041c4200480481d050300c0d64040484604103200040c0402008000e10494010ba480d901d0031142d800c2c804480381140c0c020081c1c41c00300c0e001d180105010301900d108855004c0360001800ea00040c840c20004070800030380e10241c0a8070141804800e0020204002d4820002d403580014010720410400e1a00a10640307100400d010020000007076281da80b03001e405690400c2c0e8080e00c1540050000825100c9030341008001050804401d1005401040002e60342804104003d0309142d00001c20504580c801e6114138040399101008104c2c03c1d07040100d940c0e598001701c80f682c00790310500d02c000c200c030f29140ea20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 246296771 1250 246295521 246295547
    0x10b1315120f050f1e07030b01030b18060c04060f0c0b01050402090a0f1e1e030303110906071a07021b0d030903020306130501060b030610030c0e0a0902070b0601 71
    0x5242041480c0100c0020307021001401960042500b0b04110001402804100341070100340307005149550650b0350701a06840207850700207641c1d1101408000150341c20050300d04480c0c1000e69844680c3d904000503943c4030100000541900481d407c100b68000b00c00050416902c0c0c80d51100540c1c120a4410303174041d094407a000d40600f106100402507440c3c1600144481e1f80040d014100d62542c4525110724858281c1104806032140581a9444804846140001c01c0c91030b000611081900300d00c04000b4080d4040602007603120f0141e200061501c2c022505000760241809946922a050240081320814601c20702c0680c108085a140b43c400149410025501c0b140c40034281085400c10004941c00e041c200c09000c0740c0400000581d900748902e520131b50115001e01c00f440750301d2400a00316551a086030461020070302c1400351341e4507100c1d40411801308078200000c3c1c05402103025130340d03039a06d112800d030f0020b141240030a48241c150013a000d0749100b810010515240c0c10015282d038a10560b03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 246298021 1250 246296771 246296801
    0x2131d1806190b0a03050606150a0c030309050a02091801050c0f16140102070b090606030d080a0903031e020406030605060f09090a0908040b04030b0a05040818031608010b13 76
    0x45441150020141166900082800911415103d0200c3e01c0f140580e0f0064800e90018800c103e82c90524000d5600014130b940d405604d070a03403021000c0e001001d400e10160825507200040c0b02000320070007000041c81c1e0028048001b51a10a20040c1c0ca9004450030b0f06141d404c0c2404125400040d03000e0f104403070038228250341415081c10340220f01501e0641c060343d4500500c1d40e0100c0204080c4010216a401542001c0c51460042442858400041c1405029501c4075407840e2402d6840502180c1007a540e80001c1a00007080c1421070240c95503081104510001540a01e0516003560007041141d215407403d02003a541d981c100842d60103018441d100c200810040f07102035251011407981c1c13101c40054000b48203201da86840c00d090b00a038020b44402c4400007018020f000d5400500c030ba104203410303030902003458070765034400c140d00459503d00d06202c0c40c00c54108180d80c043c00720402082c0c81e20410f012144d43c0d212164040d200c1c000c1d02030702400107444405081d104a00540901c44160300e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 246299271 1250 246298021 246298033
    0x20705010b0316140406090f0506031209030a06050c1902011a09061302030c041203090617040c0311010504120b04030e0109062a021801140a0518090102131d18 70
    0x100c50814040c060300405c1d4041e984400210303005003184183c92030340e000480c0024041c940320062610709034102c0820a40c0381c00910002c0c2c42c40d0b400241101c80b0540c40315000c40c990703ea0b0345900e003041c051102d4040848088031080c242081c0d0541c015017a42c80b50140103808038500c01c040c022035210580c8c02c541c11403452040650346004c182c00464000454183d106d191070303560b800d1500320540840046000440402c0100031044d84440760554401103010858018100ba980c3c04184040a1100503d10524103400010300da01a00a84e0020880c150001182c28050314141c08406c9040f01c046011410f5405100041d5210b050741d02c003038450a031a6044c182c500f1300d10178028000010038941481441200320340050b260002111420002200c45c0c00c2c0c91750400c1c2034400d00c1020503402c50b00441110340300b00718a5842c0080844e01c40f55142d40d19070243c076528882806482580301d4250b4148030000c00041042d102c5945003081c141c201c9011403142c0b03994409030600c9000e600b10074180c0d0321031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 246300521 1250 246299271 246299279
    0x41104140a180c120c150219050106090c11060f010303080a050901110d0f050903031009150314030c0106060e062a0d0f0905120d05031513020705010b0316 68
    0x2591091041c24242d148800510300b0941d620f10380c4510b00d80080344100c18040c0d0000800c03480c22280340140c01a1141105000300302007000b55642e0300544180d40441403c89240306001b02988500080d01010030140300c506907401c0007815480c0d8020804175036101c0d28002030310703002420342200c0c1070b281d1554036903100e03841e01100c0d24083d050280c007583c02e95686918008074140b68400030043c84408840200300103803407864010407640010003109061700200300704450b840141855000b903c2c50f140300041c003900c00c480103101c0704503560001024511102991503c0120000142c182d0f0030388403000388030071615078000b110200a404109130700030009021884080e4642030200300d03001c51030f054002d1001c400b810080d00d003d082c0d01c2404049400c000a40d01501c5d4000f446001418050703402204c02e454203480d5560710200385070900c04100010000c46c0301b4190158019048407801005220900c083e1ba80345402540548070884056103000c1c12140d1508011648117030022243e907081d400b130740c58 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 246301771 1250 246300521 246300541
    0x513060f1a040b0d05090609010504020132040618140f061c090c051002030c0303042a090b0901060e0a0302091b0d05100b04080c130f1404110414 64
    0x4100c107000c40200341808085011041c2e10f02a1003400d001843c04146410010b107154201100a4600b80c9541d0510b010000980d8114050310032101c0701001008164007403881c091f800c2d00b9480c4480104040020300012115441206400505d8000300c030035240f039540700c0328190600781e80441d1a8028070454105901d40c50b0003005071024014031221000141445011801100c5888004a40c0450070a00c02c0c892402e00520341a091281400210320b8000d40c0f00016969001c020002055944c64514007841c51809411626002c4020011510b065440d502540050141c042109014200c20000021154841c3e60004e429100241409071a141076800384980054000c2c51901d00e0400685800c506550100062045083c8464001070500b042c0154014030701c5281e115000e10b2800384400c1c488064041009000f00750200e8495054104090300c0d000a4444000000c010902c0c08694104083c024003e03c1e01c5207120380c0740c009014040354204411102c24602e404800b030b988034000313640149 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 246303021 1250 246301771 246301799
    0x60141010905090f1503010605032d060108101413020904060b060403060b030f0309060301090c090909080a2003090105131a0a0e01080f0c030621070513060f 69
    0x10040c58203980703598503100032032000007094890b000102160390030803c4c00102e0b00a0210294070490092200510341000039a0b00d180f284401c5e100c5005024650a580c030091000e201d2641d021000d83c0e40320741c3d449821503100c2e98041c011005150409500300080003540340d4030752184072a450251030310002030f003d02003041002802152626030750900c428070b544c0d40384054402140700d0302c0b0209000c02010305060400d000c4684441d02c903407040c4140e1003aa0b4681c010f59045d5203a00400043d81d002010b01154140c055500103102c8510705a600b0301480501001030040c004642c6440e16451031284000390412500c2c24a1045c07a00144100c10072584204028402030056031002c45030551108401c11542034642c4100074142000561455055048032403d84074070b81c00d080c000d03404d18000814075031002c0e0042101ea00c0c1140000050f1b01656401c034403083c20003060300ba0150b03404210840c5030b41c4407051f000f45441518060701c0504e050394140a40300c1501c409106030224903151500d541c0c0584 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 246304271 1250 246303021 246303149
    0x50109050603011707050a080a110618090912120402010e0f0303030a020f0403081b0709050c040303030905031c05010513090510050405030f030a02070c08010203070c03110c0d050601 80
    0x20145d1240010196904200e04018190304c0b0b0241032440018581005800d820740c10880c01810148039045401045801c1c5459080d400e482008080d0380d0010701d141030040001d45002c07002000f003a06400201c40d2809907119601c00e03214070580c02c404004205851800442181c3e050b4010400141c0c0c0d4000c9801401c0a00726090f541e03800d0a480b643c4003e250b0b0424402118844001c07010b0349414901008040700400e000c04041106081100d5130180901c290b00001d800d00d40c80b000d5a2040050800032103114040000031002a0b101e0300b45000b010780803e01c111440303003640d41d11143c2042424852241520390040041061010000710203010380320081c0241e030076002c24800043c559200301e00444c07140402c1c450040c2d49515034980340000b0380007a000209542c0c03040c02049409a02310b0fa44465007038041c2403190f032251241e011a0310709180116001d4101d214640780400304500081c1840c145c40a60010366004140518048034040511012220050951840704c20100310905100329007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 246305521 1250 246304271 246304273
    0x2010b03060c0c191b0f08030f09130219080a1e090f020a080319030902180402120a080417010c14030709270c03050717100905070206100501090506030117 68
    0x90004c1110036940d5505901c1030358003403c892001c186145c0301605107005040c2c100c10407440c0390f0609000942c0c84c090340c3d5203080c007281d000940d07000542d40d52a140703450340040c2106641c1e0300128a0004000724810f45208082820000814070031403050068149626a140d02190911407140d11240903004018069a28403c140c6800016031a0080307044042c00e540002907075929101002011800000d030707580402c240c03400b0340460040c1c1d0703103800e40040010000c805805c95186e41c0001854610180c10204c8a4855150150b040080c88005402100e098501c00f05502100111541c02c0c2d42001c080040002c401048030003601c4031540c051608011145850403120751180342d4140e121110f910314186286064450714580b80a602520a407002c09107800c0c040c9061591020b405100480c204c810002c946100080310012003030820300040c00240c0041c0032a05109002030344400056a44440955080d54042a554010380002c002c4480c05048545180e1814401060020b0340b0325125841d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 246306771 1250 246305521 246305533
    0x105010c11060408160608011203120213080d0908160b070b04060f02070b040210090312050f07050118020a0806040807080f070501060f061101150605070516060c0b0702010b03060c0c 80
    0x224100030041103600101c0d00880d4500c507414400301910f0450160b0004d400e90803278155450000354003600c816070b141d24002002d03880740c0242402501c03403d0240c00c0b0310414482d511a540c0510b0344004440c0c01c90720208203942000100290b90940a00e0600070104030703942c100316110004055643c0700d68468000c180024411008461708000c0ea8050081a0b503a2065801070005502d01560000c1c40103895041c40341d4120314541d110108014844002c1003481004a15903040c2d942540032140c040e680140200b00040038040c13488805041408164000c440052012441950000d00b01d0301032a041078000e800c3c030382c440d5103c001c240d111300030700700d000f503028401100000c00902030300b0f000d40f0310000b1641c0c100d810108001c280014180c20740c000c50f0b05088410b0390901e50100050191752081c900340b41e4034203d41c00c0030380c0b1389900c800c24286044803070b403400214190705c01000d0a0707143c810706149600d611100c01c00c038240c51484c000558540c100c0c0c404071302081d40342c030002e2a400500e0030a41c0c071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 246308021 1250 246306771 246306779
    0x1e06100515130308041508060a150203070819021e0606060a090504020c06010311030106052101020714030408100606020309010e0a050d030302090a0f0b27040e0a02030f060105010c110604 82
    0x791a0020b500813221520701040600400c0c00043d188001e100e55850052240e140c10340c0000c0013030485114a942c0721000078101040c66100344102c030003442d002207205070369680900c0740b945682e0b0355081650050086c04031003060041d0072a0f400ba04d0b8411000240303001d41b1900100b2100c0e030300840072841400140400003413551640d0000d000d0f0061681c019000c150700d1410714403507803000310b6020792180e40f4000042c4103d980d0078a10080580281da02c140d034149010840c540284074496014003249404010322000000c00402401524a000107464a0086c0d01040c0c03015158240100f1004d60014480c4c036440d135104045104075031000030880071000c0da82e00040b64103020701c551b05038006500052145100c3c10f0400c09413004080c41e68610b201c0382c0c5400e4000400b405483c81c000d0000d8000c1d45c40c8450001007503480341251000030810840014841c0c002980c80290340400c0380a070084110001100d480458468100c98060311505980034213661100d01002c101000290302ca041400085 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 246309271 1250 246308021 246308047
    0x6120a0b061b0a06050601110a0b0a0b04060f17150105190f0b0403020910050a05060715050106080a0c031103160309150203090f0f122503021e06100515 67
    0x501c0b00c540907200e01d5581e03041c07020654000070600c40c1405161007402c60324183c00140d03c83e00c250002004120358132594000c102809010440661040c1003400116801440580c09021030b01c4800c101001c031481028050b8a41e1644030080714150100c00040046040610443c090423090f07031945040303140c0b902c003601020840ea0b00301d02c1100001050500440c245403a840e034000e40382d5a101c44040d0314081c00130b14441c034a030185174007440300270800d03a0402100c80c0310900700403c1440305120b00c2da11010001e00c0324404489002d04a400c04904141403030107440f4140050785e400e005940740da0b8030050a442e00389000c64210081590340d810850224441000711006000c40a9015035642055840e0914052503e01300d4907254102c012201c00b900000100194040d03982442580ca540f2071680e408a15030880d804540302501e00c2c4d944074100b641c040f856115a41100900101700f505040b4007598a0400f01e81031910140c50002c00c1c44240307442640600750300c01400482d0b10f4140b25119603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 246310521 1250 246309271 246309307
    0x13030c0c080706030c02030405031009030c080d0b150304050a03110708010203010b09010f0f05070213061706070216050a03060e031306030207020906040c1209030516030503010305070506120a0b06 86
    0x3803080b90050103050041c10707450f00401c180c4a07098070041d820941000b000030744980f83d2008021940c0c5c1e5070591042090f00683d28008540c0d0001051904c03000d44810403c081c00f48140c0076031155403010510f58070b10301c00c50b040c4c0f40100d8110004000101e80c27a9000d640314008101010800c1c411000009000c034803d000450190040d0120551a0a640000582481800d80440f008c0c00b403030003210110158803c058800343d80c1c045800c0d070300c00e03146030b80c1c000d009020b030360011543c038012405a6810440c1c0021018051300f4070f80d084400c081c1c402c00c0c100c11200e41901580707601264400041000c6403c54000e442c7c01515801a00e00d00b9050309407444100c60b140d40481c0c080703900420749a042d8a011206154098011340701400204400c4d50010a0f1003481100b801605545500650038544a01d09460301071000e666030320320000301c1d030901030106d0700244411130313080c850100041542e042904c03d981482d9001050a0310030380350110200003802100d00241e8200300d062000340c0100f0010b59003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 246311771 1250 246310521 246310529
    0x1c110706020c03070504020708031f05091f05041109090408092205100e070f02010609150512010209030c12010b090708160c02010e010e0f130501061704080313030c0c 73
    0x2c040c84400c54080c9400c150380d59011505c25403060054038040b0b003c220072264842050000e1540e241c8100d8a190503da000c0d40100790040c04c0c2404115801e4001c0c0302501e0300403101640d50003919a42c03010803058900700102055000c005100a503120b040c110021a00140704030031140c1007442c0003000c10800d02122031100403400302040310490f4041c00703204058000000122140040f410824044e4040d80d0161102080020ba0100001110301c00e50090000d084590002d0041950040782294001018011988100e002402240b0344480503c2140c6400700c01a0140c00b0860030300b000c01c202c4200c1540c0c0078510703540350200400c02c2c0d0381c0d0240083c41803410343c603401018102581000a00c3c0140c420b540180b05095625401507078011070301d035003001000d10300420004440d0340403408a2404d04005030b00f01d680130080101d1148907801c618140d03041d6550301c0d07840070840300c50081c240000b034501030400c010410114040100859407140064060304000292032410b036200d45061000e540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 246313021 1250 246311771 246311773
    0x60c0327030b0c030f04020d0516090b03010b0f03070e060a15080429010302040507170a06080606030607051804020c0f070302040501050d03080f070216080c040501060801081c11070602 81
    0x48240200660b2125003500961901c855a065150100080f0b401120140c4041c1c41004041c110701c040280401c20780f640441001c0c0b0181c0000d50b500c15440c0504406c0503218865420300d10300c00f829082c900f001448527140180113220013842c1c80c0f140440380c003024001c107801001e00400410784a5004004410510444d0703140034451900b418641c0303d059440d40100e898001343c011300a840a40240d00505490b0110740002d001c2d12054000c1c1e40000b04038801140311044030301041f181000310b500c020116040003095918913a0b0300c00c201a00c41c0000c40b03039100454410720044c0c3c0f40701040704400d0710780403020341b00500e801d020310081d500d08180c0d000440b066501801050045041c540103190040c10181e512220103006e5540c00b81005070010901c085001013200011840b44c4208446043e14200c441c81078440c6455482c000e0710f5841c0b0160381d5002d0303401c000000412030320807076400307040b61411030140803401d811000708070045004105070002c012101e85c80f141d07a07a03c01d1003010001c1c21990 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 246314271 1250 246313021 246313097
    0x100b040b030f031c02030105130c0306090603080702040617100b0a2d0806070210020c12120f010803070312020304020a090501080a0201110c36071d1504060c03 70
    0x107004c140c4603c810000b281d400c0d401400100165203400c807001500d008249070115010414082c02c0b4010030640d88038180f400d0403d800001403040010003452100e0099405110713040e210489414001c10100e070403c40390303014840500001c040c90384108844d85005000e00003459a0f144a4408008140d00d4030020030040c10240041d800382d490264010a003180241c0000e1401d080040d48410b910351200c1d00740b5400040305080e220050000000031400001015140c400d0030742641c070342201c1142c40354040d000710340001c180004008191180340e985640d64031110580201124040e400c050400c903044265041b0201c2c0a00c0c45010341800303041808020030720054240001005489022039a01c482d810603d0039a025864505d0f4140d8521620a60b04010a845c0095a504e201d18403840c1c4010341105030a00690035031002010138a00480d01c150401c02c06044c00704400141b00e000308581a403001c010402c07200c3e008451103503035035002c2d003080b1840401c21025007110341a200388a500e404496 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 246315521 1250 246314271 246314287
    0x6060b0306120c031b030c04050a020703020f0a170d0b0a181406150a0225170624120102070c0905011a04050418080c0d0f020f100b040b030f03 63
    0x540300c5500050030301c0100243c49504000c240c40c0c8024161808905940c8110046036860401800300d554002510801681c0f40a0100c1d03c02900240f60403001030050400b190880380e00060107166164201e2112040380a0460341d402e41a4890b4510141d42134643d05100090f9a070441040020214043c100c1110700d40b0204500481e1400030746056042002414001c0e1502d40d54034375451a110400e89540d01d518184050389040c1d451a401d480c1e15900280c0da90428404403000030440308a0300c0495075046503c03480d0740d01d1351030861300100c080d1000c0d45540c0b03a103280010340d8015044041c4c29a050b0340c08a56803075003640c0c0b2007001903070140c009102c10411811248200f13801000740e03100b44055149154000440380c45a8822244180e407102c004800121101c007103001e800d03500c101125030303138041040f0070340e202c4003d0709032000813450041a00e0455400170400203045050900504190030350a140740e4024511a812030f074000d07a85100c52652501d040110034860148000155124525 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 246316771 1250 246315521 246315529
    0x9120703110a150e0d050f0d0b13090204060e040b070f090807030c1e06020a110301060b0403060902030f010b0102151306050708010f0f03080904021602060301090f0b0d020906090c0706060b0306 85
    0x4802036110705a001003e445d80569003c81919050105103040301e07502e0b0003907209000540303c1c1e041c03410f0303000c85c010000c030102030f031b081d030010914520a48090200c103590700c12540e10418100da01902208084000405540c85030603c101b6420b403e081c503c0c4441d40301c40303107070b490281d042c2c004035001d0031040400d000780c1401240c40d00001c5800403640b2801410054000d44940442d20b00130124005502c02140d2a9002e4000c40090300f68031310b0298560790340c2d0800e50003400e0200e405074002e0180b2021800040e0043c00783c1d100e40c26060700204000700f240c490010341590000c10300012050001c803404001070050040d540204030940c0d94450650510303083c2d111016841c0d012054210080900300005103c00c025940000310403140141c680c4a0750300070f00700c1d500311200003c0d400301c8004000300b600034880c2e000c84c44612503e0010400350008200740520403d4003400a540700180c0030004550b4500b00345025444191882e6203800d05046a80741015502250811140f105000c0100724980c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 246318021 1250 246316771 246316781
    0x906110c0601050901050a030f05010e030a0504050103050604060509010b0c0708060709030c1706040b060d1410110705030d0e1603030305180102280302160803010501140309120703110a15 82
    0x541280d801d41d495240500181c041f001300e20000701a003001c00504014001c082d8403141003624181c05590740c900b86003500802036482405201d0119140c00042056400c141c4644800e4560151041020742d003400c0da03090b01500011a846243e102c1c000e0041180386040c880719014030380b40d880b414081130562a00340d031030032200d4200340960390710400c041d43c00c038200042e0079802941040b440b45c80c1d40c858102203900d080741440b0140070907000312501c440700b03c0001250090043c548400b0010002c81d00c10300085803052840c064200e5206000640d407060080d80301d00300407000d031421103d8286260149a009500da079109401090f911400c000c244075081e188052400c001d0030086103040808050800710a695408002e414103920240940250080c0d045452500017040e405c4e0006030640ba140c50305e0340c070074000c041c00940030084d48292900094241c80c0691450009465030b04054a21200c00d504071000070b804201c03061030410070740381e0240089074940e40101ea4481e102840c18420b0740643c0c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 246319271 1250 246318021 246318029
    0x30609060209090615070f020d141005090106050307150216140906090421271a07080d1509140405010e0c030c010e0a0801180c05010306030c090f0906110c0601 70
    0x350b200c6080985d0502c40c0840b66840c5d40203441d5203621215001059048180e40700003070583d901c00111804402000601e400c48103d03d8409202598428800c1e0342a1040740c0300e6103800d0340c0007910612240031400702c55450b05405104a41d030010003010458010086075008143c0c04a84044130502814a404866404002074440110314103044d6500c4600e510070b03000c03041c0942c0410f0701d03a030f100e98400c0d100760169051003040400000b551003c0498507800500c40c5a9604014506840855210800313544100ba003042d1381389c0c1040c003103005201c0513044801c8030f503040c48100c60010402520364840c1a40c1807000c00b03010707801031506142042c06c40c1c462800482042d0320058a80749981d40015085105013401e282001c4084040800300e040c41200b07411200e940e500b020500f880200c040c02d1503100c52405003042542490341c440041d8101e4000340001b81492040d8a414011f42d03e00b5001105003c0e000480080c5504441e120760307003116900e01c28058401000100d04141940402c03c242c050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 246320521 1250 246319271 246319279
    0x110d120f0e1309031403070306081b0d03110703020a120302060a0e030a0c030c12020d08070302040f051e09090c040b0402120402010f050409060f15031406011202040306090602090906 80
    0x10500d61000181400e400702d245542c9281c4034000700003010303c1030200c061004c2001000f15203a003801100503010304214003c210403072081115825100144032940740c10580050708400406410391802c940d600840102c110291048081c00001605d1700030b403402c0100484d2580100c658400e14000f4140310018000941c00c0e0708141c49030303100d004007100b110703101401ca003025410362141d03190503103280f100c26601400d8090303551180300341140c01054441440354150381e14074031580d8082c02982203010b14040e90701c450811620a01442c144003000b2000c06500706101d061441c0c0d440c0003e81c8982c0222050300494110707811000703981c101401401c2c02c801c422a003e604010381c071501080a0000104080e042048802092646030302400889000e045801d03814410b00da100c3d90694022003140c85881e00d00c45903010310300001e070300c00e103d00b40907914201c40344101925000011075648443e600241403d903400c0000000040705032140406d201d2240c4030240c0c4990011040001282d0b0040400d802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 246321771 1250 246320521 246320537
    0xa110304020a0522060e09060f0f040f0212030318060907030203031c0204050307090204060206070806011e11030c100e060c0a0302030a0f050a05040203010630110d120f 74
    0x1a41c0382c0c00e0303880c01e481e016100342c1991111040c0c90003010610089884486141080c04280c01036180201c0e88146540e0044504a403204403002415560440380721a1030417034240482c0c0028014032158252070300040103850352101e401c0f00c4504660041d0b07488150301d004800c0411981c8000d00c41d050340705411101a02c1482d107140c0100e43c4078400d4800303e40e0100451182c02c0c9080009606a4001c0c0101074200c80001d0345035600c41009501c0b501801000d8490940014040c03881100000e104090695a0018603903022032400d015420700081e0006000e507412911500d10400c002034600121083d004100c1003040010389003c650310310081640c90b80041c0d04216510300d00c802101d4580c0c01e9442c0040c0e8940d2650109001040b0902d074404255041109110000c1e00e50f0f0882d034041c600840081044642d90080102100d869220511500054400342d0701503070000385c51000c40602521103800c040c028200050102d06040c070088491140151510072010751003ca070100d036000c10f00b09190 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 246323021 1250 246321771 246321773
    0xb0d050412081009021b0a0c09050a15060806010e060d1401120b011e0302060f03060111060907140a08151009020408100c0318031218020618011b0b0a110304 69
    0x3c040325080c00766821198002075000300d5400056030b4071810483c4182a1160b1031800e19001c40980ea1910401c0c041a0610000c41d85842d0700b80b1520041d11000c800d50414545401d5043d64504001000d8034140807070618800708a03111800200a14200700e81c1c0010b04178082c04524441c0e01d410b07000060807030624000600001d0381038031b607076065030120b0f20580d0002c1e1882484c08900002500025000b02c0c0100304001c0c3e01389890099401a0001d803690506071103188056a03460340c0861342c0c0c14096010310410010500d140016008109025140d644141e8a5801052515440c03402c81081c690040d403c0003a0181da00c02404040c050002065142900e003c000f10b03610108046210041680d50488200c0c1c0c5000b944040560800b410144400f50040d05010f0b091840c00c0d410040d40f982044500c9042c03003119096400c8250b07000b011181044006194030f502c11300303401160b80c1449000703a49400e190348403035089208a0f11403803203100d0038940614100d094132102c040c0c1401c900810700c2840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 246324271 1250 246323021 246323041
    0x12c031011090f030708070b090111030c062404050907061106130215040314060106020708070b030c03040c17030306130603080a0305151011010501080d05070b100b0d05041208 77
    0xba480c8071040b0781d00ea2014070f40070000b90400c542940700f8030591144107000101c0094000162074010004d0701c96820f00c015500401e5240e101d440c800611503088400041c201c1031a4a04064051a40140340e0113241c4902c2d02042c1160415120346800b64004031003040030742d07444440d0588080d0204081c0099040008002d0351a040805001384100c1c6401f000034070740c10707800d01610021900f061441c4a1210b203003619907110a0203001d400010300414101103008007001412004039103041500900d19604c1d42d106070344a03080a44200c0305c2c0c01442c00d0004004c3d203141c4c0030070001c407500d101850303403401c0c800200300300e4080c084032142d03000e03051040030400300d43d9800c281c1c0d940740311760708000c100d035956034042079140600318120a41c403a00340000c141c1d1195002c2182c02070110a4402000207988842d0805e40d607114148009002820406c10200099090110260400540c00800160b40e4949010707107050703006208120318059841040100740311360210a105518803500300361065043c9a4295 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 246325521 1250 246324271 246324277
    0x6030f0609030c151a04020f04051512090303190c090311041d07030c0f05090118020d092a061e0215010801150b0a0903030e012c031011 60
    0x80d201a0366600160145030280c10704072129507228100d032070890341c1c0c1031408004119104a600d200e028500e420700142c203083c402c951314110315504190074103141c001001600e442c07800c00b80c0030f406070a22400d6800c040c440c015034000c00008001c0c3d52a40340810541c4d4504203140c40007510942001c0d10318a540c1e4002d01a8416240c0118200801c07800d0500440c02811104c0200804070b000f000058919042c041900002c0d80d10811403000b640350b0302d400c4072101c290340340a0554800d56842c01041659120321150f10740722200340015050034041e00450045a04a540039120745400081030b0303505003040c1c030031b12900c40076140e03441d03030323400d0512200401d4422014090024041459074401c91a1f00070040b00d44c0305002c00a40360060343e11103140602a05e98010304c46031600d4468000b10345012070f002500c04e09c404035900c84010b10714680742190a11000c1d0b840c203050059018010240c190000c2d480c00560450210b5907440741d40c000141440c044644481c140d1283c64420700d4400b1405031411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 246326771 1250 246325521 246325523
    0x6030c120b0108011a16050d0e030a0c12020120010207061b021216020405041406010e010303050703120e030c0d0f0f0503040b0a0e03070c05030c010e090f09012c010f06030f 76
    0x1d16400301d40c040620800e48540503d2044581c6c501c080340c000c001f0001078100c03141c07056070b540c85a084403c03014540d4441c40d54100408503074540d50103102c0c042e01a50a203420a0051401041121170503290b034410a4640b100b0302c48a9400181c0c120034007241d8010750060b910003041e11210b66403e814002d456080c4000705004841000407440310328415200b00c5502a80c000380100154202840c080c1840000d10345d10130014020400000340050403064118101c5c0d8150f22010b02d03003100ca80e000c40741c00c1020403c085840703594181e44070b240901000980705002000004050707040041d04054140c3c07210000d00ba00300005c0601004a40d9440b005990308650f0052121b1410b441e0703004128003516010440c0d802511000ca200e0050015280c0304034100d03081902515003c040000044880d6800100001e8008c0741d00c0010942c0d4402d002c500c95404081c00703000080e15410a400206e0038080c50000d9010303000c083d03840350b00e001c1c0300b803140c01c1c00700802910401c20f8a186580d0488040e02c4054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 246328021 1250 246326771 246326789
    0x4091b210e030c0d0503010302190b1207170108060601090806151e0603070903110f0f0607020301091506060e030d0f080c04030c121a0702072108030106030c120b010801 74
    0x2000310100c1080040d107100c3c0880350b0696400070810749004245420900c801c0c0d1058010b405004070300120b00843c141511912044030349802c104c04104000210040d1501040040101c0a802c1d1416602c0016000e8107100b070140485040101c001800d014154000e01c51982061083c440301701c03d0b200000c10142c40c290381c003802c40702d200003000a180f001d1511540d08584000208415940d028542400fa203102ea0307203410b1484003160610044030380703a07122503402000841c001d0701c0c1d6280c10701c05030003141c0c4028004204d128440d559020741b00101c1d901021031540780d042c14000d0740d07000345a401d283c0f0019001010074046030980100b166504407403035001e000fa20300104034804411001c0b10007541d002a501034030344d5691200d44107070a62050b016100c0d403a0350013216920425181d10240102910340c002c0405500b03000c1d0100d41c104401032140320442e00c103181680007448103000756000302240d88000404c4514000082d01d2070400030015625070b40361500b8070b13a25a070416200703419204210 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 246329271 1250 246328021 246328031
    0x1a0306130611030f0403020d0c050c0402071b0e073903050f13060806012607050405090a0f050603160311010302070609140709020c03031302040b0604091b21 69
    0x108124000380031052095070070402c0081003058400654807214040c502c2542103880c03007082c141c0201c50142c1400c00081407a002074007000c5040c80c054019107409800b64414403044121592509044c3c0000d80c020782c104016441084000c58000e80180d0100082111458003100c11042c0d0101d04c160700245812041701058080003458852030945079400616a240c2d42ea585000c1444004000280304800018052000241e01e6520450700a03c65203880b4240c000d001d10101246030381103400500300e0301000818040041ca0740d8503540160f01a9001c0440011034006810800040c0c48005007118082c0d44108450a807290900111104036504002034480000c1c0c0070004a029106501015140506002004007030148640030380c2071044040046561031943d0301200f8050f07001d007607909952034006100050a1602000001246074401080001e1802c81000069480d82261300000d281c04d07178842c1d021100b0440304510120300500c90070136154a0568000900e400d100c44d41c440b100441d140d07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 246330521 1250 246329271 246329273
    0x905061305100801151e030c1412040506010518041e0c080f0d030612060209061b150106030203060d020d0c05060409150f06020703080f13090608011a030613 69
    0xa186030019080042c1400000c00385000d0003800c1d0031003070042d0241c4d00c4204081401c0e6501070070f903c10b03c04000b400c10460152124030190014445851054188010030b590740c048103503c81c009050042e0101c00085803414a41410f5142c100160491401030154400011000f40322440d21a40158403120301170801154052180c4000040c14004004c13108000c000b00c2c0f64000842e0601a401041c003c031050202c03400811415504030b4810861800800c0415402240c003d4004000845028081c0380c0b07000415854404460f444005c042e4450300100c3c000d00740c2850090b042801400725207015810340c00d00130001050104140e50003845042c2407510941000121142c03200200b600803c0d580c0c80700c0c0d03030f140c888002d0014203090422040700210046914a2650005d406580d410f44c000d00c401401d44d1744110503944141e407861807c8609000508000380880148005402d2030000482e04500e0300100360b0070342d02d0480102c0202c112070b0f02e611000740c50015000d40d0042c844550601d00110b6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 246331771 1250 246330521 246330547
    0xf04080f070b040f02040f1416020111031e0106020109081602010e1503010f0e100611030c0a0303021e16031413090902100503100905190c02060a0509030901090506 72
    0x98008001e05004102d001c00052129002c2e03000c0c0b0640c020380d4284895040700007200300300c0e40c040001900d001d04080c00326081040f00c1d292084201c0d4140000102c041c00400480c039160070441e5040d10500c1103a07424910142e00d0740c0058018200b40c0003e00500d403a541e503000c103034055202c107410700005145150701561322a00b1040418a006003c1e11043c0d600c0e000004c4070340d882406140001121500006003040301115418454246a4a4020f000c1e0820400311100001d500f00d02c03030907100070711450050321428001549280d2080e200165640441106031080807030301e10311100e50050610141d4000c5200045d008041945440c0c60340c80e55085000d46070039800340840c02c544d00d20310100041035250340743d404a0300c0b45000b201c00008100f0044403c5615110488d145c4800d0400800c042200078115042590851a0401c071240710f00e00e486030704000c46100e01070b07090059010506002c5910034a11915400034002009035140c07a0049001904180316813190901604002512000d0246 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 246333021 1250 246331771 246331777
    0x2006220206070f120c050c131d0a050c0618040c0201020d0f1509330504020307020607091e0303140d020c030406020c0405010f1511070602010204030c09050f04080f 72
    0x1500030115034990300300d07043c41c8598680c0c205044545070089074a001c2c406010315407105650341e110707004104400b50348050180007074004512241454480d41c06200c0303001c1c0c587c008100386021800900240c0c01a040c0a40b400359031004450060f40f0400991029410841054503020f505503004100c1817030b20b4804038024481d60030040d00182c502242140c1801880c0c0060a03030025400d04407102d143c850300d0200840d012035044001031030076007030b0380200796085d40d003018007201300d11240e105000d079a4008034080c2ea2089401100581042c0100312050390041c00310310280060303566a060310035440705420720b0a04180005801e202165000010a078a84030845018503682d40003036499125070a010307941d035005401004003501071185500564209842424100e030141c0e001201054500740030400f0075a025183d0a0803ca00303140c2030908603004102240003440540d0005039030754a1400d141c0d541404e56085500f00600b41001c1c010000c0403640c86540180e001814584e560710988030451a030702c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 246334271 1250 246333021 246333023
    0xc1c0f03020a17070314060a0608010536010608090c01120b0301150306050907090506031005130501050f1605041a0a090e040302010b0112090b010605090f09010e040201200622 77
    0x4254070404c200c0d5036054000720b43c0a0031017000d9006030388501080143d40b40c06806840700065070000108038515003075030160500907000d05c0220740d800c511140302070107140c030f48074446264191200400403e41e2142c00070368000462030103050f00384034880000f04084504840d4841664039001c110795540d5080d071200c140410b80c4103580081c5540c07464900d0142c10200c1e4504258041e00c00d00051501c4240102ca104140c010080c1c0504030821821200802c8040c005a1a070403e0044440c00510700b48911809030f4070581c6620b401d0714000c0409001c41d02c80750364090800400b800204050300000300c0c4c1000303580c59145095105e90320340300c08a0744050217600c95012a01140140002d042d01075220010044003030b62200b40e2030304140e050300152417808500400524031200104019482000940a170010050620003000401c40c0017034510002a04a01c0c4007241c282c080c0700840da0041102c048105a4003a403000003241c5213049501e6400c01046404000c20b840790f00010241e609001c600030b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 246335521 1250 246334271 246334307
    0xe06070f02121b0d140a08040f02060d090c060c081207022a0415121b050409150c09030f0807061b0c050f03090d080d0e01020408030c1c0f03020a 64
    0x41e107000e40f4043c10a103a41800d00a45009042015422070b200c1c8407030201a0002520f80352405000310011102000b000b4402e6565082c0010310f03c0059981800500340f0164400000c9596442401c11030041d20442e40034405102c840b1055400007640c6205807003056403504159207036650b81010a0342040380694141c5289902c8007400043e9800d26242c0b007035000300560b0308009000002040c0c00d003a9880340592f26100108140c00000100b0500c40000e003940741040700024680e8602c082000c1c0c1c1e14503281191140c0c40950250aa21101c0c421008212518034200e07100c50324644990303025045850000c1c0583c1c1000500301d0031300070141c1080c1d00200424401501c11b4401400c024040d000107242140c01340144150704800310000000d03039040110042c04010681c51030b0f0384000f459401000141c1d2415200c0002100c00b40082c8040d100900184001d1956511140d1101b42011450a204041c0c0580d0b15085d502c0306502c80d404500c10115801d005030784d0090381c0030940b088e49c0b442c1e50070641 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 246336771 1250 246335521 246335527
    0x109030b270604030f02030f040e0601090302040c05180a03120c06020c07060807021911012102070c0512030708040306092102030a120209090714040308030a0506130e06070f0212 78
    0x11604000030031a103d1070003580c40101a02c0004030480c1c6038418020b110514076024003082c07100c1440056016003025050400b041681d6403540801c1c1070300e400000b0407001c1900460138002510880070b42d07008180c82203400fa40c04a05556424156400c070944d00810000454049002c12420ba41120442c9000e40c2c02c03581d46580d10306008010f018100e03640300060166105400403a514602020542c03540700d04d010554800b40b80044907d40c04c241d02d05140f002c4041d5440d00b07490220306c000d040080c0204c400400c010708000902240c419056451400740e4810415140801d4180c001d03102902d41c000740c0410f0300140c3e0f0400300d44010340f1000002e07902d6029213003440c2e401d400200601e00c0c4041d54407442030b42040d42c41c0a4049014441031150171030303891800106c03454803c030501000388250706d01150401d910303901e41349500d40040781d10111040e507a0003807080c189000101d0312640020030f00240201801904203a84614015000700e003482100c480d0303511018000e20000f20765440d200000da80b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 246338021 1250 246336771 246336841
    0x60105070615090f0207031e2f010e030a021f06031b05010f030605150a110f060709171b030102040909030203270a2922080304050109030b 61
    0x6000c0345110f00320b842e5151000c0000b00c0703d00b0b8001d8844003a05610f42c5042452825240c0119201d01a14101040851600d500a01000380c800740c404191001065940c030106c0152203013140d22049140c001c0d80d00502181c07501503400200c0261014496101e07245030a000001c20300500101c2d000240b908a4824000640c0138210380399408a60b0240d0343d00c100110a203209804070780c2130740106900440303010748032046245c1c0c0c00000c00604059207081c00e5902c0f800b214550800c140040390b1005500000705100c4100c0d407004401d000390010b8201c448801d03541c200303400d40e101c055005d401450350b0108040c2506940030741c180d0b40105520f450034030071a6007519000352290300404c0d8009003401c0c441106a2821119150011198030140c0350b010b400d401c02d04d92815180d00008000101c0e281104108681b140e4840a8900b04a5107001c020041c0c06200741100c10011541201805e64003d101c10021a0390000030082180c2c0c1252598070b940c2c031110b29041e000700d850200c4400242d208080d0003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 246339271 1250 246338021 246338051
    0x16030b0d06020904060e10050f030c090405070e090607050d0b0406080303011401080f0c09061621020d0e0a050d080c06010f05151c0b1c0605011a0403020d0b0601050706 74
    0x802e02c0c1ca02200c0401403241c41c0c6c5004580c070001078814445080c007845050003a820303c0140c0010500d401012600e0317010000c4009216004125800ca6040d002040200640e00345005180d8201030b80d03102500182c41c14800080c254054030460000c0c0c1a16800c40c5c02c401e403580d520510141c081e41c1d055030307543d6855102c2c040880310300f800c583d4001240c4c04000381926481201290290040a444d0362910803800f0410045800c0058610320b068074900004001540c614840c460f2107080500c1811040c11821020b402c001c0d00c03910b41e4003885091080f0415980d54800c058040d43e4040303514003a29030307040c2441002800341040c500c0e0b0502c645030000c0380758075202d14040c0884e00121415501e42c6d5640001e05007a01400d2180712810b4080400f00360030700c1441e0480e2100d00c00140c400500d944010226440f8149082000e48016580304014080e0303000844010b551808078140d0039103000c0c03555001ca81601c3c01d0b00340c003800c0a054079010480076032260048034101c4e504002c0501c94194054010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 246340521 1250 246339271 246339277
    0x30703081309060510051c02030901051501020303041a100803030109090507050109060509130905030a0804020406050a06021009061103040507060e0d020f040b010908031b010e0705060316030b0d0602 87
    0xc0c01e000041410010310038041e03024070026100040c0004440e41421001694950000c04041030301104080d0840210f86061015520a9445c0400403500307041084680364840800d04180c3d046410030020080450609080c1d07140b124494044180155600800103d03401e60365000328645d404008000142c01000d600202040749c090b009481d030040d920f6005445103056840ba0402245061248482034640380310140301c00c05400c02c000c50000c59607a0390508580c171030035140000c1000c410510040d410944a030030098a429903007088943d08248000c2c3d62611a8a02509030a44640c2000d042103107075041101d05501502d03031251a8202450b07c1500c030160b074004e20300000d0b0851200d04083c980049010380b060780147c0a10349c00790140060201809100380315074140a21911b0000c2d403200100000e1282504541207007810170143d07100f41d425100321101200386940030aa00740130341d680e08401c0b01d41020000c0e20b01e0789140928074059020704107c0c50010f6100d4201144007003801206d03002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 246341771 1250 246340521 246340537
    0x41d0c0c010c081806040c06030c1809050a060b03191107020d050d021506060a110c130b0306090d050901080a0603080a081909080d020c0106050a0b0729070c030e03070308 75
    0x21395845820304002c5507901d50488000e4031412400ea0208210f9010780c0c410380b030102d0f042ca802150b01040311030804c0045e88550280c004a99940200040c4899034410078014200c2e80000d03500d103051207182c2c114101c0f01c00301440c06050307031803040c00c014640076421076102d154050207503202c100380c1e0300304a5100e201043e8000b02502840d208040c4e003080e02000f152103088000d00180c10150950740480d520000301c25600c03080d00c40c070b4007000d55590340c011040d12540048400854110104824035081141c0504100c0c82030380882400c0760300541000c140da02960003860300c40195075501c1144400742c8801d40c405080c048002403c02c04942c2d01c00020f0340320b0310003441c0d01401e07032028489000c22103010107000f81070b1203014001d0036510701c3c080e00100b60360703440c031000840c0c03181c0c80e03000180114039181e0010034629000943c10701001092043c401b442010308504c1da031709020075842c1881080d0010b14103010080d2907004441014040c4150951038200176040390302d06070b120315101e0102d610402c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 246343021 1250 246341771 246341791
    0x501050a1806020f190201170a090605191802030606190b04080a230706030c0315080a0201030b01050a0801030602031e0406060303090f030507091116030203120705041d0c0c010c08 79
    0x1600e0661410312580f010b4826038182d60780d923115445107180c0d0000305009480c101695854641400110b1a01e00030301d8002c03a4602081618080103221b42d50848a80340001041070300409203040160b68081038440e80301000b0f4842c07115024005180b01e90801c841e13000b520004001190104041500041c07030b82e0143c0c4500c0f050040e10040c813a00c110580d4403c90312036000d0b07000301414410301e031113600003001c008154100410b507619280f1b40c1c8501d40003550403081866025543d05425903900d070103680c0400d01c01303003006441c2c804003040c01804244140005413140c1d030000046051054506464194907000c0c2c2801851414145023010280545203c240d002031007844011940c02900780d250f80c111303948040103044031850000444083c080790707040d00c05251000c0c40301742030080881d0b00e100482d0b072195010715a50019100402d11019000d042001000400e10040c0300c044400b0301c2c3c81c042034206400c0f1a0300f075922184d040550303100302031009099508050403082c0d0303140c000711402d0081503615 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 246344271 1250 246343021 246343033
    0x1c0c05101704080304201e061303030e040f1b0c051006030305190203310b040b0408070803070c090509160b04050406080d0203031803120f06040c020708070501050a1806020f 76
    0x140e0003c603c2400d04a050341c48280210843c030300d40301e10394172081c0601f0b015103081d00b05140b03034811981d00c158684c0154046590751180c80c1da607140c603205004000340d0701c600030424200313030880705140a4605640001408010807940381880300410500994039410f00c414021241c603403900402c140c001e0508203121500242c5001c1102d400481aa40d942c0101c5030342d05400507c0302c83d40300b545828880b1003500814003280100310400118014806071004009041da01c5207028410751800f18560300c885600d400c01e00c85880068803d140c040d084503500030001c07a45459540d01c00d1306050f80230580c80180004001c1c00915407000e030001d04212081250100011a40c504149031561000040d00c00140c00400c0084c04613102800d14502c5c9005450860b41040c0490403040341400c425951000d07403642c0042081120b24190107508041c200510103421040c0c1f41c40501e6554403401c4c083c07541400800700712160158030074003024410580302d91a01c4020340e601c1ca0040e4a5500c8240d080340c060240d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 246345521 1250 246344271 246344303
    0x3020d06021909080f0708060a02070206070807080703180f030201051b0109140c03060c03011517040507051e0109030809060706020415030501290306010507050a030e1c0c05101704080304 82
    0x4611a81211f0395807003c5d0885c0d81d98062080300a52140d5001c03139106106100705000b08200d4805070400901c01c5100541d40c00490401422041103014001c0c1e001521030020b010701d034500303030b000e800f100c2d82820142d89482452000705034500c00c1c444101c8044d0f01c0d21a0359000d04c6042d07000c00202883c40002c2c3c0741140103020502d40c0303070b040c00c45041c030a0800800040040b0450210f0b054440510303890203041040b0102d0b441c86010380252400d9440741e00000040c030083c50000c01c034290034100400e40c8540d05000c0340020f0143c82c0f0134440900b80310408201c201c4c2d01c1e25071a044407a1168040d800719501e03602c881c94500501da1640c104000a0f2034400041075206510744030400c1c0004240944845a83c89040f130803481d0700003008035040250a0003a00c0004008100704049548251500c3d0f900032980c00502c50200e404884007441d0340c0c01003070440c000c00c2d00d1000c10002e403101590030700c0300c0420b0840c040d10075446240050451000200400c01840900c00282d40100d1003007003080d100102d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 246346771 1250 246345521 246345523
    0x70209131b050102030f0d090b19050c0405010c061a030a0f060b03010b0d0807240902100f0522080a050615030c091611030a03020d051f03020d06021909080f 69
    0x41c034041d180c0580c4c4104044854016a00050015040751000105070b5031180c0e551401c8000b81070390b0080041500d844400428249800348561114009207420306051412000a01d00c1d030074020042d19540c0d56081102a500d022000b5102111001c1c08980c554030051406001d000380350041510b901d49003000d50086894103009020400e20300a010f03506120071510303840c1f5550300103c0111984030208070443c06d5200e10580940712101c0d0081c2c0010480c4880c01880382d03400d02c20304c04000b0800c0c021b5451034100d80080640710000c00000710341d04400102106140d00d1a4030b504206141e02c00c041c082c800301702c1c000802d079209090680c16900148110301c08d143e650140000c0300780d844030018000804d12043e001d650240303288685840c0c5500610451135605540c443c80940300040c3d00001c0b8811102c945002e0a504801f04003a00b0218a584010480340c00764607000081c03041d0140c403100d005000b5143c050340e10203444a040d800600c1c280306805000d200c6188035420300c0f405500c00c00d03840408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 246348021 1250 246346771 246346823
    0x1e09092821050301030b1509130605060a06081909050604060506150301121203092001030b01090b0304120519080105100f080c03092104030209220b0c07020913 70
    0x682d1120b5003140d00b16038484001d0140100140152a9820040c07102661b460130054082c000c690a1148002c280741040400d0b90310050009000f004007002c10000254851025036002400c0ca0250910070201d101900107485000c07005801e51041e001807005102030750f80254002c010444d0b2807820388409840140e0640002d128060b81c00d040c003c0900045420001440001e0450746000294511507541e00703030030304007408107911020651140d0703010f642d40c1510035507000003003d003007065072285080c1516000e4400240010103120b882c1038000846130050055032030f20b198589030700c1c0d0141007210004103120b900748201d030303c01c404000101e0300b01402000003203e003042c0f980d1803c60740c0c0c1d00d103181039115500281c4084120320401c0d01c02d18030102540840c818090341c070ba8050303030395074503500400c01c003044040c0c00c11040d5664801006440c6480d59030b4030414507400390156030305548510001c03655000354000a03403c8140b038410014801e0070324044641d070b2407103641c116050301c2c5825400c0fa2404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 246349271 1250 246348021 246348083
    0x106080f031603030b03031605010501050d210c08030a0203060108010b030633070b060906042702010c02040e01020c0d1d010509040f06170c1e090928 66
    0xd04100300c9450001d080040000b041e9000f814040b80c0340900801080c03550f8008010481440505050002004000c0c01101c0c0180421541c0c210080082c0d11402c041001000304941e07440e03020300701d41c0c0c031060080984280395a00034400648a191101c0709034083c0d801100d80e540000d145400103c0e41e8042202528010381c00682030076403501c901200d80920859060b060500c4640c200740707410810700308100900145204043d50041070510b0707400d02842110250010340b0840c20240d180c280c412417070140e41003504049801c85644009800140c40e0101c41c108040d40150425070403203090481500107140407540001107861055030a002150880c450441111280e465442005002d42c802c001030300d075a49000b480010489144200d190844000d940100291030085240d01c0b175420f000e100108003280d050f501d050f11010b00c038000055201c99000070b0b51044480b000841e403840c001b001610005425a040d034842036030081c054045108072000200d030585204419010072054014042d9201 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 246350521 1250 246349271 246349273
    0x51c0c0320010b06031303031409030f0a03091b03051006050913060e01051302090705070b0a0c0203223308090a0f15050f070f050903070e0f01080106080f 68
    0x1002900000d0075910000541041c1d00d592958030081ea1992000e00450062210202c0c10180e82d495107405010f940c80c10ba071740c00d4019065000c00c110402c0105c11a03181034140c101440c4d1755846200c05a0061000100c05000000b80382c00304030441c1c0c9007a1124003a00d002d4001c0f034110728a046440c10036a4624000c054020806c58041001200c400d51401c00040c80b07032001150345141a101e59085940407034500f030700306020030140c009500b414000c49400ca211840c04a18040407070301c1d4881000f101a024644c2a82c0d144050b0060314428400e46070442070480b41c84512210f1f4000814000d000c0d030040c0304d20034130382e0b0002c0c031941828964032612070010498001d8042e02c1101c02642d116200070b080d42e1040c05036122072000204030540620019109903992401503611007541421a44014000b2000307d4010081c0013459800a050381150b9000c0d02c0d00319a583c42600100341840815440781c1c1c46c64100005000e41201441c01300340c181c410b03a5000b00000c070ba032000702e41d03590a2106000901 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 246351771 1250 246350521 246350537
    0x702010906052d04030210020a08030f04020a031401060923040602070f020d0506010e070804050c09040201021f020304060b04090201050414040b060301080604020f0108070f0309050106050607051c0c03 88
    0x305015002a0003154a0492089851410a403940000c6000b403c18a00c003a0341c00035040c400c41ca0188400c6550b00c8179840200300b9182140e42c3d0700e0b41131101610444041300392500003800c40d620042c402014581c045082100c0d4800c0765209406440a0b000f508149400c00d802e0309080ca855002d5100f000c5543d100099040c1c5440d15050003d501090b819209104034441c00c402503120301a402c00e4040c8954010103856150a480400c1c11a014001000700982c00c010b20020580004024421030001c031001880c4e42c80e40d10050b0b20700b4120fa050748500f580c403507080c4007010b00d4545c0a907104a001384028403035502d44004020407104030074402404904248018402a50080061456450701070000100220102c0015076903400c2640810095403103401008114140307801100c503d0030003801c040820b0b0400e810058203058400305c09004142c0c5d41d5081000703111003500044e009000160038541d0312406410183e4588100551142102e07e5809044000c00c2c400c82c4054460798040d950000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 246353021 1250 246351771 246351779
    0x501020c0d06020f070501110304060f05060a0531090b060604150804061806020901030b0301060f0501053004170c060c09060c1b040b03060114120a08040e0f060607020109 75
    0x100079000408134024102c014000329000032401d20600c2c00f80640e0030412622444c10f0301c0e00d9000d8650404003500240e0030300c0284811a1907400386101070301c0d4102c49105e6802d00d040d00810400c0140c445035044031031211010f160306c0900754021041c4a02403101c03500d00340d68190610403d4401d600c6100201c500c84080155107034414800e4030b401500c50040410310403040e0350b03802c803101400b400589070340e80e0008540e20650f80610030046506401e900900c4002d1405e061081d0711209886001d0601000050302d2a5802203000d00288500500c001004011075100a00c02c1000003140c04450707500348840c0f41540d51240b402138600700d4000e20018051541e0f8050a18403940002c050203030480e4043c000320311000803c2c40480c8210f81e8103030822101c04001c0080000f940d00207404240207412140040c810f004041c40a1003840300243c48140c0ca8800c801c42031403411a094030041d200c4234000c00d01090a4403140d407001c0c002d0702e6174a45d0b1803143d00c44004103d600e106810009000c00c1240700100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 246354271 1250 246353021 246353033
    0xc0d0c050903280b0c0d05010504090f02130207080f0304020103111303080d020705030a030c0e0d02010c06050c121510030b0612040302070503030a030e07090c08041104180f020103060501020c0d 85
    0x14000c91000e034010b007000c01c0655914090004c095602020002020441c048110b5203489100d00404044a0500c1541c0303560719002901d034400507019000d10b00302211003081100359011107082580c850022640c41040b400a040947c105071412800282054034250205111009540c01c11502060000c2c040e891740d5144601944107028001406809112207404180244043d1009e0050fa84001c540b68818240081c5840035491544e4820440540c800c40940d070b2142c103c0d84113560100b00003585441d92040008a8002c41201c80b200ca070390003042205405200c41401c0380d1050a46440c03000004080040c0c040d9081c5502e80e0fa04600107020314100502d8803061650800d010340180d400c40c0d42c9890100b401e55008140306000300e0f03110010410309240410402e802030034402d004110640c1c442d42c005100310310141015044040c140000e610310f45d1190300c00c0d0301c04880c1e110f152003800c0e21860401c440b80c503912410b03400b280c40e1510014003540046200500c00000800141900c9815902c0c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 246355521 1250 246354271 246354313
    0x2040503032d04060206070216060f080a1d0312060d080909070c02042f040f0510020f06040308090609071412010b090f0906070e030309090c0d050c0d0c050903 70
    0x41030350b05a0841500590100d80b80144090b10155010705034501d0048000b914250341c0b484034001100e586c4100f00700240c1d210f4160443c0d810603107804621515181880800340803140202419000750400c0410340f40d07000401000c1007030750390a03010398070360300d081c00c04c41c00309030440000c0c02d901c0e010007800d0101d2401848007580004641400343c400300c0f49801240441d000800c0c103600980c61543d1907110109080e41488802200c40070301c900d064240405201149517a1298500480b1881c642d070362018000e000a1860818050880f9454901414000c1030b00505030369503c018040d107808944d92040105491007600c0140200582003444401486600c01038000c0000a81d5650b80c00340c40c107a5688001540507900ca04003501303180c1802c0400c58144400901100144018040740040da82c4000c0183d031a00d00c8112803400300f03552901d048101174850313000c820016031b02c0c000402110042d0131000d81410368102000700540004420203650303038410309104c1a4140c0c8040d2803480b551300c4883c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 246356771 1250 246355521 246355567
    0x7080601030e070806060114070c05100504181a0613050f0a0b070f1a04050c01201c020c04140609060103090503070b011505040e2e03150f0204050303 66
    0x4001442d0012401d96030910000713410075a12508080280001980e0080030f1840f04111940007a01e0140542d451007510700980c0b0415004140d80d458414001d801041500c0060040400c8152200c46a100440040c803003500ba0300032000d448519007c0f1810040c0c2900d10800d00559200700450510040000346200b0b503d195511a12800340403c55007400005400250f214805941c0200c0c0d00d8600b8030f9104034081d0407400a2411300c02000003090b0000b03803071a1b05140a00b0044092840d10705403242600460305249940c0c13298826000306d04900d00852a00d55040b0350a46128031540001c12081c2d41a100c034211208110b40003283c81c80c80d00d00007241c0c11003014100040c100728075955070b604580000d0000d0310b48490b000010407592041244101c1855014030342945040d042540003025000042e018030180c6003c403a0340d00c0040c14694021050403000075540042c50b075689006403a0700080c001c0960100c1c103040b070180c05032043d8000d507010382d1001005141451000000802103a00c40c0380 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 246358021 1250 246356771 246356777
    0xd060608030423030a1703100906030809040614010c080c070e131101021f020717031006030e0705010f0c0804051306081905071211040507030b030f07080607080601 72
    0x5000400000c20801440140318000d0b0b182e404a030000b540a5404940d100c400d8003039000302e05500002840000401c0e0030035110198a520b07919800b03956000540c189c0c02040c0090320b0054040280072000006d400008000c450901155443d00141091098007480341c5001c145494030340ba00143d500d002402100c1602e0342252003540c1e941c050f110b401d003020340b2030301c8800340c01c03061490601c0321404040d0400c51081c00102070010a90411000070100b1500b41d602065001c100c15081100303440610507128048042c81b80c481c10007503410041c40545200341008613180c0940c1d0b038510071011078044201c0c1c50584030303120b00d00551074003034801280e101e10859100303c0402c404140c07566081e451058009010000190f0700f030130151b41c58a091044811242d2140a8002a01c00143c0028501040d2140a4a0744843e1241841d112400b032030b210a030180d01c1824201004041581580404c0e00220110119006414040009500c072111802803000c107400100004541c14003d803404c581100c4189 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 246359271 1250 246358021 246358031
    0x40914061e1c0b07030203040510021204151404060f06060207032a080a0501090209090a0f11030304080a05160f03050303011e0b130603110c1e1507020a02011404140d06 74
    0x95038920b2450340813112100480e40c040300740814083d0401c0f140024004c807040842c584000400e404083e18070040005140c0b050600c152151071005801030200021018094112404d0910740000a0420707084c0040c5c45524003080010b086100160000c02ca98100c40303103240c0b101c1e0003020084041140b8070f440c9440d20b000c030000a5440c0d000c0107040d101c14001c80000403030654034810050400f4000d80055044d512004054000c1140501010049544044002c0c60203501e20042401c5010300c0d4800119401480540d2003400004130300c1200c0a11288013410000d5107890804104106900002e446c0c0e0384140014010a080001078001050040c42c2b0350007010b40d00d05090f142030303010142e800b8440486000402c103d039011300841d00c500c04403e2145061010420045c0e030740740310740d0385229110807800d050203801c0c0b50144014555143e5400994005140101e0040e50301c00da00c1c0c10403800900d005084010040201d002d480503035580c008c5540c8902800c004011001d107222000340c5543d9614 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 246360521 1250 246359271 246359273
    0xf14040b030d020c04050705030c03130507231302030408070326070f12110706200415090518040f03021c03060504200304031404050402040914061e1c 66
    0x2c2100004080903540140320300180d403403c1c041640c00241c20381060000a000744400010110306896021184a0b5054020f000d01d0070951325081c0035510045001644980003503209020303800c0b40780d81c80b8084e50607400a81004050408034442200c0243c0100401e01441c00080e10580e2080e40852140c5241041c80ea180b240350501d519090351580013203010640c154010540280700400d031811084400c01013540c000082c0c15503071060040c01020305998112051043c1c4134082030800c3d0040c42e0701d42c55251500c0380884c0e5581403500c04060080f9503e0100003401e443d1a000903021045411000b40740764a0302d0707031460400c44c4000400c5096024800c0d111480c4440c092030f200007aa81a50045000d9140c0b60034842120680d0110784000c0d84180c0648150724071403011260010b5151500c1e00711041e84441010300360003603030452039005000203070000b07d1072020b070856490b41501240c050300e5600e03842c3c20007560f1280940380f04a1b48880314a14034441c903103a40c80f09244102821402c0984820b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 246361771 1250 246360521 246360523
    0x40f0212010e01020d05070219150f020d0213050a0f0303051b030702101206080a050a03110f011a0109060804020306010911072901081b090402060405040203091e0102040f14040b03 79
    0x1000d90282d0016550f4030400030448d90402622400e40b0a0b04050310003002c1c0c98480744044000c40c280285000c3c0c603804100d81c00b01c041c0d41100d81c6016100011500d500034942d82c00000b04041c4246403250304906800314032908940060012a075154590f82e1a089400d40400c0d0003054030100d00c3c034940828411000588c030784503400711517049690303501501880c105000c0300c12100706400c01c4070540d1044c2120342c00290001180c04e141c40d054100840440400b040e000d290410441da262029403c3c07901503d4400030082c007100c0c00390703000d8031901035080d01e07214215107013042110b0282d4182c0c400c1c030040142c2071f803942c00405941900f80c40a03140c107603242c5500c1a03050200500d0854103607100d80041605200400140c0500b051170054030b04112a001a103524246146105200340960404502195609411540181400740040d9102e2420042580d1100d4119a2450046800040100800206208480c180d4002040920740d05003130a030751074185010390404030780095031008121240d86d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 246363021 1250 246361771 246361777
    0x220303020403050d030b13090f080c0f0f06070e01030908091207090e03450a0e0711070603060503031c060504050c0301090c082401021608030a1106040f0212010e0102 73
    0x4c01520049034901a040611074140b83d030b9030b405200c852a140000c4005101102403444498018040c1d0f0341380c11500c008542865a8041c01c4030041c4505061404c125002094240c8200d034a0349800c0030701c4045400540c10717120207520050015500b00a08002c600d000026688074248110854070b50a0302d4400c40e808a50300c0c0c40443d0020f81c80803900381000300c0c202c2003903c405c2114450ba0100c2d15620810103000e4040d95a0319025201808241480d80d2212002c4800802c400c0042e402e031800c0c0b048001e000b026010b1a020258003030f004000c614680240a00340c21904058019450a029001d0302d10940610750381e0310b82c0351500c1e42e000080d150399030f00905014401c0c465850355039500d0f1284890880703611914060034000035100300030046040800900c00041d164546001c20503c01e00100d0415844200680d0180b0414801055440002002d420fa00d81252203880c0200088120306696400840d0005d1100c526440c1d56401420611038600c182e22905001007030070300c290000c103030aa070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 246364271 1250 246363021 246363043
    0x905090a11030102120c03130f0606080c1207090c050705071509120b011205010b100e0a090603050c0607210329030c06181c1a22030302040305 63
    0x98002a034030000d20105807503a4001000840c000c40c03a0410b801016002024010014181900c010000402200c11440c6078001194800c0104c84400c20900d400d0001b230140e030144520328412015901c0c03131410200744490314207004100402c3d0b0b003403601d18402c026294503202c5004001041c0001e5000903800c000502c00761015400e00240003441070030041c59008994080c11141c410040c0c0740020030700c49074a00303054419408030440482190308040b40500760400340c80750010803081042000c2588480c15110400f411602e09001981d02d070781c103a00313032042800003038520f801140d0181100e1610500414005101d010030400000711411102e01c022a20082d1030082619200100100c280840003c11001c0c0c00c07600031251500c0f09400f01e550350f000b160001c0d0040360001845d00e2081c030b15070701d125109a0020310110090401941d80c0b2030054a03524111364103110600c044541510203000c01e480341e2141c032084031300600c0200d004407094201c81c0003603051550030000400484c0043c05240c09403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 246365521 1250 246364271 246364273
    0x60301090e0d08040f030c030c080304050f070b090a09091a04110103060b19031a0a290702030a26040b190e0102101505031e0606150304020d03020106090509 69
    0x10341494000364200a03441059074200f1042e101040300040880804e50011501490301d01c0e681c03130081c0342c160358001e90018090b142036004010001008000144066241c0c0d00c0800e40b5501a610742c021001806103139400b42d44044000400e000402c1d840d8001004140142803e002032110f82d4030040d1701e03500c2070700c050315440201075030001c0c65601400307034800400301c4c0c2c80c0c414a80001450146080c0048000c09000c050312517400e4280c6050b0b25441d40000c440043c1844019903131040301854403050b0400403044035900d00c500b424500000c4c015200e0058020b405021080190798511030311400b92a10721030001080c0000c03000c180e5020001d40043d0205d10050f659a20540715044942420502c00348100006180c5419480c0d0780420603a8a030b4121030004915a2820703440c200d4100703400e07007049400d440703052401802010400700c078248481340c140075105661504002c2c406054480103c0b02000802000070034014141300b034611040e50300a1000161071134036240150242e0341d044c0c07041449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 246366771 1250 246365521 246365531
    0x71d0a110316020111030105010f030203090c0301020415081e040803041506120213060602030906070f020d0c0509150109030305030a090506010605040503100e0c0f011209081315020c040f0b06030109 87
    0x2c05409104003138540c94008030940c21507240800082100031101c0000c010540c010022903508801009003c0300258014000c1d900c40b1707141c1c80c0400c4102404013954000400180202d2001800130004890312000f04111024907070703803515480419440070708115443c1c0c00d80f03095050100450700c82c41000d800d05043c20301c4004000e004204400c0351b4201d0340c0b022a85004010480a0f030000308882c4122001e684240d22030740d460511003100c50b0303e00800b035004034098484504002510794034400343d81e82100e0159503500d416000d02500c0a4110195010a064078401d1000c41e0241001e0759002034100c80124081da965038442d402d01c1804c2c2c0c0420701168001c242032100345004e11610b40d0302c14504908003d024100d000300d41d5202642160940161903500c851400c40e44915226044100740b0b040c02d102c440358924240344d482e8841364180035113000c00301c004610356003c8189141e051003954014010700e000f000420008101e03d06140040b40c1c2d484a0601c1d4544514020354000c121403640021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 246368021 1250 246366771 246366811
    0x170c010603110306070921020301090b010e090a0c090504080c0d120b0315011e0f0f0312030504030804020108090c100512090f0307031101060b0408100e071d0a1103 72
    0x30521107452034884d400044c03c0200c01580030810604817500c3c1c242000f00c000031610a00031140003440c000e501035007011000700911403000c03110750489201854a6150f5581c080701c450f104c0c1000038005000402008040140c0d18440c1c129503007241c05101590300e82910b40b01105e00d8028819200400b042d280c0c0161080070b891842100502e51042d00640421007507401142d0103e001401548143c1c2803402070601c0b0303141e2041d0710768064108031143c0805142c4400384d168a9181620007100c503a10040c030106149482070241034080c543c981c4941000e500c503a4010f4842140c014000030140c803038200c503026507030354008090051101c43d480d0707c3d40d100411b11900312000030050040c04158840002140703000c41c00011036402c15050b01d05034014168021070030340540744542c400d4590030b801040c04502d4841c00701707440f040050b0410040012a4440916a4039070040c0c1c410001c2d0400400142c506a05600313240c0341e8016503000b00000c4c0301640300100f0340c454005030f40229410601314200d007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 246369271 1250 246368021 246368033
    0x60503070e040e160b0f070f060e010c170c070b060120060118050a020a0203160303020409050115020d020c01121104030c1d090714041d1203160c0c05010309170c010603 74
    0x5806400310341411460300b071b100300700c6070b035503110b51303040201101c0341802c0c054140b1078140c0c4000042d404082c0280850302002c00000d0801c00c2100100700c0c8075003180b011482c5001e008040741c510a51103241d0075680d90740c2000550305451011403c5080d210f9011607100039203801c1c88518041c02840c3c1c1d805040038206080402120b00080410648034410040809040d40001c10350b03038081444114414040c002d8941180a805150b00140d2181c0c245400400c0f19030055444841c00c0ca40c2d0b900300c031280000e40000f00c0e99407840c20000d90103ea004c10305801042ca150700010792103201c141c030142c038083d920781da240300b07a850f00e40c44183e040a002454407180a40e64026079042480800100200750034040f150420161100600c0d2250b40e80340d801041540510021400c0101030f0f0041d5221b8259480d189002540111441e170300200843e9010808103014450b01480c040d082602d2800c0755081000641c002c0c040302c04207403007500b1451000400e0121100050420b000d4100c0040390142c950302d004d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 246370521 1250 246369271 246369313
    0xc02191b0506070b0a0b15120612010b090f060a080f01020d14010b04050913060c08160201060b0405120c10050a0906090e06040518010c0302041403070807060503070e040e 75
    0x114842d4104201e40c00210743d00344003090304040072250006e82d8980c80c000044840503c4c05800070741c40408030301c0982c1d0705100c002083c860041603c1078806a1000b0510500301d44900c15419448034564000c220884400c040706640400003808001005844650701d61401e00580118000b6070f4000420081c4915280902542c008010310341106550418480110602a60040500540849000070030401000d04d018440301d80049081249079040c8000a10000d4101d90b030102124111303801c01102441440751a007124102c0d45200d00b8642000c04012240895152008092240342c96000300c41c0d540031240c01d51214030752501544e50080e80c10281141c01c03640d100105008280c1000c2104104040040f07170b0005c0c2c1254001a2a03480b4104602c50340d0185201c22040d40ca032039807030b8520380d03010741c0180140c0b00c40030180103403021098201959409a4080c41c1842d40007804201b00503030045010315040b20190800c002c13202805130100b400c886e01c507222601c495111040b00e2201c5d41c141d9a80b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 246371771 1250 246370521 246370529
    0x70c03150212070c0602091807030e2a040f05070207030c0e060603070c03020a060f1410080307030c030c0209070c11010f02030405060d09020d230109020f040c02191b 73
    0x30660402c40071801c2e0a002c140001d1515061194591411041104039412034902050080c43c0b0381148076500c003030080c4004116184404646000c00340e11155000280711040301c10f0764071041100c1350121030404040e5201680d003e400903241c4408031882025800b078240304d58841e138003c08100b441e40c140203a40701102d500040407100d90006011140d1501c20032a80e01411508200b105a40d0625080745001d00c01078010b001585400418544914a6004040440007034101c40c2c940c2d803602c0c41203404602e442d1161a07450f03481041400c001900807014000440d009040c000c1e15103040d074001c540ba81c10f00715460f0b0000340c0b041d4034003c2000300c5c070701d81d0142c90341c020300c0c0080ca43d0101c40400b956034401d03400785070310543d00407500c1c07800c607481d9400508185038040d00109540e2002c0c5408030000742c4401d0000d5040f6101c83c4c000b101100f0512440703000341d80041c1111024021003040c04000c180000620086004a1001c3d08150b076031504045200fa00c6440307201207298400a0a440018207600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 246373021 1250 246371771 246371813
    0x60e03071823130b0a0c0c1205070b0a050a0c03050f150607050a12080a0b03150a060f14090f040c05090601030b040203070f02070b0705060f25090501080a020735070c03 74
    0x6c0e030b007480198001460b1054651210f0914803150b90b40005403064010064000c114000c0341081082c1c80845401981c006ca54280c000d004450030b0b15015000d55604580445926202c03400248040909087c41c44a0542c064485864440c16480d0103081c0124070b10305482091143c034502c0d2406902c206001e5001d03c42003001c1140120f400c0020b030300c980e251168460740402341c030040f8034542869480380c802022121103d14191743d660f03001121fa48118407810f481080c0c0d4400140e1080c00001407140318540c480d0380d100a080c181410020340b0640642060f04056440d18003502a85503880150700982c1c45480c1c1021001e000c220080ca016003c1d00032041d03225041c4000310025800040d015040080743c0500d14080c0c0c0c0e4410368008038055001d00b2001c845814400c1c407051500305850806641080e030700d020349660fa14403500180e1081d018001c0116100f40024040d070305465030148254218100c0003200a80004034614450b0040308060b151100d90000810401c05052060b100c090403241d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 246374271 1250 246373021 246373031
    0xc09050604051008090f01140f010b0301060816050720090a0b210f1c030c030203070f0309020d06060b0a0806030109050d080415090804060e03071823130b0a 69
    0x800801c00710310f2404022403d0000e400040b8101c442e0a2004103501100100204a0300c03446446040301d4030015a150612500c0032400410701c10340c0c420071079050340c1c16034550082c00d4580d50010701d081030810440c801044014400d03040003400c0f1958a60f0210303403410350300700400194402c118110783d001d40b007a9512480e002048241e503e804140914103510480349023a030916806507503082000c00750500003680030301c401001100400c1c00a07902c1d949955642001082c180c1d11064040f41b10903200c01d0007040c2c14002400c0000d202e0340241c2416880a09008000103032551958142c803440e4209140c800c001191561413035134042003481d8443c4084000703010103030140e110f1584a070b000c00340d42e0f800c02c071800c000607007445241d030390b0014030102d11346007000f00d58604d003011003c54116003d0100000c600602c0d80c4410320f00020044140c40350780344c0400c083c091100403107004080f40d020203840b82000c0f0555181064004009602c680042c03484001d900c2c80c40d283c03070f02520b20300030710300100c0524007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 246375521 1250 246374271 246374279
    0xc0207031205070203100e0303070f02061b071515080c06130e0c040b1c06050d171e04080a03030506120607034101080307080f0306010309020d03030c09050604 70
    0x38209000740038106566200c910703001003420400c02e41c00d0101014200000c0001d02e00000000711f00c900d02d29560201c0003400c05100302c6e00e403601510803c90402c14031442e5507102e50074400420f0500c2c456450419404407c0d0307040c40540f04000461300705490b900b03604002c1c8000c20700001001480855040d8900a0504104411031202d405103003003a4500c4800a1141d441c64421500642000b620300b5841d10501d01e441c0181e011210060000c107070600d0400203141c10b1202030644155803181d0725030316002003041c4030041600030101c03040c01c0407008501120b407003510308001c01c080c266680c00f50000e40b01504000e41034400291140c0e02132020240a40058400802c0d0b00d0382242c4540f40c0421031b9800c080d00c0c40c06146540201483d080c070700701d00594040101111074507100d0a112941d104c40d031380c2c4012580c1c503809816409014081d08100400c2c9850b600c0006540c04101414002055041600440e51a07540c100c0100c000c25515001407903803c0c0c02059003801440102c411a2601d030034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 246376771 1250 246375521 246375533
    0xe0c010203030a0c170a060305100c170402010318030804050c100c03080703110c0f0d030c05180d0b04080d050108190209130b161e0206071101091205090102010c020703 74
    0x3803403110900e0307642583c0f11041d8403038800103684500f016007203170b018244140404014012444111034034030400800a03108440d50003424045070147d20741c506802c0b9600082c0b4803858006000b2410180d907442000180100520180c080038001d03980d4241901d010b2801903c0c0c520125070040c442c105400c4010301031944202114030300342e490316040110b51580d1308160054010308030502c070006400308169040795800a00d16031032041e0b500845884510502080e41100e002a5001d00081d2041102e0b60840030122071940d21110050304101840c0a1a242c00c450003406541c2264070601c0028114800100d274082c05002d4040d02000c1d0401c14807007041c01c00350425180000b030288100038001480c520464403214409504a0214455450003d441003441070729407074980c002ca00522411101d4150501c050004903280c0e400418107500d0f480340a89500304550350f4030815640707a12181002072621400000c3c95040c6450b415140c0031510006401c1d02c0310440788502310360102204202041d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 246378021 1250 246376771 246376777
    0x50303010501050c0325050c09060114090609040c03060509070503071e020309040603030e01021002130e04081b0a032c1504090603110916080403120609050907090e0c010203 76
    0x1c82420800d555030304142c5030074110301400d80c0051914000840c40004400c0c4800070b0080240b00300243c68248800750204000820203a40b12030001d0a100d05071030103054404c00401400d80300030074644c00c105e60140014140d9450440460000303454110401041c10700c10030711034024010381001800e42c17400560082c048101001d1a08c070b460844200e2303d146034000e00855030702c000c02402c180302c03d81e241e00b800b5000c0c01c440f84080d4018450780c07640342503200f0507200341c99980f002240d8440d100d9140c200071380d21800024000340c039080300400100301c1100d055482c05c0a407140ca20007a01000d07400e801e02034441c9100181c900c8440f46021582101d035926490b6a80102030200c80d040c071007242d010107201c0c5d035000311703002500594a0143c1c0401841400c0c0400422004100d4071420725680c0c92501c03200c9032820b80d4510001c519040c0104001901401118040e050140030000d43d903991401c80c402500d0b429145442d0030303081a00f0902075100d041c01948014100341c070040084140c8000001e56a02c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 246379271 1250 246378021 246378029
    0x309011206030209241c020d08090603091609021c41060a03030203030114011b03030203150a080a0f060939060c0b060414150102060a0905030301 64
    0xc0248180003414400d6070340240003843d00034100360002d1170240300e8005042c4044800003103004402800c95114688001081c0303d5009800b02e40214003d40e90911100040e942c01c00c68103004144920000358803541d02552140030894010803407440e000c4242c1e00705401076040800034a00400008000d410043d0b04030460071240342001540100b0114507801440d203103140d5084d64003080b03800c01d4070740c0c0c0b0509d4001c0d20900c400481c80c840b600c61004011110b8900c0c44001d016801c00d00c01000b04100c80442d6001511041c100030400d0301c0c4400601703501500c910011000300c1c1e8040107101e0f2202c419404000e0314207080e81c80c04005400c104074542d8400c40ea030802812031640040040c20010160081d490159110148440d005800050641c1c04840c18608861070240c803000c4d000542e6031419010110380301e030749030b036805500b49881d2800748000c01403a158106446a4200b481d1180e1414101d00c00c0030318a140340c0105030308800090401c007001d00300b201440d040081c3c4002040c00030007102c1c111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 246380521 1250 246379271 246379277
    0x3012f2b060306050a090314090a030b07020f010609020c0c0103051005210f010605190605041a09090108030301051305061008040c440a02130e01060b0c0f0f030901 72
    0x30552500440c0094000d035040106103600b86020720000c0049500440c0e04144240c0342c00e1043c00351451180303003d01508070303000d52042001d0010004540c21302501a00400244140e41a0200c5428200e095079a968080c2028a60004071055640d0051200d800501401d00c0c0070b000d28109a00d0700c64203242c6034000c00b0f00c203600100b40c2c200d80e280000d4060a000308142c043e00c508403180300c40c440c002c002500c034a034065201112408103211071601084152003c5071502410242003084410403400b42d968200700c4014100301000080c1e84865000d80200829801107035203606000c01d1100921950390206081401c1405008459880502d1814550704030300c9c140c03819540b81d00305242c1e01d00c01030b80040d07030b2080d520300309140003204014209208500355420a003a5010050949035845140c0f412480c80e4108070500c000524060140808942c0c0c0c07181c0101d44c00705464001421102c3c49e9000d003a095000003055a4150424001c4003410425900586202c0882d000502d440780b244000f65410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 246381771 1250 246380521 246380587
    0x3080403021c0909060509191a0a0806010906060f17041406040b0105040605061303080f0f03010b04140a03050c0f010203210613020715020906070c180608010e10110903012f 76
    0x1d0925601c00183c01510014440000a2f954001580d02d4105c02c1c0038039403d990900d80b010940030700940201c6170000c8550340e03c14105e451409001c9503644090400c89441b442d01201c00421541004464000d82c001c00c1320f9002945024100811074265510440c040c410912481000d0b07042d0f980b8a808894000d0341a0b507881c41c43c1c0d05050000d200b0405242d401910200011035100003204c0a4001c3d202022104292800303035500b0444012220b02c00240f0660041c0300021860a010190004500701801141c1c1410890290190000d64601100c000e482d480310400615291a000341e04043d401c6074011460b10090703032a1600d04201d03007200c4c80d602540016603110581c07a50300c1201c59071900301d440703e06850b440e4090820f130904526080c0a00504145010403801018801c0d02d164548110007014846014803083c0040c0000707641055610b8814010241552800c3c042c101c03111004162200c0e098001c8034400d000210320420541504109010420490758402d03074120301e240e205491105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 246383021 1250 246381771 246381791
    0x10b03160b090d02060418141918062d060b090d051f24050102030301090902030c03010c2001020301060918090609150c0c0f03080403021c090906050919 67
    0x6180000c44000307401c1440000d000640d41201980a00d072440020804c0c044100c0128040040d203070150303414140c0312782c00c03080d0301a81c1403503a00050b556010040345909401003a216134085524060036402c8022403c0f03080e83c11544414505540d400c80d0200400c407050a1182c0d508090248241c240d01615107646a01c09010741002003090105c8030721703080651074150181400141040894003001d01d0421224840300c7c980100340202500c8040c2c0c011402d5a20b84145c14020300b0302d0a0003641c05004118410300251801c1c01070300d44d048800d80b20144403500d40024107160120040c841c8400d41d01c10300042c06041e91000c01031044031421036075608034051586c071800c01810a02d4008003411315001040c420401d400804030044c420100d41044440d1410206540300c50a046c0014040c8048000000000780511440d580103400380c07040361044004004c107555001e4084007940302080c040d145c1000300c032034540100405040255507020305820f000300c141d081121a580040b0716242c0782c125440b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 246384271 1250 246383021 246383029
    0x61a0403030f0c0b0108030a110a0f03080a090204020f090f0607111311030709050a05010f020a0b040c151706040902061c0e070620062503110d0b0102010b03160b09 72
    0x344829400294801e443d51b52081c42c9683c9621081c211404511803d0205280a101040e03e103d190b40048141411900d1a6400c6030b00c4000103100a1600303039120140741c0035851303e2015241d0f0302950303504135540369512820440e40e5040c1491031407003264100710950026800b520746421001d01a640540351b0715044d942030014106a0ba14800b1407203020041080e425449030000045500076142e8482c0f2548500045404144086c404c0000d68841c2020400280d40b5084041e44103000d1108086000e484d401d1010f2917446094008001551045c1681e000190140d00190001c0c01100c080002c000294007080b0f8030b014460400d0102031705400310040800c460782001880300380303500035922143d4032030340040e14041c091001046221003800030840041d000058842c0640d03070035007244484050409241c0c3c0600340c0c1d01c4004040548503890601c00d240e1650160040800001006c01c4294151000a08640202a0b0742d88640c2c01080c0105441c1e5031040e0f11400d45031264800c6070342e900024081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 246385521 1250 246384271 246384287
    0xa02010f02070f030e090c0406180b03010f030b010801051003022107060f080f091207081c09020909070e0a0c0e1302030906010807060e040504060914030d061a0403030f 74
    0xc000d40c00041d400c0200701c0f0714514411450b12036181c070700ca10101c24040c031222083c01c4a50203d00c01c1c0c2040700344074407400380d1042c0600081c00305008802d04d803500c000d8070303140c1c1082e0310810b681c0800010030f004000c0c10f01c40d0140500140e00c001c016914141b200840100c07040d100c00781c041c24500303c03030a044040303595084c0344070440c1c507089501040e60fa40c801080300c9150717407007400010084000f0a03420440c004072940550804002086104045d0640d04000d50011804550f032110810070104080c130101200f40748075540f0180060301c95201d00600603a140d004044060b590040344060202c003640f4402039801c01003d0354005400e8510700c5007620b102210002199203c51094001d00201c1c200e60000d600c00c00e142003e41c0c0e21079988034000c0b551940c86014503800f140d5840b0001009080a034001c96101d0300030364010441c42032545510f941c0e100840e065074410b030000180b00c0064403160040600400514050801c0022001e81c3d042580c0214000281004548c00c80c9407000c038498011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 246386771 1250 246385521 246385541
    0xa0804060f0c0c1415160b2701021803032a0c030601030803040201090f0e060108100509091c0903081c0204150519050c030304110a150207050301050a200a0201 70
    0x6100c061580b100310413800a01d64491041c810920f2000030206040d01009030303003120720040403001115851307613145915007800034400a003121075010420400d03080f56201b010301c0c640080006039648800b140c00c00d20004d00988550180e1310400001e4404100c01024403803911480754000e1a4404602200d0b0030f200c480340c0380503450301c64000084103110218004501541c400d0b201c030382c0384030b0b0380f030180000c80394243c4038800c9000c240c00d00185080d4080c400c20f50f48850780b452104059516000000c01d400710a54003030340355a001601805851414085441c003c07580c80c180341e88002c0c9550782e00500742c0b046c00080b1980c070304154100700b14094990140c1c2d01400312140406200b40410b08004c01e1500a80702056914203265000003000c2e00500442c1c00546c50240034621750758903a200c9001802a010301d6a03000000190b00048008000c02d05110300e40c2c80350701070002903140c401054291180500682d007154034003009419100916200400284030500000d51125004801070b80189501c40d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 246388021 1250 246386771 246386783
    0x5030a0e07080307150509010603030215060d0c0e0601110102042601020f0a0507050705010e130b0a0b0d0204080f1b01080405010603080708040801180b01060c050307020d0b180a0804060f0c 83
    0x1038031020095600417409180c28414420040c90383c81401032402da034510b200c081c000d038014018010704101d0710f1280580c0a0009420002c54145c2a80c0c1c1e00305001d01503011000c5642c82d4010f000e80780d070b0301c5035001400d050010002e600b02420002003a0717164000744d0f4041f810b43d5031240951141002034041d585c8840c1c21003469038803950000009080303039201c0a0100e03894020680040741079030040c2a40c0f240381002600700802c0d4100c0340001801400048120b81c0d22048040c1c00041c2254188010300e5100c17241400542c13a03600c1c2c080810b1800070740c0350b802c8196400c0504003d00e4511040351030362151609103400107035625a03042c040d00400e0283c10181c6007100c0014140240680080144103ca5403500200000440d041e0a881d1640003440020b1406e003200b401003110b14810985c0000c41800303281601e00c1c6c00e00b01e5000034402c43c1015012140700180340c0401c035030620174030100e91426580d1400303442c0d00070095032111325503c03036406040c051141c80207aa14001c2e204401030510307070b94050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 246389271 1250 246388021 246388027
    0x30a05060c0c071703030402060d021605010209010e121005071107030309030209090303151002190605011e0b0a030510151e0912120201020702181f0605030a0e070803 73
    0x21002030350042e00e03010000d00c01e6620001d90046000304400c43c880e08100a181540c69540c2084001d500032518410301640034070800705140c41c1001c591020138800d800060752400303141e001400090585c00c14512560305100c12500e6800d000c546060102c001c0300c000201903861a03800e980813009111441680d00c101c2c00b0100816410000000a4a0088600402e01d41d0354000550b0f480c40b0845411001070050303446600c0a00301030900e240b4001482c010384c0d0000540c5c035050088a8500c1c0000d4455030f8440c00100540c0c05078050440380c0d680c248029803801410300c480b08440e0f2168030200010503554400081d820402c0340d8110b070150400103600c210759000a48000c151070341c1d4404041101d20121100003400740903660b400100c86a039030106500d0031554651000b010401441a42995020040100181e503200300c0c2d40518014016000c0342401e0130268000000318071204020012000d11050010b00d41080c2aa0750007191440c000c20080d001c80c00e140c0c2050000c1d030002003030784804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 246390521 1250 246389271 246389281
    0xf06060f0b0409060e2205010e0102072004050705030408161a0411010504080c04020f04090212010608070314150112020d06180b0a150e060a030e0c030a021e030a0506 73
    0x504000c104850407600284082500d0342800d122805044c0d912040d62005031b580c6e609115040d400c46090b550107000006090765112950b0b40c2a43e000700003c071200d558024086c10210b5030032250500220007650100098034100001410703511028202410300d1314046800f1844e14411054031005650100e914202c0c006000e0751071400704010745084684480b041184030b4203500c14070944048509000c0201010000302c003d010080d03000f24803028201700208801b01d064240342c0020040300350348000c054095850524003c00f0050064201c404150400c072091174542303181442150814001c02c2c01100c015080e00042c0c6403c0c2d10540e08103070850011400318034440d2207503c408215501800030190f58240918848112030000c00f049500031100c0c0018031030088010520101a174a03400d00b06210161a0f0014003150048112200000c1d280d4111841ea070a040c496a070740d4000550003042c5d14003841e80040c0c5c2101d1003401c80f040d01605450505810365040207050f0910f41c1203c01d1720307151b04103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 246391771 1250 246390521 246390539
    0x1d06040603050f09010c080105040f0e07081c05030c0702040e1c02100b0909031b0717010b0a091802010e1c0f020307050907090501080705090319210207030f06060f 72
    0xb0854001c40038000d5000040c04840701801a1001001e1075a0f40c0d40b00c607828602048018104030907a4a44103a40f49650b95170001c003000005d003d0140381004218050445407a8041c21300c0400d126000c000c030070703c14080c2c2030b0702d66801d841d1042c1d4100c41c0800c0c008041d2445510b8030012040c40100507810003400002d1a401054858510400401c144081e5403440d040c0f0804030000c1d076000070151300400660580c1010303610b100c1060b21204082e03a40e071556071640801c06d840400c2512426940d94200d81e0910f28006596000400780d804050094a151810004550260700030290600281c0c03040c590302c42d526019032102088540e50b00070303603003119400d00304444000c0174000c90181c854104081002e00d401c0d5489440f5010a41d176840f1b102e8204801107882e14409000c207030500c0400d0010451954051010f0480b4840c80e10751100d1271402e80c00d220b0360307482ca00d034803100c0d10155905e61110b0b165400f00c0c4070400d0f01e0301705c848220400c0d16890140020076040c3c0c80050051002000400e4101c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 246393021 1250 246391771 246391781
    0x50d1d0106140117070c020d140d0806060703030c05041206020414030c030304090b030703120810060f0c06050606070203070e1806070e010e0a08060c2a0c011d06040603 74
    0x42800020050349880da5408100d0014145519001c0f514200d60300200c00c0f11380e07000035844800761401c80c10540c210341c08101c0d082c03804030040301c0a000006902000200401140f00e8032881c0307240404540c2001000706810b071003014005000c05444803080518030b400384044500030013441403000300212150134000c0c0290054000e101c01d01c0b54251034407203070b072400265183d40100d004024501d010700d0104c0100c018903096a09580500034003100002040c0c0c0c86810707d50b103228544a40314180f50100320f204031019542c100301d080c800226606407029510080b00b03003d803030b88040d00007560b884190008082d8059040000e501d8800c0580215100c482e845045000d02e0240700c8004a00301d03104109600c944046681c88000345110300d0b004080d42c41080d412455200240c031240d002d0b501d80342d0301820b1010031102c840e00284c0001f480320b803d840380803480b02660b500302d0207455644004008542c03120b07542c0300300c1c038100140120441c90954005640e224008801010780745d5459441201030084c0c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 246394271 1250 246393021 246393071
    0x30603060b0a05091609050303070602031f0b0f0904180f031b110d02063f041e03020f01050112060b0d03080a05100305010608060604061706040305070201050d 70
    0x5400d0035040851400c00000b1803064410042c800c2c516541c1c0d048039860301c02c2c03104c59524100b218219000466840601c0104900d034003c48015030b80e8501103c0000d00c504448501e560545107000003042180003000c150f589680a800d00180c1d5810b5110024014205440c1400180c3c2d45400c250340c204814200361807030061107600e414894980300b0100080751680a103001e460904075030340f860403601d4410300d2405070501c02000c050901d0003410307403040e42d0454031003091b4003105036180703011102d00503180e20500071820007400041454540e030703850326020400d030715480030001100c4035604150090141c0d604082c0080c008014640e03603940b010b10166400b2009a40c0300c0d1410410010300e0038141d80260106170144c54088142d01c91503c1507004040003448500070b40101880400090000e01a01004101c80d00c01007115040282c1000100c2e6901d03400f407000404414010702000d50085402030380b054060800e42d40b2340c1c0090006907400e12075000140c000900d450040b00380b440280100c0c0c1c480c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 246395521 1250 246394271 246394283
    0x31c1701080d0f02061302010e010c0b09010c080105031902040c0c02060c0330070f1101060306061d091f020706061502010b01031104030b0903042103020c0901060e130b10030603 78
    0xe586003c606a8480d138003030701c40c1480c2e13441d01b0240d1005540900171040340040185000c1c5610900b5491341f14160308241c3c3c0e00f280594480e02c010702402d80c17100703295015000485c0a00136900b201040303186005c8603210000d01480d1034803040b815050140050745907554014090580c5d0b240010002d84d120361052100000d0751003180b0070b1015010010b50003c040d50004401c03110f5a0300c4000e42900d5403407186201404010103011210304081c407c1c010840258410714022403282e0800a0b4800c240326240f80301c65404107032004103e01280009101151380c01ca05060450002c1494190800b034458420054406410b207035001030100030081c28158854240d074000c00681103e50011020b4942046560700a00011b04c814030100d07454084c80c0d600407510104687c540740d0365034180da081420110580292503410300b0762005154051100341802101140c4c071004542c1800d50203480c0d2020b04151070300841c041c00c49003180c8140761b800031540007001440701084a8619800401a0905000807105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 246396771 1250 246395521 246395537
    0x151302040909050d18032028180b1c030509030a200d110f0a05040905030901120204060210020702060c0f070f14030d110a0606120b15031c1701080d 65
    0x6040c90004032010b50340c6c00007500c001400c0c920300c22186194000741f10b541c00049001c0114a2010b116034071904180030b00154842c217443c200d59a1221851081d284542905240c040c800a903144000030a0044902080c4032241ca4903040403075140c00748031440354252054006041c1845111106010050062103008050448210034026050b8050000611030164002100d400b860044118141050050310b4800350030713656800501581ca20b40c60540749070f04002082495540d004c0f20854400d170440d60154130305480d10038001d5546404070b107041000ba030b01040d50301c21980e4a0342101c00390f200080417221910061810503842e90500e200380b071076810303031400c0000f8000e55140c0080000e000040103400c0030039900d42d05881e505c11580c5c10302001d014107420301e00040d50502c0703214054140c07629401750030310181c41e001001100141500031101940c1d24208400da400160941f50f07480201c000f6090800b0205080d1144089141d0311070004501c14004122400005000403e1020a945440c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 246398021 1250 246396771 246396797
    0x111e010911040902010c03030c14272d040608030703020c010f110c0607020d0c06030203090706080c0711130e010b3f03131206050f151302040909050d 66
    0x7102e41030f402c001e01245e1910300c503001280c0284e104c2c14080049041140a00c50782001c0e583c40c40e4000c600c204128035050642603002884ca00034021031040542c0d104070580040d105d01f10800143c0b840300c0003299019484060740b616203403c403c009004900c2280d81b1071a003131a02a44800c1c903400d54900080c0c0415061005c00d100302810003030550b440020300103d5080c2000e00500703921110069801c19840070741e24000403072004040700109059a8016141c3c282000300301e09111840c2c8c005010018500c1c1400b40d008001401c0b96506031303005417a0380400741c010022441c9010191815080e403813130f0116550804c80306401007080f1000450300340c0c882c0305a200542118503265412060414004070b01c4156444100d5407000842500c80b00f12030030900001010018491a03400c42801e022034030076540c00b0080c0c58007130940c02070502c3c1d0214860786088a42055000e00d88225288102d80c8040030080154913a4111005019003960510034007109040071940c9428042c4c0800c000780d1041803d034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 246399271 1250 246398021 246398029
    0xf110a03061e05100b12040215030106090617010e0f130203160f050604120b07030e01180210020f0c040c09030f080714030f09010305041a10081e0d111e010911 70
    0x4003c2e40d0030814006d0920402115080c0c1c240d000500881c0c000003c001002151303829100514020700c50381e90b402d0503181c20710070020028141c0d8500485d203503403034000600c000070628160740d500c00c03490035070500255645c20008108000741c01001e5014000c90326200e170344d1080c0c0b170071401c142c0f03131008070100003165110140001d520482c812540c100342c1010660000543d28400c003500001c4d2403a000c035020068001507402c40d01c0c6401414208401000000c046003022120413809070200c1c0043d03e454000c00300740603110107140004a20407592010b50b820418000d080c900041d540145590014a450749810304055204070801d99aa02036640c2806549100008480c101018000014245032002c801500503001c09002200c0c480410010307a50144511034200744500f10400820320040d02d03008081e07052184400c0c48141c2e00320b203864842c981d644005444000000a803418040c4031501e048000d04220104004286217001c40410100c41c40054010103a124015480d001c1c10200c07a00801c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 246400521 1250 246399271 246399301
    0xe0a020a0f0602010c020f03090108180f0321040b1506070804090504110901060e010c08190f080603010608030412050c0604030305090109150c230f06100b03040f110a03061e05 77
    0x3840230f038020084000306500c40d41c082900110242440c503800d43c90880d04500780b40100900508940c00452604800c5c000001060440042100c001c6a1401c0940715800d40c0b200090900300b15100e0060209043d031111811100c80b0342c0c01c1407a503901c99490304e4459010b000c060310241c031000c1c44403820041c0341c41c0040c001070480381d0a840d103160701d1280000549000201400555041c8002c0c0440190044844d9060780c4003900395640205103281c0650241965101a20840c080ea02d000400c0c00301440010444050740c804940614500c1e26916102c0d02e010315a010260b04000081000410180c1010241c603c2800980380c00004588a200301d0350002d0100001e0800900070080020201d0510314001030b80301210b2440b8410403c60034011403800b0307600400c4142d00c0d44010100444007150500b800b02901c3c0c0021482c0ca1401d0a45412401180d1000b0190010400c0b500309440766450700d5048008661004040c4401200c1c1e0003000e8526104c1140d54040c1c40c00c060000703040700d8429001e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 246401771 1250 246400521 246400543
    0xc0e0a090e0312091603030e1216030602030c0415210c09120c09110d0e0604320a08030411010c0c0915090509010209010f02120405040e0a020a0f0602010c02 69
    0x11410000b5210048034040f80c05482c0c0300e19030007261440a03a00781102000d5002e107010f5103030110600c85c0141400000b6000303131005000f039009200740c20f03985c09444e45c0c01012a50882030268980d11100d600184502c540da1200d5107614030000c07220080b0380c1001d51404860503c140100c44045103207081070950300d80416403400651074841c1400721011201d515000340d030290280da10740985485500084401c00100302480c0b0707101141c0030f4103000160140090304608880502420309260b82d038121420121b81040701240788000171149004082c1503800204080360b002c8400b006403508021000d40e1003940e065852002807030107002a940100042119242d101c2000044180741401d070724000e0002a01c0092400c044410000c0d001c221409803500804a20000680c1d41e1014000036068450400004056411000030300140c1800c203010b50741107490a440201c0e84294501d900c1d4109241441c00039070003801d81c10080f9101844074505c2c0142e1382945c00811000030586001d0ba030341e002140c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 246402877 1106 246401771 246401773
    0x2120f0105120f0709051f030b060f03060603121e04030501020d06050a030c0302100908010903020c10050c060103060e0c120a0b0a05040807240c0e0a090e 68
    0x603120300802d0440005040c0c1011000700c07540c0b2013281e40300b03022641d9644e2000541d0140d2130303021507400b042440041c888107922840e0440768920140ca0003400746013009403e00031824005801b03400340c1c0d8010010700034180312062610301ca0340007840e00300c2222514200041f0141e500806040075511079400942c503150121242021181258042842070310958006c002254402b201e00c410781c6d805440d80c111003005a0700544011020341e10401141d840c0c0409a41416404248040c10031000c40359642c0300ca1440c0c0d0110b81d0b502408420700a0382c0c028100400001c0c0d81503020078119810381c02541c42e85460040080e0214042a541d02c40940000610100b080600c036902e07580082a040c081040d0f007003680341c982860140381c40040214408403007484804142010a080c0304100290501c1406640c1074010321303502110858030b000d0720703032443e001c500d507481805079142c0810904 = true := by decide +kernel

theorem cover : BRFrame.Cov 246223021 246402877 := by
  have h0 := BRFrame.cov_init 246223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 246223021 ≤ n) (h2 : n < 246402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
