-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4340
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:18:12.342125+00:00
-- url     : https://prove2.me/submissions/d9023d46-e067-44e7-a18b-0361812613b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 780395683 ≤ n < 780575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 780396933 1250 780395683 780395687
    0xa09020405092821050405040f0e0d0e280e0a020a0c0209071e0801051003050c09191d16021609050a0f15080f0601060e060a090302100c12 61
    0x261058102c54407080003d051003a020007080803245240c041c805880ca15041181c0c0c6040e0140c030314400070041980000c0400250505204040b1910f008210411110030003041850300c44001d903440108000c03000030b032840c2c10342da49211200483d45822a24102c00c075900c0c440d0303010072414400c411003189444000740000e460f5008603120300345035a507141e0581c440c43c0e007008440c3c00b01070f01d5441080603400e19880007039040f0000744102c8000c1d440346003496260208000080700a6038030101054200401c5c08030202c003040c140c40c06d203041111070407a070500d40740d0840b240fa169607112112441c2940b40400661003e201200e000d185a1140100c4a00390050143c5e81c0f082c41ca40001010300f40c1590400c0942c3c000d6106541150b0000c0c40803441090400c003503c1910750890b030445469599080c10002c00301c080040e482c0e030007000c5003d40881c0d0b15005001c5d103403091307802020b0301807400014012503c61189102a001d0b503401030a9858441005000070200908a08222074885c1c10350401a4918 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 780398183 1250 780396933 780396943
    0x1f18080706180b04062d031b05180d02120303150a0b030106080a092a1d010b031909020d2105031b160215030a060902131e0e0a0902040509 61
    0x240004000e0f03442c1c50301d0810101c3c0d80000c48079011400410350b681c00901e86105062000681007240d4020492100c1c03200c460f8401c80010702c9100611008102401f06030740a0180600c0f0307024203ca00d8a60000c150000c140c01115581c14913080340400401c101c0b4040b211001000c0450080d10202e0516031185084202c5200a00840011904282c00070b84611000d030007404201d4420540c400c100d02070001c112800c904003401614820300b1b11340090040c00724008280d10140003107580180154548140058184030241c00a0300c0d103c40c521001318a0403181d0408882e040c0d02074910001d40502d410039012944110903140c000550f00107070601c040707208030f050313a000d03018031740c0d0341200b21808584a150a5101e154980014891752840c100541d41c0e600381e00f44c2891200c0c428550f24600389420310207d075245e400c41c0c002144103002a44188440100740e000b039441c91401c0101c0980349100a402060340340c0d00851040c501441000507809464002042e01032082c0d0742840300c3d1300d071850360688503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 780399433 1250 780398183 780398189
    0x8010f090b0f09041106040b1e1908090a0b010b03091606020304170703080a0e091e07050d02130305031305010314061504080a0506060913021f1808070618 68
    0xb241c0c0700d46103280346040c8550903045480740c24001c401814000c04101300e600036a01c110300300c09012400801201c0c50b11303203602a2a9a0450b41454800c480180c840862085040e62040200d00c00c0000d5208908000307200c082d58001411000e29a9079249005031544204c2d91800e541c080d400f0100c580414107c807000139605240c000d10705150601d206450203c88100b4801070300e21502d04000040b448041c000c20317038616540c1d03a005003418941c0903c040000e0181892400c83e031642244000205180390554200781c0301d180650b030342e1030a20030510180c021181618000003640c81c0000030401c00100030000c0000821960020310340d42c400640440ba072085054402841d580e0000d000303440d021280800303449090a940c0d06007034590340c02e13901d440d0b800394080310294041c00511039181303070694010b54010b0700030010580040035036000c60300c3d00041c50040e07560b40402150310090750740102e4050141c0100400a0648a903a484415075070398114402c0c8008904a10f40e0305c170101502c00f54450503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 780400683 1250 780399433 780399439
    0x813030c08030c1c0903021c1a0115030b120d230a0903120207081e06061c11010918090620040e04151103060906010806030a0b0402060d0c08010f090b 66
    0x10034103039001c804504d10280d80d02c10812000020110040e9902800e0159038440c0103440400a40f841c580040e2000c1c804540000b82c651150040280d8000c584007803802702690301c3c0200310414400042220001400307080c800c036018001d280b941160344241c0c15004038040783c00c40404071581130650040c3d8814102c81c0000a0401d80090010a0100300c4050700112030f88102c8113010b80c1d80744e40508140d0000388125408480b02c0c1c074102120000c010040d04039608464a41c0b02c9504281c0180e80100b040e40010094000c8070310000b03a6a019a060a00400040c621054002600f40302d0000904000100306c400901d0503000d02580c9844155071120522800301c42480c0505040c044900004010021265210002c04508045542d800ba00c03050303902014160780c40e4100b00702000300c3c0782d1008180034100042c035410000c95980000364440040d421801003485e9450380e00105865105d4200e00407091410a00039429042d80309074418100e40d0003014180d986616021304c0340540b40142c10840e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 780401933 1250 780400683 780400693
    0x305130305091906051e03071704020d050105090d02100c091a2701030e01140a020a03180c0602070b04032d02120d090e0c250813030c08030c 62
    0x10000740200010642e90307200030442c0b20b00310010418100c400d002600403e000640c0414084e002c408016449001d401c0c0c4c07140f40c242585040c02d0020302d84c020407154a07c44c210910042011b54883c0d4a0074500d05403c80e009000600d0400c5485a0750468014800c00500c07411440740780040d42841040082d864643d10311200904e868480c24805000c2c02c0b041c40941010809820190300b505940c00c80079207085045400c180e80c5100250032141a47c1c034800300b69040023412545042811165980624130000c010b0b16aa00b200c82140104a4800622040840514180148200310280d08120b402c01d074220b420550f25800301410a010f1844010031480032069415082d1481c0c1c41c072a00c80c0c80540c006607604140703540000d402c0355004911000240c2080d0004000e0701c0c0c0c0481540041d04121880d041d00f410043c4a41c2034030310410900312401c3c489445c40d50014004401441c551176000a0300e16152200c8070600a132000071480308691110a01000041498011041d200381c9010140600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 780403183 1250 780401933 780401971
    0x509070503091c08180118080f09030111030f0108070b27130e192613090501080105011706070e0123221a0d06030204050108030903010b010305 63
    0x664981c001600c018080d01483d000d0004503241004410300303c04183c1e950840d281801c01000180358040d400c0c010950b41840c02c2c4608203550500c188400540c000c00c00d940d5074130700302c09400c1c05d40a00d0040a82c9542003644c0e880000503107402450180c0341c0b8904106459030f9074038111b540c580d030900ca42e5051060510403946d40a0f40420491120794071003a103418510190000240c0049100c040004403e1740d03040000110350003001302416003030403c15003070704c480c01c42d465800b021010141621008080806030760b580c09107000568400d01004001e801a09450b0b4841c14040c2c1024021405250b00e88400055a071000c45000052121000302a204c240c0380c1000c03c0b1100110724000c503040c8402302442642c2000303502400002c02d003005441c280c54074030501c0240202012030380e20121140c0c0f05082400450442581c61980404801c0b1483c0e840700007507050406051079510195110f407505d40009404140071008200d07604c0114020003901c000c1100640858005481208444d0204142c1e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 780404433 1250 780403183 780403187
    0x604150209270a1b2001140915090c0609060c010605060a3203071d0d060b0301051b16030201020d09110112020c030d110c0f07050f030304050907 64
    0x24004203001502c0040d400c0440c1014202c40c011001000c11603240e50010044202680c0c0b107018100c00c1c42948194507140010b030001c00050560052055182c0c40c2103003010006825403280c0e400d0b4009070341111841c178000d08603649806400c5103940d0300f00c03107540026240010120f801c40800000030422420301040c4401c0c00556044403042d000203668807030003c6102e5035118013074a1512955600c122000c0c0001110b0ba00c1c810440c1511007003a00740a1081512400d0002900e0f809501403801441100824070300c01a5014101c40441d00b280d0341c02d401d0b005100880d0040307251007030180c2c02404541c0b5813040440e410404c20341c6154005100303008a050000014181005040c000d10000d401d20810030b14800880d2103039181200c1c0c0310a41c5121610340d5030032804100700704402c40340441c1030040c24035010b40c9a2041480c6203c0c0943d132401013144801c0040c017541c0000e00d80c0741c101c800c00c80c08203440542d1440c05000b401d1241040e201000c0142c42c00101b04c505442c4007030b10410140d220701c002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 780405683 1250 780404433 780404437
    0x1d07020607030b0d060614030d0908060403030c140301060203121501020706080703060f1202030d050f04090b061b010b030c03010605060f0711090907180c0f080709180b100206041502 80
    0x315500000c91550f641c042240c0b4002c500140089420034a203c16000c7c0401d840c1ca0004003d030414040c900c00c08024030403000c00e205501a0b054200401c25292a01d4221002d01c59010040d40c0c40c0400b00000c11a40d03800800303007811440d076203404019074507094014100421400540c90050344140004d03c80c0610a1a2040e0010802d04000c03520035101c658100c032085103070f08084040082441c4140c2545810406043d10741c140b428424940581404482550301c80ca001d000078460700d484005450b40c0b00d0303800300c41d003004000c07103004401c041039418140a0304105000c28807901c1601b40c449102e14040c0b00700c10886000a04040c03a200c5c41c80c203030b00e066800041090b1541c001c030100392a4581c0342c5c8035045115200c41c0001e0014242080e010a0718080030000b00e41c0000e00e00840344101c03640002c5010b6480c07090341407401441e034074801c00722403240f02c94000800d003503480c2a2110030041a6004607078051421184200c6100b0054000c036503406c0202c174003820380c414a40040b681c040c001d0380 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 780406933 1250 780405683 780405701
    0xf031c0c021c230f0a150b0f010801031103030d050a020703030515062b06080a1e08030f06030c040e0c0310090c0501080406020706050c0a1b120e040204120c1d0702060703 75
    0x2042e07030074200e06000301030f00384400c4000a41704a8004056060101c03800e11640c0040304044030050070032300314000000d04407241400000c04084560364a02c5142d5010001c0d1688070400d001c06011925007480c3d010040d410a41089004c40e043c2004160000185007540a1000c0d000c0c00c4582404c8505507403000c05400e0f01c0b00ca00b541d008a204580180085004071000361041c030006204c0400b5030303c0c4c8510481059500084581485803c41001825000c1100c0d000b00650100396200e40390900001c0c20f2004003c1d01640c000d1070b00e0f000c81c0ea400d1011030340d013052603c11019100c5080070407161406072092a4402040006020340a00c0f00d50702803503005411030b014610040c1016171540d9081c0460b00d00342d43c01c0f80e0000d00030880340c5295600c03000300e0b034254030441c2103201001110b0355404000284a0380481c01e0010311000300130b1a855a9064400400b1303c6a4420301c00d40e010705004003222818060082032507008440717542c5000b058000d04d4080d40841d0300402c8541d42c0c8100880084c08200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 780408183 1250 780406933 780407003
    0x29010804021c0609020d08041d010b040506071b08010606030b030105060303070b22080301090c0e1012092103051f140d2301060801090507050f031c0c021c 68
    0x91402c101580306c244041080510444019a4030780c10126981007000c01c0c050b054648884035401841042040804e0342e048a809540b45510780b01f00c0d01d08401060280800d00e9066902d54600203403052054100000311010307918108060000e01003072500740c0310100d91668040e4001c00644000600c0c500080350301c840c0889074200000300003ca18001000020001d950702e0f64080700510640004d4458440320840508005071140710110104031014242e100c1101031089e46500318146003907940048440d1540101c1d2403a207492521030091102c01c40703090400010785820b001030481a40c11304908803080c07490b24055003180c58000700c03000c801150f0b0101a0400d07030346144034001a0380d818100714255800c004524070410015001804c40f20030b580032043c5681081220030110b403012941030180c0f14156180d148020303a04010a00d01900d5680c4403980d18181c040841d9095402204250b9407842100e80380c103038001d94034072000d1900c100d02000d000580481c58050030212020015604c10b19a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 780409433 1250 780408183 780408191
    0x27103e0705060708040c05012d0306080f031c0e0304030816120314091c0e0a0302100c0303050901050f012117070212030a0e100c0629010804021c06 65
    0x9584060810b4019501c48001c1403507182440200111000d4400141000b8a4a400307600403400140c1201c41402c0f544203d411105007128841620a80055001c0c1042c8021680f0117141001607a583c1d0384141c402680d088145241140c0c1035206014101c0034171050310040d801d06045807142c000340c0d4440c545d211449003483c41c1410000d0728415112040a81036100064003140030785224000e05001403c40d0407035004490030740d81d1403108242c0b04034041c1d00c1e454004c0c2c4451401d03020401590040d08060360005043d40040c030000e9200c4021080c0b180f00c1da50501140d210100800d007a2402070720350242e151030f40e100610038840300780c10100c04e03048004280ca40b00314080d211030f2900084a2041c910a07203001800005500b1f04584e10060038440300e0003075141c1144c4000007020f500b15059450300c00e400302218000c503076108007074500d40c2c0c0750451002c00c50200006008041040748481340350b15101d100718210781c60742c0251040780c840c40e0040d080054105040d640d10309003561100c1c088032031a84d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 780410683 1250 780409433 780409447
    0x1e020106091b0807020d23090604080708190f0f0609060e03030105040e07140907091701050a0b030a0b060402090a030c0825061727103e 60
    0x21900400b6259103003002810b490740c8410b00300500c0050000d007050250b600603c2c04980c007951062154181f041c80742034070942100c10307407400d411a1207600f12a683c44107001c203011903c020b0110b91035080312001002c644100e610800f40b000c0d1800d403a9000381c1881050740b49840804c030848404501140b05220004010103180c3d518001c4544201101c0c03103a85c0084014403c42c1002d126500c80c84088070010301c0c07480c0c580b0b80d01d80303c11448146904c1c080c000010100c2d144074010703240000546120b100c161516610b99440d24000c0800b20707141e54405003030007200b105038200030038168000c980281d4107000e560740700428003020f0340c0500c4601c5d811185070000080400c00420302c0300090f020b254040d1490030000f0524a01c0d03480f0a05226201a5030a08100541900611500d440c007480442d01c041d075a81d90310f0300c5013560b480c820344802c5071041800c41d007490290108001d0181d4441c40c40800000743d4440001d1305010120088040b5502c41c0e20801e07090100030841c503851114184203451810362 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 780411933 1250 780410683 780410699
    0x70e0a02040803122a09131811010e06040b0d0b0102120a050d0506120316030c02040c020c0301060602010e12090a081e010e010c0804060b03120a12060801020a1e020106 74
    0x4c845035000507401c04001c14841c4c10402e000182c0c4041c140d80303402400041407202c0b410282d11800f0542445540090342c080c110039003039000300c40c1c200d4611006000e0083c1a00303080c10411a2410440c0c000f40510f243c00c0326924206059609a03840d0023016414040c050703072441d00400c6007440c440d056208450300c207100c00645000400c55601d155540380d8545581080c02000d880000d0f000d07904c18007481e804035844610001c1a2064000d100100007180305250030103031400d03050050040d40090400f04610852500010345a0540e0820b4000704071a6941e01d13003c03400c80306501d48001d0250400b5001810103c40d0b6409009007140c0201101d0080307503103030401403800b4a90204141c14007408881000140310a100300011103042000074030000760620001050a400240010700306940e070385a90440751400c000c005080b048420a10307958010000000e00800e05d401039070310001e41809000709000720b0600a8900740034a43e1900c42015042e80700802e03440e90301c0d6020000315136a032880091521 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 780413183 1250 780411933 780411937
    0x31801230a090e010f030203060c030c040b130303110714190b2805040b0a21050f1f0b0927071e020d090e150910170609070e0a02040803 60
    0x90280c5550044515060b81c5800f803040590120583c00c0c1041420000350b1000308040b9804a103140586070b8070355a854607000e050049030400c4402203000301d000740003466039482103403d40c0c0c066152051110312540c8102c1e40c50b146070003140034450044402500c41e00303141007159400c2101540020754a171310b8210120b2a90003808941414080520500c42000c03400c601e2031725180c0d624604640b6080c00c203400c051140c451207000d2000c10141c03c0d640c068404400c140c400300703501d40b013209000ca0b003014011300402501c299001360195001c8100c2271880e004107841403003258400140d490600440d1403c02c604030b20b04030034a0f0340000c00000d000c2c600040c1e0708202d80c031404960322220203204809e481d840414003606900713001d65000c030009507882d41e084018082101c00c00303410400e084d1744040c3c1e03c0306100031581026030848101400d000ba1520f200d44941c0a5910303000d804000c66072000d00c01c66a0301c0080d28212101e400c14a02402004001c0d2849039204408070009480d15907140c1c525131031a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 780414433 1250 780413183 780413197
    0x90618100c02070e28181a040201080f09030414040e0313060e0d170708040e0f04030311030601200f0106030809030c0303040b16020f062101080f0d0c110901080a03030e03180123 78
    0x1547d51803041004541e0009111a0400f640b4000300038103182c890307845543c0384520701810315540340710001910556955003150038210f403448292521407003803000d00c0d00d600c8491301800c0d0200b034002c00307422403d05202c5512840070303802c00c8200c41009030800c1801c0140d0300c000020340b502d0104010201e040d07600180381e00e0042401c0b4091b104207240501380101140d080b50009502c1c0c41c0208180002d036079010191510100d81c404040301004040c0b25014900110801c070400c0039428002c0000034000000050003007850194159030b21070454104140e101d02c540d00600c02d100e001030022100300c07806610078828170b038800342044140010000c0084e03159008a1401c5000400303090b0321804000003003002500404010000709190344403901803507168001c20450b0401c120602e0104000d01c999411444503415001d0b100d035000f07507106c00340b603074844160080680c080303420001062001c1e44000111a44101d10728022052415243e00448403800da401e08407400b190301c481c60b850b9040c0244001c03c81 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 780415683 1250 780414433 780414473
    0x11180a09110406021207022b1e0c0806011a1813020306190311120705060301060c0b010e060112181b140306090618100c02070e2818 58
    0xb80d603c0c05400a16101c2410b0400e102070000380403140040c0c03240c0c02ca062680841c038404411083e81c2005614404940701c3c80980300f5110035031500d95146c140c00e1020f1089004e41202c0c00c502d0b8517000d010ba69240c0a125600654640100054064240902910428800841c440001001c40002501c00d02030700d1842c6808a900105000441c6003044205510001d1841c00400107865600c400000510a1500e14024400d00a4cd44070340340e0241301c0f2402802000f407110f512561181c4000340b0400c03100d40300311a085040400401c00d2008165170b5441650140d42c1c480442424000010107400700d5034003140007034100154140000c0b80b000071041d000220071600c8a1040c9008601505000001802c0e4065081607080c000d060b14082215a40301c015100b04007210300b981c083c45032800309086040c0e60403d00d002070490400d80e0105000b0100d6005007400760440d00c5103a03000b1107850391030b2000075081c103102000d0140200706030081c2e410f11301070507005c1102c00201d07140c1d0f0f0105c424078059944 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 780416933 1250 780415683 780415687
    0x905120d081807140f030f060a020c0717070504110c0703170409020d0524030312060d0c0303110c010f17040204180506160203090d0b04020f04020c0606030c01020111180a0911 77
    0xc92800d2840e109451a84100d0051441103602c071442e80d01c540703010f02080382c4140c00144031202f541c020000301000b041c840b81c20300404215540c0e126240d0720316029080c4030b942004c485031501c03038820050310401000d400c00741940918507130302d2243c05010203280e0030101000744000035443c480c40c40501b1303a032104071502045e6803600013004142079000b40044144580d410000f10101e132000070594041c107030910203408041d1550340002d1140c200706070004003401803509000c000c0507070100301003d081e00d0603400c032007078821000010341e40c51880405081c00521000403258405c010464510707007207800a00009000c07170440c40f80c410700400c1ca20061b6010352003030060084c580801d00b0f80b456500e07054400303941050505c000003184240005805032102c0004000704040d950750703607185140e42200401c1150b40f01804281961900c0c401c03036030703075104c0d006400e0040302e10b50043c021081640540012203280100c40811800e151040f54125500640800f8021582e03103043d10030a24010700c8801095 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 780418183 1250 780416933 780416969
    0xf030f1a030d0203040807140a0e010611010c0c03050f0a030e030a0c021318140f100f180c1a0c01060e041b0e0f0c13060f0905120d081807 61
    0x142c98200078088440441d4020482003045010108101c0c043d244445102000e181400002801e2084035030446071903550f0402c00001c015030006007002d8603d00c1480244140d0041d0503095541d400700e00005800f1880c10488904200b405c1c10040c032031481d03107007800900d19440d14805032a54004040d0640401c100e91083d905501c5d0489006080e9046503505014070444400b10201081038100020108403201141002c51703c003c0c0002801110400c0c12104414800042017020300003903010555014039000020300341100d001c40345620141c002072014440361800c1d560071101c50034905150004e04040c0320110f2000740a00800c0020035001284021502705420215071040c81041186101d2504810411030030f109420403603803180d804181285540d41d1420041154403500c8502000c00c600301c0e8012942e0768101d0101c1043e8561950343c1c031101d58541044c0104440c01d80c000e0155540984605140f95104082d51a880041841c500d01c1c05040780500c41d00e4005660460b0a145400d88450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 780419433 1250 780418183 780418189
    0xa170c220905100f02031306111e030a060504090218090a0803101d130602090d0b09011a040c080a090c050a060203040602010b04090f020405041e0602070b070206010e070f030f1a 78
    0x1100824590b0301c13007140365082002d0f8410411b140980000d100a840b41c025603030b06000c80e001d4880b541081d20002407509104288032429074012034144000fa440d200c2c0114290909206c7d01c000c00d179000e00b603100382d044ca1150b164083d150090800500344600d90180d00001c003c0da02950051143c20340300d034089810711820001d1000240b414031380c1c283d040b034200143d90517161400900c1c03581000d0010384c1c6036003070300c08039000118891001c1c1c0b91070314070000e200501105501250b482d0b04080700e5060b8402203142000305982d41c1c0401040001c401a0102d820340c41c0c6a40400403091007804900342080e03440010a00c1800300e5070281e00507810114082203030755020b01031106081c0c0f08640800c0850f00d19900c040000d4007005020f805241d03144000340400555031390469845402c078030840402c0c001c61810002a51148208440c00c1c600c03100400c00140c00003030600d0596546643c1c18010b80d075090307000c071580250b10f5100301c00c042d1692a0b00605442900c111a004104030007161040030b075030030174 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 780420683 1250 780419433 780419441
    0x2090c160609060605030607140f1204110f030c010c02040f02070209090a111005040306020a020115080313050d020f091b0307080105101403061002010b040c0305060a170c22090510 79
    0x5d42c002e0f0003400400035901d510070b010446d124000c181c0580c5600c04400400d20a0051112201100b10020f003840184085410400c04904048580010460040301072544442081d40c2ea140414555051080189040d400044042183c441d00508044246d00024288241035030f18542e50f40090640300c0600003a117050304100a01520158084648200010a0381c030440c80003800c015404034603001e02c0342c0300390401032400341c03070721404d0105903115410030351280d00452110b0401c500d00710000903036040a8032820b41080d0000c000406208140c0c00380000d03d0300c0207140751012009449004461200000914040d6880d950f41c03407040e60500044c0b1030307030000c05500902402100a401e00c4d031410050200d03070b403141c42500c546a05102006080c4c1c054504100c129600c2818212042c400c241e0590206101d050100c907210010395545000e52005101e101401519070440e035401d140c2c40c0bd00301c54510003040030f422080c41090802d2440c078215030628030100c5032900201001c2d1410403143c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 780421933 1250 780420683 780420689
    0x10c0c0b091b060706090c060302042d0b031e04060b09060105070b01061b0b150f0a0305030d0c140a0f08090c0a030b090f03030a05010816060c02090c1606090606 71
    0x90101c0c00100018601c0c0002030b4011070b208400000c1c40000b04003060300700c400e0495102c040601a65140e00018000c0d41060090060029403050100700301084c1840c8504810f918100c0c82c06028180309040d5280d0f400103080d07205040b1541c40842c0c500440041041c459405034400080c00003000040100844000d030005041100500046000c51140001241150303003a0412007140015052411081c100031341d801780031400e051781040714550301c0b82800841c41508840b92031002c0440790404c1150301d203a000240c0346074030038041c40244001070b5110090148041c2020807603000381660146241c0d00c51a1301d131001404d5903007880f4850f42c000300030582045842018003000f00d42400800d0340e036059840081d201c964030401042c0608000e120314501c0801e80e10659650303141600c036602c040d110030701c601c0040f403003101c005c000356684c059254410340d030703107595281c00380103980d020085d18030400f4044002c0241c08001c0221000326542429124a1241e8004200c0d20301a0600070229402a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 780423183 1250 780421933 780421951
    0x27030405011715090403030b150918010308030c160c03060c2c04021b0105090d0801050d1703040309050901090c180b09060a0522090c1403060f01020c03010c0c0b 71
    0x4050286035006190f54140c444401e80e60604180d98a060403806090710403517044d08a040340030510030480c6000c008140d800001d60b044600d81e8010603200351145001d00c009000b191050000c174141040c3e4400402e0000300c03d0b00900a014401d0310b5403900e400306c0c7d6108039019580e0358661490290803411701084460344084000b0809404200e0b00c4010080d039074554490b41e40000c00ca00c4240c0444640d880c20300d00704000704054034211a0349a41c1c0c7ca0461500404600c01c840001468504024400545540802c0a224248070a544040c07140c0005d801102800b100c40303400320b05a100e280000380280200e001c0403508040c03491016141094030219540c0d110000d030000d01085c1720040495201c194240e90345913540c4015401228240203810f0401d6000c91205e030b403100480c40307100088098030302d48841007258554144041d01c1404c1942007000380034000740002a00d600e02925000004041070054a40301c102004c0060b085990480b0200003140e0520440002e01c251b24101c2075104480c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 780424433 1250 780423183 780423227
    0xc0b04080c03062811042c09030702120c030105070504090c0203041a0306060403080f1c0b18090109150510050a080a020609040e031c0c090b0d052703040501 69
    0xc50601c40d8500d85074403102400b403141c010541c05060285c0c4065051414803044a48a40c0c031940c4003003a00c5856200440069103090046118007184840310340242507250003546032071510340c2400400c086030b21481000b80100514580309840c2030051901c075100e04d030b40302941c69003800940703c2182e500d100b084c0215071080c0f0003440402c0c1c2104004003a12040d404880d2207680700e6001445520541c0c00040c407820b808100c4548a00100025000c20b04203a20503008151441c0d03444000c5981e426602030340100e030f030030b500294084503010341500090203d0000c1107503481a00e5003080401884000c45000382e6030340421408022508040c0701801c1e0448004201d1481c180060782c0e242040c80c0c0180c0700700e00c006500600e030b50340d9512500303c51000301d00b07072a160000c94030b544104036514640d1005513414070070100c00c0180714100413401c0d19014844c450406158024000041c1070050401e0000031800c481c1130341e01d40408044150080e00070300110755842c200000104441000342c030f41c42c04100c817 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 780425683 1250 780424433 780424441
    0x50f010b0c0601170f0f010603030f0e030c040c12020c0703021003050702030409020a0c0b0712050c0306060a080a2705160b0a032a0e0a0b03010e07080403020a0c0b04080c0306 77
    0x40840c20b2811940400d002d003003c3e5211100381424020740c8924402240714440c0202c140e20b0040d04640203c82c0244c0301c2800d2510310340c00a41d0340e2210700d81e80070340c160401c3c00080c02625250740540341c510060715140d100c105591082d601240c5c0004058005580078030001c00452421764030002e1900803d01d828415800d20702006950ba003c1e501801501c00c5d004543d10704034502c00c2007402c1181d03401c480c44910034101001c2c041c015042d0104010b00c51800c100008840140580850307005000c00741c060b602e00b0321140070440b40c9403000341008444c2600d44605c107801e1505203103c0d020012031045c2001d169400c2d0728155242c07103403c1c0900544c050320044208200001c50301640c800c92190b00740843c00c4500078080c203100c05d100300c4038002c0540da002e5822003c1a070103400c80a18803010346030382c00229180c4a0018960109100342d03e0168200390002e0012031260f24481e801c00d00c40e004454014085075500140d0000c0c1e40c0050200104c04141049080c4c4100100340b458081034001e0461820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 780426933 1250 780425683 780425707
    0x190e0615120903160c08101104060c02150328050601090506090d120e010201060e0105030601060c0804082a0f0f12070e04120f0f0801091107080d050f010b 68
    0x1140d007950014102200001c0b40d1100a0045a249035102e807200d03030814109103090303180c006403070240318114440c84000f14411815403180d00b00c8185d069042c49d017414a000800c031100c0224a804981181c25941c1c044030003614040614080e03503080703040d0800c0020b907aa1103654aaa000d8403202d59500300b101b480180e0342c100108809503031059034020380c1d85029201041c2da032a001007005222400e26021440d0050780304543c0d24400380d09034000c0c40015a22a628008a4028007807980c0c541c114400410180d80101d96600c0035500c2080b44508080c0e4a00800341019001c610075884031218150700080c20000003c0b5090000c802c07107102d0300300c0103020f0200d0301d107105150b4614040c120010008113240c108104103802005506040080303440c2600e4028040201032490101142880300c0707602c407042c02408401d02c40f82c0aa0703100c03802681307800d2000004c0e1001030101e17403d243c400c02a50001c03922030402007120030f80d040030200711810522802480004140c0c031000e1042c00501000701041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 780428183 1250 780426933 780426937
    0x130b0301020d1b1704113a05160e060d061b02060406060509010e1f08010903020309041b120b18010b090306100602031c2307110a1502030403020c190e0615 68
    0x40c19a070b0325007040c90b403003401e611110350000c0003640c6801087d0110180510706114004c0113128206485289544821380400403040d8061750400541e900300149982c10000032409180c0d000302c1c2d000c00e01c089405000030100070000c0048005030081d4041105104107801800014030003500c100506605d403282404190f54060140d4028803c0403803410215000c1c04004406000e03180000c114404640c50003940d6a88010840782c040c90030540128640307510821800b0350020316444105007441c000c0c0f9544020403072204040d90108400103071711b200e15494002103004c0c20301000c03200d130354000d040c04040c98404018050500001d0220027400256401707c00e49001d0401e018500302001c040d2403088010b000c0c803c43c901d56444000540d5001c070008490382500554032900d0b88e03201100310084003500d07416200005400c10751500c0200380200c0d81075005644c014028415500488080d90005100c1a8403081400c0c0050701c01000344829000700c42c4ca81d40100082329401c070a0150000008228 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 780429433 1250 780428183 780428213
    0x515100e1302040b09012601020a020d080912191b080a0309020f031c120605031f021b011a0301150b09060412030306090c050702130b0301020d1b1704 66
    0x401e1003840c9100c215165500602804100107000c0f510568440105021504106081070060014001c050194410606c00c840c541a0141c8c0901074015912000b07541c0100b002d040d08025201e0161410740c1c0340b00c0301001e00343d1440d411459101c0e68210890003003021590304440904492100e1388440042e4081c02103542c040712a00340490788880c9400000c54880ca0b4580858160156010644c00078684a1074071039208210b44070b00b00505d4901580100315034903801030039050b0f403110300108013a1005103404549900940c0c005032624800c3ca628001c0c2031b0b00020307000c1240c0c1d1201450100c0300300030280c034114840d09400800602c80e500003503104244440c0716080901d400045c5c01c950b5611120129400381c1100706104038443e140d81b0700100100a188500ba031b10900d46119242c00c144140100c580e9160024084049090f40210f4240105050354505a1540d400c02254104002034000c1800008201c00c4040c0d5291a410014000d0014004828840202441000002206002142c0390 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 780430683 1250 780429433 780429451
    0x11403150115030b04020f310504020d0222050907030216140f0304030b1f050f0925110d081e0a09140606030d0813140a0605040515100e 60
    0x718610400c2c041e0700510b14491050741040c00011100d200c40040030081000c071210007401208442c0034100f0902e4800709020410203040304c61030400051515030050155081200001403a2400291f1480c240a008400c071810f03243c0009000c012920f48846403592064050409601d401c0300c00c1c0143c5c01d4000c001500070b01d40355001d502100346641c00c200441e50350804800b01d0341e4558890900c01104907044403105a400c51468811001c4489040c40364129400906414540319070714003044000c0740c00510b03052011440000340000654213001d03151070b00303a69403a544100c109050465081c190180d41c290203101c80e01c2c09000c104900300944040b85e01d00e2a803a0485c03500c82c0ca440c0d102074440b510001d0300c0b00d551042c1146a29001103120780c01428118102d44540c2e034101c1c015961002e088440410a100c1c0c03c4040300403e00c0402030300b000200400c2554040034040d920030703080750000d903025902c1d940801104203481e5a01c070880e07900711006a403051040342c5030440328800c680d4000c0407604 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 780431933 1250 780430683 780430709
    0xe0a0b03040507170304150e010e0402090f03010507030b01090f030308070c030306080a110907171611010c0512130b07030e1c0e03071a0d0b13050a050114031501 71
    0x901405000c4803000e03241014030006004040e4050f182c5c0c81d0401d02405402d0359002c018102154040d01802c0003404060310f60b1881900503004210094001250482d044100e00450721080c1c0d07002c0c80742074402c8405403400502c0041010004100c180aa040050032100d80705d41440880e800003040c0740d0042040c134100042c03429526086014082d5036000300380500c00c55402208018604203101a40481900c140c446a61000000ca40c0b403500910310074011504140490038424030315440d0840a1f00300e081c100311841c0300b00006401c698092422000049000c501260303803d60840d489904003095150080d2403c115444a0001c00d8010300f0305424560303a40121100710400380001c010440350048515614000850003416403400b901302c2511a002e82c1d1004160441c0d900f803d000d51100c0c01d1446400c02c82c03000422030050080c0c1800f15803080c03205441030b4426245001d103c1c4039044c20840403480b540742c070360003402040d05c801e0031602c240c000c00070f1243c040e40742d0364803d41100c44804a41c2c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 780433183 1250 780431933 780431941
    0xd2303130f0302130509150f0402012a140a15060e010f21170309010c0212160b0a0b13020c010501060f0c1b0f030302210c06040f0c0e0708070e010e0a0b03 68
    0x10b8600f1f0040c46d6034845842a003c20420754030144210284950300070b0303d46200d80700107016040c0c1c061400d111445074214400e004140850368401880f45d22039171000071250441999218410300c00380b443d13001010355803260824440701e464654060f0042261410680c0e545043c2000c9403450710080d0aa044440d00b4811654103210318000440541c510f541c3d00726984c1d0034400001c40c00b0344003014001000d8458090b080c000b0024403c21207404102c9141c50304a040b0859440360907004d009441c08200c142c4800d5401d11617651003d501e0807042903110016034550a103004182960f00503407000c01403045685846011a400140c21002d15900200000c4441510f42da041c65940041d044617018010300351021080580004081c4484040e0704a128540420500ca5640512134070208007001e4120101003800500c0241c501051240303c0e4400c1400c0503101c01015000d0303401225480000742c550f0042c01041e94010510450004003880d021000d055a5070106040040901c43d103041a40004009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 780434433 1250 780433183 780433201
    0x60909010e19050f0412080705070b0405011103130b01050f0604120f060e2a0607140a08070303020a1209170906120114130204060206060d2303130f03021305 69
    0x2100c44007461001004a800c01d904038940c00007040705c04468100912855041072400f50b24040d10401e0300d6a00c0364501401c0f5070b2040642900508225020745d00e171411401890482c4000c1d61207612030107c0f1071141009030901030b0140d40c06a0110b809030080100d40f4000ba200c5004172010b890b440400d148035400707030f4681000c0c0f1408011001c3d01c007a20341101040303a8100411184003135440840829000d40c02d0092006c030640d0491031541e404241045104002406e00114568088015040d281100d10a49604000f036000b0702c0200c0009500050340c540740b9410120a15800901000400100d8400e54420a0030340010145140812020a40e011315944600031180d514084210016a9503528240c11078401c1090885520411501400c800c2c5c100307892003550300f220429401400c25466050920214540103042691000c0c044461034011b0205124002190050ba800445c0d03903c1441340700c841200065084050814114071040000d42da51072841004078510510004a5864107086 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 780435683 1250 780434433 780434461
    0xf0604020c0a0501051f0906180e1606050a09080a05100b061c0c0e0306040b0a0510050d14010c050a0c0b06010c0507030501020403060506040c0807140f27060909010e 73
    0x200920f5582840c0401102e010301c0e05548a0000c104400c80144545820600080d21090700848800c0a0890181c00a004094102c801e42c8050503096078000f085403142e89441d81c00a4012070b01081c0009034440b001a40b01403014014141c62024105601d882c0d43c0e0309440340d2142d40340315802e0351500e06001080d9519012a00c800303c241c5007540e8080011031140f409004c6032020400030841d08020f1a807607060200c2e4545c41070341c0c0280200015a510006d80004010180c10701c0801d071004500800d5a88810710f1741414140120403105044800b101c656082d0392100d061642000002d001d480d046a4000b11014082980060110880d03601d160040343c1c2614002c00103022845504000014080190b00810079203001e50741c203010581e917a03402e00041c3c88501c0f41100c00120581c0004e415140301c9e43e0130585402040c0c03500351514030030b50441300c51504910410405042400641c0e401e9400070366641048020940e01682060090710000d40702d801c0500c61050718040340800030790522900d06d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 780436933 1250 780435683 780435703
    0x10060e1f05030f0c0901050301050f0a050c091237030e13021b010c0806060a030c0e03030a020705190b090607030e030313090b090f1603180f02030d080f0604020c 71
    0x8031001c010024192a44e111104542e040c001c8071070400200c0c0f28101801f42c01e101c0c020f080044209612030b1194070f001048002c02c0306440b1001440700145950b50500c1208008287c41d000300020420041d0030486058100c01d42c0303420151203141d01c000c006400540120b5a82c0606117581c8414030000450030a8212513020101c0f07900c002541d07a810058000c3c403011039030a980c02000b400407840780c01d483e03070071050b2642d9602090a010f9865010701c280c003c211000c84500d0300318034041200c00420b00e150480f82c420b10142c1c00c140000c0c086410001480c0300020700c3d568040366254a0220703c05494450b1940c40c2d4003640e400a215010b15020350518a1105030242c02c40e540d4600c840305403405107440d80a1011001d0511101440601d0039465080c020462110b02400d15120058444410305200720241d05042e107a0b10500074004408c425464664083c2c04078001045841c0f04250910030555515001d2080c1c0e0410702c6a80031001c0d1803d130b40301000f500d006a0720341200101c5854644c80b49 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 780438183 1250 780436933 780436939
    0x706110301151101020921030d14092103150a0f03110f0105191d06040807260d0e010c0b0a1509020a0804080d020702120a020310060e1f05 61
    0xc00c0d641c0ea007401d50b405542ca80d500c1146016241e1510300342e110305165183c0c003442d110b604400c1229070002c6007003590000c008482c07410100fa481d040507513840c8807204020040050401030300301d00c180200e09d6640d400421f241d001c1c0207482c0301f1101500000d041c1c00f8a050105010215503190400034102800d19001e0a40a40c0d45d40d2600e0060000741100440c054201c070400c803041540240c054600c50b01d00c41d07030300c03402d00c00c0983c10494032000412035141c100a070074001c410b400e0300d07000000c0c4080e2032104042d24200c0d080c8642d4841e48030f03907008101001001c201074211440e5021958070f90f403401501e00b98152050210040b20075505104000c0c01c1748540c031060080c05a10740c2d206c2c60213a15a04030202c049039444031001c0480c000c42c40e2401c042050080010005440100103004240c40410014100710554000c0340e8039010280d007040d00c5038007600c0c44009500d030130042005100071148042c032031030b81001e000c0e548101024110341800b003006018001442041e0001c03c01401c400703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 780439433 1250 780438183 780438187
    0xd140403260313060b01050306060d1104090f05060a0506040f030b07120507030b03070b0a30060b07060b100c030f020708011803080f090a08072105190f0206070302070611 75
    0x20070043d42da81050200c04440f19403821800c501d043d4051801d6921544000304010b05207000302e01114045c0c6503070411a03050350001c000100e40343c03813648180b01c140301e1541d00c00900341c80d101c420b0000700030701c51b0003541c4212020f0200f04903502085400340103895008401418079250514256008440e90300c014403817a082504009056070725512003e40d10004900b00e505107969585a01c00c82e00c503440c15800020440d01d117030340315215004100d102e046420101c15117509179002c100310484625410a101c43c41000039000148201c40c09031407206030084403004000511650081c02e0443c1044004007441054480f100c81c0a0007403100300003c083d4200240480c0c01c0f403107945000b1030850241103010030001e101050900003411203c40c072469561008041b25122621036590a0304110300403140104440511144c5034181e044d4800d01240315211f464480e413218101295101844180c0b50801600421b004203044c4d0004d8401e410400e1401e005a03610103c1c01d00d83c1c040d00d015a00c4007254000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 780440683 1250 780439433 780439441
    0x305121305150a020c0108040816050f0109030503162618010f2301032303040f0603020304120513051207091a0f0a080606040213121101020d1404032603 67
    0x500e80040c52000e20f280e096507103242c000d400546100303905035405021180e05000c3c25401006401810942c01c3c042c2c0115840305107010304260079200c01c03c0048000034004014809040c00ca00c3d02c0d80c15840490a00d0146107400b12040201c100c45d480e1042c4845400b403020906101a21918001e102c128500910601031070f499640060305c0c00404003220542e48200c40c14140c1031443c8014145c9900c0030300003800403001e519581d080c1d41e11480010300c500040000042c106074030890580241107079107000d601d91410341011840b01d00c0c07550001090110400102001c12091164101034a2080780d4100004809c629154070307101b0150030036180b09180c506c442c03041c41c9200704c507150404002c80c1e1040b5500c01c5e56040c0320100101303100e401c1c0c0ca5402080468000d02d01a0007803c0d0111945c1c455081d00ca540d40c42500c20103c00c00001e81e940601620004240d59062054808480d11424981000382481c560310b03003a40710f5448050403062441d02c03a8280c1002429602000b80c5403012807544900b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 780441933 1250 780440683 780440719
    0x120c11010f05060102060601051206040515060a09030b01050604030b190618060f1a03040605040f06050103031e0f0219050a02030717060a09020f10090803270a0305121305 75
    0x2002d96405000d440f840d00007d10542c485c0d8202c541c00310300760200c00001d454401c1403002400c00075004050b002ca240310b01c40c0d80e6440e50000781004440982d1010501442c50030700c0081c402e41078102ca4003c00e030820040c40801e401c032500641040e007001c2c1200c945d034084c007542d00050800790058030300882070510404540d2140d8010324103640e2403190071a5090350340d55050700d4416a11051a650030024800117000ca10305070b000303c1d4420302a507103400c0001c15550b01d050440d0001d030421004240ca01c1c000c040604103c10302010413052038180000903000009010b0340e12990250724104132920401e41004112007800743d078400c50381c05000c548034540c40719203c9c151041003212508161080c440050400e180c07902644202c940c028000b9401d1404030000d00002c0d1003107410190030f002c1c1c0c07100d000950358400c100800c00c002035544448004030206d0001546007514240c090300c940c100800074004541c0101d40f851681038000c2c1482d55512101c810710b52300c152140c0c08a81e01aa0007100c52417100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 780443183 1250 780441933 780441941
    0x60702121e0717010b010804030c11030304030308150301270c03060203010e1b04031113151818050606010f11030a0314011e0311030a06020d06050102120a120c11010f 73
    0x2e10000e03c800c42d400741d03440d520743c03ca0b031030764540c0c600081581000c00c001c80d004280548a01d4011a5400c0100301840f0100346103070300c03951040f000940388004203c001c0e034034140500080c0804800a10501c48400c801050040c081c5086a0000005081e2607080100300d454030002154800c1f0300b551071307603582c1d00800100301c4103e5003034801400d00c442c41c2140400040840c0c080c0c07940f044c04a0380c1c07a02e1503130600040134910340760302041c555145500f00c658503100258500500ca1203140000450b080071101c0191024072000040085a036101039000802c00f00c0d42d250301081c00e00e0a20741c3d03108203c0341210025107a06510f4820b000010340c00b8007440d4590440c0614000514603001da0340d1b41c40940c3d020552400c507031484600c15403e018400140d1055400c154000010102e59941c2090744840c0102c1c0e012501051400f55240410400ad50701032000140340701c0803405560070408001d9020b055494040342d404d046681c0c0b049007441c414060b00bc3c44c9101409030f40204100ba0292010000074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 780444433 1250 780443183 780443189
    0x721140c0f0316140a050616020f0a0e010504050718080601090c0e0609130b0316031106090d060c0c080c160911122208040303090602010209060702121e07 68
    0x200c125004660307a074140001e4020b0020003001070784a955103410901030750040460f196a9100700034580018840e0303203000260040d41941c4407a410a0984c41c8100719001d8200d02c401400795000440c01c000309080340c01c0540c110b0340e095901003100c1d82c5210003126401e88031a80180c480e040484085802800024a54161404540200004014030006803200d403d00c0300130320b6100700c04201016513420030301d4146140c6100c0d0380e00490070601280000313040c502114600c061032848914100184107a034440303100c8190068940a28203100d005c0452405003030440d01600711500c1308074054560b0321443c01e0310002c5420100303490b1641c03245516240c6071070600d1801200c220400741d01117002c40b11885980d441798081c9100614041c5052080300800c0b2000b00f08550708100981e0341800c10a01450f50280385108154040c0e0703640c1180f4002d08030400b990000d401b1a031050000c4011516220704865480340c0444421460051641c5150301d0070b003101c0c011614480b0441c0014000354400500c05e829 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 780445683 1250 780444433 780444439
    0x305090a150807181211131107020f060406080f090c04050118051e0612031314010906091d040525210515090715050406080a09050721140c 61
    0xc511100310100c040e6141178000c1c2c0110703183d08044040011030f8501c401d9a440005080c4003200c45003c194601240c0d002e161500454800181100451130300c0d01081e101c00070304503095810141003800c002c0c145c980c010500c50840e8000004910145410001c0c4208200d0050040c0100e41e12040d0b02c01885044840c2e80060504040114007004007194844c5902c50020301c180b08250303542c004114402a5501040003e800f0070072070380d86040d4604081d034002d00440d5000303134801c070b8500000406458a581c40348040255082d01807000c401828024410104129034241554403103080460400760507000d040046c1c9800441030280c010702d03180d54411610702485c0c1107032103d000c0b1442c114003002d901d00144160041500500c0c0c2c4c255800080303420545030000c50340b000781c903032400c6501c000d09500c01d038010a0307020608224040e0f0010313120391310402c1101c080c001204261754159941686005110003002040c0780c6000707840701c01800c10590b80c0c0010400c0e8184001c240c929440b603e100d501640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 780446933 1250 780445683 780445697
    0x170709051e090408030c0d051602070e01081f14040f0204060602010e0a02040c0314130501050c0c0d0e01030f090b09061807060c260c0c0411070305090a150807 70
    0x1000700c01d145a1059004003074440b40c00740c2c0c2d4580e5240c403264401088201c0305031081c04400080552031003424820703400d4880341c401c050b0400c04003070320b0451142d200554404858006011600d00850507c100804035044441c584902d4100702020745810000215030603005004c210a20802d0102c8204c42c6000341c608010b1661200030413800da0350311802d1002954040d503089070041c1010303404120101c0051078006034035408000000c040081c1070b14601e00c000721030060501484028850b0903040412000c0300c82c039104112a800e0b844000514515041c40800d008103900c5900070303041590107413900b42e4104a00f0ba151310700380d0200c0030305441c10140c520071140080ca900480d0282140344404050062144e1480c0c03900440310f02c0980d01e0102e4011581030312070000100e4170000302e0a0710b040100d015807680b04a50205143c1728980c0c0c0302511450038050b101c500507151908540c900740d0585071890f0703194201800300c0c042141d80d500c11827200d41e03802494400a40c2c08081240a040103603282ca0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 780448183 1250 780446933 780446959
    0x2030d0c03051b04050a0e1503060c0a03050108060f04060f06180608101a0d050a020612150d02060d0b0d14070302191a070609210e010203130603050717070905 70
    0x540f6a008600529420440c0b50400b408884482c102d500d070300490b88500c3c81001e80d18000801c2c10b0032000d40d981c10391310101180d410980394040c003507a809000c03040300506c080d16102a190b0040c0d507025002070702c5140c0e00c4490080300503c03600401c014111851603009440740000d0314500a08541c840d402c0e80f0302035086504250303a8540238645002c0002d1003074040703142c2d007503003084000d0241020031109446400105001030701c0703000140c039440c800060140c00070714214060101d0000d8548040784036500102920b401070b030f0b50600741c850007820141c0010b8180e0b50500070807036070603864001800700000314000c40b006150000d01e10090b42e20070380c1c05842c0448084169085411603002e02510f00b581c003000e00c2e0240000c14094004070b401240040380c01200d5480d0b100303070501103841e2035507250f00b0020b1200403640c1240c28103881203803c2c0300540c58080a0b03451007400c40f259000d104e0406450f0000b00318030034464024600301d40e2503128145400d040801000d0039494903842054014004c106040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 780449433 1250 780448183 780448231
    0x90301020d09050d1d1e01110d0305180f10180b0f0115020f030a0c0623060916200703081b100606020604032a080c01050f1605030702030d0c0305 64
    0x803500991003d00030101b03444078020b0305102680e000000c5070400c0304240c4030ba204c044c800c00103c00345103500d8800003a01d0802540006035a45014025201a40030b0740700161400000511740703c07940207000707000945541d090860403140312545000b030702c0d042131507050104a00d0100c18160403a600281160f6048071200c038242e880381992107040c0f6041d0003c1c0000c6802034050494100306d40d00c11100001e080f4400040703c072134101010369415004a50f001081068201a81c0700b40e0032054440d20043c103070300b0410000b00004c110300e190883d02c800d4800076a004010405c03c00c8095544a00078941715440c81403000101c410748004016648612a0030121240d4180b040c2419111103034003402c82650ba58500b070380c4d288104c82c0401d1200d0145119100300c280802001e0312068451007289039202400c59513207080d210050001c19091401c0030a103c0c0c2c3d6462202044c14643c3d140c14420f40729619480180d065008200000c000142041c9202409941c035901041c03040d80030a1004030030824403034035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 780450683 1250 780449433 780449477
    0x7060512010e06100c05031209010f050705031003020409080f0703020f25140f0604090b01031a06041a3a0516111009050c01140a0e0105090301020d09050d 68
    0x103d0713034028804c10940c2d081c1070b03c1000c141412a00540499107061982407104981840c1110f05138116559448004c444070414000d250300402d503460003a003075080c10340c005440c1044901c0002c0c1301d1035407204500104500001030300c100c0031891402548441540c00c1c041e4681c0d01d034080b01c0d18280250038880c0c0040304650011501424900b20800c4080c1c2002c00c2c40410b4480f405026a000851150a0945a072100001c001406000781d000c90b41c1051040050151140d80070300708829610807181c0f40b5030f40c80310026182102c02000300800c013074402c2d401e44403143c4210262107540b918070410442a44620400070955520b940c0780101802805041420807602e060741e1b9000b45007000824802c24034899491100d0f419074490680c3d81e01280c0e60041d000719002441e04840f20f80010980304180e680008000c00946d0800380810725060702d41900030402110351000c1418440c0120741d80c01591425415102075500780c0d04200180c16150514659850401000400140c04812003040403461030300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 780451933 1250 780450683 780450691
    0x6081f06080a0b041e031b0212070603021e09280314011a1903111518040b060c1914030a020705030115060c02100c1a01180c0c0f021207060512010e 65
    0x1648411184411f07106050a80240700305a034400d52240c00c04410300400e10a00c002007a00c0e40300181d84c0c106040000304078045240402240c98410701002e0459210096140103c244040211074070900074000b0000e8241d660300054a80c02d00c100e64502114015030045410b2100c206498034a9a40da0b01001074000b4421038850f165620f5038000c0000038245584d42c58a00030040140b0504580f820f1001c40700d400c2034a120642c0f070011449403a0300d0515220b02494408240c03092454980c10a954540d144260640c0d41d284c07180000600d0300380001c42e1a40b0180c03941a201b603a41e984480040255107010340d0040394480d5282000d1100c01d0480306c800302c41162150f449a8441d0000d580030030003103070007031115103061020f401a21030005582c01c4091803c1081c9000106a07541080c240c442411f0030001c8029010380b070b20003559082030b0020358540d185a0f00c010508111217452000c0390aa00c0300405d800c03810b100b68403001c01e41e80e0300040a8000c4000b80900303050542c1c3d84d1204548840b1082d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 780453183 1250 780451933 780451937
    0x31710061403190c110a030305010e010b160b0702120a0201020c10051e0408090d0b1b0a0e0f180702011a030706050a1b1b061206081f06080a0b041e03 66
    0x10a0144209903540c004d14241441402d2a08403000c000740214100250703030380100c000a40d502c005100400e5209040d038003419146075074504043e21003000c1007100c032600301c020f0514290440019074443c402c020001c00c02c1d512000030354079910b1004029001c0c0d00800143c1d101b40c010074482d0710007200103229141c400d0800320808070900219602c7c1c180884c40180080e40c10b40010414446282c480550350300c0c105d0b00c9420f5074103803840c240c0455480d0070744101c035070340071030a0401203404810389c000b10982c2d031131000b1901c0102c25054400050b8240c840d0000303d2420400220810031850b40640c000380c1c0c0390310220020b080f8003071030404054071800d560007020040b82c0b09003c0302002511550700042c2c0408680c016000d0518103884005584684046800d016080c9250a002e4142d000c0000c0032450101c00c0107120701e40c140902d07180c0381c2180000c24031503014054a1141022000d4000000a052070f0050700d21015090804060480f012913060b110040001c1410b40a600714141c0d200e40070341c06d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 780454433 1250 780453183 780453211
    0x30304260d0f1b0f0c0305070606080d020601060c030e010f0c0609081306050f0a052209020702040c17010b0901090320100206040c0b03060607020918070906140d031710061403 77
    0x1c4c01d0956001d460804241d04001080c001076000441500c2104080e000c504000c0ca40b10110500003490001c0c140c00c0402041100c140c0f610000782c018800c01140142400e201c071f4042d074104002c8441c18440203003d8540360a120341081801208030040103410b06c4941e0a101c4251503420540c0d4500c54006641007400c1c0070420046d525209201030203644041d1081d400c100318000b04500d40207041504001c981d203900051001c114030380380c8903400c1c07180700d6810002c1038104140024103420005104c1c10380c0d500340c00242424140c1c0724946103009075074061080e024041078200c12001400200d2181401440840c0703c8a114038000140244a0b0b540080707100c00301e0781484403904d03403a0030251100340c110005201100060380c0f1040c1162023850355044003c00c20003146070707203440c0014660104050528007841030000302201512030204400945d1500100031441c50f044030488582c03030045100450784d00900415128035000701c030482d101c1d5640d4150b60809980348020900c800d407014001d06440c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 780455683 1250 780454433 780454457
    0xa050a0e0a0c0306180f060e06030c010f021c02150c0c061609050402071115040819151b110c09070c0507080105010b120a0905030304260d0f1b 63
    0xc00e03004851082c625190120b035481d039800140c55446084d8070b10721040e1740c407845000c0c0b0105151082d00010841e00141c50300a0910501203515401d40310070709810000c0d44644001280d0080040a40d42008150208009440d51800a464154129243d0080d81c00c0d40042000313074403a00260ba2a031004c044c090907240e05c8072810000000c0d0002c40c00c01c28001d44000020340c6568600c06449410b024401c000e194085040070030600d6a20300c82c05860000052006004004000645800005888050000540060a00303010010744180c0103c0c5183c1403060a01243c5c1c0c800d0285a5514110b440d403002e00e080004844d82c47c1c000e48500c20740c01c0546080001c81a51051000c1401d81d4003507015035030901c2e03d41c420302d42960026040050f4042c40041c0e401d4500c82d00782e103070035400803940c03030200500301084d80c40a4603403001800c007401c1078020040c0001c60464040913803a030340f07110000e06940ca1203501058000f410758404010001e61a150a59414402503401c0010140703050f5030310307a61200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 780456933 1250 780455683 780455701
    0xf0504050319120501060801060305090a0510020d02070c03051e190803061306090518010e070e09070f030f200a030201050c0c060c01020706050705041212030e010c09050a050a0e 78
    0x82d40700018080241450248110040902c1458082c00170303692445265818004040e041e90800360441001c0d91251400c400821004250a44025507030700e000b50740c414022640300f01901402d5000303002c003942c565002040010024410300c130545070b4070007a26103014284e100c0c0e8581c0c144011444088480c1e400400c00288403400a5070310444c001d0001c0b0b101240c1001d260122045904010301ea15510814016481c0e80f41450200c0c4092940090206002c098100358440141d072050100b01c3d412440810f02e03880b400e00901c1c01806204a01040d0701d9624100603e00400e0b407882a500c0000c0e2130394a5820386007901c040c864205e0050100b020306403956004403000d610070010144180501c0f0410b1403070307540e80030092400d421070000240c2c0b1000203040040850354060321090a02508020811800300710703c5040e200319400030403848126141032806d80c043c0000d03107a417181c154600b1451124081e04003181005a035003e651b052072490b00c40003031228001c130358064000c1c1424040c0c0000c0e0542 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 780458183 1250 780456933 780456967
    0x7080405030f0f070f0c0f09110d020f070222060518040b060301022a060f060a1a071e14010608030723030724050621012d0f05040503 59
    0x41400c00b00c610f01546500d030070000101d0140708940c0d0305a01b803001c1003106840c000c080c0180440740c504104caa40803000c105810320800d04800140c540103d681200d40418506591641350064400464164151804d05034415011800550203180500205d00d41c180444001480c04184c94002030a03100c0340c03240400700c1c400509007a8199000c0000f00b45905c82c219228001541c6c81d42e60300c50811446211a00b0024024204107003c1056000c220587da1840c0942c012190000880ca00e810500300760300e40c0c9842601d6002c2d1042d4a44c014888141d680140003480a900490003104c4610a01144034240c4c0c04520907081c044e40140004e0b404648040600d40c807064900c4e41c20790207000e90441c01429074210f07050650303010032815040c4803506000031020120340482d000400440c42c0c110f0000d0170300c1d507520341e442e10306030307804495807800107007d512071219002c003030f8218502040c22900845006200402e010695030804c0294580d020107402101e01466005d0003440c00c00e104040e0001000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 780459433 1250 780458183 780458197
    0x1080606090a03120507051c02071503021e0315040912120608010507030b130504050d0f020f01090602090109080a11041119030911060a140d02041703040602010507080405030f 77
    0x10955038500000010305044c203070900b20311030b03031500ca40792200e41c00d145040030f4819001144400208004104040d8082140001c0c0e41d0f142c01c82a1000342c0700e40c0101c0090040c031b218401c1017822103103400204004000554454280d10f440f01c604883c2d51014441901d58800006000c00c0e4420080c0b2045402400860a0900c0075400040d01c0ca0340c0318061403d40346c0035249200032980d41c0005054030300700a5011491b914008c0d10038040e0781066520903a5918011082d030341004000707945051014070030f10110890070703607040091068050343e05010000b035109417119804200309080001e040c3d0800310300b4442e050b404c4076041c08030b00c0b11103007442302425851103a41e0101c10200301a031001c84c00310504418240542c0da0018080c1001e180c08082041ca00c0c20040c45071301d052004508003680300480340c40585120020989505000000002a0149030403039003040d00c90703800201036810008003800407100240c0c000c0c400740d110980203481d1940280c0703001e400c6400800034420f2554407c40200340c0c1e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 780460683 1250 780459433 780459439
    0x11517060102010f05010306020a090b04150513051206060301053601090503030a0e061e0402010c03091d040b060d0c0b0307091d070e030f0a0201080603190302070f0b090108060609 79
    0x604d00c1840110000c580e400d030411188a07601140300c11440b5070001584001c0c05c907000344c09180c5030500107034841c0c0c509038400d0403003000b03c00100c5080e04048400b5040040402401c01c03121110046d00e43c07621010100d800b80d0080d840d040c006014695004910700c450061041891645550600c3e1a14100100d05080c0c07002d640310303d0940b0003e0001c00085100303421300c582c0010b20117891107049081c140090316024000d81000d050000055014031170075045542420400f40000092405503622051588142800030f10001e03031410b0f072600c1604581c41940f05501900055030b400c0304212400c2d0012070003a08444c0300309c50074001e20100d4801950451018184541740c1e03513960654141c0c4900e0a000300c3c0080b0b58402c1400000e5030401d012500b80d0004401030070305041392401065a860070b074040030b410401590049402500d0500c404ca01a03100c0c0d004105604881d41006075545260b4403849080c20312494001a11045000945545000503521041103840d010b040000365000202940c4c1c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 780461933 1250 780460683 780460691
    0x18010c06020403170706060b03040209061e060d270c031b080607030614030a150b010e031203071403090a0b0a02090a03031d01080609270601091401151706010201 71
    0x404105802c210013510444020041d940300954a041d01c151210750740160580c92090084c84010382d100d0180981c410426070f01000752a503144417011291101d9180136401c00350020f1f20600000080c0c004120940b11540803041140038082801c94454800001a0014281160500005141d05c0640c5030107041036034202c884079183c0003114213040081e220600840d035036103410050040e101c0c00c00840210110054444201c103a112082d6101d56142d60080444c0d850154074a00d07070103210702490400020303003200c580c0503010104840303c0d07009071010030100e5a019200c6040b03544da0000c580c4610000d40c0901050041e070b540d40c075100600030b0f288155185d000d0048042a0301c1d00c07601f400085001e030396590051070704042656402c0d146810250b04101d501f804000c241d0325100c00d1550007900c2d446070a1003502003442c03206182c3c4507800d040d00d00d40c058400001041d19558100d4074200782c0380512409a44d80c0c1c0d850301d5a8400c2d1701485000414141c01503110301a400102199200006000104d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 780463183 1250 780461933 780461939
    0xc080d1d060d2a0e040e030c07051012060b12060a0b2505060f04150c09030213060f0306020c0d0e031b01210509070803070302100c05160b0a1118010c060204 69
    0x40900054145080003078080b004c444483d1805000e2000651103034005940303464201600c0b80e84a07020b80c01554080c00000840007440d520800c1400b0005454520810001d1749030b40789981c6582c0301c450000000703545900856041e1420812502c21540c5c64880300d460040c00700c8000e01c1142c481003031100c40a2480e0105404200c0501c4170a00c5000c0a4120b8540fa10f403d03c3d01a1800e084082c0000307070380d45442c0b0196105da421480301e80581390119012160b0380030000b0407402030000d41c6c014600c4850303403520020070001160083c05c015107074203042d260074503031039101101d00c0780f88003c2056060303000c4003201e010f003a200101d8851054042c900080404015017055404562078500e40c1e00c055650801c100f030203901440090060407841020754608400ea480096880000005003401070799100710390482240920129a90003902010401c002051420110313420030080f81e10310bc55905201590349004100d40480d003804142400e03a4a400c8040b03801120782d08101001141c00d01e900304404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 780464433 1250 780463183 780463241
    0x23070302100f05091218062d030402060f09151b0f240a02090d0f02010201140c0412050f0102120105190b0d0504050a0c080d1d060d 58
    0x40504902a0300180034240340c4104103001c54000180101000b8a8071090280082000c11521185402d00c00c4060b11602140341c0c01004030203280344070380d10040000c0d00304829070400141040b520722004a040d02c0b541c0503210828288000c0324001d43c030034420411560054441c001802c2c2504d000fa1905003c18a5800036200540c002d40034107152200e0311820a0350b148041060400700319450303016102d0959105a0800c020500e000b113001000040c0c0c00045980000343e043d102005801010382e1840401d90401c0b40d08a11000303801d07801542041c90a034500100781030040d001d01007501d8034cc0d14042c50311101c0c1045080500c42214640183e4040000c0d2800900240c2119006246c0c9041113500d844d0401020324a480d0302d00c056254440400c02c403203084102603e03192007041101040f6980c80340f403c181420684c4500401402c8c03c0d44012441c624002781007144030515454002c00c110443d80803400d0800c0907142c240c1d0143c003c01448906208a41200701c915820038401041c5003003013511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 780465683 1250 780464433 780464437
    0x204060e0d03120c03021c09080f03180a030915022e02090d060203101509030303200a0207060305010609080c0f0a0806190f180215040f06090812040f0623 68
    0x26800650089a5104000b08207d00301b07100005076241007222003200d9607001c480c0c0c01389818024101c1008000203d00c0f07d010199200315888000a42d2062405407401800300348442c05030200ca101c0208610110900002d40360900d0320900002c0c01003c8110421912690303592050703100e03540e03001c0c082040706132244007081c00d8980c4101009600c92421020342500706046a03c03604a006141c8a004102900f0490350000d0301c2c0c0515002c02c20081c803551886a000c84440d190350111400500313040284c1d0b0205e1980240c90040d501401640d0f80c402e000c8980c024113001e0b2821a800c05c1c1407005061400d0740c481003120300060010350205659800b110b003003803012607a01184040655541e800800184625201c1101601c0208481c69a9201a81521424503070007806000c8183c220307030511a400701501c00400425405e401102c1d00c1e41c40040640340a48601c1c03040384a4440480181ca031701105a5003520500c040070002d0380c0c0ba09008489130344070418804d480071500700c2005010720810380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 780466933 1250 780465683 780465701
    0x41b050301060f0503010c020c0108040b0919050a0308090d142d0c0c01080f06090a09050d020c19081c0c0f060618061a09010201062409090204060e0d0312 68
    0x1515180d1079203844c0c00e041c20b40d03600541d00021034201a82c0e944850f80c104003041e40003904140c00e055603070703038041c9800d107030a00030400c010b4034003407401c01c803c204030340001d00462551203956040b195455a546080e9601f070b0400b12a00890003245440784010000b80c05002684c0da41c0035000000146074625050502401d0138008c0c0c005c2d000155402e140e54100141c40d01c2d03071800c0c604003500303240051200508410150141c3d22418a8101040b14240f00b03802c400e20741a000404d03100c2403401048041c3da00c0903da0a92405075030154203070781e4000d00c00300d084011200f1a9010744980d580c590312107254451450807680501c01c0c9070300c000000c00c5242110520030b620070000051620b0904005211581c102051940ca250a02c80305000442c1204010084c100c180070010b0740710060140140e014080e2500009411004000c1c40303400289641207003004954980c079a004516220601c0342c00342c1c41113000f82d074046008014508070a040407090017903454040d10380808181445d80d0300c48241e8802403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 780468183 1250 780466933 780466949
    0xb0f1528030c11031903020c0322290d11070501020a080a0b04021305060307031404060204091107110d020414100303030e0c0a09090c051f12090308041b05030106 71
    0x44a02c10034540c0140c480180050b01500450502a8910045072004200c1039404c04042d00421506c0300c0780c0041094881ca2805240b25201c020f090862240b0011601d108050702d03510340b8090041c1d005d03035260070940440c41c1030404c28540010140c0a10103020300500e000d015440422008000c030354284041d09001c1d0741035507060300e01d051010450f17003611508582980328a2041040c1101204000080d40481314103640c3c20b41c8a5954a10560041c001814101c00d0740704480c040000f0003040750b00510580701400300c00c105500c1202e030000814010340c04010240b080500d680d000030300e001c001c1d04c91f98601c01072011528000840c41d19030300c8217040d2015045103003800d1080c010950107008174040704039003500805142880c40006002031001d03200350b42645a4407020304089c000010003900207084040c2444203030320300b2140364400340082444030f00300007040510154107281103030140c51401d40d0907076680d41d07050725503403540c115103031102c8491002035000b03590029903a1800e007d031310300410b411 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 780469433 1250 780468183 780468191
    0x50f091b0a0e01080f0601020a1106090607030c061404080a03050a0207080a0c1101021b0103050915270105191e06180e03042114030f030405010b0f152803 68
    0x2900001d0012107001e4010100c105d840000c1000a0340d0009010120325006851425203070602c001140981c801d0400381074000c04002200018590800504014180704500401c8800951150559022820381c1c0091084804000c3d130781c1c409119800c010340054202400500d03003401940c48000d158004680c603030200700c2d0b401103501803204003d1030f80f091500071700103020549401600f07440c8102074800305a043c143d0328404141241c00400c181d00c0c80401c0c09100684c00d01380307001304028109600000002d00410206d100d002840b0601071f6038002c02c0e100e401c214007400c150743c1c0e22025241c1d155072209456801c8600290814003401002c0003031800f4403914002c000034070042c60503143c0103007686405034401c120800c003070707107404526072000f2004981e84150803080f0b2810802c2382a03000300d000480d11020aa601c081448500254000c521071402003090564040c1031108007010a00320950203002843d640312500e410307100805d502084042c003690180030000d4174640391201821010002651 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 780470683 1250 780469433 780469457
    0x41203030509010c020606100915030b03060c07020a090207060948050907090f1509050102160501030f0f090503030411010c080403171c0e06010609050f091b0a 70
    0x140c801c0e01d8100036070000a008880b141580695580d0010f44401d009116075407451023114400c0200c4000340c0907526641c5c40c03152021000a020b4901c00c60418401c4c0501d1000c20b02e070081240c01c5510706a800350400040d43e10780040d4030001c0d00040c81c20399845854128080c0011f4600c04140900c00307050000080300210f0002d5803c60704168411004108201007000d031000c0c40c503003195811501d00310f070301444580e1590000c4402c0b00c072030b91062083d061035840c04503802c2000680c038800c000c00c69480c84042c0c1c3d03a0710012170362886181c011903010181c5c1c10342405194440d13004240c0f800f50b88800070130300c00a4050030740b007240c41c264010303596a00048180000c02c035805140c0720f00c0c0502403800300454080c42e124040a03108902c0f006201501000704421080030341801c0e10071141807100c0c8501121f5900d5000380c0500402881d1800500803040049002c0c0e01038502507099074000707009000d1841d018414001d4a0070003030100c20340c0c020300070406107000e005c1000030010040166612890a40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 780471933 1250 780470683 780470687
    0x8040c05060f0708090102031903061406210a180501060306060504090512030a06030b04030c0b010b2a01060b0f0408010c02070e04060f1b030c020c0306250e06041203 73
    0x158100620900c802c11000501c0c60300340b010344448030f0700820402d5490201c90300507851880ba1120007042442180300e40b520540e0198801012a8006a031646a44404c0e604001c1d0390311900d1348074600c100d03a402c0600c1003a0741070184182d000786c1c03506002440c54014500d00e5007c03191500109c80580d101c4405004220450080a00500c01560180020582580c0d070303c1e1a80d4980d0100800c04401200060728440f0700c1d0490300083d41c0080285c074035070800703080080055107104001da403d0b006020001407002025000c4404000455200c0350f1000c036030121002d11a801003808010541d00d50801081c560240c4008008400c101c0f100c2c540e68514000c041030075620b05551510642d00442004c109003500b01101d00e42c0143c0c40100041d00c6000011410020112070140101c6807442046441d5115015840f80c28484081d030215880403480300c04041e516601203a4000008825103002d60011501940401d024052414418404500c80b00800c00b184c2007584014100003141c444d140a043d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 780473183 1250 780471933 780471953
    0x180804080c011806050304081e0315031902030c0f040f0606020a02190302130207080d0606020d0921080a020717010236060d110c1e24100302060a0804 66
    0x75618403c21225a45030800103003a50000034000b51540030b0020f0007207150f010321001d010101540b2140c4580702e08001c0121005c400c0c0c000b03a082d02074400c014610045410407000b8075400d0b5801002045050540800c0c48602004861080d0300301c0e0b00e82d00c6403c44c44a0754042e4a001d411030f42d0052000c802503004000c00f1090742c699010303060040c1e00b41440035886206014401c10846440565200200d203440d41c0c0e01c2c40782e2261601654900803011940c40d9000c9072440c001d920716600c003400c150321020502e000c0444481501450400d503007070000001c64840190100c00003900542c0c00d0a9034804814403128505006c02d10103950008080f0540c11005080d94400c802c3c052a41130460207069440121400c4c03540b5562150764040780044940340b0582160511040d081100d03074682c0783c40c4170181d0761140001c0c07400d02c4220400100c5820150000b80b403040c1c2c0c00c0d007075170a20f050b072241000461f40d207a0050000582481d07003a00c0880540c440710010094410b565503042400e2425087c0180c1c54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 780474433 1250 780473183 780473207
    0x3200603040b06010e01140a02070e01090e0a020d050a0f0b060108150609010c0213181e0b040308100f060c0b060a05061c0207020a0b120705030c030109180804080c01 73
    0x14200034818072000c59000000c056001d002030805140c22045400141d0300040000207080b020400050703124205603010903100c04590085801114990300d0300300c1ca006031071614210610f00d5000340103050252070003e00c01c8028501940c1541c0c203054241c0c494001849007858190b503045001000d00c0002e5902011140d8000c1604040301c0b0050048400031b0b070503104203015181081403040204081d135645400802000f003002c24100f1101c80d100c036916003024a480c605a079101040b2415810508242c820b03901e409030301c441014640d0f41c45a600350380721030b07000e810004900d5920202040c018000140d6402402480d15015060759951500400521b00201494041c000b60351040143d0f03140c41741030f5010070a10400c500d580341c0b41c406d0340c24001d00030b085c1c01940c40030750344400054850030301d0001c1103215042c0c0034800041c0e50301c9070181e540748003d4510244004080004006c9240035a2054201004045804403600d1482d201d400141e0096003041446070401a0940019030b0410180c5e160 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 780475683 1250 780474433 780474439
    0x11131404030e0a0e01140102010608010e07141f120e0703150c11030d0e0c06181206070801170f0d050a0906091206020c1f0207030e0d0c050420040320 66
    0x1244d090140700c04400f0018401e600300d10700c950710028050b038002c0d04000007901030b2100030441080201000ea9546455124040d558086100b590f0300c98145030303a1801080700304410003104100007010031500c40c2050440e400181e0369034080c8000341e020a00c0200001d40c0501082d02540d100c210300b94080729802d84600d014060414170907100c203c404800e48012413801a8000b541c012520920f5042410809103039a10000005030079080f25071100742d4500009041e64401e42c000341c070388919580c8150540d040404601940c00400c4000302c0c00414201820050081e118100046c10205291070f0a02294001150000c2801c170070982d8062040740c001c2805250000e0406d00d082e00d40c2c82ea04400503805090709070002001148854104042c0070782052106000380c1400e121030184009400c0000c0450000700e0b004c0c040102442c4c04607078220201e8014001445040c41d1404010041c0780307002652150283d05503030503402d40791135406880298041d00c1d84030f1085501001c68480000a5040588 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 780476933 1250 780475683 780475699
    0x10f140415050c0705010501080f071505070f210c1101052b140a05100506030103021f0318050a021005071e03020709020d140c090d11131404030e 64
    0x101e1604406011500c1034460300040585408580c04024815084098595801c1400000701c1300c400040881040c0000025105034030345440d0f0194903034082900c4000012001c0c4100c0c000b092144048000d2180b02d10540c0c0c49001c0d5407241c400042008811402c0843d00000c01b035001d01c903070041c00f800042e00034a0b14600e00345052085954642611890051000c4c05810f41844200c10383d014043c0a010a10004410f2070a4004140036007c1100c400020388554200000c0a0a014007074a058980c020403201c0020345d50b0101e0030b4400d00d8480c41402700758461401011035100d41e15072401d4607001e00301a00d420701850042c410b400108180d140c0420108100303070408204048410140541107030411000110a81800c074600541d41c4c000e103000920015010031403101d9a03000000c10541d900941c0300aa40c0d09401f1201c50044007030140d04a020000b05038001070210020f81101080101240d00780707172000c000c4204540000ca000060202507038103210505402500e600c0f00c040d41110400c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 780478183 1250 780476933 780476941
    0x20d0e030306100f090308030618090307051006180e1c0e010e060a08010b030405100507030207020f01020c130b0604030c12021e031c02101a0a081501050607140a05010f14 75
    0x17000303903000d44405000800080b020a48549d00c1c03000c1c51020f641202241035440c10100ba0003512607008003001c0310355102d40600c110b50150240a04001c0b680c408a80b91103095101c0a00805814544000c41030790103512843d10b5084120011102507140f29038810808485081c0090704003480e030b2100d140301e44403d1203002856503200d4a0a0305507840b2501490b280d444919201d8034081400284034045800c01d0100521590f0560140402c02c0c0201c581800c42070001005a80700c2044184180e00494941c80314610011503421900801a019145501d0f19603280c690b01041c000a801650400003410504401d502d041e007040e5011030700741c0024104c2d1100f03540000741e03175035800080b40302450569a101c14009000340000444030051003000d12080010181080801d400720017400d01c0790350100c2c00815419400908050403542104a59251341d0902d000c112050f0801c400403190302c84542001314005209006040b00b0303a114400209004503000c1014040d40da002c00c05845004001c0100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 780479433 1250 780478183 780478187
    0x31b0d140a1704080d0609150303110f0102041e050603070c12090305120a0f08160305060a0e130308011401090e0916080c0a12030e19080304030f020f01230904020d0e030306100f 78
    0x107807048032b515081c02540851000d092900700745401c0442440c070f500c0800c1c0014004a00c0604e0703e054800b0f40c1e8940f00d059120000c1040340d000688030100040d89602e40c0100183c00d1043ca89e5880c0054109188203581c0d9030b88461424402c0b114110091101180b440000c5401c85036014414106041040240c64102909035900450030040001c05031104040740060302d4030342c0790901a00380c035007030100c0714944840c50041c0c4000650084000a24450000640708580c1e25402240c61050352020070543c035203059003041d4200509440c18038081c1e1142e00f04000b40c0e240f45140201480307401703402704807205d508000035188154410f401c0c8042c88441032000035803240c202c09811108403170324455404c86040224a010031030b086407825100019022052021060141008501c00c032612554075a5510045403070303c03400c03440c0c9030821101c2c80c480210304200d400039101041018000509040c52181003100f80d51807200c8203c03951b0070000500c036a030304119086c140b00001508200b09950303000b100c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 780480683 1250 780479433 780479471
    0xf31050c0d1703071b113f0106050d0506010f291812250302150307050c01060905090c090115030c0e03010509031b0d140a1704080d0609 60
    0x1c80c146402c00400219031900544100e03032105c03c0444074035041d11161a1000011035101c0041e445840c80d007202d2008206210402e241c0707014115100c02807148405c4191408454a01d140d400075500c0c4c00000c10140c40f140108249a030060004040d154500408040481d00ea60007103019600c01e92081c0062400e21a808074213080319010082d5204641e034000803412404c00b10459001402500640c0d100030009890b0302441c04600d103404100303c42c0101e440c862400b620000750002c64401320850000c107580b024541c00f998508100d8a000c59007803006003103891b035800855143d41e480082c060301010405c008448101c0a803031100b02941808031807a900c3e454917240a00b055220700d0010380c010721903820040102001b6009108a04081c080541c40e0382080c03a6060341d0015038180c22000070340003d018820780c40030782c4a501014001c0d8145200943c020300481050026071003901030201c0700060110b00c02e502966000d6200da0420903640b003174810b07562140c0d145900f81103401d0742c0c503121580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 780481933 1250 780480683 780480713
    0xa06051602030901140307020c030a0605161d04021c060b0a080f0601080a0b06040b0f0d05130c050904031b050c0405070c02030613051204060f0f090e0f31050c0d 71
    0x1580317640700d13920044101e1402c60303014202038040c001c82e002041000100e4101c1e50242c400e40000035032140121800300c6107005040d1145800f200d401c0c15068985c24998010620b0031201141d103040d461400140300180c0f007803239108120403030000031800c154541c0516541d030000d080040c0340758141404000203104240c041c011400d52991040c0d259010759410741110000d02e015030406807208090b4121980b01e0b088400f110b2911401c200005a00c0b1180e1100c50705440d900c03011407905070381040305101d400c20380200b0803030a103e15000c660280b544801041200240314400030841c501b00328080c001603407000740480003400860f040d08801640c000c01d01c52750008103078410010b283d5060a0007840c1058014194070001c8001030041819a480560100400d82c20703202c014565001c11800c843d00520b80c400c040c002941d400105600030f003a2010203400c842d0504500290300407140c0c031035442c016010961420100c1003580b8904002d401e00243c0b036072010840c0d44541c06052511800d503032400d032603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 780483183 1250 780481933 780481967
    0x1b020714040b180601120e01051605070507031511041514030108030a08060f06070308010602061f0510020c09090a03030615080103030c030921050616050a05070203010e0a06051602030901 82
    0x2400044c90b40e4484c0000d00814007450500380007031102e00d502c1c1402003a045e03503001d880011034254142c02d94021400c6800c003580c0070b4001c01c01145140c40d050300412003080b4083d00702d6107038038000151901440143c4081d1003480e200091346821a100a0104a00c8000c5028000300600c010420741c40040155010b0300702074145040c1960712200001c00c0c0c090120320b0960f001d10040313507000502d41e0044910b410796505408071603403a2982d8040c07490a4580c80b00c16040714000040500c00d07070500440560229103203004440401c03103040c00240503000115150041035001e044a0000c0c1f40e8140a03c8000340b50f90f145010041440c800c00901c2c0040500015003882080305d1500c080500c6015001c008160001c14005407401c102213680110000078000e440510403000460164022a43e0209103c0025141c9500d0982540c5d015550780d00080c5040c1ea1556070340015101d500e00a01080c07803000d1180c240001e881c42e0030001c0c401c006c040e01c0c808a00710751080c00000011b07604042c209045440301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 780484433 1250 780483183 780483229
    0x120c0901153e03040b04030605100e04120f210e010c03060506041401050c010f020a1e0f08091e0a051606020304031112030706051012170307031b020714040b 69
    0x342c01d2a901d503204c1c80d4458200304100250020500400c2d512003030045a541d001c0c0f5982c11741d100c1002c0d4084c04140c50103001500d520200d0080e01d8040e1001c1d441d2241a41002200301a000040000301c0107e042d02003496516401403088044081c49110886d101c60308080040504050200e0614000c074000d103640c250714450140c41507800780d0141c402c0901c601c402400112401d1289002075000300f090800410072101801002e481804101c84164090382d48000b208290b005040b24001009402640039014003c20000c0c80c1c07030400c0c05019610f05034001003246039100c0ca010b40c03420518101401080181da0014000b080d404401c560440c0d4010416032413080581c00044d400c090300903804d0100c3e200c0002c41c00200040c0d070f0000d902c658842904620b5003903494410007803441c2440c0c1c000b46004007050908840403100300c0a50f070000318900d000203107207410391f54880b03200d00b005a0800159004a030104041c1d800d64240e55414141030390280b1100c0f43d41d20100b900c600207450800c0c201c000d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 780485683 1250 780484433 780484547
    0x212030c0f070c06090503060708090309091f0f1406072003030f0c2104060e0d0606050a060c05070b12161211180d050c120c090115 58
    0x904400c0e1001c0c1d6800c0404003407044d507101000341200c08203100d650302074041c200014000c540280902e5100e222850051854003140300e04212201500400c0c502d2071050b1007070034004800588543d00058002185151080c03428580a201004103c10009108100400c402c400080b1000314800342c90b114408130280070303200540024254042c403c2141420320001c1644a400761001620400012814925200001c1000c40420b103c0c4034030300641c40840e60f944020000350408903130f04c2c3e80c014010765001074182c1d12403000445144803a840100090103605201c0d0900c4028800c0328020032400c6c10651600d080c90414911040740200300114051418408807500307409403000d001e05003545401001840504a6400650b400102001c00f041418161140032814259980c1c84c0c0f0300c1d080710080c502d401c2103600b00f04038100001d070000203c1c0501001c03c03105484200c0f41c24042c0680201401e00a01568001803901c001710300140c081e0030b0480c600105d1042c000e0300207042928840e441c1c0703501c00300f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 780486933 1250 780485683 780485707
    0xd090e090c03060f061306061b03140408030a0809060f16020f0d080a060504091e081b0607030c080610080c0c030403061506170a0228030e0d0212030c 66
    0x14492801c16010301502c1c2c200444138296000f8548208001c030b40c078954902c01c80c840d500071645d15008a401040d500c080c7c802d0701001007007003039409038441c0c0742020100d408000400010707003140d48180c060f98400304030641860b41140c001540101504010800c0340b8028140088040c1c0140040b4803440c03d0700c0140d50301078402d0008880c0440a802105d812900c81d0700001c0540c4400c0720414003141c502900070600f40b529001c0c0c0040a44c111005175201807604013603018000342500121001201001a4413020b0704030600440109044005084035103000d200140983d00328240340c00400c40c0510800c900c640d101d14450312451201d252450099540103c5580399108000c80341800d4803011070008100046038202040a04880d83c81700f1801d50342d804295940300030b108010207c40000c1d40016648695070f8042e0002100180601c8039442166803103c1c54001c41e1202c0400183d12040003d00c130407020400c040c1c200c0200d05c010a00c000a020701c0031200c2c00040e0412004550018460744004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 780488183 1250 780486933 780486943
    0x204050a0b0414070e01020d02030904050702070e0f1017060a0509210403060c0f080406150504020f030901110a022d0708160e011a030a091b06030e0d090e09 69
    0x60301030420007203d0000c00d000000800119000c2d0001811030340420300a51001c120320f00b038411280c00075818540e117042084007800c0014240b50071446208000a007103d46866640c0c0664403011800880c2d040088040042c08850b400c1140c01c0f001840c000984000000b031100c5e4040451280040d0540f14903018500b04081d0b1450b03215518881d82e107010100014a00600440b0702c1b40c40f080110122003142590601d00f284100e00c00b0413140c07030000340451845d4001c0310107603814500314001d49031110000b5080740c11820160b1128803000c070403c10003030400d124905e81400d0021284c3d052107800c4000950b41c03500e414803c071881120007111182a48140d18200b568610742c000e4030103040d00c80441c150b42d078280c6107005003200303110000082c890121212139410317500c038a10f03080c4200403100c038043c55540c0090028180d4507500c001c0c400124001e1441901c1ca0813508508900030b500d426001029a4034200c601c50325900484243c240c0d0f6500001c80030101c402e83d9440c0041c035520080318074205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 780489433 1250 780488183 780488201
    0x151018051c0305161b080c04090203060106140f181e031e0c060406020d090623030403121a01030e190b130f030507021f0807080c09031b09061c0204050a 67
    0x80030099040417195a03c2d00c00100a4070001c4080b039403125103001c100802d641201401a402d0340100f00140300051084e08141000ca4401c2030075031510106c00c9009030740c4d078408044000d8107150301c1d640c4101403900c007452541c001040c40c0502030401810000a40300c0c41c18001c0c0a41d8013415140d000320000342880340700083c2d9801440a5100c59a40304c000e03441d00c0c00502c1c4000068800e00c07000c20800d006000e40c000400381d001408032170700c00c00141c03d00168000b5100341c0034080301505c0c2003801303a0503014041e40300c60409424081840201c0000d4290f4030145280011608040183c880c1125507140b030550441c1c0010f0000364a40f6021071041e01c1c41c4100c1009000c402000c030281c0e060581020041c102e46100b500d010745007000648035041180d50701c50000d000504a100490041c5100740c118540200d2907056480c80c11814200092600d95030340c15002180401907200c0e07405143c540b003080c0e8003132401d584048608040381c038090702580e0f840360001d2040795150045203400149904c80fa5034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 780490683 1250 780489433 780489443
    0x15060a030f050c1f09090c121d0d11060a0c03020909010f030210080903030403030e2d060606090a060c0c050d050c120c18151018051c030516 62
    0x21481c102c1c14665110616400518001e10000b003c10b0701c0824003103101c00580e00242d0304c2840c102d04012662010f00300c140c1540042240c1c040400c0384d000398500c941042c1c42803904c084089141c0713082e03255092000108221003403042c12214074141c41408030300c1d19448104903400041d2484090340503402800342e1510b40fa0403a0a0000201e201140d9100a0043e40e00844601805206805045440303080071aa51000340c1c00910101b030002e4000c3e04814841d4440c20f040e0b0f0740300c071416030908500c0d106030300101d1000800f0810310524554240001600000160b0f0414600300112011030300d4004680300f03440421030483c08440502019451030005410010500c5061602d10300705030f542d03a55284801ca104008c020808207640301d000480c80b100c084e024100c100c80d891200410151b8841c024809000c8100044200843d03580d50384201d00c25156a448600110070207864504038880c4e00e40003503015800455400d5030007502c289285940030350600d02150f0b1110014180814411481c0c40101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 780491933 1250 780490683 780490703
    0x1314061210030302010b0303040b16061116020f100509100306091107030210090201230f0f120112050703060f0219020f12031501050721030c0801060309030215060a03 73
    0x28110101600301d00480f07000e84e00900180312860105904d034071907840341040f04002004080030b001d1520380c608078a5800b0310000220600000159000e9038000c00181251107030f1a41c00e64210315240301c00d00d13904030b0f00f51402d042d01804080b0151141c41081d891a10035060b140314580294801d0f00035601910019105101c0c40141a01c80030290f0880603040b0058050301c01c44038416001403059010780e42d0140d5900c2107280035100400710701d0070760036a42c0c04449800c01c8002c142d0281003004040f524200c020340ba0307542c0c200403080c0c521844183c00400d9403030001c00a500114a00103600415260048400a0701e00030342d04020002303105000800c0203c40032990111006900401d41c00e487c0d440180c11f8a52003034035030346600750341e01c41160a14002a218840101254030590150147c4c9200e00500d01001c50400c00200005103011081d00000e9151100c0d0500241d118045500401903800c09100011581c1e0b40a51594034061003000003101c090001900c2ea0307a16a001c100079034001136060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 780493183 1250 780491933 780491941
    0x302030714120a050d0f08060a061101060803130504060503061e070c02130e19020607080a050405060309010b1c0f02010c03020c220627020a0c0206120711010213140612 74
    0x154a40f500c40081c0d60224590320341160086007c0c034003451107060000c00c0040c0241c20900f05645e031035800407418240e50359a031000702d46210100010203500350084410f4100e14501740c2000161401e0b5042140260425428003d100b0910384200c40054020143c09440e66940e07601200d840e1210303030002e540014002c2400b0380c184c0300c0b68014040002030105590200d55515440041d290a004000b90030103020841e480110b10840702800d4000003070f1a000b85001e640340002106a0400d84088415955815011495240c1250f801d84940c4210701d401e1020761041e241d0b2422200314402c040d040c0110350440c5c8003003500c00d00000382d4078040245000c00a001e06201c41280d506170040480caa1840c00c003020402c060f4400310380180091421400041e900b84000c044040c2d00051200418000403044140040c2e541501405905421405004692400200081c80711040344001110703644104400d417801e40c0e444640b2f005560743d65100d0503c403580d44010801901c07440310500510400d42c8184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 780494433 1250 780493183 780493193
    0x80d0b0d03050304060615091a1308030c16030b16020a05031b01050c0f0f0a09080703060203040615051302070809060313050609030c070501080402061b070f0e010302030714120a 78
    0x80c0d07001340e000314400c0161548030800c29a00d039040710340f0342000c240e41c810100300e0311201002203220380d99050001401d01e0050b02003801109015040852980c0001c20300c2d4003142c60800c03100c187d540710324241c00e10141c07131368403031202400000e4010711081510842c0703641054002c0054210081e8490102c0f03503102d03800d10020f421808100b400342c2c0305500300404100050344000640c2c880004074000a441e01c040300c84403000e83d91100300040c0074407120300320010b941103081c008080118011103025944c0d24082c54000d0071580450402050b80300145000d2205071a01c945410a800002c41e00690b10f100600344000140650f00d122940f08030004108141d203590480e002a20382d100c0c804840c1281c6a82a42584a0046905401b401d910420b070030061588a81605030700240082e000c3c5103442403912007210b501c9005c81580b261a0300ca443c04020304411081c040c001070000320701117a003550440d03000907210395141c0300707008058411036a081c03c0c40d03813585010f20a666032507080354040e003010300e4070b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 780495683 1250 780494433 780494437
    0x5040c0507320105010815060a150207062a0602030c070819022112061302070c0608100e010b030c0f0403060b09060109080d0f0207080106180e030c0307080d0b0d0305 73
    0x34102c040440ca81002e81409494140c80e03a10015081008061440e50700c1d8450040c10707980e00401a04001910111305184801c9410444d4054078940303003040c40161003982e00c80180140c1016407003000d0300302c07543c4202100c1c2c0198852800b50303a03915090301c00807641c05881009000c2800010b4031008850b42180800380341b48280d001da601c214a07000c0b100760500038007030b03c83c032001c54108901c502071a10444020b603c4880100784d0541c00d00c1840c0c441c1c0c126004180100d82d501d117034030700c20301071aa04a00550b074407072003c0c079400404504050b60425a14810310941d9000d12011001c82d0141c408801682c83d4140c9034014607486551361b0402c00050141c2d20003d501034a200360204e001d6501c54800358040c0c49207100181280d519080c01115104d101c010564218020f950003c84c1d520300c20f0240701d0040c0302c2102c50b81c84c00001001c900c400c40d010044100701c6544100035100308035802102303560035541c10040060322030080000d4034000e40403c403042c590001d10540e01400701070700540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 780496933 1250 780495683 780495743
    0xb0a1e02040311030102070215090301110a050a030e07050612060d1218050612040803060d0204020310030c05031b100201270b061e040b01020a0204062c0f0105040c0507 74
    0x15030070f0780b82000051600700e200b40040039400418010715450b50145500040150180140001402e1400701d022100d080d04040303103000c005480001c52410301c66050140402002d028006440740f02e1825000034464401e5151a0300b85480f0200010320307a58620354641c0885400410031025604107510081008803180c0095188002c42c06001c07640d41000000e0b5484103541d0340c0031008507200c5449101031900700602702684261106402e100603210350000e54002c004c6412460315580c110b181a450700300303194029500230380c04044109262907806c0ca25000100080d1481142c0d1001c0900480c00b5000440c8940156500c10008031a8542c070135210510313035401100c40308081e40b1880b08001c0213550b80210402c0034070034145242d9a502c1c155120b0406540140100c40b10900303254003040c1561010740c0700c000c540c8a454901000740c600c1e14441d10203401c034161000f107a4503000e203098100b0001030082c00e0003580c3c0d4001d0b03000800d01400c1111811174215080050240c4140754070801c00143c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 780498183 1250 780496933 780496943
    0x60b03091c090302010c0312150e16050c0c04090c120803070f03020a12050709090e03041e060f051c0e01090c0b040501020a15150803071b050603040b0a1e020403 71
    0xd90040c1c40e02e2041c030060b001e0325416503038140d9296071502c04449001034903140b4000150350f06071941840c01000c0703200000b030240a01c40102850032444450680200301c105000f803080401081104100c0442c0006910008480010b502d454905003601d840c601900000f11072034004400d58240021000518811142d96684900c10b0502e000200c041c1d015403402240400d06034800300c100c003c215000158086410b00e00100341036503507506a01503544058516141e9040001c062108080f0140d9201102507264a006800c40c0350000040481ea5030000040400c01c002ca0041808800311081900000f01c0c5401070055002c010022030080c0000c41080300c0b860041c60b000034802c040001076804645058002d004003103166100d003500071000401070f0317007001e0740e81016951000c0407513007140143c02050000c68640c003503450a041076254085180c004800c2d204810095556202c0449030700c0f44d0b02c0169a40c1c0344e01d6071800c40e0040e100440604402c500c1c15089900e403804658003070005c030f81c020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 780499433 1250 780498183 780498223
    0x20301030618030f0809030c03122a040311030c040c0f18180e0106030605040b0106030605040b0d060b0a17030903060a0b0108180c0d110906040506060a0c0303060b0309 74
    0x802500a003180c076001000303000c21311004011302ca0b5401507024942c0030f0b082105582ca0280c800c0e01d41401c50380a1800c407680348014500384100ba21103003030306200c1180c0c20240c50010085030500d01c0d00e180500d100050481e41240c44020941d01c0c04d200410758808050f000703003c0c0441402c000750046507000184000101e1800700e08401280c6419294111224800c1107560351801a00440207014201c000117900c2d0b499450000009203144111885540203d00d400d0350340d414048014107481e00740e4082032186081c84502c01e1030b507491071005041103600a000090703140c0c3e118040303680390900780d014095441140e6103541d44041c000c030051880c54001c03003e9806503a40d1081c503504541440072564006008400011b4040720030818920303440075140c2c110344401c104c84c070010304080d82c10907040381d0b402c000e81c4900c44582841c001c003d410140480d0240954034107100441d2403409408110020052039a14480034540aa4800d902500c40b00403030b6960b07403a00400080d9100300780c0034207604402c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 780500683 1250 780499433 780499451
    0x50123010c0816050304051302030906090f150a0f050403120b0a1d0601020f030307030c1707120f0906050109020a080f160f0e0306130201030c020c21010914010203010306 75
    0x200301d001c01d00541c0d00c1000141482e500302000c907003074505040b08840502c0104400300302a541e1500389440300017600005684c9103440c50069041601c00b408091042e842003c1c2c041c40c01c0d1000c41c03440d59a10070318130085a01d94841c000b0307001804a500402510500e08000d2100307040d48803000a40103908080d00384554283d0348117108000c0802c0c800c4030b0320750110700c2900f4410555181255008041441261020b601424407141141d0081c2c0d40030b00420b03a52400b800320390750403001c0105954070602c00000c941c81c004030064012020740d100040403aa0302c42d044004d006050384044001a0080f60400c029a103a00190000b94000c84056011824590001e03c0200c0c0c031900d00c1e441080b24920b03401e00c640f21198180d400f200c1d5108040c3c01d2121504605600d51400c2005d58032a0040c444000302c2d0500d40d00000d421240034912000841d04041040d40c510f4444408003a00c3e2000c07004d210341a052002c4509004001c0d290b001031136800d0962624032607600540203141601e024110410907034071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 780501933 1250 780500683 780500687
    0x33e04060f03050c0d080903060115091208190909110319050601022e05190e160513090c294b0406031805071203090905012301 56
    0x1100d40b02c020010360042c00c00000a00700003c0c045c0d44207104070021030030318140301d0010b41454401d03000b42003000e9035070072190209944014094000d04824216907031251090b00c441000c1e12546840841c1404c1c0d0034040902c16104008030001030800002c204100100c1030051000c9602c1034401ca290050b00c1050700103495000d125003806000140c00801205412140c46120782480b10444800816909c140800c050070a01407503200300d488a82d001d65201c0303c103000304200c420403a2a040d00d070b030000340001d40000c1700c0c9040ca401e9030811200914075840340100c80c00030b8259170b00001e0588004d0380d4006201c496800c800d5508000640345070550903191101507443d8060200402c8003040600408120102084061285035010000f4084152124444100007022088000c41039680009040218991610482d941d000314814904110780151322403d07601d1105000d011b03010001b6144510800d4002c00c0000c005020100c4248280d603034601000c49405240142d10540c0d6124005240d640e40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 780503183 1250 780501933 780501959
    0xa020610052b050a0b06120d0e0607020a0906141c0b010918060c080a0f06080a02041e060f2301090b090402070605090a0212070807033e0406 62
    0x60300250101400007075848181000c80d0400382507424011108004001143c0103000044009015030161007060520805100004210301087c20003074000c1d901a1109942c041c0f234550303401e10202e500c40c6d103d16160000031401e541e80d83c803140d945c2e4a400f000140180940c443d100300700500b26103500140741d15a060741c228000d081001440c1405100040c0f20903250b0394031903107031703202d21440f0140070b0b41e00350b9504070459019521007004106503204200780300c1180d0244801e0f1040418080c007000f0314001c031482d6a43c280c0b1000900c180c0e07c3d00402c01c487c1c0c2d2800c510070f0f0700c542d0600381484816a00e00e0301040c02c11480c085d0708034040d0762814042182c1c0211710b104151020607510480c40300d00d42107116007103402c681109640a5000c0081e0310210342c15000742e6000d500c89201401004115204101c60648003900d000740135000710f44100903080d000300b20401102c2e04144040b002400755203040c451200d5075000d5003440360304038040c19203404103013140301c041e100166420080d164482e00703054070329 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 780504433 1250 780503183 780503189
    0x7030c0f0b030610140a0206040b0105030c010504030209060f030a0f02090a0e030a0e061c14010f080d0c0c0e0405010c020c0303032403210712030504080d090c080f030a020610 77
    0x1800100b002c114141000064180000ca840c640401070340040000d00c82107901c04400100164014824003080c402c15810079401444210000c0050500300000a403c901a52002a00ca150014001110b584403020700c0d81d10040000c0541e031000c540c0d46460380540e60800b60580c002c010010001f00070352028442c0d140307010b171060020750030312940c0340b0215440c040744008241c10070024010411115100c030b0301a8514803058101040d500d500790b10569000c901607002400242d1528400c1000001c0071800e55000f44451808a02c00840c030300340070300100788075070000790a003403000104000d0103410350040070300401560954620704817500030183d5038041501d000450904102c0d221050341d140c4030000c8244403014064a0b52001c01d0015000e078001c019807444941000000c042c0c0820040f044821101c0c0b20380d05040006040075151201c4078010008a078011039074484a481c1840f4400149100500c42042150b40720f00402c11030701d450381c00c10368100c00540710310404142d100414060010039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 780505683 1250 780504433 780504449
    0x1508090c0d0b0702120f041404060509070513030b0103030e10090302061b1903020a0309080102040f230904080c1905030f220602060402011d0d030f14030907030c0f 72
    0x8020080c0c49440b00004050000810b42c803e0031140000c040341c450140912090004010391030760b1034249201c0c914080030800c28840d5250a074203100c50b541c5c081845030000c4161400b6901c0d8122084409032a402d2900060000c030b0380800000101a0301282c0040e40900c00e40e900e07183c50046140c19907a60743c85000080d408403060055940c02c4010800e000c1c0c407043c00c0740407220003c000752a00b102804100d50254010f80015090300c040c1a002440d203402441d00b900210719181c03601c001c1a00c0103415026484000d002c40040c07400c09040da032035034031292030010400701b094281443d140038658402945010180a468007114812851a400c180d07510b8001000c1c525080d100840140c140d8400120b03007558103890a081140c240da03103603510b009014982c00402a500701400054040c1102120340d010030550760f94440540d031190340452110300e5050614920302002003000351500c1440e44281c240d801004000c1002d9050700013100c03c1101d0069041a045988442041c040f01c5014010482 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 780506933 1250 780505683 780505699
    0x40b0402070203100e0705191d01080a170f1210050d1707031b050d080c03092a0d080d050703020702010207031e0b091501050f01021f02070506011508090c 68
    0x415400e50045000d00d00d211051b0789455807204000b9000b410b08680d4030000c0d081d914000e00c00c3c0f40429034200d01081e0300070460100703980343c9a0f181e0740e250201c1c1c00003800480389022025540d05034000791400e010140c6c00312600c81c050040c6880704058201c1d80d04014607013041c400122414000c502c0ca0b805500910180d580d0701c04030140030100e0307000580440405c102010000c02040c80d18a00074402c83c410009003052500c82000101680d0025101c0c240c0d100f010824082107003030004d01c0c100c01072074050b1005450005400000c0320140c00c80008c42d00003198140342e104104800d00109403540f80704034100440d458a8001310200c3c0203001c00240540c1c0030840078408201901c803041c42040c01d07420301c1e4056849540e658030102c041558547e281ea070041003c0b401180c0b11070700d010302400013900c640381800301c0140003c3d9600c20480400c042115514161000c02d006601215141c40c1c12078226851541c1d20050b0000000d041015040061610030200c0c0b0340841c08200d2821201000385218 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 780508183 1250 780506933 780506953
    0x2710020a120c030c0c0809030a240f0b0609041a0415090e03040b03041704090f0605030d080f0115200307052b12090c060807020c0103090506011403070b18040b0402070203 75
    0x3000580c41207d040d40d0511800c07410800248843c0d1500e0609103a088101007070b5204207070041c0c00e4402d41c40040317040343e0030003a0300301c800d13241d04060b500c0f5441c0884000c00e5600341c48042d080001000141070b82c100c2c0c18413414200021049440380304030361081001300085100c500c07031261a4015402080d404010400100700440c41c6130080300c0000420942d181d107010b549014880032181e9600480d0501c0e030f151801041503150034004502c0c0d01d01242401c640c03e10b81440600d1100805009101106d9032003450603c000784917844003240420580c9641e490b6416682000e036072034114100455191045100c0c0000540700c4500c3d08207112000c9d1044240e12660000584006000c246c50010b840d036039506e8a408640709180040040810752a0b001c0750b4206240c0007030030495070f4031456041c0750810340b40000295000601c07d04641c010304400c00c1c040544400242408000d52141581c0100810300007100c40c2c00c40b50701b2808000c02c1750100042c0b030041090000784e0082d0b16000e903043e00454500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 780509433 1250 780508183 780508193
    0xc0324030a022823030606010f08090a0206040306090c05060a0c0f06092027010e0601020a140f07060c05100b0f0a06080117062710020a120c030c0c 65
    0x168003072a680601c2c0d4186021003c0252203058565030002045800711402c21035210702d20000d500da24001a40609003e24200c00082c0007001240030020030029800006a8040b8042c410440d420382d000701426990790380c9040c04006021140c0043c0d56120101000050707528018081b100c0294803601c038200544a90380b01d10581001c1543c05031003294960590b1000a00d030326481041003c3c8001140c0c00c00c0c11110180009803c0301d0b0121401c01060360066401c42d40000c10080c1100c034801039444c1160381350030040b414146c0061f001043e44ac1c3c1d1890340e5003895004120200008441000c4628466640004588000c003605c005070650704011200c180400490300056014507007c0e01e000089241c03940440c0b1550b03441e034445400103185100600551100e1b80182c44519a80b6004012900b03241c0c000c1c4680a903510811164240c005048449400c0300744408090b40c041d03002d007107480f11000760001e80740b00c8103091081c400c280b0300703110500c0d058082e00c201c0c2a9100c070355490003021204c5940e6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 780510683 1250 780509433 780509449
    0x190308031504020a11010b0405150402070515070504091a0d150b120a0302010510150c030c0602040306060311121c0504171e0304030b04030e040f050c0324030a02 71
    0x503182600c0c01d04000d954070380d216800105000b9040d40d4941c0742c40c01110750045e00b11540e0100b443e210300e09103400d20003a8114080c150903640800c4400603560142454001d02c0e04030040d81c50345250042c60308000316190030002401c121602c5400c05d0003c0411000340030040f2442c050095402031300c006c075810109075031426007400700444640008814040d800040e44683c07821611b1200c0c1e034407000c1c00008155080c01103580182046d28080c13420390621603104080c0c100036681c02e0400c043c500300201031610483c070032100c1a801501c1150744907160f00b410000380c0389500040c0c2d042a1a50800d51090030108900e1001c0582c1a02412150302d46445541d20552405105410403400307210210f00f1a18048180304c0521190008000412001100812800303420040c0d140c1608140420404110810350566100e540340ca8654a260070000000c1c0050240c85410341c840c03071920003001060120343c130095001d2210082c880c0320002c20488040203540c002c01034180c00d03400a008045c014141850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 780511933 1250 780510683 780510691
    0x31608030a03180233030105061803030706050406050403110f060a0e12121b0c0a1716050a0b0901090203120a0320090a06030c0c141c031a19030803 65
    0x7121150700e40590005010040404520701c2c2d180400d54980b0307402d80480320b000c003c0301c5d072480c8103504640c5084005400d5001e40024040d1100c1300c82c0d068899030742d043c422102004e80c00743c4200003500381401c116004110444044020a1b072058a600500000203201d0b51040d8a903002442c0c0381d90b40131045d0020f07000c10300d0070007014851420300b8440052030300b015051241058203001079a00c1c2a00843c2c2c0c8044840c8800c50501c401001410000c00020408260464120b801c2d08180104040116060b1069007892841044080b1403801000404a08401c070607028030785515842e250390340b03801c0c02c80d4a0144002d51551068443c0c081d20300310400603148544450a0010351403440c80034450900c1d0344540710001c0404009900c0c80189041c10451000e00254030742004042003040f0084c000c40220803000e855034411030040154064204068980aa00314618200100b200000075000d0084220602c0c10f007165100d0520084c00c1400c0611007c007810741050900b10300c0d54803003071040d81c4090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 780513183 1250 780511933 780511961
    0x60304020d0f05011b030f1a030d0f05210403020d0801151103070c080a1e031b0501060308040f062312090a0c12021906050f0a090806040303050105031608030a03 71
    0x205c0505400e088800b00c081700203401d450114100b103200ca100800c883e100d048480c04e4010100a280244d01c00080300000781489003840c49031180108800c2d10179000f030b00d850310091038000401003900c14102034200e010358841e80854200f401c400100b940c04c0e4000340500c1640f603000c1c1c02c1c41d1003210322603884c404241c690241520302d48a2562500c40483e200c0c0d402c1008540d10001c2c0180404c40034001516411a030861148074442ca142e40051120030f524440313048141d030030001076090141c01e40c840030045601920140da180c5e03460b4a107040800507071041601160318107103100340707195520008a4040400d003005528058070080711907040e010180c4080380503c00c0707031203560018003804801000707040500814454201a84100814660740c0c2c404004160300180080100703580000035100747c4144048095207548110104a03100040e503840614948100c50500041c0742d01036015905070b40c4103038295a2842c00f100ca40f5061525a4495000030b40e008000c240150340c4240c0c062511b050302c2c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 780514433 1250 780513183 780513191
    0x6120e031c0b120d120911091e041202070b0702060703030914030f0909060f09010608060103141f0f0b030705070f080c010c09060f0206180309030703051b060304020d0f0501 76
    0x2200882c0424021645940250380a654011800e940050f1701d80050740d20000184031040a69036819606030203405031500554089011032420144258450207c40500203414000e20341030400701c10318501c0b00c11660250042490100d400c1500078212550960007411841c60301c0019034003100207059003030302074411001122144201000a0000384042c00031072034843c1d11418a4010001c00e000d0181a25101d44880c0746c00c03600ca038407213074130603411600c403400c10340c0c0543d03a5100141c1c040c02c005030210000101040c10450314000f45510819101202c01401c00e10603258804001e0105850258100c12002030000451052182004181c6c2c40c0c4107001581410302c0382c2c0c4e5449015041007000803620b944820803040a503501a0030340c40141600d26007030340c4040303521074041d460b0080074154200c1c0d010300f1300901ca824103040080740c404210241c1160303070060341d038205540c072149078884042001c1d030100c2514000740303001801d5900540d00100b500c2524000d940d41d0b0640301080d010215030740d540b5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 780515683 1250 780514433 780514451
    0x10815011a071407150305190c0e06130f0902210603010f020c2b09050609030a050d0801062607030b011202130806090f0d0c0c05061306120e031c 64
    0x38503d04400340060724801441250f00308001925140000c104003020503207000c00308580c100781c82420380e402607540803000640c003018000c2103960300101c41e40e5a802c8100002c0c407401210400381d42d42e0448030344440a0b82030755140c21440d000e0b0302c00c4045468860f54400d204603051183c46101e02d40048000300005105013402440c00180d811207000c11105400c410301c0141101c12022044940705c0d180780d00c0d039680c040d000c503014250f40d185006484c09800086610401038030300f000414003c036005001c031107100040c0d550090400c607090103260000b91042280c80d4800010581e802d0500145480c2030380d4507a285c0100301c0042c6200d80e4aa81001410042e08041c1001c5200610b49200c1c000e00003400382d41020b90003860504041c00840c4290702240780c441c4880008079139807148207054a04201258104d080c1071420300700541029905c010001510102d02c807518102008403282034076043d00c012181001e130030440c6c8100004902d00e80007000940240c0c0c00e400e400248480182c0800220166 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 780516933 1250 780515683 780515693
    0x907051c0c090b0405070903050d14040911090316030302120a1e031a01080903030c13030812060a0501080403021c1103040f090e12090d020d02120a0b010815011a07 72
    0x107555882142c42603a900b0080c8401d042074010300f94407540c41c0c01d100403103a00c0c50340c4040c0e48040542d5120104085058a82d407081520b6040b20024542e1500600000618044e1110702c3e520101200b48648a1a0740303004090310394800403801c59806070040c00c0700d0818401c594546a014060300c4082001c0203140d0510b41400d001c1c01201d0a110380d4000038980b05403550103901d04074110320141032240f9002004003445000044036030106141031074a441701080d2004a00c00342e00350700010b000b01c8001c030313506102040240809114000458a8a00351aa01e200656041300305840160042e04080b0002440130000014802c89141c64586410b0440c134101103103080d90032640090522602c408001c0101c1c00c0309c1d01890758145408000b0342410040c07200020b2061291001e20f501400484005905554940d0050b608007038024004210350f05000d0280b035111034450700d04a0302910040c002080120002032501c031034034a550b901900913400d08480d60700010360800480c2c0c0c400d4003040b8000c0010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 780518183 1250 780516933 780516953
    0x4091203060611121605030417010506041a030d03050403260402090a050c07030f02070e0703050f070509030d0e120f070602060c0304020109140f0a1409010b030907051c 74
    0x120240c0d80018810b0a09600500f141035180802989600142c1c1e0343c00700301302c054111030790215030031031a41080815103802411401950f0110700301c254814520000480c040d00300c01d02c1400201d801300b000c6015603844042681d000d801c42905a484a1001034002e40245d0105401501a040101c2c00004110180481885041855010044840a02045040072034000350400c0c00c1510510003403800300c2c880c0d4400d010fa0030300941045803249000d603031340f0b000f402510064058038940002a143c01c110140242c50140c443c480c10b0000180013580c00c80c0b180003079174002c5a005000d0704e130541d445072040342c03501403881ca40749e4414035103801c104440c0401c001c04503504007031001401c11689480406418880c0c006c180302500b060400400005030391150803802078901660900021404090205001c1d41c002810260440c0b58034101143e031207a40c03454110103800c1141c500400307030b8940b003d100442c081602e101d544c660220070280140c0c500034800c0900e07462070203241c030255030194469003209 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 780519433 1250 780518183 780518213
    0x82a010c03111903170f130623070e0103060b03011e091b1b0f0b07050909011818020a0308091f0507140607020703030e0a050d08132102040b0409 64
    0x40003028002400700b68000351044801038181170004646c3c940f1210144110320000c094492582004042100304221544640c140104c45c00703c81c0c00b108080c103420940141e041d44e00b100854a03401240540307600c01c0c040d510035200365180180c01c1d6464080150f0003003c440000d0355100c41c142002048000c89807090b150402e141c410a901c00c15012880500205a184001e1180300104101c1c1c8021a0110b40340700a0183d00075005d16290b035513a241101c031401505001d43c0c0c040f1008000241c80f4070788456000910704c030b00c03400b00a80d017820012002071090900e0020740003c0003000810206031090081d10400d0005004130412442c10900d0704601c01541c400d85d000310f000401c614041c000d5640c4040038642d5100c0007004581410000070391341c6c41035848018100010840003400759146e01c00c0c1d55009080181811508081d06d1900040035004030040c02c42d81d2450040028000503c03410070f9452505800d00d00d119881381d5028040900400305480b9049038550b424400000c100865103448 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 780520683 1250 780519433 780519463
    0x31006030f091502070b0f07080f06010c20011425110a06080906010b0c1005060109080307030306031109190b0604030b040510060b130e061302030c04082a010c0311 72
    0x146031564a07206c8404ca90103041c15244c10150b00c10440f010341c101d10890b401606043c003140d0103954582c012178514219400040c600c0911803a00e0400e01d145100b01041c0200980b07541d0700412104e2110f40c01d900560744500a0042807030110b9202c404c021461415241c05080c5c0c0c020030100482c04555640c0540d801080020400c400b0850301074424042c0d039015200c0122042d00c0c186401500a0752014004280703590036944502044003680140780c220014400364058940762810b03414094020041484180c98100070134000700403038034202c56214494000c12144500d80b60a0000d01b0b00240f25545916402480070040840801c41110100d031040d0300c2240104034281d60800c1e600141c1d130103544401c1ea500c1003030000e00248196030714008203440c07907044100312a40e43c400010b00501e105100d101c845c070344000144214005614010305c1510210001c0700c3d8005908100360666040c3c0b0302601184c0c8400c0c0003803500f107601c00c1c5560440c52b40280742c10044103140103d064104035010900d490 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 780521933 1250 780520683 780520687
    0x150f030c03180109080a1206030c09020a02060f0c16031b20041413060204180c1107050a090525081f03020a03030804030c050a05070f0803031006030f091502 69
    0xc010180e40d00d5412408038010081c482288103980d00c134070a00950746d00340203204082200311140441c640c868401940c2003080000260342d502191002075115002c8400140602000110307441c5101c1c1c4518003030b60b00c0b03940403458800d500d402001c40e0303c0d150310202c0400913030075414104440ca540840484600a807500c00003816080c005e5918580300300c8640c0c0c001da01700800b0504107103a200034681c4c00b42d41c51900c0340078000c00c0e1604070001d114940081102e007407400411111401554080c40c2215019115508296604921127644e5042c41c03160541c00820b1220611660b1200c1d003101d50008164846e0030b07070b901880ca140041c0441d0105515002401500c10885010b008003604210341000c0190f201806003560081008640c0c940005024000c004001c60101803142a6203084142c01c5000e6074080d030101e1810079210b000034071460020300302204010078402404000c0328003c0450901d014495407420f5070079000b0f06641e83d581102e10360344d508548041203480e000102c2c06207003000016 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 780523183 1250 780521933 780521941
    0x5060606280e0a06020105070e06090103090c1d01081516031107120311040602030d05041e080705010b180a11041a0d0c02010c05030406090204020d113402150f030c03 73
    0x3003143c010751100003160706200510440d40c0d0032002e1800146003e40e0382a41d00c1d010400141c000d0005860028000070300e19800182d929100c41c1022810b01d804000ea01042e41e03600e41150b03542d51540d901d4041c103d8203601085800000c42801089241d0071f0501242561001c0c3d0614501d0f0009901558154100009680300d0380c1d05105410b01101e0000c2000e040c90309001000f55a80101c102c2000550b0fa0b1b4000704041c40302d510601c920240171500042544405464075054035041040e04562560a000d04050280b4140c00703400700005041d9902e415903516800b50001900b40f103469048820070030400030510a0307001440c0081044c0079080c4c5660360154807650800c0300c2c020095101164989a81c03562025071060807250051741000f4085008211400020000d00c20040c600040900c0e11005c01624049000604400c41e13041d0303220440e002030041d42c14004400580030000143c8200810303001031030805448020804000c88050400c3e00407807000380e19a1056036030015140003c0100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 780524433 1250 780523183 780523189
    0x215030f10090c0504120615240201062301210c020c09131b0b0d0c0206070e03060a0e0f1912090f09020c0109050a0803190203010305060606280e 64
    0x10700e00800c244682001594032581004006015a00078440300e5880c0d400020103001c0300b41c01c503044031f86500d55030620240e502c91080c40c042002990340044220303400c400e801041d0061184401f2520383c81901e1307402c0342d403031401e0010780040c00c118581404032980c10302403c0d0840780c14016100c2090b040c0003600340307080d180191600202d80e88240c850340c0117804001507034160074641d648190340810012010180750480943c2110a13400501070f100d00400c10f01100742e541d07000b8210345603858003542d40d40e88400408480101004050320740650004010a11110145d0300800c4d92041200541d0b90407240046c2032401c0101e070100b01c050740d4010300c8480d4140324910941181c41e04071401c081008928050000110000340d01c641c0c10f8851b80800c2a43c8641c200f0740104c0da0305a400815100e40061510f451031034ad40060b6008075417408400ea1085080015108590580c0d4000000f880f050340d99104000266005002500c4220340852140101d91003000c42c05050103500d8a520115100d48418 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 780525683 1250 780524433 780524461
    0x16031101050f0a0e240402031c17010602030c070e100e091023070f05090d0b100501030c120513050a030804060b01052109030c070906090e060f0708040215030f 70
    0x4c04c160342c010080c960805162a21500c0c0b10071078084104000f0742da41c0c00003a00300310320784080d0540d00c0b619040c0700401503486100044580501305103900d0998965204a90380d0040c0c8082e08095440140248480c030780042569500917070846680300300c00d889140c454070000c0242c88a0312180d00c02e00700c00001c40e65602440c401c09100d107a20600f911071080341c0380d0702c01c1001350000050000c1c010aa034030851040d4129412490013070540c10444009140854091804850000d01c1e0101743c20040748540c485e000d07061080e40241c1e241d015000800c02d0340c90050201901c20540c40054110b0030000610a00c11000414000d4a50b0845490141402c0e41a9207070ba050b503504000040028402c200d03030408201d92048585507080c140b0346d035514092441c6200d08424200103118403072000031181a0341d0001c40c183d9610041c10b004005e46c000d0b0140e03a5031010384061500c0500600020030061003400640c4d0f105000401880c80040301190f40e80b1031780c1c42a5040d0440c0070140d01040112046848 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 780526933 1250 780525683 780525701
    0xa0602100b180c0a0e040c0e0a08160303270b12150604090209042a020c04110301050603041514010905100b0d020a26010e01150516031101050f0a 64
    0x3070500099401006040d02d54480144000c68030000401d041c0d240e50310a00064800f260302900400118100c40800381003201d4401c001e42c81007040c1600460381079008504400c2d00070ba0742d00044149411650180c0700d0280f01c91440d501a4421030760b03142c10707440484143c0300519803140443c4ea243c4568445894000004020b0170f1152000030a0f0591521408101c6082301c01c00d040058807900e80c0c5000030044c10300d02ca000e08481c5622101e613170b1248100b90700c041c0c906205808888402c40c4040c240000d0b1805075500b4103948a05000400c02824684001c1d90b2007441010811911110910154111010010007200c00c560200060010b20591320071036400012401d0740a00c00c0740351081d00c40c954850481c00084864010414540b4240240000c61800540b075100b810010f0078201143d8001d0030910841d440000800b000041e01e800c54659400c000c41c4991780e0500d40b1609546c40008810101c80440030080b228040390020b50080c820b241c0503003004106022541045240c80c070030380750b11007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 780528183 1250 780526933 780526939
    0x103050d09080a110607060e0c0f180106140f130e011e0504111b0c04110c0601061b080a021b040e060402120a05120a1b020904060509010b0a0602100b 66
    0x229040c0480000098030200459101000c20100c0b1004c00c040340e424001c48200501c0c03a42450354001d81c0000106402d940c0107002c0c1c0c1e51116159a0404129070300a21f6100c00003001004001407109620851458544255400d1503030301d400e2810707030501c00960140703901403503030102400107009440b0200c0c0200d00521419987c2c0642c0b908045114100f040c0c18420a0700c1159111001d12400c2106021f40d20100111840708180c000381500447d1241d5000031218880c0d031030140e007000b94070200c8091b912001c1d2628020900780e0309040003542c5450b403039980c446207511081240b1001550140c010200c024541e4042c2c10703600c0c60301d05915030440c0c00c607035030901c10750400c10143c0540714006011a40990101c408807240702c1c0160050307040008080d0054000d028643d04e0f80c034616070348401007080d11040e99610718000504a603d2001e1600c0620007541324180ca000300740460720303a801180d0004121000000c00b0a000d10000c2c05103006a40007501503000400316913003c260b58424800c2c00e550503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 780529433 1250 780528183 780528197
    0x20d06060e1e070333080d0c080307140d0e0a0c0f080c04020f0f041512020906120406060509010807081b01020c0127030b01030b070c23010b060703080103050d 70
    0x2149501c0b0782000040c01402010350782c0d04080b035034250582840e01c04201d07078180da4a4041c200810b000c40c040b81805410440e11aa01c2102042840b40d1311610b00e42d50006819825903c8045003102d0300e126402020344083c0b401e02c4503078490400c5201d280d042218140007083c903119185003103e0381409a0f1310034024080004001c01c1980008a0b607008100c50844005a4030310b6455241c0b542c500424000303080803000442c0100c0c0c0440000302040350b00c0c00c2d94440c1402480d40c0d6000344243d00c00c4148064000c0f6051014884d20035200802c19002403040302c0220b00e154803040428604e101c00d81c0054281d5001100402550303400740101e0104400b148504d0200c030074802c0010399207829900c0914100b046072a004400340340121190f4148404101e50500d08030380e00d0800004620023030106940c0c03507500c9000700780414010590103800a5000c0c0400000710f0107054141030ba00b8407200c4a078515500c422102400e56034210043c40d14900c2904c1c0c1503c07030350550a215150070b0351882c1c807406000720 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 780530683 1250 780529433 780529471
    0x4050315040308130f050102030406020c06010b070c2606090d2705090612010f0207140313050f0406090e030c0d09030302070b0a1106270102070206030c0c0a020d06060e 74
    0x4801101603205203420f842d1041c03120249400300c1c00204400e0080c6c03182d40b001c4180010890950018034044000130116030341a600d03140c0342c9016208440c3d0042c180c26001c0d074100201c1c1e10001520404084c01c0c0c0c2480a55450000f0300e03803c0c1602160350039038035004040e040140d00d070403041e42c4199a200d8840d070f03403102c400322600a18100184c02241c0c483c0d90040d0004400366103176550003841c6018400244040301040f4413050294008600440c0e01d12603a81d1010b101c1d680000545800312034084034070011a00d0314007844801c140d420381058110f62240c4010840c0e00c03681c058a0021805440116585c4044545481c2400d44003227800d401c00403100c1d404c101103980012098169401c01b50070a90314042c3d00701c2668160f40c903c01c0101e40b80103210400142c14504450107130071410440505040030640c41c002400c031b00c5200c0740294803140c140041000403640c44d01401000a04e00125070840a0717580010315126540030003160030540300e036010700c40c00080003506504040b02120502e44100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 780531933 1250 780530683 780530687
    0xf0f1410080a0f11120106060f0512070c21080a06090b01050f03071b0f02030d05031902250b091b131503020a081501080d020c090a02130b040503150403 67
    0x2d0294015220f01003c10404084c0600a80c880381c0c107000041283c1c9000c10210718440c00b81c00284101008114140351416035107005104591610132952a900c01d9070351b41e0441503800100a00781580c3d9400a080d11a10303019100f0841701140b00c203510307907000d2440e1800410003680c120307401280c00c682c1041581c03c2c840c0d030440180c07800d0001c2405010b0326a6a1001e045411000c2c50220501d88841609840c0501148a001218103802901a2981c141507048151142c0c402070311003da100007420340304050100b5035806400201c0c41ca60460729408106410400003c440320019110b0348041e10901502c035004104512500c0b82200703001c3c0c0c808144600080c0f0032000071030403580341c58441e40a00f0070000000e21341009580c0c0100140c229940303a030005940d541078a014104007140d41400403840503c001540da41c0400903900812428130124140001c414020780040390b0f291b002c0c403a001959052000181c09004400c0b5140e89403440c2104261030620b80208604240d03e1f02814000426 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 780533183 1250 780531933 780531943
    0x150509060d170d02070605060102060f06012319090e01050d0303091104050c0c150112240f0f060905101418040609051c050a0f030f0f141008 62
    0xd041181c88100c0452035052480424464a0342c040703140c440001e6000441c04a507014204041c06034404001c2540d41d6401a80d07159000d6450424605446001032030079842001810143c601c3e588014081c01e8504105011b01d400c84000352190007401411f0412865110030500c0082c411002c24408652400022800c0c10251400242c2019204d104020038480010040d40c402440a88100b2091030844001c2005801420891485000700640180c410300b00c220b841e410707150800e002c50122030711350782e42d0344240080602d195800c001c175050f05810f01105201d850f94405000b14003140d000320392150307041141c070341da01b1440c001442d003401e00c110038604804400c02d403130480420045803444d0384000b8843c0f41d1110200541081c200c42003204101d1142c000c1d003c1035100d201280c03030030144a07003000c0841032036241031000258180684089203110310a5032100305101e0a001030031110280c2560103440c01d07800c04440d0300341c0352864030a4407214030a92a512081521400c002c041c203001c002038503a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 780534433 1250 780533183 780533191
    0x907030b0712110d0501050f04090201050405090a180525230a1a09041a011b1b081507030513082212110303070b0121050607050c01150509 61
    0x10350b0580001002c1c1841e440307055003818202e01d42e81c480c0707070354603080001e003809000340c9000d980000c0e00308c8000d00b400e0283d500f40540c16100c071420b03e41004241301000e040282262070039034440011410210300d4540d00d80d8554040d50103098462122032120000c01140c0c00300850540403d6420400c5020f400c4200000742c0c46c50004603c0b00c4003c10000d6065401134000c9126601c1088042081d05d09680051503005411340307003400444100c10030340e0505c42204001c180070601010325040300041c00040c282041d44900c0318070042e03502405003e902d2280e51380184134507921881c040d10040003280c94030742e071000442c45d0030322036403519001084400c2848840280126808103404d10258070103107100c2624002c01844020b950340d2914681a0148002816a082180141c0130350103410080105d82c00300350041c0034120306900c0e00034421250b5442c00490018040020303180f20004e003003809101d000d642e20760b49041e00d65a00107070b80d5086a2080c0c5100c0320108030341d00200807075101c200d000f17580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 780535683 1250 780534433 780534437
    0x103140604030c1b030b130212010606050406050d1112060306250c1401051f0e01140603090309030115050103061710110408150415231e1302090907030b07 68
    0x584000516440080d08250700000d22402e203441c100b00d1603400c42031010b1403488c000c65501c8825200409958200c404901690001620801040c4003072401040100364102c4c213000d000407200540b050404071900280c20b21205803030301e0f1050085602c1d04002d03035500034040c00504c0e502ea484041c0070b48590500040c09034148442200c5e180c0074809200e80ca111020300200c024002890b200110244000442e108078400785102e250105240d01c0034190300313041e218030740d4110803042e641c801000000c1e04000c00c6007000e0f10040241d004543c40c00c0c0a0b0030500c2c4107004496200d503040000140540c1c2c00b035000390846e0099540d0240724203100041d003800c121440388002810300200321000d440b91042d50060805407180c12809a29138645501c0786100e140566200e5009031007a0007020f0603103030ba000f4190254903071032005081c0946030b80301540d00000106020801400d0310013180b012028200c1e0740c0c2e002c18210540d81c00c06c3d8100680750030344c0058880d001d40007123402c590b180b107010345020700040c003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 780536933 1250 780535683 780535703
    0x2b0f050a0f2d02040503060c03090106061403040204151d0406050a09051b1807050c0105060402180118050d060209030d03020702060a0e0a05090108011a040b010504060c110a0e0103140604030c 84
    0x340c1e02d9164111409000c0c0901560424a480c2070b040680ba80b00380c44940103036107812400a80e20748a0702a20301c40882d4005a00d2a41c4ca8907020170014014040711020307149202000040d030f0000e00301c0313019040282901d0684130391406041c81400c03250010403032681c41d8200071622002031030106064040300b030414202c8001d40c0b800004500c0b100d00d500d0341c0c00401448441805802600301c0090960002d40600038801c03503803103506000031f07405000c810511003160120006070070340c002c000000814203207856000140707a0303c00004410649043e400d43342d4a0780020a056542003d00c1011181d031104e040540c034101055001c100684101e85400b400c106401071000300303c1c0e031a6240c420007404001c24000c21540c42d100c506009100c80f07a800100120141d540e42101d05050048500c407540c16140c03a41442c0c40d000058950344014102115110250902c000003659031114806c00340c040e0260005c1250f0551516108910182c0c082c1c150a900c11010400020b40c4040041c80c00c41c0d00560b401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 780538183 1250 780536933 780537011
    0x105040e090f012f1e12090d031503150f05160e04060b09270f060f09010f060f02010204050a0b0301060822140a14010b01020709112b0f050a0f 63
    0x141221000f1001c5c1c00114000184400c018000c48454500801001060320b41034900070340300f0b41c201c2d588540307401c0e08500c242d41d08201013002c0c094105c02e562a500000300c1d0146000c0b4402081383c104540c0b400311008000703a0200b1481d4040300401140740203440401ca500e0070702c41254007034000e080c01248148100038010402c140d070607100c00880a1007524440d0182480c02c401007040d0070460708107010b044c000da45c54645240c4a80320a040b602e2030a07008120754101078007114003010f81d0b4143c00956400b0000002d0350744030350136010300400c401c000c21900c2c1c0d414101c00401d1854041d05a01112010014030302c540100031b040110344541c00a180100201d070500102e0906e00c014901a081225460300c9481c50001034003e100c154400b40d00740c40010341c07201d101c0001c80d0f454045030300e000e034006d001d0280a00300b5000742d88040d00070000300d41d0580d41c82d025000150f46607203150250703c0c0d40b14418820703591418000c405040080e45424480a065154000c545045841c0c03410b4400031003200305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 780539433 1250 780538183 780538207
    0x6090f0b0901140d0f0513120e1206130b0601080c09090a1d0607031d150711030406050d0b04020405010f0c3e0306010e04110105040e090f012f 63
    0x6503e0950b10700b20842d11050700c03010f004020400d000b100314566091000080c0c0c1030b881882e1031036195522900044000c501304008455601c0854412900000384016000d207000c3c04004046c400c44d540c10782820742c8500c40c82c00202640340070b028241031049010501c400041c01c5026254a07070340564188100e070751041000400b410400d46143d448058180b418501c1200100d0030502c501075a4505100440c51100407030a44000ca120400303d50700180700c03100034074803004903036504080c443c03800d8402c010000801504582c8036500a501280c00040d8401c69a4554018445000f0b01102c0c01c50a10b454000041c00c450319080740501042000d4640d0002c000d4004042d00500b0800c42009079200c0f803000c060400c504840840490604e841c848640180c6000117440381a84c2c0396401409054841d82ea800f00381c2d03410b00704020b0501106000210340205841321591248015000400b0024020300c14142180e400d06401000640703180311403140005001882c40701c1c140c8009030b00b5654040031401c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 780540683 1250 780539433 780539447
    0x3070b07121803020d080c0904050a06050619080601020628060f080a021302040f0302011202070b0a240305060105130f05090105040b010f030c03020d0201020a06060312020706090f0b0901 82
    0x910100351501010324000001c021580ba200d0340b094007140e0203002c950070103840e10b180803282d00ca00000108803030059818281c02c003541168200c103000c01c0c99519000017900d03a8121403c00314112444445605e01903900525258110070280042c28035400c0c0001c01d40c0f44101c034011000f00c650711042d0100d1007908035a000c00f00802e8400705980e00142c0301c4413000d81354500c83d80142c0c803d88082070b036003102c600c55200b1901201c0c0b4900341040c4403403030b590040d10040200c3d01c0f4000e41c9a401c1c040d070808215200d115a229600c00e910014100466800f4490720071420804081003411a03601400010000100e00341034480c2240d011401c00c048900c0400a4000c42c280c2d12000c0b4180400c0c090428015004580264890140107006a0300c0700c0d54070008110354030024040350038002c420005800c054080d12d030b88600620640b00140507035180e0006a07140b903801111107280c6003c64203c80c1c0d6060001307a01624545ca800041c06180500164031244d26003d1030380c89400002d244a2a82c1c02004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 780541933 1250 780540683 780540707
    0x30f1e040b15120304090c02160509090a0f050309040501090218041805031305010906020d021b060409020304030c05010c0512010e060423160305060117100b0c010509150903070b07 79
    0x101448014840a07005a04c0783c00c548909444a42000708a4104c18000304261200b4440d901d4035011440c5040208041c1e408080d04003401400b4412890000c00c80520342d140900780a5001182e54640000910045500503070013032060610510020560505c80c90268030080310450b808070307021510729035481050070a103000500034840040e90300e9246852982c090700b1108262210302c1d0103962150140c1e1540510304c1404016000000d280c2004400c0308952004408007170304c441d0400e1703242c144520480c1d1050303c2c01e40215248180c40c008010003401031007030403216031504034109640d02c1580c0c011400c042c051281912204000114240c80d598420f40c0d80b54010008c00341d42d141841129105c2c1c0e0015241c02c1008100d03280089001b500a000700360003408107035036038541c078048030391008243c040180001c401028180c000168140c1e04001510b0781102c8400001010708101940130710342020701e001d01c1805250b0404000d40e0a0f000b009035005e050300049203034401e07511002d0807618940184 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 780543183 1250 780541933 780541939
    0x1308030613020f0715060501180938040501060e030723060304120912080f0702012309010e0f0f0d03050909102919050c010908030f1e040b15 62
    0xc84c094080c4180c4121a4884c440702c58800c001d0141c0f90340045603c01484030354010039500c00d035420405803500c3d600c111041d680941c50703103241814182c401d40402200e9059000041210003080c29145414450b050041c04503060030ac0014046078040b9450312018800c0c2034246180340c400154002c1c0707a280c2078840100050555039607203400d00e400c5103603180c402c0152000070035082002c1410581d1709a80002541c21145c3c5c1c0e81421107544c41a28140d000c07240c00c84c10403c050000c01207a03a007190840c59140c0b60f8489003904c1d441c403034000406000003600d290703102d00d44180c2c41c1c2000d43c42d40c280003150004152110741048819082c1a140c5107d1810019000a8100e017000b022261107000e8500ba2481011400010219600d00d940082c40c001d80001d40740c1d90800020510307143e000c40480103081c0e28100315050680f620040f60031107440040030340c1c54000001c1040703030700d00003217a0107540f043c110180780c41030246040c0d401007420340081c00101100103a1000c01c00106842854400c480c0d401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 780544433 1250 780543183 780543187
    0xe0708010302280b0c010228020312060f090c0415050906190903050a030207061b0b070e030709020c010c0f0206040c061803080a0f0306050f090a090c05031e061308030613020f 77
    0x3005e0740074001d60200c0e4011680b0b401c02c5842d400500d000103030b00d20380500d09600841c180600032000001c0d25002404072940024003000510460325a00d000e03074440c0c0c3c51000070a48451401b00d4020b201c03d00b290407401004410007140305959510b03016654904080313080c0c1180d00380382d00d1050b0703034811454101805038451045907000301603000844106035040e40d0380301000004031102c581007038100c60301c00401c00b040050021300c0c01886000c032002920b50090840d5085076440d2400e00c101da001324044016651030780c0e0003a04403901b1000714009075a861008101c20302d0283c490288100c0300f0300661042103820118105021400c4211f44003940d0005802641e8512221015140b01c1c0040040004030341000d000080070702e4141454a03030680058030302c00c1d050f03581030300307110080400840485807242e007800c01107500d032802c01030f90104940c1d2036522601e0482c4003554a280810042516422114000040700000c0000d0180c035040403080c0c89140c031401c01990400068010640d10f00510640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 780545683 1250 780544433 780544447
    0x2130305120a020d080c0d05040203100c0e150301030b0705030a0209060a020c041d1f0905060705040e150604090903020f061e06091b070507030203160e0708010302280b 74
    0x1002006008180d15034085070078000b440d10085d24a5841280c4e080386c000070602c1050b42860b15500020380c4548010280d44080e08205251011200c0b4000000c00040405180d07030b42d2410600280c1c03001c40c0400c20741c0d88c00c40d851a641c19000400c024030001c104a4040049011003140b60141e82c0c0d1304400500320740e1640030000c402980c07601c00d00c9841d0310450038540c0c000349030301d501c12940d00c0301c0741d40e200a05031102c011221400440301d07402072106100e03034a040400121343d080c8030460280c0050740c1d4103030341c60f40780c410018800a4007403c01100e0300702100300c021042c4d98003411a000c403000d0076008503104846080c00d81c100122240780741040c0c0200300803c00b07121400102c1c2c1c4184a00d5014800d800d484d070400b44001000c04035036250180c00c40108104445415001030b000151041040700c1e00c681e01da5020034148421b4175401d00e03c3c0d41411000303101c1d4070b10401d00c1640c01080c6180110712036155800061a1a000f4144100084080d4a103020b02215500e00b04003d40380201d11642d880b8a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 780546933 1250 780545683 780545713
    0x7020d03020a1524050a1517270c091512161a030f07030b03030f04031112010b0f010f050c06010828110609060909040605011a120a02130305 62
    0x204559071072603d084d24011000d01011150074078410b460b806401000d5190901c00c0b00158501010403440c1801412200681c2e05580d030b1500d1481400d502000880c4040402900d03030a44c2c0c4840000c06035500072950744050341e140d030812140e10005ca001c0d403100c140041c2c40844c0ca80c6050751525410390103042e006a00a1202e241014100c45400b0403007814128004071127002c2e8003040c1c2e0050102021140441c0c001c43c480d411041464400a00b664a4a801d00301c0081e640d030b10070303031003190811449800c0c0c1e0380c1c3c5d04c0c1080600c0d40c01002c4034000c6c400640d12000162170319611101d50f80c1407041142c4448104d521030340a640000032a541211034551f10394072156070b40c1081d036a070300c80110390306820703400c2d40601c2142a0759100e83c00409100290301c88001c002ca150000d030000390308408140120601a550007440901580c0503c4000030355505011041040003140303003035040080c0040043c01d01c10504600c096a20611000c40143c4612600c0c10f5120036988a40c40a45184104110320903060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 780548183 1250 780546933 780546941
    0x209090403210e0c09060f060d0f0b04020301030b0f22050a061d06280c0c020f030325140a05060106030510050a06120f061502010b060c0307020d03020a15 68
    0x20700e0742d541841240803141d8410058070b103a03104071403494211410184443c1040481e2a801c0720f0000e18031644007003100080307000c40d0494000564500d80780c103010090350300070340b003259005d0000382e806500c0c560454480c01203411000e84290300140c51480001c2c4842c00b6440199916103600500001034411400d0080d036071012018191440b40c580110750803820b01070280c01e1740f0300e0380410250016647c2c0071210005901600c0c00000038200080c2c00d000300b02c201d03114040110041d03441c1d81c10704001d140140004100760034406030003a4820013280758041c9907510030141c011201c1c0c0c0c1e52082c0d034403a0320b8682411009142c15098510071114100204407021910340c0c140c809680d030402c5143d882581584640b030b9580b00f01a0012826081404191b00c900201d2a400032031480c003140b0340c0070307804280080f40c2066114500c64440d105c0e400702d1040d030a0141c0058030b4012505503003080041b68900c1d48a201c0c50310000c0c403a403440080391040500900014000d65082150080320f0075012203100094 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 780549433 1250 780548183 780548207
    0x50d0f0803010f081006050d2a09020a0f021b270109090311011e050408121f0b040b09040b0109030b07020304030b070f02060a1107170d05070c050a030c02040209090403 74
    0x10380aa004034901814480c45101c0840c7c5004050310907403801510380d003c010008001c04145222a8a42e04003010220710656008100401c001030343c440300303e24000c00c01c04260300041d00b15088040d50f017240c4c9045c03600301103c68000f20b41282404140340c640d84005e60f0b00710005200e03035205038000a21002030368800e92030f0500035280d40400c802808030050172107440341950a80303030486807144008440c05034410756002d84142d03552440c0180c0c1400018142d5012100340420311070303071080144200401b142c023500512585440c0780c246401d021506010380100003001e401590354590b1036419030f103e0150180296009801c40800c1d050045000b0b4480c1d00902081d10503206102c0841c02c02071189402c5207440702181e001d444180c880b60240e801812000009044090f41070280c0c0c00403800c022942d00c42100303040702c050b9442c9030b00030b442c01c1030358001401d0b1000d210112403601c001c6003000c260000016490301d070400410006200080090148421143e00201c40900300004c06400030307910495 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 780550683 1250 780549433 780549449
    0x2612210109090b010f08030403200301140402011103090d0602090a1208130e0c16031e08010f09090807060c050f19020f0f0c0906030709090503030a0b01020a0b01050d0f0803010f 78
    0x10985e00c0e50a401802d421520985007154400c0004001050030719040c0342e801c00411285103c01a924000603013980c025a4010750030342d008800f4401150b03000002c00842000c3c12015600341042c21002070700798808068050581030300040c0905c0641d544c040740401074011018441301c04103140c18041c0c000e4000d4001610000d0b0005400700d200322244010764416020302403c0c501c2c0805100f200e503e620201c407401c609010452003220400500b044240c555035003113903a45460b661400c01803070040c0025610924029180040880100b440d50302216030444e000b650110380c56005501c1102d10380320303000b540250b0080201d1306069809503450190f900341c01c6030703003200e030704a44e4800300300d858070f2011b01039410319808a03160581d507040100402e90f2210005007a01d414030303901d161038001e4500f80c071011107503a000041004581e140510800d254800203100520144034982d8400b034042030107010b40c601c02c0d0780c07801a20741000181607806803696440b155890710707940d4034011030400075207038000d03141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 780551933 1250 780550683 780550703
    0x912010501181112180f03040915120201020307020108190c03020703110705060d092306091203070f1b120e040f09051b0112020c07261221010909 64
    0x118100698241c41441c03c1c0803540d0440b1740c50302682d5030029224112001818026401c3c1c1841054051000d0002000032143c08100110028401c0e6440011904000c800030284241640940d0b13001040e02c0a8070b5080c200140647c5510002c903a104a15002081006040c0101d00b000380354180c002e0040c081c801d8440d0100302c0c000d4003010744c5456003400342e01d4101d00d05002d036025400030f5411022100b0b0054008141a60088a1041c42d00c0300e203c26190040e0b2200040c0714901d1f0b003c1000d43d460342d1840700e0302415428555001000384161035141c50400c10b02180c4640c1005888804554a41c0e0029000c1c40c070b12445030001c0c0c9040d2040900760700c214602100315210091701d02941030390582c00f03c0904040e11403480b0352072103804c001014a040003480f00b201e40514100c4c0c17004020900860009060684c0351042c0320b0b02c05401480000107a0184000c1c9460b45080010800e2415030445e80d110345500c0741142e0300074400f481400100318503586e100001000907655229175410380c042c10303000d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 780553183 1250 780551933 780551951
    0x309153301080f160f030e03131d01030b0703050711100c030b03071404051005090a0603110f10031116080414032103070909060b21130206091201050118 67
    0x2c0e46600f411118120405510300040d5602840361070700451440c1c143c2000603002d00c00f4a00c203440e40e008640d00700400d25000344c050000e030000400b030304050107102d91203881c150f040d581c2d00c04102102800302c1040c540c1301c10100d030321107024110601c6580d084104540903000c011003004040c00c0e00e40c11070004a80703800078800042c180400c44105482c1040300d09a1241003400c140002450010b1086000d816400b4010a5aa0311070741c507140940988400882c07c0e41c11401c01c2e2040440c07101889114a00c08007884030075403601d07110300090308810306000488071500d081102c0c191061107012007444400e0b980c0c2c3c5003001034600240054644c0412203d01c0c900364031040c19a6400c90b0040c407203842543d5291020500149401140c1c0700c41a4900124096a224101d2007610745c176801115049101107000380c3c0320988060070810030031000201d083d00341041d56985000402d01c0354060700a0070006440380007908c1344442c0c4005a40810020041980d4800b01079400024100546800500b081124 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 780554433 1250 780553183 780553201
    0x60c0e0306060f061812030403060507022b14030a02071b03022d0409060b042307030209040905100b012c01030e2b0e0402030915330108 60
    0x85104900c060b1004421003102800c10041c0d410460940f018401c4045c2d49a6242c1c0340c040c8400c040303071807004c01540c40c2d900b5440c0c01003c0e160001d042101310743c080d10710004800b404011000c0e419001c901da10000105009080f01c80c18200030b02401c00c0300c00003050100d200900d6000b0b26000b800b907146d032000700c078105500480285280c80003a40c8000b2a4a5180b81c04030107001809060f0807807036000241c201c060300400c00303a0b00400b00683c0ca40e661020707201620305007401804140c40711a10302ca43c02e455401d07010a02d030040070b022901019404100385070680c880c0d070701213040c15820000321041c0381092140040074000c1803079102e0028507122009103180d80710745d41004480c13200e2025980d05500710001140104104c212100d003500c01c802400c0c84841d60744108520403522000b00c40030050f05039a000d0282c0c1c2801602a010358410010000c8400c80070501e000003142194940303041c0d4541d501c1d141403001c01603a6030384000741008082c590100d400c005900c0d03a05400e8030b601165030346010038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 780555683 1250 780554433 780554443
    0x1020d03110708450d02060a050c070305060a1e050709060e03011d0d03060b120708061c030e0415030305040e04020a0b0a08270c13020d02041413021608030c0d09060c0e03 75
    0xd4000106008d885d92030360054002c0c00b0414103110446010aa69031102032034900180c4004007826960300c440b08921040714000c81c1480503440003488181420b0f9001000981688204000c00c11090301c400c01660f0290804031500101c81e42d0f1507500c070903000d04240c558400049010100b460044000383c8400d20000791183c1c19465921303184560784074001502ea45000405e41644641a1030022400c09001c56036040740600a41d54189925010b80611040f00e42c10352120200100350201000020f900038112426038074240e404040544682c404261003d220342c000c10084140400e107034046c181d201500b5072245141e0301f00c400e02c00080341201b1221000d400e0b80e50600303401c40d100d10100743c2070010314000b007450030890061030101440c082070100e80043e0412070403803c8103940c011a0740b0702585103d0310080301c071a04600e0f00350b0b40d50550036541d04217a0300074001d0b240800010306410100043d00c001400c284e6080c01030380c050b464041c000f41207107000600410040300f1102600d043c0015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 780556933 1250 780555683 780555709
    0x60b18010605040e090339060907030602090f0604080f01060e04152a090807091b0f020c0d080405120105090d1b0606031101020d0311070845 62
    0x19010f1038581001502031090400070320713180081c48108248030310040502d07809110081c80808a10a40001041c02c409038202d08551444079840401070103600c0d4000710702d0b1012aa80003100507900c5120b200480c841c4901d8244050b8417010208001a0b040d03400b10303042d07440120f454000c00005444098002c0c0441045d2800340803c62031301510040455103074451566140d079049600280c020030f04440240460132002c00e40001c40d54801081000001c000d0700024040c5a10184509014070b54100c0c000015040e9000810940c4c082540b1554002d10680408100207061151518028240030000d035219201e030764001e0754441c1a540740c40006110700c600819441001c1e003003011410108940d503804101884020080300744031500080d00314800c0c003009511450310900c0042c5981d00181c184514a11042c0c14035061000c1a040b1a1142044a50b11544400ba16403a004440e0034600c040c0c59000b4914003201084610004c282c0070004201d100103c1c014000740790050b214288050414904 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 780558183 1250 780556933 780556937
    0x3020309151e0903090a0605030405100c09080f070f0b090a05310c17150907050c0609070314030a02120c03071509060c031a0103050c0f07060b180106 66
    0x4100342894107809031116810044601d507000051108904002e0740c0b040c00c0e00c05501c2540000b5501145051118050000b4800350411600754501030b141e080c7c85611861000c0c84091740c3d420b0407052980250f080601030700d0080c3c03c407840c10300451856a81d803074030b0340907038542c080480400040101c03440049460894000c0d00003c507080c5800107000911411828940146580b089902c0301d40007c152179503814441d03210003144091460788007420030441d1414240b0014010001c02101100c201030400c1492020740b005469640c1d268803c84040c000d511100440b40195000e029042c000000e5900959009900103c1c6014820090942e2441108041300c09a00030f5020b0041141090700a440050301c14016240340158580c0c0d140180928031212803907050340d80702c0c1d040038054103101d10412040c40313042c10828004201c0140541c4c170085003450b03040585440004080315001760640c1e8200d1402d11503640c54400710304e00a0064034004c41114003844032152110210600b5010942c100c0b444c40d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 780559433 1250 780558183 780558193
    0x403110a060c03210e0319142b09051501050a18240303090906080309090f0402030721200a1e0e0406020417120d09030212220603020309 60
    0x243d50191410f900c10b542120102499004800b1030026500886100d00b0500000d9981c541406111048030960a105e02c0304203c42c0522092900300c0520440d00e9910001c03544460400030000002000020008a512214180310800f01041000612800c0800ea14503880510386c0c2c80c0c9003404030110b0700f882081c1d40707030058000b00100300350554400940e28003000d070700004c8240c0030a2000d00e81c6581c0c0e0300440c0005c0d9400c80410a104080c406e290203052140e001c0d40c03501e059070b000901e03540740103070051103003118980104045580070441d15005000b17400807400046065000240d184502c0724041e90750034185019000e0900550390304c0f0040d01402411090b041c1c4c14456a000040301003903400c540040b8905012400186144615102d98824000940d599003880e809560305068400110f4885d8000030040c0c0c1085c005009a64144610907070014100b140b50500703c2c83c10800200440341541d00190703200007036581807001c481200c284a00700c0401030f9513020883c00c80c4405c030361f0711381c0035001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 780560683 1250 780559433 780559457
    0x1050a050c250c060906110a11090c16030807020c1207150c20040b0904020a0605030901290102010b03070605030106031d0105090f060c0a051803210403110a06 70
    0x4840b0300300c0d126076800c4102210a05141e5521168a009030410004a42004810001c29600c4900699220311070b038007800c5041c3e400e603200003420102954861041d0310b0000050296a00002540e00404403281c40041c102c0c2c09040103804d808003a01d004005000d41c1c0070074413050400074bd503461001d40c2c2d0f02c020642d42d40340c0035488105880749540401040010010f48000c81c80750450958480071155480c407040080c1c02c10001243c0303034003032024000c20008041201588c0e82594090440e03070241411036403651500b5410380100b04000080c2c40241c2401603e6078040810340c1d20711210b4400ba0001c101c0e2001100800d41d69000b18403807000020420401400114429085182003250000d54144201c02d03401180e0f00313448041b540400030b640103111120000204020850f040807035460800d18281c16140700502c02e104060349000c038082442449649602c0400c22502d0b5203800940c2d8103401d4a5410f00c414642d80940700c02e503160001841c0d074640610740b0355a10401c465a68030342c8400929 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 780561933 1250 780560683 780560707
    0x30608012003010e0a02070c03141e0d0c0503040f1206050c0405060403060207080d0507080709060e031905070503030a0c0501050105041b110a050607090608010807050a031401180b0103030201050a050c 88
    0x800101010417168080c04058000b856881c510b4000d036116045000c1d1181500e10f1030361501280301030707121004861040401c650300d00400c00d0384a0148600d81401d14540c541000c80c9144510b80c0049010b1000304000198074400151000c049031203683c06001c0b944070200c951002d802103010310703235028900308030800010b0066401090114413894032a410a00060000d200302e81007140c201000c90750f0b5504026640380e11804120150a42d4180807880d0b4107204003080d40c90462160b0040c4000c50300080301c1c1840010095000103190041c100c9603144139070640281600c0300d21608484e03560811002280310b182c05d00034101d44003203d009400c840036000e038084071484d04146a03401e07103005200044010a0040c80028413841158076030807502482d24034004c0214505900c1130308030f83c1140340d044c40543d0703803584007008880c1c0200c0000b0748040c0590400d80144461a4240e0300d06581c101d000c01003141640d481c074100da000e038008100650340c480800064900460700c80b20004410420018501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 780563183 1250 780561933 780561959
    0x4180b090f04151805060604091709121606091401020d120e1209180405030307300c12090c03080d0b21010e1603080f0708070303060801200301 63
    0xa00400503201c521005015038021141d08884c5107080d41411a540e6090003810004281c1003981070314200300d2540c16448403020a60205450409140006141d48695980c40c196085c0440f0100a50b03401c02c80c1100806800c0b0100c0c810303c40480c01c0800000380c001c11001c013200035001c1c1078002d4459001c04030011203014290125000c013041d550004d184140c4020000c1c01ba000610b201d15650700c00c6641c0812006d21035020074a1111449002040000303072000c01a20780210241c1840701c1107107081c01000c41c0407641c104803005244086003400c045c0024035040101c9002e403903150900b000030090a41000e41d6481600036012800300e81081000a040d1401813868116110b40028984207000014101d00c9140d030b500b001c00a000402048580030a03c11400c1c1075040400a0089100c00011407154205a01c0050300c00308000c07503d2010708086900701c4405c075a1240780f25076588001c1c90701400134072850040010359072a00608c0514143c01140b0035801c518a01c01450940e031034541605804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 780564433 1250 780563183 780563191
    0x30d1e1812050a0201110102072001020304050913020a090e34030b1b04061d0f090c0c0f061504051b04030804171501050108040f0b0a0204180b090f 65
    0x410203040e0005021104400c0112420388602c015200842e100e00004081804281d180d210b42d9204104600c0010a05444000c0c520410038410311000031036001030f400e5004643c000c0b90000004020480321400b001a80500c49100300d822034181d42e1a1502ca03030031211401958580341d41f24075480b00407000c0070400100090320944420a0304416410039010f407801d15030044924003401d4083c0a8240c5051595502d91a03140364214101880c1c040000d190388049084420b03400f56040414500e0b80b01d40b00ba108104d08007078800149030516030024242075020240041880c06008580800381e88040b445c540282103031941501d10360141c400b000000c210160064401c03424844c0003200c3c0d4803103080038000460041c0c2c5099280c0703150407401303420141401149005504a41229441d1203040c0d01c145041d11002c2c60400031580d0389180c41d000744c0c8070044000c0c081e200220b080100400440c3c000380241d03059030003024280c0c04210700c000282d40c1c140c1d401aa00141041c0001c4400110003002688 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 780565683 1250 780564433 780564467
    0x20a170d0608070602010c03060e0402010801061b0605040b044101060e010b130e07121d010f0204140102060412082a120c09030714060705010f0b030d1e 67
    0x240c1e444085524040b2180e00c5100941d454540c013a0308288c0512640c1d008190400b24500a4074003580001c2c0b280c0414040c020911904d090204001c00c1d840303a005514aa0051003003003030b420181050517024004413011610150f9040001c0d54a01c2d21000b50f41c2510107901d01c0403010520f01949101c0003045209941441d9a145000a800c08c81110110700a02da116111540d407246603802c1104640d2a1304042d020040c05014080702e0f9900000034803110203c5100041d0714410301c414a54804c1e106008140c166003070002601d40d8580c198010003c84078041014008102c0050059844003811500a4a03588030001c10300300ea54040d02d4880d50120700c2820618201c2100b2108850008070b11010ba042c0000c003250b040380900c10f00e02e085405c510304e01c4045080620f803034000b0b035403a003460061103110b200e041c5860b65a5241d14003541c4090b503120000303025000d0700760000001841400d001c0303407107803141e610081c90781401651400010019080040f00320041d50a040d03c403400310000442c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 780566933 1250 780565683 780565691
    0x6010918050a110301110c07050d020f0d061a0102010603080f0901170103061a12030702130b062808090a06110403020d050105070906020c010f08060d0605091c020a170d 74
    0x1e01c2885400241c510490b840c0300f2082a1505050849858900c01e107144c020801c5180d10360b100000f50a412a0011034503004100103a02c00714481c07140710f00e81c10b5004145d0083e03490410031550491512507841c0c401c0c540309070300307030000490a86001e440060a43c18080008100c1c00d041c542c0200310b4082c0c10704200411410741e031650a01107074244d200b034400b0703560f402000c01c030140300d00000d9507031940859104d40d0580728840e40c1a128460000c009100b042111032400c80340700d044d000b540d08120000c10b0f0300d403100503611062048031000107200902081104102020b01c3c0202c0895000308112001080a24620395843c8020001250240c42001c2d0501c0700100503a14110900b201900c500b00125071400c101102500e9200c19400c4401990003000100350103982c001f601900a0700c1500e01801d098588134045404860081c8c40030307040b04c3c1007104220350f4420001d1104101c41c15500000e1420080480c12600c901d412078004140d0f0544100201c4139501000c0035004049541a0001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 780568183 1250 780566933 780566981
    0xd26041403160515160f03060b04080705181005090c09030604031e08010302031b0f04141b04121101030f0e0609160b0409200a121b02060109 62
    0xe286400c40841d103802000380314201d0040010600640d1018698080b0600c414180b2045c20400d45910300d40c0d100400c04ca4040c0071144500c030360030075030007000d10101c0310780e80741e03200e00550380c03150014050a030040c61050406050181d8005c0d65a00c20035220349420740290410b020825000c1002c2c01804c41000c05008012856605105040c02a8425110102030340e10b030700000041d00c001c0078000e00c24494a00d004101684021410740d0350158450104108425414005124640d550025581003450402000f160213101d0320020300990700306500351841094070340c0441300d910650040c03003100c80d0305e20f40c0d00c0001403080c6004c02c0c1c1050141000b00701148810344940c11900304e00c17591071007540410144440480144040404a000c06c0d0500390a031741441d901c0902c0b031003a032090a00c07007035956021000050400d14240340107450900e005a483c20f080078010a080109450101d09038a400c2101461503600c100a0b40c2c0180e103600070b05002e03131174140c0d03407001020b4641c1da5442181c0007600c26 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 780569433 1250 780568183 780568223
    0x10f031e0b0f0609130b0f0604112a03040f050423041b09090b22020603011503060902090904060b211e0a1a0c0708030c0c0d2604 57
    0xd102e4500401100b03243e140050411200000c051308407080a03d501c107603000855949503a0b290f020808089081d03441e04c2e070b01e012500070400241800185900400c0c000f681c0c909241900128408060210300c0f1031980306e644980780c0c8203500c200500071489d03090801c240e09242e007103044190840b80300c4450810100d1202921190100c0c0d08450840701400c14003d00a804611030f40035190b240410040c0b5089a5240350005001508007010300301c0501c912608142240201d0200b0760f40a0a4580c69580d0f98039408903c0b666480c805022904044002c00c03190440d00c04d0301c0f241c401c0200fa91100d0b44480c0c5a00c4020540c0081280d007219000c041003014a41001c0b9940b144124040141450100000c6110907600c804041103901d4020034000000b10300c4070144000000010140384a503611902c41010540c402e4041c02441c400b03010041120101104000e0303d0b00003101c5050302c80711225404d00711600380881c1020020b044070b0071054500d281c1c0c421140e0b0360240c0710b00b1004110b15040008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 780570683 1250 780569433 780569453
    0x12170412080703020601082103040503040518070311031b18040e0a02030c060c07030b0a0905100c0809010507090b0d0605040e06100f14040b030c0907020f010c0503010f031e 76
    0x4281c50710100050840c04050b07040110b03500400103240501184400180168044030421058400355540440410103020040c000c84009050080011801c031001c00608001ca95048900c0307000b0906d0b0088001002000350222845907580300c15402140f0301c6041c5400c0345401040c0c90210302082e04980d01d26540351841160361003041da4004240c8100740d4070406140c8002c5991a6005220910410700442d1001620b0302c203407584008108025914403d40304010895141e0141c0148900c40d031003c0e44000d1944206418a81d99131085002d17500c104403170b030907607c1c00d030b56440008160030800c01034060480003504010710305220210381503a54100160a0380d03000300340381c40e80340c1140041c403030351461114042c4000c0419040d03603541d02e4078081c030b4603131b4001081d0851802503803907001c8649582c1d4180010a10314000600904203400c003e0402591840940c0c8141c0d03296103090782032411940101c0c10303203040700c446400048c1d50300c0c00c5540741d0105c0c80d09000844180c0750b1241e00840002d9034050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 780571933 1250 780570683 780570719
    0x3030a08090a0b25110a06020903030d060b0703030507020f0601140111070312020c010f080406020a030b210c0111120a11070b090a05060304020918100c080f10121704 73
    0x10040d08106601091000c40313840c0b1810b01c00a000c44580e14040007040810071002a0350000801a2514171040103e411403140c000c4840d0054a0203c1c0801d0803075480c0050b0500c2070090350304025696602c0d501b070340d907141030202c5c284403681300d680100030f00d103440c842c44243c224042c500b519031010480c410701c0c540710640c4c004131608204100716459455042024010840382441c0ca818091042e01303004c3c0c209039002e00050065500040c0d0310407040c0c081c1c1c01c2141d07070040150405010b074140c100007003d0500300e03031020801401142102022580328480707440c00509601c0182012480311aa1105958012202c030414084070000201c0740788024408078005084d0307915142c2e554610001005082881a0813141c844c1c4010b10911000d600d40607041a0300601c031903201100c1d00d40c090303a03a52070000300100c00c44e40141000d0907480d64540c0084514012440c0c80c0c503160725611000209281e12809006503040f05840c92009008100c0c80c2d02d43c000f1a00c441c400e142e26140d12401c1c0700d1400d801c540d07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 780573183 1250 780571933 780571951
    0x8060918120c0114010303170916150306060e1c1b03120f08100501080703091403120a06060f18051c12020f1f0b09071106070e03030a08090a0b 63
    0xb0850308050a028010f0054081d200e0070328100c0c56046590180c4015074a408100045016000285419a04100305040403807004062680c490341c0e4a90358000514103007281000a0a1000000c0d145001da1704d990480c40c1c00500000c41d03420070304504001500003100c1511001c608401c040b040c40d81421201c4040c5011b440259105022000c024082c028098003110802110004008003140e4000307030764050300c1007442c103440c00d44c4641074228050001c0b4640a00300c5034401903580c103c000004010244040e9004800e0700c41ea07144850f1104641041c07080502182d08100010096480741000161400342031b07007000300182e01d1304040340b600c485101d46840c1c1d5500d0f0294035000d010030301151341c094101c44c1c801042c03192011100e007074880d50400c141c4061020044d490141040b0340380c0158000603c054512600e5141c24000100741c0c5554001da50001d00030b4002080f4181d00c40c40c448450002c01500452074000b403000700f110350000017401c40716a030003038900e2400080e11100403070307000e11146 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 780574433 1250 780573183 780573187
    0x8030405070314030306010c065c04060c150603080405040e0f0d0503101a0316020f03180406030b070c3309060b03030304050f15070806091812 63
    0x261a1128481280c1c40c4080d0b803030b82c414010040b03e41e90040986440d23550000d00800c0c03241422442c0b010300e01010700c1ca9021070500d80703a12011062540022101580036181005207641e89207248841c4c0b0388402890750b00403208010521000e070159014030b100a100381b200c0b611004c000c0304c11404036040f94004036005d090024041100c3d1410f0b0282002d9409450041e040c41440010007554400f030358a40700c01401004400150200c02e41c4600600906038600900d0402c04095440d140c154400c40e01290f00340c8108100f18820740c400140036a04014940c000d511f81495008440011402428010f90203500c5540220006019600d40c2c0c0c064855900c1d0142c0d0610f444c60010314086101010245490100c00d02e2020015805601001460108400201c2c1c0c0c400d824814090011250050741500c07000051200300b00c0d0001c0e003c40b220b0510f00c03e403101141c6803808070100b100300303650840001e440807000c80c2a92400c20041070308000d00100d2604210355040100d42002213018401000c0600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 780575539 1106 780574433 780574439
    0xc0f0b031b0c100e1e030a0509030a02060a02160b09180903040e1e07020606010507021e040f0e010b0a081522150e06040c09180803040507 61
    0x142c0302511112400394140c1c0000d0140620003d00921403185200090044400c404940080a0000d1850117800704822640c0b5009080020b6260103218842c0c80103a40e05001400c0802142d00548200618a0502c40380f83c4490741c00098200020003210026951780d00b0784002001101b809100c240c1c40e000401d51030360003070750041030a0144907030500034141c509107003520351020703150000041c650798078038102e0b00c0700c6040c1c1e40c290111f40248919001803408084109080d030075800101600055480050282c501c11500285040d6642c0c2c404403c002c0c00303014529000100ba10000c86543c03a10702459501c1015107102d44040c050000840e0441c5480e10700c0809440d0b090515140751412410030f802d904c140b9001311000b0780d29060718554144800304d17035588280e4004082c409403074508000407010340031203000014139114081d5100f00049010010b140164003c070001c10f11681 = true := by decide +kernel

theorem cover : BRFrame.Cov 780395683 780575539 := by
  have h0 := BRFrame.cov_init 780395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 780395683 ≤ n) (h2 : n < 780575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
