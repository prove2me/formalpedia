-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4370
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:24:03.293634+00:00
-- url     : https://prove2.me/submissions/cb8e9ca5-b6d1-49fe-b205-116596594d17

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 785791366 ≤ n < 785971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 785792616 1250 785791366 785791373
    0x30610260402040207050f01151211010f1101051501170601090302060f070b010f0302180702100c14131a0702060d0e0a050f0a0b060427020604051c14010506010507 72
    0x31100500c00e82c0c00030340801c070b580c0001c0c0c0308103d0f003041c6d6000c5d00000a40a05c1c1d0402c0340f0000682a801884c0c4048010340280210f2549191401040801d003440ca4000e00482020350700a402d1400300c66140d4a03110400c20000c0c2518100c0ca0224401d1740c0d4020281d10059921808460603100e060008070075103014401420980024101c0c0210750305d6090a044096860302c21a8600b60400c810403500d0740c00410450800c0704500c0401840c00303600480901c0c01200082d550300390444d01528240c0c441070030102c901e0003501e212000951042c80650380e280002d000c2503505085206c3c2c445250403010020303800b480c00d0303002d0311700d5075500078a401c0c0303441140301512000d000342419a5210303008102d0310100103801005140350b929046400ba100b0b910725803c1a0903005030040c03e15024508040042d4072902208110404c80b80900e06041c210002e1070002c120240220b41000341c0110500301c4000e034520626004081c4c00e40f00709032051310041e03c58280390a842c070940300c00740460010300408000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 785793866 1250 785792616 785792687
    0xf0810050a0b0a0b0d0e010b1e0105040b0a0804030f02061303031a0907110c0301091122111c090803060907120516021b03060a0c020309040908030610 66
    0x204030724401003829090400051503001041e8401481c0410014419035226110700408201c070a500c0300807c900521030000c11419407442100ca005e5941a626045d103076801501980c019020002116861303108d8444080c0102500703540581c00b25107649009940e05200113411885411000410002940d0503541038002c0e000140c400517540321211000c2540f521920b030600d2007010696190202503480c41400c90603c0310031041140aa414004c900d8003040c0c00c261b039500444c00c1540c401c0e15824040c4514511110a1050005000e081006000100b9581c201814818417078440c0b00030711340d2904140c0c40440310481d10082c644a010710001e81d061815100c15980300300d590402000341100344500404882c4100c0b003448401344041c00d220b606907070400038010150384002042d94a2104100026900d1030010013607040b058503aa0341c03201c02882401601c0d5000130141007400154094901290386400c01c44209021380d5030319481c108250b200740718811400c1d407940114070500824903080da08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 785795116 1250 785793866 785793871
    0x403050910030b0306100f1401091701020d05040b09010c11100c0507082a0c0102060a020912030706060311090c0901052b0e06060f0a29040807050a0f081005 69
    0x149030b81c3d8280314407980c40c00d10100b4803401c03401a420700d10a003403150a1040300320b0342d0014040303002a0324a001140e601b00072000180c410f10308c0502c071804550301109002e03103e0b6030411401207007010f007841301300001d9a507854018030b101c4000340f14000242c942203906021641e04043c1c9580190710400300103201d9804496540002c1c54941c3c034103181c0752941c6420b41d10925416014842c102c0703203c40e500c004009483e0810384140003400c4074004000000b0355408000e024000625030014080005070f0340d90801803240b403020420b8130340322052401c00000a0030248410388403005e51240340102d07403070103140040c8682d12101e40d041c00c19419000444954104518540141075910b4850581c80c0c42070042e01059826104041800442d03410100d0038007001074080c5020700c050f030703100501070360b14445410140e448008652031071295070960b40240c22a140c6011a8042c0700003004601160042100c4040e01c1e001d0f15a03041c1d8650381c94901130024058402e400c130542213440e251b040006140c01058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 785796366 1250 785795116 785795149
    0xb060d02010e102a11040b01020c01031d0a052d030301030f0302120705010213090b06040e0c0f03100906080c060f1b07140306010509010509070f02030d0911120604030509 75
    0x2c0385070355440440500321202c041c0c44d40030402c0c11380c00642040042c81920308170100a0b681409030000490010b5600c44180da41641815111401e1160104603210204e80b154442d804035010303510181001901c40c000a25428030f00c00b48075000c0a00d44402003030041c035020b5208000e40c0345a01c0c54888041001c02c0c3c603000c0b811030103105900320000c03041c0001707040307540d000c4d80005a0300d8000007021004008503a00c425149810910442003985d00d807400e4038100c992803200e42c3e08070350315502480341d02d00c1600204070180c0404024000c801035004605415207003408420444592900042903844640314891a40440c04016150039110003c004c0c084d11f6158a001400100a0f070b071030941030810581000d054001a0300ca015401d107000c02c0018010581903641e40350a505240100d0304004000b03007003805011907121107050451003002210090350f07500c8810003101030f4510b4540141c1b0301034586070b8881c00c0381d0600c043d0420b201150441c0142d40c17640b503003841c10b40030710207100c1c0303000c0079005c0c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 785797616 1250 785796366 785796377
    0x10c021e03040f0b220602060c090321120c1206060a030b150c100905030d15031b061409030604030305060a050d0b01061803080301061b0f050105040b060d02010e10 72
    0xc043c00700805640191804114403510b038448841080c05951070319448122980d0030a90801105401240030b64024984d80545076490082c800428a40400a0200400c002c0c2c210000b100907003041c00602021060b011041c580c0c1d45500c208414507005091840421a90400118481c0e242410040c039040c070302424082450040f00c030001ea0041e814101e801d50714400003406148808052025110110101c01d0400c0a0700031601c80c40d80d603014501d03040b032a15690f9845035400c0440340441d50020b550000c0d499619800c507041210b4003034054840c21001c01c40a14881000c85a1704040d11040c0341c014004100c00d0391251000c07405824060030700b64000c07080c594081005e4450750b200ca540b290080039500c0c10343d40b4040006050b00e10300080c2000c0d0b03001c2e580701400060240011a411030301c040c03a0202c49030b429003618040706101044000d10120000d60540208141034118034442e5005450070805a03648500348100c401c5107800c02800105101408450341c0381c602d0169004010f2171400c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 785798866 1250 785797616 785797619
    0x80403020309011b060203160f02070b0405300109060506010e180c090303070c050a050a05280909110307290309010e0a050703050d051809040215040b0d0e010c021e0304 74
    0x503101283d0060311168032300c05070b0804c0302c02015080390101d607a02020f44000c1031414a00083c80b0a0390003940109881214a140c0d2481207400d1001c030070b201c0f603c40402039110500d12040450003000081401c940a0b0b003440000b03000d079070040c401140c0c5e125001d4030303082466610011802c00e005004040c40d525420900c04550503071420000b03007402c14072034403440407102c0c14041040110030440d405a80314001c42c00b028091912403d8840b409035020210214120307480701007008002c2e1064102c03a0070390f4a406040d078240304266190001521081e016036000f02d4440002e141404040c0011454114141038502c6219a410000b0b40e4031042503400000c00e801405c407801c0c10040340c0c41c001d84d519441140140248032042c00b4030407130035049081c89450566400905502ca089400c078243c42460408005010354075030f8074060403078080c0e4400c0d240e6159250100000c164000b881c07104001031601d07003a0041c003d014491021680000d030014207507400032141010b9a20141d403089c00090209210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 785800116 1250 785798866 785798873
    0x3020a0c08130e0a0b09060307051c060e030a120c0c12050d11070b090f01150501110a12030c030b011403040f0c09020f0403031103030411060a2a020a06080403020309011b 75
    0x100c0718001c2458100105d01c0504440402940d02d50103000e2520942001c40b04000e569100440c24140320b90f049804512500c0c1400d0200040100640341c2d440d500000842074245540700408129505070400c0402102c0b04a080c1160010a840c038028080022031030340c040414001c0c805044018603000d0701094071034900c1400394403074011000c100c0764a00f202c02804071070b240c2405541000d920783d10003046150502a102401c00103540300c1c2905101010f800c5454000c070a001c1c450896402921020300c40c0046140200100011020316001901c2c1c90303140c16081d1b100750010701b05802c541c940d180c15500c0c0d5031910007848800324801c880000d061000001c202146d80094202400002d01c102d844519509000d02030318276111b031401880d0000c004103c006820b2040c000380054090b1a095258269076005a8030801909000030310308008182c14550301c640c00b04002d440724421f483c07011090366a4002a02c0140042d540100580c1062282d1031aa5203c1d099041215440f500300c0c8045c1c0940d5207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 785801366 1250 785800116 785800139
    0x303021806040f0602070803030c0403020409060b06340b0406110918010e0c030103150518031b0d0207060206070c02190605090909060c0d241203020d03020a0c0813 72
    0x3d100c0d403900900d80c44108101501804140020315405010318607624224103410014403c601000b03114554031848242801055800707000c00c60405408549c4d038602c264041600708030784c08071003543e40c411034603000340f030901d032007107542049501c88029883ca0302d441d0b80f864003510841c04104000e00c014031100040d0359074446414042051402008565410301b40c4150000400030048500342c4400c01c0100001000e90040821000c107417800020542ca460034505901d1819060642491001058691001c1d12a0310058511201081202c5060301115400d0340c88009034818000540c0104001030892401244015901e500c018141c0012581101c1e03800c0b210001500030400081000c602c034040c0b81051603045401402e0070004000c0381c40c080203101d459101e0500203c440d039441e070070366021f508941084002c160031540d042c00c400302d81300c804424015000ca0b8003035005100b4102113010090091007100c4540c4040d6480c8c2c42c1ca904143c031845a42d9111007030625142c0c0c00d05000080101405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 785802616 1250 785801366 785801369
    0x70c030b061e210c100c0b07050f0a1d120106050a15051909081e010506040e07050f0109150206040317060d0209040807150605030114130b06180a0b01090801050f04030302180604 78
    0x58588684003040d50078a20347c000c0e801000501440390401c0050344e102e14100c00d4034400c603000d244c00c0d48040d084201c0e20442c0b44100c000a43c02105041880e1003081c419080242620800d0343c0365414155941100c0d40200c801c0549400411000c010041401d40d1502d070f2200f036401c441c00c195441607500c482e128035159511100324080369096080c0000c04c6000c4c0034140c0c006004540c10300010016150170b9444842912074144a00721008101c1c441d64010000307d4010811040408408a002c03100691a40e01c1101c5c11400588042c0304d005240a40b404080d000d20000317850000c40030702581c04e1102e22103014206881c011018840180000d031496060560415401700100b061403600d81814251455070b80080e0a500055041000a02000c0c0e068110f031a004400646140c68200c0464000040f0740d202c0c40e0509803100c02c11041180c2c0b45c001c4903060000b81e845a0145540d0001d0030b00301c660aa6007001100ca030040450701181c0300750081c0448004200b1900010360800f00000c800d80c2c00b6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 785803866 1250 785802616 785802649
    0xf080c1e0411220609080f15090106030c030b0103020a32040209120a0213060b03130303060b030c03070818031606181a0106080112080d02070c030b061e210c 69
    0x10100207100380390340100460006c161280050410303008203c1241e444000d03405c1c1c5424818003103000641c950601b5000781000795000031400e1511910303030410b9642d1540c01d010a078000c540692000684000300e42500000e41c0310f0480f4142c8410294250ba0030b601d01c0031074038681c0b003502403042c2450b40c0e5410024a00002e0142c004090102c01032047c0714940d10710b501508a00c910701241002103412000440b64071040c1400074000140071881d041e4020900d80e0421602540040204031841a0700350040d03000310100d4440844e51b9948840380030680680c0006404c441d002030016059002103603078200c0b04288103400200d07003400d03480100882500459025281146106061070300001d20200d2940904424a80390260f9818480c03c40019008103900911075180051a1680c0d0b0b48203905403161194070440d8a1419507132810030340341c60784098459034852440700300c61101c200005001b1840184010303003a21100c1d86000c80780700049050f40503400c490301909011644654803418184070310940c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 785805116 1250 785803866 785803927
    0x1a0c010b13090201120b0622030609240b06220e091039020f071403010b03072601020d06060309030206100b0d02030405160f080c1e0411 60
    0xb8540001040c040c02ca54090036864038048000030661203000488080ba801c1038001d10000011119003180e401c0544d1004e002149000c800344100004800d0f10584800c000c00c56442805141c1c014500321080c1030340066000e00c0800519915034040601d1a008100300043c503c1003070364540e110300d0303110021034000690f0382098003003813112541032103142c0000d2010190710603550340d20038000720b40c0600b08041442801d851103500080600c20442e44040740c2601082e510301694642c80c01ca14008440300b5148254208220580c181c1400260041100c60450f00c080c1d0384404d02c0d00300c4030f80e0800c0c1400082030755020000e003461081d45006400c01841c2e5554005100794031401e009091034008ad000c81c1100d00c61000400032110b2035820341d00307480d54041005989858074580f8600d0708544c009190142550901d0001d0702d03603400242c68080700c0c4400c2c00d403a002d04002040003800342c0b00348404042e50014410310b0a040c18207501983d0012144510b0340d18000511003c106150107482c1144a0100c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 785806366 1250 785805116 785805131
    0x705090409050d02160f0b16051501030b0606120712090b0415151206021303050d0809011505011b140a060912030504081b2e0e071a0c010b13 62
    0x95040200c005007440e100c81e05c030b082504041c01c81c2812040307441140b43d81030740480d0000c20b820020002011103580f1400302d44411750200340c006280c1000348000c0d1102419000080c016003400803c8809021071040c0380d0f10305a68200055070781e0702c8000c0640c180c40742d40d001400c0005100039102405240945101811140f44050410558110301e22110340d40d151880c08014a0660f90604921305070320030805600d035100003450051982e2203074805800d51040101315181c3c590048082c0740221142d40003400018620a0502c0c085c056030710a043c000343e09103400e9001c01c3c110381035018441d886515a44401c04c41410071034600302c504482a6041a99500c031042000b101e4443d220f0040d0441c1020301032480d03c1d496024850103016038019042510044200e080a020301601501300142d00b014041c401c000040c44403081c035042c8030000090314000201c9581d060029071070381160354003200d1702c0c0004112044125a60400324646026648807001c0d02240e5540d040b090512034000b40c80054040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 785807616 1250 785806366 785806393
    0x140f010501051207121e0c09050703050a0b0d0222020a260f04020f030c28050415150302090a14031005010f050f0114030718060f08040b070509040905 66
    0xc0f41c1c0e071600b1580503400798404024a660041030515180e400159101700c220350761400d906021031024000340a9100e400c07000c92412842d601c001d005008507076081000ea941c42c01c030314046401c1c041d1781aa000401480c1c00005203421030b013908100901c2e0123040807c0051124100c2640c02000e2140c020031500d5100012196404000d41d00c00036940b40c0121441c10443c080c1a549040640041d00a0740300450380f5241da102009054481c1e100501211881040304001000da200322055000c103251078420001120b14203802420300d11540041c0c840e0115107040407000102241c8488001415028880c984569580c000c5100c007d01c51000c01a02c1e0011010800d1308060b6040103111400385014010b0060124100703100043c0d4109540d4603100c84044401070742c000c140290912040c04c00001000b000f04c0d40700118045040000c1c20441110341c50b60303019516240c0b280c40c50000030f54800d0000340450072070420b40307030005201d047c003a1914000c200824162032400d841990994440041301920 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 785808866 1250 785807616 785807629
    0x40b060f18011e080a050705070b1906080c0604051c0506040f02010f080730090809090c0304050c0904020d150c11010618051f0305060109050c07050a060504140f01050105 75
    0x8484000f0f6901450100000702800300c03030014008000c1c035a5107000152000d030150086803900c5801640c0743c9030780d140903040b141002d41d00c1e002c00410b80381807d40004061500040d02c001d250001059079042c80e003440c3c00d1040d072644012079840700c3c00f0082c1070b03040400c100f88132160186d8054803100c40d04240307500000d003031021100c1c1124104008182040401907006d1607628506100c00380354442220101409100070004c84e52103000c462620701048104503000c0c00600b0403810035241031010b80c0d20381400300058001100c01800329005141c080600d490244022980300744010700c086000700040e00e61080030403824240030451552044170400d042d4114030200b204580c0310000b844600d04281100c1c601c42c4c0750020800c4000d4945000c07400700d200c515010742116194083c1d40180b20b90ba400d1480d590700c0203200d0079801c5c901d440c0c04070b040301a000085802c5690020b0041039186605d0396040008e2400038030a9501c401c02e03180c5852500004e00c4114a2a0b5103000003152550502040080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 785810116 1250 785808866 785808887
    0x7230d0e0d051f0227041406090a02030417220801050115030518120a030506040c1d0109050619030501120c17010608010c0f021005090705040b060f1801 67
    0x4902114460301c4002000014500003066126022400540c885030b40c20700030f070250100907107910340510700604090404980311818218120707400d016200c180009080c4804050701c0d455046545400002c0d1205050b800564005200d401400c0c009841010307681c403984c2049046540b000700d81100c015080340c203c42c0c110040c060510013004154584800c2c2813941210b03001100516489600040c2c2d4044030100024148500701d040d01d0a003805000e6500391980b2650220f4082407404002c5035450500703119212994185445404104881c079210f00c0301110181500b6041003240300d07020400782c8481003e042810b5203004280c00d14008400003a0507980140c01911000801c21071141c040b549040001049034101484150f071903901e6001640035200340d40141c0b00f50347c00c201c1801c00e403c0d48508252400034555082c0c940c0001401d1841003036074020385500300c40354800c9509104c940790035444100c04100c01030032907103031080c0c1d80b90600c1540c02c4003141405c10020b40d10745d4601d0396044080c401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 785811366 1250 785810116 785810119
    0x50a1503050f010e0a0903050403060501080c09090706051b01021603030b0a051e040b1503090601030b0603010e0c01080601050d05010e0103061805190c09150503070602190807230d0e 80
    0x14169810900d100341c80138402095501100d46400d00002814004c004030340c05550008010b000360340c3c450154565508152005900603d42e02c40050780441c008a91340d0203444566644030b10381400840c0c4400d926488010001055500b0030106c0c88020744070240c200c00344e2180c0c5020905100c8a000c0004c000c500f039000c240551507000e2254420149018000c522075012240040d8855065020404c841c0160340e8030080c01c1c2c000018880d180760000744040c1240c0c170507882d1f144941d50b403005050980b02006807100199020700100842c40d0f0241e2002c0e40c1c00749043c0342c41070614070140c00781000c0ea2020390010a00b6024100180b0a01400b80074000c00b401071010342e281c1c0300a180e80d0f00380e034a8000e00301c203031208202c0c400402c0400c0602403c80e00108103803013040c4031180f03020104940b0f0700714078402ca9109120b008000204c0600110300302048a1580545903202c54490711842401d0340080000c4070314400c00840006540d11a000c0c007091083c1c80d500a010810003002c01800d40d02d44000006d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 785812616 1250 785811366 785811391
    0x50c010213080d0201110913090c030609111f030903031e061d04020a0905090102090915010215130314090616031b0f1e020303161a011a03040804050a150305 69
    0x20344000c0c0403081100c0426500741e80041140c8c0030390074050020700c40040001d0101c40c0580c000400e0000582000e03920a02401e00d0003004800a000c008075014203851000e03510310b03451801d6405900a51100d00303624002d0401150310324024107010784101e000145d03000d1050703403001c0a000d00002c0d41d4800d04400c58081000d02d150401e50001442c66103644184076180c0d441b04000b134600700080d01518851180075160740c81505000d101000b40c0c0d02c0d0342648a005120792584c002040c1107040e10240203c402c01804418400692402c40d0f82c1e505090300542080000c03c120340298544200400c3c02c04c0031020001e0520032281303001002c20020a0310300c0c01c00250105180045441e050b03000c240140c0c040c8041d0b143d80161981c80c485541c014201942c14000031455181400f00d10b441d2183c02442036160102104100c5004c2501d44421b001d000d00660305508114036002031880155045400b81842c01c1c101980c44000a002c20f00d141c10880c00007a285c0c20b01c05084e50580119500908030341c502 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 785813866 1250 785812616 785812631
    0x60e0f0f03180d0c12030e270619050a0902031e0106120c23030702071703071202070b0d0f0e1b010e0d0203010e06010812161101050c010213080d0201 66
    0x4402c9051894200303500c2052440110801c1003a00d14401004100c4002c40342414001d07810003038001511039a48602801001d041c00001c12800c07034400d60b001c41c880303c0e1002552503050911400c1005251159520500c212000c05e80c1c1e40c4180d6a440100301008000d03070780c0d00e06280c005400c1010302d840e0030550141400140002d03500b092080c0214803c0d1303140020702084a2200300d680c06460310b20354810039078904071000e540741c65100441c0f08a45a03003c40d4002550f030420140303601204c0000c0d41d0180c105010242c0050010807038040382507014070403200701c030340c4440d0062210360114882d59420356032200c1450350218107014850072981560003421900050014034914182c40300d425030304200c5038100041c29960b0b414801c1c00320302d030050020400380000c0220566038220a0003064407610500c3d041c004081c1c171044c102c071b4520001c1d10030100750203296610700040c0c4a0580d4142d050007810311083c400c80500740701422400c07000c4000031348103502d0603401d02d040002040480c8116414000f5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 785815116 1250 785813866 785813887
    0x4080d0914010804034e29090c091207090c050f0702040c170f0106020c06040302130f15030317010f0513020c030f0a210e0304050d1406100f050d0b06090a09060e0f0f03 74
    0xf441641f40006807580a80d40d911142d0490031032280700005a405559001020441c0000280c43c03400e03200011801c1090030329010041c0e0310380c050a0115034440e4403c0180400604045d002207601c28003600740b171612048500b00204010008480c40f03664400c000004100441d41044a44040802501d140303240c00e0458000c0743c0903480840f4401645510780840c418484c91641c0b00590007090303000500d0303d03a41c41c0e1400030301d988840882c010346004020000f044541040a030403003101c40041c082c0e0300c1d041c100e003a81006508844c078000c0715400b0603c80d0004590000d8018150f5a0003a078440b000081001c0b00160051800602e140004e8a0000124858000041244d058410488049407000c07014a40280d40c1a051030303590855004d9401070210b411414800d070002d0b1014403070440c46898840052256001540c0d0000e40b0008819001c03c2d480c1c102840402c0e04414a08000700b0000080d4039000269a050f14006840e68400d4080340700c2c8040a00017100902c101c50040e6152565000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 785816366 1250 785815116 785815181
    0x6190b010302041d15031e0f0102030112030804050c09010306060e160f0e03030714060711010b0102030301181b120b03010e120f04080d0914010804034e 67
    0x240903010300e07000c040390340300c52030100540c1904002012a451100d4003501d4040300326611140500030b11944100712008d020600070359050310300d45240550740c01a00d4130700b2600f002d0b028005403120300600d015603010380c8620b0304540c042d60103414081205442d2040840d50b11100400c44451280480c03030385860b00b130b8450382c011040f01c128580007100f446003400090071486080070040c145038106002031001c0c140400c0d902d11400040c0c07150028001201282400d95405401d00c47c01600100b0050000a500301941c03c214002080c0019040e90484007080121503101642000305031144060901e001190040c0c3d011074105500a01035000784040b00c6a59a82c0020a603421050104200d010708010f01c0c1a100200a004110303616601d081c3d4001d41640c80c2c41c0900c4c400304010320030203040755000e80c180c036002e55403580c0c03480307507050760611202000f15070440912055102900e0382c8600c0014035010030b00d10035050004104114400703124904650558000801c40741108908034602d10260 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 785817616 1250 785816366 785816399
    0x10f1406041a0f01020309040203040b01091808271e0f0402160f0204020f030f04030905060c0303070f0315030503120901060303080f07260604150b2a06190b01030204 73
    0x143e48038aa0241c0803401030f400c501175550101e8109102004000074002e0103250181261700c1c08004204841810a81341c0841592003000380c270302d0f202006101640c4e0080d4011120005040100b94a22042c0000090301e645a41406c1c050505c4451485580352410702c00c000070011045600f1441d00b070390b8424496140c10001d00c080c004281141514088d919140c0441d2001071f80491266641d151440000e1888501590154005049000042145d042c0303001210a420204002182165a81441241c007041102565000c00d1744400400524000400c02d0002443c8101c0182d80ca84d0020b0303c1c224108c00004016090701da05010003000840e411628094004800c9a02c1e00400d5a40c4881610340314414401c07500c800403904040201c03d0341e0400c1e001d0040d14201c43c01d000c410b5a46450340c00c94002c80c000c00c0e103c86410041c008001d40c54403401c1c060004030400001140780741d25802e50802c4012144418000e16002e808080c14416104e8015090742c00d0a08600b0181006030491072040790 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 785818866 1250 785817616 785817619
    0x3070b03061315031115180102100606031d070b032205060c1c200c0106030b0a050118020406140f0720030f070e040204050c0c010f1406041a 62
    0x40810340c41c0e112452046540b009140d000c0c4810704054643d04980c2a042c4001e4034090500303201c0c0c003403514104855980b1007031500c0540d0308040e101e11450800d1518a66614154801e04002407520280d50040b0700c0145a1600e0003e0a8900745060701602100d620860030581c002c2007050000107400002c1c0d0b50080007420b0001580c3d1010f649915034250341090152103407103030100300700000f4600001000985820085c0d0122140b440743e04005841d540c044910071349001c240c0b031000b10720242e00541541c08001c0004240b00381d4030349803602d01c0303c0151640008030380c640005020640b82800c0b14196504074040452030503181c000000c0c81c40d50001580c0d420b072440003c1c0400411400000d44d20f00380e0300103a42d00303000d040001c3d60031840c01c010066523010340a0b80c081e00754240b902040400c210398010402601c01c1d5600c0d820040244402080c0342078440c8140900004024240720314582181402d500160006050340c0000800c0c0c00100f410b0b00c100e013444100b004000700a900c20318520b10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 785820116 1250 785818866 785818889
    0x29040f08090a03140115060810060305070509040504060506190f05060a1e020114100f1403070f060f0915050703141c1a0303070302030f090a0e010e0f150307 69
    0x7070901c001840c41100b584090030300316070144800d104050650084024110035007011040c00e688440594100a04a45580c0c81c100300b11001c21120307000f6085550322550a140081c9060071120014046400c2038600b0b860345030303980c810000c20303051141c034070100500c00e071710f406048a00d800c81d03418035902d01d4043c940c090f4030003045040855009070b440100f2003c1c5a0415849194810700003802450000003004c01c043d0441d001c54030040035a80b01d10141d441c1940e100842e40d00380340b1030751544940a8441601071081143c00520b80d0034400c410b002418069031844100502c0780b00017451146a41c0040c00300300d070601181043d840d04a0121800184d041c10703d81c407202c008041e420214055000c2c04220f43e030385001c4c2038a208440e82c3c411250002000803141401d642602419134a00550741c0081c0540d104104004100f81d41c54041c00c00035070000c0401e689103032910350003448402c00ba03200c404041503c406004405c445116419400003e09008400c000e0308040020b80d00ea440d07100d207038502c14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 785821366 1250 785820116 785820127
    0x117060114030a170309010b0418170f030421030203070801140a0b03011503180209010302060319020f090f04110f0a02030d18120903080d0c0309060929040f08 70
    0x11020310403600320f075400041003d01c0d4405200b01034496441103500090b194640b900c0324202d8038103840b4081c600c60154050b41801c881c0e079501d40c502c174040c01c0c10840c203c0ca010b1090038003002039203000303602c500e20840901d10300440708044801c44e40307015031940041c5401802081509940103090b103045503402d1000d054110380344008108920466046442142c0c0008004146c0c00c4001d1446002803a00d075804020841c03540802c2030304a00c1e0281e009502c40601c4004001601e8100055900104007010807000c0800c1001c00710126808125483c61418001c100103403113144c50f8010080341c4c4400c0c1c82c18864221200d031500b0042c810302401000c100340c0030030f01d4034019108005841c20328035005810000c400f48082c51043c4980703102c5040310048070280120391746030b104032440001c0742d9100c0d00260401c1c1951f40d61501401e1014600c0c002c050f5901c4990000c00d000b0301400d01201e004108842c0c40c03d8242509460666591810281c0d00f2405000c1c0000251032821010b00550005189506d41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 785822616 1250 785821366 785821369
    0x100902060d0c030507090608010807050f010203160f060b030d200f0a081207110706261005041d030f0702030109150e0c040b030d0e04180c0e0117060114 67
    0x303008464030105070780c2c0740031000325005400d90701407400754089071940c00310f0301d50303581c0c04441c02c04e07090049050300e03044440100001c4c2410814400d1000d0140141d900b0004211103548050480c04420f0302c0c800000d020400c10700003144654004000180c014112100390510050811728202c2d0100c2c0c014144041100c1c0703000030074880311180514007402ea034103961090424080d540c0181100050b5030000a01081605002c1e12100c0c1c071140016000c1c04e01189044010780c0c001e0301d050401c0401610b062603183c90206100c221a00c00c0303c21801d42c0001e98100014403007100c0300d10600c0e124600c529248a04490300000c141c0d58030540d05070001d599400c45201081c0076005c003840c010300d4019030040c22584041c290304000e420322585411500d0364003010007040b0903140e14114154150704001a1100304074816120308101ca00090b001068011b00005e02c5801c90340810000c2c3c40f880c68041c0103022150170714010b2401000d40e414042e62a0201015031500c60206105403030141c81d0a00641206 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 785823866 1250 785822616 785822629
    0x4060b090f0609130f0b031501120f0c080a0309050301050108100906020702120a0b0f1b0d110a1805031501151b150b09160509061303060626100902 65
    0x882001a00c4520040c0f20011321001800440410b102140e003000c0c81e1044070b00300043d440307141680b0a81e660540b0392811a200c0c030403448190094035001e042003d4580030a80345100c070b100a1440400411410301c0e2401c00030155a0550840c0d442070f4103100041141c035100258001e0107104c0314a000840c07054502d0128001c0c840c03240f0081d00a040e0441c00300740300101040e05140d880c0580120f00550751882400d03810794a080343c03c070b03801208000700c1100b20112a809031681c0c0e0080c0718005038848500c0c40d60040390300720045500004400c2c4da100841000c808607880700030b240a600030310000d4012031615041080500174000c007541c0c5580e2000300d80384075100401200d00c0c0d0003c9284900c030b40d0705018105040968644c0c0200303041088404041c00c0c1013054038420440d40a9101e6440726101048886a000b009041c0c1d20040070320280005111401420f0f0013984a030500240407072501d048081c1d8600a4000c1900724403914000c007451240c04a0130007852044028005103000051000078203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 785825116 1250 785823866 785823877
    0xe07050903011e0b0108090109151d070b0d0c030209060403060207020112110915070b070e01030902120d0828090213090c050307050f031510030f0302030a030b04060b090f06 76
    0x260401c04241034021039564025904848203136031b40d40850307452100d00d84c00e8903c1100010006002100d418042d409258032840100d00307800c20708040d1000140000d86811202c0d04030300101d00c400a0040028005407040b00d91002d1a42419400c0040240001d2200c3c05540b0028000603000a031003030442e8071030a61028194420384040103a402200010001c035004002500c0c018451907840e0007030390f00154192648903901c292036051503a01e1f400d084403000c40360aaa281890340f25280000141e40720469201d1a4041c9401400400e0807100010b104110241c1000351280d00318003a041840c8612030b80d1580d04408400c00315502e41e2520204903030001061040308101e00e000349030740c00c00c03418800400840300c0403400c948a40703844000700001148803610441d4968001000080e0108003020703285d0f4449031000b5820b9000e6a40e0300c0d5001c00030b4038003200b180141c1001906400040d058411002c1030041542e0400549087c40c0d007034039440c0302e50080e0503c1103541c124055840d80d911402c544 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 785826366 1250 785825116 785825141
    0xa0f020d03052718060d03120b1804061407020703080309100c0e030106090204060c241b091d0106030e0c03011503060b090405072d1d100e0705090301 66
    0x880386061501c0c1070041c0026004513403003014100100c26025408034035540c003501d0000c28071140e034011a901550391072405003900521948404a240d01c3d81d03182e110a078529402040080700e0352500d0314220045840aa45030004400003405010300c0540c0041c0c4c400c2a40e0303115082580d00d8440d940400c2c0390130014407607408001e04003050b070034445034044c007400311907030055000303100c2d2a48405d0180c050340920300420300040c04c03050b8101c01061b0800d0a0061a804500303001460706110754504056960441c030700d114a41e801c2d11402d0209074071207030700e10042061281003161032071246c0008030b11000601c90308007055100ca070054040c1c40113000e91040c07040010000c22107680710a01c0001030004a100c260f400c0c03868903258020f1400d003155110300c9160f04c4009484000c3c14548a040c8a4021070000303042c8014441e28015000892080e0301d02401b9008080500160b00040118041c0c2c0000c00f18080510300803c2008651089020301c0e407c03441c40d091042c1c070744910001084c0141101038801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 785827616 1250 785826366 785826397
    0x309120714070b091e060904020f040302040204091b08090a060e2407090f08070e07050d051906080f0a1106090d1101030b030718020901030204181d0a0f020d0305 71
    0xf4030b0749588070041c040404241c444d9540901880d48506000074208000d540000041040c0350151070542c1c000d004160094048904280c1c81c1e0b00800c0417a005504614456a0b036060402201c65240c1803200d50f0a009143c860482e29059030f0070350300d840984500070302032604c8034244107581c102845840c02c0340840c4d011883c503100040e13052010782901a214580861081c0c0001f04581d403d00d180c08040c1c1c0c074054005c0c1001880c00c8201020200700030204810400140140401a15140107250140307010903880210310011018403411208140d00640035640403402003440e1500118070289019000008412042d0182000c17804910840c1401540003100b8980c01c400c0182440200350a000c00f0b90701040303824a9041815035a50366030140189505810846e0600c8a269800800344c0940602d005814960b0b50896005100a10040502c3c0d140d01c0e80c1e001c052120118083c411a038110000510360340e9140c5e1a4100081103401010f40242264690642498051002c907299841c00c041c16 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 785828866 1250 785827616 785827619
    0x703030e0a0506032e08070b0c0f0303090d0905011d040c021c0201050f06010504030201051e04030c03050631021c0b2701271401050c040504060902030912071407 71
    0x30141c5071440d41c0004c035901c50b030b141d600e050b110b079030001720400b501c1105c0c000b442d0345070804e054030071160407503403a600d0b50740b203403902e10f08121b0418006903024080d010010320016440074400341c000c14a5410090400c0514444404141d10250314088581d0040e07600240e600b0490104070b007009101400b40000c94403140a4200310365055001034030980510301d50207240e4581800444003441a0311020703000590a0101000e1b02840c1d1102c0001e0f241054489850307d81e0f00c0d661654154907503481501c03181c00080800100e03001a424980410040704e110302c1e200c40030210310f540b010450034400fa00032108a140c41c448507000d401403040ea03540001e420010703480e0845028030b03040d030f640391894580c105a810340020004c0501490178105101400e4034280e00c1c14201d6115208001c07401941c00279110118000e000c8400e1050300e0241d281c04005664075400e140c18441503443c1d40d0b00000c0500d20400802030030380c00108049800c4098101c10135980c00c414181044a1000d1122420352030240410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 785830116 1250 785828866 785828881
    0x30a0903060228260f160306031a0f0702010e12090103060b04030501020918060a03032a030905010306050d02180c0d0612020916020a020f1801090203071e020703030e0a050603 77
    0x1202203004031850342c00c00e0390407010001450f810703040c0d41c8403650203010f1010800111b01c1010300840703e4094640041c180f0b03070b03945071001e4a0140c501d142081c00c0d406418403074141495000203030f00640341e0000b4842c0381206201c440c0c2d50040584420303000400407806049036071298110300c000b40740c80b01919403203903102e05002e8003d40c0301008a40c45140600004840301005e200114031403100100000500c0e072950320207803803007084c4401d001e2210301c28024803072036840071104244080b406039481d1207510341084000340031120349800140c41140c0a5107141300594400a00090315042c081101810342c40d540d8801c8220300410b440c1c64412030030080302094556035080100e0105000f02c52030080b45e15a0300050300851040c01c00a00107800600e514005420a18040d4030100c002504400d4010b00100d00350403480c2c02a00300710306050b00042882400c42d03021101a19625030014401240001403074045d5640346148001414003c0e40c102818a07541c0e2040d90ba8006d283c05000e083e600c0c0741191 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 785831366 1250 785830116 785830127
    0x91d0f030c070503060f0c07060f0507080f13080322050f0102120705040311010e01050903192105040905070e04021920030d092a17030a0903060228 65
    0x440718200c0780325004000a0f240381c0040c1c80c0e4002c60201c0d1a01c1c183e61110601807102d130b44070361001d850081c1c03105881780614080b4858031740b02c0d40d150b903030344030f040d0a00c02c119a90402d00a0264a1410040c18194001c9900d610403242c0191546000a03501551401c440712030307a01010003e840c0740252110080300030410340040c155040400a0b11005981d17400c0c0c00c0e03030540282d01002c0c04520800541c4016940125884207015005040460420402c20002854480c006c0540036407401c070b0f41901c60802c0500c0e000700844a840c03480001d540c042d1428005d00700d000740d109010b40b4681302e00100d411a0b00031241e80f4407106c4084c1081d50750300700e00c8800c10308074452070b0740c85000120414034144409249000448a58a40e24003031468003151007011006444c603400c0c00da5a080c009000041080a00c43d080390703c3d0103201c080c000c64a8075044222140750000785180419070402c0100304080d9a0200840d400e0780d5008030010307120201c802d50f481c060000455a00751002210150404403500320 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 785832616 1250 785831366 785831377
    0x81e070806041a0703020427060f0b0705060c0f1207050d021b10110409020706060b0403051c05040e06010f120f0b1002070e18160e041101020c0307091d0f03 69
    0x8240f02050f0703140c40070210202c3c40b403880b0708080c6548107054800c6080410303034803401c08501070f02d000c24040d40b90540f4140e071f071750140d000c0324200700001140380411800b0f00c44198090341c2c2245050810000c1c184817a900d00c9002d190403e25012007000905041c052801d64403480c1c44000215100d10104103100d0708a030070700b584c01c55240310b0341c111122001c1007030107640c44080c4128a070a0420745000e190001a42004100700c52913034441e1808186100114003510055000380010a40c0d41d6040e59200581445000c81401300700b01000705101d9010b984a106401c20001e103040280c500c10020304550f12040c110451542d2410141c0101d00d1400c036400c0250f00b01c40885200501c1d411550003a0b81d20700c803500c2144d4840d002d54001502251081d0b18141b4509885416940c06003c0529105401e02007034000500ea00c52000504c4184500a08a050444000e00080c4007202c17134600005c1da50031251041540998680007200c021028020044842c0c504900886118542402c8040d03241e0b00300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 785833866 1250 785832616 785832653
    0x91c1b030204110903151008030c01050105010f05070c05100309150c320306030319020709051302010e120c0d0b0a050a11070611160602120a0204081e07080604 70
    0x1060740703000c3c0c07030040c20088922074a8010f005105030070803441000310800006000128201d002c000c00969503a050006101540c01d140000174250f04050014140060039070391601040000e2001c0c00004551400580a6a04c2220311074043c0c6c1d0024400c40281c08418001040d00003443d5942280e10915080320b0824a1070b81c443e0070611030300c1d076280b07049001c0280e45241d21074500e1900d03080d20003509000715001540135003928540403d5403d00d495101d80304041d2001640b1180080050181510540782c000304000306044808280f07400082400042504440c40707150099400801e40304100221048e07140d019140b1130038140c4900b08071002d4101260740d10031071420200000c19000765841504d521045280c141401c201458441500502244000346980001000b021810300c503070804001c0c4442c8501700c00750b40c5040c01842d444400340b004d008112007a005020a116a00000c1010900b14500300c4100c245070010104c900d10700706155000c10703002d00503502400180b01c1e07a010f508141544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 785835116 1250 785833866 785833871
    0x21b0a031424100509131a090106150e040510170a021801290c03042303070501051c0b090703020c0d0e0d02042309070f050114091c1b030204 62
    0x2560303070740d51102e48801c54000c0d038841039100c2c05100030300c0c00090040e08002c200c5100f070140c2c10039984018418542800d01c01e0075041d0f5204118245109000b443c02400361b00c1e08201d459000924041d01481d400520507100d20b444100041810782c076440340c040207010380701e840809281d41d1134220b52602c2c003008003031380142c0c0314000d441e819860450301c4504a40c140320200469807140000005405a03c641c40c50003803108000e220900081040904060001c2136400c62090042d0302c1c9241e503000f9102c040502030b80001e0300c04c00c1a60781000640d590801088200783c00740030f02580040041c10740191103035000c144001403006150345603004d0480c02310140112580715112050a4030700d000c284e0802c581c4440d11300d00c030307a00606154002040b8505200d810740c010754080c0007102c0c042c40040740e810907640e004403c10402e1200103540746008010a0904251801d5a2036007020180b0680070700350701645454110110032110541d0069101c1d402003080003842e09519010140701d003c5d8030060b81308a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 785836366 1250 785835116 785835163
    0x222031b0b0324010c060e06070f020d02070b0d0f0e011401080307080729041101080703360203060103060509060a02190c050106181515021b0a0314 65
    0x581d04481c00703416040800304051110351203038a50054451006410072007418090070024102e40252030801400300e01030842494055801411076035003118480855002e501e016080307035004986803003581c1000809a5a80c0b4101501d080039081c0e41c206166034615287c2904600700b010b510005480040c0c00d0f240b55980d0760390b6042a0340f0300414001400301c0704100711040000f09664072035003d00888012004044420240f000c08210080700c0941303900303019010030200341d070b84154002d500c0001c0381010091701c83c4000203c1c80b0070010140c2c0c6400d034039440780303440d440c461840c17681c20a0943c01803c80f603c56841c1c1c54107034080c1c00c059500c5001442401c0210321184130358000d581aa803000700c009d5a005074548070440d01c211560074144c459541c0e4017401b20361038281d5004c1684d566000d0790082140c41081c41d6040742c2490716030044242c0c40840d09086c0c504c80e40410607035094500301c01c000081d9480900010714034031150340018506c41500000d8030847c00085101103803544810842c00100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 785837616 1250 785836366 785836379
    0xd03060509180d050304021804031d091605130f1502010e0c010e01034a01090f080706060e01030c03020108070e1311120901060503190201080a0222031b 67
    0xc1628642d8031480d00040c0300100c103e44160701841d030041c002058600c804954400f0415000401c0d0b600390300007101070030416400c0b03180034003552200006888803104e528020700c40707801d100b8841e2030b0f1408001000032400030f0500c1184000c030261004140721302e040c6030754100e9042d049188004040c055400e10140d040c109001240d206410368040e110b150f204448000110020b0041071070b104c900e0044002c11401da01cde082c1c20309403040e240c00b0030071429050490804400021100c0d00c0c040380c0ea8104102040050030b40301d240c0b04420b0740880302e907440d0000b901e00030014000c40c0d0440701c5050561340001080c40b00c4e904109045034001e032119101900ca003007044a0491000b03011a80004007020318151600ea00d902a070b40b81e95142181034180030b842003000c6180c1505940f1084141e444580903c03a07864148003039000044000d0100a10340b0003640041c1c81550020440c80805602081c01a8034280401c503001030050440400d06c06552603140045a0a1903801d111458a20304d85c00428035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 785838866 1250 785837616 785837641
    0x50717010f08030a0509011b030210110c070e0709080109262b0905030301140a060219020603100e040b0103060f02090a05061e0c0303070206060d021e01020c030d03060509 75
    0xc0d02d00c1d5001452030200e88070020340d0b150703021842c924108006070341aa000101d540c451001581d10035800303882050929038403201669407800386c00c10900420800c20505d007070006400c600b280c14040d07103481690f6415205032040d40442e40207195650030001300c5001c00022840040c4504620010301c0d13000301c05400900854024401d0301d4040340500a41030f0503110b0480c0401c2c040d8506000040b40e52185951544d055410a901030041884212448000351600700020400b40c0050f01c000c00b15100c848000d40010000000c010340240c07800408210b0b6541400a4030010301103401a9440c02c5c01e00c0d00d01a004900c3c24070040e80c800c0c0c5820312a80708403055000316205454000c02440c403c5e402e0800300b01f465481030f01c42d05030412203008403070300380c41c1d02002500c0305020904c042c42c0c680c50b04020107401c00100920071071240b00c12081450041e50742c0000200002803855640c1e10010301600144c1ca4100c0c0803031080c0c1c0c50710500c0d180e010840d902d034104106547c000d542c29035070741d00ea8140f040030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 785840116 1250 785838866 785838869
    0x60e030d020403170436020a030603060606030e070608060f041811040b0307050114040e180c0604030b010b0d14091b0907020a03050a0516030c060510030c060f05090301050717010f 79
    0x103421486c04900c170f0016880760709042ca2a0451800710030a18040c80075508030707401404202d000c45d490b00801c1040c0103681c0716210080406e401c06016200c4031200290f155891806940144080d6101289075921848041288034102910030444005421031049824140307820889000d004a0881e4800c2c0c01c19000700b4030440c03006001001424106401581d9542041401c165000ca040c0b00000c5e003248200003a60140705908803d112000c01e1200786405c18881040d080e008020400c070800019004000c2141100d0300d900348a501c0d080d40c0300701c1401800300204071b540d042c2541010320102c0d810200340b40140039401c802d81898480320000344200c00d1011240e64000d82c2140280341e0100740500010301c142082441c0c514079000309032a0104403090300c86019000a0059801c0b042000040c0c8503180c3c103c5d0103c401d0100c25851070f50345014214141c0a00d100700a06080c1e02650f25000c0c400380d940f03070b00008009000300d02e03128070010561070210001043d60000c50700000b800d50f42d442403040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 785841366 1250 785840116 785840129
    0x2105040b0912190219030801032f06090f09070905031506131503050f0a030f020118080901031514040b10120c1e0e030610061b060e030d0204031704 65
    0x5007000d007010707070401220600d0543c4005602460202c00030382e005003481c184106203c0d8541c00070550550820807081212480321000f100c615281002260107402c0d00d0181c4000100e500c1c03640c8500c000041107411420301c1170b07650440d23440410303c03d44030703041054501510010340441d1814804260301544078202507420301c0cbc004142c074400704a9016190000703900e501926181622a41c1e4a580e56444c20126420304945504040f00d00000c0607804030440b02a03c510344028041c41c8420003204500705001800203008a400143c400b0341c80e4040d030091030412410712659280c4564803511100206280d0700d60a03c41d900e800c040d40ca1a01e01315007640c49108103991221405132894214400510b0720106240a00214ac907088100c403522038a00400340079250340f1521040541c0090628109000d40307980d004a000102c140712456006180c10f140f10504030191206e12500e0900070020b010712100c09480d4000055081c4c42d242071030b002482224070808001d0441c8201d540b00203841d01440c0034a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 785842616 1250 785841366 785841403
    0x3190b0a0b0406080a050f0610260106180e0c0105040b030c03041a04150c050405030d14041d040c0509010311040504051002040f1701020a0806102105040b09 69
    0x103250340c2a65004841504028100181890b03c9101c2e080c0b600114180c02c03206a4000b08051103110020f2100035080f0720030082c160348076420502e48070010a100e00e07800d60203154400c10409090800d421400040c0f40c030400340a22841c02ca031404001c0c09910703c0ba03400c54890002c27075443c0f030351190049804440303000301218150740b555181c030001c581c0b003d082500c030b480284511551814220b1400d50160b44100c1c8003030180c0031210741c400c1c02c1d600380408000034031130306100420a40d01c0c0407508070319420440c51f04500603c107061072801e0300e000e0343e000341880ba214080b0b07500c40c014200340060300179800340700080c128580d1142000080c41c001d00004202c0030090104034118107158004503013082c8035005484042150040b400100e0f009a4170410b641e05407007030100030503061a881110a42d144d04020b600c4e000b402c01000c0c02d004005000c8900400c3c50103940c2008522407807942060120000803554092003080b8180c0103003d0994007501c07950020300200c1d0320703900001207a8041d001c40f100348 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 785843866 1250 785842616 785842621
    0x210080405011b0203133f0c18150608060402070501150e1806040f0f0521041701050f131505280207030906080703021e070b090f1b040603050d090503190b 68
    0x107010303021760441494081c405c01400d100000b0803801140001e0100500031079010201301d21302c074080d90405d01c1c000c4100181800f00344045339005200d282c0c0320005a80250b554403451030100d0040c244200005120000558003285114001448034040d021203402580300b58a041d550503200d03101036030028034035005c00d1808800144603a51400080d40500280c98410310007a0164040c0071000544424035440043c00780311411101d101034103100c2002c4000c00841c07a0950708861444d1018040f44441400444402e0070400d1001d01c01a0510060700c0c00e00460070003510302c2c41030039069500c2200a180d000a00341d4100c5241c800c1e954a690141da0b1501d40504d880360030780e8600e9004d0482c40405808100074103591007000105400d8a500300212030f0b03907a02d1814282e0301801e0240c0801c41c0c58201c400e403103041503400a02d06840c160102090710350701c420360f0001001401613900007412400b071240300d039a881d50040c121004580040d0140d901400510100c1042084113207001040304a26402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 785845116 1250 785843866 785843939
    0x1e0510050324090709061b020f041107051504021c0b07080702010b120703020a0915061d090103051f2d020c0312071205040210080405011b020313 64
    0x181c01e5000c0b11221101d00a2201020944482e030841d0200081003112808101440d0302c0f201d0b0707440a94600d0804131400b0100d174001a024000303004803502c12a112502c030700c0d4895140d02110042c99021701140e11070541010b4460682004171010307480381891f41c0300c08803e1406011200280d80e80f01e25110b400b070f980c40c0d00035245004080d04081c215135940f211112075440311000070400c42d00900082c2500d81c07541c41004240d004030303040f1940b85800d04426001112140d2620400c1ea44981407041101a07601003407110202c40d445e8165005104800000a11201250f03c05540f8504212144800501c2e500003064580c06c45002540e10955503610703403404401c0400d01d000703800d12000549084894004246103402071060007900f009502e0500c100b894109480c01e0b80000c0c0b90b4010b00c442d1030590000b81d0300311541c0301160140301410000808021003940720101c0c0c103c0714120300c1448100800300943c1ca8100810300100280400008106400d01481408095004c142c5840701d40a0094 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 785846366 1250 785845116 785845141
    0xb01140f0d06020c0124031104110a050d090f080c01050f091e1504080a020613050a230a290402030d0c03121107020109060c02090705031308041e05100503 68
    0x10040b480c41e540c1e403009484841d02024003141d1011080441080180c11410480a0040c50b448d005108900d0700c0c1260307031035900040070303242d1400d0346040103501c1d0490303101020050401448001c069031184122001080303480b80c098005804c81c84002c1002c1c0d600c04034224400035050322103032840d0344040700001d040c540008070109003100e800c0640e1060422007150342e8040e034003520700726403266011644500082d41040881d50000c10ac030001e602a280c6a00c0310750300c03841c407500082c0c13584020000a041010020304410a07504880c411121117495604004009686201420700b040324030b0b0060102400460b0002e6020301c3e00100580003a0214400a43d140c5840e51821418080f8500989031454011310801c4000752100c09030b17654500c01840010088101030700104240003202d8062005611105240b070786c02402e81c10711990320703299800c5281c000c80301c200c00104410b40009010035400400000d0180e85481400e00000305500c80f0100401801c1454881c0d0003c0ca060000440300d28040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 785847616 1250 785846366 785846377
    0x80d0e04021b06040809010e010203040f0603050a0219030515040b06191b140d050c03030f0c131202150301050607110604030209070c0308090f0706050f0f03040b01140f0d0602 77
    0x2102c210298000d92000c042c10450704560580f00c45102080f800600d5170000d06102442400344091490942401c1500c0310b00c0806001d4141050b0b950000200c400c3d0595040310343c103100c0f140100e0403821000c280100544012502e55450300782010b0741940d1410107018030440c000740208410706080c546068032030007040d0b0b55600c508118840780401038144052440c41b11981c02081d90002440390a0600343c90584200b0100040010130011031001c01804801e894003c5440d0b51540025116002980315601580108800b4072404080005d9944807058541e06400e20075101c141c0003140c02020b04007240001d126007900302000708200c100085c0c500100161034070f0010051820304d5101d03000314800c00340464058021604011442d400e264018440701e600040d107900808072030b0b80340035010341c8034032044c4285410701030007054524101e0510019903a40391070040502d501d80c42d00341012400407200b0720070f401d1200c8159101c4500d5042c041b0210901c2d500c082c103841200441c81d0780b080004e40c0311 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 785848866 1250 785847616 785847637
    0x507140d060510050405040503070c081203130f02060c07140a0e0613020c0604030807020f06060a06180801020d0c11060c1608090a060f0912050601030201030509100213030c080d0e0402 81
    0x1200004c40c241d0703610311a050095002d2030003180c540e000352a20a03007113170864000d00a82e60191025030b07141c3d200941103d0340529100b2802d1901041d80c03402c04048564214002d502010100d480c542c00400000d264045501c2d55800078641074020007403049410884c000c0d80c1105200c40e002813a40e0500100011503403440c9031005180041c1651601d060000c05e85084000903540402e20003981e03810061541e50307005560142100c0d0034000300180700b03c405485071605228072044403250180004541c800140a000020b55641002e545003400400c80c80c0e14160110350715035488000c8500008440e803142c0c91036003800d0702d440c40c15000301c201041040c1080315042000c0100e00c8a54507501201070080249484500a500b400320029000341d4064000d140d541c5164080780d00860310003d99681101d4080c03c0000e0213032144443c090501c034481c000c1440c840c0c00003a0104400c0c074005a0765040b603000e80000740f100c54a80002c507441d0500d20f01c1400004841c030b0751084d1545850360040001281 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 785850116 1250 785848866 785848891
    0x180901051519060315080307030f170f06040506150313050601150206060d080403080711040f0e0a021009030c1220090a0c0e10051c061532070507140d0605 68
    0x2e0300d404162841d441088e0450000719a0003402d1a410380065404602311404100b41013980f80c40c130443d0000060040081d4032079500d0f5408249561075001c0d15441125010382c1c041d40e03e00e840c911410202c2002001114a44980d400005200307402d80021000c07043d2950180515444103020840d00411000c2c054500003070801002000031000002014001d1050701c400c1140c448540401c0116945074500c0710201e81092680d2400010100b0714054195040f1521449000142e0003243c40442c507800c001c0103c0200300010503c41841c801c8099107510030304505404a018881d0300c1107681c0400d03070040d0084920404182010110382069007603400743c0c5409244c030f8138800000754180d040c60200d0004602d0004ad5015503c46500c151840d1288881c0c00707115481c681104104004041514041003140460103010311380500341852000c49041e0204501c44a00742c007228613103038400300d8101c0d490b210700340380012210b00d8007040c14400000101101c00100481d282d04014020007010340d01c5091 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 785851366 1250 785850116 785850119
    0xc03020c100f02010c0e03030904021804090302060901050709060c08090409060c0c1403070f2a06030b030f0a080a03021b010e030a170114040b180901051519060315 72
    0x40362490a5865481d0558034104000d542000180c21245000f0700c200c00c120201c905079074540c800104a82025900383c07001665000d07484071124058501c008042c0c1d0003424151b14905155000031041c4c0101c030360000070400c2c0d454000342940c0c2040c0511480b400324062484c4c040114030307004094640020013070700114801d0a0790381c909084a980004403004103d1007810380d030a100034401d0700c038004610240114648000c4c1d0301c0351045045007800c0101204161203001c0052001e0398045004c0101401d14000d0903034880760f01601030141118000e009204100000e40904030000d00d00154a400c44106480e0580d1400c0881c040e42c0b10000b118400b0340352100c020f071110300900c500203c10451790007440c0c60303040410006110441e000740d00b002e55140c10005000b00c0040c803c040c0b80442c400ca4000482032410001b24020070000c249252a000444080000160041d0003051249000303040ca00c460303d103da410000300240c0d202c1c01d8034160074421424020320f03009502204916140200f1010182d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 785852616 1250 785851366 785851369
    0x30c040e030c0f1c02011109091f1805090102030402010801050402090f150309070b12150a030f0309050901080316020409140607050d0b01030506010f120617070810020c0303070c03020c 81
    0x2e16030f100240d484020180503402d0410020f00411280b84028000713005840c4082c1014015101d03664400c00321240450b840141104c0c40785c0e04140d001e051401c0342541c03881403040b140381d602c1602c10024109400102411410700c2100d2103654140c503500c01d10313401c204c01e000080d0411400f903034021001480c5c00081703546000051814000000070b060741c82c50701060f91810b02c82e040d40102c0740620184200028280c8446005502c80504101c03d0300c5041002d002a4045980f40d1002d00b1031240785006100f4142c1c02007294065542c1581c403000701d030b40e031501c0f040c3d96445050300e550031501c000710102d4010300d05500020030160042d44050500341c9044001800c0190654550300031540c0080c0d0501034242d140106100a0400d007001c02c60361a120740040c2010088800c030508021203a03003c400d10450580c09200506040c1c1100390081c00382e0103005e9651140c07070041c07040303902c10141c010400c0d00c070b54000c88180004001c0030f54111349800300c003039411034800701d0100c0942c000e03100202000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 785853866 1250 785852616 785852623
    0xe0d05030d150f0f080c0f03210d1d16050102120f040b161e021c030918020913200705150a290108160c0c06020304060f030b030c040e030c 61
    0x40c0140c410304d004901d00d0012810b01e8a402204241c1c0036920344000d05400b560041031614000c1800c00862440ca07c070300c5102451840750030341581c200d501d040d018841050116000c1402500740c5811146034450001d203103400700172680704030350040c0d025481031b030301c03e407502c2d4081d00101da420350a4505098403005085034640024500c8901c3ca03200301c071a1024000d01c500306208070381076007500d8000d26007180c000c83c00083c1400318141014105c01900c03410103109505070703001041d403c040a42140c2c41c84902c800a58480404e651195404d14a82580d280942c80b0300141500e01421200701183c28660361003041e003103071130300751407600507a442c0868210400100500c120304800000036064010716004003080c000d0844201c101000d0078841080d40d07004100280c1042c0d03003030214040604130304800c231800d464414004000582840002a00d65000801741081c0c0d51141c035003030702d0502095000c40071901c40c851003e078558042c00c542240c5007096803007640c51216075001c1c1e915125420704031515 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 785855116 1250 785853866 785853869
    0x21303030e09010e07020c090c09030105010f090e0309102a0c0509070804030c080c0f1005010306242106021803070b0c07030b06010c0f0c05010e0d05030d150f 70
    0x716007080c0d0a0349451600784070440c05029030030290105401c114000a54030550108610300601b120740104000360008016111000b00080092000d5a192003558141c0b031014031074bc8501c141407064400318800040142c40744103602409c402c0c1403040300d41c1c0850f012501d40c0d490341d010518150741c28800313184510421107401e00908206801c01c0c6888280103041c10018202004c2041103018000000d130310038091900103412080441d1210341c1150a1802c01000850030b69461050b00b104181105607600124101d0380682c000b0840c0b103032070700c0d00580141c00324980c2480754039036820309005079822002002481c07141020300259075075180e07660404030f1744001c0a00041054100d10315a9a04d820490400074100007660541842000d00d013195603480c882c00700508280c0c0c01d40018071181d100340c0c998404160404001c061910300d178200420b10156034002c29001801031740024101c1d0401c4c1d0601c094140e80000210320b00021022044010021880d5017200308030600c0c2c1c001031000c4440090300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 785856366 1250 785855116 785855123
    0x318051e0604261005071b1e0318080606010f030f0b090a0212010b0a0c0f0203011b090f0501050a0503190e0f0c040605040e0601060f0302251211030f0d021303 70
    0x24048080700518920740707000162501071145c10101000f11560f44006e101c000714550000b80345100c17045203004400d2030215000325501380e00003040007044c59805800040100c154500b69503049490b00d0045440300b0080740e101d0301050185610402480c8207600480e41444400e500040e05490380340000d44c50710b010780c0c1c40c84100343c01280309014007801d051030500501122295030b261581404014000403841c000280032000d6484440c41551000c0d007020040301424000f85041404581c400b410b410f2080c0184041e00708000c3d00400ca0354080d10444204904946546043d0b1307030313006500080003182001451a4035180c1c0c4134141000010003800c4102e400031409060301d000e084043c441241c01d29402541b065042c1032007800d0031a4080f9885040d42c0280c034240390501e00902d01540a8410345400c2c401c2c1e89000740b1881440c0d40b244190303d0b03405100d8591f51381000c8214000320b50070950030510940d03c0e0810441400c10080359801041c005900d004d002d03040c04e0100208000d801300e66130003074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 785857616 1250 785856366 785856419
    0x80c07030b0a051006021f092918060c0a1107060206090f120d020f0f07080405040612020f100c0c090b010f0c08040605030601030f090f0318051e0604 66
    0xc4010060003101c3c1c0c8400903800d6440000c2c45c01a00a42d944040140b000b0303032095004c9401007601c07a035003180c501190807041c403030700d0010400d0f10b450003130386001200c00c1200f054502203091481712010116040c0d0001d0300a000070384030701c80c0000e40c903801000c0c1136040c04415001080300749001d2141304018200d9402428981c80c00f000418144008242800c0700d5402c0420041c55034141907047e00e64074500309500603100c40d80c0d100300c80c02c1845000f0000d13281c0140071813000c0c00c1101860040080d10b009403824040a6519420080504c0c158840294800051030310860ba50401c2c20a80300e0314460303490842c20400d40c13521600700520303068001c501c0d01611030206540c0d658000c5d07040449020b542c50003602444540d111070310700340280d00403042013240010100740941e210380c01a640d0040b1080d010401140f5070f1410103290103401c2c130103c0c080755483d42141c101360b080061260031aa00170f0b1440b420228540003551030598041e00c0c0a9002c1001d000c0881c20b0b10f0041091220b80030281c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 785858866 1250 785857616 785857621
    0x608060405010b04050a18061d030403050d020d030b01080406050c21040b060a18150504020415092301050705100c020601080709020f04090902040e03160b01050a080604020d080c07030b 81
    0xd00040e80e83c01807100350f00300d0130f00c1160b0500a031510304030300e540c9411502c000340d2703143c1401c062000041e110303076201c5441c440420003100340280442d00c445000c80c01e4084420412010b4800c1c0c080c0d909400f8514041111303003001501250098215607031110400034640c1c40c1c04a032085800224900075181000b0200810400080000381d855850700040c040354000d03e840d2805042034a040000303000e0038102e07501d44100d581c0022142d000c04000c0c000c002c00640d05d85484e841040ca050640000180000c0c0c1d0030480000c400c1c2d60030400c403001d1101c030804821030306803110043d20350b0b070f01029084940c0e200c4d0240003001078005d0311a0244032400741e03014059551611400324a07051458000e110858410030881110000d03000c2290102c3c0c070032180110304e2080038000a0018040141d01e0369060100146a0b940c2c02021800c02e012144100811a107507601c1d5024045021100d000d03405481c0e001c2e1010401520300a031007420094451481c980c82c00c0030f000507142c240405580101c580a000509 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 785860116 1250 785858866 785858869
    0x9060203070e0324061e10050a022a120a080f030f07050901170c160b0a0e0304050901030f080705031303031b1109100902030c0a0207050108010e0c030a0608060405010b 74
    0x10628840c400041c002c580c050648405004e44c2d0207000203114000d01214030b61031001c88103c1102c181401004100340c04880040a4000d03403041d85600d0050040e4404800503055442c0540441c00400244001400001041c001d0300860002d00040c03910a1a0b40c1c800041c1318003004000b1345a00d11603990f220b050a44001d002e03000d0141008050280901c00c001542e40c8c007000a845031000250454041e407114061620a482600e08032f014135105014410f041c804071500140c01050740700d408000c031540c100781c02030310b81c0114000c10764094007000c010404a520314540c42000e0b401081d101e80b8000c2d95680e00e5117954071180c940501e8441d4403404000385504102c00b503a286c01905603010513090256034030300c41e0084941c4490f10426000300880c085000d0300f05144040d003245030045581e8145808090003c0c1c000300040001071262140229032544581074141c100c8091050000c001d48613140712070f04c1354000900508a156a1383c50000b001c1c2c00400a01d8041c03400703a0000901c684140c170 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 785861366 1250 785860116 785860123
    0x11070b0a02150c070b04030509030a0501090b15030318060405060c0a03080114090403080711030a02060f0112080d0b13020f181e010c05070801050405160906060903031209060203070e03 81
    0x102c80394005400c420400ca400d000fa10700b2501c82d10390140129030196141d2409032070900804180a4143c8a910340c140b007003140c154848039589008440071403241d5110300b0908081d109461515070150402d20104030401212202c900003900e0050800f410b003034640001c603005400041c80010310350300102d0424103042d00200c0c07450140c01c4805030400070311030f143d010801214010304002d040155000010b00300c81d02c15610b80981c50040c105580ea2001050030003507480205441841c10300c24488000100709880180d0000c446038800400e41c10a50b0801d041d0000f003440d015440d800c401001035202032920b16200a04800000c007260644a012101060a00d1101419502d0113110301105000d04a071064000b1241c442c0c0900e80401104250700e421800d00d40da59010040e103600b000140400c00c5400b0408035009001d804201c0111956548004141e03542c9204840202e4001340c42440070912455081c04050b85200c3d01080400d103079030b43c0c01d0490703004480010000c4c000c0b5003006d400e4038050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 785862616 1250 785861366 785861383
    0x150d0b011d060a03110310020d0603110303030601021c1803060f0c0e150a0c08030a0203090625050d29030c24160503040803250b06090711070b0a02 65
    0x44600702428580301000c42e54070455800080d1020322a1410791040b65420051501f2100ca240401e41d1030b07101001d4800c0140500340412100ca00d5440440081c2e8200001a07a1262307005900404412500b81c403140d0401045411400801100c0c4114400c00c000c0351f101c1da0000c1d0311039900017038031500c81600241101c410302c50f07510412041c051854190341e103000030307000c0c10451007140696a4401c803005a03507030701900390002d04044000c8200502582c040d805144145d1400041d590303142d4851855010b02090040150710f48a00011903552031031064019140080072034100081e0101980d180e1f9001c241840e40c10807622882101c1107606040c1071003486843d09003a00c1302c420f51038800700c0e10550036031a406402c4203600701040d040b6003101603000d425111604801030304e42d201d407185c203a1501d079840b0380086d620240c405c0041c0352a100e1502250a2003c1d044001d142090b01e070071041104490014005904102403000d80c08840c1c9010b20500c0014084c40303000c65a00c071104000a401d15900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 785863866 1250 785862616 785862659
    0x20303040201020a11040902180a060f0b16030c150606020c01030908220e0c0301030204060f050102060601120b0a0b0405190e070f031e150905061305150d0b01 70
    0x28014000140d03000115205040d6210080c0e55000c81140d0116008011400000e54003100d403400b154001c040c0c400005001e900f01d18024401d440d02c400e4019000800c071321542c08a1a020030202c070141c011101e80c65030103032080c60304440c003c4070754456800d0f0703100303e40381c032038500d40d66090400c016501003003038a086e03000a00b0144041d0320030703480b000c40358000c04084404080c200e06684010031800246800500300c0944242441d0400440c00000f6402c2400124041c0b8904030000c210125141c1d80c0c0c802b2a10168003e00041d07503050011510f82c0402c220040c603a94450854810301d5a8000b01c05014000e20501e154645d0300d401c003002001c2000d2000a00b10145030303502408420405005c0c50b5000c1c0c401d080c40303100080076010860040100300d101d40e42c521f6240c004a00d030031000780c1240f480107108004200945440c0c41c1048200d8000b03850310340d80010a00741d18107140ca030170b0304901c0d8040c0320105040e1151340c40304003099203aa07049000311071600a00d801449209190030201c14010324 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 785865116 1250 785863866 785863873
    0x30506060f1c030e060d02070305360f0d02040e010f14090d1413091a0f03100f0f0c03050708150114072402130509040b06040b060c0a080904060602 65
    0x2400c11101a00c420080800f03030130001c12442c404595160032045480b00c2c0f1403202e08540d2206c00d030070014466040604503901c840802011030940d40510703600c001c2c0f1a031404517240000d020b99810460111012001e060708101503107207010240c1e41c4c62090a041e204041c0000c589801d0303d44a100456a0782ca83c002a6440c4500501c03840303050000b0007207440000d900f1f000182001081d005d04445c0900c401c421140c2e8200d500200300c3c00070741d801c500d409081e24050210a801c401e000c0103056880005950b030540d124041c8442c140322180c2058200c00c20a0800284014816004c40c0a0b90841008000071984034800d1050301d0384c1c80721059a00003003000c405081800740e140020840d11001c00074a4002001294817400c1c8074090003181e20076808814005080c02c8901c0485000c1d4004050342400b8036140349002034241000c000d00c03441070380d00004501d000d035151001c12004001075031060f90420024040c0c005246010468000d034a401507030002c1d10748a0b00401c11080e90890b801c010704540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 785866366 1250 785865116 785865139
    0x71704081204050a0605070e010e01300603020310061d0c0414060c2b02030903030f07030302090604090f15050f0d1b091406060403020a0b03091501030506060f 70
    0x19003200c155207518901190340503054685040061810015940c0a8880c0c3c0c5414103000c4c0268114442468400703086e01e4a0484030715490043d40c1110185c80302490541d210012094090824501c1030f07040a60b802000800c15100d402217450306080d00124900640d03542070501400c00080d016040003007a001068000707103082c2c605100c2d14000ca100e10040184c103030ba00d459140e5100000d4070300c40d40c00d243c110f4080a0260340220030303140300d900c800c02d20344d00200403a0244c50b1000c000c031480f112001c2c00540c90051502c150b848242c0c001c10059003055401d12a6172421381d40c00b00100b00411269102017951031003841c001c0c0488040443d00e0200502540c8100216103946030383e10700e030090450700300d00200160b0821251b04400b070310084440740d203c010042040400b50f8030002d8110444060100195034480512031076210b5408041e6100081d0142041035100f03005c021235003c900d5509a07680d84000c030000b24a45c02080c1c01c225030755000141040203038207211005180c9a41304441c0310340c414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 785867616 1250 785866366 785866373
    0x4020703090b030406140412030522021c0b0c030a0608060714070f21030e0d170405030903010203041505070f050d180f1218030506070e13060806071704 67
    0xd2a00d0301c6500c0c02c02c00c001c400070341400010340c4040740c0180c000c10a08546e01e1721345843c0c2152500c11001c2030100c0d03e4000480c1800d410300008002e08118200710a040c0441c940820100100030050f0350307200c1165903144c030001011004c0d01c90041c960f20180f9901c030f05000c40d00900341c3c1c00301c0c0c1214496074410800c000d038207580405e00054000410741080c1d5176400354140f40340510041c000280450590b0403071518100c0c01c000003100b210110303560400c6802d00051205031110b00b60203461002031018407880282400700380589800c00c1c0300c1e10840b4980000e20b80400d0070780e0411101a03c600543e04460302c0515414050389900c00294030307210806601f4948007030701c1c90041c9100f580ba0706664103440e101900c803100a4410a981144d85171500720114600072100403a200e4502d80064032220059100c1381c54000c000e030949921502a003046e0390f461500312180c4020150440d407003116003450b01c5407511b8611811002d040f84002510084c42d001102030104c00540c40b02007c281f14010410012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 785868866 1250 785867616 785867627
    0x5010302121c0c140a08031b1e091c0c091d060109020c030408010603081b03180904061b0206092a06030a02070c0b0c150411010c02132904020703 64
    0x102c03a2035040c9041e1822140c184060360344501e521010302c0d44940700e40f81062000e4240030398803603004035106480303000341686460b8039030049100400c4000a010301030002502c1c103c015204000d0060200107104d00c4200d000008144600000d80c0c5522610600f880000114041d05c01004901001410039196102190b540c0c1d0105105441d62140d0214082d4008030081c0101c500070140700c4020b014243d12410245269030240000c402d103010240042c0f171a40e1000300540fa40050903030b45421520248100f03000894500500880d070303569450214102c582980b2110007a10f4403242e006020a2425103012440e21421035090f0224407042007104035000040009204091002e4815945a0703c4400030a4040d01070703844010b0811480316000314088401e0005401a51040b80845409144018841d0208501654003500821000400e03201950090550444035480034003128071015130014071100f22040140081d169814040148001c1544654108900c8800300d908518001856801070302 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 785870116 1250 785868866 785868913
    0x140f090414061c06060914090c0108190e0a060c050c15060303070212010b0a0321030b0d2306070c030207172107240f050408040611120a030501030212 66
    0x80e241c64000c582c08001945d0050300003000300e0201808024004059184000340c1101c2000f07a61044a0324401a5072241541500134000e0302d42d4610001034542d40d410107488e107130022104c0d5115403140707440018400e2080d0f01c1203c2045e80d805445d000e01075100750410b64403110441041000c40c050000c1a5008400c403080e05504a88451011030990b840a0261030082c010b668040700031440041803061400320000462211409035224256060040e030465040404e0107402507403885010300000c65864207000d08a2004101c01c000242802d403061411070700725042400180714004031820190100b003413a002d40342c110300c01c1c13801866244e0655a1141090b60742110000c0b080364095400840104883c0c03184d07000503501401241020715405c09611400020f02040d2516107241d503030300681d1080740d00495004881c645000c2c9880e0044802101e5481c41101c18081c68054120b201001c07401444884880d4501251961440c01005298010114042500d0704040d4070a480701821046a00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 785871366 1250 785870116 785870149
    0x190b030616090f0605030405100c0806010f020c10230403050a020f01140a0810060e13050a0605130f0e030a09120f051e0c0604081c140f09041406 64
    0x80c2a800c0e52042102c9001440d03110031002c00b03000fa00443c0840e4000001e620850288045881ca42c541c10310b00b40440380030310700d6980003a2100c404a080d661040c8650b034100c90b01403040b07403a001820800074800000150031200070400b05103698074540e000c0c501c109a101d00c4452054241440d5450311522500d800304000d01c182d20440e1107081d07a0380500340d40100c0c40f50300842c40e030b204c2103038060242203160182c4501c03045100d0440002482da209001503c074502c0080c0c02541001c0e800c11148014100203445002e42540320f1201040d1030b210b2048200b14901681000b04101d45001103a1045480c07042c10f030415038100300030700190f998004200f1011030311003010780e5541103428200740740c031907881c3d040c01080c5018400961140ea1502c0120100e060360380c40c00d980c1c114071907408000451060384202c90468200b480710410200b050079640659104a0602c42880400b00d030a000341079102c80483c2c0303500320002c41c60319181c1c1032902c03410328481d1802420058504100700007800d48000c0c0c40c4480e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 785872616 1250 785871366 785871391
    0x20a121104050603070803030109050402032b2d030b0405090705061207020705100305060108010b2a0f0106031401050a230a15060306061107030c051c0b0f190b0306 72
    0x380d05511304000300002042d0441c00d4a48a584a00040c0080c0000703440907071081c41030360314601c1120324490000c081c10503152040d01c007141044405842140a0495100c3c030840149030054103030b0441200230003810300c143d034002444030b803d03410041115005482003005a004100038001a1901c1080b40c240005584042c103e03643d60751005c9283c081507401494029600314000d1a00c140c0507004a1300800c4c00762201e81050b81c0f034850144007030040541c0c41186200980001d0010300f0a494011490340e005030a03501030a400c004028255100d5a000f107901c0d02001c88202c5480c142840b409810030303280d4009104410310b100c0904a400343e491120141c1a809030003054600c41c003076124042100841c500c0c0300c507055480c00b01800405482c07140700b020401102e0360b0f00020700f01064020581c0d038845410041e02c3e05290500820030b0140710203000300b01040601101107a400e140c6584a1198a1184903a0340f0749000c06501805030034600586440c100110400640e07004150750307510842d800c1d0705 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 785873866 1250 785872616 785872621
    0x60d05010204081617010507140901030b10090806010608070c030e040f0504060b13020f0a03091707080a030e01021201032006071104050903030403020c0904081c09020a12110405 78
    0x80d00a22580c1c0c4442d010f841128240003207060200c034030380122000061508807900000305020700340d400c111065800904620400c4070300022080141050704418900000e031041c41c0380208504d018111100d4010440c8007904001e00c0d04200441c501500b000e150074400c2d030901e50300150140d100c542001b828003003540d0b001d50703151300d555000e0360048170941c4041c441804c050034a240102800d00300d40340a540f400348070228500940c000c131881074428120340342c64101702d42e504900070614044125407a44518018420240c03104016000749802800020713950070310044042c046402e0071003000824cd0040c0a025400c0c0000d485030783c11039410400b640b94169015031650a00c07409000c0c589d510600100b940c40510201c00d259829040041d1001c100c941c81d1900e4050341e0b40001c40d00200160b020740209145410039100d0150071502c244483c80c01c0645003d245966404521072424074540d65400d01d506510340350084000a003515002d4400c80c0c481900c845121440c07000200e4080d1b61603802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 785875116 1250 785873866 785873873
    0x316050d0510080d0306030f120201060b070b0603060115020d080a24091404021e011806030509060c040803040504240f1d1006081302120a0213020a0503060d 69
    0x212a52203850303400802441c41c00c106242d56a001d18090030405104540e100d0051354043d106210035680c03c80404034062000755074801c018511f400103801155200d280c009104021200036010061182038620214036000342418581441607004680c800c211a030072401854022810460721361491801d00d219581c2e43c04440c018050903002d0340c082401a10700c001d0181000707030751308080d290420390920042680c141e101c80c0d01601550003a52106280104103c0c5181c441301254622006051004140c04041d81c034804900b07a030f9201401291b2100100401008280009544650625881030a0030700305030300c40d9a00d00860003028060366854642110080340c1349191003841e00c940c4807152a440d112640342800e0041172084610105042d010760b010064a450020b100e031034052a680b4040c1e2030190b04031034059010b01846088441030451002681307800d040d5510740100c4500500d800300640c412701c0615161801c0950950384103010140c070240e8003800702e83e088407048980290300021b80c00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 785876366 1250 785875116 785875127
    0x2f090109030c090c020c040b0a06050c120d0902010e0d05060a0902060c0601150909140411040e070b1809090a080307090e09062418310b06010c0302030316 68
    0x10005400e0030b50900002420220940101d1300002e4541c1c00ea8140f0302e885c00c10f00040d6102c00c40041d500c1520341c0d109210451048010703004541041e011a10382c000340002d600056880b00b880d400e003003030303d618091082d542c01144403c413001c42940c0103003400e2040d444890322400301130315008040742c45001200640d6110b4003940c003400c09131400e84030329580d60018031007400180810bc50108040210015440c410792060703030b80c00801d054064020b82d8540d0b070303011a45106568455449543d443c20400d00c03602c1001010058400490402e03642c94514210803c00c40042c00b1551240c5100d0040080c000c501040e07030707010340b94000c020a88a4564000079100250a031304200b048441c5036003048810307800001e12500440c8020300080200304030145860b28020403c101c1038026415400b110703056000d403c1c1003544038403440c841d1661201c441c40a0f0b6011410042a88000c1100061000901c49803401c181e802c0a000d0904500400c1d4603a130194a038080103040010040c901d062101082c0d0080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 785877616 1250 785876366 785876369
    0x31201050432010e01050102030309100b0a121b050f130e1f0c14180f010207091415041808030c12010b070312290a050a030f05012f090109 61
    0x180000b0308910707098502490709009204160002e020000001003550022084a016200b42000f4213020042c2c0b1040c2806045238440c1c09801030f854140c00030b0401c51642c58850510322410502c2c1c10406040b02020300c00070303075800c41403007130100c0c0d02140d01958407402c10400300060000d0104002100c108010304110800305000104a543d4803561190110396011400b07401154035604070010704925a000d040c0210148408814018008400e1078540075106542c0310005104803001103403129030610a560601b60750415403850042400118013008800146c81441903600300708ac80300880b0f500340c000c0c040303400152000e40c0010200340c0380303a00d00007100c011101050075007250796519164414158007181041d000168400100324562841c1d000d00e0b9450040400b04149507401c2c0125210803c80c642c0406a0083c08100d00090a4a56042d00ba0085001c0c56600e952a48241081820748606000c8940c130342c1e86a000b43d21072100f04410040100c1c0016a200d516190000c0040c3d440b516103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 785878866 1250 785877616 785877671
    0x12051011040819020604090b0d05030a09061b0506160c0204060e040605060901030b0c0f070c08031b0c030601060503090a050f030901022a1017010609050a05030312010504 75
    0x206415684400c2880008004a904003030803107180e114040319520021401d010001e40c40b0318108002c10a110043d0440100b105004000c407a2141c100d503211445c40d807080d031107400498070a032030410801c3d030440031094036001e24200c1170664500540d14140c0380d0800421440341c0380e10760840300950511840391062a654058420091140c6551008000301030481e0100d40c03070ba080c03100182441c02c041070303024100c0360b200b103040c0081d03116800c240044e90010020b03612090010303ca40700c00304444081d0320005000c0d0034040c42c1d80d9043c400d2550b61040d82e40c2e09155241e4030654025601d500c00140050440e240740c0f81140c0c0340e4944003c0203040148100014107640308000502a04c001e000c001814118026021034400d107503000c2c14049541303403020215031540c03031072071598480b424000d401004140f120714220350000c42c0b8000d038503008402a08000001611190b0a2000c1d040180562010301021001542008012034541d031404005006890040d6110f5070810301c400902d000a9030070ba0035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 785880116 1250 785878866 785878871
    0x3070504031202150618070806040b130b010f02030406121a19060e0a14060c0c0d030e130513020f060c1002031009290126070e03030310120510 63
    0x20079030340003552041000361101070a04c104000c10060300e1b007202c00410101c00c40310808070f19a500f14056910400080003d0341094881544100319501c00b0140c20950001450009584840700001051466078200c0907082d940100f1047c0165074004099541c1100c0141001c1849000300f409030301c08015a015050300400080c0290781c58200d4a600c50058a426581b40f0480c1ca0340001080000e41c2907109540010781c504901c60b04504025004084840180c41201c0000c00032001007800c18480441c164005088408011034915010300c848125041d1820248040d08010320300304482c10b0031683c020f110381000c0e292004191214000e64815240e5a0107440340030100b03002990103503204031000750540640304008584400c1034860b0f00c43d20b140c9036484d000c032180d060034014006400c00344400d040c000d84001000c40910301c0400c1c00640d0991400004050400d1130004d0608903036000c407188a83c005000300080c44894071944c4048950500348414000100d040c41820441c80403038440640b170 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 785881366 1250 785880116 785880143
    0xf1f060f020d090f0e130c0608040b0c0901080c070317130204110c0309010c0c08030a030c0f02120306130b03030c010608071e092315030d090e04080307050403 70
    0x10340000345103403220225001d40b0400d4925810442d0200914010710801001e41681440190025001c586e1310540c2d1040c985184407443e02c2c0c410020f85640e004000054580d0104010020f03842e03152038000c0b81c5103210390f00f00b0314103500191031070358010198440c044000c961303001898401c800c032601403000100c1414650500b116102080b8a040e141640903c1c10601441c003c00301c030404407050000007101441c00d180313502c8011036011540020a850000b00e50b2800300740740c00240010080080b46031400155081e0f01d12004d001c8580c20304180003550000c80b200c0c2c84030322102d400c0382d5201d8401c5801154104810010100801e034100c0207070340502c40442d0b6048181415808031041d034859108580b401d959548078405032544450968038181100501007103035041540050103106c5403004048404418444249420780d02214407e51005c2c12800f031102a00f0140003560100b6100c0c40c110481c1400c1c910071610304000540000d01c0d20307a0020005a043d445001035034061540040140b1148 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 785882616 1250 785881366 785881379
    0x6130905090d020a051e0a080d021b0f060109020a171005210d0309020409020402070b01141203090d06090b010605031f03020f10090b0714060a0209090f1f 68
    0x50608840409182c0710307031606071020900019484204c140c1c894000c01244140c040326554014500d0b0040c10300e40304001444000070310301009060008020784005072205440c091004003070240840c0c0f0069904816031070040303144080b070200c0c199408564003590b220300312401260001c0006070010140d0212106100080c150048071400f1030303004440d0100303614851a18183c84404140c0300e030640764004456107262500171b4021841d960700003840003549410a8010500341d0b4090700040702e61903c041e00510050703801005000b01140159040b05190182d01099640c030b1041c0060301c0d10414907d10300340308000aa42100b070855034402c500180c956581c800c003808640068805c141c00246940704150341c804000d04200449800074401072486180700c040c840501520f80021040100c40d0b0800f2402548a00017000882d05c40c0d805d00c28503840801d900d80c10b20b0b602405000e9464010001e81510365100300002d500401c0e81c2d16401e211b600d600c01e0098400c0038a4008841a40e940d010005e01c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 785883866 1250 785882616 785882621
    0xc03030601031a0310060812131418010603050415020a0c020d060207081b010624050a09050405011418251b06050108060906010e010b0a0908190213060807050f061309 73
    0x211f44070881180c0348200e1810818010b40100b12201d08426401c8508001840c0e0741c24440d140050058030f101c5001106a501d8040304c034007600901e010030341395000e2104000d2a03000c0c04415194201003141803c400e00740040c042c041c031510280c49400c410b007000c414416180d049505555100c0d504507502e02c907850f241c82d40481d0545420606520b0004005640420f05801948442041e6810140403090060655054110109a030100060840d0105080e1218812103011f1310200710702c08944080038081203041c003008010001c15184142c20311002500c031520303030052442c500c00350440c481c0070f26404540d02c51228083c0013601c81071100000c1441300303c1d03001a040c4c6e03030060207413110b07030342d460350040d940f60700a21680d003076400341c800100590403a100c00b509041c2050f02c5d1201c2006e07500c00c0951b25210100344480c4032011560f00c0a4110b18084101d0659047d21210a0012515025505803201d184d8894240248076030b400e81c1c0c10b030b90381c0e000885201021025211800d19102e1503c40c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 785885116 1250 785883866 785883869
    0x6062d0c02030705180601110a02061c020d111308031905300103060507020f06060f010201110705060114030708070504112a010e0c210f0a06020c060703020c03030601031a031006 78
    0x46041844030492086012403444a12a0040c10706460301d440300d243c2e0204cc0c898080f0035004039a0034485185440407a0080c1180b080d00c10381030340d444403040322540114030320307035803015000d94010003000e11654407000c1c038921090860704040d0348400b43c1000402501c5c10301d81d1200341c00844030006080315075501c00f01605a03409020100656915848282e98405407042d045006130f00000008510b0b00d0410422403000c081840041034a110607408580da94000280488641c2c00850040c0480c542c048982000350340100c000386030491400c0341a545501031402954007275600c400c961810011a00702300d40d010039803881c03032100d84800340c0301c02c40c5280c410f18807140c01542018241041e0180c00240e00d12101c04c0140202d544411503440c1980b88010b5415150007070191407500100c41da000e00c070703102100b406041c000d651030000086550501c80b00801d40020305105110349905031200000f942c0c0d00000070b00b8002103004c880d460f01014075003c254010743c1486905000030310a6000d801040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 785886366 1250 785885116 785885119
    0xa12120207030c120317040305070609150f020315010201050c030103060e070e0a150618052407081809040b150103060306150503150103050d050708160606062d0c020307051806 77
    0x128001d4510640c3d0940c46002e41f00500003400611507040403516135403000d0b00707941c03048801000c209002074408003a20883c0f0300c00361342e507a4080200220400160082e440c5944248000c00003481e110541103c03500040c0000303440c0523600c200301d020485080008101401c3e0100f8480c80e10318011448402410920504844d01410300c100015041d0007070088200b080851802080d000d0b08207030a00c00700c03220003552410426408200031b07020a10590040100500421006540741c049010a010843c00d41d0600b90007004003c04110124402e10700c0d0729000507442152044c145099001240a0300305504040c140f40d252800c28520000c0800020741110342c1036040d198550003c0c881c03500e010740700b40310142140c1c02059107071400600c17074802401c006114003030290903d84030800c00100308806000c2124250759821003800419002405040034100300c02c0d40c00702c1010b8212400495440004c806400e200f40000c5040440d507081c0007640c050318025150110210702c2100d49941c100098403c40d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 785887616 1250 785886366 785886377
    0xf0118030f08060622050d061b09051c0f0209072606150702010203041212080a0e0a0b07110303090c0a081b09131407030308060a12120207030c1203 65
    0x81c50418000d800c11485200c1c02009142410060100c540420070448003200c0e4858001c0720200b00c0750f032000c80182600e8050440043e507000505840c1840101c692018014841280010480b07640c075200300c00c500180c1c0702c1400e05000301b81d103000b2650460000000b0360007276081d01000351550b8001ca21440842a1012803400c0207503c60300c001810000b606c400390080c1405000c2c007031252400c4024140a4810b104aa18007940c0b200c026015043d0f0600882d540303c41004c144a44990050a060b002540050304010601055183c281d88070079018004142401c0540007031500d034018168641c09021400c1617030f5a0749848440b00e034403552803a000728441c01d401000030540c540000341000718079080c0311030032540b21004400c100360754800a009225407900b500400c0001525842103e03254450701004007007850440c500503123104401802030340980700c0d40c1d104000d81501002d608003480d803c40f421415040884108a0074034409410151680c100100001855a0ba075400310b2035090080e940d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 785888866 1250 785887616 785887637
    0x80321011e05210609031c0506061c020412060213080f0d050c19030c060c031a0d060f051f0b031006030b13050901020d1b200f011803 59
    0x204002039841880c0520404074005000600704074140c40c01c81c0c0030715414241d03000015502c0e5882c000c1c04503041d602941001c5510700e40f0b006409a540031b00031001c2418003452803e0008950a80503112400c07100301145c3d00800611140c0f94110340c0505103540349170901d29510704020003e9405801c008000d503070111030000e818500480c484000e025207001404654410b603008403200e40101203c0310090183d980c041c02d48014824020701424443d46600304a8001802c280c000c49404a20110515003030048086d01d40c0881300508085c031508949403140000681084002445c00031075a040c900e1400e8144010640c4104c17000c4114030000160074005920341c02076041c0381c00152030164001c5202d0109004460103500070703241c60307940a400c010441104a4403001030781c0e02610054a165030000e0025203000740c4c1d00a41c08280644c009040f034110071000c0080076191510112500110b40f0418107024036410300240c1c0340020014024030411400c010b110141c011072100407000300c2d051041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 785890116 1250 785888866 785888879
    0x150b0c0c041803051e0a17070c08040501030c26040b0703090f111c11040e16030b0612030f030601120b01090b03100b0309030408070e010b030a0f0608032101 69
    0x20744800c0020b001e2003215125200c0e901580c0b190000d0118004204402203012102d41840c00a007801030196a5407003907149a40740180b85204000e04148200f114900c912000300742c25a08807401c9420030b00c0d00094451880000721143c014103407011b000c1d0140c0541e074007160f401c90490140a540500340c0d100403619404800d9003140d2500c00020010004144d41c800414040000006010000b511800c80b2145010b48002d00e032881c0c0b14210f5401c22440c400405a092601c600b8841803030050080c50100031012030381003052440d1100803c4441e501000a00310b031a40150f44102c1408281100e4076000703000102d6515400880b002070001300c0112220150348010700549082040686458044509000c0b101c00140c2c80207140003031941000b18001001e41100b0011403017007010502954845041628850800d0011750104c5241e6007508010b001d140704040450360000e0400100091100300043d0b5440a84102d07405850180404668102000b0102007250701480b1112807028250703817201e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 785891366 1250 785890116 785890121
    0x1b12090a0507120f170f0a09060206150d06151505041503021204030c020324100e091506030709050f1503070b0a0c060608011503060624030f150b0c0c04 67
    0x144050808107404d050716002c64041d04030780380c00c949002c04c842d142c124071008107142540b001c260300c00040c0c0250760070410301e80c0c1802550b8001d8a4864035110000074240050945a1015400f030159591000c50b0b980030458280d842c0c004210400c1d004010403039140000d8082d0b00584200140c13501118404404580b02c2d00c01c41d80c0072146460544c5190312075032021901082100740c01c0703825110720700d8100b00409110441407079208100d49191945d01c0e14204155101c005a4400785501003001c0510181030b0b00405c0405810b002c5045041c00341c1d0340c00303000a1425120b0350010410b00d10740300030b00c0800c2c180001c280e4800c000c15404502d01d125560709143d40e60b0054441d50035000404e10a4000f001e20071205000c54902035000815245e0310fa0030511308544214032500404c0010010400c00c10149000f040c0080054901c2d4080035551501c3d407206240007084407200f0599140b8240c12813440b070707a010981d035600040c0c00210381511441645059804000700308954428070112215510745070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 785892616 1250 785891366 785891399
    0xf1a0a05010515090f120304090e0c090f04030215010b03061c0b0118060e090a02030d020601060e122b021e0c0f13050a0b12010902091b12090a0507 65
    0x38103441090590443c08031210340090704607940c40310306150074500b590342e12024400d070840d041c0042c2d40d032146401064401c50b03800d081209056040740c10040d500d030356408400c0d40c3c0070140c4201c450a03596585404c07030406101005009250784c0400012544440140185128860a6402101d0004d81401713024540c10541030003055800d1000060103011041d05054000102801004c2100d03600c612403031031808011544003810794080c05001d0158a000c0000484030341e06400070300020750519000900482044c1170340381c0929911011109034810070042c5042c580011498445000129401400303041c8031051903500503c56401180071115510081c0d49010740c03243e006040d1940c408081c00701c20306007a0314481d40842c00401d024140200c1d40121482806881c0c00080c5840c00c003c208221582d80d920703d80d91a0b850201050010384070803540940140d080c4a036001c0c0d092081c80001042e12901036820416030500043c0b01c14a00b0005641c02081d00c0b0b0f0081e02c0c03040e6201c8183c0e03440c06005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 785893866 1250 785892616 785892619
    0x405030a03065d0512030f060d030c082b1a0907110709060315060b07060515040603080309070b1603031e0203070e1f0e040f090f1a0a050105 62
    0x607100000c0c078035880080222140f03444802d2141050082d000000a900d82c0641c100c911054003880480400509210500355500014441420350a000c41c02c0b90702c092000700054000e08200b0040c07410705002c0c02000b10781c41c2d4002074080d5102c4010f092241a004200009610f03003440c0030f564056110103000b640c0c0b5640078600c003000e0402900080284c25140a0314140910600040029407418240060701c060b000d02400401d025185107402042c04902e0f4040507001490700c042809645851000c58084541050300803a103616289800f04c000c1030b03040c840c660320a1034a00c00108001c15030f030240d44120003030400e8544050380c5158054161103058150808003880890400000c4e0003584000c525507000c000420650b280c03428080101d91043d6004c0c00892440c807402042403506010500c540b29511082038200158203401501c1030601a07121032059454540034a01c0d407801d580700c00540c07608440c400c000c8055904001d0300000705481d000115400100010f41e8010441c01400c0c120b800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 785895116 1250 785893866 785893919
    0x901080a0c0e010c020f100203031b0403080406230c0a1109100b0d0e063301020304060309170a0f020d1809020f13060905030d0315030206031008060405030a0306 71
    0x102c14011201e10b40542e400703c2e88015141c1640d1800d071030b0021103640d4558550029590303410501d54020120244031003996030210200701c03e0001602903030696003141d00b40c0c03e10404200c42000c00b12004401c0700101d0160010204000280309400513400b24080e000d48044000780f4451000d100c0030440890380c5280c5050014010080c1400090003809021015940050540340440703003181092401d880181980795040c0c80d19000290056000c03e5980041040c54404030706180080e440c1e00607031107100c06042d40c940000c001d00c4104600490582c0c410a1003550310216814098504002d50203008014400c5080c2600000d01411071100b0b50001c411903001d11074038200410340654404e42c500c1041400911610071204412500e190181c1420b0301d4550307a15040c101890f1900c0b03c0c9200a00806043c11461112040c046510105494050307a4082d6079545907000300200a000d0792003854207104000c00c04c0300340070022028004680e44d07503030103222940d070741c4101e8444442e56000100d0600d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 785896366 1250 785895116 785895137
    0x22107171204033e0f010c1a06030f070801150504141906030b091e0a0f0206092b0201020d021f11070c030803160305010b030f092e0e030412030c0302030f0f0901080a0c 74
    0x61040d241c0c5940300100a00301c9401c0d4010034941030508183d80e118637100c2e9107032020000c84140130041080a044180d4040254250b07000b2540c0600e8400b07040d11180d42c521200d003920500b210381200002e150400c038442503a0a10a59590f40c41903101d0301482118014414180000350100e24840c12a402600007251324200d602003245a034044171071154401c0903407119464440c000340d084000887c55034030080030000300c0d000190510190300402011504140b042040c040c480c180f901c07210489100b000500c580c10300b110f4000d640320381c05d006400458141400010845040b004501c01c0182500152aa05500c031081d03007654002c2c000c01c4460402440050000103241c0034603036100d0320100c111401000018001c0016000e00c0d20014808000445803100d4003c00d80a04942c0c070180c00300841c07605203409094594090440c034001c0410035010300081c1410302c20070940b034101c0950180755656045c0544800003035444810b415020031038810006c3c6a0100612071141c5070b80c4107440750040c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 785897616 1250 785896366 785896403
    0x90c0e06010306170d020f03040602070b030c07080f043b1005061903150b040b070c0f060903110306071407022107171204033e0f010c 59
    0x440208124100740d6601c0001402c2c113055210b0751381a1640034040d10700e04c240340200a0600900000348000c0307070301c1000100060355002030a00104c6200c03684e0039842c3e4540e02038503902d603c0b030202c001d010500e0201c0c10400c0180c03540000c1c800c940c400c1801e0160104d401c0d901c21039200c1540107031030130250610b050340143c21503869499885500c000c40986596141c5c000200c2d188c108008000b4030309009030400c6034141d0144109140c2280c0d00202d00f1000e40b0f00454002544644e001b20314808401049030b20421621545070382c0a01605130351000e08545a81c00240044802c0c8010340b210500c03954480d19a003404901c80c3d016042a54980100500680d25114180d01192040341c00944000ea107070710072100360485d00a0318440c80e001e000240d18054041350b100705c0c0031294980035007288400b504140701c1c1504484c1102d521111104540c07840804c01600251303c4240c2801d0303000302d00700d0340031624140004500c04400840d640039140b40c40d030004440311409040014180219108aa40714 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 785898866 1250 785897616 785897639
    0x308010611011416050c070e1e100302040b031618110a120c02030f130e0709080319171801060902040b0403140c1f02010f0e06040b06011b0308061201090c 68
    0x2020301c0d13418041c3c82d002202c0b28aa07d8400f00c0c1c4d006082d06e08800d03080c07082804042d60f50000c40c0784240080000382c101440302c42d10041081c400244036541c0c403d0480e0854070700b440309075601d4105102c0780710859590340410070080c03010707032041862a18280040030541c0c00a4181c40340440d0541d01c4452500a0420391001025464040e2055100c18005240004105001018100019185c00060506d40020038611020190000c418088400000c0c082e2000c0081600c4110340804444070013110300301e4040d87c40048560040c144500300d00100005048201380c4140c5d0450040003c0101c03640d0f511202e4102d000302d00a01c0b4002d90100301c01c10103e1203560b941b0300100e01d0203054a49011844d0300182689400b4600240364960032950590b20640a200d01c0c512030040c07000600c0031002074254161100070003040104042821800300312580d1283c3e504030404502904800d418024504000d072040e0070860b6428411310344420000b51140042c010113900c0d5a102c3c500b5035206007003100e9441c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 785900116 1250 785898866 785898901
    0x20918062d070519031b0f02060c210411090f0601020307030804110613090c090303171312030b0a0807030c0e130203031b101a0111120703080106110114 67
    0x812106001130a10b60403080c81441c292415a00c0000381058100a070100081c007501140090013503070030392040d004d1340100351300307900280d683d00482d038600b036008410410b20000c00048001142990030401000050030802d40c4110302100c42411650701d811a00e0218001100d8031401a0400c0c8041c50000380560003464116100c0d0099443c004680c03804244d0580281c00c401130211011142003103c5031840c800c4048205c01031401154590564034090700d150031400c09001d0b8545840001001d126082d40c0045031036a101c1e1004460301c5020780000d01403c1010441480f07900049070000300c2d44800541c0004407030340004c580324a14642140c04400c0e0300300511003007031101003101503001654140000d103501480c007094004c40080e206e120602c2d1811850071400f09074600800c808030902c0b00c403c104102002480c0415402e07003030000447c280102900e007a0103502002c0350900170183c0007000310307041c3c609540d81d9040c6941d004414500341c0c2c1c0b054030008005200c00380416101030140c40140d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 785901366 1250 785900116 785900131
    0x60a0512190809010906020111160201020c030d081e0f0403200f010c080105100905090a06051c03020105342106090c020115140d020918062d 62
    0x1908150a0000008140001c80d400c841d140c2e000603040041e5030300056404007410582c4020403c09840e000104541d210b090112a2500b030000d83c81411a0710800c4202c10200c005420380c2c1c1c914551904c003429660043d200e1943e03003031304c140d41500080304006400348501c001624010503a10303991000d4a10f50070315041c007240c0014a001c01c941c0b0304410031962020030000c42c000105801c400e10024507521068111501c035100702107032190100e52060300401510001c5a07290308175200d01d5242c10040a4507401302d46c110071503030800350310031030f4220080b96200d00940080c000b555403159491942510007021700000801d24404c61056501031030450114022070a080c000c01250317404620b03111800d801c401034411b407101c40511410031540a50000007065000074407444800394180501ca0405014a059580320301521410071760b00c06602c041010707009059542c032820120721071a4105900310341265144914400b10340413000081a20002c0000b401311842180050182c11107061001303403604 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 785902616 1250 785901366 785901373
    0x10e071e0e090a03080a0629040f030f060e0a030c260c0a03030e0c01120509070909030c030815061602011206060c030e030706051918030605010e0a05060a0512 70
    0x45414541e01c01480d008800c028000c0c83c0000e118540102115001000034241d9401c00c0e40c10400501d01c602810004501c06090410400c008440c84100e030007103900503c44100d00e040d000051000301800d8005803409180280000414084c070a0346d940d0b60144000d0015255642d01001318941c007215032007441da03004851021480400ca0202c840d08010024111904090307030b0740c800c2503014480c0c0800720408001401840c0a1140040e280c21852511501002d40340c000051410710244411409020144403c00c0740040310b0070010f00c4180022001c60108030310b03d01181e80401034004808003230308002c0c0b01a02c0c01103040700d0400c60100f0964100d06100028000a000510501480024258698a060201c10903003401030a01150240d00c0d40203822207141030103020740c130808884031044c072484100c0d40513a50040482c0e200880001c20201000340700380c040100402904814101c401110804c0c0c5252200c4d40d0020443c1c00603a1a15401950b55404100c14100061764945410751001074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 785903866 1250 785902616 785902619
    0xc030809070605031f05210118023a030f0801080f1c05120109050901180503030a0506060714010c0306081c0f17010305010c0311040e060919020c0c04060602010e071e 73
    0x324660350064595814120b002d00c0d47c3c801e02e0b420034401c90010440310885c1a6031001248c004c0381411035180024441d0540740c850480758000c800d803410710000c02185e00300141c40305900f40209904414040b200000d9014400084d80c22030010309400c0c4941c44002802d6070080c0c400040000c0d02041003148288001448910040c51020800038020516088082a23a20b0316510150845001d0560a0040c452400102011610020980b5030064942ca400540b6890349000107086010305180203100400b000c4000c5d810010640015680c90095101481101c2e200c00d81c0d552141c1e990a1443d0702900c6900c0039207039240c8900030000c0050a5420108584840c2d0389403401e0b400e070240c02c1074034036a45400191164503410320407003030b1a00940c07400b903050905204400c649820040d0a841c410110034001c40e4501d442c403d5195103078860020115070342c03110300340c4850f00c034000039101c0e612541c90004006412030042c0507601c07002c40150084e0405a00308a803480359090482201e044480d44903d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 785905116 1250 785903866 785903869
    0xc030e0607050127030c02060702040e0d0f02150702100b0f04060308030906010f18020a050f03090f0c0604060f0c0f050d020303040b010b040e04020f0d02030d0c030809070605031f05 80
    0x30000756005074000301d00514142414070203200e00c1298891030202102c00f40c00802d600450070080d443c0e0481e540fa0b5180e100c1d0001401030030403c1c583c20304500424900f0700d807854121030264202130054080d241000f082d00351030311024104990600241c5c009600c03849118406902c54a50103100828031040d05111001103011148660000c98424030300100380b0074240420020f0702d005181e0030200041160401c140c40d000c00000100c10079096402040640105006005503840400162091612481c0c4a6105075541c52044514001c5000f605003614003420720070200c409651554440c9480111980000c941d0a01040c001703445018509030400700080303090096140700c0c84a035005545038100360608548804c4183c0c4000c0740c120041104103c40d400b0082c070164020340440e001400e1030600c8000c02c3d0481c90104000758036010341440015020342101e030301080f00d40640e451003031a0b40e405954946d10720103800f44601042e41400010300c070000c08114511228529102e00d8841c654420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 785906366 1250 785905116 785905129
    0x201020715051f061101060b04080c1302120f1510020607110a06050405060105010f030614010c06021909061701032a09140601170f010515090d1b170304060c030e 71
    0x1040704000801c1c011408050174030074000c0e01c0282941140507458a072404030000e075905040200705000b040c03000804101130007243e041d6017a00322100c801c2001d0f40313044665060b9800c0101c07050420f0140310f030402a018242000103031400a0f50b03400400303807522030b510240c49280f07041d030700c2003094810a50b40000090f01400b6841c0200d11038402045154101000940040e0305014580109450540c081002e01d4286900150802c400e00741b130200c0540c641000d4002e440b480e1580542c4c110300006414050f83d01c1510441112240e9407404504801c40c8118801d109003880040c20600c1c900721100e0702024034021000001400304520408940d4035545c5800366824010180c906410507800c0115658005000c41413558420300c51038002d140c103491492174900180921800b90800c2c24040280d40002401c842e90f080e0020400c1c500c0c0b603110b1801403044d00303030b02902d900c3c42e02c138452001404185075407440c2050880707803000d036040c1b5061070b400301c2d96500c520505a08024081c10420083c3d1201c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 785907616 1250 785906366 785906369
    0x5040b0f041a150309152d0106030b190902160b010806010e013006020409060e0a0b09010f060f02030909150405011e03080c010e01021b010c0201020715051f 69
    0x8414000100d02c407007084401400d620010107800c40820030400c0e41c4001182e10745410b91781080d07002c1e180d00c0d144aa5100c90320540c1640d01c43c0340314204039240e211180701c007090480e0b0a81ea000c0c051080b5050500a45181100400140c403010f01c0c81400303c540c190700500810201c42009003001101520f40c601418000c0e44151a90307002500140801410140d00c18003601e0794002072864451418025040542c0303000007100781c0c80301c0035400f40401c0306d1501150028035040c001031080c02d40728040030070191170648d4840000d500e00f8680e10980d0602c2d402c00b5040341e005002903000c0501d001001c2d2045001518400218002001000900c2e916400c105000c0c8860fa0441a5009a64000d00085800603000044808000410703041b4020300c164003e8250399100403401d40318242c0103100d5000d0110b0b40b03110790301540089500c411240800c2076041e00c1540c0c080c001e200010b24854181e00301c0c8a9840d0103000c0d8003135620304140400c26900200d070001d002b0207259000280c07200c0d400c40d414095 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 785908866 1250 785907616 785907641
    0x121118010b042306040608100e16030e1c08040f050102040b031503010b0a0510020721020114070b010303110307150507171005090405120403080d111305040b0f04 71
    0x7003024454a6141c02a0f501c408590041070b401c0c3c00e02c03150000d0000e00a910410041113180b42c00030306a0106810290000d0400c0c42ca5010366082500c88000d00049003844180003a00c2c140d2000c141d0540003074110010544004842c102d049800d0044401c0c01e8020000e41d40001c02009060001d842403009100234003118015646a0800d00140c50114489004142c03003a81440c14440c02c40d620400124111b071801c5404078861401c071001603052010960000c141e01c20446000b00c1c0320303e0240c480c00c890324400d988000d04488440c078a00b0140c090910068103213450b5070014000240542c03495580143c41108076414981d44c3e5450005400260302090700c555218018005450f0f04401c00030700c50503402000c0c03011440e10301d800300d20160151042503c40d045034400315007071110501003410074412000d0310565a6490b414084d02c103600c810001d01516107420002d07154020b45005690300c04401ea0852070070720b85000d040202a00040759405e0340031510364a42e1000d651240303d000c041104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 785910116 1250 785908866 785908889
    0x80c030703030b040b0a050f040906050a0506150a02030f030c250b0c0903060c091215160801080a020f010207211a011d1e04060905010501050a12111801 67
    0xd494000d050f2504218424007070380c1000d056015658814088509860003941c15500c0e0007640c2e0b0008001d402004d40c041c000516210501c0f6000566410075072041c001641d003001c83d003903429900c8441344502c6000c000140c000380310604850815600541d00089075507046410900c2004c03c1100c0510404818242401140c8036901045810013941d503003d441d9140351400c0c4031a030b001280e11400014250b0244034400a0038240d1543d49220b040c0c42040c2020803140041d0f00340c50035400551003030320818005600211010803240c1300c0d41a01c0d0581c1c0980e0094040d820b100c0e03090225005e500d252403070640c010b40d0000300f05e00c045401c03030008803009500d440002881a0a242da1000c080a0702c6085039074101c40140941400c0c0c00102d4960460580b61900390783d28106e051801a001c6034101c04000d08242c01d0000b4003000da044400400e0107203000b0880d50b42e130740c0c04014001d00f940c070030b880c420b0300c1c02d4402d8008515660a6107100304009402c0c165004d050450901000b1800d03003040c0b11000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 785911366 1250 785910116 785910127
    0x91805060907031a010c0227071209020f060c0718060906080d20070803040e0411010905101409030102070f0b0a0207081602040b04050702030408010c05120121080c03 73
    0x10305840c08581180301c42c02c1c20002a20400860b8101c1300c0f0401c030300c60501443c0200482107442e40d8988021031030580c840f0b180030a9800049180f00a41901e00200007800203420340300751400c52003181c00c0603600403c801c04074042c2c0020300c02190070011589143d8016403c0c0010285105550100e100e00b070000002219800c00c0120343c1100d840303403c6500d40783d01503842d000c07010342c20048400c041200c40303544811040800c9402c80c90241c00c1e4009901d940000b0400244414a40c0c2240340528812a402000c000c1c01d0302c01107400c610507102d03443c0d00c41c2030390440a032000d014007204c0d4801600104680d14008042c00420b0130780c1e0000c6022240820001458001c3c400881500c582001c048802035140540c1912100b60360700a2008016046800c840380008540e2154071589076244098012b20040c0f80880c4040d4907604180b29402095090a40031824184aa021114030504800407610140d090512140207100155002c8072040b601d1a26840842e0410002d13116103091280195a02d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 785912616 1250 785911366 785911369
    0x101e0f0e01092a030b13050a080c031c02090315090c09040b07030606020d0504031506051804020a080f030706051008060c0403060c0509010f0c030315090617030a0909050709180506 79
    0x1804400600b400034810010b040c40040d49141c4c1c25900f040d80d41c000d512081510713040250500c00b201d80014027071035000460345003088010018042c3c0009d00198150f0b001c548240c1581a881081e61865054001041440c3d41035552200a9000300255086403030307240da20b40106004480c01d4a06071210b40300e030342c1003201c141d0b07041c011074007e01740a2010384803150b404400038186010f40c1c00004c0040325840380a03102c0039041e0780450f000b80710040107503103002451221040100425207081e4041c0d0000760000c1103542d00020309180428900005502c2c04045032915001804064038200320f030146041c00003034a02d02009074038012b800b112a025902d03803039441c5c450100c0d80d40070541c0f41449400e201d50b41c03a86c0e070030142107900d01069040c203800785200c07483d04800a190300c4c0809900103540304d00100e045080c6d98000c1e82030700d041c0164445240155048a0f41c4c80c001d0300700c0d0500280304010700303011183d0f00c0d410090308405581031500783e0039201d130043c80c2d50400508580310110307941c030f041010300d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 785913866 1250 785912616 785912663
    0xd020102280815031002031303022a19050607050303070f020d1205040c082a0420070c08010516080609061e01050409140405101e0f0e0109 61
    0x80810080c0d012455060402002e020030000610b40c2e00300026000c00780c4010344051181c0c00000388540411076403450041d00c01c3e895140e4149080e0010700c51003501015101196882a102403581f48180210f140358008121a0700383c07103541e8969000c081c0340000740d5922000301802e0045c1c400c601035500c034903040400a00300d9401c40172410440d4400c00800c0680381d040b81c02d20010b0350741d02502103000c1c0c0d1641480180040342c1d501074641c52260300020000d034100d2101c0021640710204a1403910020001000181c604114010040b00d862200c046503a01d03944c4000e11003688103e4290703208580d10f801260840710201c0355680ca038032000c0ea208034101da121a04550082040302c0400f514100000410103600f1010721244070003484c03038101601a80079170f00f80c030f004000c0160103110541c0c055642080200c0240c50442d003a02c130700d161708080400c00307014003902a401001a910024540d00303440e00903241c04010701d4071aa40e80d10005003c1e00c3c080c060700c84039038040e620f9081d0890500385003202 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 785915116 1250 785913866 785913907
    0xf061002030906340f03050a020102070c290c0309060c190c0302181302061e030103260403050c0f04140a05010819020102060417040e15030c010905030a0204050a0e0d020102 76
    0x418a40d50280e13078002680060552103c9600b5203070964461081c03100c10703802840703481806030690035002d0000402130b0740c03150a0300c01880000103a207455102d07043c7c0b90669009500340700086410920a809003420094058400c000300c2104a132106000c41d0f0b88003d03640c1c018042030b60b400d001d1a905200b1f50070140310711000010915039104980c0745c00c2450703c4009a60010081c030132140015035200420010409003004c1c40c81d040d040d0703680e580d240350145001c00c6484c1c03107000c01c1d440c0c800311700e8001440760150f50460350840c0c06802c25543da0301c20046410070500d01d06500503550038000114604031402248035450b400c10004507035041c854458604000340700125085903c030340c01080141d0780400c04580140d0320200a020740682c0d00100c0134140642d812036032038003054404100018814406150001c00b0640554001142c08001103401d2606401403541680c00b84881c1c1006051690000e030f03004405640c0002c0040748900c40d6810300f00041e8078040142c2d0081044400145020980d60 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 785916366 1250 785915116 785915197
    0x15050a060501091412100f1d01150303121e020a0215010506070f1a070f0908060622090c0605040e060d230f0a0b010311090f061002030906 61
    0x9840a160811103c01d220900c55a40d0059103220070030045d43ca41080b0140340c0134811841848016003000a00004152488900715076a1010010005900042c418450f4241603d00e08000c201d04540f07040d1042d44000320213a2440d5076401030500100105401c400e24040d00c81000340c8d0300c080c4404000d1901500d4000c42419020600c01040310355070380011100025070044070496003a801c1c0c101a04030344175814000040030b0505c400c00c01150342c1b11040e07107000741c0552140c2112a44a1386102c0d038650703080312180d4000d14040d1030401882c5c40c3d140e1800741007010781404a03164025070b41c1c130604902503600074804644042003c2c0081c00d5180d044039030240d015102d203450711041d07450760440d00030f00d980016190b54480101c00100041840f0500c05008801704403019402240b80c2000c40c1e010900c0300f510b42c5901201c0b20441c0c0c1c503021a4480c06000076000c00c40040d07e51000b00301d070300e150174810744055100400c595900d42d16a0000341040b44411b0704030a1a002440c0100140048540c0004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 785917616 1250 785916366 785916377
    0x9081209190e01150201111b070605070209191e0509010b01020c1e06072f04090c09230c0301050108010b07050d0c1410050117150414070315050a060501 67
    0x280400c9142c0e5500b5811540001c0b461001103204100c240c1c01810308072001100d2003800a001c0d1168410005031055505540086990031070340d404044819005200f00254400c400e8804144164411500c40000001035000010003000082d2240010a0744903c0c50341c6046d15801040210310007840b03541e540030001c4c001307401550a0040041d409100d003000209410607007015001c01e6454001c107450012341c0c0054014040d044885480b0320b130004116000f10070202c101d5800c039480c1001e0166188055120352400c80080c2062040300c040c044180001c08541101280684101183c840d000d004148211034541d595042c4400185902c40580043c0184d1300c0802030500012000100f03400203490502d0210650b140e949071180c1d0500a4148201e094030400140055203a52036110604039540510485041840d0f086500d03115140b28805c01c0c954000d9100080200d90200c0e911240f40c070142c800e0f503004030b440b682c9503140c000200c40803568490b035176010415007107018425203000e02000d00f0311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 785918866 1250 785917616 785917619
    0x412020f0703021003020c060403020109110a1202040b010e030312010e0c0f030408030c07020a03060c080f01050303070b0a020f0a18050a15050901021f1416090509070908120919 78
    0x1480d070721103140c48001c1c0a00641c042c81075626100c0d40c10b4640d00c0f071484094500034101824024060030543c4000d8958043c60030440c040d919080050303401710b41c615040c45041e00455020400100070b00c614081c1800006020401c4644d410b100504000c2140310711101c840d41851080b01000710010f00903080ca1b0002c208840c5607070240411350b680541c0c8140101d40c0c9a451441c0d26256000d110340094005011030404000c10186801484404419545140d01ca503130300c0c400b94810900030b200e840e4140c0c208000000c086140c400c000703940300040e9a03000d45401c140c0b0403441c244d07901c441a1080040d44c01202000b0003150748108000914044031020102c50910079241c0c20a18a12292010702c080010041e04990080c44180c00303454420761421032200b40ca044203009080554051601d190300103002842034020300c5180c5102214503613515241c9420701c401d01010b048044c00910034011020310003d59407008005446541c00c804520350744a40090701880001038400c1402601d5800d8050f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 785920116 1250 785918866 785918893
    0x130f03021f02070b2106100e130204031707050d0e100f0c020a060e04150810090812010807141c1b1a070302150408090915040c0206041202 61
    0x305a00c41c0618a201da01848049000760703d4101d0940c81046401c00216200c19500d040000320070510702200c3c0800d000b83d48040070000404004220306000c075109484028032410407000e43d0101c400e0079034005183c0358980c1ca8072101c01e01400750204040e44005400c50412409000c0320361003c025041484041c8042c07000511120079240b003500411018090124a1038461090061002c0e00030389501c500782d446182c014210311103104064022030801003060b80201c030303280c8407008881108010f0590072141d8440e40c07010b00b2580c04142d0b904401409151890300103058491300811668004043c0c4515155102800d22690132506218212103020075004100500d05142c02c590f000c04008040c00d41c44210340000c41c1d541d04103803c541000803407400c410707999030f0081003c1d0303010b602190003000e0003202a40fa202c2040b28018030b0800c09025040e5603051000305550020098984441c014440401040485031b0140080005a01600602040c0303c2c5000751003c600c2c40a00c0034020705245001c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 785921366 1250 785920116 785920129
    0x80a05071e06080a0f090602130504060b0703080c03090a1401061a07020603072703230d02030d02130306021204060f02041d0c0405030a1401050108031206120c1302130f0302 76
    0x28000c4c940d0585901503000c1ca81061382c0980003c03a0721a404545070b40310403000070100700f264007519000c0c40c646107020407000c0450f4240d542c9141e040d9240343e25036690043c840607a41028002a501d440750a940900040181c00d114006410b0100002885442c0c0b06402d41800c2418070345d001d10000421a00c0702588400382200c0d4050f00c941002884900003585000c41d84500010100d8050a80b02e8007000b0402c08a4100030382c0074003c8500e4a103080c43c02030315034070744084005003000342c0e0003048100c4542c174042c2c010349410380002d0a500d02c225602e85522050781d0100c048054488205820031081104510466502c1c4201520440c20703d424140034408220415411581c0a0802400665004140002c030340203400050159503000c0c150b4606041c2c6442d505040c03280075400c183c008a50300400009031080034019403131050003038032030505101840100c214005002e014107200140d41da121200352441c42e0a4210005a40d03031510495184040c0f141d80086804140301702003000035a6502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 785922616 1250 785921366 785921371
    0x30204060e01031a0618153604020301090606110c0901060c1e0c0815071403041a180114010503030a080c0d0c0e120a0b0a020c07080a05071e0608 64
    0x3803c1c0000c6181a0318402810958141340b4243e001000042c410400f840707424002c80650820798035820300b000c100050001f6405000f049402e0a104208281d110100107001c1e05050054581c44080020351840400d081ea44240c00c060b0295480e00810849940e110b9403500b001035410014149900341807002443c00081071140c03004101c200804039044c04006481c01801c2035008509412985040ca40404200494800c41c00c1c0c40c040d2900d040720000c008803402d845060140d8501052620341440804103800240c41910011429118011541540c010050181c03424121080c0302c400800c0916013503a058102041c104030004004000c01e0f2000000d503118090329050166907903950749041c0343c80b80141b24940c1145428a5610a6081c3c0c000c40900d0041030191120b035410709004000b6581c4840b1580024000c04540300001c801c0901c59000d4072001c0392090542c0d01a5540d050744030326040340b50605035a07d80000d9000c01c0718030802c8040c807a40c00000380501c1c099a16110300504502e200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 785923866 1250 785922616 785922619
    0x101106040b0603010b12070e01050a0311041a270c040b0301050d140a03080105180402061204150c020f01060806010b16030318030314180a080919061d01030204060e 72
    0x104000b190071503a007900b00c0410750102824503154807103500c240d40c0d5100150300c145400180300000118003420070051240a9a40040c5809001c002d407405210042495184138446803e04803012803e035901c0c080c41e4184a8100c140c5d030360b8a03c0901c43c50945072040035010003a41d5404000c204196400503083c1c3c2d044400c01c440c03034401600720742003000c02d1088409400f43d03070b8010440aa0105030300132040074103880060300c0d503070111544c000b11402910780685003c4d42c4110288820700e01d80b11405c021542c01403003000c0c000a01341449240c81d0645000b40c40d5400944c04c06488201d801c070091103100c00a1180304018003165151104001c402c1c0710324001d419101203a220b41c170003414025005030b03544a0780110042c481e203007e800c00400a040307200c0d20005108500340420700c0030652603184208244081e002e01542030841d07550300040d90098a03001e41040303520051507000343c01041148010046500c4040314101204602180b0324842803006043c0340c418002401120b5020814034180c84c1c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 785925116 1250 785923866 785923883
    0x10b01120b0d05030406080f150105070f030314010609030b0606070b040807032d030c0f050313150f020c0d020d120c05190e03070602060f060420120610110604 70
    0x4a004101c0342d0586960107015444006070002c0c95690100d10f84e8841c1e003c56418200c0d64542e14400171903403200c140c059000072000c0c131601001c100141c42071211980709003000901c5a82c12080c0e20034a5600b40d0104e00401c81500e010414004100706240c1d100c07104403145460100c807503aa0360b0351100c000e04007614051001c61040100750103480300740d4030082c0c0c00b2064030b14150248034030b030601290751010314006424810343c51020303401104406e41d0780480740c40e81c605550341c0310f10040c0d0406866005482071040f04800c00100c00c0309100d0800c2c004c042039130150b40c401007041000c0c03410056802200440d440300305186603903503100c0d1407500d440c03601c1040824022a4104121010b001c1d152300784400c138454050008099400c4072160307206807416000ced00d081950307849041c0d8071035a0498910020b08055000030700c1602e4583c1c0321802c40003010b00b4411079581d4402005149800043c00a40c070102c6c20300921406180c204441c034810360746440c1c070740e498018001c621030704c0704c2000c3c10003001e003003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 785926366 1250 785925116 785925131
    0x306020c030d020310170307171c02030109050a0b03070810090204141302090a0b010c1104090503040308030402090609094c0b0415121106030f06040e010b0112 70
    0x9062089842c0b00305882c400795100d060481800c0030703000301c80c4030b40c1152081101c2c1c003a00900002c01a208500d80040d94501d003010341244001035035215601040080b2401c04035108a0641440a9400381c0651200003075585003000c103030300882d072000481030720a40c04407004004401001071103038420100c40d50302007981066880424041d08058000703038504440c44082010380f8800b40c0803581413034001c860340d450360b40f11a00a8001c44a0381300040380029202d118940116802034012440042c010b0400594000c01340c0b40c2030b040d034100d50821a84030000105100561410144a038bc000e402241c22600b14244480116070312480082c0d20320b105181e2403041941c401c860b04a54044900740d00d59a10180760f030340d920100201101008152840c40c044c54000c05007040e220b1a0100e0400301c0e0f0380030303666040110300050003418503012581e83c01505002e8030103803940000b0394010b445484081d811414031a040100391492000b4892003a854440200750702da0f40800f105103454220840003503c00b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 785927616 1250 785926366 785926387
    0x604080316080d0c0e0f0405060d0807052506030b15030414010b090c0a0210060503030306090405030d1503033e03040b2215020d0809011d0d030f15030602 68
    0x103024143e80444a00e14101580c0305198020710401810301041b81c0c00c10f005c00104041000f15013083d0780c3c1c160082402030181c2c0c00516000024103880d03000d50225404e0303180c1130040d5500b0391849000807030440c102c0c0d00100141900b600076640318240c01c031030b001014003400c00c100381c0500000740043d1041e1f00b0b43c008140810400c0d0b0107101124800340c10031040d40740c0000c000d441948141c40103030040c441c0e59161070700c035010341c4242015540010055442d5460b0b640800110b05d802410980c0d260104102d2030103041030034800d5403120070180303a4403042c0c54a103040241044254104c80f65040c10b5030783c207840b51000002c02d50708000003000c00150341040316102062442c01150040244060009100441041c5031440314500246020903102c1c0b46403140181003d1240da42808009a8080682c104005005021441c2c0c007034601000001d1400c5841018400200c0502c038803803d40e009000c0c1445482e40c0f500a4103c030420301001803203075200510b115201005a848043c01c195800300307464111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 785928866 1250 785927616 785927633
    0x913050309130f3b070915090e06010f09140403050f070b0406091101140a050d0e1020070206180a050d05010e060f36030a020708010b0604080316 64
    0x10300c1220142040341e0030090310b6002c182000c8542048903110760a0b0013401e80c0721002070501c901c1c1e1165014050a900e001c4100020b40000f036120141d29400700b1011801810038440c0c1500d90016100030600c0d94074001c2d2440402946800c40d60905041c61400840240807056950300b151b4103141007642e8115100240000717010b6407000030248069942400b06000c0b4079000b400c0344074021041220020a0743c4019036460700c1c0c24260103204c00e0144003110340a4001c1d0003409103500140e40200e064001d00303054a0601c1404100003000316581c02a00021881c206000001c9100b00c03420540390110503000103a45006e0030300d080110b007002620362165900c0e012041001401c0280c00c0e64460352540c5807640c082d00ca650f00c001c005102e032400086102c14510010783c001d6140381c4241400300d00906103080c11a1140d400d40620413250340c1d0580207444100001c1807021031950280a48a080118441c01d486000c440a0700c00c0d00184002e00c1006070200031201103900c60201d40201d41c4452038907060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 785930116 1250 785928866 785928881
    0x3121b210204170c030124090b0a050d06020c070905011409040822030317040209010b0903010b060a0f1b120513050a0b070209130b07030c020c040603060b091305030913 74
    0x214030b0b60304483d42022000004083c1200b1004400900000810340c4a072485071008078000d5686604940e0208a08200b80c6d020488030340c000b80c00e40d00030030b880b800400c841500114003114100d0340011119000c440520005020f003448a8040c0700a5242c018158100c0c030720800110310810701ea0380400c0c10044a503003103481c0c2614031030070102042048016010b411000e0311003540416400d00c0c20036031104500110a00ca03681c0204402503907420401106e00e00c1e0031031a65079070150740c0c0c0d108506260351200060001140d5079070760b49600103070828004101c41100c40e5550510503111032072400280b050700b0501d00000b12454001c0e00c40401d8008252088496484a5003140400f4004a405006c0e08000c02042d030003a5130003401516000300091200c07004ac00050950495600415041d03032194000c125899040e01c11188a50343c1180000d08943c802e0b07004545290750303000d40100078145618051b61080444960f07041c4600180c1743c0c08d40703c0c4145503042340724000c1190100c00d0480954000030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 785931366 1250 785930116 785930129
    0x111302070b04120909021c0207060f1508010606030b06030601050702013e030c0d11030405120f060c03070512071110050703050a0207020a0b090d0203030703121b210204 74
    0x1600b4070342000c0c10300c03041e6140c0742d03000102c2034500441e02c00c40d68000c176050781d04a0307500394189a02c90226200250080c3d038044501548440c2d80529071280c500030f0104075030326400d184c424a45001c543d107084410b83e900c0b000615080410b00007850b0341e400c056a50003c000c0c2041e40c4d0764242c901c0121038260140500c4d240203078041c02180803000f0b24000ca041000186011034008819880f4070543e00d008002e8210440d90040d21540d5581d0300c40c0001074500b80d8484112070800b03455200040c3c2041c80c0c0e465060300366000c1c6402074082001048000c0d0414038102415166040a1400404a226803c02256041034000202e10b1542c0b10b01e19044030800080706455800310030b0003000c80600001d9450300d0019091001280010446208a903a940d5004012035100b52905104000355000390011a500036000d00c040b40150b101400108545886545c070717040c0000032440d0a01c2140c8040000c903030411402e030b86020446800a0b556031648a032580303030003400d003c00052407010b0300c0ba641000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 785932616 1250 785931366 785931383
    0x9030a030206090d03051501231b0106060c0206030c160f0320060c181203070308010e0f0c0a050d0e030409151a040509090a0b0103081b010911130207 66
    0x5009241d4040755050040b032540d402c1e200c13401e14240c1c00700c1c2507450668010b00c0b256042192100c66601070b180300c0702100080e03102e00f030099548039032548003034200700d00302004401035201d00c2c0b462800a00c074900280010341000062807081d5008101680001000014000d034002002480c4400c440c1d207034007030313694002e04040c4404c4661a008003801204e03030006003031406a011003407104034045001482040398000301c90900c22510100304608105401940d08102c88904e052207184041c8000d0029601907140e200300c5514014481ea6100401812500060080024801c2d1600d901c41129610901882c205031912a84625000103203d41040346801e8400020009509102500801c900410b04200700781e62a58076000c00e61410b80c141d402e00301100c3d081000340081d2030400a4181c00100140c100c80b42c0210984da003600c00802a007080d2006480421443c1d104a00246007151490b1807000a004c1d12100d580c41321980f8000d03450f614800e0034243c030050703101d501a80c1a10311071030b00720100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 785933866 1250 785932616 785932633
    0x204050c041509081c031d070f060302070314090103020d1b09090e070e191103010509061c030f050f07080a030e1506010c060f0f0e010b010216090506060903 69
    0xd1459a119200300780c41c0c2c9000303210305001c2c140200056000c071600c1304050840180740410b05240c1c04145004c481c1850b0b0342e20f12160043c0d0320311700070341c052120200c01440040d041912413071444085522140070036004000510000e0b6001a801c00490549103081e1b869544600060700a4060b086078513810900e001003d10107440a42d0030451441a40c0c0ca49100702a1588070100648032103000b10b44950b841950200149800b0106c8664084110950303649800d850301817000c29603601c6d584441101d81c010005109919145036040d82011040300d031202c0580000f040d0310f51205919001400340314400040080080c000c0d4101c9140311182c0d800c0300d541d035050b0b00e0441d0040d00607544035030001e0300c3c01701000c2c1d2102c000102039000c555000707103019003a51840c004480441000d034085940c0d9464001403003029115014040c01207003100004222029424085070844514401d05c9046601400700c0c0c40d86056000c5400050f5103141c0340c04507103036540d000440c100e80310700341c8866014483c4442 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 785935116 1250 785933866 785933881
    0x60905070c060605012a0218040b060a05092a040b0a080405010614150a03090209131a161103210a0b030a0209011203090302100203041e0e010b0d09020405 68
    0x3a01d448491240d0401c03c1000e40303800c011904110300b6540c0090f920255480812141040c0034050100d51000f40180366403c04028820f4600ba81075600311007054a9a0074400b10b0301d005d44c100780103440151014603c600e09010115070b012129007440981c03c7c04804042e185c0c48107442140c0181c5100302d900c0da0303110b9036110000d20219044030b00340c440c2d51034a200441c1c1d4800f00c080790250a44014000200040d90306481e034070030345c480403694041c50360390740d540801621344030402480790910000c141c1b058441411b01400d60000030065150755040c500420405094100301e0040001d0305162080b00b0b0443d100d20940f03184a8040c10401c00014600c2c0c41011114507540c41d80725440740c7c4024081c07100005c0600d0340d241c2100c8402940007940e0030050200c00c8045070201003e138000d00d02042c00035503e4001c509000050211200140c00000e024041001c51441144281c000040f000324498980307a80150354130418001c0c2103054800181141c1022002c3e08015181c1e50020000c000f83e007400c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 785936366 1250 785935116 785935127
    0x5061303050c040c1e0210060306020a020d0e060a030b03120d0b031b06070b062101020c1b03070e0c0d0609050a0609020306090a050c040f0b0c250b0d06090507 70
    0x4000c0380c1d01d00c41d54101c40d59070306203401610b2036200d0640310b0261168100c8401d0603003501600b407001c00c40c422640c1e1100d4024640c0a04801103005480050b0b890745002c60003400c1510b0920040300340004854601c03003a440d008116071510849107400101004420700190809090038005c84220300081a642d5918270350758080d00380f441044080750b542c82d04803100c0082c0b80323945d10102c540c0300c2c10900c54a00403c40240c07403664001c0b0001c05100d51080900c02d03940c0c0c66150f0b00d6030b200150794041003200d51503e08200b9520055a501550005407101100181d600ca015004541c02d0103540c801090880c1040015960309072504c820a214030b585070b490200050501300c62a10070a4100000007803100c03610b20032640204400390901a0543d1254200c40180c1030150076001c0c019401c000c00112001110720110241840d40d5481c0d603142d100c45c0c4003e180840e010000300c071703003800300c0000c8650211100000e011034200015090b1204c40400c1010001c011580c40320151900700300805c1052035200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 785937616 1250 785936366 785936369
    0x1008151225060c08040e15030d120b0609090a0905010b03030d051005040c1b05030409090c140307061b060204120803040c0e070f05070f12050d050112111009050613 72
    0x60344850555a80c8642c1140d070202000400340800c64100414400b100c454a01d190340186001e411604088003800071900c0c1c100d0302c0805034009006000344203081c4005008400e408402180c8072424040b0750000100d880d48040c000d180d07500c0d90343d9202d80400c203083d0011720003400003e056a07152440c000d210009000100caa125100c04440400319140c07405118001d20280181d94242205c00404c007100b20020ba1800309840300d100c18131001940503500e007d007020141c407404000380014070300800d4010001145000c0c41c82600800c20500807668000e01d103020041109034400524441c5003011030080c86103400004103034030352901d10300901031048000c500661240141200300c03031307480118011071041641c01070005000c0180220800340b044e0003030034140d4011945010401e460f9034650005201c00d11480300411800304403030402aa549c8112401407c071100c4030302e0368009664030030040100c94841780b88101111170709524200d00c100c44140140c2000303400c40d41c2d21112078000900d0703c0c80a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 785938866 1250 785937616 785937673
    0xc06091507051615050a080723090405090f0a1b090501171c090513020c030408071e0510030e0f07082508071205280303050610081512 59
    0x40c12000113000d0750b40c9820340c1c00204203503622030030400c00e094101c411550140081c420041416216103001c401102d1400f4072070041d06400d9a910100400d11050341d40050034185c680e0080c00d4503200c04080482c0d00c9020a40c04001400c05003075594910080303100a400ca1080203107400e0000c640da03210800b80040451060046514a0700c840110320100070381c2461842c00286039410420050405c07003201c81c85580540e001500305018070444a1941d001903210020562002001300600c402030038001d100e80241c4040b0000181c2083c0114040d026143ea4000416940c0d4a014807566000d0103030345221440d0303100741c641444d42c5043c40303961000202413054400a9a1000c0c0482c2c4400307407034800888109201500740c4030b141c44107180e0319180c40d1405903128024080f55024044184154141c985098901035100c0411414001c00303c400007822507005c1c0704920f05066800da0400f400650001c80004010100540140070824440d41101c60715054419034031000d0f09407140c3c65003c1c186045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 785940116 1250 785938866 785938903
    0x101b120206061305100b0a03020c0a060b120a0302030405090c0d0504050109020f0d02010806090c1213030f110616182303121c110a0201020d0516020c0609150705 71
    0xc04030043c82142d00c142c40314401e1802c2c0442c208260b1071000e000d01002e80c1c141c1401410805440d68140c00e181c00488112007003551181e038001141340c0550a00c1c032402a02004041c41a041d40c0e02079561711031030062a00c80e8a03080700042814019904607504420717040000e102604242c0380c194003074090507404a1080040c24085a0320b41805103200c000d064059542284d2521034409118202d0300c054002c8880c0d005c100410844c402d80410268000d04a00882e502c4080050400400d08081c051040c0704029084003040d4619000140d003d80200c20025880011711205400762a209086210700e1120450044005814103107903510342d41c107218901250b0200b80c13802c002c05072603410315401c6003040002070011205410120703505401060520b000042d644010022440c8940c20403144440140c3d00015691504506400307205d0f0031843d62055203da4003a2024082d4884600910407400b9410126901e0030302c2c1d44141862a60310740709020565a882503040058950a0382c001040505c2c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 785941366 1250 785940116 785940139
    0x30203090f0d0207030b040204090b0f011509051f09080d1d03010c0203041205030c1506040b040b01050405060a05121f060504050a0b03040302010f0e010b03010e03040302101b12020606 81
    0x10000b080c0b0b101c4892160f805071480c80c1c10355031103080c0100301400683e000795880454034002070208804500480007000c11303220a600d0b01c4560721084440610200802104103000c21154940760303a00021119401c12000c081841098116a41c0284e50300061261242d00000c05805070010156120441d405143c400404660300c21b050030f85000c40c04800041e0f2040101700041501c0201210300d070f51141091300c2c5080d09040c0e68918242c0704603c909040102e0405100c0301345040e10074400f030aa030070b40701444211021000604140542d00c030703640c040c40000030702c0c038203480c450310850700c01d80c0700c00800076128203000009070600144107000d0800703a01c0d10600850b0310380c06082990111000240308c8804141844807252081d04041c208900350b640b02c075038007540d502c043c0c0500c040307001d07000d0000540300010310101402c1d0707004403111031920381040205101603200d074203405c0f60440c1e00f0b003440108020b0b034543c1500000500c44000d0000b16400750442ca240e07a0100360715014001c01c48146c0fa400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 785942616 1250 785941366 785941393
    0x909012d0807090506010528030515011d0d02121606080907050f1507060515040212060603070c02220c0801060c03080402010203130e0a0c03091e02030c1003020309 72
    0x40c04640140900c03035000c00c90401500d50240c014980c0204181742040c141302c00b05020341e000701d00c602c40648407039444040c80c55410394180b0515038070907000e8103000c107104a07040020704215034030141388201421026981c1c0641d00c64000030501030f42e000e030414080400c8034a50030744444410800c011a40404200010b88501c140040c0d8000d00d40714001e010300301c0c5030601f040341480707000601980020410401d0480e0203901c0300540690341c003d00011405107098130114078020b400f103403418403952052240041c9000711500741540200309846981e81e81c3c0368064140c410702400b800c02175003da24881d041000c101b01105d140303107403001c418050010041d50b00c4242c4900d00c00f402401c000600426400010a200310413103038100e40180140d9203801948992480d4400b0746421480940c15258240104010148141e41c800c100914040240304070540e1580c65064204d012183d040204041c0001991b40c2402440c041c000000c1c035624101c0420000a8069001120506d500f03005510b07600210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 785943866 1250 785942616 785942699
    0x80903060708090d0c0609140c12030a09090513050316120311161b1502150f19020f0d0c0206070c0506190f020f04031506230402090901 60
    0x103031044502500390498031404c11a004003485070141c5150352140041004076140c070700c00d06200448080688a14001407040c0180901d000c2a0400d070380e48104064a407003984152440180d07061940d010416440b000240300924607030303072405007241c00009107a45c4101d5511089800c0d05114004007d4064007180040c2d0486500740c5114075520000c001141403120502c01030b0100d60300c50820380e00d005214000b50307034400c001034018030843c11000701c1c400741850f01000000e006045440c14030509252034210a600e0700070251078400c8040b1243c002100c14009078064540c200744105045488801c44a410405003407849071440c0036006a40c086401c2910449009658a401070000c11040e107a4001440d4a5140c1c524503550032540d4144240000025000401440b0208402d20b9150760440c200290300121894030181524030f001c42c20011501a00c0c0101c41140150003140380110700440800d0203403040f0000680e000b200130340003290203924003001c503004907035205001002e8400071030108031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 785945116 1250 785943866 785943871
    0xb0304080d09030c0501110a021e0d0f050d150e010e0f0403180e0a020c010507360e0f010e01080f0c0913020901030605071416030c020f0607080903060708 68
    0xc031600030440c20007401459000898620f11a180010070401309840d41400c40300300d02c1c4031540d401c4000a01f90511907041106c40200401080000d004480e5101d215540f004000e8110b410300011b44241c030f030034a000e107080e1010070400703010900c5014503031400030b42076040038091601824200b000100305494000d200d144100f002a1a41c41aa1500e48090740d4402400c03035001d2400700c04150100704401c403400b9850244800b900007603103840c0015461b90a442005081008212845d00541050f03081d6100c800300201e44170320b2602200c00c1c0c211410515004940101322032400c40410301c48403054400c030003070407640c0701e4122007841c1e40c0b80d21506031036009800d0507100e01da104804607030b101c2c42c110352859000382983c0f0100b0a02099540031800b0250243c0c802e44400c0d555804101501790040018080503002c0101d42d0b142058110400c294124180005002c0100701c0300c80408540b02c910f01c150310281c00a01c40ca440f480c0502c0c058000758000b4004d40d01074080d1001044005d80a08801070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 785946366 1250 785945116 785945123
    0x1b010c0221180a050604080a05010605091b2203050c040609060f0e15030f0d02120f03010b130819030306050d0c0b0d182306011a0d150b0403020a0b0304 67
    0x14644030b84140402000c0071034045082d84840c43c5500026196118001080200301c444050003200529050140c211081540a02d010b0b244201c20860209194812440b98200c1a45039545a98624010304143c0198842080000507000000b106101001070320a001340b40c00c4505000640c1c990b621441a0750b158170403a01c0d4800c0700d180070311400b02da850a1641c000301520032400b50b0040c0100291801d0b881ca0740807031654124a4041a0860f4140b0101c45800074a8040518102d505060350f00c540c401442000d002c0d500c08a085034a040a00b5071a000074181d1500f00e444c1c8801241041110601c104e2045002c2490303c02d00040a00b0003055000e00e45802207204812585085131000040c0d000303000f400030b05aa2034040c082c03407460070324600b443c05010320710030300307000301c554607044140712118201000d00d602c07280041020841505c034024064a00386482074403031090314001c4001d448046026421601e00000c04104e80900d43e02a0040304d008581d0150031a98800707020400b4031040c1d0380134 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 785947616 1250 785946366 785946433
    0x26060702030406200712061b0527040c17100e040305030411030d0504090e06040c05010503090307140a0c0608240a1d0703050c0c0307020607150203070c1101052b021b010c02 76
    0x1006c0d125000015901c0100c2e1202b000d110b5402501d00180803074640106001c041100c01c4200741c403000c00d1000c05a80820000744007880d00d410151000e00e9024024401020007000100003410440901ea845040c803d01504a0300f420b000600701a002d60028050301060510340924801003030309c0094400e000395005070a0381120380c1000d00440c0c0b10381c401040c640043c0b104100041c0000e86d400c0c078002c00f0311514030140c2101c007a40d1078a070b0b50b41d4405503c0700e801c03c605401400403c0001c021a40e401c1008030844800150f00c00f00441d404800783d622010524400b554100c00c5010010107071803080455503001c0095507035660141003540200070381c0b00c03513661080c0700010060400f10020b03e2080d0184a464180c55042d03044003040e40e00c00c94000300000c0020b900201040b586120b0001802d20074203156040c1003580c02d92020307103080b0080c2500400312007590910035805a604450000c4646c40c550200d407552444018081c0403800e558030010f20504603242260b058180881c007015030f4000c0c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 785948866 1250 785947616 785947627
    0x905060c060c160b160e0a03210315080d030c050a05030a0f0b0418060e0708030a1d12010905070504060518060415031a06010305010605031f0b030126060702030406200712061b05 78
    0x19640c00302200007109c0103055640802c070001111606100008003c008000c1290b6608503400a00ba01c444060070300074807a0a0010303800301a00441a607521095140c40040d03504200c3d03030300074027510001161541140c03030f100d13007542c42240c095510f0148902481d008d114080c1040b204503a40c030000e2143e15a50b400a01640320380c00e1280e0070030401203d17500c0c0302480c841c41c48400200d01d0b046040208185a649461f01010442c1c2801400c0061000300c074208103003841c02e000b00b0112070710404c01802c0380b14420b0004031656944c3e4490200d4100b20002914156100e1405088500c0174091511400d400381c1e00140340366209000390381c16034005503101c60450301c580c8031805062a040654010014a100300425102d2210001d98001c003442c180a01c40b103400350300300032030004135aa0140c00a0704400c0400c002c0c15000812242102e516107041e4440c038168900070203081003040c1401d4070600620400080d02c00c07041d807516801501440080080c007070034500941001004162440119405010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 785950116 1250 785948866 785948903
    0x5041a090f010f02070b030f01080f06061e0301091a1905060a0504180b0c0301052416031e020102030a0f05060f060d1401150905060c060c160b160e0a03 67
    0x441c00f4254054011500c070b00b500c0e00210301c0b564000321407041140703000c00010003134454100070320201c0d00d01040240295041090204000003601c40350400014600303800b802441d00c00b5444442c00741d4011000c401082e0171261f01c20b4000c0e6041d11034407030076a116000c140802015200b094043d00000300a055a507180c10180310190050034144c0b04520a18000e030804a04400d868500c51158010240d41d258100000c00094415208400390380041d03041c901410203a40e0000c588642ea801001000b2000462400300e5070141c120300d031583c0ca5203809081030601c070340540255002c0e8902020901070001d182c40010100e8404a1340198803c0e100b15070386d02d1a007800001017419000101021403c0d000113034280100140030791104c90440450090240d0150307000f035610010b4542180c88500d0564201040750799040c0141103410b03800e800041c5e08591506c400440350101d07602011100c0203181c004003a40388080d089074460003140c80070b0800c00152400743c034271074181d84d80400a496114903201 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 785951366 1250 785950116 785950127
    0x19050109020922060c03110723030903032a0d18060e0f040908090d1109010b07030f05090616060527030d0e030c0f060405010c180915030b0705041a090f01 68
    0x200c0c0c25003810340e40c11f40000c45228890043c86524082c2d2001020a442d01c0d00000b0809441424540c0507081440031030b0265401204841d107110341d02100156502c0d0119101d003500280901800c840e1188210700b8181c03a8001d00071591084489002e14a4540c3c0d4490603200c20101d845526407100c00da14120700e1600d81a40419038182c000d204030740c1080c1131070010032143c04446106451021440d6419005485c02d01c03001405020003c04580c05d140d0640d80103000f81c08101c1304002445004501c2c626135480d060b041e55007034100a010300c62102114203100c001170009992040e021815000c070101c41e215203a00341030784595041d008600c6c0c42050f5a0080043c062001da283c094003042140052a900801103500560200c1018202905061400c0d0782101c5018a51805220f4001c20100d1802560140c0394200d40320040c01080f41070302c2c0001818230b50075542000b0240320340f030420b1010103588400540140c030110100307800380940e802d0040480380628021540d200b40c1042c003c01003940700380b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 785952616 1250 785951366 785951381
    0x12030e0d0303060f080f071202010804170c0303010308090f040c0206070e0409060e0d170103200402071205090f010507050316021f17180a03111905010902092206 71
    0x2440c0000f9400d80b0f0780340100c0611382540c170000b160742c071028050082c03050500c82440200200986034546000035800a42695001003000e000307440802c80c4010b180079160100c81621a401090304c2e0369684901d070002e1280c1080c00e809014031b80d401141e07416814a80b091411940098008112a42d1494401c131042240d01e01c5031904692604100300008410b801400c00c40c031081c1c0c000d8031009446400c003c04054410300d00a074004082001000030900038a4188a8502c4c202001820000c4100105d00648200c4500a204504e20b10418070810f6004010b02a0030404550b1040d8605400004684900403481c02500c02c1c0c1040001000400404c1f18103000144040c0c03642d03010004c004140004981d00c1c03941c80c8086400441e100e50003180001c05164044800c00250540e1568180740740c0d556000040300a00f441425242c42922a000700103500204941006552804c1410314002c1c0c040d2846d41000c0303000d10070007c0492400d034504041e400e4014041000b42d0003602d0252118006004503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 785953866 1250 785952616 785952623
    0x63002130b070503040503010510030b041104021908060910030515060301090c030b061504080a02010c03020f0d050405090c25020f1e09060a080a06200703020d0912030e0d 75
    0xc2000014032542050007910300e0354003a0001d5078840340f910042c10b00f556001000401c8002c4440308c140b0008060703000e02e42d007180d00200603182c03440c0c146011400034030800c000c03118407002184540100d20b034060b003481d2044c0001d80d0410752680390a2801c03404030b00c0c20b01005050f9081064200d0803054001070007540640c00034008a0031101c540c40d014818841e5800584034010204100041403c100e00300c2000050306244144c50030745014503160b00c44501d030b24002c0c10800410002c805140c82004030b400c0045600098a4008036074a0b0081c1280e4824404c480c0650807200024207010094002d55030386010304038a10076008100c0c60680882e400a404c200e900c4102561480c2c6c03141c9400f4413926219903442d903184e940c01d5103042000500304c0c00811003031280d141540c00340044d60001c14060302099211070b0109001c890b042e80040d151703d9509014042e40ca0100ea0002455800226641e040459072901000316840d000d424200310401c660103408100704524490060816240c080a000d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 785955116 1250 785953866 785953897
    0x403350705070e39280f0e09040c050604170c04020c071e0f090e1c120e2803080901060b040608220c0f050a1a0307020a1506063002 58
    0x3c07050340201c140e800000ea503485d8600c010340c10f604036803180c05041a00407031a080c0044681e006803002000c01418240c0e080c01200d044010900308183c01141101501004107142d031600d4541062100717100e0044c014984511400c1103002e03d500703051089555803c4100040e0521900707112100841280003080d4607843c00308403400080305501d0b05840e8001d045009004107034881080002817a21a4144c50700c0c1e0954808a40c0b00c0e161900003140200c031f07141040700441d0030001c860700350342412050f50a1801c7c01324414842c013682c80361a2161208607100b42c4920b4500d1300c955843e5822901c03e4043c902030f94200304011f2040900607110b26900040d001c1d88250743c8030b964083c5008014440000f2518402e5840d41840f01001c8540100080c041c2a18401c852603e001140380807258046d80d55124400000702081e0302e1072007441000f280c5a0840c40101d14500150f50b80c00081405118690002d034092100c1a1000f80c0400004614420055850308507a42140d640009600865500e030303e004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 785956366 1250 785955116 785955211
    0x20f0c0601032102030a0e09150a0803090a3f050a0516090212010b090d050619051513052820070203030403350705070e 53
    0x300800c07406148030307014102494000008a5245103264180c44040d500107108001101d6481000b800d1110411259000b660700d0f01c2e0310007820f4505807401290040410000800d49080020060503200415159280e50300e41e160701042c0c0000c044001640350b20681ca440740c00851815500030b82000740380104c100f10082075590307140b9107400020300301d542d508881d05180c102c100300701e00d0500608403a1700641c50515800c5850715010340c14081d030443c1440c04540c620140c0c5a120355070b440e4613400812110745041160701c1e003545a401007001141903040000140920192800205c40144c0c00340291103058554507011016100c0146038214000fa11403050040103440d1580d04d068521b282c0c400208080e4840c0d80c0c10000c4102e864128241104000610040c0c4001049400322a00060410440e05015945510794042c8400c0f0520a40d404101207a45081030001403202610840071102903560b2050032101c0d4100407a00344001d000c50360361500021403420302d0000340030b010f80c03400038014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 785957616 1250 785956366 785956387
    0xf1a042706060c05120921100c0216120309030b1803032e03020a03080315040f061d04150e0c0301020f040501080912032e092c0a06020f 60
    0x951a99100b140020b090391103510501c1018009641044030742c2d80024070b40082c40022650b07041c1038240481195001008000131010140402d84011007503810501c484003000c00c000f951860351001040c01109845030000701c21405800200440d60b164403202900d61542e1035041300200000d050b0310600c100b00100c840c8203174080c0000d5224203030024000054014400c3d580d0140c465400b4140d8800d1b44d0503100f400980d652000f98401c880e07000b030403941d40f50703519019003009604482c50300c0d4001b8100b1180000e08000c0b03030003013400c1da003214400300c81b42c1800591440d80003a0603103015120845000c12210391000c1504040d416401000444d40c502d0a06404642203a1206c0300080d03880c03002040a001ea903a00006850700028000001e0a20f50f524220b00021480098050304101140e2040001d0340014844142404225036000000b52551180c1403000303020b011104919950f5400000014151001c42c000114080c140007856110401e0b51020002d600450341d4000d600c00601440340d60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 785958866 1250 785957616 785957621
    0x15040b0118091508010212040b04030903052d0d0c150e070e010311030a1a070905190801060b16020909190602130905070e1e0301090b010f1a0427 64
    0x201602c0310006880600d00b88051185078480d04511031590040142e40c401e0b0100d25415900f103070300485200c05540f1079203003d444e0720b407840e030000340f082c0200380802803080255802c2c00d03100c1c0c00d440c20745081c201c10404815103031103000d5810710104414604040c040381494441c1c10340e1480501001a403c2d03102407185103864025401034502e80d0b00e0708010720800960b0460010641001c1c2e00421070038005540701600f50010b00300e00100c081007900000e840c80d00c02c02d865030060402038880c4141040c40c040b46d0a5070300c42c90088031515800c2c1803000a035160b1900c200e80020402254042c0f0f007460303035800c2190303010026150480d648a0100f140a60502109000341514402c020040c2d50702e1801244224401103a072091000500e800200000c2a820074080c0050400c112184c1141d04044103e40c8190450b42c41410740543c0f906e0300304000c103e90701c0350040c1070b500e03401444070100c0c0e41e5a0001c000646042c18480311154203100401401c541a020301100100c06180d001c100413030220083d08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 785960116 1250 785958866 785958869
    0x61d1810170109141203010b0315060403110a051002071205030904110a0207060c02010c060e1e011a0603090d14090616110d120c050a0615080f0615040b0118 69
    0x2482c1c1d5442c0c1c800410800981082030140700048060800465104040c0300140414410700b240100e0001c0001e440100800c1480e0050380024041522280c407801c00c903140d501c0d2105114002e0b00f1605000c2014940a4040804c8070703e194002c080301802c0176404900c5c0382402404a0700340c4010300060903507941c1c2e8003e0300c0040210354112911a11002d174024030f40012070f8451824011400c60700c4000d40d03070010481c285190081008038100302100c000c94500454143c030070100460350707080c20082c0ca40640161040c0995010101340b1401d058082054612040c0c0b08a0100d901403080586203c1c000c00d40000f03805c1c0300400c06402e081c030480c00b16070642e00c180c8801002229924204081083d41e4016000000068a41180803081c0d0345c4d6540204000000000a01407040c40c0e9400304601088080d400f158004014010206610018031107020039008410f01c0707000751403c0000c80c0c0c80000758640306040c08002c40c25812103420a000c02040310050090400144c40c104050541e1030400010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 785961366 1250 785960116 785960159
    0x1b08030619170d02070e16030e0f0d0503091203130f0c170d08090a0309030206130b040b0406020d08040803040204090f050105040c15050c030304110103020909040507061d1810 77
    0x19620410f2200900305201070304210902401c8805100da0b202e100fa102951014450500045503948544030600d004840c002092440c0300780e209070514240d100c8080e5001b240340c201150f09604403032403140d4880c0011030f4041044074541c1803500108411043d5049080d00400c2000c5005484165a580225405440607101d610511003222020780c44110b6541c0001e411020b86242e01b40c40d40c00a0030020144406849110013050780303000810380c02182801044070b95860303580c0b265103003000c2c00c49270498491903001d030081d4148450050f01850415114039406101e041ca9582c495003000002d00c41502c00b44c402449910803400018400d00c44d4030300880c01001100440391400b540c0546c00654100d40104000060080a84e1244c0000589801c00c1d0700c01078100424000c1c0004800a014a2861581c880180d00c24030007840404140201a504281c1e15a80b90a2000060070300b1118280c00c4a5005074800e0328051048901c00c81d03142d0440e0440c04448225960317620700c80d8118500201c10b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 785962616 1250 785961366 785961373
    0x109052d0607030b210309090a0e010f0f05090105071e03060b0a03142d0a09080a09030c050a050604030f02040f0507020d170f0c0703021513031b0803061917 69
    0x8400034174084c1469001e1503411017160720100d07105840b203500c9000d003941f04c5010f101031001040050700140c2080fa0b4400650000f0058075104210400240240102d0700c070b0414a07080120707411401c1030280714070030b121980350500c0d400c21010304904140014440041091394400c00402c1c00c81d0720743d0050441211031354000c65101202107900c2d4500d9400f030130b200e1030701d840d890000c0c074082940085881440030b904607480603903850ba0744110241100c160014050003000404c00b584903000f81d90507044d68040c10000f00625190000c1c020284424042c00e54850000d01042001400703070b80d0500204d510152001c110b82c40a000c4030401d1b1481503c683c005030b002105200c4031694803059900743d00012000841c00c0e420542c050400541010748501e013030360301c00202102818001c03c00420074515640e680906480c0c40d091020a4440c443c000f2800a14444c0c083e010344040407038000f0b42d968000c13003003a1561322180c0812084c09003c84e10071044c4216007078005107003100d180c40709108802c103901a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 785963866 1250 785962616 785962631
    0x20c06042a030b060d020a1203180603180209040f06090507051e0a090e070807060f080603030c0d050a0905040f060302120f06040f0206040321020c01020109052d060703 74
    0x91403401c0c00400c101180a5010380040012a801c41d90741c1d03400c0a02511140345040060000c600480001c0e0008901d00200d041005c04242e400690f403801e2000c49002000c0e29603c948086007915040341c070031107500b00c00c3d030f040d0000b518180c2c40c0b07140c100d0f204480d83c0a0403519940c8003010341d00510f230b041d038181d00710030401c00180c1820250f0500740c00810a040600f80080c00006000705000d009111101c1e50f11026689195030402c1000c0c090045001111544c1d642c8160050101040c1d07814400020b4a99000c1411800c0020517622070003482c00140101d108042c20443d00358200c040c101d010045401c03000113164840b407240f92220203042001192803411070041c04060052a18500220f6003e0004105a450089601c0b600158041106000f075061030000402c240126000907148100000360400848451841030003110026000e40340b541e0442c0c401a801c07101d8180303001e082e070703001120020072280b001200302d201e054036008182504c200b85503a0760703e843c2c1d040312603402007a91181c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 785965116 1250 785963866 785963903
    0x9090a140619030b0402061b03040503010605090c0a2708060603010b0105070213090602090a0e090f010c09140409050f0d0813080a050c0109050f030d0f0606050301030213020c0604 79
    0x25598445401c1d01c0461030b071062854101c0c81a9101d10000e07018102a4010500310355542d0101c0e81b224500b03482004003085452a050340326480703485407034402e40c030f460400070756800c1c42d05040b4810400c08040e1814600c40c030b641600c107030b910b220200c0034600d04504000da411051010305009040804020655850040c042c14211141c8010250600c441070210400580d00c1d012008103140704901d0100b0340000074a4060040d0045c01c141a6110300081c4011440441c40a030341445002044100c50309030f28010326a60803181585074800004140300b0041c0518078071103031301d2036400502a10018080f0b48036120345003020030b0000300d00c0c1c107600864403a100c43e039403003100c003500070440c1c09100703800410954a8081a01c54601c1607000d20401190b180705916081d031100b180290400305944541c6120152240c40780c2c00081d1b8000400c1c900014004c8160843c400d0074140c9a076616194a10303401c40d000c100c5072404651400028030707002c000e281c101385014071040740140d100302004040e0318003000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 785966366 1250 785965116 785965151
    0x303030a14060f2101020d0f02071208061c0302030f040305030a0f110a0627050609011802090c07050f07060801140108040302100203090309060408030903010c0206070804080f09090a 80
    0x801151044203403600c0d40c007043d550800c44e1010300d415400001d01010074035510764060300461001611143c50841941b001500a40040c00401d20900500b0070103901e10300c094460002c107550f410742021001d440d070500050b040400c000918080e004680c205001403540311070300c0e401500b040341e0355000840c0740e0a0751608130800da84200c0280c01c105a1000341c11619603a9008005000340500b43c85c1c0ca210407008281b05603030518503170103540a480d9200142001580d03607005541640131907180000103000b1030352010101080950082156403240c0b10082074030000e41060308140d800d4000d4003070a10494601308400d90040a09032181102c640c90031106a03110401e00c00c3c41d40c140005072003000000f070340c0030a049107255401d4a0041e03c81e201d0400b0107185000380800b25421a000042c04502d2840000141020010403002400004100041240c481009072103003008500040d010400181120010b00400e03605000042d080020301030010f02c4a4400340ea2410600340e1b00c807080400c3e9143c03030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 785967616 1250 785966366 785966371
    0x1804060f11070b04170f0a02010516091409070e090106081603020403050c040c0e03030a020307150605150309010b0405011401020105090319050702132306010e010509040e010b0303030a14 82
    0x9070340316081c100b0702d48504220080041000380407405d110014580e1120150a07294108000c16200e40c6400b4118400307070080c201a908086104190001d21400a200341c0b401030a507000215040c002808800500007450f5000d0080303c2440540080c0501d5134a840c0c0185008010a55134518903041c501c4013115042042500c440030140100001e01c04242e00141e5400c416000340d8002803000c1e10920708640462038034240ca075160200180e85054540c2c000090100c141c014000120b1040042e046801160041d11405030024001003003180d1100130400596484541e41c0000f262400e5540002003c49000342c110300702d2181c01c1d403550246542e0901c1159840189a0000c0d45000d00000e0004a07035400c4441120030031400059036011034440301086081d03188100018440012111b4070301c400c01e03214060294400d610240000c2c160761007180b04410340241a100c8920f480c3c403500a0101034145521031040c2592146120812618100000d61027019001c10004405458480b00f0303100303074000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 785968866 1250 785967616 785967641
    0x1c050408041d271606050a12021303080d0905030d020d0c020f1e07080610030510060b09011d0a0905070908011a01111005090a030e030d09141804060f 66
    0x1030041000100a07910120000003180701520003200560f8052031802c444a04680510581c04c074000030901d4101003e08889816602e40a001610500c2c00000300d02544081c1c04200c0818601000410b659400a1180049041c004140c0d4039094454924680c804d0b4040300460358005545910001c0907c2001560780031440500500a4284041c694564180e07076880e0104018441a040b81401000190010940340e819101e1524101c010120482000c2c40240c07800d0041d513407440c100003200d01c40c010584000815060502e0a100011140c0e9100d03824441c01e005203403a203221050b42c83c211118020008681d01244602d08004020034004443e840305802d07030305020650740f400c001c03000040c42c0c1c41c41c00e01c0c00c0c40d00b02c0f543c011a103282c0440610034411162070700c014461036131804102e081601d4042e49500c01550140c10a1540e61b00040722100300042502c44c5c01e204000c100c4410740c1d84000c00030b00c10380d020104400c184011110a89003100c002d660340001600a81c618051500d10544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 785970116 1250 785968866 785968919
    0x5060a06060c0b010b0f070501060e16020f1b0a0b03040507061404030506040b09150408090a0605030919020a320d05062a0d24080a081c05040804 64
    0x1e85a84207000c0240600440700d003800c0101d01a181200c01b40142e5041641205c02440701c5691049a1002e2038070a0f50504403c0c0c0c44559030b20b404600006008000b0040440280700c0b6a004084452000107050b40c050762240c410b48000400b048600007550185024030f0140601e00c0c50701c0405080560464601c0c50104002e00c402c01c04038201254095010380c04c1410358109540e0000b01034203010071003a009141d5050300c424003062021510160180c40c4e07007500c052002c335495000944980c0411a00d003035007540042100c0c0d594540c0d0006e160740c56031000d010070002545801d40c1d10200cc84c000c0d0b1500800c0d1084503092450780038030209400d60b501c29070310001c4028442d02c5643c0c480f00c00074546000000e41c0c3c0300175403274121381424611080400b1140103440b03514a51a20001e021480b00e040c52000d000901540c501110740d44100485800358020311182d115507682da00c040e00b080340102c01044001c20003140c2800c1c1c0e4020b6a01c594802d035038440c1c0c4c0d02d00300704070f031030546c3c0003196800e14011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 785971223 1107 785970116 785970137
    0xf0609080d03090b0103030e031e0309011805010516150603060203041209061e0302120103030e1f091a0903010e070512190602030603120705060a0606 66
    0x88081041da4100014010704905841ca4200054001400c2c40300410000c2e004a980e40320180300a4181e550120701200d030030b01640710812850895403c005155201982c0c06031036000c1e5292103920001a417800d01000a16078010f00c08900d0400c604180b40302c0510041c40e03c2c44400d1101402c06024481c2c60386070090103500141c0c2e040300c0122040e9000c5d0003c03402030100d0320903100295958001104600810300168030184020828503600700001803035054a107003924080c2d80640c0303d04101c043c1110a004543c0750300100000001500c02d0b600b847c00354007400d1790040311040300c40b2010100c4034400040d55882507080c517907419032a00d05141c07007806c0d000c81d1500c21184100c0b00c128207040c4803100345441d9070150200c0e00c4146081c03519a00083c0890b409540c0050002c0d046400702e24403502a210254001c0f02c06440d6a03110900b0401a01054000c8101030b22003490000c0d403a9 = true := by decide +kernel

theorem cover : BRFrame.Cov 785791366 785971223 := by
  have h0 := BRFrame.cov_init 785791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 785791366 ≤ n) (h2 : n < 785971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
