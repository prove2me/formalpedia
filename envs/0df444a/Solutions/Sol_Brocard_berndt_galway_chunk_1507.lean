-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1507
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:18:37.58399+00:00
-- url     : https://prove2.me/submissions/b3badae1-499e-47b7-983d-5123ab02053f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 270863309 ≤ n < 271043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 270864559 1250 270863309 270863353
    0x310030b070503090f0f120705100608100501080607080f06033d06060504030b04080903031305090a06030b0105151b01020712080603070303080411090a020c013b 71
    0x200000c0000c0200014440108011105407900c0c01c01814403d171071003500da40d101f032081d18035074000c403000c544401000010030288011211940303091040301c1e00c4060155560200041180a0034148000040d00703a5001c12094000c410340d580b4030095946200c540b070440c01003e05120f80521510b01410211050f5024404104503010024921250002e00043c056005811500c44582c5040750400019821004860899a10118108039540c031820280628014802c0403501400001030ba60344600c951229a815910f080311119990323102c8105400450380e0b140030090000c07420200520541c44c0a0701d44507004a0140c6440345041840118940d4480c40d80c420012142c0d000b040100410220000d60320820400e4541800d00340b40220000f6502c0c003c500c406014403110802040c2401804103402101610141c021002c5081c0021610000d50141c0360442195203403030340f0040b42c507006031019400d040c1060030369000103080007541070761440c0c1021150f0040c40b440034141d070a006004051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 270865809 1250 270864559 270864571
    0x904050607020f0f0a12140d05040204051f05060c0a0204060905010303020c0312041514120109110918060613295202030d080f0a020310030b 62
    0x603240c5030921000280c0740040f6051038010030f82003292200540e18002a11000762900305461a840f00325001007642d100c21a0780400d84042d07000101c0d0404041d040e040140550302c02d40e010005a5201c84004036455032505200d08005461781040180385480b4015265044041c0c00755060454240e000070200c032100d60000034000c6c0c44100400034180c050101c00310a01081e000b8100b010b0307184050500302e04c0307180901c1000d6002c0c24000c80d01c0510455682d680d06014447c2a80c0e6001c844140ba400484240700d00c00c000740c01e049682c1c070144420829281c15810141a581c0003043c0c5802e4400814001424150406410302025050840c48200040144400000b20310140000c0c00782c105041801e2034122950707401048041101d00140d441c041c502047c100c1d40c0880200b01442d0700024001c4c50f041190100468803509001c03070740004610641510880403183c48250418041e0354941040310066810140745001549030000341e001154007441c8013200380ca04541766038032180b40c20410380b84 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 270867059 1250 270865809 270865813
    0x309040929060a08030f07031b0b0a0203060306100803040306050a021204081909050108130201031d010b1903080301052b061a040b060409020a03140702030a020709051e15090405 78
    0x188100b60500715680b101826034a130103140381c075151603110055440340400c0103003008005080d1421942c0e8030186041c40d0359018006200505002240340044e400560301640300b801928041340c07100c004891950100c0b20800c0c091400d0502d55200c1000900f4010180110250200003445481e1407845856114a1069084a03142d01c52014403821086202d41d01030b080c40b4014000740030580c1c115010b658807801c455000e40e544000c6100403005840c18903070560515880c0104000010410341082e175918009907508245001245c20b2101211510322018002941c10001440281088600e0000402c0000c0d0800300c07070b103440c8000d035034600107080050b60181d030359030043e034940d5074800004490381608441c00c0c04140c80942c0003504a100d640702e45110940c4c005079024805019404c010b0602d550008451854a01110041d460768844030801c03005010300c801c04510240107111304c86c02071002054030780e014a903000c46051101c0e005032110110302000044000d5507038410010f10711407445400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 270868309 1250 270867059 270867061
    0x70506090d1d0d020105090307060915021204062303010308030f010b070302060105280b031b13030f020a050616060c020102042102010c0b04050105070e010e030309040929 75
    0x15a560800700c90301c5050080000c0e0001c6008040541d114044440758110380c1103000c0d404502c0141e03800d00c1280010b6030140242c802c0060000c4e0040020003c0320341c40700402d6045001954101d07203450b402c00c520661118240828000d4600c14141101031600c4003440720b5100c011021010400e4100f43d004a03800c2c031000003009035004111040c1801400701158407401c0c41d500b41d4000c2d40760f10050240d58011051580841003c6002c1d401000c0318541841c11a4042629a00c3c0c03011154800c403040581e141c02a4074869620184000b262413205800c400d0144560456036512510703001000103036842130703440e9008100e50792070300b006114a9551029903c01c170310707880c0384c1042907031201040c0708107591040c002084400031440303085000e15400d499090313034152284016035a04140d40c50161070030442104200070080154011801190703a9141c3c007003241203110045070505030015055805070000d011000c083d0400360441401148290704c00c201510190034600ca443e040340c000b218201c1d408e00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 270869559 1250 270868309 270868321
    0x110f0306010e060a0515120a020f070c05102c01020a0b16090e01060c0303110403050d0206070215010510030e01060b0c030a08010506130b0c210406020615150a0212070506 75
    0x1001c500400c3d05541c049495411440306d00043e00407681503110b400c42c010001411040740c1c0d411206c44170840c107012034442d10a414004240349490141500030300440300380e40080750144203000b002148059001d60006007840e5083c40a80c005440b09040d44200720301c14000035000c0c90b5180c8108902c50640810310101c00000344015010b5101508025402005100c282c0d440314502154940508020840c00c0110321501c4061040d603001401e58060011804030882c2d000c548070f80101001d90846150845103242c0c0100300d0400e10841c1c1c4e0258050f410050075074081d4010f010502c1900000250796940c50f4120007003944440703541a8a03030400620042540d0b003114540c0d0140c88140c0310725007002102812843c80c03038841e0180c0b40f0342c8000414003038200c500401c078003545107210300e00c0512007030010760b0000034507081401344c1e0002d40101f00c0046c14403041c10701040f82144c070003440130380345505001040c41141e02c00194402180242100311075060741003401004d12070b1288000b0a03640c03030a9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 270870809 1250 270869559 270869569
    0x1d1e0607080d06061e0305010810090c05041109130204061d0402130303050406090f0509010b25080702210c0103021b061f080625031806090308010603021303110f0306010e06 76
    0x141203450113051504c0012710100c0030002e44000c01c02034815001a4105d0702c0d0815a4143d000f070307070140382c1c45410408007103805082140a4001c0600503110a03428060155902c0283c0c00f5031f01845000606c1040d921001e1880c1708000b0240c1c40010304014900414440200d80c003400540043c0c4c00726200043c03c002240d80400400014000500c4146e1010305080008040c5101032240741d0441c680070030f4100d211a0100c880403401100d10300040c1d00d640103807900d2000b0f80c01c0140140d00c00c1c034075401803000c9a901c003200303c16420038000180c0780b1041d04400650081d00f06014415100c103100d816038105100410031180601d0203480c005034980c104a84244104041e6000700700c141e0058800e01100400707407a440b00510910021404440464040480003010b152002c5140d1060702401c0d0000d00809c0c5d40003d4920703000303580d01030707823030fa26200260164800d0221603a2410452041040030401541d40c5010300e14008040300c540440385c02c006460600282c1000c4180b5112905001c5c0502d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 270872059 1250 270870809 270870857
    0x2803050f131404020a020a0f03210606020705040212041b080102070303050a0b042d0b06071a07020c130504050a05060f01080105061f080709080d1d1e0607080d0606 72
    0x1243c040d440c00510020003034680c411010010b01c031840d8800081d0405005400c0700712028161301c0030b52481300380503217414054401c81c4200000340c040c100c00030030141801c0c000c89102c200c8000343c1000548844c0e039941807a031511500719035402403054000c40c0c4c4c114280000d041d421301a40d40400d03d401c00300402021a45074170003552156203001c2c056250000e0412808180010204611017003c40310000c0b41c010b8001c00c0407841d4481b0001aa40303042220340c0480680c0318070342a2584c00241d450174026039403000d0010f030b4194003851820030b06c40100d007a504611341c080d00c00c0c0700baa081d2124030360341e00749000400d96908050195480060060342c5092159641c031040845107042031003806802d80301c0d107070007003c00d5004000c84100010381c40340c0035440280041042d00308941d101c91900400610590402013040742d02c2d4004449030340c2c40c0c82c2a1031303650424100c031000800e005d480003080082075071146500322940c400501001d000e00800d40310300d4005003e151180013039800b503500201e0180b90 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 270873309 1250 270872059 270872099
    0x1020d0f150303020c0603040620030a1b081b070206040e091b0d0b0403020a02151c0b030c0103150906150f03020a0206010504050c041208040501020106082803050f13 73
    0x40044010800f1a9000a04040e030030000d17112983e5070744850806a010303045c40c070403d403520b40c0c81c6130005041c41c4841000313601c180c8002c4410000c6c0300c0d0130b40300c80c90a40c3c290300c031020020780d0100c0442d140200c0f442440142e8918009a40d00e044801c0d03002c220aa00554800c4815105050400081601c2400403400c1203007642200800703500d510b400203424020038038000e4295112000000c013014000c106603010244c009040c2c000b003000e0707a90f03920b0082d0310400c40301d04100000c6000e80d5140b4120b02400c10301920080c0035003004401800114001c0c030744040100c12840d2079420014003071015110340030250201d0368031020807500481019100800c2000c0000805104114040c03017284c1c0880c825054583c1128045019110810584114019078020910000313468420004000e10a8006e00840708203800074030071942e070703144016290300f2560600f032081c0f01c039044e003c0c4544050743c0249910384d01c40e042c224105580300c41558003070b4002041c0b0340e45600e0a03200503c20480300100d0000e070f00c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 270874559 1250 270873309 270873341
    0x3090510020d0c140105090a03032301290c0705090c09061c0e030f03010806010608090a0605061309060911040513030c0212032803090c062001020d0f 66
    0x15645090003550349000b15680d40801c001c002035281000f14109940407001c107070360000e0010b400c104030201c6e19500583c20444c003281c5000300000001c0c02d060080b001c13811006a4000c916881c02d061507102d10703125082c80607d5a046049a890050403102400c51060420000c00c0d0480c100300034040d80c1880033b8054100da42082c480840fa681d0345070704881200303581180614003800e4214540c805001c5072907200c070b103a0001248903e200400c1c0d0003c1d60484201c1c004031006640c1e105c90a84802009407075081e160780000011301d0215010b90402c54100c1c2c4042c03c19019a040d2803903110881d450341200311041034a610420061103601d100342030341001b04072401c000c18104641c01e9109850140b80003410701c14090010000e6503500c038440c80e5403400040642ea45c86a19400c0d11805e908540c2c03011250100149942c1c05151181c81400402a4005640ca6480b4200f44003079400c4501c40b12442c003907c10003801c10103212000c1c009440c4140c14050042084041c11000e4002d0b10140681c10080b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 270875809 1250 270874559 270874579
    0x140a1709060703050904150b09030105060414070c17030a1d0607050a14040504090b010e01080a03091208091509030118020904080f07121d030a0c05060c03130909030905 74
    0x16030350401103403003850f03040c1409a40c600d28400424083d01c001161810303400004000062110f400070010898400c08500030086907a58408100031600d441a0500214010740c0c0040c2c241400b940c03a0b00000c6004107020558142084513141a65004885041c642038072030176541d415034000703035000c02c000c03d50102800765841d0505008009000305501f9004002001c0d80880306e00a0748000c64010300340c00fa00510002401d8105050302d507501f03228010101045800000d12881d0120f03038400480e0b403540e20030303c0c000c3c075150340124440d480d91001d90f1048000c005488071035417001e88400035002c6146515403100144401c06084a440d8003040443c0e0400d134040000594410b80c143d41d200358030880b0961a0341200720703802994043e050b002461681c0240b9074012141e0401c140005030b1108030309041c6001d10706818907848010540008100402c155030602462070b004001d806581403100032641449201e6a0103000303604203a114010f0315a807286508180350303010328180302500094a0340440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 270877059 1250 270875809 270875827
    0xa021308191b080106080a031403010e040f0311150126060f100b0a020309040b0117060409110d1a060919020d09080a03020307030617030406030b060403140a17 70
    0x780c84980c400080074000e40a80d0700c620740b001807036000054100c4000030022203444808096417000c03000402e41c08074500c60030001508c08000d0031203042e42c1c60300e01c503105103460303d070b481c0d64550302c0c50358040b0306000300b00c044ca0703c40c1901001551030343c901c510040f031199450320022045182c0c400c81e0300c2c03950400c40300080c000c0c20000a402c90708603500d201e21500c50307a0b070300c0a007007101c06c620380102040c000c0000390040e040d03a0000140600b076004035002c100200e2550015140104400e440603c043c0341c400024846280660104c41d41c40d02034046000314020010000e0a4680c042d1000c03582101107802c0340c3c1c1d168440001450f4021000c4e9541c03821414a40b03030007007603c4031b0882c048020540004024001041c5c5800115007640e11660054840907003481c060041d4000302c03100d00010380b91810001e02c4001c1c18008420014085000c1c40c5400d007070a00c00c50140c051000780580044007000004001a1120032406040c03030800c002d0b1907000744629200500c01c10414405820340e40502c9a058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 270878309 1250 270877059 270877093
    0x415020405011b0f081c0b03010204150318170403050f01331203030c082518030c0f0806070e030d081f06210203090309010e0a030b0a021308 62
    0x40e0368070074811005032075043c6142403500381114031002881c129000c564038900c0500190598120704030084240101d00c551002c0c54203e000d6480380442008080d034405400c58000d40c40707a0003010844041034884642a200c80225401000c20306904407070000d020001d1180500ca1031f0701d0441c10100034040000c00c91000d201c40c00d4411a040c5511402c54030080401d01002000002031245e00150000c031010790030041d006000410300c01c40425020340001d002202c1e0755604064141104140000b08a2150011500442e40040c00500740b00002030100100d0b107820a814014922555420030240c1040145418204080d2450301840b030b92944245139641c010030b01c5468624180380502d81581e850342141e92000701c1c0005020b84242034040070400301c0e41302080040c06161071694006030043e47c6080f82c220710044500055581003480055210340c441c034010304105500500000800d80c480d01d40b00c0d540c400035200240361550001f51600b1700c0b07004400c00d40c003c103d42400707810900c0310410250 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 270879559 1250 270878309 270878327
    0x102030f070b07200c100c0b070302090607060e100b0105040806010b030403050913050601021207080d0903022a15070305070f02190807030b01080f1b0402090d0605041502040501 78
    0x42c215008140007441e41881140d08401c00554000c040b01842d040360091a02c5000d080401400740c5280c2d00180c0d44d05004082c1c00000551004181e6895038032020114001c2d0040e26555030710610400004d40440d2042c0118050004d100c805000020000030486040720100d54041d41400001d0000b0000d42e0300102c3d056044032000e8880c0c0e9560341c0d4928044480c0e110714206207900c51800ca068610052180c0e100502c5144203030200e0795501c04002c3c1d0003d05001e84d1034000e21003c13003000034040c4901c6940004103954441d0044540d0070580e13a04044a81e907030400c980e030340c81403020088034407858a0103126120011b8502141e1400f414be4600030982c0c82503078005801703006854192030464a4601007208840e00e4207240000c00e0f902c03402159103641c454407082d29002421000820401d00100304841503034114401804007080a280034034042242120721030340b0640c00e101d40c0395035454054001b00300307921600d00003032149001d01c0d01c0d01440500f0f0800040c142c1c81032009000c9640c02003210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 270880809 1250 270879559 270879563
    0x60a14030106030609080909010b09030c0d1712070801060905131a03031305030c1f080c0f041202041404030815030304080703080a1211040314011d030a030b0102030f07 74
    0xa100010a1180460301414050340000d10842c6010841c03020700c680d40380078111440044800c1c600c9641d85100b1110309006041c003047d0300d500070000806582c50518181120b049c880e070034903c2502c600c8010000d103034021440c5c138408891040f04003c20b83e0b42c451021409045141000000c0608040104048040c2020301c0100329580e251812000c08003210031046264005084956540f2100040c0d400a1002e11541d4000d1041da000c8048518080c942c0011201c000c1001010004070b83c5000c0b20240c0c00507141443c61001000210b0910f89400d0050015220380d0b00d40750705461143c410f0000315003c914a50b0384090420b418400062340c003d154036000300041c1c80b4504442d071690000790544c03240e90301c66001c61140703480000810500350060001c000203070b298882c4050180401600b41c2d8002c940703071a41c41c0400c00007800015140c00405603011040c80001802d80160703051803a0000b13030702c0c001003c1c580c00440c4060084c1c0d030600903128080f0302032010307600709000c00341d052030a07010303030180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 270882059 1250 270880809 270880829
    0x21c0f030902130b0a1d07051c02070605010303080601050307140c0f01060f0914090d12061707031709010c061113031b060c0320070519090c0305060a 66
    0x25210845100740c00441d025500180a102c019041082003c0140f681046080c025509603d00140b07001c42850a0b4a40b031100450b01201640c41140840741980072500d69a8400b103c80007200c0d807442c407803000d418201d1040f07a000485504500340074000500045c181ca04005080080040060303008041c00e02003102810791580f60034000c001d403420450f500016500d25840c1160004600c00b1035040041100c0102d401080071688912606240e020708a8168200341d20602e170410754180b00e81100c03c0c2601841d000043c00c280c58038814900d800c0e00c0c480e1003260b0b60005e40b06200b40100c505007042e45c0c4500d4804e1914241c62000040c2c0031404603d4045c0c18a6036401040d01c5004180c421110300010704109a12903545914041c407940c0c0400000d084106a1f000001c02c8a900a0007010041d40e01a154900b842d00440381039004a0004003402c0700c0d60107407072000180c07500c0b40d140c800350080f01007008460a605040c4110202c402d5208104109030524043c01029101c0408034800e5440481e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 270883309 1250 270882059 270882077
    0x5040201050d0e4308061303090e1305010e03160201050306060c0d0f0e030705012007150c0b060f010912031701090b10020a020a09090606051306060f021c 68
    0x103401d8104410818507040c601652100e4a00004034034500120a00d10604c4420440d803c80d5102c070300e812101d0083c1c14659000d400072601c491328090000103801e1092803c259896102d1400c8141508180c0f00b02c0d40a020423104078040210030700981c8846a81c460056003005d41c0f0440354002c80315a8070f406818030070000040b41e5503888040c00c40d035003055008100e44882c800568014107882d8055045000614842c02d681103914004c0b85090440341d05944006014a0b1480341104170840e402000341a84940d801c002420210f010750902c14449607150300950340047c3c200348074070710401001385106840f0903803242030070383e00448100250395800c0131042103c0314a283c26261160341000c0000c80c02c110400001e1008503a400201502c003058030241025914100b050782e58015540c0000d41c04405c901c1d05121030440c60b40a03400302c0e40031b6900403407001e6448000c10300e00324420441000068440d0000e0046607002100110541c100348002c2442509000c0d00300150034103503500d401040b83c1c00d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 270884559 1250 270883309 270883331
    0xc0501050f160321141801090c0605040906170d050304052418010203060a29030f0a06080a0302030a0c0303060b03070f0305010819080a090f0801050601080a05040201050d 75
    0x14241c03190304810440894840c0000d0902825040c259401459410001c001104081240f809174101842e1801419112500d8028481d10481b0144403106031642d600c0e20b00c10301096094010600810003500d035140d40f02d04004400040c0c0f0901e400c203220141070440c5141c0d15140001c0c030540c0f400e0032850525200d494500c0c0c03060600502d220038855074140c0d00c0e283c0c00002084070045014400d5288901e10030508174031214203038002110110b40c0000710603000c0141101c641212030b214103039540a07404140881800f210075800c1980c00c81207659000c4100810f8041c03030f100b0b00e4043c21440c0000e0904845a580095403403140c801e500080059080b9070404150003078010002401c8820300342c549914109030010030101d1043e010030000381c14440000f440c12000704520380b440e081c3d11411850810242c5401e1802da03c045042010414441c00008141941e01104405000c4141c004507050030306000051110340094102c5002502c0d280030b000040c1e030801c04031a904d040500c5c001c14022009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 270885809 1250 270884559 270884587
    0x40b030c1302091801090534030e030a0305150a05060a030e100f1407140a080c0c06071e08060d02041a100c05070803040501021f2003070f0c0c050105 66
    0x8400c1ca180c000400000e4241c130f000c100700b01181038450640080141307544005400351075040454450750035071001c19002240c111281181412242c1c01c3c10003240140b10041082d1031503100c142140d000070354500901805440788151322124003001c03541051b15900b050000380c0c40344154400d04050594a44284001060a0182c1c0c550541807000411080c0040c03035100000d030110100010a00039210000313031480380102d00d40c040401c10f00c42c2c8a420220306c110140c81596020703145141e00c00d028440f04440060801009100e50074a540d40e290100d0340100403c4100c00d82002d180074007c1003410440c0c16165900c003801c1068048402041300c1c00c120401d02002000c1014050f007000035018144126030300044120040c0b4402e504589110b59104907141d143e0080740140c0780141c024040840b2040d00c041d1041000c1214094002031240d40d290500d844200351001d55000000040108500d4a80082441d400141c06007801d0351005d441d0b61704c0390301c5124607001d218148440890380d00202001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 270887059 1250 270885809 270885817
    0xa020a1a090121141e070f1b020405070c0b010602060106020307030c06090b0c04080d050f07140f0703060603120e0a09050702010b0d05060a11070c0501030911042306040b030c1302 79
    0x1040c4410000a070302c000e02d8100c410740c21140e00320f51484a02c0003c2d250259070404c5880f4010b070b87c3c0e46000c00c104c00b2a007140d420941b83c01100c01c81845010810150395240305080c09214107407580c1c1c0010281c0c4c6840c18488005138071820954020398010000150040116000c26500d4070b070045401c016450008001d00c41644007510a4404070100030100308100010300a80341071a084552940d0783c00800c0311140b044400b802d5040034103018950000702d80d0220709a0500d0403d0a60b0200651144218a000c6071584180d40182d1904020000c4c03007170346048841c401c00e0310701e0003440a10209012541c1d6a07142d1142c5003500d0358850028202510039800458624001041d003085201c0e241071203561000c00307032551180b103850520300d541010000d10881c0e520b04da10201403d10140b4141c01900201071100f810f403a00090000c1525081d500c40c802c1c66544014910b91030f038004020b02968a00010060010303000313a14160a1622507903000804859258080b218030702c202800711032080c06405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 270888309 1250 270887059 270887117
    0x80310081015090603170c030c060c0304020901090e340f051203070320150c0a03110f07150e0a03050a0f050304020a0905040303110c0a020a1a0901 65
    0x10030110400e071075256002190716003000b01009209a4403008000c00704c4145200040400602c060605c0e031085034500540444100300060fa030814212404080c01c00008a03a0050098400010042145010510a409441d907600b080085112500c048c2b0717518403000c1032400d03140400c880076141c490011181031030720700c14502100030031607500d071041000f900301d50080904c5640200c00c1c0d401d20345000016507009035010f81e41c02420140c2c2580c400707088900440600407500a045159016900050745203000707800c018000c5581e03804100c802811200d40850070b80e4841400c00204080d490b8100950f03140d41e801510390314544119070215002003c520411402074003030b18038201d0601d50050045c000202c40f40e2915008006014003c403424442202e00039404007102405110101681e400507612520074100080c1d1100780142600e0141c0250304030745030b540d21203800341d0110705001c10b00e80020280c0c6058103242180b44c1d591030019005e005c407046e0400c214a40c0320403501891045a40a4107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 270889559 1250 270888309 270888313
    0x80f22060b030d0c14010209010203070201050d14040f021009050306070e040b100503091603020a1a070606140a09020c061315050901062621040915050103150f0308031008 75
    0xc000d001e01004018201917448000c04046007a0322401802152030905059000d14a000c2c50750f801034403182c0000304000401c0d60303290300821303d50078444080740c0618006c401c2070322101c1c0148100040c840710009503100b04940442c080095840015085800c201c450503c00300041e066401b1400800c8141030040d440200e1500649916800c41c008cd400b0b002100e00384c41c0718a040e02450304d445142d9200007500107040010401c03105041c0c143c9080c07280b80e00c1450a1400c041d81d195070b41510074682005411540c91714011010f850030381800d00c0144071141e02982058026000c0300e071075000080c501e10005815220380400c0003801d07803e10606070030040c41008242002d0544500904282c0079214000c0f803940100b001d0f40300400424500c400c00d040041c08c90031050807140e80214a0001c04c1c0084110602010070020710b1402400303100ba58000c040d074070076441c210004040c0c425211110321070407c031714000d10005c90080c0a42003520781103505c40b5681d86441e42c90b0b58024007558010072040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 270890809 1250 270889559 270889573
    0x2090a050a02070c0b130f0e06041116060f06050414040f0503091003020d061a0730080a0b0a0803030c0703020307061b0f1e0e0303090d0b07080f22060b03 68
    0x3800c407140103842d0b099182c00c841044243c0b0380c1101d039400030b941e000e0384a60902300390015034a4981904031001e0f58119050050401281d00c04011003c20003103411034140d602c80000d54060540ba2249a0040004540c02c7c001b4070507207010001c042e08081c0c40600404805180030050000400c115000050098400213044100101c000e000350451a00d585005041550005000a00b50500c9101249184805143c0700c803e503644a19074285404000144112912110000b16015907440d100130058654dd001c62030210315103030854014001c514807580007864103011074080042580e44c00091850881d6030b41c00603040036403650042c0d14004026904280d1201c6c0381410710410360581c2c0c0b003a5124134655042000060340c030010064011150000d502c1001210f03184510040d1500c41005019a403030040541c3c082001c2c806240802c0d0740c484817200030320500c26403040d00e0a500c4040c154001640f810081135600117414031001c4610802a0a021340c8140300700f039030117506002030040855105c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 270892059 1250 270890809 270890819
    0x405090c040906050a0b0a0807020a1b06020606040501030c06053a0b0f011e11060f010f06020102041203120b0901170f150115110106060309110301020702090a050a02070c 75
    0x15507403190080042c028242600050941000018042941d0040151504010300c01500f2240000024010402c51081c02d81071004112400e06840c500ca1408041004079428080040e00d0300310003406490080d80740c0b10040001c50700e240488000d075030080c5085507803452000380d84041030010582c0c4148c1100d10807800118121031a030b0521142480003020301021107200100990091062521404500054070040c1e51070290702401403061f500e400c01c0081da05003154020318280707017250390096040d482001409141c2e1110701c1c60004040f5840258903140c102142d8000103881100006c0620081c20881200003140d030308222515400508803501c15030752440c505110500a06000800c0c0c0501c1d00e41126581c2d0101c2c0160b81c0700c560002e8554180d2a095051a0044a0344005810050349001e080c040c00d1082c0140c9004040d0b41c0d8011401d5031880c2440d0410310000c002080c8a80c1c81044801c0060316140011640300c1154040000c080c2e69001c5158042d11880c5c80007404a1204072010031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 270893309 1250 270892059 270892081
    0x2102a0f050c07140f01050a0c02040b03030d15090506031c0e12100501030210090806060f01030b031614060307120c020709060f030b0a021317030403020d050606090901061a090402040509 82
    0xc40d40803240502c01781640340c0107440c00c2c4602c4031310030001040a03004d00b0260420760418140050050300701c80c504404190a90100c41e0f200e40301c0c620a010068081140d04680c2c050160820070803800fa02402200341c00d441040400b00644806000350303140a00c00711365440d4056039588641c1820340300c2040001742300100405090008034840c000303849060b82c0030b034480c2c0700c80d03070555284a0040a080c0c49450801c882040240b45641c101a141e0800c4c404a880610001c1e08110540e00003201280c1443d00550345956000d140714000d500c24410401b041c2c0e0b100e068030781045001200091601140103049040044070341194085a081680002e800403480c0b4580088030301502034403c0c1e40d00c03680381a00686c4980642580d600303c0900c8140203001aa16205499007042c204482c0340640c0c96001c20034185005800303030b5681e080901001140d00b04424110b82c4a0b400304000c001003410030740b4602c128107105030219440c18002c00c5500d42a01ca0780c1c105d030040c000042c030314016890b140750030130 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 270894559 1250 270893309 270893339
    0x30703020d050405010207050d050c0d0c0e0115120c18080d08010b070206030106140d0609060e10150e2403100911040311061902102a0f050c07 63
    0x200144100064103195501c2002910183c401c140d0150652a00d09004c20980016044054541c3c2c05400d091980c55660300c0c000c020a40d202d50fa46a03159071410002c4240000c05920408450421100203081c60b91310401c00a00d000c04820001014050400210341400c03402080c4160884043d0010440c04000600c0400c0790340550b54543c8560b88410485c001402043d40082d0809420710041c001c0c540610b004c4465030354000d0400f03041015894140c42034640c80e911441d00240c1e0382d003061026a0080340300c240d2098285503441411450304074042503280c240001c1101700a28540310190590f203450724215481c054522a545c5090002c40004c025031041d2640c0003240c1e0349060028600303032035004400426116040a40c2494515128841d2207000c4200c1154014402c000d04804100082c41d012080c013000d5000305014108c00156204030740007040318030804400c1c202017000d5803110409071030303403c101454003244841c10810261424020b6a9441a282c0250b120200d105c0e00010034003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 270895809 1250 270894559 270894563
    0x70515040501050a150e011a3001230402030c1c0e0d021605010309030e0d15150b16020102070509070e01030f0501140f22051801140f130c06020307 65
    0x5c006003001d41d804c556451409129102d66071001d180104001c80d1081080044650011b0100e8581040c5205200108944018000340c940d01c2c85400d4903582e115001103030150100204800580441d03c100b80c03200080100c3d100e01c0b5640000001c0c19484024040d2030f030300d2070321400c429065040d42c003088000c3c01c0d070007c01c0003852192919502d1000c1c4005494100001003540150000c1e040200440240c00d407000c040c0d080c400ca0522084594440940801015004450710641c1507503a600000c20317a0603896200b010483c560500340b200c0030700c00040703d4001c204814840c0043d1618030041c3d0608546500c1107034441e514404020b00f040d0444080c000241c0309990400010b10550070070011a4001e01440074042041002420715041c0002034000c4114010a034808100038403503908442084062240f41643d103c10510500480d400404850403403070703200a0289403501c0780d4620038540700a140f100ba00c00c0b0300001c14030110f00d0b120048036094200d44111069a01e807a0080d551382e04c0040c3c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 270897059 1250 270895809 270895811
    0xb1210050c0310060305070c0f140706030b0105220305030f070b0606210a200d060e0f040f21051c0618020a0318060e0d05070f08070515040501050a 65
    0x5410a410841120310030384140f1440c445450038120100c00624004150340e0031300c507603000701c6804509920516001c4500c00e4075401c1203200014800f50400090354008010700d03003818814000d581c0c00806844540c900c00c04d5403680070040951540200119074005410b50000269117003660664000624a10b4015003002e051500c4917010301c20341e0321810280f4003c00a1003400500a6600c02c00c0d40d98105040f11004207088046950320502202010b04140c074442000485006074000c0d8081c407401003a000f40201004d00c1c3c03000300a680e107c0010300007000b0350044003441c420070503481c2c081107008862603001c0000101e4001c010303006602410b00c144000b03111450490314031a040c0504804c1d1030038411036000c8001e5816084000c0e4003c502001e0500da02c1d0704858071b1a8101058084449000c2d00d40401c0d2981818040c2d400c10320001c1c152010030078204411130100f0100441c9141c100d901510403581c0e00c3c0e09090140c1040c10701403800541c03140c400c01b070006100b0150060b034098800818 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 270898309 1250 270897059 270897061
    0x203273d0f14070c02060909070512150f04060e06010807020307200103051305100b030106030b0c0403020a0806010b030112030905040c0305010801320a06030203030d060305060c0913050403030b121005 88
    0x20584103000c4c4080c000394405801c228444641c1003880c4515048849400c042e402d0100003448106180c10480301140003034403002099400340703400309101c00c00c542c00703580401000c0d060095a20007444004c6c0802c0c18403040c940031030300241c070070400c8031041d0b90002c0e000c107010030124135030341c0502e0030b0380344000c0c0040c0c2044042041016040107006003aa400001856000084150380c400b50000d07482c101d60655903154000003250f000b440f094400e40c5800d04640d515429441001072022482d0402403c3e5440f103c018011044044100c90540b0b03880d03480090f14040d14030741103170b010286070046500542080e041e008041e0701500700c03905803a1031100078040b240080000ca1300700e6274000040c4d80340180301d01881d6641d94040c52185e40101f4601e601203000c03500ca03004240395a1101083c0940503503103403810030a0000511413280c00525015205180c00b280e440010306101030402040d0300c03c1e81d00c00110301054080c0c1d1013119071620107498281c8800c2d8100301180ca07015941c00c028103c50403e8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 270899559 1250 270898309 270898321
    0x5091608040b06010e0a0602060603060a0603020102150c07080f030a0c0e10050309010207060c0215070206010b0a11010617010207020f04050408070b04060b040203273d0f14 76
    0x1000a548016a55100055a62500e42c103070491405407010f8144141699a800b0648510038607901501e0550003d04090506400789841d0800045c2122a201e103040008d20041c2c2e070106140008102100b0348100c15101e6140c0341242e40300383d0800600c13200c030004101c0900369554000d0b40c4504040b0f0401c0107405502d140035201251010b2049074403c10841d05190801e000b20081c6400001c10000141000b500da13070740034225020300c242c2801582c424012102c0340e50b030020915a1003c3c580c40940815450700c0342800c01070066100701400c1c4081c8000c0142c061809502070401406103041510b4200a405400d6000b940004400c2c1d010e4a04410407000c03a041502440c1e0007190b20135150b911303203071142c1c4400d010802d02410031902913850b1082c0240d59569400034600456849070001cac00c1c600d545490792114003800151807480e0b048a240c0c140e0300c00c445070b070203d003c100c01200300c600d0040c4462030715480210702150b40301a6280543c002c0d0302e000c0a51105a122850300c18102c081d07100c40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 270900809 1250 270899559 270899581
    0x10311030609030d0213080607050418020a0c0303020904291806060306060c03070804030b01090e190308100f0b19020f280f060504030207120f1101050c03040605040509 74
    0x2102c2e511101e038403c120302001aa0b09038014501504012420482191500308030b9040200c10b4800d07400142c40070034144030000c06014415071400c8004000c51030807a401d080079040744800607010f018554003040180c03940e1140c1d00b1003032481c0400786601c5240300c1d00740c0e080b01030780c0b2030144440d0061040604a02420440515190003144000c1045042d56100c60800c1259884446901070b180010720005000500c00006000554400d0034009070362f6041504c4c220469182c107030f400c044c56001005002c400e201c2680101a003c1d0189046a159950144c40d4141081e081d071040001c9100402c002811800e10300103006515041e02548201003c680801ca95401e20080348201d540c000c0c9000150100d80d0307000d5003016690b4440d001c08015910340782e140304054048030036941140c41d01c04000c1010f9051000d10040e11500c0590006c840068491126030541c4e00b2008114400c4d030a81080b0a0303005000703032100020760408403580c640d280c1500411540051240760300650121001c150a4010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 270902059 1250 270900809 270900811
    0x105100305071707031509031715040f150801020c010e07080d121d0c030f0102041d06030102090d050d031404080d0b0d0501061d010506040509040f080c0102120103110306 75
    0x1c02444003d041c030b200588100055600d10003244180c3c40000002140c0107943c51806208410014042c0c0f010b0a028040d034080600c521311207410f600030010459149040da1040075001c2d40c00050000c08000d00b0401001d84142d54120615400d200040c3e80c10150010714000407030400034400f11540300620b668505441c02400b0b0150460140c40d8612440b55591403c0c00310004070110f00008912503816006840c0c0701016220f40068401d01e5080c1001c011840381031080d04021458603107001c40003c1c0c4240071003c842035840c5a81c000c41c071556425010780e10701c1e40c401840e1501604003458880d40e0381c049040e0b400c010a0500542c562820006181103105903002f03105140307084a404464401858009000e9500030302c8404d010300410400d204007005003002100c1c540760440d88004101072000168456446984d04110521003521140209508140e00480c08000320a0f0b914200280f03000e00c11011045601c0491700100003900d0b80807080c100d038000d0b40140384554a880034552650b42c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 270903309 1250 270902059 270902063
    0xd0c0318030804150f0612050d020f06010b09010c1e0b0f06010e060306180c0406091205032b0203091b0f090f1302040906050105040605061903050a060503030307020105070201051003 80
    0xc201c0006010400419984c000400c00840c0001d011540184900c110341c4103401c0811008000390b091410808200701030403008500e80018030b1000106100d059440d8414000e441d144c05020841003a03c0e4080c3c0411409203074070001902c9401c0d019291002c1131000380c5001d43d40c038070901c00400e2142000c0d1120301d00541040c2d4850000442d1074091045c0395101034081504002c080ca1440020300302130580900170108050440d80e500d10300140141980030316009004404184820140001c900201301c441a02c2c0361180d130104510300d074107804840860307881c0031000c80e0700020421090000c0414214100c00302d00080404921140b424402400c0302003016540014a08002c6031b000c104010722680d2242e10601c1d10f010010743e5074042800e540d2a6041105c0407070b20740c0018842403400c1c0c00350070060107059a02a090a58040d8035000e07224a5101090a0555590110325040000c2e080f0001030300000d801ca96032418907020080c02003408840078070065180401043c08084846180400c0769 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 270904559 1250 270903309 270903317
    0x152003040f0b13050f0d030e2b02120a0207060207060302040501081305011803080a230114030a020d110102070f08030a0e0f09090a05060f1006030203040204110d0c031803 75
    0x11482ea00c0044104000e4030072075400312040070720000100100300369169403d2401c040d008411b00498040c2c2a03a40380d18210803260805201c00e00f1072042425403200651480200c5004041c040000360704108407008064010b441c00902940c0e1550002413103022a41c07550301f1222141c4e9228012012800b8900a4500007811803011a201301003034100004280d01a60002500740000119003451266614040b00490107210030028038540a100b9813048064a441c0c5502203855052401c0c4a203c05000c0d541d0b412070405610724242c2c07820404d9006196003c0c0c9030707102d00103890410700d611107102c01d961070052055403c042400c1441c00326440454021000031410004082c405030343c406002304120350400c1d0b40e60200c0009981340740180d0700403080d1700091b280300c40f580d04016081500040164030f10704079010901503426810b0032848100c4171140307130041e140d0b04c0380d10028028201c019074001301c0500114001041c0415940020382d601040d8a08000314440d0122100e540c5c02c3c80c480103000300d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 270905809 1250 270904559 270904583
    0xb070e06090f1306090f050903030f0727030f05010c210209010c0c03060504140a080306090c13030b161d040c140c0307060b0118150c15200304 63
    0x34207160461620050b401000041d0b0500e01403400b03800c441d0507900842143d5142c14110451200600c18070f50400f00701f2010b0751035480c2039070f5150380520000d01a617040001c44007510580d40c41401c810b105074040301901d8000c0c641c0c1d0341440c0020b803000c03c2081c0c5065181800400300d1501034a001307520700880c071400e41c82010500040c02d000303400c000c0c0020f062101c0c80340d4410000da2002c14030000366208042c0007580d800d040c10081d030010184040b460555001c0c1c0902c201280944061703e51003002150310120a507203103801c060f0180150745801e00700481e01a40801009200845580b1905801501c00ca02400450040300c90000c002486034000c4084800060340d400c0c00d80050070000d1580c1080e228004006003a024250b00c04416240300350404103206007007041c180030380390140c4024030f03245112040301c00b00002e80441c44e00c9080002c0b4490802112090b0041c48a41190b42d0041503401d407481d9101c903607801a0140a08440c1ca000710011044041c1d40200107807801260030080c41c402c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 270907059 1250 270905809 270905827
    0xc080f0705060309011d0f0f060f16050415020a1202070f09050c2b180203030a270f0e09010c020d03020313080304030512060901050609040218040c09030b070e06 71
    0x2ca6400a0054030140d500c03084003614010304c40d191007104000c8603000f0314828110f410190b0a040040001446c07e4101009101412192620840c3c00845038158803050f61010307201521144075603030140d0305a546000e04c68882c1030f0003003421540c2c0d600502c6959081c4000f1003040740c49026070300071118803c82d002c0041c042042142d00003503000701240c000524100b00001020340030200c0600030200108800402c851034a0107000c0c0c5a03600b014041d041c5c4a9100070345c0042d4885c0941d415a0381041105040080003543c9000a0f01010388000b5030081040d4a03070240101082d0a401100031038655407000c100c14000503c02c1c50b10014080d0b002d8902c0c40a4104210080d600241018428030303031050f40341c80418441002140941e02c030351a05540c0d04001ea454030000c1100030322040c419140c81e0700401154031444c0c1120f9404000300c5005903a07c08107281c0380150311a080140d50098500b0b0000100190004411410303030b03029909404181d03842c0f5904883e00c4150181d42c9070001014880540d07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 270908309 1250 270907059 270907069
    0x30b0411330d0e0715030b01030203060a17100f060801061a0a3002092404092012040b0c07050a030503040311010f0b1e1008040510180c080f0705 64
    0x4540380d4070a0007181460810003007502d400c00c2c0d0303004400c2038070043c510301d01e421b5018400d0720f00b2540c01b820190b04610b4040000380e04e6010301d1241000400c0a02e070303c01001c10041c0800b01880035404070410a000030828504018000c50040604a600e050404100d07134029080b505941c18a140000b444c0181d080d004940203042c0c01161103111036a119102d031030010851000d612428190001070310742402008100d203440c80a9580010522000c44148450043c802200c0503655011008a03a20188649440194568002000341c1038404a030700400d096006c1c40c51800380340100f44030020b03900c544400034114414084000d1031544083c031070310000f90084011711b40c800c1c00390070002401d0100c5080d69007584c45011004010543d0340345040032038584000d10f91740030b00b0b04102e5204900c0c101c4001c910302121018000050000c501c000904105040009114544408205010300b8494050481035405469000c03a070303203051140c02050f00d1600082e0825016103c600270008a0300d400d040c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 270909559 1250 270908309 270908317
    0x180b09010909180209060f0d03050a0203070203100b1813032109060917040308090402130b04140a050609011209031b0308010f0e13080a030204030b041133 68
    0xd041c803441080005150350240704181c400c0740c28002040e10b8202501c10004103002c0200203520407446004c880c1e903280c440e18403202a13940d1604059544454030102a490b50003100c100a50511031048141450760054200500190301502c50a040c00b412020301c000c454800c035281c030503a070342c04038080303010034420042603421503e000c10400507401d1a00f107032419a0441d0380c060f40e1307242c1c5801b106170822800d4414844000c600702c1c0068145415641c4101c22032049241d1a445543c001c11840c4102c1071000f102d030010041035240b01e0782d55540f9503400c1c02e0607814400c12885212070140000d042d003002c02c2211b54444050b51981341d4844041410002410404419020040380d0103880040c1000020240e110501070b488400c2d4962406548803501d14040e0008008107403d801848800e00142402c07003e91584a41c0c1d441c1c60f10841c0300c0840090103194405000c6010305401c0c00148240c068010b01d03070103010345081d4820405a0408061080740c0d40c1625001a04c0f8544c115540700c10304080c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 270910809 1250 270909559 270909577
    0x1121070b070f030f23030f0c1306030e0c060c070e0109090c05040906150909021903050601060c0f05070b04050f01020106141c0b0702010209031b010206040b0717070302041401180b 79
    0x417202410418000d900014629090813460388000418484070f010984c400a40c4404aa464949002e0164000c030074904000e206007000e042d02c0341107119410348244404040340e0406045583c403109140c2c8440c0e44c9140394880d0500345401c190002c21403000c58014410301c036400c08000c00c0c100d403801040c0b10080403109002e40f025541e680b803030400c0c018010f98201c003d04008034003140401306c1d801005400c0705108248071528402030010000100c0100d2090304444c01c0c6d04102491354500d0620003907011014000901c1e60094000121309005d075040036000b560404d42d00d414000c0400c1006a089400a0181d082035114000440e40345242c00c006080540580c0046030507901c04079a21084c030f15500741c550402503500072640006a0a0030032400011340303000c0704074a5a42201c0c4c0700103500c0344009400a04154841343c0001d003d40d014104203203c80e05a0080c078405440c1c4203200a0081d04a03000d03020400c4201d01c80c1600d551702c141800e0181a41f444144089145080d60340c0340d5a84c01a0342c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 270912059 1250 270910809 270910817
    0xf070309050703120e010c02100e01120e011a040c09052103030c032d0103080d020403050a0c0608090d020601090b0a050904061e1b0c1121070b070f030f 67
    0x480d00040d10502100c0001c6200d0b00140c940c1c8960480060300d01c5004203561410010b000410304056622441c80170300c0900c030390070724900300f9403982d00403900c05001811011aa81c20680030b840500e00541c01800240c0c1c884489604030344040c0100001c1d40c8200780c54800140444400b840b062070546e030514101c010134245030f5a080104035007982950012124024925004400c01c1044003078500c99021007800c03200d00d04070401004501d40509501030002500b41803020075006602d80310b55040358080c40e0004211007441480d407600120040e040d000c2d400000d89007001241e02d80d00005821610600103070042c040750b03030034000a01c00412904904651010f000c910028283d240c9581c505d0280340103150220321a500b08526070302c80920803d504603c64940464403285004030003500c90079000c00e00d4602c20714046401c00d00f81c40c0c8500c518042e07000503030010310001701d00c4125403101c52143e890107441c041941c0d62460030715402411000b5203603500c4c005407503000901c200300c0141001000c0c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 270913309 1250 270912059 270912071
    0x2091e030319110606040b010801091e11070615080d0e060f04170120090d05010e030a0c02010216080703080a03060e13140a020f040218030f061f0501080f0703 70
    0x3541c00b4010300c52416940c00704202000412129805101d141d0b88440281c9090100450050000b09448414828920765541d203140c110510500007040248e200c15190040c0030503406141c1c401d80035841842d04131080b83c5028014914070010401c8001140e5030350001c0c1515050302e07001a101c04280b0115141d00c10410020710740c4490614028102500200607064180ca00f50300000b400c40755040440d45401100d008540b8904043c2c808440074120240c038904843d140e17a01e0701ea4050000e034014070046001c0421450600391340711004ea4103c500036402c61b0414503001c3c9103088a603c3c04e00600b03045800859060000c5a0490001c00400c103291034001032803030b641c110340d84032003000380c03451860000e0111404060001c2c403064060364038824400b41207241a03603800558511010a0118025170b004168070710140c800200c02c070084003024094814443c1c0340c03041c0940310041280c984450304402d5600140d0f1400c056405001c1c0c03501a1683c0c0d0150b02d580440e505d203204000c055504250b100d407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 270914559 1250 270913309 270913327
    0x1090515070e121b0f0d030f02120705030a0c02120d030c1b1a130f03260609011503020d02160c081209010e0f0d0317160c0f050304030b180c0402091e0303 68
    0xc95246800c5000341e4a95801c99881c10300242444284502b8070f00010f82440750001217540801116003108840c2050100060503102280f01d80e21a20076203401030040c641c00c1520306070940c018102034440d42e61090002c00704400c148000d4a0001d0b070107000f8071a0100c0085a42903003036145d540100780201c0d15031a480c21940c1e140700e8101c25480460002d042021408100e008101d040204000140340707012581c41c0800101e07807030040501c50100d07003945802d440c1b15010f009604aa0704581110b00566403250842c0c039503594031880c890120341120340c000d800103884001003110b003c400c0104d1035030b07071421107443e0045514564000500c2d07401001c034403900320303d907a035107841000d80da00c03e0f101e20324a46144005d5281920004011011103d030b03690342c098000743d004503013a90440c1d21040e80c80e003071649030030907030b185000d203803c018120001c89060108103009840300c6020b0881e4042120000704c100d60510059026100186400c44030306141a024143c42c105034426034100a001c0b2402c00c0016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 270915809 1250 270914559 270914569
    0x18090207170328090f020112110409090c050d0201051819150f020c030a0f0c0e0405030408010b04110904090f0b13050f0c10080901090515070e121b0f 66
    0x1c0c0c800000c00c100d80c00441c2000c40552000f4251031110900801010700c4c1911400d40c2c841c00340ea0020b04002c80c81038004000c212a40c03194945d501c3d692030300d030386aa89800c00ca900800b8001d00075120341c00302c2100001e031890700183d90400300d076043c0d5585082211080d0070441c048008000c0e107500ca0407504440d0f18400740825940020120050112040d4882032005441c0a25400403c421900400300400076518005068610700b54400941c5540003a14240703ea00c1003407a03081500c0001255040c401841340004c054015a14404003c0002101141c20002204c440c050788554078982444a02c640d480e041c0d1011746098083e0420411021a5684040b042075003268209528030b080100c0c04148001041048503034103449000304800211040050b00500000382480208407200d00020340640080d0400007160354060120707180e40e1303401a503203000d10404030754000000d180c50510f0f00952520066032003010b0303c01c0014103e004070b409211a40000032500e02074000c0001c0f9081c020715200c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 270917059 1250 270915809 270915811
    0x4020c190c09020d05040303051503070501110f0105151002070f03020409050f100608100e0307061d07060210050702010203041a06011815030b060a080a051b031602010606180902071703 81
    0x45804c0018030b803419160180450740050700c4094034a580b00540c1c041d0380c400083da20305a0302c0c02d003042d48814200b481120b10b0052003c100c0b240769420070003404402514030004d00e03142c4c10110f40000340d065074004103d0752006c82e4402c0d0030442240020800141c107240e413111200c680690150341e0b800441c010182d2901c14544030b01d40740b55a41c0c0800b00040303401803000110001d40800f0911812003803414081c0e07280a00300c0050000ea40d1200c0c80e428201c601462904050b01c20340030307038804650f608000303902ca14540d00e105d003085050000043c0034070300c18070859108941c0840c05840c40402841414012040104001c1c180030034003900004c981e01d0b24648200a0a002000c200283c84410000702542c200e103200034001c81090000151458204180c0e40e40084030180004083c0d0f1003c412415100b0032000c41d411741c503400800d200c9880c010780c40f401286146500203000c03440d902d140448440303003007170320f00040c1c421402d505003e502c61503002812a05d00510400e02403041c950400c04460344 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 270918309 1250 270917059 270917077
    0x510080906221221020903031c061d09010b040504050d0c05010b1306080d020a0201120c02010b0d080306010306051f0e0a0b0a08150105041404020313120e01020c04020c190c0902 78
    0x400301300906041000c440c1d104010314500c0c04194101450000420755030300641d0b000e00c0200603101e240b0400c0030003681c0207000400151b40701179022181d092b480d42d0810010b6500001950800402da4000d081030b02074180540c0d413000c001e0a182c2d481c08003c6454cc69071000c21200ca548034061640a84e9a140042e0303070604074a50b00155892801c1c03803186c9040600005075007950828410b90000d80e03088408080c2c840c06544010a00b45c00103d0100d00400c0d00503034659005060f01e032401c0c2800203080145101e8002a24100b0070300d41c498007048965900030714400001807a1800465103a442490405038141c000303012444d040c0d45900244400e03070009078104000070000c4041100b20901c0c6e03128117040c1e03402804c0091500d42400c490705210390b40c0e51080d40c082c94000001c981c80e18401d0944101e046d41250b10002900b68843c401030000032580c205130300611505038100d24a2a0900c00c079010101128010682510403084d440114210f00740705503003080802000081c4080c1600003408046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 270919559 1250 270918309 270918317
    0xa12060b04061e2304150c0203010f06031e050f030c0607080c040803090f030307020901090e010e060613050c0d2307030b0d030818030c010605100809062212 69
    0x90a001004001e510001080011621201c400c110500e4001200344110344c4483ea01c80440040d42c84012168411507100166095a0860144041da0722403d02c0254a00c21402807000d00c00f003548650640b0302a00011b44040861424844003904643c10001d200344102c040e02c0c130011027a0f94150960f000001001d00c81c1e0010320070040541e034804c480c10360101d4400308a80c10203060610382c51b46c0b4011a010b050055508442c18810b582d004c00c01d507801507500401451282da11f410342440a0248407940044640c280042d213011000041446c0f81705110140949003980c2980a001002d0540a880320b110308008026402454203240078603900c42500b0220032031021403070050b5044000c0000c015070b00b0149411050070382a951032140d0854250140780c10000c40c1c41d02c1403220344000c1c414046032290b1000041896018206400c1201140c40489018002005600b82502e41450440d2100c4850700702000041841c11000301410840e1040315041040401035075407010032a0120f0070340d001003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 270920809 1250 270919559 270919567
    0x3060102010b030610031b050d030309020f010f17060d120f0801050909060411040b0d03090905010603020306090f1b070308060901060f05040b030910111c0b0f060a12060b 75
    0x6560240602030b9040001d5008011601e012100e0702110001030200400040c08046405030340712002241a000c0d0030000c01884480722603207405070051030241700803400781d141b0310300f0052950301445220941c482d00382c8031000b00c1c20030074080171004030b402407c0c1e50703002c0780690003407011412034001101e90f4900b54442072414008401d000d4030385601644418880d013480400c1100c4810042020b54003ea48011107483c1500c10500182c05080f80c0c001098001e44402c54060a0591003188101140c44c018020002e9980300c40c802c130140c0c803080380c800390014400c0000c9903c4492103a92145e10000100d1442030251001e00c0001c00c643c050030099000a221009120140c41d010030100d0040c5491308005c01c0c0c0c00c0110704050154000d078400d050039040b0200006407104414404501d8140740383d1010400000034006480b480d80115062058660344910300804d100c040344504420104010043d00d070301900c04080000950010310800c04008a00e003244186a01502904010746030085c212030316 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 270922059 1250 270920809 270920821
    0x608031314060f12090c121b1005120709270509010504110d0201050f042603070c05061b0601031202010e0601030b010b1614010207031707090905061206040803 70
    0x14846041d030030588640c00800658030071181a5044800186101074100341d00eaa4904038241460b50610301760303400036945140d40c1c000150200d60300080d60808086000494000c07010f01c00071170303e14001caa001c1360007004081c5e00d4400410b0b561303a1160716482e1441d0816200d80c00e80c0e6603c0890b2922403042c0c00c4c80a0325982c500b02e503004903540505200006c2000f4540380c0c40300c00c0085544140c56001e00f000000c44403e691060080301c0c0c011010107140c55540741d8940c3c980203800c56245032100b00d4002160314060500b004012242e0701a04070b00001d0301c403400c0000700002d9a101d6400c10a008a00f001c14030f00440060188900a44c0076103040070b00c1d000f40040c040d080d55500d503103004494000700018000240c405c07480b2419103806280040d00e4907110b1441501c100c0700d2000c00f400320034036a039a110308048150000c1c55024030a540341c0c1c0d00180500c000c1112100c05441c00c40200c1c1414800707100201041d40700070350001004040c0003c1e1b40d001e00b102d030b0518600703560589040000104104c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 270923309 1250 270922059 270922079
    0x10c03020d0e06070e100908061503010b0a060203030708070e040c020d02070f0e0c310510050c10090813090f060506190309080d0c02060a0c020712020d050106080313 73
    0x2d10790500c101811142ca44050001d141e41c400403011441001400744a5005a1203031460034042c01901080700c0450601c0c4030200905002060014425800c1c03080d0501035007482c0342d2600c205e9003030f82c000b9402c2d622031110903502c480b00205280200301d0044002c80c1d0035035442c0070b07403440c01200c0d80150600c9403c1c1d400003801d028042c1c0100c41e00a42e060020040840320100309580512004113807626100c0c45941c6128040d030010402d2032101000114004440e80324071481c080b170b90101c1c0c50a0010f000c1080c2501c282c0241040d500f41740d00310b41c0c0a100f0090b03013600b01c40210351251a00510b80000000186a040a160405055541d031103002840d10096840b6034005004200ea800c0e0801d02c100c6031284000c1d6207625204201a11030400341c0c20032503010b040d200000909542403200130000c1d1402540d504080391100308003410500070800450000c07031100282c0783d41000c09003a00005400703215103e102c44804540f159a00d42000607154424000380c404846000704c3d4450141c6002c1200c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 270924559 1250 270923309 270923321
    0xf290a020304030e131407030c0909090804030b160f02010522170d0b0f06120601120e010603080306190e07050714010203150a090605011b1406040b18060402090103030818010c03020d 80
    0x210a0519180c1a0410036030403081560880b20bd101c0040790306444c42c0782210302c50059901c01400107402000340000c0e08041341813184c655407680d40762140032020940407426603006840158400d54020302074080c403501e9010a030403c03070269040308160740c9814102c844a40c807480b891800da5560781100800c43c40c050003045d502030001c40b012070616501804031605a140030b0811414400710145080e00d4800d40c0d000380c0104011000208070095581c203000c0d03065841100d00034841c42c401044140c800f20808410740c00e072140c5195107905595081c3c0b003500c045d030200302c007038500c040100800c05088909000031032084025080003001003041070300307004a200c070b96008180540d040c08024086a40c0c0502c1040e40e21412640058401025060100c50910308036801003040c05444100030a0100545151380140d000380c1d40c1140080c02c81c0d004503268007054500035848003140004002103032250783c142d41c100100c0d9040792280300e800e0404030b003180c030688100004250082581031000099200ea8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 270925809 1250 270924559 270924571
    0x3120c13120203100c1809060f05010503090604030f020a021e0a27050a0e0d0903200a0909020117040506040515010513090302190f290a020304030e1314 67
    0x201e14074481d40080d403a0007000d010f00e001d4964400004000900c980e00d07400040b4010b02c81d0343c24060703c03a01d015000d0000d83c091445071030203c90340058554410803c0703921031000c00002d82401d4540c1e960031280ea801410700101144210031440025945042451134400070061501540030205014041150b03000c3e0310420000c0c4088002410a04010010149810580d8400100c0d5a100b0301e10700b00815503038061500351b10560401840d004d404c481c04106a07801004511008098520703115090301c0d04116107604840e020508001443e03145c3c00c46040b09105042001101e42140c1c141da404100c12076060380d45038002d006002c18002c1c18054050076140c608004a00c940c101000308072030103044401c0c1d054042c0d8a419660502d4030903c68800d0f014a59002e07011100008c0c1004107200ca032220081e11900c103050605a254440c0f0300317118035a0321408030f40301d64980da4560705400039000103005900707002e0300a040c144584c0d900442c500c3c1d1119400c2000444404012410088450040076 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 270927059 1250 270925809 270925829
    0x30f010b070812060d060f0506090a0c0e0f13020c0a1a040b0106050c0708031314030a11130207081c05060307080303160908030f120f01030c03021203120c13 69
    0x9000450a604110703544090140f480d000c01d130321100c0100341040c200207000791a852404c58440c0e440d048079040a40110070850300b000c0f00f80c5034000400c00312045600003201090000911050908010001101c480e100030a15100001056840c400782c0e03201442191454018205038010854440c15904d41000c082000340a50714061740c8818202d04107005034810b00c807010a01c50030b585020001c61020b001c5a205603601d4107110317091500405c505004480b50010250043c000c2030600040140303049401000002c4101780740018002401c0900000034150340d003c1200c03201044800703001b01141504609103d062a8206160b00229000600341d036102c0e401610040021400000a0b01c0e000851005821401c1c1d20b100c0081c0c5610540d0340c0016018040810703c00c0306810131801030043e00c403401c034407440559981402103850344824040244074007818cc6051001d41405c581c00c01701500303100116454207466804401c1c100008079894000c9000024600c0b80300440d00c2c60300401011030300e00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 270928309 1250 270927059 270927067
    0x305070e06090a0e0c1002011a120d0f02030d060324140718050411030601030501150807030b1201051005130e0c130b0a08031306050301081b040f0f02030f010b 70
    0x400a5100b000c064000156540c4070318940000d54000d20104a1040c001081c01031004003448019018041010000070f406110f007005101600302801d890030250382c0d4501921b580c0c045503400351607071b038442200389045210500081c51950b039240308500245000c0d6490200038005011035101040101c4e6100120604108103a004e08100c6064507410075240c3c10a005015221420b4005091556103e1036105080c018144103850090008600070750342a40d00b80030981c0c0700c1d00743d070b4010310001d004000050040070004090b284207600406000700001d0480312000c4007109505d003560000e50b150b580c0c51030075800030480c502d4105040c024100720220280000c2056020030b5480d0800521064090381c444c149105e4142c805038000d0840031002041c4519154032000803a950f50810546a04130b01903402c000b14000d802402602d04a5009000404690040d0b82040c623085a05c607010701c0d0003c1d1956814004100c1754042c80303c04511a000068591a00c08032005902c0ca06a00002400d50200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 270929559 1250 270928309 270928321
    0x108011d060f0601031b0c0605060102030910080603120406030e15010b0403030804020a080f060f0601021501060507050f10021c11070f1505040b010602011a09070e0102030f040e010305070e 83
    0x401d24541c0301c9422815814103548010040e1302410396000c140c00b55080602002e845183c2241c04525030f140168020001c9690700401603035070b4401c64007019130141032400e0028100d4442c004003640440064140c501001454400c1781180c1c1044d00b24101180e107800318440c0e0110100850140c1340d11016180820b0351515110146620580c0000790030420054005003d54480c07041e180b0081c0542070845540c0c0184040440d118901502c00701d41c00d510800104c0c0c3c080d807001824014035010015000c68036481c20f041581c1650241d50b04560354001c12124040c0088148010110b030644008050b0355071102c1054600742911100180045500e41400d800d00c80d000b090036500c5082e480050002010941d0130088400e240811004003264100341c01c200c00c01c980100e0032412520148c0017405204581d11b00350305041291203076150407078113500028100c1e501c107130900740f0000010300540f0314210302101c4940c8281c1c825086000b406513404010400c101c0c042025600912000c0c4544526003003031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 270930809 1250 270929559 270929563
    0x1030b091006030b06040c0207170303011d07080f060f0d05100f020c030414130204030602190503040b19090203151006020a12030b0402040b030f010e01060c02011b03091d0108011d 79
    0x60170b69800b45685000a8004900030800038020380010180e1900a00b031220300580d0f20b510034010000c01d84085200002c8010369004002d00400164a9804080da03e9403070318846110010a001e51100a6645480058807606051200c05020f84044d00c1c90003850072224050310f16058112040b0383c0304001301c1d60410404400c0c0c400751803015409400641c07400c4000b42c81c212107120580045403000900108218a66009003c11141c150407008074000e105e5080d07031140021180608049000300015901c06c0c407104004142d0060080b002402c2c204a07000300c0d00c1d141001c4130750441245001c040c0030b1160421160000200900c5c4002c048804041d9240c40b204145140800285a03c44600301065a02c0d0b4040e1800340c200743c1c50f40c584914002c456600c4202080c440c03480000784403000850464451441d64081c141c06031950524098603e510000d0012002c00690800041d0000400c440e01e41c44404011200d00e503a81e0a03103941085080350031140421500c015481d00e0750000ca0b40d00d100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 270932059 1250 270930809 270930811
    0xc01110304080a350703180302011b02190306051e0c0a030c0e0409061d120906030a020d09080d0e030a0804030806040e10140a15150e0901030b091006030b 68
    0x4801c80b41d02044e00703822036a03801241800040308070000c0012401d203403406040042d024140c06951268009800c201e40454003200714000640000c98081c0782509c072141c0c4c1d91442c4078507840603007948551040b4500740c08448080d50001c031405626042402025803881500000514808a500c0344074204850034000078403c07120100c2c20b064403520321110380c82c0200717041d48100e4005002400002c01a241040c001d04003442998213696100209012164001170804001c002c4116500d2510403e0300030800b041d0401030424802c20303020000c403802001e0600a8614480c41450420348544614104500b82c890b0103101d15010b40c41400300c0707038604c0e5100490035040303901400d0501140c1c40340340104001e091000361070b500340d110713585101e2540125640a20b0a0101800404e0402d4981140103004d888580c0c003500c00d50310051105000030740001c01810b5030071400d0300700a005080401c011918160090348207450744204041000048002030048150103519841d08000b400d045952306800c4d010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 270933309 1250 270932059 270932063
    0x1104050a0303200607210506091302041b0809060108060c0d0c2f010b03060907090203101e06030f0207030206010e070207091103090708070f05040515040903020c01110304080a 77
    0x1030f00d0711048000e038805202c0e046500c914400ba2801d91420000c040c2c044500030700461403241c0b1088840b09002030921480340190001490403030b10740c40c0c20210a0096018000071303031348941d0310304020340e13410110101c5428010498844905619001d442d1a060503c160312003291904500d041000c1101d8a204842d58002d84550006000492400440e04401d41586281c4084103a844850902940328210707000303860400024840014640c0c1816100c10040c0c1e00254650300c41107003032000c42c00540185901500d101101c24413543e0350550040080310a1314142c00c4031500140900034240c3c14000e40340500484d20080d450030680383d60003590f5110520a0103010340f02000420000c500c04e010701c7d00208000f0100b8442508070f40740d010034a6205940b00d4004d4400c103c800611001c0114545003156041440803048901d040280006044001d03e080251204000c41c4c00240e0389038485c00091074000c0d4000c11024001f840094200c502c0ca03c850340d4142d00c2400100a4004001140c035180d40d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 270934559 1250 270933309 270933317
    0x1c020601360e070603060e0420030d0504050a0e04021f031d011406010207030b150604090e030712031e0f020d1d0c060a080c03100305060a09061104050a0303 69
    0x824151211203040350a92650109250001c54415040c050740c1020724811070200c15600d090b5502c2009034110348807441a00d614140003c0000c0c003050101e01c00903502c8200780301c6803801e49147d0b00041d0904a0b040e100d030001c00c41c042014401420201c83c9500134044010340f03800541007d4001030018102e48150f100d102000070500013070640302c1d0f0885402c0e01503060080004517421603466010f8041e030a03403030b24052620f81c00a081507100060139000c881e0400c0ca940308540700c00749000c1803060340750441350b0001c00401001600f0580c52080440103032046024648406441c600342c0b2000305005101820141000f1441420350b200d00141c00030900003030740000b61061001e06840c082c0c005e40c2e022150351031400d01e00802d201e11612400d0071200d5000300780d0303014a44c1c14003080030f24003a40c4c044000091030300000a00ca221402c00654000d80c007241400700155480e580d541c030304501110b0b1b0761030941c1c5600c8040108841e42c01350200c080c004603000e5042c60304000115649890300e00c4050108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 270935809 1250 270934559 270934589
    0x18031202040f14031002031e060609010c03120b060a090920190903080d020a0206010801050403020c01081504060801020c0c04060302060a0e0d17270109140307090203090705031c020601 81
    0x4d5604001c1540c08415000302513490307140c004030b2034070285003206082d4410001c901c0004d00d09c2c17410f00304a600b0454141c40e0101385c08000d4904a90740301254038901c040958507501564103940307003c040e003510125650b90460f0141010011002c1d24016044104010240c800001104600703070207a94082c5c0c2c0c144029024413034a0101118000c905920181101303800041c600d81060326a0000e0040101f07030740032540c00ba40e0318583e83d801c0f54400c035000350068102c451002d2942d8841d5040380d03040b040e030217142c04181d0b406500040c103c80482d48418460380d030000b0304031800d60003803080382c00600086a04210f62483c64010624511542c0340756010810000d00710030007070f51802408410260010a01c0e44c08484c040120320755680700880240c500d002c11742c601c11100b140e0505666130781d20107948540105180001500201c2c071485a6941c0c54000c00402260f00580751000c0c510440c1d0820050840314a464245414403005650006031905041c14081c0c455400041090450321119040001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 270937059 1250 270935809 270935849
    0x18020603091e010218030d050f07020a0312020a03030b0a08060a0e210a02070b07020f010c051002180a060f1b031b11011202090f060306030c0418031202040f 69
    0x4000c4950859a03003040461550b8861900c158041c207034a0030740841000a4140c0303030080590f00c00800001d2000207004104005003c0d08000190804a1020b0030800d411901e90f900e60400304071825034000180d101e2841401030644c94090000b10a009072041115103003081403164444d41c00a15011500707071600e2010680c00020400307520040d15503440800c400d0f070388945292150b4020f00c00940107116a10010030035a082c5012141d00da82d0060074014182c45020064442a41d1a10191583c2c015a4003c04a03650b00740000d04a86a4420085544221150030082982e5407504610200500781c2803841d205500004004152071100000282a042d245012a100d46c820b1700d251009140342c4400c0300401c45030148100d080c2c002600c0314001c402c40040c401c2c00300e0041c2d0044543c40951440141c425041c050b000319004100a41558040e00703440c1c0100c2d00b0740d4034007503901000f91104c501c600d003816804a540d90340d03407030071040540c545454580640041c0340304e40968902c070607071030a1800c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 270938309 1250 270937059 270937063
    0x6050a02340b04030206011d0705070b100b0309010b2404031b050402040f061b030203090f0109030c0608180607020a080a170910060503030906040b1b2b031802060309 73
    0x146466000d02d1500311442c080c0b070001e448250038818070302c89070466410540503004082c3c14902c038103850f5480b242884403070348409140d8800035000c103e10084003080884d0034200100114401c0c107900f400841c0d031990300c4080c4243d0380b0b031801450b08088204040b0201d41c1c10720104880440b50071107482800d110305100740e01c41041c1c807036001503407040c03000a00145c01c0c5416100c250848445484082d00c091018221212500349100010300680040103440c000f4a400d81355241160b60600d000341c5529204e0b9100180002e81d50000c82c00302e103d0404004e007988002c20125014441c0130080e010a04148502030341e101d035980d50040c0080e03000700d01c0c2d41540e84950321031040d03003080d00125041820160081c03500d0341918508200c0c424100240480c003030070000222640c10001500d070034501880c00410160039002100d4145410000c0c0504146052040200c00350101d603101400d8440d000c981e2185103824001c2c0c00c440c040c5400d11304080d980c809100344680c41030f40c050304c0703465036940da254081d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 270939559 1250 270938309 270938407
    0x4050607020a1d0105090723031909050106031b0e01090b18040b0f161706041b0e040b100e04110c01090b090f0304050a1a090402040b0706050a02 64
    0x2d901c0c50f00841d981151410b0512514100d0384152100e035401e80782e2030000c50b45401c038603040c2c9108a00d0300c3d0b44280c1070314030388000f1a0301901c45800c004001909400030020b80c1c020f01416191030791a24000e000307100d8160998840d6030071200305801514a841c40d0041402c00500c580c0040c942d89070784114198485409000c02c50b085114420f0061802d8905956114405e03500b002c60b03401d0850000c0e82c0c00262400e141800f4410b13450b030031090b1030110320254490500038015500300c4d4450012700b501c241c0142c64007051000c1c40d00d0b0641905080c07020b2104540404c40420303c00c03102c071a50b41c041c03281c010703104003540181a20040b407076500e0448440355a208890810440d503103052030301400d024600c01024011081801920b01888114a42c070740e9900442c02440e030302c00303209001002a610103040d2408480204a0003505010f0404d00007002c03604030703074051021030400146510404c140e501c6901da02c101000811401c04c01c0c0d03107280303c69810341d000207100007148078001049491040b5003e2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 270940809 1250 270939559 270939569
    0x2010b040908031005010e030327061318020702010806010c03031113060818060f0a0f11180a030c140a0305030412030f14030a111c1a030a020604050607020a 69
    0x1448510150320707002e4a030b0f0380121920407420208450120340c80d8842e0703c1030713652440000c000b103023020031030303030740d0314501014004046101c6142c501c0101d255158100500180c81c40c0110780400c8034903000f0a102012030903074071845480d01c10041200103030b0b000034505400510a20b00405021010b00d010f40003496800e10341c04110a011400306001040301c001001541d04960780d406036a01c0d050030111a0511245c400c07412600920005148407002482c0c0f540d01101d01140800c0740044c01002400f1038580c0c001c1c1e400500d8001981c680c0144c5041218180d201060302c00310f64051441e107034030050500600031844441c4600c441014559203c0e0400c601031900720007aa6a02d45d82ca002441030402c00403c2100400c0103d1810018030f400380d04600e907541d45410304d180c550b9480000c2c16000b86020700f40041030301000d2080320b07980784203640304801030811400005010b2400341b020400c410f80ca410254440e41c45403a83d00016180d00e0b003601d04445096403420340311403e920018440303510507004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 270942059 1250 270940809 270940811
    0x203151f09060e090103121701080105040c05030f0d030b030703080c061b03010605030606071e05060108070f05010504180b09071d0603040b040210200105090d02071802030702010b04 80
    0x900c15036410450040580c811a403a00095607540c1d4000303503051010580d000d81d1207290200100081040640c0000742c803101c51a004051a00200301102042800e811026060790359504120800004980040c00350030120001d01900074203201195413408440c0000b42095111a464203241e01e00f00260005558400d03100d039102d104001c0c6881d52010221080e02d95821440000700c100b144143c01c43c1d05a520035500c2914650b620810310a940d40090411103501190312414402007408405008005200c1c0000d0265549400080f40c40d2228540241c81600641e150800c41a0380240031181100d680e00e416291081d82d100c0c10400030710729288c041d504800b14004205203180c1c8596602110b5145000100816000758140701d828001100e008002c1141c00c0086405490074101d61116090340340340c110b43e05c0c02a585540d401009080e1200c1c1640e45500511010000600541c050094544003c0004624201c1d008001314002d0360701d110f40740e03070000110706214400e40240d28640f101400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 270943309 1250 270942059 270942079
    0x4050307080c100f05180a120614240f12300702090601031a12010c09051504061103040902040b07060b04090b180c270c040806010306020315 62
    0x80082e00c4001500d030a6120720701c8500c50903403060141c0c100c3c0d40c9612643e0344450903e1151010344100d00412402590300540c0084005110000000c1031713000284103002c085224031505660042007100030300030040fa0a046c0740400401c00003001d0382e5843c40c00884415401650a10100701d041c1e10982c1131602c10b01807080c40d1174644815050600f041d0058600f40741840092201d0f1850034011044000d6111503a41c02140b03d940c0f003a0041a043c0c0106a2941ea980c240070380050303101b48201c680642c41d0707519883c08150b11074002045000400c001e4809203000c5003c0c27164010603114078040d40f8148410fa0b20100201002041901c0c080c0080c03100856035151550000e00c1036800058084a45509003040f006650405004810780070758429200300311900c80b4400910700480541008030b0303620681506242d680c0d500d5a81ca502000c0644034441c1814402d90300c401c02d644020249007010340100001c00c05110001240e6044035006100140c884c2c880e00080015035800001c02580078940395 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 270944559 1250 270943309 270943319
    0xe060d02150703080402211e030c07030c050f0a0b030a020f0c070308030f070f0207030201050a050c011509050105100503040b040c0b030403030c0806120a0f0302031605030a0e06092404050307 84
    0x250300c9030045d8000c86164910740b0001c9041c00b4210320340c1031401c09980010b44031403e4242c024406800c458080742c1900d0600080002d40c0d46810b90551041d02c584008080800c0681000a2035000003641514480301241c00c201280304180f1003e0080ca256a03070010328205084204401d5941d02d0aa05d010f6a0406a60341040200e40e00190307000241603a868000c42c0351107004d41038945081403c1c0d006408854595001521107410540b040c60601400300a0507e4100d002c2c071505802801c0c0e000b030142500d007048012070413200c05810160140c0010168846039a07000425241d0043c0c0c0310a458a19507641c0c0b03001c0c0e402e200164000181020003005000805400d9003045482c440242d40d18800d581ea48000c020502a018071045d000d41c00c40d24202010904100c108000d040c0280122403500b05036912240810a1400c000e9071680c0022404001496200b0f9401e83e240d5000c41c0c2440c18400c0520000f0b0000c003040c1d1a08203051b012480048a83300c1460560b801464000c0584002964a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 270945809 1250 270944559 270944567
    0x60503281a090c100e24130605032d010e1b03070203090306060405100b0f120103031e031416030b030609160b0301080717070315090614010e060d02150703 68
    0x1e11010f500c505a940a20036246208034001803c240e4000d04100c03402000d24195854408201c078804030f004403c201e059070844410f941c0700004c080c0f9681d5550f491901c0384101401c00700c0c441c02c008a24500201600000c902000c116054880300d9480b0701464685180803a10f00b8182c0715980540c41003c42009205500400603040303050050b003e441903a91781c601000101c3d1070407942c109201101c5c400c20711410004030701602d01e82c151034a81520b4180069080090790030300760f108400080360003c61865205800451031426502c1c1d080c2031119a550183c0344400040c02024410b0304800500380c0f4001d68400c0d08180b070900c0c00a8180c55590805d882c0c06074560803c0d810703002c22004c10010000c2d164840f042168101c81010010788200340c03c14900c591081c45c0c00d551200d42e40300703501c00800800c00754401400318000b800c0000aa0340f144e480d0440a403010b0450181c60042c00030b004001600e171140300c840d8800811110340501c8000b610000f4503007220003081c49c000000100c4c00100701500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 270947059 1250 270945809 270945823
    0x18060c010b04051005040e0706050d0f020c07170d0f08040f02130f0501081501030f290106030606080c03071d030a06020705030711060a0e010804081903050703060503281a09 76
    0x1e61b401e022140c48059032607030341c0c0704030710070340c03001450803c08014000ca0f50390111100c0d40c910980903103480d40000c80f0614002160304101101106464400d259507410840350341003440d00e080540118000c8000034120880041000d4044e8a4580b8400c0c21580c5010610703007000800320040090b80d40c0d1001d00e80081009000b89507440c428a18244880d214950544e812280c0c803111203040c186080e51000501c08014903100c0c050000940c0005a00e00a041554042d02c69982d00007512403a000c03000303016980240c01210842810001d12941c1540240f2200410086a8040c503803500a800841c1c68000c11401c0a80031900c003240c50304c1004008001001c440f4060803088030910601d2040040da031040001c0d61001c1803104517540075a5025003c495441405200c500d81021550b03040d038904d02010300703220300000766942d04021029070144201006402c0940c0142041c800303441d511010f08921008401c91040c0c100ca450040000c014141c82003044140d010300d00702d0030908405580e0b000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 270948309 1250 270947059 270947069
    0xe0f0403020d0905030a060b120318040605040603050c010c080f0a050c240f0c0d0218040e0607021002090324040308010506070b0105010c0201120c0e010908010218060c010b040510 79
    0x6030811124400d44101030785410f40d207006011b069003900698a40c0c009040c40c01c41103810040700060000c103030b4020f20151004400b000c0221241b00040c0d0208012100740d03800444c851850040c062010800018402d1307a00d00003800d00784840704942c248102103018078651100d0702c0000080051040e90b00c0300181880c1d942c100100c580400300c02075440104450358100c0c0004590a0001494224480710000d4101c000c40103202c0ca400382007500b91060380d0003591944d02d91007074404480e4442c1858070590580414141c05005642802603009441c4c042420390f0608158000c10010349982c0c06006032048980604c0c1a1944007020440b290b0403080100c406078081644030000107003905091080310305031503110300b0042550382890010344582010542c20fa0400001102e1050744451900c9030f0820007505440320001100c00000041c5044001d401c0380300c2c0e603401400382803800321004400b0801e0410454969403103040da4503070140100322821000c0d51007824a0280400310981921480c103980c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 270949559 1250 270948309 270948313
    0xc0803040f080304080d0f05040509040305091009180b180f0702100b0d0204020a0c0b0916080a020609010c050f070b09041d0601181103090106082a060703090e0f040302 74
    0x60b0380e4a20141c99000d14810820309410111144078114400c1c29000100c985904003a81440d440d8008030b050450122005c90215400103108070003490100100d85030816503144c4000d00d68200940150f0b0b40c5003000035601443e80b219000d0405680b621842642107041d005620120700e4402c5200c2c020007070698054001d80500305800b4201c2c0c0d518020b40d00004405014648007194580c03c0c40020f501840301d410401c054400074a0000701c40ca02d80b94001c4040500400d50144505d8034482c1c01e901a6202040507400380d82c003c0e00507107840043c0d811001003400d000280003003905019013400c00d0785d0104955405002000308078111824083c08a030364094070200000c00380700b440b400c00ca10507006000800c1e449032004201c1c00d17044444001003909038410101303988021154200786500107554050059465a606102050741008070540840c054800035041011006125601110001805000d00000180841814041d54502004000039081141306103801c8820300c1105100f6074040f4018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 270950809 1250 270949559 270949589
    0x3140105040b1f0b0a030212041202120909180102071e030305061c140309180402040b060715051b03010e0907060203040f090203040515012c040b15010c0c080304 71
    0x280c3c1c0c00c041040d442c84080f00d00107024100a00305900b0b800031500e007410150200300c07084150000b122501d00441c0301d9500c1042041c181c090203414511450b0004040c0f02080c04000b41136669608400d40019124444d00003c95032540700c00d0181c8075419000e8141d0b010100711100701c0c2035844100c440e460082e0f404000039110760b010041041d0541c24401020341506050fa0082000c000e6164034071080d040c1241c1c5000d4600001c02e018080c2e8003d240d038101806030800c020350815010303035a1020412280245400b0341552100f41c8400e8082c0180651030f40d81000a03070f0440380001c001207030076403100480d44a40c4e5920080d10b120f503044400450a003ea2580000c0540c00041070f45c068550012000820a08002d2106d0003500000d20644003403160840d54202d604d248039209018205440013070b51900c56a000c0300e4038094100e02040c00e414070840030403011a24440c480c43c5c100352050003240070b1520120048412001c850343c082e000d951481c3c0c0004d403030f103c000014000c948100c80307903440e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 270952059 1250 270950809 270950821
    0xc0e1009050f06090603010b090703020c06060a050604120f0c090903021c05031b040906030309050306130203030304060c0e03010f05160203040e010302061b06240301020702100e03030403140105040b 87
    0x1690002e40b9000c94041805010070f03103515000012582c42400a40002801558140000d0742c01c40d05540302c2e808240d00003181f07a80f030711003401001e500c001d06a500c80fa03168981004038045100d01d00c00c84075241c0090540714100712904027400700080d0001d58000805864104c540d004102c842d10413401f51007450364103c1361041141040409000c03a413100341c1907a442c450102d10040d036a5005550b01401000b011840089511504026500030355070796603403a00b02b000780b529121000c0d0890b2900c3c410b881c0d901c001640d00200302c0307500541c4407070041518600120261614200341a6555265081c09020485010300d5401584202d034081c07030000d0080800031017a0b889218030301a01d80c11318005c4005001600780308004101c0c000110815034141f4406407074144c02c0010907548654590040c2d9030010f222895100b00784202102200214038100d036550004408070b100508000500507903000301b01995505100b520f00450300880030304503e10000344814020700381124103e0343c403c00b1b000412a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 270953309 1250 270952059 270952061
    0xc03170a06170a0f110307090f05040501050f0112031404051c060b0d0203060f0606070c03061e021801032703050301030b010e0106020303010e06031e0f060711031806070c0e1009 78
    0x200c000d0b0401346444054403a03440710000c4121464a10360980b0402da030000b03041c5014440d40c2401c110304000043c040c2454034081d42980c01c003074011070901079000018400141c0e0201c0d040c4940c2d40c07508082041c094080c0703034200c2c5070041c4d511295021900d09440240441040c801e6140e4a02c1408100f1104540300b040100c5070001a60181d0164400b10001e9040700c80c0307031042508104000c3c00c00c0d041600541d0b03015855545500115000b50b01d4880420511001181a0315444100705056050640c00742034461a000c40c0420241016180d1500014219041c0c3c250000001a07101c101c2c4051424100a400740e4020310040394410759003800002c081d03826140d105d060b602c4a81c043d5103103920f420000d244003917018103916414054a000002112040e00c0c0c04070034104840701400c2c1c182c82c61a00d00f41406001803229042c0000240b0002c0702d64404011540c078071a900d80072042211144002c560140164407008159511001c000304c1e44600b0241e40901c80e04543d0b111022031516255100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 270954559 1250 270953309 270953323
    0x6040309060206090307021c02042904050f04031d0907050a12061d040c050a03060e060f042d06020406050327100207050c130213170a030c03170a0617 66
    0x1822134006108000048c90f100400c05100d402c4002c80405500a540005080ba1628a40049100102c03a089483c1114040800341d000b84103d40421a61400e0714800381e8048000b031004007000b10b80e40350b07029890901200146242c0020308240d0712468400c402500700c0d4402820000440c000010700504105503004400c155044507459100e000c8910514901c20f80003e081110004000320340031807039031201c2c42c500000354040d0502141d9007402c6903543d0704028000e010710b8154000c3c0810080403908001c014042240a420682541c0145019811800c10192030003009a8000200024a180c3c04000f0703501815840c0d107043d9669110304126541a5803908600f05207401083d01013200034032960261000500036001c3e501c4241d40240001c6ea6143c040c0ea100d01c0b444e5000c1461800050801e00503030180846200f004041d040c1000010341e10090071000070b00b004030300c034680420980f181510b90103181800381c01c00d00b2030418000340005000c0368002c982c00b9000103101d9007580040010700c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 270955809 1250 270954559 270954571
    0x30d09060b19260718050105130e0601140f06070f021f021f0f0c02061801110f0a020712080702010810060509010e0f03070902070210020106051c111206040309060206 73
    0x100b04203804240c3c0d408400702c401003c40141d02032058000f0b214802c0d160290100340c08400001000e43c104420003601c501c070311480090303451820121049070000041d01c5815140041d201e1403c107814600010700144810b0310a0390070943c0400d0784c1c0d003000300e40300c0710031a424400c40344010f00040f00b4a00301c1940c101d00d5000c0d00181c1c04842c801c110303610200d20703042c1c2c0c0b82403a440200f8034004004243e02a40d9a9000d00f0006911a90800c542d0040c01c0315101c100b9a0514000d0004000007801441d06000b810000c081d07503c00001c084460a008000d001c00074421807070100040b01117410203c800307421815040c0d0200c5c490800188100c2c070900206c20558180c2c0d1283c90805a6240044079080310b040d80c11900a00303541408150b07603030104508001000405000b5070b543c55244107000100d1404d000440c20b580c10003205020070755440c240408805031500c40c03c0d07242660382c145a00702c0c0d44e64560b5140c0000800151607548580810024815030194880401040d07031440200e80c0c0f01740840360 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 270957059 1250 270955809 270955829
    0x1050304050d110c04050f091b06070219170f0c0402250311010e0f1c020601050d17031806070c030e100201060f0603061e0e01050f03030d09060b19 65
    0x803880c14a00031010090426030140807548a2030202005c40d00305c460640d030f9061100210f0080090802003000031850a100c210480c00e41d1161a030f004c03620501503018000d1294201a00551318020801e68040081400f0603000440605e0322400c182c650003c1c0e010a03400e80146001c1c43d000781050300850f064103800300310700ca0100017944403580b02c2c806114012801c0000c00d9070212500c036424020170f81400645005040e040441c0524240360400680b14802050360116281107141c0d00400c01a045075400c1e50b850b2000c81c49031030308070340310181c5140f10401a4000b005201002a41c8899040c800d1017640880c0c51b15280c1c0c0b032094407000700c0785200038005140c000740ca0181c1d080800340e003401c0a6050002044154460040451170310050704a6400290784081c2040014140228195141103000141000702d0902d01c1201108205020741030080d0220010310a154600300100d404e01800d0b00d50400031840b003071601c00302602c2d042c1c20031441181c0280c0d12941803a40d0403001c104842d52410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 270958309 1250 270957059 270957073
    0x5040b0409090302101b091d011a0f07051e150a0c0207050a080d03140106020a0f0c26010605030102120f0405072615040f06050901020904021c0b0105030405 69
    0x80c1e20000d0500c50504904602500c08143c0300c036440c5005482c95112038180c03030701c4004900440200320b1280c6030301801211243e142d40100c2d0080d01480b09041d81e113000c0d103880d003810140c004503115200f0080d0301029080c0002e1315005201c1e0104e00300d0f0040d865805500700c0c1c02c0e240c0040568400d0191070001c4108400030100304100b159900001d1010194016240c0311030b0354100240c1107030041e034081c40c40c0390011401d8000c181d5044c442c078440d10400c01c02001265040800080d074404040c0c00080400410001c402c2c184404100c1d204020000e0410000190039581045140300c200101006155800c180d8003040324a07060003a01e407908400c0c88a64031980e6180d410700c144400c050002e8a00d401030f25008100600d04602613400c8060441a46e440024007860003460300e16880100e100509101c2c050000241c0c00c0da240009480d0484404900c3e529101c44084c028450f10f800643c0c428030000385103281000001d140307440080c40c02020088500d0400040d2a03a1104680080007500714070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 270959559 1250 270958309 270958319
    0xf1805030303061003110a0905090c0a09030308040303110c031306110307020904060e1e0f07030206090409210c05070806010e0c03100305010c1e110d1110090804030c0605040b04 78
    0x4108130038000b10700e1a000c502140f51000030301c8154440c1c0c400c14001005010107105a0420312506030300803503400307d901d1515003c0080140b001445000c000c3c00c2010382d0022605052086c0c10051503083d400c807071640d0324844104460740d60750000b0b5140e0024034101100280d200d00502d0301c1410744550720091441e06803164200007160400610850745107030340380e00500034072000304161aa11000001100d00350350100441c2e900d094114515180141e0000c1d1085c001a142c107020754034121010382d00130481061a241040c001000c43d0155404415000300e404040c0341d02003001d070b65203400340b000e40c0e195030744030349101d034444100340501c02d190541000401e0750200440000e41d4040c08070b544510304e850b202e035900740c02c0d100807030b440f000090204c81001c0309034080c0202c400300d000c1e268240759003041024010261a905c40b0700852040c004144900440e01c0f0051200e6100800305a100308030801280c58544680d4000c2e0006549041c0c0b05000860f203d4024000c840503038410786140e908044c034107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 270960809 1250 270959559 270959569
    0x80304060e04020c072c0709060302250b19021206010e0a080109030507060506012d110a0c0e1609050402030a0b04050f0114010f080417040806070f180503030306 71
    0x10004140c20950820003901c0810382484110094a100d9108140e501e500c94100d40380300d04040031511101b4203450a00000c540c2101e10a021100c442c200540c448010306200c1d0417040e10040102100507080008000300441886054465501444c200c0c2e40247c608882000324000e10001506c204a40400f0410b1507001e141000c0c1000e5008028413030340ca450719400c6081d00d07042c500883c040781011400000b0810340380541c0e47d10450a00e00300841d000d10700d040360000d100d08032810382030390b440400015100c0d104003014074206a070701c0e0890b29070484900d48640d080206101c2d01c0c21111242d80412004200040c0615000001d9030b41c41c0310443c200801c1000a42c03000d00789081940c0e0340c0000704255280c2e400b909d44241e101d446546070b00d41c50203010303814040800c50020b04021000345054495a04108102d4101c1c0d00150300c02c40d40d500325450311020b0701c1982c00240340c82c4140702c200038086038020454445481c1c40d07552030341d2211740e402d44200140028060f455040e003040c0000740c0b1360700380 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 270962059 1250 270960809 270960827
    0xa050c12030717030403030609090809041508120c0d0e09040b090c15070b06370306110d0e070f1811160303140c0702010804050307020a090c1808030406 67
    0x100300030340345005010394841207040510140001c89507000710421041c55011307c1401c008040c802028003010115907079040c80351207001ea07028441d9030b80340b04080254014440c000054160301c01214540b810520031040c140e0000300e0103043c1d80c46010f500c005032920030350325038400e070f88040c00022098a46d84d80b20f09048070001c02220b02842441034000c039668858a48040364008846c080e5611309149c10850101d400040c15030307006140720b003903c05e006038004456840c400c3d03010180309010254910144611000daa01c0507068604005000302113220300d0000b0640b1451554007040303608491030310107460310402c1c401e41d02c0c00030303845600f00b1030390401c00003514040183d034000044131845907402d0526a041f070344820203088030a95060701090381601c1940c02ea400c00a580300d8946c904000d0f160f50703900c1480c5000f410005814082020044100165a4800d500600d21507840b920762150a000f452589a07590000b06c01e20141c3e80140380c900003000035903480b8030240d03242c542400f100b500c150310 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 270963309 1250 270962059 270962089
    0x14010807260303010605030c0705150601120501050307050f010324050307090b060a0e012001020d0c1e050c0a140a2a03022107090b01020f030a020706140702030a12110a050c 76
    0xb8204927100008030103102200784e0040c05804015203050102c0010301c1030710800040c0c0351443c90700006000b00c1d60005800b0013160401c8a500d014422040c0c0102c1c0a421078151040000c0050040003203c4c000c01809081a2013066044031a10b0350f5038404582510001c00980350030102c02c00000e00510321510008040c003c041c18040c0402c1030a240e03202846095121000e1203960204418905080c6400303401d442d0300140c500500d800f00244501858118150b1139a42070103030003c0d41c2030200c40c061200c2c0d80741d941c00c412101c0045d40c400714025151400d1100c01c03591007103401c1c11010f01203418001d04254403003c020301d10700541035500b4441d0f065505070407501c0b10126407c4d150448181042484081c0400c603038045061506c000000e441c01038a605a00244e40007441000f04441d400604270b021194186000c15540c811500902120300c81c4800103074060180c04d01c00424001d5244200040c107603240d45d405030401d501c2d49800e440c2c1000101c01040740c3c11020080380d0503d403401a03032403c1d030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 270964559 1250 270963309 270963331
    0x10302010f051c0f0621060f0603030509060309011d030a030510030b0a0b030f0a06060816061403070e0a060807020606040203101202120d020f12070309181401080726030301060503 79
    0x10381c80748802050b5511000001d022001021450310812425008010142380403000c1804800c2c1503641c0900079020302a0b82c9400742c00044001107015409401c07240c280c031580610303454074050340702d42c482d169031158030004042420318003c01c00080884512108581e0046c1d90194140c0701e981d154400345c1030203100e403945813083c50924070a403c030034007e2902c6144a000c0014520307191142003403c003481e1080700081024240c204014031900451810307182d44100ca68a40d0b680d03039805055514030003144820b600b0071003900d804121650000314044c0101c0c070980172100ca82ea580e40c10002640b0080399007144080040b1000c000c60313241e1454010350144002e186072200e208070000703980f4150a01a2650050b48800081c0301c0307540d018014076040c01704002074146803413000e0301c3c090480c0440d44105081030903d000303c44c00031006170740107020074128003482c16282e580d00c8151964500c111f000d54120380c00c40f12818281c00c0c0100031008094682000a50300316032030002c0980da01e4100034a84a031074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 270965809 1250 270964559 270964571
    0x203040522150b040305010f090335010b07140105101401090905131e03020a020108070e030604030e12030403120f1101020d021206030c0a140d0515010302010f051c0f 73
    0x64240c82c10700c0400b078002c00ca20b0a40301c030b1841c01e00700c0c00d644030036004940d010310707221610000c07a0b4082122818040128114000c0e288641968a4076007160300061000340ca22400105002284000034031540e4004c456082c0e11a0814030143c0c00c0700d001351361203003182d2108203040000940c45001c034400c980c0705040c8080c000380d485100d2415104100c41c442e2114020211900c00c00080c11500c125406510900c4111703104c941c3e6002e562a005140b0181c180100e01d800685c40d0362050840102d0488003500703861050500d454007908100c40c1c03108040c801c100380c8900d40c0b403e003000815142100d170405003ca10032110008251003c9288404071000c01401c42c03012a11884240018140c201554100503600c190030b0103039038031581001d404240b00381c100800d05030650f83c03040401c0c0c083d0751b0401150088050340d10001002e40e291900005c243c2d00a5038a4903034090f181c45100c3e0b048134000c1e2103010700c144200b00100c0301e5104810a04240760794804400311b02925035840344a514010311170000780 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 270967059 1250 270965809 270965831
    0x306010501120b060408010903110a08030a05060a08102a05030117010b190e0c03090607031d01060303170a111219020c1609110906030c040e04050a050d0203040522 72
    0x3c4d54020f4020800c039039100d00b400e400300359000c581040100103000c09442d4811595a4080c1c03644000380180d4074407600c030b601055041d40c40c48580c41c002c010b0403089400d50a441001d10001e44044003601046405011072103941d100680c0c1d0079440310807255145441c51382000140b502c00c10b0100b07112116036603a0b1402d050180c0301c0c42c1e80302c0d03101d15149004405141c90110b250749900c1d8000d041d0900003005000b13000100200166040d000f480b14100840e4404614400880312440400005403c0d07003003450000615420800d81019600d401183c4200b6030340b8039084400b0b5801c25101c6036a1182c0c10414242400802c106180c1c00400d11581e81c81400040181e03c070591304180e000714965041840e500340b4a0041e1038002c4018401c0b12003d0000c801c1c081285c4460b40188442c041c010f82d000000a100800800c1c100d4014050b14407444040d41020304200f40c0e0380b4082881241c0d2841000000903506000001b6501226401444455a805200c3c01110340b00101c56007554840e131900c0d40191 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 270968309 1250 270967059 270967069
    0x305100815090601080a022b150b040b030a020a1a040906090b0f03070819030c0b07020d110102091f02031e0307020106061e030b0a0f120605150306010501120b 70
    0x12400c0291103001e9640c00d0000b2510708022040c1e01403290355109456040c01600e80d0f0b90b00d807074804d042c0800c00f1003010620500c07040c08803100000038a82201141e01c4c03001c4c0c003441e51102c5842181500d0401400448500381659041340c42c1006c0c0d441483d070082040390720224800c440600c0740003c0240d050070798940d80c54050322400d1b008080400e44a018034007843c1003500c050300e40d402d0b00718014102985802113050701c5521081c918851507400700c0c0d2090505002da081818160390042c2ca01003286000781d8004c1d280d1811103803200c0062b140101100c0c0b0808140261445480e00801003104107445004140342d100401c0c4c03800f81940000c0c0032000c612084d6900c0842d820010180956580c41c0410b002801c5883e6a044401409aa1400d042511703640030281c44c4440c0036420f00144441034000000c1100016500068090050b01d0740400d0341031022403154000c5104807400d00c0b694a40445500300340000302c03a42d54155000000401c801c0d03100d041d800c0f02e0300092a500040d48081400469 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 270969559 1250 270968309 270968323
    0x6210b1b0a020105010501030b01050712140702120604170705030a0e01030b090f041104020c071505130603020d11041409190c0504030507170703120e04091103010605100f03051008 79
    0x30740541d645000401280d601402040c5c1030721424a00745180c4045980c41c405905440b119820030490070322000d61000143c1800c80f14001d4000b800e00d4034136108203500a54501040724100d03950360008410902103a4080300350b883c10356118004d9420140c5888041b0f4003105a40c00e0141053b4640b141da04c0140c440700c011074044e4a9200d00c502d090300e494201082807440c20b01d0058080c130f1041201c0301c071841c004950309060300d07809050079203000c0d040c0740212a240200d08102c0560000c00100048140e003503030051050300904002405030010982c41608503000d1442014581c001a42c2c0d007202c9450003510f000d030300c091400700b400c004004c0300c80028112601c2e01c5050001c240002400d200f48107040000d070005040c0d04030ad41d42141c041900860301da21140c44000c0036002c81e010709081203070040a04e00384074600504104507500c0c0c40d05150074400b02c0d04000d9400380d4a000c81c04220341c10012940071341b90300540c480d1480003400031001c03401410300404442d14206030f0300e03011400d503030240608 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 270970809 1250 270969559 270969577
    0x20a1b080306150a0c030e0d020a060206010e0108070b0904050a0608120a0e03060709150201110a270302010e060f0403211704050a0209250f0306210b1b 67
    0x46440e45011020b21038021003e0280c00030400040c0300c0740c804180d00030454000d00341d251400c00c1e560f40d4148085000b103031101038000d501400040e0003080d0a940052554104c445409035000141d17a11340150380c036450076019000300d0840c10051070501c0c1c10f203604a02d030081881c0d8000a131407640d5070103841c2881406250036401d010002922100e56030301c0100118440000c80240406041c0304c40e0141c2080b03030603c50742a45505002c81d1074a010b00039400280c0f00080400f807550784140900004242d660418807406883c4600a1200490b031404c2d103201c0300b030300e9060311074482601001c420007605801c07842d0304100e000b608004c04000a40c452a40c400c0341c0d0181c1d0390306005084c00d007502400d1092608145a5036055580400000c1240001c551010940554801c2c105880e0703c80c24100b42c0c03c4140803440c0c2a0401c0311040c0c40d403030340801d1038002d14119641c104035542c0c41308404410b00040c181410388001c84604c0c401d02144440700500d4102d015080361b00704040240d22001c965811010b25 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 270972059 1250 270970809 270970823
    0xc06060303031b0504050904030804050a080a03051905040c0911160b1e040807020d030e12060a110c100c110a060b04050a0912110106051201201c020a1b 67
    0x84810002d0468840d000d101000707050090a02e0304010102e547c500000f400901004001c00100b800d00c041841715120054204110780e43d9254405008bd001d0700055885100e944500c00c11400c9036030385481064000c5600c0300c0701c004041d1410a1541c0581420243c104d20042c0c01c12002100c01961004803801e5441908001c81130315001c6031404a010441d400d09043d0074581d02044002454541103400355a81103424400174816414111031705014045140d420051f580010034a070000021814803440c0090400d005281e5484002c400c0c03400b650641040d10b91200c240c07202100902e4024011800640c42c0c840c0a60350b020004c0b6203403940300319090318242ea8800485c986030504d8010039030711190103442800030641c6c40d41c034005040c046002e50800c0110204d10800007460a401c03c0e4001c2600415614618420300c060320f0007041000e10b03203016400d18508080b11405018151070511542e480200c601d03266241d260030282d030017404007000b007056003003003039a11020714504240820300480c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 270973309 1250 270972059 270972071
    0xc170c010b0405010501020102090112021e0a08090f010e12210f0703060503150a0905070506031609090506030d180801050c04030614040c09150b03180d180e070c0606030303 76
    0x2080c00b04448042c0c00050441e4010000010680d030400d00c0c0700d1803c4000d160041c2c1d20540c2c4010000090500c829031030074070800007020b103003070b41d0700c50f0406001c0e040c1c07e0280d4803003210841c2030070300301c581040740c80303d007900065280c0205800d50405806401e84c100c40d56088034070060701514101e401110f2001c0828185024050016803500c2041c0241006400805101240308003452a0b03140040605150a440c0c2a09904010090290500908014003000d4507414000307407440e0340d000340c503403400c0c00620000d2000810003014000e00c0d00561020b13015048a034001582140c4040c06c0311710159080150314000a4140d1003403060500c200c0c4403d114036191401d51600100352680d00071940c07280784560040c8030200b0704110303d22086030b07264840007804118402c114807200712213074490b071903406000c0301b00801140608507149810ae0b110051700c0303208101580c00e03030f0308845d2014030702c0c46410aa2000e104501000340f0640d000007803410034203400315841d607880303064815a800480000f500c0b68 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 270974559 1250 270973309 270973331
    0x70c0e07090b0a080105121603150e070b0301060e06130608010302040f0c080c0a021203010e040b1b09060a090e070314160c080306180c030f13030203030402010c170c01 74
    0x1c100c100140118514483c81c00100782001003158106004031072181400c0d10b07101228420800901d520990a040c121004c581e40f0700b0004d1044d00d442441d40031660030225420341c40c034404141c0320b06070b94070840498256400c001c4c2c2115940046030800781c11020400040401c0001c0400e0300300104040e640300341c4650704500c1448280c5019001a00c13081c0d003880e2000311a590840740032540071803814800354544004810072071070040d10480c000c11043c40000007090341500e052944d8030660003617111140f82d445110240c80c640c059804401034802c03041c00380140601e4941c00504020109242c080501038941840102101098501d4070100c0e81c0e0b004a51000503004114540c085044554808880019407001e00300803150140284107802c0000091913640d035610306e0300c0e4000800701528019281040c4048503560050b10120701c170180c0a0001540405405842882207500d640658216110f82c0c0c0159802440800201c03a94000c035405a0041503844000d0445c4500c40f000100783c00b00f1030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 270975809 1250 270974559 270974567
    0x60612040f15020403020306070f181e050609030a06020702030106180f0e06070c06110d0c111501030201050f03040510050a0c08090a02032802030d0c0501050a090213090305070c0e07 80
    0x10070b4099a10b80c0c0180401c202590b004074503580d111440341015018200d29100031240c10310882c2030300c07401d44078020f0003094240c00034110421152500c0310103101103031180100207060007a80a0554160710550b0264006032061700076180c124030140010a03060b0320355001404001400e0801307000c142e601c40c1205640310081c01244424010800508014100a00c5c0107000b03000d60100900704a0b215103035500f51413504c00490360070b00801c0004202c191441800242910350000b0410510701c00c0ca400e41c407078540c2d904d03210380c12a50b050310703080c0c508040890f021189810080c8164dc0601402c1d0200610030064020306106106410740000e91801d1010040c100890190886000f035011740d000c000147c50020b140303004035002a602d01301d4540358000f01034812104040081d00350086070102c040d101e820110b0300d03130500c1c4150001d00242d0b4400081e24100c91481002a60082d4051554605a10594450071449020b803911500d803441e551240b00340884198003180c0354844003030411011300d605c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 270977059 1250 270975809 270975833
    0x150e0a02040b090111030d060306050a18050705120c0a0b1207020d02030409090f0501050103060f060803040806133f0c030210050a020f1801081f152f0607170a05060612040f 76
    0x10000c910b18400d11552070310303540c03091280070b521b005486294200c10384810810065812c40da0090140014a850320340e8900580c00442005200818107404100140c6c004120f1440203d19030b8000c60500d4940400c940280c03a2840c01510004015001440814801c0c080c89020303502131200480c441c86803528260031214180e202c1400e64100f40024003076601c020851540005041801115126050a04200100340070b03c015020508181c0310f03803080300c0100940301c6208010f9400001c114401380054523518100d51000300103130040c8022301421107507544150340000a8010060510840140d0703004998004c560740141c070303882014609400c0d80c3c00400c0c542d104514000c031070090800320103580ca808085d030140322070708003001c0d9010b1a071912500b00103039044903031581000750181d0081d5402075009a40800c4d00d42d4022040050a0503020381c1241d01000e071401200c0801d0307070f18801c02c07100420300644041ea0020b010403001500e04009078500e4051400303070a8000845c1d5041c54400e060303200c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 270978309 1250 270977059 270977081
    0x9140a020618041104032a0b070f030e0d050102120c091c0203030904021206030706020c01140d15031a071403010308180301150e0a02040b090111030d060306050a 71
    0x4054515000141c84540590345245422030904401d0741480700024081c0c0740d840841c1c0340244000c5000000d0007140a01001c8406001d441c01e9001c10241da03a403030440c54180642c028080701008618000782580306d025141500034074010020b43c86080c00280d1040548409440c1a0740200f90a0b84903031100d0070503500455a4000a49807a2500d408142800110554103400050030a90702d42952428800c41c0d42c107110090045644040201210005041c2683d04034000c2c81920404208640005800d50b00000161a80310340705031061900e103440c0c1d2001031034200143c2c81c1e1861000c40075410a80c2c4028511440030400324401d000055070996800821101c104815440c606500d8500f007030803039042d01c0d0050110307039807014440300c00241c060004900f07941641c6001c030003202020701c01e0002c4c0144c0304803e01e00050b640750415007c1c01c0c0c0c041d5014000c040d200400c54510958020741d40c1032800c1e1098400e4034144110b0888100407110a6402030b540181c40380704015918040f07214503200301c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 270979559 1250 270978309 270978313
    0x30f0e121501080c10180b0307051801020105040803061c0f03170a11040b0a0203092107050103020903031603091203031509150e0c13030503040e07050406020d12020d020309010914 79
    0xa40a00c0050f503504c42c00032845041c080051b000b0140886620303400c501520302c40c45260782e2820148130003011a40030120480010203d0049901e0940c4107014150180b6000901c560550b141d0004100742455409601e021120b500b4011000181c04000401c45440c02500d0b803130a0300c107041054a00c0703500001c00000c2001d03d006442d070719030300c01c8a00342c40558825012454079003e80000992561059528980d4085a900500306064016010503407540070560262105c26940d800194160b0082c4580958190010304c160b003030078614400c540400e18024580001a01d40c1ca21040654505080c010740000e07072200c198072010304050360703484020050420100850441b60003103042c4201d41d40a404452103140c000304102580030340c290764403100c54491508000341e0300c0c03415980d01c0e4464032481d0019030ba180d00040307582d4000c10540c1c007150070b0303a00903101c2981c420034110703100007118040801282d0b003800800c80e40d180c0381c4003562151027040c000103148411410030540c1180380a161041513 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 270980809 1250 270979559 270979573
    0x606010801030f031202040521010f02122a0a0e1005030f04121101060b030a0f020717030912040618080d02100203060301061e060806040506010903030f0e12150108 72
    0x1050486000310b600c4d0540351404e012150400d4440107441642e000750703803020f882104d6046421103d90300540801740c0304000c009180c2c2d0005c004059006000c0040c60301c0841c1000100801820a15507042c50010807008814001b04404060b603600404180b50009846585440741820a0503004100c40450b042c0641107241030540101d00c80c000800041c5421b11106d031101b05503014240c5201a403051000034030600c0d40b6100c840d011030f082240c0c00710245080c1003869012251f148216034249800c842d0087c101d88006c560300209500103000c0031010310812801003184403429028101030300c20380e6110a01c03503408000e2501380080e160410070054000980950f60760b900050011080441fa42c1f014de00d035031741c2a0000740140301c103130310260705041c0d03c07003200440708103841000303064840946500e003850700c0704814002190001c4900c1d50102e4004c0e4800d06c0400e005a00c0303c2500c80301c0b0310b480f07844810f4403008196030426546c10b40c0c100e9400206100e90b00815040301502401001d8010992 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 270982059 1250 270980809 270980813
    0x20615100c06240e062e0c0503160303050c031b0315041103070f030507200705090405030a1107060e0105030a0930030207050a03050903030d051003351c1805060601080103 75
    0x42c462044a41009200171b15816005540101d40466501c0c2d00003080e69240c2509241d96550503400c4401100080d00e8040060190396107c01503e00420b03408003140c000305d100c1a60507107240d0024000f507a214046010b1a0070607070303030350280c07030f03282c46000d4001d81e00c80c01c000c80c2c0079022008041948050500300410442201d620480403c40b005094100c401c0b0000c011040506140079508400c1d00800480208001d0190002c01454a002d070745d0f5940c19038000c41c4c41065110702c0d242c0503000c0001c040c00580c501c1036201c4e134041c41e084848042d0028008509550b201d2840345540031081040d90514800300007500417001c0b0103007100b00b5041c154034002c42070707540700d440c0c40e680c440c028280039002c144d804a40e00e00b0025035002d03030324101c0104a14280110490356001503413000b19054861281d141000307042003211000442107444a4403544540c400303412550b40c000c00381200c0050f070101000d14618049000b8040040d40800b069402175015007041401e0080090803039060082c0b000c01000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 270983309 1250 270982059 270982099
    0x1404031127190b13021909120b150409050a0308100305030405060f070510090507091b0815100c0b0a090c0306090206120403050a020615100c06240e06 66
    0x2034004440d40300900a04000c0c210903006041c0c448085402000501111320072085940c000c200960521900c425006c041d40c4040740c05000074001c544e4883e5542c00f8200014000c0110185c02c00803140c030224a45041c4000b050890301030760401c4d6483d81c0269414418190000400c9411102040c00b404140c2c0c1141c48656492281e0b01c10980a40310008960ba8064607900968109075803080c10741d055032980059000c081c0c0001c03070040e02d550041140010301c00c2204c1c85100030070511022100034110b404001030f43c21030303130052100c00b00c02d07541c03c3c094145942d400e032072040400785a221008101e1a0b8200740c1c2807482c008100207200d500d00310400000c103448005000440340d0021021460054502c085030b813a00408500d10325030340b00740003400304042e000343c05040120000d82c00c44006036190300900040c203c0045042e81c00a683d0780240001e40c0c03064524041840c0181e02c08907810001481541520f0b00503050030ba5003038101b2500f4070181c1100d005060f044076040b5130080c42005c00b180106 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 270984559 1250 270983309 270983311
    0x4030f200712020f0402070f0501060b07020132040f080f070503030910090515091008060a1203090e0c090a09050c03130f0c03150f110304121404031127 67
    0x1482c280c4226110340300710b40c0c0302c8020b140c110750701500554a91001703150509003048288030485065003060070115644007554281e0380714a170142c2da51507403062000d1f5291020030706400c0300300c00039080c0c100500001c40501d0040000304071610041c40790034030340b46481e0f04128215954810315000002c2c01c1081b65400402d035084038004039a1170441030350002c8151900354050340219005500d21590102c52071811026022541c001c0da84401c51110b100c03011121030b002212415800071f5203690a02009024030600c4651074420f040c2000380c0e54a80c10104040a011a0041d10745c06000031103001c18280180030000404070440240014101840e108902d0300000b0371008501030fa041104003031140080c40e1090a0303410854800682e5200c0c06d00594030318003001458003403070420144d0414100a8451000500b00c410400340c00e68480b95910001c54039810181ca0810106034a211720019a02e00103000461140c442014110707154401d011950b10010740500c0114031401904000100f074500c0c3c1d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 270985809 1250 270984559 270984569
    0x807090b060c1510062607020a08030a1a0a03030806060f0906070302010b0f0d03020309100e0910080d080f070c06020f040303050d0b0d02032503080304030f2007 71
    0x200d15032404a0101d010750242824684451081c194180718000301043e07054014254900c0000d0748a44814041d00c0100e185000b40403603010200c0e440c10080c160000046d00103000740b05491550a03103844c0c1e2191170700181c038800c0e5102d0783c800c0c580c6520f14190007034030344101d020703103169031401c0c5180c0740501300040007003200380038400000e00c03800030012540c1101c9003010300500040d00c910590030b0080c002e00341c1082c0540101e00c008190b0b8000d240c100800880594158000d40c0342c000c03840184082e9003c42000701052107803010030210b0700d40d580c2e1111442404a984841d040da0b14103911a80f42c0007442031100140701e00301007032180c1039680400450303000603a8109800c00c04000d1401c1c800a00c5030240c2d84800a0020a002c0100b56026000b090800c0f007040050062840e0303102003000d0700781201402035241c1e1104079151894402c184650b4441d201918240b44101d941b40c40b198a594812141140000c104c2800740866903046902d0107003815480c038442c0614040c1044030b8bc0d540780c581c011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 270987059 1250 270985809 270985811
    0x902060703141c0f0b0f0f130f050708090c1c030c020a030b1503100b100c050c0a140103050a0c08182b1103030c0d0e010219050a020d09080709 63
    0x140a5112111002c07070b8a01000780c04114142900903007941c0081c5440c070851303501341c1d040c8054611585020340b09082405002001401d000e40d0310804c00c8011411451a0390322103486000b4200c00000303d218080c41540c042e26451078510304004100d0610500031101c2d4800c0d20f0b050208041400000c9104c3d070099890b040150071034450740000f8900c4200d03540001c01c1c207240c14081000c44840f2181d4840e699800b501192425255004030340d06075910303041c0041e000803001d0302d1240b003540b0540c4004407081c010016a645118200041103101070a81c100000300342c04940820308a50341761064a5011042301401c0114110008009000b210003a00d00c0d0b11200c6030807180ca014010074007240c1c040d41403068072644420105090b41c943d02000000c00404142507800c540c110319000720403280700b01820240c3d00e141082c02c44200005120382c5a81d412290340c2030000c856001c0402408a0a0010949540781c0304c05c42030744000d2a040c52001d900c403c000c142c2c8410444188001407410070b0f03981e5920 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 270988309 1250 270987059 270987077
    0x2100c0510050612061501020c0306090606190b0c010b1512010603020f04050405150102011104120f0c0e040b090111162612101208190e060f04180902060703 69
    0x40002d00e03a44c0c1c000c0701040340d070040905111001c50780c12001c02c01e840007a02520035050b0120101034540313200702c80701c03c400e8001c040022a035152042c0c4e5004811246400500390300d0f01e503000e00950303400c096120b1030030369911004103400b4035103110128000340030f00000e00c0c60154840e02c0c404841c0030620443d414180c02090042c1c1d080380240a0710064a80500100700d41d10b40313203c1d000409012030b03c1060141d46403100d10307100050604200c9041e070b14a12400d2400c5a040e0783c511440c605d100e03401391100c0200603008904050320302110750003203000d40076001581c02d01c10102400c450461220841401d820413084603d800356010480c507445c1c0104290301c02000003100b149252509410090220703000041060901d098580c0c228028002ca04208074669100c01d1100d49030030100c078003d000c014051140803064002e01c0c0355880c1444c3d05203810140520208003140380b9400c03441492440400c0450240b200400d40007200d80031101107d0240300380102500841d465200740707140501080201300c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 270989559 1250 270988309 270988321
    0xc051e011a0609010c0303021c060504050703020703022113060302090406060e1e030c040603120305100b070b180f0f06100f050607140d111506030304170a0f0305040302100c051005 79
    0x123419941710340c44c2c4072440d01440c4040e0a0280050440b07010706846985402c3c045000709219100b643c0e181ca47c076400500c16151079045004012040c2400080c802400300071241005281d8504040180500e807009600c6111075070801c03080d105590011010040c00800c10580390b9190030800c00c1e06c523040c0d0408024021128046802e0201d064629608681050000000c02074400050010038034982d07802c00031030329010341c0508501c1c4030748200341c0c903801c0600241002c103040c110410340110340740c131569882d500000051401c10341403a1104015800c41c00400c40c41c02d40500003a03a2028808151000c0d1500b4404840c0740140c140c000c081c014100402e0501c1048410302100702070354038103402c035000c0920302200280442c00c4078400d489140511490f82e04541c25074074980c4c0c000c400060256040c41c1c1408030320b90190400b12200c50032071040a04a01c040341c1001604c20304540299039042d0740740d041d0f00501803191030341c4601800704801c49441802040740030034032040d941c01d80c44000c203441e1101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 270990809 1250 270989559 270989561
    0x30606360f0207050601152a02061b01050103080310170601140613091b0c051f0b090a0606030c0503011818140c010206090102210402010c051e011a0609010c0303 71
    0x3805006004c1d10a0b20000319034802a0487c526155100d60740c0c1314220110a031244d1580b02c0d000900c440c00041c956440b50041c030700f640c00380100b80300030741003d0316116580c8001c1d030035900d0a0380203548503840081807186c1d4443d6416040090308070700e10b40c0714030303c0c4145d89010341c2c840e0144107141160b000c2c0380140d9010799640c0e04480d960f003641c601054520352241c404000401802d40300c61100f640f00382a1003c4d142c0036081c18402c450b004001703454401c0c400d230b440669a000c070280310a07100c0e607202c6044000e0341d91403401d036009000d040c000190303860070110007030201c42100c244881408024401000104401c0703020046529481c0360118040941c030604048408914a004000b603100e080c00c5d01903400006031304041820260f01702e440c02d48403410040d08034410710000ba010803200041c502104051101c07101d07040361061502c032100c90f007240c4401e030602103030305191102c1a105607002c1c03113500403d000780c078036841ca103500c522001c0c0003001c000707407080c854800407506100602030390000381800703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 270992059 1250 270990809 270990817
    0x30e060c0c0d06020f0c070602010b043b120909070c0203100c170901090c0b03010f05060903070b120f0f1612110f07030305011a072406030606360f02 66
    0x2081c4170140d201d0307030001c0b092a100c40050042c40010340c607103804c803000c0346840d0003541c801c01141030012600f0b1984032034240325549550003051800c070400040c425124801c100c07020703581d400001816100e00c0d00d00c040085000c00a03017148100f0101c0031305240940d4001c1512403e044003a10005940000d03c001550701110344050038200c1411f801c104000d0007810342007034107030380d00c00c101d0003442c11380360070304165140028019844081d007085424403c50502c1030040001c100300908541d0b900340e8944140381d0b41e502025104680c207a001c2e00340300046070b000b22a0354110520080e00b18248c500800b020b512501010852010045401400040c01c2c890f1380c08061200d1045280c50740d40c40b841904952194400542240080e05d400000100c0707075139800d00c0b0462840050f00b118a08074003a261901c801c4e82002642c0f10900c0640e5058494840602c0340d800114800c21003c00c4107460500c40c030b004240c04282801e21545821412900100303046104200075100f0750300050310643c58140303070000b405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 270993309 1250 270992059 270992077
    0x150f0f020c190302040e011e0c02070906030c1d0c070602031509041b05030712020f150304050607030b1e1e040207060e0d0c0b0f180d0c030e060c0c0d0602 68
    0x4144001c10608142d00d00c80e0070156802501c0c107100701c650790b0303036100d00b21a6090300402c0340c80000c42c900e0210400d0f540212500441a2040303031085901c5100c1d40048401503401101c801105402c1000301080d416400c00c4271201030440c070350440c13400c40740c030b03903900c2c4a46100206880c0c0c1c000000f54200000030b21350000120081c00580c1c8615107443c4c980c0c028403841d81104090006076800003580c0c50001140b000751002404200980145c0382c3c248420503003100303038141d0300421940c042c3e0302a00a2001a5110303901400041c0402e05189001408a0f0602072481d402040e480301100020080200f4103072000f4002c0e2160142d40c40200345002c03010035464015988240006895000e0000903040400700c9181d10003a600e028030038520070f81b181c1c1c02410000b085825120006280820799031205a40300001840a0003008001240e580c18030001c42d002c0404149651340d260180740d4025100d041a202c285c0702c243c030303150710305820356a0341d00c41c0c0311803910440784000101c00300000340d0196100c900b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 270994559 1250 270993309 270993319
    0xb070f0b13020f040903090b0c030909100306061a19030e0f03040302040501140d170403240b041107020d05030d020a0206040515011a0a0201061509050a150f0f020c 72
    0x10a11094490154507000e109078030403500c1e900515100d107058401c0080d91941500c403010480d1521056401580148440305000e000c1445444629201d0001503841090007003200041d060440c0361501c00c42e5071680000d24040c03d07541500c2e4004003040112040305040449030070305d900351240210b0180000c0c0c14084400d004151034880081d0001000d401a24805c603814401a80c8800740300244c80c0d0702d00c0c0c0840d80604002c80040200341d05880503c040c40d04c40e18420324154480e1240c03150302c0d40c003c1400e429100d403250070541606c180d101c0c4003c1d51070100d03014894511400d052102a00900b0b001a214070075180c2070307e007048000c204407407500c0d00000d4159100d07240004040c1d200c101c1101c4c151150300454011048240c048d90b0503a0507607004e0150603001a91102d0623680c0d640010041c41c040d5940c0780e00c08a0202c1e101202d4400c101c51990700d10b81e4640c20502405840c0003075a100000d4120304e0016811003a03080313410040c07616094500000d03081914241286089100b1982035000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 270995809 1250 270994559 270994561
    0x15050a09060515070201080f1b070c0305100b0120010f0e01051e09100504030c0203070306023001090203070903060f05010e180c1207080106260a0308010b070f0b 71
    0x3861194004004940d001ca5403961403c210ba001842e0340c0c401c11000030300281c00c5400060b03004440c849216000120f610ba10612680346180310a207a500407030090b90020180c0c0c2081041040411000042052001c018000d14206800191003c1c8520103843e00d40342501c00c50f40d058880961014069140646041c411034180c0f4a1440c001d00098a40903c5030301e040c0114980309540f01c092501448030040140180845850a4001450050b00031070812200d68507040250b6800c0102c0700107140580001030341c3e4142c104180e2003900d00c06c07401c1d9140502c036505851048807010744003030440d051a0805a520754808174210b80d4038034290001050360b450504804003030001a0300041c140c0b001c00404020729103803a08488840c1c04071815100c220b9211001400c0582007050071001c04251403011160f00c00c1e1102c42d80c03801d484803508400d84040110000d01c210341c0001c030140c035203903c042000e0b00802a490300c000b09440014080d410078914009103100c100040303031911071411034006e5050022 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 270997059 1250 270995809 270995819
    0xc0c0402190201051e0f100321030b0d0308180a0203030a030509070f05130c020c0d0609050d09031203051e01031101090509130b0405010603050111040806090601060c020415050a 78
    0x700382803500c5010015071902c80064200080c10096544211420741d495004d41d03219901440d0885006001600c003000d01a800030006c1c0c03d1400d003000c41c4114005007461030601d080020201c502515210340300300581c0141c1e03800f00340c2004c449a001807000b4160000c034000d078582c852406034141da00940610000480c9159154981d0055001782c08803c280c4151942d5106071074480c100600940d6844510200b450a03200110303400022840f08500603100403051000003d0403403e08030800355541521100820b003006401c6c404200e0040c028101100b079070781140c680d2854003103800000402e1656074004a1081d818080080154015464580c00b00750303160f180607013040d40e00e901a00e000c212403480c04540391600000c641d01c02d0340300c1007200e0a03030341c200d1315007492004015200b03403480e543c0e42c4ca0110104c2c07028043c404c0170a2413403084030b40d180d00e06010103107000401400500150869001408640d902078a0202900c2d0101e401241b5039140c00b042c1341a8511603440181d1103020a036000403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 270998309 1250 270997059 270997087
    0x1002060c0f07050a050307031101060b0f0909070e0405010801021809100512070b0f12060f100509010c140d0807080105010e0f06130e0a060806010305191a0a02030f1305070b0c0c0402 80
    0x9c2c454250001d002d015514800c003c51802592403161610105002c1c64801c0e040074100e07942e0048180c580a15808045004501110401c0e040130700541d40004a01450705484d80041c0d95070303001900c5038461450040b2244810241034003c043c8102c40d041e03662641074504119840190842401403545c411060300d9030241d55004c1c100b980b05608480c0006100781c5001d051507400c62102800c016031445200004070f50381e90024000c1d5040c00450580400070510320192018040c10120040098000145010385500d40003040b110400c0550b00040c0000c3e640b03e42031310000082910700b41004044040003964030300400c12a0000b401020f10005480305040b051140078081d02282040a152110101074481c0f6007400060001c0e4008891040090303d051915042c090155004100c0d90035056800005083d041d60101800c40c0c011007405a94010f280d2410740000d0260b645074405201d03956810b40b61f80052103441e0040401280007140800107000c82d00d80850014411035491020b82d652030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 270999559 1250 270998309 270998327
    0x2120a0f090e04050715090911070614040c0501032309011b090e0628330e040504020406050d08030a0c0e0603010b0a0c0f0305091002060c0f07050a05030703 69
    0x200000d000d01d40001c0c0c03140e040810340b800307180c021001d00354050a01e1550503d869291210004006c1d013104c0c00540030340c4512660811a070400801035440d4400d00f404020350344102440c040000001c400d000005e0b00000040742180c0c2d0a0070041200c0b02d00c0f1084800704058120401f14403403d41040116014040d4001a200f054030924250a50030840c4110b9120010740034540106424501161892038203c0c5401e0300a440d84420380b1150341902c140c2540300b0001d600010498022034034201001120038000000460b1412240700c0a0b0040c420091140881c841428020350f80c60300450199101c0d074001e0000b500002d010004852010319040441d0b90040301c44143d814948600c42850521070320503416140350050680d8110f03400d00041081daa0b02c0051100300380f0140311100c50005005d5620000101c0c081d4564907200c20060041c000ca80c0d0f01c0408101c01c54012074100901e0707034220400d4401a1030b003200450b807a800140b403c40d15000c000c4d00090490305c00400c080e810554812501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 271000809 1250 270999559 270999587
    0x9071703120a021e1303111c0503180f09040f1406090c04051510050a050c06070504050118030201052208010204090c0207080d02070312021c0e010e06120f0702120a 72
    0x136454543c00080c6220280601006548020280441040840c07490f10400c0c020103802050110a200741c3c00c206402c0780c1413105d0031a201e03000450241210750700c05403010001c070700c03da40740320001c4803940006514040040008285000340f072050010322100c107170b0032841c020400040f20b241d42080c0010035602c000b5564001e02c600d06000c005444a02d90120000300c1d02806480c0070304402030043e00381c07140d070800341c100420041c09001c0e0000035981042040e0181035240c4501ea070311070610380010480400780700121101500b400c41000144da01104895040c440548014003440e000015015090503641c46010a5130010074080391210240c0c2c03107440c44000c80d030211031f040da83d0b42d5801c41e100c00642411201580101e202080440ea402e90003024810031031040d1080902e026120340a00b0382ea141d040400078581844004c9156040355020440c2c2c0c01c00c9803050708014551341d000c401840d000b4415044500381001103941c0600821050211200c2c0d4140302c0c0d03c0341c0201c0401070294a50184c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 271002059 1250 271000809 271000837
    0xc0c0a030e1302090a0501050703140d05190509150a0204081606030612080306010c030323060a062a020f03070306051b04141207170604051509071703120a02 69
    0x5101c030b00a2600c03c5607a0f900b0007034041c9284915200040d11586c204600c141c2c14003511600710041ea082c3c1c10020250340740585070009041c10034004c00012a508148142042c51902d4240100d0810005d80600c2218400c040d111103036450000c0803001c2d0140e603000c9006031045a00c9519100301302c241c90b03010f80b1103907a0108840360362002c4c10104c020390204003501d0040100040342aa501c40e00c050740c1024003070b00780481c4c0803c281c070040d0f0401140202c2310130240f070300307030244012454a40c1c003403c024111460309a900e1407600d0701640ca600d00c114002035a10b24041c800f5002c54a810b81d1501403118024241e40081c0d640f410060042c09085409841c01c2d002c0c403000f040c43ea06d28405840c103440c04503181300807000043c02444000845a141d0038a180b040100004902a194005002803610303d00070340b02608151405a20340041c102030300008000d130108004d1403042c00108030080301ca0722441c10341c4601c000340c0032900711b10841a501c3c1d8000411000c0000ac1d030030a4004104021044070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 271003309 1250 271002059 271002079
    0x1c1d010c09051e010804060b0a0308040312030c02070f0b0714071205120406080a18060608010c030506040b060702060d0f2c010c05030a020f04080d090e010b04030201170c0c0a030e 79
    0xd8509a208041a43d180428241c1010801140081e84a81487e01000d03009401040e0ac0e51501c007002e40155104480d4442c030300a03004229070303050103400036001450008007070322400c0c00f90546e564845c43c01000c4911002080c95014400b131001f03020301906000701564640d686031044030401d007070350300c200b0340b814410b24001d08494440d10003100e084a0050361040c1312612008440307030292007a0001e80300b06003403030206080400c1c01841400c0061443da000003840c20b07074080015041d14002050705100b17520f0b21140309030301d1320380804684000da81122040d5588041c901882c000786580c1c140c0369516450651584011800c40e4200d211010b608501d1407801441410018281d40c0c090152a001400c1030010407445a5660040c000c0540a1040981450740b542215485c000e441c084540004199420403c510403462000c3c2e80981f0b00d0070b030303150310b443d045800107007140042c201282c2d00103920700009910ba40d14481503480d00403062060301c61541282c1402840c0c031050f0b8003510712422081c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 271004559 1250 271003309 271003339
    0xd0606021c0801091e050702031c1b1404171516120e0a0f1506211115070c03150603020307090b06160804030b0c1c1d010c0905 56
    0x44007031400d908203035546000503804c1c08074010203008007660907400000d1000401c90380388014018140700380c0d020760013940c032114262807031003003008540c0150008501c0c05403e5100000c20349242d040c2500203060121110075440e02c0400f1a00c929030040c440b0380d03e05001308800100c0800d28002210803494010150384901e80403031880180d00c54040081203085480030a50442a0401e640f401400c405580c25495551038030701c00d0628103031040700e4012407003510f01c540e00c0d514810003000d0268501e003a1540807048500b50b000c1c00045c4005414038804400030006a5501c603000b00042c114498826142c043d5071905a42c8141180021100512300302480007401046204800407240c000740104541854441410001d2040c0f02c1019088101001140e0841000071030700300800b4031075904956640d1031418030000000010b0900084501d040040740c458016043c00700c0a2910100300008410b0340c3c003c000c040000e500b108071040c40d401c0c411417101c2980c00807801011a00e094130205032801400d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 271005809 1250 271004559 271004593
    0x30507121704020f0301022a15070f050711180601080604151806050d0507031205030105010e10110d1101051b07030f020102040915151409010c0f080d060602 69
    0x201d0104001c1601100002c0151a00c0601c40322032100240006103080c010750380211074140e00d5698020182d41c0c0c8044000d60000030402054207403c44600c503d05824191b00080c002400410510108080810001e0521101083c003488800009080110005908815810384402203805501062031080000c601c0d09280c0a95204038803900f100000050a00c44002c1101c01e05040d1910b42565418012540762180700825280c0d600420040c0b2503940b9501d06048040c0056180c4810420140010082d507608a1b6035120f25041c00c8860380318010709000100c401503207000590b02d141c07043c1103840c480140c0105a4100108041009004607550f00340e2107100785d01c51142c460032124041000c0004039100d6a04040c1d1507100340b0002d4a8143d0b21141c01081d6040380100d40c42c0101100c3c42000722115a4022007220719050030400e1240a003800e104816000e21b105903410301603a1070b1480c0400604d04d0f1301c1d014050b405489251030f1130310014214000c110700d002e800d01511131000c0300c032410226 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 271007059 1250 271005809 271005827
    0x14090703031407050a0215030117010b060307030b030102070507090e0f011404020103091a04121116060302090d0c03050c0a05060c060a1806050a0c0914090c070309080a03050712 78
    0x5925002c800e0702c903000b500e00490f8881141601d0600a041403074006a0701c038440010400f08440d002500e9504020f01c1103000e803003406420780c1d141c1c9002400341458039104c0942c1c0c1d10440c0c03420005620150703140460f019105002c00108180208c0c80e001c01e5000d5140d2020844201d114101d5400d9038088581c1402c0310480c168150400041d0000980103610907001105850311819068051a419502007000c0301d10548085a1001e83d288140e1907031b07688109641c0c0369445c1d80c40184141c91016011418aaa40b4040c660401d074000944141a403180c20701c21340c9107035109584400c0250740381416034070b034040120214800d012a020004003860300340103a5240620030000f810058680180c0d87e0010000c030441807410500c100c50200204070a4801e1920a0000c0440482d001035100002400c2c40d01d55002901051062307004083c403605d032103103100e40c854001045685d443c0503904040e1440500c550201103103106190b088000c06500030050401148100480b58803104514000c2d00c0c4110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 271008309 1250 271007059 271007063
    0x114070306091a0f060f0313030807080c070209040c0b070819080f010b0304032d030507080c0d05151f080109050c07030c02040b040c0c020f0303030405030f0a180914090703 76
    0x1000301c039800140d213031015903003c00310340080030341e441d01c00203646c0c10b582c5400880c0c001d410f1007a03950746103003895006900a6404815440c00d10000d20341000e5080407030286c084040d0288401e8800142000204044200584a0041c00540381c0005203440e100341d520141c2e20000305000e0822596803140070360070700ca005500d181c683d40c1d9641c1c2000c041c11000d0b003008005134200001021000301f4401e4110341d0a080b101007281280800c207a2040140070ba0304080e010404002940c0f00704801e0510324000d440c40d02d80f4515000c103481e190400c0b0f50b886014001003c2c1e0703004030120741240e810003044480e0841500d143d10341400b540e91760090303401141d0003110100c113612020400580028890180f410b140c3d03200800003d0440c8210010908446114543c2004070360074134079000c1075190072054041b01110441c0114a10b02d070940e0342607220b00806106554030352000c44c6048000b806035505c641c02207044559030b2000c1e079448140601401698520a283c20b10410224481c41c00204088090360b07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 271009559 1250 271008309 271008341
    0x3060d0b010f1d1618120303090b0f0c03131a01090510091802121005010e1e040c151709030a0318051c05130b0301062604020907090305011407030609 66
    0x1500c6007400317540c1d01d00d5052280c0300c44000490080380103491030300710f07100301402650006404051807504141030100034084141642c40d282c00c020123005054104d9030304c0410261002900c458615103840200405105010110106400031071380d02071a51000e0f1040081501c81c501880d910118101100c180044000c100114100d4900150a2241400d0633480c503400445212000d4a100c0034111034080e00903003119410201400700e038040d00c0e4240421514481c0b60711009044c660390f00581d081091241c2c603007410a0b01d2500038940c3c0a00c82016064466244225103807400b904550b0712036014030041e02c0400d103068a13010b903071041c20900d1405658001d00410700e910110982c2a03803414429140020000108850580c0294810010000340000c20000c0d44070750400c0806091090880c4003103482c55441c8030341c007032881803c003000d58020f901a565034444d6150706004039a00300c41904054080c0d0f080401400c1101c04082c00140b00325401d540070021581c40b00e4000c010b48481c0180c1d002c0308 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 271010809 1250 271009559 271009591
    0x4030b06190612050c04050301230108030901080f07051b06010e15220b03032706071a060612040308041a10051201021303050703030e0301020f0f03060d0b010f1d 71
    0x7030f402c542c40345401c0f0f040041c0050400c6ea6681c0041e00351019020341000725616010700d124004003500d00d20b4090301708200a141082130b0080000c00b00c101c000c0101c0801029903010403580c602400c215031001c941c030301d2146980052040c0d044d582312828421420420304401c0000e612030a0002c0e58544090000c106000c0320841426900882c00c0044240034929a984441c401e150b5003040240120380d104102d4903031020154080908010082480f180605000c114080000da5540c00608200241c0d40c114205500c1e03400100300c035401902c41c0d09500180d21024001495040000144154030444003405103864105568501c03540c20345540714941c00111060099162000c0e090410304800c1c03000504110843c110011400d815038015191500f0628041c02410f42c00a102440d189040d0000c0d03103407502140c0c401400c1c0c030070740706c1400b0811401b10210361160380703844500300c5031034001134000b0465031140301c2d0500c48116031041181c011540c16510900240085a00b40700c1e025041d41e5440c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 271012059 1250 271010809 271010837
    0x1031a09040203070b19030b03190f1a0a05090c040b0604060f0e04050403050a090b0f0f0a1101050c0414031603080304030c080408061008030702130b040e0304030b061906 75
    0x10848041c01c201d9142c081d1050101c1c45102d110041e000c0310030144101000103400b00c0001d01120b040300d000502a4004081c1e1705202060080c0c183e102552100d001519aa100d05000801805541c81510341c000060144400f005003604a54050040d86098401294244040104440c3c07a000140c0d00418244010002140a111410008080ca090805541088800003411200c04440482c007050000c941840169440520603029000110700d240c0f8200118500781c0c600e0003080b40400c0718079030020760030300c0c0f2511800191440903424030007882181011424150b154005000b03840b15000340b074103420303014900000c0c810380d86a91409400e0440f8119122000207034401070040e028849040008400610082d005100400c1c95001404460030618462544684550b1000b00258000e2040c440542c0e14501030101c0d89014600004501d917611010a0280c004800c0e000210702022400205010300d08150511410342161004400f031000501c41c50b83c2d440ea400f81c14001000001c0c8851 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 271013309 1250 271012059 271012069
    0x13090e1b0603060102101d0f061b0306010905040e011b05040521010209130c08130b190b1216090c1b020d23011d10180501020f030108060601031a 64
    0xf07040354040c810b65800100001180081e111203013080300c0454011264003207222400c0c00700c1c1a41c2d10602016010a081c0b00303402412070b2108240c0203004580c0040411550303030003008980e000f003030b001e00244600c50b4640d00340c50003030018529100d076030500b00c3c203598171041c4103004903415a00c0c018685041343c200c002d84280d020f03d81008048141d9403c025010301607461680d100c1e080f40d506807021501c0d800c08a40184841009030114a074080e82c00715140000308000c40030355107d0840400360070400070030301d800f501030103120001796048001c031401031303901000c00326a0016000030005a04c40f2960b0354107029045841c0445440c0004140e00008070407188907404070200c49000a0440140061548035410459421000900c800400c1c844801c60b255080c010026030f000426081c0404264050002d5200e0b5030724002d11107110303900c0b4044901928040285c803402a0040021500d40329480b094494a038020300950780c0f1885810001001503100740202c101a0007003604000307455140b007091003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 271014559 1250 271013309 271013311
    0x60f1e0b03130611040e0c0c0708031c0e0717161d0f0408120a090303051e0105010c050321010303091e0b0c1f0b040f14040813090213090e1b0603 64
    0x100c0c84c8a400c0000141b0384201c10221070080348190171a80d036940360903000504c0c0403a075600405d06d03600140480c1d4509018901135030b844c4002101d010400e50001501030f810492142c000010f200805030040405140029140040700d186041c1e0342d84460b107403041c01751549281c0081e550943c4003c00000e600701d04a0400c242c06c5480f0f000d03442d080000710415071003404000c846407104107664800300010b059043c06107039009900f440b07003041c0200b50041328044203041406640d062040d0f210318802084402c0040340d4a1140a0300e0075001081222040000d06c9000c0c8000e80c002000f0b0400482d9502d05c2a103c5550408000b004030071051800b001a0002d0700050b1aa809a00407024481c00750302c90302003000741d49014540d0011f112014a000c21003298400c0300405019840e081d1aa0b903410201ca070715a80060300403106a03100c0c82903e030120b01340e1016400c944005800440d064024000d800080303010740c0c1c0700d0442407107004000c5104564030300c0107160b0701020740692030401403942002d02c015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 271015809 1250 271014559 271014581
    0x402030d050f0f1c060e0402090703050705090405090c01090b0a0f0c17130e1501080a0902060702030f0307061d06070c060204050303071a0703111804060f1e0b031306 73
    0x4034148640c41c815076515410111a03001c0484c1201e48220a4480611549000e8207030690380035464140760300419007002000300200d060540d030f200450b002e140608280c2c0d0310007034010300c14002494200308050711060303125400e40c0892100c2c200405c0c0c0c5120901a03d01d11596a40c480740601c00e07070501203030302d403414210a0350301d1841c078a00c6010802c00e00005201d0806c00c1450f01c002070340ba101611700701502c01043d0703410300012054070100b01da030300c0a0b805820051845020500f20200e0001442610130380400070740c14401d001e4041c41c2141c000c070207002d80b10300418003040980305484000a81c0c01144405004680126000035480b034080c20b505600329001e8240142407540b80c0002c2f03455603210310b80c01d99001c2c403604c650ba00d12800c001f42c40d90f40304215107001c7c00342061601002405002d455161144034201c842d1030900c584481e488540100300440100440c41c1d07580714480f444030f0b901e1300840c81e82c02c08000c0101d8504211400c4a011380104100b11030340341003980351040142192484 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 271017059 1250 271015809 271015837
    0xc060506060405040903020c010f05130902031807030c08060708010f0e09010f0c030605032503020616050d0e280501050a091517010806040b040b04140a030302090f090402030d05 78
    0x400f08558949105014542e48a42c0040920300b0303000002600741110000840204030040054044400540b0200d60448080240143c1c40c2d8071154041824685001d00d4004244500c0600006010100004008031800300e01070b501651980d100880d007a88090158908060700341391704003c030745080025654003400d00c100000d0600000003050060b01d190050380c0c40021f840301c030140308038502841020075040c000030721420482e0b44420300400301c13961444064401c40b00800c200c0404c0500c2c0e103070a4001a070140c2601e0982c0d46400015244d2411031300c500b8081e8107034a454070b01c488064100020a014114415031031149000700442d81d1b544002d06400c204143e8a00c00242c400c050181180511540c0d11000c3c40350a0341c21540c081241d0503446107055074000010b100100342a0080d142e00281c03c286030030b40d00c0d0707142e0901c4203482e64140c03000825403007020031100c05d069060780900070011080f95054989525107081018205042da0081d42c1504201c50b44000c55008034003d258414560034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 271018309 1250 271017059 271017067
    0xc16050102220602151e0402060d02070305030103060b040902010909050c040e0112032a0f030e091f0522051b070f050115030818010905040e0307110f010c06050606 72
    0x200070501c1c00b20500007400460a105104154051251046285207003d40f006180ba02d40c005020104404090141c20390301c107008141591100c1c401c07640360404403a815941d40801c1e10b00280194024401501c400713107400b081d003110f4509406840700c25501607486221941c02c1485c10001028090b20240304080100000140710911580040c001d0aa00141441079151410003925201c000b40c3e00b410000b546082c003900d100405900715481030f070401c90040b01d617102c03441c0541c0d06040714420b41c1d0b44034046004000011244940f0850f003160010030345d1850070f80c0e80003848107010341c1c1c100f0281210b003e00003282c1c4442c13199001d181e1084c040061a400a40c5003001c0740c1070741d40070f5042a240c0b03950b4100c41c1c2051100074021500351280c2c0d01c0324101d07883d00d15142e142072800b5964070a0f0b0040e281116440c0182e00c1a891394018000084c010818500740d03411080e41c9911011007122020308504e0240400e00c0d080350128040c10701038560300d80c0320b00705654117402864000c04582d44020300f44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 271019559 1250 271018309 271018327
    0x503070e0103050c030c0307060c061d030304021503070c0818091e1005010801180b09090a110406210302190b0702010b0901050a0b09040b0607050a03170c16050102 72
    0x45120020500d65103114229411810850f05168540841034000c2d808860088625200003540404560b80380c54560f0030300f901841c01001919070f003400c0303442c2d94850f94800c8001c140003200a5001e217208036102c0f0352410000b52100041c0c00100d98450109510b01b1854001c181d4410040170b070813202c040314448071484100080d01c0003205588001e283d1500589050b49040c0500707030f040d01700303034203507260000c0c0c3c0d1810000038441c00d01406604c14044204051a0304490303603800001c030b42e4000421004243c688500358940ea503503040350540e0320400e0700d03906e400c403403c0c948110401d403003003241c0750500c1e01e40d42e0a075600204c1066070110110700c260840303c002c80400d0000400120300c90010310041d41401d07480203003901c202c400510b104407a603100410042d9036141e001d00c02c64280c40d4030543c030b695510340001d0003000008049038125034001081c03000c1140c0403801074142842a1107220703004542108041d84030504032030090103c0f0040100362088403036042c002c0442ca204d03a001600d407040d52 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 271020809 1250 271019559 271019563
    0xe0d06060312140f0702010e03030d060612060f0f03060b0111060a0203010e162120310e1512010e39030c03070e090705150d0b0a0503 59
    0x1980140d40c48000102c1100d40c65a010310440c46545076210301905198103000e03084242d10941a00030305000180d2030800150301c2c20b100752101041e03408000c001041d914003010740451030302c9000707040c4c00c0d190140220b40500104031140c00e48480856441141d801e59460400801c49418028103009070348010703a121403070401c641031068400380300c003603140e500d00300d20030030b601c0e42c090b242d400bca10400150030700b0964403584402030342d620540c0800d2002ea094602500520700b20044040d400c1c62500011110703080030b401446017007000382d080c1000b00756080202081c0d070201c60f0b2000017160120310030401d8079149115030b908081c01c4e039038650890301d04000040301110141d0440007280d445000b01e035025481072221405410700d5041c5503141d1400d5401d950300100e001809048601d50701c014044c410f4604114001911b08094100e50440f901c500c2c1600902000721164000c0d4442d040d004105800d110180000c1e0754005811113060602001410001d8001701c00380d20382140c81000c1c0050180c0e41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 271022059 1250 271020809 271020821
    0xe010c020c0333091e01020403060c14220506040303020f06180601060815060414010806040c0507061512050a05010e160b0313020316140409080f0a0509030307061d0a0b01060e0d06 79
    0x300c5c1e00040c3d50303d1561400f00e056400c034844d40014451034082c05001071900104031f4400c4110601c200d0000303000080c0c0701c20444a02d400040d0080004280801010f400081c410710140c000710072210190303103610303100344c1080040d4130320010b0f500000e0040200714001c2e29050b070003460403920310f194881c00300c010403510341007588000100e0300103c0b02d604c62540c20820b216000131042d2000d01031510143c0340a0300c940315202006001c5a983c9400d880600480e40c0e181020300f0580702d108000310442c1c204207aa503100c0320010303a019481c0808198a91600150700b03500810100446641a450100e00000380d41000b0b14200c151b000341000d100043c0c2c1c051101c0880700c000164501000343c20002200d121030503000c2c140d4001c901d8460000c010441c1c01003035881d000360340542d070743d611007004c18120f40d1400b52441d0355802d0700c0040781041c1004055040ba048100b0300c50401c00340100c60307852043d954a000c84020b040341817a0801400158801d13640001440707009040d1048000d03440ea0780c0001c540ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 271023309 1250 271022059 271022113
    0x604030c020111010b0105090f0d021c05070608011809030c05070f09060906051311040e0a0b010807030c0e011805060d02030f13240e010c020c033309 66
    0x8205140d2104668000c14800b214030150002000142c0114001070b111340304000702c2c03d21031018142c100340d56550b025807046a1607805004494000c50841c2d6040c00e44048000c121114054508041113141c85021312504070350315a4620340d0b00f041704420f6900246050072041c0d0410005c0c800001c0403601c1081620300429408411031400381c640b0701caa0085407100e402c2080c0b150700380903003001950b840d0301042c0c46110500300c00040702076a02c0c41e4814075104660182c010181e00004014401041e42c1c446183c080c030031b88400741d02d0317559801e045045440445038407010410100980c44c180d44185403401c07580c0304130b030360344189603444d07400007440c64012620b07940c1c01640000c100704135614001c1d82560171200200c00079491048980c0c1d9034811018800c1e168903159803c0e0f130700508984494000401c4003107600001c000d00ba0112000070744860b0342c1400d0500034419980300340541c0304070010a0065070f4030325001440d440b8540d040c202d194040a48122018410056403103a0b03809000702200c1421 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 271024559 1250 271023309 271023317
    0x3360c05100804290f090715030c0201050a050408030a0e01111b0706020c0603150d0606060201140601180e0a0209091f0608010b0409090c08030f09040509033603060403 74
    0x3c5010314001c40c54902c00b41140140084540c104140781340341c2c1ca9143e420041020010400390b4510076000d00d4402c0a40c0410380900d0400c00c41c00215806520101c21070700d03d50b0081c413480d0b0340d80c2001d0f01a11410384000304036210401c0062031a804036070001050010f40400415511048490301249401004000d030f010100501d580305000c03020410b03074004000e40d00250200c02e45a81c0001c025000c0204060440b002d40085440f403965440070024070540c1c010000c02c1a81e480b240002d00a10303c01d039010b24141c050030081000ba40c080c60040140705c460f00c07100000755040200e90401c448016202061054080c80a0241552038085040c41601509400c10340d03415188071808810f140b0b0b82c0b000d010300610070010b11558904c10100c0342543c0d0039000100f0902d00602e4410f041c0182030b8001d2509000104030701c14048500c500070001e07140111340c10b008a46580080325243d01c210050600032240d0114401848200108820742c00411b000e0000d510182d800c000c603041280071030f0210300007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 271025809 1250 271024559 271024561
    0x91203020912070503060601050c0111190809061b0c070b0c06100905100611100c0305060a0504021809061504031211030a0e061c0608030a03360c051008 67
    0x150800742641c50303160240782c1c01480d0451400d00841e486a20203801ca9040120005044002c00d0003500002a0800882034556640300a85589250b0500e0200030304005186400420409040012028003a4840814207a00f043c12180c400c1e001d6404941c01d000c1c0ca0003043d10008000c0c03e070902502800c03142001400d81c514043c0b2070800c00c2d01454010380e1080d40307407170148400101c4d140c2d890025a61241072143c5820360b208482c904c0d1600300720aa0030308904140900490990540125000f21400e0b6030044d080c1c1d450710100300c140e0044141025041024003001082480d003070044079040301c1c2c05014403003001130724101c16103654060341041c1c4400c0211907840004e29489412072144240c2440074604150040b80d0082c0206040003002c2d02c40c00c0081200b1040d0342d0f14000d89520100804804c0100950b10305029450790852500710b004245052040c0340704000c000124940400742e010406030b00407100403805178141e4a40c1b0181c40703840014101150030b4540c01c209140015075070305c075481c071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 271027059 1250 271025809 271025827
    0xc11060a0e0d0f082202040203090d020f0c0102060a0507110f1c0503040b07030504031b14060901060b0a031e0e03090a090c0203071118010b0714031303021309120302 73
    0x150584004500c802c1010f40e6010222013a80700c0c048a4200310028001c0d00c2d600b42d10b81d06110282d12040b4003070b501520004c00d010740c81600040220074039030582c09444002c0302c0099000e0711514281c03400c60168100c00c0000e84042520780c05681d00480604158070010f904000c154680103040e0092003442d480070389204801c08000e01c00c1001d00c0d1b1f007458528078500d840e90303495906542c0601000c0606480c1c1d80071808141c00348080071040030b801580c00c4103061b00f9017807110000d0003a4000644901a120204e000c02c1c03418050041650a0306030310364030b42410f0702812402803030b02c44d00200c1a54044020f0700001440d9005154130b503000342000307607114981c40b410400402c0d02d40e4000803d2510384283c41c0c401e2034004c0156001c043d048080040c401c003070100130502c11603414000c00c0d25500b00c0d000109100450304080c1c0000c038050207030320207009100010180d0f00d2103441c90300320381000a583c042005181c1a8440c4111380c807070300e402007014445036440104814504a0800101317030013040b0704607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 271028309 1250 271027059 271027063
    0x40905010906060f030203040521090a0503150615040306090b01210c060c020f09070302070512072001050c15061905090705090616030c0c0501180501030c11060a0e 72
    0x2000d441c46910401403185850005802c40010500490a060700030001505005051044c140c4041442c00203260300240c03400703030080d1948032400980c41001403c2c8049828280010300740305010542070594020340303c0364208280300000704d56140b40140300300030200000d40d250103400c0020380f1448102c08607504048a10001c5004404803040d40200d82e80320358042021150003004980007810601d25200060000c41e08441d030742c10203070b42c00c045241c050084556040e070043c9821406042030706c144803525200441e49124072075014240724080005104204819800900340ac4014107150f4036105032240307038600300b0940540301c030b42c6002010104038042c104100302d0205403404814440c5a1750801e000508000e102800e140108500400d20b01c0aa445043c1160460349516001c01c1c098009031800a2407045c400f2000c4070484146030000032154000c03142000b1000307140d90203050603410600114000c041c4003054004001c0112000640400103002582c014480c0020218100d05001b44441c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 271029559 1250 271028309 271028311
    0x5040f0e0405100e01020d090809010311190e0d12020a1511121003020a030b0103060f0506181f030309150806060a113a1112030a0e030708040905 64
    0x4200c40a2440401c80018404208403001c0032160340009800c0fa508a18140240140300390841694a001002000d02440030042c3c40241008da03170034800d0000d001a05080c5000b82900c0c808001900341c801e804450260f14500282e00c4050810000407a46444070691400480301820161700319034540f80c2800707100c0b16a15040015a08203022015140c402a100c40c0708407003981d070766482d20780c0200d01b210100000031030040d500104005181616402d0a5490603000c1c07104417961483d100c1c058a440b211750158a11076030004103504803080f00c0c80c08418210744d000b000d10003441c0b29052401580d0380309480c101d014501a9403009102814141000c0e5003980d401030a00901c41041d040200321b60300c91048462500041c40c215041004142005152140e03072441c80100c00c0c51240c090b040080c1d0500b00d223071100c2c1e10b000c6c041d4043d009114251050211060030b00c51507041506035402d0220010002c540044540134002003d89200d0a2107045411900080702c14420018003042206518001c007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 271030809 1250 271029559 271029569
    0x6030e2e0b1f210e060a05090a03140d0f0f02090f040e060105060706090602030c091e01050a0311250312110912010209130b0a0603110409020f1905040f 67
    0x80c0c891039100c5460701070003a603854400320400452400b1480e03c195012031801c05004a54000d10191101e80e00c4580c64407800c403a20b00d441480d200c0010542440002e0b1562815010703100c0402d4000141d0f004016940710303683e4140101e403205070f0903440003e11b1140c004151088400140c54030210410040028000500d56108901302103031800c9140d00850f850341124000c84002e0707595801d504d0300034054040744101821142c408020044482c030054001c004180b0100c6a0008400c03410307160300303047c841c030021560020700240214024280240e1220b03020f040040c13005410a59800c2c03000600001d0140000c55042c0f82880080405800c0714074403000d81410281805001d180b04020055800b035050b40902c900c0a034400085154402e6040303481030000604021819000340404c04041c220856040307000b0082d0280024069100c3d101c0c0d0302002d10307c002001d19140c90000308201175000030880001e0072404010340d90103d501200d9250141100d6241c198a403450055400c444880c5a444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 271032059 1250 271030809 271030819
    0x105030c090f0109050711030c0601060e09100501050c330105030a20010e04140906220807020a050603070e030d0e0315270a0b01080a03020706030e2e0b 67
    0x82c0700c1e51803a228580740c10346020700c500181c00c0c0e0394164200c482032110b003441d62407800300140d49241120302050007816220a61a00106003d41d84180013124100b25107010402c030707040505001e95849400100341c0300080f01c0c00c5414044018030030140916030300c410000f4031805013454002c0350542c0d10780b840c01440c04030050005401d4070b442c0e0010390b9820907043c0c0d5154a032800240300a85c090394019240c40c40c00341040000341000c0300600c84003581603808000c0ca11408000a000586650000c0d00c1e50b043d80348071178045203da40e01d555aa0300910002c0341d1199a401d40403038962200009188200c1c443da07100b06080f8541001d04d42440c6808541504010800150500c0c0b40c40001d080c00081e012001d40ea401036440d01c0c005000402d0188442807000f200d8241504079001c0000c85500303c0313001d0300c1c40b010180d076600c0c2050b07940e00c0701040003000360300055000c0088900980c01b0014500000064410b0421040e641c0d1440400a0145078a030340a040301d0940c18120501c54038010510a843c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 271033309 1250 271032059 271032061
    0x302070305070f060207080c15060a230a0b1303030314010e04081e0c030a0306050307060c0f05010e0a03031d060f130f0206032a03010f03030509041d060105030c09 72
    0x1401000e51107840000380c0075001c0326000c2804c002c1c0c03940c102c9030f68640202030301d5141c01c4814030490b22803490302440300300458144040303507041c90840391a000302c400b50703142051400b40c018141e200342e81c09581d1031540f2525640000440780703880300003000072080001c80c00700c03030905518010f42115038000008403040c0c039540052140310501403845030400c0d04280503d89030180444248000d0300e03c43c4840d40c417440c010544031043d00000016214460060714103000240e15001415a80d41c2144107038400034070384080d00004a1810b031040b40c04c060140f0b0002c600c515180d1512031038144014403c60010742e40b110400000104e509000302e029885101034011402c2403101004024400f0f8151911201d5040c00c101c00c100660030040101c0d580030309041d80300e1401560b00800f040100c01d001c440da02c286505450a81940b1085034180e6804005450640323086480450702070704214022900a96100d0f82c905000700e08510608211910800070400c6604080915040c4030340e031010680500e540c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 271034559 1250 271033309 271033313
    0x150c1d10200f190309060809010906090503032409150d050f160603050f2e0306021210061209030c0f0b010305010b010309020609041808040806040b06120c040504031202180907030207 80
    0x8072220045480340d261103462515054231043c018000114000c1c05039140c4401002003101c04400f45d031013610903441184944800782c42c0c5450300f1201c0c082481e8444d40100006071100747c4040740001000c0c0141940f466080a0381d0303214908004601040501d5100e00183c038514550b14590303a000c0e200d2854140090b043c805508409148050121b160340f460140e485180c403d14404c0f00000810705150024442d5528101a4020350068600003010884640001ea40585e4403503e0400c135082d690720340c400500448050002049165412820032903800070150104401caa010003105018464000701942340d490b0083c00c5820750814181030506000014000da035070f400640307103d44000ea501280c081d01a81009960001640d00144401c0d404100411090400144584242d1281501194a80340c00007080402e0601180050040d44194401c3c9030508040c1c0000d40c100d407090601103039140104c3c0714003003642c01c000e0384201d0104000060030700301d142c500c1c421500842c10f41000c5161413541d03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 271035809 1250 271034559 271034567
    0xe06040c0504031a0405030c1005060301060605040303090902030402030307020402041d090c1003110903010c050c010606030510150e03060c070b10120b0c16150c1d10200f1903 77
    0xc102c1c10500304501d0000501889414000c0ba640d16223044c4c21342d03030b142107030b41309400082405440c202c2c0258030740100824114001e0b0308490035203416865000800d890404150041c0d40005d1080f078060100b40b002030010b031140d0010304040c019280740d0030448605111001d0007241c0c004c0c441d044c0c5a109402080c42a1038942550070950910328002c1006036812004442d684101c4191a80540c42e0848a4488903400809801d0f01490341c0c000344402981c54802300c0544501380c90740c11481280782c1301080201d24171108003400118a06040d030307128181c0800a403d1907400c80d101040b1480002d05d007002c20070b14000c03290707020194800e5501c010313040509041c40300a540b41e00600941c003000205028010701015640c1c0d040c4180031101980e10f06140010700001d020a010002c40d05000303959803240d02031840200c9041510200180b86e83d40202000300350703501182486d0601c05511100c11803108804035111076119480c000f0400040c1103100c079032401c6c2e045c514021501c0b190855401c0000d0340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 271037059 1250 271035809 271035833
    0x41a131110050901030c090f0f03140c0306060402090f04050117070e04120c14060c1306023d050a020403020126011a1204030905091b070b0417040e06040c050403 71
    0x2840c2c0054005102c0d40290f550400c590014948d62002c82e6001449070000c114640a03207118075a00b035842411000190f079a90036801c0700f598160032400014a15051a40c0544070280000b02140100600100807500f20f55003a0440d030340036030b00b000e02e945100300308100c0c00d801840940c45008640c0b410707803030311001c00310020b002008001140c1965001d020380454101c03952218401a980581028200c1c014544d010190540480504513800a5418004100e110180710741856000c1100710387c14a072010300000c41130b4030500b82c54002c24101d41408510855200382c240c1000140e40b542540000740607000981c40003020150b062039020035111408504d030b41120900c00341c46850304248002c181290003040c0c00d02290b08949000c0000381036001e0031b0802101c0095034254100d495120340d502040320803006601450200700880c1c0b0001e61a07440c0640d100d40030300f4140c9080416081c0075500c960190380100d9080790070100703000d054079143c8640f02020015040c00307440c0c00c0c03540d92804e904283d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 271038309 1250 271037059 271037077
    0x703090b091206092b080402010305220515010b070c0e09071505090108070503100611070306061806060305040b060d030c020a090603141501050603041a13111005 71
    0x110100d00a00e0382c0e01d840d070030ba041854101d02520400c0c6401c210705a070b280c188502484050151101c15015940000d0800080380206d90318a60765a0300c503001900078000180444400011208402da08181c0254903801c00e5881900036110815030340c100c00c0c1107443c040e001014501010804880010050b00010701140c00c4406114101c1d61840305c036a0502d1165480349480e140a010b151541541c0031008010350282621b034418161180300c0101c2d01c9000c12a001a015401c16206000311801201840140c04045049036030b45503d030f903105000c2d1556640019014400c07070966034108491b0b8028030000d80024a07040045d0303d85612001c00140c0041c00e07250041e01310741d040c0424507118030101c0c59456006401604a240e880391008010102b0b0702c07085e01c03411500d4584200588000c140c03100000756018850340c95908104c1000031580c4080c00440305850034007401503244941c0f0f485644102c02c07446030002c025207241006000c0e036140f041442c2c400c6d4500c2d03004199542d000340541c0c1c0208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 271039559 1250 271038309 271038329
    0x7080c010f110703050303070503190b30120318030c0c060906130e07121b0f0903150606030e01022d0405120a02010f020607090501180b030f07020f03070309 69
    0x40c0d02003104900f0711800d904090f200d800004100603170f0315044401503010300d844c081000c230034003015140b240458002104055010b00501c001d05807280c1c1041c0340d5100c1c43d8070000720a03071060494840c5440d04d6480003401d01c030030754040100004040b40742d180e01003110b15030010f035140c01c000618041c0c403036140c00e02c02407081d640811342c0c04064403040d0607602c42c040203401c0846141d4440c0e1707e044410604a43d00b500203a8580d143c003401490394041c031010f1040000ea5803120314070001060b10100d8024902c182000300d501800404100c11203210040d8461816002954a090000080c251461802d8503002ca80c010010301000483c0f000031180c0504404180110811740441104180d04c074652001e0ba004031076001021b29840081007400b00d01c3d1003601c0b80c505800ca0b841050741c50b15011034100002c100381880c204184c5d4001c0682c1c00049009420740007210741c5404030b030100c83c0c0090ba00e90501528071400c101000e50100151001c05041c00019420110243d4006050111500400b0480e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 271040809 1250 271039559 271039577
    0x12030705030c0c0607020a0b100b12040303090515010504060611030a110705030d020124030206040e0a2c12130506090a0504061d060f01140c07030b010f0807080c010f 73
    0x155040c503043c3d4028884000c2900c45505005800a5a03054014070035a00c0c118414041501d0401c1e1054a030101c13204800020708101b400a800843d001c801403041d000c1c152656005000141d05000000003000341021000d8a0b50600c0c0c20700c800c4491070b0300941b061102000b400c0240000020640e54502514030784104030481c04021107040c0850f40d845541c0500c2200ca00b60716158041d00035580c00018003104024401586890808803916403101941001c070400044c04148480c1e040a58403001181d400310343c2d061411107a10000c031a0319100030f440000c011307040c4903403001480344420980300000c0942c1020040c80b82c0815001301481035502c100c000041d03156440d10760040201c000d0000420802c40d940d5141060360361000c0300d01080640300e035040009511803a0100c8901c01641069542d103c0401000b000e01c066070340180c01070003580c420300300c0c000700281180001030b001e080c6e04101704941b40e00c1c118030140b42ca80c00780c020412640001c514104180d80c40041c1c1c0719400c815103480029 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 271042059 1250 271040809 271040821
    0x40206030f04020f1906080a02070c030b090712060e0d0309050c120c130e1606020312060d020a09020a021501140105090a08011812050c0a060f02040f15111203070503 73
    0x354080e44c80038982c008404021004100700301017044402c450b5580c4804e5003540d0741210400c100d10890500803c1111403071001d2001c540500001640050103404503804507441c1c5950001c542c0346803404640e40d035100c01d010300200b04148241803172842d10342401c5c440c0e01000d40d15a503e40407184020350051080c03602282c03054000b0042c2d84a80b00c8060207070000400741445800140c046035540a0f0144641c01c0c0760305501d4007040d8400d0448a480e40a1800c00703200c40c801031042e50000c0c08940d8002d11039030f840c034096918000c00c9001402c54890060340c840c1030f25400f03410078086604d401707407100014004002c004c03118a051442c0b0032003460080c1d501c840c0f0705c00140d4142050b070800d003140c0d860243c2c500d5041c448000080100b0f805504044118401444100c40c4c0d840b0325010103145400505c0401c002031081d402404140700201005420f094031585c1402e49165a540091881607403003400d00700d5660030491120036852200d014101e0b59111701102601440b01805101c00c0100010004903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 271043165 1106 271042059 271042069
    0x60703090e0601030204090f0605010201051b040e07171008120408150603030d11031803130b0706092120070b18030d11010507030203040206030f0402 66
    0x1126a060007803200341e455000d0010303818180c080c000031899403114001d4688001d0084400103d551500c800242034660182c960410b40100000f803040080e070364403c64003075511911400c8042d44603140c1c00c070360204903101481a150013050500984000000c401030403103040b10100c586a03d0101c416803400d01c40e0340b16881441e0b00980b058014003949542e05540410700a090740d04000950300c202045e540003042c0307501c0e002d40000030400c5560110000c07240c1d00c0207040c010341c00d0001840e0b504d1420b02e01c500800c440d8580c04240d03070041007015040045620b902150142090709a5000b410f000456030020f0008103c880b2128842054105194006100ca810061240c20300c2d181c1c030182c1950205401c40c82d9200b00000d142c040f41c13801c0058052201440e0b41c3c050014003050012402c545011f1f05c654201401002408003682d00c000559402072003070b2100050a4565100081c = true := by decide +kernel

theorem cover : BRFrame.Cov 270863309 271043165 := by
  have h0 := BRFrame.cov_init 270863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 270863309 ≤ n) (h2 : n < 271043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
