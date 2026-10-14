-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2764
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:40:21.697548+00:00
-- url     : https://prove2.me/submissions/cc7bdfef-f6a4-49d6-9098-a7ad4dbae1f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 496942446 ≤ n < 497122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 496943696 1250 496942446 496942471
    0x101e060b0c15101d090f150105040c11030f041530090c06050a1103070f0209061206041505070c030207050139030e06210a0603240e070e 60
    0x4180f0b103003001203900142a0300200d00c030b80039449031011101c02e03416100c3c541c4611404565019000021034a014a9841e44c0f590014680ca0303d0308000140c50b030001c07558180407070781c1c22020540340c0034401000101102d0060b603940320700d095810110481d0a030344080801110300e000650030b0081da405a050302550480b0302d9504031010016900410340c050000b02000030014000801c650071401a1040b09655160b03c010304028407070144d1607100300c0c3d41c014425400340381075400500d08034945a030409000380901480481a50f4400e01e02103060b6070994100b00d80d00c181d01c0b03200d625801600c0c2c0c4080186402640001c1540d0060360b19625030094078148559880c042030000f130358101c0712208081c1d5989001c940030001c142e290f0050841c2c0400d8000500340c480545907410100125030807071009851181e04040100b0030f0706201c40c0c001c5c0414004640311003001001c81c003d50041071442d102e00006090310740400d68145e003100d485a0058002d900101c00400c499140c0b098226030011000140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 496944946 1250 496943696 496943701
    0x60a0e1902070618050703021c030e100504030510050105150a08070e0f10120609110f0a03021603031505040615080907030b07050c010506012c0102101e060b0c15 71
    0x2000c040d001e084445035140c88452800390070b12174005641d0007102d0090311568016460728002e1981c138145500d014012890100354510282865003001c0603840f601e00d00f00741002d0302e80d51198100081c0e08003001c440c2d500c8500510241c540301a14218060113010801e151810401d8060b100120080003074060005540c0c58518580351008801000c000c028000390344103a1080e000381c450b400d00e0013002100341c5002c1e8082280401c5200c2d030541d01ca210f43d2910704140c0c0c010700028a562101246608042d0203000c056115207203503070302031034030303032081d00c0104803c8604501440c1c03408086d84041c0c807590401070104080f05490441c0c0b8070304103441c03520000310b5a440f01c0d0145800303450741c03008145000040421011641c03007030140c100d00c00a41c00a100a4840c100116000c0d201d01030b2081c0c403140340d00e0034814400003004181c40d8010341801550b1440344c4407980d410071900d01c2245011205078111001d03401500b240320358009800c0b0341420364201044585c40c5039540c0c000e07540407216071014401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 496946196 1250 496944946 496944953
    0x50604060902030903070b0a0501030507050d030c05011505010e180a020c010207050304031b06031401050d03030b10031a151e0c03030702100b030d02060412030e0a0803060a0e190207 80
    0x403890240501020a643d01e08001008039620b0f440000252907494400003c200c0ca03034400d00625048a030440011300180b4101810000c00e04c00c060022418441100d0386000042d000b03000300303002d1b01580c100f82401070b4508000508040b0810300128070070b0800345400c03807003041c1c104089a0810044040140c451400b00034207402449154800740540c84082000000c1041011142919941601c064480c1560761042642036420161903d0001031034400148842d04043c49503003c518064540801d0030f40240b0b020503035000c40d503010f4000084e00e4031030039021140e00c1d6140e0303508850700307032175151000b4400310b0341e00c01501861900240c0c02c00c091000540c07184185c81594071003c20031056039900e0a014070045c1d504c10850701d10300c80301800c04c0011034042c5400314146061007080d40103000103507266900e0741c0c2403410144442091540e24000e090000400304100c0550901c01d1802e2a62410403104200c0d00307500a91040300c898600030200101030909200240c0c240085640160302d40c080c0c0d29 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 496947446 1250 496946196 496946201
    0x1a01050a27020d020403023a1a04030e100f02071a04050f042405030115050612070306150801030b0c0906120411130f0b010206070203091c021203040807050303090a0504050604 77
    0x50010b5440040c11804503d04002c52611171240c244003c02c0035140c230b010452018100202c010060514515410750018401c04030101561040c030034a85011440d0710b61000551007101c41a0400c0001c40e29070755a4441d80c3c040001e00c0103088104001480303c0c44202c0300c0d42440c8214002d860051843c0441c40b1700944490704068002008849400c1501c01a0120b410301c0000c3c52044521941c00c00900c0844107040030359840c2038600c05003405181a0b03c1094465100c07001515041c2010380d1010001142d821002c510200c40045544141c020351441c140700d005298003509500f5440004c000c07651250751050100c5280002c200c3e04100780350341d01d00b4000d0500c20f5104800d50030107a4461000f00d8044180c2c172902400220480070004041907000482e61484200c039800c015a204102001007442d2950321414681000f038544480718071a503004c40e15001200c1ca020403c0d41c00460107210b030940c144001006030100780d00440c01e0090010000e0b1880c4450701c0303281e0040b542e800100d4080d880e1358 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 496948696 1250 496947446 496947449
    0x121819022103031009060b030a0902030a060e010f0f0c05340c030b0703090c0909170a050901081b0703200f031c05010e0403080c071a01050a27020d0204 67
    0xd800c0102080020400c0d602c0c0da00c1154483d120128105012804140711b1044d80c0645901070b010b5811507481d0a0343c0c40041c01c0d0041b090f070740b51241c0a16000083c41500801c0d1484000d0300000c601c120819000800780c80b0b02580d5900003604004000381e8042c0e21405440c100c007641180100c80905100007220fa180ca40c0e00c1104050b042c46203042c0500140b000c49c541100c0c8603640403a95030750303188421002c55858030350040608039050000c0000b0520b41e085a10103a000d00580d01503003000b039407407401650285511901107000499040060340e0480902d9512000300c54144c99080000d034015541031099180c02401c4c03200812440d40a80105030031045460103441c1140c0760b82c0b00380c0450650720303000136803412140315003035540d180480300502525040f180100c5000f0015100c0c0d940039034480c4c03401024100003180500c9000d010554908002d90f40c41d0403000030950304e5040c5000d10490b131045411805044000c03407036120280500300b00011011400b108010f031154203100c41003000e403049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 496949946 1250 496948696 496948729
    0x18120e0f06070201051612050714062a042303010507050304110415080a06090b09070b04030f11130506040b0603062d03010212101401020a030c030306050907020312181902 75
    0x514020740311f80c40d0031100805219026006840c448602c40c41629a1844d04480c814031208800c40d904480340d8280f8a420741000c0404911810552201c203800c10280704601c04500702249034042c1116401c00f80700380b581148040c540180b45140907200d00140203040500e0328011583c13400c0b21003141e0100d2007900040c000040c2640d50748016824414054041a079054400f04007150200790703507240018410088880e000c94850500345191280e00d42041901002c0c0d40070308031a00c42c82a2696110141d4175658901c000c00035440c1444030901c011110b00a0900f8010b080030005d100503075450740c00408100d1070140082c3c00c0c41e82c0002d00003a1031b500b0031001c25050360020411000d0b003d03640241a11605008807003902c0541d49005a0041c00e0103945c201d800358100c0c0010f207000ca4452591040d0850083c100401d8041d03071000480c14140c0203e403000d0041e040411110604414003c030290415000803010964a0420f55420b0f02c524106040c030b030400180308101c40454564405001c80a2036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 496951196 1250 496949946 496949963
    0x70f05030721150603030206100f0812180d05030d141e06010905100309050609070302060403120c0807030c060b0d230c12070512030f03160318120e0f060702010516 72
    0x51764903000e0742c0c1d110150b0f0041450101c4610221301e00c0c80205405040311150381c02401200c00c040602100396000029600154542d0301d02100e403500d441000040d0548a50002d523602c40303541102d03504480c503040c01070001c05548070034070644d054894035045040794644280708940d101d01d07005841a0256a201c05e4000113903010468006416074030105000b80a00240c60055a0b1081c8680c1c60702000d00009600100038401400881d10403500c40250b904a0b00b07194100121540340c081031070b04162030032030010303407601011401c100b4540900c409101d400c0da042141e002880e0340f04000452541d43c42e43c511403007025920600c0604001113000d26102414140350b071820811001e4880001d80102030241c1d82c5100440319031007002086540320b40405540c5815a210108079038000c0c05201c80f81410191078070008c0c40c0c100b559241200000d4072541c41032061480c01880640008882c692242c0f242d168580385945c0341d16210100c50405a09180256484162821000c0f8850b52030030060030f901b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 496952446 1250 496951196 496951199
    0x40302090114213f031b07030c0b0a1d1c030b0301110414010206060105180108060f0405100905060103020f1608070b090304030201080a02090f0f0a0b0c070f050307211506 75
    0x80e00020701a840c01040c034002100180d003902440454401034614082c4410386c4480c203035241c05040d003e40f00d511700c030b03140481c8498601d8850403600c9400b602c0100c411555124841c00c8071940304491011015568041c10110703003800d010091220054490005041d00c847c440c0685540c00c0d406504078045181030261596216001a0f107121012038000d40540325080c0452a40e60280c01900c00d407514104c1d008050141034001101e81032030142c0000d4200c7c0d034038000020699140e000302072156010088800c503051500b003600c010348802030181414584100314240012841c002240d041074428983c0c0ca00c80d034054a0035103141e10400c6030252010000b0700600c55504804401041228000d0380d40e5451519502d03249005c0303216050089a02019070612641c0c1401d08000c141c1c90004024030303d8030802c1d40c03414050b01e00e600400d854042d54001305801e011101c3e0928642000d000c1c10380c01001d025007881d10405c0b001244d4101e500100228242103000c10012008100d16014010424080306 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 496953696 1250 496952446 496952503
    0x150b0403051006060219060f3305060918060d0615030c09110304060e010b0402030a0b0a080102030702070b0d0b0612040308090a0210030c1b0804030209011421 70
    0x2c00480c1518800c09003400302c0050300510000c0c00c981403010300c441003513100d416a601c400007041d03014811040c160720389005d20460703c0001110360f903d00d18440203480c11007001100580c64425030b04040d208240621076112181c45004029202c0c2207a8500c01c01c1588504002840080c102c1400800d801d003041d01007010008a4010301c4c003124800c4007198859502d48400c5800c0c0c5100314040010b80e4010f00001780498100d4000b1000514100000a161428540494117a0344219106030321551158503560040c10070b200b07204003c3c01c1420085042d818101002500c0d59958030980848a00c0441c2e0308081c651203512440210720018251591080d48003181d0300c54110445003075020074459400103080c8140844d80750070301030303008001942c2032002c2c1109800420103282c0c0341e0304001728000320b0a005081c42c0360541010380124151a02c40c0c4c42d500c10094044416000000c1402c00400103041d141c6440d20385904d41000342c5e40842d01c07000ea81142030704d4003600c40303408a00b1542620704040c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 496954946 1250 496953696 496953703
    0x60106050418091101050d0b0904210c020f090c0f03161e0f1809050f0916061704060f0c0c17040506030a0f060e1602070501080402030a0204150b040305 67
    0x40b90b2862480154085690500e24100c811416001d403030708540c0c15521210750300c100c00030404580f4220f00054031800c1e0300f001c01c040d503d080750122008540c043c4030387c0c00c00c072801d0a0300c8025a500c1c64203414a10981d0b0100702100607128031580170320f003844080b4900341040c8068440f90039071380c0380a0f0389a1500d01031004a6801d01c031071400201718204110070b221020080c9182c813548098403007405d03d1560000c01c40da0313104030410f030400c1c0102e001d40104801903507000342d5008030240340510b102d904010300400d0030000c82900c0a003c0b490000010030299801080c0c07a491a561604951044d036201e08186025010481181d1805031400c102c0403041e0313410040031400c03c1c2c000c2004010304274000c0840040d0b44514060aa40480c0920000e002050181c0080c5245020030101164040d41d0b041440703900d40301a030f400001c11074182c100d618005c0e03041140320024002440d1400003410300c2c0d000b0a0303c030000194080e0042e505d51014040a08d080325080000340000c0d0485c2d991583e4034204241c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 496956196 1250 496954946 496954949
    0x30901110307080f10121103030405120102040302030106120506070c020f0604030f1b0617040c08071206050604060b0306061612050702011211160f0204020f0309060610050316110601060504 83
    0x44142a21000c85d01c00e01c840c050000654030560309000d184d40c1c96441d04400c100440303895950500c02000042000c0d110b10300074510700c0c01300e500090788650440c4101801d681d80c030b40100b0300003040c00c50624042100055a5a001003880c14076410ac1001c2d4000b00c1d0ac4c121000c00040e4000d90009400420401705e00c984030b480340e004809000300d041440c12580c11400c154490500051107204080b00305036219001d07250420310500b0100d4800ba9540300ea41d0801741107612004c201e0704190700845c2800303400e00526900080454041040906003e00e05100e070002401c000d000e0750700480d400040320640003012203066000282d00150389260f00005042d94422001240050b2080b04030304d41c20000342c060050400c01920645003000e156480007840080034aa059511b00c0c0301c0d00c240009a20350784010107004000314020340e520310f400d940d9103141190107400207006009125461149641c01400c0d25040950518003000b46120210211205140c1640c82c40660048400010303816401000520 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 496957446 1250 496956196 496956211
    0x4030618030806040e0616180f0f0b040f090218091006020c030a0b06090618090706030c0810030201081506030903070b1f15110d0309020406140109030803090111030708 74
    0x442d95441c4820310064402c400340b20722080d07006002040182404413200d00740e040362841d2509101d200407c1030800041143d0000d000c40c0c1d00c11340180555240c001140c00502507a108042c0b90600c1c011500d910b207001885039250305503020404031900500408440000a00100036401c1030820808003200b091507131060750301602c5440c081080a003800315a08071855041111a07000d41d480b0014800c801d0700081803183c0c42001c0d4000c1d1803514074102d64160107034020710f004119031800c0103409000c03510155018403d102100003003103000c0341040301c0e200980e80d081ca442c00560702ca02220040340c69191000d00c0c1d0005020040040f081000000380a415000c0e084c4400c060320713201480055400c202303469001214400d001403020b4604102c80540c10541840c155083c02c54028100b4103001d0380e21042400251206000703015407800340104009800c2c5015050f520b81c0550300042d004410f94030005200020200001342d40900030340c8640f020010400300e039903880c940071500408016085500c0e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 496958696 1250 496957446 496957457
    0x150d060524060304061808040306091b03050303060f010311040605370f020a170d0501060e01020c240a11010c090501120525030e0f0d170c0403061803 66
    0xd500007150210307440a48002e800b0529548450329180c1c0900308100c282c41c41c14101c44685800608440000c00c0114000c4800040f580520318098840642000a1050402100030b06001140b07001c01140d4100604030340794100d00051800507406041e400458440e0102c0220340082c105800200038081c0d66841841c83c09041c400030b502809001c2c0b45041c500e512400c0f22a070750300441c05421814100200341c01116080b1a140d600c41e0124100311140300f80c032000c08614101102000d00425014220a082c140b401616800000390f88024a45169108501d060a0303074102c2d040c401e6011010f014100d4113955960516100a0b15070801b800003035689600c0d0210007140385100303503260010303600165122586a000d1402d400701a020282018200b4884103203820003000c4440c111003084031090320302140521420000310f092442e1449002100c1d001090820256a4800500000701c9c108041070055600c07a0b83c0c0c1d0300f100d1f0065410003840726240403820107290311411400710340d04c3d100e80d944 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 496959946 1250 496958696 496958731
    0x507091413080a0807030b03010c200c010f180b0a02030c070b030405101d060106030e0f0a110111120c031201080d08040b07110a0f0204050906040305070308150d0605 73
    0x10100c510340140010b404140700380300351003849100d030360101e07000780540c070340860341c0164140000d084500e564100b60201e501e55007008216240318641f07461400d40d00d13029180001c24400060110008640040d0412003d80c64144072580c28600000151480b0748075035450f52020000a0b50342d501c184007099640c0701d040710000f41003501000b124401c951200c0502042e14074142042c001e0000a1304510019891610707904202c5000c01040380244038541d40404d07583c070600f1000d800c01c114404011481e400a450310300210b01403c144020094081c40c0401c7d02c0003680002c42c1c14500d168851440003080040c8a130a0400c0002c0509021684544014a01e90343d41004603520503840700b0a4002c40c8602000502040032089100d600c5011030a1003101c920b2149100c5040008800e42180d03d48410940b04e010760405128680c1d00141c1e40c0000c0005090135200a81a8018904000c041003800c50002d168001d1501d244695200040c4c003010090b5594600b6401a140403201805d428002104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 496961196 1250 496959946 496959961
    0x1020c030a1110090b0a0e0f1002150a020c060906040201031109030615010905151c2c0a020d03020f060a1a01032007050a12080c12090a05070914 64
    0x1003484456a0290b0070100d454007080c2030001d080340703204099050202200d000145400240300404100350a030391440031000c4104100311450030f40701c6a45000b52040d9001110391500000c2d9030480c1510202e4140344c41d501d0f20540c0c8041c0c4190304910100c0d00651060200d11000020b80034041e41c402d8030203000508001d0115003803801070302c0206034107034480b1000c104941d490039118900084c040c50451541900e40000c201030703602010010420f004000784032040034001c0c0300d0a04814041610900c0105101108000840580c00c03004c0100300200c824401d900c5c20411405440b158042d090045803031060078043d442c0c20780155020301c24020280024101c281c0c92080440105200925145400c2e20100440050444d5201602814145802244080000c1001d0142140300b100103002d070190a00d4044190742450759002d083c03140301c00031310070340820320004d48044000c05d034105002e554510a2a0b441c021004e04083c2c900d0041000c01314803a4240e4001c0d901c40a24840b504507103403507121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 496962446 1250 496961196 496961203
    0x30f0a05280206010824190609020a0f230306060c150a0c120605010206070c03020304091109150702010804060c020124080f060915071e0c120806130b180907030201020c03 75
    0x100e80b400e0841c1d1b0800040c004901032450b4101540b128540041e0030b41d180e40d01d610880e44800300d04404100c1700345107501c51647c0544039000001224100283e0038075001c2081016002c05021640725900100f40f07100c41c0030b810407440c55a0000c05824080c0d9041411514000b02249124080010359440c1080600328690107450102e6070107074010b1032a943c030602e04032414000c0e10401c40840c0401c12000410b40e1241c0544c985000c0c00e03008181d80c442c58a0108145d10102d483d14036030089080c402c100c0540c2e00100703141c1e44541c00460100c1ea400f041e40082b0b00402c0c51640080c1e00f20b0710380b003131140d007030040a101d1019074440004643c4000020b0b000c00b540c400048030190003a900c412502d4003098044240e10f03400c01030030308002044d082d9003609040010140d10451000600360301c05c4100788045140c00c0005070720181003038442c5040c450007103842c01b1000d0311481d92041d141d00300400951120005103079600c1c0c001c01208207500b06032410b00d8030740c04140300c140e0041c0715140c2e82e00918500130 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 496963696 1250 496962446 496962493
    0x6040b030a080d0228091e031707021905040b22020702010306050904050a1209030f0f051e070e0603010216140a021002010507020609030f0a052802060108 68
    0x9004101c80501a07035a002e41c0e91002d192825082d8080c0710741181c4c1c001130504d41e60030310702002003c1650924650001c100410f00d602199601a041d207000440d55400320f034900c00e40c1c2e08011308260000314103800c10258807640900941111030084442e0b4241e601c043d10f070064507012102881a01050340c100024115068000c072488190442c03540110016079000389130b50303441030501203035482d44c88002914043c802c03107054540d600701c400340c1401c10690075400301050b0400d040191407a4290344407a03044051248006000341c920110001c00e0210402103290040e03008040e00c849082200e451a45405031846101410604071012a000d0315040c002e0741d00710407900211007628002516450f07044c0b000f83d04a4030881c0124013881d00540c5824a0a4070b41c3d90103a0000315407810014802490000700410907101d5810501c04a0645141c1c2012282e03011068a8444d850320b8800059428030310003d009030301cbc44808000035519403500419154100c410303d000791303000c68a80d44139904845001c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 496964946 1250 496963696 496963699
    0xc181d010903020c030d1202030429070908060c090d031103041706102405070f0b1617011502010608010c180909050303010611010207050d11070b0403080a030c1119030806040b 77
    0x101c102c00585180c9923020b141e02501984580310040c8080c2229410701256200d0790000d0040982005000c0741c002451100900b4858000d10072842c200e000c0094900130301d240f00e031058140e8003040082c184a44225258500380c5070580b6500c640da203401ea40000248408030469001d0306000803010300d440e044280860716901e10008200818021440c1c11f5107d007030407001401414804d0743c002c01c40900c41940042e20903001c030b20060401806207c88003401c1d040c050f040041c00803200408c034000581050458101000c12401d0700c6040380164090051900031030716641c40c01c42020b08081d23122900c02c00340c85002d00e0020409841d1028101070321015800901940d1007000100203e500c50422444a041010001030030402c259468178106034038120076100187d00030444030150107060000c5030091900148041c07400b0304c1e50780e03003082c24002e1000700b00c2459500e140420701d090040a654056110352001c4d1a130724541508081d054081c1d02c401075001500341c80000e001810248201045040c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 496966196 1250 496964946 496964957
    0x4140628090902030f060a060e131709041d030a030612080702132405032a09040305090303040306021903140a0c050903030d2004030c181d010903020c030d 68
    0x34100c001e40904403440d02240c051040b0280440e071501c040c061a03004400c442e8010030380500d4204844a10341010304001590010015110001403400f03002d25140c00300b0821007522540007000141c000d1000d5441d050034000f0740f69135a6070100b000700c0142100350490b02e08004413034561647d2002521500c0c80100200c5082200001514029890400b00b240301c01c40822001c4c40120300420070713500c41d03d00c0840480300f08414081407609005c146103540003e48030007640d0380000d0002010354110311844d0300501180011505041c4201c0c115480408007030304980da40d80c0c6d245407880c0258002007280c9050341c0326010945106100303004040d40007160400701d09158850040140084c2410205c442c20712400f044803816544051000d0302800400900006070600407031208042d50400d643c0410030035004200c24000a44001440340c2a00d0000010465602c103104e5800001d16171500c0c1c16040101900d03110b1044001500b107200391600c00c3d07090b110001c0d041000c0c0341c1e4130080c03103440310301144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 496967446 1250 496966196 496966199
    0xb040603050903040504020c01020c01060e070c140102090d03180b0720030a050706050903060a112a010204170c010206100b0d1b020102031e010f180b04140628 70
    0x2442500400c0d0420b02c1c10b02640d14042d514400101207a1003401d0317010042e5008205c9402810080c481c0e20000e280e03c0d034840c102880c0021008003440d81c1c0000040c24203450582c80340940b0400d40c140c8805240260096540b13588030b08020300111b6183c40c0b907400304111140e0215002c0040c50940b170700705a00c1002940f207080c00101204003941c901404603054030402c1d00140c045901082440f00508842d240d60b03a88032a000145410810000c10840e90b650602c00c0c00d00c00040110300f2621000000040c4080c0b02840c0350440c480800c0c01440c03422503600201c3c021940400343c4c18006440b0b0120f17412180a0103410005a03141d0004940100003034416100802406045000602440e045028002010307a040c050b21564290201c1c41c00006030760100800505002c0c0500d200d400c1c074503408030748000e580751141064805c00e26020300c01784a12071944c00d011010003a0410f810003c0300800a0015800c240e80445207011b080710041d00c43c0b03c0000e00030250906960510310304080100c1c13400702d9513 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 496968696 1250 496967446 496967459
    0x1050a091b0815030709290604050d020105040906091e0b010e120304030602040f14030a05030a1b0b04111005180d0812070305010303030c0318060e2d01150b04 70
    0x48200070300c2050f0f00340c0031802041d181e41c1d042c0520801341405520004000040b11002d03034212120b4000f4480e0b0015401c070181041ea143d000703490484008403903d088000e5540f00482da1405940c2c02071128600b00700c030100b212501c50704000007258820140044d036500e00300300b502c10780b20403401280c00314103440c5252a45e81881101e4100056040703040b286429500c1c0c0d40d483c220790142d8015862051180c0060061ba000740c19011a50201100202420b8039513458403600d038807070084070406001c43d444440003850010071507003850f950481000da541c3d03e03080c100300140d03031100075100c3c1c8204280001c529000b03010300d00b1b8400034000e000b4000703a15442442404100c2070901c10540f80e520b800c0c0324411501d4482c5450b00e20410381a41c010a195165143c0602510404151042031600303114032026106e060401070382c20b1a07000350340031410200c441318541c1050140d113061100198500710107000001c0c01c0c00c101c84602d20043c000c01c40c0b00700c1041d003d103800b1b201d0301844113a00000c00040010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 496969946 1250 496968696 496968707
    0x607020906040612050c090c0a021b0112060b0901080a020c0a03050c0c04050117070605190806010c0b1512070f0303110709060608010801050a0e0c010c06140106050301050a091b 78
    0x5070180000400586480c500d11522010704800c0f60181d0100b507507203001c1c2c204521082c0d08503100d0100d9504040781114082d4130b89003000c545526000d0342034034076110b40e03106e03152100a90b032640104001e240c2e140d090306142c942c0040c100700c1c0402c0c0d0701030215090010900c2200c00c041c1102010785038600c019a0100c83d607500807100390000d803165205503525a51075100f824020201c079134400700c00c07000e0880000d0410100754011418054144110004810030b034210101c84400c078903010b0301540d540b50041c4c603600c1e1013110103480e500c0c400c1c007042a098078200108807845401c4401b00c0803203001c244c0d01640e03040c69008194014000340d90400001e801180d0740800f40402070b05a0310000c0e01c2ea4040400c03241d00741c1c0840300141c0540700420560170288500d0b90400c0815600b8402c800c28004940d56550711035400c981084080c00912080c82500c3c0e000110b0036803011900078003565608802001500203010740d52160041c1200000e082440b07104404bc2a1400d01044202c040d00400c10b455 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 496971196 1250 496969946 496969951
    0x511803081e0405091005100c08030106140c100b0301060b1c15031a0402010318050601030803090a0c09050103050c0604060219021f0206070201062304051b0a0302120c030606070209 79
    0x115a010300000c540d03a6685004c07980300e40f890148580d440c3e4a8002000324550100c0c03401400e002c8416212004558005c0450741034a1702400c20000040c4e124074090791501c102d24a090712070003808401040c41c1c1154000c140d042000310024043d8036200c02102c0750790b2040003200101120104540030b000c1c002c640040d010701000030780c00032000340c0d02e031a600b100864040c000c41032088000f0401c0304540e01407003074080714910303070702540d02e46042079913061b9403041c0602018144200c00b000040c0484030400640700a1a130210301001026951a4043c000c3c0c0f2080c082210117004038000b5040906000341a5801c468031507004020350402c3d8504d161020010440590300400012103506015400441c0d8444400306070380107006500d04190003e0071102d040d08008040c0190081d80310558101210001840300225000038064440e0743c0102c98809038441c00710002d12001c41c0e00404d40b5003550103030501c484802450005d503030b039000c4849024401116036941c0440c0900c2400d0150600c1e022107503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 496972446 1250 496971196 496971247
    0xe03100506121e070e011202010806041b0314280203150a0605070c08010b2b021008160915030c020f03040906031401020451180308 58
    0x8814107145071802e0415100c1c0c12481c9811544101d561070f0f001c010008500104590b054055455060000200f00340007a200080d04006d00140440c4044e0303504e038402d80300017458000300365500040d480090007610242e040d09218010343d80c00034800085003190345400d09a03003860450750201c00100d40c0d009401c05860041103c0c0040c00390300490b00c41d40c1121020303010720380f03929403681054544078940d19401e41000309141d0400c2c1a000b500d0311105001d550703001c905403880c0480f16154250128a40455001039404001560444182c6810800d0180103003000d1496180da0321220500752141e01480c4282c250649001c0301e62244a8400d6200345000b407214415038440302140c1500030300c0c6810030380000c400c071942c40c0002c0042041c4416504141c500d000020b46c2405c3c40c00c0800600c01e103151000030400c004550b5030b90700000701108100e50303241c42c2c0e0400c031a644200c2c0d044050003000c180089800b183d4003c0041e00080d10080c0d60344103ca6124016500e4520300c005007411400d000106203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 496973696 1250 496972446 496972459
    0x5010518180f0a031106060d0201090909080c0a03110d020a2127171506040e0316151a030601050402340c0e040b06040b0604030812010e06010e03100506 67
    0xa044206001c10100d003400303175681d5500401c003018031034148980640307004e105541e4040101d005036080104001141d2441c0c0b00001c01c922135042c90140c0780704600e1442c0341401018244410150003030f40d6500114506001c4988c1c00ca828042aa5030f080c2c02e07100034000c00d40100c05006101a000c00c40c08482c4201d00d8a1a0b407000d45131141580c04030040c00904500c01d20303140910231000c051004203001c86080000301040d0f249140b500c07940110107011030b03000d1600c0302e5240c002e0780030410031101c88040880c0300500401142c107281e1804d02c403001881c00d0281c201132294611200c03a100700c0301480380040c0540f5680e4a40f6040000035440541030b449000318040c2940413000c500c0c500c0020419003003010710300311180f503d44241c1240312500500c005e00204d0082c000400c500d60345803540034009450004a1503041c0380050484c0c0143e5000500400001600c904074803100a61603048a001d075000d40d0703954590703c0064603400c010200752034141d400501c0c6c0001110f182d03040560010780c0030300300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 496974946 1250 496973696 496973713
    0x6090c070f1a09150c28021510140a080c040c09050a060c170c03040b0f161401060503010506060720030a0b010e01060315050603060a0e010f05040501051818 69
    0x44551629080341c41e10002d80180f40031113000126155000d5008001001051601d4061032001c8010345080d00c900e03c034991240c8600080600800c030040115410b180541041e1400740066000b041041c0030702e10803580b011359030454500f80b10f4406000d5071203403006042c07404104018440103103946c814400030807074090000501c544075505160040c02441e034a92222501c01c2c180480c2ca40c01c074554280c0500300401c9100307034002c800b0065805603207000c0499a9200340820900c81c1601420a9243c005211240301c0d20800c01c0e40a414504100ca12009001c2645e460040508075082158000e400c0341c001c1104c080007518200d0103062001c120341030404054846000b1900e010b401c074008841c203031a00c07001408200c01441c41d913401002245010b1003020040801e049291044d440343e640580340210100e116a510320b0710302e07405440e94102c1c0e10074540e0740b46058403040b200d910865004902e041c0002c1410f05040b215843d1a02c04108200d8290b15442c00200c44074040342508038490107100075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 496976196 1250 496974946 496974983
    0x5090915060c010b031911090a0905011d0d020607020615130501030812010806010501120504080c060c1b0a0c1502030d05162d030c03020702041e0506090c070f 70
    0xe00490b6051074000600408080c05161810b48014240300101c00c030782c10008000741200b5080c0c4290a016a1110944d03120059018081c0401d0f04008101d9402c281c1c0c8082e1100b00d90009040690301c0e00201c03407a8411800e000d98643c10141d40d407800603017140300060000204142c124540c8100139292400e00c52895141c03504a0b1021382045602c01000111200c45051f2011054050806900540a6540b409001030820113110401101840d181e500180910940700c1c1034451031200307c419507000345410b600a80d001e40c0482c54404421074400c1c11102c3c00780001607102429544864907032401400c1843d003120421040d440107046101c100482021480f20380104d6025060b40401441c2c0d0300c182090203030040341d408442001003039000944461400b1441e0a440340c058036402c0000d0100d144180440107827141c400d000e0342150900300421014030b81480d140c80210401d6504205a865000c10450841c40543d48035801000034411039002c00c0302e8440007a905c500c80e01810815002c01d08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 496977446 1250 496976196 496976209
    0x3090e060a0b120a140709030b041109090a0b01140f19080304030f060b090925080d050301090c02070315020c07030b01031a16050a030e160806180d05090915 69
    0x581c0307094080c3c0d070700d018041021420700440c521000f0006000542d4901040c1c010a15030b607174400581a600d800000c0707414400d032a600060058005003000e00d2600d0103e41c0350759144902081110281042000010310b0307803550220061403c4c00400500030242c69900b0086a64403c0340880c0c01c42c3d00f510300006641c6800c200410040d031050150510b400003500740031007164141d00d0b004e8040e4100108101107000081070b24980500e210502c240b11103042e8180f40083d8006401c041c060740b2668880950950704180594102c5948034420700ca03038540e421040f600c1d00b5131480b00400309950070112010210070b1ba002340c00c200c15044100c2e011542d89441d0f8a041d054282d1069400782c26404a17207e150b07085000d11035000301d80c0942ca140140789450010701c90302c40c0b810a90205980c0d288808a03010041c80141d590814500002c1e0f5000e84078000e8580321001507411040021496003c1004110007040b0600d0300c00d0a07131581030030010141c003402201500148006000034000b50000016500e08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 496978696 1250 496977446 496977457
    0x31501230c0a1208070e04090f0b1f050a0e06150c010f0c1205010e0a0e0106050d030f021509030a050a0507050a03080114061204122616080403090e060a0b 68
    0x7400142080c40643c1062018001140c1c140010420500200640c0c10340001d96907500000a490010358031134641040b070485008050010581c04410040c490b13640d007010002e0308042c00700100049400d517500204461002c05c0d11800c008140c8034000510640f410803c204024921551400d142440c4401e4284c00c40e10740b20b441e60546580c2e29001030500d40c1c0880c81c2d1420900b035403010001ba5040100d41c15441e0307401000480740b6501da601c00d00c00349401f9041400100405490030014940924019201c1e80c804040400107200754402d03113614102c51340c01503000e80c901c00041c40c50002209000c8030319a002100440601108100b0700000071010405446554080e81e04e040703455040400081c080743d0080142441040203105400300d079008800815001603003d0088a211a40c03c0701c10348810005000030409011414428004076081e628200e106032440a14049074071080b01e1b082e07030003000039100600001e80030070302032241108480711543c000c0c10041c210100305641d000d2002c3c056004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 496979946 1250 496978696 496978717
    0x6130501120b070806010801090f0b04060306060e160c060f180606090c0c0819170c070c1d0f060604050d05010e0c040207030f0c060908120f0603010203150123 70
    0x101c032458140500d03000050b800140c5441d101e903241c146100001d08014042c040c04044958984d0f5542c1c844181d41e00500d4140c4026009010315540c90170190010400c40c802e0b02c9404010500003200c040561907280d055010989611400d60990744540c00288041c5041d03000e503c0da1490007a030301200b003100b00c2c40460310a90740403c46604150501054a00400c0c80b1820300070b1482a010006010500340c80c000d030f4000d143c44507154980c00c0d04940c6110f40c2052803c58031224030910030a103e0303220040c0074803400785140c1d143c1141d8900c580742c00c0c0a0302420240f5403040083c042070113034400000300e941050004020504098503040010304408107403904450036035503a160f0001c405e03400e2041110006003111304504000468401414942c281da01c0441040290b0070f421041004540c0000061608142e10356160500807a84002d0200d050710407003040d024500002c2d40714134050003280d2066041989103a04100e0803001528142455082c1d5101c101100d003031440c0b12411030b0f0180c101c0c0000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 496981196 1250 496979946 496979969
    0x16060207060b0a2115150f080c0618041a03010c020d080c041d07030e01090b2e05060714061302150304030807050708090d080a1103040509010e06130501 67
    0x910000300303e5a6096903001a990380741d41380c0240040d480c00c5110b00d42003a0001880d22442d03d51050381002085240401c105180c02070001055000e0213401e45004e0f510f1a00841c0c045544072410809036000ea50004100840c0f5500481c4072401d240c2c0014154074800d040051010060000290035582c464101c600180c8c0103034025009194403d00254000407981000d40c40c2c6030801610b40700c0c0b0b444041d6000f03d041c07107000201341c4031803095102010000323020000308023900b840d02d0b00c8012000103842200c03130840090304804102d5907401d405164006404a0107003018034000c2800310b81d0b041104e0507601174052100d2404072035400d00c0228429600d80401031144c01641c81000035603001034091a596480500c20400065000002c00d5000110745c00e1040d10703a0a180303028500c5104141100c1c2d000192544c02408001d8401d01400402c00e1684801074251030484071f1641d079001385e01c102c60f4420742003001042101c0d000410540c1090000d08699850300c540c1652034107440c02a404000c400c035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 496982446 1250 496981196 496981211
    0x3060b0a120b090f160c1509050a0b09031b010c0c02190e0c0a0305070804030c06110c011505120c0d110103020f040602030d110a02060414012705010f0509121606020706 74
    0x101c092240c80c4001e4017504143e0000566520b4032040f0f10860260b901480396070360605018080e040103c0e4980f035500c040c80300a24904000c0c1c20340c50390800080c090383d0302040000900800810b018010701c02440f941c801d1100c603007940802c914420f801000d4040d52a005c0d40220f0300e0103102081c2c0d841000c0b06a2071980c1c8084180c0020100c80d001003003903041190321020701001a60102190750410f030421004514030480d880545203601c50880034051543ca040ca800e21030401c0462004215002110030480c03c000c00c03640b03d51180901284c0650094010704000e00080c826103114124500625005041c0154460342001c0c0341d12640013000964404110a0507400d11402000800c0d00044d003c0380c10204a940d02941d01c0901402c000c10130084041107000341d00003540880b201d46180780e10b0f80035406040303000d003446001d0307240240c0340b6509011102d10100f440b40981801001d03d000102086903509005070384540001e200030000c801c1540040012688900180c200540a26400540e59 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 496983696 1250 496982446 496982461
    0x402090c0f160209060a0e010902250b070207060809070b0f04090c0203122206020d09120f02062512090b0103030509090603060106051e070203010c0c1203060b0a120b090f 75
    0x503001071080d441b903100202e05000300300c80ca616460445455410158440000002481c2010000319a00d100144a101c162081c80b59203103100c4d002d22589d800303442c0002c4c1c03103180c00c490a18084884040c240d01035182040714180c074000800c0070141150074241866190759021094a44c1c1c20142401640046a04100b40c2440241150090b90500c103e0403d20034102d21541418981341010704002d9021480e490130002641120040d00c0d0320041c0860440f8000c0000750807800c20108020052285c2c0002882d40700548003000e40701107604405880301002140115103600300300110700001c030b454203015000900c145c400940614840d4450a450300d90b15001d210f0b2100e00140310901c80d030b0001004004050f00401100c1d14114858100079000444003904103442c829130700f0080d050342c41d0213a5180b5059219250900c014802c407000c0c00160282e003811401e0722032500032503451035010001540b5076405401000d0740404100f0000c150481c194001458a81c811520300c405031156400b005802d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 496984946 1250 496983696 496983709
    0x3010e0115031a0d08160b070f05160f15020f030115170f0c070203060108011d0312190e031305030d0207180e070302120a0605070905090402090c0f1602 67
    0x80d5030151404000743d001016241403103101100034503003c0c141529404090106a200b01da941d5040d820311200c0aa44071b103040041c40341d045454030300080d01040140c020910401c00c440c44201c1c00d0340701c03801042054950401e0404020012648402d88045600b100c100f5400501030b8505401c0300f00391071b50326000c01c41c0308003d40c0c00789141c104070140c6055210f00840303030003881d001641c41100ca8410303541d00e84140c030307235106041d0041d44c5480341d8800000c5844054000421343c4191000c0d00411003441d04105a40b400b4840ca00104245e0a80000d1a03904c8100040d4211508008011a01e50304008103d03003141e000500800e58651074007000e010b942010021100c20100510050041320301d0f03c2030001902c1130b80c03140400444d850b4120b65041c60000c100c000b0145800601c0600c40ca015003510a40c0c8100182045843d9406c01000491107800b0354100704c221a40500140d900c0e1b40d99600f04a004200100301d203104d500203003d0b503030342421044054038855070600f0f20000348055500410a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 496986196 1250 496984946 496984979
    0x1504060b06032e0b070f021003230601030f1a090c0a21020d0c02150105030c130f270204050f0108031b03041809060f050903161703010e01 61
    0x100c004005002c3c0005080c100070120070300d112101048030981500d50048008558040c01038800c0128450041c00708112203a05124800c0f10710480030640c800d01a4142c075906445440c03860b02119000109840c60400b460707010b5014900011b900f02000d02400844084104a078014122250040c01300e04204040c0c44d00410340074840c03410301c00002c500900360046245128030840b40d07070b520300740700740d0785078041e034030210010b1402788452141c2040082d40d2700d2850104035860070241000180505003c94042000040640042600c00039a200d10024103c15001c5d021714994801c2d00001800b444c1c41880109281601d155030107004600410050f00c0d00505440e1042c9a803000402c41003d00200f118038001440f1080c490b0b001c201c090725415401542e114540a651600c1030310b000320780903400503009612505040015009000e800c0c0215642104c0550309503008101e40340441a040d4005402544a2404051801c2c0300604600c0e123078200307030700040301e80040c1d10050144141c9a0141003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 496987446 1250 496986196 496986199
    0x9030e040b03030a0318020402030a0e0607031107032703080c0f1b15190c15050402030d05030606040b0408060f07020a05070e040c08010c0216081b1c02031504060b 72
    0x11000301c804002035140c1c803401c441d403020b060751007081550713151704810307101c0c281c85c0c00500454a03443c000800c140603040400c1c109240380100b03000544101d000f0b104c4d051507540d80c50341c0b0606081e840d54003079903480d000440514142d16030220280e9100302007050795005c1e5105d000d0558072410005006407404401580c455560303007140781030203400300500e1140b05200c1021141c0c0d041050207040c86102d0fa2180002c02072120507070b0300da80c00002c0d030005003110310a4403c0503d00b41401e08116100e00b25801602e00940c10340040c0804c0d02174900c104043c54012000602c40c42c90640c2d07850446940350b0055010704e84070b07048442080340c00e0f8060781405520200c030380040c0c10034070890380d1781c60740741d22142c0075a20781c080194000c9001d00000c480a0400303886000c000300001088540c01a60b5003070488504103000c41910382c0459581c0f408105c411036840216240d1002c02c00b88010000c00e50000c9000f61920320310a00c02d0000369074100b207510020f6000c10701c02511802e05080080c252584803080b039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 496988696 1250 496987446 496987451
    0x60503010501210b0402060f0c0109030f0309110d02010203160f11100507060207060225050d090f050402072a0e06030309011b03020a020619120504030207060809150a09030e04 77
    0x2c0c8050016840c80c803c540c4480c070045103075114400241340d40510060b10810200108241e182c40c40150300c0b0f1a1564002d4075008414003541e01c1c12001d80f428184000c048458250005a440c03c001083e42052441401628200180e84143c0c545000340070740181c0c2c8503042075018030f003030002d0419a10074050054030041103204180901800d10712680c50020105940000d031502480595030640303040800c0e208454280f517540011001c03520b004000242d64500405020b1483d00e40141840d000700c034040340072505000c0c5007504200080d00910002e42d92441809004059424605041e0600c06c1c000030095028904041c1440303042c1c0401407040e4040c0c1e10070000c6100ca84c1e008104803443d42c8800e090550003228501d000c90400004e4400203401c200041340110242c242407080c0c00404a00741c2d141800124100740c0c040c19507000360360280150300065018820144644d0350b0f030350700400c1c00086409100881c0403001412200f100c14086c4240d807500c01a08142d80140c07035040075070301110203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 496989946 1250 496988696 496988729
    0xa0e090a090519082a0f210706020c12041a03010e1b13090b040b0411030a020705030c0d031d01050f180f03030f04020a0803030405060a15050d06060503010501 70
    0x1507a94944411800311094100f05207003000308041d1504883c510481680f0390045100060481c0d0f0201c0b0340305038100060301580200c52504000018240f4568074108200821540391a84180e0030364024041910390a8080211750150081004104280c440080045980c1c520b070211a90361580d900710401c2200b4001c200410078009204c61042e000300011110314010100d0703000c0b0a12030f200f00c0484015114000e01d002400095503446444001c105817414800d4100300700401c0110f924040400c60342034014004200c00810940c00b40c98494800d800321303131400c41440c2c002072070b00c0246601c0c64006912801000c40c0700d580007207a041c2c0c4c900181c000b449282040b48192081c0d2000070500d1082e2803043c200b415150000700107038903640070040182c0e50f99013004114803480c0081180d099000d880c4004000441900010459200b070750003c0c040d080360349030065034101501010780040e404c247c0d401c50203d01940d50a0802e08100d10400001038818548401d041c29101c050340301440c4205d84050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 496991196 1250 496989946 496989953
    0x3060412050a0516120e03011116050a0b280e0a140102041d010524180a03021302070b0c0a090603050c120c0310150507030c0510020a0e090a09 63
    0x40041069410309010351502000030302141c0764000c01c101302e100c2035407010001d404d00c140f5100c284040c51007a0303503084403d000d180906007030302c0030704909100f02c0c0d20070080c41c0f80152001241018582c8610180e0b10b1600c0b4a0310303600d0713582000307445500c200c11341d8090003024144a11115010260400401c1c04021083d448164a0301030030305024001298890305400510780079411034025140009042440c141d04007000383c80d140090040b140182d03201005101e2261833110b64500a0b44505a690324059840c44007004000505244030b0b0850220742001c00140c3e0f0301c2c1700d460b100b6190030300011f841d2600c80c20020034014004d0300205581034208090140642d100c4545019500386040100d080c3d22004010600c901c11000202100c00c421000d02802e4040f4800841c010140100300041c60783e00d410b680300e0302e20000c03140c000202d0020030201c1e0000c0d000f9510842041c1c0100191001440034610900c02da0f400b84921400040c1c0320460442180350070607110ba0420549a020007251030700b0f44d0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 496992446 1250 496991196 496991213
    0x444100e070e1f0801050c090102010f0204050d0f08040305150403200d03020c1203010303030204150e010c1211060703050703060e060d0618080c030d18020f01080a0e010204080c03060105030604 85
    0x2440e00c803c1d0720b40404415143d40020b4855002041c00200070400d13031911706400d10309034000929aa00550800c0002c000c08140f6000345c4050f664024000c07402041c0317668400700003404100040700c0300b130014000000841e00502480421215100514211349030a20b8000c1c098082100d148032803004035800510a40340020b15040380d80d0043c240160f40344013070140503182c1981511800d81c01030001002208155268010344120741543e0b200ca15880d078544020340d400100c480c42d15000070780081c1c08001203070113040203254404c620300308007000d240c15610103070a00e00b04540210210f0344030001c3c0000c0ca0760600c0f4480041c180c205090101c0d0a01c4800032720541021503018203656103034402d080c0005a200d40328100558846038496840c80d0000e030301601d940089000d40085440c104a503290b1510080301c10a550340d0080c106003030703441c3c80001500c085401420400b5425900c02d03111006140034030003400500b840a00419100311260b08040ca07017181600898020b421020034080080d4452 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 496993696 1250 496992446 496992451
    0x3050d0e090a021e2a030901030e030a0e040f0b030114091009020105160c0521060606090d200a080304030c050f0a03120509040f0c02010e030444100e070e 68
    0x214030309607a2407240c155040d54840800c03086910030800e05051017280000001030102480070b80742480500d0303140382019120b000b006000400300300401d6070172140d8502988507081c1100e003103100141c1090450082402c5841c541000d01c2120014802d02400443c20055041e40c609140e209100300a000c1d80003d109025041148810141001c02c1c6400c0241c0c0c158644081c140180c082016000c00320b04271625080e0002d15002e8a0213160040b45031820844112201c1020107029035410074815907a00d50301004900818820245110f81001c0607a00c003080131700101102070056441c3c034210b003060380300c0c0300055001ca07219100c10311041210351070f00c2c900401101c1e0070141030300e40c080d0003503010f48a91060300c3c030040d40103140041241f14005c02d43c1c80401720001d194000c0103d40c02c6204850740c0e034400c9004160101c004011040c00b81c0341c0c500e281105a4402c0340124801014032040e10301e0040d986602c142c0300741c22a54510040300d50354070030f85208000c04401050400c0c07a08480640c0c0c030402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 496994946 1250 496993696 496993747
    0x605090c07150f0c050714060114060a09051002010e0c18010e04051f1d0a0309090b06070f0f050d090b031324150f0b0406050a0903050d0e090a02 64
    0x400450b241c0400359500200d03003500b8480050000300c42c80b040080031948501c204039a501c002080c0110030120001c0c10300e042e1003c14001d4101e08615800708444c64000a020f4800c01c10340d010045000e448a1118000640302038001064260000d80c3c170905240a038002d43c1e028002d50601004101d003006121380c111240e00a2250310f9840e030307081c881e0400940c0f08000c902e030130461502d16400000e0307a000e4444180c3c039580c2c6241c4c00703040b500c4464560b039114402400160100c4010700c034990041d4002482040000c010a107010030a40d184070b41c48501c984140d4051402c0140101030000074008401350fa070741d520f00f55540303900340400c1000a00000d0126961040851100b60801c02440c0715032808101250f0744903200c0315481800805421040043c00050740d00c54030020391007821a0501e01a9451040181e04080c04c2c4401140c0a8112420101c1004000440000840c10a20260501c46599610411180b6180080c0960001c000e01688800e80c41003000c00e0014918154540b8000310 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 496996196 1250 496994946 496994963
    0x1e130902122706070c0b090303090d0e0415030614100b0a080601030b090a1b020a020a1703130f06020c120a0303050606041503020705010e0d08070c0f0b07050703030605090c07 77
    0x403551410094907101ca25640c2a203c0c41041c0304403a5000922204038030f100d10410310041d60740b41d502640704d00040c1c85442d5103a00041500b040c01e03004443c414120301026100042106042e0651203485885030710507104640e03140702080d0306107844c240403a4060110f0b0401d0042030b180251910051041c0d01c00380d0304000004010a1487c0c2c480e4110b0040c0d803500400254007400c18003c0180100a40304142031a40c86844e40d400301c042c00403490210041e001030504408a02d404000d80118002d58070140003400200201034419400d0012800980301804551400ca0704200740a840e052889410710310403c0041403071200402d00064891341e01d40c0c0b520b0080b0380c94032144085100c0d030049810403410a220703520b25009907541039001c0e1807414084e000030b01820750110f034000e844079401403411000841031000101c069010300202d0300a40d105d080c89000300e40303080e100c90055840503188240040d00010f40710051503414012000034160454144109041c03000965086100d0100f000301a00e8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 496997446 1250 496996196 496996231
    0x8180a06090614191e03060b0f0c1e0607020c060f0315012f120309190809030105012409060807030c03020903010f0903080109020909010501030f021e13090212 70
    0x9a00505890704046401118048196100405010320000000c000000700341130540f803a101b440f80c0a0348003190945a41d032442c010350001703992070783c0d4840c0903440d40a11902282044100802104100341d12611024150718284440028100030100b00d00d54400c95061080441600d40d10089035045898035082e11011248800143c1d510061038a5007140340021360b00140100e407460503000645448081074801c10b004001c00c0d183c4500058507103151a901c071440b522081c1840c0000c2003940703809416150301f80303010940000e0a4507002d03040b040412801c03502d0040301c008012000981d41c0d2240c180200c81500381030000f8010500100810109511440f2400010b8042d80c12200741d442c003d0000e1000c05403442804025000c248011000543c180000140c40c602c0d5101b81e44910400410140040c0d02e003400440151a100071194040c2d039080081003064210382440c03c04854001a8207a2140c0741480d0b00f201c2c40d0600c1d44000b50702c1c2e00401212120706402c2682c81d620030414a01c400400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 496998696 1250 496997446 496997477
    0x160f08130b0702010519020301120f051002070c0608012c0c07140303091e06150406090c080a0b0f0a03021003021908041209211e08180a060906 63
    0x100010380038144100c00d405120225070b06420152045200701c0b0543c1c0001048800c180492100f40302d01003004a9102000d00040d42c2c00c0305944089008400300d0301038000100c0d540007203902c503d01c1124030420380042000301540040410340102a403900401c0d1780e00c203c01113155070204031718020700c04001d440c002440c0003078000c080d1079101c3d070414403107045007201400c8641d8980c002d40d0380310341512640342c49031182200100304002061118000e0903191725030721142c130f0790b10304500d000a40c886d0301d4240c040765400d828820702503100896501c8103114103140241e235080350980101a4040c00441d0411010358480ca03402d02c040701d07030584810305204a6124120002d003c2c107150600d0403041103022080d101e622801b01f81c041c0c8e006464040c06160011401d40d0100390501c1116088400810b0b402c44100d1080300c0860f8490080c3d104100880d0509162950403e04103001c882c84400800d120317050103d000c6040300000c10640340203481c40d0401c1809441400b1300e100e0501048411151030021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 496999946 1250 496998696 496998721
    0xe0c0a090b0421151e05010e07020a1509020607050604020406050a050a031401180c0303090602160e060103060b1306080a05060f22061418071d01110304030317160f08 73
    0x12884d095041041030a64550b240c10983e08850002c40c0d90304100c00441d85442179a1424000c0c0b00c01d070020300010010784d0300c843c01d4060502c0c0120701644d4820358100981c0303580c1c0c01400070503c03407006080149014810041100c01603000b881c02505805020b00081d260b031489581030340c2d04912100c11602103150707298003400030f50b80701480f0b0100e041e29030710030004041900700a072441f0f038854442e40760706c5220880c0c4c4da482c4552031281c4504c02410820003809a03000b05c40e00305d1810324000c515192582c02078240e56015020f0301f11034810300c0804111441d40a2402500401c0c00e09080c0700134189080001c4502208407480da1180da0703482034544040c91030305030104d04016190000e00c00d5603a68003000b8100c002c40c0c04001c0c081c1070300c00010017101034181002e9210340603035101c1030038003271480c5003091a845104d40d000d41071082210320750521200400141c0000e41c426aa04000328588501c0c1c1d000100c0060301c0c40054808104045031480e4100c402c4404031481032034050101c3e940e55045645 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 497001196 1250 496999946 496999973
    0x21b0d140c1e070317030f0402040903020c0901080718020f12070c1205071415040809040f0e010b040e0f03042304330b0d020a090e0c0a090b0421 64
    0x907000c0640d0400351a1100415110300312805a06054002117400c1d59442c4684012103041d1101c0810134001030041c5825440040400d01910441d510020f40c02c1c0495008a403c0e040811607a02414007004141c0b64039220407040e0342400020750400c100c00706000d01a0003080112134445a100000800c02c2c1e11410b415001646c0007182403c0d40c100300d04010303105034400c40090310010b07180d800031480c0c445c0024080240079406d1060a5580d070f29500c1d0175030f05400c2019034075840750725012040040d01060058105511402d0000644894820200811651101b45c150519005110710600f05400072090b18112080b8003110381c42e10107500a0495404400145503038440d1a081080d0b8510384941d080c010401400f00b4141c425004081c040050750b0701d1403040c80c19081e01081181400e041d15006005800c00034140350b00392030303102d220035411640c0c1120076031070303100001c1042d45902c0e0340881c0c1c4c0d00040c2070004825203024103101c0d80c5000c0208400015915041c908100310070440c4d00c480a07070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 497002446 1250 497001196 497001223
    0xa060e0309130906050106110d110f10150801060b040e0403031b020109030806040204120f02060c0105010b07030f030c080402040e070f0b090306011418070c0c09021b0d140c 76
    0x2c1080d9118444001007031910b80c103580d02490000041507a034000e6800c0c40343d1006080080040001c070303002c2191441208007042c1d820740510010f40221040801912a040399040004102c0304109480d03102c0103441c41c3d210b600c80e6070502400b080600030030404c40c1c06650000403e42d40329503407800e05034003601022124200000300d50740d80c0003082c2e60640c071099651740b003a80c0d00c0c01151500700800c001d0740124010404a070006a1181000602e0320180e00310a0744090b128031b081021280c000b508642090b03201080c01d82e1b00144c07810825070b01003240d031501b032000c2c2020442d00d840500b0003441540000d10003400b070740d030b100ca41c0d1404190810924008001c040700c1c0d4448152100108003417038210b80c2c0598040d00c07569002150010380d0013001002c080025014000401e8508202481010040c0004060110725080840450600707420300d0050700b0300c001d0140eaa1880c995007140060200007030b030340b0690000101c8000131035000c03c803501404c0011303034403503140d02841c492182455038059078039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 497003696 1250 497002446 497002459
    0x100c0804030b06010e011403010605071704080a051002070507050907170907090b0f0603280204030305070308091606050f0f041205070e040c091d031c0506010e01020a060e0309 77
    0x401c210070602ea40d8410142a0ba403410f0100707400f00103440390034059030b81d0000480140010301055200364003608145009050002c0c3c20606400045070b00d40c000d411416450704070801d04028000200244442103242f24011480c11200f41c594584410190099074814094880032458141c41280c071161b0b400c1d111003072180b081c10b0421000782c0e24403091084140003402e103514260b1510b0700c045d18094409011b050149950b03520b0b080e0503c15400320003052100c000500e1041c9400b02644043d01c05140f1a072191b5542c0c0c1101d003009441068000c080219981c4140e007082d80301e00040710f48004441c124140303030b42c54440759007007401c150007040b2100080c180c0100d400140300402114031040280228242d072030301a1151802c000c55101158040c0c14210788040801c004a8554040705602c032105000c010030a07100072401d400d583c021640070310342c0d444e085420b0003144400d104068009000742081030441006100213521409000c41c003a01560340c81c901c442400c0c0044c02159031114008020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 497004946 1250 497003696 497003699
    0x3020d0c020d0f0c030801180204030b0106020703021c0515060f040908030109053102040f090b0a0e1b0906150408030c150c04181515020c03010b010509100c0804 71
    0xd540e040302c10880b9000991295a8080041c0a61540080c0c3d0f905a40e42c0c8040f83c0c20086481000030142c1c4030241015400c200000110f000a86c0c4540601a66406070050501e1070041095608204d5076031400240c0c21050003000a400040760f000f060000c022000142e83c030800002c0c1181110091141c00c541425130712800c2050300d40086050300c68030300041041e40c80d50084004465a04030364803503100c01c802c4800e41d1201c000192a4925440100045403081c17001ca40070b82656034103102214400e20090a010340c84a0714010a012841da000044c0030700501000380344a5801c40d0384045001f03036141c90104c1d6003030701c4d50600ca00d1120754081d042c80d91140d03514210b6940758400001c51034107010343c0d021641c05884bc0170240f4083c1c1a00038502c0c0c10700b4284030324a2103e684500d400040300d40c0d107a481d03080690714100144001c0c1040901d40c0d10544403848040e040005000c0c04074801c1e4544103150303260f6a0844242c03038906c00c0645000500d41060f100503648460501d40192010401040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 497006196 1250 497004946 497004971
    0xf0109030c0f0815070c14010e03270108040507050f060d0236010c061d010905100c020304120b060109090536060f1506040305060405010605240a03020d 67
    0x4800307046480f1a0200d44081d100c1140c2182c0410040d00c0d40800240543e0110011403000c92002002c00651300c00020f061002061551542d84158550a00d031010040c031501083d103003d40000d20100e080c2000741140c5000c5d502c0b503455624a000d07992080380c5400c00407905403101000e685040c040076030304650f58400c5a05a620040c01109040a0360390301c191000400145510540002e40041c2c6a465004900740c0e20f201c00342c100c4011080c5880010741c0485c0f4101f01c01d009031280c41c1d02410140081d0000100c507842a2452114421709561080000308030000b96090506034161300959100501d03200c07a0300480783c1d100b1540c0406440d900300010321000c7d02c45002190302d11058421413a50907180c110313100701040005603410101d030b00010b00040c43c0c84201090298480500c82140410081100005801d608250402d507196407200040004000e402d102d800041e100850f405030340138500b400c00b1403034032003081c2c0d1411a03150041000d002c014001d4050f180b915159040601042000d8003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 497007446 1250 497006196 497006219
    0xc070b07050c0a0f1a0304030c0b0f1f05060d09030306031502181509011d1c0506060102030c070b18041e36020d020a0807091b0903020f0109030c 64
    0x10b4824481c007201c200c001030601e2800d1200d411107031510121040c00c07450040009403600000d00580900000b40703800400180d0403240103100316030740540c2140364240303919038929100d5103501858882e00e040205000c0c95aa00c0f013641e03184050581c0100e200d01040c50120702420b4035a10051038a9042015555030003e00d0300900602c0400315910302e00444141c0030054444180f000003802c00d94104104100c952181000da280003082c00754801207a0214400700385050812041c11486905504800d01007240c244101c1c1d070403100910007141461546903900c1e4076104180309003a51160001200342102440502d03006903004014010041180201c00300000ca00d840101007034010b280c201c1018144400075600a0500305080c1c2c02035000d445040d014410005d4580149c3c1d000300803400c440010380c1c0f140703c440c2c040d11444010b4a000707481c006034a010b680c0086080402d0800700a0400b03c0d10342d10840700022660104d582d240120013050058501001c2d50b040a0030380ca0b911140480e070310160a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 497008696 1250 497007446 497007463
    0x3060e061b0901050a0e0411041401020c180708041406131a0103080315011202030403031401060e060f0d0b0301060b0903070b032203110706020604151e020c070b0705 73
    0x1089040c02a000206030034200e201e8a142d55000c40c0d0144140343c52603104d419105803007100900f0000b0f07030031001410207507150010752010b200070034402c5041c0f065503410700c0b68a4403483c1c04c2c3c0b102005502c0501c05102000f10083c211410040f80310006000c1c032501ea005d5540402040c000d40300309043c60030417a40f0140c000d15040e900845011001400c052580e400241203c0e0407411130b82c11504c420f150708000501300321000307040110f0088108482c0d5803600c0158000da2103034900040100002e1156084944143d20640501000003880541a1a81002c868480d05000d9a06a440b45a05000d1000304014045550503602c0c1c600041186103082004201c404400c404031082565542e020f45070501c03007110307a000040b03a40414001e940c40d07200c4601c20814405d0924a1050880400b0302d4541011070348407000681c040410b00081c80394080e9034440041200f1014801e4480c00c0488110804072503030108104c9074002404020b5401c144640b1001e001481c244a9943e10b890074502c1d03075510310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 497009946 1250 497008696 497008711
    0x115210b040c090c0810031e170d110403050a080d0e0a05070f0b13050d1106190909020306100f110d05040504060510020604030c02180106050c100b0f091003060e06 72
    0x10401003640c07480c01004039503c6860380705042080f8a007940e2380c0d00410804007840c1210710100200100002d035170310745644050411040056145c00706000084140c80fa800c460510b070010800013407001c00c1012800b003e049801488441d44c401e1002041d000816039055403800c240207a41c001003c012000c1403200481c2c5407050301c548056110b6078000d50600c151100700c6061650716004200b1420804c40741e00c1d166000d070894520118481020801740e5000d00b410140402041e00100c81c0560850340d208003800940c1780031401c40c6440404101402c24050100091114400d0301603010361144c000400c041c4405010381d1f960380c07210b860107803054109015503403265041800203c0c0c40c1c1844104120701d54403550051505440750303102560198950401a0307000480440031aa02e081041d040e54020040c668403540d41d5124400f1884c101100c0c0c121f442c10a608140015902e0307500c04580c11011803007280d00c0025034840f844132002c5645290700041c5014100900d0f4a561200800d02c24450400e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 497011196 1250 497009946 497009951
    0xa0203070332090309120a031202040e04150621110d020a031e020a061115010321050c060412020609030c19030e0a15030e0115210b040c09 61
    0xd4a074210120000040303208411400c180c0d80110301518071045050300f001458042d24a03085994021400c0e2060742500348445a0200d0f004400300342d8030102540000440c01811410702e402c0410048441a024001a0100720150f81c203401e003a44a074080c0c002800031012608895a1000030103100e58a14074058691000030320598503a0705140020640c0258004d000507000ba08650700c0a0035103042100710301c03100c0038056002c40143c0f030b810017081c0681290f4a83c0b0b00007a0640c250b840c501505074103645400041e0f20010000a5204c0181161003132502110858400003418100e64a001d115500e03101c5104141c10b0100b404051a00310004030026402d0f14001d90b03e203211641d99104092040c14190b010340b000c06a1011948803035142c003446854520740700402440015600c0c0c1481d003200382191152550100c4d8140c051040d00100c0f40030034005d0241e6403000a407146000304901c80d12003414001d4103640040003d2680c3c0c0b40c1502e0b13104452008904180c14031a946102d40d0140650451 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 497012446 1250 497011196 497011211
    0x201051c1505040b0402090312070f0b090a061134080301030b0603060105120c0103050408070203013b03070b2805071815111e010504020406050901030c0b030c0708030a02030703 78
    0x6180c02241d40307e44000d00140b0170b800d0a007592005560025100382d510b00340c4528440005104906514002c2c0140801400b03c4078450a2650440302c0c5400912200842000f11004a62507140c200c00c904d400b2680c0411480780e564450006041080360040450400100100401c60318104180c080d00c0d00f5002c0301c400d60b80720020300c250104542c1c5140b250350701009400e80c140d80f0a80000760700911a40e1003608003852540440e0a4452000018144c10301c640d00d004510003110305521a06a404403007403820007511030071240c807407044141c05801d910035000020708886000520313034221880d01c40c017841d0b8042550312a100500e0240c40e10b5002035000d200050048103050590030545110340c04880b2001040b600076610520400a00d401d20302403580b40e444219960025042c060f55240c0011640e4a018030401c02107800c15000b45124943c603000500116500340820000d80f030010001950341d0700c0baa0701035003090081d09001003c003003001082020040003a009580295500c3d1000d00c1480c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 497013696 1250 497012446 497012449
    0x6010b0306010c060b0102070312020607020f160308090301060b0f030702010b090105060f090111030307031a120d1110062709030e060a1101090c0e0c0c07030201051c1505040b 77
    0x1032009032885400101040301c0d01c404504280d2203c10402c0b01401200e5038117680703035203000c0c0d0070300109403800141e0046403c0040950b010300004075042080006420b4103010703480f003171680c4100e600000e03003000c0c0e001c5211090740d1000d41c00301010b4080d258030503440b01400002c00c00258011074094005500b8900100001d0038825949810f84600400e11414000001d020070f45641000003003c1c10846001c0ca08805128180021802100244d40c00314105609520360042d1208005085008501e050311300010080003081c2c94913600b14501e08029004c000b08510340c509401809a0f940403440c0c04030026a07100781d01d110b000e1508031442c0c00d2221100f500161400c49008200290120750b02e0220f6a0760303072902c80010800220300d401c0458445c0007400d4814211503419404983c1c211480d641400080b400c0d803619680a6005400c25160041c1e800465803144850710009040c00b2011400445070314261699500c20900b00c0030401104100401406100d0460b110f0140698504851181d00b0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 497014946 1250 497013696 497013719
    0x902061204051606090312030b0405010b0c010b0102120405040e03120106080f090a1205030606040306020706051b07030c1e080c070f060504060c020f0315040803040303060e04050604060507091a07050601 89
    0x300d81198071842e1145d842d540300c4108140d401c00c0e00004043d45d806d1201c91658941c840d19021f00041559140c68103010440c140c210341d01c190b022415035101d03400410407228480d0498042d00c0041d5000705a81c42010301c82d52841c010f00c03590f1000c807524980041403656204081c0c40c4070351880c100b15420b907154002016100d50f0600c0010b410403840c1106003400a00500056030886401740089280c00da40c0e440314000c91b00101c2d81183d4140d10391050014030010420f6070004190b42c000759500e0540c00b035501400d070b9201c003c001450050000908032002498043c403009154000084603502c600144129454607902d009088440850300300100c1d1a41c405e1090301d0540d40e09464400c94030708141c08016080d003c0c5501d6607818410302c24491411039400c1515802541b1605520b62203041515018068a06580010304244881c0c8108000305d1030003d41541c206410035030000c0c458a0f250411100914a50400710303041c3e0452001c0e881180c4494028414a0300070800d580490343c035840903094 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 497016196 1250 497014946 497014949
    0x12060a0b0d0c05040f030302030c0d03050c0a1b1e140f0d0e04110a0c031d01080a05070c1e02041a0603071404080d200f06160309020612040516 63
    0x1400005006418181c21598040401402581401414581d542c8410107102e20650070440058101007a80d41c030500003003100300420343d10780c00c0c20f00c01894200400c03a000d006410050742003156410005210a00703038024003101540000c00d494122594101c0c044446038800700031525140012100f0024400104030001c01c8034040b00030740303089101004202c6e00442401040c2d940a0703a10701900c40d11511901c000c0c9080c214640b075101d804849410040d0405e6140d03800c0c480c2e41d9420401c41320706d0340c1e800328541b170344117441002c0000c95880c1c1503000c840c18129408010000700326144602c00050000c07101c52440345c8226418070100124105d81d261040c1c84400f001d400c01001d1021900840c01058201c1c27403c40309078900350800e0350310051145030403108440c02d00810f01d010a003521140c1e81d82e0200304184130500c000e03e1000040c0700295034407280103284440c3d01c0b40c1c0d100d140e0921486a000050340d80d03001441c9944034080010b00c046502001e9070125098800e0144080784182210701000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 497017446 1250 497016196 497016209
    0x1020c090105100207050910050306012c070c050703050c28140102120d050115020f0a031805030a0825110402210a0606023c2112060a 59
    0x2400e82d28240901220280d101124000d40c01219400306094880d4554688650b520011203541a072910040c50704142c2d040e0407815880074802c1c080c00e248803100448880e1002c1e600148036003561007050031104003200e030400038014058210000188038001450b03e0300400100d8192020000c120462100d0245080c450b040818541d6410060b07059000088035100781c0600550b441c2e100303000c031490803680c42640c0042c440340e510300060100124014101c8502500e600041c41e8964840a017140c1e02c0d154040c000b41040361160688040c0c1d0410100800241806002c1f00c4004042d03282803d03040c0c1210089070f002050b01c00d1106a40c1011001c3c40110580043c4006404400c03c82400065408000d00c0c1c041070301600c02c1d1002e05804000260311841c8902c20000c0d03140d0034003200900b00580514190b2004103040c1c1070041d41c40013000140e0050507940c008101000c149155030341486195000412076000c020f15003000c0500210003404885000360b4a45842d545883c20820700e2000c50082d034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 497018696 1250 497017446 497017459
    0x50718030b0a090f03021510030503181203040b030114090c0a080406020712050901020d050a020c040b1c0f06141306020a03090b010f08012009150412061a01020c 71
    0x81001c181122245a00b011801c0380100700700100d030701d5605071000c41d041d045005a0045c9500a04a101202d8194020a01a00300c44803a440c540312103039a4002c0c865161031081d103100002c2d001b507032072141242d000d0705410144c0e07460f6541c601c4920710b15002442005460b13540c4064454040c9801c0d40028800c104105000e420100b8442e0308884002d402801100c240c2da01704180000b0982c40550f0061501242e6140f0341c3e501d401d900028205200c0d080c01c941400028410303032030015004240819031850684000a4003040b0000184011140921020741031440d04098014490070009040b003903406510148040501c00c45400c031821422554050004500500c550028030550028043c4545a00e0301090300c0f501a12140c0c00e5440aa10806846042a008002000007070180c0542500c0104250003145000458194903104141c0403d1040d1081c400d10301c61406400d0643d405403030030244581c00554546042c400a1800505116a90b0840301080354079620014100340500400b0b0200c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 497019946 1250 497018696 497018699
    0x102061302060412080d1104050103180b13051c091511060402062b020c0106050a03020901060513090e030436050901060306020d02040e0c2701120e010b04050718 71
    0x2490b624804c1c0200480301460104031a41d140e03aa54000c1a4070001041441644d4615040c000340444180d0f0188804a0b101d00423600702207075440c1c10084d4048035001642002101c0e03407038102d05103080c6114000345460600080702005520401801c00d403000e8180790034998414540a680b018414948a0707004d500450011b001810860007504407010000714907842410114840000c2031403122000110a602040b5074035084000d000d480300074001981c07100e10160441d00429905481401601c046c050005800c1c030005050242800040c41c124904001140c1d04504031074880c1d0082c4128010102a000da1828180c200c0882d80d00c10310900e90060400240500b80343c3c080c0000034030070007640d540c0d04000004910680018a030810002100581e43c60402041100b024005000604c000d0000e006024484501d0a101072640c520012804286441000101c681815124801d031846040460000304000150040210150201e90501c19665405806c90f01162003109425003030701613910 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 497021196 1250 497019946 497019959
    0x14030319030b0105040905070c0c050a0b040306020f0c0d020a1217070e0109052701060305090307060917120405010b041b0e03010f060e0708090303042001020a020a0b040501020613020604 82
    0x15941440040c1801410031b552503a4480481e00b0890340c8101003441d10359088100801d818010000d45021a48081640d080c007404d070145000d01d02000f031507160b001505400d1038100704240e5481c002c201c0308651101c60b0310300c07000391102420345d01111142441c80382a41014020388140025598007581d00c08030350f95204044640480300080e060612130914404512500c580c403094084c04031845155140c4642c0a80303201544005034010030401d441c0000388041c580c404003c031016260000800300340c555030360601d800c0410920b03200001b0484d002030400c40103c150f900e49841140550020840014070034103220968003040c0e03400491800c5004c1c840030320b03070150b05161014200540009000600300d48000112581d82c0c215011001c600010402480ea000504a80c010650009107065003440d40d60a10303140c0010810145800c1e02c03840380000c50344200f164040c42600185003d0340b1607035440060f8031640c0203024190060041c2800501030401030448400c03000da0282044d49407629000703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 497022446 1250 497021196 497021201
    0xc0207091407080c210c04061407050a0b250804030f02162c0403020307150b0105040909061404150606140f0a02031b060708010905090703060b0d050709061403031903 73
    0x20745011091100700141700c0003544201d20b1803190340d22a140b60b6a86040c0071014040f030003440380350400c082c020081040041c2005c2080d18050381c1c01101e081864035280804911948a15240341100d4801d0300401201540290381038040c9010380c03620700f507001117618120b8a1b4842c16550604d141d0f05001c04002d11905202c45138041c2012822450004ca002c100c010904c580980701a0010303400424805d003800102c4152190140008000b08000c10504002038414085ca200303d47c1c8540d681c80500302401010f8018094000c0c0c01c110621031450985080728449000342c1c226000d181c581600411100e0040d00c0e540b0342c0d10726060340d8600304024094116400d51003003080c58114002400603130030181c59821a4117105414201800c10340c64000402000580c0503400300f1012410042448540c120105092058a030442004900c0703641c03550114030b488092200060842c440d1007400101000e8562100c810756000105120003038500d80f04141da64080c086503140c191101ca200c9102060280d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 497023696 1250 497022446 497022457
    0x10902010e06070b1b131202040509160b13030f03030510060512061011101a01031109040f11040e0108011d06010e10030c030b060907030614090a020c010c0207091407080c 75
    0xd00345c0a01c1c10601200400c0c060300b503a4000c00310315010420f00801c600d0680245a40040d114000f0140c00d50140702c1101101c0444c420b500c06e45030005881d0024000341c9004601540e0400690102d06c2524503000b001014100c420b12500319564001091851040003126140395005030540515240c3c5420080d82500d0014850140101d1100c0c0000c2c5010900c80080f8426800c0400103008100d00780216031554151703081810186007040351194450b1400560710307600d005075800900c110000c280d01006040182010054a5003c10000717081c030102349456050390356050090044044090b02520003a05a984a6200d42c03c50070040c0002c444903103074560f1040780d0301121040a0703a2030b2194103207940a5001951000e0318001040f6650401500c1d06812441c24501004850325120202580f1801c00c0c081d43d100c1c9203203402140000f0b043d40c068400400f80388000300100c80956101954138101c904c15a00d0840c00c09d0b08011883e11403078891442581f442d02d40145035a80c003003c00f802584003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 497024946 1250 497023696 497023741
    0x309060f1e180906130c030b13020417010603020a0b030a02121501080610050a1103091e0102120f070602070f1b1403060903090f030f0f010902010e06070b 68
    0x148644004020403810803012039000e074400382d40d11022540014040c400c0b082c40700380900c41c58010b120b0315454020001890f65042d130800201c15107010030480140284c01400365001901d04080c0c40d85501640c024003c480600d01c1301860b11045003440c9003600c2c0144006940040104010401424204001c613800380b5041c80061504c40041039400240b542510b203003030790744041d030480310391540c000c5d141a0704204220749061044003018002005072145084140c01c110041115040c0c9a4040094468501c4010440e00c08450b00c01c00094020005440850061048404007514189940304843c0e11000c2c0306002450043c0d81d4550034040d6000000454503041c2c000074a0002c1140790026080e151030703180f08050303840e26140e075801084140f001d51620980011090240c0c403800001201c03000d11050b20072034507410402c80042d05250f103c103401d01880c01130980c6500b8528040d40020180c0303100740c90b640440c0962000380411341c095030400030b0140c1d040901080f00600d200d141100d00122 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 497026196 1250 497024946 497024977
    0x8220f03030309051203010b03061005180103020903070e090105090111031006051e18040c0203090612060d020604090609230a15051804060e060906040f05150c0915040602030906 78
    0x3600345c02c940341075200760320400881a020091090360303c1c00c840120f01805961401a0920a4404008100c40d1400b200c1e54181030b03001500c10f007a51030a0041400901446145590914010803800d010b0441241c4050783c5520701450000c0070580300d02600c0c0614006480c4a01c81c0c2d041c4030095419901c0080c1f000e885041004003d00660320407002410782c000b104030301e0102580c40a0500c0b050b1200c10424805541081c044030109031079680c10344140b04801041c074202034440c00d0116552040e103420194112500160100700d8a0060704040300f103030550f44082228820b458601c0320412000c803800c41c0c040c440c1340007081804070180c0103c0c0d92041000c191701d801542d00c100203a6003600503a1804036081d5143c08102c10f000d0310340308000d40c60243e04044c1003285420f003550364403440010002024450000c8041050010800401d510404030303645580c110b0414100b81c51540c0c000c40c6486125054503807200085004800680d01158010780043d42012502c1b010001290400d041114040b030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 497027446 1250 497026196 497026213
    0x10507020a171308030c010c051c020304140f0703051605060a080603070f2304050f010509070c0b070c050c04061a091903111509010e0f0607050a08220f0303030905 72
    0x15400502c0f20f004004140c0207580d16040c040400c0d094818640342ca03c148001803000300c0c1c8201c881c507025403140318501030050b541d81c1c840c03400018211511550410134440c10880400700040000c00c070060342d0040048032410a041311148036042c025000749a080321081c0300c5040c1d8035005e0f00781c080e0880350080540c0e03c040c2c0c03503004203143c00c135455000800090040307a4a8005148601d805d1844107400c1e01c050007589030190342403141100610500e80a21070001c00140868803030a4074240081e031040e0210001c3c100310900501c07444440c80182c80e94000e62030903907154a801c0c41000221012155000e40c10218510407000c1d6400507000203401440c5140f02d4405131560001420180d4843c1e03004000c0b118001d01071052401c441420440c03a49001c11901d84940c0c2c2102440840d00c8080719012510968400400c5a030b005001000707109100c0c2a0315041001400d43c003410b903000710103284602c101c1c150070b1248103441e02d501c91030020f0070200f030003400840e200e50015544203010702e0440c4d8090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 497028696 1250 497027446 497027467
    0x1060b030414010b1305041412210c0a050c39010309020a061404080f030a0305010602070e0a0902010309020316180c0c110411030901060302011b0201050a03051b180a0503010507020a17 81
    0x5100f40303a80c00d2404000180c2da02d120020b003415a4ac40d0000828020540d00d00b490000c501c600c030b0301c503107001480300124a034a10203030208130700c0d00120041c00c40c041021002072000580c2c4081d96060b9203501400f00205070361035105e131040e080e5154000b000d04070824074240c0705890f080c40400d001146010100b0000c55540010800c502201c1c2d04400115541c1c3c1614000a0486d10306030091000c40d001b03c0f008000301500c42c2d80c41c2c1e81003410f54000140702645480160010040071070001d42502800901d402d101009490250442c0e0080009518940001d070010302116922640c440102c0d518610030408252031500c200d840c44c03005040001c40148a00054125400440c4d942d00d040e0b45070170040c021941d100d0810b00c042d001da01c00e0089101e1090b400a0800c2c01801ea00d2010140c0d9080050b8207a40d0403a00c40d142106a20308141d59207240208a105200c540341070103005082000d40002d90341030511403544205d080307070b01602070b05080e55a00100f22072141554400d050f0180820f1058 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 497029946 1250 497028696 497028703
    0xb0f010518010212071b060801050d080c01020d0e06040209010504020c030f03040807020a08070f0816170c041e0e0307020303040e1f0f05180705161401060b030414010b13050414 78
    0x14010054482d0015002090b88400606e98101d02c2c01c20444c840104410f0b282c0302d410380103444d4452062a15401a00b0f880341c028003424400040710307402c000482140e25804581c1074003642c02500c85401613030300c80b0103000980c400c50040b016140c0c0204090741e0410142c4001d550440e100750b1040e45800d407141c0004070319601c103030065501c680020000b0010650354282035401401000c01900000b486100514a07400280c41000394000180d00114009141440500300302e090081081102c1c681100269101d00c00089141c01c41c43d1805e110301900c40700010640d8501c03039000b0300031072501e03003055980b0700400e0028004e1144070b51240b5a02c404012041e4084025000440000740401e15040801c0820040306000f010f0b07080c00d100600a0582d481402c540240030841316070440a199031500c4000f000480d0802c2c240c5518101011071841c0503180158002d6016400d04d00d00b140b043c0031510708881070341c43d015a01c41d081203010421021903800083e4045d0180718035004050f42001c482c1c1c01d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 497031196 1250 497029946 497029957
    0x80904060b040f080a050a030f02030904050901021b03040e161b0f1a04020d1205040b04080106050111070e040b040c09050f07180302090c1324030b0f010518010212 72
    0xc00304046800e01242a141d583d400007001d801009140c2c0030916114507455401c80d503800740810200c400007182d46e0f070082045812160000e8030811261501990150017504001d100c1507511070080c17920717810903100000741c0e42130310b0964580600e01c2e1501090791140b0529400d584080c009412710010b9649030000e442c032400c5001b694000306031030807880c00840504101c00480e0110f18a032007800301580b200c211901380160712843e10100b4120300c1300c040d04d0321301582d440588455400100410030b49010b401c060100c802c280c0b00c48010051038402107454024a001e4100e15030502d20004005c1343d451140940c0050207655502c1c1d80c1900e900030030084d5403007103035014585512541480102603100410007007024440b6401500070341180e0010b107000300d02130416074100c130303010844070510302030381811600501403d003060b825a5800101410480e6081e10150007213481d03c2d00d00c0042d8244200041e9032540141c0d500da02d00b090403199241e84131030600d4041e0441c82400c02c60848190000002d21 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 497032446 1250 497031196 497031209
    0x90703021908060c070b06100525020a06020325020415080d080606090609040510121b0801020f0d090302010f0204060c0b060f0907050a03111b0607020f0c010c08090406 74
    0x44071070741000801807030580081c1810b803124004000890114100794407032504000c2c100c40102e8603000c00402241d29000d03011030b06a00d0680398450b0f2080380c07101d030465519a8820380304104503070760320907090340c881c0584005e26a060b0008030070861a60801c0d448900c0f0184018000203012402c2c42e030050400d546500810016444051701c0078125400c403001c5540720600315125440d0000080110300385000e4201260301541d182c40108624655004459010b49552041b83e008100c0500705880940c0042d09a0385000f110080041400394040c021600d00170b180764000c500c2c000d210940070b001400c06450540440d543c0d40d041c407040e1b040318002440240495903e2041000396401c0006070181e01614691080c68070011802c055250713035100607070000d59418045c1d10f1344004482131b40940400c4640e0302004000003a413070a003209150401003011403800440307003e551100c000b646e46849441008100f9800740302100c07080e41c8070342d500d0540d41340310700e16103070600c3c4070720001c10150b900640180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 497033696 1250 497032446 497032489
    0x440301080f010c02070504020f0c0a0602270a03030c08070c170c0a0503101d0616110c0919060b031306051303050306090c1213020103181a09070302 65
    0x1040501020044801903101c860020000a00c448001035079818003803181034001c070380129820850640c0740d020744010720825000d079091800280b1b003210081d440300e4240280032462810502c945102e080e5200c008a034040e21304210281107480c20307035040741c100108a0380e10004104410006061030301b52001071401c1c3c0c02d07005004a48848541c10070229075441409100114004c210b5954005943c080c5491103071400a4000030340c0b80c03005400345c01c4058a00803486000148400700d2064008038440c642181c0c1c410200c2d5078850758064546101c140c07101d5008400b20f002c50480049100c44c500007440740b1100041180d9503140741501074004070f0b080ea56420502c03480344188080da002e02603000c4120f0200080c52030a66a000e84039000181140d80640c001000003100c1c0e98981084518980c0c00000310304840c90420389040304c0345a150400c0780000d05110b84140d2444085e580700f16a80e90112034070f030031424441081c00c24140300401d100e20034414003000101589400e11503018070404050361 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 497034946 1250 497033696 497033699
    0x61e2a06050f01091a15120103150f020913050a060f1403060c031006050703030209150d140106200a0804061d010f0c0807020f190819440301 62
    0x580c460101613119070056400c1060300c139010002400311000070f180c211880c0040540b121401c1d102c40c01a0b69019000405001c0007000b44100b040720404038096851061102c000780c00c514038140d00031b803409035400084010320440c446a03031ba080030360710a4034410001080b0b590340c0182c070460f0401707a0002c003d0196100100040d41002e02680e940004545046807450501a03078018050070f8501c2080200003021441d1000c040c42901114101e03840104103824200144a8210740359001c403100310031407441e0104c4150214000011581254140d8a41101d80e04203000805001d84800640404a01400a0802c0003030701d0100030300040c0c40c0c0c66494107880100c0e0441071b01046100020181804140300311940c1403607010b00b201c00907a6115a9076a1211418808a05945a4900880c2c1d20080e8500743c4087c40e001000c581c0d044600d41000c4841640c00c5040f400c840030310307000c801341240d041800111803c040030a450560651a040c2a0103607520041e80000d041e03960043c15079114200000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 497036196 1250 497034946 497034961
    0x904032307050c0603010501140f22050f0f031f090209010816090b0303090d0809040c0201020a1b0206090d211d010e030a060c091a090a061e2a0605 65
    0x1203609040400d0700c10178515410500040e1402d0b030307228100e07800d90100160308815440b90b5003d0712000c100b00d01d00580038840911818003400018000d10307000f4081d00c045d043e0286000f528007c50031901402400400e5103070504800c40c8030382c2503040c1c42a203440f1840c2400503152480824020100803001e4034074004281044031240107282d102500707143c1800c035035514580c2c001c81219140d8400b00e51110103040c0a240200c1c2038007802911f0350b440f5190803190b1822a030190001c0031401199620040c0200701a40c90f080d41d483d100c2c4e00a50040000c0c01110042c1c100080060304c2c10303008900c03480e0302e49501801020058024505e500002c0d15020301c11031049006ca4011035048401d09248490300c0c014008641d807a0540c003005060591101e030701c24a07042c0035074844c20140038460580c0b41c00c900d0b400c801c04815030000404500a11100300d00280c4684243c50a42c51001080c18000b40348840c850100d4152142004200c54503000a40b18481c454020482044140c410400403070646018407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 497037446 1250 497036196 497036203
    0x2102030a061a0a03030e01031a040c0816030606021018050316020a0f0501081f0503070e041e05151b04080606030f0c0a121b24020a0809090403230705 66
    0x1a0b450055000110503c0000d4001000f045140d1003840c000515440e240110b4841448040d40f244d0030528026400140940c403c1c41c00d0b20614280c2070003209604139040131022203440d0700c680001608488400e000d03010301c40d08100c910b48640320181c2c2c1e8151072901c4d01825076108207250000c440c1c0c9080c4a00840c03c0502d0010f00030015452151382d141c0c0740400190510200070107254a028403090040c03607603140154588007502c0081c0840c0c0b003081d2038000142565a05407000c1d5444482e0010b40d4605072207041d000012140c1c028090700754a40300080c00c0650307400160082c01d001c500c05c0b6200e000114200041c1004181060003052641060070506040001d4807140044c00e40004035080f0454842c1c401120885544185902e024445030400300d90200d00e0f010b811040a1030043d0020b001e070581d80700c420800311000512800d00b5000c160a81e41d50480e148002c01d0a207050040b200a4644484a154032500038200f080030032500c04c0d00f086070240c00d400c1c840010f16000c550700c0300303214040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 497038696 1250 497037446 497037491
    0x901060f0b040314030307120b041b022a060412060b090c04030311060c1803010e01110405120d08160c020d03020d12021303111f0e1807092102030a06 66
    0x240117103245052008004000350403080e00058101c1e00da050140da80c0e101c60b48008095000f8507000003030400b83c04802502c80c035500024404005c0c3d080301d1884030041d02c0d8248095408020300003450a4030300502c1c00064008500103a46843d42c505105955403610329040d0b10402600c3e01e440d0307540c0c3c118a00503040e101081907401d101e074400c0b010411041074000c1116081c03c0c8082145080e400740000080c0074002d4560301074425400e103001640304900c0d00b00a4010384030100c2d0001a0824000c07c0103549000000541c80040c070301001050500c2140401d000b0440385600d8600891112034002c2041c0f8428840b04600690080d00c2080b202a4444174440051050a005614000030841c1411058031203000180c030508103501181c0980d85d0303024a0040d822035800c0411074860740003401400b05c0500d45051401440e840c031201403143c40743c04025100781e2035908c0700382400d414025082e42d203580b0300c2c0000080b10900c88200380903a404114100c5240c0c4140c401007599810600b40003040c0c40d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 497039946 1250 497038696 497038733
    0x70e0712050702072d090605240a0c030e27060301020711060c03090d0803010302090c030903180f0a0f240807031107170c0c0901120b0901060f0b0403 66
    0xc1c074081c822429404601c1000b02d403240304000c500c1c40c21860f449007070208003814155010012100010340c41001e60011400c640040321200c030302000c403070401411489540c0011020a004100108005000c1e1030342004a50080c5442c031101d44110012500040141200f001a14164201c84404011184026a2042c0c0c258025420039845544525403031b10481e554134400c00c1e000c108400400c038200151014040010b241240401607400d040200368401c0c0004e031300441d10400000d104d07007090710450340200c41d1003006502d4901c40395000d51807843c3d10309000741e102c0290300076002c5a80d59245010050305140b02c4d40d681c05842c0858000290384508034030541083c1c1030122070b0306243c004215691201c0c0d0760601050351107a59880001600c07440c42d008107604410f2107600000c03211500a082007201c0c620866440c2140794040200203070003441601d2907500d10705604400200c003181c4d62038200d02150008038405484d06011f378021000d6410560960101107400c1003402201c40000c40707548603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 497041196 1250 497039946 497039951
    0x6112b0c02011104060302031e07050a02060c07020112150b0a12061a0703050f0d02160b130203030406050f0906030406050907060c050d0c1b0303050a0908120301060818070e0712 78
    0xb111010f598900851181400303042e40880051401840147e40340e00c6450303000301ca002c5510300726001a01d0398125191302c0005214200000350003030030780c40403a001560140c54452108000c000341070041c1c060803541040c2420b80140010b07402011034080c120f01619629001c2c2c100b03200d004003004560180d800801507405440c100b540c0c040a0b0001c0340c81030742d018500f0903a11801c00c03005480702d00c1045291400d581c4006508007240c811103540c10980c902c01c03410780d541c1e511905044c1300040b011403c081e5164004010406c0590700420007410b00d01e10107100c2504101c140c80000e001c0d604100c03000c0e1403650300c480c01c10905000078020785001d8001400e0544078941c0ea41c072980d0f8bc1d280d060f05100103001c1d04034500424860001502901007205140c1c0514460726440c0003030054101e85000004a1140d410109200760049040d0144440d048032890840e80b13000022141000d016001c000c02549100c003481012400340a03c101901c0c602c0e42c600304034103003118014405070466110344020fa1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 497042446 1250 497041196 497041211
    0xa0210120b0a14010503041403030c0d06150212031003020a030c03030212030906133806060408031c060f0e06011e1b02060c070608060a0f06080406112b0c0201 70
    0x401e0b0700d5920b00e08120178a89541c595980f03103403c5807000441d40742400070748008001c00c0102e1540c90005c0c165034400610500c40196100032309002030501500003000b50f04000d2003c810086a0f030041c55000b181d00c45582c1d42503644e600450301c1c0c1506070304140c512040d040800c0c0700f0701d501080380c2e519483c0701e07210032031031403500080c1e143e104d0101030038203070075103840e45041c2050140034040d0300b40c00c022600007100c610a41e2244008402c840545503400d550030305001a01926101d020b8a0843d001c0074041c51600102e51740844888481010a50803981c0d00e820108148803030317280d20f46c05410140c1c031404680c00c0c1400058089891070320f40c100b950014a8850340d10a0b4004c95203441a5204204014200460701c00038540d8001c0282500491260000000e030b103075403006070300e4015182070b1111040161100780400000d03625004400101d01d8840100300040c03425031048e0050101c034010715003400c46a100892100c04101d56401114800311840864461244280d90341140c15000800c803a2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 497043696 1250 497042446 497042459
    0x7050c0a0b0702010912020102150a050f0c1303080f040305070e0405011103010b0a030905280b0a0507020c0d080904060f261c030609060e100803040602100b030a0210120b0a 76
    0x42c850340c051100c0241d691b101d44000c5900801403c100085807102003484d07407520409060081401f00c850030501800e050200d01191544400c42d6400c8900c200011107803030454480074407a42c0135104108132464200030020105009002c0b51000c1c203071242d808415400c01307040081c01c0d1500b034002c41c20000390410040250194440403101c1340b0015040c0421103225034203000b801c002242c405405206203283d0300b00d10343c0c1c00300302425441c9480b801180c1c00c9a180c1004c5082281c070104c408a000d80d02c5810b0b00079841c649401c001c81e0040c40b41c0303c41031505c10354a0100341510125400000140c3c001d041c1803002c0c0aa041070301c80c04881c01c410303c8501550403905941c1d5808411903400400354085425900148250040340c050070300b445013072003825a190801031005404903a424503250640c540410700407004801c0b501140c0c00380c1e00501d003803101e0001c02c00c0141181c201c0954107104500da00030058580c80e1448281480646a0601c0c1c850700d00038540c1519050415584540488001071061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 497044946 1250 497043696 497043707
    0x5010c020f0d1b0203010b1203030702070b030c030703090213060605031909020a051c020607050312091b0f0117070f090503070b040b0f090604030b0402031507020a0209100b07050c0a0b070201 84
    0x800811143c9007010200034000320340100041e10b05584c11503940c00491040040000046000d11101e508441c0c2d542e65401c420456804155400400013404001040040c0c1c841c0c0c100c0181c0500027403411100c00b0301c6260410440b0450b034418808601c01200f007080e4000d82498a81003c503019809000280003640014070454071805003a21541a4018001142d9900f80c08110075607030142c0881c0e03803030b0f00e641052a9203411070741e18411114003200014182e9240454442d0f4007250144030240201d09003002c000803030100c40004c50402485160100569850070340c041e0007400e05417124850b00c0c0107200010b0440c1c216402241c040e622282d0100300d845460802c83d412036100118030b42c2c4132459044105000e02c41c42c4401c035400100418080309001e4200d00c0c80e40100d2003107003240c901d6902100c191000d20b004aa011001d0b8000101000150a1003051994042580c01c01c15105030380302d0081d0301e00e40e000b2003000d560b0795001d51060324144c188010500043c080803007844e800c1c082c055000801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 497046196 1250 497044946 497044967
    0x6110d06230337080d0606030b220b041d0601060f02070b21101701050f01050910080d09051305011401051e04060c050c01090614090d0b0405010c020f0d 67
    0x28441007056910306022826001000c0304011015182080c3d0740d609003121940c000d0303810a00c0540c50040001100d038001e1198943c070403c0500083d4a61002c0400120707040e88000080742c0c2152075101c24160395855208085c40c240250211a21311449480c002d072a260058000c14140070042c18111007260300080c0e0030049078801c46946a5480e9902501034031003e5521042d2042900f8105008079099401a1841961980c2d03d0301400300d4200540c16003621000e407001c07000c01c00700c0c00046c009401d00c965801c0e40304000c1400741c42000c4e5140c0380c503441e000c00300326044001000c015060000c0d1501000c0c010761409010000e100a5040c0001800c81e1a5068260b80c1840400103001c401601c5100300e00020301c000c8a410358580740d40c0c020107451150070074000c6549000d8510303a10343c1e03036014010715000c0d908141c0e41c800043d11188207581d203950003080c0150b4405850316103c40041c40d14030304144034a22070f03800800c40038034090004c1d00c2d20049900820054010008440c84998010701449 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 497047446 1250 497046196 497046223
    0x70c0201080a0c05071b180b06030103080a0c020307060e01020114090606060702010c0b0a0902010e01021b09090309030a050a02040c0206090a080a140705010605010e03010606050306060706110d062303 88
    0x9462100300c1000d4555105501c401420130020311003000070308082c00000c01c2101e0300c1c1c0709040547e159064021040365208207906a0108060005101142c101d10140c041c15410341051228080300d9000603160040c0e035445100001e040c15001c8055590a0044100e8454107a02c0d00350700d424451030315030301d13881e00038001e6004060108188095a100e071007c1111550031040c80905030914061180152114240c00d9010482c40d0f80045402d52002404850405415012603405103500d0704021400340040c007118000d21007030004080d15541031040c2640d50344584010b0420719050720500081e14201d04084040d034001a0030021590008199090321a0740440d4580e80ca01603400180c4030001d003036020680d5440041054020404154080d01c2501c500b40c9640b18103c1c6c1d10301c2054280e424501850b00061010710100d00c50307003000c8d405001014441c8401140f020842d00043c880781e040320f010076070004c4d1503103c1080b2748500d00d0b200710b04004000701d26009040e000c01c04a60b8039402c000012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 497048696 1250 497047446 497047451
    0x1519090507210e1504080d0903020f1203010f080708060a0222030f1a010605040302011d091015020307020607030809010608030a05071505101a0d0212040b070c0201080a 74
    0x10304690711030380480304100850100c0341c00c1e814082c80c180c030041c480510001403910402c18040e90101c284015184103591000890380303880312040c91307203000d40b8600b1412015442b60390203104031041e0902c0001d4030800e84001c502e4580d0314002500904281c00c0c2d02c42c4400360006003003440680310110b100ca502100c3c02201680e1090319100c00e1310f290121981c02124846200004000c0040c0c507000441e0990060440021500d42c0180d0b43d00e11400078418080800e83c00c01c401c10055000f510b829500c451360b990203e01040c000008030703541030301c11144041041a082001c0c008032000c81c065480ba02c055100940c01d018003540072400742e04c2044000303014810410002082140309401080c00303031140000340e0340c45096000c800781c03942e00700c25400c80c0c649070000c61a00358201c60f0f1207024801c6020100741c0c00e55610301034400c0b41820020800802c0c0c100100a203000b555104d0000700280c0100d00300013085481c0504204140300009800301c0c0400c102160b0050245c0c2c0d2051115030815005d02c0300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 497049946 1250 497048696 497048701
    0xb030a02061638010f12030c080a02070512031c0e01020c010606030f0c02060f040b091615030e0303131b05030a0f051504151104050607050615190905 66
    0x2a48507001c200300c0082030316580c008070340900000000d448001074050615214100d030b43c0c010003000c05030240220a1000e40503a01003250015600e0a8030039035010742040c3d8241c0c01592644003a0b0b070321a569820160340721850400c16420081c003884940f12100004d5400c01408444c100754240030500c0301182a0745815180341c0c190780a5040340e41240d0000d00030030507145d0701c560190151128007802c1d0012494518005c540b9800841c0107881511248071904150380c4598903070f04004005000d401080c45881c60405c102d01c2080107602c040c000d10a000d40d00808081401010307242c40c20a94802070308180240324011803000710804410390b0047e030360301020b94407000703054041c4c4482d4030090f410302c190f001d90401d0110380715510004d94040c0b000c2e500d140e010f20101c1c00700e40760141c03001401080484c41c1d030f1312450196401450f18800c523403507640c54682d6071000101144c0011406903003e402c01002d01c803403445a405e8445c0f171810180c501003141c0303070700440e028502042072240d1650f41e5102d200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 497051196 1250 497049946 497049967
    0x106090b03060114040e0906040b1308030a051003021503190c020c1e210705030303060d080307140403051c111509070905040b010812072d02062b0b030a0206 69
    0x10703103006d882c0403a116013051800a600300d548035400d03a81620310b20303410f0b000f04500c6034031a881d80c804950010010303451600c400c0000f000405005002d10b4000010010220050b0750314990001140000144035880782004030040040b1583c1c3e0200f8000280707808040fa240e00d0300031407212007054003121a06039030310803414940360304100b4070b401c00c3e48012012003c2d8031400703403e0005022107000204072400b09484101b8940ea034032055401a40c0003244110501c00515550700442c0d11503550301c2c010f04d19500d5060010026040380d001114280c0103032040c80d986941400c028a0602500e2800d400400d00d02c640d00c0f40c86241481d00310401c204143c1c0044c020100803c4540c0042603101c00402c41880c1c681081703040f00b40c085c02401d140c1e0040602c0343d00780390098001e403811a508590040400d541075022084032902282c81b103900400d5028a03d00565201805084944440480c0c1c2e00e0340210410031402d020b204110f0880780614006055819403000035220500c41e07410fa880076680c00035582c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 497052446 1250 497051196 497051237
    0x21020a15111c09050d020306010b0f0d140f0a1401060c060b0d080a390212060a020d0c0207033903050304050109060507111017100e0106090b030601 65
    0x400118648103080b04100c0d40072907091002c180a4080c0d0f95180c07110703260000c0048000078600080c3d4964400c40049c4406078401c0000e04000303620070262440c00c8039821407002550030881a8a92950001d410044400001006d4607405001030000300003100d103000712001e038508107000304c408009003440c1c03240800050b035108180760750f40148041e45201d040d00c1c10303c0c01503000800107000a54015090075445403040170410710403600b03c0613865040c110007002030380b035181140c09a0340000411020303030300c0c91003c1c01018000d940900000d65641d1b4401c5d0010300703844050710079401315845010100702084d9010110104c02402072144a80201012014651901c2c4001450403098401d0307800805c120300040240100d64082c0c031015074050340c81100743c5d0240100701020b13100b007041c130125a45600c4c10f0000050444000e052039810501d10a000421142e8111590140a01040e0b003e000001d42d49130b48a004006d5460850849410130030b11406c5404050041410b121401000001448100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 497053696 1250 497052446 497052467
    0x150b030709110306040c021203061c06020a08100b0406020a020f030a05030f07150506130b1c050c03071a070f111206070e01180605090406030b040b0121020a15 70
    0x4880c02e02840c0a04800c504603a841074940e00d104030b241c481000385407800800d00641c1104c02841e0b0303d00719600c1c40e0078002030f030220340d480100b20b1a8070304100c80007400c0c505c0a0480c24056a640a8072417074422500e418030342c426040858245002c2c4401c2202c41e40c005200001e2075819071380c01d10f0280802d80464a0480c10f040c00030480e000104140c1c0782c4c080e542c005840715500500d0320700c440c00c08410b9804100c9a05407000c0d234200d0540350755040c801401d80c1110840b428050800c2000c903442035003058034070035410021030f00c9400c82030f1100c0207807508002c460003400b43c6200c0d03c0e00350342110f00e41364828032400000405036150980180c0c140710814460304514a0040c02140e20316054541164942d48110303405070100c1d05c81010405503500c101d005148000e284c00403100842c0c1440401d6600b03421454100e036015031180d41c04000074540c103200c43d000d1f41c49800c80903140d5051030011400f509002c08803406071601c658102004d65107400c079900803240d100105000d0184e92000c02c99040e80380 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 497054946 1250 497053696 497053709
    0x14060d06030b09030715110301030b04050c10090801050c03010f0e0a0207050d0906030c090302060a11010f0c0c0c0b07050312060103020909091e01060f09051305010c050a080f04150b0307 82
    0x2d400c10007190004001010a5840740c01078048100e07007030300131000312010300c03100d0000c10400307200510020b401d403000d42d0f030040e004104032903103000104005110105074800074000170355003640c1000070304e10034041c258020802c404103506660401118080c01800d902c40d114410581c2404140d004071564125800d15404c04207880808842000140000140c0c2c030940d400a441c0c8242c2004252180201d003050766402003c9600d0301c4104001120040c001c008000d07030a540e5030400000c01c9142d440389081c84001c50702c0b23880400d50369041800d05103500c0c1c0d01500d11000d04100c84400201c0203c02c84504104c0000300000c42d840b8032004034000d0054040b055000342c41ca00601c01c0d81400060900e0b003e80b6070715440e0092048543c4001e00340c400c40c1c4609009035010b800d0070f0180030099041030380d114a1001d0010442c0126444050958030a1400704001c01c0c00010303800c0305241d024030320710f0740b1080403400c4807241d0030b00e42d03298496488400c605c8410342d9565041507502d59070900140004001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 497056196 1250 497054946 497054963
    0xc16082407210f02070b06010503061f0e03070312080609010303020a020427050c04060801110d050c1905130506190f300506011e05070203010f060602010b040b030714060d0603 77
    0x8000700341500170f600c404070a40d030301900300b4002045903110344111382c4601409402c0d00618080040102c45908601c6680781c00d210b10b0f90000c10154408120400055001d04988051743d5180140a020610064150750041d400240184040b030303000201810400ea054500040d0481401c50a0069918480d04420074182c128021028004001055600c84170119002c00c00207517120310706400ca820300b50029a047c9420720007103601406035807010b503120302c90000c0589401680306440414139030400949010510110380740b4403100715403440401604007034481c1880d207040380700b002e40c20845540a2408110302c18006101551044101201c61289050003030200c5000141c020302c403d80c030a14520a0505e8007002034a01d40c40307030030240e00c000385070948030711104d002d1031040f03a031680030680c160703010740d00e46903014401d441a100303800007000325500014101e480d0034204010380b010340d01050306c41e0b0b00c0341c10140400c420b9400400340c08007080315180e0750b640140001c880600ba0903071000c0c003c00c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 497057446 1250 497056196 497056211
    0x12031407060f091202060a2f04030501091208090703081b0c03070f080c1f0f0e13050405060702060c0d0f2a0908010507081602030c1608240721 63
    0x6990f1404860380c0348030340940b1b0a594031040e60381e084485c005006054801030343d09212161400c11003840d09809030f85200da29042e00e075102c2d01d09580014008a804078025501541c803141c0c01500160403600c41800703002c44510315117030300d0202d0041c2c27212016070154818038814150020410b44400b004041e05071000b03203a07145450340d800f000f5841005114000e02d40b0904a40c5004003d440400070500c039011038019801c281100c142401d0003020003804130403209001181d442180c03110b022002010085042d20700b601e0f01c90704080000c0c00c0d007070941d4080828094403000704419a0351a001002d00051807644011440016000700301c2050000350400d45038441010340f840140e040140c4644500070b8190759180114221031040340c0500c00510b508003c1403895001c2c0712203100c0042c407441100d0500561980e0f160424a40041b0f40500d08a41c9204000710710f0140819408517000b5282c025038191058080200310400800041c00c00c40d42240a000c020052018400d80400c203407810003040c1d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 497058696 1250 497057446 497057453
    0x209061801061805030109080a03050c1b0106031e121103040504110c01060b0a08010902030703020c01050a0b030d1106130c0b0d05071e0e090a1d0a020a12031407060f09 74
    0x602c3c07a030020510180703900001069034241400f4070f04810707500644051820001d5403086008040107001960028000c1000c1e141c1003041c1d20710345a00003045e60000858600c1c5240024544102c030007540f0000845690a80204020b402511b080b880a810007081102e0742c80105411803146800040d0f1151070b0000c0d114044440c0340240c18009140c0008002494030b44a814565000c0d04d00303440700050110005201445081d00a19040501414054104402c1481a41c2034070012603411144d140d035103e043c0180e00e01081000e5507200d05041031080c18010300c001d0746d22010300a10302d881312081c0115407030421618002d00c000030242c140c20142c541c0c2c040d00b035080180001380c13503000000340b00d00307840241d800701c0c1c1581d95031107590741e101d10700f10340700071010320a102c6e4005201c0c014195a4a80604104549013102d07503c0070ba0340320180c8034580292040002d140703000c1d080903400001c0125904002a0050803814038420803107075480d1a903440e0301d000c10180c03001040000c0d4050130a20080d041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 497059946 1250 497058696 497058707
    0x6090309210210050309030d110f07031d150711060c0f061b03151c0c0b07021302030c07080309011b0807030e0105090303060d020d060903081f12020906180106 70
    0x10070b1080b260100d600d210355604a9680c00240da4440a85c1c004001c1e80700c1d0002140c2c4044010300b408843c150a25400c3d0500080d16002680242c0110740c002503c98083d040300d00030441c040000301d81205140c00d406500070b50030300aa4800030402030764004843c10b1961390f01c043d28054102c0400b10340101503440300184d110708050b2485000318216100d19161800da41c001d89208099884451014100c80810044002003514403900410440d5800f440814482c1108101402c0d404c805642e0708c0a140c41400841c143d4540c0700340c8440d00c148148820542c0b1081160300180d0010001a00c9485e0110f45500405108400c08401d401c4001e0000c0300b150040540d92091729180c42c01c01c072080714034420764281d4000f10346010b2103800420000b2100c1c90305010000105001800c209500540381c1e80754002ca0b01d58403429808900361a04200000071900c114100b007010244111207040d26242903000341c3e805080009219033b010800140a644413100861000f550781c049030f0b091560358100103001c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 497061196 1250 497059946 497060009
    0xd060b0a061707031805010504120e0303120a020a1103030a0507030b040b03120a0309051f060f1217070206070605040c0501030b06030f07051309020d050f060d06090309 74
    0x50081500000c1c409008048010005000041c03110103661100411002880360440401c007910342c1884002c0416024803c0c1d80c443ca10500460700c5035a907003140500301d0b00c41100e225100350300070015140c844200000064101441c6070703000d41c40301071069054070203d810481fa0b404505c008400c000c00203070385030412401079060780c800700040d08940d0180002c1d100d000b80b0554140d402201c0c07000340248d080740281103006040ca400511314442d5a030f040d086c0702e002c0082e084034802c0081c000c42042c00c123200b09001802c162454003840c42c074000c1c0d00b17074080011031005004000030014014000e2003800840c1e00041c0d00810707455840c2d506190001c000c100654003900d02e181d0084001c186035000788540070080c00000c0038582541ea032038030305c00c580400040000017088418480d00d40040c49246415002c3d003581b82000d40c80701400d406030400c07100003c0008520b2000f074414800103450300b00000710055000000401c1020042c2020f842080040d0300c118804a101d900000c6004420107010b0b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 497062446 1250 497061196 497061199
    0x5030f0d03113a0204030b2d0109050a06030803040b150f131d01090c0305010f0c050405040207020a030803101a03010b030c0304050c0a0603020c060601020f100b01030207020d060b 79
    0x20642420402c62402d6005880006003a040c118042003522021011400349601c3d881a40142d0443c18601000903604603500c100c801803184002c2c4040d2143c1c554103040d20404c7e0644485020282c4070340445000c41c1881243d40c07007039480000c6280520160003040145030410803565407405c2c03a182110103070408503400c0003860050001d01e40c0c5440c0039080100c0d500c800600c1d204210700c90052100c020002c50040520120310085500f001490a0040d401e05034001d60b500c500540c5581002420340300510013078480c06181101068500b50044151000d80d04d0030341d0010f8070f07156a40b011892503d02604007801c030110200801110001250400069407005550b045e811090241420b07180e020a010300b00a03a02c043c400120b20200e80f802440d4054000c000700c45402c07142c000465000901d42d0003582c00260001100d0460f03980801c022508290207200521340c141180a07040d80320788c8942e8000b42c8450b03ca20f1f0b0901d1a80c072903016104080c2c1c000346001c1a008561901d80000c00700880e549 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 497063696 1250 497062446 497062451
    0xa03080d0b0a0b0d0c17010f0e090c0d1e0b0a0b100e0612092a01110c0904200a0f14060a08010e060406081006080613030903140705030f0d03 62
    0x80a060030302c40320101c2118a6402c1041c246045018884054201e60f40100c01300000010340042406181c000c05001f85004454241900c0c108144031034030101c014840b0207145d10404084020f5100c84c0214842543c02c44844038000305064003140030858042da0103003c005060007407090304141644030840385001129075101130f0b1029402a90858418010300747d10110a00440300317403c194a411b01c2c0e120040c00d064032070090f120a60544507140340d450016041201d604a18100c1d60030007003800c69040c2e90401000d40803601c400144440f2170041004104a01c0440803e100e40c0b90303455801421600140418950350700c81e214030340304c0a82d0b44621400300a00340c61413441c9091100c1101d80c0841aa03a40c03907000d03801c003000006400c03400340035560082da03074440000f0802c1045c82030241101e4007982c041841440c22100600d083d1020746101c4040f03030080c200000180c2c105204a04603030744820a600110803400f10380e0706020665200365054040c0c103040040c0a007000c03d00205500302501c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 497064946 1250 497063696 497063711
    0x708070e040911101b0b0709270c030204050a181103060102030a03020f04180b09060111030d0b0406151e14070f020d020418031205161b020a03080d 65
    0x7040240c0300003040291800102141c0d129a030308005040b44c180340c000c2d0821000000d41240c11410304403408000303450b0700c80d400c400d2055180d4000b000800810000700c0c1031040d4424800a45038281d45650100040d81d519400b2074050350098065400400000f001400b503a0398600c4107910501851111090951608512680e50b099020640c0c1c0a81010303030041d402d00d00903000660080d13100c5801d003080c1c010107000024101c2d400c0321018816a000440114074841e06005104178800c0107400c46051001c509949004840000140d441c40d00c540000407807902c12650214005100039044000750302d0000e000c1000c8190400e05414288201c0c1c02881607103994001c1c11105100200e07200351030000d04202410124000030500c0d4920b83c0003c10410b10008a40d00003012980303000c1e1184500300c41ea401d00000e1680104480100305403010b8248803074500300c9100030000354003822240c10300008145524503021000281601181d0181c1059a01ca8a80c24400f00c00c1d0003032100484004c0c2050303071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 497066196 1250 497064946 497064949
    0x1409060907030212030d05010b0703031a010503150a03021309021c03020706030f0e010614010f020a0b040206070311030d05060f12070e1801020403060501050a170304140f04050708070e 81
    0x100203208448140140001d14295403c01440e01c400b01080345030b51006002c045c4000071144252030080c10302020060b03507030741c0320f14014094810000c4454001c03001d82c0210000c03640c00c1000c40f980000c04c145901079103102000020005910340e040030303400c0541c0103000c1a22444640c803451020317008030307003024039001200c9802e9000d190407640200160880b20f41085a43d000f5004440d003403201940208596110445441c21201c5036444181e18006d554100446540c100d00d00e5209c8860b648060b06540d950b544410f000c032350300031380004d014050000d00513003490b00c24100b001c408100303a020741e07039209983c8600e100606411742c3ea00784103040485500d5540d14164400c0d201404c0300710041c0612925141d02e006000c000249404e2400c1c134040b1b1800300e0700c507080c0b00400181d4031031030000500354102403e01030044119000f1952202d908085000c0140e800002c0c0c0c3d0495010041c1250803000310f42c041440041c03d002500d4100703041c907003448000f6410134a540e110700700c3c0d9915505e0340c0c1c8140c030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 497067446 1250 497066196 497066203
    0x1050411010e060c0a0f06020702091911040e0103121103041701060e070c110109051306080f0703170a0e1203030915152419030b10050a051305040c031409 68
    0x503001c10301341c2c2c00240d5141c00036003a281107a422500450005086c5107894001c82c5100c2c00407507101c1f405902d5122a882140c140c0d104154403400d090000c64109070401c00f0901e5180c2060002a1081041c45842030700d00303100300707000d440000c41d078419203448941e1455143c0000c0310502d207128040d400c0c010041500075031041c0301c0b0310031320155071200700181807511000a62590b0180150410101c89004034168403007034101400f01c801140005a110300d0550924100740417803c1a00c5950815001000800d0031010784c4141780100502050b0749080c0c2035404d8609102d82c00e030042d08031545692071480801d0120203584199148400d603640305214141180b1001c40854114140074a10240d001d92810900c00103108881340c000c2c1040001c0340b10041d142c998002c101c240444800c400d85a034400c50b2315005040d43c240050b03d5800307a6145107080a8854016514424100100412204041c0c0b03203908107180144009001000603a800e910010080c00c807120b444181c105003000800c00072503002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 497068696 1250 497067446 497067457
    0x72d090b0108040b0619060203090a080a020d080319150302040f06050a0909060b030a1223121f0e1005090103051b030a080a1d06072d0501050411010e06 67
    0x141c1d2101216503d0b5951405100300141295070412504440f6074884e200c4c618105010b406d50b03400a6842e0200501003214480c09074001d481550401c0b6880300c01a113500403140801584000f0050305da80d55080b04d00089410000003500650614800110790003202505e001600c4c02603c0074460000d1b01007801050310414807a580d0800335042081103017012a90041e480584500c9000c03908541c05000689028a4076105a55800c440c541c500400ba40182600c00408078024001c0329200716103042c082e85004d200005089070041100051000b003460550711440306484d89102c0d1a00d40b525640e040c1d5410480c2c0c0e03ca42c4400812010400e40f41c1460424104c940c4000102500c01083c20072002e540181803001e5010702c0742038060800140c0c40d46c00303044041110f035188500c011200701c4242e0b00004488032240034000400c44400410706c0c031000040c54003580304101c2881000142c44410002d030904020302103520704800e0000b0800c0086c2c4d004800e5500340e9800d4800200d810130030840e482007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 497069946 1250 497068696 497068699
    0x106080a1a01080115020a17030a060608040308060603071b050d320c01020f04030605060102060705090108060f03100906020405090a060510080621061e060d02010c05072d090b 77
    0x143c1004000444c172075001c001300029144140c4103004038a43c1c40a000b43d85041e0907001c0c040011041040c604458800c403401400c03145049150360400c6d0701d0213080b88401030441402803030000b0000c0c01d180d010310380300361011101011140d98990310313003030035030300c520340d0f00f101da000103200c6100204000300b888607040a8605003485501084030f14524008194000c80c0d0740078503550207101c5140c24481030782c00743c0000d40c0501c40120f05032400c00002800c012004050703a0900109000c18203460340c1c4100015844403081c0d800161109001c400245401c1c0184076100c200b031f085c506603404200e429005403007124000e44d0a404551901444803064802502445421a03d58003581001d548120403c90304488040d041f0240300390758003440303002d0344034484a84125900a0b014403a48804101d00c03080c0c2c03116024101615800c140307002601d0320f558032501904020390102100188082444680006c04901e19919681d04a2840035581a480c0702400d030354400310145c00051240c954040c110081c2d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 497071196 1250 497069946 497069957
    0x10b0a05010804060e01020307020f0d0201050c09060a170c0403020102010b030712030807050c030d090b0f1504020913090308060108090f0c04050a0f05011e140d080a0c06050106080a1a01 82
    0x6200c0111001034000300305440c8241c840303000396110f010a10065014114660240c10b481044d451501d2810b06480502001c5a00d003070304112104401400351441385108941590380c5102510b001c54007407074036503079540d1884200802d10941c1c2c0ea01600810889100780c0080c441d2002800070951242c10030b00c502c04851030b21222443c00240710710407656006480b42441c604001c00c240d01d4601c0c40d0001d4849240f040c1d174400161080c40b03516541280d11480c10444810a86014981940000c4030005624040ca4020856501c1c40e5500c5888a0345214000230400c000b04443c107004004200548180d40032070000d6010074030100780400c2d41540c1681c000300620203219800184002000000d0030200f90aa0f0f40c64410420201c9020311802000b8400b42040c0f180d40b40c5424413004c041e07a90100c2001242418a40455200d0001c117030f050640101c02c0c951181c0c8540c5059403041e03c0f806004060501d01030000c030b981c5404c400740a00071041610200701072001190001c413a044a000070a002c5031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 497072446 1250 497071196 497071199
    0xc2e14070f14030a05010e09030918090a020d0f021002060709120309030203030c0c01020d0e01090b22030f031403010806040f05120f0415050304020108010308130308030f18010b0a 79
    0x50096108400a02003450300300c0b14440c0c0601d1282c50394209946034840c3c1a245c9004010000680620940001848010703618029503000015101da600d02e0341041b401180000080548000b4490b200e20160041d21034034a00b1a5460701407500328940c08100d01c03428200403104a40d0788009000c0f88207101c50b80300d22400303605001d0440c0000e1003d034011410420b04a01c00b00060b20b0030f002618459410f01c00420058074031500181c2030001c5105d070705c0104213000024007840e80c0e0045040003181c600040c0c003981d8031580b250141508035440041842c444e15841f001041000c400301008142d400b03643c0d1004192601d00103818a0320007071042c02c00b6642301070041408282401c504042c481e201c0d808440805a11203036242d42900100000d400c003900200f01002410364045003d08058090300c2d041780355141550000e40120810b00026058003400302e2400015200010110043c542003c5541d49a01c0c0c2030752148100102150540305242200301e02ca640c400301401100080d40303005046801e1503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 497073696 1250 497072446 497072461
    0xc03020f10141e0f13060c121103100902031003060e030408070902190e1201050a32180c0a18180b060103111b03030105180c030703110c2e14 62
    0x400103801780e140326000240039070024400340714900c46040b40b920f41c02940c2e161030300c0000843d80020344031550580708100308108858000070620554030103040050310303510345203100e0040d82225080185418545001c01004003030000c054411510740300216199070383c4482c0c4240030f80c002c0c610400e00b0880541190050f082c00392400380241c0e00017800702c003001e41c2c541da076060030b40c0c206548070b6102640c1c0b405408903680651200e800702c102004a8003410900001d142406010001c001003406c07150700d048040e159038144401d0300b0880005200d0483c2a1f1640e450003035482e50a1403c4040710700d001d054a6024181000e0303003c07407541080000003503699403001940581825218411504000c0020b4502c0341c180c00d00790420500071200454581d8100390500c881044c0c9114408480b400c101c00f00249110000220785c0d20078a6403501148050f08860203141c2800b07404506d04460240d074107511a401945e100c106450607080040d2000c00003941c00800440700000030f0b91944900460004450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 497074946 1250 497073696 497073721
    0x7081509070312270e0106030f0e190201021005041b12050714010e062a072417180118021804050304030c0b0c010c031b0c03020f10141e 60
    0x18130842c03c1a501c0040e0440c4034251191a1307030f000b0b805006690b5005128056140c85a0007510301c000800b080410a81450707280d60300d000090301080040703035103241c0e81164404d0000000000c0c0724002400b813400c291520f103150b40b00c4008a000c43c544600000504000e0031556482e01c160010080c0c240d203030600d00e080c824a1803000216040c00000c5807070403040d880c3e8800070149ca0250340785078000c5202101d8822489580e120504600d540001414003040d9502d040c00c2c000701c082240e2043d141d00c10a0000d50f50401e52201c580b02280328081000a960310407041d208601070300d03d00070000040501e1a915510942072000394100051010b51a100300c2c60602840c9c00038040d01c01c4905103940e07035481c004140215004008402c10106c2c150144d00c04c240502280900c40307040504c0606040c0303640c0c0074400c801c6500c00c010002580800014107000f40039041e402c03a00507040d503294450f981155000f91964030005855600b003040003940c0410b22440401c007110440c0400543c90b140c03207081d500d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 497076196 1250 497074946 497074967
    0xb09340527040507170711010b0904030809070e010b040509040f080a170907140906010e12031309020405010509190f0e06040e060c090418020307081509070312 70
    0xa00008001c0c103240c00004070041d0940c240d1107600c14610080d40402e000c10340e600035140c0814481c10308003d040b041c48103000e16620110f586040c0304010010400a400351040e01003440e04810300005100516600c445e000f80300b03075a50030440e03010955448079004401e6091207204000c0a0610040c829403610703c80c440d40003805a030042511032800d1325031a803144c1c040c032001804207054060308195888074614081d03000400e034010b00806c5181c0130a000c81282454221885460003400007881d60b1300441c0890950400517083c82c40c40c1c100b1030b20742c603540d0344001080c1c2c0f5000b45110703000818007058021130b0241d45041e59100d0400d01c0301e00a100141c2c0c9540d104260341000c000000c24151711142c8840d00030f100c000074019050400c00d09000840d20302409601d070f0303508400300304558034161100f107a41404058030001400c8501c260407101c440c2c0f00000c0298035000e850030000d02000000ba05038400b000c6850038000a4865100141d40c0d240f09110091405036401d20b00416603006104141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 497077446 1250 497076196 497076301
    0x103140c2d0a0207080f190f060e0106060305061c0c0b07020604150801090b1009031403130b0a08060306041a04080f0a020a03020601080a020f060901030207150b09 72
    0x41c04051801c1408106801104010b00180d00801c2d08004411007004407418154120019000c03600c4030024241a03d4413021010300000b00022140041140c0b48c0c1c406024200c98100030010790f0b80700c00004000c0d0a05803003451080c244a8410602550a800103c9415610154000c003280c50445100b84640014030700b66403041c0c003804005141d0084120500020b51030340d070366000540c1445004021078081414160042032525261281745400100000076290000c1c4042030031100341c030325180b0714800c803c01032840e036103403020004030750f8590740140c0b40c281220340303c00946070780b01030130325981d40c40071607000c0c0200035175031400040041c8842041f03070003a000303c544601d0006c00d00e400c00810303401022128010380c0440011010315a05119140c05044030700003900e15002180c00090f1200c0003a80d24620940001582854a038002d42c100c414155008a16040c1c00c255012a0001030041089490045059400060b0340d00c5400700c0002040c07030b4200c2400614490841203a59490030b66080302c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 497078696 1250 497077446 497077507
    0x6060f030a021c0b0a060b18030c130609050c0f0a0c061d100c0809121b1e010c0318030c030306030212010e0c04022508040306110403020103140c 64
    0x20015031541036000c50f980d040c0081550445102e842c200800c448010071048082c0d1822100348005080c510440f21505158902c1d240c3d403025017030020b401d04401110244e44100c180d040400d4076000340d0001001c480c40800c0030000b135560414285040e1291219030300000c0005c2240d4602d142c0204e0780d0b0203800d07020380b400040900c1039506200c11900805040c01c0590f11802a4031110145405401d00060030343c9011440f900301050110784c1c07007100c008001103c20000ca82b1829000014800000c07941303110341100c2d140d41d00d5661031060807028251884455080280c0b078120280280031792100300f45026029800044191412141e040f070741c6608404040d01d0302000409070f5039640c039001746423540000009003070241d021810719010900108034095030060203103108041000158401100d040c940d0380382032881d02d242001c020b101d940c0000b84500e1030001e220009501050141c005c1c0c0717100786c80410021000d6580c0084c1001c040340c405001100411010700040141302c5054001074a41320361 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 497079946 1250 497078696 497078713
    0x307080c0712050405130605090705160b130203100902100c050c09090309040e0f15330a0504021204060218090c030702010b0a0614031302102102040806060f03 70
    0x480e107280040c0c00100c8000f8001060034812841c000c1c101c1403000b60440020414180380201103900c50b04014506c0d01400004101a1940303054082e903030700000c1e80f0640750040f52400d610866400c440d4801c081e4060710612204d606513031802d200764090650028100104050329080c02c585c00004482d0031916801740c00c7c42c6036010b131510000180a409048061a201d40308807017440b040303881c010b036800c0d5141c0c46020140c10101c4045541d11300d01070b02070403d1840743d654001840000d081e8440804034000d4420004031503620403000c2c0007113a0801c90381140e04541d200c0c200000da0058483d40d841c10041400420009507a07940104518500c500c0c00100030a034200c001000d03003c1c12583c1a0a043c0e000040040b0030354203100d21034030742e0800c40325182c4150030441700401030102d43c1c64984502d203002000c078142100c0c0258801e0442d034020515142503d20800041c1400c04480d25030f150b6460120000120070318034001d60341950b044400801456031030074204040410000b510a806000c0c07a4034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 497081196 1250 497079946 497079953
    0x70809151b0d020315010e04061a0304050f070806010305120306101211040906030b010b1c02070c0312050703030501080706121509060b030f090c010906210e0c0f03070b0307080c07 79
    0x11314800d011000310f2800340f002c0b410024000706030760141140324628026003403103200745114980c1100106010110b40782d5079039143c100d25002c1c05404d031084910811074006154100000c40f14181c0703110f0020b40311600210700503003101c2c0c0425200c26070302c03201d034281c3e0300201c5200700c3c0c00b082d07103119018011403014141021044164403540140d20304945811051050222043d01c00d030041c001414650310703051410b80e501d001106600b1400c240303541c0020351142880052201c5074040c41c0c100850f114410440040038106900c640c0049010a0402c00005903803074010035051308883c00d81d120000f214001012610060505601c8400d032604035880c0429004824812940603080e201c0c07900c1c1d41c0381807040003800c012100404d030320142d6120407506072903079174094110000c9521500341103d21071008140300090100c10203c0b00e407018a40030b844180c03280000340e00c440c0071000380c5200848205150906489800070301502d091010204045180a442006800c0c1c1c00104041da49050070100d07507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 497082446 1250 497081196 497081201
    0x306150903050f0c0d15020702130207030f08010303020601050402070c0b0f13091a100309050f03040f051203181203040b0d050a200d0908070605070809151b0d 70
    0x8850005410480c050040140401c500990071104070000d040c414034550000d4001c0403407407001000d2000d0b003150303c0724909040e01504c1030a6802401d601e4090307542c119040007500b1400f403c1d00060200b08840c540c460060141605070390301540071f010140e0800007480060f60102d1011241c070094680d00240000b1844050042d00904100c921b03510108103402500f044a290410303144035140c8911070602c180c040d50750000801e000e50381c035004c0e410070303e0080e0b008203d500c0c009006c42c02060340d1045050300200c010410394941d0410040701e16110300900503405001d148005480c0e10810801500e07901070081c004184100414840002028110340350440d00580d22803162420003048036406100d1901038542d0110b21420b04010390114071120004003140c94030450140c020001d41061400c4282d0448600d4075041802c941d0b44003036038a003450080c0706c11200d200010301444041808040c002c80c5201e0100300c80392101c0140d40307070005039250b84042c00d040b440c00c4240412003260188481e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 497083696 1250 497082446 497082479
    0x603151005100504060206011511010c08010f060918050a09170414120a0303090615080609010501090c0234080c0a06020102040b04120f0605091b06090a150306 70
    0x94140da4000c0e807a010600800080341e054907814041d090105000e110740c0000d00074110752904c44144103082d81708074155465801302074802070750b50a101054150b203400010b070b54100e5042580390800d69940c1d02049030320802034024406040c5ca840038018449039941c102035041005000000759081095403801d4551141c00c0340b400740c00350007003030801046000c0d000521070b001041d241c86801e601814007654448498010023001c0c165541a03080900809030f001025411a4031031560a142d01d444080d40e079150200c07030b20b442d250308100000c600030046000381c00c00360210f5002000b103103080c6200c1503001c41c10300b20716100b004000d100751003441058803540001400c1c00300140c001028a070090001105c00358205005680c01004200f01c030a0080c0116011202019294145480c2d00e01d043c0c851845029405080282003d0610408210114a810401c0c0c10705010880741c6e862841880741c0c034020101c00552003030307409504002c0381c0403840b0003180201151500003011038880c3d0600715030541e003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 497084946 1250 497083696 497083711
    0x6150b0c060a1802060403021306090507030603020306011e0317090d060204060219023a0812010f030b010501030902010509030106091d03130909050f0f0102070b0c090a0e060315 78
    0x1001e10100c0341c49485800c1c81d5150140f204041c220ba2900451001d01c0b940c48003d0107408034403001b0106101c4c55004402801068006000f40d00300014020003529103804107921a00940c000000c2a5400100185c02c0c0e210914958001c0783ca5a03e951550b00404d80a0010000040040d07501540e6101c4040c80c0c100e00c501d40040c2c88a04042c0024900303d2100702e007020740084641914003581c0c4804c0c0c0f1110081c0f103d28080b0010000e44c5071414092004000805090509800034041087c08409090b42d161020380d00308191b80c2c1d445145030450250700c0b001e00146080300052003154440d81140c102c0d18018101503107086100d40100f400c442659000d0340030b083d515860603401c02d805405a1904181c03d00065081c403c0b22a107426002c0068820b00c202c1694a541c200c080000600c02144803001c89012307500380c0c0c0c1d1901d0740781c0e0207944200c0040b1040d8010100050784480c410080c1c0b00c404002400443d801810007549252944010301140e91510400d40c4059207100a40480c6104458 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 497086196 1250 497084946 497084953
    0x10c090f051011100911091e0a060f170d05160b070e06030a0b0405060f0916020a05060c0a0201181a0601031b0518270703060906060e0f10020a06150b0c 67
    0xa0034828450946220700521a96403a1f042c00071800c17000140000c2c445840e581c40700d5980b2003240c4070006007a5a84003403d031b0040d030100000e540540340c00c020101071041044d140301980825040301c441c8541101c0304080c9000e518601c001c1500c00c01c40356440302c6582001001385c40300400080c0c035a041210307420001350311a10388501500f014090a42c1008050f00c0104005001100241425100828104c200d400c10f030414183c00c5d01c00c01000b04103d8000099880c4e90510703040010f45907011050010140d801c0050b1100720402d03020081c5d811a03006507505007030415005500203c00405441c1c41e04068039460b10700c24000c410400248042400d844603680d0340e40d02204500c0e401c04801499110b085014510082c0b520000b910001c24031035452030700e000d5079400710281d0083c041da8111401c1286009004501242c1200b1000c90040084070b0403100100c2d80c40420600914188140c00143c104040f51000507500d5005860b4126420ba0006038075600c501c40401e06401020300c01c00b1550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 497087446 1250 497086196 497086211
    0x1c0525030e0102011107061a0913050c0109030f03080a0f0f0c120902090f040302100515090a0606020c010e0607050d0315091104060f0e040e0f010c090f05101110 71
    0x1504000300c00140d010a000a01042c1c0301d5141c0a9014021174902611240d160340e02c0440b013000c808401d1000c12001403040c1150309100c4c40100510b14002c070201d038bc0348140c0c0c0312243c256004400c0c0e94122075110544181440c800d030740403550045d01801c0350703010646a00b0010303006100380c000c10b00052081c40002a6200070200c00602c3d01040466030018a4a845c800e0340141c0c680c11010ba6009011001c540000d44803031030b0813454200103400540505141c68180102030b441c000e0040c3d5104811034a0018548800310714400f1528540325510140c4c4c00f80076034003015409135080c0011700300014441401c010340c5864050620790b0f07244452002035590361031010f5042c9440e00c42c03006810301c00010025820442c1440d00700d4801c0d401424148510002248011072065082100d0440c0280c42030045400d606c3c4456581c290244554805500b0018218140741c424014103040f900b503901d1031040c80d071a00c42800800c140b28003048081040550b91070800c030f202042501542000703140c0020b102d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 497088696 1250 497087446 497087453
    0x5011b030e011406100806010c200901060e01020601030212100f0203060319031b02040605100f1412010e0c0f030f09100b060d0b0402040825050d051c0525 68
    0x1202800c3d10045101101000c2c028507841e0613030840a986a18100b030680c0e500d4200046c0d480100c1020024a2286c03851100450030718051b4104804103000d541c4408140d8a0301c60a90318440040740660060340b00c0c000410252800b0b1714030300d011050000c00d5071240c442004040c02640d400c0f0401d2540c0980000522850303003010407a070064144005243c0a61004580c0d00402408801070701c40220308643e2105000e540d29948813000a05005003042a03041d0110307405040f8401c3e01503040080f0b2040c4c1c0b400c68002d690b00c401c0b0b0300310180d0001c0081c9141e0a096140d4403007800a400c111038410305106001c07810007203c0c01513001d9004000094810714242c0c0003145064402c1592000d03183c01c0c00c013010340e40d880f94415140d500c1c40c0720001045440c15440401e00a015550040c11127100700c062000500d074075110084000c0c03a40303582044000f6211424058084890b200c000e0440c0d0082904401800d4291100c0008908914109250094584c5440d089901000f8504040843d09a40c0400c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 497089946 1250 497088696 497088701
    0x9050108041b08030f0705150c032418040201020c04020c1504140105040c0f0f0b030609060d050102041d0f040c03080705150708010e070e09070e0105090d0b011d0105100c05011b030e01 81
    0x1039100c80d062682c541c27901c0300754080d0074003028082000307070030012440003005594981048000800504400e208500071050129072100507641a405800340d0413101449052078003c580000403690010050100300081c0055a000010001d440c0502c0300b40d29604800c1c028051140594045e1095010342810405a00d1480d0200d40c00200824541f44c4204900c0d02d40e01c00b6681d10010484285074940c0d5500f0204e960041c602c000141154030006002c40c0d612030000d0345606001403d0221032296031080502c01c00c042c4191409400c4c0d6000725400c00010707243c800200080351241043e595103d44840c0270f00701515042d600b80021400080c01400a2081883e40c503501c10303802d191901d0500000d901090301070f9030146c01c420420096401104650740602d045500c90040900461480990344c181084910004c1c044c00001d02c1c00e0720302c01c4e8602c041e03c40724103050f5140106400c40c2a00a0b040c00d07140c8140c09801281c05540320000180204040050441101101d80b40407466900004d6010f08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 497091196 1250 497089946 497089963
    0x20310090e0a0609020609041518110708030c070b01030f11041802090601180f0807080f0c06130305010905100f11040315180302031909050108041b08030f0705 70
    0x8031880e110380008400c200164140d2401d4104070300013031070269030002c00c00b0f07072159111194000d81411020241d41c550407890341c044502075142140282c070070500040a0700c100d281c00c43c9040e501400400302003602d910080d5001b818070700703070545000d18035560f814001d1802d90040d120382400240700d806214101408090044044408100200c0103015080201c80d901101a004402c01030005100c1d174024100d80c03506140d041c100c040b403c1c0e41c81c082c3c00e17160122402041c10310300901c00006406100096030103207007020307200503000e6110304905120301030b0000000303002090f013422400404950203100c0c560701c1034000c1c3c005d000e09c036000d1003000e4150f40c000d0382e5841003e0f1420101650442104080e00e00743d035030110010086076064050390002c1c00c034280c018980f80406104c0c407002c050300080104011040030f90007041c041260070080c0e8040d000b503c2045c1c0410705c11400500015460200400c5420008203800342068403110090301d0740d00115040910b81c43d00080000511504100201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 497092446 1250 497091196 497091209
    0x1504030204150b0a03050c092133100f082109010c0212150c0406080f130201051c0c09050906030303040519030e1009060e0301050c0a0c2301020310 65
    0x112034915080390360f5110310071044843d04059641d400324030a0106001122920180102400f0f800c2500940c190f8035070b4901c0100f401a849203414903075800c480da0310610400e583c90b410607070443d50035001c4c00349a440c2c0142201584641410045040d00108121002808140d8000d004002c2841000e0b9403114401042802e200801d00c040c0110360390142d207105400d42c0c15038051105c1561810b8482c9010102c014403507403180700320b0400132041c04a10182c0110303480c07551404c0383c0f51901e80001c0e40640041c0d034500c508400c982d20190155010f1700084c40300d21180c2941c4020021114007a400700c90003880500700040182100700800d02d030070a04140c0294045001d589141032a5907015503414614031624072843d4250030706824107006420400a0380070282000100c0001d9440013404900701d4043c1802007090210a4401410144603003441003140c0301e0b01034a485040141694401c0b130040c0222034808c203000103040e0b14940961045250207a840025803a81400c0386000c04d20b40d52500041e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 497093696 1250 497092446 497092481
    0x7060b041503051902010903050106060206041704080622050d030507020f3c06010b030f0f040506070302030c090402130302010e3f1504050105070c020105030115030603021504030204 80
    0x900203e40e0100e000100009804500140c000c403500c01a64000f00c5a40003418551914200180c900d8010840354401c80c410200b603d030300481c09078030b1040c50080340210601940080000b030300d01400c04c0006507508403036403400c1c25015001d5860503d003400e5020010002500c0d00c0620000780d07010031188810014100c040c0502a070f0316100180300131802030f481d150b80708011820520007400c03c4000454132103a8025100781e5a140c0c105019a0752096507071140e02d10314680020201110b43d24451b001d198050043c04040c0ca6204048002e0340015000d01c480e000100150361399643e5520041a080d07421ba40041c00b4246540000b401461201d060607005085074001d0365010400004440c040300c5032855007100140d03800289440c2c821200700040001d05c03035014440381c03c1d6407001f501c41c0302e0342c8038000a00c0195220300d0b08440211400c0402808035074148014001d031b07204030000091001482c640040d01a6880d0001844440c10340c00030320004c10001002d205504080c01100400300f03100222 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 497094946 1250 497093696 497093699
    0x22050301060b0f1e0408010501050a09050702190201091d061503090d14070b0403030b100302040815061804030807080f0610050703090506131805060d02012307060b0415 74
    0x412615101d2003454600390107002818610025a013003142e10881c020b800d07256211901d503492180200303002e01a140c418841c00c00d00042450366806640d224a0440e80500108100c452056106444280040381030105000020032841d07509042e103a600100c2d2080c41c0321a0900c8010700140c04d01c8410410038080082080002071200000c40383d02102d014900106108110305a00c505030184c002c0041202d0055401d0101f4554950801001903030100e400780c00c451000d803000d40c1288114440c0c1f581d01d800007442c80d102c1c1c070101001e40d544080c7c0540340c0712598645404003058200c040f80e0840104580c1e00a02691940c010055544954070752001d814a061540001d02540c0c062840401080400101c1404051154800307000030b01000d01071640b5034140003845c2602d480207024040e06401c1200d81403036001003d00036213024200180c0000c000494070740044a000c0c904070750600d0720340340c4400d1803c142e11480d001445858003605002034900c0400d400c00080e604511000c40000941200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 497096196 1250 497094946 497094959
    0x7060e0c0a052707030c0e0d11040b0312280f090902030c1605100c031509050c0f0a031b050319020d0b03030d1a0a030507050607060905032205030106 66
    0xd50003500c0c42141c10040008040003d06040c1c1107141c010341c650304011050140140d09904018240700194941d07104685032a01482484000a10040c2514002415289080c10550b006100007030700941a0b404915080340905040c0c3d00140c203091000c105828824040d103800c000300e100746280c0389800d041009007101c0c0104421101d0140b12403e50307000020a0140c4031400881d042402a6151000e440306c503030801a89405600488840c0b01e07003441c00290303105202e0f20448440c101d2807020040c46504020140c80200707001000e89001d11400c00120380c0b070124010182810044607900495041c00315014801005800b120711010b0000600a112400d510341c45040000c04e4080001a2140031a05c0c00002030504e08401e2a010300000608040c020229013040b40004100c40c500c0019007800b0040c0040b0200708c0c40080c055410100781481ba40c0f0300503000b00303481c0c3d00510300420011b02c252941c0c0d00b15800300d070003900300c003000c0d1a5054000300e07081404801481d08400800c142850500d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 497097446 1250 497096196 497096209
    0x60409060911090c210604020d0c020c090c09030a14011e020d1a0108041b050a0303030f110a050a141b030702030607051602010c15020f0a03060f0506090d03140d0207060e0c 76
    0x130515401000c60030001ea213a1f21750342e058400300041d214051000c201c840034013a40741c2d6401c24802e40650035183c00111744a0820048a00c1a00c01030001e101c880b0440d00d4a0403240b10981e1200110754851500192588070304115044bc86e613a4500180c0e102d049100050840c1d001880c00f203401d625051072007055030f030040f4090340d03c140c02c044d0303446202800104c9044401d01d25007040d1360082a502d404030505606034172855620031030702c500308826484c0b03403000d00550007005080c000148040006044a5214824071200d026081c20014100140e2648440300c0c40c01114000000394008190300d419440c04000c80358000752103080603440c06121040707058070b172440d03094068188840046c041d003c000001d052007888400e04075085440d500c10400120041c0e0151303000c500000d04001011504c04030b0480c210703084480060186282410001c24800654887d030026000d1100c0300c4056542d00c2d120348014850803211a20040e5160924a030000459414204038880c0358055501250603071280d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 497098696 1250 497097446 497097487
    0x100c020d11160b03040f060203090115080a081b0106050409140606010f270305060f04030f0206090703151b09060909020c070504021b480405060409060911090c 70
    0x20f880240ea079641c0c50404400002c60140024285440007040102c80031f010340c001d9007045e20004210f840d40c0c0d610080c661b580d0711482e1001e0b10020040045160750754010940c0e88400c07028000102c2c003640e03504001001c5520810003503e25842040901c00c1d228000e00c131071a885182400d101c1010546410b00904101d030701112040c800403040c1c812600c2242c0043d41c100155444001c58035146800202e50a41d0701c8155821400301d000c031104034406074004501644601d81030b0f001001c142d07107036489100010740b04102054200e507441c2d0442c20810000b1a000e40c1c82c0a007a181c080803940380c4003004042014503030044014920504c82e042c00d60b1804510401100c00848000d6210311040300c035011110052110110984506030300c80808210000c060607050b100c0c0907200341392541c1549140d400c00c40c8808000c214184c044c2200e0614074040c2d00c0a0f40081001c3c00028280750b0554800c801c440f0026006d4640502208030075030189041c449656006240da0a014180b801c000380d00760928203032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 497099946 1250 497098696 497098709
    0x71101021c0b030a0204020f070b071d0103200a022107020a09090203011401140114030f0f040309170f06070309050a030309020609040609020702010f030506031b03100c020d1116 78
    0x82e14440b6a290740e040180900c1650010002c56070741000d0002c800c0c00d684146c03000c581c0300b500400001c100c240181900071000084a480080070115140118014541480c880080d2002c07583c0c034099000101e0b01070500c1200e190000c06c1c480d0415080d0342c030741440c01e840000580904106000040e150754112100701c8600e13070b00105500c1080c0c0300082c050082400c001c484000001d0001683c00080e407500742003a1002c3e25175040201d10188140c0d8907110448000d40320520240200700701d10303010a0980c0c1c0c000d01030718014031030523240c40030360010242c40c1006030380c181d128100d541c014400c28402070381c00111a045c20052000555655500c1d0075071014054149a52900b0b40015519600111003510304c000300300300711094641c10000025000044261300003a1062004100f050007449a18011400203009058400010401d41d2015110001103605801800c8a144050540f8043d00000d849203402600d00c207030007410001d00c0c200004281a10030341c0500c079504038043c480707050202550007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 497101196 1250 497099946 497099951
    0x10b01020723060f12060402040509040f020d1203020d05010f06020d0f030b1305070e0906030c0f1903030807120203190c0e0a030b0633090307090e06071101021c 71
    0x30314456500441c1c5540102030340042000400c1d815840d8400002d01c85e02981980084c900d4440f01d060004038041d03030080a4019032813101060225150303000300c5002a10061041c8180819695130300031501d01010b9000c08250080703560705214520b801500c0c094155546468000b901d0304200039a2107020a1410f0140000e0192001c405442600400d03420203018042420320b610400f0458000c007000c80d64100050604040c0d29081d1a15040d1203014401c018000e0110007460010801c4800640e41869805a2141c03020072500e0614600e0000450003a12140001d10b41500702401e140c03c0c40d442c8505a9204104000221003000704100790a0b2004400288040190405450220010f040554016a118000020840d03240c60040c410b40d401c0e02d4900e0087c0b0003045448801403a0b48100303074050224031100c0f0305d0040b1030300544181e403802801c031403804d84d440907403d04807009845a00e020750010020003690350f800041000e07414010600840c90031001c0060030000e0001c00d100080d0442c2c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 497102446 1250 497101196 497101229
    0x702060703081e0f0708091902150714030a08010e0c03010306200d05160216031b1a03010e0c0a0c24060e06040e16030b0c0409022208010b010207 64
    0x15641c150000c0f22010308220400d01e8141107000c091510021203592000030010300c00a24000c0b00450440c1070460200d22180380441240c0c00c1184010141c071800b03002d100184084030110b0340c40d600c0c11910007134403009143d944000c080000d180321416001964481410f100344154511101c0440341100d0b0800400034003034034940900c00f240724121038440ba0441011038840320820481d40024001c010074080140783d01889001070b81c4581200720004000e100c620b80400c0442c13810a070202c1a100c403000403071707540d03901c40555548800d800071142940b140f020006200c004011000c80741c0200c00f2034561400c2c080078140c01031080d20107a100400d020a442d081d40d2041e00c10700324400609a0099060200e030b40c443d07545d0403203040102c5405105504060500b4000200414600b0b004100011745680c46419034071000c02c0c13014068080d00c00904108800031b400982880031b81a44076820b403c000b41c410100e014080c5d006499040b80d02d0701d914001c41c880c400d81c0c0001e007003030496000030385032948403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 497103696 1250 497102446 497102461
    0x91c0b0c07020f0d050d11060621010e01060e010e0a051302120111180a0e010807061b02030d0918050601020d0c050106121103060117120d0b031204050411070206070308 74
    0x114920f00d0b1550b00052040040403c21502041180e914600d9a45010300300c856502e2655032003105507000394000c8016450169140c2e80149400e400312200b8001181c4010000105400c44d8010742c014000d41e140300006000840000d21025004412600180054145900a88040a517050000388a029a04a80c0101d0b000a40001840e2121001d01c075844007003000f54921140724440c4035030320500b192180802c01768081015141a03514500c020300060b420080305644904e54080742c81301c4840c00300412001a502080805601c249940d240042a40341014895112290080c001170703460801c800c00c5000d903400150b4555030045840d01422a030001e003002da004013465001402094007515a041c24403206080303a1109490a500310780039603a13608500a0202e5170351944100d250402c0301074800c0464604050140e50b00245000680b020451000900c1e03c490015513501924000c038041145180920601c049000586510392400410384e0000c0d44510541c0c50007418000014045040c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 497104946 1250 497103696 497103709
    0x608090c10030e1e01050709080604111210050403170c09151c02070c1a0304050c0105071403030a09030909020c070909060b0a1806090b090f180a0305091c0b0c0702 72
    0xf07000202800008400c40368290302d006e048212040c0700030072074034000011000000100c091065070000346021103a42c50360200301030084031030700f07521503886800d20005d801509441483c2c000c6110391221000c0e0040d000c219201d014008100002d1080c0921011007952641c448061012a0844103a17a441064808071030a400c954015440707154408074030b00080010541c1070700c05407809244a909030390b0380b0540d070784414401290001d2441c2c00400a03600654000c0c00684080d900c9007694409012001d8140b03880c507081128011580d07a01c856848040c990004040c60140940c804107600e03140d0303440e80450359800345109a40100c0d41d0703200a1810303c6019400240524401011120b0b203580d038880031180903613465518803069141650000f00c9000f54890b01c21144400b801803103c554a03640403c1e40e07404000c00c0f801080340c40080c02e006005041c81004007940c402d403038054940034540180a0049848512900e00d02c0d4646126004500a001d00030750140095440d1581c40c4a1807020414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 497106196 1250 497104946 497104963
    0x903030a0818011401090b0f031e011103040302010903090e240d020306090a0b0a0605090403080601110708070317030c0316110109060b12010c211509060608090c10030e 74
    0x410f510b8242e02c1c1072001505064241280d86181040c420b009044041000203800c13104603d600d41e2010340303040ea1a8040304410580c1075000400000e034000310405d07001003603004880441c011707503561841d8420103407c00706080103014400311161051810007100d1106050074902c0c501c00800340c071101c540a0341c520f1003080c07890360b0150aa910740e0030401a03c81c8d403880041c0040307038000360980026802140c03a00ca00c00865030018a09180e507115600d0540d1070160140150b810050b410003850f0461604000d900024015240100842c1e499400d200303000004039619104801010001d008214000784256a04150901c042410452383e406082c3c45107400d11260202a5080c000500305104865116814410341500d030783c400c14000d0f0136560300300c0309084100c2012580742a10071449841c2a5425074803120480d1000440500841c002c41120710154002d5402e41e4842c039090043d07944c084502e542110301c4400030403035540d540300041c00207016044603d0405668071030180341e41790104090007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 497107446 1250 497106196 497106241
    0x1e040204030c0e070c020d02010c03030e0a0b07030c2c0a0e010e040c0e040b0a050901021c050a2004181b1107050102030a121a091305120903030a08 65
    0x40d5160350702c2c501a07070200e80c1849002540c43d8010006913106000711008a003282d40282044c100c42d91590040d5079008175030074164101952181e0301d100c0c14008000c240082402445600880d01e0940c40003402d4031041c08001c0104180041e00c4052000c1c4140b800d851340c0fa41034480036a05803550b0226a1403a0302d039200241c2c0d00e0343c401c000030b0800240c031001781c0140d0044000507a007a8036284405e945a0040c1c4005000b201150000741e1800c1042e030110f6040b040c908009441c20101d0415041c1082100e094240742ca81d40f00d0034003103901800c3c440c8286030760076207410040c40c040e201c5102c03445c0e00507071180c002035034101003072443d500d000f5030304c001c90816000c64180561804404000c0100c0c50f40003000040d03110354440815150700002c00d8803011085a030382c4406407140c5108140240c42e45070078802c7c101c604c01e2000c40540d81c404003214401c0b03061980c100050709180c10b1051404044081c40800c11100300640c01407900c0101c11a4460145030601548507101c1c04021080842c030001040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 497108696 1250 497107446 497107451
    0xc090e0c0d0b01180e0c101b110a15080a09030e0d0503071511040b07082a070f050d0b1003050f030a020c040c05090904111c030225051e04 61
    0x62003001000030a480c10303a489100318513200100d40d0703500c01c111411520600b00700da04c50201e500040c60082c840c1c2180401c1c030b141245030600880c6c1512001555420111626013002c9105000e50400850310401400d078044000c11210146001629102d0301501085129031244610750a040c0100c00070343d5401c49c081c0c0504072130802c40c1485500c2790800c0800704c0300443c4444140f03880d00c5807401080381b2030781601e811034645490814407271070360b5110710310450340c50300148201d0910f110800b1048000c824410143c010301c022140d44682061100e820802034480701d00d10602040c0c03103a0510040d0254024002c2100d40c6600080650061036940000c0c02441144222034180101102908200340c2580840707010b80007a0040000b602c0204442c0000210140030403101807070611384031a003143c06140045260400138001c501d490381c1d0b019103041409150300402d410150b0402c40e038400d1152038810080388021403d400180302c4d03618410640300d0114a0001440d2040c44a421880010000c008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 497109946 1250 497108696 497108719
    0x1009060f0c051e0d020c01080105061e120105180c0a03050a0f060602030d0b0901051f210614101e020c220507090b040303050a0c060e060f0a090c090e0c 67
    0x100018041510f07180c030103601070104e118210900000d400f80c0988016100c0040340c0e82441c0070f000d91504032203d422840c80c4809248260051607c0080c042d01a94420206240d8100400e00845004039103054207800302c03030010000803002c100151411a8194a030100d007580345c0c841c1c06400381200284000f0210700d40000080c3c0590004010100c2840f40b0301c081c0506402202003000c160002d2182c241c0140d071400490504403d01c1301d0104c01c0c42e03c20b08140484c0303d442d031600d1481011f010130b81c4415580d1502d0512680821508851000204a881e070005845140b80105401001006a102c807049800307034400050091050707440020000d0406c02c20841c0d0258a00d240391100c1c3d4184640d6031921001c914424414440c81c8140d0b281c1060152070145507a80464003a4425034440b03003040f400104520008825000390720764584080e00a020301e04103019010354001c07010300300b030120501c1c041c4480c1c0010100015007040f40e0044000040c40f02902d034a0500b4445110f202e85c0c1d018400281 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 497111196 1250 497109946 497109973
    0x5240a030f110c07090e01020c15060901150e041e02070f060b0102060103050a030c050120180613030b100e0f01090b0108060a0302120a02060c0102040608061009060f0c05 75
    0x407080712514001802400c8151808070400e106100d40003006400c080828410b9210a0300002e04242020000500d0102e80104803424400c00f1920030360f0118919050188925080d11441d01404403111301f1800e00c4c83c0000b007e41505200c82d48140145e49440c807205401001c00d0400880700c07401c0c0d07010740d030b0b98034140b4014001c023150035421030704c1a14215081d01c09500c001444c5060f41d07800302c0144804081911705844804074118125203540d2a154003c00031600c0114000112100c489800c0d02c030184a000020300000030030155000713010900c0440303e103000c440d1281741202e030455604102e07078907414081e00b40319200c1d410515820b0402c034180700400c4a03c0304064100c51200c0005c01c65403014000448035140281c644650250f0054000e002516062044c2c20000c011201100d182d11065804a44c0c20703009441c1d01c50341a54049810090142c006248541c843c004036030040c03000e14515030141001c811402400d003008401c008031609a03009580b80f030001504070b0300710392040b600c404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 497112446 1250 497111196 497111201
    0x20d09060c1b0f030515070e1e1f0f031109010f1b051c1704150b04090803100b0c070e10080a08040f091b081302090901091a0f0105240a03 61
    0x3c42120a031040e110300400c0740c000d0286c3d16000f107038030350b441d0300c0080e020030208522142072085510905417450000c1d203c1d5980c00c00702040d04904107035411442c20010b032010b0812524199840141402c000800300c80c110712b4002c844c8500e80c2403d240f44081c00c111402c07503503040c0c2d0400744c2d03c0110064040304180100001d990440f14a065440b440f080005101155a0030002030840705071907030040131400080e41e00021104503100c0c0b410009400288000140c15078200002c2603c80f040008180180e4140c3d4505240140c4502c104051a10b020070740182d98440451166a290141c140081145514118951402016a0000c5a40c1d03030310715007811181940244034400e1101122000010640700c180118140d0031345500042c40c00000d0620291079a030320041040843c10004500b80c030050303840e101c916005031131500c000501305c4541c4c9452511006061300060314902486c00f0007038040003c01e803903419582c081d00d203141001d2002c040401c28400b801c04014081e500071400000d91941503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 497113696 1250 497112446 497112449
    0x81204031704060915051218010506030111090f032104090501050108130f02060d11040e0105121c1202031503060109180206090604050a0e0a0c020d09060c1b0f 70
    0x20122000705916000034441c1a100714810030001c80d410020801c051010400340d000b081c03590303051251a2440a4800032040402101d6820412500304016900c009091041e0380e1300c248103030002c1001411034003a04949009112505128004001c1d030081d0940303007801040d400030540304095514000c0c0c4c070f840d040d841c1c101c4c0c010082068640000051250700c507911160040101c1c90301d0071040400703607d0702d42800e200504103907040310080017640c40c1e2002500c03680703000104003a80c2c0b540b16800c0141a0100c0c1078180e010f24441d818002c0c1d0703490100c0c40030840305080b407a40c0040c2c107000c181740501070310f1f11940803280701d40d00c41c408000c0098030400201003c118040807000c0c0c400980e282d5444800301d580030f1000e9480011b501d0078071801820000000e000c00c210081889083c2952640000c1208425401c40d065124210701440751444550081104206440c0091311401d00c0002c3c0080100e4001e128100400c0191244034080c454000c1c02c0c140d40c605a0310748141318503295192440c04003143e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 497114946 1250 497113696 497113703
    0xa061205090a080d0c090f080304061107030809190504051e13210504051c0b0a0207050604410d0903231002030a0614030c03060103031808120403 64
    0x3400006040101c0102e41420001d40c085802820b0080300c20b003150041c8044032002043c45070400001c07031100015001c200080040500030750340e031403d04c1c0004000c80315142504045500250060000420b5242038070300a5609813500b4813019104258500d641c1803070b5100f030b0380003407030074007030000d0801400b00d8a0450148140b41840b55142d03000d03034180403036410318090715400708100070810100b81c4a0003496200681e1500d24101a2110001580d00380a8549808621036a074601420000c2e84281150b0104085e00c0c11420121540c031101d44411000740000c20729040803d040c0c0000385105c1060101da03800c00600fa05070500d0846101c15100e90340d54110f02441200d40c082c034814032501450f415243c0c4007810000403004005180140d0301005d1005009024004566004c00390a00c0036620400041601149080c034048098a106044101c030b28020340203034004445540780001c1e504d046990528003660704600044440c01c400c51682c100b9106402815160340680c00da420282c41500e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 497116196 1250 497114946 497114951
    0x901030c121a0a080d080a02090a1703311202061605010501030209090a080d051e0702070608060a0e04120e0301180213020a0c121e03230c0f16020a0612 67
    0x468039459682d030408085e802c40061010300c0092050103403034000c2c15200c000036101280e19a1550980c2c6202e9490f070000c10b10340c1e80301046c0c20507026806c1c03104488030b6070325407086043c82031000140c0f0b110003214090043c8020194401c0e80854540801321b8010548881c61002040f20794503000c1d010700383c2807006910903c101d1000c02e1980c14042989124141c1c41020245400c440c21138403006000b000f010f06010380b85200c03649040a0910300c10134481c050175806040c0190401c80050103030240585554001c0b55003000602280340090003003508a900000e810001d5118800119080307100c08070754035015420300d1102c3e0100b0f501010300d28405407007201e1044041c0300d68141d06040740100541580002e8580300843c0101e190280f00c2030003035099203450315910b00d951040100325407004800380002691400b01c44103003159208038a42a80c0513a410200c18140a07003000c0e0140911444c03403040b030b040060100841c2400308154140658050241c11201d0381d6094040c2800e00c010101886060 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 497117446 1250 497116196 497116199
    0x903052a010e03030c0714070504241d04150b270109050c160f02060301030b011d091c030209040e010b090112030903080a26061201110901030c121a0a 66
    0x40d0120640341709041001c90241003000c0b035110348015003800003c00d00c460180720808101c07503d03180501e00060304942c0e140c0900e0048143d0070900071070568041203d00824404d00b040d01a0111310042c1c1241d048030290381c103c0c00800c0c0d50301c0140401600642d03c40d41030150110882a80e51180c2c6d13202d290002420303042d0b0b82e41c0030b141050702c4d0112050001540c0801030310440340004041c4614850145030301c04002e030550350219180ba4800e0b0416501c4c0d02d000001008495070310603840302c0450400da40f288035420503403441607540c0d09014500c08050002c410140303400307209030b040d1103401c40024410300901944401b0035000346084038100d8001c126001c000310b00c2010050300b406801d0f516640340f002c1c0341c2c9141c4071103450b90403648412041050000c200b5408010321003141005034040c884482143c2401d17410816440300c445200b94481e41859514101c000d00e200070365007845001c1c00d020803900c1a280080318880b40400f415140145007184519125100062040388100c00b07444e194011ba = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 497118696 1250 497117446 497117471
    0x19050d11010501080d0807020703060e030d111804110708072001050a0806100903020d03110c0d0b040f0314040b030709050603060d030c02041d030c0615090a0903052a01 74
    0x200e800f4081d18010345d01c00c4080c3c0e5000b0b440369a100381c0c4085948165450300e070700c9580b01e81c1903403200004080b01d50700200b60b0080e070441e14412a25207803070102c44d180c41c010200e91040403246003008401d105a5550540c40001144035040b03a04140e400034003683c1c0c9511500d051081c0d0180f0f6061640340704030250040c075403940a9811600340300c0d0552640d240d1540d580081080c402080c90f0824104050300200200503111030855140c464403076103a2800003041211600e1031b0a60408403940b20740c0740d04a500000c2025582e0303060b0882d400034100606072480b03040c1a40c000c044440e22012089000400041c64602d09001e540281c226584400965645104014003804240d8219a0140c01c81d042d26002034082c0e58a59165803010740042040b00441e10007010703404003409201500c0e04001031500400600344100e80e0f20140640641c154100541d001c1f600741d4400134030300514140e40c1c2c00c6810500d4041ea099901c02c0c43c0060304182c0343c1064052040c250004901030068030f609200010615 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 497119946 1250 497118696 497118701
    0x31903050406320a110a0e010806010816030504110d0c0311040908160611030c0a03060f06080118090c060504061805090a09060204050604090203100603090b07050a0219050d1101 78
    0x45800b1401990140c1c3c3d4000725000c444100905002030740e50340d6529192a00d803041c0082c110458040e191282c4a5032007900140c201c00300104002d0402030031004004082c160600503103045d4000e0b107800030309a07403240350840c1b40600051416500090b000b0102e0200407079103601c00240da101e1014001c90030151070030700090390000c45004102ca1014031100545141043c170b0f01c45054011540403442c020703101e041d0701040d80b0035030350720162150000d034100c0c01582602505009003980e124a056261030010700414000f018001c81c04640c041e20000c8041c4d58442e04a840200d400444407420190380e480e0142480d8054460b2901003420301c504d1803042e03440740c10304108442c4080e200c8600c0c1d0703545020b0f00c00101401c0c84204c43c060303428440403480362559006000540b40d10940140d90b03003000e1015518050550340610101030a00c0d2840e8001340812040641158190400e152034210702d02040c1c0c01c042400216a2504009001138024000005405d0043c2249519044522201c4608181c02d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 497121196 1250 497119946 497119991
    0x12010509190c140102190b0114010c0804030f080409021309050a0203160e12100e0f030c1504110303031e01080c180c16080702040c05040303080a0c02031903050406 72
    0x240340040b1000c02c100595000300d405041c2c41441681c0011a50080341ca0000240c0e000c1540c070303141d40c0c000602454160004c0d0b10048013003400c0201c40201140d1381c07036040d1300c2580001481304ca4604034450406c0041c200f51406010001019511000200a068070910541c41142d071880d09090204821005078400c990040b0580c5040008180710a5410348000c04294440d58208500e99907007c000d420902c001c4240c050b01a074040342c09110071121526100c075008040d81c5a41081018448412000a41003145d180080703004071036607641d00381000c403201d0812860340c15010000070000c948560b0b04011414010f041c41050050741c0341c6031040e503140303030032406150032141c46202c07052a182c02c1c800140d8014042d094943c41c00020311001415681c100c40101e60008000c42c90904503d4140500e1824070381c20f02c2e1841c02c192070754038000c00c80b0401914995500b55504c0c91071030218400c0c011600c1d120a6040d170038000d0b51016500400030502110152030036444c202824200c20905074030f914 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 497122302 1106 497121196 497121203
    0x319050c0c070f051305310f08130803210630011406011218050303100e0609010605070209070215130614040519020a051201050919 58
    0xc4d2103000341040d0f2405041c030007004400540c0d03620a22544580c08000303007000c050038640c0c00a000e20407d01408c0104280e00b0380b020300444a008107001800070811814040e941c20300b55889011b1812805080021540c0c180c110500d0741610075049800180381141050142c800109a81841b0000c0c10740401008140f0100c10303801e00c61050a406200138108141c648100020140040704002c100302c41e07540e02200d81e034004507185281c0038030740c0030f41106e40c1c9082610140e681030440d0b201e02ca01003c071610020340ea40c00e012001c00d040703d203a901d6884c1010180c2e0301708a0b540350000d00c070400314850382c0c00c3c0c080602d0301300403e9800f43d41c952180e4900d00c001c0d400d141d0242e9071a14048041002140e040c4000114000f035641c5480d078241400700d06c0c08266200103900710521368030099000042030f00e6126101810351185000e840900102c91445030f483d0361480d6886518100603 = true := by decide +kernel

theorem cover : BRFrame.Cov 496942446 497122302 := by
  have h0 := BRFrame.cov_init 496942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 496942446 ≤ n) (h2 : n < 497122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
