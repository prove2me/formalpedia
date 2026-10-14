-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2554
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:03:41.091015+00:00
-- url     : https://prove2.me/submissions/37a89f9b-22b9-49f9-8908-4e2928fbac14

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 459172661 ≤ n < 459352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 459173911 1250 459172661 459172663
    0xa0b060d0206030a0c030c0504030b041b0b0414030c03010e0d0311040b16151a04021b0d020d180b0301120201020708010c0c02040b060301060215180109060203070f080903030711 78
    0x2440103a40202483c0da00c1c902080020000c0404c3d442000000b07191451480b2000d00030070880d0183d94001d14580d4840d0340b641d4ad4891400d0840e0364240760320000003000101c0481c8000a007029002c2d0140c0c1017000711981041c1451316080d00d00c0107110340e0400c0c0340311107000004641107180091a00d00840d10305100f25000465200c0ca40c80310700d0b910000112400b02d015404031f076038041445a040d02050107481d81d101c0b000e89031102025855020381081402040ca040c0d4001c11044607050380c890007400b8180750752030a10003401d04220268004820720f55a40e94010103180c2210034020b80d061400d418003000c04100d00050050381452131075031074051305580c002c02c2036600a000c02402440001c60340d990041c03a1842c3c5400c200d0040307050414610030b40c036099050702e0688810764010407080c070b503400344102190409040f120020044c0403802280310b400707014034103d42e0b001d10310260741c034200700340010464141e0b4601c200070844030b8810b024100d1004001c03a9001141480e104070020f2155a180d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 459175161 1250 459173911 459173929
    0x2d0403020307060c0b151507020a0806010f0e070306080a020402180d0c080f3c160303121a0907030b0a0e061c081603090e1014010e01020a0b06 63
    0xc1d505205194000404641c0254506143d5104620b00c0c3e9194a980b21080180010368694179840342108005004200c1504040c05009000801c10310120383c0c0c6100b814201042a04a40000c0c0ea4401c020f000c510b5140503200e070000c140b0700c4e0030000103180180250b2181c0c6a044000d1041d0340004020002e0000c11041c10bd10500080185001c5012031030300c69401d074200c0c0308049250082d40c2c5040450030340842c100602c421242201d84000c0c440c3c8460300241544100c5512550103600c071010340200080001000705212008050442821340c1009403104a4040700c0380d07007140c00c2402203132034120785400404142038252038181454844140c01d9010303001c01d030101500f00c2110a00021951300701d220711402900144c030403003010b49032030502840044140e0f02c05000100c007000380e80071811800c1c040240060003441c007404080d4468240c1d51200301c080c0e0360050000c10200c82484081c2c503480d00181000024280030420058a40021b915081d03401000b03002240008001501c03500d4800720 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 459176411 1250 459175161 459175163
    0xe01020a0b0c07021f0f0912051504050a0b042d0819050f0c070302090f010b0316090e0903030406060e0709090f0b0316090501140f121e010e10022d0403 67
    0x542540d5621001004100c14601441d400005103041ca00040d0340490b4030b40440550b40000180031032b080b1050740405400740103003086506101c0c101c091001700d030f081800c01c3d01aa10441c20002d075045003071b1100b01902c004002620506000c1040d01002030a240119801c030f0043c0445014030030181c1d4800d5445000c0c00e0300402c0064000070340c0c0f42029202140d81d00c00e6030310848040781d031a03e50400e460303c3d440d424040d6100100080000c180080c1800801035005002490032880485c1c0b42c0c1180f0915801c1a1b0300072120341c0c00482441700300325490146034058004442003011a00c0c150000900c085510b108100000f03966242030812036a50f03401c5180140000b40071600680040f1002500e541c160348121511585000b00200318014044000801c04500404071080000b1380d804001c00031014607100625031107164800c1c4140071480004004500d00803000080700c40b80d200805003803000c0034080c50b0a591040014020f818038500b2030202c40400c56120384a0040a525100304511560300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 459177661 1250 459176411 459176449
    0x6092702030c04151d01050a0512070b07140606041119140304081213050a11130905010e0c0916030b0a0b220b0c0a020f0114030c0306010e01020a0b0c0702 68
    0x103000c4c00d00b00700300c0700b010044600902d588990541200c9000e40181e20a00885a0046038082d04028918003641c0341742c200c14015064030b240760740c2d0b088000382c264072440c2c0407190100410544a614207040c004d40d81e1080040d00c0600180262420300e141a1007041c000344010001103240f2032409201e0b81e42c100011610f8002c4990380c0c01c190034041150b40044955404010f0040e00158850078407041901c000f55202000700003601c000d9560403414044400c9c400c0c0c01c030081d01c20480d9600450f029102c4580c7c001d500010b02040700d104001c0c10038194900301405042000140080b41910481004441c4840d01d00041c00c880381800141f03c1c80b00320351121030190742c00b0440382a521408608070741d001c0c1d590305280301025502c0c10f040f00300d8090824080c4090b00030101040160074524904c4003500340500d08602040f5502c00010b4058000b034030b00c8407004501004001035560017042c0c0d5850307402c0c01d00041000c00003503500d40c00040307001000384625000203e46241151203108254003001b0f1116 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 459178911 1250 459177661 459177671
    0x10f050a0902100f0912062901090605090612062202030106032d0e1f02030108190203100f020d060608040c24230a09030606092702030c04 61
    0x12100d54054070070814141d101c2c000091004880318018001c40b401c0e58499110041d01034500310184821240d004000e450168483c42c65001203250113108400a5003082c00c000b00c00c010800004200117400d070030440038080104500e00241d82c0311819201d0400211500c0070280d91200042500d2081d082400e10180c030402d00b081440d0607194020314141c407140c0d0f07801c004080c002c100040000d03003401c1407654403048038090818040001d0708408004c920403070840c1e964120318896640f504501e0b42c2100052940800103008409045c440384105413110500045040c0840e00081d8841041806002000b41c1e1203107c1100b801140e010342c0d000d6021941e04020299680502822100d4226011203e4005661012800c418500307880d045094005008488c0e844001805490070b9401036001e15140d414500180042e121100041170064465990b0b8803140d85507282c0305042d2059600681030403803c00d20a150b040d48007502e100311030500300361504031900131400800e081c58440314a40d40c11074180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 459180161 1250 459178911 459178921
    0x902030106030807061104050d0b060a080d050a020106051e0d0c0b030408040303110a1509031211121302010c0f0201030e100e0d0203040f0e04020307150c030e1f0809010f05 76
    0x44070113407164030302900c000e020f1111000003015042c0b14034000c056200000340d09003004114042c1c0c240f680110003070110901c0c0e5032035480c400e10b0100041001c60000380e0004520303803650360a000d05002444280d0fa21244001071149a005481041e1505401401408440c0c01408401d0701550010180480b4299403800c00b414a940c29900500040d008180101c3c4081d828450004000d2407907508a2071440070b00320108090340141034900c500360204440907041c001c8002440c841c1c1c4a1280032041520b40e41c040760810b140030054010701100c00352646450384030150341c10410b0341091a034040141c002e107030740b0351006034020407844000901c0c9128142e4642060003140d8400d8844003144e2044030b0400040480407a500d00c80c5000340d031f8123106203610821401c09025402c4c2e4201e0320090170360380c0ca1507c0d880c5035541e85084e90520b10001e9120b410107810301d600305080100e88041075072840445540c404600c0f00329600d0f0ba070010100110b81c400a072445000f940407851f84500850300340203600b08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 459181411 1250 459180161 459180173
    0x604030b1017010614180a0518060906090f030a1710030609030e03010f1109040b0d0f05070f0e070f08041b1202190806040b070302090d03021c0216051201090203010603 74
    0xc1c004c05800c000c00f900c0b40c5a0502c1c0a1240800203e1000d11b403e400756201c120700e5000e00f0019010109031008156010001c00d802c0c0f240c1880740100c07400406461810100e45032901d0210040d2121030b0700304005582c90710b90b21140c05404d801c1e904006030001d032220840341803054019800913115038502203c0c0380415a00101d0420186801c40080c08068590784200d0102c91060703e813035917081810401603180b41400d80000c4807518000f0480d0001242c580c4800d0103903011201d0071a10364200d140705100484029000354040c2c41200071204103031805600123041e034503054002d034040c410260001010054a085000032290410b00042c00315079441948981c1180d1070a0300700c3c4902d400100000040f40c10080d0030086030500c1e801041d864455441d004044500900300904068080100000c15150880e40a1318148260300070036407214403040c80d2001f10014003100e421900030b5203030380d440c0041010b40f080a4460845500a1801003c8000f500400308084001e4040d400d02000100b4880d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 459182661 1250 459181411 459181421
    0x1e060f27031306080c0406030e010f0e03131508221202070906140d020d060207060513150c0e01051c050709031403040f170c0301110903100504020604030b101701 71
    0x5540030307050300700c1a15200c042d00c0d880c13800c80b500c001c080c1092004102c880e2003078101500c140c0042d0000680c000c448450542621130b2142510b603203904c0005d0150201c0c8030544454020156041c0ca00c121501011006000c4e02018112a1440039955800107080d039007494140c1ca40c5901011214030701800a80180d140d0881d481100c5005141c00c1b400141802204066071502c04000d03c90104030300300b6400c00c480a03110002c01c0d1039040e4244181400201503103c3c507402110303604540c10101205180a140c0f00c50300014429440381802d00180c00181c11240b04580c054090030041e8550400100c00d1520002030b1101c81400d80c02d08052207100d40e0450040400d41303010b42c08944490b00700a145654910641c030030300c50041c4608000b0010190b004000d0340408178500240c400c0b11241200007820340f000e14510000110b4005000c02041c9030400c054078410013aa98140403903c0d26400241442c011032002403e246040d000140e20b02c0b1a100c480c4025051300100e01c0c41000c40990110b000f02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 459183911 1250 459182661 459182677
    0x2011e0e0102070f0803040b1c020a021c110a060b01050c150709080303010e0c0714031801030506040b031b06070b0408070219050f1002120d09051e060f2703 69
    0x801000000702d00004852180d1307080c1c4512200030b5180c289000c07030700e1f00254840e49042e462101c296490203415441030000703009020195000b000f848045d00942c0c0100f000d000380980510011012800d801c0320b000c542c918506410800000301919100d0050340d480c07241024140b018054031141e00c4c0a00304090300b9601503900d03a514120055214262030b0760300d2000f8000e081380c0e8402c0f040010032140006008290481c4034a1040450094030300c1124950782100c0f2107103807507024a28101209503410310606a00880c00c54081c08921030f004080b0381c841943d120310380860940c045050039151500740c101c1e00c40c81d40c00724201646203070030300704000e440d0420b0004900c00c0c0581c0041d6010703406000791403015070718010600001c880c010000c0000c100d0041d2030000c254025824100680b0702c0920241c907035800c0c17401010a2001e018a0728600700302e070b40c11080d443c2e4a42109404c0c500744001602d140e001d41000d408081a840314126a5480c107034421070300d040c1e11b10fa035001e150a84008000b0308480317 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 459185161 1250 459183911 459183913
    0x60f030b060d080717040b040602010203090f070b0f03040f0516180c2a060203011412071d0910020a030b0306060d0302100207080412030302041d060a030f02011e0e0102 74
    0x1a1501c000304805000100e030058107401c42408070f6008a01c551040c804440c509585140c074040e618426144581c009a00940c0503035400300400c41e0312081071000a001c1c1a5200c080e0180034180421031340c1600a400444108040c04000181044031005048401941000440301004842502c00c50030408501640658055040a40008e86c5550040d41c0d042422501d409403104003002a01060542d440e0040c8a642c201607850710100340c45200450103020810740f080071518210b014458080c4045064455560011004001c031103076802c954604907002c0d69807414035031520202145001c807031800c031421043c80040d080c086643c01d070f4041901340701c0607400d407005070359100c08000e01030f018940003a0260300500410100750b1090b41c014068244a54011400e1a451340e88000d003d0310110320032400301e640003a040c020603030600c4006004002e0382c07000010f20b241003401300354110b54a103c0101462090724525003160300412010b000012807205000ba07405080800405040346c0342051405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 459186411 1250 459185161 459185183
    0x40e07120207150e010209090f01060f0507050601140a0803041d1608072a0b01030303060e0c04260307030e0906030a030e06090102070e070f0216080d03090510060f03 73
    0x110350054001e458040d9009034907000803103c070194500140c02c409080c1c1003e554200000751090b038501e00c12902640303410481182c59810141e020b4a02a00c0481c840d0500c00309128010000f83c000030640d06480710803011180451140000c42c141c01e42071f0b0841c0300503020202e00480c107040c070700b5070310142c1e40d8004044603010348580001400c2040726480200010303005200103138200340101420041400600328400c4045014000c180b0017174041d00301200d56154000c01002415494000c100240808103401c03442e81c10b108405520a110f035100342e00200c09007019010800003101800c011800740d83c8c00b602e0b61110326140c000c043e0180044e0403880741d4184d00c0820b565040004403844000d80c503444130740b11108a2010401140c00a00791681144140c84012600d980e0070340c1da503409a84152619500ca100d800c10182c10142d0720040f0002460105008121301180020480a410401c1c2000a802c80303031400d04070b00703001c00e581611140130b04105c0b0000b2a4120b294609048030f0180d01c020750 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 459187661 1250 459186411 459186437
    0x50910030e01050703020705030a18090903020f010509010b0a1e03140d090b09031f0b040e100c080f0a090606170706020f0109020108040209090a2f012d0201020f040e07 74
    0x803030047d07100c007a180d540b0610140c0a40c90081040a0031032002074801800c060391a01303204151381c001c1c1802c0300140c0240000d0305e400c0f10240916504000480700902c91a4840400715001c1c0030541b141500000e0584041c14100810b225480c016603003001c050040d40072414030266132002c0c44849040002c4d400d9000203100c1200006980d0080346c0100501300300d013110084d0b610440500c0004c020020b40c0d421010440c0c3d500c0f07105840c2e80c2003081010380091000141d0840490f40602040414410340d041042810b984021040381e000c036100b20000390174900746c18132a00804880d080514400c146807105000201d00042100c2101e40540c00c440c900412080094261940131100901007050303c404100103180c040380f003690002e119130840b20103440c075803035403002c036690b5400070080e508211480b03085810200d12075440820080c2899102020181c16a05000365401800f48464900329140303030b4254406e40442c1c003080d00b00210942c55a0301c40400b440300440c20307148480451401c1203490 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 459188911 1250 459187661 459187667
    0xf031b06020c040218060703020a0201140906030106030e010e0d050c01060602010e19030c1703011410080c030a0b15040e0702120706020319020c0604022103090d03050910030e010507 80
    0x20503100030358094040780c4480030900001c0d401000d10008080e54407a420701c11505c90201401c40380f4003d5006051940c61400007503d0010441141e1aa0311010000c140aa8a504040361f04448140ca00012550703048a025401080030b80440036a5006480000468640c003030068124000c2c0300008100f01540c0e00016400c8800f070100350940ad400104810003200221480c803240c0320700070306000960001503600c98038800740004002b0320011022005000000c08007601c41500081589c030100800280301001c0c15400c8002c110400070400080041d64042080d0400c2c10050303006400031440003520152115980c000303020341c40c151786456001500462000030030f000e00c9601d135805a8645005500c80b1070107540014019481c0b541140e1068044a00d940700404420300d466002c1c0499080c184100011000e100c4250075007166560441070501c5400700c100d55040d2022910035000401e5441c041e21503000d943c1d8450350100203c0c540d889540d4042d00503160f50000b070b2008020396a46c6050907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 459190161 1250 459188911 459188963
    0x1308060a091218050f0621040302150f0a2705010516181502030909010308070605010501030c2a050a030f02010e032a0a1b1d010b0708031f0f03 63
    0x2110f1011140404028070709104442e001c4400d000f81400d07260100450317403203034240d0001c00c80d031243c1400f8204010616505120020080d81242c4403084142080c2810740201400500741c000000d644000035020009003022205806c05800b40448010569007841c034002c00d0200c42180b48a648444c180094034800c5c1100d480d414120710a05030018203000202c0206011001200c0c1984020800380505a07140303070240d0b00a503c40c1e140e079980d460052030544151001a8081030515052907c40d4603899003180a40c0b400650303000e030864114400c00e1500354412780404020f4180c2c02241855030034160b0100038108440c52540080c00501d40840c85d25940b4891418010092400344461003d030b04030408000340c8900381081212a20006a16921400c0d4034201901110343c00d0040c0400400b445c0003803003404900c0001181550b0340c074240040c1d03502d00c5131070002401c582d80000028041510b4001880074202904150032078a0b0301e562010500e404503010a54001300b80300c103074030180d030078007040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 459191411 1250 459190161 459190187
    0x7080703031101090c030f1b080c040b03010917091815011d03061f0503030717030c0706050c07020a0e06012c0303130f05120a081308060a0912 63
    0x10a652465520202c8038040c0c070225400d10355480d400258046401d0444480181d07003d1103070084001c51a240c405c04c0b00b00b9400440304a40d409400420102d5408641c000e010b003001d0300c021440544000000c1c0c0100b1a2440003040d1102050741c0d01001c02d140f901402018106950617030110000c0c010015180c001294002c03100301d040381c0762164a52003003140f00c540c0d0b0703840705c100c0388074081150010303041501c1114601030b500800421395210f00d41d000d0512008240036000f4600d000c0325500c0b10b030740804882180c5d0090b407a0001c04a03003545112411140e0f50394112904000c0c03410865040702c42907000c04c0d82648a51040b41c0045070406007540e419000b488161902c42000584c042442d420140401d0045401e60081d000a449514240024240d004058907010103107410180c805a031000c2075000070740600800000f004044400240018281d508000d2450b1203d0990310b1b603403140d136070a4000321242d000c0c2d0018401c90030000e40089250620582da01201000500030440c0c400d00d0b5a55 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 459192661 1250 459191411 459191413
    0x150c03141302221b02160e01032013060612060e0f070219060209091006020a08090303071a07020c0f1003090219032102030f04050609010c0b13020a080708 68
    0x49a00501d055845021981c904014103d0708028100c00141201c02d1122544103200200039224499030341404220504c413602401003600500308440041001b005000003852007445400031207000c1100420032181e030000620f0030008116154001014040c0c031b101e9407000c2400c80c02086c017181100d004003026102c41c02417101c03882c1d03990724905205200c0541a0400d6005209a1680781c1240c200a070302c0d000e00512001d40d0703900b00340b0140100748500a24140c2c44903005402840385a9010500b41c40d1680c00560413526040750200207400c512500d03034010506098030b050070011007054103495210b20015001c1e13a04074600c04051266060040c02495402403a210220076011701075840340c840313036001500c0700320f0018038030307209048840d155082170355066441c1d40b2500d0f03403102d010200d001555035403000c0d50600f84128108000b501603401080c2c8a050080740520150340320300510303582e01d504200c64980906280c00d104900d01501101a400f80d8400d10003c40d944070001030250489500350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 459193911 1250 459192661 459192691
    0x7020607080c160b15271602010e15090c01081005100306050d0507081207050601092307120e0c030a110105040e090c010f0f02070b0d09150c0314 64
    0x90030b14010394810104902007890601c2024041510421024400c6208180700400c13411a401040881210307841490800410103d5001e4186a40d20b8541c0c0c200031454035104600c041c0c007005078050010401c1c2c05203288a00c001c11440b0100c0c41508600460b400030640e00541c45203c01101c144600b100c500b81070b66903d050801260070491402440c2180301d18000910a49820028201c0059110251010381c044103003800001010b200c031403003141c0d000081502d401c0d1039035a80c42d01c40c1414800c41000680e105001c1e1a8103500d071180c0e403486d02d50b5910405032490710382030281c061804080518619490030754102150314000501c41c42a6500178000c1690101568807010103003a04008a41013050501000400a5550b504140035030908000b8110080c0e4600c00144445030944144082009080c00f400600382c020507010140c0c2d10032105503a844487c145441c024009045006103502092000780404100c2c40d44200b20f818407540e4144502060349048010200007500c82d08415a000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 459195161 1250 459193911 459193921
    0x20114011806080f0114070813080315090702011416020304090203060303300a020403080304020d0302010b060c1516020303010b25030c06060b0408070603020f040f120b0702060708 79
    0x300c59241181141c00c08003040194948002c0ba00380560201041c120380c0d103a00220810961600d402a405a15403030803081c03515101a01c000c400c0300b4848060312101000000c51840c400c44000400c50200143c14403d040c2804d0b20002c3c020101c1c401c20000039035800c004111003200d484981c41c0100069030086003403034107080c000c0c0001d500240105505110170406511200916007120f980c0b90088034500111001d00d01e4100c144003401440c4401480c8100000e00014006a064035006501a10340e10091034080c901a80140307001603200782e0001003c0340c40d603403011001a03d81420310309994001c50680740c0203079111040047c0d0003000090382003800140030484800300604200b2515480e9640d04d00d580250220fa440c4030344405400007868020000180801d90051800504450300c1c640d01d000d00c0e01e80400d0700c455403030203440d080540010300078106072000800c0d14098100f203111035070800d58400124900f061380c45001c541000243c00080c21030350010070010312844090301c035030b40b140c1d0761 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 459196411 1250 459195161 459195179
    0x161b1406090f032a120408060708060109031b091107051203040c03120519030204060318030504092a0809300306180106080612030c03070b04081b1c02011401 69
    0xd030307001000d2441c101c164050141308010030035844813a251100eaa90f03040940003030a041009045e42c052095000a010859030302100000c201c0740c010030400060705070887e84a09600e231543c88641f400307090002d00c2094400a40003011028400c030100e502c25841840140301074001149e010f405a1505541040030030102c00d02d40d0b6484035a490070382d1410400100304114072a807046d08100099010805020842e0144030710440e030451a8120061507c0d1650000d219103d81d004400d082c54a030009102e81e580c0030765207091846140d051855a807500400d000744014400c980180452180315100c0004003038102e92805031003440440500c4440e2804a09005c80d48013614082d0000601c410880150740c020300035034080c1031580da404005043c050100f1125100800305c2807041d030020810000c00c0c1e0b600000711150b081e807010800101d0303507940c145006d03035018441c0b0010020034603210100f0051008a01c0c184005448000a0303801a80242c0403800c03124901100c07e00018040014410281 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 459197661 1250 459196411 459196447
    0x1090b1002150c0c0a121205010b09030a031805040905060604050f0c0703030c0c02120706020c011701181b0306091a090402130f0c052106010206161b1406090f03 71
    0x2c444d400ca410741000c0703544400184000d044040c00041113401411600e280a0189600501d0345103005803c0124050020362901c2c10660b005051004000c12092106001a450030041000400400c02103090381416a240c0108072001407060380b91400003441c00380f00c2e03584503004010118990f4140a044d5805a009040101e00c900500840c9540f41e00140d40b40320f81c403184d070442e100180a286251660191414514603a100e040c040410912002e410b82c900015045851581e40142d001d0400500040203000c81000a0541c0c002c40318481b6055800d9001070088074065207040003c40c441ca0300100f0b1f541500d81006074040021004603003d842d240101c0200400240ca001456400070202401144c0454100b20007040c0c010031048034403000f105040c41240c402211403491850035100003511890b000700072208e592004414800010300c102000b003420024580110110041381c01c0034101c04500300042002c911442d00000c00c0c030b49000c034548850b0f0074840029800c00001d04c8000303407400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 459198911 1250 459197661 459197677
    0x41a0f090a030f030e060901050a0e1306170f01060315050a0b03060a0b1302090a060f02010204080d080a0e12042112110607020609030f0a1701090b1002150c 69
    0x1441403280180d00d9596070009070045110750140f0762004250302d030140c1951440e108103031143e0703018030154030305907080001c071440311714107180519803148104005002040249101c03084a441c1c02c40109030290b4031001c1c012440d035040201e070348104143c4646401c0c0c64490000603c518035400410701b41c59000e030400790304114502c0c0003207807403680a00482d140500071107400404944402000e09a410240c2800e083d48100322419881c0c603a160003c1a510202ea1255004000650402580d400e1003913055038080c10861040e901c22070007511006200000540d0308010030f61030b04110b807506860005e480a0007080c0791405500307103440d104842c1076020900d41403041c0d11604006007000280460316013000d0400b0fa07200c00c0c1019008103401454000002d1841e0150351250003070241041001059403a010081c801c00303540c4112004081300c45000000c4c18140f694184130003c00c565003260000c5901e4201516119003514046900300e03aa14031518640b12a41c00840104948802c0d40c2c008056007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 459200161 1250 459198911 459198937
    0x71503180515060a06050f0a050304020612012306130b09060d0e03030a050606070b040b041e0b01030311030a091404090206270103021206010309020307120b150105041a 74
    0x8512684916051070b8080341140d03072810507101040b580d443d1001c4a14041d103540d01d80103091042e010503428030b6101d101c1c44c1c1c8090180100000e0210f5071010700703c8003200c030640c401c08403e507507818400c1100d041700c04000711003907034440303000800b81805000c2c0c1d104140d0381000324040901d40110302d2015400341c02010b8000c2c0c01080b901000700c5450158203e0410b29a004503500c0c9001c01c0d842e800c9420203400903101d00e1081220801203800c0580590300143c01c4880740e146600c0e50721300756131120f0207401039034664030000c050041803008850820303040320300a480c0d9000c036800b8000c081c2c0c0c59200700901c00e80401e545000a104c50643c03c000241c00d000f01400c0001c00c01d04540009560303801100d030a110031034915407070820542d5444084004200300703003029400c1401002e000e100d1208020300c258105030f5114440000d40d071381008070300010704c2e000d05204441151800c1c0340744050303412221480c550200542c1c0c400c880d485581210111601c0700c1080003007440c109850702e03055000220b402e40e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 459201411 1250 459200161 459200201
    0x20f0a1d0604060509070e0f15180f0406050a0e1f15030e030901020a0b06180f04060f020306010e0111070306021605010b09090d110f010c050a03050601090506030105040209030f03071b08071503 85
    0x3030003e600008110030ad1152a0078514684810304000d0803e240d00c00181c010340c07c001c01088191543c039a400155091034141c8952640c464405c0c0090806405c0b1040d0510191800000e82500030314540a400c0c10aa8090000b40710300c0c6040e0741e5a03c222014240180c2c4207070600c10210325400021900084018540c184141110101c900c405034291000841c0c1504141840b04200c1607200340c5104505e44402541140b82c5900085e00b1010002401c9042c0140320070310520a007400d10000c0061684403030110b44a51803c110401216038680040350150b180a011104915100346100e220300080e60041000c480d1000003101d0f503c0e1003141c22642c034071407140310000b29042801044102d10066039015180c0c1c2d96404000d06030f4030058081410321401c0c0c1d206028903201c6400702c82c1503039800e42e409a5100441c0d8082403520380c1840d0312003558003000c100381c0c0803c01280405001130b40050f01052103103444a80168a4402d01d1085207000a8440d9480c800c06002c0c1e0002c0c0c108000300104004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 459202661 1250 459201411 459201439
    0x70c020d020915010f021209010c06090c030809210a0305161a060a0603050f010b090a180501080106060f2a08031e0a0216020f0a1d0604060509070e0f 66
    0x51520141e0382d01d80e4000c03d0401c800120350303100c4284808183e0a2000304451142c0001c225094803c02e11101d04000028050300148000d641040c0f048a41c02422140025905e00303082080c1d401000c03900348188280042800a43c40c82c403140429200248e0203811014202c0d60180c1d03003603004002c2c540c0c01d20310b100e440001151800419580710b00d003100040c0c4043c6010380800821004070381192003458601070501225031842103400381926070241c549556402c0c401d0024003d40f019070302285031150415144a29030003d82c00c614100d40320840240301081c0c6440c2d0a5544806200c100b00004c5e8400e05000e204e900c5038012070b44c1144100c0303500b19031031002d500c446402d0b81c0205e480320180020610765800c0d4205200c2e0030356114016081c00c40c10800017074980d0060b02440364010f441346c2402d828011180d41c8880b5a64001d20002a05c4100002c06104201c0e01d008204d400c148030f18500743d4001000e040c4010743d54807403151640c0f040b11442144003000242c8020819107a00810743d02c0442e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 459203911 1250 459202661 459202669
    0xa121a010b040608063016060c122a060902060f0705150702031e0904050423160b03070e0907030f06050a0b040b0309010b0301061203020c18070c020d02 67
    0x34040c10280440d907540b0303420040082d111aa0103080d050107408403c89400e19045081880402295a50758090034207907517a14203032601025015215810f16604800030f400c541002da02c0080511600e4094201d4050f914181c54249071107070490401903480481120081c0031000410180b071042c10b000071b60b00f1480e00859110b400040045060100000303109041c0300081050030002182041d50240074944908000d40b64000c401070f076810082d04e000071041c07003c80c080c2075a580c00b80c040c108010b18030b41401c0c07000302c901502010010150421214922601d8040b580c40100209244003140641c034004001c50782da0f0004018008100508084030720782d81e940c42c3c949004002c290f5010403d02c1c0003130200b908556040d8080c621a089a40c020489910090281c0d011200b0299049440f40c0d10000e9050140c15050038507070307055107800400704513403042d480079000b6107000c2e5084440c141d2600b82800b05811401c1120707424030b82480c000400c50b070b01c680300c4140100c0c0b0103030034014002c2d036503400300e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 459205161 1250 459203911 459203963
    0x90212012307050a0c0c030b0a020d1d0709020703110f07030314120112061b090801060501030501030f0803040507080304121208070c11041119030e15060d03090b071505070e0a12 78
    0x1554160340000307410840d0074aa01400311188044d8030cd6084848517080d01030340d00c40c4240b10780c1c811550080b440405150180c0792900d20181402d00303581540420b178100d00d4403160175000c1100402c00c0020349903ca005220182c0b54500079503c075040d8140d08040d4660104030300c13040204d4107980c0350f09000b40ca40c0c1e04001c0c0c460740d11101c1c0e203d5520450030408502d00b507403080d0304464105803030400100089114a260708805d41d8202d11225078944660400504002d8660840412403000140c00100540c034410354011540c0600a8a5000403140c0d400302d034200c4003a207003103001452249480c40864444100410f0307001c80140000f9000d11344012030500354102c00170410100d0032420881b545680c05000700007002d1814400f0713001e1004d62401e402d101c03000141105001e408860026800c0501900c01c3c00081c00f001040c0e1526440c4030701c2d040244031204600540030500341008034003414040c0310310020310080100314601d958146074401545c1d64100b40c040d1015a00151584100c40e410640 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 459206411 1250 459205161 459205171
    0x21203030112031b331404081605120a08071b0201032406020c03010528020306010c060905060426040605090a05040903050d0605150d05060103090212012307050a0c0c030b 75
    0xd42e424100b0b45a880303042550b8200a071500d00f0800001c042c100f1b2440803582c4103074880d042d030340ca421482c044129040720084c0020a10301c03030b02d0bc4100402e04030344050214038007d0360302c0106550340e001086400e014a4010300300c42c019218118801580641c00800c03580a000b070f0400c0f417880c80c05d80304444105459100c080582c110304508981d90400b030207640da0040c100810b0500005000031640c0044070805c65181c2e00e140d010001c140307181e2082c10f0303c0d628542c0180003808144614100103840302e0301642c4c122201c282c14a0b01c0a0f503402c0356440820340c0011104000e0402d403506034140c2d2240c0c004a607041e0302c40070110740400d041e543ca03c81c4108281c0a81d94650321003a03401d2452040369001e411091081c0421952008aa45000c08403284402d86042c0820103440d0b0b000182d000d804c141d04000d600c02d025030100f01c0340d2141503020502d6100e0f0309054035490030300c8505c01070340d5020650700440003840402004c902c42c3c0c0100d02ca810300d50f05c200710030030002d1fa807511a0351041d070302520 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 459207661 1250 459206411 459206453
    0x5041406220c0f02100b030604020d03030e120913060506180f0904120908031e0c010f0f05151504060e1309060c0906110d1b0c12021203030112031b 65
    0x180040c00144c2c1002824405150000208040682400020703603d041c010b00007442883d4603c44d9408051003a0483c2200100e40f0013119600303e822417281126812910b8894040c0c2200308010005154030b004200031640050442846d081c44c2d0108030b1001c14844011a410201c0e40900031a1a111800e19521540c014076100d100400546002003c0d90401d5001c1581980244446040d40c00604207100710000c001d040556070300c8006107054050084010074181003460252075030518034140c0c101d58494002003522015200f4600100085403101c0382c4203062143d01070009004071805111140c2600100070204c120892490211805031541d1020488031241c03104900e075015900208030700d0240c241d038181003c038900850744540d0741e6020461a081000036102e402074003000310b2201c5944003900002c60408050704c2e4101c040c1c01c082c2941c800c90203066003004040f4520404425039050ba130701c101443c1d9648400f030700d0841e04401a0903282900e202c0c0e0030020300004000c07950001950070580 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 459208911 1250 459207661 459207677
    0x705070305011b080903030601050d1b020c04060b0703081918080414010e090a050a150e090610080a030c11060d0515040507020d050c0c04060b070c05041406220c 71
    0x102e0340e400f550b4441040c940912000406202e191132011040d00d42c410300030710304141c8500004000307201612107041200344510440520ba001a40c5c04141c03400d2081c001e50301440743c1d5594030720f45941482a11405000038110318089160030103d581c0329140c00803240c2c004039940740c0111441c507101202c14011104a100028200902d10010080070308003a424202095038210800c00700758000f40040810410fa9580d2000411041050b8880d40300d515074940c0011010f500e40000c2c0b00004400e64584915100c4d0138005140c01e01040d00b000155241000034000c10266950203403000e07945c032030f811141002c4400403001e0326100c000c06840340c0c01c4007001c0442e150030b100d500314540c05048070b28680a14217000800c140180c00203050b11580c45035182182c2da40681460b202c0c10b00c82441c05065100303041000c00038001d04240b01920486004500e410405c1e40d4403001c1000f10f800c01144001800c40d6440001e81610307041070b54000341040d0001c000407103a90000038034111110f1483c2400454900c3d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 459210161 1250 459208911 459208931
    0xf0b060a08150414060d0201021c050408010501051c021207091406010e120c0f060f040803030108120a090303080c120a1e09050a02091806070305160806090403030b06070507030501 79
    0x10002c03041e122100340d904102810154207803984400000304542c0c041c0840341c0c0c0301011a4820400345610181d030840c0480c411402001c010503da00c00d10541d90750b90309100010807a40750507508244903003e00b00e021960900d140d402d000032180c01e660104114025190000344002e10380c011654144000b2140b10301510340180050554048054428007902c880006101010303c00260f2000e02c80040300c0c00807220100500294581c41100c503040c190190107d00041d5841001001e181a2841c2206075030101c00c80554848450003540c1040001801a05080011134000c08505400405031103400b032418001c0741c94461246020340c1c17903008a0355140c041c071440b69940c90541801d002e03c0f200610074880d0750340352213a5800700410041e00c0f6100780d00200320fa038000451001c502d00e9030710055407024a0822809801400d0440d0046154491081c10360328031403207440c00768807650004041c02415201c584003100200a200c021503008007003044100d01003042044040019407186d0300204000200d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 459211411 1250 459210161 459210181
    0x51209030d11090a17010905030c010509012301061d031e0c040b0901300309060207090e19050c060d0603141f090201030b0a15111605040f0b060a08 65
    0x414072030b244000340600522102d5920f880300c540c111884d880c801141c510003111081e00401d04048002d0003440300061400e54400d040d080588140f5203039008101c44000c88074000c0340c020034420000c14180c1d00c20b005101050040c00d40b041000011035501080080020110745000520100c0458130b011100529009990802c02c8090510058400f44030000302d44001c90b85140741030248900c50403403980c041405d03070010000c24600d12004c04d00070408442c4ca00780501226054000e007001401030200104620319140503411403000300d030340142414003444c030816001c800401c901320394500a0b400c102e141c40e1b40d120054260101144070015500d455441c02004040b00d001d261314150b00b1150a0108000b0b28480510904041d003a001c00c0c0c200d9240300480003403428100719540310342603680c04903000d001390003013040d4800355490f841501c000342041350344e4906405903030741c00c00e050656042c0242d04294202e041141100c000c0801d0310921007001400c1c80d0040150480054581d1040000c0340e00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 459212661 1250 459211411 459211421
    0x905060601110a060e032101080708010507080609060a0302060a020f06090721060b0301050c0702010e12071205070911071506051c02190b0d140c19051209030d 70
    0x909003440501c280607860b11a40700d41100c030380985507a41d96816480d02c54001d0089840c4200d04518000c044801c5045026007650203005002c0c10740b16a14000c51400310511078540541c101c5d4486102d20b540303a000708140c1c0e54004000d1600030b82074460000041e11502c0140175118803540150804a08036000c031f5150180041c004012548007420401025444c0c000c0c100e960755003091105040305031800c00c0f03009020312a4000f50198030b0501008411031100000e421000c3c0300f641c824441c403141c4800c02c404190300c440001c0d01900080020807004c000902000c0040d41b0650940344c9096440399488203c450064000e0071900c00000d000d0100442c40d5a14140e09405000821144e4100004955101010744d04501c4000c424074800083d035950a082004074901c0b4028200c1c4d5640300c034166011078000ca030041519078180a22030f00e03124a1500000d102d0201d01d000365003003072f80006580810300007003020501440820825900403400c69110a4132440405d40155502c40e001c004100841e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 459213911 1250 459212661 459212671
    0x11401051c170307020a14060406050a1401230d11030f030307050d1e051006030509010204050616060b0a080601030b010b04180f2903070f05010f05030714030a090506 73
    0x210300c1155400002d046aa9080d604240c503a51140d00c81e55003850980c03600c0f0700c4044c0a8250300441d03030502c00141d0005071041c46144a50b10910140d200d11000c0300a54100407102c0c0c0161580c8401403103200000c4a22110101d400e40340250715881500224a003803103100019603916503103414102140c1400c01510b0507100c990401103145240010005000303014003103440e6040798031003030004052078140460307990344000f02e01d080000d410041560710744040c031440360b00f000c00e082000280071005d040c0f0035141280c102418062402054079984100805410000c5927550b1b50b03080120036984901954002a048882c0101015411410000344001d0142d11503c111102008148030540105140100d01c80262030041101c034000780c81507000d0907880c07803c0000120000c03a0000380c06201026901c6071101502601c0d0b5040d00c50703291a0064080c0e0103070a011403080b40c818a00e40b0300c1000199400900d40c5842d2215400c000d801e04c0155005880d40e0014946a080d40000d00c4414854642c04c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 459215161 1250 459213911 459213949
    0x21c09050a080a230d0309020d12021506010e060d0b150307090303020f03031005010e150a2001020301050102070e090a0b01030b0f0a05090607030c051608130f051f03020c01140105 79
    0x10b12030002480c0d5181d0341542179404141d1100003c004540b10900c2c4000a01c4d0b11502d021072210404200039910f50180300069007008104000c00c40f0303540501c111220180c0b0150040385442032803034894000c1c010140715030790028035a10f0780c0c132400b401e044080d6010380710640c1c4648485180d03090003441c283c0701403406000c2d0b0b04201300b8480d411607002c83d1502101c40a081140345010708000040c140d00301d04c506c0c2440002e0010720000e4255000c0302d049103c0c40b0060001280d1001c2064050803030109000e000c1c0540d01c20703801446800611404e590707001100c0811948100030301d43d20000c6030754003a0b104032800c0740d2600600c52000c0440400c940e0082d40b00300100440c2c0341c60303155160380d240083d2102003410f503075124040055101d0130485000fa007208071904810003c0d450800c07840e9100034400041c05804010200303480503220400c0d0221440188460400c56aa1041c0c54840c200307030050406056080001120214081c000c40a0440032003044403404e61420040c00714005081001e4200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 459216411 1250 459215161 459215213
    0xb0708010f050d0f0302030702040e010501081504050d050c16090507030e0102120c031009060b09011e020c0f0609040504030804050d03020702150706090f0c08011b021c09050a080a 79
    0x3030b80c0f21800b0700500340307402481c111400040750800b03906520079150041e40060521000300c045a505400680c101c89200080b00c450820020310002901c4059a009215400074085001101d124001500b0a031004400740c44042006202030f540c03403075550380803206664442042010250301481020071408100000b54039084000000390300c03920000f00000050f610100105007001d4580311010040d2020550402c4205d8903060811041e0f04100203050010700c0c01d1340006201041005600190b02c10fa03001480300000080410031044031000402c0e410100070302c41140c0c1c82d90f6038040d450042d0300940b03800029007017900380f0506050021290600b414010040400161240304d5244045419100c850762628018601500601107501000e881901c40405403000c1c820001c050400b190300f41030003004003a510790402052a50039600d500050b03080240c0c61000e4100c20400305d03c03a82494508138600c2600c4000181d03913440580c1010708254805242c10342044004810080c4252448090340d031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 459217661 1250 459216411 459216419
    0x9050c07030c20030f0304081b0117060d0b0a1d01060614030402040204050607210f0807050304050717070504110306090c0c19030c1e080a030209030a0f0b0708010f 72
    0xb0803003160380240150b02450ba2008503401c0042800000700009054409014403040542c0d82c0303800c58020a4518026101071609192078540e0040f01c0c950183c60352142681c0c6000c00c8058840d00410b0340b034011100d0ba80420000d40c2c045c078400d03c9100c0225002a0a0100810a0303044541d4903a0880c55a80b611805000b1950003100c52004014503400c02585e0742c0e640d20124019000d19809942c12180204511040140444c07d00710b0020045000d07818400c98884203c5000302040403844c00318180101081d8044c4c07040340210f602c60b000d0310850b400d0b02d590f117030a256030300b0700e558071400341741c000341028081841e2902a0b910303643c2e120f0034bc090a40c144400010301140b03000d4400c030042140001d036080c12090900c0050312080c800a12a00100101d00740682411003180c411215511709541c8040c0c41800c4e0100480040d4001501c42d0030040e900324180c0c000d60002100c5a407610460030608001988045217006ca07034815699880c41703007080300c40542101d20617040300c4401031105c134040c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 459218911 1250 459217661 459217667
    0x903070c1d06030a150b04060819140c06090103020f121017070b04090b0d050d0315050303030412031d03031602010b0109080d181e051017040f02061c050109050c0703 73
    0x29100a17100000160308003840000b400500c071503488034010380100071031a11101a1a151906128065040c990006040c62a840d495500302601198000b0050201c0c142d10751203680601001540400c03401d2801e2440105250443c000b00c4060210013021002071189140e400d009003140048500103105031410b211601015000d140941c0700c11540c1c4240c1c04419507039581c0410045034000c001d50b03421200d000c20090282905030078156010700b44000c005034504000003140d21598022480c103103420840d0b0400c4015002d1140c0e41d00800407200d40c0302001c3c4a00b403008600800188450b074028521007800682503944010a07030341404240042000801e401080300810304d40d4600c1c2089026000c0300342d08420b0b0b5410b0300b0443d540858401a582084800d03030130300080d0350080300e1055001e40c80c828221001c502c010241c100716081704c0041070014480c0d1820070102c81c401080c0a080c00280c110701054500956203031462070f501c40c2d004000c0e44002d48101a0050301c66180e0741c0ca442100d40717000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 459220161 1250 459218911 459218933
    0x501080303070f050a1d061b010608122b2009180103020306040314040510110c0405190c020102130902130b030c070b061219170405011e0905030f07031b0806010506030903070c1d06030a 81
    0x20f8800e000417800c101044101d1644044100011311602808015000070712040343d801c51030b1182d0007401720b404030034841c1c00390d00c00483c12a40d0040c000e1107503540e141e4044800c202569040096802c0500010a66649500c4058650703c035030303604d400c1c000c03001d03c0200b0b1030107401040160150b031401e020f0004198544004048010344200081409002500100d00910844c010980e20302d41212020a11001680081c104203105888005095071600501c0340c4500c01943c07540c0c0c100708100010b00005e8180d00e00e01d0741c4003000500c103d00c418660583c00341403540c040740c40441950780c551301c0400c206000258016050792405074030704050a101c0007911610100035140b150014084030402c240c0d2007034004c04060000030b400c4d501183c040c008030a03070300d000a00023152820301c034112495104010b001d844080790110802421103910305824400964405441d40c0c0d0715000400100001c03d20126a2600600da509900b0b8199002409842c181d84030182c0414420f4000b00030303200105400e0120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 459221411 1250 459220161 459220207
    0x405040c0e100807030f020405090c0a0603110c030f03040507061d12010902030a05010203090708030f071b0b12060405071704110607060501080303070f050a1d061b01060812 76
    0x84003490791030b40064020251026408500103105040012081144102401d001c407407082e03a0900003929042c100e00d481d000307803003800783e0000e4064100f040800d2082d004200421004001c0500e40000310004504550041e0000a40401f0010a000070007108000e48002410b10340b42c0f4a140d58100300070480800d05030b0f03011030320070400920403c072015420760001e50722960040444003505c03d24a0014040e400484900840780540c0300300003058000841141d400b4100444200d1502c0115601c598034403403104808101280c100902040e040c00201c000c10290300f020907408000d1420204000a8400040071002008184903100c1c0801c00000e04494000764080d210080075001100815540e00806a0141c403250400000040c840070100c01140501320503507611a80440c4240e06984074810312081c1c10008440403078403220101c2040c3e45000f0314800404592070700310480103c0040401108400c3c8842e551401c0810616200700400110210444100e40c204401a00017020301d451802c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 459222661 1250 459221411 459221429
    0xf030306010804060e030a0f020c1c020904050c03030c1b10081311060a03090b0c070203060f190f020901031406060d0504050a0b01060207030b33030703140a060b0405040c 75
    0x200f0100302590f00300c0194401c2040031213441d01c20000c002421320300c1d200c103404090f01034230ba00500a414403465650000c5207481e11841100180da0a00c0100300303000300241c440c1c0c010000c0b103180b07598040c00140080d01c1c410004200342c600380023509240d6115900682c1c03148045601358103400350000b103202c0c2e0002842900c0701404015051032484040400c444540c810800520411516019400250380c240150390a0030070b5607a84001c0708180c400c000c0040c1d0305502c003c00084078008c0100c031041c4d001002114403903400340d925016109071603280040c864559000324084041c0d5a241c45070202c11400041c50078000c1c03c0040204903d03225440b410000315884100180c180002007025881c0c030b82c1d100103103102d55030303450070029210172080c08216102410032000c1100801143c00040c010011081d21054081081c01f008406010342011160140503081001000c02c003d20100142150b41d140a080f0440703951500e0f4045401c4030358814499407504060001150060700e0751070543e0300c484 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 459223911 1250 459222661 459222677
    0x90d0c0303180b0a09200108160201060e0406021206031605060901030b1207180b03030a0c0f060f051801090809010509210c011101201c050c1b0f03030601 68
    0x569002e000c0b880700a89000300c0c050034005000c016500120880340101d00104034a00044070030216400c80102041c00034206201044160981d103c040403250154000021085e170380e48020041c40e07400701c0d0103603169980132a9800d076200f5064100f1b540004214094400a6181c010542070a00c65008a40c054800841d00d04001d9000341e101071f0321504000c7c5080c10582e0024203099aa0340d981c025406c04401a003c0101004900d0080c0b5054140c010055410840c44481c101c5804000400a5425142403581f42d4040b410b603100e40c041c10300f4603490120303036803509001ca10544c0c040040c000310142c0c5020307030600105c5e10642c2030303a51080007441c0103551000310b0383c001031004507811202c1801c241071040a0803010b05c002000540c0032000e80340c240d2015822140142294540b85501e211248031040302ca0b6141800380040100e01036a484544a10454a00d14800c99508aa01350820703034001545520003d00d100c2e400380b2000030b200003080391071403c000003900e03400054180b506000c020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 459225161 1250 459223911 459223931
    0x30818060705031f090e0c09040803061903150608010605121b0103110c010f1401290c030c0f150c0d020703021c170a020301061d030f060f0103050105090d0c0303 71
    0x601041300403045032071094444580c0b9500e070300300103042041e403030355a0344503120030181103052a0350b50501c119001580e1034119942c920501244000c040b10000300e180d00e4100200c0043da045210044101481500044240c20120340c039086600a4005a01c9405041840314180e480013810320342404204010f085041003420040e40945020812452100b00125480200d600154807241411005003014001000e280303d0204600702c080c0540c1074001070000b0f03451048003121042c51804a0502461860001048850b5007141c00c0080882c403603402c0403000c00f0600c4010400d0707480d103800c008250040380c105156000241c2c803c01001d814130a801045500604d402486181070000d40104a04160031507030500501102196400300240c1c8802c1d80401c1e1072100a00c2031380d0680301c841d100c4510800ca0100c401d021701009581d403d905110b0500c180e10500703c18000c1c24020000009892100e5046140c03141c2501c0c1c0040030682d490b484003d107201440e40c498070250105415080000d402901 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 459226411 1250 459225161 459225181
    0x60b120f15040917031f0605090a3804090f0b03061303020a08040f050907020c010f120b060a03090b0705250317190c0e0609041104080a0f03081806070503 68
    0xc602100c4003132200c080100b2150100c85114100045080788100051075110345d42655075000e121003103500039002000034040356864a040a071801c044d10684820041030a1203002c00c1103c4124035505083e0100c1d00300503044403401903096801c644541030251075440e00210350340300c0004143c0701c414960715011106141c001c0c041c0c280941d40040c042da40d22034546500c001741c14030a104150188503100002804540f0102d40040400c10580d514180c0704440c1500f1113450040c0194071079110f42d2413104480c1d580e221801000201c403551004620360f13a10742003071003403120002c00c142c060002c00c00c65801040070034140f81030110700c00d1b560f41981034090708040b140003000024109541080d03106124202c4c0107001000f103404400f19050041c81180d4500b00e840c2450501c5041d085203050024a40d50714041c3c020309050000c0c0c5100d80d040941e1085600d28004104000b610100903084a020516078000166130b4070414031041510344034450300c202980d0321401040b0b1402c110300400442c4800403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 459227661 1250 459226411 459226433
    0x180818060d0e061e06010c0b0a0b0d06090b0106090803070213020c150115140d0902031501090504021314061203041d010e0906090703110a09060b120f150409 69
    0x92140e041028000641542e9070340c10096038480340c1c1038151362265030313150080b11100e8803800040c0c0d02c0c20140101943c803510010701c00390042c140240c4940700d40f0070303a88a90000c0d00246010700800f0924401509100190b100d06821035820860030580c14491034000204990140d5415210716075514403040001c00240030300c1c01c04a04030b01400f0f9031071030b038212644041d505076200e56022034403120030101300b510164240051950404030a002c14000c124495100f40e034a18005015249045149002044441c80c2600540d010b20354480610056040100003182d010047c03a4003040003202502e00450b12650050456214852014903400044414400d540c02402e2104400340d01503201124984441000d02850f04144046000650040703400104140500d41031409412058203545589501d4645245082d802142e50f1100090700c2c1054030a5000405106082c5030b1a900c0484148110f60701c003805141c4269421002e106514103d000c101c000c07420102d500007203020592521000f421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 459228911 1250 459227661 459227677
    0x1d030403081e0c0d02070504050709030f020f03151b160602031e01060905090c090a120c0803040e0a0c020703150f1104060e090f070827010c050d18081806 68
    0x2a80215410101d40c0000522a900c600585c0982d0400e0340c56006200c1114011601e5100160340c1010404c0444e010030200c100184c009032080e00e054848001007490042813228400240c5669000c000044801601040c55003841e010132528207045001e00c504554000b10010b02104c0d40000410303004083c200391200c60400902e041541e640c2c1da403070041c21440351845114001d881950010b4001800002140c140307400080640a0403030801044401026144504650481035200c001c5101001080607100234036500d91207800b18540b06890509a40b03410030120107552152030140000b41c0041d8500b00c10001005002a4142c0200002c0001d0071030700a80c80344000c0000703008500c10b80e1100429803200000c4e01c51303104944821007004145034044408e4070004030303000301261145201d07003c844002080c00c0074034108402c1800e601d500b111a02d40c088800701e44000b5030304007401d44034000c48410185400c12500740103420b4072071450070701c00c51080c2c130000c841e000c84408c100c4d079480381951051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 459230161 1250 459228911 459228967
    0x9030304140f10020a0e060f03010308070206270111010c08071215030c1d13020f040b04150306061502030f0c031207030f0b04060501020a120905060703050304061d03040308 76
    0x310300301089030b4001d62150f40b02100203413200e0041b440c607041481c115214036801004e40c9240d60300c0c2d078584017010380008e2300880e4804c20420403081c08289011a103c614000340007811000301c000c10003d405584c0e103982044e683c0c0d0410501c540e00070340203680742d0707808401803c05010588400c55500001d00729082100f070b07052924040402844030041d442402e8449855003001c3c2c0d541b804a8a040300c0700100c414010b000c094402e15401801c00e4440c00c0e90300080603001046003003140000509540600701c02d600c508410f080704005118045c0070b80d40c000c108580008100d04140c6400035228400c0c0400711113640b41c0000d5030804141d0410865682200070350225090b402c00c50710003800360a1184d5422010750500c88401014a4144190000c40d503058005003440304050b601d940c2c405d800c10480006100c440d180000741030b15901c1c02092968882d0343c0c0c4c0765a038035040c64a0f50882e00d403071030540c61003240040700500307da000100b141c05403078001150580b40c4c4003520607841d079450301d18040006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 459231411 1250 459230161 459230173
    0x7121a0307030b010e1b07031805041404150209010207050609240a030e0309010503010603050a0608011121010e07200706091d040c1202280f060809030304140f 70
    0x42c046101280784c144c41c0d444007185002d442e0b4050342c1808807042c507522140d10740708000c5900020b000714142d94144040103404901d80340c2c0c540020f02103a03010800803ca4039103d0040004000f15500000b2a1800407041182031100c402c000035a20120340c043d950082c48006400507155403605002d001e900304600b031442010104103001c0707a4981081800b680801e00b002d411507000480481a40d9020701d069580c40d00b03585c80c05c03504402070400908040c0081e0750325400420480400c0c0540f100c0454031080391540c2c2c101071030301e182e280c0440405504c1515241c200502800780c4404200d5002941c51070019600314000c1a0706010143c00d00b2141c610b0701c115500040c450360408070700780490b8201000002e0130002c80c0c144141d01f890032a8001e2000000d42800c0c00106100d5140c2d284d03281c0064010018000d0000380c0101380003600078904000011030b02c0800142c4040c1c13500001401051a0486007801c0240324141c0d2400050002000324007000c004c041d00003410028240ea61641204540c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 459232661 1250 459231411 459231413
    0x2151023040e0d1701080c0405060105120408130821030606190e09010b2a0a02030303040809040506060a020d2303040b1b07020a1203031410051807121a030703 70
    0x10392180091031180200313a442540c1c064a508462a0341e040720041da01801c3d8030081401040001c240040c4024140407081c0501e0401e41300808030b4500c158414031546580e05036a4a40c4800f0b4402680030164660101e81c4c0c04180c1e5014420018081e88040003254882d11000d000502500683da80c910780303090705291411f0701740c2e4000350f0120014024bc40c02591662180d1603c50a841940012500d004032080e4103052803022540c40400d858848042d40c1d264940c650000e41194816181900d4000022480c00030743c9c901842501e411140c101c03540d07458401c04c80340103511045c0c8031a140d020712030083c0300340481e60b28410403854010b104401c59030340c07803a1901c1c26541003481034507502c0c0e0a0449801d2100c800303140c54101d400540d0014006081c1901d40701e0501d00507800780c0d1085080603144d82091041800c003401040c0912013001e032259100703041000b8000d290b658050512174001c000740c203109460350040d10745203440d1850b00021640c0c00c00031101d170b2007020710504d11076007521070114000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 459233911 1250 459232661 459232663
    0x705030f0307031506020d230c030c0f0a17130b04180f0b01020c060c0c06030709090b0904080313060b03160303030b1f1d180702151023040e 62
    0x180b040c0c10039141040b02c441d4185044200320342c180640005a1300607c1b1502c0024024a070b0740580480c14082d0500301c03c5d0907154206c0c0c5030403003d40c003040b0b94008902484200c3e801e02080c020202000010402202191078902d0324248800380780100e41c00010709102031111004551000d0141042000da4655441c5421429620184001254589800000a1254450f0280410402059000f407010031607000c00c100086d40200d0a00001c1c0c402d41306003440b503031034007400b86124001d03c0e280c2800d40c503c0c1003c40000d503180c00840b9482059038000304000104008290ba420180070782030f00c40c040c201031600c003000b071020001640d494840e5031200481e81304491150000d0301e208e44c2d02800501613190a000e28004d1407064800e07112420207064456a1058501c0b5151003250100c07000d4022078540811000e8141e00e510310102c5e140e0204011010350100422200841c602038590041c2c548003500c1d0120030980d007d02561507500001803003000518440e558501500108204070341064280d410b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 459235161 1250 459233911 459233917
    0x1090e070e1c08042d0b0a110106081207020111031c27060b10090e040204020304020d1502072307052205010f0e0105030f150403090b0307090f05060414040f020705030f 74
    0x1501c20066480c5d40004903864102c0b080c4200c030f80f031840d1103040400c41c440c15070340e503002c00c3c1a1003065907868400003180340040205031181840201007551351902c9000051400714801c0700c041040c2d208101411111f008003400c40484007444500103608980c2c0d5116155441c0e002994a40044461810900f40406076005500304a001c59640e080300380301c1c8000b903581102c0d1b4494040c120100d14006805414541c0080d5482403000b402c40b040b0700c3c0c29503545d1904402003120311401d01d5000c192181001461140c0503101084210540d03000b02d92990740c1555683c1c80e001d01e0f40914103418402c0300001c4540015084001c2a12041c000c4c1d40c1c5070f00103616490240c3c443e040c9000d0000e0700000c0ca50a02007844028010800c014281c01080c444030a00303c038001800480800c10342c890009025185003002e54091103c60380c400080514011014800c1e5503507070009072091a04000820009001203050150070005481c0801d100c00c09503540002401440c1001c1d081e4000014003418026051000f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 459236411 1250 459235161 459235199
    0x1b0708070f0b1e041508070e01030608190c05040f150504060e0a0905030405180a11030705041e09180302070b160809040e0d030b01090e070e1c0804 65
    0x115003a49a540c00400680c150718415034418030010041580e60b501001482025031916204503841c082c0e5401d42641406241c40000c1c001510703050134004e20f143d00c02481d055010003480d040c4906801c20188503191503401d084000700e0308000a5423400c004050000200400c4010704c100041466900c00b1000f80800324166503c2c00009a000b0070389107018800e9a056508131100c4a40d25562650305400605146800b55003d100900c030024032a40c422000e0003845c1c2801d9510110703030500ca1491025504c1030716004002104c18004c21030f14603441800d8070708650421406041c070002c0700184024a8810781c00c0650b42e1070904a042c00141c50500e00c07036411034860760840c1c0e00c107503070b0ba0119051409013079990031545400c421030001141d00400500703400c100041001450220005003a0f1030039104008010100380c40300c0d0307201020340c0c1280451009207281c1c42a210301d807400d000b00410002801083d94880c6584003071007101c0f0f29601404803c4154032a0380aa50349803510840781c1072a0004d26 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 459237661 1250 459236411 459236413
    0x420031f08210c0a03110705040534140a0e030f010504140d0c0803190905010f0b0d050705041107080304030207050f04201c0f0f0b06040608010302010c0303021b0708 73
    0x40e41a0384408003030215442d40041c0c00c0070702268213039640c0480d00352001201c072039040d2045081c081403613a52441521701a1041010003030365034508d0400760f5648805000c0c00c3c013031601e100c14450132030341d008078005080d80d5400c243e8658401003c031041d03030b000d140292503507014481c4850b00401303120154021307400f40303006980c030f101940c5d0850030017641c524400c40040005000008102c0016400f0740c00382d90407000c1c20203541d80d4105501c0c40b078001c403a0914026902a9181c4011280120140c4240b003c421030a60300b0000c1d400ca1512120b03038a940d18822680100c0d92a504107800000d00c1c0c1c103803500140c0c0512410350340d04103802c0c0203603034900c180a1103205000050210070300749814421031800710801c0e001c0c01d880300c502021641094018182c083d20f4000303203050131100d0b14000d100e0300d0341019181c54002805c524003040403044a03121150540240300c2004284692a0804080c50459509103002c04000d030031490101e01a0003030800c20070030b180c81010102a03408020030f40c83d080d1081e43e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 459238911 1250 459237661 459237703
    0x3040218040309031205160f020f06040b030c03060d0f0c060318051b010e130203040b06040204050919021204030c0201020f12120a0608060c12060420031f08 69
    0x803550440251060394010080752110b0800c00000d0040305507040b0f07201c0c0c1030925505114a500d5041c01c01030103e101151543c1c0d4103480c030011460400b08a0304c080c803058601c5810141001d01c4001075100180c8071159200340400003802036992a102c0e1100179078080c940c00291913051810000480860042c43c0129043c03d01c81c1d11180c054150252100ba0040010070481d408200d402e0401aa10203580f4100000e4102c0c100351500c4a1075050300940460713000698902d0103081c403507846440501000c0c421401088104007656035905880d40004452685418800500403040c3c002d11524090107804100c800422082c160800041231409000f1703026a0f185440b44001c460b1542e11006101c003245806101d00d41c624a0403040c1c03581d0003003165a0005985441c1d18a103858440100c2c0c1c010642403002070503c440c5401c65030b060b0303008001502d00703100c80d8400c0300f0b060608001c802c40c4c00701c68620100009000440c1c00c982001101020b5002840d95a21203420503259811b0b40d544003407120b002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 459240161 1250 459238911 459238939
    0xc240a02030f0402040207030903120c03031103042a05041406040e060f07030e1905010c120b0604060503040816050f010c0512010b0310030503030f0a061202100e06120903030402 78
    0x20300071a803107404040042c80340c6607940d5003000025080480181d04000184001000040d82c41040f18544c1c041e40e2034035032107200d240c0390040030b807160b620f0f800383c961106005200004103846002c41d051070340c0b0948101240c840401d0068240500d07440f180e4440c0c10041781c0034518201e0200580149416038081c0110f0558110081c0e0b0345406591407881807006a0025100d184030758420a5804820404d555540302c0038000c404000e203d2400c1560305941d10380e68591341d50b80003240c8403c42d81461905102000c405400600540964800d000c248a0000300240410031004110303110400740080a0405841c54105165a0781901e41c001c159503103064100490a80a40180c0d0b400030301003000303014140e0a04900407110340000c3c000c00b03c800301806011000070b2042c07010314862140540800024a4110364107000c2c2e920662164810540c00038541016850700d12101c030b6141010708114121034401c0317000c1200707403050343c4882c10402c42c42002e06c80b07006e05c0440290302607402110000e401c5209 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 459241411 1250 459240161 459240181
    0x20901050904170901050409020c060f060901121b030812010906060516080d1d06040c090c084c0504060609060f12050c0306011701050f150c24 63
    0x802e03100a001c41e8001c807002d000140d01c840080c00a0a03041c9030550605641e6000002a03030451400580329030091420044460403641d000c40e401041280d5030031a95240041c03000c5503543c1ca0724040c0c03000340b500f447d490181c2e5954100d40c000b10350180d400c4c0e94420008118040310082030280d5850f071818001e000031074034402d10564080e07551f85150101042920b81e14140310750303c4000003043c941e0b114044100e85001d80030307190000c0342c282c03400b400251420386003a60030440303d600905601c9240150783d0500b66030000080760f20440e00a621441e80b1003031210340c520404942690030b0941140040040b81c410985c0030390702c1780d40508410410041c3c881c0100001d9400c01d009000001d00359050400400b407254510041032001810210941c83c03102403041e043d5401125079500c4003c0003c180221035a1207103004101c1282e0b48541d10b20b95040c080001c11030040a00e00d87c1c40f89200c00b00070221402d000301160340c45924981200c1a607502e0ba01d0003044801e04101d4805000040c100107604500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 459242661 1250 459241411 459241429
    0xa050303090103021c05040c060f021603060c0c06050903180a030f1203061526090607140c0d020705210a02061c0e1606140714031303060902090105 65
    0x14004000e94280350741c03500110000e40004165000c49200c107407039802d0070b1101c6d2189a029038020718501040500303042c40a0041c40c091010441158401000d182802c6010b02092003560307440340c000b00d1500c01c0300c041111464203c0c44040d0010f441c00701440040e43c400401080c00002100004440da4051800c00c13514aa00780b2000e40800d072040b2400b03002a50103240c1d9008110302d814001226601d820102070590b02c20000b59010841042130b40605801d01b0060426102070204050000d1401c001c009455401c00341042c3d05000b0900d00040c1180e0240c0b0030749200e40c03001c0b02101c0410800200c02940c808441c454180102c2c0c00702c0006a03400c19400c44010f15a0060005020140603a800d0000c50f503c102080c0700c2c041c0c01002030030500c2a00f40201c5003002c0c0d10000504078541c00211074003140b07000e81c0c8120188150403903c0c20000c048201030380c2c14550403c46100c1002902c1240c82e0840c4540001481110740306080032040140c150710002d03003070740280d0301080c2e283e80b10350501c003c0031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 459243911 1250 459242661 459242669
    0xf060a06080f0c030c0c030c0706091e0620010f1d1c0804060b0301090b060406080f0619090c1805010f270e0a0308060f04020a0f0c030215071107050a 66
    0x84028400103c00d409035038025030300101407000c41443c00c101c034422281542c03c142400380c5140c00051040103082e83c001c2c0354001801c00311080d91211118600f2481c020300e02e62041205100351301100c00740c4803800b680300c8044403492000034011000c4141c4640020071481c60b1404120344140008061500005000c1d5180d88130303030f201501d2005100b00280d41e415001402141c08513100d050a81d15501c00f07014034250984600030980050400404100c2510203642080c6555889682d03d21134a140002d0f020350030a0384003126007003641000c0c4000c0050003040d4406002c40881d520005070f811a5404500d4588401d400104880c2c0d8a035030596150050314030400c040300281008000307010064102128841d0040321000440001400c031003420b0080c1e5a000307030042032030a01000103d0901201045245904807021894040000405400b505401c0040317000c02880b01e03a82e904050080107000304c845104441c00e1000d1400e4200140079900700509442c0c5070191003800956420031840300c10660b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 459245161 1250 459243911 459243931
    0xf1212050921070f0303080f01081c030203040c030b0405060a0c032c0a1b1e050a0605030907121101020f0d0e06070602090607030216080c18130203060f060a0608 71
    0xb101444078803001003495030102c1c6039000310600050b07004031100491004511a440c1c4013410314100c1040d41409005034404038490300005201e54078071300f0002003c80200000d040040e280d407030f5401c000781f0700c408580008001d20303449418441400800a1070030720414031b444060100725100c0034120f054880d40c40c81510004c042c1e620419500344441e06015922010000300e51421005d0345443c112341d4581400d55041e0040d00303005010b1682e21a0600103c001e109500c40e0705c0d103103020007240b161001d902c41c500822501002181c8801024407141c0e0040110001d407600014250602c11500c4181c05d800901512964039004001400030603030169002311522010003119009013880b00f1036104903400ca95403903081103614010b98600024002080c000da0080c141c1079910105540e940c0c3c032035040b9191551003964265070a40d40c000314540c5080701e190b040c41042c0c40c2c1503503490b05070040b5407000303605004580800c0001070072011103078407900040f56034888990b40c0d06415035607107605580f85102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 459246411 1250 459245161 459245179
    0xf021c02091b13060807110106080c0402030405030c0313051c020a090c02010e1b04050928030302040b070f0209010504140402190f08010207060b040501151103040f12120509 76
    0x1080b0040b410304103a40b110090b956150400c4160b600c0104600c58004502048044091007809540208010280c6080b10001c000785401e010001c3e0342e64421070046031003150008000ba04104051054840e0174060908603a202c103043c0c4925039a50440c4d0090f140036507102d07500c01880c006200364008005402809d07000c0d90034204440f0f400a855200b40d028155900e50b007045100720810804801205201180c0b404100e040710200b02c01d4500150042e4803580c000d1304940d4900701c0c55504030808107401c00d5001d000c0e52180c07406a02a0080d40e01004481001052200a0290a0000e24041d6101311030309040ca07a25a020001150541020060411004070000e00103040c0000851483c060007034585840c0765850118001740e012540042d851079401103140c804000f4a806000f807074030000c0790140703e103604220180304105d1000081e9800c20012103400d4004910038803c4030054111004440031352a01c501150940d1200c0b202c08441000f01e858403110100d10802c00d8604c810b0b8014900e4507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 459247661 1250 459246411 459246421
    0x20c040b0619030e0d0809010c0201090203061f0906140a09060f03150e03030c0a020d2a031e030e060915010e07121a0117010612020c0a0f0f021c0209 66
    0xc0300b10103010400d000c2c143d8400760003001810802c0541c86500c0d441d5a40740d01450445003040c20b407254122140300750780c1030501e400700603500860401c0d88000b03068002812581016802e24110034140d020340402c914100d00032840c0d4413619005031030302d9030556074880c0d00e940c0d45c004001111298419442c120844c15030500028007041002c0c4084890b025011072040c0720400b8450440d44140c0d0b42c10360b01c4600140410620f034052005814280040c2080010000301951400e0120202881d29804828112000c8e04145c05504200c040104048071000400e02840001d00101048401400b0900c912000980d08150000d403200194041c040c410000d40d1a08950420101015203014103000501009400c00d402034440e1036140248072407001c0007804004000b40694080300d4105001c200044014480c0303903040716210001c4c21058500617510004038540909005c0640700040c420310740d1280000501082d0a503520403680211012200223500740280c41c124070032450300035000300c1c41c0e1002403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 459248911 1250 459247661 459247687
    0x1030b010b07020d08030c0301180c0c0b09100c020c03212209090b0a05070507171602060d05010608090a031b0215071212110d09080702030303040308010501020c040b06 74
    0x1a0032407002d880501c0c00030140d505d91078139400071218820620004001013018a0a10b50b0011a851306000c041011810085004007041e000c054007506424440f00828918502044011700c00c000d00081000010322b0414000d49540302c4200240c8648964a0b110013004503000c54006000e00100d0320500c0c01091840040100308408030041034070301c1c0703058001000301050040c0340d206403064030300c0c040e9482d10220220480313402070802c6040100034440e84000400410000060000740500181c4900d0081c1060403444100100250082004103048044484540080341a9141912101ca45545843c4081d40d0380f00d200c100a000506513100600844192010300001240003621080d000b8000361489600c81d4028a812103402c0800c41d00b0154803a8480c00e50312100f070f8541c0d030501c03104404117054800ca020b098201d0030b140d40d41c2c4400380100318070b0318122290b03d0740c003074103032600c0307241609014165070002d110b141d025018100c07001c0c03000e242c184240e8803008001407445045c403084101c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 459250161 1250 459248911 459248917
    0x7090e071d0709031b0503070608061e0f130902100c050a0308040c050a06050d051023040e0f100b06030402060a030c09090e0a1a0c03060105160b070809060f01030b010b 74
    0x120b000c1c0074404401101140c5414107202080c2100d0401c2030040d4a00b409151503d07025038080010420300780d09020466541ca025050800076845803604280408800980241441400d0640c4503140300300b42d4000b11181d03007244002d94000c0b1000705540d8169141542c5240618130004c002e07411012810b00001d020b0b0130550b070018001c0c6043c8000d15191b1002c1508003551740c1240000c10340110762111301c00414001c456000b5103c00f86054403c1c68008680385050b100c400c0c80b5031002003a5030701c070003907111035000b80034140100e000c07611071010020800e41c48041c00c1345001400b0b41423000c418040e0900710100c0340240d80c05440300741780081ca90310071801044081a08420021b07040070001d4203010714028514100d03000000b07000e6008041c42c05001c512a9008072a1054518808002c505001c0200392540900282409a84d50140303a070b10220b2a9040d50005041a20b401c080c00714003688142114802d0622200b2a01c954842c401c0c030304944502403000409071100080180642d11148000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 459251411 1250 459250161 459250171
    0x702010203041a04091107060c0e0609010c030c050a230a0b0c07020d0218070f09030f110102100f1508010207050d03112802120408030304120e1207090e071d 69
    0x1030400785c42c1c4103854107071100b034580c80e100440d000ca82081401824440d8020102c00c0c0d00700f42c014282100c003c10181d028a0032003c2c1844a68907d43d42810700075203c40002075400025212004554689584c90046112a005c000c0b0703540807115100c0c400000c1c1040e60140c02401d038146a0765845200b00c1258894601240c22440c041c02c2000107031078588003000000b01c20302aa501510300103d0081845841080d04003c02000d0503042000c900075840c54501160001204402c84100c0350041c0d05c2c0030440c01136403002516111403860b1901c415480310f1745044042940081c600d0740c6003240307403d03800cc1d00400740540d002501d24101d010b00a50000d001245134809480c1016060400340e9550103500d01c0540c0c1844080700450703050780c0e040c807080714054141526181024181000c040c0e4902000380001c12040150280d0b89066004010307600398102c000b82510b00c1c1440d06250300ba2202c01e240324941c0610b08021071a0424240801c081d015254160b1b040700200d8012a102c00c003004003e44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 459252661 1250 459251411 459251459
    0xc0105010815010617151c11041802190e0c04060206100e0a27060e16060f120b0a060c0203100608100216050304080717032703070b0301090b090c070201020304 70
    0x2611000f81c6401c0050754030b40c0da6021240301a50701c64107064134008205002c081c0309c0e40c9010152009070541580c21305013540c05850320303680444074060104075442c090308110031501c0c03180200701e01d40d46600e00038000e0360120ba080d0307005501c441c845610400b5050092070022000c0d03500040401d1030076440b02d49a0341030b003000104d00720f034107042c000c03403070303030071104180e4816445841001410000708400c40700541c000c40804c0c4602d2400d1002001d540e849100768007000b1400c9180103c1100030703000f2240110f00109015001c2c2d03920000940b01d00c0b20760f00d00b28005d0044202c150035561a5114401c12a450040540403284164140300025802113102540c0c81810280d958007255040000d0800b5040301c10062040c03a05110341d02e50f0348082010181155801000400b074240e20f9200c0e005070a4070f4038109190707600c08480000b0b0802c0490340100000308004400060804200d0300724501d1171209644104680e110740e0403d810383d00c682800030340540d004220401c4010403a2400c041a001c54074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 459253911 1250 459252661 459252691
    0x70f1b0902092b061503110a080303070f09030b01090e060a0e0d121104090203060a09381009150903020d02100c0807050615030c0d121101020c0105010815010617 71
    0x20b0f0344d01c021500d1889407114842d15180d020300030040c120804410341a8100e82d00d4825a150038a0b00d5a00e00c4018110006c01071512084c0c0d20381402018500040c540c0324154912a6844000420043c040448038026038031421011642904003440341c100380342d03000406040340002c0764000b903869a0889480482550341c1e0080c40c2c0d03100b664440580043e00176808050303520300f481010020483c00c2030300044100c82c5040050005e2001048000c4482d03503141c2c0d1400c54844030389070340a858540e4101215040b204440402c0b03401544084c035042518241601c485a1845402c3c0c1141c1c44502800700a4114020103000c002601c2e08180c003041042e030a00c0c3c5080c14a0f0b056840d405a600402c00c1118241d0190080c00030007500e0460708240e04109500403c96a0300600c001142001403210140201c5078008942c1e07401441100d8030b0074440b4550000f91741d9407002810141c000c00b0244611145800341a5404d50b4001100070402d040f1201e550350505c9452a0726125a4101ca000c0d1412198555030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 459255161 1250 459253911 459253913
    0x1b02070b180301050c070b0709060504120809120f011104050108010e0a11070305090307050105030c030601030504050f072c0f2206060e04031403091f02070f1b0902092b 74
    0x9011382c0c0e01c1034802246040c0ca07000c1034a005404a0800b030030b080140a12860203000c9a40d00409640403582c1580c0c80c14412039190411a071248030b0002c8854000396184503854291400141c88084203100e00020041c0c4c02c0d200340040400e00403406520f00046120004003c502c0c40741455580004164000103503c0c0070400050030990b00c03840d4120080351010420f02c01030714060050000500c801c3c242140b6504e0b004030070340c59a01c0700615081c185681c440228040c40000c0100e80c0a00c0004412100b03c1c41c0c0750030381d001c10800d1a00c5c000315030700503040c85440313403402c100c480d14050900040c494100c3d4861680088451035140100c10f0340c03c10080c0c050000c180c060140400030304056003410f40508050138000c14090302246400c441c01400c10034000d4210b000140d00d0a1202ca22204c80e40807070641c00103002078444d0340c60150100e4100d41e15401032015041c00038503003007485824442400d80d900b0f003a03000e07401840041d031352140040126095510500e9114001c40a905000300a04a41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 459256411 1250 459255161 459255163
    0x70203070f030b070210020414041505190812160f050a020612060319020a090b060415050a021006081e011b090f0501030212040f020a0909060c031b02070b1803 70
    0x150382c415941c0b601200103001115405000c0200206203035030042d85003905044105400588403140240116910350a514600e50080444409804020030001c018880700c0280f00c41080c040c020113a05000e0300d485078112490b88800c5030030319180c8608095880740c40342c589241a0f62440000d4420380102052100140d07201c50003050f00b410b009603000c0090130084245807070542a022090b0b842c81c0060129009a581d2550f00000c0b03c42d01d440100c0d481001c980440d000340510b900c1b4890426892103803483c0c1c0c540200281a80d081e05034202e80c201c20076043c1e020103a03106071250700003d0300001e0fa21401881e0000b00000241041e00c000b040c1c0005800400507031100140c4d8401c00141d02400611001071248803010040a003441d0942c1860700f2a03254040f504402342000b8280618500040c04541703414005070010303c2130440400080b40942400d00c00f41c0018a00e420010381740c0313416240c1e1207907070120f094035400d102e80c014210703681400f116103202d620000b869000610407260400c0c4540e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 459257661 1250 459256411 459256439
    0x6040b070b0106030605120616050c070803070b060114040902090f131a04090c0504020a030b09071214070215150a0f15080f16120218032a0607020307 66
    0x44559005200756140c81c00040481d1555017103144a0380982c03c0d07007913900c1000074045800c0180014240928042000240c6052007111500c43e00c60150303810000d01e42001101402c942e500809013440140c1d9440b00464a00c0714171820520140030a00c0180413900306030340a4240003101428071026482d03280c001a8240701d000d070200c1c0c0401c0c0c890b02c141c01c240281c00040120214213490920106c1056a2200c18090150050701d006a5000c2030b070348540c900c40d820003110b04c440a441601c0303500b80100014002000030f00c02030740c91824611404508440c40d606d01d881144103501515900c000e907298282c40c0d1a01520aa41c003191032080d0400c2981c0302c2e5148002005000e00d070851031440c0c180e8000303489900380001000d005400701001485110350904a1b40310541c14060b200782d000300802940c155072000e00c4550000e00c0401c151091600c1d0b8803908000320b0084049407804a00c1d60001180c101212003441640031107400140c5160270104050598148010281c4800030344601800c01004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 459258911 1250 459257661 459257663
    0x60803030703060b090109230a2301050f070605061801090b0f0603070813060e030a09170f0d03020d06051305040b01090b030304180209150d0b0f0d1106040b07 70
    0x5040001808040c035014840c0400804400e40c40c2c5044c0740b04a0000307411041d00e886030000308544603d900300440071502e4022340d032240081c05089103907150a01082d0004c0c4900600001b94a00e8500fa2590360103201511203041701c8080c80c910b00300c290703554080030f020042e001d03a400843e00750301c0b80d19030b002e20b51001e8042d1600c0c98000800c0e120540801a8401a145086005a0040050003145a4041c4a5aa1154110002810185880c50703d14001d200b0141c2411035408049542140507500031a160111944d03002803240c08241d04664680320170b081003414140f50f100c804c0d8003c04501076005440442e4a400340080c00c1075403140807841d0005849145500c41d40d0310001c210410101c08a49030260800480403c0400320080210f641c07803255000760b950a100100ea0b402070519660110303001c40101418003400e160388401c113150f860704007a101c2407440d42484103441a508010800380c44c074036002000224880101e03201d640c4440c01c0304800c1c42e00420100b07c0460031070848001443d40f1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 459260161 1250 459258911 459258913
    0xa1a04240506070c0b0c030d0c0801051002030a0801091d1603032003091306120c1a16060c031401030b010e1003020102100b0f1c12030b031203040201120608 69
    0x100c0084440032a10310080e801c010321a600601c1400081507210002030142d0b102c1101072aa100302c480341e2a4590b02036641510f8100d814204003201060344408214100c4d4070a0b80e440e01e040c0f8a031142a41c680c09010107800008520000402c0041c030660402c501010310308180d42281001210310b1420409251416052080ca42004004041e8400c00c016810b001e452501d0480c00707041d094042d06c03485a15030321442092010313641205201740b075004a0060401e041e1035a03481e41285840301c2d601145104180003814244010707100d40903190102c80b01100c40071800301c402c807182e5640b1001000140f004108260341c84030706451034290340c007615020f5400b03519100038640c5004903243c5c0602005280c0390343c940301900c04000503600041c00740320f10100c1c2314010401c000350740086015507a548003075a03031103004894400502e076450340340f09200038003070101d81d4490f12061509400361098940d0440d0507a1240c2c140c60100080392000d590040e2051521100c0c0f04d402c44440c0c0300365001500303c8136407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 459261411 1250 459260161 459260201
    0x2300114010b0a0906080703180b0901050f01140105030c07051204030c140603150301090203101a1507150f09060b090709180f061a040e090c090a1a04 66
    0x1406124200e401d0042221050981c40c0c4204910010020603141c410301c42445400c0d00802c00c3c442c003941101103a0a94560f0101a0f032415040030b0b50000310559101c9401e511b07140102c0d00e4460a111154140c1d103052a2003030091550400465559000400e92000c496007401201c1c0001c10a108050072003886a208944650440c1800c81d465245940100c4481d102603000003400c1d2100015aa8402050b16a240300c514442012902412010a0007941350084801d0308416072080ea11808240b1842003c1f400c0b001504400d0021006580d4800c00c2501018011040011880440b10b0382c41c0050700f40c0030030040c800310325400039135a41160407988640c8841a0900320b00b0501c1d01c0720340c0400c00e441c010714880c1c50700c01c0400350700740c01d40061452680ca50951112051498000e00c000f407540c100f440c02042001d504411094006000759203200c003035000480d000c4100016400401000141250280e844504c080c0d8010482a210070908030013490500419a50304d210760107030440c07070350b41c2c07596 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 459262661 1250 459261411 459261431
    0x13050402131e09110919060e090304151209050606010f030209010e060a090f0306020d0c09150f09170a050715021002030702010b060c160b0313023001 66
    0x150700a07045070341c80605142000b4008078041c0010002c0041034281030000e501040d900784141071003442c04040b80c1003c0c1d814240a0070321200300c515052229a00f204001607600d450820031400700c203070f886507041e40c41032200784441804601003500c01501c0d4140f5851083c44504002c081c0c3d0300ca8501600d039500301c0b4040111035600198098658106031404518004100c1c0010700031140c8801414040c82c00030070700411490061529401600c1002204006142ea914010300039520902d00401001d0130994860183c2d4010100e140c16540002101f9084c1e8000880c1254489a1003110a00304195040d001131041100c10400c03140000d0203000d420340400500709a46401100c0d4001c0981232440c00c891200c3c96070101340c80000c0d03401c2d0a009607882d1140e000880c003529603040c0ca02d502c000700051003a48c40800040c801d41d401002e0fa084020a6580d0216426a010440305814011080010040140703170400034440c500c28000120411186540381d003248265400c40c4403081030707549104001d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 459263911 1250 459262661 459262669
    0x18140f06041e0e0c03130b0405030c0106090504110301050712020f0405040c03150501020d0c03031d0f030a02010c09050a030602030405070e09100501123201090605041209050f120a0213050402 84
    0x9a030000c03e00341d00a2946c204030030500707160040c03440081c101c0034a010208003002010f00449100e013140342c0c000d00840d80c9416480c40203100c2510101c8008200c20000c0409080602070503200e142c6a40b20000e6100429001c1e001039400318012034540c007000c20021410340d03640c1c8143d00900c1525600002d01d8003811829044981d029004079055521032000307100401e6102c2a40f1503050752502e00410350710983e030080c4030380040c2031b00004080d024a0110b0b084050000000d8207030505146e009101d0440490000c0d214280107025498101c4d400c100305001040300307a0025604940304508580030140da4a007000400001903d03c40c1e00c0d9003115010340e81c4031441c1d00940d80904100c80f007000c5003040e80e0b56803061022021605d880c1944d855002000f81c0b181d410001841c4840a03c02400001c80f50310b0500000c040c2110100d450106003d507006140d0b10544803002900c60161100303c01c1980b0104001c20742c0c5562105002754030489400e840140c894091148581800d007402040c1070400348108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 459265161 1250 459263911 459263939
    0x102040302030a20040e0c04090501060e010b120708060f010f02190311010608070810051305060a021903020a14090d0f050703030201360201050d091218140f06041e 72
    0xd91249091a0161500620101f2088a02c6100725000690341c08185892405401390340d00507046444103500009882440e8802840c20307000d071503581700142e0366100f070076196604140c5c0c025802800000c0394592950217618000b84500e001d00440b51196010100b003c5064401075044001031210340000c081c03040240201c00181592038007070b1020909008131160f07900000011200d80c1c6880e40e021911070078038080da980c2410340050954195140007241d00340a94081604116401480c96001d5405d902c82d2090300e40100d82941d0f100040c041c12403200c44d1940107401007580c070600c0b56500b00e0029011a00350303000507114001901c2005d01d07608000c2d08459075a00c500b980d0141000001160440c40107a001e880b03070f240440a00e503c01c036400122458020400b00d0074107185007240d000c0501c0300040b0a100c4002c0d050b80d80000d41d11300c01065041032840c40c4100c014031a030307800c81ca0401c6c2c5440c910104484001504c0c0500703040e5105401c41c960b0040c1210b611100041c10400c1c0f002d0342c001c0e1a8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 459266411 1250 459265161 459265223
    0x60712030b120a05060a050c070c0b121608040b0a181b0b03040c030807061b030506031605030a0b060d06020f0301151e081305010203070905030708061b0a020102040302030a 76
    0x901003c0d40303142c83d4a525080000d00345410755039980e0014a41034004c6040e59450340c0c100040d0201c090715203440c402c0680c810240c03c0301254126000580424110342d2005000c7d0244da15103840385c80780c1d5509040711401400350000d06807119007148200d0f69290000803142e000d06502148600501c0c01e100c01582c40b500610411002001000040358031f0010070400c480c1c0c84441c59036605e61230300b8420010090218a5001d101208441307141c0981e2603007003507000d4081241034401c840e08901034441c4051052007074940640000740c1610100701e004680036400300e000303000e6484080701a943c5800702da01180c1c0001d000c1c4004801440410031541510108000a0411501141c084540c00001da0b622000c403004004162000828403200300f0302000806620900a40d222b051000e00900504c0d80e5005042c002d2088142c00a5007000018034103008580800c280f140c1a50740b07445d1024079038041d40c50042559020800007006032000c0184400d064050040710000b150807505010a2405141c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 459267661 1250 459266411 459266413
    0x7111f03141005120c0310020918040312090314160b09030a09030602030712060b0d0e0102070b060d030c0b010b090405060f010e01081e01030c03050c0d050a0b06060712030b12 77
    0x2001409031002c02810107641040303e004003801048100580f034015440340d85034241c081c0f00c8074201d8421007500a00840349040703407808201e1084c01058180c010f012900503000441c58010000e0070511a40a105214020301d000303400c03c07903414089200e03988005001b181c0e80e5204c0103940103201c02c03c2c0d49503410000041c0598940214810020301525041c0005000182e0020105010314022003d8448082d2820402c0c451940e0f1251460910342040400b41150390502081410f02c09040c400c442d4081d500c081c000c0126111035044c0041090701d42001c400380309043c102d0384007042007640700300c0c001c010b140c8880b03642e0304000062009540004d0300660240c0d0074000303010450703a0000c1003021260707007c4c60700201c0f1343e45100d68a1241f10101c43c401940541c102c0002c0140301c1000e04840c10349004908440315088000c05000354911031107009030698000b00c0c043d10005581e0400c050b0400c500412aa05142254581c0f000f2581c000e490180860384d40c1c010000b1a040c01c205c3c011180030050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 459268911 1250 459267661 459267701
    0x319230601080703021c1a0411070f14031b0d11063603030f0f060904060506040b0a08011b26220c0311090c04060507111f03 55
    0x121080519000280000d4180145000010f0b000d500c01d40c15110ba602e400000150600711200e262030042003000402c007030a1081d401d50407140c1c00d01d030144070540e03000b40071054900303d126107840000209180b01240c045a504038000ca540004101134640882c01c80c004a0320161111030061521011104480c140b201c002000c5101e400c0106405e50b011000d402040742c0e0036042621264013880100c0e000891042d02421900c1c26034002010b0340c402c1c0320030800810592030b00003440c000242c0882e4000d90202e40310001030006a0750380c100c5e542002006c1c00100340e006200001a407544142e0b0404d22030340c0c2d55138200e5503400302c90500150f508800c5050040012490031044072802041103500d05940178200003240007500d1080032a0505074013030003100c284042501c1c1140c861855444141c404282001034100c0c03034541744005030300560b20721611600d40b6103009015203494019943c162007190001c0d1414806869891440852101d01e0400045103c00414043c04460101c200040094402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 459270161 1250 459268911 459268961
    0xa060509010305180d020706090906080712110a0b03090c18070c0c090908030702071a2505010c05030a0c0801080a020609060c010e060a0b0108090c01050d0b060319 72
    0x800200c444555081c40c01041550750b40000361882000005420302030710602d90f0607000640c0c041540d02c2a6409a0f5410769802e54800c428400e42d191070103148425000400b04010308142100c2448070588030320000e4018a5255000580c0112194040b074059207001041003481c100c00e01144980440c11102d000100e02006510684604010b00b804180112041c0070f50900c2810311055004014840007803102c4a12440d100c85143c10540f008000740c8164003010039152858070054081e090a101000e04000800a91030050114400202042c41440303c01c034002c200c0c04e008401740740e2602d0b280d19990b4280f4201c05012500c000c1001c80c100f1003103000602030a240810070008544e01100c4242d2900810400101c192062140041c2d283d86041171644c0b5128001c14082c1c41400b103d00c040020761240c1c0f00544110604550404464021b22000165076000700041c01010300303007030700001d8001e1040c000300b0f009500550f007250141000001c903001080300c1d400340c00440c0300c0d1001502010804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 459271411 1250 459270161 459270167
    0x1009051e010902090f13120905130903090b2701050c1504020114041a03182509090816050f010212060f18010303050f0d091104140c07060e010b0603010b12060a06 71
    0x60800501c6243c0520482e1147c61040002c4009040000e00c0c032019001a036085600070008900f0131030102c0e0520000003000c480c0b50b002e441d01c48090140b8100b00003000c030a0b0821000742800351505001c0c060040001d402c03010420402c05150015040f00701d818140009000000000000c00002030200828000c240e424644d00b58503080440040c0d480c7d41790188042688080d00307003080310038803038251459000c84103803020040c044030b000002010030303845014140964103202000352000004000012200441c10200030480f8000c500740e800d00d100800d0b0150981e405166040d40c015030400900c122440c0c03c2030710b50101d2108980c1c9040c0041c0c01011620208014070000d4144140412840d84484110040b44c601070700300c0d5020019002c140c40e00100b94101c0810030b40c025458459403030021580c62000d2405112402e0b0141d00341031599540001409090113240fa00d9505c421440c03180c1c3d103804001c2d50280c1007944056486020094251201400007001c0510070169400100712030360f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 459272661 1250 459271411 459271441
    0x90f0f160b13030f050d0e06031e0403020a0821010f0e04020d0f02040c050c0c0d020913020105040312090501260103140a0b090c01090e01081009051e010902090f 71
    0x1000d055507500c42c00c0d0071207149403112060340003401032041c4441c001c0c00c100b4041020240718009803070340e508544c00f40c800d018071404220384002c91560078030442c0300c1402a04008030f500c14800e204403405080a6a541140c5400ca030082a214800110f05503000300140c20f00d00b400341c0119910040c0c258600041e115800030082c20285c0900c071140c0c3c02d10107201020410042568014000340305a000d581002452a48105040605402140d282c06007a191160314034410780e4004040c20000e8681131040040b540074040c08034117001080000100103071f02c90804450180700e546407040308a10341000506080f180103074001c0c941101485483c100e08410a0710390540340c1205141400c070042d5a495807822403200005809461040e0400201d08000120b040a207035081c0e0740d91200a5446c4040103800317200303000e80501c0d500000313403110044a070303640001a410b00034011118010800307184038208580d00e07400c1004994440203483d05508100c480c01e40c014441d10106140c0d460b216165010000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 459273911 1250 459272661 459272669
    0x1140610030e0a0c0807090b040b0d060b041410140114040b0a0e03030313210e04050a02071b060305070e0f010f030e0d0c0506130b0f070c0b090f0f16 66
    0x180d980c004a050102e0030040044410b6101c0050034445071142c031000e5a403d458460300c100035003401840051814140548400600045c1c02540d8462141e0b4460002d0003400000c81e40060395882d84401101049600d076000c0e2450300600301c0c1040c104000d0303500340d031402ea41c0141030021441c8003d02c48108503040380c0842d010340205c152a642d000034212440d000c40314089a0500c8080300307003c00c103c02d03032842013441031080c51100c8501a0f0365090725641e00750010b410001c9040c0010719189418150050f41d40140c02c0300c0011314002150b50703410005280801c1c2c1807500c2c1c459580500c0020b03094811590006060f0510282e009a883e0008144443c10011641004002810215014040c0d0040e00646070203c098900000003040000c080420100045e0b0f01407244501282070b001d60729800f0480c054100d1320801165440c030040f40c81804c000342c074500070040c1c807650080209486903011030058007210003a04a00001e4030a0230301e8896040d2051750702e80c0010200207142090511a50304079 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 459275161 1250 459273911 459273917
    0x20307060b011b062c030f0f091f030c0c112107060203070227010608090313060f0e0901051c23010207030908010c050403020409050c2101140610 64
    0x44440c140125203c00b0581201c414a40c514181c10080119940003c40d03901c80480c2c2d0b0aa210340184032240c0325038802da0030000d06403c2005044140e0b80110b00608801d01c0102c01e440c039115000c804182c184651103020140705080009202006505004401005640d481c207a210500b0079181c00e0840d000c0444554402d508070410a5480d2040100c1d4644100402040d100c08030f66964001c4d4803075004050882c424040300400c014040d6080403200203462050b41c41042603030030004252105c9401070450000e030310051081841c24508014007602900c520380e91000b03548000c10018110054040c07000b48905200d0300180403a0710340c800c02d0400325100345030190100c085800c00030030a401ca0f491001003100b4503203020081a00c150000c004c4503110b640c468000307035a101a400c2c04c940840c8a50760015804000400161805410085107240500191540009658009600c2004a00c601c0e2040044884100d048030300c00e1007201c11000808090b5140c1d4940440014400d10091900c00e0034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 459276411 1250 459275161 459275171
    0x50408191401060e01140a14040e0a0c2c0402010206070302090f0306010b040314060108030f0f0d0212040b06030c01050d151a03010e130f0b151519080702030706 71
    0x1e01401c0c408001c89201d0040007007200c07a071100f101d007110640900407604c2698000f0615400360030040d00c200e040319030107403010100600b104100406080d41440c0e170b00b05071242606c0d6101003414601d66400030589050700c0580b80704094500d5850f17614a500ca060404c08580801000d0f036000f00e0040e87c0030201d403500603540e4229030300044140b6140f0404507017510410002040c04211038009000780c0c0c7c0980c1d25080b0700b200544002e50703194800d0045100c1038000780454148442c100002d0141410355502550a1101d01321480d4120303002030300c048074034103400d100380000d01a604240381d41101042c1c004c0d00010071500f001824601c50100c082c0952584d641501e00050050402403018081c1000d14200154001c1c0300926160028043ca0052035400381c0801c654410080700c0841c469403203050180030070382c241c0b10441d00001c0240705003014454450003103419684d00042c500040e109241e407684130709441508080c105004555181400811030178800720300c2e00001030380c00141c1c0c02000411 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 459277661 1250 459276411 459276413
    0x91e0504030504090c050d0e030a02190f1203020d0609061d0a0f050403360308030403020c42030c0f1204061b09150e030f240705040819 60
    0x4481c4540d80c42007400314075000717049000942c054000c014007024482c06114900001c0c002d69201d101c3c0101c01d40141c0d01c03071695840038200401202c003449004000700b440ca0038240d00e9002d101040e0b5000000044e500050105a400c140c0c4503190180c034a820040181710305020700030740a140540c040c4940c8000d4080001c3c040035098004a1030504418020710280c1042d14004c2c042c82596605040100b101d00444000c03044a402c2c0c00e80d500369105d5080503aa8a51b88603004d0990024005408601415000c0b004984035090002064083c83d1640c024000300c03002c8468480e503071a0030440104045c1800420200c100b50150380d00011620541d41e6640d4070012075503554410740c515140720050450410052000c1503201011100c80686002c030f1413100d17a00101c88001c0b141c028402c4003410f00c0d51000700507115455045040c00c3c050104d40c40ca150000805e131500003082c00d00d140c0381c0150744c3c01c0714030b116480c1e07030881e004940c504015040504000709180c0316030f1440d550b43d0008141c40d003004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 459278911 1250 459277661 459277667
    0x60906040f03060b150f0a141b0706110f0a060209030709060308120702010219030507030e06160306060516021003140f0603060114210307080a020610091e050403 71
    0x8000380703920795001c44000d9481c90500082c0200d04801441080c0042800da0950000f200f2911407030b1045a100703141c040408803c0d0b40b0310441142940c036002042c010400b02038100302504d0007655160008103030862901d00d00501c800001c0f01401141e4001e2800c0c9051a000001d80d000404c0e0301c010003586507412100440d1414160703500c442c031410705201000040c000c1c68001041c681c07050805000c100c0d524143e0581c207034420403002d260605072503401204014031039400280c01c800c403481d001c241181c00c00b0003240b41150070f071074104030502c462944210300358140c4201c0004010328100f10742050b014180c13420507000400030281c000c10b000304030041070b640710b98448200d840141f65002c18030304100084650b0003400700c400901a208140c00420078078040d03094049540d80090094105140e80341440701644520312150503544401c1c8041c3c00060309a80280170350142a034010400c61614091a40510015a0000d025a4a80301c0490900d0307200c02c000c08410f0a400c0d40103d425280e41c5000c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 459280161 1250 459278911 459278917
    0x1a060111030d0230190e0a0305090a060c051009051905030901030b0f0f0d08090301050c0d0c0c030801140d050d02030a080a02040806010e040501020c03070f14070f05060906 76
    0x400309000000d55441d040280c1c2c0d002c3e285891030b12400c0e80c5030350700e04144140342c0d04503280020080840c0c0c10000703164014102c4400b407000780442004c1940c1d5080e860141c60204a030008401186006c1514000c0741032000701000100014907055207074001640303403183c8034800e202d1088021034489030440140a8100640f0b940041603000301440103046040003500c0f80c018941c01400241400f8020784a0310b0180000c900c3d2440003428003180302400400c228070701004040880d42074000b404000140c2d6003c0c03168911a000d01441036507200d44489180040307469020343d080901c0400300ca0000480d52110030641500c04c10781694014107800d900142250450143c001c0c074a110b00d115004da0940d0120180104c07219a8840500304c0d164101c817002a40580c1c0201030350b59110030f00401603000070b407046581180c0500c000500d0200d45030310850031580701203001e81c0c1140d00d4211100c100004415007102d000c0f000d002406040342450328440200030725204203071003002c001c500241c0396a2120b0803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 459281411 1250 459280161 459280187
    0x809010615111c1e0f0906051803060708090d0206010b03040b1e070f021b03030703050306010c0b010308040f06031503030305070905060d151e03020907030f0207050c1c1a0601 77
    0x3100c1c1d9040d83c0b03100010b110103060346580c0326003003051401c1090700d806401c404a4882258803180303c00b6003800d200710b506030400e0b40c120401e00b1000d01c004105860138030059000e40d10982c1c401b0071910b4080e008034581000740d051303207007154080001040300507400d00640c3d81296104540c00d085498031002c20040e41c0004000b01c0d00c1601003010301515640001e20312850f00030513003e403802400c008545c2c48603000511902501a0020041c240010748240300460380010141030211005040b40c8801d141000244c00803604907500103802d00c11000d52036032000c010181482c1c01e00000301c2e05c4106440552540c4001010703d5154000704400500070b140f40d10142402034503003900c0340f0740310b00094090402110a42c504502e003200106185406c0f058500b0b050b000c060000201d54650342c01c0c0540840b0007890b00007010707a01c00e5007101c00b2840380001c04d030990045004126846012080151201100e80002040040c42d4000d070b000075000b4124011446403100b4100c05980d4080040e40c2e00c20500c42 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 459282661 1250 459281411 459281443
    0x7051602130e15070306030507120c18020c10050c1b12070b010e010803090d150216151a0f0609130203091e152212050703080901061511 60
    0x190003000c03040001a01d01c07141d43d1884058075582c80e0880203a0441d0320714003001d0643d4009520504c03003e00c40301086001284240d10011100ea920607900c520451034107441d20300182c00244620302070300104000c2c84c480d103c00304100a81c0c00d007495881050f2044000d0640c001e000c4c00f05074645000c051115000329000e078100c0755a03d0783d0525104600b6003090145401e250400130000c1911400082a2106211701606032100b0224944071141c4c99601c610301c4000c13082e001c1100039010301002d60500388403031003141c0c590981c085a0140d00b09031141c6500341c20281c5080c2003181c0d00d44d90341d40024001e1003001e1711150358822400c0003058a285c46c40580610050000042c058065000200c0c01d080441121521004202818850740ca030040250305a441d0340070400420100403955118500c05c0782031403000941c410f19640e5102040c09002400000303c1c201080140905411250041c0d0041444008020660400803224080d049a0328008104411000140406001049544442c041860b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 459283911 1250 459282661 459282671
    0x30525030f110d0e2103090a02030307060c0e0904020105180616080304050706020a020a26120d0606050f0a0305040f15050a0b121e010f0f0905010c05030705160213 72
    0x100700c500c440c2d1110241c0041d113841c007014003480f02e02c00b08950f04101c0b01c0e4600302c902e0040c4080800900c0c3c10280225899000785c64104006a030200000e0580354418000442c0700041054054580c511050801f40140309440400005030ba002c000c03144003c5c0c4400700d24520588403000f18200d80a508440709003008080c40c030409000215002d07500c00e42c80b9500700c0742d0040d01e407207040341c882d610194002e405c01410305041c4016041420a02c8078202610076080484d004a030300107180000025100c500502d0014079480c1e5000d1900511024001742c1c00c1091030540d0b4454041d110340701d01d942503403c260740c44c4080b60030030941c00500c00c12a5040620000c07480744030001400180390179178820380d000f45002c0c003502d0503090940c0a01c03088146940070340b00064005805641c01c84217031031100000e55841810b100d40880d644903800d0b400740d0744000000d00000c680b80041c03c5603100320a44040c04030510070018416880000c9600d401354021320586a120213102046e520080c0454203070320b06040c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 459285161 1250 459283911 459283931
    0xc0103020d020d0e010603171206040c030b030a0b09300a0c0c080607021605060714121815070c1401020304031403090a0f0b090409020a1205060a0c030525030f 70
    0x15002601a240559525003403c8410100c0017400d100b41c941c8800c003280c5c89c02c000380c0649400c0e44000940000c43c10080361802c19000042c0c2480031002c011201c1c0f001e0003090100516040001c08440841c050441c802c00c1c14a00d41c104500326a1a1040c003118000100b100d0454441e0402c8224258850703024400141c440401c00e03220881100d2100c010310400d500c0c43d80941d00a80228210307540600f10f1440d10099885820543c4061943c07120944130f501c0312220140d445c2c10080c03800c103030000d00c11500100041c0800440310340309802400e01c0c11061080d400410600720b40d41040f203010b82107900d02d001803040143d05501460b0f00c054001c00802c406003500000c003100424440200b1501050a6611081d400b00303406da0600a040e0028002e00a03020141041d80c4141681c034001014044e0060361981943d80c80224624200c69a400c004144102c0350100d0042d40d401914a040a000078a010082c800c1c50366804138550b40e10300c140480401303109029072b10040b5000b40c3c0c49400e0240c4480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 459286411 1250 459285161 459285163
    0x20409020f1207030b0c0703090302011d060f0414121e0c03342301090b04141c03021c0338010302070503070f0c0f0905180a02030c0103020d020d0e 65
    0x20f00c0c07000740c0f407032441400094446a1810f04a51985506480c3c4910081c15074004464480b20400300001c03000711484000340980c1c0343c00c041c1402c10b07148102246d45034184450030710243e25000006015948041201c000004040341043c4c080101620400d0801c810080b41860b00200041294041c040c80030362010b40813140c02050094907074035043c91250300a001c9411051815441100038601d0014858140d00d0500380034650807210515050911a403500c0040d10550300941c0303c8040c0c042e5860010041e0704041400054800034048003141441c12514003940ba9070215190054601700090241e080724020341c84602441300b03004034071282c4050300308001415800f1401c280726050f80f0000c2c04050b076100740211152160711002079400c00381e8698a440e000c0c81c00480444405880b19030204d000942405000700a106034070000c500760510610340e9001d030581c0c104c030203031a4000488010261b180024040304052080c030b00160766001104241000f8010244202141800c01411840d0110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 459287661 1250 459286411 459286423
    0x38130b03040809310b030705120601150507050a0b04060e010903020105220305041a040e0406020706180203060601120615050714010605010c060b0103112101140d020409020f12 77
    0x100588164141402e01e0403c1c0000e00b184ca201c0d51010a00401e102100703108541009503180c9000d021a805151a0350010716071200a82d003a041541c00100100408880c10401e5000352510303081117482e20720b150312080c0d1682218a005002d071004070000c2801c10903150f100c8400240840700030801c03d00c05140c024045c20040d14150800b601c1490301c920404005c0c450740f0611549a10f0741c0e80707000e18000c8115400a141c1541c3d6000700000c0c04009040030785154803d100d0361141e480181e85050514003841114240c1402100d54681c0d03901c0d00d030058034005806a0800000d08000c640c41142c1203045015281a800480c4480c1e0384907500f81500390400050600030b8426805003601f648e540955500325405449000e00155800c009900894003990040c0c42500e030600d40131440d6485500d11005643c0001c0400022841c0c885481c1c0d1a004001c2d0414098007606d0729449080803000b00080a64020040c0a80304035910607034801155030b0004546100c5001621480c08214a42501740c0c0307680c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 459288911 1250 459287661 459287677
    0x6170c0f030f1608160804080708040b0a111f090222020903010524060a1701121101030b030303150d0c0801050601080112240f05040c38130b030408 65
    0x82c003a5000c0c1e108a01079550726128a2030541d01c13017070389041075200311141080079100f07407114407040001d0800715512000030009458648401c99036148580c100034450b445000008485411440302488060718070102d4585800028102042003107450000440c82d00210401000704e101a01c8002800440c68014002c01d602c210000c220581d01d0310150610551403003c041c0b001d24600c00300300204e14052019051010048ca412841002e900d0026400d000d0280c005407800049400b04100700b1800c0d03510011041000e180c00d1026403010300c0403da0361b000290a48600c0c0c5508a05102d6a031182c0388855150741e040340811400710303075036850607009084c15600a4002070700c490001c00d81c4034004100c1c0c000d0680c04a540c4c1c1c1d2000d000c442ea1400700b9002c85a42040c55100c41c1500c417004214010240114051581d242d00946003050400f01595842c0010350107040c512070903454220304580e0b000511328000203466903400000441c810761711180d0000c1c0160400071082c07100740300100002d00600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 459290161 1250 459288911 459288931
    0xd1a0a0906140a030f0210051209070f09021306201504020a05090f0406020706090605190f151202010912140c0f0f1e0a090906050a0606170c0f030f 65
    0x911900b414000018028000031340480d0403108810300500700314450344903941d070303500d40302d401e0480303d0b1410461800181c0365407030300e940001410f01c4040d600000740b03001000480b0045280400150080e58101c0991040e902030000c03540c102c00c3e140c038080104400c904610001e882169100c074809a1140000703071401c1e03004403000d032004200d81c02c081d14081e0088080061800d184e55071a510b0602030b601200007200c030035456040110026046024560081041015500012240d500714808907581e11140302d070460300f4103202c1c108080c16890000c042e10780ca00400310080340c107400140c45440c199480a4035900e0511862018401e44c161301001a80640e0241c94429540c0400c1000414a07400d02c0e0703500c03e026903000d80700c03490100016402403811040244141441d900060008040c55000100c043c3c0c03a07141703034010005103200d015848490b030001040444e003000c1c001064020200e440c1c11001160001040d84002d40106507211b490001c00242d80c2c910740f206900301550400d991988107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 459291411 1250 459290161 459290189
    0x11220c0206010e011208040b0d0f021606050f060a0e10030c0816080c010e0105070614070201020c0705030d050708030a02130b04061805090a020706020903060403020f070b03010b0d1a0a0906 83
    0xc045602d090848025000142d0a0030141003100b1400326270321001060034210b030340e1442000c0c510824000307000e0080c0b042500d090002c81c1e030304101090722002020030f030102c1d5004081000b80c0ea12025070005aa00d600610880d903590000088440d01960304080d0001c2035804001401040000303642c5004003003104010081c82d81c07540c443ea9140c103000e202d140072510a601c1c0300443e5200750007034089e00340940d1010031241e42c80308041485d100103071000c0c00140d4001940401a060030030410005100580051a00f1485984010b1243c01007502c000c05031000040030415003070041e01547c075104c05800c00e00100c0d699610608425910600c1400c0c003003400e960f11281410148500c0000300c40000d0003614043e5240900200207612036a022580783d03909210318501038030108142c0d445944a03800400d0107841581e0540d142c03102c1580030345104542000188100c1070b180302560944550030304003064103101d03265141103070905101481e8101c0003402c0d0004580405820980844010340300442c0d07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 459292661 1250 459291411 459291419
    0x605040c080303150d23010506150408100c05190c0b0114090c0d18080d0e0d0e06031302030a0c15020a080f030903040f0305010603150911220c0206010e01 68
    0x61640011240e8070b079140d402110b13040c41410a0360082c40d1581c4504510240c0e4601840541d10b0203007101900c918980d940c10400c080d0382001c100900322241804450390500745408e03042980d031f24a1564400c8603940300e03203d5001260148041d581254200c92588190703000c440c0009000c1c4105907015503014228070000552001504ca2043c200300e00138041844030b588803c079100c134a50000394034508407696240c802002858800f030711085948241d409550b289148583c42d8240d0720503400009650300000205025250050b0111066640075282141c895440f84031440032103d460f500a5050300442034010b042000c6020a481902e500141c2d440340310008010407079030b44030b6020f0020814481042640713041e101190185601c6410881140e2909482d104989036103401079100f1206691034103000d00400c0b80084210bc9000c010820401544409403201d175844d03074013402400c0c0282c0022001d0b02000d0005071000742c031410340303440c03e2018014004009580d04e50074403511948100c9000040b0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 459293911 1250 459292661 459292663
    0x3140606010c021f02101503020f030d0c0609021305070f090905070c0b0c04091d0c0301020708071101031407091e08060f0c190804060506090603030d180602070605040c08 75
    0x12960b15000380200d62524042c01d40e64a00450080a9105500c03800059403500103403409001c4450050000603101c1510b54414407888281c0c818455100c1e400102d602d10186900280b445c1680b17400c52000701c1e03140d03442e00215054031000d000082800d810301e000c0000789a0481c82e05010030956540741114244d46501c14800c4403c1901d1040c006918001d080020454010200c0d0b00301d110300004600d49595103800c9005c45242e00d0b56000c1503c0e074034140e00054013080c800c0766180082038000307520346180d50781c0e00e50303442c8038082d001000101c50a0403210307243d01c80c0e442040307048101140992142040d0340d0107881000a0312541c0b10a01958600c40c1d203a0340c160900c10704540d0664020680307a15040071800305404000c0440a500009020350b960002002e60944840001d43c4c9070703201c06061070b0030202d00780c0d64010140d90140790304105022550720000f046506181e00139100191481c0000302041001c0011000a4041400880d5600600005034400760240c0d2050302149030079641c411a076 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 459295161 1250 459293911 459293927
    0x216020909010c05032d180708010c0206060d031205010b090f1c0305030601140a08010f080c030706050c0c06032401320f03040b060a120c230a0314060601 68
    0x5000144d003e10215000c2d69044100c2e0500030190716440e00400c492807020078642000f1105101c0c0a040300641074820318060080401400600c0028030243c0007424019540ba6030152880303020b1030030350005109140c416100309030308a84191052140d56034400030750044d5003050640c584500380040810100e80313003d00c0c8400381c5070544000c116040c04652000e46098000825103410300c88400c500c2c0d007034000000000d200b400c1650311041c0065044c42c8110742140203941042850f644160481c440d59600015800e007140c1d003a1500315a6404413000071400c100b03c1c040c4464202e2404800c1c0500e924440c026955015510829443c0243c688401111686600303503100c100039650899007001c003c40c184c229101115013003c028986450000007a00e290310481d0b0540302c4116017024401039103004035600c8020520b8032403080300c0c00c2d880d442d10a0002c115110700215181c010300d0342c12150440c1d00c0110059130340140810911696403d0002a00c440c86002207418020380f80050410b42c021300c60 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 459296411 1250 459295161 459295181
    0x2010f050c060a020904060b03040f1b0302030307120306090f1b0507020d0618020d060207050c0307050604060810090207032a3f090315020309060f040c09021602090901 74
    0xb003003107403250001d9500075403010026641003501d585c130100742a0000300045008911504910610b10b40c1c80c203140200304174442c11001459074640040004d60303400820b4910181c1c0198003001034400c1d1090540061129510041016040c00111070309034103594019100b07502021121347e07961b1880c51040b100c512412100a502c5802e014044020070310503406811084500b0700d03010000682d94001a1428401c51022a09140c00255031401c000082c80355045940013603009005403410600003880ea401035014075000c1241403000100c2c40240134141400624100004560321211b90030010b1041c14054031103159180780500b01c0c00010980360030ba01c3d88a41044080441445d03e9420b400020945003020429942c11032686035114500c1880c001014a6034a909100034513628010403524524000088241c0c81801040202c00b400b141030340c0d00c000715842c5014a030f038072403420009550542c0c011404040c408540111401c41c00410305c1c0d540c038000ca810742c00710b90310719191500380c40e4aa09 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 459297661 1250 459296411 459296413
    0xe0c130608030307260f0a1506020c0f010201090b09010615050a02030d0b04090c080f010b040905100506010504080a05072303070303050f0409110a030e0304061407030c12030902010f050c 82
    0x50b030700758440c0070714190102402401240b551700440c000111404142d0381d030985e6107440c00502003201080d115001c286150100c14000f02841c021003e502d60010240050144080701c5000050303a20030343c006e00c18550f11220040071400c017840150b008040c180120f220550800001840f6940031b02d06942141d40c0b15070044d4606112030040b0f10180c0041c40c9600e801c603841d03020b00800960100c14480141c035240300100103404181c1056401e45e100e1214450140d840c0194400101d640480c0e6004004007420b00490740e620744030012601c0f4415030344844200d005032007000c810040702050b83c40468490600c005c420200141c0b06d04241c0310304850591389136200302c5e02000001c2c00340000e0310100403c8003c942c102556081c200050365001d100400600d040050040d16440d091700c590070501c0c000c28000d500303203410320780f0240080ca500c242c2c6403100c80000c1035050801d071059038429502036100b01c0e08240e031413050201901038410600200c1c0880c240e008409031481c03240c01a1686200500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 459298911 1250 459297661 459297667
    0x4060c180f051e040903170c0a120c1403040b0709171005060a0b0a020a020307120807140321070f08100e090f06010803031b03060a0510120e0c13060803 67
    0x2000c003e0004003401c01e890101d41d00001e06400c0303681e5031103801e082e607010303480e40d61014541c0d60303144080c444000c3c13000c440c4200038000d101c510b56004003400d103401c1303443c603001441012400c020766240e102044200481800041040100300441c81ca8a000305555282e9016154844003e003000c1c1d4540700d0604107541c0b028070039020444458200a0304050081c00c41c451072511030140000c10350040c0364103030241e88046512011414200701e0032000700720405019800c4409075952140324801c270310000e425804c80c00c03480201d001c410300c2141c078001da14003120704901440d10a120207904e000c4a495021400c030b0003400900c0d1740074050701882962490200c4607240d0400c0d008115404002d40914203a101c1c0040e500d10b241c604101c000c1c040c0c64100300843c0c87e8035005801001000e5000d100d10722804050003400101e44440400c801074903c204e034810222952024215034010b0103901400c010b6090980c695103600000c150300e9212001951701d030100c040c11060903c150f80e2680720703041d03c41c3c2c010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 459300161 1250 459298911 459298919
    0x60405190510050303040617010905091f180f06050f0603100c05040b0406050c12040806010311130c121113030201080c04030c06200607140c0a050604060c180f 70
    0x241d001c0703a070080b85080050710b459240e00109240d50081d410490204041c0701a0003203910b680c01c09280140387c0400148a68078188141ea611031042d11200c00302e0f9501d1010a00700700c04160000a4190070000203402052001d040c4140302c0c00d030100040d40c00031b1034100481c10100b03209035000d00c1504082c000701050450021000018482d40034030320100174043c4400318041070f44100400041c9120743c4c615440d0000817640f01d017001008004403540c000100420099004041303001c84c1142c0d0480542460b41120b0f10104456010070a0380020761490b0200582e000fe8202c488034022601c819030400044038900e440040520942442d550f002840900408c0103610500c0c48030781c054102e075140c03420a543e903558240c80410a4014501144242030320801355080020081109240d80d00108420308110f10701405091941c000105101e000003590078442c1000c001c9a0346681c2d000044604a10b400d007403040c02007002c400c0a0700003518100034000c4c02c1322180361600590746c200d44110b186500e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 459301411 1250 459300161 459300211
    0x207031b0b04120c0b150f0102060108101806090507060f11031b01090807050a0b0c030114010c0203121317070602250314030310060801141c0b01120605060405 70
    0x40182c0204104c800304103040010300001d8028007941c06544820090310030380c0d0801c0030401c0900c130520704544c0f10100401000800180000542c0301d4440c00064245001141190f840d03000c840141099080c2039a020800000081e98011200c9580c0ca06041d4402018103c43c040c0e0310101a028940c4140300101d01221001102050740508a0002419801941c0c1d10718950b003141c1810b98150b004480c0c6402070041802c2602d03403002551907001c0c95903041c51596804104590715a604024012841e407045440070000c0018516a41e0910358903192004a801d1496031540603203800301b03035046044810b840c0d0014861007528040d8010346514841201016411390340b07041303c840d0403010b9080020105038103504010381d80021401650350b0b45414011480c03100c4856224008000b0001c004000d03884120b0300c0f0368513010086800c485040304c0041109001400c0714009004118108000601d1a8640c01c240500d944a030105000c590703145800c000481d042202e0102c511641c0341648004040c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 459302661 1250 459301411 459301433
    0x10b09010305090703021504031a0618090c13060501030f02090906101704030309110109050f100302070803130510140406110c0f0309130b031915020307030207031b0b04 74
    0x14050f001c8803c00d564a400048442424080890700b06000203024814881848c0c06044140010106c0380700c2410b0100c04180841c0d40350806a003442011310200340105420b20111201141c010041c41882601510034001460305105442c0400c0c07429010004000301402034410380e44006041c401540d0340c02041c41041540520610200201d0503401c41d11101600300850180b8002e83d400550201d861524040000361020b0b104c0c14419454800c01040c0d441400742110001d0a64408135407038502d4005401a0103070100087c20340c41c022003005660003032408000c1070b46000302d0840e9005640d061500341210158104404900804800180800c1042d0010f01c440d141c09482d00d8642a16149003074201114060100480d410008900c0d900780780440070303001d107056041010019604005c00195076000286480c001d000758082400083c03106502d603001030900440307029940c914041c0c100800079807200a0850108510300c0041c3d04195201c00c0a01007261302c4031152000741c541c0e407a0664045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 459303911 1250 459302661 459302671
    0x17030601050f04060302040e06040e0601032307080c1c0302030307030c2d090506090a0e0a02120c090901140d150e100f0506030d0531060f030b010305010b09010305 72
    0x801c1c10460440a0010369004000070a859074005880b035081805242d414500500110b10a60424603c040f40c0e440100b65141103aa01c01a4443d1403e0851002c00750411012880c1c03646005a020015800102090050b10200b08540180d0009181403031000325189845003c0c005078814000201100d0003540a05924540760a0411811006105500310024024000400c0c5100380389000701050b00714840c0f0000d448111040e40c1480484000300c0c0720201a48031740020300601202003000c10450768101c9047c6642d240700855646030403000303c0c0499201d45072180c00f48030302000006080d03200428142c2c1d2210010401611005107468840c05001e15a1101152555030785681488540820900c00040000000414044200c1980508540c002410140242c000e000032060783c1e940607080703a03800010041c1c1000010721030307a4404c160b092420307001841850101d1000c10229002103052540e6005564240310f5010508011401d4500a11a03040030020501400c10998069048103603c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 459305161 1250 459303911 459303917
    0x51510030c06120e070803120a060801050709060f091a0a2f12040b07020603040c12060b0f0f060904020706020c0102040f0806071d0405040201021c03020405041817030601 75
    0x21903101c0d2540000860507600c1040820101c2c0b03103200407140395005903e1006021009400082d281c100110386030320840c0031451070076400344001400c0d0b00265001c040502a800d00030096490710302005401c40346240038000204d608414510100b5100d81f0412045c1c13440030082140000c43d036096450503800c015051418000c01c18041104041e04030803808034501c6108c10110b4030608080e0300c1342804407204031000c801360200014405080100110307440c1c1d69068440c155a603869042641050406030044441c3d2003c2640c1841400b002da08000f92840e81154a000f842c0c501c88108140605000300c41034020350140040d215524003030b409000502d010303200261410802c000e11074220b070301c280c02c410000d415a140500000d2820019a5402078082c105049824003581f42030404058103242c2a1055845000082c00c40e4401c0c03000c40d000455131700c0c04a49031180c060f00500a90070502940340034910b04100250026101198450300c03513042820180c844012441c64296584010029414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 459306411 1250 459305161 459305191
    0x90b1c0902031015060e010504030507060f050d05040501020d050901090b0c16020a1e081515012c101418150403030c0b071418010905040204080c09070206040515 71
    0xc0309030140544c1281d1903544e40105502c6040000142480300c4103455175040000030301003840005c030009100001ccd074900e42810410300303e0840084a0620602561904080c1008207020400c1015006845d0810b0403d03010310a81d550003960710308030f460402c0081c0542044034003046040d03076140003c08520700107044060070100c0980108007500c0d1a03500420215042000c46190040682c0a01c000741c000320002d0440f0200c41c084a1b0500d4030090b20281d0a091a0012240117a000341040a4200340f12403110440b02d80c01015010100507078480f2078025001d00d015039005501c90380103800082c501030401c508068a01d84900100c000700c4040540103000141d420143c41507200140000710f100c0c0e40c07407205819030b0745440c03046104007800305030510003244460612100315606540200d00c0c440d00f040031001e0f4141c012241d0031203540c8010380045c4002804070b010074001c954000f001805940240e103d0f100c2072401c0342d481c041103a0203041e41e00170358042d000e00059240d20740c2d0032045543c0c45141d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 459307661 1250 459306411 459306433
    0x702090f0723030a111611062502010f050903030d09020604081504050114070c02090a0f0f060504051003081207052a0f0c1f230a090b1c090203 63
    0x109100c900407106081e540c000c42000701040160007941c0a035013005e04880c1c10580c50b40c0c2e031001ca400c40000010722a181d0301d18802000c0c2c4550043d289000c02148280384400d120180c0d030300400314400016800a5004010701180e24002d000b1120300c104003030300644c81e00590349040402444064402c0b40e000c041044005810003041210327107010034583c440c03042076003001c1c60102d003181c803040a41134818401008000d0400e4100c1c1c9041c0000360141e6803070704070f5901c0032802c20041c1101076a00c0407051400c0c0e050f03400011140d00c0300040d10400d440821003901c03000318403425102c0034031004060702e6041101e4a8004041c2d4041a0090f0803402c005080c81d0651780003a40d07010040c4103c1c1e002d25511212002d10746401c03c0815940d1742800301409800c0e8540c40440e08141601a0051205040c80941d4107000d200e10003529454044070300200321a01000c00d45907031640001240400100342200114144800d401150070f4988006d039841610140400c941d00540031000c4180d0349130040c0385100c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 459308911 1250 459307661 459307697
    0x9091107060c080717010303080403052a0c2b0f020d082b0b090606130308070b0403080f090c09100b070605010e0901020901020a020d0c03080d020c070b0702090f07 72
    0x42c0038003005460748038042c5840c1d100103006441d56660f5800511050300104040b94101c00e125800035010702d031540e0b94005110b0090103001d4903d40c07c6071444610840b2145150700422049019441142d03207180c0ccc5601c02e4010405500c0500342c81001e00030f603442040000364850b41c21503110384081c0201c0c0c000f0381a030306d440c0e640f60061076006080e1600c030529100c095440c1005203060b0200d86208201a0340d12802055805000070302031801802d00140341d16850349154281e000540d4006000d0703070b554016103014003844a05a0341100401d01101c00b10355920340c8072140381e10400b094002801c802d401c0c1d004004a01001605205160740caa10001c40c1c0c103400c0c000140100303806204007150652410035900f21b8404000c1680382541d1061141c8a1141e901240100c00d65404031034102011015007800c4624508a030b000601241300000d401182c804650007524500c002c2c81c081e14511f5664001c0a1800d118080000750f1040d088800241412014802103400c0011450300e414102c1e0300803a04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 459310161 1250 459308911 459308921
    0x3200f0715030b0d030503070c081306020f100e030a03020f040e160e220f0b0d1505011d010303080a090c0b1c150303081503070e060f0a03030909110706 67
    0x1020121030021055441c56014010030507218002d440a000c002c2694800810a000140c5100c1c00c110010b20800e00303000c0c87c8001c1d5046401280010010503596503406541c0d0001555817220700c0c0288600d180602034103104950710551000055803401e1042a8110001d600c0225088041307102844086084211007140d41e2181582201c100c10000018002400302c203940da04481c4100314083c080012100c0013458214818120000850345410141c46400905904050160400500001d031014405030030f445c1d42c4080d500007000c10059803100c810350f801c0045d0b003c0045842e0380c40c100410000e40305020b00ca512806804001520840f20b80c0e03000c010032420b51000c2030b0800042110000c1d0051408002c00d034540100040042d000840e8403074080c6079071880040c1c10f100c15500010190b0500900c0c41c400c005001301990030094454868013911b0340c0035591a07004840c0880c440d801030070607410020640e9016283d204850f803070045240d015210310701d901404110309100368030000e0310f03074064 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 459311411 1250 459310161 459310169
    0xa0210050106090602010515060d0c0e04020a0305160503010b030f07030e060a0c090506130611070e0405060a0c020d0e09060a0e01090c02060907140409021c06090b070c03200f07 78
    0x3815048500e031044c002e082d900c01a045d0000d0120b40850700c22150350f4035089680324514000b0101d10740b02c14500981e072110581008030740050001401c404180c0d81580003621922200088268000d140e000845050109000b40900341c036040012075007242020740d809031701404034900440c1600340310000b141406001c1e104060b98503119220b01c01c4603600903203e007014082c1138510310708050441409190341501445810300303026000145002d0b04400380031000113000140c1800340f4a0415140003540c034182103400310141072402014003025407003c80d02907842c07110340d500c2a00c0c04501e1000c00500590281c481c40d840891141c0010381e0b900038406480c0242401d610000e2007001e04d00010382405401001d01d08190031584003440f0040c4076541001d1001d2040d100010000140c0c40802c40100012203040080d84032404004104200c0d134011071803841c0b050200020380e8440c90b43c1030301c8aa02030751000300429013503003c0341c1590341d00d00030f00c214030942c20b41264030f01c643c18074103142001c0660704 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 459312661 1250 459311411 459311417
    0x7050604020406061103030406020d0b0d0809010206131112010f23090303040c0312032c01060501050c0d030e100c180f0b180f150d0608030309030304080a0210050106 73
    0x1041105500e4548103c4004180b141402c10702228a511425128440148000c080640c080768046100841740d100202400000e0460180d142e42e42c20504119089100600c2c018032170100094040d208032851344001e02d1b07102210180b04401c02d0100314481c92a031201c11415961612250030284050041426605001d0001400c903403040040000000c8000c1048203036500800900001914501031001101e0f004082c0c048050b04280c400c40160600c0710701c0783d1101c0c101090707007c82546201801e001030355000000304807140c0e0381c20054410307008003600c6440d1074000c0ba140c881e0143c000c0c3c00141c04c40c0040d8040c3d40381240340b130304010100e030b8044840320001060fa00511041501401c440320282c0103803e00100d20600d4614914800c0c441c01d9040e50103a611407a0034542c6844183e00c81c0c406480081c10034103424068040b840310364002480003140f90303092180001d0000d03070120849000d019004c001d10f2a40c2e88a84401c00c095221341038640841c80341c00c030035011603095449402c0c0030702140c0d9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 459313911 1250 459312661 459312673
    0x50d0b10030b0910050d0308041103160e06090712111e03010305150408090f0d06050906060f0f0a09111219050c090307050906130203090106030c080706090306090204020f0705 77
    0x902405500d80d0300a1542c982420714503030a0101b90703641080100e10139414038001101c2d65446c40c0050b540180f4a03581a00f510660480c040c00c0010498120151036280058a5003035803000108004110107450400124044140c80314220f00303035800c201034240d000c440540c6031810780c00b0781602d002e04017141944100d81c0440140108001840b40040c0003100b40c5600f1154100350700c422003a031241c120801c1c40380c1440c201c00e8409464401c98540d4541d04140b007088549000ba045a0b21004222400740c412002001c0c440301501e000c80d0310004882000d400041080d007001031030342c010700a0645c0315007000024003048581560142d010340c030441082c5040800083d002c140c041c1a18400360840f4030b81d04040c45107240588000403084200c8004075501400313601d81d1004503901c4003c0c02007183c4a540000100505981c1c1500800101c03441170300003003011541c92442ca91251114000d04000491401040002c41c98036004200c0c5180010320051a290b400c801c2d0081940c4840c0041f03505030000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 459315161 1250 459313911 459313931
    0xf100905031c110a0b0a0903170a0c1407051c110a0f02010207051c03030c030b0301090f02090a05010608010b090a170c0a09020f0702010c050f01060f090501060201110406050d0b1003 80
    0xc400c0700e08100003000130701405043e680e0740c5d11220f03c0280310700350407541d4407a42401c0c584114030005a9403a8103406e18010304100c42c80350098101c0c0b10840c00030441104c460015074080300c04440c24140c00c140a08003040076042c1c2c2d0315014441540d41c0d41040b0724070200d4020b4031418080e40d44510301c215841d1790300002910000e42001071b2030f48114822540701490b04109021103000c4c201090303040c9400203145410a005400402007500403a0305586081d404104000c08a41c0307400d1501d0003100d9001c4a507940340c4c8035000703680d001d0056900080140300100940400e81000d08006400249086030985d21442000c2107a8240c840103250b51340700c0708141c0e0060501550348009082006429440c16214000e4040e1070310035020001c1c10003500d80c074080c0604c001400342d4a84010400020300045030b403103e007907003401140c2c00f6900d4450303d01b100008495005104035940c0c0b041e543e20041c203040c50224140d1701e5030010b4145815854641809940d9550b0702d07030342c15680c400651000075409120f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 459316411 1250 459315161 459315167
    0x20a14010e01110a21170114040b13060b07051203040804170c0d0c170a2a0902030a051b040e010312050d0e030a090f08120f041703030f0a09020f100905031c 69
    0x3a0040429606c00502c00501c000210100e9041141c402541d020402072003a2000c628020300014500007810700d0640c000c42c001140340002c00c4224001c500f107400c030740d180940f00610740c401a200102040300410040213490784894100101290303001c00d6a07031103030104d03000ca0145440000d00320b85800080702c0a00a14a545034000883c044420050a8400d00c41e038816482c00100000b088c031408018107107044001c0c407102d08401412a407901551a41405140750000d40004c1d54031000d40b5040700ca840c12002000c0c0169400c0300c01000740300302180d203940c642c551301440340c140e08801c11404000c9075a0341c071102e00400500c64451740066942e40e0b00c002000748042c015800410081c190158200000c4130000f8100c0001c3c0c12002003103580c0e101c100001c80842c0328641c49004d042e10030000c0b80d8451100400138520504c018062a040380e9501d0007504115964508001c0d8001c040e555601007904190011100700055401d00103d0300b5126400680791041d80d0410003400c1c05d20340e58411748158 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 459317661 1250 459316411 459316427
    0x150e0d020913080f07140d020a0803060a120503030106080612120f070209040b09210909090f0f06041703011d04020a090e07080f0705060406030207060212070804020a14010e01110a21 80
    0x140346004e000c2d0080b87d818002e44812280001802240300070000c9134003552010008001441c00620303003842a146071030426101e810900c100700200740d03d400020350f14203119441c40000c40d2244003802a40000701041203098004098074000f014051014600588441040038003580c01070300342c0200303864184162450f001c03c5020000d4500c2ca446504002c10386003805584580c00304880110081d0760314490140b400e0320200c22600e95100740c2040c008280004181207002ea4041c0403451a0740c0ea218056010a02c801e00c2905045039500706000b4101d00242e050742d030080d2004269120340c1c0c0c0e03641182c2e400c1c1c3c3c84d61542845035030000e40d410407140c41d0030058802c280b00598060690f0707900d010300007902c0740034902c0b440c1c06040e00010840d08000c45981100c0c0400084850003407281002071000340074030012039040780114103c0a010030450181400301c0e0210702c05075981c00c440500f4500450300250035440a2030a03110702040f505c0080d40c08030070300951088603003512006646110340101090 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 459318911 1250 459317661 459317693
    0x31112010b030d110a0b0f071b02010c0f060e010608030c0c120d080c0c0115033e060c01061401080a0b0112110c0d09150e0d020913080f07 61
    0xa032600078014841d0710003280900307842070541001031032501203d450904005104000405000381481000042d9a0440b891802065035a07107542001c2d4165500700110214084080d021440103089034002a20802d80344c00b15034410b40340801d001d2a99200603007503c240d9007050070349810100e4208441d40041081412200301219810303002d8131294207441d01d1343d134400c04600822248100107002c01c03503048116804060321400030002c901c142c140800f540b0040340001c44414656502510080c4648202814040903184510a8a02c108405003002c180e030068a103400801c28042c08000d08001c1c13040398000e0402c019940070090798000018031405000300146029490250100c50b540d034000702d000c1d01203e44240c0042c10715103041c1200002d01840d803c1174000e114149200300c1c51980249a10119150507400440050703030101c0540c2c01c9004401c2090700900c0682c1d10a025141650805801c4190321a4520b11303494240c954202d04e0703000214103600718130005442e400300903803490050021 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 459320161 1250 459318911 459318913
    0x2403051c0504030803060402161514181507020109080409090b0f040f081605010c090f17190c08070e150f03100c030618061a09010504180204050a031112 67
    0x881d0544c2d44040e40c42c0006007159004035030114446500c107001c80307500d4404640000210016103680704207503014010600c02161115031001c003080b002582c00000e0041c44c5500e00c0a0521164140c0c1c004500c03000080c1180304641d01c4031068004102090003c0000d00f0980e40007240340c4400d0b040c201450309020307264100c1c07410250104408110220003a094060f441103140d80e40f6400c01d601d5203146005104003400c40e510380250348000c1da8104c050b900440c0c0c4980103800321150b48200d4500d106400a19000c019008076085000343d8089154000c0003510450110f04800d49414286140c441c0b9a00009440f43c40d21041c00301c030000385034504006502c229900c106118099001c03c0c2c40381c00d00c0810718000e944400040700b1090082c2c002070003070002d0300100200c0910205188000d41600d20a050400119031000b0400c0c2d0708250840c2d03000c0906850340b901d0700f842c04480c82020b4924000c0740207201e500740320105140c0e890810700700085008a00d40c612414030b1004010440c081e280c200749003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 459321411 1250 459320161 459320167
    0xd05011a120303070c0f0b01140411030106090303080604020f1201090b0306040f030e210d0e0d080403120e060a120c030c090b0c070e070816050c060a2403051c05 71
    0xc01da80000480e90300524500c0c00d162a008030707203819003ca02c414003004045480c88000801d80b18000398040f403032044100c5082c000380b0420381e41c00c80c03248020b0080d800029101c0c03d082c0086806203030682c0d000880170303000619086c2909690041c641004101c088007004a03001045002402d00a030100c102040780036010078281644c1d480d03c001c50203500241404800c26013203903a580c0e04040940748000042524144400840303001d5100c03841c5c0f0b06104007166241d0a014240c0c20100e040001003640096154901815138a884038080c0420410500b0032000fa00e915126440c0e110207840400c0054a42d5900555018003400c10380e0640132681e010149800c907170b030b5111540002e40d20700301c0b00b803140702d540d440c0e04040c0c8190604507540c02c94a94a00c1d13503024400c04660180701e49219905010040780742000d01d0320101ca80c4d208840c141d1410760b014002042c062119980f2046110100420449280d910207900364210f000c15401a6000e80140060710480040c11a0100e0320000501e8120720f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 459322661 1250 459321411 459321439
    0x60207060807120207020307030506100905060906220e0c090903031317210a060501140703080a0b031e060606040b1204110604090e010f050601050304120504050d05011a 74
    0x21590718001d010a081000440d01d012030754065604448400342c028003610503058580c01d0855071400700303071004900070760f840c03100161040a521405004d0351009251108940b148010850842c100c2018040b100009140342c4204002910644480303041c60f8010b840642000010000d803507600500006603a0010000c001090801401c80741c00107500c054040c00d0319071000b05440712030082100811039050151130116244908001d454814400c051044c0300054450f001100c0844240d40b40040c1d012050020b000000e020b01d800c1da900c0b101002c0d0000350103000e0b80009140220640002a50728031421440e4000c120502426600100654200749080c0ca4001c44481d1441743c688086120105400417404201003021071144684004003503030745868503904400008c01c00c12811624030f61802c100310300300b101640100d5100e5078050b15458119074980d100c00320518150103040701000b60803c000b00d02541c84c100c0d80c0859a014000011302c603180310f00e02030500c004543d0304500c26041c4d04800c070303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 459323911 1250 459322661 459322667
    0x62114060111121c0606050705060117150411030c0405060f130b0628030b0a03060c09080d030c11060105061b010603020d080a0f03060311040b1201090f050706020706 73
    0x3500054286030401d0030010410800341885200c140c880780705400042c1d281c03001211041440c40709007240d24204000341c0e84007001c5e1030610441d41e008000b0781289004200c00d6403a410b48200108445007035544400030b640c00c1c4850070780221303011101f01c10707880c000b0314150400b00035140910304180c8040142e4140080000c41e91401c1004651107070b030700b81c8030324003068101d174010080c0010040c1ca10f41d285e2a8100c90360719000c0030300c4092203540130916800481c451180c01200d250010140c401c2c40c00d1400c50f110b010180c00010b80807810311420007000248240e04008030203c1c10400d80d00012851007100c0c00034110381c00d0051480e040c3e8000001400369960300c5d811500b032200200c0041000341020700400380502101e600196008900d240d0400c144010b01d8010425000103999080b0164181b11040d0112641800050b00800414056a6107820326030b00000c441040200107641c030940d40090b9a080d620150070448006800100c80c50030072030100039180c003030000f6001611521382820001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 459325161 1250 459323911 459323951
    0x70f1a0c0d0c02030c151617070f02010e10020d0c050306060f031e07030204090b0613090e011103040501060f05090c030a1509090b010e0705041802130f0621 69
    0x16032001c039542da203400c910a00030000ca07012155040c00b40d8001461180510910f1242115000d51050010440c00001842032a00c02861b02c0c4000003100c07292100581101e42c183c0c00303c1200c3c299940c070b08503609044000c200450102070140d00269a80c060701e0700d00d0058910300c1c10a8028401c0c01e00070f101072a5104000d0396004c840b8601d580c0c0d01c0b95180b41495017200320700440d00e800c002410301406000c070340c0754005200b13640c00030304144a00c480071320502249200c0c0c03011026010034219018404803c154003c098141c0b40300740007159000c14803102400329841a1021900c903951f0300d000300710b0400c080d040c40005101c21281044075141c5480072803103d21000317201d219031030369801c50305080c0b210308d142c03980141100c51003c0294840780c0c030b402d10885c0000c2c0902e0031031004903800078444034851412181625604a29086288030221a0030042e401015801e00722050b25000400d03902d0030008524002e0070190780320171007001c41405040740890824031404616040907400324078903108401c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 459326411 1250 459325161 459325177
    0x4020109090b031f2009041b050909090102251712040f05071a070b0c030907061112220e01050603060f0d120c030908010e06071101060b070f1a0c 64
    0x3009180130500784500d0002c14104a810031840000704050f100c402071100503090261041d00c0c100180390311400c084040c07c1c5e28007501c000040e001c0105000c1418007a5805803c280300d8800941004510400e00c50a00c0c41c6080e140200040300c50010248005c0c01c1001c0816030440040a04e407210b0f1302036030388217440003d2001c0c2640300708150f80d0040000400c50740c001030072104010700c0d60342c898440c9400d0540c0b0410051b40e0400c650740124080d89040021280150070031002030081c41d240900550701c01e20200002c09050058501004104090000602c44035620200110425924050300c207100d0100c1c2c0c00460901500c440140820784a620403650011403c4074802005594003000441c00b080c000b00041100300c00903411200c42c0c0d00000c00b00d10691103a01c071306000c035403076049140c200c0e15070840a030707513651000012038881c50207440903840303c8034850000b0802980702e074001e034840d601030f117812074085017101000d90900021903603100405080140120141c1003085e075485150140c442 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 459327661 1250 459326411 459326443
    0x203011107020108220f0f0f080306030c032a04110c2a0a03032106030b070908060402030a030e0303160804050a0510020c01030209060408010914060f01060801060507020d150504020109090b03 84
    0x1000d0780a200b182001c107c502a80300c100010701d11000d1400a4690b0030940d4018068030901d49046024138001c0703004a01c0c5002c40046112017410031000241342c07002010016003082e66041501c009480010081c40d1042d003001c0140448950504c04c100c6041c080c00090010003038240400c80300390703540741c0603804980c3c052420001100d42003500072500307111150521070a13072804100004101e50a6501d500c1603505032508503c069aa004007a104e281c21240258150410440240001d0085441d120751010150440f0f00f081414482c0d0703220a000000c0035103441c20b005c1400c01a41c0352094002d000b4280070b603400f0b807410081100c06541c811440324000e05142d00456180b1950725810300f80c13402050352400030f04c41c0d03001508014600002e02138200e80c86000ea44d000400840c1c650340b21a04072049542c4a80c0385070700c3c0c13600440707207508035610403030b40310800110303e401041d8008414a0807501c202400074240c00c0c42e200250005035203901c1903034014145003c0240c140d5003c1a107180c100d01d002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 459328911 1250 459327661 459327683
    0xa110105070819020a05010b01020706080c0d060503100f0606050a0c20060a0c0b070c02060a03020705030d0204080609061602100f0219050a090807051003020a0c020301110702010822 80
    0x11500c04103d00800180c9010081c2001080f00c01c0341d400070303804814600a0f4000c1102c00d11100049864018a0141c0804150040e002c6100661230350300802c1c0c500b43d111000a030068441000034103260000c4003040380c4540311000c0c808602e0503885048001c1c100c5040c031030320b406250711000c2c010200c1620042e02144603803078402e4071011040356501c02034000a1145a480c1001180039103101014001070701c07143d5090000841050149442c1840241c00400c21424038044040032006540210030868040c001880740a4008516002400c090b04911010700000c5c940342c5074040c80c000c002000340c0004a0841210705d612500441c0003048521845004685058820a264042d200e1205004c006c64212120054096842806800412004e030f6a15034039039070f20002c1a54507007560280590242c0e0b0760380000e0f21036019600920240340346e030a0001a1149940000342111a59203444280100c000b440100315a4040e40c01684034151100c00844c1042d51000c0450081100c1b00c0102121120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 459330161 1250 459328911 459328913
    0x70602220e060d0210031104080a030e0a1a160b0f090d0315061b050d05030106021912050306011206090507030b03030c0d1809150311030a030e040506180f0610020a11010507 76
    0x782c004da4030302107401031f10550300c0c1e99940080c0d0769400300d8030045e0001002c0318166807040c600390740d01c40121400300581c0240d6002c54404c2281c0b41e40090b400101d064054414500014a5070514912514102000f903090346480002542000ca501d4400010549070804802e4854650115001950a5840c00c15000304480710706942a210366240540284070728116081c6c06c45e400300003141610300e03650a0720411040344050030030200322100002c1c004004a038180b082544503d000d194440030502d891841d105815002000b01c41c11a0490480c80740c170351041118a6405015078426000c05400031807401c01c00b61040358a80f9001d6020108010702c442c404001008019003d0300940004041002040d00d03258450a2003810307844101c6074603c000c024070215181c08654144060f4041d00d40c0300c1998040c07000c001c014240100b1090380190050b94030a00114401030507413190369403014103400c90810a0030081245107942940086601c9003400f0000203601c5c0c06200c9100c002070900c903032502c800d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 459331411 1250 459330161 459330167
    0xa03060c1202070605010801140c040b0f07022e09080303060f030109020618010905060705030a18080f0109021c0c120201030b1206100e0624070602220e060d0210 71
    0x3103a074103031640307400803c5800900c10703664003040c12218060b0080045610f040040101c401040b1007420010b0300910042140b0040d410040041d13032a051010383c94217003036500140c10301c40019818840c00201ea070b052440c40c05c2030300c41e810074400d1500302851006e2500100c143d507803000800c0035019454590071600d00392800d400c1103403010307130050a0707940300c405000484012550ba046510700007400c0b01000200b80c1015000c564400360040d000c0d52030301501400a4824400c45150100d548004400010f1954011b12502401070300400020850900c40e0042003d00940014480c203200740c24461580001c0a00381c01008446021780010266100e900044e00108403480525030031080c8502102c4854002260f0380b84641ea41c2c0411400700f43c0c43d04110002c40310211049504036120348c0c2032141c0e8441421941942c2c088400f03201d0302d4200c00369604410398010030f07406031604804040c01d440002c00c041d0100081c042d9803d07820703200d141c904002120390000e500040c2c068041564000c000500c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 459332661 1250 459331411 459331427
    0x31608040504090807030f03020f040302090709030210120b040204080703030c06060b16050607030e0705060f040b0427050402031005040227090f1f020f1207030f050a0b0a03060c 78
    0x200080c030410035140f0a041c4180303168007991044000400e44200e00d07945034000d1098400d0f611343c1d40c2c80141480d05560a20090344005084c0c0b0302480071070180000181c0e0780e450440d203408926580c595020720b1192148007502c20844900d80314900501003800b403803038001020421240c06281007100840d00d03040090051410303800800610754000b402c24894048440341032030480c0300b00d08442569441c14422411191103a02e06070407a0008101042285844005400521040e041c280c1c50940d0f540d6011203640d0042d0b020080800c19810941e00000340001042c0a245441205126610f89940000e882e01110402c40c40a1940e40002c5019901d6088100e6010520b00d8401641d020300003001d07500c00070044500d20514841c40008002804000c2907070f1072214003e459603100e0001515446001c3e400400344c21040d80350500c40c0146403506904c2d428003444c45038600007030070400002c0031020380d07900600300d505407420182d030080e0545558035800b04481d009400069a09100e40301159000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 459333911 1250 459332661 459332669
    0x21909050411070f0825050c090f0906010b030916080a03020f061909111804060f0c1b2105030105150f1803011107110414010e040f02010201140a0c03050601020f03160804 75
    0x22500d810300410040c00249080401030109d42c2050301d03a44035180000d00c06000c9803424400d030008070042000810703100c040d582041c054829100350b43c0d090640001c4020056001d00219032051039900d0503d901401180c1c24007980d10007901030b629204041c109114030403000d03804010764454800003845001e4203d80c40b17a460003441107a0032401e00101c2064041d05a034107985451800f5490700601d1031500c2010340c44e9081c2e44415059080c00c80307041041019071078007a2a0b1f0309042100c03003061b21402d80c1002c40703006588c4480f41c813541400e06000301340384000d034982d01d10320f0b0404c0086d04003507038441524000805000c598400f94400c0001c039024104c1c050f0640180342020882d60100419818024018281070303c1c00c005200e401c0c00301c590701081c00c3c41500210003154020a0214101c0c4e2040703416207006000210b0503242c00c020805144100700c400e040c2081e602c101d40c4040c80c0d4180030302500400b00344002c0c101c200c0c0c02c845064076032250700350724030010180511200c204101c6005641c010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 459335161 1250 459333911 459333967
    0xe04020309030a02010609150308180604080303040b06030d1b030c060e010e0f0606010806090417070b04031b082a070605040302090a05072001021909050411070f08 72
    0x78207000d608140e0303a4022400040155092820100e2445005c0c81003c1c0c80540100700c42c0c46c844e1440e1035000c030542c4030b40003c8010812511102c0300035200c1070004c2c002031903000003d59581ca40b5040010320014080d20241c441c0e0071140007905d40552141060b004001c03007441520203070b400c0f49030585011031507000043c585410281e215030010019806209104054800c0c0c40070800107814640d242c00c4112101d82c0811801ca0205481f230512400041c1d01034030413000060008801c10b80c0c00d03656000100d08442401c1c014080200301a8030440c40c44181403c03062680c512031459a0710903890065448000101086140000c440c07110142c440481980d8641a1002140c8900008200383d0042c04180d01444460002ca4102506845464801c642c0380e51250704000c012100100f005100310001440da42d0217029803500ca02101c02c54241010f45500d031282c1c100e14000c10710023968228441640fa01c1410b002c5440410f464002c61011181d020300841c0c7e54a90540312990f5007040f56040d1505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 459336411 1250 459335161 459335167
    0xb031303030b041d010516050712080402030a0b0c13090b1302090102030d0905030c0708070e010b1b1009050601080a031b02010908120a02070f060c03030e0304210b090a030c11010e0402 81
    0xd0307000c1036106c540500030a081420144002c0c40d001c0e611441080030042030888002c1d0150b401511580040c0c0c0c0140c030003400d894910303209480c0c0300a0000d05861300c00c80258002200300041441c505c40314001c28240a05011420324040003032803415800c444034402c95000185103060368400e000301d44141510a504106e6050710381001c0b980da41280c09004c150748100d0344c000c43c18101c0000e211048030703007800f1054416800e005580300190401d01e210f6144081d55100000c10303210505c504040c03450100c40000b4002101e052440c90118180c0c8956642c0d0000b981c00c1c0086039025001c1c0e1042040000e000354510080e20040358101c115520240701800707540d05402480c03100d08010221070200c0d0342200c1c0040d4640c1082c0c00104d1952142c000807070f0051340e025001a003e500805003501818050783d00b0b00b42e5036900c41e007074040389210350304079401301c0c000c08010005007281154003e1340d031038001c2c03034a9082030760050100c1f010300401404003503034400000100e0384146036100c5694405030080d51 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 459337661 1250 459336411 459336461
    0x408010f0203160e09150102031902060a112517070b160305060d261317030901090e0a02040302030312040311121905270a0b031303030b04 61
    0x1000b50030940780303c0c2d48039800c140035210351403083c0c40202d24600028808003903a1242c103a5085445841103459044d030009021096908400c00c40c00c8140d604550081c1031203140c81114035040798010300e40850300eaa0280710107034174003503c44548044007071403410045041e00507045c40c081b00ba0325001d501400010000d0741004100d06086c0c5980108202c42e0f245a4140542005405454003161640d810080018022012030705181026035030400b40343e0b01c004a00e00460305980b1a60102c03000d6444400624401c020120718501d4140300d55032010060350034200c40c4000201115520320540c83c0e18500e000115130341c46039036811a07006580c0103044982e180140740e0722500001d4116000d901003601c3c180716041074040468406e00b580e64034020300780780102989034244030340c500e003c250781004814000565200b00319440d40012410380c44040a13028034500800441000e1504819540903080c8207210f401c07416a602502082e906044c041800c40020000c50000e00941c01803d0380c0381255542c401c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 459338911 1250 459337661 459337691
    0x10509030304080c01322208031e04150c0c0f120c05010201020a27050a0902120907181e0504060c030509010e1e0f03030f01080d0e09130305040801 65
    0x401d034144c083e01d410f01d15008107034880106592804800542064094600914008000080c280c011400080021008261003900080340d55a04603480661000840c0e440388118084a100c584e0200301110b8a46030a01c18806140d00080000a0a20000071014020014a2030610020740309c522464000d060303890912040d6206507000683e4007582c62640490954418021070700750b058103407184405c51190aa040710b5401400000e8144004049808101540c50010100051115010150310380c400500e000c400400081ccc1810020390280c007080010540c2081d07050f9861403646000aa840300040f0540302e40203001c4400445503141c4002c01c02040310300e41c805020300f1041c1c0e5080120b5a60b0407140c6088070620440040c4c01d500800c2a0710000803401c445a031081144825030360004c00d044c0c01185150000d484c10041544244010302c8581810030951048107014a42020b104151501240342071202900c0028100c00c0c0500110500d40170310101c600a0001e030000700102c0740c00b00424 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 459340161 1250 459338911 459338923
    0xf09061614092805010f050f1605030c01022a06070930150b090c040311060405030f0a03180b0301030305090a170f060112210c060203041211010e0c060901050903030408 74
    0x13607408940d07240082c0c0d11180c032540070344640220101055181190140ca0141d40362a00303401203803180300030448400061000e0000d800c001600360101d03012008101c0d58844104a555890861075100900b00b022859005541100301c1d05840c42840c0da01c3c802035402c3d0340d081c80f54454200c1468500200c4820031140003240d858032482c0000821902c003e900030081d0780cad2000e031440d03d8125001c0c041480410400c2140e82c060800080c42d481c5015500c0300800d0502c1040455050a50085e20120301415045a5882c5814030403c1c284040a4100300440345980018040a420041c0215580241c2d807510368003100604810f02480c154040010040c1343ea9a414190300c1c80103005107800001c00e01c44002118480da648801410b42c1079030a0424062050090580030040002c025a20300c0441c000384000d500030340c040c4100b01e4904492080c0a00060300c0c0e4099040749030f01d0010045120b000100f0b000e01042011100c0e65598070b1070000480350b900134800d000358580800500001c0c1ca481c0003404c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 459341411 1250 459340161 459340169
    0x40c030201080a0c0e10050409050a020301080706030507020d03021b0a150c090b09010c02030a170d060e070e04151703030a0b060a08010506070611030f090616140928 73
    0x502c5203a5074a51000a00780c07101e09852501084109003100c4081c98220320490603824139242c814106a45d03000c0402c2034404c2928006890f81d4004010700010105110f0716029100e075007020301440c1001200255501d03245914801019808031300d1080300040380400d0840e6960503001c07541d0140e402d0a090030142d42c0701455a20305450010815402c5025502103001c6980344110b50b8140182c0b1401580d955480c594100e0b0b15010b42080d20700081c2070307100300840345682c0b24507030307503c0350700e0f1416240895050781c009012030501e5804220a55500404124110800b50750100b03850b54841c980355440da40b40d41000c509181103110000180390000b0103184944801c3c0701c00c1c41190040404d1060300e12406a4102c0010300300e000521080c1455001014818030846000449000109110301160400e1340c0100a0550719014000c0e888000c002e8590401c40f00c007142100060406000f41c1034009080300300d0305015011402c0d50032551a945492a00b541c0700c0706c1700c1101451004c4048040c03040d405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 459342661 1250 459341411 459341417
    0x809181005030a02060d150509040515010b090f040b04020f07030e04110406050304120513060203070b0c0414120c030703050a1b0e0a05131407030b06040c020a15090b040c030201 78
    0x2030002024500000c01c070750318035005001680b8080b0303400a1200907145e4641021001d101c0b400c1c0004281d154000d0382442030740584050b14102600644900b6519010b90000310a14801c0c0121031071075940f04421105a1411600040c00303800b4080801c01902550807100c0f004c007c080781003401e054015030760600f2100100c0f010096104205200c85540c040c0b401000300287d820f000190000d1601d02d03c001d42042d40742405401c1039124903001c0e0b41801190032480042c1c0000c0303002410481c0d40250785800109600c42c0e541082e0901141034400318400e81c000d40308403444141d20301180011300c03032040350190140641e00015143d0074550341d103500031041143c0c81a2540e903000b61100207082e401050303d10900650320240c0350000c0c408050000501100c402001242400c80024165148000782c3d0042c100079000d0940345040c11045e401009008034000c60500707030150242c0d030b80440d803c0c420552003180894a591040d1908004004604008007006081403c0c0001d1100710508901107900c01d907 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 459343911 1250 459342661 459342691
    0x110705030109030237081b060610030b0d0605010b1e03070203070311030909090610051806040203100b040b040e1e1504090b01090e0106051206010b07080918 69
    0x14040c10300701d40851030080c0043c2c2102c100440400380100414052005031200e00084c4180c103802507905245000040358400350026000c4e0040c1009400c0c04020785803180548124075100011440342e5001095650801d6600c5c0e4654007195110302c1800d003000e0308003104100b01e68443e03110902c1a80912105181a088918503050400c80081120702c6550942d01030b5041071404c0c1d809941c4c03004050700705452400140100e00301a22548200c42c81192840010100c0d828030100c403c1106106800240c01041e1040b01d01c400b940340310504907000501902c0042c0d80349e031406101d4561811982110120704000500000c3d188081e80240080c0c40340580301e0304198840500c54440f669003c1040314006100c0c400061081e50144880c15103c42c020700003290f4280c203a40e0307141041100760030000c030541d56034000d0101d02400b4440c641c050705050700c0c410340302030034482c0701ca80d91601485141100781001410f901048501d600b500d0828501400c170030009540040d03022512001140c2d00c00080d0080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 459345161 1250 459343911 459343919
    0x23210403020a080d09150908011812020f060f0a0603020607050307051209031915020d20040b0f0315060a0206040204050c2502180705130902040e010902130305010c1107 74
    0x1048413181c03200030791581e1191074070301407010340d0b1941a03020351410710103184000144054203006580c100c1519400700321080380240340508901206a0f01c0f2811075121490060812400064617031b0041150001c00c0c04603545c840480c4060240d54100030b4021601042c11400c100c000809403508078810340641d0900c100d4070510404500900c555aa815801814035004100300d603034001d8842800795426489021101c0d0071a400d81e441a1140d10f0170301d07079070618040e28440c64840c100018280c0110a440d01f8607005c0f58000398010520034011580c4000080341e0390341003404c816081380d000070f00500e40361002c3c4400692500f4045500f68042c40c00c0038000341074410071500303ca100d40b6000e1844010040d45030030080c0c0f032404c83d0364100d0300309100c6100b8a2020b009201e140b48112199a01c840e55108007000d0601d4040050780951310150050006118841c1584103150645001c1c541c01629485d84210120020800d40c0c4050a5035103001003c82c0d03465840702c000c110f074003105000ca07401d4550f6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 459346411 1250 459345161 459345163
    0xa052d06070305120a0f15050a0b0307020a0b0c130f0509100e010b0a030b090901050726041113110405040605030a050d030e030d0501181823210403020a08 68
    0x1401d0700180020010821202100d030118402c6030058680100042c0840c000089001150501c0c1018958a5a0860200400d107000e00c5500c000d403040e012014118109610042d540d0b1252140081518400c000003405207210328007502c1001c2120600c00440780c0d039604000d900300c003090265a008130071120000e540010707500e00c001c2c108c85942d07122407e542c2c0b81041d5400c0075048411b40c3c1d010541c907003200170400c2da00c250390980100550b400001c0c89080c9200058224004034030301d91240c400a00c0d0007090807080c01c80403940944c11001134a81c0a840d4000505043c41803541e80c1c0760285040300440304215072b07502030300903518242e030100700c082e41b1001055913861001d1401000c0f0360014201d00d0005200790800b214060422084904042c1305075601000e84400340c00600091440601d00314002e8102d014810303e2601001c2c020f101c115090b04d41e90010740f0105080900e00314106c0f074418070681c1c100003581c0f0042e5482050400359904188540e041c1c1c0c0305200c10381c440c0300000c10205070540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 459347661 1250 459346411 459346417
    0x100c0f03050301050f191e030204060807141e0609011407110a0b0f030c1e0f03040b0109090203030307030c050d090b04050706090f140316060e03070f12060207020a052d06 75
    0x3810f09042e02c0130303a01c1e080e904003547d076010959008845450701c000006854501555024094903005061080d082010b01c44841c1d0f00d490304a0310500400c5003040c1030707101081381005500320036515556a43d00281c01a07660360b036890005418080300055040a01010608a0340f843c031088400c20701c1140d0324184003406014540020340d5007081080030840304502440141400c18034240f8400010f4481580c3d29815004a454207042c54030020410003080718240c030440c050028000701700a00005500030943c1c03400001c1a010906540740d489030716041c094030603640c0c1c006031140c0c00c0c0015a1507103810300700c104003520110399038400c4800100704180035020480507039040030890b4606901d8a0110300803049151380c5241c00d400380f4500c01c00c280d54030903201800ba00e80e5403100360040742c0780030500d171400c0d4840c2e005140040004c4024451f600d01c10b0030b611107480d0440c1c030242e01c40001e80005001020703e58452a4054100c0e00d98840c4110f211b030b00c420f1031a001d00d52603505e840141080c005584 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 459348911 1250 459347661 459347689
    0xa20130e131103030316180e040309060201051e071b050105071d04050f0403051303060513021806010807050705012a17091203090c030f030903010f0b0906100c0f03050301050f 77
    0x102da030304111b0b1030441c400c2544202004000f200c1c81c1b68141c0d2003c00d09a581390a480542c0001c860040500c5442c1c1c09014003074110384040b40401c11041034001850041c00044d000d0300030001d04520000523030452041d07101c800c3c0d82140c0200110300b0a0040644000c4200d40003c0c0f0701c09902c6030b208142c0c84d051003001d100d100c2ca8162080603a0707a80d41c04803510f0380000744500c82e8440484021001c6009031066612854140078400c3c2105400d00401c0548810042d0000e0303c0c851030800c20205981c0401400d0304886a410281d413111211315107103014025042d41c0b181c104819030213080b5081e1560384840c030040320036240c982c40c580e0b000340c0298140c030048403040a075074000010748500326007120085a016005005036040c0d13071404000241880200440c0c01030b241e101080d00c5e42c06240a101d0703441540e80d152010000261400041755218500414403882010b15008100750320380680081c40103950320182da000c520381c0920323003d0f0298200380113480c01410903a6604200b801c007603803464090703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 459350161 1250 459348911 459348931
    0x4090c09050604090c050c06040606051309050c09100b0706050619150f090e070903050607020f0c0f060f07060e2a10090506210a20130e1311030303 65
    0x82404c0410180c00760019060b04020488200b2054040c160240100c0b07000394070880000c21164030780020004004c40d580001100c582c94500c030341d00041c10008117280c1e00c1c0d42c16101c082803581d41000e00d0004150381d5001d0b25010000203010780801200390300075403040c1001c03038030310f00412044000c2c549104010300038504c12040c95444885414056440081401c2091030107034211502d540e44200c01c4c10041d40d818002c40c04030032090041202c207000042d8451017920082008901807501d250351400c0d9000101c0c043d11081c1c505401c25168002261014014150540d40d02d150030b140001c012304c0c5ca210405454003a50103c000d01c80d03000c0c900c4603102c01803524418041d050007400c0040040740c0350a11401d025040c0400940d17510384101510600c0100c169030001019500d004040c998801017030702450502d08490440308140c2d84c42903805240340008090b03101c80068002c0722106409030032440b0441c400da41004001c4807004000c140181c0700d00c501904230880c200038569280420303a40f00c1d4603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 459351411 1250 459350161 459350167
    0x109090305030112020a1206050702011d0705010537020706090302010f082a090126130602040513021b060411040e0304090905010c080c16030e0f0a0b04090c090506 72
    0x1103041381a440d40c00c90700060885d007406d43c0e00d103143d64540301c103144200c80d000d44810400400f40d8089c40b40540f80494644894961607101402c9a145c540314084d05050080101c0d029a1810307198140b9110008140069002031080c1003c51a001c0d041c10020f000600c603540c0007041d824401ca41172802c89a0603150140d812148a0b41175460040c020840754a00c0944440213951060481848542145920500e5079903d0a4000148a14072622104020141205040d1607100c0c0300d030030040d485500000f108070350790081d15202c1d020344101d44c8030503440350800c0c1e0341546e400328aa0050601c0050071818038040000941c40c82c3d180c035011900a04031091131031407400c60f41482d406c00c0020b81c41070410343e0b103802d8840180780111104c0e0702003a100c07a9900d81403507550540040c480e5030011607400c00d150500c003088030042025015070000030b08120042a004d802a19503819030040c40500525080c0304584070340800642c2e27042849090380305400d140d561414640a2400070098a03000340c24549 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 459352517 1106 459351411 459351419
    0x204060621050c1210031205030115170109020a03021210080d081306021623011503021c0c0e04060605041b0507030f0908150a0501090903050301 64
    0x40711516080c03e018280c0c0009041d107403420b00c84182080c0e10703618464107280709011544001c105000030f01000000c141c0040103035050310300614041c2c00c03404009908495521240240c4080c0b05500e80050100041503002400840364a04000d40760112029012000050403035070f2482c19410400d00740040c90b814403002c9803c0305145044500d6040030b109001e8134810042000700010340c00030b0324203141d0001c5880d10701e4881e004040c111212701c800a28044084c468032034148154a8801d040950010710040602669005043c0f1094540803030204026a5903001c026501302000c0800051912009681184914840e503002724402d072a02c428002940c00303401440c80f0780c0c0f444601d54442d60754840140c0300c403d03415203400c00302c1a090356002d85014070142c21038819801001030818444110301d0400d80902011801008143e0344c503442c0808641c28164001c00041c01040100 = true := by decide +kernel

theorem cover : BRFrame.Cov 459172661 459352517 := by
  have h0 := BRFrame.cov_init 459172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 459172661 ≤ n) (h2 : n < 459352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
