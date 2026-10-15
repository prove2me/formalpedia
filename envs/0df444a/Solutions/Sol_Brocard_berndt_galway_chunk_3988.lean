-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3988
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:15:09.680986+00:00
-- url     : https://prove2.me/submissions/60a122b1-fc2f-49df-a03a-8c68b3f76a5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 717086330 ≤ n < 717266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 717087580 1250 717086330 717086339
    0x90b040b010e011d04180302011b031418070918110114090618030a0f030e01090e0c0a030f0e0304060e1206190e030a030e0c041103070c17032a04 64
    0x11a4003004c01d44050114810401c1d00340b81c8035540314201c148058100513a01e40440d01c4c000780a48035060422000005443d0400d101902034020300d29004541040280d981c0d03074100c07191000300e0740c1804506052107110800110518030b8456252200e80c00403040101075240c0c281040700402c00c1d00200c0c10403c0201502d031203889050161469800e040740d0342c50f503c0e907407a10040c1e841c10203000740c1681402005d0301c6104000580400300c101e00d20903103588203422000760064401e0341c601d00c148003580805078000344500704a80010301c0900a50304000804a612072000c108982d080300d041c15090b880000e00b030003407540007a9000d0200c00110703100342c402007500f441c080d165a005404102128109611049499215005020301b0055102102e89034041d003200180a0104203604006038081c590502c00c1c0e84c107042c0159030f440503981c140c42d4510b85485a0440f50002c1b4007009591a140940050084406000c0214050680300141e03900490740c150100c44d25108a5a0a1039070010401c001c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 717088830 1250 717087580 717087587
    0x6180a0b0306041d030910051c1b02120a0e031504050d18030c030212070902130312020a03080402091509040606090615090306020f210109110702030a020f0a080304090b040b010e01 79
    0x6040311020b0710801000003a1f21029100e5000e0700c0c080301e850303021003460540c400320b0582c000340101d00f590391210360400c1e00f0a0181e0302e030f00021000156042c01080107200d4036024544840d4415000703012540c089005a841c1c03c01441d041e0b40449407a000b50300000e01c81640500030040100760249081404e034511f41c0d9000022480e440000e024508004112045000900540c002041055010742d96441404120b02c80c1e500c2c0ca000441c0c900c001041c0460000d4800070300a21000e50540b9101e0454403542c0801c014850700a001103803816892030007000c103132116403c19008a200d03140c003003001802e0035090019103041d43c020b040300d02c1c1c0100165041c1030307106440408a030f802801c010303a034840d40b6006c62424443c1e188240c402c0f4845012880706854840074460407268a200200409440c00d030110841d48a21800694164048504400980351100c0b0b92641010010145044155186507803801d5810950003100b15a40d00e11003686c0e6401e1602903848448400d2904046040321040040c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 717090080 1250 717088830 717088837
    0x60a0b0316270e090f0a0303060e07050306011b020f030d0e03070b0304020d03180f15020c09060f0609120d0207030327090b041103101802030606040506180a0b0306041d03 75
    0x101540051840482c2104c0d60038007038050300b02e007030f103090760264005824094040d020034410070703604041c140c0015518070301c900207481c0151416920720000c074409810003030742e916001e40c05a078045141240b200403583e0412001800140c04cac1c890207401c150400c03c060034108c440c3c0c842c0004500400c00c100040e582c064440c42140d5041c10142902c501c141580c2162403c0e03500034022040c04581c001c200410030161203101c500942e4202c0c0c3d80c44042100b40082d032101503402c039070040070b5100d480c80b81b840c002000d40300f0041e000c0c00408881c1c1032411141d2420340e00030a4040503801262040c0203042d80854415104821083d030492000104070a042003000a0f104d1201c3c0341d45d4032810a903c80d940da130004001c00750041030f81d6480b800e001c40c0c00f0324030300c09a00c00e0403190100c149a8100f44002802507038840c400c02460075051074503000501000d0740c4075001005450649605091040d61003800300340242044c2c2c00740540341d20f0a0130901085480494005026021145034602c0b40e100000c110b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 717091330 1250 717090080 717090089
    0x72001180803040c0f0e0406050901060609050f27010305100c080a090f0c0803031611150601090b040905041401020903070501050a120f02030405070f08070905060a0b031627 76
    0x82d58940d158180704040360b080f608031a2510082804c006991004006118043c9010340c000300280d03101c0380a66030032908a03109050120300108004c0003a498039030003148880714003500041d000f103000b6040b07100f442c0c4501140d44406100c480184148a400c001160b0030014100041003100c81d8100702400030400245522035003034503051482c003044609d50b46400e00940c0142d40b80500b0b0b490728000307912034000704e40303075040c800c441101414810310480c0b1402460341240c010f0100c031040c02c040000701c9200203240d035052001c00d010009107a00d00c6802400103100c607140c006464101850410240b0000d02d1024210341c3c014841415241d8022807000121942424a2980d50405041c2070310300d2003145c828000b045180c0010744114400f9500110b1240b0720031001d0700c000c952a4034200700e0309102c50049a2441c1d02402c1c041c4210b40c1c5540c071864110303200030030414440d95101d400c00055401203400c402202c0e1080d5181c810343d500281200402c6130345c0711035200141d103110b03604180c8800d60300c074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 717092580 1250 717091330 717091343
    0x6032303130e060d02210d0207031a0c09030a0609020102100516120f0c020105010512120a11070308040308090112050610081f06020601290d090c090507200118 70
    0x2080321075803010255a40c4035805032030803060042c40130606d04450980f0300c640340c0700c0c00b820103041d500ea03201090341c1040d2940042e8441c2507e0141c00040c903a620010300014007150700b00302d0340c590750f0703030811560901511942c004101651544002410300c5203a400c1002081d0410061003129012411407101d41000c0d8501070110032008110381d806483c0c80a0b900b405141350002140300307182c1c10b40083d410b96405a030120341c2e592040c01e0651340d4000e401c441d039241003020300180050b0fa20840780307184e146030410219030400751241c0366014280c4c4507a0003211040c000150403501b6580140702024811401407003001503250027400300d4034111280c1e00d95000c01958400140901c101c581c0c50004d1a090007a00d2190b413511a2806541c8460a00030315280700c103140e0414803250807843d0002965604074116a05207901402c1d0000a44500101150900490007000c14010190b2051503c18465a5501e818410b251002c0740322846220340f0501960b410240d00e808415410524184105c1c0c0c801c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 717093830 1250 717092580 717092609
    0x313060906060306020d060e01080606060301030b100f182a0e011806030903110102090f09181b120102090303040e060a0f081605030c032e0603230313 66
    0x54503200900b1203400042000b0310204895440d000141e200d0001d45641002a00c4141d80710400140ea419003190469172203030041005000045a0003d601e400c804995000165241c942a1024200314160000501c1e15084c0169000c00b01c0c01d0f0165000e1441429040d1181041000d07440729608440300660080c0500880c0c650150b03440780c004000200d000d41c00000a0544030032005000c0c25410030700b81d000440c07e403c8225415070610031204c00c104000e0480620043c54001d018485000a014110303516056400320404d6000740882c04c8400b0503403026141c0c680c80e04007004201049041aa61aa131050100c0d80c61502c0000444e403e45110b061002055901e8000150441e1000e8001c2a0012054040040c3e0b00000052100c1000c005c820407102070307a10780c2c0605035544500307400e065260b032250058a40d030700c1c1008002040107183c405024402645d11a425040d54440e034800c8410340200751401a0001c190203030340d0842c40c0c007100610714160460800c2c5000602501030000c4809000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 717095080 1250 717093830 717093833
    0x30c03160c030c03110a051e061b0316030e151803040621060312030207032c0108070e1908010c051204030f030f0908180a06140705070b0408030d0b0603130609 70
    0x104801140a50720a0882301c040611803260681240c01041004c0c15108590110314501940710241603c80c00f8000614250f640b000800d00e90214500c00b54070906641c0d0380c1d0811003040a001c418490030162090040c20306055810721510784039200d0b0044590010300040c070a8550100c16420481c514540c1d02e24440300301c101c4000100400d500041244110320040110140c01d41c010b008214040d8448a0800307520b54a07000b480e110400500100c81c0d01c404c0034180640c010018a9000301030303450500604412100465801152000510301071202280d00b005611024002c060500440d840c14900b007003045440d00880356805000101803104001d22400c90510a034848001200c01c0582030144450074145003150381d00c01035008180440c40000c042450810040740300849140c0e0f80c50046400b075051340301d003071500280011506405000000a010301804000e480903046c100c0145664800e41c006400494041030007103400307041c1c140200604e40c40d01c100610103044d0031120115814026 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 717096330 1250 717095080 717095083
    0x705091012022806090902040b03040b041502130e0c0a0905060304240516020610060c0f080f030906091f1e0515010905012c0114030c03160c030c0311 66
    0xc1004050401d00700c1d040e5a0b0410f070803012903000c030355440e200c2e21308035600c03054084141d120300d020b00724121000f000480c00180010341e10b07903400360080a84000f41c0200b20f0b4450107030b034010103808a0007030400300f01303101d00241091801d8000086003500d501d00483c01c0009070402a85100e0f052003403901200082c1031001d200c980070030a040f41c402a80071705001c5402c010041a060718034410401038582d887d42e015000103521801682818044050b1901d0200100c2d08405c00710822501d880400c81c4a00000300008003034503032000102c20700c503100c4c81c000400d20303d00503000700310b01555405100c694448a594490f240145130452401082490005203000d0103d00d044000c00cad00340b40341ca8100142d400706401001403c00c0242d842800541c1d03114011036440044100744104030b0b01118541c0f810148906000356580018181803014542001003038041e604210b984041c81c0038008200588280c60196018500d60141400000044c2a0302d00411101c00b0b210000d0602c0904030182c404085d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 717097580 1250 717096330 717096349
    0x14090a1103120c0a1e05060114180c180d0c0506070f02100e0a06030b06043006060305060a0e03092e11060603030a050f0f040515030603070509101202 66
    0x9082282d071041d03a100c0c803603030318500aa4282c81c4007000300880f095100503603040c0da00864004004003090b27420b20540c1c1c42d40000c5440c0155002002508849000c50007080d0544a00000c04201e52070f44500150141c0c11000220039600c240c144002003000a9034071440c001c1a52400e440294541803245407410b408075034400080d43c03081d50031144402c034503480340c0d400d1500340d4180d500b0002e00365036000541c01e8500300c01c44135034040001d020610602e1030760a003034240c0d00018181441140d4100d0b07401c401c513001c00c80f4144d80c0d40e03031103640620502c181000044c0c0c000c40810300801c6544401c1c141c1070746900903001c1240c0300e210032179580c450381100660700900941b51184e100c81c080c0803c08000e0140114142204183d000f003d00244036071901205882034003880e500c910b441c15504035840442d81d40040080e0105ca1810700010540ea264501d0000301414001d4525540b81060b10405161070f00d07a501c000d100380d03901c0741044800c01e900c0001d001101e107255809000d801091002503000384 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 717098830 1250 717097580 717097603
    0x14120a2f060d020d152117030106091a0a05040303050313050f030703021504020a030209040305040b0301030f1e03090b0c030d020c0607111908160204090804050414090a1103 76
    0x1e4041518200d901c4150700a201080220800700111201100110f464004c3c40c407404400e40c14200c501100f0074841d01e0030041c040c0c0300d0000d004110446a400714860340003071b048500003405401041c0540f00c4401040244510b02038113441c204a85c003440206148203c2c08010100007021012071200e404108850180d1a40402a01d00c01040c80b0301c40380d81c0750483c020a500520584000814103641042c4040c081c94000d05154201400d68091201ea5200508220104202004000394000c00da10281d80a10b108500345950034856040605c0c2c8084080c6250411505a24405000a421680340c1d001c075100101075503240c005280c002401c500034034181d200c03000e000180720704e150074022400c22f120304141d488100c4540c0140c2a4035990b290600714035005210007400660100da541e1018200c3c5581c40262000700c001290301203000c3e10000b0404491050001c2001e10403485e050149022a500a0880d55014985804520707941c06c01c8c654003074600031307040e440e90300183c030709000302c03c2140c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 717100080 1250 717098830 717098839
    0xf09211e03020115170d052802030301030c081504140705060f03040219140631060206090f07030b06040b09040c050a1401120b1914120a2f 61
    0x140c15003000303070190480c1000c001c0040c40103040070076101805840c405c4000c3e8221700405201c409010191000d40c49420308130000d000030800c0c0301d07441d0050304480c0d42e00600350380550307200e514601d041000500c20340c10054007a080f100075000764020456105d80d1150f04503903400f1000101d0f008070b9043c41c1e12504406c1c3c1202c000202010740d241d0070b200840c0510f1003a5064503040116480710300c1c5030003140c054100c01c008159003200d00351038a03502504691413500402c0110b15007401c54004070550441845221000500c0100100d680600503c0e41c090030b0000548ad0034048003507200e840e040c040c0002001e60070501d0108400d52507070380c411461440f01812100040c180380c180440116030912502c0d200e03002008012860000e449051508a007041c1c5584c003603240403400400c040e000101000380c00c20516240c080c14505002001b2005100441f85400585244400d06c0301c100d8007041010b02030303400803000c4000680381c11200c0304210070400f10401200400ca0300741549848103040a54071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 717101330 1250 717100080 717100133
    0xb2701060b0304140a17220806100609080a02011d0d2001090b09090403120c0c1406280608100c1b02090a09080906070c0302010f0921 59
    0x71503442400031809640944030004003414100d43c3c10365201e0b44150010b00b01001407220ba070780780245002921075038060450244001140e04220000c84c41e0075480a80107030700c030308240032036018002c445d24007030090b038680089070030304100c0304607500e01600070024100328a11204221808900b8038803400f41e1401450000c0314000c2d4107010004100c00080241404941030048405600985201085503035040246040c21103042c200004480e00600503414401280c0c3c0160312002c003841500c1c66240e03103888048a181c43e5042c0280310004016902620f0780c440c030140510708145045500c02c81000c0b249502400003016809406040580e000c020740d48181d40b99000007038610740003c405092140e54500e602213003202956144400035a010307421880d042c0101703282a191341c00c03c010440c0200040361810800c140030918a40c820181544e451449407c18000c40d0307801075010030f0f07200c0c4070316110b00c00b00c2c14104503212a45095100303441c3c2c100c082840030100080c01c042c980c0b8000498003040701 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 717102580 1250 717101330 717101339
    0xc010f021504081c050603060c0d0e06040b15090402150c0f0a0b01090f050622060f1706060303120604090201090306050a1d0a05070b030c070c081b040501030b270106 73
    0x2c16402030382d060300d003422034032201395100e1219100d007031b2261030010b0040000f902c50380102116603010012070344465860300000985c4c9101004a140586c8c85070307500504610380b400b001c1c0050a4160380b0a40f1882a1101b4403000d40e0710b0401040142d60030300c808035a12010000010b1400007501c02200d944d01603d07a005050054001030710341280c091a01c20322500380892000d5045074421620326038800c59090901c01c168048050030503c50b030300424000b0b1a81d45608104001c0c41d4241c0c00801c4102c04d0000008a0010511010350481e03400d40040d8201081c0366486035103288014441d9000d80d550b0012101036a1241414600540c0c00c007030100024145890b040700503044455001d0550180c610514010341c20000e08041c4058000d806448410f0401c130b55080c80364005020114210014003c0902090288070100b00900c0700a000f04000e42140d0701400000c402760040921072403070100100082800c42e04420342c0864491104d81503141c0d01c2e078800410b20802900702c0310944c6440e20118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 717103830 1250 717102580 717102593
    0xa02130611070501030e10050406060801020d020c0f2107170304060b01030b0916181e1505040f030209061809010c0806040203151212030a0c0e0d02030c010f021504 72
    0x103a041e2603009451495840308015000d48080000c01280c079407024404404207690355104507000361041e030300070074125500d191943c2643c01004284644030f90009807407803181d40030480d400c0e074605048050610108044144502c2c680070062041c81c15030002100c10400c10300c24240101c2c0300d4080b20654a90a203030804200030517200014030b0102e0324141007400103150400065115200c0011036032400ca260f0345007241c40d0410b2428055604200d0030000c1144c0b4495501c800c220742c201c4c0d0110302070501d00040020030012180b411014400304210902031860f1820240d010789405440c4260b26481c3d5001051490709204c5550b83d444881ca406d00000303c0040d001202c1484040d074840000380c807a101040100c4c030054a804c642c40b840f4803010001402c1100520020400207800d03148906c2a800038480158401c4889201c01507440c2d803220215504045a03003040f80094805942100e825070100c0c1d503807898600c10704c0c14040745110200c1894800c100141ea021407140c0707481107034142445c2c0b04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 717105080 1250 717103830 717103847
    0x80f1b1c06061a0304260322020603010b0a23040603020c1005010b0c0c180411010203120f1b0c0c06030606070c1203200601140619020604020a0b07050a0b0a021306 72
    0x40b9000325020b011090a52242403201b042c41000102032861900c425805544040710148909043d4182e200403074056500c84001d50300070405a804165121224000240300840307035100b942d0b900c4081207080b54015420b10070340301610304900700103944010b0034501034640180300753751804150a00001080107100b41010b811110f55100450381ca00d4003090030000104d580421500b9440107070300006003c20201c3c0300301d40340418180140ea240816400450001038821030b80c1c03400182c2d180040c4460000303058807a0361295102c07001a130411001c2a00b46031210f40300c0304503520a110210100300542c0c1c2d082c08455100b9400300b0011f10040c0d5540a5011066100e4020f8001c2201c01c0307070304002d524400b04400c9807006c00c140075010076802c0a02e90150304000f00c0089800032000d024180311502d1080d034404041900e034008040174074081c4104244911544c11030103083c0d034140542000036100203950800315a0082003101140d6401d0030760b070300034040e6401184c3c10300e0004800046213074010516 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 717106330 1250 717105080 717105083
    0x70c090c0e0103200d050a06030f050c03060f0106081503120a1205011e060804082106150f0a0507050a0b0712050105030604030801090c0e040501080f1b1c06061a0304 73
    0x3d014403a030003501910154044c0c1a6003015120400c072400d14804940e11041d4491030201001904a80720b0311440c44014403c00d0441d10740d8403651211400345001c005165000f50343d0087d030745056061040081469001902c052421140c1000b104287c0c0c0e000d006c040245661031301101d4407035030b440e40b00601207840f0f203034082c00d0789140c172001040c401c24400c0d00d240c001e008920107103162807501ca402c0394141e43c018400c0c2c07240403040c01041e211500c400502c2c0c03141500304840c1c980c20308100d0100700d402c440105400c900900c081101c0003400250300306070f400800c06800c000d91103482500b485402c2c4500f482e002481040340c901000406a0021300d50741a03002e80540c04c000d0742c1c1e2030354181030350381e0400d8502a010501e07490042251f90302c16080104000309515254080c548103d011405680c0300380c211003a00e42025031080703249802040302c02c4c025031840d40320410400162010a200046031030480060450814010083c0a0943c0009000303208002601c000c0010310f04800b079190708103440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 717107580 1250 717106330 717106337
    0x3c07120f05070c0219030f0f0605161d030c030a06060e0702030703021005071101062706031e0807080408010510060f0e0906030a170c010e06160302070c090c0e01 71
    0xc00800102031032080740d1050342240c8a280342007440d5020082200c001070001c80000400e820040001240003440c3c0603014802c089440c4141100d1400c0001c0d02d50003041c00528003c0d607c0000c0301d1300d0344610303c1c116034001011088100503401c0042414186003080c12501441000141010410b41d54000e030f00b101d40c0044000d90f2a1a0114200c0c1c59114481c000b03801680400c07000a01c0e242c5036407182d60031a6503414140c0b80444442d0001d4295040350340081c00b441264420043e4400071500303440c1c030094160204010203410350303480030115204c03254103414440c0d60012140421980d04115144940c0206c0540d80380c81e59000803901074001101d000c074032514207450004400707000c0e84500321040010340310303038212002910500c054184002d040c01d0385072189a00072404a0000e098202c5da00d00e6070312050703994241c5141d42c10f082d251a00343c03a480300e07071045080003803420044007404100b801501d400340e543c0400b820100040380320f0750060b14649103843c1c0644900d0b0380000c01660b0000d07081e01c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 717108830 1250 717107580 717107591
    0xe04021305030c190911160506040b0a060302060d09020d020913120504180e120406030204210804120302010902150d0e0f0d110708030a0903060e063c0712 68
    0x3c0601c800e04440b07010528115a0199040c01092000e400c0b034809000003d1120341807a0078000302210a03040040c0c04d548035000b504c02d101c01d01c040c08203102d600640c0d44a0078009180b440c0d000c1405846444207901002d03035240c40d40d030704554690301b610711140d40003800030225042800d452030f91900144002c841010020020078170a9018034165000c58110b82c0900501c1c02d1041c480c9006800c201c0301080780c900800400e106002e603101d010300003810440d40d0041c2c440d81401c01c01c0c660a850840c2014103080b4110420000441d90320484027a24400500440303640c2c8589001e0313014281c4820300a61144019005a8900c00311001600107949400c3c014401c03d5181e140b115103174049040c080055802882c0c480c82e0303050088982c1140d07190b8240459100c1603030303031030294215044141a5000150700500800600c111400313103540756103800014110700d00b07007424102002a0784d40c158683d244041054161510902540f000202c0340342c1010750ba862614680c01031207050b2522000c64030520b441d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 717110080 1250 717108830 717108853
    0xc1e030406031404020609040e1c030b041a030a02221407020c040c3203010803030103020312040e04030c0203030915030601020132040c080a03030f050f06011409010e0402130503 78
    0x10400e84c041c41e0050600b80c0350950000602c0003030101c0980e02c005d24421894140105000104040c2e05105a81d500042030410741d000c00c415212241e080318041329100380c804440356808100113101c01c0d0304480742c6c5200c04070f0a0b1150707100004845800350203450084030306a0840c61000c418420aa41d03401c0d61807400141d0100801c642407805400009048a0a04411140030242440700e01e18046020b05000c0729507180518070340d000760031207070b144e42000c0010401c6040411200503809203050de040d04080c00d003942020408801031010b801c0041c2c094080c0c0a546042c8210b800c0200081c113813081140a8032810f80c441d074800c0c0c4403030380190b1801942d00308040c0c030324101e10340d081034bc141110380c0c89011104070503201ca00540f068800599210340003403900400c101103d5014400d49010441000032401e6500300e80004003c180c400c2c10500401545a0344513150b155503040d000f4a05480303807001c4004072480402c0d484c405422a1001520b185602e8120b54440d0481d20210100e90105500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 717111330 1250 717110080 717110111
    0x120a0306090b0916080c13090e06090a050d03020912010507081803071a09010b030f1507080f040f111302030108120a0503150f0d0b040515011a0c1e03040603 69
    0x21100d0721806403a2181c030500f15480340000345d401240c042d100d6820b240002c42000780107c150b60241c0c041070b0392400c0c4c001d1824002e001540e032007240351000d400e100c25036499450f11401e2000110040690005801d0f001d40d035280c1c82541440007210003008540f820310400b4100101c03d0b03694094180c24440702c5030440c0f50005c22070b0300b40e6030b100b1921007121844d071826202c6081c01924000307503552282c0c40f0050310748003009030310020401d510040911a903685111501c4240c0501306070100542101001005106240326540081c2e211a881e1b107042c40c1c40c18403544180090b0481075108000f02a00007014241d500a50b05a481d204140c070441031500d507813203078640b0031483c114020840c00e00000351103d070a40b81d944410540588280b9452450034005000c0000003401119140b00107800c0c44240b02c010088034114002803442c4d01c3e0b855061580190700c588403c441e800c044c5200040c0300a6141e0248403400c98140c1c1c0320b5501c2491900c4815040d1250490300034000042d10308245003540105c2e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 717112580 1250 717111330 717111349
    0x10b091905181801020c061503061e09070803160302011103010302031e0f06040609030305130503030105060a03021c09051204030b0406050c0c100c02070602121b120a0306090b 77
    0x7008080e0340e0546800c54030000340150080400b5600351040d001000144003c3c002401c081c803500010b050f06d440c6c00424078003010401d000c0e050103940306600300440390003401c4282d6003000b090780403c081981e4150030f0500e4840150040491400089507030300410408800b03d404051280c4c0081c0041940301206507400e000c03d00c40a9416444607050480d1076510b0301c0c00c68500000c00050f01c26001890041c0c41c82c01c24152000c07030383c0c02c4c1d40340c04105c181a03041c0b0503e034100d15660708030640031543da203405560740010b00842c2d1050170005014515907002e6812980c02c2c0b200d0111080342e00b8042e8840c200140703010602900c0390b01802c0d0a070317402c490300007045909699002d440441c0c0303611240c03101c0000340001040c0c10206601081f08240d000e03004c00440d01921442c8001242e03030001c00600078201010381d88030300c0c02c2d50b00a044102002883c007082e036216512240601d006039010b9031031149040c2d07482c03113195800207001544101165040c0c11070f0068618400d4140315408449080c4a8000b8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 717113830 1250 717112580 717112589
    0x606010e0103021809040f0f030801141008070e030a0b1006020105010b04080a150204230a0815060d02010324030606060903020d02010e03100f02030f070509010503072105010b0919 79
    0x44150804c4411850300041d00b0790000d00800111401c50a0780c1d035088965400c241c0c0a60100b00d140c0e00421040305445c0c0e8480d50440c06032241c100b03a961051026008000191420040c003500c0c0036643d040d902d040002551246c2c000c00e00000e6800d00c0004030402c0401c0e070180390010b500f4040085548110101200c00b11214900207140d002c0301c4e500c45580b02d00d480c6610004c515000c120018003210040c40980e0381d8000c00c1010202d07a0341d00002c0110190040c0d11401c00380c0c04c1020281801c9440d01032650780001c0944503200b101d4074507c0124000c10196051004440c1c0803900c040d100f042e5001c21405a910642042000c15191002078406102c81e02c8020b500006044502d001544207841000c0401800380c1166880c00c40100d201c000d40f0920344490a18a50210410526a0301c030704443d500041c1c941001c500c0c1c4840da900003071192100901039400d20882100c000c0c00303040c96403035030000d64880c09801c202958452140c240382e54000012148142c045c0001c0e020b003400704100030700c202c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 717115080 1250 717113830 717113857
    0xc03021003060531020a020c010f320c0703150506010810030821070f0e0402211b0310060810270e030a05031009110304020d020402090a080606010e010302 68
    0xb003c603182c13042d00645042c40211400d00542e682e0304400b8129002620406140c7d401400b00009240c0004040d00403030f0b5121000c02000309642e402e101620f540443d942911a000c955104000515108452084e01c01c210400e124680d8008184095485180c0040c011540c0031301003900c58100441701c0d03a00603034144a105544803010000101500001d140350341344415000908042c8000c003c0960b40125080c03804078840e003034503200c895480f016010054200b160114206044201c501c000240201030801d03046101c0f001013040d0040da80e0b10b862990501a035019600d25007801c803207290802903c00c580200c0c5991010418104003103100c442596a42e1042060032804a26201032502c035005c030b4401a55600d01111b82f56a00500c01403505e8070b0307551207a075540e00b1300386070160003650a40d20050003d4500f503c1c0c102d503e0208401c0342d4100317804845041112502e030000034000e00c01e0640c8280d120a444000242e8040c01058044c8142003d89804e15140c0301040190141e200e45d0621a140d07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 717116330 1250 717115080 717115099
    0xe010503030f030a140103081b030c03090d081e04030c0914061c0507081507020307050a02010807030623100c050309100504030c0e090d0504031a0601110a0c030210030605 75
    0x201d03402d04015690142c1c1e0041d002ca2a8096a942c0c00c07440c0c4d80a8106031080b200019001044c64074031842c0940b103d01c0705c03008511b8203011a04040c0c5a000d60704550f4801d036511100c05003406808401c0c1c1784000c194078030311404003d82001d900798a621034401200d032400020300028005065200b40100d00004541105042e40d42c407007004402a03d805101008540809c090710218804000c04000b0b0075498008003020300c081c900c45502d908000300101d085600800003000000d00129419013075944c2801c0408464990a03025400b61055420410034404c034a80d01c2c40f0754030092048100340501c143c42e2042d01c107024040c11103180c4004a80500503074010450b2041504241030300c9680480c0ea0710300141080d0310f0355211b0540c8042c0c0e03032050070701800320402d0002d4403000b403084100e186541d007001441c082c5580c5d21010080c003408464019076486100043ca241d002c1d0403821040000401035a80945503480c108400100d40d000590060140301c4078003a020740284600c8080d2940100300c81034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 717117580 1250 717116330 717116347
    0x91a090a0506031006170f060103080d0e150411010806030c1c21050c01050c1603050307021f060806060f150d0902100305062d0d0f05250e01050303 65
    0x1d42030260035030750140720301c070b40111054100384140c0c80600400c0f4400c1c090101c1882d110340c038003202c03882d0502640c4c1200c0c00400000d4002c500300d5400644c0d01030003007058010f81c0b4100d4100459405842c604116000c108402c00648407400f83c1c803c007003629a513805458040c02d159481800c0b58101d034000380f505035110703103e40030300103d180d5039407007065904080480c050024480c9115244540080390000c07490741030705c05080c0107480e44904005d503d04d00700313003803141410501c518000c1e02500307004002002c076038528800d0100c44038440d035446003503a0910b0402161002048140309902c828010b65010480c90f18048014480140d00180400007d0389480e400075001c0d80203540310442c007940c9005000058480018403100044180c40000d4145000802d000d541b40740c4e4060310844070341940c013150626200d03081181c24814141d501c4542d07410703545052140b0f0b45009201505600c1520038986c2141d080303010009015041c0913801d0179044d59640d00a024840a02600798076802c140801038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 717118830 1250 717117580 717117601
    0x21b0f040b040204210c080309101116080d020c04110a030c0c140d080112120e030703051b0f0312041203031b110c01020a0b01030803041a0a06091a09 66
    0x701aaa0003400145020b580311000000001404030668100440c150014244814070007001d009010800240d46403401250000710109170503200b01e414000300c15031a000c0c145007040410790581e01d00d803e030410b00d5105c01807250303074039a0085600014492060040c00d00e05083c040d8a0b14000710702c203c3d0341400c410100542c0a010011050310800862890b41d03400714903050000b1710903c0415018107000150444001c002140517081401015202c1603164000340d130201c04038a12404030315044a50b0381c0c68000280c14820f00d9800500f1a116000d0040c5603110003e007803071000e10702218660580c0c583d2006141d05d90b10150780150007440203003c1009414405880d11007503a129240c000703402040d0038800c41c0900c4052044c100010000700c01030541000c1081445523001e4240001c001c0e00c0102da07158468003005000c01444a140800814100f200c2265181000c101a01154400e8a80100344500801091107503078506400c15a88601d2040d21000003d400300700680902080c4d075600d08000b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 717120080 1250 717118830 717118841
    0xd020306160302091003020409060b0301060806090702071215180503030c0d060302060c01090507050406290708160b010501050a080f19020c01020d11281e0807021b0f04 74
    0xc50500d5020412000380f075030394142036513891030540c03401625582441c840800301d400603000bc9502500400040c04043d8211007425400305044030400410b98405400300c2c1480481c0e4048091100c0d41c0c400401040780400c9500003028813030408002064a100c0d8101d03c140300c07607001600c0ca8008002240003002c5c4240200300c1a07060710408110142d803075000c140c035940451254003039650340c0e0204200b08070003402004010f1408403030501030142814200054007040300c40c10006100d501403c0c2d02e810707001c40c0075508031076004595130307807510010030f00f024141c096030700202c441000000020034150b0090083d548410306580d0380707042e03a55520b81184017968018004407120fa080002d06040b140147c0002e18140030600000350b00c0b0f82d010742c0d546c2d003a03945a0750400108203042c0440004007210b4102e01002c00f0300340c100c4590502d010788041e51780009501c3c15541c52810b85140c01101d80d00b01140394040c500f20303070032580702041600303c00342c1100302d41c140f07254032003c031098103001850305030401d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 717121330 1250 717120080 717120121
    0xc05160302090426040e0108100c1b2a05100804050c220905010c02011d030f2b02120c070308060909070e010f05030712050705220e0a110d020306 64
    0x3014031a881c00744da1102982142c0d2000748403896042c018028800103002106011151400920104406040280c103e0590181d60282e10307410100e40001d106046690482042c050203030b03a20702d6166501c200c403c1516a019840c0030300080c20a1046ca94807070750301d0318802c1d038000300544201c15481e010400c00e65680a0411650b004880201441400780d00c03d40714018410000000c0f94038008401a007900c0b0000401d04a100401c0128001600080201c2c1c0850003404d84441e51010703141151000c00742480340240c02138075546420030320f14200e540208450848141d40000b9513480b01201181c61141c1d0100a001406100201d251410940003c54001c034484007500c00c2d40c0d13118a046000007400b41e2102881c09071456080150b0704091015101406048000507141c0150b910327120f0348c4440c2c0340b01e0396004554205a101181804408088945e0058101031203800503005065030340740c1412109480781019580303401d02c141b40c004500c03181244d0280107032203142c0d01ea1461101c210210000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 717122580 1250 717121330 717121373
    0x702060f030702010608010b010509010203040e060a0b07031701120515071e0e150a080c0306030307080712121506030203040c09060b030a1104050a03111f0c051603020904 75
    0x41840c0011420001d148980c0319a80000340b01840c180c4a1420341d1030426a10b81440340400040358266408000c4500b40d030000d65019000340c4492020031813128065101c0c80c0c003520013180103001c0550110440b001e1f0440c4801800a50f44c03503242c0d1004620b00c104c4010030360382c040c1c003c80702c1d0640207400141d132017040703070900030400b48034203500006420181c0c10103000213400034a02a040c4c640b1104140b02c3c18500140181450745c2500d0241100c04050038180b0400300110000e10703284c0d0100100d0b50103507400700510340c84184626003240c89002d400592000300b85901204407440d107040c8903941c8000d24480c1a0b001d42890404260001d510241040d11003c4c803850380070031044802d000e01001011811400ba0703581c60f1244041044840884102804002c108020001036491020b0241640e1f00009102030030003074040050084a0005078000c00c2d01070310310140c45050b41068107450304030f000d101510008095001e0451031450a804020340c4414000c0225003c11500c201204130009a8031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 717123830 1250 717122580 717122587
    0x1030f0c05100e010305100e100515030f04170d020a03021215090601120617031b06010806040b0a230604060b0c0d031508010509060a1a0f01081b0304060f0c020601060e06070206 78
    0x8c0340303080041d200311580000c030030040b0810421802c1941c140b000050031024102d0a60a000019080b440d002403c054459440100e901052100040445560541d803601c1195102c0024001901940220000402111402c00020b15038001c01000843c40710005141001a54a000041d24094841041b035411669100c2c0d0206030009160040003881262800a5443d500d024107003100f00c00a2003580c11b44c580008004111508001a0150f00298010318007045552116500001024000618401100030190403085040504807940c0500d2054130f0601c900f5403100b0f9400b44500c280d40917600c4a9014011a5030305501c00c1d0300c00c0b12110701c2c0104244d4501e0741d490340c050035a9015162503000f9003060061107083d80c200d01c100c0c296400c91014040f00b84d4542000110106800309005051100300800030f04401c03030000d448100300e81e546040039200d083c141045001410718800540266180000360100c0c503000086180c100e424954541c5e002d5201c41041c01883d0f041078030101c0e00100e01b030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 717125080 1250 717123830 717123839
    0xa0b0a060f0f05092202010c03031107060b090115091202060903120a0e2b0201020f0106120b070201050c07060b0a0905011205010c1e0813080301030f0c05100e01030510 74
    0x4100c078030001c02c0994241c40209042404101e030421300501032051754074100300404064600f641e4911449902400d241166803481e08055010f0005481c41c2d10b40c92200040314420000184e004500140c01503a0160b01680c03079407407d00b91001c031060039102190000c01c0c10007401c1070100440000303520280c071481c24900395a0129181549043d054a0300a40115005403001c1d404000403218580171140d9608080b000040d981016009095210f2040000300c80c190559000300300c0340100e0358a10000f003209660715440558201144a012a03250348094080b40480b4814040e160040c3e15140c1c4d030914103c400e940e06002006291021a000a11140001400c03a8940301d014001c3c80300c03c21144c107006461406a00b181e4526014405000781064a101c260310b4000030030003071402030706000b000c540b11243d00c448002c405501c0180780741c07000400402081591403295840d64440c01000da0f0040c0c0b180e04011940e0101441d0500003944109890342640c4260090b0341c002c3d012411070a000c0b500e8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 717126330 1250 717125080 717125099
    0x4090c0302030f03270901140a170d02100203091906200c0c0a1a0c01060503060a0c02060f010602032a0d020d1106040b04020f0117040b180d020a0b0a06 67
    0x4042c4a0400d503000894440386017030a61040c42024002d00c560801c058101e0400039603245018007900e480b60003d61000c1c2c2013a00c0329038402014181d24280c1c1004081802c1d1856a1144680103030300060003000c130641c1d001e600c2d5000b0b0b60700400700c0601605521101d104000803c2c0031201007521000d07101c00c0c10081c16002406000c810003044061140e66864110b02986803555104415000e841d402c030040050036505e240c1d001031b1555036089966640180d092980c05403102e40c1115030315021701c900340100c0c030407254040c2c2c070728a08130b40031b503a05a695914440c4c1086000d210310310158004104410b01c0e217283d03071803c0841741025118040c42540d03c0035060300d01803130001c5100c05030340401c10182600d074000340c2e94450713640b142d00201000e107090341e0b46804250002c0d100038054101d00d442241640e0095500c036080082c6050107849900d450b06020a0004042e240e20900c0303c0c0c030f600d05001800c400304080d840d58a264004080d804019500c110a03040b0041280285950300e00011400116 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 717127580 1250 717126330 717126343
    0x9060d0f0c0e03060912090102010204090f0603021923060408010c0e040e071208090406050315041a0702031c0e07030602071103070602071a04091b1403060f04090c030203 75
    0x80c55800100c11100001c0500104119006180300340c0c803060800c82c07031400001b80405128089003429480b0144180140e009e0700594019041013801d0220046604800e40d0005048900848800b204040303032082011604840740207220b000c1c4902062086680508400007d000070082c00c0103142541c0e81c61118212a40544400d0000d90407143c52091882d00c1d002d103000b1030341c014010b401d500c2e180492001d9200d080c880010031208020912840340d50381c95010b14010103000e41640d0031568400c0c5181c44045003180d0454a4100901700d120400c000c0c5000680300f805103030000c600d400820124500000407004010141c940c507071107101c441003c14005c54004601c82e01026031a485035107010080c8081241041c3e001c1d40c44904100407155000a601080303450082441c2501d00709040d1808030340c40b480d080586001d09200042c44d07900581d00e96148104541c3c1c0d00c00102e02d106c60540d081c0e038407041d0b64a992120301c0c22401e40c007034a01076010002044c0300b00e01700001607907030b44d0100e4100030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 717128830 1250 717127580 717127601
    0x40c05090a0902042a0804020a090513140303270c060d0b0906031204050105280c1208042105091203031f0f061d0a08010c02010f020414040209060d 65
    0x3030b2940701c9801141814001c8080c5a810401500c0010fa210000300f4004440d0404c1202004462804101951200c0d5001400f5050354281400240303003040c1c019290301050071045590120560400360201d6021080c0e030300882040d00d05041c1700400290301c1403081c00d50710781c860150041068413007181d9528030003441e07003c03108035011503400d00e42400c002c0400d00041c170382c90180d00319038200951048460304a80541d20309003010390b01c42c00330310901c004800c00600d40c2c0360558140c004156000385c00512420105c0d200703400d4410350009000e0112900308043e900101540380c180701d042081740d1003201116400c007880c50a02e01b030244940010b40a04c81250030748a4a400c00401c2c0702c0a20185c0503149071a4011f0f10034810001e01d0000f1040d0340310800d10a6108120700025081252041240d03007001d04400281040d042680300c21000d402084000c2c00400598604012074039000202d009a80c1200c0c10742c40e0b004400b80c840c805201c003075402100190781c000d00401c43e03041c0502d4244550f06c40c24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 717130080 1250 717128830 717128851
    0x270219020705040b0d0b040f030c0606141e0108151311040e010f0e0a0b0a170d0207123801080a050c040e19171b190803040b040c0509 59
    0x24542030a02003207a1301c08818134059052450007a0116000620709604940c1c08103002400303a8a908080b1182155040c00610041c2081e900003500c0c2440541c11003503080c21140c600d0804105480648081100c8507840c0c0464090b0000035000c2840d5824090824009007000d100c910084005600b1200c9801a2200c0c605001c00c1c244030030415094000d02400445070f5200c180c43c20070020250b001401072201418540f10b03104070585032910000d1100809a0004070f0401002e5500b00c03070344641c4000085801849240000148114922051702d541c030380140c0c0310400701d00c8450f070f62204081200036030381c131100c0007400705040d02c80d54000181c0203019a0b000381032124403500d03000d41400001707203900740309a00b01248840b11350030211304001a6103000c1e581c108400418035200860004911000c0391401011a26070b0044001c1e110000024000400b41d41c0b440c460b02120040c0440c00c02005800c07000240b00184c0015003000e20590014002c4100960030b41d0780d1400102140c1045801c280d96 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 717131330 1250 717130080 717130093
    0x30806150d0e0f0106060903050a14010f06060201020c0c0f010507230307052104030308010521010e030406180f0312110d0e030136060b130e0d050427021902 69
    0x485820300c62174024016501e00359400501c0d648a0987e105404000a80b03801c01100703082c41c0303440c02540100007041c444402486103556a25010b1f000b03420108a50742c075809900005031040c68500e00c0c20414200503102c03241801e0454442103a0942040f002d610b22034000c40c0e900c00c010307030f04101a00c10a40b103800102009581d054404031429012500d0104141c020700050000a40040c03080d410b4074000d540801d0400d01a81c900158401c00072000080313940380590148a010010008006880445e1601c0a00011018100d160f0a0342131190341c218540030305041c80014103400304041940300070b24040c07019030f60902c1d009007440000145030021451507400b00c00241028080d140c0303200c00032004142c0c41c140a09004001c10a28a1024180d1002c00154000c100003035200c4103540b0009030008800144462100009092490108a0520444049400035031148086400b071782c08018402d10040400000200460800101070005035003c0c0900c04e54074101361810001c0c0c070090380c0280030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 717132580 1250 717131330 717131353
    0x30911120a210e01030b01030f06030c0531020723010603060506060c07150c0b01030803040c050603160813080a030f060803041202060f040e0903030402040c0c030806150d0e 76
    0x81e02d201074400304240d001503080c4942490b400c0041d4070341c1c510342805d020840c0a02c41d03004070020812040320403c070500c1c1c440b0100c01e00034410310400556030290303010640c0003180b8103c4001022490480c2130030340c040d0340ea4070f220b444854003c1d0a645218414411a941000c50380d6039201d412001c480c840b0340c1d55030340c01f00305014050042c680c000d07405648080c50401551921a00d0392400d006005950501250303c1c8240d0303216603010036999400400f01d62165851b0304e451541076100b0b45003610428204030001c00d69180c203604590007661b441c1c0010320300c00c600000a1b90a00c900030f08501446c04000b68883c08034028500900701a8010b56000444501e40080e4408a0355590020303811035105010a11001802400d07030950960100d03529500c0301c02e0316101500034402c5410070b003200c8031540e050000c03240001001d5801144201d6041c0704e00c9030018422211074103041320140002d90718030042202d900349200d1400340d60074000c030501c0c42c04212115820680d568000c8058490748803541462 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 717133830 1250 717132580 717132593
    0x91821030c0309050c100207050a030c0306110a0816140304060b04051b0d02090307090c020d031404020607020f12061e0f0405151e04060902012d030911120a 69
    0x2000300c1d070608101079280d51300c88981d24002400d045008150314a40e4880e864002c0200d00020000180346546036900c070b15141190134072078401190742c2c50800310301c1c8503103c805109032003610075070360b03600a401d58510000d034480d9045480d002c001e100480e2922103020410710011032195000780710115185050000f44004c641c0020f220700280d030b07190382407605510080d408490031000248000741c3c896282c640000d080c48030507408046914a00708444083c1c41e00803522514111090301d04001441c2085040e403c0c1c4030085400a43c461810418480103251400680c1844100980b101214030304444400749003ca0a4070100084920711281c0104c45e595000c840f070f80102481c00503482c0e41000e540301a03550602d04038020007500c000002488042c0441c407001c5101c18540c032481001d080c9414030f0b5000781014402030b400110302d0004d40380e9000d807144800708005640c41c502d60344191081c03811002040c080d00222410311036080010740a030303108143e800056920201038054040c0c1031404c207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 717135080 1250 717133830 717133841
    0x40806010b040521100e01110a030c020d0c050c040f02070f140c0114070b1306021c06050f0901030303270b01060f0c0c0e13080c060702071a0409182103 67
    0x1801c003071a04c0300b418074005000c22000051100303018045001007044800c1405064090f0b001c07201c0c4000401d4130a4501e5141c0c120a40001d41c0d502580d003100329500d0304070750150031954003600b560302c501c580301306504055000b0f40c1c800c41c2683c401410000aa40c070000f03d0510240c090310f042516006c035000f0312034240320f5842402001d0901c45616400f9203031800380b0f401044400341841ca00480018000c44046080c41c070080d41c0f1003003c56a41204502d901f0b44e0070981040d04411600e800320114003030410050980507031000414202c45030b0300c1c0d90350440c090300601d1000350031071b00001710181d00184001000d071102885980c13034401641c10a03600500c801a1140c0e110100515400c12030007080003074510209450811204c00340e2a992141c80b01c0c02c10340600001040420b0014180304190f401056031400b40403160309441c41d075550b804002c801c0c810700b02983c00103500c00f0001040b03151843d50009a0b1020803401407403100c50a030312000d00c414050f002228580200704200b09240d030341031044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 717136330 1250 717135080 717135109
    0x405090703020f1c060911030618011b0c060c020f012d11040303120b06030123122a0312040f05151c2a02070b040b0a0c0305040806010b0405 62
    0x804c021620107108489030341050001e4500c1c1e5907055844140000c42010704140070014080f21950b04141515807040142d41400c0c21a651811007440b50141090004100025091382c8041c890111915030b02d0003451035a085009600c1000411441e08400f0700a518010100248014801c14410a0b2502e40d2640c05000781d036091505008200120402c01502d0039640c05280041d201400902c54800402c12265059400840030000151528103011101d82d20850f168000d90910700700b400307026130040e000780044025005003098510000381c40d16601d2280c1a1420309c1e100e14034105000ca800c11191503280d10070f543c1d001a0500030300240c08c0d54003000700016103c0050944280310f03598403d00070701ca0100340084003451144219a031580011060300381d500c402001e0003a10800380c2e207400502d80c10820150180c200005080c00c094400c1e141200d2041e1070307080c5031280c15441101c59103030810b41242070000038800803030103813000c201c0d075400780803016030259481d07041c2820801c0142d00001c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 717137580 1250 717136330 717136339
    0xf0b0f01020a080315300a1e0305120718061d04090f020a27140615120c13080c131509090b041a010b07020d110405090703020f 56
    0x288506580da00050300740c046a08001c11644035281c04038115803056030441d815902c0701400e888002201d100910001801e8030f18051442501c0b103006030961a803203805400b03014003049a08550204901d11080400c04c0d21a2405a00d803012107140c100100c40d0540b003500c001100c044555a01041e0400c0300400b030300190608240d5456054240c8005580c0000c9182c0141c2d100c03003008041105580c489403005900620b030070f01c3c41c0e843e4100b044042d59200070300c2005001044412422149a128007260220031440d124041e0b500d00e01070080785104a070540845980812801d011010001c03606805200c1c0c01080c60365407942c0d400c140c0c200003036a400060b00340e00034408059017950b90113800b8082031421480812040d1102a072080008825030042c002c180c20441c00c60200418003c11a200d14030031203000340c05211841c282e4141003024080c4c0264003400304092809881c0c10304000c6100c0e445140e0940302d035481040401d042d200e0907281d6a42551040d141801146056054218039003400e66 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 717138830 1250 717137580 717137599
    0x19032907110714062109060c040f211401090c061e0f1b060203040b150a3011090106050901020304030602070c0f061101060801051512011b030f0b 64
    0x201c906071104042c0c8a82c1c640c100b004400190b481d282c4106440d400700c0c801ca002d904240f50544a90b8074100100c81034103083c090f000008000c0c03035800c819141580d11301d10103c4c02e180d081440291442848981d0708480c48040d07510403000a21045010040c41c030070714000b103581c289500e0b042040d8146a0000303024480d01140f40c015034102d00c5841c0c103c2070201c2c9060301b103e4282d40d0050b1071008031040090019440004e85000344822500150b00440c0b14101450140d40c3c0d40c3ca013441c140c1000342c034255109003506010000a10100c00001904441010780700401c606e100e400407a4121001c401c6070160aa8104001c041c0341c492041401040d280c10001d19003001040001d48910a500000b000d09501068001c02e1005000500001c1c000040c8c290789110b0b15404060405200804a46d04940c20700c80b002c144a101802568002c2c00155031362185564180200301810300950f0b503214440d962a03100d40e0703201c0c070b500e05d441d12020480e48000400304034055064041d12256030416014a2244 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 717140080 1250 717138830 717138857
    0x30204092315131103030d0c0e04060509070c08040b040303030507021b0f0d061103010b0301050a0f08030702060f090405181501120f03110307150e0105060f19032907 73
    0x48100c2c0e42c01203d40f65404849502803900c48a00d09014924540611000c5038030241c0303200a07413141010404c45d4944000d4951a1400c1005542103402035a030000c0c2c9100118001d5070080002c1d1400a10034000c0c40d003003039103807414445070f0b0700144e00c240e00081d15401402803080d0140a5006405d004d1160034509000d00e60103e10802c4500039000e00901400c2401d50070301c00355511814540c68407000c5940c0c0e0396034400800340190002e00031107220780d5500000180c51002140048201d511b02d0000d141051091340030041c0a801020560320513110800000d031081c2d84620600b88a034802401001008044025840c41e19041d01c3c14800f00445050050040c1d4880c0e0b0b00d40d107803080d802110008013070100d10303003160f6030318090130b45038400c0c840030806008020240c00403010141010f001040f03e8003c016000d800e0310015075016800c60648554040c150030701110001143c00c4003911040d95944d244d13185d8040001701406d88507402e610b0884c5518441d01104002d400224903c0c0054912100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 717141330 1250 717140080 717140113
    0x1808070b06011b020d2a2c1e1008010509060a1d1c030603020d050604020907030218010c0201020c0a030b061302041a0a03092102060906010b07020f0303040302040923 73
    0x100c840070700a889a2003100191a00d203420b44c1d0f0069041b10310f0b4581850751100403c1a60075264040c20700b41d0300103480c244070b00c0c000c5c0302403d1140001c0b203003c1d0950b0010000c00740b03025a0150100106412001000c500074009014a03030203040c1d220014138082c0340500d454000c0b07032240502d07400c0ca08403860314805002400940117071b545190840034070000320800c809800a02c507682c4020f4200c0300e4400c3c0c00040c00720220b54103205074029184141250b813484002c40c221312420120008100b566030281c0450351140b08840d1381548107004560f000003601c000101000300c240d00c11183c1981c1c81c81042402d003030044c185201000113207419030906050540c0041c4004c041103003003d000c1c81c08501e002c0b503144a81c004014880e00240800c82c41c010101c4a100300c0d08085c1d85075800343c419000030800740c0c400002d51038101d0740c0091400381060255820000c0d03036510102c026526201c144408809a92148103008400744600030301950a1a0165690301d0783c000b64407110b2254000400440c000182e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 717142580 1250 717141330 717141349
    0x91c030b241801020607080112140f03090f10320f0307020105100302010203041701020f0d0e060901090309030b06030a060c030f110f0d1808070b06011b02 68
    0x604000c51528144004140740390600303a03007801840080350205450701c0c03461000b056030b0400003031603114900d48000103aa441c10b050f03900400040382d02c00104620303c0b003001c00c064542d2081c031080f103401c040c00b40d0071860000100d201c0111034000154151041c0b41c1244018407000c0b095a24400781012800054601080054005191405600c4401c6009006021130207000c50003141292a2810090440d00c0c40d00101c464202542c600004148903003500110081142d505a00441c5040c0c00d001e800e1032001d031b80103000c28035903400384109400301c107900d00584545100b0141c0050703000c0880004a00d040d501038805401640740284880c086644882c18106590f00206024101d841d00401310380f07010480c82016011520740303030320003d003641c0c1a08000d01300212a082400188c07181c03074400c0c00c584103d03440c80c0c90142081210411401c11031b00001c411520329050359840c2440751301e5048056011100032a600e03245c172010032000e90f0700060544d02d240002c49840318040328a502003040c80b007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 717143830 1250 717142580 717142633
    0x20f0616110a260408030a0201020a080a05090606060a0c020307080f1c1b0c0302060a08010314011109120a0c030602070501110702060711030c0607050604200a0306090f060903080a0509 81
    0x400c08100c00c1c920350043c500700d500418040049a0f03a0b01d005610090017500803600c40400182040d0206034810070600a40340603400c41009082da9031202010403449600210303c8400f40300009490318096582481800d0013880d00c0c00c041d04010307049e00481405c0490341e044084100071051171144000760710200290100c440407010602c02c1ca01400e000078021595403000b0b51100c1e00042c006210303a448100541241d00c42c0c800f456100488051031403d881902c0c601c80b4143c4014004050249080d103060030111603d081a2110200e0b5900c1c2c3c080084001e070025685e458000a150301000340c00d02c280482140c0f01540503082c0001c55001944511968074042e11069407000f018059903014030281e40203200040540360360b10810b18002e5103424080780e041d90403402a0600f403061a5903c51021075140005040d03465103800d550340d010042203103400c1910702d0000000144001b5015202d9444d10303500a407901442840d28005135810307141c000300700c0401e41d00504e000e9401c0310000341c1c0110488 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 717145080 1250 717143830 717143873
    0x10807080c030c0f0c0d030c09080d0804020a09060e0916030c151101050a0c0306080c150a02030c060c0712020a03140c01090204181205161101020f0616110a 69
    0x282c442c03d50404a40c064084240420100010b0028005600041441d00880e03d51030a1041c0030301d042069400b04402c3c803807549283c0007511891002c510a8010590041c401880d511030962141002d0007241e5207508542e03003440d950b8083c820342c1901009001084140911074007007140c02e50303807807005d502080d11420b040304100101056015005428000c441e04c1200c000700128a04925590064050840c4800c0402e10f060360114914101040c040d82e000d8000e401c401c0800b40c40582c29440e070f80102c80d5041180401d20001c0c1004109000c40b038000d8103e44d42c0c0540b1000f60342868021200000416829540488007000009421084101c650340703480c0c100c40e40711a1940d600784d002d00030700034009507c40d281c10741807048100a100074401c602d00401c01301132413043d166402d980510461481100e09604401290300188e9410b14485d80c00ba010720540e6044580f080c1d14603c0e01400b5178a0081001c66a2550240c041e800400340c0260401c65008200c11002502c5690100382400c4011861 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 717146330 1250 717145080 717145087
    0x30f070c0f0806270c46031202030708070308010e0105010f20070f0902030a1104030c0b0f04030f0605060102060606161b0b0a0509011209050d0c03090b0c0601030203010506010807080c 81
    0xa40009124140f100340d009000300c0c100a01600001406c00d01050422a900440d81c40501c1d60302001d44050b5200d01c2e031214025003050645d00c41042c95801250541c08521007001008000703040b00c000707060380b2031190710354a0f5a5414000e2041c4901c405800c603604000440066038075955002030f507400d0940300c1e501d100001102840d65a42003072600c1d0010b1721010742101d00001d400e141503006600c41d04c48070302c040007280b0074480c03142001d10403444040d007501ea00440600a031f140e901e008001511000030428501a40d9503510010113032055403e0300c4655844040007203d51f0107014440c0d21601c104c1c0c995182c2000c250307101e500c0138809074000d46004080c03051031341c030078010100c008050b001c0d1103049034851a401d54018200c1d40909182800681d02e285401c180b07180350b00030f042490f81d100d00585108407100c0d1040700c5207080d90400760104144485e000030521006401041d030740c03070250044e00940d8154018075080d01c0024080e941004020010088a685d01c19071498103d07000380510b695 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 717147580 1250 717146330 717146401
    0x30411040f0606050304110d080a08070e040f0b090609011d0a0b03120d0c14040905070903140f06180c131103101d0c0901050a02030f070c0f0806 64
    0x80c5401014807000901e4907501103400da0b089400f540c81580314200031f058105400007803024000e02c0240c010000801849066400380c06060f4203a0705c00c0b0246000080c110944000a081c0c40740e8102010303003143e480309204014101124015486501501c940b0703000d501d0704003941e00003082401c0194000c145076002c00d072210701c9508a24102c0ea0010110750344611860945541940710700c102c8030145141007015525640100301060824071002e00781d80c2014a08000c1e8000340000034240e0b001c01c90000c0c00400000c2d48040c3c2e0508140315100141014400703001040d14092010300048211003000ea0418000400001c0700311884500751802c0c2c000902001010016104e00d08030010042d10210030401c0d401c20101052080712403c842c99071221001c83c80c0a104c000381940c032034103c00020803040d1000e5010f03600030710b14110740d0300c100da01d00320a41d000c031525074202c9801117625441c8003400308203c08040710403074003402e405030251815080c2810f201d0010030200d000c840800e03114407030224 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 717148830 1250 717147580 717147589
    0xb01081503010608101e2d0912020d02070609050d08090109030b04060212060118031709040f06080c1509010f05190c060513170309032203020a1a030411 67
    0x1000c955007143c402071780c603901400c00750902620a90034030b1500540144c269401e8001e80c850170300e030b44240110340250102c10703940300c52441100c018415116400b940001e285445207800c025901d90191080808280000342040143d51020302040940d400a000395641c0030188000c0c507501a50043d03482c0003400068407841039590000e03182c990901300b04410b000322500201510260150040b400ba59018010340d501c8686468007004100c0605040c00024940041013440b0402c008800e400d0582403c00682580d4243c11001199600c03040c04002e8040c0c2000001d51520302114082c400c1c00d02c440d82d0802c41e0262110281c10000c410300c0300c4d440140508116003070140151040006420081000303440300c1184201100c60702d00d890005010044900c003022119544124050007110444c403001015401c05481804c2a01041000100c0d4040c5418461f000d01e055581c4030054920798010001d4400030b50b4090500341010210716885002840e0440340d00c943d02c49410101d020b14070340440d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 717150080 1250 717148830 717148841
    0x90606090b0d0e0604030203180a0608041401110c0102120907050d0605060105070206040b1e3f040b041703010e07050c0c041a091b0415030e0109080403150b0108150301 74
    0x440140144d1040c401415400310080180000c4085402642030060080c098000c60f46d100c0c0200191004001c00d0010316000607802e041441400085400c026130340341e1306001e91040090a03096980010020a039500c8030040c240e200311300d031000d40305551401d4007188040780e581134000c180c207607030b88002110703a0f0040303080d9209241c0103400c040d11647c0f658151402075002000441e11140d114200e0200009030708200c50703000c11407140f50407407501c0c1442502c040c40e041564415803407030340d0301142d185005c031042081c1c4241c2c02841909114149401d0080d1800d042c2c0b03009101d041e10030001400342620400000b40c00c2a050b10700b05907111044140b0f50704004400740036940c00303400e0030103d44450300750900c48003035804111440b6035942c554405040010b081c1c42d9844010810500041094000e4507054042180c645d0401152030a0300d122003034212000d40d581240c20144c049028801e210644581442e003082c12001084884800030020f4542d8000070710440b8482503c07a106480782e142900103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 717151330 1250 717150080 717150101
    0xf0806130218072a06050630071d1b070309170a020d0302060603010f200a05040e0a02070605060117160201060f080606010f02030a0f05071106160507090606090b0d 72
    0x700007902011407040500301e80e0a09045e1000e90600000c42c6980c0362101010079601e01015031f20b03403011039500b900d80c1c014420110501a40c050254005425003c107200526010200c0c41200e00c3c07803401c50111801401100c40721082c0e00c00074803c80c070009070041444019036034501c02900b07821800440309454540010002900952050940020543c0000d000c1c0d0290b20f049000341b01401592031442d080b107441d10f1664a124482498540740e040950008100c0d5a60910b0010700d01034a5280d909004103080d1218181c080c0c0c00200481405100d02c11103401400034070f0890081d14810401129155006d044040350181315038140c1d542e035000754026001030444900c21001981d030781c070300180c60300c2d411a500e5001c90301d0f404908018500c08030448010703540d65101c00c8001002d041c8110703050340260740c0861341d685036150580515920140607119260745103a41103108051407900701c0c2401c00c01d9120400460a08106021054000080d4070603101e0301e4075000d4441e00c1c1d0910340000740448020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 717152580 1250 717151330 717151367
    0x80c2701090216150e06060f0622080322170615031e071701020c0601170c04061214070803041a16030c03030e1204050d03020a05070f080613021807 65
    0x40d8080d145106805c150f06041d20b103802e841507541d030a400e10040e42440000310307502100c00c0161200c161103801c0d41c501ca80070058010b400e51070300d4040c1d440c6194441c05501c0c1c3d400c10103900f110206000440180041c182114110324505607030019980e55050142a0140c454440325140843d40c41c100540c1551a94084021000d051b61501c42504c440e418007900d95480d864020380386800390140200e584114103000281503580ca000500c000e40542440050441d0140c5100c046044e0350318010180a0305890b207026a00c0392851900310201050301401e01c03002e0b001a80e0801c420300e000710a544c2103441e68240010f400d80311001c3c0500c3d80c810007400390317681250141f009042c964000244030388a03110b918100003035449000c0195860460251241085904000c2400b007800c001d40b02c02082442030044803564403003542c1e02c0b810110640c10a0002044003c01000130300c7c42040b455401011807090f5618601d21034001c075048501c0d003407001144090040104001c01d04c1101612a160100e50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 717153830 1250 717152580 717152603
    0x1d070507331104080c0603040201020706080c0d060b03090606030c030d03020f070203010606080702060f040f14030c0d0f0e04090c0e10080a03020606010f0e0a03031202090406080c2701090216 84
    0x880b59690001d000f0b040b2640b00307046042c142400c01d6001c4a018940580080140794509402220050130007040d11140c042d00f0b102c41301d200001070040c000640300035059641c4924102000768501030f4020b10f202d101c0c0d4050301c101075035038a0200e0312007280815032038050b94a42c2440310b150854443e40304029059881c2c69400034541d42d1080b000b5001c1c41c0c059007600c41c10707152140030454158007a600a0b00e40c1d40c90001810018400844224502500c074003501e04001a00c56040d0a103481c504150011840380342201302410383c012020f040d1084211401c000c2c0c29003030780f200f0044105501801c46402e2421020804907000070350300000600070001201c05040c907a240003034031254190340040c045003e404142c16010b0080503160420031020b088410380e985543c03422a903802d582560030403101da007004880351544581c09040003804220b401408940910400d02080808180000040d400c0c03400c100c803016111110304904681c00b60501584840007200c0c012210400300c10001c0c800301d00030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 717155080 1250 717153830 717153851
    0x6040b1f0b040b0706110304240b062a070f05040207030c02030712031b1113020c0109050c032811150d090203060703060501050d180c1d07050733 64
    0x340004c10030070b44110400d008644000c0215855400f003603034000e00c401042c2e806003485010500c460584000301c95400f081d0814508041440360b480604000004d0703055841451001c100741c0520101c1b001443c000b000705500c3c02030400442d11003030092030320545d00090050241485014402452034004003601c00c07035695100c40c020a1080308008801080403035460b0300f91000c130205000034030381d0411080008454203200304042050300014550800c2e0b4244005904841c003482045038440c4200c0042039000c4030f072000c06103440c0e030451102101400c40c0c171507129044504243c40e80055840b609113400c41c2101030004034046158040d02e121030002080380030691590741c1000110304c2c02039041d101244c4905008405940300340c05414081034040040c4122105280d018a0307d6042c11075200c1040e1b181d41d600d040400c815584640b8512041800c02c54000b03039282d103c45d8115249083c01481c0500c0c5664580e401c20a800035201206240c40303032107048010200c40c00240d00c001c020100511680d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 717156330 1250 717155080 717155099
    0x120905120c031801030209060307050d060b040906031e0c1502010221012102101b120e0102070807030b061e091f27050c040b03090c010f0206040b1f0b04 67
    0x55480701c00f801e08a41d100501d650203403080f00e0480c18041c1c080c62540d51152001e480660007000f0940150303541d918000744040341807002d080581410200410064918200f020308007251202c0341d00503d40c555241e42c0010903030120503007100c000c0b1407451f200d9160510140c0c0207018450998400880c0c10f05180004c0c850340300300034180d4441070300103810720300d2811070380d415100300c03150081d000001980d00700380c007901030910800b640842e015040c01d80150b90340e4440c0e007084200b1300c0340c0202c2d25002641c8034641e0140710700c2021b00f54440085c884e007403940d1181105000c2c00b404c1da80c0074401d51210401c0d030b0400c18250b0048008040d081c4010b608008210101c03008000840100901441d00007081000b5140c030640070101603800e241220302d40304e0000c0d400404003c0c000e0303000c0200070000020444109000f56125604d180098103418403504005010072099075010700454010004110004101c001059004003002091f5040d102d40c0304002e1800141a42100e10100c00116001500508 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 717157580 1250 717156330 717156337
    0x111150403170403090e0615070605040303050906090d0e010504150804122c1c061512120305070e0d05060a0e0f03040b090d02041a03011407120905120c03 68
    0x402e03902c440810001402002040300d0030399000b40003450101080084450018001c0c1e0400c400400410843d0502c0c940c1c1e50076640007007000c9a01a0302d07030302000107254061080740d0f80000841c010308070741c0ca8580d2440f07883c0d0012100c024180800700c4003805459104900380d0b405400c80e040d40c0086055030204c09040640e08603021200313100340e140000c0344527202c2c2c2c03244107005900d012a030440d04200712000340080d40000c49141c008840784030002c1c11413015402441054042c140010305104001760f400c01040e0103800452000c08034940c0900050494951441080158900010b8584030501b00729040c0c9030609400c1d030b00680011506c0103004011400324007565400e8001c201503502c03002580c2d124140c1c00194030464000344000c0106d0b20b941c800034414290010442214003055034000f030112000b502404480160341c0541c14020305092148000302d24111070044424a00000700a00c1e02d0594009100a0342e1104110401c00804000007000c044040e2061511400b074103204980d82d41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 717158830 1250 717157580 717157583
    0x17100504090f1101030b0f0d0614010b0c1c0c03050702030a0b090102131706060d030905040513030f090b16020a0801020a112e0513200a05011b0f0201111504 69
    0x804a1004400f5980680302d420a90000a4115010603c8110400c0b918050190042e1203541c0c48081640c0b010301120800350181c81c510342241e85070703a01f40c107840d4034008448071640c01c1c5142144504500a4001000301d007002d605150103a43e40195102280c01d00d5503846009010481c103405000401c00190050140d41002c42360120456a552440ca800604480244185500f02340701041030307801c122052140740c0d80282000880c1c1d960b60004201250002c9618402083c02040c4d910200350f4010072030230707a490841c5898086541480e013840310130311503d910a15110959a1100c046440d4a444a80146070a0000319180d0003001d2020703101c0c80c075004001c4020f010f00d5442070304007004c13000050b0b141e004c01611303007003d140f111510600030200035280480310200702241c000014080d2181d04111315119981591260811062007081102c5400c11410301403040d0350203403868540c81031031081c290031241018601c0098001668031f1900c20101e419240a40522400351500c1d00164038050b6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 717160080 1250 717158830 717158843
    0x618010609180b0901050126070e09160e1003091502090909190308060109031209080601060311090d030306051203041d090a0209060f0303071b0807030317100504090f 73
    0x200d01d0302d120303002112154842a580301e2036540052150394400e040740941c1500e0040040f0002c0d460f99020306801000301d801c0e03400a10818103032000740c1032441602ea0400070103c4043c41c42d04075600301400c81045299814080d195555440a03041d1094100d10b17203080d0042120682c580c80c00311440080d51048100c14013400005020401440d0005007180361000862507a83c41403049076030458841e00060611410440005400720115100840e400c1c00d040c0b0544a903c020342c50701c0912828644141d001e075061511348841d42c01e4010b020310440340c00c0f540031920300707401240703515003034009041540040360007030310b000604103c1d500700100510a0325000c0004a44898010006202484089501c401b240e003000b10500010b0030004951904100010100010500f4100101c0d1441e0440c1e0b2041d20040b0030328041103048022900b00c88003404040c40500442410b5440c040c200c17840c20403110600700185d0b000540314903d008607180107040014024080788185003000b018403101c1100c1a140d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 717161330 1250 717160080 717160109
    0x1e010323070b2d12150402040b03071101060608060d061d1905120a090306090323090a0512061605250203060a270f0c0f03050d020607020709050618010609 68
    0x2408010003992600d00f1901201340280c5e0314401d450740f40400300c64105400503000d002c0441c928510340095480b0b4001952483d00c0d03609840105801d5441582c880001d10840e441400025110002a480056000f000100700c503096002800c40000f200c01203a0030600419142c404800000025003159034007030002c880109440c000c107207034184900d00340803000c80c0070f01c44200005503868002d805d606002c1d092100001501189049403140d00c0c2882c8000710000261503400e51920b902d0320000f5040c01e071150b02096600c00c2419903141c4d0081c0c00030980044031100b260440c0e00c00c8044a10030159031440504640d480000e1240510840303800720300c42d00a500014500380c501d4401c0f020984005100340c1c40e001d1100344c0481d43d0803d040e0090351403845d00042c400104510540940080c02254243ca03d128074500b00142482603001d90f01e800c44d0440c0082c4580b5990001342070055811400d00007500d07480d0040011200068403035900f440d49454000011000e4111888008036842031a00404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 717162580 1250 717161330 717161407
    0xc0315031005010618360912050c0d111002160f050304180b010e1009030f05030a0e030d050904110408011e060f030b04060b0f06121e010323070b 64
    0x1c601c030864821440c014015540d03072158100e0141e106c0804881e0307140021300c01c2400d842d4103c2402c07000b00144086a070021300e10041781d004114440307402d000c82c81d1846601d0700004945440d5017201017001852500401c3d1035441d03220202003810103582c80040e000c480c5100b4a4855101c3e0094803c1c0404480c2002c2ca0420318845402410385945050b510708040d449078a08120030000ca80300d8079001c001c0c6028001c4001341004551072040c5000e40001c545403051071000070541c801a810440c083e0301f011002c0c00b011900481901c0d10807004840105086028480078905405240d1150141c0d41c00c0c00540301c10801090082000d100741c00c0000c3c0707d015210b8189031100886407000905149142d000200803910550000003e00701c014001c1c0100b040318400074100350003d50010180c414210144038040b16448100c1c0c2000d800c00701401d08543c91901c2c1c0f100c040b4520748408089191003040800144070600540300548440c04400b45c590003d801c0302d02c00142072800150f20744ca0702200021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 717163830 1250 717162580 717162599
    0xf190806120606010305070504050a080c0316031518080a030510141305060a031209140a3203060702010b031911120307050a060b01080f0c0315031005010618 69
    0x200e0701407510001d050740d8844100460007820003d00f4882008030602001c20580e4444d5110b80080c01010020300c03202110500301806c0c0300c00380e45003d04460103a141000080c1040911030030094240720000740e046502945d0f02018500c0c20b0380200603a400040079502550141e00c164081d0406d26180c02405840b8200b422104c40c06034004c6500625800c0e4104c005d00b0950407203940b0440c060213240b101643c9a692211400480800c8008070300c1c00501403000844031101404460400c40d414007883e0301d041d14145449010a607041c08448010b003c100848044d42441507091801804940f414946044028001c0032040c103650310a00410140d59013007104084123032017031608000c54907211010b4108002090060030200d4419000c14000070001c41c9050144070440c2c3d000e40004950a4113040c00104030710310062800e880003480405000d100d012080a4030b50050516001c8011316038045c00191400c0105519010103034104000450341c140e108081c07880d0803040e000a025425110060030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 717165080 1250 717163830 717163849
    0x825060e0a110d0204060e070201060326040303050703020c19090b0102150112050f0105010308031902070c030b07090806010f0e130506041e060f0b0f0d030804060e030f190806 77
    0x41c040441ca80c521101c20f107010001410075501c0140300040c1965030b4034001440c3c01048903580050b0355100820001d00440340e81c82c42c0d00382c5001d1002c2d0400c5140700b100704103134000ea0002078100031000ca04001014020010401201e400a00e40074046040d800f0050f020005405003c2400342861100c40c81940005007100612080300c0e4424516800e00c0a0a00c0c46a00c600b000d41d031034424540c0c8680d650788203102d4680079602581d0b034030b41d8915020b148140e540b4010411001c500d0301c10071080340428002018102030380d52240e070940711515a41001c480ca0605600005c10038081c52000140001e203008958048803142c080380901980c8994014207298239800000e0000d0b0441c0c4000b50010b44001c20902201300480340c090200c41c0c898541d50100c40c45550b0101da065030310300600c00c082c83e00c2c2c3d026103181d4130120390f01d07012502540e5004204600141c0b000b00700c140c4030b5060400181c000c0c415218400e5520f6440391710350803c020002c5819501d04030340c10100b80c1d60b10200d0441e0500c000c1c003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 717166330 1250 717165080 717165083
    0x60906080c01090b0703020a0f03050702100503040203031c061502070533070f06091101120606020d080a020c011e05010506090a540c0903030c0825060e0a 68
    0x1c44090918160713070f010040d0300c1640c049086028081d5054001030070400580c0615000c1d95405131110124814045a0304214041005000041c0100300c0169800001ca512a61140521401c02180c241202018094580041c910f11540104e6050807940c001a160111a81100c3c0b14084914400300b10842d00b14958a40c1140f82e80c0708902148080c01c880145001e62241c0062114503075191290b1048600e2400211a07158040248903140e6900800b040300b0030800c9442041038902d407140107540c51024050243c14080c921001505a28455050300c4105003c80001d0000030701100c0844c0160491245402815140c413001041c41c0c01c008060b00c44241c1c000d0f201c000f8003402c00b207101c4925071116030210480401d51400b41006110050b10403400d541e40020000d141c00d01002c682d8075a82000b2801401070302d03000d0003840e00f0f5841504c2e18100c9800d803c10002003031085c106036401d8400c0c0c0f460b122154001580311050705503010741180380c80303010341703010881141e80c003c0b2f150b00c81100c580b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 717167580 1250 717166330 717166337
    0x1d090c040303050309070b040905090f0d12091a0103060b030d0c03020705060304020609040905421f240e01020703062f0304110d0b01091e0f060906080c01 68
    0x41c00064050390046400ca9144c50482d010b990791211000096889500049000350720f4005100c14600e04202848442d1441c0d005000300103032028005150101d00d02c2d2101c41c940d2910f81c2802030010071161082800e01914000301c072580c403030410f007000d0911007a05034041d00ca070100440f415407048040fa02510740c5540584001880c00040140c2500060008d82e8408000c00000c03055544504c0348000d642d2007400603006540f0803651050300415014440d2811882c04201c4140152810007106440e140c0c070402c040b0141c841741d203210700603148658010640754a581001c01c6820231551a41081e11207449818501c1a13049800c444400307061910b64050b078040728060000401c2c2e030b009140102030f0046800211000b100341a040103014644150075120700000740000d0140c10040416115030649020f490840e20380d855059612051042d0808596940d00494000090b1307400c52468440950041c08400b6030140640001e206c02d07c6410060745c41c1080009600c500418440340a0724140c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 717168830 1250 717167580 717167587
    0xb06030c1e2b110d20280c120e1003110307030b0609060433080103140a06090809030114011422020a08040c050a031110030e06071d090c 60
    0xc491041e0308207079076140c0d1002d030b0311800c111000e0140d4201800d601c0703030400004141d188036401350110342c030080c1148580303954003000142c4c0d801075404481d00304040600b60030480c8400e40c1c9012150a4500500100360031030111441c655203500a4540c144150202c3d4040c03444000b8500c250210398400c1c3ca1106c2d01c030701c18000a40070f64000c2c0d220f81d10445014003a2071034208010006101c0341e1054020500c00c035020342e4042285072000340102040b61400f80c04141e1039940c0359002c2c08000d01407000808400044000b68180c0c0300620401a030300c0d601c02414800c10009141504494104421060007980307010000701110044090f1b19048514446401085403030310703c10710604072000d500b041131180e006d1812042c00700003131008094000c41960f82c10601d041604e0030040a200d07562100e486030348038003014804621102c40d800c0c8560401c5907010020446d40d80150040d084a031078088090003040d082100007508840ba6001360105511500d86455102003081017408042d40e1200040d5400d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 717170080 1250 717168830 717168877
    0x3071a1306080601080f09120301061107080d08060910090c0806030d09050f15190917010506060a0804140703080a03150b0a05071401090501150e040b190b06030c1e 72
    0x3c07082641207c920800c1d111001805140440d1702d52081e4031130300000d200d19007280325200c803c2c010303100a01001800740852992194005081e0a00a08440d104031000c6022841e450902140c0744014000c1441c20b1003281b0003d1005481310200f02c3c0c900d0300a01600500010749032042c158070083e83c00003003111032412110414070910307100d01c3c2c0158003091005c000c0450400c01d80401003d8181280d03850028640c03e000501000d2806020344000d943c0c14401449031a41c0d03100196001410a85058a015030b42c60811004803225103802282d14020301c071010041c0855174008082e04801c40d00c060080000c001800704103c0ca40e0b01c01c8000c042c1c800d1210190707141c0b01e0303002411100d004a241c208800241d00c038403401c4410f200411180c45e907403600b0014459011440e41801049a8030301118036181c81d07200e50040d50402070458409190030345410900e259203038400c2400c0e42c000b42c03460f40c582c600707030360301e90016403000d9220442400c9d000c64040080020408035001000c1d8101c0070038064404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 717171330 1250 717170080 717170101
    0x90f070302070213060303260c070204020405130609241a0c07060806150c03031801021c020d0522150618150509130209040203071a130608060108 64
    0x2604400806408125441c0907a442d03c1800d402600c11960014840d032440c076000c3c1c4010b050054188040743c2d000300082036541c118450641c48420040354a0766200b0a100141c000d2241da045140d108004a42c10228550107510000036104440010001c50f180747c03018010700e9112a000b949020b12802040c002a4000c00a9401c0315404801c0103080000c0160000c2c00c1110719006400054108030400c00c55203807420382200041d40f560441071624201c114000c1c0c40f0b2000030041c0110600c0d081820184690035412550344a0842c0b0651441502082d000d4000e580101c81c244142420b08000c01c40308144103c0320507070248140d14a140440342c1d039640c4110804400d40084002d81e4820002900b021101900180f0182049001910070300c081c0c0780390702299041c1c00c02ca0041d10345c03c0800c003203204c030b9250041d00103030120380d080102d60b264400a40750003000c0c0c11802110f0050708080e0040704003c00506042d6201890b88602c1c03c0c0c07140c20445d02004102d5280e8009150070b8080b0304541d49 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 717172580 1250 717171330 717171361
    0x81b040902040204050301231003030c0201300204061701050d031101090b011502010507080c0d0f1806060501090801180807210905030114060a060807050c0f030702041a09 75
    0x70141000d8101552400001d084407c500d401c1ca40029503008a00b019486c1c00c500203034001e170002c0d501e262050861318010300c0d0071002c44000741803020001c14681c01c1f9030700d41c2c00c00e0b0b54450515a55120b00c0344041c90700029410500c00d1202141c040142d03084400418201c0c00d05984001d0320303c1d21007902030748085a80c18804e0102c60882e541c2e65071000f0114890080042c081d00702100125044c0c0d911410013800c451008203800300700400752007400031140e102422030b58844030301400450221202140140101840d100e00100901c00d19034010800090360070000032114242c1700c1d03007129a41c9049a50070386000500214000e608201c0000003c0c070a00c014020143c041e01502d240f0f4040740c80640300040345081e10001241407800100f19502c0c0902924002100b1000e0403c1c490a240001c59040640f50007214140706803800000c6e2143e104109440c2c01001088c102e5000324134a14185480750b01c50501a400350381090702481079408600428055500e020300721900b15921030810740d01019 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 717173830 1250 717172580 717172583
    0x8161208090f0a17070e2505030a02280305100b03010323030703111009031409121c140c0c010f030605180901180302191a091501081b0409 61
    0x64415800310307080401c841100a6001210300a00b0002c0c184049900703810f80060070501440311489021f403100171000300c0d42900c1000d509085489895642c1140080c2c020b004101540c421900091420507060700c09505440080c1c3d1800c101e80e4a850965840d85030070350180c0f2102e0401000104001004020a50354016800c0c0764194483d0801c1c0101d425580700303440c1500002c00038014031403800c0043c4004040d0311488001001805919500034200e1400c40ca0120800d600124010110b9214591401001042c43d0142e0702e0380051a529049070350901c10b201400140240c2000f051302041c107040701c0003684060010000142c21100454490401d1200304d000c16464040015580e22070100020307800c504240303144164506200c01c42d0031100d6620f184011880604a44400300e500480c140307809810204054042140302e081000070a40f01207421000242a1410040b0540c0c010502c07048a8000300720000c040d9a0302d11249507030790328000070100d940483c042099024602030b8004003005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 717175080 1250 717173830 717173839
    0x130b090301060b03071107050303031005011d040204120303050a1e0e120406021014010f030803090a0f0303230f0a15090c090f06030912140c0708161208090f 69
    0x140c3c4038180c000090704162161800f080c2e01192081629400307001900c05081c0a8004604500d0102c60115980b1a1407040c2c03070610481210307408940d1010409180101005041550b80302da5416010240750320902c0250002850000030070200135590140d03ca034410744d040101c1d522140c1104400080c0301a6010a07100c1c420605c1d4100701490a50240c0f000300010340142c803401400c01307465005c0d0392038042d21294405003440140042c4903c1d41410059070f030010012616035445d90302c1d141c070f07000c403800c400340114991801355401c0582c1034014950b80ca42c003504841143c070300c000410a1150041d5aa810300300c4e0003000181d08401583d11002102003411f014064150303440c1001401c6545400c00c00c400201c1d005c1003885944d0220400e0002007156140070002407045407107000031a07060700051401c04c80080d131112041c2e1003810664009400c00c4054440d40c070303600c4105a503510401d030f0704401c00250510002130707480c4050030201070701a0800700d030300d1501c80300000300060180c407820300b5070b8403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 717176330 1250 717175080 717175091
    0x903080609061c08030105010f14042105060a0207060b01020d020d0807030b120a0b061c0b070302040308030a0e0c03010e0a0b0702070e010927020102030a0c020a050d030e1203130b090301 82
    0x2580c580c52a83c0c04694007450001e650703541080001415230050040120030b2080251060720026101c400321001c4500c07001c1c1600a221141000d903c001c60000400b42c00e034419003040c0540204e29030700800105201d4502007181d40024001607840e504100962000358006401e1200c3c1180501009070340524240380015440a1600000d440d00300058421100f551010300c640d8200002001020b8021750110f414561f0310b10881079400d402c0741034450003801c80305c0d100c020031a25800307501950007540e48500b6440e12841c1281007900208155808000f0714416041010010304041c4101c1a4070702503000640262081a2282c032404071001e402d10303003144560080006e43c1c000680f1003030701070004420003085003109082801d5004001602584942c0c0c0c880c00c003880140c0e00081103541c1000d9034145040e900070b99000051030100103a1200ea0858001404c0c007040503409188035100700d00407640744181141c400403060f42d034003800350a04440c030101081840841101c001a2000ea04010004640e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 717177580 1250 717176330 717176359
    0x9030b0f06120d0507050c0109050303040306150b0406030920010c0f1a1006030e2e0b130207170f1c020702182a03072001050f040b0109090308060906 66
    0x3c1d06078100c41c000b0005001041c0e0b0401c101e400e00801420300c0b800d00e06041102c6c20000001d49901c201d100052400b43c0d211500035500108005c090000d1081120090f1601c7e038900c030107400342c40f01c640121014075010000205030364191101c010b20b0401070356900d8038000c183d91039000d04181e00000707503400203d544021014044501000b40b00704a040c801c4800c05290590182c01d4070440710041189800402041b4007003150000a50318103500c140640c01c0d0300c02d918030342a008180900d601d64000e000075016000f2070030150010300c000ca10a04d981120440c1203050600c1e50300503130850203a6602d0070484040d40c100c0702c10b50090301c0d114080e001441d201107035000540380003020701406146024407040150040c88020310200c14203000c3c200c41814000300e02d4800103440028551300500905160803081c03003d01c81c5002c5212440700c0001c0003a070521403c6403c00300c400315001c1740c044121000108500d540d900600c0320741507244e1103412454a07094100040c4500080c9120b8105100052404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 717178830 1250 717177580 717177583
    0x15050706090f0b09030307020a020409031106010e01080c01050301080c010c081b100f0b0f010809070302030a0804080d0c0b0f1306051305100207051b03120a030204060f09030b0f0612 80
    0x7107064403554202d4010121843c03c480c0058005014a095030810b0007000740700c075008200c018455a0442e00000c0713442280ca07040d0303804d81042d4001c083e64440c2d880007003911150341d180981a91110300484d1489005c1788011201840b00f40180000b0750442e201902495024900c002229881980000c2c00c100401044101e00302c0c590311821010b6006a101d642d40d88002e20030f00c041c1c4100d00c0381c140020160640401c0110b4280c1d10307113074104246000020300341d40301417100c400a50b41c000c0c04d0b6a6480264145660a0b422900a41c002130241c03101642c200e5000b8400000c22652000200e41c00d540c2d8000c081468020003400c4c41003000044c0c08480c0010407074840c10f88568210310010648540c14200540b40410300009800854410081100400d90000d1000c0c44465002a501c504c1c805032800709007428000724201380007501c041780b84412550550080c01c00c5d111507540c0d8400070348480401304ea0320718075884082d0074642da03500490344498034003165940c00840a0b00c2c02d00ba030b060100009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 717180080 1250 717178830 717178841
    0x10e0402070c120f0b010905010e180f030708030f07020a030f050c0a17220b0d1109060a0c03080a09081605010b1504030209160807050a0e0a060c0605090f0715050706 73
    0x1c0304e6040c50425000308002000c030881c0c2c090a81c0c558108101c0d0704080400ea6442401307800310514840f51050340c540e0a0302000210104041403094940318403040c40c2c4052180c2041d6501d1030800c00710000241720038030014107048816019a9410704101101c0403d40345a030145a40c1855030240000c4a400710304640041d10841c2c41c8400d0051b031f540700131000101c06000d2a11f480d10380e4842110b0402403069010151906101c0c14400018a090000204002e500c15101c1c416040303000410032958640e00624a91245800703030f04d41e6015070752403c488204032226030750000d19810003030106019035003600d050244014410000021100c004c50700144c040f40c2083c000c101154000501481182015500d994001128550500900d51064005031070550014402000c101021071904102c920a03c1c40c002101400351080071469164000100b01ca0311403981515520b05280210b0f52051000865151100120018040e11410310b0307110b82c152400198190100041804000d01064592044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 717181330 1250 717180080 717180083
    0x90414070b0715050a060f09230f0105010906080f0103171b0106081905070504020306011803080d11090f09060a080f060717040f06110c03122202010e0402070c12 71
    0x42c1c0520f034003000c540050301c900030440b00142d03013422002c20032090744e005040141c8544400206140060f10102130f40d0b001c01100d4a403035400100c09119084000350403250580f417080e615001c01c240c480e0003e43d540c900c00e813030703c0820052490042001c100210483c000c61041c1201d076519007003404142c1040d043c45a0601615655207403c00c00c0300e900c0800c50700340700d030704250a1202051000e0b00c0307840d01c990070782c0b088034020740d00040000d0180c0e00c105030f081464641741d0550038071a5240e0601e600d440e001000ca030b1300e800d89405800315510004500b0b5a680e068014a02c0c070303811114106214200c2406002203400420040001c6074800d0140700400c5800c1c0000c0090016251400b070060a03081c4407a050300000c40240240300100d080342c484d10844e00e0b00408041128500c04d44200024824030300e845625020100e11000200458080280112440d040f6224420500030305411001414100240881d040c61521066810540c0180c012180a91050002e03e60b4454010780450341e20b820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 717182580 1250 717181330 717181343
    0xd03090801061a030a021803030a09030606050901051e01031e050405060124080702100603030509120d050403141009050d17011a131806090b0d02090414070b07 70
    0x1400000c100b403003060700910006440c141e69900050b01020140710151400300280d400041e1110710340c000d41558984808003904032aa0388540f02d00040094410b03000c101c80c0c003820100c0c00503483ca0000f070210b050b240b00030001910307492400c964006451070014214141a26003072456940d10000809100840700b1883c0401d4a180c50300c2c0640c10490140c04c4020840219002030080c0f60040007140c01c140042e050450858a0740d40c0240c0c64010400000c040b082e050036804410150b016000c0c0c00074000a4130085502c0d0543c001807501c914200c040d8a0018030180000c0022030f0a2070410450ba00a03501554840d50300c8605500585050483c2070303c0d90750040307010050041e442030f00903050414140403d00d05504116441c00940b0340c00980b00381d403010100d9400034902440e201d0b013004010403403211080402034140d2801810080c030603806120700d0000040c441c0d04200c0c078400c0c00a68010044d101c01d542300d5036070a07900190002c0c4a0300c03900c41c011011908d2502103004004941c064007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 717183830 1250 717182580 717182597
    0xb010311040b090a0b070b01061d030d0e030c030a20060d02280206070c2a08100b01050304050a170f0c0c04050106020c10030c1b11030c0118030b060d020d03 69
    0x4180290701c9a85c0e44100ea2074881084001d010803604492a4155041460040300520280c07202025080740344002c16414000d120309440c0450b0410249400031a0580c1500c184026900130140c642078184806081c0b0111561400fa44e0008045e150389401001081c0d64146104480c90304120380041300c60b0350f00443c244000c0e1101c3c20700380440c607007120418801440e2500e8207100c02803404000c010014103405100250b400c002030b80c0001006981141154039054599070500d07190740b000f118501551003490030030b1b4041c00354460030440b44207641081c01810144000c1da1402c1804c1030045051101b12014003412462420442c014205613401d0401461400091400c000450b00d0607030101c0290340c00690300c000c1b29240e80e05042e0803801103040028400348500016515140030581d09211040488c0c00c1c40104a651030310b55a82501c1901100d002410f040c005540c0005051905905189102c0080000030030b068101d60740309601a0580d406041c003513001c54103158a02108401154056 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 717185080 1250 717183830 717183847
    0xf032f0309060606030408040e040611070c03171809130804090204061b0519062c061b040306090f0b0a0e060a021918030b1305010e010506060d0b010311040b 69
    0x1040b815401003030450b50b05243d8101540d61040a11a521402c01c0d01c2c1c1c41003000500780400741d0f010764003201c500c0c4080c5646003ca40740c0071021403020301040f1030712442c00d1081e0141c0c50f0341c002a01d141d030701c2c890423b00702c0364607440400002920081c0108440f401888088000410500140008100c5084003586a60030f158000d0500d1740e8400145490940c40c80002000c943c0c005014025610611907140070000b2600b042c1c00682100420001441e98181d00704107055045050034801070102c0d030a903401512101b002002103201c3c17a580552034403080c4010f0000c100d05600c0384100030310401c1124510805640c41649280b42103481e100c8165481240c151045010310100350f00c040c00c443e0451a000245401c3c109500380b42c10b240c0d0400480c5808400c1c40c1c06004940d0024540111007200a440c14071a4a5000c0300b10300d20032113407542000c01c0051004814099680283e1300107240500706295441050001d01081c1c0941d410180c48200507000d0a00410044c0041d0480c282e203aa504c0d00d91 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 717186330 1250 717185080 717185083
    0x5070b1308010b0114090d120c060b060c0606090c120106050406021507090b0702150c06061002060105090103030f03021629060607122a0204110a0f032f0309 69
    0x25a40700c4205a4109200d0b5459aa8480c1014144e45c2115007030340c2e211021035001c1090703032a041d43d00a101d520300d0022400355940100c086540315210300c10501540c080b810501056015402564a55621250102e0428504160324562215030120410704000000c14203900203d42a441440866800201840800c3c1d041c0014111210a0014000103040c8130000070450061485250000e070408a0b0100441d40d42e50801c68000041c1c0580c0c07071312050080307260394560400b035070b002d0f11070389a51110040d10340c008100d0074101c480c010440b100907072a51b2000d8803020300306941c4408140c0d007044100c038075204c26030f001d1035a24000c07076a54400604240000f4900d00458603034549940f8407008103c07035562250b049946040e40030300012001c00140c00c05071102c02c00c1c001c0356640c1c2c00c580c9005454103000000d10310852030081350240710756243c0d501a000c0e1441150a0303580080d00009002e010580240c110030006014000c005528000c81241060400c00a10100c0c2103040c0000611a04250 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 717187580 1250 717186330 717186367
    0x206160c150f1805060d0204080105090313050909030d0507031410050301050a1814070f0929031b01200616080606070605190203040b0405060106140d050c0705070b 72
    0x2d400d0000940e800402d1102c50211141314540c070415000903132040c80c440e2501650002c0a284000340201c2c244984401d4894018010403c000e06c481c21000031180703001340030325000c1c0c2c1d007000285141504001c084805000010402c20516450703043c3e501c680420455120301c207a60041f110034000703003088c00b003600b036030405001d00c2821800d00c44030803a03054001800d800c60650041e10024904801c56580382000300b40e0344180a0300e5030f0b1382c00000c0d100906400103100100104c0604903110307165544042100c0d40007003a25055880000f0114000d1149102c48016100504021a80016206541c2044420711903485c16a4000b035050001d5440c1647c501c4041034440e003030500d42e0b480d0440216a5500036400d015100a845502041500c25804d0886100440355803041d5a2880c181c100120501400d0b94110744901c1040000141d0610a15503a982034402032907103890010307151507580c00b41c00080c180001031070b03041101000003170080001c0401050100c80032034440401101c9850000c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 717188830 1250 717187580 717187607
    0x8030601020f071508060a0911180d0305030f06180c090112060605120a0f0903030207031101050f010b210901061a0307170901231603180206160c15 65
    0x180700200601c203240100c08a0700080e141460b0100242e0745640004110340171f81c2c4c1c40351946600c1e10b08505440740f0000d009103d2803001101c0205407a40020600000c01410030001e000900e05002141100c03c0d178100c001d0300310300e005104201c801003141e4070004816081d648055085000280614656000030300400812141d190130410280b814002801520807013000620324007502000448060565000c0c410504118104200d9012680f40c003074000d5008550a030081015034010418404c014042c2c00d02c90241001c90402c140d103000b0400415400c480200401c10070303404c100645d49040c81c14454481c0c01d00c980041251071034090003030100b4400e2038003644034007020410410504d402c841007441c10410702c0b13a443e40f1a5035044803c2e006040d005c920700d1a05181c580541071860b00c0c4012140524513000c0031160a8549400035000c03110740c40916a803030701c7d24808000151400501a116141c201c1e01001c101400559621100381c0454100f000a0144c2c03d042c2d40340d0036803108a50385802c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 717190080 1250 717188830 717188833
    0x5011a0403020a06030203060303040906270b0a0b0a0e1905100503160503040c080303040b01080706050703090b09060f0408030711120a020d170d06171912051608030601020f 76
    0x5811034010910001c02400742109151b00000410050707103040040750b00401a05104004094880034001a03560442c100e058070903d02d00c05400c0c03050b1a9210310500e00000602032094940740030300350340244d000b807201d040900c61004000d00181e162500c0410041c0308125000c0400d81c1460f00300b207003080c210086082040030038000c1251902603c5035149012145041142e00e954681c034048442e100c10f60000c0205010101c00d100410000b00d8549058030051420703500ea0a88032042101d660054681c0540041c0d001e0b13030100410511400208040031014001030324000500c0e44514281d4066446420290710000d080c60034002100041240310604842d03002c000141c0601280d0750f800001c601030b01c207050340300000d0100405058400482e01700200c0309901d402084440e08010103081c4601c610365a4070154108410102003180b4420103640c00c40b11074110815150030900358040c1c103100050001c1041590703110340b0322401c0710421612500c0c1056507880d018000a043c4420684005c619 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 717191330 1250 717190080 717190087
    0x1051e130f05391045140a030c0b030a06032001110d020303160c150204210c05060a0c0c061e02070e241305011a 50
    0xc02260954154926001010031080518608155082000b600d141c2c000c03a803c41092441406030007984610f2028490f10b401c01802080401d010310031020b9003507400020601050300c4100d00b0001d0b03504032a2003203500405030080000e140181c400803c0d0b9441003042484120800138560580e0818010344c206032100481e03589141d40c2c01c1c0c0195883d000712054060301100003540000c460b8050001190400514422804051111440c3c000e05010003400250b0b0140001009031000440a4004900364000c41c6103540790000100b00040310301c00301e01006050074113200401e150540415041c01803000050b540c5146c403420058000c2d58228122800c1d0000c80424003080003050070780e0403a00c058030f0007980c03600349210490b0030b01720a8200601c41380204c8400b1542e04d61000444944c2d080e40849042c01000c8148160f0b03503100d8501c5000031006901c400140500e440500042c00341c215100d03822424481d150001e8000b0441c00c0241c0724295541c0010041040381000d41703840d40034081001482d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 717192580 1250 717191330 717191341
    0x40e0312010b1c020c03070f061e05010b070803100f030c0e07030504020a03140307020406150801080a12030c0507051c080703060b0301121e0302010b030607090e06010807180801051e 80
    0x501c1c24140400c1416075138085080000104140200c4038110360080843d4415180703440c203100288170208481c10007111503a41014404040e100e124142c030401c800c040c1c14403080d60360b4101c1c0d683c001402c1a00d014420880050380104003000c40c0050b500c9041000c1c20b1900f0300303a00031040c1c100100148101402e1a0500016864580441080e03a810880040344101d03d500707038034030314414048003d4015203030140018507100d6200c8001586481551094100d999545480c0c0e42c8a00c224000f9002c0592102580c880c14000d600c041c0e07181c01c2500701a400c0407008d49569003441c00000f01e0004140c09942d200440b980e016810a9205405007001c0141e00d061030b21610380c43c00305001e0301c12000060200c103024003240a11122101c1c1500880c007801189520300203000c0c0c40700100300e85c064480d0201140d20380c1e006071001c038240c40c030110381010181da0f61001102d54100152540c802e0004031a52008030407040804980a84840070000c12036003030510311a003841c1d0415040000c111800c7c8107000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 717193830 1250 717192580 717192607
    0x60a0219300315120212030c0a051c0206061e03070302041b0306241b0c0314060a050c030408090f090709060905040c0f180e0103033b060a020a02040e0312010b 70
    0x850365806440381206d80401c40e8010386544213101484009200300321004040000008182140c21070302c090104010207110380680c1d40b0201900c0c1c0503800507184400e2885004068400034288100908842103659240c000c00d0440380a41c00d030350141200e50300b0303105250350903000340c100030003506450344000f11040c070070310010303e840e000c0c0182008034580c003100c484401c0c4912650f206400607110841e90740e89103000d5003007020f00b91000f00030740100d4001860804c00d61050b01d20405981501500d582d0792581c0780d6020390f021840080c0e00403400070240d0380395110f404c00705120304200d45500300e9807030a00d000988a5403070303a03018034412410714400310602c603848000d6416001982c1004100640480c001c507190050a070009010102104000002e16621100140e0511042901c0003070041201e41d820f80c003401d1040c0d1140707010300c11101401c9941040c8000b0021440a4415a40c000c1c45070341c00141902c08034a81031a40d0352010403101c04000350303885010b00502c1028510b43c80c1100e00085039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 717195080 1250 717193830 717193859
    0x50f09070e0d02010c12050c16050a05120a060e0d0e03030f090d140d23070b16030f1d2a09040c091404060b060a0219300315 55
    0x440c0104942030b15081103900071076041250f15403003000401c940c0502080101107400c018403c070307214400c0340940c02105003410b10007030a4840240c02401214100b81c02c4c05280440c2c00b07950482d41c402d17602c0c25800f040b582e1140c90442c0200201801204400c0301005004070380d00040c0303d2081c0c0003080248011480142155003042e01903680300c0301c0b0000c0b0300b000301c1c45501c401101c0400c1d0082c0c610340120680c0c001c2d00c25198160001141b98244040c501c2c150660041c40c2c0000c00480c5024081007540c400d0b00d0081380f13408610325011446a10070318004090b00c526941d02002c401122000f4041d84130300303220080d01d1a0302141c0700c4014554054000d600410209a02402108040041000e1190454400000d882005014860880c100d955100106012202614100e1a00900303150300c2c5032100494401d18155802066003040c18440300000c00b1800b0790444020702d90800d51200311a82c84000003039041c1141055440090b40080542030b940040300d444001e0040000610140e10b001205 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 717196330 1250 717195080 717195107
    0x412060b01050c030307030606080c070807030e1302070303020904050606030f01150203090d0b1e011a0c190b07090504060b03040305090a1e05030708010b0306240613050f0907 77
    0x30521050650040e00d05224a030078076042400000108421542c0607001481103480326641e4580da6520352442c04403600544000400e020010404800070921074686078031050002050124004455401c9000301e0380141070481c04250042040207413840c091040c154002c209540151031482d082c20b400d421010140150384071016000c050340101c034400c20175100c041034007400702c09000859090412030a0000c407001100380c0303040d0b07051205091704040800d040314000742c7c00c10034140044050800541200b04080b0301c1d481180c00c0781041803030360101500343c01d0040c01d4980d4141000180240000d030103800c454002c41c00c040c4200300240c40442140d5105405280240d00c0d41803940008035104d030f403940440900301c1c808440030b11603402d603850042104c0f0114211040540d84120582c266009042200d6060300101300040b41101c0d4400b0300c480841c182ca03c507038440e00030400000e826410200300008400800301040c0400e09200c50202c54011003118403010701d1400c40401000310611200c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 717197580 1250 717196330 717196343
    0x23071407050c06040905150103090206041214060a02030f010b0f09010c0201030b0d03050c0c030f0613020d0803152b0204020d0e0109110132211905010602030412 71
    0x4200c401e200003445220304200c802050f00742d07595518211100a00803d4034029682041030300150125802403054100c1ca0707502a00d003504191410000321490885005c045d1051422487c500c500e81d1000d001c0e0b1445540000f1005840b4200301c1151486440142c1121101c05001c0003100040c1e902c2c20b0580d06681c00902c3d050500c0202c520048002d001460710068111882d0780b034035401c2541140c050f2a181000070221102e1007003003410541c3e10383c2c980c0403094040c0c0100c0701050b0304505110381c0803a21800030b0040b0420040d01d5554540315070045412000d4201500c080001c145040a8500c040b801181d5200368292107140741d80040c40002c0a0084c031440e80020010f40c50741c40380c0c00401581381142c00030020700401d030078000a00c080e0411031a0010380f401208c06940350012882140012903038003406010b82c1070300c1d000304841d48000300c5401b0000086030030402440641e00002e00ca002d80c44c8a050444014440c902c1c00d991040e0005415074006000a000c00034285c050110303065006a17 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 717198830 1250 717197580 717197587
    0x8030108150c0f030a0225200607150b03160e100303020d0e03100c0831060c0306050d1b241b08120910020a0509240d230714 55
    0x154030000034800c040f11a01d4810850300038400d42ca411f078000700032950060041141610300c4500c1d8007401c95910703100c2c0303038401014030800012501546015010210803080096464040d400180ca0700804001d44041c0281128051003131a0560100300d400501d1051141c06060844e42d021b034603420b0020114041046180391000c0b541d80400c41e88450380720f1607804001c0300c5c1c2c6c144030082044404488013425843c0150030222000f0001584110300310302c0c4403180040c01140d6580c000a801c481803c0c03410551251404a629960104a210814407812250b00804a500c0010f030b45000d46900c90340c00440640340501c260000e583d860702d0880d034586401851000015028403408810580261002c4008075003d84010350804c2e00c540254052402c5544810341c10a03400164421000c24000050051258010300d080100c80c103034419400c02616005241e01d030b06406590380226040c0d0032100e44910301c261081c86404418140004850165152403528540c0680700031030b0402004444040003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 717200080 1250 717198830 717198841
    0x118060e0c0405180609070302010905011202120c0301030b060904120c0f051c0210060f060e0d062c060603030f0c030f0f122202120102070f08030108150c0f03 70
    0x9004580030000001c004010501301038001510100135141020040e2185501040351b201c400540c1c0710460703a059681080b424108001180e500501074640c01c427954007840000800d44031030340301d18492078180c0d002d1502ea601d103080060030310034090903140c000c2d5060f000384408520f00b6003d5800030490b074180000c484260f0f1070000d03d406000030000d009802000b1150000401da14200108041a0b90031210040952101c0e0002c03200d1a02ca2101410380d10b039401c100c1103004030f0f0340050440c40208107502004c0542c50341c03c10780b1841010403030010740307040080303140c40309030245011902d580100810407443d0490100382d0b00d10072501c03014940359011881c054001e504204840c2085c40c100f80701520343d001c05c1c00c00c400c0c64105a001040d52460b80001500600c0440407000070071051110301c0c850f040840c1c00740611540820300078005950200701e0440410405038008000328450318049030390b58174112540e802c24003040d059286545c0143c0c280945180084c00f030791180c2600580c0a42d490300c46 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 717201330 1250 717200080 717200083
    0x80a0c02040203041109011a0a030b0604080f06220b0a2a020a020307171e0705060423010306061d04140103030f11030a0c110f0613060f020118060e 65
    0x8000003907025000208020410140c2c0f00040e01900040d41d49640310707601ca04a403060760410202d80301c3e1402d005c1c03020361900c51181d00840401c541c098001850700da10394000604101c5800e000002c1548aa0140004a00f0100c0b0b5811242c40f40a02894600147c0c1d840c030740b1144020340b920010035160305800540c103030341c0484564107402110303d8000d00895000040d442c0c0701184403da00c00c0c0121440047c09402c000011400914031501918100d0f02c0c0d608040300c604040c040c0c00385681b050348000b00c0c158840788001c0015114404032962480000d03020008015042e003801810941000380400083c0d8100300c54440c2342d20008016a1403c5036007000c64000c1142104902c11801660000020300d034102e0030701c100c2d101307140d9140748442c5100c60f1020b030b90348a0302c00707a14002035130341c4280130100da080035100b100c002008202c01d12011643e40012800c3d0000d43c0d1441020307040820407c8425045820b110050040703000034060b0600700030034000b16544070a0044c2c01c0c0c9482e4010344c5070040e070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 717202580 1250 717201330 717201347
    0x1110321180a0507030506090c010f0507030c081308010f0b0a03150e06160315080d0c0314030421090f0312032901181a13030c0308030402100e0d080a 66
    0x81c0c00031500c0c008242e05060341c2d00c0199100c240c4950040c600440c1c04800089000c0301c80303040684410304c001000c1c140071985944580415030400c2105942800000e50302e100400d04031100d21618070b401818125040d00b19840e4180300c40c1940e00d0404031306081e880d40c45030032046980105018405007054000780c3c019141c40a520585401001e081140110403c0c0c90904005059642000103070303514580303105107000e140207804440d8054188210190304c54118040c03440d200b860080c0d982130020b01e030940300350000d480c21104d1a80585801000b0040100c02c03045591540c58128032061401c050b20641c1c24a5010242070030b0800c012243c2810300a4000e00751071400b5a01250304070b0340b1038100707503c1c07540360001d441e0018500c55002c45214140d207565030165440c1526400901c54880842d00303140d40089000031482c83d60020001c049100090100010740c05420000d0b40c900d007510400042046c80b100700d1041c06403410303007283c00c1d440f000035003242c95900c02010341e40e4542190b01501c800c003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 717203830 1250 717202580 717202621
    0x11040b030f0d030c1d0307170106050a120b09031201030201260f01050a050f0105160201230c19081b030d0e03120a0908070b060609040606020c01110321 67
    0x1280c06490b030880381d0703d580610028109580c645283e56500441d10961054400d0040e17030507442040306000d0480030020501420841c04000100140e4410200340c5d170303000c550710906203074810304921014007621004155000308071401551414050700307203914003800103010103410840c440c1c0c0300014104041c64120341e991101c803407118180c5400100e0085076034090190900405070319400080382e0411040d4803c10100c1612100c0c2020000030303030000405544207040e0304004041c00c0403403044034001c0c01048810380f1000c0082e40c0703400a56080345450403860342c480901c29078050303003400301d00e045003a11000e02450a4000c042404950703100d10b10300540f038050404a1400407210b0b200300c0b000000300104680c07842c0d43c0e604c0c4e6840d41e03101030031a060990b0103084d01c181080340000261400c6140d988c00306005026500b0444010085800c640054018034003581c00045241c1c181e40c2c10003414070740104c1d000025403505c0140d08520002e0f250180c041d020440034080032414034008051010a40d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 717205080 1250 717203830 717203833
    0x5030d05180106170c011b06110a0305150901170c060c030c06010f03080306120a0b0f061915030b0102070510020a12090f0e090114180f030711040b030f 67
    0x1030810704001103000c1c80c1c07120400315540c80c0550009031040035440c000041e4524801500090003074800545e0b00c520000c0030000003079940c1035650700040c03243c8502c0003001e86416035103440f10304201000e011114040c0c0801c0c4595000214140940c1d40c1c55540d6040d10040340c034004040f0740c206040c91800e0300b49010f1079488040442d01e410180d41c000058591a1905400c07100240d0b650000c5c0c048220b014007002d4040741041000078400d081003080c030418200e4800031140c01c010140c403101e45020301681c501d46120f40d2201802110b01c1c005140042400414008a80c40c80c54845000e5064040380740034420706444100203034031030b07000b0301042d0001d02d0090400c0350f0040c81d49100a41301c9003840360485001401c584280c1800b407080890300c00b42c3e802c8a114040840c20403000e80d102480081c014449503490312550140380b5031003a241c0f4028a11441d1007817112032000c01705400d0a00588100b0000e9005200072004900389056042c0c0c9082c0c00e030f0340001d000d00d00402203810180c4141ca2503016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 717206330 1250 717205080 717205091
    0x30c06040f080d0911031623011106070915110c1201091403041a0c0703060203040f1b1a0703080f070c050304031104060603090201021b010e0d03020604021905031905030d 75
    0x602c1710520b00e4480c4500124159000b0300b02007003101c06081c007240115007802c0305035400035280c80c445c00b41d41a5030402c1414550b40c10210494a40d01d802001c45031000080c4100c2010007000b80100007001348840340342060009582d103ca500343e503c640d660032881c443c100c18100406c8081e802e6100305005134101540a0303103c503489090f00d649138000d1003900210103051a01103415000403007500c1c802a44035014180c8035103541c5501d0042e40010744162000d141002034140051503408015500f485074049010700103151040810001d55111410314555908029800c00660b0042000b948010f940c1d0040c10302c1e1b01d813120200c4100401e803500500d00c0c4000103012050040941e01031601c0e8504031005d00089403204d10440581e401e00c00000e02503403010440444802818200e1440281d041c03500c41c0400c0c888400151481c00c81003001c0c0c015030406e1040c032080d4144500b141000017443d00403800c0701460b002c0400ea5a9128000549d0000c0e2809540f404100041c0210341c0f00030301e4000305025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 717207580 1250 717206330 717206333
    0x306031f1e05041e0f080705010f0c0e040e071d10050607080c01050c191d101215030809090c160309150f0806040902011701030c0611030c06040f080d09 67
    0x6003002c0d07401365404558240064540da0800150000166004410f840c003403141d541d90401ca0f40000008072015500c0b4454a07400054922a4458403800b95540c003c1c1456040140310884540c1440c241c441e4003c400103100341900c50141280702504601105050f50b680d0b141c010403c029600130780e52081d00003500c04248114100900205882d490080103661100c281c100c5c014070442c0c070800300d40590341e03100d40701c81c60044010206020040a0f05841584040006100c034440d46040702c0110b0f8030900d02400140c201e11611b0030030a4200b6100381c40e00d045840340600e5001d20f40c54188101045000035030102c1c034030001d441404828a030803d020401c140340c043c1c0b0354403d5014449071200052000d540e01e91140d26212b442181607102c000c0320b900d4200901000e4a02c0071400d074144100e46101410a10054034014029405200c0c40c102c2d09090800c014885408603060f030354036500074481e890f6640c00224032130360010b034007200c0040620b1481c43c042e0359034041e80c09000b2146103000488070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 717208830 1250 717207580 717207641
    0x5010f06050a0806010303021509011d06090106080a1502030403050403060f0902090a020310090b010e060309030406020c1e0103050a090b070c0212010204031e0311030301060c02040b01050306031f 86
    0x1020741e07074100c035000c00580d11203640c1665544248405001a07018041030800c6104100000d50070514a900100c0c0d050894040100044081c58580000d50302c0702c010003600c8903003032040c1c20103040366001400d8500c1c1152500060383c201a040141c43c20f40c0000440c0c02c040c0210112001541e00ca001445082603850250700242039141003070b0f0007800709000042c000e0140d0700c2205c0c0b01d80310f45010810120306000003500244104540300d414011000c41f041d1030366842e94081d512988501000750740e16400c0540c024240000c41040c1405200400d41c0e1b04101c48144016003203400d800c0c640000d07150740d6080700c100504070805c40500715041c00003e06c031181e42d020910320b0702d1074000d070350011252010401042c200d1181d4800503190381c0308054812100d030922107809514500a2401c3c034000020541001e0a50744203030f02010100d0150441141141858000d042c0c82039801d0a01c030b4110f00e009004251105401103000f01c140400b03407034003001a5955071203004104440c4245280c02c0d0000c05200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 717210080 1250 717208830 717208841
    0x6060a110a14010c0516060f0225020a0b0f07170d06090c020c0901080c010c020310060608040b060a0b0a0e12070602010b0a090501241e0c0201031a0a2105010f 70
    0x842d542400c6001c2c0c8464000c4041340e060580c8040041d6120702940c136040020582c26034962042d035001c00c00d8021984c15400d00b400a95031403540d0480c1000f403807040206200241e80500144071040c850030340d0102c80502a1820305400c9400030803003110328147c10071144035145034203038107a140207408181461160300100e241d05940d021907003074584420801684041c24400e0203001d42c05090303004100c1d446080b40c807070b00c1c4c0d2000d0b00300c40c50260402c003108242c402c5034100c4400206020204000d01190140031608040c00303031901c000840c1000e17444182c520078641c1d0b40081c48110f0035000303501e8455030f080c90300040e06501940d415586941d8028043c0c20302d200401c0c07103850800b202060303c00e070500c00d10b41200c8802c01c100c95074820f170218005401c0b141c40307840c00c10701c00c000341002c100c1120480385183d2036185a64481c4451075a10001d82203603030000344d81515a003034800b407010a480700901c000c1035804191000401d501c9981a248450b000318800619650910742145410350494004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 717211330 1250 717210080 717210113
    0x9130318090c031a1c29060102060c0a021903020c090a021309020f04030227070c020108070c02030a0308270109050f1501090b040b030a110f0406060806060a110a 71
    0x340403000051142c404800741d415002d40d404000d07001403035250b9844000400441d4401d1b40021415540d050008042441c00c140c0085011201c004200680d0381c10b020040c1e000c0002814903050220021000350b0b1150404081060b80d6290340c140404e043c020084000ca00100130f00d82d40c0c0764909000044080d400c0a0b051041180d28085e020800a0403802a198189584e4048074206495502080a0b692807944140c801c440640032107400850485c2103140310b100c41d0340b594120100548001408204010718560810410b148550300503680443d0701040907815140139062a141d020941c58010b00000000d901c05088110400e0101019041701d0f01c40d074000d405880b183c18100c0b000d16141c43c0e050001e071503e02031a100602144290758000e90700b4600140c40005c0c4000c001c000300b0300d4002a294281d90148904034040319070710302240312003261175040d50b050007018504980a0640040900418840c0703030b001c1210602988250f40d000b094005035000c8410800880c1411202809400305 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 717212580 1250 717211330 717211337
    0x60a0912050c0a050126100305121830030d060e0108060601080702100213050904082205010c0f05210a2709150302031e0c0f09130318090c 61
    0x100004e0a6002d09501c1a02c40001022510105454918104400070051411f0074011001c0404804a0010810889010003d95240b83c0ea541141200c0325650b4800d85802d20442c0c040d030807800c5490800c054002180315070305038128850b1040165606502680564145003072810000042000fa452015812101600c0c1074820342d444250046130f0700002103030410f0150740306115012480760305a0050400c2c4400700d212002c01358440740003544092040e6004e503890307840854100904070158900405010710340ca103124401d460000080d108001074413016024070701491120003409418014110706600d00103018841440040704013085c0d41041d24402c002818546a4003031561000d40800e401d80c0101903040c01003460700e03508002804041540b84444081d0250000043e2400c0090750288080180821140e56021070b066103490854030b607c078414100d0303503e8425940c544040854000009006d20740d641328079070406851032114100c1c110702e41542e0640010b13140c0010340c05100082035594 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 717213830 1250 717212580 717212599
    0x110103060b1804050a020a0206040f050a060903050a02191101050f04030803010314060a201c0f0c021015062d080a0506190b1c0203011707060c030509060a0912050c 72
    0x5c0c440002c9028001804000d64032004c0032401041e00c0780f00d0180a64420300813141072120b0780d6110803d03a40820401c8010400203d001c5541d240c040c0402504940c0f452000701a030301c03054a8510b04102001a0a4140f01c00002e20044c4001c40d90304803070140d9006a20031341c0c4c03035a607072a141d25101c0000861951600039a0081103a420442c050111030513401c01110f040403c209180300610340c00504c1c0820710043c0b54a400c0246049030081e450500d410080004450398903400103410060828010300c4e10034030b004100e413101208019440107070f922a10740b44900c1c61030240d84040c40181c1032030444198a1144102071002d03407007000a48281160319092003a52502c40a0104800c4403120420742d40300d43e540c2c140180c0c3c0d034040240038000185150401086036105094080303034400c1e00309041074115985a4a843c03403040090b1001040b00340382a03981d01d012500c00502a020f20b2260780d00c0760b580000c10380807440c0b1070301c1d4503005441c01c0034244410200d035140c040d54910040220501501c1d00c070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 717215080 1250 717213830 717213841
    0x10110c010606051810050702031e0709060f1511070e190b03030313020402221707120807021f0e19120323070503040602150402060403110103060b180405 67
    0x1801501c03084c1c400b0124041c02400c00000f000544034113034000c607080001c14002030000d40c3c3c041040341400b2188155228181c072a500505061102582001c40aa82042420881000d2560484080314110820b54400c0384080400f10b940104c20030b1090800d00c00c1c00c0f00400c0710b040305a44203000c1e04240c0e002900a240b02045c04064480400f205649a081400052080c070000344074036118501c01440141703050400f00450300d40510a400d140c10600385404144004421030328042d1083d000d00c8000d043c82c80c43c081d0100f02000a0440081072044c000c12a0030442d118443d148000102c86208400ba01c1104000101444e014644c910700c41c0c50018a402c0901020103061010356050403c5002001c80a4030255001d0308080386150010340d1214401d00e0880454000e0503400c2d200b207010755030351890010700030320b89070030040d60b180c080641000b4000169a143c00300d40449038000c00c0c3c411500d0200006034010940795010f001c1151002807032007500000024800c41011085074200866105e8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 717216330 1250 717215080 717215087
    0x8010f03020d110f0a0b1213020d020d060e1b0f040605010210090f02030f06181f0c170405160b120103260a031a030607021506010210110c010606 64
    0x26848080e402c61504100704000c60010540342583e140050810050784c20740c040822054680c9a00c0001d44010200e041488182c010502641104054032031282581c0950001030414030700c2a402407080003441009010411181c00003090010701b1000c2d601c0e41078214007231b0381d81c82c5403040d0014422460300c20904804d2426101f100180c51040c1d00822680e90004102002040c1c1403105903022000d120201006990030404024100d01200c0500303403030b080482c00850102c0c0c86c42c0e40c1c2a2035410024071407180100c0c00c48004003070321a5820100396450800750540d840c6075600f0b040d544008101c030401051003000640040118038081a9641e12a40e0700100c95182c00340d00c85581d189400c0000420203d4500803210064404065000e00b00c2c0304005584005507100e102c001c80800d40782ca48100301d600e081c4845400a07078050700a0f00443c94603840094035100c00e044042000b00e03c00000c80e81d283d20030850100c1d8807076110b100b00003801719032207440101c3e04100c175002a10340c00e201021558512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 717217580 1250 717216330 717216359
    0x80105011814060114040b0d06030201170403140a0504080f1f0209130e0c090106030e01110711040f060b0f19090810050406020f0714060a1a040506061204120801 71
    0x84041024809441c0c000c011114960310117090b00310700505200c08560840580300a00468100f201c0000d4001e1940c8009880f07a40d0743c00e15260070080710f50410000c0394000c0240d00710031010400041da910001c81d019580340c00b417500000420b21031204008011900060b1700030181c01d43c99420142c5440440030344c800c1e4803544528a400440c003004840f018002504600548074a04003681e28011210b408078908031801d80c40440082d4071083c50030080c0d0001c0c4580c2c10380c50b0142081c940740c224240c54950000964041c081d000743d50300c259501180030b05a100c04050b1083e0040c0360b0f41e80d441d5860740e20054208450f0102511598111740042c41e000f40b481008540c00b203c060b00030b142c000003606000303000044c810f03585203400b0440304032130340c1000e001421010301c200411040d805070140c90f075251440081c085604540b803d60f100c110540003910400107607004840215042c2e90700000b0614030b004025281411009040520040011510303140031845240d50702c1403491b0781e80e03030114a030004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 717218830 1250 717217580 717217601
    0x3010807030b06211e03040f141203161b0f0b070501060f0f03030e09062b080a032004060c0828020c03010b01090e0f0403020f070801050118 62
    0x900440040002900000c506540544001c2040b0001a113031042c005a9900030b9044480c550811030001a01d00000700c402280020140c000f50b08150400c2500040145903008100c1e00950001203003480f0b6844d2440c0da801c401919050742d46800008850411541c08204222002e00f9401c0c0c0081070002d041d00c5402c11541070b501d00c1e10142c1d281440c251490784c0015000e0fa41c41d500d456000c228061000d10f400c0081558070441c485080c40d5081c018400031803044094400c5881e001407128650350400840c1e00546904800ca8910a2944000f00750390030550000708042d0340404d031840c0054141c1c6c4074802ca84840c48900c2040c9010b9841d501c0c640c0300b540144008602080307500ca001c00d840d1009400c40e40700075691040384081203240e00c0411411032418400680c0400c0f50b035a41400e0a010b0000f800a0a0a000c114981050411110000f00911103100540c1c0b04c0001810715200b0407070458000d07000e0083d80c500f15101c120041c080d003824058000c01401c0c001c0700300e0413102e03148035000149 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 717220080 1250 717218830 717218833
    0x131103040803040206040e04050d030f0b0d1101030b22050105031908030703060e0405010603120e0310090303090b0c030a050112050606370e01060c030807390611030108 74
    0x5540e2651001025040500181d0700403005000100380c80042c61401c5002d07602400003010094403c640003400d9400001c8426400d80c10100352a0070f6403185038403454181d0780700d6000c05810302078078012001810260f4409621005506070800000c00001181c11100c0b40a0310a12050b80c03580d06143d03076a41c2c44010000c170440202481004a00841d0146401c003005103004980d071913445000d4040ea0301c2c165002d6031680d40d110b80410801800d5000d142d130140031801d046480400c000c001903103e4820341400003045407601401d00800d4480c1e440b03418003039800880d41c61700d402c0c5400d00c803100380c0003111103000702c41c50403001103405141e801d20041c4240e8494020049540c074241881450b0407071194805001005150580c1501c2c0c0c1072013a516540406400c4001e024035120007041c412174180d1020041c000d081c05030300c02080d889400e0940c422050700b820144044010350b0040f494001c407245450004046088281d65029050000c0d6118050442804095109081c01203244420300c07400415 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 717221330 1250 717220080 717220087
    0x60f0914160809120a020f0c150a030e1e07150314060d0212011122030302030f0f09040207120305100537060e09070935010c0207051311 60
    0x1140c41240b50a41c00b207025403d9440a51000d00001143e4001c1c0b40d4890141c1c0022020681d01c0b98100300e07a20720b21600702c4c0c0d283c1003000035856101643c41103425003020152036107030f41000d445040140e00900c000d03000003142070040700c5d54115151100703030041d1141e00000b85846461079100b0302506048810b0001030759a2074850344100315a10307c402404981045608280080703900302849180380d00f800c0404440d81e0340b862038140c1c0c0c01c11006c00c8200301143c032142c1e9080c40883d6001050b145060401e0b120305940750081103032540c250050f20342c0301d40d10a00000701b00c0c2c100700902032030601e101e807140c40c04d00217504c841c5001d424150340d43c09181d4114014019108014940700680d0f400500c60b081100718101103000720068445031034110402103034021000e03c00340e0030300d0094140c2c4191140b404103616401c2c03606034a0031008000b801715440c4d0004a00001044502080310309000d4420000c0105002c84000a5140d980700e01c1f80600c140c51182c180000312085009040e1050a842004e515 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 717222580 1250 717221330 717221371
    0x105060307050409060906110c07050108130605180f0d0906030b03150601170c0408240f10080f0606040b0f03030304081b0a03120c0c03020d120f060f0914 68
    0x2804030590954466131550b01b1000814107a10800159080c0720b5117a42c1c4e01c0d6200c099141c90100076038041030420030007004014403030821421214000d40e001c072000c41d01d91543c0d5001d15643d503000c040303210309001300c51a1034000c003000590045035103402d80b5110142980c880090b0101c07a02d20320400c1c0c142e0000841a4041c0311560325040c0e201005041201d2a10a041280d0707070078000846d0030650b0a10002014400c15008100c1700d070710081c3c0c000e80441d0402548203074040404000d0101e080203230300000440c10443d003040701900070300580c1c4119a4400c4544810320f90301c0b102690f501d4083c0b803420007441e41c0b40c1024107510342c03050000b400a615640307555035680000c0d404502c50362801030550740c0541e6184014408185c1d1070f030090303a5000042903044506012603007c510b01d070090222000174000002d13008164a10f640c0c0d0241051040100d03626411809000041d16090728a840c2000103da50700c424103c15064a42039501000013210055440000840c03c1c1c03022001030b44000340c2d941 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 717223830 1250 717222580 717222589
    0x3090c03060f0f1812130515070f060c0201090b070e010f050c0d120b03010204080a05010605271504020d060f050405010b030f0c0403020d20030706120c18120b0702010506030705 78
    0x590241e8001d00300d0390501080c101700c40c40754114254049003107000c04400c112a1900e11084111041c00401c02441c3c07681595554000d19440c000003001c1d03548075000d54507014001c0d841001c2540e08400388000d10300d030128005002c5c0d0400c055a03070100714406c08003080c0c18402c005840e0300103501030080c00c40751030449080c0c58002060402c0c400c1517845088a17a01e030b40b400c3c00600000c004000091002c01c04c0c5107066404d481654010300d0103460f919040f0024850340202c100090140da0403050919101c8a1510104a2410042c01d4200f0700029114800319400e510040031104184d080300c0c0710540320b00c10030054078003e20600005510600211303a8030f42c0340106840c0c100c5800c41000341b07003c3c1e40e1f030f0200d5201ba0a0035010b49106a4a020f0080d280520b1070001d1500b2070100c0180c03100905008000e07101c504030440704d1644a998100240c802409414480f00c600e803140ea107099110f42c2c41c0207510f181d001200d42110b00860720004074292500501816010f139200a001d01405070424042c030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 717225080 1250 717223830 717223861
    0x1a040b0a1503032c03030d0501060801140d170d0618140c031618080606092a09060c010e010b030d020601060804020114121005010f14030f10030803090c03060f0f 71
    0xc4d4000500391401d000030380e070800042084d038090613404102585022005003030110164031000802e04140c042080c242e07519100c0b50340d104e90181075515100001080c555040c0906000d1107111843c16a02043c6441650800c004031031020344284007909086c0800841c0c40000e42e0f4840d140402440481d41c110410700e0f001110b45064900b441d6803214041c103046042e88151701804454101c0414002d0f00c0c1403070411180d00a07480c1e107041c0d1034200200c24042d000020710b09280075401011440c0b451a83e0340030202c400940074100248500c24420328014001c1c403010614510a10410114140b010b0000c602c482c1215407607100c42100d80e136a50015240b0710b0380030b500d9603411603040054400c54039020000900035207101d00d0452070396040c2000504049640d0001a0038030040c84105401a82c0c15030440354007500004400c48161124041d580164805400041c10f0910100030403030302c00c1c0e00003810001404200c0071591a40c0328910101450201030300c4103000324960200082c050705080000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 717226330 1250 717225080 717225137
    0x604030b160302120a020403030915050304060b0102120a111608150408070818090606040f0b0d0e01022b06060f1b050615010801090c020a030c1a040b0a150303 70
    0x1d460710140a013018426001103c0402003282d0200c3e00b40207060b807042c1e16001030300d00841d280949070b0800c40003408501000b44020000c584400e0a21550391007400080e030040140740c011511074404840c0500400002c4506078003500c04d2115042500d160b9040311011074035110042c01020400f01140c4000c0c150040c401da5410700100045000540725600600c00250801c04640031051418204001c12401a242504c035460a200900c1060030300441030341150101501c2d142e40301c40f0045410090032030384100c40c030302d5407020400318142e0b010240308003c1590000c1400c10081c40030740c80c075011140c0502400d0001410b9a21144541e80241110011010be004081181c14150743c0d50900c5c203402120b0162186a2a0f00ca1191958200c3d0103035026203031864091000e0161441c00a60750200c844000d000c201c01d1404100601650b1300806d5910038640c102ca0703a40349440d08100711590360940702d15101505c1c3c40c940900c039054944541003666895034944c1d03003c0151140029178551103d05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 717227580 1250 717226330 717226337
    0xf06050a090b0301030c05030d03050f070c020102070503062806141509090405030a020f0f06070e130e1f0509210408030408061509040302060106080711030a0207080c0604030b16 78
    0x81030100451020f94002c5100b070096903009410002030604081d00300d03440d0010b041c00c0506100030b0110301c002d5154800e800d440e003031520130005c4c00102c0c5814403030f60110f6018042c0e0003d0000f21203a0300c04c00300c19413115201d07102440002504507822a415481000c03400814030517403400f2850300c4040c000f00355050b0000380d4200891500054070100003a20225400e030b00004160b00c65036014444038000034103600c0900300c40c0f0904034441d83c45039802080d000400c402d14841d00c20503910440d180e03000325114541044400c001410b04c40d0340e801c03100c4030242f5054a03c1d0003283c0264042c002c031817041038044040c215500c0c950000344440c2000703031541040b82e01d062001003042c400801c040c00080c0070a0005200a061203504105807000c0324280c80c2c020320a9108000c0440e40004605045848514180c001943d9850b001c580c0082c220005400318080091540034003580040d0f40070541e4484010340312042c20700001c018181c85584801007a0b110f203040021306e52105030301b56258814a1b0305 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 717228830 1250 717227580 717227597
    0x6020a0507060c0305010f090204030c090b0301150f1406071109270a0209100e01030314160803070f03020a020c0d0206040504090c090c03060e04020913021c1403040f06050a 76
    0x10b54510079907420070a002c2c0020707a614010071002c820301e07140c20020801000110719040c25a2a49034601196000d103100d200d4584d03000a2030340d00c0962140710980b607042d54080c66076413070300e080000404441c0b01d004031400390141451201c0ca4144d045a51060b801442d80300b000c5400c009002543e03200900b048841c10740c9415120b9240c0701a4402d042c49090000030300b0f00c20b20240304000c4944405010207464611030f071400d00424600c0d0b01441e06607501030401924004a85421075940d02c03400500c1141d903540252090104403481780994001c05e0683c4440d100a08024400c07001c9000b1030000600582c8403070020181d60600c15194031425002401035450980c07140c02160680b40400c0003103032000395250040208010f40e1180014000701483c0500801d86004c3d401c09443c84090000b91040d51400003251000e20419a00b9107501d60240c61040d514104140740e01c1c41c1c03019024181c0d40c8950706091a02d000d070001c405c880540d89000d6444413140c1c24080201c0c2c0c030390818a400c8050100c1709 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 717230080 1250 717228830 717228833
    0x12050703050102030903040618050306060105070c031a0601030b0f01081501020a0503040b04151707030b0409020429010806240c010f06061214150a0506030f040c0602030307050706020a0507 83
    0x3c0c0000d40c0f003142c11400556585d4500003000f06414101e030030b203c8000b204c0794010b00c03480d58082405508040246030890319010306040440c20300809900040c40c4541c08003c00d4102da1f998030005200b44001d8904009603800f00d4184400e401c3e101e090303240091020fa00007145801e8028040840c8a4184102c03000155650350b41442c1d640150811030f441400820104420101c6412060b000382c0d0300c2c03030700070002000280e80030144140a0880d1342455144c0d182c3c41407170740700c540c85140c501d50001d0041c01918140003500035040d46c1d03190034024068902140807042c0d40100e80b8180244005008482d140314500d8008101e41801c1d480104041d6080150041104090042e41d40c2c402540c00f000a0451401c500540f48ac0703400300405603150b003001c05091448000400050740440700c8802c2c00c61078211680050040340c120b4010592020011080c401094680300c2000d124030301c1114000440303503d614090340c0e03e01003110000d0000d002000b000001540750b40141c06860b240e41085400c00445 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 717231330 1250 717230080 717230083
    0x70e0d1403070c12110a1505091810030b0a09031e02070807080309210a1b0f032f060f070318090203040317150402070809060403080d0c17011205070305 67
    0x1070780030540c945019000b01d4107100c0700300750117509034034119041e16415160815058032410040408000e00c6400705c0c082d6001c0d01c4a1140380300c800c9014a0b102100d29012185035422030003404140c541d0f40d1030100107600c048540c45018942500b40e2610751407500c10610010400c0050107207501140200d20700040ca0290800c03541000d0041c1c0c502039611445c00c0000e0109004000d0311702c49014120300301c5990040400704050300e005800c00001e05c5580c080c150070b0810854035078050b0701403002000c00081031241002003840220701100043e800c076590a680900d040b100003401c02e500143c00c0094856080c4603070020000307944030b0b0034203445a108221540400d07105550101000c2a000010001015403001a403105503001c2c150403011170421811104270341800c1504039010b80d0740050118144410201940d11a9a00500385603a03544c80303141903020364003c0d00840d5081d50900c0c0c00c094415000303426407413120780b4442c08a5190380ca030200c40b4000c1c43c010007003501c45005d416804004a00c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 717232580 1250 717231330 717231353
    0x1315050d0203150a080f010e0d0e1017070e1903030f1d030105010e061f2010090305070201090807032d02030a0602091512070503270a0b070e0d140307 66
    0x103180042e200c42c64407404040c1c00d55512340446ea82e00c3d048040d40314100e60700420010300c0c0b04000d440c50300c55001900c105903141d9003003210b8880c0f003014640402500540c0031707203200307081d1600741c814501c10f2603556080c4101900c00e010080100300c42101c0058014811104141c003c0003c42101c403400d4070880119003101d100307030001007804080f8010440e09080c02003115103030203000c0c2013a030b21203501d5100041031131850250900000101024442c105202044034004082303c4200c00c1000a40615001d0400d61001001b03d002c51540d500016003200302090032002c85c0c0e00000000c80840f010b202d20303c03088801440b040c40c4104034440e20005030b00c0400484001c188111401a5144010320400050724500101084a1a03040110265518100503010b030848518207044d41c0720f449406a8180718100781c42d0703c400d0200c418141c0d0300e910780c00280c03000003103000e16208829a120340340201c80f500300701d8194a4111402c10040380011782c038a44101810b0b42c80b0b800781c0b270a0030390503520740300b0346031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 717233830 1250 717232580 717232589
    0xb0102240606092d18040b0105040f092a0807061b0201170a050a0e030a050d0b18090a0308062b0c120c0905060906031923031315050d0203150a 63
    0x8541d07080134445410310041520150400110913040e40c40c041d40c81000f2400140a0b050041d40c80340803820111803240c02210010707500619020382c4556036503c401c01400c00441000140525400000748080003080481c251034199803056105c064400c0311030617550303011714103d04000f1f15070b45c0c0d4500e40c004000e20314010700c070510011030541040480581a121030790b071100100d410070082c24400640007001c03942e4807800004046046001078000a06160f0214101c01451215400700064144082860503950b44240c0381d500e0b40303485500034070841c10503108078056411045d40070305110030704c03014452148601c21a001c403005502e42400d040011400e00c01140c103c464048103001042e11405200c2d401041522004200d240010010341c4d20140c1c400d184d2881c2500030003810038004078a0451203844024002e0180720240480307915500d51069000460610240304027260704081c0307111030040c2400b83d40da42400d00d0804421f1030003d50010f0010031618042590160342c503107039045c40e6001803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 717235080 1250 717233830 717233899
    0x2160608180111160203100203070804060501271d010f0b010e041103060907030605090f091606120c030e33060d030c050109060e010b010224060609 65
    0x90915030003901c00d9444401d0998001e0341030a88040c550042c0f40f081d5030012403400d08007801e040b05400070904104000310100c0c10b444c0000f040200c40b0b5089400720307004511840b003c02c102da0b40c0e0806800318280349220000308510398410b880904003070360810307107101a070107030b04141c480202c00c481c81c00c42e01070501c854205911500c14442e15a000301e03144001400998017031100c0700841c820b00640b0f10000700f1140c842c03640e02011900b030602c6a4000f03006460045c1607540d150820101401100c8011100c4251501c900ca96070200c145882d0081800c58400380c880034818102210154050020260400e0405070f40311101c40c4001000c00c108070074494029100c04901c1a0903140b00c0d81606944800540b1a40d00340501c88252200c1d03c001c07400c07903050b00d0504040007840c605540908540040980640c2c08c2c0740d002c44c80101c040d440020401c0d0242c00701c0385100000034038440701c42e1901e0310031000000a81c1c0001d8031428004002c046051004081c4052980b07000c0c0b00c1c90740d00300741c40d4080e0b010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 717236330 1250 717235080 717235097
    0x801111b0c100f0320220b0a090e15090a0e1f02070506010b0a020c0f06120405011505120a0f03050f03190b0f0916050c010c020109110d030c030e01021606 68
    0x213501485003510300210518941c080c800490700c0c100c0148507001c00d02c50a040440c5800ca40c01342d109001c64050107002c022140d440f202d8030305c018400c803482d000c0d070140d00b503a030070104514103807080000c110392201607c040b840b03585070004400223002c25000c540c0540600c003410030003801c04607024040700302c48100040c0c441c8494105240742010503040a090480208056140ea540005268803511811140300030301000c094041070103401840003003203524010b402448104078042d0031180030b44089040c0c1d00310403641c4204000041030600980c0440f0740060610002040003c1c00f40c42550740031303080051411096808002865104865002c1e11030882c01e680010035403980294027040b8130840b582d1041d0689080001c801c0c66000d415020424000003000600b18003403410307501e032410f4120082004a5000310041e000e01011803040b58000a0f03840303d02640c0c50403000c0115070640564a47c0d484040658041c4e03041c2e40b152184506510800400d12202112080740c44050038555890550 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 717237580 1250 717236330 717236357
    0x40b0d0320150406022206030b0f010f121104031b0602010e030a0816030609020c03120105060c0303010501050708120115020d0923040e0f03070308010801111b0c10 72
    0x64035510721209292503000300405055018110000316005a0800401aa191080d0807420000f901604182c010303414542c00000d402e64066112403842a4140c03030072842c091441004485440b440100c01c40400d100906c981c59000d4140d0082401007403036645c1c585060f03102c2d10f0710040d010b458040011121200d00c1c050100c1e0b942170217400394454001d4021401c10754100d6010b080003200a0054034022034a048070641c807880398100100400610300210758032074240901d06e403280c0c0310140348100074030b05100006580c00c110307040f05d45290348400918216400c04004480031b078030001040d2000c0200340000390b031582240710128002d00b140050a20216010b500c080e00707003d0310707511000c184030380d4031810010741207102018aa03103992003000c0c0500c0c010440c005001080000080100740c401c0c802e0440418100100600045000e40c44808441ea40c68140500380e03101008403a090020078811a00088030100700d80c1c0402030351070240c07203c2e50100008514124002900034000a0703007468840c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 717238830 1250 717237580 717237617
    0x70b04050708060106020d0e0f33070807030e281412070509071701140a17030a230c0106180209181f06091d01060c020d02040b0d03 58
    0x80c020701c100d42c0500780390b40c981a0080d4584000c05000020301c078104c03142c111a030b030b91041c54000c0070100428000302281d00d00007080e2142100b01c0750501c81e0620141489480c3c12200c1501d00f6145d0000807507141c44075580c0c04481d20b02d0b083e400140c1000070003880345203007690701e8000e07250460030309880424a89000714407403203080035026a50052818802e424850580402c0810594000b5030b164001034940ea003040303600d2051029004060388008001148100d15501c0006000208444d5901020348032078084206958003048031805a00410040f60300c0c0b8002c00c0300e11103060b19401d0f1740300c20045035070151142d40c0c0200c5a80c0500e95407802e003400301e00e002040c55289100c2d0200d08500b4200100c010070a50030600c000c2880d180450030000740e1440c0761401011014089001031040240c2d1501d026000e10000d0103010f1911a035100081c90410b031904003681291119510000e600050b50284180c0d5a40008180d0300309460b9068010540c94100761201454801d0707440c4040440154400d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 717240080 1250 717238830 717238843
    0xa021005011d061f0207030507171f090206180a0e270c100c0b1f0e06030c0405010b0d061202031f0b0405010311041506210603050102070b0405 63
    0x124a5586008014801c280c14000852400c4203041d00ca124a9141c1034002800c580300c11200c0580c01260005094150342c1c0032886104580c031620032109115213030560443c800c051086030030881d9011400070840c0c483d07150302c7c0d00820887e80000241405560b00451555072059201c42c042c080b103035040d110541440c0e01214028942e2002204440c244018040112450464044001d804500804042e00b1090000441102008082d0340404130361680240c00b540440f40d003500d02048040c001940d4201d40008450304d04541d00519444c00d05150f0300c17804186d009464150503102d640107416098a50342705540c00ba00841804949441003d140341d4240c500c41c2e00f00c0e041c0c1d0701c040c081c3c510060b1400242e510f81084a2418800c0c28420095120b008154000c04140d1140c203120002090001c51780e005240a801620284580020080302c075000008031b1080e0030009075180111b00300240c1c04641001307100311960010410341d980c4c0c0c0382c0c0b80c01ea80041806030b85880d1440144000c004040003035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 717241330 1250 717240080 717240103
    0xd1b09050f0f04051e10020313020a170604021512040303050a06090209030c1012021204020909010203040308070e0301140f061011030a03090606090e06070207060207030b0115090b07080a02 83
    0x51042c0b860140d80e043e0302c0d980440503180300d0071124042d00c04110000e02100e801030b800d5140c02c5403645090901c44841c2c0841c2e4005034054071012101203500700703803460f07044106048640200041e80b156424010801e80d10400020300304000c2c445500000040d82c0d103a07000328000e68000c01d1300d050021513102250195400050031610401c002505601c0100f540b12070711408451100e6201d0866106440c03005500201c2070f802840003800d100200e10341039107640100d000b83c0d91134175074ce92501c000500f00d10060310301030003041030b0100281c03040b80321b401e61400088001c0c00105000900b07028624074100c080c1d503c40000840402041550b08150115110040b11403400328503c030740d00c0c12030305c2c4c4138480d40c046c0b4001c0544401f241c1050142d150008030050002d05000c00c001004141520740f5207006840d00001800303107840009100c1c2c0300013000c42c15242c1003d4a80c240c0d03440c00180c08100f555044000f000c3c000c42c80000035400b40000007914400340109a40341d901c1c40620002410208000310307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 717242580 1250 717241330 717241351
    0x3030a091e0b0a0b030a0503120115090e0622090b011a1314030a08030c130b09030706051606050708040c060f1b02030703060204140f060313020d1b09050f 68
    0x7194400b1900c69100541c0008088200040d29100100880e00f00405014050094800040e04030010031038031003040d049601b82000d0144002403610308484031804c9125801c03540c058500499a01c1c03403c00d000c60b880603e814070040110104030505019075040000c1912140c0f41c0d00010010100400c1e15800c00541c007101e1745251513885039990504c0010b901606076110180e0b50b43c5000c40e10100074894040750800c414503103924021034219400d40c4a09213000c20401008000141800c3c0c42040c0c4098101c001c0190050b1420310104542a42002e0725014400719204209400324045119040c00790320150384084280c50142440008100250301c62010404000b03a0690b20640c804103103155000e042106103c44d804500000c0d10b0114503410203458240700050005030b1031140c070032040c0002c4041d01d420b400050810f04000702030000b00d40801039000450400c6005242c040d8589015500c501c2c110661001031022082e595091908046000760303880f014015108141030000b50702844004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 717243830 1250 717242580 717242633
    0x12150e0303070f0203071a1f0f21140703031119031419090f0504090b0402060f0f0304081b16050112061206020d0506030d0905090c0c03030a09 63
    0x6040564a10009201000b04a0381120380c1c041503200f44100c0302080d820240d000580c41000c1414100346905460078030b00e1140703038060410701032a0000c112084600c10950324002c1490400104046100c43c2c85c1078811140c0b2140b04400101591150040541d801001b00038403815403501401600c940c80055400d0b5200d40c00e055180020440010300c2c4581c145010354001d440c5c4d410002c0c0a001350130316083c08884400e00e030500303140c1c01490081225420601c40d1140340e590341c01c0c4411900c495101800c8080c1700d000040141c14050300074480f2246040c020380c13501860440003101da40082d5411125004002082d40303840c900036030380268284081c0040c000308162040b60168040e418411030f81446901ca40081400880d0742c0080c2c003e1a18400f2041440514075244009500040909210519040c081a2141130015250760012015116491245d040c8400c000844200400110074101c0404c4111000c1c6c1c02800a5409580c407001c011030168083d01d003291200cac02c4195480322002001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 717245080 1250 717243830 717243851
    0x60301030c050d15020304141002070302030f0304030e060c0c04050109112a0a26120118090c180501050114160204060509130c05011409130f061215 65
    0x701010740480d0303401c0381c0c8400010f240786003082c001c480b5898851200ca201008100c240200814206095451241138403041e00c15000d0f03020803400707070003400350050380f050283d00d00b0800c25100658200e4001d00340003800d41104030002e11164808400c0c2c45060300714040080301d070b04050081c6400b50400030300500410003510b80c802e055009290f0a42e804030040c09004540d0800402c40c2c46035544680165501c1072200d0806088041820060300e19203802c0d600c40300c942a10300002e82d80c0b04800c0740d842d901e5691900805201d0103421500082049544402c10740002e819094460b00600a480c641580a1002d13100c00b011104d0580c45541802103031a04c4004d5280f042007100c0112100c46044649540c050001c00c001302038030b41025801241100a0208a22a40083d04400c0b84603000086901d038445004450200c01900c1042c0c084e00c00380090800380c903040a1000c4401c91941c00002c0d0030100f9401e0344181c0300f40394029000500c031140400203101030400030740b1328511034440034804c01555 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 717246330 1250 717245080 717245093
    0x2030d29010516020a0f03150b0f0118090f050405010c08010f0512070e1305061e06132903010c1b1e0b070504140f0321071403090a0506030103 63
    0xc601100d4104200002d43c0c403001090801d511901030f40142c01010000d40f0340ca004080d0210a000039105052a4403420030307131000b80d0103111141c1c1d80242280412203043e0703005480003002012240141c92404201261800580c480d0343d0400301d070b2400c0031a0350b0a01d414000e00b1144c01c40546010001440c00500c030b003080201c40f00382200c405403000003001d4488440325003000c0e4250441d0402c0f5002c041803050442c00030b651460424000d0b02560381c207403591100381c905100c004403204800d044960010700b051503e105000071503001c0580200d00e800700c0c5491034801c2c800300100ca41c00c4415031048055030341030900c901c101030b4800b4207000183c0c465454a076034070300c0242c2c84002e1840e0f0800c102c5448911041210003000da50081e5060010b0510070400381480d0418040c02c1c028030758454060a0600d0807500c072029200c0060013070030070700c0c00d0300307031801d118002d0198841c0c2c1c0b40b903080020760f0002d0f6030030b824103801c0726210340616100c003105810012007400039031003175129190510061000c50003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 717247580 1250 717246330 717246401
    0x3090d171512030708211e01031704030506100e10260a17122211010e030706020601082b1101060306021204060f0e030d05042102030d 59
    0x1e003101d01c03612680442280d00c0c0b0394032841c4001040c44a01040d202c6a2200120121080c000444418841c41d40e40040f0034504039036403990071140340c95002c010408110050414441c1400e400030741303864182c480d203230103181c21000c2da48d507821840801000c001c00440503c1481d08a402e070074049804900c0c105500c42c0c03068240342e242c64504811214141060010030042c030300254810184100c8030078510784610306420014038165407160f0783d000070380e40c1081ca0000c2142ca0b034503151698008010307501c1c2d00510003146440c1c54140100700680d41416901005103500821041e4000e100560410450305e003460200e00c410002c224019218007050101d504095481000310310b00710f078038180180000707805041301e5130025100920006400307948640c06d204040c0b207a40199018048140016112400c54062001c0c00185030070034010b480e0380001030381089420601841010b482098086019000706202034244401350303000041070b080e16001400317a40d0300c0d070701032405d00c450202c0400d110144951 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 717248830 1250 717247580 717247621
    0xf06030b0f16270905070206160306060504030605060301090b010801020a090f060504381209060601050f07061b0c1e0201140c0f0d0f0912020f010f021203090d17 71
    0x6555407a07940c0d00f09900c103000c0d002495404414843c600b410f140294580400f030390004044c1044125442a01e4000e0090340c00f100c501e0703540c042c0781600d55129040240030240c09aa0306540310b0a120011450f807425880c06080000300050380c0320307540b003000381003d00701e640101c04a42d50364808001c3e041d0403e003910222000403120a42420000410b000d00294401001c1041c1c0b240b402d80c1282e056004024001c01191244850740c80d4a0722440c9580d140801c4030300ea07001074010010b00300c0003075140e0040c001003481043c004c203000c80c2c91604409011200060172000038028000d003818000314410131004060885040b070594011070b00020006135054a02c507201000c00242a11500c8082015111002c07024095030400205403100400e0040305a03d0580011019540420340e8500c41030041c00c520b60080c4120400c82881005440c0390f8003619251040d070080301d4020004461040040d8400c0c0c43c110050b101d82d1003025000341a20741503600e4174441080e15010800031088070080b401400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 717250080 1250 717248830 717248867
    0xb0c18150403030503040510090b040c0e16050d0905033f06040510050d032102040f030b0907031a010305150601021b271504021207120f06030b0f16 65
    0x81c0c0c6c450038113074a0040071585d520710052511100005006000e940c160007980300c2c1c50f03800d441603901c5141d00b0700c800083d00c60b11912402c45803058001c50103030004001d855010040841d10311529156142542c225007420f4005901c41106d540e0745503650002e944501c1d108240c115a49000c1c04100d50042000906541c0110f41d40e00c081120344240040d44002000000c1024890100c103160042040c64240b101180350b1200794503050046c5100e0081d60b00b90342d00f100c44044c4a61031525061401c110140402189000d001300100c046401d00e820010180401104150a549145050351508200c032003128038013100e50081c0030b034507030f800705e01c1d0101a075000c0780c440700c0145584001081c0074844441508902074440d00e581178000441c020611858910007030b42c01e400c00c600140810f03031050b04081011208580e000441e401d001c2c005505580c1400d940010703101807000100011030316260826070f00d041d04a003c00038a11071a94006503c03118246210081c1600c0490181c1804c0ca00000084036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 717251330 1250 717250080 717250087
    0x70f0f02061b0c130c050915221e0e0f04060e0303150f03163c090b0f09070c02041b230c120c01090b0c181504030305 52
    0x1503548850654101104100075a802c08802c4102e40360b681c180405a00d005164410307a07010140a5442804160051a103d4a1400f104e08040040c40f07442c41c0c0701419510001d1115404980080380c645421030026003140c0c48a600f000441c02d1003000c1100707010303100c0001250912110f000c000310075800c240e41c0c9010303101c0d61302d9500d0860060110311010800d58400030080059070360107818250221301c0c007075903840071a0038a00140358442d44209644240214a110100f001680041c408030300410ba0082c00b003803a05d41d261084414210310a114603124074065020b04c43c400d03040c400d0400c017810803108180b0b0840b001c8007041d00c00500401ca14148840402c50b80700390b4a0b80d070080c8620031601c2d129546041008100642402c210000c0c0c40c00e152848a00401242850011181d809442400401403402d85551280e103603800403d00a01954846d000b0b1310029960910440c001c04a9016494a40c3c12015801c2141c800c1840c10b14460065030001c003040011f034070101c03826a500b52908036034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 717252580 1250 717251330 717251333
    0x100e1b03030c0a110a0501030e0d0f1110090b0a021305040507120905210703090e060a1715060118030213090506010f090c031a090405010e0d0903060b06070f0f 70
    0x15030161155440740d03400744007000340401a4480c100402c004d070403034020340d510b0b8507400110115020725081110a0b0303c00c20032045000c1c050784284100070240e241c15003d000719458034500b4140010540781185486006480400085e46a82c03030f4080c400030402c50070520503810070482103215114150282c0d60701c6000c030304400c0c0300d0707084140134004e00355045c0804051440c21550324808500600305680ba61040d01114845400c00c9a4000d505a034440b2000c60500009401a5a0150a181d4029413200703000071035005010807007808403095400b0f0080e1140203501c12010150080c207440c1041140038410110840c3c400c070560a0307035010f0baa8041c0c08072035880d0100c01003001d0140a4002c0c810880009102c801b5424242d040d507008a01c140812428102c054040d1121200410141c1c0380a0000140b541821421300da446400741c0000702d410285862914203082000d011400090980e0030144140400c50280e036149a030305132051417a0041a440b29150044c1501000300803c03c0058000c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 717253830 1250 717252580 717252583
    0x31d120604060906062105010b15040306020c0c0d0305190f0f030506190b04140f0d030507051e0d0207080a050d0c03090801231b040501120f05130203100e1b03 70
    0xc0142c08601d80302c001d0b17107040d24080e030248100da1b8070480c2c0079800d0004001c800d050610307404003100360f1544e00604190442d03403100080e4010724a10540ca03c00c0307403108500c5036902444402a06c0c000e03211079990364010b21954000d0007100c000e0100380701c40350200030400c690014004c0724040e25840c00254544904000501c15500f445000c2a4800303d941c0c0820312482110044c8100c41d10711204807100b007200c00c10b00400e13080c00050503505c4617800000310b0210380101c0060503010702c1003040c2d4a200001b107640328a480c03000c06a509096000c000d41201140e010030052000d0300765800100716401c100c0e03407140e540340744840300e04c020402c03c8414a820140540103413405059400000c0c032580a8075100342d100803c0380201c41e1103609603503001c2005111580180d41c0c0c48840b440c600b910f0181003400546555900780e500414070b9030780e01c0b540205825103110369030040707844180c01100c248041c01010315041c0702040c5061624a0245c01d0000c01c1c000003600d41c900540c880740d0103050342401000030b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 717255080 1250 717253830 717253841
    0xf1401080d0806030c0d2108071b0809091f0906050a081603110303040b030702101a010903030318020d050102030103030201051014090a02070b0901090302010e0309060304060b041107031d120604060906 88
    0x11407d001c104103085101c0d40c1043d681445101d140d034503019940041c0172a0000700e09d030050040c007180c8007000038410350b040108102d5808044a1610b036a82880001102950216940b201010545e42c2409216034a40bd0401c03c000f40107500040c842010310000146a00d0020312000340020101125400c94ac1c8052044d03070028000004060380341d10f1b103410040d4444031410040b114032403802014410302d9801400c040205041a0341c1c103072001741540d030280c004192025011142c01e0109800e1380050350b603040700c0c07600144034100160f100d5155280103400d5500107000301601c450a40005d2191203200103481c800d5840c22200340200e40ca5040c1c60100900c01c890014140343c0b0008104141d15105411a40340d8a03c6070b402000180c1424410300c2c0c80307000b41150207a1040c0100b0108012170301c80d070000605134400070b100280c1000c650600403c994050b0344101d010500e0070b070408561a144c804100c11080301620070b8508034030411100c50311b1b440f00900080c4090755a03d80c141c248540359000707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 717256330 1250 717255080 717255113
    0x10b0313021201050619030b0403030c030e0f0c130e0615040b04050916050a0f05040b13090b0106080f06060f130f180515220f1401080d0806030c0d 65
    0x5008108070b2442c0784501800048900d94000c100800c8003030022001411072000b201d406c01c541c0e5040340c4541d58200d0103021070070f00780020162070f003a41040e280824003201c6881c00c90309005141140c0c07280140304411020a100d41c48403841c000c044055442c0c0810307050f038498904448025200c12040c00075004080d4042c07007035081480e00d8204580c6850000d02184054407283e1800d40050b07948007004a10311b00e9001d0360840300e540000230809800d058000144080b00207045460680305c0d010301e0b000711010003000341c0d80241c1000c01009150713001445a5007003200e04909004038034141010808900c1030115284010a00282180c010350702004010064442182c48600842d50b40f121100c460200f0508200c0b1b25282034040340d89040e20322000080c0c0c640c090640c0a112246841d10014403405c030851007483d54407441c401b88038191138440d801c6c2054031558500f403607504140c11315141c101000300020a00800205000b06540c2c0016003896000085600304040c100c94500204d1810200d0030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 717257580 1250 717256330 717256339
    0x31b01091514091f0c0c05010504060c0f020d090b18090709051c2001050f04060504180513060213091e0e0a0b01090507050412150c02070e010b031302 66
    0xc400760400e0140c0082003410350b40c804070070141e15121490b5448940c2c80a0030341c89118007607619588030710b150300502040810b604100000204944030700e800d4803400c440c04c440d80c590707461b494110345812480300d0b0081081c92004144131114058043c000344482e001d00c4203401400700c0d10402c881940060000032880c080c101440d10b0402e4040544040b22130b008140c803480c6416446c505180400320340d07058817500000c80d00902c08001e1880340d1162055486c0d5810400c1c104259a060448940140001c00c0d0a5480c1c176911441c0c00000340d07036041145104583c00d4140800e01441401040c80080050b4002c84010380d41c0c250705002d00d0300024141e00220a280c01c141c19041c586440141c1d08010a00381c000c24890100e61030303102d40d11101c8030900101945a100010f202c242a1139009039070160f0281821807810707440c1d4802078102c181840080791508408211400d4284a0740a0802410054001048403034200840c06060300320500814541d08030110002e0141042503d9101d503641c0c0181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 717258830 1250 717257580 717257603
    0x7081e0f060d05030c070305070618090c0e0d0b0105090c04080d0f0201241a250c3c060c02011d0405040c0306060b041a0714070b070302070b040602031b0109 69
    0x317110f5070f250811480b054621f0f00511900181d4603003d504030794a5014039130700340c0d0001c50400e98200000c140c034014081c01c202d030071540c00d4401e03100c4950304950580240101d03401c542c580000c1100d034480c0100380e0300401c181800200040c54000880700c11030003182c00c2081c42d500c11801e0803801018007541c02d06800010081b0b14000320301d07038132228003035881d00100c060403c00a0200b00701c861182050a01d42402c007003465808217840c0c0c004895025115055802c4055070f5104242d0085040310000d50204160783c080c480300c0d0100042c00040c0300e118140800f04035240010241c101031040c1c0002c5d05000c44c14101105c00d4003851403440d28a603004004000908007820090b403500007a00040351110308d8540080350301404001510221201090080786500c40e02d10a0304058100b81002c84070760750422841c04400505020070406041406c0b503468072049079040013441c0640b643e1194050100401043c008954007000329900d041000c0160b071414035500907071078010010782e04050020103080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 717260080 1250 717258830 717258847
    0xe1f15060e28061808070e19020414010e0a050307290a020307120806030606283b0703020714010c170a330509090607081e0f060d0503 59
    0x1500c1600954505648419a00444c03402c1414110760368041c480c5140d21100e41004483d8000d15043e030301442c032540c0c4100903e1002442d03410b84e001740d04120007041200541c49519603100c003008011207400c8032808041480c01c00440d4941c4090702070140e10302c5071003400d00b070546c40c440c01207114014000b802e40e60b1070703401d510020345030f400c99002100c0d00515039180b0060140700b4440a801460020b000e8039954540100300700444500c100c40c0c42c1000701c00c50948a0004000380888020310320b95010b04044e0980a0001045a02142c100c1002c8400f1108080300e5095a580c241c0e4010020708005950300c40608115030401000d6242c0d0000d5070924940c040155400ba4000c0c00d0031038580b21004a50b07c070191070a0036145141e803451402c2c0c0000078800361643c0362501c45080c00c1e41030300e50340f01080c4d10f03480415088481158400a41d0340024180012150301061a03540318421036542c12140035040348c04040f500025008213018011080418502d9803000a000e22003030748003080380e42e100c420 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 717261330 1250 717260080 717260149
    0x10090e150a23010b040b1308030d05061f091205070f030812220201030906060b040605090a0807030201120207050c270a0c0504270e1f15060e 62
    0x41c004581c64032195040d02d00030b68464010240e042e14001ca6980c0d040038200011815a03400c00744900041500304640040c0a440600041118000c7c0c4c2c0b80c003007200d00c0c0c80824400a00b8810181d4140e2042c00820f180100394001190300c181ea0341040d0191100280e410310398a841c00300e0300040d400c074040400000810040741c00074182d9000501210710b5513030300d141e03c003c0f034049440030445078a001e03550032400540c0301781c2c8500b42c00c1e0700c00c0400080b05905c90f40c10204607040780d0000b4000c1840011030b45c0240c85c003544541c008020705001000014296030008291b03910000704508100e801190180070404280320b0b02d0011030780580b600c54a030300385002d03040c00116030300d501d900c0b51090040803417503228450040000c0154291101c0f442c1078500400d070109107a10100c07140071010301d114030b00e00010590007a608041c01d91001010244d1101c0e0085080b4503020580000303240c070b01609000c0551429000804603912420300d01c0000c80241c000c00c80107100b01c0082001c0c4030004542070040c502 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 717262580 1250 717261330 717261341
    0x608130501020c0d030c0207120803040201031d01020705010e0601030804061103070230060f070c03020705031222030b061c050609060a0b01080402030a061e090b07120510090e150a 79
    0xf0140d0701441b800d0b108420980c0c540c01c141c015922020740c51030b001e5021030034020045401a10624000810b206182e9040100207003600d14260340c0e9400140d08000e021090044031456400b40002d0600d55240d59510030444c03003280b00d05000d00100030910340e5444c0e024000e407040b00da005003074040c440010310344480d908007281038140c10400d280f0741d140503040b100044092046d401e0007207124443c2c0303d016003580c1400c0c4e240340890442c850030001044584041c00082021504451016114051480f040076140c1c00030442e5034000c0c50640007000410030608410350004d6050310304845414841c50048002c80310a00e02421034490001848050700002602038428010f48504000203804800116410001981d010394035900c07103c8103101050060f0b100c1c40f101c2e4410108011958021070340c1d8000d840b0000c800340da000d4500300422880380e80280c900c00e00584200d00400c25803802c468041c80c050010700900304d0300d644e0b27070542601e0070390208601000c01001c2e02c81c2941e6444c0c40d0311803030003400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 717263830 1250 717262580 717262603
    0x4080a0308010e070e010e1908070501030e0d020606061312030c02040c05040b07060f1d01240302011709070f090e011107050d0e18090102030a0e160608130501020c 72
    0x154018000503400c000c612555002d1041381d511180104080d1004440ca5107034181120743c01441c9603040341600790301e1401a0300500218010b030210368500000982203509030041e04066800001006000aa003c100a54070034001c0311b50300e07203840f45041c0c1501502415000304507802580007692091540044540010307604c22901400b040c094460103e401d40118460000450f074144130100c0014074030b802030000341041070705c0003a5880e610655503049881440e10412141d42d68442035042407650000c4d5402140c07441c1503840483e1456000030488540e00c1c0104041c0c01d104e0001c00c41105c418030121008240000680e01c0560310345544030005e000300c41215515620340303603204c01000d1011003900d1010303402001401c05a001c403201a00ca804045540d568041050840903c682c000c079105a03002d105840001601d0f86031001c0c00300700300d4032408900707002036001c0503075021450710b5007801c8800d440d40f0746001f12517a00c0e00a124941340003002d10041180d4000716104826030000160091010f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 717265080 1250 717263830 717263837
    0x17160504030b1f0b0405060922110c060f070f050307030b060406020c010221031306090501020d050412210e010f0c02010509060c1303060506011107140a1a03010e060d060204080a03 79
    0x25a10344449401740f00380d20809400c071000340047c007154580030666540c2c81c444400c101d04003c030003e08400031101c160030440303202c1e03401242c000303c1c0200c100300c16588108598040300140c1400c19002d011000080420303420840c0000c0080c080758840c1d0482d013081e0070060080b540321138641c00d005c2e40b162002907610b40148100021102c10180900198800000006c0303200d1540d2120982484c001300d40c0e41c1d040d140c0d13940b140d114000241c02403004200d14040f421001403581842d1901c558032111a801c02010080032100d841d1400f07c43c280390b01e002042c0500c0004050043c040a28094101e0300d281d403c502d490500250400b54064108912940c0300c042a5036450b910030340f441000d07003c1c21002d045841e105600038400207010384c0c81117812800504106c07400704000b95142c4c0c54010386070001001051440110103c03410710741516400f41261081030205e14101c41c45280f1030b400140300d50211085e911f8040350303e43e121070300811492908020199505d6441c0e040c03159940c50480801c4000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 717266187 1107 717265080 717265141
    0x91e010c0b0f041202010b01021b15030405030a0e1219060f02070f12050705060f0c07150b19030b130606090609060e0717160504030b 59
    0x1240110b0940907645180c589400714044107240f07002e00030f681c1008400c4d40c842e80c0102d003030515403d946d004102404151340000d010101480800300d010301c400014401448408801041e00382d44030380380c6000c10510f0805111443c4580030000340c11340c104081803486500300c8003100104900800000c01c0c0251640f0084040b81e010740c0041703d000003070041c444200300010006800301e8240c0e00307080c0c2c184401c9444031516003030024044900c040c0d40c07a00083d51218080140c6c1d01d0703560002072079002c00c4640318004005080390100c1503c510030141245440c54406603494090341e501420f010b00325114170041c0040007812850460b420b0f521668007086a000071303c00d0720001c0c40c54803004590680f505014501c0c0040c003500e0790040050340100c40304520002c503403054100b404000ca2600302542442c007120207006a1704000c200c00d00040902196480c0001c0c0000d00d603221b0581e413a0b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 717086330 717266187 := by
  have h0 := BRFrame.cov_init 717086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 717086330 ≤ n) (h2 : n < 717266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
