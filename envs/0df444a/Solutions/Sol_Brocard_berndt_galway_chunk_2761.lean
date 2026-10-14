-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2761
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:40:00.019953+00:00
-- url     : https://prove2.me/submissions/7652df92-7629-4440-93ea-f6f8696178bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 496402877 ≤ n < 496582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 496404127 1250 496402877 496402897
    0x111120307031401080601030209180d080c040f24020c150d0902040f15060e06090d020f030a0b01080c010c08070206030403091a0901020105090105090601120f0210031b02010902100e01050d02 84
    0xc6d55045004014406000420b8100380c19a40225210500004151076103001c0080c10b24407010340f140005d02a0398003d541001e40d049020200008296440d04254041d2200c40346c411a551100014120303120b403070b080c0b490f603040104400780d01e5030249804001e00c02c448a2040000d41d6803650f83c0050195903104041c8095140c03950303190024030401c90030b880000d1040b42007059290b144e40700460868054205074600c900c04400d010340a42d1070b4407501d54138110000b01611040083c9182c00c03070100b482800f400b4060300c05d01c0612280c6500030700380aa4404c1d0080600b40c20aa65a420807105500050084080000f040000a4070381c40c8154440b0040030040703045a11000444002070848000170201d00041e8186014444901c40200700c0c1815110302c5040001069081c3c1085003100071032590080d0014820740b04046815459032005810b42e00c118018803c08104440407400c0c1c0f1010007000c0c0d0f000140610710504640940545881c2030818180360b4180300100d0038160403604041c03404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 496405377 1250 496404127 496404133
    0x11a070602070b0709081006050a0612021c02031f030804050d06140c0d0f0603080304020402071a0c03220201170603011104030609020a05060705071827050c011112030703140108 78
    0xa20102505115511900022507c10001c9520700000158100c51900c0b0701000d1100741c0307002d0307080500160100c958003a804824420340d1014084a98001c1d40308548070310380b51048206440003400380a050304201c907001101542040d0400c401c1044101e90110100c1c0c40700c0c3e84010201c00031609a00c62440344660340001501c3c1c2c10326440c0d20003030340c0d0f40d890750b1000c1d42d14024040c80025101c00030740741c01540642c5d0058460495290011480e103110507448121b101260400407200035240045224044460003400d0000e5442100800038014540003400b00e090341461540418001c2c29045e40040000c00208131400d45002c03c2071154000c1c1c1054504907102c2120034158100f401c0c2c8407004000071744049142c0700703664a81c0ba4540c0d40601032040090001542c0c400c0c5542a6008000c0c46031819001c0f0400c02a004440e010741010240101c0e220f0003400000c082c290f02680006000c80f000c280508903c3d242098407080a5100803d110f050543d18511040040403103404240680004002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 496406627 1250 496405377 496405379
    0x3160302131508190c1e031401030c140d030c0f11101106010609080a0f1703010b0c01050a020f12060a091b09120c0902090f030f01020a17011a070602070b0709 70
    0x6000d85481840610103401810845e003541220792001e250709052101794480c51200d004068118040e108281c11441440d08410012042c00901101c2008499000c251109500e0025060140c5503200760005804aa00380d022400414000c900003503901e4032540c1132101403640314000505684a2100410000b060307428610402ca070f080084d14090240713410424002890050007940e40e02d4106002050f80041d10751060410545103040d4010718001ca01c0d040d12903860700640c0300c045d044400040440d40c00c22011986005841c400c0301c050032084030785503107448010480c4042418028141b1500aa401c03180015417401506c5240ca800309020100c0356a402c4240c0700811918035074104002c1c0588004d2002c0000b149803007850202d40c2400b43c09600c41d101500050010f01c1d525044540500404a050b44d4080041d4000d05510009480c0e050808a01003c0389010300c0003409640265020040a1404070068034054211a84a042d02602d0a219651084224142030307451070045801d10340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 496407877 1250 496406627 496406641
    0x31e010e0601030804230603040f030e15160507090509150f012303030d06080303310b0c0f2206172d010b070b0c03160302131508 57
    0x200c81003081154020185941551100c603441d03c103078403c0c0100d80b001040804844900840421071014005004549a1400f4140401546000801200040c4c88069102c0107840d040040103541403a041c859420410039107000410541e1102d02070f00d03184503a031800105503070744d40119407240701400003404111701249000c03a002100601107d541703910070300c0140003a81c540e2034440301ca0105689050341d69180701010038114814080702520301403c26201180840300040254001c0d0140406411510207110646540030403072203180004480e2044100081034002c0d006a4120880c4514245407000020403004554002e0122241a1400c0c480746250b00c1040c0c11008000c003018106105c41d03900c0e04030136100c568001002c2511401540346c054020141201ca03260a09080704565000b03940c40381e04000e0250880c82c004c46101c0000780006940d62521000da9020b00c51794040840d45110a42d8213070040d4110780e2042c480d2500c907002c009498184810300c0500c0f94140d85911919083c101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 496409127 1250 496407877 496407881
    0xd2003070c0b180d0321110a11120903100c140c070302090106080c030609100512030301141207030b130f0b1e1b0c0a05010212070f0309031d0f031e01 66
    0x10f58450310445508060b540030942000018040f80c0c4646014000c80f1900e4500700020003030780e06d0000c01c01e00d010450340d0b445034000155080544044040712032003400810010300303920904420581603004a0404075074191142c0101603004964100805641c5086104c1411500081000c00306075100314001c0095040840d20140582198070b0640601d00d404204c860041c840903203158055014440054100c2e0701e820400006060001e16007c2d40044031b007031f290b40d00d41080c00703420581940d42c0900c074810b01e4049411002c80207800c0240c0345452864896030f5011070b00415205101c000140c50000141344202c680b10b140d441600c50410604012410351000003500b41640e081074100002e0141c281480c03401d405035102c0e01401e2542d501c02410460b400d011140703030020030640c00844d05c0741c4500c40805c0194840c04540e80d92402181c42c59400704d06880c4c07000710107804590070110301384c102d0b032402d1070f80514110054030b40c0000d80c080202103440d00003108100e02c0d5645010508922400083c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 496410377 1250 496409127 496409167
    0xb0f010302071a042102034f05040e061e0a0204030501060b0a0f030605030309040903020102120403031d0303070e060702041b080601110102040f1e090c0207030308090d2003070c0b 79
    0xa100560812818030300e1903581d0241d000d1140c4160303104048d00141c803030810701030f0108240010b958407000320300e0009034010800306000341032145085c1030420002801c0000d04034403500000c00e451801c60001c181c0c5a1a6810142c0000c4005800f0840400451005d004200042c20350710281586c810382c0460080150702c3e00705188003007504190f020005580c0010544d41c116004642c00581c128151400380d0092103900da0281100012400300000e00d6016884140b010f00d0500803282185204e03100282c491004442c02030208212001031581801d100c405001c5091002c0c000081091440e502040320305001c215040001c0c8600303080107480d5a0245081c800054103000079402c040c10282141c01c504039500400f0070240071885010200c64421500380f000f444074400c1040b641c1c00b11a0029150b104034001903020071039131070200f11250400200381c10ba800340c030750f078003960b24003a0101050b0f1118a44d1030310020348400e001c0c90012030014000140104043c03401d10f81d0352440032a000d00c0c00448 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 496411627 1250 496410377 496410443
    0xd08070933300902040516020106120b0a110d0504140c10270b0c060703050c0306011b02010908011d120a090e0405030d0e06090705040b0f010302071a04 67
    0x100c0b8441200c0c0a10703000e40007140d1080001400e40c208084040d4100034086158040d40c858200360901c04510303034402d6074001169455000b444140c2e02d0b40b0000d0808002c0b880000c1100901c503001a211042a0744581e8840007000d503da4a000d04550000c41035500c15101030b24010f40d80321350031501400c1000496440c1400f5501d14402981d094000b400303075001084175a05034006445500c1d409a010402c000140c48180201c0c2d4842c00400b03901640c0d01011542600464a0200030880c045440403d4034868801651083c0010f10200030b030850a00c50190f00300d050020b1000c000c52482c00a0140c030084505441500c10601100c100c0340d860300e20780c8214030403100e408100c001407880d0b02c408010305460002d041e4580c01d44039403030f00c1881c5100b250f940c849032525045601b83d00d132101098840c00791501c0401c690036143c650b403c0204030b800da02003036a8841b40e01d0080c2c1c5015402600540000750068070307014414004000700c0500c0c03d004550440e40c0e0703600c03100c03150311507010390440030000c0704 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 496412877 1250 496411627 496411637
    0x207030c020d1b0e16080606070203010c0f020d080402100c05100203090c0f040e0303010512030c03160221100f06031e12090503060414030d060905091b030d08070933 73
    0xd25940d104030860780380410a0401c0541b00018146032100c03401c491700c0e20380c0600200600600c00c80000e0080500d000c01c500140181152080d402e44150303900c5019940050462500c2c10b40c0300800c1e110503803c01c0c41100e10f40151300318400580001e1000d1449508980060712840e090201007020080d40c1001030341c4142d282540300c40c07030b05100009890544200b0355140b03c80050202a6030b2541c000c1d1001818540300002d0001c512240a2108001f0f03240300387c0e0135003c3c02e03001604c03003503450001c00354a005950003030f80b5601000c842500424504d4150307400c001451500d07038a44c000c880c6050f40c402004104120890410003810414072000d100b25481e021441d9070410001039220705010f000602040030080c03080b02044400c1c82100d1710640404c50401c03100740da0b071a83e2f5010388001c40f252407550181100028990841c0d41240c4007280004003d0301807108030680654141002500410070080216008603c13200b0454100680900c6011018200e1403000054000202621803441c2089 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 496414127 1250 496412877 496412881
    0x3070b06010c020a0305030d0c1d150307110714030f03030403170c0f0a091a090a090504481d0c0d02040b070605060a180207030c020d1b0e 61
    0x154010545542200d02442e151610709002d000142e000c002941001d482408005404c0302c04850507444501c090185850707108400d40741707081c1100c0d10486100307000c0c2c005d182c40088015049141d00103560001d9503081c80d48041c80f0f82c030035884c81e02c0002d0b00b2a190b0710803e8181d0092510b4100044c0e135100c0c070044000c5280d4501035030028440490403848814810020000c90001e01040c406c0e40d03000505d4403895078503001300800042c4000c040c0c0c03269009800d811150b880280444400f00d6070401e1014007815032407860250f1041c02080028001da9104908403004446022104000810101c11505000b03e0102460048140010040b41e0782d0b920315510008000c0c2c0b00b1b501c0c1c21030120001041428100790744840110304144203007980369101c20320015001c00e01c058080c000d80581c80c0980020022641c5e01d50034001840c5031800784003034641c0e0411410421000340d80040266502c64503102c02204282d80c0403900240c211003080720180b21003450100e6003e0003612442c014020120880028 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 496415377 1250 496414127 496414133
    0x2a07060204050a30022e090605031b031005030a240b130207060f05181002040806040f170301030b01090e0105060f0d0c0e0c1306020607020c1e0409080310080307 71
    0x80c080203098858048003211101d001d41d540c070b901d04d9600f21550907100501501480e006d090601c110582480442c9000d000403e0f028403030400c1c1c2e0311480111080030302100c61800c192490ba000140f07100300d4400036103400f080d00d0310203101300041c4034800c12250b01440d0b54000352594910704002d40e0f4445c3c5280040340c299590740c055140a6845101100503a181d030b4a040c080090718115811400302802c05003841202e05010700c000c2000c0d038107402518030301400135108070140d204510900c2015880103021801088441c880040303054071030440f58210fa12501c860311955002644159504e104860040001410038064600c1031303070091008004a241440c0007403207d01c0d01d0300f0716274002ca01c48103040c02040580300301c00c40985500407800c10186010b0301451030070382c0000b10a402b4903604641c0000c44500014201d8000c50b040d401421040001030140a038000305507030b6056940141c0e02c1c1108058940d4492940b8140c01020342595a252480755642c580c0701c00d03807000f00c03554000c2100c9008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 496416627 1250 496415377 496415429
    0x1080c010f0e01030b12030306030f150412050d14180d0f03050606040302041b03200d0507050f0d0912090f0b07020a05130608160e2a07060204050a 65
    0xa81e1007281001c03145801d00703000403401001030301102c40e00300d658104005044000000958401c0301c1c102d080303444100c400300c07c8589480410810340031082d082008140060200ea440406510301d0f8a002402c10042c207080009171040f04c40108100d540000901c1a10010b10456031860800d110007008040c0e90308100a00c01c8111075414000c0580e6540800c145a84607000c035001160000d01c00e00c2004100c14052210b041102105070210345041c4103118600c1540103d0074420421200031070034880c1c0e80c180d1a0160000034044400c000d0204001c520129845010f400d481d80c07240c00015004201c0e00e040c000c44211034000000741320f6407517000c00011510f411140f059034030542c0f8868030f4034650310101c2c2e07405007103400040c2c0c00000c625035030301c40203860740c068003c403001c0e03408441c0107010552801708401d6450040c605c0c1c0c00091300c000340c440c11405030030303100c2c94400b175803200c00100510140c170a0b81d8102c1c29040340d8042d00000e04201528006800708054401040781405200c0c1248560b00713 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 496417877 1250 496416627 496416647
    0x409061e06170a0216242711090103030c0b0c2502040204030203030a17010501170f1b0f0a080108061e1b0f0a02010e0c130e0309041103090601080c01 66
    0x4040c9403400100c0b4070440d9010b80f402d085003520000d40185036407400b04141340125422001c035030400d82d5006e1070144c0c0e9002e1040f0b02c107090181c0c3c04000803510043e0014010780f84059500f0943c049100e00182c0340e60031403c0c02035000766a25004451b13039241005c000c1c0405012056021800c0c00b1000b4a00d0941d1003040c0c0e00e43e2292081e110000303803880442e02034007903540080c2d40342c007012541100150304a950889180c0c1c0100789181180c2e00e420041d54020314924841400740c0d2716200144074000030032101ca8200a69040070100c081c0d4400b01c000b10355121400580d40d6000206901040680041c1035501610f6500040c0001d4508600641800340c0943e0324032855040b00004540c80340c1521503030804520b05002c0369517030395568440704401e9a00400501d0010b602e000030b42e110360480402c095427003000041401081c000007600d900050501c2d90b60f5a42640020040070503180c0c0c4901c103a5010b1028190226282c0c41d040301c0842c100b120590203001c0369000904840b1f8035a90101d00a8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 496419127 1250 496417877 496417907
    0x306070305090c0d2907110106030302060711010b030a2d02130507090906030c06090b03040c05041d06040506010303170f0a021c021206100c0507120609080409061e06 73
    0x2805040725410445042c1c001074041c010088a0003034070001713200310207101520801c03031034444855841402d81c14071708031025448081c2c01600700c0d00214a40d94070074054502c6d1034031400000703c1c02d030601000107424440310302c2049461485654030f520801140055049451a010703000341110000380d00451040488800b503100c4055031030300013031201409420700d0b80103044208400c000b074a07141c0c6082c0010303507254002e400c0450100075000524501c603004581c03066038041500d4044902d4441480068040643c41c0c01a0800c00e0080303c0380210100440e602c614000e00c000c04007545503080c0500b010b40b40185d041d010b102038001b04500240721041854100c0041d800c0180e690610300010480040c0d02d00b0740d400d842e0300004202114480c0946440d014500131105400240100318003030b50b010398480310003411a041002d04010310341180c003208000601030100491004250395550000d0361040c0c11a44031550344200a00c5041d002030040e0501d5015944a820001d04008000d032400710401018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 496420377 1250 496419127 496419139
    0x2301030809061201080307063b0c10030f0f0c02060c071109040b09010b0307120b040606090e030d11090105190c0803070e010e0d02060a36050306070305090c 69
    0x10320310b0b01d9070400c49181c410524a100e0965031074502880e202d520500080d15070508005a00d815000344a21800713800201101440460005101141400701080002195409990111503254603444130308a00d5880340d58001420f5210302d00c0c404121010800700b82c10f000d145c20001c40203182c00080d490b81086220f919181c80d11700701d140852021903581000c54003d0180c000703100030002d89d014401d01581501d4000c2c0034600070300040c10781d5011507200349201d0000581e844008a440c10b00e51980050191402052054441c5280c600b03a4070320069200b402d0744001038280405003070381f00b5008444100c80c021841c1c607481e100001c2070360142d81003d1101c150100040711400d4000c441040283e544866216140d150003803024000018042086d40858004000902d0600d010505515126401003c141c100651a0300440d070442602c00c031400c1d4030502d0035143e401b010b04030342000b005591003440d40c5902400c1c501490700f00030000c0d1610040c107003003100340100b0348401b0070000154182540c2e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 496421627 1250 496420377 496420387
    0x80601050708040305010f1406030105040b0711030d0c0215070c150e010e0d02010606090611060109020a0207030812010315140f0601141801111c0c06020d1e23010308 73
    0xc042c50900c02ea80c00100701d0341c0b80c984c000350242c91a0304110442500300c0030f0000217540b00c4080c9070980d00e0441c1d0080c0240074940004003840d003c0c240c01d40340d0800450860f030510000900d010210707481042c112004d40d00000b5030000c04e034108000075600c164240350500709011955660310002d41c10380309484a03683c075009004011902540000d209009040032103000c04442080a4000c040701e0181c00b001405d204008105903004640c0d01808814a1009101e075a00e406841c00c02904010410b4085000d2408000b0110700d101c000b50081d0441c2602d524080e5145142a060340d800d08000c8150450405080d04c0500b0103070701c111980301081183c800303101e80c0c0b00c100485100521100b01018138001082c0b44120803e0605000d941c2031003a03d45004094247c08a1a9101d0f0b4003900c13003140c00d080000d078248451040c010241228400c0d100903060510952484007680d03030280805000030340701c08001d0905000b03406024110040410140c0c0b1481c007014150441210501020b80b001c440064 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 496422877 1250 496421627 496421633
    0x201030906090b0406050a09030c0609030c14030c07121e0c0504020c030306040b0402070f060b060708030702060703061406040b0304260a030c0207060e0108060a080106090c1805010806010507 84
    0xc1000955848042007000425602c0e0100142000f0f56090311218a0000041e05251241c4102e8800b181c1546501d05054607540c2d0b03030809020004421400c01124100b03100000e012400e00a003201d1031070028540780c1403494801880c141440c0e00495a403283c0762028004078041d40c00c690100642030f0121050402d5034100b00c0202c0003954807081c0c00c9880010380300403449010002c0c6000d0341c000c4a09004084481d01008180e000d040300241c2043c0780304006000184a0390b018034040300c030190840b403c0544644480401d80c01c01c540325405600054204142c2c0d80e403604c1506c0c09803890000c0e140240d20290301150142c0581d00625003600d0001000c501402010342c040041c00001d070000040c95107070660b000840b034016010301c0f40030a040004603485140080358483c15103019a41c0c401c000c1e20403078011910f000b806840e540c0c02405411001c6103040c428000c0c0c1014003c07801010614004140000780301c07070000316030040e451614039001c2c001680c0c0b101c1810b4210b0402d1070b2207626152141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 496424127 1250 496422877 496422881
    0x60c190804021f020f0d0903031b020a0b1b030a050d0b180a0e011e02090102070608010b092707021f0501150309080d1b140a0c0b07020321010f0f060903060207020103 73
    0x280514882d211b402c50300b8048076400701009055901c01d40d1141410344407071040801020b01c00000035400400c1c034070107216403031060340030700700719a0592442c60f1451170112109085030b000c02048000918001083c400b0050035008505034481c041e50101c2450100c0380760407514450150018072400d80390700043d80c0c0c0c0f440c250041c462034142a00081c05200c1c03040540c800031341c40807142d50b01600481d040014800e0064491504070750740c101819150999103002c1212040705541d000401110486414a034060724441e1f80e40314064a0300241042d840a9168030721850013844a030b01c4c5030341804014841c420204150f403e82007807500f030104003810240b810a1840c0628070000784440e01d00500f88418200d4040c1d07210b01d035030168854401807150401c60503414828a041000418011024080003442c140041030b03108400344160703070404080401e03208210940490544440c101c02006110184814021900502c0d501885220b464075051010781403070750b00e100240400303030301044041c00d5902035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 496425377 1250 496424127 496424143
    0x8120f090c0f180a14090d0509100c14060a0b040b0105040306090c0b031603200307080601120c0207031202010c080c0a091d090f0d020c190503060c190804021f02 71
    0x11140c4409442c0620001d0005c15444031000b01c221810000b291000e140481c1403044003550f0fa503050f150410040c1400000400201307900204170050706c40c0c40111f210212603181c03030b0341d45101402141c10011010b009494421040500c80d42c0381140241445c0c3c0c01c0b00c2142c2c100e0b80d0006001c0764000c0e11781408404d100c407a134000f0348055000820012141c0e0b851170881c0c5800500d450401c01e0700809c5000d2100528035040c1e106d0410780800c046200c030b60141e001030350700241c1458202d406030b082d0081030040c1c458103d44031300035a1001000740100070340c030004850701c8000ae100030000744460240041481c000a1b02c6408107010005d1908142c0c0d119a81c0e071006000403204900440b94244034a4072900021108080c030350040584200d2301c80300c049640c40e2480220350007085805508001c20000298081d11142d03000341d03e0b0f2300060151802d1002c42c1c030881481010301d855104200d2020340c0103007040780076010450000b04100059a440c01c1e1490a00381c410030841001610b007005914010b15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 496426627 1250 496425377 496425409
    0x7140c030118230313030507140d060b030f0102040618090207050c0d1b0e090607020a0506070e1c0b1909051b060c07080d0201150b09150708030408120f090c0f 70
    0x200740d051700608550070b0044903c2a002c5a81c07296035042e20714482204544030962100204000c000845c450303806c40b001c440720050039142105407035030f00f0508a0780729501c0580800c0d40041c100050300d403048540d500901d0115001e600d0318255544064542011158030761250080d03440a40500c0040c80c0d018541d6a0740b42c00a05410751110b411221465086400320a81c1c1304000002c0c90403440032581040740c80e0f01100820050700c071300f44103407280038201c00a1a0406040082d86280340d070b03445a0048054000d40ca54000d90521040c45044950310080d40386481d4109000d0340001803001540840f0681188884030000710a00c0000b246da01c0f0709464050300c1e2145290110f1544030100e42e0202c804010303002000091103030883d03403e0415180c4070b00c1c031060304148141502c0d40bd0444034030000008404c5024589030907a603a0520b40e4200703940503100302c98007160b02e1180701030910b08540c2100c81c56403d60440d00d000310030300350f9a84003601c101c2d008507190403040d0110b0701c9100c4a2064610 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 496427877 1250 496426627 496426633
    0x50c12010e042a031101110a0b011a0a0c030e040f0c020f01050a0603020a05100201022b0b01030501032a0914090c090f040f080f07140c03011823 64
    0x6900c5038119000c041c266010303602d000c1d1094980348410a0a04036a40c000e07400306510400034699140c00640e44081e00c40c03c2d052040002c01e40c0c00401c418448001c80c981300303485c11149541001d59800c00c00c103208007502504002009031030106504200d148003400c0d4540383c5803254000d0140400c0151019000b140441030400010004242d0085884012070030300a008001c00c0c0e85000400e001c0d565a8840a50001d040f4003042c009410301e0100c4a40c001481d000140c5412084c0010490403959039441c107800034601240c1a40345a000e000ea031495000034602888103504603100e8850000f102e5410200c0c0c110800340381c000c84d501148480004112804c008c202041a04d5030200340c19004490504d900e00800d0081c0d50285031a0b651a8066021449028003960783c81c1ea44032000102007100762500700007407001190720f007411300c001c1c00d200c0e10a1800c03c0384068001c4815180052103a0040e11030790400a505014200502480541c20707089050810f0039004028110800d8805003100b481c940 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 496429127 1250 496427877 496427879
    0xe120408250b07031d120d0e0102070f1401120507120608070b03070c03090e0c0d0c11120904110f27011715030703060617010207020d0303050c1201 65
    0x1000030414540480d080507202210707003900406148001c005006100722580d0078051640800c0c880c0c411500520b500c44a02d030b22034800c8a0000d0000d45640d8003490066100c0c01c03d01070070982c41880414203110070b00081029a061100030600c1c2c18041c01000d5521450702031141c00790388510008070f411340000c02c040041c0e080020008004044071620303d81000c1c01d2000c0081d103000c001440d541241c3d4130306d211601f983c03035801040783d140c908244107804015000074040f41d904425850315010b60b040c01d891a64a166190003070f01501c0300305a10809208022031005248200071800c024480f2110210641d14075401000070000d103d000301280c9801000708007010307030f0000003009002030a60b0300d25400e500c0c8a0008203041078000700c200c041c00a1852880e042d180c11000001c035410150803010040c078a40010301191a206a035030007034a6068441100b000160b980030075800020f80c0e100e0080d843d00c1c0c8150040703000b02074030b60001010566600c0008054610200a81e0b00c0410702071700c00301c065 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 496430377 1250 496429127 496429139
    0xa06110d050f0a0606140301210b071e02010c0f21020c01020409111e0304061e0c030c020a0309031b0e04110f06270604091e06060c02010504090e1204 66
    0x14442c01c031a40c008213032074004003003a198040d00714024500e18501c07a8616507801c10411010150a00b42860220001407420b50006250030940600c203a0450b40c130807521f4010800c4031041500f600c4200015649005041039007154002c2c04070810100c5810302242c44100344440f280000211a14001400e2001c0351491a0310742c1074004008840000d131051082458030f0001002070311680381c10422850380e03041c5200000800c0c101540d4482d002e030754005031360b0f0040042007042408540c040754100d035445000c0b80480d0382610805500d110148001c0008502590700a0640c00080c080904524070041603030b804101d00c0c0700003102410355600414100e081c14508002410000c506140c8180d0346541400501c0c280070741500e40c1c1c08545070524590a81460f40d4100c01c0f418002e01355000481040040781d00358280c003508045203481803c1c603044500d807080003012034003207400000070820300f08800401360307a022050310207841801500149981d02521554039095882541000014012800040c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 496431627 1250 496430377 496430401
    0x150702190c03110301020a0906110a1a0709140a120c080a0c171504080d0b04060f050301060b09011707021f050106080f040c06050c070e01120212010507020a06110d05 73
    0x3243e10070340c581c00c8000c80300e40800d0300741d001c0c8002002c000f503a6081c0810450b4400c10700340f080003401e04c2c01d49016056a440f42102d00307401002e400a035412820034481203e5210043c4d6008108818408182c661448005070200181d03100b40202c10981345d40410a200d040e1a1900041601d00c003203610440c120b190070a00c081c2d01e485544120360102c92154501100031400207501c0503141c85400d05561303142d52f00811508851080503100c1d80d100a030b0f12035520b40b44540d00180a00004003d5200d00c1c1400305400c2d00c9031504a1000315000b4407a607021030740c1061410310030940c0510303800322544d29000300b24503140c603011301c00401e040c4d05425141d4189035980510b058036082d41c0c840e8590f554074142151440c0090f580140103020301039040145511503005003025501c0c0c9010f60f14616075070700d800411050203800a403490400302d001001145007030305c0c0b068161a4100c000340254640030700041d442c0c100340c00c8050106074642d02a8801c2c261000304451700030010aa041105040070002581 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 496432877 1250 496431627 496431629
    0xe1e1522081b2b050706090f0f1a07330608151603060b040f080d09060e040c0509030a0b040201030b01020a0f060c020a0c030311070e010503150702190c 67
    0x829004250044144428440000000000180c011140580c483c84003a400c4030b50305140341c141e241c02c0300b400c1c00050414040040100040d5840003101c0342000c0841c100c40300707154041c0001852585040242c610406000c45902ca20804180d441d080c0700e04000404651030318680980c41103c1800c40c2c0401e0130030580c9040c0d01d91280301000642c0e00c2e11803541d5a0703103611140b540d0800a40c2d00013544540d4400350250002c14078a00450303540d0799070240800d00c1d00203400c003d45024250800740812079040015445204040c40c1400c7c4103460450064402d91500c80454040c503201c40c983d0000c1b9014204841100c640641202d030946254140207020000a940403030020b820300780340c1d18180d0310000d0820316503600320181410b01070490752650003d218410380c0c8411760040e0202c0ca00802d2018000c180110300a445582d04015010417581c10030200d42c1007003074180030340c10051100da2000901032840000044224989440340641a498056440c0044503862281c0e4800c104001d000f00c8414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 496434127 1250 496432877 496432889
    0x6010306060e24120304090e030705061b040b0a230c060f0c0a0309060605060708040810050112020609040605092701050402030a0b04030c050102190e1e1522 69
    0x1e9064885808200340303401c42c03590002d0000b52184115035907141c84444808944c03802002c40c1e1505640d0304200c0161a9034003098001c94002103070220610800780320003640810344500400485c101010542c12a024900070100399100102c2c01d2415103000d014140300c04d0000720141200350000100100c05039014400e403820b180180b00221344425a00c018417030042c000e403040641001550340c0b00f10010121250280c071038645401d00004c55845000040130440e004440311503542e41841c507140e1504204c0c900e2616000c0c502801040b241c411038194007112941215400c1c1e40d800d1040c0050003406445d0080303a48032140c08180540c40d01e2610654081005120103483c1203c40c7d210010b080f20000c0b20081c0d0541c110f4080703000000c01c003072a1960300910034140000d01d40c1154590908a810282c080142025141c0546904c190030800140d502c42086550840a8901c1d501480707803074a940d180c89000ba5800c0c21248a000000001d40b1100c9800e807101c079161100c0004201c000c2e0443e44624 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 496435377 1250 496434127 496434149
    0x60c04030614010e0c091503150306070c0302031204060219030b0f010203270102070b030403093303020a02031b070e0f0c04060c0821180a05060a0203180601030606 72
    0x148032202140302c5100e0413600c0310303602c020065a441100c80398a42c040c0b11b01c42d611183c55241c100040d1680300c003460042c494540c04081141904040c10b281c04030140002c0103000900c04100002a400406c80c0c04181d5034140741c10403a156481d11070080d02400401d116003500e4100c0c04044070750306504c0030042400c11907010031214100c130016a22132045c1c1802e001100651011542c0310b03d214400000c4004040c41260780095075088a040590001d07541100003900b6043d082181001c001c041c807400001d405008100241c803000741c440a810031a05050a1540108003811024000d10a80d200c1c1058014014110800c14510030f40702c4005001d411916040c1740082810390701d01d21281841414800d162514181c1007210945a076040010110b40100c000c018010300c401400f042c1d003084551801d200405d40c10201200318441c0d100400c00d4126511500c21000803c1c4005135840e0084501040180d507511080304102c421607900c0c40c40001072041d10000410851164044000c40b0a07800da0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 496436627 1250 496435377 496435391
    0x11150708070f08150a0b0a0c060c110c01080a060b0a08040c120201051c06180c080703050601020a020f0a03061112070504060905040f06030203010e030711060313030c05010905060c040306 82
    0x70948028660300ca02d031001a209000240013000c00400902d41540e0040031002002c1d42c840f110304070303070b84500003510000d40c00700160300800905020b1100c11140c141428079800440040c0180d40c0d019400781c4a040041d80004501d04a2196000a0280042404255956403c504050300c201c009036000c8903a000c2900000806c080e10004150304541d05942c2c445c0b40181c40070040b0070720119034182542a680e03420000038080f0201d0b000000c1c01100310310110750b0401464000d416001c0c0240300c03505050909041084603a400310341d014149504468400e40703910340c040801c080410039003000b0203091074000c042105800300b1028000c4048211000c0c0307260341c2c07680b00458250060344502000b0500c5030038140668078040c1c100c20720b002d000900018517030740daa4001a0a42e82c940340801c0c0290400241c00040c014000050380000b01c0648e1001e1840c00d02070804816400e82c154058200466241803004104082d0007001d2480d4000084801d1400d0116601d602607200303100494000d460159 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 496437877 1250 496436627 496436641
    0xe010e070515040618080a150c020604032c15040e18030703032d1a0f03030d0b030f030d05012c0c0d02040503240c072111150708 57
    0xb80b00c600c14404562140c241403034590183c6001c2d8402c420202c3c81c081e103480c0829450f40400c0191800c43c0107050200080b0031aa1403d011122180380d104111b4101004000c04030350044080d106150104108a21040404020480d40c64507060782c19449010001100c8503e40c081000e0015540d084841030b81545801e10407110207080806452800e8005010310400b10303000380d11080d542d0320f0440c0d201c2a00c41030601c408091068000404609658500000509a0208002040001041d81c846582c00f5075400040d80e07900034400314000141c3c6030b101090064a06128450a01d504081240d48034214a03201c4000361000b401002504490708030200702801d1804045041020404900302032611010540600796104001c1c001d07529400b0800060070fa00c04002e00e54000e0002500900c08003900600d000072003401601c40105407005106038030121349101c2000b07241c400c00323021400e03400884040564040007a5003490703095010354900c00d00c0e41c1101d02402881078041c1ea0764110aa40c03019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 496439127 1250 496437877 496437889
    0xf04050706020723012d020c04020c100507030204030f0b09010c030903230f18040b031609020a1403070507021002030a020703080313060c05130807030312020304060608010e010e0705 80
    0x1102c3c0482c00142c0040b415080d059900c9107900703a04d4107251860318052100090341441c443e030354240b030688106d40f504135803e0745c3c14016121034420445c0c042d49060300740c010f010703650000302a00003151691400800c168a00a40c110750003181d05c100103841c0752032107080510040004540781c0b2045c0d402c0007243d0405912900c1003512a41c0c0c0b640350300c001090240c400c03e0002d220a40702c1074070020200401280c09030b040b005000b03841030b00c0740070000942e14101840b00342c81014400602aa11010355103000e518140b0424081e9032080500503280d82d07816108803110b0001c03604a45800400006202c0159801001442c00c28001d0782d01700003850300d51204a07901d03c103041c90100141c20954082c03000800c0000115000261224030349403c0d44c3c01d855000403642c0c152040341c003042c40013858141801198003814018254031001e4003030a459030710064040c0710040310101501e5800400201001082c1e032001000d410004001c01420710b500c005103000300213401007880c03541305003440020316160030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 496440377 1250 496439127 496439129
    0x702150a090b040b0403030e0613111534060c030c0804020a051c0204051303081003050d051605010504080904140c070206090a0806070923010801050f180f040507060207 74
    0x2144030800b0b2a80c8a0b100c0020680e07014000314101600c80c116103e000008010305030090031311141503c0c684074030780340c81203610b10540703503040c094500405a40b0080c00b00c00b041c0d4400304805c00c5400d0001022101444007205803102030100805203021030300a00266a00c1076a0000b590b8908110941c4005030540d505a0200e5000758841c0f442081805181411600c20030146c1104500844e2004e00303a00140648101302c500200103039001c4158805e150b4018962a000150381e09440e01450850300c900703495a007048200d8081c003100242c80070400c0c043c44428490280c00c04020401410f01e46041c010300e0303010400444c45141010030510075032502c44159802411815045880d1080550034040c00d0340014220a900494100f800a40040c0902507144607042565440000e1428814546c00c0781c4003542c05052580d804110032007483c6d800c01011170543d0701c201e82c02c0004c0192a000505055030f0f04200c410415804003d000c0000c03488501a4042d502c68426194000d8880c00201d96440f4a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 496441627 1250 496440377 496440383
    0x3070c0e06130e0a0c03060507020d0f02030a0e210d0201051b07060515120a0204050c0427060b0406020f0f0f060103031d04020406020a110103180312140702150a09 72
    0x14000003a00c40e441c2e50020070180c3c952000e540d40d4903101e0300c0e0f802c404e0380954415910340b9112010400d01c1d85e41844840a19510340c2440d8140304003010b4001d580b405801074100620410400914090303440381440c14080c120f10002c1c50204240801c41030701c03041d840200b41c02641c00c140100c0c1d2208400120354006c080c50301c0c0700504100094452102074400a40440c50f080c0c20344400c0c0c0703855180c624021801142890090031440030b01d1050104a0f1001010f8020091050105014650041001006110700b500c01d0909250340003002c80010041c541c407842c1000c400250024005401044241f00b483c0c03500140c5000c0800c0c100d00c69194a688424040142c10031801400080d0146010f501002c1d0f00b00b41c45405a49003402003001c0364050f03041000981e005039900c8003040420b00fa40c0b26075075421301e0140851041020000ca4103a0310038001014408210300e4100e2103040ca0344004001070424410b4015402c00310000307500c80203200c145031030809a0100154a402c0f10307001b403040680d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 496442877 1250 496441627 496441639
    0x30910120b09090d200d050301030317040c03060203040201120507020a03120203013f320304060f0c020a0e0103020102150903160201020c0a1e060c021f0c1403070c0e06 74
    0x2001d02011240031003180c08400b008005a1000701e01003d042081b01d1400f0303850f0716007541d25411828040c002d4914240d59a440c40d481c0d8040000043c907562074802242c0d8001c0025880b51210320041c0c854200e9000340d92141e600e00410070000d141c1c00103401d101180207440e5400500700c0703000c0c0c880a070311003405802125803541d4841c031026250b003800a10340001146049040850180f026025007144070410395250b1200441c0e0805040300d402c40d079200c3c410320302c0c0000e95180d400c181f4948034050361080c2d0060013180350a0300c5000e4007a0849041556004160f004445d84a6070708200c0c040007070000388c1c0103119800300780700c01c00a803001d020301036030b0010020b5040c142076001056456558103003c90441c0600081c4410355115000c584020340b4145440500e4a0f02100d005002001c043d0700071810003407414212005a10385000244110100901c0c0410107404c0403400d4401d0200908010400c50702190240707031104010000d4140749120781e0b040b422450351703407801e411410030948003258000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 496444127 1250 496442877 496442893
    0x911040c031a091e0103030e01030f020a0206010302100c141c111209180708072606040509010b060a18090e0303190e010222050103090b18030910120b0909 68
    0x103d0210380355541300c01407803a0344507400140c0e2081079100800303034070071404a2926001415990381500486010082005c030460500404020003951024107100107409070404104500502e84210880d0712a16005800c054030000031800c003940d100310f00130714640c424640e680d841c070001d84600f40b100c00311a001070041449034269810117540da8002c030344c03c03540000511900d4141c032f000008207610520054880105928062074040c2000c10035110000c45410380d10036014a05108100e81504400295030000d159038680c40454010408140791075448200400c41749071030b0385d0004c1400094400c001032010000e070307581100800d6a1014880e42511340007400020180c005c00340d07603000c000100c0302002c100c1c0301040c0c1825007280e015144114401030800c04001d0302900e0389114070002e0000b0718080080c1d4110340c44003440030300c0103891080300032101003103949518030030010740b11840c0008000052142489801614141d5401200010941003010411051070310440c240e10429421000e4443c40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 496445377 1250 496444127 496444129
    0x3040c0e0903131706010503030f041a07060213030c120b010603051509011206050c03090a080d150909021e030d03020a020106030c090606110706020a0305030403120911040c031a 78
    0x500c008181100c144030521907042003030500c1d50344500801254a540602043c0e051009041c201d05803c0f06009500c1002426120f014035011a022030b0b0950200e016089141c100c400424429a00050401c3d030000c01d60b40c442c140c10350352660481c0c3c403034151120302507681c505074102d00c01304008c06032005050b407004221050081c0c0000742d1005d400c030401a69201d0b424002010079400381c1000001c03c022841b03c0040001c41c2c8a540c0e00030b68035813400e505618000c2c06007580d40c000c1c1e5000034840100494582822031450700804020038500e10700d68881920b03141050002c0c9104402644908042c6010180b5400d07203580403145458060041e016180c101c80c800e8001e9880090400704566985400101240118103a44045c22040e50301003005803401400030005e68035000c501c4842d80051004210458001540c0b600c11540b50030066101d5440b0704081d01d03e4443c0c4084104051309105404003000030810464a6441d03080760708110704071004100700c0031a008030850500c514001c8000c4061 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 496446627 1250 496445377 496445399
    0x41b0f060203040b180a0801020307020c0a050306010312050f0a050a030c0315030206030606040f080a05150903030109090804050d051f09031202070206042d15050a0f091205030301030c0b03040c 85
    0xc000145c0e4005041040094041090040707240c0c06443c20741d5020040c400d5190b41842141c0102000703c440714001800e11001079120311040c44020011500c100000006a0143c03054500c10310215240b25118004140090610307480506008000703450b0410700c4680901910811500c0055448280710707941c20356003030140f40d500150406911004c180000241c90290060000140074154081c141a1015240c070707510305160f88000c60b248290101c1045003064002050343e045544e0060007254401c002d090100e5144501d4201c1c0b5004008141c4040c2408000541c3d5a92000c6580d290142e2100003107808003100c103104e4000b40015051381794080c12800b00c0c0c0280184c20b00040400d403030580c0c1c2c0d06003640480321102a103112680d0034510a001c4c0341210303d40a0013010780b12a504500e07a1038550040c520311580c0122803c2c000d12440c000350b500e00c11000c40000d02042004100301e00d10385d00f031051352034000f444112600609480301081c40d07441c3d88180e0b030089034000310418100c0d0510140b101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 496447877 1250 496446627 496446637
    0x70501020c12030910030f020d0213150503040b070c061d0f07231f1106010e0f060d140f1f0911330c1903021b06090603041b0f060203040b 61
    0x800c040c1c581201000c00b004034230003402c082446250050350f0791060000e80c201d62070150b2000040c00e80c02c20840c154141c0010407258003a0b40050b2010765a41c0781c80094481d0f88400c0c40c0507003c1071800a9480580d08030120000b000c06100048403c60300b0149041c0e6507440b014024072084005c03800c989695040c1809841c4a0003800420401d0f26040c002002118101c1034445400000d441d04c9007107080c04004c1c06290301414501043c41c03468a00784140c403c021300c000d0041e5025115504000b02808400c0b280001c2d0300101c2c5094a24007001c00014660310070f05071021480c0740088142c2d20071441468030404183c01e9000c03400468160480c010402d86a03501070400250030300d45440601d00d0104d01646011380c1c03210040c105d440305007003100c80b858103100d02e8080d4021340c03d00c0e5185001c26000900c8100740e03d03002c003031074110301c0c2c3e032001040f01c50099400e4150482c10110501c0b0800855821f604131601d81c0812002c14140e880e00000b030902114820074025030010070050003c1c403642c0300200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 496449127 1250 496447877 496447909
    0xd0c2d0c060f0e07031406040b0c2101030303051021061113272310180c030e060f01140a030219150903050c0f1809070501020c120309 59
    0x1210326000c02ea6005035007603401c3e4030031203400c008020f200300716000c00c003a4840d810103801049245010381d0748000340c55019042c01c2c0c0d01040803400b5451054140170180e0030304c02a602c40019035a40e4070b0060003815091754244070b8034003600008035819a150840300c8140700700040340b001d18020780d100c0600801a04007801580c2000304012031035021060050070080c0079104200c601e203d03000740819100d100c526004207084d27090204c404192890060341c1c05641c040c114582c41c180c3c46000711b06810400a46c080744052030301d00c8200301080c4c65a404070000400d181c17414000181c0038508103880c0c180c00c44081590100303280c0184010b036900c441582c45041e015041400300758a980028a101c1c0c0400c40c14096880081014040b0302070100c5211048007a90900c5020a41035980e00f40d12080004000e5000f5440c08260920540e19520550018800641085102d060a00d9031946a0590707000b450b000d0f10910012400fa8140300224580494030760020310300b007203400020000d890680305025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 496450377 1250 496449127 496449131
    0xf030f030501050402091f0504210209010902180f0109081005040605010602010b03062a030a02030405010f06080309040b18091005070e130c090e0720030708040605070807080d0c2d0c06 81
    0x80b4ad20112550110f007118210f0310700310700c108114810450102c1050300410820303401841081c404805180402000c2e407022900700c10740300c1c0b00500403519032403680e00600082c071546600f60340b01041a0b0001d07000700c2c05010140010f030380b0b5440c264240c800080b089900756116400181c84005000e401503400305280d20a60890380c560382c040d01c0e8079041990b03000500b40d070000500040140920a07036a1035084020103110302454041010745034050504240c1c00740c1e03240c68801030165a0f40100d08151307226800d640009081000100390307110090800521890701d400d000c5440319000d01422912084024000c0709807442c170389032150103040c2d628070140a0006600001c64110302030450035102e0311040ea50001c855030002420012603503220340a02494008100510108412404460940c1c42c2d9041050b5142520301e40039402c0e22480d400500881d41c007086d0201401d10740d40000b605204190399a014000b038056680c2c0912050088103000c0c202d9544038059030034081d0032000d03041c034012200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 496451627 1250 496450377 496450379
    0x21203090a0609030302031501030515040218090a06030209070e0904081c052a0f070803180304091406011701031101110a0605040201020f03040608011a070f030f030501050402091f0504 81
    0xb040255500c1e68021804250080304110007502c80e110001000b54003460203010706d0400054010400001030202c600481d000103030340780019071214401e0030700c01018211800f11303c1c060441200030071083c002240728119807008642d411744034503490300701940014000705080c1c03115a507001c4568002c0385800c1398408101c980080c655518400c642c481ca8500307034480280441000321520110615104000007039044c080c0c1902d015507c1c081d0f880c855403103024203075640c452040640c00d07800015032040503440005400f00d0b28007903036003000610312440c1122051030780301c803001900c40b40740c01200c0e08030a540100041002c90b1412100411048040c14074841486c22100400e0901c0284d038010390385903840304140000c5581c10001c0c0d0800c4110310016609281c10103000a001603410701c62005000080300103004070300d08840890307030b100d5441030000e034003401240340c046c0078843c84803568400702c1d2904c070000034a0304140c02112401d002c02024441070000e8210740a03958100c600b0350108000003448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 496452877 1250 496451627 496451633
    0x60703030b090703090212032503020727050f04030c03032c03090a0b030c0a08190915050718050423010806010311100f121506050d110406021203090a 66
    0x8583d000306699600491900c0c043e00500c0101400d0f81d0300d00640c1e600400c10114410101a40b0210081c00a4420a05000076003401c03407401c3c455801024440100c10b02d0307040b50300c03041140e1510b480c2155a0502a41d0744213602000041c004640240114001c0103902000a110384e100e0110a00704400704c505a8100f00d8901e03944021201c003a02c07171680000743c6092070b0718000d07800c80d0060101d4070b141440c6140c85101c00b425030044402e000c060ac10710300003007044030f8194800140244810720080003c002c0504104096030381e070b48103071f580c280d24102c0410242449010a40345800703030400e0403050140762406010090480d0074005103003000c5c00a00308403040510480e02d00902520008007265410343c1090800320300f03040e0b0300c148105144499109a10740026900d45200f4240c1003d40c1c0828000c40200c010380660280d10f0000903051102041b001d80003409840702074404001048200001d1003211114460350050f8000350348550582c0404820400c01507030f12029202c15190040002e41d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 496454127 1250 496452877 496452889
    0x30306090e15010f03020d0b0a020706050f060f0a2709023c090105012f0f07080a05151f0602010f0e0115170f0703050c04060608070905060703030b 65
    0xe0030350500c68120101c03207000d014089600b02e01410392107504040061540e40024081c0e000d1040007442c0c1d2800c040004c034010030941c140d520340341d04113809004030b180054036a0800f0a04841d2148585021800102d4905000701e440b01a6070354a1500034a8402089005000c0344d8407805445403d5250154400180c8481482c01035000c0b44100c3c180814006407040c08003001000309290103500c0e0311901c42c401e5076680512a0449400307080c5014411300118600758010302c40280c0d403c00da030103c903045002810020b002a100c0b582079003511a05510750650b16203e441c1c9034806002503101d510b449101011120820760880e005841100c1244010865410720056540c403110140c2d55450804070350f5607a0f801200321344501e540c020060b4400021480c40940411302030912901000038a03c0120082080528440304040301110b68860342c85c68490b9598025010180c0518241b0030300084070f0380100c072040d000f5441c0c2d48424000a040c401400351941100c07606408040d00e81a800c00161101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 496455377 1250 496454127 496454141
    0x9030a0b101a0c250e0601030f05090604050705010e0603041b0302130b0907030615030507050f130504150f120302071d10080c030a06110906120702150c0d050403030609 74
    0x2a0595a100c4a000c2d07071083c100212051008010222002d0403c1808030000c218400c0c0e81c1c0343e074401c5c00030341c0382c040c0100c0c010801004001c2e0700921780800d01c0800040014045e03c100d10a000311044a0307290001101c0d103c040640980c0c01590500c08140002c00c03400b084009a4612242d19500d41e96a4001441c01c05607440165030081d0341e012000250b0801c503400e1a4400340d141014005030346494000d0000050f00d8180f0410540d54601250090b8850002c40d0720703100c40407000e281c0781c100d00054000c0d880318601c10148a145044007284244161800d40421128000d5501c2d401625255955500c0041d080c03084045000344c1d0008965001300d640354070260140001c0780b00c0307546800c10403400810001e030021030b80386e40000b03484501d645d40040c80f81000c650001010407600c400401950040c040d9680490b4400f801003003c5000c80628001070384600321985c01ca40c601960384108ac8044003082e9091401c100741004540144d2005030061741d0445d00c45e00e40001e50f6656002c03400112841 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 496456627 1250 496455377 496455419
    0x141212070b0402121c0e0f010f0806012d03050a060b040e090114070809061810110c0a030314130f02010806011b08130e24010908060a0204090e0309030a0b10 69
    0x120f174906299071250010b21044000e4841d1300e210255100068103442c1c2d40e0041d0010049031034000307a943d92107000d03546003500b01400d03070707c03c0d0035032400c03c858104202d0011030700001e00d441c2c001a0000d010b800f80300c08803184900d40e1458182002031060143c040100685003940d05c46c005094004840028a4800d541036901c000080c20303c00c1c42e0381d041880181000ca2a00e0509000680c80d9001042d0740e5020b45d02441b000519203c2558405145d000c0c544c1b03e0221800389a542c0c1080c11b415412080c4000002202c022481d42d0307a09211400d0809000c000d440e62505a46100055018600d05500410305040600c4074510305408800044030041c000c452501c400b041001213800d01c4001a806080507080078865880c0a42140101060f40154550240200c1015604c180d00500c1c082c0d0142028805a44003480e1100c00030340603600901c16090000d19050b240100d5400c044242c4244000c003c01800b030f0003281d52030b180a4950041c014400241c3d04820010b2251411490807d8502c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 496457877 1250 496456627 496456663
    0xb0f030703110705060604150812030601030b0303071a0a090f1a06010e010206192004150c05060406110d020a120b0906060f070318141212070b040212 66
    0xe8100002410346400000000e208542400480c00140011900c2e81e4000c000f070782d0000c0c56403c0d014001c1c031103010329840b0501030701500100c242013070364a0000b14441d10303080e02c1c280171611405050698130304c5400e10103484050820b40e503070406d4100902180c0c003d908100c001c80c48401c44c1c0c40340d41d01c0340c200310011608407842400000407004140345141e0b102d6804d007040c13440418000001f035126800240368400180d01203030010385840c01c42d8007800803c0b040703042110490003a0791108a00d40d10500400384804981c1c140c00207164810b0801010803517221000d030000e9212a580c00740645000942010300c42c005100200d000c00c1c0d984043e0207026141ea40700f00450b04010b0b50b1070104c405245031701e0b004600c5070040106c5a19408200d4008280d4111065910201401e048810080e031112000500c414858006030007040088101501345080b20803e9a079030001852503070781c0b02c02110303400103058140309820104000c0120b50b644940040e1003101e00100407840542800c07202c00382060204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 496459127 1250 496457877 496457881
    0x170a0303110903070b030402210f10060f0512120d0204030c09090c260601030f02040510050a060c020a080a062007021c061d1018021f05040b0f03 64
    0x66140c052404201c00d4484024980301941021a45804850160800d25040080820b04545407400303804c00010182d10107aa440079074191941e11601400c012840e0f5100d6034024900420961103403100b110040214010150310305024000c2c0c2056503818079503940101030b0040e008940e404000c182c0018030900059696085240c980d04a14203500000022441c0441c4000050b118417100004d80d2070511001c001c07014105810401c402d5250380d40e201d0f034040c10b0b000008200c0c0e0b6008403c1c0e021700c225000d100c142c3c0c42e400210701981c15413290310303400111500c082101d0360141d20b000b07040741d00140c00d076641309440705012490408424011180c159491644e82c0441a0200c06007104942c1042c5107841c00101d03400045034040806032940c51104840d4601d420000d030399015010600018540603170400030707111101e89480844079603800c00c0d820525482a5040240564407d00307138000d002c904214002e2829001000080c60228240311040001054a454401c040c240d460402d8246982ea4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 496460377 1250 496459127 496459133
    0xc040c050c0f12030c0310080d021b03010b0a060f09031a01061403150105031e160201150303120f0b060403120e0a060e090406060512010504060b01140a030213170a 72
    0x3000c00c20994160000c50f010141e030256001143d42000715a4040344c0c0f2a00d951840b0001000707190710100d07a40c8242d02d02100803e03004591418000003601c03070145e40091030340906098034450b03031070300d0b81c00710142c001407002038050301e482d041403141da1600c503140c641c8a60344e88201d0700140741d907607855003c02c100420085a0240c0010b40b11348280d441c46d402c504040c0c0050840c07000c0002d006040c0100880003840c1d00013444050304400c0840402800c3d281032000800b400d903c071000711200154200050300210003035041250040f25410340c0c07426484c6420394000d0000f401004007120040717884d20369080e000d664400141000d9800340e540131091011203a809480d035500950414065164158100041c0d60051250b41c1100c8051300e07013184540d0f13207240c1440100034580041e548918450402003181e0070540c0310350f22840c42100d042240c50210340055130040c030340d11036482c035210003002103160040c070039005000e1130031b00c000c917150440e0348034020701e0b00806842c4030000d181d03803101c40c02c9014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 496461627 1250 496460377 496460383
    0x1d071d1e090928060b0a06080402010e0603011a030c0d050106090e01080d080601030905100216020f030307020904140f12070501050a1b0e031018140c18090c040c050c 73
    0xc0c0c0c40030018141940342c800d0f140d0f241156051140080380e20220340c0400e21000b0b070041095680c0c010501806280c64030006000140d01790f030140d000620218102e01ca82c04c001080300c0c103036840d00c840303800158002c480020140d40004d141212440040c480c004038a8418000e03a80a849951a0503d02500b0110002c40c02d14059004018a501004519901a0708400c089801440038a4041840b403010300b041841c203e04110700b05101da20001c3c0740c90401c1035891680703008620849612700107001d600100b40d80e038020600042c0d80030903075a01090006800b007060380000700b180001d4400c402e4100207001d00308000070424084c0c16400050f4502042800e01c5030f20740c4203900d19401c01a5500c1c3e28000d0f103503969160b114400340302c0d0403101f1816568040024852607094500d06000c045039128814442080343c0d14100e070002c0d26040702200c0380f04041200020301601038018801c00c02c1c113401c038601c00403000c3c10108540c006c3d03c505d54226144e42c080e0401c0c25206442d52540c400c41c2640c2e0718a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 496462877 1250 496461627 496461631
    0x905040921020102041a03040f05060a02030108010b01020325020312040303051b0a260409020301030807030224040b0c0d1a100c02010c1202070f1502071d071d1e09 72
    0x2c59204000a001c8907044401030b4200c109502c0c031150701c9541e40d1500c41384210309e0000c064a1403041ea8100050500340c0d400642c140ca070301e0300003803144907000001660340f406a90ba10b00c2e03562200401c0e0540590706840003404aa000904403510690080c00e00b0324103501075001900043c1d40006c0c1d01ea1403c02d02807107240040c6e51103005020402c102d0f1030b20380c0402521080049449480c1c5441c0481c2c200d400c09907030192401d03040456495949207001001c1741c0c8000702c1100540640d100e90001031000e08904083e12010f9584411959501e43d0f416032250300040111503001414002100d05201c0e40c070500500160301020302070041c2c200010040b1404e400ca101d4020030280e280c8120050f43e02c000743d1051643d100c03403d401c00c0c1a005005034102461608114645040d003440090b0000611402c010740b00126000d40e4600b684405203c20641080c01803e4420b890b417001003060244220303030f0140f044940c0416402c7c02004ca0700050001d001d07560b044501d02c901004059490702c0c2c072076070140d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 496464127 1250 496462877 496462943
    0xd0f0206030a20090d0308060a081b0301050702070501020618030f0a030f0e0d050d020309010e0a0b0106090f0f0e070e1c020109121110050c0706111014011509050409 73
    0x10f00307040130300c0005112900003d03030003000c100d40c46010826517212100b281c00030742500000e03031720b5684030881a0442e00091003542c500c250708100c0414011800490038000343c03501070b406061150f4540204403c001d031000404a11480300700803100319400014050024204203640200d80078001401c1c0800351501d1341c0000029800c100c2c0b5046402e0f030000211000500c032401b0150716503880e045200e0050105003500c1c4241d01654119804109904039564141d440e59168900307115100c080c0c054040112f40201108a4881c1105114441e4881d08070b90313100c2c0d4203203800005ea60403030b00172441e059140030b100c41100c848030750200110340e044980b00c3e0107491410766668032501d164440040d48044d50038800c0c016035080440c2402a032080040700d000305a4a400c4490301503481d08006d01d1520702d074501016500640b4030000d00d02540d40074205d414110213054450326400c248912000500200b25142440705101c3d00240940300c0b070280000d4280076101e020400803c0582c2082d0b40303a0294010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 496465377 1250 496464127 496464191
    0x30a030606021005101e030503030117190209060904230c0a0b070b130305190206073b0303070c0914060d0f030e041d0105040c0602070605090d0f0206030a 68
    0x4801800820342842c00c9400c10131501b900448185220303c003210182e0800340440c00004000300c1c4100c800381450500c41c002a044409110341015605d03058044583c00070342c40745200001c10a60302d4456102ca0704a0700031150702c3d100c50480c03941c1c0705644070034500d8074001d50020282c0c60300c0c1c2d00e00b00c4504401440c030614400c0c0360510031342e10080c044400401c011507a0381c00707060a0083c90300c80c4041c1d81b250f01f4200080301000346401d01c0603544642c115041400500010100040e903c088181038000340110f003100cad001401c101c1d5421100d00080d409540d0036100500c00304020a060900c5400207008001000521440c000b21500d01c00b14002c0001b8042c0407803102603030001d803268103d610000d0b054900041000c201034005070180000e46898203c004045000400011040d445075000354400c820a009059031f49034180d889282501c540004550240002c1403503051081481903040e12038048a0000185540003600360b42040d90400c8005584140c001d1040d00f498042940d202104058 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 496466627 1250 496465377 496465381
    0x3120b04180b01030b0c1606020a05040302060d090c0b040806061e150301080f0610030f0618060c0909180201080c0c010509060711010605130f0b210c09070c0201050304030908030a030606021005 85
    0x407400071f010109000401090f400224403d0b11403107503003528051640109255030b42d00c11604a6800341c1407000d81980d41800000b00010000c134040e0480c1c3c02c03202020082d08690341d9500800c04400f0b40e4a211003200a000103030007203a5600c0341c501028038081090015103950401e0322007407400c6a0858041e03200d502c1142800410760000f5090f4007101d90050581022300700500d0020081e2501d4040c14000d001020391a4003080903a80020300040055a5071050341a0b40c0c22403441641c80070740c00700120035050361409002d135215084083e8800c2c0d40003c654606014802e5217400c44104aa046955070810414404d0b40b540c0039280d0f507409684803009001590070540010010300d640c54401000071b80d10385080340761907117a411603080154010b082c0103040103510110506030604060489241c000c4550111305440c082071f0f61750084d101561001d4400c52254019916a4000f500540074080b03240c00014141d1010002450300808580c1d0100d00320740342140107131170001d200400c486607a0900007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 496467877 1250 496466627 496466647
    0xc020f0c0604121a2509030c1202030118140708070803030a0209031f06060e04020f091c05010504030c0c0b0c0c090a0b06040b090a050a0303120b04180b01030b0c 71
    0x20b0342e095801100c483e490103192842c0103851112000c14060441c0c500c0c07400c0100240c10300300100903000580340105802d0000c500101c1d01d200c1a03000082015a40351018402800035200c034800c050710290001440e0f010304040d0340c42c40220080111818100d8202e6102e0b68101032040074002d10400004100e00c0303050989043e20303404010003001c00c4ea6800b28507084569020030400620021281860560501010000c2d0242229001340004600300d01181030082c1003902c01c841900300f4a07110b81c1e04240c008400c100c801030074054030107420f4022a56007401300b602031040c00c0c003403031090f1600410b072501d9141240d960041603125120030601482001d14400002c00c040f48184012a00c2d003850350764111120008000f00c01d4050341007000407801080e6040f03501e008141e002d804640075950700d642d0300c0812103d1010f42c040200041c4442c0d1001c0881c0c0c1c16608a001d491200030400709014a0b40d4100220034202e0343c0041d106c241c3c43c24010014030202203109504203100c2d100c51440c20310350714 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 496469127 1250 496467877 496467889
    0x3020402160c121e02010347030a0b09070b030109020307200a020918070608010f121a040303060b070803040204050c03150f030312010b0403110105070c03060f0f0509010c020f0c 78
    0x400c810044900c2141c1104c1168400e9210f58a0140001c0607011407071a0b5128925411190030850890724140446801400d503071f0b5200303501d44c50001070062600b00d40c0ea640d44035580c1c0c006880c0500512400102003a042383c4400038601a1411560050300d07803038103560040c8035002c440d6170115000c00088000340700c020081030810100d0340540b0388011548411126100d494501c800200729401340c010080350660f404a072080c1200d680c00d21a60351305454080400d050203015074028020350240c0302e1030081c554166501580b00c0e010b414001080c6a0f2011070b440c01d60700c074040072181008004200011481c00340f04058001c02d41d10615411031a143d401881618450700d03d4501c154288248107003150760410444444c0e568210404140c0d594550144925402c240801c86000000d841b4904180d44500b080d1b0b04a2031b00400308144003859031708c0d040f0040180409550700d040d2901d5242a800a03c1d0050a00401050000140286800500a0a20341001307815142078101c4103180030344d0381c2e0300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 496470377 1250 496469127 496469153
    0x20d0314070e1e360606121003060c09150305010e011a1b060105121203010e0916080c0f06180108100f0e01181503060f0603020402160c12 61
    0x41d1005005002c103036500100700381141c1c612981c04028400d1090032a010444448818990385000b5080c4c0c0041c402400035035072003298080c0e04a1001e0055043d00881094003640020701354120580c0c45860b512085c00741c5143c03255a00c04210006010807565003603890704c031032495582c9010491b83d41000c1c1c0004103060b0620586070148126400854000201c00450304c00e60034640c21a600314100840c810b451f0082441082d10480c54007009203c01316000c1150440e07000b268110501d141e00b00b0426118040d40949106818460240849502550981e0700c9002c0c0c00b4040c002e24000d403501d8100490a42c20354403440c00b5180078032191102c1c4811110401041c2000d00b0019015540e1007540f1218007981d6110810b03940240c0f00c00100a00b040c500c5505a0b1000745580b0724140c007104c104015a180038505c201910081e40c030400100d1602d078445c031a0003000580c0443d1550b500e130005026a0888041c4803900031804400740c0401069404083c0100400c044c024980200ba8440ba9640015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 496471627 1250 496470377 496470379
    0x30d09090b040f06080d11150f070c05060a0f06170309090a020c031308102a09080f0c10030c12020d0b060f07020f0901080307030c1b06020d0314070e 66
    0x140c1c208410340c0d50320740e005410110407440702002840c3c0d6401c1483e954600044030140031840070041021b0007140803d103581d00c05980100e4001a8450b10604882c4400041610042104002c85000011004d000c120700034100b00e000465440784074440c070f06c2150b4540d40b2485800c1d00d16490f55002d280044140e546d10301c801c407a0207031343d0790b40c0e0046007010b03110760304c0c004400340070028010303588032058414441601d07030b444100c4821121418021048a01020324101030a02041c1460122031010059962203c910328010010340c0c1d0701c0c540146404000c400c00c80040d040744546001500300011580d4402d050362905100101800300c014001c1680031400124441e00000c07036a04055003178000c0e0014142c0074182c02e40d120a40c00d108803660700710482c01c038440d90801c0600082440c15006481c146c500d400d003e50314148895405466464201a04803005ca80c40c0d905040c00340c8502241e04002c4c035a5401401d808120481d000382262645180319140040314002e000015a0190144008402c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 496472877 1250 496471627 496471631
    0x901050a0314070b2b090803150409020907091d0403050f130b0a080f0f01080705130902030d0903050d08100501050a121508010f020301050904030e150d06030c05030d0909 75
    0x45003000c2400c03c0469040079129000010740f03540880100c2c030301203039016180c03110103803542001e0703410505440000c100506100024408902080ca44031445864000020030010340301c94543d0124180c100d080307030a540440d901d40d00c03c0042c0509007800c0383e0700c400c0a180e525401e15040d50040c201e8000c5220503061003402182c0c3c0d22a1008c001480800f800014221945910b085071008114040807507072078400d404800041a100d50700c40b42c031107060b64030b801c01038082241014140403d2050500b07c11210355140d00d82600903031020310442d00c6450880e611141d80a0940c10514a0f1481840e4602c0800c12010108035114105034000401e944c000d00e040ba03a0f444521706c00300d500c00000100356051502d01450b5404600703656202c0c400f204c071980001e021481901c54014104e000912550340c0122403403000400091040b01c0720341d68448020810080b0b07611005e40091140c02034a031a0b0061580d038203007881484810440e01006103012002084002c907040c0c4014030380340062040303100f410303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 496474127 1250 496472877 496472903
    0x1e120f151807080d031a011d060708030c0706110a080c0f191d030102040e0c07020616060207200d15061a090a060201090209160c060c020c0f0901050a03 67
    0x11910403003031030300340101c0803110039580707500d51561904460040d003400320346041a00060b021903404561401d2105844034075612203000800c2c0da000e0b1a08000603400281046500006038206024601031904050110f446490600c2d1110817a400040114140541401aa507034254850b01e415840069004032035100c02451000c001c49028401202d04c1405042191526245d400702c8082112110042c4402c202200e42090500702c0c0706038010342c400c0381c084200044222810200400c44039102a20307003440c0c4001281d0f1042c80d8808041c003180e02a4002602c1d20030f05c41c250010f4044c120340a905034944412910005109075041400108148030303600400c0405203c1e90310202c024529401408201ca00e403144104040d03000c0108188144040000401c0d85441441080c40866000c1d05112103a280c81c00540310395905500c80741c0802c412031124a00140c0140100c4210100c1500201010700c1c54001304480310410000302d41c0111003400041181e030342c0704c4560f5003c4079000316000140e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 496475377 1250 496474127 496474141
    0xf0c18040f1406060406120b030a051c030b061215040603050d11011a0a06050f0705030f0d0e120d0b190e1b0a0f030c0e1e120f15 57
    0x4065504046a40203240c240c1e481c00d0850103801039445103041e410303003001c03603036450701000502e000314020319001448100740207026800591048050081c01001c0b110071090300d545179441d182d0201e00e829034481e403042c8004042074140c051407600c0349084940c1030030b041c0c4200c003111001c00e00074414544040c811005034035944859101e500075503000000c1e1828094801c40c042d18101d003180030310045628007503480e16031a01d840d40c540e0242200905c01804140303402c408403065000b280402d0440300c0204400000100100028181903e01d0030001e40c8411940f214602143c0c2d4507c03003a015500031a031083c00184da0901200e1104112020016000c4034030804521040055501201600220320340400c0351a128404103100e44400e26444010324031000621816002d281c4410300030a070540d1401c01d546000b508041c40c42d0a1500d403404222400b44d000034a6038540200100740c85401ca9010344d0181072141d0000080105503009100502c410245950b44548021805000030303280c0d0041410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 496476627 1250 496475377 496475407
    0x3051806070917012003100e0a150504140103080c01020903030c030d0c02070303020705010815040c030c020111070308010e0402060412050d09050d080318010b0d08030415050f0c 78
    0x10580150200c8045180c445005001642c2600403008a072580108a545440701401003089010424403091003080c40d600f541020394002800700c007980c0030220740100b180b0101e41150340c41a0600007000c20102d0382402e070f10441c2c6401d500264016428240030161070f600103e68181140c0e4003010307180e40c03012207090141c028060020041e0b8503000000e0b4141d054400003028104110b41110100040c1d901d550041e603880c05079110050168100103010445036000710803180d404041c04042c0c1c1444000580003400700e882440d42d100c0407aa80d01c12106010b1350910949a10304824600c603450582e41d48c0703024101800500c01d02c4203002204000900315218803060384d008020b89060b0b00b0b041c61041c070704552540c40c03c081140000708058400119464110b031100501c5401c0b0b90b40d149152562140400070700c105146145180d921004a20340c140c947e0f4801c03200041c000c4070340319124100307071070030356510001690740714901ca0034402441070401112600d07542011407812007940c0d40b84000741c0c00132 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 496477877 1250 496476627 496476661
    0x40b0a051519050d150605060403030f050334020706020c0a211211150708130c050307060203070b0a05041a131e06050601080c04060c05031b0312070c02060306010305 73
    0x504a800311542204001c209101010f0b506480ca0043c454544c80b402230000358040c1d07202c064001401c25510b06012402500107580201e9294020042d14003018031100704889040325050754940859405898103505000940141c049440036024480c00d0200117003d41046003d100038009401042c00c1c44085010301c82c4108a51002110800f8074807000044c2c0300301410442c9031500e01512003208440801011464031801c02616159070a442c2c0b200c1a405100c07920004440c4014251000b00c4c041d40c0801040000308a81d50041d5a03400321494244951440a01704800403400c06080c4000100812255003d5070107440303114501d84d0b6140907078070080a4071000034105c0e99182210f40d40b4000320001450b401405000280842d88075080119604a012203400040007070a20083c003400303108800c00c084450046080b203041070441d5040800e000c02c05204800da0341d00004450710181c5140c101c150303001c0301c90306182c0075100c040c3c2c010071003900c001000c20341050354400009030402c02081d0424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 496479127 1250 496477877 496477879
    0xc010606020c100c020105070b0a150b0a1107080c040c0909020f040609050306071205060117100302010e0a0e0106140d0e0a020f060f070f020411030906040b0a05151905 74
    0x22105a940d0316010b919940d65070035490041e03c030306912002c2d26000d404642c40c01541070390307042d1600040351550a0620303030141601455070344401021000701d070b040d0565070140c813200f0a1651350310312010000c0d19482c940c2400d0050ba8110034820400144086007030b07480b050058030b01055451003080c00722103072100c07038021100003480400d1400081e0170100c060030998442d40c8030070105540354410903585090459041700083c4101d03104004c00612a0803c9402c04410f041c1811040200e4480c200084001c03101800700c452013040130010b560307008580801030700382540c07031b0071141c0e09017000c445130300303505002d15800d2101103010081164500411242c1c10056072074100494a501d22400c0e841d242803040a901c01c1d02c100040c016281390140c1280c4008809518285c907104107581c075001204050207099a1055440d04600e0040515000851007040104d000c0d100600d09441c140a03030501c05440f43c82e1303291500c000c00042c03070149440b61152480854400500c228100202040518650852 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 496480377 1250 496479127 496479131
    0xe0910050a0807030302010f0e0307021504120308041b08030d0c090b04030b1501050a0c02041e0504050d080c13060c050a050d11011b08130c080615040b01090e07140c01 74
    0x50354078808510f10040d43c3c40b95000344242e10000042000307a400358401445c4a410802580c00180380000c80202080d540d42c0585080664071248809182880901a00480d115030100803c0000212440d4007100c0e05a0a5000c1c3c0d03421304071030681e01e000309600c20341d041d5524421015000d010b0801c8200408596210566958981c903040600400640d60440c28141c4000748041d158050008e071002c8002c90760b40c40440a40d00d40822001d04440c0828880900d079082298049100030b01400d0300c1503005c0c200400c1081180700c4020400e510007003008515801c240080b0a090f403500b01d619046503206d1a1240195045040140c100201e200e00208039110741c0f861503654070703000480a40a0788518000b040919280c42002c10f10520078903440000980c24030005a848250000c0e1056050003103c00304002c940329201d60346884400d8800071b001d610b100300c0380d068500c2c16010b03c1001000a1915000084c500280f038100514060090360501050442e94980d454000007608d03036170f007810002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 496481627 1250 496480377 496480379
    0x5061e160b01120326190e01020a030c1806090302041a03100f06050a03020a03121209030306050a0b160201030c1404140102060924040c030b0702010c18060e0910050a 73
    0x4840c950f0102001200451800310481d030380c40407442018640450b03004081d4403a0f0340e80000728000ea011080d899001c0540da441c40340d0042d02d09102411025a550f10005245081c0b0400034103140000707881040032103105001403041580c8219200202d0707505032404640e00b0180c858035040134190000854261146000d1100406811b80004607a071014001c00c020701500c94043c88030003062404084d4104801800410020b81d80c5180b1035a1860130349404484255170940030360030b45103600d00980010f40c90b60400c1c4643c0c83c000307116100a140c120286860b08030441d1040109007120340001e410f06035100c0c132000c4900e01a1160300140b10300403038459580d41d110b20074209c80102002e0154014400d0f00c000407001000000e070300088445408c541d5000c52651110107004090080040f2500701800c8400000a8103408040c0d0203030000760004039003018103203401090445d046010080b04003469100300441c980015004611072420b03125a0030b6035543c24405402103045500c0140c10107110310f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 496482877 1250 496481627 496481639
    0x16020c1507022d040e120d090515010602060c07021305070e06120a0608010b0901140609060c01050910020a0f030f0e0d02061902090907080709090f0903020705061e160b01 75
    0x94044081908620003e00d44031030700c0140411a107420384941c050354015105250400d8100e4083c042d07241c000075000c24000f0300355a0785401e0a1861140f03003603e42c441c000501540d5010b010483d40080500354440c00c0107841d80014041d0080f00340e0641d515075940010034a0b0b1482002100c24400c00070303165541e900c2c4105055016014106c5039100d0740c91030800081030341070042c0034103044800b006060228a90034940008006d400c00b1103074990203c0c0800503000309403505000b8000c8401904000601c0c0d1a1440c406424041010402498980304100c4d0401d00b42e044008038a192965250001d9040b1a507803009005018101c0c0c000362070701c201c140425501c0c0d800640e80d48901d51130021100c0c507035955440001640512602c180d4001080f0000480c294820400c160303220000303107000303001541d46010841c00c13200d064140d8a5440d0f00caa15400905804100c0c2c031004003803d40f0010310702a810b140019482030168120040342c000010381c01503101d0850008032429800070201c50407942e40c1c2c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 496484127 1250 496482877 496482919
    0x3020c0915031005010f0302060c1c08071b02060315010c1b23060403020909010b10110705090f060609010903120302030f1e04110a090e060a0516020c150702 69
    0x105103129224864501c05000d0044c014181241c068840d60050b0a0a5a08110707068000c5100c900341031040741c4002c980524005940d030140b44094540401504207000d0050612171194800d00c04d03030318500c05150041c0c0300d50342100d520840304542101032540100040300e4668100d0400f400007850101070700080949030440e0002c40d0301d0191070b49852a68010b43c0c0e49040c0c0d5035031005a02c80c009000030409418010541944444d4600c00050120041d0000448080800035050f001400d4403e004002090030004400a005c040300c00c80f00030b251102101c0c00c0301400420282c003602c2c0100e903065045c1d02031610f039005150b00c0035080300724a0707400c1002002034204483c0d903026010035002240315aa0588451401c0151041d05204c195035030752102e5540804070715600d900318504060004800070b00c3e104400c01c19442030003401c080d00b0681d050324252480904183c50840c0301001c0042e030281c0000c3e902e400c10100369181c040355540f45841041c0c502a020000c1e41000c048550013107010801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 496485377 1250 496484127 496484161
    0x9080c0f16061211070b13020a0501050930070e1603092a17150702030405030a0f1a07020a050709050105060a08060a09020c0f070905040c0308030403020c09 69
    0x1042103410107050241c01c01c102407a503105150214103214841410681d55802550a08503126450740c64482c0564441c3c117030f1042181c3c0e011520b0300c3c07002100110314103042044010442441d140c2d08003007544000905500a01083c459407000301251091545c0103441c01602c000464403e5030040e0307a0300c03810100320350011101040310300680d5846100d02802032080306082c53f0007000660000200340c121004100001e00035550b0135001600018241e00319043c2c401c000e85444000c0c102103014100d0100c2d13040c00c09880481550401d2101780840e40b4009180850207421031200c5055101c6401e05074420744481007042c0501010104000000303400042054010b481041125080303a41c0c0e00115048510a010b9968030000410030503a0407407140e541c4a4110710300034032014251741e660b2131003404ca07484108152130380d400001c1c00c5902100c0030b00c0018010841120b0600091a107641d42c0b2118401e80c0c00014006100800400d080c18420400204a00c0000d8452141814441002c160004039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 496486627 1250 496485377 496485403
    0xc010921080f0a02070b0a1d22020c1902101d0402070308041401200f04080a0c0e0a0b0108010303050d14010b0318010618110d050708040c060806101209080c 69
    0x48030000911b0f189500c084940455007540c40400202225042002980140781c0240c1d005c01e01c03010a0000f008106071100c0c40502444c0010703503c015481ca100d0800c554500e80d968056030802c0da6901503207480f002e45070146200e00e0800e803c803c1059900e5046480c8081c1c4c641c019101044050030190442042d6001c0c2d8042d1428501c40d401c0500c80f142641c80c10741400351100e10381c840c54504254071101805c1d9401040c0c15450500c6d4441c41028540548004150391901d681103041016549813003040c1c0d0000c0300790170180451401000083c10948040c400142040b4000490355403104c62640021210003101d04d510020b965100f106426540017940c400041a048003422038410005111f0700d412141d0300c50000c1c070714540a0030000020541d0501000b81c0c03142c00c000342280064180f188a229105070b45500e601400e00b0b040c80c2c45281c5950300004144903410003400559981c0403400c03494044546401d1010843c002440005000c180400601e00d02010850381c958010200340780003d411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 496487877 1250 496486627 496486633
    0xd0e0d080a0e0a0209190e070e09030708070b0c090d241503020f0d0803090607020d0c05030d05040503040b040b1903090f080a021f0b040e0c010921080f0a02 69
    0x980e02407120031100700424980203035120403120001401d0031905694406458004007000d50700514003041074030600550754036290070065040c00548680d0005640103034000e07000f5800c00f002959030806c607225502d00070b8001e641440c0000c481072a0402154418000070b080491040c1d581c1ca03100c3c0e5040c080d80d20041000c0200c41d1103015005407846002511034a640e0340041c640c1c81c5409100405400608850700303d2141358101d004100080000c50045a280006041c2c5150040700241030114840894040043c04e81c0000003003000003041e29203425a90030002901c0d162403801c51301d14862503102c400d0706c00c0701180c0010380da0100e60140070104070f4050002d0700380304001011011152030641c001c05c001000065100800c820710054000c080d2240121040301d00d803040030744c00c005110007003a607544d0f49514000341d15040ca0f0082c8031200300b10301c0052118030701100c0040d088907a280a2900b01c81e220b081c232100c405815000822099801c00d22003980c2d14140301c501c0340183d0011454801506c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 496489127 1250 496487877 496487881
    0x3031e090a0509090c0409020411030115080604111b07230406080f120a171006120e031e0d05010905010509010f12140c130509010e03040302060d020f0d0e0d08 70
    0xc1843d029252188a0342c502408040c502d00042100600d441c0e802a80c010f44d449100130a6140050f00440c040c100e98020595281d0b18501c0003040c101000305800d00490070306008801c00780e0a241561202908500408403241000400c5481c1103010341c0070000c058444108003000c1d0440c0540c6800c40c101c299001d109507501c0719465540c0f109007100108080c0d106004040d041c60301c10000d003004003890301c4c0ca4000d4020a19a0450928043c0c9504441c203e0101d4208a0300340c200d01c0d9864100202c0c0b80501c5001201d40c001d036101e00900103a10401100102d007600000414411298040290f1000300003135619001c035500285000d0142074021b815600000c114460308103c11070865410440b5004600000d0f0b4524840182d0704051081900c54505000d00f2641c40e1240d031241c1c5403d80d40300107194507140340c0d481e094032079051500c58580c10810003440540c440d002110300c05125800003681c0c4403640c1d841004244030b04000c1c550001d2a0206482c0400b8011412041030101703561484426 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 496490377 1250 496489127 496489129
    0xb0a020903100b30010204030501020307110a0c0506031f080a051603050303060103110417060603101e09051f0209011d010813060b03030f070b0108031204060b03031e090a05 76
    0x3e800d60701d00c07154000d00c00300740740c44c02c41280421801140006051080f100c04000041800c2e600a40c2007221241d4020040042c800e41c0005468154800308004003402c910355200c010340f0300039a00990303016100000008981601c10b84042c402040d110007005809603039105055240c034100081210740c1c1c01541c10380164011540d44c140c050f40c1c1c00c034000d985036803a044010f4004003032100320701003200070074000000c0e044450380030020144404800340556280c0303001010f0501000c1450388880c47d10380314030102180040c203138021400e880044001000303042820f040d45445281d00a00740400c5481c6070305090401980c0103400c2c4d50000f80c07207200001264482200c0245016500b070380c0020a08000600351600c008101f00c0d0303481c010440080e01c4240e0380d020904641c00383c101c42011040c001144000c100f002411280100b10036405181044032424800706000c2001c4c0019001c2038039104240b030700303580c2801128841c0c80d51901d03d4082c0c1c0011b0300400d0145c0c10066019115101d070080004039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 496491627 1250 496490377 496490381
    0x12030403030914180a02090103060510050a030e210c0709050405030c01200904020d1113080c03010b010c1202120a090e06102102070611040f12200303070b0a02090310 73
    0x3a60211340a00fa0843c1c0e07500f00114025000040442e04150b121040050742e40c451010f0350030241c05e242d441d6503403183d0115000e810b81c0c0032039009103103e0780001301c961105403d008004c0c4c0c01c1c5440c0c0780002d503107440c0d440f0010b15040a541210001c03070300d0202804100b18000009203403d4030341d10024040c0a01543c622440c000b101040c048000200b0800862a490194002c0550340390842c00012000301c00d02ca01c1940341c0000c0380114414039158024041c010f01006141104030b801c4009102013906000000c0103031100203002081100009900d010300ca0081c02840c0b41301ca03543d2605074840d040c001008028009034441c0402c0c5001300710209607641043e02402503182c0c1103850f24842821422500e5a50004170140141581c0e828008040007440038011002041c0000890340e840e9803c050460212042e20b90200b08140c2840981c000004c3c02c03181f00791505088850540615214140070a045110f034100041850f14400200081c0f031600394013501010000307500302c40c046081d010410b02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 496492877 1250 496491627 496491649
    0x316180e011508070c0b09150c030a06050a1406090a170d0305070e03120d141f0e040c050603130506040309030c050a0501050403080f0405030d0804030e010503150f12030403030914 79
    0x1a06881700d210204e4402030071982c00034104411102c0038074000c4044241c1d610b003511496441d05000042c001c141245000317030b030b000d098200c50705120b03585130003182c584401021881354007032030000c107a03c80c00f5600c1c210a60002c0c024680e1b1340540c0c2545130003180e2a90117030400d03180800e01d0040422001ca00c06d8551425020015000705004440d102c03404109410007a28413581d030b9217880d0050a507092010b006402905a200c540d4201c0707031613254141400005420030181c0082c000e01b040007046e061803142c0304031402554040e03983e498690b4094108142d2201c054000d03c11f40040c002056446101c1c44100e034003c0b0075944101d52290204100001240300d400d000401c1400144003052092004085040000400711311300b40c0d9441c00b180c1003807011602200820340240410050582141c000100c1d410309182c039034a54035003030060040d038248005045004590307251600482d80c448d04070b46804607034036a0850b41c84560341c0c84c000788041060700680c3e15240300520180d1007070401322a460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 496494127 1250 496492877 496492891
    0x180a02071a07080a05060f030708060105090f061e2b120201111218060403020d020c03030405060d0e071a0702010e040e03030708090c06030c180f01050316180e011508 73
    0x161030b86071070304400060b22000c1c02055200d164124147c0c2155400c00080009107901d601900447d0f15200c01c0252030b400040070300500754074410030024180d0f17800000c0380d5102200184508018503601c045024250302c0c152102103903038444103080e01c00c140fa00404402d540f094003400c200c0c2c200b0794003c0317003690b00000d9150129041844100d076491105401c46034003032026080b00c1789407054883e604d403400d101a00d090b00542c004490409885a0506c050000300105400644c64940740c040420039603c2841030486071255202c40200d4074400621161000f001000240c44090303082050901a030781c002803089020031580030f030301800d0b410076000300a080b000f402d001d9415907030350030313025900769a004004140d1401141c1c001d13132040d52850099401b4040c107490750ba03111070340c01d40d100c01c1c0280c1149000744a0102c1c0f141000260380e005045075071004100c400390080070b0104505458520004503040f9803c0309816012400180f480c01c40d83c12038214110f409400b00300081d0a8504c10030507a540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 496495377 1250 496494127 496494137
    0x90c1806010e030a151e05190f0f110406030c0201110d05060310091505070509030604030e0f150c210726030703140a0608030315180a02071a07 63
    0x165150701a04480b080303242c002d410b85103001c0301952039400c90203c0080001e5001e81d0b0700071913101c00250502e41030401c080d619080259003001a03040108103100d850b000c02d221748860342c100c222000368006102b1074030300740010320038a421902c400321260084c1c0034000c0000c3c80c0a4010100728414051541302c4035188801d286807035412190000900001440d40d605442000081c038400d10b020f22421085c10300400c10780d543c0000f50b40210041d031340041d010204101e01403010f05115940803136440e4125600d070401000010f0014003082c90500b0b5220480d0713020a01210f0003024180f080014607034064020b056540450803d0445002e8201c4244500c203d2a814041040018103100821044c264200110010503d030141c0408003030b4030490b40240001d490b096100303015500c01c00ba1a810861186d4140728580c03c200207980d0340d000042c80e405000c44404000326450302d404080940100f82a1101d40031441c0c111031403006580701041c2240c3d1070120301d02e00f510058119400038041d030b12a54070303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 496496627 1250 496495377 496495381
    0x7050f16030302071a010f05041112060a1e09050708010308040e06030114010b090a090506011215050a03050d0f030b010804030503071817061003240609060e090c18 72
    0x388100d50142002281455820440786012031010040e0040d6182181840f040641c1085004283e0f88182d50040b030140703041c03050307050070b900c261700a441041132100c4d08196240d1b5000c000a02d00d80f104c1d8000c04003000c00460050094005c0e0303c8030b4056078202e4038144516203c0d0002100c84200c2440040d118040c14441030100c0c1100d01080d80c3c20040041c00407410b0011403040d0f000800d02030b4444c21082c1c07000070b5030b00994200030780c0c06002802d001d03400b0409031400b040041c1c40a540b8640c071880180e50b80100d0040d04d10045010030240c8000340040d03270503944030728000740d44500290035200442c1c4a070605101c254424041c07400d03d200180d40300c440c1c98403103940c183d03099007010b41854103001e4420f001d40c2d10707410500701103001885000351007070a0701d8256000c1400d000d00035010100c2e107070078984284040b50410741907542d00f020000f0010030544003020b01000800198101d0005203090240014100c4940705446004a5902c8103680e80042c1d14420401041628041c001510841d480 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 496497877 1250 496496627 496496647
    0x7031b030503191e0209040b0429010912140f0a030c150b040c0203090109051203090d081c1a0301020705060109050a0906141e010806040609030c020d050a03030507050f 74
    0x254108818503160f408180503100c0f84045181c0b0044200403240240c0c0800c11b501c040c40c180c000c8401004043d502003103065005180680c07440c4c0c3d032a007851504c09120920f401d90b43d2082c410f0200421603030010980360000f5280203038a603407454241c01800e1040000c1c03000700c1c14010940c0e243e0540d160f2210010b07000c2c20354650404044420004000e80e42c0c03001114116161402003031025440c0d6409136903210a04000584010656003000380605000b95088511000002c1200c10444040306d01b00148000d0703180001c00c900c0340a9000721b203030140c0c088801d00c0c5130343c2c0e4100200185407600301354a040790090038103080303004e0004098003a9104000401c840c080550006030000d4002c28041040d0591f901e4480584075100803009440c0f44001c10026455490900e981030419490f110201c42e5240ca80305a548400280000d404c00750345140e10000c140c01a0160000c1c03d5000d09120360160a60030421340340d80c209101503001c80d050400007010144144210390364a000403115504002c602d003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 496499127 1250 496497877 496497901
    0x1e0506060c19020a0803070318060203160b340e0405070f08100801020a05030a0507050408120a0c0c08010f0506121b181006270504020d110f07031b030503 68
    0x2c03034207a8000c002500007045109052008050550180d110f82005000d0346444a82c442c4c25a03100b6030071500288a4242244090800000069009000383c00940c880c804100320f0081c48004400d07000084028801e01802c0c00c60f01e48a41c080191a01c1e48000c2240040c402903135811541032001030b4000c0000a04140146440c0da00228070b2450f0100503529442d0031800ca900400c80d040100301c0c040f0800c200c85556009030359000f130192411034105483c0c516582d40e43c207071032010030401c3c0502041d6888014491481031074981d402c1880120340c20343d40c4030503500800c502c4030100402424000042c1450410750055000700f0b40b00401401c0c1d5800c81000c880800302c5640079245c0c402c024003400200100140000d030301801c1303400c507051900d510b420406484180600a8507900b10b14005118030740780a010020740031100103072005a42c2e194405001d0006000005500181440c0450207141e210164000380c54414401d8540034440d0144048a2183d0340041c0c900a00180c0100300181500c5119 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 496500377 1250 496499127 496499173
    0x40b0a020703091a070c05190303050f0c100e011409031902010f09060606120509030904020a0c060608030d0e030306100e03031204031806110d030c0c061e0506060c 72
    0x40d240c080394440c0c940c3c0141340f5043c610b00700c03045a0100461104140b21200003403c00070401201c02c564403030360414084030360300d400384000740a004011501c11100d02c6014129040d54500e50182c41d0082c0124054400a1007900200304096180845000b040307524003080030700070009100218217040c0d41c41010320282d10140c1500701155210008954003002d60f00860a0481c4109008a60541016002070203420610340f2a03010505200501000ca034004c0300301c0e40c608806403409030b40c0b2603110030180d60030b1202c0480140001c0c50100002148107020025140008046809020000781e203801640c1c1ca010a070340b00e070341c005003c0c0e0040100314080d40300f42581d030601405490500e5080c00e0301030341c40e0804407000d901090801c10803c10701d805a4102802606203410303c01aa0440312480070342e14503070703440031405050b500c10200310300f540074505030a80070707500c410103000542c0d90100c660740c510034681c4008890b42c2002c0100e942840c00c0415548a180080c0090a4000c070000c82c4210304409 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 496501627 1250 496500377 496500383
    0x140108060a0f08160803130515070b011d060d08030103060c05091305060a05011107260d090801110703020d0e030f010e0a110d2402070206180a090b15030405010e011b03050f040b0a0207 81
    0x10410ad43c00540b0b8802141d00034085c0c2541e440003490710303d11280750054001e220f42d01c44c654103040e4000159013002668103580c0c020381c0c0011100c40c143c00944040c820a0080c81e80548504246014008550440d9214030407e441020181e0f94603c0151146040e216558040d0303000f8910600c286101046002c44041a403c1c0000c40c81ea00e030701c3c0355070405141c014030b080000c0500b07405000c414003d00600c220f0340d030854550f51405009441c000c0d250217030540b2200c10001881800b07043d81ea4104412043c0600c03920007000071098280d4095540d0500b1340c0120748450b140401b1840d01d180c41d1640c140600d40141a03644148140701c0d001c050a10f8603224080c00c56424405140580c48140c05442d90a07000044504618034840130040c044210342c0c0002406414007004403107603142c2400350814041161840385c2c803503c80b4540540908240008425550320b0b0041075030b00070090301a424070b490b000361000c0110f038a409698130040c0204980103030160780400c01259403082d050f80141680c1f40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 496502877 1250 496501627 496501669
    0x51c020d0b10050406020c010804110904151a19061704030c0501060306090212011e0b0103020405030d020610060206070e0d03050d060b040816140108060a0f081608031305 75
    0x218180014010488100440c0e00081d00483c0c14081741e501000304500b104401d08011406240c41c0d81d85a0320300310303090312450080e18004041020401c80308041041c40480c4c1c0303014070403000c1c144000e03031045010b46201403054007180450100c050800c012003054400942d80d690800e050a0701c4417520810152040301004450300c2d501e00441c1c000c0c85848041c44c82000d0214030107206004020b0f0b1000211046a01030f45011620340401c2884d0341a626090020040440d01450a400580c000c0c0035560086405000b232485c9026102d501207410780c8210100250080703400c0d15039a080b699268215003800c041b0300c00c0c6c00003140314039056403075403006446481e00f20715050f09410f03035100781d07121640003607548030000c14240042c075814800307040001d600031760500110b85042507000c0c441400200280c14400004003140b0913480744c0c1c52450203090745515075807100d5540c445441d519040c0000c00340d9406008000450360640110031154021012021800001d04000800080501903000e07088901 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 496504127 1250 496502877 496502891
    0xc030602031009050c09010f140c060a0603140d02190f1e050f0c0906150f0c060601090905010e040605150301090305070605070503010614090105070803090a05010c051c020d 76
    0x21500d0004612a080b008400c00d40d507031508a1000036548050804000058140b06103405039034002c590400c0600302c0e1520786c04600e0107403a4040b0301d2290982c0304440d801a0802c001034201107412076400c5901c100d00301d01d00700458641964072000740940420050700a0b8000000c1034410704a458900f40c003030860124000e81c20340e11040c007858501360100c0e051030072040c0c3c10240042071118408600c1c0040c00b41410340003960019a5400000345490b220b0400032600352494082007003610300d03038100c90300807903034450b09050455510700e802c41d42e144c0010800da1002c20881018043c0301e04956030101d800d00151159a11030026240090101c41c80b0b030012040400541d400b4020000241c3c0207031600b0740d54110505260081e110000c012006100c81080100481d43c8d011116140001d044049a9210344411004849921902c030014040c000c002c014010038450104085102500c181c0007000000b000741001e642c6801151922400349d0741006403203507030301c0241e002003000000b0024002458 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 496505377 1250 496504127 496504133
    0xd030627020d06090e0609031309050c040803030709030c2102120a05061509010906060e12030705161809081803010905120a0906080421180315290d0c03 67
    0x81e0f4035540411201034031111202c1c81c5180505c442a000603000c4043c51030020380001180e0140c0c2c01d8450082016500d00020f040001c0d12002e641c05007107610290703592410107450042c84152240000d590454050900142104401c40b0340310324080c403580c0c2c0b90003800e019000c10281e203203103074660301e940d0190104940004505200b01440354441460381c441c001da8800a008003a08142c001e440d5407480c0110501100760070080c00042000100c0c1d05c00c14081000000506502034250300070701900c074902202c0200750b211140e24003941c4c1140c84000000c1d0300c1d00510800d4804229000c1c1c90312070100210311000340424040d501c5603601130004500200c0c15138900f40780c551095a940c20022010030410007840e40241110000c2c03809180c80441c074200f1351900d17181c810100500c160100303000c0c128101d80074010244042c00c07070080c00c0742e002c981355a828003056140f0b8261002521520301120b001c9040c108480d10303006007c0409404c500c40c8045400d01c008440c10420a40e064840c0765000400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 496506627 1250 496505377 496505381
    0x1e0d050a0512040c060e0102010504021e0d080a200105071202090f030601090e010506030f06010e1504020d0c090f030c0302060c010b12010c02011b02030d15080d0c050d030627020d 79
    0x40c62103480801d4005281c001c2c01451b54414006150469040400b848003580c1e9101c0c045c8085441034140c44050344a0301d00140d04588800c50080c0b050700b010905032030b665002002d43c2c40c400000d0310300600001000c5001343c221031048500e140403c0c00000e80150b035650f00d5001d0130607984003410341c4000031258000607142c01d00c00d0b4403403d034031920350750b908101c0300080c01a5078101c0d50690050160790320001c0b090381c9891050044103c1c500102000a50380705c1c440c015505c41e01401f520456462040e4034851000d0b04125000701c000c226000b500042000c0c2203844602101c3d0401c2603000c0260960342008a0ba900c010203985a41d92030b0f035108640340d038441c503403901c418143c01d000040b004c10004002e4203482d9106602400007031021208250240c000c0212003030602503901c009842504034a0362541000c9640014440c1d01c603030f40654468603003050182003882d0207003003114150706089008400740c42040c00f4441c18800074104220005c5148030351a40e4038042c0341000f606000307441d264501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 496507877 1250 496506627 496506631
    0x705100c090f1404140c1204030504090903320708071109010b0304060605030622020102150a09031d06071736090c042d0303020f1e0d050a0512 63
    0x580c116002d10205444e091103002c0803018296100da00740c1c500100c00e260a40520110103042000000008040503c42c5003280d0107043d01c2c40c020083c100f8a4180189900140702c0714a400d0100c4000d01c6e809074812661030f00d0406c0c2004c038418a0050142e56030380868210b50000c461103450880c1102840c0d0301c84407007a01134205403507001d480b0714041c01d040042d00e50591041d0301a0300b080c030500008801000307100b01c00510035205101c0c1e8042610040b442c0c41c450088110004000c1d0045c420040b013560007500c036050081c0e980030001c0400c4034a030240d008250700e0b003540c800d004100d0b600004668801001e010400d00d4809030411148403800d896000032554583c2d2030650911700e11302080010b0600b20400d0406464513280c2c1d14042e211291184198025078803243d00d948039184030110780300040140c800e103000c180c1d42c0b06a90391030065034645561491a103a4000c695031800300081800d030694640180c1c8000b86510205450283c03219442044d00c00208041040b0700e40700b021480209034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 496509127 1250 496507877 496507889
    0x5010501080c011e0c020405130b040b1f0803070b1e04050114010602190b0c1e04050a24030213120b010819080315011803030c170705100c090f 63
    0xc8501d80700380c4001404c0d407100c855200c05180c21403200c015055880041e11500f140d05030340004054990101031015038806150061550900204000c00c2150b01d0700c2d154010100100314400c01c802110000c58540860f0040540070b90040c402c40c00494100e2004903000580380c656694101880502c824000340112001d5072560b4646042d03400c17005025629600510300ba1015004810080984007040884140040d04560b00131003c03c0594030782d0421a1080306115564600640b110a410701d25508248901c62199008107000554040c0d210144d42c84480101c00401c4074000c030341010ba000350861014480c113840706401c003090326442e50560000490103455040215071421a40a10f0106002c444107442d414240b5040c00150004058a4210203024090f2a4030002c4200495001201c1e12454040100807000041410781100855100c10300035000c3e840d4007900d500c9601d140f44640f044c0200703150720941030304c00c00e442141d2281450a01d11700d84061215501c0204801000f2170750060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 496510377 1250 496509127 496509133
    0x3051005040f0f08130b03010b0a0c0204020c0d0e030d0c02090a050a090b040305070b09210d020f1204290106030c021c110c0a030209011e03022106090610061b0501050108 75
    0x5c2e0000010001013100a080c2c01c00118034560416100d001796020b03900c0320382c0502c00314416030f0045640f280c042d1600c10340c0c00e404a0741e002e03514510082a844076001410301038002c03001248034440c46012940c0c083e58003e482002c0f15282d80000500030040140340c40c8903160364569120004402c8240c1038001c0f4000d955580e29000207081100d031214001d0900422075005c41c0c901400c2c140550782d07100558038a0000152642900085540039100d1692451850800015901e544240540c0c81c6e44c050307401106030003080310000401b821401c0030b040120301440780324001049440e1003a007085803650140d10560f466450020240004950310301d0200c004143c903c00d490b19614010001524a2402219544500d070300d1600411180201801010202000e0f08510300728120490f4015004503400303000c2d42929020340d14080000c03a003000c0e001106001da200490b0000b08002502401085610700103690345262100690f825000c0f010380314502d00c03001d258080411800e21405009002032006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 496511627 1250 496510377 496510387
    0x120f0218040b13051f06050603090703050d03050f0c030403020a050d0e0411031905062b020f0105030609190905161401050a170c0c0105130201080108010603051005040f0f08 76
    0x415651200b00034011000311100c00075000c0807410026040204026650100b030000e0030056103540501340c1c54024030740100d030000600c8441000003a54404a9000b441911800b00d50008100d058032020b8a25000b41c82c50800424050004980156003103031080c0100c400d078900326541c150a1020310203481c40411900400301c0c034107090500500500c00101007449246290011848907408403101e140f55245070350b20009240360b21603001d030076220408000007805403103020050520380c040c00074040b809410403e08203800703540500b043c0d078007d040042c0118856070b180412400c0d40e514017500c0084503610b9100768030100300203100f4412a18400e0080620070750601401180d504c40001000d81001010050f030203981d5071010500d040c82c01814020f14080c0c4400b0f80c004039038000c01b4003506080d460101070100204810071807900a52003a02d071084507aa0345d641203400c0703882e10310020b409a0000c6806200f1440e603980003651240c07040c000b28000f03000f1525031140801d00740700122074500e40001c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 496512877 1250 496511627 496511633
    0x3141603080406051e040b04050a0b0c0418020304020d240f0203150f011d150d0b010e0111031c020421060f060f05121c091e060504120f021804 63
    0x2a60364030001c8070102d17081440400640d050388010042c0045d00c0c50001a010604200013401100755840d08854065020b0070b051f03200c401c0303d0348184500e240385001d4021404040e9440d000b60707071140e9001440e40009140341d480741c2103200980e06490403001f41c5480c8042c00e007205440f40050340417648000685925207001c40c26200c03c21070500f94414444003500010381daa00c11540c0a550b0071101d50744400c14242000301e5006404d80903001c045410100f20003c0b2000c20381d10900760b201090341c444200b04a80c42c01516000100c0015030600d400c01c000c001030f01c502d101210801584009001440e065030386051210801d90300801181c1030251811400a22125002e01051004214020050145018981141e42c01d80d445114007851141c6110118064244907e82100601114103090400c4501c801040c0d06014001e0440f481000c01048900c407500a103080d0541e911915a1031074142070103403010061408880468080c2c040000400050311807141c400380100d000040e456031420285 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 496514127 1250 496512877 496512881
    0x201060807050d0209010b0703030603080a030c032003360616031e181a091615050913020c0106060e1e09060402070b010308040801060b03011203141603080406 70
    0x160115200d00010f80000015039100d100345811141d07114040d80d600e103400d00d41075001e400b50343c0c405040024041581000c96030150060244100d82d84c0e0104081c0021009825254141941d4441104000c3c00012a0003048002c03d20000000d6031808000c400f42520003c1c0d084103044440100350401e2061140d4217540305071006254020382003d0064040a6046400c1306800881c4000d103d078030b80d0b0710003c0e031550703c1c0741e520780498224080800c0b01c3d1480c16896010b00c0141d4100c3c4032480340030300c1c00030484210081e610a072400d28425400e5824414001c844980104240e0780d402200001002110f051a20041c101015450008584945407210240100142c0034030b0b14050900004031040321440565481c803403203000c035001c041645410300454000c1c0504040100014103a00020043c40340c0780010703108072071040009011107034662810a4a9010038426110900121091500024061040300766150900640d00e81001c40f4039641440456054030281e0100b00c0a50502c003c0c08058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 496515377 1250 496514127 496514129
    0xf010219020d050a0503070e090a0b100c0201020a060908042403060f031e0c0801140609070302070209150103020f04151d1c020303090402030118050609040c1203030605100201060807 80
    0x9030001d004075404009003c3c015109014030b0400700100000043c00c07507070249100054841d0081e0229503070385400c1d82030308010409054513911400440b52048101341c403400303040e140e07141e040c0c0c0506280c150540d40e640140119100c00c0b149030b00103210200d0380d90700b5950000c0810600000341044001f1140c1c0c0901115030310b801102600c452440305102103034162660044100c2d01d404100018180c2e41401d000c50b00154210440075403e01e400d42481034064135178240034940495824903d0b40300c0f50f1046c0c003240300e01c0328025080b1020304001981d07000c0c204201200b01d54107041c05460040c440c00f0791141544650803050402103000d00041200c0d910003d891580e03a4407203403006034807442c04002000781c0260001104030b40501188002151024000c0e81e040b0304e800b60003951203584a484554450101c580400030380c5181000181c1d00c0c1c40c0402859025507040040744a54a0034400c030031b605007103122016024940c6441c0f0010b119116410707040501c4410b907000080c84c50402000d607080c0011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 496516627 1250 496515377 496515427
    0x3010f050a050a06050c0f07090b01090914061509090f01031e030806061c0606080f090a0210030b0402211807080d03021303050a080d0605010503040b0412110f0102 72
    0x41d0100c2808181c03501c0c5125410382d80306041c00e64a88904c03251141c0340a9000f0b03005e031a03a000d0200c0020307001001d030f0054228082d098071402003213900d030402c5208075002c04001ca140031040102003040d03820640c5208400b189602c0340c1c1d9203012200c202141000c481600c0c0d02c0c0005e40c01100400600070b22100040e1035441c4092a0b42000c0c800d620300400c0c160300039042030710508002070601280b035501d0b54942d41200c40c0e0082807004035540c02024001c01c004403000341c0c4d2140c0f17080000302041d07004210b050226900508e050168000c821b401c0700100602844190010390800c80c400d00322149401c0070001003210f03502c49003507150180c45d003604841d0100c040c810356408240305024901010405202c41c030840c0c680180c5910300b4080c2076401070302039800640703180510050401030140c0e00d0b0082151404070301c410b121040c0d4440044071144001c540c0600011213020100c0c00180303203a02900603400c15403030030f90f8560760030086041c10b2139407059034400d00703030f42c0055003400e0b25401d0710804a080b11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 496517877 1250 496516627 496516639
    0x8040e190903170c0c0f010e010606050c03120c04030209091c03180b060607080d0b0307060c08220b0f090307090b18040501020d09150e0303060d0602031b0307020303010f05 76
    0x1442e54014040041c0b940701c03481c201030840005095510100c043d00c040b0b1020800300c50040d60031140d514000c1681102d5440b040d42841c074042080303400340003124048414400254a010a506015148440007500b1007031404801c1100001603030322708403a075014601d81c0c00a400300b40d444a107420303c5990b0920281d03061504060032580040e18481c00003540340e401070003005090341d4003000070b004c0344550301d40100410400b0030498280065680b100d5000c501c140e04450501d900c94109844440a11030000c0c00310404100444d00c1c00051000180d00f02d1003070114109031601c1d04409101d40c3c00503505d180d08002d01044130a054982004014010408140d041017040c0a2401240d00c1092480c04e1903129450b01000c030f030800c507003581203ea240200c100100600300e014901410030460301c040d054504c600f8844040c1e00504040226401900c0003461300400d40e0895488101079040280078100481d840b0b4020700c07104025100441c8035190340d901035941c0e9810842200c070104081d0b0040c1d40a54 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 496519127 1250 496517877 496517891
    0xc021008270a1719020609150c0f1e0a02010c0305060a061e050d0903110f070825050307030b0f16020a082208030a140306060a050703050708040e19 65
    0x1403804615030b2440c503008010541c0741d10301d41580c448280700e1140a44982c98144512005041c1d010410601079100c2105071445503024400c410300d0280113665108500200304914480c01260400031b04034160301042c40000800300c001d007046c19800c50a80c07100941d441e081200c8409a1510650790711a9080341d44900680c00d2080040c440c0c1121540c45101d2001d1100c0301d4041401030b8141c41d07000341c2ea59410702c004001403500604d94070403101d41ca01c00384901c14210388030040c0420b4480581d92800018225111509000c100f03c00c1990020f000c038034819100030460781c809001c90000386006004107400380c10001745680401400a0800d1a041e01da21803421104d13a000c0341c61100c40d03810110325500c03881804040e8002c140c10001c6c1084c1480070101c0000c01404c0803000d061880802d88488a0030a04a09054118441201c0007980240200040382e100c5000d40c0140100d68042c0c6465403d11010341d403481d00b03a501c40e41000318080b40769810001c4000300040f0440c45030502810510981c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 496520377 1250 496519127 496519201
    0x31b08091c0e0a060228020d1b0501121404080901110114040210020703080f13081005041103070303050702041a061c0c050901120c1b0305090f01080105130203070c021008 75
    0x42a480454020740c0d128020301c103002c7d9540c2201c4099000d17080341012a00421803c81405154440d10032140880c80c11070b113045550090380708011030551107065445a0707503a50781d00d4520540c032450226051064020040030604401d01c1001d20741802000e50300c405040c5401006128003c5e080350700215400043c041c000901182c0aa8001400061429444082c0760380c8541c901c048a1b0030a207994880e003040308500e40a90f800160003180102c40ca2111041e4280070305d03454022030700002c0d0200f801001001c005062a0303200e15110904101980d4030360ae11080007444a6006d01040b00e0074201601c03440746000380c644039810031a2002d0600c00e141210810018020f00030807140d404800b075032802040710250042c4040f1441c500345d240c001170101014903001c0c1594111101150043d001c03441d0f0481954040d10046050b1400144840304001c03581c10b07084042d5000811640800450031402c0700103845140c821030a03000c081c0c40c1d42215160480383d19040600c0041d0106800c0b11124030f100c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 496521627 1250 496520377 496520413
    0xa0504060609060e010909230109110a0e03030c0f03070b0a060e0711070504020d020408060a02030f040b180303010e070e010e0109090f200316031b08091c0e0a0602 72
    0x2180c04501380070302c2075911503006840d01503081e03025034180c900f0000c404446c1c0080840500502486144041d4140d03201c003202e204441c0340300141d0304400402c000ca0359500f40108800e820002c402000c1324604045a10a20f040c0001141c12445513400171840004002c0b140041950108250104001013031500c82d5404241030007800400600000c3c2c2c0049451000c1406244054071020700199560003682d0310b024001d40c01132181704c08034041c000115442102600849000701160001c00c0623b4030350f0b8440b900348010140104095000c0b209920900d100d00f403001c0e6000b0700900c100c1030214a807403103020f0151180707180e440c2e0400080010b402800d0303130010714840030341d018081c000036003181400c41e403030060886503034401031a504840908110410344008610400060150410059501c2400c0c0d082c1d0712031450240703401d070441d100e10618500c91010554084803000455021090741c3c011110180103180c0d01c1400a51080641481820450b4040d4010003c0b440101800e140100c22441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 496522877 1250 496521627 496521629
    0x50a05040b0d050a321203070201090c06020c1e0d3e0103060801050f041b080a0f03030b0306010b0f0901050d0c021e0d05040b0f0c0f0c09010b09090f04020105160c03020a0504060609 80
    0x2071b0f42c01003c004510300c0740c0b01358865441a648094080b40080c1c0b02c0d5006941c8103090b4450071311460041c06420300c400d80c0c0c90703001c04441a001e8081e071401d0b4134540e101d2010342c1c500c0000c3c6c81c19010850f554030000c18425003c0c074168282030408407108400e080018103690039600200056070511040c40080b4500409080e0301640040c6103c44440f0318041b00c10141c0d14540c400d03030313a03403084c0f01c42141440b10b800c400c01e40c110f100351010410000c1c140c06050711108240b18041414006105034041007a440c070007080341040c145402407030003007080c0650044804141c0303410b0042e0b0100c07207150352030100c0c2c60206407200c142000610a0f01c554080091180c401d41c0950040b0600101d00c401d158115007054401032020b640a5811001d42c4101c0541e40d0f02c0c40f00c050901c1842c440c400001c443c0d2102044801d184e4019280c2401540e850014001900c0040c108a0400004000c1e0064009112000508092046200030b1007646140104001480d003a00064422403800104001071904549100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 496524127 1250 496522877 496522903
    0x2030702090c120c0f2b0c0203092815020307060203040f110402180103090c050d030c0506070c1a0603100f0b12010e0a0b1b0d0501050118050a05040b0d050a32 70
    0x5400c1099040207500d114000320106c80c620f400c0801c0311510f160044043d25216405580d50484c0211101900c0d0241da2200142001c11030f01500600910f03103122080304860600d80101c03844c10145503100c6049a00031507050340c0e800079a854000401c024220f115a2800d0f04460560070241490003101c880300c8a0f034000c2c1d0516641e61075000401c00310000503002800c00806d0210024400d003000307015000b041000300ca0500a40300017910342802400e40020207500701ca000c404000000084040000015000355414401c038113801d000c1526501505082030081140865801c0307140341070240340c5219004142e034a074140080038840c0400042c41d209015000242860641c807074040e4103c0030042d03005142000c2134000b90300070b00400e480e0001e6048803030a99414109500c0c1c4401c41c0c0d9241100d0046550103000c0c001c04108600e0103802c440443c40d001403400c0d0803400c0aa5403d4542013001504881d1030741c2e90107502c85580502441c0806101e00f130307100d0740420049254856114003440e1600c3c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 496525377 1250 496524127 496524157
    0x50d08071e05102702130924050108100f0e0609010618060302130c12090b010614070b070815060c0703020a0b0c0a0312020f12040b010515031602030702090c120c0f 72
    0x803c1903503684444150211b18a180c00c0111300020f0800e852280719070000c4070310310b07500c2d950705034142c1c8950303c5840c0c100c1e080e1401802c45110f8070141c0074060803a00c186100c00da62240307010301c280c5c50240310541c000c0c10498000981d052404102803590007030701945070b150b54600b6a0070000750b115070b0703501c0c0c9148104030720000b1031001c20502654440e401f07030030300c3c1000b62400641004010404440038140e0380340d5103540806098000303110300c1900c180b0034000c1130005d0f020040f90849004006003508010b40c40f00005e407828205000c600e0035040713903410366a5075008040800039810000c00c203801400f14450b0707a40ca0282003016880d502c43c070a0a0040800450070038030202610954151080410300d81403440ea0744928122503d00c6103004e98042c1c480030011000040c0910300702c203040d010080501501d40c1165981c401c652250200403113a44191f0004224000059a079442400d12525142c400039071582e990070001a0307080d40041c040c80c0d0f52001002440030b010004800c0e01d4100040c6405 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 496526627 1250 496525377 496525451
    0x20405030a060209011103030103060e1b0d030c11030d02010501030b0105040506060f211f1401020a1b0506030f0f072303060f090108030903010b0d0c050d08071e0510 73
    0x100e0308411604100d0b01c1b103004c040001720400c00c09810405420451800311011514942c00d111580c1c2c81e5105126440002409402c1c0082d000358018500c10340901080030907012590003003400c18007440d11a5005175510401842005980c01101c2d0140c50300350760400c46440c000006c00d080d4402c1c804010010240400d03440d01800400f603ca45418181d840301c041d040c10060103070f20701188075102410320101030038000f05030707082000050280307914140e005103e2039100d40c031110000074100060b9450099550360204103600c5003401140568400351205189251000200c0c844103005040da40c100070105d440b40410383c404c200112410201e1b81e140555070b444003000140f040f9804004d45400904450001602034404005014621000d40003444031b440344004202c40111094001031810280e00002d0149080c910080c80328070f48501c0768286042100d031501d0812008550301d40d02401e410710a6038040000a00c2801d0001e4004101400b0112f0100006450114000c1017021403070a1984 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 496527877 1250 496526627 496526629
    0x1203140a2c071211040f0903050d090c050d050319050c100c030902150a090b0f07030507050a0f050c0f010c0b06041806051314030f03010519170607030f020405030a060209 75
    0x1c0302000500d81064101400019454104505426030384210320507490810f207110842c0c040d00444187d194990b6030145000304001e4a074005000203c815103211403000c02c00700e40740c0c44510660b21074500490003503440c0d0741304070404680175290810003c10401e05010b0f41c10508400140e800d540c42e07000002181000418008900070700004d18040d6200f880355044024814a5800800ca119500d50390000015110064035506101b104112141100100658004248140060503109100c2c074140e400c1110240c0b9200306070340c805207065401d274110603c1d10702c0e940fa101180d0b84003503000303007060603100f8030644403801c54076070060946004640f6900d90200e04101c1007108001554866410829401e007081d081d0341c0056400340440c0d0612440f543c04050b408004280e9480092851013145076030b003054240180140c1c410818207040c8114000420314442c0380c0005401c405040780100312528012400030140c03248610f000542900c1040144150303200407032500304040d04100b003d43e851003024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 496529127 1250 496527877 496527883
    0x6090804032f0418080703110f030702010e0f0d080c03030109050a05130f080c070905010e07020c0901120c3b160804051608030c010c020d0f0c02030106031203140a2c 73
    0x2003401080700c1740004082c401c154002d0300214000c4000c0b012619403c80e00003420b40d682c4030b02803001c0d0120301401c003180b0491030001d03040f0001729005000d6002e5640c0554031605650850a05696035400100043c000c41ca21171040d1a800302c3c801e101413119050603800400140c011303c201601d503034446034240091080c0c4904485103912220704503402d580d550201400241001c0c044d81030100540c0c030110303000502c0050000c803210b81c0101030030440e074030f4a20440d0080590308421902107241d500006514070044066000703441d61500011000e484910b281c00c410b035411205142c442400741d007031100142c030100d5010410038090a10382c6403511103007440c51403e40c0d1120380a40560500b01d010800c080080301414042486800a0064041603203040e82c6031000c4011a40005056686403150544144c21125415001400000c1ea140c0c5039100c0c0640e604a8a064201080d01c0e465900181e00c000c1a030103a008011003002c021120012a0700000e00011851200080c01d0341c0390380842d00c01d028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 496530377 1250 496529127 496529171
    0x80408160c031b0305010b06072111031602012c0d140601031a2401030902010c050f030306011101020c030a08180a03170a0209150a030906090804032f04 67
    0xb160643c0c2c180b60000d15001d09a05404120354550810090b144203082a1040d83c0580d80d10416180010f40300280440c1500c00c40c0302080c0400c1514034003a841110180010607001c442d241b0b448104030841d00016210107441c41d03402c9180c40700c01c5c0138001c0d549802610513044086c200e903e0340410860f03083c59071600141030310300700a074040c2c20000400c01030705040842c410395502110207215504c59145450840c1505c510b40040307041c0c4402c3c0c134071541c4aa841503c20728414100075a9072105a01c07540d01d801501c18a900c6107078400000c0c002d0940c0c01039060709480d00803c00a43c44c00942071000c9849010307111045040c020340e84013062400d070884102e4031400348904115a02c4005604000301003d50440991a80d180f165000c1946c0b07a041e8000c4582d10500504400754840d40000c6407843d55011194460070160707201603181c001809030140c1e681c0503001c0d0150907116400e50401e62140080f1030300700c071403020003070541008400030341d40008200f04044400141e09200c00511000000c00303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 496531627 1250 496530377 496530383
    0x90603020a02011d161509062d030506120d0903060b0f0d080414090103030c240204140307050901030f060902030a120f0e010f020c0613080105070906020d080408160c03 74
    0xb240c00c001800d018001102a0041c17407107003202c20020f586540c1c1c012091a0301544c800002c40b040300502c1001c0c0103040d500c441280840f80d0211755902d2443e161030900d10420880d00080e260000d001c9103103441103410740b40c4403e070300161110856918003c0c001c403100b8400140841c0e03e6040041d000d0f991031038103807080350000d0410b07000c035001490100c000d40d01901920b403540c0404d9015079518245103848078141c9601d038480c80600c42882d1903423081040401c50000201404103a585400c0c860742c0040c200610b101900300c5160503000e004c00d404c208503500541e014134000801040452140d80602c0724080c4c12030030009000f4414004039060028512014010380c0c00b0385800c1400d41e5000b0b010122500540d603c0202010f440001110202003030000b80d80140c4c05442d400c910340c40c04034010300841001d0789403494003070340e9a2000c6003554004c881a03c0491420030f0100842038040c07020b00d420129501e4030f44542e00d070a60700c0c0e00c118010080314a80914554120508002d1a85100c83c0a150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 496532877 1250 496531627 496531661
    0xc061a0303120a0c18060c050c03070609080705062b09061401030b0f010503031b2404031403100315090b040605090c0402070f02040e25090b060a090603020a0201 71
    0x2420460030b03000003000b55184076603103103000642c07910b043c032920744070302c0303502004100555641c6412030880703601ca004242502d29014100c0d1303154041d41c013003007900c00400d000c1e2220b00c1c62520302020981003030044ea0150340260340800103400e000f04e4021225510000c4450081d648421132400c2c0c4005110303c00d0002c21403481c02d560001001c0707812039101d040301e100d401150641d0303036040c0740381102da03100b072003466090350040c0704441e04d1000d4100480803085090044504800480c110841c89102080c1c0844961407114240300034164000041c0320f4100784c440d84c842c03443c140800405000d803040e200280c10708150760452046803901d6003200e0440e5800c42c0b01c0409030304150510100070682030350b5100051143c400c1c4010b04d420603000f69807040b900301c03500904688140d02400007504407400c142c0418041d66403007000e070134000c040e400311000720101c05000560810ac1c15030205c1e419503410740d200d000103210043c802580088080141d070202d10b0050f031140301c0350a0036030140211010086d1508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 496534127 1250 496532877 496532887
    0x20f070303031d16091802040501030f0302120a0f05030601030204090e070609090b18060307030f0b060414060d02150c0d020319091220040c0c020910060c061a0303 72
    0x140d060304425025440d02c401c1200c18500000c60903510203101400c0180030113864010883c5510b90b40c0600b10440c1c0380311080200607083e5000030b0071030f04240c000315050a8404000320926a04111000a1802c943c1c4018a0408414000b90000100c610b02c00d0070400d00200141c0280d1094050340c00801c0c00907802e02100c4141c200c019102e600c81c2c02140300041500d40300042c5091903000d4041c502901030000c17030107001c7c2d40701d160002d1440200a15054402d200300000000e09180015901c1c90203568050860f040200811041d2809000384000b080394600c10b001036595a1f892868000f070b412901c0d0404090032007800c0700213009003181e0211900403400181c010035000b000900c5c5040c1d1040149c0f00f2908003010a550605850185107010b05161907510001140c1401a00405000144401c0c1604030040001c06440892201c0b10004100e402100214103207250503d4001082032142e440107420000020809155100c000c0e084d25142d14041110201d9119520030280003d8281c1b035840c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 496535377 1250 496534127 496534133
    0x7110709090f120c0215030c0409020d0e030a0207091107080f0309070819021f0203090d050102040b0d0b0405070804051b0d0510151e060e0120060105010905090c0405010f020f0703 79
    0x950013250041c0c0c052900081e1020700c00b40340700100d03071083c015951254201820410100021341014a084d805256110b08910307036610f04202908100145900400d0b1090610402c00f064568107084603616500501500c00082e2208007a01c1d206100304207519241c0c0d0341d00311510701e021000d62202000340242e101c0c00000c1e00c0d08003800d04255009840c910707580c0d0781c444190b1b10005030181c0c80000681060148020514040325044080f9020344000b604003502c0e41000842035002c0400c40c0803481d9280d099014be41040e0040a0b0700900c0c40c242040c0d81c1c6015154030361074480d0f4100c0360001803111903038143ca40c1e44084101d88081e41201c211681410740c80003c80060021001e0000c02800d5071a000031030300d02082d41c50034980e100001c0a1289454000c003950200303100c000d024140801c0c5104d1454040280d5100840754290300020f0115501d0f104c005008041213801017400b0301108810040d0140e1400700322000c0700d10a103002c1d8026400d01030100c0c10260904500070b00380c01582400014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 496536627 1250 496535377 496535387
    0x9040302100c0801030f0b0705070b0108010204150309051e16030b07020115082109031009210c08090a030b0712150806040314041d0f07110709090f12 66
    0x241075200c0410090b44903034038030075115103000740f00090980ca9030701c0705200004c2d442c07403205400161b20704109003482030329562a4840309090b00a5103807a903022070100401d000070080c2004060a40c20100080b4a00d601e50301c1e102d082201c548035064070540e038009010f55040100181c80c101c100c21405030244c50f85000014094159810030056080200d09111005206412800c540140c3c000345030f2060700300c0d480007445642c900300c0c401e03800e000c0c00003410503142404a8a109095880c0000300320280303150107203036580450715004040c0d5038030445009a541200c80c862038944c009013426128060500014012401500018070f40c83d03c4500f030005e0b058000d4a03020045400a40910440071300550311551503800d44924541c903070041010501090103910191542c0e001d00310880e14140d281c49500a000040d10703840d200440c003400400c090450100881600001c3c1480e00601201007000115034803540c0b4056040090340da15078420401c1281241618040c1c0d01040307419052803030b0318020304 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 496537877 1250 496536627 496536643
    0x50d0c0201061814010306050603030d061502061b04180b150c060108030f090f04150803250f031103070204050408040815090303130201230301050a060512130f0209040302 75
    0x408080c003030800440880d82d0180b000488941a00500316a180d47ca412003d01001f400b69501800704000d000708545c000c0c000c07540a091500302c4100700d000348110003841d29200406125040c1d6501c0f07084411201d12508550480b08113004d50b6265441800030b0000034a00d07100d0b2164005440389005600c015035102415a50070b506054803026030740e42038601e0700c82c400c0403081e0608406c1000866076170b00e13140710048991075018000041102c4200c4a900880b1b2490704030146503400442c011a45413040c810a205803480030392501e88042c4955120851080c20600003002c1c40a1400441800101081500c0850350010070034000c60816080c03145942d4030030b000b0030354640104819080321030344414049006894050003517195545400c1000a4040c00d40c40407410451881c10100001c4550400300c1c134450140910303185d03a5450107080005028003540070005101045c4803010902d0440e0058590250b0194140c09466809142c4a04c92903201440254003c4012003072109140d40019095 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 496539127 1250 496537877 496537889
    0x101401090e25090509040204050c0d0e030c21040909052506110307030815030c1504050109080d020d0e13090309050312090a091a060a0309050709140610050d0c020106 73
    0x60b8111031250040350300207124041c5503000044100810f005090076880700754000c04040c400d604040300040c3e00002e82c0c8804c02e03402d801e60b1010a038034081504c04d000440381c07040700d1100d6055001c0d80b1240784a0b14012031103030450040d40d841500041c000180720181c920300040d4140c0301c4c035a940b13000c11251041e01c0c0c0140000a1052030038008024000021079030819015150784140341e071f032140b031802d41d805010b01c030716014054408032800c035464600c84c02d01c0303c124613101e41c1d0f1900e0500d030006001d218180d003c40c40d1540440d10200b040790700400c40c4440c91096290200413460079401082280214441880c91140341200c5d010074503a2011f00744080da4000c078152041500c9580e4440201c1c010111310540c080501d810401c40e803900c541c0035504c40c8514204881c212031884000030f09036002030008a01003510740e20000f040100c2400b00001402c05428100301440446031801251140104980c0c05019855590812a40900300b0760b04145039070501800324001030300d4000d020307201611840c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 496540377 1250 496539127 496539181
    0x70201022e0c0e1f1824030203130b07200f071401050418090204061205010b010c0b1f091e050c040b0304030f0e0910150305101401090e 60
    0x185074a100d0150341490b60790041507071048030044450b004038403914010700c1c014020300c480700100c81011204600000c101254007000c0c46186c070103e002c481e100c00000b03402014410820028042c460841d810348058003e840c1c204150303251501036030550000011403034080d04942041c200220002040e0400c0788000040d40e00a0780c0e03540d00710440d10b0311150a10f01184061000788a40d09291401c540d00344014080458540301c40d401241c01c035100f581040540e0981036803804148030007400b407820303a00300c2842c0c012030740c85003500e44098203100500200b041e03219500c04505101001c1d894080030b0001004104524400892515001056501c0c0160180d0a2a0000d84002c0d8610b05440c21100c0e00c40c00c0c189907540381e543c100c0d00da1038000107000611110040741c120585540300114030640580c00701040160402078003544003003128051300101814042045030005c4a0880e140454200a07103e03030080b001c079801601c07940c1c0550030000f04030a01d9020001c0c0502042c84411b81800f0300556 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 496541627 1250 496540377 496540391
    0x30703180809040f020d180c1d06060a05091801080c0306011a0309120408010c031a0f0103050a11120f010503060702030a050f070f0c0e010506070b0a02070201022e 72
    0x2030350411090a000c09450003006200c0e0004070b09007900581c0c460814000018a040c214000c0c2038122101e02103680c02d10366000e54800c0c20408000c6007003020303040340048900c3d14003c45007500100d40c00184524001c1030040343d410302e0513026006607816110700800c2e00c113090b412084980c40004092048400c01e101c0e50941c400a4100031442c02e0680f41e0780320118111003000c14581150b64406001031007103100b2102400c0142441d02c010b40082c05141001040c4103907902801025285107140d06090075821054900403680c1d8141d41340c480078420308002c1003641d0b070103600c1d000070074400c001054039110014504542c21418610700b0320414102c1c0d64125540d0b04c51003495074804040f10240301690040080b0703603000380100d024200d0001d05588107480c0c02801d40d510340340442e0621007181c0d01030025070144040d005201c3c125002d400e081c1c80e540c1c1807501d55143c500421601520704008294002986020f59100340322949050b840e80c041551074a0328106404509003546030803c41e120300d4a84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 496542877 1250 496541627 496541651
    0x712091a091603031d01140a0906080a0218010f020316080c0d020c030601091104030c081b12030d0f020421030206070e1005091315060201110c0a080c0a06020f030703 73
    0x105410590b0b4155540171a5441d4071012145001c000c3d11080d8107001c40440e4100150115000900701e09076a99100820245000d00c041d00421012780344c3d40d5268018030200f600000b14000c0c0070100c5509182424450068480903070940c0700e404882046410f015400030b0912044000078442d0011902c111041203484400c101c1e122000000c0c3c081d410b411200040000c0a078a40040480602d050310300c40c5843d50b29500d00d02906040c1c1c0c41903109800c41c400100300d40540900c00018804261811181514010091526481520004034100c0d80c0c41e011007151002c00d80c1aa4003038254248203000c04c2171848080c0000102c540c500310010301c28000002d511910840d1884ac209502900302d411003900914140e80c81d800281e8002d81085e0b94a584441400300c9000e0354000c90001000404018107207130000342560166000c00d0587c2204210300308030101d0024025520b07a801055143c1ca4409000507141071801c801d0000d07185900104240b4a4840c0d43c0004501444054404109142c0c44807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 496544127 1250 496542877 496542913
    0x1031e0c0903170304030818070b030a0506031905070b0a11070602150c07020315060d02040c0f0f0c05060610090b03040507050a080c090412090e040803012603030712091a09 76
    0x40d0000d000403c3c0340c0100b460899462008c40714400c88101303480c03a058803903615440641044819000d210780710b406000c940e013800c0c407091103142c07203900044100d0021a15219030f104018440c010441400150200e1840d110701c0303030381380800c0c5044103881941e81d0312305000351356803440c480400110310401c02049049821408490030700c1d901902030310001040103074081c8a00310040c601600305075102da5034801641d41c0e108440c089401e40c0c840035035102e49078500800d20768201d4060000e104030600c083d004071300001843c3c1d502030012682001d0b044001c400031210f40f4a5a8045800903a0210038401001408640b0f001610003e4074110541c0b0713502c404140c0c0c0d0707030242129250002407500105000c00d203d15a60503450110703042020340c0030b40c4c5404458002d24221020b9a0084011005200f8103141d2522000d401a0a9840c020396108a0380304503260700c8080d040c0001d00c4000c5250105020094100040d010b420444c910440e500c10340041d1107604048a540c2c900f40103c010081800e1644 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 496545377 1250 496544127 496544131
    0xa15030b1f0f03060b01030b060705010903080a0c0909380312070812042105030f0a090b0106110109080c0606010909110a0305060a080616090806010e0601031e0c09031703 75
    0x410740042600f031454680500421003600000c1c1050303160856044142c580360000e14801707106000004141007241401815260090218035860b820a43c08040440d40010090162400c00c58000750041c0f020164507035180303003203003020808100070680c070b6100f0b4800c20351600c0c000015000e840702d682400f90301c8101407181d06801018200c09004443c0800c11034104140d106224150030b07442001c804072850449210807000d000000c00c0001000f1800303407003110390368000724060424840b99040b0350340c00719484814040e001c10065145650007503080d0075007151700c00b5074010344a01c0e0344000c0704840755101e1303404907282e90101300e00901c0091032170414401c15142801c0d404c4046e0030904da81500703c000d468042d040075400b0615140100301c08205100041c020700034508482c0928050760070140c9584255413110302d0f9a040f88004000354000000710541c0a42e0074030300000c04010700e61160051202c2c50ba50401480d192000b41031110ba0070a08a03010380f4014600c0c0000c18000d5424030f0524402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 496546627 1250 496545377 496545389
    0xd1b14011e03021605011b0306050f0a030f0f1211060f09100b03010b03060903120c1207030902180f0a20070201030e1015030212010b10080a15030b1f 66
    0x215401140702a110340e010f4030f402c140c51007810400c041a6101c00b402d40e401c00003400711060300f0000e8082025003500c50b4000500c0e054030305481208004000034810b003070610000e007038400ba6086c61010800d03170340d0000440550000c0810710f4242c601c030004203a00540070f0641c1140c4504000301d175a00610200d81c510817a6244000c207010040e0040c024040c11124003c42d400d50740f00c1175103a091740e40c1404803d108000101c01141c0342e91f080c82c0d1142c4800806840c88906010400448800150f54450a60702000c3ca040105000e2481c0c40400c0c0849000311410070b00452240c18404030380001140c07240549100f180500000f16070040590038140c500c8034000c0842004c00480c001540280c018030034440c205005e80e900c01700b0305082c52050324241c0300494a402200c0c9070a00441c9000541082056a010002c124150016010506890050381d500e002d0003c0c0c41c001501881c1d1907080303110705186d4240d01c03110f190303500d260200707618005542864000009001d01c040c0c2140e003020800480305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 496547877 1250 496546627 496546667
    0x90901080c0a03030e03070e180118050a0b1308030a05071d0108010e04050f030f0903150c0d092d060c03051b03040c0b0712090b0a0e040b0d1b1401 65
    0x4610f607000c0d20700c00e6000742c2d0305da05402081c1002030115500381081d40b2580968481c040c030b060300c3e07090700d508460058125002507aa145452008204005090981c480d402043e060b100c2d00d94180c4d26216060b081030003400204008100a2441c105801a9001e40c905468050911039410759050104c0e9035100d0f1075000440003001081b0542c010b0510303a801034021000e032010090000ca400f030450f805074a845809a00c00621100d81741810002e100142c482020419103508100752902100e02c2100c8250560743e494a01c010b00b0302803035500da0140002501280110006882003030618080c60b1001500d0745860000c105190500a001e22841348860f09108482203401d078940c0b0040c0d401c050410307102c0840d034200201b01d240809000f4158140101440700c1000040035004080880680100345400c07020700c8942000790b0002059604001c0890b0081600f840100200700c542d4410b44001e000c200700941e03020301400c0d01c8510070090b01d20040b681c0104203511300040d52480403d074030242e4115 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 496549127 1250 496547877 496547879
    0xd0c0e07021c030c080c03012304020c0625020604030813051e0d140304020a05010f02071e03021207080d27061e021c26040503031623030c07060504050102090901080c0a 74
    0x4927121940c0c01c1702913001400141000e00148d10185070440880322100c0d00040e6451361445240417000c1c8480450142c4000c0c8064a001c2c0d40040055101520111841c000d0040a104110041c80b5250082508400d540302c1d10880100840c0d480d030b4803402d804041384d4902c2906000c80c10344001c07248510740103001404034a00e4000110b5400060345083c0045004020380859001001c03141c0f4100641c82030b0742000380a046004002010000240e40d0380280d10000c07040104070780101d10301490079200d00b030030803984400303100d5400d54843c0c0d10a0025804640c0c80013003a03154010342e07008844240c4182804180340342403020b90b907902580f5604040d181d202c003034900903140b25100c0d207514405003501d2401d440b01915404aa55801583c04907a035401c080104881401611241400c82580780741c0308400342031000c0150341406c0c80502d072a404420000c00203803146004400c0702c0c0381c203078054000c02a80c41c0ca820100e00075046040e11314450115100009084880081d60101080004103440c00c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 496550377 1250 496549127 496549169
    0x30b040308100b0c0304030b09030705060115030e03120108010b09100302150d0203090c2701030f030302130f0e07050405060d0506040b0d0609110d0c0e07021c030c080c0301 76
    0x141c00e008000414038100528007084003900180070b0051490443c0c010f44d251415490800b500c204010b02c0c11000c0c0d0320600004003c20400a01e80c1c0c11112440826100014822401c4000d40300401020440b4031000403000f403003031081250141200d4043e4020400780d5282d4041080d0718106441c6800d001d9075480d0244003502c0c290140032903860b002ca149170300e81a40f0300740301c2d009ea8004903034141140c0c2112030b00900c40d09140382c00e0001314014862241c2c1441c401040022455410b00015004541c011919820075029038100d4001e0016481c1031140700d036440300c210440c417981d8002d000794440100c000c13510b0540590162800e03030700010101402c180319084480b0091500418250703001d900e03611210030710f0f260881c0c02c44810780111000300e41035040703003000c0503102c203c6440d00e03000348082d4801c1c1c40401d40041c114419540004100b5804c0e46889000702d14250100c0d00380c09180171070a94030300009070185d102c80769106d402e4842c2d4204c1e0b61015040c0b003071070009108484c40307001032802e1210700f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 496551627 1250 496550377 496550387
    0x70b030f070219060c081006090e1503010e0f07090b09010b090d0b0a02040e010e040203120a020111300103030504051c1505060114340506070504050a05030304030b0403 74
    0x48001c06104451901200950700d940500146005464507070342c1e51010a12a94403241495004024150f94401285003440007403404003030f840307480603060f2403001051079818800c9030703071402030340007070003805110000751a03142c980103510b5030b05c5410b01c20010005000d500d180102c0c200c07504010600e180613031038000c02d1842540308441942e80071024007a904c0c000341e92a0262405500300090058440d41084229610290103030000050400c9142c1004010b075070000d042c0c0201c1c800c07440483c4d20703042511400d0303025007804440804640d002240726000c19050f0368420220201c0a1201844400b1a40031401d00410030b000150000310204000c2c0801d05214030758115800e1200c40d84020034000d521007403100c0d0102020603094649410606c262076034011a210242c6284c0f030313281c604d040e00340d0f55079440c1c803a401c00c1c3c804003186042c100c482c91580c2800d03869000e103420105a450038900b40c04020404d6105010f6070b4801e40559001260604002040d502942e500490300d1016032582d89003511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 496552877 1250 496551627 496551631
    0x903020d0c0515070504060909020304080f1b0604030c11090f0103060c0e061605010605330405060c10150303270f060201061d090d0809033603070b030f 67
    0x90074450070110040040f8200303c1948100d00d580d82c0c181d2501c0c18824010100a2a580103111141c014414040811058011038503002c81104030140d4601d0107092000c070b011481c841340341c818010384c020002030541240807a82c009100b1400c1c248100300c80310400c41414002d681c2100307007800e4600140b0000c1c607a0307403200c030140c201030a20300d030400106800919598044160719200d070345141c0e65002040401d00824014002c01c640b031032504002511640260040c6c00112000c06094501144480032641c0c200c4014040103485642c1c0c40c22514031032075403000c10918105500e460014050b81a000c24030114051740d5240d610440304074561400209030714070743d01040071000d500d03190025003c0040f05c0418020041500040740c03543c0b0b840f641289800e0080508140d4209407410880500740105908140031598102000140c0382e58003c245180142505140100c0394111340d05503111200e070b000030742d40502c0b0080382030b0382c0079040901d80c488030a841410729000050011848908000314020703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 496554127 1250 496552877 496552883
    0x90418030206060d082a01050109020c19020105070c0909211d0301060e190501081c0305091f0e06061507020d1a04060e1b031213050a03050d0f030903020d0c 69
    0x142420b86e01c50309441144070741c22421901c1e5424914207410002e0a0141c40d0051111031811814600803c2c461a155100805844070001403144000304580c000c106894109401c8071844040e2512000410b0013044492801d494031540e0070000032001100c1d442e081403001c01d40d903a200302082c0010302c114085200d880066810b540b80c44011800c81280c139060b86c81029020341410100c181c640c04c6004841c41030700415080e41000250307100c0484800d4098001000301c0c6000140f43d40c2d006440d5017060068103052114650592075840d82e00c0e480d40122120141c25802e036555a110901000107400c000001100307102da040c400c420161030500e200c08081d40c014100585004901c5140c02c2040e0001c0390200d885542d607019002c401d01003000120001c0900003040f10a490703c1d4400640d4443c83c0c0c000e0b20104000018500d400c0304000c0700800d008210141160380c840d40c80745480741d1190045400d90740002c40390241525024840d0055104058254014011400381a8800c0f607494a040000ba = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 496555377 1250 496554127 496554143
    0x1814060c0d0905011e0518070e01060f03330f0e010b0c07080a0c091a0904080d0605060c0d0f050412020d030c0803040f0c08120d021e04080102090418030206060d 71
    0x3008001c0b2503a10903645c50b1850103000102032030f003045003045c03501c40000280d890f0345c811a014441c841c0541d070b04506580e1207081420404180030300031400391020751003030080902050780f041d0580f003c11402204001c0a000c6c031107100350b110500c0801e894400e2054407601007a0740010440c0061010091041152400c1034560007500c0305201848c040941c541181d90a844c2c210807c14a9894411014980ba28400300402c82603d000000c5540313102600151071540c000130807407000b01159000c04e00411000e04415119481000c50589030a0314500000102d10703030143c881e43c0a03200cbc9048500b600e00c1c1500b0080052400c2c2c0070300401860205044091045403e1801d0105510300d02443c03081d407090101c010f4168281c9418020041e66078400181d03580460400c1000c00c8811044c1e4903240d03803810780140c960520408440d80c20b50300351115106c0d80400200400d0b400810b40003460061001c0c3d9007440060702600104070b100c100f007240680180c12200102c1e5181c9032105200012a0240c108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 496556627 1250 496555377 496555391
    0x90303180c051503060906040509010e0d05040e0105011b0b0a0f060b0315030f070608090a0204051f0506040b0901050a0e030d03090203060604050403020d081008011814060c0d090501 80
    0x106450014485000c1d9414840241c00b0001464207400210f424000b5502c0241035041482c0440c0c00a44058109885183c6501c00919490340950021000c4801141118102d010820020b002548540250040b00c030a1030008601d075400b4240c9a294850580d03220300e40040d0715254084009005403000307540d10303116100c0140426590040c080501844006684d40b41002d55080b44440304130a00e1070300940120080d4580841d0101b04c2d00300310fa80310b003082070315982c1c1c0d40e541506214040e00d009504c1840c100a024200462800e01401c80600d40203002d031860301e9404002050040744221001814200310007543c55100301c029015204042c04c018014006010000e03041c034145046030000241d680032802c0a500d42040b1054001505607400c001a05181d18025220004a90000c041c000c505002c179010310140303000300b001080b203100204805108a801a8600c82e01c080781610a00066400101c081401142c484d024002680200b450120b00414800c094188007000361865541c0c1c00d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 496557877 1250 496556627 496556651
    0x23040603030e12060105010519051216020d050705030d0c05090a140f1c0f05340e0f1504060504020c0c010822060902060904090f02040e031606090303 66
    0x2008059407003a141c108056007003100b4002c0004440090103c1540b0000040200d030340c11604948100442d4103001c1108070009806562a11451002d0b601c80c0c0f88002c00c11075180000c541c5010922403960030390306000c0c21400b048545011700d0038050910342040001c0012545030b94004000c000d00360822900f0202c5034000207260010b15801801352034088600c8144d40d00e420411011940ea08075800040f4003100601c01382c0e50026008000e01c412059488401400810803620200d044031810740b03110310f4808840130010b02000c1c0800c220001205070040b501200d80d024062082000d49400700040e0703507018400010700802501141c00550342c45010882d034856000a0441d640d072080100281240080014160480200a0041201c0d00d071007031040542280e104c1100b840c0c0149000c20f40542da40005031942c840d809000340e101e49020034101c20400002201a41a07000312410400c0d481201c1c8040c1d1607100d80c0704001d0402c0c020303480316800510141d204941721030091038005503044841c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 496559127 1250 496557877 496557881
    0x170c0108070f1b0b16030506060a050f0708040f170d0c030806040c0504170c031b030604080d180b060f010503063003030f19060323010b13020a17060a2304 68
    0x1e0b0350485080402c45240c5c11581d014011280c0080d400d40341c60703107070604130507008095000740d1341900e075880c2d40080c254007070000c002c01f0341d40a40111401c03d0358080d524a100d8410105065040995004081140400601880721003210742d401d034079002d11582d07410040200520841c41d0b0341c01032000a100c0403c07010b8060690a42800070040100104400102094603044501c0b0500340800301500100702c09803030211300103070840d500c200f8094036008041c0d07500f00641102104500e18409140b14801480148040c950150740242c880d54a0300100e8001182c02d48002c544450b08404064040c00d0185140e05104120690302802c076640520318409040c20350f4019241000c0d0780b901401072085494022109040c488101c4c1c5080100d1341c07555450700c000900d10052485516040444e02d404040c0a4001c0f10001c0c20003000070b0303030384540b007181c20000f90004d120480c0000e801d44503290117010328103541030052600070542200035141c15990f68256445d0810300c0345441c10071064040741c0c2c86034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 496560377 1250 496559127 496559131
    0x10509090a0b07031415060a0503100b0d06090f090c050f0d05030703080108070803040810051e01180b0612010e04021c0308041403190e010201090804170c0108070f1b0b 74
    0x10354020130745e42c114a00901450300054950701c840345c40c600c02681e0319551002103c2c03898400d0304049441f5596284050034840640c0d00440890200181041c6d407250a503011009407601440700300242c00c1484e88200464050300c10040c5030b08120807040c4070754506107140400e1210024414001c0300301e43c0d40c42d907046820a00d012408a0050b10040c419118284034980c081c01e90740300118241860800d54075561407181200d12016956000810302024013031509120b00c100c1e0300306510341542d49096090f43d2005d410107408001d071070101024041d18195084521401000201d4220380e403d10601c00701101000d08102d900035600032403005540d42211100c1e8065020f07071220400c51800703082c8840002d44956505082e0340040209804080c00000000d416840c1450282c0403100c850006078010300c03140801030007048000c10000760744100c4944c030f00d2401d450079040d199160b000c1d20040d252490150b5004004c00c1500c074200d007202d03204017080c0000c200c8404c69100c4014203070300c0c0e208031a142 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 496561627 1250 496560377 496560391
    0x100e06040603020a12031b051c0528031b0905041503051204180b030a0f17040f090f060605070311030702090106020d090501081611010e0d2015010509090a0b 69
    0x50110481e06064100c581e288000e00036551035801a441c40d508c940e2141d541600d02c10b0311450a1400802d00e0b4403c8042c1c0b5184603540301c2c034190864000100005022071043e2040000e800c20403020800040a00e00d019960260b0700d8180380242020100701c060716080c1040c0c2c0007000354440004c0861010010f1001d0290003181d00356480342806080c21441c066440c0b000c05e458100031001e021a01c00281003002c9036082a07113444200601d2410810141c246400343d0070300c0318080f601044040044502c081200e8581c0f20801c12910342c03007030b4001a0748280c1301d02d50104806000c0c03540401e02810405041114400540745054116800078002e4607003030b0000001039111810948e009600304d0000c034080c01090804c2d80780c81c44d154589600703403003010041404005820b45c9040303250b4000d400c00d103004140c500641c0c0000c035902e48000c01c100040041c50240c038100100c2da401d001004101061108502d0301a04000ea0900f0144007605c000a8501c040701d200300c2d4001008a10401007140c05428 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 496562877 1250 496561627 496561649
    0x30b150f030f0a02040e0103120c051c0206100602190c0e040b0402040f064202030c06011e05060f0d0c052703032a06100914100e06040603020a 63
    0x500c12600c0001100c010030510301d15104200920071100c80d03140c1d880c1101d5000c016a0270422650743c04a950409041e4001e1240c482c00700084600280300c00700000c0d03258076900f241d456541e1070350124a0800d442c0300380401342c0c00c1090302c1d601c400050a20391100e0f5000b501800c0c2041d50758250081c1c054021201540c8406520301480b0441c40c050007100c004490400c0c0502007070b41050030300000d001c3c001c040601c0d84442701080414200f044111300300240c0418020680e01d41e2082d50207902d07540200c144a0540c06044004900e404452804141546130f201c4511030031401c0000340b181c103a000405445603803800f4003034040c000c40e0b40d021307050700e0003602d0707482c1030b2901241e0700a036928540c4011070b1421040001c600d1102c2c0e80f800022380d0440c500e048030079818004c4000100c014000b030614440568080c100800061407101284441110411b60007005903107207420045140040661780d1380a207170304e10303e403c1145603030a1680c1d43d003005004100142480d40c075400038284260561003a41200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 496564127 1250 496562877 496562881
    0x30712080406030b0103230613050c0d110a02120912030a090501020c040207020f0f040209030303040b040308060d020f010f0203040f0305100e0d0909090611030708090105010f06050406030b150f03 86
    0x10341c18060301801007821b090a104014060032465030308154081126049032142d000660255507405001c0010040850104524101000c400b20f40d0f03401008102192400c103000b1a004020980807a0506009036020785005030715582c505102c1d500420600794808405000a100b011083c40140b011851507114044000d18000003e802d207030072014000c4c0f103039106101e004003603214070204004924089400c3c00e0403902c0d060004000340501040306802d03200101c10081081845220280264000c0d15402c07400d41e02d200421030070031401c001c004c0d040007009030303424815400703030301c480c02524818010b8900f032a8490051211100c01a4010344403580105021442071a01d4442c110381045986c0180400d003401d8880a401184244151542c082d9501866018029190321001c90500950b42e1250341742445403005100c508183c5420505510b844000a110900038041e54105c0c0c41e992541402e29140002c00c0d001000c003591b603640c004c5684000d0001c0c0745442402000d50700340c22038030540c4034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 496565377 1250 496564127 496564139
    0x9040e01050f0703061a07050f070e040c050312070206090a030203120405040f02120612030d020406090e090109030e04090507241202040320041d030307031a0f010e0307120804 77
    0x1e03020242a083c10b00d45014414400c0c40c000511240340b421240c2006c40d66041c4ca407034424a08030484800000302c0c0034145000c42c099000b15049401039014a000031006921481010f45a0a281e26200241d4004005407801403c1c801e01518881d03070002c000001031541c80d00400d040140b5200551764400340000c041c8041d1600d8030560410030740e555400c41c10036080300865140140c003d0b0501d032207402c011b00080500e210030070481d24075152082e0103544596407800003034a1220603002e94a03201c3c081d4030014040810500c20801c640c0e400d991102c440d014107070309100c0144146002a1807a00072403c001c14003412a0b8183c10072521501162010030140050080800e50840820f0041900400040000c40e80c2d9090048054a000349010804510f180001d03005000d1540c400764000003c6505001d0407401002442c030403040c42c0c80601600d005c00c4200a00d4040500c030752940004020301150403940700c3c000c5010786800240c11a90095250100604000d0302000e0844007a00001414006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 496566627 1250 496565377 496565401
    0x5150702070810090f2312090f01080405031c0b040c05070f0b0603070503070803090319080406142505071d040803060d17030103030f2d0210090b040b10050604140609040e0105 77
    0x1f0720000c0000c05400d1141010025104003440c946142c1048880320200b0280328041c0110340c0101042401e15801d84660041000a081100401c034403880c0340500c09040c1e40d0240b4120b441060b0701a0307020042c500240d4500682090290885805125244000c1410786082042c071014020620007540ca4075500d004040c0390803601803560090f03503c184c0910b030000d4000002d403400c1d101c141c1404000007201454404c840d010b10105800041b0b80c4219000f10f00b0b10642c2c4070843d13103000c0c006442d0b0051f02d9900017012100c40600c40c048102040b4001000700702210099034011000074000c803004411904c826030214900d00c4042078040f8000700400c1010f400820902042200e402c2013a01c039154240800c180c900c44e52071170301641c5158582c003011140300b40407041840c64492010400000f650400180b064400c440840b40445000d003c500000a440c94880864000428061500381024010082134a1780100300340c214031f090110001d01d54441c01254601c1d20794100025161601032141c0030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 496567877 1250 496566627 496566643
    0x7271805100503030a080604090f0b0a2714030f0310090507020d080a09021513090609020309070b072d110d02010207120c1205150702070810090f23 65
    0x31540d40d903a04102ca900c1c00b0080d61101c403602d0514510540d44c035000f05003d0008900c1c000c0003c0c80c200c1c068003c120052111500481d5045401c10440440503000c00c0c40c01141401c52459600d944410000501081d01542e11041804113480c02c0c07142442600e0810b0700256507552110b111500d06200e8180f5038421160b0100ca03c0c401009000345e1881c0c003400582e400390000d980a40c45560311015034803250350300c0002d601c0651116a8541c800c0c2e00792250040607001d0220018142003001521004d5402500d0045205201030241c042c900308100071168403900d421186e145801c8400001450449450b28a40d501c0361203682c8d0107080d510388407100c00300f022801c902c928194290040543d0b03000a02c001610301134000c007110200340d414094051500d99102c41b10a114100400c4100326000c2400c040401e4168009025074072001c5d4182d0701c07030210780603440480d40300e90754051680a0f40c4d0403403403030b450003aa002d0110741c0058032070310007443341d41691742d803505445441007140d0101040016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 496569127 1250 496567877 496567891
    0xc010c0e1f090e060d15020c010c020105010305150414030406050d0605062d0c0604050a060e06091c0905060c0606010806121203090114100612060303020607271805 72
    0xd64000d029070028000b86070764003442c00b841d00124000740407031300c9500f010301125801040341c070024000050340d0f00180d403040410016039400d1007a4511f00d50300500886050303035882406858484081d085400c5c1c400801801075409804400c1035081180087c8001c0010300120f80d1780a5558402c14800802c0d20344592143e80501c00401166000041e4509045209400002980c040981d84e100b1701005000c0c0b40d00c0c03043c00d8000c400511081190000d108400c1600c6800103100440380f46d08883d0315800c08803081c81e0a0b410501184c088000d004068000d44000f40c01d280840300d4a5202080b02500015081c4025600150a205441d078120024541c071102c1101c41c0c124410002000a46500700ba216903008041c011000c00e06d030b014290040c00040c040c0d52003900c540c1c60003c40700c40c4140c0e2944a224003280d031210210307881285501414043c0c82d0940c004000315100da203c05c9485084202d070780c1940303c80f218030300c82e2000703114020706000b042060182100e80ba480e0f4203001c21650080d02d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 496570377 1250 496569127 496569169
    0x510050a06230a230c0118051c0815190308130b0a020d03024b030c0711030703060e010212010909020a0515070b010929011e03020c010c0e 61
    0x3001e446036010b1440e600d00803d0220300004c181c050040c10340c6500494420702425400c0014205031801c152400081c014040c0c0c1c11541e000001c1d90644c0410309041600b20005500b00002992843d42159100c4604002502166002c81610700090023600f40e43c001701c448900000e007100580c00020400400b6140d184003207464036140040207980c40c90a000c2c603006254010502064400002034000402e50340704000c403071307020082141c9001c403540704010b44044203258200710318695182e8082c0c6c1e200700207499a8034a004555160750f0540040e00c0e00c295458800c000c0b000c400610304d0301840c00381505440000d81c90741e100c0d02004201880581150f04814540041c40c409a602d05860700300b01c820a842180d2504150006104103200b90903025059000d140c000041c4001d10754040202e480c001c1c000d1001e07c118080094412402e040714581c0042e1b000445030029405005250043c588241001442c1c0340d142405c007400c0d0382c000710780c44c0080b0b130300715694240c0d90134000110300080c5141e40c2c0d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 496571627 1250 496570377 496570387
    0x30109051e0c16050312010603090506070207140f0607020d06060f1406070b060d060c020c1e0a0b03130b091c020a0b01121401021306030e070303020a02040510050a0623 74
    0x2c050400e000d80b00d00c4403465500b0000c0003007407000c00d004483e0309052071440c0200c10760311148041c001c1d01813400c0403900c2d032180308002646280b0204100082c0c84042c0c10110540d00c01030100203480001c902c20550180c800c00c10170005076035607085038109500c250310100309146026142044006540e110031070741c4444140d03002d540d5484404961959602119190454454a022400121603902c009045510b00520005216000101c100c2000c3c401c4404031104448a11455010708041c10000d4002c1d1003200c0c107001224208014540c0100030740a8550b00f000103031509050f008040c2c619440c00d410030300e100c00c20942c02a64140c00382c50280000c209909540c1d4600700100310503c501084180d1506408007000602e00c221030741d100c3c103d4029503c41c0810030304642081070601c60b00e03012030701d44400200300001c04070380c00d0700312030b0141c0140105101c69002e04c000b4203c02881c426200c5465180419541d4510100e1805172030643d07510000c3c9040c200001c03e28007105100c0b483c1c1c80c0000d03c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 496572877 1250 496571627 496571641
    0x14070908031204030201140405060f06010507121116260f0312070c06140a0e0c13090c030c0e0103060c031a0607030207031205091306060c08030c04050303030109051e 73
    0x1044540081c1c2001c21811143d4032070070300300d0052405000311512405020144400c4c0300c0e000400a0040c0402100401e150311000010b54042c8504417005201c900400300460100340190408482d62006070705440e406c4486070401d818440340c03504108a5100d42c00c0320a4001e408518100c1200c0a0307410061600c2e84c1e03541c1070140c0d24010100da826691400303800280d40303584030714044087e0300d500580074020105c699090801c41d200031111803030554640a007034140c18200250a42c88810003520100070050445c264001030200c000061b42c0c07908554038000006500445004001c08041036181c40a50440c89c020f0142c80384031324000c04140c1042d9990407440ca6050b45a4004c4d00116101c641d104114541a0f080440075800900301ea844810705031980390f00003005080c0391600302d548100034401c20301c1039001c030780440c016030700050080801c80d400901100025038101401c1e2048030700f07165a07540081d2039580700346c020304030554440052100101807241c8100e0b1030303d80c070f00d5200004d20700b140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 496574127 1250 496572877 496572883
    0xc0905090112080a09050d0c0e0603060f0a0c0315120b0a050123030109020a150e030f030f090a03050f0a210e0108061305010e100f080601061202041814070908 70
    0xb10000c0c1143d0000207600e5601c074007031010700c0e004007005803000b800500e080c10f15403440c4d041e0303100700790b0400101e00010700d4629012400502c01e6412400c0c075051b546403803103a80010140d154030041415a00e40651040f10f20154209005121031010f0254840031841d05484944020b0071910710241401d0051001c5d030325404d2000d6801415442110500d80d125002a000d03050440001c0d41000c0a02000304060019002c030028040450711848207511042003030507982c140c2501552896041400605250744600340101070780800280300003001c0703032280c440c10f0030441d80e100c0c244842c0e84081082c004100843c00c0d004074440e1500d48180c10390080d101702814501c41380c0b440c17504000c0002c1c005100d658424000482c084040c07001008a0741c0c40b1154a568140280c90856810850540c00150000e0110840082d02c41c1c1c0005030040c1d902c1d0580c2aa90410150b6810b000e0039001e01000c14034000141020005031508200850b849100c400047c1280e140139002c0310400018031404e229040d000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 496575377 1250 496574127 496574159
    0x7061103031b0703030f09050c0a14131d030a0801090c0302070305030a090201030e030c06041703040c03080c01110d1e060f060c02040e070e040302060a0507081611010f0c09050901 79
    0x2a0407450383c3da42191400320001c0c0a106098890149086103541c00e001002410b1041244140d44820219881d0030704c2c0314161400107115030303000d188034100d0040c98100f40c0004451142c100b0b41c0401e0100840701190454114040c0c03076002603d50001008090903601031800e800f28a03040440c5003c69607140100144030051040713030040d403650b03c00310440e4072a80c4103480e80c099820680e41c80c0e0114030009503d944090314191584d000d0001515020441c0744212070060307071700c80440410240380d547c84000540002c0f4032014507560390b050607001a030410004021180b036260000804019005902003429030120600000e0703880c0210902600301450020000d075200c078100b9466882091001078042e1400440e070b002d00d4040d140c00042c0319540d0b2000c07a40114480d0b02642c80c035995040c07032501215411a00d04002a40c0600860484117066140280c200600c1c40e026002c0303001144240c0c2580c184c1100c11725000c0d030303486136000100d500c1914607015040c11540400740e0752601544603809585 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 496576627 1250 496575377 496575421
    0xd0207080d060b1218070f120b0a060506040e07050c1006081504080d0f09020a09020a1119030c0f050604111801291201060e1c03080a1802120706110303 67
    0x92140c82001035800c009410041000f001d02001c8241c644d024091405880f54003100c2d250827540c0400c084080364000d4030242c45010b04050f050529090300305480c40e002810b400b06200b407c0100d203040d140107100380c82201800d2000417420f10310341200940752070841441d4a2042c60040d041c00005000c0c40c0489101004401000c66280d03030140c080300003003819420007544268032107400101525940c0260421140030b80300c0760300398401802001d403502c02030300c006034110101c0c00030980041d0040182083c0c440c02407403400440350070350380c0d00d40c13a00b032056805440c4c60f40c003560032417600d2506016030350b0a04821034a040565241003441c50301451141c0009100300b03419000a4080100b00095804042c1208107a01c46542d440001500001001c1141030040c0000a5a4400c0042c00341207140f030355905550300440d994552042a00801c444000c140300420b104030070300050307a80c42880f00d103040004405011110700d407410146c038002002141c00034640007403040201000400d0454010104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 496577877 1250 496576627 496576651
    0x10302030f070e0114032a13060305071704050601080606010f02060c160c0e06040f05040f2d03050c0708062a0d0f0c140324060d0207080d060b12 64
    0x3051100599085c583c980d4000c8600101008000454480001d460b180c0c00c419003860b910349aa000000f403461142035564042540d942108200c0188260b00c013643c081c0321440e00c15010b490107000d5201007a826241031741c1c0740d4000c1005111400c0103011407508000e003420142218441603001135203e4800600c614030100d00480c03c014000140c030044403515500600c0c0750600d9485504100c902c0b2010b4030114010743c80c009550b42180518402d05014036040007481240765941e940b504a01c540f14000940c02c18007110007410348880350740b04021a42d1003074492a0301c44810680c00d910380f00300356200041c4c69000780300b80a010710380c8121501080d5810f0f00714201c0f190084100e01d03641d1240205140700e4a1401032412004045540072102001c91541d076400f540c101d54600d46868041038904000800c071030340c010442d40190110700f443c03c80016011500306400940c42808a800c4454203031422400003614000c0400309201e16009403400682090501480c100040440000100181d032004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 496579127 1250 496577877 496577897
    0x60e1012060906020304030206040b0a0501031502031902031e130f080c03070507061e0e0a0501030c090b13030506010608091506010c0c0b0406030b060c0a11060f030112030806010302030f07 83
    0x810940c01c5020010f41115043d0b41d2800e0a26001395200b4084070140c801c3c000f190041500d0080da4000e6904032604246451031140340280c510000b5030000c5d060780b404000c4490040d91819650000c0d510070003004140c0080701001c1020f20640a00007403003400031101120200c0d001030745144042c50120b402048064441c5481c070942413a51283e40c00140041c41007a40001381640e10440c00c0038400404803407007010503482d540a82d14002080344c40c41d0700840d00341051000394401d83c41074242034250f1426070310305aa5222002c0595110000b0705840340c004080a00500c403041200a005298030302d0702e0450f505d00054259107401c2c944905400c41200400840d205078420301d0348000458000520707410b03141d42d91400702050f038010700c58000400e0400f80c1c03248903454240d0550341001e0ba5000038005143c0140c0d502e0288040707051342175600000c20301440e02041d00d600080d60103082c2c6104504e0107944d81d400c000e030000f10b00515107410503004004009102650a01c8070340c00242c6420000d41c0d117 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 496580377 1250 496579127 496579133
    0x150b0301030b0606121005040b0d0f1401090b0a0203060f010f0e0d061d0a02030115050619090b04061713081c0f0f0207060b0303040614090a050d0b0406060e1012 71
    0xd841100d405040d1703c00c0007002c0c00348006114200c0011500c003241c0070080c0743d25082c1400945c07448080003400c010081030000c40032801c5510000740ba045a03000000b030795806640c4420305403406850180e40640d0100c2008514100f0000f00030f40308409091048e52b10716084030041c2502c0c5600c0059014a003242c11000030030540381c2010841c94000d03149120400d8107140c41641d20705842c01d050b48251f013051050b4071000100c20156064441c0a0260b51921242240001321100704402030000c0140c0c44e0307800191001200e0240028040b280d6500281000d1500000d00424014000c01c0c041640443e0160000c2c8070201201c513a800b0010400700c00b01286040d8400400081d60042051403c00110a07880382069000f8031a1070712030780301041540f80702c0050507500d01607401a000410500a01c03440640150000b49c0540c0782d00509003080307607071102c0214490302c0c3c0404044070f55010300c0b002e1004002d01c502a4002138040c81200e000341c0d16010402d00c002e0207052040903511400340c8040014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 496581627 1250 496580377 496580389
    0x8030319020a09030b01090915020906040b070809100c12360503010213030c0b040e07080a15120515060a05041a0a0311120f0a02010f0216090b0301150b0301030b06 72
    0x1145c100c80c15189a41c1d64002c003034041c0035030003001c980201011904540074086071003030741c20350790b805040c0c5030400b401d1241c0b18190b54008081640c00c24024171412195680d01c83e1403481c10401713982c80c0e0601d00c996290003c01440c80d10b03070440038048030301040b0103030b042c0185c480e0a140444030001d10790108140000c0960f9000b5801aa4165000203040b0701411045060001124410300940034050b580f13a181d07068038061405203646c1a080040450105841180d8203900b0843c0c0000001c2c40f9500001108106e1100e80d102e010003d4940e0310400c24440248440a4140f0006118104501c3c100001444000381d60041502c00e5a85101002c80c45401500c41d09150704080e0080c0003040c0c680c00e004010800705026140320342d90009801d0707030304103003c5001c0c2100d210860081000340324550040d510030f00ba03090310604610404060103038200000500300003d11428000040386c4401c8014582910300a0b540d400c01d00707460310000c101107440442101d046a4006134144450b45900001500c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 496582733 1106 496581627 496581629
    0x1020708010e120f0f0408100f0506011202030901020c06130c06020a0b1b0c061305061003020102031b010204051816030b0f131803020c030708030319020a09 69
    0x2189401c0c3c9000342540228981016007000503244400d203041d00aa0302140c5554010024814680407038400d1002010b10300c0002d00c1540382940020304100d814608000e5a19030020014a11040a60550b00e800b078043c020740300c4c6424111000084407050500a0355500055940040e220b4000146c02c030726075500607126044c80e41c42c010071403010301103480b0040e50484100001002e040080c09800d100f1118440b6011485240382002840c186004007803030340d0301c1001503007440984e03000015103e6081c03046c2d4043e0110210f404440d030180c00340381d020701d030007084140364540d00d0401308040611500305800c0384440e1560111089095514100030150800000c44107011a17041c00c60603018aa2120072000c1011880b003400c06541c0110008250010303007142100707030958642802040c3c010840d90000b9402d40c2007944503502c1c03222400507000711542d40090110001c0b0b000d841c440c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 496402877 496582733 := by
  have h0 := BRFrame.cov_init 496402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 496402877 ≤ n) (h2 : n < 496582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
