-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0644
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:54:39.443469+00:00
-- url     : https://prove2.me/submissions/cc5244f6-d0c1-49f8-b9aa-eeb9d8b87430

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 115647482 ≤ n < 115827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 115648732 1250 115647482 115647487
    0xf060c031b09060706050a0630080f0c0a03020609060708070309020a170a0605090c03030901080a0b090c09030f0d050d200d061505040303020a03030902030109020a0f140a231302 78
    0x3845500c1d04040e0081f00342940c1007182d140d03111460f00b400c003101041443c43d0106120300645521040c0c42c85581103000d81102c0340790884400d08510550b0107102c0f16480354100c0441c10b0245901482995417245004025003110301d07050704010184000109481e041c0b6580705c03041c0b425901c03071800c0100a405200720b4400d244100421685d40d5001c01502113800f0f9052034001042d140000c01e50a4020002030002e505000b0034030f0064540341c50003890524801e64410b49446030360b4900700d1041c080c02e0320349002c83c0d4a21184007031600300180140300401d2948a0f1200e000f08561010071680c81110714180002c01c11b403549564a1007030600710900080903c08180006c4404140d0b21450071201e02c0b4403856a40c1500440c1520749014620010303001d40c2206854901281c001e801c10717180b05200070300010f10f921142d070008084803106d030040b540003182180700b80130b4040c22180400c3c98520440390f40d070a03540741c00b290f100b5287d00c0030400c48184056041c5480961100b064824491003000300564 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 115649982 1250 115648732 115648747
    0x30904110417011404030503180102120604050a050402030705060d0609051512060c04050d0c050d0311010b03010b0d0f11030a1101030b0409030c12140c03030103050f060c031b0906 79
    0x26941c0c0c220303024a01e50755803584160a10024140702d08080540207044600c500d6540707032405d0742d860300003c0c40fa20a027282d100680d807400c034080c802890041451080c02c1c0302402e0100500c0201d9074014180c0020354903103424030002d6640014294102d0b2021101280d46034020030002001d00500e5000404a07414441882186007105100704c00400703040e200760100c0c4941e01885562160103440c00d4115210800080c483d604003089140120b0780104041c0ca902507464003c01c040090110040c1d0005901a8a5003c200c00c00e001300d4115a0040340240400c00510b0001991041e440b94000d01c511940c0040004201400411074004400101928481800c0342007502070400400c6045000910302540052107160504c14032881c6034140c2c2d11004803404c01d94a0303c525000400d1030380e09000d25030500035102602c1d000240f03d4002c00300c0140d6140c0d455464990300d01140740b100d0307881c2c5420502c201b011504e0140c05076544099802442c4102c1083c0d903007a10303090311440481c180c1200300003944c035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 115651232 1250 115649982 115650011
    0xe0a0506010311060415050d021e030a0b120d1d0409030507120206101e1511010b0d0201051c18060603030816021b1809010e070e04020f12030904 64
    0x398101c81c020109072810204000821020b84114000c290010300240161002e40e03220300080c1041c03074403102c001842c201c105403080354400401042d01014802c000f0822107244000d0041c2520703404140c40307852888680c068240d8075a48058215030401204150fa040800707500500c007220405c0180040100c1f14485c00c0c000c000e90712024083d500070310302c501c0b42c07040d642c80059010300c1001c0c40c181c290b882da82040342c00c10f1741c01d21150f81017a00c0d00824401142481c010443c80410a4090f122140440c003140c1e000d81c01d60324960449c0e1300c1405e41c403d006026036040307000c0390080400c1c11642c0110244154804006140809a001036151a86040030400c060780d402441501d001b03881c1d4499a5403010f440d115180c40000c0c1e01e10050700300100c0314288808038421081d036180020400c881100c0b608014041001d0111007040320744c1e440c0c4401c880c08010510888000d4031184000c10300614043c1c01107440106040c4200703000341408013a0b031a105106100751000305400610501c031105298040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 115652482 1250 115651232 115651243
    0x20d06020f0c0f07050a050906010c0605090f0c01170c0c030d09110a240f02150a0912081003020f0604150c0516180b01030b18040c050109050904060f0e0a05 69
    0x50b0189200384184000c8000c00011034000303c2d04014144000982801d09100604d080945407030b050100c130118040000310b9070b015951140d00748500900100c482080807e241410078800307141481302603500b03282c02d20090f011556200840c0e654a0f69507200410313255103548074100a41c0241c80c9040001000c0103074503200030b50a800c0032507007680391513103030b42d500d88030b024025083d20001505502c80e05040c03400707800c04900802480c016128480107003011603490b602d0440c1c0f1041c0d401d13902c1e10500c08221b01c6101d020310f4590249400c480c0c0f443d122405c1102910315000180c810f011540d8116900c0da11401214080c1140065070000f4060b6400064041034095008032050b0156040850b00c007101e4600d81070485126207085400c084281c40307000c00a040c0440f2540c101512900a00b001c0e0315400303940c0c0c080702c15100c1c9029141c601030405802d12680364100a04202101e081040580d8420103d03c0c0c119030000300000b07850441c5810300000b4a44460b62880c5070291110000034003a000c40e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 115653732 1250 115652482 115652497
    0x30e121615021c050106020c0d140703030503090708012c010f1a030606240304141510050603072c09010b070501050105060306030d2304090204051003140a09020d06020f 74
    0x40c0310b000b543d400d00c0d8120940780300340036a1005031302454034001070745052000701c07500034001d03000048510502420541003007225001940810400030600c09080406c00c82440204003541c020031034a5059454103000c10a92521f8240c80c0802d2001d4442004080d0b0088020381a5141c0400400034802c4100c12103d0104000f14030034000c41e4001035807400c14100e080704044103c1541c0000c0070040c0340076032881e080503009440e0703841080c0940c0c0c41c11904000e480311303504110303050301907034604800c11211804454110900a0f030080c020300c051150003031604800c41100e007000c0c9070b1041d1400b90b804000d80c4030301242d81d0321003245000002c00d00140d1005048a0b40610000d10803a0780f03400620240707210513141550503030700048005814074070600d1001200c141036039445e00242c02400d0300c045140c015801400040f136000408000d24a00701410341c2444401c0d0505020702d10304031407194505c3e000240f0180303405880301c2102e42103680c0c0d036214401c150340c00502151207000010004d50b56411007072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 115654982 1250 115653732 115653757
    0x9020d09110108010623070c0e0f1b16060e01090606090c02011107170c01090b15030f071406040f09020304060513050604030302090105121f06030e12161502 69
    0x11002140382d48540602c9058549a448401c01c00d2482c1d000b0380403441c0c0c0d01c654860007500500c42c8000085403a00b111006000c2c0190740725140c14140c400c000200c2c40a0039110720590310044240c441c140f071000740e0302c00c034102c517001c06c3c00050710741802405090240250031081d40b030101d0079802c0046e66030100040d1404000204615810410183e003290f002e92103074416924144a48400565211a0036582d454200042801c0220701c210708c900b174403500b034801c640211b405402c012030508400e0010310360030784c101d0090180c040100107580e2581001e0164060210300c85e00c040c80f682d12480c1c200c500500030403034003200f2a40e40c0d0a200d0000c1d0016201241c8040c02c02c0e010907030503420f000f0018803071500076003d03007240c0c1c07120795003500203501003014181440003e02c00d1446e010b2030001d00c9445484000c00080d41c6003003684024410b610140c01c00740605180000e60008850300140e0300d680d10101261082c0c0c2e03118400c161030400103207510014205041c050540c3c58a502e04e8024019a03820f12 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 115656232 1250 115654982 115655003
    0x501060509091902070203300301030803040605071b0c0315020309070e130803010b0a0201111303060e030c06040c2108030a0f0908180f0303071205030403020709020d09 74
    0x5180844980c881c0d8020386078000034102c0400c107600d41c0141203032080d410a0500600d041140d601090410000c002810950f00b0720120940e090121400603c07594040006840c1c44d560442c1d13100741c0503020140000c1c0c066170b5614002a40c00c0d0044140347e0840c0b002a0300040300380310341d10340119841c80a00045980704003103c0c40c865800c556000341c0340981180000340a600341003245112161400078810400020508141c2c40031511200095020308120990103581d40081c290180c02d40b446030584003040311003004000030080080702030704140c030b074001404034100617449855869809100f448042130f0050f00240002c00021001c1d40c804c4900340810f6107074412003038541e02484142002c02600b0401d04000140f6130262607840f401c0c1003141c2602c00181d140c55620794000366009038504e10010922001900d215190002c0602e8200e9400c4004615000041c0c0d40c1e82d8034844280ca07044180080480410304050003480280c01a18001c9411034660440000480141948403001c0c5c440c403450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 115657482 1250 115656232 115656239
    0x5090d090503060103030503011802040f0b04080c01081b16080d0209092d0621010b1302030103020a09020a2001090309082407200607260708040201030612150501 71
    0x8a03d0300c0c101d03034141c0c48850460b07190208400c0010f1840c00300c030409950800001ca2051201100c050180c03600f01e02e103640312414114024a800d090b402c0c014140030b200020040c095880707085482c80100b484542d25291050ba60b40d41c109814610f00041c660800895000d44008041c0d0280c000140110b07103c2007943c4400c035400000098404c01905000c1360315001c000d00000c51222550408030150484520114003440e003031005250124001c080c1e511045142e01c0d07072404007503400803030000c402b0851655141d9030001c0c207440190f03c2000c003020b0700440c01d0590700d8010207903100d203040301a14060820701c4080c1d08038000d00d40380c081203001c603806000218501d900000e840d90101d01450750030302c2c4d414885251000c2100014101c030300300034a08590121594070b10501c02258060040100380340d01303290390040c04045d800007d1006200908139401406100f44a100b80c00034500c1c103252030151154001200509000e40040c0703004494480d0000811500207051030011018207404c103c10f0f600c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 115658732 1250 115657482 115657489
    0x60f060509131b21050c030c0f040c0318060c080a0c050702010e030c1503010905010b0c100903090512060403020d030219050d061707060905010f050a050c010f05090d0905 75
    0x141900e000b00c64480302c062482c00910343c040c0003000c259000c4801c0e4110b696410904400d0309580d442d40298416683c030381c10411400b001014a4190304038090f0901220324400303e00b203401d00304030310307841b03607858807030110b1014040c1d40140c07041403054144502514141c1440c0d00a02140e5a0800000d070310a40068800040e40c03164040c001140d03901d031032034441e0310740046900c1c0d0f1000300303103503414003604401a0b1180d0b5030344603060000e211480e800d5160362600200b4402c60344144c0c022600f9200410240807644ca010560202c0b0a8030301c0c4d00041c1f40030391030030119090134190300015000000500000060400028041d110303038800d0307084924244038030404409030701800000c4400c0b5104c009803182002d0144003c0c00c140784011200280060f540c031482510203a00740d40c5a4880c4c1c21018050000960116050000e0002824010501d0318010b02c0200140f0551740c14a0400a002c900301404030401e4010240c42d5020160034481410180c83e04e0f900c030140300425001140030524000b03001d05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 115659982 1250 115658732 115658749
    0x509090d080709030f060e01110d06060e060a210209030115080c0d0206031801090501020a0309030f03020301080601090507020a050f03090406091104090b0d0c240215061903020409060f0605 83
    0x1d90042c8400903e1201d6a105d2015110703034031400006540383c07900c280081f0309d03030380c081e0000a202c5e240100c0c5040c82c181003e03200405d0184882c0c0115410481c50710340300d400c103055541c070780f4100d0144825900310004540080c0903502c181031b415402d003c800303422140669000b00540300c150042c0c5404501c0602009130391011054000c0d00400188006048207401e045004040230084001050701ca42c036540c4e540c01c9a21801124001c2651036010405056201420060b03040300f0741821461541050315441c0d0710101407180850068440740041d0803640b0a00c03c0b0b400640d070040442d5080c07042d0002c610307201c1c0c21000c8054000c902d40800000d02d0440b80c02502c10308055003c3c4d452805041006103c080d00b100c2e40500d40100c000c00400300003801c03d40d03044004151000c0c1c9080d030340038011200c4960b43d40c2c411940d82154021182d0100041c9c2c680c10040d007194003260003a6411005001075001c144803a400030358090f00e007185070018000190419400d0f0a032a100410020b5250000c000095 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 115661232 1250 115659982 115659989
    0xf13030e0108070903060501090c08070c05060103200306041406130804031205040803070c060f0806010f0f030e030d02030402120a0503040b0906040504060816050a0b0913060509090d080709 83
    0x502840030900507500a2448036081501d070f19050303102e25101c1d20354170151030080e4054200b03199550180c1e4a17080e480180d294200760149040c10b040e03400d43e01e8a599400c4103001c081e24006584c103450f0140c60386011048000000903007541c40c03614140c10012450016046c1c200700750701503d40044c0c0000003618006041652001c860b5003031500f1511000d07400718161740b8880038080304110100312810f00704041d02c00c80d44961040481c1d80c2c02c050008104020002040d07050110301814031685a030011624404040146000080c400d0001d000b01d01270035065003000c5280c0000a00d0548403070880e0000d502c501d000303844900c015008940480d584840d84100a4001d030400d01c824805100400c2c0142000e4100800550034291106c002400f00c03131880c0d00403081544000800c224441500980100520044075402545c5103841e030840c0c42880381a080c24031070600f00d29484041501680b0400203850b014107450441e2800b0901d0750fa03250100156440400c3c0e038840090403041c070521501099 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 115662482 1250 115661232 115661237
    0x6080c01051c09060213090b04020405060a0309020102120c0a0302070b04080607080a0905071202130b090c0a031b0c020a0b131a07050d230405090f0402031204030303050f1303 77
    0x70203a0398001c41441c4502d081407203070b980d601c82c910740340456810b0000d80b0410300a00c005155491501c01060101d40e030f041040c80c01140140701c20001c036690740302540c4030103a03c4d05012451103903c5c40100d050205403180e0815150b40856520a2108001960b00d80d46201c0c1e000c42d90300c40c2e00e80d041a80c5500640c0f08000c40f9a10800020b41201c0c0710341c14144d0010710760000481d050342956101c5042c24019000303620350f0072034242d010082d803410740b03a00c0820303c078054030801190f0344000105d10040001805000381000008003030a566100382d10030b4152000d403034581c01d03103110660030051240e080d90800340e100d4140d120b00454078002c14011151101c3e007084c0c50501d03079031520050108400301c6030000903900f6018080340011030024049a40c2d041805d0303442d00d0503001e40c00c1206d10100c4400e042d543d1485800d006c10b00460f115194050342040403503400307041c80c2e5a584002403a00c240c0e104460000040801d002080582682105000e2145001081c620343e56183c0074055105410341e01500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 115663732 1250 115662482 115662487
    0x40614010f08090c01030921180b0a0815010e040203010b07021203031510270f1703031803070203030d020c0607030b090a1e0614040f02130317070b0f060406080c0105 73
    0xd251b020764403036000c8920440c01402e032542074a441c441c035902e00800020124500303007111103c002440322000041d048110605040200141c80145040b90007494046411040c07591400e4680c000eaa00518580000340295a42d41e10741546241c2604032030b20403802900005826542d090000c010750340704500701c148100d02162101c04001d90f03000c1502c01001032050711000049501301144000c00d41d40b00c0300c41030b42e0130b030ba1901400441c9901c0030b80c40004404950300c4110000a004001c6a40003040c00e00d420ba0143c0b034071000241144100c280080d858400044d1005c0c1007035445d0050124281100103079429551020360a0342600c02c14000305030703c224042c000508660555200302c13044a0401240500c203031400c402c0c20100d402c25003108480c00c0c006440b50140b4a014042c0e0b00004440403801e40c00c0410340100c0c04100b80c414080203190800141c0040c0780042104191452981c015191409a00741108561071421050742c00b0f83c0200e05004002c1130325030001072080c42c0d0703000c10383d2000e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 115664982 1250 115663732 115663753
    0x6050603070e060708070b04050f1b12070f0609030c05030c090406050403170702070e0c120402120a050703060f0507090e060f0117090d08070e060909070e040614010f0809 75
    0x8408042e00700d95254002014004200400d0244001d03122041c03081d0b41c242c1482c02c0c50b08240d0716000e0385560300d00865101940c0d00f046454900c260880300c407010780d60074507000c0841080909010f02034209002c21800b250001891650002c0005c4c2142e00541014002d039031104207058903402441e0010340c0055021012400041160f4041903210380645404030f461000c0d0125480c006c03006540800060303201c0c0c842404681541c0e000ca603004074107111014541080e400d8401c00220004001901c41d800c504046007604209001c00700496a2050a543c4c0f1981c4a00e08031000b401b403090b990114519141c002640076008884c0b1030140c0f58040303220780ca16510a01001700030480c10034068100151111200b079090700072751101e40500017030406884d00d0500c8103002000d54000620003420014103e0010002d03803541c601316900040c3c15154031140740d661400c1601c81424807030003c0d4011b0b02e02000000e0346c40314011091410300c5d00340c2e124104c0104e0600222401c00c0140c4c1c00d410260401c4580030b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 115666232 1250 115664982 115664987
    0xb010f0f020d080a0b0a08060a0c0c0209010509090a080f0a12020306150c0f010e03070b060910090207030314090c0102060c0a080f15030307030f030612152703030911040605060307 79
    0x86500c13800002c00801c213280201c000c190b41ca001e550228031140d1140307041c05440b1409000720100e00300c2174038012660764225000160440c0040c420305001e0454540460f03103072401886000a000e03046800039035a0304075000c2d102403652194901c031001a0f00c840400c00f158485000700c0e800342074002d05030140328030200c4510245601c403480403ca988280c03c0700022410082c0100380c07643c4101005142c40fa852390426155180c0d0040c140e500c20810842004101e1141c900b1030070586061410050b102d26651405400030441c8501c003240c03c64004c0100400d420000403d055240020fa0030342c1e4540c0c403620540070480c0200c4d070b0b0080200d40760714006010f1703070060390b9150f900030014020309589007034201c0400c0c210707030082a003980010210504c1990060b018019030000f0005142c080e28000d4080d02c450140c00303500803443d51001d85808484244c02e6900683c071079015450bd00f610b0900c103951030064028001e91404482410044203109c2d558a0644100400c4840140030b540c5540c1d1121000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 115667482 1250 115666232 115666247
    0x1030c020c13020d0f051b070506011502010209091815011202010507020f06030c0706050105030c06090d1703010611060a0606020c09090709050a020d05060904020f0111030409020307030b010f0f020d 87
    0x1c090300d05a0a01c90a04e0601d5a8081c21041c106410741c0010f003403d081c440601d02c901c050303003a00443c120803c002000a240000d1541c111500c0684003918115940801c0340a0702c00c10800e5903200184105110405001030040303605601c000b41107400003886d40e400c407103000c0c0003441481116150300075a0340155000354021312703800b0b10082030720003200803010020301e007a001983c20308550139002c00c2000401202e0b2040c94050300e0114001d203081c01c6c20500080041c8207243c480c0f4001c85a00124404010a00100100c09000c103280707240c50b036840d031100400b11a5006140b8801e44200c001007070300c00b00d143c403844047c4c99407035000d0030000c07290070144404414040c1c200241c42c1f05404000803114840e100b01400f403480c1640141c1d0310591044484261035000c1d086038410480c010611005a588410040040303500b801c050705d030b11b441010602d00b0342c01190702c080e584c03600000030092981d80c581e10008810409032a0301e0064100320b0f00855071407042c03000040259001072440b44890780103c44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 115668732 1250 115667482 115667509
    0x105070905010c1410060501021002030c031902090901030302010506190b040510090b031003020a151205092a090c03010b07110d1406010806070507081c0b09042001030c020c 76
    0x8010b00d00b54030751480ca00581c0c020000502c0790ba1b040b0500140d070303060004e0203034001c040c2030542c2142419032900e0485d210140c044501c00b040300040454400e916015103603c140d00402130210340d80e5a081c080c0c06001c007201c029201e0316000140840c031030b51003101c0000b81d950050300c40b401c20b41014184200e00c3c9100740c0080c140107900c0c2c2e0011700c107500400214840c03580f2403c9001c0302071961041c04007221041e003220710640040201e960700b540c0d2041c00c00d111700c501084081850740750710303030385505016a012000040c003400c61610011002140507034800c14030241c544480c255240384400305c3d00d000030300505da0004410448100480e11402200c030900c00014062b103060819640c0340d0007034009111036010281c100c180104100b0f8410b12941e640440c080c1012441d02c0c038160b030361081c10b2040f0b6100f01d042c1030b0705090b0803c248000c1c2e400301888040160072030b00e031814141840009500240b01b0410100082c140b440d180d94424002d40c407020245400404040f18840c041101100643e80c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 115669982 1250 115668732 115668743
    0x1207020409050f0c1905060307030f0b0316080c0d08120702011401060809060702010c02030f390705030c0a050d110405010f14040b060304030810150f020f0105070905010c 75
    0x2800072011900c180819251080740c0c0005100d6080110305203c140c0d02140d0180302c9010418104000340d4030303040d0859511990500d80000c0b04804500c0d040c004000c0b40360403580500c0340d030404603094820b95071060306480310001160000d42000040081c811201000245804018010119a1a40800328136007003905400045140b801201c0901941d820990200e0001000f171814000240c0c4140501500300721345200038040b01e030741c07914061341c2d0348901080d017085141c00040ca028403d4501d294040c48040f0008902201940c4072a500310914000420110034021801c0000c0c5c54580003076004040c52010f4000c0004034a05006c20990b1209990152129400c01c42d103420155036620449000e0282030040440c42800c01101c40134a00312089420300076440c100d20810a80d0311801a031364096494640100340d6947c00e0411980c141e07180e400600d080031010402541c26400c146001514035a690848010b485c6041c400c1e402d13030340143c40b0680400c16685050103154840d004c82a03082d070041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 115671232 1250 115669982 115669991
    0x209041e0303051f03020f150405100504080d020105250e0904030807140f071202100f0203010e0604090c0302060a171e0f01030809040f11072d0512070204 68
    0x1500001029118901240025990b20410440f60344404c500581074909802d09031a80c2d06582c003280e111101e820201c1c2c8039a15042c1b011400040001c11503001e0030303001e42070340301028090320040c080d074129024081041c0108292009001c0c41407040a10640200520700c881c121102101504003080030001341c00c005808442100903200d541d0480e000c0d0344203035101c3c08585050321004026114121407080d19000c00c100b14061001c40409503070401d5003051104501c82845441603207403095000740100321604103d90b500c1900e005501a41c1218003414280900d0b41d00c40040104442c64488010140352202006101506015010303080040305030030100c0c480c840951034068002c070304542a1000c4008160324840e0881042d0b0303e5500b0510b210007000c8039504690ba01ca07558000d40780d28070301440d59003401c54103050300354004411141032500d00301e55880440c10400d50748070310000341c24046129940c0225485000000751481260002c000e005a81c403000180e19183e0b02c0542c00f0b9a0141d01c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 115672482 1250 115671232 115671263
    0x30201082809021302070b090f0706020c04020c07030b010f0e07050901051b071701090507050301151e030c0305030a1d0109060e0f04050702030d0c0804120e04090b07050901200703020904 82
    0xa100034406c2d10b00503034041d40c1c10318103110702c5403528860500c182c03010b4001070000c0011a40000d1002440700b0100c50140e1500210781c0d40e43e2901c00705a20140130f1810081c0000b452814200c584001d40b413407866950421f5a40a4040c1c2d0540b24040c01e140c0001c500700488009050101d411000c43c654440650310032541c0c40c0a0640c490700c2d03040601d00380f030355200b0005040140800c000001004180c00a00c802c0300840500b6000c0000c52082e4645000c0fa440b0940d110080f0710049800356511507065980152a0b080c0580d90381c000100c80404140517001c1c05a02c00704d80c0c3d030040e8203840140d480051103420040202c8980c500408016008000c000f0400c56682d130714015244942500e50045855108140e210701c141c6030024450414070a00906100101d40d0740d0a02801c01035260518803c080950380102d0000c003102000506602105824000a140d00c040142241c02c426a5200d140421110828078038440d017210007035030b95004280800c010301340510850341c040d0190300d001d080741c400d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 115673732 1250 115672482 115672519
    0x4170d170610170c0a031512152a0305070e06190905030a0308070f05070b161209120908070807091d01060f030c23010e1c0c03020108280902 62
    0x401e0351001401c500100320024003d0749845070b842c1f0300c10f0010080d0105450906030001210031070001401c00c08100301e44002c0c40809400c2072501805110100805074500010001d4104200842d400040c1c10000820710052142c90607100d00341d001440300d46007141d0485185443c9170740300c51200602075010b00000c0e087d5420f000140e03c980c082d40f00c1d141c1c1072510380c00007480500a017520300300b4000184101c00125151004c96070384003040d0030614008990081040d0f400606403d01c07440c0c034904003400072007000305081c8184180d01e403640f6840c1003c3e480c4c0d4031050700c44259000d04003c5500244003002521910b41203072411104013428401c03100c00301e841d01c90a580854101c400c12180a0b0700800c10488500400b6000f040441b01c14540c2c03000820a00303400240f070300005810055a042621050340c1e075912580843c90301d001a070200c1250720b1400c0e5501e00c071144400d13030219925200240c1000350411001503c51704c1160711082c80903065030410000c1c04a414281c0c2c018a8030b0381c1c0160003c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 115674982 1250 115673732 115673777
    0x1e110a0c0b0301090c1b080306040b04050a0c120207200a0b0403050120040810050a060b0a0801031514040f05120309011506050915160804170d170610 66
    0x52501c801e50741d035810300201d03100782c0c1d500c43d07407450400200c5c85030b020410f0110980c4110706940103180030340e2500c411000030043c01c40200181e0340b151801050091442c00c0d03a020303d41d145c295071a0070a00b50800c01084040f03018030308015003000300c2d446018000a030b01004507520001c0c0200b0319140103440301d242c822144c101d50811078082c2e40d0f4024010701110007080d525410980c042d4843d1400341061101078941c40c1c150600d050194440004c549129625003152001e0842040002e4a9400742c01005140050a200a40301d64003402004055014079001707401d8031242900b40c08131607031a1561030442e40d40d14020300b03981900a2110344200c1000001c029409128400008901e241c107032440e1b82c094120a82c0714070144081009446410f4aa25264140b00000303404220b44a00703505494030300c000d545c0d01d070040684600080206000c0101402003052203110f404841c1e03d18903900c0107036041c2c00f40031120b502100d81e0390000740705464520b1690603d81040d203050b200c1000500da400f071302c45 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 115676232 1250 115674982 115674989
    0x3080d11030c0c211b010e0d0c020103061a0405010f110d0306030b0601020610060516020409030c0b0a15030623070203030117060c0d0c050c030304030e09071e110a0c 73
    0x7810018512202000401000c5002000102000c281320b00b40010070f552441410342c8818a1200c1c119003c0d485c0c1820750040541c4a00e201c2610800032044000402e07501c0764000490100703141c110080750350003254840000c442c84c11030089182c0f0741001c0055035104c004d1410042009500481d0718500b0500f4005590306c07103440c0d01d0202e405411860f042c1828240100003a0448d449070f0b0410207890101c0c1010411550182422541c1d91440b00071540c500c901401c010350410301300747c0100c04140c2d0051840c41100d0045d40038250780d44981400389c0c1554640d0701251200e62401074240040740641e4824904440388844c4080148000c26030b512515034120f6000d03002d40c101000410414001900c0480020141c4000c0d0055140c030300320f60740c1c4500030b8030b20400c9419a81c516032607d15000c1c008882c10469058122500c03031915142c0148590f4102e911795000d148500042460240954a81552146044010f0704180d00401003100c040c82c0c00185e40c015442003920480124810400a0300503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 115677482 1250 115676232 115676251
    0x11040b0f0a0807050703021518010e060709060207121b180c18050114072a0305070b030c0711060f07080304020901210f03090f1508071803080d1103 65
    0x107400c81c8110103030402800601100c1070050070008000025070100b0000103280d400000640d86032103858400400091120042c0d11039840c00c800500b4814001501070b1140d0800c0d51f074020242c1e10b442c0e00700d0319545544070342c0003880f00d0340c81310000203820303200c03481841943c0e03019080b0200c2e46e50310345000c06901000555038a43d0b45002d0031482c15440407070a0101001304204001a6290500080c01a948a5860f400c41180422001c080180407104039052400d01c00700c41d07001c5401c150040c041d4070b02501c001c0712144108480010b41052070f8007038900c80c4003901304050503c03070b56890b50140c1c0404105116840401080106403800a04010304000e500ac1c4914980341e260910500800c543c1c183c101c2d15240041c072000c10307000754244c082c2002c0c0760760244603200b581c9c01c1403906a984650b5904040d0340b07a04031410108148803c0e581c0c0c9990501141e039070764a2512002d40584e400411a6070b400c55078ae04ca41c8007800070480241c000c01c00152040800136500c1da24055509031604165002c3c140d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 115678732 1250 115677482 115677487
    0x20a030f0f050405012a120905030301060206091009081801020705120c1903110607060b03060f090d08150d03020c09040b041a070c030c110306040510060e090705010311040b0f 77
    0x6000c806d11442041200ca80403441d05a100e2883d90b107817210000b41c90104114034072001106013003071a00040142d03039100c030880c2d44031b58450002139102d80c1c00b01c1b0084e60a11600d0b0f01c20400440340d01800659a800100751440c003540d81402d910f0410000f030503941584160341001459444450060341000b501101801100521000b0080618658030400e050501032681c14004100986e10703894515404070392072a42c1d900349240c2800a811003600c1e0680c1401010200950480c40321002803141000206540803501300741c2003910010400c2c0c0303200031842559540c50b5058103066480e40c072003900a004642c50300280000280501808075000c0304d207203840030107100030001c6400102c0322800b03c030b50601c017192408101c01451054a07550250400c200c0c24604010700114181d4213001100c040d055520528003401e2003583c072802e01c034103400040e1803c0303c0001c000d80e000c0314281c06100041c0103032980f540f030040110040e210500c03c6156551040000262030356000703000344503113001c0c3c4104e5138 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 115679982 1250 115678732 115678741
    0x91a091003020d2d1d030a0305040311150f0604110c010c02010e030f0a0e12060a05071b02090612070f0303030902130b060913020c0d03240506030a020a030f0f05 71
    0x6050302d03420b4800c0c0500f103101d01440000d40c6003070502c041c4e40140005000440d03100681a0103100c205c2c11611004a0000040e600c54641d41a04640d104034003a8031240401000d6004a950720a4100c0c5c1c42c41803054400e020944da901214501038009030700802c00315075261840c400f8070b00c030f0380f00410881c550b0399104002000b0341d03020302600008215000255041c03100c5c0001c1004180310f80f00c0614104410b03902e80420035526000301440b041c4c802000c4400d2490b007036074804000c050a17101a030205440b004160120385141c10044411507001d01864001c0d1514010301c544203515095000307680c002e0f250b01003000c1100700906e40046000781d50101e043c4070749005006007100008481800c213400d00b14054901d4a59904441c2018810380725110b004120003443e200a0140302e03080025401039500000c0100e5040d080408120300c000c442c075066000000c52003008110602c14150805400d00018102e202c996016184a20030380c240410300100f076414101c01c0703a060700444012942c0d00c4c802d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 115681232 1250 115679982 115680007
    0x60e0f16050109151b0c180e07081027030203040e0a02030c0307120b060f09031b031213051c05010e0a020109050609040b0d06090203061303091a09100302 68
    0x400a00d802c0c00c0140f212400d2041c14501c0c3d0f014005448144101c003a01c1d8000c8152901d94800000d4015980000e00d136100e524800300100c0105202e441c050502c00c1c41e10000d0004690042150700c89002842000d41800c2c20b0400390041c196224250000c0d5101150403030704082d03480004a201c0d502460740c650418210841070304000d001c0f0891a841402002440075480c011290080729508241d04c122507040d08080c094000001c071103400a1001c00c0e0320f000410304030701418600c2000c90a545070707034020301607038800f281014100e50303495401036103200b0320b9054850003071103000700780c01c070a11140d42c98101050515050301810108030b0010740d00c640a00c582071150b042201d0001d0003a00c91850703942c000902c41005030041c540304d40d030b00107000e186555032580011404500a0311044501c0b80e603082109c0181601c800c1603000740118000110f001c100d14052802c2603605071101000300d400c00100b00401546404c2203000329000b00140381450b1344a090100700006143d40242c3e440741200e104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 115682482 1250 115681232 115681273
    0x9010203090f19020112020d06080601180203040507030204200a080f07020c09012705040501020a030b030d051204140313090b0a03230717070905070903050c0409060e0f 74
    0x1211600002c3c01d0411a00381c10300300c021902d0b0240380002202d10f0103540640240300b1109a181d681d4a80080061482008600c0030b0403515600b9105080d42c0c14070b84a0020391208580003011600140028070041c60507034060900302001c0040d1414100107151038504684c040c11500001c10090000c01400d4031081490960240d40d03803000d444010000000318485080600074042c605602c1c00c0c03050001041e08944250480d0305175010b00140c142800c0640c001d5001d05005000281440f200d201c1c01c0c00c0c00104000c4070740700c81e55414600001c08001040791070015000b1604219140800803000000308003514266400302c000259451400031802c0444600840303850281d03130110800c1000c566190380c218814501c03c071000fa1a044001100e030305108554104c0a8108220040400c1499002901005583c046c4004024030b4079600025240c03400742d444020101d1340410030f8401340e424113410902e000d070310810002c100103141b4098075040070a1030000040c55407004800f000c3c00c4104440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 115683732 1250 115682482 115682503
    0x30b06041d0a0b010e0f2803020a0605090a15120507050d060806190e0a080c0a06060608010b18030705090109020d0f09051908040308071101081b030601120204030b0901020309 77
    0x504001043e002c0d030010300300340312000f681d510424510000034001c0d01d030420709441203008440d190400650210340c406141055020276030041202500114410340142c0448052a0009081c050b00302d1601d01c0450a84000d503026008004048502c6024000a0700440d4000c1d90182c44e07250700d8404643d45242150721a911450842e0321038000d01c045818440d403807103d141c0d640300000c207502505211151034090ba02030000c00451001400300c60701c2201194840c4480e1045d01c05125656440b50201c0c0e54002c28000c00031681000c100380ea1504200d142885c031003c00160503244250795880000d46642026407184189a80004050021070303998451303208540400c00040014040d0360711141d070340f925140106a40318031041c10ba0400d0141050a030303002994000d00c400d9940003a1320f01507104550100352540425101c00200c1d0400501040400b22082c5081802d4195500c0d6801152400c401d801740d443ca165082001001040c0f000400030301c00c940140000d640c03402c0c4036900c1c5141020031030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 115684982 1250 115683732 115683751
    0x18010806010503150a0503031908090a05100903030b090c040f0905190510080a110406080f0a06021c06090b0102061803030a05071709060708071419030b06041d 70
    0x141005500e0b80c108080e00e8000c0000309804c603680c403181c8046103201546400130790780341c071001c0b0700004001040001c2c42820000b60741d8650701500d4880b51103030385070032500004200360084240c0c0c0c620580d4940c00a60340e00d009280110b4400a88404101c8107041920a00703411440054140f08480c40203500d00010440d503a001c01c910705e00810710080400c450384003c46005c6e256004a00d95410b600c0c02e840140c8611b2060394641403031480c100810707c0c1c010007000d00a604050000820241c0410308060400440c4098505034455a070f58000962001420009555032004100e500c0700c020700c207036005801c0100307002a0640c044000646030600c001c021402d040c0c85180300c400d107040044290380d00311460000106580e00d80300415954041c6caa82840200030041e82001102c07000060340e42d004102a4461000a13215110111002503800303044e000000c00c10040540102150001034400746040d250010341103002c5c000207180c40c0e00560000d4814160454100c104103d01c0d00886d41049442 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 115686232 1250 115684982 115684997
    0x5100306140901050903090a05120a151406010c080702010804031103070605010305011506050a03050601030f0509010f060603110a0e0a1d07080a02070309052202040f08150906010e0403050f040b1801 87
    0x1c0c00054248d8a0364080c207800703001c0604d050545500d00b0410781842540c4480b407401011850240c11004146183c01c01404001d0071010511a500800a264026030442900c51070000035400558810350050800c40400101c142c103070b011b85200b440a401450300ca440c0225283d45141019401d4499480c0d00015000409404101858206084400024042c01d012860740d80b41d10040c0c00401451100c25441404c1000700300060b00c0640c059010030300700d02000c000a035100c0c0b42c1101151306910300026251010001842034034052181000d045c000205020b070510780f1168645c8100c1e4000791551310072540c40082c40700c002e412034a510340c043e40c520000c5042c10240d88009200107124800c0d20b000351241100512440c8014081804998113407005554503552074980010000052042d10928018400262510301c03072050614020801000103000c2a401c010082400d20000343c412400e0103001c002e0102d40d44080030140c8018907064040395181c08498144150800e0110019810000f04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 115687482 1250 115686232 115686247
    0x3010c020703021002011104060e040c02010614120309030f0106050a08060f070807030207051e01200711190602071d100b03060102030702030609010204170a08070605100306140901050903 82
    0x60303000480b5011600ea140304d0041c0b0906074018201c0b515003203041407000402040c0036402440440024405070342c00c200300c51044400f242212401e0164804200c003008031601c6916200010740058820501903d103840fa51342c000038070340780c0d01450038845130f515644c04000619151410f80018040c0801520140c94019000c04401c0c1000342140148450040854801d51007070381a0360083e03600104031450004902d46454602d02032104000d1258241101c04c2030061421050f01d40c041c0a26402504084042d5140e0341d1a0003840415500405041c101c10010307100241c2c48401081c0d1a0054410181001ca200038008014010403082e5002a070034403012284481d000801ca070303590b20031030b42c9139122100101e0861041c51070182d854807508080c0f00c6030a0341940140102d503100e400300c180c41000114031684031074400a003d0701c4503000380181c501045168105c0c1350b00501030303802000c8032500c907aa8041110b16400da20840380005100b0025401424414a074010118100a50a0403903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 115688732 1250 115687482 115687487
    0x1050f06070b0703020703030e030705100e0c0105161e1109010603090f020d030210020d0e3306010309120509040e0304050a0315060801061221050a180803040602010b090603010c 78
    0x4041d01000130540e00194040034148a80e0203407a00000101c1541d980f29030a040c11980c80391600b040819544c94140c0140314040d001805501c0d10b80c06031902d50610356404007034101402c8801007a507592907030103018034a110842c03039004020342c032031410407080c07040207001e0000c0900d05070043d03010b00d071a1000980208910031031994505038121000d000b030700960f18040303003800c0c0448140c2d606c15001068292401416070408a10010340000b01c684102000c07a03080038290400e01c030300901c07034502c1207070030b040200380a8002d9005a060601041a0307021355100c1c885200101114400600040b5402c4510b1505008541100704001c00660905080100150760000c0a101c0140b0b909040e0352414507180b1240c00071070092503481f00070411569030340c4286050300d8000408458841007000954800341e0085c14a05004041d66900d6040c5603038084182e1785a005060340403074590b040b0100280b41c5004000603c040e1a0075400450034014507000d000c900c1d080545003038880c0e410920003059150707 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 115689982 1250 115688732 115688753
    0x8030105040209040605090702030d11040f03080d180f05190506070e010311030405150c0a080109022b15080a0b0411120114061005031003170f070b01050f0607 70
    0x10340c211001030f911035048000078020505544003a40000b0b00d00e040003c05500400a0140280400d0003444540201408002c51b48118003c0400c010100f039404d00100d6007440240065806010b030000d4140c10b004a98032620208002c00c40390503100101c80c0c0204101404800000c0742d00c0c03402c12030640e140c0c0da102e545950006281c00300b0000e4500f00404140e100c1e8002d420108040e01100d6134a061500f0801d4907a080b40c6c41d40a04109000042204090180100c80606c40c3c103075210603050f42800b0101001c0c2d801450f48600c140ea0503520410120810482e0604248035960000388503503034428100030910b80c2c0c0c1d00030324480c0c2041c8111030100d42442d04c0980c2c0117038443e0044881079003110000392a0005030306002269843e060120540303c46100c0d515016610803164284c1e0440007800031140c6102c200c40d40380139801111010000614000c40c030b00c0140c4848801d0504002c810b074520f03c16500b08420030380d6007401141c010005410a04030b0495010000d4072030928081c0d00e91503d40c03008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 115691232 1250 115689982 115689989
    0x2191b0608390408010c1106130f0f02030319110106052215060201050603150106020d081b0f03040c0f050136080604060b0102010c020c190e04030906020f0604080301 73
    0x307600b0004882c054800c44011900146003000721a203641c0c882822034001c05a0741d0000700410320489000c006400c000402c1d5118241c07030424090141e0450361441b440803150141214000c0c0010414401030342c1c240040c0c81c5074403180b0785104061004003001003040380340b0711000070ba517403612409120b141c49180c07041c521100d4100924401211400c1d0f01c40c010565078038070011b4101900408030b0784580c1900320500035103084040750564055008a01c0184c1000c1c403510700076a224003412441c15000c3e000c010361005801c0c164259450b951034000625a0015112880f802800401c11040280c8005010060a81c000042e88114184800a80020002070780c007801405900081c034580d02012007251281c64880c1024044141d41300030003692520252021190305003003150f0025554030510448038400d400b5400ae000d195082c82c2401052180c803001220000419500400c11404010403940107500c20380e1006041c1d86005002814400c00c00ba2a5072260410303c1807201003a034000135241503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 115692482 1250 115691232 115691281
    0x8090a080f0403050d0c05120910080406090605010f05092d0405010b13020714010510050d02030307170703090b1303061d010c09081504020904110102191b0608 70
    0x80c0d4207450300154040c012903000034520310800a81a900381c1d0f100c6000a2941e210340c040b2a000543d02c89040440d0103011074040d000002c0800c460040342c405c204660b04940508400107141f8580c0d22050140c45090b00401450110154104000c1c1030041d20303d0707809103280d10440406400010074501031856660803d400001950104084c0b0000f9441401800d1004040d50007889150501c04080e421000c3c040c0d810542c00c40c1580c0044406003c1c00d4032650300900460303c15804c03c0d0401c510295000c50a0b42c1501c4144841030020f401031102055442c062100350341c0303e0806107002408049150032001868409116a140c2030310b04080c5001600c0d840040880c40003003036080c5d601210700100111280b0341c2009a50b0b181c007600481c14a040d6041482a80c00c1c052051000c80034030300f825500250000343c1d0100086c041002e40401d45010b01c0144155401c100e00d883c0c0580348180c03108000d43c0c00600526100f0802c400507400e210080685040c2210180351006400e040310303500c40440445c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 115693732 1250 115692482 115692487
    0x316060e01021c030b0f060c070303050d0207060203042006070b160302071506150207030308041b180e0705120303160207050406060203130801270c090c05030a0c08090a08 75
    0x8807680240a6103464000000e03104107100340ca200000d015210310700050340525400044080181091800c44010250310401014042d2a6950448076540210a0114090341c06e0054100154140c00114083c60081401c1c00d483c0310004019015001c1c0d0030051807040c00300304240d5000400c4a25400d034003c0386400303039801c4041d41807c142e000c1d05c40c110f0002c00309548115403580c0b801c81382e880202650102c4044050b126a044001d0740d81d59903030f02002e40401e90010018000903a003012031011a001c900c400e194040da1980e81042c4002d8454001d5842519841e009201110411030000203110464440702d4561400d0100ca85070311002e401b03107210454004803d5031441c02007040600800700034000300305641c3e580e00300940700e03046207903143c8200000220004102d03c4c140100c010b060094510103032080c0802502402c0c0c0c128240c1e00f00c400040174600000c40e03100c503104070000700d82e0980b22181d4030325010b48402c089818000c1303040c1c18800c141041c00500c2074005402285681c0c03100c0c01e5503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 115694982 1250 115693732 115693757
    0x103060c030209090a150906210609080712110a030503041b081f0e03090102120d0f0204090f230c091503090d090e07050a0e06090a03050f0c031606 65
    0x20702034843c1d002d090750810005401d104a80203164800e2039240c3c1c1031040005001e46401c0b146054942e1441540802091302111012212700783c0d00409800c1d106200c00100080250303602034403500030704416074424001c0c01c0f22541d0940c110203405114107480c0040c0035008007a43e0042c100e8080600060144400c1300d02001203501802c0e0300702d015010a2007224540310042c0d4a0101605a845928038010300f02000e09007500b500000341c91341c500c0141c01604020310405000c036550380008107038260b6907440b80544d8001840502c0100080c10380c00d44c002c1000c42c10155640162600040304d00600700400c8190340d02d00f44d0614a42c0c0e001254501700c039a544401e400051224181890125000e07400001804541c4a00151031584c0c0220307030300c030000500d42e220520350000034115828004a4402c1052071060340c4106030110b040800240003130308141400c1c0c01f10307094150f40e4000301d51a40c05056100060407003000648084c0c03801720002c0510703482c905012942d44019104141c24000d0084820 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 115696232 1250 115694982 115694987
    0x70602070b0912060c09011409090c0906040f0e04020f03031305040f0b0301061403070509090d03050a06090203090d080903070206090f010c12080a050f0106020a031805060f040302090106170103060c 87
    0x120b0409403e0811901039060941a0110310752083e051580071a483d0908441302c141d4200540307405043c018540c442d90354a6060043c22503100c407108031740c000750401003c965024a002640054202c00c612480c00d843c02e4418000c181c1f109422152007640180001d44030894040f00503c1514000d0b1350121380c0d914807141c8800907180c0c07000300310ba00d5403c192012440003c8a90303000150320341141211201682c3e6000d214041c64165130700841600142c90341e1400358003d40040d5005982c425002030a1399860007024126003090302c007460180c10401101403003581c403100d241c0d048480000510304c0c000603a4001440d9106940c01c2d1400b9440070318004074540e00440681994681100340300003440340b691002031441608584642c011450440030842c208004000c01d4180d540640080214031460384003910030340c0d507030221060029207024000c5080c1d00e07003c0c0605050b40001500030703103507400e40c41040100c51050b04003604102800e04941c45c015135840100d4116608800c00003000d64289004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 115697482 1250 115696232 115696249
    0x1030b1611010c0512010b030f0406050405420709030f06200301170703080d150b0d06060e030604020105160302070b03040c031e0503090120010f02040611070602070b09 74
    0x20007103076503e0101090907550304070000b4500e41c614415982100da8039005081c0c1c40b07000560390b90440031401c10001c0d00040480d444250054042c200700d690b007910050130301c9240d20408905500710003503014038110b00050343d145450303c00031441e501500d038a00420001d240403414400981a0305206480c0301c10b028090f481103203400c0c01c905000c0049134841810302c0d041e510038850700840001003014071651490200f14401520f500c111124030741070f001c41d00f040c058583c10420410034a0400c00c0010200c42410007040ca8210030007010a84501c0d140b00608541c09001c0718900a800c18010400180c0e4440111038481d03000c1146030300183e007a0b0400b2454020f0a4010349000e003000410f01c014007a00201400c201c0703108049584958209031410000035a440400402a9100780710440e001e43c055403207400c825861428807030b01c1c0d441d4801d0050940321101c06400d40d41d43d00003414000302e0350288004601b051082c0003024071920380031000b5600e01461160103d0100301040c0102d07241d550422 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 115698732 1250 115697482 115697507
    0xc0f08071407060c020a03021002130e190509010e010b010908121e210606070b04080c0a0203060f090d020d050403060b060c0109050c030705011b12020109020306090106051801030b16 80
    0x401304003002d9440c101030760b00d842e50081500580b184403003110300c0c14028000c9904071441d2100c010f40c600d02e03092800c80c00501c0501446941a506960842e01ca8014810b09226584140001c035040e04d0b521065800c50341001a0f0b0750403c42c0d000e80612401900160780c0340036211954059586d412213074910745110303030541c02031081c0346400500c4175986c6010030018481c0d42e9035051118025210700e010002c8a00c03e025008004c1c00c0740030000b5004c106e00601901d48811202e094030040a0b05500290030100101c503441c14040c02d8a0078004000c0040101030300078003160004003101030361181c01800c14047c1d840b00600a5407a1410b005650701c841701500d074040c442a0003401114414682161a07446820845000b8031407040001415882401c20f80310850729013186000c00001601c480c0500d0800303c02c10425076407604e40d0313400181c808109051180d42d0f44800090301070308100400420000c180459442d2610722070040c00483d10a1081c0c0c0c0d0403a105d2102000324140c401c02c00e49441aa0b01c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 115699982 1250 115698732 115698743
    0x3010b0a02071211040c050423030c0a0b0c07050108010513050615040b0c0c011d090a02280f050a0e1017010902120108030705070b070606030503030a0f0c0f08071407 73
    0x15042d004012100000d07041440045405106e4090140740440fa18092440303262156880401c07901c0c40304840600c030108620300501510918a14540416014005540440080d0100054000f699a801d10266024120901c1c041140b545844001400b155a00c0c2c0c213100c600380e40e0b07404603061780e450421441c441002c1c203e1554507155101031348421074020350303044600c0c4e010785200d07000703190300c1101e14078066480c55180e0008908a80240104801c005003440000d60f4200b09042e401184a502414100394401030040d901d01d042c40002c0401001c0c12540007800400d000c058561034100510700742600d416940030401010f40c01c001c9a9407050400c014958a41580010402d078100e03030011301c0e020100b00c450701c0c03071642d070b40784400e6491042c03000c00b03040742d04008420b0160b40c000c98000d0030041c2c0600d02c0410910b407a0386070309080d0360055442d0941c465941038100000445400b07550340301d94403810a0f80004009001c040c00b01500284150b04205612038040700c051124004d5600d0700b40c000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 115701232 1250 115699982 115700009
    0x1f0b0d030f1106070801090e01060b0f0a020f0601030b0109090201051209030d140408031f0f0e0601080a090203100203180106080105040203190302030904090f0506150f06040b03010b0a0207 83
    0x1810050481800348107034034000741c1c42a084102107480010082c0c02207100e6075031543d081c1e02e0300d03c1d03000c01065060650744c0507540701d000004003444180c7c040d00071550518003043d0384000c0804080e190039205201100b0507004000100b01280001c8801411940103203070108200b846440102c0704e51081100b103084602c46141444000e007800406004940981c2904001280d1015111240c4c100200d4005161681c1000010b6912903403180f10200700035030070240c058060301e0b11682d00464005030811501c3c0010300040082d2583d1240d0307450b0b0882c05104c000c00044909401090300e0304406a529081980c000010810b001c0030708080d000c0800060000b04182d41c0c64a14407030180c1010f54042c4c0c401d2003400c40d006148040340c3c040154090740b5070015454000400103110180000c9001a11200450306012022420a0180d544100110131010080481b03c0042101d002603001050340036010030710040c400c5210080031241550311400c0d1a5031540b100e51802c9150a03003e81001038003403c034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 115702482 1250 115701232 115701259
    0x703050d0f0212040c0f0b190306050306040302010e060f04050a02010e150403140714011223180d030b0105040b090d080714010b0105090a030b19021c0b0d02031f0b 72
    0x980301100d024500c150340005d000303a0307102142c15104595000c4d03003480c02c1c81000000550305004038030041c03607505802c2c08691259101d0000341400400c52381640941d44581e50081c11610600000ba0b010032007407921500303824540c0303400c0d9803649a4140241880300344040115980e862101032820113a100b000141c1d19910b0b403900103003250f00e031400c800e080d12800c0300100d4014444030703d00c0204007069541e036004164405003403020b82200d13246204d000580501d200c0d00c3c041c0c8845030502c00c0e200320080f200d100d24910300c40d515190382d89540800301803401c1d10b624420b81e03000f01214211038194805940700c0702c00703000060282d01410002804a80c1c009501c008104603000d4150201028134000c203c10813042c40155030b130384951040d050380311080c440c0a00029601119550f0060744e00c2c5203c10340080701440701c000b203900440070010200111958000c8184d20340c00b60034a200801d440c078940c520312a50120b40c0e14800000c0c1408a2668140c0c800c0d00000650b201c1004044000c1500401021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 115703732 1250 115702482 115702507
    0x5120702120d06050f0603040807080f040504020d0209030609070501050417120c06040b0f0c0906180d0c0810020c12070302030c01111305030604030206040b09010902090408040e010f08030703050d0f02 88
    0xf15441070038040d410240a00c62a03190060a0300c2c4619040700b03d441c50300f00c413540d40402c0c561040c1e04288005200f80030210305902c0e01d2029000c5984010307401640d03440d0304820140742c0303070000b010030700c084d400820240142d0341e2000039078080b12040c20040a5550a0340480e40c28440810f006415400c80810810b01a400010350b00d80a00e0040380c0082480e15018030752020400203c5030341200b20402c1018040508200008011401c0075403921040c410440c400192900304140d016149080d401e5020301a4440078080c2c00c0046200f0381c1d0461414000d03c0056413a0001004180b9075000d001c00c0220525000340304131500303202400000c0100e0321103c400100039800c11240201ca84800100200d4541400200075000d075426400600241e9119035610421141c01420640d46540b941c0e900c80041c1c07164029036005a21070404140c64900301040300d0f541c000140d10102e11480340c00c0040000c10004000c940d011505031409560320110f003001000500344016000c44280c3c4002a4241d5100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 115704982 1250 115703732 115703741
    0xe030a0b07030e06160507080f03130c080109020109170708101b030207030c021023090909060103021c0c0e0a05070f020706050d02030a090501060b07050c04060605120702120d 77
    0x2007454500b04446002c14102c1659450204c0d840d41c440e034600b5007810215405038000d0030140d0b1181c4400d625055501034a42215001510351901c0031144540384402c2009040c1c1007070203022582c00030021809143c00003404030382c2911412103403a40010f03100d840b40105011407006822407200301ca00070388442001d075005040a0140d4861444240200c4104603c00e00071039213000e425030b9a510400906070204164a2400100311090011041407480f1703c035802e01e18040a41c5280e51419225100c10b4140500b10100500c40185034005030018001a0f949507104442408681c040050380c200d03a00e00704500d603a41c0d0300010101115141006696485078000500c2804607540f003a00d442139405061343e13211a507024181c04a0f0084c050710b036030340103564040c41e8071218a00b404144400303640c0780c441c01c441c469040b10300c10307040005c1c510060005c10004a0702c0000305541c104040792400000030554040c614006503110141f10100324814402c02c00540b0407107a440c0c4956035841024420030091 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 115706232 1250 115704982 115704991
    0x50604110105040e04031b02032a0a03121b08030f040312111b0c100201141e01030b070507050d091d150d02010504121a06040203090a060203070e030a0b 67
    0x121190381030030540d407145003614203ca0351001c04040d1078940e65429207400110004070b400709468804002c0241e036041103901515501da03c4442d48526100d07183c9405e12001c43c4075a40507d4080104000243d0f402042c80064049843c1c060511440244d1502007000026006000d500c40030050100901b821803483d4004e42c8a501e80f401144400310009094410101d5000c10820f0284000784c0c13114803000001c1c3c1004000c0c0140c40708041c503400010a186888082400140c0d580c80c07004000800320700149401c00206901210f01401d03808809122000501001b400b00b0a144d02040805003d001980d024580c000300740c0f580c07514400d80c02020202c8502c5810914154a00d1900c0b040c0c850080507806100903004005808883c2000d104100c03a0302e4004a0400ca420440054400300340d031021802684a030703c440e00c2c021044c0b403181841550207090244202c0c41081800340a03a0700140440b42d05030302c0400941c03a95914501038440c503200c00740c00c5402d409411180310420180c601e119100e07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 115707482 1250 115706232 115706243
    0xc1e010b0a0909050a061a06030903041a0f090d06060b0a1e030b15070302070f080307060c080138040801050a15060807050726070c0501030203190b0a03050a050604 72
    0x382955041c8074000c1d120541c2000d80313903400c00100c03803000c01c24542080f000e803810501c828012034030580100e4201c1e80101d0b00c04060ba000403506101d20b015030065a00c005d100141c800f824074600c9803081c40d00d8441c61442d0351040360340810744801c1000b2908060010006c0500254403003515000c05021507040c1d0070071454084100c07143e070904074000d01c11750051140107020139038031030000c02c10600b40d90700040055040d4860f5040c0050614540c2d83c1c1c19024200202c0a562562040d2401d0001e5407550403d80302030110000c0144104080510040200f607028041110070b010700303e11000c1c1002c0c80641480c656400004e001c05e20070b905400c854023518104000304801e501101000d100600c4502482c40000c0400e8081042107101c0d60143c030794a40689466484200624005150700f4220001c2c0d01d45c0401c04905e01052040840750240104020300741940340d86000f0780514a5040c0d0485001100c46d1b81d200c3d120602d85410101c00301960f030290880f071600d00c29081c146da0300d68044504480 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 115708732 1250 115707482 115707499
    0x18100e011211070201030f0e0601080703050d1706060307030905070b040315020304020603060105070c050423070207061b03020705030601171006050d02040203091f0c0f090b04030204020c1e010b 85
    0x30110701c9441481456005a031903039040003c590700440203015808500092192940f80d4092122014410343c3d00801088000300649495494814140041c400951003800790000e0006c08500040c1409607003c402191220391ba581e403400300781c00801c01c40300b026000388030b21071010490051440041044d00d002e485e003842d15041c0340368410140e100c11a0000c0d08103206001182e040d50195000c1d1901c1841917104400c041e44800c00704088441e2103990030b003c0c42d9062108080c072004000e2254010480c0d2010380400b50401c400a400c81c40a4841c68000d41394207111070b1300b814401d00c00d40010b0400202541c005507900d8100c05191105041000000d000b82c00d020711402c5414400c1d10100d0304090017580c03c82840b9002c000003500001c1c91310426000720550a00c41c00080c15065894540c005400200c0381d054401c01001d58001c03040e08820f120894034240084020001904e080344e50498015031b83c1d540c0a4407050034810f403280308020840344bc00c40400130943c1034200e5080014155036001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 115709982 1250 115708732 115708757
    0x1030506100b04030f081614070302100201050708011514120108010c11060406050c0f07050a0501060602011103042303130501031a011709030405030a060501051807050d0218100e01 79
    0x2c55900c207511004001c40f80c4503400e0301c006a06500503214084055028141d2a05140c4550302502908007041d0302a80143e801841189417526000202e54092b00c001c00281ca807000000d00740b80d2060003020b07180500c0c2c110b602c242c640329188200e0075101c080c20030f5488504071030140704240300070700801d103165007802204c5942ca8400d45010231000810002080300c0d48070781d00c850005080281c901444500d0401c83c64984803441801001010700c29001024104443c0c100542100e8403600041c00710b9042424840301151464166904070b42c1100d100c0b880c1ca908002100720f1040100c0010b4420b02010030694440b8500070b200000711882a00c09009455040010030101c40b003507010507000c12410220000101e0034640c485a01510450440c2e2626450350700082c41c00051407000c6426a40700c0c4010b00441c108030720840d0a94ac030036400518103041040000c0c15a005200b1018103290340420700881c0f05990350507903480150007410990305018002001800710170940c1865020070030496101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 115711232 1250 115709982 115709999
    0xa0905190c090b0309070b04030b06090108070f14061b0604150c05030a090309050603100f170a02060a02010b090106051218281b0614070201022806050103050610 71
    0x110300305100d0b0740c6010324103041800144150700007a1050b01503206801006c10704074070010041000c0c50094600840901e003132170070421621030503049541103070001a001c0149442100800042d905144114100c0106240100c1c0b480c0c05034a00301d401507030034040c114504400100e100d90140e8040c1d0f1714800801c490a2181051b200e100b8000d80003e0800c000158841d43e15903c007403003680c401d01e0304001c040d5642000810f15042600c0304070040101c10380400c0000303070307112640009040d0000070700040440c10f0595900c41449060282c002c5c4070004000c40203034801c3d0310900c120440101510707007950319418010443d400c01180901448210700105500e1402d1a40b035601238080c9400138480c1710281d0074084441c404858901a502c240311106400003405d40408101d5200b400c0458002d86143c198010071382c042031101050804800c01841d80941d80c0030441e5030400c1d6a00d51000d0b4100c081342c80d4204007940030384001e001c0c0c40c5030a002104000f40802c4442c01020f0000280e41c91588400c0314 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 115712482 1250 115711232 115711241
    0xd0201150303050702190b0c070806010810050405150405010203040b0112171c0609020d050c03100b0703050d090302011d07060234060e03150f04020409060b0a090519 73
    0x451203004000c400c10019200d03070018500184041e201010004446d4030840346a060b9070070038135140c280411050407405042001000420488008003441e502d04000161103540080c40d8880d120748a100180c1440020001705a00c1d036175410060810b031400303092041c000d41060300c007290100801800042c04151140e01c0075180c68204180c040081d880819110003944881c031781d030700e440e030301810140e2901c4110700c1703650002d001e0f101026940b40034808682c0c04480d030051800c03843c14010702c00d1210600c07902803401309036240c1000c1150760300d946050135510b502503480d8107000c0c1820f110b20072040640c1904001c40b581d03101100340d0f000c10340015010791584410301840c1d005074007140000c1e4030411020050382c43c5141440c190361a084140c241d2078201402900720001144040b8080300440c00d08001400408a071002040210b0405d441c00e000d00340d20240c0060700c52900e405690b01400320030350011141142c000c155540340f03656000c040002c1c040448070310300b81c41e03440404940c980c2e995005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 115713732 1250 115712482 115712501
    0x50906031c020705031b030616080406020c01060b07110f010311071e020307151106100504050a0b060310170609030301230a060908010e0d080a0903141b0d0201 70
    0xe01804000030707600c01600300c0c0c14904001184501040020f241d1010700401c0d0141000ca010388802005081c20325240803400742076451404114503503500b000d58840035035a003181e400000941d4544038582d40f280500082e4108143c810f50018600042041303512441c5140780c4280e8200c80a9018000150300311031290703d50300c03021881086500e00091005072107504d00340c00c01c201114011803d4000c40c0c504003c44d00b0110000707000210300c45150307401c040c45000341800b12004100510f4095907240600d1400d01c552400b440c1c403030380405da50359819008101d4091028000c0c60300c0780382844086d0b140c51034910400a00c0d54070b14900c0f507151030b03010030307280d20699100005500d0342c3d107880c41551440025500c0503180c24030b0085240700580c2c40c0031903200204200c1e07841c01c1a0340c0c20305028900b11500241814801d50103925404100e40c0c01c08031165000d02d0764400003405940600b802d80d154a000c031a8a4210381d00020348404021400c8802e08403007882c4001ca03880e076228160160308a540f40720 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 115714982 1250 115713732 115713739
    0x9050901050409020402040308030f2a09150d150612150509041415010320030a06020f070206070501062d0b03071209050d140a0519110601060201090309050906 70
    0x100510290074a40c0103e0006440030b000185015980d4031442003a8105544001403210300e181404050706522044103400156500007640b108106000c00840e07118201000307000da9030198141d00080c2142003a00c1070031541ca6014810001401e50b0307102c0d00d03c80c80c042e07035011400003125080d41031401d1040001100c0600456102542000304002c03e4a500a00c00c8030044111810900112028030500030300442c0c54450030601e506500e4851550f0b08800085007105520341c0e10700b1043c0d603000400031501500300000607560101c0d46d051610300e21074242c000e900031030001000003c110056001c20708641416504401c031018606200010701180402100801600e85051140c01c1440c002075821001d07500b032000000c02c60542c0e42082e101d20000c1501c072508a008414051742d000301d220303140d0088a43c030652400420b020040d12a00070f0015103030500366000c12100c42c00c0d009100b18101c551741c0788101c070065a540c06000703020b840d03544021400500307150300003e10350401e1400c241c01002e004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 115716232 1250 115714982 115714999
    0xa020901140112020d180b0a0b010f05030609060f031207050706080c0f0306030c0d0b06030d08130b0612010914070518010510031506050d180507060c0c0806010b030103120905 77
    0x65492202a400c00c0108140703c0e46d840c00780c0300140305120070814060f84a0903580409192020800c0c04585030308a90ba418001c028003410b8600764030204499200008036100710090700c541c000f041c409100001c40c41c0d050f02c2982408000e021407240580700c0507209104646030b282d04c0c1d000440c0c0e00801a038001c403400f8020b03c80b0842c1c20200401560303005c000607046440c0310b85c540380021520000300d40207481c640c0200c800e1020500707040c04480000c2d80c1c81e040c440c1c1e49090241d0060b1094030001000340503c40c141d00401c4c120b41d502101c1691402559009000540b05801c000503d800001213030600392051f09000505400c1001191940003480c00c0398070b65903803903d4144181903080400075410141d8559880c07034402007840f050800380c0601e60300d6039125400b040d0540c1c00c0751030004048034200001c0680c840015400540c0c04280c0d038040ca025040da440702d2130052a68031040e0000d41140c042c1d1000440d01707200507000f540c122030044000c1100640c2940080c3e030740704100c2c06025005101c0c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 115717482 1250 115716232 115716257
    0x612030503040b2a0403030e030705060f0f04050634020114030702010f150501030c030b0d060e0a050303010914130506070e031e0106032607150603050f0a0209011401 73
    0x8a2806503100c0412622008452101c200c400c40008501c03204c800740c00000709041c02030503800340325504d40030b1083c1c2c001c00d0740341c0c03c1800091960103a00310340c840103213000611980e140c0251081d6002401c0c05041c164441c842d509690050f084006054200510012030940703030039800854603005650182c4840d921190515040001984020104405c0d0746d05c41d541034400303441602c074035080d03c00c5802015020300c0c01d01c030004042d5110150f42c0410141006502c110303a564214000100c0e9500900010702403801e80321341401d002540d40042e01c83d00011000003a0580c542e0030201c980410050302c42450b1b81c8010000300e45076200003000d8002d5100e000010b646a000b1040c81400b42c0740201191804424100500701d2445140840708490751503d0007003080121800340b500440d064070720b40507120300200d2003032106405140c2c40a4200d94004408009490300382c3e210784003039900074040d5190001481207165840e200c4140890141201200014221000010a80d46890143c0d01c00d00c41001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 115718732 1250 115717482 115717493
    0x120d050d02031312090602060705041d04060b0d080903120703020307060c120f060e0703110706020708040308030a0515010f0c0f02040e01050117070602010605010f08090106090c050706061203050304 87
    0x5140000c0240401403400c0804e0180492612002039992880000e46c2003c03c002e0800001038445403d011040c0024015a072400d04c41c5540908804640c0d100b565803810401d0241c081800c40b9604044500764407414854044c0003042603900603412601003025180d012201c41c81011400b40060300140088400502650001c1004680d03900c0c00c000c0c0790224020f03003022601d41e13456107405541d4400042001100c18016260300001e1401c04100030300411a400311903204015004100170740c005400f0081191002c1500c016540203c2c4881e2a031500e5441c000050500350f80045080c203100c80d0071000b540c4140a05800322485075900c41c5a6012a80e41419140241200302c1c0d015032100c540054442c02445618024051603620014234512810146c1c204001790b0000821a410000140004c2c3d030009580d0180c41e19030315010a0b540d0710313411941c0c01840140c20021000e410504502c100035403000252080074020401005465500c214510189800d5003009011170310620000c0c01040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 115719982 1250 115718732 115718737
    0xa0302070f0506040e0a0f1b2304031412040303090e06040b0310020f0d02180109080a1a0402041404080414030703020f090c0c150103060515150c01110409020702120d050d02 76
    0x14001070302184413a807c00c144010768420300000845d42c1c900d5100240e825503c103101c00c0d0031001da05c07568003440c1e02c410700081951050f80401341c00400440060081d102c0200010704041624441c07490f122900e80c98010b05e4a1014850040f4607100c2c6404594a440c2921038640c0001e0f0060007480b8900e07404034020701a4001d8144400204014000740c0c48980581c001081c110400c51030941094070042c0025003107501c260011141c650180480d48005100c6107034414079002183c0d03401d403485d80d45100141c0580864200b461f044400c1806210030130890b80060401d071030020074121a0807400c681815030300c0506100c045d40c030485a00304240c441c18040c08940d0001c40344800d541c58900c84004591501501451058058604200400a01215115442e00403142a040c180703841a008000344052009a01c54505480c0000e100f079584202580b01c020b189841501d0396450f550f40e000c0241c003c0d00400010b0307004414081c548000c0207030100f4844010761581c0c6a0038240301c44030080000a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 115721232 1250 115719982 115719991
    0x3190c020102160b0a1107150c0216120c12030305010f060c0323190906020610030201211e020301050a090b0d060b040209060c0a0c060305010807031419050a0302070f0506040e 77
    0x46036100c407039588044603003000741f5646019a20703400d44004191503002c01c0f070b0f4600982404542104500000104a101c05a8212401c51030841000303070803800c019500d040142d1040621007101402ca0b01010341507004541240c40d83d84201190650f20b600540c0c0750595441b0040015203030820325071900d0030302031448041d2841802198203003480740140c1500078103001c0c41440802c03000c0034100880b55041040342c1d403001c6c10b00c1c0d06c060401e05d0365001800504040d00c40282e004040340300030326111051b6100d002103000500410351040c00e0f5944000c0203600a0061a000e28400d00c0d020491305224000c088005001074145420f103501c03600c888000705520806076034040e808000c411401d075a4900a004e01003440400350034904001d282c000300c4202964000c009041c14800108040140402c030002120307042051207915141c45a121401d0025901a6010388111100310200b405000600001080d120345c080b0340500c1c0c0c440e000d01c0040ba09900c20542c0c401030130082031000d41c046000d41d5422 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 115722482 1250 115721232 115721251
    0xe09030903070602070e010f0b30011203080c07030f0503040f120503010905090703020306010501050901171501090e09030415030e100203090c010809030a0503070207030803190c020102160b 83
    0x40c409030400090411070580c1c41200107a205807818030001d035500d00494010300310010342082052400400c020b4a006400b600700c041c510800a10003503410b9046840b40e100d2410404c01400d41e12065124642c5a002900f86c000034000310008000102c480c04940705075402d41c803007000e0004200f800311500d81c4010300880705041e003007034140d0000700880d00d80c1c8101c5086840f190b40f25814181010101c61005120400c6503210110401c056140132510606441007803074403994403801c1a0040e00d80d00541d61402c5042006c080820040c0216030058031074070f12099994442c1c40355141c1c51b940c090303202a540041103820400003000624100c16402000f40c409040100790401c3c0907400600305000e0711a02d0f24060340000401017000410f00014040c0c940c242403c0006041584c9001e95030b00540d001607044c0306000002c200818020000b0341e00460740200c80f82e5591401a00e0401210060848040c0950506044080c0c00380103009a41d000c1d0f069407070329000c0c030307009455001c029540903014210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 115723732 1250 115722482 115722487
    0x1210c05040305101d011a060f070b0103200303040815071103120a23010317070b0a020712030605060702010c2a0806102301020312150301060803030c040e0903 70
    0x90020320405441580f96800055110a0708642a1740f1a086102c1c408207645000303900341d45545a22900906258152081034a52100d0f0364104514841c201000d07000d102020000410001010460140c0c6003a02d0303c0192018a08020300d030b580d004030f00650702d454002e403804640d501e003044c2e8200d5200340340e071a00311140340b0a00007882c1907900c00900018000c01c0701702084060101d07809101807507407034080b01d8402c84110b659040030f0f03d001800000e0180308003065203582100c0c0c00d4140c0d24000c1c1c01031400816802e204010100075404000300b1240c0348411400c050100d8064401c01048a4001d00150310700f000b00c1c0d0044580032100042198652034800185076140300e10850504400c060b0703000340c82c01c1410324070380524040f00200f03c1c03624422a1003040c0894940c8030300c81043c00894031604c100d045944c2d00181d041d4000c11081601ca1041d0400300001e84420300c103200314890040d0000c00100b42c81d0000c1980344e100c2105cce609080701007044100036800940711403540c000301c11007e4a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 115724982 1250 115723732 115723739
    0xe10030308070e040606180806270c0a08060f01080a08040b0a11071203110606031218220c03050702030a0e031609090b0705190c030e090c0d0b01210c0504 68
    0x900705c840c0c07500b119001441451050214070b84030900345001c5c011110003048a8604049940355111048030b540404d0190003068040000c410440304d40034100080c00120955141c900095855808840c140380000143c3d000086034000890321a55440d04085140d24190400400d43c485034800840c00301048020102c5810126046c416000940480d200c8c50850440600f001007203040b40010000603a0800e4003170016982e00010240103594812440d1500c070103900c8a41400001c2c003102c604d0300044104451440303d840502e4514584a030103804000d404c29802c022401c03140c1c1202c1c5000541d0040003158941402000905c41c2501c0050454542045003c811700c200507442c0c0c480d5482d9515503d12401300040e0103034465000209103009400c1001920103d9402800c100250081c4580001d06100f4988141e024144900d00641401d81e40d00306496001120b0703000b07aa200300420325082803801c4962280003090340c0e282004400c2410003080842c2c0200900160010ba802c1c41010400007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 115726232 1250 115724982 115724989
    0x1805221202010b0612010515070c09021e1602040b031f050603010c0215060402031506070302100f0908030f0601020f06040c03021f200f07030605100e10030308070e 72
    0x21180580304040902200490040180c00c0d140685200c03486608140603110100083c00a403904541c030441e6070018400c3c881d0f490324a1485501400303031040100e02000705003103890390001d01c0c08542c4d2440600e040c41852220720428040c0c201d42510142c0281001405450181c002c0000014003c060316900e01c20b0305200542d030762a03602090b003000c2c0c6400400455180c28440e03170b12082c0b00b07400a00042d10900075240030b4400c0081601d803040b03901001180045a6403241d94014050140009a80c1c818505001e5621080300b61250011424102c00f412440124000c51171010f03440b043c1309065407540101c6910200004004038111300c1001c1451000950030802075001e030307004000030441581540140031a00c1080c410980840b03c184000d00c40b19a44554200e00e2145c606040b91b100c2103d4402903400e040304858030010503c5024001b1090215680c41a4080d058070b4020b24101c2d0b0b81c607428070010031401c6580c0010500000000c1010038020400c00340e0021141c50a005a003c00d030001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 115727482 1250 115726232 115726291
    0xd0e0c031006210302030d05130209040b0f0a060810020f070c0b040e0702010203010e0f3c010e04080a080705090a14040e062707090e0f0607091805 65
    0x1000e0154481c2c8081200d001c010420707218904000c0c3c500c2e0780c0654242c4004c1d640b44181e8098821060f540d500141561940c110001c00a6900a00d512682d00700381c00c6c001101a003d0b50940100c501c0302000c40c000148a01c1001c0886001d04058034500b1583c83e15800290444010040d410f64200585000200c071075072490080c00c06994003a03200c60501164412004004000c18150ba10400041c001982c40d4110140d110200c240c0f8100d40d9910a141e4a00c0e4804000498100c030740c0142000075030900c007152501c1c422400d0000785400f45e80e41c00080306507090170b071805401e062080203c1c418040c401c1c502c040c3d2004d46801c10501e0b00c1c000c980071032490403443d88503407007407200316021618600e0103010b5940141c1d070780c00003820241082000360564140e1303c031203a4061030702162076062508003030022400512118031700700419036041543c00e4403050040c0224105001d11070020303100502404458082c1c400c446c1c0324000300b60318001e0b003030000d1101912041d0728031005c040034049000082c52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 115728732 1250 115727482 115727503
    0xc0b0a0503040c0f1a0c030c1e010c080606041e0b030112020907050703080a0b0d06050405060105010905010f020706030c09080a110f0a051c0f0506010e1005090106050d0e0c03 77
    0x140e4540e00d00d000e0030002d881045640140b0600f4480910400001e40828540000301203400811681c406085290916500c51680c0382c50860141100013540c840840301c1d00c60410039508001e20249403220000c6500326012030702a0f030311000c00e000030b0004030401985c1224450882c044840e541d6154140f010181d04241d011040007001d0721184011401c0c03200195411808900302641068116600a4042c1e08000c10240319070340d40703018042c035036500c440740001c40700c0e040f4508001500301402c00c035441d003809010341400710764400800540c952080c0501b500d1b80000758040d000c41800d1080c2100903001591268081140c0c42601103140441805000d04851040e50840080d09080c02030010382070307003441a641b03d2004c42008019540310101d034080810110441c8081c515018506040c00c4013aa03107009c0c1141c1b198900102d031100c095401680681182d2000000080d0f5500400008903401d016030f40000c1d40602200c2e00c2842c4c1e6401440401001d0380c00d4030041108540440e142041088 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 115729982 1250 115728732 115728737
    0x20030d0207020414130c0f08060411040b040f0221060114073207050a15081f0b04090515010e0409050a02060c0102090103060504061d1008010501060306050907030917070c0b0a 77
    0x1a62504006c2001175a45c0280018040124083d2510212340d4942100400c00350ac00c5100315506502a5242c2d442940c044000401c10046000340e80320740402074000040d02c41070114850443c076140040c010f509032243c24160341e0b511091a5800d4807941d0f54101c030a080340c0c1949807031071b481d003403200b449116900081c8142110040d0010000702c64500b810581c4a0f0703010340d00c00c3c1000d01031174010092004008080f400d1a01d040e8491540b1000a00680c02c48919803002c035807004111120980010002c544100c07109010355100e451100410f00c224219480c0880c100720001e10013824150007010042d4024000d4030401490381d00070070500d50191045170002c0c0d5000442c65503031b60b0540309500c0a0902654100030705410031913001231101e00c03046059002038000c4002800034642160306000b41c85007600a00103543d50f808044d02405603402035070300c205005070000300f050b4400d20644001c150800e2441c0681c0c01003070174007950f6a015910598140d05c2088002c100c0f8107552000b80308100065 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 115731232 1250 115729982 115730011
    0x3070311041410051908030406030e210403060b01120c09050109060212070308060a09090c0e060105031021051902030607020604080a03050612060703090320030d0207020414 76
    0xc000c1000311010194240400000071007844002895000303401c2c19290142c40d03021140754007036990012032400360b1124060740b00c0084c0200300d4980c15000340c00b400b05004200c0700501440700b00750103038006661089188400900042011030229040040300703200606200d00384e84000d003400c9017525004d112000125105007002c101c1941d02c480d06030001d000c1c620107440a240f4084d00c5000c2446020000380401c20340102280c490380e01d82a001004040d0568100560f1910745815180d02c000da1045e85080791034900000c40c80e5004030101c0b84103588003265652070341e00700020681c200d035124800b204451001c03c0140005203081000c100e140e482121900e001c10b40510400d89004402031103003045401542c14000001c0c04101030381c840402c1400e0200c3c0399074a410100d412001c542c01e68800701d1156000703101c4119059406500c0050180d903843c92a9668100e0400541c2c0141c0c0401402e40c1c0204110354a6510035806031806a100520102e10321819030910030303106005445688550545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 115732482 1250 115731232 115731263
    0x50c18061e0706150501030b0f040209010e090103050619091a0702030d020705100c03020703050307210507030e0d0306140603041403030702030a11010603020a051c1e0c051f1d030703 80
    0x3040051300c0107120034602800b280d084640868440d685400b0154000d40e0082500e40700c40e030003540c00c200206000f5000b20241e6030350b4240507170713900400d0700c214007900c0030b507a440e000542460040c80749190f000140070b030750658800c0c2c841c407603100028141821030109001c45a01104540000e01a0a00400003000800503542e681003c807101140d1510a05d481005094006500101580e9101d4030505010b1201f440f05164044123606007404800310529183c100854107400d6440174003095210421110325407400c0c4000d41c100c5a90f402009040e881c101100461440c0c910b0043d0351040c86413448485450003040080e10790b4109440203c01768201155035079510740d001c414010301120303620003070040703604d1500460b891400c00d000d241c2c0100b521540000c01c1c03088410740492010750001142c5600e080a5440f0745089890320002c6401820502c8009070f6440e008040568038402c3c450346840e10140610b050702c925a00c040a030b80c1e90a1144900c030307074581e0148030003c0107500070822040b11058 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 115733732 1250 115732482 115732511
    0xa0302040603292b0303061d01030507090c050705011107020127050405150d05010c0e0108010333090f030305130b0109050903090a030503090301050c18061e0706 71
    0x221401c12041000c03580500711004000c015012014405031220098260903010030f840c1503800c2040c01c4c0c07075004007020000c10140d15500001c115040020040c1e503115070561800c00411080c440a805584062424041e00345580c2c40054070564500344180f400300160b89039801d41304d920b0318404200300081803140655810032031781a4a0b002052520500581c00180c00d0041c2d440d40c001c1901a0344c1e54000505005000704400307080700c0c0300800e8444c2c0340320b261070041d000e40310045684000a0000107044150f50040004038180c0c7d510182d0340c4030080b50a058103c540c4074680b0fa1000709100d0915041c1c200750360b4401c040c3c0180c007507107540560310783c1c84c14050181e031800f510348040c030301980c2d54101c0441d200d24085815035980600101c0c0c241c032051110b514602a000a581d804004c0d00c6002040000010040590b00c00a4009000300d58400300d910307035940211200c4042c03001500440396080d240840003040908100740b42c00f54584143c0191030001e400501c0c040b0b031010356a803044842c40e41c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 115734982 1250 115733732 115733741
    0x111207081e0f010f05060304080f09060702060c0d0e0f030c1203040302060a020601090b120a1112030a0804051608070e0c0f041401180b0d09020303040e1918080714010e030a0302040603 81
    0x4002d6031507e1550800366078010480c89040020b40d420346020070038140a0b85c9200031200c180d03030001c1140c2e8664207110010390301c400d009000d02000c10542d020740c1d560f40c1003010002c0d100002c000c01900e1100c0d60401403201d0464802c10510481c0410800800180d032410050000c03080c0c42e0f801040c25604144141040741e5003c0fa03114402c0c2c0c25882c003031000000004a80101c2c0d13600c2a100c1e01c8000020021801c0d04000f0341c40c03c504c501001c905c4036001036001c1d0916200e18044c000300c6d40d401c4602c6d424038482013000c1c000c1c40783c0c42e08200740500481c0c040100300c5400c440c2d0f280101e4035066102d980c2d4107041e005604400d00c408031010303068005e036078402100c0006100310001070006a00c0e29011070030511604c0310041c210368464801c08159682842550010005021080c02ca481d00c401180e0400d02c0c0c0b440c0c1c6010030740c900040102948803030202061038940c0581228607206403034541180c559407d8054012640d02d428070303000040e42c01e001030031540344180c6000d81c60720300b010405819913 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 115736232 1250 115734982 115734989
    0x5040c021006080a0f080a03090c090207030801050a030b01060c030e03060406090b0703151a070b04050607080906040b07050304051903050a03060803030906060d17030712111207081e0f010f 83
    0x1d501071340c01c1401240c031180c030391901d080d448158903655440805055005c4e20340030310042c003c24100703040020681095001800340d2407081d42c540080c5da0b01d0744104072503c0104c1c0009001e1469180061001a0003021450012802401c28814042c1d9a40009190072021241140e10381c0c2ca40034640704001f49420815004407050500307100030500390a90203000c6403107128941c541b2250710544280c40486404803500b454012440030f0b054602820000c1d9614000d03184000001e80c1000040c400032404221a4051035200041009649407a4001c41d0b160300702034801c0c0e03000e0050414113464114030420140071b40744241c982e580c660109840280071540e0a501040080c0c00400130481541c03130214000d58004ca0840d202e42144607582081d0b40011010048241c0a030310000078040500e030042c448215140c01c1e40414414086081c040c8107190240302801c07120009440085840d45001d840101d0784030550580ea0302c61400d42c49070481546038107941c01d00c540c100803801400a0180c80c1c3ca8000035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 115737482 1250 115736232 115736249
    0x60b090f04110907050d020f0a18030305040308030c09030109060614181b1e0306031902012c03030f0d0e0706020d0302180a230418020402090a05040c021006 69
    0x10745041d840c0e0301c5800610014607842034140c40001034010740901d0a480e07041415400440d00c40b050440c4103201b036407068200d500442c0d0b80b40040055541d030311a4140c250707a816a18141080d281d9502d91020b900050aa40c018440500024040351000d210310980c03180500301c0414402c1c07a024040d1a0482e200c20b505020780406039071849980305915240b9000444081d00c0880c0c0350b030640821415003d202c2102142150700f401655080d081a00610b00a0300120305441c0880603114844c010101c20250090102394102590780032014015030500c03440313070404d9031101a01c1c4400c00090542c0d000341203184280c00e010804104800652040340c90032140c0d00b00902e065800c0c481c019503900d04050417102019000201d8628030040c01125005140c006007030b90054a45840703070303809018440002d1800c203041d907070b03841c06161501c1d004044e6039600c80d5a40280d000a96001c3c0b1010791f00c444a115000b1a03420382c00030303a6485a20038200410507590250404903000300100c0281c501e954445101e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 115738732 1250 115737482 115737511
    0x3071706031e0a0c151209170a03060506220e09030f0a050405030d08040308090c1f03090803070306030507080a11090403030b2107050910030f1a04060b09 68
    0x3000d45000580000382c4a08442e070a03100302826003194581038841e1001041204d150340f0018884003400040418050079807200b02145480480e800110381440c030700a800300c0401c034401002090342c0c2009043c20805c626000c1030303498860005c40c4440c0d200b00306035540002d9104143c1c140740a400020700150080b1065090f8030b041690300c195032402160240c10b4100da00184a4000b01c0c00b44040350010321000e01a266004910f02010b0017980b421074040d800704040000040c00c10310042280e0084020080c444c0ca402241080001c441a202070070180602d13aaa04000c0c003c00c505c140514401c100f10364005c10714a0031481d10710304080c840c2e13100c2621030744a08036910000c0d20150601c11803110070b0380c0b403454559035406c00f01d010b40380d500c00e8035420806201d176000484059148507207041004400b00da0280e0750302c1d0300744860140d00700c070400e07040c10312804244009150203019541c1e080c001c80c413030303284412031042d05141e01605a8040315a1551854190580c0c10a150220380c099100358101c1e2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 115739982 1250 115738732 115738741
    0x40510020c090c131a0a0f0315060e010201060b040e010303020f0a051f0207020616110a0b0d051b030a0b01030501090203060105160606080a14060603120f0307050f0c0102030717 78
    0x185030350b802421240c015940031036400c000707145075408000100380c682c4440000e0103a44c222503010b070340180b40442c0002c505550003405a8004e02800c00c03000008c107581000f540c580341c030490741907585650301d07030455403100300008001e0140e80203000038104035019200c05524600d0302a1600800c40d41c800d0a41e00100c4440021401c00b00f4461040764100e4250340710b8510308c48440c4000c2c0300c0c188000354130140206085405803a5052520001885014000c4100c041c8508104861600e0b01c54101012420000410f00c036440e90846070f0044020035010f0001c60071703401003034100c1d0000c60f0002a0b2554600701e0a4903981d145c040c2d07500510b403030102107207103041c0240024014860001001c1c528480454002d04008c4141d00100c0200f0744181170303c03a12410f6150200c0f0007075a1941040440c410140840c50524000c220340c107020081c49540fa20f4400c92144280041d00014420030030700405001d0040408440d4000344401c030503000c00140d89181c410005052076001188400303540d0030140411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 115741232 1250 115739982 115739989
    0x380103050f0a050c0403020a0303020607080a0b0a030213020d1404060c080115051c0606090302090c040e040311150c03041e02060a030902220c09060203031501030518060408040510020c 81
    0x50b00000006000304040d6208014010f09102d50361000350495034000b000418182d0202c4d00d04d010f00b5080d0b4490207107440d030703501d41c0e4140d03042248000d0340000084000c20040c60107000c420a8041c2504000d8101741e00310302280c044801c4c124400441d02c20341e20400080149900c03d0030703180070040c1802001d550620400212503511009040d0a001c800981480000740e039414400c18154410010301c40103480f0240185141c009200480c000d410340000300b00d2207141d5005071415600308205901d440e41d0f0340d0314215030328030f03c400c504107450203000036091a01c8002c0319030301d203c2c1a0070320700079540c0c1c1810718100f0095803d02c520f9644507880209003800595030401115144441440d01068810303043c00022211880146800f4a11001c510940b9800b41583c000654101c840e45076002c1c00707075882070143e8803480100c0701e82e00c1120704c42e001602951702079400282c21400c14800d5900a0403c0d441884c5006400c2e101075524030783c040340c100203d01d089903000003800d2041c030103031042e000c001020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 115742482 1250 115741232 115741261
    0x305061003050708010509190614040b030102041404180b0403020c090609040302150a06090e0114060315060411040504180501060b040501020a11150f03070e090408190338010305 78
    0x2038610400014001c144248200302c0f015241c0c8c200000d042003c02c1c1d0742c80800305030b01c0c403003c6018080c0b03084c152400301c0c3d8641842a1811a03546086402c0c40c400c4220810005022840100c40143c3c2d460460001103601c0300d0b88644124030a070000d00e80810181d08203d08444000d000c1032042034200200000039602140d610b4030800e0100301c0e146281c80b010b030038101070b2420390044001e0720b15080308450b82d0001504004982d104901c0707007410b10740740c08081c103448621103400f40601e000c001001c0b60060a240d40807d91465041c540c079401c0c00c0e141d40014040d074511080d06c2604207503103510b0105004081c4962401001d14090072442d080c0f03801c1c0040e4461010680103070179030101c01650100d688408694010bd0704180d540150f8a415011000700381d90010344803040080c0b030f0b1000b110214180100c4042c0034680004072103041c03000141106009000c4100b04600b015210140f280050740c0014004601010481c1043c0613113694000c00009088040500d80c101402c0c9000c0c401c003460344900c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 115743732 1250 115742482 115742489
    0x4020a0f0e01090801090b0115050a0504140d08071406071b061d070303020601060f0813020603100512030913021303030c030c0203030a030212090715120603060203010303030506100305070801 84
    0x3001e0488038000700c0160340041080e4404030702c2d542015022000c10050b1030040b41a40ca18244522441141c450220f80034081c02d5400d0010a00c00c01051210049070006030801c000020405600c11039640d503001401c1d0072080f400c654108001080883c1c0c00028008198040312910f001984800c600030202914040610090030305d07a6030300900803c3c00a014100a40084210200d17680c242c4d0380d1038029500c2c00244600d40c0002c207203108040c4ca0710320a22060340074030500b800d80050540e0310380070403140d81d0001d0b10b8550003d002c2e00c000112510344103c208000d03000b0720040e507100c0f6810000d11846490074891049060310410045004210500f840b005403078040ca01041115001e250a889180384800c0107580b41c4004a50340380d040d80d058004102a240c000050340280c0c56020b0300c1a42e0301c01500460840442d4404c0c0c11100300d12039902c00e00c8130304070304001103a6942e0780d0b01c0d1b03c4200da10030b800980c00030303440303004204450805208815a05156103020401da1a0100f0b008080550601 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 115744982 1250 115743732 115743737
    0x30f150705090303090325090e030d0e0f0a0c0f091439030403030c0c050a08030601180f0e010609270f0e0105071b030e0d020409050706020d08010504020a0f 69
    0x2030b9040081d2000c20550303003084006811a21004442c1c0c85148020310010549210103507a9000480c0209044c0110003e401c0070b80c0043d800e00c442c0d240036101420448502c04030f11701c40e100724400d1604007080850b518501984c5103009182c10104602400085900310100c0c0c107090580d0680840384006010354031040440c4032044611740540040c50b002c42911b105050311a600d00e00340380908140300114080d6200c0c1d00d0030800c01840c050140d481c114400805005034101c401000302040d0301c90015903000005240c140b1200c21400d540d18010791064010307920241c0c0c401002d21000d01d03014021409090380342400740e9101d02c6c02c000c40b0901d000815042d00040c0c045410480c40d4407460300804840781d0f04a50038802c1ca80001d0b0349074000d0404840440004d03902c1903246102641c0c230b040c18001d440e01580da03040705220131402e05c480242c080400326005030381c841d14003004c40c509004040140081d940941208418064000c10500303041c0c110510992041010701e206603080010340048440d41d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 115746232 1250 115744982 115744987
    0x8030403080a0c050a1406060d030e040b0109080304030c030611090604060c0804090e0309030c0103050606070204091e0b010e010f0f380403060f0b0102210c011505030f150705 77
    0x2c04a42c0040007480061543c801d98280e0720030440c500c0e8a20491012071b0f070803114955580410020300045d0154080e0220320444031400c90f41c01c140d017200804c08810704150000d80d69849080d40345501c2580b00f503800b6010346005008200450040e81c03503992540381154103124110f400103010348200d01c204424008100300031010407002c1016a0004c2c80c0c0c1400800001c00110901d540300e5124a0700701e8480c3c000c040c02d1001c11340c040e1081d05c1c010113000e064a0b0410703c096007840010690080d003a148030a440880d2039281030070813003000388640306015071880c5502d0000300c0d01e090141a0480c0141e0615401c0c14004e07110380040200499461203100c50b1a9061580000d0b8106c0c1c860020800c1107040c0c0402c0340c09100c3e01001002102c1c820002040894801407802044906010800c1d0050300500c8112070003a03141004120200d80c1c01780590703d4030000180726401c6170000c0104503004c0099200401c036034a02030003510840c40500c03014100002614500040f5508002c01d10810300001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 115747482 1250 115746232 115746247
    0x1b0906010818010f0b0325270507020a12090b07031202090a06030e10020903030a05030712021215030a050c0112060306050109200c060103020609040920120102040803040308 76
    0x340b440c0345120000c5000030801c01036124100760180034000706441c001e04c589000481403500c1d15207004900d25528420420483c107058071044889141c0f0007281c1c0640c203089803800e50b040742e07110f46070041d0207940007170580500702c1c038203400d00c043d450b5454003c1c03100040d010002c1e85507440c1181c041c07517031514040c0d4944c02c0c030502100090003145000d83e080701d4200408296190141d02c584003e0595404450070041c9103403140d0700382d2007954002500360f0424400090303407500520203103130402910308164015482d641c05400c201d800020300072400c10110400d1002e2002da04a20070070529040d00500710003c45610748030ba8500c280c041e8503041241c221103079000841c8030352111000e140d2000003032104e9603450600c07401400c0c6420300c082140181e900007204420b035181c01c44d502f800d9a0740241601d6031941c4c082040039040f02003041e0304140c40302c07001d00000d0341d070b69688c0b14044409100301c075420b0910403c2c089420751040d0300078003d81c810401801030310300010580d012a9404891503a503941c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 115748732 1250 115747482 115747501
    0x170d05070f020d0b07030f0f0905071e17010c1707051e0f0a0e1c0209040f02040209090f0a051501091404060f06020d1103030610081b030a020c1b09060108 68
    0x248006000103613900b051080e000c0e45600440d103102c400c03090034440d503540d2001250032907030401c9000300036900802e410000280c00e8409c250541c58078000e05010715075981c4500e10030840c41e003c3c80955940d140040c0c288240c1109403903a0580c110410140355140c0070310080c0440c07085c0e14400c4c40000401c5460385c60150640100e410a0342041074082e150b40180d80040c1c844e81c100c903040b92040369846101101c5240a060718061190014414006521151036514100401500c140e0308180c0802150006884031980d940c0a0100c3c078417424414034091040d81e0442c2da002c0c14070104034130050041c4000e682e0204440080e0382c05075111642c1050007400280040c900360740000a002c01400c40028496004141c03985912040c7d1221000a800c40d9003054403480203c3c0c0039940540222070072a9914801e001896114480107040400d40c2000c04c91640303075401c02c4800704001034000841c880380510900c5070000398a074811050502c0b170b82c000d000460422004040c00d04000c0042e002607130804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 115749982 1250 115748732 115748749
    0x513051504020d15081501030b18011d0d03060b030a0f0f0906050610031104061202130308090103231b04030c080c0a08030a02060408130b030109020301170d05070f02 73
    0x100003041195201c0201100c2809809402c4d049110f6a4181c0f40004d42d52402082c141d420f000440850505a801c503900c0100e845030107803008000c0a40d200c4418006002446403200751000c5078804074140304450065441c1c00c60f00780340e4004050405030200a0029510b09581d0081800040442c031440c000848400401c15070452402e9142000300e040300f485050343c4618002c5078151400101c04422042c1901a24255091190400003c000070409144914800c1ca000c028854015140c01c248400c0488940411f030026644c801e0300241790b601d03a68041c4150401b4400c01341c504c03c000c01107592440011080201440c18102d0040710789848804010103c0c0d0145520060440c100c1d91200892a55485680f403420300a0078468804103c466000040c0ca0070708040fa030091280c0c0c2c0d00d698582e00706821101c5480510341c99000302003507005014018601030800e1680c01620780d2b00d08040a88403202c124010462034010800f101c42041e4032000310341c41c0a0700691aa41031426038404180b148 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 115751232 1250 115749982 115750021
    0x5090109090e0309150301031703041a0c040302220e1f0c110d050a0e0a080c0f0a0902040e041b08030f0c0312010905180705010207031502040801021c15051305 70
    0x545041100c0017401010040c3d416070b4010b1104410700010b40b0000f4405210030b44015140e11400786219105503685040709130703c40e0190310b84606080d030b642e010940c0610000141c00761011000e0202c024003c6034810301d500424803100402000c00211500b2151880908003100400d07200d00e5040281c41c01124090000603140781100e5000c441e001d0000d0668002c20801d40001c1c42010540700d00e8900b0350b020105861808014003020f40f044e204000000e0503010107140c03c01640c400024041420b071014100600781c4000001c00ca03c0d00307180141425850109007480d00700048030600c081078001050300c8070101c0c00640c80e0740d07585500d843c10703203140100e09200e00300f00032600005c18010000d4118501600c0c0260740d0400d101c0340c121400340c03500c2242c002e842c016400143c2c108007056001f10010342d00390013404014a03003511600343c03600366880201808801c0320040d001502542440c0f01d01d4295440350344400580e5414003001503009109080c28000494484002c100a09001c89030514035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 115752482 1250 115751232 115751239
    0x13150b0a05030103120e060301060c150507031d01050f061003020403051c0e03010c1b020a080703110112020307090302060d020903150108070801060311060c0f0609100c05090109090e0309 82
    0x1268401030340100107a10074001241c2010b101842244a50b0089180e92010000180214116800c1210480310140407100c02d84980c09002d40f540c0500703551340705041c010301e5240e402040b0f00400e644c04160450090700400c903142e01d400304024036070440d1505a0742002d02142d90b180100c400c0c2c10210017901842e04058200c0c000da40700041315100c40301000608000903182c00b45600c60181c1014222041c03404120003003100341c03034401d0070050920fa5244c0d40d0b070320081c0340c44003540d2900c521a2406600c1d420840340c2440070100d014207903030001c541c0190f01920310801d42ca523207003a0f440200340041c90310009014040104642c0002260740c0c06880084802508440600d4260740254104040c2131180c0c00c101d000e60500400d00038010f0003000d00380c03904030991045142950701444060b9001400700d9100303000354804800d404106015150142c141000148500090f41804d101103030b0305500315078203111081001c9501a604203c900c011242018000150b15145107481c1d0708601c100f01c1990b0b1b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 115753732 1250 115752482 115752487
    0x31903110304141509030c01031509090c081608120306010309050105070f030c0207080a17040f0b1c050405060a1109040606170108010203010605071202031b010504030e0f13150b 78
    0x10083e20420216200c44021210f00e400e0f141016101c04580c4580601650150440340181c1c10a5000780c000d4180c009180d00004501d50b501d030710b044125900000d00311010b03c404941080b002400300803a819076102040351040440c600604103907981c5040351203040119000c000128943c0c002da00c04841a90018001c1c0414508508000d01120401848101003450308003130040c41407000070741c00b040e43c4039400140248065511600c0b25500c0420a41c1a00a41040701080d840301100c0e04600500d86443e509443c0c000070340a6a038580017515055401c17501d44010000401c60004407503410042c000c00010307400301c00190350074062103460049a00181003980000b84254010a00d940c442e864510218450362107081040c280d10080c890f100c0081c009005010200300d0044005011880a004a0345040b03140b101b020405007a031b80d4800341076555034080105041c1c1240350312040c8a0111080350f400f41007400090a21250b265070300441d82d503500f804183c0901428030200c09049a400d0780d54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 115754982 1250 115753732 115753739
    0x30f0b060c0c011107080c01030f0e01020a02100506040908071b170f0f0d0905060a1211040e0a050702030f130e0a0507120e12030619030501062102031903110304 71
    0x55440d9100c141d0b460004c1c9651031000c0c5200000704140c41500d540201a040702c00700341c0e0045016041180e030001e41995220451881e0300c1d000d200800041c541c0c1c1d0050401161114510300489000400241c0540c0c00c000080700000e00500c202e07601396502ca0616510289401107018040400b60400b044640800000d5140e441002034030072044440034007114038454442c214035444403940180503000c030f6078018042c8003629128016100358542803030a402402050500c220a40b400b10b00d90b0fd0005200003000d000403405c4031941d5602c483c9900303042c0140e08140e03600a65a00c282c028115001c2c05c085950040b46001a481c100145a0401000010b081440b48940185001d680520100303403468045da44c41e4046004148240c0701c2000948000b001c080381c54038180d030000340f03016400207200d10b11443c00040c0c485084091070088000180c13047c14044022400902d811064101c07514025200005a40004100d40800504607004902e014180f6013034646003040c141a007041d020129010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 115756232 1250 115754982 115755007
    0x203060f01330507020105070506010e040606080c0906040518061509010f14010804030509040f06080708070515090f130f0b0603040206030a0c0e030d05040311190303030f0b06 77
    0x150580c1e900d820b0084078448101d150030090780b01005416451604214400c12040c00b54000d45403990042c14070a20b009180c1d52403600b015802d070010100c601c40300381804103110442c49081c010b04110740040c140744c00340c000011520440100180e1040f42c4900c009500103210258440c0040c0c0140112146820460001c0002403140a5014081e44020000003049844082d0350b104843d6880703011901c0d4501e060045401c500005d1094041c81010000300c0495182c5110382041185201c1c0002406810b0110f01410485a94061201d0340c0c0580703c00c0c4129607460454940e80341c542e6108a17074501898001c41c202a01c00c0710140d85c80103200100c030110b4134250b0007216024100a42c2005940c00072070800a8600090ba0040e401400c2400001c0704003100e07502170701c010a002e00384410291030a10000c0d140011142c440400500d021508104204106442c0c0b41d035900c048404260810200381d00036020412413102604054a621640180c12a40da010404001000e0141940e554541f85003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 115757482 1250 115756232 115756261
    0x20f10050103020f090c040b0304020a120b0405010501150504050607020307030609231b0d0201090e07050d06090b01140711090f0108100506100f1806020708060901090825020306 78
    0x61313000e62004c1140b441d03140707000785000d481202840482070405003030021f1044140c1005100300c0c0c10012144001c105041d4040543c442c02e0b1003419550301524003440c0c05401e40c1d01c107a101000c004039083c8501440754103d81070700c050302c4082d21840d494483c04d0000030316240c03042d40003620f014a070405070000e0080201412201e15103c0c1c2141031084c80300002c55650300e902803214000708132049500d48051a0030052040c0007401450301c0540301e03440c0e60102960b030034141c5040011070000501c0c0900c083d00c1e40204001059507030002c1100b1030345500040c081103003c030a15041c91307100082042c1000301b1110010400e1402510f228658504699034048494080c0540000c0d889440d568020701d0342ea60092a2290328050191410400b88420036101c2500700301c082c1d410300c100c0b004011910304600c1c0d1100000c02443c2c1c000d0036020314000300181040805411740409034103006000303010035090011540e01e085007581e02001e02229000300c015004940c1c2c002581070040700107200540400504 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 115758732 1250 115757482 115757489
    0x2041a0307090611030d0218130c030c090f0e07050f04030305071106070c05190b070b040b0c1908180d020609060606130b0c010207020d051b0a0803030610020f100501 73
    0x20b600c41c41945840040d241c0e51452400454554020081078000d1071194026003a200c0c002803201ca20b10924100091400c0d10b111003110740e0541d1003048100866049c041c119040f0200d04191003050309100c101d06940d829070103002e158450300d8011950a600c0713003003200e01c25040002c200d81c889807240340003001c0c1d07808800d086e50009515401c0e09218a8030100310341041c0d0b070000803201441d00c1c0c40240280070682105542c04008402c0b8002003d0186034028919548580d200c80c85c140707010310303050303010b000082c010681100c0706010381180245034503046001c007041c0b03041104965403104016100516003d446035002c1c014040151802600040d4107070207170081d40c0c01d03104541e8030031050184600036147d07040d07940c02c0c040004011074a80e140082c8041c0010a00152802250303401140c0711040c291000c80301d5501015500045214014504008000403541c0d6030300ea520780710f503031541c0c0c0c040505054412280c440e08019654020859440c55400050660b10240242200007004010911 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 115759982 1250 115758732 115758737
    0xf060901050a1118030102091e040e01020720041d03070c1e0504090206091c06050106080402060304020f01022a01080903090603011505040f030c0312080405060105010507050102041a0307 82
    0x102085a07004103010b0394900f941c086034604d0a2501d5500d00020210b002d16005406540c00c101101e265266242c9044d00464058041114005010248002c42c0e00e14143c47c04641d2051100000040b04550118030707840e4101080310b0b81d400400f000500400141008030712416284107140704a41c00400503008080c041ca04035a100341e65a83e84841419030604480c8009840404c18001440e15510048039140043d04440c148400e6070041041580d040240b101c0e003009410340031301001501d0245c180508a6494a0b403003d0919074080b401c00d001c0544001c0c811081240da1364032603407013080307807215144405102c1c8410700d45128041c50440140180640080e0f84007000400e009800012107020388000381c9124503580c0781c410030f924800b9a107001041001000c100000d841040e24082d500650302982c1015109442c500d004405014403206520034803208004200200d40003060550443d0310a08006e540d40d441864964020304c07850700106555000c8a070000403215404000c0c1d40315a4058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 115761232 1250 115759982 115759991
    0xf020102100605061c0f09060e0d0c0b0103060c030b190f1d16020f07090209130504050c060d0f05041b1706060d060207050a0f02011407020603010905040c05030f060901 74
    0x1001c280255603903405840c2e0001010464501e0300000003840001c1c00180020015401040c0001a419103250940503149203846488100d5030000600c5281d852050b2424101944101580c402c070311a0014840a8072840e9501412020f4030b001c0e4002030660756004001c1407401ea03160300d044160900301c0c003914032040b01a210102e514280500c103c483c00800000c419044d80c3d03200c0806119000f041d9035101140501145101003a008206440c080c1030402c42c0503072540d12010900c50f6801880c5c0c04901c24900348018040030941c04581281c0391801994455501d2407103c8844003e440c101d0420f0a455152108010602126034000100688003e00c00e8234803d41da510201215080d01680c3c901c6074021001140c1c0710f00e809003250640d45c1c81014090704200d090b8880c1c1d030030841040c5050700c241c1c1d0200d102004642c0e201040e0104940a196000d0504d080c0743c01040351030005008500c1c0c000e584034040350038007005441c00b10003884001d08403807410f800d8000f00d6848aa003981c14441540c20f1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 115762482 1250 115761232 115761253
    0xa090c06020f0a08160c09020c0115060e01181e0302030c01080403171e0408130b0a09060309080c0f030c010c050315010e12011503030e040203040302030a12180f020102 74
    0x70034414802c03110000100345828841d00e0740382c00741c2c1c04602e5180354605800c000c40000f6100070711380b000a040b150001626141c280744d2141c2034411003050441444101881403000640080008441d81d8083c6481c032207180002c1c090845180c2c507078101080c1c04080181a0b01050341c4152001c003030300d20940c15280314281c0700d401550100d509841c01404a000004402c03115100c440320564400304085070300450040403542210b44100030380e0203480d05000003641d109180680c0c01100020401da40107149003150307039040109054007a003d04420183c8035071410f81032181a4007a21050240141628400704000c504140e85e58044a0582c01e00e5081900e0a101c0714080c90540b0b2280c0d5460898545c4060b40800440303140700c02030342c000d511200949a915004500740704d1100490b036180720341c44406041d402d0160180300e840e14440d100d8fd0042080000003503010064500f4107056092103a140d003c400d00d1100a0010103a01007403034030303060b4029801c0c8032042d60740b003030040e000382c00f0307105400b04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 115763732 1250 115762482 115762487
    0x1b0111090a05030607090512010b060a08221709030705030106080c1302120a09020105310801021903090f0510090308010806100302010806030c09090a0c06080f04060c0c0b0a090c06 79
    0x3191007201046051b5020130803814103241c1748121000c0c4200001c0c4942d80d0000103015a08007101c03190004140d0b40800501120042500c03583c10380000c2416007445981d40d640d4040b54401c5d81d0034803003140104044041d518200460005064020020310040303890341d034901d688100d82c0c0c510502c11111070316682404030807442210011271f071015103107443e942e618184101a1400c20422810024200000c007500069410030f00c00c03c2e04c080c0360210200c8003010381307110444582e40202c18076910403c0540701138080121a01846282c5040c04a2804d500d410300c801c00705000c050140160203040381c1e80ca40705800d80d200ea1a07091103174a80e203400d039807120113155880c0130417100b070304085104601c140702660140c0c1c4e5240d4001c000800301d44600d0a804003003429041c2c00da5540c081c40e03100342440c1f020815031030411800381240b494807501c9441c1413115003c003444080c00c00b60603d9610303100030307016601c034499040c03000c1d400014856107414480309174001041405800e443c07201090601142052 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 115764982 1250 115763732 115763743
    0x190c091701020a17070c021512130303060602150406050601050712080106020709090803040204090804090204170d03141b040902040806101e0308030907030c0312030c0c03141b0111090a0503 83
    0x200d6941300000b6039001d1f400c1c003c1c2c2000304805900803000505c18015584001c500c080d00c41c404e000b03420f0178500b1041c0b0300603080d15050340050013550844080c8000d0380c0d611820056216400240c04038103602c0b014010784007841072407000380c8440a20841d0400c0d59401000d420b0407a0002c1c0c5c01c4480d00342d600c9036440101e0340201c8001308464401c201003805458681c100c4100383d070080c0700441c6400d964501d840101e0780300d6171001c07604003844803801e0301503036043c8883d0b4a4842282400e0009041407511502e0300040100f90603c10401e40c28149490719049003610040d2003000002c6642e5911601e5482e0780383c10840c1c4c0f1400400040d00701188041040b210b0402d1b40c44034141c01d290442c25548c51401e241c0000305401000c2c802e0b0307c07000020442094420008500500700c81d40b00c045404030050a88844170700c410140480d0801450000e644070701180c0204c2440c1a0090716070034104240010109500d40c0d1400c9036003080350b604084200d0800a00208104842d449241c5540e01306264454 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 115766232 1250 115764982 115764991
    0x907050c0706020705100509040b03030a3603080304031403270703080901030902030f0109060506120304060c030503040203010b030f070501030f1a0105070312020414090f190c091701020a17 83
    0x4040107010346d0884c019005003104103001000428142c16840201e86541c02103d440304c00125001c00b11a1054804410418400d520704000f40a5807888031418111091501c00100700010000000b000e2502c5030b4030043c2032030700804255030f0728240941814124981040c910300d0502c4102816207a0f00c42c00508901100d600050303450500300712100540045c500410140d80501a415185104803070a200d00300e8010300c550400503c0b801e018003405400c99900c80010002c5d4000c1000b800115000054a8825585490b202d40c0d641d40d0b510110340949811120650148104109820310700310120740002a01d2003030707a0070401074821501c420240ca00320810410f07078020220854406505c1000201000d80c000d0419084d10401002c40008a034865404195000d16045078004a40703011001180c1001c040480c03410b480c00c190014071034003031840c0b201d41d003010f560359900111580034a214100800c80341c41034103501c1c04d01640c03c0b40030790300400c401000541001c00510480201d881d10364044c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 115767482 1250 115766232 115766239
    0x27020301121502031009111c020a020c06070b2403030c06040b090307020904080706020705120301090b010c0b1302040b030f030c07050901120f110402070312060e1b0306040b0907050c0706020705 85
    0xb01443e02c80f9071001041c5010940481c64070230403034013401108540805e429400418001a0b443c401c0d010003d060025450b1024403030700b82009024042000a002c0c2d940210000c040700700070f01d2444162407a90700d408a2500e806000c003080c80c1070301c0400410000d02c100c0c0135002800c000c1d81c882c00d40544034850441c00039840210074003c100814a48000340103100e1007450010710742002a1101e80c54000d10002840c4004000001808203a005001d500c41c039409c02e0038418001000b980e6844003a0310014001c401c0d8400c00c100c1c4c0750a654864000700002540542900c81150403140c041cac1c1c8a9005108140301403194010018840c2071004000e0b048030803889207402050b00a540341c80e484800840280d810a12840942c880c0e0f96a601c0202011031003a1601003000c101105050190361030303940a010014003500c1000b4080100303180312010280e85001103a50380e9a90b00000700280304000003290001c000f03404101213950401d0007480044e10182c21240d2495541c00200d03526621030280540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 115768732 1250 115767482 115767511
    0x609020c070e0903160b071206060806040b0406050a09060302010e0d02030c10051207090303021608031803010e0106030c0e0a02210414060405010c03060902040f2702030112150203 79
    0x2c2d0805140c0b02a005000f100640e89004015030319142a00e00005056800e00d00c000144990b0716046071288403802801603080c00424980080a460804001c0c0244d02850301da00f611302035503071a40d01440c09408010854400503407508000d10003820140801c0380401c8101d1388543c41c0f440c04000049041c1e900500a100341d03294002848100004000f40000b4410140401d43c0c68a03900440d0703d01c0741c045607543c90040c07031560800915000401c4e15a00010301c00701002e1040a45c080121200721400e100007080500c80c640110b8010710042e0f040070810751030079201004100031152114110f03081e407425280c250b190029040101d00c00d1014280302c85a14159081e801607030300c189190302a00030043c00105007080c6028a0a040040314104d429035034030290566099014400c100150071040021420641040c0b502142c0806074003a511300000b0800c0500b202141080200c001003040301130654803940d40c0c070303115038108818840440300d0707011180d0207040c120740a1090382d1151208400c54035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 115769982 1250 115768732 115768739
    0x806100c0c03060915022116171003141b15040519030b070809010501141c050f07060e011d010e04110c0102070503040e091606080a0209220609020c07 66
    0x1c005045654088034070703c0045d1440804019640f0190000c6c02245030781d0350f15101000d10011f103010005007080014204403550f41000d50b8011103440414205140041c8075803141d04901d030803403065900003064050b40b5201c0411151000c6420101101e1a1441003007884075602000720b95060448120311800d01072008210a1800022035044460b03003081030540c040d120b031204440c0c8070045600304042040d94080c00412203007486114014852265008800744802d1300240b40041000d8506089500d08003d120909c08148541180c42042000f03c030310599965201408180c81f608201c2d000c40c48850422030514200344c40c402c0c820505035200b0107402c160700204002400601240f0342c82000c10b0042d844400000d100030311049005800035600c0e070f481e1102071041c040c80100081040d03001018686c1c17030030302d4150209040d2612801c2580d8a552080100c10003030207002c400e2980301031034001c0210100001010100c803403d49010a01041d40c48003400c00581c403545031195450350002c2002c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 115771232 1250 115769982 115769993
    0xf0102030421140309010203060114090109030611090901030b04060c0504141e090c070506010f0e04081608040f170604030504050d020402040f09020309060a05090703030f021504030806100c0c03 85
    0x745242e00303460901e20081c103032540440019400464034000e55a6001007441000d680181030980e030240b0001c500b42c5840c00320030000304030141510000b0a400d4644603008400700119040e41c4000002510b10500d642c0e490601c030062460540b02501c80034a400b00c0c2c42c040703d00c15000c031403c0c0c4001c0c2c044040b10f00340354800c0c8140954030304154084d440301075160a14582e00c0218090140c01c0201016032111901d08005041182c1a444984c0b80304c4501c108001031964030b21500d61003500222996150902c4126501c21102c062000501d20680000c0100f1162000a20030007560a081c801100c00f0651031280c0303a43e11400e840140200700188410050361520040c0c0490482c8041c0c009400c1a940d03010880414000e40c008070b214680120402030003403410444c2036400700c00200280710608050880548851003400040e00300140d022403d030b0514001c01c41070780035071546001d403484c41c540b5042c0200038400582c0c20314410070980402002e11481561000600d80d00a01290221451942ca8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 115772482 1250 115771232 115771283
    0x6010c1211010c0201020912030c120906070605070c0308090a0309030803281a0102070f0504050709080d020606010e0102070b03010902130305030705250b090906040b0d0c080f01020304 81
    0x31441000110a4207804a06003806031200c2902250009030700d0380307280c0c0c01304044141c240f200789544c3c2c0e00030b108400e00300701e00051402c0c8101e115022159200103650200381035205114000c6c0600f8100010300c211aa0b02075203c0b03030b01e036020350f0b500da0681d100e612405032182d403518405800142c10030018404129107400031078105420544800e600b40c0b41200c6100301310903404407541c00320b83c2c45080034014044041c030b080e642d80702413019103410741c201401d8400b411702d1806061b0103203684000060903d40988112005000e0300c134200c880302544a14025a58a022102a800600c11203080e0019500028481d0141d4503049061803c0d42e00b46603480c03009400054400300a54800c20300040400e40134001044030b240075a010302940350048003108a0055940701c09900b42c00e0303483c0c0400c000c602c10019944845402c4495840a13200c42002074050003074001d01641c4100351143c44010040141d1040e07003280e00840c15919107980b018111801c130f00040364058902203040703810100000c500e100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 115773732 1250 115772482 115772513
    0x70f0b1e0703050a12020d1a1302030105032e020f0d060b0a050a0503040611120405010b0102030a0c0209071421062e050d0f0509060907050a0b0f070204020d090b0f06010c 75
    0x10050070044041f0014003592051142c070350451010091190703140c20001e1081c81304888443c02036143d9454840440c1da0f03010064103458407035400341c2002891240e01d1000c540d880c10700100075515900324113090899644070b16007004241c4d141c614001a5034030341000307a40c4103e486882d034030b08000c44004140d5203a40018001c0742d40c0d41d07842d08406405005d400103400200c50482c0042d40c5442e1520b4400c1c21500c2d00c086650641d0300c248600e1a485520110048405506556076811500c50304829141d071603814140514901004c60f020301c0d01c048440480030f04004c1c5400443c1e40c0c0d00c41c0d0090000743c1000b010003d04200c0101c030f501c110540d0f0041030f04c5d40c1c4251844c0047c540b6000c0b15400046914004108200300d442d1030502c801001704009440d000103030031028051080c074000008414244c10301c15400d00b1600428030840820758181911585038000d40190354031000b0356488170003041e074200d040b19514403000100300049544800c0c01d00c00d80301070710384840301c00c11071b2a209074940070400d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 115774982 1250 115773732 115773767
    0xb0117070302091509100e0606071401050a0f060608010b0304060c05120903030a0c171b04080f0708010522150b03030c060f09010207030e0d05070f0b1e0703050a 71
    0x40c0040140c540c02c40300d502ca0b03000880b0207102d5585120402c1807908000d400003105424049040c400000001079a94005100301c41650340e0390894507024074039244208400c0403079481c11b020401c00600342e81041e0652800391004000e4503440f8441514203580a000b54520a0800d0001a000922650021095201d241822802d040740700c0c0c0003034215802110328041c507410200a00041c14203034045e01010340001d081c041d030644042034240c40503e200401c2481d24064a05c204042514004220f138094403002c0251030001006503c00c6545695502c00c0c80c81c03a61a100000d10b190669080728203080b400c3c030000950704d0280e510f4070310b280340000d9007600103a5074a00314644642d50410042180c640001c015103e245058000d01e42044001445c0000990040042c0c5000a51240907154144800c65540c907010301e035420034501c3c1039800c1e0411224050a29800300e4001000c0025003251402100c1e4141924040078002205008a40b801000718005010054082c1c1c01512510103041182 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 115776232 1250 115774982 115774993
    0x180b16020a06030603050132040201140c010204030b0105100203040e06010203090a080604030e0609100c17030f1812030601031e0c030b0102190209060d0302010f2a03090b0117 77
    0x140c0008203401079552103500444c1e0b0340c8400b002084402e001d0040794040e00321040b092050001e0400d048a0710404170f04040c0e03032000000404680c0242c0c500c0700001b00c68015075480340303503078281c45000798494081924400d544000000d810301e40010b83c0d400300e158542c090340c1418a409840d800004025240700d055000521000741c4070340300e030644540182064002004503081c242000352010303030700300025402607034100403c0080e0b448040702400c840400d407401240006282c10581c20040d020030031214502c9002050159003a1080d607120700407034410a9083c444010003840940d80c1c1d00c4140c1100030000140000b03940c560007507015001c0c1c01d40c0800034202400340116004102c0f5030f8680fa44012966580c1903003042c0d641001003200000c1604000b60f4112001d400140150300002c110700d11880c104a202d80c1054400c0d0007183d00048003410522090300361901c2c091890070402e880d868000004802c400c0400c1c800d01540b411580c101700358403456400d00040030300c0244003016642c007078410cd = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 115777482 1250 115776232 115776277
    0x504060f02151009180c12030201020706020307020303011502071a0c01020c07170d11070e040305190f0f021c0e0a050d0605040b01050607030e04090c090c0c03020607180b 75
    0xa044078074815040121a92080f5003007413900c1d400c8469206130781030984a017a69604c005440e41d000f83d4265100c4d02140c14000c83d8901d0128061b11036084010502400030003400900c40e000005941602c0c803000c008200103940300c3d003c907a0380700688100724103610f54030030300301c60b044000006100041d0044005403510f0001d2400c940b030010580d101d00c0022700010b4400807203d2045c401b21328800440e24007085240382a0403411394032096805400710441388140814101405042180c0f550801212089110700c40e600c006001e50310944244004211409110b010b820310100d0001001404202ca50342c00f9040c920040707540050742c03420f0701c0e0400102000411a40e440300d0204004521401000c9540e00e002d10b4414480101070340124052081400302c0c000083d009501000e203420261000136000c5401c2c00c0036205000b1550144107410714148852401c142e10082118601d8001e408440031500e0b0b100d41154041c015170200d884c0080100000d2144812404c02090241a0003040300304d0081e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 115778732 1250 115777482 115777513
    0x51302030618010609090305090915130f050f0f130201090503010e0303060f030f07181401180b0109080705211207050111090907050d0e0106080c01031a010504060f02 73
    0x201640e03074860000ca508500250910701340124030140c01852010301c81c00d40c65680c0541030f409490100b078415528940042c807003800b04c1e1411010304900404184a9041001c1954003c0010100341031032a400c00b80040c0c1c0e40f0110200c80c0340108032038022001c1964071121409030703d10804a08034104a02c0fa4000600c0e66002d0158086002d400700203940d0300e0078100c040200b941c0e0340754090360203608103002d8094007900c007040c11412200c2c0003c0c0401d01100b40802880140301a5040e000b100e8080c08c004141411050788500104407001400c200e00e0099400550304910980b10340300c410b5100503c11701c4242020800345260440310360520040d02c0b80002014144241281c51070008407010844805100c4240230b881d900c0c001c1200024640703400e001c0420101b0b4801820042809000280c8541e4009141d2203c0d04160752500208541520354015648403001006040d00080c1861001701425000d050030044a01c0c05866645c5401d162400070303118224000320f09d0b8158054112400b0800e803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 115779982 1250 115778732 115778743
    0x12050a06090e07050a0f061e030216030e0306130809040b1203070302060f010f06140304140109030306060e061603030e03120403020703060e190204020c010e1005040c080a0b070305130203 82
    0x140007405020804e041a05110f40a01660b100001d02080170030100481600f040700036442c41c6400c85007082ca0904c5c003209801910070104400d000c0c20031105500145030340610201c60900089099031503e4840000445030740c0080d110141038404204a4252185860741c01070f42c1c0301801624540b042101e2056035405c0d504003a009401682001301005081660600410301518451040d405a1800d10034020254800343f5a808501600040032901f4005042e680a4442d90480000d2201d41c3d59454001c0103400c243c421304c0041007458941d808189002800d45100c00807404000c1d4070307002d40e910f04401400c0304154002a50000f000100c00040c0301c00e85441c8600c6c000c0d0001c0030824554034180c01101da0b03044075007201d03810183d42108692441036091003c00d4045801684680c0a107440c28010401e0803031010382c620520040000c10b0385285c0140d1b100b1406640b619031400d9a030051182c65000488004044090f51070004810754025401a50006ea01208040b5072550541c0441d2400c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 115781232 1250 115779982 115780001
    0x3090201020c043206010905030a03020c100519090e060109060c0f0c0e18060a06150818010606020705180108120f0f0c0a12020c0f0409080909100303021c12050a0609 73
    0x200340c1130410007296044940c00340105820b400602686603640c40085d1a5107186010303070b10030081c2e10070300042e40d44603505403190741c01c8140d1040003555040b040541903403000d1040f107040913614000070b1543d60140f8030500854095403291250144641e807008040176109108880040e84942d0208810707c800441c684241500c18840e1084509031201d58078258000784101107041c1000420b0000c14a4039007d898180b2403030600101585612040741c0c1d07280c4a0920700d845a6103084400221294001403030300c00c85005444000d2041e141c0310346604600000d024510941e80240005500704981000602b108024849180d083c810081c150701d04650101e00d400c60b240c2c0c800700c0010280a0f0303c100d02c0110480c0340c00100b0b510b80c0f90703030081440e0040201500e841036540305441803d108600d001c035549651700520058140c81d10307030308110102810f070006a00610802c4c01c81030040074902d14080e0503220035150348462480124120303001d4180104900c0c09161190400180700702c0c1409441c0d100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 115782482 1250 115781232 115781321
    0x20a05070302060604060f03030f03142d090c09090a0f06060612050105010806010f020a3207050603150607060c030209033a090b0703050d05060103090201020c04 71
    0x124440c50400901d850b10103000030384624a4441c040281c40e1441c07520404403585410702c60340a210307120040c0d0007440f00c4a86c0940012080c0708200201d0a030840800c41c049000313030b481c0350568000815014114044443d02a04e600804106001d0328040c0e0105620160b00822103e8596541d91400080e4070b100794200c4d21651120001c0c8844c5070810208040491540410011340d13140c440020117a0780068502410302183c0004180081c2c401c0c40010f642c56000a0b00e050480d45070b0b07120851100d005104100c118050b10051468032602155203402c580004144a0440e10798503441000c040c01c00d100c440e440711003040f100001900c607019031002ea11035a1070051712040713174200b03040c18408101e0030b0950b103054203513001d580d0a6802e5841d42d03001c1c625040c0480d0426030040103031041112504004440c044c0410b40400b00340d800001015041d2003128203022980754140194191a1101802805030700520380b0048681031540c484000c015100801106a140010300004001d03054020402d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 115783732 1250 115782482 115782487
    0x132c0c0909101b030c03020910121103040b1815010b1c05070903140304030804091805030d020a0e1e040509160611060c0f04030803091c0c020901082a13020a05 70
    0xc0d415101715411038000f81030035468950008001040e12100350000420301104806503039900c0b02c0d0358811504402c000c00d003207039a81024109102d8078201142da0070030071401c0c0040e00c03080a0340442c0c5202c501c0d0180c18008484e03401d0920880c81c58204514017507400d0801c1c02c01e81403000d900c1c0500c500500140e11030094490440c01c04000d80001540c807070740c3c3e9a00820003040003d0300b620480c1c1c1122810100024091200d4095148441c00c296002e0400d00c4040303806110114594010403036020303540c40703031440f0300454001d004c420500240010b034000c00e20000c20520782026007100d0f07441902d40040d91681610b5420b02090754420303800500002c1c4024080a508150410816400007a11040a414514030f078813001054421070000400070752011021031260402044200407a1000c040d1000244081c46801040860074580c140e00c035404510000950132008115a00c00140842c0b1030040d1202d582c0400074000c00040072140c205c1003640c0e0610405942d4400740c1a10b10301c0d5602d465 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 115784982 1250 115783732 115783781
    0x4090c02010b041415101b0f0b1e1302010507080a0e090c040801060e011212030e030d0203041a240d0803180d020115150e132c0c090910 60
    0x30a402080c805e0300841c41030320244550b070340011032080c512510ba0340444c003102561801d501340801c1d1030002400c4422280c240540080c2c0e43c6a40300714020a031508014541d41c0c0c900e00c022200315188081c0c04503004000d6030011031041002042c9081c0c1905291202c00344600c08650408021034406e00f8920000c038040c440c0324000c0c02a0030040c60180e541c54000c1d4100021034141d016812001000034061400c50304495009030010301c01407080320152602e8184183d1100041c0d80b00321000c032880d8460f1420380700940440030070640074400296804201a0044113500443e0440c0b40d100f81d4084a900480303800100110011841100800f81d03902d0070300700c242c03801450b144d01a071b090390070b43e4180710300d0044a8201c200c40104440401104400040c4003020542d6405c2d01714120581000409010b00c0c0e140311540c00c003503010204031025000421194000441c04030b07510540152640100f0300112441c030380500c100c0d0704214500152004d0745440d9401004403604010583c1d0302c0f01031421200b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 115786232 1250 115784982 115785001
    0x90606070219140102010615080709081912031b03021813020706060f06080a0228020c190501090312090b0c011a0f01020619020408010603150f090804090c02010b0414 73
    0x4586203001c0c00248110303810801c2044080700c88d130100d81c01700045400005c00440c403c0c08406c006006440589003055840d50078002c0258040006880302503c44130b04000d458424420301c503414960359206134500310041c2084002c0e5001c8003101203c00b0001c1c204a0855407a40907a00c800c0701e1001005030341e07030543d1034a07030306442082e1301c483e10800a0343c104104190700282d403640c0c040303a031900050340c1d81c136850f40e8910f562022580d102c00384402440c0240e062030700051008100382d002c0b10010011198468070840c801102d0280d0303030004490010800c006280e00c0070341c0c904038134141000048181c82d090480000d401403000242d8680d120852100e00440d0200316124504040d42c5c90030282c40e404002075525003002d00b0300595019084007010030f0401d5907041c0c1c6d01402120f002030100e1643d078146900c29546a206110180307160040080f0140b40314460341c0340081d403043e40079040c43e1078404280e009050040e60030080d95211400207403295160f10554060901c1945002c07411706015622 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 115787482 1250 115786232 115786259
    0x50a0602061812030411030715050c1c0f110c19031b140d050a1b080f010b0a0308030910020d050108100e1b010203041715090307080306090606070219 66
    0x304082c0d50040b030035401c0b0035411402240da005410120680b410600000444d1805245601402a95007140c040c2071051b0b50000050059003072640446810000e0340a003c60040103200700500030401c4803000310302c454080c00c0058140c0d1030b00e2041d94071801030040490030041221401c0c1403140041c0005008001104a07004550a640060b890358070b42484028151001c0f07020b409031146810781e00d440e00f0001c04010f4170200703590000ea101110914410311441051a502a00310140940f81e00b0078558901403042c1c4e5512500180060911850b685420000e41e0002d0700240c014041c1e21905a07a0300d43d940028041420030788070001e610b615100c4078604042d80c2402b544803081c1003500074244043d0000d614035900b0b5011130401c45192010006070300d107100e244d000f46d007a09149500c4000143c008110744040165819080304959107042081e5200d215441c03006010500030b1011480c0d5081070210103600210103801c242c540801900007c1e00003014801510320406010420b00c4807440c001071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 115788732 1250 115787482 115787521
    0x4020109120312020304151b170f0408130f03050304031505070e06160b0a0207120c05060a0b040b030a110103060501031505040209040216030314071403070810050a060206 75
    0x12a1281d8036555001002116000c2a41d007481d500400840c0a01070fa4409180d04420500f80400c1000381c1d00c00d140c1c407204a24612100030401011072450700b66241d0f800710740708520f800a08500c41c2d99981d59000130750004200035201c013407031000214800304d80040c5140510300640c011034803140741d45440410a0702584460300e181d4141401d118815030010200c0408500031140140c4a00360000b2100524044940250800015400780030b44d01c0c0c00ca42c02004500c0c001c612101d400d034080c840507140000341610090403544280c00052051910b50301c83c10451304001c201141c010380c9840001e1030094584000e0381c1d0500c04031721050722580c01d40b0841000340b10a080038402070100507c000008040c13441658056500018940341c0d0b95526030445004081c050140340d41d184040c1030003002808984001345040c550880401e4029014007880381c01c011180e001a4074690381c00704200d903440c03070190000c86806c038140004030f074a540381100b035005080d141e8001c0c502c07494410000d1400000c1c3d2034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 115789982 1250 115788732 115788749
    0x302040c2f0111180d060b100c120207030209070f03061203050c100506060919031b0f05041103011415030106020d021902181005030304030b0603160f050d0c030503030a020304020109 80
    0x8000c02030300d01d403910383d082030134002c56a800c21065941814401340450880b19030340261200c0040359103d800905603d4070030b000c0e1210000605803400140d03a9040c541c00081e500040f03010002d010a80f10720210100f50840c1e203004618640c2c0c0b0159000c00b0003109004030040749020500d00d029110800c0030280c016680d8806015505000000c902e62f4410510060300582c445500c202303080c1d0305203c40400840e405044403d19605c1c800703114060303048074090a8130078042104001503a14081c0038180360941d4500c4500d103180d10f0881c0c0104240340180c04290000307041c1854002d4080d842000d14004d0002e500900910040240020300b02055074401c10441d81d14002d0100141c0c030b4000100c20441800c010481898444000c0003880e10115400715034140300000e0003004100e1141541c40c0200c000b43c0032602c10244240c3c060040380c059001d080036810415004002d60314111a01004140c05a05d0b044119a101d4452078110740c01101d02825498000080c4804c550703114551200920100303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 115791232 1250 115789982 115789987
    0x3112e03090501150f03150c0503010b030a0e0604200901030c0b131a040504050112050c061e03010906050108010b031012020103020c010e06010f050a0f0302040c2f0111 74
    0x9600002442400505010405540382007620400c1025413000d0f41c007030340302c8a4071012a5070398020070b6020b4415000c100c0e181801d50303100072002565400352840d8600c058994904503030804502d5100c035013009140c0a07420fa00c07400101c0b8404010b00109001e540102e00c045811092407011014a408500c03030980203429660040010459810300e603c00c1d203007006000c2d940c81a809024840c10301075a044110700c2c01020b0050121104100c1c014400c888040c1e6007400702c0eaa0320a500d080e680740807007000e800394005810f42e00c1c51b8035203e0300802c0960701903054a10040c042608030710007600242c0040d181103a07260401d1000d9a0020582e0740189000d0000030301c1c0d46854000a131010859110741a88803035440c030080216802034054840d0105400000c001c800703011200e280d03440400703100d40c1c1c0e00c0300c07940d20000c00c0d58101042a001526003070450310301d0161861b401e100c000d043d03a1952004000700003002c43e4007503242e10084501d049041d0340306200386082c24502400c5405203203103000c03088004c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 115792482 1250 115791232 115791289
    0x5180109030f060e19053c01020a0f030921030609020c0601170f1506030c040f0c03240501120204090c08150405010e010302010c0f080c01020c0c06040317070501020f040311 76
    0x11f13815500032249050041c1c108400c0c000c0c1e20382140320358426007008402c1c81d8036002102e056000d096454140d5855615007011008141c045035484d010252070ba0400c04845140c01140c0b4034010b0690001c3d03c0e000441035601d460200481e0041501da0f070440d0406001001142240e04801481c03096030400f500c15043e8035007885591314192951031b41d41d03010180001e80240e4061040d140031040240040c8605010519814001d210002d07500c0d010a03d0310011180c003140071030450503080c0308170550312000c07405c00c00150750b10340071a0845041d1580810001ca1441403070b003e803d001c92003548814007e0700740000000d50038600c80c1c10407801686071038010070902910120b01d0b03045940a00384148194858180026241506170004d80120000644081c201c40d05600030581d40001c0c6080d940ca80d1102004c0203900e12030b51001030034840c5240c02c4080001c01c25001085000e1140000500c0e010b802e02c04010980c00c40d43c01500c81052122000d20070342405400c01080e400768a1115040809 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 115793732 1250 115792482 115792493
    0x5060a09061413051905090c0304020102012f1c0c17070e0d03111e0f0d0c05030910050403240f05100e06010302040806010b0408070b030705180109030f060e19 70
    0x26a21545202d20501004a580859803021700c1000e0400600200b040d03103007403080c000d02131b13000b6a412030042d860702100e0a1015001d95018035411038200074038180301c0e052814440d00e83c200c03100c890242c00840c1858609000e061140a100011b1621030160407400c40c1c501c1116001c000702a00b082c0300ca0b1100441807641c440d846c0801c40795060404020003040c0c07200c00c034508031000701170407040017003907000081e0fa8400042c80310284032000226400c03508441e004640200c1c0b503001c0205154001e0150b41083d152410458940640c0342c94450b00b01556612100603402295548100d40c1c0d407d0b400f010750166490294295000d0000e00c24480c50a04d0f02c100d050040081c40313640081c5a000020a4030740e0301ca901142e00501c89002200d005503112003917007086034801d208450b51485440c100181e01c1c1014401d80748110910f8540c5030501034065500460003a50381c1d596410408424004030000e980750b02d0b0303078080c036000394000a0402e0030322090b00d1409100c403c0c9000e409505044000002e40e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 115794982 1250 115793732 115793767
    0x503030f04050402070c0b0d0b0405011e031e080409060602060106140d05040c05040c030204090c030504170a0909020a020a120e0a03060b030102210a050604231005060a090614 77
    0x100c043e1001603403809a81081352442440760000c2080301400540c000f003011280d0859500c20204a40801079640e980d146004900c180c4000e401040fa4154010000b00c0c1046044a41c03400380340308400804400c03940c48028079407080c0c00140c2d9980d959141401520b82c10800b440c050945400c1c05050182e00784518010384c0a0818494109611100054100684090240c00070080a8010300007140001805406500140180000c442c0780400e207150080c801c3c007c4074015600800c945440241c02e00c0c044215511400900c01481f0032103034005007a850074402421b120b1201c0e4081d01812a40b490400c004c6c00d1020070702006c00450040c3c0740c0e556600d00d4039810131641d20030000a00040d4101c0828064010840b0320400540b4001410034014000c203403841c4600c001d5842009503594500c1000708441e0000d0b507000110b4010107480060f81e506401a50304404280f00208070700e90348500040050f484084501c00050041d901080341c980c201c2401b004c0c40507000c011904009401941d0b81c03152 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 115796232 1250 115794982 115794989
    0x8090303060114130510050c1204051c1106030112030e01030e28020907051b010908030610020f0a11010f1119020d06050c07142b020c030a0506040308010503030f04 72
    0xf030b50006100d40126a6900c0c10700002c0c034026125000c480340701c0001070401e400a03001e031205030092007126403408524004039000c5da00010103031550140400345030110401a000100c1d0b003c0c8050314510039039660b41014500904440b041a81c0d514501e10b0000c203602c1c80d8246640c141404c0c9080400d070504080742c3c04031440713200540c0d00b81c0480c1250704012403c0ac000380c01394011030954103202d112a481002049094019000d54004800c510175060880b8012500905010014004101a071405542242c031044140c811034030a00115035105040200f100d00440d00c0030b00300841c04a040d40c0010300c0060300011400c200e40010742c03c1d00056103440190b080e8184255100b14144119a180c030364002015402150030410ac0c9042ca00002003a8400b4000340d0f071480f4a01c07500c9808010005e045042c25a2881c64818914010700d0311710384058061b90f01e6020360040100041c45134404000c6003048500600050026003000c2c18042d15603201030300101e011340c0040040c0280c0f042e56030110f0741207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 115797482 1250 115796232 115796267
    0x9010509090a020d0501060e07090e0a0c0c050607020705100507261c020405010e0a060f080a0f0c03091e02030a0308040309150302070204050105190b09030c040c0f080903030601 78
    0xa603030740406040c100b0341040c034000e600004080e01e01003031050541c031807415198100d800c46140d0321000030581d04102903201d840900d08580300002c9218009030803001040c1103608002419801700d0b9142403d1803030488400d4016441080100014035013070004204a041d00d040081ca030201c5521418541c4440f21851010b404900e000c02007851907110440e868003683c00d8951590310541c0b408030029511911946001407a8104c685480b45403040e0303500126042520fa5041004c251601501c6079040207100304005542c401d00e03066901c081c0c0c060780d134203105030382c3e00081e21000615100080b080b1000c030283c3ca803004c1981601c0140c030005200c6543e142c0506100310590368030705d01200c03a20155000080035002104c49501015015000703040140e00c00c44003440680c0c1c07560188620b0403d0707070070540ba000d03207503010400c0240c4560b802000d94500c081c046d00c00c41e0510300089025215160142130000c0c82d500005c02c407050340002d10b1a0045000d60146295003002c40000304100010183e9890 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 115798732 1250 115797482 115797499
    0x3070b0703021c0e0a060c0c0c08150a050703060b040603091703010b04035c03030406050c01061508040b07080105060703050901210606030608030301080a0602030405160e010609050f090105 83
    0x804020170000340d42c2e40342c1d01035801d10082c0030f103400041c50b44164800498501c505088041080000441e90140c001c5d0b105490784199503883c203424028200260200d010702d951581c0c00305103000024000c0002e88504d840200b1590340790320b844115a11344804c4061610818401844640fa1040c00c44044a42116605a03650340c1c50040e001814420072800035002e40b0090702c40c680e0300000944078148048240d085010701402c502600302c0000110b4020344c150410841072000b90b00420150903660144000091b01944130311000d01c10035081c21400c004200720310204800c0203462094594488904c0c60014903a501d4000030031028022400b008080c084045924100c0380d215004156104411080d0500c40890942d0510010101d501030a000a4144003000c10354640c000112412500c0040040c4525000c58540310000d4001502c120f9260050042c0031000e8100168000040d10504004c80201d515046d0068408140c030b0380074a004900002400341c29030356107002181101e609403107240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 115799982 1250 115798732 115798751
    0x2160f08030409020f0d05100e090a030806060309070f09090507080d050301050f04020d090f0c08010902091306061a0a0e0907080a0c030b13050f010506040803071403130803070b0703021c 82
    0x11410f000d004403185030710b80b0f030000b000200f2023030b08400412115031840034149070b1651801c4036211450924003801052880020136281d080840c0290f03441040d40080d41c1e00b181d1a5410740d500701a96910049241c1d84030b191850507c4000c2c08594020710007080101071407200490081e040c0d010520403039102e203c10407090070050300c0d1501100d001089058041050080350324190240c0c6200d08001d460614192402050300c0c0300c1446488102a0000c108980c3d5907950541d100f660007807040222400c988445000484c24941c2843d625164204c2c04020b4885a40302c0f4018203800460f07000b540704ea8882d030180700d021501300c030a150700103a00702008941d03081030441c02d4004d8046803a51581002046442c07061b4000e4660016004071600f0b8100180341e60b903030701084201d00840c054040300340c000300541000105181d10041c0c02c0d40742c01c025079042c118404081c0c920402142d020074415040011508208440d4842c1c10350302c001a814118100804c005501c11201281c90003d10455500c076400c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 115801232 1250 115799982 115800007
    0x14030d24080d03090510110310090510121b06050a030c0201060f0b0703171003061505031905070b0f180d0c060302090310020d02040302010207091404020d0212070602160f0803040902 80
    0x1400361b450604284040020390044003101e610031582e4455100c0f0504003c186200140141c0c1c1c09040c8d03280014110782d04100100e4841c00c4401e2003100c102d650b00d40c5402003010b4110703c01008090580b50f2a40300c0c10301142c0941620040546c0408691402c0010710001050f02040c40a41d8130210301c1c203480c0c448a141c1603a03c202c1180112140c0440300d400c0280d002a01e040401c1a00e00c18102800040309101041080031894015158103030415001c0314000072014540318100744c055001c80381843d0703640a070304035164400d050611041c540021100701004440601c610040020740d0420005803040d01c52415041c075074000c0104041d0000346a10450707030208046011200031600441d0742ea0b55045100f80250701500c0224054090140c0010705100130f03124051029103000f40c09042541c80b07a080200381d260580089074000501000780c601b4550400c6200003921542e0010500f031915024100600041c81d4000144200b18510900c018100407041d241201c0460f030380075172600c1c00d03210003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 115802482 1250 115801232 115801243
    0x60e061f1212022d010b06250f0b0405011b02060412030c050909090f060f1e0705120901150b070f0b09030721030c08090d0c14030d24080d030905 64
    0x44007004c0f4900400515440881071030f00c140803e002044407441c22028805d0380d000d00b0500c18500481c5da5079402c0700051000e585400e05115514564850082d80e03504c1c600c04000340c0f02070703500340c1d521503416524002210080081c0c00c2540020321092030300e03548180c441c0c0314100441c004c05494044003901240030380295080010024071050316813a203488e00307035921041c040700d0128074072410b0049825290f1068840307018100c17010219210300311a681440c7d50220103880304041000401000d03980c09400c03a1018041e46a1000105454681c3c48000b118005943c1010700c81900c2007141c000001d0108055400c0c807940a56001040d0317648032052410b600803d4000b9014085d00f617071404109050011900650720036803020080004202c1c002c540c01501184c81e108540d2140c8004010507006070741c6101c10602c40c1c0e5894a2084141081905541044542d00a19034644801e481c1c420344910343c0f13035951995220510899450202c0c482c1d81c5aa03a0b07a140350a260f0340e05182818032800340300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 115803732 1250 115802482 115802503
    0xb0406030f020a0b0a0c06021305090c1b01060b1206150a021f090c0302040906090c0b07020418030905100c170307030c02070b03060f0d060e061f121202 67
    0x81105503aa81080410042003007000c82c40b40200541c041106070341d0000782c510340c000d1341c0e480e04407200440d034030040294807a41c4001c04001c0c81e408005100e58070602d01d40d1040da40010860b44804000c0160b651001800f00c0202c2981d0500380e09000a21801c000d50740501d60840e11895551166800300c1d00c902807100c82c0d06491000003840e41000d070f8000aa288003007100183e50282c490100c8030000895240303a0004041e0303084410f00700050300e030541040c5442401610000f4416096aa550000460742e9000d0250b5120116400c000d40c5054880d4124442000140c5102c0d040d055900910380285402401d1050801082d0850001d01c01ca91381040795500011000040040d04000d4109420441d201700000b42070031180d010503440810b11070201c400d210130301810350700c07444104070b804942000c01a0b08000c42215030004031300d180c09850740100c000300103450b440c24414004190300d2000702200542009910342044052901000c00020035042040c0b0b00101e809600e0480c1031801445 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 115804982 1250 115803732 115803739
    0x4080307050c0a08070509060111010f05100501030f0207150e0f011401050f0d150b060d06090b010212030c0706110906120f090d050301051003091403042c0601030c030b 74
    0x21030300100800061031582e4150200c505040c4a6030301c54030160b460380c01c0c0c05a690402030500200783e8a50059401d0b5800348607407000800e0708010020490120b94040b0b51805446c0c50440c0d0801c040d58041c8100340504203103140075031a29585481d030f5a400080549000040c0d50740b2a507601412a06008540810004000070301143d540881c804005050a003d032510540c01c1c503400b0781c41460b18051400031a42d1104002980d4100e0399248401420004589a0803000410465982402a21034030780544140940060018030301c200080c50310781d90b0b80030003c10700400c00602501082140540d6201540070360042030200500d039120f5424050754019940148010900c0d00300140c1142045101d1131703103a001d00d000780e074681640680d00d9001601450115100300010b006508028503918814441070030301103480100b82d610300f25201060340d0901c00c0d0760400304090080003041450030003141500022401615402520003102c8c440203498a41899a0f8400760000c00303001c1d4102e00007072480103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 115806232 1250 115804982 115804987
    0xb240f040204270f02030105030c190f08100509010606120c0c06020c030c0d051303030c020303090306010b0a0909021c0207031e0207050102060609130b0711011119030902010e040f02040803 83
    0x60581e940c0300320b007002d500034800341030011006078808288203403170407140c8c010700910a1038011814404014810420446041004400801e034802c0407c1e401000f401040010301075007900d1100c4074100c40014120517000e0f410040304218483d8450ba44504000185400080c04178400905841e005d500354001401940041101d2603081740c003001804140d1815000e9500d00c41c4201012a4a48200284546441415003042c800b282c8200d01c1a000315101070100c070302e8141e088001914144090307000c060b080d03c000a0041c20030764001c031408010800040c0c1541000d5140b0454845a01910080b04c000c070741c04a0301606042c816141d0503071450007040b0400d8110740c1010000d46501c0710b40240350140c481c1e5404581c582c10070040491050021240700135048002e075072804010a0302920510410855003039070000401c080c03150a00c01a013078914982d584d0411024410f82c040c41040000925251085950141c1d0b0001040c1000318070450300000e5030030495180720020700640e00014011b1002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 115807482 1250 115806232 115806269
    0x50d171b010f02270a0b0711130b0a0b0702010906141c05070311040f0b03091507030507090603021e030613050123030609250e0907030b240f040204 65
    0x5070350080c03004038403c442d2690169540c814550940f480900705030b4000700100300800446c580c08000e804282d00c1810788240c02050480020001100c0c0c160300010166207078940051440c041c071002d8000d1540740c40d024100301c21500007901c0e2510502c221802c0c400380c0b11076400c03000000c8003140c00015203040000500c04900412100400d8216080da01007840c00904106010310365098804035400301403020b0145082c8107485880360406421007107a849106680e41e041098150014403814055400007900c1c0f8014600030303d004070f00d07400341007814030400c0103401000d06150407010264038104655940d032110030104030780d1014020711002c0300d4a064004687c0c94840d13401e842260034403150010036500902d041540302d1400351001c14113130748034544e555803440c128061441101c0401e1429144281d4031080c1c414640c3d01103400e0049504000c0051003000400da0134543c1000418100400810004000d46600c0044194652250301c4800100410f0782c0d4a40465003c0c0841802d0ba91201c0403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 115808732 1250 115807482 115807511
    0x109080a06050a05013002031e010209040b09270f1e010605030c01081501180306050703050702061e060a03061104061101091502070f060c0c030207050d171b01 70
    0x2058440301e01c020704100001414407004002d13018184c006c006800b01c3c0c5c0101c0c006d01c00d10035a60394400c076058003681d1441c04132100826500810300c84298000f694403001c000800c422078a50341100ca1045c5000400d00070107200398801000140382a440d42c161015143c12034a286c1000c072488204a481180112841d4038690b949200c0c0713144051009100d201c1e2a94105500c80c960303510b82900140c40da0000840e00c1305d02c00003407061460b06061005c9030b5040c0c0c0159900d44072050300140c480c251034006101940b07515102d20382e40f044640c8013601080c140304d42205048582c02006140c554500d40100b12a6a2108500e50003180d025408000542e8428810001a00144100342c045800c4d076141c14048c0906019420082d60321008003a00031500c0d0b0107020094006210a950800700400281d00003104c1d80b141380071505080d2a0000c0090300c918000b4071b411070540025016602c8070280340006074a814210103480f9030040e07401e885000c0214028450751012400142035820540003035200315 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 115809982 1250 115808732 115808741
    0x11803171504021b060f040203030a050a030605040f060608150901060c0303110a0309050f0609060105010f030e0105070801090f0b0d02010e0613120606060503060109090c050403150605040b0d200109080a06 90
    0x1540c00091702e42c5030350382092580d080082140d000e500754000300301c03c04005204200426032043e4509000034125180e074085030441d11203a01d000d0503e40c0c2c0703242c14800b007034210511940c46200c1d49209002031445a003c540788000c1842040203102460044a040502a41024044121403080144c5649507007a0080c09001c2c5000e0a8425018409001c50000f401041d90340c400c2c0c4110008001d039034030300001181c80300c02840300c000405542c0c0042d014017181c2801441d0044410381d9840300c0c03e50419452100b00c5a14210844c0001d02d001e0500d07240d44c81d20405060300d16024200300b003002c940d450115503036210f10000030014605c0c0c0034011968180351515a0b142c540100d00402202d52070b0f410aa41034801900e16901140046208011000351a00001c00100d40d0b85080760800350b9a90b104c050fa03201c003440b02120306480e02828442400c003071143e5034045400702c03a1200409440c0c2c03590398064444181410315803684034071101841c5d015900303a400818031042124008451820301c43d00a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 115811232 1250 115809982 115810027
    0x204020319060b340f03020129090a0203040c0e0403030204090c030506030a14123105010512040507030c0308130905100b0318061801180317150402 65
    0x561521001060348603078503040e582c0402440d000b0700c640c0c0c90004c0400e0400d010325220f903014000780d401a0000165481c500b840b0b014842c0d0001b040c1c2c91000300d11120100c400407205002e60070034020480e1a60349100f0860b130040d0403c1c1d4016520b0b111801c241054112903041001c200c81c0700c40500c820554154001d104580001d201042404200b050840640c3d43c10b44110740c5c5544004e4895003c5000c94035a440d48801020413075400411480d09410b13a03800caa40c080c03000300601c0c1c040300030030700014022144801d00000c50315080d42c1404d0000c1e110340200d03550000035160750300000e01001001c201c0e0001644d0016a131142c440d0392480c061969510800c003c0c00d280c00e0b0f40200103140236180c0541401480c10a05e000f100d94101841300d000344c1c00080003100250400031103110318074400e01207240100402045842e040d2410030515094840001005a13204110203816010a034030080410280180107001111078a07603007180100045004c002c10340c454800510030311550341180c880c0c0c181 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 115812482 1250 115811232 115811281
    0xd080a02101406130b010e1009030b060d03020706081503030f0901110f07090c050909040c0e011d010b0c01090210270e0a0902030f1603150e0d1101020702040203 71
    0x2c10000b60401014004107450b4250480ca0b81e00184880050a0304041c000100c180743c03250505a400000414034526007221402060034400305009000c400c410250f800181640d200541400560b0002e40d1491f95100d05e00401c6a002c010030244911000d40007001180201101d46501d138000070900c081d4008242140420100c0003108007540740812582c00342620035002e0244c117840c0110f044040c103001a000000c00c0000c0002d41c6040d500e41c8600b134003540c0503141c240c3c82e10781040e40403582410706820036171080c4041c0d103024801ca200306d003505047d42c0ca464107081d00e8564110556000d00b0312000300a500000308518000c40070780c880a41101e540310092404250703103801c0034800030b03604907010700c10040d00c01c00c00040141c1500e4105a40881c4050202d46041a8489400381451041d0010700369402030300e14108140842c1c028120815030008208006500d400715816a0b14820364a880d01880784861220503024429815110a0394020308103658078500882c904c0d02903245034460515 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 115813732 1250 115812482 115812491
    0x304090b030f060604021b0303040f05011112041115030f04031e0c020d0c0803032e06051603030617030903060106050313110307050607030507030e01180308090d080a0210 75
    0x55490001620310b81c001c00000506401c0d2501310500c0085d50003441c0c0b0481c091411030303040f03155845c1007000318402c41c011800010301211b175180c110f082d11f480200c0030fa0f07040d2081c04640e05011100707511907009640800125540344815000c61003007406030350b1052191502000b000700c0c0c2c601c1d01c0003807445036210b503445401591107241140c1044084034551030003d08030690110042c103018040d410032501032954182290742e290394081c6142d008036143c6282a80383e004400394110901d10420044055440c8841d00e14103040e001081805620840c4400400c0c0c0700704103051500a0b07000c040944070180c040d0042040e000390407039a9502010300280684558400042c079580700d2130959025590000039090920b00941710009840006c29000c0e40c540109a0f00060a0381c65030010308a031807090721a607454680b81c0c00c010340301c4607104203940e0511030407000103010301d4900d440150649901140560301e400c0395101080c034810002c80010560200028900c1d400e0b600060f00c41c00b41d4224103330510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 115814982 1250 115813732 115813751
    0x90c040608061e070e061e040303020a060b0a03020d080307030f39080606070c050d0b01050f090c0f0c07031202070f06030608071418040b1918020d03051605030409 72
    0x14440f10045400344006200031481090030302d8140d0007021148000500e010f86038149401481080d4810780c8114090380c82106540b01300116030040b488200412107c0c0b07171021b855500401c03140c07040c0160080c422000000041c0c0c010340a6030141c00c0c4022400010081c0c581c0050320314822141c0c810700c00543d4000132004d15100d800e10b040c10744942e1a640d03100c0100b912081c0a018079908680021a140d0a8602c4003082640300d5440e40110343d405050149415450417040c0310b030a40c0c02c3c13880f0601651401b8108a02c0c0c44480f021107100c210000415075a038401070417010308080440d007004000c0c0340081807200c40c09500082800a88640d010440a0159255025000c0710784030b100f00503060700b0041040140d18400c900e44004404017419600d110040740441c0c4200c010111000c0b06d4400d00d40c02409611090781c2444080101200c01c10800c40290401480343c0000310301c8024031601d41d40da0b117601014480d106a441e030409244242c00c1d048103a10b0203075200d4206004d604c06045c030b003c4130b0b43c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 115816232 1250 115814982 115815031
    0x10c021b150306061c06051c0209010302010806040f18050105092103180d0315120b040204050705070203061608160507030806030313080a06060e0f0f090c04060806 72
    0xa021500d004003100200d694444551950b60802003a0580c0300605000c19407102c3c5c0c2c0240c503581401d040c007800040c040d05000801548648054401080a056464100060726a40321060640b074090030301c0c0e17080d95901c40003d005408061080740141d8280b03261009040342c040000c400c62803160000340065a507030441a0741d01c5c0d81c2034884440c0d141450000740305200c403030801103400c01050380e80f6500c04100840e03118502030880d48840e00107503030f406180c0c44588000c90001c2c013500070121140641440d0361586404120003400283c031031070b690b0f404104014000c104480b583c96000d400d841540ca05000709058044058244901140c00880081e4600f141415084d110919030303101c440c03c20149072811188114010038290b0544420820b20f00400003450311070f0000e022050051007044034034600300090301c07800d42c0441c03145c0d441d0f0300501010840c0612015403104c40f00b090002545d54221006180c4aa160410790b0031500e00303800428402400300b1a6481010040102c1c0381108494150 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 115817482 1250 115816232 115816273
    0x60f1b0f090f0f09010e0a06030204050f09070603060812160b0112050115030f060c03090503041e09020703021c090e0a0204030b07020a080301120314191202090901090207061b02010c02 81
    0x50313011210000612140300c21880050300031b58050000681940c0b2580890b00b00c88040d60b2441014030b0380810084072103020450b20010f0301d030724a014001e4514002c1403e1b541d0014000440f002540824000700c0f42c00014008001d854000140040c1940d5440410700e10060b81d980507142542411103100d00c003091404154100c1e54403c14000301c10340f1540f0340c00c00a00801d03690303804141d150180000410310406c080c102400040e400614074960304040c0000c2c5001ca0f9015455490050060401081d0041b4503010b07101042080c00c84c1d4881c3e60b88044034a803416411221210440034240001d900c40303503001c0e005680c892014046940c8902000307a03138862880b0801091504100f00510070132030390b9946000e24500c0f9040c00181300b80c0840c030303201c82030708080000b07580c080029200740e40d0264030204030046039048900031440d140300d54010400d0108140101c0001d00d40010b210010400c03590b03c181c10b0309800100c0180c01444c0c07110028060300d400f450881c0188180403254911500d10200e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 115818732 1250 115817482 115817509
    0x1808070501081302040501060201050702010f0b03030a03110f03010b0a030507020a0b01050f0d08030906041e0c151e020105060f01031109040b0d020d0c0e0c0309060f1b0f090f 77
    0x400045141000459944900030903014145075001c01880061701c903401094060940e58002081d580703890940242114014100010454140001644a80c40100c12a9012509454017144040740e40045180d144110403030103006900000000651600307031405401d880165580c240525149c5074400c80e07403460706280c00b800700542040108103602e440d4094a040c1100030380024000301040c2c80d00561600202c40d102d0080e04440c0400041050050750300521003078030b07014031700f00c001251259501644d0500a0000394010074418982c010f0040c3c1d24003506085044ac1c060300d490419030001c1c0038120a486035401803c401c003510000d507000303000350000f40b1089201103043c41c01030410440941b00c01e684042d00010a0031101d000f42e02c030300019425540c01294400b0220b46001d1012100700801403989143c8041403042c090780c0c00000c41e440343c0003901e0b440340354187c1e101d100754080715440250100f410f03400006001401d910f05040646244141114a0300784880302000388504220070ba40e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 115819982 1250 115818732 115818749
    0x10050901080c0c0c040e1018060b0103021207110c0a060c050106080c0d02191e0f050d080a03050603070b0d06090b0a05010c0f080c0607030f0f06050a050d0f05071518 73
    0x840310310b07041c160b2000c2001e40280c41203400d01802516501d04440723041d03800c00d41e45900c040c2108280060f80c0200311405100703290451510150407502c0b400843c003c2c000c4d100f000100301c501541d030f40b010041001c0e0290014801035450342c1d25180038141c82c01c100c4003124a5424000005440e81c004101c0c05c4a20401400556151316994200200e507d80c07080f035a00610b440744404109000c90342075205020b051244c640510505040c0c01c0692101c0c542d20540c4145442502c00d80003c40b014290f91112945060101d606d8444200003400c0860b15002044482404600c0088169068000001b110380c60002042400c03240400c0c406141380c5c82c014180410810b18901001074002e99448008500488965040042c1c80d02c0441c1000ea080c1c420b0300000b6210300c4a0040340322244900d080890800d002001610319000106024500328890300d032040100c01500c10901070321080700c0c28915841025a146261185050980715144034400000100e1031480300e5040746070702d03014034180d0743d070766 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 115821232 1250 115819982 115819993
    0x6061b0634050316031401080d0915120c0309021302030a230705310e0106170a0c1103030a0606090e0f0604020d020d140a1109010512060105040510050901080c0c 71
    0x142d801c030035180d0225260340308051b95800e101081411110b22540688690b40260010000126009000308096004074045504802414806c00d80002410040d03000c03a4001091134111035205400134654504041d400081101c1c140051007040c3d4021440340c2014182081240700c041c00004840c2020065103080354224000300b00114002e01c050b00050185401404040600f421461082c0000822304111103044210a10060170401d00c05400351580703162002a0140c0e50025407034008000d040c00000b0769640400d54480d602ca00300098001c1440d6048030f541e4141101204000c04040c441c3c14002060124040340010320096824061a0402c00e0b002030b40d1110030812000b584611800081d8544c01c01c03c10903003820a0140203261300540c41401d107145440c1d0001c10986403501032041d02188104000092a03170040195030f070003000280312851a6490500580d454456604a0381d8005002828110402c2d800001041107440c01c0ea40c801041c1c0b103401440301030340940100c04000340c220 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 115822482 1250 115821232 115821241
    0x603210815041b05030a180f02090603031b0c03010e01020c070905060f04053d06140c0f060412020703120f14031305011406060306061b06340503 64
    0x320000081d118400400018070880c542d8140d5404941c00811103010800c04000c0200506940c4104090140100c0030041680000d07079403005521a0140000d109048400102c0e40e180c030308000741d8034a11000700135140c900c0c0c4510b411aa64003d03a41075244650300f82400c0e102001f00600a1740d804058034002055061308100020717000d004c00070180341e00020307050660345186d44c4071f0246501401400303050310700305400e801c0034050fa0402000000b040703039480d9039a8203125241924030710445007149866280016038200e1601c0622504e030013913003148181c407421580480003103a090b0240b4412001078090004103042a606d85519200241c214078003a100142c00d28000c1b0002d03124103080b4034120405110380210742c5034540084e10b400c0d801217617075034036401040001d1098640705c285403a02c915240c0f80003c001a290b220007048d03240281d1020030001944101040480109150507043d0b458074a01801500901001d03000d500c0b40c0c6044a46069008a80340c080c000c00c00c1c242a9a81da107590384 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 115823732 1250 115822482 115822501
    0x803040609050909010f090b040302060f0f0c0d06080d030219080f0a020f0909010f060f03142e0303030b010e1009090c020304050306010b04080607080112030c030509031006032108 79
    0xd00808040e01355407113110141100e221442400b540c1071180c900d403201f600f82410001d140a0b00100f00c40c5101e20f010041c400c40d203401c8602c441d404440e81400d556280d80324050300001e046154403030394080c8121800406840e4040c2c02900401601c10110300f600451103200b2281031038190340c041000111300b0045a031032a4560010000d050b02c080041d4030b88250800801d02152090340100c0e010144044140f02d0b140d444840e461442c2190f00e0107003c480400c00541781d081c00081c04a4410f1203c820011403040070318070900c40701c4000c042e042c142207079481c1009405402c42c031000741c7c00200b04414241e06444e00c2c1c0c082e0400e004260380c0e500012828451504020041d0300d81305425440705000c0000c190b50708000d028083c00c1d2a5052a4030345162290091400310043c06007014441c100c1c0051161042140a030350b0001d805241c108021002c50409461503c40c124551fa014002d2540304180c60742c4540189080707921414a450520b0442ca6100d8200f51020721040e00055220020949201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 115824982 1250 115823732 115823749
    0x504030803060d1a010e0702011505100905030303010b0a091203020303040b04020a08030d0204090e012d020d0c020a1101080601050d0207060b0d0b04121704030302130b0301091401080304060905 85
    0x102d000c2d01000c84400f480c2c82d241a04a07859250124407660500184590305070801400c0d013010700350000380107118a60300340446c404e070b6600070540162500c880000b00b8038841e24141e401031201800342c0c2c0d982e5031202c03004080399200100300c0000c00c401c88000520641e4005d242400150150701960031a2100e540d51560302c100035001786d03400403011101150100b000c0c0010306c032401540f500140d41e5450403140c242955001e203500c2d02180d140403510112500130740b462622a1410a890100c01e010030400e034030080c01240c17220002c00f458440c0c48243d6a0700060103015243c010007903c07001400100c011600f4000848a003030010b070041c0170ba9804890150090810140b255401180303840302440400e458003484039080c0d80500351a8288014000010301741401180145861403411403041ca0340d02d607c0101800040c1055400211a010316000c442d81002070041500c0c2c242d5696500c038100c00c05400790a002c1800c641e880000003540b028008221411101c640d240e100f9400e180008222900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 115826232 1250 115824982 115824991
    0x6070f060506010f140a140a02030904140105060a1b050d090503100911010c032303040311070609050909010906051f080f060103110d171207030e0c1c3008070504030803 74
    0x15100102c000501e000c000f0303055230052540150b0716039282070100010b9502c95030020340031110303943c010300458607408200c8450520350b042c210211120036800045c000e0321003c000c2c000b0300030550703101310182c0e100608500b00c400880403a2017a131229000442115070300315005000e01000d00c1426029401003006402c1940a401d055000945104920700b00b051117061a60541000004002c20190040110310400082c08000d080550030010040c110030701c00e003e02c42c41481e01c5000608501d00c00d412038003001d9880001440607042c480c030302d26602161400c04c00103250361502c1c04102da1100054100d0711a01c0c14004000e02e0340307507803502403034a00500e40c0140c1180d031031410100811440f11b03480401c118402e88a60b51041a036180045501c00940032500f054280840410803600000b9640700e03c400031512050b03084d400c1c070700c540c121700380d84c01e0700a151381c0030303001c48221070000d000c81100d01841034141c205143d0781140302200c40c0c1070212800e40201c0c0e014001800841c41d010080d5500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 115827338 1106 115826232 115826237
    0x1021b12160b06040603020d0c14030a0c0315090506101806050904031404051002010f0606020604081207030605091314062403070506070f060506010f140a 68
    0x9054007a5000d8690840032001c100260784940c0848011036004080340010300c118a805c003100220352080008203036021343d5000090a02188050165074003e900088450039580c4d07550780350507803460050110f035990782443c002070000c10042d4040c20104070303a201450b2826100d40780b604181c1528138412410f11342c08201c5c07030319884280c3da0003940c9420280301c041007000c40300006000e540d10142e402440804140107140d01903000ba143e101c0042410f0001d1501e4101c166501d24098070300030f0a1010410030041039031091500036812a0242c42e020480c1e580c0e68000604a040507200160041d01c980003017420481101c0d502e0400700c0c1c44101402007442c01e14589003c64101440020002100c40b0040c1d100381d80910850002d4503000b4000381e00c3d0f204e03a080070f107040310300010101c1c0d50514080204a041d03004140c0909506001e82d41c40540504c8030084011540142ca8500d05 = true := by decide +kernel

theorem cover : BRFrame.Cov 115647482 115827338 := by
  have h0 := BRFrame.cov_init 115647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 115647482 ≤ n) (h2 : n < 115827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
