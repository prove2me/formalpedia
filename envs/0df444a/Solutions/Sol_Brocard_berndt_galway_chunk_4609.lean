-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4609
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:10:07.290311+00:00
-- url     : https://prove2.me/submissions/a2d17f72-47c7-4ae2-abc7-665c18b156be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 828776978 ≤ n < 828956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 828778228 1250 828776978 828776987
    0x70807060507110a03020d110109051e040b1c02011803020402210c071e020d02060a0201020a080916120602120a06090e0d1211070218061f05041214070b0a 68
    0x800d00710549132810240c0c0b465020501000c49044040c003100e0040c43c4020143e1300c03410700b000c01068028041d0580072a000c00755010b4001d400f008078170681c40c05a018681d801c1c0700e0502401900c0c0524001b0700d0500c00d40040d20400d0302d440c0060f080303565480d00070006030790b5403015001c0440342800d50318040b4001911101750100160120603040c80c10311100001408004800512940044c8600800b1005e0320102c1c80d404c43c2840001d600010200d44807030341a90540c05468070f401d00e43d80b00c03a00e640783e05400e16110303e41d041600008942c055014840922100c90403004648607000042c6450b0360300c5000b2043e100300703032240320300c550f190b0b88200204207050103040105201c00c0050031a80088200c042c0c8000d500e5826127206584480062010f107243c4421b83d2078154014191881001c66186804450702c42141c0700d0f8030031030300801071000140421075603203c8400c4a4440900c0c190138488842200b81c0040c07021620b209000d10b58021a2070107000c40b03402040d0002c0032a440e42d14005000d007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 828779478 1250 828778228 828778253
    0x4020a051e0408282f090603030d0509120309150a050f01091104050604032d050307020118050d030c03021b060d0209040b2107090e060a0e070807060507 67
    0x20015030040c401800711060100c0d070600c4c1c06061003451007280118564100c954020300c4c50241100207000c40c12200d84184181a0001e2004880e0352114a0b250700e041100e603402c1030b100c02d60150f000b403100252000751684131a8108820004031221814403040f10720341d6900444103000035400048162405025900c0b10a4111804000501c22440c11030000814210144509200d141e110740307100c491401440100d4010308405014140e0f210388a0420b12582e00004007c0800150040e0059010044d5031a41d135032460f0707112020714608100360f001100c0c940d82d1641c00d020354401d2144000703030710b5403401040c508881c0700352100e40340b80d245410043e084c400001c034591080c40c3c1440b60380d4000c5c0c0d15041241d6002d441464010703107079480d100101d0010304540e0040c2e5040100006408002c00000303070b6054200017400102e6542036111103013402590785200b9664100d40c04800030603001c40140c0c20252300e0182942c2183d03d99569002818580010b541c030190228400040003014401c2002404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 828780728 1250 828779478 828779527
    0x20a2309041e141501050f010309120509130203150405070e0109050d0503120c130801020a0c02041a0a0611060604090f0212030405040c0909050603151b04030204020a05 74
    0x4008900c1d2503241c5007081c2c2c400c8042050300c9482030180a0410031040b4007007040950600c01c48590388070120b12208070b88428003401d8071401d005440d001c803d621901031071450540c00324401c2c40d88180d1240940b81501301c2d045083c2d002600806100e01c5400b0340c8083d511442c1066001e2486683d0b403400d01007200e00280112080007082d410501e10759802c0600501142c20076900007800d4a80e42c1065819806a6003526510400c42402d02415401c11009000030300f00c1520318014196888030414201c4c4034032160343c408100102304080151505070310590a03000501b003034105580348500011012001074000d0400b00d1004c5000c1d0701c0b44503003008040d07481041501c0812860405454402207984100002403181c00c42e0b1203a00c12038001842038400810003e0000c0c8605442200d000d0080c0c1034a01a48030b01514090019800d4038000446204050801000e00c0660b110070785c1254294030307050021400e50008010020058861b031008103000051981d0301c3d034a40588414100c0c0300386410800b17 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 828781978 1250 828780728 828780739
    0x17040312120f1517010e0703030c0c09020703020d055e1202120d0f080f2a0c032109030403050c0d020f06070c1410050d0c020a020a23 59
    0x11a0358911240703400585446144076402c008204101601405812001c6c0026010f980400010580c03c40e181d0428140708a411440c0580c4400c050f0341207005101c0040e0040e4410076001000600401c000d101410250140380c1d49461000d0640603003106203c0c01c03803e1030020341e4188417507445058036440000c2d41c02d10042107a4040020203483c504042c00b55480402c0b94000f00030855482c4607800f00051458802e0340c4011000400181000d40500c4000c000301f0300c400c00140012900c2d6040d144190a80708040e07112205150100e40030150300303101101000001c0200071101c000800c0a08609604001310b800e00c4c650340601c02c1c40402015005a40551090006000040300410540d40d00c0c14143e4004a00342410300004c1ca03104491711610703410000010b170950034000001c6841c400c1d200e0110603001c1c107002c40c80501c1440101c2140da0790025401340b01540c0740c0c5540e60882c0d40070491910403140d0402146d0002402240168804591007c0e0010104981446802012030301c1004464 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 828783228 1250 828781978 828781991
    0xc0801180c0221090a060e211e010204090e0601140f030d0305150603070206090d080705041206060b031603050f130807060e03030c0903010b090103030c17040312120f 73
    0x100a0b40e2500c2141c0e10300c246040e6a000c42921140c3d00301075030301e5928002e1010b108107640300000383c451544d25803031070f01604020501038080c1040035440e1580c0001c90005240d003259961306030b021a2100700541107555000c0200280300040d901803e050350408001a00a07540340c040301819004101890070700800c0c20340313000314a5960100300940c0c2c0c0500d508000c03400c0d64540c0850000601c0e1012241e600c05408410b1000e25540015164485d000c600c04450020b940840c0c00d8510000490b80d490001d0002c1100344640022403e5080c0303901d11070b49001c2285502c07507d540e0301c56041160114501d1880d941d19144003503050280780c0d08240a0210000181805403032441c0d0400c101602400c8000d0000700131003080482d50080308100f11a9040e45d490741010045088503620050302e80b4460341c00c3c40ca03007600300d242c81c008a41c1242e50503204c2c810381901990300d003103001008196901c0c9601c802d02001002c01c1c2c0e110440c40454200f41d45140d0780400342d103403540480380c050340a084481e02d400c0c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 828784478 1250 828783228 828783251
    0x5030609030f2101090c1b0c090b01230913020c070306020714060c0c0d020304050d0609051f0f18022202041802040807150e10120c080118 61
    0x2044602c1c0b41a4440c07040d43e02c90460042c0180d81c0050400052142e00030400050b4588055026104441165031903404100d50151000e007000203003034002e040301ca00404100003030000f56011038030300301301070400240c00305041c03030010708961420a842010380310014619100303107040c07401e815412003202c8003141401c04d902c619903a55180f038000180496400101030060001c642000341c9242c044c0341c2144c41d18034194080d881c0c1d98020103240c0f8200d00c26010142e00300c42c00070098a0540300301400d960030000541e15600003801e00841c050b0b68a0142c10040000400e84010109016400103800b2400b840e14041c5a0100d5001c24010100c0000c40200701c001030751403c00401000c80694041003e4859030820300009200b05c1d4000424415100025008203029070007410480d4028001c0e95120b596404600d102c8042e1403d01c0c10014118080c02c6501e890326403c1455582c1d483d00d403d4003d8944580d0350012282c110a441c1d01140d500001004090145004542c81504960091100c40f96a9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 828785728 1250 828784478 828784483
    0xb040303051008120307090305030d0605040e0106270e0d020a0309050d0203030d050c040b0408070f06030506132d090b0c04050604170319050d0b0d0809211c080105030609 75
    0x18901013410b0310740000030a410900c2440310002a64004040d00c0d9118881140c00d00100901e1240e14007441c284111603480b1a8180301c1d200803940c591081c030341a5009450210b411002080100700c52075500ca095a811105c01c003c1030f5440001074000782990010742c00d0240c0036420991002e44070703440e0300880d040161404016101c861b01d10a0340403620f40c582020080c014002c0b40c00c41d05940001040c0014680300020710002164040c041c0c04595980ba00c4007102561400c46103a40c01801251a41d0f09540385076100d480242030003050000e03000161608416150b01c0c0101d0030f0742241c1c8072000300050002e403e5220b40c00030080c101c014075144c502000324886009c0c5114103003243e004098004d0500c4000e100f03c4094040c00f00b80e48403010a80315010302582c10542c44801c1c0e06182c2005401507082500e090300c1c0440d00510302d41d003440d41181c20042c1100002d030103018240c0d0301040300100c034036040110f241154003401c01c0e6010540b00e01c40051003004168065032180d0f018005221404901 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 828786978 1250 828785728 828785743
    0x11b0c0b061009090b0a030209100303110309030303060607080d020a03020403020f010e1e031207030206070207170c1003090c0b0903190b0f040c170706030c1d100306030204090b040303051008 84
    0xc0b00130210f040b48450b000200c8030761695101075001040001040a008085c0d40d107031081c1c030312a40714078001000da150b10b241d80b17014031501541c1550007003021034068a042006081114424070245140410000203039082e070704480016404640c0214080c021841d2100c80814518028038082c004012400001106010782c1802c10700074001100301c01c405a10280300c189a2030300c41080b442e60310107003860029642d000c00c5515100600400001107000144c41d1703210502840a08014120720150404006012002c003c0c07002c04d06990301441d1000542d182c020720010b0080d03000d240d84520061061505000c180f007800744808856452110000318010012508010143c5081006075942c0c50088001c0b8010741040b04c0c85139880503011b2001d100010700c1400d030382c51643d080c4108512020151038070380301c1042c42c2d02541155004a4464106200c507040910150b103404125540d8035000328084070340881007650443c40f103000300710515815024094001d0862003035810030034908001c09494081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 828788228 1250 828786978 828786989
    0x30606040506040b03010207050c10180603050c04080d020a120e091602070b0f09100c03051207090f080307111207030f030507081b0c041509050603011b0c0b061009 72
    0x2901c6000c10225291544400ea0121000c0c0c02190384445604159a4440811603410300ca90300002c3d01d40c41c454843d166002c1d003a52108100e00a0b242040b0301600605001400c0700e00402c4140400110b2040400841d041d03c026500580342596050400e41c0004200c090b00e102440f401e41050f09903a240c3c00583c0380d02480744000300030012502107049007820701c41e6104030452070000c6044500411300400815105204a56001f00c3c0480c0402c05d98952800c120040c000c1101405401007650350300c4034803a4001060701d4084011600c4031000b584d458442e411814183d480840c109c8100000034456881c10780c2c044405901070051860000d540e01d0f070900004240d5a2243c02075000c142c0198260b4044580c0031036003540314454041c1c008808607004010385803c2c882c1401c20002ca00b494805c000004142041e403640244c1402c5002010f4a0701400f06030300f40d035941004514000c11004080400c0215035141056000d032130801e02c3d034006014024034850000d840b000040c040c3c22a6102c4110f41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 828789478 1250 828788228 828788231
    0x30403030c150501030b0f13031d120f0d0207090b10050c011808070302010c0c030509012609010b0112060b0304030e040207140102041802040e040b250201020417030903060604 77
    0x701d20b85030000748070341c032101080702c40d50402001100b0045e0055a551040001400309003003039446803160550075101c5240940420007019180c240b00d401e540300c60701c180b2000340032042c9003072280540700d02d41a0044c40049564024000c2c06030350a0381484a0740042c00395441c03d102e0b100440001901c4141c81021355407d006c17001418020341d102c00e411050340c02442c8001c0000710340c85414502c41903449400101c0041d4681400982560f004150300002c180d019a12682000c5266005684818411441c400e800d03d60038a4110108618031126208031040c80005c5042d018450000d44250b8485042034001403d0810520001c001d2105032544907030107141c800201420880802c00911551001800041b08003826100c1359a054000380210b600f0340d00c0030b0030b01d903c1d80b01601c4100d0285001d04000240110040b0300402c04040702d0507006801652840c1c0056046c04500410040e03e002040250750080303410040d040c103d00465145805420103140340454190000f81c80d10300c000c000b2032155 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 828790728 1250 828789478 828789497
    0xc011a06030c0a110d02011505180f1005030f0c030105060109031203021e0a0e130e0703230717070510080601030f0213120b0a0e0703110607060c23030903040303 71
    0x313108881c203954111036107003912200401c4400c000d0192006129481140300340600001c1d0354248213000c6455042c414aa002031912048201c0032131a2002d4403c0801601a010205907a941802003081e00541030005218000b1590185030a4907402081503040c0090072108001242c0501d1140c40d041820707140c010381e0b40464031701ca840c01c07004120042c1c0d0901e50115040d2807040e000340c9444400007040340c0490294580759010341c141c0f0428000030398185c1100383c04000256202d4204034072014120b42450101040007489450404c80c0c0e489011060101c44600028138018000d903009040c0c1500c45044010341040301401c1c03001c0c054025810582c5c0c5407440c1d80d0b003884503815107070404501584902c489946424880031401d1080d4240c41e1320802201081401e0703128440d44d004003c07800007800d1064a151558105034013160310300d0b038200c0000c001d00c00014155101e4040f8402daa5140c44180004030006009001032007508901c0646d0b08000b4090b055100006450031030b640344c034000d10384 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 828791978 1250 828790728 828790747
    0x60c0b0a092a03081218011e050604020d050c040306060e160e03070f150305090f07060c0c0e040305180a030c0b09030102040e0a0501210b0a2f0c011a06030c 69
    0x30003840e0f0300140a891003c00d085c0d0301c0c3c4a03031680d0070703004d000c0340e01030501d030590307100c0c046402c85d5540d0030449141107a001c19240d18141903082198020307401440103080101c500d0000d42651000c6514030003c40b0001410300c1013000500c108000b401d64602c400e052403030215405022041401284028070414040400d126038081280c94081d0100d03c45a0104955844000c04029101c08420020030b0526000403010240010908844400b40000300b090b0380c40d14105550240031400c00f0394642e2600c003004100042c015120602851181d946c9640d190040b11010201111a04100384507114078141040842e581c0351406003901d2040e07000c40e640e1480c0200090080c86070340d121454000700745003040800c802d564441c60495040c070ba1600c10442c070341a0b4055040c4401d1200910305025800032802028280d40001500701c0c2c00030b0381043d94907040c00141010f4195020700c1007141000120076030003d4080c0074407400c8101c8000f401d204250380000251301c60000030b12081d0145000301d1200302 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 828793228 1250 828791978 828792053
    0x200d0b03010905010204061d030703121404080a03030f0b24090d050105150303030f0115030b03010e07140d0503030a0207050a0f320604030c1b060c0b0a09 68
    0x9400000400802880c000751800d203010303404c240b0640011994440014000c4a2856886005620020041d150460960765000c0030240311100b1002003100800030703484e48044010080000d020001c0c000c1c0742021052500078181d4107100b800c0710130a030038541c900c071080c1c03030f001d142004000100c1100700c2080101e00c2001500d0180c0d058003580020400c01b0017080c014198040307801501746243e60401c1d0340d401010306580340300986606100301c2c4158010040b8058016120070404d0a500d8007048824985000034250b505042d65403c0642021204014901e188101c0912030817081e00c0c00a44402143c0700c0f40c1d20b03808010025155613400050340001c1100522141c100303d5071140c840c245121240c204503000769231070345d0b11111002c1c2100e400c40c09881e01650402d20302c1580741c0100074139a69075408580021500b0411100c11a107000c2c440034406c0043c80b02d0b800b5140c15070300c406d10310b00d950a0490326400007400091042d0f180500c0400440d4401001603c1e03016603007080320245031403080c0101d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 828794478 1250 828793228 828793241
    0x504151b03112503110906010507120909020a021c0306120809120f07080f010212070c0f150905011802010c0b090307120507301103120a02040513200d 66
    0x1d1080000100c11640f00800780701ca00650707000700c040c001d281454106010708a0700984035240410001d000b804006564801d80181c1c0d00030914203961040c0d07482030a04c0503600001c45140150304046051428020a06608441114a0f02d02448405c1c0340a03480c0503458500720b80030b841c442c00003a03003051039118030f079445011040f00000c40700e10020548a66032605054000c00714503002d4050400d0700d410050081d29018400384d000801d80f502d50a10941e03140102030350884601c002c104080011074900360541c00b0a192403c0b0205421460307181860850306a0f00320710b8410404102c000009d80d92100000b28520f500104500043d00d5910185207076000380c0600910b580b08001d080c4030f510740c0c4800a0049240300d4200740c2c020390940b404103003054802211030411300700c3d80e0000c1741c8007034071400041426100c2042030380d14149451a040300010405c03194261f8058000400b003005041c12105880c4544480d502041500f0064900d0010854401240c620120001c80e00300400e007115070100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 828795728 1250 828794478 828794503
    0x6261504061d07020601060903050c1c060c030b01020c030106080706052b0b2e030b060702030f0a02030d140f0d02090d0c0305010b1002150403140a0504151b0311 71
    0x210001c1041c16000b0504210440d00c2c4001401844000200540100149170541c0d91000c085d000030718403003050001c00c4a14201452029510a00c0f4030080b50092094440c90074040e07502007010210540064501502111150701907803601c1c130b0400c03443c0f00205580301038600c0c43c0b0301a655242e680c051452400e1447c0355500d081c3c0c0702e803c041a84481c041c2e0000071290400d032100b4010381064440300ca80c801031034882000905507000b0700d903c42c5100350301201100000410440c1408890340220f442c1c1150280019030750752284412030198501082402d050a0082c600b02c0580141c005601d5131602426140c02070030000890003840040b140d030140c1d03d441c1e6014015a1204050341003c1d10400d00700e01c0305496552038041034200380d00346800840f03d641003d800500b250340e0486c2486408840c010410380c2000410224989030592940041880c00310710b540309502c850512180c0108907510182c80000e11a9402844023072028410041013025054201503840b20b0343c03814050708068170402c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 828796978 1250 828795728 828795749
    0x33c0309030f060105030d0c020f0d081b0609060f011208090a1505090f0603061e0a090207140708010c0f08041a09070911070209040b130b0c040626150406 68
    0xc000b0105000641d8504880b02241103c1406d5182c450039140b00d0704142029400480049150b0300c070f81008580704400d207103e83d40703081c90585100140410701d071400b517150040d03400100500075010700c01c12010f44c0000d140361424000e07500d4450450301c0728050300d000a00685003c990202c02e81d8690050f03000518a81c1c1d590b403141500d001009001d60300c100c60f00c82c41450801c0380e550032420300d04d0949101d0007000e050140030f648880903800c0c100020b0944150320000c60390001c030303011949001400109200d82e501d21108032400d51440e003000302c550842c1c400e5030701d0300c4207440a06074406501410340c0c02d80c3c2400c8806441e01d00340714030340b2441d20802030000309140080c0560900002070840446010b44010412000310180c02c0f07206104941d0b02035440b10341c1102040115100303143c601d80161034460200c010040d02e0f5221043d01c01d04846416010f0f0021500f08641a0402042d04d030040800e60401400c0c0c14210740034083c0c002c003034860700007526603400e148625107649c1d1102000e810146407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 828798228 1250 828796978 828796993
    0x315090b061c12030e0d26040309091805030403050303071b11060903030c12130e0c070318150302030a05090102070321060506030112031e0504090c052205033c030903 73
    0x100071f009074080032100f1001c4c1c91030003040707802002d60b0b18010b405503500d41c1c0c80c00540d034501068500a00920200c1007840791a508002002813000c00060008522031409180c03a807800c41d4020707084802d4078010440071500c8043c05000100c03420300840040d601106c07102e442e03e540c20701103451800384064402c542d10070f01c0d203070484907000d01303001c0c201034601c00043e034001646890014000b070700290341c0f10010b620180000000030340100501d2420200e0002c00f00621580c0342c2c620210394100055001c04a90300109105890003240111607010556500942c900105030b500240961135000d1500c22011080070350601414003608548001c0c00f000f040760b0748950b140c035130540d4001103440d0200e0100707000c03010044068031004240c0c0204645600c44904140c83c1054100146c4130f840c031034104006c01017050110f0180031020800610023906820994a030408090500d41109442c4131182c140407030806050f940d4401c010307800703144d0380b2400c40c4006c100300443d1185140a840301c080e905029105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 828799478 1250 828798228 828798253
    0x30612060506040b0a140607021207091b0305070c110a05101e08060603010b0304110402040314070602281406043c110a0315090b061c12030e 62
    0x10021400b40300112400c000300e00450003000182e03d403e00c520101191030480b04819458540050034180c0e0000d014482c0c40010504454108040c40d00303c020b0752035480322000008006034550800c103403010704007005903040170003015054030044a030081c00c210003602d0342d03101500c4060100d401000701410f10042544000c002500064000b0041c03075141f034200d100700b09020f00c40c9000d01d00400b00900038500e10703408c0c00c0840342150300042096071090705c801881c1d01c442e1201d100a000a40c095044041c0108031203102c5410f091882c4d00020440d8422010b05480c0c03444a4444400051f0400c480e2030404198030740b03c40f519110440c03461003130040d0340030003003030208051148008080405210b804512090900d40700d9070300f141110039101e261071101800290007031800c17012405004040c1d0170b000d0340e21390700c043d842035540445042d01510340d640d040070014840891074000200310b40c50b4001d00305192102c0c6060310844409042c044081c14003500c114000c1e404000d0381c2c41d0640949070402400c0c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 828800728 1250 828799478 828799481
    0xc06020102070b34050c1e0d03050907050103091406070e0310060602190f051c0e0402041811040f09020a090e060a15021203100906080d08040803040303061206 70
    0xc1c801a182c0e0310f02c01c2c0014880c8402ca5025880801500c900c0900c0c002600713503e0f0070780c800c0d0041200284603080101c04c000040030041040400303108001800741e03000a00d00e80b0308140e14824850181400c0906000c0c1008000c5440c80603500c0070318002452918a080001d52810f20160044e0580520818800115400b49a02410320815400c039004041e00c1150001103401030711075000140c0084d03004116800d2901101c820300c90007610f4240a80c005500c40c18200951508031041c00c204050030b03034014030303000703104910110400c5400f10b003004d00e001c2c10041140310f115001c200e001d0351100324040c0420f058040e00c2c0681608418203029586480c0c041c0002d520118a07180411340852000a080d00c0e5505400d01c00d40700600480111880c20341840051921104006e0950107007040d042e030024007500c0954852010000040010b03441d00c404e000031907210341c0140c070a0b03410000c0f07100965500094040d8010364841c040580d2591182401c81c002e05081e04040b000f40c40050040b0280b200c035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 828801978 1250 828800728 828800737
    0xd0f020408010e0601062c1c021f08010b1e0c0706120603081b07050d030909060501080c2203020d050319180e040f020402040e0702060c041a09010c0c06020102 70
    0x190001c00807840743c49245682c1d88000d10135600003400003c41c81455109079a408903865008841400c01410100002441d80386c00201c100d44603908046020250300e898000d4003d0f160006c41c0b00d22200140c004001c0140c0014080d80f80030074400264004045034031460128404100c01e09103864502c0d1744a0140c503421b480c4a44000200800340303844c0150018440c00f41101c2c1d01c000070a182c07034009108401e240040604001850249a4001410b6121495044020b610a070f50f019809805e044511044800e42d40040d0304100301d010401001000803012140142900f045004010002000c41d00d00a0050b820094126240d52480001c004000010b03103003410b10004011282400e09030308072074021f800c03150441d04000342e80c4200007c0e2205c00c066a0010b00800f241c403c622860f80208041e0380c0b0640c068021691000308210105505000c040d0308200c084441134541b80c03401110b0703061446031100c6d4106c100000034400360140e001e5401c001045034000c40b108a49641c4040280c003d400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 828803228 1250 828801978 828801989
    0x150809030d05280b0619030608010213090f0b030309060c0c06040e01090b0306060f040903022d070b030915070e04090302031305060c03030c0304290613022a030d0f0204 74
    0x8850410b50500403ca025115040002402107400c1c00c0c1e101e83e80102d850030046502d41031595518010428800c20b0000300a081405411221650315151a075070031a07400500b0355030100d241407801503040d60080103d50f142481101c0705078498002c7c9007401d040503c071031081a03020304000380c00580303005181c2646040b1751508204000d41d098060905803108011220164440020000e081040c901640503201090180c41280c1003c0d60313a5128000c40d4560040c20450364220301c604003050741041100700e000d84030840007281036040103001182d4a0714403003500c0b070501d00d90358000349080f0310680301c250100200800a0140d4801820041d450f81d00207070007118102401d18002c1484d007001000c559031081202d0085280d541e0700d440d04041b036007014100311618800c5048039444030a010300e00b180505418010002141441d20411082001c44c010341851540144004c0081c3c2c4207009009420000d4001c804803a080c6544220742944a054001d2a01500d461544014031035203034050410b888 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 828804478 1250 828803228 828803281
    0x3190804030e0d050c06031b03041b0f03030c110d15050a240b130302030f060f0709031a040302010b03030d0b030f070308180d02041b090b04150809030d05 68
    0x2d0158240b10f180e404144000c0c01c203600140501030303c0e082c0300300115801070102068a40d000490300c0c150019500c180d9059075840501d2105013003800000288000034200c5c00c810000c0140b0355036010b005610304d41c5000d0010300030b000340040c29451703014000001951210480c120b409c3c2e01c0020304014001a54059015440c06c05c140c00c031100e403450090079402041e81e00c11926071515a501001e90b002e000c407422200203a040000068504110b034401400c80040034041c1440c11501d92940d488000b8511020412101001c00200301d10418004402c640c00440b169255102e044c00da014200c4611044e030144400210843c044540341d002e900c020a0407800e0f04c07148001c1380b803000e5a5000c41d00010f40f5411003003203034800c144203640030400301040180079041c1c10201a000102107035080c1612100c8801c0c030100c47e00c481c03640b04a00801a02e28545650300702802d000c00544060741030301c0c0034ce041c40819008140c0038070302002941c1415000010503c82481c14040b4860700300380450b84070078400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 828805728 1250 828804478 828804497
    0x3030804050c04111b190308010905060913030309050c15090f030d08220b01030804090e0a030e06090607020d0507080d05040303020606010c1a01090c0e011806050c0319080403 77
    0xa250a00502c1401e103010100740b0f0034601045e2101c0010100e1601c50019031080b6500c6010b028205013032040214040d441d04407482d0301d40780a03401503030070003070a184c0700350f00150400c1030080007080115080c980518000034400e0503407400d1450050301034902503105180e80a444180e11211005220f01c000580301c1c0085014250103160740c8501550503240851407080010310b0000d60f220341207034070041e80072851030246e545884480c1070300000c0c1c00c261a206030015041c44506001c0c0030700c0031103003901001440412440d840080801501c941058420300e07000928042541e940000d0b00c48850b00100783d9903480c01140352103591a901c0e841040018090403500006c032a0044d010b98040340c0c1c064000e41050340c1c69100458401200d507200721b601f00984051a8288800c0748000c50280ca003980c00002e110002d064054848001c0d8448903040005074644000001204240007080304c8183c205603032100c00d50050300b0308601034002000c01507021010502c0c1e42d0b035404280079020302cac0680c0713a00300072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 828806978 1250 828805728 828805753
    0xe15030715020115030812100b030903070b060303031303030c0e041b090b03101412300408030915160f0b0a0b06090d05070536091002160c0303080405 66
    0x10300079510024103013040c10f02c044620307d40340030015680080020f030b80000f52030701c40e104281150401e8440318200e03400442d080007041801c60500fa00840110300860031407030321807002403a40350a40e000504154071400d001c1d82c2d4a01a2801800c45c1c24010030500100a110501d00f001c014094409800500c895a0008029220030100d9000d40390300403600309200e04144218404541e99a1f055402450100001135030302c1d0103000203d460b1511089074015045625804400c0844040c0580500d404c100000c2190500001c2110840481540e41003043d103202d5160708007500800309800c80b048110401c80042100646440c2c0300c0e43c2c805c0c00692030b00d803600c6e070a00b8115842e0001982d00710404101460892811008044007144244100c840203925407020501d101c0d1181e01c0700320102101000544002d000300c031503440c40a441040c5942e24540300d0005a80c910030303981001d0605900148680c5240c4100000182182e0084044032801d60f591400503d00700041f10b0682e82409044140b045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 828808228 1250 828806978 828807011
    0x7060f020a1b1a0a021c0b01050901200607020d0207060c150b0a03020604060e090a050f0c0a030f11030613050f0106050d09050d0216080a0305040e150307150201 71
    0x944100d240da400041c10b103140720000021401c040c040d60024001c114489248a1901009100381e034403210146c1c41c1c010402c4103c0f00b005088440440301030601c8402d02c00e59901009841c0500024a00a10007032980030750103060a0309191007180d00e019110070480e482d40c00091101000803240e0844801950700c480407107400c1c0700c2c10303001030002d10b4580584140700580d070810140c51100074803e9060030f580c0d90000b001a4801e50129021600400c0e9841c3d41c2d19140001c99031040c5050014489460518480301c200c10004241102d40c0001041300c007031603842503100c1108000e407900c080022080411010344190000c03185988201c25003000d10140f9011805681d00074880100401040e07400c00300182c1300d43d0400640c055070b503039503151180301094040018042004071600a003980300b494400c0c0d0071500b155608401c03015400f58030340d807001030f510000b21001c6400c041c4c2885080d4070f600b042e448032014141c200e01d40c0340c031410030003150400d80040303000c610714042d800801c440310074103248a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 828809478 1250 828808228 828808237
    0x309021806060703030c031d070906170d031e1505090a091502030601020c0d0f0201110d0806012f060604051f03020402090402090303070303020408060a020403081611030d02010207060f02 82
    0x70b030442c205101042c0068026040f0005032052428007246040f4032014160209500b082c40380c40d20703401440c0800070b8030700c0c510544000d000da131655180740c07010208805039240d8525a81c03104055490741120140303503848082030480c54980c00d051040584480c0b299100404030702413980326101c8440800c84145e00d070700c034050503a68480074000710001405104402034000401e0981540210320484503503550312441c80c8012071091010706180b00c00c90000525040c03420414042503070102d42c1031f020b9950020031640c4d10040c246000148004050142403807008030b03e28115101007a050a540300c4400452410b106500585d820000c0343d5a21060054148101803242040d6501e882c041c000340c10560002d152360103010b40b015140042003030200b40303181c3c0240d0741580040c1c0d0104041c0040b2400348035040d00502d00c4d140139810b060035a00c5a0040b4421400c0529050516040e1a0100b0020350b4909400003c02419243c0840c9080c1c0c1c080d0107944400c030103c818510b0841071180c191010320984 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 828810728 1250 828809478 828809491
    0xf010c1e1a1515041a1803150c0304030e092d01050d020105030408040b03010e0a15030213020c0c060a1214040b180705131b0e0616030c02030303040303090218 70
    0x4407403070342d100c400d00904010703040200c00f1000c010403000ca8404540f05803910485840d40300c850baa0070030000d4010103103200daa06140b081c0c1184140c420000d10031800300382c009400d8421550389444500d401c0d42c049a65020881d040b510150810082c03440318003000301c000000003103e0307a8480703004240006560342402040d034058078200940340903500c80c1000d1517021348100708251600c0d80318440700703030290030990000c650110090108403842c0e081d07010b003c9041050440042c0418119400203070b501d5a040c103100801640811440a210410408051601c0028140b945c0d580e904c100c004210715041941102c2203801c0150100423000c0d130000d0306100d503400480600b0385444408882e1110b0304a40444181032058000110311a900e003202e2803c81100c0b0300000420040c403400b40020f030035400210200744400000580c855840700d400b26401c100700d0100060341180c40c1d217802e840d050318044001c1d40511021013004101901a030040308024002c941d407240c060001c809488c4020000c40360f9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 828811978 1250 828810728 828810751
    0x906060e1b19050c0a0609020111010213050d1a0702030307320309071d06010809011b0f090807090b0f1e06130312080a15140f010c1e1a 60
    0x26040b00245180e041454050107252a03450443c1512100303140900e0801c00341e440b44e9992900100319a040303a0214401c0d1598002941403800164031401484914420310b07020b20ba041c07040a0400c115115283e030401200c180c100928141902c0c02541c903001290a803011440700602650b0001612104481d042d042442200e05030b402c80e8071810301600081d02006143c4110360005c070720302c60080d00400c44240301841160300ca1506400040400304003034040315260f49008201100c01050a070100151215400c040400b00c8404a00711207a040e10b5121a03460700070518041140720044e00203428201c000c0301e10014489001c0200801c074010b05001d03e4908680801d082ea190502c040540384000c80304035001c0c842c0e652038440c03032644081003581c1400200804200101c024040c0310703205602200e80d264140607401c0c0500243e0140340216000e1040101d0b901607002a0b12422800d180315622080c40c40d58404180a00403074a084c410086840000c40700b041c011155090641c82d1103441c51511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 828813228 1250 828811978 828811987
    0x2070206071106160510051e04320a2307090e010906090f02040e060720070b0a110721081e1801030b06040b03010317070203010906060e1b 61
    0x11495001d9803004502c6400c0030091006800195001d00120ba216018001402840c2d0300395420380c1c101c44005020084620b51071818484034a085005158070640c045418900d8481da0300341d41c4442ea0044101c0e01042101e29503035240481c001c1040071142d84102101000703035100001c001c001c1032140040c0c0003950b1110404000d020740c10b42102c54012204000001c10340043c3e1920b034243d40003c1d034184c60030440e18018404604040c8200c58030a00070001904040c28100c000810300301400c0481001500100000c002e5600141700c034100030881500700c40e6031890419406000c64500790805015070190600c0096580600040d00e00307803086010600a07441400c4e9220707412600602c40c48280c5083d8070b28504138a400d4100100b407803000076100a42901358002c001801d0b21b480d070301c1044c040e04050204100c0d090501d416a415207901c0b108a40c800400c2007101c0e401b5010b0782070302962541c280000700051002d20743c01201550302241040c6010740e50340074907220907207400c0041c641c0d4950810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 828814478 1250 828813228 828813233
    0xb030c030609100504020a030c0e040c08010510050d1b171005040c020c0d0305030a060602030909070f11060103081201153509062d01030f030905040f06180207020607 73
    0x10b645a60100b0b0030000700c41400e440c0e00c00b140c12030308810b2450000c40e070740350900245680c10242e000000178044a041c41014011b5400800c0e0f51818441d413409000e04511079204940103c0c2504d112a9140e5001c009003002805ca000311840050480030110b900310700848e60901403481c840b8400c803e24201c42c00307150310300400d200050a000d041403085009441c4103c840340d039811407402201c0c0c02a503881d07032607050461584007110302650082c820365004010f6402240ca1711020a0f038800750750300f03029040c7c0c80140c0c0180c403003060441c0d03100d01a005d520000710800c4140405044c0120703610725248650ba0302c800d28004c44080075040b001c08903904501800034440b000309414051010501010030780380940315001d03000041541c032900242c120b14100411482404168400f81108484244030703280d813110710800014041c0009032a0700040100700d01818000d00204008200250040205620548a22000300981d00910419948212207001880324034001c0d0351445400400c01458440d180d17 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 828815728 1250 828814478 828814489
    0x10e0411070212031b06131b0801020c07031e031b022e0f030515130b04020f0d0b190b1e1204110f0303040b0d0b04060308070c0e0f0103030302160503030703150b030c0306 75
    0x1230050a070384100203440420200400e0000d00170034640003000f40113660075490f1660f81507001070030b02a01c40048210300c0b800300f603114465003807110b101d090140c460503850001c40c00001c96200e5070340f101c000307091115882c0c0703146100c08000400c0319902d05600c1b103110b0f0003c17030a680007560001408540442c08000078640b0022007043c00840040c009030100707240e80460181e8200c42c912001440c8003195000c0d000704c05001e11441214125000ca408841d54800421403400b24021800b603ca408a00c05080442501c82c603050107952030f18060702d07982c105445c44090317441107404417042d003a0301003620b0302e50070070300c0310040e000000401840c201800e10b001580f2507040b408085440c0d5482e4420782046499910400c009507018014184e0740d010142070001c0042441c1e441502c844d02510208880e0288a502550550341d0500d00903035640140c0c030710034000e500d5140380500719000000a006400760140e01c051481d0094441259400350f55180f54004d6020483d03056541c02400c000051151920 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 828816978 1250 828815728 828815753
    0x609081c0f0c140c04050a141303090504050c0903010f06051c02180f0906010605030c09040b030a02040f02040602010c0309050d0818010507081b0702010e0411070212031b0613 77
    0x8a1400000ba2503041e200e0704400c4030345003040c0c841034000b0b0b0001c103c00d04140c0a0940e0000100c02c051007030000240032003002c050300505000441c15400c907031004141c4500400307070007018010814440c03400e00591440199000002c03040c425842c0404020500312980250801c49038024032100b4420b410b460040b50f803590300d078030482c4c1c8403460300005c1002e2040051103a002d07503076240540596150200c103c07440c021060300040180b2030f0502c00c20039582c511804032a0003ea054034003041011a10010031720706955804000e42c00b074101140748800003125800707001101c840d50b0092001102100b000d5048905005001d4510340020840e001440d00589103a50080e000c0101940d01141c406403050071107800f40e56101c00102181c2c14840507407246010342841400e0110303500d190030650713130001e841d00a40e052400c0c042c549454141001c0c5500800b590100c50300545000e1400e01c0b4540c6c81c40e240e90086041d0303201c240001c00443d2050100007072052080320301d4100041002002c2d214010705038517 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 828818228 1250 828816978 828817007
    0x1a280302150f041502010510080a020d0606180f050a0209131a0603070e010e0906100f1818140105130e010209060d0903080705030c180a030c0e010609081c 68
    0x4204000c0b04440103100080004000e140c0301c14442c0301c081a00213003074030005030841c808030110410a004044012480c2480c0b0340d41100c071684c072061145000405420b190b0700002144404c690388850714000d542000c4000300c03584904001ca90303518402001240500100e0981140302c110040c085080581d010021841d43c2071100c1101441d80d0340050740591040302c804000540301210b00720b840d40c03c207120b9604d00e01c044422034024600180810210011605013004021003003416001c0c040c01501121412525441d0f40d002540e2210600f0020010880c02c0d80d600e40d01d41100b9074091b00007a04d02030b060311030091200001051080d81a005004403028420555500704100511907690f00024203500c4800030b0003003846c08880c103010700382c1c102c020000428007004200700220044e1405c00c50b00d03140100d0380d070004c01101d55000b181408000c4e80008066241c5e41001242d581c03c10075455048032221381d60106095107892845444140024891034108514466408000d000b072041061400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 828819478 1250 828818228 828818269
    0xb0c010c0807140f19090914011d063c040603030203071403090414190e0705120c042a051303030302030601051c0506030f1c080711011a280302 63
    0x10810f0007268051804400c105001c1101290200066201b81c0507185030851320311281440b5624101e04e00040001824242b00c00038a030100007041c03543c40c00c040348040f9548104c3e030200301c4000510000000e8107805240324446424114071280d2509004150540398036502560405416a480140354400380b1020100350009001351905c0d615903106482c074804240d88802211f040c0f0382d422074442d0800c3d1000300b40c0d190500c49441c03c44000011040121101034401c01015101c48082d070b41401d00443d485980503003042c4070889803083c8042c1a2481e41d84140704010000103100007036416214a50304082d5a80d9200c10410110f8060350140d6400101030400500e8011504035006400b05030580490002d03565005220b420709040211404155101004010012000c499400100300c03980c4c1c58000c114501001842a51060031040a620640802880009400c0e02941c950030050040e031400f552201080a500c40407034421220115070b1010b503981c4c500d0541c0c00744580c5a904000c42d48044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 828820728 1250 828819478 828819487
    0x21071a040e070215060102060f0f0a060902030f040308010503060f0106030b040f0e0a0c050a050306190e060103210c120c2402070218040203030f071a010b0c010c0807140f 75
    0x249241c0e2031092064440d030707010300f80007a650750490306420310140c441c80c1154040c10810484061001825800142800c0c4040340b40d980c1e45030f00400f60140350008a1010700210900c0a02d440e20075040c1d0041d4840e48039012035030381710300c02e0691b0780e13130100c03100c41c2c12554000c010816540246d0040007800c0f0060004074220704540200c1c0c0c04d0b90300748955051658481c404240504c514046220302078070303003207502c42d440c83e152200095480d0741c060402074504001c0c46a84a05001d550b12948510510030250b84a5685d64104441c070755010001d42c5183c258022641c01180388983c2e450724260364481804012540400c10488540b815480f044481003000000c0380d1000c1d80030075601c01da003142c00e1000340e41d46043c4e00c140b048801a0070000048207179854240401654044185c9600040036004907803140c49504284014218101d1480703910004c1c400007140400e130110007000d0018400c4003c0c0681c5861080071240000d0840d0002e000a0700f07070300c0e0901041048001440070701c40c01460503003007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 828821978 1250 828820728 828820739
    0x603070b0703022d0c09090742092106050c27030c060a03020d0204141c0302070501180b0a180603020c0307030809150c030621071a04 59
    0x207610080c401d5000d82d0003070214030f49202c03240806680004040032941c0d24080345000e16079851102e40e4402e8443d504540c000b43c0c0414042040800070071800c1f0303000c0240110269003c051038515001c00404507407042e144060755040c54004d40c41100150740d1511300303616105c4110740d00c0790f03002000d95403010207582c203101090150140d180505c0800101a641c0d070001d0b17107489140c0c40c207140b00c04948481002d054100388d030003240700c00030110252080d0b0b54401c20729008070000d219200804000300d10104010840c520b50340100c000525054400e0075541500000840b490095130700e0080c0117034040f0380d05120b2075124002042851003002169840e580c0c5864250340c16802c5180f080000410344000b070b0341c003842403800c2e040082c51241801c618244140842e29164450300d24089d06110000b030204804403000c0151b5050000e034542070010908140d00c003d400d41d030007902c400d4400c8503020805068032160504401c00b0b44203020007428240d1400000e0000c081600034400c050b5101400300107031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 828823228 1250 828821978 828821999
    0x130821180909010b10110d050a140c01050109230115200109110a03050c0d020612070815060a020a1b170304060f1103030a0f0f0606200c01020a060203060307 69
    0x1440c02c28004924000c044003440b4620104c07003112000c12403020f80c4140c80040200d8148500407d43c41c0c180e6075900280350548048454100782182c00b100080c0403c1c8070070040d440075041c0c4940b01c009000c08507512050781524041040850360b02050600104004110000c1c201c00322103090401015180c051002d20303a1150b00e00701e03141540e03515201c406042004c44d161a95079100200c41c21498107040d6110590358421481e040c50140000c01096400c0d90b035100c00791201241c4d00c10300d56086140c01e02005001c82c8054800000f0215002482242441e08005489084150343c1c01441c014026444400000040e10000e622416480780d002c507041d401400c1c0700b400010100011995180b61010040c42d5069801c80ca000300000300021017201c02c4003008403034000c071001c00046800b0140e003865030028203c0c03403842c40c1d05500e071000000304e40360082e00c407a0182806c40350744000d68400c14017990303e44211040290041e042042e0107000186154041d641102e0041c0803201841d40310f010300d90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 828824478 1250 828823228 828823231
    0x213020c0c090105100c060b0f04060b120106052b0e030f300115021c090602010b06030c0412050f0d03090501050702010b010f0309050c09010b1308211809 68
    0xc80380c0c1000c40c0c46003250616030b91040c01020191035240d40c107901c4c0c160092554012400041c41c00d61100b003015640da40b800d8a41c20743c414024400c20107a40d4650300f41c14298401c0c0301380c08084485000001e1514000c41c165280d81d4040e40c68030005c81c0360860800082031700301c3e0040880310f42e82c910301c008800e01040a003c02c141c5a000481d660b00a01c1d800001040400300b00c05401e0040034001c5d0b900150440b1064115001240100030641c0d8002c4d003603050041c0b00065890401c0f80e9a4200c1405030f108030548215091034008000c08006041400401d20080301c001592000400080019590030348a071030006014030180d0340138001c012021400e0030006042840040c1e240d0b40b0310024401c3c20b10030650820a90b000812126036124000303046404101840e03000d0690b40c00000d01071180501c40b910654900030b0240b40d903581c5920080c0c02c1500490205204200382000c017040c45030ac0041c00300192251500740e1014800100d04114041e070110007421280b80c441000c1014035116020fc2c02d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 828825728 1250 828824478 828824497
    0x16020a0f030905011d030307030305040f0506090610091406060a0513032301090b06060a09030204050414060708100504020f070501090c080c04140a05100e07020607030f0209100c021302 81
    0x20a4201c2c83c3c40c00041440b98080b0b00685214107064007004290740000840d240c0715414140401c0c01d03511030401d003250381540c4101070400d000d01c40403c104008082885481045e00900e2280d806442e581c1400449282c0d1080c820003007048000300f1311524040c0041e1002107003070f1030315510b404110030311113110703000641c81102d0303e10707072480624003203920800d60501c528102c100800c403040580d1103000e104003028082c280545030009003242464031484c0c80304040c0d50064030031304c80e500b0b05241004541ca007515828059025400108101d184034034100c6010b2001003200c48100e5003080f0801009521800c15051602e41c00c1001d0000900c003806889000c0d40a4500030031801c1c503203100181070000d8481007610461807c4d03204c0601034000741142e40c00c60810039000649a40303040d4075201d4a12140c02512140c801c2c0350030020515800030f4070a00c940402c0d601030203815010105030040e4002d40003000c0d0700135501141100514811103602c1c8880e40010f1408484400010106049034171008c1c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 828826978 1250 828825728 828825737
    0x90e070305030a0f0e0609030a03200a030512090706142d09010201140709120501090f0f1109010b0706020304031e050705190305071523010503011b0816020a0f03 71
    0x4502d8054001e17402c1d44003510142e034024034040003000040d868040624004080c8481070302004d1070b941c04a9a0601c0440142c42141c4110a0300d050140c0305130070041060070743c580c0d07078000600b00c001d01162590449601c0e0300c0708681c80001d00c0742b0100580045803a1003d4080045101151803047c0d0b0101080041e86200140c0d0b40145400080c20740c2d41c0400001c00d0030031442c0c24004d049900c400034100302c40c5480c076214140b051903d445030141c150a0307001b03040c8407100400384080c080300a8860301c8035886400305a038800406010300038503000034030800e03d014800384005000b0880340d80003076903c540700c0d20301108178608010b058140d041c90005c1080c006100420303031100300034003045549204d2941910b0481000d4403550010072900c10f004000304003117000d1454403010724a603044103846d18490010580404c41654002054400900c90a4401d40c244500090301000c1401ca0842d42050f0783c0c1c448070a40d941a68240450b41200d03811800c6100308406a00480c00c0040c2540791244665079 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 828828228 1250 828826978 828826997
    0x60f1e2d1409070306080d0c020103020c1015080105060913080c06070801080d03060b030103060e030c032206030e2a15120603030c0304062313030507080a0309090e070305030a 77
    0x28403034002c01c010481402e2500c3c02106000203803000a0650200441d4a06165400c109100403000390003404414a80e03441003d00e03240b600c41007600f0141c154126400e507560260b41d00c01005003130b070b00142c4095804c411140003048001442031201c4161a01450303800e403504c030381112f45c00e1a0140407908034000412840c01442090305c01d001c001003180c0103290034020141032600b23109461106100090100340d45400c00440c140c02803041e1a2054107603820f483d190ac3c4d4018000e00d00080583c01c84000c407002c810046103030b03406840303200103200e0040d00400099155130805281c031461300341d040003030309071000030701c1c0c1e5641d18500c2c04095103c3c0783c041e541d00c907009180031910b1054090401c2e0307c683c00a01041d0b007201400025681143d182e458442500003c0c140c03100d240c000c4d401c442014080001482902c070010080006003100e22a600301c4000d280e0341d5421a03100d02d08208000d0005442c070204118460164001c0181600440c00b500c00d00c656076647c1500c0c680c003010290700031919458 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 828829478 1250 828828228 828828269
    0x9040605040b0c0403350a0201020403051903020c0409020a0902070807020a150f050d0b04020d0e16260f0a0b150a060c06022a01060f1e2d 61
    0x3501d98000710b0414005040c2405c55483c65031542c4060024603504e00704002c04001580300f5a038400900804404055881d050388600901030f501600080c0c4071441120751a03880d071440d0500c4001d11030b400d680500001b60800c001c10018024040013640d100042d40000300f01200680f00134800c0b144503140903035440840d48103004e050382c1540c2c400c0006282c12030504111030703000014a81c500c151890043d568194403803101005125101c00c0d03a410030301c081001d00e0340600560004031504040f000700d400b2145d5842001c041000e05002d64505407041840002400b0304065500441c51014000e8600204044002c00d1600c0c0a00d5410344030041e03213100340005045039403078904c6508801d40302c1038070843c02c01d000940740104812004040c0f030360028804240901a03070080394002240d8850740e08201c0b814120318041c140501540b004c03144010f000044010564009a810700100c0000f50182403030024107540c441441ca000c078150040d2204482e040d2500264007801501090200050454051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 828830728 1250 828829478 828829493
    0xa0c06051302012708070e0a0f0e030405122104031b030f120c0f08030a060803030114090c0d02070b0a0e161a0403020a090e06060109030b0f04110904060504 69
    0x50204600708100c051841d02503644101008400d01e000c3d185428640f20f51942d030880069180d0040c445070141c1180400c032018265440d070301410410109002008012540004640846580c1d14841c0c0c410001000306007411078002c4100d0030300700c0642c1c80c00e01108085000010500d4070444030a0000141882082801c121505001400000401a040c10741e600c03a241c403010340001506810341340b49020311584c440d89107075003c180d00044421400000d032800e44d445400c2600e0341d4500c6414440049060f00c00041070313078101d901030708429404880000901c00c2094000e000c58403002d0042006140c003110b00d00040c203045200350280c5081d407900d00d5281044603a004016107443d040002010f80640d040044103007a540c4d08500d046a0203100d07034401206105940c802508041d440c01c3c0002e170f203003840e4040c22590042c0025500c481e5503c000455940350fa6001c01854074200320046005035005200c0503038400c1c4299892000300310010001100b09104407000c80c0e0941e00c601c200810403080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 828831978 1250 828830728 828830731
    0xc07080109031701080d0309080f120a0507020f030d090606082a0f0609040e100e0106090c022407030617060402040b0603060a30051b060a050f0a020705060a0c0605 72
    0x103100600e4802d5061425240e01c0c1c0c1c0c0301d151b44500305600c4d0048030003407000200843e035961140494047d070703400741021442c0081c00200d40803022285001c001840039400400c40d440e483e2944405103143c0b9a10209010007452100340640f02280c0d10180851448020005900c40078011455002081e0003000008003503080300301c0b2140603c0900f417842c001034840c00161462782d5412030f00401c81d0b101c8904034601d07210402c0307401c04042c3d040807884203401c0419030041007034400d1001c00703020005643c001669594081082c101d500d441a000c1440025001d0100a81040c0c1c0c52402040f07041d42d521021100c011110103002e429000b000c00d100c04c6203814400e00a0100b0142c030b15038114501440011000301d418840c01600d107004890105880c8405590b58080951013080880804a54100942d8605040d26980c000b000002e00c449aa031903da0140c03070b45480c0e1070341c50030f15106841c59641c600360004949903013580300c2e14602140580c1c4007405448581c545e95200d030032251050800b102603ca0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 828833228 1250 828831978 828832007
    0x2007080a06110a0e2713061b0e09091510080d090f09020c01020d0f05040c1a030a0b130603030e01021b030c190f080a0201030507020607080402150c0708010903 70
    0x7800c03c18001400c2e005640400410022140009402c11040b001c080c000f280140c02c1c10504108001c000580d040140d0f40d400d428090803040240f00c094030034070380801541c861407001184410b6412807031498841c4003e517000300040c041d201802c508c1e08014260b07041c240d4034107043e243d4141301400355010401c65401d11711010719007034280340c0c0b51020710301e00050385000c1d000714681c0016041d04901c0094044070b0005600c1d403000c01c03c010300f458a01c0014134040c2d41c00c5800f40030090000401c40e000b0f02e5440c0141444a8100e45140c4809803c1d01c0209030010310281c003c41003208100308004d192086030001d601a4451165190403074000a05003811403007041c3d012000c105880000380c0300050b407003030203681c291400720b43c0c0004404200b1503d80030384c0c401268908507050114010a010503540c09142c0b003a00c0520440d00d506400b40d0302c0b0041282c0703040010715000b00180c0980360111111658000100d0158a00800350480c217013400c05c1034011041f2691a468002d003003540c0f2042e400180c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 828834478 1250 828833228 828833261
    0xd091103010c0906121103040f0314070b0c1606140703060f0308270a0605040f060503060904020409030e210f06070801090507020712030201140c0f07032007080a06 72
    0x3002d003100945460000d0207039008100300004401c403190690f50001e400e14200010b81a1a468945031040d140c00a4140440000f44424081205140100306a0780783c00d0740400260030a583d0b00000385007503000001305403e11010070354038001041462040b250312408034000d0044604d403444018007034840d103501510f500f4491010030004181c250043e54100b501e04140e40d040c1e2041c0344c1105c0d0b001c40e0107050050348808401400a40141c200008100b04c405159102540d030f0390354141031300d10b8081211550340060742c5c900050b00628141d44030a80b917501c0790400340b41800c442c0d80498441d421940689804030410ba10042030311408100c0d400010342064001c0803035142028006110620610806c0c041c141c680c1c0c04203002c02d0080c4088405030050145039038a0503498107000b40071380700c1080084134000303052001c180c5150301d4108403020341d40f0340c4030030345e10303108180da022112201100542c9486c040d0b140d556180510b0240b01020007004040c00608404100d41407900803070310b080180446a5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 828835728 1250 828834478 828834491
    0xa0506101b060b0d020a060c11010f1407051002030c040603050108010c02251827020307290c060405060702030c0a0b2a040f0b0c030906070c0b0d09110301 68
    0x2a915001a02030503800b080c04540c85003c04041031040e050f8403002940000002c802146440e440880e0601982c01900a04014052100103480b5501d44e200c0b04000517640e00c490f000c011840000601a003841441200c40c95044007a202c01240c1080e102c0922694000404100c820f500d40110341c05000d00000030480c11465a4010b960381030400c1d440e82401c0b0401c0c1d5001c40070050f6001440062141003514000814038171500e2000f04028804510310700842400e02008540c1c00105550255016004013912410320102c411031050454840700640710360358820850036114406071101d10141c0000384003a0500c0e2900904101d8003c1490f030440d401802400c581020020700940025000210321200b502d4410760608a00c0e80d12a0010740c3d220512100303400f40d01450000c000f1620304104c0c0c140019100c0e07504560500c1903103000030b0a80e2061000c00c8543c1751180c0180719083c07240060b0444640d03685d600315619004a080507124980d1500c0300f90500811003c4101d0004c0210004c2000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 828836978 1250 828835728 828835757
    0x7330e0105010b120702030706050c0904180b0f06031906020a1b0804050603070c05010c1d04090c0506090301090c0b1c020c100b040b030726010204061e0e090a050610 73
    0x140130b0b100b4044c884910860100708007500038030849409a0300503c00307000710328018402c41c0c81c0354002c42c0c45600a901c2c0054441e09030300389895100000381d100602c03446540701c91030281722055006d40556814011003100240c0042504030800d160352080501586558500c4070250040b549100d503920391021214100b0300185c1c0501c11902900d008641694481c0c56020341110001c0c0800d6005140303600e401e01966030150050300711800b664503a000e160701d0080e5241800240c07204e00c88010100707092540d05024516200015140020f00907000080480164035009900d103002c0d4040003075080d0000340b203801c1c541004c4460070300301250007042d4980031341120300c641e844540ca5540c04220f55074405c0340d81d00ea642e50f0442001004010100c402954613000011309020700c412092030b10301c100b0041e61001c15018003d0354111541c98440000782c07440080700104000c0003095031130400c10780c20310300c80070b56440c0f100c054010b2000d448001075910f071200c10310218400e40d0300b501041c480c0032040e41e0407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 828838228 1250 828836978 828836999
    0x9060f040f081c09081e0a200307020a0312081608040b0604060503060a0c170403141e0a0c020319050705010507020310060801140109091707330e010501 67
    0x71082c0d002d002079039203103c10307a030f04000c18960340b020508507400c018081d0140620200a80221401d007031594002140c3c4421803140c500c17a1400706004242610904006500c401c0c080b050303080480710599280c038959900140c82640c55801c11180e83c2d0701c3c0854214000c0d800507030035501500c603841044800242c1e0030050008007005000406507403060002803001e03160340c1c024100a00340036080707440d1424551395400c090900030407060001600c180300c00380b07000d1030214000d000b20b4058a038240c0061001c00c1ca414258010008400c048a42c1203032032021108910040ca81a8960f98603260b821a00b84101820300c14040700380080300301800d02e201c01151011800714101ca400b420155500c0c62540f0100f42446400c7c103590520030302e886400102124103401005c130384072540701c6007080c50381c8640f2000308680b9140700181041c1c0c00400052550a1000d00400809016201110f18505041d0030003404600364104040c00700c40b008501c20200c0c6450242e5000c5115a400134480c3d903061084600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 828839478 1250 828838228 828838253
    0x1111f060e0718090b0f19082112150d06020307030c080c12040320070f080a2a030c030b0604050f0408070b07030209120a030f050412080f0705030d1b05030702031621030509060f04 79
    0x1a61120000030074400c0340300c4080d00b8202f071400703403110b0803440050600c04003c0d04112541c2c4040f038140941d56060f41d2185e5095880340d010726040078201030700c0c440c4051010344002d00850500c400c078040c01c2d48841c424903140001e241200e0050100794104180e00c03441040d00d40c405a0703113902c03c0090600080a48400301603400084040e00d03c02a13040c04840c1c003045042c2c0c0094841c44d076489010051203401810644515010349040c003254551107000050004102c40280040c2c8080c410100052b40d013158154221803203140244c208aa80b000203281140d00d6111884c16600c5400d041c1e04168002d20808840885810000d00b89407070709103200e5004e840e00c1030080100600203040e04064407014280ca0b511500301d0201c0c1d07109c002c0710300018020b00c00c08a81070540c128880e4503084040c89181141c0c40b034802c5c0e40c0a14180013105a40c506610100c0c2c1c402c445e0030710700b003d8081d0080807100001c41c11661598001c149820461056800c000020300340600700310f144810440864003100801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 828840728 1250 828839478 828839497
    0x2011b150b1f030203100b04060804032f03190305092107080c030705100209180612191b0e0601111f060e0718090b0f190821 55
    0x100d1021030034070000c2d1000100d141d040c00700d150501c0791601c0daa54590b025601c60ba42041c1e2000075a9150102c18150b4052849042c00142410700020000b1307100b00d94400500c040b2000042c600d1300f100d0b421501d610350240d25070820358004144007480c19020300a02c03402c600c031400c041086040c18040980c9030784c1211b180d40c141207946074442851428000072071706042e0b000b0200c035444600030842c403501d84d4004001a00d251043c5001200b407003581d0720803641c0d55040206030640030415a5005a5010802000203601c805512044503150400b0301011050006601c01d00300381480c14a08038040d1954a00240310350380c580c280c00c1c40003030301c1a181a5040102400c0c103520b43e5880000715494110359250a80680d00c1c140044210091181c01143c1502d800c0700c9030090a40da10142180d441d28400f000ea1800201c1000400003604c0e40d0b441405610005000b07400100c00560100e5044806808000d2288403502e900308080d0505202840c090300445a80d40d180c070390070742100d081a00401d8043e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 828841978 1250 828840728 828840731
    0x6050a020118020f040b0609030d02071e0e070e030a120e0a080118031416030c1406060310020c070801060b03010e0106020607020c0f1c0c0905181002030402030c06040e0402011b15 79
    0x1041480e41c0d64071f05a0f48480c400804552208c081ca9100a442d203080744030307004440c0030804111400c2680840281d0a4505506840381d1075603d140c41111800b48030b00364103816018624039080400c6008080b07000401c0503440e150b00410042c410b00c40d800c07040d44e0200b00786914100800e0742c86901c80ca10f42010942528040c188900c90b0040c10075a84503000c6000d1251010988450415030440400001d890040400e040c1c2d01c0c01c1c12468540b600030403220300358180c01034407000415440c0c99019281c0943c0d9401210040340d1074052640c01c64145400c013412120002c0010080d180040e20081d014040c0c1e88042c08241c14034140213542c41030100c449900c20b20346c0c0b0710071150036124a02c124482c8044040c00c40950070440c01c000c40031a550303000303210300c40341004002078044003c86403040f085000d0310300810a604c1da2100c000300030b40000e0000c0ba8140280f24101d072480c1d642d08042c00c05000d11500d190480c0c03c2a2002400c20290740300c022a0351104400d442020520b651008101148035010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 828843228 1250 828841978 828841991
    0x7020d03050c060a060509070c112416050f0309090a05190f0903021e03040b130b041e050a121407081204031a0f16020703060606050a020118020f04 65
    0x14107403000c1c0225050440b0520400041103002565030f007021007291400d941d40d40302c584450404030392208403041c000d403e1f100c1251480e12241480b13006c0040820020081d5006c09401c1c06402c1600e42c03080c2c01007080c0c01860040d020522406011443e442c0003808001d40c1f030105c541021680c0083c00608000c5102c1e03480001072000da5a034a1481030601d20108100960342074000c0d0403000780b410210030750040c0b04100700740120140900703600b095456001c2c01907090605d0211300402d2684170584882c031701c1009010000c1c1030320b500d10240019060104401c0300e034000c1d81c08000149031f1a03070b20062042606a00c10440300c4555542400c81542107002d01403080f11042c0028a04030303c91303100c1a020300c201580d12009050210107401600d2191110044030200e40d03011616144c800d5a082c03002c1000a800704203950f00c80241c840f955280d90064601c984da480d180c25040f01c54503072095011841c0002d440500543c20b225a18125010034801501001d198006c00d0450504d0044903000d01d90310b05 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 828844478 1250 828843228 828843233
    0x1d0106050307050c100929011a071209080f03040e0406230a0b0f04020414010831120c0c091e06170d0c0503030f06010e101e09080307020d 61
    0x40c100d45016902c0030032100d00c02d03001120300e0000c0c00403c0c1b041e1859201c40d01d80c00c0400d111032007031500e13880869002c02d100364244004c0f00d0311000c281c0300c0000550b400b0400c84002880b24015200e1690442c1c42c4e254450b8909040c01c0d08040220345000181d80042006111034200340c0045900240c0059001507102d55101c03044e03c42c20700780400065005a490108200c040954110141c40c00c42512035000705103086040c40142d00942c002c403180317200c40d925036080d81d5120f40c100d25409800800709142082c0300c140910389075201042d0000c13036031002651040a00c8203d40c0c2c0c50794401294a422100c40766203031684101500d0b40d000f5034101640750145814031040c12218011516505802000069910f000401d02c046210b42d01d031010b40540140c81c0c02c00c81c001c90607000815041302c05549155a480c44c0c9800d2075400603c0c15041c400308544031030340b584441ea0001914502303a2200c03c030543c80044000310800840b443d00c0c2c10042c4486041c13281450100a0b1139010ba4161000748205c2540e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 828845728 1250 828844478 828844487
    0x2040f15031211032d0f1303030908030708030411030c1e01170f280e01090204110909010312050f0706050a061502120f0702041103070807141b0c12010c02071d0106050307 75
    0x80306c4401c05190040b640e10160100f03108001c040f03a1080c0c851050003641d0b1144c040c0c4a004810000d44000c00034400100404c01c1c01140440c0d111001342a50468050400000e40e0b1054000491070302c40c400c2c0302c03074904ca5604400140d032050500b0114085034508404102001c080007801425101103c4d03895410401800810703508540c1066402c0c801d142d0041e2030140240324004040c0c0c0304a00f00106000a0b8640604a50f00d039040600700b150301d41c0c21910b41501e02e400000804082040400003030000003c3c0c070f006030803060303c104808500750a03ca080d220542c0d0003500031040c480e0440e41a01e082d40e4001415000027800c100c0800c1c0c0f1a0081c20080c0d0311401103c8000c0c0d006030500c90303000d9a004482000318400c818540314041103450f0250115031540c00c420302c1480c1700d903003044502d5409002d0640340c440c203546041120914040e000114100440842100c0c0b1540c0d11092000c2186070103005400c0a4900490282841109005903404200d018422001031050002c0421040c5128 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 828846978 1250 828845728 828845737
    0x7060c05030f06092503141e34020c03010c1e08060306071805060703050310080105010617132f010309020901060f0903060e1b03150402040f15031211032d 68
    0x7c003049108a2600708008010181da24003040030000951000039091100d08484c40d2203400d0038100240c51089101042c106881204250410b6105028001e41183d07000d0148842d250140e5440000e00d026184001050203c0070384180f040c020700404012158400050142c1d120240b0b282a030405c1c83d0704130074841e848625410140e00314900041d26405d154104000b14011042017000c1003a80c5d648031941800c03600c0a00a01e00050f542d1034607086280000f03104940c0001000555000600c525664066903800741300d10544140c0d2400710704818102c04d0a622103401e20207003818860030b10107030700045118105005a00500110003c40f040312841007025001441d03000c0801c02440880b021020b40c1c0b080d100203c6180701501200b9007040d4240030640547c4a0203038041064140c07220381c00c1201610818118502e00c90361101151034179460456104001c50180c2140c44500d0000e1400504981119220320720903072040280c802c0c2c1810054180c8000880100324584d5240800051380c0c06104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 828848228 1250 828846978 828847001
    0xf040e030f090306090f0a1205220501091e0e15060d06030605010b1603110f010c080109050622110d0e010e0d0f02071a07060c05030f06092503 63
    0x3000c54210101910080100310140040301203c0c4950740c0c5044441d692200e00301e0440d02c80d00400d21200c00030b440070082c5c00310000070342010340c1007040240202c401a400040c8581c001105030204100f9940c02c020030b0006070080b0910a00e04402c56008817495044912034140c0d00010880000d050400440e81e805840304020115076450140c0070b181c402800d060300090300c2c2c0c03a00d400000945031030300d0801c5840030000031680c0410808562415120303840303d00100c803554061003200c1c0140c1c90302031040311001e0486844198281d4100302180003110402002c080c001c0220707094170015440e100d107010182d444090404600140030328450441030084042080d00c040c00c000841c0743d10501900050108416a4102e0302171881c1034404440382210f941c00c1c4801768001c0c501c24041c506e8481503c0007810759003d100307803400316070350703540c40071608406103000002e5004401e0180c03030740040d0883c07a00504100e0780d840980c2860384050308401d80d003035400010ba907150010b4030149030003504010390000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 828849478 1250 828848228 828848233
    0x1407020d06090b0406050c030f07050706140907030b09062505071a06011227030e0901030809090a0c170612060f060102010e030304110d0c0305010213030c08030c0c0f040e 75
    0x142d00e00b40c00143e41c03c0d1011180e00f403c3c0800140301c05100402e0301e228038401400710340b031610340c040c01391400e80c000c85c3e003914059200c454503a12044200607580c0110790070401004010300c0c0d41065102c4800c00f4048002540049083c0720748108150340e0000e1907402034410802162404005803000e20400500074580044000340e141e85480c103c21052086e4000e881c1c4c0d09100b555419250100c82e8102c02c00e50403407041546204907039220048880030f15100c3d050007151340c200c03200080e0584000f40d10807110a02c00188444060a00e5120745070800b500c1c40091200c500c9041000d80601580740c040407865281800140c0fa5580d035100d006504c100300c00550b0003a00f400410348160610494515015600304185000809400003c43e0310070381e00800d0100c00100c0500030001004030001040c0d540e07440200011000c64801c1c4020020850490041d6100c949145480c4070404005c1c0d00213000364006001c4030190034000302c4c0348004040c04642d41d00300b80d800000040c006101d005030b04040d91 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 828850728 1250 828849478 828849491
    0x40b0f090412050c0f07061b0b0c030c07050f101119030b0d06090b07030518030f070615061e030608030315060f12060f0d02010207060c03030b040c080f0a0c1407020d06 74
    0x100801b207203c9040c3d0f11290ba600701c040f0196580580041201c98004091011800015040d11000f40285401120780c070102e502d800c8a036101e080c0340022a002108031a0403014685c0c01c0000c01c2d101394240442c26200c0c1505000b11111108038902c9000083c40c00c0c9034559401c101e140ea0b071807425106c6682d018108100b609410b05028505407812501c0c1e00100c0d24080c04a064580480c2c40c1c90788401c4608010b41c40d02039000e2201403960800c403012a00a0345900300010240242044640038105680d00c0e0545c5509481140403c181c403910030009040c0303849010300121201200720707030f40024400d50b02100c1e4242c110108a141c45400c1a0035418100411540a400c840c0c0070391324010341080b12010081580c4104101269601800090140e8401d900400809e401218071521082c000d003030009040c4e1058010401340c1c0c0c02800081c0000d1b240c50108002a0f1803a102030341c10842110b000c000080d000c6101514281c4545042e80c00d242d40403550204640e1480c41000c90140d0011081c03041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 828851978 1250 828850728 828850753
    0xa09021308030903030913060b07050d2703060504050f160609050418260a030b18150f0a030c082103130b0c0d1a040b0f090412050c 58
    0x9400564108984110403140010001d00c008107994040310001c020b90310b42682901000765080044000c140e80c03d48a882c000703600354114000d4601c00d40510007034045541500c070300030046525001406c51160300d152044202219404014050b00d91040c400550b5481c0c50030300c1880c1c10400040c0d21441e1151146032210303440202c592004845075034441125142c2c0b82c408000c107403042e1011400d10307808280b48400201c1d9420100f40743e030b07050f0300c000c142e1031040383e4200300b0895011008210100c0c3d1250800c54440c1000e8070459000c0b4100340410259041600e00d16042c0d071070081d110b500c41d000200d02c04120395564010350300216031103007040708241d030340381a5035490ba0480e10381c4180c5500340c11010010303a0003410440b48500c0c3c0740140081c1005903a520700000c243c0c050b18600d1f01c040c091001c0e54403200c0307a1003011b50090b10490f420260341001001c00c019a00107403100b80c0606c410300c40c04030440c0c850003034254000b9071141800e001050302d20000c540702d02030a501c0b0b103c90321684200e09039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 828853228 1250 828851978 828851981
    0x403050f0d2c010c0c0209040602220f050a06030209090105010e0102120c07150f0503013003020a0c05030705130b0105190c0506070302190c1b1d011d0a050603010b0a09 74
    0x414000c5000a1011840b44c0c081501d40c1190703602d010390000f00c05c50024001aa0300e5001300120242000d03240d8140c0000900031054548a400c040c1c1503020b8440180002e1030064244001003032146002d43ca00310903c404108442010301c81e0905206583c00004103981c003d1145024210303041c0d510503207401549502554500d00780c8100d8a85003050140070340200d03c04c95800900700c6468039168956440d10f078245c4245003ca02d10750b41240304204d503804000d0002c00041c0441c60180d030060000f0143d0342811840d029550340868825032018800f0001c07501c032405003400c4840a101c002030013240c0e01c0010b0341c581c811402c12125444040000000c400e400a080d200c0040c012400c0b60f00796523b0700c400340d08921591a51350f0161001d0340302030424030310403140c81044600c034000d43c031035011200000004021407a0052041001500740c3c5d0705251340c42d850158014440140001143c10b00000c45d40030780718019104c400801e488100044c1d1688007500441c00901c805000852039607642c3c5030540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 828854478 1250 828853228 828853301
    0xd080702130f0e210c1c12020d0506010e220f090b04050319030603031e030e030c0102091305040c030b0901060305100f23010b48060403050f0d 63
    0x604200021807141d1140101800d6030000000940100700c61b200011600100301e4800081104000340f6941c080107404031800608214401d07000046480d041c20400908100c0c3c06085135800b0b502c9801141c1c4031074412041100754808104400030761544008102001b03420b030048050310a84024040c4420010000010840e030503000e101307000034240450341281580c080e0b100c0a40001d01d0f103000ca000d594070840003091303001c80a00b000248442d10f10394480c15500300003d01d00c0a654007256054141c00c000d54100340304c011100c01041540f42540e95074400003070a00014022080110001f40502c1d0309500c6003001e19005000c580c41d840384000c2507030180100351481d20b034880c24641c1c3c401c04100000d013079102185290400c281c19a00b0b1110341c1055030000c0707200b44c4e044400f001d4041003807090205040881d000d0b841c80c5103541806c4c1d08400b0000d40c40d80349800b1066000c0300800000c40d5001c01a40c4c0c00c0003000a14558a800d220b0500020f4442c88501c1d80201100150808001850034140e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 828855728 1250 828854478 828854503
    0x1080115020c10081009050405033a0c110a1203020703140708090f09070c1e0212030912070b07030e1f0e040c170604050601111009060b0d080702130f0e 67
    0x2c2030311507118015002a107c06440050080c0e0060002e00c8250200a13000020425079840904407180442445c4103510310840d010034441d0b50703d10080c40b809034441e01ca0040c0329064401448540c51076602c010b035030300d03140351110300300365002c02c03001c04051142a4038104c0001102c20079844481d1410000e500f9840760700c07000d100704002c801c081c1141c100703886041d00c60000c07070f1189041c5800645422806400702c1c00c181d0703400c2c20149aa42d0040c3d45044417014100c00c05001151500719003401d003c2c44600c11040c0c0032090780219010030102101c0d40444a50a80c5032611a42540001010820304504a1045107a0005e0040c4000310260b0226010f081c600c0126010b06c200302004038107940c2122907008a01c80302c030742c3d00c0010f215030820360010394108030180340c174486900010304950308201c078800503061001c0d02d503403820003400742600402041c0c4200b115100110f404a07519140e0a10030304000a00411910116001e800d4081c0d00c2640780780d8520700309004c0d45500c440328607292075008507c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 828856978 1250 828855728 828855751
    0xf01080706030c050a14090307030809030d030e25030b0c0a0e011b0201050708090303030123100c061a03010c0e131401030b0405010b060f071a0601080115020c1008 72
    0x14260b01c02c1c00b071084540080d44900d460081c1c0c4180440707141400030340d4020300c80d01c100010000c40d14100100f02c01275005003003c1d40c581c04602c0815080c1805181c4000405062142c090300140010410601400d4080343c1c25031130380c15122200140350465030010307016643c20300401101c201c01c0e400410b0507140315610706080040e01c00054032000e000c452103014886030f00031003200650098005001d160b0146014905040f0000002455544246c0040c030b40d10010302d04e01d03a084030800c141001402800c81e03031400c155060203c01000e404005170f0141c038240e110242546006840c2208000c4064050001d1061280801c3d020b40039055000106004165004450040a000784030340d03110100c8204408201d46d1942d11403c000400260068403117540e110601d2090342d80340c40003440c0004020030820f464511a040203902200ca00c0260340505201400f01705403681d01c40030a0b07055072914410b50b844070f002d0030005c03482c001c060804660490580a11400001d801240e240d02c03660003c0716 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 828858228 1250 828856978 828856993
    0x30e010f03060303080a09060f06080c120c06030406020d020d1104080d020c0901090b01050f041415160305031003080d020c0105010f06141809040f1e0c030f030c0b0f0108 75
    0xc0450032a40c180c4805800254240c1c08616000000c0d00420f413803e0003200c1c0440d842500310f04010440d0341c90340c08520240e00075101c10314241042207001304580c400398085c12400a0f0362011410300d1000900013806e982c1d0010f030819107034034207505903403140850202c1001604404229000d00364801d002c2c018080c841c0d04d000401061000070582180d500140402d4226460a02c48101608250030440d0610001348001841415048042d1008221030001e540300f07000c0840900c440040342c8098691540820052003d0010007031240441039541440d00076074950300c4c0d4409100c041d8954000502c0103200040408110320306401801e001040c0ba03000308803c5e603a0301d9941189140034071840c400300e030900e01559103c811110181000300c5c030796507111403012001030020b24400c408480480e01408000c5150341400041e010206204004a2004000b101c55480d89180783c0403030312000701504a40e44e03241c010103106012120300154450000c82650611201e41e000800c400d01031004a8864941d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 828859478 1250 828858228 828858257
    0x13021b0c03010b042d02070b1003110603130b06060921100b13050a1506020d030e030a0c14010e010e0a1b0302130c02120414130e07150c02030a030e01 66
    0x4141c5003800d805507100b0702145d15000003060203800134803607503001c070354244141000300c0c07603c0c0ca000740b050401c0404a1006801c6103080707008000c808001a015943c28001c10410300042e01000350950b40092501c102660b4003030006000344900d115540e0040480d450015030302c40707511400c2d8a212564815555601240144c060807035405640c079030341c0701582148540b00b499140d030126400094062000c47c41e201e0701510201002c20544c081d600507808810150611649031040454566070b0070051071412860100003041144100c80182140417880f003600c40c100c10960090f10b102ca200c4009104908032400013a4407603d002c50151840d400f40c4441c00104612800d8a00c203480d8003c04180e1000d0500090a0081100344411b8080d48641c80080015808101c0a00010011358103d0350b003101e549020322038070307250314418200040e0900c0311800c0c0600c00403034034505540d1194105e0100801c0b40d6021540c407120110081c1d054060f41405409040d44003042500750542070b00c0300045442a0b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 828860728 1250 828859478 828859481
    0x19020a05061305060a091508181501060f05040e01030803040b1b0f070f0b0c0a0e040501030f0f02210a0b060603040b04060536010605010c0b0613021b0c03010b04 71
    0x10368040385602c0d960b100602003480c001d00079140092040c50505580d07512514084000c1e80015040b80c041401c4000b003288400c0f111020101c3c2880040c0501180344580050203260380d81801400705100b03041110f03140c001e1091050b14001d140d0400b1200480d6500e0138030f0040c1d035105036000e55010001c800000e4120b065a526868840543d050041c42c02d2140300031521290091541120304200c4050320401181420408500403034010140c00d80c1d0744126035000d00b01911512415004034105401040401d008140b00d070700c0c8a40003000d00928964a100045181011035070703002c602c8003801a00500c01380001120f0f5450351141c0000407441c0c41300d200f0050305010468004000089101c00075000450300e030070186e000340c6240e0600c4541c0703101d1085090144810700403030480803081031043e4400d003c2400340301e000789000e0a11031650700381f5480c1d001206400501d018041e41100c910000c080c801603040380c0300180280002600d40440500313103074480d094021581d1003503003042ca51001c1460107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 828861978 1250 828860728 828860737
    0x92b120507030e0915031b0913020a0e0a06180605030c0a121b08010e010b1f02060a0c1b03111e070905191d06070f080708100819020a0506 61
    0x68070b0703c01c40003c40400f08090140004c090030a4805040d00b820300c1520204001d84112a0045114414800c41c0c1c0900041c11402080000881100c04110307002da04c3e2410703420180c511190b40f206807035036080c0c0c20f0310140032183c3c8140c4a506c08000400d0031003650342c0c09501a41c104406540c9030308240d07010403905507014054814040441d415030000180c2d103c0441c85200c4d182c7e84c001e10610f50381e540312170841d40c841044407503994641c00c0003805458010428034552809a003480b0400e005040000d40c0c2e040010281081c0305e550b0301000d840355010706550541824032469081c4600140d15008120070b070300c4402c041d00c4d8800c403d0060f5000c00200b94a43d011080e0344010a0901e1a004222001d42406010605e40800e01508044250050b000b00c5040743c2c51038001906e40c8154510051405030300600700760800480441c000310f440e6001d04842d800842c5450481c12640701d2104078100c1000c20351001800d031182d41e80c580c0743d2403c00c030182820349008032040e900047d510070900696104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 828863228 1250 828861978 828861983
    0x507030f03181d1302010c080426060112031b0f14010506030c1c0303020904090602030403020d0507050d140d0e06100b0405030703061e140a0f02120c092b120507 71
    0x1090400a16503041c4200404084c0e40140b4003004240400d03225505a60b02c1a003103810b100c50782110340c05c0c0340300b450480322502030440c40c02030130b80350300d082c0d060541e00e42c409000078100f0980180084864200d2840d1803182e5802480001202c0e07002d00d0040f207240001c0c08052425400c1400003006446c0118a90f950040d020b04455099160074406881842c2e2001003102855030034050ba040c00d032075a00c9469074413480391000581d40c2c103113030030060700d880d4400d20b05008004040108a002840215411418001504000c0c00b0400c1455075243c09005015288405a1030078580d40115080003410354080d0a9044500e8225616100c17117000d1845640101d680540c044201000090030355404004480c0e00400080420441c810020b401d880040190a24111400c803e10001c00710510403400d800402020461420741280b1900405c004000c1c148004032101040c4105141c9882c0700040154030b20001e650b00401210605080f1004041401e540c01400d0400ca203441502400c115000c403034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 828864478 1250 828863228 828863279
    0x1b040516080601180f03050a030e0d17070204110c0c100509092a0c030904050c04080c0909030919150c150b04060302090a0c0e0a0b07020405040507030f0318 69
    0x341e542d801550003418603100c038071500070740000004080746032405580146114601405110f070b00e5080040c80c106003036110343d2007a41080380c200c000901c07440b02ea0814140703004105444015500000d4000d041c00100030300c142d480015518564440032804140303100c1c003280d9481c0c404482c1101115103010340e02081e600000d0510206452001b040d00c0c48036000b00e00c00b801e0150035083c10740d80110340c001d101040c1c083d42c401b1a00010900e8280a90790f40b00000c00f240600b0203240c140d0965407080389648007030140040711701080300b15106004560011340003920038000c50310a0304841c0e0101c09039100d00319030810040072580003148210050910305801601c6113483c214110080c0d801091210b400c140c1c03080e070310640000142c481c1810544146a03100c80000c06861448018111040a288142c07040070320600a00074010748030182e80e00e868060f500000e042d80c0382c1c5440f52604c1481d8101615020341d11506108156006030f00218055020048a01242d40d41308404648500000d4a22044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 828865728 1250 828864478 828864481
    0x80306030f0c1815190e310c0504150303030b0d02010221090a030c050906150301090c0c0602040e011d011a0f1210050a050105040b090108040f051b04051608 69
    0x385400c03411540c01442a90803542002100c00001e40040548543c0b2417400030300800410860f03511046141e404012109500c910081c00076041040d040058064032040180408190510400d0040c040240c03d0240c410403100c0200075a04d1900c011034482100000d0500785e42e0021400c1c014180045180e040c0c00910b0007505c50940c0411281c8005620955000c09001c1e40c100f0b5a101207100c0000c43c0503010031040e075030409050190001c4018080f07402004040303545c40c00c01c40c185040340c0c111204400001800408086c1c102c404040d0110043d2142c0e001107008034406c240702c1507550480c2c002100c0803140500c01c03000640d18690910801690308105038403542c1103600d8000504410400c14a4a032501003c06c4c54466100400e64400303841582447c0b080c4903600f051001c00c000b624090900c94109071810220820310320034400e03002c0c100a042400304007000242c0443c0c0310000d038014190341c0d108a1400813600003e50803000c4510641c00c2c80045519200741c12900102c111581e40c0b1085103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 828866978 1250 828865728 828865759
    0xe010b0d0213051801051303031d07090b03070b0c0f0d0908210f030405010b03120c070909061107240e1507021c0c210909090618080306030f0c 63
    0x3408002d0400091407420361104c1c022020030703c80c0341c0c8128100803030320744150154100141200e03940c3ca045412000741841c10f0762002c20020310b240845410b08800b01c0c0e007185a901103410525160b1100050300b20101e001018a84081412003103c2202e2040b101020031560080b152001d45100f01c92032500400f41c00090716003103050fa41c10b0140c0314200c40f0310307140038500c00c0341c001d62040f10180c50366555900f901c09180b50138411500c03825480200f85060003250107a16840318042d00c40c10b0308403590b55102008002242d0401100e840307240388090385802050521400c881c054480380d1107040203000407141c400d1102d01c40d10340402440d030010b000031460894071398060380e0301624034000e41c8284000d40d44111014541034807441565070314128081d140340f0b001c600d56400024003180c982d6014151045103503200c810740e0304554201c07102151074102803d02070300070820144010441c0c10b17020215002c0c0803d4000844c00b5003400d42c11070b000150000c18841d202c015800030310b82c0c0300b854203041034035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 828868228 1250 828866978 828866981
    0x50607030c05011805010c09080102030603031206120703050d0906031503020d0615230f1f090b0f07030221090d02030c1c0308090a08030c0c011b030e010b0d0213 71
    0x15500c15000010114007103041c4100104c00c1881c00c4845a4480c1d04030000141d100710488000c01a040083d410b41c2490000a505d0307000300d0031615070b9100014000b82035603486050303030392021402d18180e03001e407034030b07418100d4460360f144001030007003401ca00002503002c0c46880782c4c0b007000548d080d658503003a0850382045018400d511041c3c0d4400e0300c661545102c044010412401094400c44040d542c05040c054443e9520341002a1407145a2520b080700d180e481d070106800756180d618aa110a0110100302034a0141460b00032580044010981000303c0d40340100030694180039800320303003032041d0100243c04850003c5910701d0b802c01090210328054204644000b5881b88011b0580b2103280c00300011414400d16104021500d5010709001c105041c0c0040b07845403c040c4020107880c1a0390f2076141c00708180b0010b084403516200002d85010901004e5200c208002c031f441d100e43c2c41101740070320000e002d00900820503499520b40600c0711001c2c0b4140c086180382c103034040c184e2555000b040a5000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 828869478 1250 828868228 828868247
    0x6060d12020307060606090801141003080f0c0708010515030d020c01030203070c150c1103030c04063e0f0313090c110a03051c1404060b0a15030e06070905060703 71
    0x951005200c614001415030185c80060800e40e614420f20a2400110b1425100c0343e0030410385001d103420900c500b5400022080094941200e01940e440031400300c400794a204203084a4054002c40201107642e0506410482c0515902a0340c0800e00c0d020104044d02c0e9050072481c81c0143e88071500020a550194001d19444055400c1000c9419071a4850025080180703140798549a0340380c0b07210746c910307420a403005c8640241800442c11441c01c140a84003a10850095a00b40b0044800206c041420054060301c40211a51400013651180c5062112828100711003403142c0110600c01e108040004192404030100071548004603280c44c2c80c41d001402038084842c10401d0324000c0d5152400200705040c59a1721030741e9516507411210000c5c1000c6203042e40792080d4241031561740c145200344101d519030803070340000c030000e0f0405050001824440c00caa0000440490080c1200c6491750140e1110b0405804d24050b11010b036100c18045404501c1030241591044060100f840070921442010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 828870728 1250 828869478 828869513
    0x24120406050a270305220e160206040b04080405041d3327031306050301050108070e030708190b011706010b1813020d1407120207030215040c030c0806060d 68
    0x1d520300248042001e404000307041000e1a00760f500c51b42040050070320319050307501180000802001200c1104000d4031288040c0000d027482200c00040b17001d2140000459000301002401044005208c040c070805800010302c1c0f118040c0a01c1c8950a86890300121105107845400614160005110054914000b001c0c0c00c0500d1000c1c000720b03500c0f120708400f207000d0400300001c00039520340034214031405100a864000100f005802c0c0010822a60172020302500000356041c20031225040c4070100381f50031203075449180d00b84580c035009a10700c08c2c0b00d4039582c2418019107150895a032a807001319a8a441040440800e9200130010404c2001c1c100140c44060740d0191540c080c104450300083d030f20400c90314029038090780043d055006031010300c514503040409040e095090f20346410301410301c40306044201091900050030708105442031000d0034449100051100250820781005680100180011502e0910741750b0081030383d04000800622903400105415040c207016500e50440903612081c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 828871978 1250 828870728 828870737
    0x30806121e012301150c03121a030715030f050603120901090305061501171306020904090c0b13050931050a0515070e010e24120406050a2703 62
    0x240e24000c3e0110415505840d0390b031480c42c40650400c181285004038059100041c0101c0b021104c1c00290014105801003895440c002460a20300c04400d844d004880092a4103000d81030010450084400018613031350303030030340d020070000750208240d508440d403d640099156201910385110a07000400419031210180741049005581b5174440b89440e005840401641c42a20040511941d02c40440481d800d5406283e03e02814400700510600c001c07468040d00031a0001100c42c1d4603241c0e50440706006038844880940d86a4800760301e00241c1080d000482010100381000903903241c103141d46801220004150350b92002400b8101c001c160000c1d03d014501c200141503400414800c0c4000070541e802031001d0b080380c84c200c02c2c110340c41c841c009099a0902c44006540e52950764406144011502d0039508440704001d1a50240c6460031003074000d0701055400549001304204e4141c0040c0214492802800380392a10407003581030b220100303022007503100d100b04041807071128066241c0040c0e000f0b051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 828873228 1250 828871978 828871991
    0xc04081b15030a050411060304031b081c05090709140a0905120403061a032107050709050103050a030e0609060906130308130f051c080310081603030806121e01 70
    0x205001c0d682044459800365683d4030108070500c0b031812280c14031400111400381c9585003030b64000d805500140b0703000325544400000303c8100002c9004403004911800c4103ca0101d181000640150000310b40d000424020410001000b60b264040c841130b1401e4a1110b0217240d41d001c030110000c180703880d016640b512480c818207210141420041000d03502036240401c0100303118517a01c03408010295800d0281d800360811051024240302d00300c9a210078003004596449180c14aa446c0030210b170444c481c0d0714581000001005000521526443d10a803940087c0c12185010420f00d409001030345030700054100480d18142c03401400401c14052038283c0d401d0070a031070703448170701694001c61802411005880018400e0750700c3c021140c001070004036000d1103d4800381900c041800d485d911b0044c190540400030980801000e00c41e00080d140403001c950300304058400003418001c0920040c3d02060002c4045892414604010704100c0b00d621b000704034106a1040c00070b443c2020617a21440380d5030300c0c203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 828874478 1250 828873228 828873259
    0x2040e0a051e01150f0905100206010303021005010e07360f050a21031b122d050a09030b16020d0219030311120a140c04081b 55
    0x245014014050a400040d0600d0076070a00c11507044944846412401218010030100c95400340b01140841a4548004001722108040e1140c41e116004941c1c00390310040103580c25640012414100e900035400c030b07600c80c00c10003021411917400f80184600f0b030b01310340300180c11a8003c9079858501c1501e070487c4000e0410490450301111801c54240c080060506000c00c130300201d540108000e4a0101c2d50103c03041d190103180e0499401082044002c1e41d40c00002609050040d908400c0c800005010820310307008518092032501305403202000824188045003468221150092030418006e40985114060101d016038007a08a01078040400801d11030110014100d801014084c1980d844910038070140c05a000e82800e081c0e40d074405c11988680c8031040b040388204485414580c050500040090f03d000d044907952041111000904202e40c0600c9295203c9600c00020b613201400648095210401021f100e445940716030801d17035101d01d00c0c080030b18049840840340710100611341d460540c40340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 828875728 1250 828874478 828874499
    0x4030507053c030706141228020c010606030608061f051509040e0a2004110f09030c01050a120510080a0b0403020d0c021c1506083318010204 62
    0x38020418002c1001001140c14101003280358040c008a081500d0600001800389099001e894004e1510092070b601084850050b050310701a40c0701c02001c4160540c0d82c802113800a0b41c0040c400c07240e02d40c60800001101440b0f80f00c0c00342507603c4800541401d468001552450980c8980e0901040500c160000343c00d503a81c00c0182007100c0d48228150326410040d041000f2100110f24100076034001710203020010b560000100703038050041450410150071000414014000072401e5401c0d20000034203c4c3e00d1200800c007426800108034210713081c3d280000d00447e81809403095443c08140080c100c41e032079070459003007103510010303031050904aa5541e810041c900004000e00b5216806004103010a055040c0202c4200d64041d04040c40898081e50108903501b03020500700321180c5000020104011091143d403002d4100b01500f48042916120000d0700d860034901e0640203602d6030701d06482c145074071668040c04a045910548295540e032010815480520000e500c200d542c00c200105200e40300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 828876978 1250 828875728 828875809
    0x80a0609051005041d0c010f0e0d0b06040b0307080615030c090112030207080d05191206090c2007060c1406091c031506030b0d06021612050403050705 66
    0xe00b2094611245084180030840d40102c4212445002c452820000c0c80800141540001c00030300e0f144041840003c2c04031f8070203e00300001c3e684a440b807408007050006410540c2d0007198201d80401c2514000d004141c2e030b60400b48542c030901d4002c0b01c00200070403808084a0681c00c0042c0c00c2d65090030780740e0005800e14109800c5404980c200c0071003401410750400401015100450082248840d004005070507402450b06001c41440c1c811030300701c0c005104842d200002c48115500780b00950700c5801c980080c00800c3c298600050000c4140e040701100350b501219600011800303002207500342001101c0b2414200c40035a148040003020601c0d1b01d108211701c2d44100790030b0010703003803036040b00c4124041c231074260a121081600300040e0081c00c0e800c1c0103400048480c0c034103000030343e4800ca1000c0b5a85002d048000307881d0398804180c08500c42442c409070308040e440356a24078112a82c011059030319004500016120b640b100e4010f2019040148000c200c1c1606246003210381809500e490307040044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 828878228 1250 828876978 828876991
    0x2060c060a06050a030b0a05270706080705120c0c011d06070306151e0e060d09110415090504030e0409050f060609070518060c060103120806090601050406080a060905 73
    0x900200800d8200742c0c802c51000d07250031a002d024151642d12001025000a4107850400741d03144003150509036140c0c00d4040c015102d5250709500f100796980c1c1500d8100c41d1042c000032036101c41c00a1b02951042c2c04851201c580e085541c1e0003500c480f88036030340540150070454065940d481b81c0102010794001c51344d00f9036080100074020f91804c260000c007a00c0d05070b071001c09060f542c1c002060031a41c21142025000380ca242d8035101054400d0022902200440520350b0005e10004500380034048942005c0c6800b405410321420111074503050204803401c038103203240d982d01d403e030083c808000a504640d4020b4002d18008900c80703010000101150408503040f20a0b03803181d004000c50b01c00a0290643c0480100d03112034480c80c200b00b01400b40c0c031031800b80116a09888846403281d40c0c0300005d6840406034103040398000e40c0c492804402c0003011044040c082502c80340050389614100c201d282c030410341a901c40d81440d151013000e42e11542c000c0d20005610f5150f28021030302e0703c441d100c0c02d0310984 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 828879478 1250 828878228 828878233
    0x20160b010b0706181520030a060e010e0705040303110c090c091e010905040c0c051005090f0d0e010807030e0607051b0c0315040804090e0c131509051302060c 69
    0x240c00385080001c40e81550192404415801483c8000c9041422000781850016602160a03005040c0c1b41c1c06840500001303445510001c4284412030800b03920190584408030031044180e43c0740e013004660120115910000600704200500c002403160440c1a45446520f007242d581c0c180c44000610640400c95401d09140c4000c40d0303600b22450324000f4503c40a4a00383d00003c80020314000070901c0100340101406991240140102e080c03080a0307445405411102390340c10064001092000b07440d095a90554902c6402c250401d000d40c08651460701484e140c44c1c001d041c0c00428019521010001c000b141030694514400d54850700500c1081e2003907985542d195075805080c6216107800682c041d0a5007250f025401030641030311b00003486000021007a21b4468aaa554a000001071149400504203181481c042d010140320004d07400c55510400c0b11149006007816281c2012100450450303480826500400c0003010302542c0800d80044843d8210000358000c2e80100700c44c2da210203402d1145a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 828880728 1250 828879478 828879487
    0x703082a0a06060b13170304121a010614070b100b0c0d14180607020301110c010c0905270615070308010504060815040b0c211920160b010b 61
    0x10552040f0030241c848030002508100c0d5601345800106102e00941c20741c0803940209811082d0f041081da0020842c18410214241e002c0c981504143c550341c8120500246003400072030240c0c0501c1d00342510819000005040081030f4071048010a805481e07103128078a216404210400c0b03c01c01040041c20440042500390700d171400040200020701d0a00205000074090b40604400000c055582d00904845c4161203c0181c00082d00500282081300c9030a203000a00303c1da40d0303606400c2081494819220705500e55655424440c03420400280c0c42c900344111556901c0003107100d10743d0354200c0000f40403104060550044404641d000480541c08101c40740010003080c0303040d020701c0024180007005001c4411514940040c44100900010416a00c01000a0442008005443c081c003072881c007a201c84068806880007001c41a02c1604504080c40859441d0440354010b00e0101e8120300e42c03140014807100c1e212031072904004440d580b16101000c1c418003054258042c03502130f259060705a642c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 828881978 1250 828880728 828880733
    0x60b12070e0402040602031b0111040e1608130320033403090b1e03010603020406080f010e19110c0319020105060d0209040609060c030c030c02010b030703082a0a 71
    0x1c0400303a01015100314010002400034650210540c0c094808148400500c0c0000401c40ca0140c04201542054040d000c900080c0c6503800c1c0c10814090450000c0da4803440540318001c0b2101c03902240c051503a0440c200c02600000c0c49a10314200e44403004480d00c443c030880c00030441c2954402c0403810a00810b20200300d807140ca10aa0340400000082c0001c86c0810030760b0b40181c0100e225208101c420240400c19030000054995003a00c540b44420f146a0781c2d6071100d201400079082802140001001d0700009071070707200321120f154181c88000503c180380d56200100c84c01848030901c1e022081d1a07c0304065030100c09450090305c40600300102550b00c0b00d00086c411484024800d40200440e03050205000c40c41c0c903800c82464003640c041c2c0c1d05a4035996a030804101602c241c400050442c0d1400008400030b6074141c0c005030504105540510800c00032030000c80c280c403038040c1340355403542202e00d04000080d14a402440c81d084000d145600c1c0c0d107034101c110b07840c611503014840d050b5045100c050b001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 828883228 1250 828881978 828881987
    0x804090b0105030f04080319020d06090f09350c0106031a0c0d200d050114220e07081e150708041b080d0c0501050c0306031f060b1207 59
    0x41903001e203046070451a140198440640000e0006018480300001085040301c0141000002c103030110000e641e11088507000000500842c412a26002c1c0b030000c0309400c5d0445801608580d03908007070b00000c2a00b09030b44a803d6180a4010805150b2100480103203044000c8094081410841c000141c014074500740664480029141c41d0202000081082485801c03103094485449101e000000d8000c61703103551084c1c4c2450200084c1e0640e10210700d0408001c041d41060341641d1803924403290840303401c0f09000d844031480201840e02c4040000e401ca01900d40d904c540c041c28554400c035203c6940d01c003001820480d4400341c18030200c800b1138000100c0c3c6d00401940001c0f00484010a41c1450080d0703005101c0017003d003000300340350701c02d858614200900121310340150480c00155100d0050009016000c0d842e070341012a09942800001501610342c181906d1040300060003a000210110038410070f284401040c000407030341c0e00c0c1f00220790074820b40045d01001841c6074030b00005043c409406803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 828884478 1250 828883228 828883241
    0x30f0612020a0806061e0f090a0b0a080d020c060304151806051f0509180708010c0e030a020d080d021306030c02060604060315090c050312090a090612020d0f0f080409 73
    0x45180c0d002005000080d01c44006d102401c00c2218801c080300d407080c5001800814045a1950340326a40320240f111010301a481000d002c0412184801005e0741d40a103030b5111000b80c1828000758010014a41041c1011801540d01601c20340c1261200403230707001d10104a1700200325680b603074a809041c01040180500c9a183c0221030ba044008520103180c1006685100078002e890140c1d40c01c2c4003048000da8800080510000c0c0c4000350b403d01500c65400f54000c01ea1001c03500c0000d04820002d600506001c1a1843c049801030b04460500300582c03103c641c0c542c4411076102801e0350070401c440b541003e100c5004054000c0c0e5a0100d274960600078002d150160251115101e9450301030100300066064603c681c10101c1814085460500d5050602a122640d4015030301030007400c40703001403a11203400420115808030360110a036912442c5040c02c40710300780100101c2203115100b810140c90700003d113040961095005d080000015910f100810b81c6481e0112000074000c2020300190740d0070700450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 828885728 1250 828884478 828884489
    0x30115030b0a2c090c060904020c0a14120403170708040801090f021519030b0f090411100212040302131e0f1109010c02120c03060f221a07030f0612020a 67
    0x46034207048000c4c44d190110b5081040c45103500080d210302a40f41c03078058503540208181505c0d444046400c065511359240d019860780c41c02100b400303182000380700c81614240c0c0c0d040646071180004200c141240c40e8802c06091383c850405001c000b074035030000d02400000501c0b40c1c012412620180c07050001149107070620704808041400032011040c803a82d1203281100c0d40d440d0204095807500c0c0030604441c441c15101e500b0544120800c0140030703112640300010513099a50081011507107008985401d65601c1080d0002800c0004001500d402d904000c0082c0360b007840002c140f072900000310050003491060490050b100e00c0d2030500300b00c5a1150345083c540095100d0320f411b01d44000200301d1001070100034864142030155206d20b60b4100205641c09002408842c42410002c0c00c541d10414201d442d4020701d071000300c2e1900031400580c00324482070380c00b00c1141c1c06168400c0340034005920080111040650f141d100c0c407000d407900d0003040003e042c0000c1840500740280180940d1000a4025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 828886978 1250 828885728 828885809
    0xd05120705042d05010c150b0f040c090302030c04050708041704090203090616050f07080d0e0604080714070b090d051005100801060905011a0703020a0f0b010501021908030115030b0a 80
    0x207000031440c682c180d02000e10107200700023011000790000410f00500c601e1842d400c036140c4020300e05065000030906058a0003142100c6c0012094010882541d8080398402c000032804c10100700000c0c440b28000f006620038030612800c26413920026003c03a04200c6458000360b1241c010310a0781c111180c00c0081800032803a081c1d00d080e40804e030f20b84151151800c01031042e0000140007405000e280d20887c0004154002d8402504080c2081d44540d0008034003a42d80911161355484061400a90b0604440c10201d070942088003010070002000136000d400d56a0f401400600710180f001482494460b000040ca1100d803c0d0603c0340542c2100c400350000c2003c1440c12006000c4050070102da0340408844516182c1d441c8601d1a04a04000c1f404200502045094040d1410840ca088201c1c1c1a940d080e402c0b240340b030381500080101c2000440029081c0035082006104818003c2402410040725040c0405c4407030f03801005c18034001b8903600c10301120203944651180340c0c2200c103004070b0080c4411072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 828888228 1250 828886978 828886997
    0x5011407090e061f05090402040302041b090b03071707020a140601090c0206060d080c1203010f15031b0f030e1213060906020c0913080d06030203010e0d05120705042d0501 75
    0x12080c9020700020350044c18071101242c1c180321651160100e4001d141c0c0940213121001c89051546400e42c078840f070340030100d00a00d001042c003085801c1520700c50754260b40d80501e55a06a00a641c0503c4003401c0c44045002c0d980a500100d2810340d80200000c45107c01480158549413a0104071158000c218085400140c140300d2160fa40010902c2450741001e15107a6540d655110a032800e41c00d00d40000a85e034001c0700000c0d0100706420440c04482e500c0c070f9007040310529010218211181245084600111020f0f050000382c441c0c19003002e031a0341420001019108000c440b441d0035956042c02008138000a0800c101c01418035948004194a04111031103608010019488091100d0118010207001c00020f541050403408030050980048a00c1e982d0450700340c11002500301800203900035800d1003040c0e4410030000600903040b2001d50f840c10f0a0510b488005c030200c81015180204210091001268504050382100d1103003520a01c0f5202c244090758810f64071410a6000d03a050156500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 828889478 1250 828888228 828888259
    0xf071b020109170a12121d100b1201020d02030a14040206030708190516020601060e011205190e03031f05060a0f021e0f01050f010311010c05011407090e06 68
    0x90712000340c03400c1e03c020414241d00848002d20380307001200007401d1001c0d070b8920640d55070b400c00c0b01064910190841032102074115001a5056100c840700c8802541c00f01407031000300300c4a41d000303061b039900c001c1400043c45c0b41c0503011400d9802142da0100700c143d001041c040ba8203024413402c001da54040704003140b24034058000443c180402095642800b01c0a40015050400d625880903006000041040315051001420381c0341d03010b08000718003600c00c50001145041c0558035155060005070366190700070884030a008003801c005401c1c550700b0348403e5a03140c0743c04804e00806c40b0030f030000e0b0010b68a0345040c1201450a070200a5510300290806005001c2d0b034441d00f080342c0c0480e84a0420365541c01051100700c1ca00240c005081207240c0c002214050510004210800171901d00d00c0240207a441c0e844c1d031400d040c40300b80b20040c0811500407400700309501036402031600074060800000c0300f0003207000300714110a084403800000381072030f0302c01c0c040380703034a01403594004a003034480c00004222003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 828890728 1250 828889478 828889487
    0x7020f03190806041503140a050a120305100b0a0f09030c0b030615030603060c0c0c12060a2405011b17030711060405062710052e0317070204050f071b0201 68
    0x40c000600071498031021342e26000010080c080823194004d08660045000c0d08200f200c0030300d00c0183c0000282403201140310a84400140410f69840c0040c0c240f900022450980300c60701820550014407070844000404103501e005440010035040c0318045c0d40c1c0c0703000c00c1084003001c04c00c1a07000b4461014028016580c90000c0d081e603100e840003440702d940d507080200c01c901e001c01011030503600c42d850000d0f0440001c3c000c90140d025400098051009480080c00d416003528480300c60282c14241c15020055507104030440ca03500c207202d4038040d04403801c9440d0280024285400300703039200030000074000e01640c0081c4000a03403942e040038103054140360f50754680341d12002d8440f20310902c4c00380c51803c210821310170040340040c55008440b440c0001525440192208503010068049100d03804c19101e05401c12003220100c004000c8541c141c1036650704a0041c2401000c21451a000e2104100589462154a00843c01c4113900c0c0c0c1c040c509854010460b00016200710324003075041440c000180d810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 828891978 1250 828890728 828890771
    0xe040c0302040f0f0504050a110102012a0302040b07080703020607091811041d06041a032817070b0711030f09040f05041a0708100b0307020f0319080604 67
    0x100c1d80442c0400d0703d20010300260071107030901c001c19480c0c002070204000c0d00107004010030780300d0030480d86c58090050040e800c90311802c00307801c2020402402c0704002121080080c00302d001c40d040050a0680390362406200c0d41001c4000c49120750001580b509040d0100909580488180b900f04c1580e03007404000c5114410b06042450161b48881582c00c261224205540141002410744401e110340140348640103482910741a000d649802043c1b0b9444100207541100b0707000180c0107148d08040a14a4040e001c20220b4503403180341901220800101c2c081072420090103445001511ba50407414031013070f040d0019201c00240140210615580d00700802a610222600b4020710f45440c14080850b02405411081220491402c0100000c0043c413071840d200c0d240f105840000140d80354030059400e20400ea50b4065280d02c031403800c102800c00d5000640c0e001c0ca443c0305958200700c002d03103007034519080391645101320a0341d0800303507403103c0e805040c00354842d8040301c081c026070b80b8039207274100011503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 828893228 1250 828891978 828891983
    0x6210318090f02280212030a0e12030405010509010c02250e2503020f1b0c040911010e031b0d020a1e03020f03060402032503080f0d060e040c03 63
    0xa4010041144040480d00040550907010b10124240c0d402000003544000400160440351640c4080d07480c0c41400040c0c00200c81e50000c1408040000035128541c000401040c10b603500c40c03e10210001060200c1410a030b22003580940340e060a103011401e5450062156030b8aa24280030200d4140e4001101d181110032001c807c5a031101d142c1944104164a800c4001c1011110003441101070710310402da4811500c003443ca1280189038a8210264410b10717000c0706612a040c041000400303041c0042c0340c001c041c2c040c111070b0004480ca000c2000c2ea50090750070384202c518031807410744550700403c01801c0b42404030054642e074595002e0402c1200820000180560410b6800001f15207d0807000d0000e40f20f441c1654410040c0c035440c0b0380d80142c050000302c0c06200e03400e201240a041c00aa000e000d107034010050101c51200c2251094a04113071501014201001100040844c2880e0000c0c91000080f00030340e9912407010700427000740c490320b5008074404414181040086840c225504041d40e9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 828894478 1250 828893228 828893237
    0x2220e0f01080c010f0f02120415110d120b0d0203010e3d050907080703050f0114010810241403060105060a0f030b0102070306181109010501050409051806090a06062103 74
    0x50403042207241423031104804c9000080041e0204030400c80b1a1203800003075035a503c00110201e801c0e009500c5c1e40c03410350190301040e88a014851401e40540200c0b4890306e016000402c031140702d40001e405d503500f240007401e147d04000c88066a000c03007100c819140042c402d40340340c2c00001c00344540241280c40000c101e001039031540800c0d860b60702070101d103000780b8111041342c1d49542c9a040c003e8039418031440c0782500e586841c1c608920014080415030407240d0f980058251403e0507000078014200340c03001400d1703d540c2180f030340001e00740a266140150580d0072840c0d91901011040c9032820b4410303003000e03200f0380c0248030307100d80194842c4a280032803446103004159040840e0050740750100c580c04c0105503c1c20301c480482d0b01c90141103405040da000e40b59405a0807005000d00c807141300f00b805109d0010704200418088020700360001c58100852441b01a800190604070078101a01a80c140c0c8030b64210480c51014412240901d07005400f202d0001140030000d071012450507400000b0040500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 828895728 1250 828894478 828894497
    0x207140402130302060406050a18030c03031d1302040f050906060702120c040c12150806151219121107051302070b0a0522120302220e0f01080c010f 65
    0x180d242c44045004642c044c00854880e600c40102610790307042015a00006503d80d620b560040c012580940c0403284c110b00000c04040c05c40c0c42c21150b00402c1080c03401c0d800c10f0307509004040d4941c03d000305060940300c00010f84072420b05814034499025984594403500b034600078040d196440300205c42e41c0c81d50481d40c082040e68072010860820400004140d4002c1c13800400c4104150814200e2000790401e401c1000b40380e00c01600d01c4014103ca01a80c04e81d58055000644c44814900d080c0340700c14801003600980c00a00842940781c800c1c0703161581ca001400c100e85208004103450510300a050303078141050403c9001c4070703c03540c1e5425885030510034a0071050f00240c41b00300383d049403602d41c2c10103e0320f0f07120301c0d00d482a68082c081c1580c0c00041d4141c0c491002c101c4180a0b040034000302c0d404154103054501d500800c40c0070b5004403112031b011002e010710043c111003004031448018002d04014010601e03001d1440c18a0500503448441640c10030b0b01004040d82c0e00039000400c1c200c4900703041d11003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 828896978 1250 828895728 828895747
    0x3060606090418170405092a03070201060305160807060c0b06090a0b1201090b06060a0806040902060c0d0906120603110904050115060903050105161d040b0d0b0f070207140402 77
    0x114840024041c00b244220b403599880007140000030020b4410a407007801c06031700c23041148a9031040c03840505034940000003032200e00c03600342c5000350f801000a1001154254030703038603118100300c02c15070381094403d02c40b4800c1000c10700078003041c401042c1740d00307100900505d5074030388505d84407000f413880d031060750040f000818202070b543c00088003120140c8070441110381d00100318028018010240c0e07642c190200043c110380303810b03000c8807210002e660b50410192140402d000c042d003400f02040340d00c4032040c080e08401103020810a4450f41a956500040d540380100c083c12821902d5828204a401c040013400456002c00e01c9040442d02502c51300da0395071721414070707a0040c0300348105819903a442c400d0026640303500031128400e13640140001c0125455140444500310407041440707000c0b45114031948090141007545409652001d000883c1400c070f0440083d42003c2d010008441c2866140d090200d0700da0389020700c962101090006082c29400c000c07800e001c0c0a20b00480a11a50b00040e40c2e10a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 828898228 1250 828896978 828897011
    0x30a050a050322050c030c1e0103110c010c02060f06040c0e0d170a020102180301090c060f09082d0703022107050405010b2701050304140f0a030e030c030606060904 72
    0x2d0780c0f40b0390340c056540a880c034a0000d44419800e08518820f10034240101c245107000c02c61015005140010b02c1403500c81032005402401514050b007841c241d040c400550400382c01c0c00f505e510120760394060a02c2c0d140c001030a44c0d903003a0261040c1d000e41d00d4a0310040726a90882103c511400c012101c4212800323252410700c810320749444005041c0071011914080341c46e015009050885040d5580c28104210001414225140e901024003c3d143c2e040b01006240c1c020304031014411414a08001000c0d103503000c0602c0e220802d00616100a07040c0301132490645940110b185000c5550060070384e092440d00000d4103045104424010f0362000070b03611410b060200640f000801c405403090140f0343e51184c050b00381d50820b40d200d801448424095504018407207070500c0d4000416190181141c54a0305c4220036142d545004019601c01ca00c3c2c0170310038801c20008485c00c44e210303a85000c0480000c50525040920b0280264003030390008041c04455690003041c0d42042200351400101d04405190241 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 828899478 1250 828898228 828898261
    0x503030d1e15300f0819082221050c0a050606040605090112080d0b120c041b08010b0a020304030b10030c170c0f030f0706090f08030a050a0503 63
    0x19042032400d50062580010b100b082801c54000004040c440104003048542c006039036001003c0f01200071194000061a116050201900901046050a4010b080686220306107802c0e030000c21211000c01209002612003520f0380d2020300146d00c490b6102c0da4407020940c00c90b05840072001000d4080450061040c010f0702c5007041c50308200c540c61314076402d00c0c5403500000d8440030301460801d0350108950802103030040c102e032164107407101011011b41f2125107581100a1380101907031070b400c010740160760314540310003551410805000d16103504010081107641810301046050300d4202003012031504018054111059010900c0e955005000308078190700c21034000418404040701400300041030000176000b500e2041002403076403034071400e07003480d090044040d452150384400d96100d600e0500c840454001c5202400715110070465982050800c00b072604407100080f007005042010503480310740c8400601c0070901070743ca01400d003c4010024401c0320382d0340b418000008049904072040c55541d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 828900728 1250 828899478 828899531
    0x3120a0b1e01020f030706061809080a03050717010b19080601090b03040c030c0e0916050607021c060c03090203070f051c031101020406050702043611090c070c0803040503030d 77
    0x2282c0e11400b03447c09000502c201d0043c00c1800030140142d11050b0594811908904d404c040d2041c1061415078088024140c02003200041181ca498418140e000912080e17011f807801712117071910381e4907684c1d4a00881c604500b0034401c100d06c070310a0021a98014001e40c003a964220300c4299650b851b41000d02d80418690300050075503419800c0007400700e085509590203400d041d41a100b1050303045041c00490f8000340106980f06000300515030046c07604c52001c0d03000c804c917640b0080700c2c02d14940301c80c41158240c010840100703071075200790021840d05122003009410220340721341410341003802184c8181858540ea900c04200a5941d100b4140500c40b0382d980712242c04000d41d5540e44440c4001c09a4201c400200d01440c1000e0118001544405800a5100b402c5080c071b42c45074007042c0e6000054224220550f02d03101c644c5c44e4450145c480b03580961082031142e203a20381e03d40f9a8588822030f0541030b8000d0f8150380007403100344202e03500403045822071458500c01160207122a000d9400014003c42074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 828901978 1250 828900728 828900733
    0x201111602120a1a090c1909060506120f09160308071406061e0a05040f09020a0510080a09021c0308010303020105220215070206040803120a0b1e01020f 67
    0x2090203885a606800191442039540180c80d40100d50499503507040c030a00280b03011464090b40c5001c8103140000703544503c00c0d800f21541e041181d804179550304480c050001850701d080809000c014014014040200800c5e15500d240450541c3ca01e880d4030030141c551a9006c00c0240411441442080720040b503000c007000c1940200d5032840d0140035948010411616480b4052070140040000700b10244030380301c041e091071003c0c182015507580c6a4400f21805503c0320321502c010905407905d1180c610781c041c107030b031000952501c035004201d15468030740c1c00326210300c0b00744104820581d0f000048a801080c810070100d07114400c1e1000400312a4040400d544540d0341400810504d03a000c045141240e001ea0001c1120780c45080e442007030042c203d1590001c0074040ca6881d001801c1421000401d18030b001a102e0a0081603800070b41c0aa10650008c0c166500104030705155000010aa540190400b01308001200e00e0b403011604800a906111200c59101890340e010742e4001d1080c3d003603041d121404d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 828903228 1250 828901978 828901987
    0x5060d0f023705190c14010f05040611040302031f060e070c12020d0c030809031210090606020a020a0311040b0301020f0714071a3004060f05040b0105060901020111 72
    0x35085070816820a41000c10364194410b00502400f03207048604400c81d541000c4810700c0c20b110280c0d5510311031002142c00c840c0480c001032800e4401c0c0329441c50019800c4003c030340c0b070500d4100350050303075a8400c0108010340300f00010070060f40c0000712404400c071581e55090350041201d004030010708580d88224103d103882c0b4100450701d0392203588500d020344141d04101d00304000c03400407a134030511205200302240888800002103401409860b82c0705042004807403409c03110b5541d450f02a0000c0d00d55445600100c58180300103e014050300010700074600c01045d603203d03d40c000404150803440094110900ba80020a65403282d0700b0600148502a0080d1340c2c0314045c230755850007640800e1054402807009605107851410206500d41144c81841c2d211201c1500e1000c10306040d8407640107038004400e18a21002084c0d0703a18501c08040616500402051506c0d0038a6000c0c0c4038031144d161070780c0b45031404220015a41600203815110140d8000340c540b0754070001030f8010480b0101030810b6040104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 828904478 1250 828903228 828903277
    0x315011206020405090112140a08040b0f0d0615020d021501052b0309080106090902030c0f011e0315080c0a0e1e15010e01110a0f03090504023105060d0f02 68
    0xc1144001c1c45a59101c2e230300c0e500300b0034080e00d44030382e100010561001000704011241d4203001811141d500b102c1811302d03007181817503682e08660640c2d0255041da000c00c401100c0341901032101036401005800034100d003030760f8880482c3da05001401941e03c90704204222010111070f1400c0c10740b0225515040c411485000d0030042c0030a566031250300d00940c00c0a001040680150081141d4560302400034405d100200c8200500110000072450401196507408803086040f0a4202c0b041d041540340042e4184086810b104c0d07041e02900041c0a075484440900ea1350b454001c01e000807180080207466141d107860140f014140d006088420240c6c9244d81801007001414640050180e0240c0361042c840498400640300c1206945c0466402d8100480c3c81c40440c084003440c02c96070788031346848003446403113100160490b086a81516039000c3c00e100d140c6005c841e2a80a020002030700107542da0041e20703060000e41240700b0242c0b04d010103521219140e25005042c0c044e5101e10304022040b5006140d9034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 828905728 1250 828904478 828904499
    0x6080f18030a030b030705040c02210c060103030f17090a030f0e041d19170703030f0203040609020123040306110408010e030c01050109110f18040e1b03150112060204050901 76
    0x80136002c2c420f0240c01400141450184500700b808a11a0050030719411f00036180522500c959034460700c883d00400c14420009000e018041c00f8500c02c2e19640760001040f0790040c094041e100800c03882d250780505000c6e4060340059814460b0340d00d4900b020008034200b508464080c01c40c640c02da0042c0c103090400018811b03548000340c02407609002c40701310804003030100300b41e000c0400c0060030000814203071030880d0341050010a1b181d400b0b400e02107007100b00a0405800c980c42290103850069407140c4c00801c5680c400c41803207801810720303045100c0c01c05074407860449110b140b10080000303a070b0304001c0ca5143e9031001a9002090b02d28001c0106140e40d85003542c0707a5204402000d0694a440c8c000f00301158944205045048894107841c145403a400240e503955100e000d1141440b50300503242820b0303660b54020340024002402c080c0c14080c90880a4810705840000740e07a11980080a0341852400d42c2c6002d44c1c11907008000344a20131a6a0400318004d10440d000650064036240012580340e854 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 828906978 1250 828905728 828905741
    0x13140105091f0507140f1227060106020c010e030c0604080d08010e0412030c020a060e0106080106060e030604030327060b0f010513051005270f0a06080f18030a03 71
    0x103411206120282205070840f80220368403404100106400341074a00d8103405030403502c0982c1e40382e9251049026a4107241d8504a806c0c0c2186803004210b0036a55040e0340240104000140c014142541000d801a450348032160440f030410842c803a0b00c81a40e40d0401594061501c050000c0c1c2e500c23621040c040ea01d071003c2d81b40043c0400c13000000082d0640d00340d540c16100c0ca82001c0d441f07603411001401100039202d03421007442188208900603012403020b01c03a100b0918103003130000402c07030315081c0c01c9404e41d070066100400f40100b217007007191a601c1c0032900590041d0715207030000354550a0b6610401800b00e601300c0070039140c0f20380b43c800e081010540c4011007807001100c4890090342501c00450b06446a030001d6115402c1020041115080c940c000200100c5e4a00b81a4205807800798141350041825407100020b4015420580d80c500b040703940700411315410381d030041740035043c440080c051500c044e280b68003101da038800168a43c0c1c0314076400910041440166a5166401c110007400341c81c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 828908228 1250 828906978 828907003
    0x307020315070909090804050918100903090302040c050f0c0a0309050a05030d1107080a061407080402090c0a020312070f022a060c010914030319020f031314010509 72
    0x910401401c080c6440c107155109a060740e40d00e801c19414205840d02619004004440e451070a01020809642e06080244140c030317044600c1e01042c1c061140d10b1b00c0c1c00c180801114400e8070781580f4901081e84200b2070016242c0668011502800e542c404481c1d80c4688000c0881041e804102c80001c01408913010103101d001e0303514070b180b4030f88402c2000215116481000c2c2d0640c8103003510782c00680a01c0c2c1c1000f10880d20006c3d03c08c4039684600301400d044000e0f20486040d9582c004807840c40b4040c50219030030248910b0003915a117015400b1032218400504503540190000c0b9020046d240f0030000c8540b031120464104095050801010701040c1d01c81c0c000c00301500a01c900c00c4902c0351000124410124010304003102c80103d042480310310b03848104180c805541390306520b000300c0c207440440514100f580c8015941d91408054520800c05040043c1100a0040080307400700362012090b01d80003e403010011022100602d0107405c904800e02914001d54240700800c0900b1802049480041c0c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 828909478 1250 828908228 828908233
    0x120f070c1e050609180702121b010e16120501150b090f030a03050405010c020a15110d02160e060d0c0b1b011413050709060e1b0a122301030503070203 66
    0x50701c51041203c01c2c01041c050507080340d841100f01d0300035181c14400701e8000c0e655005550001d008616507030760b640d0001c91108044c40d0014000c1d86a094244503c1021403250400340232140e101d6a4a03510107022442400d66010b0240c000e10706004003984a0f568003d0192b03110103e030b664070403281d2030030b402581406e4481c040f90300116803903080128002500320b5243d1344241c80c02d030501c1e0055070190042c5034180d0704214550b9002c50320403c625014440803070306803121358400c0c4c0e50b03102c09071a0024011108003190019120100e0a005626443c42610907222120001c1d68480001c509082d00101020b03045021138400041c0c0c00e01c00d4801011514100039120321a01d181960441c00c1c0e038010304c5803030307445900540041d401150550641072130798820f5080d00c000350f45d030707040d84e006558541d00441c601a0078030090100d4072400d030f10a41c8044501003046410424031030ba015094982c02600100c0c4a0707200c000c00b01d1884080e06d02e500b61481e8803081d2841c41c0d612818556600d41011804030700a2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 828910728 1250 828909478 828909539
    0x1c02100c1b0204050a0b0301050906010816063903080103020f1c060e0a08030f150d0b1821070b06040b0913110d0302060f010e010503120f070c 63
    0x2803003212001c4003007400200311403064007158248801818018402c843c007980e01c0016a1080c0e400303014540c0076040080080c0610750400050310b04141c23503a240c00d83c260031f0841007041165000355618240e4400061b122100380000204241c1c1030140c00311040600c06014031071001c140c1c2010360070b4140c80c000d64460b592041503406111665500c0703421b905c18013803082c4050b00082d2007a0054801c0c22060000da5200a00655580b141500240c030f4102c0c44149800822204403002480300400403801c581412a10301c075510340c8220864040c0101101145001910302d8008040020309481000c00c03001d002041c01404042c6203640000104032074048482d40460b0440c940383c0201d4155041c010158a1320351948804d010017084284411942e4201c0111268046d549000c4000d6940d030090300609035603c0c1000c408244403005800c5001807415001c0140005d8170b0019100400000c1e200e03049a40e01200c038a0f403880750041c41401003e001800e00041803404c203002001200500a10306803100c5d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 828911978 1250 828910728 828910751
    0x30c0615031505090d09050906280311040207020a210b0c0a1107030c0b0a0c0605071115091c0c12091a0a050a0e040f050106030209120105010312050c1c0210 69
    0x9407007000b01080300180c41b00d0750500003880c0603c0b001d070f041013001b000340c2120080e00c0c80003908000ea0071100980181050740410520050f49a181c2c0701c060211003c6140000c5580000d62210303450081c000d13501e031000c0c0721030350039880d02d00c03050202504000a0041803800600c103a0142d8082030400d00000e8803c611025070b454002050001c0c0c83d40036040c507084509103005090150040d4002c002008600c43c9940c001c1143c2d4400c5500984040d80c1d10780401e160300d00380d2854280c8041c2e00d05290350f01b442c10040e84401c08243ca107440e1a11140c061070503003aa02e411555100c07000000740800014124041226030040403600850b100e200700c40c2482001c0548018850140c1d2190381c002c52010401c0c1c84d1001d02c41c040c800b1518070001c100003481c0c82e8902c50001203600980090f00402e43c0042c0e96405c41c80c0c4020161b010309580c1e402405a9030640d61101d8940410301201c1c4188a004250f1504581d0300348105c00440704007006000700300404a000941d18210304010070001880d02e01614178 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 828913228 1250 828911978 828911983
    0xa05010e15040c1e18090c1d0103030318150603030807050a050307030f0f0219030e01021e07060605031c0f05043206070b0405120a0c030c061503150509 67
    0x104941203001156150700c2d090342e554900e04030b1002040c1320300d00110040b070680c0d50690083c00c1450200c800040000051034403021000154010317082149448510b03a01c0103406007800c2d41505d50610f0041541c1c1c0d44110703c6440103800c210024140b007060008101010165842402142c1c040d0b0f0340d0150680f036050090b605d44c401c0800100001d0001c00009100d0340c0641c00010044048802c006526007000010004a07001054003102602e10380f082d1080d21680f601860400240c004000c43c81e0103000400d1755a003040c160b0441c215103a0115011702800b00300d50180008001c06415202c0750300224646d0b40604001c007a500012400c4008906039541c450700946080c0c9510748200d5002cac051070440041c0b90000412048a81d0102d10040d40300c988500303003c1c045091081c1ca040d001818149810307400c040e0b0302d5080c0f4a1000301804004210380d44408507143c42601400c103408104c0090400c1c1d0054070010740810540b40105000008106c1d210084402001500f2410405522005950f98 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 828914478 1250 828913228 828913231
    0x15063201080115020a021003020d0f0e03160c03050d08090d0507020a051c06110c15070c0816050a290f24090a02070c08071d15030a05010e15 62
    0x50025a200700140415121500000010b500300d0046503d2a04a5800501d0942c0b0001c90600000d801241c0020405554050443c020314140001d020b191020000d00e9035a006222042c051100010031403000d201c1120084401303140c200043c0c81c410021000054503003801030392410141d2085420300c04a003403040c0c084d02e0309070350300800d2860468a440c1c20818102d1110342c1200f01d166580100800081315481401a035940e00c10710541c90320702d0318001030300741003040e440071107001030040811800c40e0384040000f0a05a101c81069161001401c2c00e084d0120382460040440c17181042c8041809001240b0001c050b5401c501c0c105510907032400941c04003410380707205991485030740115860713440e401c1c2448000215104003101540b95440000c01070f1000303440082c0082d03030020f07001003072150b40655003001d01001401020b02d41c0c0f81c031041e82c000d803984814106a00e21038a003c1442221829400800b8030740040c01c4a0700090740d8140700307000741414003141d0264880d107a248401e00201080e40ca = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 828915728 1250 828914478 828914579
    0x3011805010f0905040809030706090501020f160e1306050106030506210d08060d06050421110c10050d020d1a10270e0a1b03271506 58
    0x18800d00f4909000c50700945009041121440014050304686480c1040305600403c1c0c40c0d5a141c0f942840c00001900301660b500596845402082e10b01d04041c001c440381e00e007281c40e0800121940e68400f05201d0a040c01c009008010500f4100001401581908524040d4108440e450010b22402141e903001c404840d4040401c1c1d0032500c0e6084150f0300030b2001d154461001340c000c4175000c9495542104680382100c0c201c40c00c0e8a02c000c050408515450488019203607410040d555241102e40b1030fa03500820303043c03280704a0001021480052080d820307912403584515080d0b440d8014541c03a04054071034500210044600354079029894900000000408cc3c2a5100d4401c2d0b070b059800d90565080d0344480e00c007200c00414a0014840d104880214840c1000d0140011088480d440b4011030010349a0880101414189144000900300590825003051203800614503400c074a0a50311005492060802e880c1c0340c40d00000d81c4d209100751400c5040090680740e4400d0740c10310000c040d80712529030503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 828916978 1250 828915728 828915749
    0xd05070308040b04020604150507060e030301030f0b06061b1b01022a0d0210020609010b0108190203071107060e0f06040f1e0b03190e0d08070f20030301180501 70
    0x41030100390881d0740113800c80d0020303005925154586c2000101d40e43c144454100181c0006501020b00069101c0c000752411080040c3d841d651542d240d03912558080d00c00501a0312038400420b1066591a048403002094a42031691009802c01000e41750202d0a2450307000d00050a8900403940c0f010800c2d88011810354040d01c0349419003960110100c0b105180942c00400115054000d641e4500c40d02190700001c0d40145120302d403480880d8250f80b0b80350041410b01c440304d024006503800c1c441c80b248070b40d40100ca0040c0c036660f80080403a0200c034410304fc001e650003146d40101d5241e42c40291f01c45410415a905004c0c6102d01050210742d10480c4580406140194014040c00c00c881c4121025507500580351001c050321452241c040390300684140650803548140103040801500440c02c52001141c0980000d20544102900e01c0c0001007a503410805a044007103c4c1c94041d828110752800d503110501074440508052507030320b074000e01807040b01070900d048074030308003040340500b03070581e00040d41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 828918228 1250 828916978 828916981
    0x60f0510170c1b03030c041d040f0201081f170f03120604021617090f0103020702010e04050a092906120a030f0509090f010302130e030714120309010e0d05070308 71
    0x3048040390019000f0304081c0c0e0b4000240c3c048510100050750240391341c500211766503071509418400f00b0f06411030000a2440341c90403c40410315101ea56103045070207007801c1e06542e4032491f402d41e9266000d010850103a8000101240d0440e803403408803443c1481100f2201081582c21120303030b48bc002c81e108882d44411000010b412030420b900504040302142050480300451a039400c0e00445002114441a40e80030507404070030b02d00725030344443d07202e020302f800c501d42651900003c05449014040a000c2d5841c0e0f00404d80d041041c4d8000402c10382c1060111000240c038a0b2851162041a11903080c41d0103508040340d01807601202100c00380c4901c00c0101a0704030140c1d41610b180c2455030559090042c184803400d42ca4490910705881424044a284095815403042010709400e4500040b0810310341780c80d82c20421070010440780099040009040107518000000e490b0081594000c54004d81c04000c1c04901c05054100802c030203441801d0f03602d0900c0c8e05c1400c031014099104080c0010f0540e40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 828919478 1250 828918228 828918241
    0x705030a020d06150602030304020a1428050d0b0411040c080f04030e040501080a05010c081b1c092d0803070f0908010c050705070f032f0301060f051017 67
    0x7070b00100490321468010550300f0350300090601042d500c0e400f00c2d0247c1c00000c100011481d10440d80c202070944402e242d019410710b4004525098203282845c180f03500b00e035130600600c0006090310401460002e01c82c056069140c81c1182c02d0b140d0540d0115468107091001041e94a424041d200b40c94400c2d66501701c150303507194080c0e0520b5a003d0000d5040c803419207221501d68481c3c1c01058040c0802c0d80050142c4031440c600942168040d03241d00c002c001a5209125511414902010065441880b115210001c0810050010800b00b00c001c52440c548a10002004941c000107400802c180c14680300300741d02d44824882c18002034000501070346003040003a54480c0680c014102e80105840c020080588540c6d14030b08559411300b1240200d90081803807801c100003000210003800d041081c41d1000791965584803141c549070400d9582c0400f071404c9440625507000c001c1c01c000342d130003002403042c0390b52400030101343c491034020700d405801d00b035003c484524080c090641071039051401900440c0d6840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 828920728 1250 828919478 828919489
    0x7020a08060103240e150f0703060b1e0c06040b04142b0c02030f0f070504021c181b0609090c0e010e0102150f0106082d0c040b19020f0705030a02 64
    0x42c5040e0184d07503940c180004410100300030101c101d901364018080c2e01c3c1070842000c021001c004018100301820420180071604c0d80c0e806035030b09030683d0100980f000112501d040d01c1801010104060b9104400c200000d004200014a01442c0640406001e0b4441a001c1e191603400c0b2950308501400f510360300d800500c40c56400e07699404014034014a034400107500090802c002611300500035402007070b00154254040c0014002000c1c00c40c2d0861608088006e040c0c25194030405503a0899950104100308140901040701d64075441007514410a0800d07250b0b203816000c6000d5803001410a40f03000c01c0009080c801e062203401152a81a081c0c0e000f5001155102c20440c15241180503048208580aa00b09420341c0140c034400319488a40d0b04140004000200080800010420943d400d80c0c4441e00e4400362020114240403401c4140d0301c084038200f483c400c81d840301800c08400160b13206644510503290024079100e9003980c000810b21882190740c0c0e1482d001f180c0d49a0460401e200051805 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 828921978 1250 828920728 828920783
    0x20306011e081b07050613050709060e0c03090f070b04091104030b06091018020c060c12010e0c160302100b060301081009111206070207090c050a030c0908060c07020a08060103 77
    0x19940390f82c50039006a841d1802e00005603541e900c45102c2c0746008040080600c01880030f01481c0c90100075107031404604600e980c0002d05000c50121001001c02c0a4600030302c0310340c13521035003032048840c407980e241c05628581e84184a6058024a00b015862440040390100d60440b9005810b00310161544000c01c11400c0b4054610705940658240004442c80740410402c0010b060b2440141c0b80c51540b41000c1c20b0040040040415070800c00107121000c0c48581c0e040c0c107484001c0d05042c01680c820084000501c100b8081580c4200c4003040441010341c0018a029920140042400400c2c80c0c1c01c01d00601c1c0c017080c0036180068028511400d5500c107198812101140200c0040c00c80c1085e000100c2d04000b140e00d0608400d41010b000c000410b501042411f006105041c0c0400c42c9605a40e0000c10600400446030105a2034035500381c9002d01c01d90a401c042c3c1b070741c003081c3d90b890708050a402c0016400104124081c41030010300165040012803010304807038111424805403c6c4400c5004bc1d00b800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 828923228 1250 828921978 828922021
    0x60f0f170c060f0a12050106120b03060403080f04050a05191a04080405060a0c0f0b0906131a090a0b0109050106022401050103021e0703031e0b011e0908030c01020306011e08 76
    0x442c1366004401780d030501409009107030b29200c0e690b190a01da1204402d4408100701c840c020b5000000b40310000390b00c0603545a1003c6140c0c00d01c4a15103c13071030028200081808081e01902c00c0c060030240007400e0440b8106068410004001d00e03009a00244440007000c4801600702d0006020800c210f0030110024000c0c4c0b0000e140c01030310810503a944111b0340e0142c041c02d44e220800a0304110141c8000c1284c1c1d9048800e1010f89020305105136200160320f241c66081e0f5a4031a08080410842c1031704000c00d9401981c007140c40c921a60311080c801c4010074003441030700010300c0784800300120b9100c0042d0041d00c4d540b00c00b401403926800c00d00150003a40c0100301c6454110411078680c447d00300480054420103110b42c0c0d003c030300d081c406e1180d156020961040e0003816413810541d5140b580e0042c000c48070203203414103413484042668000340c3d041c0009502005841c007002030080500d072419401140304032000d0300e4150000300c8020054240107500c0c0c111001145404020401c4140901c0c4507100810303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 828924478 1250 828923228 828923237
    0x10f020607050a0908060408070204061a0306131d2d0a0b1308280509030307030309060f020a0309020a060201050c0301090203150d23060c1c060f0f170c060f0a 70
    0x45c1e6807003000c0e02d4000103d50a9540c10801f1511104514103401050b005103c0da440804030f0348900540314809110140099100301c644d0549003040020380d411611600740740c1105a071080c00d8505406c0d8640c41e40300507808001407003907803804280c600c0c06c0705564581722820091140c800c1954500500e00c0d4098204d4403d501c546480743e00044005000b0840340502d54030765010440400011911842c40c50503120078000e09100742c0c1404e850000a0f11082c07601072a01086000803801c180c0004c1a101e105010035070b000045201d4544d8154010700a02407007611a10007a541d00d050482c22590151980500d03000208010000301c003550f005181c0010b4400200b1400072070030310008007000c1e662007040b683d035440c0e003101041c00c0c0403524403054905a98000b6000e549003031800165240f0545a00843c45119100c0004403130342641d0004002e02103541c01008400d4803030003d1198001d10b403003012040703c590712104c0a48940400c02c881c02200140005041101005c1d0f4000103800c45d40c0c8420801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 828925728 1250 828924478 828924497
    0xd0203090f120d0906090e0402010c082118150c03131a040c08100c05041806080102030c0909070e09040803180d0302190228051006140a05010f020607050a 68
    0xc2006012070f5000c0e01d0b09890f5400301034a420340c00391211090380d00000d0a582d40404210244c2d0300f109a980e10203134480d00c4a5a14000c242c4680d170041400f40a0000d001500020008a42d90402a4000320303200c4e901140d4405903440d1b1016480d00c03003110940c0ea80745041c00402d0300000808008440ca6118000c00304c4034081070301082c00c4002c0202c03001d9990821145003002200000d00c005810b4907418001801900d00c0d81c50081c000c0d00c0303284610b000344e49690050000301c12107588440d000e420024000d650301d0400f100f110240b50800b9003000e20400c1c0c58008104618014041084c0340302d03018024060301e0b580c035261040150002468030a5036079900702e4000039000309000c105024421500d0041e01caa1042c900c002d80c0441d0020408155489552201c00102c030000300b100d40b50310000c1c0742010200030313071500c513003022000107809190034240000840c80a0038040d49104040041d45d17a102c189694400444840c2c41c00e203c014096040704001c41e000c50710600c000d1164038650304026010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 828926978 1250 828925728 828925759
    0x1b05010b3d09031509020901171f0f060906051801080c06030a0e06090109170a080a02070507050a060503070e100e0d03020c0d26030c0406350901050106020d0203090f 73
    0x1254954502040813541c0c2e01c42d030404519100780d1040c0076050005280d03000469003c105075991405040e10460701c40803142c0c52800390390540241019910005003482002d0755031280c2e101400d103602885100d50200c088000090f0400c000d59412109400000c000341004403060000d140d0002e881c2070116501d40c621804061403c00c0320714080c52100000007010700e5142414a0048513001b100005080e08000c03c2c00c1565000039611b07000092804d0040e51001d842ca01140340c01510f501154104006910004426030000041d520902858a800c801c0141d060100060098201180c50205681d010590603508103070300c4022086100780111100e000020300003c40c4803030140c40c100e841e100010403001d228100014840c540044003010f481c00d6060403880580700340600d003e41c03010004820141c0900c1440502140e104201030b880004032003400601150354502c0c01c40c1c883c000c035803c0000000c1d20f2480040c04002d411200c0d4051828400200104908028402c448540c0031002d0207800d0311 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 828928228 1250 828926978 828926993
    0x506041509020a0b030a020426070503190b150406032a030209220605013c030f210c050d0206010807060509040209060406020d081501050a0f1b05010b3d0903 69
    0x2d20695001c68034094009e208210380c9031440710b81010380244c000340020a500341900d1510f01c8040e601101c18201c0b81c1d106000030344001e000c0414168482d0030410000305001ca40402d8458408410354100c070350360308a80070b42202602c1840020740006105000803038100700400840d0340b0305000001030a400f0140d0702c0b41c0040e83d100703170481c4c240300c10354800c04d04c443c10100f1004042401e8228142d401c101c264003502200540307600c070280480e800300466904120510030702902611074110600e5402c1d5206100800750549100129010700c1840248520740d800082c0b03c0c0d048a10722001000d519003003c0080301e640e003000080300d0b0044d4091080344025078908001c2c2014148641c01009280d2a2890042c400b01e00600140240b8110000d6000030f40d030f21400300d4400b5000b0f410f05642c06684010101d0b1100800b0885000140020f0a10010800b06400403043d501d002c81d9000440e140c01000100707104591146800c5204525042d41a044d4111000f85007080b0741e400d10707040580da6900c0314072 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 828929478 1250 828928228 828928259
    0xf03050315210115030f060b0d08040f0509010e0f19060b0c062706160c0209071809060e040f020f150d0c0918150807030506041509020a0b030a0204 65
    0x4004001d10380b504030803060912800c0b0f801c0700039095141da41460350b1103611184092140291543d42c4842c040c6131903807070b6180143d06081c2d0000025580741d03511100345004682e02c2c051684210180d000005070220b103400701900580c814180440b1036100c05500c041055800b200040720a5200c10001810350b803200f0182034004000c0c405402d00d468022940300490080003003504060040810410a1890000e0040d030310480e0808626240140382005440c0c03803107501c1c8000d6004a0500422848075400010900c0380780d00100e00d085415107074035141098814034003507141ca0705035080000e00401c00c40d0013089402d9001402c3c803407131600c1031404900c183d141100158859003000901000d0b0128501c107280080003145808005c560506c202d048464000801c8500110b403904c1e0807501900740d0f000c84600030120741e02111400c0c1e580f0300d4100e84404084170706403030038609182d48070403241c02400360800301c0e82e0082c070980c001c2d8145007100440c0d8101500c03040182d40c0c20b000100e0412072011011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 828930728 1250 828929478 828929509
    0x9031918140301050702011104031b0504050c120f01080a020d171308150115030e0c060309010902180c030408030901180f120f14070533070c0f03050315 67
    0x81d078511801e140c01d5030005048541160300d0030b11080401e0040200f6501580ea001d00107280e45038000c4681280e00640360050f641c858078000030f0040300c1c0000002080300c40400d1700c43c82155510000285810503007440391030555005000d206006280111001e8100c610038804820350400403e4005201e4005907035810610f2060a02400301c04801c20100c03003001001204d1440c59030600303d0f480c1c403244060700000107041d200c200785c080c100e0342440090b001601c05000035840e071510074800d40c081c02c0b45103c1a0b00903c0c10f0166200d4169812650380c1c072450f600c8800502d10f8680e03507071f050036030351009101c10000c0d56500d0409411110407150216120301034a035000749442c080c201000006a0859900240032403402e01c0d0a0030350f00407510f00c00e15039400c0b00107601c07130f180c0d03040042c204110008100303100001102184055a041c00c115a1103840c03081c102c49440e82d40c1c2d5015500391109001c0030300101104c410b20b41c00240b05030001c41d40004001400d00d202900200419071001c080140d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 828931978 1250 828930728 828930749
    0x1504020c031b1002041d0a0905060903210402030c060f040e011e06020c0307140103020c011119080c090f04060e041406090703110f0414040606140909031918 69
    0x90001d081c100000c0039030f00d83e5804110f15141c5030400b00c1c2c460001021501900c3d034a544001010303162141d201243c7c058000c01036880520b40800200c0c0c89a20001d0440e600c82e4117404842080410400c1e040e01c2250301500501440989400700401504101c107081d003a030300704100104d0340c00108000341d0700034440b5a45504062264100c01300501c007164104000f150b016490102465800190000417240d0806900041c084a500100c001c0d106102000f5070941c2080444401d00d840d840040c0200b240071003240c2c0c000001003004980103403040e6803c500048080c484000c03580f4000030f9960f07010000800025183d0703a00d03140340411100c11a41540c6040d40700c1050f103c00300d0103005440e8048207803000340c6001411990b464080c814440d02d028020303214011100090344503070b400041c11a245d02d0b030b070078660b240c1071070032034080c3c000703801001c0440f0089a003030441c45c144102c4142c0606000c501030350600c00b01080800400c40c00480000411aa800b8200b0080031500120409022850302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 828933228 1250 828931978 828932017
    0x3070201020c0f010e0d05011b0504051201020c101806180b011e1208040902040308130b0f0409090203010b1012060b0403020d1202010605100c05150105091504020c03 73
    0x19042c00d0000a850f80101941c0f000e0901d16070b0302c000c0d5094118011100c4c1074407400182816401080440c1e45541c0380101c02003110503141e007000250044030320841d28070010300c400c0c3c18000c1c282d02034070f10b025500340e00506019200000c50f400c041c101c0b40d0070a20002840200f920f51100341e94200700c805401d03214003c01d140c20b04c1580307240103015015010180011026841e01078204482c64401c820201d40b94000c51000c10510300c040710000c09444105540301c03612414040341941c030a030342e00f0a140d0188840041d031a00d00380b007510303187c880c105208d508003450050980054140201d040781e1555984148240b00d0390740440000c0c900c0f205584d02840118050000c80c200c03a45034100b840c400c507080c04208010382c0d07800c0742c0a0010345d01810341d1401c04c0d2034201c00d0340903003415081141c0c0580d10b0205000229072200320002071a0244048036241101071076104a00d010038040c1c2a044584480003417540084844c64031040e590140005141080041d0307203070700755008170907034160020004c131 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 828934478 1250 828933228 828933233
    0x3070c06030509120a030908090d0b10140112180609150c080c2a071805010b09031c0c0609050114061801050f123406091e0312020307 59
    0x2107450f90266a08008058940c8505964421401040004c404050322615480308101039802940d4251801130b00080941c007552801d5010728400f254140c1035000403203800074290500c25441c001e02c0070103844007013484035401c1b4110080c181540c8201703000200001148000f038554414210898096140391407161650300b8010162503082c644802000040014003500741c91540840d082c07440e02410b06541c58000700281c28002074581c08031501d9002d012400034a0b0b8408004030b0380440b510b400c1c00c000517038803101002028014004241d80580c49042100404c0001403803046800015040294040c08181d903100c056500b5074a0803949039449212983d901800c011a0303a030401d800b2112442013090600300b6200c401014801c041c49181c0001c115615910f0740b042102d021410081503402c100301000701c0c0070805803020071040c510102da1003c0a020140307014800140c400a5441c0c2407500d2408106401241081074100030f80030360303010008001150940b24018207031207500a103445080a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 828935728 1250 828934478 828934481
    0x10c02012d0e0103060302130f1d0309311a1905040c09061b03030207080c01021b2e0e0102130f0501030b0f131103280608060105100302070503070c0603 67
    0x1000503a040c14213105c01840180d0720386200801d02001c1b007500281150703242c10032101a11014000208110440c002c0c04244c90020004200440c0d055640720b4040012444c2c004250800e000302e01c3d5030750300007412804000c0480d009052a000c1c0d401806914407440780020341c000c074070300d8841c040f0403440403000c100c00d0400d802008a0211070342401040c0c40d19151000c1d003a08000c000a40e44003401a00c45030405010740c0c140c2d40102e810005858480d40c04606e458001d6003c490030145052140c064a004a00b001514601a00c0c0e5007000c94800091030a4a51203266040d1010800544815100003c2c1400b44040c0024030840f4916411551501e480000003440c0da40086040508040115071142c60364a100240100250f95509444041d90300134002440304040c204030755000007040c801310801000e0009010a000300500d0644003150020320201d039030f98810940c0540007200100300340d02d00705a0015850038542005860712801da69800c7c1554000c01040700c4402e103070300c0b0038010b040d0706 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 828936978 1250 828935728 828935747
    0x60f030c180b092d310209090f04200307030803040515010602070803250b1f06030522030c05010e010515041806020d020c100b0111060f0105010c02012d 67
    0x2600e81181c1c0c480c030440c02004515209a01d8903000d211000c805003d10017150b982c1e40c0c40960741d9a045031030065404c908001039030011405501c10b082c80c0e008a84000c212004d068041e0740d0208895203a100f480d81009121400b0303e40080e4940118440000031031216002940304070700c140c4c05003030301e2600710340e20301c06180c01030704000d08641c081d91007130141020000480e5400c291155118042040340c1340440b00c01e44900078000c0c050300d842000d010314150000c00e0941a031190004001381c89031103900840803a0002c4420311208501200d1300c011300c480c4a050142481c2c043d160003d402c1c5081d40b41d4509445081c80f4115a580d5201c0400c001213604a14031140d81c81c2c211800c1c0000c803074514944002c11090742c005000c80303a002a1225510455078115070310702ca45c0303d0030f50b900300217204140f1380140203441c3c1042c0403400700703130003944240c80200d0038501c41d50542030151556401c0800454120000c01c0c0200c1c1400140010100010125580e0700c01c82802076070035241c012117400004020301d45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 828938228 1250 828936978 828937009
    0x3100203043203030f180d020a0606060e011403060103090503031003050606060c06151201060b09090c030103020d030309021c060b0a0b1905030411043201060f030c180b09 75
    0x1028040103003610b101208581e040104480b40e05101d858030741543d4502850f281d0f0160291081050444401c0c1e0080ba41c0041c0a000e00c4d41009819520032040c0c950014002d80c0c0c0e400100070686194101340d4050246405c91810300d0700242866603940e4451960b801529a050b20b82011182081002020030125910100503220b8604101c0c000141d59a03802020b000c20f2014150003403006c4068950380c1d0701400f20350012001780209540c50220507944c0c3d0003030b400e40340140391400c0050907042440c011681240d078081e01c3c0030945901178800324010442c911040341d01c0186c400f800c0c01c485c5c11881c51681400d001d004001348482241040050309002e650220b40d020030b0070300c41100000b000c80002c410905150403c9980d0740e58618001a03120507051a407a071061401c1a441900c06500c80040003070080d44400c00024111440c0c41e6a041c1024455640059980740d0421282c5100b80c100f03110781c8070541400d801c00c07070701d0020300309480683e60000d5540c40f80114000b03180d0b24004003080c0d10080c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 828939478 1250 828938228 828938303
    0x715050c04150e040905030a03140a0603021503070c02090a02091201050c04170a0804060206090714062502030a061b03050f060d150510090c0503100608060310020304 73
    0xe02c0c040302d50000c0d1409400100520000746a400416100d070340002001c00ea0100541303581d4448040c000c6c0c024000c0080e0240041c090200060041d0f406102e0103098940041c01c03180034050102903a9032540c0002c1c003500411055482000060b00c03141c0a0030702510740d0301d801680b90b0358500c0c203000c090901c0c058480107580c14241884464001c0c3c400b00d50503509444011404100341d00401451b10010210040500e5000030300000c019901042407401210b600007954100b9a65940c6d01000d250500000382d0b000c2810048060303211038802c7c0b001d61050850300580a913417920b030006401d01e000e000c0295070b030648800e4681c074100741d0b28031903402c11681400c04004604112054071078000c402401540608619003070003092101d000c00b501d04188078180180094901508200d40961192040041c00c50614080b40034403030090090f00c0c4111020810b01000a2510340120b4001001030703d900d415005403040c1011891607400190b1150f0300074007507010112521a00310761204041d20b0a5600b04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 828940728 1250 828939478 828939487
    0x30509060411060d0b0d2102030a02030a08060a0503010c03050417131701110301080708060a060311091803040b04030b011401020714010512040b04020a0f0506091e060715050c 77
    0x44450025010b488015220180c680d43c081000c98020403440c42c0155000215118840801800501100c0034411847e00c421050007200c2042c4d80c4ca014403402d11015810910640004900c0782c0c0c1c0c0268044401010304201c0c0d13555602190840d0020101c0d0f100280c6c6850412043c016081804008080d0340b14003945050300302d042603145030300d06000e040d00840e203a42ca85103005100350440c01152564624003a07036540d43d00301c250350ba0030780c5110390f40d424020400003400303000c902d104400440303401200c1a40c4030b034622000c001039054020561403003091031328607a4800c001c00300050070240440c208000e0742c076400c1d800c0c08a0801030507403004219029002c2d48030000d90340800e18108503031088403421040040c010040c0e8540c01080041a014000e500821042c030100d1603901e80034078026101c12410360b445108a140002d2140156608100204001011070412714007080c10f0706420500c034004000b00c00c001400e00d034040c2c41c0c140d540d4248090b0019280f10144a03c642203041610721500c1c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 828941978 1250 828940728 828940733
    0x1309060c050c0c0108090a0b1017010b0a120c15050903160528030f11011205040308160c0b1807080c0a03020409020316060f03230103020922050a030305090604 70
    0x41c3e0311503209050412039041e012600718030003000360308a016845450181540390081402200350850302c03c00101c44081e8004961140040c0705840c003610700902028606403d0107049661142d405000312414100d1101c0020303800112402805140c80580d42d240d038412602c01003600d8840103014004d500101b1010401099460010642825140c071906042171380e01c1d180b026817580040e510141c0018031000c1e4220801c54076540001d00d4581c03d0b03c441d0350100088201804075042250b0040103c0e1951021400c49110081c125400002d94036125040e00c0d407942d035440e0403402c19a080b0001600c22002c1d02d28152003441841c0280109000070101413610000040c0d05000c14071010b40542d54075050001075480601010511080172603894406940c0c514006101c10310100e00140024580301410402c0d01c4034421071010000f0b501c0305d4402c141d0070b44c1c08000404d60040c00e46001d102034140c840140022149046400d14001e4010380800c80140c113020301580c0d070061100308243c00002c1000300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 828943228 1250 828941978 828941983
    0xf0e1b030d140d0603030806090a0e06040b090f100b090612030423031906150803220f1212050c0604060e01060906090204090c03020301062109021309060c050c 70
    0x2090381c1c070328085241c40035000501c00035204140c603040c955030900d00040141608640c40b14081ca4042d10b2049090380d529000d00c0403640f48072010074242d00243e0100d00801c040d400010b410150300c0c3d069403071340c2014503801841e085e4000000400d4a843c0c0344030101520b08040ca680e8040b40580d1548900080090201c1c0c80740314500a9403001c10814030403203000c1c002e0383d000541c00500a0b04441f80f00840c600c0d403025520800074100c90441c00e24021800b007248654004045802590045003070080042e08003111044074074401600c4d5110401c00200100226541c4000300b4007182c2403400410182020b00422a5072012101030180420091101c1e500019071564400e42044000031095100305a00f0301401c003507032003076118504002c1c000c286031066900600840b4002c10007040b995401b07010640584c00244208e00103d59605021000344c2d2880340c6186245803402c0000424544d103600040c0060030440416052651b01e820300d42c00c02100c0d1045102030106405c1c0641001c02d0b0901103503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 828944478 1250 828943228 828943243
    0x20309090708130b01060e0901240309080f2805031303110a0507080106080c0904030f1202070b04030f080702070f151403070e0a09060b040b070203100f0e1b03 70
    0x74200034084001403100001c0c901c01007403003540102108031650f903900c001001e02c1441180303603204070400400007450303d2800304001410072070b00410b804c00030402c1c4415001084035100940e44142d0411200c41910349120007030040c00c110400342500300412282d0006803c2c1042154400e011007041403200043c07460342508030541d81481e00d02e81b81d440702c1c407545041c440700c500c0040081c440e4140224020b0010b40002d0242c0b43e01408a54500c1840002c2000082041e10068041005a03640002e51071041c020854042843c0c500945001c8907a51040800441260250300041d40e00071050145a40040c0094000105100506005084c13072541e00b40c0100c10721501910451075004814181d00914860040501e0040791940b40e28290001804443c0103000081c032031500c1c05004240c2000d01d101d11800c0d100320601560405043ca800e46c00103034828042079905104180d03500003260f1680c020304454640460021810002e5003401616089250901d4680070302e140030b091015442c00501d28 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 828945728 1250 828944478 828944491
    0x1090506011e240216080706110105011d18060703020406030b0d05071e1208040906080d050301090207020a05090414190503030c030a1b090305060a020c0a11010302090d0c0305010c02030909 83
    0xf40301c000c4140e009a1400640c0444000710700705a2030000381ca04004100401200d119880b59441c01205040040c04c0360400d01900c801902c0040300c41912041004d00c0c01c1d0704c020304c2c410f0004042a1403442500c0c0600c03c542c80d00c0003940024090064941c5402411100c6005030350036440c880343c0b130303480d103490b94068003618071201070b440050855052a070211900502040fa20411202001d00381040941c0c420b00442c682d00303040070000204000b000810400488280d96624210f90825800402075802110166840340500001140d43d54851807018046c0303228656014144c07118a29150030030601c062603004001003408a20f01080010003183d60190300c4000c00c5680307640e2601ca0710001c00c0c0c1100e4600c00c01101c3d407e0030030382d03a03041344d00d2a0a80740641c040310b01c41d03910504076206a01c241624403207d82c00c092484400500c40c07405610940300c1c14100582403912100114400c00454031007561035a852000400c03d0050a02c281083c40d00c3d10301c0594940142103003c0b900d11540507024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 828946978 1250 828945728 828945779
    0x5060109090614010f0329090f0103120f02120a0305061f091413061509082404060605060a020c120303251101090c0e07080106080a021b01090506011e 66
    0x141710903110381d0000b40300781014241c0d83c5c02046861400c0c0c04861f100d00901d4044c40701c200110303210203140ca207524120303070303001c400c50880b0000c602e07080b0740080b4200aa60158400e60f004040c41d04441405010f6601840e50002007514106041241c243c01d1404010408001c2070f0040c000164494096400c2d03d05114860748800314040200c0c2510304c580003120f00c258035041021600c0d8160344030f064142405582d44100c0a0744800360030307449400c0b01444c0c2e543c2d00c0c0e0380d04280300e40c43c07100002954481d0081c1740020310f09903150042140c40c0c2c002000c88005030480c201910b19031a118540c030100c081c1d2803005508518288012075500c071000d010350044180900c1c454043e00d072241d1703050700e94180840002d004c00b1100d0b160419807802940220103844040d01e00040403d80728102290403034000350b5400a86484079000704000f940140d43c20315200c04007420010714001c00340180035202d4031420080c01c042d0b2400e0050950140083d403806a1101040e070100580d0881204021000c44000311 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 828948228 1250 828946978 828946997
    0xe091006050a120509070501090b040f050906030a020a14040609060b0a0c152c190813030f14060606030115030f0603061503050708010e0a0b0601021207060506010909061401 76
    0xb4243c0c0e0038072200790070207019070800381001080d20000c40c50307404030394003070f2501c84003961618110b0400d40034600030b2400007070300d11a042004d45401c0c4421500108040c00759500c00045401103200c00c15581c205154003005c0d81d60b500070700e0401d031065800074020010200b01880c244500c50341d240c451204420b08016000c01d400c0306010955a400b4090326113564100081c00e031260084c8415601000f140b182443d0094102800301d00224501c0601002d40802400c01880b0380e0b02d107030440d00000d0502481c00864900400016800c0c07500385003143c020011503400c841d00100706464000000c08440c000d040c00d200410042104003042c2c80c25502d02e09021030069a080d1840000b032900754001b80c411400c20240d45144281c50b00010184c0380104142e071003c1e51245101e5003618181040c1c0c2019600c100c940b02c2c0070424000c94a6002941481a034845000b004d880070041c0e0481c002c1520482d86c1c803800d0041d00d40e006174070280180f841110a025051400f0052800070100c074a1081c1032000580 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 828949478 1250 828948228 828948247
    0xc191202090405030c061303090906180915140907080d1e0318030c0209060405060f040513020d140609060c030415110c07030203011d0705060a020307020a06030c0e09100605 76
    0x2043d13501c05000a0210f0b01c1134a006801f1038032040c106101540484c05440b00820001c10b1400b0317040a40d4483d61080f0602c50410300e036100146109001551034407881a5140e0707198070f040c0030b070311200595019001400d00300450135900741a22540025526030090080c403082d9a044080486881c0d6110204000c81c41c0b0540140c0103828a0200c0c40d500c001c401e1030300c03400c050300801201000c60007a551401d0729942d207130038002181c0d8144d40c032692149995801c0041884d00b604920780c0300038100700316107500340ca981c00b08140749407a9108070343c0d020700d034011117001d54420456607506c0a4100b00900403401c02e080e040c48140b2000e80040c0074a41ca9070310f111800380d5a5000125000e240d0403080d540d03240c81307005054a9a2203800128429401d0442840000c0d6805201202d070b40304100242201c40d2820042020075030005c90ba0200b9800280140341c09a82d80300c0ca10002080103850200e072040010070010b200c9101881803a02c260344610902c2500000c0019040c00d9461606150b90b4602010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 828950728 1250 828949478 828949483
    0xc1e01090c030b0906160212070305122a03010302010e010c06090c030b010f060206061e0109030b1905070c0f020f06160809040c09180c0309140c191202090405 70
    0x400000e0141c0d1091400001040300b0020f019204407a0b0704244c80803900c603407080034001080ca40e00a001a0b10150780048000070040c0180041c5109042152409030348440d80d50651504039200d802544800c48101955100c008c080e4180082c84001d20b465507045030f0010300801e481190f518100300c401040340e010440d46510214059400c032030200b075415604c1c078100303040450034081c0c00d852065030340d00014520300025001d40500c80042c200e0403e0f240c1040405a8002a28055410004101800808100443c2445001c0d6170384280124100c15911038007025500d028200c0c20400211545501c0882c030303e902c185101580c101d40c8845414807840004484d8040c14201d0300d28000b40e0007540d001c0000b40f000521800c542a103081c0027640382c68034241c500c440300d0b102d010000580c4980c80048861140e200744102403a034200000d10b02103c4c2c942c0300d40c03215181c6101880f5440050030b5202490910340e02106800100050340d1314a040c12650b41b240040361500900070100e0002141c10001c0a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 828951978 1250 828950728 828950741
    0x902160609060b0102010b040b01090911120a020702150a1727010e0c09040c030809030703080409020a080f1311060d14040b070201090c0b0d060e01060c170c1e01 71
    0x10501441c1d074542481401040500c0d1076a025600e0520201a02c3c24580078444036148140c60b01c2e40700f0740c640000d04c4090803540d05c607c24402e90410695007950520420315009e03031a101001a00e42d0310910520004004500d0b421508920034804d000241d80e100182c00c5107003e68440d0f02c402612107410f580a507030841807080c400100d10b410301400c145415030140342029000c00460384821208414011503c0c0143e80c058103584020340140040307010500140000000901100d408558988520752160401e400c081d906030b400103a00e55540e03602100c8641c21100c141640f0209083c0416120340c0b81940a200400c810580480022141d45000075a140e4040d12103052100700340e12070500a0f44441250b0440382407500c900411415841407040f6110643d115170555030305070400a03e035020350081c1030041701582c0c81d0710740400c81c0d41d8800141c134020180341d07e800b10075110a291194441c48443c8510b5442c10003030000505105001503c3c0c035446008002014a007591808094050101d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 828953228 1250 828951978 828951983
    0x15020c030303191103040b040f1712070e040b0a050411130b0417030a05030f0603030d1e0e031806030711070b0a1d09070f1817150c04090216 62
    0x101000f0005440203450000d42c0903c00d80500300480c18061030003d0b81400142c501501c0070066400140005000403a00015180100031403407080e00706911700b05240d8810f0345a2080080d9450610a5068000411462003401100c0505c010000c01d008112404941d204903072255445910032a80700b4000f00480300c03094a100d440c0c0301c0294072600b40c030405500c2b038448c000d05010243c1031000d210001200740c5403154400d035501e6281d40c0b40d80d02114240c980140600358140000c008c0e619000c01c082c480c140700030208181016255140e030712010210340d41070221080c650030412403421680b5035078020070001d2000305c51083c6c581e2290002101c200d4404c4c10422490710800801148070200a00034008802081d134461142e07642200701410140c4249114075000601640498001e602130b04400718603000c176140002c405180140c4000f086200c690140e81c0606140e800580320038428810f445c2d130700100701d5000000d401c2c0103441f04032510842c80f030380802c540c3c0031a491410316000c0300500402d94 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 828954478 1250 828953228 828953233
    0x14031504111305010f0509090601030f09060c230d0e0f160305010605010e0d02010c080d06030b0f010906060503010e0402030c0604060f03050609070e04020304020609150316080c030115020c03 84
    0x5003400302450290302c076920020b0400302000d40001c03950b1140c0c0701c1c004011901d680302414080c4400601c02d00c47c0001d80300764140f548803038243d0200c0d1030610400d03c20324000c401c00300f2034111408001c0d001803000351411609545900d003071f4400003004001c8a000000c408000564106515030041c01e00724121090b40c4580100c0403040c03804881039900300280c9000300d00030049155503030010346030301c0d2001c07180c0c0340c2000343c0c80b21180142d030044000e03e003a00d0003012240e00d4102003040309411220903070000c683c8070791030b2420700c0b84001008030043e024203c9104100901e5043c00005401800148200c4080a0a0100040c00c544050000030b55400016000a448035190315003e0000264a0400c03070000303280c003001440f103140480c1700038080c1001c0d80b900800d69411030248000303540004c10a0340c100000304030380d21094641049242c2040407540301252642810b104810815504149050801c1500c02c00c0c08813801806048904598a82d9507283d0440c202550036030420709007040c1c00d680360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 828955728 1250 828954478 828954491
    0x70c11040b1008040c1514070c030c1215230403090b0301090f0b100806041a06040902030402190e070e190801050114030f1506030a050706030b0907020d14031504 71
    0x680025105004c0e620405d0b80813910b03621500d0b48111441c2c611404400145444c1180c051050310500a05c0964090f4080d81003241e10b0f44c480262070542503011405c001c513402c43c1c01d41405a881401034a085814400344118081504030041c4041244a0780c1720341042c64001c9010540642e00203801030004800b815100e603502e1646800810301c034000300400d1810030854103014500075401c421090000c0e20340d030146132150f20900c802030909031401005c8880c1840e4441207903441074042c000070708541c20007594034601441800080d40079051401e00030070410340c0034018007180c0907889070700c1a803d24010b400503810a0000708034144001040e40c25428114021071202030640107241a117100e01c84c3c4240380f54500702411759980541c54004000d0b00041c21780101c0d00100e00003a80c01c0f0310f0080441c1c10220071034440354200096640540c02290361703800700f142c0030b08190001960245090014242c0700444407800f80c40c0d00c0f864000c00c809240e00000140c3c00c4c40340030340400c0000f00054402c0161 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 828956834 1106 828955728 828955759
    0x41208030103061a0310020a140711010212070b070815091e070f05042c01081b0607020f040c0201020409090506042006070f0c0b0a031e0203070c11040b 67
    0xc0025090754144007402078400b0b130ac1d4440c0030340310b400d0344241c1c010006450035000c802c0840c51003200b840508040790a480c940356002c401400d00040700e949042041e0384828111400f03940c0450390500340f00030b105980040b04860400740e68054080e4441000c2602c1000c03d80300b1300c40008400700010300c003000c1c4036140405844981c400c08118504243c40301c0e03034402e000b40c10001050b440741003007201500d10148070700355401d003c0d209a49803003c540c01050030010703201c95441c000d0fa103c01c081e80d2064800d40c100c1d0010030f200c09041183d0040d170b250250315141c054a040d02e000f440e031a540f200b8011300d01414101c1440041240346032110b2982c4e43c114078400300c1016502011500340c0004d0f0070380c9040041801003001da034005000304001c010b82d10400701c840c000080c4103106008003c825900070043c80e41c40f0740c001008601c0500c0400c0020040d00c02159125003015002804440 = true := by decide +kernel

theorem cover : BRFrame.Cov 828776978 828956834 := by
  have h0 := BRFrame.cov_init 828776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 828776978 ≤ n) (h2 : n < 828956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
