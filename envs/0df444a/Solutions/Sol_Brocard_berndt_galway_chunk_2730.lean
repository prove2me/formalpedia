-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2730
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:34:40.716229+00:00
-- url     : https://prove2.me/submissions/99742c09-1d69-4986-91d2-7856c1f28fd8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 490827338 ≤ n < 491007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 490828588 1250 490827338 490827347
    0x9150309100e030714070803070c0612020901020a0209060406051c02040c1106060906062703010f02070201050d150f1e06030b010e01110304090908043f08090402030c0a 74
    0x101031104440c108100340524102c991644107858003e08402d60030400d032500e4100c244219001402000d088030b544200c0f51034a0403200001d4496640454a0710316488010300e440c1c0203d60031a04164040c101c5903481d07500704040c03000c0c0030f004079804c103544500c0450142c48a000030509500403d681d8016402e03a44100803e851070303a00007504001513041000d9409200041071500118111800c40203503032550049042c90140a942c402c0042e100460752045c0c05601d11001e02c0600190001e00041081e02508005d80c460190f00a0005c0c0c1d081101000510381a444504401044003e42c4006a5110070020107030300b4a801c4034032450100c1030520340741c540540c1c03031000616082c1070600096502200103821118101e851030b0604c00d0a10400e028800c007401110b010b803140481c00c0044088509056903d6004ad0280005485218025058641d81d03011516107003680703d40c0021502c01e407840003a4107444c4d1014211407588007800510b001d551280091446280180781d407079200ca5030b6900003003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 490829838 1250 490828588 490828603
    0x6091e061422090803040b06031c050405010302090a03050102070c090506090708130203160611060c1333080f180d03020c070b1303120201050112031409150309 70
    0x34012910884990229242c10381d0000c07032041c02589803900680070b1030b4100041c1401600050903101c0000801c8200040c0d604a9801020240d0444406c2901c072281455076050313500c00b140c081001444100099032190f0000c0c501d6240103450304180540da40e07070b07032400c0e40c100140884a0140d01041808800e0b0345200c0c03d41d0260f011502c8003220700b0451406003030101d000e4000d45080c1003844600c420343d00c0c20424510b0000004418158255444100410051402e041042c0600400c000f051082c0214800c0e20840707540c441c1400142c6180586d40200c15a04410352a240c0041c442c8000840080d0301071000d20560f42c2e11910506d15020006110f0400014808003a00c90b045c0b5078006000b000258440c5802020b050040c0d071041f54440c890f1030a100380d40000740072800001c11450800718407124104072881003411006607204a84280e09950090140c1e0481032400510b00000c06e00c56451064042018420f0070b1600032960040b0319036202503d0800c404407030000c140406c1c03410070803401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 490831088 1250 490829838 490829849
    0x20f0306040c05010f170c2218230114010908010c030c090e09060606031506190e090906040b0c0903060718080a0c140303090d030c300807020106091e06 67
    0xda110300140c5290962514041c0039076850043c00f007588440f44050030b6054032062551101c0c00003140d51140074000741c5c0544027148201e0782c1440074003441e0001d55030014466004203544010641c1c00d200010a42e816451407081c10803d1060002443ea002031107900b89425447d90041107811206c01c000e41191019405004c0c80600041000141080454044d401035002c0301c61590303a44400c10107180590707140c240680e101c80002080d0001c034410814440d41d0381926189e006403603c03907004005146d102103561001e5900a6000240014582000150301440881c1030b1401c0010183c0071a1802204544400c0030800c41062070200c0007040034900d009003801c0d402032a14141c0c030707943e448252207284100c0700c0d4401c2120200200d66002d1041d58503d9601a00c203005405160600a1401024100685418811100701c100007184250604811607c0001c080301114452800f10f6000e4001803883c0c3c115543e65030003283d18131071400390008203802c20462100c4c280050805004481256208 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 490832338 1250 490831088 490831097
    0x3030f1b06060d05030a0c06060504020d05011a040521150118060f1512090525060201090f0f020d140d0e030102190809012703030b0f0306060409020f0306040c05010f 73
    0x10800103400001b02c40310340b00c007460b050000b21050700e0510b014120642019074028000b20390b0702004038456000c641225242c1800d00c0200b8229000707108544035a00a55401405070ba00f585000072002e10f121142c600f50341c0440360442c500c0540c4130b000c0341080e00a440041071480c1d01c800801c88901549001d4103030001e01c000c0007031070010445145a4101a15024003108540c1d07131039440c0880d40700c030760a00c0e044003d56a01e0001102c410b04000390300c02d42c00300744031200400070425920510800c040154058420100d0307848903203591440080340d0703008070307484035080c080c2c0b0340042c103c40340040c07648480303600a148204424034081c2144a0917114903001ea071062140600350280602403003c0c401c61070a00d403d45894860b0803030b024052100700c002c5460540d07292a0354040644400d411141d000c1d03942044030540c4402000079001c00c2c111107d9040c1d1015020404034a441d81c054a8036510040a4801000c02c14002ca414624115402e59141761001020092940c2100001c0400c144900c1d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 490833588 1250 490832338 490832359
    0x4051f030b0f0a1206200717070309050636011214040807050f010204080c0a05010f170702030c1606020613030f18120b0402040f02040f1403030f1b0606 67
    0x30680c183c145100e4854501d420b903628030107002a40d030001a10301c06c2030f0520503440400e100755880e194818401104d407030f00c441c140c0c1300c0c0d0f8000c01403c1d074043c50391507924003540c4e61801c400c00c0303c0c41c3c0002c14001d8a28200d0460607d000804420710403c020b410046107000c040c1410014005c00000704003000e205040040001395040058140c1c4d9105500219072507d0310342a0802c0c2c0d18120261081d42e8031580700080102d030052300010500100c1c6401c94040034442e464000450b101e60340c121410000c58132140480800c0030311446800da209100d44100d80c2008042801589402081c2c3c000381e01c80d1140b100c040c010300d90b041c48070f254402c134080c01a51113420241c1c1d000b0140d91070140d20004020101c11001d2000c40008410300c02004002c01d040144501810810000a01558203e105510f44051200c07100c055000341d0382140e24107105100d1313051138028500d241c07008140072560b00d40020440c5800d8030f41068054006c83e100c02d6070240301d4940c0f100c02d9519041019140e5840b83c1e0020a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 490834838 1250 490833588 490833619
    0x40b030312040606081906050106030b0607031202091005040e0703050405030a0e0d0b04032f0d03150308040314061b0a0c0f080a020d0201110a0206040f0804051f030b 73
    0x40720080c0e540c07100110340581e5281040002440217401c13a24080c0201440d5116807500c4035001b80b0030b00c0c044c5004201c243d903a000300b82c0441310001c017a150400c1c4280801270110340140801c05c503010b00e803040903107003440300c200040fa08401195400c0c08560013182c140103100e56841e00c550b205800741810021400c2540b10030341d49010300c070304e11001c210910811100e03c2d05d030704501c5801307298004801e58090a1034a4081c0003005407030604136501060001c80040c129407140f04007205c20301c02016010400b040d030030490107072a111400f100c494100702400070005039107900a000442c041c82c1846408054105046d04201c005407044040e590040d26028110b030040e4119078090909013415106511980360031170480100d1000a0320000d00071581c000c081d5004943c1d5007071420a94001c0282680c8841c6001c4203005a00c02c10700180d101c2c10010b400160b5140a5a1043d8060450745090035079810010340f000e12060a81401c00400c040102806078050240c038203000e10172246a8040031840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 490836088 1250 490834838 490834843
    0x90712060e01060c1514010b130f0b07021f0816020115060c02030601060c0305160609140c030706020f0303070509130f0207020108010b0309150601050d020301141002060106080109051806070903060b040b03 90
    0x18090023940302c20000d1605041e04c0e818584038010701400c4a1b0740011691001c0b004d0303458015080503030040b03000c0e820300c0c1c11404c01c0c100106080152a01c608c0c0840d154040c1e02d425180e050036641c1c007590341e02c120922107400d07003e4030a801450132780d0710000f47d42c015105160400c8010f034003d206100c1942c8100e00025000401d48443c0152011440382c00c1105042050180861000c05808a4545a81511491008034607020700200030b07030407108010340e06c01040303039940e030803010f803004541041c00840c14041c450401080c101400810303400c80000c1c1e620042044400d44110040300680c000b507424210358204407501d00404460003850300b9490a002c0c91515900d81d003c00015444070b24000945981c01a0181c0781100c00c002030440d100e40c0c542210780130030400311034030610510008612410140c400281d050580e21507980f50314a0380d1034261480d01614001d8010a0081901e190714002078400b0060319201d02016038418041700e103181085022100c040610174000c9082a45258554400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 490837338 1250 490836088 490836091
    0x12030c030703180b040b090105150612040212160801050c03090a06090816060204050f062701020309040c030f0e192907020609010f0902090712060e01060c1514 70
    0x58240440c43c035042048040002200303110040405003142d040c002481645000c45100b910f01e0b1000b04401d8072aa07000c02000100030100e03681c00725041002c10704005110780b4440e00244050224402107118540207818031284a5a07003100b01d804010030030040a09020b8690040c0c80214990303c0e50038640116a210032550901814440d103680c0800f080210480c110b45c2e0b00e090716004004052010301d070203006903209208051081e0311145d54050340e45800401c45074803c80d00d5920f14600184154800d186c2c41081c1e8005040d0302041c00300c102e46032510302a0815030302071035800240d0750720704030000d5044590b40e0000f10017580c044038001e400185192001403c1e2074010041c860b0005d1040c0c030740b1140e1030001c166008050070400034000d010360002682401071090344009e004502d81c20030440c007103510810740030f54400c040d2000300d80300c2c80c014000701900100303002020030b01c951140802d540d417210070f0780b0420009020f80c0d103a0341844117801c900c505840490400f440000100718822190301710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 490838588 1250 490837338 490837351
    0x708060901061d06010302220b0c0f2e0608100603060c0207050112020c07050604060306080d0c0c12060b3003030c030708060d1203020a030e0d0c03030b0d050f0d0212030c03 76
    0x21f001410300c00040700c2030300c00c0d82030b07603666103044000c0d51303c0314803640d8107402c00e0030400011300c01c403540811410380220300b61080404428001100a507204000d400007030644054a201580d214070128900c17605100e01d00c04010310300310202e4620700d945000e804803000088501c045420602c01030100784c0c2d2100910604040003003002d1388031030340380c05480d081102940c011030340503800041c0000c0c401d4150f00100c04607100d210076104400490002941c0607644c403d0020405c2300404000c2c05044010144103140c603001d2200055980e07102408039116200fa00c0840d42030702020f40140e031a0700d0051580791301904042018500b90304040202ca00c060101a043c5020705c00f041e000644c2c2602d41541090889803c6010380c1c7c00c40c150028090025800043e0441c002402c0541000400300300168540441c0425620024464825107044000b0440190050351200c21507038040701194080041c01c40c1c4010032405071a031640c4104010b881c12a02c40000c00030b80f03a040c010021401c4001055070f91043c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 490839838 1250 490838588 490838591
    0x30307200f0a0e07080c07030c06020f0d09060510080a0203033709090b0d0312050403031806140906010501020601151403090607020c03030414210708060901061d060103 74
    0x8050000700c80d5401901156007121031500e000540c1d120614945000780e00544444865031103002480030184143d00700640030801012141c400102c161380244040144080c0280c00d280b4180f600809480c500c050a4414076115001d0041c0c90300d07020a10310040c03c509004201368582503020903260f02544155043c40991045841c076510b074282000020340040340d2001003c51605107015090350864001e580071540f42541000b0356040070319140b0310079505529003011544600003850081c0c60000c108a040513110f88150b50420041101c8088103442084041101070301610740e04112000100401c4060703000000400040c2d8021400ea415503007601249015030070b151030f0580380025200c0c11048844000010014111004078100c1d01a0140c2ea007954014105002055501e00075401a4541c80c8500751801c0703064585200140485070040d10b280966a5031a00e00320300b0700d13046a100000f40e410070340400081107428882c9001070b1800d03400009901c1c081c20124100c0f004018004d40c10705 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 490841088 1250 490839838 490839893
    0xf12090204020f0705210304020d11040b040f06080114130b091203010905180a050606010302070623041703070806010e13060b0406020706050c030d0c1101060b18030307 74
    0x107480c0c540440d08541d0b24406551394905851500a43e03d540d000c483e565050038515004410007070540407039002c1e58004103044110102611074040d001c085040040c1e200340c0c4c40c51041680d480d40d01030f0b6280300000201c0000c3c218070f000215400e5402d41c501506044c10803000300000e003020009041001a000148030301a41d5400004c40c2c03034140350315a0442002c2c00030000141d407140b540c00051260701540d00c101d100c07001e4518441e070f4521442e440140036030003500010348107520a40c080c0014a024030000b040e0f0001e2444500642c401c0604910100384100d17041005010600c00c0c460382e180329070a455851031400040042c040d40014040c83d04008210b0640640344c0c2d1071005030324191a9071171040152643d96055960541c1c0a4410038000d4082c0b28800948207020b9002d80e0601d00012001e1840c15218000200060606250344400e1080fa01d0340e802a0880034800c4002030714501c80c20301e9031100c0301d80101c20590000e41c107041c4251b00400c03600d4001502809400d00b10300421b4048202c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 490842338 1250 490841088 490841093
    0x70314041217040503250803040c141906030e0a060504150c11060a0c11191704050109050d03030608030f031b160f111017011205120d0212090a0203010b010f1209 71
    0x140e020301d10300605039007801301c00d000032b00032000c082c00100d0300502406200c03002401c0901400020880c48241d01180b842c408201c5640a030b00b00640920880d400d03038002c01401d946140c200d039025501640c448207480e1a003008050b1a10410141d142c060400440c4950114035240e507480d4020220081d9a4803140061260b90141080195401302982038554001d011401044031400703020003a511515041884030001e0a07083c101d8080c0c80b010786d106880c180c145010f100510091250803420140d0f200400104440c00f131019044080c118a01c990f07407400c3c005920401e0221858000c0b0f11400b080040b880110880d10800d03d00c5030b441070710302091540e28180707032030030154250a0680001027800c110075040d610604240b010b10100481c101c050741c9a80e00c024190010003030003881ca40c02284038201000410028003506510f01601618060783d5503070301e203c601000d490350b0f01c296000406883c1149028012000042428a041c84840c50420350007040d08124840803145030350386071510b409 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 490843588 1250 490842338 490842397
    0x10509010e0a1a0a080a12081308070f0b0403091e061205130b16112e200301081e1207020105190503090d0809030909070314041217040503 61
    0x9280720004d000d604500d03520300d420354480f142041c00b1110350161071580f9403082d001e00c2001e03010f40c034454400302c10301c0565611842c50740d100d80c0c1c0030741e4901140364003030000426905519108a02ca580c840c0c000d180350084007030701040380008100041701003000a0290550044215540203800e00c5d000c150390321800c4a041c9122002000506400c2c141c50400c21f20f5082c2c1482203800e4000e0382e4540c10308041d901d012a80740c0c03a1a0305d1003220907605100400d110507c02c12220380308464090300151611041804050078207604964400c81440400100400344092180c00e003014200b506a0b1401c0318030b110807685030070701d080350811126808a2840156403042d0151124040240400c2c40320780c0740302d100a00960001c907440540c51140c3e4903480300740c03882030042d6070059401c02c1c021030900c0103900070864480e07802880c0804160b42c840b0000f44008403518058011030060b000c580b01c000c00c4500003401c0200701500352800714080d2007400700003000002143c5511481d800c00620009000840300c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 490844838 1250 490843588 490843631
    0x606022e091a10050a0b16060c050c0604050d03050a050702120f0408030409020712020307080403030309150203070806210c09040302030c120408010b101706060405041103040209010509010e0a 84
    0x1000c200060100300e0f101014000c580155034040b00c48100c003d554032040109403241c00d203ca642000300081650014500390030241d40762050f410168200040c03901030350b1410008403402c2e14250b01901c0d101c01081c0d0181710f46178001c096404148020301d001034020b541c40c0840c002000040f400010b403001403d55210503540600017440070703690f5481c6d030b9443d41000f94015440944120003840b51503091107000104450f10307141e00c041c989080c140b542e14103400a0021007070a813000454240e107203000e00131500c0203520034142070319406858203203402071024141ca942840307100d0700d00c1c040300905290400541003000c90801c4170b901e016640c03189012811401b0b401d880c0c005c1842681c20f074103030348401036000c1e0083d518904001c21101d01c0c140304000c81a24207000303d80110740b550512104221140c1c0005030b00003005803d940c5856030303480c045021260b66040100880402205101c210305e00305490b540184000c85404101c0d50414444120420000d0100b500c007a50303801c0301c500c6c9010801c014a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 490846088 1250 490844838 490844873
    0x21813150303170606030714030403051201080d1e020304170a0203070f03030f05040b030604020c0c0603150415060203030610090f0f0602190507120809130606022e09 73
    0xd01425941c0d16001c3d000ca0001e107080303511200c804000036210b0404200b5284900c2e002d550b0136001b09607000c039140840d40040c0c02903040200c100194110100c3d0130080074001c18494000340b001414010303000b05400c0d0241e0b10329044400810445181d135500100b0750307058070301c0c01903428050213404c1920380c81c0104840d0001d400d40217940d800104001c000c3c2c454070031a8001d03101d0f0050400a200115010b11950258403584c0106202291503820150701070891070300c1c00d208503424a580c10000841c2038104580c40700354031010380d522140509241c000e030750800520305201c540e150f04100c0c000e51a404014021405044c08901002000d8030071040d001c0107100500d60a80740e20b4694007004510041030048c000540725040322000282421040a81526006005040c045043c4132501c0c00f40940d032141a9503545060128041e244d0710b4000700205e00034405000156585019006810800d001c83d00808a02041d0600e4a55015200c482030403c881ca40c4001401c20880c81d12110791520100c12 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 490847338 1250 490846088 490846121
    0x130c0801141f1e020105090a17070b091f0509070e100f14040608160501140f0c0106030309050102070b070609060219090801050c2b0b0607030201050105090a021813 72
    0x1c102e09190007a4941d8007000400320005400350a500059007a12403d840300f10450703203c009003501042e52801403000071843e0b020340314505100d80c0c41d49003d0b00c1d81516071800c2504880e1508240c140c1c203c10304031142141d0705051200e3f10742089540e82741d00712442002c0080c41907031700152700200d103220b0620160400180d0103071419141d4040c5001c143d1110003040c001ca00c3d0149c0442d01400001c0e4a007103c184d4a0300c09802e103400d00d4011038a00c5122080844210010310030104030300301c044054012041e4000000422074590304000f040a24254071080c10342d0000031090241c1d520a4003180d21458100901096544d000c2c41d00d0802403062091503403244038604001d44109501141600844070480000d000b0364942c008400c10030310559070301c0a0400048480c19520b04600f1034070754003841940000095400440c40451075544c0011000c80041c5d5442006000c60b2624040c03043e0001e0303103800d003141880c0c0007030410800c5000d100e07600d40c460180079214814240c1a5001400c0c0f18405020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 490848588 1250 490847338 490847389
    0x7080a06090201080f0108060613021902100501170a080f120a0e1509030901110f03030c190c03050412051f020705060f0717040314070c05130c080114 66
    0x245038000304078507002240040c0b030b001d011846600710303002d402d810703600e046000d0003441d1100c81c10401291010020894116004c0c00702c000c4d580c40030f490252568442c0e401070029090110020320441d034050300240c04500c03049041050407500020408229980310074520343d12030351146418030310300820305440381c120300700c0c42009580c6449030441000e0050ba0804c0360b502c001180788608040300c084842484680c01440106041d40c42402d24103181070512054a00c140c0411036060b0840d80202c03040c0440e081e0004039286c1c100c56490f208010000c007840c0c0307440361408503a0020040c2c0f1031849030000e07803418089410b0a0007014062003215203001802d0b0440c99251540d04800394001c1003051ba00b030b000784030015a44072441e008080c07080d03407d9500c00e844c0c4400800f82d5000a84081d20940820402e4404544047c03041030040021600603c4001410361508040011a0b0860200351000f641803081255400c1d40004d1660b044d286a070754030313040c0100a9000308003807001400e50088407d50302c0d803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 490849838 1250 490848588 490848593
    0x130801020f0c150103030503060d020f04050106030e1b0102151503010e0106060f03050c09060a090e0f060f241608040b090f0604030c050103020d0f1410050103090c0e040507080a 78
    0x200140110700c030410554101c0c00d02c41c01e2100781c0310f40901c005804507608000203003e40ca8503c1c100b1300414401010200b0401050740460200c80098000e44007090b170310947c030075440714104a001c08001c1809a040300340c40356440000d448000549045031441d2a6a0108410f82881c00140d102c2000180080008400b800c2e5014040c02c094490000420b0007803c42c40c040701d00c80c0c0141441440d0002180c2e10b410980c10034809250711040803c020001e01c20300200300c031a1407141460145040a00c034205e40d00b0718004102c00444240c4095129038038241070710b954604514288540040458240350701c1c0c5d010040c145810320070a84005020000c0000c000c90806844c8026001c0000207613045c00640703220a0a0262500ca10300010b84501c0305c4040400456200e90014200c00c1a0307c580031070003030b03007041082c4107441c1814002000141d10008010300c0003246044580140024078081c00000c0842d16094408043d6000d40d80c41007049900090900400b001050001c0180c58100e400300d58050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 490851088 1250 490849838 490849867
    0xd06050f0d050703110d2a0b040608013b0103051204081e1606032304020d080c031c1e111210031202031210050a270204170105160f0513080102 63
    0x1000d21f06284003d0401c049640302e40f0100fa2400c0c0d0345180c943c43c902d42d003007120b00c20018a00442c424000423440c84080d040303d484008000c108407031081017021a5046103401d5090400d90300c40d1010046c0184402c1140010018204c009845901a800c14504101140c9402c0000185080d14800c0141070000f9040c2d50591005d2107000440c24003d074040003582035560190000d442c06580031a4040600c000b05180d88000c064404010044a29251403030881031142e82c5c48841180c0c0030380d038a0281c54004604a201c16040b50b4280000f04500d00d59030f141d1040c180200c403014008080c3c1040015407000300ca04048028603080f242c01010300b4200a0001d58130b40c001c1005c894042210030100f41d000400c065200280c920092400d80002e0400d0043c0c44446a507400782601500086c41883e010880c600c000c1000e8000d0300044524402a036035101e0070755402500d040030b003405208034001c201d5400845650a0001c902d80142d807505103d01490546407580c101e00b0407540300050940104041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 490852338 1250 490851088 490851143
    0x20a020a0606050f0108071404080a03030b18060a090e0102040504020f09010f090803030c180a080607020c0609061207170a1a0301020a02120904110d06050f0d050703110d 75
    0xa807006011003901c400a0044868004881901003040301010401d50b81c00740110140c9042003480b00d50400380c0c0d03070811314508950310310150f000c81d84d80c049400380d138105130012240d844000030301a111410300750045800741080380315a071880d541d200c000700300d8108290101c0d0014100100195107541d07a0400c91410740d4444030919011034481d050103140c2d9800740520344101c40050317015506503a02e01414600c60790203202ca4500c10001c2c2001c000c4a0f0355000c0301040507180203402001545005800a85081014142c0c1485a94144020681907507010100c800c4000d0042c07e40103280c03a111400d451940760076070f01d81410481c41c4c04000000c1001d50044000c0084060400d41d201c002c20181403c07071140a960381c005030810b07200030b0340503026075004000d1140040c000080302103080c41d410a540d00072405c80403059031585800c000c64a01951800d50720309003101c24000329212590348660b507110510000b005803140781580000380e42c0788084012800e80148140b0f0f207010031040100400d044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 490853588 1250 490852338 490852343
    0x3050304030b011401090e040602030402150309070f0906240c0c08101b0e0f01050c0703080408010e010c12180c030b0a0f180f0f0501020408030304140d0504050d02030c04020a020a 79
    0x1030035801040a61044e106d8500f02c034400340c0c1c800c8090f2601c0e08c800000c0d520041042e40c101c00780005800314069043d0080d803040d840c5401510703041c1d003041940c84103070002c1d0b84421111800d0000921481c003070100b00400c00381c6118809801101d80b008143c50010446001030010030f0000000260000046520046842c40c0002000b96192101d4402100000164010005810001000300c03d0409544003441c20005043c40c900384040c49680a143c400b0a4004540040340850108110f400901030b08180c07140c0d80000b408504084840204140c10041c80050303402d45407609010520384036001f40c030802c0d400c000c02c0b04107aa281d0800845c00d807000c1c2c0d8214600d070b03c2d1840b04816005030344a101c800e04250030800032680360303540302c1420007420030100b521124202d000700c200203030702403000740003c0004502840d00c9141504000c2c1401c2c0b11038030f0b0f080300c41d00506490010107900008a800f070f100201c500580100d06070010034508248503a403160410310000d808031040e074000460803030151 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 490854838 1250 490853588 490853609
    0xc0611030907031a0f180c1201140f011203080c09060a030b0910030b06011409030607170c0c0c220504052a030a170706061d01061e03020a020703050304030b01 70
    0x802c007094014403554100c2c1d034400200c2518003c10b440860079001526a81e86c96011034210110001c0015012003003144240c2031a992960710314040404191050390142d24414400b10707039890503003041070050507140010f08015120000440140c003c00c240d50141501810440c5c03a071072613000180080c42d24400d101d11a40318100050302a818043d04182542c3d231007100301c0050f449150054541c40c1c807048240b001d0810038000000c142d01c0800080b40319680c60381c0c0744001c0c80792141011100d103c0240c840140c040c1c080144860b04031300012030380480741c42601c104403102e4040d5200700e5074018680380b0244281c18030003804140540041da0b403980d41100c0d0034010801003c41451420107003140c3e05150550081020f030740c08078078545064040d118404603003501d8580c0300e94585040b1109078000e49000e17601e0803109000c00c1e00705482c03d0301402060501e144d200e2908003103080d8401860010404060b00020b40e5032034030740301b40140401107600504580d2030701e84074a0041110207090003080c1010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 490856088 1250 490854838 490854863
    0x3050304121e0c05060904061a0703031b0f0e010c150b011227140f030c58020106140301140406050603160608061002011b0c061103090703 61
    0x804080021116612841c01c0f01c1c15440c11007489156080040515401039480d00c0c006061190152040162a00d030407516030342e000d551034042c04031000c10382c0c400c6a035084490304030001c6801140c0c0021303056407400e118555407400f9004850003104420000c000c0244000c900c9108500f40d0080c0713054120903211483c0d0880c651203400c04982c0c2c6525074900d200c000400070a20f0b07150000e2040c4140307003e40c451001121201400305d01d0001400f503558416403002848500e6590309000c244501c0e21420340948035102c3d1004042039070041130180400d00e15120b200c030714440304001b5035010003103d04200c030021594102c0c0083d000348078500c1185d0340301003080503013000c92506100e41c0050f80c0c6da08014208a45458490798001c017401818150540308803078980d5810302ca80d880c10300084ca07030382d41d60080e0b903d0b00b10288500c01c119821031505580c185150400c201014041d0f01894000a103040c0907007100302c0c102100a80310040c581004403400109104002c1c0011841c00b095a004441d5a0002c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 490857338 1250 490856088 490856123
    0x6090f09050705120706120204081219080408040b030a150f0503120406141c05010e0a0b030a0c140d060e030a26130302010f06062309060304030e0a0305030412 70
    0x403109101c03441c4c042e41d0031004083c031140340111040c412501c0302d40c00040c145509c0f40000c501d0244010800f801503c0302056241e101e0001a0122407a13803c180303000911b0381810741c0c0d03100c0103006501039810904008800a01640710a07800444a9014056104031007540c819080191301d82ca40640c0d8040d000b0005182955036000080b1411504582e44641000000c0c0100c50081d80027201c241002c1c2041c0b90401d2206206c81c020317240a820950302d500307030360308122008404840540222900907007010400714049a9104441402c4484203645a400c401d0054005000c0142c840700003072080303103003024000d1420710010180198030090380720242190000b94082a0b41000350010120805036040000c10441d13034849000100b41c441e00002c2481542c0703802000c152681500403400081220280d50002e04821400c50180500e03d1141841c6c01048000b10307805101c000e102030240b26030044600300644400040400458000040c1ca849a0f00d0300100f051896141c074054a801d08428007180340c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 490858588 1250 490857338 490857349
    0x70524061e10080903040902040b0a08090d0e10030b090a0e0c030615100504030818010e042c070f0303020109060b0f0120070b070f050f01021c020c0106090f09050705 73
    0x384540c000700440d00c0400b002c0011242094000c0180c08540418400000c502100c1e0020740040d0103410407180e11580325075001840c404000f0f0032240f0076482107191601c0c0c1c0350406a209a005403c1e2458002d803414080c3c15009860500403035504620008100008920343d540007980d00310307400f429600da418850042503038444080c0d961402e15800d07102d40030414038019940449507002810443c7c00e0a0fa2a15105901d802c003a000901e00303407404450420540e48001002910882100c0411580e2215101d0800c0025207440e59400d4544448600c09080e5040185100070403d444410303998030f499180081c00f03400000e03412034a950910480545070303e800305c04016a030b030040e928164004021004500c1941906003049003501078000e0204440c1c242600400c9103034041e51076500c0180003480c1c003074500302801400713101c113910600c584a94025840540351560442400140e29000d04082076030041100b6404080c680c0e140c28014280c11420350842607100340510242d403000b03079496081c841c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 490859838 1250 490858588 490858639
    0x180305030324060a03050402033409050c090d050307050d0c110402190e0409051c020618072903011202040b040b22180b01030c08160b07052406 63
    0x250300041c00e004d83c0210a2190b40880c0d40103000504451643c2180308400d5401d5500c80c55102c3d1100d003140c0700130f1a50506031903020040c10101d100704000d1a005440401074081d45816500c13070352891209205100082040e6501301d6084029100c1c0b51503001c3d0098806003c0d0300c0f040b1103201d5400b00b04800c0f03140501c03c2e214020185250300044900c094402c603a4804000c609030303405a03480d1070b1140840c8003003100d11a08840d030800340e030700c141d001c0001038640607004000411056280c01060021800403580401b01c0b44140203004401003904500d180801c40c4c0040850100804000003e2000c020245080d103030b4001c2d9410090980c0d0102488107443c2d8801d101c2e50825580c035000302c900c110384d810100403405c441c08001003400000f0a407407840001a001034503001007840040c000d100d00310b8454002031101c3c10080501c4503000003210f0400c440342c400c0140001c8003250b2242804024007002080d8017841c19004d040282c3c2c0300c0c5040c0ba003401905d81070302548203801444480045995887d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 490861088 1250 490859838 490859911
    0x6090a0506011a0c0a030518040504021011121602180702150606070b0a02120123101101021c060501020325030c050a0f021c02100305071803050303 65
    0x3001c0d180c3c2000d040e808075140f02c0c0100140042d003000031840703c2000384171451069100790f9929a80360310940e050b12806005018241c41075180c0700c18840140d85401e41c07400d904000d4103000c0942d000036002c4c1130900303090140200022200242c441845110304a040fa20b044c4200e503001803840c0c4440c1c3c0f21942070811039200c03015920100c40b628455801213002540020020b11345803502101380d48a0700300078015604103207916004541c0b44080b00c6001c4e00d00e400340144401102c0c618040c072108000014400c10028015003844062510f901d20446456940c414100300039035459003000380011a401d0320704108406545800c0010840398030100486109840585054083d01c0b0349850b010002101007804409100c06036030040c000502c107006003440c0c1070140036180300340300882c0103000400c003200d1070750a9204a00f1406c0e000584d524404e1a80709812407400003080c2e519610180e6912580801504200114100003c20440c2c0040190310591019015031801d481524004100d8052400d48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 490862338 1250 490861088 490861093
    0x30201021c020312100504020d150e160e01180602060f180d03020c0102070b0403110f0601030b150102010605030708012414220f0203071d0306180319050c06090a05 72
    0x21844030240c1d10001e810170f000d4000701002039030302c00002c0c04a0b8448a80c8035003880e141e25030703408255984904a0000c04890018203481d1410300071407185200803541c5c80e8140100c801c01d08000364030448075000f00c40241040c540000b602c6580c040c3d0387d500215225000b0406070130000e2803012080a800a0a11380113004107040d031540102600039420000007c503040d13500307124410125844ca0880c0780102e0094840da80180980360515040a0800045100c09d0f4000801080001c2c0303a80110350b4003031400d08171200103604800040380075110a40c0120350510600c1000b1503500e5041d40403045c0501e40c0014000c800303400011100302c0c0e14003441042c903507440007019000f050a002000714011075441d11107415074003044002d54121350041009000d029404170400c403000d9002030f101042241d075a8120050b00300c02800290f40d592000340380000c52441902d6400f03201d94100b09580f0444015603031541040d004400003001178002c0c0d81e10f10f265214007004546a1340340822080c10081e0400c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 490863588 1250 490862338 490862347
    0x20d090b06030d1e12140c0304020a080d020d0c050a05060a0b0f030a020a03030f02100213061407020a17011404050604261e04090c0908060703060b0d090201180609030201021c0203 79
    0x9056030640140f402d005005d90f03c1e0701101410f911101c07040c1f4801c042d01d0150903142d0905d03005100d00702031103401035500f41d8400f401c21954540c0000b00d2800c14409840d196420880d28546641414081500180103120b02d0b018019185005d4200368041036041e02c1c0d0024500c09501095503c030f110541c0a9004481354409001091044092140c95111401282e012030503003070700d98040f030344420196241d03c2584041404040c0d845000141048040c0c155039080514503000201100b283d441070401070104401d800103403401c00e41080d035011040201c064518a050304105841d00d00c1220120b0300c1c0d84c03140c030040c2c501d089190f982e1340c4450095064141401b0200e0300011201003d203071b06070142c140038003002650081d50301507900203202030340d5101c1c086440c00840500d8600e014010a050606150050088031901d0080d43e040d04415000070031408068001a9a04002101085c0c100c042610303002c50069080303503a18084034800c6c1d0854a460010305c0007030f100f540c156400c07000160020003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 490864838 1250 490863588 490863647
    0xf03120f060f180204050d120201050705310f0603020903100903020a08070201031d010e0c011d0603190e030c0607052502030705121006080708120d020d090b06030d 72
    0x10310f000070f0380d04a0038018070b07042d1602e00154000c162035070304aa01f0880400e881c11407036428002e05400403042d08009081800c0e620690f0300d210545920201c030008111090461001c2811180b8000d00404008101043d15004010082d40c0031303401e90307130092194a40058107040e551280f000301d6038050303020300f0090f825692142025404104168105038940e441e1071110004004c00401d01c0c601c2100004503d9600b482c000d08042074040035505201038507603c5841001039820340d8441e004111740d0240d90b60b070741f0707103484114aa054180c04a0030746454100254160300200030300c00c0d210300e00110350465a62001c100d4a078810740100c00c000b48941040843c80703032a425600c0c0c207510300c0101903441c516103850100b00c0c41000355001c640a035100c4803005440300340c18402c503806802c50002074511242000202c030703547c41d00300071900d000c800700081c440c561840300d03419207008501c2c0b88001d01140c6080d003040700121505031100c80c030034019190750f90042e6009900346046000b2081c0b801c40e031000b250 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 490866088 1250 490864838 490864859
    0x10b0f0303121803120702100902010f050a02152a07380c030109060e01080a0b0601020f1006030303290603090f01020423030f0c06160f03120f060f 65
    0x584481c0c0e581c80c0d8050303243c940d00801e0026201e0058140382c240381c20b2408260080c41c0441090108042038603282c240c81c00f603607001c0340300b01e0381c20300714200140c0e0740201d80c108a1a00d11807000240082d1056030a001d285502c404c040d44180c410304a04003c845442a00706055114200000f004071400c000c0404d204c2d64a02d43d80d0400180c145010b0000074443d2500080b0320314202d03a10003c400d000001840a09007921035000904054a4010303040d40c1000345407540c811032910050310301c1c1c100340c1c00640d850303208206207090300ca5118107441c00a400c608100f000752105000072400f29050107044442d0103a0951000b850900301b44032030a10040490a00c05a5400a80b0044450040c440000e10700d5100b40000c2005011002c08200c03d051200810064034003d00d80a6100350404c080000d007002000940014240045500940d02c0e45401030b10440300c05c040b00010307c0f43d02001011418190850300426181e44805070034060085c8000740e15049981c9801020510f9131805001d00c140e1400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 490867338 1250 490866088 490866091
    0x10b121b03150d02030d0e030d050406050d0f0902030a080d06060e01050a23070b061005030606041502031207030f05010f271d0708010c0c0f151409030705010b0f030312 74
    0x3d8403225403602ca40c0c01180c1045c070302d02e030100041002c10160603050300f0100f00c1e5040c0c00c175040c030380305060504044c0020b0030f0784144284c0b017070a136071500e52584007060907034098201c02d64000d0072580081c502e441c0001300d0b81c0040c014084041d01d4802c0006103c1e0007501c8064036580140d51b0300d45402040d4000ba200e45e0124882080c160302c4030764400c80c04079000b40c020701405000b2815804c0714030f01602040074500c60110394a04021080c400d10205445640c01d0707805a90100f005e00681070042a4120b10b9070083e083c009004041020900404a0701035015414088200320144075a030307284c8489000c00100352103003ca40e00d881500b003040001d00315981c1000c0000103003012650444c1c0403180090340090745001e820316001a0404c10000d5801d2040207441d041501317001941805ea900c54800d00301c10801b010304400d50012848075400b071075900800305100c0d007400c0d21042d4280b15404641da40c10501d0300721425880c14000c085c407072510300c0580c401b9250040056103005601032032410600030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 490868588 1250 490867338 490867381
    0x709150902130f060504030b06030706090b071e03032a08151f030506010206010614070f020102010b030a2109210311100c0912030801210b010b121b03 66
    0x1940702c001c0f07007669410160030010718544c0e41d403a40f92800c50a088010b440040c00c068425800001c2c10807416401c1040c4d47c00304c404200c105521524141000700441180260001800300c1180d502d408040e01540400714038505819100d600801c40182903000310340310052580480c0c10780c0e001401c0a0000905290000009400700d400d551225080c00000c100f8030b8240c0c00443e80303900c00c000c140c1d641041050300501d020f15107400e0302e500480300701850b481b401102920a1030b04d031585a0640e4003d4000141d90b250280484022075550706100000b01e10307880248400010614030500b426100305030502c203607140c3c10003039170160144155000b591a110b00c411000c2c805607803031800d0200000c1c014088140c0308643e0200d0400244940101001f880342c0110001849540300000829440103003641900c0740c101c100300003413031602581090003100c0b0b880200403849603070010a02c1c1c44043e01903c0034048a0041d06a640c40c2c0b02c1d06248030460446a16821000074000140b60102c581c12042c1500d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 490869838 1250 490868588 490868617
    0xa0b03030702030a080310080307061b140a180e09060103020f010e0105030a0c0e0904110a050a142b05100e06040317040201030f020c210405130b03030c0a140709150902 74
    0x55488c070416003150071041c7c05881c0156504035110001614601c11381c000111351038850100320f109520101b6a000344607001d020041c1b00c550010303003e07554041c13507005400d05112900c40c62501060555079140240812070017980702c280102e50650045100013070201050312914110350b1003410700e10080c8610300101e010070104150203002a150111040c2c0114080c25103501d5125107030342403100b80076031544100e018101c80041001003034210691526100c40031101d1041001907180c140072034020f00d00084014102d5800b0301d508110f0000f5190700d0a03c4190003d100034050048030546411007150060042441c10100f01012160307440560b5020340305041c002107a10742c80884100300e030031449411075030b6481040c0481d280c120f0180c0a011001c00b002c8002d19140c10400882c1600303025101805002e5240c00e0001c1c070683c0c050050751400d40b2043c04407002400c50781040700b4000e0441004e03040c83c3c0502080814040124064542c641010788052108140342064490003544071441880051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 490871088 1250 490869838 490869871
    0x60f300b040b07030c020706171f0b040602120403020303030601110109060219080604050403021e01090204090812090105010e070e010e0307171501180c0203071a0a0b03030702030a0803 81
    0xaa0182549070269000c1c00080b591450000e001404a0f10981c005109540c800305040041c035030700c26026100301400c0e1203c5080c0752505a401134445000c02c11a0090641848000c69a038038214050f0040303554a6007125032101001c0c203a10700b0f41c4154003000c0e4041d0070810005404e940901074100801c400e203000080c045240e504c03601d0407a00580683c107228148000342460940d40110031036040601100c00300410b0909a4010355240c44aa20004180861112080e0707040790071341c00000001d40140087c84005001e107400051a400380c40c4c406c202c1d071a03880200d240414148501c5068400e507440858032130301c40340c4050f03400f10144c2030303042e042100c0308819002545061042600402074405c0e680c00300c04044d6070050405104900c4c11300c40d45c0080d401000b03010380022446859003514080001d2000640104074198440d44201400721221030500d9949825801d03601071003840d2038001007040c8001c00e42055143e101b03041010354940d1298503800045480c540046400034206505034161 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 490872338 1250 490871088 490871093
    0x180206040306021309020d0c11010c08061504030209010e060411040e01030b040821060103050a090b06060a05071403030403020c01080105011205060616060209030c0f0a1e0b0309010c03060f30 84
    0x6a9000802c40c00b8070230348803010010915000a0700c00c958140c0140240040000060b00030240003004000e18881c405071801100c00c50002c2d400c0301c0c0a5034014208402d03d40c0c44d1002c0f41300c07035001a10418061403034103140d209a008000151b6007500c80200404c0066461611507103509400a0010b844003402040b207882d4000110041009045400383c0c842c01e1498004005801c44800500140388141090500d00006440d4a03282d45c0c4008100c40d00c0e070700c0c1e0412000403100340c003030528000c25482d10380c0c090f04a0401c0c00406140705510030340c21601280904001140c80d40d40030711605000c940000c0c0800c007040c000e84c100e82e0740401c0146c1103604000d2040a0070341c0c400c4000406940d004c0c1c1c0001d03041c455060030f001000100c40c003079074010082d408120208060074143d1145401e4403e0001419198962854040005108200c4c001b0f45900f8402015402060921925000309240c00c10021300e0b01503103a001011200000d038104c0d4075000006074110004640c040c00202c007003007050540e00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 490873588 1250 490872338 490872341
    0x14040504020d0c030605040506031515030f07140427050f25090504020a1208040f0f090e010b010e24030a0204050a06050c0d03020a260703180206040306021309 70
    0x5402000a0b8042420702c01d410010303086032001d81221703010303506100400c00b240d10300090604803120036401500c82559020b200d43c0410f4581051164035020f88031501d500e030f4000048020030341342400d501001c2c81d601d0908000c104c1350f00b0f00115041d20034816000014503103000a040449006202741d03030b03800306840307030003824902102004030301e2a6017071001c4181c2000500101c0007600d4101004c1120341416000141154690b2164006110010031a03104001140c019a0300500090a41c5042183c03111542c20039101107028400c031041c03806a00f110700900c1401034442c2400113171644400c005038a8184040d141c0382070000c10851030220750289000c9151030086205010240e40140c40e14205020441440c0550740f143c002c000040c010210040b070045050780e864201402d0050b60341d98185010b80300c920351040d0326200a8a4040b036458640300100100d44034807510742e010007070050801035507152101400b40194004000b80014000560b6913030040101c40300181030040041e98490750b420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 490874838 1250 490873588 490873597
    0x90f06180f080c07060203070b0115090f120b13210306031703010519080304052106091e01060621021324050909040233040f06110a031404050402 64
    0x481002001803c80d1903580c080c442080a418240301441c035000c1280c035020a0b848042c01164840d03185050414000c0d4001c65520b8002d00e60b5806d00880903980304040c161001c070b0500d0a82e40300480100107452001d0104000310803d50040c00201c0d2032401442c03c154a10011801c038052656804001c00130448040c100c001010b20380452079a05d40c1031409100a501c1c2c8030008540b9490441c0081c0b211034004419202502e1083d5030265010b8040b002004070040c00048603c1c00e80601014012012404140401c0646015060884590130922541c0c225103907403084030006000800c200c4400701079510b103011441d041240243c20100200b41e030420286107584000315140240b005850b0a03c1300c080d1081a0740010b040c00350400a0401c04154101c41c0103000a2107511591607136000c1030303000f00d8a0242500704031741d490900607a08144c115550721500800410103010342000880500c01d54a07050150000300c064080040955001e54901c1440b1b5030b00042c4640c14400821140c89a10142 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 490876088 1250 490874838 490874843
    0x50c03040806100f030b0f060609060c0a0c150e01030510030c170d020c0108130c090c032403030c1e05062d07022e2d090f06180f 57
    0xb0031190a10a19894501c403280c0d010080c1c1c903503135400400100320481c0302141d01110148058000d9540d0000041032442a044403562100000c9611002d010700007a854582d54440d000807034100d070320b888903003d078103c08030043c2000480c0c10f1094050765120343c1145411107860b111710381c400351b129a0b03140301083c0d142c3c12510443ea8000e0b004c101540c0c04008100c5000c2c014005001407000706800201603000041202040c0148521038004200c0f1041c0560000d2048060030032400800080040c0548203651078074507040308503144030000300c0602003003074201c2c2d61584911803a42c4445c0d0724100500c041c0d04030f171a14201c3d608009404187c05000140c4110180484415014003003c0500c114100d550001219061203e0170003007444e400059860510500e8102071518132481c02d20214102291190600e0180c00d28440a080c02075041c510f0100c00104a03032a070240d44d4400d03410381261001a009443c50701400c0d01e0300b0101d403466005054200c612448800e4207000d94403400c16640900404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 490877338 1250 490876088 490876093
    0x20d0501020a08240f0906030a120e01030606050f09040504020d15021908100902221508131e080c190c05030f1c03061d06010e0d02031507050c030408 66
    0xc01000c0081e004811301840308000c403041201c104940850707200080050280c2c025050603021034900d9030b0400104c808250310112502c070841c401540203000303c03500c141450102e41480f03004202c150040054600b001c14421149049c030b54907100b048003070305000d0302c10b030b1f0003003400c4481d0360110b034207200d81a80042d106130f001b698400132501c04039904042544100208040b107002d00115404080c0b6441c04c0f16800c0d5805601c503001d81340d90720400d080040e46d415480000400000c3d100c941d98a226a4499a80d1260201e650700d5901c071804c41400c8600003400d40210750290009401d0850229540d107004030225414050f440f9403151604014840180c40014120060300070480c92070203160250505030040c2641c0f00181e8202580d85050020100ba4424240e00d0b01d41643d10942c8044020081c1400e05803070f50f909140414540007080d510300d0300180359103050409608140320684105540640244500031282411034108200600700e8010810304024150f4548810070280014100d103001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 490878588 1250 490877338 490877341
    0x204050f0406080616050d060806060a0b2521050304060506040c0518121501090f1a0402130317181203030402090c0408100b0f010327020d0501020a08 66
    0x4001044040c195898420360504205000720000841d11a4100c9100c1e5404070001042607015a6075004070300030103c0552034404000b480c01d000103203260003044c0541d04942d8264894000349031607c01c0784025000c031074801c0540300d4094600c031040307849a8010121955a070013103890011092444407061400194007100380028001c0d90303c13505030882401c0b101000055400d400c0640503000310814540845a0030510001035111a00d403481c1507142c0b502503602d441500600c8521841080c001d8180c0c0030b140c0381c0881c1e46540984510701c840c42007445070044c03e0218504100c003039400800004a0b409003654004000f4407076041c007031205085d03905041e4881c180180303801e1401c2c000c1e8112500c42c1e45114a4021400d1000c03003103982103901078807858126038444100000600c00c66200d048d039881783c14400044e0b02c2895124029488040364031a2409003650011810f4540018070089202000303c14050f1640d102000025024406482400d809203541c58007400c82e00683c4011000c5100e503070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 490879838 1250 490878588 490878599
    0xc0f3f0221070e0d020f060f0d050a02030f130206030a020703110a08040810060f03020f0607050d030903200d030e16080607090f030c0302061e0a02011b211515030204 73
    0xc0e840620b4a80596034820013140680000d9034a6040109242c02400d0008d103444001c2042000c903004c0000540007404181440a8000025801160481c1030400c000000c110100194030f4103c55064005080908580f01e00d00c0c6600258450742c001c509022444940103c003042c2840340c00504d500800102e5200c0c0d1503c10703a241031000b40b210700c821440c5000300501440c0920401c001c02da98040d04c3c03402903080005c0c0804c22138840c4040c00b6084e4461000d1700104ca60f41900b012284600c00e56404880011085840d045501d41c40301000490304916480040301e842907200c0c070341020284003150754480c10080301d00c6403442035230000582508407508100501c0d412580200c018101c281c80480058510303101c1081d110064040284166400078260100d0f00f00c010b54a103280741e181d448555141c0900c8000f9008203c100c0051300e0741d181c80c0034448002030150407441b5010304050802034102007070014800c0146180000009112083c9a005c2100e00c0800e41d50105840c1c59100103a4481c18613 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 490881088 1250 490879838 490879847
    0x631050d03060f05060301030f050a02130e010f06030201020c01030504020f190306050112170c0309090c1201150c0f0503210a0e03090a0e0402130c0f3f022107 70
    0x1e400201540610010801c03841d00d038170341100d04498100d040c52001c0b07852407030001d040c207071540c00181d44208401c0030200d50200700c0e444656400c400030700801c00c8641c00d910310415549580f002a015030051050070401d54002d4003e1680184000e00049030032045000181000015000304240c04001100030710403c1804d2050702e02500b281e000c510008281c40d998641000d00d4513100c00400b240209503201a90020003c0c0d414042005200f480340e403400a05c1080076410410750403d100c41c800c2e0000415204001303076002080032035903460721202d2482c2c9418820480140307003200c241c442000300c0041c14509c6102401808400c031128005410551001d5058800c0300b6000012034108002c036a500340d8800003120110b0f940c0c00c12100895a4500016180343c3c03c10121595950030061088005a44140a680391664984400103608501a10640280c4080510502080300819440102e1007071881e040f042c203403444070241c648032030b01c488042c203460307c2e42050100c04000f00612a0b601d800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 490882338 1250 490881088 490881101
    0x3070203070510060321110303071e030b060d150314061b030108062403070305010203101706010e06060d0216020f040203100b0c1203130c0e04050631050d03 69
    0x803c0090000d2404c584400e64002c5200c481194002444442c2141075409440051002021441500c0d280d2519103000750610400400c94000d03190740404180c01c8030700a01c201c0744400000382c6503a04109554504e08020100b81140549219156400000048181c1d102e40750740d80e060405010300d0306000441546003a07102c22030f90400e240500052000e0b20f000625513503c14410203520010303110080041d0714010f002c070411381e0140103220002c424440150011809403061081c2c0000d481c0d951800ca05000140390810280360b00007034010040107900703100341504080020842031078454030480c2d00040382e0244030411004420000c4060941c030b04802141d03843e600c03d5405500e103280c072140c400000c8890303005848100c600812090f038483c00030052892550b41c035241e0b1554a0600501c0b1009a01d801c84085580707462120000c00c03010365072000301d402141e010000305100c0d00c4098440e18000c0218144040d400c034801c08401902045441c841070141c020009040d585a0150004007510324 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 490883588 1250 490882338 490882363
    0x4060b0c0d0804030f0c0c0513141518040611180109121a0c130801020d05090a050d0311270102060703181712070203030711190803060411030702030705 67
    0xc00004000c0031a170400c0d900c4c4a000c001e894514403002e0310789000c124001644c1c0107550000c06803600b50800040e45d6012090313180300622402d1f0350b43e80c1d00c6d10701020560180300e95500409070702c0246109503000301c09950020711511001c502c00008001840907030b08038550b008960910909580e407036580100c0000003801e0056031000320000030784c031040c0300030b007004030703440105100400014100003600c9e056600380c5103641f1400418aa881030124040e4010480980110b850030700894901400003501c901c6903580040a00b602e0910480254018a07500e18001a020010007191013503183d041c85038030010503580642c0803910411400249010002040c180030b1514001128107940c4444e422101c01e20380c00400c0f88481c040c0089042010b008494010315004100300c2400038954011004d0341c0310700700307503030303601100701045007206076030ba0545001c040c49104180400b002142c000d41c01140d0041025001082a000003444028541d1048884c0c0c001078001148070b10400000b40100c00c003001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 490884838 1250 490883588 490883597
    0xb0c0c0402132c0408070609150225020307360f051003080415020c0d0507080f120910180612240b03060a030b0907060807020d0807050f0904060b0c0d 66
    0x403d4001c07014030030007000e84017425482000c12000100034003504400040e0740d10101102c448006010b214019401241221120300030845030507404218541c5550740d8660000c0040016915100c402001804050001107950f03019002e9004a0500f0407140140c08861190005801c80030700c02100c21154007901244510b02007501c01c0010844407001d0b80c06940340070414043d081003040d42a89491002200c40d0342200c51544040c06100300401d0310000c88440c00e007624000340c1d0b880f140b41c1c0c6a1503a00075031180311006000b4840360303050000300e0006682c110b04100030b010214200c4d40c4284049a44601f000401c040c0800012007200c0c0544440c2c10030b076040c101a40750b020025420381e0140760080c2a111000800010032903a100c980d020300079900000c9608050400141303490f198040d40c0540d40c082040c0701c011652141c4006468440b031449956140c8150b12013110485295000261460569400707108512172a5603900c200c400918000700300640d84d41010780407a00f01804030b0410800e02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 490886088 1250 490884838 490884899
    0x1f0512090115030b0a060923130507061d04090507140625020d0b0108070501031a03060f07020721060c080907090504080d0507020a06060e01050a0b0c0c040213 70
    0x94800803480590354418144d4455035980d040b120020180790344941c00041c20840c01a800c040c5c4520b044090080a42c0100703a959a02c1202c0c0c2c0009044410060540d807054038100161882104101003401801c405031510141c4070300000c0a031b03802140d040e02d007900100c0e801c01c504100c0482c1030382c0c0c1400c180c400d00d08080a82125007015441d410700355400c1e1555050400855880681608207564048200403242d41c64103045c9075118503078004d0a020034500700c080ca6541348a0070111110b110010018044d03a9181c1381c6060f941d00d40030700001e081d4428007201143d20111588007140c1000b443d6908140003242c0d051010907a042c805a81d018043c5210034030144502c08501207080d240003042c0407895480e40d1400c5080c03482585044a441890030f0240070f907183d40464101e40c0f090007000240000d944807000002903c0e8203104995020445040411040040b280640f1240030b0360001d54a1200c0c1c0d0901007001c1c0e030311030109400d80c03862440c2c06205250701ea42420409030b0454000c090f42 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 490887338 1250 490886088 490886111
    0x61b0d090806060a03080d15060c05120711010c150c020a0c050a03050601051c080706020306040b0a0b0d0e100c021516021207152a03090506060607021f05120901 71
    0x7841140401b8081c040700003030903d0012505d400a4040d0301440034080999130340e4520040103a000d0b210204c8550040c00100d45e071b0301c0f00c04c000740e0740c0d1641c2209080b8100b40e00c800c01540c05124081c1e0403503082280c80c0c030407452810103100e40880041550040c008040c858030388200c80c0520f07608858841e0901400c18800304030002501419900142c4820404461082000611465091000740356010000c0c18a0400040e500030311b0081000b0356042c82045400e10230025204200e0040d0a44400148050844220341c0d811101460b0f400909680b15000704c1c42128059500b04403030940913a0041c080e443c0c8001180324201d912a100813074010340c40b41c24600080d11000c280071903d421400100d0404c1c144410080ea006445103078060030440300300801c2c41c1c840321810101840b141d2000350581c0510351400303030080040060b03001006d01166680c00302000001d400c0b5080a0340c2009851418041080b00408440b08a040c90340307949848030110801004410401030112070243d0500344c5072000e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 490888588 1250 490887338 490887349
    0x503010605042a05070606030c050a0b07170a030e0604060203012402060106140c03120711121c06051e090601031b031e11070b06030601050d060b061b0d09080606 71
    0x402070700c4030f4540c40c40143c001d402222039005001d0080e048600e0f0020000401451009604c1261000d07601000d101e80d0b0703481c5600c2e0600515202500c010003501c03643c0e0000030b11070010400d48029040009034410300f0140d40746032400458044520300c0d400401441039a81102c000c1440d880d1000c85071082031004a40251a402c2c103205040501ca908100c6a000020100544078150980000c613a00c400c0d0020754404982c0c0306450240219032469032000010741c3c0450b9400c0c1214640550303074546142140f518100c00412148025003e0b0384520116082d62260500741c42d40022801340303000c0100e0542004a044c80240180703060501d0701801c205903032481e03840b42948208078140000c502e0307a001042442a02051020b100092030715030000782d000108009014464021040c0b18980d5840900380346c0c3c0c0b41c00a0081a5000c1c009001d0400081d03019004505105c3d00500007a04120050700c0321040a48900548001d94000d4000310085544c004050300040003081d000300042d05003040401c1e03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 490889838 1250 490888588 490888631
    0x60a061505030408071e0308091c0810170a1b0f0909210512010b030c16171b15040822050310050906150f04181b050301060504 56
    0x2041c0200840040d090100400039564070b940c0060842108200048261580d4490208114045012503000c030307410310400140a200c000300c0c0440c00080e508003400c1510034800007040340000101254011400d20f03940380b8054400307800c100040403281310500d41103550448445070b107404400c07802c40030000f0706140c0402c40200c507070110740002c111078142005420185103200c01c00500403101103a0207100c1d4004028000f00381c0c1e030f11203005641d0301c0d240c03030040c0e91200359582a066081481070b45060210500c140d080d0354440d1a01801e110181225201d6503000b030358403160741c00f1001a1611070310409220070364900c5850728256081c0e1803c2c1d40c88802c64040e1140c0d00500c130162480c40c0050108500c50385014000040440341e008007400e650101030701e422642807000d40508008212940400b626900520000510f0b103510350310102c05200003020f0040709001c20040b01024100818400030030100724001c4100260360b4076080c0001c0c1030958040c0c1d4070a50241d4a094510b5000e103c0ea0400034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 490891088 1250 490889838 490889879
    0x90102071a0714100b0603040b16090e0112020a0506031006030506181503010c110a151b020c01022103040f020a0315020306030c0d030203120601020f0717060a06 71
    0x90140400c0781e1100414003a9620081850900940020090b00000703036070801c140780c0c000107001c41040c0506015a40c0401c5e90020f08100d04000454181c411802d4812904ca0042c0380804541d51f0b02c2c00c1c22100e955007070b482030f103900112480b110103604110190038041c1006a420380d14500b08584d0b45412080380f841400d04040d42e42c00070a40650f1405c0020001120000c403202c114280041003450054a0865180c420342c07170070030031100c41401002d07001a11074800000d0a1000c0355901c40c603800400c1d960426400c00c3e0780d00c9150b400d41c108044280e80658041d2300a210200d01c44002900c1d003041d50400c1e6039102c9400c21402e02a203030b00300440340c2c01a444182c2c648021081d201156048846410041441d41201c90300c800c1c154655000c0d6100707400480c03c548080703418200303100361030100060140040c2c00802c201d9600c2c1c2846255103420007010f10407100c0000e1034107091424822a50000c0090081d04070351403160711800c00203030350030030416002003000a16100c40a8881d07035603203201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 490892338 1250 490891088 490891109
    0x70c050d1115071d010318052d030a0503040f061107030801080601050d110f0306040b0f1302060d0b010c02090108030a080105030105100509130b040f02031005150f06090406030c0501021209010207 86
    0x1d13041564800d0f0403140e152a510714484114241500d0440d44503034042c8074101000404030314a0104105050000c3d000c2c11681c009180742000c01142120242c0c40100141d0307200c030300c1c01141c40014400b403141d140d0440c00b210f40e0740c0e1601850f2800520203541a0300100707d561015005010580e1140701d10002240d0000020180c0705102c0007240325085035020b81c41d8540201410841880400a20184107400744540100e442d5205000c42e4036580b44880080d400030018400b03015a4003807070f4010606070748141411901540300e940000d4000710240c12540a45e00082101e0440940180140340588002c4009201c9440d2a01840a03090381900c0780a10071318168000c0707a44807004862081409800104903805407515060052009240325001c078001d210b1560300340b000340040e10075280035403d4000b501c05007203101810014007188d4031081d658014005c10150409585520850000354850340c0d200c7c40181c600740019080190400403501210030800005449a0707000c14460151012500e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 490893588 1250 490892338 490892387
    0x7030b060607151104061e08010b09040b040903030e0c120303060108100803070309030c08241b070501050105040501050604030b013b0f0109021e03070c050d111507 72
    0x6202103408100e826100c3c52900d8207405513035240000004205965290f02c501c52501e115803100c1c00392803080b5030000002054800148540700c00710004000000d07004101040d07015901340058100c0d02da030b0100700c01290782c404a2000d0260107000382840f202003110200c0e12070904035480f64480c8001031805040041c00000503083c0c0d891090700a024166a404076919551103140103000e43d41240002d95440d10401000501240000349400c041c26201c20241030001410380a9242000c005e010b0700740d03111070019a140c03004409405021143d0295001207829490102444201c42060700140d0040c001040f0500c08244038100ca070781101d0000140f01c50079800d6610001108040d804e00c102803240f240004860304103502260b500a5183e0003110b1040d0340d0702d0b00058200d1052a490000a1040c5801001c44464100180d54025814200103a03180c0143c3d0b1514100516001018003050b203c90020100a4081001300c2e00c102d207203014105241010308020700724100b00b80c0c0d484c00340680d00c003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 490894838 1250 490893588 490893593
    0x604090309080a1406010b0313060f0b18040b25180f03140c0303130b130e0103080301080d021902041a030303160e0301020a050304260403080a0e010207030b060607 72
    0x101c528001d000c00e40035034020200501e40301030942d809000b440010b02c2050f002203403030802c1108890140f03081340342406040307899560f0348014103903200d4040c659a9480c4140c1c074190711415031540c5180c0540c0603802c075074a130a00c1d1030b008400016140d00c003000b010010410707a018501c480041054030604020003070240a10b01c40319203c01c44c0d042441c001211220000402c035501c08861071440f0201d0a4401c0540b0b20410305941c1c1c001d4810b2801c100312440c800f00044a404001807046610032444881d0442d00d443c1c0301a210b070800c0e0700c2100d0039107000004012800091003065480001807020f49040d030101c04d41c81c4d40003080d122010344200e694030300c004000d10b8084000000c0010280551b03883e850148001e003404420040707101c0102e00312030320082441c0f906100b2140203c2c0581c681c0c500f591075645441010328045015500c02820f001300e805403d07144080988002c502c1440300d590303a0314010400500c0040b00340a128150750065a0038000582150500d2358410f000ba982a62100c5660 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 490896088 1250 490894838 490894847
    0x609060f0a060317030405060f0603060613020f16030210060506040b030a0b101218170a02030403080f071205030f0103020f03030906130f0609080c04201303200906040903 75
    0x207620080500729445070f20944044e0303d1020710312850181007603500b00c2e65151503180560f0011600254190030510000b1500d00d803544904d0b001d000003600040c117021207100c81801c2c40c0d0011141c0720084107a04c4c111010103034100501d40185d803158400740641803401d40401c1003400f4070700070614040700100004264013a51361000030344031002007868400740c41800700502500c5a42d07411890781800c046c4402400c0300c10074080c006140d0300c0403031504408048040714884c0d4124414003811400b003044000003003001c40000d8400b4000d171822207640c0b810145000c107a00301c2c000030203a003888014000c118082080e1442c940c1107030b405880700c5075095890703800241144a840c00b0f02d51700c040c8c0400e5124070000d8180440007070703070610074122030350a4944006940104040c8a03910003a40200034900f5141041c0c0c0007240024000928140041170209151030290000742211241282000c010000c0c807503c27000c0b069041c4250710180d03030300c035180c4030101c2c40b4180002c00b11405151601004010903228 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 490897338 1250 490896088 490896101
    0x8040201030911060d0905011d0309092e0815130b040602040512010e07080309030a12020a0c092a0504091806050103031d040b0a060f0215071206080609060f0a 70
    0x18401652140c4205c141d8004050710175068071150700c3c0400e010841c5640280c6500d500b103002e8000d40c02d02424008000130781000403d40c4102e480000b00303410440c3d03081405001000d8000082103009401c10310301038900080b03407160044c0700105005116120281d01e0307210700c0f01a0400b03040f02d1a944c481c20548082d1080d54040c0b42c03c1509100d03041c13440d0310103511240d02c052003001941e081540d80c03044242c0d01d0295a08243d0b1503080711514800080b2a100341d190b108040d070040d5140c020712038455901007009a401082500c1d01c50034000741c81030021130281c10320b468514003185040602e6100030300e00c0c00307180201a19540d44001240c106031264000681d219406a0f041c40290307144c2c03900030040007440e4040c1c2141c11154108030594900780c01240310030280034041c0d407501480c11070104d560080f05030360041580200451003105424106956210f07200700c1c2c690009403000f282c603a80c100c0b0119842140190400b4082c0550700c00e012030b1180d004200b40007803603040d40340c84211000610b032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 490898588 1250 490897338 490897373
    0x1d0306070203040807050d1a09010b040c0924050418020c07080a12031a06090d0f030305180f03160302070807030605250e04020d090204052a0a080402010309 69
    0x220010041100d41c00001002030380d071038009550085550360103101e00141e10290003480f080750400406148054000c3d01588150395000110b10701318a0000300d021501d804020384005203c0750414082000c0e4885030780d0280c5c800460405200d50070341401413450089000d44481741e0b80903460013021075025015039012403e10000e42e48455a40d9103020380d80c460701401101c10269080c522110a400ba11410840c40e2605801c806070700d06120800c202a400352540ca54040e1940c034241010a0030307901a100798610a40740021542040030a807408036a80d21103542d21a88191121104d000020090b1407120031000c2d8012035803982850282d08001b02c0340c0140c040340c454120b000051100e03a03000035004150000c00080810803d14200c0540110301a5250114100d0a0340d00041d0070280d005009075178510b000010b40214950004054034000c0d1140f001c0e01d4080d01c07030031301c0014889001c01000c40445440e246001031000d00641500e4000b2b00103414169928541e1062042d8820400304115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 490899838 1250 490898588 490898593
    0x60f0e0918060c04080601081c080604290102010513030903020f06040e090102040513020a080f0a0f061215050106020a0f15060b0d0b030303070c0f0c080321060102010504080403031d03 81
    0xe4180f200ca03003e904a4030903d4514843e10000054128020844038040352042c10544842441c0c0caa080d0b80c81c01c000f50029412503a922803400a455800194010000c030300c1040409504414000a003503a2000e800d0140b0b40e0448c186c40741c00242c1150a400c102c0341e05a803000c021406940000e8ae041c025a40712100c0a60761000b0030207103501c103500600981300c0884d110061104100c0b01ca01c12800340c1000d6002296240000c503505400040c0f0b4603500038002d08002c078440c1074012013001620781592002c5600180d2240c60410803a04100c100b41c426402c580400480d0305d40000255900354845020300500c0080041200380310181e155081007482036071042c0581c6a4400703542006900600b6070072070b407600e022481c0c5030900d0302000b06d030b0141800d07540340c180308034590301c41c070041c84141c000403548005070000c006103914060000c0d2444a58580300110980009862000b405100a040904591600041200044d840c2c0c054806580e01441c2c580003050031161030030351440e0406441036051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 490901088 1250 490899838 490899841
    0xe1c05010c02060a06150c1b0b0d2019050a021612020f15030109180f030512100e271c0906080f0406150f0303030504020a060f0e091806 60
    0x85400007620303802544401c071304001c5070303a54024852840142284020015031a102034102040300240d101071514400105001080c0c0c0d01e0659028941c050059054142e4440b51080760130b40c429a400304660869240351481c1c86100880f4440306152881030070140500030480141280c82004804024506a08032030741468640a02a442070000c5004070322400712178504400c1403c10200841004001456550660b42007602c0c440142c20429621503c50800c110401c001c01c9010354185140e41c000c1e101c60356a0b60014003080800c4400a21151024031781a50402401c90004c011540c000014210918003e00c0b200114a07041c0495040700c2c05442941003800d40702c01e502000140b0510203403122000d085da03608082e0790341c0c60f040b109151640d04603400900800c4d05900054040c540300003103406640d840f0941041d00a40d0342d041034000035510020002181015450500500528180390a600052540003881d051605d401c0e5030041c00c0c0700c40826501c5181212121a2101c200103036080d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 490902338 1250 490901088 490901111
    0x50c01030c2a06050604020a020c120a0501020f0301080d111b011e1215061b0218130302071202030307020d0602040f140f0f03030a0309110d03030e1b010e1c0501 71
    0x980b1018501940d00602d010003281301403901b0300c00c90300713500c5107900a80b0303d11151804000702141c0e0710080b150301340541d81020000406c01e10003444401d41c002004d5880394105424246007200d4006020181720611502e403000f41030004940c1140840100d445070b8105092004860000c0c1c00072000800085480580d0a0300742c10001403075412041ca04c3c00c1001c030a41518800380c41c2ca140c030915001c10300b020b0110b0b0003004960720740d000300b034005840005625000805d02c0d1003803c00300c5005404080c5140c0160801d40e050151100074540b280c1804903074402900082d07103911032844001c0c4200a0b00710b2900400096405a03401044100c4000304a02d0341c1d620204020070b21117201d40d10510700048420701500e0b00f60307804030402c64054019030a10650b250182c00070504031600b0303558003105154001305a56106940041548244d0300854071526006003640340c1544403d56a003101e03060b0b0726190041c0da11a5481010f00412103070414800c40041450f0040c04900b58090055401d14100e4000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 490903588 1250 490902338 490902407
    0x11a12100b0303070f200a0f0314010209210d050a0e0112060b030a0212090312190e06040309031203060503030319060803040303051207051608030601171f050d050c01030c 75
    0xd500086500800314060740104118202c0c41c64021a005001c2408e004e04c0030032038900740902107444580006240180c424009054502641900a144120342011112001080c801d014100886080c503a050200c0b944002d401288900110750400c0852070801e140d140c600e401140042c18101e0712241d8034100070403401701941c00701024142095a01010503d0264008101d41108404142c120116220014215144105800002e145c0c84e202c2e0103d000400051209600840c46519004401d6245140c40403030f501d109038824041c10700d031400030480740d20048201e0780e0004040c1c51054074107011000003402044281c10440541c440440c0200405800c280181086603002c00e01074041c0c1d0b204c1c10102c07000d00ca8141c00801080709546000d0004100501840d0001c1050404503840d1150b4184666032810845900319442e09114aa01500959188040240c4002c0e14400c0c81000103880e4250398110868080c0d04150f40c0300c480f80001c612880550840e5400c40504002e030309603503150000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 490904838 1250 490903588 490903613
    0x2040b0303161b1215180c0b0d0b03012a020a08040801060303030b0a03331416020d0e0d0c0b071101021002090d14120c011a12100b0303070f 62
    0x3100010708031004220400812440c2c0c04059110080040c140c17008038001c8090010380107541840c0300b100d03101200040082d03484202030032258908a480740381038541d110a42da46c8410480c0079900d040102400750311060403042c0d41d0005440794030f4900304480c904901e88041c000000e0450800440c0c0842c0543c0103410100481e8080d039000d1014041c030b0000c00c04284c0d001d2100912403010203241c02d074944503200c4200595082450404510820300d070101c000e030307240c09400c0102c00c1c08a40410040140b21010040400028401010048140b120113040d240101300386503c94864487c00302c040002ca581c801003d4585005800e8586009180148145100451460260241007a04050781081d07200352201e0b184020308002c0c08201584405442c440401c00d1ba1300140175542010000d01d052030002c00d402d01c40305000041c40d00e001c80c502410500c2a243c154851030a0440c0000685070010700800000c2c2940780000c0c40d0040d61000174074600c990000100800d101640c2030040c0700464075000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 490906088 1250 490904838 490904873
    0x1020c0715020f0319050f0c0a140601050a0303030504150e060103060645020307050405042003070813151b0c021c0215032a03040f02040b030316 64
    0x1c2900c0910081c042c1e840d49074801c0d040c0c0290b070080c0f101084021100781c0b500c1640b056030500c6441c04c03c00d01d1180d103c2d6070200481a48075070106010004000c07000c0203000e020704032100644559414000002c44040702d5120140416840e040072034107125684845403e40c0b9542c1c0780800c042c103a440d030031311303112002480161036003840c1903000140324200c440c6408102808100c6015040080208944240807181280d000030040e40c401c070350101c0311031001350b0140999446083e112032401b4204410703600303035400d20140198003004c0004402880429640c0100039801d11402e90340d104081046440015030010305824003104103490076402551100c4a05000510426000312440c04140ca00d1a0304800c0250000300354a000d8001550442d189101d40780700034800c14000388009000e00c41c0d508142c8440803541c155600c0c10074001d040f844403441d0712030208840d80c20351034262650407410310350001c043d01582e00d5400c20586035a0500480c4c0c40c0300c8200039000f100310b0309030400b101108400c1000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 490907338 1250 490906088 490906109
    0x504050d0206070f050c0a0c0609090c0525020d0807110a12110111010e0708031801141c0b10021c090e160306150203030402030105060603010e07110c0301020c07 71
    0xd100180c80803480307500c60101911050b800c0a4114012100c9074811282400203019220100340040d41000f540001807817580d03212110745080003c40812120504403a8045c044100203c031051303542c00c1c2c1c408003810034014031484a41084d0000ca001d00008034401030070604005811420400c2480703a0b20130b1b0f07440640d525290a13481d4612100403091011010304001c900f004405c1807581b24519400f840b8144800104a40005581d083c1ca80300040e000418036170008035500324243c000c03180e01100c5203000d28145060b036076498101d086034070403462008019440c94609074554142900b01c1c03201c00ba4050b21032200c1c101e036020001d440342d034170070465503010402c0240081c0d041c0c803414142c001d232900881a2100c9848542441021140a4011409142c1c036031100040d601c00000010040050740d402031a900c1c40d10313204050844074000c09492085800f84014841c2078203e2840c1548000c943c00c100307661510380c4061074988860681940d505600000b50300c06501c1012031090200c8040145 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 490908588 1250 490907338 490907353
    0x307060c0b0c03090a14030405030111220f0b0a0513030807020901230f1f020304090c0201020324030709060803430f020a030803150307061d04150603050405 69
    0x10000b290b48401c3e40c08000a0703001c0c2d240640030400032000c44040342410300c11686410381c4c48012a0030344010428568042c030000c40e10b41c10754815080e070130b54000c140c020200d20150410312040740c1c0c1005400341c2000e0305070100780c151046000c2d004494011446444144402da9a0729008105034020141280500300800000800c01c4410303040f94102c09001c0d105003090720809003480321074603061011703230b03403100f5100303102c50741d018100d0752049010710700b039000c0c41c2e884c0d0604044006445004030b0420442e03104108211640180e030140c0c82d140d001010303240d420f8240c030400091034180e5030740000100918102d0005001c0c40000020003c1c0d550000c0f803030904003145509100b204d15141c002084508801551080051011680c140766501c2503030010000703a01a00402d42d14034194108441007031000003404112000580d610030090b000328010000382d130401c01c0c0180307589031209010b84594018098000c0b0f46e505d40e08120040b10340c03000742854013030391440300401929050b90140c40798000c894 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 490909838 1250 490908588 490908601
    0x203180d0309121110092108060f010f030f0f0e0f0606092a03041203050c090a03030503130f08040303090e090604111203070302060601020d1d0609010e0307060c0b 72
    0x1011845500300d02d030150703042c2040000313403010310b5402c2104030180103244030041d403000d481c443d2800c6c8030700600c0040040e031520a1960068010100e0f0403080c4810b0500300322207a5101d0365490303d0302e4028a02000100090841903001c0c208000c0e1814611b4103040d401d0000d25415440b081a100c3d42004640c0b500c10103000391034440d6015915150841000300014600c404040c0d07010107c4080c03000500003078400c0c07036801141c5070010340d411503a080826580000c3c5580c18000c035608000c00d01c0c862458400c0c02c42c00511040c130f8a11008003070181c040001035810141e6014040c0541d000200e80c5912030341403600005542c03050204078081000c03440c001c1341612081c03500900c695043c0b0001c0c501c3e038446454407103189186207402588004205405005008280050705c07449200b50018509800e00400290400741e42005040400c10203100d907083c030b01818440304068180540c1d60300c0d500e08060004a40d2801c440400c2a05807256090008240c2d60040341040a54040c104906c00c60700ea24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 490911088 1250 490909838 490909841
    0x110108100803030a18120305060a0f15030903090503031209120f0a080606130b19030509030703180314060a0513080403120c05060109020702031603051e010207060203180d03 76
    0x10300540e401c540c001d200103680001558802d01d0501d540102c3c817841c0c0304c0540d80d0b80b128480607110800000c1d4840091152134280030030310401801030b10204000345402d01200100394641c5c034441a003055141d0341002c061500500407480500005000d80b96100c010b105002030b11003040e170f0302c0751451044030b43c21a240306c0c040c400d07548c003019151441c41c80d0a40010302142c0b81d0301d0151960794030100800070001c81d1348207820990b00411024a01c00d44481031944003000e0701140840d03200602d400c00040000010001c000c48800300e5050802400c640204a0101050780c00c60b08020450070041c0b8036604904400100c092207080185028030442d80c541e00c03003410040c810100200b14003020311050000801d584032082100c0c42c14944055507100359240d4524000d020780c080d859481c2d0002d0100c055003010f00c200302030b19013101041d0000902d1580c409075141968245400221960a51603038542c0007074044a09140d00124203646030300344004d07400c1054114800c40010313071084000310240c0c1c40c042d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 490912338 1250 490911088 490911121
    0x12180504090807030539010b011409040903030216080c060705040f1a16140106240c02011e02011505011e030e0f070b030117150a0207060b0409110108 66
    0x20b03000c681440034030f5500351603607046103000300e0100c2e1140b1751003009840e08030b0001351404c0311680392984d1040000591802c44103214002410402442d07004900000900100d0f15400d034241e50000b202012070800701d0090050410309a1742180701c3c1c00000a11000f60007820400000c1025140103864406082d60188984d1060b0381b254009600104040707194104999000c8800058161a08800c4540c9504c1540d040c0d004440380321801900d50004c240074410368028008600c0444501070012018096418800d403c80e810814605181c0c011a44114600401b8110401e000e00381d078500200041c0c083c10885030540c1390f03951101c0b0000b40d198826513105242481941154010440300c5030101c02030450003006484e688120100c0d001c11440802204004001c081003080d125410402700c820416013000c80d110385a03100102c44007a48400c1c8100c540c00075042c141c01a030741d060301e10340403015024141100740d000f40f401ca41041403008508190550a000340e8a040007a999601e41500c2d01fa40d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 490913588 1250 490912338 490912343
    0x1a130608011505181011010b1e0405100e0405030702010f05070b040f02063601030213121707030503070206060604080a03050304080f040f140306311218050409 70
    0x110a00b11555140680010108100c0880c0c403c29030504000100d1486061118140e0020b031005c4d40c9210645420300c0303200c88180c01110000d00103600e0040ca145080140f800c8103115a0703403480490510042040600002c1c203902e141403a4503d02414070a4030fa0300030100c00e070702090800c40350b0040316108408513400c00c1d5008103042d950385c0303854540300140c1e010500c2c1244c10110400c045d4450440864004111414404081c24480004001d00d8081042030061905050040c0440c5503e551841c81c58004c1d80e040d09090030126245003400b40a0f1000c0f0b240b1050345450010f000814150310600451003841c085c0c00311482134603060b05010681c821889400c0b07481c0c100882c500002840740300107640141c00b6484072424a004803c951910368410341c401c54404100302e0003000f900e400617051000010702103024115130714100a02c20038a01c555035038408002c5030759000d100524240020382e00310070b0300a0301030030b21a81d00781c1d0058041001e03440c2d1040ca2500d1041c0000f0365191901905801c4c1da03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 490914838 1250 490913588 490913609
    0x100506060f0d050925030615121b09020f031e0f15060706050108010509060f010e27070803040519030804060f0903060507021518060115091a13060801 66
    0x30b240d032080800a20002d007480a0301d0181ca62a4605070381c5100da5266101d881c0d01040c00d02c1c0b0302e9840d081080380c41c103826080070816660702c02c1003029110701d41d00c2c1c85607400c03c0b150f41c490282c2d1404100c2e140b1454228680c0e040c400300b403440e6040d103d000607520071080340482043d030320300042202c80301c040d048a4648501d148a0000ba0340c80000d100c1040b60110b028004606242140da1082c0554000b6000f0381140da541d00104074061004100326071f0000c4004400b00c9a40d41010b443e580c1c0031a009048030704042300c480015201d081d074006d03049500a0400306961149444207009600c82d030140c8a00c503c550191210743c60000202c40100c0102ea0b03226080707600e024075058066600e0144110f03840d062000c2c424001021606900600d0701c01e44040d80035204065203001008400280074241b06602c000c440b51400e008000050402d056650350181c2980504614400300c4400741d603500103104c1c1681c0b01030701821079445007001c2c00118103d01440d90090761540d1044400a10074443c00d520325 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 490916088 1250 490914838 490914847
    0x506130b090114120f25030c0c060207060501090c112a13090201031103040b0403230c01020c071d0c0c0703080c10050a05010810050c0c01060602100506060f 69
    0x609180c0001d00364081c043c10a200559888851420190032548012145030101c0041105003440005c185a00070b404808481b5007115500003030750660000d9001100b410b5458850314045030264624080140c1d001c00c003555115503d1500304003405080c4100b800c11410260161a4030b4002c804507002c40c1d1140001300410604a007101c0088401452008444501c1400c5041251500119103101ca110300001203600c41040c400101202c0d04509181c04030882801400006499021582d4110ba0140b4000807002440e03c1041c8038405601509480307000009400c401544064010f8208402d0643c181c4500702e981d08070b000000c4004584140c11034001500141c903000c0640050202d1024410403506070545a43e50305405a204070b54015aa40c441d20041e07181000302e004041d030060b0b03040c0c0140140d5140401039562412140c1201c0b2415440310005001484124152036000310701100078000e02e581c900f0003a4668844201030070301541000002201820004101d40d401d51040d00941d240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 490917338 1250 490916088 490916099
    0xc0f03120f0d0b10050408120301030b0a09060f05070e0f03210c01020403080f090f120601170c0907050a12020c0a12050c0d080603010f141609080604080a030501050613 74
    0x165888102d419141a54a40030880f1584501826104072005a00e0b15a5110b0410711581e01d071225207107074010390b0001000180f0029040c4201c19800100c908004180e401c6145040009000042c0808032503e10740001c02070b010f5844800900310080a43d400340b00c0144a48c107240e02d501c0c100c64141c2400166040541050703c8071070080c03141b42d081000040c189900c070360f11030469a00c00e41c0a0100c004005c280c6041e14134045011554080003111410b074100560035815445e104140301304100105803501284041d802803006900c03131603005200c00340030b203400704002d040c03034000900030300000720341e0519065251800c0c1708440c00300680d00000d2035202c0441e55a2650403041a0402081003014084080c8a603010807400c0e40f000780a071140d45e41071a1013400e040c215005003421312901414551200300c4141008043c0360061501c58030201002e8030b4031000d60b20041c85a100710302c40c1c410442040144000c82024200c0d0240c20b50b41800181d070307980304015003400398520000542040d05800c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 490918588 1250 490917338 490917367
    0x90f02090c040e0c030f15010e0f210721050a1203020c030a030915060302060403020f030a080c061608040809280308040e07050403080f09041107050c0f0312 69
    0x2800300d20000181d10309a240d041d002c2086400344da400120100c048284141082c3c00c28215500038425003110b030341540c00d40c0009008107a0303e0b1500e40194070030319511f51240c89208400032522044088081d20100511400340d1b1400300b40308900300c2170310301000040c800f940c8180d05518250400000c0002c5000d50300c0c1c0c0055540a01646014180e08000313088014501780041c0071203480903240040e001d125400d1203030501260380c84114002c0d15110050005a5510080c2c0e01078a4041e0341c0030a003c2980b070007191a0400001c40540031344004580d6080b14540042c8080c411031010b0b110154130481780074162421001503400400c15a0305120070900ca00700000700500c181f000030f40d6400590802c102c2c00703c0c101c07299002500c1c1c0c080c0000702030210301035810329260000218544185460b1854892030746c0303402000d81038400a540010004055903884c0c02064040c0490f035456590750125103001c60b0740d0300759001120b02456021100342114070b404941c031020940380001007842c0041d0a080f061 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 490919838 1250 490918588 490918591
    0xd0c020a03060e031c140105040615140c060f04200117040201030906060f050108011a0403031107050306070509043b01140412081006050403021201200409060801090f0209 75
    0x20f280e8801403001c6100100303d10703150b030122103112000003040e9140003580103822030160020381c0100e0606c0070400010441d900b4204c2e50301080c0c80c00c100c1000c0c0080c2c0603802c034814889034509610403402071000384880800722900461140b1001060781d0040000001c8028005100034080f517030442c00600c00300e0b15003450700e41c45841491b002500031029514801150000e42007460b04c6a0500b40500c803a5130415080f07405440c0483d40201c00b1001c042141c4d20500c214000201003000002c24101000030800030000030b00760047c1650b10a14200d000100143c0020802c00e02c65800c0c0004200240100c0d21b9180792240d0350403d10075442c4d100c40c0314200c09010307441c0b844855980c1d401d901d4070041e0128807031406940b050bd2805440d0856010003445014094440c0790013101d0140c080007003d82113400c030380482e641170307030611000301125107101e00410503000301c1c89880c0c1c17003c0022001069a0b07001070041d04c1400000300003564484584500329001004020512881d03890f500e009460603601c0c2c50b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 490921088 1250 490919838 490919861
    0x911030f24130f0c050306010e03010216020607331a010905120309030a1a0907061205040312051006080108030f0d091112010c02120c0307060f020c0a0b01080d0c020a0306 75
    0x4030b00d0703560000c042c0f0100d619130f070401000220048180411580e20020307911801c04110020340c100300544002c03c0c0c0c54014010700911695000407454208811300000200030190b0001180718070740b18115846440c1005a2014000d600c0e044140706c280360040650280d01c9010796450640504182c184040818030340405840c0d4030040c05864041d175803c0107956000ca1040f503100b460000c000b070b000d407501400682080e1041c2c0007208240022031380580c403c03e80d0200c031600864140c480d030600b50b07071284103a58514842824201085460703080c0b40c0041048a04503a038000c09030b030781c0d10708591b221b0144410410114908101e61000307130086030051012030380955000031101050b44001402a60403169280d1a0394440408010301c030340512080744100d40742407025140c24010002070741c4074404c1d440c00403c0a981e0b08640314410410354107880c10003100c20119040c98682e4100201084d000344103081403840744440a00c005441101020710056001d00710080c0281955243c80c090413000658 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 490922338 1250 490921088 490921091
    0x50115030908041a090f090702120a0e10110d030c020a03180905070c120203120402010302160507060c0b060a1a03040809041a0f010e0a0611070911030f2413 69
    0x41141e070035000c0401181a036040e942e035901c2c90245e0a10440c0c0e24801021071045540301c04108181c3e4011400c0419002902c5a40b50b440e80b910805942e0348101c1a00140c1000d100c025210308150841040c0841003210f600301e0709840130030f1008074160b8101407100380040e0071291041000070300030082c03501000c10a00030720700055107a5200f682111421110000007d49030003c0381d051001507071049494400f184040c5292009215000e649030130060802410144c0c0002d40d003902030031802403504d4042c2d1210654012030380e1020000c040301083c460580e40c07202e261005c1803a900c0c145a001c0f003110b20640e01d1650808039611300c2d04403038000400580e5220410003174481c1329a40e40c4030742e60f01d94544500e2000040000c400344001000b2480b40e803414000d81107034624007665089560001c9030000d14080c4418101e12103240d05001c2c05500c4010f005081048100416000d00080c52241c0d50044000489035540d9101a18054030481000f00494154011566a0404c0981c100042403403250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 490923588 1250 490922338 490922347
    0x110106061b14010e16080105100e0a0e01060305010e0f070e01030308040c0803041e060305150f03030c0115030605091f02030c091306050910030215071a09010903080a050115030908 79
    0x806402d5450340102043c01760421846164030b8020040301c40b01910401c4000c200c20300d04040b0001450015002e50b81c4040c12b9200009e00040b19a000348034026501c200030700c903c0f982c80c9485c9000c0c20701004440468043c5148008030070ac0000b03000800c40d0310383c0300320910b00d0b4a140c500391383c40f003005401510102070300303003020840300b40801c002e00044c078041204e520142c87c0d008150f100024280c01890406040c10184010804822018114000c04889210250319018002441c52040b18a9902c180d420701c50348412556504150004482c00b070030040c403203030ba00ca07010310780c68544020b1100d03003508400c00c2c028070240300c03640510f922801c100e01c05442c10070304030005010194914100d82c2e1281e203d1314240b03c01d007459440c0c1d0344c0020715418128040c0c1e00b16030020f400040000440068450301080302c50070722a1140c206640ca2100b040000b03581c0c00c00c0d030f0005018059946040e00410301e058007094801c8a01d100e020b0482c4d110551450900b4404401200541404a0242c0f043c141c03d12 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 490924838 1250 490923588 490923623
    0xb0907030c0f080d0306230f030111070203011b0c12090308030108011e0c02190602090612010f05010e2b0212070f0f0b0406050d0e030d050403110106061b 68
    0x104000098002d0000092485140101d03040c90710191214031400c06007440c008020081451020000900240e0864405154200702080348102c0b101380302903256081180754044c05030042c1c010088180241c000f445402582140c20710740c080c200714650002030480034041d0100b03200421500c1400325501d01040710607620744500b41386420a03004480180d56400c0d10343c54040b1076104060103520180c009109060207490060345501c2858410b0281401404480e020001c1643c100c621081004000c5070300d03002d80d40040c4042181c2401901286a1407110118a645c0900c01100d169400249030500524102c02404540005114074040c0b00100c1c411480c0140d5405003a4680901d401000b04105864241d41511401155000c0d0f00d00d900f81d91400c1c840040c2c1c68007110b0940d05141081c9039104031007501c0e40001c040540d10008907020219407040c0c100c1c0746411250086000c1d59500c11a001c00d000c80600703c0e0b0b49885800c0c00b0800b23a18900d00d40482c400c003081c041d103020f40d01c0f0003101030f43c94 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 490926088 1250 490924838 490924853
    0x1a030405120d05190b10051e0d0b2407060930020d050702090c0f190c021318030e01110f0f0607090f05090406020c190209060612040b090703 62
    0xb18881401d00d61102c2c10003030a58100d414140e4000c1d0906014011036014802041481e1040780e1141d04002c4001500c1118007800c1c0801071070000000941c41d80e68083da0107100040062020561086038030030b141c504088003134018194103541c0025181c0c0381408559815006141d0f0b004120b403040d03c182110200d032890103082d13046039100e5401003d94a00c102c2002030078182406044024484207201e00c00260300c0f010700140d404000803512035940c1002100071451401001d104802c00c0302d04015103d003040d4801c0103500c0441c4240c40b405181d0350039244060645e652000c4405040200b94525070201b4450007152505e21410f040140d402c2184144040c2000300ca0500600c886c0d00c1200c41111501e010481140c1c070149a00c1c010103150b00300710840101c0722241c401c0a106902c06404a070a000380c80e812036085031b000d0b5003100c107941d038090042c241d40b80305400141d00c240d02c1040016118244501241c1c0c28850b011141c40d0703c0e070b45541d074084030000d000d4500c0400d440f60540100c0010745d503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 490927338 1250 490926088 490926097
    0x4150b09010c030c1b032303030f06030a080706091b0b0a0c030513030f0b010504140103060905070e070f020c01050c030f1b0613120306060c08030604140a090201020c03071a03040512 80
    0x1403001c0690721421418940b41940024400b20b0207141104030b1000c00c4c0d070011041c0c9e904440910440f44941c0c5035100000d103490390f94003003d400048000365000c00c101843d807103020754a11804004080c030602c9a8003820807102c81c171031280840320030420020903500c1800d4040f00181b0074100340c1d042100102041c4d040072020741088802040f909660020322a000d41c40701d00602040710700740042d258654201d0040d40040c072005002c5921011103404205043c0010b00c040e2400440145061401180090990611003030f51070141c054141604180e5100d00708840460540000962409903000100301850f80500e000d14030340c00c0008041e2502140600005004210204044102c1101401d040c0c40703406a05040c2d0050515100081100c1904011740603069a0072018660f2240d65500202d0094140882c0090000080c0c604005c2482c90036805204458001e908842c224500c28050583e280b446008a001c2c00c1e401150f52000300d2042001103910602c01d0065070484030710400d6501450b0003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 490928588 1250 490927338 490927373
    0x90501120203011817031005060706050612060601050a050d0f020d0b090a02030603120a0e121e012031091a091b041208030604150b09010c030c 63
    0x18449030801d51400340104906030060724422100405680e80c1c40c0d410200d9140782c0a0418800704c0065410030b1707440040f00040a010f0806a6900b6261406034020b24040b0b4401d0b2080b040c035254110042000500300d40308500603100d0b2883e00076000401e039655004240c125500326202d402050001010b8000b410070401c4140c07001c1200115442001342008000b8100c05000e031050041241c95070300000c0610309168011103d81e52486600800c07150882034114032074202d0104200000d001038006040c4960f8560303141d000e411042c800461a0070307551440341c1d205807030945000485440d000d440003082c0c1d4200440302d030300301c1201c10b9aa02d841c400d1505001021412240380401c00fa11042c05071801d040c1405140d094076944001c00101645005040290200810514240401c0000044402407d004081c2460045861400204652040320035501403820040b021030b046813111a000c0c296480e03102d4850030801c1c80c900445541d10400f0040c0c0402991200b2100440c2040200c9000440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 490929838 1250 490928588 490928609
    0x90f030408010e010c08240d021206180c09181e06151516020f031f1104060f080604061706181f0e161706010602072706090501 56
    0x500c1c0c0d050b0b405c5030740641c400d10500200400300100c680500308007007a11008649502207956000c404544103008038500217401042c2c00e2100e0052000004103d131081041d078469059101d1014001519112503820756500a012f60020401c170403161102c1008800c0342e80708561040c501d400b802d0756000f5906ca000ca001d40c0042c01440800c09903419807400f021001d1f07810039000c03403080341507074a28419403000480c0f4048841c82e1342c0440d0ba60724940c40c81c0680040848a1000c00c3c134002400c189940c0d1314411165140214600b01c4500c1c08050b80d045444946030000440c00d00d400a40f08030310001d10456216a0f00d80340480c1454500000305402980c040041c0b0f0b1034606484000b0400c010390600140c2680708264000101252400e00c15010141410109404078410001440d00405404c08150050b81c1e400c0806d00b0020100b800b0012a000c00031900c02d03998507030084e070320745a2170b002d008a241015551450f405158030341842a00100c5d00000070029a2506044120f070001e802452160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 490931088 1250 490929838 490929851
    0xd050c070618020619020c060d02040e0a06030f02090a0902030303070c1103011a0d0c0302030d0f091a0315010c120806031002030c04050f0109080709060509090c0d0308090f03040801 80
    0x72244116441c0550409020100301801d4000640340d0251101511500c140c0741c0f40c80502074403d0109017002c0001614850b11010f4413000c006c041c1d00940a0000c80c0f480c4007000400c0c5c554240660350440b034108a040001100c2d41c2c00380b1641102c000c0504803131b1900c0f5185000180c50800056200d101e20b6074402031812050700c1d1100000d810702690b144243c0c10f00040156005100b43d0184020104a5005840ca4001d2a020390a9800783d800a54140101c0d0306491445801c00b15184960322540e0b5411989034584801e14100745016951003c5403200f4400141c08440700c0714040171440d0141001901c40c01541c3e1402d0b140c0c184400c0d00700000300750320f050144504040082e00350354100560b081d811071030715100744485400387c0c0c41440d00c15161000c1a0050364043c0c0c200b00301502101c01a01e0080d52520103902c0a000380d4480c80d03000b4404040007402070080405c60032803c0760010014001c00400340c404840f01c40d80600b2005690281c070100300780c95a0100020700003003000c40004500c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 490932338 1250 490931088 490931093
    0x30307081207120b032a03030318010b150706020a03020403050d09051201060e06090417041202100f08060904150c020a06060e061c0503040e0112050d0201060501170603030d050c07 79
    0x2c8821001451803070400d50204556a000b2035015a40d024006c0d151228496070240802c420b101e0741d94550b01804000113000010b0342c51825040b030800e51303900a200c002543c031f06002400034810707210140104284001d40c00a42d050f002440600801d00d40035043c1501da45820b4200030702c100060000c00d04410040220341030000d072940c42004903400801c1040e1801e404403080c20001410184540c0d1303060005010402c3c800c120030204801480003a450700d4945c503490380180340c64032003a4402c011200450b05803920442800d00041429a60b00c0696200c500501c0ba10040c0540101e8900c1c401d11012101100d03039219682e106c551070b50040400c0c0b0001d06103201201c1c0c3e540c001c044004481da003041200d881c0d080c0310304102d07410806119041140c43c10447c2c04c6000760342024540c03004040000071445103540701c804500f405041a10f040c0755101a090b82214018403500c4e0110f240300405080f40b0295481c1e40d680035001906480c40e164050f0821001c0741c1080b603904015040c086000b00c107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 490933588 1250 490932338 490932347
    0x607050711150a050d05100f06030e12040e100503030301060e090a0e01020d020d06091505211c170108070510020f0a0c150804050c090a1503061e0b1e030307081207 72
    0x4020001f011990105414004814006c5180d40252002e041d107c11700800082400c2100200c8840903040031a00c4a45500c01120000c506807900c0c52208022900440c56180c0441140e04035100d43e00c6640c600306402003400090f04000301000c85855603055403503030f502c1082c0000c1a07110b0380d25000681e03170551000c1c100c04030b54140c1c001814243c503001c410b20b1300c0508040c01e1380684030200c8258600444d138280e1800d4590780003008031014080d195005409419000d415150416192158103076101c06107005407103400c0c2440358021641c0205400c001a0030121004000300a0301d105827010342c002c3c0740b0205c0c5000f030010000c0f116446401400c002d00030918602120042c040d2401079010700b441d84a003540d40900d03003a000d12443d41d00c00440c220b0400c0f0b6200807040b41d17070b42c0c02c1d0300d0b48030340d4038200381d0014000e0502d0445410b072607803203101000701107100d50800800000c152a000c902000f201c103e107417442e6a046505031100300420300109000303001030701030300940c40049902450000001030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 490934838 1250 490933588 490933591
    0x108040f0b01031101120b030307030c08130e060405070302070f150e01110705150c0a0305061309030305150d17031b1b070b031e220609140607050711150a050d05 71
    0x451b051a0513040d0740316640200443e85010b8241c6032801d0401000c0c02c1c00001c611680440204191444400040d031020b40c00300c80744a0201220f04001e19a920f0506a06a110b101002004404190a40c0002804180c0c41c4c04900303886482c0080d40c1c8420000079401c45517205032448005001181801c10400700300241510910340508820b0326040c594508040781c054400a007040c9611480085c44c66202e2258484200408540070701410b45a400c000c3d0007010140c400c0440040b001301d80c0c222a003070281003900c1c01a4054138411691002c0040783c00d13181c20140c05000c2442e00c2760590346040d480b01d0098052413140d1494001030405024001c0d2030311040783d120710303020701d810f00820100a030b144100c841b00607062850151650b90701201092042c0101c44990b841101121407401800070f10740c0007101c0305109103400700d20000780281e40750742c1d460100d0382c1800150003044090009414070484556810020f00740040b000022641040c154010803400000140d0214000c50154490701034175 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 490936088 1250 490934838 490934867
    0x10302031c020d21060e0402120f0c010804050115031a1e0703020903070306051f0803190c03030b06070305031f030510090f15061d150108040f0b01031101 68
    0x40c8090000406512601c250003c0300510440141040b640c21000345101a140700350380341007007069242c900e00b03c00e540041c0d80aa0082240035200e070294580043c000d00d4030704880000f001c0515a903c01111140301c01007048455540300d10891b4030215642c500000507520407070080b0386002c100048070300840c800420340343d904800c03c140250f2101c1043c80d80d640000707940c60050b9644614401183c54010380c0d60000385140e150908004004200c0031480700e1201c013212521200c07a5441784010360b01e006821440c00c003810b0400100b107189003c0e0b000d410515120f400c01060380604900000c1c0140c2242c001907000ca0000010050a644c0d004101548140c04410051003942903842e051303650151000d0503021550b9070340000e418021f0031410184143c5e4000105c0340600e909826210181405115004404000b4540b80e0401140e145946110b20501c0d0710100b4161031880044945580c080c2080e5410101c83c0a0303100800d5514040038061402400710003507800c140e000040a00c0c22480d0213 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 490937338 1250 490936088 490936123
    0x905071103090108180f1c12050103050312061305130b0708040312020a050d0204180b06030114060703050f0d060e06101e11070e040506061e1311070b01030203 70
    0x10742c4403903030b00845080e4125010b20b2002c1400c0c800c0c007621038545101ea0064102d18890100c0e1101400030714413003101d0058071540c03900f15004513000d444007074440030301008000380c206102c1c80d01c500040044d0310360712140c014108002c107628090080c00f142d1707054030001d15900c0e11840100c140301034241da158024007a498aa420303883c0c6a10001c0c0395008594001c60300c030380c00148140d41c1501c0b81e03050724110800741c9421580d0700d50b2a08010061b204c1420440101410150f1090750f03894500243d9040780d070044015900d410104d02001000c4c0d001480460500405021020351203080e00090003e84101100002e525420b168668000f940d008009920500204108202041e0310010800e084400e20601c1050380c0032120046e5900340b01218410040d2095000003e04848a100354501960003201a00d1413501e4240500000c440030304601c41c1c002036100900d15580c01c107841d41c2071000d0580c07c000121000000c5060326164407070101a9060280c280060003580b4060100d0b03800a01c10902 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 490938588 1250 490937338 490937347
    0x160303091a091f06052106070201050105060a03090203030d0504060b0906100c03050d0b09091b0901050a0e060409020603100509090115060f0c02090403030c1e02100b010306030803010905071103 85
    0xa5150ba6030307254000c0f40644480c1c001c0c001e5032420303541c100c00c0280500900ca802030414035050541c1072108485002c005108103004201010300612130325069075400381c03219182400c40c8000350007903c41e400d0100c1e058401040381422070381262103a14040d52285001082c69101c45040221090b0050101c3d403003070071804220f600d203c0d040301540102590509240e5194107094404c01c0040c8030305000700740c010001000b007211074400440c0e0b40080704101144240c0d900c1c020740070300440a409015840d081201d0000034841e08100701c0100c0e602010061020a070200301d64041940c0d0f030010f64412080c2501000700f4080c038030340460b016900203074a078000c00801620009a00c400f45032481003a060149034a00450035030b1046d50010183c1d600602507490700d08061500500a1400500701c00004070884a0746507219501c4c50300b039030190a154010301e55140389155080c010504085000d040c56501c0d07400000141c80600918000e0641e0800085c607403030291030140c1014221079030a80e13076030010003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 490939838 1250 490938588 490938601
    0x6050108011202030a02040e0105090607110c130e0a030e18060901030620121605160303052205010606020d08040803042414270606060f160303091a 65
    0x31081411114001880000025a0b001180c18507002d0351019402c141000040103ca01054200b6401403141c038007140c4465503100360407144840340c270020800d20703000700c000e0401e0391070480107000c0e1050302c03544005070388400c0b8200c95203018000074048000c21601c2002d40b0316450056070030840d1440d108800c4065252140c0020411141400700a01c22950384060380c024003082c034440d05000007404031055540a000d28410759002048515000f007079800040d040390680300d01c090758a5140c11161107022483c03039035020340241000520b8085007042c60740b9904844440b410300c41403028007900c0000350b0700b4180607000b4146070f030650b010b40601c00c40c3c1003400001045c08044a5002c1c0d040300c0400d400244e20f448102d800c0c281c05070030120107400c004c01a010407680c0100d15001e20030031500e0803180b551114001010851343c030064507058002c000080d9050400c0001400f07988060030885141100c1006240d400384903204050740002d40d03a5075410200054003181040e05c13a1a038030030380560f18201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 490941088 1250 490939838 490939847
    0x30f0c0a0605120a0c0507290703020708090d2112181212020f0d0509150702280b090303010602010506030118060209040b060c0d1205040308061009091b12060501 71
    0x1d40b1410304130b0750310106028524401d80c1030f80c00301c59108a14040525048001c600315049419510058607101008101100d00900c03c98050640c01140c4608001d1500100200220b90030f0b003d070342c28076400441041c8025401c80b081084074007074590703244401c000c00301c5004a8240311018121342080c600d43c9008900030b0440c980d0401102e04d411708800043c410300384082d000310320402540c0c01c004207150070300440c641c014a1181000d00200e8410441c00742800703d0000003640c0d200301507000000e00d44c91100310140b050140790100000c02041c41502d5440c80941c0c03000b1181109186c01c0072005001103903081c0607064000108a00900100c0d88400c6144a60601800010800c90f03000550034904e84883d0028403901200503c41030700d503002d810030143c07510300c2c0e800c1004c0095001c0403000c0c0907803460300c241c130300541d0996a000003d41e5240c0500900345918500f21007800785480380050050060301841c031030b60001101505800710780d150041d151010b441d00c650103139400c1400030f200c1640d01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 490942338 1250 490941088 490941091
    0x12030408250605070f11060414121506060c0708030705030c0706020a0515180a15140907120201020a050f0a212f0f010203041716021905030f0c0a060512 67
    0x4040345070800e00b014a41b10b54100409924a07402002c007050010f091030894818400424090728010f1031007001c2c022203074880090001c4107580705500c0010580034100070024018500b801001c643e0306a4640d81818034503041408101c813980e1000444507540c40c014401ca0004000500041000700142c0d5181d640300c00c190841c03030000c07052a800080c1c2e000f481208981c58010300c9400c2c0c60851101d41006c03600c40c40004005c181440c02d0040e03000141002c4d65100c1e10070381d50540030304100381c10245603480b10303421594164118482d000b1001d011900500100842c0c001110003060a20154504245201d850800480076481100050f41c074032030304885140e80704014038501c0205d03c9124128030b00a40481e41070240e15104009558240920560086007d00c2c0540305424400920301082c450621030058000601c00d0003100181c018244000c2c01501e0519071191004c245403164046131810600c9082144250f00a0041206034282109910003500b10381c509140b0307082021042c110000320 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 490943588 1250 490942338 490942343
    0x105190f09150c0b0c16060e03041d01061214040222020406090f0504060b0a030c0c021c0b06040203012d0807150f0503040b01050904021203040825060507 68
    0x1511822960218824140440030303200ea14041502c0104501009018000701202254000c0411011540e441d9202c001c0d0340551400b04040204010640d81d00c8001d000d800180040700c0c40207100100d0701000188070f000840364060700d0840b40303601d060402410f924020341e100580d10700e4040c012052410300f5280941c41601940d0304031010250031030b41d28400d01848a005203540c03001c540465000d5110764528221f9580f101c024201645690070441110054800c04c0c80c805001c001c464040d50107500034110400c0f02d030800c08121680c58000c0b03400a240007413500c4100002d04420401c01c13106003031190b04180f056408605540c1000051680480201d81c1c0d11061000c2c544040c500145481070b140191180209070345141c0d65503010403503030152240c160300108501c4141541854841c100ba240f140750441c0001d10f507a4a000f0034810048001340c001e903040300542c010008000030030001440104011001003402c0c02401c5009000240f095018082c1c62021520810400e86e000c2c007510102078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 490944838 1250 490943588 490943597
    0xd0803010b1b010c050c0f0c0108161116080618072d12030206090a150f0e0703110f030c15090613030c230901150509031207020f010519 60
    0x1821070b0108081008440000748082d0300300030190f00c0343c0e9441070243c1008989007048840c4003002258041d01c0340c1e07034244039a00292002d00091070b46e0b01c1b041c0b42c2c4440e248040c18110300c1c442e100981d03142010b201c2c6031001d4540c4810321040000800400002e58010300c10138051071078082240c16030f9100c0d01035210358450075100102059840c00404004c11130b0a9a410b54008003c3c0d407007240213900500010168054051000003e110355030114210204e40d90000c0311286941e402c01340c0d100140f542c440c101d200103a860b41141c01102c000c000d014003843c01242c2c1510404801c00030030443c0c4803254103c0303000c0d800c818141669034581d488400d4151442c02e448584404200c000700d209030180350403240490745528000000c0c400c2030140d0384181c0d804411034103410b1500290042c0300300f040c0050f0980000300c04004200e080400003074801403c2c40703441e0552070709010760002407800460000308409224000380c40303005c5203003140403410001400c0c00c00300e041445503458154080c144c1c010000a00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 490946088 1250 490944838 490944847
    0x140c070312021905060603010605010f0e0907120504051c02070803090d060e060f0405150708040b070201110c0c0a14030a0f0609021f030f0b060a140d050705180d0803010b 75
    0x86000340036a10b40764840d54000040b207801410100c0d51791605486003070083d4a0b20740702241c903520508e1b03440048096901c0342c049000118040c42841c4000403c48004c00814041c0004800072030f000d414050380c0900001c142c100100000703c02c16600d0b03a848202950720516081110708000310540b851000201c1e0b50403036542c51800c0072409042501301c0c0307002a005503401c0207984683c1d011903600607406001210704105060780e820070050300945844022038441b100140004000202c903a500204600c00410441d003018000c100d1a040010031000f142c111884115460030000100d000402020840c14175a00804e004a6103c4c1d00200e03014000e0084c1c41030a03014040f075900004290365028000000300c2107600c001450b81c3e15071805540000742060142500500d060003160100d40d80141038034a0007828523030a503100c05103a1440d903002c490501c13000003c06200c0c403c80c0e2141d00c5039112507035034082018540c6200a2521400b6200c0c6203100000408280b0040a9a054900c0b47c541240c0e02d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 490947338 1250 490946088 490946123
    0x10f060509030a0602160c0f03080702120a0c090914011b1209210e040e25120302030702030f1609230a060810090510022a030406140c0703 61
    0x103142c2e60f560080c0040c1d00009480c103036541d0382c00c0c00c1140f03170740169181801d186d210501180c6140135840301400c409414800d0f20003500c0c1a41d010781909001008540050300c182e5180100300700c01c2d070300103010181d4840300801070040740045410300e0040c01c4005c004102c0381c42c4000c2c3c001d412a1030500100043c5e000f00e286030144540c0b00d070184c250070116402035a1024910f40440801d046007410019240e2403c5c00580d01b010300900c0130100000001c3c150103100c80c407092800c0b2481003150701140270880b10020ba500803511003860b0060181d400755a40341c615005052500d1540302440c1b82950264208502da00001c2c698401511080c0c9000f04281a03000d6440b40115694891084980048000c2c080310721116408081105c0f0794009a540c1c0704108440c2000b211504c1c003010b04503800a0079035103400da030194004c0004040c0c104200c4074914060707503001c01c00098854541029400020180310503074210308400c00605040c0d0759186806880d101003a203030b44403840000d00340e0010185070100b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 490948588 1250 490947338 490947343
    0xf070905100e0f15030312070806010903080301030c170d0f0c061d06070f05090a140a0f030602031e16080a0f18060c020c091305030909040501050406050906010f06050903 75
    0x62042c07186080480c1001c1619484480c802d4407106941e0034030042d00b8100b4100402554020b07210340203440c00c035940300e00090f0344e03044e0003c000504002000102000040030000618042c4d40250300c54000f00e0b040040c0356444800010292041da40302000340e1101c1540050780190b100864904601145200c0c82c207007024008801800303034283c44041800e0084200084d44134420740d400d5880e000e14086030340080d2107030b21030040c1054200b40c451100b0301c0780a102280c08031408a0141c082d041c3c603540c580d6405c61023902a0001c65801d9000010300c10a138070b2040f010040c41c070400c4a48041da00341080307540c3e0310212664105041c0600100000c034a6142944040325803003544206005c1c0146018600752080042101143c0c500d10b020b00c4000710610001d01c40140308000f4001604a4582d0901c0c01c041e00c140100440d000d103c204891981c2c0d4075150761550017644038a0000c1014180ba203800800d581004010581d40e81c4440c004000c1c946591040c44100c41e000d0034075070b5540840001290 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 490949838 1250 490948588 490948621
    0x108010b042313142a0912060708101509030f0c05120705031506011b060b2110050f0601030e0a05070b070b10081c020102131e06020f070905 62
    0x2030703210003812010031851402c1e804c25200090000150041d036581c0b03480d414201e201c091122440d4507080020b2940882e800c0d4020301603044018260503400300f031100c0c0c803031601c81c04540f0702d000600000c050106110f020603d400181c0710400c40b4140034003a400c00180480c80500c005401d10201c814a00c042c0462401200c001d410b02402080181c91a909050b5440f015803141c217004e4491007045111010f8020207003070090f20140d40303032008042c400303016a1300701405e82801c0e690300f03558400c601215036811400010101d02e0440c180301305440c0310481414251480c078403007052070410041028060344103a006900c51024200060345002c4a14840d00c0e0101030f24004190703208e1000c001c510b411501c4080d1214910521005808ad83d4806000100302524840d590b00303940b01001c1d21901e2910441e0310740180e07040384001401c0000400150351204510b42c09460800b40d0820050600303d040e404084c05025540000d000b000d4240040e0381d903560309445038080040d500c202050040c103a064112 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 490951088 1250 490949838 490949909
    0xc0f08090d0c0303050a110c090105090c0d060623210915090309030c0d050304060815090703060f09091520030c04050a05010f230c010e0601140108010b04 68
    0x24880d00d84c60090440c1e441001440d02041103c141914401c3c00042d0800f5004000b9010303480030b034641428003441e05030151130800e041100788100300c400d41603072060344010305140c2d488242c101d0702140e480d003114501003546044040200701601000041c40b800c002c0c100d580702a80400c0ea030700d80c0030031170400b980220b81200c080031490901240c840008050004414200c042c1e500e80c5010200300400c50324880401801e0343c10600c0b0801110303000b00403041c1d11441104058100c000b61a001985040c1c003240d001c408255541b00911040051903030180107407000b80c0c0100564905503e031185c940152101c0540c500e51503c2c08512905100c107034000c5c58942d40c005440d102c2c10300c1f450010403900240a9240504401c1c5c0c00090150301c1a40048150001600c810110a410103041c1e405000111000f401d500000c0201168443c024420420382810000140c0a0755060441c0c00c080e00071648113082c10881c101c0014407001d18a00200c0f0101c842041e0702c84861160010180d000b41c103d20441e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 490952338 1250 490951088 490951103
    0x1c032a120c021b12030c06190e07060315120f15150b090a030f08070b070e060a08040615090f05090309030c0d05190b0f0702121b030c06011e060c0f08090d 68
    0x5564104c4000844a02440c0070345805d5423208070000e151400c9410480c00550300e42e0058108001e500e0003a8007954a0304104400022815250554000000c40010341214084883c81141061100003412100c5829007854144140c1c21460021061700d8040e000707076415540c0014500c54191303030712032903a0011584002050ba5000e12418812041c1d004030304103079441a01c4000298000d486130a5904a8030030050001d400c0000c10034084a000d1402042296001d645003882007220045440c440e0040255040200c0c920f01140b00280c10342d5400351010600d580b091101104035540498212450b50741030343d02203507110060409074600848103110002464103101c44009208549409920644514025010307031713206d045040303079030300b07024400c04060301c1c03060007d9034410b660054102406032000080782d0411402a54850a083d400e03400311520180c4a0b03900f00d43e0541d05c0b40302030000c1c103a60824060841e0035840f06c03c007201030508002c0811000089042080d640c1c1800e100549801040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 490953588 1250 490952338 490952347
    0x11011e27080319091d04151109040e06060603040b071e030b0103050f06010c02150403170a1106010b0d0c11030c0f100e1c032a120c021b1203 62
    0x30954890340440005039601101900064089010b10100d4046580c1d00d0700c4401050910b031010025030345c01900843d540484901c043e00010114015525a100e4820149582c1c5440c1c02c100030890f002c00081340c0040e0000810003220740d03036207416260f10907040040d0304156074552404840760b00300c03e16800703018000301d1440326855926511247e0300d40420789040080ba21110050b00103c2001c54015000500b030a60542c0181024680c001e40c055140112604054683e96980410400a010b0307456054012807049515030b070100b180060340d404240908002d5050002d102c0c80d0b4401d00014220360368507108203000c098030800040102200c420309894440124444080d2984014464200d1030b1080889802e90807132144140315180d1000401007040c0340368280c076180c0c03410b110000c010502d40d480642c406160011413101109400141139011b4902c9810b1000c0d048202e001a4000d5061420103030640e41900081c0251000c0d0b40c0003071281c0d40001180009904801c0311a551030700b40070105c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 490954838 1250 490953588 490953599
    0x6090d08121303080c03011401031109032e1e020307090b040e090609010515041a211908071e080c0f060a020703050406050a12020307090311011e27 65
    0xa0039a0b03a500c203030394403100c41d00c0d00c0080f4a0305000038000e0700c04942291144044560103070b40201d80c5000302071006420940004000f0381000c0200440c2c00c44212081c2d5142001700c0e02c440c05c16082c141140080015038100310000600c40d940e030401511080d40000850201402409034000030302c1c00c80c000a1f5140e4035980484540306c0181c078829001c4c845c00020038441001030148510a1000b0903011480712900c100700800350080c50301e4450303059201e0042e101d842c4c07200e512a203007407070a040614541789011000c1c6450180006406407a0b0740019003d07200107a0b0010407a075005800c180350800c010804c0da001030300744203603c00007061654001031340e802e00803010420043d100c0c9000283d07200e540d203409841c0168414030000800084040000380030307840c0034801a040c0340a003446c20444402c0752408840483c1d100303075552004203402c030f10704004000d443e8801d041003840030b01e004400c1000440032078a5804a0810300d00034800410300350100744900001481e015050032800c22245965234 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 490956088 1250 490954838 490954861
    0x50304020d0c0812190c0210050703230a170601050412060209030a050706020c060903150c0d1815021603080601050702130c020d080907090f090501090c060315030206090d0812 77
    0x600c034456074026100c1c203503140302d4050740700c1b00801500503160560002d2403000403501c6a01140d000c809005c80058035070220740c0c40c2801d240c501000002070564030712403114003604074299003d07035040c01d252940402c030b2140d80c000d065a046565410154007109050310380400607006440701c40c6d4140c420090201c0500c1070008030340f42140c2c11a000e5802e4003861005210061043c0c0c0d0304c45825234000030301c055120112074500c56000d103100000b60b080001d590498019603840c1ca00c03d102140d040400c25052000400104039807102c441c0046150103214000f100480b8030342c01000d0103000142000a0069005904031440700ba401080c20500c0b0a909502000511140345c8400044c0300c1c2e0801040480e014003581800b521400e0000c04140d4138000d911400b81580607508180e05031a003040900044003400f6401c0450f100d8011007e5050a010006044401541203c1c6180084003000c0015884800445011800545002c50140010300303040350680b00c0c00030420301d6061000308100000440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 490957338 1250 490956088 490956097
    0x50c030d090c050f0f0d0512130f0b0c1c05210a0c02010c050403140c0a0e0601030b0109121b0509010324060302090115090f14150406050304020d0c0812 67
    0x2038407082000b81c1d110002e00c0850f0380c0c80c845094210760001e01c0041d8074600124941c01c1c0300c2c403900071550707500504444441a038010f40d0840e214105441028071440a942400001501d03102c0d00c040d0509010a01071075031800d2803018002662906051078140611480849448090103000c00301c0c955800018942d043d40106ca000c884a03142c5000f0301001481030140304a9124540e41d0a03041604680b1942c427000007410100003035204440907181c06450340c00700e0200520382d0440100041c41c1200026041e1880c01c2402d85c10441c0c21003041c001c0112a030f019410340f5800c0070450b10340000a664103003120034560811940140018000000c00102000c941c904a071019180340c0f80110800703099051b03507954007000754408441001408580a0f9100305801c40701c0614103030300440d54641c038038582d00070140c1011a4400d68100e0142090908001081314880c8078000d40d85442d20f0100000c1403400003070030091151440044940611046501c6140034160343c00c19a16180141803080356603612 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 490958588 1250 490957338 490957343
    0x5010305011a09060309030d0c05071101020d020d2f01060302030709050c0906070f020415050a06090f0b1b0105070201090204050f1905061306030b100f14010f050c030d09 75
    0x809002003503102c507000007280700e0500410b0150901c082c9000300300c41e941004044549034401030042104a01c024003c085070554a074451075070303824890030404a0b1039841001e40341994800c0410f110559400254400d49890b2072810031803c500d840c180c00e035140300c22032030703018180c1224141c1a600319041d440034089a00c01c50494031055036410340101030702c0085032003050781c0c6003d202c0440242032800003800114424400203680c0109540020200c3e000703119a540c016006040038010f50900c50408006090603003400c41c902481c01d4000101600e040c09443c100c00408190301d501e944252090b1880304c05444024440741c645128024000d1155040581c415400c02d0042058100c4071455640180c095603921440701c00402e0080d80507120141445400c1001c24800691603000c0c6c3c411000a5441070507190300030705001400b070300703108496004400d0f58100b0417020444000d0790340d200d0000c138100307007401e80081c0100039007035941c0d0040f01d9001c9143d02000928024851a5600c1004000e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 490959838 1250 490958588 490958591
    0x1404080d150b0d02070305300109020f0306040e0a0b090f0c15030406050415020a090302030c061201030f0c090f02091002061e0402122505030a030807081519050103 72
    0x1410300400c0000510540301e407801886040002c19a4003000307400401c2054001d082103454214402944c070781c0d07150720681c440707501e48d0100540000c80122010190040140318000d41c10107098014a4295102c042d003600d11683c2c2e5222580404601405451003042d00461610194941a0105620794554525080320740c05581014903180c46d01c08404143d5190741181075007990703900d0769164001e0402034020b031289919000b6519510043d40014407000d600c82e59002001072031441854504440641c2280c4035100611900550342001e64100f4110390300310a92824034140342c1000d02003c42181c10040b0002d041c0400b13442d28614940040503083c00c2a90a00c0b0803a600180c12038603100107640e560800c0500c104a4032107402c07159416034000e8002450320b4100c02492010b07a1071b011010403030700c3c0101540c80d007449c100b0600b1480e0a008140582c060309a810003594010303d68100108a00d0a100c2c0e100049843c940540306880c4515101401510f18001c0d2280c60300030051080c452a03000a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 490961088 1250 490959838 490959851
    0x70f030605011e0807030603050712020108100b030f040303090203011d060f16050a05090a0e190501030b0c0304110405010305030319200a110a11040b03010504241404080d 75
    0xd501ca44541403214928554071140f003ea18582200c814002411140416407500030100100b08148034040007402c002180f10705c81a540e1001405032800240100041118400c00300f128100c020112980120040d601c080c1a0b9900d00e03050700107040f08180a0341541c03030305404454040d1410605c00032685998100d82117540c1b1807a65502d40d24003240d0340707212100f011000112284c014406050740c40d0a40c180385050a074030f0b40103c0e60794040c50744440c10504040090000848205500c2c0361090a020018042d40d03040d92200c0c2c10900019290848040c00000050180322041d0b0850328140d80041c000e1183c0d503036a09000b070340d0350405d840c0321b031518080c1c0d4000400000320b481000b1308030b0b400c01c8000c602944039406000c0c9a130041404042030103004c003500905400c0520030800400c2c842c00000d41000c01c2201030208407051000240e00a80c0341c02c3c180404150b8051002d11190908202c00c14401040403580d00034040090320781c02001380b00c0c1c051004022010703001c0c20940c411800e0401a8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 490962338 1250 490961088 490961099
    0x4050a080c0109060b1e1c0f0c1e0303020d0c02041b0206010e1f03080a050c06010f030303181e02060d020a110c011407030305070219151a0105090423070f0306 70
    0x149440e007441d50a00c80284850005603003012000800c002d03900c7c3e844051400c40c1c075200d0312203031188110202c1e10044030740030511040c0d10380409001d880c084600d1014070310b400d559001e0745d04c01140048909011000d0407803411561540c05c444800e20307800350410300e254008040690340700001e0180080e01891900080c84451440700c017403114403800081140240d00e0350b1900541640b000024900b00401048444042c407810410140240344268210b507020f45141001811503503a0303080d00c28000035040c03d610100f4030a0440110085c2d225401c4c85401c00d00d403000569030f2148410402c41180081291501281c01c01034031900d690160003540d07280444100111100c04000d09008034043c1d0610200c00807170b100e50300ca01e5100146004036090000c421101ca4608404aa000c03a902104603c043c02c20b1007507806030b00d100c0b223002d445081160900d81c0020307046004250280c3e0103503580d0f07580c0410400312207045440362180d04417590040d0810002c01030035201a20043e6021a0502400040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 490963588 1250 490962338 490962349
    0x609110f01030b030c01081503071d0f040b060f0d05010612020f03010902010912050a05061006030c080c030a1a04020f1207020303010305031902150106021c030605130504050a080c0109060b 83
    0x1200100200070700103041a5600640c0c90047c09800100e002c010484940140d8a040183c0301c003409018542c2c04400246441c05240d44800070503c414180c4101c082c800040c220500c01c03600410304907000c0081c103001101284c1c250b03403c440054140d600308080000c01e19010008020f40600980380764451540d400c0c00d060a80303244020080c000383d2450340800c01c410943c61110380b0700e03100700103a442100d556180d4611303003c016103041113500840d0303108210740340d010710540412205600304401241313054200020540802041c0003045a1160724941580019002910a4450040086455021918011aa17030308a512101c410711080000f058010b800041603c2c103d951043c0114a48100d0300f94a426031003103081500103600c03419548404004940d101075028101e01c0d030080000e420f0004c801600a401d40e240390040c513150540520140d00c540302480d4202072690000b01b0300e615549030041c0380040c0110041c20a030000f080d00035900106400c09007141d13004410501440014004111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 490964838 1250 490963588 490963601
    0x7120204181104031704050f01020a02090c090105040b030a06050a080609030403080723151e010b0a0e120d140313020d030306080307110306090d1d06070609110f0103 73
    0x10468010440070185400c5070002078001d5005414541825a01da40d910300a0882c00010182501c0204d01072105040641600d45820000d20040c0840e145580120707030181c4016044843e545e4000801e03454690107a41160000c0c603444c028542d49140094030140182034601403184202c85614001403480f80028400b400385c0c0e40386014500e8141740d40d540301501e50120070101c8603100000fa201131556a403034401071010200e8401b5160003401940c480082d4070009000640c040003100f1301d41c01d915024110b0fa415038003d692079070f0f0f6500c42034805648a03000c044030b0351380c000c8404840100c82c1001240c903109124141d01c3e114030988103449100c2d10380c0411118111480003c24914000d813414664100740540242400980680c032102d000b401c50f800741c030b010303101c004c081803c5200c5414100042c9a0020003100505803d0f47e012000900c0041c4601102001c4c0c510030701c241d429596110100c1e00d8150340311008019010301445c0c400e240e03002c480c100364401ca48680c85524154041d01624 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 490966088 1250 490964838 490964849
    0x90215040b0f0304020a0308220b1602040b03011b1106090318010c1103010c05131502120711060412060b10090b0c10090b250206130201050c0a0b07120204 68
    0x250420b008030b049220290802003084e07030300080a00d000004685030200a1401140b048116200129040307060018400b030b40d0302c00b5a0090b810014200c104441c6042c900c44943d040380c0208002a441001a0141480c0c00d01c441d2041c01140c1c542c41101e40080913003060115a0f030a030b070342d02c0d6070300b440803610303070244041d8910411085086041030750310401b101e0302d00074401c03a00169280c28200100b821035052411500c042440000c0901070803022115100087c0758103420f020281803d900d0080d00c0d102c12403490550160301041c41e00c1000100e004040203020007800341074179159500d00740e00c4c01514041080e29140c2c580600c5c0e05c424188440004206c0c2080e8030340f85a0b8a00d0680d110509601c448200704d03c0b8040d50700e200003045203a020704070b9402e00a288408060800507000d90744250000b0f034030310042c1c0740802e003000c42036008181d1a41c00780001c9880507504946000503510340c03160300040092402503001c5030b400c00c0b202026040c0104801e6841694401c150141c0404030720490161 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 490967338 1250 490966088 490966109
    0xc030609061309120302030601020c03032a0a0501020307050a0807020c0117070509090901060f08160302100302070803090607020118021818030f0315090105060904050402040b100309021504 83
    0x7078140d05041c408114012401c1500040e18100c0d5116401d1074101c840c040700c0000e4002017030015541e070411001c021160110081c5140c8000c0c811104c16103c805810200400740b801070394000018184410b04040d41c20030000d551744d1074004130040555010030035550204a1440c0401c1110788002500413051a041c0c548000d040340c680010304085000400004c100f0500b00100001e644403041503a020300c40b014000720781c280c200f0300c00406442c0150000601640300b1106032040202c101d40c402c08903078060342c80c2c12540e00711040c110042d02c41d81c907020b007064000000b80607441100081040c4149070039802040604041030781265070469039400a9804000c003113410303501c0c0d2501441d007500300d0390700005d11000a1311542200e0942e0030248160b1222100441007091502030340342120880d0350b0840b810b0030190304110003c0d5450184058690045994000050440d2110303403140942007002010b60440c00381c5041c0040241450102c100d0007424424007900503280410151070607901c91914 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 490968588 1250 490967338 490967341
    0x90504050a09032c03070b0d200307030e07090903080402030601050402040b0a270b0c06010608190902040f0612021c03020a2a0308030108011d0316021212030f0c030609 74
    0x914054011340b0030900c1c10074070401d2203074a400ea94200000b00061002074010b6469454010aa10803903401c0b03909080e000c04c2e42c1c550450145800c00449501c4010b074140040d80208a141d0a4603249941e0468207109190151aa0506801400c010322503442201210401d07a00c2da420710041c1d000d544103140c04443c0c1030194081d01ca01031030242003403070304122500140085d07075003001040c9403450b0f00c12901c2080005100d802d6480910800e8003500882c1000b500900b481507021000800d20b40d000168241e558100504656450308080840c188082051200c903489003070080650f03420324401c92286014860032a402c1c800f0035902c501040e01600030701813030201c0f507e070751008450307200d007144840315211100040620800c400c10301542c01007804a84a60400327103080d084031b10b1081406120307002040f51680044c4000216144500d641800b41c100008a1020940c190a04c00c0128102c1c02602c00c580f806100002c00f842c80f91441504020694444000c07961036803005403002c2c0e0700442c03400e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 490969838 1250 490968588 490968617
    0x9150305031c020c0a0f15060501090603020d1416020d0215010302040507050c030a05190813081e07080c0106050604150302160501150e09010c0512060f10090504050a0903 75
    0x1144401c0038450301005841c000760346404500f4044505d078200d0301d0026610a02003070101d000d100501c0908802e80c200200c0e401c08001074545800d5201d01001c02d03030002000080390f109a0400ba0300042242c60210003810314194060200c1c41c6008120014400e4000d04086e40b480080c0c070040113200c0e46508030203070342143c0a120142030b00070440000d00c24100280340c2c03020401c000030f003240c010381e640300d5441d0312030703801e5060b0000c44600031034041051140520560300f135040618180345600805069031406298120506d4500c02c0244031310804020a0003000e0044890040000c1a07a9600811040743c444040200e2409203000d10682e8680642c0e0281c0114040d038002c1481060005065514055a0b501c10742903c80444070289442e04050040200c00017502d02c1a8201106c940240050300d030750381004045028a26840d0903c0e07422001244003602d42a0526491040c0a886205810140380c0050040c02e01032055074012480c220000318410070600c03507505400e81c03541d10040320f0314114 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 490971088 1250 490969838 490969867
    0x901080408090d02031e07120201320a0206100e10090906110f0903010b03030309030703140f0301080610060e060f0901030b041d010e19120507050102030703060915030503 75
    0xc1c2c00d9603000842108040c0150360f0410a8410004000140160b00c420a561a80c10001158000315502c1c11443e410320041c0e0700b00d012184184414010b2400c5942120303208103960110410032250304d207000904000300743c3d001c00d5031481081804e4101a41c50740e036002002070400115021540c142c5140800e01072041a60442c104650141c2c0c008240c1c0c0f0300300301c1e07600d00c180d003c840703022500c1800040101141c103082c001c3c169121300031400f0710f003180b40c0801da8540340c3c86101130040801c0620503106204840c06415136405900e42482c8a440351785617003815660311003ea500403001a2403000010302c892007140300842d0800d010384058141200301a002e41ca40c2c1012145d141495100e1010003a580c0b100e102c0c1d80310441902080321802050100c0c0982122440320342e100300e0340c00000307818003d8291144260821035015503403003868820154103c500e40120700e00100154000030503c0101d0782c4c5078004200b82c0d40040b03010083d5071120700c03107030101c01031900c4014440d4005000803d51003000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 490972338 1250 490971088 490971097
    0x101d0f01080403110c0a0f050f0910050d15090605091507090902032502030418090f260d060302090a091101260103060906110301060815040e011a12030901080408 71
    0x11401160b5440c5c02e0100090b100a1041d0072080c10146000410403507450500c2c0c1c40f12540380d042c0d541d4101418600b00c12190655540100c40c00707a01c001003e101000300c4060f4170219a1700b03080382000254190304c2c2c92000380c00262210211307807080081001c0030040a00c40180600c03c079864008410349006030450103034000030220319950b040d151000c080e414400c0e10341503120b42c2030b070301442c0c1d5a03086c9604003000c01c0c6820343d500d58540c6044010000a5404c682e0b55000f15000a80603480000ca6601d0012018010750240b604a90100c0c482c0d8440c0c000342c1000c01070b01c0c8200c41c500410790f40c19000000b281d94442000d401c041705158000840d5009001541b640c0c0815460710045103090b00880920480a03401101c006640341036040078404940305013050004c800c60903500e507524082c8002e100740d5000d080700301070b02c59041d0401d9280d9103d030700181080076040000c0c455800f8035180a04000e1100c900903004c0c15200c10b0743c0300e010401000310380818405031282d41c0c80352190307111405039410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 490973588 1250 490972338 490972367
    0xc080f0a09241b052706040b0706020910081e150316051302070f032105011202030d03051014040e0708160b0306010f080411101d0f01080403 62
    0x10021458900b0210081081100079007100007140d124000c60009401d00d2080101e9010000140321541210b101500385483c08a80d2156001c0c520744260b0004a06125640c4807201c0b183c0d000070524200100354000d460706400c2110700d404102c0004000350703059581101c0b9080b01d0040410185c11560400b0301d5640c2100450341c2d50700c90075034001d01003442c021030200b026600f1686000100042d2401d41c2035029850101401981485590741d100000c000075454000c050046a001c62900c900f004040d0700a00e01d0944002d0007a540d403482c941c00c02c0103542c10300340d0290050f400740319041340c0280a040d01400c00e8402071240d0b2032401c2a5001411103640304250301580f1010201c8091504104c010003404c003601c0075103a91200c1c07a80c1081555002d81c04001041c1050013004480e03030b0403c503410b8061001d81408030301a50781386031000b184503500f1903055120380c803840001031042d4071140100e48070b502c0500048160001e041003241d086003441d18540050f0f0418001400030340308030f400c90900c48 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 490974838 1250 490973588 490973603
    0xc0b070c02040f1d0d020706050318030a030c03051b030109110903010606030c0f0c0302030a080408130602060703060b0f030606071b0305061e090a120215190c080f0a09 74
    0x4001d40c0007405880d04450301c14031658941c04000c03103035009500400c88440103e001411440d0f0074650294503041a485000e00344a03021000600a010b620300e03070003140134800300340d964400b01d0500240040041e00030980000f85400001490f4181140d95010030280b07428001d41103078030f090580c1c0082c00d02d003160042904400c0c8504000c2d074500340118805420036840c0452000500d02008107100e030501211b004204201c68000046a0044110748103007240f860003e600f9543d1f4101608a8481d004488011045000d400500e465003c29098080c000660b014800070745d580c20b05680718020383d940da086580d001c0010550a141c480d00401605104030f180c040000c0d8119141c40c40d02031190700070390f00c03500540304021083c504003c000700e80502d2501800c8007070418024499803021740725070080c004400c0c003140e800708074003c22640b0302c0d141170345c0c3d044211031807c1802da988059201e13100c0b41740182440b558000306d0b4010100184610014420410079695880200018000d88142a01c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 490976088 1250 490974838 490974857
    0x90d09080c150c0c091003020f1012050705070f050618010e03160c0e090106091803361403070801090321060e090a030e100e0103110c03071406070509010c0b07 70
    0x145c5444809902c02e800c0411410010f0745140180400d0540100d0400d20650300034101c0d8060305d40191070800110000c0070002081c0e50b800000b91603a1144400103020480c50100394020010005481c074422030180f8100c00041540c03001c02ea003a41c4042000d03c5803a0818800461000c15200f4007010b064003c1480015055032000300ea185420700751142e400c5030351240014810300070180240f00717905c0206a40340d4003040907520020001062400004020072002c401c071a00095880107090f94102d51030440f540a680c1d071002d8205030301c030010406006e80200c1c040081c5240043c8107110140740c1540b01c090043c1112143ca1b41003d444608290203196601800b203040501c2040303941c49440c82c440105821f10480c02c1c090100743c03202c0c60a40c415a012040509000d030700c10080b2458600030b080204058450040117650307030081541d502c807248804941c2209010041c60407441c511240030990341c903500c0c1d6030400c0740c040c81a40032035808101c03142207a00020380c82d00503850b44000c4a02d40000107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 490977338 1250 490976088 490976113
    0xf340905010f02031831150e01060f0c1b030b0a02030c12070512010b04050906040509030f0903010b031b211f0905060709170105010321090e090d09080c150c 69
    0x200207045036151650025004400a4142d1b40e125007500c01403084100080e4924100b05501c024605016510402c182d03402c14101840c05030510880c91644480900b00c000e10612000038401140d100c10745d0041d800c0e0012030b00d4440e49100303c07400303851008040c0303207085600e003801601d003d00a02981b003000710800140d101c1d82a17011180e4084c01452565960f0b461500c0d0403c00440c0f070160013103201310324241c144000494000111a2082141c014564a9000c11400207005203a20b02d507850f0180140d000301c08003401110400f000d236a00031075a03a05440c00e039185142803840b50340032003440e9038000f45015842000c3d2460041d10707111008404101600650ba078107082c5a4117440800c0410000042031000180b40c40c0042205800030000308881d40c0745407074460000c82c40d80d0a002c403400c1c28409038200d46208410032009064210062001030800880346c43e40e0fa202c041c114800600320180102d007255002c10b0440805400400388081e20803038a08140d441d51004007102c02318403811905146 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 490978588 1250 490977338 490977379
    0x9061b030f02120a120606180510031112071713020d020d06021204020a210b060409120503040c050a030521090406080a050f0d080f340905010f020318 66
    0x1d00c0543d0305e81e0303101d8004800101c00e44100e038102c8414012241e000c1900305001301040c40445008442442c600c69040303000390018113005102280660f40003a003030395038080703045145006920b41d41d40c40303062fa032407c2030b0a031500100303036102e00d50151254540b1026242100b66000e0050004214051002d465600c6074100c0e8401c5501710420011001080b0640c680000a080203180d6003050700065282c030150444049400880201a036102e807001c60843c0e02c17203038003082516a01051110040c00e0500b0090f20642040380c045415902906020995040c41041c0c9800ca80c1d002c00205807170702280004034210070412078110140901403001c5440307540c5070701a407002000001d0281c90241210b061203810054400e0405000703921000d4110a280e40c4001203540c0b1484100d20301010b600c442c000d001e80c440044111000c100f03c003483c1511003107001f51900d0503e24035034a400444983d204015201015a12080805600140007010f8025500d000301c400c4c0c0310380202251a8011a0241c001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 490979838 1250 490978588 490978597
    0x91e0606081e1006030504140f1b0d02010e01050a1206121b062a0c0306050906090c060901110109020a030501060e01081218012003030709061b030f0212 67
    0x1910704010311240c40c4486841e6600c440c403039800081c4602d081000e000f5140c0d8248203080070180d0360300000f000c0c802c041c80d5080e05032480509440d208a03170020082d581300e801c3c1001c07125410034564200424038010090300041035060312040d10708400e810064815030015024882401288030702038031492818031030880031b00144107140308a440b003820410000d010302c52601d04003681c520018401107070480c0c100e140c0748180880c084c80c9284120401030006140010044c250250349001008101407900961303c61a101400c40303885954035520950307038180090740707250003240400c040a2503500c035000d0345101122074400070500d200a5404120090020391061340c990b55501014004d4188801025005100c410014040702c02690125480c5100301169110310b800c02d40030306070550b4080e003c004000101601d0310398000008030403a80c2c80354011103541000420384980810928000d1110b2600720002c403594010181c82d6507402d4441608400307501055200c0d81d084000001030340300040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 490981088 1250 490979838 490979849
    0x60625060501090b01030509070b07080c0303010f17061014040e122101080705042304030e010201050903042103021c0903020f0d02090403030f0209030a060506030d08040c091e06 78
    0x495625000c0e180088454500d004c604150806d8280300b442e000004201060312b0824a0855440000e80f92a201d60f10a01c6c8070414640000300c000140030024498000441320190b41000c2c4030360005003225103500003103840100b0032408500c24000d01c003901c41034411010000d0310002d0808000007240307140c0f8090720304102c0c1900c400505060a414104030310340304100c0045d03c98003a03504152240b5281c000a01400d40255030343c441c40d15161790408000b0840707044038a0689400c1c2400d0a0040804191248160141d070815001c038540c500c0020071541103902039070107425800500f040741042070018070419011403090b000c284505011000c0c0350301c403802e8107480e403040003440e52052051790202d501d0601d00ca01560800070000d07847e20400e02d98001c0d4586070004900a485000c81e000b8000e5503411034052180b100c007981000459030220740140802c40071141c6140302804210b81c81203044800520340403e80b801006140c00580044440c0c004105448140042d0400300c2d104440895101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 490982338 1250 490981088 490981091
    0x3071a0913060305060c0c0c360907030807060207230610050f01051b030a20060103050a12140313060b01112503050105041211070e06062506 62
    0x100340181c60980990840d51103920000d01c140c41c030710b4440d41d8803040020f200300e0f0780000c000f40500a03040c080c8903174240718100411003001e501c1c81e0041461404002c001d14a114a5a201032010301040d0404151280d5450001421b80b0b5085541d03000d9280c00c500c030201c1e0362640901034800000c00e141400c9201d801c018000b0020752803c14810381c501540509114805204140103000e151100400307005441c0080c20100d903680105045104407038407101151042c0e002c0481c10000d20380d407140c1c0b4842d0112820314546034105840c89002c0c2c60308002e01c001400d590101085100007101311110711201480c0e41071105c40c2940c240f0a082c0c0c2684126240a2030114070260301d420059180701e2913074200000c0c078010f8a540c1e03c5800e416540e91403100d960000d1141c41c0146c103140400d40a02c00e02845e4080002c1c40b4a04061a040c4811350744005c0040c003140150728071a01400000030544211483d40303150a015450f0041844001d40c030258014442e0703061006910381891b244416629220302c1030a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 490983588 1250 490982338 490982347
    0xc0c020906060706200c19030f08060609030604110f030c0a030204051e28020702090a050604020d0f0c11060702030403060513060e071a041215090b01170d050f031503071a 75
    0x754107042080d1f10300001108001e1040c805c002c00d0b801860300011a1381401c000c0e45c1d17a01c0b500002000750040000c2150301d4030450703042000b08480740350a281c2c130f60f100b40d076410400740380c403400c05413142d01811b50070b508410200002c0000d40740540003a41c10001c81c184401d1070000074212000e04180440f1410000040d50300c0d041100320b02d0340251013081100203006c50424401307a0025200d003101401e5403003001c0d11040891100d50315641201c140c0c014103130080000c00315504d4500d014042c82c1c0020b2000c6440c90f89400211407011070014400c00055001d5407402e41580d4a08000707000c0a0050088803440e03158510000710113108054454080234000c1020f50700d49140001e04c28884005010352010900041000b00341c80341c030451120340e001420006803018448600c005214100024140c02030302d400010b0303492104e00c42d000000ca418425120b44d03032450f000903507080c0704560321402002070400c0010728072820307800c24070b0b10a00300a00f41c624040d0398143c0383d8030901c6540318200c010800000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 490984838 1250 490983588 490983607
    0x302150708041a07292404060326072d080a0305040b0a06120b1e0c21040b0406150e0106020115090c0804080706020712080108010c0c02090606070620 66
    0x2158a20015a00b034107120040050240d17003085010141030a0580100000c000c855141c3d8007400103c0400040c208120303160b66400d0003081d00445980c0e045025042039403001007402c503202101c013030a410a0041000600050494014030008001310301160809190000020b01c05401400c80c4046941c01241606207410720741c510110182404052515091040180101010b81c2c8800b250700806030b00c2043d540c00a020401c900554941c46034000032a04100300c0c016420302900304880501181c55404c5090584000150801e0b500980380040f00300c0003c0010f040340d00501400600c2c4100606aa81c0d100c54041c409442a000480940d449214400d042192103145c800201400c00c001d0026000d03020006c2c100720406007001d05910000598907050210503012036140a5121a0346041e02c561500000c20f031400a01811096508000c1f039025100d2041600b290380b031b0340013003a501203074503200100203041d40003e800300c41c501e454403880a100c2078210820074846500ca1000d035910304084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 490986088 1250 490984838 490984853
    0x20306030d020a051c1806050712030b0112021b010c09140a032006160305030708010e0402031c020a0209090615030d2703021009140402040302150708041a07 69
    0x410110003154032403140c000108900041c0c41c1c0c0c514104005000444117102800c54401901e4004820401080b4800050883e8424014840742d4080c141d00b000e0050258011420b41e9000340500e4002a00320182c07038615a016030092210030440380c80f07500b90b0405a00843d0a50b106660712401088041c1c0b400c02091f240d100c4d16510b000400c540a600a60541d0307556040708c12038460480211114900841168442074226080f210341601ea540c44800d652900800d6940115510f40007d03800e0070000170f12010480c000c5029541c010058602d22706c0300c20301c5885100c1000d0b5200114450b0419080241e01d96100c0240144007040c040c04007482c043c07114a1101491038503e602030342c49481d610700304681c0250040024500395912070306400d000c10468001e0207a580004c0e50000d074412001d0b80964026810800312034081038a40ea03560045000c01c0201d0003a48006900455076403031002e000e840319001001481e108507034080c2440e465000400c00000b5000803090414030000c2ca00081c06101c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 490987338 1250 490986088 490986103
    0x1a28030e071413050405190c0311010804020102030a030e070906081c080403021903020c130506090903090114070602070c032a03120c02010c051930141204030302030603 74
    0x1c844801c2c40611441c00030514180100e526070385410356070b001003410004184425642c44075031b030000c40c0c08003809051031540444184002c403031002903000d0845140d4080d00040d48510340503000381d410703e070001600b60040c100140d25140280104100410210101c2c0b00b81d0f0050300780000201000b208103c840140c221886d4280801d12000c28200000a0383c0014506850760400c01c18070b000c81d5452406074a00407001000581c407d8040800c1c1d94080d40d01d0380400c2c45483c00b1150380056883e4802e10548a2107680d400900180900000d80f20042d5100300900703c40c0d1103200d0040c0b07090a9a2202d01c80c1140c82d1704101c60540c0e140d1641409441d200d9010806168000c000c508810719659441105050303a042040c00d000d280940101961301a0a401410301d401c0404d80b090080701a403e151005501c40e01201c1101a89859088100d61442e03180d48910488006030fa41e00c190340419035545c0c60a07407103409200c00c104403107030309502170494090003144280c0700941c4074103020f0304250900c0c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 490988588 1250 490987338 490987349
    0x1401030b030105150d031b0b0708070c051c05040503100501030c0b04050a050d051c021609020711040b150f0901030e06060306060402160222060f1a28030e07 69
    0x40006100340c00700e64544010313216200300d40000761a0040c1c40d040d244200c0a03998001800d912090310401d00283d00006c03032007902c00380e0302c00d03002d41e8030810103945d0030314003c40280182c1e02c030302c0011117164103982103d1409031040c01c02d40d060030b41d1030000a140805291602c14803540340d10040082003011001200906420007496003031500b05404076403030114031b20410b84620030703c2002c40107021090204403854156071010f81d99518080d84060368800c420b050000401c0c0480c240010441010f00c00d4032078240c1c1c007040d01045210f03c0420440a0003000114907809100e0001c42c6101440e00e10051180324980140c158458400c90000b600f201c0d1f0024501806420070010000b0541e808286030358058821580141c64010b445030740c000160003480000c2d00403a4423a040c071450741d0500707000102100c0e05c10023032003000c0d100d000d002255100380c4101015401d00070000514003080c03a000c0c3c081d10001c240e080040b507901201c04e400d200108400e20005c03a0355003c00042080050007140080d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 490989838 1250 490988588 490988591
    0x260a020d180f082511030f2a01091d01080712020f1003020405040c0806130c140702010c120e0102010f060501020c0f030a23010c08010e1303090f1401030b0301 70
    0x54558a8121100c8440300c40107000d04000200a0019001c821841c10302d11014100741e0140305403407600364185c5a50700725051085c421051303c80c1c04204000741c415500581e101b100141ca800300562940015803596545052000d82d11010800c0c4400090052601d80e400880075099454880b149040c0710803034111496000d81358402c44003688810202d840a030b00250b410007000f6403840300480c020301407600041c1d070041c10542d000000071740c0f0130390f9107004540448000d0b400d5a440341110003210ba242d0851340104145082e404080041c0c00003a040090040c14020b103040401d99131000440d030904054404108414084ea0081d68240300b0080ba400d8410020040142071000113560b8285403082948545c2c403550402050752030074440401c41030380c0200703a409030f000000300b00c0041c0c815100c1441240e40c6401014424548640e802c941280d2020400800584800c5420003541d1640c0030142d00344494a2800501e54000d244103900422107021561815041c040006082e500d203400050310070f0307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 490991088 1250 490989838 490989881
    0xb06060f040e0a1d010f0f090507050126101701050903090d03020712060b15030f01030803071107060e030f12030705161e02090c030906040201260a020d 67
    0x100080c200e070152840000d41490541d07403402040c018004071410404d507100d02400040f41104150440406c0410040f001d0040c4c079060f646d600200d400280010b0300c103601c01c010403ca03030b5000b400b851001e03100070900300c41c001c50381210030a5110401c0d070740c0020202048000304554500c00300c0915406000360700030b116900b003e90000d40c2e6800b80752034280c4a0b003240c07410f8204241c020020000117000d500c003c900580e5a6040c5140180800781da41401a9001d251000040e80c141040303a100c1d108049080c071130340c0d09640302c1045030b800051984080c89003031001c40326284004c101f003030014030585c1d41707885034494044107040c1441a0200394520781d9100a1718420740cad90b03410b025254400302070b181181c0c5500b18010725045030064450007500440b2800300c420040880c00134003040150090f15940515254041444580c1c03000311000300d0aa00440045001588900407204032510382844000c1d0341140c1c458007d4140e00e041d0389010400c0d0340068001e41c014150b00940074000c412801d910040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 490992338 1250 490991088 490991107
    0x70c0602340806010b031503070602190602041d01150f08060f0a1d0a14060f040b040204211e020916050d09030201020d062304150306090507030b0606 66
    0x941ca4018254208842480010007099506440300001808418126400c6582d1030f2414100356005035244d6460020031102d403240d90400152000448039036074024005220180c00e00c0d0604102e0507422100e040d02004001400001ca2000e12105c10300304010280319490010310311004241001c03450140803107010040c44d09900300c03104a502035411b6400106040030000000c000c904550040002000840521206640340d201c0503889078100e65410040c4070314901410609200460b4603950240e00c90500d9080760038035822031441c0c050054030240c02d06484242d42141094190030410510030885a1402403185444060f8088406050b8a219008554002c038400510007041c034210742021000301c041c4c0900c42c03412a04103c940400c104900102403030024042d42c480d660003000a800c0080c0881ca0f0a0203528149048411141003041c1814450500c03029202c0c481c01d165030402d42d01400000325449000c1d030901c81d0300c1400a04001420b41c83c280702d00c00f00141450740a49820300a2109 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 490993588 1250 490992338 490992373
    0xe01091404020c0a05010501080a1103160b0c0703060606020a03180803040621140708160806041113140a0f060206060d020f030a051c031b0e010c0602040308070c0602 73
    0x31a0041a00c0c00340c1d44440400ca040c0c9400c0c0082d000500341d40ca061300005080201046002400d1b118640542d00784003070a040640e030718002c001d6004c3c481400c4404211503805a070042084000c218259942c0c16035a465110032240d95902c10000350708060b54603030070903a12020381e021074151050410456400c0c040d21a50b28001e9000301402d0203004400010300001100700c1030308440107600306015034654916072817007070101500d9240c00f0910010101d00650069041607200000c140e80307180744c40d564401084060301c3c2c1034041444a410030801021245500b121a00142011a80c07600c081c513407010a002600e90250700c908242c03503140303609111f541da0101e03180790803001c111a40e014840e8503000040303e6544030141d990b81481440300c0304c410801c010441745600700620700000b0440840040580a80301a140402c01d0842d00c80da4000803540110182c203800003062404000362003140c0c0c5c814003240c1c803e80051700d2144000c140002003003c1c58111401801d10761011788081c00a040810a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 490994838 1250 490993588 490993619
    0x204051005101701050d03140304050705090610020607080a06181a0607051f020c19050c011103090409111215010617060d030e031e0705150406030209010207050a03060b010e0109 78
    0x82c850346c0c0c82d24000c01810300c10851220034080601210740c0c2d9007014a4002d995030004d10415018401120009071140340c01c10050f240740c0d849401030900f0360340d006001c58203461300800d540c41a60b81c5e85008580c0b108226401d42140210031400181c11500080340382c00424200d482c50b114003000c018840c0042c80114408010313051150109255a032500300410203402a00703225000e0f846103402401c0c0c252009201422114025000c1e10301c1d00006d0001120141d110b2421035840d80e00402c8078240c7d6050541c804c0344c00e9406200c1908103444007100080340d560f00c01c402c000c100e071b000c0c2c880d1014050700c51030181e005010074205240704002e1000004c42078540108628401d064210304501414000c40c02014984002001d503062810002da28018084680d01d900d8043d00c00c03a90081101e00741901c2d4200c96036580a0703410b0074203180034412030281d03000031003141c11030194030070000d410384038212120041c1d0300c5402d0216640e0300c03403000100f81e4211012580e0410010440400c4244080300d81c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 490996088 1250 490994838 490994849
    0x2a060206180d05040b2109031309020901020c0603060409020409032007060816030f151802070b0f0703090203120a030b03010510210b01080601061403070504060c050a0204051005101701 81
    0x854a0341071820070242c482e12000c06c40d400d040d55001c00c02241000c0403008040d00c0d0080310b40d2040f465100c500340012406a0700f100c901603404a184040c0c240b8009010b140c1c00305c80184081035107021075020906403040e80e101103002c69034111944041986011179111030102000040c91420f140400042c0341c044090304100029800d6400c0000c1789200e038000304028050705105003d045c803184103055444101d803164401c92904200420802170a1f8006ca507070b803d4000e6100c0249403603201206020110150074001030558810380640140c50600012000080f1002d0700b9458a040882c0a02900c80124000b40b01c2e9140bc41000790304880c1c010040c0c1a10121744040302c0c29503c450359400440d01448002d443c81075a100002544a030008a290507100a0390b02c0c0e42010503403500c00156800195015800703c0e50501050100512540d1482100d50203a0110717803a0003460b4000c1422a03400f82d541c0342510103110818010b6007003010964010311254a0300e549441d40450402c1442903060055 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 490997338 1250 490996088 490996109
    0x914151e0402130c050414180c03060d060e0309090f040b010317040e09070906120308010e060a031a060306060a06090e09120a0306080115080a2a060206180d0504 71
    0x218040d9201c0740e2408410f12010482000500d00c1100043c0040e0490b200d450078003201c0d00081c2c0340718103280b8465114407035114004241138481e00030610840d08002c0c18583c00c05001050400490300c81e000d00301940020001450b034a00d1900140803268800074035010b00080700c0340074080000d04c0013919904494011021109149009000c505141b00d03d5000d02815800c1c04144003a886c400b0404000300c4941038010022076990710400c5248414841000d008a01483c00400c401010310000b140d10000081040148645039591410705a502c401e40c0c003249908201007084505040103801d4110300300301c4130030000320f1410100500003100c90003980320b422205004550303c0e02003000750310315143d06800c6441d00c40d240c00d03d0080050000d031040040660138034074020b50706003080ca250403d42d12071201419030580d50741c8410103d2400c0a0a1010150859070b0f1495080c5c007030007074800900b107254064003d6080c0082c81011004091a959440350003800440404641010884003111802a032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 490998588 1250 490997338 490997341
    0x1060e010f0318080909010801050903030a020901020a06181a0912070c0b030708071b120503090c042405030102031017030d06170d0e090601050d0e010914151e 70
    0x411000b8000c00303850a1983d0240c078043c3c40c1081310207806422003000584d001030441e0399038420b10382624400e85910366039410400c0070034031480c03640e001403180790b1060045079042043c07070352100111003802545440c200c408a0700842049120143c2c422110480b02100c030303d80c03d01121711511107400c100006c9500800144180400102840306ca004140341c0b81510717282d1911701c13805080d44000311030860004204110300225003074410104101035800c10320039400c0035902c0009881d50340c40030700041402d01c03901030601c445640b540200f2034400084903040c0d01d42c9016180000241900f500440d20a0f40180108a04800480711481c1115510014428090000c0c5441030031403007034903d00f100b485d04001000c0ba500c43d000400c41b2003100110201ea54580724880c08407680304004603010741c4556900c000c50050340c8204082c00f004003841074009100107521342d65a0851b005400103c81c050402408000408014442102c0210713800341000e40e1ba1905803d8079100320011004060710381800c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 490999838 1250 490998588 490998617
    0x18070c110301020a08190e030304151514030c180c070804030f050a0201110a0c1503180f0c121101080a0e030d06170f0717030c07060810050901060e01 66
    0x503a1000389480180c001c640e100c10107080104a00411520400aa10010725403111481e80340f18078201ca418000156003541c95a0792000b008800005150000707680722080c20f4050f1400380340120042c124030390341e4014204000141070508c031464000c2071148a802414043c00e0010800c9145e00c00b01c2a402c140d40c800d00f0380380c001a1409160405090600d442e40700754200080042c02d810014000d8071084091310300048020760701e00c091a40100421300c4050100442031041c08002a0700405003008905920400c8c0c410300e8040c00e0307440a0302c02c00da2030349205d0309010100140402501070311800000703400c500e4442c02540b2801c01d0400c0d042000c0d000000e45540d00300e034460038484030040e003076030342d50302511354032501038001c5011f80c603104944104408078994000801004000c00100a00135441ca01003170743c00b41c541c2440020240e80400c0141c404902002d0009101030702454485408a04141000c40742010841d0407050055244030018008142c04c602040014502480d0403d24050440c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 491001088 1250 490999838 490999853
    0xc02070f03120c08030f01030c091b030e0f0d02060a0506010c03051801020c1201050a050a020306100c0c09021b06100e01150c0b0108030a1d0a0b1e0d0203041118070c 73
    0x144081c08544c808402d000a0034100307512281240d009044c0441c01a80b6000039804903031141d00402c20b100b080004100b1098000e4200d400c0c24448042900c91400f02e10b803131281011000d031103100041c1c22990030410007000360302c5140c1e0002c40a00c0e01e510b482d2180c2d500901548590100865500750510322159244c0c0f0070040e00c800c0080141400750500070b40c03a10103019180950b09030800d103003800c0010702e4103a02032003528800c043c0200700e0b1030028901c1c482a1540c0a10002c02da80200c0743c0240820441c2c481d000800c0d41c03120101e1050881c0261000345400c000d800f41c9100c0c4151240c810811008a50402e0a415a4044600440200c0d940b440650711400c1d24500200040d894000010700b02c0c0000c00070304840c451a4035a003051080d204d60340e4801c09186000c8540c04023100b1018009616140040c002d03044000385040e540f054210b0403141c5c41e070070180b07580508a400000f04000c002031740611601c0500c1c01d5034a40b4801c504c1a001e48003020740105201d040248440e02441403002c0d6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 491002338 1250 491001088 491001107
    0x909160803070201081e0c0f132709080d0b062811030c0d0503060f0307080c18190b030a0f05072d050103050a09020414010311030304060f0e0f090906010503010c02070f0312 76
    0x802e090b001003a56030f1031710030400600b03d00160600d82c41080c01c03108ac0900741d008403501d455002007003516186091307101c2e20041c001240c4845d04600244403840b500c403542a1070810711084a4011005903030310500052444900361101101a003003440000c00c0100c0c00a4104014041410840d440f59120404900c2c1e0901c0c00c00203903850701c501440003480c50710100d00c503900a0f42c03c4e01c10b040038151481e0810104a000d23031b403040700100041d0500c0ea1325201c0383d12494103528010281d0784103101e1601c4940850794680c505441640007004c0c10400301c0464598525841e40000801d40305071040d11101651183e01c9c8607950505031500000f5003000010751001c00c01c654000d10070032044c8610101c980708148240000c07144940c181205541c02d1400200360740c1101c44642c0c1e1071440f01c5841000702c0d00040d80d440e003117821094001c828442ca644541085100d984c080000b41561b600d003504143c01c0d03503141741d401c900355044182c06110314213a4214580a1ba07400035640014054018000c50b0006030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 491003588 1250 491002338 491002357
    0x112030507031b30090305191a09010510090c0c0209070908120309060a0b031b0a1a0910031a12120a02060115020d0e0909160803070201081e0c0f 64
    0x9400c10130711203044080d1160b007605212102e45100c115184140c6014a01c0e001c05865039210000f240c41c0041002598030600f440f4008100d00403070701702010400c0c04002d0300c0820030f50351030300704000440c2400003001c0018001d090043c00380190088015241510b06500603000b40040000100858014035043d40208a43d01c2290900415580c8405080d0410740d048841030140c080411364031015402141e00000f801009426030110502c0241c0d01281d40048203500448801130008280120400c0c044001c66922010366403202100108206000070314503d030300341840d124504c80b00600803c90300000d01c3c001e0b6080104446c0c43d4040c149060180d02c194200c9000c0002c0d4130403025070203e012812111103802008050020b41030607a11035041080c540002403101540c1f000910b0203915050300202818103965010fa514041891105103503045000c1a0340000350721030465034450300300390b4030101d11003400d40d00c00f03080440401c0c55100a09800040c00340031070003100c0505c0450032650505c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 491004838 1250 491003588 491003603
    0xc0302060d110c0a060b06031023041109010305280f020f130812031b03061305010b03240a03021504240f05090a0303201e060112030507031b 62
    0x29020f501141d0300c03241014200d41e2607040c51802484e604050b41503a008101000200f541035003004451500c00005040401e0b46401120300301140c0c1d11a8881c00c010f04c8200d10040b66642c40400000d4141c1c1d901519480400030410141280c02181c000c039008484592000440c5100088005401a0296404000c2c0300800010442d54035410011060308585100c1c080c0d4035804421440402240002c5a40c01003041c44002c45e400001c200d07800656000000500d0660781411f007211481c11280260401c8001840003c2030010307490428000198060031501c03520341c10481d40000c078210056a102c02405204401e180d0b010082110060f10054282415115003100014200c00c1250f41408503c3c00400c0864405500c550720480481d0313500f0074080c0c200003a092071560101c42c00b90020304d50991102c22907980540c00780040c0060b8015808a031203201c003e5004d202d01c03905252060b801020400e071041c02100c0005c2c0c01c001a117500d6a090b040c030301d1030940d8642e020313098074502480007020f09 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 491006088 1250 491004838 491004847
    0x170f070c09050103060e03121b0409050708010806090c01020709110c0d030b0f0103060830040603200405030703030e041107150b030c01050d0905120f0a080708040c0302060d11 77
    0x1c5030690056040364040d040500100140d6044592280f181d010b02c0c2c1c01d201c10540020b0412001c208440b4400b03c2100e816501d03141da10a040400c4603002e407198400100c51400402040728104052500210303000040d0542400d02c400103551201907205288806032210110501d1052140544412138060f85c159203045013858002030042c0b0110460a101c2d44006039010600d5100e0711031481542e007858010500e40c075001140440f80c00918000e0200020100d8850000d107c140014000400e09903c1c0801c013054105822200000001e0b0380c44030a803818001000b2540d000500c00c400c03a6090b0034020301b203111420100d000341403010003a961003540054810300b08811946801980c0d91a03440070001504018101510b5292001400d40041c205005441c48514158400d83c5240d00c9502241d800c1c0c03021440360200e540102280c44c2d180b07907004c96041003250300561440c0d8040110f1810011301d03d415a0f4080010b5042d01000e400f5040c0459241d8682416a120409002c08050801d032207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 491007194 1106 491006088 491006099
    0x60717061c050f1b0414220f030e040e0c100f020115081c0908030d1116060203090f070e06010315030b010b030403110a170f070c 57
    0x41c5a0320642a80000d07404100e031004446901001e0308000800507081c3c0206075040024900650034255407400c2c0e049034031000ba510a03510300c160104580200365200c00460040700003003409044118090a140c4c02c800c0244050000300c50901c40007c41508854942c1103440e1703059082107014504015040c010203000411024500c0009030040174103004000e03541c50381d8804105a001864400c04075410714001e503000c54190b046c044541031603d0038159803449411112080d05658400c00001c16441c001150040e04040306200e54054045c180080254010388010710b0078450101c020a00c1900498034000326514620388862650b210801500942006200e0700420030f8201000b0000034000094039001c3d01901e502a620b91816103009403903071581c40420f49456201c1c001c940000340d4403180b40364421005c1014552030301401140400c19021b2208001c24401520501091 = true := by decide +kernel

theorem cover : BRFrame.Cov 490827338 491007194 := by
  have h0 := BRFrame.cov_init 490827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 490827338 ≤ n) (h2 : n < 491007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
