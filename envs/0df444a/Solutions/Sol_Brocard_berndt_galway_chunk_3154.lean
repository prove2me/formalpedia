-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3154
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:49:15.198178+00:00
-- url     : https://prove2.me/submissions/e6fda4a4-5602-4bdf-b5e5-f0d46468433f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 567086330 ≤ n < 567266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 567087580 1250 567086330 567086339
    0x8090f1203090c03010603120c1e030215060109230d0204051801050702072409080d030905011d0712110429010f0e04021303020d0c031a010b12040f0b04050601 70
    0xa0607443c06007940280c0c50000304002082c00e00709100015100360034441d031400e5045c10700288010449c1241d007280d404188c0c03000d04044d80022440c1c03803030340f05542c40f4200e41c03240e500454141e88284034040e000101d80300d6091020040e020340301d0b140c2400800c40c01501400e41d01040644100721b840711410719a40c060709000840038000e00350b20600502c041d0030041c3c10414510042d10115040042e03801000480c2009640a80e42c1c80010745442c9080724003284030100014080c3c4048201220a54200342c1c00e919030707103000740c0421188818080507208441c1007843c0c0c101c145d0000f213803d560b036820f0101091144c0c0c5662042215514103115504074440280007a210409034543e00c55042000c01c1800c021815800400c84000e0141254096507860380d2401c1420206410340001e94090000289034040002412442007180d01c02e40c404210441d006207100b50b10310b0709104054100404126847c000f10009084076480b900c07800316510592856203503040c03690000c65040302d031a84004018030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 567088830 1250 567087580 567087583
    0x90c010f090e011706361f0e0111130b0313081204110f0f090903070203100209012a020d02280302010e0f0f12031b0303160e060a08090f120309 63
    0x11b610a00040940c4500c02c40c0d810040800e030a100007144445002da11052180941407019020017480001e001980303262508002d00100003840c4911915841c100c4829402d603400c05c16a403003102c41305801c20390b051070054500001d0303000070801c80b0010040c140c10000511407401a01036a070768a510340c20b00389018501015541a0002d03018494100501c0d001415030f111f41086896200c150380340c100b00e403181074005156010302000254107008a0030443c41c2403607294040e245115090340d540c800400002e01e003814141003804902d0b00038000c26070f004007504103042c26001705480a00085152161081184108403810082c0c003201e0084400030025507070300c01c2c209954640b046880803442c10319140011054810601200c2c0900f00c1c60800720a4014284281c8130090103ea58400c080015070040329240c5d40200c81000540c0340555451030324500c500c000c6d03510b181c4c02030041440c0a40c41c0b0b1003910340020040600c0045d105008030313214054010f07c02000d640c40702180c1d6645a09044c030005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 567090080 1250 567088830 567088843
    0x21b030a121a040f06080f280b0406020f041a0307030c05030c0a0e031009033b010e040608101505030c01050708030411090103030806040507020105090c010f090e0117 73
    0x34188141000d050b000c0c0e140b099250828a42011100010036007038003403c240242800754480156801141000280001d012401d02c201c41d1181030452001c0020113508009519141e00c050b041c034500900080020b031265008000b0322500c000720a0620742e40d04a4500f09611884032100500ea01105120100b500340c059502591100c1c10210705514040001c0800c40c0542003a402c20809140c1304c00786542c8007402004040219035005112241f0b1909002d444407068802161609001000006611709020000382d0320383c240c3d180c00220481c20100446a41e0f4240422275846a84c034900001c8645041010411605680002254603880c1d244d03e1111810a0703840a0b010341c1094003500d0a40e80c0c00400c840102d035100825646a440c3da00700142e50041018000740c1001101c400803082c543c11005441c4921130407200bd00260342c2d03401c81242a5031041d25030403626409800350810382d601500d00104040014035040c0d50700b550f50f00c0441000392003030f0f0268030b0941c80055184507120040c00072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 567091330 1250 567090080 567090107
    0x90103030c123f060806040b0f0403020a060c180303021c05040302030709050417040b0d11070b0c031b0d0516050309060604090f060f0c120b06190201021b030a 70
    0x1d01e46202011407840f202c040c0c0840c002c1c05141c5800c00548503580d02c0b03030301094402c1120200525903c964440c0da0768003056806036410319030000000c43c911045c1d000180725130b60541c05800144020782c1d520000e4002681204244520540603031b22214082031500300650003a4010310418a00d0b08001c040982070400c450200042004140003613180017642504482052400050a42c4c40d400c210a02c2c40220b03070400403132000000c1c009a030600440c0a445070b079030112010005100c541d40312300141e02c20b095008000074040d00008551041681c00385d540a00309000200401504460201c815480b03080410251540c1d64140107a4461f103107001c018000c8107080444c80c42c2001242640d9520004060b2441107880740000d50402201c10450007103154000e000b8401e1501981d40c5001801c0d89100c4400015a1703050001c8031003d030b60040440541c4003a141d54a880107071901c412066000d030015405540d001c01c11030b20400d003000300c220b1400802e00007458580c091110000e00700d50380044c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 567092580 1250 567091330 567091337
    0xd0801060509011d03010216061406010c11011215031406130b0a05061f020a02040e07060f1407020d0c0f0b1804020c0c090a02070b18060f0a0b090103030c12 69
    0xd007102c0d90b0040aa103d000d29100c1c6560420342c00e00c0c002070702a215800d0104482e0325150200420400941c00c01004840905903030f0b0340036074030035004403071050550340040d050030359400c8070607082d5000e17003180001e010f803003900420382e0340d00002c610006000c00e61040313400c44600c2e0b40c0c190141006211040d00644129420180b8400d6a1640c190b402405017005542075900c0000c280c0d50707640c201c0c1c42d010a4990880162030b071242c111001c2d4990034440c806a004509140e22602240800310348401943c2e800e449400210740c00071021038140c0048044180203507010803200b00940d54001c50006054030a001c0c0791003960810a080b16081c000c0d0348822000c030700500914009040d20100500701080c180c40058441808015081c90243c2c13400c03580e9000740144041c014042065002811900e010700003230100b680f940640c4044060040081d111142c11450100380c40021300b01902d500311208d81c1740403c00c2e022840010b03c410300b00380d0048002c12420602c510812028a009005890f000d05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 567093830 1250 567092580 567092587
    0x60b0402270d0c15091d07080702010c080a0911130605011707020c010c0203100c02030a0207120809010804022719092604080f07050a05191809140d08010605 69
    0x3c2e2501c01002c244e0045241900c00070224044d001d10480c0004020000071040d001d02e600005002d04c5c86103010f0f1482d1001640c03d00000b400300c2d0050150030511205550b03100c0140d0740e135840e07080080181090490f03003000da0303070400b240315030b1580b0a8260000d502540010020310b841c0015000d17088030414404400051010002001e030045071141c02c141c1e080c2030480104005200107402c0060700500503180e145000c00107083d003a8004060650407086408032500941c6507108c0b10350860081200400c0c2800c02c1000e40b0543d407040780040c0d0418406060400c042d046000c589164040340720601d050910340304100103240340c02c170503070004160700d24400300000d109039210070b1118a15610019220400107248002d0303020312004482c010030f504401c0d5000c500d10f8090464440145110380b5109090300c800100380c1d442d001c030340c14400000d03078a03201983c1427030413940c40c60780c041150840d0042d40c4d460428502043d080407008040b0b5020101603d1140841750000d014942c0603004041040f5061 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 567095080 1250 567093830 567093833
    0x912030d0c090807211b0632130f0b03071d0904060b0307050301090c0810020a020d03090314070303140a1112041b0303020a110328060b0402270d 64
    0x1103644001d441442c28a1702003801003010381c061302001100000d01107020010f03040510104902c0c4401540c5141e40c801c441500c0102149040952504000d884504020341c1e803042519400020010403600940d108803042c0d580301551340856a0340e10188503d000001041003441d803100c90140c1e035070403d4003041c0d8003a0300711022903d99100148002c04103551282c800409a40800c2642c0c0200b4000700280060402031916041c80304462181d002d43e4451813415400000d01070017541c1020080b5402400c1c80408090101c0c0507080508060301400a070035000100c0c1882c88004000590007610040307800d0926003e031241046005010394034807403410100400c40c0340c05904031400f00c980303208651150b48640c14a131000c8044401e420b04d01800c003100000030943c0100300341c000701c1d0003542c0e000000c0344034a041c0350312200d080481c00000100d25403000342840240c6200031126000e031000080c4090000b003c24100e034003000010720040f000000805541924030102c621080f401d650030302c00384299 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 567096330 1250 567095080 567095083
    0x170c0f03010603020d0e070801060603050a020702090f1f06080411090c0a0c05031201090510081504030c080d05070203040807050a21170d0906060509071706060912030d0c0908 77
    0x40c000c00302019000a1a41c05e101995040600c8000011080d0b46880b0791360380c0741600070f180c188500b0300403034101000a44414158400d45801d41d4001e440d1210035500c003d500810000010724800f801c80511321a81003018061318400c01411554450200314101801c00440e4440c000c2039003440f48054108011400840c00142d4080150b9030800c150b60700c00d10b2401d14214055042d14035542c071141c1c0000911502c8a8002a001d01030b00c0c80041c260685070502c481e00e55868007031400a443d250310104000038410f25154080500506030700303003025a8904000181e0701d007540e2040041e40f000c601408450401d00161000341011100701040c14500082001000d510301c3c4a80d02c800c00f0403e800b4140400600040d6650072031240d8140d40b903501600b20f80041c034200d0310685c2e046107801c1c00403a140c101b4141e0f0a02031070146d1501181c0c405c06070004041100700078200e07a00240107202c0c0c3c0c15540c951180b02648501d280001d5519004401640c5e0b0440c4e1409400d18104a500681040790800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 567097580 1250 567096330 567096337
    0xf040308010b07031718010912030e15010501050a030605030a03090510020309090a0906090206030a050f010e0403020616020c031f050703060f17012901120209100e031c170c0f 77
    0x1c02e00d8480c60b45540300000d0203d07a40c4105d12054955090070220001c1200129110002111072b480070085128141c03407007a40c603016031401866207461000140f201c1e6004902601d2541e040d840d0108020b501c0e040402d00f80101810224045141d8070001e00203807a0240009032040141c1c0300450400c01d41341c00080b200b9101514160300a80d80b9000c0e4810b0049035000121180c0e00a4082c60366403e080ea004801810101c5a40c4081034030540082044400d0901c001c2c01141c1550041019844e08c14403805112180c0704003400b0340c46045840d44c0503440511200e504942540001886543c1105c00c80c010b0306c00003441802014500307a0306220406480421000f51030041841c0e806800c6c0d45c014642c01003030501030186828511030355140c00b00004101c0e0f140948020f9941800c281c442903003d1301070340511007000350b00c020304035041034140b4400d01585405d14002001ca50001c68070b1642d1960502c17203998000005403d0300c107044101314000301d406800040351031015142c461040c6c0360104070b00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 567098830 1250 567097580 567097607
    0x10c0e091b090d051509010c0f0507020f042a0908010e1507171312090302060d020d090611090a06081306050603031c050601020d030b0906270f040308010b0703 70
    0x89010031100143c0e140e4040081c5510b6000c400c4034aa0440000d221108030000c580c031000e25805c21295031002d52140c3c0b00040d05047c0c40d04d40505010309503082080318a000321480780c2103980c8016082c040500440103001e4141c8031010b40f6003c560480000304145919040606282e0404170242d14800002564652500d40b6001c0d03c155134554400440b60b10070900d190640990406082c010900b10050b07500703240380e208030420801550f540c0c00c150b500c82400d1001035800300060140d800d812802d60001e000c41d2000200010706041965504001c4070011701c0d801794034900100e8071441d503081c9448200054645420810207916194015044031080100d0080915480d00301140c100e4804209681d140d41d440e0500c1718a0451b1030407040d00500342116500c1c0144a819400703a88075001b403140b109101002b40c000d01407503451405100c042880040b4042c0210f45005040b107000c000034070744a0044601803074030350f464109804c0050030818180c00c00b08503007808000141c002500b00131810000d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 567100080 1250 567098830 567098881
    0xb031009080a2c0103180f03170a0b03121806070c031118220210082505070b04051501080a0c050108070813080c030c0304050a080307021018090608010c0e09 69
    0x40650006c0c1c054140d80403100100700381c40c1100c40008154201d08034504400c250300303d2205a41e10424003005a9071004102c1b505600451815200c440302a4002e00c06500d0000e11844d402c40f60324049942e95200c00801d0310f0203c04c400c0b0620800982d04000c21410300c085840f80416140f20b4000070884074090203000c02d4038100c4045580384924002e030b000d00150001c100c00d24418980b03a02a2404804a990380f20301e4034110340800d19101030383c1034150a54640c2e0340d041d013000040d954030024400d002d4401d036001d10801d40300c009013800b80013941e406410440040e19646401d40380030306e500d030182d41099060041e403908101d82160712015040d070002c03903d42455052401760814007024854407985d039035140000902e05203003d100000400851b103082e183e042000c1e0307544403499100d0080502c02940482c1485015080c00d01c40c0c00441c0403141c60300450220190303030f2005c1c04115605070780001c0ca280d4441c00048000c0da00081881c5400074180d850304014070b40303100d101c01c0f100b64040142244 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 567101330 1250 567100080 567100091
    0xf0902121f0905011401020c030f0705040203040c0b070c060201110304031704030c02041b080c0408120a050d36022d040617060106020106180b031009080a2c0103 71
    0xa600c9280c00307180c001d00040c0010012541c41c2c403142540001702020389409841010071808450500080454058a90102814026092004002c0a903001400a1f180b840c80c841020403981a02002840380c5842407542104091a0000c0a0b0a440d043d5030b80030300002c03041c410000131903000522401c09021481c18407215580703500c2c068030854a007080180d045840c11202e00c1100315119041382c1c00060603160b0380c06a41c1d4142c039445091003607001708403054004e82e89080c008400503000d0030390b000550402c14140420510030b207042395a0b02028502d961002c5000420803c94060548c2460322917042c421600101a000310b601d00100038480c9148240f042c246605080c070b40c00800200c440000e0042c03108aa40e10812482c800b03815060041d00d020300400018454014807c0b00100c860849842c02c0503010130881c000244000d611064140c042c00080d54041030aa1044010036442201c02585814000e0320080c0401100b5101d892910b051003c1070400620800d21500c24450920300441c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 567102580 1250 567101330 567101371
    0x140405061b0f01151d1504090c15030f0b0f01020a030503060a031a040201020705190311061c0518010c0909020307140f0403020f0414040f020303040b0a090f090212 72
    0x24141c01e85030b1540a6510300304682c200d4801084c0018112a0001510708031002158805005450142c4101200ca00301010b5403042c0c1c20f1581202c259180503508409542c0e660b50300e04e1030040460700c07071440040e07030361454188619070074171503c07030f5403402594900e036548038800002c0e40d0382007204400340c18050040002411740d43c4503d210006103500c00c07010440203846c1145400a0b010581e81280035024902006c10141040d020000c0c5aa076141c4104036600d103140c8030b41d880161040301042c1c0001d4100020481d00c044210f0003008605032100c0040c1c18941110704040103075500e40c0208499060002800030258013a0070b60702998000403005a581d1960b05040e101203507403c121107a200004113802551042d1b140190084074001e58407011454140c200f000110390484c410b1320700b1443c440e004035010a1a1700d10035158584094221380c43c1c9a196800c500307158110152140005036004c40900c0b0072a0060000c000030b0000320019400c0081000c07104140e100d000702501d140042142c031000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 567103830 1250 567102580 567102583
    0x7060905030922111201120c05120313060801050d0b0a180b09070b03100303050307031e0e0c03070303021c09092c0a0c0501030e1005090d140405061b 66
    0x441071400248004183c4110783c40e402c0500401d80e075150045464107045001c22000d04045404003564644c007503809038202040c01011003141102a034612000f0040458079072100c800c8041e003040404000c40d142c0304101e10f00085040f041d00403000308100000104250b480c0d20400c035905aa10028940056540c08426401800000c0c070711140e021038a600c0a0500002081041c016400e0705c00b9a000359445a1032401c80e84001c0d0380f48a400040c200040002c00e02c500040d5400203035a2901141880068810166005419000941c05075450024a002000821440c56410000d502500c695891910065207500c4a202c2d0100004141c01103503035542d20031000d1001a2014480070480700d00003500100f907403001c5845509040008048a0510b52000a240055198407000c0042d900303082000440103040c107403080040705e2280b600303110750244050042d03511802014004042c0800010ba00820444461015903101c100c01c00c010b0015403900001c860129070702e0013403030000780c00c0091244d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 567105080 1250 567103830 567103837
    0x309050606041823070609050d200d14010f09020a0905040f06050108100f020702091f0302030f0307051c140906070615050a14011b110604080604260706090503 70
    0x10106440200d40d003400041413440c079892038408900301c8460036284e25044c1c1c1e840340c040c0150f40c0d00190340c001d01400510b00c8140143e070b00c2d80d41503026400000c1000842c103100c1c0d41880c2142c840302c1803040c8603980c0c01d007481900300e016040601884400340c290003095850702103009040b49581c441c8001024040c0e0444004106580148200f15030b684d68440c19446400382146850fa0700d04008404001007031900990303500d60780090085803140c5418148205114410f404030714040701030000040903036420300045612080d2180a5940c81442d03241445c1031210903c3d05410303042c940118111101c0d070254a402c802c420b02148a5036480081c8006041809000d500a103c0c5051510070b02009a00c103100108440c4142e40e1400302c81e8680460021480071000e03c0e5001031031101d46642404681641048418060052031740001c16040100b10640d0140c0c00c140c0055000074148000c10290f03400388050001e040000000d55011007641e04002e02c51001c1c06000540c035485445d06000e014005c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 567106330 1250 567105080 567105083
    0x70e1512030c030903010b0a2711070302031903110f0a1b060b1305070f0e0a0e07051216050a112505010810050120010204080303070909050703090506060418 69
    0x21240c8500700b11060a41d2907010885881c001e508004c14215a4182998900c05940b074071411010241500b4001c0c4a00045594514441a8460881414480c220402865551b000e036025550300d0b07003407602440450b865540030000b09454030b03003c507401c5c40b41b120684561b20302c4142d803030b903440301804001c4429080c1000e410514807a4640c200f000c2215540c04418400340a03200c6030302c442c0004c040c034001c5800440d103400c041781c0d020f012606101d02c111300380030094100410858190340c42c2ca442c407180c00300450340c40d40883da0014401c02c102003542d029592050780b1901401711340c010000010a90f000d000800d806000c400e25000382c001c0300c00d10100000300c00c0d10110b40b480e45801c18085042010b00c0c8141800700e80c4e1440455468461011000107070f80c81a10f40620100342111180c019100c074120310059558240004150044188001c5000c0d00d10b40c1d0350b41c9891814842031500711030b0050013150038149000701000000d01c1c085407207540904211000a803070007903100c9582e91507803090790 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 567107580 1250 567106330 567106333
    0x1b01050c0304031a070f0305060105180102031207050307140f07020108070c060504080405120105061005030603160e040201110109020d060b0a03020301062303070f0b07030e03010216050c0102070e1512 88
    0x510740b009007030300707131107446903007980c5c0e80c42002101d001e810740171a01e00340c8101d400180700308015a200f03040305401d1034042c403040c0f046928190040c01016144242038411b040091400824400000c0d88489910500c1c4810700390146441011000ca0b030307aa20907510024184010440010103140c001c2690084280d00490f0906c00d0340b915203060103a0794414014144207071074200315500c01000500c50a0b10901010b80100b1900c0030480c000d54844d0001058640c1c11321130401d01c0c4000c0e40c0703e541c0000081c02801b003080502d0801e440050203181c201040041c0507898203c5007405a5213080340c0041c5940c00032000560004400301068a4220507000a900341d82401d800007924070f80103015149000311207000380d8140d0360900416889403018461090101a0554144100c1207035000a02c8024460304090040710700a0000c40d003a038000c07150341c242c0c020290715003d00340b110a010754010351009102030480d103401c051043e201c0400c064020b5202c800c46c030041c0e0713105489020319015808030400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 567108830 1250 567107580 567107603
    0x603050c040305160515070203031b16060f0f0f050a0804022b14070308070605060f100216090c050a03091a041b09091110020703021203040f081b01050c030403 70
    0x24045402841c1c0c1c1c1714040c003030b14105800c483e109035182c2c16542c0c0c542d40140a035181692460500451054403030f004405406110030350341143d40003d0040c0700400e0180c0703e502003040c1d8050050003200414003481c0070300409030440c0b40143c0e400b004681a506150500340c035681c0ba6800030481c4551403a04005400c22842030b80c1c40e11119030b03011035111a12648042c05880380001e8001c0d211401480018002c0c0e8085c4001e20020b0b109030040350b40b050018109002c0070000500091429000c0100040581c01c85154101ca81724540c54281c060215000180714004030502c0c014241e200d01c1030040101584c9100d002d0402c1103034440349002400e4070006240e28100f038206030748451515215048190030803480054140d416000744503400b904480400000c029007400c1c0708140390341c3c40020045020344800480107076103404205411642407002103032640d0411104d4a50042d07240c1103420740d40d00a07401050345071002254415145001e107042c1d51101800342d1042c0c914010b9400c01010002c580 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 567110080 1250 567108830 567108853
    0x409051008071d060f0a031203020d020403060606171b07051c09082401090203150a0e0703231810050106050d06140a05060913022107090f0603050c040305 68
    0x20000249880c00303600903d0168444904206131895850310050b000100208200045440c1c1c0d00d6030758905006040140c600710b094550241242d105800440300c540d5110424401d9652000f00503c000c0f20740c40000c1f2443c00d140801c442d850800c8038400c0c0012000041900400074144490b00780002554240701425400c4000900350814600820000748203a5006c81da80340100240903907041404803495401e0390070324590300b01039030000b40341d50750003014214040c9061f1105c0200300b0003051203c0d007810b224107107110001d003a06c8108844810b00f60745400b541442080d000700007604210090381d03421101c81c1d0002401c2c24945041d0211440902d883c000080e4a600503004002002c0b00000c200000c40d00d03801114001241041030581181c683d2005200500740364000b02400714004046000c04074110300c3c030000341d03480800548078004201025100c0101c3c1c40182c0c9070040018248180001e0403c003403144440d25521447d005c05071540003041d06d8810582c120b4001d10303080700a0341e81a0b040b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 567111330 1250 567110080 567110099
    0x60a050601050f190f0216050f01050c1f0e0f100507020c0d05150c160f02010302090607080d05010f0509040602090103090804030b0709050102060c0702010c0c091e0b15040905100807 80
    0x400820005c5507507000d407038541d5840412012000103c400b00380d0307800e50401e002d00418100d610346560500000300450800318a00300100c0900407008143c032400c00320706d0000807003510119141d00c24107910603105200919800303c3e4440b070f240e01d0940001915034070460104d00d4581d0302d006c1550001000b0b240700041c0304022a0030031409803100f42d000e03580d80391807607017121760b2003802c83c4200310240b110300f883e0002c0c1d0440840164540145409414403d10800003040740c0c1c048a1f00302e030070b4200000c0114644145010f45401001c4031178081705034030710f000b0200e5041c4034000c2000b4061680003642034450303806030f40303c00c07400d82c0c1056038151100c0d180c1c5031044280c0f8051780d08070301246001e0070003e51b80d81b0024140c4d01c0b80707240c55100d9081600e55230041d249100380e02000c4859616005011505039000d1049408804203400203c80e081c100745075980c01c03100401101d500941034031410b0f2501001d098120b50469060000c000f41682c1c07220048225028150441c5985000c1d00d01c00182c102c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 567112580 1250 567111330 567111367
    0x1c0903080403020c100e0607050a060612050c15030105090a06080102031602010f050603300c0309090121080f120709170304030210031e0c2f060a050601050f 69
    0x1080d000c1301c00c60925070701003141105050341c10200040c031010300c602d03080c1403410107810700c240b040040305c82c021150b54400c1d0603a0340c550040c5420340f0b42c012401040c40b100700500180780f541914695059000c0c090455a103220501405004070007100106a20b08000c3d80080010b00e03026008540300c0c1414072111038001226044500103608040d03a040c0600094401c41d030282100400030410951001c1c2c40405c4201c201b401c0a540c114901c1994400342e2203030004040c0e5151580c0515910019003080002205068010f034100c40440e076a01c04489000c2005a100f054201200c030303403101c45c0009519254801c81d2041d07501007180c48144a140ea800c00c400c801075074003011214100300c00800c0070035a030340100d10000e1341c81210f0060301c42a041c0658884101500e04400c1ca0f028007008480400030380d0461032901002950304451208541c08406806a040e030200d0011114a208240c02e00d503141d401a18683d40b043d0340b1000b0524987c012001c0301c4d801d65074039003c00d85032420122158003405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 567113830 1250 567112580 567112583
    0xc0607081e040b1c290103050a0e060f060315160e06090d0b090708011802040c030b030304030305041505070f110f04090b0603060c0c060711030405040e0f010f150b1c09030804 77
    0xa05002d05030304400e8280c1741180d42410441c130103c4d9004080350044000c0c0c00301400700e00750303ea681c1001aa84010a0244911a401c400d0144006060800902d498000c40610f5101c003c0e41ca00c00b4401e180b00b54034018040b841c0149044043c035030203a8001615031003074141440c2d0000001c1d01c004d04200310390030110b204a41c0756050703c414542e0f5a2005098035a4003100385080800e60050100624041c3d00c121403440c034a1800107128402080840e14540c840e4200740e01051020508004103481c604800481c00c00a1070072504003540d0750b44040c0d0320801b21070300902442c440c1c0c1c40946075407550007030a030120304024002e010880260038000d4100c00c051721104d0090082c000040c4184456400725000215000000c00035a624820121200c90030307540240c1c060b00040100280654482c01204c1080c1103c0c805018038402091034a800c50b072840c0c4242a2080c10201a40c08520700b00302003c0442e80408c1d03000396240c040007000007402101002125601d46003418030030a00d603000130141c0c401c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 567115080 1250 567113830 567113887
    0x1020d0e1e0105010617090c030f1513030c030c060f02041706060a03022803061b0201200334051c060b0d0c0507140f0c0607081e040b 59
    0x40100714080c600342e60f024001c80001c1400e05842c0d05a05003100115944140c125054400c1002c0318400a414550403012408141c1c0c400390501d0181112500001e800034020b1007040c43c9000d80313941c00b0302000c3c4103220240a1040b0503c4400a1000640001481030380d00c0100715520b549413140409007411518100d1740034410000091030b02d040000416054079001410007100d011010044041d8910105d5401c00000c01c3c454000000340035401040f48210307403030304619448c0524144c000d0845012038009540145104401c00402c1300003402c51750410025030849085e100d4800d07032816100550f048420040e2420110390401c181d012000d05204c01070107600421440018103000103461490280720350040007042681110031b100e0344104000c80301c034241282400c01946641c5041d800d5a9100c1d1400c1c0c0000b510000c2540040c0510001d01130200c2c0d4035400c4c44069210310001d806095000c1c4c45541035030044000c0320500c04142d400030820b0039066903a9107400c6100402c80c501e04807a201c103c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 567116330 1250 567115080 567115123
    0x3050d09080106051e030f06100302100e0d14120d0f06060f020c090403031e0c0f17150316060f08150f19050604030f12091d04030201020d0e 62
    0x1da14042c0180320494500401c41641c80c180703030812140100c010841aa41803154424400445009000345441019036002200e80c061960040c071090314000c1038244c5c1003101c0d951111060b81c1e03610030380099941d0410451081820011103051400c501c200500102c610041120031100075a6080b80c1480e81400006019890b0b60f8801a5002084000050050707000180282a24100054a10b91040c06403802152000d18000302900f1002d850395540c622584418008500342d4100a010402d00c0c507500d44007001200c10030b02050200c0c40900307101040c00c102c07259406250b07800c00c410360044142c00c4200c400b25030754040c05804101c44030040401305504500085100401500c40d030122800a0300d41c05215020904001d58004002415010028002c1000c81e540d12903102410182d48580d5072010a040c0030308101c50130001c0c50012008001d10008148500030550302100d0030040742d0120044103031120f00e0182d000e802508007039101030b407a211000301c0e0000002104e24801001c0c51141c4003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 567117580 1250 567116330 567116339
    0x90303040e060a1e06080c040e0103140f0d14070c0801020c0a03110604020d06020a0c06230a0504080708032e060806040e0601060f110f01021e0405090606071b03050d09 74
    0x20740070ba200d010040f1081300010414107000e1b085880d4401c8401c5101d51816466012100b40c1c2e035000e82042d80d140c8117000c502001700e041003069000380300c540d0006010740680e80b1401008158141c280580117000407403200c0410000c0c41482002e00034500081d52520003441d01c00341c0d1600034071002d07000103000051a014914000c02c80500440e00902000c2458000c4d0f00c601021750f2044004500300045140b000001c510148940303810b1040c000a4100c000000d4807032203003209070103030440c0302242c505410b010000f01c0f01011140002d5110b103331651655164804e541030201c40c60301d1240c8d040414103111102d0203401412405650312030300e440c400358440205000072200c07000403c4420b0352150300180400e600551241c0c0c03642c10640f401c1401200ca01c140f480c01c05903240410200c5079000300b00114070200c40d822200100c52003005003030070b05180000140f480c0401402403402480c000800724244840315000540d005081503041120f00c0d82c80c64040e40c0e0304001d281500005402640108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 567118830 1250 567117580 567117599
    0x1005151c0c031e0c17450c0607061814010603060e0313141201110409050612210f0c1005060f031b010c05100b01030b040b030d1103090303040e060a 65
    0x4041e03010070781e03c82110021400c0600700000b0060180001c50b1140201b124010070580150612005040d00214051080c076001290703040c000000c551030340d08101e10280181d10b80e202a80c84458020b400881d031104043d020f01d4503903520301009880b001141900d5041880150000411039200765810031036500405102c3e6207034021001c84000ca0454941e00f08018018980600740f8003034002c005a401c140b444140a0851340c0344d82c40c0302d014400224041041d4461071180a611002c251108103120903c091503070f07118550702d0303020110021142541d070388100307010055860042600028a65482d4008101a5285c130184400440d05040600264090500c44020501d17a0000b60003000b01a80d101000031040c4440c001481c100800c030a40000461800c214a404814a1783d00004064010350001010350b80c10744407a90045003040071021040d1070000c0c20140d43c0289240000382100c922003074078110321808900340d0745407201003400700ea00000c3e901014051074044a6968100e5540c0c21840d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 567120080 1250 567118830 567118841
    0xe0406060e060a140d02030123060f03030705061906030c0e041b080a0f0f1217010f180509070504050c09041d0303060d060b03070315051005151c0c031e 67
    0x2c0035410b04c9007855030070f0406810070800c441c401400403231a5101070315200d14145c2242c1c0b01c12080c0810300203200715800c0901c4418070180040c0c000c2c500c0cac81c819032039046e902c040283c8920769a4100400407420200c90740e20407006960f10103058102c003a92203e18003140c0700103690945452515803c8180d0301d1612a80f00c408460100c0054032450b03080e6190040c9248408030283c0e5a45203104611002035401c8980c400640000d48440c0408000140711041a0205030001030780e0b105864014000103403030f0565400c0a913080c00740070699503500c0756445d061846075442941c002e410002840b06030140d820103030009400a49041007002c0010040584490300e185010200c1d400030000f00d001401d01c2070a815105014442c0424105451404285000590760094400903100c80203454945c1e02801441c0c0c000d41f0360035890300054141030004413a0b5040100e031041e4484006000f00445601c0900740000c2c05041c40d003000300c140c080c01c018010748812044964500032a039045507005c001403198 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 567121330 1250 567120080 567120089
    0xa0305150109140102151f0e0705030f0c1207030f1503150b190f030204051302030601150c0506090a020411070f03030b04020705011d10111e040e0406060e060a 70
    0x141c0080d9440c01e0280c1040d0f941d51a01c140c110700402d10044811224216800c1c0250010004000a0550300100b0801083c554000e500c50150140c00d00030325a60200c152600041610303d035214503147d0702d0204200e407154454004a0011260130014016015801042c010b11000001d002601150604070391100190200034540324224000c00301d104c14036404030480d02c10241c045070500542c1c0c0800012010140d000d0004820420340500441c00c190041c00c0d0411040a8940141a8658006034840c0414000e0950b6001c001d02c0c8541024403480003800020382040c00c0c0c03101c505100b24026210350560341d0681c001d90408003100044030a982c11500d40ca504451010503908481d80d0440149c0010702e260383d4016005c0c0b11103408280d0a00c00c40002c1400c1028014503441d00140d501c0c00d040c1c4070050480d04074500300c0300f10712100909046030340b02d120b84c0d00842da07055207110300c03044240103541196000d442500c080008003d95035200005072200c0c1c00c2044803d5603000308002400400e03001d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 567122580 1250 567121330 567121337
    0x62114030702131d0316061118240a0801051f140309010f05090303040c1a040504020702040252021c02040c05040302040b2b260a03051501 61
    0x414041d80346134400e498041d080c8905290b4407450040e03607455504221400c0d100c041280c8581420090785124010b41101070428030760601445000c0d100c03040e9024605140140442e48120205c200810240f4840c000b0141403240c980c121040010705602c4240901400740300d1002110b007803002c105000c02c001207e15541c00d20603020034041f503015a040900440c68940d2944a10b49401c4480e00031540f00b41d8507c40115141d141c00e0503c02c00d14240d90b0702034504032403000c000912264a4000b10f4040c1d07541542c0140c1c1d2025a807010500030310948800320110801d01e0044888640380a0b0700d020700001101c01d1080300d94101c461088400c040c00c100061081074000d800c1d006040c0b940c240c041c4a40c031088084500c1c03503250007003000c0c0c50301d2400300c1000400004e0207104615140c41030034050700d401e031007660035564941d0b22144203642d07c601110403007000c0a11501001f01c20003000718040f41d09071490100c1d45950184400b00c0d0824003c800c0424200f20015400c00309440d002e80120780c0507034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 567123830 1250 567122580 567122599
    0x11508030715020f0304230601031110090305100b0d0204020c060108240412050d060f05010f080f010b160602070305120f040c0302060307030b030f0d270b030a062114030702 76
    0xb911b01c0150308000107c0e030000d103411600344002c05000d200d40341c021070240b240803c680d1a21400c226800c110100c40c4004c0c40000d18090010410000302402d41c02c4060000150040c8080c001840c18a103944000707512500019841010340743c080f0b02c84d03040b6100c139411160707244078203c11302c81e503401b4400d040a9122003950001f8046465080301c074503141e089043c041c1c03500310b5060040c0140d81c6140c0024203c3e140c20901003245507800009554610103c0c40d08960508040f82c420901031018440e21681c10408500801410034809914a00907880700007155a5041494050100c0c3c01002c2250072810107480010800303004000301c0da01c200c0c0d0100c14902210308641c01c01403281c102800c0d10003010781d50312a0071901d49042040c0f140740d91b941030043c030120702190001070000d405420900c03507004681c9140003031020481c604601360346c0604d01841e11b03035660386110001040158007002d0a284581141180c0480030410070034454003c9078120000310084001696030301c6803e100941160004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 567125080 1250 567123830 567123833
    0x61b0c15190318140c0a1a0d110c07030b0f370e01090308090106090c210213030b06090c09010c1e050601080d0806040506010e0111011508030715020f0304 68
    0x294000c030400110b820342d81c10f0315039003a1111a01d043c006680c2448a500c852000b9400e454202c0f0b0034402011076181d03e0140c3c91540c0c0e5101d040e40616910900465103420b12908488005826a0f0300b001c1d040c411034a80660b0307428501e150303407001e950b00030903400c0ac8000b1950710f01d1031221511604031040084965a00c0300f1030306907041031801c515070b40069695a4034a0681e4800c6c002c411100c0d001e503903a4806030400c0c0010a007112601c1e030211100500d80103c0003001d5801c04c02980b06600c8100c40c00421001c002c507180e001e442002c425030300a124080002c02000240100c40340640c0050311040302a544412142c034441c03040910349804600f40c90030b8900011400f42014003000d0028400802d89c41d203d41e11146044001e03045101d150b081020b1002085900504d602c0d8407050465080c040d60400100280980c03040140c158100b251070410b41d80031480075006080881800340000340c41d10382e260003042d200e03002010100c2d40069620505609400b03140250b410040680000d2403035078403603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 567126330 1250 567125080 567125087
    0x5040b03041106030a0b03010f050403090302100c05151e0603030412080c030705150f0f06060c1f0f0b0402030103170705330112030c11061b0c1519 65
    0x103104440c4002d020040703140c180c4543c806540a407107a80c1c2c01140d6440c000c000c041c2510001140c1e80e450238501010000400d90146070300301200e80541d84110b08525802c0f04480500d2000400707813a84c400c0c2c120503942007080c7e01c1c03000e10900541d03240300811034010007006c104810a5440d154940d00512040c00045100055070031064440c0c4201440c4c004a880d0403030840d000440c003034800ba0010314052543c64040480e003948000081d0140307038145000c500401c2003250181c4402d0190201040d004030ba60001c000207020b03103161204d0b8580c180807203640300b0040c00100c00c0c0204120b06005210445080500a4038140ca03030014052040e14002e43d088840c07500030b2801a1039a10850980c0500c0b100c40d0502c900010810403150f030500704640008001d0128107078084840149075249000100740d1103686040483e0f8820f9844801840200004809000e05140000036150309150004900d0000030b004e41e5140c1c0980c0c1074500b0f0740036512080e2060042040c16a0b501900d203d516420610 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 567127580 1250 567126330 567126337
    0x203041a2805150d20060d05090a0210030606081f0b030a050603120a05074e0f0f03051e0406020304110609010207030308060f090c040f09020a05040b 66
    0x2084801d50001c1c41541c08640d0400c82581c0103148030a6031902032022a0f4521166007540700401d8510116040b003da41e5030a00c0c0b50303040c8131800c800780c54541c12003096450f081210a5000f00540c140014241041100d807244903140c13080b4812030350800c15619407030090040d80101c03009074445103650307a1641070075109a80c421002040c640c003900004074a40d010000510301a407251100099035142c0081450724100414151500d90501446440078182d0700800f201c4905900c0854191150610000c3c01145584034100760007a020000780d5101070150f1b018203d80c0c4498101112003c00321403c3c09446042e042000b2200050f1071142000304103010380c100d160030180c8000200341051040d918080c48000aa40890340d1680000921003848001c521120005400322120b030b1412200d2000070b540d50500d0300c002414000e0640001e01c090b40e0300e01082e6000140a0804907840c60194100382056009002c3c000c0300b1303c150007000c1034034581031094554031010741e00c401e07103401e0421458000030f42 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 567128830 1250 567127580 567127591
    0x507030608070522020f0304110a21050109020a09020a120513141501061706010e0618120a0813080c06040e091c0e100c020a12050f070e070908010203041a 68
    0x9410343c1d010004c4010b1403005000340394a10340445c1d2a401c0074035113203d400700b981e00518071842d031a4038284008840c0b40a40c80803291207400c05041a0160b140c0306000d000340901c040d5001040d0880040c00c0415500107001150342592a040410310301d02d070f4003044031b406690001d055000644003000044450a244440c44240021550b03011030380000c942d01d90100342c00200002d80c0821003110388040074110303542c124009003441300d4035055040114669024203008100e511000740e4403400661034417007611101c3c0e0f0f55802564540159400c00324050380c00284240040b407100c000c001541000450b48403a4198018003551500f0f2030140c0b40303d25041d002d0855801e500550b42810781060706180880c00003030068031001603a03400320742041240d60109200905003c1112491801aa41c4403209411356011200a02d8003d50504040d413800c01081aa0015031049403400714211600c3c011981c4100c00b103954a07078100342ca843c111803d07404261002002e0b94900145c001d10b41905100072548030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 567130080 1250 567128830 567128869
    0x2010504080f1509061b16020409140d05030712051806181002090604150e0607050303190b010c031103132702070209010308090105040504050c0c0105070306080705 72
    0xd912041040d003080030103503108026922084003102c07900c1060015980c4180e01402404140c03030240983e011001e80c6590f6881102c0f400103150407035001d20385005450301d4028008104d1403103c2c0c64483c0c85e0342c0d0b00301804000f5125034030902404610070400c03a4400e074020b41e2140c1e036155600940401800d0050306222040b4060b5503a01c0b04d41c030041012500c06c8001042214801c924900c003103003084200424251120300400141030700341c4851013141c4c11101d24403891341c841c000303e8030202c0d42c0340c032001000c680c00500000c1c0701c3d09100c0000040c0d40250003030f0901d0145002c10203000400c5410100c003090210f0341e00c1d2040004079020340030810050300caa6003900d00c0c000c1040f00703422240781d240c2c0190195001103002d5003803800040318100141d0b032020404500d002c0503074000900906c1c05110003405030302e0020b40049164840c000751070081001910900c22404c05070070b03201c4580c01c2100e901e0581d41c603010029001c640300340560347c215500300000d403514504103c14844401c00641510065 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 567131330 1250 567130080 567130087
    0x1502100203090a0642061d03030f0705060105040203040c03060b2b1a1003331b090f06030e011104060c050f010c120e0a05010f1a18070c020105 63
    0x125000e8002c0301108190260700b10b01040b07a90b41c0e031141d65080440102d00340d044503112941c00940108180056031ba05080138508101c0d118034a420002508958035017500000c503501000440540183c0004c612030b03000c0e01d40513a20743c0d0505c000c9000403140a02001400d00003080810003691151460042c05070800030b10104040c0d0b9440c01e050b0700f00c100c3d807113500412914014800316120301c42d1584014140340c0301c641021070324084200b19500000c0c1c0302061159052103104400f95602440c115081d54202001c2c0700d01523810001c0100c41e1f04c0000412444100070f01051080c50108261115001d0034100c045c145407048008040004101c105c0390368503140390300394104c0800940024196540c0d0902d43d02d800349001801c00a245201d41010b0381052420803100b034000e14490840f405041d00056102c44c001000d501c0c16a200002600a520303042c800340203d49690005c990000300c80721956414451a003d01c0300c2c400701d0500c0c40032103541c440c001c1004070b803249404181050051500c40d08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 567132580 1250 567131330 567131333
    0x1170f10020d0219120b09010b190219030810090e0d110109020913030215090a030806061908010f080a0305030408030a02120109020705120c1903111005060301061502100203090a 78
    0xd4203285104e989011800180c00f07415240510301480f101c01d8401d03582e20768594500030504459001d2a00c24240400c20140703144c40d0305208102d5204202001c9100e02a00c6d40b2134100030301414010341d00c00314140640b09000c50140d582c0d0150451400d4040000d09100c54609030456004503030301d0645945548444004002d41d0301d40c5807003030042c105141c480000c40014a0068548500c00c01104406110142000903091002c144441c030250141490481a5101000120b00d44a103100c116040715020300800c000e10382c000580b60503112030740c2c0d08801491316009600e558031143e080090004004000080000c0c4201c0d000e180c102500034405420100b10f007001c83c1440300240c000b04d01466001c9181c0b41400740c100003448101c00e0240846140008c00c4111f06d480d40301070b95610702001643c40040d020144942000741c05042c044081e1a9240c03542c4002d174001c0c05040c1d484612a47c02c1c1140490801810011107580159580081142d0494a00a2806500b00401d0741c1c450340607180344c050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 567133830 1250 567132580 567132607
    0x5010509061207090e0c1008040309030b07030915020309011d1b0d0f0503120604140c090f0405090a0309090e06160c08181c0506070c0204060801110301170f10020d02 73
    0x1010624006e00301c00c5c010102031000d200c548240715010030058809000c04603400011800580b0b0b004014109141c0c0c0b446010390150030135210051608a400c0c4a211008882d0742c0914025248200207020600b596094007004031403441604107950491030a0b031074443c9c11692000ba0007000130b480b5848003d555211f605841c4807041c0b040d6201c3d00006405440004403680803513000c81c2c2240d082040008900811003944001032102e40b900d4030019110410790f440440d058030030500148140402c1c1342203c58103454000100007107012030196000441d10510b2402980840c0015200800da6940d80c0403600008908000003403007400180e84007100460304180042030303113846c03080700f10b85103c012038180151042c0743c001c04102a20907006007030002d000894029044042d518145200340b0050002600610b102d0380b0420071036290150010003410064090760403591040007450110008a1029480744003603600b0040d560030954081156032160741c003078050791455440041c00e0589460240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 567135080 1250 567133830 567133841
    0xc010b03030408030403120207141309020a0906090b03060f16050d06030c14030d090303031109030615031c0801060813080c07080106060e01082703070b0610030501050906120709 78
    0x3c1c8076000082d0610a200b00024190500c06042c0f00421440e458489440101d1021401943c4910b0038054a4007a501c0e40350049000c0a400074003054100755034000d900020421032044105850406128180a240100790356100c1c4060303008004807640c80d4503100180450105010b070500c44140081688814244291400b43d4440d5a0029409080c0340501100c45188503402e84690707c455500d1080e07591282894017101c0d41403c005c207030f042c00201709000f42d018002441d509449041d00304808552280d03662000e0910071380c10f4465841220423903007406508190b0403808950a140100607151090030856417012140355442e098541a68074103545078070081e00810907900c488000e204015086c0b2543c4003d01050030b00c004010030000000e008500d004000d10030340c003040004000c00c1e00400c030503452010320000c142c940d111030510344010380709001c4d25680c3c0904114040314500038040d00c070b15416140e000b00f0942c01d5036030f00d00420103618003620908095008372080018208003a010b80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 567136330 1250 567135080 567135089
    0x3031211071a010e060d0302031803122106040213030b044116120602130f06080a1401140409050d0905030127021e060f030430050c010b030304 63
    0x2100e50303552501d909020302d11805030069104406d208617407000a0307000411215840c0e03040035500c541c07a100c0b0300000d0805100e101505d06162002941c4181201001e903114090387c5014001d50306a1156000c4c4401c034000c1c202040c10030700e0b0041081c0003094101480300d900034428140a560080c0a9118264002d0403106030002503650000780c0110b0001480c0c5a5a0400000000d20180d40288251014088284039469158644034031640034070489070112502004e03074410100380c080e603900020f803a00401d442000b000030340c5031001c2111410300340a01d44030011102c840e44426400c089001c04405200c8501c150701c507640d04400e10003e0001e20503001e038070f07240c0d071281c51000340380c441410700b9900c095044440c001c0360510700da03801810781c19005000c56010707550616800b451600d840070000311204580c1d840207020804055a078840001140b04910489142c0c50b6034000310350b58440114040540f00d4444028044400031910420181112044403000480c80c6803802010905540c000d070803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 567137580 1250 567136330 567136373
    0x13121212090c0e0f0a05061c03090e180615030c100513080106080f0f0d08100305070e061203070b0c0f070b0a0507030b01020f03120411100c0605100303121107 70
    0x20440000125400c482d07202034444418011403802000123800d134900203800d41c0701120a019140107251080f04c281d03000d0301680c09020021300708042e80c045100450b1072042c00368496040010b400c210508107200360b042d0041c1c0280803101c202400c01c510510356020180c01c0040505c03800c02401c0d0b05141c0d84004141e41000000c40c582082ca405082c5420745100c2e0040d54802c1d2403642d0030343c2001170240c88500d03861170003900c5511581051510030181b40e0001e480b600c02c1d40c1c00450070301021142640501c0049910003485036501c0021920f074012040701500c40d003044400140300700c003508000c0450301c1c6c60450003854000d25948100d0641c0c0c0c00e0355044801d50f0344008210a803034252040400344842400180500140008029603910840d81200c0705c0c41c000c02e0216041101d00e0007911051207000340b603045c0c0b060301050002c00c51800c101055035803a0400d03001c20107580c1c8049520701580c0d059911056150b02c4031542c60003a00c0001d0003010310701010011200450040280050100100107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 567138830 1250 567137580 567137609
    0x90302010c0302040f12140f0105010608060901030b0f060f03030406020618060c040b070f0f0f06140903040b07020604030606031a240910031713121212090c 69
    0x4009003150100d40905081c10710402051050810111504041754250a54842c2c0c048041ca868511800c64848040c61b912445588007080c0c9010740000d4141c407090343d240e60382541e0f00d4003001101d48080c1300140ae003181c0380e000705242820196400303520400141036916030a2004010a25640c01940702e50300603000a01030114400f43c01c0d5228407114804e80c010202820102c003610050b204a20031050110f0001803c5020481c00c15240e80320280c001030000052900c50908400603668420200d400e02d141880022021100c1e402031801460744000843c1814107061031101c069011210a036404201440000002542c42c0191406123109850b00343e8000b0701d0790036008401030060240314544001414240d40b081c902201c0d10000300b0700726510100c54a803540c14100c1c3e65041d1300003400c220400c2036046030600c480030062400b03406001ca02c000761551441304410340454014000c0005546040308200c0c60f00c14410655100c80e003200009084c021135481601c0a04c45070b0044640302d0310b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 567140080 1250 567138830 567138833
    0x13c0501020f03210a0e010f230108070623030c0703090b04080309010e0609090705031012050a0204020304030210180b0c0a082a0c0f010c021212061c0609 68
    0x60029040348a000001581400000140b91074134100e0030421200c00c1c0310200008054244507001080540034660080201c5501e81003c0300191151414440e0002903084a1a007503500c2020880d04031207800300034060070707428000125070f200e024818031401395102071045a10304100100641c02401e205400ca9901d80da14900a020101d499000c444811400d1004110a400c0031080b514011024640400081c900100050710b9002d0072101e241c01c842040b081202031600721008600a401d00415101d1081ea146214031409144035002030658110b21040d00041c18660041d54010303202c0c0c0162a14000c01c21350b40c00844c1d280e60329a40020500c2040c030400d0103030030000b0701c1e0070108000000c1d00d0080700b80c030041c184d4440175080303e1000b0711807058600203070340c040080700c1c61010702c070440c0c0d0f564142914070541e96400303c2c040c82d040d03510f4224580501400020b91010b41e10341c46942a04040810000f40d4083c0001071115030031540c8580319030091080408401c038840d1040000041c170340c555 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 567141330 1250 567140080 567140083
    0x3080c07060617190b0c13080d0906081305030d05070c1403070209071e0c020f041a090907240309020a03060c0206011e0302271006110d08013c050102 66
    0x5100c640c04c0400c2421100e1000c5000003240c01c0d8441017500010355604407503402a0b95001a5a10120140c021910b55406d140e5003c046103089904550f0f6510f1203440e502405983d2141d99540141242e1042000612050060b04032030360100550800540d022000d0b150540c40c0b00400341b04124507000001c000b42180350501c200c0c1d8001d126803400341e40c040e04150b00302a070308114a202c001400543e400e440215035440000703504c8400060800e020958070403522030030290881808600c60480301d000148850000940002120403003516031004c102420b514501c1b074086d40141c0d00c20140c071000b40234050303100c1d0701001008510840300000d6003808800001d04102d4180c000c018041c15074444500110650314800c81900e404a0300307880e074201c0d0010b00c496803140d0750b8a02c0307541d8182c0c1d00800c10554502d805034030486050b5103035501c0c03101a90040da0b8a070303143e0710202c0020800c080c0060013200100c2d9031900b1441c0c0002d40500b072200e0241c4210150440d500d0321715004500b00340c01071105590 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 567142580 1250 567141330 567141343
    0xc0905130c0506070510020d0204081b0a030227041109061206180f0a050f070b0a120b01120f050702010c050304050d0e012106060e12060403080c07060617 68
    0x20445099030303114400d599030303503290082486801d11611010400c103040c06018042141c03030890492046560302c0204040c003000e500103100e10f4080e8010000e0074191180c041c1c0640c0c910303440c0140400c8115048d034ac00c01020305008854408900800c0c001c0640050003041761070300940c082c44882d5010000340c002c024400740020400780c050148165000c40c40440013401c0340c2c124a1901c078170090f02ca42101603030720b041804905c202680c402c085825042c001d0205e40315140812a209480b070291b290078440750ac3e07106803405240061310601d0407090b08045948400051001454441ca0000e0f00c200044266400d5255251100b56254240f20842ea02417092070b100c0c12450800c1c03415840d06890380e50f1103211a2204c0c00c2445040510245968401c030071086c03461031007140819010f611114001c00400460141c000882e40f4003404890900d130034581c03d50755002030401001c0035502d07030750102c618500203050220a99414004000050305c0340c0a0309028082c5a5001c41c07048518608032450080c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 567143830 1250 567142580 567142591
    0x30c050f0609100f020f06130c080f03030c0937060f05091002010b0a06030203070807050705190c0b12040c050405090312091009060f0b010e0303070b04060603020d0c0905 75
    0x10410034840c10b0340300d0700d43c11000054a0b00b490701c1440d100b80400e07410142d110007102240e0040f0001c00c0041c1e402c10325020252030150490a0000c0e440e1040c069070b4080c1010250b170558818000181c808802c000140303020b0901801103c40c140c0001a034668140040c81c22101083e415440721014810100818006000f2403130140b0355500d41d81c40181c41032080c084214001d01043e8000e03800389000f504403049100380078044445480da5000007c0085d0410340d0144001003e020206100504c5441910384854011001e03082d10000c1c18540749040d40d4410040710a0038040200281c4416040e0140040c01c06c449100300c010302c1d040c90550140102c0da00818030503441c100900806500c0002542c0880021060000513600e540034002d141441007590f0b02c482c1403d0a1960707080000390340100000421428046c44120750060043d42c3c0301036902d04481d0154001e201800104840300c41064100d030003010f0010f002c2d6101d801052200b00d100c101138a819024200c10046140188074003a03201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 567145080 1250 567143830 567143839
    0x80f2512081605070f0b01031406010f03120f0908010e15130822083306061e04120507080712110904060b0a060f02100e03031303120204030c050f 64
    0x10314250119402c004080b40c1c94004210010802c02c0c100328030294107402081c0c00100a042640c0c4d030f4584074000184e00900080c0c41d000e0319000203103804143c010324041d20b902a420340d804001d0040100c80762644d042d03e0800300090142d0004a2400a1260b083d00200364030103404821080000600020005041c40c061020003848100101d60780009540c032a908907060480e00e5801d44e4141049003400b601320040c54058a0300985540d402c003450000c07280d00918805172010040341d0710a960440480d0603a421080800c03418103800392022030704d2007526295451300e080540301c03590a0451481d444040b1010b034040001403105e0042041640d009000000b43c007071601d00d280c0e42d071138040700120001a029040000c00719007082030300c0e0014814418080d00c40d00c1d040359103550003048a4211001e16015000340b01640710a171117a801001c0e00d0740d204200652441d1201900d00c4041c0a04080980800c095480c180c11a110170f40020002140942a03080400b800c0070304021040844a8100340306 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 567146330 1250 567145080 567145097
    0x180a0803131e03080c0f0d09031104020705280c0e1e010b0d0c2601050906060901020a17190e0a0f030b0a0504020a05030d080114030a0c03080f2512 65
    0x46094030404100307503030388182c1c0d064a07562491030b017034075040d18911100c20b540507071141004000d6006103400100c2e4015684001c6880c030301802e00080f881400b60203030403230300210200010b001c031310300044402c56102d00046540e650191a801d82c551890780099512a5495040c060760820540c1c45000020103031020b020f00f0b515014000d5007610441202c01d03111030700d0340c03440c10100b8018450501c3c806100b600003501451000c03240c100d0000300740551481340070050302040c628140711003564449901038008245030742464441d00011064040c207240d041c0b40402604400320540c004580040f8610303261802190340f524100f021407041c0340c208100380000990204041100c861080350044180c030700000e040e440b030b030001c00c603a5456a040142c1510450200407c116840420607040b114000c14001c4040b005408042e2990b0318010061f00c0400c1c4507100f4004159440c0c0140701c0f4000c800062490811028260001a440c04418444454140d4414002e010f8450680c02c205101071816184 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 567147580 1250 567146330 567146369
    0xf0a05060702011416090509070c060c0e1305040501060504020f210c030408090102010b06040b1c050402310c030603030f030c02100c0203040305030d23061005180a080313 75
    0x307130840240000c0d281040682c101440e00d00801c0798201905003d1702941052901e104c0c00f4004ca002000110b80641c03a01c038905420b14400c000b03a9170080c0c030061125020034028031444002d000068010b8500d55610f0f00d00203000c2c0c2d07c80c801401012400d1034a140c48855481c00c10b07040d0703100c482d00465001004030070450352240480c00c40703a01c01c0d4402c40b241d4942c4003000c0103d0050056102c41d60304030700d001402060032080c4030068480b04d94a05100000454404040003d80e001900c000707400c4010801452509041c442403600440c440d100172101030049290f44800b03440c400d82c030520110303640724428010f05911241c0712154500d581003d001100283d4002562400d001c82080078a565030707a0307240d582c1c40c42401202d00850b0408205da846c1e4000c10004001801d28003e00d03080c241030224110326408080111078411440101501c050310981481503880364040011000078604080103540140d440f0b0400e10042c0074088003c64440c203510580380c1945505030015960446050381054 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 567148830 1250 567147580 567147611
    0x9010e030901030c02190507080d03020717090303070f1101030b03010b0a0603050903070c090605010912080d0f020705033907050d03050c150a1a010c0f0507080f0a0506070201 77
    0x71490360080c42d0016151130001422820302e01c61115010000c03164074801021304c80c000034003000303841e001c2003a030b01e0380b084d0880c09500301d12800400a200c00e42600c2c4003017003601a03002804992078040d095a2905d920b5940710f540740c071409842154048120f0340a12820359040c8503481daa410180c008201d0320345e000c0001464520140302e04010503444030002480f61500780700750b4070041d9012600104c11600c51a541000e0f01c018064030340040d003844030002e201600c00032030920144c0c0002c80c00307103030031040c02e9101c01822803102100401c81e000c00050700004c104000030701c0f1700c0050101444900500700710301c3e00e00886043d88012014a0a03401502400700440c0042c110f9808880b02d0903841400e16069409004209200070746000e030f05602000b82c0050612217214054a4004000d84d10340d60320501203e44010004a00244810480400064007071200060043c00369085a80c100d5a4140c211303d01813a241a0110b16002524003904000c002c20400341c101451740002d02000701c9050488 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 567150080 1250 567148830 567148837
    0xe101707030204120b0c04090e0f150105090f0714041d0708090d0818030a17013201020f030408100e030703081308090a030c0608090d140d0e01091a09010e03 69
    0x9441380c0c05d04004250310b025041d00715402442480001d00c175a11090ba4540c0c2c0301d0309000068003841c01409401c08500d001d104000f0b05841006126031000c0d06c4017507400700b444800a000c00240504040300c0e036105500400544014001000000a850098100b9014160002e0220414000c5402c10b0001c003c4000c541070040d0342032450020556500e208903028aa082c1451002c10307400002a000d100719488012030991361030126207414685d0b42c502503803a42c90641c10301c6000b80d0003802095985440c640010414102051044405a4040b5600c850555001c0e52003044036601c134250113031121a09006a0b400e0742c0380c40c0040d5081a0581c0c5003e007c1c00b6000b08061074001c01d44081c10100f0011200380c0d900c50303002800c000c1c5419100d01e003110001070b05000c0c080114481400045c4101000101405450001d6650411426a5450b1200c0c582c018034241c1003441c0c1c070b403c201b001c1090248030b2046c00034082c401e00d50b494450307880c1c080e401d041d0280868401e641803545090708003500000710f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 567151330 1250 567150080 567150083
    0x1a36130c121a1311220b070b16052205040b0303040b0f0307050c01020c0a021519080703020c011407110a0302030a0c140d08090d03060f0302040c0e10170703020412 72
    0x42d40c0d041c42c144035010f0007825030400403480b14002194a84891901c03901204001c004804880c2c4581c1d01d41c1100c2d011401070301401010303803030244001600008100c031444032035172090402500300b14070223020a034075142c40007800c0c0940c0c910880c100521f140c1030140c50340340141a405540b8007802e00b51942d07402d01c600515540f6068001000c103130f0f840e10613801c648100c01c502d030007151a10a0083d10640342c5420000c2684106004000010b98011a90840b1401840300d088101c440c50643c0b000d6034001c10050214062588c00d008c0656851000e000e000a994880c64099181c0d191120010300300341e0500e0f0108915900c8040b00c000001e400104440c1c26224078103068001201034a003004005440d003207180c090b0301400100d80702054102d84624014801e031000e230340ba45141d80c0e500700c0031190319110320810070311508410800b5080580c00340082c0165842c0840441080001042d50302c40c074154420b00080002101000000042008c1078000c04a4501076107007500d0f03c000280f02c1c00030f5a50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 567152580 1250 567151330 567151339
    0x3070f0308180d0c03050c0114040e0439081009050d0318120c060b0609010903030809160e0403090e07050901051b161a36130c121a 58
    0x849a640e603a0107030f0f9081e20360310040080105881c0c0c50441d859041040000b400300b01e0f110920706904500805a50554101d4000e950701503545480742c20401a07003400d04a40ca05a0454800921201ca201c28004086480089515516150200d0b00d408210b2070040c50861034294000005940401c400155050602e03011440e800800d0401e01c94400801c0002c1c0590b1681e880040358607045074005210b0741c0502c40820900e60500f0601c07004e44034908803240003646000f02800040d0290a105401003c0c4100301d6400e100d02051a0071342c03c0860700314075804014a0100020158848140e00140c044504540b1180c00c0082c0040c0c0240103240c4928140034001c103025150202d8070242440d1080744c60115407500134020300b02036488540e40652202d01c00014007660a800300d48003211080c0e2207140460080b00040c00c1c4c0b0294503000c00c3c440f009501400502c8000075525801c14410000c00100c1c0060705203410304000d0007410b590110341d941541002c0319207101d03440c0344101d03108207002940c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 567153830 1250 567152580 567152617
    0x103200c0a0c080d20030c0d0f0201050601110d030f0609060b09031b0d0b06220c0e03060c070305091302040303052701020a080d0609051303020106081603020409022d03070f0308 78
    0x31709801c6000d582c442240b54801c00e4000d01803035620403807400e500400c1e500200880d40340e40b0011034402c5404100c07164558006196050514400c0e03000d0100540d05880c0040d40e5900e505070361090321425031000b10690300104040d0b540c2e00d42804016055580f516007140c92340380c500086002402a0980640048146400210305441c1c1d821803485140002e50301500d0410818800402400074034516000903403e0354200b101d504001901c030f40070322103e420050a001c0d641d501120140d03c1070070000d4100101080f04540f802541c0094005103110303846658a801c80303641070f004100380460041e205074450001c41030040e60046000a01c1d240c00204603640c27000c8240304103001e414958004401c40d842e0004100d0080d0284a600900318800d9000388a0185d4483c0e4155582916054138100d4565801c0c0400051034a130f400369035128805000180300c10f01036007455038004000c07004007280e4903034020000d1080c5014410300d406009100480c4c600f503411600c80c0700749801010034180c002c12220 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 567155080 1250 567153830 567153887
    0x50a0305060c0304152406051305130b060d09170a12090813030309170f03030a0c090e0415200a08040507030b10030c06030501060e0103200c0a0c080d 66
    0x1d5041700e504020404280b0048001e104c905107001401170800e43c800b44944004549640300d10111590039149140103507500782058200445854080f641c90002a600c605d150b1603521a08046c104000c100c41002a601405007000c100c0710b0300201a00511440c200903030020150026110032452010b60000920013046240403800d40c072a038181c0b01400300900318001704140e03101c10742009440741181041360001045d500956220716000302c0c10b806820510018807003240b03540c82480b800040d8607100e048241c0c0c4828000a401081c0c9003903031190000160200741c0c503285d004105224420030194001710100d803900845034090b400d03d40c030402c003101d4003190a05c00100008409075400000000c040c2c2040b0310302c8e0316404007e102c00c403900c0a4001000494500a101d00c0c1e04846181e1a402c802401d9078004400501c164009400c2c0c0c0310f414200d40c0e64044110002e0243e070441c2c0320040418058500340740341026150740c000b4941c0c1d40156030f4032100c2d40d4883d0308903100c1004042031801032900d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 567156330 1250 567155080 567155093
    0xb0a09061e060311091003030c0c0312030b03010b0316050d140106060f0f0f09171e011a061303020402030c0705010e010510080d08160e06130f050a0305060c0304 71
    0x121101c10450300480541d41200302819841042103034840ca0515801e80d00d41070030f101d03503942d049a0050064060400030000f1a003c2d90303030031903002e02c0b070041c2001a580342c1e03076964104944041d04c5000240c0d1034002d202181006d106200041c1c0c0200c004081d0f001c0300d040203010480f864001e1a018a0404c1346174001c0001b4190014964440c0c80300034040c0c0b03920340b40014150241c490388440021000d80c0c040b42c82c28020310707000150312040d9440b1541d66081104140d225088401e5034021481000428100001c4c0c00d41810a54400180003151101413400c40e402041401010144144010000c1421004441c1d18040440b03178166805600d1380c1c0d8090b181d200070301071550058a15400c2004440d8140010362091340b1a0302c220a1401c2490744401e12540d80d41f6502e52680d000c1804040031610801020350014100c004510b48440180c1c14040462140e03000300310a4490500910000e01ca02d40071b5010a101a14040c1c5051203080d1858503410b0b5218005032808a050380300002040c00d2141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 567157580 1250 567156330 567156341
    0x3030403021c0314030c07060c0c2003060c04050f0f04270204061d0f1005060703090e0a050610050703030b1f020d021c0e030c03010c021c020a0b0a0906 67
    0x30002d102c85041040c1d0740d1440032075000d03840101c1c0050921124240b2240e082010f40b4007400041d540720341480c000c0e83c1c440700140704040441040c13084d41c00030840000d5000704070141c0d07480d0b10690100c029100c1d4060616045014100c1d080705102844180b0903078a03810826540e4501c1200d0094684c6680000300d001889110344034900c6852007805010140c034055010745050744259000c01c051641c1d0800703a83c1c03503050113084030640860480828107800b4a00d078119001425500c403070908594800004050303900a0100310007041c07000c002084649108c0501c1035001d18420801d100320f1506e1800154108685421603050280100c0c481090600c2a8840d0003200c6024149040c0d4a521004c0030807807030480100a0b0051045c0c08800001c64804a01e0030581d0b042e00c000f03042c0e281d6103040b0641d00500210007054042c070442c03103003a402e540c003402110860b50454001d0301d251906a164495540b04401c107890035580143c610707100080000c45030341c0e071111000e0000200764405140080c003130070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 567158830 1250 567157580 567157583
    0x1080d1b0b090708100c05030c0912010e2a0a0303050309010f020406050702040e1209061b0d2d090608180106140f120a14030c01061d061f03020903030403 68
    0x1007440c00c210004000003812415281d89800320350401548000a41c155400c1e038044600058051001c101000b5506000c0d149603140242408183d4107d1528282100c007100e449070740d5580b00c81d510511301c000e4440401103040210f03a440c1162600d0030007054101d07629100c0107042100010008903c02801e5004490480480800350b40e5995036100040041d0008202603104a11b00040200088400502501000034031400c070350a0900034820000c09800c084039200e00140d0400030400c15940600043c108020141c41740d40c29103540a8a1542e000380c500010004220140603407441d081d0006521000c0360300a10704110f0315540c13407056140314150b840ca1040298205003000c81c4520f40b4540700c00421805031038150184540070304100148451080c10724180d0400c40e5110b02044508101001c00c2c0c6452084030300e8159004102402c659455003c3e000400c10387c07036100c012080a60b08290410400c480d01c0c0109202000b01000c00c0818407110810301d41d0000c0c1e4184075407414005c1c0c40056 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 567160080 1250 567158830 567158843
    0xe0d0c0c090504080a03050c0a080403030b011403190b0a06210e1608010b041a09040804050a080304090f0e0c190504090302070e010b04081b01050d0504030c0b06040501080d1b 77
    0x908107444c10b4580390f004803103140046400c0c000014a403038148016950a01490303904c9040584843d1800d030014111044518100b1640140d483e0184041d2f01c000c6000f0011000743c0d0800380c07038041043e802c4405c00101144980ca070b181c010400c140d40003094a1078005c2d0315050760050801420f4840007048804100c080e1801898840000c0c0100e040601d011075452400a201da0781c600d00030881215601140b20111108900c400111800c0000c225035200d880b420a00b454103484800007424941030b41d110018980c0000350a00c0f015100c0d01489084803000310040c0700d003060b00d000d0191200d1001000d540600313448054104220881090328000740400381007000720134014200252220300d103005100c0501c0b4414000a5030150403000c0b2000c031914203025103100310509144600001d06201c000f03040003001d22108041070340c58070589000ea4800d464a8a80c079007103141002c09464000d081d02d1255151900410000740f000c2014603112240c0d1074400c10030b0716407000e4030b01a0360000101400c003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 567161330 1250 567160080 567160091
    0x3050903072705060301051026120d0c1d10120510050312070206040303080c0c100f0506150a0e04091a2203050f0313050d03021305040e0d0c0c09 64
    0x2420001001407415032a482d00a00c11950760501303060907500182c488450040100500304081404c202c1c01040b01c01e15803112040042c20030b0b188524040d0007110032410004001034044070384900d482451400102070030002078007184106419011681c0c00e40d902c2c00b6403800004900c0480c814030141c3d264445440003002a400e10200b100e0055000b4054103000303100392803101968000003420b5440f1a070740189190301c0c007415a50100c444000c043c1c204085418148030300d01c9429414400352100003450400000e4143d0246800700c1512070150000e40a005000ea01100007140b000131190751003c41e013000c171410416440801d00400c2c601c1006000f088071041e1603610002c400a0a5011324199500e0807013940080c6000003101c05000c030f005000c92001c100e141500129031025503800106003100b03110f031100c1529940d003016041c101440000b540083d01c0303c0042071a03407140001d0310781590108945012400c40c9642c64070101c40a805022061322200200f000901c40400a0b064a9005018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 567162580 1250 567161330 567161369
    0x31002091201321302040902030f0d020109060b01030b01020a030806030a0f0c0602060106050c0309090714071a0109020f0f1b070e0601031811010c050f031201080d0203160305090307 80
    0x305031a000043c00160ba0700010078030302801c05500054090404a100719002003040e038200001446401c0301280c043c0600d064111406605100c0a002e400464001081c2c210091424400316080d90500034141460584c60903242d9074001a28120b507641400d112016880345030009103032030004007004040c41c020320140c8042181c06003081040701d2485e000ca480f070341d032030380c00c1521180105030a1400b164828003840315546012034a0540002150810510040c8070100c0303041c01d60700860041d00c0440500000340150305011800c0b500410b4190811403c24108155110883c426a11118903c44020500d00d107060808002d242c2803440c0042194569030b61b0301c00c0c088041004440044c01b00317144c0505c202c108a01e00c1002021035034814000310070500e00000649220001d0135060300c0500c1184480c0c01c945d00c00b0402050707443c0a03e4000c90482d03160101007843e00041007402e100310b402c04c2c08800c041030407980c8504042075243c1402c5031901c8420300828a404000d074000702c200c95031081e01c100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 567163830 1250 567162580 567162611
    0x90115030f060501050901061202181206090d1806030b030102090307060f020105060a05061b01091e021320030c090306010603090209090109081803010b1207061805031002091201 78
    0x1800c14801d5200f80a03070b80e17843d81040501c4200340f2170500818583c03040d40d503844c64a0381c0144101c11800c11a5030041c89400c01264003803070501c00b50449030f031150342801110f000c06c204220040080340340c26051075068103e00811461a40704500034162a80403154090707130290140d80c030340e1a0180445130740c0e586c0d59500070051000e03104100c015518101c003264007400d00c1c20350881981c2010704158035007003449115904031810451070341c82c155038038540d65002865022004950500300b0300701500003022801001010304400100f0101940350010507034884544880000f903040c0384889080e100e55461b031044496104080c40307142d05000742d40c0081440394140d807000d64098000c1d64400d240790b588500241c01c80d580440c000d031100a0900000c1801003814440c00c3e10150080c00128140072a203001c1a90604044a42c01e8580c01c03881c07003800401d610200c2c481d0428269047c56004500d045c0c0420b4444004100001440c1d800050790100f68a074034482d0012929208020000e20400c80c4140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 567165080 1250 567163830 567163853
    0xb03040521161e0b0103200f130f090c060f02012c1213061d0a260f0303060f1804110a03081305030706020d14030402030c130f0506010c080d0509011503 67
    0xc5130110304074a103600342e0071200041c40400c0e00d406840098541051000c000d012780c80780c2407190401e9160781c41040105194051801010300c544400c2c04d626082c2540644104802409038046a14104032040071603854503030402038401428101d09441510381140b820002102c1c035005090704002505c40c1c0b005507080303e80c4e08807481070356003410011a81c0306018001040307001c0c4076840b100d1000148440008140d27148000305075421504d00c031610700e81040b4201001c0300000c5034a5080401013203002e0408002d010032a0400b01c0c0c1005154507141c20301c0300e403e40050006041d446507100300d44010f840e8849590301454210740161b4817841442800c280c5071400d40030f0305019008462000404038000102e000544903603444e8074035510f0b5165405180c40e000280166070500c41d200c2c0304010b64881c1924800f01040303200012400c54000c40d10724051302d1001d0a441d04000b801c11407500400c40c13030300030b03034408006a0101180d252201000c51f8003400c10014008901e00d859440001000302a03c1d41c3d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 567166330 1250 567165080 567165083
    0x60702060a050901091512050709090c09050307050d0203030d0915050112020a0f0f0b03090c060408070e0f010501140706151706010801050606031f0803040b03040521161e0b0103 78
    0x400e08441e444d6120003038810030340d203008800f141103102c103402c00d04115004541c9c409014a080d00c40a551400712100b61248007401201007001c14100f4002030030103010740e2014080c1540e441240005680c00319559108402d07071808040d58541c41c2e4020803182c5044594140e80c0c55206221558455540c0840446214005c80c400c000c40b2100050300031140308030f0400c0b1551010108a69843c0840141603030f40014110351103402101d449070010754507440a8000380100c9001020031600f40341003600181005442d0305020540400100007683e48190f070040b96a000d07040d1141c0342ca0080c9060b40190941c08900b9400006100b0007003418002c1c100624640105142280d50590b40c1d4008603081314425500c09402ca0400c00c0000c16420741c07920600440c80b0b0200f10074a40540d590501c2342550010f80262900d04400004e01c000d000c2c0030032035000c103511420001e00400105080d54107581c401d031505080c05646010b440c0003445030000780c03a40c0640e000d0a066803095110b01d440d921144003401f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 567167580 1250 567166330 567166337
    0x60602120a090e0f010801140f01050f1203030718080a11062506020d1d06040308190501060507060f0b0a03110411041401020610030506070c08091903111509090402060702060a050901 80
    0x22100240601d100c11103024801427032101c0c10316400c00d410301c0000543c0d60b41094005105107000f89205804100441c441c0600b82d0340c41440c4050310940708100100c1d0f03071100303049038040300400b4003081c081c0d030050f080c02408442700303a510340364440505402200c07600076a50b44540300300f800c0240040340d0014030882e100200c00b0003841d031504942614404070690104e240ccd034001c80003d00002e0090481541206088900da120113032034410038019110242c000400044d80842c4010400080d8042c0d080c20002c403000922442c0350407800b25070814218400580321800a141c0c0018907141d95000403981244210700783d9455445031601401c2c0704820480e28014400e500000d40c5500c400c1c07232400305907603101000d0503183d12003101c2240d407101118025500900d0810440040d56181801941010038451426000a1940c10319170350201000702001d00410032612600391503501102201d5004500b210310580c25283d17800807410501030030070000d400c05400250400e882c0e402c0303c081c2c40d041c0000d80c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 567168830 1250 567167580 567167591
    0x603010c05210411060c1b01050f0a0f050405030109061509090c061d10180902030907050112060305061003050f03040b0d1a0307091a0301060602120a090e0f010801 72
    0xd0111014460740b240800c81100b890010100000101c1d155500507000340c5290068040240005400360701101c1d4448aa5000e451140d50421542e4607401485009013040c034100055030007104841d1043c05a40410080031105503100c00e0700860a41d0003406c00034000704036010b071500e040b10040800a540c84403a4540d41c400181c00b48450180c940502d0f1302c4851080c0540c5820740665030945902c22000d0880d050980b1000d09031150402405000380c0d075a144080070790400259003882803182c0006640ca0b00400401c500200c0000d44107007190000c0c80e100d0b140720b0b10f0440d00c00c010b041e0f503000181140903880503ca03032241000140b00c160303401503064804551038150995680c0c4030b24803810600010500800b9a92240c640c0400100c00e400205800b12000405c002814454107822004866584681c0d80e020419030302d01a2024010940082140504100000e1355882290404003a404400500c003c941e0f4410042e43e001040514910701090500340610900d1a000740603c0c4555071809 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 567170080 1250 567168830 567168851
    0x5220507050a1d01090e0a06030b040825200121020a020f010c0f050306130c2c030304031b12030504170a030816031107060e0106050d0309090f061706060301 69
    0xa00d0f41d129683c905031a074034403061a086100d0400c200003000e0030680750b41d4841c00000706441910040c4034600c60042c0c5ea645544d48600e9032002c4549250950b19450324041d00c8000502c0c05001001c1c0d0460888504900219080101c0e1071507000e18072a00048840201d006d00b000440e0042d1507070b211070f9000d9031040009210154201c400b10340c508000100306040c0261b28034080ca00450f04000302408054000c2e01480402d8150b9150020940004000000340803c480c0c000e1035141a0031a106455541e1206010009a69015a0001508454206040c0f00281500c405030b01c3c001c18024580024079601410080c213641c21610a400e05a00715515240a1400102e403030440c2641c592180c2e021500c400100c0e100948240e05000145560350150a0089803224081d0549521441d00424041400414207003912215441103010740108403150300000d0700010554103880f0400c00024405162903007120282465500010003040d01c100d001c0d00180c0049105486402c00303a0003400142d244 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 567171330 1250 567170080 567170117
    0x1809070f02060c090a12050a0209010911091005040509040c0f1401051c02040902181509181b03010801020a03270609020301020d0e0303011a0a050405220507050a 71
    0x32011200503048400080c91104011014000c0d510780500000c801300d4840c0c0302c2c26410701d01c0700d00903103640e48a082100110b10340785404501600721010b084c807607030405240b888400e018101c07166224460003030001c04028440c005a0f0002c01000b030604c0d07900d040ca418110307005412800340394810110f04e40041042d51b01442822450b041c181e54092800c040304050925000d80042d02090683d003c010000d48881180054000e0100307400504031556802c004120386c2041c80f031503005440748107109000300381d90b4020103804040c504141204080e651a202d646200500228200c04164044000b150001055001d070031103a110b031f20f0801014100c420f150f0760004003451300136281035080c100d50000a80076000041528030240000d400c01d04e440020754280c89510b00c3c03040c02580040010400c49010b80d03054241550003242c168501001d10034020b00e14400c0340180381c001c500c8200c0d051006e0444c850000440c5844e0b44041019091985004116602014414001816180310102e04580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 567172580 1250 567171330 567171347
    0x150b0102030a0e090a060e0c09010201150b0306270f0906090a020f01030906150816060e0a050409031205090601090b011718030412062c0601030b0603010b06180907 72
    0x281d9281c0581c08440f0400300411003c0080056640c81d4580000180c3e81102c103c2880c0581c0301c03d035450b512a030100e0300082c210341c00070708444160010004100045203082d0100e03504032906540d006d804040c1c064046414441514502c04e07100342420030002d4841c0c0d680701c3c050041c0b01000a0301c0315034540703e11040d80c9030a6890003a501c02030a80701c0450a40c0603500140000b0b204da10080f41c1070714807000110792250f0720781c03204109070440c141800509001c00c2210011346614100440580c0e20000400c1709054a070280500a03560388014070140343c0a50340311803803400307514070038426480d01000c00e54645800b072281143c020f082958900c030941c05980040f05e407590308103070b840007581e4280c100c2c0028826081000c4280c0000c2101061660918650246480c06500003181e50034200f41e0110012650000e0b441d44809106020400c0201c0440c003681129082046030807a615006c00003401050110220303503014200161a00c20345441680d050328400303044801c000c0b5995002e00580c1c0901 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 567173830 1250 567172580 567172597
    0x312081602070519081507180f09021c050711010b010203040503060a0c090b04120b060f01020a1202010617150a0b0112050c0f03150907030e0a032307150b010203 71
    0x80000b00e090103a820320003080d000108111340005880c03591090b41c2401c042e0214055010800041c0030488200c0c0c0001c64906840c800c0300000b01c44600d018610301e070101c110f024400380d06400040b41920f00e44011807007030300da422081c0d00b0001401e142d40081c007035090704442030b0342d10750916100780c0c01c07580040213a40440b9030150141c200b6a40e513000441c01049109103034400d02480713070808a1182d051402920103800700e00002c25031011a400c01c4103650f2401084144200c140c10030400b56070741c0c0814851307642036004207061084d40b83d800d0282e000d0001130f0480e0101c0030054105c030240d91400150740c10703000c8501d00890324a840c1d24510314103403440c01c251507012a200c8621056088103e5100603030141c24000358905001401d10083c40740da200f41c4840140d010b000810a80f14540689056041407030342c20104511007038580c0c802d0715101101805028000105030415a940030a1080440c0750b4161021954a18240c030740741501c807540aa002c000d50b0b1070b00010040550000040301c1406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 567175080 1250 567173830 567173833
    0x903060c0e03010b041b180314161e06080901060b0309070942030501020703031a0d23070b0703050408070f0e2202030f010e120f03150312040312081602 67
    0x1c0020034410740b00d11200c0601061100c52a500008c0420303003c150700304e44004407001401142410460700c581d4a00581c001590300510515065940d1048003408000c454040c00e02d03d4980d0b80740a000341c010015603020300754410380002003121a51000c80d40c50155004400100034005124458148000c00b01c0c0c1551000e01e202030844c581f411100728800c901072060070300c0301003845e16586d81d90b0070fa822018081300420384820700c1007413000750f60410601c0d180040d200070003800200d443d0f101c0203000741007141401e155503203980d40500100740f01d11405071080c5021507030303200c00e54680205954420301c58065a400b8609005c1001aa1016401d0440340e64411112075034407000c0303000010001009080d640c1101510003503005031030501c14010541008000007034000c40c82980d140c1801d2201c03030843d5113101b0400401d4207050408040c0c079048403003800c84002c0d850b411000b1a20b4101d202e0302c1d002a100c4041740004c1005440151505c0c606039a03603400c0300c1d40d1a500c6452844103484043c400c0917 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 567176330 1250 567175080 567175121
    0x27050a0605090d12080f010803120c0904110c0a0501140702031c2403030e0d081b0a15150b0405030307110f0a0603140f06090708070903060c0e03010b04 67
    0x5041c86200580034215008045002c0c3c01010f690f403150f01c004400181c0e02007000c035001c12002e603000c01841401021039901a518101d030141c2001302d00d00d0024441c251a41011038903030318584880d44890010340da1154042d03507841e103031007400366a00031085088038150708188411030148529803000703015804640055060481884c9ea00d1841c4010403e0000c0c4d0b0380d074031504032942c504601140348082c2c5410280003501411414024002c0451403105030040000b804001c001440b44411a600b01800c0f4040a4080718000100c070b0174100710200c043c2210500448209103c1d40d2544640b002500541c0e41034401035694042208078001c034450307190d00d600b0501032180420403101211140c2d6000238003890300c2e0345080000070190031040c0c201100003603445c204500084078811403141c00c00b55007401c1c40031600d8640700040d100000200b040c810040d209021a0b03006000d054280042c643c00b9006100300c031400e050041001c40d036491110320079820308500d801c2c40d040034400d4450320044221071445 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 567177580 1250 567176330 567176339
    0x1090611190303020d1116110303090d05030409051302010504231e0a09021306120f050a090219030503031b0409020408150a0b03100906090f0327050a 66
    0x50446204428806500032105100d2600d01d124204084241c440d440c0140c480e580d04140700300316410a8044d107980d0104200341d9840c6810a0340e004c80b03a5901480b0f4910810f5101c0109055028005034182c01100f040e280d5420400b001c0702078419942140000c10041c0d035180c07058034455000700c80c0a404140100014081c075580c40842c21402c41c06050680d45200c01203001c00c041c0071b0001141a00e81c002464961514549001400014041c140342135081111419454982c00e42600c0f480b41449001c1400c1d06911426800c02009030003030050410442c03030826101030140c203424104074800d198001e10304444008000e41401600d800c40c00640c210b0382c5031a1100c5880600c0b000e00e13807200c0810f1000013040705a60000748090002070b0007500c0c42104060810200010203001000003500301881c0303040585000591040b501a006008900000341c0c1c20310038014103003504085c05004003818400140b40c1c0100c5009280c00d41045201d00904580704280e0b490306480c003c150307200500020400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 567178830 1250 567177580 567177587
    0xf0105100f02190c170601030c05010804020307030803042001050c1e0a02030601030c060f050a050d0906140f04030f18120602040b12011409010303020a140c03030a0824010906 77
    0x180e00700703240122010072140540d4010300300d002000c1280c0036101c0d801c0038020b800841941c2c803032030114040105140d50455030b9130741100825004240c10000c0304400507055603000c1100e0002903401010396596405e19041c0740b031204031502464101d034078504608024035407252084603007888240c030103042c0c5600316000407420b212050107210403600c91865000007503030782401114020341c4600c00101c25585820005054600d0a40000050150501c40000c00c1c5420000b2201c455000d01c00c00541920f4503c0e08400624005450101e80200c4504200521041c108428042c5009860340f000408a10700d0448200e83c242c0b904844d010f000e0b40081100d61105000c00c440745100d00000750030183c489000c03500503042214501d5840d01c1754001001301c254030312020840d0500640b00040650b0454401035520076028000600e54204208410b038011b4041c066410240c1006050f40da403003c0804005055003001c1d100c2440c80c0c2e2010b4030162186080c440c500014110607198402c40c64582001076 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 567180080 1250 567178830 567178847
    0x6180f06031f0b0a06110303070e0d120e0109050a1206090f020612180601030c05090910062d06020c0603040602131203180602120d0912090e0f010510 66
    0x2034161040001d90b00000d80800d1440c003150140910019a5000002c1048105051a80200207105426011643c80301001c000c8952000750b83c148040001741381030105094402c8490040c1c003400d40c030441e403111181c0c031030702060007200b00f42d8030b186029480d0410055003106900c036000e488920351009100150a81c2c200c070050714080c90f07402101e45010303000f2880340e80c01103c03030444803122181080030780c02003488500d440d07203090001001150705555518045e11454040d0502c10f001c1c04e0005090050b0030089416400700583d000d11540d542d4840510322a04040580341d9590003c034000704145020b90f03e0341c070455040758002c00385448140203220441c0c2c40a0003d8950782c0d000c1109002c80034070701144800801c140d10404108030050708009016403210403110f20341d110380c02c1c010002607070b000a0545060000d600403a03a034000a9241400600300c04400074100749402c40420340b1250000ca054045078562098280b183c0d4804501c150f205800b402999403010004454500b40c510034001d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 567181330 1250 567180080 567180091
    0x30f0d0318080c0114010b03040b0109091401091401110c030a0c03091a270f090603030403061b090605070b150a031e02010912080403020607061808070b06180f 70
    0x446081c109911110311591090640c0b0005079190307a654000016218080343c01881c10307800b01419805c1c075a440031403190042c0f0484502d0383d140c1108106020500003240c00034072400008021140e000c0c5052492091881481c00c4154640000d81c400c481000c412102c29100c4c1e04050751400c582e80109603500c021440c0141c040101d07212010a00912400303a20003460000c201c2540c991081480352a440752610702030380c025554000c0b610a560301c46d201c4200035407500f21290500341d40e80d40c012903c0c50265a101810f00d50418840389a00c00ba407c80b034400d5501d2a5480500f01603c82c41f06407250b214001e8002d001c1951800000c2040302018400444100002c250764401c0c1d59a442c1c601c91f1910a00c02032404801031180e2100b19a000003a4170000c00c204180c2c0000200680c9642142e8002d602c006030094400085480400c807440d0702c01c141400c940d651941541c0780300d0800d0307480f9801000080390401c58003c082501031410440042c0003540c1402c41182582c0d07800401100a0405840c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 567182580 1250 567181330 567181361
    0x1511091c030809030f0316050c030d06090507050414090612010c03150e010b0f09041b020c041b0215060d120f14030c0313050111041d06040207031704050708070f08010b030f0d03 78
    0x92272294801c01d00040800b01c0129501044090900c50480c0880d10003408840600c10304220400803100c8100103140865002c41e099aa41d98072000030428650010310160020352034050155a025019480042030060740400e01e030200b0b03120074401701008000e0081e0380c6281800d1040c8009145540d00900c14a1005400890854015280076028032002a6a03401507009000c004c8018103281c03003190300c0f4200e1030303802c02011240c038840a91a10460f003418032201d50101d000408a0f290389001220581d0b00064519402d900b1103402822621190700704c1001812040029000303003148003d0700d000e170892080319440c584030140f210b12020550f900c11120355403213480c00f68984609001400c0200310001460340c40c4281810001e1144100601e0280300b28418403907100170944c000c243e450007000c4005000030320b44450411620308a050b601425452082c0707000030680c0c009441c0340c10111a440c60083c0304a4210008040d101c1070300c04942c541d10b50040c0740c00e80102e4807903000038420b011850f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 567183830 1250 567182580 567182587
    0xf050c0301051024090603020d02040f03030203040503100501080619090b0a02090f010305042d06020403051612111003110708090306131511091c030809030f031605 72
    0x40200303003910021650183c5060040004104094180000401544015622881d01c0040b040042c00030226801504105075012031a00600301495040307801400300c02c1100208655a40340080d41d0307030f01500804e0301034002c01c01c0410294615004041c145c8000c0c4000c2c107815540c001d001c0780c0c070b4030f85043c950714a00c0c1c40351280c101091004810b42d008948501c0090f0340c2c2c4400c1d078140181c1a0751900031904040c541070070070000c43c0c400030f1340070340603100c0c0449502d52034403000c2d0040c07500301c4015000c4c0500d84006000000c102e800a00f8040d0b00f180c0c180502400f940d5282c11442c0c030741c40c50f5000b030314010701012580514503081e43d00d160611650308000034000c19000441d480c41e004900300f22020342c1e0004112002e03107400c001d0700b98083c4100ca00041ca01030381d07994800c4d0404044171030900207504c031442a001d901030b07007041d212040c1000c0c08120307000002e000e48000f041e003426001c2e00840e407d00085245000044110390540189003001c52544e19400d00f24a05121200c690108008083c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 567185080 1250 567183830 567183853
    0x1106040f091a090403030b0a32011115040618030f0c06200403050f07150c03051c0b2b031d15070506071d06031306020c0d0e040506030303040f05 64
    0x4843c1c9010701e00a50380080d1400c0541c091119140482d00246014510084c44001401e1640c0008980300e0500004110b581c0c80d400068520707070343d40c14401807140036181c0c00c1c108402080f90024821401610140312201401200150064000300043c0c0000e90301400d262407140100d65803032001e441540300080101560f02d0780b5a12a8500d850103410200024040050020410816109040c170801610155103495004130061004001107001e01801003c1c002c05d0501540c1565102d808482080340c0a40c0800200c2004181959109200e0706040080e050000c09a01060f0440b500e88200f941c03400d0880d4400307460000c80c0c04121103481c4907003056070400d601c800c40f01041040120000d07a407596030601d001802c01e0002000c4000300007a0301e030041044000c0700c001d1402c124059134031a80e03d40b1080041140550f04075070180c11180001441d480740980001d010041e038405944600215024000300f02c140e4106842241d810b1f441800403402040d882810460094815812984442c500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 567186330 1250 567185080 567185089
    0x70605100314010204090b060301120f140d050325080a0902150a0c14010b06040b0f0c010c0e030f1f0b220b01031a0901031202070518041106040f091a 66
    0x5a0720001ca42d650040390400100c510340c001c815614808070b41080c11903040c00320031801d001140c000a480d54504004c54414044680b4002015141031001c8d20402c1450100142c165841900c0350700c560300c000c035510041c0035644004132000080d503a40e044965100c07030741403002403c289941039034096070404112407503408010082a0b94900d42c1c80f10000c0e2070507420040b01c0701c0c07074071401c4803285c0e41031030192289a52210222000d540894a11584a982020402d5998095104554029841d000411014680100104107203a40c02c80c22a032500001002ca03944032400071030f81da0740b540c010400c588091941d6801161903da4081c100141c2d40d940280b071008075801200c04480180c0e5030713074005007d95034940200f03951892a120318201018180d03001c03c0c1c1d00c1c00705102c06030005c41100108201d052082c8500c20081c0300090440c0464044004000f004c0d540135a02101d00092205500c04541040c0d01a1822210310a00d600c130301e03070303c1c0c244140041c000054101030201012440850300d5030f42c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 567187580 1250 567186330 567186353
    0x60a120f021606240f0519171f060503030d0c0c0206041e09020c0a030e032103160807051819080d020c010201020c21040902040803121b0706051003 65
    0x400c40404c46030b800b014030f0138000c0ca0300142e4a900c941e032070609000c040c03060000c3c1c0049850617910100402c4903803440d600b0000d4503030499900b6004425000b0748040d00083c00100a003904c3c850b02c2c280e070001c61900705c1101e00e80d2003110f415030070a2040381c0c80050780d9848034040700807070704004032050281e900155640d40660000034210265120749200c0c54440040720b00540090f240c110b18107110240d03540e07619a006400281003198a915203070903520140203240005440304a450441c03d01c40500e00d603260000c450304001c2002020000c1c506910410200c1e0055201c2e0312018030304840c0312058079440d030290501d1a004406080c50101c88070400300580010320130000030b0310b51010100c100a04007000700c013603e811603005000c021803801011030711003050840610032442880c0c0d4030380d00510ba4080ea5220481c010701c040307000944280080002c0050300400c3c900700090740d58a40f200300100604503901c0c100240c0c28400c00002030301d44e0344100d8100c40304a44050301280c0d2a5910341e0f0b00e65 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 567188830 1250 567187580 567187583
    0x11030705030103120e0136080c0108160f0507110d0f0201030e0d080a0902010309060f0b0a1502030f032701020a17060f011b08030108010c0806060a120f0216 69
    0x144000010814044503001201407203250b468140b103c070818500003080054002500300c00c00890b1142c41601c8101c1401d031002c601e51140b40042c0342030340da00d42c2315102e28054a00c140450035180005846004290201e07007480d20230f40f1480c400b40c103905011034142d00304c50000c60341449004403442407aa1003034115864603118020504a070310a03840010107840c0044600e81c0a035111007000d680064110b081158041d50b4414002a580221300040740581150750000d4103080c03401d0001c0e00c143e440b41d048069955420364030300b081c00d80e030307007448911140c51420aa401604107100955203107044400842d041207040200000f4081d4501c05041940800380d200b40084c2e500043d90040c064002861280c2c0310302d08025040307146400c1002c11003600044140e0742c10040701a004203103000d14480100011780c0c004002540b42c0d0f85500b0310038001c3c030100c00031501007400f2078000f0f491417411070100c0b14032840c1c1e5a80d400c5641200d0070001d014184c032200d0105155020b2007083c8444500b030803004030b804e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 567190080 1250 567188830 567188837
    0x3030c2d12070303060b0309060721060b0301140a0b0906090f06130806070c0317070c0b040b060307050429030c06070503130801020f0a120204120b07080f060a1404110307 75
    0x102c51078500602220721030303842900040d806200304582040c011406640c05030b02401c1c058000003801001c140b0b2000c08244060410340741000101d080e00b1203070003440c140e540708030301450800071000401c00707400d4032442171100c4100e04115042d641d081c080c01900c984c1602400d089000c00018000901e50b8210f4000302d200c1049000c400c124025003000801d4020400d800d00d0040081c96440c010700503c688110101c0d00c104500104103000e12a62002800715000901c020702d0741003c0c40c1c108844c0006443c2d0350300c81e20a5000108940c0781c9440b6101ea011003008842c060b508082c3c0d0301d84c901c448244401e542c9401032980303003c415100e80004100e01846180a16600d440e012010084d80010ba000490144e206008824056209604540b0380c0115824110b130902c0407964008040d00c102c1d0841400a410007446a0800805070410343c050900c81d103620710540d8481c003100c8803085040750000d0303100d91110300c00c0080415030821580d810350054004120707410084003418035648280c0340704002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 567191330 1250 567190080 567190087
    0x6050c2406040515010c29091606020105101203032409110a0f050d0e030403030f0f030504050601060c061103070f0f1706041d0f011a03030c2d12 64
    0x292515104540d4014002081301000c10420030001303100c50b101c48801002407000001c42035607010703c40075644500c40c403080704680c1031030501c151585070780040140c040c49130f010800100b4140e0042c02005e00c00c41c012072180312203c1c9401860510492520020740500d99110303020b075110034010200200f84101200c21031540c9143c000c0303501c11984103910150386a5401c1c001580c2603a44660001c1c0800380c11b10f4410f4803840c0142d41000148030648201c107003440001400410581c02540c51803001e040c94075041045880d000c8160190b860031100100345400250040c01454001c4a29880c105c0c081e460010794114640e210800c1544141c41400205140341c0519030342c203611844003202c0130070f58900b54910200c100300300d00029502511aa00c10782d150350100310490341010203840081105811500f4040002c41c08034000c202c2e4682802a484c004000001309040010803511120303802c0c00104252196184c1e00b03880311809041380d492520404650f180c80c0802000300b10b8007903880a506c1540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 567192580 1250 567191330 567191341
    0x605010c030f0c1a090c01030b130e0f0604150501060216031403040f0b03060337020d0206070317014b0b0307030506040509060f25020106140603060a06050c24 70
    0xe00600b00303e21b40d04050800c0070b03548032500d60001059059681c1740012610f540e901300c8140c18201484130b4040244549000c1000788a00e42002000802c40308201700f2083c0d8031170a00b00d856503c0d046507100c0000c9465001c000044904001700b12541c200780990703040a44841080c10f1000403035010300f0504070040140f1140c0e15060000141c580154481e04400032880010320f1480380203816842911084000c0c1c81066446000c03001050680c020450f0f961501e041c6405070001842c1821104894030210000c9400b4460b401840d07040d440c20004251480501501c04401d1a90500d280c13801903001154440849000300b00000a001b88802194903441d203154006c040310342c020070541c4605d00309024403c0c84e031404610190418100206000c0035900d91080d0741003841200e5401c0c020118401c031191000b40d06600000a580481806100c1042c60400300704081c081074400c154085184481004031034025401080e40d503045a090710072810b8006104c08003020311aa40507090705082c0c2c100013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 567193830 1250 567192580 567192583
    0x17071407050306061309081603020f06180a08090607020301090b150a12081819081006080316030908060406050402010e0d080409020f2206020d030605010c030f0c1a09 73
    0x98541a8000e080f146031000002d203086091499207100195298264402d0210740801c885500d40c04d0170003070020ba07409140088d959080c440c2a100540511404907503170382211a00300b003050500d0b50041c08038510f03076150303030311580d0215589552101080025400586007130082c4400a0b0040c01819240d1921108200d80c02d003102c580c5510645103c0800e0000c0421101c0c880c4e01190004400c50316050813030f0864045d4000006510b074010072901541c2d039404000350542e4244c4d0190401d0341c8480c043c640340340e03003901c82c9400340c13a000703410501c02041403d00076104540103900034a001c08200e682e840c0350703c0c2403900c20f0b1020759446896104010941d60081d481c0b03c0340710700540382985282c4503515a0f40c80c90159000e40c1016940004030007090800d002c0a5a4410848808513698900c2c0840d00003030103c0a03118507005401140100300d03910b07010b4802c1780220746040e1140e4806c0803050b40c0440c1c0b20707240d103202c103c140211592482e0104464140c0512440e507100c6a24000d42410b41525 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 567195080 1250 567193830 567193843
    0x50a050c0c092e03030f05091314061c05070512070b0c0601060f110601030605100e0901140f090606010f2606030f070609030f0501060b0f030610030b0306040f170714 73
    0x2c11002d450b1043c03c00010740d00283c15840c031055031401d10f44850a0b440020103030320f501c0d84881d041c503082c01c1807402e05410060080b8020241226001b00199102034800b103041c14410300035010750441031003080365003840074981e90071001c1d40e011f955a0540310741d2040c0d803940240084c41301c0b070ba02131001401841e0b0000e000403230500c240c2c200200700441020b03502d552414140002421142c6a0b0045404503030140b41c580081c03d11489000c1d014070340506858024000c3c1c020500c410101040842c600166100c56a4002c039648000f9181d1036446000640c1e04001c0000e802c1c0401100c40c401c03908603851343d41403000c0c8108000711a0900e04006042600d04044c101c0da0179910b4000e40740c104900e640105225080300d07448081d20032040c4e014140940140b0311940840c1c159480000d4100060814000551117040202c4005802400c032407401c40444409841c52501a405840800c0119540c61010f0aa0034464035001042c4c010341c0c1a09819500040411104080490328800b0a1081032002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 567196330 1250 567195080 567195151
    0x21b0322050d120908031602100314010306090f0605012301051317010f090c0e010b0a0e060309010e0d0e01080a110910050f0412110102010c050a050c0c09 68
    0x200c50142004000b5010030b0b00910014420620b00d144240c405018022aa005004107401d403a100c5050603010340e141e00d14420224885c030004c4c224065210301a12907130841c1407040c8400501c070b03804d540d203000042034161010b841011302d15504000044060044030701820900d0300e4040d20103031100d034040414400c071151505100090106000001d80381410ba400c6800c541c40600d032000300380c2140c50041c12000e000018250814144a003809a0200c04034100c80c80401d11402396a80e5019010041c000d5141c0b02c000903890030741c08407080c5000c03000703560800d0007840000f601342ea4600f40c80d413526007901c1e001c00218030346000030301d29507802026480d40704503015814000c81c9100b6001e40d0003441941c000d944a11f1200f5907210500d0700c218252848815401d481d40d5849850b80240b02c2d0082031118211110940d601410f5095441800343c40a1043c69440d45c40c02c000407104d00382e4098104c0e460094091140c0300490800d9680c946013a40134000403840c0c0c3c01c0f80111100c80f8444a04e24829 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 567197580 1250 567196330 567196387
    0x1a04060e10021f1d0c1c03090e040b0601181a0f0d0606020c1306032a080601081b060715020904111b06010815071404051e0907020a0c0902090103021b03 67
    0x17210000e61509503100350329800c1401c00c5462130700c1c28034041c1e407541c509420189a2801000800c02000b4000c031b03500d801031100340c0755002d000301500401048040c560141e04100d20310608085da080802001410340310840030102ea0401d614610b8420880c4d526501000040c0d002c0000c107440d60810f000c4000c9500c03032a1b0070a0086a085881d080d00e158092420803007280081140c8460380901e482002001d0940340c1c4c140c03501565528085641c41d601e101c0951b840b06200881d1030000d18141c41103441c00741d17010005400301410700455400a400c540d401c2c5810680b00c2448103a91b948500003000606410101c45401601d80c0c00050301c0c0100c141c004c07040a61150541007103810640180d41ea22044078504060045041c13030014805000729030056801290303404910080051840403060001020f5840940e941e4841c102207903902d46410000e02000e0103d48103100400036500185403240042c107000d0b142100c420403030187e04a40d104010060b810202e00c0700c503500019055403408041100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 567198830 1250 567197580 567197593
    0xf09121b0f0a0305072c0403020715170a050415090f060506060901090e0a09060c2c0f0d2d0507090621050f0d091a04060e10021f1d 58
    0x81d13446036242801d0140182c14148107610184140c0b0a4800030743d0b00c0c1d52920000040d05191070080d40d5410341d80201b0040704590f0124445081c4103119884030685c0d01c4105074015101d191071500142070280c0161682401d00104840c40800c034010052924030910500903000034608210b0122180035002511810040202c4411a03038000d4020042c0d581c00c2030b5440c1c6e1034a40c4081800205102c01c0c0060280d41011413494030250003d244500a0b0713103d564000c200c807450340c0c0114525592020b103581c1703c0303100903500209040400c4599085407251f0ba0440c04403104800701c164a204205056110100050100c010440d05000040052079802e509000d01c5080c6280000c480000c040c90b1a641c12429111b0020700404001d540f910f0b607040c0050b01e601c0307400c10720001c004e40302c10700030301d40303044286220b0300642c900303034412a01180c0460390340d8460f5400c001c04000101ea13041c400f40085205440e4050309450201600442c0c40d02d071000300046003603254140034211b128420300c1000341d8000b034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 567200080 1250 567198830 567198833
    0x1050402070b01031e120c0501140124020f07080d120b1813020d0b070306050904020607030f020f01050a0b0f0906180a020f0f0702240f09121b0f0a03 66
    0x1107031214151303030f0700410510307a038640b0b042410b588001c801009007543c108004005456504404440311280c00f5400030b0150090203250141404401c1c0304a03c280455042e0706040104450703500d182c2d851742881a140882251080c0926221b11134022040d2904031105144210b03422182d0f84480c0848920706002803844080001c0d51540c1e000c01d18809414800006032a400b41e5000000202da401131189400407802e0412040d424012a00c10001c00d1070020701041038685940024171840c0c1c0205410700e080c0307041e901203d6a0321140d03c48801c1d0f114455442e000d01d40c003030003076a12816880f140011208100d208000c0300304413802083d03005038450014407655490706010682640c0c01100000a16110007030024000d00c02c80490610084002c2078210002101e0402002300038000c5483c0200000d01303802e080800c41d01e5000d0036801c1c00e000c1000b002c801c034581c80601003a101c0140390101102d01600c506003001f02031050403010000b4030552860a1034106d0811625501c1500c4543c4010300b103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 567201330 1250 567200080 567200093
    0x5090109020a151112120714070b06010305150f041116050f0111181504050a0b0c0f031c05070c02060403060507080702370c080f010608011b081302060f0a080105040207 74
    0x64840013250004c070140019009806000032030202c80032401c800d40d50790081d080004070301e1001d4bd4210300081c24100450484111101281a1204020000325a8550f5001000000c140101694a00000900001a04003064859404058080e402a1103544441200303182120702c51482042d0381102441041000c00c0180031150341c021040e604198080c01048100d0703618016176110503800714581d05d0104025080102030484503410004440c440000c42078829203d004040124826803c40c50b80e96048801a80040d600700b0f40b00d051158505c2d075160081401031b400380d0030580b200c907200c0d801d10034850343c05451303164002001c3c40640846511032200c4c03000384003440b0500521603840c42486c1c0d42c40d40080d40c803203101a03002018411203076a1310f031000d4070b61b5050150f800155103055070005a203203040c09646500c0003000240503502c0c1440b2000d80d550400507010141101040d042003005850b80802880d0174842c88502c0c54a078083d211008050310710580080380203034014032140b0300044c003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 567202580 1250 567201330 567201337
    0x106020c0301140105221509271e02030a1101021005010f2304020316020d030603021302161209050f010c020d0b18010c030609060501030203091005090109020a151112 73
    0x17421150038403950070b01402429074200110031041d20602e07200002001141d24030000c1c00b20351044c4814400100f21310280c00001345410b04c1507591401c0782801000048500702d254031244003190449000300002d03004641f41030800e10080b11680d2004200825a6804011000144445200601036981400c190650019a601c6104101a00c1a0a009000d40b40c030380e4054540002a000310b4581c82c00b000888025035041800c40d000d0300400741100300e40e91181c0142c0090f41c0c6c003d02a080e204659110304030095004c0208010040e102c10303078100000b21913241e41c0200318896520144030a0618007000407604106c5a40c0341804220300c18100141c4031013001003403094202c000590256030724440c40241c090f401c40a07019075444c06e0500095241c2540c0400e043d685030715010090305840e440103404034030090b9200300e800c1d40411090380f85204150002c580c407410800020448164907800b0850704071403604010140105811503540301540052080300202a440080001881402c030b61b800e80c0c40f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 567203830 1250 567202580 567202589
    0x15091403030720040e06040c05040c0503131b080303100311121513080c0115050114070f020114130315020a050414060f030703050f0903040510030b1c03080106020c03011401 76
    0x143d0302c51556503954496014001d00640300d81502c3d854074052608026842e0b0314003900788128541854000002d1243c005d0340d20550081441004480041c1c864a0925482e010001d404104410740441d0524052001d5800742c044402c0c00d2414905500c3e05540c40c0c040c4900041c00380010201460014400081072004c0902d400d80500054403128200e0340d0300d8166810181c10050005520301c20210154030040c1103524903542140740d1174503000111540a0299080001d00700c2c2440204c02084504454a82340ba105051070386130f181012003000d0954112241403604820030803410410300c1803d44031000c03c585281401c500e800350400f000fa08600481c01507008161440c00000f000352035140455401c5003404c441291649026017004010740402c5401a00c805407120101d8181030001080e1403c3d1200200203c12001002104500404070120115030040000048284500200072043c0d201800ba81d6008100c1d030420b4406898031f0040c40c000c9021784e150103505a1000c154190350342c15075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 567205080 1250 567203830 567203873
    0x2009060703110f0f0f0f010b01091806090501090b0114070803010e0c1e09030d1e03020d1808090901120f02010f0302121f050306090709090c150914030307 68
    0x460712030b031400c1c94a440349400b08042d02c50100c03d00b000c81e90010300c81c0301002038101110a52081e150b005800d0b100024082408075603514004d1024411820118540e2622050006003403580d900c0c616090f10000e034003018100e90307030300c0501081d542e01150340c008003a005070105207031401c142c5e659562440148200f480000040002c103020b0440b8900701e419180608030308080310703009940441c00c030341c2c09003600510901c601c1500080d080d0151807030740c8000781e521181c5c0500c032031440402d40203580300d41140050207543d002601c904280740c0707144451507806031005945481100e02480383c5040107030040d09031000b01c0f801d5140090340340c10003900031603820b00c1c01c10402c0300e192400b03a000c0d000f41d005a6903105090313002c01c040a0040c20102c0c08400c00441e20085441e61002490b4072030307206481c0c6a4503a0001641404044040d8110b9040140f0441c003a400385030f42e40c16000020107214800b0340004607403520420948003510520745040c40120060342c9442100e66518200008504090491 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 567206330 1250 567205080 567205097
    0x12130603020a1e1206090b09150409020d1b06090f060f05070b1608060f010912112d040605090f0c04080a030e120606100c02031f2009060703 62
    0xb031a200d15200300a02c5403030034501c3c042500c103c81c041c0021800032100d01d0140d16054000030480154001c40050400240402807691503540c840603c0d0070401c00300d590460744a58001700107031a02c0409400440c003038a02850b14034030180483d082c0303207400c1c1d0149007002405d41c02408441c555a510400b1101641020000070000c1c140a130fa040c081d4070b6016106c0c0905000308202d94003008810b000600d40d503174880c286070350307094108880c110201051500241c001e000a005441440300300240150092000829034140c00000034400c0b4034824150034103182035151203003104103890400402550444040c4415030801010954807400240019009840d01021a601c2d98444045134081e041000a441c04101a810b0180010304440007242c00f80507a521f400504030000724015000b0313100180040000700541c0702c12940521fa602090742e03d40640c08118611400c0c402400404030304500c408150003402c4030074080300c0311100650f549003010400c18115565110800c03206e0195050402c1c604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 567207580 1250 567206330 567206347
    0x60501080a0e120c0d1701181505031c0207080718020306011206230604080d0c03020f03070f020f01030e030d0e010603060609090b151309110409141213060302 70
    0x141442c0302c00c2030b925070f070800220340312180c0c004a105110450b2648500034102008600c01d021404240704001e050001c0c0c0c181c0c00702103010740e006040701394013281421441a8403800080c2c02c03e81c1030318003404161a420595900b4580520088005041001c080d09289242400500641c1c2c0b203158000d140d1580080014281da015451058048400080405c603917601c03203508100805524a8074200300130885035012861400004440a4542d4000035041820540c641602c003012042c80c01c0301540600c20813580e40035810009054414098035486940035818014000c18494200c0c00740e0400d03040101a80d8a41400012a50462261342c000280c1d08549d1071f103640182040d400040c90281440f5000500c1ca040d03401480e1598010f03086074550740c8940c1d80000c1c0c901c01ca03044860f009500030701f60100c1d5034201d51084200a00501950b821004060005412900c06600498040480f4003000300c15113000c01280c10460b0300c0d025406c2c0742c01c1c01c801c8410440c02c0c0074803483d010540c00140d07180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 567208830 1250 567207580 567207583
    0x905180a050d1b0f0803101a071b17070e070c030905091e09030306011e0905060a03060503010c031e0b09010b1608040f03060f0c230f120a0506010201060501080a0e 72
    0x5200d90b4000204c0b40d40f442917803504034090362060f50741da0210111018045225503003e0b404c12041094040301d0f51600318266600105401c21028041c00000d6034040040c40911300c248502c0c08858a00150540703500b00f0300e200e006e41030701401d010f081007a5140d01a0019400207280ba05031007040300d8441060356246480528601e580040c0c50720641c4900c01d010b0900380000c05140201800d881c0c5c840010140b0a02001035090038440500080c1700840400c05400d1860060081540516000c680c0300c0e04d8101003401c2d075502d201e034a000280e0f14640e41130b415209242030a85c540b01000144a002c8a80d40003600c1080b044c0a000c5e10f030704000030b03089000007195a494408590100d003143c0c0326907441840144501c20b5202c1521640e0800c1181d95840c0303024425050100d605440310f8035001000301619008a0004075820031000707013088111511180380c0050b00060a02d0501841185400c0a9450030b5400c040d1074103055a04040c0f050005a0f000108035901030740202000866268200380729 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 567210080 1250 567208830 567208877
    0x103140c271011060106113408100506091306020d150e01060e030109170703180b0d0e01050408120c0909010f2306180a0f0905180a050d 60
    0x2540442802c0a103032105400c0300780c4040465a04003a140c2d030344c1c3e9035142030f41c114001008284460700142602404810142ca090345950310100190f00384400404a580d005e07421600b00b0311541e03011100d5140c0e056540e01030139903c4030f010f854032825801c0c180014048001601001004c981d0089880940049150f000801c501e4039040c85080096441011400d410030a0082c0300000c3d94484800002d42414028111560390040c003040d810180c418400d242e07504289070440400071503001d980740b082840408000030b080070703110080c1c0e600303008502003084500d001e1411040e6410401000003141c003081c16140c44041202440c8803a0740c550801e6019845800d0140d40d222004400208402c984031443e0020f030380840310402210089000980342c1d0548038481c065101104000035400c4032840b072038000900c24050880102e882e125940d070948803525400880e90030b90f4400406c401c07404007800002100307000030050280c1c0c4995807600350b00c1e0007402d420003050180b41010b0500500031002d21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 567211330 1250 567210080 567210157
    0x10180608101e1a010912020904020d03020a020a090507020708011107121403090307120e1f05070b090a05011b08010303050304020604050303070303090506180c131b0e0103140c 77
    0x4000181c030003c0d186035481203000c100c2e800034082020202d4010b241175407105c0020f400810402c0300313503680d0b420040c0e100e40c600811000c500680c1054801a1194152030000e8184000007190320321749110024500407542e4403400441c0c0c1821006041c4408403400c89038840c1d005401009200045181034403201403181007507181c0900041004600c810102c06001d40721701c40d4001544030359014800b1141840880702c507076840003034404071141007060003003410751241a03418100d00305403054441c2c800f030600880c0e081c1101c1d0810908641000710038480c40c002240048942d0030a2280c5d0f40d00101090300500000742840070000c0418255031300c42094030001e10b0010102c03030b40e600d00c030b01c2c0040140c108000e003101c10344074910206d0b10003220100815440340ca00d40c01007000c0a07054041004049801c5403032000306580311040012400d440c00d9025a54403252100f04101c02540c000404540b00203062000e18120b010030302c5100032411003142d16010164050103010794103000b1100244552004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 567212580 1250 567211330 567211391
    0xa09020f040f1205100e0c130b0307060305040b0703050708010605070302120d0209090c033c01120302060a0b0906041a06030709051f0813050c091018060810 69
    0x5001a4158040204820f180d1183e001e607850f81c1001c0c0855001e44192160752a21034101c001808802c0c02c000c003a18221440304000810000098000b003400e040480d00450002038849040009210300401019000300a07890708100a180000d00200303410018052030042107070014076101490b208108000c0c0004d00c0d43c1c400741d55115061b21001c025030141d43c0843c0200700000018050f81c0c1242c083d00d01c55844102048542c511032100d40307081100820ba034034100740e004402083c2e203080c4445654080c1c0112003281041c42a1800c019140050041802001c94240601040302d600c81840340342c0c0002017079502003100b001c04008606101d14040d00c0542064010003000000c55000401d03504903001a035200720115024243c1c1c2402c0e40d18103a41c440840c4600020035104184a5825a00c00f800344050f101041402c200091204500340c1d420414dc0310200c0c811701c103a41818142d401a19a000010010726203080d07810f41e00c3d03172008a030070491581c0d02c0d50203801c408000030031090040345101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 567213830 1250 567212580 567212609
    0x402210d0f020c0307051e060d0e07170c0a050f01022a0103060923040206040b04080a0b0f1b0a1101060909290c30060114090a09020f04 60
    0x600070400e001e810610300040c03103094024003250802103079500a40e84050000303580015140700c40410664100080d40d0000010014600200c0081c461041030751801000703843d45500d03043c038001c61030407904201d4001d0303045003880280303d80c1c1c0c0c00140c83c102c030002d803084404816a080181d0400103281804109501c2c004181e680c14841a403c1112900b4243c0b01080b0340760b25180101c044642002d1500d2580004d2981c4580215280841d241d005100410365403038252100c800300134a80065102a02c0b903841a941c081c108030380021400e5010075009404203d5141030300c152888031803030680d0072070b1480000541e6450280f180c6442e00d94030205e407009000c100d82d148a140010071490000703640c501c2d41c441103c60503076000c0080c1e41c062070302258580120786854140740d9441e8406d02181c070091203000296503210440002d250302110f104903808034903103040e030b0025000d4001d00100d000142d008100b00380103595010450020358008010040e1030768210402c44507184034030740041d0007075041e88 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 567215080 1250 567213830 567213853
    0x241b020d1101180605181216031707021f0909060608010806090106050108041403190c0501150803070807110306040c06091e03080a0903080d2304050303040221 70
    0x20440d007103102003a43e60010228100da0004500001d83c000c5000040040241000c0791800b180319007400c0f90018403440c045862241000d1500d00080e8040160f44c0e06414108248503685988004e4129003404152528a40303500240d016150301c895958141110104941681d10850603000a8000c99404000b05c549030400903240080902c24a4064824000007888401c07043c0240e00842e0342c1031f1529000d1792155910b10950703d45000044025100c140003220310303441d0414120032981000e4403044001d03450b41c200300e4250707030120662a541d00040e5104000111001044900054002c809103481c1c03078a40c03501a2101a8404000d685131040c41c06000501071b04216000441d9401d4441c281041d643d05059500392081e540ba8455170640070f0010004641044020456102c043c6054040b41e0b40700d5441a840350480c2d0028030081d80d070b450720318941491400c00152910241ca1010001c0d1a16a451560b02e00c40200700034003500124160b40b4401c1904a11001040f0280040d507040c1c9411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 567216330 1250 567215080 567215093
    0x106081905130b0a02130605030702030d0501060507050c010f140f19021c09050a06210501061239020f03120f060f180c0c1b010306241b020d 62
    0x46140c141c8081101102040400089208917844403006d480400600780c41c0001c265582d0b04014103510642c081008656407030200c91040e03a018040ea03464543e00c1e203104d03061842c5000380140600c0e042c410b00070b034200001303030700112200070040382e03110003036030f00c00d40100a00803600500c901032802c201c000380c8001082d90045078002d1340700c000c090f68080c035840b180d1003181c4003c100c1c41000e400080c41c00007840518450010310701c940c2c00390b050f810041080c88030354000b01e54099200c40300141c10115520b1183c0040d0040880b040e51440007a100140e6941600017450ba00c4035140100c03001d100b100b007242034000d12440406c81101c0050703d4450002106185d11000101e9400d8046245e10001420074908204090706c0b0003009040381041c006d040c007181d0403c3c40050103102d00c088041c440045800300402026020001c9074446401e1560403000150584210b170700583e8410b0380c00381504400400c3c0a02074103d076580c900e001a250318024450340c0d0074241c850f83c00703500822140719a0081c4100d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 567217580 1250 567216330 567216361
    0x1e0712050d080606031902030402040e0a1113060812090a0503030d0e0c1c020d0323041a07260d14060a1a1215041b080907030201080106081905 63
    0x16803141e22903690f0304010080f035448200c60340c408140300303e0410302d1404044c2d030242d9845840a80000796540d003409060345807140c511350403148080c02d120000c1c0f150803d05c1c600170f4001a009828484103040c64003854594000440080b00c101c03011a14581c4c60f0749610b590f400401016068954038810106482e0180180c0742410f41c903441440a46500d900b408040b03900e807540c000e070300c5901116aa034208482c840241505a04100c401d440000c250101181c0301071200e090006075a540e540341600c80d80c0c0306030801c2c0e8561f4140805014003c00300d00156400f0580c02c20801c0c0e43c8808021032500c0110501510000030940c51402c07550400031aa84d11b080c602603142101c3c9142c40035a500703c2c54052000d9401c404800000a21840da660212207040c0e03508202544100c0d40e902c074041300401d0840320702c00845100c28205600350380b43e098012005581080c0e0410142c1030440c2580c002a00c1e00f03406100e01410403002c0d5000419000340b011041d5500001c000b0f0601990a29819804a508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 567218830 1250 567217580 567217603
    0x9120e2b0c032a0b03040206040902031503010203090c0306060301061406031906090c1106240111010c0c0c080d1706010c0f0507080106141003200304051509010203091e071205 77
    0x8020860104c0c07000e40c0d00d81a00c0c0720f694000e14542c074190400c003a65000c1c1d00301030043d80ca60210907c00410640e003c0c005144120030a200a2030b12030312810400d49840405484107019901d0a402842422000d0f10101025082965003590f2520781c0340381d640a5161442810b40d9041c038045001c185c5090f20b4101c1c0701518096515010b6a92074002c44940b5400141e1700c142000e003003000200c00c9030440c6101840c0d0080e05042c2030310034018083c001c909444050f00c00b000080c1e030401e0300700c081001146410020300089001408000e01c490406007141051160f0100309001020004a85a04c03c0e10700c62140b40c0e200350300c03000601076413074000d45e5007010b0700400c4904d500344140412114858507003030b02c9004000300f2020800c647c1e0a800e90040554050054000488500103010002c0201c011801248200010241048100040003035a8400340c5042c0c0c1607401001802aa81c1c4009074490000f0083c082003811149610441803900200d87d020701c00c0350320161040c0c400e2290108055840c070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 567220080 1250 567218830 567218903
    0x1b03020a12030c0815040b0603100305010c0207152f010603030e0d15020a0c0218091912030b01050408010f02090406090b0603071b0609120e2b0c03 65
    0x10025010b6081d9000c4240d070708005040580012600c691541356201e00e0f21024100245124016000c0f40203a8000c4a0b916102c182690003001000000d202e0200b6031488d40c40a44825410080796100c0540c155070b15000f0000c81c031059045c0c44030010b848950590b040200010760007c201909406003c003840180d020662000110400703090401c031581340290301446d41c00d80b4252060340c144c0290803140418040191070f0f8840001600c0706400781460301a100031102142c13400c050460710f070120002c170040300e030101c1c00d08ac90005540c0c05140000400941008a2030a010320300489240c00b581d4007240c143d44c00c02030307078401030091a4000c0120031004c0d81c041c0480d54560741003000b5549041c64640d040001080045c1d80184161485461107000d060104140405511581d0075030301801010341c2c51100c0040301c83c0b4007039080000044a800107986c4182403c81d00e01400c03802000f110610040d424414240d00104400d202422014540c403507900c09166401074108000c000201107006c015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 567221330 1250 567220080 567220103
    0x1060c0303140c07140f0601080708010e010b090126031602040b030c030703030f050d020a080603160312050d020c010e0703260d020906091807122a1b03020a 69
    0xc001c0b1a8001d00c29141041c1c000e103401010b64400e070501218024640950240710f40f51001034030140a0b0500034801d41005003401030524441c2400c48216042c00c5000d0f078900740c07182c02d840c0c8441c9042c40c110b84d0060051160500000407402d40b60101100b6907a1500000038648015006104c8001d1018000c0d00c00b044200e103098141992901c00c060b00b154941d11010f020000203214407140042c0040d18501070342022801c180300400da0704050f0010340480e01110402c101820b04110031034100342c11402c207214852554803240851031102e41c030842007280000b0740d5442c086640e0121044034030b08500070031402c004c0c80411601d032106800100c401d135508104a62841144900300e42402480744a010303d017560302081038000758881018250004814080301d00c0980c0c0305507840d03d8020090380405914501454010308603903e00301010403951818aa1126244102071410a01c60841e920b41c08810510031003901c6620401842844604500200408240c0e01003841103910344150045000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 567222580 1250 567221330 567221351
    0x1030b03011d16032111030a02061806040c05040c090f0b0306011106190b0114070b010e1f140607081903180515070908030d0204050a060c0f11061201060c0303 70
    0x41c40030610010b440a04031701010000d420304012004079800c01800c0948031020364135003044c11500203840392005600920100222080f240c1e90500344040840040c010528066450042030004c0d401201c1c0201d5960341d5611544c0e01980401000d442d00685c14544140e482082c1c5189a004682841c001351031001084e000140c0003501c0c6008080d180c3c5184038582606007420000c1c0480c0384980d0401c211115060404081c460041121500901d0700f0501581806207151100d80c001e40101c5c40c44000c40e103112010003040342003200385e070500480d80f0030b040c914000040305801201c00142c07008800003143e031f84081440d4146284128a034805020300440b02c1d415122004845601800d290459525030740c40c5604c1c80700e510391060203410402820390322500c1061a5802004030141407550008083c0f040c0e103130001c0c0b070100420062820448800c010b64501c03007400c6070404018008440180018225640c040903100000f081d003108540540c1e55500c000d0038032403650025000b00f40b5201c203015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 567223830 1250 567222580 567222613
    0x120a0c05060322050a060e010209010e060405060706200a0206070f0302070804060305060d063e1c0f14060f1509100318051608010b0a0b0901030b03011d 67
    0x244580705056210f0340c006840e525010030f808901c08101c403280110054000069580d00c14901426155000143c80d41e90590015001149000c0000c0c07050ba010700041140d665950200c40440c1d40c400e8012654041040b9250301703001c0921044072240502240441101d075000408511415150350782010030043c146042d822803044000160081e101000148405800b9410144c5c200c0c4000d4800071308810f05407200c100321040c50726840140b162842140c441ca0b2a01040c00c1016405005080b50300c5101481040703542c03066403000c0c0442e10303924030b001020300ca156010200e4690003801c24441c034503807414030555031202281c1c81480b8030800300300350200d0f042200700c2c69541107206070110324050464040200d04c443e400303070704c07010180c0b10f08985442090142041080c14894002030880c1e04100342d0310682840140c002d100755038501300c1d0424050750340f000311004640076488203656505001c40124050300c8120903882e00b541c28107034042e460005035241e47c60305901074001c3c3c5090000c41000c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 567225080 1250 567223830 567223837
    0xe18071403060609012a050c010e01170a110f0c07090f02070b0a02030606040504140105010f021b01140c0d11070807030309030b09150403020f16030b0406050411120a0c0506 76
    0x71500030340140902400355000c0e40040c51b00759602c8404c040c07100c82e041214441e1030001c03841144c181c0c00c04107282030203581241e01040303040c0c000d08207070300d1902e0801540904d4010003440c410f41d01e5203655603124640342c0031048400c01034901401565503030981280f40d50b640302511480301010300d0480c1c1e0101c80d142a200f503440081e40020030f540c1c951184e07030a0320082e400143c00d0390343c403170410400061141d03217501c40c522907407458940001e903035850300c0005801540c40941440c10341d0400c9201010340c030b0b440d22806000240900f0320b100c0c000104860340a45009050f1211658852a99240e01d03080e000080d0072100c81c47c80040700c10a036158458503440d28103500c4010041200d00350148001210520401d81c040103032402c844a40254184000ca0028140d41c02d80240c0c114107000c4051043c02c3c000344155070450351028605600c0c40d0303505603a5210003840a0980c940d03d0012038104482c651280c180c0300001041c014105846000c1c1d6510f1750125071080b149401d164000203080e00703045059 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 567226330 1250 567225080 567225091
    0x80f0303100b0f031906050a03060e0c06030910090618060905070b0406050904050a0f09230601140402030709032a090b0a0312020705040f050115080f160e18071403 72
    0x340350954a44104800c01766a1001000d100651115408542901d4150b5100b004501895020610b221140000c904004051034001c0c003e460401c1000a6903100003a000032601000c1e000041e03200076824200001e02444e0035030304010001482c42c0c400d04c543c44c3c00442115000d5401e80e000a559101001040d10503841518003245062000381058a0130707510a5500038007511010072403c0c082d41010f4112717410b01c2000c0386d00051031983c0c0d00e01d20312040700c103407400c100150003012a0350401049003000c00d2142d8011344100e40010004e0003031441682100d0042d83c2c1b0a91181099100800c50b030014115000c03010f4188039003200c0042c181050b4000d00040c1103015100000003404c603250a440c2040e1100e040e8194801e642000030b1548880c851000071011900f0700241035410900718002503d0520707103100401003900280032142d004030003400e07003090301210641c400d28441c003025500000245410b991040454881d250520702190580d41302c1c09295a41c03c03541d480280c403c02c8140000d80c0d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 567227580 1250 567226330 567226357
    0x10f0509090a02210c03120316090b071e0b0702100b01020109020f060c070f080307062f0d110c03071202060103050c0405100801020c07080c0f010507021009080f0303100b 75
    0x1d406607103510009003030348081c0c444c0c0c0c2a80c40c42d20110f070110740741070420075440005500c000100701d1074180c96030000018000070303e404200c5600c0c014000030746016004c0040e1800140000710400c9003444285c00303000c03d510001c003141520300a9406502c90b0194101c096890b030425008003525032040c450310205035401411214240d040c00184045030b005821b80c52002d2048003000b003084603c5008000060501030000c0d5900c81030f07407415105554110445c22501e0900540034154541c034040000302c114801d00c43c6d41d0301e9251000d4140050001c0400101c441403001615220b0000080010148a07008414400c014803120000300d03500c080910016000782c00c0a0f5031810503107000e0b00a186c1005100c2000800c19031241880c0b801c99008240801c0c0c19400202d04101541050007200240e000889115140c1c2000f440003070b045119000c0000d12850300100d1820010b4021001000600042c00448206c400d4100f070040d52a441511040c1c3d18403070650001030130316000021030304110800f0302c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 567228830 1250 567227580 567227599
    0x120e0a05071a041a121302010f0504080c010f0216030c092a03020a0509270108010b0604050f0303040801090b01031704180203100b031608090f0c01080c0909010f0509090a02 76
    0x103490100310040c4c0c407450300b01e0b80010040301c900c4050541c1680d001d280c41780400c184c0b14405100140c07512507405100c50030301c4000d010410415902241c0320300d548c01c1c203091081d81d90401b070031b040b8108440213028400c041c104020210521003640c0300381080da03d2603001041020341004a04c0e590142c3c1c96042100c04001b00100010584280c01902c0810f002c0d0a1a40c2010301040005426051031891050031072403604020f041c15079a03510f40750050160304001c100c840c143c0301c0480c0d450700c22805914064030700c4480d551b2079914204101d40c020000c980080100c10494a03050111210038403098540d01001c1c150603a03030022150440f803c0f121418034141e56424100100406900020044410f22200c004002444032001000f1441824400310007503441c800e03202c0181038810301170b1001d0020750100410000031400042c011640704000d00300940c1c56501c00f4072078201403040100e4141c11207254400040d03d10110103e00040c0c03801114040c00035600c500e00155101180000a50300034803d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 567230080 1250 567228830 567228839
    0xc060408070303050715051e0a06032013050c0a021606080402090a0221160206063d1205060906151c02070b0a05010803120106030c120e0a05071a04 65
    0x980c02094024802d1409500030f100006c030402c1120303421101d40305010080003012001d03500f5480300c02d900c05212542085402d05544035240440c00715002181d005d020750084002650704c0461500c400048110144014605400120101d400c035040300c0016205040031000781c03140089280c0c0994a45988540481e90b960b0200115150701904041ca001d501708502106082c0d66420801d0354245c51030a8619800c1104030390b1400d030b00700701c8040115046041800b0166540741100c1d440a40c03204e0492f801100303860900404418010240c1c0190280301d15044021500480821800242d8010800c003540d901030030702555510445410341d010400c0a0000c05103c10080030303200c0020031802546e80380c859606180100e9216602c02d841b00000e01c0f080151040044c0101405400c030b6a01860a0031003808011b4112801802568241a19184450000c522802600e083c0c0c003c2c043e424400d45001a03444da4a80c541a442514140a0a0701c041402141000178140c6600b06165051509141 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 567231330 1250 567230080 567230087
    0x10611100b04020712090f08010c08040b151e090711031605070503160e250302030a1b1106060102030a0504170118051b1503150a23030c060408070303 66
    0x224072400c2d031060342400b160b8085070301446820703074088440e200c0540003401e002ca003d05c804220740c4411000d0381008001d00d001603000c80c00d1a001580502110000d4960141043c076042103089455041400600200f0540071244400240340c80d094600700c2c1d50b0f03103400108441c800d035404852603169204124810b091001c401034036800600032016184242c0d2a2000281070180711104c29510000c0880248112400040a00d400023030714441c6407540741c0080c4402242c80100c80c0e013001070540c0840010303c0c81c0881c0c2c0000040001d07010004880b1031400001070091a08030303050b00000d204140c0003404030350002048410010141c0c844506140c501001d0b0306602980900d40d0225540328030309402d05d483c0100807401043e00c184003500001030329501e407a10802511203000e04c90062140da0700010a550350071244c2240d4a00640300c02e0085c2a40407600d00d58242c0c2c483d030b1240300c85114002c0010b440000c00c400c2c4a0041701900c9a80d003680701001310300c0c0250301074080340d500305601c2000000d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 567232580 1250 567231330 567231341
    0x5060118090c14010306080304120507080d170a02040317180103050402090a020d1e0b01020d09050a2c07020f0c0d08030f060d0c090621110111031204051501061110 72
    0xf0149008200e00351240c020b903055811a0340032008a8500450300e6040000c14440c12002d410310000400c45900c8040c402040b1145000c0d1700042c181d21030b4085641d480d51a01100c010f1034010001001d10100400b045116a02c80e40c0c0d1800c04100c5045a03029540c403d0003000e000790380081004c400d0f0f48490707041000950000d0359003549503550f8100d801c50b101450f8600181406031000006803040404000380c1800c1c05210040c00300f1000306401c2c01182c0e68841424141c1e400000904080380032050705000309105040312092040e0420104000c07181e001460340d031020042d0341652044c0c1c081d2004d1103403043c80260018800700091000605000c080c1408a50143c001051005010619100c01c85c40c00119080f405d80710341c440009000e01d10f8105000c0c4a41c0344c000030810866941d41d110002c941340c0c8034404904000c0c0701e466000c4140d01c1041960300e20046d0042583d140d04080c50201c0d941c503c00528601c1d480c501c0343c00012081d000e00300026040254001400e400f03000c5031520b100504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 567233830 1250 567232580 567232619
    0xf0308070302040807031415010b070609030e0607151506080f04060902100c120f120506010e041e0b0f03061f0e040317240d0204060503060405060118090c 68
    0x141d0074000002d04450401c0b41d00000e50081040c4501e801c2a11709440c181042003071a2641c0316802301c010844940f00d04201e401d6243c102d440058881000d2034101d640020100f15254404004500c034003d000508420100007c1d01401c1080300342c0d644103540c1c011507158441c80d0b02241c031203800075103442c0401d03480c981c2c07007445800c1c00110340d006940010000703e0240e80480000307100034004001c00c041600f8481d129981d03802e0400e030003546840000d0606088802e51200c0580f80da000c2059a4010540c03159035240040081c4061b00741500a0a40c141c043c6100003140382c1089075810b10381c10090b1092200640107005801240c3d6200d9960440d50200314000344030ba1404c1400140e100c0b0300351a8a40a0780c480c1e03179640900448010049001c040c040c02c01c010703107044c0c100c085124240c11006d2090458058808441d01c6000d40005001807089910071b0b034240c0501c504005c104003022034404d040e2001250694841d03607c070b540ca00101c40316903d004080703013004a010700850303043e10219044d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 567235080 1250 567233830 567233837
    0x112a07050d02012a0506040c050916050c010e0601090e06060f010e100903050a0303090614090721020307030b070f0503130206070204021b0106060f11060114011202160213090f030807 80
    0x8070b66080d5151340c1c0c4662031000b40d07541c1c0c2000051004208114403002d000300b000301c851241a08159846003a185040e030f030460705100c2c001661000314002900018041626501076440310342c2c1d16840f40c0301901400e030300030111740922000103100c2e01c3c1140d20401c0352541079607502401e422140900440200005aa505102d4540310020008404108000b883c40c800c1d900070070036160600d840e90a0fa01c0390b0310500211b8050300c080101082d00061240b0450f5843c002c41c60380082200f014072a40c208050000c1c0d010700500340c3c044280a5542520b500a070280e40ea052454104220101e60501041c0e03586040c0721002d509200241c41c1c444050406103000400051610110814020100042c82141d0360707240d441e141d0030071246400802ca02c11814541c1402c94200041004036a00c5503414003038503a002d080200605101d034407854000c018031842c02d00c11580ca2080c21613101c00591241c20891290b0924851000181d80d40d02540c008268042440414000c0d20b6a0a845500b4024001340c1007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 567236330 1250 567235080 567235127
    0x70c0c081207020f0405040209150a030203061003110303040f06080606090d060b01020105010803070803180307120504090b0604080a03031d1509010506030313031203112a07050d0201 80
    0x54a4284400c035801000d00c1002941e82c841407050056200100d4100d0303100d1480e00003004056111a600a540580c520080341c03003e0501d500058140303240c1d50000381d010311907a02049010124800180f041d40c0c003c803150300401c280902090341c5c030b1103a4060207135401544002003200c14000d80000c0d4101030000c041d10f00307080c1188041468030140d0401a128507446079054481940c082c81005d000d4051400907504d0000c032511804007a100140c2030000700c0c5001d00c440009860b082c010b8070001503002c0c00c032506144151030010b00c90780141c0544201240750484c0c4110500d0408110b03400c84001002901d0f1180c56904d013034008001002f1010020028040d429581034002d201e600718581d1481250422400c1a00394642100c0c0010700d154001d40c403c002c12040041c500e0107410840341d000c503031039407403e00d03400f000c6001e080421074a101e200070209a5440b030032620b0a0150300c505460010451911090511581d10803032131045c540c002c0c4400000f480503521841d240c40d01e00302500a580300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 567237580 1250 567236330 567236339
    0x10f0908072d141908130f050f0603040204020705012405060313060c0e040606020d1b02300a06050f0708070e040c03021207030204051201020304030f051b010908090301150b03070c0c 80
    0x8068070400d40403600044001ba03e415148154610301c406454a80085401d25050402050116411000782c520070180400001c013150f94640403608000d5020b0700900000b0250f00010641d84400301c160082c1c0d6401c02004101c40c28441c1c2903070b1090302810602c2c45010311a0300d03458000c00305031410204000c803c0c00115500d031220b005440c0144141e500400ba47d030852080144035010061500074108020207180025030f4400f4003425452007040e03024003469040309050500442a084c0d2420725003e42066201808440d42c07007030b44280216003100a90b9030b54a28201c50010b000c6602c000402c065507450140c0d814640c1c0807408500c8542401454030003400059001c10b20200c8501c40002d80010302400365060841150380c8065000000b9401c5042607038000c1c1480a003084c40404001d80406d100303502040301d400403451075400f60001c000d010201e0a240131194418041e041c0690709009091020000b150300c500b0031102d20f6414541183c681050841c0c0700c00c4404400c1e960540748200205 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 567238830 1250 567237580 567237613
    0x90f0605162a020d1b0801110414012708060a0c0806130b0105070501050108010c0306211205071506140105130e040201020f1504020f0901030209040f05010f0908072d14 74
    0x8035442e0000c0d1028100340303815446c9080d200140308011260703e05101c100a4115031164000c40c6481c04d09010507010f901c4030b841c2e40c402ea050718410040050301c001c0080c05801c08900180241070f117450500820706042c0302501c118006403090ba40000c40880c0c2d0102424441d4004050150140750188c5032403039a0303c0e21800d6407400c0c0c025401c165991606ea44550380c251103142c005044040c00c040d69401420851522110407500140c16411030314a240080ba102c0c500f100e942e144e01000701d141e02c0001031105c0313001b003100340139114082c1c1841c0d0301400700d58040c2040d10001018403041c0400182401c4420780001000b8004a05500c80c9590624559500344020144d05903210104000381c80d250042209501d0191407550080e403a55006001684446018a40c425008000644a0f2445140103401400031207000c0da449841d00101e6020030a0319001484000d0141c0b4040c0503881c2074100d194010440301041d05821940d1001c02c0780011541031482c101071070040d00740e0300000d8800c01d404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 567240080 1250 567238830 567238853
    0x50709080f061e060d0803060f06070f064502100f12060b0a08150603161106150904030e03011814010b03030307030b04090f0605162a020d 61
    0x1107689401040030081c044038000c0555540e41c50340c1031400c5460500e50041045030a00a10160020741d0000000701c068550044290100320007902d415914101410f00b0f01425038004412105035080c42d010f010107008050018002554071144042494071000c03406680c81c20a0900c0d03100360204d5810000565580f00010045840546648100340602c0304020004800000d070301c0c0c1c020b46811828440c03031549100340c0714581000c0c03c10481940351685041d00303c0081c1406241e02c05800010060400c41400b100306406683d41c4581240061414020762503103402c680301480f4034020352100105280000c0595041802410100d5107101d0600119080d5440e1040d0500c240c0c29105070401000041c1801c012480f02d480c001704030081d50100000e4680c8009040582019190b0402c205240c0da00d03402040074540c010515858543c00340341101c00307003100711241042481c0e20314507522564040d0240f611411088034000d00200056084241900d1a80034181c3e00440302130007080000c0c041c3c1100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 567241330 1250 567240080 567240103
    0x507240204030c09020708030f07050c0d0e19050f06070c090204032409020906130204090203010915080303040503090913084b0703170106180902030105060d05070908 73
    0x507a48909504100440d5649580050440e0384100818408140f4010549030008002d40001c440360300e03000c0f8115168000c3c104021201d0113030348006041e103a00310103040b002c3d40059801e0030201000418402d24000f0398480c00f80c220241768074001712850719000500c20244144c1c1c41d050010307200c4c3c035007808903003050300300700e480d0204010094188004140c040d040650000300a01004115078041000203201500c140d021340b201100115803000e0a4064070b003d006074400c115100c1da514001080540312610a40c00080c066800c00704003031402008480c8030f590072000861030400000c00b40606400300400149068500d0588000050042d10040400780329401c40326100c202c042151f503071190112242e41c4016141942504441421781150b0070350303461000c1d20117450b140b0a05040d1000280101d01d820314038038601c000704406410404541c200c0c7c06002003001d03003688510000080384803e00585a0124052088004002d0150862640604240742580d00c0540c0c03248818074040a4114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 567242580 1250 567241330 567241403
    0x90315180f060f110d0c05160f11010503040c060c0204060f060e01110c0a03030e18070206011a0319090c15050d0b0a030807232e06080d0507 62
    0x307000090241a0290b60644260f01c1c4082040c030451600b048910310400b049948a51344554174500e145001c1e070259501034602000c21303020540c0520f4590101e408403030003114400c1c119076452420754428820340340f08940c4803002c03841c042e05000c010b46440004103c120b0384035882e85c002040b80c0440690410090941c2d13281c800c0c28502c810005495001401400ba40660012800a040350340d000107083c1126014200000c0300840580403480348100740c07060000c030320040c8080c401a240d0000300c0c5812036103050152404240f00307910901d0342e48030603a8140c000d081e00b101c50020380c01e403070780c07003042103900c5500b10f02040c0b650f901340901c25640f079103120004a600130404404044a40c080c0e03007a50308080b00c00c081c03000e00315694503c0794040d058000e016407940488110003107030102c0040c0c50900b0f01c48202d42e000d140085006422800c540c840565040520b042c000c6617032254010903056174410005081e8560600a0807105500881c1c019030b411810102d42c420000b04c0c0d00750360020a0810031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 567243830 1250 567242580 567242603
    0x1260615220801202704020c0a02010f03090b0402011b0c0b0306100504051509030f010e03270102060a0e010b0d06020705010c18030206090a0e10080d0e0109031518 72
    0x154001d08440c0a04a070130001180c01080000310401d83d000c4131000c184013820603d00701c070344424065044001550381034200b480080c0b07210910000043c86000c0c80d100740c3c0c2d4280118041c00084003580d15942c0b004092640840c0420010340c069400d618100ca01c021000840b812a0344400080700500c0e4031210301c2850000c2406424100b81b9881080d000060074018941454280441d070384802150b12481050b4005c81c0b0708100d65001d0000031040e2030340c10f000703208010541c3c0e03286440760b00100c503403084500c5040076180d03481d15080003881c2c01203058000d44002c2e07075030b944a10b0160089003103000040d5a1900b1000542d599605c034080520b010342c00060b07e44403103103009421101c4404560050000010680f0b8410f084150420140c03036042d02c08549443c01c610100d21380f000781e50041036013407880300c040007800c40c3c001c961942145c2161080307925203a4151004d403103204100003880e000502040e82480411781c42c0007070201d040442640000c110144142000c5012450182112a001000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 567245080 1250 567243830 567243839
    0x12080415120903030c12090b2d01060509090a09050d0e190803031e0105130209010c081809070f0f110a02090711070906050d03081b180126061522 64
    0x40240e4500040f42401007124403688d8481c60a000c0004140500070f804c00f540c48004040e00d95400790204110311065900c958580d0409440c075086030482a002d92070480010f0342c1210140904030042c2d400c407001c0c15990355078840494954181c0640d640d08940104101c00e00240e40c091024010308001002e152a03003480c894182404609514105c1180b9404005000030303a1010745070300740c000d118a40180d0b6070102d84016111a0704050000d0080c000c0450074213822100c03e24032242c511003c64448007181d031500c0059401072444203840001034103083c0729400711802580d101c0050003c01040350f41048091b03000880e110400c440d000c0c001a0504182160140d007080305402804101e48140300250415011801c0d4074440000541040800401b056030510180a14140c4000942205a58001401403420b01c041d120f02038034001100200c06020340e52503c0c4121052044406c02c0900d02e0b2912410411120b058880c50021a5010801340c100104450294048009a680c5008910340382 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 567246330 1250 567245080 567245087
    0x109050403200304061d011434111f0c0501061503090b0a090206160614010618060504030f0209040212010f050114030c090c0307110a1b12080415120903030c 69
    0xc0081e01200b000c0e1031050b800385071780141c104c411804001c0e032410748a52410025032030402450171640e0300c01d520b045480c05907014004000274440e004002d0680050b8040045c4081e40c0d2480b91140740031080010003445040c810700d44501c03d44d002d8000403880350b444012904003c07082410000119a48440c0c1d4000c00c40110b05da1580103600401c1040181a2034000c03800358072a0040103a09266100388020420540d503100c080c20a1010b2407800c0030b580c40300d03409003000b801003c003450340712503051001400d20710400866007a0ba0b802000801c0c034403219401d0221851014100304d91084881c0c0106032041c1c000d114506102c0000c541c081620b514041010fa01d6100f64100103010b83c02414501d5840c2e01d0346250348d900141c4a5104607030b00da1b1201c43c21502e02d41c0740004800c90f8085c03801c071760040c400c07802004041d00c03007070412011000c6d0b80c84405602180840e2402841000248410401c2e03086410300c2c14035035034542c18035400303800400b04020104c42c14107500300c001c03981d98541048940d91 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 567247580 1250 567246330 567246347
    0x9060e0d14012c030708030705040e04112404050402070f0812040b060a030f0b06010905060408012a0c08090d061113050402031005041d061e06010203040e010905040320030406 77
    0x180101502d03003043c0c10803c0c05849100c1c05d003002d80581800408510700034420811140100304114159900303007418544074490380c0c0d551011900c9041e40b9410004a410380c0c4041d03184000130317400320034a4546401e00340310280d000a082030b10ba031712010b546440070650b82c0b001001481d02070000600d0520b4a842c000c3d0007280060a044d0040d21220300500c0064000f40d0001e007040d0300300f5080c940a135107102c0100c681000e81c3d08066002000850005070a0382c054000c00d40a0003600103c0c42030070b030b00010222040310794089000c00901085040c002248030b00000b00080000a00398071142060b541701c200544108200245d4074900009100c4244144070890001403e030489040d40f960402c002c038099a8110390051620540c2d45200c0130040c070036080901d0041b104810242c441d2031401c80e1810991078241d1040321b2503a401d2a000035401d600c040101d400303551100410111507401e041200b0010310f0000c000b00d0a001c41d01066100c00c86044121101c00f480102c0190343d45c42c00d21034020003024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 567248830 1250 567247580 567247631
    0x8030a021006091103041e02130b090a050f0403050708160c0e090a0b190609050f061c0c0306180c0b0309070909050a0201051c05040302280309060e0d1401 68
    0x1860960103010040c0340408903a041500420502c0c007080007c44206039040203000c0080d4000181361400b100308140781c001552401084607019015558034a419041e6441115000009044c0c100003500290090003e01582402490140d0414411303925130303060315600d42800c2d12204d4000d281040090640b11800f9444100c420241c030450113269034086583c5c4015003c4000c2120300000316400284541c44600100902d120a01c000e0030210442c419005082d18181d0051304c1c14a08038005032801402011380f594840044447c891075900c6000060a0708188180410380004a800200e0000c00155000c1d10380088005d41e030b4142200d20030b15128031030348030340d0020341410000c06c0400c0703012420a05d06a02070910942d2805030394440302034000700301401c10105103404148000d155001401c000c00300b03540c181c03400107221300d0340710718550199001005001412420003841013a00c60b05460403401c4000c1c0404039000798656456641c0030740100040b820307030742d104194084034081e8401d131303c2e104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 567250080 1250 567248830 567248849
    0x409050717070203030118151809050610090c1704030c020411031602071401120e03040b121b0c1b030c03070920160f020f060a0503090105060406060905150408030a021006 75
    0x5072300200c541c6042d0782035110780c0d106040104601060030b40304c0d402030111143e1000a4610a02c0c1030301c17840040c85141d02032048050314007401e00d2030007230085000f20b10103041a100340d20650340c1c541d000c40e44001c000c50100d0b00241c80d12054450070b00030101542c000c07440c80c80ba02c0d0001082c55002407518070349a21440900780d0b10303c03040f11266000040c034001101c1c20080841c1c2003000680007807452040d44e011910900b0000b92508900c640d0041c01c074040c641a034131104184030611008515809441201d0f460f0f5000040c4c0c8000e040300e400c440141200c0c014040d1003211846100080c03e1075603562000e100f058403500141c020301d5500d5240e06080c4417150103641400c440782d620102101d00110024540c0b8808104c070350035943c0c3d20f42464070300741d00100851b03640d03010210b00401c950002d03181c088081d0300742070210b2035618041c000c00c801d81c1e840703540d090000b6141800f00000f04142c005500d1310b05108000c0429183d9060000b01030071021a001446540078140c900000c4a0b441c1c0d1043c8610b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 567251330 1250 567250080 567250091
    0xa050a032004060c1109071107050d0308060d0309052d2718390303090f040f02030a06030308070201110d020901030b040e07060306050607080409050717070203030118 73
    0x407039680042e2420b80c0d280d442c041c400031165191000d20068464403559100350300c13000f0002d12541c018611b8031407249020030740b10902c0d2365405111445980020080102e140800010b8041c1040511610414020300e0070030189a07079035011550040b60b1410628440380c001c0a1008050f0415110000c5407500307440003210311414880000d13030002042d042010f000005801310b42d0110a074444140c0c0f60050700c0959206045044030b060303a140076003020800321450340310300c031409820901503a0101903002d8051460004000304221070071105096095015555000c401005010307480034521440e4841000280d240c15401d002c0c080450003010030b000c582c1840070b1a8102c803000c1c0150f40c0010148100940c4404c650001a005081c0503071506400906d000d1444d80032803030000b8450215511a05c04100b4982c44000340541403040840180400508200400000301c00717511607540440c5914001044600b203c10f41c508000c0b080c2e600c000140d102100601600c2c8503201452070300d03000700310708019 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 567252580 1250 567251330 567251381
    0x70e13020103021c111308030f030c09031608060403092301050306030a0f060e060f10090b150d0510060212041a0c0703080a0e0103061409041b08011a0420070809060a050a03 76
    0x649c0c2c80010070102a0003400320350000c070f0b91001c00400c51580c0072450f1701c03800d0903103c800d0141d958401321030a800081c4e10600004001000081080c0c0c0301c0c1d40d2042c0c1907034031001c5c800191240c0c1c0c0040e008940501c0740c90300c8600072620155510224074418403021800805500d000c40c60701401404820340d2801000c14030150b161640480300031101c03004800b040003041c1d04001078082c200c1c0c100c409044d00c1c1c0020780a1900555600c06031040382c6140c10240d441d915604100d031385010000071100402800c000030300940b9140500b111170541480d1041e0b2034541c284c42e00701e080400c40c1d0b004850101000c522000d00603001182c102c0c0034503080c40e0810031b044c03034258000110072481c198640035500440104041c0b261581090304180403182020a1180d5036050f518001d140740421000c0150381c0028540c06031404e8000e034030310b20343e0003480500390b011414010b603140e50100c01c00319000541003054020360380301c0501a201101c119100d29480f04551a005400c1d10690302e484100000c240031403a5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 567253830 1250 567252580 567252607
    0x1e03090c141c17210702030f07152004060237032d02061b030f07050705060103080d0513030f03020706020909010e01030203070e13020103021c11130803 67
    0x5501c10360103401d110501c100d003080c1c00c003540c43c00140d810480300080d00d58071104124107105014440810341c48a40d030f0719450200d849005102c20074202e010200310290100b03654a00218400303c40306000216201e00e2421101001811184400c0101010604202552701848003030304c0e1100d01d180c1079842009561072522800b00001185a048c0c0054020106044c420141c00c0c0124210356049000c10402d903c00400090f8403c15400051140e0710004050710400d4400c42c07039603025680703010f0440d00c520074856a00c0138000e04000070442d0902608020880400150303000f9409500c1d11991207028113400d40694400a00910b8018010300c43c0710300081e4003100f21180302d90340d4500162551040c0c50608003a114940c41d0701e40c0050110000700b1003184088140d8100c82c1b00310111380d4460380e5030504210003501200d10500354915402d508004d0750098004105416554420102c4d400304607614400700c800c50154401007034004145c01801d0600f801305036002c0d050040040d814400321a80300c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 567255080 1250 567253830 567253849
    0xe0906070f0f03090827030f0a0c05010c03230d0b040c0915201014010f0e2d0406201c0b0612061003060501050306040c1e03090c14 58
    0x1441015601c3c4e400c2ea003400074100641d003242030314894100318148030180da0226814050312851290080700300c0808040c0c0000b581480e0554054000c2c010b052805005480512007220150705004540585c030102d4446621010800710480410f20744904d040e01060044540001310a405645442103d44078245c0049010080f130b00c642d040f0351042d0b02c800343d007150052000c640c4103151240040912550200128034081691203056080200c0c00c0001a10610001c0c02c1c4107a60360b5640960080c00001c1844494541c00484604004401507020340713015520701c0544044d4541c40143c009101c02c0010718000c948605600301d810b4118145841b0712044d251280380d8080003090b1508845041c89c5c815500140501c0d803000700500d86905a1120407030002400b01c1d22140b00b40400d01c12072044600078419182550010395400d81940e841c03a09010041030708070810f905102c01a0258080140c412804520282080d0780101d46090185440c4000d9015038100c0380a1004211403c2d02a13101c8136a107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 567256330 1250 567255080 567255107
    0x2010c0903033f05060f060405060a050903161e08160b0711030f330f04150c050909010906080307021c08030106030905150c0f071b0e0906070f 63
    0x86411600d000882d07840703c0d100700c3c0101000605400006440000c19882107100d0741040e114007a041c03491504120f5584550b000d030944c040300c24410b09007003910450103062104005801c4a034a200008a45000011690311180480c020900714013050840440691300802200c0e0041c0300803031641300581020001400740510721180800e103039007030004000c5180306c0044050140c40065580414079500e501e0040090589410709444130410554151203420042c0c00603d40e5035020f80700e5483c20f24800101500079030b000c3e070749007000380c0c041507044c41080240741207a1217460781c80710850b06001e40124164049020740b071030200d040003410404400c40d50071035411624480b0b6180021070850600007030080140000701d012001241e0503406501c1104114003a5003114044048010100356140c000c44140e03000d110284402e6208038a520041c10996104210940a10364940c0421214507100d40c00100301c92140700c00c0c0541c07100d00f4407025410041c01e28280c5094100b08101400c000d11000c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 567257580 1250 567256330 567256367
    0xf0323010b1c0503040308040603050709170d030f021903020a1419050c0307061514040b01090303050d0b1323070c081c02030a060812090d0b0612060901090302010c090303 75
    0x2d1082000010b000301c4000d140c0c4140740c2500e0701e4450034010b00505040b0b0390500800e032501808118104001480b01c4c4060307606000302400ea0305120b0481c0680416401c1182850702071000310740d9241100c6d842d2045001a03070700140c0303450340c6100082c074400081c8000c0d1000b10003040408003181d600380e040b0f107076030405090086c0c5e2a5400396041d8038500c507a05014140328503008801d8100404500c1003411034012911841c4504181802c2004803246200c645001c540b070000c003000041d004002a20395040650360000b0152400c0d00411180c400d0516865001e43e03503007509000e90300560403120741c013040c0541c0d20b0a9514007034202405400352250050a5041d000c13441d06000c0c8017101c050020740395109029500c908040240001420460044880900908074000001d00d9840141c1c1d5800100407e2078107014200d0300c440c100780c440540072a400645030314022509140401025004070342940002625007442d003002421030b0440c0d00c0300d500700711900d5401c0003c250f001d4440416041800c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 567258830 1250 567257580 567257629
    0xe06060d050f07090603053f040f0f1d011220040e0d080c090a120213061806090507080610020a02090c1c020c030a05070c0f0323010b 59
    0x10704500d0444040741514140c414240302284510f003d0304004102d912550854511820450251010301020161038444d0700441943c0411410f840c4440c8094035450a4541e02c0c1c113403108900c0f40e0b81402c0390032248080140c414100011401c0e5132910013401c80ea10200c80311075042c400d15120400101201a104000482e070100718004900c03965060320030b00800030420308400e042c0c41600c480d01000300c80c0108101d03600180300c0200000c00c483d41711000410219080f41030100d9291503c1e58400140e030080c08010742104c4011442c810b98001d0103054850740d281c20b2150340c0c07410030b80d04235800c030804460800b014884003c1e0815450f0b41c000300100c840382d6442c0300d007800481c81c00c4d990400182d03101408005100038005c420700184070348074222410032031040d80091403d00742d01c102c800940259208111404200d4880c0c0c024002d13072032140c02d030440c0b02c80c0d075580384401c0039003246c00c1601d254101c142d0310400d00d80f4180400942d080340030002e000640090001805c00c100034503d1204098044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 567260080 1250 567258830 567258833
    0x2010e100504050d030306080f07030215070f050706270b03010501080c070c241404030201030507050c060109020a0e0118050909070302060d0c0323040816080d05060906040e06060d 79
    0x114259005040081e00313410141c1528140100a003405108002c2203001d11801c0c00c1c1c4131200030890b0800e680e006400302c40604400c90707010146510070403094410300070320020140000c10a0120100038401caa80700551886171002c0c40310454198003541550900c8518100061074007074059078112403090808400300d0b955038041590718402d11400510b40c2545140102d000c018044151013254100c2c41100907200901905a0700c1604089010400b542c0c140010001980b0036086280d0008c42840c116003410030300c85046191074000e8114000803500401c0c891000e40e8480d09150314800300740b0748030015030000c000f01d14011032a402098012004040001c104e030208024620046278098030440d1f503441407090700c40041140c100c242000174201600c0c6901c2c01c180230107820108015414014060f11950344210300c03540220700d6007141301c80036400e5001146081000d03111901843c00d002c105072030000300f00440b07281d0051415104516012071808403150001311164090016181e844200302d05 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 567261330 1250 567260080 567260087
    0x160501020a260d05041b0b0c061501020c0a080a1704050607020f121f18021003150f06030c020106060216120204090c1d010b19030b0d022106010f0302010e10 69
    0x801c2407051000381130000388820040450b4005668800224589007565100c8400140e20710801c041001142d0201021072070005680c4c1c2c4a80b40c041781401122032180041000c01d00203030a560014055401c64103c0c0303002c0c071440107107074540d07040c070307442007501e06400e2000291050044100290241700d22800107552a11004034000c00d429110781118001c1c0b0782c0340f44410345210103c640000391401c10003541c0c1002d402c282002d141030b900801d0b030300c1c409480200840c0100001c10f0501a080f142400c00a511204000301002a00550f41e01190300e1402500190a4906680c403040455225903201c03428000ea9410090130385043e00d41900c0e441c01b01d07000081c0540316001000d440700883e1140042d09585800c400d0701a82048a030304070700c903a6500030940c11802070b5040c0c408c00c4003a680c50031305440d00c81d500410090f0801000c19108400540218202000007800844105056030341b47d42071080812002d80105030100c441c141d210305640c0000d00003d00078030720600400d1a2031460445034003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 567262580 1250 567261330 567261337
    0x30e03010e0102130810050c04170c1c0b0f060a060c060b0a09020913020906390c0a05091e060a030f031d0d020306180a0f05160501020a26 61
    0x750500255100c82d0040c100403d00d600621503c1a1403081c59032400492038280500b40c0b149900d180d045080900d408080780c4880e1070440c0d165000d0207108610049079032146000031244089080040344100146030000c0440800ba100c407520703850240c1080031540c1d81c540110190755091411400d8201c45203003c4001d0410521450f910114098000c20480c406038050025144112403242940f02403042101c120b12900d242c01e50015400c102102d54000000d000d0640c00d41072080310211104507954015011104140d0402d050f00034016000c1c80b49001d500130b0b00a480105c5103040ca80c103082002c450303270001305542d482407160340300000380c0140d98a00900004641290714084100024a001840b6070179003000345c20910f040100000fa14145441e400c555698050020300c40c0d500d4038441043d140310081b5440107903100300180c40340010100106861342501c100300a000d810365440003030340e00319841c3d0051411075004100b07010100e58100e0f85031801c4007030080180800321045a041d8610310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 567263830 1250 567262580 567262601
    0x20a170c061b011a0a0b1c0c2601090e03120a09030201090212010221041115040506041d070c030f0c0312050106021f18110409062307030204030f030e0301 68
    0x1440e2100c5024605140580c4204c9481d0407030b960807215071110942000c0c0d000b10343c103802501a500d070600d50307041e8855210605032101403d18401c4000c413000c1d40b40d1281c80d082a40309030545c44000401074014640205400e14910788083e60405000040201821200506040302c10341c88090210526000b0f600c000c56181e0040d00c41e0341d2b44890030038140d01030750000203000044c0100842c00f003041881c103203805000c1c1da0b0060882c5c01f003034002c004100c0c1501c450f00042411510400000520780c0d80d1000600080074400c01b001031921400c50721000e601c200a08000034841900c61200002c0c0e88440d502e0b81880e001d0030a0031280e0103e0400300c07844498032509210707152130003001048640e000070f8040141818030306212001d40c403c1c0090320a0301e218415003a00d40800440140c001000078190f41c89900d0080d02c0090f1485043c0c0780c500035a0400d400410007041b0001d0070504001400074055072104280c1000d5103818956900c50300400840c1002a0800200360070704071242c0e0f000c1d08810001c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 567265080 1250 567263830 567263833
    0x503030a0507210f17061309031812150504030507020d21050316110304090b0114130e07110714030a02030f0c0a0816060309140304030609020a170c061b 67
    0x1458500c0010b04040000120310300420b281c0740c9031018203035102030140c0c4500390103800b00d1f26581d200c200f0000078145801d4111f06001040c3e00341c009502520b08210001d2800501411004a09051002c40300b95030301100c01400e404d080030070000c41d801c141110040c0360706030b88001c01e4450b2800c0c0750700340518a11138156440005648000345542c400302840c0219900f072104125195806010341340d41510144d100216001880100304188556104800449060404a5007004011107110032940035090154081c24040400d20011340b400c40c800c1c0d8030880e603040c40780d10309044280385d55440a00b40f18483d42c90509003041030795070301c0a00c1002c01c01c0e54043c0894002c0d80310060032641301c12168010234010b10100c00700040c40d1800080b0000082c8401c806400791a04000044024000d051400ea0b490420000001e80d51002000248010b41c000d60380003d194155104100004280f640048038900c40e04117241c14884011600035010401203864541e506008804078055143c10018464607 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 567266187 1107 567265080 567265133
    0x70504141c1b0e040f0c050307060e0d03031107051b041401170a08030c030105011b0231020711030c040c09120201090902220801060503030a0507 64
    0x6039031031240c90302c0321540311501c8601864050710129902c0c5420130180051007108139010004d44021006800c03964a4250b0040c840220f04103003d2162107070f182004105402640714507080d00c1f100c140a070b101c1c201401c109071102e02d003a28104010002c2e00448400d858075200e00400c100307042001d03060a90034150203a09030404c00000000760b10a0720301010104411101551290740c00c1c04a60b9a02d6050000040041400c4144100301035101cdc103c450040ea01d070158041d03860098000e1030041040c0183da212482115030580c00b40b030b40f001510205000c145c0e4088941c0c01c005808a33050748515006001c2260112030308040010b290b000e080c003c02940001101000340140351006205440365000300403a400903858002d866052100305403854000f07940340c0010704d1880000c101503460100030a4403841500d04c04020420000748400c10400e20321454401c00d100f02001401 = true := by decide +kernel

theorem cover : BRFrame.Cov 567086330 567266187 := by
  have h0 := BRFrame.cov_init 567086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 567086330 ≤ n) (h2 : n < 567266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
