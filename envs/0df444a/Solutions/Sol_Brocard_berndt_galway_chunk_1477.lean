-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1477
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:10:19.456874+00:00
-- url     : https://prove2.me/submissions/ae2db506-ffeb-4691-a2df-71a069a5e63e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 265467625 ≤ n < 265647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 265468875 1250 265467625 265467667
    0xa0306020a051606090c0603290a17010209040501060207060c080306031606050703080a050105061e0d0c0915020a150c020a02091003020a0e0610080907030f110103050714 75
    0x50040900c00b144003c25440140c18039644604c0d0300051049107880c0818107a4070710340001080520b0192000c1440300c20501100c3c036294144551000b100403100061003e502640081c0012103a40074041c011400540150000300d0f030844041c8500e07a2298400c9135121001d200340d00009039031522004c0400c902000460700000041c1c259030340301c60140c0342c0400702e12003540013100264000801d00c0505074480d41958000d0901041440b0951410700041c0f9940100a507007196899503607058495a260a42207030203030841030005101019114202030640942c502c42c1d40d00c4c1a05801614802501c003088001703849912200000d01c005001552000403d000c0607944194881c0d45800383c00341c0c0e00c40300c05610a080ca142910016411032040c080044081d51000c4c1d0404003a1060180c40d594a941320610700b03015141c445842d0342c814003240e182c00c0c590b43c00a131642c841c01c40840180585041d05900010003030300d0600460711202c108468410140890425001080c0403c440c040c00070042d0b815 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 265470125 1250 265468875 265468877
    0x702010503071403040b1f030203120a200c01120b0108040b0402010507020d061a0103020f030a05071e020703030e0d0302060c090402040b0c010e0c190515040306050a090b0a0b0a0306020a 82
    0x1240c440c0c03243e04641190b01c03c1d10f003a214a0702078010809504510040c0350524141d1400e40044149140d0210780c0ea151003c41160001c02d000c9060454a84500407110108a440c805000003c50504042e5220fa8150011600184503850703500141409070080d0422508107070341d00c0b160350356280c441c00c4164601038070480c1040001c009110142c0e8031440140b0030f80d40110000510503858580d101d0300c0401c074075190341c107150050010a043e5450101502d0744150981c2c4042090307074501c81c003116084084021208402c0480040311030599002039000c05a0307110345c54490000c6800d40411909001c1d60b0401130050f4030010008002806c41c1c4040c000400029001506145c6c5810005540c1d4120560000f0039a41d0f408141802000030008042003007010741e46824140688480340e400c0e445180681400b0380c1184030880407400d520310454008540110003000141406a00e032400750041000503151780000c6008078154601500c03404070b550345c0042c21010032910b5552920701942110215030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 265471375 1250 265470125 265470137
    0x70b0904200d060e180304170304080f0601030c090203042022140c07050d261e010503060118090809090103050d031a01090314010e0d11010b1005070201050307 70
    0xd1030501d00d00000e0680c401d00c042c408962282404104500b07008000c024402101e64441803501e10b0300f0110850f000d8a900942d17284903496038140ca00d113036100c1c0d540008aa441182420300f642c0d01c1c0400c0703182c10f03a4401e41c3c0d05da041543d1040c01c07070180e0100b505c1c040c1510b111100c41800404480c2610f90981e40060007200c0144640c2103221134400855204501e80750700c0744141c0c40c415008014465000d0840380840e42000031586980355229560306a00c07080c40307900c68100c0d001c4600321940c0c082e80072504071118024589541051866080301d25040302c13085806001251915011400074142c4242c1c0e44008502d00c04403c9ca08050040030f00140e843c920200f04c40460f81d10781c050b041d80030754044c0c0b005204c03034402031000404a8414000b40781591541840c0030a0130780c0d01425413030031aa0854041d198600d14644101d00424446619a584d486100c642802040e000001300159803134000c020803a16840304140054043e04207a2900001c1c1c0403c186001580128081e50300903d00345802 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 265472625 1250 265471375 265471421
    0x30e04020d061a0c0c19030f24020903061e19020706020309030405010809010e0a02090a0e0f010510051804020427060b040c0e030705240313060e070b0904 68
    0xf410301840c041082001200010701d42415200c01c201810698800784ea0443c071544150b4980004010180401400b505140d140681130180942040040006050b20549041440103e2600070360100816a01134061100005d80c3c040f02003013100d1000c0c04800706000e20741e540301c2c441c81c12010041d40350b07000c2642c00d000000202e6103d1016510804905001f16541c504100001d818208020103003101e036810706d1207012030f0f01c0c07021403041d8400768103898000c40f94841d905804050030711030600880302d120f0034041e001ca5500541003079020f100c10541d0401140e441d0001d010150303c010041140781140c01c008200113040c07691240d107000c0d4500d0081209204003599040c80e142411106441281e1501c0b6810f10620f0710744500c07170b1a0409420920084040c0e000881d4980507144a19071084061405051060210074090780001900b01000c07603881c681100d5a440740b050450342540d03074078600594558030315000110241a00c40f0340303800504001003002000064034000d000c08101caa00d200f00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 265473875 1250 265472625 265472639
    0x30a0e011401090605220903050c010911120a230f0f03040618060c120513030506090706110631060207060f0204050f0111010b0a0b0a02010f09030e04020d06 69
    0x328081100141500a1079515020101c0c042d2019600b241d4070910340b01c21803002022022080820040540c040031444030703600d05081c2c40a00440800f85003d50800800360304110303400c2200709010301c00b00c41105d00030301d400c100d103035491280c0c80c4000c02e20354071440d41c074207a04c18610641c4030306102c4c1d07801c5811102104c0001820440e04114050303981d031000c5014070102e41c019039040a003a40c41da50303141025150031001050b2810440c0c01618121003c2e406048540c450421a030440a041c402805160b589240c05540d0710303c200e65805e11402910004a92103202c0e40a0700ca46c01d01e0b90000742041d40b10041d05080049100eaa81c292122500d560070000482c07491441040728060207005032502038605000c02540d1031540c0c00b00109104020a01c600d03034030288156590403081c6005001c004030b10039520300404803603503095400b02d03034a10000350060303030600107150101c0c0c03a0b4020b204540100e0555001c0c0e0315924002004610200c0192406091035809440340550416000c90859600c1c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 265475125 1250 265473875 265473881
    0xd0c05040c02060906010b0a0e06090d060203131b03030e060a2a060e06090601120618061b02061501030c020c090c0c010b0901210302032107030507050304030212030a0e01 75
    0x100c4107000d60002c0c001c11120120900c1124014400c1ca04154600305101c1401001c15880c0d44555110304004140f0302d400c0d880d0305481410450f40100700b19524181b40d11040d000d005641c200302c41001001c0c422081009411444e2012244c0c552210700d4040d441e50100b00d019007151641404103e031081b4115000c0c148098428011060b400003403080d0109800c1c0784003540e28031200841c555004c0420300000301d0001800c0390448128600c0e00400b05442c2c40e0041c082c05042c200b0030011020540b402040c04102d0340031000360200f101c600c040e4614a1081a80c60f84412a4003651030390003072440800e40e5000341c206600203405441a21041c228480020321503d03011384129640313400200d0048480c0100340b00d9030f4090903080b240d501a41d8582040e880d02030b08400321b94204001403070b60b1641054020025a00d0a09428030420002094580d0307000d0903a000300d400c82d00090070304d00416842070044c3d0469000d180c155000c1e103080e02451401c54895400901007115181e907405140039810380030f00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 265476375 1250 265475125 265475141
    0x5040308011401110709051305100c090e0f06041a031f0f060b09060705031608030f0703020306060a1808030409050907320f1c120302180d0c0504 64
    0x912820200d5040a0009220b190302c6258141404040250101440030005510080b58034000b000b003002d41d5002400340c00e400703010800410a21810240310489003030780d0004130180c00140c2e210525a40d4400c0c03800240c10b801e6807013100307514400e0003040d040d0030640c20901c413a0b986ea10350040440141c41c04640380c14042040a00c6582d180340031608203204e44d0280e6034a68110081c01d000050078101182900d03c28002c1007440f60f500000d00c4000c00900b0300a98a001d040da104d40300160226092100320343c1c2c03040314a000380114960002c0c2e14140a442528002c20740a01400d0030011681c10a403100c1703514010000c1140d494200019210204100070006404040300114040c00c005103044c2ca0000d00d500040426868041611514040015041000c24404940c6850400d80201140e801da404082c2c00b900442012400c0840907041c01c03030f070210b00784140d5190300c804d150410110204d004101c2000020b01000d41020801d25080703178140c5445004101c2042901c1c1e45100242c03c07a140c81d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 265477625 1250 265476375 265476377
    0x304030315030f02041a1c1505010b030901150b0906130b03010833060907050c010c03020408160501090b0d0b0310050106080907060f050a121406031006050a090e030d050403 76
    0x43c10303901046052a019100d0501c001c070390302c501101c010000048070310b003000307210086240b003464101d4180701182100b50240c1513049010000f658481d21404400da100700e071100369542c00c040190b0000c1c40103507a00d1040f565800202810000d000c01004003541c0180050201150504d00110b01503e91000450081c01000e00800f0050441000180b04452550044005849001d45074011041a010b81540b10074101c035220030780d58880c4010382d0180601d8035060750070f601c0d14a803d13034030507007680c010026146100304545840030041d0340402c0d60035103801500d00040e5440c03420080b916900000d084114644800070444020300e01c08240760030000d1440241c040d850300b00403c0174a4204050f0740d04618882c000c0c100c034509107000074080603c2041e2200400c900015000c04a80c450450038508000c6640140034404642c11206503144095484c54400d00030341c03d01c00d00d64101c61260804464001e456a6030300c031700c0e15900b4001403a21307880c4000c0c64002004404880c0d5154482c00d4400c500c0307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 265478875 1250 265477625 265477643
    0x209010f0611060f0606070507080f030a030e030903100e0f0313030c0803030f04020d0f0b0a0504030807030b011b0c0b0f07030207090908030f040519030203090405090309100302030403031503 84
    0x54400010007001a03035a207600b50b60440f030300384030500c81c81c2d542c00342d80b0507001c0c1c0f10395681d030080e8500716103441d019601446d4140241400c00d091010084002c1000040c250307028000c1d0102c058109850303206048685a050340b0008501081e0400c40c3c02000070342450800b03484103c00a980e03528110341c03010b1860244a00010818000c03c02d403c80050b0180959000441c1103182903d0b1140702030700060b002078440c2c0900b002c048100100e80c548d00d00450b500180681d05814144645006400103403011400b203207a120014a541b40700348144105240141c5d0b5450102c00c840714850356007462414140c0d81c80700e084801160311111a00180a5031a541244964a140c503040090400c03a00ba001a0401ca0805115030080b440050940350880303640b005108042e1a64500f80f0300e02089101541c1d030080624622409064012020b00403041781540d0602256440c41601501c91198101460740302201e982015006c520a902a5501501c01e0500140c45440072200003440ca105620403500d40350 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 265480125 1250 265478875 265478879
    0x60601030e0a0f0c150c1a2202190305010203060906010f1202030c040e010308070c05010e09061002150a02040e10051809010908070c0501022401050f152a06010b120703090209010f 79
    0x7c0300d200440030000d601841da9843c1800141d4282246008030914016200300c07551000b9503441d000000c0900c95003244628015542c1d1a2482c082d406c200c034400e100f8001040021500d500511980064a82607070b5481d05110141d42001c0c02500301030854454032000748000316414000e07840c100e001e140203d5080d9103800043c0782c0100003c805030481c80c10821015a0140c0d203440c0c401c41603804c40002c0310049200d5009200403460030b8211000c0c1c2c9507009064042c400c4804880d801401075070003001514079190b4540b40d5901c5620700300e21403582c204400e114071461152140c2c0352690005881030001c200007045444004d41c503004141d064902c0040081c04100d65a010446011001c807640445d059241c1a44000e040e5110140b080318010840341e070701c482c8280e517001c146a140446107907040d0385441e8448030301174980c0d1190b980d1404507480c0d803920298a0b0f50000304a0f0486140d2983d1503e81080e50383c00d14090715002c0c00c407000f45519682400016a100700400c0d01070b00c1f88601d48032083d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 265481375 1250 265480125 265480133
    0x509090c0306010807050a0b0c0f100f110702030a080a09150302040e0708040302070e0c040f03080a090b27010e091603050604090f0204111b01050108060601030e0a0f0c150c 76
    0x242c103030b100080030b502c440001c20407a11201c041d0400c40d040c01004c2c54481046160050800e508003104421070300455000d003001120f00d070310210180c00076000800c1300030041e00d0042000c0c410b0072000795040d407004807d030001500d104028200c0c43c403d881c119440a60b6100f140c0080c0f03401742122008660003080074003481601d1030845600c00010314200d010ba0030542c07401b07511000c030790054a000c1178400c00003034035400b49541194014000035483c0c00105a690a0a00c01c58002c903030900005000d06000140c140c460209541960003207459024a8001c0803c4207040492a01d441d1418049208800100c80e520807280c940f15441101e44098032204880e0001c003240d0004200c80d10951400c0c0030320740840c244404079184180d0660740010400a8052031004900600602e2030001410308001d1440c848190049070407035502070100d5406c0d4491400540030740c0c5100e02c0e48a030991110100c4008103815000440650740108100551280c48025400d94a407131030a2800104a4684070a4200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 265482625 1250 265481375 265481383
    0x7050607020606090103081204030e030304080f15060931201f0315121b0b03060904112e0908030c15041a100603180224040509090c03 59
    0x3c0501140c281500350f0540d6915401030080d010087d018000302c0c400101010b015103119944081c004046030744076556031410360f50b18004010190514020700202d041d146542c500100d011706c41c005c107840321aa40310619020410a00f6284602500b00701c0c41a520001e050411084107600400c50070006400d1040340525120b001d84205000d42000e00301c01ca0301000b2001d036004802d14520300030552580485201c10412a16080001180700b4801d1240401407158160381e0000048920640c50a40d114040481400308640c259040404600000d00150084400303000d03401004100c0c50860140b00610707a207504015410201c00f003411560341c1c2e402d64001e00d41030b004041c0b00001f18503007069250000d032188000c51004001d0340d003600120b41002112560150602c003004401503041c44c00510075980540e0500c51038001c80e16040c0603000c6001c103c1e0345001e1613500070b800154000e194940b80500403013841203480c240c95041c0f00204842d07440a00490056980e44020607620000104040c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 265483875 1250 265482625 265482631
    0x1050907080f060103020714070f1e030f030c02061b010605040b0d08070b0601050d02030c0301140d0f1502070b010b09030607090602120a0302040e1006030f11030105091b070506070206 81
    0x2404510810001041040391140703511038401c1c45c0241c1c4a0101d40360a082000044005032140e0156000103e8412114000c040c00c98155508404401001040407129040e0b0b0303000161001ca00c11040c100403900417403001881b28030290165280c00b280c041e23078407186550a0f1109000745d4644504100903d81805909490041118600c07003004440d5115903a501c02d246000344510000e800150311603000e08159070560840b01429556490700d45041c809503442400341d01e060030041840b400a904241c1214015180d01c421003060800c129198110f0307081c10010a8080310740c003006903100103a00081100e0080401c03094440d11072844004043c213005004000e03401b00040c01100b044520b42c006421100880703044429030307541c1d0304100c00300c020b80b085801840c0f46480c1801485a00200101c52104513030040d5020001d41c02e031902208143c4960340c007000302014041c0014030251400c0e0424641203081c0701600301201c0603c0b08030080035041650195080c2c1c102d401004041da070184252a4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 265485125 1250 265483875 265483877
    0x10c02070f1a030114041103070201060e0705032e08030d0501091107050613020409120e03060901200c0114090d09080d0906030e01151518060906110307170301050907 73
    0x324002003400e034060105102e508940a17030302c80d980019444681c01038410f01018400150351b441c3c07050000e8040c0c002841840d10a900107400501c513503100d1415640035000f55400d18858080a07000109444000450601c4c0c07218488030004400000700010400d1103540341021415602d00740b00c0c2c8048400d000920042000d08100d0040051008100d140d40024011a40b0000f0000350001c80d0040002c0c03070005042040c1c28036581070258200503600705c1d68400f03c08a41d019907a840001e82030703130341d0b641d0503501d2a42c400c1031140f000c0303205201905180503420000680390100c00c10907100c5039820360300c0c214143c01588589030300d250300c0300c0820040d251003401002640a170350780040054000f0700c00d080415940d039a201040c001c0c207401440680312807412040e5001c0d191100100c500544461181c0455003481608644102d02c01f034860880380e01d034550700403c51a051058400010004c2c0303080d002d000420901c7c0000320022060082030032402e241c0c6490750705080c00e00810b0b20f8041c140d04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 265486375 1250 265485125 265485149
    0x10c020f0c030c010c060908162105091c060504032102120a02070f0212030a032a0e030a0605330a06110c0a080a06230403140c010c02070f 61
    0x241e265180081d07401900002031030189410340450820400820b1640c41c02400404c00042c1070074610b0318040001d12030f502680c0c03034861000c116000d940c2a10340c400707901c030301140f0305000754040c46c40d01c15a01c60910100c404601c100c6102565000101c40080720200c3c042184414102045841c10b81c0d812012100c0610442c0f41c01c0318580720741090040100720810860700000e80c03004120002613842c1030b040d4041e14034003403200540304d42034481c1c0003080b001000134600001c01c98803100401c0301c18003104003440390b0410840a442d04072a026264030107160144249201040050700612480d0310500300c0e0b403541c000b08604903006241c03003a9160f544030580c1d901d0240000c00381e5510f0002c682100d5a9042038411200c0003240b4609000c402658280d02494105d4005a1b182012070698410b92088404000040c00c1f035120b04803c00c0d1200304189011021400100000d025241d01041da10b40b002c001c60601c01c004185a00392540c80d032a000060300084010004d41c0c00c80c000c1c82016003881d041c08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 265487625 1250 265486375 265486393
    0x3140a020c162304060b0a030504110a0e04060203040503090a03030309110108070e2b080d0612050318011701081c02010506030d12060312090305191203090c0803030108010c020f 78
    0x40b00a01c3ca040040b0440c508015000312181e4481d4446001003400e48100380e10380940c00c0d4050002c20040724251245a079070300045085280c514000c071b007995840c90385000c1139110390320782c0750007900000c00071505031204102e0614203503580c4506e1307030013144079580c04501b110040c45c05201c890b2008024a0504c0781181c203001050ba042801c092031f0102c1030310022411400caa9070107a908040755218412200c0c44000c000c03d100104005140c4071042203400d1041da030780e401500714022040d44016005070070901494009080e1020150303c255414904015441c0c040d0f017545d02c0e41710080e4482c00c869401181c10301c4964450410640c000303d03082c0003c00045c901000400e4458101c105a803040000da50f103091180030b403a60100f4059500198903110030101c8040140034101d080c00252100e101e180860302180c07522503610800a588004111510784200106602611001c2401c0381c0302030305d016000c01c01201c100003650003004a0303000820341c809410000b90814400c91045400b5402101903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 265488875 1250 265487625 265487639
    0x211c0e0108160c0209090d091415070309091a0102010c03060609061107080607020106050a0b03070903020603040614150135041a130b0c0315060a03140a020c16 70
    0x1499900c08440404140b2010021400325103030303803826400a43c00540d040c10302004c0c030000225082c61640e90744499600765200d02c0400c000c0c00d0942d0507980d1200320140013850702d08100019129007440b0b402c0000d42a1303200d201c80c5050b00e25050210f89100c0d4961460100e940e424003c020092106050801082d81000070082800645000381002c0c0701107404e03201d1005a08210900c01842e8140a440c46400c00c200001c1c042c01d010301c07034039114114000c00032407603c1c0c55504480c02074101e920b0f030507461f9103564280101500020310a440c0a40d45500809140744c964010030320402070b018040346503007000000508883c80510494103011640e15071035440604c1c0e0099202c140200561070340c40b40c0d40324640034815581e081c0c107004104a0700400d0041c50410001c900600c0c5105d4407586201ea603521610b110b003400211840d58402c00c456910762400e040400040201050380e14001c80c1d05407403100e00824550302034a02c041d0352980001c220300b420750f05002c12000d110030110306030305d854a007000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 265490125 1250 265488875 265488887
    0x3051c02070203060a110d06030b0915010803040510031e0b04060b07020102250f0b0301050301110a020613050c0a0e04020f04020c0d0324080a0c050603060a0303030b211c0e01 77
    0x11025007651b10150041c00445040951b00070608424090121940303d2410901c041c07800d0354400d400d80b00311540390b100192040a0745069503520001507003050b15180070040800d0100c2440000c3c15039461a600c2d41c2444441e100e80d00f000010720204107058500c0502080710007a904c4911481014400140180c2c1d0101d2002460246000415081000c900c140d50940d141ca900284071344400340710010b142c0c0303003c001540c101c0c0c03c00c03070080005916044290f07481e4414290002c0040e00300d040050060487c840300186111b000e081251402404440880c07030400454001c01a0707510301c1c804000c11490100e041e00c580700c005450560a01556031560b41d615120014060249511104010765071000c074825200792f014403001c48200c090f03580041030749500440c80103032541a50040c010449003003000803030303000b0b010103080d103c0d2035442c40e10220020300004000540c44400950440300000c1c068040b0061000c940c005440c074942c0940901d0b042c641c19411a1090204a103c401566178100b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 265491375 1250 265490125 265490131
    0x3070203130f08120918010f030b0a05070903080c010f1d01060902340606140906010806010206010513061203020f0f0c010c080f1204066303051c0207020306 69
    0x201041da25500711200040d4203040d01840c61b549541c41c8400022184006240da1080b01d0040341a00c00300d840d801d02d1081a24412141031000c00c03000001080040c14101c010305030900036000000c4c01c0014415810141d5888920b07031014072001014158580342e080c800c0c0300051100348011481e010b04011030f4841c4101d001400407581841c0051000c40d12030082e28000d00a9000b14104241a1660354903c1c0c1d42d224150a10701401c504400244254000d00509007d008140c000f442c5503031803d820010303481c2003a80d20030245a01d030b40000801207008000002414402d4001d0903503043d90a01c840c1c03500710034545505040c1e011410310360243e600001c0703070034800307810030f444540e610741d0640040c226115074000c60110f10b010104010900030175a0000d084502002030854020525815030b100054404080d02d40590207641100b01014003640401c00801285440d4141d290904030343c542c2c3c884e0340340001d4002c1080044d014044090f2881e090501c440300300000c50800704c12b03401195950b0801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 265492625 1250 265491375 265491403
    0x40e10020906070b0901050a140f221b0512070e0c070816141b011706031204080d030501060f020307030c0c0b0f040302090705070f111503070203130f08 67
    0x2031511040c2c440e01c003140c0314260000704007034031801e04103c440c0c020542110040c01e59481c00300d0300015400202400350084080c402a00000e45903000d0249001c00d20383e16084c3d100031516004030000f0000454400d01860b00146c0700300e040c2c64001407002d42c01c1402034207401508500c800b440f200c56048041604502c0901c00c982d100c401d40d103002c04862080d9040041c0a401011a0be407c0240c05518410800d922805842c1e10700c11000010001003400780e00c2c1400714040643c920030a14144402580c042c40041c2201c2100001c41701e0145a0360058018500c190001c1c0490707001a50540505030060520345415034446108400003500c1e030044010090801c022144200e09100300000c0403c0544561a140c17076440b000c0c1e680380c0d030300c075031040c03004038016482d901c00645401d0050054070740d29130b00090b500b4000e030319550300c8002229141d2016540000c0b10f4214402c4614020041c610030300c803070340003155900c1c602c407803450500c181e990120f400c0070600c4100f417081c07100101e2006120551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 265493875 1250 265492625 265492627
    0x209060a26100e03031501090609090519060b030916030c0608090c09090a0201030e06040201080408070812151806011e0507051c080a230702010f1b0e040e1002 70
    0x2000100600b0160380800e40d8140e982403000c04040100d0120065019541d5042001c02c02c00814005541d4a03a140c07141c1c4000c10044002040f400702c441d0080ba6001d59200101400f444151919004071a80c83e007014030b1101e0003000b009409241000304140012600225001d40d07484d46e0b642d1862091140140d10400c03540d4070201d0780d21401004210503241c4001c100746414502100065078516010b1402c0e4002810080205132485011417254050754043e51203101c1503a03a5100ca06443c0d001010490340b400c410400070301000c901f40d183c2805400c0720000480d1a0f039004041056241d84d06c1075412007940d00b80c0a0200b40d81c5c01c140022100034051002c0d050716040200309540c00e0107480d1026003c0d0140d41111205c0020b5108040402030050f2100416a10f42d2040072080f121000403e01a081e8010504000c0010883c00305501034042e10011914104008400e4143c07002c1c0c0380548010502d003040c8810761600882101d003640401d0350f0801c400141c640403280d4a40711900f21080700d51f8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 265495125 1250 265493875 265493939
    0x8010b160807082a01060e01050307060e06070b0411040509030a08071107030804090c030e030c0304061404120c060f02010b0319020a0308030403020d03050732190503040209060a 78
    0x265040695940140345100348210502c41c0e03800100c10301030344110344c0d031a502e04400440c418181c0ba2201e8140c0f60080c00a000c3d5505000c820303210360b0342607441e06600c200b043c41014002940340584900c11480366180d4030f120b0b1209420f00c8161030003c1d00425840c0c00500200302e4080d845100c0550000349072402040103481da80c0c007a41000616000541313422000100441d50403500d410405131002540d60810403c00542509070700c074000c03002d4100c180c0d0010041007007001d114985541c03410b140400f401c2c0ca0155650041010083c9102007144c403000c508908002c000c0e08204102030640090000b400440d036003c1c00640c45003444150400d080c1d400e50340c490159119204002c0c00355511030f41c0380d692410a030501940e1000d2a4100200181c2082c00240001d40316002401070b18a03500704034009004080a8800c020b003012011a030302c048180310402c0c1240e4030061b1510008110780300c1039500d0620740148200c40c0c0005180e00e0049082c990108056103c0c00303141200240c42090444c0501c1d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 265496375 1250 265495125 265495133
    0xf0b0f0d020f060c0102030f06010f050406180b0a0201140106141215030d080406050105010905060f0c0109050d09031106040b0301030807030c051e0c01020a05060a0f0b0a0b040608010b160807 84
    0x440b02030191a0040404103200440490540c001e6000d0080381002d02c00556418004603400d09041e0540c200044c0248420032009000718002c0144130203d010f0400240d8076001c02c504103401181050703005039160207036003081d655805402405007041d072404000c0c0000b200d240c6080c5109854140442d28200000125245d407001c41074042d0080003000c0d103401801e0780b0401490369038191070030350b0a0791502c00005050b41c043c0754001c003101c201412460a0800864969815810182c0e817941c943d500e401c40940003031000c2c009521480d071145c84450045043d820040c6101d00001e400501401040200b805581103081c01d6904590b40a00d92030f40d10040d501d000c803040302031190010140d228401078030002d489400b000612074420141200e0101070070100480e61441c01c0c0c000039010390400e802290b19160b890b0054100d40d110000045403552540003c03911b071050542c030841c850310021605010b00d0b46e105410500400c0389808080c10040b0b01a034000c40102d06103070041900b580055000104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 265497625 1250 265496375 265496389
    0x504030b040b040c060c02090a021b0a0309090b19050402250b06090f042a030f050f0d1701142701080d0201062103020102070c120203010f0b0f0d02 65
    0xa1035000900c1036080c00c1900d003590071200c040c3ca0846021400d1300d80442e02034030030f0822000040e0024003a030490380b0303a50039900080d40110300c04004402c002c42e5070211f50b40c04202200d00e8038880c6d506e074441d1038580380d01d800c225500d2a4001d841001000c0d4004991040b03208050151b0b4400c13540140d941c034444046031400003003a511120114075042801d02407203400741210303120340c0342a14030000c281c0d15103002070481d8004581c000d0100702d820104901d40c02d50200f880004038441d0400c50308090b20381d100d0110203804050704a42030b40c00b400b5500b4044106000412004000342030586400c40d2888038840c40c82014024642a070b4040183c00126640303504403032907050390f42c80d418100e000708103c48000e84042406040509c1c1700f49018000c120b0710520401040b074080905100303c00500307072142c00494105c0042502107640034082540455140f00070030008007440c4040301d41c44541441031500391060040100000fa16040d07034074140c0d85920048450185c4201ea0003041c1e40d80a200041c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 265498875 1250 265497625 265497629
    0x14010c12110a03031e0605060d0e01020d2a090509010603020c120c0307020a1e060309060e0118150606080609090717070302120f0a0f05210a031d0c010f0504 69
    0x54424910140140360b0140d00c09482c2400c0c1c0381c40e81d81c0c0e00d03800c0110b40086e078131240b051540081e0200080d48050100e41c0c440345281140c500003500c0d048860011409651020b42002440390110b0000201280481d41100001e50b80341027440c0910f103800300141c0790300014825a070506400103040380e400c42040c81880e54210380c0c040051346410640410300d940360441407040340940c00341d04011038905c00c0300001d80c2d801d0002c442335000e003600b010411406403140d100111f49494440c0380071203203581c0038011000350b800d0980c1c10f845200c88030700b08a200000b10511118040340341000521010350b21940300c65100b01c0503907065215440f00c80d509413429072261700189250b00b080b01e14a5a0950120301d1034202d90084030888582000044a2a1500c00801d503025281e0b03c0700344228001561846100284ca000c0d40c2a904000c01c0845107160040e00218140c0c0c0c82d40f0000303060301c080c54152140c81c0400d00540b1310912600c0d60b269260b40c1c0d4102d100312060600c84080340c01c6040510031011100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 265500125 1250 265498875 265498907
    0xc04060308030c03040f29091b010f020307020a150f0e0109060f180602030a0905040209100c1703090c01030e01200313060f06050a05090c0f03060d14100614010c12 72
    0x49409481918015607107ca1031609a00110010900004000032611711744520403088980d50800342005580003440d03048080c007076020600100f00135a44407104070005150f0a00c0829030641c5400000385440c07180d40c1d070741d000e1043c46000b00b00340b40d90040c0134105540f964149045400441e403000c0c4ca000f800d081ca030b5220745184000204200e41c3c040b0103800040c4140d111102580c0d01c07182000b040e800f4003400b50350403000650a01e818144900000035102c1e00600da1111280081220300301c50342d1080305c010165a102e00405810365905100d145001d00c200350003040305203040440406070040e91000d030a204100400410404188403203c4041c040e80000c04108078000030b04040040c002c103100d44c3d4814441c6240c0000d43d801c049070041d01c580008941c45180410601240f05190806002c90303804c004121101d20008810140c8180301c403a0610003840201203642d01c11082d5001030b00700700e40c464a05a0024680c2e600503120329622540018440075140500c50701b01e130b0b43c08100d2802d070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 265501375 1250 265500125 265500143
    0x504231302010f0f050d0515060a0314060d02030a12031d1506040e0a020d15060801090510140c030c04050406180e12040e06040e010c051b0d080604020a0c0b0114030c04060308030c03040f 82
    0x2b82d0340c94040e80907404c84010744604044d540c2d03c2004000b100c0640c004041d415400020000c00001e031041d10a80803044070b41000174110751106406481070030315026015096200c0d100030031a503003660101546c0203000300c50a04c404e640110b4001c3e2101c42400d402806907a2008954041001c2c980e4415002099008100129950b84107001d0190a04647c10768503400342900221200246000e0001382144108081e10141c594442c404003680c001418084210018000071519a6860103070704001d00c400301450030b1409900801e0f8045482441da4a2000d90040200e17504141194058908840103444101c2072640e42501007000f0b071524200124035540b806021270a03158015000d00041081c1203460080c002000c44070b980c0d602100c29010000c0360360240041e04038982a0000c1010420500d0200d00560503a610b900c40c104003a04403148108406483c07000509003042405401c3c2d008031018400207140d6203515005200151140306001000800a01032000213021040c125038041540d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 265502625 1250 265501375 265501387
    0x50a0903021c06061d04120207050310050a0c0e011e09080a0308010e070507020117040203100c05030a0b090c0304060b0303131d0105010c05070504231302010f0f050d051506 76
    0x300703400e04681d8012243c0303900e441e20105000c528a040080705090380355081c0e000d601c85407101c240e4101c40c101c003841107111b034100120703041e03e040c0b190040048620402140905140c10580c0a8508004665080085400d558a816a07000b265880191241d00c5060407080c000c8404540f040f03031075006001c40340b14a00c481401c0581c401250340c101c5481035500440c43d04c6503101100d25104d03c003401380c000303200521005150300b40501d13401d0b041880242100c41030700c85d201c110b1083c0ea0101d00d602d004a5004410000c042c00c0600448842c0c000858040d042d501d011410302d0780a00001c0c0c4050b0401340c7d221065036103501c040044594840c0c41080420400c0d80d80c0280200700c040c001c07400702c009042e1400000c1d480d400f6040500005a20078064042c071410001030100501c1074407101250401c880b1214003d100c034201d540d500501c6110600f01080c5042c1c000075290749885140c0104101242c50350000d055030007410b55140d00c1c801c02005c0b90a45401d503005070a15050f1402c160701a00005035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 265503875 1250 265502625 265502659
    0x11010302090604120218100605030c090d050a17070b0a0b04060305070807090621110a1502070828031202090915030705010201060b070b060d121115060a0303050a090302 74
    0x50144e4540c421200c0d100303241c00c01014200034220543c1c100b80504401582170045c00e0191028507806804190528144145000012446443c0203402c1c0c034642c0001d0010801e200f28400d006901001c00441640740c6a401d5485500c1c1482c0180400c1c0364581d100500e18a0780c1c0c40381c10010003150088111800c01c0d40b21404a61034607010f10541c14400e00d8100c00103450f0032561205409a0105d01c15003115000c1c0740c6a000c0c80440400c0c15541c440001040411f0400986610700b20289081c1e00401d0361900340722a03c1d20b81108100b6010b0040307151103000aa000030b040542c090300ea41071074070b40049101c66155070003030300401d088140e109610b0070800055040520403c800b0711300450407201c030196280010382c04c9400500a51001c50b404009803070200e2000c00605812140250890309502c4031a00d400d01e120710078215444c0001c0e4000039901c0c800c07c04100c400c0401507603407001c07030a0341070420000341c152a0034800101440404035115500394040c8903241c00554020b0100c0002528460b2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 265505125 1250 265503875 265503899
    0x4090606051207020c10080a0902060301060e0310020c07180e011b02210d11160303141b1611030105040c0501020d051213020d1707060e0607080411010302090604 71
    0x300704011942c02c030000340003510016058000c1880604000800d128903002101c1e002c130010003000ca003d40700c1d030740000140c03a16401107008140658805c11224070300400c15041001c032110424103103005010701310b40b1722000314400040380c00e249a03d0888000011652000e41495107401840c0c3d481e0030740c03640c0c0c414088901766041004aa0035900e01031380e081d6042003550042954010002c50034410180c6a02590340001e00500c801c05c3c649040c5113041402d00ca13684c0280000700d0001c0e480b1014244040002c0768800d0300030845402402030f201100e203006c8040c1c0140300e052105200d80240035000d002204107034082c1e000c0c01600030302c11841c040c01d010035004130920074180144150080940138a114006552070b06814215018154403413800080440c2d030000c00c1a648564020f168000045c031007400b138107004403285017a80d105e003818280041120465822107120b9003100c07003005a0f0540c0300a010354031541c041c00b849003618816004030000e0080e0200c070b94000f00001408910400e23109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 265506375 1250 265505125 265505137
    0x406020a0213140c090103060b130303030b090f0604051806040b0414010c02030d02070303020910030506040b010f080402040e010e1203040606090219030b011b0b0910110d110409060605 81
    0x1e0361414400e04001c0e001c408840e40c100f0020f01c4a0078100100e00d8461002c8001c20302050140350100e20039413248220700c4a07a111031461450351120900030030030150140504a0804411105405030b85007080014005440040605110741d41d02c90004003200001d090300540b0700c03018400c9038410b04d0a46001d422103417050b142620001426844000140d205029401240d04190b000c2c0d4100790041d801d000103074002c1c0c90b084080c5502884078040c030303803100d1060400048003a64040303500d083c00408d010484071048003c504001d080c0068510142c0c015101d5a0007950584000174011090000c042c018a800111988680a8030701c3d09501c65001902450146d805036a04000107983c44461800f06d02c220000761003150380718000141c00a0103944080b21011040c1410138680e0321070b03a520403151074001c80031203590768144140300d030003401002038003241200d06004210b5800c5401d4110164046c010300095400c1e262050071f001401d150059030000e01e50484188803aa1b11210080c0040c1c0001c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 265507625 1250 265506375 265506379
    0x60f1e0e0a051f23040e01021603180b120915090307030201060f0311130e01020d0204030b06090c1803030418060602060903040303091502010b030f161205070e09120406020a02 77
    0x10742d5462940407540c3c0c03c804200d0340c40d0001d0380d00c081a50307843d075a81c08401109255000c2d0344c90100c450798030420300080c50450085003422000c4106494080d00702c044420405848008180040c8541202da60845250004207114420f15541340138000d07140c0760381c01d00b0130404038102005000103130b5400805410300301e200383c0017800752907101c142c02500c00482d0701c0050081d04880c416025507040c4980205480c01e902c0742c000c074200000c46215030990f0301101003010f41940c002810000d108040e02401d400c14800c0f148403a007410050030542c0e90307020b11f500760b070003e40c030074400006641e90410880b8001c14001b0801d85207003c648031600003c0c06c40e0306c6070320050700a2100040201070080b0031182541d6264855101840c00c0000d0300070103540300d210320310541d035854075180c42e03eaa0420892030392105440c000c01c40c1130007020034400c0c0703041c04e90b02c482890294411440c0003d003000c04d1360021b448011155102e0b503030700d0303084507460100144420305000a0000d408a01755074003184070391a076802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 265508875 1250 265507625 265507651
    0x2010c09080604080711010504031a0a0e0c09010b0d0204120605090613080f2a01061707030f020603040611041e0e1306051f060201060e0a060f1e0e0a05 67
    0x5510001d940b140411140103113034800800055002443e80f020510b01888185021400d1540380c1c2d8411852a05100000c2110000801000701d403821902409200404a8015050309410200030407500503042c01940081c0780c0200d941c1a00c1c0d030883d4180d0f4014003440700700801c802602e04015004101c2650609001d002c0c960025203800e4404400f08600c550058005261002030083c62220b40c10010b0040d8181d9021403907407216015006100c03842c51041c400000d01d2914110b1601c0068071050802105500541010800300d8142d4003680d060350340540e4080e54a6549203000c10042c002d120300ba80e0025070101b404120043c01c3c1405403800341070340c04040e100d44c0c0c40e00814180b600d002c841c4003900007081150440000d8590300030721b0b0004252540f6003c4103c603e809445012415008180140e55940042256218101700720340c05c14901007041006504000b102003980003680544401201d81301c810348031064002c10510020b0440d841c24107404d04207090001c2c09883c0035100b610001c14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 265510125 1250 265508875 265508879
    0x5060a0b0c030a03020d090c061107050901050d20061308010c05160f02040905060a020c060c0903030a0503070e040908030103020915030c12013209060c03060405041506030302010c09 80
    0x10140485041e609004019030520b0144031048000c0e5001c0440f6180a940f02c1441c000081e1030381c6a41c4000d001c0d00e440c1d01c01190303a031960007454800141c3c081449100d2441c010007258890203030709090f164022000860002c01000c0c060407540001c00303002d4110070009208225010041c0c4400d0a6450900091161046002c002c903018011510b0b041440748460381d80c0c400003403654992020342440908081081c5055849003410681d0841da500407560300050071016840050082561010240002e40d040411210102c0d0362401403a183d902403200020225103006e00445003070024850050090080d841d85140c070404c0742e0800c1c0b100724054801100071850110303841e080001c0c1d06001600500100b020041042420020b01b0089641956500000c107903108004801c1c0403024800d09010100151142146001000040452000303400003428401c1620008048a4112030200c034046800d84a50a10111003512841807190103440c18000008058064101034909001600c1d8801595 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 265511375 1250 265510125 265510139
    0x1060908010b0105181305040803160503221a07120b0108150103021309061508060904030c1211030c0d09080a02030309060706200c1002121302041e05060a 68
    0xb610072607100303021680034449440300d035003c1d2601c00c01e02000207028040c0f440c0000b03003803401c5500a59080c1d81104000003040b400c1d06082c02c100b9000502c9141036480c40c036100380303445d2044c80d1500e0700e0300030307807480d01508800c0c0054050b0a6140740d450004254181c101000d0203408170200c5503507802050f0510705603564646c01040207900c07400d080c018045049400c800114000d5010520412402007008800f064030f100902c03030140a85000d5032743e014800316200c40541440340007440d062088600303804210010382c4c0400b0010b10658410090031040c40e031010103684042d2001944400c80c40b0203d030754071007800300082000013141d0036160a81c81503169408140c40f440c01c0035001e90586d004018151031414420014904030f80511400103290310702c041c001c1058000039880c001d00b084085000303442c6490600c541c9145940c6440f085282400c0a881c0740d50400004101c040f140310040018811f54450f5081320032907a0340c960200c0030252081c188000280320944190b070150080400c080707141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 265512625 1250 265511375 265511381
    0x304060b0d030e10020304231903081209070302090405010504030f08093c07090b040614041d0d020a1103010e06060d0c0b04030305030402090a0501050609010c0212070e0106090801 79
    0x40798056039441c030b8200e40b031002c1c00500d0340102c0b05001188803c201c0041d0011182002c2a4180c020a42e140500a040d808101130180c618410702200501c0c02010400100900f04a50601070304287d401610790b103d0301d003282040540d61002c0e421140d0241080700f048810750000348507a00c69180c1a00c50002c0c80b600312824a000c407400640341e0302a600541c80c3d001040e80d0528104408858002c0300030030100342c90018925840708040e079501001c4140b0100800f80100b00b8041000c3c1c408115442ca842d17401c0142090002e2014040d0340d445035600700c802c50543c2c2d81442c0d402110701301d03650303d9401d64009507180d241341019500c1410701c405076055482c4c103010b2a54100c0003c001410192030f840108200d409103a54115100b003e402c00009130101b1100190000b1806921050340728071b45401840341050004003042016454440140919600c1e9403e0301c2d140714081c0ba2200004e05640701151248550000c00103076031280220006095003200c3c0c43c18140d5a00e9610100a50381d01c48000742a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 265513875 1250 265512625 265512649
    0x170c0c010e010501060203090409020a080d0305220c0905070e0a030c140f060d23040b0105090a0b0307030303020901030f050a091a0403020a0807080f0c0606030708030406140c030705030f0304060b 86
    0x6807c02c0050682500c0e0070741262210a000401d01c2c8100307543c1d0f820841c98401075203903590110741c5680802c00891003412103c085901c8100350b1003a400690303910415000700501880c90065600c60100302ea06201700302e619204100601038200f21a22030414400c0d0312000d11032846007000184204c907607400d02801e001386400014291908080b400960351003d40400248642c00c5440250303070f008088550054a4001d9004122001c0554100420302c06094402050710580908244441e0561f0324002003410440350146801038036841a0001240131304020f00c941c054082c101400d02401c00442d0b800991094450707403441801c02d030700c080200e00c1e1141c04c272005800b40c1c02c8400b02d140854000401030560603c11001c0614203a4000d1007041c582c0c02010310b60005a10080410105003002c004510242c503600005600706843d0050041c101d00c07004403c2c3c041c000020890301c52444007003054030006a03000c02501c0e1146007450111b0360030340049034107a0b1814205565042c07941015420152 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 265515125 1250 265513875 265513877
    0x9070e04150e010302120a021e100801051e011206090b030d080907090507170f1b03010f0b0c010207050703030c060b0901060e010c020f030609030d050114010504050d03170c0c010e01050106 83
    0x1c50f41c0c61a0200011420804c140020500400c0d8120005035100304011402a55007001c4549a5100700c4c03c2c8404a200100e100741408800e40062055030340e220107000207500c41d150b20446002008004a401503d4007040c0e1400d24200b50001c60030f660b503504104540d00040d02210b118441001c130032a1100d10650f40704a05400a51007406500b80c10340120354490030604006e24000740090301c00000030012a00341089a88080510a402e44030302d081500c000e40060016096504080e101c1c01e601c0f00504c60150009800122004031030020b40560742099004015900341c59540d06000e003049108540490f401b03440d0240380311181c174008442c94180c96143e540c6009180c03296005480985c40c807041640c0c042189815580d542c0d0303040018500c2422135601441c1c84015140404085e100103802403a80d45440c09002c450691707002d81560100d48085841c000e4440c82414280c5289100c43c1840c851008858100001061300d0001800000200d000800c00071214290781404c0701d6003030040300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 265516375 1250 265515125 265515149
    0xb090c100f0e0603010b040612050402103b09090307052802041a10030501080606190f090c0917070504050604020f180f0d05060c031509070e0415 64
    0x400c42a12595000e00c801c1041d0422000d0b4080940000705190005d070721000380110001000d100c0c035a40b1000d4480e11503501101800b941c1050390000d640410036241400402110680740e004002c03944000700f8200180303c0440940c50002c3e00d0403852160f071446160b000301c500c0c00c04104580000000c90701c040750010060800c8256100b40300030740700c0340b071004100096041c449a1002d646ca0344981c0500502d99000015102980c1052010f409503d00021040c1b41c0b5000040013680720215100350b00100c21240c0c040200001300c04090b00d0344041e00640780d4040079100100d0003d407954001c400c04440c9844e003070b041c9a40c41200d0719034018002c0705410b0a82114400b00607a092641002d900103200070b0015007009008451602e0f55002542001c015421150413107015081082d1044048501611502108007254a0b0a541d030080505020415032001001942e206400a00303208050402006d1141c41d09104800074624120058450310892a141e4242c0c0d914041034070358401c6802d444801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 265517625 1250 265516375 265516399
    0xd09060b121f0c140d050a0f11071707080d0501050306060405160f0905060d0f050612190309050a080c0a0806060102120708070206030c1201050402091c140f0a0b090c 73
    0x190014043c035800300e005018800c6403041c1a41840c1002d800412030412002602c1d20386200014242e0b0904000c8810940c500f4000b000343c451010b04441d56941c11140191307980b5400700079401c81e48160280684409000305241c118001e040d00180d0495104070b0440c1c5490b1202010042240c20580300300070b542e07054028109107540600c0007002c6c0d5020508048031003d50320740201c2d405500c4007042c10200c581c5d81c00e208804061912a003500080e065501d60403d5107809425030740c0c4c45c01c200000c1510130003040c48070300301880340002c00e025220240801142560342c01190b50745095628103070f4070420080102042c50503001034201d210305416402801e000741100011170305588103d800b511500001c200c02009030b21820011405030110b500c407540e44800300c40094500002c10703080148180c0c01000344000c15501d910340c2c015049a0b130078004009404600d460301e444580044003200368040c80011300d0b1200c0000c102d007140f0307601844000089a69408045480b200756144250340204c0380e41078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 265518875 1250 265517625 265517683
    0x1060f050403060c1e0e1507030f120b0612181b0f011806050c120c03030402040f0b040f0209010e04060b0a230319060b07020112020f0d09060b12 64
    0x21410b080500d500307191011000c1185c00800552107411a4000700b552034080112509020074503050100c5d41445c2d0380e0400c2020b41e03004084c80803401300c5a0402010804415081030190b0045411184c000c10aa03660b24150609031070305401202d41051002030511206400c240110b5031280102d5644801003903080310508100c0381341c1500380402e0410400c5060703107080030f80c1e24103030f400548502c3d118143c03a00900e40346586040d80c2110707645135180b800d01000850000000c01d50703130440c9d4102c03030120307001560241050060114800075540b00d4180503103412581c0c1103500500c1c481500b0703a108260302d00c0e19028802560040d00c2440c21030340007000343c040414400d09001c64000744141940d02c406601c14114407081e001912401c00c0c4032071106903e0f0300a078461060030000c119201002d0300304038103600042e10000441040e200d00710b40009171a440861018102c458030311415408010350002030030000c3c000c0408024960040c0030100ea4403080c4800012400b0a00c08444106180c240120708 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 265520125 1250 265518875 265518881
    0xc050d050a0221010f09050705030a0b0f1504140609100b0f07030201020702220f05220201120606030209090f09030d02090d0b010b280c0305090315010806010e01060f05040306 77
    0x103011190102c15084040416083c0140da040c0c03400d17913501003131401c5a8180702e4200740d007541c816442644038922450002c0c0e400c01c06640e0182054080400540d41c110302e000350b0501c151032680d486480c02034000301c81070700501e02d580101005e440d54481d564801e0045100c000c02d0b8082c41c0c0d45002c041c0080d5440107007050090044c0c91085c4005420702400341d010811101252180c0026100d82800314040b40f8039901c501010060070020a00082c20101c2c0030015003007106101c484200c40900d500c3d801e59000d2134074606030351501802044403c0d82c540008000303411821420b48078010f08000700d40300c81d08001000d030041401034050352400b8804c12445001754010181203802103005a001c0c804620981641802050300e003a0080e84e44c480c0102c142c409051020b140304103c0100c50b10341c000a648080040081a4036017407440e03a900b0200c000070301d08200002c5038840030410f040040380305c41001c00c1c0e89048a6400ba120800740e40c881c2d200395034070451092681d00058007480200045003c0b50 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 265521375 1250 265520125 265520149
    0x6120f02211009020403230312042603010b0703020c100918230402010206091506060703030f0203040602070506090718021b0d08060a0501140a05031b0706090c050d050a02 75
    0x21012584160303454500f402a60010750082c0d030311340a0960401e00d004400703540c00c04084040c00145181902641c80704500c2c031005000504802d408002c0c440042408596031400b03589001d034403903101d6941d00702800303031a4000c1808a00600400a413000c290820b07510700c084503d0962035581807903003411b01d005010501103c284050548900480f900103261213100c0721241500c40c90070a417480c2c00e00029141c000c0281134640c00354003800c9032143d03503854100c03190f40020049074580da0704c0d5103a0900701d000e0700030600c914000320700c00018801006215402049064031403c10381d5001d80d03808110a8841c00c180c0305840b20b5040d94030021050402c01d0740240044080c940031841e0800b003822420345400403104420001c10540018800240b03002048400140f0007480d10301f01002c203c500041071402405c151406015000c40031079454012981100150a440e1214039180c64040c140b440c00b41c480000180d96400f000780c80454941004d00c3e549100035040401032410000075401e01294040715 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 265522625 1250 265521375 265521391
    0x80d0e031c1b0b0109090b010e10090506011709030702040c140307030b01090308030403080901050c04060c0f020d05030c0d0801060504060c0b07030605060c07180507090e0c040504020406120f0221 86
    0x200c200710700020701d0f241d12203029101d007070b07800120952580f420540c10401a0010703003060b40e0280c10050100c14002d0007209541c2507c001043c26122440142c806c080c3d48107a0529201c654003c0010b448800805807030b402e80202c40501059030041e1301030354a204040d07030f40358100d441040000d1241f4042d80010b0000c1c0418981052029583e8446070308a41050710100d00040030f08040c049411300902071690000408080189898a0104003524440c0070304001040c06c0d061420103030a65440c14005410360381c02105036035551510b640340303079101d6a40c000d0b0800414844400800c00c148114151010340f204d81e140d0304421802da849050216000415000805484407400f0586440f45406000c2517200076005105450816104800502d62180900303020fa103040100101c15500245580031503910820061054580100103a40d81c0302d01d8000541180c00000c0000d88580e0101290b42171800e901000c00040302004c071440180d00c50603042d140e500c080000c0e60722800c0d1003c0f10382d035000005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 265523875 1250 265522625 265522667
    0x20607110a0605070e040b09092104080601240206040b01050405041518060515010e1905060708030403030b01020703080a210606111006080d0e0d0c080d0e031c 70
    0x80c1c1d98420b42a600111803001c0001c042826148040c202805040c80d03d80b03080340c03040d91528100d06880d5441d005650954801d503100c440044844501c0c0c01207801800b803e10680b41250f840d46960180c0115402071a07c0c003050781c02c03101c00000e101084141c05594048883c0005901e0b020030003018041c041d00c103a40310105441c04041054640c490b2043e8814241100483c40610303080010031203d0003400180b00c0480400f4614803a030780b00d082d04080050032589110340001c400d880d03410340f00180d003007290866800030b28070703080c04a40006580f20314841d6805128800c5108012070321034101c0d00c0700502a850074484210001d00807244100341c003000c20380381a419041c510164044e15215401301000c0380c1c40d0140b070704403d04e045c8841c1c8000d6551507000e118192501050641c0d5116240d80750040280d07c0c40c62801c1e65403510a82c070200c1c0d400c01044031065489162140c1c41c2c0083c4401240852000c1c450340810b4140030685100f82c0c0c564503d468001305802400b55112400e503140084210030b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 265525125 1250 265523875 265523893
    0x140405030618161410080c031f0306021615090b0c090f0a0e040c051002032203061a1219060e190309180608031c06080304141f02060711 60
    0x4a2100034038020300072665191002d8541006101003a004240205c0c02c00c440c04003008060a000300c1220340054280b00c0503080e101c2d000c061881d05008540000300098000034800a558080000c0245000d010b194140284451007006074111101564014183d201e26000200800c1051020f000d4aa501030440700c8045112030000e682e5090715008bc051000b024000c1c4820b10002d4400100508001d41d44003c00544551020350741e80603541c070180d29426688544038424800107800700003954000300601c8460030781c000f00f1100e851601074160150900e01e6065482080c0000c40182c0c07008001e84100d01c400841d200c14000e446090902861071003600031002d01d482c0348000300451390b030003541c490302914104441e03420501e0100400c04052401c101c010f102d4000040f00300c07075602100c481d41442e81c404510004001e840650f0051090f800085800500446500c040c00340b402411124031403043c1402000140f504001101c01d0700613840a40041c00710f03800758050b2041a0188000c56581c80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 265526375 1250 265525125 265525153
    0xa060f0305060a0b1c080c011803030e0c100e0405060301140c0315061c0209040e100b01080f01030f02060703021c110d02070819020112050c030106140405030618 71
    0x2a025401159030340d00000800c0201d61951040d41d100d010100d458007404080b001010b00b00704410302d009044090002000000850250f010381808070303003100051700350749003800d000e401400500c1c0c02c41018003859001e42e46a2a104a51544141642e1981920310b08803400348001400c00070501d0741c041d940c0700503124007207042e000000d102e070800b654901da4928015015a11030741d52800440d00991003440907424040001290000da041582d40c0161200740907030001b80502800003072070a59000320101c0ca15404d841da0001045041d003a210015152162b80390711480000074400600031f03401003101a001403410720018014280641304450700b0720a0000c600c0c4800b603190040b20b02140c250450b80075066028010f2404200b0540040c2510620f01041184c407105010400d2212911628861085a000d050503003d8040600d20411803441d0103115103a0340d500a02a84010039002c102141034080070300100d5040d038002070090700c2d503a212162006044128140d0303400c030f02c2c0220448500d0803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 265527625 1250 265526375 265526399
    0x50108032d1303050d05071a0403031e020a020f06010302030c090408040b030c0927060f0105070b040501150b070305090103020318030c0106090e0f1b010c0c12050c061903050a06 78
    0x80c40301e0108140c0d0b40c920310324041d450041084140400d02c0300510001011411407101c0028805001c000e21400d030350b85240840c0103000d0030401e03805400e68483d0854503181a540a0052250160200c0700858034154069944c0d0a00b4400258550300000d41440340b400c04a80d01d0381c205204064080c145516440c0118036600210b0380c03448006800300f01e0300c0c6a0318080850306000c02d08644040c0b02c403000d01d002100d824800811150040c88107991551040e4402d404a525a5420074003100160801d4604079000e8800e48007a070074102c040310700110380c81c0303a10ba0031192201e03490b841e21071904001d4401940a504001c00d098200441a54540480102071009051404040c000050f100e41000421400c03141020810346140d4081081103445c450f0000d01c00d181c407446e52003000310400ea418012039006410750401428080342010029006900c8000d640c04a03200e10240d484403029a424000140a1451500b5071030982d04001306406009501140c3c020500940c007141d669101e0b008140c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 265528875 1250 265527625 265527637
    0xd021606150b0405010e210115090606020d050318031c02071716031202091809070501021c03050402030c10170a060302030705150c1606080a050108032d 67
    0x3090348030725a021104030101e148402401c2e6400010741020705100008062807800300c0c8071400764204191010362101c15200c0f14a001604900921050110b09540007400a1138030134611950b0510700d02050880c0080b5030748102100d1540c0d0301e402c503601da90354514440005501305046000401016080341e40d507140e940480d4900d003030090381d900c3d030514111040e4a0304c02c071a85083c0710180305484010310300210b0140b0b91a01441c0c006580c15003424140d00a00c40d01390183e5220a81e495281d0a1341d0107900b50710301c00c007012010b0700c0c00c45a480c0016078580854038461060300c1020ba5013152880c1c003a80c0f04a400c41c3c006400c0b95901c52000011a000340c0170b00350890701003030846440d00704548010007843c1e03204226000600c02d50b813850b80803d030b4945440c002c061056111a01c106110400c0d2000e0341c0041030309400b2144903504148290204003c1c60141074002018800003880b15031180c01414100c60306103005610701159044e8008080c0035064602c580b001c10440000c2c0210041009800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 265530125 1250 265528875 265528883
    0xe061b0a03170a060609060c0804090603050a03110307020904060528150603061d1b120402041d07060e06070c0803030604150b04030320100f050a09080f0d0216 70
    0x1250b84402c460021954200410f03900083d0b05200003031103040d40c0004040119080c50030601050300d03023841c0ca0842c5000b19001502c040d03140034000020711500054010701c10f07000342c440d802c440311648a0181c481c41440d10203500045134202250020b04513038412984401d90654a10100d94034112001c0d42d451740d00c5080c88240e07200d2611040d80e8401e0004500181181d04003002080e10300550381c04281c0c1583c659601d201a42400505100f0760004084240040b440c502641c40340800d00c654208a4107460690003035160490924010400a10059003030300d0030001400043c1c50318000b1103200700c0300090544c20000511102002554100003c4041e111040180d501c924000b014802200d02c0344c4101e04150f2400c0c0c070100000e049100c1144d01f03036a09031821021101240406c441d559004024600c3d01d803040c001c800e9000d40c11544031501100c0225000c0c461a115004d1301d00684890f50000b404c0e0b240204181c1d0039100000b00104029103901e4405410300311510742c020b00200000320180d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 265531375 1250 265530125 265530137
    0x2040e030a09080c03070e1503031309050708070c0b060d030225150207030309150201020f07050d0305090313060c230d09081908070f02030706120f0c0e061b0a03 71
    0x110002c44240900c50006500350002e14070386d460000001d0950101400e01081900c154028221644050003141d11489005204060003680c50102c040144030899032140003480c00d40c04240e500348511a45c2200e2500003d40a032692224000c0100360091054214158454443d400b442601800c60b08107442c08000c0003c500940b818540311032600700c0080000854000710f1003400043e03041446070054901180221880e10340d4034609900a02c01c1c03103485c80211501040c3e42d005c12500140035000286c4940c0e06100984a4002e955038070701940b41c00c990781040643c17050041610405090440c680240c40c094a42541c0e0250400318441c40381d0700d180c00390803844100f1401070308180303804000e00c2a40001c0c1103002136007034030300c68040311100e00600c86a8001550340a01166800c1400c03030540080540300c0751740c5d454502500e44411000942c004508150010f1528070191040c0d0164400644030310303042001500421025a00c107a9035260001920070000001034401c07c0300d400b610344aa2105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 265532625 1250 265531375 265531379
    0xc1201020c012313140106140f030706051603030209060a02060105360603030d24050906030d110f0d120e0c030c010f02030405030f100c141602040e030a09 68
    0x81d8259400040b01c2804409142c012140740007495150b81c1e44405048030303a00040b60940b8040c030b01061203c44868240d0b080c00c41c00704407030290007803000034960111180190380100205040d1a48054030803c40801c00034002c0380d42c60b010aa0402603142e200349401442d001d40c400c00100150488503c2d440140e00002c0180110b08022aa41103015610350620391110303030400244550550107000a04070074200b0000c180035840030819034002400c1c2607030506c030840803202c11190b10120010310744692030617100700140c40d003490a8581e01a04024001c3c01e0444184c2100b40c2c0c1201e2903145207082403085400d880b0510001f0700030540c880980e5900c460f40d00c0c0d0200400c1d0b060780e115007101d032000d40041c8d410303200560b000119008100e500b800c1c50a03205201080a03030842c0110380c0840e406003da91142c01c0c0d4540017040c011035000144404114400100000308c51004840301800c1ba0840c08020400c1d003500800c1d10104110720052002c00d818806600050454001e00380400120300740c9102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 265533875 1250 265532625 265532647
    0x40b04080312070c0f080a0c060903020d122007050a0b0c030421020d03051911040e010f0506030c0702030106050a0936021306050a0b04060206010602010203010501090509090c120102 80
    0xc9a00082c544c5048a10710940d52100060560f9221004052074000104c041ca903501031608100540d402600070088a0300605000c0d440b03121048400000801c0d200e072600702d980c594419205034110380305600b0007261013552048074035802504190381c1d500c1444d10a10000300209081031184242d407a10907102d040c41e18020110360101840b514681c4902000380307030324036400035000c42d0721103440c80c000c00e417074440088400c0c172203114940e580d04442c10100b1907001180d0b648014130881d40072408100c441d03170b0790f001807046045250040d05d60007c003c20201c0c17103603c8014041e1034203e00042c0005010360ba43d40005884a4443e849803440d036413906150070081d82000c11030a040c0c04130000c0503205501942c0c0203084030010140091041100201c20890b540466020360003500c0050000d070006511442d40ba005034000340301e1384006115202c0041192841030003640d04032071040c1c4138500303085d062004000399100000c1a0405510504088820598900c4000381082c0721250006030358214281d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 265535125 1250 265533875 265533907
    0xa14031201080a0b0408030403030b030708030414120a0b0c120f0105010e010e030c010c0f0210031407020f030403140309030a03090f0e10030f050f060c040f2414040b040803 76
    0x448040c050700243c2900c0042407900074050341c030542c404052541c80e0b6651500768001d0110b0580c0580510800346c0100750403034004010410f40300403105003000000c4131000c1001c20b0000d01401803054101c02e500600042d48420741c41c0e00000703c0340409080200c6180d203c0a81d040032101c80d101a0060b400400055030400d10921460350300703103400c000081c00c0c00e001c40c0e540d181c80c00c0b841d03040002e10380e80c9200380182c8403180f001e4940d00030f0145d881440d105c00010047e04000110412585100000c00e0010b400000e80c0e00d110b010b101c2c007560803d841c50b101c400c01d540807000c044000b408200203604071a9000c1c4600781001e44070b51205ca0300ca60034181845080302164001c1c0005210030001c1c04141d000c078101c40c40c02c0340d520262540030300c0c0741494014203000000d03e00000310300c00c50090000002c114070140054401e9048800000d65480340d005101c4c26a41d1858981611182000c0200c0c034403440c0f4060355840c1d10064a490180e070703146101515071180d44040c600f504003003503400e81540808 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 265536375 1250 265535125 265535129
    0xd0f080109050708010513060801050a090b0c040f0e0604091b0305011a010801091d07120204180b0a0e01110412060e060118020a030b040f0203070e0301110d0506030a14031201 77
    0x20700c1c1000b80d031411000291205034180141c1e03102d254141d00c1807075442e4450b04124040e1191100900c12410160060350291484090850702920090001a0036004e10f0b010b60b0200c0301d900a503030010300c1c41c00c2c00d410500c84d405801c16800944458040c0007082d10074100343e001c00203488080030700c1455400d0407400c681e0198440070b8444254459a00541c1c3d011040b2815036101d2540090800040c45991b8162000000051040e010740800001c42004002c50701d210940243c50a000015484070051455444200c1c02003280d54500080342901030594003220040c0c0402d000002c0030326141e016400160050b5101c40c082d001d501040c3c00c01c00002d80243c050030031401c8028174a035410048650480700c08050310850f0103a000c02d19251341c42c4203070807420347c00034060400c014003284081082c2c0650700440d508000b08003004e61100140c141441030488800f000701d62503051400c10380344440540000b0f0955036040c070815249002050200385080b0034010040300030750741d074006540c60b40c603100016 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 265537625 1250 265536375 265536389
    0x201050d091a0f100e0a0f0c081005040203010b1602120609030a02011b080601143714030a110c0d020703020306070c03090b0a0201090c0b0301050f060403020604060c050307050d0f0801 81
    0x83c80c18005902c10000d00b01055803410140c5900603920070409100900d82500c034410140d04164007214500d402c00705240c0500308181c00100140c1e210030500060348020b00c50103986a4080003140841400615000c101507c000c100e40ea03448503c0c5040d6103001000d03102c2101a4000241c0303098160b03024401c40c0c0b5144190080000d03800c914900c05080110000c00307007810700103000070182b100c10a410440752104a0303110700340f00450000c0c60308040340142602403c040c1d03e1075081062110702940360b00c02000d8850140910319981da0240c800544202a100594010f042c000d80309015420300c2415007000b1203600404040d03203980105031406001416132024007160580e0500404d600c12842c205a86844d95403664500c403070074003240100402440500381038103140011600580d19001107048034012601c0f00c83d41540e94040180601c581c1c84002d5000400300300404c89180034481c00c0e49024018003d690410601c2e0703c0e09801c0c8004a01c1a100040324a502001555045007a1a0240900c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 265538875 1250 265537625 265537651
    0x90608010902030a1e0f030e130b2d0402071a07110a0305090d0803041412280e060d020304060501062a02031002070309090629070201050d091a 63
    0x780c0d4010903100d00507007a000d02031565000f00403840182d080700c00303030020b030340041b102070140f0fa103040082c4008d030b11040d0184281100c0618a280324518000c50962440c010140c1820300b21510a2012540301c0c10155a03205180340049042c940d217610181c40400c0c0901b521141e00c01000609540180c4024144800c0c00b4504252200601d40020303408001c540c103003409540c0d0355408002030610700f09018000c0540700000100b2003041a41d880d880811803074181107a0031950441d200900c03c0c007589074003c600585100304d084034003220400c0d42888114600344800401d0240d030100e01107074000011020b00980010a010400c20706200c0c075401003440f86406469030128607800f8404031501100151410b09044181c07040d5607040c0104911100c404101f190384a44a14000e4030807940c40c411104524581840020028a00705c25030000b82007808065113031401c0703140e03c1500c68208101c2a41088420b010503401f0b1205889170407805402240403900a410326003031511000c2d4020508041c00e10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 265540125 1250 265538875 265538891
    0xf07170f0703050f0d050c0a030f0506012f030304030f0f090515342a1703070611190914040e030708072102010204290904050a02030109060801 63
    0x38842050360840d0354035140680d524620001107484a004541c038003441c031442c080a1003140580303003000748112041900c0c11300c250104414828100c0b2001c131001804607045500d20348000310030511080340069400203849004400c00b61040c40d40c2c0044038100c010a90041d807410f00f59800c0110198110700c9494240092810b0101050342488400c215600700c0d0b2012441d2b043c02c41e00c0e0008050b401c805008110381c40c240c18100035034031605180d4180c1d480400458268440d06800d1500c04084a0800700e0381d02044c45d0601d1601d480e4035a80000d5041d010603c65240000e0090048040c801c090f00c0c40140ca80000201402540e41c2840c440030621425a000704201c9041c0d616001c20404c08480001d050340300807482c00d0941c0b05070701c3c000384240b0300000c1c3c00e02000a07445d041414440224951a000c0b024050140d080f44218090580c82c2007144441c0c120396811700841034044000401481c0c14140130002080c03e0f502d06845403107200307030044018000c1d000360340308040080000e40020300c80c80b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 265541375 1250 265540125 265540147
    0x30306010c1e05100506040608060f0c220305030a03050f040302070b0306180a020c010509030705190804030f0507060807021b1003090f03030c18030209060f12030f0717 74
    0x22900d900000d00700c01c2c00e007a0b526081040462150540c0fa0040700ba6418001066468001400304a540d244654038044022444030f600003003583c81000300400c2d42100b5150340c00c40802507040504503a00c0c08031642c00c0014041c250402080003588901b0003941c50304040c910140c1500c1004114604901c10f50b0101b101182c0c0c0025001c00308d810500303600b96603403503000c0450b0200707425000d02c85042210748140b0500f0340f015401400d00300c00c0d1400802060322a00d02c40d0b51644201440a0100d6003e80f508100c0c00c001140030862181c0b080343c109150542d6581c07062b10302d00c0d403180b003a102da42180000300322464000c11800d52003c203030300c040d00414440540745240c0c14081c00703035140504540b4a415801a000e6441015240c1e00200e594600d4180303450020007070310f50310034080300040e41d00d90802c90081d080074414042d00d41c0200562055034440090040c911210340c0c09540c040e19202c13001e694020140024840c4804014002d41e90711050b06150040403203000b00301e0b076440020000c50643d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 265542625 1250 265541375 265541387
    0x72a030f03120e03030a090c0801020f07050118020604091104030f050c0f121b030c030102070f110105090a06030c1e0f02070e09340b090111010507021c05251403030601 74
    0x1c01103000100800c0d01e023002000c91b00c246e00a58503941c40040d154243c010540007510b11144100020701c2413550300000c8001e003065a0000940248040c01306001d14005600800320300902e01011900b0942d072a102c50025000c610002e4606401000c2400284d0916038044100c500041c0e48007860301580090550340c03003181c08014040c00d070f03d00c141c141c0555403c0c03054449840d0000e00954491446051203c90b018101d0000c895403450b4000ca40c41da540a9400c0c2e07018100d00518907280702c0d00e049410380181c06140300070020440740c25034100903c490ac0d49420a2498a980c44401c0e00381c940c840640ba11070f081e003214076601202d8040084403407001407407064019083c01e1010364a408401c801e607200c0882e041c0c0f0540308411800118507810544044c2c80007900c26070301e242d960362a4003040341c00c98000792807030001604148011b40e0141044062142003e40b1071405078503040b078407002c5036540d010f042c2240c4004108003116105003d92002b8900c181d180c81c001461450a186002800e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 265543875 1250 265542625 265542631
    0xb091e030622021003050118090f02010302250501020a020f03070c12050f030307050d060909030e09061c0501053c130501150503071a072a030f03120e0303 68
    0x19003505802e0211011001d140c10011440e8041d08208981c0d045030300140140109000798120310100b00403d4440d01d1490240c9030b0000d03001951300850502c2a0011000796006044d501e10401150445240c01c1022541000b8541d000b070000588405400070000c0c100410484203885507403040c0b0890001c2200c0007584c42c2103403100e10107039401109501d01700b03040c9061090b5081c1700d4000442080600f176040030007041d44100040007084481e881d0701d9048100d4401c1900a00004d024a86800c0346003802c0079a2038200b00004d00c1c4091180e1074401d03038200c0e1902d0b000221901c0c0d4445040c044000d04091094000d10030044200791101d81e42c64050041e103262082c1015154100d01c04100004070f00341d2410441601b00b002400640c5281030514080007031885098001e00c500d01001461009a2100250040303508001034500680d41d1142c0810180e9084032025114813410000090744001e102e40004602c42c1600309682403250401620481d041c1c4880301d2014103100c40e00e500a41c011045985c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 265545125 1250 265543875 265543891
    0x3060a0e010f060b1603020705060a02060a050612060a050a0f06060c1e020904030507031b050c0307050102070605120414070303080a050a05040b060402030411121510050105040501051b070b091e0306 87
    0x1c071171902818100c0c0f07030103020ba001942040c0000740c80040b6590105040780301e13080403034041c003140d1030314020b004081124551701102c41d00314a001c1000d51240e50012070b005a01c0b6000415030711902c066140031900d05510140c0810301d034541c51410824000c1c03102e40e0307100f03030000c81e02c00b10009038011030300300d2034010401410004000342000030117002d5104510351034142d07680483c40e0100c9140c45030f0f449a00009191003441842000a8039620005000c401d0300c800e9031701e25040001d0a001483d481070081c2080319030050704030030404843c2040041100a500994920704070f81000781c92101101c2020b0060701c1101e09017801c020204031860911600700d1815200103942e66039600308401804200801c0690040c3c0010031070180c0b4030300040b40c9501c3c00900c0000d072595200d03543c925000c281a40b05141c04508e003413004102543c0250b0180800fa0a00807001d0440310420807001c0c10400b240e001410814004546c608442c18000062003900492501c9488030100c0c001c0040e6580780004d01400f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 265546375 1250 265545125 265545157
    0x9010b070b010f14060d020409090818040b03030d090212120307091a04050120060702031908310c06050a110d080103140106030203031908160801030605041103060a0e010f060b 77
    0x6103806a003031f4102c400a207a05802081800114600650030380d00c5403441010340b00d01007140c082d1070300c1c1030b228950b00000011700031403170000062061005050f0b514020381c0d103c440d00f1600d0001c40070078441915864000102c85a8034078221300054030707501e0150015486881e00010030000308440c0c00440c2c00f602c40908001010301200d00381010314055031010b01d501c1c1e000d00010301c005590000301511080032101540c20140c03c00c18821903e03c0c104a5901c0740426045c1c41072440701c0508005404661b164440c0c0d031442041d10b4a0f103c11091140e442200000c000180010450380c0c4007200c0c205607888003019101000700d180c4010502072040c040503080d510715881d030315500a4254000e1004560107015640ca4010522054404043e4504401d0202d4089400516000045400841c0c0c9403210f403103115030399081d512030200500005000325585ea090009664180d44c04000d254400c10841030b010030498003040c84a402c0d40c131050f11a282090030b00000b03001061201d0203455004400345148 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 265547625 1250 265546375 265546387
    0x40b1e04090f150c110706140f07032c030712060902030610050906040c081f0f03081e0a0206040305070614090604150501050307050f0a03060204171b0f01030213030209010b070b010f1406 82
    0x21030024480c80d0f615409e40c0200151480815402c011610b2007150800404100a000c610402c01084c00c10b0240a038036403c0000107000021110780001170301b6000380c41c00586119260701003850410f00f641d400800c10007010040100346000300314180d200c00c003990284042c968160340507001c581c001d45039041c3c6001d1140304074050580900443d004007100400c0c10b103142e07903a0030868250343c0500d42580f14180807080450402070428112400c80c00250300070702e40359a84d42c900319a95000304504465030750f144d960510b10f40000441481c050811007002d03040034206442c0901c581c00b40010400c01c52802c000040015540105988044910503030395a10b050b10200c00103056882540c0005018030310218001c40d0314844400111048541d20040300c0c0c07514500c8544c11503144132008403039800a01d800c4140ca640d4801d4018020307602c00c003410001415140d1340000ea40100c2600321240c100c0b00400c1c0c1c1c1080c840b0b806422801003891380311611285003007031100b0005160381000e05020780800604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 265548875 1250 265547625 265547657
    0x10209010503071d0402210901060b0423031506041a01090b0c0a0b0106030b1302130506090d02100305061003060308070f140d03020a0806040b1e04090f150c110706 72
    0x100c1008800c020b00856503001f520b01c0520707807030300c015052482d90845030000440c52101445100180c421100c6c82c40d0034240740c40484c0144980149461242d120788506203001618100300810720f00705548400c9120385130050500007113034008201500b00707190f00c1c110405545d8106250000392111450b230183e81e2080c2600c001d01c0c111185400804118610000017400c540c5680282541c4c01d0071903c0164420040650078143d0103401001d106401f401d0004004910b08007004000e103100140418100745020303000542002c0d005a45980401e44a01c10402c10b441d20f41e40d50f84907480340382001c000c41419a2110181d90058000c020440380d440200101444805505041401ca0340f10442e0300041441034000c000c1d41001c90303507002081445002c07428900d07017030180c450f003480c010b041c0b103140d000d042d490103c2492944040d1500150386407040c5c004a0f02803d40b1141c400d0180c0314410840401e5466142100c00d400c1c10070b020050141700c01c1044460109070842254403503c3d1400580c0041c0d20 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 265550125 1250 265548875 265548917
    0x512060915060c0a030e010504080d0e18040b0703060f0e040f02041506090e0a0522060b062a0f03070b091203070c05100c02070b0706060e010e0a0506010201020901050307 75
    0x3082e038084804109a183e488001920980f814070030359070809030007800741c010b455900460007428010b400c82c0104000c0d030791240000504807030300280b010840c810009010414010283c4040d52140c48800070081032940500a400050030959040c1c2c490310f2030209002c40f41c500c0900f00400d003403d92001c9806540d0b032504203824400c140c8250140c917540d50440682051102d100306420003c01000044c00c0c2c181501c2058840c0322441001c0c10151280514510b074182c0602048407a182d450300404401e441d100003829500c40110300d0300006804004c00305240b000b10110b828035035403081741d0740710785010044141d40c106984802500c00341e4540d80100ea003000340f9196140000c6c0408010081c000750302284140000780650143c920385034541d0300c01010340d0490400f68015078170514040140500c018000c0421a004080001e1290b44400500c9100340081c2d1006010b072011200703102c504a0644503039500490240003c41c0703440c030241c1c0040c007180802401602440103582d00c00f140b24007210303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 265551375 1250 265550125 265550161
    0x904020912030403031101090b04021003060b0c030a0207050901060203040506070602071203091b0803040605310501020d0903030c08030406090501110d06061b121e0206070e0105120609 81
    0x81c00c20707951038503007004140e4940240c4801d40c000303042119040001c16062149042c00398204022400b16929a020301c852203000a522104140ea180c6001071018141009404008208800355179a611000d2000b40340c190030350401881028440010030015070000100ca040305e0007600d5403038581c15076003000030081c090148044c03c0c030f51a182030b1900480c0d02d03500504415106a820440c02d0f00b00041e03840ca80140383c0a007449076401040180001c90080001d020401049403209424080321044c0c80146008546d00e101036042d02e02040c032042d80c0512a204902c1c1c01d034076003802450b1964800502c0085044005007401800101050510043c0c1e00161a03135500f2400a000c244a124031012040d80481e280c107445602d821b0000c1000c5210f0340701642803d01e00c054100003014a9211010340c140160142d07800d2009d85204003852200101700310303c00d0500da40240016142c5020040c015000c03c1010504000d01000040822076070031000641090081e940f54803143c1d5080c9161814130100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 265552625 1250 265551375 265551379
    0x6070e12030313031b050c0108150a0308030a05010e220303180308040507060c020f04050a0b10090e340509040207050615010c0b01030611070f1a06031c0509040209 72
    0x4100c194900d90403400c072014401d50790304103003c2c641c10542280d03485c0410010001d801003d426116988584d68a941189001030005043c1c0444000107480011a60080b07c055002108020400c1c0240c4511801402450289031103031422508980c1007175000e0740d000e91840b13080d890280c00d1521035070040c0d550034801e802c0481e2a10b40c0d8140600360440440d407c0346d151084040c081052441840d04007a19603014107da44502404001c0101502004090741c05040d6141252100355a904110f1b40759050247c4801003503600b803a045081002000345907090490810340b100a030600310250180f010f1079803503100200001044000ca03414031400c0c0d00194014004114002030120115840340245503c000501107120940015614844500409084091982c004101064894000d0041c511a0382d00807480c0c885140d4800302541024001034460503460300104428410111010b6003113a400c600174401d414031580781000c90707680d840005081180101d0201000e490355016030b0444000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 265553875 1250 265552625 265552627
    0x501050904170d020c03030a0627020f07020303040b0c010e0105070f050d0e06011e0503060103020109170708370503030a0b04021c0c140705070b0a0c06050403020706140c06070e1203 80
    0xa05c51343e0319030360703002a104c2c0034810389407000011f40b804c5000e00b420210400ca00202c4000305107002e02c000250000b201207955100c0402003540169010700040000e403503c642c0b5951218255502c40f421200300d0f602d1458907030314000500800c0744e0010070f402900c41040c6051556054070780c2484000d020100c81d2412688034440c004101c0c4a030940c420380000400c40b5100e4a802d0ba03c404055551400380300103070100300903c0003800745002000c0e04400241c4d000742190049559140c00710314200c6152012415140203010323608a5881c0514800b01d071003070300980310160102c02d4075090303200d01c809000204580d075035041c10075240d05c4079019070349128118200ca40298608203016800350910a61001c001160300582d00e4118003c001600c0700c0e035800030001e00c010790500004207440d07803224070241c09014008a000001a1080c065144524400e80c080d044452074a0b00107030648603070010381c03c547c000905c0000428900003c030b036a0f2001c000e2404902074454400411441c8802400d18492400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 265555125 1250 265553875 265553887
    0x4050c070b01030c05040e16050f03032704050108010b031f090516081c0203270603090a06050705090904120e060310062c0f0a0b1605010b040501050904170d02 70
    0x38081c000c4c0484100342d030113010481113080c60f59115005450002d415540401061055003040b11400e2116100941200e1030318017041100400d24502030140e800805074000000c64605043c0602c5005104c050002d20000d490b520000303803200844112003182801c000e90300728550b082c81d00b1803c000c1d60498280d58000d0140c0355907561030744280c01004070610454a10710f000a6995000c40c004210035809542803580a1141150800404170307008014141a2003d01855030303005c0056000b44038510041c41040341c0c500c0c10710103843e8004c0c0010140201840200381035110680c0f00b0340d01c294492002c0343c080ba10782d04d05585807540181141e41004001c000c2200c5c0480c40741060f41520b00645070259409494a40e41ea240400c04d00814024141d070320004031a0b040c204150389880e04001c040b10310f000e86030041b0342d00c41e0f000510b19903200034000382c1400502a080c0704003201e1f00411b076818011503040038045034002c0c1c0301800080a04080c0f04c1c0d00018014544142c1c1c0002c40c0c00103003550707150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 265556375 1250 265555125 265555133
    0xd1e020f040c030b0a0e07201509010e1c05090607020418140f0307020a060e01110d030609050105090f04080304030c0803043f180302030d2d080604050c070b0103 71
    0x1c0c4d15001c050040c0c02c64800400c114400d808018882c566658500103241d040040451100410308039012291081c050422070003d965007190748110314140001a41076950a48546042500d41c00702c8564041c00d20303030160701076201e000c80308400c0b03059520f10342d905e40c5440410000d0040e404049003061038500d08004104011400c45030f008a601c0c00c4540c0f1b0844440d401386c580c0304002d00254800740302c2c80e0411007070303000301280d501000050602040010300207030004d0500311604c000800181c0d64140a0009800521a06000d804242c0d5001c0080ca00300411201c2500c0140000e80f91003404400107003003501c903c10310703a40c181d4020707201c80d2a401c0034a043c006454428682103001e03000e24100742090074801d80030788040248100c203080c040b92098410b44e0311000c40d940041029203828004070140e202040f41007092241c0c1c0d40c90405602d40301401c00b185c80550715405045031818010140401d620040840c0c004008a900103075648402007014252b100d9180000d003c1403a07500008180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 265557625 1250 265556375 265556381
    0x3060903030b0a14090f061926030408030a14040f030b010302010e0405060f0f010207330f0509010f0306030203060a0501030b09030702091308121503010b0d1e020f040c03 75
    0xc2e002915044070058075800b0a005140c0454005508100395200203581c2410500c50141c00800150484550100204d004952484181c004454407170160303601d50300000701c68528a03c0c0b4545480903608050420544684912481000000b04129076110008104171801110f004200400340700b00c100d036030303071074605040c000921041e0702140f0001558a410704007405401e02c2540300070195200d201c80002044010020007400318110f108001c400b1a5035403081c030007281d040b0b5544c48208102416003105010080300440700e581000080d010400341c1a421105561600009081c4058000400b140840003000b495001039450b1181d0814413405510641c130a60607680a01d40551090b0340766542c5030f58904c120b95000350000741100001c2d00401c010540403d055115000700d81c03525443d0312350316941e00c074241c4000307510041007156249245824132401c0d0000030140c5802456140750348a40c0065103e0800e01d800d6120075141a904541e50a1200055650001c0040203002c107109402070003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 265558875 1250 265557625 265557641
    0x30411101106221205090d05010e0c0604050102100f0207120c1b0503031803030f03040507151404090b010207080f0c0a14030a080d090501060303051c1103150102070306090303 77
    0x241d8064100451800b001c00140050b0140310f00300804428102c60b61031060209107032942008112084c4000c0c40300f5902c039030030903118a0140380003146010265545c1410000001c1c4001e101d960100420052640c010602c808c10b040007180018580400c40c000e80c1c0a440b41c0d510040c1800200007d500f62980c20200308400c0030700403900340ca0640801191406181918011142d060740f003070042c1070300084407040c00301400d01d01406503410088111074055180e0810740d0116600d801c464070902020f16035260b42022103000e440c01000100403240d07603008510481c01444503081e259200b46825900822068008144a5045502d54000000c05c1d940301e86003501160b1042513b56400030303c40713500200e46002c400004001c0c0c0020001540ca40019902461180050325100c600800100e6003e10440d030040d4000d885096440000503210212451402c841c0304171586041042c4076070700d258009890780700d00d01e19101e520508902d00140e2401640d4cd200420b914100407501d42010351642000b01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 265560125 1250 265558875 265558907
    0x5190605010312020a080f130b070c0510050a08010e07020a0f0b07030b031b061b060103030e01080708160e045408030c0904180224090603041110 64
    0x341e40e1903140300483e1155081e00c1d004c6d114010074451860700014220007010542118054a90455070310310b00c504003034000308025611020558810809402e129aa07284114850300c0c0c09468100440c8000d031079030b40d0602441c40c0b06d006c04400112200e000f0851040800e13003181000900c1c2ca004d141c030381d007800b104483c01c4000900740141140784d8240010008652003e002c06d6500026210090003150b8010010604d840d0b009640000d144100502099010b14040c0c2d4030f10040d940401c00240c8240d1001d1b1591080000d014208044080c505041180c8403026282100b185461344001074040e228440700c10013803004008006442c0d034000298007000c04501c06d0030103a1480200103a01000302c84c5580c281c640a205616000042c110380e00651b882306010602c00d0910744400d010404417100c000700003184210140e915019031800316031780c40c00c1025280b0806401c0c1d10740308500c6c04900031489240d01480c0c000c400305040180d9141c0c2980d15280241c40070b030540c01c1e060b100401c803121945143d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 265561375 1250 265560125 265560143
    0x70609120306080706021b01020a080c060406110f07260d09290708250c0c0e011a0705030405041119020c0105090105070201030f05190509060105010813051906050103 73
    0x60f020b5001c50102c0032070300e094006e00303161a02d0180340681c07112100442411401120302c107100280c6910041c01c0c1d0f90000e10001c100340e103418900341003200c20289058500d100140541030134014104105c07002305a105980f056038005209028084c0c00700d10352070500e240c8010030762111485070359002c80d40c0d56000da42c1c0c410820305200c03d002c90340341490043d001e400c40b1103800102c10034001c5901940024124160325001c441001841450010310074090780051400d003107000c02c0c01000815080540a2942e60490039450880307010900e09203009405c81c41c030008901e2200b400300070320503107004080240083c04040c11004444090f9800b04a010510905100b5480e042920025541d162340b24180c4510b490003091100540310354100a100b02d04168948102c100c1007a41e03809000c1c02402d103800b00a0301290458078050a50340c005014070a9a4070540c01004141c0e03001170280e401c111090001b0028045605045d41005103100480403949a4045020104040307a030040e412680140814 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 265562625 1250 265561375 265561379
    0x18120a0b0a0504111509130e010c1d0d0f020409110312030609010b0c0138040b0303040b031801110a08060907080a050705130314010c0801031511070609120306 70
    0xd0790840340196800303404144a030040e40218105140000f25006082c0100341c28142c074a00050405410154030f24622911031404007100b40d424005c0407c1030001d401c02062540c4d0080a0514150180080600c140e030304014203001d11541903214110960064028000341640342800c0590038005d6064a0191081864603907105502d1001c0d41d004410040002c5826440d101c0103880301e40051000d15001c0d5602c0c1000e6a486030b06220f0349030003101c0c00d032501220b1002401000d454009142c5120f02550800340d903580180d4001c400c49065075000c845842d00c0340c44690f0300349007030a11200641c0c0c4c0c3e0341c0303402c81091000c000c5201815249005603100e41791341d84c0b46814480c200300c0c191b031a00c011407001e50220b10421419000140e01582030f282c03182c01c01c0f00c017002600542075250700c10340750400130f02880c400004d420f0150511294090078031b0f41c000d51550f0351744c10b40800075400c003041d500d0b543d400001c24000200202d801d0304c2d8025038184200003080c18144600340c2c0c1c0c1049400424503080d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 265563875 1250 265562625 265562641
    0x150207051203010f14011e081f030b06061b03040b0904060f0803030406091419060c2c01020c0a090b0f0901060215150306040804030605070804020f0618120a0b 70
    0x100d0381130307407042000310501c03d15040c1780c2d4a5644a6802541c1801070071190400003110003c0316650f01c01b5140d0b95000d0a0410a02c81c40060030704010622585416400500201e140304014582200054034403903510401080a00c82c080030810300b00160707000c00280050321108043c0030b00402d000440f001c000c0980d50340103468810241d03220702d0350181c00900c0054080340640e40b10350110f5000d461a071a01c210f640c1602410a9905042e90045008280700102404650721a001c82e600a07824600c1c02035035802c443c0b814482c10f400c0030654424a04a0207041a4424085208990006017a1208070790302c1d951420094114601c3e4607000d440c5080c003100043ca08805014129000c40c0c014181c020340a80900740d2078100102405100c44040900f02c009490400c203051095026141c8661164150701e440350030740e0000342c851010012250280000f50780c0364010004036460843d1400d66452450b40303010369a441e89000140e1040c4a0000710901c0c1d000800c10108680c4038056a0420782e0724512 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 265565125 1250 265563875 265563877
    0xc10020403320d050a030e010b010c0830041e111903080f030601022a0603090c0d0302030a14040e0c0901020708030d060509070f08070302161502070512 67
    0x70014104008189012940800360115001141500b06104000804001d44249404078600700c00c80040c900144070510b681c1c0c903105081c444041d60000b40400d15014000a050101c80640a0030300c41c000134000c000d219101500b448405800e10662400e0120851500c0702e14a04a800390340d101766043c5078885a00154140940e2258040c0c505140c904008040c03101003004208141128440e01c00d010020800c0f0001a00c440008001000d903240703403503c002401c1c810f1024800c030701000f0140328111100510305031500c1003041030f03524a072240e80740d51130030749004007440405170000b0b8075a55400515070301000500c459441903c030402800070011000c003182c800c5100717040031000c0c480701040f140c140714001003045030760503c11103150a80300d5880300d04551110100c48201a81c0ba001080941001c0f003450b1307440480345c10055501e072020400600742c0074000b42035030101079000a0a2100001d0308038074641c01034001c00c0556401e072280c0b02400003540702800a9178584510924a110b207500c100c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 265566375 1250 265565125 265565129
    0x30b0f04030807050a020a1502030402040e161509031a0603070f0b0301210c060c110103020403020609090a151d011212030209030102070f0b04120806010c030c0c17030c100204 77
    0x50750310740855030f603c1d4007110180c100701c4450045010380545040410b0f142c180c5448140340202d00141e5904040c810001100c08080004201d608450814101600000443c1088819001cac01c40040c240d444070458100780c1580000705800f010404c002645d60408003c20300c03840c01a400c58110988a04084541c05000d201e1042e0030319040006004001d0351066840032080413034142c03000b0002c04d55030751464000c1500706100040c1c12281610903c10100c00054151500303013403c503e070030f0550300800d80d0792080d41e4401d4041c0c800c290100e0321105560748246107840d10b0110307400302151180c00a901c8402c00e40b010900c002d6403100040381c12000e44400c0c802c9954050a640d040404115099029400c241000c9034107550034040440814075003c41381081c684103610b810590f1070280b416030803200c014040a41046406c100300000c40e41c101c2d141500460305030030003511360f0823b440e00360148089600480c052009464000c0c05407a400005090042245c0c9c0a0b15032903103a017180541203000d98 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 265567625 1250 265566375 265566377
    0xa03110306031f020403050d050a090605070803040201030b0a080303070f03140c12070302041206020405101403221b080d080405030f030a09020d1511070503090906011e0306030b0f0403 81
    0xf0341c0300c9500300c08000c420361803268034521003d030809540e615658100b800503003c0c1d41c0840c40c00a0900d091030f5015008001804060504504000036038a80d02082d00008000034141580c80d8521065a0742d51018400208107104c126956490070f00001400104001d000c54086424003104c0707450304084451080c413480a18030000d040c042d00c01c08448511001510105c1490340c02c20020803000c80c00038618042c80c1c001d600142c0d8440c640814840000403002c401c9081001211200d41c80d02041012640c000c03655060a1480c02c5d000700c01e96103088481500140b100302205a80d10000744800204011034480c107090343c2e0480028a4181c030080c40c1100c2c018619002005a400781d11036541c0a10f030001c0c115000020240c000e607000c079a144002582c00d0314450000d1403411400074003070042e8100c201a640d1460700b44449070391001c2e580d00038a10254850000400064682e910846010700e0307884078549401000951b0705030141c001e01240c0001c0e00c44440c60300000f2a500344410282d4042c07541 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 265568875 1250 265567625 265567633
    0xb090a08120f03072007050a060503190b0310020d05010f0b040b25020306090a1205043b04080a021507121a0a030317011202030a031b080403080a0311030603 69
    0x64076020500583c0010b2044c0305008012a141040c280d10038455074849440400a110f010300340010001c0306100340d070081302004410401c001110f900312500f010050020b01000c100b140702100040c4c00c0a2401806840081c07001c500900d4040094010904a03201c00c0820009640c48841e50035907445a4058484040001c1107421085041d102d465003403295044400b2506c018150b000030f050020982d0f2800040e4480c1c035408050015503d102c2031000031a041c030500c1e1510308100700c24508100c140603041c0800301c040403400b2003150f1700e0801c81c2c1144060700320400c1c0307054580507506400081030800144504041240c6580750156014061516030300c4003402540030125a402074544540814107113801070201c078800c3d8842180c040b0245210743c6881c0b046800120410f8500e4030141d20540350004012503110141c0c50100da00c4040541616240c41000f4400c105240e0303070340f600c140c000d005400000d400018004205c026001400c141d035000e0240c290990310400e06400305640003941604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 265570125 1250 265568875 265568887
    0x603020901050f0c1018030206180a03110f030309280b180c031e06090d0807140c0d050403110117240a090618020403051b0315010b090a0812 62
    0x104403000740040010b807908440300d4012941c1d240d0240c86c41c040054060880c510240c00401d5010711440364000010300c0c4801000c405101400c1e076491640f5000f030300384001d41c014264400700a010b181c00c14129107044903a41e09101030102ea68820ba00140100b20002500822080880000a400c15904000308030760713030745800c032810040c000401581c40440c4030311000207d860301c05100d8442901e1150b0703e0355170704060104100e410090300819850158001008404040350405032641d0010083d15062051174022114103510b481400d0902c4202d00c103841080546950080050058030300c181d298a49075000b44005641100e144001c42c03590412450011700c40408114054035508429494403000380003000c00302d0107610654000c1c44096441b0181804110b1000c1c0138100801c140700000c501e800c0c41d545409485281988244034081103020700b41d0202c3c0d8003002882444c010741c030b041700c2c1c04d075940e40035030485580300e91480e50240780040c0001903154000315510442002e854000c2c0d01d008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 265571375 1250 265570125 265570147
    0xd120605101409031605040f0506100509010207170123091c02010b0405040f020406050616170d020c0c27130c0305060f04030318050a0308091212040c060302090105 72
    0xa8000107002c90228050240c4222903404101841561605140c5806401c2c104000d0106550503518160a550f04000c2032003103903256038181076510121450001e44507074052004030f04066403a030004a0b41509541c9603105102c040d4440402c110b050304e114090700c0c44031014a0034801044461062640045011009103281d1301081d042030280c40c03000041484008001400300c1f602a18290341500d0000900d1085061610800000d8a0200c0700380c0d050414103d201c400145035648000c0030801d18030558021300e045403060380c0c00b1300d14000056444e4455196a00d5a0f048030101d010b108540780c018620440250f00520400c0c26070360540c0000c15a60720400c00345048400c4400c4440d0300a08900201082051040c1e90040c0104042d60501d0304240c217006041e81e0018200302c5040e60581c1001001030400210186003035414181007100b0383d0340415242c01c002e01e003c441000c030500003800c04500c141c4200f900d0b00c140d10035240b031005252540c1c03040702240944214680800c00400011000c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 265572625 1250 265571375 265571387
    0x52a09010810090e01092913080702041d070f12081309091406100b0a08040203100507111e2a0a060e01110105070504060513030c06020d12060510 64
    0x1c1c54540d101a0f54160500c2220074075041e0108a035911208082003100801c0181e10840d01000d1090319104100e01c0384c507034124060003c00303100441503240c1d005c0022090a454095800400030010044042601114114402d022010a01901c2c0f0301081661800c00c0c1d40094451100f103190311204583e03180c85241e4896800b42e6101e4481402c0010a40b00e00c1c0107060b040c900c117032000b0303503000d055020f801e14200c0f0290031b1603180400c0007001e01941452506840d03624403185000203240d15180003007030407c1655080040c14030b08140400500b960055012400390340908116024034440c030089401941130f0b91070a894030340260781c160b000602450b4101084071034601c882d01590001000003015441c0503441100413440155505090350703001111801d007210080000d01051500d00001001391056018580500c4370100e10310100d11000c4400c4000745900402c00d41e00303071703440b14400395a800c55801140c00140b00100d000d2840c0c00280604400c94101610001e00403400c42030503122 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 265573875 1250 265572625 265572631
    0x2040b041b05250c060206070305090a11040b12011d03090a0e19020301060921030c120507080c010204170a0b01050607080c060a0501031205070b0a020d11030109052a090108 76
    0x202d280303921443d030003d204424004650320544038080024500700c0041d043c6003004101d48185858602002914003003c0f407952011030340481c52282c0c41c00341000150040c80400c22180c0c00c00c115032091310302040158030003c0d0b603100e8507075041212409200410369070b119050450f41c00202501e030070001c2d00d4200c8020346d000440c17004170750311606402040c3d50490300300360300160009004800800c176030080142454041d00118240e051400348070345014000301c010f00300043c1048003042203290040d110720240c0b080c260b1f215a1940d40d40100c010750501079001405000c0c140c1a030818508144800010f284041a40c00741d081d20003070b2f10700303010014203030803c0b82c09840d004804c100900d1401c1f030500079544074040394035002400f54114240880091142841c034070500c203041201d0808240c1d8806510b50080b036405000d40e44460b00041d4801904a206002520b12030100001c2001d541343c0c0c10107481a48107103000c8619100f0013181040403003c034603900c0c81c400c6e41001031000d294881e290300f07a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 265575125 1250 265573875 265573897
    0xf100516050a0b1003061107050312071103040b04090501050607150c14041502060603011118030a051903030b03060c040501081005090903070303060b0c07122d02040b041b05 76
    0x44542c59030f1162441900d04541e5092010116042401008076501c40c1024038005440c59034104a961b94400e9074a20440c03061048080c00c66000910240c0300d00020016100388509072615a9500c2d02c1d03203981900b00b4001d06200c14280b03000403905082a000f504c1020703400041030102d6500010005000b4404581020b0070448040c110340d2000014100510003415000b841c10603a03441920020b04040c409003506101c0d9040540301d811038030660f01900c04c400343d000009402c182e00354000a01d009481c1c00c00400ca80511289400d231903801d4034103100414000d480a02141c036954040503115581110700903d41841400b0600565204214540d48580c0166249000d00c0c0c0310000145440750458030780a984d8400200f030810190305008200091074119100d90500e44410b0400d9141c0c0302600803040d016845600b21030510030042c03103c4040143d0344e010103a0701c000400c09111000096402a4090b80c01c2c00c20440c1c0c030b41064881c003442485035091218141c0003c130760456941d4451203110f5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 265576375 1250 265575125 265575133
    0x1d1b040612021216030c03090b06010f12091113060303121e1a0f0103230c070b010801151205060103021207081209010206070c150213081603020f10051605 68
    0x1102c5142050924000c0443c0443d901c44d04003105401000e031030000c1031507010181880c0409001a1003441c4035604480c09082000711803079180002c8484403e040c84485e9040e00740104d20048c0104444900c4c40d01c9401d0311101d151041c07000112041d1070140c84010b002448000d031054015003254010714a08240141ca9880c01a0b079080340d1080d00c10030301e005080d2210442c1c1140b054078018046100752002828103024096074192450700b92b80e034060300145202480400a04442d403581300715484160f21009440ba031b035842d003c0300c5008103041c40b42d54904038802c038400f160000c64400e00050856110008080750303070031070b42409510070a848a040c00d511074480701040b0b45d101440000012984c003100c090b216401d0340c00091a0442c05000c41047c4030008940d503020075240c0d103115052441a000150380c0301d0705881c3c140d1005a0329804001103001d641c5c9600c2081d10614080000c880c000c6840b6200602c00804000080d00001080302c00304104010860041003140f883c698010302031401c1d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 265577625 1250 265576375 265576387
    0xe010f09020a0e0d050d08013503090303040e01080709050405190804080106031104060b03060d120203090d050a0308010803090d0609080906070308010e01090204030305030f04020a030203071d1b04061202 89
    0x10413894044584110342581050003100203184d8059222801000e03084005045141f0b00f4000182c444050070880900403030341030303061090b02c03010800c031b4803202c0703001c2c049030b82e03903940d9031400210080d0070b01400f8514024201e000400710003600038140181e4100f03024244000615068611040f14400111070120007808001045442031084100441c000c40100304030381d06480c1008101c1e8516000001102d02c14014018152030303552000018039800210603e0407984441d045c4d1450103441c01c140d0740b190440303162008020000c600d107146203200f41c5480490f40d8075400d490b901ea00400760426080040ba8640001181180e00844034aa0150403964540807404010441030b51003040c0c241d0201d071a5200400860b00032600990040884035004c6003050306550300102503100c041e144440381480d1102150955030740820190003164020b003190807881c1c6e203182420101030494600280c45c8400000210114200c610004c1c1000d0150341080ca01410a0015a000103403030300c14044940d824020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 265578875 1250 265577625 265577629
    0xc05220f020c07050406031a1b03040c17060105011d0112050a02030403110307020f2101060618051804030f020f010f06032a0911161104060e010f09020a0e 68
    0xa031016200c84940050795480203101014500100c0b0b60000d402180340410030004202d0b900080b41c1100b007500e0305480706440e0140c0c0e8101051040d142034a004000006000802a0040c401c03022181d005203081303540031001c00d099446040c2441000e0100d85001001c9046030f2054483d440d44142c141091800c00c0450001c40381103c00440740021203aa001040c0302c00e05800654111282d1940c200031440d00c5c00542c045aa5007028004142c0601c1d010000d00a100326181410354001410030020070140d81d80784001002054184e80302e1941100d804c0000c0f40c03c1c1445c00405503c0c001c000f80b45007a07070f107031075404403400b8105c0d203d20011030040e4040c2c0c1042c40c0c801e00a24a03402c00a82c07005c6402821410111071040e00c0d2100b244510780700c00b02c10381c004e45070151301c05c003140e18641c00050070082c0c1c150b200c2d42c50303c100080800c500199aa10000300004d540340109142401d440070032801c1c0d210081343c03009007003e006043d1401e01c030b540100321044458009100d03003515407804004c1c207441500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 265580125 1250 265578875 265578881
    0x9060501050418020f19090c18080709051e15040605040902010206040210020f0604050705010f1b060f0e030a0c0506010b12040b071404081f06050d0807050703080403051006080a0c0522 81
    0x7d02c04294640c440740c028154820040c04041003042e008000242c94046040d40c0d5202c01d2103400c0c0220740381c900184800c1050207440b900c1d211034207074180084c40d00c03c119540e0540302c1050b16201e40c0c580300000c00d16060601c291100560b060f00140955100c64007009200160f0b98507000031031003100740002e180d603414001d10340554411030003081800d0500c0c0002d803007105407052880400981c00001220b40c01c0c00551200075580210000401103071025000010f4660050604410b200002d01e8a0400c2c0d4460303d0880c041b8001e806580d01c0382d88800f11134400348a030321041e020041240c000308001c1410384c2c070380c04e401c11507500309003a00001e8907608407455081a4080002500300b000505640154801d80780346201d14800c00300589400c10001035012001010050904c00010a84504100c81000340c100074503000500b00703446a0b507900c3c010741c0c0c079a00704988804190034420700241452002860341d0401d1b510160302d041e050308140501c0102d6110140110000f6104c8411005840080c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 265581375 1250 265580125 265580129
    0x1015031e0c0906120221090708030406020d020114070e2704030809010506030604210509030601080307051203040c0306020c010b090405010c110c06180604170109060501050418020f19 80
    0x2031511903902c0d00d0010060f052000b141080c810042c010001440303880c02c2c503d801000c2800320707101c040e00340d110242801d1806485800141f0984800a4007040198000410348182c000c180e0081c004100c1c2080c0846544c0010f503008008100400c0e03c007411490158a02e001c80d0542154081d1020318a07070100490800542d010f034081480c820501000c48020301965621400030b40080c180c5040c00d41e240d200c1031004106107810301c840d9404c409140c3d8482c20403500d9009005044601c956107640d08aa20f95026a101702d03414460100c0d44a144d10684c42500e00c595000b103d001c05091840c1c440d18040d510448192049540e202d022145076504d600d40a80518054800001c80003848000a000c80340c142c248100700364014181d5402c542d0740c0b8411201030350700e0300002d1903807603500d8800306210380a1a0089a41015618034018200c14154810500a40611024412a6a1401440111021b07184c038034130300d20316890852300581081080d104036884060442007112640c0040301480301026 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 265582625 1250 265581375 265581377
    0x1f0b0f090315040b0f13200d02040510080d11210c0613200303030a150302030f0313060309150b0307090e0304030b0106020d05070f1509030203030901051015031e0c 72
    0x3000034030040c400d401045c81e505c1001075282002c90020b81d00c490075102c0c0340c0580c503000d8100702c00d000042500c8040c40e18280d0b50327020b0300a01c041d007403561000030a0340d224000c0d15428860a200602c1040c81601d40c80006d240c0107024104601403028898030980e04540d07642550700c81001001500318082220610903241c0f0005e035039808059180008a11302404410005020700d04050f9015940110449030041000903000034a50400b5281080e503101c950300195150103040c0c2074408824002c001000d00d8090f41e200c00000d96140c2c0001d4084429075880900092581a144000c0e6019076000140212004049032042580c1c0c52040c0c0a84060081c101ca50340c00c089810010810749505150250513140043c1a42400c005401402406613140250201c00380d501c80d1414051080f0034400800d4a840051007403c4150801a60300c1d072003a100e0f5100d03586030400088044511003c200192040040181200c080740c21080f0054280d07400010118820b5131085030352003280d441031100304032075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 265583875 1250 265582625 265582643
    0xf080a060606111005040f020d0503030403030c30060e09010207060e0307020f100309150e0d170a0b0a0519080706171305010e0d081f0b0f09031504 65
    0x9440c240003039500c039500c2042800386a55400c50340b00d02c0071072201d000e10341300c480005050f0343c0d608050481c1403d8100c06908180c11a0300641800000b200645c0314034081d0b10103000342d4440726002c070340c10103441c03003405903c500810303480d13034800b61080e91020f250020b0100820000e8440110070250542503800044070381d1300107402000c00c001030040100d03103030344c20000d181030491036004101344a603142c0d41140706850040c852011540240c0c040c07906160494007080c2154010141c0200820181701c41041501c11031840d00003007841200e18500701420a1384030b64141c1c68040c4000041c00103419002d910802042001c00c840d2100000c0541d905c444000c010102880c086005090020381d07040002041405412051071f103544030241c1340c020700c2d2040140d07401e0805061050040001d01c8091085000380410320110b6648001018001c00c042c0c1c01d20100380c111440014000d03482403040c900110310a0100482c4000b111000d41108000a81500c190240005440c55040801c880131900c07002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 265585125 1250 265583875 265583893
    0x2d060305090c0432010803030402040902060c0109060b12010b0d060b0f0d0b18061302010e0607150605091807171903050d0c1b02040c121107110306130305090a0f08 72
    0x60388040402c4c3c5810050000e981d504060309261a0310004001030f00641c1c680f07864004549a1204880c40c0003c9071008001e802c0c0540340410251240e01b000502c542d404104040300c2100c107108050a05100500648180003c4c0d0b451001401b400c2c0a1603510882151b55410a0f0302c4c1d0118040c081441698010380d5071504000c1410348a92540c0c01c4042680030508100c3c41e0075420071b9804040703409080140d607915a900c0020f031940300d0710740000e10606003001420020b00080c0c01910940d881101d48180680da1054000134a80b2400e148030641d03440340310304100f0b12110340d10900302070801c4030a030760007030b03e88080c585400d01d0486011070002e0000a04210200d030309210303d013942415032400482c1840d20320314000c1039102131000070380314a80e0b82e410304a41501502c40541700420580b0140a030030000a01e50401e03400424090f158a010780440100c240740c0403c42c01e21800c00e42d078a00c1c918503100e4038115242e070400038542d80c00c0030303a5000202c0c405020000e88001000c0030401018401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 265586375 1250 265585125 265585181
    0x6030f1807091b08060306010308031b0403050313140a0b0d0605030610090b0604061e031b020d030f020903060c0c16090501061e02120a03140a0203012d060305090c04 73
    0x90b0710441d5040804c103000e070a000395590041406030441e50040d8402d0303202c1e114581e803000881c808600e00c00110b000020000100207000c000b900340521810210b007a030383d644035107000c1d1901350400d8942c1c0c00400c642090045103503000181c41030030980003002410702c1d10307a408285004419607100391481c021187c0dc00640c1e0040c000d00f2003114040e00c000d81000d14180c07001e842c4d003040091a00c4451341200140016611a621104d11a060100105102003000602945034142445a000040e0802000f60502085130084a120101c00740c01044150345042c2c00303100e0b9401c294018038180c043d400036200c801054200741c1002c0d000c2854005446c1d4900080070304003039a40700f440345412507102c490325409500802c0c41d09030f03070842007141c0341d8940c04d000341140145031403600f4481113404001404980e075107641c0030b14161002f403100038102c07503519800c1c000c4e5003240103030320300008207c04001c0c04540c0c403e812440d0450119000c40345140c400800180584d1240c0120010b01e4004d400c0b41c1c8582 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 265587625 1250 265586375 265586411
    0x40602070b13030f0309032607020c0904050c0105030603210a11060708150f0a0b030109051807060f0302040b0d091b050102071a1b07140f06030f180709 67
    0x4910100b80041d1045950301138800260304c881076041c15a01c220303000906000f002190b00951010b20080c4000340c100e0251100f1080c00c0c0e40c544018440c5850514490400c40040d44c0111780210080011055103001101c081d40000d0200f40c01d80243d041a495240c0c64000c8034000501c0748104d661920400c0c0c1000b0804111500c1d01c0000d44c0c0710206010400c4e030041000c941081c0c248c5141000d01c01e00c1e0f404075030041c512000e103a8002c00081d40001d8040c01c442c01940c182c4d000540140150746901c0a00600c441081d20303060855008020b08001450050404904448403800c025042541d03400b4080d02640103105d40d5080d440d2202a080d041090001ca503070713440000441064441420100001e55500d120300038006540d001d2015080c0300082042601c015812220b81a9103401480d5045903c8005d503101c0d4000c0d003003045140401c00d240c1142174a04041d00038100d11b040d0343c3e51401e94800040040e0040003c4407800030400ca108105008190143c8220480480d83d402410901000303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 265588875 1250 265587625 265587631
    0x1106040b0d0b0904030503040b0403110f03070c080c0916021e100c11030a03020c010207050601081b04020a0e09040201090306180209060402071101140c07030f12080906010909080c0105040602070b 86
    0x490f480f00c008020020b0340040036a60440e8105500021503a1240b40659000d40c400b051300c0d985102e0b8004034441d021002000700a020303c40d00a41c401c856841581b590307120b00c031200c040e81c06200340b0b0001d4680003151180a50090862048500c3d40710581c41c0b10f0020781c4001c00b0310582e80c20005e60b02400300c0d07090140c0e2001d44035900d08603011000020f032f41034403400384a01e0f1608154000606d0106040c00b50150381840740c008050328004c0d40c0d03d81513256504c1032240c80240c000131101400c0602d25061003521210741858a0350060006d000c400c00c9071103280240220b040c0301c85050040086102c91080a5149240c548102c5007000c40340100803081000030003003807080d4010080400091945001c1022282081c2009542d510b25200c2000507070046a2140400748190003000060024010340e58003581e015142071101001240390032070f080202103400750130a501082c0100f00d5601c4a0b1300805015004400550510160b024058250381056505580046e0042054000c2c4500028840e0f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 265590125 1250 265588875 265588879
    0x70302130207060c110c040207060603020910180b010801210c140f0f1503040c0305010c020607140702090601120905190201030b1807180504090501090b060a03050601030206071106040b0d0b 83
    0x1c1c81d880c45c104001e42d103a0004843d64000d54010411408000990300800c0246070f009090440d03500d0b06030190301c1303000194801c1114040700d2036418414044c0f80e110f90b40c404801030f560058076a0a000042e100c00b91816211004d103030070301e40003102080c803140034800901883d040302c4840f40442420424440e039003e040512170000b15032400b1040c2d889001a03c0258041d10320740d0740701d5445041c00041e1b117095030700107459942010f02d0140726a038045403a07481001c05803580745040b0446a005401e07801601c000940040c3d4440c0490320a41c000c0c00d0030b90240f1900c52000ca9030303480e1641c4207428000d044480d07000e640d101c000c0700c3c001c540c0c02d402030f00c040d01400d640161550346112072040d100c11020780341e04288503040042006810400540741c0103004058402c0c045466640fa00318000c00300d248003270b03c032111160045612480e00607c3c0750110303504040141420303402c0d50200600c2e0340c42003104803021612070064003440e45031400540000d001788000c00c3d448081008000c4107a4007018070240c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 265591375 1250 265590125 265590137
    0x200a050601080f0a12020c060a080a0f110d0b031e06150414011502100e1b03010507050405010e06040905130524041e050105010b13080c03060c03040302070302130207060c 75
    0x220003a50004d6a003555a4100c11380e03084e1010440c00c180d0800d10410059600140000b800842068006140c18001c8070f21040c20003100d0b1150500c88201e40d50000005091001005000e0350f12070301c1d401885c0303602f40060a41d00748032105c0d13018420110800403d04600e811000400101401c0c10514441c0d8600640f024000d10166001d1002e0741c0805004900c80206101e40305c7c860107108110744141055070041c1008440402248103540f42700740e00400900c0c008040c400755490a0602407540118940c0e01c4e40d600b8142004019500c48c15441c1c6440d4104006000001d440d54881c02481d01415650000610324682414880e040480364010f10b031120281014400742e0781e00a03c021a803154100c0300a0006100d00c40307640307034611a9104050265800d120010680d9150080141201c110030701d03601e03a001c0d03903400c2007d440703c0c0ba04000d0f9503d9044100014100b150243c011076106109106840f04292a9030014440c42103034074440f0740055002c10620100300080c45902e0844030203051107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 265592625 1250 265591375 265591393
    0x203070504050d081c0f0b0a030c050f010e04052a070b010308032a0a1107051e03120c0a03171317090402070f030327080a200a05060108 60
    0x58001c1c400c1e80310b03503070103184500145024040444151020003501200c01e860720041107038140040d09103014190344042c41c1c4640180ea61030300c0c01100781140d81c84090301512520f06810461206840150707541031000c88160400c4070b954500c13406200340000da81d0441d84054207a001030050ac5220080c0150b031508100400206800300403590442e90b20100c056038942d030b410b540348030310000401803122007041c1c140d0804407081e50350b026004040b00350341c0c1c1d4803601003000311071a0390b50014410b00f50401c02c0b01010594464150101501c0b6400107012034101c46503407060b02c5469032180030140c0e4240c116402035400c05a00c0145d645811344204408021404e001c207081c5280f603640d500c02040050015170070b08410503030f082a5036003402c0003001152511503504014401d240c04042c200c00092501038944491044013501c02d4110751100c07465414050141e036104015488100c2600500190983d0b03080c40c04031551013260344242d00405401c1ea000700c0d25160303184c540d041e004205182c00074280 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 265593875 1250 265592625 265592627
    0x90821010803032809050a0b0a14060906010c02120105100b030106170a0b03070303110717030d020a05070c03060b03100c211b0908070b03070e0405041112100609020307 74
    0xf500d42110716001e54410b101c40007542400d6804c01001265070480c00c003003c40c4280600031070001200750040b800324040e070b41c4202c1c3c0c000c100c460303640401d00402505404140d1608014401c1580500d040c1099446a006074000401c0040c2c0040c0252040e915002004000315048100e90010500c5140d40d6086504018018003405940c01d0a081284130090014a5a4909070001e01c1c1b005c1e006002e446a075602da01b8000d0020005000368501407082c00f00c002006003000403c03210464240f005182000c00441e0008069803164682c00f0401c003083c41000c3c00305484280c04002103102d1040000d407800a0710a02d800c111110460b03010b51454402440840743e000306d4104200d201d42d4015540a4000d00400f10081a4241e0f070381c03108408641569900c150082d101a00380d507804011210400c1d038580c2c0140702c4d807000721141000100e0030604110141042d0304442d40103442204503005400e149008a0081410100c450a940d845149498009007662082c600940040e50b000e52540c544420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 265595125 1250 265593875 265593877
    0x41e050f0f0103020304150606050702010206060d11010f14040e2203120f060306090b06030f010c0509091905090304090b0319020d0503120a050105100203090a03080c0a0501090821010803 82
    0x201042c18150000000f80030849002c1c5030801c4113204c01d13820801140c50b85801000d03600621400c9026102d488042201803401c3c052140c8120f60102028400300b00913001100c4024401d1902020301c646140320703410b100403a602620142c000c0407100b10241c40d101c010342d034840145118180b690509030701c404020035481140c04650381e11286e8081005800807080400510b4654070140000703290207031000810804071501402104120203d0706000d21001c822800c0302c80000c1654089070b420015030006003401c201162380600b100d540400101114a1143d040d41c41c00c440045a5400000381030200a15074440c1c60801202540180003010094030004040200244040d21407144124001c00b0010104101c0e1402d518a02120885041c2201e5000c0505000c1c0250741c8116015142c1030200742c4000150303000b400005241c076918600c0c54482e21420750100d418880c640c09460303880e2000c6802400354059080c456541a683d03016001880140d00000021684800c44524010010120000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 265596375 1250 265595125 265595149
    0x50a08030f1545040602071406010f050d03270303081803031504201801081303120e2401090606140f04050a080a0203060a050c071e0503041e050f 64
    0x44a4200882c40004001c144807030f50300d07290070300701c04032402c1100308511038000c0e1140f40d20a61203ca240c4612307291194507040240101800902207100401030351030030076900454540213007000401c510343c41000480ba00640da8148480c1c03136001d02c1c00c10801d0391002d0100d600c0041c500720b46500c2420304d80e0081d01e920029000303084414070b00c2c844074010b60302c40c0c1c040c02040300ea080910703080751040348030441c4581003102c41d02d13466031034181007005070350194202c0d9200e0000c1803910000310810350b4007900c032147c0030340f0b103c102d6990398500025950f801300314444076400c81a41410b500449052440a180016017000200d60304061007040010b0f04180484007200c2c0360401287c6800b800740204c03445001d03962199274031203205000001c481038041081d240036402542035903943d6403203910b80d00c15150b054440340c010744401c00030b00c1d02141d1358454881300007505107441e002d01c8156441d89451500143c2110021a003648800c5007100c820700c02d624000c083c00e44200084210880c000380706079101c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 265597625 1250 265596375 265596439
    0x7020d02070512010f0624020606090f04051c0302090f0f0907051b030712260c09040605090906060109060f05070b150411040503160b16050a08030f15 66
    0xa24403c41203454290003850b094002a0020890380c0c3d40c074844040d2410b413402d4040030208803440210b00182c4089522841100c01908144140c0c41d10042c80c0c251041c010419903290140302250320040100424181101c0401da4002d40c45000020400c01d54404004000344200341300e21000000f0f1725083e0407036a1050640c207080b62a05140e07003012844025044109400707010008010041000c0103040c3c054011955030350501c0c1d010800c41280490320b01003200401d1200312000a1440c00780000200344492001d440071812541d1340c00444d03021403080e11500026040a020010b4950340b00e0050001010546441c0300c4942c5548000751561062940c0584012209000a05025595032a82c00e040744050010040c000308040780860780d8109008040c428040d5031b21a0034203080450702c020642d10076041c81407402e28132086200101416890407926805100315010209031904081c51207080d901039000b802e440c08524802c0e840c0c1504200e1880f5030900c0007100d0403c412250b0324100703051340b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 265598875 1250 265597625 265597639
    0x302010503070c0b040309170f0a02060a030204080109140d080f0c0d0e100507030e0c130e120403080414060c1c09080d09081902060d0203040602131d07020d020705 72
    0x5009400c0f00c0d1000700c0c150161000d01290140010503078000180421580d00d00c400c46174403107540909644400c0020380300c407404c0c0d0000152401501d000c0c401890001441c2c2030045c40c19649010150135070704868000d0b50480030001c5201030080301400021710449083c03503c03070503901d0b16101b24000c009020300701c418a2403012960300c4001802d07030303c030644c8400b604003141c00301d40c1025462009400c044601c00b002a0520402c40c1160314002071f02c650601d0700800740b0094174000790103c0d000301003050b101c442500c50381800d24000e04c05400280051805184000e80d2541400b2041d03489404110b5114080c0d6810400f5010001d00800c0c041b50f01100e00700c40014000e03400404031038400043d044100c00c0d00401000c0301c1c02c0c03030300411284c007200c03915010f440e400412544001d5840c0458500690485400c0241c010f500035142d000715441441110010b003001340c008412403101515030000344004202107003060301e03d456a50800d5000302c061001f01580b149440000352507201a10500b806080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 265600125 1250 265598875 265598881
    0x30206040905130803090307030f0905010507030c15150e01080601060507060b01020109080d0204060809030703050318071508060f090c1c021c090b0a05010b0f0702010c0c06020106050a051206010302010503 90
    0xf41c881045032245030418102501d0341000000251650b1260000b180460200440340c0b071030a004035038200444105031682030914011351016100b0010501d01103034148035201c410541c081d41e80c407403410368806003c3c2c910707911400c12164403c001c0c2c06030800d03040c41c2e214000402c941a40300017181c050b5907004c0408204c59100c400180d02611030b84c00002c1ca0000085841650144036501510496142d41d4902d45070b0b8450701e40719034880c03140030342c0030f400900c0c2000041c0c681000000d18143d0051600304071840300c1c0d5203420302c0502550b0b45440360700090041040c0009454801c20007212003500322914091800e02c4010480c081c0f0503100b00850100500c070101240f03040c2c950650b288180f81d85000d509603c500c030250b40040001000c1211500110342c0450300c03d14841c4039107410703915501440c5103014010901810640c00c005400c9041018040950700000c0442e140343c002000907400105809092201300310b14000650049400b074170360368100e2520220000b505c0781c1165028240503a480d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 265601375 1250 265600125 265600141
    0x332150c181008090c0103020403150c110706081e07021b21030309011d0601050f0a05040207050717280f020612060915312a020106030206040905 64
    0x14000300d9810b9128040c441e6450b582da070040b004901c2503201c0020340e420000691700640403801540000b6141c1d11060b4132081c000141c07503100d405404082e04204020781c004000ca03074608540f58110000007001d030018006469601c140510b40404205404255490803100003036844a04103800b002150550417002d030b4a0b120309481d01480489104180245000b0100340c40d17407907000395507071302032503190082001c1c40921280403483c846500300003400050b4608820404900070980c6900d03030040c0d118500140c1c9039203920041c05600d20401c060b03e505880e05c12214001c1c90104410b41da2504007070701440c0c0041d5612003441c5000803507004ca207646445810002e0079014a20b0000b50004000194502841030401295100b000100c1c0c031107140d5039801702134890301944c1c1c0c60000e40002240b2145485502e0b03505090145a00e20391100484000352484c29013076501c04641c0030300b54410a0035000c0003134600c02103440d002c070362800248400c0d469940031441c0c82c8903a20619810a41d00c0d80841d0040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 265602625 1250 265601375 265601407
    0xc0712140c010e060901021c0c0306091404030311030108030703120608010c02060114180a180210091805010b030106051c150512010908090f0105040332150c 69
    0x9164120030440e16a07400031469030080454801ca0b20041c0701c1d00c4002070416005008507000c042e40042c0c04a0418002141c42000e010400c007040141622003a0105084406200d032402003a150301c4c180c08503051609024044030402d4000750881c210030070050180050000441d02015418504024001422550940140043c0d003102c0465401d00c0001000f040d400200c242c141d841c0c1c0f00c1c0c00c80c03030171604400f08003985045400700d041c1d207a200b070006060543c0c0d03503205014280c00080e041c04006241e50004601245d1002800d003c204e09a40501c8200403280c005004c400d10950200070550406403a1321040c0814460310040203000500343c00103050100540c0d4511216078014000307454005240f2510210034040c0d1401108444214880f48d00c0500030f4601107504041701918140701c540034080d20420005006041c040100f00c000000b0790040700c103810802013240b0041c1100c48119407466185a070094407500340c4e20482184150890304100c03030303030444d0200180f1982d841c0c016083c9100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 265603875 1250 265602625 265602647
    0xe13170301120c06020d091203020a0204090c260604020d03020a0b0405010506041a1003020a0309020918010510140108070917010e0f0a050c090405190f0c06080c0712 73
    0x1540001200000304418090040d00345140f060a488520a44845081341e5450440e80e210340010046582003240d001046c01c0c0d14102800b83c41034031540f03c2c06402141c150b50800030102d40d0b07005044010480c461110303941d00383c003031040c00350754061815464415581710300240010384141c4600d0030b0041054000c0013940e10865104440259504d001d00f842402440200d54240c0a942469010458030b829a107010422540003440140c841801441c220000d4208405070403d056584c00b00c0313005680c4500c1b0103403007403120040c203256200c48460024251038020704070385043da0280d4000e001503940d08254604000c1e0a182843e440d990355001125010a550301c11584101c102c00050f9803131130706401c8094208803907021105405400c0305069036031406148054196082500018040d14006049580182c0648200c2d1040c200d0b800309220b0340f400c140342c102c0b1010540a049410001001e20b6480181114244080580fa04480c0c0d44600c0c454074200034251900c0c40c1540c51060302400d600740c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 265605125 1250 265603875 265603913
    0x41508070b04031505150913200102031815041824091107060501060c0b01060906210b150403110d1a07020a051b04050a060609121104050a0b190e13 65
    0x8081d080c18068a09128448c42040e82c04400000500c0c0d00c1c403000072034001e0b0000042e03000b949014080207501e10242c80400c140f03a0b12160301c0c950f0202c11884240600040c05c1c41c0f0310204d8101301c0384d11240c002c450300c00c020401c604103094100c1d0500c2c0103015200702140e005020216001813007080c00072132445652402000c45141c039001280c299400040c1d0100c42e445064214140e989030801610390000601c95a0001074600c1c00500c0380c80b00b4188260200d01b10003001148031000c1600042107121a00003890710410042010002d120480c40303443c6015000b80d600c2d19000420b034a40241c810f210201000540307290030085a0924400c001c0e04100b2500074041d500038655180c40c82c0821450704041c03500c542d050078045800500c0e207100b0170044518a89400700511314111040403055a122403d96120004114200481d111806054880c0aa11900040481c48803040020846040d0307582c00031602581d00500c62020301203480e94100803130101010f14400c803460204a0800400107100d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 265606375 1250 265605125 265605139
    0x103020a0608090313091a010e2d060408010c1409060304020d0212060f01051003180b0414030c0d030c0206090a2303120901060e070e061305041508070b0403150515 72
    0xb807200c1c1d03554002800c0004100502d074200e207c1788011a04420744651256000d0030344811181700961841c8011602e440050802c031402040341c0c002a5681c00c5548591a20794480d10f00072100c1d58000c4410b50301b8240c4800c1c1e0b604010100000c5a494003000300028014a602d010a0040d9138030340010810700001781084501340e18084c514414400f40031702c00d0501807200100c1e902c1c0c0b6035000380502083c229030b40901001d00c000782d4503030001c02c00014100303695a40c600c0c1781c0d03030310443c81c2030004114800680008001c41c01700b00000404540c48030980e0070440d0441c00038450f05805c04210804030359002124041c000c0c000d181c215104200c0306400e03000382c1c4000100c4990030a2a035007500e1244505030003c0200aa41e0403141a018000b20f814000080c001c0d640500c140c41d010018002c101e164088020b0210340f200003007021500c00300e0010304010b00001041044e550100081d1001e005800b0a0500b000e1071a51558030403e180c0b0600112140c0f1640000d80a0404444c14039038034000034104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 265607625 1250 265606375 265606379
    0x30309300302010f0501120f020d08091c230606090c04150810050901030302031207050d090b040b10060e01050d0e0312090601090501050120070b0307170a050103020a0608090313 78
    0x6402001c1d101c0c48075681504020000074040c02d991a402c1955800c0a01c81c0e1708c0038083e60810034011b4945c02d04882045060283c00b40984070810000440d0f4020154940065100c0c1415008007036400395004014081d6002c981c02d9400100f02c0d0748e0062001d541403051038840c2c40440000d40144e82040b2400d6145540058800d42d001d42800d01420b0b90f00c0120040c01c0d114414440d420201740405005039004002046a041442c41d501d58084c1c050b24280341080c80010703d00e810741e80008800e03124220000b06220070f0010317040b402500f0480300007604241d546840006050601650a0a4140700c0f020070344e1203101117150803000c020b861364020780c3da1303a048207800000c440200b0f584401e03652089100200e0490560b02c205410f03600140c603030701e14089072400e210b00c92801502c44850540181c40d0009054040700026501030303c1507864644130807501d6a44159080f030002e00c001e1069081800420241c3c407504041010b455141c81d081c12195580c003400c41c0780d442081100310319001000c1c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 265608875 1250 265607625 265607627
    0x402011d150f0405150c060103080708040e0f0603012306011103040e100602120f040e090a0b0c0307111204060807051b01140705090a170109020d06020a0215010303093003 75
    0x810903074000f10307101903501d41c28441180103401025031b0000c1644c45440140042102d900140010030700c110440d038603003620750340280e002d954180ca500c0c5c400c01c1a0018081ca5190a0040036007400c4007149010300404402225000c0c04000b40a0f603060000030000404400814803c41d005413047c0ca1040400b03040103680607005801b039200b10001401007000b80680200914101c43c000c00400c2001400d0504001594030300150103040ca0b405881101c52540018182c14031862040c044056143c0d10391910750000f41c140040751189a0080c0c119030186484c0300001c8041e20182c40141c5400700d05655805416607803481078100c101030100d402240c2900703c11054000b0035031040d506c4100d44054035400c4055a0a00075002150b502001d101400e1280700c0019a00584400c010400860406090740100341c2d00540c5460646402d0707000108142c2407601000380001c55076503c1c4005005614507200208091114050080c050320b8204000009403c01d8454011040d06440d01c07500504643c60 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 265610125 1250 265608875 265608877
    0xc060103020f0a0806060609010c060c0903030e2403130c080a051e031902030d0c03050f0105120a060b0316120b10230d08160611030402011d150f 64
    0x11040344255001c02d0071690034102141c11200304c9140200410658031000100659038210342000c1d410070440540c04404140035010304544ca281c581ca0b40e41c401425824000d1aa0305a158aa405400e601700003040d2130082055601c04120b04416441d240d03180d080032401d056804010246c4001c0718500c0c00300307140501180f400341d10341c0304404a0f0201c442032a5144401d03c0b030400400340729001840510b0754800c12404009251295105580c50301050504020490304001070400000c1e0fa24420441c0540602c00b506000d8203080721581034030010964103550722207000c0c400a00d91900c610f00c1181ca07440412081c805010001404c0d07010b5503c030100c6620b91844140182d904800141c0401c41000c2c00c100c00d45c00340c07000301041081c032a0800703080640e28860f13098001c0c0c108114110210119035444041c1005812044503000c05d11800d0074210300b80c594802c40c2802c41c2c0002c00c2800010707078010544040100e08903803110381c1c1c0914030300013401e51400c02030301181180700051030a28050046c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 265611375 1250 265610125 265610129
    0x9030a05030301180921030f05150102070509060333190c1103030c070c1203020c0907030c0c060b010c0506090705013b0604030615090c1d21030c0601 66
    0x44040c0304d0541c400300c0c2540681c1d1000b90083c0c4403850040d258602c2018000882580035218100400c010350360121a0040701c00440c0c10f00c81e10318032481c0c800041e41c1d042c04054001d140481d0a01034909000700000c2c0c682d4101c055503111050b004900d56045807414403480c607a03410380c0440542918050104201140318414249940c2c1d280800c54104603019060703d803940b000e81c400841c1503a070b0740c5d00c4040440d132150005940c00344c802e201c00030385092580840c1110301d03c240d01618141219109001d02c9540c06080318050500303064442484541c4a01ca0a1501e40c000b00041a0811407a0060b200c6880158025085000300001c006824800060034030840720280d841483c0ca036680c40c0d0201742060f6040034a4001d881d40034070a6030342502e4425041075a44010101d03031402c2d03600e070341b160704179040d960300382d04500da12110800c940119445907200c0900c160900320403150746085c034a10420f600c540790b00e100b1010707864409000c0319099510010400100c1c00c503565501c01c0b42425543c2d00c024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 265612625 1250 265611375 265611389
    0x60c1b0d09030213140109050606070c0b0406020d14090d0807051005061c031b060b0603040605070f05070201200102131202030f0a05100b1c0b06151c050c09030a05030301 75
    0x9140e056058154810170b45111141d042c0752010703900f0040814094040900030030b0344520203000c801e010640000c40c550013400015030391a50343c0c1c544840170b03003410f510355104c2c0144000d0302070341c6107401042411110340c8542201c1041340e100003840c001070b890040c024050440c0c411980741c2e00c0400c8a0342d0045000d81c20443d40b80120300a40c0104404028034050010000344140300602103000e5200c282c4c407155440f910020980c80c040d4804150260003c0360156078094440c000d0200f465040b4071204c851030140e10700039103080002d400107414842100002c084030504410340600150084d410b9990f41d8021070028681d140c0e035407140031202d035a460800d038428041c8000000d0040d50000307907076288a501001800484c0007061920004004c2000343d10340080d2a80c0c000d092105440410084252285200045034107091081c048040c0390440388140c80d110070404d003540480428505664000b25080200f050791320086025841d0007260b2106400d441040c1c03000d401c00401202960680e108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 265613875 1250 265612625 265612639
    0xc100e0406031e21020309040e070e040317010501020604080405212a0301060509010e07020111031e070c0b0a0e0c100906080c0301030c060f170703050108070512060c1b0d090302 78
    0x240703d02e201a0782110482d44400346e032003007221500700e04040d004100c445000c031007502c1c02d0590301c002c500101807080720100c0c00204c02c06e485440074080d0000c0c49024220031b2004104e64a09a62025042e00c114024140304d00c1208a02001544c8880f004d1041001640f01740c2d800c031049014a012490103a104180101c03e202c10421942d0405128020844000a04503286a442d101c06041c84070405040c4030300b155243c81d83c41100c0400c070001035000300d04a08215892300603110240ba03140c0005402c0b6410001c0019552007c88d1601800680000301004001242c12101d01041e1500322801441904585155003049045402c880707442d0440f205500d8180d650fa6880901007220310003400700425004090300c081c89014821545440381704404e080054004140b410300f041021011110f0f5000a9101c02c010b01c172440c002d015500c0100000d0300c600c076903009100c40007500c1d41c00c000c0c02044546004603088041007103694180d4074039510002514003032030103110700030720b800a1400140c0c02000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 265615125 1250 265613875 265613903
    0x140a060305090a02010c0c0b04032405070206060603060d05150a0c02070602031c0b0915040b0301114f060c05030d050402060c0f0106050f030c100e0406031e 69
    0x8001c0c01540c1c460040b01c2c0241401a401e036006490700c2c1581c49041c1c0d9412501000454180480c1d40180051400b4510015410b403000d0b003441010102c0140d15802c1600f4001400301c0e031500047d4894024800b2190300e51241e48032404a0210301120102401503c1100c80300c051340e403000a07080303006007071100041c4155000008280c0e910b440503c20702005034030404c10300301c89091000303a800c407899000c0404551070b00c016000806840341661981e00545225101000500d031034894950b01c0807054009201e00e00450a5000281c0100400a003401d40e2000020050046040301820380e0070491410f80040c01031507015010f07401d03400b1000c2801c3d155504020074058040c0003082c00c41c030f60007001145400c00800440000c1d04000d0000c07a000a402c0c071551001c1d075070a1007040c0314480313001c0000a045280004011490558040c0140a81c02100d2001002c3d20782c594a02080b03c8030b41403010f60390740701c4008034000301032652028090300e200840030028440c00d1000c0c00b010500800c3d5a031844e030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 265616375 1250 265615125 265615127
    0xf0e01060e060f0d0203100509010f0c18140d0204020309120a0c03090f030c23040f090201080a02070804030f050c0405041a060406260f030a080601090f0305100f0b0406140a06 77
    0x8134403100040e51541c44205101a00034464201a902158800010a0020004a060080c0e500501480c400307d00202596540040400100b2005140808a00003e00d0f40e030030216201d500d100b00040d00460300000092a0310108101140030082002640359950988060040885089610860010300d0003d4006405094070f1444019039400c0340c1c9843d401440c200d803c490040d80390160b1011003c1d0496214a00c0d40c50303109094010000c1000840c4005452000502840c40200300d0030300c080c418401c00e808250b030320701601c1c1520b9101c150130304c0403107440c14880d10380581c803070b182c1c0d81c07003800c9c00100300c104030001c440100411a403080e43d9059844140030031040d2240c50203518046000c2a0704072200034100307800100c00c00000025a424103030082c10306411680940c3d01d0034042413181081c8905940c1c04003c40c1c0003042c031110451314490459907a2619141c40c1c0403048009a01c3c0c0c2428400081c40d039104001408005108004c1c040c0c2d107110640d803640421a40c98403400008000003001c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 265617625 1250 265616375 265616389
    0x8130f0501021e010e070603060f091a010309020303071509060c03050405101a04020309030430110109170d030c030c270b03010f082b030f0e01060e060f 67
    0x1850050b00584641107491910000e003040c0c540300031840d5900c61002c410514818004032010b0420360360040f0b00c0900308038801c60a000c0d07a81c45a410503203000ca01d54415081040d0140f42e004003480c000c90356900b02c0c00000d240d4060104083e01e410412600006c1c4c1380390035070103a90140e1041c501800289083c1c28181c0c00c6450490700070300a500202c800040800c0b40b9403140c003207200d00c03012010142c180a00401d080ba0001c0b82c0282559000003001c1c0040b1351030f140c01c0c07155018020045e801c06803030b900301403444860260004003130b40c5070703055480d9460f0300030b6280030007500c1412108156000c08103440d90b036450304a001040460b20b001040320201e48079010781080056107855800e540010042c1c01c0041d00500b00e604210000e80d400081a0b81c410741000398020800400100460783c1020811421300302941300445000d00307007034000d140002d035070fa0b000b2480241c1c6040004580030b980c2c10701d01c09050404464000c5510b0f2150110780d07044580d8905014071000d940150103c11002c00340110303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 265618875 1250 265617625 265617629
    0x81506010906050313080d1103060a05060708120a060506071a071d010804050f01140711070303080609070905100207090f02210a0912091d010b03070e120a08130f 71
    0x12002c00c00240e07a01c0e06007517000052803182c0e0030145400b0355078801d90300315408440348482c011000420f07c01da501e0940c502001030303d0b084945a14041d01507503101003600c81c501c80506070a5a440004aa100351648214024903000e0076035940d43ca610b20700311100c10500b40c214010410102e002c038001500c10003020084421a8026100582d56840191560a00180202da19100d0b42c0890380d02e104080c0a5070600006110702a00349080580e00a4611405d240300824654081c030000c00c0807d81c86000f0907080720054070025a00d8440c8001280c1500305a0030058110301c107000c511004980c00140e0b00216050f5034010080c001020011f04180c0c1700d44030001829a07581346441da614070040d110142c00019003400094810042ea030b540b01910548080600890051003080000302e01c0c503000b034020785841440d034038807540c1400c5903c0c40e5808040c04031010803100a450052a44815200c0c860340c0803081c007103030340c520414980040d01da400010403003046840322000281c0920100f5110701 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 265620125 1250 265618875 265618877
    0xf02010903050904020f09150403021f0801050108090307021005040f090b2422050405060616081b161a07050604030c082511030c030a0210051201081506010906 70
    0x3c43c1c101080100006074000100001e0640402c0100259131f60f00e8580503200a00500d50103600c80c3d2844c010020b0403140406040a8103030b81007418040c4550060130141901e109091506050b00c40d140964a907008480000303400c0701940d10303807103d0703250040094003c54400a12101c00942c681c41c1c03040030f940c031119a60760828481071901803125182d108100f01c4a0300745407414188403050000c1d07405100b04000f16440c03200710003802d01681c10b06004280d400030042c1e840500c0c10300428442c1e940d6425010002e8504000443c2168010000e4501d16000305200f41c122402c112003000660070031402403103042220603610038843c0e00041494180c4681540000c080c14035555152010b03511002c04040480700c042c0100640e04c0880140ca100e01c3c8695407247c401901050545030014082000c0e800c030342e00c60752250b5001541d65400107108540c1c0ca9044d98860348049800905907400d000e02185080b0310300081e000855443c40005007021011f000c001c51136a141c41d07160041d1751054080c0260380c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 265621375 1250 265620125 265620127
    0x60507021503091204140f1503151504062006040305030a0c03060e090d03050a020f161509050f060703050106090303050a0c0503030114130e031b0f120a0f0201090305 73
    0x7800c0070401ea0051503102445500303451140e086540d407880d581e0b100350403109003a20941c141500505100d180040320443c1580d44d02515850090455002d000080c00850021101150394407580ca4582020480c01072410806480340d0700e07000050030351040802c1044040743d050200b4401c0ca200021414040c80e0151603440c0795840d941b40307460252021810880c141074a49200064000b0405041840380d0000c0d0003605445031f1400f4003c059550140c10881d01c40e006100d50031880c50108100c0b02002c00c0000d0f01c1c00303044010321701700d0030b11500500341c40801441c019030340d0240b0001144480030501003000f038403c0c82d0b84464058046070404c1c0220400a82030b0601480024003c0c401030400400130b0511310072080300c07a81d4540c950f03032007604089440040d00c3c00f0f884aa041503482c1c0c518500b0701c0041407181c008072115140d80c80c020014510594464003541c1301020000348842142454100e06840c41030960050a2010382e10420750030000030844c43c02102c2c598812310404001e180d0503174400b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 265622625 1250 265621375 265621399
    0x90301110f071b23030c0a0303020304061d060d020c0d091a0702040e010e010e0f0303090a030c0f06050f04150504050718022511190e0a020903031b0706050702 70
    0x4512002540c100c06201c051a0f004042a0799007402c034241035140003c44a849100303040e20034541012a20350450b405540c0b480d00900c0020380210a03a010b407880f501e014210a5224401003104143c48082150001c000107240345200700703039800a0a40c076802c50704491312021001e00448000b4203074400d800c4080d2840d440114080e960100a20041d40001e001182c424000d41140f4211200742c010340055030b40d503450f6096018402d006107210099040c0255085140c2100d10b59140d0b244200300400300140c1030070060403c01c1c3c680115900710340000e41000f1524141841401010042e202a00c0924204107031001c3e0002500446102d160b029010348862890840c0c4418480c480d51141018260240101c884a40000b0940042403e4070b60f5074079003c54042c04c0076040c9a190329022802000301d05004043c50710920b031940100d5001c03a207100980d075544448100280100c507927055044c00000340c55200650350310210b03210024540f0070341c3c2445981c0c04054819219141e0000e400c20941c901c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 265623875 1250 265622625 265622633
    0x1201030224030a090201020606060f1204140303070e1f17180d02060f090309060414150d09060c020105090a02121e0717010501060c020d150203010803090301110f07 72
    0x480e410700350740c0e000c0d640051984802001542e001165074400c1140c1d106806000d56a0400003203800c0901590700901e814208801c4101d5442000c06100710440704102040800c01000d03032100020920506407070300e03810b009200504110f50840c4091103423100080001c14185410001c80e005881ca84400d4940714a124800c0211400106042301208802c4010340303543c00c0c14020920212455400360440f49815407a00400b448061711041c51944148520110b13500c1d1041180c040d02c0c2c0d140400c11248801100117041000f149020b100c1880000c203182030450a0742c2c005421a9106000911040e160208220300303c8400b00c07011080c1c0c0d07010300103460250038140001e0103d001140d050701c000d030a610142e54120128a0305800981e480f0341d400b0440080720043d18146108400004d1025525190005000c104d40c0380740a4030800816080a04002820400c04ac114a22100030754407580c0d01c206a58070b0b50845103c0500a5007004940160010313060100c800500100781503e080c030481e03440d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 265625125 1250 265623875 265623889
    0xf110301090c0c0c061709060106082a0f0d0c140322021503181f0f0e010e01020409060609053a0602071101080f0403030e0304050a080a030f0512010302 67
    0x280c0b200b400805407002c00402e00a0035036002502d020b8407040d600c022128410410444020304c0700c1443c0d0030600c0140305080c1d01803101504869441c4021180b2041c0e4241d440c17908141e1b01c8020242000001d8249a0440700b030082e1101d05c020703020410010203c1362007a01c00c040e5a00340b0f5502000e041002500040d00e0020700c45992841c22410440c3c0122a40807441c12180c001e4041c1c103504010082102ca5444641c8201000d01000c0180c03031180c20441d1710307613010000c55a204030800e03111700d50000180f20700d50103e861200000003e0016100344c1008d58001d50040c01100456801d0200c085041c3d40288880c1088a0010740708110824400407903059070000c1d803c20030f899280c981000c0106400107128011480d0040c0340c0103944032107a282030030103480c420002a040c00818030070098000a26009298401e41504020800540030a0380e981035104e43d8000c9540105045008074800e0302c00128109038a00c240c075020156490040255100c0c06010300d81503026030008014401414071030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 265626375 1250 265625125 265625141
    0x3050411060c0c190e0907031511071a1602010c021b010215070305250e010f11120c01050c071707021504030b06030105070509010207030623010e01090f11030109 71
    0x1500c01c00800000040d131980c02852074005128803060003801740410342c00120f904200341c1001041c1e2285107688510030341001c581c0003002c40c7d640c0c0000c0010084c5520031a1b0f4410380c040d00815030900d041070100135180b01610050580d4210800d0364429600504c120003090000b500101810100400340008c8698400005411401198504400a6801c03075040e0b00035115074074049014940203a5503c120400d0384100320040c240f14203020304203a040f101041c08103c2c20b10381422403c0d801041900c40c2000144601654468540051803004605001d41103a095401c000d0006448481001050380a140c10180c90303540ca1814003510300945078000c004491020305000c0080138071420041154005074003e60b00f92440c1000c00250f40303000c0c81180c0d880111030400c182007040240000350381d60f0039800300a00b0541e4600c6030044100c09005402e0320303041c404508881c82d41e1036001c84e0710602405e10811240a082035440ba50f5080180281c604404800113402d003180c5c600041d40001e00451 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 265627625 1250 265626375 265626397
    0xc0215180601060c060c210905120f0a11010b1018080d0e041401030b13030c08160b0c0f0a0e010e04060305060910051303050c15010303090e070305041106 68
    0x1030559455400041c84828020425921a00302040d042d060403402e5a070714026507010440140c07000a101c2004862402404810200c00105c0404500d40b90b40703803c00914040c01c01c0303030012038168410000d940040c180b44107140cad240079400b01010009030a031541c0d0007200d83d1003050011f103040420702c10840c5001c06804030700e94940184e6201240b5080000160b01400041c900d503030004424103250103114080d280700850b501440d85985c86582805001909110700d010741a80300d03000781845561807039003032900400c440d43c0c4c0d00302c60380660b1141c014486044030b900b861040060240d050134400e0311540701c0c002100307510f4032600440c01c031b450fa068280d18906001d461440c0d42d000c0c0e25039228040296100350020314250500081551510345940020001c841c00c080410040d20190f80700302a0403541800d00545416001a01d18200304031004064891841c2e000000245948140484105d40c2c400c1000b01d44ca807180c50048042d110205c801a140d02201001c01600d820498001d01c0310340785c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 265628875 1250 265627625 265627651
    0x20402090105281e020706121103010f090501060206041205070f0b04060903090503070819020328060b1503070c150906050108161215090c0b0c010b040c0215 69
    0x20019031058603942039011841001901c810030704019040000031040140144800b00c841d9a03a040003075a408903406244208034441400e00d11308c084a4000c181016480c8c0d40350b0741c4940c1c407a10900d03ca2900740c0b04011420f070802000007855400403a50031b005941203a008403c44513011002c2e44c8a900952048030405c1015503581c020038800c2c801140030364410362000c19110910305004000c182150070481c400d030020001000401c80000e0700042e9001c000b50f000024001a0000900b0110741f006c98030440280c0c1c6800c601c07038982959401070402e1107503008120016600b400d11032043c05102541454070300030030106484a01601e1000440340c030440191540144602c0460207407000b0324402c5070f100d51194014803a481042c000062411180c682c00f9030144d150081c2603844601c03403c80504900c40040c520b4150348a190031245900d03400501c04441b25950f818486581d0780310400380f0155501e0041c0220413841c150281c091400b0142e801040380c1155040054407200d00035080142d601a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 265630125 1250 265628875 265628887
    0x160c0804031502070203010b150d0e1002030702070e100b0306040e0708190203071a0417070302030d11010b090910020a02030d0f0c021c0504060804021c2f06030103020402090105 78
    0x810015200e006038107060000d130700c4103618418182902d002e4800c0354800c8440300c402c20000e41410702501c00144154a0205850f442e502404d07003040a08003150301c5040c0004104885907400180b002c084452180400c56503a6850007100006020307802501d200070070420200304940b50a0304007000020701175058804803a55503a400b0301e07180499029680130b05801b00c8900562805104050081c40810011034103007243c15440c20481c822405500780200c00c038040d60250f02c90422100018503400790450324240c192502c040c02c00b03004000d01c5c010301c0d800c05284884c07504120040a01400110009000035607001441c3e03406904203005150462000740010905500d00d40203094803075204182c001038441c24508000d080100b641d10344c64034a010131600740c60740c030350081c110b404542c1c4d1880c105820307441c0c40c400641e02802038050807200ba1500060a014440f400140d1680313a101494081d2201c0c03a40502d0103030018000603010351010042c801013005d41003940060500304014035005107048 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 265631375 1250 265630125 265630133
    0x120f0501021c0e12160803090a0b090a140c1f030f0f0f060501020a050312101509081b0a0506030a091a010801050c04140112020c030417010c08160c080403 68
    0x4000248025100d481d00840b00402c0f00a002c102d80141c0055111898400c0d40074015a6040e40f80310020b020074000000103000860510000c40c2c8150b0041c114140740c14807812a81d5102d5811030180d0318030a1180782c1c41c3d8240e200180c0b4400194001c1c114807003040000d8070000004c0c4241c07a2150078141c44401c1c3c81080e91701e5100e410144c90040200140080003503a1140440f400d5030480f1b4159400b90040c100403d40000035520b030720b0140b5501000781d541d0394102d5207262200d940405050743c8071010881b185608030720345006680c640000c03241c054940c107034414012502c0341026034000c0c060038414801d6061410046130720400700c807130110301c50140750384441c1605064049512f16040300401400a08400e0250a41142c110b80006062030b0802c0511429582c024400f070b030500c210719060180c400c0c07164058880000f225415a038607241d8030314210902010401c1450500c0d440c0010780d1011900601001d400390401d55002c1e040c120210340e00b5207820000c3ca1050341e0f070368803e2000000107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 265632625 1250 265631375 265631407
    0x1401020a0513060807080411011b05010b10090506040b030a090c080d020d090b16060f15050109080f0705060c01060b030a09060513020907030c0c05060702030901080709120f050102 79
    0x3100c101d9840caa5625a00000012140c08603004541082209414401199400703082d058016070003140d0301a00006080c016925006c07030341203900c0003040b52005030084c08810b601c090a03500080d81c120320841076202040f42c01c443c140c001c0c02d40c80403041c442402030050040c00b03941e00c21400c03000010a004180c6400c04101d0190b0300c00d45640d88000c482c18030269042c446480f10130b81b103060003120a810300c5100c810382d000d4112808040910306040105009154106043e401e225050400c0107408020f00301c1600740300f41c05400c0c0815000b1100191481c00083c110000c10402000b038504541072038204006503000c9140700900b5901c1c1c410204a21070100000d50042d44610030002d008540742c43e0100c02c2d280024100200941d2110400b409a143c41f840c203680b011440c600010248400364080e07659010709000903041d80300e04030800980540000090480c00703803d887d60310241d652030004071100345040c000e81d84407410049071500010440208440c0c0f40b84502c0026042ca888181400702c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 265633875 1250 265632625 265632637
    0x3070803040c0f0f09050702101409011a0603060405041b0602031201090c0c0308071403010906170d170c0c01330509060609060f030c0903061501020a020d140102 71
    0x11002062000300b103550a18480104002d42451000034907010b690911002280b05801082e5107520008100602c20300a003000384408070000c110113010110400140c2404a0707030800503610303000c901da01403104908a119011801402c1c6450b50340c520051002800019000720340d107954103641c2008580e2030000f058007421403507000790b17114590382442030321101c0103030301200c113980c82c14150892103607021980c0b400c07164050811400325283c1200c110751084840810075025180480007040d9500c83e83c000408a0308c070304031f1100346403007004041900c8102a40008000c00e42c601f290b40301212030503413070319403182e12510254104900d54000c24255900300d02401981c0c6000a0401c5c0c80c14021210400e00c001e1003015a465907080401082c005000a07200500c140341c085580d40469681c0000c131003034a05010360b45601d07814003204000441c1c02c07038445e6a1090040d100000e03881c500402c0070001020b8143c1c014440d10b803c54003800780300d138400031065404c1e0905542c420f0b2049001d0004047e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 265635125 1250 265633875 265633883
    0x170f0d08090610051003200c0106030213060f0303110c09040302010b030f06070905120309031501062a200901080a03090b030708010302100c06050a0f1406060a120b030307 75
    0x100c2440c0100350641010b60007082c9010300c80a40c0410303c01915441803501d81000103043c0010843c80c03840c2501c1c400c51140400042503280090013020300078042d0000741c2124070942d1880329946088604605981d643d0081d400792158280c01080070911486c040d031144003610055900c540ca030703c000704900d6001200c043e00942c0d1030700301160032803c04000490b000f08000f0050480d034182000d00818061283c864640b0903085010301104461051084500e4940c0080448418002c05150a05108000d20811020420940104d00f00e0b040c85a9161a0b206900c0545c1816101a41c1c803040405a00d44400e8a106040640712101d41c584643d00c1e406010008002e1031070350a58680100344030340729040740c0a440d41c24018464440d4000c0b403014152581100c5103a01101800340440300001001005001d050402040c0300c246000f07540b0620b030b030802142007484041c0543e640414504000d880e01d41c2c02060410200107511b200701c0700b21001c020b201070041480c040101c0081d255400c0f40c0d4041d9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 265636375 1250 265635125 265635137
    0x80d060b09120c0604140a080d020f07061823040614100c0203060c0c0f2d0f0a0b1803031501260604020d021902010c0809010213170f0d 60
    0x38640d403421442c410141003040005050080c0100c1c0896a1170040e44282d5002a164050040c265a0350780d02c070324080e180c13a01c22102120101900255a10039005404d08030303014562001c22001d02c2140b07006601c40140c101d1255a91804109140540d0001048102e4080d20070799505103a0ba6400741100910300c2150004150b01c0d900c0400081c850540d4025040c00701e01081500140ca01054555111810340c1c01962500c030750f03045440c14a129494904518003521080c81d44241440750030303400404191000354041504035601660f500c006a03c00c02055200c454450300050941d00c08036400300c11031030540790b54003044d404145150070544115080c10940030301c90346c0d0f6581c040c0c0c1d00a072030848820824880052000c200b452040040c04142c051500016040409105a011100e480516626403615684502c000038001d00c005033b00000012480404603042c02c0d0140292412480030001e541440c9141c400c1324807168a0b46000301e0300c680201240035a10203428800180810790980320b070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 265637625 1250 265636375 265636387
    0xc010e0703020312070b010b090301020c1c0207050a03050c09150d0807020f03030405010818070317030405060108030c0717070b03070c0b0a140705030403090b040906090f05010302030a0b04080d060b 87
    0xd0304059882400b13081a06003130003a20041415003203060304440c44850719554a901040c046406032103150142e510511070030a10003140e11404610f0900c0f032009509036400c540d00d88080000b80c00040c4409056030f801443c8040851074882d0a05800254680044445180600110301c005c004030b44142c03540c40000c904a02541044009180d0b034200440180d460581000d001800b0110040c1c4120f0b80442c40110803180e414040247c04040d640080d0180c855072004001d1030b9065004550481e124081d503800060030740c0002003500d9850b50214090030680d03051144c84008084070410005103481149400a03000c8044070007107000340d030540d80e860200300c4107051169040002428504106150419603000c0041400c41e0315000200d13454001e41c0c0391140e040446600281d60080640c9001c0010300054000f4260f210000f2108191824040b824404014500b03c0b9024440690107402500f400400990003603c030581c482e2080c40d000d400c007401b050700e0000b01d0f6181c2c1c0190401180c0000d00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 265638875 1250 265637625 265637629
    0x306080c040207050d0c0305070204110c0d020f0c010f02070e2a04180207080702090f071d06090603071b03180b0a0e04021e0c0304050a05010c0c03030806060c010e070302 75
    0x200c40104103050781c0a43c940080d03030356401e565003004402d02080100074080300d01098480c3c401c170b401c2c1540044c01800303481912202580c259119283c42d040070300c60048242512400803404121024030b41d4003803c1c11a038120010b4448080700510482140a10003011a025a414402c40c1c02040108041d0389400d40c1d01041010080116034805244201030200f00065039522224800c00b8940c22005610380300d10389008501401403000003580500c0c02800c10410900803141c407441152107503141040202d18000741c15100c61500c00c415001842044641450b00741000210b80041044c41c3c0007443c441000600700d140c0192280c00c40000391040016000003620215643c00f40805005880c0f40c0000c0e403031701070705200100d400140030703e40114500b00e08590380003c7c5014080c4400800303582c0d00e00c181300300e40c80ea803290084910658281d400460554412842000721950081c0b11320000c9045032420340e40700d80000c001aa01103000c10a0201500080c026224440409001007207810b080d441 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 265640125 1250 265638875 265638883
    0x90c120a05041a040b0109020a0504080d21090317040c050a080c040f0605130f0f0c080105040606020705130513170318010203060d0f05030d05010e01030b0604180210020a060606030608 81
    0x3542e903401d0f103049403d03c4041398800d058981150141c800c01603940412070b4099402e801541e000e002c00e070141201d6414825003004800c3c6c3c0614000b1120f03000400c643c5d07008012194040c0010740000c1002c82c2e041100e40607807050035001806a0ba40c400d80984d141c0c0095001005500300c0c078456003180075241c3d01410a402100d05941041601307014084c20900130805001e10070003038503a0551112244008191141d11010030b0125114092044034241310f030240012b5000e00c00c2c80e000c0c0f4030b40741d0000740c01440820307110250350340244110174944c403510245020f06005081f07880701114204070500061a22200002c0803480c0465842c1c0720316007071114090442c0755101510850b40100b042184503278500d011142c0c19a80000028008046828120710b180510f4103085000c0c0d140c00002300e100314000360194100d0b4801d00c0c025141d559000c0c280000e03201030040108040c0c4081c1c12040051070310b88003003500d0303030200d10456100c0c1001d51550004e40300240c0c03242e070100e60b0780d8006014081080c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 265641375 1250 265640125 265640153
    0x2030c0d0801060c0f0201210605010905040507050301060c110307030609050c0a032613090605030d020114060f0409020d12031a090a0b030f011433090c120a0504 71
    0x1050050307107585003042c09401400070600080c20711410302c4a0b42c003103a000701059049400090701c031285420345544484002d0042e40101400300d10500800600c610b450f010f42132040c0396a80c1c855007140d02e004015111b640c2905011501810104222100342d242002044010b50181d10f0218196005052650a040c0001085409214402024004103002154003121100501d0114099030001c9000781054002c410700d62600c1c06410340e000444a0a581000017500c030224203990490410307100607402c841c4400c7c0c402e02404036910005a26140281c040c0e804c0806c090b2011a124815500040c4480150a0111508000b0740950000719034140300d201c041041032000201c2e030440031000100c9000004003201019512201501e500c3d0300d003408501e0038941402c0c02407103202c410441400402c1c1041b6407040581c01e814081c401840c504c030f10381451004180140f4001d001c428000d01c80d0f40e103c02041b444410600300400e48605e0203842103e446041c0d14a0001202d0900b440c0c201d000030381207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 265642625 1250 265641375 265641377
    0xb010509090a0f030e060d0513120503150d02040b130608060c09030303180a0203032d03070516050705130e07050105030f070c0507030b160207060f0203041202040b04020a02030c0d 79
    0xb0200c9400141003014055031039a058205030468484a1002039414803d007140201c0741801c06040c40007101c024803400075507511440f10070500030314910048550340802c42c0c03d400c1c0001c14968110b00c1e8109a0500800540003500200d4540f330030344041607280707448040800d03140703580b05010821030304180042900441048181840c109103034000a035640005800401e0001d61407160050301e40080001d80e603440d5001d4256512103014002c0510800d00980304001a580102c1c4c00c40710b044180ca04480c03141403281c41d41c0d400d03e40c800c641c03404d00080044045900d0b1281d41c0021a0507a42d01c100101c1d05090100c010038110340450300300e0b050401c95800380307051001c00d00600801d03104403150954420140e2070f280d0f10500060624920300303c032a5101521144000e01442044250444a100c02034041d4007200d4065030344510403030300d040000400c24010f800c18881400103160320504004140e00041c00442e0b4200d0000015003240c0c0b0890110000d6800003441002c21401440719035080c4450f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 265643875 1250 265642625 265642633
    0x90c0b070302100e1f0b0301110c010501050d020604060807120609020d11040b0f0d090807060c0806090f0c0a030603120305041509051c02100e1605090411120a0f0b01050909 76
    0xc0d07030740322681c2d10f9000e41d60540c4500c05d400d031020210302c1580a043c83d10700041c020310004030114106030255101e05807100c0e10b54240000410079040015100041c1680078003507524007403030094112071800d009000f41c4104211f9070003c002c000c0030740c0156006010420350060391880c0c010102800c680d5001951000d210b028403080222507091410303110f44400c85420295100c00403e4104014504180010710806011440380c1c14003419502902c905c010603251422203859800c104540c02604640d10078001038004002400d00c1c903100c3c00b51400c08060305001c94001d449a030f50408800c2c203a60343c4070000e55250100f03c00d0224a0540385000c0b900c01004022180c1c89032985a01c400d000d6080508480f02d5030302a80006100704500c507407a2906807800c011160140080300c0c0ca80c0103048039000605100741c000704151074032a1203140204d62001864a61042090034080800f00000060826000346850342c00401c6c000103550315441e124408c50703100356052404203c081c42024015410540c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 265645125 1250 265643875 265643891
    0x5030a150812210a1a030a1101110f03030a090605060904080901050306010504030f12121503060e0c0901030c080118030203030a0f060906120203060a0207170d090c0b07030210 77
    0x40c0480e0b2000c001284000e21030f0348224190150104000c0d42c07140d2003104224904106160320340794002071907041d1500c4803074011a83e90381050754602e40402d01404c507000c50a00300302e21398014168028103901d0b60003543e80d00482c40c0940c9086804c111a600401c603102c008200810126100e0554092002c50f1289082d06083d01d40c07420f18025812224140040000403a5035130b03001e4410b40f002503034803000710a10b2206920304065250750031458403001c81c401044803960504203028003041180800120b103001e40c03540e121100506081c10300c000c054062144840680e4980020280c080c501860000008600d410980741c02c41e00c1c0317146c51b000c0f901c0d440410700002039800b00861fa004000301001040420312001d03081c00602441d444203031740f640b81807000a000f04440e820a49000c0c02201500e00752740d0740540b24020391040d510300508a909034884446180501000340403800340d490340020703100b1030301d40e2401c10a43c00c07504142c1541c400443d090703080541c10410b40018180c0d00101303101c0301da = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 265646375 1250 265645125 265645139
    0x2010504031e0909240e15061b0322060806180a06170109150204031e060905010203010f050f0406061211070c030b01050a090b0a0b0a0c1205030a15 65
    0x3015480818420040765034290700591180d10712030080c200715001007007480c5003500140311816120040812045e00c03000006000d290110175688103508110003480000826010080c042e40940c01070b400500942c00010040d440c02c2000d0302c499075803035645583c0400340b4039416120042d6507000c0010043c3c40400c102841d1070794280c042c3c0000701a5039214194641240100152859810201450f5803082041e10403a405410014942e4050385d806200140e01c03000100a034840c501000d231002c0703080700145016003045c2e42c506140c035008510018445400d65102d509a07031081e8091802900001401c0c441032038905911400302c00212010004249000c101822110381e03020380444c1981c2e41c0781441c41c58886041290f680c0743d881041c008220b5100d10b000b0b1007828082c0a040c1c0149120304009c501c55516110f4103d0b00d4400418950505280c40140005035005d801d0031010441840d050100084026410910380c00c82a20b500c0d880f86030082c020300483e0002400d100300001000c108101103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 265647482 1107 265646375 265646387
    0x6040e0d0518040504020a030803070203040e010e1005040b1f05070503040b0d1b0804120e060a081821070812070305041101050316120b040c0806100201050403 70
    0xc0782d521000e100440700c0031100250000d481c0c010a0004c140c00f07102441d03000101c1d1040b20324080c2c4500c0c60741201c0303000b03034003d0840c1040c0e6028040c4a5210207418000b900d0191004c10140e802d003400200da03982c400250400c849024480e0040091040b07040f15a0207403c003044a943d00e030350303194240c5a41e00a4841020051400410441036116400003030348106c1140d03201d0351980c4503919281304184000038943d051004020600c501e94a44030080c001011068861550500d40080071001c2c0701c2c501c160071605a000f40d003036228505003504080c5c5100ba0070b150750702e440b414246451b040b40c0c4944014105460f480c02e0401003c1e69154100c01c3c030840c4548e0000880d400d0030360056030b4501003599400310324005148a11040c51080800c103007020400c0501103181041140442d0803502154100c07000990b098040001504144038600183c0c5458402084039203040d407001131603 = true := by decide +kernel

theorem cover : BRFrame.Cov 265467625 265647482 := by
  have h0 := BRFrame.cov_init 265467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 265467625 ≤ n) (h2 : n < 265647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
