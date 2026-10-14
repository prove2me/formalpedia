-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3404
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:08.277591+00:00
-- url     : https://prove2.me/submissions/82064eea-e288-4da1-b161-04032dcaa4d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 612050359 ≤ n < 612230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 612051609 1250 612050359 612050381
    0x1151107031106070803130b1b0d1112010608011833170f0c06041a0a050f0409060503160503061305030702040204060c020a06020607080f09031228021804 68
    0x103a800e012080d620001705600c15200245510100d041d00410030180811480c0d0048107043c5000701d21104492860850217150703076014806858205039400524650103868507180310b00403080c1156074508000d00650703c2030190319003c049075031001f49110f1b514040d0080014240c514014014040f00d0070845402c4404006001d15201d20000a1014030701c0c00d00000b40203034140030700340b00d041c250140d520f8036070021401405030200348010424900d01c1070325034880110b4401019650300700d4600071501841055460810008085030209000c49a944a41c0642d68181c4c00c07610745640701d5140048030800c52007810fa040e48200b0010b00655100541d00c003040e032049003102d04083c080d6002401741d8006804c10740008040d5004002503281c0f100400e0014565400504040d0510300802000181c005205424140d1314101040925400701b0442c0d4460034604891911030501c00c004040d042d5640d10846901e451101e17143c592058a07100b00c41540040302c5074551028541400c2c00042c012080c03403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 612052859 1250 612051609 612051619
    0x3050705091509030c1906030903020312010e18032b0b060c0105100b040b0d1a1f03110c06011701060e04060225030c020405090f03040e011511070311 66
    0x500440c0351651000b64100d42d0110b2825621051580c044c0751811040740d0f155440342080320001065520507a185006559040c503000c0b03180d001d41c0c141030b45180700b00e800708120003041c8400000c04140540300d19018a0400d2203441041d100f44400543d03d008048600c03540c54a10080d0411404d610f010660b00706d007464002241c0a017081d0009481a00020401d0410384d459008110058909004a5001c0c1c040006580d04250a060141000c1c0c003501c10f4240d60143c3d5202c02e01c8015488002062449200504694086400751444585041c403900c06402003401c1003031881000c0300c1c1400b9202c200310030900901541c0c1c038027202e40901400f11648031120355a03c0c98045149080b04101500c03480c0180b40240c1d4900c0b00c10415204005180300e0302030340c1d18409a00c800040d62100c2c40c42650b54040b17030042141d0b1216017125003002c10080c42200307a440002800620398804114140c1201e4000e504c0055650100c1300c281e981c20000c110b4106e07140c11810080c400201c405000000e44d28000d40703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 612054109 1250 612052859 612052867
    0xf010309050f030408010203010e180304060c02060d0f0c0212031e061f0c0c090b131d060112020a1d010e09010e030406030f050703090b180c0907081012020d0303050705 74
    0x6241800d542c0306800040b042d0350000014071a206412400070340142648070101d0304403485400c00b680343d00dc0d034041e03a010080d00089440555803040b055401c0d203c69000c0c10040d00c007020001c0c1b4014a0003182c4030002d4020300d01e1900451910101741c170710400300f410b15803c4c1a4010080004c248900502c2581d100d9004011400707090303d0040100e0120001d9181d00c0c0801c4402e05022200fa6134990240112505215544400740c441140501c409202c4801c04602880054180e8801e500c9028600030103220315400041d401c000645030404071802540c03081086601c0e04100c1d0a040c604500503200c804102c40101f240d4501c80304110362100b5520300000350b22451881450441d8420743c820710010303840750721041101c1424454a6080702c684d08040010300c085564022803800000d000e02950074020000b01e0011405006000210a0050101a01e07190480000d00b0202c0b054031441003484100d680410f802000f200c500030116001810300302c83d032580e55070031409020000c00f15010410244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 612055359 1250 612054109 612054133
    0x5030a11030f070609031205190504061803080a0b0d0203060403110a0b0f07170601020a081629090325062421020609041a060c07080d0305060f01030905 67
    0x60b0252070040d01c0740501141350071035824020025400c0c510040c01c0c031441c1100b40301c5030400706c01e0350055842c1490350110381903885003803a40082100f00c01e007815500060240100701a441076201d841140030307000821601820700d0502c0344001c0240d00c002c0d05503002030003040200e4010391007458010022001c640030181903546600503010150707404103104504005002510b03801001c0140e802e92169401642e030f290000000b0f65807508400040c214400c0018850600407005a00d00c9089800c00e0303c44601c046120110303050007007075000d00800e2041c2080803c5841c000401211981e04403880008400c001d051030003400c182d5420030440d02a69182201450756151444402d17503120301d807448000041c901a000030420f0900401005041840400d00005980b4141944d018940940780024074600070740810b00c01e0f5024841080e0b2080003c10690480500054500241d41105055655101e5800c1044c3d090701e2007501e440f0f0b03014095507000aa5035102c1d0740b04030b14840c040c0701202c2c5000184 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 612056609 1250 612055359 612055387
    0x7050d080c030412030f0305240103060902040b04080d05090d030e03030d0e010209030f010b0a06030f0605031219020706050d091a0901020a14030f07050310180f1805030a1103 77
    0xb9401413405250000c11003084c1604405c2810708441141404e100905e4901c4191042081c0040030410b107140060080700c9a91280d803100c0c0190034044011907482c0c0c0c0f80c4c080401c2d1500144110801d610550720881d20300c40c810000e803000b502015001e507030b0019403650240c4000e80800d40f0305801d0300c001d010b02c06845585000e4188480b584400041c0d81c2c916250503d4141040240041501c2e0706003602d40d0100e461f4840c95a0440b0958a0001600f800c445032a2001d403115034001541031161840c0020b00106900007840311600107620208070300c40381e800c242e84039441d81c45000701166007031146907181b185035003194002c0f03441245400e42d003e039580c035003a500e028150762110300d9070360104d03c448141c0d4112007002c034441c0001d190b441c1146041003020b00d02c600000d1400040150110220b40e070800b8854a00c1d020b00500d43e4607082c00c5501e00c400340020301402c000070800b1810000380319204032001c0c01a0740c445400c80c010318076006403880166020155180207420503c03007080a61500c0142e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 612057859 1250 612056609 612056617
    0x7140c0303045a0605040503040f1d040828110c030a202215060e0a0303030b030c06030a060e060919230a140a0b0307050d080c03 57
    0x104081140d00410798401540002030180105180400003000c2108091003026240c04104080c401c40c4008209920f0a0848600e031050010700c8142010144810424080003400548500c24507011041c1c1e0742ea20109001d841290084603c040b150b0080f9000c01c03442c200900015052034102c0d4000d81040048000c00074507045440e000448404000b072001c841813025604840d0220010f00d2a8202500e60781ca00000c41d84400058083c800c43c203803100d40f640d1540d6044203500f4006c04072242028907602025194488000403000000e02004c200c4500604181000300c10141401c01d04030b0642e0703000c1d401011a03103022681886007080c9a402070343c0d118000c510800d440103011401e1494201d00d60049407014024900c140501f004008000c250100000c0d00c01c1140900130581d04005410f0300341c03020000b0041841c141c100c03410800c0100340f54026401e030024000000714a0750310390084908460701c0f00600355043e0002c2400b00241d02e48042e840c071445001d010341601e002c04141e09549182d00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 612059109 1250 612057859 612057863
    0x1a010f0513021b0d0e03030c03030a0f090c0602010c0215010b090d0c090e07080c06030f22020904060e06090706050a05280206070206060d0b013f170403050607140c030304 75
    0x448400c0d0012140e17030010702d050000700140c0041d0708040f051030031a0340300e0200420b94544980d44401c40e07400c00c1201d410540c46c290300882004252134403090005c0c00303003103082f194602502c951600d09003100c01100c82141261240c0c1c10f9030341044029001c0003240c01c0b800500341d450702c010550108810702d19219240700007182c04010101d1515110900b810325807801c5c41c007803141d9400d0007000745200b100302c1050381c030411070214400300c10b400003050801000100000794000b40942e040208220441e4407000705500716400f191400c1d902e14014030769a16203400f0b5000025824070640c100a40607070042c210348010b0a030110021000c070558203000d55580c8004100592018050000d12501801034a8104909441074034030300d400d075211700340b1100c0c041c45aa20220240101c15941c646a9003280c000c0110f0108074160494401c24401c5001813a040d007070703c003000740d01854200d90b94240d003142c00704c99100380645004c4c1c0d5262030507100c105044039000e000c18810403440d401c100c000d0000f148554 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 612060359 1250 612059109 612059113
    0x40c030c120201080108060601092c0a02070530070309050306043e061602041b09080303041208090709020a09090e0d0801151205131a010f0513021b 65
    0x46450b000050060b1410f0784104200e40248041c040c403660301069910507074109510b281c1c4071003051401e801c4510408041200701c00c0600c0148035801c1401e030000c0036034500400490b00c45072100c50040c8112540101c0c090700030b040005021581c641c070705015044d440d020341003220340b0399a20383c003190a0000c04c68003140e0700c1506c000510440050055013207104103e03d4421060001c071603402800603400c0c1c00040303110340c0010408041081c581c40080c0150790b4081c106000b01c1c15003007004a0300a0396840010081402a000803801d40c90000c140c4e0f1155402c2404038000240d80042900d900d60050708900d101c2c0140c01d00032840725000d00050100c48003c0e41c4840000f8a80405c000840e08521400e0300a508403000003203441e40e204040e14103564180740402c9601041c01c2050701d060064507203100040782040d0410036020040c0e100f0340881801102c4e00c500c00c0c810b68442d4a800c02003405001d2003140b4104084c092403c00500c03030020340038001401841d00d8010380c8003031401d29005d0341c014115 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 612061609 1250 612060359 612060389
    0x2030406050601230301050d0606080307050a02010e041406040207020406031b050a05220b06040f090501030b060607050a03080c3907080d030905071205030409110f12040c030c 77
    0x2d540d00c10252604650821038000c501103401000c003009101c18400c5a105400b803010070000c0c0800b5030b0081d00248039a5084030b5481080345415a103903402c5040990214100c840921201e040a005844c00a1136182a01c203066590404200094005407016a041507031880d0120006905481d985900c0325070f041110b98040c40c102c10841e14005641256000b500141a1440c00b003506541d041614080085c000c01d2500001c0c0102d0360f00e0003203074059004036044410000d02d4a80a61080c0e050f40c1c01761420b411603070707101e0080c0680c03032180f004001c103682e00c0660070101180c817640d0719607000311015445900d00720303c2e1841d001e01c040c844922108407000b1500a01c1182908190362120a004000130340406841c014442c3e840305000603d80f000c2c581c590090508102e801d2050502a220815070251080000c1c10007940e250040c0c0a08010b03d8030380409400300499083c1610014141080c21510b06001c50ba1035081869000c2d000719081d401409021001942d03036840c01004d844410001014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 612062859 1250 612061609 612061621
    0x2d0f06111011090603060328050c0a12020108131a0610020f072102030102070302070509071e0507020d050601180c110d0c0f140a12020d2c040203040605 67
    0x14400040c0c1d00301c0000c0d1805100e503081d0340110080d9000e200d8200d494036200d07a03038000440d007801080d01c0154080d8202c0414200205110305500c5541405a000c44894801d420300b8004e844123540201d95000500084100056102e0340e07000742e0103020a104152400d105079a604900c80c2c0480e965102c000540041026504101115070761000e914801011451003001d91350780c0700c28141c004c0030701b4411224041003041c80200100180143c0c054001c640d2000c45040094407231800d4015140b06407200070126080c14031410010101c0b0020306c4801d00c408090300b0003961698400c0f9000c980148504000380c003c02c10a1000a000380015601d0f014000220358080c8100c41d130090079003040c0880b1a070508410800014814442207103070420b500d07040300d1414004980c0000403001400d00c41c0c040402c0c4a04007022403c2e02945100301030701982e000d00102c2c2a40c944900007000707000180020f85425420b904001c18102c1c8000c14042106c40003180c20129099038030031102511400e03191021310403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 612064109 1250 612062859 612062863
    0x8030d023001170307051e0111031e06043c09080702090414030d15060c0b1603021309050f010504110409052d0604152d0f0611 56
    0x40003011030301da19001c00389101000e0410321041c0034002001206070f03030f60300340f0510400848500980090840701080c010f02c10715051540c1c3c40800c8100b55080242200441c01d0480a890207150140b164040b20f603466590802c032203600800c2242c0c402d4030b8400501200081c49104031200d4100481e5080311005603880140300500c01d42070b0246185012207120116a100c815108d4466040f12810843e07100d0b420308800192800c00808014080000d440125090651202c0380c01c1d0010081046010b654107010303150307581a0380000e0550010180010100c01011040f078803401603d0074014204541e400d081a60310b039032a000b8441a43d0303102c05001003030000380100e82c0102401c54040c0840e107140c120b0000103000301d100741c01e101e94803034001c20306120740f8015852a4900440c0c2c206070141804001c0f0540300d03000e0360f0003801207150502c0c4c04640d6407540700c54401c1c0c0c2d400958200d4a4030f074450200284503e0007003c410f003041010000f290f611200f86640005140c950344070510919900b80c124 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 612065359 1250 612064109 612064147
    0x6020a0512030c16020a05041509060905060108063c0306101508071110050a0b040c091511010e0109050f0309013516020106060804080d050c0408030d02 67
    0x1001d19a0180304200e008400882100c15440300180050001586407002c106490210b412090344142441400c0000081407030150044810f2140244140c0d555400d01c80c0803a034059940c1400100482e0004601b82400c10382d032031000d041104050003001000c815180304992000340500c000c0411001000f0701d1030700300040c17500315924503200280d461420000b00c885814460700c46090228030000910300314040c1c0f84140034640c0c2c04054034282c52030002c49030000c0000f11461403040703142210024040c10188112460349016880d4401e42038101543c3c80d07054887c11000c0d004102c81c1e400c44010081c420700506030360782d0441c00041034020682c544541040da40d203003024150b42c010300403556a80c0c2e001414005510b01c1100311180203000a1524540c4604141d40040d00d18120041c080104c00982c000c1d030a50803030780d0003000f2450b2600f00440304000181d80160050400f44240140030000d40d01ca203401002d005403080c901951001c590307080d604004a003100066001c030380800703090f0864050b1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 612066609 1250 612065359 612065383
    0x309040c020102341b21120513090513083c040b03060105040806090601140d03170702070807120210080c0307030b0102010b0d060609061715070201090b0106020a05 72
    0xe81611000c200b26810105011240504100708584004001c00e0103120b0800103005a112001803081c154038150380d03e01031b071000c00c136186028001c1c1c3d0820035210303409403440d01c4030101c03454905515210b5103034050000a0421a0034800030300200002408410050171001c400780c030104652036250118003242c103400d440d02d030440c1140500000c03000e02030a01300c50a45141603006030f242c6d110040101c501c0d0003a504440240e00c0307071a060080002d0000307200c0b8121203002c540307228040201000d03c10b0a140900c0000e02240200711407103508001e0000b860f03400552481262107069895880610b8070303695030310105141e0b0b41c4812040039401d246070045040e0304c4508000000b8200030074285182d1000801403400c02d946d40044030a568400c0d004410f244000404040e00f46030142070000043c1418820a2a610f203400000a0603604148403d13541c455128054120805440c00b90b04000310011700b40f404655035100358070002801c54002d280600516401003020301414540507191044103150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 612067859 1250 612066609 612066667
    0x36030102030408030a23180606010318150b030d0f11030a0c030e040e030f0901030b0409110d1a160e010905090117010f11121003080f0702030309040c020102 69
    0x1000080745103241140d4128091700000281d10a4214444003041c02025000342c0c0421081c080c0000d2404101003144407940c08000d4850740c1e220280190101e803510b0352000300a0344a01100d6000c00c516594000c804044030340045010000d030303000039041103101815035011840c0005001055540550b03d4812088410021882c0c69202d2a02500018500000504014410b0782c1c0041a0321560042800d02c00f890040360f480301c0184080784c1c2213400c902102c50000e0b140842421041c03401c1d00403003038561741106105600c20036817014440c1400d042c0794280c4505c48905003030589100060b507da40702c0c0a02041030300c0c048a981b60700820556491503901d0400642290500850b038540c020281114102450034407842c4559070f01c80e015001440d0840341d151314005030003440c241c1500050030184040303c0c0307040f0f03541c0d03030742055000303461590102600303404042c820f0007102e601d006c004007150b41c0010201ca0500e4080000103041e101d41c09000c0c0010303500811808959204121280a10b8600d505 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 612069109 1250 612067859 612067861
    0x30c0705011a031c02010e01150e0106081506090d021e15072012030f0301060306150807050a090e09060f0705031306020a030b0409230a0308040213060e010803040f0f0b0d0e033603010203 82
    0x1040c0360700c400b1400c1103f0311800d40041e01489a43d500c2080e000c03829409095400b5441d011741252902e122210182406440f0488010420b1010741044402c101d61041074991039034203141080e040c041901c8401a000b92482c0394080644d48100702805005400714161940e070360410400400b941c1c07241d0b100084200910300842c1c29950024400e07944540c0c0c0c2c0c545940c5500c500c1c242150410f1035540907910030311444081c85080e030f10102e29584601e044409028a644511000311030520045402e058501401d81e6090b0008500d034008011103e00c9150205607a280303c400503040301c0071040210b80050107030408080e0240c0b081034005550000c034011700550100ca4034064810840240001e100c0e0810225148000e0403d501440c0940208552a5599a1540582607403a0300c1400307052103240d00c00c84000381c0f18100d0041c003010b94000e07038030041c00c10700e21102400160990b944c8004050006107c034104400c080c49220085039245460620310036602039404110b400700805050003a40100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 612070359 1250 612069109 612069121
    0x10e0106120f03120216060906140f040b0408070b160f0503060307030b0603010f05010605070507080715080709170a0b060406060905121002030c0705011a031c02010e01150e010608 79
    0x40b010020340c54050902c000414a10100c160080c0709600340c01031040000c020813424040d90742e2001e0401c1d4481c6004012100e510031112458203030480c0e13030b84110a10040050005401861440d0304030b407045000506220321991001202c1c90100c8140c41d525400c1c42e4101115580f001c00109074030742e01d00f4041d00d5424400c0110380c440069000113090013507a54045180c40d14254440328580301e030042c04002d956182c2c840103006500044082c0c03994400e0b6140452000c402160140840e8007800f090a0110031900c01901c410300002c06182c1484070382000002d03481c04c000640d4401407a41805049400c1a625103041c107210b0140c1385602552a041c3e003440040e0f000128481079560031255803501c4200c0705038092070700d451201d4021401e40080180400303550079501401c116846100240043c901d080110441c405810410070307416071000329100c032074041640340c0340c0d0641120310001c50801078040c441801d51341032004c4800488030181c42089000e405003802d5000d050b02c0c1c80c0c61740640c1014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 612071609 1250 612070359 612070373
    0xb160e0d0b01060c08040b0f0702120313050120120910020718091e0614070512060909010e160801050106020f0d050f0d14010f05102a14010e010612 65
    0x500034a0300740248455484c00748801c06042e00d004200c2c4406503582e524121089003117036003014004070b0140783c030314400b000d9040c03010061303a40500783d4282e0704043d98600001141c1c00803507541c904452442c07003814002c250300140107100e20404840e801a5035010240140544002080c10700c0c000c40d003064005000c480c1222040144480b02100e0228001103581850003480a00d23003081c41d10000c1d0080f0b241e04008443d040710200d03a554084000680e0703a030320800e4a1501c240014400010b0044d80022958908480050b8000a00780000502603e002881515002403480700d1081d0740c055090410101c03009000d52409080b20b4405030503021003e0701c0c641c1c2d072202110222800d025000c40c4c48a40c2d14031000c1a1070707030b21500c12020f01c8042440816842c1d0804203000700d00112882a00204c1c46092034618180c2c0f400c070550b104a5400c1d45000d42c8440f41c1d800ca003a20340b15a180c00a04d80118031007156602086001e0400092443c100c0c03134946003102d0790781c2e000800003110780803d44080b0341c1d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 612072859 1250 612071609 612071611
    0x20f1b060601090509152e021225140d08040209070f0503130312021603090806071b08040801020c0f0106051008070315170d080c040522090b160e0d0b 66
    0xa80440d0b00305020000d0008607a800c7d414504615140340f81550b04c0300e070050b01d0907042200d24035002d85002c4a40107540704654403400541001c030010040001c5038103c901201c0d11200780c01510421580012075046604120007100e070f40000854140500c8203516246403126041b20369405c2040c065000094050083c0c0402420628100d840320303403c00926000b442201c000da540c03074200b1507940860003842041707580000300980c0007560490020403040400070700b150150240792154120151440030440c904c0d690014106c845e10410301001903441000d001500201d01c01c04040c0080890000e403942c01c5400b15445030703100f000c020301d0459000341c100c410703142c02110524000c00c0c03001e16100e080241d4031655204103256822065560308406000c1200805000680c1d0703017405c070b074856094204103400307140500d99002c4400420001510036189814021582c4007001040c0381c2100e0725203581c000030860704488003041006010f03150f9a8840081c00401204480003222682291694640804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 612074109 1250 612072859 612072871
    0x3070306050f0907020c1309051921050313051009060203010321050a1b050a0302030307030b0109050f0108060307090513020406170c040c050d0905030406110703050d12020f1b060601090509 83
    0x19030007c881001c5509604003501640c0c205040b903070b44129840c0080700741d2081c01d82c240c80c03a04c10841c50302c0813115034046151481c01180e642c18155160009409044000f81c1d0007110240310341040c52183c00e00b140110049107020f4400107849600d5820311404c000824a442d95018507410124104950408252400780354103141620400707003500810054125966400b502e103208142218041503400002140302d606140e03403e00841c51081d0055481c10903e015a43d80000f000d8012507155200303180321544550300070102c54010b6909c001c0801160307025a000c0c951311000c0408007013541000d00404004041200040c08010380107010203895005003c940c80c4100e03114000c80c00c00c64400d80c00d40e01051803035041001010030b00e1034816500d500900c24071011500e04c03000c650b03013280049060000c80b5004009804a0402124120f440802c400b1003070584582c06d0161a0454a02201802c0328042d140e0340003401c0c000702110107142120003041d07181080240082405540c503603421b00d0790440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 612075359 1250 612074109 612074119
    0x1103040b03042006121503070602030405091b0a09090c080103110d0204020d020a11060601090501080f0a02070c060201050f0a2d0e0114100e070f081b03070306050f0907020c 76
    0x42003c0c410002c0c5402aa58070750b40503c1c04a1141e081e150040c24083c005c2e04504800c216421203481030548801203803013000c0140c1c1090004200c1d50038144d48a603400746c0703031030031301000d24043c00c0625480d60444042800000c041750400c3c440c0906900c2851290100e605244405604d556641c0540307100f580c0d8168000d1780c00b20008400c6495540540720081c218036810b5441d501c1b920801003000c0140ca101c501c0078031611b008500c941d4001c0004900b80d86040c7d50710303003165440c004111207c40000e071100680daa402c0240d200411003c048a0005d45182e900210703c600b07003008076402802c0007030201d800503460007440340b048801a03000700030f1454907503520a0a0001c2030501e0002407000c80072241403942404900305070001e01e058a203205d0880711000c107204584070a08010b19940c2140c1210200c1c0d403010a410100b80590312056204040e030541d1050441c403050842e405400c02d40f010004030380c9442007071190746444141c0245102d01540d0f449024030b0007100081da20100003014034050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 612076609 1250 612075359 612075383
    0xa0c02040b0a090b04140c0906030403110307033b19091a100f2c13020c01200f1605010507020a11061806090604090608010c1103040b0304 61
    0x15200c6411080742039030001c00329400c0681e610016409010358902043c0708a1501900c10202240240c4039406100313410001801c1c800d15000740070042d44040c1065040c04104900d0110364402000140b221034800d81e56189078100241018240d0800e03815412590707804d4200f503003181c08081c08402039446080320f40d622019043c03504428060710f0360300801c0c100741c280f12a03d00403840900505c0000d100a450303030503500fa0703a10300803161848000c1c00c241c009a04e420392850b05200b1401031071681102507034054204550a400680004462942040c0c0381d41c02191280c0d1b48002842600c8003074005059683c0f0540103070004c0c46d40c2d0320450811208110b0301280e564407407141001c2c40c00c54260b1001c020041d40c02c00d820069943c03802ca681c11202401c04622441040c01d04600780d070000c4044500c81280e030f044031010409141c01001050b0f4007d9014000012001e4842c0a40707001815801d00000d80c031041c400f00200b100e0414405039142e540204002c1000a400c0411603502c05e810418540003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 612077859 1250 612076609 612076613
    0x1a0108040201170a0e06010305010614011809020a0311030a1a06070305030f10081504020f0a0e0f15132307020622060614040f0605030a030315030b072c060a0c 70
    0x34410005c8401c0320307208000001c010444150301003010390b000040104410305160004450284961001110046010710100815102500034203200c00f0300d405c01103840481084644071540041b90640013494840c00d18082c8e0140c0381c0e00100b5545c030b050310f40c00c3c07402c4210348018015104c003811000e83c0040d19000100010140034041010304110002d0b02c019624580c2c958003d60024bc400381d128034a103050304206490a150088200d511130100144a0341c4c1d544520102140014a8904004240484101c459580a00a80110540c0d2030005107100d40003801000b10f40001e00074502c490480020721100c2d58000070529030080560f261007103840540300c6401c800ca070303045c00c00411306420264046100040b140c801c1481c1030042c1c03020096805208a007200783c0700036115040d0943c00c45103c50340400d100c1e0304007190320700054a507070410395a2540c500680c0c8508941c0c0130001101426a0f148030401c90390003a03220320721b840300f8260000c0c038000010701c1c03882030003a048103005050b409001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 612079109 1250 612077859 612077861
    0xb10170a060503061311010203071205090d0803010803070c0518160c080f0318071a0a170a060e07030203011505091816020c031605040207150207061a0108040201170a 73
    0x101400014064035954100b504107a484810380e504201c41c45d1b401d106500c13205520000688101a030400d20345030a0811050094455a002e010f54035040b1000e419280003050807000214001d022481c011683c0d1205401c0034100181203800c000d12800400540c1441450740c50141c0b9000f403009810380095696540c3c1c140c400b00c0c0206401486240e020a5a45e00c2a0721003002c0d51146240510112440118005140e107408084c0151b121a00c03401c6040c546e01080c08001d0054060603080c0b101c800b00407103d400f50264070848511000b01d864034424891480084811500410141000e60841d410003d0000108042a004c401044008520f0381596940c10b8081c1c4010301d9076904035916414250700e84180c424030801017401612640025050301d0400203095041c191056074541c8005d41081d040001950042c1803d40c1c0713181c258030100c280f00103648000e15969108200000b0703460495810b09401151440b41075040c0845482008090307600070014a0728044401c940c1d40c003903514010140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 612080359 1250 612079109 612079121
    0xf0e0d2d11180601080f09010b040914010c051801300b0909030703080c07030c0512120a0207020f130e0d051e090109090f020d0c120b10170a 62
    0x395081180d41410814041d80e1103030a85400015540300414120411456484240650790742d40041c103100006400564082d013029045541040042843d40b418000542500d060060940303058141210101522500748111120400d0500f002410840d00039505400ca44412030001d05121220010146203080b40101103510841e55a0300b180d1100c80c07000c0a4000d101e904281400780d8090000304443c0d200c000203588903641c1c5551040090798604003080d91542110800b00c0c140110104004009001440488030032084801d12070b8584007540000485080c1c050f240741001441005481c0141e100c1024030003100788151141c2d541c141603039004200030444c40e03100445034000c141803410141e40c0031008190f102d80504018551154140c900c0039140301e1031400c14040303003001c3c0342040b021340e41d908014219020418010306000b08008050305449a40c807440c40007668443e04600083d0540c8900e005000007558202d42d142e810200c0604099008112101418400d20006080c2e0b40c0d590055 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 612081609 1250 612080359 612080423
    0xb06040b0a17040b0f0106031107030309050f010204030803250c0b04150f0e0f01020a0c150207080f0403060f0501060912050304030f060902120d020706050d0b04090c05010f0e0d 78
    0x200c20b00d40784c00c000c1c41214055400300e550b00042c10000070464031a028850700740000c040c181d40b5060555500358000c0000b8081207802e8003030801590400002032000d400114001d054007030352898481ea420b040d0a403411000c0c13038601241480008030640c80600340c60169400a03080c81c0136200d900700b490342c00301181e104448040c02d0039408110407060b504400c845483c100e08803100702800d4102c0a090340a030030650400654a0180480071a0015a035000440e032008001460003809071500e241c19481000741d01041c060001e01041000070a118031402c50051041c20802075041c45002402c5114520480b80507201d40c500c40d0050100c20300849000390780c481d214865103201c6140010240507800d40230b0344103050003100951103441c041150003c060703107a800340c50785a0402130103036030300d4100c500c51034002690703517141d031a240d20307036103c1c500810f8000c244070f0020760301d0300000608240a502e5094200801814009400c0c0c83d00f0540c010101da02c28548a44125114940300e0084861034407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 612082859 1250 612081609 612081647
    0x10e18070605090406050d0b0f06060706060e010e0a1515300b0913120e0d0b01051905030601050f030a0b0103150627090303180b010f08010b06040b0a 66
    0x40056402d801000402c1d40c60001d81e410b108080d42c031000c011400c06142c2000c5c0405443d14002041c21641440c5a80d00002c000c188905141c00c0f9210313001261880c0d00801151403804006221540e5262007241c0d0000300b5990901030340d4030b006a0700020780d100b4811507148050381c19098407138030700900403c000c0c03400c28409000074101aa0111010540003c50900d000c1c0c43c0075003400c100d0811403425480352410344034048001059541300c0c8500041d420b200c00401200d200c82da451603440785c90074841c260043c580001c2d6075040804015110344059058001c9051188040215490209809044a030110b03000180304080c8004030303080410140000300b08204503c004001c0012081d80001280e0038000200903854403250030604000d03600300e040d0100000d0401e403480115454020b00300540c031a2502041080417030b01401414840204121a482100d0006110380e00c0b407415120000c1440c0d10003803120340360000124406100328001c080d0203001c006254540f060007100410301c407289a1f20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 612084109 1250 612082859 612082873
    0x603011d1b03210415020a1218090507020a0209090d09050603040c08150103050709060f030b060d02040f02090102010e0a081b010e1b120c0f040c0314090319090e010e18 74
    0x185903c000d900070b0241c407806404141e6908006440050081e81c0950310403054480c17200d101c002580c006800003810000004a881e02282c040390070300030a03014603010340042003a15150301c100860004020303c00306a542c031640c000c1d9409903000c0b01c0c08048420039200582d0700d8076070b4100406281c0030340e00443d11910503c8251141ca0044a200038103c81c0903406881d020780d204c081c0350382522614414200510400e00382400400e481420007a00504020004214800c055000c1800d80303107218206000e140d808110030406507028005c020360100000050900d0120f00d654032482c034051072804800103240c12140b9600310200350b1001c200c1f807202c030084420005030355841840e00c2664850050003000c0420001d111000700007887da4506c13500510082040580c40305002c01040031450820401d902e58456220f80c5a00d61800c1d030150001c10003561f551303841c0046c050b0038400d40902c03c104020400d00108205d2030108081410b5400303200d0100e0243d280c400c0400001c2401909078a00da001d503903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 612085359 1250 612084109 612084163
    0x7050a050f1605060109090507180902180a0608030403050d0f1112030103031e1d06090a0e1b0f190324030c0902070812041a0a050603011d1b03 63
    0x4a100380c2503c540f0484000d41c0c2c0350503240701525010000180b8030f0b4010f84080c800c0003550041e80d44034a040c0000003401400c2c0b1340020701c03511f0400b10a401d4040c0c90744184552120140100b00141445600642c0303003130310716616290340c3c4c050704608030100310025201400b910320810340c105640001104440305004403010401e40780c4d10070b200440101b22208090600c5150111501d20701c3c402c076441d041c84240e0681c4079130706608200700440307920001c20404424982d4a54002402922907050070038054586080c5000c410401c0c0c4103800c1c1d400d0b070244015410f8100c24801c0b68403441c0e8040b081502c0b13411048041d00503000c00d0b1204805541c5c0002400d05521284505a048030b014120b1413200325a105502c1c405c81c4903500018000c01030800a0002c8140d1003c1c1c0190414818891041501840d8030442011201501c070490183c6e142d40503c0083d00c0c090103600e01c6400f1950080c510b29076034480c070300e65070341c404040c0030050030480301328941d9507805201440d10503c0400052900420342 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 612086609 1250 612085359 612085387
    0x90a1404060219080f070c03180f0f1208070305091306030b070f0305220c1703070302010e061504090c0305030d0c021b090c13030203120a0e04110307050a050f 70
    0x10101034500f02104106040b128414410140107000120344144c59440b90b64003224000303034254058050204c2001e030140c0c690340503a511002040c0c1c03101c1c0d01101034101980d0244030f490544c005680f1000c4c061f44003010401d800700310b40003584e050518a966070240400b05103108462192100321902d00354000003400f649000742d6128030350325034030440e1040d40c58000381e0454201755100900c250b1041040c10001c3d401400d0602d41600803501506d04c5a40c52181500d0075000040101c401d0700301040d42c4003016024000c0d0300750544540c01420503480c0440c100345858070680601071107191110400001e000c1d45101070b0018540100a42c0c5ea02c10b80c89803120042c0c54160a914014818182e4404100b10b15404041c401c200080540c60f01d900c4044907007d103500b110a5280389a40340c03110000069404000740e400c47d4441d44a8951500c21402020744007801150f0300b94015418244407140070802c2108403503000030305003031090300d03054038290880e40c0e40680c0b03408030000107000460904c0b12441c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 612087859 1250 612086609 612086617
    0xe090c0301110715110904090c03060603050c09070509090c1b160807080a050a02010c050f06101401030c0207050909030f04030c0801060b0f0301050906130f0b010807021b090a14040602 81
    0x42c9119842040540214030071511120328030003032242c5c1844100c07040e00c1c154110b40ca005010380040c0103030546a4407140112760443d8401c5480340d00c5588016410308050b00440d910801d0b44c14428145001203021070920700c002407010500f10700c0010741051003000c41680e101100c110f081168840722424111031079140f03041c0035420a0f4410f80400042010001503264103c652110250409020b035500545c0c0d10542480c04880a015a41e10104480020001f15100c0c0500c078000e0103180b4a01300e00700c080d41a00e00c052504241c1000c41103102c464000034402d048803025070311424240d4a41000c28218000c203441020714040c00640003041c0902c0c41440000e0303c502e90001c03c00030365503c141071311920940510220380f0b0f0041c80104010701e400017800b98002d601400c2c89080b14444440d140468684840d0104c0351656251010003e590100d107640e4040810700092140600c0307050942c080042c15060544140e0034000000c415051941003107113908000b200c2c4100904152a054000c1d403c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 612089109 1250 612087859 612087863
    0x20d0807140c0109171b04060302031506010e090403020312041704030c0e0f101e1205030304140624060f04030c0603050a020403020d0b07200d0801080111040e090c03011107 76
    0x1100c6a004070305c003030511030015103082d43d00e40201920034168003040000c142e18490942d200d41d0b101c0c00040540c40600c00310420502c076941104040c03410400140003c1200b038040381c00b90040001700b20000360000b0803904140c0f1192000c5440c0c1d5568600042800100c4400c2401c0040115000082184180c100016140d0381c0d00c0c1c1343c000f41c0c0c0f16555903028090440d40078640d00e03515201001081e03242c4d0071a004484e41e4100e296070664940910f0900d1131141d420880b41c0d688000208818403c4001c2503482245010000c0d03c0141003030b2040b22001010341c181480300420780540c030481d60f0b0f0307054122241d049490949549840e501c0c2000c2c211080148103410202e81844006410a003c6200719025a0360007083c00090400f641c4500c410303898010301080a0145107902e01054049101c44114503110000c0201200144c80034002d000500685c84000305130b0412070340d42000e42030300b4107650540e180302d00481200d41c3c0b10603001c0c2c9411a598491030301075280c01080304142c44603d00500c0914 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 612090359 1250 612089109 612089117
    0xb04061715100302191e031a01051f03090210020f0609280f140709060501030525021c09060305011d010e07030f020f0403110901030c03020d0807140c01 67
    0x4448100e071221607400807a01c1e2100705962000c14001460070810302ea1101d20505013140695488940d1604003d02640c0c1d0103040103500310003081041054189504110b00c0303854203c0c015450300c000f043c80196061003440064994a103040c00151003580014107140d00148250050460311501035240e6114001d0042c0c603010300c2001a00c021800100c480c1384002c0d180c4c0d00009450208000400c3c503401c040200c600c0b1000c01c0080c00070a84841e804010080313000003800b400c6103000c450364216000c82d404281890300b010300300074490400a08480c52000b00004000035449582c0e0308a080c02c003689041c520400300940c0c071442d402d0380070700d404050f501c41762404c0086989401031141400984100700850a10240062000c0881c8414403600302d0054200400c0b4a60104025410780c1c01121020450b8480850200203201c843c42241012200c1540d414401b541541c40b66080c510b10f07400064018643c81c521071042100f01c81c100c0700c40c1070b003188441e08858000180350b51182e008001c054002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 612091609 1250 612090359 612090373
    0x912110f151608010b030f04140609070602010f1406040b030c130c03110c1015120b0415050105030613050a0b2d191a04050f1008031207050c010b040617 67
    0x82d402040114160707a4040111030460740e64600d280c807009002001204c19469480000304040000c120b0203000303500480181c0040313801e01d6130007070860b400351a0600e21541400d18240c07144400880c7d03103800400a480c082440340499010070b240106421100c1d800014603400306000741c43d5039100108407502568240a81c0b4409041100366008020000ca903a0b0170400d80000c80d40e000c0c0d40242e402601080300030070b0059440d00e00e06150340e00c540c0c00361a5103842e0400c01007002089a07e02c3d01039000d210f020400d40d4101000b0079036403400103084c4032103818009100414000100400c046150b81328104100c03901e8440303c41c2c80707281b00040d0702d90304922740104400c484a98100c01c0612656a030074002400030751b980700700c40180c0303032001300c0c0030381d111008103200283d0300c03a406540e22501d460b84510455061060007000c1c8130200740d10a40d060341050120720690114440280e801030380d10300c1c00d180ca81042c00710450041c51601d00543c2d00c01d00d440c100007643c445500f004038504240005407089 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 612092859 1250 612091609 612091651
    0x7080312090625030b010c0c0f030303050109060b3001031a0a0504050d0c0c030803070908100b0303040b180307030c05040b010c0c052e080402130912110f15 69
    0x100384800b07200c207015032148250003c40c4c0c030a6201e003411040500d0003000440036030300c40881041aa400c1044003920000c814002c1c190035010f03250047c200000100035441c50100c03014401d0043c034400840701154060b0003103118001170811150319801d01d1105d105540e503898181c04181e80084885010140c040000701605c05610030280704680002c040d082d0261146421107034055449001c0f03425460f00000480401e1905014600c5170074261034a00040d0f003000c02d05454100480c0e0307a0b180c09414445003034503a0320080181d408803001480e0700c44c0c0750020864800c0d005010b428001d90036214010000050003c00e0150008880c4140c40404c003144881004691011040d0300c05409200140c0301007101b0700305a24801d000c8801020b807001d107611020300031a101e80040d0250070000d5418030901082d8641114004450603030307a502002204000c1d601c011f20310b2954500d000a004040310450341d070ba80203000c01c8400c420000b091701c024814403540e6110510064440f049018000040c41c81 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 612094109 1250 612092859 612092881
    0x80c01080c12010e13050105040501020d050117070e060d02060c0c100e0f06070609050d0e090105040903080f07090b2a01060e01090c031508030a020d020105060a030f05070803120906 80
    0x503014612500c4000c940c1c01c100e4040260180601030085601c0f0608689002c190b0a200d423902480c4103a00250340c0781410302d180003d580042e000701c2c0000b482a078411920520001d00002107600c031110500f855920703000094010300d2600800394200d0400201c5c0e0101c510003142c0b80c04180022100c841c411240c0c40e6041b81c1080c00c02101c1e5400400d02c0e03444405515081020f0030455100c0d1001081922250f0360b0340381003000c500210004514003805a601a01d001c3c5161405420180e808008400c0c0c0b030f4400800c419070280c10801d90301c1031103012640a81c410b4000c90701600c08800c1150740c5e803e010a4141181c403643e203600074a42804407001444102c18081d520485060540701c9403141d082403243c00040446008480038150740d030300040000c421529600e070013400d504000d991036031000c1074003a0402c544a034808045915190821406507102000003040da6000440071042c0d4050346041898903590f508150b841d48400303d0154640c03014441c400c5d10070540d01090b03540d43e07120000489 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 612095359 1250 612094109 612094117
    0x902040b210709150603050411190303030b030111030703151a041e0302092410050933090a090f0e0f060f0408030c1c0f140126100501080c01080c 64
    0x11121201c4d00400145210383c214a81090042c0f50080030003005800044101c1c002e600b59850407120030030708009054151140049000068000f0b0007041c40e400b03207052061200905000506665440c01e48400b0103618070030303001e000502c03600030300c100f2068504d000d250400d2203003c44424805644240112400c03002c9403c41c0e5000e8403942058075407609103d030100d415845070200c2e101040030411142d50f9016040c1e42440292591a41c501c1004140443d00004000c40c10740700c0264400341500d140c8490410b0400680c00c01e00e40c0d10b0307454100c0090b10040e446ea010310340441c241130f5200712840b0305620144441c9185012144225800140261641400c03114442d09031202400036011400c00002540d112032031010040c40c1c40c400d41101030a00048021118036507940d1007001071403400901c150350f41c100eaa244502401e42c903244a591440d84c243c0c202040c2529075001d01101000b0420000c41d5000c40b56905201660b190b80d0060790b201480c0300b0842c006950440402c03400003c00c0c1c111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 612096609 1250 612095359 612095381
    0x6150801060b0c1b03030f0a03140106050c15070507080c070e01080d14030703060302060705062710090503041d061918110d0c0804020a080715030902040b210709 71
    0x41e0603002a40c90380310403e0380440144076017501041000d20f222410380350003460310a5031610000346850340f615513144000ba0582110342481010007100500d040c000800112001b03200003600015034841104860901488500400710303280440c8071440088082403080540e4000c01004000b03070381c4c4550382c99842c0f0090300500d001c076080900f40c0003104030310801194046030f181000304280b59281d0200c0e40a6103d2a800d4815801400500c460034043c20491030102030000c00307140c130140c80440c01c6502e52075900d6050000d169034007100420050207000303840c01041c60846244c2030003040c02c03040303510b18001c8a10503c1414421000040031200103895001c0c3c4520750100c122458403104941c006103460602c10faa1910103100c4403c14200b517000d903510400083c0da80310f40906241c410311800300d405030825081d68000d640c0c03c0c859000d020f94020700216151802145211480c0040740c0141110300ea4070350401054001e0f1287c0c4041e0410725a8500070200031034030542d91b12141101220011498 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 612097859 1250 612096609 612096613
    0xb06180403080405070302060408030a03110a0203040608041502070305220f03020609010314011503060503010204050f1908031801180501020d0c1b1401390f06150801060b0c 76
    0x10a000c00c1c802c0003101e80c000d110300c1c101d42e10307036869130009081500641e000c850302d03600003d50711460a506000b00d40340600c0d180c007403606201880c070002e0349038000c034094041040301c540c0000703003885250301d560080140f451808560326113003810014541d6121240d4400c2c2d403003c0000d4004c010142500344011920490140e1851b1411341c6c0c04c10409900c0221254109600c40c0b1a48011150f03c4103180d00803d501070200140f0000300e503002d41550b034240d02c11480ba074410700080029441e100d40c03d011004048034100102007035003d101c50b2441143e00540d01ca48404624181240f5541750709124989098071010140362400c076801800b04007501402d070041c0c109030b00a54489000d00080d0958038071800f000710444400040340070580303007141c4c07260b0584a400310700ca4400d035800002c040d00713944611010080780b0340054602c0090400c00c11814041c0668924002c040c402e407402103100d1680c0c0864140308400344151000e1034000b0034000c0501a501e0303c00001492111541116904604400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 612099109 1250 612097859 612097861
    0x2006060a0b0c06010303030507020f2d030403171b1504021c0510020c07030209161403010b03040305160b07110610061e021603030f300c0212160b0618 66
    0x140c01c80c0a448e020740031000750b03c036004034010b000b40d042c004002c1191092040d0451100d40040c1920030100c1e00c4108281900108014001319056051140300300c8018000c2c940d69040d02d04182034905031200100f07a150040100039a441c0000c03400850140d80200c03107000c4800703403030300b00c4001207428114002e042d40c1c40300300880316a6082c0d8025001141d090010303983c910f51350782c0108503c03c00c111000848440da84842d0048190450040c50512000c9460a81550f041c4003c060980c0303c00381015040c0000400c4029010200442030143c50f58842030251072420b02e510050b02d00c00f1542480f01d614013a10340020b404c40443c610580c211000b076692034200d20903006080d200e4940341d825030001c40c003507443d030b40c07202812203c040e0340254403035074500b00e0400c1a00001058030750301c0200714481c90b0074845034003040030b03808104901c882032800300051025240d80d4242d103040c0b0105c0034540021000b04441150765440c904005100340202c88210041d42e6910802552600e030307600203003003e2500e81c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 612100359 1250 612099109 612099113
    0x1103030402010c061506050c060703050112030c0609060f0b0102010e120909090102120403020a38180607030903080c071713050306040f0203011508100c2006060a0b0c060103 76
    0x5194841002d000f07901c000b5005d0749240340026640d00d1900b1000c00300d000065080e03a8030340304124030360340840c080c40c080200794100700450b841000300d480054208803240c0640d01c107002c02a4018413100340e00420420400a8a104c5030000d0203910440034059440c2100c518142030005c14003518510602509501c0e009011041006090025204241c40d42d800e2001c0c0702011944280203006a000e0b4000300014611303803078400442c0f1050090406c001c141e00300000d16111103011a140490782d43d80200c0d10326518200c0d0f003614104008107d14480c49410140701280e03425a1040c040c41d0701990342e1200c81e6940b030b0205440780c840e5080040403142400c7d62481c203d0030000180212182c2d520750119101d030703680000791424400795410356504010864074011441c00348a020f42c000451401480154a080105901e9850300e8070803000660329400e4010f2003030310642054100222030b90242e0f80b80d0250520803030f619281260b03c2c502820341100b0100e1825281825606814040802071406a00315 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 612101609 1250 612100359 612100367
    0x1509050430051605030703020312130201020709090f050726060f010b1308101a0904021807030b180711120d020f0d1b020c0d261b01050f07110303040201 67
    0x2408000e440300110f002e022000450500c01040b01900a6004549850358022900c14415001e070000c950350500c02d50744030050340c0101c1c94400319000450001400c80082c01c2640c20b00c042c00c0e030020b0140c01503103000300e1009a0440740810b400c0c41c00c040407400c844070140706036907828162103090b008004000108075601c0030100034800782d0150307141c0a821036564000285420081c0342e0150840d0380341c0e800c400700301c07050809080c40348000700c50f10961820560003040080701e00301042002c0300410f000080c4510300a420081714040c001d40f28103203690300b10807070310001070b010b403541800a44204002c8240200000c0c1010a8482c0720381c1c0300f40b5000110755440029404803902640c00d9900303018a00c11a00180301d0300500300070103070003503600c2c000e00c200081c1807000c00c2114500c2008030700c162001155128510b41401403494400406090808401503c14040c2c00400c010803401d03441e00564210041d00118010302c2e80143c1380400b601d03508000d413010042c94801010551003840018050740c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 612102859 1250 612101609 612101617
    0x50f0a020f0f220b1c0209040201121107080702180403082802040305010e07080d0e09060d0f2a1226041205070506130501050d150905043005 62
    0x14840d01c280c1c50308407800400400e0407102d0f46005552904900801e0412a951400b8556000034003a0010340e281c0c00243c1681028002a040013402c0f40e02c102a289140d01c0400b080036201c1300140c0340d00e03076450105242d9101010403400342c2201074840d00303c6a9002c001500840d40b58480c051107a0341e481d085111812a000303c800707002a8078041c02c20f0100c0034801000654040c60000c100402c405d42600d28200b80c542c80000964480c170420304042d40d110401e480c0c07070300c400c54140d031050322140005038500f003c00c00c0c05059444884103980401100b0b5042a400960302141c0b001001c1d03006128056a0240d48150030514480361902c000141020101d03054081d07408046400710502901201000d4000341c00c040010440050301d01d06004007080150000d21040301d056290504902e4284620805882003078180800403480c8205081c6980140004803095100321040c56171310603800000c0c0c2003d0307506554040100303100d20f00301800c0b00e00c0c40991a038807007a01000402c1440c0106c2e09644 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 612104109 1250 612102859 612102889
    0x5060f0d0c1e051f1409030f061f0605040b0313030c0b10080705031603080c031204050109020108060102060928140106050a17070e0c160b04050f0a020f 67
    0x4445803002c0790b9034401c40262082100400c40507122181490280500c5149240c0c011134216004000c0c01c0a003a44140e14800c2c3c000714a5283e40c460305d213140464500754030f05810640e10b014900c2001920302e035512100e041e809a0840c10001c1d90f9452900f030f14503210380e0240c00c10200381000021000d10980c000c1224040c8a80b0f4202c80c42070050300c0f450b81000c4151900880109628010000c500041110782c010341000c0b00640540054000f64100c43c0c031161100801521011500d00504041070040e26008100018591011324292404e54002c0c4038400c1c0803804107040e400030806a510005070030744100008030090a5444159440d2185480924000284c0c1c108804e0000001038003800c40441e0440a4000840d0180c01d240c201b00030340c00300e46c00825041d540b01d60000c0402000103108012600580f0441c0a90740341c0d411440704038402d40c01800701440034486100c0801500b4082070380b00d14010001d4605071002e540416848150035803005e94080100225942c8901e802246030009030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 612105359 1250 612104109 612104123
    0x30816080f090f06070c0504021e180f0411040306050a150602012004050d0209150402130905090a122d0c03140c2a0405070f0f030c1e09030816021305060f0d 69
    0x3035555180e4a8654170045100bc800034451488043c0790900c40065455400f0444003407005602c074842c1c0704900d0195204c0908907607261380c04103c8107081235000a15004c45a254600c4554683e48064040c0070030079003a0f4004100303c1110f020f0124407100ba0781c151200104800c4048004d5003c02a4500c0301603d00484a45d00702030b105145e07600c0e071000740058071802c1000c0e140c50746449911012034000919581c141d40100044c5400240c0651029003d92014108270b81d410140341c641104c2c804003401d81120903c400811504501d401032120744001c0d10075540c0304001e00c02c0c0c01030002079000b400c01840259002c202000301c0c0b484cae081c5203c1c4100d883c0050a00154400c0c0b400281901c20070f0321003d01040c078850003c0c141c1a403108501000d95014182070002c040418801452801e850b10384000b490310b185101740700d607440f440700900150b8000e00c0080c3c5603045a00328546207002c20100704c0c8100810b91000c002044140103162007940c0080c084205058440c0610601e220001c800715010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 612106609 1250 612105359 612105397
    0xf01020c0402220f030503092803031205070e21190606060809030f12060609131506110303040b06310c0e0a030816080f090f06070c050402 61
    0x203600d551002c2d000491842616a04050405188140340100340e0820580300c0c1c44c4000510200d6000021a9003928007a2200050600514800d00c0caa800c907072003940000f440c5a40010a0540c0016205214205a00c1c200400c0d100c0d604140c2c5c3d03c0d0300500f18150081d440542c00d21a03540c16803000101c00800c10180c0721481848900c4645401c03c0707003801c88581c0d54911040c05400e42c40640f03680d001d20004019841c2071a0303000c0080850045030341c0e4050101c004400201d4540b2150141da64103100a080d800e41d00d41d94121401c0a0300e00b03d42c0c1c80b404410b850200040c418450300d0103001d5807440070051803560301e40d40c64203001c1807c020401a004000f1810040380342020095814030b0602218403440426030f001c02200690700b1070605041000926000440c4c01e903944080f80e000c0b41c1e88688981e0b6648500b00140c80d08920170b400240c0985000704a04601e00e01d001d0041200403000c40c0d041004151030410804180205103000d0900c1c0e250080c14001c034141540100102d0080388580c1080b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 612107859 1250 612106609 612106633
    0xe060f07050d1e1b0c080d0b06130302090601090b03040602090a2408070e090601030b13020703021509010501080706080a090c03050309040b06091528180602010513020f0102 76
    0x140c549080e9110b0f40b41006000c00880c0800b24850002c000c4c0c1d0781400c002c000d501c074800040c107000c240e85001c0c4c13541600041e030603c001c01d95400700c0280c0201600a988944060208800544591105034010700707034900090086c0d0300c528a1a02954400b903281401c58480e07480e5400207400c0319190769000042c0c800089180d240c040781c2080c0307210100b00c0440d200c00354854020807041006c0c00b10000d2110f1010000c02a5403924a0141c1c0f00300c0a1900092034002ca00018003500c0102c6c00307441c001c40c80010342d10141a408a5022501c01000907211095201e0703132502d84c00c0328001d01c910503481d0000d407014811940318600c0c00307810140b601c202080e4a54240c5480d040b00b03005510840d881d900000786070007603003010b0086580b414011507030541058a14070208403003800113480c4a00d0400002200003085030700190401618034941020a04503c6040016100303007103514100d94000025607001900c10b00c1405a03a1007406030101c03640710b0f200c01d642400204a049e803069810b5000700840900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 612109109 1250 612107859 612107861
    0x61513091e0804060f05090d0308070c0b150315060907080403050f120109290d020619030b030f0a0c0b2b1b020309030304030816060e060a0c030e060f07050d 69
    0x41000d002e540c0e4640c0d124608000542070165061010341409400c0c07040207819600e507074848c03040d19018141812196103031581141c0080c0d260038014014603600c01408070041c07100a003161001c0d0309800700e5200c035254540441c400c0c40e00b1122194000c801c1740001d54024400c444094026209040140c1440e004c2c205c1c40d0800c0c0c00158032002c100f01400b004000800c240d0203000760740740717aa407101c0c41e4172a1602d50030741c102802450a240585100841c91086407144001c07101658003a0b051600d11520f1001c00038003402e01403605e50301c2441644945c002400020482000144c0e2000c070005000b45004240505604600c2200200469103600c0000f031114000700700d8110080e80a0004080c0c001c001030055074120190541c00315071050010786950f450020854003a40d4124007080d40310b2040b0a540c07000651020710092010307003060064a03002070002003c1c1d008055540d0107116001c44a0411070031505410315840107039000d070020446100c18603581e160000d00f1032400600d049a0400104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 612110359 1250 612109109 612109163
    0x1415160515040b0a0513050d1d18090c01210c050d0c0801080d0c030e13110a030c170c3702030d0606110a030e060d05150306151309 58
    0x80d983d05035000800000118610a260340f0000c0340c5280c1a00d20195140e1503602d03000000b00c0300034044056040c0c2202c3c06070104c80c0d04507400041c00488452051104941d54507800d83d01e414003482008100c442c998082e00d071200c0001c140074000c8100c009d10908035400350148004000600c48104089845142680640c1c00030281d80d485426841d4900103469280848100c2d0860030062100f06440010b07501800c9054030820840340e1b144c0c08030064032400d00800641e0441e500b1100300050b000b0199425402141020243d52508a10240801008518490f04076902c02900c4020031000b948500c007139140a6090940c00c00d40340e401e0710110485609141040b0341071016900225020700114450300640c0068085490944610380c2035039270306503a50203003440c028140316a6400c0f40d1a1b03612000c0546090700f100c114280002d0900708480000d0000600c0a240640501070006074091000f200c180f000c00d01c06407074a400c01400126943c014100020111070001110080c501c00400170544c0d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 612111609 1250 612110359 612110363
    0xc0509041406130b01170c1605070e0901060501080402011b14032502010f050a020102070b131a012709080c1f0501081011130b04141516051504 63
    0x1000030760a098003000300c3c031004042200001c83c204040300d841660700c1410f000840340c0d10030402000c0c0d110304410080501400a081841039142140c40052001c00905001100d0124201d000ca6032503081c0c0c403500703840003806200e0100342010301090044d44120007841d5014249006024071148556550070801c008100d8215a40e0020803003060f940d8640b50b1246010b9140c8920a1b203440c03c5500207042c0c0b0b5659612401031000200312544030b18005e40449888940c040343ca000e85103001c241400882e01c0c0c0341c03416a441c82e000300c040d070711092003c80228181d0320b4050361048102c1c4a5441100c029408050000100351038841c20030010310b0340000b40c0300c0e80040c0b10142445a040c50811245620000c0110703001038184001081310600106010140030b80740803011900c1c03444c420042c80507210704402c00c0b442428801d130015070141098064010f03144918030110001c050b0744200000d03050110755094024008010380544101a14501481940b00e03105840c1040e01c0d1420407082c0540407201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 612112859 1250 612111609 612111641
    0x620060f0c0d091412190c0f060513030e0618150d0f0b010e03060c03040303050c040302030a0b0405070b040e0105040902010212040e0f0106260907080706030e0c011b060c050904 78
    0x11030800541070180105c2c039003034002c1039410500b2180403c03461039001c02d002024051140300c08000e101e855811202c903250409402c1c4440d00b0510791079407187c10100b0064002400c1c0944100451a281e822510820024480152301460701010090680e8451050b10000b00c020000164100c003d07004890010250320ba001920400c0c0e80c00141c4126010120540700760880001c02000c96110300a42e85c1294152400040990301d8a101100e5072103907030000b81d4103101d041d040c0002c210026150328422481032003615035507603440f4030740f2441380200e010300c2c02c2d4804100014005030920b54001c41d1220300520403910808400102000103a0003074105104000b12f20301000b00b000d8500e811a801410300e0301d844004082d1495580325a1424440d48802950048010501c2c0d00707000c20529001d40391490503034a209035908009001800482505850790041001e075030100d40c0503804200750303640006a02c5002d255196030f1100101030300104841409414410410503803101d1107503401505207065 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 612114109 1250 612112859 612112883
    0x7090b03060a110307030207060b0a08060703110a0c080702030a0633060c0b0405070e090127020108040f0311120904150501090b18040c0206010620060f0c0d09 70
    0x8241030900c880101085001d03800d0042d8040c03070310000000c80b644042c0a180c011703241c04503032515001a041800206500500c00c010114003c0c10100326030740268860340301003003034054080e1602818000c983c0300c01e000c01c510001c568045600c0b4002410007520041c282da008001070b503107100071600c40780700c040281450282d0244050a4490381b146003a0000718251203102e2a00a00030301040002c04010a000f480c0004601004810441d40d4040c00250000a43c1864005141c1c0d0007002045d0101254100e402c81e5000780d240300505102c409501a5218a441d944a8450400d0b69144a01c03c90412440038405070303041000380810313300000503d050565424180c820041079a5403d08961000301c001d920821181e03070000300b09401c40d02640d40c0e0544940001600c1c0c00d2218a03a11010b0700103040002410b6400e0b800705074a81038400a40340e00e13013104141800055031100400800329142d021202152040003c0182c4070b40c04002c041403d0300d400e000010341815510021004c807400d0071208 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 612115359 1250 612114109 612114131
    0x70c1709030f06011d07090e060f041d0c1305010f15050c0f070510051801030b15040e040209011a07261306091502031803011d160b0c0307030f02030c0709 68
    0x31134403540000721460700c488000c0c00c8c60b0450302043c1c800341c60240302d01a0981d0805c0346441d2a0882c0000c0030a00808072070f45040f00c0b19598858070b0f42c9950510902e50f12002d4a8580101e02c25a030698200d10003124903c0d040034912001c002d603000400040c410709001209800e241080303054000304403440600b4078149041c0500401503204d4110600f032000a108404000c0c0043c1c18591110741c0900c0c0108401d074403440460843c0352100c0c5c044000f2a80000c0109142c143d04030f800b07001d10301c280c41c0c40f01c59a9803640404110040c4042140440100b08004030110f0700080e403600401024684820046588c0d800c6c03a0032030752094080040782e100c503035010090981c2041c5100000c0669128100e1102c244844c02901c034896525110402405039100002c030751002d6201c2c007001400360043c0800101c030008016a10521709481c4850030b6076500010680c2c050304800e4a00c81400f0100071402c140c2190380503942a00381507001d0045100612002068210400030480102522940092152505 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 612116609 1250 612115359 612115409
    0x150207060506041415060d0f0e0c090f010308091c030309060c030b03071719080408070906031a0405011407050c010b0f06031612140708070c1709030f0601 68
    0x1801c1c248201c0c039212504401034001c01c044c030380c4140443d03030f0b4030b54096008000031014061100d249054924080220720443c540b544465215680f001c119614000c00c41c04000541c1d01c121044026151884010000601410050071001c1d000926a46903500c81904c0d42ea01054030601c01e400082c1c9403150384042c01224070491041240514080c00b411031024003080d990b61076445044905070002c50307121000d05007400a1508691b00c2d50404281c01e482f4100b094442d0094050204203001e25800024451850f105001c00c90350320441c0c61088240740c81945c1101c02004000f92040d54036400700c441740c6041c00701514421152034846544582c1200080c9003100c49070340645000d00c0c0c480000c0d070015030b42d541c284c076484031801c0b05284100b0300c200c000715442240c411501c0c00a40c1000020320000d003c0c127015038840d9140755511941551401011110303440000c001520049400344070070440c1011500500b02088003800300c40c0600b0281c07200d6854035500b40c2c01541074070086050301e0f0001080b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 612117859 1250 612116609 612116611
    0x10c1a07260c0a050c030405030601030f1502091e01020f1005090c0103050f0c09030f0d0c06050901020319050702010b06040927150b0114070c1422020f04031502070605 74
    0x16401c44800514185001e10740e02d201d80048901886004510f01c085402d0070400c0300d003c1c1001074191404da5030f40740b50000d50600042d10488000d094001d801110105502c203030f9492013030041c82c21002c84c00c2003024000c6100714030034003411070044807841d0b42212000c00c46098401d00d0758400152506e000960f050410041e1000c00d8101800d04051184404036108440e4000840b0380400340c0d40c502d0000040d146c589807a180c05981d0240301352020005411655a01d60b035405510306001039503440381054200c0c801202d0395a0f150141e44529907a4040c0b9074080d44d8041200c2c0000a54041e0f41740c00600c1c0d41d00141c2c00211342544410754154140c4a145910710309005001c6440c0030100c880c1c0d030302e900340d401405012106607030b9030900403407aa1065000a0070b910403980401d07510070480c103015180040c40e0060015540b6403c110701042c3c24054006500c494a003400031000c1e600441441c030180d8080110300802071020301010022450040c581e240b00380d800303400140c1c3d03200d507440d14000b5268 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 612119109 1250 612117859 612117917
    0xd02060a0f060b03010308160b04031e080c0d15050a090615020703020105121015020607020d020609031b1011040e0c16080a030e0f0f1002040b0405010c1a07 69
    0xc10620204140c003d803409503815641e0162460740c40d01c410902d207900e01e0340c801001404450301354051100741900550580c0a00000210400042101078000e4594400c16074150100c041c04105d50043d95059510001c0c011842d1000644150750f42c00010741d0010a68005642940d640c080c02c1000c1c420800d200ba03034001450000d000c01520b1030b00040e005010b400c440c086041c6203800051920b186100ea40030151012540103152803003650070007980d0391f10841d52480544203c3d404010554000241c0a01c117215140007986843c04500d005100c0c1582c00303200c002035100d8040c1c0d103103010002c0d0280011102e2400b0016403160300d030100c171490010001c0c00e10044003904001c0100255100c495401d5515000b022407030740c0e01d86c050011402000001a0001c1e580103204c00b912201c0c0c000304030390b100107900d60110303100390015140480491089100b410410101040100040d50050a50701b010b140071780040c01c4031800300e8800c081010021941c0d0400074004000c54030030b0701021080420855 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 612120359 1250 612119109 612119111
    0xf06081509060607060e0111091011030906071103070801091b0b04050405221b08012307050c010e06010e07110c0105090a0902070521210402060c0d02060a0f 69
    0x404044007241e584200505807038060b40c400250304d0103000003600b011041a0424008002074402070303c81d010540c210ba200b8130311461691064506071880785491300382914080c0c016625004424003004840d03800717090b08481e0718007172000000e420741d41031151800030708000c0000b0941202e10301d040806ca1072a002c000c1850f44040500f408406210410358050340d800303540c0056152103030072000388029842601003181081a000c14420800359010400c0141c900010306604262181203a03402e070741c0c54070140448120340302458600743c0b00c02460550072901d40c0c02d080d45422600d030707107040c00c0d1800c10011940c0d95101741c004020085440c6041c50f4085c40610f0003541c1c280a40c9000b5031103404101c901810414041500d003580e64610006074010b003800c01c41199555000e14210f5118017403c10407010a00d04949409e01a40c0c280c0211881982008400500003c00102c040720380c89010308281c6e0056402d00c041c0300c82e10002c0142515064a5400505140c03501c0c01031b42d02541c0020254413602 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 612121609 1250 612120359 612120391
    0x31509011d0606010c060f09030c030909090206390a02090f061806030102160b010f0e0405070b182d0a1d0405030903010623060a09150201150f0608 65
    0x401c1021440d9a0007400910300350b079645200d800c2c99000380048025901c0d0f41480d051280c020150440d10725120140b00f500d42e400b0540d5109165030480e40403030000303500201c0130412070790407c0d02e0340000407614140011002040601e01005080090034a942c0704d0710f40d200800c2d482c19840c00c44419940254000745240151811001042e10200b030300c060420322002c5040841c0c02e6540a40659150342d07507258130300004114038180203151440c28420010306070b40790341c0b01140040003106000e1141d90868010500603140000c1806a40d1243d51400155004101108030b659120704981c842c41010350710b80c516a4a0f104411000c01c80b40f44040c7d8801c1c060300310200700f0b00340314041c444052052039450f000540e80354100b2390300314441d400d0410390552800b0004196010600c0d259414100b40803400c142c4043c070380007400441d2040ea0001b90100e01c44590030400142d4000300000050454400402c003041200c81c0c0d4510b281250700700650040d442c240c140261980a45600d0388800003070794041d90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 612122859 1250 612121609 612121661
    0x60803090630041a041203051b3105060910031104030f11120714060702030105091e0c13020a17040b090d0801030b2a0c0102130e0402010e0105130503150901 69
    0x20800094103138005058481c0d0010349452101c0e61083c96800c1742c008159a1035014400c20040400000b03803041b00d02c03a454008080950100340ca110a80d078018cc001d0345007000c00b1003080a4640102010000c254988079030200d0003000c180640b0040d031107084100d101030310b10315017140c4150320000028000c1c43c0c811003048118000080302000c4440c3e25081008044280c0041141c0703100f15000650903600300401d10100750307000204814115800700c2c4420303420241001144c0c9814102c0d02d0207034040040003142c90300030707441d600a082c60801e40c14150036101041d0515207206070100c1c0c0c141d170014190404c114078a8402d00148104022070715155510b981075544a40d000b00e030140090760301d00180fa40c0008003282000550300d0b03860b0544c40d8a40c03518401c441d114041d43c407a03051880c0e000da15820000b01410303907003541d038041c503416100e0181404190004580c6904098441034035011621400201d46d2030038481d0034254001c00654102a143c112101420b46407086100b45901e21540c5d4001c0e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 612124109 1250 612122859 612122873
    0xc0f010225020d060e010b030102031003020906030706120c0507020d11030601051503040b27241e04060b04060f0e0612030403062a0804030f03060803090630041a04 72
    0x1001541c484400140c17981030080b1030380180b440d07080040d0550b10010500103640c549459400440307200303c4160145030f07036000905846069a102d024041042c0520b00c041c2c1100f26002904a540c0c41e28101d42403448540004141011a810a546006244c071031041030f0305090000c240502820b075a00f004000041d081c441c454440280003401418842011480c1d00300c10010603840b14442d4820303120110403003500181c4030518158201c42440d01441c044002020300301110f84603030b42d48d0706118210303d40821094205940184103c881541d16031601184d55124410f08010b001000c41045240f401e01d06207280044016120700d10454107480c00080c241d000004a4080d01d81c007000c0400d100c003a600041d0400701d21300451403005040c903100c0c2d0700401c0d48142018490350103035070342c0740c0f003551801020f60454100380104070f06504104108403150038504000d000c0241100c41250b5050505030440000795100c0e05022402229a400c0c0401d002404004030300c2c441c081200b40c0d60900f816640c5407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 612125359 1250 612124109 612124129
    0xf05010509060a2114030a030b010c0b040f02030a0212010b040f02040e01050118030605070e090711190201020a0812061203030f07030e03090a03061d01111e0c0f01022502 75
    0x1800100304400d14500d0850300101012405078030401928030b140d0404015a200d4004847c40400203250200a078500d621030760303141c050300e17400180507581d1b0f44580d120b0700c050514200e0281d0b018404c0031003140040e1640245c2541da880304100005140801d0000c12042d02c0801145001040c014041070202d03034080c0065904440090a15508001a0141c200f00c080d8159001400742860711080210840c1c019026070301d115002c035450005a0b488402c192071444074101c1c46c00d075a920505c400441010700071404a038003401401100c0d4140d500d81c0d2812480d6010450340980342041000303002d0a818070041c44240d4540f500003560451421080340030075024010300400400d40c548200b1110094280100c0f40c04c0000030308102c070300c01e072a07003880b0b030141034031030510ba0319540e0018403014007407410705c9107540262454031424504010241c5017404202c0c40501c6400c49401000840304d40c400c100010b028007540c0400250325100360980741810304032011450000900030400110069882104e12 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 612126609 1250 612125359 612125369
    0x10602070f03170c071e050405070c0b0c1e04030c05030d260a0603050102191101020901050711121603030207140310090804150507050c040605060d05041e060f05010509060a 76
    0x2513a01c401071500c0302c40c5880340552019900030070440160119201d500d0a0310300f81e0750159014802c540705c150085920941049000c0c00044202020802c046412002408110420f040c201d20701c482c1c9550344c41c02548584d06c200c0d034000071100300300700504044c82007200070300c1c450520400f040400c4e0185008400e0054114004007440300005c1d010320b000b40e01880145030020000c54640141a000102a01084500f500440c003015990310311004140212441e240c0e069441c0f605080c030316500d600403140c11390756056201805c203191910b084400c01c4140b80c6503140c45000e8501602c0c60074017905100140d04100c0940802c0c0c0d50800998071300185030b200da00d05260300050346040c6410845080d0080303400403c02d080b0307440c114130580b1f944080540b0b801d6004000355101d400008040004481721881030542204c4180042028040d0f550300140d80907000b03c0403c411845190702950049100600c211442a5120485d5194078224411503026100a0703c007404c00c0e040c4400000c042c01183d02c9070b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 612127859 1250 612126609 612126653
    0xc0503120915010b0a02010b06090114091314010608090102031003020d14030c0717070f170a020d060507120507050409022508040812070b040b060d1703010602070f03 73
    0x32554000c0c003044080381455070001000c0b1903584441c0b11401a80c8903d25042c010740c00c04520840614004003200c4034254144c440d5800c161a000350240329402c16040142d0000e00f1a0302010f07006031502500c05200c11004016520798103008018024500c0940074800c541e105004020303641c6400b112800131381c0d0301211030901d01074940c0f40541c070000080d150600c03280400300318040442d01c005030301400e880005501e0b210a81c207420741c503680d0300007900c610000030425810030403058010124600e0030081c030009a0701c00d0022038010603c0d100030142c00f241c081d40d440d010031070201d610518403980500038003400e02c0703241013000004280c0d01032402600c004550000e40702c0110f80701001803616280e49600c03a0f040148883c1440c1360b10f9005882400035501a0300008005406c0c45400c56040b1548110244070a803115150000a030328018801a0040340354402440403410003480b507100b0281480501c0e590b0340c10460000e0800c3e240780d004026003002d1400600002c0c101c903283c40101790744540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 612129109 1250 612127859 612127861
    0xb030f0408090d110f060304110d080705030f04090509010203040b150a050d1401050903130902090a0902030a0f0c020d0804120c0222050c0304030e0f01090b0f1305010c050312 77
    0x4003441940b1a034204070368006810300c8580100702c599031046495081c226042104100d42800307001d110300c02114000c1040ca805024101c0b1440d020100c45c0817140255445805c201d43c40d60303860318650140e458440300d11004241000802d030b681c0603a40c0d000120708001d6007941000e036511200a0f0f0058100c2640c902000c00c11941034035401c600900400004001e80055251070400c264402c4905a00c0040755003007034002121040e0010031540840c20a4100c4405240f03804e03110300003508100c40e2290f11401043c000905440345001660140d200c400700040c01c0f240119511086039014822003003550031041d2a113081c2034000101941c03140d0002d04100c0101174144d011604000e009100a5100300c0549c0c2003459810700c1c0040d80182a440001005587c0b9942c0c0d429800d07000c1150018001074804d8a001a40d091800c1840015041070401094640d180d113020b1442e0707006070380850107840001c40e22007900f01560b854000204420b013849111054582c41d07482d240d104c2d0441041030381131100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 612130359 1250 612129109 612129113
    0x606040806042a14030c0d0201090e0c1902062403070909020a030b2e031e03021507050705010b04061d070e1e03010c080709061107150203030106080703060b030f04 72
    0x43c801046520300704072014551511303120000401c40b07031500c11602a110312010b04255044c9441001031482d0141c564003c19803a1508105035036030001c0403082080c50074070031500c0c90300d21800f0142c41c071034003500901b65a140c200710002e2008440c038030300500016102810689a1404540ca00a44200e401c003c5440060760000c140034000f03d600c01003408c85000e08000d180890503c000382c42a4072441c0c803624130f181e6a080b201c0103800e1030102621044030851480c41d626109119920118443c1c01038804a50944659466150707040310607401155002990300200a001e110360780011404590030003182d820040510a803c144800e00c81c1c07061074480c003203440b0b14064444d0320f0071004018404c88900480440f5412a11034a080e0b40340690300344541d40405600500100b44101c0040c2c0e96400d00c10b1070644d044074148400e000c080740394010403002040c190101c000301900c61481e9001035640354540407005007507080007001d12003050b245c8401402041c5600c022a5000f412503200040c41c0d495038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 612131609 1250 612130359 612130403
    0x7030c030905060a0c0914030706050c1c09060212030f130807170d06050d0b0403030222090606080601020a080a26100302040f0e0a0f1a0103050f06060604080604 71
    0xc94068a6407103610200400c41d08550850320074010311b50b5030302c0d201940c0c51261b6a4441003400903a949508092428014a440340c0003400304c5040e1442100d842103e241001c00b109003180c0350b50300028640b020240305403a010046030228480740030a0b5807451600d45001d40028201130044d00301c055800b0300801c148052842510161a00242c4074080020300380a0402190f103e228035a501342d040c0000081e440c40e10a01c041c0e0625000a249002540c2c1c5640441c020752042c580902104607621811117401210ba8044018050307549002580c1e50800380003030701e1f004000300300a0440d8030000c42f500000b810081600e034800d00c50f06040c100403112004400392010060f941c1000107000c401040f00f0780d000d64405c00c0440707001b500d007081051040d940c01c90030b99422200001041d031007040c20301c0024101551019034603010701c0742d003070511440b0b0840314000320007a8025500395202407400c003002c0e00144402c0790030500454201e0726003494000c0c441c2d2124002440549181030108242c55400c1e15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 612132859 1250 612131609 612131621
    0x90907030507060504061421040c08070803070204201603020705090c070c0614090d02060c030a090905071e030203090c1c0303060b2104050a02130902010e090403050307030c03 77
    0x40282030750070b0551142d00080c020341091084100090444d40c031200104c00705001c07900508030220082145038810103d909040c02d0107882240c036400e9050f00041c482c20b007840840050034a19004d03580d0303200c00d40104001e540c0c5840000c88400c10b14004800e82c140c544040302c0d688108041c10110074111814203034248012944100c0d0031541c2c000802084080c401c0040000f40c1c401c0d1a201c4250f61950000c4074480540c0030f20f114074034010005400d451500c0e01030814410310080060f458442e030080c42d01e085030000c111400200d007002c40280030210440c003999a1103c071501e000c144c031801044140da0300741d217400d203c2418158000041000d01800b030008401d114005445202203a40345e45402600f01c801810540000740b40c1a0041030b450340384000c841070b2034000c04200110042d0b0781d000030709102024001b01c54911840081b0001602d5000e09060170750740c6141c2c002030440079030001604005440c501c441c4030b4aa54010040043e4124050304c0d00000180340000341d001e882e00040d401070403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 612134109 1250 612132859 612132863
    0x717070e010323010e100f0204030c0902130e06090f070c240b09010f090b130e01022106090114030a060203090f010c021f020307120905060115020d020c09090703 71
    0x340300001009000c0e0340c004100c0f90b14000c0c0402510029020400c0e42204d00c080190300f140d4000038140c02c1c002c00180c0040081d5402c1d11801407409642e59154202c542e442c0e40000045600410b09142843e000329410000b0810204da00c001c615001e400201c06010080c140800da24607107011030040c1d44601c144d1101d40390b12400c0c4290013080c0803a140c1070350301d008483c48109401c01020442600b003400000b81220280d103d55100385007050706980203071207810161a00054902122402c040c410300808500411201c001680c03031b080c0d08603200780003d00c0c1c0c2c071002c4900d0074001401460b495103071a007811200003c1044440800440c002030800000103406003200d800401401100314001c40e400c0d603990404030003001400e8028809076260120340604c00080500c0071070340d800e042400d800841d03103d80289003c00c41086558800c6040301c21001c016101540944010301c01910081d0b425a0101ea060004003142c280c0e14000030f558406003c002030294a00001299400c3d20821103e00515 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 612135359 1250 612134109 612134129
    0x9110c06040303090507060e0105030a1a032a0f0d2d0b0f0f061e060d0c050706060905060d1104020706020a020607020c0405070e090402030a06110d0f0e071707 70
    0x41490b0400602510303111034255031070300444100245d46c50161481006051042c1c4600e400e545d5816811401401660255944042c0b6007080304400d98003400742401106030320131501c503850072036a4000c2252040310000c81c022420104426890f64504045205041d80005101c003006100b411130100c1b00c01d014141c65040401c1a0450100190303c0a140d20414000b01095256034415030180300041d016100540c01c07403103c19a030500000f107100c5442200001810740c6280017020014a400c4580d025403000000790003090000400030640a4100104100a400c3c0b11030304044000a040c2c0c445c00c03200400d600d0380140c22081c0c544075038056a14190704010219282e0300c0f040000381d180e070000c848542c01402004004000d52802d44562801103c00da0750316400e1001c288107202e105031001c2c000b83c1c0e0600c1861440b130009895409006500711219a6203901c401902040000707843c205e081c40554241031a81c039840c250310005085044800d06640821004407004003581007030000d130001c030105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 612136609 1250 612135359 612135361
    0x31216180b0714070e1f080d12050a0b01050901050a141303030816020c011d04060906090f0221041e03020d080a02210a0608061303020c011809110c06 66
    0x2071000070081c0c10b0082c000c221004a50540d410041d0326070180c3d002d44900da85e20000420400030001d0031100c0e07070083c1c60724440117180e00d440c8217074500079503000d104000481b581810384448445004645e007104034000e0a12000c2c4c0d041e000a855402000d065038100700e000310700450400d202d418107500c0134043c440040c0d80c401c01c0f001900810701440c04250007180e103c1000c42c5012100c07a418040e019910307406400003801071401110072018a000403d01007071a244aa0071a0365180b02d4000185403042000032a946001350101c141e070580d004480d080d520602116060a4961800c3c20b0121211803d5110b240c0d1a45000040d002d40040300740c4214418a43c1802010303000036140e207064105031076001a40c0c0d280080e401c264860112945c00742c5008100c540507000580b03088a400c034030040305c04143d99880c0d030662441c00004460111503403003040c540c5001d140c0c0600081c0d000303200a01e0300146a15010f8460f060004041c03003a56030042d62500703100300440d11402a254158101400d0701e851f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 612137859 1250 612136609 612136619
    0x20f030a05100221100e1b0301180b090f0414070b0d1503050f03040e01050f0609040504021309051c230913091109092a04090b010312030e03121618 65
    0xb86001c240990000701d46c6030800f1541c0c01010081604204c44080721162950f030038000300d0b280032802c0c00c00303000f481625039014014903134a68841d10720544890380310820500d03040c10b02000640f0813268407031582d001580107014445c0504200c8000b00348102c804600008000c1414030448995480a40036020707000c00c0b0404500044000c008941210f4400c801d240d80360800c0004c0b1404801d40168071040c108448041803c044d0002a03000340000c0151f0394042600103020150b410341001250690805480d405841508031050039403c460ba01e82240030803012840d60722016103c00740b04840d1100422010565510542058030b1814001c00a000d41d5446141403111180d2404111b48110100c1c0c0c0000c41414000480040008404004640c40c001020565594ac050008002d80154417103e0b4030021601880d1000c1c0250300c16004410500351100c401000c07103415141694003a04104220f41072a0321a800f0a034022280490820f82d5401c00e50068808400322000310041400c1d003200010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 612139109 1250 612137859 612137881
    0x12110306101d150d0317100f17010605060c0a14010b090106081504020409020a020c030a0503090103020a09090204120b070906020607050f0d15140402071a0c0c03070609020f030a05100221 82
    0x303440d4406034007101c1d440c2c84054030100801c107c0d0003603418a2111410420100c4007000220700c0030211000006249601c0303402241c800d03400048690400c3c0d0204405000f0402c010708001000948000200407006207400021907200061050702c00304100500458a00f01089040451510300140119602ca0741c2d501a20041d40090f420310015004441d603204581c2400b1891080301c0b40d0020144d0300d055104401580207403c141070300340030084100004206034820344001d1000e020701c98007000c0500c1e49450002c1d04064024101020015441c8041042c0b580005019421020340d05143da2a092158014419070103080b50f0400c03054102241030640820182030300c001e55800070704904681e6014024401a072096510007020380f00e2070044448070003142d40c0d5150b0000e1010240781e03d000540d078211031841d000f901045c0da0b855941d203031070011403810802c0709040d05000d4000d014500d03e20341303c9a8460700d074000a4135020f078000880d408041403494000528500c03621706402103042505c1844 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 612140359 1250 612139109 612139127
    0x7020319030e041103060117070c0f0b010312050f030105040c0e270603010603080d18020a0305030a080f070c020d03020709181401020f03150a12110306101d150d03 72
    0x9000b1490400c901141540c420111703841250180c48100701160102c2c03100446002c01880c03207003000760507020040000c032980f0101c02d032140aa01c010b80c1c03550450400c1031031040c074140094207000040091100ba24400c000362411a0300c12503001410b0301e400c40c0c06441c86c1205c941e40540c40001c8000d0000d4102510440c8030040c80c00400340c00d402d65451040c5400c8030082c1c00080c2058030140011301d800c4215400100c0d9600b1030030403806002e0119408107150305141d4004840302c0e00f0118080b9802903016106c04c1c2d000c40c0c11025031039541080704020b03112800045010b4000c01003248075005250082020034028a1144820020041003842205401c158641c040b00d400c8003080c03050606030014003e683c0e0015510310707980c3c599110096040120300820038110f410110184000884c02014119a60668020745015104100c800e08050174a200100000d075281c05090060000140a00320f41c420000d20509131040e1b03440d000300f001445008051081e03448095145c0700810968011622 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 612141609 1250 612140359 612140387
    0x10f11031b0a0e0f1f0207090513020d0305090a03080c0a0605180c220c091d0103050705060714030a180608060d06020a1e090501110c0a05060702031903 67
    0x140c56203a003501c000754607511034216a00c0005011903420b802915140420810702040140759401c080240728404041401000815026800055080228207410700840d607011010403601d02d000c0c4d510b40d0000d4400680080060f040010101e0403013402d40b40e00603100c004d140c06c900400d4a403800c400c2c1c055581c0075018400c07160581030001013140c0050a0000d10038001890010b00f801d180c008090104620500d00c40e071801a01d818a82c1d140d5494912a0f00c2036514950b0b0741c1400281042c49169582d000307003203903510b8000c441c1c004101044000c100c200c01c0d1141211130070356841c040d003007002c8081102d00c202c1c80780d408005461402150448180241103445203c0411038540e2a00c01381c5401404032002c0350403804440204000078460360003800045220700307140c44039984039071142c20070740809401e000c00300d10b5204041c401036070420084035001d80385000a001050002c0c001c21488007041c81224001d03600410050304541d0140058040030040c0200c4260704d117502c1c01d00500910386021a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 612142859 1250 612141609 612141631
    0x90f11030c09040206070201031806020a020a1a0f0a020306064303050418090f030804021e010c140f03070303091a070c0f0201111204080c0316030303090302010f1103 73
    0x100180302d04020504511a6400030700050520026400560190142d040c400c0c803031501100c5c005002071340520240c210490140d00030840702d096840c10303417138944002100d0000c100c075210800c4040401000c42c250301c1000003002584035100d070000f007089401141140c201d4800807010700000845041040c2c0b00d107622420210b001d602c0a4140d521032100858809030004000b040b051092040a207214a2820751452b0001070200c40b40d00c412203984001714003180040d01c1d55003400300798948062011300844500c00a14580c9540c1c00010340310003900d8900600504201e225444500414844070b01702000b080241c90b9036601c5031038004d000303024000e01100c0720300314000612040840d0701580b6205400c682c03076040c21080300341c0302c5205010116800701c0c10004e080440c01003017041440102010300341c0d9000a0b88407130030014080d0404003942c030313014000d510207890000c01d24403080880c1d0407a609130800280c01c402c1c1d818100e0150004100c110602d5051140242c0c010180e00b0040d0710684010342 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 612144109 1250 612142859 612142873
    0x30d05090406140d1e020a030506060108100627031212140105060d15080106081509060717040501020c06040c05011826010912080f0108071d0a090f1103 67
    0x80c01004002d5540c1400e8101e03626142070400680011000201c5441180d1805c0c1c4881d542d40c00900500225082154280c001c1d0303041c801c840d60002c1420390006504c44104200304d0500e427000b400c40c0000c443d42900342500d801e103509401d00180c1100051500700140c00305443ca101000b402e2800090781d0141118030385018500c1012049003c14140c0304002c24151501e03015072038440180020742c0e07040e54006500030000600e09c80034894400140303600400303400d20b0080d80000301e0200303e0007031098030103402c03c0b030400c40903d50040410038540003038a02c03800300380c8503810514024050448418040c1c4908404e010070320003e40b041e03a00b2a442642d8141c464030030098241c08400c4648a9a000c1880c0342001302a2140041001c03450341c40c54a000081c8408561100281d8044021042c0e01252220040c4880b0320400390410707025101c03080050402c00d142a41031500305500101c2d01c582c9401c0f10011440c42001e44d00000c2039a5044503ca01e0480b803c1e080c85004c848030149414072a10481c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 612145359 1250 612144109 612144119
    0x120c0109090606051b0102190819020708040509040309031208061f020a2a0e040b01084920070f12020609131406040203160c020609030d05090406 64
    0x100038241076400315910b04e810002c030100283c004201d0282c014070195002d00103c00d80492550b004101e00d1000e44e12080c5605100d000d008403892402c01d4913254034010050071010039900011141165025110800f5640c0c460404441142864200904052600c0020320304540d10a903164042d00c403c50381f401c000b11203120f40001400c003003400341000d40c2284509002181402c0c400b1a0b00c1a546105041c031580080348203402004a0b81080f540115024117010512403660074081c05850311200074030305031880304005d410fa10800020318602500190364840a2460103140010401705c00550700d2102122143c044d0030901f03401e90203405440b40755000c026003800000c17450100c40070340c961880c5e0306040c0300542c00c80601d00d80042e40c0010702046004d4032600d45011100c6284110003001480b0b412034025803c4509014040f140b00c0c40c01070003031203240c551b100380003601881203052221607007070b15101040305409002403050b41030040000010040c0d030003500401002038211001c00800d5110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 612146609 1250 612145359 612145361
    0x40902130501140d030c02010c0c1a0301080c121203040602070b0106030e0d0e150f0f0412060e0105070e09060a0e0a020426070e090f1e0c2409010e120c010909 70
    0xc0d04c0c018000031228030044000d54002d40803155524052141030f41c429803075100340f000c0344200d01c00141c0c520800100411a05a05003c2c0c03c1644070111100ca410900084200303039103201900760a040d000c8000080b40070000c1982c116810300354070200d02c2c1280c1d070b502e540207401044844c41081e25402240e202c103090f43d11458515881000040800c8036105160300404c41541000c1100d80b041c10040007640741003452000603000810503c1032a0421000e00c0c9400003d40d00c0507203882c1d090341e052005210080b60000004004000140c17440f800036901c2070001646219140c1c40100d09461100501003440e400e9001030065810500b2012405600d08203074031181d840800107041c3c16089407200b40000c5500382c01c0309402c00702d04011648103020010800b801d15a1840c0350498a41c0780000101401c44184804c2c3e100240480d01035004402440700100030a89407100103108910014400059a0264140014a501c06022102e503078040300c44581c2c0d101c02410f1618080303060302c1d01c002070701605 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 612147859 1250 612146609 612146629
    0x17040306050610080c0a0306080a05030901020d0e102703080315030c03121608031006030b0d02101407061401050a08030304051908040816060f0c020603011404090213050114 76
    0x103180d4404c070403a40e84603c2c040c0a138110103065400c268945800044900b0100422854540503101442c0c0c6ca210781c0c0006031034684070444074000d200030029210703110760324505800004071160800b03a907040701c03049540d000714260b001c16107019400d845012090042031170155201e945582400303818441308504255580078000e90301d0782d06501110341403445000201c0034142c03119002120020b40701c002e6481e00419002102c041e420211541820031615034180580240f841094550364071000c040d0700410000790303481002ca024844440d00110400c203404003251000380d080b8900700329580b5004030110300c038030086c0325940c40b54040d0341010640d24008000c5074041c0790305c10000c1c40c08401495881c1482501620241c803901380522000803009410301c0000035880303010580c1a451414040c0c00389c5030341315100000d020031214034800001603c4030000c8905444d00d1480350084065841c000801400c4070308402034000304011040b103d020100c2d00f100d4140e40782c20102000d801c0445003400340c0300c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 612149109 1250 612147859 612147889
    0x3120e0d0e0a1403120f2802010b040501030f170c0a140c0603012907060906090311030a2c1207030302010c0c0812060d050616110a05030f031003170403060506 70
    0x160285181d58803011700034000c3c41e002c50845030070000c1a062107808076020008425401584d440d224510560a103c0c1403021171084404020a5040d0340320184840e5a01000030b001c07540696118005114503025a125550103c084603201182ca2070300d20000800411406018418540c40c0022072802c1c00c280c0703050340c03843c041c00b845000c1584000c2c7d041000d2032844040c444020001007011032180c0c014104807500031000452100610700e002081040d164200ca4600d400604c41c512200394440100e1800c0e600d00c2a203c0508003803440e056202c0004040c8065001e0a03403107032103501b02000f2a5070000c076402a0001c10540040c01c50548103007c03078580043c082d003c1003142c10114000c0ca4013407034009901034000007131320034150f030b03481d15120050ba03513204500810f070890b044645e4492030482c0120f03652030140001c0d9046559641d582d010300044c00c803081030b0100000e4100346440035403800444c1c00842c2c007141e0101d10042800b25034841d001c291807040c01e040018203d410940c94142d0002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 612150359 1250 612149109 612149113
    0x10e060f030c1e13061401050f0903070909120e06090f040e0d0f0210020306030a020607081209030d0e030f16031b0b01050f01020c01020606040c0e1302030603011b090303120e0d0e0a1403 82
    0x40d8030000112909d0740021070030000c41d2420301250105d80c608000746000790010700c100058940d01810a910007074030081c40d10082004000e81e0f02d246440d01000e40729094415181c0d0f80700c2c42e034580700003400381050400e446050300c9000400b81c05240d1140f0021081c41054003030b40c2007071000e503095405901c01114203680590044030700d207006041035802086002c3c0114503050030810415030481d840c1c0e00580f1104407942c0302082c00503098030302c0d11904030300142d04002185006046090b00e040c5000c1c0104203500c14404000110905015401682c544002a00030080607482031514547c03885003801074900681e0384041150302540002416100031105800a0149a80e124100005802c0c047c00120800c49017042d0020280c9402c8500942c000300c403040542c4038500141414211221909900703d820407651100b104141c0020302d00041e45d40604d0b00344540000500f80078040c003442079000c0c02c984038451101040c0c0385c0c00070810300380c1d00044601e129a141d441300004c03007004245e01031a50507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 612151609 1250 612150359 612150389
    0x608010e1311031029010c110f030a030f03060605070503071101030e030a0203030412051c091704080610060915030906091e0605010905010e060f030c1e1306 69
    0x70310450034000203194841c2e40c2c0390141c0030350140800e007091010354030008070326180da030f160011113514405030b007000340908160b42000311a00002040651100f00c0640132600d001b44140e01520340e030704840c100383c4018040740d10001542c9002010400714800c2840060300e40707100410f62510540440340f00e503410000a6003000301c1d40d2a682c10800040030207905041d582c800890208100740042d0002d4400b54002d1912850103003016190b00780d812038207104001c000c0241c1440c8082881402d00c0b90702442e00005400351492070a515440b51161280200b44c60214001908003400601d181c850307850800c04000181c0d64a03001c1d10802d0300c0d4000c1c1405106040e0740641807520075400f00071601c4c0221400314105200b82c03902e41080781d0548804000008a1200b001031040c2d5000d450b0050580c2c5500f00141d40c176000c1c600321450030141c110781c03190b0080f00340340e03200340d42c02c000030446c3c014020000000b5000c47c54050303003088181480203004040c146c03c00380f14407170984280001c80e403958840043c9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 612152859 1250 612151609 612151621
    0x9080d0c03022a150a0204060207120203190f1a06010210090b0601030902012105090d0203130b0a050712020706140c1e03120f010609170c0906060d240608010e 70
    0x80e6071a107260000c14802c40c411420091580798410707010b405c001c4001030350740d802c14000a041c0000d5420444070302108107698801a01d00160306080d0340c4c40000040441c404038641404030320510000a410824034141541e007185200c0180f41c05041c00342c08980c00c110f203050025064070845903024080c9680b15001481550013604082c048510501d82112400a266145014078800251001000786d0700c03800c0200030003041103060303500d1006000450610102e0415280040018010055028404184045224041c1d01501c0b01d0a0b0f000700e02034401801d202000395170701782e031380307d5000050280ca2214007180301c1d10045505030314290b0060098001880994460841c3c14940030b2160f100c10400303030007000c1103080d00c07a00403081c2c481580900c1d491b20742d0040503520180c00020031072908020201260782d0004000414070780544160300160307070b800006922401140b070342e540d80703a0610401d038151490341c0500e1100c0c40f40e10241e1040894441004540a10b024021605000c1c0c128012482e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 612154109 1250 612152859 612152917
    0xa18050d150f061d0403030e1c0302090103020903031207080601050412110d020d050105040320060a0e0c030a0c1a03060901121b1508010e060a05120307050109080d0c0302 75
    0xd01e02c0000c09020407010707607810703184d183c0009120510b42041080c009010805516002e02c22003050590b00400c103040f610005c8800c0c0c1558009010140b60380060514100d90294060351060303003000f001d990722080c0700c0d202141c440e0000c0300c6140c0054042c0000070007541c010f4082d601581c5104410040014440d070b1580040c1142d0300c102c0f50302c0850001100d0050340c076410480240c84c441d800201e175506081c9000340200000f07075944620b084604810390425440064080d500171207005010030180008070b11681050b694000c2c281d010700603100e0075824440214107020072a00c0d0064140d40c0203080d12103241e01c600054600b107900c078000000400602100803a1002c82e680100c0c0701c421b085c0201c00c4480200da58a50001034824824102001708581004c0350740e006140b0702c80c0c00e0740d00d4036140700041e44c4c000040c007682d8428515140c9841180104005480030b1581c401c0080103000c0e081d0500d002150401c18010141030f0904041a440510078003d85a481d505661090b40c06494034100903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 612155359 1250 612154109 612154121
    0x3040b030a06030606121a070f0f1403070518040e06010b030403051303030e03061503071806180e070f1805040204020d2406021b150f0a18050d15 64
    0x2109860b21018040040b618600c100401400e40c3c030288071510f965803030401050384650150035034002441d001c20030352036044006894440014500340c02007900c43c440c1500c4403252806529161180032040018954000c0c0c010543c06c0035684602242c0821442040199552104040c460350406801013040c681c0355005150468417134140326060000e56512030802d0301545d4020740008454040c3c90055003424821550811017084401c00c0c00403290b00425902c5900c0d115458021070039032042410003030680d000e036014041021304100c070314200303802c50700c042c2040d8201c0640030b0140e80c0c00003a88443e030070240021125108081450f040004003290000c1c00300500907a0456000c10000c51040354510030301c1541400c1140c240303581e00200b08410103c44007908075009540c4100c0300200c035440c1d8000e444000354021903010084281a5400c8017650044510b1200c0c840ca0210f050707221550004210504124000c001d0a5504d5136581040b080b20301c07440028107000d543c070405030b2403800690405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 612156609 1250 612155359 612155371
    0x1c03030e070803120f010902180f040e01060815090d080105040207080d0f1409010c091503150f0326030714042310021c050306041b03021801090803040b03 68
    0x2845401c1e40d5040260b00b0b56001018150203502e0000401560f403810503811805040d58842c01c5040035030303401c1d10100503641c0c90300d200d10901800110ba0386543c0c80e60400b1068000d100c0084c0080755a541c0c01940d01c04000300450650103a84002401441c800207240c490b803169a03030744044513481c2c441440000d50242c074044d1a448401c0201e0b4107001b06601034000c0030b440303880000610034a01801e0002c13029000d0980388859040c82d5840002c40d0388000c0321005d60751002c1c803130303c90601012020f07001406c0c1c021441041204c41130000404016524004d000c507802618a82e040710800351108a40c0d40c0440c507040340c011014001305103801d10814501500c0071500c004c840c50700d51074030007144108405040840c5a80241c806d2104681085150400d101680f0f0000b02040b503600d50780b044441d020aa4400100203010000403080c1e0b45507008501c2c4150310300c0004a003010384036401000380d03104980c84803002c00049900c80340d40d44180410310444030300c10302660a182c2440003044840c0c0c4040c0174 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 612157859 1250 612156609 612156613
    0x1603020a0606030318050a05010c0201080a090f080a032f07020406080f10060e04020102060718031707030305060d170c120a05190e090a0216150b0f1c03030e 69
    0x40c40001071201e11400c0b01440c0070b51245c0c805040140500d1003240040d8100e00d01a90f070004080060b80d80012910700040d509081507101580d49000c010001c0840590140c09200b44041007814005484000d0209402039a414040d502c0030440c40a2400d00502805407c1c003486040c900f48210100082d01da8240300410200d05107686508040c50b15000c002c8110300c64003e180001030040c1d80d845050010f080508079800c1e05d29082c2c00103500c0341002400c01c02444202c0d1403803038825031762030604000346902001c185000700504000160640040381c088021915240c00714500e4507003802e096001c10360003201300301c4c0d6400036010030b00c03280c01029038900c2d5407007114484241c02e0302c000090804410340d6030b210760726a6860032101040140da1200b001c01d0024640d480030850310352400150f071001500340050303a00d41c41070124141c0707801d403080c000e0b01030000010a0061016580c000b070440030401ca50750220325920b0008c0005117003180494100340404185800c00203030007500482000305000003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 612159109 1250 612157859 612157873
    0x5060714090d0b060109120809040c0912030c0c120b010302060901020a140a1b08060c0a09030b070306150f0509090a0b030a08071511124302030f160302 67
    0x802c604040105003107508030f455030100090303564030040c0ea8004281c0000c1210300c600c00c1e80c464900f54499044541e01070b076103415880f492640207487c41e50080030000e40001c6a6421410010014040000c040302c801e41d03d00000140d0300100801d00313090301d0708492098500c0c3d00c1c680c20041d86a00c075000c4207056004120400c004607104659002c1c8600c45503010749a0f1941601e4202e01c4100405215101d07842800030038000d40b0304c00a80150300c14a84407000740d0b03515a4180c02c2d00c502609910080461110100f00250143d06401c0001240c0a0006c650000280000c1c1512004000c040220010740c091040b03000d189002c888140d0010408900001c004002201090626200c124140c030001c600195240401244043d51100d030301e1900380030031454450403040c2c60584540948500c80b80c200f1008a400c40400c0020340c10401e100909034aa14414200030903c20b034070010b0b6035081100010881c0d1000c50002c002c0b03404206a0f41c45072403030070310040401c0300960a441340c1502140b080340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 612160359 1250 612159109 612159127
    0xa061e062c030a06060806090a03081501030f0203010b0702120609100504170f0304030e0a050a0b030a0f0f090507090902060318031c0902090601020f06010b1b0d050901020d080405060714 82
    0x445100d0b2168003504001c95101d0401b40d0841c90700d07030060460200b542c0401180e40100340d10081c4150003119400c0b484405032003680c01200504072120f03400110f184000000079240071400020f140c428800c0e07480c042e421010320182516174038100d48480303054101c0d6505003102c00e44c503844954014860248943e801c0c0d4a03082da540c01d5004150582c4100c0c000000b0f010603d03401c401000300c81001103540c00c2040e4100300204500328010301c9a404c00321000720100d0007178a0143c003c1c482c0441c028004100c04074103c00548040d02403401d058a1074040c500b004180c00c44540250001281c010b42213034519182d0340002c2001452405010440340418040b00303404912440100010708860342010032400c0203401000400b94004c0d140b14107660000680084050022540c0b0b81111403000900b41ca4581c0e00c1c03020720306203924a020f4000c0340681c000382c00e481c54012000d004c03448000c0c0c0c00c0f101440041e41050300d012000f920302070400c1d884200011030051051825000c2050710745581800d01d4150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 612161609 1250 612160359 612160363
    0x31b1d0d14121b0c06040506031302120d0906080f040201050f2101230f040e010603051006170a110d03050d021602031027020d02090a061e062c03 64
    0x201e07004902d042c000207111100182d401845281c441c0204004c0d000407a42c40000844074412441980e0040402000281c032110342e0105440070907801900041d0400014080d10762211000740122000c180c0420012410a01c83d00da9544240c0d0460365200568561703800544090b00001c1d01c5162000f420041516000c061a05440c444502c00d03071000c4142d41050001c4003800c4c000b1200101000001c21454015a40ca8200c802c0c071007015100001c403202c000d0780d03a40c0540096000908244954000480301414a070f000f02d007140d5048440c0086c0810f410304598a824011001402e0007024811740ca025103065201c90300050300c00d007081440c024413001c1004c20381e080283c03064101c020590812040d81010b0103075690040300030b44c0800002e482d40e03800c00354270309100d500c41d0180109108a4070854442160380c401d142d800070500340c0e0519044941002030410b1b40614028000710600280010f2130a8803101c080da001529102620640040350f048188282030b4034425108100803a00120307142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 612162859 1250 612161609 612161623
    0x12030914070e1b041a04030510020c1b0a090c020c091e07051c0c0512060a0f120203010209030609030408010c0504050a0605090a090c091a0c030318010e010c031b1d0d14 74
    0xd81c58282c0c0d1207d00e0360401500b0050580303075140400d4010030400a15070800303d440d60a0b448095a045581c421080100f04001d000c2e40110701f003589032094441c2001e0700001c021083c440704a03181c542c0750b0781c0ca0561125240507207041c2541e070a404008980d00501442c0a420702100031304c600070f292148402114282c80c0801501d9001c0f80c40065407800c8201e4001070b89a006d01c090f01ca04070074510708507020003504841c3c482d064000c0125030007901199001c0d011a014100001d0807103000e03082100c0b8190301d0f80c0c480d11400c08950310f00300805401a0050003a6001c88200810400b034152401c00280c500c1c1c0e02081000703030310100826003c034640f019842807100036007155882d4000c05080413008404004c1c403000962803207a0501200e0751280c0c0c004126a0320055050441c245240c103140322a0140000030f00c00069542420406800d15030700d544000307404001006568200f4051000580790518001c3c0041c0b002030300c89100b00810300303210b1003400015201c5ca0f01c502c15052000c26050070094 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 612164109 1250 612162859 612162899
    0x60f090f0703151814060105030703090804030b1503190b0c0a02012a23040306090201170114100c0309051c02040e070501090f140904020d12030914070e1b04 69
    0x805103080d80c0c07641c292842010040117880c074008804d410036800103040fa000060042c0100350315a42558200100c0382c2c1505c0023107501030324803803c60821403c198091848040340350701174400c00a1000e141d00b1400300492060b50000c00200058880340c1c0d81c0c01e40c0381d1003a4040030556481d10180f0b0040d100c234103500841004001c0c0c81109079810b207036000f400e100650001502c040c80d07454102c4d0142d080c2034221412030b03620001c001a00c01e464401600c048500b09899045075a16400000310304c0a48821403050110455440c03400c001000c5068070b03daa07500c08060b000031540b2106206600388a006021008034500c00710140700c1d0241d0008094800248842e01c2d250810702c0100b004d540c01218070806011080034a0200d942021740b41d0b0504c00a404507030348500041004a020f549a00c4000780907180c1119403a1081c030500132002c0c02401412800b1189080103100c0c0b010091f40110300f1030f0666070300c2005071410f5203a6205909070003444c0c42200c035081d902044001103580031045102c4c0314030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 612165359 1250 612164109 612164129
    0x509011209140619060501171e090705030705100509040e01020d020c100c05040e0703020a050702062808010b0f0906090603010e07090b0403080d1521020405060f090f070315 76
    0x4504048010f000c1c9886100800d161380c01c0030801d00c1203a820589608000460f2000c0070190396403c143c0f0000441c1581503211020b8241061028040d00401c044095070800e8040b1003580b951a0148038814a80000c1c52001540620a07011107150036008150f41461500c0050300b4096103140d048200c0c3e00100c6540601e60100350a52401c6203640942607031520981480390506107041c1003c0c40d0f8400041c419400c142d4001a450b4050707000c3c00544852a40140050341c4590081c002220016400400d1040b55043c010090001c0340c030a0001c0c81c1641c0074000d5050070000b40c1d4240106a4010280c502d500100c14401c4510549460018500910098240f00b0740344c14104400740110074241c0200c151540308010910215030703458101d41d400030110000286007020108011030000071900410502d44001c070031911401114001c0803103080c000c6500300890740f07540040040b848110b04806410501131400105044030030403600794000254180841c038110011001000761000d904151003003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 612166609 1250 612165359 612165361
    0x2040f0e0d120f0501120b10030c0306090308090a0503090d0807080c0a121e0f020a06060602011d1f05070c0609030338090a0905060c0901110d05090112091406 70
    0x4085503006058180f00901010002d42d410315504000344034500d88068070040c0c072100031640b5401e090361410000c0d0780100c200a000341d1a072403e000070b000f0581040d0002a50760703022441500c804600e0110203a4003000540c80c004064042c464091104d0106980c0c0100c00e10580c000307d001c0200800da041c2030140503002c4003105207403000400c602e0ba0400010008490b0840040d42d0760146411f045070001e08140c4004100710008a1600840c4800140741508120300000c02c2c2c1e03015040200503130700d94555000e136441401e400c9941c81c500c0003510140540c004404c44c0c8405140d510182e004083c900e07100d0700418213502c8400c11745405000440001c1d6940e07480f800610544d1f8218180816940c01c40a00340c50b506035990703031400c4640d108510401c400390220300c0c0c040140d480060400d90040a55406280c4940491102d070441841c4a01180d040d2210080d4803202140c8040c5001c8a44c41d0981488002801105d40484174400c0e04a0740e0b40c1c500c4203c0106030203540180700d00104500070401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 612167859 1250 612166609 612166637
    0x212307020c0618091e060d020f0d03030914121c060b0403050705130506030d0e0402090d030e100203041d0705121512030412020108041a04050307060e0705060702040f0e0d 75
    0x103201002401017035130380e0710701c04090031840b84444c1032030700444110b80701c1c2c10010040c000a404244103240484e80400007680a104164150308400d003481c0c011800000001044082245c4640b0505900c41d0110f1040007411010340c00881842c9010203030f0000061019250801c0d0411540036420565059100300800c02183c6440c000f807004076080805c080c016414460f011944d29070203601a0010301c0007240b070b10000c0b5219a41134500100c0010802410791000d41800b8040b01da101524900810420184400b2103000008440c01c031401e00000214211000c101034119400103001030040200411585104120049078280203102c0e0440e981c207882400c00030486160410400742056810520081210701800f0203400401c030780a00707040240380d8542c540000c0c170003641b01c051060000e4001c280300500a00102034804e40e842240100501010428031542cce8042070311840358014402c204040060506030014014a0720400000c1401010030f0790090404c1d1800001d600059811481411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 612169109 1250 612167859 612167869
    0x3010806070203180d05010f1d06010905040b1303090e0a0c02100603050d1d03030301080304031703040b0403051c0f05060a050f09011a040312212307020c0618 70
    0x14001045000440c03410708422407120341113044101e4948200d0021090b60144102034020320407074008803c08001c588202200b510301d11a041d49000850b206000002c0340408562107841c2c003c43d080880403103e0b0b5a00c40d5140707a070a01260044041000300c000005102c2e11240740e2a016a00c66940400c004c011818000d240520b4803507690513282c201304040010030408241b21380a001a85441040700380622041030390309111040207034042c0f10000c00010b031408040085c00c182d80c81049142c01407405441c034080d841c0420307500540103085403400300d40004d009000812034071065582e0340c1d00901035580708408840ea40e1020902c503075165400c02815107454168140900000c4440300312503042d01c0c000c6109140c0501400c2c22452003c0008441025658155001958820b0741e09440104c1c801c0c00030310130020000ca24200803800b8480355000d010500608160200c034202d102c14052078132151940690f03010b0904015800341c04030132000c41d12460010314000a040b094000c8040641d01442 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 612170359 1250 612169109 612169111
    0x1203090714100f05030c04030503180f01052125030606020c010f0e0904050a0c12171c050c0c151009181b050402070b09060a020301050112090f0807050303010806 71
    0x510510b4140c0710b950050303400034032a0b61406091301e0066280c0d940d40402c0d420074885c0d1303000a00584808a0141c04068000c05080d08201e42510003003001425840150340d030303000d800780e110110841c84070303404503112992002d0781d400308048084503000c58010002101c04180c10804500080d1904010f02016404001707000c40c1010030319000c540c4070303018030008045100c5881003501c0381e07254170082428000f0800900241982062108410564910000003002540786003101d6903034034001c0e404550241c800a4800e0341d080d00309034800e0329007800340c090002c000041c2038901c5144103000920150b5820840c0b4004a00315204900b403d013000000281c02d1035240e8042c00000c1d00f4405d41002d001228028801e000f94400c2500903445294440c0c40b941e00070350341101303401a1010644d0411310512010442c0039009078401d60b402500e41c00301031002d91200340103660209030b0204c20140100841e600c006d21f810b002d00c000d200011074035130f2008025800520161015071021005200008041c4481 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 612171609 1250 612170359 612170399
    0x209090109030801080c2805040509030a180b030a02030402040e03031303120216030f2a02100c0b0106050f040503070605120703091a07120608010c090e04022112030907 74
    0x2003415000391701c00500c0d0740c4408600e0007003044c00b451f02042c1100c030b25040301d0003a100040c000c0c8014580030703125503500d4104102c101c0c00110101404900d024941c8204026151000c2c105032850361a880b19202039403014004a070000e41c0c544c84c03800d080c1c2050002e50301a207818418a41003903840c7c1002000450b00740f40c203034440c80c410003091b030b0684030600e0f0b225202903160a04040009246009440c0c2e40ea04110741c0040510031603841412107200b0003c07a120a00c21280c2000c48080c0702803c0b034580c4a04800207004420182c014001c240c0643d0150000c40302410841c2d181540303c0c40400d0070a21107602c5a00410310228580b0b0b4450f610354031040e4801031a240c02c00c64190140c5036050300b40e094024401104030100082180c2c240309001080251500d1141409010341c5c80107201d00a003407150301c1c0b83c001103140b5408078001111901e420f0040d40c0007420f07007e1803945a18080b0000b852502203142c144500040c0c41c80c07130b43d51000694441c1d00c191000c0d08880e17181c4103c000080c4158224 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 612172859 1250 612171609 612171613
    0x10b0f010329060c0102130f0803070507301101110a030c020d060e1b0114361908100c0203070b040c080703050a0c0501030603030219020d020909010903080108 70
    0x803040000b00302000c54051a202004040000390b10b00081449885450030884c0c0c55400010021041c2c0210001070f401c44810814914007141d450510507164007030788034014269085040d0400c4806010342c02d410b0405110040c0681401c1d0081011908d005030090032595045014600d052541c4c002c08484e101161140182a5410300d50381c006019550400c2d00074821100c080008091010603445005001e20707000071114050900e050042440040103407980c001010f02c034444401c400c2c801c09580b58200151f401090110b01410854005541c03804d4803210120352800e00e40e81c03980c1300411059120485450254a181420781960501c09018110200c45040600f171050f800d40c00001c850b21545c001d6000e001d1502c66240c25011724545601000403841004804000c0c44008209404894822440340c0312269443d4010f6059801078030000c2c0c0560800e42e600300c17030348126501030009188000c0812901c61025800a428140155050440382c1c2d0354404c60340030181c00028940c050415540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 612174109 1250 612172859 612172871
    0x1305040f0f1110200f12031b1206032a130905120403060b030607090311031c110115060c03120f1104081603080f0a200606010206150901210f0302010b0f0103 69
    0x11071146d441c1c104640010ba0350000200040034404254004490180041c2c100c0761742e030301c65044c420280c50042e500c1c81d10034051040101e04042c1d80c26150b010b140481c0c501d44074842e03003000030800c4c81035a003c2d1030540c854a4241c400002078003031080c406e0050301030b6451a00c0d681107080c004100e401c4603858178040c2e8000000c1c0816030381c00001761000c0704d51080b4841d5a503100100803d0500f071110349000075070702d1001011601c80b40c01000c0002c005810304000c02c4002c000b4000b51001d40280e02c103050220b00001e80110104c2e218643d9142d0310860f001d0701050180c44042c81004a648081c3d107070030b80e900b000c034092140e80000e101144080c1c1422440644c2d160654030385611510aa00d0004500b00d000901900c20501600c0010000000d52040760855118030300d000d07895000032641b150041c040e0720001806201003d00d0008042000b6180d20010ba09202d03084800c807148180c40d24402c0c450359040030009155211034021b00784030b40d0011400300d40707010610020350b0380d01d03130300d44d0503d41084 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 612175359 1250 612174109 612174133
    0xb0f01080d050d09020f22110403021e012a0624180603051009020907050c0615010c05060a09140a02130906021c0b1305040f0f111020 59
    0x29090f10848211640c000403420813a02c00660340e24225040c01d50410549003410007000351404c4149141a10100e0070b00c50413400c0d03189480b0500c0b4a000081d84003042d080e09081110409000342c121034010704041684120308076070345402c040c115110fa0036029407048403404109281c000c1c441a03400c0002c0364860b40601c0300700180050400c1c065500b0180c880e200085111003250001001541c1280585d11890310801d0002c010b0410040164000c000f40c1c4003240e40303184650308880311b55201070041e10340c0b41c0301c03140082c1e000108200170504222855401802050080c05410b000300c040800008902c1605d00c1c0001c03032a9400100d031003540c0c00282c1d844000da15107908004842c030b6807140010304004180341550080c05805403031088901691040e0705851100c0c1d00214001908580c90340d0160f48030800d0b001038034401c40d07000705040007141c814030005420100e0880c0702c0b8400c0501a402603454808a11442c3c10648176400180815014404003501500b2414180c0340c00310142007442004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 612176609 1250 612175359 612175367
    0x3200a0f030b100f0909020c07050301060e010b0d0e1204091b02061315110408030a08010f1a13080f03090a15091e050409030e01121a0f0f030a0b0f01080d 68
    0x14008201403040c113810301c6100f0780c0318110050141034140f000715140c04155407955a5a50103001f841e0281d0301c0e050012403800d8201c40a503040764040d00c0c405280261005e9403030050100c0c0041c40c40a03218031007010001c1c110078005840584001e090000c0c0b200c00a007200c28010010101e40c0e0195003100091085103104420318058040c0c00000130000d41035002e01110050000c05603520040c0300208000c81d40c40000310040034205035581c0e6900059880350714501d1200094030484503944480c0e1641503083c410b00c80680428105221842d1200b0b075211407840c00d245407208215115080003914400794640304500c5800707424018840f8140301c64050024242e81058016184860004202806d076481c14031001006803901030824043c8601900e00680950f020805003400b00304103201380d00b000744003842100680c00d5034a1440c950001e405e02030090f42050781c21a00e402102e00140145952030401c90405818441e003420318280c5031802603144c92550680085449401c000c04c07000c541a80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 612177859 1250 612176609 612176629
    0xc03230405011808070b0403032d030b040b030a08090a0e0c1204020a1a04090506010804030c060e070f03081b0d08040b151f030501050d0b01031203200a0f030b 70
    0x1c2800c0440c2151a0000307140310364580303580135803124880d64030045014001880076100300ea100303880d041c090708030000e012103c00c00c1118100359220030340070009403000d101ea005401082009040000c03884000000300b0308082c4006401d590601c80054204906c1c00c0c80d11200f4000d0965144900031424010700e5011350788200aa4405041c3d0468081000e56881c90104801000e03000d142c0040540240350340c000c160094810410b0503454500000c99550141200798440c55140d520a01c05a2490b511300c40140328240c04614648100c40020441066028406001e14084d17844e09407240c4840b52b1510000040706050107042e0031103481321103500c1d0402502d41c0c1059001d100301820b55140c40000c00c091034141c40303c60f400104101c0b240400300d4088101c054601d41964280701d90fa8849091180d044150740b0024108000f0400400100710542c1d00704112280c00e00e00800c0c010000c10b000700c0c90402c550b04008e034440c00021007803003190b00100c00f50008001c9007800e02c45801c02e20001006000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 612179109 1250 612177859 612177869
    0x16050f01170414100b011209020f130e100f0e0705090a051e0c0a090f05060f030903040333150b070614010807030506251407080403030c032304 63
    0x8290002c1800c00c0403c19950b400f88201c58120742800d4040f08158020700110f0016502007880075540395040c46480c065081d00c40e802410355550340c60b40710140300c0c0b21104082410b40d150f0f0b5440000d044018107100b07a0040c06081d19012403041c1e13044c40810101c40c011002c2622982c0120010821912210345080d40030143d03000008540c1d840700000051525034000003107803d100c20302040562607820001c0c000c0c07c50703103503038550019444501d40b980c03118903401440da112405011b03410380f020124005561064064050324289030f0f681d078542c0c5515111450502c80c1d4649d1500914025144103007030320202260710750a104508105260041c280300600441000030800100e0b4824040c19070022641001d000c004290307079680d1180820b031a1421400112410b00030040410300174101100340318040f034404d24404a202c0c0c1e1207001030703c025030f07030b0307203207a01e800d41e05101600104101d403000d000114029214020303480e12529000b84a060800c80700411f0003a80407640303400700303028002d0f501568 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 612180359 1250 612179109 612179147
    0x509040501091b120e07061d04050925030b070201021c020307090504020708120c030a20120601110114060a1508010302060a030b09010801020403030e030a05060601080408040e070216050f01 83
    0x1200b64590800341c049400e411000b84581b00c1c0014000c1e07030020044040e00450385106003000d035540d0400050340d00558040c3d1480c2c0c0410800705810490754440c6070014010707601091000ea990f60360b14038540f401c562440141c0d50204012000040c04514400d04900000d003c5146181005025080131101c1c00303602d00072540885e008080000340c034112905440079034a0701f86c0781d10b0305000750704442d401210361040082c10b018202d4251080c10b00c5000302d185111520a00300300c1480445c4400c1c40000f030a4170f0400c150740184107c504000c0c810b04040480840f01c80c0301903d016010300c000e030a0f05a104003510b1b6054b0390f40c089031a62000095054980c1203d8659403181190011406000d450015a500080a200002e454801580200100e070f109413506030000ea42e003802c00d501c840013010041c0441d006030b40082c4296105041e03042e4018401d1000790b0426131240d1108600180440b1090b0159110400a12105d9032040a6000605044640c08140468280001c0000900c82502e140709 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 612181609 1250 612180359 612180377
    0xc0906170a050c090402190207060201020f16020307051002060402150a080f06010212210a050c04090207020102010f02180a090c0212070807020d03051c0902010512130606060509040501091b 83
    0x9540b1a4013240c048001c020301c01d549800c1d8014104600d0005000850050301ca40c00f0001491070040c001d0b6000c040100c01c516081c854840c508502d86902080102da00d800348100100320755030340210881d490541c690007031240b85007510511100351807000700346607406414005e030211242d001c82480d07170110300c54801304890389480005034a800090002d8040808020601c0d0b85181c2e11850180400c207215401241a80c43d00c41d60b5804031b81043d10a00309028007003100384032071080c03070300141522441071000144803c0c0005268049030003c0c003a600a000d0761240b00c0e605480c2c01066403000d00704102c4208055000910081e43c1d5460401e0004203180340420b180013842049420b81c3d03c0d9039000380401c4028040752600402c941d0000d600c4c00d4031400207402501c0180f10b5413098400301135060311014075125004c00c8600c070403c40105002038031440310414a000660900a81d402030903140c540f40e0302d82e100d40c002c0206442c8142c124006140c600f6480200d000c90306212074240450500300f103602 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 612182859 1250 612181609 612181621
    0x12090812040b0a14330306160905060408030a050f040302040f050103060c0314060f010504051003060e010f08030702011202070212072d0302060a021213030201120b01091707050d060c0906170a05 85
    0x10900ca00380c100740e8580610310801011155641d0234000c8401d003a6107890446072a0400c000341c0c1d0041d8043c07461036506c14007910389268040c0000749882c04104c9a6141450343d2540054195805105450200ba449000420410880b401800158074944c107003888621911410101aa140100164864204031500e107846034010006c403030140c00301500400102000702c002a02402061180e414001c80b0a0000610740308d0902e440d20035188084090340c0384c03081e190011107a417003e1210601180d9820041840140e07654044800090709507806410124a407a000c3c01025812a640d019920351480444603401c40170341e03141003500c2c1e048030380580300c8040803412460200b002d002491410b00014095803480c0c507124040003124400d1741d9800c81c020f07254280000b624000000c60340030402d00d40b024403103103001e508071305803c4503a034080701d15903650b850018601c504900710039140503a0340c0c99a840096071241010001e050941002111524401c02e805141c4100400d00044180d485000c104c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 612184109 1250 612182859 612182941
    0x60915250807020306100e01030b0a1d070f0504060f0b0c1905010e0c04290102010f0c0302040515070b070c020316080d03060e0712090812040b0a14 65
    0x1400810404115000d0384a450061159800301c07100707a00c244102000100c00700c501c401c4003001e480b820600b400d2280d207107584450910700d010b01a0a40c00b5118001c0400700c1444820014541d0050700c001c1140b2403034407400f80d10001030ba4021600840c1008014000c10b800c0030100c408a0380c951142a5880c0e01c0f0305031f80390030304ca03c400914030300d002009020001e0081c150010800100107400b0782c2e07503844400c070030041184c00760a0701c0c02c1c401504004c588101709450281c10199501800041512240e045041044440700910701c0c004c241c0c0890280454103003030184144210444090318600079950321141d6040c075004006a00700305841e540041152001c0c0303c0c1284045000d40e00550041d01c0701107203925401e03040320788000680340c6400090040c0c8120804c1e4042c0d10642c40b51060000d110b100c100152151a005441c405810844506d081403004401441603000301901c184505004c0c9031081520200e54100c03041e150303500248540c4000c09030b074101800b054150240044203014000d80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 612185359 1250 612184109 612184147
    0x3110a031a061e1e1c06060c03090501031503081b07080304062304050d03030506030c010e10050703050f16020321180d12020c010e19050103020c030408010608010f0b060915 76
    0x3084e0840007007040186034440300c0300114003005040045c0200d42e1507040c102c60344441c1c01800307000251403450801843d401780d8030895410b04101c40801c0c4241d00c0340c8130300d8a50780c04072136020a0190038003c610b41c0002d0902248019140d6440510720b49841d00c000200441c0d0003d030710410031515484042592510b050407a002080081c008400084442c140500181000c071402c9010740201141643c0325886480c9101c50320400510f5002d1424001c0f4040700c40c1d8124080843c00e00008001e0366201c0c00071700d000303804503604440344c0c80010082072041c5420900d0b800710180c01c0c1403c1720b02003107030b5559043c03e440901c020005c009412896100020b2510708011a014100c8600100e2201e030035a80842c1700f5103100e80170780710707503094017400ca040c400e00703c24203081c80000100784202400598801d4004065514050080b00e00381758448103441e0031901180c0c0300b14401d82d55494501c000311514000c503400c10000303c2d00107007002c0c0038601042001c0001c0480c3c00740e50034009010142c08404020752 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 612186609 1250 612185359 612185407
    0xd0605060109090c020106050117090d1215030506071808060f1003240513030e040e0a02310606080403300504231b0103110a031a061e 59
    0x24400100b013039801074000c2120780950350018a0140c0c0707a006409550043c5801540500700611903000340d01301c11110400c041809058098641c1d4040014055002030340010b94000c10182055042484000d040390800100b64a0356245120041000300e101042d507550244540c030300c5544580d0703401c0a000200d4090307080140940490000c000c40042c0d6031483c0640401c100000700500e8980c3c0b061050b4505221034014005204105a10b50b1410150440100001005c0c202c03000c06450303600054000000e44c04101c02460881e0090820300392051310751400c003403205800c0204506085000344501c100400180500c2000700800d4002c0034543c1e04006c0790f400425032001001d10482d0098050907042da0f0503035064041407003114410400d00c09034205241c0503001082e403d00b205d25940600700115000506150f5610300c1d0600c151070701c0005002e01e01f40c4c3c0e6000502d1a90b4034500359070403010030180a01072501481071200c0e03d00c00215400c0004101c5d054545c4481c03080e40d4507103a2103031100c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 612187859 1250 612186609 612186611
    0x2061308030d050714090f0a0f061d04061a031008070603230709060804110907050903010c03051018110a1e020307020105030402060a1106240303090d060506010909 72
    0x55040c40100c05000c4041502e0300c14000e44d200e4010850b00b41502d8107809030910b40c100640c1d02c0c503142103181a0000c50001c0c0000700700654810350b80c2c4c055200d84d4010408100c0c0b42c030400d1070380b4002403007400f0484401c840401107503080512000301c00005010340b00f815074000010a4031f640071804072500800f03034102240d0f034540d240e01d002000381036000c20010603450394803500d001840b0340342202d91140000c1d41d654264a03140290444504e90080e0064a2403002c100d41084245c98110019106131070b85d49450380d454280805141c21194001c096408242c6130005211010411810340c000f29103a0700c41200200303c0d1289084001d02d0802c88240c12a800001c401d0289034120504e02502c0c4000c000311120310701404002c0c0c0e140c0c03156002c001e00140382000041e0040c0780c4400a071400404d80e14007106003a41020503e86403002c103407141e1412092901e0700c5117400c2c0d50322880310042d0030194055230a0051190110314240480400240340c80d131107100044c0c1991040d50380710300070210064 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 612189109 1250 612187859 612187897
    0x4030c150608070501090603051e04300e0405040f0b0c1612021507022a03010513020a050609130f1416020c041109130b0d05060906130b010603090206 66
    0x1050703d50343d954900c20180410031003000000e81c54001d10855200e4000500010702c614410b50084800c0400100704036000c407004003401d411201c203284c0001041116420581c01c3d550180c0d0050300d803160b210462485282440d04110009189000030241e1680c070529040503629481c154408a00501c4400c9602003110504034041c0081d81ba46c030101c0040640070b0f604900d8500300c103035404031412203014004d603221a1400c5400c2d0344040740c84001514103408031f080c00c0d6042001909450040da689030000d907040900380c06514208444400070441111a0b038508000c640104090300450f038590349074103a83d49840c0038000f003581c010000d2929640c1c1c1030b08040c0341c03a48030126900d41d501d0150005200c0c06010031601d0070203201b16461001c600020909180c102420080e01503508080c00b064a629000f402d04243c480c4140e0503078507032141c0040e02c213030700d00080b2091901000a10543c120340b01c0d050000046000301d00c0c824155942443c001c0b40c0c91001d80041f8156103c1da04182c606103e00380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 612190359 1250 612189109 612189119
    0x201050402040b010302030124030204030804060305061e010f110127140604080d150803030903040303110601060525050d090303110c030303190e030a0302030105010f050403050604030c1506 83
    0x250050348524400c64041009000d0100118201e0200b40240d8003c140d409100c407420310042d0714241011245450058a0243c40f9690311845410580c004000310740c44d842030047c40c0c41d0911b0035000c45000308800d01d101c02d180100082001e070310300e60b8140a00840d0540680f13415020340100301548158a03803c0140e40300d100f00c5072600840d20078190348110410384040c1d02c4180124400380555040fa12131400c100014000c00000d000c0442041c201610a2200085981060006d180325010f800c014544841ca141009000351000c409910780c2904034500503c030860700601a9070144000b14076040d82454490f550130312072011800040c056100c1c42d14040c1403240d0104400c01903a200e90ba40c1a4401d4410710702a40d121200040580d050300300f880020380c4402451014061748018800c08280c0a004001013400c43d40105108030000350000014400340d60458594802000715203001850586507850b070340e0b204c1602410007800c0060900c1000c041c40784030455019603a0201c5000c01c4034680e56 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 612191609 1250 612190359 612190361
    0xf050a020c0a29130501030c1107060e10090e0a09020d06020d0902100309050d030c0c0821160f050a050708130f050d0c1203090b130915141e0d030201 66
    0x1060a440240f080c0410840448050034255464403011200712007903d814a0b0041d000380ca1048520403c105c103000e0358a0010030108000c400500444c0c45a030340c00b0424100344012160385660a009002e03100c0070030010004440c0219a112484410000d8110102c0c0300054021744c00c004041c00190010403080101e00880e400442494422981c001c214905d0303d2069040d90020040504682c001700c00300b4030380c1c900035004480c40000c0c903c2c0246074004035a44100755500550400c1c803198070b0100009a031480c002078035030780200a141031200340309410740d0024501b441c415080c0e030070000c004c04e4100b14140a10180c680c07855000314502d840b46400d26201c420308156108041102000e6180007585040c643d854280c940c2d040354080035001d06228402120300d07000724089040119036030707000400a480340c020388001095900f26640c3e40d0724140340c250a50703a070445001d01442800c1004c100c000021200450007246c2a03130004424031400d9205529100d0400b44030f44c00402d0709902c0c400305a41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 612192859 1250 612191609 612191639
    0x7020a2001211a010903051506040e010f021903060506031308040b07060b18072708011508120306012c03030c010c021902180c0d06030c051309030f050a020c0a 70
    0x1210082d2183c14000c001169854218840a0315580114486074200089049000d62000024101081c2011403100c46800c66010741d0516501c00d50205d64050407507422001e03013a5080e481e00e130601400d030070600080d1032440003406c24040f0b000c1c40c0f00c0217801c004000c01a14010311652417000d80321469400c180000d44034001005201e02c200000d055004c41c03002c51254029411591420504100c0108481d41d24400c2910b41030706403c080320005421209000d42e02c207158000c0386c1d0000b038a00e440b41e00d40c9400c40206410307002c0b030014020812035980c0f19840706129604a844040003e201d90340c0641c24900083d0019014000040c1c0400b1600381500310904044255084403006c505000c0069900002c0c064000d5005047c0407048070079409901400350000300c9804901c3c540141c0c0d0307130260204d5030075510403600000381d0350003003000b40b50580b192003802000c410144114041594001c10440c403070507114090150108095221a10070007075106c031800041c000c41c4a20781c54208441030200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 612194109 1250 612192859 612192881
    0x3060501170d09060e13140109090b0a05090c040f1808190507050322090612020f0609031c0e0607050303010f05011713080c01140a0507020a200121 65
    0x42080c124040b032910607021001182e00c03a6079482419481a01008122031109151200480d00c40c50380d030340320440304642c19008022501000509409038942440d9655000f015822094a1704c402c02c1000100400c240e0f0300101f040b0740018030000070200c0100144007549a030405d618420303543e03d0800450000400d482020a011030718001510b820840385441b80040080ca107400a00a01c45130480b58601e500105419080010345d541d00c64036140c00322620f07540b04208945c18240e0700420350405200c0112200c409070f503802c0c5020f1851303012035920b002c51507810b100f508601e6007401a26200c0c500c0e40c00782d410001c00041d96242d040c24601e54a0700280030720300d403600f052100003030036601a81480d207600b01c008900e00710780c0e03644051405640708510000d0f03410020401681d44a00d07828810114101d408860f00d01c02400e020043c076044803001007061041d9071140b084d0f0008035980000000440c01c04c90b82d070410040e080c10049508400c000c94140c0500c6224904c40030301c02e0141c00c052441c007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 612195359 1250 612194109 612194113
    0x10509060105040c0c0b04060216030203190906080f151201020d15051318020d06090302070f05060904020309030c010606091517060409020a0e01060302071104020315190306050117 79
    0x290702c820030442150040000c4401003114a40b4200000f0020050154414000c41d00182842030007200c9608001090b40700700e005800004c0d42035281c0202d8400c003882d40c107051616420250400c2c001908462014050001c0c0039001c0001442c81e02521281040c0136002420780c0740c0b40d0220380e42a40c04bc1d00100300c001d50090030062440140e02502c0344c81c10449070010246240364070f4183c80d090080081200034108000c0781040d04026807203ea06a5000368411440001e05440c2824000e080c1400c13a00204e1850f40b01c1c40e0200322550b213001c269100107104640c011798076140e80d4240c1d440c501c074072960325080c1d509041e07001400c1d81c0c0104115007140d160940b119981111400100c811403e81080f0f1100e154584001c80c045050551001c0401ea101a1207a0207207511881449901c600981c020000039800007901c0f4104102e80082c61016001600c0c03e40c1141812640002d007141c071052628090f00c00c4103519051031a081804000441d04800308000342e50310344018038040381c00c00032406814 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 612196609 1250 612195359 612195361
    0x222060909060f180b13020303030708041103060402030d0e01021905011e0b060d0b0f0a0e0117010902030a0b0c360d03020c060a090e0108030a033602060706090501050906 75
    0x40f0105005040b501c0002d40076020900c9480e40e0380c5803c02801130700e00200d1110804403a001600c0420045009901ca0b4440701254075040c030700407102143d1f00e4582c9010750002c800384001a240010b41d12000016030410900c0052000b0040380f0300540c0b0704060111000c80781810050200c1984482e1402041910b4038440340d000da40f0040a42e00385d8141550084410414180486210b07800711a100d00d0007000300342c030b1032840c80026500707070400e400003800705c00c18400404c80300d1071400302c8921280d2207400903c00e4080035000203413624290703c0040c18010403c4002140308000d041100d0115103403110443e03255061070b210099501824042d00c09009a011004a607464400346142c120b036072682c0144403200015081c4800c5420a2059a040c0320302030602142d003d040640326800b03030101c132004580ba40c980c1603000701a6514045244601958031440c907000c0c901ea40b1803a559030010340c0317041386900305c07078804100e1510440348041c0400c0c1c5040820410031006401142c082d200700c800b12030b25 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 612197859 1250 612196609 612196631
    0x70503011a0a03060e040606080f120f130512031c020c0c040c11030a0c050d0c230a0602030c031f051c11031f0c030c0c022206090906 59
    0x451000380140d0200a564040038808004190300809940314107180c003289540d80e4200c1024104016182142d503d40c44600c04e0044203800c02c03400750014002001041d801100e5103690381d16200e080c1c900c85125000242c410030354040030001000a2802400003070b41c1100031103849440390020200448540d403121901082c0031024001c2c1c428039a10f140240880310004001c200040c0010503000092005102e864000d1040900180803036040b1a00c440b5801f10700b80c54118200007102076004140498000714001103201c601c1100483c00c9880c0e0141002d03251280311526190071000000c0c44140000301b001a48034207800030798003884092003400b9000c58284001d00c20424140a1240c0080c80044102c80304010a0181c039801802090804140e079814000301c3e09041c0c428240d00b0f40783c10f03e1094000381c820705200d44904860546010000300c81c200400500c0e95078143c2010f13200d2266441001345400c40945081c0010b24042c404000540d0b40d00500da000c0c0014810659000307280100d1864 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 612199109 1250 612197859 612197867
    0xb0a08010b07020f0d0f171e161707020307030303060e1b0f0a0509030d020a0203100504021e030102120a0e01061a03040b09030c03030a15080a0302070303031a0d06090b07 75
    0xe0465000f040b40c0c80c420f0090003071108080c0c1c501003c3c4c40d0391b860320306003102240944603902584a110f6030001c0d0b8507100740780744110300307a194200c0c0c00103a201040b21040040110380c81a0f4119803021030380302c1000404d4114549030050143c0a0352500580100100f050303007580c0034208035140d0030681605903840c00c08085600514100d010300c022810024484200c0080005201d054100e0400d00c0c1817100c0000801c1c0f40c802d01800c3c81c0050780c400c0c1030b0706007503281c1005402040f6001200034000d0340740950119a45610b0203010141d8060483c1d0300c420b0a42d420340540d0240103014501104034942800c8600240c407640311000781952818402140860010083c142d5800d10031b14401c1c955101c030740d1200040c80005112000c140001c3c4010b1110000c00d01c0158007403199000041451481c01268004440c850f5105c4040c5500034014031002039008103850040300c3e014100000c80e400e605a01c1d40e0f0790f89801844a6211083c034045008000ea9a41f041068602a218061950b80d4901050f1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 612200359 1250 612199109 612199117
    0x60303071203020904020c100c0320161a070201050402120109050304050609010504171b1f030e070f080f0f2d190b060f010206071220040b0a08010b 65
    0x40c000e4154900010744080c00b940080505242c003504c010715000541950500700101c41120710a815100c61240800396414083d10711105400781032502084244003044030140b05441c4810035080c2c03085030a6051050304141440c146809a001e0744052404140c000d0090508039404c070710800e480791654903084070510a604045511000661505060400304015900b0280c48030341008000c000214003141c010f904c807840c4405840090220120071700402c030748984000c00ca076020744404400040c010302c2a4415104060342801c0014254070003842c81414444a90018141e003014030000250880000030794406d5880f81c40150740e81030780c203110b00c9503d640d1140f0303074130f010f100940d13401c000700b0204800c5054540984070704803a0b40e50502002d42d60161001c000982c2d10a10100070820f59040c003140c14214a5000d00c00742019152a05000c7c2403c4001c1c1184010590f13114820b200c02122040c011020b003010310074080e1595981c480180d0242e005520038400501340f040002031940021043d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 612201609 1250 612200359 612200363
    0x5180312032d0907050409110a03260a0801060f091707180b01080c0a090806010e16030c09090b040209030708030921120703020102090a060504050102070b0306090406090c1a04050906030307 83
    0x4c1c2885a1500c3c04100240c25440c400b0784001e105444920016a80c040b01c0710000d511030a4020418011040102003a020211000c4a800c4c8200301c070100070390b400b051050650f21107051420380c030179402001325007030f083d01d4210350448202088034a58020001442e1003c40d002c001e0842a44080712912005071161841d540b03012420203030200c0c0901035081c025150700c83c204e207044490309659201103450401c084c0e100700c200724440b00c00c3c02100741e06525421408041803c00b8890300060840c01080034145204481001c0d90360508401d0960f02c0d80c049411500f002801c8510494451582d19125446010b103140716060410f045003110903a80c000c2c4002d428540068201c4403a20304080360903521445c003c1302195800c201f489080d1382c03954120000f0f0300081daa0103407240d0400001a2400703000380c124070203803042441081903d0351011002a4882d6201d10081100e030589d02e094501c9001e1504180c1a4108600ca10010724031110040c104441e0129000780f295102c603818141c0781c0c4190b00c80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 612202859 1250 612201609 612201613
    0xc05040b07170c0d0806090c0316031802030f061f1503050703020712080a0c03111b0c0a0306020d050604060815150a031515050105180312032d09 64
    0x90401142d248034060007501501035000f0329284641502c281800001e04042d80031a18000921009050050096501c030012007450740c42c5052a080e1080c41c0003214440004041e101d10542019010102040e010740354003908440a01081032059510ba00044607030401c0482151821984280049500d000300c0b100345e0b08420398907220840c12005054010510014140c0811072040090302c0365400d84200300303003556515034908013a0a0f4000781c42582103400304140c101b203000605074403282e040340c00700c440c0081c40380f001c080c49103802800c02d440c010200b0361100044000005004540d0000d1550050124082042c1d43d205010002120014003d5881c0c507448178100102080900030f1441e013090b10348440d0008507900f040080c0740310800340c20483d031204011086010b4150300780110010300016100f2a1326807414003000812a019007807a49620041003140e03503840d44c400384081c00b00d1001c4004000e0743c5c1d2615103864908040d020506a101010f0503011590300c9510181a034020401640 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 612204109 1250 612202859 612202867
    0x1020a140906091201090312020306100c061103101406040b0d091505070c030201061a03040807030348080a02070203150403020c120604020109031212060e0a0c05040b 73
    0x8000340c1140c12054055070040820881c1d021a5620682e0360066800c040001080d84803c43c5801400c1040c5445040d0310307140140180031b15907803040519030080213145011000000d10f810714002034000500d00f5032070648000180300d10020070251034000d9929407072043c2e211320001024004240b242e4410100c82c54828480300303020041e1500501aa43c0c002c1501e0b6003002610740c56030003103c0c3c05581c401c012428440c40e0f030081580a0181500a0001e840303c20f080c84c0038175442e02260710004100030b00d00780300001c2003130405029a0000c2120107602c003048842c1040040b80c100c0110002070f22000704085070000c90b0305000c03249602c100100250b500d0b0001d544075508510065045400201c1c1c0c980210a80c3c9402690018101d61195000c2d90050040f1650b00c000d02410a10040095041e908404100405030340c00075081c80440e90301c0a40e807601805411000c503400100c000f070301100381d0308002c400222040803105241c00341001031020000d0070040f4000343c40502c154480c0d0004904180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 612205359 1250 612204109 612204137
    0x20604140f0309041e050a0b1908030304030e0316120b180c040b010c1704330503100302061611040209010c06020f120f01060e060903300a05190201020a 67
    0x600b005c01103004010003400c05156101d80007064500c203c40340d201803075803015030410914081d03a0402c2c070f00760040b0b582003901e0f0a054945880744402407000e403e01082d00202240340e10104a500300c200550510090103d4075220111044040200240d0700000303064085070141c094a020556070300c480c44010010910750106010142c01040c1990341030041c0702c3d0038000403d0180c460305a1031845060f106035600c6c14054103010086490013044010f06408031102d111400700c0c40b80f002419500e081c496141c0c0e0b24000d003030701001220f800003500090086400c800100803141400070313891003a0402011440f60005100032400342040c400d0002e1400b60741000407a03800d81c000c0c01c4070b85442a20502d4501d520503600f101103400d4408000e4205402e0042043d035a004c0c0c4041901d15044800c10302d013004000010b40d0741c059119411a44450205071041e00b062014030361003c081c5102007007600c45d06100005082500210320807003001901d03120040b0310300d1061007200c180b04041c2e04c601131205448 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 612206609 1250 612205359 612205361
    0xe06072a080c16050a0e040314090a0512030c010e1c081f03140705040203010b0f03060f1210050f10062106121a0103020906040b03160303020604140f030904 69
    0xc030666840c20100900000400c0a000d41c40d01610002c0030050700c2480d00c401d11102040300c3e400380b290b60400c0018440001d61020103c04220000420180c544201000080d4a8012075012550010080002c1901100080301600307128401c01c000b0000303016013110303c90b02d4013800c450003840c54203a814174a0703441d4025072201741c00c40301700c000900b004d2588000c03009000c2001d8205a800076004410300500307000030001000544015107040d801c1d549020544401c80c0200703d04065170360000300000d4925100c5064440c5880401090403030608540b6412a45400311340c10307405031071401c100004003112024842d040c015640a01550281481d104049400040d010300040500b454107220401580c031500070303039002e456514414903042c070082c501541040141ca101c05003055040c001040565500707d07807a54440c80a480100c0d280907a50b00003410240814014541022030f10030100a065000a10700d200c1ca1046460003410101503503050fa03560880050303448650f008000c2c0c1d0010b8182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 612207859 1250 612206609 612206687
    0x1110a022209020d05031c0b0f100e0901090f0e030712030207050a05070e0712050702070311030106050405040c080705010c0807031d062d0f030c13050a06030e0607 72
    0x1900001e03420b1202e90002c2c0200c000c0c1902900d283d400030400f000c02030316042404a0031414040200704c0203408402140c2e0400b034800d2040d01c110b51580d08111003d0085500e01c2c3d02e110024403c02c41980c40c0e410038001445145e42030034029142c500068407030b40d40002112101130b044440e49011b183c2500e0704030060b40c807101c01116a800b41c103145a0015500308441d0b07014103901a03c0441703628041900800200300100001e00540c14401401009900410508140c0e904036400c82001c4140e000030a0242007a03520443c1c100380b40000300020302040c080e4500c00e8880d03a00a4030507030755840e001150f902840070000f420386281044aa00068041c03450802c054440109115075220007000140080d0441c8240034042c100c00c00d2401c01e0700445201c00c5c0c24580c9c290402d2400c1c1032401208034803030300004220030003a03000020024807103200701c00580d006050040c04104255111000100900300f2421b40d94000c0c8915000714491500520701e01391484817820000100003024404901d9400c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 612209109 1250 612207859 612207919
    0x5130308070f080f0306090703061202090a020c03040b1c060632030f1501050c03041a0d0204080d030f0b090430170a021201050904060e03041401110a02 67
    0xb00280d0140002244803020f414110384080001343c892034a50306018840b04001c220404240c6421410301c20004402d101100c4140c040d1382428407a500e001050000344107401c2603050511000c42c0008020220310014288070301c3e2301080c025801031805280055030280d01401c004101400c100c0c100c0c1254448040c240c1a000160318039404d000c41c00014540e600035105620881d1541c01040102c48000012004168003860240c3c1b401300081100b503160300440c0240850307601d0080142c88020b800a05a5140d042c8101c0115620366a82801c2540c9800c1610f0000100b81842180c900c0500755200301d02d11888050b01507c019a50340d40c800d0041a05181510034185181c441c09122000e05070324200015a0b54503503282052100e884590210001024080d02c103004200122003144c6052541e030446000340c44001d01510380d468484050303c6e209400c9034480c400890001464210901d02c54070628081c0c9844078600c2d0280a4140c54003071155001e90000d61a00c0820000414102d041000e80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 612210359 1250 612209109 612209123
    0x1005010b28020319140307080103050c0102120a1805090a09140d020304030210020114040c051c15051801020307030c0e06160201050f0c010204090203041106040f0e06010c051608010c0513030807 85
    0x8143c00001c0c40386c4c1c0090310782a002844442c0144204641001905244c80c0b09000401b41440c14240300d2100e03109025082003005642112174458000390b83e000406868000c111424a1508100a44c014001141d055522582c081402a400000800c00c4840c0c41c1956026514090541e028811401d8000c203038042150750720741e890030402c1e0300c680c0035078000c0d4400c42d02c06180500d880c0030480fa642401d208040003071400d801d90000200c00d0700b01d8402a0780101000b01c1e695440ca004146820700003189440d03154000800c01075459071503408004035524641b501d000c14030000090281d03d0240c0c0c040b0b0f10890590401020256001e14040d0002807249036030b840c038003401000440c3c2a40c10590040a80e00d4000c014032007000111181c0134070a08040d122542490300c2c2402103040c184280c0306040055046034041400d50340b14044086c440740e0072400322001c045001c1c20305181e01d2030364881c1010039403810781444000c61141045440603a0701d00001ca9020742191544140350b800540120b540b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 612211609 1250 612210359 612210377
    0xc050d0804080f0f010c090b12091e030309071409280f020d0b0d12030908091008160908070501031503051507230f0a021005010b28020319 61
    0xc2c102005041c03c49000c07400a07242c40d8850b407030300d1425111105441024005114002e00c040e8540c1c40035503405c60100242d80c101600ca13841424100842c01110035009245802c0100343c403030b8000011402610280200d42109544114244500605484440d03000407480c001c2840000d040706418501e10816001d2180c3c07006100094048844044020300c1c40d40d00440c03000c4c05c04d8818850908150001e0f542001d030003000f03940b0f40b00350b03030a41c3c0c1400d0241543c906880f000d00201106880c2030b9000502000110300700740c40c025056900844003640015070f89225030f9103440c0715013014022182020001e004103800e0500560103800c1c071060000c0c0d11502c0303d60020204504021001c290840c120060350981402c220091421207090000034401c0d2600702d490010010035401c40300d04000000c5d015032180d0921404a080c5607512084014203030030100003042d082035210061000342d0141122036040030141c56140d031107001c251030030030150300107002038140a048a0400c1c4030030707403c520381604c0d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 612212859 1250 612211609 612211619
    0x3080c090a15020f190201020c012105010b040509060f101b05060406021c090f03030b060d0e010b0315060a0b0a0908010c020715020f06040816080712030b0d0c050d0804 74
    0x15001410b400600141c0c080c40c600d00030440e0502c0b00900c11a040101c41c0c0a06043d600040c1da030320b0000c0416410000c0d481c00b01c00e45030310040000608a0303103150043c0b180e942e44104003401500b0a02803d40b240c6103443c013144061405500c024404031020f0002c28103449081000c1e11007074040116500a1000540160001501807103020f01c02c1d84103810050700d6030150301d0004030600242d08107a50161500d5141c0001c110300071f149042c0d29606140128131000e4000c0402e1443c02010380c144280350620501d080008419001240c40319801c0d0111014200313a0003c0442a0f4419180e040c0c0042d88220b0511040000000528842616042c280324407075079984000d01719110901c070540180c0011030140404c0100080c803a1000025100610502ca141c0d0803440c0c4820001d400205940030006813108000c025014a880e0560040c0c01c0ca501c60342d5038109009085101c1d828800003a281502c014598a0101d060b0224150000c000700119400c01050010161007000203484441c0d003400001a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 612214109 1250 612212859 612212879
    0x60803122403060405070f060503092503140c030d0e0913060e07090c02120304210909110d1407021209030a061b021b0d0809040207050d050c060108010903080c090a 72
    0x8081d5210320000e00c4894600f910002c01c404088e00311400f044820002c1c8203100c2d60001f8650940d440702c1c480b004044000407a00480f04c0c0903580024240301192103a1880b071080440d944100b5407003a81034680d468004d202c11103492064400c800d43c80149071020851440e8041c1c000c80c0f4a6204050001c0c8000c00500038529011069102240c02c2ea12611400003540d81840990f206400000500f81541810342c0c94400c4843c2c3c000341c0345064480301031480442032148076400024850401c04000f0036009a442c1d400990000ba0b1405203a802c160103402e1030080316030007600c904082c0d80a0701004081141e015015031090507415814400d20b0921400b25503103206082076004106618850303609410740190034a035980340a8082400c03030780e083d0b21068480e03896030168140c3c480c006564513803a540c0050000d0084840161a51064042403a0140d80000040c4070f61305c5100101c60141c3e076110381103401d0301c0803440c0003800619920b022884480c00b02c000360407050f82c01020420b1041d15045018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 612215359 1250 612214109 612214111
    0xd060f15020706020a032a1212060b0c0601052101021201090b030706021207030320041701050907051309170a030c0228031b060207020406080312240306 67
    0x80500c5158040000403038042044500030071040c0050a03500840c0d0f10040e20928a03001c0110f10742d0b5100c0001413130b42ca480f203180c480c159801882c104030240e8a94008000701a40307816403115525010010030b40303040c540159811180c84a004203800d0782003205000306014400d8030419508100c9566000b40c0c2c1007030000d044003211044d07000c10158500b410319011b07940542c801c81d0081d04060360a00810307038040350980840102940540d41c0b0780311071400f10003c10b140c109003d13a003144840d591030b0107140c0a00510031110349014056222030300d80c00381400c954060702d01652651141d241000a8148500320010307014958074001509506a00c40840030309190301380b4060b80fa00003c420b82d58035050f11645070911500d20041003544240302c1c002c1944400e03003074030914600c2800c2d07151040510174064160400780002e02011080f03041e16280c4060b40103a4002ca2189041200110300c20030300000b91003100c101100524002e850b856118550220740404049407030380c1d802c0010016450420980d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 612216609 1250 612215359 612215369
    0x203150a2411072312101d010f2f0a0315090e060601110a0f08220608040c06080603100e0309060f0705120702060d021312050d09061b080d060f 63
    0x400c84c00c00440e0502511a142c1c01d04880c440d102150b01c007007024100040002c012060403000042c0702898104c11840c0c420b80c58480700345c9600346204c10750141800c1d041201c607940003840049101d128101601244012402143c06908040c03003c2e210a43c0700e41c100c002c0542d084903258a44039210541c00d0b0903162005c200c0e40a55100c0404d001a9503480000422440c0051015015046042d034880302c0c2a0305640c0054005000410041d012001000c0c12a4841400d05402d101b415034980c00034240142c1201e00781d6034001e11000010f400c1d0f005902d140e120340e100601900ca040d5090424000804014010028512050140c00f803d901c54a000380840800705281d1038a5002503d042807074005d4044480c0480a000c4c842c40700140c881c10140d4550080c0d03044096110664600d084c00340c0501540400d04014200c01441e00b800408900925485c1060f42d403403160645600e07060b80c0c00368080304510400c090b040300d001c000c9100c0e04088e00c0070354081880880c10035529a00c01580e000d2079001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 612217859 1250 612216609 612216629
    0xa0506030f0609061e040f02040b0403050a0b0609131b0806190b03031806030405010b060a0c02040f0e0d050d24080607020c1503071e030203150a241107 67
    0x50020900c0c103d07400a40c009001c443c05417080304a11150840824096081400780343c461545500c070f812260140c601401e5540d000c1034031a80d9a05000b80c1d02c002d001d401f502c2030810f4070049841070900109461160001d0002e2030009211940d076003030b0b0442038a003003c0c4c2d100f128080102e0040c10030b005480c056100307840c01034840314803c000071048501e00c080040c402da0081100888000e02d2080c050148102200c22603182d5035107007041405800c0c0b40003440e1380442c0004000174541d4008090502c6d20780203603410401d00c00800c040320125034001d074003200668454107442d201c142c82100100052841c042011420300048182c0d8401c4204095520090b0903403400140301c44802040604d921403911310003013010410610220b03101e51214a140028403c00100203210b9a000c0c0000f14010100007100d00310170f6900f418020000d4000795089200e010f00841c115005140400d908420756120600d016030b14a001141c0100882940c48031509000017140d40c04101001880314200414600340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 612219109 1250 612217859 612217861
    0x30e01020d1e270303080403031a010207051504080a210503010b0d0906020403050313090e0d0816211a04090f0f0201030618060e0c070807030e0a0506030f 68
    0x100281c00c02665184003010015040d100520390440c400542c6903a442c141021040040751061048503e03000d05049050b4003142c807030000c1010343c000f40e9140319030f00030340d4200204140000d0b075221460790050001c1c01684651002d1015150a000102c3c4010300f410041d4641680c8010b01414901c4060301039445200070054038810300100c1012210495a601e441d5246606050b11080d09000f02d8140420b040c1d0740d0f2702c641041007003a41c1140d028580160450b0740740c2100c180b41d0006124240180d2014904041c103515040000103003020030304403145c4031b4003240e0f80d40078007a041c1c550311400d0302400c0250300c154a0340e00040c0102090783c2200803460104440e103820103100307440c54001d01285d01513894401c4070f2020481c44292010303403503481403807182c00c0181800100e01800883e0080f440e28145c045c100c41c102550fa61100046030566448541c7e07640e60304190703075500d008501019144100c00c001ca01e0010744a0000d0b401045001001924001d40740c102080b559002140d07510300080300c00c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 612220359 1250 612219109 612219137
    0x60f120303010e1323100212090d2109110406060f021902060702010c051608010e010f0c08011701060e0403080f060f010906030c050405120a0b01120c05090903120403 73
    0x50781c0c1d03622521203118803883e0070740c980c0c4110410300d15005c15150720225400b0441804401e015582d41506a940d007951100260600722040c6002680c0c00e00f0140704000c03030072281d41d000301e400000220403005c20b0840d100e0342c841c008029200d5814202c550790108405411559502d100305005070031140c2d141d210071181200007a28001b074180c0c9900d02c5100c0c0000e5000169105401c8032141caa0a02e441841c0320180e250482c5005038a40b0105441452448085420541580031044059114009000d4000c0c200790714400c6640702050500003035910001401b000529040d840208845240005409560340002ca007804030144c0f0100c0010f0040c101707005800002c000e1480e08050115120360030f13880480d001802280003480380a0916840c0e4050366a030f14011410b8500500c00078200124418507402000e407141324240040b2105031480c0d0021520000441c1c900100a0340050002409814102004010ba0004241c500399100070041e0b5818400e00031240c6015038402d4036004080341e010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 612221609 1250 612220359 612220379
    0x606090f060d05100803120604090203010e0d020c180f0103020103090c030803070c12052107021527032d070818011202091806032b03050627060f12030301 68
    0x82d60080200391b0003445540c4000070301e240659000b0400300d400250b0445c00e880400d01515580e41d5018180c0144809028219004100c0e05200c4108030395021004030f03d6108904a401c041d2440c985000300c500040c00103500950000058900a05030540004d0380c4c0c0d5909541d50b401261300c180014115000c400070069206020760b980c03801400c0007030601c4200200c08010b10002400e03c0100c08445020030071040c020300105080401c810201d85035464101d8464145d00c00c200424a101804004115039800012061b104030900c00c0f00c094800d02c81c418000340c003040d0110303040700107c10100144000944801e0040c0440760300010b89800d45c0100100150429401020501c1d40600412075003102c0e984070301c00b41c5602c1072102a4444a071b1a0b900c0444e141c4620b012103082c4681c0c90103607000c41302002041025800380d41313550500c126924102400b92210582601c56511914800f8100d10155560b860381d81c0310030090075445401c0f074880700080044800c04003d200d00d0b000040140072018107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 612222859 1250 612221609 612221641
    0x6090711100b190b030a09061b020312010906031a0907090e010b030c151e070b090a14120f1e0f120f041208070e06040e06010f090b030606090f060d05 66
    0x3c03100104010900d001e22010892100030800544655035490100400005600c40212138012601c0d81080c80360344e01c0003070358030341c001c8041a206803c54800000da200540c01a00c06903035010170120303030000c40d80c100c0d0908090003900c0711406000d14940031402103101d20905c0c00da821824004079841d00c042050600344200c004601c0c1c06004c2440c1c0c1511561b00d208102d60b4140b440b0408040c0444505841a00781e02441d840181f14442c40c000303002e15044001480b0700304034040c0501d40e00c11001160407a68518804e07050551000f802d0160a511040b0000500240006648480c50000307510311548201c0e8420403182c440392402080020001401d203184a03070007400048410f15134102500d0f031f501100a03400d120740812030040c0c0050215845200301442c1030502902107500d95854220b050607081c000c441d50b50010b001c14000d40007291040040100701c5400b180700030316649554040c0445a4045560b01d81c01c00007120248105031600402040000e1003031600107224240801414a5806 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 612224109 1250 612222859 612222889
    0xb0f0906090d05070f08040618120b070f020c0d060203271b010c140a030806010215061c0b04080408071e06031e1a01180303020606090711100b 63
    0x4040c00c2048900000011051815031040c102141c540309903140401443d61240300003041c0d001c2c0842c0c002482030b08140380c281040c444420342d03850161203149441415841041c050300e02c0c040341000c24203050049603040c1405440d84141e0f00966041030100301d1401241c1400c5408960002c104181903001901510079921003998180644011030030907941c1c1c4000d121302004d04c80307503102030540d682e025100c040060f5912108034450030540308081134440c00d405a0540c0400d29100c00110990f101140d05042c4941c00c0c0070001c942c0c1c03145000e1081105032a002c515a030143d182011001c14035603922a84581d1041c41e40c0340e500c50a054405041c10b106600c030b00d4044c1c104000340e05915a119800409a900a1900140f03560401d4036030044101c0101c0c5805103c0e103043c41c5c2c54030810451070500c5080100b0b1301e0301c1078801e901c2120710200740010300c0060300503040b10000c9249480e10300c003240e0f00004240707486400c2020f90881e09060240040c841d80c1001c0d0b0302c0c0000c01140c2009400c070650030b8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 612225359 1250 612224109 612224113
    0x3051606180c140d0615081608010c0509010c1b120b0a110f12090a060c0f0f05091c290103030210090c06030c02120406030c09090b0a0b13080a0b0f09 66
    0x1a01d00000310f40c104d0100301c0700901140e111950507040c1c02d07840f0f40c20f10003800c4e9001201e0750320140540e1411464001e0040d03110035400d208402d0a441d0052040311024101030f500c0c0c000c01c100301d03120010310a0180540c08451040f040c000034805d520000360020382400f51410105038140139030482c00300c0b030b4061a1781d56101000c4c0b10040c070004080003500d81018540d000ca85950b9103400145082640c8840f00070041c0e898044412781490b40103980d408000748a454200c3c60400781e060594072400381c51f4540741d2002d8101080e000c42c40210210608030740c030810898841402d6081400490690740700341c1c4038903070031010041040c50350400c1044e2158104c0441040400c110341c66400302101d45000b80000e250326140d83c59184c5100b0811320480c00d2840303507115121916500d008001c1c2c00501145d070006025204003184540540c07186642070311004110301841e9141152070261504483d0400031300c088105800a20130300c0c1400b445007581d20501d00900586040030628900d200c4c0034101c400c8035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 612226609 1250 612225359 612225389
    0xb0327060405030a110703080409140f09030f090d2a09091a040f05120903070504020c0a060b150403151803021e0307050118030201062103051606180c 66
    0x411008412507030241203524085505c85040c201c0c00340303840310b00d13440180f4180f8001030000b03030044a0340c0a10300381c20105000c241c0b42e880c0c0f40c06510f0705030011b50340c10800d600200004820441d44000401c0c9144c00948521130103001500e07082c0c20440007002d64400c40c03280080e9a00c51390940401e10000d4540b1403000c02600100340c5a4001c01104820011540c1c0034100101d002c2c481000c04051440f91300078100d48a4503a00a1404056004822007500912032580e011482d45007500039107800003012001440500324649804c03000c0d180c4c0c50f1010750098507203d641c12000305090000c2000d9401500305542c0f4006001d0181d08407a150300100b0707a83c03071f0354a00c0240002d80c0401c0504454004504041c40380d4000d00080e030861281800c0148290719120f411a940301040d42c090810034026002003000503a82c2d03205940a43c851984200d50490800003000080d000c1d1015014005144203840904100c6503079100c1200d0050641000880c160f1128500b0032a03100c2d40c10000c0e1085242d20866 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 612227859 1250 612226609 612226613
    0x305010f0f0b2a0114010f061403070c020d06140606090d03030905030f22050102030f12190e010f050a0c050702090402030102163519090b03270604 65
    0x6031801c0b03008580e804000000c2d6840f05406103400038420b43c0618520815000c00440018001c25010643c07076045503030a000012468001c500c140c0c1101c80c140c0750101071203251582508103034002001441070000340f110080260701d0b0391540300b0400d8460b000016400b41c4003040108008002170289119650410283e921502c0752800c0c0710096501d4180494180c042c1c0c50181e003503001341920700350b0302840421130000440203c035504c01d017007074540c2c125000b0355116401241c0700d04c03d50085017048801005008241d08510f6603480d071010b23000c2501001e1038121f4000b03009488004031924110703074460111403201c52840c41103940107007081c8010001f075066280b01410601500d81c010344500c003500001425500c0030340440d03180d800c40b0449a6007114003403a1010000088444242c0070000035443c0080c000c01d2001100d401544001e200da040c00b0b9100c021005c40c2d00e155440c1c2c010400503050000d0b450715100d0145014a00c034000ca6000c0c0c1ca001d10001007003102500b5408280c2d03000e1424000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 612229109 1250 612227859 612227879
    0xd02060f0a0204031a131709010306080102070b1f05031006060f09051c0c0801090305070302100504320d11010f05060d081315030b01030e0c10031e050a020403030305010f 75
    0x1144112116407205555404580c0c100080b00f451b40548507815140d00400916804002420428001d0700d041081315140c3c17075024200c1c0280c41d001002600d0040c0840c1a210380c09000c021000c4000300024038064841000c2420702a032118414000c030f0b2030304070034000e00e40c0141040d040c45440303141c4403607842c0c60b0900207442c0c070400304806214246080300c41414070502500890140850780000d000402030740c5001422036101c80000e9006000d018903aa007480d201d8082c0501a03508013010361a01c202225860903c3e8cc80c0c800c80704540003e1188012900b4014402442c942096407101e421484502d40d0a6007035416204000c01150700c0d000070030105503284000d48007102d0b0846407041d1160b03030402134206400781582000310001d401c4207100302c40640c1500405aa02c0081c2c0e42400900300d400d0790b155803035081020542d4040c8c1d403140c044400d9842944003051100341034404081d22181102c5440480e40d056511602c1582c00240a100f0300d501405a5070051900d80f0040d110b2a18064001d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 612230215 1106 612229109 612229133
    0x306060308030403270506160b07030b1908120d0902060d051b0f09010c061506080405061005030307060906090b07110c040c020d0503090f0d02060f0a020403 69
    0x5074003007440d4800b0605000d1201603005d4001d040c28100b0545030455004481c45214024960300400c00c0d650340c1034041c03160358500007031001c520001e1004003d08085041c0289541200c100310188001481c6030229401003041c5855100c00240907001d000b5100000c1c0d4405004941555070000d41c0d845603000e0000c0d1841c049800c03090707024020550088040320000e0b1181404809102d500031010901c1c400d100d03400c00100c0c0d010440ea030b2030600419070000b50004440200300820450100703c09078004130908080c01a481ca41400295a03110300342008003243d46501c0420b04000140c3c01040c0f0090384120000b5003460706041c024481c2c14600fa8403503151003510f032000e0701d90038207104229045046074040d1195690f580c109803905d80c00500100310610500242d4003a01d0000c3c48000401c40b1507502074841400c12030003200344120060300041c1c10fa441000104001040d04040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 612050359 612230215 := by
  have h0 := BRFrame.cov_init 612050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 612050359 ≤ n) (h2 : n < 612230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
